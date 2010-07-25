Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Export targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import ssa_dynamic.

(** symbolic terms and memories. *)
Inductive sterm : Set := 
| sterm_val : value -> sterm
| sterm_bop : bop -> sz -> sterm -> sterm -> sterm
| sterm_extractvalue : typ -> sterm -> list const -> sterm
| sterm_insertvalue : typ -> sterm -> typ -> sterm -> list const -> sterm
| sterm_malloc : smem -> typ -> sz -> align -> sterm
| sterm_alloca : smem -> typ -> sz -> align -> sterm
| sterm_load : smem -> typ -> sterm -> sterm
| sterm_gep : inbounds -> typ -> sterm -> list sterm -> sterm
| sterm_ext : extop -> typ -> sterm -> typ -> sterm
| sterm_cast : castop -> typ -> sterm -> typ -> sterm
| sterm_icmp : cond -> typ -> sterm -> sterm -> sterm
| sterm_phi : typ -> list (sterm*l) -> sterm
| sterm_select : sterm -> typ -> sterm -> sterm -> sterm
| sterm_call : noret -> tailc -> typ -> id -> list (typ*sterm) -> sterm
with smem : Set :=
| smem_init : smem
| smem_malloc : smem -> typ -> sz -> align -> smem
| smem_free : smem -> typ -> sterm -> smem
| smem_alloca : smem -> typ -> sz -> align -> smem
| smem_load : smem -> typ -> sterm -> smem
| smem_store : smem -> typ -> sterm -> sterm -> smem
.

Inductive sterminator : Set :=
| stmn_return : typ -> sterm -> sterminator
| stmn_return_void : sterminator
| stmn_br : sterm -> l -> l -> sterminator
| stmn_br_uncond : l -> sterminator
| stmn_unreachable : sterminator
.

Definition smap := list (atom*sterm).
Definition effects := list sterm.

Record sstate : Set := mkSstate 
{
  STerms : smap;
  SMem : smem;
  Effects : effects
}.

Fixpoint updateSmap (sm:smap) (id0:id) (s0:sterm) : smap :=
match sm with
| nil => (id0, s0)::nil
| (id1, s1)::sm' =>
  if id1==id0
  then (id1, s0)::sm'
  else (id1, s1)::updateSmap sm' id0 s0
end.

Fixpoint subst_tt (id0:id) (s0:sterm) (s:sterm) : sterm :=
match s with
| sterm_val (value_id id1) => if id0 == id1 then s0 else s
| sterm_val (value_const c) => sterm_val (value_const c)
| sterm_bop op sz s1 s2 => 
    sterm_bop op sz (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_extractvalue t1 s1 cs => 
    sterm_extractvalue t1 (subst_tt id0 s0 s1) cs
| sterm_insertvalue t1 s1 t2 s2 cs => 
    sterm_insertvalue t1 (subst_tt id0 s0 s1) t2 (subst_tt id0 s0 s2) cs
| sterm_malloc m1 t1 sz align => 
    sterm_malloc (subst_tm id0 s0 m1) t1 sz align
| sterm_alloca m1 t1 sz align => 
    sterm_alloca (subst_tm id0 s0 m1) t1 sz align
| sterm_load m1 t1 s1 => 
    sterm_load (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1)
| sterm_gep inbounds t1 s1 ls2 =>
    sterm_gep inbounds t1 (subst_tt id0 s0 s1) (List.map (subst_tt id0 s0) ls2)
| sterm_ext extop t1 s1 t2 => 
    sterm_ext extop t1 (subst_tt id0 s0 s1) t2
| sterm_cast castop t1 s1 t2 => 
    sterm_cast castop t1 (subst_tt id0 s0 s1) t2
| sterm_icmp cond t1 s1 s2 => 
    sterm_icmp cond t1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_phi t1 lsl1 => 
    sterm_phi t1 (List.map 
                   (fun (sl1:sterm*l) => 
                    let (s1,l1):=sl1 in 
                    ((subst_tt id0 s0 s1), l1)
                   ) 
                   lsl1)
| sterm_select s1 t1 s2 s3 => 
    sterm_select (subst_tt id0 s0 s1) t1 (subst_tt id0 s0 s2) (subst_tt id0 s0 s3)
| sterm_call noret tailc t1 id1 lts1 => 
    sterm_call noret tailc t1 id1 
                 (List.map 
                   (fun (ts1:typ*sterm) => 
                    let (t1,s1):=ts1 in 
                    (t1, (subst_tt id0 s0 s1))
                   ) 
                   lts1)
end
with subst_tm (id0:id) (s0:sterm) (m:smem) : smem :=
match m with 
| smem_init => smem_init
| smem_malloc m1 t1 sz align => smem_malloc (subst_tm id0 s0 m1) t1 sz align
| smem_free m1 t1 s1 => smem_free (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1)
| smem_alloca m1 t1 sz align => smem_alloca (subst_tm id0 s0 m1) t1 sz align
| smem_load m1 t1 s1 => smem_load (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1)
| smem_store m1 t1 s1 s2 => smem_store (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
end
.

Fixpoint subst_mt (sm:smap) (s:sterm) : sterm :=
match sm with
| nil => s
| (id0, s0)::sm' => subst_mt sm' (subst_tt id0 s0 s)
end.

Fixpoint subst_mm (sm:smap) (m:smem) : smem :=
match sm with
| nil => m
| (id0, s0)::sm' => subst_mm sm' (subst_tm id0 s0 m)
end.

Fixpoint list_param__list_typ_subst_sterm (list_param1:list_param) (sm:smap) : list (typ*sterm) :=
match list_param1 with
| nil => nil
| (t, v)::list_param1' => (t, (subst_mt sm (sterm_val v)))::(list_param__list_typ_subst_sterm list_param1' sm)
end.

Definition se_cmd (st : sstate) (i:cmd) : sstate :=
match i with 
| insn_bop id0 op0 sz0 v1 v2 => 
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_bop op0 sz0 
                     (subst_mt st.(STerms) (sterm_val v1))
                     (subst_mt st.(STerms) (sterm_val v2))))
                 st.(SMem)
                 st.(Effects))
| insn_extractvalue id0 t1 v1 cs3 =>
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_extractvalue t1 
                     (subst_mt st.(STerms) (sterm_val v1))
                     cs3))
                 st.(SMem) 
                 st.(Effects))
| insn_insertvalue id0 t1 v1 t2 v2 cs3 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_insertvalue 
                     t1 
                     (subst_mt st.(STerms) (sterm_val v1))
                     t2 
                     (subst_mt st.(STerms) (sterm_val v2))
                     cs3))
                 st.(SMem) 
                 st.(Effects))
| insn_malloc id0 t1 sz1 al1 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_malloc 
                     (subst_mm st.(STerms) st.(SMem)) 
                     t1 sz1 al1))
                 (smem_malloc 
                   (subst_mm st.(STerms) st.(SMem)) 
                   t1 sz1 al1)
                 st.(Effects))
| insn_free id0 t0 v0 =>  
       (mkSstate st.(STerms)
                (smem_free st.(SMem) t0 
                  (subst_mt st.(STerms) (sterm_val v0)))
                 st.(Effects))
| insn_alloca id0 t1 sz1 al1 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_alloca 
                     (subst_mm st.(STerms) st.(SMem)) t1 sz1 al1))
                 (smem_alloca 
                   (subst_mm st.(STerms) st.(SMem)) t1 sz1 al1)
                 st.(Effects))
| insn_load id0 t2 v2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_load 
                     (subst_mm st.(STerms) st.(SMem))
                     t2 
                     (subst_mt st.(STerms) (sterm_val v2))))
                 (smem_load 
                   (subst_mm st.(STerms) st.(SMem))
                   t2 
                   (subst_mt st.(STerms) (sterm_val v2)))
                 st.(Effects))
| insn_store id0 t0 v1 v2 =>  
       (mkSstate st.(STerms)
                 (smem_store 
                   (subst_mm st.(STerms) st.(SMem))
                   t0 
                   (subst_mt st.(STerms) (sterm_val v1))
                   (subst_mt st.(STerms) (sterm_val v2)))
                 st.(Effects))
| insn_gep id0 inbounds0 t1 v1 lv2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_gep inbounds0 t1 
                     (subst_mt st.(STerms) (sterm_val v1))
                     (List.map (subst_mt st.(STerms)) (List.map sterm_val lv2))))
                 st.(SMem) 
                 st.(Effects))
| insn_ext id0 op0 t1 v1 t2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_ext op0 t1 
                     (subst_mt st.(STerms) (sterm_val v1))
                     t2))
                 st.(SMem) 
                 st.(Effects))
| insn_cast id0 op0 t1 v1 t2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_cast op0 t1 
                     (subst_mt st.(STerms) (sterm_val v1))
                     t2))
                 st.(SMem) 
                 st.(Effects))
| insn_icmp id0 c0 t0 v1 v2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_icmp c0 t0 
                     (subst_mt st.(STerms) (sterm_val v1))
                     (subst_mt st.(STerms) (sterm_val v2))))
                 st.(SMem) 
                 st.(Effects))
| insn_select id0 v0 t0 v1 v2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_select 
                     (subst_mt st.(STerms) (sterm_val v0))
                     t0 
                     (subst_mt st.(STerms) (sterm_val v1))
                     (subst_mt st.(STerms) (sterm_val v2))))
                 st.(SMem) 
                 st.(Effects))
| insn_call id0 false tailc0 t1 id1 list_param1 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_call false tailc0 t1 id1 
                      (list_param__list_typ_subst_sterm list_param1 st.(STerms))))
                 st.(SMem) 
                 st.(Effects))
| insn_call id0 true tailc0 t1 id1 list_param1 =>  
       (mkSstate st.(STerms)
                 st.(SMem) 
                 ((sterm_call true tailc0 t1 id1 
                    (list_param__list_typ_subst_sterm list_param1 st.(STerms)))::st.(Effects)))
end.

Fixpoint _se_phinodes (st st0: sstate) (ps:list phinode) : sstate :=
match ps with
| nil => st
| insn_phi id0 t0 idls0::ps' =>  
    _se_phinodes 
     (mkSstate (updateSmap st.(STerms) id0 
                 (sterm_phi 
                   t0 
                   (List.map
                     (fun (idl:id*l) =>
                      let (id5, l5) := idl in
                      ((subst_mt st.(STerms) (sterm_val (value_id id5))), l5)
                     )
                     idls0
                   )
                 )
               )
               st.(SMem)
               st.(Effects))
     st0
     ps'
end.

Fixpoint se_phinodes (st: sstate) (ps:list phinode) := _se_phinodes st st ps.

Fixpoint se_cmds (st : sstate) (cs:list cmd) : sstate :=
match cs with
| nil => st
| c::cs' => se_cmds (se_cmd st c) cs'
end.

Definition se_terminator (st : sstate) (i:terminator) : sterminator :=
match i with 
| insn_return id0 t0 v0 => stmn_return t0 (subst_mt st.(STerms) (sterm_val v0))
| insn_return_void id0 => stmn_return_void
| insn_br id0 v0 l1 l2 => stmn_br (subst_mt st.(STerms) (sterm_val v0)) l1 l2
| insn_br_uncond id0 l0 => stmn_br_uncond l0
| insn_unreachable id0 => stmn_unreachable
end.

Definition se_block (st : sstate) (b:block) : sstate*sterminator :=
match b with
| block_intro l0 ps cs tmn =>
  let st0 := se_cmds (se_phinodes st ps) cs in
  (st0, se_terminator st0 tmn)
end.

Definition tv_block (b1 b2:block) :=
let (st1, tmn1) := se_block (mkSstate nil smem_init nil) b1 in
let (st2, tmn2) := se_block (mkSstate nil smem_init nil) b2 in
st1 = st2 /\ tmn1 = tmn2.

Fixpoint GVs2Nats (TD:layouts) (lgv:list GenericValue) (locals:GVMap) (globals:GVMap) : option (list nat):=
match lgv with
| nil => Some nil
| gv::lgv' => 
    match (GV2nat TD 32 gv) with
    | Some n =>
      match (GVs2Nats TD lgv' locals globals) with
      | Some ns => Some (n::ns)
      | None => None
      end
    | None => None
    end
end.

Inductive sterm_denotes_genericvalue : 
   layouts ->               (* CurTatgetData *)
   GVMap ->                 (* local registers *)
   GVMap ->                 (* global variables *)
   mem ->                   (* Memory *)
   sterm ->                 (* symbolic term *)
   GenericValue ->          (* value that denotes sterm *)
   Prop :=
| sterm_val_denotes : forall TD lc gl Mem v gv,
  getOperandValue TD v lc gl = Some gv ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_val v) gv
| sterm_bop_denotes : forall TD lc gl Mem op0 sz0 st1 st2 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  mbop TD op0 sz0 gv1 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_bop op0 sz0 st1 st2) gv3
| sterm_extractvalue_denotes : forall TD lc gl Mem t1 st1 idxs0 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  extractGenericValue TD lc gl t1 gv1 idxs0 = Some gv2 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_extractvalue t1 st1 idxs0) gv2
| sterm_insertvalue_denotes : forall TD lc gl Mem t1 st1 t2 st2 idxs0 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  insertGenericValue TD t1 gv1 lc gl idxs0 t2 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_insertvalue t1 st1 t2 st2 idxs0) gv3
| sterm_malloc_denotes : forall TD lc gl Mem sm0 t0 sz0 align0 tsz0 Mem' mb,
  getTypeAllocSize TD t0 = Some tsz0 ->
  malloc TD Mem (tsz0 * sz0) align0 = Some (Mem', mb) ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_malloc sm0 t0 sz0 align0) (ptr2GV TD (mb, 0))
| sterm_alloca_denotes : forall TD lc gl Mem sm0 t0 sz0 align0 tsz0 Mem' mb,
  getTypeAllocSize TD t0 = Some tsz0 ->
  malloc TD Mem (tsz0 * sz0) align0 = Some (Mem', mb) ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_alloca sm0 t0 sz0 align0) (ptr2GV TD (mb, 0))
| sterm_load_denotes : forall TD lc gl Mem sm0 t0 st0 gv0 mp0 gv1,
  sterm_denotes_genericvalue TD lc gl Mem st0 gv0 ->
  GV2ptr TD (getPointerSize TD) gv0 = Some mp0 ->
  mload TD Mem mp0 t0 = Some gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_load sm0 t0 st0) gv1
| sterm_gep_denotes : forall TD lc gl Mem ib0 t0 st0 sts0 gv0 gvs0 ns0 mp0 mp1,
  sterm_denotes_genericvalue TD lc gl Mem st0 gv0 ->
  sterms_denote_genericvalues TD lc gl Mem sts0 gvs0 ->
  GV2ptr TD (getPointerSize TD) gv0 = Some mp0 ->
  GVs2Nats TD gvs0 lc gl = Some ns0 ->
  mgep TD t0 mp0 ns0 = Some mp1 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_gep ib0 t0 st0 sts0) (ptr2GV TD mp1)
| sterm_ext_denotes : forall TD lc gl Mem op0 t1 st1 t2 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  mext TD op0 t1 gv1 t2 = Some gv2 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_ext op0 t1 st1 t2) gv2
| sterm_cast_denotes : forall TD lc gl Mem op0 t1 st1 t2 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  mcast TD op0 t1 gv1 t2 = Some gv2 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_cast op0 t1 st1 t2) gv2
| sterm_icmp_denotes : forall TD lc gl Mem cond0 t0 st1 st2 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  micmp TD cond0 t0 gv1 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_icmp cond0 t0 st1 st2) gv3
| sterm_select_denotes : forall TD lc gl Mem st0 t0 st1 st2 gv0 gv1 gv2 c0,
  sterm_denotes_genericvalue TD lc gl Mem st0 gv0 ->
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  GV2nat TD 1 gv0 = Some c0 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_select st0 t0 st1 st2) (if c0 then gv1 else gv2)
with sterms_denote_genericvalues : 
   layouts ->               (* CurTatgetData *)
   GVMap ->                 (* local registers *)
   GVMap ->                 (* global variables *)
   mem ->                   (* Memory *)
   list sterm ->            (* symbolic terms *)
   list GenericValue ->     (* values that denote sterms *)
   Prop :=
| sterms_nil_denotes_genericvalues : forall TD lc gl Mem,
  sterms_denote_genericvalues TD lc gl Mem nil nil
| sterms_cons_denotes_genericvalues : forall TD lc gl Mem sts st gvs gv,
  sterms_denote_genericvalues TD lc gl Mem sts gvs ->
  sterm_denotes_genericvalue TD lc gl Mem st gv ->
  sterms_denote_genericvalues TD lc gl Mem (st::sts) (gv::gvs)
with smem_denotes_mem : 
   layouts ->               (* CurTatgetData *)
   GVMap ->                 (* local registers *)
   GVMap ->                 (* global variables *)
   mem ->                   (* Memory *)
   smem ->                  (* symbolic mem *)
   mem ->                   (* value that denotes smem *)
   Prop :=
| smem_init_denotes : forall TD lc gl Mem,
  smem_denotes_mem TD lc gl Mem smem_init initmem
| smem_malloc_denotes : forall TD lc gl Mem sm0 t0 sz0 align0 tsz0 Mem' mb,
  getTypeAllocSize TD t0 = Some tsz0 ->
  malloc TD Mem (tsz0 * sz0) align0 = Some (Mem', mb) ->
  smem_denotes_mem TD lc gl Mem (smem_malloc sm0 t0 sz0 align0) Mem'
| smem_free_denotes : forall TD lc gl Mem sm0 t0 st0 gv0 mptr0 Mem',
  sterm_denotes_genericvalue TD lc gl Mem st0 gv0 ->
  GV2ptr TD (getPointerSize TD) gv0 = Some mptr0 ->
  free Mem mptr0 = Some Mem'->
  smem_denotes_mem TD lc gl Mem (smem_free sm0 t0 st0) Mem'
| smem_alloca_denotes : forall TD lc gl Mem sm0 t0 sz0 align0 tsz0 Mem' mb,
  getTypeAllocSize TD t0 = Some tsz0 ->
  malloc TD Mem (tsz0 * sz0) align0 = Some (Mem', mb) ->
  smem_denotes_mem TD lc gl Mem (smem_alloca sm0 t0 sz0 align0) Mem
| smem_load_denotes : forall TD lc gl Mem sm0 t0 st0 Mem0,
  smem_denotes_mem TD lc gl Mem sm0 Mem0 ->
  smem_denotes_mem TD lc gl Mem (smem_load sm0 t0 st0) Mem0
| smem_store_denotes : forall TD lc gl Mem sm0 t0 st1 st2 gv1 gv2 mptr2 Mem',
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  GV2ptr TD (getPointerSize TD) gv2 = Some mptr2 ->
  mstore TD Mem mptr2 t0 gv1 = Some Mem' ->
  smem_denotes_mem TD lc gl Mem (smem_store sm0 t0 st1 st2) Mem'
.

Definition sstate_denotes_state TD lc gl Mem sstate0 lc' gl' mem' :=
(forall id0 st0 gv',  
  binds id0 st0 sstate0.(STerms) ->
  lookupEnv TD id0 lc' gl' = Some gv' ->
  sterm_denotes_genericvalue TD lc gl Mem st0 gv') /\
smem_denotes_mem TD lc gl Mem sstate0.(SMem) mem' /\
(forall st0,
  In st0 sstate0.(Effects) ->
  exists gv', sterm_denotes_genericvalue TD lc gl Mem st0 gv'
  ).
