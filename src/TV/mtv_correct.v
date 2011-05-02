(*
Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import ZArith.
Require Import Metatheory.
Require Import Memory.
Require Import Values.
Require Import ssa_mem.
Require Import trace.
Require Import symexe_def.
Require Import assoclist.
Require Import ssa_props.
Require Import sub_tv_def.
Require Import sub_tv_dec.
Require Import sub_tv_infer.
Require Import sub_tv.
Require Import Coq.Bool.Sumbool.
Require Import symexe_tactic.
Require Import sub_tv_correct.

Definition mptr_has_basebound TD M vb ve vp : bool :=
match (GV2ptr TD (getPointerSize TD) vb, 
       GV2ptr TD (getPointerSize TD) ve,
       GV2ptr TD (getPointerSize TD) vp) with
| (Some (Vptr bb ob), Some (Vptr be oe), Some (Vptr bp op)) =>
  let '(lo,hi) := Memory.Mem.bounds M bp in
  bzeq bb be && bzeq bb bp && 
  bzeq (Integers.Int.unsigned 31 ob) lo && 
  bzeq (Integers.Int.unsigned 31 oe) hi           
| _ => false
end.

Definition fptr_has_basebound fs vb ve vp : bool :=
match (lookupFdefViaGVFromFunTable fs vb,
       lookupFdefViaGVFromFunTable fs ve,
       lookupFdefViaGVFromFunTable fs vp) with
| (Some fid1, Some fid2, Some fid3) => eq_id fid1 fid2 && eq_id fid3 fid3
| _ => false
end.        

(* fs: function table
 * lc: local variable mappings
*)
Fixpoint valid_metadata (TD:TargetData) (fs lc:GVMap) (M:mem) (md:metadata) 
  : bool :=
match md with
| nil => true
| (fid,lbl,nth,b,e,p,true)::md' =>
    match (lookupAL _ lc b, lookupAL _ lc e, lookupAL _ lc p) with
    | (Some vb, Some ve, Some vp) => mptr_has_basebound TD M vb ve vp
    | (None, None, None) => true
    | _ => false
    end && valid_metadata TD fs lc M md'
| (fid,lbl,nth,b,e,p,false)::md' => 
    match (lookupAL _ lc b, lookupAL _ lc e, lookupAL _ lc p) with
    | (Some vb, Some ve, Some vp) => fptr_has_basebound fs vb ve vp
    | (None, None, None) => true
    | _ => false
    end && valid_metadata TD fs lc M md'
end.

Definition valid_memdata_db (TD:TargetData) (M:mem) := 
  forall addrofp t p vaddrofb vaddrofe ps lc gl oresult M' vb ve vp fid
    addrofb addrofe,
  mload TD M addrofp (typ_pointer t) Align.One = Some vp ->
  is_hashLoadBaseBound fid = true ->
  callLib M fid (params2GVs TD 
    (p::(SBsyntax.pp8,vaddrofb)::(SBsyntax.pp8,vaddrofe)::ps) lc gl) = 
    Some (oresult, M', Rok) ->
  getOperandValue TD vaddrofb lc gl = Some addrofb ->
  getOperandValue TD vaddrofe lc gl = Some addrofe ->
  mload TD M' addrofb (typ_pointer (typ_int Size.Eight)) Align.One = Some vb ->
  mload TD M' addrofe (typ_pointer (typ_int Size.Eight)) Align.One = Some ve ->
  mptr_has_basebound TD M vb ve vp = true.

Definition flnbeps_to_metadata (md:flnbeps) : metadata :=
List.fold_left (fun accum => fun flnbep => 
  let '(fid, lnbep) := flnbep in
  List.fold_left (fun accum => fun lnbep =>
    let '(l1,nbep) := lnbep in
    List.fold_left (fun accum => fun nbep =>
      let '(n1,bep) := nbep in
      List.fold_left (fun accum => fun elt =>
        let '(b,e,p,flag) := elt in
        (fid,l1,n1,b,e,p,flag)::accum
        ) bep accum
      ) nbep accum
    ) lnbep accum
  ) md nil.

Lemma check_mptr_metadata__is__correct : forall Ps2 fid1 l1 i1 base bound ptr
  TD lc gl Mem vb ve vp fs md m2 flnbep,
  validate_metadata_from_module m2 flnbep = true ->
  flnbeps_to_metadata flnbep = md ->
  valid_metadata TD fs lc Mem md = true ->
  valid_memdata_db TD Mem = true ->
  check_mptr_metadata Ps2 fid1 l1 i1 base bound ptr = true ->
  sterm_denotes_genericvalue TD lc gl Mem base vb ->
  sterm_denotes_genericvalue TD lc gl Mem bound ve ->
  sterm_denotes_genericvalue TD lc gl Mem ptr vp ->
  mptr_has_basebound TD Mem vb ve vp = true.
(* We need to say
   1) il in l1 in fid1 in Ps1 in m1 <= Ps2 in m2
*)
Admitted.

Lemma mptr_has_basebound__eq_ptr_object : forall TD lc gl Mem ptr ptr' vb ve vp 
  vp',
  sterm_denotes_genericvalue TD lc gl Mem (get_ptr_object ptr) vp ->
  sterm_denotes_genericvalue TD lc gl Mem (get_ptr_object ptr') vp' ->
  eq_sterm (get_ptr_object ptr) (get_ptr_object ptr') ->
  mptr_has_basebound TD Mem vb ve vp = mptr_has_basebound TD Mem vb ve vp'.
Admitted.

Definition mptr_inbounds (TD:TargetData) M vb ve vp t : bool :=
match (GV2ptr TD (getPointerSize TD) vb, 
       GV2ptr TD (getPointerSize TD) ve,
       GV2ptr TD (getPointerSize TD) vp) with
| (Some (Vptr bb ob), Some (Vptr be oe), Some (Vptr bp op)) =>
  match getTypeAllocSize TD t with
  | None => false
  | Some tsz =>
    let '(lo,hi) := Memory.Mem.bounds M bp in
    bzeq bb be && bzeq bb bp && 
    Zle_bool (Integers.Int.unsigned 31 ob) (Integers.Int.unsigned 31 op) &&
    Zle_bool (Integers.Int.unsigned 31 op) 
             (Integers.Int.unsigned 31 oe + Size.to_Z tsz)
  end
| _ => false
end.

Definition pars_of_loadStoreDereferenceCheck t vp vb ve psafe :=
((typ_pointer t,vp)::
     (SBsyntax.p8,vb)::
     (SBsyntax.p8,ve)::
     (SBsyntax.i32,
      (value_const 
        (const_castop 
          castop_ptrtoint
          (const_gep false 
            (const_null t) 
            (Cons_list_const (const_int SBsyntax.sz32 1%Z) Nil_list_const)
          )
          SBsyntax.i32
        )
      )
     )::(SBsyntax.i32,psafe)::nil).

Axiom call_loadStoreDereferenceCheck : forall fid M TD t vp vb ve lc gl oresult
  b e p psafe r,
  is_loadStoreDereferenceCheck fid = true ->
  callLib M fid (params2GVs TD 
    (pars_of_loadStoreDereferenceCheck t vp vb ve psafe) lc gl) = 
    Some (oresult, M, r) ->
  getOperandValue TD vb lc gl = Some b ->
  getOperandValue TD ve lc gl = Some e ->
  getOperandValue TD vp lc gl = Some p ->
  (mptr_inbounds (TD:TargetData) M b e p t = true <-> r = Rok).
  
Lemma mtv_cmds_inv : forall Ps1 Ps2 fid l1 nbs2 cs2 id2 t2 v2 a2 TD lc gl ptr,
  mtv_cmds Ps1 Ps2 fid l1 nbs2 = true ->
  nbranchs2cmds nbs2 = cs2 ->
  getOperandValue TD v2 lc gl = Some ptr ->
  InCmdsB (insn_load id2 t2 v2 a2) cs2 -> 
  exists cs21, exists cs22, exists cs23,
  exists id1, exists nr1, exists tc1, exists rt1, exists ft, exists fid,
  exists t, exists vp, exists vb, exists ve, exists psafe, 
    cs2 = cs21 ++ 
    [insn_call id1 nr1 tc1 rt1 (value_const (const_gid ft fid))
      (pars_of_loadStoreDereferenceCheck t vp vb ve psafe)] ++ cs22 ++ 
    [insn_load id2 t2 v2 a2]++ cs23 /\
    is_loadStoreDereferenceCheck fid = true /\
    getOperandValue TD vp lc gl = Some ptr. 
Admitted.

Lemma mtv_cmds__is__correct : forall Ps1 Ps2 fid1 l1 TD lc1 als1 gl Mem1 fs 
  md m2 flnbep nbs2,
  validate_metadata_from_module m2 flnbep = true ->
  flnbeps_to_metadata flnbep = md ->
  valid_metadata TD fs lc1 Mem1 md = true ->
  valid_memdata_db TD Mem1 = true ->
  mtv_cmds Ps1 Ps2 fid1 l1 nbs2 = true ->
  (exists lc2, exists als2, exists Mem2, exists tr, exists r,
    SBopsem.dbCmds TD gl lc1 als1 Mem1 (nbranchs2cmds nbs2) lc2 als2 Mem2 tr r 
    /\
    valid_metadata TD fs lc2 Mem2 md = true).
Admitted.
*)

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)




