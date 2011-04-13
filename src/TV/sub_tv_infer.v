Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import Arith.
Require Import ZArith.
Require Import Metatheory.
Require Import symexe_def.
Require Import symexe_lib.
Require Import symexe_tactic.
Require Import assoclist.
Require Import eq_tv_dec.
Require Import sub_tv_dec.
Require Import Coq.Bool.Sumbool.
Require Import monad.

Export SimpleSE.

(* Syntactical equivalence *)
Definition eq_value (v v':value) := sumbool2bool _ _ (value_dec v v').
Definition tv_typ (t t':typ) := sumbool2bool _ _ (typ_dec t t').
Definition tv_align (a a':align) := sumbool2bool _ _ (Align.dec a a').
Definition eq_sterm (st st':sterm) := sumbool2bool _ _ (sterm_dec st st').
Definition eq_smem (sm sm':smem) := sumbool2bool _ _ (smem_dec sm sm').
Definition eq_id (i i':id) := sumbool2bool _ _ (id_dec i i').
Definition eq_const (c c':const) := sumbool2bool _ _ (const_dec c c').
Definition eq_l (l1 l2:l) := sumbool2bool _ _ (l_dec l1 l2).
Definition bzeq (x y:Z) := sumbool2bool _ _ (Coqlib.zeq x y).

(* true <-> id == @__hashLoadBaseBound *)
Axiom is_hashLoadBaseBound : id -> bool.

(* true <-> id == @__loadDereferenceCheck or @__storeDereferenceCheck 

void @__load(store)DereferenceCheck(
  i8* %base, i8* %bound, i8* %ptr, i32 %size_of_type, i32 %ptr_safe)
*)
Axiom is_loadStoreDereferenceCheck : id -> bool.

(* void @__callDereferenceCheck(i8* %base, i8* %bound, i8* %ptr) *)
Axiom is_callDereferenceCheck : id -> bool.

(* true <-> id == @__hashStoreBaseBound *)
Axiom is_hashStoreBaseBound : id -> bool.


Axiom eq_INT_Z : INT -> Z -> bool.

(***************************************************************)
(* Simplification w.r.t program equivalence. *)

(* cast does not change value. We can prove they have the same operational
 * semantics. *)
Fixpoint remove_cast_const (c:const) : const :=
match c with
| const_castop castop_bitcast c1 _ => remove_cast_const c1
| const_select c0 c1 c2 => 
    const_select c0 (remove_cast_const c1)(remove_cast_const c2) 
| _ => c
end.

Fixpoint remove_cast (st:sterm) : sterm :=
match st with
| sterm_cast castop_bitcast _ st1 _ => remove_cast st1
| sterm_select st0 t st1 st2 => 
    sterm_select st0 t (remove_cast st1)(remove_cast st2) 
| sterm_val (value_const c) => sterm_val (value_const (remove_cast_const c))
| _ => st
end.

(*
  return the object pointer, e.g.

  %2 = getelementptr i32* %ptr.05, i32 %i.04
  %bcast_ld_dref_bound = bitcast i32* %2 to i8*   

  We return %ptr.05.
*)
Fixpoint get_ptr_object_const (c:const) : const :=
match c with
| const_castop castop_bitcast c1 _ => get_ptr_object_const c1
| const_gep _ c1 _ => get_ptr_object_const c1
| const_select c0 c1 c2 => 
    const_select c0 (remove_cast_const c1)(remove_cast_const c2) 
| _ => c
end.

Fixpoint get_ptr_object (st:sterm) : sterm :=
match st with
| sterm_cast castop_bitcast _ st1 _ => get_ptr_object st1
| sterm_gep _ _ st1 _ => get_ptr_object st1
| sterm_select st0 t st1 st2 => 
    sterm_select st0 t (get_ptr_object st1)(get_ptr_object st2) 
| sterm_val (value_const c) => sterm_val (value_const (get_ptr_object_const c))
| _ => st
end.

Definition eq_sterm_upto_cast (st1 st2:sterm) : bool :=
eq_sterm (remove_cast st1) (remove_cast st2).

(***************************************************************)
(** LLVM.syntax -> Symexe.syntax 
 * 
   If a function returns a pointer, e.g.
     define i32* @test(i32 %mm) nounwind
   Softbound translates it to be
     define void @softbound_test({ i32*, i8*, i8* }* %shadow_ret, i32 %mm)

   %shadow_ret is a returned pointer with its base and bound.

   At callsite,
     %3 = tail call i32* @test(i32 %2) nounwind
   is translated to be

     call void @softbound_test({ i32*, i8*, i8* }* %ret_tmp, i32 %2)
     %3 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 0
     %4 = load i32** %3          
     %_base3 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 1
     %call_repl_base = load i8** %_base3       
     %_bound4 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 2
     %call_repl_bound = load i8** %_bound4   

   The idea is defining an abstract call (icall_ptr)
     {%3, %call_repl_base, %call_repl_bound} = 
       call void @softbound_test({ i32*, i8*, i8* }* %ret_tmp, i32 %2)
   that equals to the above seven instructions.

   icall_nptr presents a normal call.
*)

Inductive icall : Set :=
 | icall_nptr : id -> noret -> tailc -> typ -> value -> params -> icall
 | icall_ptr : id -> id -> id -> typ -> value -> id -> params -> icall.

Record isubblock := mkiSB
{
  iNBs : list nbranch;
  icall_cmd : icall
}.

Lemma isCall_inv : forall (c:cmd), isCall c = true -> 
  id * noret * tailc * typ * value * params.
Proof.
  destruct c; intros H; try solve [inversion H].
  split; auto.
Defined. 

(*
     %3 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 0
     %4 = load i32** %3          
     %_base3 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 1
     %call_repl_base = load i8** %_base3       
     %_bound4 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 2
     %call_repl_bound = load i8** %_bound4    
*)

(* Check if tid is { i32*, i8*, i8* } *)
Fixpoint get_named_ret_typs nts tid {struct nts} : option (typ*typ*typ) :=
match nts with
| nil => None
| namedt_intro tid' t'::nts' =>
    if (eq_id tid tid') then
      match t' with
      | typ_namedt t0 => get_named_ret_typs nts' tid
      | typ_struct 
         (Cons_list_typ (typ_pointer _ as t01) 
         (Cons_list_typ (typ_pointer _ as t02)
         (Cons_list_typ (typ_pointer _ as t03) Nil_list_typ))) =>
         Some (t01,t02,t03)
      | _ => None
      end
    else get_named_ret_typs nts' tid
end.

(* Check if t is { i32*, i8*, i8* } *)
Fixpoint get_ret_typs nts t: option (typ*typ*typ) :=
match t with
| typ_struct 
    (Cons_list_typ (typ_pointer _ as t01) 
    (Cons_list_typ (typ_pointer _ as t02)
    (Cons_list_typ (typ_pointer _ as t03) Nil_list_typ))) =>
      Some (t01,t02,t03)
| typ_namedt tid => get_named_ret_typs nts tid
| _ => None
end.

(* Constructing a icall_ptr from the six instructions. *)
Definition gen_icall nts (v:value) (pa0:params) (c1 c2 c3 c4 c5 c6:cmd) 
  : option icall :=
match c1 with
|insn_gep id11 _ t1 (value_id id12)
   (Cons_list_value (value_const (const_int _ i11 as c11)) 
     (Cons_list_value (value_const (const_int _ i12 as c12)) 
      Nil_list_value)) =>
  match c2 with
  |insn_load id21 t2 (value_id id22) _ =>
    match c3 with 
    |insn_gep id31 _ t3 (value_id id32) 
       (Cons_list_value (value_const (const_int _ i31 as c31)) 
         (Cons_list_value (value_const (const_int _ i32 as c32)) 
         Nil_list_value)) =>
      match c4 with
      |insn_load id41 t4 (value_id id42) _ =>
        match c5 with
        |insn_gep id51 _ t5 (value_id id52)
           (Cons_list_value (value_const (const_int _ i51 as c51)) 
           (Cons_list_value (value_const (const_int _ i52 as c52)) 
              Nil_list_value)) =>
           match c6 with
           |insn_load id61 t6 (value_id id62) _ =>
              match pa0 with
              | (typ_pointer t0, value_id id0)::pa0' =>
                if (tv_typ t1 t3 && tv_typ t3 t5 && tv_typ t5 t0 &&
                    eq_id id0 id12 && eq_id id0 id32 && eq_id id0 id52 &&
                    eq_id id11 id22 && eq_id id31 id42 && eq_id id51 id62 &&
                    eq_const c11 c12 && eq_const c11 c31 && eq_const c11 c51 &&
                    eq_INT_Z i11 0%Z && eq_INT_Z i32 1%Z && eq_INT_Z i52 2%Z
                   ) 
                then 
                  match get_ret_typs nts t0 with
                  | Some (t01, t02, t03) => 
                    if (tv_typ t2 t01 && tv_typ t4 t02 && 
                        tv_typ t6 t03 && tv_typ t02 t03 &&
                        tv_typ t02 (typ_pointer (typ_int Size.Eight))) then
                      Some (icall_ptr id21 id41 id61 t2 v id0 pa0')
                    else None
                  | _ => None
                  end
                else None
              | _ => None
              end
           | _ => None
           end
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  | _ => None
  end
| _ => None
end.

Fixpoint cmds2isbs nts1 (Ps1:products) (cs:cmds) : (list isubblock*list nbranch)
  :=
match cs with
| nil => (nil,nil)
| c::cs' =>
  match (isCall_dec c) with
  | left isnotcall => 
    match (cmds2isbs nts1 Ps1 cs') with
    | (nil, nbs0) => (nil, mkNB c isnotcall::nbs0) 
    | (mkiSB nbs call0::sbs', nbs0) => 
      (mkiSB (mkNB c isnotcall::nbs) call0::sbs', nbs0) 
    end
  | right iscall => 
    let '(id1, nr1, tc1, t1, v1, pa1) := isCall_inv c iscall in
    let '(sbs, nbs0, ic) :=
(*
    The [c] is in the output program. So we don't know if it returns pointer
    w/o its signature in its input.

    But we do not check if the called function returns ptr. The problem is
    v1 can be a value that represents a function pointer. Statically, we 
    need more work to identify it.

    We check this property at tv_call.
*)
        match cs' with
        | c1::c2::c3::c4::c5::c6::cs'' =>
          match (gen_icall nts1 v1 pa1 c1 c2 c3 c4 c5 c6) with
          | Some ic => (cmds2isbs nts1 Ps1 cs'', ic)
          | None => (cmds2isbs nts1 Ps1 cs', icall_nptr id1 nr1 tc1 t1 v1 pa1)
          end
        | _ => (cmds2isbs nts1 Ps1 cs', icall_nptr id1 nr1 tc1 t1 v1 pa1)
        end
    in (mkiSB nil ic::sbs, nbs0) 
  end
end.

Inductive wf_inbranchs : list nbranch -> Prop :=
| wf_inbranchs_intro : forall nts Ps cs nbs, 
  cmds2isbs nts Ps cs = (nil, nbs) ->
  NoDup (getCmdsIDs cs) ->
  wf_inbranchs nbs.

Inductive wf_isubblock : isubblock -> Prop :=
| wf_isubblock_intro : forall nbs call0, 
  wf_inbranchs nbs ->
  wf_isubblock (mkiSB nbs call0).

Inductive wf_isubblocks : list isubblock -> Prop :=
| wf_isubblocks_nil : wf_isubblocks nil
| wf_isubblocks_cons : forall sb sbs,
  wf_isubblock sb ->
  wf_isubblocks sbs ->
  wf_isubblocks (sb::sbs).

Inductive wf_iblock : block -> Prop :=
| wf_iblock_intro : forall nts Ps l ps cs sbs nbs tmn, 
  cmds2isbs nts Ps cs = (sbs,nbs) ->
  wf_isubblocks sbs ->
  wf_inbranchs nbs ->
  wf_iblock (block_intro l ps cs tmn).

Hint Constructors wf_isubblocks.

(************************************************************)
(* Generating metadata *) 

(* The label of arg. *)
Axiom l_of_arg : unit -> l.

(* base, bound, ptr, flag (true:mem ptr, false:fptr) *)
Definition beps := list (id * id * id * bool).
(*
   We assign indices for phi, subblocks and appendent cmds inside a block, like 
   phi_n+1 s_n s_n-1 ... s_2 s_1 c_0

   At the (l_of_arg tt) block there is one subblock --- the 0th.
 *)
Definition nbeps := list (nat * beps).
Definition lnbeps := list (l * nbeps).          (* block label * nbeps *)
Definition flnbeps := list (id * lnbeps).       (* function name * lnbeps *)

(* add b e p if they are not in md *)
Fixpoint add_bep (md:beps) (b e p:id) (im:bool): beps :=
match md with
| nil => [(b,e,p,im)]
| (b',e',p',im')::md' => 
    if (eq_id b b' && eq_id e e' && eq_id p p' && eqb im im') then md
    else (b',e',p',im')::add_bep md' b e p im
end.

Fixpoint add_beps (accum bep:beps): beps :=
match bep with
| nil => accum
| (b,e,p,im)::bep' =>
  add_beps (add_bep accum b e p im) bep'
end.

(* update if exists, add it otherwise *)
Fixpoint updateAdd_nbeps (m:nbeps) (i:nat) (gv:beps) : nbeps :=
match m with
| nil => (i, gv)::nil
| (i', gv')::m' =>
  if (beq_nat i i')
  then (i', gv)::m'
  else (i', gv')::updateAdd_nbeps m' i gv
end.

(* update only if exists, do nothing otherwise *)
Fixpoint update_nbeps (m:nbeps) (i:nat) (gv:beps) : nbeps :=
match m with
| nil => nil
| (i', gv')::m' =>
  if (beq_nat i i')
  then (i', gv)::m'
  else (i', gv')::update_nbeps m' i gv
end.

Fixpoint lookup_nbeps (m:nbeps) (i:nat) : option beps :=
match m with
| nil => None
| (i', gv')::m' =>
  if (beq_nat i i')
  then Some gv'
  else lookup_nbeps m' i
end.

(* If assert(b<=e<p), and b e p are defined wrt open variables,
   add those open variables.

   Assumption:
   1) Used within a subblock
   2) b e p must be created all together
   3) Within a subblock, b e can only be bitcasted or selected, 
      p can only be gep-ed or selected. 
*)
Fixpoint metadata_from_bep_aux (base bound ptr:sterm) im (accum:beps) : beps :=
match (base, bound, ptr) with
| (sterm_val (value_id b), sterm_val (value_id e), sterm_val (value_id p)) => 
    add_bep accum b e p im
| (sterm_select st10 _ st11 st12, sterm_select st20 _ st21 st22, 
   sterm_select st30 _ st31 st32) =>
    if (eq_sterm st10 st20 && eq_sterm st20 st30) then
      metadata_from_bep_aux st11 st21 st31 im
        (metadata_from_bep_aux st12 st22 st32 im accum)
    else accum
| _ => accum
end.

Definition metadata_from_bep (base bound ptr:sterm) im (accum:beps) : beps :=
  metadata_from_bep_aux (remove_cast base) (remove_cast bound) 
    (get_ptr_object ptr) im accum.

Fixpoint metadata_from_smem (sm:smem) (accum:beps) : beps :=
match sm with
| smem_init => accum
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _ 
| smem_store sm1 _ _ _ _ => metadata_from_smem sm1 accum
| smem_lib sm1 lid1 sts1 =>
    metadata_from_smem sm1
    (if (is_loadStoreDereferenceCheck lid1) then
      match sts1 with
      |  Cons_list_sterm base 
        (Cons_list_sterm bound
        (Cons_list_sterm ptr
        (Cons_list_sterm _
        (Cons_list_sterm _ Nil_list_sterm)))) => 
          metadata_from_bep base bound ptr true accum
      | _ => accum
      end
    else 
      if (is_callDereferenceCheck lid1) then
      match sts1 with
      |  Cons_list_sterm base 
        (Cons_list_sterm bound
        (Cons_list_sterm ptr Nil_list_sterm)) => 
          metadata_from_bep base bound ptr false accum
      | _ => accum
      end
    else accum)
end.

(* The propagation case
   sm: symbolic results of a subblock
   md: the bep we found so far
   accum: it must be md initially

   We consider 3 cases:
   1) b e p are copied
   2) b e are copied
   3) p is copied

   All the other cases are conservatively ignored.
*) 
Fixpoint metadata_from_sterms_aux (sm:smap) (accum md:beps) : beps :=
match md with
| nil => accum
| (b,e,p,im)::md' =>
    metadata_from_sterms_aux sm
      (match (lookupAL _ sm b, lookupAL _ sm e, lookupAL _ sm p) with
      | (Some sb, Some se, Some sp) =>
          metadata_from_bep sb se sp im accum
      | (Some sb, Some se, None) =>
          match (remove_cast sb, remove_cast se) with
          | (sterm_val (value_id b'), sterm_val (value_id e')) => 
              add_bep accum b' e' p im
          | _ => accum
          end
      | (None, None, Some sp) =>
          match (get_ptr_object sp) with
          | sterm_val (value_id p') => add_bep accum b e p' im
          | _ => accum
          end
      |  _ => accum
      end) md'
end.

Fixpoint metadata_from_sterms (sm:smap) (accum:beps) : beps :=
  metadata_from_sterms_aux sm accum accum.

(* For correctness it does not matter whether metadata_from_smem is called
 * before metadata_from_sterms. But hopefully callling metadata_from_smem 
 * first can reduce some steps towards fixpoint, because it adds more bep
 * for metadata_from_sterms to propagate.
 *)
Definition metadata_from_cmds (nbs2 : list nbranch) (accum:beps) : beps :=
let st2 := se_cmds sstate_init nbs2 in 
let accum' := metadata_from_smem st2.(SMem) accum in
metadata_from_sterms st2.(STerms) accum'.

(* Parameters at callsite are some other resources of metadata. If a function
   has a pointer input, the pointer also has its base/bound as additional 
   inputs.
*)

(* We assume that the orders of ars and sars are matched. The function finds
   the corresponding sterm to arg with id i. 

  define fid2 (ars2) { ... }

  define fid ... {
    ...
  l1:
    call fid2 sars2
  }  
*)
Fixpoint lookupSarg (ars2:list (typ*id)) (sars2:list (typ*sterm)) (i:id) :
  option sterm :=
match (ars2, sars2) with
| (nil, nil) => None
| ((_,i')::ars2', (_,s')::sars2') =>
    if (eq_id i i') then Some s' else lookupSarg ars2' sars2' i
| _ => None
end.

(* ar_bep are base/bound in the arguments of function fid
   fid's arguments i args2
   sars2 is parameters supplied to fid at its callsite
*)
Fixpoint metadata_from_params (ar_bep:beps) ars2 sars2 
  (accum:beps) : beps :=
match ar_bep with
| nil => accum
| (b,e,p,im)::ar_bep' => metadata_from_params ar_bep' ars2 sars2 
    (match (lookupSarg ars2 sars2 b, lookupSarg ars2 sars2 e, 
      lookupSarg ars2 sars2 p) with
    | (Some sb, Some se, Some sp) => metadata_from_bep sb se sp im accum
    | _ => accum
    end)
end.

Definition get_arg_metadata (md:flnbeps) fid : beps :=
match lookupAL _ md fid with
| None => nil
| Some lnbeps => 
  match lookupAL _ lnbeps (l_of_arg tt) with
  | None => nil
  | Some nbeps => 
    match lookup_nbeps nbeps O with
    | None => nil
    | Some beps => beps
    end
  end
end.

Inductive sicall : Set :=
| stmn_icall_nptr : 
    id -> noret -> tailc -> typ -> sterm -> list (typ*sterm) -> sicall
| stmn_icall_ptr : 
    id -> id -> id -> typ -> sterm -> sterm -> list (typ*sterm) -> sicall
.

Definition se_icall (st:sstate) (i:icall) : sicall :=
match i with
| icall_nptr id0 nr tc t0 v0 p0 =>
    stmn_icall_nptr id0 nr tc t0 (value2Sterm st.(STerms) v0) 
      (list_param__list_typ_subst_sterm p0 st.(STerms))
| icall_ptr id0 id1 id2 t0 v0 id4 p0 =>
    stmn_icall_ptr id0 id1 id2 t0 (value2Sterm st.(STerms) v0) 
      (lookupSmap st.(STerms) id4)
      (list_param__list_typ_subst_sterm p0 st.(STerms))
end.

Definition metadata_from_iscall Ps2 (flnbep0:flnbeps) (accum:beps) (c2:sicall) 
  : beps :=
match c2 with
| stmn_icall_nptr _ _ _ _ t2 tsts2 =>
  match remove_cast t2 with
  | sterm_val (value_const (const_gid _ fid2)) =>
      if (isCallLib fid2) then accum
      else
        match (lookupFdefViaIDFromProducts Ps2 fid2) with
        | None => accum
        | Some (fdef_intro (fheader_intro _ _ args2) _) =>
           metadata_from_params (get_arg_metadata flnbep0 fid2) args2 tsts2 accum
        end
  | _ => accum
  end
| stmn_icall_ptr _ _ _ _ t2 _ tsts2 =>
  match remove_cast t2 with
  | sterm_val (value_const (const_gid _ fid2)) =>
      if (isCallLib fid2) then accum
      else
        match (lookupFdefViaIDFromProducts Ps2 fid2) with
        | Some (fdef_intro (fheader_intro _ _ (_::args2)) _) =>
           metadata_from_params (get_arg_metadata flnbep0 fid2) args2 tsts2 accum
        | _ => accum
        end
  | _ => accum
  end
end.

Definition metadata_from_isubblock Ps2 flnbep (sb2:isubblock)
  (accum:beps) : beps :=
match sb2 with
| mkiSB nbs2 call2 => 
  let st2 := se_cmds sstate_init nbs2 in 
  let cl2 := se_icall st2 call2 in
  let accum' := metadata_from_iscall Ps2 flnbep accum cl2 in
  let accum'' := metadata_from_sterms st2.(STerms) accum' in
  metadata_from_smem st2.(SMem) accum''
end.

(* Find beps not in cs2 *)
Fixpoint metadata_diff_cmds (md:beps) (cs2:cmds) : beps :=
match md with
| nil => md
| (b,e,p,im)::md' => 
    match lookupBindingViaIDFromCmds cs2 p with
    | id_binding_cmd _ => metadata_diff_cmds md' cs2
    | _ => (b,e,p,im)::metadata_diff_cmds md' cs2
    end
end.

Definition update_pred_subblock (accum:nbeps) nth bep : nbeps :=
 let bep_nth := 
   match lookup_nbeps accum (S nth) with
   | None => nil
   | Some bep_nth => bep_nth
   end in
 updateAdd_nbeps accum (S nth) (add_beps bep_nth bep).

(* The indices of subblocks are [1 .. len]. Subblocks are visited in a 
   reversed order. *)
Fixpoint metadata_from_isubblocks_aux Ps2 flnbep len (sbs2:list isubblock) 
  (accum:nbeps) : nbeps :=
match sbs2 with
| nil => accum
| sb2::sbs2' => 
    let nth := List.length sbs2' in
    let bep :=
      match lookup_nbeps accum nth with
      | Some bep => bep 
      | None => nil
      end in
    let bep' := metadata_from_isubblock Ps2 flnbep sb2 bep in
    let accum' := update_nbeps accum (len - nth) bep' in
    let accum'' := update_pred_subblock accum' nth 
      (metadata_diff_cmds bep' (nbranchs2cmds sb2.(iNBs))) in
    metadata_from_isubblocks_aux Ps2 flnbep len sbs2' accum''
end.

Definition metadata_from_isubblocks Ps2 flnbep (sbs2:list isubblock) 
  (accum:nbeps) : nbeps :=
metadata_from_isubblocks_aux Ps2 flnbep (List.length sbs2) (List.rev sbs2) accum.

(* from phinodes 
    b = phi b1 b2 ...
    e = phi e1 e2 ...
    p = phi p1 p2 ...
  We only consider the case where all b e p are from phinodes. Because
  the phinodes of b e are generated by Softbound if their corresponding p
  is a phinode.
*)
Fixpoint lookupPhinode (phs:phinodes) (i:id) :=
match phs with
| nil => None
| (insn_phi i' t vs)::phs' =>
    if (eq_dec i i') then Some (insn_phi i' t vs)
    else lookupPhinode phs' i
end.

(* adding md0 into the last subblock of block l1 *)
Definition update_block_metadata (accum:lnbeps) (l1:l) (md0:beps) : lnbeps :=
let nbep :=
  match lookupAL _ accum l1 with
  | None => nil
  | Some nbep => nbep
  end in
let bep :=
  match lookup_nbeps nbep 0 with
  | None => nil
  | Some bep => bep
  end in
let bep' := add_beps bep md0 in
let nbep' := updateAdd_nbeps nbep 0 bep' in
updateAL _ accum l1 nbep'.

Definition metadata_from_value l1 (bv ev pv:value) im (accum:lnbeps) : lnbeps :=
match (bv, ev, pv) with
| (value_id bid, value_id eid, value_id pid) => 
    update_block_metadata accum l1 [(bid, eid, pid, im)]
| _ => accum
end.

Fixpoint metadata_from_list_value_l (bvls evls pvls:list_value_l) im 
  (accum:lnbeps) : lnbeps :=
match bvls with
| Nil_list_value_l => accum
| Cons_list_value_l bv bl bvls' =>
    metadata_from_list_value_l bvls' evls pvls im
      (match (getValueViaLabelFromValuels evls bl,
             getValueViaLabelFromValuels pvls bl) with
      | (Some ev, Some pv) => metadata_from_value bl bv ev pv im accum
      | _ => accum
      end)
end.

Fixpoint metadata_from_phinodes (ps2:phinodes) (accum:lnbeps) (md:beps) 
  : lnbeps :=
match md with
| nil => accum
| (b,e,p,im)::md' =>
    metadata_from_phinodes ps2
      (match (lookupPhinode ps2 b, lookupPhinode ps2 e, lookupPhinode ps2 p) with
       | (None, None, None) => accum
       | (Some (insn_phi _ _ bvls), 
          Some (insn_phi _ _ evls), 
          Some (insn_phi _ _ pvls)) =>
            metadata_from_list_value_l bvls evls pvls im accum 
       | _ => accum
       end) md'
end.

(* adding md0 into blocks ls *)
Fixpoint updatePredBlocks (ls:list l) (accum:lnbeps) (md0:beps) : lnbeps :=
match ls with
| nil => accum
| l1::ls' => updatePredBlocks ls' (update_block_metadata accum l1 md0) md0
end.

(* Find beps not in ps2 *)
Fixpoint metadata_diff_phinodes (md:beps) (ps2:phinodes) : beps :=
match md with
| nil => md
| (b,e,p,im)::md' => 
    match lookupPhinode ps2 b with
    | None => (b,e,p,im)::metadata_diff_phinodes md' ps2
    | _ => metadata_diff_phinodes md' ps2
    end
end.

(* The beps not in the current ps2 and cs2 are falled-through from
   previous blocks. *)
Definition falling_through_metadata (md:beps) (b2:block) : beps :=
match b2 with
| block_intro l2 ps2 cs2 tmn2 =>
    metadata_diff_cmds (metadata_diff_phinodes md ps2) cs2
end.

(* Reimplement usedef, the one in ssa_lib is WRONG!!!!!!!!!! *)
Definition usedef_block := list (l*list l).

Definition update_udb (udb:usedef_block) (lu ld:l) : usedef_block :=
let ls :=
  match lookupAL _ udb ld with
  | Some ls => ls
  | None => nil
  end in
match (in_dec l_dec lu ls) with
| left _ => udb
| right _ => updateAddAL _ udb ld (lu::ls) 
end.

Definition genBlockUseDef_block b (udb:usedef_block) : usedef_block :=
match b with
| block_intro l0 _ _ tmn2 =>
  match tmn2 with
  | insn_br _ _ l1 l2 => update_udb (update_udb udb l0 l2) l0 l1
  | insn_br_uncond _ l1 => update_udb udb l0 l1
  | _ => udb
  end
end.

Fixpoint genBlockUseDef_blocks bs (udb:usedef_block) : usedef_block :=
match bs with
| nil => udb
| b::bs' => genBlockUseDef_blocks bs' (genBlockUseDef_block b udb)
end.

Definition genBlockUseDef_fdef f2 : usedef_block :=
match f2 with
| fdef_intro _ lb2 => genBlockUseDef_blocks lb2 nil
end.

Definition metadata_from_block nts1 Ps1 Ps2 flnbep (b2:block) (udb:usedef_block) 
  (lnbep:lnbeps) : lnbeps :=
match b2 with
| block_intro l2 ps2 cs2 tmn2 =>
  let (sbs2, nbs2) := cmds2isbs nts1 Ps1 cs2 in
  let nbep0 :=
    match lookupAL _ lnbep l2 with
    | None => nil
    | Some nbep => nbep
    end in
  let bep0 :=
    match lookup_nbeps nbep0 0 with
    | None => nil
    | Some bep => bep
    end in
  let bep1 := metadata_from_cmds nbs2 bep0 in
  let nbep1 := updateAdd_nbeps nbep0 0 bep1 in
  let nbep2 := update_pred_subblock nbep1 0 
    (metadata_diff_cmds bep1 (nbranchs2cmds nbs2)) in
  let nbep3 := metadata_from_isubblocks Ps2 flnbep sbs2 nbep2 in
  let lnbep' := updateAddAL _ lnbep l2 nbep3 in
  let bep_phi :=
    match lookup_nbeps nbep3 (List.length sbs2+1) with
    | None => nil
    | Some bep => bep
    end in
  let lnbep'' := metadata_from_phinodes ps2 lnbep' bep_phi in
  let preds := 
    match lookupAL _ udb l2 with
    | Some ls => ls
    | None => nil
    end in
  updatePredBlocks preds lnbep'' (metadata_diff_phinodes bep_phi ps2)
end.

Fixpoint metadata_from_blocks_aux nts1 Ps1 Ps2 flnbep (bs2:blocks) 
  (udb:usedef_block) (lnbep:lnbeps) : lnbeps :=
match bs2 with
| nil => lnbep
| b2::bs2' => metadata_from_blocks_aux nts1 Ps1 Ps2 flnbep bs2' udb 
    (metadata_from_block nts1 Ps1 Ps2 flnbep b2 udb lnbep)
end.

Fixpoint eq_nbeps (md1 md2:nbeps) : bool :=
match (md1, md2) with
| (nil, nil) => true
| ((n1,bep1)::md1', (n2,bep2)::md2') =>
    beq_nat n1 n2 && beq_nat (List.length bep1) (List.length bep2) &&
    eq_nbeps md1' md2'
| _ => false
end.

Fixpoint eq_lnbeps (md1 md2:lnbeps) : bool :=
match (md1, md2) with
| (nil, nil) => true
| ((l1,nbep1)::md1', (l2,nbep2)::md2') =>
    eq_l l1 l2 && eq_nbeps nbep1 nbep2 && eq_lnbeps md1' md2'
| _ => false
end.

Inductive onat :=
| Ozero : onat
| Osucc : onat -> onat.

Fixpoint metadata_from_blocks nts1 Ps1 Ps2 flbep (bs2:blocks) (udb:usedef_block) 
  (md:lnbeps) (bsteps:onat) : lnbeps :=
match bsteps with
| Ozero => md 
| Osucc bsteps' => 
  let md' := metadata_from_blocks_aux nts1 Ps1 Ps2 flbep bs2 udb md in
  if eq_lnbeps md md' then md'
  else metadata_from_blocks nts1 Ps1 Ps2 flbep bs2 udb md' bsteps'
end.

Fixpoint metadata_from_args (a:args) (md accum:beps) : beps :=
match md with
| nil => accum
| (b,e,p,im)::md' => 
    metadata_from_args a md'
      (match (lookupBindingViaIDFromArgs a b,
              lookupBindingViaIDFromArgs a e,
              lookupBindingViaIDFromArgs a p) with
       | (id_binding_arg _, id_binding_arg _, id_binding_arg _) =>
           add_bep accum b e p im
       | _ => accum
       end)
end.

Definition metadata_from_fdef nts1 Ps1 Ps2 flbep (f2:fdef) (md:lnbeps) 
  (bsteps:onat) : lnbeps :=
match f2 with
| fdef_intro ((fheader_intro t2 fid2 a2) as fh2) lb2 =>
  if (isCallLib fid2) then md 
  else 
   let accum := metadata_from_blocks nts1 Ps1 Ps2 flbep lb2 
     (genBlockUseDef_fdef f2) md bsteps in 
      match getEntryBlock f2 with
       | None => accum
       | Some (block_intro l2 _ _ _) =>
           match lookupAL _ accum l2 with
           | Some nbep => 
             match lookup_nbeps nbep (List.length nbep - 1) with
             | Some bep =>
               updateAddAL _ accum (l_of_arg tt) 
                 [(0, metadata_from_args a2 bep nil)]
             | None => accum
             end
           | _ => accum
           end
       end
end.

Fixpoint metadata_from_products_aux nts1 (Ps10 Ps20 Ps2:products) (md:flnbeps) 
  (bsteps:onat) : flnbeps :=
match Ps2 with
| nil => md
| product_fdef f2::Ps2' => 
    let lnbep0 := match lookupAL _ md (getFdefID f2) with
      | Some md => md 
      | None => nil
      end in 
    let lnbep := metadata_from_fdef nts1 Ps10 Ps20 md f2 lnbep0 bsteps in
    let md' := updateAddAL _ md (getFdefID f2) lnbep in
    metadata_from_products_aux nts1 Ps10 Ps20 Ps2' md' bsteps
| _::Ps2' => metadata_from_products_aux nts1 Ps10 Ps20 Ps2' md bsteps
end.

Fixpoint eq_flnbeps (md1 md2:flnbeps) : bool :=
match (md1, md2) with
| (nil, nil) => true
| ((f1,lnbeps1)::md1', (f2,lnbeps2)::md2') =>
    eq_id f1 f2 && eq_lnbeps lnbeps1 lnbeps2 && eq_flnbeps md1' md2'
| _ => false
end.

Fixpoint metadata_from_products nts1 (Ps1 Ps2:products) (md:flnbeps) 
  (bsteps:onat) (psteps:onat) : flnbeps :=
match psteps with
| Ozero => md 
| Osucc psteps' => 
  let md' := metadata_from_products_aux nts1 Ps1 Ps2 Ps2 md bsteps in
  if eq_flnbeps md md' then md'
  else metadata_from_products nts1 Ps1 Ps2 md' bsteps psteps'
end.

Definition metadata_from_module (m1 m2:module) (bsteps psteps:onat) :=
match (m1, m2) with
| (module_intro _ nts1 Ps1, module_intro _ _ Ps2) => 
    metadata_from_products nts1 Ps1 Ps2 nil bsteps psteps
end.

(************************************************************)
(* Validating metadata *) 

Definition validate_metadata_from_blocks nts1 Ps1 Ps2 flbep (bs2:blocks) 
  (udb:usedef_block) (md:lnbeps) : bool :=
let md' := metadata_from_blocks_aux nts1 Ps1 Ps2 flbep bs2 udb md in
eq_lnbeps md md'.

Fixpoint nbeps_to_beps (nbep:nbeps) (accum:beps) : beps :=
match nbep with
| nil => accum
| (_,bep)::nbep' => nbeps_to_beps nbep' bep++accum
end.

Fixpoint lnbeps_to_nbeps (lnbep:lnbeps) (accum:nbeps) : nbeps :=
match lnbep with
| nil => accum
| (_,nbep)::lnbep' => lnbeps_to_nbeps lnbep' nbep++accum
end.

Fixpoint in_beps (md:beps) (b e p:id) (im:bool): bool :=
match md with
| nil => false
| (b',e',p',im')::md' => 
    if (eq_id b b' && eq_id e e' && eq_id p p' && eqb im im') then true
    else in_beps md' b e p im
end.

Fixpoint disjoint_mptr_fptr_metadata_aux (bep:beps) : bool :=
match bep with
| nil => true
| (b,e,p,im)::bep' => (negb (in_beps bep' b e p (negb im))) && 
    disjoint_mptr_fptr_metadata_aux bep'
end.

Definition disjoint_mptr_fptr_metadata (md:lnbeps) : bool :=
disjoint_mptr_fptr_metadata_aux (nbeps_to_beps (lnbeps_to_nbeps md nil) nil).

Definition validate_metadata_from_fdef nts1 Ps1 Ps2 flbep (f2:fdef) (md:lnbeps) 
  : bool :=
match f2 with
| fdef_intro ((fheader_intro t2 fid2 a2) as fh2) lb2 =>
  if (isCallLib fid2) then true
  else 
    disjoint_mptr_fptr_metadata md &&
    validate_metadata_from_blocks nts1 Ps1 Ps2 flbep lb2 
      (genBlockUseDef_fdef f2) md &&
    match getEntryBlock f2 with
    | None => false
    | Some (block_intro l2 _ _ _) =>
        match lookupAL _ md l2 with
        | Some nbep => 
          match lookup_nbeps nbep (List.length nbep - 1) with
          | Some bep =>
             match lookupAL _ md (l_of_arg tt) with
             | None => false
             | Some nbep' => 
                eq_nbeps nbep' [(0, metadata_from_args a2 bep nil)]
             end
          | None => false
          end
        | _ => false
        end
    end
end.

Fixpoint validate_metadata_from_products_aux nts1 (Ps10 Ps20 Ps2:products) 
  (md:flnbeps) : bool :=
match Ps2 with
| nil => true
| product_fdef f2::Ps2' => 
    match lookupAL _ md (getFdefID f2) with
    | Some lnbep =>
        validate_metadata_from_fdef nts1 Ps10 Ps20 md f2 lnbep &&
        validate_metadata_from_products_aux nts1 Ps10 Ps20 Ps2' md
    | None => false
    end
| _::Ps2' => validate_metadata_from_products_aux nts1 Ps10 Ps20 Ps2' md
end.

Definition validate_metadata_from_module (m1 m2:module) (md:flnbeps) : bool :=
match (m1, m2) with
| (module_intro _ nts1 Ps1, module_intro _ _ Ps2) => 
    validate_metadata_from_products_aux nts1 Ps1 Ps2 Ps2 md
end.

(************************************************************)
(* Generating addrof base/bound *) 

Definition abes := list (id*id).

(* add addrof b e if they are not in *)
Fixpoint add_abes (md:abes) (ab ae:id) : abes :=
match md with
| nil => [(ab,ae)]
| (ab',ae')::md' => 
    if (eq_id ab ab' && eq_id ae ae') then md
    else (ab',ae')::add_abes md' ab ae
end.

Fixpoint addrofbe_from_smem (sm:smem) (accum:abes) : abes :=
match sm with
| smem_init => accum
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _ 
| smem_store sm1 _ _ _ _ => addrofbe_from_smem sm1 accum
| smem_lib sm1 lid1 sts1 =>
    addrofbe_from_smem sm1
    (if (is_hashLoadBaseBound lid1) then
      match sts1 with
      |  Cons_list_sterm _ 
        (Cons_list_sterm addr_of_base
        (Cons_list_sterm addr_of_bound
        (Cons_list_sterm _
        (Cons_list_sterm _
        (Cons_list_sterm _ Nil_list_sterm))))) =>
          match (addr_of_base, addr_of_bound) with
          | (sterm_val (value_id ab), sterm_val (value_id ae)) =>
              add_abes accum ab ae
          | _ => accum
          end
      | _ => accum
      end
    else accum)
end.
 
Definition addrofbe_from_cmds (nbs2 : list nbranch) (md:abes) : abes :=
let st2 := se_cmds sstate_init nbs2 in 
addrofbe_from_smem st2.(SMem) md.

Definition addrofbe_from_subblock (sb2:subblock) (md:abes) : abes :=
match sb2 with
| mkSB nbs2 _ _ => addrofbe_from_cmds nbs2 md
end.

Fixpoint addrofbe_from_subblocks (sbs2:list subblock) (md:abes) : abes :=
match sbs2 with
| nil => md
| sb2::sbs2' => addrofbe_from_subblocks sbs2' (addrofbe_from_subblock sb2 md)
end.

Definition addrofbe_from_block (b2:block) (md:abes) : abes :=
match b2 with
| block_intro l2 ps2 cs2 tmn2 =>
  let (sbs2, nbs2) := cmds2sbs cs2 in
  let accum1 := addrofbe_from_cmds nbs2 md in
  addrofbe_from_subblocks sbs2 accum1
end.

Fixpoint addrofbe_from_blocks (bs2:blocks) (md:abes) : abes :=
match bs2 with
| nil => md
| b2::bs2' => addrofbe_from_blocks bs2' (addrofbe_from_block b2 md)
end.

Definition addrofbe_from_fdef (f2:fdef) (md:abes) : abes :=
match f2 with
| fdef_intro ((fheader_intro t2 fid2 a2) as fh2) lb2 =>
  if (isCallLib fid2) then md 
  else addrofbe_from_blocks lb2 nil
end.

Definition fabes := list (id*abes).

Fixpoint addrofbe_from_products (Ps2:products) (md:fabes) : fabes :=
match Ps2 with
| nil => md
| product_fdef f2::Ps2' => 
    let abes := addrofbe_from_fdef f2 nil in
    let md' := updateAddAL _ md (getFdefID f2) abes in
    addrofbe_from_products Ps2' md'
| _::Ps2' => addrofbe_from_products Ps2' md
end.

Definition addrofbe_from_module (m2:module) :=
match m2 with
| module_intro _ _ Ps2 => addrofbe_from_products Ps2 nil
end.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
