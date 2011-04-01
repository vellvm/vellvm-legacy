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
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import opsem_pp.
Require Import trace.
Require Import symexe_def.
Require Import symexe_lib.
Require Import symexe_tactic.
Require Import seop_llvmop.
Require Import assoclist.
Require Import ssa_props.
Require Import eq_tv_dec.
Require Import sub_tv_dec.
Require Import Coq.Bool.Sumbool.

Export SimpleSE.

Definition tv_value (v v':value) := sumbool2bool _ _ (value_dec v v').
Definition tv_typ (t t':typ) := sumbool2bool _ _ (typ_dec t t').
Definition tv_align (a a':align) := sumbool2bool _ _ (Align.dec a a').
Definition eq_sterm (st st':sterm) := sumbool2bool _ _ (sterm_dec st st').
Definition eq_smem (sm sm':smem) := sumbool2bool _ _ (smem_dec sm sm').
Definition eq_id (i i':id) := sumbool2bool _ _ (id_dec i i').

(* This is the tricky part. How can we know sm2 includes sm1 ?
 * So far, we only consider the memory effects of Softbound. 
 *
 * The axiom assumes the memory behavior of a lib call. This should
 * be admissible in terms of other axioms.
*)
Axiom smem_lib_sub : id -> bool.

(* true <-> id == @__hashLoadBaseBound *)
Axiom is_hashLoadBaseBound : id -> bool.

(* true <-> id == @__loadDereferenceCheck or @__storeDereferenceCheck 

declare void @__loadDereferenceCheck(
  i8* %base, i8* %bound, i8* %ptr, i32 %size_of_type, i32 %ptr_safe
  )
*)
Axiom is_dereferenceCheck : id -> bool.

(* true <-> id == @__hashStoreBaseBound *)
Axiom is_hashStoreBaseBound : id -> bool.

(* We assume there is a way to know if ptr, base and bound are corresponding
   metadata. *)
Axiom get_metadata : unit -> list (id * id * id).

(* We need to know if an INT is one . *)
Axiom INT_is_one : INT -> bool.

(* Realized to check if two function names are matched. For example,
 * in Softbound, 'test' in the original program matches 'softbound_test'.
*)
Axiom rename_fid : id -> id.

(*
declare weak void @__hashLoadBaseBound(
  i8* %addr_of_ptr, 
  i8** %addr_of_base, 
  i8** %addr_of_bound, 
  i8* %actual_ptr, 
  i32 %size_of_type, 
  i32* %ptr_safe)

We assume 
  1) We have already checked that %base, %bound and %ptr_safe are valid 
     when being passed into @__hashLoadBaseBound. This is done by checking 
     if they equal to "alloca..." 
  2) __hashLoadBaseBound does not change %base, %bound and %ptr_safe.

So, %base, %bound and %ptr_safe are safe to load w/o memsafety checks.
*)
Fixpoint load_from_metadata (sm:smem) (st:sterm) : bool :=
match sm with
| smem_init => false
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _
| smem_store sm1 _ _ _ _ => load_from_metadata sm1 st
| smem_lib sm1 fid1 sts1 =>
  if (is_hashLoadBaseBound fid1) then
    match sts1 with
    |  Cons_list_sterm _ 
      (Cons_list_sterm addr_of_base
      (Cons_list_sterm addr_of_bound
      (Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm ptr_safe Nil_list_sterm))))) =>
      if (eq_sterm st addr_of_base || 
          eq_sterm st addr_of_bound || 
          eq_sterm st ptr_safe) 
      then true else load_from_metadata sm1 st
    | _ => load_from_metadata sm1 st
    end
  else load_from_metadata sm1 st
end.

Fixpoint tv_sterm (st st':sterm) : bool :=
match (st, st') with
| (sterm_val v, sterm_val v') => tv_value v v'
| (sterm_bop b sz st1 st2, sterm_bop b' sz' st1' st2') =>
  sumbool2bool _ _ (bop_dec b b') && sumbool2bool _ _ (Size.dec sz sz') &&
  tv_sterm st1 st1' && tv_sterm st2 st2'
| (sterm_fbop b f st1 st2, sterm_fbop b' f' st1' st2') =>
  sumbool2bool _ _ (fbop_dec b b') && 
  sumbool2bool _ _ (floating_point_dec f f') &&
  tv_sterm st1 st1' && tv_sterm st2 st2'
| (sterm_extractvalue t st1 cs, sterm_extractvalue t' st1' cs') =>
  tv_typ t t' && tv_sterm st1 st1' &&
  sumbool2bool _ _ (list_const_dec cs cs')
| (sterm_insertvalue t1 st1 t2 st2 cs, 
   sterm_insertvalue t1' st1' t2' st2' cs') =>
  tv_typ t1 t1' && tv_sterm st1 st1' && tv_typ t2 t2' && tv_sterm st2 st2' &&
  sumbool2bool _ _ (list_const_dec cs cs')
| (sterm_malloc sm t st1 a, sterm_malloc sm' t' st1' a') =>
  tv_smem sm sm' && tv_typ t t' && tv_sterm st1 st1' && tv_align a a'
| (sterm_alloca sm t st1 a, sterm_alloca sm' t' st1' a') =>
  tv_smem sm sm' && tv_typ t t' && tv_sterm st1 st1' && tv_align a a'
| (sterm_load sm t st1 a, sterm_load sm' t' st1' a') =>
  tv_smem sm sm' && tv_typ t t' && tv_sterm st1 st1' && tv_align a a'
| (sterm_gep i t st1 sts2, sterm_gep i' t' st1' sts2') =>
  sumbool2bool _ _ (bool_dec i i') && tv_typ t t' &&
  tv_sterm st1 st1' && tv_list_sterm sts2 sts2'
| (sterm_trunc top t1 st1 t2, sterm_trunc top' t1' st1' t2') =>
  sumbool2bool _ _ (truncop_dec top top') && tv_typ t1 t1' &&
  tv_sterm st1 st1' && tv_typ t2 t2'
| (sterm_ext eo t1 st1 t2, sterm_ext eo' t1' st1' t2') =>
  sumbool2bool _ _ (extop_dec eo eo') && tv_typ t1 t1' &&
  tv_sterm st1 st1' && tv_typ t2 t2' 
| (sterm_cast co t1 st1 t2, sterm_cast co' t1' st1' t2') =>
  sumbool2bool _ _ (castop_dec co co') && tv_typ t1 t1' &&
  tv_sterm st1 st1' && tv_typ t2 t2' 
| (sterm_icmp c t st1 st2, sterm_icmp c' t' st1' st2') =>
  sumbool2bool _ _ (cond_dec c c') && tv_typ t t' &&
  tv_sterm st1 st1' && tv_sterm st2 st2'
| (sterm_fcmp c ft st1 st2, sterm_fcmp c' ft' st1' st2') =>
  sumbool2bool _ _ (fcond_dec c c') &&
  sumbool2bool _ _ (floating_point_dec ft ft') &&
  tv_sterm st1 st1' && tv_sterm st2 st2'
| (sterm_phi t stls, sterm_phi t' stls') =>
  tv_typ t t' && tv_list_sterm_l stls stls'
| (sterm_select st1 t st2 st3, sterm_select st1' t' st2' st3') =>
  tv_sterm st1 st1' && tv_typ t t' && tv_sterm st2 st2' && tv_sterm st3 st3'
| (sterm_lib sm i sts, sterm_lib sm' i' sts') =>
  tv_smem sm sm' && eq_id i i' && tv_list_sterm sts sts'
| _ => false
end
with tv_list_sterm (sts sts':list_sterm) : bool :=
match (sts, sts') with
| (Nil_list_sterm, Nil_list_sterm) => true
| (Cons_list_sterm st sts0, Cons_list_sterm st' sts0') =>
  tv_sterm st st' && tv_list_sterm sts0 sts0'
| _ => false
end
with tv_list_sterm_l (stls stls':list_sterm_l) : bool :=
match (stls, stls') with
| (Nil_list_sterm_l, Nil_list_sterm_l) => true
| (Cons_list_sterm_l st l stls0, Cons_list_sterm_l st' l' stls0') =>
  tv_sterm st st' && sumbool2bool _ _ (l_dec l l') && 
  tv_list_sterm_l stls0 stls0'
| _ => false
end
with tv_smem (sm1 sm2:smem) : bool :=
match (sm1, sm2) with
| (smem_init, _) => true
| (smem_malloc sm1 t1 st1 a1, smem_malloc sm2 t2 st2 a2) =>
    tv_smem sm1 sm2 && tv_typ t1 t2 && tv_sterm st1 st2 && tv_align a1 a2
| (smem_alloca sm1 t1 st1 a1, smem_alloca sm2 t2 st2 a2) =>
    if (tv_typ t1 t2 && tv_sterm st1 st2 && tv_align a1 a2)
    then tv_smem sm1 sm2
    else tv_smem (smem_alloca sm1 t1 st1 a1) sm2
| (smem_free sm1 t1 st1, smem_free sm2 t2 st2) =>
    tv_smem sm1 sm2 && tv_typ t1 t2 && tv_sterm st1 st2
| (smem_load sm1 t1 st1 a1, smem_load sm2 t2 st2 a2) =>
    if (tv_typ t1 t2 && tv_sterm st1 st2 && tv_align a1 a2)
    then tv_smem sm1 sm2
    else tv_smem (smem_load sm1 t1 st1 a1) sm2
| (smem_store sm1 t1 st11 st12 a1, smem_store sm2 t2 st21 st22 a2) =>
    tv_smem sm1 sm2 && tv_typ t1 t2 && tv_sterm st11 st21 &&
    tv_sterm st12 st22 && tv_align a1 a2
| (smem_lib sm1 fid1 sts1, smem_lib sm2 fid2 sts2) => 
    if (eq_id fid1 fid2 && tv_list_sterm sts1 sts2)
    then tv_smem sm1 sm2
    else tv_smem (smem_lib sm1 fid1 sts1) sm2
| (sm1, smem_lib sm2 fid sts) => smem_lib_sub fid && tv_smem sm1 sm2
| (sm1, smem_alloca sm2 t2 st2 a2) => tv_smem sm1 sm2
| (sm1, smem_load sm2 t2 st2 a2) => 
  (* We check load_from_metadata to ensure that the behavior of output programs 
   * preserves input's. If we did not check, the additional load may be stuck. 
   *)
  tv_smem sm1 sm2 && load_from_metadata sm2 st2
| _ => false
end.

Fixpoint tv_sframe (sf1 sf2:sframe) : bool :=
match (sf1, sf2) with
| (sframe_init, _) => true
| (sframe_alloca sm1 sf1 t1 st1 a1, sframe_alloca sm2 sf2 t2 st2 a2) =>
    if (tv_smem sm1 sm2 && tv_typ t1 t2 && tv_sterm st1 st2 && tv_align a1 a2)
    then tv_sframe sf1 sf2
    else tv_sframe (sframe_alloca sm1 sf1 t1 st1 a1) sf2
| _ => false
end.

Fixpoint tv_smap (sm1 sm2:smap) : bool :=
match sm1 with
| nil => true
| (id1,st1)::sm1' =>
  match lookupAL _ sm2 id1 with
  | None => false
  | Some st2 => tv_sterm st1 st2 && tv_smap sm1' sm2
  end
end.

Definition sub_sstate s1 s2 := 
  tv_smap s1.(STerms) s2.(STerms) = true /\ 
  tv_smem s1.(SMem) s2.(SMem) = true /\
  tv_sframe s1.(SFrame) s2.(SFrame) = true /\ s1.(SEffects) = s2.(SEffects).

Notation "s1 <<= s2" := (sub_sstate s1 s2) (at level 70, no associativity).

Lemma sstate_sub_dec : forall (sts1 sts2:sstate), 
  uniq sts1.(STerms) -> {sts1<<=sts2} + {~sts1<<=sts2}.
Proof.
Ltac done_right' := 
  right; intro J ; destruct J as [ J1 [J2 [J3 J4]]]; simpl in *; auto.

  intros sts1 sts2 Huniq.
  destruct sts1 as [st1 sm1 sf1 se1].
  destruct sts2 as [st2 sm2 sf2 se2].
  destruct (@sterms_dec se1 se2); subst; try solve [done_right'].
  unfold sub_sstate. simpl.
  destruct (tv_smap st1 st2); auto.
  destruct (tv_smem sm1 sm2); auto.
  destruct (tv_sframe sf1 sf2); auto.
    right. intro J ; destruct J as [ J1 [J2 [J3 J4]]]. inversion J3.
    right. intro J ; destruct J as [ J1 [J2 [J3 J4]]]. inversion J2.
    right. intro J ; destruct J as [ J1 [J2 [J3 J4]]]. inversion J1.
Qed.

(* cast does not change value. We can prove they have the same operational
 * semantics. *)
Fixpoint remove_cast (st:sterm) : sterm :=
match st with
| sterm_cast _ _ st1 _ => remove_cast st1
| _ => st
end.

(*
  return the object pointer, e.g.

  %2 = getelementptr i32* %ptr.05, i32 %i.04
  %bcast_ld_dref_bound = bitcast i32* %2 to i8*   

  We return %ptr.05.
*)
Fixpoint get_ptr_object (st:sterm) : sterm :=
match st with
| sterm_cast _ _ st1 _ => get_ptr_object st1
| sterm_gep _ _ st1 _ => get_ptr_object st1
| _ => st
end.

Definition eq_sterm_upto_cast (st1 st2:sterm) : bool :=
eq_sterm (remove_cast st1) (remove_cast st2).

(* 
   ptr = load addr_of_ptr
   hashLoadBaseBound addr_of_ptr addr_of_b addr_of_e ptr _
*)
Fixpoint deref_from_metadata (sm:smem) (addr_of_b addr_of_e ptr:sterm) 
  : bool :=
match sm with
| smem_init => false
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _ => deref_from_metadata sm1 addr_of_b addr_of_e ptr
| smem_free sm1 _ _ => false
| smem_load sm1 _ _ _ => deref_from_metadata sm1 addr_of_b addr_of_e ptr
| smem_store sm1 _ _ _ _ => deref_from_metadata sm1 addr_of_b addr_of_e ptr
| smem_lib sm1 fid1 sts1 =>
    if (is_hashLoadBaseBound fid1) then
    match sts1 with
    |  Cons_list_sterm addr_of_ptr 
      (Cons_list_sterm addr_of_base
      (Cons_list_sterm addr_of_bound
      (Cons_list_sterm actual_ptr
      (Cons_list_sterm _
      (Cons_list_sterm _ Nil_list_sterm))))) =>
      if (eq_sterm_upto_cast addr_of_b addr_of_base &&
          eq_sterm_upto_cast addr_of_e addr_of_bound && 
          eq_sterm_upto_cast ptr actual_ptr) then
        match (remove_cast addr_of_ptr, remove_cast actual_ptr) with
        | (st1, sterm_load _ _ st2 _) => eq_sterm_upto_cast st1 st2
        | _ => false
        end
      else deref_from_metadata sm1 addr_of_b addr_of_e ptr
    | _ => deref_from_metadata sm1 addr_of_b addr_of_e ptr
    end      
    else deref_from_metadata sm1 addr_of_b addr_of_e ptr
end.

Fixpoint is_metadata_aux (ms:list (id*id*id)) (b e p:id) : bool :=
match ms with
| nil => false
| (b',e',p')::ms' => 
    if (eq_id b b' && eq_id e e' && eq_id p p') then true
    else is_metadata_aux ms' b e p
end.

Definition is_metadata (b e p:id) : bool :=
  is_metadata_aux (get_metadata tt) b e p.

Definition deref_check fid sts : bool :=
  if (is_dereferenceCheck fid || is_hashStoreBaseBound fid) then
    match sts with
    |  Cons_list_sterm base 
      (Cons_list_sterm bound
      (Cons_list_sterm ptr
      (Cons_list_sterm size_of_type
      (Cons_list_sterm _ Nil_list_sterm)))) =>
        match (remove_cast base, remove_cast bound, get_ptr_object ptr) with
        | (sterm_val (value_id idb), sterm_val (value_id ide), 
           sterm_val (value_id idp)) => 
            if (is_metadata idb ide idp) then true else false
        | (sterm_malloc _ _ _ _ as st1, 
           sterm_gep _ _ st2 
             (Cons_list_sterm 
               (sterm_val (value_const (const_int _ i))) 
               Nil_list_sterm),  
           sterm_malloc _ _ _ _ as st3) =>
             eq_sterm_upto_cast st1 st2 && 
             eq_sterm_upto_cast st1 st3 && 
             INT_is_one i
        | (sterm_load sm1 _ st1 _, sterm_load sm2 _ st2 _, st3) =>
           eq_smem sm1 sm2 && deref_from_metadata sm1 st1 st2 st3
        | _ => false
        end
    | _ => false
    end
  else true.

(* ptr is safe to access if ptr is asserted by a deref check or
   from hasLoadBaseBound *)
Fixpoint safe_mem_access (sm:smem) (ptr:sterm) : bool :=
match sm with
| smem_init => false
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _
| smem_store sm1 _ _ _ _ => safe_mem_access sm1 ptr
| smem_lib sm1 fid1 sts1 =>
  if (is_dereferenceCheck fid1) then
    match sts1 with
    |  Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm actual_ptr
      (Cons_list_sterm _
      (Cons_list_sterm _ Nil_list_sterm)))) =>
      if (eq_sterm (get_ptr_object ptr) (get_ptr_object actual_ptr)) 
      then true else safe_mem_access sm1 ptr
    | _ => safe_mem_access sm1 ptr
    end
  else if (is_hashLoadBaseBound fid1) then
    match sts1 with
    |  Cons_list_sterm _ 
      (Cons_list_sterm addr_of_base
      (Cons_list_sterm addr_of_bound
      (Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm ptr_safe Nil_list_sterm))))) =>
      if (eq_sterm ptr addr_of_base || 
          eq_sterm ptr addr_of_bound || 
          eq_sterm ptr ptr_safe) 
      then true else safe_mem_access sm1 ptr
    | _ => safe_mem_access sm1 ptr
    end
  else safe_mem_access sm1 ptr
end.

Fixpoint sterm_is_memsafe (st:sterm) : bool :=
match st with
| sterm_val v => true
| sterm_bop _ _ st1 st2 
| sterm_fbop _ _ st1 st2  
| sterm_icmp _ _ st1 st2 
| sterm_fcmp _ _ st1 st2 
| sterm_insertvalue _ st1 _ st2 _ => 
    sterm_is_memsafe st1 && sterm_is_memsafe st2 
| sterm_trunc _ _ st1 _
| sterm_ext _ _ st1 _ 
| sterm_cast _ _ st1 _ 
| sterm_extractvalue _ st1 _ => sterm_is_memsafe st1
| sterm_malloc sm _ st1 _
| sterm_alloca sm _ st1 _ => smem_is_memsafe sm && sterm_is_memsafe st1
| sterm_load sm _ st1 _ => 
   smem_is_memsafe sm && sterm_is_memsafe st1 && safe_mem_access sm st1
| sterm_gep _ _ st1 sts2 => sterm_is_memsafe st1 && list_sterm_is_memsafe sts2
| sterm_phi _ stls => list_sterm_l_is_memsafe stls
| sterm_select st1 _ st2 st3 => 
    sterm_is_memsafe st1 && sterm_is_memsafe st2 && sterm_is_memsafe st3
| sterm_lib sm fid sts => 
    smem_is_memsafe sm && list_sterm_is_memsafe sts && deref_check fid sts
end
with list_sterm_is_memsafe (sts:list_sterm) : bool :=
match sts with
| Nil_list_sterm => true
| Cons_list_sterm st sts0 => sterm_is_memsafe st && list_sterm_is_memsafe sts0
end
with list_sterm_l_is_memsafe (stls:list_sterm_l) : bool :=
match stls with
| Nil_list_sterm_l => true
| Cons_list_sterm_l st _ stls0 =>
    sterm_is_memsafe st && list_sterm_l_is_memsafe stls0
end
with smem_is_memsafe (sm:smem) : bool :=
match sm with
| smem_init => true
| smem_malloc sm1 _ st1 _
| smem_alloca sm1 _ st1 _ => smem_is_memsafe sm1 && sterm_is_memsafe st1
| smem_free sm1 _ _ => false
| smem_load sm1 _ st1 _ => 
    smem_is_memsafe sm1 && sterm_is_memsafe st1 && safe_mem_access sm1 st1
| smem_store sm1 _ st11 st12 _ =>
    smem_is_memsafe sm1 && sterm_is_memsafe st11 && 
    sterm_is_memsafe st12 && safe_mem_access sm1 st12
| smem_lib sm1 fid1 sts1 =>
    smem_is_memsafe sm1 && list_sterm_is_memsafe sts1 && deref_check fid1 sts1
end.

Definition tv_cmds (nbs1 nbs2 : list nbranch) :=
sumbool2bool _ _ (sstate_sub_dec (se_cmds sstate_init nbs1) (se_cmds sstate_init nbs2) (se_cmds_init_uniq nbs1)).

Definition mtv_cmds (nbs2 : list nbranch) :=
let st2 := se_cmds sstate_init nbs2 in 
smem_is_memsafe st2.(SMem).

(* Here, we check which function to call conservatively. In practice, a v1
 * is a function pointer, we should look up the function name from the 
 * FunTable. Since the LLVM IR takes function names as function pointers,
 * if a program does not assign them to be other variables, they should
 * be the same. *)
Fixpoint tv_params (tsts1 tsts2:list (typ*sterm)) : bool :=
match (tsts1, tsts2) with
| (nil, _) => true
| ((t1,st1)::tsts1', (t2,st2)::tsts2') => 
  tv_typ t1 t2 && tv_sterm st1 st2 && tv_params tsts1' tsts2'
| _ => false
end.

Definition tv_fid (fid1 fid2:id) := 
  eq_id (rename_fid fid1) fid2.

Axiom tv_fid_injective1 : forall fid1 fid2 fid1' fid2',
  fid1 = fid2 -> tv_fid fid1 fid1' -> tv_fid fid2 fid2' -> fid1' = fid2'.

Axiom tv_fid_injective2 : forall fid1 fid2 fid1' fid2',
  fid1 <> fid2 -> tv_fid fid1 fid1' -> tv_fid fid2 fid2' -> fid1' <> fid2'.

(* Do not check if their tailc flags match. Softbound changes the flag for
 * system calls, say atoi from tailcall to non-tailcall.
 *)
Definition tv_scall (c1 c2:scall) :=
  let '(stmn_call rid1 nr1 _ t1 v1 tsts1) := c1 in
  let '(stmn_call rid2 nr2 _ t2 v2 tsts2) := c2 in
  eq_id rid1 rid1 &&
  (sumbool2bool _ _ (noret_dec nr1 nr2)) &&
  tv_typ t1 t2 && tv_params tsts1 tsts2 &&
  match (v1, v2) with
  | (value_const (const_gid _ fid1), value_const (const_gid _ fid2)) => 
      tv_fid fid1 fid2
  | (v1, v2) => sumbool2bool _ _ (value_dec v1 v2)
  end.

Definition tv_subblock (sb1 sb2:subblock) :=
match (sb1, sb2) with
| (mkSB nbs1 call1 iscall1, mkSB nbs2 call2 iscall2) =>
  let st1 := se_cmds sstate_init nbs1 in
  let st2 := se_cmds sstate_init nbs2 in
  let cl1 := se_call st1 call1 iscall1 in
  let cl2 := se_call st2 call2 iscall2 in
   (sumbool2bool _ _ (sstate_sub_dec st1 st2 (se_cmds_init_uniq nbs1)))
end.

Definition mtv_subblock (sb2:subblock) :=
match sb2 with
| mkSB nbs2 call2 iscall2 =>
  let st2 := se_cmds sstate_init nbs2 in
   smem_is_memsafe st2.(SMem)
end.

Fixpoint tv_subblocks (sbs1 sbs2:list subblock) :=
match (sbs1, sbs2) with
| (nil, nil) => true
| (sb1::sbs1', sb2::sbs2') => 
   (tv_subblock sb1 sb2) && (tv_subblocks sbs1' sbs2')
| _ => false
end.

Fixpoint mtv_subblocks (sbs2:list subblock) :=
match sbs2 with
| nil => true
| sb2::sbs2' => mtv_subblock sb2 && mtv_subblocks sbs2'
end.

Fixpoint lookupPhinode (phs:phinodes) (i:id) :=
match phs with
| nil => None
| (insn_phi i' t vs)::phs' =>
    if (eq_dec i i') then Some (insn_phi i' t vs)
    else lookupPhinode phs' i
end.

(* FIXME: Check phinode is memsafe.*)
Fixpoint tv_phinodes (ps1 ps2:phinodes) : bool :=
match ps1 with
| nil => true
| (insn_phi i1 _ _)as p1::ps1' =>
  match lookupPhinode ps2 i1 with
  | None => false
  | Some p2 => 
    sumbool2bool _ _ (phinode_dec p1 p2) && tv_phinodes ps1' ps2
  end
end.

Definition tv_block (b1 b2:block) :=
match (b1, b2) with
| (block_intro l1 ps1 cs1 tmn1, block_intro l2 ps2 cs2 tmn2) =>
  match (cmds2sbs cs1, cmds2sbs cs2) with
  | ((sbs1, nbs1), (sbs2, nbs2)) =>
    sumbool2bool _ _ (eq_atom_dec l1 l2) &&
    tv_phinodes ps1 ps2 &&
    tv_subblocks sbs1 sbs2 &&
    tv_cmds nbs1 nbs2 &&
    sumbool2bool _ _ (terminator_dec tmn1 tmn2)
  end
end.

Definition mtv_block (b2:block) :=
match b2 with
| block_intro l2 ps2 cs2 tmn2 =>
  match cmds2sbs cs2 with
  | (sbs2, nbs2) =>
    mtv_subblocks sbs2 && mtv_cmds nbs2
  end
end.

Fixpoint tv_blocks (bs1 bs2:blocks):=
match (bs1, bs2) with
| (nil, nil) => true
| (b1::bs1', b2::bs2') => tv_block b1 b2 && tv_blocks bs1' bs2'
| _ => false
end.

Fixpoint mtv_blocks (bs2:blocks):=
match bs2 with
| nil => true
| b2::bs2' => mtv_block b2 && mtv_blocks bs2'
end.

Definition tv_fheader (f1 f2:fheader) := 
  let '(fheader_intro t1 fid1 a1) := f1 in
  let '(fheader_intro t2 fid2 a2) := f2 in
  (sumbool2bool _ _ (typ_dec t1 t2)) &&
  tv_fid fid1 fid2 &&
  (sumbool2bool _ _ (prefix_dec _ arg_dec a1 a2)).

Definition tv_fdec (f1 f2:fdec) :=
match (f1, f2) with
| (fdec_intro fh1, fdec_intro fh2) => tv_fheader fh1 fh2
end.

Definition tv_fdef (f1 f2:fdef) :=
match (f1, f2) with
| (fdef_intro fh1 lb1, fdef_intro fh2 lb2) =>
  tv_fheader fh1 fh2 && tv_blocks lb1 lb2
end.

Definition mtv_fdef (f2:fdef) :=
match f2 with
| fdef_intro ((fheader_intro t2 fid2 a2) as fh2) lb2 =>
  if (isCallLib fid2) then true else mtv_blocks lb2
end.

Fixpoint lookupGvarViaIDFromProducts (lp:products) (i:id) : option gvar :=
match lp with
| nil => None
| (product_gvar gv)::lp' => 
    if (eq_dec (getGvarID gv) i) then Some gv
    else lookupGvarViaIDFromProducts lp' i
| _::lp' => lookupGvarViaIDFromProducts lp' i
end.

Fixpoint tv_products (Ps1 Ps2:products) : bool :=
match Ps1 with
| nil => true
| product_gvar gv1::Ps1' =>
  match lookupGvarViaIDFromProducts Ps2 (getGvarID gv1) with
  | None => false
  | Some gv2 => sumbool2bool _ _ (gvar_dec gv1 gv2) && tv_products Ps1' Ps2 
  end
| product_fdec f1::Ps1' =>
  match lookupFdecViaIDFromProducts Ps2 (rename_fid (getFdecID f1)) with
  | None => false
  | Some f2 => tv_fdec f1 f2 && tv_products Ps1' Ps2 
  end
| product_fdef f1::Ps1' =>
  match lookupFdefViaIDFromProducts Ps2 (rename_fid (getFdefID f1)) with
  | None => false
  | Some f2 => tv_fdef f1 f2 && tv_products Ps1' Ps2 
  end
end.

Fixpoint mtv_products (Ps2:products) : bool :=
match Ps2 with
| nil => true
| product_fdef f2::Ps2' => mtv_fdef f2 && mtv_products Ps2'
| _::Ps2' => mtv_products Ps2'
end.

Definition tv_module (m1 m2:module) :=
match (m1, m2) with
| (module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2) =>
  sumbool2bool _ _ (layouts_dec los1 los2) &&
  sumbool2bool _ _ (namedts_dec nts1 nts2) &&
  tv_products Ps1 Ps2
end.

Definition mtv_module (m2:module) :=
match m2 with
| module_intro los2 nts2 Ps2 => mtv_products Ps2
end.

Fixpoint tv_system (S1 S2:system) :=
match (S1, S2) with
| (nil, nil) => true
| (m1::S1', m2::S2') => tv_module m1 m2 && tv_system S1' S2'
| _ => false
end.

Ltac sumbool_simpl :=
  repeat
  match goal with
  | [ H:sumbool2bool _ _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:is_true(sumbool2bool _ _ _) |- _ ] => apply sumbool2bool_true in H
  | [ H:tv_cmds _ _ = true |- _ ] => unfold is_true in H; apply sumbool2bool_true in H
  | [ H:is_true(tv_cmds _ _) |- _ ] => unfold is_true in H; apply sumbool2bool_true in H
  end.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
