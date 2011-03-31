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

(* This is the tricky part. How can we know sm2 includes sm1 ?
 * So far, we only consider the memory effects of Softbound. 
 *
 * The axiom assumes the memory behavior of a lib call. This should
 * be admissible in terms of other axioms.
*)
Axiom smem_lib_sub : id -> bool.

Definition tv_value (v v':value) := sumbool2bool _ _ (value_dec v v').
Definition tv_typ (t t':typ) := sumbool2bool _ _ (typ_dec t t').
Definition tv_align (a a':align) := sumbool2bool _ _ (Align.dec a a').

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
  tv_smem sm sm' && sumbool2bool _ _ (id_dec i i') && tv_list_sterm sts sts'
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
    if (tv_typ t1 t2 && tv_sterm st11 st21 &&
        tv_sterm st12 st22 && tv_align a1 a2)
    then tv_smem sm1 sm2
    else tv_smem (smem_store sm1 t1 st11 st12 a1) sm2
| (smem_lib sm1 fid1 sts1, smem_lib sm2 fid2 sts2) => 
    if (sumbool2bool _ _ (id_dec fid1 fid2) && tv_list_sterm sts1 sts2)
    then tv_smem sm1 sm2
    else tv_smem (smem_lib sm1 fid1 sts1) sm2
| (sm1, smem_lib sm2 fid sts) => smem_lib_sub fid && tv_smem sm1 sm2
| (sm1, smem_alloca sm2 t2 st2 a2) => tv_smem sm1 sm2
| (sm1, smem_load sm2 t2 st2 a2) => tv_smem sm1 sm2
| (sm1, smem_store sm2 t2 st21 st22 a2) => tv_smem sm1 sm2
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

Definition tv_cmds (nbs1 nbs2 : list nbranch) :=
sumbool2bool _ _ (sstate_sub_dec (se_cmds sstate_init nbs1) (se_cmds sstate_init nbs2)
                    (se_cmds_init_uniq nbs1)).

(* Realized to check if two function names are matched. For example,
 * in Softbound, 'test' in the original program matches 'softbound_test'.
*)
Axiom rename_fid : id -> id.

Definition tv_fid (fid1 fid2:id) := 
  sumbool2bool _ _ (id_dec (rename_fid fid1) fid2).

Axiom tv_fid_injective1 : forall fid1 fid2 fid1' fid2',
  fid1 = fid2 -> tv_fid fid1 fid1' -> tv_fid fid2 fid2' -> fid1' = fid2'.

Axiom tv_fid_injective2 : forall fid1 fid2 fid1' fid2',
  fid1 <> fid2 -> tv_fid fid1 fid1' -> tv_fid fid2 fid2' -> fid1' <> fid2'.

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

(* Do not check if their tailc flags match. Softbound changes the flag for
 * system calls, say atoi from tailcall to non-tailcall.
 *)
Definition tv_scall (c1 c2:scall) :=
  let '(stmn_call rid1 nr1 _ t1 v1 tsts1) := c1 in
  let '(stmn_call rid2 nr2 _ t2 v2 tsts2) := c2 in
  (sumbool2bool _ _ (id_dec rid1 rid1)) &&
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
   (sumbool2bool _ _ (sstate_sub_dec st1 st2 (se_cmds_init_uniq nbs1))) &&
   tv_scall cl1 cl2
end.

Fixpoint tv_subblocks (sbs1 sbs2:list subblock) :=
match (sbs1, sbs2) with
| (nil, nil) => true
| (sb1::sbs1', sb2::sbs2') => 
   (tv_subblock sb1 sb2) && (tv_subblocks sbs1' sbs2')
| _ => false
end.

Fixpoint lookupPhinode (phs:phinodes) (i:id) :=
match phs with
| nil => None
| (insn_phi i' t vs)::phs' =>
    if (eq_dec i i') then Some (insn_phi i' t vs)
    else lookupPhinode phs' i
end.

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

Fixpoint tv_blocks (bs1 bs2:blocks):=
match (bs1, bs2) with
| (nil, nil) => true
| (b1::bs1', b2::bs2') => tv_block b1 b2 && tv_blocks bs1' bs2'
| _ => false
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

Definition tv_module (m1 m2:module) :=
match (m1, m2) with
| (module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2) =>
  sumbool2bool _ _ (layouts_dec los1 los2) &&
  sumbool2bool _ _ (namedts_dec nts1 nts2) &&
  tv_products Ps1 Ps2
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
