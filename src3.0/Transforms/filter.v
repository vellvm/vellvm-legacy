Require Import vellvm.
Require Import primitives.
Require Import mem2reg.

Lemma filter_ext: forall (A:Type) (f g:A->bool)
  (Heq: forall a, f a = g a) (l0:list A), List.filter f l0 = List.filter g l0.
Proof.
  induction l0; intros; simpl; auto.
    rewrite Heq. rewrite IHl0. auto.
Qed.

Lemma filter_true: forall (A:Type) (f:A->bool)
  (Heq: forall a, f a = true) (l0:list A), l0 = List.filter f l0.
Proof.
  induction l0; intros; simpl; auto.
    rewrite Heq. congruence.
Qed.

Section Filter.

Variable check: insn -> bool.

Definition filter_phinodes (ps:phinodes): phinodes :=
List.filter (fun p => check (insn_phinode p)) ps.

Definition filter_cmds (cs:cmds): cmds :=
List.filter (fun c => check (insn_cmd c)) cs.

Definition filter_block (b: block) : block :=
match b with
| block_intro l0 ps cs tmn => 
    block_intro l0 (filter_phinodes ps) (filter_cmds cs) tmn
end.

Definition filter_fdef (f:fdef) : fdef :=
let '(fdef_intro fh bs) := f in
fdef_intro fh (List.map filter_block bs).

Definition value_doesnt_use_removed (v:value): Prop :=
forall instr, check instr = false -> used_in_value (getInsnLoc instr) v = false.

Definition list_value_doesnt_use_removed (vl:list (sz * value)): Prop :=
forall instr, 
  check instr = false -> used_in_list_value (getInsnLoc instr) vl = false.

Definition cmd_doesnt_use_removed (c:cmd): Prop :=
forall instr, check instr = false -> used_in_cmd (getInsnLoc instr) c = false.

Definition tmn_doesnt_use_removed (tmn:terminator): Prop :=
forall instr, check instr = false -> used_in_tmn (getInsnLoc instr) tmn = false.

Definition list_value_l_doesnt_use_removed (vl:list (value * l)): Prop :=
forall instr, 
  check instr = false -> used_in_list_value_l (getInsnLoc instr) vl = false.

Definition phi_doesnt_use_removed (pn:phinode): Prop :=
forall instr, check instr = false -> used_in_phi (getInsnLoc instr) pn = false.

Definition insn_doesnt_use_removed (inst:insn): Prop :=
forall instr, check instr = false -> used_in_insn (getInsnLoc instr) inst = false.

Definition block_doesnt_use_removed (b:block): Prop :=
forall instr, check instr = false -> used_in_block (getInsnLoc instr) b = false.

Definition fdef_doesnt_use_removed (f:fdef): Prop :=
forall instr, check instr = false -> used_in_fdef (getInsnLoc instr) f = false.

End Filter.

Section RemoveIsAFilter.

Variable (id':id).

Definition undead_insn (instr:insn) : bool :=
negb (id_dec (getInsnLoc instr) id').

Lemma remove_phinodes_is_a_filter: forall ps,
  remove_phinodes id' ps = filter_phinodes undead_insn ps.
Proof.
  apply filter_ext; auto.
Qed.

Lemma remove_cmds_is_a_filter: forall cs,
  remove_cmds id' cs = filter_cmds undead_insn cs.
Proof.
  apply filter_ext; auto.
Qed.

Lemma remove_block_is_a_filter: forall b,
  remove_block id' b = filter_block undead_insn b.
Proof.
  destruct b. simpl.
  rewrite remove_phinodes_is_a_filter.
  rewrite remove_cmds_is_a_filter.
  auto.
Qed.

Lemma remove_fdef_is_a_filter: forall f,
  remove_fdef id' f = filter_fdef undead_insn f.
Proof.
  destruct f as [fh bs]. simpl. f_equal.
Qed.

Lemma undead_insn_false_inv: forall instr
  (Hcheck: undead_insn instr = false),
  id' = getInsnLoc instr.
Proof.
  intros.
  unfold undead_insn in Hcheck.
  destruct (id_dec (getInsnLoc instr) id'); subst; tinv Hcheck.
  auto.
Qed.

Lemma fdef_doesnt_use_dead_insn: forall f
  (Hunused : used_in_fdef id' f = false),
  fdef_doesnt_use_removed undead_insn f.
Proof.
  intros.
  intros instr Hcheck.
  apply undead_insn_false_inv in Hcheck. subst. auto.
Qed.

End RemoveIsAFilter.

Definition isnt_store (instr:insn) : bool :=
match instr with
| insn_cmd (insn_store sid _ _ _ _) => false
| _ => true
end.

Lemma fdef_doesnt_use_store: forall S M f (HwfF: wf_fdef S M f)
  (HuniqF: uniqFdef f),
  fdef_doesnt_use_removed isnt_store f.
Admitted.

Section ElimDeadStIsAFilter.

Variable (pid:id).

Definition undead_store (instr:insn) : bool :=
match instr with
| insn_cmd (insn_store sid _ _ (value_id qid) _) => negb (id_dec pid qid)
| _ => true
end.

Lemma elim_dead_st_phinodes_is_a_filter: forall ps,
  ps = filter_phinodes undead_store ps.
Proof.
  apply filter_true; auto.
Qed.

Lemma elim_dead_st_cmds_is_a_filter: forall cs,
  elim_dead_st_cmds cs pid = filter_cmds undead_store cs.
Proof.
  induction cs as [|[] cs]; simpl; try solve [auto | congruence].
    destruct value2; try congruence.
    destruct_if; simpl; try congruence.
Qed.

Lemma elim_dead_st_block_is_a_filter: forall b,
  elim_dead_st_block pid b = filter_block undead_store b.
Proof.
  destruct b. simpl.
  rewrite <- elim_dead_st_phinodes_is_a_filter.
  rewrite elim_dead_st_cmds_is_a_filter.
  auto.
Qed.

Lemma elim_dead_st_fdef_is_a_filter: forall f,
  elim_dead_st_fdef pid f = filter_fdef undead_store f.
Proof.
  destruct f as [fh bs]. simpl. f_equal.
  apply map_ext. apply elim_dead_st_block_is_a_filter.
Qed.

Lemma fdef_doesnt_use_dead_store: forall S M f (HwfF: wf_fdef S M f) 
  (HuniqF: uniqFdef f),
  fdef_doesnt_use_removed undead_store f.
Proof.
  intros.
  apply fdef_doesnt_use_store in HwfF; auto.
  intros instr Hcheck.
  apply HwfF; auto.
  destruct instr as [ | [] | ]; auto.
Qed.

End ElimDeadStIsAFilter.

Lemma filter_successors : forall f check,
  successors f = successors (filter_fdef check f).
Admitted.

Lemma filter_reachablity_analysis : forall f check,
  reachablity_analysis f = reachablity_analysis (filter_fdef check f).
Admitted.

Lemma filter_wfS: forall check f los nts Ps1 Ps2 
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hunused: fdef_doesnt_use_removed check f),
  wf_system 
    [module_intro los nts (Ps1 ++  product_fdef (filter_fdef check f) :: Ps2)].
Admitted.

Require Import palloca_props.

Lemma filter_wfPI: forall check f los nts Ps1 Ps2 pinfo
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq3: f = PI_f pinfo)
  (Hisntal: forall c, 
            lookupInsnViaIDFromFdef f (getCmdLoc c) = ret (insn_cmd c) ->
            check (insn_cmd c) = false -> 
            isnt_alloca c),
  WF_PhiInfo (update_pinfo pinfo (filter_fdef check f)).
Admitted.

(*
Require Import list_facts.

Section uniqueness.

(* Removing an id from an fdef preserves uniqueness *)

Hint Resolve sl_nil sublist_refl.

Lemma remove_block__blockLocs__sublist :
  forall (id1 : id) (bs : blocks),
    sublist (getBlocksLocs (List.map (remove_block id1) bs))
    (getBlocksLocs bs).
Proof.
  intros id1 bs. induction bs as [|[lab phis cmds tmn] bs]. apply sl_nil.
  simpl. repeat apply sublist_app; trivial; clear IHbs.
  apply sublist_map. apply filter_sublist.
  induction cmds as [|cmd cmds]. apply sl_nil.
  simpl. destruct (id_dec (getCmdLoc cmd) id1); simpl;
  [apply sl_cons_r|apply sl_cons]; trivial.
Qed.

Lemma remove_block__uniqBlocks :
  forall (id1 : id) (bs : blocks),
    uniqBlocks bs -> uniqBlocks (List.map (remove_block id1) bs).
Proof.
  intros id1 bs H.
  split; [destruct H as [H _] | destruct H as [_ H]];
    apply (NoDup_sublist _ _ _ H); clear H;
      [|apply remove_block__blockLocs__sublist].
  induction bs as [|[lab phis cmds tmn] bs]; simpl;
    [apply sl_nil|apply sl_cons]; trivial.
Qed.

Lemma remove_fdef__uniqFdef :
  forall (id1 : id) (f : fdef),
    uniqFdef f -> uniqFdef (remove_fdef id1 f).
Proof.
  intros id1 f H.
  destruct f as [[att rtyp idf fas fvas] bs].
  destruct H as [Hbsuniq HNoDup].
  simpl. split. apply remove_block__uniqBlocks. trivial.
  apply NoDup_split' in HNoDup. destruct HNoDup as [Hfas [Hbs Hin]].
  apply NoDup_app. trivial.
    apply NoDup_sublist with (getBlocksLocs bs). trivial.
    apply remove_block__blockLocs__sublist.

    intros id' H1 H2. clear Hbsuniq. apply (Hin id' H1).
    clear H1. generalize id' H2. clear id' H2.
    apply sublist_In. apply remove_block__blockLocs__sublist.
Qed.

End uniqueness.
*)
