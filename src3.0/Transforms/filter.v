Require Import vellvm.
Require Import primitives.
Require Import vmem2reg.
Require Import top_wfS.
Require Import palloca_props.
Require Import trans_tactic.

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

Definition insnInFdef (instr:insn) (f:fdef) : Prop :=
exists b, insnInFdefBlockB instr f b = true.

Definition id_isnt_removed f (id0:id): Prop :=
forall instr, 
  insnInFdef instr f ->
  check instr = false -> id0 <> getInsnLoc instr.

Definition value_doesnt_use_removed f (v:value): Prop :=
forall instr, 
  insnInFdef instr f ->
  check instr = false -> used_in_value (getInsnLoc instr) v = false.

Definition list_value_doesnt_use_removed f (vl:list (sz * value)): Prop :=
forall instr, 
  insnInFdef instr f ->
  check instr = false -> used_in_list_value (getInsnLoc instr) vl = false.

Definition cmd_doesnt_use_removed f (c:cmd): Prop :=
forall instr, 
  insnInFdef instr f ->
  check instr = false -> used_in_cmd (getInsnLoc instr) c = false.

Definition tmn_doesnt_use_removed f (tmn:terminator): Prop :=
forall instr, 
  insnInFdef instr f ->
  check instr = false -> used_in_tmn (getInsnLoc instr) tmn = false.

Definition list_value_l_doesnt_use_removed f (vl:list (value * l)): Prop :=
forall instr, 
  insnInFdef instr f ->
  check instr = false -> used_in_list_value_l (getInsnLoc instr) vl = false.

Definition phi_doesnt_use_removed f (pn:phinode): Prop :=
forall instr, 
  insnInFdef instr f ->
  check instr = false -> used_in_phi (getInsnLoc instr) pn = false.

Definition insn_doesnt_use_removed f (inst:insn): Prop :=
forall instr, 
  insnInFdef instr f ->
  check instr = false -> used_in_insn (getInsnLoc instr) inst = false.

Definition block_doesnt_use_removed f (b:block): Prop :=
forall instr, 
  insnInFdef instr f ->
  check instr = false -> used_in_block (getInsnLoc instr) b = false.

Definition fdef_doesnt_use_removed (f:fdef): Prop :=
forall instr, 
  insnInFdef instr f ->
  check instr = false -> 
  used_in_fdef (getInsnLoc instr) f = false.

Lemma id_isnt_removed__check: forall f instr
  (Hlk: insnInFdef instr f)
  (Hisnt: id_isnt_removed f (getInsnLoc instr)), check instr = true.
Proof.
  unfold id_isnt_removed.
  intros.
  remember (check instr) as R.
  destruct R; auto.
  symmetry in HeqR.
  apply Hisnt in HeqR; auto.
Qed.

Lemma insn_doesnt_use_removed__id_isnt_removed: forall f (instr : insn)
  (Hnouse : insn_doesnt_use_removed f instr),
  Forall (id_isnt_removed f) (getInsnOperands instr).
Proof.
  intros.
  apply Forall_forall.
  intros.
  intros insn Hlk Hck.
  apply Hnouse in Hck; auto. subst.
  apply noused_getInsnOperands in Hck.
  intro EQ. subst. auto.
Qed.

Lemma list_value_l_doesnt_use_removed_cons_inv: forall f v0 l0 
  (vl:list (value * l))
  (Hnouse: list_value_l_doesnt_use_removed f ((v0,l0)::vl)),
  value_doesnt_use_removed f v0 /\ list_value_l_doesnt_use_removed f vl.
Proof.
  intros.
  split;
    intros insn Hlk Hck; 
    apply Hnouse in Hck; auto; simpl in Hck;
    binvf Hck as J1 J2; auto.
Qed.

Lemma value_doesnt_use_removed__id_isnt_removed: forall f (vid : id)
  (Hnouse : value_doesnt_use_removed f (value_id vid)),
  id_isnt_removed f vid.
Proof.
  intros.
  intros insn Hlk Hck.
  apply Hnouse in Hck; auto.
  intro EQ. subst. 
  simpl in *. destruct_dec.
Qed.

Lemma insn_doesnt_use_removed__op_doesnt_use_removed : forall f instr v
  (H2 : insn_doesnt_use_removed f instr)
  (Hin : valueInInsnOperands v instr),
  value_doesnt_use_removed f v.
Proof.
  intros.
  intros insn Hlkup Hck.
  apply H2 in Hck; auto.
  apply noused_getInsnOperands in Hck.
  destruct v; simpl; auto.
  destruct_dec.
    apply valueInInsnOperands__InOps in Hin. 
    congruence.
Qed.

Lemma gep_doesnt_use_removed__idxs_dont_use_removed: forall 
  (sz_value_list : list (sz * value)) (id5 : id) (inbounds5 : inbounds)
  (typ5 : typ) (value_5 : value) (typ' : typ) f
  (Hnouse : insn_doesnt_use_removed f
              (insn_cmd
                (insn_gep id5 inbounds5 typ5 value_5 sz_value_list typ')))
  (v0 : value)
  (Hin0 : In v0
           (List.map
              (fun pat_ : sz * value => let (_, value_) := pat_ in value_)
              sz_value_list)),
  value_doesnt_use_removed f v0.
Proof.
  intros.
  eapply insn_doesnt_use_removed__op_doesnt_use_removed in Hnouse; eauto.
  simpl. right.
  apply InOps__valueInListValue'; auto.
Qed.

Lemma phi_doesnt_use_removed__incoming_dont_use_removed: forall 
  (value_l_list : list (value * l)) (id5 : id) (typ5 : typ) f
  (Hnouse : insn_doesnt_use_removed f
             (insn_phinode (insn_phi id5 typ5 value_l_list)))
  (v0 : value)
  (Hin0 : In v0
    (List.map (fun pat_ : value * l => let (value_, _) := pat_ in value_)
       value_l_list)),
  value_doesnt_use_removed f v0.
Proof.
  intros.
  eapply insn_doesnt_use_removed__op_doesnt_use_removed in Hnouse; eauto.
  simpl. 
  apply InOps__in_list_prj1; auto.
Qed.

Lemma call_doesnt_use_removed__incoming_dont_use_removed: forall  
  id5 noret5 clattrs5 typ1 varg5 value0 typ'_attributes'_value''_list f
  (Hnouse : insn_doesnt_use_removed f
             (insn_cmd
                (insn_call id5 noret5 clattrs5 typ1 varg5 value0
                   (List.map
                      (fun pat_ : typ * attributes * value =>
                       let (p, value_'') := pat_ in
                       let (typ_', attributes_') := p in
                       (typ_', attributes_', value_''))
                      typ'_attributes'_value''_list))))
  (value_'' : value) (typ_' : typ)
  (H : In (value_'', typ_')
        (List.map
           (fun pat_ : typ * attributes * value =>
            let (p, value_'') := pat_ in
            let (typ_', _) := p in (value_'', typ_'))
           typ'_attributes'_value''_list)),
  value_doesnt_use_removed f value_''.
Proof.
  intros.
  eapply insn_doesnt_use_removed__op_doesnt_use_removed in Hnouse; eauto.
  simpl. right.
  clear - H.
  unfold valueInParams. 
  induction typ'_attributes'_value''_list as [|[[]]]; simpl in *; auto.
    destruct_let. 
    simpl. 
    destruct H as [H | H]; auto.
    inv H. auto.
Qed.

Lemma block_doesnt_use_removed_inv: forall f l0 ps0 cs0 tmn0
  (H: block_doesnt_use_removed f (block_intro l0 ps0 cs0 tmn0)),
  insn_doesnt_use_removed f (insn_terminator tmn0) /\
  Forall (phi_doesnt_use_removed f) ps0 /\
  Forall (cmd_doesnt_use_removed f) cs0.
Proof.
  intros.
  split.
    intros instr Hlkp Hck.
    apply H in Hck; auto.
    binvf Hck as J1 J2.
    binvf J1 as J3 J4.
    auto.
  split.
    apply Forall_forall.
    intros.
    intros instr Hlkp Hck.
    apply H in Hck; auto.
    binvf Hck as J1 J2.
    binvf J1 as J3 J4.
    eapply fold_left_or_false_elim in J3; eauto.

    apply Forall_forall.
    intros.
    intros instr Hlkp Hck.
    apply H in Hck; auto.
    binvf Hck as J1 J2.
    binvf J1 as J3 J4.
    eapply fold_left_or_false_elim in J4; eauto.
Qed.

Lemma fdef_doesnt_use_removed_inv: forall fh bs
  (Hnouse : fdef_doesnt_use_removed (fdef_intro fh bs)),
  List.Forall (block_doesnt_use_removed (fdef_intro fh bs)) bs.
Proof.
  intros.
  apply Forall_forall.
  intros.
  intros instr Hlkup Hck.
  apply Hnouse in Hck; auto.
  simpl in Hck.
  eapply fold_left_or_false_elim; eauto.
Qed.

Hint Resolve sl_nil sublist_refl.

Lemma filter_block__blockLocs__sublist :
  forall (bs : blocks),
    sublist (getBlocksLocs (List.map filter_block bs))
    (getBlocksLocs bs).
Proof.
  intros bs. induction bs as [|[lab phis cmds tmn] bs]. apply sl_nil.
  simpl. repeat apply sublist_app; trivial; clear IHbs.
  apply sublist_map. apply filter_sublist.
  induction cmds as [|cmd cmds]. apply sl_nil.
  simpl. 
  destruct_if; simpl; try solve [apply sl_cons_r; auto | apply sl_cons; auto].
Qed.

Lemma filter_block__uniqBlocks :
  forall (bs : blocks),
    uniqBlocks bs -> uniqBlocks (List.map filter_block bs).
Proof.
  intros bs H.
  split; [destruct H as [H _] | destruct H as [_ H]];
    apply (NoDup_sublist H); clear H;
      [|apply filter_block__blockLocs__sublist].
  induction bs as [|[lab phis cmds tmn] bs]; simpl;
    [apply sl_nil|apply sl_cons]; trivial.
Qed.

Lemma filter_fdef__uniqFdef :
  forall (f : fdef),
    uniqFdef f -> uniqFdef (filter_fdef f).
Proof.
  intros f H.
  destruct f as [[att rtyp idf fas fvas] bs].
  destruct H as [Hbsuniq HNoDup].
  simpl. split. apply filter_block__uniqBlocks. trivial.
  apply NoDup_split' in HNoDup. destruct HNoDup as [Hfas [Hbs Hin]].
  apply NoDup_app. trivial.
    apply NoDup_sublist with (getBlocksLocs bs). trivial.
    apply filter_block__blockLocs__sublist.

    intros id' H1 H2. clear Hbsuniq. apply (Hin id' H1).
    clear H1. generalize id' H2. clear id' H2.
    apply sublist_In. apply filter_block__blockLocs__sublist.
Qed.

Lemma filter_block__getBlockLabel: forall b,
  getBlockLabel b = getBlockLabel (filter_block b).
Proof.
  destruct b as [l0 ? ? ?]; simpl; auto.
Qed.

Lemma filter_block__tmn_match: forall b, 
  terminator_match (getBlockTmn b) (getBlockTmn (filter_block b)).
Proof. 
  destruct b as [l0 ? ? t0]; simpl. 
  destruct t0; simpl; auto.
Qed.

Lemma filter_fdef_spec2: forall fh bs, 
  filter_fdef (fdef_intro fh bs) = fdef_intro fh (List.map filter_block bs).
Proof. simpl. auto. Qed.

Lemma filter_fheader: forall f,
  fheaderOfFdef f = fheaderOfFdef (filter_fdef f).
Proof.
  destruct f; auto.
Qed.

Definition Filter := mkPass 
(filter_block)
(filter_fdef)
(filter_fdef_spec2)
(filter_block__getBlockLabel)
(filter_block__tmn_match)
.

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
  intros instr Hlkup Hcheck.
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
Proof.
  intros.
  intros instr Hlkup Hck.
  destruct Hlkup as [b Hlkup].
  destruct instr as [|[]|]; inv Hck.
  simpl.
  remember (used_in_fdef id5 f) as R.
  destruct R; auto.
  symmetry in HeqR.
  apply used_in_fdef_elim in HeqR.
  destruct HeqR as [instr [b' [Hin Huse]]].
  eapply wf_fdef__wf_insn in Hin; eauto 1.
  apply wf_insn__wf_value with (v:=value_id id5) in Hin; auto.
    destruct Hin as [t Hin].
    inv Hin.
    apply lookupTypViaIDFromFdef_elim in H4; auto.
    destruct H4 as [[attr0 H4] | [b'' [instr' [H1 [H2 H3]]]]]; subst.
      apply getArgsOfFdef__getArgsIDsOfFdef in H4.
      contradict H4.
      apply getInsnLoc__notin__getArgsIDs'' in Hlkup; auto.

      apply IngetInsnsLocs__lookupInsnViaIDFromFdef in H1; auto.
      apply IngetInsnsLocs__lookupInsnViaIDFromFdef in Hlkup; auto.
      simpl in *.
      rewrite H1 in Hlkup. 
      inversion Hlkup. rewrite H3 in H2. simpl in H2.
      clear - H0 H2. inv H2.
      inv H0. inv H4.
    apply used_in_insn__valueInInsnOperands; auto.
Qed.

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
  intros instr Hlk Hcheck.
  apply HwfF; auto.
  destruct instr as [ | [] | ]; auto.
Qed.

End ElimDeadStIsAFilter.

Ltac fold_filter_tac :=
repeat match goal with
| |- context [filter_fdef ?chk ?f] =>
  replace (filter_fdef chk f) with (ftrans (Filter chk) f); auto
| |- context [filter_block ?chk ?b] =>
  replace (filter_block chk b) with (btrans (Filter chk) b); auto
| |- context [filter_fdef ?chk] =>
  replace (filter_fdef chk) with (ftrans (Filter chk)); auto
| |- context [filter_block ?chk] =>
  replace (filter_block chk) with (btrans (Filter chk)); auto
end.

Lemma filter_successors : forall f check,
  successors f = successors (filter_fdef check f).
Proof.
  intros.
  fold_filter_tac.
  apply TransCFG.pres_successors.
Qed.

Lemma filter_reachablity_analysis : forall f check,
  reachablity_analysis f = reachablity_analysis (filter_fdef check f).
Proof.
  intros.
  fold_filter_tac.
  apply TransCFG.pres_reachablity_analysis.
Qed.

Section WellFormednessBasic.

Variable check: insn -> bool.

Lemma filter_InPhiNodesB : forall p 
  (Hck: check (insn_phinode p) = true) ps
  (Hin: InPhiNodesB p ps = true),
  InPhiNodesB p (filter_phinodes check ps) = true.
Proof.
  induction ps; simpl; intros.
    congruence.

    binvt Hin as Hin Hin.
      uniq_result. 
      fill_ctxhole. 
      solve_in_list.

      destruct_if;
        try solve [auto | apply orb_true_iff; right; auto].
Qed.

Hint Resolve filter_InPhiNodesB: ssa_filter.

Lemma filter_phinodeInBlockB : forall p b
  (Heq : check (insn_phinode p) = true)
  (Hin : phinodeInBlockB p b = true),
  phinodeInBlockB p (filter_block check b) = true.
Proof.
  destruct b. simpl. intro. auto with ssa_filter.
Qed.

Hint Resolve filter_phinodeInBlockB: ssa_filter.

Lemma filter_InCmdsB : forall c 
  (Hck: check (insn_cmd c) = true) cs
  (Hin: InCmdsB c cs = true),
  InCmdsB c (filter_cmds check cs) = true.
Proof.
  induction cs; simpl; intros; auto.
    binvt Hin as Hin Hin.
      uniq_result. 
      fill_ctxhole. 
      solve_in_list.

      destruct_if;
        try solve [auto | apply orb_true_iff; right; auto].
Qed.

Hint Resolve filter_InCmdsB: ssa_filter.

Lemma filter_cmdInBlockB : forall c b
  (Hck: check (insn_cmd c) = true)
  (Hin : cmdInBlockB c b = true),
  cmdInBlockB c (filter_block check b) = true.
Proof.
  destruct b. simpl. intro. auto with ssa_filter.
Qed.

Hint Resolve filter_cmdInBlockB: ssa_filter.

Lemma filter_terminatorInBlockB : forall t b
  (Hin : terminatorInBlockB t b = true),
  terminatorInBlockB t (filter_block check b) = true.
Proof.
  destruct b. simpl. intro.
  uniq_result. solve_refl.
Qed.

Hint Resolve filter_terminatorInBlockB: ssa_filter.

Lemma filter_insnInFdefBlockB : forall f b instr
  (Hneq : check instr = true \/ is_terminator instr = true)
  (Hin : insnInFdefBlockB instr f b = true),
  insnInFdefBlockB instr (filter_fdef check f) (filter_block check b) = true.
Proof.
  unfold insnInFdefBlockB.
  intros.
  destruct instr; simpl in *;
    bdestruct Hin as J1 J2;
    apply (@TransCFG.pres_blockInFdefB (Filter check)) in J2; auto;
    simpl in J2;
    match goal with
    | H : _ \/ false = true |- _ => destruct H as [H | H]; try congruence
    | _ => idtac
    end;
    bsplit; auto with ssa_filter.
Qed.

Hint Resolve filter_insnInFdefBlockB: ssa_filter.

Lemma filter_In_getPhiNodesIDs1 : forall f id5
  (Hck: id_isnt_removed check f id5) ps 
  (Hbd: forall p, In p ps -> insnInFdef (insn_phinode p) f)
  (Hin: In id5 (getPhiNodesIDs ps)),
  In id5 (getPhiNodesIDs (filter_phinodes check ps)).
Proof.
  induction ps; simpl; intros. auto.
    destruct Hin as [Hin | Hin]; subst.
      erewrite id_isnt_removed__check; simpl; eauto.
      destruct_if; simpl; auto.
Qed.

Lemma filter_In_getPhiNodesIDs2 : forall f id5 
  (Hck: id_isnt_removed check f id5) ps
  (Hbd: forall p, In p ps -> insnInFdef (insn_phinode p) f)
  (Hin: In id5 (getPhiNodesIDs (filter_phinodes check ps))),
  In id5 (getPhiNodesIDs ps).
Proof.
  induction ps; simpl; intros; auto.
    destruct_if; auto.
Qed.

Lemma filter_In_getCmdsIDs1 : forall f id5
  (Hck: id_isnt_removed check f id5) cs
  (Hbd: forall c, In c cs -> insnInFdef (insn_cmd c) f)
  (Hin: In id5 (getCmdsIDs cs)),
  In id5 (getCmdsIDs (filter_cmds check cs)).
Proof.
  induction cs as [|c]; simpl; intros. auto.
    remember (getCmdID c) as R.
    destruct R. 
      symmetry_ctx.
      assert (J:=HeqR).
      apply getCmdID__getCmdLoc in HeqR. subst.
      simpl in Hin.
      destruct Hin as [Hin | Hin]; subst.
        erewrite id_isnt_removed__check; simpl; eauto.
        fill_ctxhole. simpl. auto.

        destruct_if; simpl; auto.
        fill_ctxhole. simpl. auto.
      destruct_if; simpl; auto.
      fill_ctxhole. simpl. auto.
Qed.

Lemma filter_In_getCmdsIDs2 : forall f id5
  (Hck: id_isnt_removed check f id5) cs
  (Hbd: forall c, In c cs -> insnInFdef (insn_cmd c) f)
  (Hin: In id5 (getCmdsIDs (filter_cmds check cs))),
  In id5 (getCmdsIDs cs).
Proof.
  induction cs as [|c]; simpl; intros. auto.
    destruct_if; simpl in *; auto.
    destruct (getCmdID c); auto.
    destruct_in Hin; simpl; auto.

    destruct (getCmdID c); simpl; auto.
Qed.

Lemma blockInFdefB__phiInFdef: forall l5 ps cs tmn f
  (Hbd: blockInFdefB (block_intro l5 ps cs tmn) f = true),
  forall p, In p ps -> insnInFdef (insn_phinode p) f.
Proof.
  intros.
  exists (block_intro l5 ps cs tmn).
  bsplit; auto.
    simpl. solve_in_list.
Qed.

Lemma blockInFdefB__cmdInFdef: forall l5 ps cs tmn f
  (Hbd: blockInFdefB (block_intro l5 ps cs tmn) f = true),
  forall c, In c cs -> insnInFdef (insn_cmd c) f.
Proof.
  intros.
  exists (block_intro l5 ps cs tmn).
  bsplit; auto.
    simpl. solve_in_list.
Qed.

Hint Resolve filter_In_getPhiNodesIDs1 filter_In_getCmdsIDs1
             filter_In_getPhiNodesIDs2 filter_In_getCmdsIDs2 
             blockInFdefB__phiInFdef blockInFdefB__cmdInFdef: ssa_filter.

Lemma filter_lookupBlockViaIDFromBlocks : forall f id5 bs b
  (Hck: id_isnt_removed check f id5) 
  (Hbd: forall b, In b bs -> blockInFdefB b f = true)
  (Hin: lookupBlockViaIDFromBlocks bs id5 = ret b),
  lookupBlockViaIDFromBlocks (List.map (filter_block check) bs) id5 =
    ret (filter_block check b).
Proof.
  induction bs as [|[l5 p c t5]]; simpl; intros.
    congruence.

    assert (blockInFdefB (block_intro l5 p c t5) f = true) as Hbd' by auto.
    destruct_if;
      destruct_if; try solve [
        auto |
        match goal with
        | HeqR: left ?i0 = _, HeqR0: right ?n = _ |- _ =>
          clear HeqR0 HeqR; contradict n;
          apply in_or_app;
          destruct_in i0; eauto with ssa_filter
        end
      ].
Qed.

Lemma blockInFdefB__blocksInFdefB: forall fh bs b, 
  In b bs -> blockInFdefB b (fdef_intro fh bs) = true.
Proof. simpl. intros. solve_in_list. Qed.

Hint Resolve filter_lookupBlockViaIDFromBlocks 
             blockInFdefB__blocksInFdefB: ssa_filter.

Lemma filter_lookupBlockViaIDFromFdef : forall f id5 b
  (Hck: id_isnt_removed check f id5)
  (Hin: lookupBlockViaIDFromFdef f id5 = ret b),
  lookupBlockViaIDFromFdef (filter_fdef check f) id5 = 
    ret (filter_block check b).
Proof.
  destruct f. simpl; intros. eauto with ssa_filter.
Qed.

Hint Resolve filter_lookupBlockViaIDFromFdef: ssa_filter.

Hint Resolve not_id_dec__neq : ssa_filter.

Lemma filter_phinodes_neq : forall p1 ps2 ps1
  (Hck: check (insn_phinode p1) = true), 
  exists ps0, exists ps3,
    filter_phinodes check (ps1 ++ p1 :: ps2) = ps0 ++ p1 :: ps3 /\
    filter_phinodes check ps1 = ps0 /\
    filter_phinodes check ps2 = ps3.
Proof.
  induction ps1 as [|a]; intros; simpl.
    fill_ctxhole. 
    exists nil. exists (filter_phinodes check ps2). auto.

    destruct_if; auto.
    apply IHps1 in Hck. destruct Hck as [ps0 [ps3 [H [J1 J2]]]].
    exists (a::ps0). exists ps3. rewrite H. rewrite J1. rewrite J2. auto.
Qed.

Lemma filter_cmds_neq : forall cs2 c1 cs1
  (Hck: check (insn_cmd c1) = true), 
   exists cs0 : list cmd,
     exists cs4 : list cmd,
       filter_cmds check (cs1 ++ c1 :: cs2) = cs0 ++ c1 :: cs4 /\
       filter_cmds check cs1 = cs0 /\
       filter_cmds check cs2 = cs4.
Proof.
  induction cs1 as [|a]; intros; simpl.
    fill_ctxhole. 
    exists nil. exists (filter_cmds check cs2). auto.

    destruct_if; auto.
    apply IHcs1 in Hck. destruct Hck as [cs0 [cs3 [H [J1 J2]]]].
    exists (a::cs0). exists cs3. rewrite H. rewrite J1. rewrite J2. auto.
Qed.

Lemma filter_phinodes_neq_inv : forall ps p1 ps3 ps0
  (Hck: check (insn_phinode p1) = true)
  (Heq: filter_phinodes check ps  = ps0 ++ p1 :: ps3),
  exists ps1, exists ps2,
    ps = ps1 ++ p1 :: ps2 /\
    filter_phinodes check ps1 = ps0 /\
    filter_phinodes check ps2 = ps3.
Proof.
  induction ps as [|a]; simpl; intros.
    solve_in_list'.

    destruct_if.
      destruct ps0; inv H0.
        exists nil. exists ps. auto.

        apply IHps in H2; auto.
        destruct H2 as [ps1 [ps2 [H3 [J1 J2]]]]; subst.
        exists (p::ps1). exists ps2. simpl.
        destruct_if.
          congruence.

      apply IHps in H0; auto.
      destruct H0 as [ps1 [ps2 [H0 [J1 J2]]]]; subst.
      exists (a::ps1). exists ps2. simpl.
      destruct_if.
        congruence.
Qed.

Lemma filter_cmds_neq_inv : forall cs c1 cs3 cs0
  (Hck: check (insn_cmd c1) = true)
  (Heq: filter_cmds check cs  = cs0 ++ c1 :: cs3),
  exists cs1, exists cs2,
    cs = cs1 ++ c1 :: cs2 /\
    filter_cmds check cs1 = cs0 /\
    filter_cmds check cs2 = cs3.
Proof.
  induction cs as [|a]; simpl; intros.
    solve_in_list'.

    destruct_if.
      destruct cs0; inv H0.
        exists nil. exists cs. auto.

        apply IHcs in H2; auto.
        destruct H2 as [cs1 [cs2 [H3 [J1 J2]]]]; subst.
        exists (c::cs1). exists cs2. simpl.
        destruct_if.
          congruence.

      apply IHcs in H0; auto.
      destruct H0 as [cs1 [cs2 [H0 [J1 J2]]]]; subst.
      exists (a::cs1). exists cs2. simpl.
      destruct_if.
        congruence.
Qed.

Ltac unfold_getInsnLoc :=
repeat match goal with
| H: context [getPhiNodeID ?p] |- _ => 
     replace (getPhiNodeID p) with (getInsnLoc (insn_phinode p)) in H; auto
| H: context [getCmdLoc ?c] |- _ => 
     replace (getCmdLoc c) with (getInsnLoc (insn_cmd c)) in H; auto
| H: context [getTerminatorID ?t] |- _ => 
     replace (getTerminatorID t) with (getInsnLoc (insn_terminator t)) in H; auto
end.

Ltac find_insnInFdef_tac :=
match goal with
| H: blockInFdefB ?b _ = true |- _ =>
  exists b; simpl; bsplit; auto; solve_in_list
end.

Lemma filter_insnDominates_tmn : forall f i0 instr b
  (Hnodup: NoDup (getBlockLocs b))
  (Heq1: is_terminator instr = true)
  (Heq2: id_isnt_removed check f i0)
  (HiInF: insnInFdefBlockB instr f b = true),
  insnDominates i0 instr b ->
  insnDominates i0 instr (filter_block check b).
Proof.
 intros f i0 instr b Hnodup Hneq1 Hneq2 HiInF. 
 apply destruct_insnInFdefBlockB in HiInF.
 destruct HiInF as [HiInB HbInF].
 destruct b as [l0 ps cs tmn]. 
 destruct instr as [|c0|]; tinv Hneq1; simpl; intro J; auto.
 simpl in HiInB. uniq_result.
   destruct J as [[[cs1 [c1 [cs2 [J1 J2]]]] | [ps1 [p1 [ps2 [J1 J2]]]]] Heq];
     subst; split; auto.
     left.
     assert (J2':=J2).
     apply getCmdLoc_getCmdID in J2. subst.
     unfold_getInsnLoc.
     apply id_isnt_removed__check in Hneq2; try find_insnInFdef_tac.
     apply filter_cmds_neq with (cs1:=cs1)(cs2:=cs2) in Hneq2; eauto.
     destruct Hneq2 as [cs0 [cs3' [Heq2 [J5 J6]]]].
     rewrite Heq2. exists cs0. exists c1. exists cs3'. split; auto.

     right.
     unfold_getInsnLoc.
     apply id_isnt_removed__check in Hneq2; try find_insnInFdef_tac.
     apply filter_phinodes_neq with (ps1:=ps1)(ps2:=ps2) in Hneq2; eauto.
     destruct Hneq2 as [ps0 [ps3 [Heq2 [J5 J6]]]].
     rewrite Heq2. eauto.
Qed.

Lemma filter_insnDominates : forall f i0 instr b
  (Hnodup: NoDup (getBlockLocs b))
  (Heq1: check instr = true \/ is_terminator instr = true)
  (Heq2: id_isnt_removed check f i0)
  (HiInF: insnInFdefBlockB instr f b = true),
  (insnDominates i0 instr b ->
  insnDominates i0 instr (filter_block check b)).
Proof.
 intros f i0 instr b Hnodup Hneq1 Hneq2 HiInF. 
 remember (is_terminator instr) as R.
 destruct R; eauto using filter_insnDominates_tmn.
 destruct Hneq1 as [Hneq1 | Hneq1]; try congruence.
 apply destruct_insnInFdefBlockB in HiInF.
 destruct HiInF as [HiInB HbInF].
 destruct b as [l0 ps cs tmn]. simpl.
 destruct instr as [|c0|]; tinv HeqR; simpl; intro J; auto.
   destruct J as [[ps1 [p1 [ps2 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]];
     subst.
     left.
     unfold_getInsnLoc.
     apply id_isnt_removed__check in Hneq2; try find_insnInFdef_tac.
     apply filter_phinodes_neq with (ps1:=ps1)(ps2:=ps2) in Hneq2; eauto.
     destruct Hneq2 as [ps0 [ps3 [Heq2 [J5 J6]]]].
     rewrite Heq2. eauto.

     right. simpl in Hneq1.
     assert (J2':=J2).
     apply getCmdLoc_getCmdID in J2. subst.
     unfold_getInsnLoc.
     apply id_isnt_removed__check in Hneq2; try find_insnInFdef_tac.
     apply filter_cmds_neq with (cs1:=cs1)(cs2:=cs2 ++ c0 :: cs3) in Hneq2; eauto.
     destruct Hneq2 as [cs0 [cs3' [Heq2 [J5 J6]]]].
     rewrite Heq2. exists cs0. exists c1. rewrite <- J6.
     apply filter_cmds_neq with (cs1:=cs2)(cs2:=cs3) in Hneq1; eauto.
     destruct Hneq1 as [cs4 [cs5 [Hneq1 [J7 J8]]]].
     rewrite Hneq1. exists cs4. exists cs5. split; auto.
Qed.

Lemma filter_wf_operand : forall instr f b i0
  (Huniq : NoDup (getBlockLocs b))
  (H1 : wf_operand f b instr i0)
  (Hneq : check instr = true \/ is_terminator instr = true)
  (Heq2: id_isnt_removed check f i0),
  wf_operand (filter_fdef check f) (filter_block check b) instr i0.
Proof.
  intros.
  inv H1.
  eapply wf_operand_intro; try solve [eauto with ssa_filter].
    fold_filter_tac.
    rewrite <- TransCFG.pres_isReachableFromEntry.
    rewrite <- TransCFG.pres_getArgsIDsOfFdef.
    match goal with
    | H4: (_ \/ _ ) \/ _ |- _ => 
        destruct H4 as [[[b' [H5 H4]] | H4] | H4]; auto
    end.
    left. left.
    exists (btrans (Filter check) b').
      rewrite <- TransCFG.pres_blockStrictDominates.
      simpl.
      split; auto with ssa_filter.
      match goal with
      | H4: _ \/ blockStrictDominates _ _ _ |- _ =>
        destruct H4 as [H4 | H4]; auto
      end.
        left.
        eapply filter_insnDominates; eauto.
Qed.

Hint Resolve filter_wf_operand: ssa_filter.

Lemma filter_wf_operand_list : forall instr f b 
  (Huniq : NoDup (getBlockLocs b))
  (Hneq : check instr = true \/ is_terminator instr = true) id_list0
  (Hnotin : List.Forall (id_isnt_removed check f) id_list0)
  (H2 : forall id_ : id,
          In id_ (List.map (fun id_0 : id => id_0) id_list0) ->
          wf_operand f b instr id_),
  forall id_ : id,
    In id_ (List.map (fun id_0 : id => id_0) id_list0) ->
    wf_operand (filter_fdef check f) (filter_block check b)
       instr id_.
Proof.
  induction 3; simpl; intros; auto.
    tauto.
  
    destruct H0 as [H0 | H0]; subst; auto.
      auto with ssa_filter.
Qed.

Hint Resolve filter_wf_operand_list: ssa_filter.

Hint Resolve insn_doesnt_use_removed__id_isnt_removed: ssa_filter.

Lemma filter_wf_insn_base : forall f b instr
  (Huniq : NoDup (getBlockLocs b))
  (Hneq : check instr = true \/ is_terminator instr = true)
  (Hnouse : insn_doesnt_use_removed check f instr)
  (HwfI: wf_insn_base f b instr),
  wf_insn_base (filter_fdef check f) (filter_block check b) instr.
Proof.
  intros.
  inv HwfI.
  eapply filter_insnInFdefBlockB in H; eauto.
  subst.
  eapply wf_insn_base_intro; eauto with ssa_filter.
Qed.

Hint Constructors wf_phi_operands.

Hint Resolve value_doesnt_use_removed__id_isnt_removed: ssa_filter.

Lemma filter_wf_phi_operands : forall f b ty id' vls
  (Hnouse : list_value_l_doesnt_use_removed check f vls)
  (Hwf_pnops: wf_phi_operands f b id' ty vls),
  wf_phi_operands (filter_fdef check f) (filter_block check b) id' ty vls.
Proof.
  intros.
  induction Hwf_pnops; simpl in *; auto.
    apply list_value_l_doesnt_use_removed_cons_inv in Hnouse.
    destruct Hnouse as [J1 J2].
    eapply wf_phi_operands_cons_vid; eauto.
      fold_filter_tac.
      eapply TransCFG.pres_lookupBlockViaLabelFromFdef in H; eauto.

      fold_filter_tac.
      rewrite <- TransCFG.pres_getArgsIDsOfFdef; auto.
      rewrite <- TransCFG.pres_isReachableFromEntry; auto.
      destruct H0 as [[[vb [J1' J2']] | H0] | H0]; auto.
      left. left.
      exists (filter_block check vb).
      eapply filter_lookupBlockViaIDFromFdef in J1'; eauto with ssa_filter.
      fold_filter_tac.
      rewrite <- TransCFG.pres_blockDominates; auto.
Qed.

Hint Resolve filter_wf_phi_operands: ssa_filter.

Lemma filter_wf_phinode : forall f b PN (HwfPN: wf_phinode f b PN)
  (Hnouse: phi_doesnt_use_removed check f PN),
  wf_phinode (filter_fdef check f) (filter_block check b) PN.
Proof.
  intros. destruct PN as [id' vls].
  unfold wf_phinode in *. simpl.
  destruct HwfPN as [Hwf_pnops Hcl].
  split; auto with ssa_filter.
    fold_filter_tac.
    apply TransCFG.pres_check_list_value_l; auto.
Qed.

Lemma filter_lookupTypViaIDFromPhiNodes : forall f id5
  (Hneq: id_isnt_removed check f id5) ps
  (Hbd: forall p, In p ps -> insnInFdef (insn_phinode p) f),
  lookupTypViaIDFromPhiNodes ps id5 =
    lookupTypViaIDFromPhiNodes (filter_phinodes check ps) id5.
Proof.
  induction ps as [|a]; simpl; intros; auto.
    rewrite IHps; auto.
    destruct a. simpl.
    unfold lookupTypViaIDFromPhiNode in *.
    destruct_if.
      erewrite id_isnt_removed__check; eauto.
      simpl.
      unfold lookupTypViaIDFromPhiNode in *. simpl.
      destruct_if.
        congruence.

      destruct_if.
        simpl.
        unfold lookupTypViaIDFromPhiNode in *. simpl in *.
        destruct_if.
          congruence.
Qed.

Lemma filter_lookupTypViaIDFromCmds : forall f id5 
  (Hneq: id_isnt_removed check f id5) cs
  (Hbd: forall c, In c cs -> insnInFdef (insn_cmd c) f),
  lookupTypViaIDFromCmds cs id5 = lookupTypViaIDFromCmds (filter_cmds check cs) id5.
Proof.
  induction cs as [|a]; simpl; intros; auto.
    rewrite IHcs; auto.
    unfold lookupTypViaIDFromCmd in *.
    assert (J:=getCmdTyp__total a).
    remember (getCmdTyp a) as R.
    destruct R; try congruence.
    destruct_if. 
      erewrite id_isnt_removed__check; eauto.
      simpl.
      unfold lookupTypViaIDFromCmd in *. simpl.
      rewrite <- HeqR.
      destruct_if.
        congruence.

      destruct_if.
        simpl.
        unfold lookupTypViaIDFromCmd in *. simpl in *.
        rewrite <- HeqR.
        destruct_if.
          congruence.
Qed.

Lemma filter_lookupTypViaIDFromBlocks : forall f id5
  (Hneq: id_isnt_removed check f id5) bs
  (Hbd: forall b, In b bs -> blockInFdefB b f = true),
  lookupTypViaIDFromBlocks bs id5 =
    lookupTypViaIDFromBlocks (List.map (filter_block check) bs) id5.
Proof.
  induction bs as [|[l5 p c t5]]; simpl; intros; auto.
    rewrite IHbs; auto.
    assert (blockInFdefB (block_intro l5 p c t5) f = true) as Hbd' by auto.
    erewrite <- filter_lookupTypViaIDFromPhiNodes; eauto with ssa_filter.
    erewrite <- filter_lookupTypViaIDFromCmds; eauto with ssa_filter.
Qed.

Lemma filter_lookupTypViaIDFromFdef : forall f id5
  (Hneq: id_isnt_removed check f id5),
  lookupTypViaIDFromFdef f id5 = lookupTypViaIDFromFdef (filter_fdef check f) id5.
Proof.
  destruct f. simpl. intros. 
  erewrite <- filter_lookupTypViaIDFromBlocks; eauto with ssa_filter.
Qed.

End WellFormednessBasic.

Section WellFormedness.

Variable (los:layouts) (nts:namedts) (Ps1 Ps2:products)
         (M M':module) (f f':fdef) (check:insn -> bool).
Hypothesis (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
           (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
           (HeqF': f' = filter_fdef check f).

Lemma filter_wf_typ: forall t,
  wf_typ [M] (los,nts) t -> wf_typ [M'] (los,nts) t.
Proof.
  subst.
  eapply TopWFS.subst_fdef_preserves_single_wf_typ; 
    eauto using filter_fheader.
Qed.

Lemma filter_wf_const: forall c t,
  wf_const [M] (los,nts) c t -> wf_const [M'] (los,nts) c t.
Proof.
  subst.
  eapply TopWFS.subst_fdef_preserves_single_wf_const;
    eauto using filter_fheader.
Qed.

Lemma filter_blockInSystemModuleFdefB: forall b b'
  (Heqb': b' = filter_block check b) 
  (Hin: blockInSystemModuleFdefB b [M] M f),
  blockInSystemModuleFdefB b' [M'] M' f'.
Proof.
  intros.
  subst.
  apply blockInSystemModuleFdef_inv in Hin.
  destruct Hin as [J1 [J2 [J3 J4]]].
  apply blockInSystemModuleFdef_intro.
    fold_filter_tac.
    apply TransCFG.pres_blockInFdefB; auto.

    apply InProductsB_middle.

    unfold moduleInSystem. simpl.
    apply orb_true_intro.
    left. solve_refl.
Qed.

Lemma filter_preserves_wf_fheader: forall fh,
  wf_fheader [M] (los,nts) fh -> wf_fheader [M'] (los,nts) fh.
Proof.
  subst.
  eapply TopWFS.subst_fdef_preserves_single_wf_fheader; 
    eauto using filter_fheader.
Qed.

Hint Constructors wf_insn wf_value.

Hint Resolve value_doesnt_use_removed__id_isnt_removed: ssa_filter.

Lemma filter_wf_value : forall v t (Hwfv: wf_value [M] M f v t)
  (Hnouse : value_doesnt_use_removed check f v),
  wf_value [M'] M' f' v t.
Proof.
  intros.
  assert (J1:=filter_wf_const).
  assert (J3:=filter_wf_typ).
  subst. 
  inv Hwfv; try constructor; eauto.
    rewrite <- filter_lookupTypViaIDFromFdef; auto with ssa_filter.
Qed.

Hint Resolve filter_wf_value : ssa_filter.

Ltac filter_wf_cmd_tac :=
match goal with
| H2: wf_insn_base _ _ _ |- wf_insn_base _ _ _ =>
   eapply filter_wf_insn_base in H2; eauto
| _ => auto
end.

Lemma filter_wf_trunc : forall b b' 
  (Huniq: NoDup (getBlockLocs b))
  (Heqb': b' = filter_block check b) instr
  (Hnr : check instr = true)
  (Hnouse : insn_doesnt_use_removed check f instr)
  (HwfI : wf_trunc [M] M f b instr),
  wf_trunc [M'] M' f' b' instr.
Proof.
  intros.
  assert (J2:=filter_wf_value).
  assert (J1:=filter_wf_typ).
  inv HwfI; uniq_result; try solve [
    econstructor; try solve [filter_wf_cmd_tac]
  ].
Qed.

Lemma filter_wf_ext : forall b b' 
  (Huniq: NoDup (getBlockLocs b))
  (Heqb': b' = filter_block check b) instr
  (Hnr : check instr = true)
  (Hnouse : insn_doesnt_use_removed check f instr)
  (HwfI : wf_ext [M] M f b instr),
  wf_ext [M'] M' f' b' instr.
Proof.
  intros.
  assert (J2:=filter_wf_value).
  assert (J1:=filter_wf_typ).
  inv HwfI; uniq_result; try solve [
    econstructor; try solve [filter_wf_cmd_tac]
  ].
Qed.

Lemma filter_wf_cast : forall b b' 
  (Huniq: NoDup (getBlockLocs b))
  (Heqb': b' = filter_block check b) instr
  (Hnr : check instr = true)
  (Hnouse : insn_doesnt_use_removed check f instr)
  (HwfI : wf_cast [M] M f b instr),
  wf_cast [M'] M' f' b' instr.
Proof.
  intros.
  assert (J2:=filter_wf_value).
  assert (J1:=filter_wf_typ).
  inv HwfI; uniq_result; try solve [
    econstructor; try solve [filter_wf_cmd_tac]
  ].
Qed.

Lemma filter_wf_value_list : forall t vs
  (Hnouse : List.Forall (value_doesnt_use_removed check f) vs)
  (H :forall value_ : value, In value_ vs -> wf_value [M] M f value_ t),
  forall (value_ : value) (Hin: In value_ vs), wf_value [M'] M' f' value_ t.
Proof.
  assert (J:=filter_wf_value).
  induction 1; simpl; intros.
    tauto.
    destruct Hin as [Hin | Hin]; subst; auto.
Qed.

Hint Resolve filter_wf_value_list: ssa_filter.

Lemma filter_wf_insn : forall b instr (HwfI: wf_insn [M] M f b instr)
  (Huniq : NoDup (getBlockLocs b)) 
  (Hnouse : insn_doesnt_use_removed check f instr)
  (Hnr : check instr = true \/ is_terminator instr = true) 
  b' (Heqb': b' = filter_block check b),
  wf_insn [M'] M' f' b' instr.
Proof.
  intros.
  assert (J1:=filter_wf_value_list).
  assert (J2:=filter_wf_value).
  assert (J3:=filter_wf_typ).
  assert (J5:=@filter_wf_trunc b b' Huniq Heqb' instr).
  assert (J6:=@filter_wf_ext b b' Huniq Heqb' instr).
  assert (J7:=@filter_wf_cast b b' Huniq Heqb' instr).
  assert (J8:=filter_wf_const).

Ltac filter_wf_insn_pre_tac :=
repeat match goal with
| H1 : context [Function.getDefReturnType f] |- _ =>
  rewrite <- 
    (@TransCFG.pres_getDefReturnType (Filter check)) in H1
| |- context [Function.getDefReturnType f] =>
  rewrite <- 
    (@TransCFG.pres_getDefReturnType (Filter check)); auto
| H1 : lookupBlockViaLabelFromFdef f _ = ret _ |- _ =>
  apply (@TransCFG.pres_lookupBlockViaLabelFromFdef 
           (Filter check)) in H1
end.

Ltac remove_is_tmn_tac :=
  match goal with
  | H : _ \/ is_terminator _ = true |- _ => 
      simpl in H; destruct H as [H | H]; try congruence
  end.

Ltac filter_wf_insn_post_tac :=
match goal with
| |- wf_trunc _ _ _ _ _ => remove_is_tmn_tac
| |- wf_ext _ _ _ _ _ => remove_is_tmn_tac
| |- wf_cast _ _ _ _ _ => remove_is_tmn_tac
| |- _ => idtac
end;
match goal with
| H1 : insnInFdefBlockB _ _ _ = true |- insnInFdefBlockB _ _ _ = true =>
  eapply filter_insnInFdefBlockB in H1; eauto
| H2: wf_insn_base _ _ _ |- wf_insn_base _ _ _ => 
  eapply filter_wf_insn_base in H2; eauto
| H2: wf_phinode _ _ _ |- wf_phinode _ _ _ => 
   eapply filter_wf_phinode in H2; eauto
| H2: insn_doesnt_use_removed _ _ _,
  J2: forall _ _, _ -> _ -> wf_value _ _ _ _ _ |- wf_value _ _ _ _ _ =>
   eapply J2; try solve [
     eauto 2 |
     eapply insn_doesnt_use_removed__op_doesnt_use_removed in H2; simpl; eauto
   ]
| H2: insn_doesnt_use_removed _ _ _,
  J2: forall _ _, _ -> _ -> wf_value _ _ _ _ _
  |- context [ In _ _ -> wf_value _ _ _ _ _ ] =>
   intros;
   eapply J2; try solve [
     eauto 2 |
     eapply gep_doesnt_use_removed__idxs_dont_use_removed in H2; simpl; eauto |
     eapply phi_doesnt_use_removed__incoming_dont_use_removed in H2; simpl; eauto |
     eapply call_doesnt_use_removed__incoming_dont_use_removed in H2; simpl; eauto
   ]
| _ => eauto with ssa_filter
end.

  inv HwfI; uniq_result; try solve [
    filter_wf_insn_pre_tac;
    econstructor; 
    filter_wf_insn_post_tac
  ].
Qed.

Hint Resolve filter_wf_insn : ssa_filter.

Hint Constructors wf_phinodes.

Lemma filter_wf_phinodes : forall b PNs (HwfPNs: wf_phinodes [M] M f b PNs)
  (Hnouse : List.Forall (phi_doesnt_use_removed check f) PNs)
  (Huniq : NoDup (getBlockLocs b)) b' (Heqb': b' = filter_block check b),
  wf_phinodes [M'] M' f' b' (filter_phinodes check PNs).
Proof.
  assert (J:=filter_wf_insn).
  subst.
  induction 2; simpl in *; intros; auto.
    inv HwfPNs.
    destruct_if; eauto.
Qed.

Hint Constructors wf_cmds.

Lemma filter_wf_cmds : forall b Cs (HwfCs: wf_cmds [M] M f b Cs)
  (Hnouse : List.Forall (cmd_doesnt_use_removed check f) Cs)
  (Huniq : NoDup (getBlockLocs b)) b' (Heqb': b' = filter_block check b),
  wf_cmds [M'] M' f' b' (filter_cmds check Cs).
Proof.
  assert (J:=filter_wf_insn).
  subst.
  induction 2; simpl in *; intros; auto.
    inv HwfCs.
    destruct_if; eauto.
Qed.

Lemma filter_wf_block : forall b (HwfB : wf_block [M] M f b)
  (Hnouse : block_doesnt_use_removed check f b)
  (Huniq : NoDup (getBlockLocs b)) b' (Heqb': b' = filter_block check b),
  wf_block [M'] M' f' b'.
Proof.
  intros.
  inv_wf_block HwfB. subst b.
  apply block_doesnt_use_removed_inv in Hnouse.
  destruct Hnouse as [Hnouse1 [Hnouse2 Hnouse3]].
  eapply filter_blockInSystemModuleFdefB in HBinSMF; eauto.
  eapply filter_wf_cmds in Hwfcs; eauto.
  eapply filter_wf_phinodes in Hwfps; eauto.
  eapply filter_wf_insn in Hwfi; eauto 1; simpl; auto.
    subst. apply wf_block_intro; eauto.
Qed.

Hint Resolve filter_wf_block : ssa_filter.

Hint Constructors wf_blocks.

Lemma filter_wf_blocks : forall bs (HwfBs : wf_blocks [M] M f bs)
  (Hnouse : List.Forall (block_doesnt_use_removed check f) bs)
  (Huniq : NoDup (getBlocksLocs bs)),
  wf_blocks [M'] M' f' (List.map (filter_block check) bs).
Proof.
  induction 2; simpl; intros.
    constructor.

    simpl in Huniq.
    split_NoDup. inversion HwfBs.
    constructor; auto.
      eapply filter_wf_block; eauto 1.
Qed.

Hint Resolve filter_wf_blocks : ssa_filter.

Lemma filter_wf_fdef: forall (HwfF: wf_fdef [M] M f) (HuniqF: uniqFdef f)
  (Hnouse : fdef_doesnt_use_removed check f),
  wf_fdef [M'] M' f'.
Proof.
  intros. assert (HwfF':=HwfF).
  assert (G:=filter_preserves_wf_fheader).
  inv_wf_fdef HwfF'.
  match goal with
  | Hentry : getEntryBlock _ = _,
    Hnpred : has_no_predecessors _ _ = _ |- _ =>
     eapply (@TransCFG.pres_getEntryBlock (Filter check))
       in Hentry; eauto;
     erewrite (@TransCFG.pres_has_no_predecessors (Filter check)) 
       in Hnpred; eauto
  end.
  rewrite EQ2 in Hwfb.
  match goal with
  | H2: fdef_intro _ _ = _, Hnouse : fdef_doesnt_use_removed check _,
    H9: wf_blocks _ _ _ _ |- _ =>
    rewrite H2 in H9;
    rewrite <- H2 in Hnouse;
    eapply filter_wf_blocks in H9; try solve [
      eauto |
      rewrite <- H2 in HuniqF; eapply uniqF__uniqBlocksLocs; eauto |
      rewrite <- H2; simpl; intros; apply In_InBlocksB; auto |
      rewrite <- H2; eapply fdef_doesnt_use_removed_inv; eauto
    ]
  end.

  subst. uniq_result.
  eapply wf_fdef_intro; eauto 2.
    clear. 
    apply productInSystemModuleB_intro.
      simpl. unfold is_true. apply InProductsB_middle.

      unfold moduleInSystem. simpl. apply orb_true_intro. 
      left. apply moduleEqB_refl.
Qed.

End WellFormedness.

Lemma filter_wfS: forall check f los nts Ps1 Ps2 
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hunused: fdef_doesnt_use_removed check f),
  wf_system 
    [module_intro los nts (Ps1 ++  product_fdef (filter_fdef check f) :: Ps2)].
Proof.
  intros.
  assert (HuniqF: uniqFdef f).
    apply wf_single_system__wf_uniq_fdef in HwfS.
    destruct HwfS; auto.
  eapply TopWFS.trans_wfS with (f:=f) in HwfS; intros;
    eauto using filter_fheader.
    eapply filter_wf_fdef in HwfF; eauto.
    eapply filter_fdef__uniqFdef; eauto.
Qed.

Lemma filter_alloca_in_entry: forall pid pty pnum pal check f
  (Huniq: uniqFdef f) b
  (Hisntal: forall c, 
            lookupInsnViaIDFromFdef f (getCmdLoc c) = ret (insn_cmd c) ->
            check (insn_cmd c) = false -> 
            isnt_alloca c) cs
  (Hex: forall c, In c cs -> cmdInFdefBlockB c f b = true)
  (H : In (insn_alloca pid pty pnum pal) cs),
  In (insn_alloca pid pty pnum pal) (filter_cmds check cs).
Proof.
  induction cs; simpl; intros; auto.
    destruct H as [H | H]; subst.
      destruct_if; simpl; auto.
        symmetry in HeqR.
        apply Hisntal in HeqR.
          inv HeqR.

          match goal with
          | |- context [getCmdLoc ?c] => 
               replace (getCmdLoc c) with (getInsnLoc (insn_cmd c)); auto
          end.
          apply IngetInsnsLocs__lookupInsnViaIDFromFdef with (b:=b); auto.
          simpl.
          apply Hex. auto.

      destruct_if; simpl; auto.
Qed.

Section FilterPromotable.

Variable (check:insn -> bool) (pid:id).

Lemma filter_used_in_phis: forall ps init
  (H: fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
        ps init = false),
  fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
     (filter_phinodes check ps) init = false.
Proof.
  induction ps; simpl; intros; auto.
    apply fold_left_or_false in H.
      destruct H as [H1 H2].
      apply orb_false_iff in H2.
      destruct H2; subst. 
      destruct_if; auto.
        simpl. rewrite H0. auto.
      
      apply used_in_phi_fun_spec.
Qed.

Lemma filter_is_promotable_cmds: forall cs acc
  (H: fold_left (is_promotable_cmd pid) cs acc = true),
  fold_left (is_promotable_cmd pid) (filter_cmds check cs) acc =
    true.
Proof.
  induction cs; simpl; intros; auto.
    apply fold_left_and_true in H.
      destruct H as [H1 H2].
      destruct_if.
        simpl. rewrite H2. auto.
        apply is_promotable_cmd_spec in H2. subst. auto.
      apply is_promotable_cmd_spec.
Qed.

Lemma subst_is_promotable_fun: forall b acc,
  is_promotable_fun pid acc b = true ->
  is_promotable_fun pid acc (filter_block check b) = true.
Proof.
  destruct b; simpl.
  intros.
  match goal with
  | H: context [if ?lk then _ else _] |- _ =>
    remember lk as R; destruct R; tinv H
  end.
  symmetry in HeqR.
  assert (forall (a : bool) c, a || c = false -> a = false) as G.
    intros a c Hin. apply orb_false_iff in Hin. tauto.
  apply fold_left_or_false in HeqR; eauto 2.
  destruct HeqR as [J1 J2].
  apply filter_used_in_phis in J1.
  rewrite J2. rewrite J1.
  apply filter_is_promotable_cmds; auto.
Qed.

Lemma filter_is_promotable_funs: forall bs init
  (H : fold_left (is_promotable_fun pid) bs init = true),
  fold_left (is_promotable_fun pid) (List.map (filter_block check) bs) init =
    true.
Proof.
  induction bs; simpl; intros; auto.
    apply fold_left_and_true in H.
      destruct H as [H1 H2].
      rewrite subst_is_promotable_fun; auto.
      
      apply is_promotable_fun_spec.
Qed.

Lemma filter_is_promotable: forall f
  (H: is_promotable f pid = true),
  is_promotable (filter_fdef check f) pid = true.
Proof.
  unfold is_promotable.
  destruct f as [fh bs]. simpl. intros.
  apply filter_is_promotable_funs; auto.
Qed.

End FilterPromotable.

Lemma filter_wfPI: forall check f los nts Ps1 Ps2 pinfo
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq3: f = PI_f pinfo)
  (Hisntal: forall c, 
            lookupInsnViaIDFromFdef f (getCmdLoc c) = ret (insn_cmd c) ->
            check (insn_cmd c) = false -> 
            isnt_alloca c),
  WF_PhiInfo (update_pinfo pinfo (filter_fdef check f)).
Proof.
  intros. subst.
  assert (HuniqF: uniqFdef (PI_f pinfo)).
    apply wf_single_system__wf_uniq_fdef in HwfS; auto.
    tauto.
  destruct Hwfpi.
  destruct pinfo. 
  split; simpl in *.
    unfold promotable_alloca in *.
    inv_mbind. 
    fold_filter_tac.
    erewrite TransCFG.pres_getEntryBlock; eauto.
    destruct b as [l0 ps0 cs0 tmn0]. 
    destruct H.
    simpl.
    split.
      match goal with
      | HeqR: ret ?b0 = getEntryBlock _ |- _ =>
        symmetry in HeqR;
        apply entryBlockInFdef in HeqR;
        eapply filter_alloca_in_entry with (b:=b0); eauto 1
      end.
      intros. 
      bsplit; auto.
        simpl. solve_in_list.

      unfold is_true.
      apply filter_is_promotable; auto.

    rewrite <- filter_reachablity_analysis; auto.
Qed.
