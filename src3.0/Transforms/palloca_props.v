Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import primitives.
Require Import Maps.
Require Import mem2reg.
Require Import opsem_props.
Require Import trans_tactic.

Record PhiInfo := mkPhiInfo {
  PI_f: fdef;
  PI_rd: list l;
  PI_id: id;
  PI_typ: typ;
  PI_num: value;
  PI_align: align
}.

Definition PI_newids (pinfo: PhiInfo): ATree.t (id * id * id) :=
  (fst (gen_fresh_ids (PI_rd pinfo) (getFdefLocs (PI_f pinfo)))).

Definition PI_succs (pinfo: PhiInfo): ATree.t (list l):=
  successors (PI_f pinfo).

Definition PI_preds (pinfo: PhiInfo): ATree.t (list l):=
  make_predecessors (PI_succs pinfo).

Definition promotable_alloca (f:fdef) (pid:id) (ty:typ) (num:value) (al:align)
  : Prop :=
match getEntryBlock f with
| Some (block_intro _ _ cs _) =>
    In (insn_alloca pid ty num al) cs /\ is_promotable f pid
| _ => False
end.

Definition WF_PhiInfo (pinfo: PhiInfo) : Prop :=
promotable_alloca (PI_f pinfo) (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo)
  (PI_align pinfo) /\
reachablity_analysis (PI_f pinfo) = Some (PI_rd pinfo).

Lemma find_promotable_alloca_spec: forall f cs nids pid ptyp num pal,
  find_promotable_alloca f cs nids = Some (pid, ptyp, num, pal) ->
  In (insn_alloca pid ptyp num pal) cs /\ is_promotable f pid.
Proof.
  induction cs; simpl; intros.
    congruence.

    destruct_cmd a; try solve [apply IHcs in H; destruct H as [H1 H2]; eauto].
    remember (is_promotable f i0 && negb (in_dec id_dec i0 nids)) as R.
    destruct R; try solve [apply IHcs in H; destruct H as [H1 H2]; eauto].
    inv H.
    symmetry in HeqR. apply andb_true_iff in HeqR. destruct HeqR.
    eauto.
Qed.

Ltac simpl_WF_PhiInfo :=
match goal with
| H : WF_PhiInfo ?pinfo |- _ =>
  destruct H as [H _];
  unfold promotable_alloca in H;
  match goal with
  | H : match getEntryBlock ?PI_f0 with
        | Some _ => _
        | None => _
        end |- _ =>
    remember (getEntryBlock PI_f0) as R;
    destruct R as [[]|]; tinv H
  end
end.

Lemma WF_PhiInfo_spec1: forall pinfo,
  WF_PhiInfo pinfo ->
  uniqFdef (PI_f pinfo) ->
  lookupInsnViaIDFromFdef (PI_f pinfo) (PI_id pinfo) =
    Some
     (insn_cmd
       (insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo)
         (PI_align pinfo))).
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [H _].
  symmetry in HeqR.
  apply entryBlockInFdef in HeqR.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HeqR; eauto.
  simpl in HeqR. auto.
Qed.

Lemma used_in_phi_fun_spec: forall pid (a0 : bool) (b : phinode),
  a0 || used_in_phi pid b = false -> a0 = false.
Proof.
  intros. apply orb_false_iff in H. destruct H; auto.
Qed.

Lemma unused_in_phis__unused_in_phi: forall (pid id0 : id) (ps : phinodes)
  (p0 : phinode) (J1 : ret p0 = lookupPhiNodeViaIDFromPhiNodes ps id0)
  (J2 : fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
          ps false = false),
  used_in_phi pid p0 = false.
Proof.
  induction ps; simpl; intros.
    congruence.

    assert (fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
              ps false = false /\ used_in_phi pid a = false) as J3.
      apply fold_left_or_false; auto.
        apply used_in_phi_fun_spec.

    destruct J3 as [J3 J4].
    destruct (getPhiNodeID a == id0); subst; eauto.
      inv J1. auto.
Qed.

Lemma unused_in_value__neg_valueEqB: forall pid v,
  used_in_value pid v = false ->
  negb (valueEqB v (value_id pid)).
Proof.
  intros.
  unfold valueEqB.
  destruct v as [i0|c]; inv H; simpl.
    destruct (value_dec (value_id i0) (value_id pid)); simpl.
      inversion e. subst.
      destruct (id_dec pid pid); subst; inv H1; try congruence.

      reflexivity.

    destruct (value_dec (value_const c) (value_id pid)); simpl.
      congruence.
      reflexivity.
Qed.

Lemma used_in_cmd_fun_spec:
  forall pid acc0 c,
  (if used_in_cmd pid c then
    match c with
    | insn_load _ _ _ _ => acc0
    | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
    | _ => false
    end
  else acc0) = true -> acc0 = true.
Proof.
  intros. clear - H.
  destruct acc0; auto.
  destruct (used_in_cmd pid c); auto.
  destruct c; auto.
  apply andb_true_iff in H. destruct H; auto.
Qed.

Lemma unused_in_cmds__unused_in_cmd: forall (pid id0 : id) (cs : cmds)
  (c0 : cmd) (J1 : ret c0 = lookupCmdViaIDFromCmds cs id0)
  (J2 : fold_left
          (fun acc0 c =>
           if used_in_cmd pid c then
             match c with
             | insn_load _ _ _ _ => acc0
             | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
             | _ => false
             end
           else acc0) cs true = true),
  match c0 with
  | insn_load _ _ _ _ => True
  | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid))
  | _ => used_in_cmd pid c0 = false
  end.
Proof.
  induction cs; simpl; intros.
    congruence.

    assert (
      fold_left
        (fun acc0 c =>
         if used_in_cmd pid c then
           match c with
           | insn_load _ _ _ _ => acc0
           | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
           | _ => false
           end
         else acc0) cs true = true /\
      (if used_in_cmd pid a then
         match a with
         | insn_load _ _ _ _ => true
         | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && true
         | _ => false
         end
       else true) = true) as J3.
      apply fold_left_and_true; auto.
        apply used_in_cmd_fun_spec.

    destruct J3 as [J3 J4]. clear J2.
    destruct (eq_atom_dec id0 (getCmdLoc a)); subst.
      inv J1. clear IHcs J3.
      remember (used_in_cmd pid a) as R.
      destruct R.
        destruct a; auto.
          apply andb_true_iff in J4.
          destruct J4; auto.
        destruct a; auto.
          simpl in *.
          symmetry in HeqR.
          apply orb_false_iff in HeqR.
           destruct HeqR.
           apply unused_in_value__neg_valueEqB; auto.

      clear J4.
      eapply IHcs in J3; eauto.
Qed.

Lemma is_promotable_cmd_spec: forall pid (a0 : bool) (b : cmd)
  (H: is_promotable_cmd pid a0 b = true), a0 = true.
Proof.
  unfold is_promotable_cmd. intros.
  destruct_if; auto.
  destruct b; try congruence.
  apply andb_true_iff in H1. 
  destruct H1 as [J1 J2]. subst.
  rewrite J1. auto.    
Qed.

Lemma is_promotable_fun_spec: forall pid (a0: bool) (b: block)
  (H1: is_promotable_fun pid a0 b = true), a0 = true.
Proof.
  intros. clear - H1.
  destruct a0; auto.
  unfold is_promotable_fun in H1.
  destruct b as [? p c t].
  destruct (fold_left
    (fun (re : bool) (p : phinode) => re || used_in_phi pid p) p
    (used_in_tmn pid t)); auto.
  apply fold_left_and_true in H1.
  destruct H1 as [_ H1]; auto.
  apply used_in_cmd_fun_spec.
Qed.

Lemma is_promotable_spec: forall pid id0 instr bs,
  fold_left (is_promotable_fun pid) bs true = true ->
  lookupInsnViaIDFromBlocks bs id0 = ret instr ->
  match instr with
  | insn_cmd c0 =>
    match c0 with
    | insn_load _ _ _ _ => True
    | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid))
    | _ => used_in_cmd pid c0 = false
    end
  | _ => used_in_insn pid instr = false
  end.
Proof.
  induction bs; simpl; intros.
    congruence.

    assert (fold_left (is_promotable_fun pid) bs true = true /\
            is_promotable_fun pid true a = true) as J.
      apply fold_left_and_true; auto.
        apply is_promotable_fun_spec.

    destruct J as [J1 J2].
    remember (lookupInsnViaIDFromBlock a id0) as R.
    destruct R.
      inv H0.
      clear - J2 HeqR.
      destruct a as [? p c t]; simpl in *.
      remember (fold_left
                 (fun (re : bool) (p : phinode) => re || used_in_phi pid p) p
                 (used_in_tmn pid t)) as R.
      destruct R; tinv J2.
      assert (fold_left
               (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
                 p false = false /\
              used_in_tmn pid t = false) as J.
        apply fold_left_or_false; auto.
          apply used_in_phi_fun_spec.

      destruct J as [J3 J4]. clear HeqR0.
      remember (lookupPhiNodeViaIDFromPhiNodes p id0) as R1.
      remember (lookupCmdViaIDFromCmds c id0) as R2.
      destruct R1.
        inv HeqR.
        clear - J3 HeqR1. simpl.
        eapply unused_in_phis__unused_in_phi in J3; eauto.

        destruct R2; inv HeqR.
          clear - J2 HeqR2. simpl.
          eapply unused_in_cmds__unused_in_cmd in J2; eauto.

          destruct_if. simpl. auto.

      apply IHbs in H0; auto.
Qed.

Lemma WF_PhiInfo_spec3: forall pinfo,
  WF_PhiInfo pinfo ->
  forall instr id0,
    lookupInsnViaIDFromFdef (PI_f pinfo) id0 = Some instr ->
    match instr with
    | insn_cmd c0 =>
      match c0 with
      | insn_load _ _ _ _ => True
      | insn_store _ _ v _ _ => negb (valueEqB v (value_id (PI_id pinfo)))
      | _ => used_in_cmd (PI_id pinfo) c0 = false
      end
    | _ => used_in_insn (PI_id pinfo) instr = false
    end.
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [_ H].
  destruct (PI_f pinfo). simpl in *.
  eapply is_promotable_spec in H0; eauto.
Qed.

Definition wf_use_at_head (pinfo:PhiInfo) (v:value) :=
used_in_value (PI_id pinfo) v = false.

Lemma used_in_phi__wf_use_at_head: forall pinfo v0 (p : phinode)
  (H0 : used_in_phi (PI_id pinfo) p = false)
  (H1 : valueInInsnOperands v0 (insn_phinode p)),
  wf_use_at_head pinfo v0.
Proof.
  intros.
  unfold wf_use_at_head.
  destruct p; simpl in *.
  induction l0; tinv H1.
    simpl_prod.
    simpl in *.
    apply orb_false_iff in H0.
    destruct H0 as [J1 J2].
    destruct H1 as [H1 | H1]; subst; auto.
Qed.

Lemma neg_valueEqB__unused_in_value: forall pid v,
  negb (valueEqB v (value_id pid)) ->
  used_in_value pid v = false.
Proof.
  intros.
  unfold valueEqB in H.
  destruct v as [i0|]; auto.
  destruct (value_dec (value_id i0) (value_id pid)); simpl in *.
    congruence.

    destruct (id_dec i0 pid); subst; auto.
      congruence.
Qed.

Lemma unused_in_list_value__unused_in_value: forall pid v0 l0,
  used_in_list_value pid l0 = false ->
  valueInListValue v0 l0 ->
  used_in_value pid v0 = false.
Proof.
  induction l0; simpl; intros.
    inv H0.

    simpl_prod.
    apply orb_false_iff in H.
    destruct H as [J1 J2].
    inv H0; auto.
Qed.

Lemma unused_in_params__used_in_value: forall pid v0 ps
  (H1: fold_left
         (fun (acc : bool) (p : typ * attributes * value) =>
          let '(_, v) := p in used_in_value pid v || acc) ps false = false)
  (H2 : valueInParams v0 ps),
  used_in_value pid v0 = false.
Proof.
  induction ps as [|[]]; simpl; intros.
    inv H2.

    assert (forall (a : bool) (b : typ * attributes * value),
      (let '(_, v1) := b in used_in_value pid v1 || a) = false -> a = false).
      intros. destruct b.
      apply orb_false_iff in H.
      destruct H; auto.
    apply fold_left_or_false in H1; auto.
    destruct H1 as [J1 J2]. clear H.
    apply orb_false_iff in J2.
    destruct J2.
    unfold valueInParams in *.
    simpl in H2.
    remember (split ps) as R.
    destruct R.
    simpl in H2.
    destruct H2 as [H2 | H2]; subst; auto.
Qed.

Lemma WF_PhiInfo_spec4: forall pinfo,
  WF_PhiInfo pinfo ->
  forall instr id0 v0,
    lookupInsnViaIDFromFdef (PI_f pinfo) id0 = Some instr ->
    match instr with
    | insn_cmd c0 =>
      match c0 with
      | insn_load _ _ _ _ => False
      | insn_store _ _ v _ _ => v = v0
      | _ => valueInCmdOperands v0 c0
      end
    | _ => valueInInsnOperands v0 instr
    end ->
    wf_use_at_head pinfo v0.
Proof.
  intros.
  apply WF_PhiInfo_spec3 in H0; auto.
  destruct instr as [p|c|t].
    simpl in H0.
    eapply used_in_phi__wf_use_at_head in H1; eauto.

    unfold wf_use_at_head.
    destruct c; tinv H1; simpl in *;
      try solve [
        subst; auto |
        match goal with
        | H0 : used_in_value _ ?v1 || used_in_value _ ?v2 = false,
          H1 : ?v0 = ?v1 \/ ?v0 = ?v2 |- _ =>
            apply orb_false_iff in H0;
            destruct H0 as [J1 J2];
            destruct H1; subst; auto
        end
      ].

      subst.
      apply neg_valueEqB__unused_in_value; auto.

      apply orb_false_iff in H0.
      destruct H0 as [J1 J2].
      destruct H1 as [H1 | H1]; subst; auto.
      eapply unused_in_list_value__unused_in_value in J2; eauto.

      apply orb_false_iff in H0.
      destruct H0 as [J1 J2].
      apply orb_false_iff in J1.
      destruct J1 as [J1 J3].
      destruct H1 as [H1 | [H1 | H1]]; subst; auto.

      apply orb_false_iff in H0.
      destruct H0 as [J1 J2].
      destruct H1 as [H1 | H1]; subst;
        eauto using unused_in_params__used_in_value.

    unfold wf_use_at_head.
    destruct t; simpl in *; subst;
      try solve [auto | match goal with
                        | H1: False |- _ => inv H1
                        end].
Qed.

Lemma unused_in_phis__unused_in_phi': forall (pid: id) (ps: phinodes)
  (p0 : phinode) (J1 : InPhiNodesB p0 ps)
  (J2 : fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
          ps false = false),
  used_in_phi pid p0 = false.
Proof.
  induction ps; simpl; intros.
    congruence.

    assert (fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
              ps false = false /\ used_in_phi pid a = false) as J3.
      apply fold_left_or_false; auto.
        apply used_in_phi_fun_spec.

    destruct J3 as [J3 J4].
    apply orb_true_iff in J1.
    destruct J1 as [J1 | J1]; auto.
      apply phinodeEqB_inv in J1. subst. auto.
Qed.

Lemma unused_in_cmds__unused_in_cmd': forall (pid id0 : id) (cs : cmds)
  (c0 : cmd) (J1 : InCmdsB c0 cs)
  (J2 : fold_left
          (fun acc0 c =>
           if used_in_cmd pid c then
             match c with
             | insn_load _ _ _ _ => acc0
             | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
             | _ => false
             end
           else acc0) cs true = true),
  match c0 with
  | insn_load _ _ _ _ => True
  | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid))
  | _ => used_in_cmd pid c0 = false
  end.
Proof.
  induction cs; simpl; intros.
    congruence.

    assert (
      fold_left
        (fun acc0 c =>
         if used_in_cmd pid c then
           match c with
           | insn_load _ _ _ _ => acc0
           | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
           | _ => false
           end
         else acc0) cs true = true /\
      (if used_in_cmd pid a then
         match a with
         | insn_load _ _ _ _ => true
         | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && true
         | _ => false
         end
       else true) = true) as J3.
      apply fold_left_and_true; auto.
        apply used_in_cmd_fun_spec.

    destruct J3 as [J3 J4]. clear J2.
    apply orb_true_iff in J1.
    destruct J1 as [J1 | J1].
      clear IHcs J3.
      apply cmdEqB_inv in J1. subst.
      remember (used_in_cmd pid a) as R.
      destruct R.
        destruct a; auto.
          apply andb_true_iff in J4.
          destruct J4; auto.

        destruct a; auto.
          simpl in *.
          symmetry in HeqR.
          apply orb_false_iff in HeqR.
          destruct HeqR.
          apply unused_in_value__neg_valueEqB; auto.

      clear J4.
      eapply IHcs in J3; eauto.
Qed.

Lemma is_promotable_spec': forall pid b instr bs,
  fold_left (is_promotable_fun pid) bs true = true ->
  insnInBlockB instr b ->
  InBlocksB b bs ->
  match instr with
  | insn_cmd c0 =>
    match c0 with
    | insn_load _ _ _ _ => True
    | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid))
    | _ => used_in_cmd pid c0 = false
    end
  | _ => used_in_insn pid instr = false
  end.
Proof.
  induction bs; simpl; intros; try congruence.

    assert (fold_left (is_promotable_fun pid) bs true = true /\
            is_promotable_fun pid true a = true) as J.
      apply fold_left_and_true; auto.
        apply is_promotable_fun_spec.

    destruct J as [J1 J2]. clear H.
    apply orb_true_iff in H1.
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst.
      clear - J2 H0.
      destruct a as [? p c t]; simpl in *.
      remember (fold_left
                 (fun (re : bool) (p : phinode) => re || used_in_phi pid p) p
                 (used_in_tmn pid t)) as R.
      destruct R; tinv J2.
      assert (fold_left
               (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
                 p false = false /\
              used_in_tmn pid t = false) as J.
        apply fold_left_or_false; auto.
          apply used_in_phi_fun_spec.

      destruct J as [J3 J4]. clear HeqR.
      destruct instr; simpl in *.
        eapply unused_in_phis__unused_in_phi' in J3; eauto.
        eapply unused_in_cmds__unused_in_cmd' in J2; eauto.
        apply terminatorEqB_inv in H0. subst. auto.

      apply IHbs in J1; auto.
Qed.

Lemma WF_PhiInfo_spec5: forall pinfo pn b,
  WF_PhiInfo pinfo ->
  phinodeInFdefBlockB pn (PI_f pinfo) b = true ->
  used_in_phi (PI_id pinfo) pn = false.
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [_ H].
  destruct (PI_f pinfo). simpl in *.
  unfold phinodeInFdefBlockB in H0.
  apply andb_true_iff in H0.
  destruct H0.
  eapply is_promotable_spec' with (instr:=insn_phinode pn) in H1; eauto.
Qed.

Lemma WF_PhiInfo_spec6: forall pinfo l' ps' cs' tmn',
  WF_PhiInfo pinfo ->
  uniqFdef (PI_f pinfo) ->
  ret block_intro l' ps' cs' tmn' = lookupBlockViaLabelFromFdef (PI_f pinfo) l'
    ->
  ~ In (PI_id pinfo) (getPhiNodesIDs ps').
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [H _].
  symmetry in HeqR.
  apply entryBlockInFdef in HeqR.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H; eauto.
  simpl in H.

  symmetry in H1.
  apply lookupBlockViaLabelFromFdef_inv in H1; auto.
  destruct H1 as [_ H1].
  intro J.
  eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef in J; eauto.
  destruct J as [p2 [J1 J2]].
  rewrite H in J1. congruence.
Qed.

Lemma PhiInfo_must_be_promotable_alloca: forall pinfo l0 ps0 cs1 c cs2 tmn0,
  WF_PhiInfo pinfo ->
  uniqFdef (PI_f pinfo) ->
  getCmdLoc c = PI_id pinfo ->
  (forall id1 typ1 v1 al1, c <> insn_alloca id1 typ1 v1 al1) ->
  blockInFdefB (block_intro l0 ps0 (cs1++c::cs2) tmn0) (PI_f pinfo) = true ->
  False.
Proof.
  intros.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H3; eauto using in_middle.
  apply WF_PhiInfo_spec1 in H; auto.
  simpl in H3. rewrite H1 in H3. rewrite H3 in H. inv H.
  assert (W:=@H2 (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo) (PI_align pinfo)).
  auto.
Qed.

Lemma WF_PhiInfo_spec2: forall pinfo S los nts Ps,
  WF_PhiInfo pinfo ->
  wf_fdef S (module_intro los nts Ps) (PI_f pinfo) ->
  exists mc, flatten_typ (los, nts) (PI_typ pinfo) = Some mc.
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [J1 J2].
  symmetry in HeqR.
  apply entryBlockInFdef in HeqR.
  eapply wf_fdef__wf_cmd in HeqR; eauto.
  inv HeqR.
  eapply flatten_typ_total; eauto.
Qed.

Lemma WF_PhiInfo__succs : forall pinfo l1 ps1 cs1 tmn1
  (Huniq: uniqFdef (PI_f pinfo)),
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) (PI_f pinfo) = true ->
  successors_terminator tmn1 <> nil ->
  exists sc, exists scs, (PI_succs pinfo) ! l1 = Some (sc::scs).
Proof.
  intros.
  eapply blockInFdefB__successors in H; eauto.
  unfold ls in *. unfold PI_succs.
  destruct (successors_terminator tmn1); try congruence. eauto.
Qed.

Lemma WF_PhiInfo__preds : forall pinfo l1 ps1 cs1 tmn1 l0
  (Huniq: uniqFdef (PI_f pinfo)),
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) (PI_f pinfo) = true ->
  In l0 (successors_terminator tmn1) ->
  exists prd, exists prds, (PI_preds pinfo) ! l0 = Some (prd::prds).
Proof.
  intros.
  eapply blockInFdefB__successors in H; eauto.
  assert (In l0 (successors (PI_f pinfo))!!!l1) as Hin.
    unfold successors_list.
    unfold ls, l in *.
    rewrite H. auto.
  apply make_predecessors_correct in Hin.
  unfold successors_list in Hin.
  unfold ls, l in *. unfold PI_preds, PI_succs.
  destruct ((make_predecessors (successors (PI_f pinfo))) ! l0); tinv Hin.
  destruct l2; tinv Hin.
  eauto.
Qed.

Definition is_temporary i0 (newids : ATree.t (id * id * id)) : Prop :=
exists l0,
  match ATree.get l0 newids with
  | Some (lid, pid, sid) => i0 == lid \/ i0 == pid \/ i0 == sid
  | None => False
  end.

Definition gen_fresh_ids_fun :=
  (fun (acc : ATree.t (atom * atom * atom) * list atom) (l0 : atom) =>
    let '(nids', ex_ids') := acc in
    let 'exist lid' _ := atom_fresh_for_list ex_ids' in
    let 'exist pid' _ := atom_fresh_for_list (lid' :: ex_ids') in
    let 'exist sid' _ := atom_fresh_for_list (pid' :: lid' :: ex_ids') in
    (ATree.set l0 (lid', pid', sid') nids',
     sid' :: pid' :: lid' :: ex_ids')).

Lemma gen_fresh_ids__spec_aux: forall i0 ex_ids0 rds nids ex_ids,
  (forall j0, In j0 ex_ids0 -> In j0 ex_ids) ->
  (forall j0, is_temporary j0 nids -> ~ In j0 ex_ids0) ->
  is_temporary i0 (fst (fold_left gen_fresh_ids_fun rds (nids, ex_ids))) ->
  ~ In i0 ex_ids0.
Proof.
  induction rds; simpl; intros; auto.
  remember (atom_fresh_for_list ex_ids) as R1.
  destruct R1 as [lid' Jlid'].
  remember (atom_fresh_for_list (lid'::ex_ids)) as R2.
  destruct R2 as [pid' Jpid'].
  remember (atom_fresh_for_list (pid'::lid'::ex_ids)) as R3.
  destruct R3 as [sid' Jsid'].
  apply IHrds in H1; auto.
    intros j0 Hin. simpl. auto.

    intros j0 Histmp.
    destruct Histmp as [l0 Histmp].
    remember (
      @ATree.get (prod (prod id id) id) l0
               (@ATree.set (prod (prod atom atom) atom) a
                  (@pair (prod atom atom) atom (@pair atom atom lid' pid')
                     sid') nids)
      ) as R.
    destruct R as [[[]]|]; tinv Histmp.
    destruct (a == l0); subst.
      intro J. apply H in J.
      rewrite ATree.gss in HeqR.
      inv HeqR.
      destruct Histmp as [EQ | [EQ | EQ]]; subst.
        destruct (j0 == lid'); subst; simpl in EQ; try congruence; auto.
        destruct (j0 == pid'); subst; simpl in EQ; try congruence.
          apply Jpid'. simpl. auto.
        destruct (j0 == sid'); subst; simpl in EQ; try congruence; auto.
          apply Jsid'. simpl. auto.

      rewrite ATree.gso in HeqR; auto.
      apply H0.
      exists l0. unfold id. rewrite <- HeqR. auto.
Qed.

Lemma gen_fresh_ids__spec: forall i0 rds ex_ids,
  is_temporary i0 (fst (gen_fresh_ids rds ex_ids)) -> ~ In i0 ex_ids.
Proof.
  unfold gen_fresh_ids.
  intros.
  fold gen_fresh_ids_fun in H.
  eapply gen_fresh_ids__spec_aux in H; eauto.
    intros j0 J.
    destruct J as [l0 J].
    rewrite ATree.gempty in J. inv J.
Qed.

(* There are some other getFdefLocs lemmas in sb_ds_trans_lib.v.
   We should merge them. *)
Lemma getCmdLoc_in_getFdefLocs : forall f1 c cs tmn2 id0 l1 ps1 cs11
  (HBinF : blockInFdefB (block_intro l1 ps1 (cs11 ++ c :: cs) tmn2) f1 = true)
  (Hget : getCmdLoc c = id0),
  In id0 (getFdefLocs f1).
Proof.
  intros. subst.
  destruct f1 as [f bs]. destruct f as [fnattrs5 typ5 id5 args5 varg5]. simpl.
  destruct (split args5).
  apply in_or_app. right.
  eapply in_getBlockLocs__in_getBlocksLocs in HBinF; eauto.
  simpl.
  apply in_or_app. right.
  apply in_or_app. left.
  apply getCmdLoc_in_getCmdsLocs with (c:=c); auto.
  apply in_middle.
Qed.

Lemma temporary_must_be_fresh: forall l0 ps0 cs0 c cs2 tmn0 pinfo i0
  (Hin : blockInFdefB (block_intro l0 ps0 (cs0 ++ c :: cs2) tmn0)
           (PI_f pinfo) = true)
  (Hld : is_temporary i0 (PI_newids pinfo))
  (Heq : getCmdLoc c = i0),
  False.
Proof.
  intros.
  eapply getCmdLoc_in_getFdefLocs in Hin; eauto.
  apply gen_fresh_ids__spec in Hld; auto.
Qed.

Lemma WF_PhiInfo_fresh: forall pinfo lid pid sid l0 (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  ret (lid, pid, sid) = (PI_newids pinfo) ! l0 ->
  PI_id pinfo <> lid /\ PI_id pinfo <> pid /\ PI_id pinfo <> sid.
Proof.
  intros.
  apply WF_PhiInfo_spec1 in Huniq; auto.
  apply lookupInsnViaIDFromFdef__insnInFdefBlockB in Huniq.
  destruct Huniq as [b1 HbInF].
  simpl in HbInF.
  apply andb_true_iff in HbInF.
  destruct HbInF as [J1 J2].
  destruct b1. simpl in J1.
  apply InCmdsB_in in J1.
  apply in_split in J1.
  destruct J1 as [cs1 [cs2 J1]]; subst.
  destruct H as [J1 J6].
  destruct (PI_id pinfo == lid); subst.
    eapply temporary_must_be_fresh in J2; eauto.
    simpl. exists l0. rewrite <- H0.
    destruct (PI_id pinfo == PI_id pinfo); try congruence.
      simpl. left. reflexivity.
  destruct (PI_id pinfo == pid); subst.
    eapply temporary_must_be_fresh in J2; eauto.
    simpl. exists l0. rewrite <- H0.
    destruct (PI_id pinfo == PI_id pinfo); try congruence.
      simpl. right. left. reflexivity.
  destruct (PI_id pinfo == sid); subst; auto.
    eapply temporary_must_be_fresh in J2; eauto.
    simpl. exists l0. rewrite <- H0.
    destruct (PI_id pinfo == PI_id pinfo); try congruence.
      simpl. right. right. reflexivity.
Qed.

Lemma WF_PhiInfo_spec9: forall pinfo l0 l3 ps3 cs3 l1 ps1 cs1 tmn1 bid
  (Huniq: uniqFdef (PI_f pinfo)),
  lookupBlockViaLabelFromFdef (PI_f pinfo) l0 =
    ret block_intro l1 ps1 cs1 tmn1 ->
  blockInFdefB (block_intro l3 ps3 cs3 (insn_br_uncond bid l0)) (PI_f pinfo) ->
  exists succs, (PI_succs pinfo) ! l3 = Some succs /\ In l1 succs.
Proof.
  intros.
  apply blockInFdefB__successors in H0; auto.
  simpl in H0.
  unfold ls, l in *. unfold PI_succs.
  rewrite H0.
  exists (l0::nil).
  split; auto.
  apply lookupBlockViaLabelFromFdef_inv in H; auto.
  destruct H as [EQ _]; subst; simpl; auto.
Qed.

Lemma WF_PhiInfo_spec8: forall pinfo td c l1 l2 l3 ps3 cs3 l0 ps0 cs0 tmn0 bid
  Cond (Huniq: uniqFdef (PI_f pinfo)),
  (if isGVZero td c
   then lookupBlockViaLabelFromFdef (PI_f pinfo) l2
   else lookupBlockViaLabelFromFdef (PI_f pinfo) l1) =
  ret block_intro l0 ps0 cs0 tmn0 ->
  blockInFdefB (block_intro l3 ps3 cs3 (insn_br bid Cond l1 l2)) (PI_f pinfo) ->
  exists succs, (PI_succs pinfo) ! l3 = Some succs /\ In l0 succs.
Proof.
  intros.
  apply blockInFdefB__successors in H0; auto.
  simpl in H0.
  unfold ls, l in *. unfold PI_succs.
  rewrite H0.
  exists (l1::l2::nil).
  split; auto.
  destruct (isGVZero td c);
    apply lookupBlockViaLabelFromFdef_inv in H; auto;
    destruct H as [EQ _]; subst; simpl; auto.
Qed.

Lemma gen_fresh_ids__spec3_aux: forall rds nids ex_ids i0 a b c,
  (forall a b c j0, nids ! j0 = Some (a, b, c) -> a <> b /\ a <> c /\ b <> c) ->
  (fst (fold_left gen_fresh_ids_fun rds (nids, ex_ids))) ! i0
    = Some (a, b, c) ->
  a <> b /\ a <> c /\ b <> c.
Proof.
  induction rds; simpl; intros; eauto.
  remember (atom_fresh_for_list ex_ids) as R1.
  destruct R1 as [lid' Jlid'].
  remember (atom_fresh_for_list (lid'::ex_ids)) as R2.
  destruct R2 as [pid' Jpid'].
  remember (atom_fresh_for_list (pid'::lid'::ex_ids)) as R3.
  destruct R3 as [sid' Jsid'].
  apply IHrds in H0; auto.
    intros a1 b1 c1 j1 J.
    destruct (a == j1); subst.
      rewrite ATree.gss in J.
      inv J.
      destruct (a1 == b1); subst; auto.
      contradiction Jpid'; simpl; auto.

      destruct (a1 == c1); subst; auto.
      contradiction Jsid'; simpl; auto.

      destruct (b1 == c1); subst; auto.
      contradiction Jsid'; simpl; auto.

      rewrite ATree.gso in J; eauto.
Qed.

Lemma gen_fresh_ids__spec3: forall rds ex_ids l0 lib pid sid,
  Some (lib, pid, sid) = (fst (gen_fresh_ids rds ex_ids)) ! l0 ->
  lib <> pid /\ lib <> sid /\ pid <> sid.
Proof.
  unfold gen_fresh_ids.
  intros.
  fold gen_fresh_ids_fun in H.
  symmetry in H.
  eapply gen_fresh_ids__spec3_aux in H; eauto.
    intros a b c j0 J.
    rewrite ATree.gempty in J. inv J.
Qed.

Lemma gen_fresh_ids__spec5_aux: forall rds nids' nids ex_ids ex_ids',
  (forall i0, is_temporary i0 nids -> In i0 ex_ids) ->
  (nids', ex_ids') = (fold_left gen_fresh_ids_fun rds (nids, ex_ids)) ->
  (forall i0, is_temporary i0 nids' -> In i0 ex_ids').
Proof.
  induction rds; simpl; intros.
    inv H0. auto.

    remember (atom_fresh_for_list ex_ids) as R1.
    destruct R1 as [lid' Jlid'].
    remember (atom_fresh_for_list (lid'::ex_ids)) as R2.
    destruct R2 as [pid' Jpid'].
    remember (atom_fresh_for_list (pid'::lid'::ex_ids)) as R3.
    destruct R3 as [sid' Jsid'].
    eapply IHrds in H0; eauto.
    intros.
    destruct H2 as [l0 H2].
    unfold id in *.
    remember ((ATree.set a (lid', pid', sid') nids) ! l0) as R.
    destruct R as [[[]]|]; tinv H2.
    destruct (a == l0); subst.
      rewrite ATree.gss in HeqR.
      inv HeqR.
      simpl.
      destruct H2 as [H2 | [H2 | H2]].
        destruct (i1 == lid'); simpl in H2; try congruence; auto.
        destruct (i1 == pid'); simpl in H2; try congruence; auto.
        destruct (i1 == sid'); simpl in H2; try congruence; auto.

      simpl. right. right. right.
      rewrite ATree.gso in HeqR; auto.
      apply H.
      exists l0. unfold id in *. rewrite <- HeqR. auto.
Qed.

Lemma gen_fresh_ids__spec4_aux: forall rds nids' nids ex_ids
  (Hp: forall i0, is_temporary i0 nids -> In i0 ex_ids),
  (forall (l1 l2 : atom) (a1 b1 c1 a2 b2 c2 : id),
  l1 <> l2 ->
  ret (a1, b1, c1) = nids ! l1 ->
  ret (a2, b2, c2) = nids ! l2 ->
  a1 <> a2 /\
  a1 <> b2 /\
  a1 <> c2 /\
  b1 <> a2 /\ b1 <> b2 /\ b1 <> c2 /\ c1 <> a2 /\ c1 <> b2 /\ c1 <> c2) ->
  nids' = fst (fold_left gen_fresh_ids_fun rds (nids, ex_ids)) ->
  forall (l1 l2 : atom) (a1 b1 c1 a2 b2 c2 : id),
  l1 <> l2 ->
  ret (a1, b1, c1) = nids' ! l1 ->
  ret (a2, b2, c2) = nids' ! l2 ->
  a1 <> a2 /\
  a1 <> b2 /\
  a1 <> c2 /\
  b1 <> a2 /\ b1 <> b2 /\ b1 <> c2 /\ c1 <> a2 /\ c1 <> b2 /\ c1 <> c2.
Proof.
  induction rds; simpl; intros; subst; try solve [eapply H; eauto].
  remember (atom_fresh_for_list ex_ids) as R1.
  destruct R1 as [lid' Jlid'].
  remember (atom_fresh_for_list (lid'::ex_ids)) as R2.
  destruct R2 as [pid' Jpid'].
  remember (atom_fresh_for_list (pid'::lid'::ex_ids)) as R3.
  destruct R3 as [sid' Jsid'].
  apply IHrds with (l1:=l1)(l2:=l2)(nids:=ATree.set a (lid', pid', sid') nids)
    (ex_ids:=sid' :: pid' :: lid' :: ex_ids)(a2:=a2)(b2:=b2)(c2:=c2) in H2;
    auto.
    clear IHrds.

    intros.
    destruct H0 as [l0 H0].
    unfold id in *.
    remember ((ATree.set a (lid', pid', sid') nids) ! l0) as R.
    destruct R as [[[]]|]; tinv H0.
    destruct (a == l0); subst.
      rewrite ATree.gss in HeqR.
      inv HeqR.
      simpl.
      destruct H0 as [H0 | [H0 | H0]].
        destruct (i0 == lid'); simpl in H0; try congruence; auto.
        destruct (i0 == pid'); simpl in H0; try congruence; auto.
        destruct (i0 == sid'); simpl in H0; try congruence; auto.

      simpl. right. right. right.
      rewrite ATree.gso in HeqR; auto.
      apply Hp.
      exists l0. unfold id in *. rewrite <- HeqR. auto.

  clear IHrds.
  intros.
  destruct (a == l0); subst.
    rewrite ATree.gss in H4.
    inv H4.
    destruct (l0 == l3); subst; try congruence.
    rewrite ATree.gso in H5; auto.
      assert (In a3 ex_ids) as Hina.
        apply Hp. exists l3. unfold id. rewrite <- H5.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) a3 a3); simpl.
          left. reflexivity. congruence.
      assert (In b3 ex_ids) as Hinb.
        apply Hp. exists l3. unfold id. rewrite <- H5.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) b3 b3); simpl.
          right. left. reflexivity. congruence.
      assert (In c3 ex_ids) as Hinc.
        apply Hp. exists l3. unfold id. rewrite <- H5.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) c3 c3); simpl.
          right. right. reflexivity. congruence.
      clear - Hina Hinb Hinc Jlid' Jpid' Jsid'.
      simpl in *.
      repeat split; try intro J; subst; auto.

    rewrite ATree.gso in H4; auto.
    destruct (a == l3); subst.
      rewrite ATree.gss in H5.
      inv H5.
      assert (In a0 ex_ids) as Hina.
        apply Hp. exists l0. unfold id. rewrite <- H4.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) a0 a0); simpl.
          left. reflexivity. congruence.
      assert (In b0 ex_ids) as Hinb.
        apply Hp. exists l0. unfold id. rewrite <- H4.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) b0 b0); simpl.
          right. left. reflexivity. congruence.
      assert (In c0 ex_ids) as Hinc.
        apply Hp. exists l0. unfold id. rewrite <- H4.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) c0 c0); simpl.
          right. right. reflexivity. congruence.
      clear - Hina Hinb Hinc Jlid' Jpid' Jsid'.
      simpl in *.
      repeat split; try intro J; subst; auto.

      rewrite ATree.gso in H5; eauto.
Qed.

Lemma gen_fresh_ids__spec4: forall nids rds ex_ids,
  nids = fst (gen_fresh_ids rds ex_ids) ->
  forall (l1 l2 : atom) (a1 b1 c1 a2 b2 c2 : id),
  l1 <> l2 ->
  ret (a1, b1, c1) = nids ! l1 ->
  ret (a2, b2, c2) = nids ! l2 ->
  a1 <> a2 /\
  a1 <> b2 /\
  a1 <> c2 /\
  b1 <> a2 /\ b1 <> b2 /\ b1 <> c2 /\ c1 <> a2 /\ c1 <> b2 /\ c1 <> c2.
Proof.
  unfold gen_fresh_ids.
  fold gen_fresh_ids_fun.
  intros.
  eapply gen_fresh_ids__spec4_aux; eauto.
    intros. destruct H3 as [l3 H3]. rewrite ATree.gempty in H3. inv H3.
    intros. rewrite ATree.gempty in H4. congruence.
Qed.

Lemma gen_fresh_ids__spec2_aux: forall l1 rds newids nids exids,
  fst (fold_left gen_fresh_ids_fun rds (nids, exids)) = newids ->
  In l1 rds \/ nids ! l1 <> None ->
  newids ! l1 <> None.
Proof.
  induction rds; simpl; intros.
    subst.
    destruct H0 as [H0 | H0]; auto.

    remember (atom_fresh_for_list exids) as R1.
    destruct R1 as [lid' Jlid'].
    remember (atom_fresh_for_list (lid'::exids)) as R2.
    destruct R2 as [pid' Jpid'].
    remember (atom_fresh_for_list (pid'::lid'::exids)) as R3.
    destruct R3 as [sid' Jsid'].
    apply IHrds in H; auto.
    destruct H0 as [[H0 | H0]| H0]; subst; auto.
      right.
      rewrite ATree.gss. congruence.

      right.
      destruct (l1 == a); subst.
        rewrite ATree.gss. congruence.
        rewrite ATree.gso; auto.
Qed.

Lemma gen_fresh_ids__spec2: forall l1 newids rds exids,
  fst (gen_fresh_ids rds exids) = newids ->
  In l1 rds ->
  newids ! l1 <> None.
Proof.
  unfold gen_fresh_ids.
  fold gen_fresh_ids_fun.
  intros.
  eapply gen_fresh_ids__spec2_aux in H; eauto.
Qed.

Lemma reachable_blk_has_newids : forall pinfo l1 (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  reachable (PI_f pinfo) l1 ->
  (PI_newids pinfo) ! l1 <> merror.
Proof.
  intros.
  destruct H as [H1 H2].
  eapply reachable__reachablity_analysis in H2; eauto.
  clear - H2. unfold PI_newids.
  eapply gen_fresh_ids__spec2; eauto.
Qed.

Definition gen_phinode_fun (nids:ATree.t (id * id * id)) ty :=
  (fun (acc : list (value * l)) (p : atom) =>
    (match nids ! p with
       | ret (lid0, _, _) => value_id lid0
       | merror => value_const (const_undef ty)
     end, p) :: acc).

Lemma WF_PhiInfo__getValueViaLabelFromValuels_aux: forall
  (nids:ATree.t (id * id * id)) l3 lid pid sid ty
  (J:ret (lid, pid, sid) = nids ! l3) pds v ps,
  (ret v = getValueViaLabelFromValuels ps l3 -> v = value_id lid) ->
  ret v = getValueViaLabelFromValuels
   (fold_left (gen_phinode_fun nids ty) pds ps) l3 ->
  v = value_id lid.
Proof.
  induction pds; simpl; intros; auto.
    apply IHpds in H0; auto.
      intro J1.
      simpl in J1.
      destruct (@eq_dec l (EqDec_eq_of_EqDec l EqDec_atom) a l3); subst; auto.
        rewrite <- J in J1. inv J1. auto.
Qed.

Lemma WF_PhiInfo__getValueViaLabelFromValuels: forall
  (nids:ATree.t (id * id * id)) l3 lid pid sid ty
  (J:ret (lid, pid, sid) = nids ! l3) pds v,
  ret v = getValueViaLabelFromValuels
   (fold_left (gen_phinode_fun nids ty) pds nil) l3 ->
  v = value_id lid.
Proof.
  intros.
  eapply WF_PhiInfo__getValueViaLabelFromValuels_aux in H; eauto.
    simpl. intros. congruence.
Qed.

Lemma WF_PhiInfo_br_succs_preds: forall pinfo l0 l3 (Hwfpi : WF_PhiInfo pinfo)
  succs (Hsucc : (PI_succs pinfo) ! l3 = ret succs) (Hin : In l0 succs)
  prds (Heq' : (PI_preds pinfo) ! l0 = ret prds),
  In l3 prds.
Proof.
  unfold PI_preds. unfold PI_succs.
  intros.
  destruct Hwfpi as [J1 J2].
  assert (In l0 (successors (PI_f pinfo))!!!l3) as Hin'.
    unfold successors_list.
    unfold ls, l in *.
    rewrite Hsucc. auto.
  apply make_predecessors_correct in Hin'.
  unfold successors_list in Hin'.
  unfold ls, l in *.
  rewrite Heq' in Hin'. auto.
Qed.

Lemma WF_PhiInfo__getIncomingValuesForBlockFromPHINodes_neq_PI_id:
  forall pinfo l0 ps0 cs0 tmn0 B gl lc l5 td (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) ->
  Some l5 = @Opsem.getIncomingValuesForBlockFromPHINodes DGVs
              td ps0 B gl lc ->
  PI_id pinfo `notin` dom l5.
Proof.
  intros.
  apply blockInFdefB_lookupBlockViaLabelFromFdef in H0; auto.
  eapply WF_PhiInfo_spec6 in H; eauto.
  eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec8 in H1; eauto.
Qed.

Lemma WF_PhiInfo__getIncomingValuesForBlockFromPHINodes: forall pinfo l0 ps0 cs0
  tmn0 B gl lc gvsa l5 td (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) ->
  Some l5 = Opsem.getIncomingValuesForBlockFromPHINodes td ps0 B gl lc ->
  lookupAL (GVsT DGVs) lc (PI_id pinfo) = ret gvsa ->
  lookupAL (GVsT DGVs) (Opsem.updateValuesForNewBlock l5 lc) (PI_id pinfo)
    = ret gvsa.
Proof.
  intros.
  eapply WF_PhiInfo__getIncomingValuesForBlockFromPHINodes_neq_PI_id in H1;
    eauto.
  clear H H0 ps0 l0 cs0 tmn0 B td.
  rewrite OpsemProps.updateValuesForNewBlock_spec7'; auto.
Qed.

Lemma WF_PhiInfo__switchToNewBasicBlock: forall (pinfo : PhiInfo)
  (lc : Opsem.GVsMap) (gl : GVMap) (Huniq: uniqFdef (PI_f pinfo))
  (Hwfpi : WF_PhiInfo pinfo) (lc' : Opsem.GVsMap) los nts
  (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (lid' : id) (pid' : id) (sid' : id)
  (HeqR1 : ret (lid', pid', sid') = (PI_newids pinfo) ! l0)
  (prds : list l) (l3 : l) (ps3 : phinodes) (cs11 : list cmd)
  (lid : id) (pid : id) (sid : id)
  (HeqR : ret (lid, pid, sid) = (PI_newids pinfo) ! l3)
  tmn3
  succs (Hsucc : (PI_succs pinfo) ! l3 = ret succs) (Hin : In l0 succs)
  (HBinF : blockInFdefB
            (block_intro l3 ps3 (cs11 ++ nil) tmn3)
            (PI_f pinfo) = true)
  (HuniqF : uniqFdef (PI_f pinfo))
  (HBinF' : blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo))
  (gvsa : GVsT DGVs) (gv : GenericValue)
  (Hlkp1 : lookupAL (GVsT DGVs) lc (PI_id pinfo) = ret gvsa)
  (Hlk2 : lookupAL (GVsT DGVs) lc lid = ret gv)
  (Heq' : (PI_preds pinfo) ! l0 = ret prds)
  (ps3' : phinodes) (cs3' : list cmd)
  (H2 : Opsem.switchToNewBasicBlock (los, nts)
         (block_intro l0
            (gen_phinode pid' (PI_typ pinfo) (PI_newids pinfo) prds :: ps0)
            (insn_store sid' (PI_typ pinfo) (value_id pid')
               (value_id (PI_id pinfo)) (PI_align pinfo)
             :: cs0 ++
                match (PI_succs pinfo) ! l0 with
                | ret nil => nil
                | ret (_ :: _) =>
                    [insn_load lid' (PI_typ pinfo)
                       (value_id (PI_id pinfo)) (PI_align pinfo)]
                | merror => nil
                end) tmn0)
         (block_intro l3 ps3'
            (cs3' ++
             [insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo))
                (PI_align pinfo)]) tmn3) gl lc =
       ret lc'),
  lookupAL (GVsT DGVs) lc' pid' = ret gv /\
  lookupAL (GVsT DGVs) lc' (PI_id pinfo) = ret gvsa.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in H2.
  simpl in H2.
  inv_mbind'.
  assert (v = value_id lid) as EQ'.
    eapply WF_PhiInfo__getValueViaLabelFromValuels in HeqR2; eauto.
    eapply WF_PhiInfo_br_succs_preds in Hsucc; eauto.

  subst v.
  simpl in HeqR0. rewrite Hlk2 in HeqR0. inv HeqR0.

  simpl.
  split.
    rewrite lookupAL_updateAddAL_eq; auto.

    assert (PI_id pinfo <> pid') as Hneq_pid.
      clear - Hwfpi HeqR1 Huniq.
      apply WF_PhiInfo_fresh in HeqR1; auto.
    rewrite <- lookupAL_updateAddAL_neq; auto.

    eapply WF_PhiInfo__getIncomingValuesForBlockFromPHINodes in Hlkp1; eauto.
Qed.

Definition not_temporaries (i0 : id) (newids : ATree.t (id * id * id)) : Prop :=
forall l0,
  match ATree.get l0 newids with
  | Some (lid, pid, sid) => i0 <> lid /\ i0 <> pid /\ i0 <> sid
  | None => True
  end.

Lemma is_temporary_dec : forall id0 newids,
  is_temporary id0 newids \/ not_temporaries id0 newids.
Proof.
  intros.
  assert (not_temporaries id0 newids \/ ~ not_temporaries id0 newids) as J.
    tauto.
  destruct J; auto.
  left.
  unfold is_temporary, not_temporaries in *.
  apply Coq.Logic.Classical_Pred_Type.not_all_ex_not in H.
  destruct H as [n H].
  exists n.
  destruct (newids ! n) as [[[]]|]; auto.
    destruct (id0 == i0); subst; simpl.
      left. reflexivity.
    destruct (id0 == i1); subst; simpl.
      right. left. reflexivity.
    destruct (id0 == i2); subst; simpl.
      right. right. reflexivity.
    contradict H; auto.
Qed.

Lemma temporaries_exclusive: forall i0 newids0
  (H1: not_temporaries i0 newids0) (H0: is_temporary i0 newids0), False.
Proof.
  intros.
  unfold not_temporaries in H1.
  unfold is_temporary in H0.
  destruct H0 as [l0 H0].
  assert (J:=@H1 l0).
  destruct newids0 ! l0 as [[[]]|].
    destruct J as [J1 [J2 J3]].
    destruct H0 as [H0 | [H0 | H0]].
      contradict J1; auto.
      destruct (i0 == i1); auto.
        simpl in H0. congruence.
      contradict J2; auto.
      destruct (i0 == i2); auto.
        simpl in H0. congruence.
      contradict J3; auto.
      destruct (i0 == i3); auto.
        simpl in H0. congruence.
    inv H0.
Qed.

Definition value_has_no_tmps (pinfo:PhiInfo) (v:value) : Prop :=
match v with
| value_const _ => True
| value_id vid => not_temporaries vid (PI_newids pinfo)
end.

Lemma params_has_no_tmps__intro_aux: forall pinfo lp (init:Prop),
  init ->
  (forall v, valueInParams v lp -> value_has_no_tmps pinfo v) ->
  fold_left
      (fun (acc : Prop) (p : typ * attributes * value) =>
       let '(_, v) := p in value_has_no_tmps pinfo v /\ acc) lp init.
Proof.
  induction lp as [|[]]; simpl; intros; auto.
    apply IHlp.
    split; auto.
      apply H0.
      unfold valueInParams. simpl.
      destruct (split lp). simpl. auto.

      intros.
      apply H0.
      unfold valueInParams in *. simpl in *.
      destruct (split lp). simpl. auto.
Qed.

Lemma params_has_no_tmps__intro: forall pinfo lp,
  (forall v, valueInParams v lp -> value_has_no_tmps pinfo v) ->
  fold_left
      (fun (acc : Prop) (p : typ * attributes * value) =>
       let '(_, v) := p in value_has_no_tmps pinfo v /\ acc) lp True.
Proof.
  intros.
  apply params_has_no_tmps__intro_aux; auto.
Qed.

(* from sb_ds_trans *)
Definition getValueIDs (v:value) : atoms :=
match v with
| value_id id => {{id}}
| value_const _ => {}
end.

(* from sb_ds_trans *)
Definition id_fresh_in_value v1 i2 : Prop :=
match v1 with
| value_id i1 => i1 <> i2
| _ => True
end.

(* from sb_ds_trans *)
Fixpoint ids2atoms (ids0:ids) : atoms :=
match ids0 with
| nil => {}
| id0::ids0' => {{id0}} `union` ids2atoms ids0'
end.

(* from sb_ds_trans_lib *)
Lemma getPhiNodeID_in_getFdefLocs : forall f1 l0 ps p cs tmn,
  blockInFdefB (block_intro l0 ps cs tmn) f1 = true ->
  In p ps ->
  In (getPhiNodeID p) (getFdefLocs f1).
Proof.
  intros.
  destruct f1 as [f ?]. destruct f. simpl.
  apply in_or_app. right.
  eapply in_getBlockLocs__in_getBlocksLocs in H; eauto.
  simpl.
  apply in_or_app. left.
  apply in_getPhiNodeID__in_getPhiNodesIDs; auto.
Qed.

(* from sb_ds_trans_lib *)
Lemma in_singleton : forall a d, singleton a [<=] d <-> a `in` d.
Proof.
  intros.
  unfold AtomSetImpl.Subset.
  split; intros; eauto.
    assert (a0 = a) as EQ. fsetdec.
    subst. auto.
Qed.

(* from sb_ds_trans_lib *)
Lemma ids2atoms__in : forall a d, In a d <-> singleton a [<=] (ids2atoms d).
Proof.
  induction d; simpl.
    split; intros.
      inv H.

      apply in_singleton in H.
      fsetdec.
    destruct IHd as [J1 J2].
    split; intros.
      destruct H as [H | H]; subst.
        fsetdec.
        apply J1 in H. fsetdec.
        assert (a = a0 \/ a `in` (ids2atoms d)) as J.
          fsetdec.
        destruct J as [J | J]; subst; auto.
          apply in_singleton in J. eauto.
Qed.

(* from sb_ds_trans_lib *)
Lemma ids2atoms__notin : forall a d, ~ In a d <-> a `notin` (ids2atoms d).
Proof.
  split; intros.
    destruct (AtomSetProperties.In_dec a (ids2atoms d)); auto.
      apply in_singleton in i0.
      apply ids2atoms__in in i0. congruence.
    destruct (in_dec eq_atom_dec a d); auto.
      apply ids2atoms__in in i0.
      apply in_singleton in i0. congruence.
Qed.

(* from sb_ds_trans_lib *)
Lemma wf_value_id__in_getFdefLocs : forall S m f v t,
  wf_value S m f v t -> getValueIDs v[<=]ids2atoms (getFdefLocs f).
Proof.
  intros.
  inv H; simpl.
    clear. fsetdec.

    destruct f as [f b]. destruct f as [? ? ? a ?]. simpl in *.
    apply ids2atoms__in.
    destruct_match.
      symmetry in HeqR.
      destruct (In_dec eq_atom_dec id5 (getArgsIDs a)) as [Hin | Hnotin].
        apply in_or_app. auto.

        apply NotInArgsIDs_lookupTypViaIDFromArgs in Hnotin.
        congruence.
      destruct (In_dec eq_atom_dec id5 (getBlocksLocs b)) as [Hin | Hnotin].
        apply in_or_app. auto.

        apply notInBlocks__lookupTypViaIDFromBlocks in Hnotin.
        congruence.
Qed.

Lemma wf_value_id__in_getFdefLocs' : forall S m f v t,
  wf_value S m f v t ->
  match v with
  | value_id vid => In vid (getFdefLocs f)
  | _ => True
  end.
Proof.
  intros.
  destruct v; auto.
  apply wf_value_id__in_getFdefLocs in H.
  simpl in H.
  apply ids2atoms__in in H; auto.
Qed.

Lemma original_values_arent_tmps: forall S m pinfo F B v instr
  (HwfF: wf_fdef S m F)
  (Hwfpi: WF_PhiInfo pinfo)
  (HBinF : insnInFdefBlockB instr F B = true)
  (HvInOps : valueInInsnOperands v instr),
  if fdef_dec (PI_f pinfo) F then value_has_no_tmps pinfo v else True.
Proof.
  intros.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  destruct v as [i0|]; simpl; auto.
  intros l0.
  remember ((PI_newids pinfo) ! l0) as R.
  destruct R as [[[]]|]; auto.
  eapply wf_fdef__wf_insn in HBinF; eauto.
  eapply wf_insn__wf_value in HvInOps; eauto.
  destruct HvInOps as [t HvInOps].
  apply wf_value_id__in_getFdefLocs' in HvInOps.
  destruct (i0 == i1); subst.
    assert (is_temporary i1 (PI_newids pinfo)) as Histmp.
      exists l0. rewrite <- HeqR. auto.
      destruct (i1 == i1); simpl; try congruence.
      left. reflexivity.
   apply gen_fresh_ids__spec in Histmp; auto.
  split; auto.
  destruct (i0 == i2); subst.
    assert (is_temporary i2 (PI_newids pinfo)) as Histmp.
      exists l0. rewrite <- HeqR. auto.
      destruct (i2 == i2); simpl; try congruence.
      right. left. reflexivity.
   apply gen_fresh_ids__spec in Histmp; auto.
  split; auto.
  destruct (i0 == i3); subst; auto.
    assert (is_temporary i3 (PI_newids pinfo)) as Histmp.
      exists l0. rewrite <- HeqR. auto.
      destruct (i3 == i3); simpl; try congruence.
      right. right. reflexivity.
   apply gen_fresh_ids__spec in Histmp; auto.
Qed.

Lemma original_values_in_cmd_arent_tmps: forall (pinfo : PhiInfo)
  (Hwfpi : WF_PhiInfo pinfo) (l1 : l) (ps1 : phinodes) (cs11 cs1' : list cmd)
  v c (Hin : valueInCmdOperands v c) tmn S m F1
  (HwfF: wf_fdef S m F1)
  (HBinF : blockInFdefB
            (block_intro l1 ps1 (cs11 ++ c :: cs1')
               tmn) F1 = true),
   if fdef_dec (PI_f pinfo) F1
   then value_has_no_tmps pinfo v
   else True.
Proof.
  intros.
  eapply original_values_arent_tmps with
    (B:=block_intro l1 ps1 (cs11 ++ c :: cs1') tmn) (instr:=insn_cmd c);
    simpl; eauto.
  apply andb_true_iff.
  split; auto.
    apply In_InCmdsB. apply in_middle.
Qed.

Lemma original_ids_in_phi_arent_temporaries: forall pinfo l1 ps1 cs1 tmn l3 vid
  vls pid typ S m (HwfF: wf_fdef S m (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn) (PI_f pinfo) = true ->
  In (insn_phi pid typ vls) ps1 ->
  Some (value_id vid) = getValueViaLabelFromValuels vls l3 ->
  not_temporaries vid (PI_newids pinfo).
Proof.
  intros.
  assert (insnInFdefBlockB
           (insn_phinode (insn_phi pid typ0 vls)) (PI_f pinfo)
           (block_intro l1 ps1 cs1 tmn)) as Hin.
    apply andb_true_iff.
    split; auto.
      simpl.
      apply In_InPhiNodesB. auto.
  eapply original_values_arent_tmps with (v:=value_id vid) in Hin; simpl; eauto.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    simpl in Hin. auto.

    symmetry in H2.
    eapply getValueViaLabelFromValuels__In_list_prj1; eauto.
Qed.

Lemma original_indxs_arent_tmps: forall pinfo F1 l1 ps1 cs11 id0 inbounds0 t v
  idxs cs1' tmn (Hwfpi: WF_PhiInfo pinfo) S m (HwfF: wf_fdef S m F1) t'
  (HBinF : blockInFdefB
            (block_intro l1 ps1
               (cs11 ++ insn_gep id0 inbounds0 t v idxs t':: cs1') tmn) F1 =
            true),
  if fdef_dec (PI_f pinfo) F1 then
    forall nth sz0 v0,
      nth_error idxs nth = Some (sz0, v0) ->
      value_has_no_tmps pinfo v0
  else True.
Proof.
  intros.
  destruct (fdef_dec (PI_f pinfo) F1); subst; auto.
  intros.
  eapply original_values_in_cmd_arent_tmps with (v:=v0) in HBinF; eauto.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    simpl.
    right. apply nth_list_sz_value__valueInListValue in H; auto.
Qed.

Lemma WF_PhiInfo_spec12: forall pinfo l1 ps1 cs1 rid noret0 ca rt1 va1 fv lp cs2 tmn
  F1 S m (HwfF: wf_fdef S m F1),
  WF_PhiInfo pinfo ->
  blockInFdefB
    (block_intro l1 ps1 (cs1 ++ insn_call rid noret0 ca rt1 va1 fv lp :: cs2) tmn)
    F1 = true ->
  if fdef_dec (PI_f pinfo) F1 then
    fold_left
      (fun (acc : Prop) (p : typ * attributes * value) =>
       let '(_, v) := p in value_has_no_tmps pinfo v /\ acc) lp True
  else True.
Proof.
  intros.
  destruct (fdef_dec (PI_f pinfo) F1); subst; auto.
  apply params_has_no_tmps__intro.
  intros.
  eapply original_values_in_cmd_arent_tmps with (v:=v) in H0; eauto.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    simpl. auto.
Qed.

(* copied from SB *)
Lemma cmds_at_block_tail_next : forall B c cs tmn2,
  (exists l1, exists ps1, exists cs11, B =
    block_intro l1 ps1 (cs11 ++ c :: cs) tmn2) ->
  exists l1, exists ps1, exists cs11, B = block_intro l1 ps1 (cs11 ++ cs) tmn2.
Proof.
  intros.
  destruct H as [l1 [ps1 [cs11 H]]]; subst.
  exists l1. exists ps1. exists (cs11 ++ [c]). simpl_env. auto.
Qed.

Lemma phinodes_placement_blocks__disjoint_tmps: forall l0 i1 i2 i3 i0
  pid t al nids succs preds
  (Hdisj: forall l1 l2 a1 b1 c1 a2 b2 c2,
    l1 <> l2 ->
    ret (a1, b1, c1) = nids ! l1 ->
    ret (a2, b2, c2) = nids ! l2 ->
    a1 <> a2 /\ a1 <> b2 /\ a1 <> c2 /\
    b1 <> a2 /\ b1 <> b2 /\ b1 <> c2 /\
    c1 <> a2 /\ c1 <> b2 /\ c1 <> c2)
  (J1: ret (i1, i2, i3) = nids ! l0)
  (J2: i0 = i1 \/ i0 = i2 \/ i0 = i3) bs,
  ~ In l0 (getBlocksLabels bs) ->
  In i0 (getBlocksLocs
           (phinodes_placement_blocks pid t al nids succs preds bs)) ->
  In i0 (getBlocksLocs bs).
Proof.
  induction bs as [|a bs]; simpl; intros; auto.
    destruct a as [l1 ? ? ?]. simpl in *.
    assert (l1 <> l0 /\ ~ In l0 (getBlocksLabels bs)) as J.
      split.
        intro J. subst. auto.
        intro J. contradict H; auto.
    destruct J as [J3 J4].
    apply in_app_or in H0.
    destruct H0 as [H0 | H0].
    remember (nids ! l1) as R1.
    remember (preds ! l1) as R2.
    remember (succs ! l1) as R3.
    simpl_env.
    destruct R1 as [[[]]|]; auto.
      eapply Hdisj in J1; eauto.
      clear Hdisj.
      destruct R2 as [[]|].
        destruct R3 as [[]|]; simpl in H0; simpl_env in H0.
          solve_in_prefix.
          apply in_or_app. auto.

          repeat rewrite getCmdsLocs_app in H0; simpl in H0; simpl_env in H0.
          solve_in_prefix.
          solve_in_head.
          apply in_or_app. simpl.
          destruct H0 as [H0 | H0]; auto.

          solve_in_prefix.
          apply in_or_app. auto.

        destruct R3 as [[]|]; simpl in H0; simpl_env in H0.
          solve_in_head.
          solve_in_prefix.
          solve_in_head.
          solve_in_prefix.
          apply in_or_app. auto.

          repeat rewrite getCmdsLocs_app in H0; simpl in H0; simpl_env in H0.
          solve_in_head.
          solve_in_prefix.
          solve_in_head.
          solve_in_prefix.
          solve_in_head.
          apply in_or_app. auto.

          solve_in_head.
          solve_in_prefix.
          solve_in_head.
          solve_in_prefix.
          apply in_or_app. auto.

        destruct R3 as [[]|]; simpl in H0; simpl_env in H0.
          solve_in_prefix.
          apply in_or_app. auto.

          repeat rewrite getCmdsLocs_app in H0; simpl in H0; simpl_env in H0.
          solve_in_prefix.
          solve_in_head.
          apply in_or_app. simpl.
          destruct H0 as [H0 | H0]; auto.

          solve_in_prefix.
          apply in_or_app. auto.

      simpl in H0. simpl_env in H0.
      solve_in_prefix.
      apply in_or_app. auto.

    apply IHbs in H0; auto.
    apply in_or_app. auto.
Qed.

Lemma WF_PhiInfo_spec10: forall pinfo l1 ps1 cs1 c cs2 tmn
  (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs2) tmn) (PI_f pinfo) = true
    ->
  match c with
  | insn_alloca _ _ _ _ => False
  | _ => True
  end ->
  PI_id pinfo <> getCmdLoc c.
Proof.
  intros.
  apply WF_PhiInfo_spec1 in H; auto.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H0; eauto using in_middle.
  destruct (PI_id pinfo == getCmdLoc c); subst; auto.
  rewrite e in H.
  rewrite H in H0. clear e.
  inversion H0. rewrite <- H3 in H1. inv H1.
Qed.

Lemma WF_PhiInfo_spec11: forall pinfo l1 ps1 cs1 c cs2 tmn,
  WF_PhiInfo pinfo ->
  blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs2) tmn) (PI_f pinfo) = true
    ->
  not_temporaries (getCmdLoc c) (PI_newids pinfo).
Proof.
  intros.
  eapply getCmdLoc_in_getFdefLocs in H0; eauto.
  destruct (is_temporary_dec (getCmdLoc c) (PI_newids pinfo)); auto.
  destruct H as [J1 J2].
  apply gen_fresh_ids__spec in H1; auto.
  contradict H0; auto.
Qed.

Lemma WF_PhiInfo_spec18: forall pinfo (Hwfpi: WF_PhiInfo pinfo) 
  (Huniq: uniqFdef (PI_f pinfo)),
  not_temporaries (PI_id pinfo) (PI_newids pinfo).
Proof.
  intros.
  apply WF_PhiInfo_spec1 in Huniq; auto.
  apply lookupInsnViaIDFromFdef__insnInFdefBlockB in Huniq.
  destruct Huniq as [b Huniq].
  apply destruct_insnInFdefBlockB in Huniq.  
  destruct b as [l0 ps0 cs0 tmn0].
  simpl in Huniq. destruct Huniq as [HcInB HbInF]. 
  apply InCmdsB_in in HcInB.
  apply in_split in HcInB.
  destruct HcInB as [cs1 [cs2 HcInB]]; subst.
  eapply WF_PhiInfo_spec11 in HbInF; eauto.
Qed.

Lemma find_promotable_alloca__WF_PhiInfo: forall rd f l0 ps0 cs0 tmn0
  (Hreach : ret rd = reachablity_analysis f)
  (Hentry : ret block_intro l0 ps0 cs0 tmn0 = getEntryBlock f)
  (pid : id) (ty : typ) num (al : align) dones
  (Hfind : find_promotable_alloca f cs0 dones = ret (pid, ty, num, al)),
  WF_PhiInfo (mkPhiInfo f rd pid ty num al).
Proof.
  intros.
  split; simpl; auto.
    unfold promotable_alloca.
    fill_ctxhole. 
    eapply find_promotable_alloca_spec; eauto.
Qed.

Definition update_pinfo (pinfo:PhiInfo) (f:fdef) : PhiInfo :=
(mkPhiInfo f
  (PI_rd pinfo) (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo) (PI_align pinfo)).

Lemma update_pinfo_eq: forall pinfo, update_pinfo pinfo (PI_f pinfo) = pinfo.
Proof.
  intros. unfold update_pinfo. destruct pinfo. simpl in *. auto.
Qed.

Lemma store_notin_cmd__wf_use_at_head: forall pinfo sid t v1 v2 align0,
  false = store_in_cmd (PI_id pinfo) (insn_store sid t v1 v2 align0) ->
  wf_use_at_head pinfo v2.
Proof.
  intros. simpl in H. unfold wf_use_at_head. auto.
Qed.

Lemma WF_PhiInfo_spec6': forall (pinfo : PhiInfo) (ps1 : phinodes) (l1 : l)
  (cs1 : cmds) (tmn1 : terminator) (H : WF_PhiInfo pinfo)
  (HBinF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) (PI_f pinfo) = true)
  (H0 : uniqFdef (PI_f pinfo)),
  ~ In (PI_id pinfo) (getPhiNodesIDs ps1).
Proof.
  intros.
  apply blockInFdefB_lookupBlockViaLabelFromFdef in HBinF; auto.
  eapply WF_PhiInfo_spec6; eauto.
Qed.

Lemma WF_PhiInfo_spec6'': forall (pinfo : PhiInfo) (ps1 : phinodes) (l1 : l)
  (cs1 : cmds) (tmn1 : terminator) (H : WF_PhiInfo pinfo) F
  (HBinF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) F = true)
  (H0 : uniqFdef F),
  PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps1).
Proof.
  intros.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  right.
  eapply WF_PhiInfo_spec6'; eauto.
Qed.

Ltac WF_PhiInfo_spec6_tac :=
try solve [eapply WF_PhiInfo_spec6; eauto | 
           eapply WF_PhiInfo_spec6'; eauto | 
           eapply WF_PhiInfo_spec6''; eauto].

Lemma switchToNewBasicBlock_doesnt_change_pid: forall pinfo l'0 ps'0 cs' tmn'0 B 
  gl2 lc2 lc'0 td (H : WF_PhiInfo pinfo)
  (H0 : uniqFdef (PI_f pinfo)),
  blockInFdefB (block_intro l'0 ps'0 cs' tmn'0) (PI_f pinfo) = true ->
  Opsem.switchToNewBasicBlock td
         (block_intro l'0 ps'0 cs' tmn'0) B gl2 lc2 = 
       ret lc'0 ->
  lookupAL (GVsT DGVs) lc2 (PI_id pinfo) =
    lookupAL (GVsT DGVs) lc'0 (PI_id pinfo).
Proof.
  unfold Opsem.switchToNewBasicBlock.
  intros.
  inv_mbind.
  erewrite <- OpsemProps.updateValuesForNewBlock_spec7'; eauto.
  eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec8; eauto.
  simpl.
  WF_PhiInfo_spec6_tac.
Qed.

Lemma WF_PhiInfo_spec20: forall pinfo (Hwfpi: WF_PhiInfo pinfo)
  (Huniq: uniqFdef (PI_f pinfo)),
  lookupTypViaIDFromFdef (PI_f pinfo) (PI_id pinfo) = 
    Some (typ_pointer (PI_typ pinfo)).
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct Hwfpi as [J1 J2].
  symmetry in HeqR.
  apply entryBlockInFdef in HeqR.
  eapply uniqF__lookupTypViaIDFromFdef; eauto; simpl; auto.
Qed.

Lemma WF_PhiInfo_spec14: forall pinfo l1 ps1 cs11 t v align0 cs tmn2
  (Hwfpi: WF_PhiInfo pinfo) (Huniq: uniqFdef (PI_f pinfo))
  (HBinF: blockInFdefB (block_intro l1 ps1
                 (cs11 ++ insn_alloca (PI_id pinfo) t v align0 :: cs) tmn2)
               (PI_f pinfo) = true),
  getEntryBlock (PI_f pinfo) =
    ret block_intro l1 ps1
         (cs11 ++ insn_alloca (PI_id pinfo) t v align0 :: cs) tmn2.
Proof.
  intros.
  destruct Hwfpi as [Hwfpi _].
  unfold promotable_alloca in Hwfpi.
  inv_mbind. symmetry_ctx.
  destruct b as [l0 ps0 cs0 tmn0].
  f_equal.
  eapply block_eq1 with (id0:=PI_id pinfo); eauto.
    apply entryBlockInFdef in HeqR.
    eapply inGetBlockIDs__lookupBlockViaIDFromFdef; eauto.
    destruct Hwfpi as [J _].
    eapply getCmdID_in_getBlocksIDs; eauto. 
      simpl; auto.

    eapply getCmdID_in_getBlocksIDs; eauto using in_middle.
      simpl; auto.
Qed.

Lemma WF_PhiInfo_spec16: forall pinfo S los nts Ps,
  WF_PhiInfo pinfo ->
  wf_fdef S (module_intro los nts Ps) (PI_f pinfo) ->
  exists sz, exists al,
    getTypeSizeInBits_and_Alignment (los,nts) true (PI_typ pinfo) = 
      Some (sz, al) /\ 
    (sz > 0)%nat /\ (al > 0)%nat.
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [J1 J2].
  symmetry in HeqR.
  apply entryBlockInFdef in HeqR.
  eapply wf_fdef__wf_cmd in HeqR; eauto.
  inv HeqR.
  eapply wf_typ__getTypeSizeInBits_and_Alignment in H12; eauto.
Qed.

Ltac WF_PhiInfo_spec10_tac :=
repeat match goal with
| HBinF2 : blockInFdefB ?B' (PI_f ?pinfo) = true,
  Heq3' : exists l1 : l,
            exists ps1 : phinodes,
              exists cs11 : list cmd,
                ?B' =
                block_intro l1 ps1
                  (cs11 ++ _ :: ?cs') ?tmn3 |- _ =>
  destruct Heq3' as [l2 [ps2 [cs21 Heq3']]]; subst;
  eapply WF_PhiInfo_spec10 in HBinF2; eauto 2 using wf_system__uniqFdef
| HBinF2 : blockInFdefB ?B' ?F = true,
  Heq3' : exists l1 : l,
            exists ps1 : phinodes,
              exists cs11 : list cmd,
                ?B' =
                block_intro l1 ps1
                  (cs11 ++ _ :: ?cs') ?tmn3 |- 
  ?A <> ?F \/ _ => destruct (fdef_dec A F); subst; auto; right
end.

Ltac solve_non_pid_updateAddAL :=
match goal with
| HBinF2 : blockInFdefB ?B' ?F' = true,
  Heq3' : exists l1 : l,
            exists ps1 : phinodes,
              exists cs11 : list cmd,
                ?B' =
                block_intro l1 ps1
                  (cs11 ++ _ :: ?cs') ?tmn3 |-
  PI_f _ = ?F' ->
  lookupAL _ ?lc ?id1 =
  lookupAL _ (updateAddAL _ ?lc _ _ ) ?id1=>
  intro; subst;
  rewrite <- lookupAL_updateAddAL_neq; auto;
  WF_PhiInfo_spec10_tac
end.

Lemma WF_PhiInfo_spec19: forall B pinfo (Huniq: uniqFdef (PI_f pinfo))
  (Hwfpi: WF_PhiInfo pinfo)
  (HBinF: blockInFdefB B (PI_f pinfo))
  (Hin: In (PI_id pinfo) (getBlockLocs B)),
  getEntryBlock (PI_f pinfo) = Some B.
Proof.
  intros.
  simpl_WF_PhiInfo.
  f_equal.
  eapply block_eq2; eauto 2.
    symmetry_ctx.
    solve_blockInFdefB.

    destruct Hwfpi. simpl in *.
    apply getCmdLoc_in_getCmdsLocs in H. simpl in H.
    xsolve_in_list.
Qed.

Lemma WF_PhiInfo_spec1': forall pinfo l1 ps1 cs11 c1 cs1 tmn2,
  WF_PhiInfo pinfo ->
  uniqFdef (PI_f pinfo) ->
  blockInFdefB (block_intro l1 ps1 (cs11 ++ c1 :: cs1) tmn2) (PI_f pinfo) 
    = true ->
  PI_id pinfo = getCmdLoc c1 ->
  c1 = insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo)
         (PI_align pinfo).
Proof.
  intros.
  assert (In (PI_id pinfo) 
    (getBlockLocs (block_intro l1 ps1 (cs11 ++ c1 :: cs1) tmn2))) as Hin.
    simpl. rewrite H2. xsolve_in_list.
  eapply WF_PhiInfo_spec19 in Hin; eauto.
  simpl_WF_PhiInfo. inv Hin.
  destruct H.
  eapply NoDup_getCmdsLocs_prop; eauto using in_middle.
    solve_NoDup.
Qed.

Definition args_dont_use_pid pinfo F (la:list (typ * attributes * id)) :=
  conditional_used_in_args (PI_f pinfo) F (PI_id pinfo) la.

Lemma WF_PhiInfo__args_dont_use_pid: forall pinfo F la0
  (Huniq: uniqFdef F) (Hneq: la0 = getArgsOfFdef F) (Hwfpi: WF_PhiInfo pinfo),
  args_dont_use_pid pinfo F la0.
Proof.
  intros.
  unfold args_dont_use_pid.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  right.
  apply WF_PhiInfo_spec1 in Hwfpi; auto.
  destruct (PI_f pinfo) as [[]]. simpl. intros.
  eapply IngetArgsIDs__lookupCmdViaIDFromFdef with (id0:=i0) in Huniq; eauto.
    congruence.
    eapply In_getArgsIDs_spec; eauto.
Qed.

Lemma WF_PhiInfo__pid_isnt_in_init: forall pinfo (Hwfpi: WF_PhiInfo pinfo)
  (Huniq: uniqFdef (PI_f pinfo)) lc VarArgs TD la
  (Heq: la = getArgsOfFdef (PI_f pinfo))
  (Hinit: @Opsem.initLocals DGVs TD la VarArgs = ret lc),
  lookupAL _ lc (PI_id pinfo) = None.
Proof.
  intros.
  remember (lookupAL (GVsT DGVs) lc (PI_id pinfo)) as R.
  destruct R; auto.
  eapply OpsemProps.In_initLocals__In_getArgsIDs with (id1:=PI_id pinfo) in Hinit; 
    eauto.
  apply WF_PhiInfo_spec1 in Hwfpi; auto.
  destruct (PI_f pinfo) as [[]]. subst.
  eapply IngetArgsIDs__lookupCmdViaIDFromFdef in Huniq; eauto.
  congruence.
Qed.

Lemma WF_PhiInfo_spec21: forall pinfo (Hwfpi : WF_PhiInfo pinfo)
  (los : layouts) (nts : namedts) (Ps : products) S 
  (HUniq: uniqFdef (PI_f pinfo))
  (HwfF : wf_fdef S (module_intro los nts Ps) (PI_f pinfo)),
  wf_typ S (los, nts) (PI_typ pinfo).
Proof.
  intros.
  apply WF_PhiInfo_spec1 in Hwfpi; auto.
  apply lookupInsnViaIDFromFdef__insnInFdefBlockB in Hwfpi.
  destruct Hwfpi as [b1 Hwfpi].
  apply destruct_insnInFdefBlockB in Hwfpi.
  destruct Hwfpi as [J1 J2]. 
  destruct b1. simpl in *.
  apply InCmdsB_in in J1.
  eapply wf_fdef__wf_cmd in J2; eauto.
  inv J2. auto.
Qed.

Lemma WF_PhiInfo_spec22: forall pinfo (Hwfpi : WF_PhiInfo pinfo)
  (HUniq: uniqFdef (PI_f pinfo)),
  exists l0, exists ps0, exists cs1, exists cs2, exists tmn0,
    getEntryBlock (PI_f pinfo) = 
      Some (block_intro l0 ps0 
        (cs1 ++ insn_alloca (PI_id pinfo) (PI_typ pinfo) 
           (PI_num pinfo) (PI_align pinfo):: cs2) tmn0).
Proof.
  intros.
  simpl_WF_PhiInfo.
  exists l5. exists phinodes5.
  destruct Hwfpi as [J1 J2].
  apply in_split in J1.
  destruct J1 as [cs1 [cs2 J1]]; subst.
  exists cs1. exists cs2. exists terminator5.
  auto.
Qed.

Lemma WF_PhiInfo_spec23: forall pinfo s m (Hwfpi : WF_PhiInfo pinfo)
  (HUniq: uniqFdef (PI_f pinfo)) (Hwf: wf_fdef s m (PI_f pinfo)) l0 ps0 tmn0
  t id0 al cs1 cs2
  (HBinF: blockInFdefB 
    (block_intro l0 ps0 
      (cs1 ++ insn_load id0 t (value_id (PI_id pinfo)) al :: cs2) tmn0) 
    (PI_f pinfo)),
  t = PI_typ pinfo.
Proof.
  intros.
  eapply wf_fdef__wf_cmd in HBinF; eauto using in_middle.
  inv HBinF. inv H6.
  eapply WF_PhiInfo_spec20 in Hwfpi; eauto.
  uniq_result. auto.
Qed.

Lemma WF_PhiInfo_spec24: forall pinfo s m (Hwfpi : WF_PhiInfo pinfo)
  (HUniq: uniqFdef (PI_f pinfo)) (Hwf: wf_fdef s m (PI_f pinfo)) l0 ps0 tmn0
  t id0 al cs1 cs2 v0
  (HBinF: blockInFdefB 
    (block_intro l0 ps0 
      (cs1 ++ insn_store id0 t v0 (value_id (PI_id pinfo)) al :: cs2) tmn0) 
    (PI_f pinfo)),
  t = PI_typ pinfo.
Proof.
  intros.
  eapply wf_fdef__wf_cmd in HBinF; eauto using in_middle.
  inv HBinF. inv H9.
  eapply WF_PhiInfo_spec20 in Hwfpi; eauto.
  uniq_result. auto.
Qed.

Lemma WF_PhiInfo__lookupBlockViaIDFromFdef: forall pinfo 
  (Hwfpi : WF_PhiInfo pinfo) (Huniq: uniqFdef (PI_f pinfo)),
  exists b, 
    getEntryBlock (PI_f pinfo) = Some b /\
    lookupBlockViaIDFromFdef (PI_f pinfo) (PI_id pinfo) = Some b.
Proof.
  intros.
  subst.
  apply WF_PhiInfo_spec22 in Hwfpi; auto.
  destruct Hwfpi as [l0 [ps0 [cs1 [cs2 [tmn0 Hentry]]]]].
  match goal with
  | Hentry: getEntryBlock _ = Some ?b |- _ => exists b; split; auto
  end.
  eapply inGetBlockIDs__lookupBlockViaIDFromFdef; eauto 1.
    simpl. rewrite getCmdsIDs_app. simpl. xsolve_in_list.
    solve_blockInFdefB.
Qed.

(* entry_cmds_simulation in phiplacement_bsim_defs.v should 
   also use the lemma *)
Lemma PI_preds_of_entry_cannot_be_nonempty: forall s m pinfo
  (HwfF: wf_fdef s m (PI_f pinfo)) b
  (Hentry: getEntryBlock (PI_f pinfo) = Some b),
  forall (pd : l) (pds : list l), 
    (PI_preds pinfo) ! (getBlockLabel b) <> ret (pd :: pds).
Proof.
  intros.
  unfold PI_preds.
  intros. intro J.
  assert (In pd (make_predecessors (PI_succs pinfo))!!!(getBlockLabel b)) as G.
    unfold successors_list. unfold l in J. rewrite J. simpl. auto.
  apply make_predecessors_correct' in G.
  unfold PI_succs in G.
  apply successors__blockInFdefB in G.
  destruct G as [ps1 [cs1' [tmn1 [G1 G2]]]].
  destruct (PI_f pinfo) as [fh bs].
  simpl in G1.
  destruct b.
  eapply getEntryBlock_inv in G1; eauto.
Qed.

Lemma gen_fresh_ids__spec2_aux': forall l1 rds newids nids exids,
  fst (fold_left gen_fresh_ids_fun rds (nids, exids)) = newids ->
  newids ! l1 <> None ->
  In l1 rds \/ nids ! l1 <> None.
Proof.
  induction rds; simpl; intros.
    subst. auto.

    remember (atom_fresh_for_list exids) as R1.
    destruct R1 as [lid' Jlid'].
    remember (atom_fresh_for_list (lid'::exids)) as R2.
    destruct R2 as [pid' Jpid'].
    remember (atom_fresh_for_list (pid'::lid'::exids)) as R3.
    destruct R3 as [sid' Jsid'].
    apply IHrds in H; auto.
    destruct H as [H | H]; auto.
    destruct (a == l1); auto.
    rewrite ATree.gso in H; auto.
Qed.

Lemma gen_fresh_ids__spec2': forall l1 newids rds exids,
  fst (gen_fresh_ids rds exids) = newids ->
  newids ! l1 <> None ->
  In l1 rds.
Proof.
  unfold gen_fresh_ids.
  fold gen_fresh_ids_fun.
  intros.
  eapply gen_fresh_ids__spec2_aux' in H; eauto.
  destruct H as [H | H]; auto.
  rewrite ATree.gempty in H. 
  contradict H; auto.
Qed.

Lemma PI_newids_are_in_PI_rd: forall pinfo l1 
  (Hnempty: (PI_newids pinfo) ! l1 <> merror),
  In l1 (PI_rd pinfo).
Proof.
  intros.
  unfold PI_newids in *.
  eapply gen_fresh_ids__spec2'; eauto.
Qed.

Lemma PI_rd__lookupBlockViaLabelFromFdef: forall pinfo (Hwfpi: WF_PhiInfo pinfo) l0
  (Hin: In l0 (PI_rd pinfo)) (Huniq: uniqFdef (PI_f pinfo)),
  exists b1 : block,
    lookupBlockViaLabelFromFdef (PI_f pinfo) l0 = ret b1.
Proof.
  intros.
  destruct Hwfpi.
  apply reachablity_analysis__in_bound in H0.
  apply H0 in Hin.
  apply In_bound_fdef__blockInFdefB in Hin.
  destruct Hin as [ps [cs [tmn Hin]]].
  exists (block_intro l0 ps cs tmn).
  solve_lookupBlockViaLabelFromFdef.
Qed.

Lemma WF_PhiInfo_br_preds_succs: forall pinfo l0 l3 (Hwfpi : WF_PhiInfo pinfo)
  prds (Hin : In l3 prds) (Heq' : (PI_preds pinfo) ! l0 = ret prds),
  exists succs, (PI_succs pinfo) ! l3 = ret succs /\ In l0 succs.
Proof.
  unfold PI_preds. unfold PI_succs.
  intros.
  destruct Hwfpi as [J1 J2].
  assert (In l3 ((make_predecessors (successors (PI_f pinfo)))!!!l0)) as Hin'.
    unfold successors_list.
    unfold ls, l in *.
    rewrite Heq'. auto.
  apply make_predecessors_correct' in Hin'.
  unfold successors_list in Hin'.
  remember (@ATree.get (list atom) l3 (successors (PI_f pinfo))) as R.
  destruct R; tinv Hin'. eauto.
Qed.

Lemma PI_newids_arent_in_getFdefLocs: forall pinfo id5 lid pid sid l0
  (Hfresh : In id5 (getFdefLocs (PI_f pinfo)))
  (Hnids : ret (lid, pid, sid) = (PI_newids pinfo) ! l0)
  (Heq: id5 = lid \/ id5 = pid \/ id5 = sid),
  False.
Proof.
  intros.
  unfold PI_newids in Hnids.
  contradict Hfresh.
  apply gen_fresh_ids__spec with (rds:=PI_rd pinfo); auto.
  unfold is_temporary. 
  exists l0. rewrite <- Hnids. 
  destruct (id5 == lid); subst; simpl.
    left. congruence.
  destruct (id5 == pid); subst; simpl.
    right. left. congruence.
  destruct (id5 == sid); subst; simpl.
    right. right. congruence.
    tauto.
Qed.

Lemma load_is_promotable: forall id5 acc lid ty v al,
  is_promotable_cmd id5 acc (insn_load lid ty v al)  = acc.
Proof.
  intros.
  unfold is_promotable_cmd.
  destruct_if.
Qed.

Lemma find_promotable_alloca_weaken_head: forall f dones cs cs1
  (H: List.Forall isnt_alloca cs1),
  find_promotable_alloca f cs dones =
    find_promotable_alloca f (cs1++cs) dones.
Proof.
  induction 1; simpl; intros; auto.
    destruct x; tinv H; auto.
Qed.

Lemma nonalloca_cannot_find_promotable_alloca: forall f dones cs
  (H: List.Forall isnt_alloca cs),
  find_promotable_alloca f cs dones = None.
Proof.
  induction 1; simpl; intros; auto.
    destruct x; tinv H; auto.
Qed.

Lemma find_promotable_alloca_weaken_tail: forall f dones cs1
  (H: List.Forall isnt_alloca cs1) cs,
  find_promotable_alloca f cs dones =
    find_promotable_alloca f (cs++cs1) dones.
Proof.
  induction cs; simpl; intros.
    rewrite nonalloca_cannot_find_promotable_alloca; auto.

    rewrite IHcs; auto.
Qed.

(***************************************************************************)
(*           pid is not defined until the allocation in entry              *)

(* 
      ---------------------------------
      |               cs0             |
      ---------------------------------
      | csa  | csb  | [palloca] | cs3 |
      ---------------------------------
      |      cs1    |                 |
      ---------------------------------
      |      |         cs             |
      ---------------------------------        
*)
Definition before_palloca (pinfo:PhiInfo) (cs:cmds) : Prop :=
match getEntryBlock (PI_f pinfo) with
| Some (block_intro _ _ cs0 _) =>
  forall cs1 cs3,
  cs0 =
    cs1 ++
    insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo) (PI_align pinfo) ::
    cs3 ->
  (exists csa, exists csb,
    cs1 = csa ++ csb /\ 
    cs = csb ++ 
         insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo) 
           (PI_align pinfo) :: cs3)
| _ => True
end.

Lemma before_palloca_cons: forall pinfo c cs l0 ps0 cs0 tmn0,
  getEntryBlock (PI_f pinfo) =
    Some (block_intro l0 ps0 (cs0++c::cs) tmn0) ->
  before_palloca pinfo cs ->
  before_palloca pinfo (c::cs).
Proof.
  unfold before_palloca.
  intros. rewrite H in H0. rewrite H.
  intros cs1 cs3 Heq.
  assert (Heq':=Heq).
  apply_clear H0 in Heq.
  destruct Heq as [csa [csb [J1 J2]]]; subst.
  assert (cs0 ++ [c] = csa) as J.
    anti_simpl_env. auto.
  subst.
  exists cs0. exists (c::csb). simpl_env. split; auto.
Qed.

Definition wf_defs (pinfo:PhiInfo) (lc:@Opsem.GVsMap DGVs) : Prop :=
lookupAL _ lc (PI_id pinfo) = None.

Definition wf_ExecutionContext (pinfo:PhiInfo) (ec:Opsem.ExecutionContext) 
  : Prop :=
Opsem.CurFunction ec = PI_f pinfo ->
getEntryBlock (PI_f pinfo) = Some (Opsem.CurBB ec) ->
before_palloca pinfo (Opsem.CurCmds ec) ->
wf_defs pinfo (Opsem.Locals ec).

Fixpoint wf_ECStack (pinfo:PhiInfo) (ecs:Opsem.ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' => wf_ExecutionContext pinfo ec /\ wf_ECStack pinfo ecs'
end.

Definition wf_State (pinfo:PhiInfo) (S:Opsem.State) : Prop :=
wf_ECStack pinfo (Opsem.ECS S).

Lemma wf_defs_updateAddAL: forall pinfo lc' i1 gv1 (Hwfpi: WF_PhiInfo pinfo)
  (HwfDef: wf_defs pinfo lc') (Hneq: i1 <> PI_id pinfo),
  wf_defs pinfo (updateAddAL _ lc' i1 gv1).
Proof.
  intros. unfold wf_defs in *. intros.
  rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma preservation_return : forall pinfo (HwfPI : WF_PhiInfo pinfo)
  F B rid RetTy Result lc F' B' c' cs' tmn' lc' EC Mem als als' cfg
  EC1 EC2
  (EQ1:EC1 = {| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := nil;
                Opsem.Terminator := insn_return rid RetTy Result;
                Opsem.Locals := lc;
                Opsem.Allocas := als |})
  (EQ2:EC2 = {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := c' :: cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc';
                Opsem.Allocas := als' |})
  Mem' lc'' (H : Instruction.isCallInst c' = true)
  (H1 : Opsem.returnUpdateLocals
          (OpsemAux.CurTargetData cfg) c'
            Result lc lc' (OpsemAux.Globals cfg) = ret lc'')
  (Hwfcfg : OpsemPP.wf_Config cfg)  
  (Hwfpp : OpsemPP.wf_State cfg
           {| Opsem.ECS := EC1 :: EC2 :: EC;
              Opsem.Mem := Mem |})
  (HwfS1 : wf_State pinfo
            {| Opsem.ECS := EC1 :: EC2 :: EC;
               Opsem.Mem := Mem |}),
  wf_State pinfo
     {| Opsem.ECS :=
             {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc'';
                Opsem.Allocas := als' |} :: EC;
        Opsem.Mem := Mem' |}.
Proof.
  intros. subst. destruct cfg as [S [los nts] Ps gl fs].
  destruct Hwfcfg as [_ [_ [HwfSystem HmInS]]].
  destruct Hwfpp as 
    [_ [_ 
     [
       [
         [_ [HBinF1 [HFinPs1 [_ [_ [l2 [ps2 [cs2' Heq2]]]]]]]]
         _
       ]
       _
     ]
    ]]; subst.
  destruct HwfS1 as [Hinscope1 [Hinscope2 HwfECs]]. simpl.
  fold wf_ECStack in HwfECs. simpl in *.
  split; auto.
    SSCase "wf_EC".
    intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
    assert (before_palloca pinfo (c' :: cs')) as Hin.
      eapply before_palloca_cons; eauto.
    destruct_cmd c'; tinv H.
    unfold wf_ExecutionContext in *. simpl in Hinscope1, Hinscope2.
    unfold Opsem.returnUpdateLocals in H1.
    remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
    destruct R1; tinv H1.
    destruct n; inv H1.
      apply Hinscope2; auto.

      remember (lift_op1 DGVs (fit_gv (los, nts) t0) g t0) as R2.
      destruct R2; inv H2.
      apply wf_defs_updateAddAL; auto.
        eapply WF_PhiInfo_spec10 in HBinF1; eauto using wf_system__uniqFdef.
Qed.

Lemma preservation_return_void : forall pinfo
  (HwfPI : WF_PhiInfo pinfo)
  F B rid lc F' B' c' cs' tmn' lc' EC Mem als als' cfg EC1 EC2
  (EQ1:EC1 = {| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := nil;
                Opsem.Terminator := insn_return_void rid;
                Opsem.Locals := lc;
                Opsem.Allocas := als |})
  (EQ2:EC2 = {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := c' :: cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc';
                Opsem.Allocas := als' |})
  (Hwfcfg : OpsemPP.wf_Config cfg)
  (Hwfpp : OpsemPP.wf_State cfg
           {| Opsem.ECS := EC1 :: EC2 :: EC;
              Opsem.Mem := Mem |})
  Mem' (H : Instruction.isCallInst c' = true)
  (HwfS1 : wf_State pinfo
            {| Opsem.ECS := EC1 :: EC2 :: EC;
               Opsem.Mem := Mem |}),
  wf_State pinfo
     {| Opsem.ECS :=
             {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc';
                Opsem.Allocas := als' |} :: EC;
        Opsem.Mem := Mem' |}.
Proof.
  intros. subst. destruct cfg as [S [los nts] Ps gl fs].
  destruct Hwfcfg as [_ [_ [HwfSystem HmInS]]].
  destruct Hwfpp as 
    [_ [_ 
     [
       [
         [_ [HBinF1 [HFinPs1 [_ [_ [l2 [ps2 [cs2' Heq2]]]]]]]]
         _
       ]
       _
     ]
    ]]; subst.

  destruct HwfS1 as [Hinscope1 [Hinscope2 HwfECs]]. simpl.
  simpl in Hinscope1, Hinscope2, HwfECs.
  fold wf_ECStack in HwfECs.

  split; auto.
    SSCase "wf_EC".
    intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
    assert (before_palloca pinfo (c' :: cs')) as Hin.
      eapply before_palloca_cons; eauto.
    destruct_cmd c'; tinv H.
    unfold wf_ExecutionContext in *. simpl in Hinscope1, Hinscope2.
    auto.
Qed.

Lemma preservation_cmd_updated_case : forall (F : fdef)(B : block)
  (lc : @Opsem.GVsMap DGVs)(gv3 : GVsT DGVs) (cs : list cmd) (tmn : terminator) 
  id0 c0 Mem0 als ECs pinfo Mem1 als'
  (HwfPI : WF_PhiInfo pinfo) (Hid : Some id0 = getCmdID c0) EC
  (Heq: EC = {| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := c0 :: cs;
                Opsem.Terminator := tmn;
                Opsem.Locals := lc;
                Opsem.Allocas := als |}) cfg
  (Hwfpp : OpsemPP.wf_State cfg
           {| Opsem.ECS := EC :: ECs;
              Opsem.Mem := Mem0 |})
  (HwfS1 : wf_State pinfo
            {| Opsem.ECS := EC :: ECs;
               Opsem.Mem := Mem0 |})
  (Hneq :  F = PI_f pinfo -> id0 <> PI_id pinfo),
  wf_State pinfo
     {|
     Opsem.ECS := {|
            Opsem.CurFunction := F;
            Opsem.CurBB := B;
            Opsem.CurCmds := cs;
            Opsem.Terminator := tmn;
            Opsem.Locals := updateAddAL (GVsT DGVs) lc id0 gv3;
            Opsem.Allocas := als' |} :: ECs;
     Opsem.Mem := Mem1 |}.
Proof.
  intros. subst.
  destruct cfg as [S [los nts] Ps gl fs].
  destruct Hwfpp as 
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]]
     [HwfEC0 HwfCall]
    ]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0.
  destruct HwfS1 as [Hinscope HwfECs]. simpl.
  simpl in Hinscope, HwfECs.
  fold wf_ECStack in HwfECs.
  split; auto.
    intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
    unfold wf_ExecutionContext in *. simpl in Hinscope.
    eapply wf_defs_updateAddAL; eauto.
    apply Hinscope; auto.
      eapply before_palloca_cons; eauto.
Qed.

Lemma preservation_mem_updated_case : forall (F : fdef)(B : block)
  (lc : @Opsem.GVsMap DGVs)(gv3 : GVsT DGVs) (cs : list cmd) (tmn : terminator) 
  c0 Mem0 als Mem1 als' ECs pinfo EC
  (Heq: EC = {| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := c0 :: cs;
                Opsem.Terminator := tmn;
                Opsem.Locals := lc;
                Opsem.Allocas := als |}) cfg
  (Hwfpp : OpsemPP.wf_State cfg
           {| Opsem.ECS := EC :: ECs;
              Opsem.Mem := Mem0 |})
  (HwfS1 : wf_State pinfo
            {| Opsem.ECS := EC :: ECs;
               Opsem.Mem := Mem0 |}),
  wf_State pinfo
     {|
     Opsem.ECS := {|
            Opsem.CurFunction := F;
            Opsem.CurBB := B;
            Opsem.CurCmds := cs;
            Opsem.Terminator := tmn;
            Opsem.Locals := lc;
            Opsem.Allocas := als' |} :: ECs;
     Opsem.Mem := Mem1 |}.
Proof.
  intros. subst.
  destruct cfg as [S [los nts] Ps gl fs].
  destruct Hwfpp as 
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]]
     [HwfEC0 HwfCall]
    ]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0.
  destruct HwfS1 as [Hinscope HwfECs]. simpl.
  fold wf_ECStack in HwfECs.
  split; auto.
    intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
    apply Hinscope; auto. simpl.
      eapply before_palloca_cons; eauto.
Qed.

Ltac destruct_ctx_other :=
match goal with
| Hwfcfg : OpsemPP.wf_Config ?cfg,
  Hwfpp : OpsemPP.wf_State ?cfg _,
  HwfS1 : wf_State _ _ |- _ =>
  let l5:=fresh "l5" in
  let ps5:=fresh "ps5" in
  let cs5:=fresh "cs5" in
  destruct Hwfcfg as [_ [Hwfgl0 [HwfSystem HmInS]]];
  destruct Hwfpp as 
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l5 [ps5 [cs5 Heq1]]]]]]]]
     [HwfEC0 HwfCall]
    ]]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0;
  destruct HwfS1 as [Hinscope HwfECs]; simpl;
  simpl in Hinscope, HwfECs;
  fold wf_ECStack in HwfECs
end.

Ltac preservation_sBranch:=
  destruct_ctx_other;
  split; try solve [
    auto |
    intros J1 J2 J3; simpl in *; subst;
    elimtype False;
      match goal with
      | H: Some _ = (if ?e then _ else _) |- _ => destruct e
      | |- _ => idtac
      end;
      eapply entryBlock_has_no_pred; eauto using wf_system__wf_fdef,
                                                 wf_system__uniqFdef;
                                     simpl; auto
  ].

Ltac id_neq_pid_tac :=
match goal with
| |- _ <> PI_id _ =>
     intros; subst;
     match goal with
     | HBinF1: blockInFdefB _ _ = true |- _ =>
       eapply WF_PhiInfo_spec10 in HBinF1; eauto using wf_system__uniqFdef
     end
end.

Ltac preservation_pure_cmd_updated_case := abstract
  (eapply preservation_cmd_updated_case; eauto; try solve
    [simpl; auto | destruct_ctx_other; intro; id_neq_pid_tac]).

Lemma arguments_dont_define_pid: forall pinfo fa rt fid la va bs TD gvs lc
  (HwfP: WF_PhiInfo pinfo)
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) bs))
  (Heq: fdef_intro (fheader_intro fa rt fid la va) bs = PI_f pinfo)
  (Hinit: Opsem.initLocals TD la gvs = ret lc),
  wf_defs pinfo lc.
Proof.
  intros.
  unfold wf_defs.
  remember (lookupAL (GVsT DGVs) lc (PI_id pinfo)) as R.
  destruct R as [gv|]; auto.
  symmetry_ctx.
  eapply OpsemProps.In_initLocals__In_getArgsIDs in HeqR; eauto.
  rewrite Heq in Huniq.
  apply WF_PhiInfo_spec1 in HwfP; auto.
  rewrite <- Heq in Huniq.
  eapply IngetArgsIDs__lookupCmdViaIDFromFdef in Huniq; eauto.
  congruence.
Qed.

Lemma WF_PhiInfo_spec17: forall pinfo l5 ps5 cs5 cs tmn t v align0
  (HwfP: WF_PhiInfo pinfo) (Huniq: uniqFdef (PI_f pinfo))
  (HBinF: 
    blockInFdefB
      (block_intro l5 ps5 
          (cs5 ++ insn_alloca (PI_id pinfo) t v align0 :: cs) tmn)
      (PI_f pinfo) = true),
  t = PI_typ pinfo /\ v = PI_num pinfo /\ align0 = PI_align pinfo.
Proof.
  intros.
  apply WF_PhiInfo_spec1 in HwfP; auto.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HBinF; 
    eauto using in_middle.
  simpl in HBinF.
  uniq_result. auto.
Qed.

Lemma WF_PhiInfo_spec13: forall pinfo l5 ps5 cs5 cs tmn t v align0
  (HwfP: WF_PhiInfo pinfo) (Huniq: uniqFdef (PI_f pinfo))
  (Hentry: 
    getEntryBlock (PI_f pinfo) =
    ret block_intro l5 ps5 
          (cs5 ++ insn_alloca (PI_id pinfo) t v align0 :: cs) tmn),
  t = PI_typ pinfo /\ v = PI_num pinfo /\ align0 = PI_align pinfo.
Proof.
  intros.
  apply entryBlockInFdef in Hentry.
  eapply WF_PhiInfo_spec17 in HwfP; eauto.
Qed.

Lemma preservation : forall pinfo cfg S1 S2 tr
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (HsInsn: Opsem.sInsn cfg S1 S2 tr)
  (HwfS1: wf_State pinfo S1), wf_State pinfo S2.
Proof.
  intros.
  (sInsn_cases (induction HsInsn) Case); destruct TD as [los nts]; simpl HwfS1.

Case "sReturn". abstract (eapply preservation_return; eauto; simpl; auto).
Case "sReturnVoid". 
  abstract (eapply preservation_return_void; eauto; simpl; auto).
Case "sBranch". abstract preservation_sBranch.
Case "sBranch_uncond". abstract preservation_sBranch.
Case "sBop". preservation_pure_cmd_updated_case.
Case "sFBop". preservation_pure_cmd_updated_case.
Case "sExtractValue". preservation_pure_cmd_updated_case.
Case "sInsertValue". preservation_pure_cmd_updated_case.
Case "sMalloc". preservation_pure_cmd_updated_case.
Case "sFree". abstract (eapply preservation_mem_updated_case; eauto).
Case "sAlloca". 
  assert ((F = PI_f pinfo -> id0 <> PI_id pinfo) \/
          (F = PI_f pinfo -> id0 = PI_id pinfo)) as J. 
    destruct (id_dec id0 (PI_id pinfo)); tauto.
  destruct J as [J | J].
    preservation_pure_cmd_updated_case.

    abstract (
    destruct_ctx_other;
    split; try solve [
      auto |
      intros J1 J2 J3; simpl in J1, J2, J3; simpl; subst;
      rewrite J in J2; auto;
      unfold before_palloca in J3;
      rewrite J2 in J3;
      assert (uniqFdef (PI_f pinfo)) as Huniq; 
        try solve [match goal with
                   | |- uniqFdef _ => eauto using wf_system__uniqFdef
                   end];
      apply WF_PhiInfo_spec13 in J2; auto;
      destruct J2 as [A [B C]]; subst;
      destruct (@J3 cs5 cs) as [csa [csb [EQ1 EQ2]]]; auto;
      anti_simpl_env
    ]).
Case "sLoad". preservation_pure_cmd_updated_case.
Case "sStore". abstract (eapply preservation_mem_updated_case; eauto).
Case "sGEP". preservation_pure_cmd_updated_case.
Case "sTrunc". preservation_pure_cmd_updated_case.
Case "sExt". preservation_pure_cmd_updated_case.
Case "sCast". preservation_pure_cmd_updated_case.
Case "sIcmp". preservation_pure_cmd_updated_case.
Case "sFcmp". preservation_pure_cmd_updated_case.
Case "sSelect". destruct (isGVZero (los, nts) c); preservation_pure_cmd_updated_case.
Case "sCall".
  abstract (
  destruct_ctx_other;
  split; try solve [
    auto |
    intros J1 J2 J3; simpl in J1, J2, J3; simpl;
      apply OpsemAux.lookupFdefViaPtr_inv in H1; auto;
      eapply arguments_dont_define_pid; eauto using wf_system__uniqFdef |
    split; auto
  ]).
Case "sExCall". 
  abstract( 
  destruct_ctx_other;
  split; try solve [
    auto |
    intros J1 J2 J3; simpl in J1, J2, J3; simpl; subst;
    assert (wf_defs pinfo lc) as Hwd; try solve [
      match goal with
      | |- wf_defs _ _ =>
        apply Hinscope; simpl; try solve 
          [auto | eapply before_palloca_cons; eauto]
      end
    ];
    unfold Opsem.exCallUpdateLocals in *;
    destruct_if; try solve [
      auto |
      inv_mbind; try solve [
       auto |
       eapply wf_defs_updateAddAL; try solve [eauto | id_neq_pid_tac]
      ]
    ]
  ]).
Qed.

Lemma preservation_star : forall pinfo cfg S1 S2 tr
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (Hstar: Opsem.sop_star cfg S1 S2 tr)
  (HwfS1: wf_State pinfo S1), 
  wf_State pinfo S2.
Proof.
  intros.
  induction Hstar; auto.
    apply IHHstar.
      eapply OpsemPP.preservation; eauto.
      eapply preservation; eauto.
Qed.  

Lemma preservation_plus : forall pinfo cfg S1 S2 tr
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (Hplus: Opsem.sop_plus cfg S1 S2 tr)
  (HwfS1: wf_State pinfo S1), 
  wf_State pinfo S2.
Proof.
  intros.
  apply OpsemProps.sop_plus__implies__sop_star in Hplus.
  eapply preservation_star; eauto.
Qed.  

Lemma WF_PhiInfo_spec15: forall (pinfo : PhiInfo) (tmn2 : terminator)
  (lc2 : Opsem.GVsMap) (als2 : list mblock) (Hwfpi : WF_PhiInfo pinfo)
  (B : block) (t : typ) (v : value)
  (align0 : align) (EC : list Opsem.ExecutionContext) (cs : list cmd)
  (Mem : mem) 
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1
                 (cs11 ++ insn_alloca (PI_id pinfo) t v align0 :: cs) tmn2)
  (HBinF1 : blockInFdefB B (PI_f pinfo) = true)
  (Hpalloca : wf_State pinfo
               {|
               Opsem.ECS := {|
                            Opsem.CurFunction := PI_f pinfo;
                            Opsem.CurBB := B;
                            Opsem.CurCmds := insn_alloca 
                                               (PI_id pinfo) t v align0 :: cs;
                            Opsem.Terminator := tmn2;
                            Opsem.Locals := lc2;
                            Opsem.Allocas := als2 |} :: EC;
               Opsem.Mem := Mem |})
  (Huniq : uniqFdef (PI_f pinfo)),
  lookupAL (GVsT DGVs) lc2 (PI_id pinfo) = merror.
Proof.
  intros.
  destruct Hpalloca as [Hpalloca _].
  destruct Heq3 as [l1 [ps1 [cs11 Heq3]]]; subst.
  assert (getEntryBlock (PI_f pinfo) = 
    Some 
      (block_intro l1 ps1
        (cs11 ++ insn_alloca (PI_id pinfo) t v align0 :: cs) tmn2))
    as Hentry.
    apply WF_PhiInfo_spec14; auto.
  assert (G:=Hentry).
  apply WF_PhiInfo_spec13 in G; auto.
  destruct G as [A [B C]]; subst.
  apply Hpalloca; simpl; auto.
    unfold before_palloca.
    fill_ctxhole.
    intros.
    assert (cs11 = cs1 /\ cs = cs3) as G.
      eapply uniqFdef_cmds_split_middle; eauto.
    destruct G; subst.
    exists cs1. exists nil. auto.
Qed.

Lemma s_genInitState__palloca: forall S main VarArgs cfg IS pinfo
  (Hwfpi: WF_PhiInfo pinfo) (Hwfs: wf_system S)
  (Hinit : @Opsem.s_genInitState DGVs S main VarArgs Mem.empty = ret (cfg, IS)),
  wf_State pinfo IS.
Proof.
  intros.
  simpl_s_genInitState.
  split; simpl; auto.
    intros J1 J2 J3. simpl in *.
    apply getParentOfFdefFromSystem__moduleInProductsInSystemB in HeqR0.
    destruct HeqR0.
    eapply arguments_dont_define_pid; eauto using wf_system__uniqFdef.
Qed.

(*************************************)
(* find_init_stld and find_next_stld *)

Lemma find_init_stld_inr_spec: forall pinfo v cs cs0 dones
 (H: ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones),
 exists cs1, exists ty, exists num, exists al,
   v = value_const (const_undef ty) /\
   cs0 = cs1 ++
          insn_alloca (PI_id pinfo) ty num al :: cs.
Proof.
  induction cs0; simpl; intros.
    congruence.

Ltac find_init_stld_inr_spec_tac :=
match goal with
| H: Some _ = _,
  IHcs0 : forall _, Some _ = _ -> _ |- _ =>
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in
  apply IHcs0 in H;
  destruct H as [cs1 [ty [num [al [H1 H2]]]]]; subst;
  match goal with
  | |- exists _:_, exists _:_, exists _:_, exists _:_, _ /\ ?c :: _ = _ => 
    exists (c::cs1); exists ty; exists num; exists al; split; auto
  end
end.

    destruct a; try find_init_stld_inr_spec_tac.
      repeat (destruct_if; try solve [find_init_stld_inr_spec_tac]).
      exists nil. exists typ5. exists value5. exists align5. auto.

      destruct value2; try solve [find_init_stld_inr_spec_tac].
      repeat (destruct_if; try solve [find_init_stld_inr_spec_tac]).
Qed.

Lemma find_init_stld_inl_spec: forall pinfo i0 v cs cs0 dones
 (H: ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones),
 exists cs1, exists ty, exists al,
   cs0 = cs1 ++
         insn_store i0 ty v (value_id (PI_id pinfo)) al :: cs.
Proof.
  induction cs0; simpl; intros.
    congruence.

Ltac find_init_stld_inl_spec_tac :=
match goal with
| H: Some _ = _,
  IHcs0 : forall _, Some _ = _ -> _ |- _ =>
      apply IHcs0 in H;
      destruct H as [cs1 [ty [al H]]]; subst;
      match goal with
      | |- exists _:_, exists _:_, exists _:_, ?c :: _ = _ => 
           exists (c::cs1); exists ty; exists al; auto
      end
end.

    destruct a; try find_init_stld_inl_spec_tac.
      repeat (destruct_if; try solve [find_init_stld_inl_spec_tac]).

      destruct value2; try solve [find_init_stld_inl_spec_tac].
      repeat (destruct_if; try solve [find_init_stld_inl_spec_tac]).

      exists nil. exists typ5. exists align5. auto.
Qed.

Ltac find_next_stld_spec_tac :=
match goal with
| H: Some _ = _,
  IHcs0 : Some _ = _ -> _ |- _ =>
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in
  apply IHcs0 in H;
  destruct H as [cs1 [cs2 [ty [al [H1 H2]]]]]; subst;
  match goal with
  | |- exists _:_, exists _:_, exists _:_, exists _:_, ?c :: _ = _ /\ _ => 
       exists (c::cs1); exists cs2; exists ty; exists al; auto
  end
end.

Lemma find_next_stld_inl_spec: forall pinfo i1 cs
 (H: ret inl i1 = find_next_stld cs (PI_id pinfo)),
 exists cs1, exists cs2, exists ty, exists al,
   cs = cs1 ++
          insn_load i1 ty (value_id (PI_id pinfo)) al :: cs2 /\
   store_in_cmds (PI_id pinfo) cs1 = false.
Proof.
  induction cs; simpl; intros.
    congruence.

    destruct a; try find_next_stld_spec_tac.
      repeat (destruct_if; try solve [find_next_stld_spec_tac]).

      destruct value1; try solve [find_next_stld_spec_tac].
      destruct_if.
        exists nil. exists cs. exists typ5. exists align5.
        split; auto.

        find_next_stld_spec_tac.

      destruct value2; try solve [find_next_stld_spec_tac].
      destruct_if; try find_next_stld_spec_tac.
        split; auto. 
          simpl_env.
          apply store_in_cmds_merge.
          split; auto. 
            unfold store_in_cmds. simpl.
            destruct_dec. 
Qed.

Lemma find_next_stld_inr_spec: forall pinfo i1 v0 cs
 (H: ret inr (i1, v0) = find_next_stld cs (PI_id pinfo)),
 exists cs1, exists cs2, exists ty, exists al,
   cs = cs1 ++
          insn_store i1 ty v0 (value_id (PI_id pinfo)) al :: cs2 /\
   load_in_cmds (PI_id pinfo) cs1 = false.
Proof.
  induction cs; simpl; intros.
    congruence.

    destruct a; try find_next_stld_spec_tac.
      repeat (destruct_if; try solve [find_next_stld_spec_tac]).

      destruct value1; try solve [find_next_stld_spec_tac].
      destruct_if.
        find_next_stld_spec_tac.

        split; auto. 
          simpl_env.
          apply load_in_cmds_merge.
          split; auto. 
            unfold load_in_cmds. simpl.
            destruct_dec. 

      destruct value2; try solve [find_next_stld_spec_tac].
      repeat (destruct_if; try solve [find_next_stld_spec_tac]).
      exists nil. exists cs. exists typ5. exists align5.
      split; auto.
Qed.

(*************************************)
(* Aux invariants of wf ECs *)

(* go to infra *)
Definition wfEC_inv s m (EC: @Opsem.ExecutionContext DGVs) : Prop :=
uniqFdef (Opsem.CurFunction EC) /\ 
blockInFdefB (Opsem.CurBB EC) (Opsem.CurFunction EC) = true /\
match Opsem.CurCmds EC with
| nil => wf_insn s m (Opsem.CurFunction EC) (Opsem.CurBB EC) 
           (insn_terminator (Opsem.Terminator EC))
| c::_ => wf_insn s m (Opsem.CurFunction EC) (Opsem.CurBB EC) 
           (insn_cmd c)
end /\
exists l0, exists ps0, exists cs0,
  Opsem.CurBB EC = block_intro l0 ps0 (cs0 ++ Opsem.CurCmds EC)
    (Opsem.Terminator EC).

(* go to infra *)
Definition wfECs_inv s m (ECs: list (@Opsem.ExecutionContext DGVs)) : Prop :=
List.Forall (wfEC_inv s m) ECs.

(* go to infra *)
Lemma wf_EC__wfEC_inv: forall S los nts Ps EC
  (HwfS : wf_system S) 
  (HMinS : moduleInSystemB (module_intro los nts Ps) S = true)
  (Hwfec : OpsemPP.wf_ExecutionContext (los, nts) Ps EC),
  wfEC_inv S (module_intro los nts Ps) EC.
Proof.
  destruct EC; simpl.
  intros.
  destruct Hwfec as [J1 [J2 [J3 [J4 [J5 J6]]]]].
  unfold wfEC_inv. simpl.
  split; eauto 2 using wf_system__uniqFdef.
  split; auto.
  split; auto.
    destruct J6 as [l1 [ps1 [cs1 J6]]]; subst.
    destruct CurCmds.
      eapply wf_system__wf_tmn in J2; eauto.
      eapply wf_system__wf_cmd in J2; eauto using in_middle.
Qed.

(* go to infra *)
Lemma wf_ECStack__wfECs_inv: forall S los nts Ps ECs
  (HwfS : wf_system S) 
  (HMinS : moduleInSystemB (module_intro los nts Ps) S = true)
  (Hwf : OpsemPP.wf_ECStack (los, nts) Ps ECs),
  wfECs_inv S (module_intro los nts Ps) ECs.
Proof.
  unfold wfECs_inv.
  induction ECs as [|]; simpl; intros; auto.
    destruct Hwf as [J1 [J2 J3]].
    constructor; eauto using wf_EC__wfEC_inv.
Qed.

(* go to infra *)
Lemma wf_State__wfECs_inv: forall cfg St (Hwfc: OpsemPP.wf_Config cfg) 
  (Hwfst: OpsemPP.wf_State cfg St), 
  wfECs_inv (OpsemAux.CurSystem cfg) 
    (module_intro (fst (OpsemAux.CurTargetData cfg))
                  (snd (OpsemAux.CurTargetData cfg))
                  (OpsemAux.CurProducts cfg) )
    (Opsem.ECS St).
Proof.
  intros.
  destruct cfg as [? [? ?] ? ?].
  destruct St.
  destruct Hwfc as [? [? [? ?]]].
  destruct Hwfst. simpl.
  eapply wf_ECStack__wfECs_inv; eauto.
Qed.

(* go to infra *)
Definition uniqEC (EC: @Opsem.ExecutionContext DGVs) : Prop :=
uniqFdef (Opsem.CurFunction EC) /\ 
blockInFdefB (Opsem.CurBB EC) (Opsem.CurFunction EC) = true /\
exists l0, exists ps0, exists cs0,
  Opsem.CurBB EC = block_intro l0 ps0 (cs0 ++ Opsem.CurCmds EC)
    (Opsem.Terminator EC).

(* go to infra *)
Definition uniqECs (ECs: list (@Opsem.ExecutionContext DGVs)) : Prop :=
List.Forall uniqEC ECs.

Lemma wfEC_inv__uniqEC: forall s m EC (Hwf: wfEC_inv s m EC), uniqEC EC.
Proof.
  intros.
  destruct Hwf as [J1 [J3 [_ J2]]]. split; auto.
Qed.

Lemma wfECs_inv__uniqECs: forall s m ECs (Hwf: wfECs_inv s m ECs), uniqECs ECs.
Proof.
  unfold wfECs_inv, uniqECs.
  intros.
  induction Hwf; auto.
    constructor; auto.
      apply wfEC_inv__uniqEC in H; auto.
Qed.

(* go to infra *)
Lemma wf_State__uniqECs: forall cfg St (Hwfc: OpsemPP.wf_Config cfg) 
  (Hwfst: OpsemPP.wf_State cfg St), uniqECs (Opsem.ECS St).
Proof.
  intros.
  destruct cfg as [? [? ?] ? ?].
  destruct St.
  destruct Hwfc as [? [? [? ?]]].
  destruct Hwfst. simpl.
  eapply wf_ECStack__wfECs_inv in H4; eauto.
  eapply wfECs_inv__uniqECs; eauto.
Qed.

Ltac find_uniqEC :=
repeat match goal with
| H: uniqECs (Opsem.ECS {|Opsem.ECS := _; Opsem.Mem := _ |}) |- uniqEC _ => 
  simpl in H
| H: uniqECs (?EC::_) |- uniqEC ?EC => inv H; auto
| H: uniqECs (_::?EC::_) |- uniqEC ?EC => inv H; auto
| H: Forall uniqEC (?EC::_) |- uniqEC ?EC => inv H; auto
| H: Forall uniqEC (_::?EC::_) |- uniqEC ?EC => inv H; auto
end.

