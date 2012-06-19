Require Import vellvm.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import opsem_props.
Require Import program_sim.
Require Import promotable_props.
Require Import primitives.
Require Import palloca_props.
Require Import memory_props.
Require Import program_sim.
Require Import subst.
Require Import dse_top.
Require Import dse_wfS.
Require Import dae_top.
Require Import dae_wfS.
Require Import die_wfS.
Require Import phiplacement_bsim_wfS.
Require Import phiplacement_bsim_top.
Require Import iter_pass.
Require Import iter_pass_correct.
Require Import pass_combinators.
Require Import phielim_top.
Require Import mem2reg_correct.
Require Import mem2reg_opt.

Lemma action_dec: forall (ac1 ac2: action), {ac1 = ac2} + {ac1 <> ac2}.
Proof. decide equality; auto using value_dec, typ_dec. Qed.

Lemma id_action_dec: forall (ia1 ia2: id*action), {ia1 = ia2} + {ia1 <> ia2}.
Proof. decide equality; auto using id_dec, action_dec. Qed.

  Lemma set_remove_spec3 : forall n n' s (Huniq: uniq s),
    In n' (set_remove id_action_dec n s) -> n' <> n.
  Proof.
    induction 1; intros; simpl in *; auto.
      destruct (id_action_dec n (x, a)) as [J1 | J2]; subst; simpl in *; auto.
        intro EQ. subst.
        apply binds_dom_contradiction in H0; auto.

        destruct H0 as [H0 | H0]; subst; eauto.
  Qed.

  Lemma set_remove_notin_doms : forall x n E (Hnotin: x `notin` dom E),
    x `notin` dom (set_remove id_action_dec n E).
  Proof.
    induction E as [|[] E]; simpl; intros; auto.
      destruct_if. 
  Qed.

  Lemma set_remove_uniq: forall n s (Huniq: uniq s), 
    uniq (set_remove id_action_dec n s).
  Proof.
    induction 1; simpl.
      constructor. 
  
      destruct_if. simpl_env.
      constructor; auto. 
        apply set_remove_notin_doms; auto.
  Qed.

Lemma set_remove__seq_eq: forall actions2 actions1 (Huniq1 : uniq actions1)
  (x : AtomSetImpl.elt) (a : action) (H2 : x `notin` dom actions2)
  (Heq : AtomSet.set_eq actions1 ((x, a) :: actions2)),
  AtomSet.set_eq (set_remove id_action_dec (x, a) actions1) actions2.
Proof.
  intros.
  destruct Heq as [Hincl1 Hincl2].
  split.
    intros y Hiny.
    assert (y <> (x,a)) as Hneq.
      eapply set_remove_spec3 in Hiny; eauto.
    apply AtomSet.set_remove_spec2 in Hiny.
    apply Hincl1 in Hiny.
    destruct_in Hiny; try congruence.

    intros y Hiny.
    apply AtomSet.set_remove_spec1.
      apply Hincl2. xsolve_in_list.
      intro EQ. subst.
      apply binds_dom_contradiction in Hiny; auto.
Qed.

(***************************************************************)

Lemma remove_subst_phinodes__commute: forall i1 i0 v0 ps, 
  remove_phinodes i1 (List.map (subst_phi i0 v0) ps) = 
    List.map (subst_phi i0 v0) (remove_phinodes i1 ps).
Proof.
  induction ps as [|[] ps]; simpl; auto.
    destruct_if; simpl; f_equal; auto.
Qed.

Lemma remove_subst_cmds__commute: forall i1 i0 v0 cs, 
  remove_cmds i1 (List.map (subst_cmd i0 v0) cs) = 
    List.map (subst_cmd i0 v0) (remove_cmds i1 cs).
Proof.
  induction cs as [|c cs]; simpl; auto.
    destruct c; simpl; destruct_if; simpl; f_equal; auto.
Qed.

Lemma remove_subst_fdef__commute: forall i1 i0 v0 f, 
  remove_fdef i1 (subst_fdef i0 v0 f) = subst_fdef i0 v0 (remove_fdef i1 f).
Proof.
  destruct f as [fh bs]. simpl.
  f_equal.
  induction bs as [|[l1 ps1 cs1 tmn1] bs]; simpl; auto.
    f_equal; auto.
    rewrite remove_subst_phinodes__commute.
    rewrite remove_subst_cmds__commute.
    f_equal.
Qed.

(***************************************************************)

Definition apply_remove_action (f:fdef) (elt:id * action): fdef :=
let '(id1, ac1) := elt in remove_fdef id1 f.

Definition apply_subst_action (f:fdef) (elt:id * action): fdef :=
let '(id1, ac1) := elt in
match action2value ac1 with
| Some v1 => subst_fdef id1 v1 f
| _ => f
end.

Lemma apply_remove_subst_action__commute: forall f ac1 ac2,
  apply_remove_action (apply_subst_action f ac1) ac2 = 
    apply_subst_action (apply_remove_action f ac2) ac1.
Proof.
  destruct ac1 as [? []], ac2 as [? []]; simpl; 
    try rewrite remove_subst_fdef__commute; auto.
Qed.

Lemma apply_remove_substs_action__commute: forall actions f ac,
  apply_remove_action (ListMap.fold apply_subst_action actions f) ac = 
    ListMap.fold apply_subst_action actions (apply_remove_action f ac).
Proof.
  induction actions; simpl; intros; auto.
    rewrite IHactions.
    rewrite apply_remove_subst_action__commute; auto.
Qed.

Lemma apply_remove_subst_action__apply_action: forall f ac,
  apply_remove_action (apply_subst_action f ac) ac = apply_action f ac.
Proof. destruct ac as [? []]; simpl; auto. Qed.

Lemma list_apply_remove_subst_action__list_apply_action: forall actions f,
  ListMap.fold apply_remove_action actions
    (ListMap.fold apply_subst_action actions f) =
    ListMap.fold apply_action actions f.
Proof.
  induction actions; simpl; intro; auto.
    rewrite <- IHactions. clear IHactions.
    f_equal.
    rewrite apply_remove_substs_action__commute.
    rewrite apply_remove_subst_action__apply_action; auto.
Qed.

(***************************************************************)

Lemma filters_phinode_true_elim1: forall id0 ac0 p actions
  (Hin: In (id0, ac0) actions)
  (Hfilter: ListComposedPass.filters_phinode actions p = true),
  getPhiNodeID p <> id0.
Proof.
  unfold ListComposedPass.filters_phinode, ListMap.find.
  induction actions as [|[] actions]; simpl in *; intros.
    tauto.

    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom)
                    (getPhiNodeID p) a); subst; try congruence.
    destruct Hin as [Hin | Hin]; auto.
      uniq_result; auto.
Qed.

Lemma filters_phinode_false_elim1: forall p actions
  (Hfilter: ListComposedPass.filters_phinode actions p = false),
  exists ac0, In (getPhiNodeID p, ac0) actions.
Proof.
  unfold ListComposedPass.filters_phinode, ListMap.find.
  intros.
  induction actions as [|[] actions]; simpl in *; intros.
    congruence.

    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom)
                    (getPhiNodeID p) a); subst; eauto.
      apply IHactions in Hfilter. 
      destruct Hfilter. eauto.
Qed.

Lemma filters_phinode_true_elim2: forall id0 ac0 p actions
  (Hfilter: ListComposedPass.filters_phinode actions p = true),
  ListComposedPass.filters_phinode
    (set_remove id_action_dec (id0, ac0) actions) p = true.
Proof.
  intros.
  case_eq (ListComposedPass.filters_phinode
            (set_remove id_action_dec (id0, ac0) actions) p); auto.
  intro Hfalse. 
  apply filters_phinode_false_elim1 in Hfalse.
  destruct Hfalse as [ac1 Hin].
  apply AtomSet.set_remove_spec2 in Hin.
  eapply filters_phinode_true_elim1 in Hfilter; eauto.
Qed.

Lemma filters_phinode_false_intro1: forall p ac0 actions
  (Hin: In (getPhiNodeID p, ac0) actions),
  ListComposedPass.filters_phinode actions p = false.
Proof.
  unfold ListComposedPass.filters_phinode, ListMap.find.
  induction actions as [|[] actions]; simpl; intros.
    tauto.

    destruct Hin as [Hin | Hin].
      uniq_result.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom)
                    (getPhiNodeID p) (getPhiNodeID p)); auto.
        congruence.

      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom)
                    (getPhiNodeID p) i0); subst; auto.
Qed.

Lemma filters_phinode_false_intro2: forall id0 ac0 p actions
  (Hfilter: ListComposedPass.filters_phinode actions p = false)
  (Hneq: getPhiNodeID p <> id0),
  ListComposedPass.filters_phinode
    (set_remove id_action_dec (id0, ac0) actions) p = false.
Proof.
  intros.
  apply filters_phinode_false_elim1 in Hfilter.
  destruct Hfilter as [ac1 Hfilter].
  apply filters_phinode_false_intro1 with (ac0:=ac1); auto.
  apply AtomSet.set_remove_spec1; auto.
    intro EQ. uniq_result. congruence.
Qed.

Lemma filters_cmd_true_elim1: forall id0 ac0 c actions
  (Hin: In (id0, ac0) actions)
  (Hfilter: ListComposedPass.filters_cmd actions c = true),
  getCmdLoc c <> id0.
Proof.
  unfold ListComposedPass.filters_cmd, ListMap.find.
  induction actions as [|[] actions]; simpl in *; intros.
    tauto.

    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom)
                    (getCmdLoc c) a); subst; try congruence.
    destruct Hin as [Hin | Hin]; auto.
      uniq_result; auto.
Qed.

Lemma filters_cmd_false_elim1: forall c actions
  (Hfilter: ListComposedPass.filters_cmd actions c = false),
  exists ac0, In (getCmdLoc c, ac0) actions.
Proof.
  unfold ListComposedPass.filters_cmd, ListMap.find.
  intros.
  induction actions as [|[] actions]; simpl in *; intros.
    congruence.

    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom)
                    (getCmdLoc c) a); subst; eauto.
      apply IHactions in Hfilter. 
      destruct Hfilter. eauto.
Qed.

Lemma filters_cmd_true_elim2: forall id0 ac0 c actions
  (Hfilter: ListComposedPass.filters_cmd actions c = true),
  ListComposedPass.filters_cmd
    (set_remove id_action_dec (id0, ac0) actions) c = true.
Proof.
  intros.
  case_eq (ListComposedPass.filters_cmd
            (set_remove id_action_dec (id0, ac0) actions) c); auto.
  intro Hfalse. 
  apply filters_cmd_false_elim1 in Hfalse.
  destruct Hfalse as [ac1 Hin].
  apply AtomSet.set_remove_spec2 in Hin.
  eapply filters_cmd_true_elim1 in Hfilter; eauto.
Qed.

Lemma filters_cmd_false_intro1: forall c ac0 actions
  (Hin: In (getCmdLoc c, ac0) actions),
  ListComposedPass.filters_cmd actions c = false.
Proof.
  unfold ListComposedPass.filters_cmd, ListMap.find.
  induction actions as [|[] actions]; simpl; intros.
    tauto.

    destruct Hin as [Hin | Hin].
      uniq_result.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom)
                    (getCmdLoc c) (getCmdLoc c)); auto.
        congruence.

      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom)
                    (getCmdLoc c) i0); subst; auto.
Qed.

Lemma filters_cmd_false_intro2: forall id0 ac0 c actions
  (Hfilter: ListComposedPass.filters_cmd actions c = false)
  (Hneq: getCmdLoc c <> id0),
  ListComposedPass.filters_cmd
    (set_remove id_action_dec (id0, ac0) actions) c = false.
Proof.
  intros.
  apply filters_cmd_false_elim1 in Hfilter.
  destruct Hfilter as [ac1 Hfilter].
  apply filters_cmd_false_intro1 with (ac0:=ac1); auto.
  apply AtomSet.set_remove_spec1; auto.
    intro EQ. uniq_result. congruence.
Qed.

(***************************************************************)

Lemma list_subst_actions__uniq: forall id0 ac0 actions (Huniq: uniq actions),
  uniq (ListComposedPass.subst_actions id0 ac0 actions).
Proof.
  unfold ListComposedPass.subst_actions.
  intros. destruct (action2value ac0); auto.
Qed.

Lemma list_subst_actions__dom: forall id0 ac0 actions,
  dom (ListComposedPass.subst_actions id0 ac0 actions) [=] dom actions.
Proof.
  unfold ListComposedPass.subst_actions.
  intros. 
  destruct (action2value ac0); try fsetdec.
    apply dom_map.
Qed.

Lemma list_subst_actions__length: forall id0 ac0 actions,
  length actions = length (ListComposedPass.subst_actions id0 ac0 actions).
Proof.
  unfold ListComposedPass.subst_actions, ListMap.map.
  intros. destruct (action2value ac0); auto.
    erewrite <- List.map_length; eauto.
Qed.

(***************************************************************)

Program Fixpoint substs_actions (pairs: AssocList action) 
  {measure (length pairs)} : AssocList action :=
match pairs with 
| nil => nil
| (id1, ac1)::pairs' => 
    (id1, ac1)::substs_actions (ListComposedPass.subst_actions id1 ac1 pairs')
end.
Next Obligation.
  rewrite <- list_subst_actions__length; simpl; auto.
Qed.

Ltac unfold_substs_actions :=
match goal with
| |- appcontext [substs_actions ?arg] =>
   unfold substs_actions;
   Program.Wf.WfExtensionality.unfold_sub substs_actions arg
end.

(***************************************************************)

Definition list_substs_actions__dom_prop (n:nat) := forall actions
  (Hlen: (length actions = n)%nat),
  dom actions [=] dom (substs_actions actions).

Ltac solve_substs_actions_len :=
try solve [
  auto |
  match goal with
  | Hlen : length ((?id0, ?ac0) :: ?actions) = ?x |-
    (length (ListComposedPass.subst_actions ?id0 ?ac0 ?actions) + 0 < ?x)%nat =>
    subst x; simpl; rewrite <- list_subst_actions__length; omega
  | |- (length (ListComposedPass.subst_actions ?id0 ?ac0 ?actions) + 0 < 
         length ((?id0, ?ac0) :: ?actions) )%nat =>
    simpl; rewrite <- list_subst_actions__length; omega
  end
].

Lemma list_substs_actions__dom_aux: forall n,
  list_substs_actions__dom_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold list_substs_actions__dom_prop in *; intros.
  destruct actions as [|[id0 ac0] actions].
    simpl; try fsetdec.

    unfold_substs_actions.
    simpl. 
    rewrite <- Hrec; auto.
      rewrite list_subst_actions__dom; fsetdec.
      solve_substs_actions_len.
Qed.


Lemma list_substs_actions__dom: forall actions,
  dom actions [=] dom (substs_actions actions).
Proof.
  intros.
  assert (J:=@list_substs_actions__dom_aux (length actions)).
  unfold list_substs_actions__dom_prop in J.
  auto.
Qed.

Definition list_substs_actions__uniq_prop (n:nat) := forall actions
  (Hlen: (length actions = n)%nat) (Huniq: uniq actions),
  uniq (substs_actions actions).

Lemma list_substs_actions__uniq_aux: forall n,
  list_substs_actions__uniq_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold list_substs_actions__uniq_prop in *; intros.
  destruct actions as [|[id0 ac0] actions].
    simpl; auto.

    unfold_substs_actions.
    simpl_env.
    inv Huniq.
    constructor.
      eapply Hrec; eauto.
        solve_substs_actions_len.

        apply list_subst_actions__uniq; auto.

        rewrite <- list_substs_actions__dom.
        rewrite list_subst_actions__dom; auto.
Qed.

Lemma list_substs_actions__uniq: forall actions (Huniq: uniq actions),
  uniq (substs_actions actions).
Proof.
  intros.
  assert (J:=@list_substs_actions__uniq_aux (length actions)).
  unfold list_substs_actions__uniq_prop in J.
  auto.
Qed.

(***************************************************************)

Lemma list_composed_removes_phis__empty: forall ps,
  ListComposedPass.removes_phinodes (empty_set (atom * action)) ps = ps.
Proof.
  induction ps; simpl; auto.
    f_equal. auto.
Qed.

Lemma list_composed_removes_cmds__empty: forall cs,
  ListComposedPass.removes_cmds (empty_set (atom * action)) cs = cs.
Proof.
  induction cs; simpl; auto.
    f_equal. auto.
Qed.

Lemma list_composed_removes__empty: forall f,
  ListComposedPass.removes_fdef (empty_set (atom * action)) f = f.
Proof.
  destruct f as [fh bs]. simpl.
  f_equal.
  induction bs as [|[l1 ps1 cs1 tmn1] bs]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
    apply list_composed_removes_phis__empty; auto.
    apply list_composed_removes_cmds__empty; auto.
Qed.

(***************************************************************)

Lemma list_composed_removes_phis__commute: forall actions id0 ac0
  (Hin : In (id0, ac0) actions) ps,
  ListComposedPass.removes_phinodes actions ps =
    ListComposedPass.removes_phinodes
      (set_remove id_action_dec (id0, ac0) actions)
      (remove_phinodes id0 ps).
Proof.
  intros.
  unfold remove_phinodes.
  induction ps as [|p ps]; simpl; auto.
    case_eq (ListComposedPass.filters_phinode actions p).
      intros Heq.
      assert (negb (id_dec (getPhiNodeID p) id0) = true) as Hneq.
        destruct (id_dec (getPhiNodeID p) id0); auto.
        eapply filters_phinode_true_elim1 in Heq; eauto.
      rewrite Hneq. simpl.
      assert (ListComposedPass.filters_phinode
                (set_remove id_action_dec (id0, ac0) actions) p = true)
        as Heq'.
        eapply filters_phinode_true_elim2 in Heq; eauto.
      rewrite Heq'. congruence.

      intros Heq.
      destruct_if; try congruence.
        simpl.
        assert (ListComposedPass.filters_phinode
                (set_remove id_action_dec (id0, ac0) actions) p = false)
          as Hneq'.
          destruct (id_dec (getPhiNodeID p) id0); tinv HeqR.
          eapply filters_phinode_false_intro2; eauto 1.
        rewrite Hneq'. congruence.
Qed.

Lemma list_composed_removes_cmds__commute: forall actions id0 ac0
  (Hin : In (id0, ac0) actions) cs,
  ListComposedPass.removes_cmds actions cs =
    ListComposedPass.removes_cmds
      (set_remove id_action_dec (id0, ac0) actions)
      (remove_cmds id0 cs).
Proof.
  intros.
  unfold remove_cmds.
  induction cs as [|c cs]; simpl; auto.
    case_eq (ListComposedPass.filters_cmd actions c).
      intros Heq.
      assert (negb (id_dec (getCmdLoc c) id0) = true) as Hneq.
        destruct (id_dec (getCmdLoc c) id0); auto.
        eapply filters_cmd_true_elim1 in Heq; eauto.
      rewrite Hneq. simpl.
      assert (ListComposedPass.filters_cmd
                (set_remove id_action_dec (id0, ac0) actions) c = true)
        as Heq'.
        eapply filters_cmd_true_elim2 in Heq; eauto.
      rewrite Heq'. congruence.

      intros Heq.
      destruct_if; try congruence.
        simpl.
        assert (ListComposedPass.filters_cmd
                (set_remove id_action_dec (id0, ac0) actions) c = false)
          as Hneq'.
          destruct (id_dec (getCmdLoc c) id0); tinv HeqR.
          eapply filters_cmd_false_intro2; eauto 1.
        rewrite Hneq'. congruence.
Qed.

Lemma list_composed_removes__commute: forall actions ac (Hin: In ac actions) f,
  ListComposedPass.removes_fdef actions f =
     ListComposedPass.removes_fdef (set_remove id_action_dec ac actions)
       (apply_remove_action f ac).
Proof.
  destruct f as [fh bs]. simpl.
  destruct ac as [id0 ac0]; simpl.
  f_equal.
  induction bs as [|[l1 ps1 cs1 tmn1] bs]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
    apply list_composed_removes_phis__commute; auto.
    apply list_composed_removes_cmds__commute; auto.
Qed.

Lemma list_composed_removes__list_pipelined_removes: forall actions2 
  actions1 (Huniq1: uniq actions1) (Huniq2: uniq actions2) f
  (Heq: AtomSet.set_eq actions1 actions2),
  ListComposedPass.removes_fdef actions1 f = 
    ListMap.fold apply_remove_action actions2 f.
Proof.
  induction actions2 as [|ac2 actions2]; simpl; intros.
  Case "base".
    apply AtomSet.set_eq_empty_inv in Heq. subst. 
    apply list_composed_removes__empty.
  Case "ind".
    inv Huniq2.
    rewrite <- IHactions2 with (f:=apply_remove_action f (x,a))
      (actions1:=set_remove id_action_dec (x,a) actions1); auto.
    SCase "1".
      apply list_composed_removes__commute.
        destruct Heq as [Hincl1 Hincl2].
        apply Hincl2; simpl; auto.
          apply set_remove_uniq; auto.
    SCase "2".
      apply set_remove__seq_eq; auto.
Qed.

(***************************************************************)

Require Import FMapFacts.

Module AVLFacts := WFacts_fun (AtomOT) (AVLMap.AtomFMapAVL).

Lemma AVLFacts_in_find_some: forall (elt : Type) (m : AVLMap.AtomFMapAVL.t elt)
  (x : AVLMap.AtomFMapAVL.key) (Hin: AVLMap.AtomFMapAVL.In (elt:=elt) x m),
  exists e, AVLMap.AtomFMapAVL.find (elt:=elt) x m = Some e.
Proof.
  intros.
  apply AVLFacts.in_find_iff in Hin.
  case_eq (AVLMap.AtomFMapAVL.find (elt:=elt) x m); try congruence; eauto.
Qed.

Lemma AVLFacts_find_some_in: forall (elt : Type) (m : AVLMap.AtomFMapAVL.t elt)
  (x : AVLMap.AtomFMapAVL.key) e
  (Hfind: AVLMap.AtomFMapAVL.find (elt:=elt) x m = Some e),
  AVLMap.AtomFMapAVL.In (elt:=elt) x m.
Proof.
  intros. apply AVLFacts.in_find_iff. congruence.
Qed.

(***************************************************************)

Lemma avl_subst_actions__remove_spec: forall id0 id1 ac1 actions,
  AVLMap.AtomFMapAVL.MapsTo id0 AC_remove actions <-> 
    AVLMap.AtomFMapAVL.MapsTo id0 AC_remove 
      (AVLComposedPass.subst_actions id1 ac1 actions).
Proof.
  unfold AVLComposedPass.subst_actions.
  intros.
  destruct (action2value ac1); try tauto.
  split; intro J.
    change AC_remove with (subst_action id1 v AC_remove); auto.
    apply AVLMap.AtomFMapAVL.map_1; auto.
 
    apply AVLFacts.map_mapsto_iff in J.
    destruct J as [[] [J1 J2]]; inv J1; auto.
Qed.

Lemma avl_compose_actions__remove_spec: forall id0 actions (Huniq: uniq actions),
  In (id0, AC_remove) actions <-> 
    AVLMap.AtomFMapAVL.MapsTo id0 AC_remove 
      (AVLComposedPass.compose_actions actions).
Proof.
  induction 1; simpl.
  Case "base".
    split; try tauto.
      intros H.
      contradict H.
      apply AVLMap.AtomFMapAVL.is_empty_2; auto.
  Case "ind".
    split; intro J.
    SCase "ind1".
      destruct J as [J | J].
        uniq_result.
        apply AVLMap.AtomFMapAVL.add_1; auto.

        assert (x <> id0) as Hneq. 
          intro EQ; subst.
          apply binds_dom_contradiction in J; auto.
        apply AVLMap.AtomFMapAVL.add_2; auto.
        apply IHHuniq in J.
        apply avl_subst_actions__remove_spec; auto.
    SCase "ind2".
      apply AVLFacts.add_mapsto_iff in J.
      destruct J as [[J1 J2] | [J1 J2]]; subst.
        apply AVLComposedPass.find_parent_action_inv in J2.
        destruct J2 as [J2 | [id1 [J21 [J22 J23]]]]; subst; auto.
        congruence.

        right.
        apply avl_subst_actions__remove_spec in J2; auto.
        tauto.
Qed.

Lemma list_subst_actions__remove_spec: forall id0 id1 ac1 actions,
  In (id0, AC_remove) actions <-> 
    In (id0, AC_remove) (ListComposedPass.subst_actions id1 ac1 actions).
Proof.
  unfold ListComposedPass.subst_actions.
  intros.
  destruct (action2value ac1); try tauto.
  fold (subst_action id1 v).
  induction actions as [|ac actions]; simpl; try tauto.
    split; intro J.
      destruct J as [J | J]; subst; simpl; auto.
        apply IHactions in J.
          destruct ac; simpl; auto.
      destruct J as [J | J].
        destruct ac as [? []]; inv J; auto.
        right. tauto.
Qed.

Definition list_substs_actions__remove_spec_prop (n:nat) := forall id0 actions
  (Hlen: (length actions = n)%nat),
  In (id0, AC_remove) actions <-> 
    In (id0, AC_remove) (substs_actions actions).

Lemma list_substs_actions__remove_spec_aux: forall n,
  list_substs_actions__remove_spec_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold list_substs_actions__remove_spec_prop in *; intros.
  destruct actions as [|[id1 ac1] actions].
    simpl; intros; try tauto.

    unfold_substs_actions.
    simpl. 
    split; intro J.
      destruct J as [J | J]; subst; simpl; auto.
        right. 
        apply list_subst_actions__remove_spec with (id1:=id1)(ac1:=ac1) in J.
        eapply Hrec in J; eauto.
          solve_substs_actions_len.

      destruct J as [J | J]; auto.
        right. 
        eapply Hrec in J; eauto.
          eapply list_subst_actions__remove_spec; eauto.
          solve_substs_actions_len.
Qed.

Lemma list_substs_actions__remove_spec: forall id0 actions,
  In (id0, AC_remove) actions <-> 
    In (id0, AC_remove) (substs_actions actions).
Proof.
 intros.
  assert (J:=@list_substs_actions__remove_spec_aux (length actions)).
  unfold list_substs_actions__remove_spec_prop in J.
  auto.
Qed.

(***************************************************************)

Lemma avl_subst_actions__in_spec: forall id0 id1 ac1 actions,
  AVLMap.AtomFMapAVL.In id0 (AVLComposedPass.subst_actions id1 ac1 actions) <->
    AVLMap.AtomFMapAVL.In id0 actions.
Proof.
  unfold AVLComposedPass.subst_actions.
  intros.
  destruct (action2value ac1); try tauto.
  apply AVLFacts.map_in_iff.
Qed.

Lemma avl_compose_actions__in_spec: forall id0 actions (Huniq: uniq actions),
  AVLMap.AtomFMapAVL.In id0 (AVLComposedPass.compose_actions actions) <->
    id0 `in` dom actions.
Proof.
  induction 1; simpl.
  Case "base".
    split; intro H.
      apply AVLFacts.empty_in_iff in H. tauto.
      fsetdec.
  Case "ind".
    split; intro J.
    SCase "ind1".
      apply AVLFacts.add_in_iff in J.
      destruct J as [J | J]; subst.
        fsetdec.

        assert (id0 `in` dom E) as Hin.
          apply IHHuniq.
          eapply avl_subst_actions__in_spec; eauto.
        fsetdec.
    SCase "ind2".
      apply AVLFacts.add_in_iff.
      assert (id0 = x \/ id0 `in` dom E) as J'.
        fsetdec.
      destruct J' as [J' | J']; subst; auto.
        right.
        apply avl_subst_actions__in_spec; tauto.
Qed.

Lemma list_subst_actions__in_spec: forall id0 id1 ac1 actions,
  id0 `in` dom actions <-> 
    id0 `in` dom (ListComposedPass.subst_actions id1 ac1 actions).
Proof.
  intros.
  rewrite list_subst_actions__dom; auto.
  fsetdec.
Qed.

Lemma list_substs_actions__in_spec: forall id0 actions,
  id0 `in` dom actions <-> id0 `in` dom (substs_actions actions).
Proof.
  intros.
  rewrite list_substs_actions__dom; auto.
  fsetdec.
Qed.

(***************************************************************)

Definition avl_actions__iff_dom__list_actions 
  A (actions1:AVLMap.t A) (actions2:ListMap.t A): Prop :=
forall id0, 
  AVLMap.AtomFMapAVL.In id0 actions1 <-> id0 `in` dom actions2.

Implicit Arguments avl_actions__iff_dom__list_actions [A].

Lemma avl_filters_phinode__iff_dom__list_filters_phinode: forall actions1 actions2
  (Hiff : avl_actions__iff_dom__list_actions actions1 actions2) p,
  AVLComposedPass.filters_phinode actions1 p = 
    ListComposedPass.filters_phinode actions2 p.
Proof.
  unfold AVLComposedPass.filters_phinode, AVLMap.find,
         ListComposedPass.filters_phinode, ListMap.find,
         avl_actions__iff_dom__list_actions.
  intros.
  case_eq (lookupAL action actions2 (getPhiNodeID p)).
    intros ac Heq.
    apply lookupAL_Some_indom in Heq.
    apply Hiff in Heq.
    apply AVLFacts_in_find_some in Heq.
    destruct Heq as [e Heq]. rewrite Heq. auto.

    intros Hneq.
    case_eq (AVLMap.AtomFMapAVL.find 
              (elt:=action) (getPhiNodeID p) actions1); auto.
    intros ac Heq.
    apply AVLFacts_find_some_in in Heq.
    apply Hiff in Heq.
    apply lookupAL_None_notindom in Hneq.
    auto.
Qed.

Lemma avl_removes_phinodes__iff_dom__list_removes_phinodes: forall actions1 actions2
  (Hiff : avl_actions__iff_dom__list_actions actions1 actions2) ps,
  AVLComposedPass.removes_phinodes actions1 ps =
    ListComposedPass.removes_phinodes actions2 ps.
Proof.
  induction ps as [|p ps]; simpl; intros; auto.
    rewrite IHps.
    erewrite avl_filters_phinode__iff_dom__list_filters_phinode; eauto.
Qed.

Lemma avl_filters_cmd__iff_dom__list_filters_cmd: forall actions1 actions2
  (Hiff : avl_actions__iff_dom__list_actions actions1 actions2) c,
  AVLComposedPass.filters_cmd actions1 c = 
    ListComposedPass.filters_cmd actions2 c.
Proof.
  unfold AVLComposedPass.filters_cmd, AVLMap.find,
         ListComposedPass.filters_cmd, ListMap.find,
         avl_actions__iff_dom__list_actions.
  intros.
  case_eq (lookupAL action actions2 (getCmdLoc c)).
    intros ac Heq.
    apply lookupAL_Some_indom in Heq.
    apply Hiff in Heq.
    apply AVLFacts_in_find_some in Heq.
    destruct Heq as [e Heq]. rewrite Heq. auto.

    intros Hneq.
    case_eq (AVLMap.AtomFMapAVL.find 
              (elt:=action) (getCmdLoc c) actions1); auto.
    intros ac Heq.
    apply AVLFacts_find_some_in in Heq.
    apply Hiff in Heq.
    apply lookupAL_None_notindom in Hneq.
    auto.
Qed.

Lemma avl_removes_cmds__iff_dom__list_removes_cmds: forall actions1 actions2
  (Hiff : avl_actions__iff_dom__list_actions actions1 actions2) cs,
  AVLComposedPass.removes_cmds actions1 cs =
    ListComposedPass.removes_cmds actions2 cs.
Proof.
  induction cs as [|c cs]; simpl; intros; auto.
    rewrite IHcs.
    erewrite avl_filters_cmd__iff_dom__list_filters_cmd; eauto.
Qed.

Lemma avl_removes_fdef__iff_dom__list_removes_fdef: forall actions2 
  (Huniq2: uniq actions2) actions1 f
  (Hiff: avl_actions__iff_dom__list_actions actions1 actions2),
  AVLComposedPass.removes_fdef actions1 f = 
    ListMap.fold apply_remove_action actions2 f.
Proof.
  intros.
  rewrite <- list_composed_removes__list_pipelined_removes 
    with (actions1:=actions2); auto with atomset.
  destruct f as [fh bs]. simpl.
  f_equal.
  induction bs as [|[l1 ps1 cs1 tmn1] bs]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
    apply avl_removes_phinodes__iff_dom__list_removes_phinodes; auto.
    apply avl_removes_cmds__iff_dom__list_removes_cmds; auto.
Qed.

Lemma avl_removes_fdef__list_removes_fdef: forall actions 
  (Huniq: uniq actions) f1,
  AVLComposedPass.removes_fdef (AVLComposedPass.compose_actions actions) f1 = 
    ListMap.fold apply_remove_action (substs_actions actions) f1.
Proof.
  intros.
  apply avl_removes_fdef__iff_dom__list_removes_fdef; 
    auto using list_substs_actions__uniq.
  unfold avl_actions__iff_dom__list_actions.
  intros.
  assert (J:=@list_substs_actions__in_spec id0 actions).
  assert (J':=@avl_compose_actions__in_spec id0 actions Huniq).
  tauto.
Qed.

(***************************************************************)

Lemma list_composed_substs_value_nil: forall v,
  ListComposedPass.substs_value nil v = v.
Proof.
  destruct v; simpl; auto.
Qed.

Lemma list_composed_substs_list_value_l_nil: forall l0,
  ListComposedPass.substs_list_value_l nil l0 = l0.
Proof.
  induction l0 as [|[] l1]; simpl; auto.
    f_equal; auto.
    f_equal.
    apply list_composed_substs_value_nil.
Qed.

Lemma list_composed_substs_phis_nil: forall ps,
  List.map (ListComposedPass.substs_phi nil) ps = ps.
Proof.
  induction ps as [|[] ps]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
      apply list_composed_substs_list_value_l_nil.
Qed.

Lemma list_composed_substs_list_value_nil: forall l0,
  ListComposedPass.substs_list_value nil l0 = l0.
Proof.
  induction l0 as [|[] l0]; simpl; intros; auto.
    f_equal; auto.
    f_equal.
    apply list_composed_substs_value_nil.
Qed.

Lemma list_composed_substs_params_nil: forall (params5 : params),
  List.map
     (fun p : typ * attributes * value =>
      let '(t, v) := p in
           (t,
           ListComposedPass.substs_value nil v)) params5 = params5.
Proof.
  induction params5 as [|[[]] params5]; simpl; intros; auto.
    f_equal; auto.
    f_equal.
    apply list_composed_substs_value_nil; auto.
Qed.

Lemma list_composed_substs_cmds_nil: forall cs,
  List.map (ListComposedPass.substs_cmd nil) cs = cs.
Proof.
  induction cs as [|c cs]; simpl; intros; auto.
    f_equal; auto.
    destruct c; simpl; f_equal; try solve [
      apply list_composed_substs_value_nil; auto |
      apply list_composed_substs_list_value_nil; auto |
      apply list_composed_substs_params_nil; auto
    ].
Qed.

Lemma list_composed_substs_tmn_nil: forall tmn,
  ListComposedPass.substs_tmn nil tmn = tmn.
Proof.
  destruct tmn; simpl; f_equal; try solve 
    [apply list_composed_substs_value_nil; auto].
Qed.

Lemma list_composed_substs_blocks_nil: forall bs,
  List.map (ListComposedPass.substs_block nil) bs = bs.
Proof.
  induction bs as [|[l1 ps1 cs1 tmn1] bs]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
      apply list_composed_substs_phis_nil; auto.
      apply list_composed_substs_cmds_nil; auto.
      apply list_composed_substs_tmn_nil; auto.
Qed.

(***************************************************************)

Lemma list_composed_substs_value_doesnt_use_AC_remove: forall id0 
  actions (Hnotin: id0 `notin` dom actions) v,
  ListComposedPass.substs_value ((id0, AC_remove) :: actions) v =
    ListComposedPass.substs_value actions v.
Proof.
  destruct v; simpl; auto.
  destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id5 id0); 
    subst; simpl; auto.
  unfold ListMap.find.
  rewrite notin_lookupAL_None; auto.
Qed.

Lemma list_composed_substs_list_value_l_doesnt_use_AC_remove: forall id0 
  actions (Hnotin: id0 `notin` dom actions) l0,
  ListComposedPass.substs_list_value_l ((id0, AC_remove) :: actions) l0 =
    ListComposedPass.substs_list_value_l actions l0.
Proof.
  induction l0 as [|[] l1]; simpl; auto.
    f_equal; auto.
    f_equal.
    apply list_composed_substs_value_doesnt_use_AC_remove; auto.
Qed.

Lemma list_composed_substs_phis_doesnt_use_AC_remove: forall id0 
  actions (Hnotin: id0 `notin` dom actions) ps,
  List.map
    (ListComposedPass.substs_phi ((id0, AC_remove) :: actions)) ps =
  List.map (ListComposedPass.substs_phi actions) ps.
Proof.
  induction ps as [|[] ps]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
      apply list_composed_substs_list_value_l_doesnt_use_AC_remove; auto.
Qed.

Lemma list_composed_substs_list_value_doesnt_use_AC_remove: forall id0 
  actions (Hnotin: id0 `notin` dom actions) l0,
  ListComposedPass.substs_list_value ((id0, AC_remove)::actions) l0 =
   ListComposedPass.substs_list_value actions l0.
Proof.
  induction l0 as [|[] l0]; simpl; intros; auto.
    f_equal; auto.
    f_equal.
    apply list_composed_substs_value_doesnt_use_AC_remove; auto.
Qed.

Lemma list_composed_substs_params_doesnt_use_AC_remove: forall id0 
  actions (Hnotin: id0 `notin` dom actions) (params5 : params),
  List.map
     (fun p : typ * attributes * value =>
      let '(t, v) := p in
           (t,
           ListComposedPass.substs_value
             ((id0, AC_remove)::actions) v)) params5 =
  List.map
     (fun p : typ * attributes * value =>
      let '(t, v) := p in
           (t,
           ListComposedPass.substs_value actions v)) params5.
Proof.
  induction params5 as [|[[]] params5]; simpl; intros; auto.
    f_equal; auto.
    f_equal.
    apply list_composed_substs_value_doesnt_use_AC_remove; auto.
Qed.

Lemma list_composed_substs_cmds_doesnt_use_AC_remove: forall id0 
  actions (Hnotin: id0 `notin` dom actions) cs,
  List.map
    (ListComposedPass.substs_cmd ((id0, AC_remove) :: actions)) cs =
    List.map (ListComposedPass.substs_cmd actions) cs.
Proof.
  induction cs as [|c cs]; simpl; intros; auto.
    f_equal; auto.
    destruct c; simpl; f_equal; try solve [
      apply list_composed_substs_value_doesnt_use_AC_remove; auto |
      apply list_composed_substs_list_value_doesnt_use_AC_remove; auto |
      apply list_composed_substs_params_doesnt_use_AC_remove; auto
    ].
Qed.

Lemma list_composed_substs_tmn_doesnt_use_AC_remove: forall id0 
  actions (Hnotin: id0 `notin` dom actions) tmn,
  ListComposedPass.substs_tmn ((id0, AC_remove) :: actions) tmn =
  ListComposedPass.substs_tmn actions tmn.
Proof.
  destruct tmn; simpl; f_equal; try solve 
    [apply list_composed_substs_value_doesnt_use_AC_remove; auto].
Qed.

Lemma list_composed_substs_blocks_doesnt_use_AC_remove: forall id0 
  actions (Hnotin: id0 `notin` dom actions) bs,
  List.map
    (ListComposedPass.substs_block ((id0, AC_remove) :: actions)) bs =
  List.map (ListComposedPass.substs_block actions) bs.
Proof.
  induction bs as [|[l1 ps1 cs1 tmn1] bs]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
      apply list_composed_substs_phis_doesnt_use_AC_remove; auto.
      apply list_composed_substs_cmds_doesnt_use_AC_remove; auto.
      apply list_composed_substs_tmn_doesnt_use_AC_remove; auto.
Qed.

(***************************************************************)

Definition subst_action_action (ac:action) (elt:id * action): action :=
let '(id1, ac1) := elt in
match action2value ac1 with
| Some v1 => subst_action id1 v1 ac
| _ => ac
end.

Definition pipelined_actions_action (actions: list (id*action)) (ac:action) 
  : action :=
List.fold_left subst_action_action actions ac.

Definition pipelined_actions (pairs: AssocList action) (f:fdef) : fdef :=
List.fold_left apply_action (substs_actions pairs) f.

Fixpoint pipelined_actions__composed_actions (actions: list (id*action))
  : list (id*action) :=
match actions with
| nil => nil
| (id0,ac0)::actions' => 
    (id0, pipelined_actions_action actions' ac0)::
      pipelined_actions__composed_actions actions'
end.

Definition composed_pipelined_actions (pairs: AssocList action) (f:fdef): fdef :=
ListComposedPass.substs_fdef 
  (pipelined_actions__composed_actions (substs_actions pairs)) f.

Definition subst_action_value (v:value) (elt:id * action): value :=
let '(id1, ac1) := elt in
match action2value ac1 with
| Some v1 => subst_value id1 v1 v 
| _ => v
end.

Definition pipelined_actions_value (actions: list (id*action)) (v:value) 
  : value :=
List.fold_left subst_action_value actions v.

Lemma pipelined_actions_action_tail: forall id0 actions2 actions1
  (Hnotin: id0 `notin` dom actions1),
  pipelined_actions_action (actions1++actions2) (AC_vsubst (value_id id0)) =
    pipelined_actions_action actions2 (AC_vsubst (value_id id0)).
Proof.
  induction actions1 as [|[id5 ac5] actions1]; simpl; intros; auto.
    rewrite <- IHactions1; auto.
    destruct_if.
      contradict Hnotin; simpl; auto.
      destruct (action2value ac5); auto.
Qed.

Lemma pipelined_actions_action_AC_remove: forall actions,
  pipelined_actions_action actions AC_remove = AC_remove.
Proof.
  unfold pipelined_actions_action.
  induction actions as [|[]]; simpl; auto. 
    destruct (action2value a); auto.
Qed.

Lemma pipelined_actions_action_AC_vsubst_notin: forall id0 actions
  (Hnotin: id0 `notin` dom actions),
  pipelined_actions_action actions (AC_vsubst (value_id id0)) =
    (AC_vsubst (value_id id0)).
Proof.
  induction actions as [|[id5 ac5] actions]; simpl; intros; auto.
    destruct_if.
      contradict Hnotin; simpl; auto.
      destruct (action2value ac5); auto.
Qed.

Lemma pipelined_actions_action_AC_vsubst_const: forall actions cnt,
  pipelined_actions_action actions (AC_vsubst (value_const cnt)) = 
    AC_vsubst (value_const cnt).
Proof.
  unfold pipelined_actions_action.
  induction actions as [|[]]; simpl; auto. 
    destruct (action2value a); auto.
Qed.

Lemma pipelined_actions_action_AC_tsubst: forall actions t,
  pipelined_actions_action actions (AC_tsubst t) = AC_tsubst t.
Proof.
  unfold pipelined_actions_action.
  induction actions as [|[]]; simpl; auto. 
    destruct (action2value a); auto.
Qed.

Lemma pipelined_actions_action_AC_remove_inv: forall actions ac
  (Heq: pipelined_actions_action actions ac = AC_remove),
  ac = AC_remove.
Proof.
  unfold pipelined_actions_action.
  induction actions as [|[]]; simpl; intros; auto. 
    apply IHactions in Heq.
    destruct (action2value a); auto.
    destruct ac; inv Heq; auto.
Qed.

Lemma action2value__subst_action_action__subst_action_value: forall ac0 
  v0 (Heq: action2value ac0 = ret v0) ac,
  action2value (subst_action_action ac0 ac) = ret subst_action_value v0 ac.
Proof.
  destruct ac; simpl.
  destruct (action2value a); auto.
    destruct ac0; simpl; inv Heq; auto.
Qed.

Lemma action2value__pipelined_actions_action__pipelined_actions_value: 
 forall actions ac0 v0 (Heq: action2value ac0 = ret v0),
  action2value (pipelined_actions_action actions ac0) = 
    Some (pipelined_actions_value actions v0).
Proof.
  unfold pipelined_actions_action, pipelined_actions_value.
  induction actions; simpl; intros; auto.
    apply IHactions.
    apply action2value__subst_action_action__subst_action_value; auto.
Qed.

Lemma pipelined_actions__composed_actions_Some_elim: forall 
  (actions : list (id * action)) (id5 : id) (ac : action)
  (Hfind : ListMap.find id5 (pipelined_actions__composed_actions actions) =
             ret ac),
  exists actions1 : list (id * action),
    exists ac5 : action,
      exists actions2 : list (id * action),
        actions = actions1 ++ [(id5, ac5)] ++ actions2 /\
        ac = pipelined_actions_action actions2 ac5 /\
        id5 `notin` dom actions1.
Proof.
  unfold ListMap.find.
  induction actions as [|[id0 ac0] actions]; simpl in *; intros.
    congruence.
    
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id5 id0); subst.
      uniq_result.
      exists nil. exists ac0. exists actions.
      split; auto.

      apply IHactions in Hfind.
      destruct Hfind as [actions1 [ac5 [actions2 [EQ1 [EQ2 Hnotin]]]]]; subst.
      exists ((id0, ac0)::actions1). exists ac5. exists actions2.
      simpl_env.
      split; auto.
Qed.

Lemma pipelined_actions_value__action2value__commute: forall (id5 : id)
  (actions2 : list (id * action)) (ac5 : action) 
  (Hnotin: id5 `notin` dom actions2),
  pipelined_actions_value actions2
    match action2value ac5 with
    | ret v1 => v1
    | merror => value_id id5
    end =
  match action2value (pipelined_actions_action actions2 ac5) with
  | ret v1 => v1
  | merror => value_id id5
  end.
Proof.
  induction actions2 as [|[id0 ac0] actions2]; simpl; intros; auto.
    rewrite <- IHactions2; auto.
    f_equal.
    clear IHactions2.
    destruct ac0; simpl; auto.
      destruct ac5; simpl; auto.
        destruct_if; auto.
          contradict Hnotin; simpl; auto.
      destruct ac5; simpl; auto.
        destruct_if; auto.
          contradict Hnotin; simpl; auto.
Qed.

Lemma pipelined_actions_value_middle: forall (id5 : id) 
  (actions1 : list (id * action)) (ac5 : action) (actions2 : list (id * action))
  (Hnotin : id5 `notin` dom actions1)
  (Huniq : uniq (actions1 ++ [(id5, ac5)] ++ actions2)),
  pipelined_actions_value (actions1 ++ [(id5, ac5)] ++ actions2)
    (value_id id5) =
  match action2value (pipelined_actions_action actions2 ac5) with
  | ret v1 => v1
  | merror => value_id id5
  end.
Proof.
  intros.
  induction actions1 as [|[id0 ac0] actions1]; simpl.
    destruct_if; try congruence.
      inv Huniq.
      apply pipelined_actions_value__action2value__commute; auto.

    destruct_if.
      contradict Hnotin; simpl; auto.
    
      inv Huniq.
      rewrite <- IHactions1; auto.
        destruct (action2value ac0); auto.
Qed.

Lemma pipelined_actions__composed_actions_None_elim: forall 
  (id5 : id) (actions : list (atom * action)) (Huniq : uniq actions)
  (H: ListMap.find id5 (pipelined_actions__composed_actions actions) = None),
  pipelined_actions_value actions (value_id id5) = value_id id5.
Proof.
  induction actions as [|[id0 ac0] actions]; simpl; intros; auto.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id5 id0); subst;
      try (destruct_if; try congruence).
    inv Huniq.
    destruct (action2value ac0); auto.
Qed.

Lemma pipelined_actions_value__const: forall const5 actions,
  pipelined_actions_value actions (value_const const5) = value_const const5.
Proof.
  induction actions as [|[id0 ac0] actions]; simpl; intros; auto.
    destruct (action2value ac0); auto.
Qed.

Lemma action2value_None__pipelined_actions_action: forall ac0
  (Hneq : action2value ac0 = None) actions,
  pipelined_actions_action actions ac0 = AC_remove.
Proof.
  intros.
  destruct ac0; tinv Hneq.
  induction actions as [|[? ac] actions]; simpl; auto.
    destruct (action2value ac); auto.
Qed.

Lemma pipelined_actions__composed_actions__dom: forall actions,
  dom (pipelined_actions__composed_actions actions) [=] dom actions.
Proof.
  induction actions as [|[] actions]; simpl; fsetdec.
Qed.

(***************************************************************)

Lemma list_composed_substs_value__commute: forall actions (Huniq : uniq actions)
  id0 v0 ac0 (Heq : action2value ac0 = ret v0) v,
  ListComposedPass.substs_value
    ((id0, pipelined_actions_action actions ac0)
     :: pipelined_actions__composed_actions actions) v =
  ListComposedPass.substs_value
    (pipelined_actions__composed_actions actions) 
    (v {[v0 // id0]}).
Proof.
  intros.
  destruct v as [id1|]; simpl; auto.
  destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); subst;
    try (destruct_if; try congruence).
  erewrite action2value__pipelined_actions_action__pipelined_actions_value; 
    eauto.
  clear - Huniq.
  destruct v0 as [id5|]; simpl.
  Case "1".
    case_eq (ListMap.find id5 (pipelined_actions__composed_actions actions)).
    SCase "1.1".
      intros a Hfind.
      assert (exists actions1, exists ac5, exists actions2,
                actions = actions1 ++ [(id5, ac5)] ++ actions2 /\
                a = pipelined_actions_action actions2 ac5 /\
                id5 `notin` dom actions1) as J.
        apply pipelined_actions__composed_actions_Some_elim; auto.  
      destruct J as [actions1 [ac5 [actions2 [EQ1 [EQ2 Hnotin]]]]]; subst.
      apply pipelined_actions_value_middle; auto.
    SCase "1.2".   
      apply pipelined_actions__composed_actions_None_elim; auto.
  Case "2".    
    apply pipelined_actions_value__const.
Qed.

Lemma list_composed_substs_list_value_l__commute: forall actions 
  (Huniq : uniq actions) (id0 : id) (v0 : value) (ac0 : action)
  (Heq : action2value ac0 = ret v0) l0,
  ListComposedPass.substs_list_value_l
    ((id0, pipelined_actions_action actions ac0)
     :: pipelined_actions__composed_actions actions) l0 =
  ListComposedPass.substs_list_value_l
    (pipelined_actions__composed_actions actions)
    (subst_list_value_l id0 v0 l0).
Proof.
  induction l0 as [|[] l1]; simpl; auto.
    f_equal; auto.
    f_equal.
    apply list_composed_substs_value__commute; auto.
Qed.

Lemma list_composed_substs_phis__commute: forall actions (Huniq: uniq actions) 
  id0 v0 ac0 (Heq : action2value ac0 = ret v0) ps,
  List.map
    (ListComposedPass.substs_phi
       ((id0, pipelined_actions_action actions ac0)
        :: pipelined_actions__composed_actions actions)) ps =
    List.map
       (ListComposedPass.substs_phi
          (pipelined_actions__composed_actions actions))
       (List.map (subst_phi id0 v0) ps).
Proof.
  induction ps as [|p ps]; simpl; intros; auto.
    f_equal; auto.
    clear - Huniq Heq.
    destruct p. simpl.
    f_equal.
    apply list_composed_substs_list_value_l__commute; auto.
Qed.

Lemma list_composed_substs_list_value__commute: forall actions 
  (Huniq: uniq actions) id0 v0 ac0 (Heq : action2value ac0 = ret v0) l0,
  ListComposedPass.substs_list_value
     ((id0, pipelined_actions_action actions ac0)
      :: pipelined_actions__composed_actions actions) l0 =
   ListComposedPass.substs_list_value
     (pipelined_actions__composed_actions actions)
     (subst_list_value id0 v0 l0).
Proof.
  induction l0 as [|[] l0]; simpl; intros; auto.
    f_equal; auto.
    clear - Huniq Heq.
    f_equal.
    apply list_composed_substs_value__commute; auto.
Qed.

Lemma list_composed_substs_params__commute: forall actions
  (Huniq : uniq actions) id0 v0 ac0 (Heq : action2value ac0 = ret v0)
  (params5 : params),
  List.map
     (fun p : typ * attributes * value =>
      let '(t, v) := p in
           (t,
           ListComposedPass.substs_value
             ((id0, pipelined_actions_action actions ac0)
              :: pipelined_actions__composed_actions actions) v)) params5 =
  List.map
     (fun p : typ * attributes * value =>
      let '(t, v) := p in
           (t,
           ListComposedPass.substs_value
             (pipelined_actions__composed_actions actions) v))
     (List.map
        (fun p : typ * attributes * value =>
         let '(t, v) := p in (t, v {[v0 // id0]})) params5).
Proof.
  induction params5 as [|[[]] params5]; simpl; intros; auto.
    f_equal; auto.
    clear - Huniq Heq.
    f_equal.
    apply list_composed_substs_value__commute; auto.
Qed.

Lemma list_composed_substs_cmds__commute: forall actions (Huniq: uniq actions) 
  id0 v0 ac0 (Heq : action2value ac0 = ret v0) cs,
  List.map
    (ListComposedPass.substs_cmd
       ((id0, pipelined_actions_action actions ac0)
        :: pipelined_actions__composed_actions actions)) cs =
    List.map
       (ListComposedPass.substs_cmd
          (pipelined_actions__composed_actions actions))
       (List.map (subst_cmd id0 v0) cs).
Proof.
  induction cs as [|c cs]; simpl; intros; auto.
    f_equal; auto.
    clear - Huniq Heq.
    destruct c; simpl; f_equal; try solve [
      apply list_composed_substs_value__commute; auto |
      apply list_composed_substs_list_value__commute; auto |
      apply list_composed_substs_params__commute; auto
    ].
Qed.

Lemma list_composed_substs_tmn__commute: forall actions (Huniq: uniq actions) 
  id0 v0 ac0 (Heq : action2value ac0 = ret v0) tmn,
  ListComposedPass.substs_tmn
    ((id0, pipelined_actions_action actions ac0)
     :: pipelined_actions__composed_actions actions) tmn =
  ListComposedPass.substs_tmn (pipelined_actions__composed_actions actions)
    (subst_tmn id0 v0 tmn).
Proof.
  destruct tmn; simpl; f_equal; try solve 
    [apply list_composed_substs_value__commute; auto].
Qed.

Lemma list_composed_substs_blocks__commute: forall actions (Huniq: uniq actions) 
  id0 v0 ac0 (Heq : action2value ac0 = ret v0) bs,
  List.map
   (ListComposedPass.substs_block
      ((id0, pipelined_actions_action actions ac0)
       :: pipelined_actions__composed_actions actions)) bs =
  List.map
    (ListComposedPass.substs_block
       (pipelined_actions__composed_actions actions))
    (List.map (subst_block id0 v0) bs).
Proof.
  induction bs as [|[l1 ps1 cs1 tmn1] bs]; simpl; intros; auto.
    f_equal; auto.
    f_equal; auto.
      apply list_composed_substs_phis__commute; auto.
      apply list_composed_substs_cmds__commute; auto.
      apply list_composed_substs_tmn__commute; auto.
Qed.

Lemma list_composed_substs__commute: forall actions (Huniq: uniq actions)  
  id0 ac0 f (Hnotin: id0 `notin` dom actions),
  ListComposedPass.substs_fdef
     ((id0, pipelined_actions_action actions ac0)
      :: pipelined_actions__composed_actions actions) f =
   ListComposedPass.substs_fdef (pipelined_actions__composed_actions actions)
     (apply_subst_action f (id0, ac0)).
Proof.
  intros.
  destruct f as [fh bs]. simpl.
  case_eq (action2value ac0).
    intros v0 Heq.
    simpl.
    f_equal.
    apply list_composed_substs_blocks__commute; auto.

    intros Hneq.
    simpl.
    f_equal.    
    rewrite action2value_None__pipelined_actions_action; auto.
    apply list_composed_substs_blocks_doesnt_use_AC_remove; auto.
      rewrite pipelined_actions__composed_actions__dom; auto.
Qed.

Lemma list_composed_substs__list_pipelined_substs: forall actions 
  (Huniq: uniq actions) f,
  ListComposedPass.substs_fdef (pipelined_actions__composed_actions actions) f 
    = ListMap.fold apply_subst_action actions f.
Proof.
  induction actions as [|ac actions]; simpl; intros.
  Case "base".
    destruct f; simpl; f_equal; auto using list_composed_substs_blocks_nil.
  Case "ind".
    inv Huniq.
    rewrite <- IHactions; auto.
    apply list_composed_substs__commute; auto.
Qed.

(***************************************************************)

Definition avl_actions__iff_mapsto__list_actions 
  A (actions1:AVLMap.t A) (actions2:ListMap.t A): Prop :=
forall id0 ac0, 
  AVLMap.AtomFMapAVL.MapsTo id0 ac0 actions1 <-> 
    lookupAL _ actions2 id0 = Some ac0.

Implicit Arguments avl_actions__iff_mapsto__list_actions [A].

Lemma avl_substs_fdef__iff_mapsto__list_substs_fdef: forall actions2 actions1 f
  (Hiff: avl_actions__iff_mapsto__list_actions actions1 actions2),
  AVLComposedPass.substs_fdef actions1 f = 
    ListComposedPass.substs_fdef actions2 f.
Admitted.

(***************************************************************)

Lemma avl_compose_actions__iff_mapsto__list_compose_actions: forall actions,
  avl_actions__iff_mapsto__list_actions
     (AVLComposedPass.compose_actions actions)
     (ListComposedPass.compose_actions actions).
Admitted.

(***************************************************************)

Lemma acl_compose_actions__list_compose_actions: forall actions f,
  AVLComposedPass.substs_fdef (AVLComposedPass.compose_actions actions) f =
    ListComposedPass.substs_fdef (ListComposedPass.compose_actions actions) f.
Proof.
  intros.
  apply avl_substs_fdef__iff_mapsto__list_substs_fdef.
  apply avl_compose_actions__iff_mapsto__list_compose_actions.
Qed.

(***************************************************************)

Require Import Paths.

Section ActionGraph.

Variable actions: AssocList action.

Definition avertexes : V_set :=
fun (v:Vertex) => 
  let '(index n) := v in 
  n `in` dom actions \/ exists id0, In (id0, AC_vsubst (value_id n)) actions.

Definition aarcs : A_set :=
fun (arc:Arc) =>
  let '(A_ends (index n2) (index n1)) := arc in
  In (n2, AC_vsubst (value_id n1)) actions. 

Definition acyclic_actions : Prop :=
  forall x y vl al p,
    Cycle avertexes aarcs x y vl al p -> vl = V_nil.

End ActionGraph.

Lemma list_substs_actions__acyclic : forall actions 
  (Hacyclic: acyclic_actions actions),
  acyclic_actions (substs_actions actions).
Admitted.

Lemma pipelined_actions__composed_actions__acyclic : forall actions 
  (Hacyclic: acyclic_actions actions),
  acyclic_actions (pipelined_actions__composed_actions actions).
Admitted.

Lemma list_compose_actions__acyclic : forall actions 
  (Hacyclic: acyclic_actions actions),
  acyclic_actions (ListComposedPass.compose_actions actions).
Admitted.

Lemma acyclic_actions_cons_inv: forall id0 ac0 actions
  (Hacyclic: acyclic_actions ((id0, ac0) :: actions)),
  acyclic_actions actions.
Admitted.

Lemma list_subst_actions_app: forall id0 ac0 actions2 actions1,
  ListComposedPass.subst_actions id0 ac0 (actions1++actions2) = 
    ListComposedPass.subst_actions id0 ac0 actions1++
      ListComposedPass.subst_actions id0 ac0 actions2.
Proof.
  unfold ListComposedPass.subst_actions.
  intros.
  destruct (action2value ac0); auto.
  apply map_app.
Qed.

Lemma list_subst_actions_Some_cons: forall id0 ac0 v0 id1 ac1 actions
  (Heq: action2value ac0 = Some v0),
  ListComposedPass.subst_actions id0 ac0 ((id1, ac1)::actions) = 
    (id1, subst_action id0 v0 ac1)::
      ListComposedPass.subst_actions id0 (AC_vsubst v0) actions.
Proof.
  unfold ListComposedPass.subst_actions.
  intros. rewrite Heq. auto.
Qed.

Lemma list_subst_actions_None_cons: forall id0 ac0 actions
  (Heq: action2value ac0 = None),
  ListComposedPass.subst_actions id0 ac0 actions = actions.
Proof.
  unfold ListComposedPass.subst_actions.
  intros. rewrite Heq. auto.
Qed.

Inductive segment (id0:id) (v0:value) : list (id*action) -> Prop :=
| seqment_base: segment id0 v0 [(id0, AC_vsubst v0)]
| seqment_int: forall id1 ac1 actions 
    (Hneq: id1 <> id0) (Hseg: segment id0 v0 actions),
    segment id0 v0 ((id1,ac1)::actions)
.

Inductive segments (v:value) : list id -> list (id*action) -> Prop := 
| segments_hd: forall id0 actions1 actions2 
    (Hseg: segment id0 v actions1),
    segments v (id0::nil) (actions1 ++ actions2)
| segments_cons: forall id0 id1 tl actions1 actions2
    (Hseg: segment id0 (value_id id1) actions1) 
    (Hsegs: segments v (id1::tl) actions2),
    segments v (id0::id1::tl) (actions1++actions2)
.

Lemma pipelined_actions_action_AC_vsubst_in: forall vid actions 
  (Hin: vid `in` dom actions),
  exists v, exists vids, 
    pipelined_actions_action actions (AC_vsubst (value_id vid)) = 
      AC_vsubst v /\ segments v (vid::vids) actions.
Admitted.

Lemma list_compose_actions__eq__list_composed_substs1: forall 
  id0 ac0 (actions : list (atom * action))
  (Hacyclic : acyclic_actions ((id0, ac0) :: actions))
  (Huniq : uniq actions) (Hnotin: id0 `notin` dom actions),
  ListComposedPass.find_parent_action ac0
    (pipelined_actions__composed_actions (substs_actions actions)) =
  pipelined_actions_action
    (ListComposedPass.subst_actions id0 ac0 (substs_actions actions)) ac0.
Admitted.
(*
Proof.
  intros.
  remember (ListComposedPass.substs_actions actions) as A.
  destruct ac0; simpl.
  Case "1". rewrite pipelined_actions_action_AC_remove; auto.
  Case "2". 
    destruct v; simpl.
    SCase "2.1". 
      case_eq (ListMap.find id5 (pipelined_actions__composed_actions A)).
      SSCase "2.1.1".
        intros ac Hfind.
        assert (J:=Hfind).
        apply pipelined_actions__composed_actions_Some_elim in J.
        destruct J as [actions1 [ac5 [actions2 [EQ1 [EQ2 Hnotint]]]]]; 
          subst ac.
        rewrite EQ1.
        rewrite list_subst_actions_app. simpl.
        erewrite list_subst_actions_Some_cons; simpl; eauto.
        rewrite pipelined_actions_action_tail;
          try solve [rewrite list_subst_actions__dom; auto].
        simpl.
        destruct_if; try congruence.
        destruct ac5; simpl.
        SSSCase "2.1.1.1". 
          rewrite pipelined_actions_action_AC_remove; auto.
          rewrite pipelined_actions_action_AC_vsubst_notin; auto.
            rewrite list_subst_actions__dom.
            apply list_substs_actions__uniq in Huniq.
            rewrite EQ1 in Huniq.
            destruct_uniq; auto.
        SSSCase "2.1.1.2".
          destruct v as [vid|]; simpl.
          SSSSCase "2.1.1.2.1". 
            destruct_if.
            SSSSSCase "2.1.1.2.1.1". admit. (*cyclic*)
            SSSSSCase "2.1.1.2.1.2". 
              destruct (AtomSetProperties.In_dec vid (dom actions2)) 
                as [Hin | Hnotin'].
              SSSSSSCase "in". 
                assert (J:=Hin).
                apply pipelined_actions_action_AC_vsubst_in in J.
                destruct J as [v [vids [G1 G2]]].
                rewrite G1.
                assert (J:=Hin).
                rewrite <- list_subst_actions__dom with (id0:=id0)
                  (ac0:=AC_vsubst (value_id id5)) in J.
                apply pipelined_actions_action_AC_vsubst_in in J.
                destruct J as [v' [vids' [G1' G2']]].
                rewrite G1'.
                admit. (*cyclic*)
              SSSSSSCase "notin". 
                rewrite pipelined_actions_action_AC_vsubst_notin; auto.
                rewrite pipelined_actions_action_AC_vsubst_notin; auto.
                  rewrite list_subst_actions__dom; auto.
          SSSSCase "2.1.1.2.2". 
            repeat rewrite pipelined_actions_action_AC_vsubst_const; auto.
        SSSCase "2.1.1.3". 
          repeat rewrite pipelined_actions_action_AC_vsubst_const; auto.
          rewrite pipelined_actions_action_AC_tsubst.
          admit. (* tvsubst = vundef *)
      SSCase "2.1.2". 
        intro Hfind.
        assert (J:=Hfind).
        apply pipelined_actions__composed_actions_None_elim in J;
          try solve [rewrite HeqA; apply list_substs_actions__uniq; auto].
        rewrite pipelined_actions_action_AC_vsubst_notin; auto.
          rewrite list_subst_actions__dom.
          apply lookupAL_None_notindom in Hfind.
          rewrite pipelined_actions__composed_actions__dom in Hfind; auto.
    SCase "2.2". repeat rewrite pipelined_actions_action_AC_vsubst_const; auto.
  Case "3".
    rewrite pipelined_actions_action_AC_tsubst; auto.
Qed.
*)

Lemma pipelined_actions_value_AC_vsubst__commute: forall actions v,
  AC_vsubst (pipelined_actions_value actions v) =
     pipelined_actions_action actions (AC_vsubst v).
Admitted.

Lemma list_composed_subst_actions_nil: forall id0 ac0,
  ListComposedPass.subst_actions id0 ac0 nil = nil.
Admitted.

Definition list_compose_actions__eq__list_composed_substs_prop' (n:nat) := 
  forall actions (Hlen: (length actions = n)%nat) id0 ac0,
  ListComposedPass.subst_actions id0
     (pipelined_actions_action (substs_actions actions) ac0)
     (pipelined_actions__composed_actions (substs_actions actions)) =
  pipelined_actions__composed_actions
     (substs_actions (ListComposedPass.subst_actions id0 ac0 actions)).

Lemma action2value__subst_action__subst_value: forall ac0 
  v0 (Heq: action2value ac0 = ret v0) id1 v1,
  action2value (subst_action id1 v1 ac0) = ret (subst_value id1 v1 v0).
Admitted.

Lemma substs_actions_cons: forall id0 ac0 actions,
  substs_actions ((id0,ac0)::actions) =
    (id0, ac0)::substs_actions (ListComposedPass.subst_actions id0 ac0 actions).
Admitted.

Lemma list_compose_actions__eq__list_composed_substs_aux': forall n,
  list_compose_actions__eq__list_composed_substs_prop' n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold list_compose_actions__eq__list_composed_substs_prop' in *; intros.
  destruct actions as [|[id1 ac1] actions].
    simpl.
    repeat rewrite list_composed_subst_actions_nil. simpl. auto.

    unfold_substs_actions. simpl.
    case_eq (action2value ac0).
Case "1".
    intros v0 Ha2v0.
    erewrite list_subst_actions_Some_cons at 1; eauto.
    case_eq (action2value ac1).
SCase "1.1".
      intros v1 Ha2v1.
      assert (Ha2v0':=Ha2v0).
      apply action2value__subst_action__subst_value 
        with (id1:=id1)(v1:=v1) in Ha2v0'.
      apply action2value__pipelined_actions_action__pipelined_actions_value
        with (actions:=substs_actions 
                (ListComposedPass.subst_actions id1 ac1 actions)) in Ha2v0'.
      erewrite list_subst_actions_Some_cons; eauto.
      rewrite substs_actions_cons. simpl.
      f_equal.
        f_equal.
        admit.

        erewrite <- Hrec; eauto; try solve [subst x; simpl; omega].
        rewrite <- Hrec with 
          (y:=length 
            (ListComposedPass.subst_actions id0 (AC_vsubst v0) actions));     
          auto; try solve [subst x; simpl; omega].
          admit.
          admit.

Admitted.

Lemma list_compose_actions__eq__list_composed_substs': forall actions id0 ac0,
  ListComposedPass.subst_actions id0
     (pipelined_actions_action (substs_actions actions) ac0)
     (pipelined_actions__composed_actions (substs_actions actions)) =
  pipelined_actions__composed_actions
     (substs_actions (ListComposedPass.subst_actions id0 ac0 actions)).
Proof.
  intros.
  assert (J:=@list_compose_actions__eq__list_composed_substs_aux' 
                (length actions)).
  unfold list_compose_actions__eq__list_composed_substs_prop' in J.
  auto.
Qed.

Definition list_compose_actions__eq__list_composed_substs_prop (n:nat) := 
  forall actions 
  (Hlen: (length actions = n)%nat) (Hacyclic: acyclic_actions actions) 
  (Huniq: uniq actions),
  ListComposedPass.compose_actions actions = 
    pipelined_actions__composed_actions (substs_actions actions).

Lemma list_compose_actions__eq__list_composed_substs_aux: forall n,
  list_compose_actions__eq__list_composed_substs_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold list_compose_actions__eq__list_composed_substs_prop in *; intros.
  destruct actions as [|[id0 ac0] actions].
    simpl; auto.

    unfold_substs_actions. simpl. unfold ListMap.add.
    assert (Hacyclic':=Hacyclic).
    apply acyclic_actions_cons_inv in Hacyclic'.
    inv Huniq.
    rewrite Hrec with (y:=length actions); auto.
    assert (pipelined_actions_action
              (substs_actions (ListComposedPass.subst_actions id0 ac0 actions)) 
                ac0 =
            pipelined_actions_action (substs_actions actions) ac0) as EQ.
      admit.
    rewrite EQ. clear EQ.
    assert (ListComposedPass.find_parent_action ac0
              (pipelined_actions__composed_actions
                 (substs_actions actions)) =
            pipelined_actions_action
              (substs_actions actions) ac0) as EQ.
      admit.
      (* apply list_compose_actions__eq__list_composed_substs1; auto. *)
    rewrite EQ. clear EQ.
    f_equal.
    apply list_compose_actions__eq__list_composed_substs'.
Qed.

Lemma list_compose_actions__eq__list_composed_substs: forall 
  actions (Hacyclic: acyclic_actions actions) (Huniq: uniq actions),
  ListComposedPass.compose_actions actions = 
    pipelined_actions__composed_actions (substs_actions actions).
Proof.
  intros.
  assert (J:=@list_compose_actions__eq__list_composed_substs_aux 
                (length actions)).
  unfold list_compose_actions__eq__list_composed_substs_prop in J.
  auto.
Qed.

Lemma list_compose_actions__list_composed_substs: forall actions 
  (Hacyclic: acyclic_actions actions) (Huniq: uniq actions) f,
  ListComposedPass.substs_fdef (ListComposedPass.compose_actions actions) f =
  composed_pipelined_actions actions f.
Proof.
  intros.
  rewrite list_compose_actions__eq__list_composed_substs; auto.
Qed.

(***************************************************************)

Lemma avl_substs_fdef__list_substs_fdef: forall actions (Huniq: uniq actions) 
  (Hacyclic: acyclic_actions actions) f,
  AVLComposedPass.substs_fdef (AVLComposedPass.compose_actions actions) f = 
    ListMap.fold apply_subst_action (substs_actions actions) f.
Proof.
  intros.
  rewrite <- list_composed_substs__list_pipelined_substs; 
    auto using list_substs_actions__uniq.
  fold (composed_pipelined_actions actions f).
  rewrite <- list_compose_actions__list_composed_substs; auto.
  rewrite <- acl_compose_actions__list_compose_actions; auto.
Qed.

(***************************************************************)

Lemma pipelined_elim_stld_sim_wfS_wfPI: forall fh bs1 f2 Ps1 Ps2 los nts main
  VarArgs pid rd (pinfo : PhiInfo) (actions : list (atom * action))
  (Heqactions : actions =
                 flat_map Datatypes.id
                   (List.map (find_stld_pairs_block pid) bs1))
  (Hpass : pipelined_actions actions (fdef_intro fh bs1) = f2)
  (Heq1 : PI_f pinfo = fdef_intro fh bs1) (Heq2 : PI_id pinfo = pid)
  (Heq0 : PI_rd pinfo = rd) (Hwfpi : WF_PhiInfo pinfo) S1 S2
  (Heq3 : S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq4 : S2 = [module_intro los nts
                 (Ps1 ++ product_fdef (fdef_intro fh bs1) :: Ps2)])
  (HwfS : wf_system S2) (Hok : defined_program S2 main VarArgs),
  (program_sim S1 S2 main VarArgs /\
    wf_system S1 /\ defined_program S1 main VarArgs) /\
   (exists pinfo' : PhiInfo, WF_PhiInfo pinfo' /\ keep_pinfo f2 pinfo pinfo').
Admitted.

Lemma find_stld_pairs_blocks_spec: forall pid bs actions
  (Hfind: actions = flat_map Datatypes.id 
                      (List.map (find_stld_pairs_block pid) bs)),
  uniq actions /\ acyclic_actions actions.
Admitted.

Ltac avl_to_list_tac :=
match goal with
| Hpass: AVLComposedPass.run _ _ = _ |- _ =>
  unfold AVLComposedPass.run in Hpass;
  rewrite AVLComposedPass.substs_removes_fdef__commute in Hpass;
  rewrite avl_substs_fdef__list_substs_fdef in Hpass; auto;
  rewrite avl_removes_fdef__list_removes_fdef in Hpass; auto;
  rewrite list_apply_remove_subst_action__list_apply_action in Hpass
end.

Ltac unfold_elim_stld_fdef_tac :=
match goal with
| Hpass: elim_stld_fdef ?pid ?f1 = _ |- _ =>
  let fh := fresh "fh" in
  let bs1 := fresh "bs1" in
  let actions := fresh "actions" in
  let Hwf := fresh "Hwf" in
  unfold elim_stld_fdef in Hpass;
  destruct f1 as [fh bs1];
  remember (flat_map Datatypes.id (List.map (find_stld_pairs_block pid) bs1))
    as actions;
  match goal with
  | Heqactions: actions = _ |- _ =>
    assert (Hwf:=Heqactions);
    apply find_stld_pairs_blocks_spec in Hwf;
    destruct Hwf
  end
end.

Lemma elim_stld_sim_wfS_wfPI: forall f1 f2 Ps1 Ps2 los nts main
  VarArgs pid rd (pinfo:PhiInfo)
  (Hpass: elim_stld_fdef pid f1 = f2)
  (Heq1: PI_f pinfo = f1) (Heq2: PI_id pinfo = pid) (Heq2: PI_rd pinfo = rd)
  (Hwfpi: WF_PhiInfo pinfo) S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  (program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs) /\
  exists pinfo', WF_PhiInfo pinfo' /\ keep_pinfo f2 pinfo pinfo'.
Proof.
  intros.
  unfold_elim_stld_fdef_tac.
  avl_to_list_tac.
  eapply pipelined_elim_stld_sim_wfS_wfPI; eauto.
Qed.

Lemma pipelined_elim_stld_reachablity_successors: forall pid fh bs1 f2 actions
  (Heqactions : actions =
                 flat_map Datatypes.id
                   (List.map (find_stld_pairs_block pid) bs1))
  (Hpass : pipelined_actions actions (fdef_intro fh bs1) = f2),
  reachablity_analysis f2 = reachablity_analysis (fdef_intro fh bs1) /\
    successors f2 = successors (fdef_intro fh bs1).
Admitted.

Lemma elim_stld_reachablity_successors: forall pid f1 f2
  (Hpass: elim_stld_fdef pid f1 = f2),
  reachablity_analysis f2 = reachablity_analysis f1 /\
    successors f2 = successors f1.
Proof.
  intros. 
  unfold_elim_stld_fdef_tac.
  avl_to_list_tac.
  eapply pipelined_elim_stld_reachablity_successors; eauto.
Qed.

Hint Unfold keep_pinfo.

Section Macro_mem2reg_fdef_sim_wfS.

Variable (Ps1 Ps2:products) (los:layouts) (nts:namedts) (main:id) 
         (VarArgs:list (GVsT DGVs)) (f1:fdef).

Definition Pmm2r' :=
  fun (f:fdef) =>
       (program_sim [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
         [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)] main VarArgs
       /\
       wf_system
         [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] /\
       defined_program 
         [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] main VarArgs) /\
       reachablity_analysis f1 = reachablity_analysis f /\
       successors f1 = successors f.

Definition Pmm2r :=
   fun (re:(fdef * list id)) => let '(f, _) := re in Pmm2r' f.

Lemma Pmm2r'_Pmm2r: forall f ds, Pmm2r' f -> Pmm2r (f, ds).
Proof. simpl. auto. Qed.

Lemma macro_mem2reg_fdef_sim_wfS: forall rd dones1 f2 dones2 
  (Hreach: ret rd = reachablity_analysis f1) S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs)
  (Hiter: SafePrimIter.iterate (fdef * list id)
            (macro_mem2reg_fdef_step rd (successors f1)
              (XATree.make_predecessors (successors f1)))
            (f1, dones1) = (f2, dones2)),
  (program_sim S1 S2 main VarArgs /\
   wf_system S1 /\ defined_program S1 main VarArgs) /\
  reachablity_analysis f1 = reachablity_analysis f2 /\
  successors f1 = successors f2.
Proof.
  intros. subst.
  assert (Pmm2r (f1, dones1)) as HPf1.
    unfold Pmm2r. split; auto using program_sim_refl.
  apply SafePrimIter.iterate_prop with (P:=Pmm2r) in Hiter; auto.
    unfold macro_mem2reg_fdef_step.
    intros a HPa.
    destruct a as [f dones].
    unfold macro_mem2reg_fdef_iter.
    remember (getEntryBlock f) as R.
    destruct R as [[l0 ps0 cs0 tmn0]|]; auto.
    remember (mem2reg.find_promotable_alloca f cs0 dones) as R.
    destruct R as [[[[pid ty] num] al]|]; auto.
    set (pinfo:=mkPhiInfo f rd pid ty num al).
 
    assert (HPa':=HPa).
    destruct HPa as [HPa [EQ2 EQ1]].
    rewrite EQ2 in Hreach.
    assert (WF_PhiInfo pinfo) as HwfPI.
      eapply find_promotable_alloca__WF_PhiInfo; eauto.

    apply Pmm2r'_Pmm2r.
    set (Pmm2r'' := 
           fun f => Pmm2r' f /\
           exists pinfo', WF_PhiInfo pinfo' /\ keep_pinfo f pinfo pinfo').
    repeat (rewrite seq_trans_assoc).
    apply seq_trans_pres_strengthen_P with (Pcom':=Pmm2r''); auto.
    assert (Pmm2r'' f) as HPa''. 
      split; auto.
        instantiate_pinfo.
    compass_tac.
    Case "1".
    split.
      split.
      SCase "1.1".
        apply program_sim_wfS_trans with (P2:=
                [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]); auto.
        intros.
        rewrite EQ1.
        split.
          eapply phinodes_placement_sim; eauto.
        split.
          eapply phinodes_placement_wfS; eauto.
          eapply program_sim__preserves__defined_program; 
             eauto using phinodes_placement_sim. 
    
      SCase "1.2".
        rewrite EQ1. rewrite EQ2.
        rewrite <- phinodes_placement_reachablity_analysis.
        rewrite <- phinodes_placement_successors. auto.
    
      SCase "1.3".
        destruct HPa as [HPa1 [HPa2 HPa3]].
        eapply phinodes_placement_wfPI in Hreach; eauto.
        rewrite EQ1. 
        match goal with
        | _: WF_PhiInfo 
              {| PI_f := ?f; PI_rd := ?rd; PI_id := ?pid;
                 PI_typ := ?ty; PI_num := ?num; PI_align := ?al |} |-
            exists _ : _, WF_PhiInfo _ /\ keep_pinfo ?f _ _ =>
            exists {| PI_f := f; PI_rd := rd; PI_id := pid;
                    PI_typ := ty; PI_num := num; PI_align := al |};
            repeat (split; auto)
        end.
    
    Case "2".
    destruct HPf as [[HPf21 HPf22] HPf23].
    split.
      split.
      SCase "2.1".
        apply program_sim_wfS_trans with (P2:=
                [module_intro los nts (Ps1 ++
                  product_fdef
                     (mem2reg.phinodes_placement rd pid ty al (successors f1)
                       (XATree.make_predecessors (successors f1)) f) :: Ps2)]); 
          auto; intros.
        SSCase "2.1.1".
          eapply elim_stld_sim_wfS_wfPI with
                (pinfo:=mkPhiInfo (mem2reg.phinodes_placement rd pid ty al
                  (successors f1) (XATree.make_predecessors (successors f1)) f)
                    rd pid ty num al); eauto. 
            rewrite EQ1. destruct HPa as [Hpa1 [Hpa2 Hpa3]].
            eapply phinodes_placement_wfPI; eauto.
    
      SCase "2.2".
        match goal with
        | |- context [elim_stld_fdef ?pid ?f] =>
          destruct (elim_stld_reachablity_successors pid f 
                      (elim_stld_fdef pid f)); auto
        end.
        destruct HPf22.
        split; etransitivity; eauto.
    
      SCase "2.3".
        apply change_keep_pinfo with (pinfo1:=
                   (update_pinfo pinfo
                     (mem2reg.phinodes_placement rd pid ty al (successors f)
                       (XATree.make_predecessors (successors f)) f))); auto.
        destruct HPa as [HPa1 [HPa2 HPa3]].
        eapply elim_stld_sim_wfS_wfPI; eauto.
          simpl. rewrite EQ1. auto.
          eapply phinodes_placement_wfPI; eauto.
          rewrite EQ1. simpl. eapply phinodes_placement_wfS; eauto.
          eapply program_sim__preserves__defined_program; eauto.
            rewrite EQ1. simpl.
            eapply phinodes_placement_sim; eauto.
    
    Case "3".
    match goal with
    | _: load_in_fdef _ ?f = _ |- _ => remember f as f0'
    end.
  
    destruct HPf as [[HPf10 HPf20] [pinfo' [HwfPIf0 Hkeep]]].
    
    split.
      split.   
      SCase "3.1".
        apply program_sim_wfS_trans with (P2:=
                 [module_intro los nts (Ps1 ++ product_fdef f0' :: Ps2)]); auto.
        intros.
        split. eapply dse_sim with (pinfo:=pinfo'); eauto 1; solve_keep_pinfo.
        split. eapply dse_wfS with (pinfo:=pinfo'); eauto 1; solve_keep_pinfo.
               eapply program_sim__preserves__defined_program; eauto.
                 eapply dse_sim with (pinfo:=pinfo'); eauto 1; solve_keep_pinfo.
      SCase "3.2".
        destruct HPf20 as [J1 J2].
        split; etransitivity; eauto.
          apply elim_dead_st_fdef_reachablity_analysis.
          apply elim_dead_st_fdef_successors.
    
      SCase "3.3".
        destruct HPf10 as [? [? ?]].
        exists (update_pinfo pinfo' (mem2reg.elim_dead_st_fdef pid f0')).
        split.
          eapply dse_wfPI; eauto 1; solve_keep_pinfo.
          solve_keep_pinfo.
    
    Case "4".
      intros [HPf2 [pinfo' [HwfPIf2 Hkeep]]].
      apply cond_trans_pres_P; try solve [compass_tac | auto].
      intros Hfalse.
      match goal with
      | _: used_in_fdef _ ?f = _ |- _ => remember f as f0'
      end.
      destruct HPf2 as [HPf12 HPf22].
      split.   
      SCase "4.1".
        apply program_sim_wfS_trans with (P2:=
                     [module_intro los nts
                       (Ps1 ++ product_fdef f0' :: Ps2)]); auto.
          intros.
          assert (f0' = PI_f pinfo') as EQ3. solve_keep_pinfo.
          assert (pid = PI_id pinfo') as EQ4. solve_keep_pinfo.
          rewrite EQ3, EQ4 in Hfalse.
          split.
            eapply dae_sim with (pinfo:=pinfo'); eauto 1.
          split.
            eapply dae_wfS with (pinfo:=pinfo'); eauto 1.
            eapply program_sim__preserves__defined_program; eauto.
              eapply dae_sim with (pinfo:=pinfo'); eauto 1.
      SCase "4.2".
        destruct HPf22 as [Hreach' Hsucc'].
        split; etransitivity; eauto.
          apply remove_reachablity_analysis; auto.
          apply remove_successors; auto.
Qed.

End Macro_mem2reg_fdef_sim_wfS.

Lemma elimphi_sim_wfS: forall f Ps1 Ps2 los nts main VarArgs
  S1 S2 (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs) rd
  (Hrd: reachablity_analysis f = Some rd)
  (Heq1: S1 = [module_intro los nts 
      (Ps1 ++ product_fdef (SafePrimIter.iterate _ elim_phi_step f) :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.
Admitted.

Lemma mem2reg_fdef_sim_wfS: forall (main : id) (VarArgs : list (GVsT DGVs))
  (los : layouts) (nts : namedts) (f : fdef) (Ps2 Ps1 : products) S1 S2
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef (mem2reg_fdef f) :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.
Proof.
  intros. subst.
  unfold mem2reg_fdef.
  remember (getEntryBlock f) as b. 
  destruct b as [[root ps cs tmn]|]; auto using program_sim_refl.
  remember (reachablity_analysis f) as R.
  destruct R as [rd|]; auto using program_sim_refl.
  destruct (print_reachablity rd).
  Case "1".
    remember (SafePrimIter.iterate (fdef * list id)
                     (macro_mem2reg_fdef_step rd 
                        (successors f)
                        (XATree.make_predecessors 
                          (successors f))) 
                     (f, nil)) as R.
    destruct R as [f1 dones]; auto using program_sim_refl.
    destruct (mem2reg.does_phi_elim tt).
    SCase "1.1".
      apply program_sim_wfS_trans with (P2:=
        [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]); auto; intros.
      SSCase "1.1.1".
        eapply elimphi_sim_wfS with (f:=f1)(rd:=rd); eauto.
          eapply macro_mem2reg_fdef_sim_wfS with (f1:=f) in HwfS; eauto.
          destruct HwfS as [_ [Hreach _]]. congruence.
      SSCase "1.1.2".
        eapply macro_mem2reg_fdef_sim_wfS with (f1:=f); eauto.
    SCase "1.2".
      eapply macro_mem2reg_fdef_sim_wfS with (f1:=f); eauto.      
  Case "2".
    split; auto using program_sim_refl.
Qed.

Lemma mem2reg_run_sim_wfS_aux: forall (main : id) (VarArgs : list (GVsT DGVs))
  (los : layouts) (nts : namedts) (Ps2 Ps1: products) S1 S2
  (HwfS : wf_system S2)
  (Hok: defined_program S2 main VarArgs)
  (Heq2: S2 = [module_intro los nts (Ps1++Ps2)])
  (Heq1: S1 = 
    [module_intro los nts
      (Ps1 ++ List.map
        (fun p : product =>
          match p with
          | product_fdef f => product_fdef (mem2reg_fdef f)
          | _ => p
          end) Ps2)]),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\ 
    defined_program S1 main VarArgs.
Proof.
  induction Ps2; simpl; intros; subst.
    split; auto using program_sim_refl.

    assert (J:=@IHPs2 (Ps1 ++ [a])). clear IHPs2.
    simpl_env in J. simpl in J.
    destruct a as [?|f|f]; auto.
    apply program_sim_wfS_trans with (P2:=
      [module_intro los nts
        (Ps1 ++ product_fdef f ::
           List.map (fun p : product =>
                     match p with
                     | product_fdef f => product_fdef (mem2reg_fdef f)
                     | _ => p
                     end) Ps2)]); auto; intros.
    eapply mem2reg_fdef_sim_wfS; eauto.
Qed.

Lemma mem2reg_run_sim_wfS: forall (m:module) (main:id) (VarArgs:list (GVsT DGVs))
  (HwfS : wf_system [m]) (Hok: defined_program [m] main VarArgs),
  program_sim [mem2reg_opt.run m] [m] main VarArgs /\ wf_system [mem2reg_opt.run m] /\
    defined_program [mem2reg_opt.run m] main VarArgs.
Proof.
  destruct m as [los nts Ps].
  unfold mem2reg_opt.run.
  intros.
  assert (J:=@mem2reg_run_sim_wfS_aux main VarArgs los nts Ps nil).
  auto.
Qed.



