Require Import vellvm.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Dipaths.
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
Require Import die_top.
Require Import die_wfS.
Require Import sas_top.
Require Import sas_wfS.
Require Import las_top.
Require Import laa_top.
Require Import las_wfS.
Require Import laa_wfS.
Require Import phiplacement_bsim_wfS.
Require Import phiplacement_bsim_top.
Require Import iter_pass.
Require Import iter_pass_correct.
Require Import pass_combinators.
Require Import phielim_spec.
Require Import phielim_top.
Require Import vmem2reg.
Require Import vmem2reg_correct.
Require Import vmem2reg_opt.
Require Import vmem2reg_opt_compose_props.
Require Import vmem2reg_opt_substs_eq.

(***************************************************************)
(* Remove the definition of elt from f *)
Definition apply_remove_action (f:fdef) (elt:id * action): fdef :=
let '(id1, ac1) := elt in remove_fdef id1 f.

(* Substitute the definition of elt in f *)
Definition apply_subst_action (f:fdef) (elt:id * action): fdef :=
let '(id1, ac1) := elt in
match action2value ac1 with
| Some v1 => subst_fdef id1 v1 f
| _ => f
end.

(***************************************************************)
(* apply_remove_action and apply_subst_action are commutable. *)
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

(***************************************************************)
(* composing apply_remove_action and apply_subst_action equals to 
   applying the list of actions. *)
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
(* Properties of filters. *)
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
(* Properties of ListComposedPass.removes_xxx *)
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
  induction bs as [|[l1 [ps1 cs1 tmn1]] bs]; simpl; auto.
    repeat (f_equal; auto).
    apply list_composed_removes_phis__empty; auto.
    apply list_composed_removes_cmds__empty; auto.
Qed.

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
  induction bs as [|[l1 [ps1 cs1 tmn1]] bs]; simpl; auto.
    f_equal; auto.
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
(* More AVL map facts. *)
Lemma AVLFacts_in_find_some: forall (elt : Type) (m : AtomFMapAVL.t elt)
  (x : AtomFMapAVL.key) (Hin: AtomFMapAVL.In (elt:=elt) x m),
  exists e, AtomFMapAVL.find (elt:=elt) x m = Some e.
Proof.
  intros.
  apply AVLFacts.in_find_iff in Hin.
  case_eq (AtomFMapAVL.find (elt:=elt) x m); try congruence; eauto.
Qed.

Lemma AVLFacts_find_some_in: forall (elt : Type) (m : AtomFMapAVL.t elt)
  (x : AtomFMapAVL.key) e
  (Hfind: AtomFMapAVL.find (elt:=elt) x m = Some e),
  AtomFMapAVL.In (elt:=elt) x m.
Proof.
  intros. apply AVLFacts.in_find_iff. congruence.
Qed.

(***************************************************************)
(* Substituting actions does not change definitions to remove. *)
Lemma avl_subst_actions__remove_spec: forall id0 id1 ac1 actions,
  AtomFMapAVL.MapsTo id0 AC_remove actions <-> 
    AtomFMapAVL.MapsTo id0 AC_remove 
      (AVLComposedPass.subst_actions id1 ac1 actions).
Proof.
  unfold AVLComposedPass.subst_actions.
  intros.
  destruct (action2value ac1); try tauto.
  split; intro J.
    change AC_remove with (subst_action id1 v AC_remove); auto.
    apply AtomFMapAVL.map_1; auto.
 
    apply AVLFacts.map_mapsto_iff in J.
    destruct J as [[] [J1 J2]]; inv J1; auto.
Qed.

Lemma avl_compose_actions__remove_spec: forall id0 actions (Huniq: uniq actions),
  In (id0, AC_remove) actions <-> 
    AtomFMapAVL.MapsTo id0 AC_remove 
      (AVLComposedPass.compose_actions actions).
Proof.
  induction 1; simpl.
  Case "base".
    split; try tauto.
      intros H.
      contradict H.
      apply AtomFMapAVL.is_empty_2; auto.
  Case "ind".
    split; intro J.
    SCase "ind1".
      destruct J as [J | J].
        uniq_result.
        apply AtomFMapAVL.add_1; auto.

        assert (x <> id0) as Hneq. 
          intro EQ; subst.
          apply binds_dom_contradiction in J; auto.
        apply AtomFMapAVL.add_2; auto.
        apply IHHuniq in J.
        apply avl_subst_actions__remove_spec; auto.
    SCase "ind2".
      apply AVLFacts.add_mapsto_iff in J.
      destruct J as [[J1 J2] | [J1 J2]]; subst.
        apply AVLComposedPass.find_parent_action_inv in J2.
        destruct J2 as [[J2 _]| [id1 [J21 [J22 J23]]]]; subst; auto.
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

Definition substs_actions__remove_spec_prop (n:nat) := forall id0 actions
  (Hlen: (length actions = n)%nat),
  In (id0, AC_remove) actions <-> 
    In (id0, AC_remove) (substs_actions actions).

Lemma substs_actions__remove_spec_aux: forall n,
  substs_actions__remove_spec_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold substs_actions__remove_spec_prop in *; intros.
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

Lemma substs_actions__remove_spec: forall id0 actions,
  In (id0, AC_remove) actions <-> 
    In (id0, AC_remove) (substs_actions actions).
Proof.
 intros.
  assert (J:=@substs_actions__remove_spec_aux (length actions)).
  unfold substs_actions__remove_spec_prop in J.
  auto.
Qed.

(***************************************************************)
(* Substituting actions does not change definitions to substitute. *)
Lemma avl_subst_actions__in_spec: forall id0 id1 ac1 actions,
  AtomFMapAVL.In id0 (AVLComposedPass.subst_actions id1 ac1 actions) <->
    AtomFMapAVL.In id0 actions.
Proof.
  unfold AVLComposedPass.subst_actions.
  intros.
  destruct (action2value ac1); try tauto.
  apply AVLFacts.map_in_iff.
Qed.

Lemma avl_compose_actions__in_spec: forall id0 actions (Huniq: uniq actions),
  AtomFMapAVL.In id0 (AVLComposedPass.compose_actions actions) <->
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

Lemma substs_actions__in_spec: forall id0 actions,
  id0 `in` dom actions <-> id0 `in` dom (substs_actions actions).
Proof.
  intros.
  rewrite substs_actions__dom; auto.
  fsetdec.
Qed.

(***************************************************************)
(* AVL-based removal equals list-based removal. *)
Definition avl_actions__iff_dom__list_actions 
  A (actions1:AVLMap.t A) (actions2:ListMap.t A): Prop :=
forall id0, 
  AtomFMapAVL.In id0 actions1 <-> id0 `in` dom actions2.

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
    case_eq (AtomFMapAVL.find 
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
    case_eq (AtomFMapAVL.find 
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
  induction bs as [|[l1 [ps1 cs1 tmn1]] bs]; simpl; auto.
    f_equal; auto.
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
    auto using substs_actions__uniq.
  unfold avl_actions__iff_dom__list_actions.
  intros.
  assert (J:=@substs_actions__in_spec id0 actions).
  assert (J':=@avl_compose_actions__in_spec id0 actions Huniq).
  tauto.
Qed.

(***************************************************************)
(* Properties of ListComposedPass.substs_xxx nil *)
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
  induction bs as [|[l1 [ps1 cs1 tmn1]] bs]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
    f_equal; auto.
      apply list_composed_substs_phis_nil; auto.
      apply list_composed_substs_cmds_nil; auto.
      apply list_composed_substs_tmn_nil; auto.
Qed.

(***************************************************************)
(* Actions to remove do not affect substitution. *)
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
  induction bs as [|[l1 [ps1 cs1 tmn1]] bs]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
    f_equal; auto.
      apply list_composed_substs_phis_doesnt_use_AC_remove; auto.
      apply list_composed_substs_cmds_doesnt_use_AC_remove; auto.
      apply list_composed_substs_tmn_doesnt_use_AC_remove; auto.
Qed.

(***************************************************************)
(* If v uses (fst elt), replace is by the value of (snd elt). *)
Definition subst_action_value (v:value) (elt:id * action): value :=
let '(id1, ac1) := elt in
match action2value ac1 with
| Some v1 => subst_value id1 v1 v 
| _ => v
end.
(* Apply actions to v. *)
Definition pipelined_actions_value (actions: list (id*action)) (v:value) 
  : value :=
List.fold_left subst_action_value actions v.

(* Properties of pipelined_actions_action *)
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
(* Composed substitution equals to pipelined substitution. *)
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
  induction bs as [|[l1 [ps1 cs1 tmn1]] bs]; simpl; intros; auto.
    f_equal; auto.
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
(* AVL-based maps equal to list-based maps. *)
Definition avl_actions__iff_mapsto__list_actions 
  A (actions1:AVLMap.t A) (actions2:ListMap.t A): Prop :=
forall id0 ac0, 
  AtomFMapAVL.MapsTo id0 ac0 actions1 <-> 
    lookupAL _ actions2 id0 = Some ac0.

Implicit Arguments avl_actions__iff_mapsto__list_actions [A].

Section avl_substs__iff_mapsto__list_substs.

Variable (actions1:AVLMap.t action) (actions2:ListMap.t action).
Hypothesis (Hiff : avl_actions__iff_mapsto__list_actions actions1 actions2).

Lemma iff_mapsto__find_none: forall id1
  (Hfind1 : ListMap.find id1 actions2 = merror),
  AVLMap.find action id1 actions1 = merror.
Proof.
  intros.
  case_eq (AVLMap.find action id1 actions1); auto.
  intros ac Heq.
  apply AVLFacts.find_mapsto_iff in Heq.
  apply Hiff in Heq. unfold ListMap.find in Hfind1.
  congruence.
Qed.

Lemma avl_substs_value__iff_mapsto__list_substs_value: forall v0,
  AVLComposedPass.substs_value actions1 v0 =
    ListComposedPass.substs_value actions2 v0.
Proof.
  unfold avl_actions__iff_mapsto__list_actions in *.
  destruct v0 as [id0|]; simpl; auto.
  unfold AVLMap.find, ListMap.find.
  case_eq (lookupAL action actions2 id0).
    intros ac Heq.
    apply Hiff in Heq.
    apply AVLFacts.find_mapsto_iff in Heq.
    rewrite Heq. auto.

    intros Hneq.
    rewrite iff_mapsto__find_none; auto.
Qed.

Lemma avl_substs_list_value_l__iff_mapsto__list_substs_list_value_l: forall l0,
  AVLComposedPass.substs_list_value_l actions1 l0 =
    ListComposedPass.substs_list_value_l actions2 l0.
Proof.
  induction l0 as [|[v0 vls0] l0]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
      apply avl_substs_value__iff_mapsto__list_substs_value.
Qed.

Lemma avl_substs_phi__iff_mapsto__list_substs_phi: forall p,
  AVLComposedPass.substs_phi actions1 p = 
    ListComposedPass.substs_phi actions2 p.
Proof.
  intros.
  destruct p. simpl.
  f_equal; auto.
    apply avl_substs_list_value_l__iff_mapsto__list_substs_list_value_l.
Qed.

Lemma avl_substs_list_value__iff_mapsto__list_substs_list_value: forall l0,
  AVLComposedPass.substs_list_value actions1 l0 =
    ListComposedPass.substs_list_value actions2 l0.
Proof.
  induction l0 as [|[sz0 v0] l0]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
      apply avl_substs_value__iff_mapsto__list_substs_value.
Qed.

Lemma avl_substs_pars__iff_mapsto__list_substs_pars: forall ps,
  List.map
     (fun p : typ * attributes * value =>
      let '(t, v) := p in (t, AVLComposedPass.substs_value actions1 v))
     ps =
   List.map
     (fun p : typ * attributes * value =>
      let '(t, v) := p in (t, ListComposedPass.substs_value actions2 v))
     ps.
Proof.
  induction ps as [|[[t0 a0] v0] ps]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
      apply avl_substs_value__iff_mapsto__list_substs_value.
Qed.

Lemma avl_substs_cmd__iff_mapsto__list_substs_cmd: forall c,
  AVLComposedPass.substs_cmd actions1 c = 
    ListComposedPass.substs_cmd actions2 c.
Proof.
  intros.
  destruct c; simpl; f_equal; 
    auto using avl_substs_list_value_l__iff_mapsto__list_substs_list_value_l,
               avl_substs_value__iff_mapsto__list_substs_value,
               avl_substs_list_value__iff_mapsto__list_substs_list_value,
               avl_substs_pars__iff_mapsto__list_substs_pars.
Qed.

Lemma avl_substs_tmn__iff_mapsto__list_substs_tmn: forall tmn,
  AVLComposedPass.substs_tmn actions1 tmn = 
    ListComposedPass.substs_tmn actions2 tmn.
Proof.
  intros.
  destruct tmn; simpl; f_equal; 
    auto using avl_substs_value__iff_mapsto__list_substs_value.
Qed.

Lemma avl_substs_fdef__iff_mapsto__list_substs_fdef: forall f,
  AVLComposedPass.substs_fdef actions1 f = 
    ListComposedPass.substs_fdef actions2 f.
Proof.
  intros.
  destruct f as [fh bs]. simpl.
  f_equal.
  induction bs as [|[l1 [ps1 cs1 tmn1]] bs]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
    f_equal; auto.
      apply map_ext. intro p.
      apply avl_substs_phi__iff_mapsto__list_substs_phi; auto.

      apply map_ext. intro c.
      apply avl_substs_cmd__iff_mapsto__list_substs_cmd; auto.

      apply avl_substs_tmn__iff_mapsto__list_substs_tmn; auto.
Qed.

Lemma iff_mapsto__find_parent_action: forall (ac : action),
  ListComposedPass.find_parent_action ac actions2 =
    AVLComposedPass.find_parent_action ac actions1.
Proof.
  intros.
  destruct ac as [|v1|t1]; simpl; auto.
  destruct v1 as [id1|]; simpl; auto.
  case_eq (ListMap.find id1 actions2).
    intros ac1 Hfind1.
    apply Hiff in Hfind1. 
    apply AVLFacts.find_mapsto_iff in Hfind1. 
    unfold AVLMap.find.
    rewrite Hfind1; auto.

    intros Hfind1.
    erewrite iff_mapsto__find_none; eauto.
Qed.

Lemma iff_mapsto__subst_actions_find1: forall id1 id0 ac0 ac2
  (J : AtomFMapAVL.MapsTo id0 ac0
         (AVLComposedPass.subst_actions id1 ac2 actions1)),
  lookupAL action (ListComposedPass.subst_actions id1 ac2 actions2) id0 = 
    ret ac0.
Proof.
  intros.
  unfold AVLComposedPass.subst_actions, ListComposedPass.subst_actions in *.
  destruct (action2value ac2) as [v0|].
    apply AVLFacts.map_mapsto_iff in J.
    apply lookupAL_map_iff.
    destruct J as [a [EQ J]]; subst.
    exists a. 
    split; auto.
      apply Hiff; auto.

    apply Hiff; auto.
Qed.

Lemma iff_mapsto__subst_actions_find2: forall id1 id0 ac0 ac2
  (J: lookupAL action (ListComposedPass.subst_actions id1 ac2 actions2) id0 = 
        ret ac0),
  AtomFMapAVL.MapsTo id0 ac0 
    (AVLComposedPass.subst_actions id1 ac2 actions1).
Proof.
  intros.
  unfold AVLComposedPass.subst_actions, ListComposedPass.subst_actions in *.
  destruct (action2value ac2) as [v0|].
    apply lookupAL_map_iff in J.
    apply AVLFacts.map_mapsto_iff.
    destruct J as [a [EQ J]]; subst.
    exists a. 
    split; auto.
      apply Hiff; auto.

    apply Hiff; auto.
Qed.

End avl_substs__iff_mapsto__list_substs.

(***************************************************************)

Lemma avl_compose_actions__iff_mapsto__list_compose_actions: forall actions,
  avl_actions__iff_mapsto__list_actions
    (AVLComposedPass.compose_actions actions)
    (ListComposedPass.compose_actions actions).
Proof.
  induction actions as [|[id1 ac1] actions]; simpl; intros.
    split; simpl; intro J; try congruence.
      apply AVLFacts.empty_mapsto_iff in J. tauto.

    assert (Heqfind:=IHactions).
    apply iff_mapsto__find_parent_action with (ac:=ac1) in Heqfind; auto.
    split; simpl; intro J.
      apply AVLFacts.add_mapsto_iff in J.
      destruct J as [[Heq J]|[Hneq J]]; subst; destruct_if; try congruence. 
        rewrite Heqfind. clear Heqfind.
        eapply iff_mapsto__subst_actions_find1; eauto.

      apply AVLFacts.add_mapsto_iff.
      destruct_if.
        left. split; auto.
        right. split; auto.
          rewrite <- Heqfind. clear Heqfind.
          eapply iff_mapsto__subst_actions_find2; eauto.
Qed.

(***************************************************************)
(* AVL-based composing equals to list-based composing. *)
Lemma acl_compose_actions__list_compose_actions: forall actions f,
  AVLComposedPass.substs_fdef (AVLComposedPass.compose_actions actions) f =
    ListComposedPass.substs_fdef (ListComposedPass.compose_actions actions) f.
Proof.
  intros.
  apply avl_substs_fdef__iff_mapsto__list_substs_fdef.
  apply avl_compose_actions__iff_mapsto__list_compose_actions.
Qed.

Lemma avl_substs_fdef__list_substs_fdef: forall actions (Huniq: uniq actions) 
  (Hwfrm: wf_AC_remove actions) (Hacyclic: acyclic_actions actions) f,
  AVLComposedPass.substs_fdef (AVLComposedPass.compose_actions actions) f = 
    ListMap.fold apply_subst_action (substs_actions actions) f.
Proof.
  intros.
  rewrite <- list_composed_substs__list_pipelined_substs; 
    auto using substs_actions__uniq.
  fold (composed_pipelined_actions actions f).
  rewrite <- list_compose_actions__list_composed_substs; auto.
  rewrite <- acl_compose_actions__list_compose_actions; auto.
Qed.

(***************************************************************)
Definition apply_action_block (b : block) (elt : id * action) : block :=
match elt with
| (id1, AC_remove) => remove_block id1 b
| (id1, AC_vsubst v1) => remove_block id1 (subst_block id1 v1 b)
| (id1, AC_tsubst t1) =>
    remove_block id1 (subst_block id1 (value_const (const_undef t1)) b)
end.

Lemma apply_action__apply_action_block: forall fh bs b elt (Hin: In b bs)
  fh' bs' (Heq: apply_action (fdef_intro fh bs) elt = fdef_intro fh' bs'),
  In (apply_action_block b elt) bs'.
Proof.
  destruct elt. simpl. 
  destruct a; simpl; intros; inv Heq; repeat (apply in_map; auto).
Qed.

(***************************************************************)
(* Micro passes preserve well-formed actions *)
Ltac destruct_sasinfo :=
match goal with
| sasinfo: sas.SASInfo _ |- _ =>
  let SAS_sid1 := fresh "SAS_sid1" in
  let SAS_sid2 := fresh "SAS_sid2" in 
  let SAS_align1 := fresh "SAS_align1" in 
  let SAS_align2 := fresh "SAS_align2" in 
  let SAS_value1 := fresh "SAS_value1" in 
  let SAS_value2 := fresh "SAS_value2" in 
  let SAS_tail0 := fresh "SAS_tail0" in
  let SAS_l0 := fresh "SAS_l0" in 
  let SAS_ps0 := fresh "SAS_ps0" in 
  let SAS_cs0 := fresh "SAS_cs0" in 
  let SAS_tmn0 := fresh "SAS_tmn0" in 
  let SAS_prop0 := fresh "SAS_prop0" in
  let SAS_BInF0 := fresh "SAS_BInF0" in 
  let SAS_ldincmds0 := fresh "SAS_ldincmds0" in 
  let SAS_cs1 := fresh "SAS_cs1" in
  let SAS_cs3 := fresh "SAS_cs3" in 
  let SAS_EQ := fresh "SAS_EQ" in
  destruct sasinfo as [SAS_sid1 SAS_sid2 SAS_align1 SAS_align2 SAS_value1 
                       SAS_value2 SAS_tail0
                       [SAS_l0 [SAS_ps0 SAS_cs0 SAS_tmn0]] SAS_prop0];
  destruct SAS_prop0 as 
    [SAS_BInF0 [SAS_ldincmds0 [SAS_cs1 [SAS_cs3 SAS_EQ]]]]; subst; simpl
end.

Ltac die__wf_actions_tac id' cs01 c0 cs02 dones' :=
  exists (remove_cmds id' cs01); exists c0;
  exists (remove_cmds id' cs02); exists dones';
  rewrite <- remove_cmds_middle; auto;
  unfold remove_cmds;
  repeat (split; eauto using remove_pres_loads_must_be_in_pre,
                       filter_pres_store_in_cmds_false,
                       filter_pres_store_in_cmds_false).

Lemma sas__wf_cd_action_pre: forall l5 ps5 cs5 tmn5 id' v0 cs0 id1 v1 fh actions
  bs1 fh' bs1' dones pinfo (Hwfpi: WF_PhiInfo pinfo) id2 ac2
  (Hnotin: id' `notin` dom actions) (Hneq: id2 <> id')
  (Huniq: uniqFdef (PI_f pinfo))
  l1 ps1 cs1 tmn1 (Hin: In (l1, stmts_intro ps1 cs1 tmn1) bs1)
  (Hfind1 : ret inl (id', v0, cs0) = find_init_stld cs1 (PI_id pinfo) dones)
  (Hfind2 : ret inr (id1, v1) = find_next_stld cs0 (PI_id pinfo))
  (HBinF : blockInFdefB (l5, stmts_intro ps5 cs5 tmn5) (PI_f pinfo) = true) 
  (Hwf_actions : 
    wf_cs_action_pre ((id', AC_remove) :: actions) cs5 (PI_id pinfo) (id2, ac2))
  (Heq: PI_f pinfo = fdef_intro fh bs1)
  (Hrm: remove_fdef id' (fdef_intro fh bs1) = fdef_intro fh' bs1'),
  wf_cs_action_pre actions (remove_cmds id' cs5) (PI_id pinfo) (id2, ac2).
Proof.
  intros. simpl in *.
  destruct ac2 as [|v2|t2].
  Case "remove".
    destruct Hwf_actions as [v2 [cs01 [c0 [cs02 [dones' [J1 [J2 [J3 J4]]]]]]]].
    assert (J1':=J1).
    eapply find_init_stld_inl_remove_neq_spec in J1'; eauto.
    exists v2. 
    destruct (id_dec (getCmdLoc c0) id'); subst.
    SCase "1.1".
      assert ((l1, stmts_intro ps1 cs1 tmn1) = (l5, stmts_intro ps5 cs5 tmn5)) 
        as EQ.
        eapply block_eq2 with (id1:=getCmdLoc c0); eauto 1.
          rewrite Heq. simpl. solve_in_list.
          apply find_init_stld_inl_in in Hfind1. simpl. xsolve_in_list.
          apply find_init_stld_inl_in' in J1. simpl. xsolve_in_list.
      inv EQ.
      assert (NoDup (getCmdsLocs cs5)) as Huniqcmds. solve_NoDup.
      eapply find_st_ld__sas_spec in Hfind1; eauto.
      destruct Hfind1 as 
        [A [t1 [al1 [EQ1 [B [C [t2 [al2 [EQ2 [G1 G2]]]]]]]]]]; subst.
      apply find_init_stld_inl_spec in J1.
      destruct J1 as [A' [t1' [al1' EQ1']]]; subst.
      match goal with
      | H: _ = ?A ++ ?b :: ?C ++ ?d :: ?E |- _ =>
          rewrite_env ((A ++ b :: C) ++ d :: E) in H
      end.
      apply NoDup_cmds_split_middle' in EQ1'; auto.
      destruct EQ1'; subst.
      assert (getCmdLoc c0 <> id1) as Hneq'. 
        clear - Huniqcmds.
        intro EQ. subst.
        rewrite getCmdsLocs_app in Huniqcmds.
        split_NoDup.
        inv Huniq0.
        apply H1. 
        rewrite getCmdsLocs_app. simpl. xsolve_in_list.
      clear - G2 G1 J2 J3 J4 Hneq' Hneq J1'. 
      exists (remove_cmds (getCmdLoc c0) (cs01 ++ B)). 
      exists (insn_store id1 t2 v1 (value_id (PI_id pinfo)) al2).
      exists (remove_cmds (getCmdLoc c0) C). 
      exists dones'. rewrite <- J1'. clear J1'.
      unfold remove_cmds.
      repeat (simpl; rewrite filter_app).
      repeat (destruct_dec; simpl; try congruence).
      split. simpl_env. auto.
      split.
        apply store_in_cmds_merge.
        split; auto using filter_pres_store_in_cmds_false.
      split; auto.
        apply loads_must_be_in_pre_load_in_cmds_false__loads_must_be_in_pre; 
          eauto using filter_pres_load_in_cmds_false,
                      remove_pres_loads_must_be_in_pre.
    SCase "1.2".
      die__wf_actions_tac id' cs01 c0 cs02 dones'.
  Case "vsubst". 
    destruct Hwf_actions as 
      [id3 [cs01 [c0 [cs02 [dones' [J1 [J2 [J3 [J4 J5]]]]]]]]]; subst.
    destruct (id_dec id3 id'); subst.
    SCase "2.1".
      elimtype False.
      assert ((l1, stmts_intro ps1 cs1 tmn1) = (l5, stmts_intro ps5 cs5 tmn5)) 
        as EQ.
        eapply block_eq2 with (id1:=id'); eauto 1.
          rewrite Heq. simpl. solve_in_list.
          apply find_init_stld_inl_in in Hfind1. simpl. xsolve_in_list.
          apply find_init_stld_inl_in in J1. simpl. xsolve_in_list.
      inv EQ.
      assert (NoDup (getCmdsLocs cs5)) as Huniqcmds. solve_NoDup.
      eapply find_st_ld__sas_spec in Hfind1; eauto 2.
      destruct Hfind1 as 
        [A [t1 [al1 [EQ1 [B [C [t2 [al2 [EQ2 [G1 G2]]]]]]]]]]; subst.
      apply find_init_stld_inl_spec in J1.
      destruct J1 as [A' [t1' [al1' EQ1']]]; subst.
      apply NoDup_cmds_split_middle' in EQ1'; auto.
      destruct EQ1'; subst.
      clear - G2 G1 J2 J4 J5 Hneq Huniqcmds H0.
      assert (In (insn_store id1 t2 v1 (value_id (PI_id pinfo)) al2)
                (cs01 ++ c0 :: cs02)) as Hin.
        rewrite <- H0. solve_in_list.
      destruct_in Hin.
        apply in__store_in_cmds in Hin. congruence.
      destruct_in Hin.
        simpl in J4. congruence.
    
        apply in_split in Hin.
        destruct Hin as [D1 [D2 EQ]]; subst.
        match goal with
        | H: _ = ?A ++ ?b :: ?C ++ ?d :: ?E |- _ =>
            rewrite_env ((A ++ b :: C) ++ d :: E) in H
        end.
        rewrite getCmdsLocs_app in Huniqcmds.
        split_NoDup. inv Huniq0.
        apply NoDup_cmds_split_middle' in H0; auto.
        destruct H0; subst.
        apply load_in_cmds_app in G1.
        destruct G1 as [? G1].
        apply load_in_cmds_false_cons_inv in G1.
        destruct G1. congruence.
    SCase "2.2".
      eapply find_init_stld_inl_remove_neq_spec in J1; eauto.
      exists id3. die__wf_actions_tac id' cs01 c0 cs02 dones'.
  Case "tsubst".
    destruct Hwf_actions as [cs01 [c0 [cs02 [dones' [J1 [J2 [J3 [J4 J5]]]]]]]]; 
      subst.
    destruct (id_dec (PI_id pinfo) id'); subst.
    SCase "3.1".
      assert (blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) (PI_f pinfo) = true)
        as HBinF'.
        rewrite Heq. simpl. solve_in_list.
      apply find_init_stld_inl_spec in Hfind1.
      destruct Hfind1 as [cs4 [ty4 [al4 Hst]]]; subst.
      apply WF_PhiInfo_spec10 in HBinF'; auto.
      simpl in HBinF'; congruence.
    SCase "3.2".
      eapply find_init_stld_inr_remove_neq_spec in J1; eauto.
      die__wf_actions_tac id' cs01 c0 cs02 dones'.
Qed.

Lemma subst_pres_loads_must_be_in_pre: forall id' ac' v' pid actions 
  (Hnused: used_in_value pid v' = false) (Hneq: id' <> pid) cs
  (Hld : loads_must_be_in_pre ((id', ac') :: actions) pid cs),
  loads_must_be_in_pre
     ((id', ac') :: ListComposedPass.subst_actions id' ac' actions) pid
     (List.map (subst_cmd id' v') cs).
Proof.
  induction 3; simpl; intros.
    constructor.

    constructor; auto.
      intros Heq.
      rewrite <- subst_pres_load_in_cmd in Heq; auto.
      apply H in Heq.
      rewrite <- subst_pres_getCmdLoc.      
      simpl.
      rewrite list_subst_actions__dom. auto.
Qed.

Lemma las__wf_cs_action_pre: forall cs5 id' v' actions
  pid id2 ac2
  (Hnused: used_in_value pid v' = false) (Hneq: id' <> pid)
  (Hwf_actions : 
    wf_cs_action_pre ((id', AC_vsubst v') :: actions) cs5 pid (id2, ac2)),
  wf_cs_action_pre 
    ((id', AC_vsubst v') :: 
     ListComposedPass.subst_actions id' (AC_vsubst v') actions)
    (List.map (subst_cmd id' v') cs5)
    pid (id2, subst_action id' v' ac2).
Proof.
  intros. 
  destruct ac2 as [|v2|t2]; simpl in *.
  Case "remove".
    destruct Hwf_actions as [v2 [cs01 [c0 [cs02 [dones' [J1 [J2 [J3 J4]]]]]]]].
    eapply find_init_stld_inl_subst_spec in J1; eauto.
    exists (v2 {[v' // id']}). exists (List.map (subst_cmd id' v') cs01). 
    exists (subst_cmd id' v' c0). exists (List.map (subst_cmd id' v') cs02). 
    exists dones'.
    rewrite List.map_app in J1. simpl in J1.
    rewrite <- subst_pres_store_in_cmds; auto.
    rewrite <- subst_pres_store_in_cmd; auto.
    repeat (split; auto using subst_pres_loads_must_be_in_pre).
  Case "vsubst". 
    destruct Hwf_actions as 
      [id3 [cs01 [c0 [cs02 [dones' [J1 [J2 [J3 [J4 J5]]]]]]]]]; subst.
    eapply find_init_stld_inl_subst_spec in J1; eauto.
    exists id3. exists (List.map (subst_cmd id' v') cs01). 
    exists (subst_cmd id' v' c0). exists (List.map (subst_cmd id' v') cs02). 
    exists dones'.
    rewrite List.map_app in J1. simpl in J1.
    rewrite <- subst_pres_store_in_cmds; auto.
    rewrite <- subst_pres_load_in_cmd; auto.
    rewrite <- subst_pres_getCmdLoc. 
    repeat (split; auto using subst_pres_loads_must_be_in_pre).
  Case "tsubst".
    destruct Hwf_actions as [cs01 [c0 [cs02 [dones' [J1 [J2 [J3 [J4 J5]]]]]]]]; 
      subst.
    eapply find_init_stld_inr_subst_spec with (id':=id') in J1; eauto.
    exists (List.map (subst_cmd id' v') cs01). exists (subst_cmd id' v' c0). 
    exists (List.map (subst_cmd id' v') cs02). exists dones'.
    rewrite List.map_app in J1. simpl in J1.
    rewrite <- subst_pres_store_in_cmds; auto.
    rewrite <- subst_pres_load_in_cmd; auto.
    rewrite <- subst_pres_getCmdLoc. 
    repeat (split; auto using subst_pres_loads_must_be_in_pre).
Qed.

Lemma die__wf_cs_action_pre: forall pinfo id' ac' actions id2 ac2
  fh bs1 (Hnotin: id' `notin` dom actions) (Hneq: id2 <> id')
  (Huniq: uniqFdef (fdef_intro fh bs1))
  (Hisld:
   forall insn, lookupInsnViaIDFromFdef (fdef_intro fh bs1) id' = Some insn ->
   match insn with
   | insn_cmd (insn_load _ _ _ _) => True
   | _ => False
   end) l1 ps1 cs1 tmn1
  (HBinF : 
     blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) (fdef_intro fh bs1) = true) 
  (Hwf_actions : 
     wf_cs_action_pre ((id', ac')::actions) cs1 (PI_id pinfo) (id2, ac2)),
  wf_cs_action_pre actions (remove_cmds id' cs1) (PI_id pinfo) (id2, ac2).
Proof.
  intros. 
  destruct ac2 as [|v2|t2]; simpl in Hwf_actions; simpl.
  Case "remove".
    destruct Hwf_actions as [v2 [cs01 [c0 [cs02 [dones' [J1 [J2 [J3 J4]]]]]]]].
    destruct (id_dec (getCmdLoc c0) id'); subst.
    SCase "1.1".
      apply find_init_stld_inl_spec in J1.
      destruct J1 as [A' [t1' [al1' EQ1']]]; subst.
      match goal with
      | H: blockInFdefB (_, stmts_intro _
               (?A ++ ?b :: ?C ++ ?d :: ?E) _) _ = true |- _ =>
        rewrite_env ((A ++ b :: C) ++ d :: E) in H;
        eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H; 
          eauto using in_middle;
        apply Hisld in H
      end.
      destruct c0; tinv J3. tauto.
    SCase "1.2".
      eapply find_init_stld_inl_remove_neq_spec in J1; eauto.
      exists v2. die__wf_actions_tac id' cs01 c0 cs02 dones'.
  Case "vsubst". 
    destruct Hwf_actions as 
      [id3 [cs01 [c0 [cs02 [dones' [J1 [J2 [J3 [J4 J5]]]]]]]]]; subst.
    destruct (id_dec id3 id'); subst.
    SCase "2.1".
      apply find_init_stld_inl_spec in J1.
      destruct J1 as [A' [t1' [al1' EQ1']]]; subst.
      match goal with
      | H: blockInFdefB _ _ = true |- _ =>
        eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H; 
          eauto using in_middle;
        apply Hisld in H; tauto
      end.
    SCase "2.2".
      eapply find_init_stld_inl_remove_neq_spec in J1; eauto.
      exists id3. die__wf_actions_tac id' cs01 c0 cs02 dones'.
  Case "tsubst".
    destruct Hwf_actions as [cs01 [c0 [cs02 [dones' [J1 [J2 [J3 [J4 J5]]]]]]]]; 
      subst.
    destruct (id_dec (PI_id pinfo) id'); subst.
    SCase "3.1".
      apply find_init_stld_inr_spec in J1.
      destruct J1 as [cs4 [ty1 [num1 [al1 [EQ Hst]]]]]; subst.
      match goal with
      | H: blockInFdefB _ _ = true |- _ =>
          eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H; 
            eauto using in_middle;
          apply Hisld in H; inv H
      end.
    SCase "3.2".
      eapply find_init_stld_inr_remove_neq_spec in J1; eauto 1.
      die__wf_actions_tac id' cs01 c0 cs02 dones'.
Qed.

Lemma las_die__wf_cs_action_pre: forall l5 ps5 cs5 tmn5 id' v' cs0 fh actions
  bs1 id0 dones pinfo id2 ac2 (Hneq': id2 <> id') cs1 l1 ps1 tmn1
  (Hnotin: id' `notin` dom actions) (Huniq: uniqFdef (fdef_intro fh bs1))
  (Hnused: used_in_value (PI_id pinfo) v' = false) (Hneq: id' <> (PI_id pinfo))
  (Hfind1 : ret inl (id0, v', cs0) = find_init_stld cs1 (PI_id pinfo) dones)
  (Hfind2 : ret inl id' = find_next_stld cs0 (PI_id pinfo))
  (HBinF5: blockInFdefB (l5, stmts_intro ps5 cs5 tmn5) (fdef_intro fh bs1) = true) 
  (HBinF1: blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) (fdef_intro fh bs1) = true) 
  (Hwf_actions : 
    wf_cs_action_pre 
      ((id', AC_vsubst v') :: actions) cs5 (PI_id pinfo) (id2, ac2)),
  wf_cs_action_pre 
    (ListComposedPass.subst_actions id' (AC_vsubst v') actions)
    (remove_cmds id' (List.map (subst_cmd id' v') cs5))
    (PI_id pinfo) (id2, subst_action id' v' ac2).
Proof.
  intros.
  rewrite <- list_subst_actions__dom with (id0:=id')(ac0:=AC_vsubst v') 
    in Hnotin; auto.
  eapply die__wf_cs_action_pre with (fh:=fh)
    (bs1:=List.map (subst_block id' v') bs1); eauto 1.
    eapply subst_uniqFdef with (id0:=id')(v0:=v') in Huniq; eauto.

    intros insn0 H0.
    fold (subst_fdef id' v' (fdef_intro fh bs1)) in H0.
    apply subst_lookupInsnViaIDFromFdef_rev in H0.
    destruct H0 as [instr1 [G3 G4]].
    eapply find_st_ld__las_spec in Hfind1; eauto.
    destruct Hfind1 as 
          [A [t1 [al1 [EQ1 [B [C [t2 [al2 [EQ2 [G1 G2]]]]]]]]]]; subst.
    match goal with
    | H: blockInFdefB (_, stmts_intro _
               (?A ++ ?b :: ?C ++ ?d :: ?E) _) _ = true |- _ =>
       clear - H G3 Huniq;
       rewrite_env ((A ++ b :: C) ++ d :: E) in H;
       eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H; 
         eauto using in_middle;
       simpl in *; simpl_env in *;
       rewrite G3 in H; inv H; simpl; auto
    end.

    simpl. simpl in HBinF5.
    apply InBlocksB__In in HBinF5.
    apply In_InBlocksB.
    apply in_map with (f:=subst_block id' v') in HBinF5.
    simpl in HBinF5. eauto.
 
    eapply las__wf_cs_action_pre; simpl; eauto.
Qed.

Lemma laa__wf_cs_action_pre: forall cs5 id' t' actions
  pid id2 ac2 (Hneq: id' <> pid)
  (Hwf_actions : 
    wf_cs_action_pre ((id', AC_tsubst t') :: actions) cs5 pid (id2, ac2)),
  wf_cs_action_pre 
    ((id', AC_tsubst t') :: 
     ListComposedPass.subst_actions id' (AC_tsubst t') actions)
    (List.map (subst_cmd id' (value_const (const_undef t'))) cs5)
    pid (id2, subst_action id' (value_const (const_undef t')) ac2).
Proof.
  intros. 
  destruct ac2 as [|v2|t2]; simpl in *.
  Case "remove".
    destruct Hwf_actions as [v2 [cs01 [c0 [cs02 [dones' [J1 [J2 [J3 J4]]]]]]]].
    eapply find_init_stld_inl_subst_spec with 
      (v':=value_const (const_undef t')) in J1; simpl; eauto.
    exists (v2 {[value_const (const_undef t') // id']}). 
    exists (List.map (subst_cmd id' (value_const (const_undef t'))) cs01). 
    exists (subst_cmd id' (value_const (const_undef t')) c0). 
    exists (List.map (subst_cmd id' (value_const (const_undef t'))) cs02). 
    exists dones'.
    rewrite List.map_app in J1. simpl in J1.
    rewrite <- subst_pres_store_in_cmds; auto.
    rewrite <- subst_pres_store_in_cmd; auto.
    repeat (split; auto using subst_pres_loads_must_be_in_pre).
  Case "vsubst". 
    destruct Hwf_actions as 
      [id3 [cs01 [c0 [cs02 [dones' [J1 [J2 [J3 [J4 J5]]]]]]]]]; subst.
    eapply find_init_stld_inl_subst_spec with 
      (v':=value_const (const_undef t')) in J1; simpl; eauto.
    exists id3. 
    exists (List.map (subst_cmd id' (value_const (const_undef t'))) cs01). 
    exists (subst_cmd id' (value_const (const_undef t')) c0). 
    exists (List.map (subst_cmd id' (value_const (const_undef t'))) cs02). 
    exists dones'.
    rewrite List.map_app in J1. simpl in J1.
    rewrite <- subst_pres_store_in_cmds; auto.
    rewrite <- subst_pres_load_in_cmd; auto.
    rewrite <- subst_pres_getCmdLoc. 
    repeat (split; auto using subst_pres_loads_must_be_in_pre).
  Case "tsubst".
    destruct Hwf_actions as [cs01 [c0 [cs02 [dones' [J1 [J2 [J3 [J4 J5]]]]]]]]; 
      subst.
    eapply find_init_stld_inr_subst_spec with (id':=id') 
      (v':=value_const (const_undef t')) in J1; simpl; eauto.
    exists (List.map (subst_cmd id' (value_const (const_undef t'))) cs01). 
    exists (subst_cmd id' (value_const (const_undef t')) c0). 
    exists (List.map (subst_cmd id' (value_const (const_undef t'))) cs02). 
    exists dones'.
    rewrite List.map_app in J1. simpl in J1.
    rewrite <- subst_pres_store_in_cmds; auto.
    rewrite <- subst_pres_load_in_cmd; auto.
    rewrite <- subst_pres_getCmdLoc. 
    repeat (split; auto using subst_pres_loads_must_be_in_pre).
Qed.

Lemma laa_die__wf_cs_action_pre: forall l5 ps5 cs5 tmn5 id' t' cs0 fh actions
  bs1 dones pinfo id2 ac2 (Hneq': id2 <> id') cs1 l1 ps1 tmn1
  (Hnotin: id' `notin` dom actions) (Huniq: uniqFdef (fdef_intro fh bs1))
  (Hneq: id' <> (PI_id pinfo))
  (Hfind1 : ret inr (value_const (const_undef t'), cs0) = 
              find_init_stld cs1 (PI_id pinfo) dones)
  (Hfind2 : ret inl id' = find_next_stld cs0 (PI_id pinfo))
  (HBinF5: blockInFdefB (l5, stmts_intro ps5 cs5 tmn5) (fdef_intro fh bs1) = true) 
  (HBinF1: blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) (fdef_intro fh bs1) = true) 
  (Hwf_actions : 
    wf_cs_action_pre 
      ((id', AC_tsubst t') :: actions) cs5 (PI_id pinfo) (id2, ac2)),
  wf_cs_action_pre 
    (ListComposedPass.subst_actions id' (AC_tsubst t') actions)
    (remove_cmds id' 
      (List.map (subst_cmd id' (value_const (const_undef t'))) cs5))
    (PI_id pinfo) (id2, subst_action id' (value_const (const_undef t')) ac2).
Proof.
  intros.
  rewrite <- list_subst_actions__dom with (id0:=id')(ac0:=AC_tsubst t') 
    in Hnotin; auto.
  eapply die__wf_cs_action_pre with (fh:=fh)
    (bs1:=List.map (subst_block id' (value_const (const_undef t'))) bs1); 
    eauto 1.
    eapply subst_uniqFdef with 
      (id0:=id')(v0:=value_const (const_undef t')) in Huniq; eauto.

    intros insn0 H0.
    fold (subst_fdef id' (value_const (const_undef t')) (fdef_intro fh bs1)) in H0.
    apply subst_lookupInsnViaIDFromFdef_rev in H0.
    destruct H0 as [instr1 [G3 G4]].
    apply find_init_stld_inr_spec in Hfind1.
    destruct Hfind1 as [cs4 [ty1 [num1 [al1 [EQ Hst]]]]]; subst.
    apply find_next_stld_inl_spec' in Hfind2.
    destruct Hfind2 as [cs2 [cs6 [ty2 [al2 [Hld [J1 J2]]]]]]; subst.
    match goal with
    | H: blockInFdefB (_, stmts_intro _
               (?A ++ ?b :: ?C ++ ?d :: ?E) _) _ = true |- _ =>
       clear - H G3 Huniq;
       rewrite_env ((A ++ b :: C) ++ d :: E) in H;
       eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H; 
         eauto using in_middle;
       simpl in *; simpl_env in *;
       rewrite G3 in H; inv H; simpl; auto
    end.

    simpl. simpl in HBinF5.
    apply InBlocksB__In in HBinF5.
    apply In_InBlocksB.
    apply in_map with 
      (f:=subst_block id' (value_const (const_undef t'))) in HBinF5.
    simpl in HBinF5. eauto.
 
    eapply las__wf_cs_action_pre; simpl; eauto.
Qed.

(* Composed substitution preserves well-formedness of actions. *)
Lemma list_subst_actions__wf_cs_action_pre: forall (id' : id) (ac' : action)
  (id2 : atom) (acs3 : list (atom * action)) (ac2 : action) (l0 : l)
  (ps0 : phinodes) (cs : cmds) (tmn0 : terminator)
  pinfo (Hwfpi: WF_PhiInfo pinfo) s m 
  (HwfF: wf_fdef s m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo))
  (Hnotin: id' `notin` dom acs3) (Hneq: id2 <> id')
  (J : wf_cs_action_pre ((id', ac') :: acs3) cs (PI_id pinfo) (id2, ac2))
  (l5 : l) (ps5 : phinodes) (cs5 : cmds) (tmn5 : terminator)
  fh bs1 l1 ps1 cs1 tmn1 (Hin: In (l1, stmts_intro ps1 cs1 tmn1) bs1)
  (Hwf: wf_cs_action cs1 (PI_id pinfo) (id', ac')) 
  (Heq: PI_f pinfo = fdef_intro fh bs1)
  (HBinF: blockInFdefB (l0, stmts_intro ps0 cs tmn0) (PI_f pinfo) = true)
  (Heq5 : apply_action_block (l0, stmts_intro ps0 cs tmn0) (id', ac') =
          (l5, stmts_intro ps5 cs5 tmn5)),
  wf_cs_action_pre (ListComposedPass.subst_actions id' ac' acs3) cs5 
    (PI_id pinfo) (id2, subst_action_action ac2 (id', ac')).
Proof.
  intros.
  assert (HBinF': 
    blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) (PI_f pinfo) = true).
    rewrite Heq. simpl. solve_in_list.
Local Opaque wf_cs_action_pre.
  destruct ac' as [|v'|t']; simpl in *; inv Heq5.
  Case "remove".
    destruct Hwf as [v0 [cs0 [id1 [v1 [dones [Hfind1 Hfind2]]]]]].
    unfold ListComposedPass.subst_actions. simpl.
    eapply sas__wf_cd_action_pre; simpl; eauto 1.
  Case "vsubst".
    destruct Hwf as [id0 [cs0 [dones [Hfind1 Hfind2]]]].
    assert (used_in_value (PI_id pinfo) v' = false /\ id' <> (PI_id pinfo)) as 
      Hnuse.
      eapply find_st_ld_las_doesnt_use_pid in Hfind1; simpl; eauto 1.
    destruct Hnuse.
    rewrite Heq in *.
    eapply las_die__wf_cs_action_pre; eauto 1.
  Case "tsubst".
    destruct Hwf as [cs0 [dones [Hfind1 Hfind2]]].
    assert (id' <> (PI_id pinfo)) as Hnuse.
      eapply find_st_ld_laa_doesnt_use_pid with (id':=id') in Hfind1; eauto 1.
    rewrite Heq in *.
    eapply laa_die__wf_cs_action_pre; eauto 1.
Transparent wf_cs_action_pre.
Qed.

(* Pipelined transformations of LAS/LAA/SAS preserve semantics. *)
Lemma wf_actions_cons_inv: forall fh bs fh' bs' id0 ac0 
  pinfo (Hwfpi: WF_PhiInfo pinfo) (Huniq: uniqFdef (PI_f pinfo)) actions
  (Heqpi: PI_f pinfo = fdef_intro fh bs) (Huniq': uniq actions)
  (Hnotin: id0 `notin` dom actions) s m (HwfF: wf_fdef s m (PI_f pinfo)) 
  (Heq: apply_action (fdef_intro fh bs) (id0, ac0) = fdef_intro fh' bs')
  (Hwf: wf_actions bs (PI_id pinfo) (PI_rd pinfo) ((id0, ac0) :: actions)),
  (exists l0, exists ps0, exists cs0, exists tmn0,
    In (l0, stmts_intro ps0 cs0 tmn0) bs /\ 
    In l0 (PI_rd pinfo) /\
    wf_cs_action cs0 (PI_id pinfo) (id0, ac0)) /\
  wf_actions bs' (PI_id pinfo) (PI_rd pinfo)
    (ListComposedPass.subst_actions id0 ac0 actions).
Proof.
  intros.
  assert ((id0, ac0) :: actions = nil ++ (id0, ac0) :: actions) as EQ. auto.
  apply Hwf in EQ.
  destruct EQ as [l0 [ps0 [cs0 [tmn0 [Hin0 [Hrd0 Hwf0]]]]]].
  apply wf_cs_action_nil__wf_cs_action in Hwf0; auto.
  split.
    exists l0. exists ps0. exists cs0. exists tmn0. 
    split; auto.

    intros acs1 ac acs2 Heq'.
    apply list_subst_actions_app_inv in Heq'.
    destruct Heq' as [acs3 [acs4 [EQ [J1 J2]]]]; subst.
    destruct ac as [id1 ac'].
    apply list_subst_actions_cons_inv in J2.
    destruct J2 as [ac1 [acs5 [EQ [J3 J2]]]]; subst.
    assert ((id0, ac0) :: acs3 ++ (id1, ac1) :: acs5 = 
              ((id0, ac0) :: acs3) ++ (id1, ac1) :: acs5) as EQ.
      simpl_env. auto.
    apply Hwf in EQ.
    destruct EQ as [l1 [ps1 [cs1 [tmn1 [Hin1 [Hrd1 J]]]]]].
    assert (Hin1':=Hin1).
    eapply apply_action__apply_action_block in Hin1; eauto.
    case_eq (apply_action_block (l1, stmts_intro ps1 cs1 tmn1) (id0, ac0)).
    intros l5 [ps5 cs5 tmn5] Heq5.
    exists l5. exists ps5. exists cs5. exists tmn5.
    rewrite Heq5 in Hin1.
    split; auto.
    split.
      destruct ac0; inv Heq5; auto.

      eapply list_subst_actions__wf_cs_action_pre in Hwf0; eauto 1.
        rewrite Heqpi. simpl. solve_in_list.
Qed.

Lemma apply_cs_action_sim_wfS_wfPI: forall (los : layouts) (nts : namedts) 
  (fh : fheader) (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) id' ac'
  (Hwf: wf_cs_action cs0 (PI_id pinfo) (id', ac')) (Hinrd: In l0 (PI_rd pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Hwfpi: WF_PhiInfo pinfo) f1 f2
  (Heqf2: f2 = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Heqf1: f1 = apply_action
                 (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
                 (id', ac'))
  S2 S1 (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (Hok: defined_program S2 main VarArgs)
  (HwfS : wf_system S2),
  (program_sim S1 S2 main VarArgs /\
    wf_system S1 /\ defined_program S1 main VarArgs) /\
   (exists pinfo' : PhiInfo, WF_PhiInfo pinfo' /\ keep_pinfo f1 pinfo pinfo').
Proof.
  intros.
  destruct ac' as [|v'|t']; simpl in *; subst.
  Case "remove".
    destruct Hwf as [v0 [cs1 [id1 [v1 [dones' [Hfind1 Hfind2]]]]]].
    split.
      split.
        eapply sas_sim; eauto.
      split.
        eapply sas_wfS; eauto.
        eapply program_sim__preserves__defined_program; eauto using sas_sim.    

        eapply sas_wfPI with (pinfo:=pinfo) in HwfS; eauto.
        instantiate_pinfo.
  Case "vsubst".
    destruct Hwf as [id0 [cs1 [dones' [Hfind1 Hfind2]]]].
    split.
      eapply las_die_sim_wfS; eauto.

      eapply las_die_wfPI with (pinfo:=pinfo) in HwfS; eauto.
      instantiate_pinfo.
  Case "tsubst".
    destruct Hwf as [cs1 [dones' [Hfind1 Hfind2]]].
    split.
      eapply laa_die_sim_wfS; eauto.

      eapply laa_die_wfPI with (pinfo:=pinfo) in HwfS; eauto.
      instantiate_pinfo.
Qed.

Definition pipelined_elim_stld_sim_wfS_wfPI_prop Ps1 Ps2 los nts main
  VarArgs pid rd (n:nat) := forall actions
  (Hlen: (length actions = n)%nat)  
  (pinfo : PhiInfo) f1 fh bs1 f2 
  (Heqactions : wf_actions bs1 pid rd actions) (Huniq: uniq actions)
  (Heq: f1 = fdef_intro fh bs1)
  (Hpass : pipelined_actions actions f1 = f2)
  (Heq1 : PI_f pinfo = fdef_intro fh bs1) (Heq2 : PI_id pinfo = pid)
  (Heq0 : PI_rd pinfo = rd) (Hwfpi : WF_PhiInfo pinfo) S1 S2
  (Heq3 : S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq4 : S2 = [module_intro los nts
                 (Ps1 ++ product_fdef (fdef_intro fh bs1) :: Ps2)])
  (HwfS : wf_system S2) (Hok : defined_program S2 main VarArgs),
  (program_sim S1 S2 main VarArgs /\
    wf_system S1 /\ defined_program S1 main VarArgs) /\
   (exists pinfo' : PhiInfo, WF_PhiInfo pinfo' /\ keep_pinfo f2 pinfo pinfo').

Lemma pipelined_elim_stld_sim_wfS_wfPI_aux: forall Ps1 Ps2 los nts main
  VarArgs pid rd n, pipelined_elim_stld_sim_wfS_wfPI_prop  
  Ps1 Ps2 los nts main VarArgs pid rd n.
Proof.
  intros until n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold pipelined_elim_stld_sim_wfS_wfPI_prop, pipelined_actions in *.
  destruct actions as [|[id' ac'] actions].
  Case "base".
    intros.
    simpl in Hpass.
    repeat subst.
    split.
      split; auto using program_sim_refl.
      exists pinfo. split; auto. split; auto.
  Case "ind".
Local Opaque apply_action.
    unfold_substs_actions. simpl. 
    intros. subst x. 
    inversion Huniq as [|A B C Huniq' Hnotin]; subst A B C.
    assert (Hwf:
      wf_fdef [module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2)]
              (module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2)) 
              (PI_f pinfo) /\
      uniqFdef (PI_f pinfo)).
      apply wf_single_system__wf_uniq_fdef; auto.
        subst. rewrite Heq1. auto.
    destruct Hwf as [HwfF HuniqF].
    assert (HuniqF':=HuniqF). rewrite Heq1 in HuniqF'.
    case_eq (apply_action (fdef_intro fh bs1) (id', ac')).
    intros fh' bs1' Heq'. subst pid rd.
    eapply wf_actions_cons_inv in Heqactions; eauto.
    destruct Heqactions as 
      [[l5 [ps5 [cs5 [tmn5 [Hin [Hinrd Hwfaction]]]]]] Hwf_actions].
    apply in_split in Hin.
    destruct Hin as [bs11 [bs21 EQ]]; subst bs1.
    subst S2.
    assert (Hok':=Hok).
    eapply apply_cs_action_sim_wfS_wfPI with (S1:=
        [module_intro los nts 
          (Ps1 ++ product_fdef (apply_action f1 (id', ac')) :: Ps2)]) 
        in Hok'; try solve [eauto | subst f1; eauto].
    SCase "1". 
      destruct Hok' as [[Hsim [Hwf Hok']] [pinfo' [Hwfpi' Hkeeppi']]].
      eapply Hrec with (S2:=
        [module_intro los nts
          (Ps1 ++ product_fdef (apply_action f1 (id', ac')) :: Ps2)]) 
        (fh:=fh') (bs1:=bs1') (pinfo0:=pinfo') in Hwf_actions; 
        try solve [eauto 2 | 
                   congruence |
                   apply list_subst_actions__uniq; auto |
                   rewrite <- list_subst_actions__length; auto |
                   subst; solve_keep_pinfo | 
                   rewrite <- Heq'; subst; simpl; solve_keep_pinfo].
        destruct Hwf_actions as [J1 [pinfo'' [J2 J3]]].
        split.
          apply program_sim_wfS_trans with (P2:=
            [module_intro los nts
              (Ps1 ++ product_fdef (apply_action f1 (id', ac')) :: Ps2)]); 
          subst; auto.

          exists pinfo''.
          subst; split; eauto using keep_pinfo_trans.
    SCase "2".
      congruence.
Transparent apply_action.
Qed.

Lemma find_stld_pairs_blocks__wf_actions_uniq: forall pid rd bs actions
  (Huniq: NoDup (getBlocksLocs bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs),
  wf_actions bs pid rd actions /\ uniq actions.
Proof.
  intros.
  split.
    apply find_stld_pairs_blocks__wf_actions; auto.
    eapply find_stld_pairs_blocks__uniq; eauto.
Qed.

Lemma pipelined_elim_stld_sim_wfS_wfPI: forall fh bs1 f2 Ps1 Ps2 los nts main
  VarArgs pid rd (pinfo : PhiInfo) (actions : list (atom * action))
  (Heqactions : actions = flat_map (find_stld_pairs_block pid rd) bs1)
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
Proof.
  intros.
  assert (J:=pipelined_elim_stld_sim_wfS_wfPI_aux Ps1 Ps2 los nts main
    VarArgs pid rd (length actions)).
  unfold pipelined_elim_stld_sim_wfS_wfPI_prop in J.
  assert (Huniq: NoDup (getBlocksLocs bs1)).
    subst.
    apply wf_single_system__wf_uniq_fdef in HwfS; auto.
    destruct HwfS as [_ Huniq].
    apply uniqF__uniqBlocksLocs in Huniq; auto.
  apply find_stld_pairs_blocks__wf_actions_uniq in Heqactions; auto.
  destruct Heqactions.
  eapply J; eauto.
    congruence.
Qed.

(***************************************************************)
(* vmem2reg finds well-formed action lists, which are unique and acyclic. *)

Lemma find_stld_pairs_blocks_spec: forall s m fh bs
  (HwfF: wf_fdef s m (fdef_intro fh bs)) pid rd actions
  (HuniqF: uniqFdef (fdef_intro fh bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs)
  (Hreach: ret rd = reachablity_analysis (fdef_intro fh bs)),
  uniq actions /\ acyclic_actions actions /\ wf_AC_remove actions.
Proof.
  intros.
  split.
    eapply find_stld_pairs_blocks__uniq; eauto using uniqF__uniqBlocksLocs.
  split.
    eapply find_stld_pairs_blocks_acyclic; eauto.
    eapply find_stld_pairs_blocks__wf_AC_remove; eauto.
Qed.

(***************************************************************)

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
| Hpass: elim_stld_fdef ?pid ?rd ?f1 = _,
  Heq: ?s = [?m], 
  HwfS: wf_system ?s |- _ =>
  assert (HwfS': wf_fdef s m f1 /\
                 uniqFdef f1); try solve [
    subst;
    apply wf_single_system__wf_uniq_fdef in HwfS; auto
    ];
  destruct HwfS' as [HwfF HuniqF];
  let fh := fresh "fh" in
  let bs1 := fresh "bs1" in
  let actions := fresh "actions" in
  let Hwf := fresh "Hwf" in
  let Huniq := fresh "Huniq" in
  let Hacyc := fresh "Hacyc" in
  let Hwfrm := fresh "Hwfrm" in
  unfold elim_stld_fdef in Hpass;
  destruct f1 as [fh bs1];
  remember (flat_map (find_stld_pairs_block pid rd) bs1)
    as actions;
  match goal with
  | Heqactions: actions = _ |- _ =>
    assert (Hwf:=Heqactions);
    eapply find_stld_pairs_blocks_spec in Hwf; eauto;
    destruct Hwf as [Huniq [Hacyc Hwfrm]]
  end 
end.

(* Composed LAS/LAA preserves well-formedness. *)
Lemma elim_stld_sim_wfS_wfPI: forall f1 f2 Ps1 Ps2 los nts main
  VarArgs pid rd (Hreach: ret rd = reachablity_analysis f1)
  (pinfo:PhiInfo)
  (Hpass: elim_stld_fdef pid rd f1 = f2)
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

(* The pipelined pass preserves CFGs. *)
Lemma apply_action_reachablity_successors: forall elt f1 f2 
  (Hpass : apply_action f1 elt = f2),
  reachablity_analysis f2 = reachablity_analysis f1 /\
    successors f2 = successors f1.
Proof.
  destruct elt as [id0 []]; simpl; intros; subst.
  Case "1".
    assert (J:=remove_reachablity_successors id0 f1).
    destruct J as [J3 J4].
    split; etransitivity; eauto.
  Case "2".
    assert (J:=remove_subst_reachablity_successors id0 id0 v f1).
    destruct J as [J3 J4].
    split; etransitivity; eauto.
  Case "3".
    assert (J:=remove_subst_reachablity_successors id0 id0 
                 (value_const (const_undef t)) f1).
    destruct J as [J3 J4].
    split; etransitivity; eauto.
Qed.

Lemma apply_actions_reachablity_successors: forall actions f1 f2 
  (Hpass : fold_left apply_action actions f1 = f2),
  reachablity_analysis f2 = reachablity_analysis f1 /\
    successors f2 = successors f1.
Proof.
  induction actions as [|elt acs]; simpl; intros; subst; auto.
    edestruct IHacs with (f1:=apply_action f1 elt) as [J1 J2]; eauto.
    assert (J:=apply_action_reachablity_successors elt f1).
    edestruct J as [J3 J4]; eauto.
    split; etransitivity; eauto.
Qed.

Lemma pipelined_actions_reachablity_successors: forall f1 f2 actions
  (Hpass : pipelined_actions actions f1 = f2),
  reachablity_analysis f2 = reachablity_analysis f1 /\
    successors f2 = successors f1.
Proof.
  unfold pipelined_actions.
  intros.
  eapply apply_actions_reachablity_successors; eauto.
Qed.

(* Composed LAS/LAA preserves CFGs. *)
Lemma elim_stld_reachablity_successors: forall pid rd f1 f2 S2 Ps1 los nts Ps2
  (Hreach: ret rd = reachablity_analysis f1)
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (HwfS : wf_system S2) (Hpass: elim_stld_fdef pid rd f1 = f2),
  reachablity_analysis f2 = reachablity_analysis f1 /\
    successors f2 = successors f1.
Proof.
  intros. 
  unfold_elim_stld_fdef_tac.
  avl_to_list_tac.
  eapply pipelined_actions_reachablity_successors; eauto.
Qed.

Hint Unfold keep_pinfo.

(***************************************************************)
(* well-formed actions for fused phinode elimination *)
Definition wf_phi_action f rd (elt:id*action) : Prop := 
let '(id0, ac0) := elt in
match ac0 with
| AC_remove =>
    exists l0, exists ps0, exists cs0, exists tmn0, exists p0,
      In l0 rd /\
      blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) f = true /\
      In p0 ps0 /\
      id0 = getPhiNodeID p0 /\
      used_in_fdef (getPhiNodeID p0) f = false
| AC_vsubst v0 =>
    exists l0, exists ps0, exists cs0, exists tmn0, exists p0,
      In l0 rd /\
      blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) f = true /\
      In p0 ps0 /\
      id0 = getPhiNodeID p0 /\
      assigned_phi v0 p0
| _ => False
end.

Definition wf_phi_actions f rd (acs:AssocList action) : Prop := 
Forall (wf_phi_action f rd) acs.

(***************************************************************)
(* The properties of elim_phi_step *)
Lemma elim_phi_step_inl_spec: forall f1 f2 rd (H: elim_phi_step rd f1 = inl f2),
  elim_phi_fdef rd f1 = nil /\ f2 = f1.
Proof.
  unfold elim_phi_step.
  intros f0 f2 rd.
  destruct (elim_phi_fdef rd f0); intros H; inv H; auto.
Qed.

Lemma elim_phi_step_inr_spec: forall f1 f2 rd (H: elim_phi_step rd f1 = inr f2),
  elim_phi_fdef rd f1 <> nil /\ f2 = AVLComposedPass.run (elim_phi_fdef rd f1) f1.
Proof.
  unfold elim_phi_step.
  intros f0 f2 rd.
  destruct (elim_phi_fdef rd f0); intros H; inv H.
    split; auto.
      congruence.
Qed.

(* This is similiar to eliminate_phi_true_spec, could be merged? *)
Lemma elim_phi_phi_spec: forall S M f b p 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f) acs rd
  (Hreach : reachablity_analysis f = ret rd) (Hrd: In (getBlockLabel b) rd) 
  (HPinF: phinodeInFdefBlockB p f b = true) elt
  (Helim: (elt::acs) = elim_phi_phi f acs p),
  wf_phi_action f rd elt.
Proof.
  destruct p as [pid pty pvls].
  unfold elim_phi_phi.
  intros. 
  bdestruct HPinF as HPinB HBinF.
  destruct b as [l0 [ps0 cs0 tmn0]].
  simpl in HPinB. apply InPhiNodesB_In in HPinB.
  remember (vmem2reg.remove_redundancy nil 
             (value_id pid :: List.map fst pvls)) as vs.
  apply remove_redundancy_spec in Heqvs.
  destruct Heqvs as [Hinc Hnodup].
  rewrite <- fst_split__map_fst in Hinc.
  assert (Hreach':=Hreach).
  eapply reachablity_analysis__reachable in Hreach'; eauto.
  destruct vs as [|v1 vs'].
  Case "1".
    repeat destruct_if; try cons_self__False_tac.
      simpl. exists l0. exists ps0. exists cs0. exists tmn0. 
      exists (insn_phi pid pty pvls).
      split; auto.
  Case "2".
    destruct v1 as [vid1 | vc1].
    SCase "2.1".
      destruct vs' as [|v2].
      SSCase "2.1.1: pid = phi pid ... pid".
        elimtype False.
        eapply identity_phi_cannot_be_in_reachable_blocks; eauto 1.
        constructor.
          intros v1 l1 Hin.
          apply in_split_l in Hin. simpl in Hin.
          assert (pid = vid1) as EQ.
            assert (In (value_id pid) (value_id vid1 :: nil)) as Hin1.
              apply Hinc; simpl; auto.
              destruct_in Hin1; try tauto. 
            congruence.
          subst.
          assert (In v1 (value_id vid1 :: fst (split pvls))) as Hin'.
            simpl. auto.
          apply Hinc in Hin'.
          destruct_in Hin'; try tauto. 
         
      SSCase "2.1.2".
        destruct vs' as [|].
        SSSCase "2.1.2.1: pid = phi v2 .. v2 . pid".
          destruct_dec; inv Helim.
          SSSSCase "pid=vid1".
            simpl. exists l0. exists ps0. exists cs0. exists tmn0. 
            exists (insn_phi vid1 pty pvls).
            repeat (split; auto).
            SSSSSCase "2.1.2.1.1".
                apply split_l_in; auto.
                assert (In v2 (value_id vid1 :: v2 :: nil)) as Hin.
                  simpl; auto.
                apply Hinc in Hin.
                destruct_in Hin.
                  simpl in Hnodup. inv Hnodup. simpl in H1. tauto.
            SSSSSCase "2.1.2.1.2".
                intros v1 l1 Hin.  
                apply in_split_l in Hin. simpl in Hin.
                assert (In v1 (value_id vid1 :: fst (split pvls))) as Hin'.
                  simpl. auto.
                apply Hinc in Hin'.
                destruct_in Hin'; auto.
                destruct Hin'; subst; tauto.    
          SSSSCase "pid<>vid1".
            simpl. exists l0. exists ps0. exists cs0. exists tmn0. 
            exists (insn_phi pid pty pvls).
            repeat (split; auto).
            SSSSSCase "2.1.2.1.1".
                apply split_l_in; auto.
                assert (In (value_id vid1) (value_id vid1 :: v2 :: nil)) as Hin.
                  simpl; auto.
                apply Hinc in Hin.
                destruct_in Hin. 
                  congruence.
            SSSSSCase "2.1.2.1.2".    
                assert (v2 = value_id pid) as EQ.         
                  assert (In (value_id pid) (value_id pid :: fst (split pvls))) 
                    as Hin0.
                    simpl; auto.
                  apply Hinc in Hin0.
                  destruct_in Hin0.
                    congruence.
                subst.
                intros v1 l1 Hin.  
                apply in_split_l in Hin. simpl in Hin.
                assert (In v1 (value_id pid :: fst (split pvls))) as Hin'.
                  simpl. auto.
                apply Hinc in Hin'.
                destruct_in Hin'; auto.
                destruct Hin'; subst; tauto.
        SSSCase "2.1.2.2".
          repeat destruct_if; try cons_self__False_tac.
          simpl. exists l0. exists ps0. exists cs0. exists tmn0. 
          exists (insn_phi pid pty pvls).
          split; auto.
    
    SCase "2.2".
      destruct vs' as [|? vs'].
      SSCase "2.2.1: pid = vc".
        assert (In (value_id pid) (value_id pid :: fst (split pvls))) as Hin.
          simpl; auto.
        apply Hinc in Hin.
        destruct_in Hin.
          congruence.
    
      SSCase "2.2.2".
        destruct vs' as [|? vs'].
        SSSCase "2.2.2.1: pid = phi pid c .. c . pid".
          inv Helim. 
          assert (v = value_id pid) as EQ.         
            assert (In (value_id pid) (value_id pid :: fst (split pvls))) 
              as Hin0.
              simpl; auto.
            apply Hinc in Hin0.
            destruct_in Hin0.
              congruence.
          subst.
          simpl. exists l0. exists ps0. exists cs0. exists tmn0. 
          exists (insn_phi pid pty pvls).
          repeat (split; auto).
          SSSSSCase "2.2.2.1.1".
            apply split_l_in; auto.
            assert (In (value_const vc1) (value_const vc1 :: value_id pid :: nil))  
              as Hin.
              simpl; auto.
            apply Hinc in Hin.
            destruct_in Hin. 
              congruence.
          SSSSSCase "2.2.2.1.2".    
            intros v1 l1 Hin.  
            apply in_split_l in Hin. simpl in Hin.
            assert (In v1 (value_id pid :: fst (split pvls))) as Hin'.
              simpl. auto.
            apply Hinc in Hin'.
            destruct_in Hin'; auto.
            destruct Hin'; subst; tauto.

        SSSCase "2.2.2.2".
          repeat destruct_if; try cons_self__False_tac.
          simpl. exists l0. exists ps0. exists cs0. exists tmn0. 
          exists (insn_phi pid pty pvls).
          repeat split; auto.
Qed.

Lemma elim_phi_phi__eq_spec: forall init f p0,
  elim_phi_phi f init p0 = init \/ 
  exists elt, elim_phi_phi f init p0 = elt :: init.
Proof.
  unfold elim_phi_phi.
  destruct p0 as [a b c].
  destruct (remove_redundancy nil (value_id a :: List.map fst c)) as [|v l0].
    destruct_if; auto.
    destruct_if; eauto.

    destruct v.
      destruct l0 as [|v l0]; eauto.
      destruct l0 as [|v' l0].
        destruct_dec; eauto.
        destruct_if; eauto.
        destruct_if; eauto.

      destruct l0 as [|v l0]; eauto.
      destruct l0 as [|v' l0]; eauto.
        destruct_if; eauto.
        destruct_if; eauto.
Qed.

Lemma elim_phi_phi__in_spec: forall init f p0 elt
  (Hin: In elt (elim_phi_phi f init p0)) (Hnin: ~ In elt init),
  elim_phi_phi f init p0 = elt :: init.
Proof.
  intros.
  destruct (elim_phi_phi__eq_spec init f p0) as [H | [elt' H]].
  Case "1".
    rewrite <- H in Hnin. tauto.
  Case "2".
    rewrite H in Hin.
    simpl in Hin.
    destruct Hin; subst; auto.
      tauto.
Qed.

Lemma fold_left_elim_phi_phi__elim_phi_phi: forall 
  (f : fdef) (ps0 : list phinode) (elt : atom * action) init,
  In elt (fold_left (elim_phi_phi f) ps0 init) ->
  In elt init \/
  exists p0 : phinode,
    exists acs : AssocList action,
      In p0 ps0 /\ elim_phi_phi f acs p0 = elt :: acs.
Proof.
  induction ps0 as [|p0 ps0]; simpl; intros; auto.
    apply IHps0 in H.
    destruct H as [H | [p1 [acs [Hin EQ]]]].
    Case "1".
      destruct (In_dec id_action_dec elt init); auto.
      right.
      apply elim_phi_phi__in_spec in H; auto.
      exists p0. exists init. auto.
    Case "2".
      right.
      exists p1. exists acs. auto.
Qed.

Lemma elim_phi_phis__elim_phi_phi: forall elt f ps0
  (Hin : In elt (elim_phi_phis f ps0)),
  exists p0, exists acs, In p0 ps0 /\ elim_phi_phi f acs p0 = elt :: acs.
Proof.
  unfold elim_phi_phis.
  intros.
  apply fold_left_elim_phi_phi__elim_phi_phi in Hin.
  destruct Hin as [Hin | Hin]; auto.
    inv Hin.
Qed.

(* well-formed *)
Lemma elim_phi_fdef__wf_actions: forall s m f rd actions
  (Hwf: wf_fdef s m f) (Huniq: uniqFdef f)
  (Hreach : reachablity_analysis f = ret rd)
  (Hfind: actions = elim_phi_fdef rd f),
  wf_phi_actions f rd actions.
Proof.
  destruct f as [fh bs]. 
  intros.
  simpl in Hfind.
  apply Forall_forall.
  intros elt Hin.
  subst.
  apply in_flat_map in Hin.
  destruct Hin as [[l0 [ps0 cs0 tmn0]] [Hin1 Hin2]].
  simpl in Hin2.
  destruct_if.
  apply elim_phi_phis__elim_phi_phi in Hin2.
  destruct Hin2 as [p0 [acs [Hin Heim]]].
  eapply elim_phi_phi_spec with (b:=(l0, stmts_intro ps0 cs0 tmn0)); eauto 1. 
    apply andb_true_iff; simpl.
    split; solve_in_list.
Qed.

Lemma elim_phi_phi_spec': forall f id0 ac0 p acs
  (Helim: ((id0, ac0)::acs) = elim_phi_phi f acs p),
  id0 = getPhiNodeID p.
Proof.
  destruct p as [pid pty pvls].
  unfold elim_phi_phi.
  intros. 
  destruct (vmem2reg.remove_redundancy nil 
              (value_id pid :: List.map fst pvls)).
    destruct_if; try cons_self__False_tac.
    destruct_if; try cons_self__False_tac; auto.

    destruct v.
      destruct l0.
        inv Helim; auto.
        destruct l0.
          destruct_dec; inv Helim; auto.
          destruct_if; try cons_self__False_tac.
          destruct_if; try cons_self__False_tac; auto.
      destruct l0.
        inv Helim; auto.
        destruct l0.
          inv Helim; auto.
          destruct_if; try cons_self__False_tac.
          destruct_if; try cons_self__False_tac; auto.
Qed.

(* inclusion *)
Lemma elim_phi_block__incl: forall rd f b,
  forall (a : atom) (Hin: a `in` dom (elim_phi_block rd f b)), 
  In a (getStmtsLocs (snd b)).
Proof.
  destruct b as [? []]. simpl.
  destruct_if; intros.
    apply indom_lookupAL_Some in Hin.
    destruct Hin as [gv0 Hin].
    apply lookupAL_in in Hin.
    apply elim_phi_phis__elim_phi_phi in Hin.
    destruct Hin as [p0 [acs [Hin EQ]]].
    symmetry in EQ.
    apply elim_phi_phi_spec' in EQ; subst.
    xsolve_in_list.

    simpl in Hin. fsetdec.
Qed.

Lemma elim_phi_blocks__incl: forall rd f bs,
  forall a : atom,
  a `in` dom (flat_map (elim_phi_block rd f) bs) -> 
  In a (getBlocksLocs bs).
Proof.
  induction bs as [|b bs]; simpl; intros; subst.
    fsetdec.
    
    apply in_or_app.
    rewrite dom_app in H.
    apply AtomSetFacts.union_iff in H.
    destruct H as [H | H]; eauto using elim_phi_block__incl.
Qed.

(* uniqueness *)
Lemma fold_elim_phi_phi__uniq: forall f ps acc
  (Huniq: NoDup (getPhiNodesIDs ps++List.map fst acc)),
  uniq (fold_left (elim_phi_phi f) ps acc).
Proof.
  induction ps as [|p ps]; simpl; intros; subst.
    apply NoDup_fst__uniq; auto.
 
    destruct (elim_phi_phi__eq_spec acc f p) as [H | [[id0 ac0] H]]; rewrite H.
      apply IHps.
      inversion Huniq; auto.

      symmetry in H.
      apply elim_phi_phi_spec' in H.
      subst id0. 
      apply IHps.
      simpl.
      rewrite_env ((getPhiNodesIDs ps ++ [getPhiNodeID p]) ++ List.map fst acc).
      rewrite_env ((getPhiNodeID p :: getPhiNodesIDs ps) ++ List.map fst acc) 
        in Huniq.
      apply NoDup_split' in Huniq.
      destruct Huniq as [J1 [J2 J3]].
      apply NoDup_app; auto.
        apply NoDup_commut; auto.

        intros a Hin.
        apply J3.
        apply in_app_or in Hin.
        simpl in *.
        tauto.
Qed.

Lemma elim_phi_phis__uniq: forall f ps
  (Huniq: NoDup (getPhiNodesIDs ps)),
  uniq (elim_phi_phis f ps).
Proof.
  unfold elim_phi_phis.
  intros.
  apply fold_elim_phi_phi__uniq; simpl; simpl_env; auto.
Qed.

Lemma elim_phi_block__uniq: forall rd f b
  (Huniq: NoDup (getStmtsLocs (snd b))),
  uniq (elim_phi_block rd f b).
Proof.
  destruct b as [? []]. simpl.
  intros.
  destruct_if; auto.
    split_NoDup.
    eapply elim_phi_phis__uniq; eauto.
Qed.

Lemma elim_phi_blocks__uniq: forall rd f bs (Huniq: NoDup (getBlocksLocs bs)),
  uniq (flat_map (elim_phi_block rd f) bs).
Proof.
  induction bs as [|b bs]; simpl; intros; subst.
    constructor.

    apply uniq_app_iff.
    assert (J:=Huniq).
    apply NoDup_split in J. destruct J as [J1 J2].
    split.
      eapply elim_phi_block__uniq; eauto.
    split; auto.
      apply disj__disjoint with (A1:=getStmtsLocs (snd b)) (B1:=getBlocksLocs bs); 
        auto.
        intros. eapply NoDup_disjoint'; eauto.
        apply elim_phi_block__incl; auto.
        apply elim_phi_blocks__incl; auto.
Qed.

Lemma elim_phi_fdef__uniq: forall rd f (HuniqF: uniqFdef f),
  uniq (elim_phi_fdef rd f).
Proof.
  destruct f as [[] bs].
  simpl.
  intros.
  destruct HuniqF.
  split_NoDup.
  apply elim_phi_blocks__uniq; auto.
Qed.

(* reachablity *)
Lemma elim_phi_block__reach: forall rd f l0 sts0 acs1 ac acs2
  (Hfind: elim_phi_block rd f (l0, sts0) = acs1 ++ ac :: acs2),
  In l0 rd.
Proof.
  simpl. intros.
  destruct_if; auto.
    symmetry in H0. contradict H0. destruct sts0. apply app_cons_not_nil.
Qed.

Lemma elim_phi_blocks__reach': forall fh bs
  (HuniqF : uniqFdef (fdef_intro fh bs)) (pid : id) (rd : list l) (id0 : atom)
  (Hin : id0 `in` dom (List.flat_map (elim_phi_block rd (fdef_intro fh bs)) bs)),
  exists l0 : l, exists sts0 : stmts,
    blockInFdefB (l0, sts0) (fdef_intro fh bs) /\
    In id0 (getStmtsLocs sts0) /\
    In l0 rd.
Proof.
  intros.
  apply binds_In_inv in Hin.
  destruct Hin as [a Hin].
  unfold binds in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [b [Hin1 Hin2]].
  assert (J:=Hin2).
  apply binds_In in J.
  apply elim_phi_block__incl in J.
  destruct b as [l0 sts0].
  exists l0. exists sts0.
  split. simpl. solve_in_list.
  split; auto.
    apply in_split in Hin2.
    destruct Hin2 as [l1 [l2 Hfind]].   
    apply elim_phi_block__reach in Hfind; auto.
Qed.

Lemma elim_phi_blocks__reach'': forall (fh : fheader) (bs : blocks)
  (HuniqF : uniqFdef (fdef_intro fh bs)) (pid : id) (rd : list l) (id0 : atom)
  (l0 : l) (sts0 : stmts)
  (H : lookupBlockViaIDFromFdef (fdef_intro fh bs) id0 = ret (l0, sts0))
  (Hin : id0 `in` dom (flat_map (elim_phi_block rd (fdef_intro fh bs)) bs)),
  In l0 rd.
Proof.
  intros.
  eapply elim_phi_blocks__reach' in Hin; eauto.
  destruct Hin as [l1 [sts1 [J1 [J2 J3]]]].
  assert (J':=H).
  apply lookupBlockViaIDFromBlocks__InGetBlockIDs in J'.
  apply in_getStmtsIDs__in_getStmtsLocs in J'.
  assert ((l1, sts1) = (l0, sts0)) as EQ.
    eapply block_eq2; eauto 1.
      solve_blockInFdefB.
  inv EQ. auto.
Qed.

Lemma elim_phi_fdef__isReachableFromEntry: forall s m f
  (HwfF: wf_fdef s m f)
  (HuniqF: uniqFdef f) rd actions
  (Hreach: ret rd = reachablity_analysis f)
  (Hfind: actions = elim_phi_fdef rd f),
  forall id0 (a:avertexes actions (index (value_id id0))) (b : block),
  lookupBlockViaIDFromFdef f id0 = ret b ->
  isReachableFromEntry f b.
Proof.
  intros. 
  destruct f as [fh bs]. 
  destruct b as [l0 sts0].
  eapply reachablity_analysis__reachable; eauto.
  subst. 
  destruct a as [Hin | Hin].
  Case "1".
    eapply elim_phi_blocks__reach''; eauto.
  Case "2".
    destruct Hin as [id1 [ac1 [Hin Ha2v]]].
    apply action2id__inv in Ha2v; subst ac1.
    assert (Hin':=Hin).
    apply binds_In in Hin'.
    simpl in Hin'.
    eapply elim_phi_blocks__reach' in Hin'; eauto.
    destruct Hin' as [l1 [sts1 [J1 [J2 J3]]]].
    assert (Huniq:=HuniqF).
    apply uniqF__uniqBlocksLocs in Huniq.    
    remember (elim_phi_fdef rd (fdef_intro fh bs)) as acs.
    eapply elim_phi_fdef__wf_actions in Heqacs; eauto.
    eapply Forall_forall in Hin; eauto.
    destruct Hin as 
      [l2 [ps0 [cs0 [tmn0 [p0 [Hrd [HBinF [Hinps [EQ Hassign]]]]]]]]]; subst.
    eapply assigned_phi__domination in Hassign; eauto.
    simpl in Hassign.
    assert (id_in_reachable_block (fdef_intro fh bs) (getPhiNodeID p0)) as Hinrd.
      intros b0 Hlk.
      assert (lookupBlockViaIDFromFdef (fdef_intro fh bs) (getPhiNodeID p0) =
                Some (l2, stmts_intro ps0 cs0 tmn0)) as Hlk'.
        eapply inGetBlockIDs__lookupBlockViaIDFromFdef; eauto.
        simpl. xsolve_in_list.
      uniq_result.
      eapply reachablity_analysis__reachable; eauto.
    eapply idDominates_id_in_reachable_block in Hinrd; eauto.
    apply Hinrd in H.
    eapply reachable__reachablity_analysis; eauto.
Qed.

(* acyclicity *)
Lemma elim_phi_fdef__valueDominates: forall s m f
  (HwfF:wf_fdef s m f)
  (HuniqF: uniqFdef f) actions rd 
  (Hreach: ret rd = reachablity_analysis f)
  (Hfind: actions = elim_phi_fdef rd f) id1 v2
  (Hin: In (id1, AC_vsubst v2) actions),
  valueDominates f v2 (value_id id1).
Proof.
  intros.
  assert (Hwfa:=HwfF). 
  eapply elim_phi_fdef__wf_actions in Hwfa; eauto. 
  eapply Forall_forall in Hin; eauto.
  simpl in Hin.
  destruct Hin as 
    [l0 [ps0 [cs0 [tmn0 [p0 [Hrd [HBInF [Hinps [EQ Hassign]]]]]]]]]; subst.
  eapply assigned_phi__domination; eauto.
Qed.

Lemma elim_phi_fdef__walk_valueDominates: forall s m f
  (HwfF:wf_fdef s m f)
  (HuniqF: uniqFdef f) actions rd
  (Hreach: ret rd = reachablity_analysis f)
  (Hfind: actions = elim_phi_fdef rd f)
  id1 v2 vl al (Hnnil: vl <> V_nil)
  (Hw: D_walk (avertexes actions) (aarcs actions) 
         (index (value_id id1)) (index v2) vl al),
  valueDominates f (value_id id1) v2.
Proof.
  intros.
  remember (avertexes actions) as V.
  remember (aarcs actions) as A.
  remember (index (value_id id1)) as x.
  remember (index v2) as y.
  generalize dependent id1.
  generalize dependent v2.
  induction Hw; intros; subst.
  Case "1".
    congruence.
  Case "2".
    destruct y as [[id3|]]; tinv H0.
    match goal with
    | H0: aarcs _ _ |- _ =>
      apply aarcs__In in H0;
      eapply elim_phi_fdef__valueDominates in H0; eauto 1
    end.
    destruct vl as [|v' vl]; inv Hw; auto.
    eapply valueDominates_trans; eauto 1.
      apply IHHw; auto. 
        intro J. inv J.
Qed.

Lemma elim_phi_fdef__acyclic: forall s m f rd
  (HwfF: wf_fdef s m f) (HuniqF: uniqFdef f)
  (Hreach: ret rd = reachablity_analysis f),
  acyclic_actions (elim_phi_fdef rd f).
Proof.
  unfold acyclic_actions. intros. 
  assert (Hwfa:=HwfF). 
  eapply elim_phi_fdef__wf_actions in Hwfa; eauto. 
  destruct vl as [|v vl]; auto.
  assert (Hin:=Hcyc). apply DW_endx_inv in Hin.
  assert (J:=Hcyc).
  apply D_walk_head_inv in J.
  destruct J as [[EQ1 [EQ2 EQ3]]|[id0 EQ]]; subst; try congruence.
  eapply elim_phi_fdef__walk_valueDominates in Hcyc; eauto.
  Case "1".
    simpl in Hcyc.
    assert (id_in_reachable_block f id0) as Hreach'.
      unfold id_in_reachable_block.
      intros.
      eapply elim_phi_fdef__isReachableFromEntry in Hin; eauto.
    apply Hcyc in Hreach'.
    eapply idDominates_acyclic in Hreach'; eauto.
    SCase "1.1".
      inv Hreach'.
    SCase "1.2".
      intros.
      eapply elim_phi_fdef__isReachableFromEntry in Hin; eauto.     
  Case "2".
    intro H. inv H.
Qed.

(* AC_remove *)
Lemma elim_phi_fdef__wf_AC_remove: forall s m f rd
  (HwfF: wf_fdef s m f) (HuniqF: uniqFdef f)
  (Hreach : reachablity_analysis f = ret rd),
  wf_AC_remove (elim_phi_fdef rd f).
Proof.
  intros.
  eapply elim_phi_fdef__wf_actions in HwfF; eauto.
  apply Forall_forall.
  intros [id0 []] Hin; auto.
  eapply Forall_forall in Hin; eauto.
  intros [id1 [ac1 [Hin' Ha2v]]].
  apply action2id__inv in Ha2v; subst ac1.
  eapply Forall_forall in Hin'; eauto.
  simpl in *.
  destruct Hin as 
    [l0 [ps0 [cs0 [tmn0 [p0 [Hrd0 [HBinF0 [Hinps0 [EQ Hnnused]]]]]]]]]; subst.
  destruct Hin' as 
    [l1 [ps1 [cs1 [tmn1 [p1 [Hrd1 [HBinF1 [Hinps1 [EQ Hassign]]]]]]]]]; subst.
  assert (used_in_phi (getPhiNodeID p0) p1 = true) as Huse.
    apply assigned_phi__valueInInsnOperands in Hassign.
    apply valueInPhiOperands__used_in_phi; auto.
  eapply used_in_fdef__used_in_phi in HBinF1; eauto.  
  congruence.
Qed.

Lemma elim_phi_fdef_spec: forall s m f rd
  (HwfF: wf_fdef s m f) actions
  (HuniqF: uniqFdef f)
  (Hreach : reachablity_analysis f = ret rd)
  (Hfind: actions = elim_phi_fdef rd f),
  uniq actions /\ acyclic_actions actions /\ wf_AC_remove actions.
Proof.
  intros; subst.
  split.
    eapply elim_phi_fdef__uniq; eauto.
  split.
    eapply elim_phi_fdef__acyclic; eauto.
    eapply elim_phi_fdef__wf_AC_remove; eauto.
Qed.

Lemma elim_phi_fdef__wf_actions_uniq: forall s m f rd actions
  (Hwf: wf_fdef s m f) (Huniq: uniqFdef f)
  (Hreach : reachablity_analysis f = ret rd)
  (Hfind: actions = elim_phi_fdef rd f),
  wf_phi_actions f rd actions /\ uniq actions.
Proof.
  intros; subst.
  split.
    eapply elim_phi_fdef__wf_actions; eauto.
    eapply elim_phi_fdef__uniq; eauto.
Qed.

(* Properties of wf_phi_actions *)
Lemma subst_non_remove__wf_phi_action: forall f rd id0 ac0 id1 ac1 
  (Hwf: wf_phi_action f rd (id1, ac1)) v0 (Ha2v: action2value ac0 = Some v0)
  (Hwf': wf_phi_action f rd (id0, ac0)) (Hneq: id0 <> id1),
  wf_phi_action (apply_action f (id0, ac0)) rd (id1, subst_action id0 v0 ac1).
Proof.
  simpl.
  intros.
  destruct ac0 as [|v0'|]; tinv Hwf'; inv Ha2v.
  destruct Hwf' as 
    [l1 [ps1 [cs1 [tmn1 [p1 [Hrd1 [HBinF1 [Hin1 [EQ1 Hassign1]]]]]]]]]; subst.
  destruct ac1; simpl; auto.
  Case "1".
    destruct Hwf as 
      [l0 [ps0 [cs0 [tmn0 [p0 [Hrd [HBinF [Hin [EQ Hnnuse]]]]]]]]]; subst.
    exists l0. 
    exists (remove_phinodes (getPhiNodeID p1) 
             (List.map (subst_phi (getPhiNodeID p1) v0) ps0)).
    exists (remove_cmds (getPhiNodeID p1)
             (List.map (subst_cmd (getPhiNodeID p1) v0) cs0)).
    exists (subst_tmn (getPhiNodeID p1) v0 tmn0).
    exists (subst_phi (getPhiNodeID p1) v0 p0).
    split; auto.
    split. 
      eapply remove_subst_fdef__blockInFdefB with (id0:=getPhiNodeID p1)
        (id1:=getPhiNodeID p1)(v0:=v0)
        in HBinF; eauto 1.
    split. apply subst_phi__remove_subst_phis; auto.
    split. rewrite subst_phi__getPhiNodeID; auto.
       
      rewrite subst_phi__getPhiNodeID.
      apply remove_unused_in_fdef.
      apply subst_unused_in_fdef'; auto.
        eapply used_in_fdef__used_in_phi_value; eauto.
          apply assigned_phi__valueInInsnOperands; auto.

  Case "2".
    destruct Hwf as 
      [l0 [ps0 [cs0 [tmn0 [p0 [Hrd [HBinF [Hin [EQ Hassign0]]]]]]]]]; subst.
    exists l0. 
    exists (remove_phinodes (getPhiNodeID p1) 
             (List.map (subst_phi (getPhiNodeID p1) v0) ps0)).
    exists (remove_cmds (getPhiNodeID p1)
             (List.map (subst_cmd (getPhiNodeID p1) v0) cs0)).
    exists (subst_tmn (getPhiNodeID p1) v0 tmn0).
    exists (subst_phi (getPhiNodeID p1) v0 p0).
    split; auto.
    split. 
      eapply remove_subst_fdef__blockInFdefB with (id0:=getPhiNodeID p1)
        (id1:=getPhiNodeID p1)(v0:=v0)
        in HBinF; eauto 1.
    split. apply subst_phi__remove_subst_phis; auto.
    split. 
      rewrite subst_phi__getPhiNodeID; auto.

      inv Hassign0.
      constructor.
        destruct Hex as [l2 Hin'].
        exists l2. 
        apply subst_list_value_l__In; auto.

        intros v1 l2 Hin'.
        simpl in Hneq.
        apply subst_list_value_l__In' in Hin'.
        destruct Hin' as [v' [EQ Hin']]; subst.
        apply Hassign in Hin'.
        destruct Hin' as [EQ | EQ]; subst; auto.
        simpl. destruct_dec.
Qed.

Lemma subst_remove__wf_phi_action: forall f rd id0 id1 ac1 
  (Hwf: wf_phi_action f rd (id1, ac1))
  (Hneq: id0 <> id1),
  wf_phi_action (apply_action f (id0, AC_remove)) rd (id1, ac1).
Proof.
  simpl.  
  intros.
  destruct ac1; simpl; auto.
    destruct Hwf as 
      [l0 [ps0 [cs0 [tmn0 [p0 [Hrd [HBinF [Hin [EQ Hnnuse]]]]]]]]]; subst.
    exists l0. 
    exists (remove_phinodes id0 ps0).
    exists (remove_cmds id0 cs0).
    exists tmn0.
    exists p0.
    split; auto.
    split. apply remove_fdef__blockInFdefB with (id0:=id0) in HBinF; auto.
    split. 
      apply filter_In.
      split; auto.
        destruct_dec.
    split; auto.
      apply remove_unused_in_fdef; auto.

    destruct Hwf as 
      [l0 [ps0 [cs0 [tmn0 [p0 [Hrd [HBinF [Hin [EQ Hassign]]]]]]]]]; subst.
    exists l0. 
    exists (remove_phinodes id0 ps0).
    exists (remove_cmds id0 cs0).
    exists tmn0.
    exists p0.
    split; auto.
    split. apply remove_fdef__blockInFdefB with (id0:=id0) in HBinF; auto.
    split. 
      apply filter_In.
      split; auto.
        destruct_dec.
    split; auto.
Qed.

Lemma list_subst_non_remove__wf_phi_actions: forall id0 ac0 acs f rd
  (Hwf : wf_phi_actions f rd acs) (Hnotin : id0 `notin` dom acs) v
  (Hwf': wf_phi_action f rd (id0, ac0)) (HeqR : ret v = action2value ac0),
  wf_phi_actions (apply_action f (id0, ac0)) rd
    (ListMap.map (subst_action id0 v) acs).
Proof.
  induction acs as [|[] acs]; simpl; intros.
    constructor.

    inv Hwf.
    constructor.
      apply subst_non_remove__wf_phi_action; auto.
      apply IHacs; auto.
Qed.

Lemma list_subst_remove__wf_phi_actions: forall id0 ac0 f rd acs
  (Hwf : wf_phi_actions f rd acs) (Hnotin : id0 `notin` dom acs)
  (HeqR : merror = action2value ac0),
  wf_phi_actions (apply_action f (id0, ac0)) rd acs.
Proof.
  intros.
  destruct ac0; inv HeqR.
  generalize dependent f.
  induction acs as [|[] acs]; simpl; intros.
    constructor.
  
    inv Hwf.
    constructor.
      apply subst_remove__wf_phi_action; auto.
      apply IHacs; auto.
Qed.

Lemma list_subst_actions__wf_phi_actions: forall id0 ac0 f rd
  acs (Hwf: wf_phi_actions f rd acs) (Hnotin: id0 `notin` dom acs)
  (Hwf': wf_phi_action f rd (id0, ac0)),
  wf_phi_actions (apply_action f (id0, ac0)) rd
    (ListComposedPass.subst_actions id0 ac0 acs).
Proof.
  unfold ListComposedPass.subst_actions.
  intros.
  remember (action2value ac0) as R.
  destruct R.
    apply list_subst_non_remove__wf_phi_actions; auto.
    apply list_subst_remove__wf_phi_actions; auto.
Qed.

Lemma wf_phi_actions_cons_inv: forall f f' rd id0 ac0 
  actions (Huniq': uniq actions)
  (Hnotin: id0 `notin` dom actions) s m (HwfF: wf_fdef s m f) 
  (Heq: apply_action f (id0, ac0) = f')
  (Hwf: wf_phi_actions f rd ((id0, ac0) :: actions)),
  wf_phi_action f rd (id0, ac0) /\
  wf_phi_actions (apply_action f (id0, ac0)) rd
                 (ListComposedPass.subst_actions id0 ac0 actions).
Proof.
  intros.
  inv Hwf.
  split; auto.
    apply list_subst_actions__wf_phi_actions; auto.
Qed.

(* pipelined phinode elimination is correct. *)
Lemma apply_phi_action_sim_wfS: forall (los : layouts) (nts : namedts)
  (main : id) (VarArgs : list (GVsT DGVs))
  (Ps1 : list product) (Ps2 : list product) id' ac' f1 f2 rd
  (Hreach: reachablity_analysis f2 = ret rd)
  (Hwf: wf_phi_action f2 rd (id', ac'))
  (Heqf1: f1 = apply_action f2 (id', ac'))
  S2 S1 (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (Hok: defined_program S2 main VarArgs)
  (HwfS : wf_system S2),
  program_sim S1 S2 main VarArgs /\
    wf_system S1 /\ defined_program S1 main VarArgs.
Proof.
  intros.
  destruct ac' as [|v'|t']; simpl in *; subst; try tauto.
  Case "remove".
    destruct Hwf as 
      [l0 [ps0 [cs0 [tmn0 [p0 [Hrd [HBinF [Hin [EQ Hnnuse]]]]]]]]]; subst.
    eapply eliminate_nonused_phis_sim_wfS; eauto 1.
  Case "vsubst".
    destruct Hwf as 
      [l0 [ps0 [cs0 [tmn0 [p0 [Hrd [HBinF [Hin [EQ Hassign]]]]]]]]]; subst.
    eapply eliminate_assigned_phis_sim_wfS; eauto 1.
Qed.

Definition pipelined_elim_phi_sim_wfS_prop Ps1 Ps2 los nts main
  VarArgs (n:nat) := forall actions
  (Hlen: (length actions = n)%nat) f1 f2 rd
  (Hrd: reachablity_analysis f1 = ret rd)
  (Heqactions : wf_phi_actions f1 rd actions) (Huniq: uniq actions)
  (Hpass : pipelined_actions actions f1 = f2) S1 S2
  (Heq3 : S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq4 : S2 = [module_intro los nts
                 (Ps1 ++ product_fdef f1 :: Ps2)])
  (HwfS : wf_system S2) (Hok : defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\
    wf_system S1 /\ defined_program S1 main VarArgs.

Lemma pipelined_elim_phi_sim_wfS_aux: forall Ps1 Ps2 los nts main
  VarArgs n, pipelined_elim_phi_sim_wfS_prop  
  Ps1 Ps2 los nts main VarArgs n.
Proof.
  intros until n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold pipelined_elim_phi_sim_wfS_prop, pipelined_actions in *.
  destruct actions as [|[id' ac'] actions].
  Case "base".
    intros.
    simpl in Hpass.
    repeat subst.
    split; auto using program_sim_refl.
  Case "ind".
Local Opaque apply_action.
    unfold_substs_actions. simpl. 
    intros. subst x. 
    inversion Huniq as [|A B C Huniq' Hnotin]; subst A B C.
    assert (Hwf:
      wf_fdef [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]
              (module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)) 
              f1 /\
      uniqFdef f1).
      apply wf_single_system__wf_uniq_fdef; subst; auto.
    destruct Hwf as [HwfF HuniqF].
    assert (HuniqF':=HuniqF). 
    remember (apply_action f1 (id', ac')) as f1'.
    symmetry in Heqf1'.
    assert (J:=Heqf1').
    eapply wf_phi_actions_cons_inv in J; eauto.
    destruct J as [Hwfaction Hwf_actions].
    subst S2.
    assert (Hok':=Hok).
    eapply apply_phi_action_sim_wfS with (S1:=
        [module_intro los nts 
          (Ps1 ++ product_fdef (apply_action f1 (id', ac')) :: Ps2)]) 
        in Hok'; try solve [eauto | subst f1; eauto].
    SCase "1". 
      destruct Hok' as [Hsim [Hwf Hok']].
      eapply Hrec with (S2:=
        [module_intro los nts
          (Ps1 ++ product_fdef (apply_action f1 (id', ac')) :: Ps2)]) 
        in Hwf_actions; 
        try solve [eauto 2 | 
                   congruence |
                   apply list_subst_actions__uniq; auto |
                   rewrite <- list_subst_actions__length; auto].
      SSCase "1.1".
        apply program_sim_wfS_trans with (P2:=
          [module_intro los nts
              (Ps1 ++ product_fdef (apply_action f1 (id', ac')) :: Ps2)]); 
          subst; auto.
      SSCase "1.2". 
        edestruct (apply_action_reachablity_successors (id',ac') f1); eauto.
        congruence.
Transparent apply_action.
Qed.

Lemma pipelined_elim_phi_sim_wfS: forall rd f1 f2 Ps1 Ps2 los nts main
  VarArgs (actions : list (atom * action))
  (Heqactions : actions = elim_phi_fdef rd f1)
  (Hrd: reachablity_analysis f1 = ret rd)
  (Hpass : pipelined_actions actions f1 = f2) S1 S2
  (Heq3 : S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq4 : S2 = [module_intro los nts
                 (Ps1 ++ product_fdef f1 :: Ps2)])
  (HwfS : wf_system S2) (Hok : defined_program S2 main VarArgs),
  (program_sim S1 S2 main VarArgs /\
    wf_system S1 /\ defined_program S1 main VarArgs).
Proof.
  intros.
  assert (J:=pipelined_elim_phi_sim_wfS_aux Ps1 Ps2 los nts main
    VarArgs (length actions)).
  unfold pipelined_elim_phi_sim_wfS_prop in J.
  assert (wf_fdef [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]
                  (module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2))
                  f1 /\ uniqFdef f1) as G.
    subst.
    apply wf_single_system__wf_uniq_fdef in HwfS; auto.
  destruct G as [Hwf Huniq].
  eapply elim_phi_fdef__wf_actions_uniq in Heqactions; eauto.
  destruct Heqactions.
  eapply J; eauto.
Qed.

(* The correctness of fused passes. *)
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

(* LAS/LAA/SAS is correct. *)
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
    destruct R as [[l0 [ps0 cs0 tmn0]]|]; auto.
    remember (vmem2reg.find_promotable_alloca f cs0 dones) as R.
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
    assert (Hreach' : ret rd =
             reachablity_analysis
               (phinodes_placement rd pid ty al (successors f1)
                 (XATree.make_predecessors (successors f1)) f)).
      destruct HPf22 as [HPf22 _]. congruence.
    split.
      split.
      SCase "2.1".
        apply program_sim_wfS_trans with (P2:=
                [module_intro los nts (Ps1 ++
                  product_fdef
                     (vmem2reg.phinodes_placement rd pid ty al (successors f1)
                       (XATree.make_predecessors (successors f1)) f) :: Ps2)]); 
          auto; intros.
        SSCase "2.1.1".
          eapply elim_stld_sim_wfS_wfPI with
                (pinfo:=mkPhiInfo (vmem2reg.phinodes_placement rd pid ty al
                  (successors f1) (XATree.make_predecessors (successors f1)) f)
                    rd pid ty num al); eauto. 
            rewrite EQ1. destruct HPa as [Hpa1 [Hpa2 Hpa3]].
            eapply phinodes_placement_wfPI; eauto.
    
      SCase "2.2".
        destruct HPf21 as [_ [HPf21 _]].
        match goal with
        | H:wf_system [module_intro ?los ?nts (?Ps1 ++ product_fdef ?f :: ?Ps2)]
          |- context [elim_stld_fdef ?pid ?rd ?f] =>
          destruct (elim_stld_reachablity_successors pid rd f 
                      (elim_stld_fdef pid rd f)
                      [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
                      Ps1 los nts Ps2); auto
        end.
        destruct HPf22.
        split; etransitivity; eauto.
    
      SCase "2.3".
        apply change_keep_pinfo with (pinfo1:=
                   (update_pinfo pinfo
                     (vmem2reg.phinodes_placement rd pid ty al (successors f)
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
        exists (update_pinfo pinfo' (vmem2reg.elim_dead_st_fdef pid f0')).
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

(* phinodes elimination is correct. *)
Lemma Pmm2r'__elim_phi_fdef_spec: forall rd f 
  (Hreach: ret rd = reachablity_analysis f1) 
  (Hp : Pmm2r' f),
  uniq (elim_phi_fdef rd f) /\
  acyclic_actions (elim_phi_fdef rd f) /\ wf_AC_remove (elim_phi_fdef rd f).
Proof.
  intros.
  destruct Hp as [[J1 [J2 J3]] [J4 J5]].
  apply wf_single_system__wf_uniq_fdef in J2; auto.
  destruct J2.
  eapply elim_phi_fdef_spec; eauto.
    congruence.
Qed.

Lemma pipelined_elim_phi_fdef__Pmm2r': forall rd
  (Hrd: reachablity_analysis f1 = ret rd)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (Hdef: defined_program [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)] 
           main VarArgs) f (Hp : Pmm2r' f),
  Pmm2r' (ListMap.fold apply_action (substs_actions (elim_phi_fdef rd f)) f).
Proof.
  intros.
  destruct Hp as [[J11 [J12 J13]] [J21 J22]].
  split.
  Case "1".
    apply program_sim_wfS_trans with (P2:=
      [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]); auto.
      intros.
      assert (Hpass : pipelined_actions (elim_phi_fdef rd f) f = 
                      pipelined_actions (elim_phi_fdef rd f) f). auto.
      eapply pipelined_elim_phi_sim_wfS in Hpass; eauto.
        congruence.
  Case "2".
    destruct (pipelined_actions_reachablity_successors
                f (pipelined_actions (elim_phi_fdef rd f) f) (elim_phi_fdef rd f))
      as [J31 J32]; auto.
    split; etransitivity; eauto.
Qed.

Lemma elim_phi_sim_wfS: forall
  S1 S2 (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs) rd
  (Hrd: reachablity_analysis f1 = Some rd)
  (Heq1: S1 = [module_intro los nts 
      (Ps1 ++ product_fdef (SafePrimIter.iterate _ (elim_phi_step rd) f1) :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.
Proof.
  intros. subst.
  remember (SafePrimIter.iterate _ (elim_phi_step rd) f1) as f'.
  symmetry in Heqf'.
  apply SafePrimIter.iterate_prop with (P:=Pmm2r') in Heqf'.
  Case "1". 
    unfold Pmm2r' in Heqf'. tauto.
  Case "2". 
    intros f Hp.
    remember (elim_phi_step rd f) as R.
    symmetry in HeqR.
    destruct R as [f0|f0].
    SCase "2.1".
      apply elim_phi_step_inl_spec in HeqR.
      destruct HeqR as [EQ1 EQ2]; subst; auto.
    SCase "2.2".
      apply elim_phi_step_inr_spec in HeqR.
      destruct HeqR as [Hnnil EQ]; subst.
      remember (AVLComposedPass.run (elim_phi_fdef rd f) f) as f0.
      symmetry in Heqf0.
      assert (J:=Hp).
      apply Pmm2r'__elim_phi_fdef_spec with (rd:=rd) in J; auto.
      destruct J as [Huniq [Hacyc Hwfrm]].
      avl_to_list_tac.
      subst.
      apply pipelined_elim_phi_fdef__Pmm2r'; auto.
  Case "3".
    unfold Pmm2r'.
    split; auto using program_sim_refl.
Qed.

End Macro_mem2reg_fdef_sim_wfS.

(* vmem2reg O1 is correct for the function it transforms. *)
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
  destruct b as [[root [ps cs tmn]]|]; auto using program_sim_refl.
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
    destruct (vmem2reg.does_phi_elim tt).
    SCase "1.1".
      apply program_sim_wfS_trans with (P2:=
        [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]); auto; intros.
      SSCase "1.1.1".
        eapply elim_phi_sim_wfS with (f1:=f1)(rd:=rd); eauto.
          eapply macro_mem2reg_fdef_sim_wfS with (f1:=f) in HwfS; eauto.
          destruct HwfS as [_ [Hreach _]]. congruence.
      SSCase "1.1.2".
        eapply macro_mem2reg_fdef_sim_wfS with (f1:=f); eauto.
    SCase "1.2".
      eapply macro_mem2reg_fdef_sim_wfS with (f1:=f); eauto.      
  Case "2".
    split; auto using program_sim_refl.
Qed.

(* vmem2reg O1 is correct for entire programs. *)
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
  program_sim [vmem2reg_opt.run m] [m] main VarArgs /\ wf_system [vmem2reg_opt.run m] /\
    defined_program [vmem2reg_opt.run m] main VarArgs.
Proof.
  destruct m as [los nts Ps].
  unfold vmem2reg_opt.run.
  intros.
  assert (J:=@mem2reg_run_sim_wfS_aux main VarArgs los nts Ps nil).
  auto.
Qed.
