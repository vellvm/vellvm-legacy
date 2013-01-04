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

Lemma apply_action_sim_wfS_wfPI: forall (los : layouts) (nts : namedts) (fh : fheader)
  (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
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
    eapply apply_action_sim_wfS_wfPI with (S1:=
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

(* Pipelined LAS/LAA preserves CFGs. *)
Lemma apply_actions_reachablity_successors: forall actions f1 f2 
  (Hpass : fold_left apply_action actions f1 = f2),
  reachablity_analysis f2 = reachablity_analysis f1 /\
    successors f2 = successors f1.
Proof.
  induction actions as [|[id0 []] acs]; simpl; intros; subst; auto.
  Case "1".
    edestruct IHacs with (f1:=remove_fdef id0 f1) as [J1 J2]; eauto.
    assert (J:=remove_reachablity_successors id0 f1).
    destruct J as [J3 J4].
    split; etransitivity; eauto.
  Case "2".
    edestruct IHacs with (f1:=remove_fdef id0 (subst_fdef id0 v f1)) 
      as [J1 J2]; eauto.
    assert (J:=remove_subst_reachablity_successors id0 id0 v f1).
    destruct J as [J3 J4].
    split; etransitivity; eauto.
  Case "3".
    edestruct IHacs with (f1:=remove_fdef id0 
                                (subst_fdef id0 
                                   (value_const (const_undef t)) f1)) 
      as [J1 J2]; eauto.
    assert (J:=remove_subst_reachablity_successors id0 id0 
                 (value_const (const_undef t)) f1).
    destruct J as [J3 J4].
    split; etransitivity; eauto.
Qed.

Lemma pipelined_elim_stld_reachablity_successors: forall f1 f2 actions
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
  eapply pipelined_elim_stld_reachablity_successors; eauto.
Qed.

Hint Unfold keep_pinfo.

(* LAS/LAA is correct. *)
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

End Macro_mem2reg_fdef_sim_wfS.

(* phinodes elimination is correct. *)
Lemma elimphi_sim_wfS: forall f Ps1 Ps2 los nts main VarArgs
  S1 S2 (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs) rd
  (Hrd: reachablity_analysis f = Some rd)
  (Heq1: S1 = [module_intro los nts 
      (Ps1 ++ product_fdef (SafePrimIter.iterate _ elim_phi_step f) :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.
(* The proofs are similar to elim_stld_sim_wfS_wfPI *)
Admitted.

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
