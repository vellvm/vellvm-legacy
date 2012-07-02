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

(***************************************************************)

Lemma app_split: forall A (x y z u:list A) a (Heq: x ++ y = z ++ a :: u),
  (exists u1, exists u2, x = z ++ a :: u1 /\ y = u2 /\ u = u1 ++ u2) \/
  (exists z1, exists z2, x = z1 /\ y = z2 ++ a :: u /\ z = z1 ++ z2).
Proof.
  induction x as [|x1 x]; simpl; intros; subst.
    right. exists nil. eauto.

    destruct z as [|z1 z].
      inv Heq. simpl. left. exists x. eauto.

      inv Heq.
      apply_clear IHx in H1.
      destruct H1 as [[u1 [u2 [J1 [J2 J3]]]]|[z1' [z2 [J1 [J2 J3]]]]]; subst.
        left. exists u1. exists u2. eauto.
        right. exists (z1::z1'). eauto.
Qed.

Lemma map_app_inv: forall A (x y1 y2:list A) f (Heq: List.map f x = y1 ++ y2),
  exists x1, exists x2, x = x1 ++ x2 /\ List.map f x1 = y1 /\ List.map f x2 = y2.
Proof.
  induction x as [|a x]; simpl; intros.
    symmetry in Heq. apply app_eq_nil in Heq.
    destruct Heq; subst. 
    exists nil. exists nil. simpl. auto.

    destruct y1 as [|a1 y1].
      destruct y2 as [|a2 y2]; inv Heq.
        exists nil. exists (a::x). simpl. auto.

      inv Heq.
      apply IHx in H1.
      destruct H1 as [x1 [x2 [J1 [J2 J3]]]]; subst.
      exists (a::x1). exists x2. simpl.
      split; auto.
Qed.


Lemma map_cons_inv: forall A (x y2:list A) a' f (Heq: List.map f x = a' :: y2),
  exists a, exists x2, x = a :: x2 /\ List.map f x2 = y2 /\ f a = a'.
Proof.
  intros.
  destruct x as [|a x]; inv Heq.
    eauto.
Qed.

Lemma Forall_app: forall A P (x y:list A) (Hx: Forall P x) (Hy: Forall P y),
  Forall P (x++y).
Proof.
  induction 1; intros; auto.
    constructor; auto.
Qed.

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

Lemma find_init_stld_inl_remove_neq_spec: forall dones id' pid cs1 v2 id2 cs2
  (Hneq: id2 <> id')
  (Hst : Some (inl (id2, v2, cs2)) = find_init_stld cs1 pid dones),
  Some (inl (id2, v2, remove_cmds id' cs2)) =
             find_init_stld (remove_cmds id' cs1) pid dones.
Proof.
  induction cs1 as [|c cs1]; simpl; intros.
    congruence.

    destruct (id_dec (getCmdLoc c) id'); subst; simpl.
    Case "1".
      destruct c; auto.
      SCase "1.1".
        destruct_if; auto.
        destruct_if; auto.
      SCase "1.2".
        destruct value2; auto.
        destruct_if; auto.
        destruct_if; auto.
          simpl in Hneq. congruence.
    Case "2".
      destruct c; auto.
      SCase "1.1".
        destruct_if; auto.
        destruct_if; auto.
      SCase "1.2".
        destruct value2; auto.
        destruct_if; auto.
        destruct_if; auto.
Qed.

Lemma find_next_stld_inr_remove_neq_spec: forall id' pid cs1 v3 id3
  (Hneq: id3 <> id')
  (Hst : Some (inr (id3, v3)) = find_next_stld cs1 pid),
  Some (inr (id3, v3)) = find_next_stld (remove_cmds id' cs1) pid.
Proof.
  induction cs1 as [|c cs1]; simpl; intros; auto.
    destruct (id_dec (getCmdLoc c) id'); subst; simpl.
    Case "1".
      destruct c; auto.
      SCase "1.1".
        destruct value1; auto.
        destruct_if; auto.
      SCase "1.2".
        destruct value2; auto.
        destruct_if; auto.
          simpl in Hneq. congruence.
    Case "2".
      destruct c; auto.
      SCase "2.1".
        destruct value1; auto.
        destruct_if; auto.
      SCase "2.2".
        destruct value2; auto.
        destruct_if; auto.
Qed.

Lemma find_init_stld_inl_in: forall (cs5 : cmds) (id' : atom) (v0 : value)
  (cs0 : cmds) (dones : list id) pinfo
  (Hfind : ret inl (id', v0, cs0) = find_init_stld cs5 (PI_id pinfo) dones),
  In id' (getCmdsLocs cs5).
Proof.
  intros.
  apply find_init_stld_inl_spec in Hfind.
  destruct Hfind as [cs1 [ty1 [al1 Hst]]]; subst.
  rewrite getCmdsLocs_app. simpl. xsolve_in_list.
Qed.

Lemma find_next_stld_inr_in: forall (cs5 : cmds) (id' : atom) (v0 : value)
  pinfo
  (Hfind : ret inr (id', v0) = find_next_stld cs5 (PI_id pinfo)),
  In id' (getCmdsLocs cs5).
Proof.
  intros.
  apply find_next_stld_inr_spec in Hfind.
  destruct Hfind as [cs1 [cs2 [ty1 [al1 [J1 J2]]]]]; subst.
  rewrite getCmdsLocs_app. simpl. xsolve_in_list.
Qed.

Lemma find_st_ld__sas_in: forall cs0 i0 v cs dones pinfo
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones) v0
  (i1 : id) (Hld : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo)),
  In i1 (getCmdsLocs cs0).
Proof.
  intros.
  apply find_init_stld_inl_spec in Hst.
  destruct Hst as [cs1 [ty1 [al1 Hst]]]; subst.
  apply find_next_stld_inr_in in Hld.
  rewrite getCmdsLocs_app. simpl. xsolve_in_list.
Qed.

Lemma find_next_stld_inr_spec': forall pinfo i1 v0 cs
 (H: ret inr (i1, v0) = find_next_stld cs (PI_id pinfo)),
 exists cs1, exists cs2, exists ty, exists al,
   cs = cs1 ++
          insn_store i1 ty v0 (value_id (PI_id pinfo)) al :: cs2 /\
   load_in_cmds (PI_id pinfo) cs1 = false /\
   store_in_cmds (PI_id pinfo) cs1 = false.
Proof.
  induction cs; simpl; intros.
    congruence.

    destruct a; try find_next_stld_spec_tac.
      destruct value1; try solve [find_next_stld_spec_tac].
      destruct_if.
        find_next_stld_spec_tac.
        destruct H2.
        split; auto. 
        split.
          simpl_env.
          apply load_in_cmds_merge.
          split; auto. 
            unfold load_in_cmds. simpl.
            destruct (id_dec id0 (PI_id pinfo)); try solve [auto | congruence].

          simpl_env.
          apply store_in_cmds_merge.
          split; auto. 

      destruct value2; try solve [find_next_stld_spec_tac].
      repeat (destruct_if; try solve [find_next_stld_spec_tac]).
      exists nil. exists cs. exists typ5. exists align5.
      split; auto.

      find_next_stld_spec_tac.
      destruct H2.      
      repeat split; auto.
        unfold store_in_cmds. simpl.
        destruct (id_dec id0 (PI_id pinfo)); try solve [auto | congruence].
Qed.

Lemma find_st_ld__sas_spec: forall cs0 i0 v cs dones pinfo
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones) v0
  (i1 : id) (Hld : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo)),
  exists cs1 : list cmd, exists ty0 : typ, exists al0 : align,
    cs0 = cs1 ++ insn_store i0 ty0 v (value_id (PI_id pinfo)) al0 :: cs /\
  exists cs2 : list cmd, exists cs3 : list cmd,
    exists ty1 : typ, exists al1 : align,
    cs = cs2 ++ insn_store i1 ty1 v0 (value_id (PI_id pinfo)) al1 :: cs3 /\
    load_in_cmds (PI_id pinfo) cs2 = false /\
    store_in_cmds (PI_id pinfo) cs2 = false.
Proof.
  intros.
  apply find_init_stld_inl_spec in Hst.
  destruct Hst as [cs1 [ty1 [al1 Hst]]]; subst.
  apply find_next_stld_inr_spec' in Hld.
  destruct Hld as [cs2 [cs3 [ty2 [al2 [Hld [J1 J2]]]]]]; subst.
  eauto 11.
Qed.

Lemma NoDup_cmds_split_middle': forall (cs2 cs2' : list cmd) (c c': cmd) 
  (cs1 cs1' : list cmd)  (Hnodup: NoDup (getCmdsLocs (cs1 ++ c :: cs2)))
  (Heq: getCmdLoc c = getCmdLoc c'),
  cs1 ++ c :: cs2 = cs1' ++ c' :: cs2' -> cs1 = cs1' /\ cs2 = cs2'.
Proof.
  intros.
  eapply getCmdsLocs_uniq in Heq; eauto.
    subst. eapply NoDup_cmds_split_middle; eauto.
    xsolve_in_list.
    rewrite H. xsolve_in_list.
Qed.

Lemma filter_app: forall A (check: A -> bool) (l1 l2:list A),
  filter check (l1++l2) = filter check l1 ++ filter check l2.
Proof.
  induction l1; simpl; intros; auto.
    destruct_if.
    rewrite IHl1. simpl_env. auto.
Qed.

Lemma store_in_cmds_false_cons_inv: forall pid c cs
  (H: store_in_cmds pid (c::cs) = false),
  store_in_cmd pid c = false /\ store_in_cmds pid cs = false.
Proof.
  unfold store_in_cmds. simpl.
  intros.
  apply fold_left_or_false in H.
    tauto.
    intros a b H0. apply orb_false_iff in H0. tauto.
Qed.

Lemma load_in_cmds_false_cons_inv: forall pid c cs
  (H: load_in_cmds pid (c::cs) = false),
  load_in_cmd pid c = false /\ load_in_cmds pid cs = false.
Proof.
  unfold load_in_cmds. simpl.
  intros.
  apply fold_left_or_false in H.
    tauto.
    intros a b H0. apply orb_false_iff in H0. tauto.
Qed.

Lemma load_in_cmds_false_cons_intro: forall pid c cs
  (Hld1: load_in_cmd pid c = false) (Hld2: load_in_cmds pid cs = false),
  load_in_cmds pid (c::cs) = false.
Proof.
  unfold load_in_cmds. simpl.
  intros. rewrite Hld1. auto.
Qed.

Lemma store_in_cmds_false_cons_intro: forall pid c cs
  (Hst1: store_in_cmd pid c = false) (Hst2: store_in_cmds pid cs = false),
  store_in_cmds pid (c::cs) = false.
Proof.
  unfold store_in_cmds. simpl.
  intros. rewrite Hst1. auto.
Qed.

Lemma store_in_cmds_true_cons_intro: forall pid c cs
  (Hst: store_in_cmd pid c = true \/ store_in_cmds pid cs = true),
  store_in_cmds pid (c::cs) = true.
Proof.
  unfold store_in_cmds. simpl.
  intros.
  destruct (store_in_cmd pid c).
    apply fold_left_or_spec.
    intros a b H0. subst. auto.
      
    destruct Hst as [Hst | Hst]; try congruence.
Qed.

Lemma load_in_cmds_true_cons_intro: forall pid c cs
  (Hst: load_in_cmd pid c = true \/ load_in_cmds pid cs = true),
  load_in_cmds pid (c::cs) = true.
Proof.
  unfold load_in_cmds. simpl.
  intros.
  destruct (load_in_cmd pid c).
    apply fold_left_or_spec.
    intros a b H0. subst. auto.
      
    destruct Hst as [Hst | Hst]; try congruence.
Qed.

Lemma filter_pres_load_in_cmds_false: forall check pid cs
  (Hnld: load_in_cmds pid cs = false),
  load_in_cmds pid (filter check cs) = false.
Proof.
  induction cs as [|c cs]; simpl; intros; auto.
    apply load_in_cmds_false_cons_inv in Hnld. destruct Hnld.
    destruct_if.
      apply load_in_cmds_false_cons_intro; auto.
Qed.

Lemma filter_pres_store_in_cmds_false: forall check pid cs
  (Hnld: store_in_cmds pid cs = false),
  store_in_cmds pid (filter check cs) = false.
Proof.
  induction cs as [|c cs]; simpl; intros; auto.
    apply store_in_cmds_false_cons_inv in Hnld. destruct Hnld.
    destruct_if.
      apply store_in_cmds_false_cons_intro; auto.
Qed.

Require Import trans_tactic.

Lemma find_next_stld_inl_spec': forall pid i1 cs
 (H: ret inl i1 = find_next_stld cs pid),
 exists cs1, exists cs2, exists ty, exists al,
   cs = cs1 ++
          insn_load i1 ty (value_id pid) al :: cs2 /\
   store_in_cmds pid cs1 = false /\
   load_in_cmds pid cs1 = false.
Proof.
  induction cs; simpl; intros.
    congruence.

    destruct a; try find_next_stld_spec_tac.
      destruct value1; try solve [find_next_stld_spec_tac].
      destruct_if.
        exists nil. exists cs. exists typ5. exists align5.
        split; auto.

        find_next_stld_spec_tac.
        destruct H2. split; auto.
        split.
          apply store_in_cmds_false_cons_intro; auto.
          apply load_in_cmds_false_cons_intro; auto.
            simpl. destruct_dec.
 
      destruct value2; try solve [find_next_stld_spec_tac].
      destruct_if; try find_next_stld_spec_tac.
        destruct H2.
        split; auto. 
        split.
          simpl_env.
          apply store_in_cmds_merge.
          split; auto. 
            unfold store_in_cmds. simpl.
            destruct_dec. 
          apply load_in_cmds_false_cons_intro; auto.
Qed.

Lemma find_st_ld__las_spec: forall cs0 i0 v cs dones pinfo
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones) 
  (i1 : id) (Hld : ret (inl i1) = find_next_stld cs (PI_id pinfo)),
  exists cs1 : list cmd, exists ty0 : typ, exists al0 : align,
    cs0 = cs1 ++ insn_store i0 ty0 v (value_id (PI_id pinfo)) al0 :: cs /\
  exists cs2, exists cs3, exists ty1, exists al1,
    cs = cs2 ++ insn_load i1 ty1 (value_id (PI_id pinfo)) al1 :: cs3 /\
    store_in_cmds (PI_id pinfo) cs2 = false /\
    load_in_cmds (PI_id pinfo) cs2 = false.
Proof.
  intros.
  apply find_init_stld_inl_spec in Hst.
  destruct Hst as [cs1 [ty1 [al1 Hst]]]; subst.
  apply find_next_stld_inl_spec' in Hld.
  destruct Hld as [cs2 [cs3 [ty2 [al2 [Hld [J1 J2]]]]]]; subst.
  eauto 11.
Qed.

Lemma find_next_stld_inl_remove_neq_spec: forall id' pid cs1 id3
  (Hneq: id3 <> id')
  (Hst : Some (inl id3) = find_next_stld cs1 pid),
  Some (inl id3) = find_next_stld (remove_cmds id' cs1) pid.
Proof.
  induction cs1 as [|c cs1]; simpl; intros; auto.
    destruct (id_dec (getCmdLoc c) id'); subst; simpl.
    Case "1".
      destruct c; auto.
      SCase "1.1".
        destruct value1; auto.
        destruct_if; auto.
          simpl in Hneq. congruence.
      SCase "1.2".
        destruct value2; auto.
        destruct_if; auto.
    Case "2".
      destruct c; auto.
      SCase "2.1".
        destruct value1; auto.
        destruct_if; auto.
      SCase "2.2".
        destruct value2; auto.
        destruct_if; auto.
Qed.

Lemma find_init_stld_inr_remove_neq_spec: forall dones id' pid cs1 v2 cs2
  (Hneq: pid <> id')
  (Hst : Some (inr (v2, cs2)) = find_init_stld cs1 pid dones),
  Some (inr (v2, remove_cmds id' cs2)) =
             find_init_stld (remove_cmds id' cs1) pid dones.
Proof.
  induction cs1 as [|c cs1]; simpl; intros.
    congruence.

    destruct (id_dec (getCmdLoc c) id'); subst; simpl.
    Case "1".
      destruct c; auto.
      SCase "1.1".
        destruct_if; auto.
        destruct_if; auto.
          simpl in Hneq. congruence.
      SCase "1.2".
        destruct value2; auto.
        destruct_if; auto.
        destruct_if; auto.
    Case "2".
      destruct c; auto.
      SCase "1.1".
        destruct_if; auto.
        destruct_if; auto.
      SCase "1.2".
        destruct value2; auto.
        destruct_if; auto.
        destruct_if; auto.
Qed.
        
Lemma in__store_in_cmds: forall id1 t2 v1 al2 pid cs
  (Hin: In (insn_store id1 t2 v1 (value_id pid) al2) cs),
  store_in_cmds pid cs = true.
Proof.
  induction cs as [|c cs]; simpl; intros.
    tauto.

    apply store_in_cmds_true_cons_intro.
    destruct Hin as [Hin | Hin]; subst; auto.
      left. simpl. destruct_dec.
Qed.

Lemma in__load_in_cmds: forall id1 t2 al2 pid cs
  (Hin: In (insn_load id1 t2 (value_id pid) al2) cs),
  load_in_cmds pid cs = true.
Proof.
  induction cs as [|c cs]; simpl; intros.
    tauto.

    apply load_in_cmds_true_cons_intro.
    destruct Hin as [Hin | Hin]; subst; auto.
      left. simpl. destruct_dec.
Qed.

Lemma find_init_stld_inl_subst_spec: forall dones id' v' pid cs1 v2 id2 cs2
  (Hnused: used_in_value pid v' = false) (Hneq: id' <> pid) 
  (Hst : Some (inl (id2, v2, cs2)) = find_init_stld cs1 pid dones),
  Some (inl (id2, subst_value id' v' v2, List.map (subst_cmd id' v') cs2)) =
             find_init_stld (List.map (subst_cmd id' v') cs1) pid dones.
Proof.
  induction cs1 as [|c cs1]; simpl; intros.
    congruence.

    destruct c; simpl; auto.
    Case "1.1".
      destruct_if; auto.
      destruct_if; auto.
    Case "1.2".
      destruct value2; simpl; auto.
      destruct_if; auto.
      destruct_if; auto.
      destruct (id_dec id0 id'); subst.
        destruct v'.
          simpl in Hnused.
          destruct_if. 
            destruct_if; auto. congruence.
            destruct_if; auto. 
              destruct (id_dec id0 id0); simpl in Hnused; try congruence.

          destruct_if; auto. 
            congruence.
           
        destruct_if; auto.
Qed.

Lemma find_next_stld_inr_subst_spec: forall id' v' pid cs1 v3 id3
  (Hnused: used_in_value pid v' = false) (Hneq: id' <> pid) 
  (Hst : Some (inr (id3, v3)) = find_next_stld cs1 pid),
  Some (inr (id3, v3 {[v' // id']})) = 
    find_next_stld (List.map (subst_cmd id' v') cs1) pid.
Proof.
  induction cs1 as [|c cs1]; simpl; intros.
    congruence.

    destruct c; simpl; auto.
    Case "1.1".
      destruct value1; simpl; auto.
      destruct_if; auto.
      destruct (id_dec id0 id'); subst.
        destruct v'; auto.
          simpl in Hnused.
          destruct_if; auto. 
            destruct (id_dec id0 id0); simpl in Hnused; try congruence.

        destruct_if; auto. congruence.
    Case "1.2".
      destruct value2; simpl; auto.
      destruct (id_dec id0 id'); subst.
        destruct v'.
          simpl in Hnused.
          destruct_if. 
            destruct_if; auto. congruence.
            destruct_if; auto. 
              destruct (id_dec id0 id0); simpl in Hnused; try congruence.

          destruct_if; auto. 
            congruence.
           
        destruct_if; auto.
Qed.

Lemma find_next_stld_inl_subst_spec: forall id' v' pid cs1 id3
  (Hnused: used_in_value pid v' = false) (Hneq: id' <> pid) 
  (Hst : Some (inl id3) = find_next_stld cs1 pid),
  Some (inl id3) = find_next_stld (List.map (subst_cmd id' v') cs1) pid.
Proof.
  induction cs1 as [|c cs1]; simpl; intros.
    congruence.

    destruct c; simpl; auto.
    Case "1.1".
      destruct value1; simpl; auto.
      destruct (id_dec id0 id'); subst.
        destruct v'.
          simpl in Hnused.
          destruct (id_dec pid id0); subst.
            destruct (id_dec id0 id0); simpl in Hnused; try congruence.
            destruct_if; auto. congruence.
          destruct_if; auto. congruence.
        destruct_if; auto. 
    Case "1.2".
      destruct value2; simpl; auto.
      destruct (id_dec id0 id'); subst.
        destruct v'.
          simpl in Hnused.
          destruct_if. 
          destruct_if; auto. 
            destruct (id_dec id0 id0); simpl in Hnused; try congruence.

          destruct_if; auto. 
        destruct_if; auto.
Qed.

Lemma find_init_stld_inr_subst_spec: forall dones id' v' pid cs1 v2 cs2
  (Hnused: used_in_value pid v' = false)
  (Hst : Some (inr (v2, cs2)) = find_init_stld cs1 pid dones),
  Some (inr (subst_value id' v' v2, List.map (subst_cmd id' v') cs2)) =
             find_init_stld (List.map (subst_cmd id' v') cs1) pid dones.
Proof.
  induction cs1 as [|c cs1]; simpl; intros.
    congruence.

    destruct c; simpl; auto.
    Case "1.1".
      destruct_if; auto.
      destruct_if; auto.
    Case "1.2".
      destruct value2; simpl; auto.
      destruct (id_dec id0 id'); subst.
        destruct v'.
          simpl in Hnused.
          destruct_if; auto.
          destruct_if; auto. 
          destruct_if; auto. 
            destruct (id_dec id0 id0); simpl in Hnused; try congruence.

          destruct_if; auto. 
          destruct_if; auto. 
           
        destruct_if; auto.
        destruct_if; auto.
Qed.

Lemma find_init_stld_inl_doesnt_use_pid: forall pinfo l5 ps5 cs5 tmn5 dones
  (Hwfpi: WF_PhiInfo pinfo)
  (Huniq : uniqFdef (PI_f pinfo)) s m (HwfF: wf_fdef s m (PI_f pinfo))
  (HBinF : blockInFdefB (block_intro l5 ps5 cs5 tmn5) (PI_f pinfo) = true)
  id' v' cs0
  (Hst: Some (inl (id', v', cs0)) = find_init_stld cs5 (PI_id pinfo) dones),
  used_in_value (PI_id pinfo) v' = false /\ id' <> (PI_id pinfo).
Proof.
  intros.
  apply find_init_stld_inl_spec in Hst.
  destruct Hst as [cs1 [ty [al EQ]]]; subst.
  split.
    eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HBinF; eauto 1 using in_middle.
    apply WF_PhiInfo_spec4 with (v0:=v') in HBinF; auto.

    apply WF_PhiInfo_spec10 in HBinF; auto.
Qed.

Lemma find_st_ld_las_doesnt_use_pid: forall pinfo l5 ps5 cs5 tmn5 dones
  (Hwfpi: WF_PhiInfo pinfo)
  (Huniq : uniqFdef (PI_f pinfo)) s m (HwfF: wf_fdef s m (PI_f pinfo))
  (HBinF : blockInFdefB (block_intro l5 ps5 cs5 tmn5) (PI_f pinfo) = true)
  id' v' cs0 id0
  (Hst: Some (inl (id0, v', cs0)) = find_init_stld cs5 (PI_id pinfo) dones)
  (Hld: ret inl id' = find_next_stld cs0 (PI_id pinfo)),
  used_in_value (PI_id pinfo) v' = false /\ id' <> (PI_id pinfo).
Proof.
  intros.
  eapply find_st_ld__las_spec in Hst; eauto.
  destruct Hst as [cs1 [ty [al [EQ [cs2 [cs3 [ty1 [al1 [EQ1 [J1 J2]]]]]]]]]]; 
    subst.
  split.
    eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HBinF; eauto 1 using in_middle.
    apply WF_PhiInfo_spec4 with (v0:=v') in HBinF; auto.

    match goal with
    | H: context [?A ++ ?b :: ?C ++ ?d :: ?E] |- _ =>
      rewrite_env ((A++b::C)++d::E) in H;
      apply WF_PhiInfo_spec10 in H; auto
    end.
Qed.

Lemma find_st_ld_laa_doesnt_use_pid: forall pinfo l5 ps5 cs5 tmn5 dones
  (Hwfpi: WF_PhiInfo pinfo)
  (Huniq : uniqFdef (PI_f pinfo)) s m (HwfF: wf_fdef s m (PI_f pinfo))
  (HBinF : blockInFdefB (block_intro l5 ps5 cs5 tmn5) (PI_f pinfo) = true)
  id' v' cs0
  (Hst: Some (inr (v', cs0)) = find_init_stld cs5 (PI_id pinfo) dones)
  (Hld: ret inl id' = find_next_stld cs0 (PI_id pinfo)),
  used_in_value (PI_id pinfo) v' = false /\ id' <> (PI_id pinfo).
Proof.
  intros.
  apply find_init_stld_inr_spec in Hst.
  destruct Hst as [cs1 [ty1 [num1 [al1 [EQ Hst]]]]]; subst.
  apply find_next_stld_inl_spec' in Hld.
  destruct Hld as [cs2 [cs3 [ty2 [al2 [Hld [J1 J2]]]]]]; subst.
  split.
    simpl. auto.

    match goal with
    | H: context [?A ++ ?b :: ?C ++ ?d :: ?E] |- _ =>
      rewrite_env ((A++b::C)++d::E) in H;
      apply WF_PhiInfo_spec10 in H; auto
    end.
Qed.

Lemma find_init_stld_inl_intro_aux: forall id0 v cs4 ty0 al0 pid dones cs3
  (Hinc: incl (getCmdsLocs cs3) dones) 
  (Huniq: NoDup (dones ++ id0 :: getCmdsLocs cs4)),
  Some (inl (id0, v, cs4)) =
     find_init_stld
       (cs3 ++ insn_store id0 ty0 v (value_id pid) al0 :: cs4) pid
       dones.
Proof.
  induction cs3 as [|c3 cs3]; simpl; intros.
    destruct_if.
      eapply NoDup_disjoint' in Huniq; eauto.
      contradict Huniq; simpl; auto.

      destruct_if. congruence.

    destruct c3; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
        clear HeqR.
        contradict n. apply Hinc. simpl; auto.

      destruct value2 as [qid|]; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
        clear HeqR.
        contradict n. apply Hinc. simpl; auto.
Qed.

Lemma find_init_stld_inl_intro: forall id0 v cs4 ty0 al0 pid cs3
  (Huniq: NoDup (getCmdsLocs cs3 ++ id0 :: getCmdsLocs cs4)),
  Some (inl (id0, v, cs4)) =
     find_init_stld
       (cs3 ++ insn_store id0 ty0 v (value_id pid) al0 :: cs4) pid
       (getCmdsLocs cs3).
Proof.
  intros.
  apply find_init_stld_inl_intro_aux; auto with datatypes v62.
Qed.

Lemma find_init_stld_inr_intro_aux: forall cs4 t num0 al0 pid dones cs3
  (Hinc: incl (getCmdsLocs cs3) dones) 
  (Huniq: NoDup (dones ++ pid :: getCmdsLocs cs4)),
  Some (inr (value_const (const_undef t), cs4)) =
     find_init_stld
       (cs3 ++ insn_alloca pid t num0 al0 :: cs4) pid
       dones.
Proof.
  induction cs3 as [|c3 cs3]; simpl; intros.
    destruct_if.
      eapply NoDup_disjoint' in Huniq; eauto.
      contradict Huniq; simpl; auto.

      destruct_if. congruence.

    destruct c3; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
        clear HeqR.
        contradict n. apply Hinc. simpl; auto.

      destruct value2 as [qid|]; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
        clear HeqR.
        contradict n. apply Hinc. simpl; auto.
Qed.

Lemma find_init_stld_inr_intro: forall cs4 t num0 al0 pid cs3
  (Huniq: NoDup (getCmdsLocs cs3 ++ pid :: getCmdsLocs cs4)),
  Some (inr (value_const (const_undef t), cs4)) =
     find_init_stld
       (cs3 ++ insn_alloca pid t num0 al0 :: cs4) pid
       (getCmdsLocs cs3).
Proof.
  intros.
  apply find_init_stld_inr_intro_aux; auto with datatypes v62.
Qed.

Lemma find_next_stld_strengthen: forall cs2 pid cs1 
  (Hnst: store_in_cmds pid cs1 = false)
  (Hnld: load_in_cmds pid cs1 = false),
  find_next_stld cs2 pid = find_next_stld (cs1++cs2) pid.
Proof.
  induction cs1 as [|c cs1]; simpl; intros; auto.
    apply store_in_cmds_false_cons_inv in Hnst.
    destruct Hnst as [Hnst1 Hnst2].
    apply load_in_cmds_false_cons_inv in Hnld.
    destruct Hnld as [Hnld1 Hnld2].
    destruct c; auto.
      destruct value1; auto.
      destruct_if.
      simpl in Hnld1.
      destruct (id_dec id0 id0); simpl in Hnld1; try congruence.

      destruct value2; auto.
      destruct_if.
      simpl in Hnst1.
      destruct (id_dec id0 id0); simpl in Hnst1; try congruence.   
Qed.

Lemma find_init_stld_inl_in': forall (cs5 : cmds) (id' : atom) (v0 : value)
  (dones : list id) pinfo cs01 c0 cs02
  (Hfind : ret inl (id', v0, cs01 ++ c0 :: cs02) = 
             find_init_stld cs5 (PI_id pinfo) dones),
  In c0 cs5.
Proof.
  intros.
  apply find_init_stld_inl_spec in Hfind.
  destruct Hfind as [cs1 [ty1 [al1 Hst]]]; subst.
  xsolve_in_list.
Qed.

Definition alloca_in_cmd (id':id) (c:cmd) : bool :=
match c with
| insn_alloca qid _ _ _ => id_dec id' qid
| _ => false
end.

Definition alloca_in_cmds (id':id) (cs:cmds) : bool :=
(List.fold_left (fun re c => re || alloca_in_cmd id' c) cs false).

Lemma alloca_in_cmds_merge: forall i0 cs1 cs2,
  alloca_in_cmds i0 cs1 = false /\ alloca_in_cmds i0 cs2 = false ->
  alloca_in_cmds i0 (cs1++cs2) = false.
Proof.
  unfold alloca_in_cmds.
  intros.
  rewrite fold_left_app.
  destruct H as [H1 H2].
  rewrite H1. auto.
Qed.

Lemma find_next_stld_inr_intro: forall c0 cs01 pid cs02
  (Hnst : store_in_cmds pid cs01 = false)
  (Hst : store_in_cmd pid c0 = true) (Hnld : load_in_cmds pid cs01 = false),
  exists v1 : value,
    ret inr (getCmdLoc c0, v1) = find_next_stld (cs01 ++ c0 :: cs02) pid.
Proof.
  intros.
  rewrite <- find_next_stld_strengthen; auto.
  destruct c0; tinv Hst.
  destruct value2; tinv Hst.
  simpl in Hst. simpl.
  destruct (id_dec id0 pid); subst; tinv Hst.
  destruct_if; eauto.
    congruence.
Qed.

Lemma find_next_stld_inl_intro: forall c0 cs01 pid cs02
  (Hnst : store_in_cmds pid cs01 = false)
  (Hld : load_in_cmd pid c0 = true) (Hnld : load_in_cmds pid cs01 = false),
  ret inl (getCmdLoc c0) = find_next_stld (cs01 ++ c0 :: cs02) pid.
Proof.
  intros.
  rewrite <- find_next_stld_strengthen; auto.
  destruct c0; tinv Hld.
  destruct value1; tinv Hld.
  simpl in Hld. simpl.
  destruct (id_dec id0 pid); subst; tinv Hld.
  destruct_if; eauto.
    congruence.
Qed.

Lemma list_subst_actions_app_inv: forall id0 ac0 acs acs1' acs2'
  (Heq: ListComposedPass.subst_actions id0 ac0 acs = acs1' ++ acs2'),
  exists acs1, exists acs2,
    acs = acs1 ++ acs2 /\ 
    ListComposedPass.subst_actions id0 ac0 acs1 = acs1' /\
    ListComposedPass.subst_actions id0 ac0 acs2 = acs2'.
Proof.
  unfold ListComposedPass.subst_actions.
  intros.
  destruct (action2value ac0).
    apply map_app_inv; auto.
    subst. eauto.
Qed.

Lemma list_subst_actions_cons_inv: forall id0 ac0 acs id1 ac1' acs2'
  (Heq: ListComposedPass.subst_actions id0 ac0 acs = (id1, ac1') :: acs2'),
  exists ac1, exists acs2,
    acs = (id1, ac1) :: acs2 /\ 
    subst_action_action ac1 (id0, ac0)= ac1' /\
    ListComposedPass.subst_actions id0 ac0 acs2 = acs2'.
Proof.
  unfold ListComposedPass.subst_actions.
  intros.
  case_eq (action2value ac0).
    intros v Heqv. rewrite Heqv in Heq.
    unfold ListMap.map in *.
    apply map_cons_inv in Heq; auto.
    destruct Heq as [[] [x2 [EQ [J1 J2]]]]; subst.
    inv J2.
    exists a0. exists x2.
    split; auto.
    split; auto.
      unfold subst_action_action, subst_action.
      rewrite Heqv. auto.

    intros Heqv. rewrite Heqv in Heq.
    subst. 
    unfold subst_action_action. rewrite Heqv. eauto.
Qed.

Lemma subst_pres_getCmdLoc: forall id' v' c,
  getCmdLoc c = getCmdLoc (subst_cmd id' v' c).
Proof.
  destruct c; simpl; auto.
Qed.

Lemma subst_pres_load_in_cmd: forall id' v' pid c
  (Hnused: used_in_value pid v' = false) (Hneq: id' <> pid),
  load_in_cmd pid c = load_in_cmd pid (subst_cmd id' v' c).
Proof.
  intros.
  destruct c; simpl; auto.
  destruct value1; simpl; auto.
  destruct_if. destruct_dec.
Qed.

Lemma subst_pres_store_in_cmd: forall id' v' pid c
  (Hnused: used_in_value pid v' = false) (Hneq: id' <> pid),
  store_in_cmd pid c = store_in_cmd pid (subst_cmd id' v' c).
Proof.
  intros.
  destruct c; simpl; auto.
  destruct value2; simpl; auto.
  destruct_if. destruct_dec.
Qed.

Lemma subst_pres_store_in_cmds: forall id' v' pid 
  (Hnused: used_in_value pid v' = false) (Hneq: id' <> pid) cs,
  store_in_cmds pid cs = store_in_cmds pid (List.map (subst_cmd id' v') cs).
Proof.
  unfold store_in_cmds.
  intros. generalize false. 
  induction cs; simpl; auto.
    rewrite <- subst_pres_store_in_cmd; auto.
Qed.

(***************************************************************)

Lemma find_stld_pairs_blocks__uniq: forall pid rd bs actions
  (Huniq: NoDup (getBlocksLocs bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs),
  uniq actions.
Admitted.

(***************************************************************)

Definition wf_cs_action (cs:cmds) (pid:id) (elt:id * action): Prop :=
let '(id', ac') := elt in
match ac' with
| AC_remove =>  
    exists v0, exists cs0, exists id1, exists v1, exists dones,
      Some (inl (id', v0, cs0)) = find_init_stld cs pid dones /\
      Some (inr (id1, v1)) = find_next_stld cs0 pid
| AC_vsubst v' =>  
    exists id0, exists cs0, exists dones,
      Some (inl (id0, v', cs0)) = find_init_stld cs pid dones /\
      Some (inl id') = find_next_stld cs0 pid
| AC_tsubst t' =>
    exists cs0, exists dones,
      Some (inr (value_const (const_undef t'), cs0)) = 
        find_init_stld cs pid dones /\
      Some (inl id') = find_next_stld cs0 pid
end.

Definition loads_must_be_in_pre (acs: AssocList action) (pid:id) (cs:cmds)
  : Prop :=
Forall (fun c => load_in_cmd pid c = true -> getCmdLoc c `in` dom acs) cs.

Definition wf_cs_action_pre (acs: AssocList action) (cs:cmds) (pid:id) 
  (elt:id * action): Prop :=
let '(id', ac') := elt in
match ac' with
| AC_remove =>  
    exists v0, exists cs01, exists c0, exists cs02, exists dones,    
      Some (inl (id', v0, cs01 ++ c0 :: cs02)) = find_init_stld cs pid dones /\
      store_in_cmds pid cs01 = false /\
      store_in_cmd pid c0 = true /\ loads_must_be_in_pre acs pid cs01
| AC_vsubst v' =>  
    exists id0, exists cs01, exists c0, exists cs02, exists dones,    
      Some (inl (id0, v', cs01 ++ c0 :: cs02)) = find_init_stld cs pid dones /\
      store_in_cmds pid cs01 = false /\ getCmdLoc c0 = id' /\
      load_in_cmd pid c0 = true /\ loads_must_be_in_pre acs pid cs01
| AC_tsubst t' =>
    exists cs01, exists c0, exists cs02, exists dones,
      Some (inr (value_const (const_undef t'), cs01 ++ c0 :: cs02)) = 
        find_init_stld cs pid dones /\
      store_in_cmds pid cs01 = false /\ getCmdLoc c0 = id' /\
      load_in_cmd pid c0 = true /\ loads_must_be_in_pre acs pid cs01
end.

Lemma loads_must_be_in_nil__no_loads: forall pid cs 
  (H: loads_must_be_in_pre nil pid cs), load_in_cmds pid cs = false.
Proof.
  induction 1; simpl; auto.
    apply load_in_cmds_false_cons_intro; auto.
      case_eq (load_in_cmd pid x); auto.
        intro Heq.
        apply H in Heq. fsetdec.
Qed.

Lemma wf_cs_action_nil__wf_cs_action: forall cs pid elt
  (Hwf: wf_cs_action_pre nil cs pid elt), wf_cs_action cs pid elt.
Proof.
  unfold wf_cs_action_pre, wf_cs_action.
  destruct elt as [id' [|v'|t']]; simpl; intros.
  Case "1".
    destruct Hwf as [v0 [cs01 [c0 [cs02 [dones [Hfind1 [Hnst [Hst Hnld]]]]]]]].
    exists v0. exists (cs01 ++ c0 :: cs02). exists (getCmdLoc c0).
    apply loads_must_be_in_nil__no_loads in Hnld.    
    eapply find_next_stld_inr_intro with (cs02:=cs02) in Hnld; eauto.
    destruct Hnld as [v1 Hnld]. eauto.
  Case "2".
    destruct Hwf 
      as [id0 [cs01 [c0 [cs02 [dones [Hfind1 [Hnst [Heq [Hld Hnld]]]]]]]]]; subst.
    exists id0. exists (cs01 ++ c0 :: cs02). exists dones.
    apply loads_must_be_in_nil__no_loads in Hnld.    
    eapply find_next_stld_inl_intro with (cs02:=cs02) in Hnld; eauto.
  Case "3".
    destruct Hwf 
      as [cs01 [c0 [cs02 [dones [Hfind1 [Hnst [Heq [Hld Hnld]]]]]]]]; subst.
    exists (cs01 ++ c0 :: cs02). exists dones.
    apply loads_must_be_in_nil__no_loads in Hnld.    
    eapply find_next_stld_inl_intro with (cs02:=cs02) in Hnld; eauto.
Qed.

Definition wf_stld_state (cs:cmds) (pid:id) (elt :stld_state * AssocList action)
  : Prop :=
let '(s, acs) := elt in
match s with
| STLD_init => alloca_in_cmds pid cs = false /\ store_in_cmds pid cs = false
| STLD_store id0 v0 =>
    exists cs1 : list cmd, exists ty0 : typ, exists al0 : align, exists cs2, 
      cs = cs1 ++ insn_store id0 ty0 v0 (value_id pid) al0 :: cs2 /\
      store_in_cmds pid cs2 = false /\ loads_must_be_in_pre acs pid cs2
| STLD_alloca t0 =>
    exists cs1, exists num, exists al, exists cs2, 
      cs = cs1 ++ insn_alloca pid t0 num al :: cs2 /\
      store_in_cmds pid cs2 = false /\ loads_must_be_in_pre acs pid cs2
end.

Lemma loads_must_be_in_pre_append: forall acs pid cs3 c
  (Hlds: loads_must_be_in_pre acs pid cs3) (Hld: load_in_cmd pid c = false),
  loads_must_be_in_pre acs pid (cs3 ++ [c]).
Proof.
  intros.
  apply Forall_forall.
  intros x Hinx H.
  destruct_in Hinx.
    eapply Forall_forall in Hlds; eauto.
    destruct_in Hinx. congruence.
Qed.

Lemma wf_stld_state_append: forall st cs1 pid c 
  (Hwf: wf_stld_state cs1 pid st)
  (Hnot: alloca_in_cmd pid c = false /\ 
         store_in_cmd pid c = false /\ 
         load_in_cmd pid c = false),
  wf_stld_state (cs1 ++ [c]) pid st.
Proof.
  intros.
  destruct st as [s acs].
  destruct Hnot as [J1 [J2 J3]].
  destruct s; simpl in *.
    destruct Hwf.
    split.
      apply alloca_in_cmds_merge; auto.
      apply store_in_cmds_merge; auto.

    destruct Hwf as [cs2 [t0 [al0 [cs3 [EQ [G1 G2]]]]]]; subst.
    exists cs2. exists t0. exists al0. exists (cs3 ++ [c]).
    simpl_env.
    split; auto.
    split.
      apply store_in_cmds_merge; auto.
      apply loads_must_be_in_pre_append; auto.

    destruct Hwf as [cs2 [num0 [al0 [cs3 [EQ [G1 G2]]]]]]; subst.
    exists cs2. exists num0. exists al0. exists (cs3 ++ [c]).
    simpl_env.
    split; auto.
    split.
      apply store_in_cmds_merge; auto.
      apply loads_must_be_in_pre_append; auto.
Qed.

Lemma loads_must_be_in_pre_weaken: forall acs1 acs2 pid cs 
  (Hlds: loads_must_be_in_pre acs2 pid cs),
  loads_must_be_in_pre (acs1++acs2) pid cs.
Proof.
  induction 1; constructor; auto.
    intro Heq. apply H in Heq. rewrite dom_app. auto.
Qed.

Lemma loads_must_be_in_pre_append': forall ac acs pid cs3 c
  (Hlds: loads_must_be_in_pre acs pid cs3) (Hld: load_in_cmd pid c = true)
  (Heq: fst ac = getCmdLoc c),
  loads_must_be_in_pre ([ac]++acs) pid (cs3 ++ [c]).
Proof.
  intros.
  apply Forall_forall.
  intros x Hinx H.
  destruct_in Hinx.
    eapply Forall_forall in Hlds; eauto.
    apply Hlds in H. simpl_env. auto.

    destruct_in Hinx. 
      destruct ac. simpl in *. subst. auto.
Qed.

Ltac wf_stld_state_append_tac :=
  try solve 
    [apply wf_stld_state_append; simpl; try solve [auto | destruct_dec]].

Lemma find_stld_pair_cmd__wf_stld_state: forall (pid : id) cs c st
  (Hwfst: wf_stld_state cs pid st),
  wf_stld_state (cs++[c]) pid (find_stld_pair_cmd pid st c).
Proof.
  intros.
  destruct st as [s acs].
  destruct c; wf_stld_state_append_tac; simpl.
    Case "1".        
      destruct (id_dec pid id5); wf_stld_state_append_tac.
        subst id5. simpl.
        exists cs. exists value5. exists align5. exists nil.
        unfold loads_must_be_in_pre, store_in_cmds. auto.
    Case "2".
      destruct value1 as [qid|]; wf_stld_state_append_tac.
      destruct (id_dec pid qid); wf_stld_state_append_tac.
        subst qid.
        destruct s.
        SCase "2.1".
          simpl in *. destruct Hwfst.
          split.
            apply alloca_in_cmds_merge; auto.
            apply store_in_cmds_merge; auto.
        SCase "2.2".
          simpl in *.
          destruct Hwfst as [cs3 [ty0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
          exists cs3. exists ty0. exists al0.
          exists (cs4++[insn_load id5 typ5 (value_id pid) align5]).
          simpl_env. 
          split; auto.
          split.
            apply store_in_cmds_merge; auto.
            apply loads_must_be_in_pre_append'; auto.
              simpl. destruct_dec.
        SCase "2.3".
          simpl in *.
          destruct Hwfst as [cs3 [num0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
          exists cs3. exists num0. exists al0. 
          exists (cs4++[insn_load id5 typ5 (value_id pid) align5]).
          simpl_env. 
          split; auto.
          split.
            apply store_in_cmds_merge; auto.
            apply loads_must_be_in_pre_append'; auto.
              simpl. destruct_dec.
    Case "3".
      destruct value2 as [qid|]; wf_stld_state_append_tac.
      destruct (id_dec pid qid); wf_stld_state_append_tac.
        subst qid.
        destruct s.
        SCase "3.1".
          simpl. exists cs. exists typ5. exists align5. exists nil.
          unfold loads_must_be_in_pre, store_in_cmds. auto.
        SCase "3.2".
          simpl in *.
          destruct Hwfst as [cs3 [ty0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
          exists (cs3 ++ insn_store i0 ty0 v (value_id pid) al0 :: cs4). 
          exists typ5. exists align5. exists nil.
          simpl_env. 
          split; auto.
          split; auto.
            constructor.
        SCase "3.3".
          simpl in *.
          destruct Hwfst as [cs3 [num0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
          exists (cs3 ++ insn_alloca pid t num0 al0 :: cs4). 
          exists typ5. exists align5. exists nil.
          simpl_env. 
          split; auto.
          split; auto.
            constructor.
Qed.

Lemma find_stld_pairs_cmds__wf_stld_state_aux: forall (pid : id) cs 
  cs2 cs1 st1 (Heq: cs = cs1 ++ cs2)
  (Hwfst: wf_stld_state cs1 pid st1),
  wf_stld_state cs pid (fold_left (find_stld_pair_cmd pid) cs2 st1).
Proof.
  induction cs2 as [|c2 cs2]; simpl; intros; subst; auto.
    simpl_env. auto.

    apply IHcs2 with (cs3:=cs1++[c2]); simpl_env; auto.
    clear IHcs2.
    apply find_stld_pair_cmd__wf_stld_state; auto.
Qed.

Lemma find_stld_pairs_cmds__wf_stld_state: forall (pid : id) cs,
  wf_stld_state cs pid (fold_left (find_stld_pair_cmd pid) cs (STLD_init, nil)).
Proof.
  intros.
  assert (cs = nil ++ cs) as EQ. auto.
  eapply find_stld_pairs_cmds__wf_stld_state_aux in EQ; eauto.
  simpl. unfold alloca_in_cmds, store_in_cmds. auto.
Qed.

Definition find_stld_pair_cmd' (pid:id) (acc:stld_state * AssocList action) 
  (c:cmd) : stld_state * option (id * action) :=
let '(st, actions) := acc in
match c with
| insn_alloca qid ty value5 align5 =>
    if id_dec pid qid
    then (STLD_alloca ty, None)
    else (st, None)
| insn_store sid typ5 v0 value2 align5 =>
    match value2 with
    | value_id qid =>
       if id_dec pid qid
       then 
         match st with
         | STLD_store sid' _ => (STLD_store sid v0, Some (sid', AC_remove))
         | _ => (STLD_store sid v0, None)
         end
      else (st, None)
    | value_const const5 => (st, None)
    end
| insn_load lid typ5 value1 align5 =>
    match value1 with
    | value_id qid =>
       if id_dec pid qid
       then 
         match st with
         | STLD_store _ v' => (st, Some (lid, AC_vsubst v'))
         | STLD_alloca ty' => (st, Some (lid, AC_tsubst ty'))
         | _ => (st, None)
         end
       else (st, None)
    | value_const const5 => (st, None)
    end
| _ => (st, None)
end.

Lemma find_stld_pair_cmd__find_stld_pair_cmd': forall pid st1 c,
  find_stld_pair_cmd pid st1 c =
  (let (s, o) := find_stld_pair_cmd' pid st1 c in
   match o with
   | ret ac => (s, ac :: snd st1)
   | merror => (s, snd st1)
   end).
Proof.
  destruct st1 as [s1 acc1].
  destruct c; simpl; intros; auto.
    destruct_if; uniq_result; auto.

    destruct value1; auto.
    destruct_if; auto.
    destruct s1; auto.

    destruct value2; auto.
    destruct_if; auto.
    destruct s1; auto.
Qed.

Lemma find_stld_pairs_cmds__find_stld_pairs_cmds': forall pid cs st1,
  fold_left (find_stld_pair_cmd pid) cs st1 =
  fold_left (fun st c => 
             match find_stld_pair_cmd' pid st c with
             | (s, Some ac) => (s, ac::snd st)
             | (s, None) => (s, snd st)
             end) cs st1.
Proof.
  induction cs as [|c cs]; simpl; intros; auto.
    rewrite IHcs.
    f_equal.
    apply find_stld_pair_cmd__find_stld_pair_cmd'.
Qed.

Lemma find_stld_pair_cmd'__wf_cs_action_pre: forall cs cs1 c cs2 st1 st2 pid 
  (Heq: cs = cs1 ++ c :: cs2)
  (Huniq: NoDup (getCmdsLocs cs))
  (Hwfst1: wf_stld_state cs1 pid st1) ac
  (Hfind: find_stld_pair_cmd' pid st1 c = (st2, Some ac)),
  wf_cs_action_pre (snd st1) cs pid ac.
Proof.

Ltac find_stld_pair_cmd'__wf_cs_action_pre_tac :=
  match goal with
  | Huniq: NoDup _ |- context [(?A ++ ?b :: ?C) ++ ?d :: ?E] =>
    rewrite_env (A++b::(C++d::E));
    rewrite_env (A++b::(C++d::E)) in Huniq;
    exists C; exists d; exists E; exists (getCmdsLocs A)
  end.

  intros. subst.
  destruct st1 as [s1 acc1]. 
  destruct c; simpl in Hfind; tinv Hfind.
  Case "1".
    destruct_if; tinv Hfind.
  Case "2".
    destruct value1; tinv Hfind.
    destruct_if.
    destruct s1; inv H0.
    SCase "2.1".
      simpl in *.
      destruct Hwfst1 as [cs3 [ty0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
      exists i0. 
      find_stld_pair_cmd'__wf_cs_action_pre_tac.
      split.
        rewrite getCmdsLocs_app in Huniq. simpl in Huniq.
        apply find_init_stld_inl_intro; auto.
      split; auto.
      split; auto.
      split; simpl; auto.
        destruct_dec.
    SCase "2.2".
      simpl in *.
      destruct Hwfst1 as [cs3 [num0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
      find_stld_pair_cmd'__wf_cs_action_pre_tac.
      split.
        rewrite getCmdsLocs_app in Huniq. simpl in Huniq.
        apply find_init_stld_inr_intro; auto.
      split; auto.
      split; auto.
      split; simpl; auto.
        destruct_dec.
  Case "3".
    destruct value2; tinv Hfind.
    destruct_if.
    destruct s1; inv H0.
    simpl in *.
    destruct Hwfst1 as [cs3 [ty0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
    exists v. 
    find_stld_pair_cmd'__wf_cs_action_pre_tac.
    split.
      rewrite getCmdsLocs_app in Huniq. simpl in Huniq.
      apply find_init_stld_inl_intro; auto.
    split; auto.
    split; simpl; auto.
      destruct_dec.
Qed.

Local Opaque find_stld_pair_cmd' find_stld_pair_cmd.

Lemma find_stld_pairs_cmds_cons_inv: forall pid cs s acs s' acs'
  (Heq: fold_left (find_stld_pair_cmd pid) cs (s, acs) = (s', acs')),
  exists acs0, acs' = acs0 ++ acs.
Proof.
  induction cs as [|c cs]; simpl; intros.
    uniq_result. exists nil. auto.

    rewrite find_stld_pair_cmd__find_stld_pair_cmd' in Heq.
    case_eq (find_stld_pair_cmd' pid (s, acs) c).
    intros s0 o Heq'.
    rewrite Heq' in Heq.
    destruct o as [ac'|]; simpl in Heq. 
      apply IHcs in Heq.
      destruct Heq as [acs0 Heq]; subst.
      exists (acs0 ++ [ac']). simpl_env. auto.
    
      apply IHcs in Heq; auto.
Qed.

Lemma find_stld_pairs_cmds__split_aux: forall pid cs acs1 ac acs2 s0 acs0 s2
  (Heq: fold_left (find_stld_pair_cmd pid) cs (s0, acs0) = 
          (s2, acs2 ++ ac :: acs1 ++ acs0)),
  exists cs1, exists c, exists cs2, exists s1, exists s,
    cs = cs1 ++ c :: cs2 /\
    fold_left (find_stld_pair_cmd pid) cs1 (s0, acs0) = (s1, acs1 ++ acs0) /\
    find_stld_pair_cmd' pid (s1, acs1 ++ acs0) c = (s, Some ac) /\    
    fold_left (find_stld_pair_cmd pid) cs2 (s, ac::acs1 ++ acs0) = 
      (s2, acs2 ++ ac :: acs1 ++ acs0).
Proof.
  induction cs as [|c cs]; simpl; intros; subst.
  Case "base".
    inversion Heq. anti_simpl_env.  
  Case "ind".
    rewrite find_stld_pair_cmd__find_stld_pair_cmd' in Heq.
    case_eq (find_stld_pair_cmd' pid (s0, acs0) c).
    intros s o Heq'.
    rewrite Heq' in Heq.
    destruct o as [ac'|]; simpl in Heq. 
    SCase "1".
      assert (J:=Heq).
      apply find_stld_pairs_cmds_cons_inv in J. destruct J as [acs3 J].
      anti_simpl_env.
      destruct acs1 as [|ac1 acs1].
      SSCase "1.1".
        anti_simpl_env.
        exists nil. exists c. exists cs. exists s0. exists s. 
        split; auto.
      SSCase "1.2".
        destruct (cons_last _ ac1 acs1) as [pre [last EQ]].
        rewrite EQ in J, Heq.
        anti_simpl_env. 
        rewrite_env (acs2 ++ ac :: pre ++ (ac' :: acs0)) in Heq.
        apply IHcs in Heq; auto.
        destruct Heq as [cs1 [c' [cs2 [s1 [s3 [J1 [J2 [J3 J4]]]]]]]].
        exists (c::cs1). exists c'. exists cs2. exists s1. exists s3. 
        split.
          simpl. subst. auto.
        split.
          simpl. rewrite find_stld_pair_cmd__find_stld_pair_cmd'. rewrite Heq'.      
          rewrite_env (([ac1] ++ acs1) ++ acs0). rewrite EQ. simpl_env. auto.
        split.
          rewrite_env (([ac1] ++ acs1) ++ acs0). rewrite EQ. simpl_env. auto.
          rewrite_env (([ac1] ++ acs1) ++ acs0). rewrite EQ. simpl_env. auto.

    SCase "2".
      apply IHcs in Heq; auto.
      destruct Heq as [cs1 [c' [cs2 [s1 [s3 [J1 [J2 [J3 J4]]]]]]]].
      exists (c::cs1). exists c'. exists cs2. exists s1. exists s3.
      simpl. rewrite find_stld_pair_cmd__find_stld_pair_cmd'. rewrite Heq'.      
      subst; split; auto.
Qed.

Lemma find_stld_pairs_cmds__split: forall pid cs acs1 ac acs2 s2
  (Heq: fold_left (find_stld_pair_cmd pid) cs (STLD_init, nil) = 
          (s2, acs2 ++ ac :: acs1)),
  exists cs1, exists c, exists cs2, exists s1, exists s, 
    cs = cs1 ++ c :: cs2 /\
    fold_left (find_stld_pair_cmd pid) cs1 (STLD_init, nil) = (s1, acs1) /\
    find_stld_pair_cmd' pid (s1, acs1) c = (s, Some ac) /\    
    fold_left (find_stld_pair_cmd pid) cs2 (s, ac::acs1) = 
      (s2, acs2 ++ ac :: acs1).
Proof.
  intros.
  replace acs1 with (acs1++nil) in Heq; auto.
  apply find_stld_pairs_cmds__split_aux in Heq.
  simpl_env in *. auto.
Qed.

Lemma loads_must_be_in_pre_rev: forall acs pid cs
  (Hwf: loads_must_be_in_pre (rev acs) pid cs),
  loads_must_be_in_pre acs pid cs.
Proof.
  unfold loads_must_be_in_pre. intros.
  apply Forall_forall. intros x Hinx Heq.
  eapply Forall_forall in Hwf; eauto.
  apply Hwf in Heq.
  apply binds_In_inv in Heq.
  destruct Heq as [ac Heq].
  apply binds_In with (a:=ac); auto.
  unfold binds in *.
  apply in_rev; auto.
Qed.

Lemma wf_cs_action_pre_rev: forall acs cs pid ac 
  (Hwf: wf_cs_action_pre (rev acs) cs pid ac),
  wf_cs_action_pre acs cs pid ac.
Proof.
  unfold wf_cs_action_pre. intros.
  destruct ac as [? []].
    destruct Hwf as [v0 [cs01 [c0 [cs02 [dones [J1 [J2 [J3 J4]]]]]]]].
    apply loads_must_be_in_pre_rev in J4. eauto 9.

    destruct Hwf as [id0 [cs01 [c0 [cs02 [dones [J1 [J2 [J3 [J4 J5]]]]]]]]].
    apply loads_must_be_in_pre_rev in J5. eauto 10.

    destruct Hwf as [cs01 [c0 [cs02 [dones [J1 [J2 [J3 [J4 J5]]]]]]]].
    apply loads_must_be_in_pre_rev in J5. eauto 9.
Qed.

Lemma wf_cs_action_pre_weaken: forall acs1 acs2 cs pid ac 
  (Hwf: wf_cs_action_pre acs2 cs pid ac),
  wf_cs_action_pre (acs1++acs2) cs pid ac.
Proof.
  unfold wf_cs_action_pre. intros.
  destruct ac as [? []].
    destruct Hwf as [v0 [cs01 [c0 [cs02 [dones [J1 [J2 [J3 J4]]]]]]]].
    apply loads_must_be_in_pre_weaken with (acs1:=acs1) in J4. eauto 9.

    destruct Hwf as [id0 [cs01 [c0 [cs02 [dones [J1 [J2 [J3 [J4 J5]]]]]]]]].
    apply loads_must_be_in_pre_weaken with (acs1:=acs1) in J5. eauto 10.

    destruct Hwf as [cs01 [c0 [cs02 [dones [J1 [J2 [J3 [J4 J5]]]]]]]].
    apply loads_must_be_in_pre_weaken with (acs1:=acs1) in J5. eauto 9.
Qed.

Definition wf_cs_actions (acs: AssocList action) (cs:cmds) (pid:id) : Prop :=
forall acs1 ac acs2 (Heq: acs = acs1 ++ ac :: acs2),
  wf_cs_action_pre acs1 cs pid ac.

Lemma find_stld_pairs_cmds__wf_cs_actions: forall pid cs 
  (Huniq: NoDup (getCmdsLocs cs)),
  wf_cs_actions (find_stld_pairs_cmds cs pid) cs pid.
Proof.
  unfold find_stld_pairs_cmds.
  intros.
  intros acs1 ac acs2 Heq.
  case_eq (fold_left (find_stld_pair_cmd pid) cs (STLD_init, nil)).
  intros s' ac' Hfind.
  rewrite Hfind in Heq. simpl in Heq.
  assert (ac' = rev acs2 ++ ac :: rev acs1) as EQ.
    rewrite <- rev_involutive with (l:=ac').
    rewrite Heq. rewrite rev_app_distr. simpl. simpl_env. auto.
  subst. clear Heq.
  apply find_stld_pairs_cmds__split in Hfind.
  destruct Hfind as [cs1 [c [cs2 [s1 [s [J1 [J2 [J3 J4]]]]]]]].
  eapply find_stld_pair_cmd'__wf_cs_action_pre in J3; eauto.
    simpl in J3. apply wf_cs_action_pre_rev; auto.

    rewrite <- J2. apply find_stld_pairs_cmds__wf_stld_state; auto.
Qed.

Transparent find_stld_pair_cmd' find_stld_pair_cmd.

Definition wf_block_action (acs: AssocList action) (b:block) (pid:id) 
  : Prop :=
let '(block_intro _ _ cs _) := b in
wf_cs_actions acs cs pid.

Lemma wf_cs_actions_nil: forall cs pid, wf_cs_actions nil cs pid.
Proof.
  unfold wf_cs_actions.
  intros. symmetry in Heq. contradict Heq. apply app_cons_not_nil.
Qed.

Lemma find_stld_pairs_block__wf_cs_actions: forall pid rd b
  (Huniq: NoDup (getBlockLocs b)),
  wf_block_action (find_stld_pairs_block pid rd b) b pid.
Proof.
  destruct b as [? ? cs ?]. simpl. intros.
  destruct_if; auto using wf_cs_actions_nil.
  split_NoDup.
  apply find_stld_pairs_cmds__wf_cs_actions; auto.
Qed.

Lemma find_stld_pairs_blocks__split: forall pid rd bs acs1 ac acs2
  (Hmap: flat_map (find_stld_pairs_block pid rd) bs = acs1 ++ ac :: acs2),
  exists b, exists bs1, exists bs2,
  exists acs11, exists acs12, exists acs21, exists acs22,
    bs = bs1 ++ b :: bs2 /\
    acs1 = acs11 ++ acs12 /\
    acs2 = acs21 ++ acs22 /\
    find_stld_pairs_block pid rd b = acs12 ++ ac :: acs21 /\
    flat_map (find_stld_pairs_block pid rd) bs1 = acs11 /\
    flat_map (find_stld_pairs_block pid rd) bs2 = acs22.
Proof.
  induction bs as [|b bs]; simpl; intros.
    symmetry in Hmap. contradict Hmap. apply app_cons_not_nil.

    apply app_split in Hmap.
    destruct Hmap as [[u1 [u2 [J1 [J2 J3]]]]|[z1 [z2 [J1 [J2 J3]]]]].
      exists b. exists nil. exists bs. exists nil. exists acs1. 
      exists u1. exists u2. simpl. eauto 10.

      apply_clear IHbs in J2.
      destruct J2 as 
        [b0 [bs1 [bs2 [acs11 [acs12 [acs21 [acs22 [J2 
          [J7 [J4 [J5 [J6 J8]]]]]]]]]]]]; subst.
      exists b0. exists (b::bs1). exists bs2.
      exists (find_stld_pairs_block pid rd b ++ 
              flat_map (find_stld_pairs_block pid rd) bs1).
      exists acs12. exists acs21.
      exists (flat_map (find_stld_pairs_block pid rd) bs2).
      simpl_env. split; auto.
Qed.

Definition wf_actions (bs:blocks) (pid:id) (rd:list l) (acs: AssocList action) 
  : Prop :=
forall acs1 ac acs2 (Heq: acs = acs1 ++ ac :: acs2),
  exists l0, exists ps0, exists cs0, exists tmn0,
    In (block_intro l0 ps0 cs0 tmn0) bs /\ In l0 rd /\
    wf_cs_action_pre acs1 cs0 pid ac.

Lemma find_stld_pairs_block__reach: forall pid rd l0 ps0 cs0 tmn0
  acs1 ac acs2
  (Hfind: find_stld_pairs_block pid rd (block_intro l0 ps0 cs0 tmn0) =
            acs1 ++ ac :: acs2),
  In l0 rd.
Proof.
  simpl. intros.
  destruct_if; auto.
    symmetry in H0. contradict H0. apply app_cons_not_nil.
Qed.

Lemma find_stld_pairs_blocks__wf_actions: forall pid rd bs actions
  (Huniq: NoDup (getBlocksLocs bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs),
  wf_actions bs pid rd actions.
Proof.
  intros.
  unfold wf_actions.
  intros. subst.
  apply find_stld_pairs_blocks__split in Heq.
  destruct Heq as 
    [b [bs1 [bs2 [acs11 [acs12 [acs21 [acs22 
      [J1 [J2 [J3 [J4 [J5 J6]]]]]]]]]]]]; subst.
  destruct b as [l0 ps0 cs0 tmn0].
  exists l0. exists ps0. exists cs0. exists tmn0.
  split. xsolve_in_list.
  split. apply find_stld_pairs_block__reach in J4; auto.
    simpl in J4.
    destruct_if.
      apply wf_cs_action_pre_weaken.
      rewrite getBlocksLocs_app in Huniq. simpl in Huniq.
      split_NoDup. 
      apply find_stld_pairs_cmds__wf_cs_actions with (pid:=pid) in Huniq; auto.
      apply Huniq in H0; auto.

      symmetry in H0. contradict H0. apply app_cons_not_nil.
Qed.

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
                       [SAS_l0 SAS_ps0 SAS_cs0 SAS_tmn0] SAS_prop0];
  destruct SAS_prop0 as 
    [SAS_BInF0 [SAS_ldincmds0 [SAS_cs1 [SAS_cs3 SAS_EQ]]]]; subst; simpl
end.

Lemma filter_pres_loads_must_be_in_pre: forall acs check pid cs
  (Hnld: loads_must_be_in_pre acs pid cs),
  loads_must_be_in_pre acs pid (filter check cs).
Proof.
  induction 1; simpl; intros.
    constructor.

    destruct_if.
    constructor; auto.
Qed.

Lemma no_loads__loads_must_be_in_pre: forall pid acs cs
  (H: load_in_cmds pid cs = false),
  loads_must_be_in_pre acs pid cs.
Proof.
  induction cs as [|c cs]; intros.
    constructor.

    apply load_in_cmds_false_cons_inv in H.
    destruct H as [H1 H2].
    constructor.
      intros. congruence.
      apply IHcs; auto.
Qed.

Lemma loads_must_be_in_pre_merge: forall acs pid cs1 cs2
  (Hlds1: loads_must_be_in_pre acs pid cs1) 
  (Hlds2: loads_must_be_in_pre acs pid cs2),
  loads_must_be_in_pre acs pid (cs1 ++ cs2).
Proof.
  unfold loads_must_be_in_pre.
  intros.
  apply Forall_app; auto.
Qed.

Lemma loads_must_be_in_pre_load_in_cmds_false__loads_must_be_in_pre: 
  forall acs pid cs1 cs2
  (Hlds1: loads_must_be_in_pre acs pid cs1) 
  (Hlds2: load_in_cmds pid cs2 = false),
  loads_must_be_in_pre acs pid (cs1 ++ cs2).
Proof.
  intros.
  apply loads_must_be_in_pre_merge; auto.
  apply no_loads__loads_must_be_in_pre; auto.
Qed.

Lemma remove_cmds_middle: forall (id' : atom) (cs01 : list cmd) (c0 : cmd)
  (cs02 : list cmd) (Hneq : getCmdLoc c0 <> id'),
  remove_cmds id' (cs01 ++ c0 :: cs02) =
    remove_cmds id' cs01 ++ c0 :: remove_cmds id' cs02.
Proof.
  intros.
  unfold remove_cmds.
  simpl; rewrite filter_app; simpl.
  destruct (id_dec (getCmdLoc c0) id'); subst; try congruence.
  simpl. auto.
Qed.

Lemma remove_pres_loads_must_be_in_pre: forall id' ac' actions pid cs
  (Hld: loads_must_be_in_pre ((id', ac') :: actions) pid cs),
  loads_must_be_in_pre actions pid 
    (filter (fun c : cmd => negb (id_dec (getCmdLoc c) id')) cs).
Proof.
  induction 1; simpl; intros.
    constructor.

    destruct_dec; simpl.
      constructor; auto.
        intros Heq. apply H in Heq.
        simpl in Heq. fsetdec.
Qed.

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
  l1 ps1 cs1 tmn1 (Hin: In (block_intro l1 ps1 cs1 tmn1) bs1)
  (Hfind1 : ret inl (id', v0, cs0) = find_init_stld cs1 (PI_id pinfo) dones)
  (Hfind2 : ret inr (id1, v1) = find_next_stld cs0 (PI_id pinfo))
  (HBinF : blockInFdefB (block_intro l5 ps5 cs5 tmn5) (PI_f pinfo) = true) 
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
      assert (block_intro l1 ps1 cs1 tmn1 = block_intro l5 ps5 cs5 tmn5) 
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
      assert (block_intro l1 ps1 cs1 tmn1 = block_intro l5 ps5 cs5 tmn5) 
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
      assert (blockInFdefB (block_intro l1 ps1 cs1 tmn1) (PI_f pinfo) = true)
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
     blockInFdefB (block_intro l1 ps1 cs1 tmn1) (fdef_intro fh bs1) = true) 
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
      | H: blockInFdefB (block_intro _ _
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
  (HBinF5: blockInFdefB (block_intro l5 ps5 cs5 tmn5) (fdef_intro fh bs1) = true) 
  (HBinF1: blockInFdefB (block_intro l1 ps1 cs1 tmn1) (fdef_intro fh bs1) = true) 
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
    | H: blockInFdefB (block_intro _ _
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
  (HBinF5: blockInFdefB (block_intro l5 ps5 cs5 tmn5) (fdef_intro fh bs1) = true) 
  (HBinF1: blockInFdefB (block_intro l1 ps1 cs1 tmn1) (fdef_intro fh bs1) = true) 
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
    | H: blockInFdefB (block_intro _ _
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

Lemma list_subst_actions__wf_cs_action_pre: forall (id' : id) (ac' : action)
  (id2 : atom) (acs3 : list (atom * action)) (ac2 : action) (l0 : l)
  (ps0 : phinodes) (cs : cmds) (tmn0 : terminator)
  pinfo (Hwfpi: WF_PhiInfo pinfo) s m 
  (HwfF: wf_fdef s m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo))
  (Hnotin: id' `notin` dom acs3) (Hneq: id2 <> id')
  (J : wf_cs_action_pre ((id', ac') :: acs3) cs (PI_id pinfo) (id2, ac2))
  (l5 : l) (ps5 : phinodes) (cs5 : cmds) (tmn5 : terminator)
  fh bs1 l1 ps1 cs1 tmn1 (Hin: In (block_intro l1 ps1 cs1 tmn1) bs1)
  (Hwf: wf_cs_action cs1 (PI_id pinfo) (id', ac')) 
  (Heq: PI_f pinfo = fdef_intro fh bs1)
  (HBinF: blockInFdefB (block_intro l0 ps0 cs tmn0) (PI_f pinfo) = true)
  (Heq5 : apply_action_block (block_intro l0 ps0 cs tmn0) (id', ac') =
          block_intro l5 ps5 cs5 tmn5),
  wf_cs_action_pre (ListComposedPass.subst_actions id' ac' acs3) cs5 
    (PI_id pinfo) (id2, subst_action_action ac2 (id', ac')).
Proof.
  intros.
  assert (HBinF': 
    blockInFdefB (block_intro l1 ps1 cs1 tmn1) (PI_f pinfo) = true).
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

Lemma wf_actions_cons_inv: forall fh bs fh' bs' id0 ac0 
  pinfo (Hwfpi: WF_PhiInfo pinfo) (Huniq: uniqFdef (PI_f pinfo)) actions
  (Heqpi: PI_f pinfo = fdef_intro fh bs) (Huniq': uniq actions)
  (Hnotin: id0 `notin` dom actions) s m (HwfF: wf_fdef s m (PI_f pinfo)) 
  (Heq: apply_action (fdef_intro fh bs) (id0, ac0) = fdef_intro fh' bs')
  (Hwf: wf_actions bs (PI_id pinfo) (PI_rd pinfo) ((id0, ac0) :: actions)),
  (exists l0, exists ps0, exists cs0, exists tmn0,
    In (block_intro l0 ps0 cs0 tmn0) bs /\ 
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
    case_eq (apply_action_block (block_intro l1 ps1 cs1 tmn1) (id0, ac0)).
    intros l5 ps5 cs5 tmn5 Heq5.
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
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo) f1 f2
  (Heqf2: f2 = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Heqf1: f1 = apply_action
                 (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
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

Lemma find_stld_pairs_blocks_spec: forall pid rd bs actions
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs),
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
| Hpass: elim_stld_fdef ?pid ?rd ?f1 = _ |- _ =>
  let fh := fresh "fh" in
  let bs1 := fresh "bs1" in
  let actions := fresh "actions" in
  let Hwf := fresh "Hwf" in
  unfold elim_stld_fdef in Hpass;
  destruct f1 as [fh bs1];
  remember (flat_map (find_stld_pairs_block pid rd) bs1)
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

Lemma pipelined_elim_stld_reachablity_successors: forall pid rd fh bs1 f2 actions
  (Heqactions : actions = flat_map (find_stld_pairs_block pid rd) bs1)
  (Hpass : pipelined_actions actions (fdef_intro fh bs1) = f2),
  reachablity_analysis f2 = reachablity_analysis (fdef_intro fh bs1) /\
    successors f2 = successors (fdef_intro fh bs1).
Admitted.

Lemma elim_stld_reachablity_successors: forall pid rd f1 f2
  (Hpass: elim_stld_fdef pid rd f1 = f2),
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
        match goal with
        | |- context [elim_stld_fdef ?pid ?rd ?f] =>
          destruct (elim_stld_reachablity_successors pid rd f 
                      (elim_stld_fdef pid rd f)); auto
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




