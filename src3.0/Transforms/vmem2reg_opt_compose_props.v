Require Import vellvm.
Require Import ListSet.
Require Import vmem2reg_opt.

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

Lemma in_dom__iff__in_rev_dom: forall i0 X (A:list (id*X)),
  i0 `in` dom A <-> i0 `in` dom (rev A).
Proof.
  induction A as [|[] A]; simpl.
    split; auto.

    rewrite dom_app. simpl.
    fsetdec.
Qed.

Lemma uniq__iff__uniq_rev: forall X (A:list (id*X)),
  uniq A <-> uniq (rev A).
Proof.
  induction A as [|[] A]; simpl.
    split; auto.

    split; intro J.
      inv J. 
      apply uniq_app_iff.
      split. apply IHA; auto.
      split. apply uniq_cons; auto.
        apply disjoint_one_r. 
        intro J. apply H3.
        eapply in_dom__iff__in_rev_dom; eauto.

      apply uniq_app_iff in J.
      destruct J as [J1 [J2 J3]].
      apply uniq_cons; auto.
        apply IHA; auto.

        apply disjoint_one_r in J3. 
        intro J. apply J3.
        apply in_dom__iff__in_rev_dom in J; auto.
Qed.

Definition ids_in_stld_state (st:stld_state) : list id :=
match st with
| STLD_store i1 _ => [i1]
| _ => nil
end.

Lemma In_fst__in_dom: forall X (A:list (id*X)) i0,
  In i0 (List.map fst A) <-> i0 `in` dom A.
Proof.
  induction A as [|[] A]; simpl; intros; auto.
    split; intro J.
      inv J. fsetdec.

    split; intro J.
      destruct J as [J | J]; subst; auto.
        apply IHA in J; auto.

      apply AtomSetFacts.add_iff in J.
      destruct J as [J | J]; subst; auto.
        apply IHA in J; auto.
Qed.

Lemma NoDup_fst__uniq: forall X (A:list (id*X)) (Huniq: NoDup (List.map fst A)), 
  uniq A.
Proof.
  induction A as [|[] A]; simpl; intros; auto.
    inv Huniq.
    apply uniq_cons; auto.
      intro J. apply H1. apply In_fst__in_dom; auto.
Qed.

Lemma find_stld_pairs_cmds_aux__uniq: forall pid cs s acs
  (Huniq : NoDup (getCmdsLocs cs ++ ids_in_stld_state s ++ List.map fst acs)),
  uniq (snd (fold_left (find_stld_pair_cmd pid) cs (s, acs))).
Proof.
  induction cs as [|c cs]; simpl; intros.
    apply NoDup_fst__uniq; auto.
    split_NoDup; auto.
 
    destruct c; simpl in *; try solve [inv Huniq; apply IHcs; auto].
      destruct_if; try (inv Huniq; apply IHcs; simpl; auto).
        eapply NoDup_strenthening; eauto.

      destruct value1; try (inv Huniq; apply IHcs; simpl; auto).
      destruct_if; try (inv Huniq; apply IHcs; simpl; auto).
      destruct s; try (inv Huniq; apply IHcs; simpl; auto).
        match goal with
        | |- context [?A ++ ?b :: ?c :: ?D] =>
          rewrite_env ((A++[b]) ++ c ::  D)
        end.
        apply NoDup_insert; simpl_env; auto.

        apply NoDup_insert; auto.

      destruct value2; try (inv Huniq; apply IHcs; simpl; auto).
      destruct_if; try (inv Huniq; apply IHcs; simpl; auto).
      destruct s; inv Huniq; apply IHcs; simpl; apply NoDup_insert; auto.
Qed.

Lemma find_stld_pairs_cmds__uniq: forall pid cs actions
  (Huniq: NoDup (getCmdsLocs cs))
  (Hfind: actions = find_stld_pairs_cmds cs pid),
  uniq actions.
Proof.
  unfold find_stld_pairs_cmds.
  intros. subst.
  apply -> uniq__iff__uniq_rev.
  apply find_stld_pairs_cmds_aux__uniq; simpl_env; auto.
Qed.

Lemma find_stld_pairs_block__uniq: forall pid rd b actions
  (Huniq: NoDup (getStmtsLocs (snd b)))
  (Hfind: actions = find_stld_pairs_block pid rd b),
  uniq actions.
Proof.
  destruct b as [? []]. simpl.
  intros.
  destruct_if; auto.
    split_NoDup.
    eapply find_stld_pairs_cmds__uniq; eauto.
Qed.

Lemma disj__disjoint: forall X (A2 B2:list (id*X)) A1 B1
  (Hdisj1: forall i, In i A1 -> ~ In i B1)
  (Hinca: forall a, a `in` dom A2 -> In a A1)
  (Hincb: forall b, b `in` dom B2 -> In b B1),
  disjoint A2 B2.
Proof.
  intros. unfold disjoint.
  unfold AtomSetImpl.Subset. intros a Hina.
  apply AtomSetFacts.inter_iff in Hina.
  destruct Hina as [Hina1 Hina2].
  apply Hinca in Hina1.
  apply Hincb in Hina2.
  apply Hdisj1 in Hina1. tauto.
Qed.

Definition id_in_stld_state (i0:id) (st:stld_state) : Prop :=
match st with
| STLD_store i1 _ => i0 = i1
| _ => False
end.

Lemma find_stld_pairs_cmds_aux__incl: forall pid cs acs s,
  forall (a : atom) 
  (Hin: a `in` dom (snd (fold_left (find_stld_pair_cmd pid) cs (s, acs)))), 
  In a (getCmdsLocs cs) \/ a `in` dom acs \/ id_in_stld_state a s.
Proof.
  induction cs as [|c cs]; simpl; intros; auto.
    destruct c; simpl; try (apply IHcs in Hin; tauto).
      destruct_if; subst; try (apply IHcs in Hin; tauto).

      destruct value1; try (apply IHcs in Hin; tauto).
      destruct_if; subst; try (apply IHcs in Hin; tauto).
      destruct s; apply IHcs in Hin; simpl in Hin; try tauto;
        destruct Hin; try solve [auto | fsetdec].

      destruct value2; try (apply IHcs in Hin; tauto).
      destruct_if; subst; try (apply IHcs in Hin; tauto).
      destruct s; apply IHcs in Hin; simpl in Hin; simpl;
        destruct Hin; try solve [auto | fsetdec].
Qed.

Lemma find_stld_pairs_cmds__incl: forall pid cs,
  forall (a : atom) (Hin: a `in` dom (find_stld_pairs_cmds cs pid)), 
  In a (getCmdsLocs cs).
Proof.
  unfold find_stld_pairs_cmds.
  intros.
  apply in_dom__iff__in_rev_dom in Hin.
  apply find_stld_pairs_cmds_aux__incl in Hin.
  simpl in Hin. 
  destruct Hin as [Hin | [Hin | Hin]]; auto.
    fsetdec. tauto.
Qed.

Lemma find_stld_pairs_block__incl: forall pid rd b,
  forall (a : atom) (Hin: a `in` dom (find_stld_pairs_block pid rd b)), 
  In a (getStmtsLocs (snd b)).
Proof.
  destruct b as [? []]. simpl.
  destruct_if; intros.
    apply find_stld_pairs_cmds__incl in Hin.
    xsolve_in_list.

    simpl in Hin. fsetdec.
Qed.

Lemma find_stld_pairs_blocks__incl: forall pid rd bs,
  forall a : atom,
  a `in` dom (flat_map (find_stld_pairs_block pid rd) bs) -> 
  In a (getBlocksLocs bs).
Proof.
  induction bs as [|b bs]; simpl; intros; subst.
    fsetdec.
    
    apply in_or_app.
    rewrite dom_app in H.
    apply AtomSetFacts.union_iff in H.
    destruct H as [H | H]; eauto using find_stld_pairs_block__incl.
Qed.

Lemma find_stld_pairs_blocks__uniq: forall pid rd bs actions
  (Huniq: NoDup (getBlocksLocs bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs),
  uniq actions.
Proof.
  induction bs as [|b bs]; simpl; intros; subst.
    constructor.

    apply uniq_app_iff.
    assert (J:=Huniq).
    apply NoDup_split in J. destruct J as [J1 J2].
    split.
      eapply find_stld_pairs_block__uniq; eauto.
    split; auto.
      apply disj__disjoint with (A1:=getStmtsLocs (snd b)) (B1:=getBlocksLocs bs); 
        auto.
        intros. eapply NoDup_disjoint'; eauto.
        apply find_stld_pairs_block__incl; auto.
        apply find_stld_pairs_blocks__incl; auto.
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

Lemma find_stld_pairs_blocks_acyclic: forall pid rd bs actions
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs),
  acyclic_actions actions.
Admitted.

Lemma list_compose_actions__list_composed_substs: forall actions 
  (Hacyclic: acyclic_actions actions) (Huniq: uniq actions) f,
  ListComposedPass.substs_fdef (ListComposedPass.compose_actions actions) f =
  composed_pipelined_actions actions f.
Admitted.

