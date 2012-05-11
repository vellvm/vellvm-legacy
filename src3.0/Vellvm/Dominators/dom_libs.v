Require Export Coqlib.
Require Export Metatheory.
Require Export Maps.
Require Import infrastructure_props.
Require Import Program.Tactics.

Lemma Pnlt__Pgt_Peq : forall n m: positive, 
  ~ ((n < m)%positive) -> (n > m)%positive \/ (n = m)%positive.
Proof.
  unfold BinPos.Plt, Pgt.
  intros.
  remember ((n ?= m)%positive Eq) as R.
  destruct R; try solve [congruence | auto].
    symmetry in HeqR.
    apply Pcompare_Eq_eq in HeqR. auto.
Qed.

Lemma Pgt_trans : forall (n m p : positive)
  (H1: (n > m)%positive) (H2: (m > p)%positive), (n > p)%positive.
Proof.
  unfold Pgt; intros.
  apply ZC2. apply ZC1 in H1. apply ZC1 in H2.
  eapply Plt_trans; eauto.
Qed.

Lemma is_tail_Forall: forall A (l1 l2:list A) P (Hp2: Forall P l2)
  (Htail: is_tail l1 l2), Forall P l1.
Proof.
  induction 2; auto.
    inv Hp2. auto.
Qed.

Lemma order_lt_order: forall p x (Horder : (p > x)%positive) l0
  (Horder : Forall (Plt p) l0),
  Forall (Plt x) l0.
Proof.
  induction 2; simpl; intros; constructor; auto.
    eapply Plt_trans; eauto.
    apply ZC1. auto.
Qed.

Section MoreMove. (* copied from dtree.v *)

Variable A: Type.
Hypothesis Hdec: forall x y : A, {x = y} + {x <> y}.

Lemma remove_length: forall (a: A) (l1: list A),
  (length (List.remove Hdec a l1) <= length l1)%nat.
Proof.
  induction l1; simpl; intros.
    omega.
    destruct (Hdec a a0); subst; simpl; omega.
Qed.

Lemma remove_in_length: forall (a: A) (l1: list A),
  In a l1 -> (length (List.remove Hdec a l1) < length l1)%nat.
Proof.
  induction l1; simpl; intros.
    inv H.

    destruct H as [H | H]; subst.
      destruct (Hdec a a); try congruence.
      assert (J:=@remove_length a l1). omega.

      destruct (Hdec a a0); subst.
        assert (J:=@remove_length a0 l1). omega.
        assert (J:=@IHl1 H). simpl. omega.
Qed.

Lemma remove_neq_in: forall (a b:A) (l1: list A),
  a <> b ->
  In a l1 ->
  In a (List.remove Hdec b l1).
Proof.
  induction l1; simpl; intros; auto.
    destruct H0 as [H0 | H0]; subst.
      destruct (Hdec b a); subst; simpl; auto.
        congruence.
      destruct (Hdec b a0); subst; simpl; auto.
Qed.

Lemma remove_notin_incl: forall (a : A) (l2 l1 : list A)
  (Hinc : incl l1 l2) (Hnotin : ~ In a l1),
  incl l1 (List.remove Hdec a l2).
Proof.
  intros. intros x Hin.
  destruct (Hdec x a); subst.
    congruence.
    apply remove_neq_in; auto.
Qed.

Lemma remove_neq_in': forall (a b:A) (l1: list A),
  In a (List.remove Hdec b l1) ->
  In a l1 /\ a <> b.
Proof.
  induction l1; simpl; intros; auto.
    destruct (Hdec b a0); subst; simpl.
      apply IHl1 in H.
      destruct H as [H1 H2].
      split; auto.

      simpl in H.
      destruct H as [H | H]; subst; auto.
      apply IHl1 in H.
      destruct H as [H1 H2].
      split; auto.
Qed.

End MoreMove.

(* More properties of Coqlib *)

Lemma is_tail_nil: forall A (l1:list A), is_tail nil l1.
Proof.
  induction l1; constructor; auto.
Qed.

Lemma incl__length_le: forall A (eq_dec : forall x y : A, {x = y}+{x <> y})
  (l1:list A) (Huniq: list_norepet l1) (l2:list A) (Hinc: incl l1 l2), 
  (length l1 <= length l2)%nat.
Proof.
  induction 2 as [|hd tl Hnotin Huniq IH]; simpl; intros.
    auto with datatypes v62.

    assert (incl tl (List.remove eq_dec hd l2)) as Hinc'.
      apply remove_notin_incl; eauto with datatypes v62.
    apply IH in Hinc'.
    assert (length (List.remove eq_dec hd l2) < length l2)%nat as Hle.
      apply remove_in_length; auto with datatypes v62.
    omega.
Qed.

Lemma list_equiv_nil: forall A (l1:list A) (Heq: list_equiv nil l1), l1 = nil.
Proof.
  intros.
  destruct l1 as [|x l1]; auto.
  destruct (Heq x) as [_ J1].
  assert (In x (x::l1)) as J. auto with datatypes v62.
  apply J1 in J. inv J.
Qed.

Lemma norepet_equiv__length_eq: forall A (l1:list A)
  (Huniq1: list_norepet l1) (l2:list A) (Huniq2: list_norepet l2)
  (Heq: list_equiv l1 l2),
  (length l1 = length l2)%nat.
Proof.
  induction 1; simpl; intros.
    apply list_equiv_nil in Heq. subst. auto.

    destruct (Heq hd) as [J1 _].
    assert (In hd (hd::tl)) as J2. auto with datatypes v62.
    apply J1 in J2.
    apply in_split in J2.
    destruct_conjs; subst.
    rewrite app_length. simpl.
    rewrite IHHuniq1 with (l2:=J2++H0).
      rewrite app_length.
      omega.

      apply list_norepet_append_commut in Huniq2.
      simpl_env in Huniq2.
      apply list_norepet_append_commut.
      apply list_norepet_app in Huniq2.
      tauto.

      apply list_norepet_append_commut in Huniq2.
      simpl_env in Huniq2.
      apply list_norepet_app in Huniq2.
      destruct_conjs.
      intro x.
      destruct (Heq x) as [J1' J2'].
      split; intro J.
        assert (Hin: In x (hd::tl)). auto with datatypes v62.
        apply J1' in Hin.
        destruct_in Hin; auto with datatypes v62.
        destruct_in Hin; auto with datatypes v62.

        assert (Hin: In x (J2 ++ hd :: H0)). 
          destruct_in J; auto with datatypes v62.
        apply J2' in Hin.
        destruct_in Hin; auto with datatypes v62.
        assert (x <> x) as Hf.
          apply H3; simpl; auto with datatypes v62.     
          destruct_in J; auto with datatypes v62.
        congruence.
Qed.

Lemma norepet_equiv__length_cons_eq: forall A l1 l2 (a:A)
  (Huniq1: list_norepet l1) (Huniq2: list_norepet l2)
  (Hnotin: ~ In a l1) (Heq: list_equiv l2 (a::l1)),
  (length l2 = length l1 + 1)%nat.
Proof.
  intros.
  apply norepet_equiv__length_eq in Heq; auto.
    simpl in *. omega.
    constructor; auto.
Qed.

Module More_Tree_Properties(T: TREE).

Module TProp := Tree_Properties(T).

Notation "a ! b" := (T.get b a) (at level 1).
Notation "a !! b" := (T.get b a) (at level 1).

Definition successors_list A (successors: T.t (list A)) (pc: T.elt) 
  : list A :=
  match successors!pc with None => nil | Some l => l end.

Implicit Arguments successors_list [A].

Notation "a !!! b" := (successors_list a b) (at level 1).

Lemma successors_list_spec: forall A (a:A) scss l0,
  In a (scss!!!l0) -> exists scs, scss!l0 = Some scs /\ In a scs.
Proof.
  unfold successors_list.
  intros.
  destruct (scss!l0); [eauto | tauto].
Qed.

Section Predecessor. (* from Kidall.v, should use this *)

Variable successors: T.t (list T.elt).

Fixpoint add_successors (pred: T.t (list T.elt))
                        (from: T.elt) (tolist: list T.elt)
                        {struct tolist} : T.t (list T.elt) :=
  match tolist with
  | nil => pred
  | to :: rem => add_successors (T.set to (from :: pred!!!to) pred) from rem
  end.

Lemma add_successors_correct:
  forall tolist from pred n s,
  In n pred!!!s \/ (n = from /\ In s tolist) ->
  In n (add_successors pred from tolist)!!!s.
Proof.
  induction tolist; simpl; intros.
  tauto.
  apply IHtolist.
  unfold successors_list at 1. rewrite T.gsspec.
  destruct (T.elt_eq s a).
    subst a. 
    destruct H. 
      auto with coqlib.
      destruct H.
        subst n. auto with coqlib.
    fold (successors_list pred s). intuition congruence.
Qed.

Lemma add_successors_correct':
  forall tolist from pred n s,
  In n (add_successors pred from tolist)!!!s ->
  In n pred!!!s \/ (n = from /\ In s tolist).
Proof.
  induction tolist; simpl; intros.
  tauto.
  apply IHtolist in H.
  unfold successors_list at 1 in H.
  rewrite T.gsspec in H.
  destruct (T.elt_eq s a); subst.
    simpl in H.
    destruct H.
      destruct H; subst; auto.
      destruct H as [H1 H2]; subst; auto.

      fold (successors_list pred s) in H. intuition congruence.
Qed.

Lemma add_successors_correct'': forall (m a : T.t (list T.elt)) 
  (k : T.elt) (v : list T.elt)
  (Herr : m ! k = None) (l1 l2 : T.elt)
  (Hinc: In l1 a !!! l2 -> In l2 m !!! l1)
  (Hin: In l1 (add_successors a k v) !!! l2), In l2 (T.set k v m) !!! l1.
Proof.
  intros.
  apply add_successors_correct' in Hin. 
  unfold successors_list.
  rewrite T.gsspec.
  destruct (T.elt_eq l1 k).
    destruct Hin as [Hin | [EQ Hin]]; subst; auto.
      apply Hinc in Hin.
      unfold successors_list in Hin.
      rewrite Herr in Hin. tauto.
 
    destruct Hin as [Hin | [EQ Hin]]; subst; try congruence.
      apply Hinc in Hin. 
      unfold successors_list in Hin.
      auto.    
Qed.

Definition make_predecessors : T.t (list T.elt) :=
  T.fold add_successors successors (T.empty (list T.elt)).

Lemma make_predecessors_correct:
  forall n s,
  In s successors!!!n ->
  In n make_predecessors!!!s.
Proof.
  set (P := fun succ pred =>
          forall n s, In s succ!!!n -> In n pred!!!s).
  unfold make_predecessors.
  apply TProp.fold_rec with (P := P).
(* extensionality *)
  unfold P; unfold successors_list; intros.
  rewrite <- H in H1. auto.
(* base case *)
  red; unfold successors_list. intros n s. repeat rewrite T.gempty. auto.
(* inductive case *)
  unfold P; intros. apply add_successors_correct.
  unfold successors_list in H2. rewrite T.gsspec in H2.
  destruct (T.elt_eq n k).
  subst k. auto.
  fold (successors_list m n) in H2. auto.
Qed.

Lemma make_predecessors_correct':
  forall n s,
  In n make_predecessors!!!s ->
  In s successors!!!n.
Proof.
  set (P := fun succ pred =>
          forall n s, In n pred!!!s -> In s succ!!!n).
  unfold make_predecessors.
  apply TProp.fold_rec with (P := P).
(* extensionality *)
  unfold P; unfold successors_list; intros.
  rewrite <- H. auto.
(* base case *)
  red; unfold successors_list. intros n s. repeat rewrite T.gempty. auto.
(* inductive case *)
  unfold P; intros. apply add_successors_correct' in H2.
  unfold successors_list in *. rewrite T.gsspec.
  destruct H2 as [H2 | [Heq H2]]; subst.
    destruct (T.elt_eq n k); subst; auto.
      apply H1 in H2. unfold successors_list in H2. rewrite H in H2. inv H2.
    destruct (T.elt_eq k k); subst; auto.
      congruence.
Qed.

Lemma eq_eli__eq_successors_list: forall (m m':T.t (list T.elt)) x
  (Heq: m ! x = m' ! x), m !!! x = m' !!! x.
Proof.
  intros.
  unfold successors_list.
  erewrite Heq. auto.
Qed.

End Predecessor.

Definition children_of_tree A (tree: T.t (list A)) :=
  flat_map snd (T.elements tree).

Definition parents_of_tree A (tree: T.t A) :=
  List.map fst (T.elements tree).

Implicit Arguments children_of_tree [A].
Implicit Arguments parents_of_tree [A].

Lemma children_in_children_of_tree: forall A (succs:T.t (list A)) l0,
  incl (succs !!! l0) (children_of_tree succs).
Proof.
  intros.
  intros x Hin.
  apply in_flat_map.
  apply successors_list_spec in Hin.
  destruct_conjs.
  eauto using T.elements_correct.
Qed.

Lemma parents_of_tree_spec: forall A l0 (tr: T.t A),
  In l0 (parents_of_tree tr) <-> exists a, In (l0, a) (T.elements tr).
Proof.
  unfold parents_of_tree.
  intros.
  split; intro J.
    apply in_map_iff in J.
    destruct J as [[x1 x2] [J1 J2]]. subst. eauto.

    apply in_map_iff.
    destruct J as [y J]. exists (l0, y). auto.
Qed.

Lemma notin_tree__notin_parents_of_tree: forall (visited : T.t unit)
  l0 (H0 : visited ! l0 = None),
  ~ In l0 (parents_of_tree visited).
Proof.
  intros.
  intros Hin'. apply parents_of_tree_spec in Hin'.
  destruct Hin' as [a Hin'].
  apply T.elements_complete in Hin'. 
  congruence.
Qed.

Lemma in_tree__in_parents_of_tree: forall (visited : T.t unit) a
  l0 (H0 : visited ! l0 = Some a),
  In l0 (parents_of_tree visited).
Proof.
  intros.
  apply parents_of_tree_spec. 
  apply T.elements_correct in H0.  eauto.
Qed.

Lemma parents_children_of_tree__inc__length_le: forall 
  (eq_dec : forall x y : T.elt, {x = y}+{x <> y}) (visited:T.t T.elt)
  succs (Hinc: incl (parents_of_tree visited) (children_of_tree succs)),
  (length (parents_of_tree visited) <= length (children_of_tree succs))%nat.
Proof.
  intros. 
  apply incl__length_le; auto.
    apply T.elements_keys_norepet.
Qed.

Lemma parents_of_tree_succ_len: forall (visited : T.t unit)
  l0 (H0 : visited ! l0 = None),
  length (parents_of_tree (T.set l0 tt visited)) =
    (length (parents_of_tree visited) + 1)%nat.
Proof.
  intros.
  unfold parents_of_tree.
  apply norepet_equiv__length_cons_eq with (a:=l0); 
    auto using T.elements_keys_norepet.
    apply notin_tree__notin_parents_of_tree; auto.

    intro x; split; intro Hin.
      apply parents_of_tree_spec in Hin.
      destruct_conjs.
      apply T.elements_complete in H. 
      rewrite T.gsspec in H.
      destruct_if.
        auto with datatypes v62.

        apply in_tree__in_parents_of_tree in H2.
        auto with datatypes v62.

      apply parents_of_tree_spec.
      destruct_in Hin.
        exists tt.
        apply T.elements_correct.
        rewrite T.gsspec.
        destruct_if. 
          congruence.

        apply parents_of_tree_spec in Hin.
        destruct_conjs.
        exists Hin. 
        apply T.elements_correct.
        rewrite T.gsspec.
        destruct_if. 
          apply T.elements_complete in H.  
          congruence.

          apply T.elements_complete in H. auto.
Qed.

Lemma parents_of_empty_tree: forall A,
  parents_of_tree (T.empty A) = nil.
Proof. 
  unfold parents_of_tree. 
  intros.
  remember (List.map fst (T.elements (T.empty A))) as R.
  destruct R as [|e]; auto. 
  assert (In e (List.map fst (T.elements (T.empty A)))) as Hin.
    rewrite <- HeqR. auto with coqlib.
  apply in_map_iff in Hin.
  destruct_conjs.
  apply T.elements_complete in H0.
  rewrite T.gempty in H0.
  congruence.
Qed.

Definition in_cfg successors n : Prop :=
  In n (parents_of_tree successors) \/ 
  In n (children_of_tree successors).

Lemma in_parents_of_tree__in_cfg: forall scs n,
  In n (parents_of_tree scs) -> in_cfg scs n.
Proof. unfold in_cfg. auto. Qed.

Lemma in_succ__in_cfg: forall p scs sc
  (Hinscs : In sc scs !!! p),
  in_cfg scs sc.
Proof.
  intros. right.
  apply children_in_children_of_tree in Hinscs. auto.
Qed.

Lemma parents_of_tree__in_successors: forall A p (successors:T.t A),
  In p (parents_of_tree successors) <-> exists s, successors ! p = Some s.
Proof.
  intros.
  split; intro J.
    apply parents_of_tree_spec in J.
    destruct J as [? J].
    apply T.elements_complete in J. eauto.

    apply parents_of_tree_spec.
    destruct J as [? J].
    apply T.elements_correct in J. eauto.
Qed.

Lemma in_pred__in_parents: forall p scs n
  (Hinprds : In p (make_predecessors scs) !!! n),
  In p (parents_of_tree scs).
Proof.
  intros.
  apply make_predecessors_correct' in Hinprds.
  apply parents_of_tree_spec.
  apply successors_list_spec in Hinprds.
  destruct Hinprds as [scs0 [J1 J2]].
  apply T.elements_correct in J1. eauto.
Qed.

End More_Tree_Properties.

Module XATree := More_Tree_Properties(ATree).

Notation "a !!! b" := (XATree.successors_list a b) (at level 1).

Notation "a ? b" := (PTree.get b a) (at level 1).
Notation "a ?? b" := (PMap.get b a) (at level 1).

Module XPTree := More_Tree_Properties(PTree).

Notation "a ??? b" := (XPTree.successors_list a b) (at level 1).

Module Type PNODE_SET.

  Variable t: Type.
  Variable add: positive -> t -> t.
  Variable pick: t -> option (positive * t).
  Variable initial: PTree.t (list positive) -> t.

  Variable In: positive -> t -> Prop.
  Hypothesis add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Hypothesis pick_none:
    forall s n, pick s = None -> ~In n s.
  Hypothesis pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Hypothesis initial_spec:
    forall successors n s,
    successors ? n = Some s -> In n (initial successors).

End PNODE_SET.

Require Import FSets.
Require Import FSetAVL.
Require Import Ordered.

Module PositiveSet := FSetAVL.Make(OrderedPositive).
Module PositiveSetFacts := FSetFacts.Facts(PositiveSet).
Module PTree_Properties := Tree_Properties(PTree).

Module PNodeSetMax <: PNODE_SET.
  Definition t := PositiveSet.t.
  Definition add (n: positive) (s: t) : t := PositiveSet.add n s.
  Definition pick (s: t) :=
    match PositiveSet.max_elt s with
    | Some n => Some(n, PositiveSet.remove n s)
    | None => None
    end.
  Definition initial (successors: PTree.t (list positive)) :=
    PTree.fold (fun s pc scs => PositiveSet.add pc s) successors PositiveSet.empty.
  Definition In := PositiveSet.In.

  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Proof.
    intros. exact (PositiveSetFacts.add_iff s n n').
  Qed.

  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
  Proof.
    intros until n; unfold pick. caseEq (PositiveSet.max_elt s); intros.
    congruence.
    apply PositiveSet.max_elt_3. auto.
  Qed.

  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Proof.
    intros until s'; unfold pick. caseEq (PositiveSet.max_elt s); intros.
    inversion H0; clear H0; subst.
    split; intros.
    destruct (peq n n'). auto. right. apply PositiveSet.remove_2; assumption.
    elim H0; intro. subst n'. apply PositiveSet.max_elt_1. auto.
    apply PositiveSet.remove_3 with n; assumption.
    congruence.
  Qed.

  Lemma initial_spec:
    forall successors n s,
    successors ? n = Some s -> In n (initial successors).
  Proof.
    intros successors.
    apply PTree_Properties.fold_rec with
      (P := fun succ set =>
              forall n s, succ ? n = Some s -> In n set).
    (* extensionality *)
    intros. rewrite <- H in H1. eauto.
    (* base case *)
    intros. rewrite PTree.gempty in H. congruence.
    (* inductive case *)
    intros. rewrite PTree.gsspec in H2. rewrite add_spec.
    destruct (peq n k). auto. eauto.
  Qed.

  Lemma pick_in:
    forall s n s', pick s = Some(n, s') -> In n s.
  Proof.
    intros until s'; unfold pick. 
    caseEq (PositiveSet.max_elt s); intros; try congruence.
    uniq_result.
    apply PositiveSet.max_elt_1. auto.
  Qed.
  
  Lemma pick_notin:
    forall s n s', pick s = Some(n, s') -> ~ In n s'.
  Proof.
    intros until s'; unfold pick. 
    caseEq (PositiveSet.max_elt s); intros; try congruence.
    uniq_result.
    apply PositiveSet.remove_1. auto.
  Qed.
  
  Lemma pick_max:
    forall s n s', pick s = Some(n, s') -> 
      PositiveSet.max_elt s = Some n.
  Proof.
    intros until s'; unfold pick. 
    caseEq (PositiveSet.max_elt s); intros; try congruence.
  Qed.
  
  Lemma pick_remove:
    forall s n s', pick s = Some(n, s') -> s' = PositiveSet.remove n s.
  Proof.
    intros until s'; unfold pick. 
    caseEq (PositiveSet.max_elt s); intros; try congruence.
  Qed.
  
  Lemma initial_spec':
    forall successors n,
    In n (initial successors) -> 
    exists s, successors ? n = Some s.
  Proof.
    intros successors.
    apply PTree_Properties.fold_rec with
      (P := fun succ set =>
              forall n, In n set -> exists s, succ ? n = Some s).
    (* extensionality *)
    intros. rewrite <- H. eauto.
    (* base case *)
    intros. apply PositiveSet.empty_1 in H. tauto.
    (* inductive case *)
    intros. rewrite PTree.gsspec. rewrite add_spec in H2.
    destruct (peq n k); eauto.
      destruct H2 as [H2 | H2]; subst.
        congruence.
        eauto.
  Qed.
  
End PNodeSetMax.

Module PNodeSetMin <: PNODE_SET.
  Definition t := PositiveSet.t.
  Definition add (n: positive) (s: t) : t := PositiveSet.add n s.
  Definition pick (s: t) :=
    match PositiveSet.min_elt s with
    | Some n => Some(n, PositiveSet.remove n s)
    | None => None
    end.
  Definition initial (successors: PTree.t (list positive)) :=
    PTree.fold (fun s pc scs => PositiveSet.add pc s) successors PositiveSet.empty.
  Definition In := PositiveSet.In.

  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Proof.
    intros. exact (PositiveSetFacts.add_iff s n n').
  Qed.

  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
  Proof.
    intros until n; unfold pick. caseEq (PositiveSet.min_elt s); intros.
    congruence.
    apply PositiveSet.min_elt_3. auto.
  Qed.

  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Proof.
    intros until s'; unfold pick. caseEq (PositiveSet.min_elt s); intros.
    inversion H0; clear H0; subst.
    split; intros.
    destruct (peq n n'). auto. right. apply PositiveSet.remove_2; assumption.
    elim H0; intro. subst n'. apply PositiveSet.min_elt_1. auto.
    apply PositiveSet.remove_3 with n; assumption.
    congruence.
  Qed.

  Lemma initial_spec:
    forall successors n s,
    successors ? n = Some s -> In n (initial successors).
  Proof.
    intros successors.
    apply PTree_Properties.fold_rec with
      (P := fun succ set =>
              forall n s, succ ? n = Some s -> In n set).
    (* extensionality *)
    intros. rewrite <- H in H1. eauto.
    (* base case *)
    intros. rewrite PTree.gempty in H. congruence.
    (* inductive case *)
    intros. rewrite PTree.gsspec in H2. rewrite add_spec.
    destruct (peq n k). auto. eauto.
  Qed.
End PNodeSetMin.

Require Import list_facts.

Module Type MERGE.

  Variable Pcmp: positive -> positive -> Prop.
  Variable merge : list positive -> list positive -> list positive * bool.
  Hypothesis merge_cmp_cons: forall p ps (Hlt: Forall (Pcmp p) ps),
    merge ps (p :: ps) = (ps, false).

End MERGE.

Ltac uniq_result' :=
match goal with
| H: Eq = (_ ?= _)%positive Eq |- _ => 
    symmetry in H; apply Pcompare_Eq_eq in H; subst
| H: (_ ?= _)%positive Eq = Eq |- _ => 
    apply Pcompare_Eq_eq in H; subst
| _ => uniq_result
end.

Require Import cpdt_tactics.

Ltac fill_holes_in_ctx :=
let fill e H :=
  match goal with
  | H1: _ = e |- _ => rewrite <- H1 in H
  | H1: e = _ |- _ => rewrite H1 in H
  end
in
repeat match goal with
| H: match ?e with
     | Some _ => _
     | None => _
     end |- _ => fill e H
| H: match ?e with
     | inl _ => _
     | inr _ => _
     end |- _ => fill e H
| H: match ?e with
     | (_,_) => _
     end = _ |- _ => fill e H
| H: _ = match ?e with
     | (_,_) => _
     end |- _ => fill e H
end.

Ltac destruct_let :=
match goal with
| _:context [match ?e with
             | (_, _) => _
             end] |- _ => remember e as R; destruct R
| |- context [match ?e with
              | (_, _) => _
              end] => remember e as R; destruct R
end.

Module MergeLt <: MERGE.

  Definition Pcmp := Plt.

  Program Fixpoint merge_aux (l1 l2: list positive) (acc:list positive * bool)
    {measure (length l1 + length l2)%nat}
    : (list positive * bool) :=
  let '(rl, changed) := acc in
  match l1, l2 with
  | p1::l1', p2::l2' =>
      match (Pcompare p1 p2 Eq) with
      | Eq => merge_aux l1' l2' (p1::rl, changed)
      | Lt => merge_aux l1' l2 (rl, true)
      | Gt => merge_aux l1 l2' (rl, changed)
      end
  | nil, _ => acc
  | _::_, nil => (rl, true)
  end.
  Next Obligation.
    simpl. omega.
  Qed.
  Next Obligation.
    simpl. omega.
  Qed.
  
  Definition merge_aux_spec_prop (n:nat) := forall Xsdms Ysdms
    (Hlen: (length Xsdms + length Ysdms = n)%nat)
    rl1 changed1 rl2 changed2 
    (Hmerge: merge_aux Xsdms Ysdms (rl1, changed1) = (rl2, changed2)),
    exists rl3, rl2 = rl3 ++ rl1 /\ 
                sublist (List.rev rl3) Xsdms /\
                sublist (List.rev rl3) Ysdms /\
                (changed2 = false -> (List.rev rl3) = Xsdms) /\
                (changed1 = true -> changed2 = true).

  Ltac fold_merge_aux :=
  match goal with
  | |- context [merge_aux_func (existT _ ?arg1 (existT _ ?arg2 ?arg3))] => 
         fold (merge_aux arg1 arg2 arg3)
  end.

  Ltac unfold_merge_aux :=
  match goal with
  | |- appcontext [merge_aux ?arg] =>
     unfold merge_aux; unfold merge_aux_func;
     Program.Wf.WfExtensionality.unfold_sub merge_aux arg; simpl;
     repeat Program.Wf.fold_sub merge_aux_func;
     repeat fold_merge_aux
  end.

  Lemma merge_aux_spec_aux: forall n, merge_aux_spec_prop n.
  Proof.
    intro n.
    elim n using (well_founded_induction lt_wf).
    intros x Hrec.
    unfold merge_aux_spec_prop; intros.
    destruct Xsdms as [|Xd Xsdms]; destruct Ysdms as [|Yd Ysdms]; 
      simpl in Hlen; try solve [contradict Hlen; simpl; omega].
      compute in Hmerge. uniq_result.
      exists nil. simpl. repeat (split; try solve [auto | constructor]).

      compute in Hmerge. uniq_result. 
      exists nil. simpl. repeat (split; try solve [auto | constructor]).

      compute in Hmerge. uniq_result. 
      exists nil. simpl. 
      repeat (split; try solve [auto | constructor | congruence]).
  
      uniq_result.
      revert Hmerge. unfold_merge_aux.
      remember ((Xd ?= Yd)%positive Eq) as Cmp.
      intro.
      destruct Cmp; subst.
        apply Hrec with (y:=(length Xsdms + length Ysdms)%nat) in Hmerge; 
          try solve [simpl; omega].
        destruct Hmerge as [rl3 [J1 [J2 [J3 [J4 J5]]]]].
        subst.
        exists (rl3++[Xd]). simpl_env.
        rewrite rev_app_distr. simpl. 
        uniq_result'.
        repeat (split; try solve [auto | constructor; auto]).
          crush.
        
        apply Hrec with (y:=(length Xsdms + S (length Ysdms))%nat) in Hmerge; 
           try solve [simpl; omega].
        destruct Hmerge as [rl3 [J1 [J2 [J3 [J4 J5]]]]].
        subst.
        exists rl3. 
        repeat (split; try solve [auto | constructor; auto]).
          crush.
        
        apply Hrec with (y:=(S (length Xsdms) + length Ysdms)%nat) in Hmerge; 
           try solve [simpl; omega].
        destruct Hmerge as [rl3 [J1 [J2 [J3 [J4 J5]]]]].
        subst.
        exists rl3. 
        repeat (split; try solve [auto | constructor; auto]).
  Qed.

  Lemma merge_aux_spec: forall Xsdms Ysdms rl1 changed1 rl2 changed2 
    (Hmerge: merge_aux Xsdms Ysdms (rl1, changed1) = (rl2, changed2)),
    exists rl3, rl2 = rl3 ++ rl1 /\ 
                sublist (List.rev rl3) Xsdms /\
                sublist (List.rev rl3) Ysdms /\
                (changed2 = false -> (List.rev rl3) = Xsdms) /\
                (changed1 = true -> changed2 = true).
  Proof.
    intros.
    assert (J:=@merge_aux_spec_aux (length Xsdms + length Ysdms)).
    unfold merge_aux_spec_prop in J.
    auto.
  Qed.
  
  Definition merge (l1 l2: list positive) : (list positive * bool) :=
    let '(rl, changed) := merge_aux l1 l2 (nil, false) in
    (rev rl, changed).

  Lemma merge_spec: forall Xsdms Ysdms rl changed 
    (Hmerge: merge Xsdms Ysdms = (rl, changed)),
    sublist rl Xsdms /\ sublist rl Ysdms /\
    (changed = false -> rl = Xsdms).
  Proof.
    unfold merge.
    intros.
    destruct_let.
    fill_holes_in_ctx. uniq_result.
    symmetry in HeqR.
    apply merge_aux_spec in HeqR.
    destruct_conjs.
    subst. simpl_env.
    crush.
  Qed.

  Definition merge_aux_commut_prop (n:nat) := forall Xsdms Ysdms
    (Hlen: (length Xsdms + length Ysdms = n)%nat)
    rl1 changed1 changed1' rl2 changed2 rl2' changed2' 
    (Hmerge: merge_aux Xsdms Ysdms (rl1, changed1) = (rl2, changed2))
    (Hmerge': merge_aux Ysdms Xsdms (rl1, changed1') = (rl2', changed2')),
    rl2 = rl2'.

  Lemma merge_aux_commut_aux: forall n, merge_aux_commut_prop n.
  Proof.
    intro n.
    elim n using (well_founded_induction lt_wf).
    intros x Hrec.
    unfold merge_aux_commut_prop; intros.
    destruct Xsdms as [|Xd Xsdms]; destruct Ysdms as [|Yd Ysdms]; 
      simpl in Hlen; try solve [contradict Hlen; simpl; omega].
      compute in Hmerge, Hmerge'. uniq_result. auto.
      compute in Hmerge, Hmerge'. uniq_result. auto.
      compute in Hmerge, Hmerge'. uniq_result. auto.
  
      revert Hmerge. unfold_merge_aux. intro.
      revert Hmerge'. unfold_merge_aux. intro.
      remember ((Xd ?= Yd)%positive Eq) as Cmp.
      destruct Cmp; subst.
        uniq_result'.
        rewrite Pcompare_refl in Hmerge'.
        eapply Hrec with (y:=(length Xsdms + length Ysdms)%nat); 
          try solve [eauto | simpl; omega].

        rewrite ZC2 in Hmerge'; auto.
        eapply Hrec with (y:=(length Xsdms + S (length Ysdms))%nat); 
          eauto; simpl; omega.

        rewrite ZC1 in Hmerge'; auto.
        eapply Hrec with (y:=(S (length Xsdms) + length Ysdms)%nat); 
          eauto; simpl; omega.
  Qed.

  Lemma merge_commut: forall Xsdms Ysdms rl changed rl' changed'
    (Hmerge: merge Xsdms Ysdms = (rl, changed))
    (Hmerge': merge Ysdms Xsdms = (rl', changed')),
    rl = rl'.
  Proof.
    unfold merge.
    intros. destruct_let. destruct_let. uniq_result.
    assert (J:=@merge_aux_commut_aux (length Xsdms + length Ysdms)).
    unfold merge_aux_commut_prop in J.
    f_equal. eauto.
  Qed.

  Definition merge_aux_refl_prop (n:nat) := forall Xsdms
    (Hlen: (length Xsdms + length Xsdms = n)%nat) rl changed,
    merge_aux Xsdms Xsdms (rl, changed) = (rev Xsdms++rl, changed).

  Lemma merge_aux_refl_aux: forall n, merge_aux_refl_prop n.
  Proof.
    intro n.
    elim n using (well_founded_induction lt_wf).
    intros x Hrec.
    unfold merge_aux_refl_prop; intros.
    destruct Xsdms as [|Xd Xsdms];
      simpl in Hlen; try solve [contradict Hlen; simpl; omega].
      compute. auto.
  
      unfold_merge_aux. 
      simpl_env.
      rewrite Pcompare_refl. 
      erewrite Hrec with (y:=(length Xsdms + length Xsdms)%nat); 
        try solve [eauto | simpl; omega].
  Qed.

  Lemma merge_refl: forall Xsdms, merge Xsdms Xsdms = (Xsdms, false).
  Proof.
    unfold merge. intros. destruct_let.
    assert (J:=@merge_aux_refl_aux (length Xsdms + length Xsdms)).
    unfold merge_aux_refl_prop in J.
    rewrite J in HeqR; auto.
    uniq_result. simpl_env.
    rewrite rev_involutive. auto.
  Qed.

  Lemma merge_cmp_cons: forall p ps (Hlt: Forall (Plt p) ps),
    merge ps (p :: ps) = (ps, false).
  Proof.
    destruct 1; intros.
      compute. auto.

      unfold merge. unfold_merge_aux.
      rewrite ZC2; auto.
      erewrite merge_aux_refl_aux; eauto.
      simpl_env.
      rewrite rev_involutive. auto.
  Qed.

End MergeLt.

(*
Module MergeGt <: MERGE.

  Definition Pcmp := Pgt.

  Program Fixpoint merge (l1 l2: list positive) 
    {measure ((fun l1 l2 => (length l1 + length l2)%nat) l1 l2)}
    : list positive :=
  match l1, l2 with
  | p1::l1', p2::l2' =>
      match (Pcompare p1 p2 Eq) with
      | Eq => l1
      | Gt => merge l1' l2 
      | Lt => merge l1 l2'
      end
  | _, _ => nil
  end.
  Next Obligation.
    simpl. omega.
  Qed.
  
  Definition merge_is_tail_of_left_prop (n:nat) := forall Xsdms Ysdms
    (Hlen: (length Xsdms + length Ysdms = n)%nat),
    is_tail (merge Xsdms Ysdms) Xsdms.

  Ltac fold_merge :=
  match goal with
  | |- context [merge_func (existT _ ?arg1 ?arg2)] => 
         fold (merge arg1 arg2)
  end.

  Ltac unfold_merge :=
  match goal with
  | |- appcontext [merge ?arg] =>
     unfold merge; unfold merge_func;
     Program.Wf.WfExtensionality.unfold_sub merge arg; simpl;
     repeat Program.Wf.fold_sub merge_func;
     repeat fold_merge
  end.

  Lemma merge_is_tail_of_left_aux: forall n, merge_is_tail_of_left_prop n.
  Proof.
    induction n; unfold merge_is_tail_of_left_prop; intros.
      destruct Xsdms as [|Xsdms]; destruct Ysdms as [|Ysdms]; 
        simpl in Hlen; try solve [contradict Hlen; simpl; omega].
      compute. auto with coqlib.
  
      destruct Xsdms as [|Xsdms]; destruct Ysdms as [|Ysdms]; 
        simpl in Hlen; try solve [contradict Hlen; simpl; omega].
      
        uniq_result.
        compute. auto with coqlib.
  
        uniq_result.
        compute. apply is_tail_nil.
  
        uniq_result.
        unfold_merge.
        remember ((Xsdms ?= Ysdms)%positive Eq) as Cmp.
        destruct Cmp; auto with coqlib.
          apply IHn. simpl. omega.
  Qed.

  Lemma merge_is_tail_of_left: forall Xsdms Ysdms, 
    is_tail (merge Xsdms Ysdms) Xsdms.
  Proof.
    intros.
    assert (J:=@merge_is_tail_of_left_aux (length Xsdms + length Ysdms)).
    unfold merge_is_tail_of_left_prop in J.
    auto.
  Qed.
  
  Lemma merge_cmp_cons: forall p ps (Hlt: Forall (Pgt p) ps),
    ps = merge ps (p :: ps).
  Proof.
    destruct 1; intros.
      compute. auto.

      unfold_merge.
      rewrite ZC1; auto.
      unfold_merge.
      rewrite Pcompare_refl. auto.
  Qed.

End MergeGt.
*)

Module Type LATTICEELT.

  Variable t: Type.
  Variable eq: t -> t -> Prop.
  Hypothesis eq_refl: forall x, eq x x.
  Hypothesis eq_sym: forall x y, eq x y -> eq y x.
  Hypothesis eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
(*
  Variable beq: t -> t -> bool.
  Hypothesis beq_correct: forall x y, beq x y = true -> eq x y.
*)
  Variable bot: t.
  Variable lub: t -> t -> t * bool.
  Variable top: t.
  Variable ge: t -> t -> Prop.
  Hypothesis ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Hypothesis ge_refl: forall x, ge x x.

End LATTICEELT.

Module LATTICEELT_MAP (L: LATTICEELT).

Definition in_incr (in1 in2: PMap.t L.t) : Prop :=
  forall n, L.ge in2??n in1??n.

Lemma in_incr_refl:
  forall in1, in_incr in1 in1.
Proof.
  unfold in_incr; intros. apply L.ge_refl. 
Qed.

Lemma in_incr_trans:
  forall in1 in2 in3, in_incr in1 in2 -> in_incr in2 in3 -> in_incr in1 in3.
Proof.
  unfold in_incr; intros. apply L.ge_trans with in2??n; auto.
Qed.

End LATTICEELT_MAP.

Ltac Peqb_eq_tac :=
repeat match goal with
| H: Peqb _ _ = true |- _ => eapply Peqb_eq in H; subst
| |- Peqb _ _ = true => eapply Peqb_eq
end.
 
Theorem sublist_trans : forall X (l1 l2 l3: list X), 
  sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.
Admitted.

Module Doms (MG:MERGE) <: LATTICEELT.

  Definition t := option (list positive).

(*  
  Definition beq_hd (l1 l2: list positive) : bool :=
  match l1, l2 with
  | h1::_, h2::_ => Peqb h1 h2
  | nil, nil => true
  | _, _ => false
  end.
  
  Definition beq (x y:t) : bool := 
  match x, y with
  | Some x', Some y' => beq_hd x' y'
  | None, None => true
  | _, _ => false
  end.
*)  

  Definition eq (x y: t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@refl_equal t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@sym_equal t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@trans_equal t).

(* 
  Lemma beq_correct: forall x y (Heq: beq x y = true), eq x y.
  Proof. auto. Qed.
*)
  
  Definition bot : t := None.
  
  Definition lub (x y:t) : t * bool :=
  match x, y with
  | Some x', Some y' => 
     let '(r, changed) := (MG.merge x' y') in (Some r, changed)
  | _, None => (x, false)
  | None, _ => (y, true)
  end.
  
  Definition top : t := Some nil.
  
  Definition ge (x y:t) : Prop :=
  match x, y with
  | _, None => True
  | Some x', Some y' => sublist x' y'
  | _, _ => False
  end.

  Lemma ge_trans: forall x y z (Hxy: ge x y) (Hyz: ge y z), ge x z.
  Proof.
    unfold ge.
    destruct x as [x|]; destruct y as [y|]; destruct z as [z|]; 
      eauto using sublist_trans.
      tauto.
  Qed.

  Lemma ge_refl: forall x, ge x x.
  Proof.
    unfold ge.
    destruct x as [x|]; auto using sublist_refl.
  Qed.
(*
  Lemma merge_is_tail_of_left: forall Xsdms Ysdms, 
    is_tail (MG.merge Xsdms Ysdms) Xsdms.
  Proof. apply MG.merge_is_tail_of_left. Qed.
  
  Lemma merge_cmp_cons: forall p ps (Hlt: Forall (MG.Pcmp p) ps),
    ps = MG.merge ps (p :: ps).
  Proof. apply MG.merge_cmp_cons. Qed.
*)
  Definition transfer (n:positive) (input:t) : t :=
  match input with
  | None => None
  | Some ps => Some (n::ps)
  end.
(*
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    intros.
    caseEq y.
      intros Ysdms Hgety.
      caseEq x; simpl; auto.
        intros Xsdms Hgetx.
        simpl. apply merge_is_tail_of_left.
  
      intros Hgety.
      caseEq x; simpl; auto with coqlib.
  Qed.

  Lemma lub_bot_inv: forall x y (Hlub: lub x y = bot),
    x = bot /\ y = bot.
  Proof.
    intros.
    destruct x; destruct y; inv Hlub; auto.
  Qed.
  
  Lemma lub_nonbot_spec: forall x y (Hnonbot: x <> bot \/ y <> bot),
    lub x y <> bot.
  Proof.
    intros.
    destruct x; destruct y; try tauto.
      simpl. unfold bot. congruence.
  Qed.
  
  Lemma Leq_nonbot_inv_r: forall x y (Hnonbot: y <> bot) (Heq: eq x y),
    x <> None.
  Proof.
    unfold eq, beq.
    destruct y; try tauto.
    destruct x; intros; congruence.
  Qed.

  Lemma Leq_nonbot_inv_l: forall x y (Hnonbot: x <> bot) (Heq: eq x y),
    y <> None.
  Proof.
    unfold eq, beq.
    destruct x; try tauto.
    destruct y; intros; congruence.
  Qed.

  Lemma transfer_nonbot: forall p dms (Hnonbot: dms <> bot),
    transfer p dms <> bot.
  Proof.
    unfold transfer, bot.
    intros.
    destruct dms; congruence.
  Qed.

  Lemma ge_Forall: forall P ox y (Hlt : Forall P y)
    (Hge: ge ox (Some y)),
    match ox with
    | Some x => Forall P x
    | _ => True
    end.
  Proof.
    intros.
    destruct ox as [x|]; tinv Hge.
    simpl in Hge.
    eapply is_tail_Forall; eauto.
  Qed.
*)
End Doms.

Require Import syntax.
Import LLVMsyntax.

Fixpoint asucc_psucc_aux (mapping: ATree.t positive)  
                         (pred: PTree.t (list positive))
                         (pfrom: positive) (tolist: list l)
                         {struct tolist} : (PTree.t (list positive)) :=
  match tolist with
  | nil => pred
  | to :: rem =>
    match ATree.get to mapping with
    | Some pto => 
        asucc_psucc_aux mapping 
          (PTree.set pfrom (pto :: pred ??? pfrom) pred) pfrom rem
    | _ => pred
    end
  end.

Definition asucc_psucc (mapping: ATree.t positive)  
                       (pred: PTree.t (list positive))
                       (from: l) (tolist: list l)
                       : PTree.t (list positive) :=
  match ATree.get from mapping with
  | Some pfrom => asucc_psucc_aux mapping pred pfrom tolist
  | _ => pred
  end.

Definition asuccs_psuccs (mapping: ATree.t positive) (succs: ATree.t ls)  
  : PTree.t (list positive) :=
  ATree.fold (asucc_psucc mapping) succs (PTree.empty (list positive)).

Fixpoint psucc_asucc_aux (mapping: PTree.t l)  
                         (pred: ATree.t (list l))
                         (afrom: l) (tolist: list positive)
                         {struct tolist} : (ATree.t (list l)) :=
  match tolist with
  | nil => pred
  | to :: rem =>
    match PTree.get to mapping with
    | Some ato => 
        psucc_asucc_aux mapping 
          (ATree.set afrom (ato :: pred !!! afrom) pred) 
            afrom rem
    | _ => pred
    end
  end.

Definition psucc_asucc (mapping: PTree.t l)  
                       (pred: ATree.t (list l))
                       (from: positive) (tolist: list positive)
                       : ATree.t (list l) :=
  match PTree.get from mapping with
  | Some afrom => psucc_asucc_aux mapping pred afrom tolist
  | _ => pred
  end.

Definition psuccs_asuccs (mapping: PTree.t l) (succs: PTree.t (list positive))  
  : ATree.t (list l) :=
  PTree.fold (psucc_asucc mapping) succs (ATree.empty (list l)).

