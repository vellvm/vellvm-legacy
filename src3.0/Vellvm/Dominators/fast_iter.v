Require Export Coqlib.
Require Export Iteration.
Require Export Maps.
Require Import syntax.
Require Import infrastructure_props.
Require Import Metatheory.

Import LLVMsyntax.

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
  apply J1 in J. tauto.
Qed.

Require Import Program.Tactics.

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

End More_Tree_Properties.

Record Frame := mkFrame {
  Fr_name: l;
  Fr_scs: ls
}.

Fixpoint find_next_visit_in_scs (visited: ATree.t unit) (scs: ls) 
  : option (l * ls) :=
match scs with
| nil => None
| sc::scs' => 
    match ATree.get sc visited with
    | None => Some (sc, scs')
    | _ => find_next_visit_in_scs visited scs'
    end
end.

Record PostOrder := mkPO {
  PO_cnt: positive;
  PO_a2p: ATree.t positive
}.

Definition postorder_inc (po:PostOrder) (v:l) : PostOrder :=
let '(mkPO cnt a2p) := po in
mkPO (Psucc cnt) (ATree.set v cnt a2p).

Module XATree := More_Tree_Properties(ATree).

Notation "a !!! b" := (XATree.successors_list a b) (at level 1).

Fixpoint find_next_visit_in_stk (succs: ATree.t ls)
  (visited: ATree.t unit) (po:PostOrder) (frs: list Frame) 
  : l * list Frame * PostOrder + PostOrder :=
match frs with
| nil => inr po
| mkFrame v scs::frs' => 
    match find_next_visit_in_scs visited scs with
    | Some (sc, scs') => 
        inl (sc, mkFrame sc (succs!!!sc)::mkFrame v scs'::frs', po)
    | None => find_next_visit_in_stk succs visited (postorder_inc po v) frs'
    end
end.

Ltac inv_mbind_app :=
  match goal with
  | H: _ = match ?e with
       | Some _ => _
       | None => _
       end |- _ => remember e as R; destruct R
  | H: match ?e with
       | Some _ => _
       | None => _
       end = _ |- _ => remember e as R; destruct R
  end.

Lemma find_next_visit_in_scs_spec: forall visited scs sc scs'
  (Hfind : Some (sc, scs') = find_next_visit_in_scs visited scs),
  incl (sc::scs') scs /\ ATree.get sc visited = None.
Proof.
  induction scs as [|sc scs]; simpl; intros.
    congruence.

    inv_mbind_app.
      apply IHscs in Hfind.
      destruct_pairs.
      split; eauto with datatypes v62.
    
      uniq_result.
      split; eauto with datatypes v62.
Qed.

Lemma length_le__length_lt: forall A 
  (eq_dec : forall x y : A, {x = y}+{x <> y})
  (a:A) (l2:list A) (l1:list A) 
  (Huniq: list_norepet l1) (Hinc: incl l1 l2)  
  (Hnotin: ~ In a l1) (Hin: In a l2), 
  (length l1 < length l2)%nat.
Proof.
  intros.
  assert (incl l1 (List.remove eq_dec a l2)) as Hinc'.
    apply remove_notin_incl; eauto with datatypes v62.
  apply incl__length_le in Hinc'; auto.
  assert (length (List.remove eq_dec a l2) < length l2)%nat as Hle.
    apply remove_in_length; auto with datatypes v62.
  omega.
Qed.

Lemma find_next_visit_in_stk_spec1: forall succs visited (stk : list Frame)
  (Hp : Forall (fun fr : Frame => 
                incl (Fr_scs fr) (XATree.children_of_tree succs)) stk)  
  po (next : l) (stk' : list Frame) po'
  (Hfind : inl (next, stk', po') = find_next_visit_in_stk succs visited po stk),
  Forall 
    (fun fr : Frame => incl (Fr_scs fr) (XATree.children_of_tree succs)) 
    stk'.
Proof.
  induction 1 as [|[v scs]]; simpl; intros.
    congruence.
        
    inv_mbind_app; eauto 2.
      destruct_let.
      uniq_result.
      apply find_next_visit_in_scs_spec in HeqR.
      destruct_pairs.
      constructor.
        simpl. apply XATree.children_in_children_of_tree.
        constructor; auto.
          simpl in *.
          eauto with datatypes v62.
Qed.

Lemma find_next_visit_in_stk_spec3_helper: forall 
  (succs : ATree.t (list MetatheoryAtom.AtomImpl.atom))
  (visited : ATree.t unit)
  (Hinc : incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  (v : l) (scs : ls)
  (H : incl (Fr_scs {| Fr_name := v; Fr_scs := scs |})
        (XATree.children_of_tree succs))
  (l0 : l) (l1 : ls) (H0 : incl (l0 :: l1) scs)
  (H1 : visited ! l0 = None),
  (length (XATree.parents_of_tree visited) < 
     length (XATree.children_of_tree succs))%nat.
Proof.
  intros.
  assert (In l0 (XATree.children_of_tree succs)) as Hin.
    apply H. simpl. apply H0. xsolve_in_list.
  eapply length_le__length_lt; eauto.
    apply ATree.elements_keys_norepet; auto.
    apply XATree.notin_tree__notin_parents_of_tree; auto.
Qed.

Lemma find_next_visit_in_stk_spec3: forall succs visited 
  (Hinc: incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  (stk : list Frame) 
  (Hp : Forall (fun fr : Frame => 
                incl (Fr_scs fr) (XATree.children_of_tree succs)) stk)
  (next : l) (stk' : list Frame) po po'
  (Hfind : inl (next, stk', po') =
                   find_next_visit_in_stk succs visited po stk),
  (length (XATree.children_of_tree succs) -
    length (XATree.parents_of_tree (ATree.set next tt visited)) <
   length (XATree.children_of_tree succs) - 
    length (XATree.parents_of_tree visited))%nat.
Proof.
  induction 2 as [|[v scs]]; simpl; intros.
    congruence.

    inv_mbind_app; eauto 2.
      destruct_let.
      uniq_result.
      apply find_next_visit_in_scs_spec in HeqR.
      destruct_pairs.
      assert (length (XATree.parents_of_tree (ATree.set l1 tt visited)) =
                length (XATree.parents_of_tree visited) + 1)%nat as Heq.
        apply XATree.parents_of_tree_succ_len; auto.
      assert (length (XATree.parents_of_tree visited) <
                length (XATree.children_of_tree succs))%nat as Hlt.
        eapply find_next_visit_in_stk_spec3_helper; eauto.
      omega.
Qed.

Lemma find_next_visit_in_stk_spec2: forall (succs : ATree.t ls) 
  (visited : ATree.t unit)
  (Hinc : incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  (stk : list Frame)
  (Hp : Forall (fun fr : Frame => 
                incl (Fr_scs fr) (XATree.children_of_tree succs)) stk)
  (next : l) (stk' : list Frame) po po'
  (Hfind : inl (next, stk', po') = find_next_visit_in_stk succs visited po stk),
  incl (XATree.parents_of_tree (ATree.set next tt visited))
    (XATree.children_of_tree succs).
Proof.
  induction 2 as [|[v scs] ? IH]; simpl; intros.
    congruence.

    inv_mbind_app; eauto 2.
      destruct_let.
      uniq_result.
      apply find_next_visit_in_scs_spec in HeqR.
      destruct_pairs.
      intros x Hin.
      apply XATree.parents_of_tree_spec in Hin.
      destruct Hin as [? Hin].
      apply ATree.elements_complete in Hin. 
      rewrite ATree.gsspec in Hin.
      destruct_if.
        eauto with datatypes v62.
           
        apply ATree.elements_correct in H2. 
        apply Hinc.
        apply List.in_map with (f:=fst) in H2; auto.
Qed.

Program Fixpoint dfs_aux (succs: ATree.t ls)
  (visited: ATree.t unit) (po:PostOrder) (stk: list Frame) 
  (Hp: List.Forall 
         (fun fr => incl (Fr_scs fr) (XATree.children_of_tree succs)) stk /\
       incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  {measure 
    ((fun succs acc => 
      (length (XATree.children_of_tree succs) - 
       length (XATree.parents_of_tree visited))%nat) succs visited) }
  : PostOrder :=
  match find_next_visit_in_stk succs visited po stk with
  | inr po' => po'
  | inl (next, stk', po') => dfs_aux succs (ATree.set next tt visited) po' stk' _
  end.
Next Obligation.
  split.
    eapply find_next_visit_in_stk_spec1; eauto.
    eapply find_next_visit_in_stk_spec2; eauto.
Qed.
Next Obligation.
  eapply find_next_visit_in_stk_spec3; eauto.
Qed.

Program Definition dfs (succs: ATree.t ls) (entry:l) (pinit:positive) : PostOrder :=
dfs_aux succs (ATree.empty unit) (mkPO pinit (ATree.empty positive)) 
  (mkFrame entry (succs!!!entry)::nil) _.
Next Obligation.
  split.  
    constructor; auto.
      apply XATree.children_in_children_of_tree.
    rewrite XATree.parents_of_empty_tree. 
    intros x Hin. tauto.
Qed.

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

Module PNodeSetForward <: PNODE_SET.
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
End PNodeSetForward.

Module Type LATTICEELT.

  Variable t: Type.
  Variable eq: t -> t -> Prop.
  Hypothesis eq_refl: forall x, eq x x.
  Hypothesis eq_sym: forall x y, eq x y -> eq y x.
  Hypothesis eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Variable beq: t -> t -> bool.
  Hypothesis beq_correct: forall x y, beq x y = true -> eq x y.
  Variable bot: t.
  Variable lub: t -> t -> t.
  Variable top: t.
  Variable ge: t -> t -> Prop.
  Hypothesis ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Hypothesis ge_refl: forall x, ge x x.

End LATTICEELT.

Module LDoms <: LATTICEELT.

  Definition t := option (list positive).
  
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
  
  Definition eq (x y: t) := beq x y = true.
  
  Hint Unfold eq beq.
  
  Ltac Peqb_eq_tac :=
  repeat match goal with
  | H: Peqb _ _ = true |- _ => eapply Peqb_eq in H; subst
  | |- Peqb _ _ = true => eapply Peqb_eq
  end.
  
  Lemma eq_refl: forall x, eq x x.
  Proof.
    destruct x as [[|x]|]; auto.
      autounfold. simpl. Peqb_eq_tac. auto.
  Qed.
  
  Lemma eq_sym: forall x y (Heq: eq x y), eq y x.
  Proof.
    destruct x as [[|x]|]; destruct y as [[|y]|]; intros; inv Heq; auto.
      autounfold. simpl. Peqb_eq_tac. auto.
  Qed.
  
  Lemma eq_trans: forall x y z (Heq1: eq x y) (Heq2: eq y z), eq x z.
  Proof.
    intros.
    destruct x as [[|x]|]; destruct y as [[|y]|]; inv Heq1; auto.
    destruct z as [[|z]|]; inv Heq2; auto.
      autounfold. simpl. Peqb_eq_tac. auto.
  Qed.
  
  Lemma beq_correct: forall x y (Heq: beq x y = true), eq x y.
  Proof. auto. Qed.
  
  Definition bot : t := None.
  
  Program Fixpoint merge (l1 l2: list positive) 
    {measure ((fun l1 l2 => (length l1 + length l2)%nat) l1 l2)}
    : list positive :=
  match l1, l2 with
  | p1::l1', p2::l2' =>
      match (Pcompare p1 p2 Eq) with
      | Eq => l1
      | Lt => merge l1' l2 
      | Gt => merge l1 l2'
      end
  | _, _ => nil
  end.
  Next Obligation.
    simpl. omega.
  Qed.
  
  Definition lub (x y:t) : t :=
  match x, y with
  | Some x', Some y' => Some (merge x' y')
  | _, None => x
  | None, _ => y
  end.
  
  Definition top : t := Some nil.
  
  Definition ge (x y:t) : Prop :=
  match x, y with
  | _, None => True
  | Some x', Some y' => is_tail x' y'
  | _, _ => False
  end.

  Lemma ge_trans: forall x y z (Hxy: ge x y) (Hyz: ge y z), ge x z.
  Proof.
    unfold ge.
    destruct x as [x|]; destruct y as [y|]; destruct z as [z|]; 
      eauto using is_tail_trans.
      tauto.
  Qed.

  Lemma ge_refl: forall x, ge x x.
  Proof.
    unfold ge.
    destruct x as [x|]; auto using is_tail_refl.
  Qed.

End LDoms.

Module Weak_Dataflow_Solver (NS: PNODE_SET) (L: LATTICEELT).

Section Kildall.

Variable successors: PTree.t (list positive).
Variable transf : positive -> L.t -> L.t.
Variable entrypoints: list (positive * L.t).

(** The state of the iteration has two components:
- A mapping from program points to values of type [L.t] representing
  the candidate solution found so far.
- A worklist of program points that remain to be considered.
*)

Record state : Type :=
  mkstate { st_in: PMap.t L.t; st_wrk: NS.t }.

(** Kildall's algorithm, in pseudo-code, is as follows:
<<
    while st_wrk is not empty, do
        extract a node n from st_wrk
        compute out = transf n st_in[n]
        for each successor s of n:
            compute in = lub st_in[s] out
            if in <> st_in[s]:
                st_in[s] := in
                st_wrk := st_wrk union {s}
            end if
        end for
    end while
    return st_in
>>

The initial state is built as follows:
- The initial mapping sets all program points to [L.bot], except
  those mentioned in the [entrypoints] list, for which we take
  the associated approximation as initial value.  Since a program
  point can be mentioned several times in [entrypoints], with different
  approximations, we actually take the l.u.b. of these approximations.
- The initial worklist contains all the program points. *)

Fixpoint start_state_in (ep: list (positive * L.t)) : PMap.t L.t :=
  match ep with
  | nil =>
      PMap.init L.bot
  | (n, v) :: rem =>
      let m := start_state_in rem in PMap.set n (L.lub m ?? n v) m
  end.

Definition start_state :=
  mkstate (start_state_in entrypoints) (NS.initial successors).

(** [propagate_succ] corresponds, in the pseudocode,
  to the body of the [for] loop iterating over all successors. *)

Definition propagate_succ (s: state) (out: L.t) (n: positive) :=
  let oldl := s.(st_in) ?? n in
  let newl := L.lub oldl out in
  if L.beq oldl newl
  then s
  else mkstate (PMap.set n newl s.(st_in)) (NS.add n s.(st_wrk)).

(** [propagate_succ_list] corresponds, in the pseudocode,
  to the [for] loop iterating over all successors. *)

Fixpoint propagate_succ_list (s: state) (out: L.t) (succs: list positive)
                             {struct succs} : state :=
  match succs with
  | nil => s
  | n :: rem => propagate_succ_list (propagate_succ s out n) out rem
  end.

(** [step] corresponds to the body of the outer [while] loop in the
  pseudocode. *)

Definition step (s: state) : PMap.t L.t + state :=
  match NS.pick s.(st_wrk) with
  | None =>
      inl _ s.(st_in)
  | Some(n, rem) =>
      inr _ (propagate_succ_list
              (mkstate s.(st_in) rem)
              (transf n s.(st_in) ?? n)
              (successors ??? n))
  end.

(** The whole fixpoint computation is the iteration of [step] from
  the start state. *)

Definition fixpoint : option (PMap.t L.t) :=
  PrimIter.iterate _ _ step start_state.

End Kildall.

End Weak_Dataflow_Solver.

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

Module DomDS := Weak_Dataflow_Solver (PNodeSetForward) (LDoms).

Definition transfer (n:positive) (input: LDoms.t) : LDoms.t :=
match input with
| None => None
| Some ps => Some (n::ps)
end.

Require analysis.
Require Import infrastructure.

Definition dom_analyze (f: fdef) : PMap.t LDoms.t :=
  let asuccs := analysis.successors f in
  match LLVMinfra.getEntryBlock f with
  | Some (block_intro le _ _ _) =>
      let 'mkPO _ a2p := dfs asuccs le 1%positive in
      let psuccs := asuccs_psuccs a2p asuccs in
      match ATree.get le a2p with
      | Some pe => 
        match DomDS.fixpoint psuccs transfer ((pe, LDoms.top) :: nil) with
        | None => (PMap.set pe LDoms.top (PMap.init LDoms.bot))
        | Some res => res
        end
      | None => PMap.init LDoms.bot
      end
  | None => PMap.init LDoms.bot
  end.

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

Module DomMap := LATTICEELT_MAP (LDoms).

Section Mono.

(** ** Monotonicity properties *)

(** We first show that the [st_in] part of the state evolves monotonically:
  at each step, the values of the [st_in[n]] either remain the same or
  increase with respect to the [L.ge] ordering. *)

Variable successors: PTree.t (list positive).
Variable entrypoint: positive.

Definition merge_is_tail_of_left_prop (n:nat) := forall Xsdms Ysdms
  (Hlen: (length Xsdms + length Ysdms = n)%nat),
  is_tail (LDoms.merge Xsdms Ysdms) Xsdms.

Require Import Program.Wf.

Ltac fold_merge :=
match goal with
| |- context [LDoms.merge_func (existT _ ?arg1 ?arg2)] => 
       fold (LDoms.merge arg1 arg2)
end.

Ltac unfold_merge :=
match goal with
| |- appcontext [LDoms.merge ?arg] =>
   unfold LDoms.merge; unfold LDoms.merge_func;
   WfExtensionality.unfold_sub LDoms.merge arg; simpl;
   repeat fold_sub LDoms.merge_func;
   repeat fold_merge
end.

Lemma is_tail_nil: forall A (l1:list A), is_tail nil l1.
Proof.
  induction l1; constructor; auto.
Qed.

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
  is_tail (LDoms.merge Xsdms Ysdms) Xsdms.
Proof.
  intros.
  assert (J:=@merge_is_tail_of_left_aux (length Xsdms + length Ysdms)).
  unfold merge_is_tail_of_left_prop in J.
  auto.
Qed.

Lemma ge_lub_left: forall dmap x y, 
  LDoms.ge (LDoms.lub (dmap??x) (transfer y (dmap??y))) (dmap??x).
Proof.
  intros.
  unfold transfer.
  caseEq (dmap ?? y).
    intros Ysdms Hgety.
    caseEq (dmap ?? x); simpl; auto.
      intros Xsdms Hgetx.
      simpl. apply merge_is_tail_of_left.

    intros Hgety.
    caseEq (dmap ?? x); simpl; auto with coqlib.
Qed.

Lemma propagate_succ_incr:
  forall st p n,
  DomMap.in_incr 
    st.(DomDS.st_in) 
    (DomDS.propagate_succ st (transfer p (st.(DomDS.st_in)??p)) n).(DomDS.st_in).
Proof.
  unfold DomMap.in_incr, DomDS.propagate_succ; simpl; intros.
  remember 
    (LDoms.beq 
      st.(DomDS.st_in)??n 
      (LDoms.lub st.(DomDS.st_in)??n (transfer p (st.(DomDS.st_in)??p)))) as R.
  destruct R.
    apply LDoms.ge_refl. 

    simpl. 
    case (positive_eq_dec n n0); intro; subst.
      rewrite PMap.gss. apply ge_lub_left; auto.

      rewrite PMap.gso; auto. apply LDoms.ge_refl. 
Qed.

Lemma propagate_succ_self_stable: forall st n p,
  (DomDS.st_in st) ?? p = 
  (DomDS.st_in 
    (DomDS.propagate_succ st (transfer p (DomDS.st_in st) ?? p) n)) ?? p.
Proof.
  destruct st as [dmap rem]. simpl.
  intros.
  unfold DomDS.propagate_succ. simpl.
  destruct_if. simpl.
  case (positive_eq_dec n p); intro; subst.
    rewrite PMap.gss. admit.

    rewrite PMap.gso; auto. 
Qed.

Lemma propagate_succ_list_incr:
  forall p scs st,
  DomMap.in_incr 
    st.(DomDS.st_in) 
    (DomDS.propagate_succ_list 
      st (transfer p (st.(DomDS.st_in)??p)) scs).(DomDS.st_in).
Proof.
  induction scs as [|sc scs]; simpl; intros.
    apply DomMap.in_incr_refl.
  
    apply DomMap.in_incr_trans with 
      (DomDS.propagate_succ 
        st (transfer p (st.(DomDS.st_in)??p)) sc).(DomDS.st_in).
      apply propagate_succ_incr; auto.

      rewrite propagate_succ_self_stable at 3.
      apply IHscs; auto.
Qed.

Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Lemma fixpoint_incr:
  forall res
  (Hfix: DomDS.fixpoint successors transfer entrypoints = Some res),
  DomMap.in_incr (DomDS.start_state_in entrypoints) res.
Proof.
  unfold DomDS.fixpoint; intros.
  eapply (PrimIter.iterate_prop _ _ (DomDS.step successors transfer)
    (fun st => DomMap.in_incr (DomDS.start_state_in entrypoints) st.(DomDS.st_in))
    (fun res => DomMap.in_incr (DomDS.start_state_in entrypoints) res)); eauto.
    intros st INCR. unfold DomDS.step.
    destruct (PNodeSetForward.pick (DomDS.st_wrk st)) as [ [n rem] | ]; auto.
      apply DomMap.in_incr_trans with st.(DomDS.st_in); auto.
        change st.(DomDS.st_in) with 
          (DomDS.mkstate st.(DomDS.st_in) rem).(DomDS.st_in).
        apply propagate_succ_list_incr; auto.

    apply DomMap.in_incr_refl.
Qed.

Definition predecessors := XPTree.make_predecessors successors.

Definition in_cfg (n:positive) : Prop :=
  In n (XPTree.parents_of_tree successors) /\ 
  In n (XPTree.children_of_tree successors).

Definition wf_entrypoints: Prop := 
  predecessors ??? entrypoint = nil /\
  forall n (Hcfg: in_cfg n), (n <= entrypoint)%positive.

Definition wf_doms (dmap: PMap.t LDoms.t) : Prop :=
forall n dms (Hget: dmap ?? n = dms),
  match dms with
  | None => 
      forall n' (Hset: dmap ?? n <> None), (n < n')%positive
  | Some sdms =>
      if positive_eq_dec n entrypoint then
        sdms = nil
      else
        In entrypoint sdms /\
        List.Forall (Plt n) sdms
  end.
 
Lemma propagate_succ_wf_doms:
  forall st p n (Hwf: wf_doms st.(DomDS.st_in)),
  wf_doms
    (DomDS.propagate_succ st (transfer p (st.(DomDS.st_in)??p)) n).(DomDS.st_in).
Admitted.

Lemma propagate_succ_list_wf_doms: forall st (Hwf: wf_doms (DomDS.st_in st))
  rem p scs,
  wf_doms
    (DomDS.st_in
       (DomDS.propagate_succ_list 
          {| DomDS.st_in := DomDS.st_in st; DomDS.st_wrk := rem |}
          (transfer p (DomDS.st_in st) ?? p) scs)).
Admitted.

Lemma entrypoints_wf_doms:
  wf_doms (DomDS.start_state_in entrypoints).
Admitted.

End Mono.

(*
(** ** Correctness invariant *)

(** The following invariant is preserved at each iteration of Kildall's
  algorithm: for all program points [n], either
  [n] is in the worklist, or the inequations associated with [n]
  ([st_in[s] >= transf n st_in[n]] for all successors [s] of [n])
  hold.  In other terms, the worklist contains all nodes that do not
  yet satisfy their inequations. *)

Definition good_state (st: state) : Prop :=
  forall n,
  NS.In n st.(st_wrk) \/
  (forall s, In s (successors!!!n) ->
             L.ge st.(st_in)!!s (transf n st.(st_in)!!n)).

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma start_state_good:
  good_state start_state.
Proof.
  unfold good_state, start_state; intros.
  case_eq (successors!n); intros.
  left; simpl. eapply NS.initial_spec. eauto.
  unfold successors_list. rewrite H. right; intros. contradiction.
Qed.

Lemma propagate_succ_charact:
  forall st out n,
  let st' := propagate_succ st out n in
  L.ge st'.(st_in)!!n out /\
  (forall s, n <> s -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  unfold propagate_succ; intros; simpl.
  predSpec L.beq L.beq_correct
           ((st_in st) !! n) (L.lub (st_in st) !! n out).
  split.
  eapply L.ge_trans. apply L.ge_refl. apply H; auto.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl.
  apply L.ge_lub_left.
  auto.

  simpl. split.
  rewrite AMap.gss.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl.
  apply L.ge_lub_left.
  intros. rewrite AMap.gso; auto.
Qed.

Lemma propagate_succ_list_charact:
  forall out scs st,
  let st' := propagate_succ_list st out scs in
  forall s,
  (In s scs -> L.ge st'.(st_in)!!s out) /\
  (~(In s scs) -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  induction scs; simpl; intros.
  tauto.
  generalize (IHscs (propagate_succ st out a) s). intros [A B].
  generalize (propagate_succ_charact st out a). intros [C D].
  split; intros.
  elim H; intro.
  subst s.
  apply L.ge_trans with (propagate_succ st out a).(st_in)!!a.
  apply propagate_succ_list_incr. assumption.

  apply A. auto.
  transitivity (propagate_succ st out a).(st_in)!!s.
  apply B. tauto.
  apply D. tauto.
Qed.

Lemma propagate_succ_incr_worklist:
  forall st out n x,
  NS.In x st.(st_wrk) -> NS.In x (propagate_succ st out n).(st_wrk).
Proof.
  intros. unfold propagate_succ.
  case (L.beq (st_in st) !! n (L.lub (st_in st) !! n out)).
  auto.
  simpl. rewrite NS.add_spec. auto.
Qed.

Lemma propagate_succ_list_incr_worklist:
  forall out scs st x,
  NS.In x st.(st_wrk) -> NS.In x (propagate_succ_list st out scs).(st_wrk).
Proof.
  induction scs; simpl; intros.
  auto.
  apply IHscs. apply propagate_succ_incr_worklist. auto.
Qed.

Lemma propagate_succ_records_changes:
  forall st out n s,
  let st' := propagate_succ st out n in
  NS.In s st'.(st_wrk) \/ st'.(st_in)!!s = st.(st_in)!!s.
Proof.
  simpl. intros. unfold propagate_succ.
  case (L.beq (st_in st) !! n (L.lub (st_in st) !! n out)).
  right; auto.
  case (eq_atom_dec s n); intro.
  subst s. left. simpl. rewrite NS.add_spec. auto.
  right. simpl. apply AMap.gso. auto.
Qed.

Lemma propagate_succ_list_records_changes:
  forall out scs st s,
  let st' := propagate_succ_list st out scs in
  NS.In s st'.(st_wrk) \/ st'.(st_in)!!s = st.(st_in)!!s.
Proof.
  induction scs; simpl; intros.
  right; auto.
  elim (propagate_succ_records_changes st out a s); intro.
  left. apply propagate_succ_list_incr_worklist. auto.
  rewrite <- H. auto.
Qed.

Lemma step_state_good:
  forall st n rem,
  NS.pick st.(st_wrk) = Some(n, rem) ->
  good_state st ->
  good_state (propagate_succ_list (mkstate st.(st_in) rem)
                                  (transf n st.(st_in)!!n)
                                  (successors!!!n)).
Proof.
  unfold good_state. intros st n rem WKL GOOD x.
  generalize (NS.pick_some _ _ _ WKL); intro PICK.
  set (out := transf n st.(st_in)!!n).
  elim (propagate_succ_list_records_changes
          out (successors!!!n) (mkstate st.(st_in) rem) x).
  intro; left; auto.

  simpl; intros EQ. rewrite EQ.
  case (eq_atom_dec x n); intro.
  (* Case 1: x = n *)
  subst x.
  right; intros.
  elim (propagate_succ_list_charact out (successors!!!n)
          (mkstate st.(st_in) rem) s); intros.
  auto.
  (* Case 2: x <> n *)
  elim (GOOD x); intro.
  (* Case 2.1: x was already in worklist, still is *)
  left. apply propagate_succ_list_incr_worklist.
  simpl. rewrite PICK in H. elim H; intro. congruence. auto.
  (* Case 2.2: x was not in worklist *)
  right; intros.
  case (In_dec eq_atom_dec s (successors!!!n)); intro.
  (* Case 2.2.1: s is a successor of n, it may have increased *)
  apply L.ge_trans with st.(st_in)!!s.
  change st.(st_in)!!s with (mkstate st.(st_in) rem).(st_in)!!s.
  apply propagate_succ_list_incr.
  auto.
  (* Case 2.2.2: s is not a successor of n, it did not change *)
  elim (propagate_succ_list_charact out (successors!!!n)
          (mkstate st.(st_in) rem) s); intros.
  rewrite H2. simpl. auto. auto.
Qed.

(** ** Correctness of the solution returned by [iterate]. *)

(** As a consequence of the [good_state] invariant, the result of
  [fixpoint], if defined, is a solution of the dataflow inequations,
  since [st_wrk] is empty when the iteration terminates. *)

Theorem fixpoint_solution:
  forall res n s,
  fixpoint = Some res ->
  In s (successors!!!n) ->
  L.ge res!!s (transf n res!!n).
Proof.
  assert (forall res, fixpoint = Some res ->
          forall n s,
          In s successors!!!n ->
          L.ge res!!s (transf n res!!n)).
  unfold fixpoint. intros res PI. pattern res.
  eapply (PrimIter.iterate_prop _ _ step good_state).

  intros st GOOD. unfold step.
  caseEq (NS.pick st.(st_wrk)).
  intros [n rem] PICK. apply step_state_good; auto.
  intros.
  elim (GOOD n); intro.
  elim (NS.pick_none _ n H). auto.
  auto.

  eauto. apply start_state_good. eauto.
Qed.

(** As a consequence of the monotonicity property, the result of
  [fixpoint], if defined, is pointwise greater than or equal the
  initial mapping.  Therefore, it satisfies the additional constraints
  stated in [entrypoints]. *)

Lemma start_state_in_entry:
  forall ep n v,
  In (n, v) ep ->
  L.ge (start_state_in ep)!!n v.
Proof.
  induction ep; simpl; intros.
  elim H.
  elim H; intros.
  subst a. rewrite AMap.gss.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl.
  apply L.ge_lub_left.
  destruct a. rewrite AMap.gsspec. case (eq_atom_dec n a); intro.
  subst a. apply L.ge_trans with (start_state_in ep)!!n.
  apply L.ge_lub_left. auto.
  auto.
Qed.

Theorem fixpoint_entry:
  forall res n v,
  fixpoint = Some res ->
  In (n, v) entrypoints ->
  L.ge res!!n v.
Proof.
  intros.
  apply L.ge_trans with (start_state_in entrypoints)!!n.
  apply fixpoint_incr. auto.
  apply start_state_in_entry. auto.
Qed.

(** ** Preservation of a property over solutions *)

Variable P: L.t -> Prop.
Hypothesis P_bot: P L.bot.
Hypothesis P_lub: forall x y, P x -> P y -> P (L.lub x y).
Hypothesis P_transf: forall pc x, P x -> P (transf pc x).
Hypothesis P_entrypoints: forall n v, In (n, v) entrypoints -> P v.

Theorem fixpoint_invariant:
  forall res pc,
  fixpoint = Some res ->
  P res!!pc.
Proof.
  assert (forall ep,
          (forall n v, In (n, v) ep -> P v) ->
          forall pc, P (start_state_in ep)!!pc).
    induction ep; intros; simpl.
    rewrite AMap.gi. auto.
    simpl in H.
    assert (P (start_state_in ep)!!pc). apply IHep. eauto.
    destruct a as [n v]. rewrite AMap.gsspec. destruct (eq_atom_dec pc n).
    apply P_lub. subst. auto. eapply H. left; reflexivity. auto.
  set (inv := fun st => forall pc, P (st.(st_in)!!pc)).
  assert (forall st v n, inv st -> P v -> inv (propagate_succ st v n)).
    unfold inv, propagate_succ. intros.
    destruct (LAT.beq (st_in st)!!n (LAT.lub (st_in st)!!n v)).
    auto. simpl. rewrite AMap.gsspec. destruct (eq_atom_dec pc n).
    apply P_lub. subst n; auto. auto.
    auto.
  assert (forall l st v, inv st -> P v -> inv (propagate_succ_list st v l)).
    induction l; intros; simpl. auto.
    apply IHl; auto.
  assert (forall res, fixpoint = Some res -> forall pc, P res!!pc).
    unfold fixpoint. intros res0 RES0. pattern res0.
    eapply (PrimIter.iterate_prop _ _ step inv).
    intros. unfold step. destruct (NS.pick (st_wrk a)) as [[n rem] | ].
    apply H1. auto. apply P_transf. apply H2.
    assumption.
    eauto.
    unfold inv, start_state; simpl. auto.
  intros. auto.
Qed.
*)

