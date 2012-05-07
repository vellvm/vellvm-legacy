Require Export Coqlib.
Require Export Maps.
Require Import syntax.
Require Import infrastructure_props.
Require Import Metatheory.
Require Import Program.Tactics.
Require Import dom_libs.

Import LLVMsyntax.

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
