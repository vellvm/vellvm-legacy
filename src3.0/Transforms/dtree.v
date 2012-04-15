Require Import vellvm.
Require Import Lattice.
Require Import Maps.
Require Import ListSet.

Section MoreMove.

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

Program Fixpoint reachablity_analysis_aux (nvisited: list l) (succs : ATree.t ls)
  (curr: l) (acc: list l) {measure (List.length nvisited)%nat}
  : option (list l) :=
match (ATree.get curr succs) with
| None => None
| Some nexts =>
    fold_left
      (fun oacc' next =>
       match oacc' with
       | None => None
       | Some acc' =>
         if (in_dec eq_atom_dec next nvisited) then
           if (in_dec eq_atom_dec next acc) then
             Some acc'
           else
             match reachablity_analysis_aux (List.remove eq_atom_dec next nvisited)
                     succs next (next::acc) with
             | None => None
             | Some acc'' => Some (ListSet.set_union eq_atom_dec acc' acc'')
             end
         else
           Some acc'
       end)
      nexts (Some acc)
end.
Next Obligation.
  apply remove_in_length; auto.
Qed.

(*
Definition reachablity_analysis (f : fdef) : option (list l) :=
match getEntryBlock f with
| Some (block_intro root _ _ _) =>
    let 'succs := successors f in
    reachablity_analysis_aux
      (List.remove eq_atom_dec root (bound_fdef f)) succs root [root]
| None => None
end.
*)

Inductive DTree : Set :=
| DT_node : l -> DTrees -> DTree
with DTrees : Set :=
| DT_nil : DTrees
| DT_cons : DTree -> DTrees -> DTrees
.

Fixpoint dtree_dom (dt: DTree) : atoms :=
match dt with
| DT_node l0 dts0 => {{l0}} `union` dtrees_dom dts0
end
with dtrees_dom (dts: DTrees) : atoms :=
match dts with
| DT_nil => empty
| DT_cons dt0 dts0 => dtree_dom dt0 `union` dtrees_dom dts0
end.

Definition imm_domination (f:fdef) (l1 l2:l) : Prop :=
strict_domination f l1 l2 /\
forall l0, strict_domination f l0 l2 -> domination f l0 l1.

Definition get_dtree_root (dt:DTree) : l :=
match dt with
| DT_node l0 _ => l0
end.

(* l1 >> l2, l1 strict dominates l2 *)
Definition gt_sdom bd (res: AMap.t (Dominators.t bd)) (l1 l2:l) : bool :=
match AMap.get l2 res with
| Dominators.mkBoundedSet dts2 _ => in_dec l_dec l1 dts2
end.

Fixpoint find_min bd (res: AMap.t (Dominators.t bd)) (acc:l) (dts: set l): l :=
match dts with
| nil => acc
| l0::dts' =>
    if (gt_sdom bd res acc l0) then
      find_min bd res l0 dts'
    else
      find_min bd res acc dts'
end.

Fixpoint insert_sort_sdom_iter bd (res: AMap.t (Dominators.t bd)) (l0:l)
  (prefix suffix:list l) : list l :=
match suffix with
| nil => List.rev (l0 :: prefix)
| l1::suffix' =>
    if gt_sdom bd res l0 l1 then (List.rev (l0 :: prefix)) ++ suffix
    else insert_sort_sdom_iter bd res l0 (l1::prefix) suffix'
end.

Fixpoint insert_sort_sdom bd (res: AMap.t (Dominators.t bd)) (data:list l)
  (acc:list l) : list l :=
match data with
| nil => acc
| l1 :: data' =>
    insert_sort_sdom bd res data' (insert_sort_sdom_iter bd res l1 nil acc)
end.

Definition sort_sdom bd (res: AMap.t (Dominators.t bd)) (data:list l): list l :=
insert_sort_sdom bd res data nil.

Definition gt_dom_prop bd (res: AMap.t (Dominators.t bd)) (l1 l2:l) : Prop :=
gt_sdom bd res l1 l2 = true \/ l1 = l2.

Definition gt_sdom_prop bd (res: AMap.t (Dominators.t bd)) (l1 l2:l) : Prop :=
gt_sdom bd res l1 l2 = true.

Fixpoint remove_redundant (input: list l) : list l :=
match input with
| a :: ((b :: _) as input') =>
    if (l_dec a b) then remove_redundant input'
    else a :: remove_redundant input'
| _ => input
end.

Fixpoint compute_sdom_chains_aux bd0 (res: AMap.t (Dominators.t bd0))
  (bd: list l) (acc: list (l * list l)) : list (l * list l) :=
match bd with
| nil => acc
| l0 :: bd' =>
    match AMap.get l0 res with
    | Dominators.mkBoundedSet dts0 _ =>
        compute_sdom_chains_aux bd0 res bd'
          ((l0, remove_redundant (sort_sdom bd0 res (l0 :: dts0)))::acc)
    end
end.

Definition compute_sdom_chains bd (res: AMap.t (Dominators.t bd)) rd
  : list (l * list l) :=
compute_sdom_chains_aux bd res rd nil.

Fixpoint find_idom_aux bd (res: AMap.t (Dominators.t bd)) (acc:l) (dts: set l)
  : option l :=
match dts with
| nil => Some acc
| l0::dts' =>
    match AMap.get l0 res, AMap.get acc res with
    | Dominators.mkBoundedSet dts1 _ , Dominators.mkBoundedSet dts2 _ =>
        if (in_dec l_dec l0 dts2)
        then (* acc << l0 *)
          find_idom_aux bd res acc dts'
        else
          if (in_dec l_dec acc dts1)
          then (* l0 << acc *)
            find_idom_aux bd res l0 dts'
          else (* l0 and acc are incompariable *)
            None
    end
end.

(* We should prove that this function is not partial. *)
Definition find_idom bd (res: AMap.t (Dominators.t bd)) (l0:l) : option l :=
match AMap.get l0 res with
| Dominators.mkBoundedSet (l1::dts0) _ => find_idom_aux bd res l1 dts0
| _ => None
end.

Fixpoint compute_idoms bd (res: AMap.t (Dominators.t bd)) (rd: list l)
  (acc: list (l * l)) : list (l * l) :=
match rd with
| nil => acc
| l0 :: rd' =>
    match find_idom bd res l0 with
    | None => compute_idoms bd res rd' acc
    | Some l1 => compute_idoms bd res rd' ((l1,l0)::acc)
    end
end.

Fixpoint in_children_roots child dts : bool :=
match dts with
| DT_nil => false
| DT_cons (DT_node l0 _) dts' =>
    if (l_dec l0 child) then true else in_children_roots child dts'
end.

Fixpoint dtree_insert dt parent child : DTree :=
match dt with
| DT_node l0 dts0 =>
    if (id_dec parent l0) then
      if in_children_roots child dts0 then dt
      else DT_node l0 (DT_cons (DT_node child DT_nil) dts0)
    else DT_node l0 (dtrees_insert dts0 parent child)
end
with dtrees_insert (dts: DTrees) parent child : DTrees :=
match dts with
| DT_nil => DT_nil
| DT_cons dt0 dts0 =>
    DT_cons (dtree_insert dt0 parent child) (dtrees_insert dts0 parent child)
end.

Fixpoint is_dtree_edge dt parent child : bool :=
match dt with
| DT_node l0 dts0 =>
    if (id_dec parent l0) then
      if in_children_roots child dts0 then true
      else is_dtrees_edge dts0 parent child
    else is_dtrees_edge dts0 parent child
end
with is_dtrees_edge (dts: DTrees) parent child : bool :=
match dts with
| DT_nil => false
| DT_cons dt0 dts0 =>
    is_dtree_edge dt0 parent child || is_dtrees_edge dts0 parent child
end.

Scheme dtree_rec2 := Induction for DTree Sort Set
  with dtrees_rec2 := Induction for DTrees Sort Set.

Definition dtree_mutrec P P' :=
  fun h1 h2 h3 =>
    (pair (@dtree_rec2 P P' h1 h2 h3) (@dtrees_rec2 P P' h1 h2 h3)).

Fixpoint create_dtree_from_chain dt chain : DTree :=
match chain with
| p::((ch::_) as chain') =>
    create_dtree_from_chain (dtree_insert dt p ch) chain'
| _ => dt
end.

Definition create_dtree (f: fdef) : option DTree :=
match getEntryLabel f, reachablity_analysis f with
| Some root, Some rd =>
    let dt := dom_analyze f in
    let b := bound_fdef f in
    let chains := compute_sdom_chains b dt rd in
    Some (fold_left
      (fun acc elt => let '(_, chain):=elt in create_dtree_from_chain acc chain)
      chains (DT_node root DT_nil))
| _, _ => None
end.

Fixpoint size_of_dtrees (dts:DTrees) : nat :=
match dts with
| DT_nil => O
| DT_cons _ dts' => S (size_of_dtrees dts')
end.

Fixpoint is_chain_edge (chain:list l) p0 ch0 : Prop :=
match chain with
| p::((ch::_) as chain') => (p = p0 /\ ch = ch0) \/ is_chain_edge chain' p0 ch0
| _ => False
end.

Definition chain_connects_dtree dt (chain:list l) : Prop :=
match chain with
| entry :: _ :: _ => entry `in` dtree_dom dt
| _ => False
end.

Definition wf_chain f dt (chain:list l) : Prop :=
match chain with
| entry :: _ :: _ =>
   let b := bound_fdef f in
   let res := (dom_analyze f) in
   entry `in` dtree_dom dt /\
   Sorted (gt_sdom_prop b res) chain /\ NoDup chain
| _ => True
end.

