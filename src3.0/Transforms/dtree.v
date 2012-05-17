Require Import vellvm.
Require Import Lattice.
Require Import Maps.
Require Import ListSet.

(*
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

Definition get_dtree_root (dt:DTree) : l :=
match dt with
| DT_node l0 _ => l0
end.

(* l1 >> l2, l1 strict dominates l2 *)
Definition gt_sdom (res: l -> set l) (l1 l2:l) : bool :=
match res l2 with
| dts2 => in_dec l_dec l1 dts2
end.

Fixpoint find_min (res: l -> set l) (acc:l) (dts: set l): l :=
match dts with
| nil => acc
| l0::dts' =>
    if (gt_sdom res acc l0) then
      find_min res l0 dts'
    else
      find_min res acc dts'
end.

Fixpoint insert_sort_sdom_iter (res: l -> set l) (l0:l)
  (prefix suffix:list l) : list l :=
match suffix with
| nil => List.rev (l0 :: prefix)
| l1::suffix' =>
    if gt_sdom res l0 l1 then (List.rev (l0 :: prefix)) ++ suffix
    else insert_sort_sdom_iter res l0 (l1::prefix) suffix'
end.

Fixpoint insert_sort_sdom (res: l -> set l) (data:list l) (acc:list l): list l :=
match data with
| nil => acc
| l1 :: data' =>
    insert_sort_sdom res data' (insert_sort_sdom_iter res l1 nil acc)
end.

Definition sort_sdom (res: l -> set l) (data:list l): list l :=
insert_sort_sdom res data nil.

Definition gt_dom_prop (res: l -> set l) (l1 l2:l) : Prop :=
gt_sdom res l1 l2 = true \/ l1 = l2.

Definition gt_sdom_prop (res: l -> set l) (l1 l2:l) : Prop :=
gt_sdom res l1 l2 = true.

Fixpoint remove_redundant (input: list l) : list l :=
match input with
| a :: ((b :: _) as input') =>
    if (l_dec a b) then remove_redundant input'
    else a :: remove_redundant input'
| _ => input
end.

Fixpoint compute_sdom_chains_aux (res: l -> set l)
  (bd: list l) (acc: list (l * list l)) : list (l * list l) :=
match bd with
| nil => acc
| l0 :: bd' =>
    match res l0 with
    | dts0 =>
        compute_sdom_chains_aux res bd'
          ((l0, remove_redundant (sort_sdom res (l0 :: dts0)))::acc)
    end
end.

Definition compute_sdom_chains (res: l -> set l) rd
  : list (l * list l) :=
compute_sdom_chains_aux res rd nil.

Fixpoint find_idom_aux (res: l -> set l) (acc:l) (dts: set l)
  : option l :=
match dts with
| nil => Some acc
| l0::dts' =>
    match res l0, res acc with
    | dts1, dts2 =>
        if (in_dec l_dec l0 dts2)
        then (* acc << l0 *)
          find_idom_aux res acc dts'
        else
          if (in_dec l_dec acc dts1)
          then (* l0 << acc *)
            find_idom_aux res l0 dts'
          else (* l0 and acc are incompariable *)
            None
    end
end.

(* We should prove that this function is not partial. *)
Definition find_idom (res: l -> set l) (l0:l) : option l :=
match res l0 with
| l1::dts0 => find_idom_aux res l1 dts0
| _ => None
end.

Fixpoint compute_idoms (res: l -> set l) (rd: list l)
  (acc: list (l * l)) : list (l * l) :=
match rd with
| nil => acc
| l0 :: rd' =>
    match find_idom res l0 with
    | None => compute_idoms res rd' acc
    | Some l1 => compute_idoms res rd' ((l1,l0)::acc)
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
    let dt := AlgDom.dom_query f in
    let chains := compute_sdom_chains dt rd in
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
   let res := (AlgDom.dom_query f) in
   entry `in` dtree_dom dt /\
   Sorted (gt_sdom_prop res) chain /\ NoDup chain
| _ => True
end.

