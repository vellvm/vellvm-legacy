Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
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

Fixpoint get_reachable_labels (bd:list l) (rd:AMap.t bool) (acc:list l) 
  : list l :=
match bd with
| nil => acc 
| l0::bd' => if (AMap.get l0 rd) 
             then get_reachable_labels bd' rd (l0::acc)
             else get_reachable_labels bd' rd acc
end.

Definition reachablity_analysis (f: fdef) : option (list l) :=
match getEntryBlock f with
| Some (block_intro root _ _ _) =>
    let 'bd := bound_fdef f in
    match areachable_aux f with
    | None => None
    | Some rd => Some (get_reachable_labels bd rd nil)
    end
| None => None
end.

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

Inductive WF_dtree (f:fdef) : DTree -> Prop :=
| WDT_node : forall (l0:l) (dts0:DTrees),
             reachable f l0 ->
             l0 `notin` dtrees_dom dts0 ->
             WF_dtrees f l0 dts0 ->
             WF_dtree f (DT_node l0 dts0)
with WF_dtrees (f:fdef) : l -> DTrees -> Prop :=
| WDT_nil : forall l0, WF_dtrees f l0 DT_nil
| WDT_cons : forall l0 dt0 dts0,
             imm_domination f l0 (get_dtree_root dt0) ->
             AtomSetImpl.inter (dtree_dom dt0) (dtrees_dom dts0) [<=] empty ->
             WF_dtree f dt0 ->
             WF_dtrees f l0 dts0 ->
             WF_dtrees f l0 (DT_cons dt0 dts0)
.

(* l1 >> l2, l1 strict dominates l2 *)
Definition gt_sdom (res: AMap.t (set l)) (l1 l2:l) : bool :=
match AMap.get l2 res with
| dts2 => in_dec l_dec l1 dts2
end.

Fixpoint find_min (res: AMap.t (set l)) (acc:l) (dts: set l): l :=
match dts with
| nil => acc
| l0::dts' =>
    if (gt_sdom res acc l0) then
      find_min res l0 dts' 
    else
      find_min res acc dts' 
end.

Fixpoint insert_sdom_iter (res: AMap.t (set l)) (l0:l) (prefix suffix:list l) 
  : list l :=
match suffix with
| nil => List.rev (l0 :: prefix)
| l1::suffix' => 
    if gt_sdom res l0 l1 then (List.rev (l0 :: prefix)) ++ suffix
    else insert_sdom_iter res l0 (l1::prefix) suffix'
end.

Fixpoint insert_sort_sdom (res: AMap.t (set l)) (data:list l) (acc:list l) 
  : list l :=
match data with
| nil => acc 
| l1 :: data' => insert_sort_sdom res data' (insert_sdom_iter res l1 nil acc)
end.

Definition sort_sdom (res: AMap.t (set l)) (data:list l) : list l :=
insert_sort_sdom res data nil.

Require Import Sorted.

Definition gt_sdom_prop (res: AMap.t (set l)) (l1 l2:l) : Prop :=
gt_sdom res l1 l2 = true.

Lemma insert_sdom_iter_sorted: forall res input,
  Sorted (gt_sdom_prop res) (sort_sdom res input).
Admitted.

Lemma insert_sdom_iter_safe: forall res input l0,
  In l0 input <-> In l0 (sort_sdom res input).
Admitted.

Fixpoint remove_redundant (input: list l) : list l :=
match input with
| a :: ((b :: _) as input') =>
    if (l_dec a b) then remove_redundant input'
    else a :: remove_redundant input'
| _ => input
end.

Lemma remove_redundant_safe: forall input l0,
  In l0 input <-> In l0 (remove_redundant input).
Admitted.

Lemma remove_redundant_sorted: forall R input,
  Sorted R input ->
  Sorted R (remove_redundant input) /\ NoDup (remove_redundant input).
Admitted.

Fixpoint compute_sdom_chains_aux (res: AMap.t (set l)) (bd: list l) 
  (acc: list (l * list l)) : list (l * list l) :=
match bd with
| nil => acc
| l0 :: bd' => 
    compute_sdom_chains_aux res bd' 
      ((l0, remove_redundant (sort_sdom res (l0 :: AMap.get l0 res)))::acc)
end.

Definition compute_sdom_chains (res: AMap.t (set l)) (bd: list l) 
  : list (l * list l) :=
compute_sdom_chains_aux res bd nil.

Lemma compute_sdom_chains_sorted: forall res bd l0 chain,
  In (l0, chain) (compute_sdom_chains res bd) ->
  Sorted (gt_sdom_prop res) chain /\ NoDup chain.
Admitted.

Lemma compute_sdom_chains_safe: forall res bd l0 chain l1,
  In (l0, chain) (compute_sdom_chains res bd) ->
  (In l1 chain <-> In l1 (l0 :: AMap.get l0 res)).
Admitted.

Fixpoint dep_doms__nondep_doms_aux bd0 (res: AMap.t (Dominators.t bd0)) 
  bd (acc: AMap.t (set l)) : AMap.t (set l) :=
match bd with
| nil => acc
| l0::bd' => 
    match AMap.get l0 res with
    | (Dominators.mkBoundedSet dts0 _) =>
        AMap.set l0 dts0 (dep_doms__nondep_doms_aux bd0 res bd' acc)
    end
end.

Definition dep_doms__nondep_doms bd (res: AMap.t (Dominators.t bd)) 
  : AMap.t (set l) :=
dep_doms__nondep_doms_aux bd res bd (AMap.init nil).

Definition wf_chain f dt (chain:list l) : Prop :=
match chain with
| entry :: _ => 
   let b := bound_fdef f in
   let res := dep_doms__nondep_doms b (dom_analyze f) in
   entry `in` dtree_dom dt /\
   NoDup chain /\ Sorted (gt_sdom_prop res) chain
| _ => True
end.

Definition getEntryLabel (f:fdef) : option l :=
match f with
| fdef_intro _ ((block_intro l0 _ _ _)::_) => Some l0
| _ => None
end.

Lemma compute_sdom_chains__wf_chain: forall f l0 chain0 entry rd,
  getEntryLabel f = Some entry ->
  reachablity_analysis f =  Some rd ->
  In (l0, chain0)
    (compute_sdom_chains
       (dep_doms__nondep_doms (bound_fdef f) (dom_analyze f)) rd) ->
  wf_chain f (DT_node entry DT_nil) chain0.
Admitted.

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

Definition dtree_insert__wf_dtree_prop (dt1:DTree) := 
forall f p ch dt2,
  WF_dtree f dt1 ->
  p `in` dtree_dom dt1 ->
  imm_domination f p ch ->
  dtree_insert dt1 p ch = dt2 ->
  WF_dtree f dt2 /\ is_dtree_edge dt2 p ch /\
  (is_dtree_edge dt1 p ch -> dt1 = dt2).

Definition dtrees_insert__wf_dtrees_prop (dts1:DTrees) := 
forall f p ch dts2 root,
  WF_dtrees f root dts1 ->
  p `in` dtrees_dom dts1 ->
  imm_domination f p ch ->
  dtrees_insert dts1 p ch = dts2 ->
  WF_dtrees f root dts2 /\ is_dtrees_edge dts2 p ch /\
  (is_dtrees_edge dts1 p ch -> dts1 = dts2).

Lemma dtree_insert__wf_dtree_mutrec :
  (forall dt1, dtree_insert__wf_dtree_prop dt1) *
  (forall dts1, dtrees_insert__wf_dtrees_prop dts1).
Proof.
  apply dtree_mutrec; 
    unfold dtree_insert__wf_dtree_prop, dtrees_insert__wf_dtrees_prop;
    simpl; intros.
Admitted.

Lemma dtree_insert__wf_dtree : forall f p ch dt1 dt2,
  WF_dtree f dt1 ->
  p `in` dtree_dom dt1 ->
  imm_domination f p ch ->
  dtree_insert dt1 p ch = dt2 ->
  WF_dtree f dt2 /\ is_dtree_edge dt2 p ch /\
  (is_dtree_edge dt1 p ch -> dt1 = dt2).
Admitted.

Fixpoint create_dtree_from_chain dt chain : DTree :=
match chain with
| p::((ch::_) as chain') => 
    create_dtree_from_chain (dtree_insert dt p ch) chain'
| _ => dt
end.

Fixpoint chain_in_dtree chain dt : Prop :=
match chain with
| p::((ch::_) as chain') => 
   is_dtree_edge dt p ch /\ chain_in_dtree chain' dt
| _ => True
end.

Lemma create_dtree_from_chain__wf_dtree: forall f dt chain,
  wf_chain f dt chain ->
  WF_dtree f dt ->
  WF_dtree f (create_dtree_from_chain dt chain).
Admitted.

Lemma create_dtree_from_chain__in_dtree: forall f dt chain,
  wf_chain f dt chain ->
  chain_in_dtree chain (create_dtree_from_chain dt chain).
Admitted.

Lemma create_dtree_from_chain__in_dtree': forall dt chain chain0,
  chain_in_dtree chain0 dt ->
  chain_in_dtree chain0 (create_dtree_from_chain dt chain).
Admitted.

Lemma create_dtree_from_chain__wf_chain: forall f chain0 chain dt,
  wf_chain f dt chain0 ->
  wf_chain f (create_dtree_from_chain dt chain) chain0.
Proof.
  induction chain; simpl; intros; auto.
    destruct chain; auto.
    apply IHchain.    

Admitted.

Definition create_dtree (f: fdef) : option DTree :=
match getEntryLabel f, reachablity_analysis f with
| Some root, Some rd =>
    let dt := dom_analyze f in
    let b := bound_fdef f in
    let chains := compute_sdom_chains (dep_doms__nondep_doms b dt) rd in
    Some (fold_left 
      (fun acc elt => let '(_, chain):=elt in create_dtree_from_chain acc chain) 
      chains (DT_node root DT_nil))
| _, _ => None
end.

Lemma fold_left_create_dtree_from_chain__wf_dtree: forall f chains dt,
  (forall l0 chain0, In (l0, chain0) chains -> wf_chain f dt chain0) ->
  WF_dtree f dt ->
  WF_dtree f
    (fold_left
       (fun (acc : DTree) (elt : l * list id) =>
        let '(_, chain) := elt in create_dtree_from_chain acc chain) chains 
       dt).
Proof.
  induction chains; simpl; intros; auto.
    destruct a.
    apply create_dtree_from_chain__wf_dtree with (chain:=l1) in H0; eauto.
      apply IHchains; auto.
        intros.
        apply create_dtree_from_chain__wf_chain; eauto.
Qed.

Lemma fold_left_create_dtree_from_chain_init_in_dtree: forall chain0 chains dt,
  chain_in_dtree chain0 dt ->
  chain_in_dtree chain0
    (fold_left
      (fun (acc : DTree) (elt : l * list id) =>
       let '(_, chain) := elt in create_dtree_from_chain acc chain)
     chains dt).
Proof.
  induction chains; intros; auto.
    apply IHchains. destruct a.
    apply create_dtree_from_chain__in_dtree'; auto.
Qed.

Lemma fold_left_create_dtree_from_chain__in_dtree: forall f l0 chain0 chains dt,
  In (l0, chain0) chains -> wf_chain f dt chain0 ->
  chain_in_dtree chain0
    (fold_left
      (fun (acc : DTree) (elt : l * list id) =>
       let '(_, chain) := elt in create_dtree_from_chain acc chain)
     chains dt).
Proof.
  induction chains; simpl; intros.
    inv H.

    destruct H as [H | H]; subst.
      apply fold_left_create_dtree_from_chain_init_in_dtree.
      eapply create_dtree_from_chain__in_dtree; eauto.

      apply IHchains; auto.
      destruct a.
      apply create_dtree_from_chain__wf_chain; eauto.
Qed.

Lemma create_dtree__wf_dtree: forall f dt,
  create_dtree f = Some dt ->
  WF_dtree f dt /\ 
  match getEntryLabel f, reachablity_analysis f with
  | Some root, Some rd =>
      let dt' := dom_analyze f in
      let b := bound_fdef f in
      let chains := compute_sdom_chains (dep_doms__nondep_doms b dt') rd in
      forall l0 chain0, 
        In (l0, chain0) chains -> chain_in_dtree chain0 dt
  | _, _ => True
  end.
Proof.
  unfold create_dtree.
  intros.
  remember (getEntryLabel f) as R.
  destruct R; tinv H.
  remember (reachablity_analysis f) as R.
  destruct R; inv H.
  split. 
    apply fold_left_create_dtree_from_chain__wf_dtree.
      intros. eapply compute_sdom_chains__wf_chain; eauto.
      apply WDT_node; auto.
        admit. (*reach*)
        constructor.
    intros.
    eapply fold_left_create_dtree_from_chain__in_dtree; eauto.
      eapply compute_sdom_chains__wf_chain; eauto.    
Qed.

Fixpoint find_idom_aux (res: AMap.t (set l)) (acc:l) (dts: set l): option l :=
match dts with
| nil => Some acc
| l0::dts' =>
    match AMap.get l0 res, AMap.get acc res with
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
Definition find_idom (res: AMap.t (set l)) (l0:l) : option l :=
match AMap.get l0 res with
| l1::dts0 => find_idom_aux res l1 dts0
| _ => None
end.

Fixpoint compute_idoms (res: AMap.t (set l)) (bd: list l) (acc: list (l * l)) :
  list (l * l) :=
match bd with
| nil => acc
| l0 :: bd' =>
    match find_idom res l0 with
    | None => compute_idoms res bd' acc
    | Some l1 => compute_idoms res bd' ((l1,l0)::acc)
    end
end.

(*
Require Import Orders.

Module NatOrder <: TotalLeBool.

Section A.
 
  Variable f: fdef.
  Variable l0: l.
  Hypothesis Hreach: reachable f l0.

  Definition t := {l0: l & }.
  Fixpoint leb x y :=
    match x, y with
    | O, _ => true
    | _, O => false
    | S x', S y' => leb x' y'
    end.
  Infix "<=?" := leb (at level 35).
  Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1. admit. Qed.

End A.

End NatOrder.

Lemma sdom_ordered : forall f l1 l2 l3
  (Hneq: l1 <> l2) (Hreach: reachable f l3)
  (Hsdom: strict_domination f l1 l3)
  (Hsdom': strict_domination f l2 l3),
  strict_domination f l1 l2 \/ strict_domination f l2 l1.
Proof.
  intros.
  apply sdom_sdom' in Hsdom; auto.
  apply sdom_sdom' in Hsdom'; auto.
  assert (J:=Hsdom').
  eapply sdom_ordered' in J; eauto.
  destruct J as [[J1 J2] | [J1 J2]].
    left. apply dom_sdom; auto.
    right. apply dom_sdom; auto.
Qed.

Require Import Sorting.

Module Import NatSort := Sort NatOrder.

Check sort.

Eval compute in sort (5::3::6::1::8::6::0::nil)%nat.
*)

(*
Fixpoint find_idom_aux (res: AMap.t (set l)) (acc:l) (dts: set l): option l :=
match dts with
| nil => Some acc
| l0::dts' =>
    match AMap.get l0 res, AMap.get acc res with
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
Definition find_idom (res: AMap.t (set l)) (l0:l) : option l :=
match AMap.get l0 res with
| l1::dts0 => find_idom_aux res l1 dts0
| _ => None
end.

(*
Fixpoint tree2dtree vs es (tree: Tree vs es) : option DTree :=
match tree with
| T_root (index le) => Some (DT_node le DT_nil)
| T_leaf vs' es' t' (index child) (index parent) _ _ => 
    match tree2dtree vs' es' t' with
    | Some dt' => dtree_insert dt' parent child
    | _ => None
    end
| T_eq vs1 vs2 es1 es2 _ _ t1 => tree2dtree vs1 es1 t1
end.
*)

Definition PreDTree := list (l * list l).

Definition getEntryLabel (f:fdef) : option l :=
match f with
| fdef_intro _ ((block_intro l0 _ _ _)::_) => Some l0
| _ => None
end.

Fixpoint cdom (pdt: PreDTree) : atoms :=
match pdt with
| nil => empty
| (_, children)::pdt' => 
    fold_left (fun acc child => add child acc) children (cdom pdt') 
end.

Inductive WF_idoms f : list (l*l) -> Prop :=
| WF_idoms_nil : WF_idoms f nil 
| WF_idoms_cons : forall l1 l2 idoms, 
    imm_domination f l1 l2 -> WF_idoms f idoms ->
    WF_idoms f ((l1,l2)::idoms)
.

Inductive WF_predtree (f:fdef) : PreDTree -> Prop :=
| WPDT_entry : forall entry children,
    getEntryLabel f = Some entry ->
    (forall child, In child children -> imm_domination f entry child) ->
    NoDup children ->
    WF_predtree f ((entry, children)::nil)
| WPDT_cons : forall parent children pdt,
    WF_predtree f pdt ->
    reachable f parent ->
    (forall child, In child children -> 
       imm_domination f parent child /\ child `notin` dom pdt `union` cdom pdt) ->
    NoDup children ->
    parent `notin` dom pdt ->
    (exists ancestor, exists parents,
      In (ancestor, parents) pdt /\ In parent parents) -> 
    WF_predtree f ((parent, children) :: pdt).

Fixpoint dtree_insert dt parent children : option DTree :=
match dt with
| DT_node l0 dts0 => 
    if (id_dec parent l0) then 
      Some (DT_node l0 
        (fold_left (fun acc child => DT_cons (DT_node child DT_nil) acc) 
          children dts0))
    else 
      match dtrees_insert dts0 parent children with
      | Some dts1 => Some (DT_node l0 dts1)
      | None => None
      end
end
with dtrees_insert (dts: DTrees) parent children : option DTrees :=
match dts with
| DT_nil => Some DT_nil
| DT_cons dt0 dts0 => 
    match dtree_insert dt0 parent children, 
          dtrees_insert dts0 parent children with
    | Some dt1, Some dts1 => Some (DT_cons dt1 dts1)
    | _, _ => None
    end
end.

Fixpoint predtree2dtree (pdt: PreDTree) : option DTree :=
match pdt with
| nil => None
| (p, chs) :: nil =>
    Some (DT_node p
      (fold_left (fun acc child => DT_cons (DT_node child DT_nil) acc) 
         chs DT_nil))
| (p, chs) :: pdt' =>
    match predtree2dtree pdt' with
    | Some dt' => dtree_insert dt' p chs
    | _ => None
    end
end.

Lemma wf_predtree__wf_dtree__helper: forall f p chs dts0
  (H0 : reachable f p)
  (H1 : forall child : l, In child chs -> 
        imm_domination f p child /\ child `notin` dtrees_dom dts0)
  (h2 : NoDup chs),
  WF_dtrees f p dts0 ->
  WF_dtrees f p
       (fold_left
          (fun (acc : DTrees) (child : l) =>
           DT_cons (DT_node child DT_nil) acc) chs dts0).
Proof.
  induction chs; simpl; intros; auto.
    inv h2.
    apply IHchs; auto.
      intros.
      assert (a = child \/ In child chs) as Hin. auto.
      apply H1 in Hin.
      destruct Hin as [J1 J2].
      simpl. split; auto.
      assert (child <> a) as Hneq.
        destruct (l_dec child a); subst; auto.
          fsetdec.

      assert (a = a \/ In a chs) as Hin. auto.
      apply H1 in Hin.
      destruct Hin as [J1 J2].
      apply WDT_cons; simpl; auto.
        fsetdec.
        apply WDT_node; auto.
          admit.
          apply WDT_nil.
Qed.

Scheme dtree_rec2 := Induction for DTree Sort Set
  with dtrees_rec2 := Induction for DTrees Sort Set.

Definition dtree_mutrec P P' :=
  fun h1 h2 h3 => 
    (pair (@dtree_rec2 P P' h1 h2 h3) (@dtrees_rec2 P P' h1 h2 h3)).

Definition dtree_insert__wf_dtree_prop (dt1:DTree) := 
forall f a1 a0,
  WF_dtree f dt1 ->
  exists dt2, dtree_insert dt1 a1 a0 = ret dt2 /\ WF_dtree f dt2.

Definition dtrees_insert__wf_dtrees_prop (dts1:DTrees) := 
forall f root a1 a0,
  WF_dtrees f root dts1 ->
  exists dts2, dtrees_insert dts1 a1 a0 = ret dts2 /\ WF_dtrees f root dts2.

Lemma dtree_insert__wf_dtree_mutrec :
  (forall dt1, dtree_insert__wf_dtree_prop dt1) *
  (forall dts1, dtrees_insert__wf_dtrees_prop dts1).
Proof.
  apply dtree_mutrec; 
    unfold dtree_insert__wf_dtree_prop, dtrees_insert__wf_dtrees_prop;
    simpl; intros.
Admitted.

Lemma dtree_insert__wf_dtree: forall f dt1 a1 a0,
  WF_dtree f dt1 ->
  exists dt2, dtree_insert dt1 a1 a0 = ret dt2 /\ WF_dtree f dt2.
Proof.
  destruct dtree_insert__wf_dtree_mutrec as [J1 _].
  unfold dtree_insert__wf_dtree_prop in J1. auto.
Qed.

Lemma WF_idoms_elim: forall f p ch idoms,
  WF_idoms f idoms -> In (p, ch) idoms -> imm_domination f p ch.
Admitted.

Lemma wf_predtree__wf_dtree : forall f pdts,
  WF_predtree f pdts ->
  exists dt, predtree2dtree pdts = Some dt /\ WF_dtree f dt.
Proof.
  intros.
  induction H; simpl.
    exists 
      (DT_node entry
         (fold_left
            (fun (acc : DTrees) (child : l) =>
             DT_cons (DT_node child DT_nil) acc) children DT_nil)).
    split; auto.
      apply WDT_node.
        admit.
        admit.
        apply wf_predtree__wf_dtree__helper; auto.
          admit. 
          apply WDT_nil.

    destruct pdt; tinv H.
    destruct IHWF_predtree as [dt [J1 J2]].
    rewrite J1.
    apply dtree_insert__wf_dtree; auto.
Qed.

Fixpoint find_children (res: AMap.t (set l)) (root:l) 
  (others:set l) (acc:list l): option (list l) :=
match others with 
| nil => Some acc
| l0::others' =>
    match find_idom res l0 with
    | None => None
    | Some l1 =>
        if (id_dec root l1) then
          if (in_dec l_dec l0 acc) 
          then find_children res root others' acc
          else find_children res root others' (l0::acc) 
        else find_children res root others' acc        
    end
end.

Lemma find_children_spec1_aux: forall res root others l0 acc children, 
  find_children res root others acc = ret children ->
  In l0 children ->
  In l0 others \/ In l0 acc.
Proof.
  induction others; simpl; intros.
    inv H; auto.

    destruct (find_idom res a); tinv H.
    destruct (id_dec root l1); subst.
      destruct (in_dec l_dec a acc).
        eapply IHothers in H; eauto.
          destruct H; auto.
        eapply IHothers in H; eauto.
          destruct H; auto.
          simpl in H. destruct H; subst; auto.
      eapply IHothers in H; eauto.
      destruct H; auto.
Qed.

Lemma find_children_spec1: forall res root others children, 
  find_children res root others nil = ret children ->
  incl children others.
Proof.
  intros. intros x Jx.
  eapply find_children_spec1_aux in H; eauto.
  destruct H; auto. inv H.
Qed.

Lemma find_children_spec2_aux: forall res root others acc children, 
  NoDup acc ->
  find_children res root others acc = ret children ->
  NoDup children.
Proof.
  induction others; simpl; intros.
    inv H0; auto.

    destruct (find_idom res a); tinv H0.
    destruct (id_dec root l0); subst; eauto.
    destruct (in_dec l_dec a acc); eauto.
Qed.

Lemma find_children_spec2: forall res root others children, 
  find_children res root others nil = ret children ->
  NoDup children.
Proof.
  intros.
  eapply find_children_spec2_aux in H; eauto.
Qed.

Lemma fold_left_remove_in_length_aux: forall (children others' others:list atom),
  NoDup children ->
  incl children others' ->
  incl others' others ->
  (length others' <= length others)%nat ->
  children <> nil ->
  (length (fold_left
    (fun (acc0 : list atom) (l0 : id) => List.remove eq_atom_dec l0 acc0)
      children others') < length others)%nat.
Proof.
  induction children; simpl; intros.
    congruence.

    assert (In a others') as Hin.
      apply H0; simpl; auto.
    assert (J:=@remove_in_length _ eq_atom_dec a others' Hin).
    assert ((length (List.remove eq_atom_dec a others') < length others)%nat) 
      as J'.
      omega.
    inv H.
    destruct children.
      simpl. auto.

      apply IHchildren; auto.
        intros x Jx.
        assert (In x (a :: a0 :: children)) as Hin'.
          simpl in Jx. destruct Jx; subst; simpl; auto.
        apply H0 in Hin'.
        apply remove_neq_in; auto.
        destruct (id_dec x a); subst; auto.

        intros x Jx. 
        apply H1.
        apply remove_neq_in' in Jx; auto.
        destruct Jx as [Jx1 Jx2]; auto.
        omega.

        intro J0. inv J0.
Qed.

Lemma fold_left_remove_in_length: forall (children others:list atom),
  NoDup children ->
  incl children others ->
  children <> nil ->
  (length (fold_left
    (fun (acc0 : list atom) (l0 : id) => List.remove eq_atom_dec l0 acc0)
      children others) < length others)%nat.
Proof.
  intros.
  apply fold_left_remove_in_length_aux; auto.
    apply incl_refl.
Qed.

Fixpoint find_next_children (idoms: list (l * l)) (parent: l) (acc : list l)
  (others: set l) : list l * set l :=
match idoms with
| nil => (acc, others)
| (l1, l2)::idoms' =>
    if (l_dec l1 parent) then 
      if (in_dec l_dec l2 others) then
        find_next_children idoms' parent (l2::acc) (List.remove l_dec l2 others)
      else find_next_children idoms' parent acc others
    else find_next_children idoms' parent acc others
end.

Fixpoint find_next_children_from_children (idoms: list (l * l)) (children:list l)
  (others: set l) : option (l * list l * set l) :=
match children with
| nil => None
| ch::children' =>
    match find_next_children idoms ch nil others with
    | (nil, _) => find_next_children_from_children idoms children' others
    | (children0, others') => Some (ch, children0, others')
    end
end.

Fixpoint find_next_sub_predtree_aux (idoms: list (l * l)) (pdt0 pdt:PreDTree) 
  (others:set l) : option (PreDTree * set l) :=
match pdt with
| nil => None
| (p, chs)::pdt' => 
    match find_next_children_from_children idoms chs others with
    | None => find_next_sub_predtree_aux idoms pdt0 pdt' others
    | Some (ch, chs', others') => Some ((ch, chs')::pdt0, others')
    end
end.

Definition find_next_sub_predtree (idoms: list (l * l)) (pdt:PreDTree) 
  (others:set l) : option (PreDTree * set l) :=
find_next_sub_predtree_aux idoms pdt pdt others.

Lemma in_singleton_inv: forall A (a b:A), In a [b] -> a = b.
Proof.
  intros.
  simpl in H. destruct H; auto. inv H.
Qed.

Lemma find_next_children_inv : forall p idoms chs others chs' others',
  find_next_children idoms p chs others = (chs', others') ->
  exists chs'', chs' = chs'' ++ chs /\
    others' = fold_right (fun ch acc => List.remove l_dec ch acc) others chs'' /\
    (forall ch, In ch chs'' -> In ch others /\ In (p, ch) idoms).
Proof.
  induction idoms; simpl; intros.
    inv H.
    exists nil. simpl.
    split; auto.
    split; auto. 
      intros. inversion H.

    destruct a.
    destruct (l_dec l0 p); subst.
      destruct (in_dec l_dec l1 others).
        apply IHidoms in H.
        destruct H as [chs'' [J1 [J2 J3]]]; subst.
        exists (chs''++[l1]).
        simpl_env.
        split; auto.
        split.
          rewrite fold_right_app. simpl. auto.

          intros ch Hin.
          apply in_app_or in Hin.
          destruct Hin as [Hin | Hin].
            apply J3 in Hin.
            destruct Hin as [J2 J4].
            split; auto.
              apply remove_neq_in' in J2.
              destruct J2; auto.

            apply in_singleton_inv in Hin; subst.
            split; auto.
    
        apply IHidoms in H.
        destruct H as [chs'' [J1 [J2 J3]]]; subst.
        exists chs''.
        split; auto.
        split; auto.
          intros ch Hin.
          apply J3 in Hin.
          destruct Hin as [J2 J4].
          split; auto.
      apply IHidoms in H.
      destruct H as [chs'' [J1 [J2 J3]]]; subst.
      exists chs''.
      split; auto.
      split; auto.
        intros ch Hin.
        apply J3 in Hin.
        destruct Hin as [J2 J4].
        split; auto.
Qed.       

Lemma find_next_children_from_children_inv: forall idoms chs others ch chs' others',
  find_next_children_from_children idoms chs others = ret (ch, chs', others') ->
  others' = fold_right (fun ch0 acc => List.remove l_dec ch0 acc) others chs' /\
  In ch chs /\ (forall ch', In ch' chs' -> In ch' others /\ In (ch, ch') idoms)
  /\ chs' <> nil.
Proof.
  induction chs; simpl; intros.
    inv H.

    remember (find_next_children idoms a nil others) as R.
    destruct R.
    destruct l0; auto.
      apply IHchs in H.
      destruct H as [J1 [J2 J3]].
      split; auto.

      inv H.
      symmetry in HeqR.
      apply find_next_children_inv in HeqR; auto.
      destruct HeqR as [chs'' [J1 [J2 J3]]]; subst.
      simpl_env in J1. subst.
      split; auto.
      split; auto.
      split; auto.
        intro J. inv J.
Qed.

Lemma find_next_sub_predtree_aux_inv: forall idoms pdt0 pdt others pdt' 
  others',
  find_next_sub_predtree_aux idoms pdt0 pdt others = Some (pdt', others') ->
  exists p, exists chs, 
    pdt' = (p,chs)::pdt0 /\ 
    others' = fold_right (fun ch0 acc => List.remove l_dec ch0 acc) others chs /\
    (forall ch, In ch chs -> In ch others /\ In (p, ch) idoms) /\ chs <> nil /\
    exists p', exists chs', In (p', chs') pdt /\ In p chs'.
Proof.
  induction pdt; simpl; intros.
    inv H.

    destruct a.
    remember (find_next_children_from_children idoms l1 others) as R.
    destruct R as [[[ch ch'] others'']|].
      inv H.
      exists ch. exists ch'. 
      symmetry in HeqR.
      apply find_next_children_from_children_inv in HeqR.
      destruct HeqR as [J1 [J2 [J3 J4]]]; subst.
      split; auto.
      split; auto.
      split; auto.
      split; auto.
        exists l0. exists l1. split; auto.

      apply IHpdt in H; auto.
      destruct H as [p [chs [Heq1 [Heq2 [J1 [J0 [p' [chs' [J2 J3]]]]]]]]]; 
        subst.
      exists p. exists chs. 
      split; auto.
      split; auto.
      split; auto.
      split; auto.
        exists p'. exists chs'. split; auto.
Qed.

Lemma find_next_sub_predtree_inv: forall idoms pdt others pdt' 
  others',
  find_next_sub_predtree idoms pdt others = Some (pdt', others') ->
  exists p, exists chs, 
    pdt' = (p,chs)::pdt /\ 
    others' = fold_right (fun ch0 acc => List.remove l_dec ch0 acc) others chs /\
    (forall ch, In ch chs -> In ch others /\ In (p, ch) idoms) /\ chs <> nil /\
    exists p', exists chs', In (p', chs') pdt /\ In p chs'.
Proof.
  intros. unfold find_next_sub_predtree in H.
  apply find_next_sub_predtree_aux_inv in H; auto.
Qed.

Lemma fold_right_remove_length: forall chs others
  (J1 : forall ch : l, In ch chs -> In ch others)
  (J0 : chs <> nil),
  (length
     (fold_right
        (fun (ch0 : l) (acc0 : list l) => List.remove l_dec ch0 acc0) others
        chs) < length others)%nat.
Proof.
  induction chs; simpl; intros.
    congruence.

    destruct chs.
      simpl.
      apply remove_in_length; auto.

      assert (length
               (fold_right
                  (fun (ch0 : l) (acc0 : list l) => List.remove l_dec ch0 acc0)
                  others (l0::chs)) < length others)%nat as J.
        apply IHchs; auto.
          intro J. inv J.
      assert (G:=@remove_length _ l_dec a (fold_right
                  (fun (ch0 : l) (acc0 : list l) => List.remove l_dec ch0 acc0)
                  others (l0::chs))).
      omega.
Qed.

Lemma find_next_sub_predtree_length: forall idoms acc others acc' others',
  find_next_sub_predtree idoms acc others = ret (acc', others') ->
  (length others' < length others)%nat.
Proof.
  intros.
  apply find_next_sub_predtree_inv in H.
  destruct H as [p [chs [Heq1 [Heq2 [J1 [J0 [p' [chs' [J2 J3]]]]]]]]]; subst.
  apply fold_right_remove_length; auto.
  intros ch Hin. apply J1 in Hin. destruct Hin; auto.
Qed.

Program Fixpoint create_predtree_aux (others:set l) (idoms: list (l * l)) 
  (acc:PreDTree) {measure (List.length others)} : option PreDTree :=
match others with
| nil => Some acc
| _ =>
   match find_next_sub_predtree idoms acc others with
   | None => None
   | Some (acc', others') => create_predtree_aux others' idoms acc'
   end
end.
Next Obligation. 
  eapply find_next_sub_predtree_length; eauto.
Qed.

Fixpoint init_predtree (idoms: list (l * l)) (root:l) (others:set l)
  : option (PreDTree * list l) :=
match find_next_children idoms root nil others with
| (nil, _) => None
| (children, others') => Some ([(root, children)], others')
end.

Definition create_dtree (f: fdef) : option DTree :=
match getEntryBlock f, reachablity_analysis f with
| Some (block_intro root _ _ _), Some rd =>
    let dt := dom_analyze f in
    let b := bound_fdef f in
    let idoms := compute_idoms (dep_doms__nondep_doms b dt) rd nil in
    match init_predtree idoms root (List.remove eq_atom_dec root rd) with
    | None => None
    | Some (pdt0, others) =>
        match (create_predtree_aux others idoms pdt0) with
        | None => None
        | Some pdt => predtree2dtree pdt
        end
    end
| _, _ => None
end.

Lemma in_predtree_dom: forall p chs (pdt0:PreDTree),
  In (p, chs) pdt0 -> p `in` dom pdt0.
Proof.
  induction pdt0; simpl; intros.
    inv H.
    destruct H as [H | H]; subst.
      fsetdec.

      destruct a.
      apply IHpdt0 in H.
      fsetdec.
Qed.

Lemma in_fold_left_atoms: forall ch chs init
  (H0 : In ch chs \/ ch `in` init),
  ch `in` fold_left (fun (acc : atoms) (child : atom) => add child acc) chs init.
Proof.
  induction chs; simpl; intros.
    destruct H0; auto.
      inv H.
    destruct H0 as [[H0 | H0] | H0]; subst; eauto.
Qed.

Lemma in_predtree_cdom: forall p chs ch pdt0,
  In (p, chs) pdt0 -> In ch chs -> ch `in` cdom pdt0.
Proof.
  induction pdt0; simpl; intros.
    inv H.
    destruct H as [H | H]; subst.
      apply in_fold_left_atoms; auto.
    destruct a.
    apply in_fold_left_atoms; auto.
Qed.

Definition P_create_predtree_aux__WF_predtree (n:nat) :=
  forall f idoms (Hwfi: WF_idoms f idoms) pdt0 others pdt
  (Hdis: forall l0, 
    In l0 others -> 
    l0 `notin` dom pdt0 `union` cdom pdt0),
  List.length others = n ->
  WF_predtree f pdt0 ->
  create_predtree_aux others idoms pdt0 = Some pdt ->
  WF_predtree f pdt.

Require Import Program.

Ltac simple_create_predtree_aux :=
  unfold create_predtree_aux, create_predtree_aux_func;
  rewrite WfExtensionality.fix_sub_eq_ext;
  repeat fold_sub create_predtree_aux_func ; simpl proj1_sig;
  simpl. 

Lemma in_fold_right_remove: forall p chs others
  (Hin : In p
          (fold_right
             (fun (ch0 : l) (acc : list l) => List.remove l_dec ch0 acc)
             others chs)),
  In p others /\ ~ In p chs.
Proof.
  induction chs; simpl; intros.
    split; auto.

    apply remove_neq_in' in Hin; auto.
    destruct Hin as [J1 J2].
    apply IHchs in J1.
    destruct J1 as [J1 J3].
    split; auto.
      intro J. destruct J as [J | J]; auto.
Qed.

Lemma notin_fold_left_atoms: forall ch chs init,
  ~ In ch chs -> ch `notin` init -> 
  ch `notin` 
    fold_left (fun (acc : atoms) (child : atom) => add child acc) chs init.
Proof.
  induction chs; simpl; intros; auto.
Qed.

Lemma find_next_sub_predtree_fresh: forall (pdt0 : list (atom * list l)) idoms
  (others : list atom) (pdt : PreDTree)
  (Hdis : forall l0 : atom,
          In l0 others -> l0 `notin` union (dom pdt0) (cdom pdt0))
  (acc' : PreDTree) (others' : set l)
  (HeqR : ret (acc', others') =
          find_next_sub_predtree idoms pdt0 others),
  forall l0 : atom, In l0 others' -> l0 `notin` union (dom acc') (cdom acc').
Proof.
  intros.
  symmetry in HeqR.
  apply find_next_sub_predtree_inv in HeqR.
  destruct HeqR as [p [chs [Heq [J1 [J2 [J3 [p' [chs' [J4 J5]]]]]]]]]; subst.
  simpl.
  apply in_fold_right_remove in H.
  destruct H as [J6 J7].
  apply Hdis in J6.
  assert (l0 `notin` 
       (fold_left (fun (acc : atoms) (child : atom) => add child acc)
          chs (cdom pdt0))) as J8.
    apply notin_fold_left_atoms; auto.
  assert (l0 <> p) as Hneq.
    destruct (l_dec l0 p); subst; auto.
    eapply in_predtree_cdom in J4; eauto.
  fsetdec.
Qed.

Lemma WF_predtree__reachable: forall f pdt p chs ch,
  WF_predtree f pdt ->
  In (p, chs) pdt ->
  In ch chs ->
  reachable f ch.
Admitted.

Lemma find_next_sub_predtree_wf_predtree: 
  forall f idoms (Hwfi: WF_idoms f idoms) pdt (Hwf:WF_predtree f pdt) 
    others pdt' others'
  (Hdis: forall l0, 
    In l0 others -> 
    l0 `notin` dom pdt `union` cdom pdt),
  find_next_sub_predtree idoms pdt others = ret (pdt', others') ->
  WF_predtree f pdt'.
Proof.
  intros.
  apply find_next_sub_predtree_inv in H.
  destruct H as [p [chs [Heq [J1 [J2 [J3 [p' [chs' [J4 J5]]]]]]]]]; subst.
  apply WPDT_cons; auto.
    eapply WF_predtree__reachable in J4; eauto.

    intros child Hin.
    apply J2 in Hin.
    destruct Hin as [Hin1 Hin2].
    split; auto.
      eapply WF_idoms_elim; eauto.

    admit.

    

Lemma find_next_sub_predtree_aux_wf_predtree: 
  forall f idoms (Hwfi: WF_idoms f idoms) acc prefix 
    (Hwf:WF_predtree f (prefix++acc)) others acc' others'
  (Hdis: forall l0, 
    In l0 others -> 
    l0 `notin` dom (prefix++acc) `union` cdom (prefix++acc)),
  find_next_sub_predtree_aux idoms (prefix++acc) acc others = 
    ret (acc', others') ->
  WF_predtree f acc'.
Proof.
  intros.
  applu 


  induction acc; simpl; intros.
    congruence.

    destruct a.
    remember (find_next_child idoms l1 others) as R.
    destruct R.
      inv H.
      apply WPDT_cons; auto.
        apply WF_predtree__reachable with (l1:=l0)(l2:=l1) in Hwf.
          destruct Hwf; auto.
          apply in_middle.
        eapply find_next_child__imm_domination; eauto.

        symmetry in HeqR.
        apply find_next_child_inv in HeqR.
        destruct HeqR as [J1 J2]. auto.

        right.
        exists l0. apply in_middle.

      remember (find_next_child idoms l0 others) as R.
      destruct R.
        inv H.
        apply WPDT_cons; auto.
          apply WF_predtree__reachable with (l1:=l0)(l2:=l1) in Hwf.
            destruct Hwf; auto.
            apply in_middle.
          eapply find_next_child__imm_domination; eauto.

          symmetry in HeqR0.
          apply find_next_child_inv in HeqR0.
          destruct HeqR0 as [J1 J2]. auto.
          left. simpl_env. fsetdec.
      rewrite_env ((prefix ++ [(l0, l1)]) ++ acc) in H.
      apply IHacc in H; simpl_env; simpl; auto.
Qed.

Lemma find_next_sub_predtree_wf_predtree: 
  forall f idoms (Hwfi: WF_idoms f idoms) pdt (Hwf:WF_predtree f pdt) 
    others pdt' others'
  (Hdis: forall l0, 
    In l0 others -> 
    l0 `notin` dom pdt `union` cdom pdt),
  find_next_sub_predtree idoms pdt others = ret (pdt', others') ->
  WF_predtree f pdt'.
Proof.
  intros.
  unfold find_next_sub_predtree in H.
  change pdt with (nil++pdt) in H, Hdis at 1.
  eapply find_next_sub_predtree_aux_wf_predtree in H; eauto.
Qed.

Lemma create_predtree_aux__WF_predtree_aux: forall n, 
  P_create_predtree_aux__WF_predtree n.
Proof.
  intro n.
  apply lt_wf_rec. clear n.
  intros n IH.
  unfold P_create_predtree_aux__WF_predtree in *.
  intros f idoms Hwfi pdt0 others pdt Hdis Hlen Hwf.
  destruct others as [|l1 others]; simple_create_predtree_aux.
    intro J. inv J; auto.

    remember (find_next_sub_predtree idoms pdt0 (l1 :: others)) as R.
    destruct R as [[acc' others']|].
      repeat fold_sub create_predtree_aux_func ; simpl proj1_sig.
      fold (create_predtree_aux others' idoms acc').
      intro J. subst.
      apply IH with (m:=length others') (f:=f) in J; auto.
        eapply find_next_sub_predtree_length; eauto.
        eapply find_next_sub_predtree_fresh; eauto.
        eapply find_next_sub_predtree_wf_predtree; eauto.
      intro J. inv J.
Qed.

Lemma create_predtree_aux__WF_predtree : forall f idoms 
  (Hwfi: WF_idoms f idoms) pdt0 others pdt
  (Hdis: forall l0, 
    In l0 others -> 
    l0 `notin` dom pdt0 `union` cdom pdt0),
  WF_predtree f pdt0 ->
  create_predtree_aux others idoms pdt0 = Some pdt ->
  WF_predtree f pdt.
Proof.
  intros.
  assert (J:=@create_predtree_aux__WF_predtree_aux (List.length others)).
  unfold P_create_predtree_aux__WF_predtree in J. eauto.
Qed.

Program Fixpoint create_dtree_aux (others:set l) (res: AMap.t (set l)) 
  (root:l) {measure (List.length others)}
  : option DTree :=
match find_children res root others nil with
| Some nil => Some (DT_node root DT_nil)
| Some children =>
    let others' := 
      fold_left (fun acc l1 => List.remove id_dec l1 acc) children others in
    let op_dts0 :=
      (fold_left 
        (fun acc l1 => 
         match acc, create_dtree_aux others' res l1 with
         | Some dts0, Some dt0 => Some (DT_cons dt0 dts0) 
         | _, _ => None
         end)
        children (Some DT_nil)) in
    match op_dts0 with
    | Some dts0 => Some (DT_node root dts0)
    | _ => None
    end
| _ => None 
end.
Next Obligation. 
  symmetry in Heq_anonymous.
  apply fold_left_remove_in_length; auto.
    apply find_children_spec2 in Heq_anonymous; auto.
    apply find_children_spec1 in Heq_anonymous; auto.
    intro J. subst. auto.
Qed.
Next Obligation. split; intros; congruence. Qed.

Lemma find_next_child__imm_domination: forall f idoms (Hwfi: WF_idoms f idoms) 
  l1 others l2,
  find_next_child idoms l1 others = ret l2 ->
  imm_domination f l1 l2.
Proof.
  induction idoms; simpl; intros.
    inv H.

    destruct a.
    inv Hwfi.
    destruct (l_dec l0 l1); subst; eauto.
      destruct (in_dec l_dec l3 others); eauto.
        inv H. auto.
Qed.

Lemma init_predtree__WF_predtree : forall f root 
  (Hentry:getEntryLabel f = Some root) idoms 
  (Hwfi: WF_idoms f idoms) others pdt0 others0,
  init_predtree idoms root others = Some (pdt0, others0) ->
  WF_predtree f pdt0.
Proof.
  induction idoms; simpl; intros.
    inv H.

    destruct a.
    inv Hwfi.
    destruct (l_dec l0 root); subst; eauto.
      destruct (in_dec l_dec l1 others); inv H.
      apply WPDT_entry; auto.
Qed.

Lemma init_predtree__disjoint: forall root idoms others pdt0 others0,
  init_predtree idoms root others = ret (pdt0, others0) ->
  ~ In root others ->
  forall l0 : atom, In l0 others0 -> l0 `notin` union (dom pdt0) (cdom pdt0).
Proof.
  induction idoms; simpl; intros.
    inv H.

    destruct a.
    destruct (l_dec l1 root); subst.
      destruct (in_dec l_dec l2 others); inv H.
        simpl.
        assert (l0 <> l2) as Hneq.
          assert (J':=@remove_In _ l_dec others l2).
          destruct (l_dec l0 l2); subst; auto.
        assert (In l0 others) as Hin'.
          apply remove_neq_in' in H1; auto.
        assert (l0 <> root) as Hneq'.
          destruct (l_dec l0 root); subst; auto.
        fsetdec.

      eapply IHidoms in H; eauto.        
Qed.

Lemma compute_idoms__WF_idoms_aux: forall f rd idoms acc,
  reachablity_analysis f = Some rd ->
  WF_idoms f acc ->
  compute_idoms (dep_doms__nondep_doms (bound_fdef f) (dom_analyze f)) rd acc 
    = idoms ->
  WF_idoms f idoms.
Proof.
  induction rd; simpl; intros; subst; auto.
    remember 
      (find_idom (dep_doms__nondep_doms (bound_fdef f) (dom_analyze f)) a) as R.
    destruct R.
      apply IHrd with (acc:=(l0, a) :: acc); auto.
        admit.
        apply WF_idoms_cons; auto.
          admit.
      apply IHrd with (acc:=acc); auto.
        admit.
Qed.

Lemma compute_idoms__WF_idoms: forall f rd idoms,
  reachablity_analysis f = Some rd ->
  compute_idoms (dep_doms__nondep_doms (bound_fdef f) (dom_analyze f)) rd nil 
    = idoms ->
  WF_idoms f idoms.
Proof.
  intros.
  apply compute_idoms__WF_idoms_aux in H0; auto.
    apply WF_idoms_nil.
Qed.

Lemma init_create_predtree_aux__WF_predtree : forall f idoms pdt0 others 
  pdt root rd,
  getEntryLabel f = Some root ->
  reachablity_analysis f = Some rd ->
  compute_idoms (dep_doms__nondep_doms (bound_fdef f) (dom_analyze f)) rd nil 
    = idoms ->
  init_predtree idoms root (List.remove eq_atom_dec root rd) 
    = Some (pdt0, others) ->
  create_predtree_aux others idoms pdt0 = Some pdt ->
  WF_predtree f pdt.
Proof.
  intros.
  eapply compute_idoms__WF_idoms in H1; eauto.
  eapply create_predtree_aux__WF_predtree in H3; eauto.
    eapply init_predtree__disjoint; eauto.
      apply remove_In.
    eapply init_predtree__WF_predtree; eauto.
Qed.

Scheme dtree_rec2 := Induction for DTree Sort Set
  with dtrees_rec2 := Induction for DTrees Sort Set.

Definition dtree_mutrec P P' :=
  fun h1 h2 h3 => 
    (pair (@dtree_rec2 P P' h1 h2 h3) (@dtrees_rec2 P P' h1 h2 h3)).

Definition dtree_insert__wf_dtree_prop (dt1:DTree) := 
forall f a1 a0 dt2,
  WF_dtree f dt1 ->
  dtree_insert dt1 a1 a0 = ret dt2 ->
  WF_dtree f dt2.

Definition dtrees_insert__wf_dtrees_prop (dts1:DTrees) := 
forall f root a1 a0 dts2,
  WF_dtrees f root dts1 ->
  dtrees_insert dts1 a1 a0 = ret dts2 ->
  WF_dtrees f root dts2.

Lemma dtree_insert__wf_dtree_mutrec :
  (forall dt1, dtree_insert__wf_dtree_prop dt1) *
  (forall dts1, dtrees_insert__wf_dtrees_prop dts1).
Proof.
  apply dtree_mutrec; 
    unfold dtree_insert__wf_dtree_prop, dtrees_insert__wf_dtrees_prop;
    simpl; intros.

    inv H0.
    destruct (id_dec a1 l0); subst.
      inv H1.
      apply WDT_node; simpl; auto.
        admit.
        apply WDT_cons; simpl; auto.
          admit.
          admit.
          apply WDT_node; simpl; auto.
            admit.
            apply WDT_nil.
       
      remember (dtrees_insert d a1 a0) as R.
      destruct R; inv H1. 
        apply WDT_node; simpl; eauto.
          admit.
        
    inv H0. auto.

    remember (dtree_insert d a1 a0) as R.
    destruct R; inv H2. 
    remember (dtrees_insert d0 a1 a0) as R.
    destruct R; inv H4. 
    inv H1.
    apply WDT_cons; simpl; eauto.
      admit.
      admit.
Qed.

Lemma dtree_insert__wf_dtree: forall f a1 a0 dt1 dt2,
  WF_dtree f dt1 ->
  dtree_insert dt1 a1 a0 = ret dt2 ->
  WF_dtree f dt2.
Proof.
  induction dt1; simpl; intros.
    destruct (id_dec a1 l0); subst.
      inv H0.
      inv H.
      apply WDT_node; simpl; auto.
        admit.
        apply WDT_cons; simpl; auto.
          admit.
          admit.
          apply WDT_node; simpl; auto.
            admit.
            apply WDT_nil.
       
      remember (dtrees_insert d a1 a0) as R.
      destruct R.
        inv H0. auto.


Admitted.

Lemma tree2dtree__wf_dtree: forall f vs es tree dt,
  tree2dtree vs es tree = Some dt -> WF_dtree f dt.
Proof.
  induction tree; simpl; intros.
    destruct r. inv H.
    apply WDT_node.
      admit.
      simpl. fsetdec.
      apply WDT_nil.

    destruct f0. destruct n.
    remember (tree2dtree v a tree) as R.
    destruct R.
      eapply dtree_insert__wf_dtree in H; eauto.
      inv H.

    apply IHtree in H; auto.
Qed.
*)

(*
Definition create_dtree (f: fdef) : option DTree :=
match getEntryBlock f, reachablity_analysis f with
| Some (block_intro root _ _ _), Some rd =>
    let 'dt := dom_analyze f in
    let 'b := bound_fdef f in
    create_dtree_aux (dep_doms__nondep_doms b dt) root 
      (List.remove eq_atom_dec root rd)
| _, _ => None
end.
*)

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
