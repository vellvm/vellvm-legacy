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
   Sorted (gt_sdom_prop res) chain /\ NoDup chain
| _ => False
end.

Definition getEntryLabel (f:fdef) : option l :=
match f with
| fdef_intro _ ((block_intro l0 _ _ _)::_) => Some l0
| _ => None
end.

Lemma compute_sdom_chains__entry: forall f entry rd l0 chain0,
  getEntryLabel f = Some entry ->
  reachablity_analysis f =  Some rd ->
  In (l0, chain0)
    (compute_sdom_chains
      (dep_doms__nondep_doms (bound_fdef f) (dom_analyze f)) rd) ->
  exists chain0', chain0 = entry :: chain0'.
Admitted.

Lemma compute_sdom_chains__wf_chain: forall f l0 chain0 entry rd,
  getEntryLabel f = Some entry ->
  reachablity_analysis f =  Some rd ->
  In (l0, chain0)
    (compute_sdom_chains
       (dep_doms__nondep_doms (bound_fdef f) (dom_analyze f)) rd) ->
  wf_chain f (DT_node entry DT_nil) chain0.
Proof.
  intros.
  assert (H1':=H1).
  eapply compute_sdom_chains__entry in H1'; eauto.
  destruct H1' as [chain0' H1']; subst; simpl.
  split; auto.
    eapply compute_sdom_chains_sorted; eauto.
Qed.

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
    let chains := compute_sdom_chains (dep_doms__nondep_doms b dt) rd in
    Some (fold_left 
      (fun acc elt => let '(_, chain):=elt in create_dtree_from_chain acc chain) 
      chains (DT_node root DT_nil))
| _, _ => None
end.

Lemma dtrees_insert__in_children_roots: forall ch p0 ch0 dts,
  in_children_roots ch dts = in_children_roots ch (dtrees_insert dts p0 ch0).
Proof.
  induction dts; simpl; auto.
    rewrite <- IHdts.
    destruct d. simpl.
    destruct (l_dec l0 ch); subst.
      destruct (id_dec p0 ch); subst.
        destruct (in_children_roots ch0 d);
          destruct (l_dec ch ch); auto; try congruence.
        destruct (l_dec ch ch); auto; try congruence.
      destruct (id_dec p0 l0); subst.
        destruct (in_children_roots ch0 d);
          destruct (l_dec l0 ch); auto; try congruence.
        destruct (l_dec l0 ch); auto; try congruence.
Qed.

Definition dtree_insert__is_dtree_edge_prop (dt:DTree) := 
forall p ch p0 ch0,
  is_dtree_edge (dtree_insert dt p ch) p0 ch0 <-> 
  is_dtree_edge dt p0 ch0 \/ (p `in` dtree_dom dt /\ p = p0 /\ ch = ch0).

Fixpoint size_of_dtrees (dts:DTrees) : nat :=
match dts with
| DT_nil => O
| DT_cons _ dts' => S (size_of_dtrees dts')
end.

Definition dtrees_insert__is_dtrees_edge_prop (dts:DTrees) := 
forall p ch p0 ch0,
  is_dtrees_edge (dtrees_insert dts p ch) p0 ch0 <-> 
  is_dtrees_edge dts p0 ch0 \/ (p `in` dtrees_dom dts /\ p = p0 /\ ch = ch0).

Lemma dtree_insert__is_dtree_edge_mutrec :
  (forall dt, dtree_insert__is_dtree_edge_prop dt) *
  (forall dts, dtrees_insert__is_dtrees_edge_prop dts).
Proof.
  apply dtree_mutrec; 
    unfold dtree_insert__is_dtree_edge_prop, dtrees_insert__is_dtrees_edge_prop;
    simpl; intros.

  Case "1".
    destruct (id_dec p l0); subst.
    SCase "1.1".
      destruct (id_dec p0 l0); subst.
      SSCase "1.1.1".
        remember (in_children_roots ch d) as R.
        destruct R; simpl.
        SSSCase "1.1.1.1".
          destruct (id_dec l0 l0); try congruence.
          split; intro J; auto.
            destruct J as [J | [J1 [J2 J3]]]; subst; auto.
            rewrite <- HeqR. reflexivity.

        SSSCase "1.1.1.2".
          destruct (id_dec l0 l0); try congruence.
          destruct (l_dec ch ch0); subst.
          SSSSCase "1.1.1.2.1".
            split; auto.
              intros. reflexivity.
          SSSSCase "1.1.1.2.2".
            destruct (in_children_roots ch0 d).
              split; auto.
                intros. 
                destruct H0 as [H0 | [J1 J2]]; subst; auto; try congruence.
              destruct (id_dec l0 ch); subst.
                split; intros.
                  apply orb_true_iff in H0.
                  destruct H0; auto; try congruence.

                  apply orb_true_iff.
                  destruct H0 as [H0 | [J1 [J2 J3]]]; subst; auto.
                split; intros.
                  apply orb_true_iff in H0.
                  destruct H0; auto; try congruence.

                  apply orb_true_iff.
                  destruct H0 as [H0 | [J1 [J2 J3]]]; subst; auto.
      SSCase "1.1.2".
        remember (in_children_roots ch d) as R.
        destruct R; simpl.
        SSSCase "1.1.2.1".
          destruct (id_dec p0 l0); try congruence.
          split; intro J; auto.
            destruct J as [J | [J1 [J2 J3]]]; subst; auto.
              congruence.
        SSSCase "1.1.2.2".
          destruct (id_dec p0 l0); try congruence.
          destruct (l_dec p0 ch); subst.
          SSSSCase "1.1.2.2.1".
            destruct (id_dec ch ch); try congruence.
            split; intros.
              apply orb_true_iff in H0.
              destruct H0; auto; try congruence.

              apply orb_true_iff.
              destruct H0 as [H0 | [J1 [J2 J3]]]; subst; auto.

          SSSSCase "1.1.2.2.2".
            destruct (id_dec p0 ch); subst; try congruence.
            split; intros.
              apply orb_true_iff in H0.
              destruct H0; auto; try congruence.

              apply orb_true_iff.
              destruct H0 as [H0 | [J1 [J2 J3]]]; subst; auto.

    SCase "1.2".
      simpl.
      rewrite <- dtrees_insert__in_children_roots.
      destruct (id_dec p0 l0); subst.
      SSCase "1.2.1".
        remember (in_children_roots ch0 d) as R.
        destruct R; simpl.
        SSSCase "1.2.1.1".
          split; intro J; auto.
            reflexivity.
        SSSCase "1.2.1.2".
          split; intro J.
            apply H in J.
            destruct J as [J | [J1 [J2 J3]]]; subst; auto.

            apply H.
            destruct J as [J | [J1 [J2 J3]]]; subst; auto.
              congruence.
      SSCase "1.2.2".
        split; intro J; auto.
          apply H in J.
          destruct J as [J | [J1 [J2 J3]]]; subst; auto.

          apply H.
          destruct J as [J | [J1 [J2 J3]]]; subst; auto.
            right. fsetdec.

  Case "2".
    split; intros J.
       congruence.
       destruct J as [J | [J1 [J2 J3]]]; subst; auto.
         fsetdec.

  Case "3".
    split; intros J.
      apply orb_true_iff in J.
      destruct J as [J | J].
        apply H in J. 
        destruct J as [J | [J1 [J2 J3]]]; subst.
          left. apply orb_true_iff. auto.
          right. fsetdec.

        apply H0 in J. 
        destruct J as [J | [J1 [J2 J3]]]; subst.
          left. apply orb_true_iff. auto.
          right. fsetdec.

      apply orb_true_iff.
      destruct J as [J | [J1 [J2 J3]]]; subst.
        apply orb_true_iff in J.
        destruct J as [J | J].
          left. apply H; auto.
          right. apply H0; auto.

        assert (p0 `in` (dtree_dom d) \/ p0 `in` (dtrees_dom d0)) as J.
          fsetdec.
        destruct J as [J | J].
          left. apply H; auto.
          right. apply H0; auto.
Qed.
        
Lemma dtree_insert__is_dtree_edge : forall p ch p0 ch0 dt ,
  is_dtree_edge (dtree_insert dt p ch) p0 ch0 <-> 
  is_dtree_edge dt p0 ch0 \/ (p `in` dtree_dom dt /\ p = p0 /\ ch = ch0).
Proof.
  destruct (dtree_insert__is_dtree_edge_mutrec).
  unfold dtree_insert__is_dtree_edge_prop in *.
  eauto.
Qed.

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

Definition dtree_insert__in_dtree_dom_prop (dt:DTree) := 
forall p ch,
  p `in` dtree_dom dt -> is_dtree_edge (dtree_insert dt p ch) p ch.

Definition dtrees_insert__in_dtrees_dom_prop (dts:DTrees) := 
forall p ch,
  p `in` dtrees_dom dts ->is_dtrees_edge (dtrees_insert dts p ch) p ch.

Lemma dtree_insert__in_dtree_dom_mutrec :
  (forall dt, dtree_insert__in_dtree_dom_prop dt) *
  (forall dts, dtrees_insert__in_dtrees_dom_prop dts).
Proof.
  apply dtree_mutrec; 
    unfold dtree_insert__in_dtree_dom_prop, 
           dtrees_insert__in_dtrees_dom_prop;
    simpl; intros.

  destruct (id_dec p l0); subst; simpl.
    remember (in_children_roots ch d) as R.
    destruct R; simpl.
      rewrite <- HeqR.
      destruct (id_dec l0 l0); try congruence.

      rewrite <- HeqR.
      destruct (id_dec l0 l0); try congruence.
      destruct (l_dec ch ch); try congruence.

    destruct (id_dec p l0); subst; try congruence.
      apply H.
      assert (p = l0 \/ p `in` dtrees_dom d) as J.
        clear - H0. fsetdec.
      destruct J as [J | J]; subst; auto; try congruence.

  contradict H. auto.
       
  assert (p `in` (dtree_dom d) \/ p `in` (dtrees_dom d0)) as J.
    fsetdec.
  apply orb_true_iff.
    destruct J as [J | J]. 
      left. apply H; auto.
      right. apply H0; auto.
Qed.

Lemma dtree_insert__in_dtree_dom: forall dt p ch,
  p `in` dtree_dom dt -> is_dtree_edge (dtree_insert dt p ch) p ch.
Proof.
  destruct dtree_insert__in_dtree_dom_mutrec as [H _].
  unfold dtree_insert__in_dtree_dom_prop in H. auto.
Qed.

Definition is_dtree_edge__in_dtree_dom_prop (dt:DTree) := 
forall p ch, is_dtree_edge dt p ch -> 
  p `in` dtree_dom dt /\ ch `in` dtree_dom dt.

Definition is_dtrees_edge__in_dtrees_dom_prop (dts:DTrees) := 
forall p ch, is_dtrees_edge dts p ch -> 
  p `in` dtrees_dom dts /\ ch `in` dtrees_dom dts.

Lemma in_children_roots__dtrees_dom: forall ch dts,
  in_children_roots ch dts -> ch `in` dtrees_dom dts.
Proof.
  induction dts; simpl; intros.
    congruence.

    destruct d.
    destruct (l_dec l0 ch); subst; simpl; eauto.
Qed.

Lemma is_dtree_edge__in_dtree_dom_mutrec :
  (forall dt, is_dtree_edge__in_dtree_dom_prop dt) *
  (forall dts, is_dtrees_edge__in_dtrees_dom_prop dts).
Proof.
  apply dtree_mutrec; 
    unfold is_dtree_edge__in_dtree_dom_prop, 
           is_dtrees_edge__in_dtrees_dom_prop;
    simpl; intros.

  destruct (id_dec p l0); subst; simpl.
    remember (in_children_roots ch d) as R.
    destruct R; simpl.
      symmetry in HeqR.
      apply in_children_roots__dtrees_dom in HeqR. fsetdec.

      apply H in H0. destruct H0 as [J1 J2]. auto.

    apply H in H0. destruct H0 as [J1 J2]. auto.

  congruence.

  apply orb_true_iff in H1.
  destruct H1 as [J | J]. 
    apply H in J. destruct J; auto.
    apply H0 in J. destruct J; auto.
Qed.

Lemma is_dtree_edge__in_dtree_dom: forall dt p ch, 
  is_dtree_edge dt p ch -> 
  p `in` dtree_dom dt /\ ch `in` dtree_dom dt.
Proof.
  destruct is_dtree_edge__in_dtree_dom_mutrec as [H1 _].
  unfold is_dtree_edge__in_dtree_dom_prop in H1.
  auto.
Qed.

Lemma dtree_insert__ch_in_dtree_dom: forall dt p ch,
  p `in` dtree_dom dt -> ch `in` dtree_dom (dtree_insert dt p ch).
Proof.
  intros.
  eapply is_dtree_edge__in_dtree_dom.
  eapply dtree_insert__in_dtree_dom; eauto.
Qed.

Lemma create_dtree_from_chain__is_dtree_edge__is_chain_edge: 
  forall p0 ch0 chain dt,
  (is_dtree_edge (create_dtree_from_chain dt chain) p0 ch0 -> 
   is_dtree_edge dt p0 ch0 \/is_chain_edge chain p0 ch0) /\
  (is_dtree_edge dt p0 ch0 \/ 
   (chain_connects_dtree dt chain /\ is_chain_edge chain p0 ch0) ->
   is_dtree_edge (create_dtree_from_chain dt chain) p0 ch0).
Proof.
  induction chain; simpl; intros.
    split; intros; tauto.
     
    destruct chain.
      tauto.

      split; intros.
        apply IHchain in H.
        destruct H as [H | H]; auto.
        apply dtree_insert__is_dtree_edge in H.
        destruct H as [H | [H [H1 H2]]]; subst; auto.

        apply IHchain.
        destruct H as [H | [H [[H1 H2] | H1]]]; subst.
          left. apply dtree_insert__is_dtree_edge; auto.
          left. apply dtree_insert__is_dtree_edge; auto.
          right. split; auto.
            destruct chain; simpl in *; auto.
            apply dtree_insert__ch_in_dtree_dom; auto.
Qed.

Definition dtree_insert__in_dtree_dom_prop' (dt:DTree) := 
forall i0 p ch,
  i0 `in` dtree_dom dt -> i0 `in` dtree_dom (dtree_insert dt p ch).

Definition dtrees_insert__in_dtrees_dom_prop' (dts:DTrees) := 
forall i0 p ch,
  i0 `in` dtrees_dom dts -> i0 `in` dtrees_dom (dtrees_insert dts p ch).

Lemma dtree_insert__in_dtree_dom_mutrec' :
  (forall dt, dtree_insert__in_dtree_dom_prop' dt) *
  (forall dts, dtrees_insert__in_dtrees_dom_prop' dts).
Proof.
  apply dtree_mutrec; 
    unfold dtree_insert__in_dtree_dom_prop', 
           dtrees_insert__in_dtrees_dom_prop';
    simpl; intros.

  destruct (id_dec p l0); subst; simpl.
    remember (in_children_roots ch d) as R.
    destruct R; simpl.
      fsetdec.
      fsetdec.

    assert (i0 = l0 \/ i0 `in` dtrees_dom d) as J.
      clear - H0. fsetdec.
    destruct J as [J | J]; subst; auto; try congruence.

  contradict H. auto.
       
  assert (i0 `in` (dtree_dom d) \/ i0 `in` (dtrees_dom d0)) as J.
    fsetdec.
  destruct J as [J | J]; eauto.
Qed.

Lemma dtree_insert__in_dtree_dom': forall dt i0 p ch,
  i0 `in` dtree_dom dt -> i0 `in` dtree_dom (dtree_insert dt p ch).
Proof.
  destruct dtree_insert__in_dtree_dom_mutrec' as [H _].
  unfold dtree_insert__in_dtree_dom_prop' in H. auto.
Qed.

Lemma create_dtree_from_chain__chain_connects_dtree: forall chain0 chain dt,
  chain_connects_dtree dt chain0 ->
  chain_connects_dtree (create_dtree_from_chain dt chain) chain0.
Proof.
  induction chain; simpl; intros; auto.
    destruct chain; auto.
    apply IHchain.    
    destruct chain0; simpl in *; intros; auto.
    destruct chain0; auto.
    eapply dtree_insert__in_dtree_dom'; eauto.
Qed.

Lemma fold_left_create_dtree_from_chain__is_dtree_edge__is_chain_edge: 
  forall p0 ch0 chains dt,
  (is_dtree_edge
    (fold_left
      (fun (acc : DTree) (elt : l * list id) =>
       let '(_, chain) := elt in create_dtree_from_chain acc chain)
     chains dt) p0 ch0 -> 
  (is_dtree_edge dt p0 ch0 \/
   exists l0, exists chain0, 
     In (l0, chain0) chains /\ is_chain_edge chain0 p0 ch0)) /\
  ((is_dtree_edge dt p0 ch0 \/
   exists l0, exists chain0, 
     In (l0, chain0) chains /\ chain_connects_dtree dt chain0 /\
     is_chain_edge chain0 p0 ch0) ->
   is_dtree_edge
    (fold_left
      (fun (acc : DTree) (elt : l * list id) =>
       let '(_, chain) := elt in create_dtree_from_chain acc chain)
     chains dt) p0 ch0).
Proof.
  induction chains; simpl; intros.
    split; intro J; auto.
      destruct J as [H | [l0 [chn0 [J1 J2]]]]; auto.
        inv J1.

    destruct a.
    destruct (IHchains (create_dtree_from_chain dt l1)) as [J1 J2].
    clear IHchains.
    split; intros J.
      apply J1 in J.      
      destruct J as [J | [l2 [chain2 [J3 J4]]]].
        apply create_dtree_from_chain__is_dtree_edge__is_chain_edge in J.
        destruct J as [J | J]; auto.
          right. exists l0. exists l1. auto.
        right. exists l2. exists chain2. auto.

      apply J2.
      destruct J as [J | [l2 [chain2 [J3 [J4 J5]]]]].
        left.
        apply create_dtree_from_chain__is_dtree_edge__is_chain_edge; auto.

        destruct J3 as [J3 | J3].
          inv J3. left.
          apply create_dtree_from_chain__is_dtree_edge__is_chain_edge; auto.

          right. exists l2. exists chain2. split; auto. split; auto.
            apply create_dtree_from_chain__chain_connects_dtree; auto.
Qed.

Lemma create_dtree__wf_dtree: forall f dt,
  create_dtree f = Some dt ->
  match getEntryLabel f, reachablity_analysis f with
  | Some root, Some rd =>
      let dt' := dom_analyze f in
      let b := bound_fdef f in
      let chains := compute_sdom_chains (dep_doms__nondep_doms b dt') rd in
      forall p0 ch0,
        (is_dtree_edge dt p0 ch0 -> 
         exists l0, exists chain0, 
           In (l0, chain0) chains /\ is_chain_edge chain0 p0 ch0) /\
        ((exists l0, exists chain0, 
           In (l0, chain0) chains /\ 
           chain_connects_dtree (DT_node root DT_nil) chain0 /\
           is_chain_edge chain0 p0 ch0) -> is_dtree_edge dt p0 ch0)
  | _, _ => False
  end.
Proof.
  unfold create_dtree.
  intros.
  remember (getEntryLabel f) as R.
  destruct R; tinv H.
  remember (reachablity_analysis f) as R.
  destruct R; inv H.
  intros.
  destruct (@fold_left_create_dtree_from_chain__is_dtree_edge__is_chain_edge
    p0 ch0 (compute_sdom_chains
             (dep_doms__nondep_doms (bound_fdef f) (dom_analyze f)) l1)
    (DT_node l0 DT_nil)) as [J1 J2].
  split; intros J; auto.
    apply J1 in J.
    destruct J as [J | J]; auto.
      simpl in J. destruct (id_dec p0 l0); tinv J.
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

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
