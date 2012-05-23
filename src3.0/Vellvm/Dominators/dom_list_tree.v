Require Import Coqlib.
Require Import Maps.
Require Import syntax.
Require Import infrastructure_props.
Require Import Metatheory.
Require Import Program.Tactics.
Require Import push_iter.

Inductive DTree : Set :=
| DT_node : positive -> DTrees -> DTree
with DTrees : Set :=
| DT_nil : DTrees
| DT_cons : DTree -> DTrees -> DTrees
.

Fixpoint list2tree hd tl := 
match tl with
| nil => DT_node hd DT_nil
| hd'::tl' => DT_node hd (DT_cons (list2tree hd' tl') DT_nil)
end.

Fixpoint dtree_insert dt parent child tl : DTree :=
match dt with
| DT_node l0 dts0 =>
    if positive_eq_dec parent l0
    then DT_node l0 (dtrees_insert dts0 child tl)
    else dt
end
with dtrees_insert (dts: DTrees) child tl : DTrees :=
match dts with
| DT_nil => DT_cons (list2tree child tl) DT_nil
| DT_cons dt0 dts0 =>
    let '(DT_node l0 _) := dt0 in
    if positive_eq_dec l0 child then 
      match tl with
      | child'::tl' => DT_cons (dtree_insert dt0 child child' tl') dts0
      | _ => dts
      end
    else DT_cons dt0 (dtrees_insert dts0 child tl)
end.

Fixpoint compute_sdom_chains_aux (res: positive -> LDoms.t)
  (bd: list positive) (acc: list (positive * list positive)) 
  : list (positive * list positive) :=
match bd with
| nil => acc
| l0 :: bd' =>
    match res l0 with
    | Some dts0 =>
        compute_sdom_chains_aux res bd' ((l0, (rev (l0 :: dts0)))::acc)
    | None => compute_sdom_chains_aux res bd' acc
    end
end.

Definition compute_sdom_chains (res: positive -> LDoms.t) rd
  : list (positive * list positive) :=
compute_sdom_chains_aux res rd nil.

Definition create_dtree_from_chain dt chain : DTree :=
match chain with
| p::(ch::chain') => dtree_insert dt p ch chain'
| _ => dt
end.

Definition create_dtree (pe:positive) (rd:list positive) 
  (res: positive -> LDoms.t) : DTree :=
let chains := compute_sdom_chains res rd in
fold_left 
  (fun acc elt => let '(_, chain):=elt in create_dtree_from_chain acc chain)
  chains (DT_node pe DT_nil).

Fixpoint in_children_roots child dts : bool :=
match dts with
| DT_nil => false
| DT_cons (DT_node l0 _) dts' =>
    if (positive_eq_dec l0 child) then true else in_children_roots child dts'
end.

Fixpoint is_dtree_edge dt parent child : bool :=
match dt with
| DT_node l0 dts0 =>
    if (positive_eq_dec parent l0) then
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

Fixpoint is_chain_edge (chain:list positive) p0 ch0 : Prop :=
match chain with
| p::((ch::_) as chain') => (p = p0 /\ ch = ch0) \/ is_chain_edge chain' p0 ch0
| _ => False
end.

Module PositiveDT <: UsualDecidableType with Definition t := positive.

  Definition t := positive.

  Definition eq := @eq positive.
  Definition eq_refl := @refl_equal positive.
  Definition eq_sym := @sym_eq positive.
  Definition eq_trans := @trans_eq positive.

  Definition eq_dec := positive_eq_dec.

End PositiveDT.

Module Import PositiveSetImpl : FSetExtra.WSfun PositiveDT :=
  FSetExtra.Make PositiveDT.

Notation positives :=
  PositiveSetImpl.t.

Module Import PositiveSetDecide := 
  CoqFSetDecide.WDecide_fun PositiveDT PositiveSetImpl.

Module Export PositiveSetNotin := FSetWeakNotin.Notin_fun PositiveDT PositiveSetImpl.

Module PositiveSetFacts := FSetFacts.WFacts_fun PositiveDT PositiveSetImpl.
Module PositiveSetProperties := 
  FSetProperties.WProperties_fun PositiveDT PositiveSetImpl.

Fixpoint dtree_dom (dt: DTree) : positives :=
match dt with
| DT_node l0 dts0 => union (singleton l0) (dtrees_dom dts0)
end
with dtrees_dom (dts: DTrees) : positives :=
match dts with
| DT_nil => PositiveSetImpl.empty
| DT_cons dt0 dts0 => union (dtree_dom dt0) (dtrees_dom dts0)
end.

Lemma dtrees_insert__in_children_roots: forall ch ch0 tl dts
  (Hin: in_children_roots ch dts = true),
  in_children_roots ch (dtrees_insert dts ch0 tl) = true.
Proof.
  induction dts as [|[]]; simpl; intro; try congruence.
    destruct_if.
      destruct_if.
        destruct tl; simpl.
          destruct_if.
          destruct_if. destruct_if.
        simpl. destruct_if.
      destruct_if.
        destruct tl; simpl.
          destruct_if.
          destruct_if; try congruence.
            destruct_if.
        simpl. 
        destruct_if.
          rewrite IHdts; auto.
Qed.

Lemma list2tree_spec: forall ch0 tl,
  exists dts, list2tree ch0 tl = DT_node ch0 dts.
Proof.
  destruct tl; simpl; eauto.
Qed.

Lemma inserted_in_children_roots: forall ch ch0 tl dts
  (Hnotin: in_children_roots ch dts = false)
  (Hin: in_children_roots ch (dtrees_insert dts ch0 tl) = true),
  ch = ch0.
Proof.
  induction dts as [|[]]; simpl; intros.
  Case "1".
    destruct (list2tree_spec ch0 tl) as [dts Heq].
    rewrite Heq in Hin.
    destruct_if; try solve [auto | congruence].
  Case "2".
    destruct_if.
    SCase "2.1".
      destruct_if; try congruence.
      destruct_if.
      destruct tl; simpl in *.
        destruct_if; try congruence.
        destruct_if; try congruence.
    SCase "2.2".
      destruct_if; try solve [congruence | auto].
Qed.

Lemma inserted_in_children_roots': forall ch0 tl dts,
  in_children_roots ch0 (dtrees_insert dts ch0 tl) = true.
Proof.
  induction dts as [|[]]; simpl; intros.
  Case "1".
    destruct (list2tree_spec ch0 tl) as [dts Heq].
    rewrite Heq.
    destruct_if; try solve [auto | congruence].
  Case "2".
    destruct_if.
    SCase "2.1".
      destruct_if; try congruence.
      destruct tl; simpl in *.
        destruct_if; try congruence.
        destruct_if; try congruence.
    SCase "2.2".
      simpl. destruct_if; try solve [congruence | auto].
Qed.

Definition get_dtree_root (dt:DTree) : positive :=
match dt with
| DT_node l0 _ => l0
end.

Definition dtree_insert__is_dtree_edge_prop (dt:DTree) :=
forall p ch tl p0 ch0,
  is_dtree_edge (dtree_insert dt p ch tl) p0 ch0 = true <->
  is_dtree_edge dt p0 ch0 = true \/ 
    (p = get_dtree_root dt /\ is_chain_edge (p::ch::tl) p0 ch0).

Definition dtrees_insert__is_dtrees_edge_prop (dts:DTrees) :=
forall ch tl p0 ch0,
  is_dtrees_edge (dtrees_insert dts ch tl) p0 ch0 = true <->
  is_dtrees_edge dts p0 ch0 = true \/ is_chain_edge (ch::tl) p0 ch0.

Lemma is_dtrees_egde_cons_elim: forall dt1 dts2 p ch
  (Hin: is_dtrees_edge (DT_cons dt1 dts2) p ch = true),
  is_dtree_edge dt1 p ch = true \/ is_dtrees_edge dts2 p ch = true.
Proof.
  simpl.
  intros.
  binvt Hin as J1 J2; auto.
Qed.

Lemma is_dtrees_egde_cons_intro: forall dt1 dts2 p ch
  (Hin: is_dtree_edge dt1 p ch = true \/ is_dtrees_edge dts2 p ch = true),
  is_dtrees_edge (DT_cons dt1 dts2) p ch = true.
Proof.
  simpl.
  intros. auto with datatypes v62.
Qed.

Lemma DT_nil_has_no_dtree_edges: forall p ch,
  is_dtrees_edge DT_nil p ch = false.
Proof. simpl. auto. Qed.

Lemma single_node_has_no_dtree_edges: forall hd p ch,
  is_dtree_edge (DT_node hd DT_nil) p ch = false.
Proof. intros. simpl. destruct_if. Qed.

Lemma is_dtree_edge_of_list2tree__is_chain_edge: forall p0 ch0 tl ch
  (Hin: is_dtree_edge (list2tree ch tl) p0 ch0 = true),
  is_chain_edge (ch::tl) p0 ch0.
Proof.
Local Opaque is_dtrees_edge.
  induction tl as [|hd tl']; simpl; intros.
    destruct_if; congruence.

    destruct_if.
      destruct (list2tree_spec hd tl') as [x Heq].
      rewrite Heq in H0.
      destruct (positive_eq_dec hd ch0); subst; auto.
        apply is_dtrees_egde_cons_elim in H0.
        destruct H0 as [H0 | H0].
          right. apply IHtl'. rewrite Heq. auto.

          rewrite DT_nil_has_no_dtree_edges in H0. congruence.
       apply is_dtrees_egde_cons_elim in H0.
       destruct H0 as [H0 | H0].
         right. apply IHtl'. auto.
         rewrite DT_nil_has_no_dtree_edges in H0. congruence.
Qed.

Lemma is_chain_edge__is_dtree_edge_of_list2tree: forall p0 ch0 tl ch
  (Hin: is_chain_edge (ch::tl) p0 ch0),
  is_dtree_edge (list2tree ch tl) p0 ch0 = true.
Proof.
  induction tl as [|hd tl']; simpl; intros.
    tauto.

    destruct (list2tree_spec hd tl') as [x Heq].
    rewrite Heq.
    destruct Hin as [[EQ1 EQ2] | Hin]; subst.
      destruct_if.
      destruct (positive_eq_dec ch0 ch0); try congruence.

      destruct (positive_eq_dec p0 ch); subst.
        destruct (positive_eq_dec hd ch0); subst; auto.
          apply is_dtrees_egde_cons_intro.
          left. rewrite <- Heq. apply IHtl'; auto.          

        apply is_dtrees_egde_cons_intro.
        left. rewrite <- Heq. apply IHtl'; auto.          
Transparent is_dtrees_edge.
Qed.

Lemma dtree_insert__is_dtree_edge_mutrec :
  (forall dt, dtree_insert__is_dtree_edge_prop dt) *
  (forall dts, dtrees_insert__is_dtrees_edge_prop dts).
Proof.
  apply dtree_mutrec;
    unfold dtree_insert__is_dtree_edge_prop, dtrees_insert__is_dtrees_edge_prop;
    intros; simpl.
  Case "DT_node".
    destruct_if.
    SCase "p0 = root".
      destruct_if.
      SSCase "p1 = root".
        remember (in_children_roots ch0 d) as R.
        destruct R; simpl.
        SSSCase "ch0 in d".
          destruct_if; try congruence.
          split; intro J; auto.
            rewrite dtrees_insert__in_children_roots; auto.

        SSSCase "ch0 notin d".
          destruct_if; try congruence.
          remember (in_children_roots ch0 (dtrees_insert d ch tl)) as R.
          destruct R; simpl.
          SSSSCase "ch0 in inserted".
            split; intro; auto.
              right.
              split; auto.
                left.
                split; auto.
                  symmetry in HeqR3.
                  eapply inserted_in_children_roots in HeqR3; eauto.
          SSSSCase "ch0 notin inserted".
            split; intro J.
            SSSSSCase "1".
              apply H in J.
              destruct J as [J | J]; auto.
            SSSSSCase "2".
              apply H. 
              destruct J as [J | [J1 [[EQ1 EQ2] |J2]]]; subst; auto.
                rewrite inserted_in_children_roots' in HeqR3. congruence.
      SSCase "p1 <> root".
        simpl.
        destruct_if; try congruence.
        split; intro J.
          SSSCase "1".
            apply H in J.
            destruct J as [J | J]; auto.
          SSSCase "2".
            apply H. 
            destruct J as [J | [J1 [[EQ1 EQ2] |J2]]]; subst; auto.
    SCase "p0 <> root".
      simpl.
      destruct_if.
      SSCase "p1 = root".
        split; intro J; auto.
          SSSCase "1".
          remember (in_children_roots ch0 d) as R.
          destruct R; simpl; auto.
            destruct J as [J | [J1 [[EQ1 EQ2] |J2]]]; subst; auto.
      SSCase "p1 <> root".
        split; intro J; auto.
          destruct J as [J | [J1 [[EQ1 EQ2] |J2]]]; subst; auto.

  Case "DT_nil".
    split; intros J.
      bdestruct J as J1 J2; try congruence.
        right.
        apply is_dtree_edge_of_list2tree__is_chain_edge; auto.
     destruct J as [J | J]; try congruence.

      rewrite is_chain_edge__is_dtree_edge_of_list2tree; auto.

  Case "DT_cons".
    destruct d as [l0 ?].
    destruct_if.
    SCase "l0 = ch".
      destruct tl; try tauto.
      SSCase "tl<>nil".
        split; intro J.
        SSSCase "1".
          apply is_dtrees_egde_cons_elim in J.
          destruct J as [J | J].
          SSSSCase "1.1".
            apply H in J. 
            destruct J as [J1 |[J2 J3]]; auto.
              rewrite J1. auto.
          SSSSCase "1.2".
            left. rewrite J. auto with datatypes v62.
        SSSCase "2".
          apply is_dtrees_egde_cons_intro.
          destruct J as [J | [[J1 J2] | J]]; subst.
          SSSSCase "2.1".
            binvt J as J1 J2; auto.
              left. apply H; auto.
          SSSSCase "2.2".
            left. apply H; simpl; auto.
          SSSSCase "2.3".
            left. apply H; simpl; auto.
    SCase "l0 <> ch".
        split; intro J.
        SSSCase "1".
          apply is_dtrees_egde_cons_elim in J.
          destruct J as [J | J].
          SSSSCase "1.1".
            left.
            apply is_dtrees_egde_cons_intro; auto.
          SSSSCase "1.2".
            apply H0 in J.
            destruct J as [J | J].
              left. apply is_dtrees_egde_cons_intro; auto.
              right. auto.
        SSSCase "2".
          apply is_dtrees_egde_cons_intro.
          destruct J as [J | J].    
          SSSSCase "2.1".
            binvt J as J1 J2; auto.
              right. apply H0; auto.
          SSSSCase "2.2".
            right. apply H0; auto.
Qed.

Lemma dtree_insert__is_dtree_edge : forall p ch tl p0 ch0 dt,
  is_dtree_edge (dtree_insert dt p ch tl) p0 ch0 = true <->
  is_dtree_edge dt p0 ch0 = true \/ 
  p = get_dtree_root dt /\ is_chain_edge (p::ch::tl) p0 ch0.
Proof.
  destruct (dtree_insert__is_dtree_edge_mutrec).
  unfold dtree_insert__is_dtree_edge_prop in *.
  eauto.
Qed.

Definition chain_connects_dtree dt (chain:list positive) : Prop :=
match chain with
| entry :: _ :: _ => entry = get_dtree_root dt
| _ => False
end.

Lemma create_dtree_from_chain__is_dtree_edge__is_chain_edge:
  forall p0 ch0 chain dt,
  (is_dtree_edge (create_dtree_from_chain dt chain) p0 ch0 = true ->
   is_dtree_edge dt p0 ch0 = true \/ is_chain_edge chain p0 ch0) /\
  (is_dtree_edge dt p0 ch0 = true \/
   (chain_connects_dtree dt chain /\ is_chain_edge chain p0 ch0) ->
   is_dtree_edge (create_dtree_from_chain dt chain) p0 ch0 = true).
Proof.
  intros.
Local Opaque is_chain_edge.
  destruct chain as [|p chain]; simpl; try tauto.
  destruct chain as [|ch chain]; simpl; try tauto.
  split; intros.
    apply dtree_insert__is_dtree_edge in H. tauto.
    apply dtree_insert__is_dtree_edge in H; auto.
Transparent is_chain_edge.
Qed.

Definition in_dtree_dom__in_dtree_insert_dom_prop (dt:DTree) :=
forall i0 p ch tl,
  In i0 (dtree_dom dt) -> In i0 (dtree_dom (dtree_insert dt p ch tl)).

Definition in_dtrees_dom__in_dtrees_insert_dom_prop (dts:DTrees) :=
forall i0 ch tl,
  In i0 (dtrees_dom dts) -> In i0 (dtrees_dom (dtrees_insert dts ch tl)).

Lemma in_dtree_dom__in_dtree_insert_dom_mutrec :
  (forall dt, in_dtree_dom__in_dtree_insert_dom_prop dt) *
  (forall dts, in_dtrees_dom__in_dtrees_insert_dom_prop dts).
Proof.
  apply dtree_mutrec;
    unfold in_dtree_dom__in_dtree_insert_dom_prop,
           in_dtrees_dom__in_dtrees_insert_dom_prop;
    simpl; intros.
  Case "DT_node".
  destruct (positive_eq_dec p0 p); subst; simpl; auto.
    apply PositiveSetFacts.union_iff in H0.
    apply PositiveSetFacts.union_iff. 
    destruct H0; auto.
  Case "DT_nil".
  contradict H. auto.
  Case "DT_cons".
  apply PositiveSetFacts.union_iff in H1.
  destruct d as [l0 ?].
  destruct_if; simpl.
    SCase "1".
    destruct tl; simpl.
      SSCase "1.1".
      apply PositiveSetFacts.union_iff. 
      destruct H1 as [H1 | H1]; auto.
      SSCase "1.2".
      apply PositiveSetFacts.union_iff. 
      destruct H1 as [H1 | H1]; auto.
        left. apply H; auto.
    SCase "2".
    apply PositiveSetFacts.union_iff. 
    destruct H1 as [H1 | H1]; auto.
Qed.

Lemma in_dtree_dom__in_dtree_insert_dom: forall dt i0 p ch tl,
  In i0 (dtree_dom dt) -> In i0 (dtree_dom (dtree_insert dt p ch tl)).
Proof.
  destruct in_dtree_dom__in_dtree_insert_dom_mutrec as [H _].
  unfold in_dtree_dom__in_dtree_insert_dom_prop in H. auto.
Qed.

Lemma dtree_insert__get_dtree_root: forall dt p ch tl,
  get_dtree_root dt = get_dtree_root (dtree_insert dt p ch tl).
Proof.
  destruct dt; simpl.
  intros.
  destruct_if; auto.
Qed.

Lemma create_dtree_from_chain__chain_connects_dtree: forall chain0 chain dt
  (H: chain_connects_dtree dt chain0),
  chain_connects_dtree (create_dtree_from_chain dt chain) chain0.
Proof.
  intros.
  destruct chain0 as [|p0 chain0]; auto.
  destruct chain0 as [|ch0 chain0]; auto.
  simpl in *.
  destruct chain as [|p chain]; auto.
  destruct chain as [|ch chain]; auto.
  subst. apply dtree_insert__get_dtree_root.
Qed.

Lemma fold_left_create_dtree_from_chain__is_dtree_edge__is_chain_edge:
  forall p0 ch0 chains dt,
  (is_dtree_edge
    (fold_left
      (fun (acc : DTree) (elt : positive * list positive) =>
       let '(_, chain) := elt in create_dtree_from_chain acc chain)
     chains dt) p0 ch0 = true ->
  (is_dtree_edge dt p0 ch0 = true \/
   exists l0, exists chain0,
     List.In (l0, chain0) chains /\ is_chain_edge chain0 p0 ch0)) /\
  ((is_dtree_edge dt p0 ch0 = true \/
   exists l0, exists chain0,
     List.In (l0, chain0) chains /\ chain_connects_dtree dt chain0 /\
     is_chain_edge chain0 p0 ch0) ->
   is_dtree_edge
    (fold_left
      (fun (acc : DTree) (elt : positive * list positive) =>
       let '(_, chain) := elt in create_dtree_from_chain acc chain)
     chains dt) p0 ch0 = true).
Proof.
  induction chains as [|[p l1] chains]; simpl; intros.
    split; intro J; auto.
      destruct J as [H | [l0 [chn0 [J1 J2]]]]; auto.

    destruct (IHchains (create_dtree_from_chain dt l1)) as [J1 J2].
    clear IHchains.
    split; intros J.
      apply J1 in J.
      destruct J as [J | [l2 [chain2 [J3 J4]]]].
        apply create_dtree_from_chain__is_dtree_edge__is_chain_edge in J.
        destruct J as [J | J]; auto.
          right. eauto. 
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

Lemma create_dtree__wf_dtree: forall pe rd res dt,
  create_dtree pe rd res = dt ->
  let chains := compute_sdom_chains res rd in
  forall p0 ch0,
    (is_dtree_edge dt p0 ch0 = true ->
      exists l0, exists chain0,
      List.In (l0, chain0) chains /\ is_chain_edge chain0 p0 ch0) /\
    ((exists l0, exists chain0,
      List.In (l0, chain0) chains /\
      chain_connects_dtree (DT_node pe DT_nil) chain0 /\
     is_chain_edge chain0 p0 ch0) -> is_dtree_edge dt p0 ch0 = true).
Proof.
  unfold create_dtree.
  intros. subst.
  destruct (@fold_left_create_dtree_from_chain__is_dtree_edge__is_chain_edge
    p0 ch0 (compute_sdom_chains res rd) (DT_node pe DT_nil)) as [J1 J2].
  split; intros J; auto.
    apply J1 in J.
    destruct J as [J | J]; auto.
      simpl in J. destruct (positive_eq_dec p0 pe); tinv J.
Qed.
