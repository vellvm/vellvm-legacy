Require Import Coqlib.
Require Import Metatheory.
Require Import infrastructure_props.
Require Import cfg.
Require Import Relations.Relation_Operators.

Section DTree.

Variable A:Set.
Hypothesis Hdec: forall x y:A, {x = y} + {x <> y}.

Inductive DTree : Set :=
| DT_node : A -> DTrees -> DTree
with DTrees : Set :=
| DT_nil : DTrees
| DT_cons : DTree -> DTrees -> DTrees
.

Fixpoint size_of_dtrees (dts:DTrees) : nat :=
match dts with
| DT_nil => O
| DT_cons _ dts' => S (size_of_dtrees dts')
end.

Fixpoint list2tree hd tl := 
match tl with
| nil => DT_node hd DT_nil
| hd'::tl' => DT_node hd (DT_cons (list2tree hd' tl') DT_nil)
end.

Fixpoint dtree_insert dt parent child tl : DTree :=
match dt with
| DT_node l0 dts0 =>
    if Hdec parent l0
    then DT_node l0 (dtrees_insert dts0 child tl)
    else dt
end
with dtrees_insert (dts: DTrees) child tl : DTrees :=
match dts with
| DT_nil => DT_cons (list2tree child tl) DT_nil
| DT_cons dt0 dts0 =>
    let '(DT_node l0 _) := dt0 in
    if Hdec l0 child then 
      match tl with
      | child'::tl' => DT_cons (dtree_insert dt0 child child' tl') dts0
      | _ => dts
      end
    else DT_cons dt0 (dtrees_insert dts0 child tl)
end.

Definition create_dtree_from_chain dt chain : DTree :=
match chain with
| p::(ch::chain') => dtree_insert dt p ch chain'
| _ => dt
end.

Fixpoint in_children_roots child dts : bool :=
match dts with
| DT_nil => false
| DT_cons (DT_node l0 _) dts' =>
    if (Hdec l0 child) then true else in_children_roots child dts'
end.

Fixpoint is_dtree_edge dt parent child : bool :=
match dt with
| DT_node l0 dts0 =>
    if (Hdec parent l0) then
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

Fixpoint is_chain_edge (chain:list A) p0 ch0 : Prop :=
match chain with
| p::((ch::_) as chain') => (p = p0 /\ ch = ch0) \/ is_chain_edge chain' p0 ch0
| _ => False
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

Definition get_dtree_root (dt:DTree) : A :=
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
      destruct (Hdec hd ch0); subst; auto.
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
      destruct (Hdec ch0 ch0); try congruence.

      destruct (Hdec p0 ch); subst.
        destruct (Hdec hd ch0); subst; auto.
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

Definition chain_connects_dtree dt (chain:list A) : Prop :=
match chain with
| entry :: _ :: _ => entry = get_dtree_root dt
| _ => False
end.

Lemma dtree_insert__get_dtree_root: forall dt p ch tl,
  get_dtree_root dt = get_dtree_root (dtree_insert dt p ch tl).
Proof.
  destruct dt; simpl.
  intros.
  destruct_if; auto.
Qed.

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
      (fun (acc : DTree) (elt : A * list A) =>
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
      (fun (acc : DTree) (elt : A * list A) =>
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

Lemma is_chain_edge_tail: forall p0 ch0 ls2 ls1 
  (Hintl: is_chain_edge ls2 p0 ch0),
  is_chain_edge (ls1 ++ ls2) p0 ch0.
Proof.
  induction ls1; simpl; intros; auto.
    case_eq (ls1 ++ ls2).
      intro J.
      apply app_eq_nil in J. 
      destruct J; subst; simpl in Hintl; auto.

      intros p l EQ.
      rewrite <- EQ. auto.
Qed.

Lemma chain_edge_sorted: forall R p0 ch0 ls1 (Hedge: is_chain_edge ls1 p0 ch0)
  (Hsort : Sorted R ls1), R p0 ch0.
Proof.
  induction 2; simpl in *.
    tauto.

    destruct l; try tauto.   
    destruct Hedge as [[EQ1 EQ2] | Hedge]; subst; auto.
      inv H. auto.
Qed.

Lemma is_chain_edge__inv: forall p0 ch0 l0 dts0
  (Hedge: is_chain_edge (dts0 ++ [l0]) p0 ch0),
  In p0 (dts0 ++ [l0]) /\ In ch0 (dts0 ++ [l0]) /\ dts0 <> nil.
Proof.
  induction dts0; simpl; intros.
    tauto.

    case_eq (dts0 ++ [l0]).
      intro Heq.
      destruct dts0; inv Heq.

      intros p1 l1 Heq.
      rewrite Heq in Hedge.
      destruct Hedge as [[EQ1 EQ2] | Hedge]; subst.
        simpl. 
        split; auto.
        split; auto.
          congruence.

        rewrite <- Heq in *.
        apply IHdts0 in Hedge.
        destruct Hedge as [J1 [J2 J3]].
        split; auto.
        split; auto.
          congruence.     
Qed.

Import AtomSet.
Import ListSet.

Fixpoint dtree_dom (dt: DTree) : set A :=
match dt with
| DT_node l0 dts0 => set_add Hdec l0 (dtrees_dom dts0)
end
with dtrees_dom (dts: DTrees) : set A :=
match dts with
| DT_nil => @empty_set A
| DT_cons dt0 dts0 => set_union Hdec (dtree_dom dt0) (dtrees_dom dts0)
end.

Fixpoint disjoint_dtrees (dts: DTrees): Prop :=
match dts with
| DT_nil => True
| DT_cons dt dts' => set_disjoint Hdec (dtree_dom dt) (dtrees_dom dts') /\
                     disjoint_dtrees dts'
end.

Inductive uniq_dtree : DTree -> Prop :=
| U_DT_node : forall p dts
            (Hnotin: ~ In p (dtrees_dom dts))
            (Hdisj: disjoint_dtrees dts)
            (Hwfdts: uniq_dtrees dts),
            uniq_dtree (DT_node p dts)
with uniq_dtrees : DTrees -> Prop :=
| U_DT_nil : uniq_dtrees DT_nil
| U_DT_cons : forall dt dts (Hwfdt: uniq_dtree dt) (Hwfdts: uniq_dtrees dts),
                 uniq_dtrees (DT_cons dt dts)
.

Fixpoint get_dtrees_roots dts : set A :=
match dts with
| DT_nil => @empty_set A
| DT_cons dt' dts' => set_add Hdec (get_dtree_root dt') (get_dtrees_roots dts')
end.

Fixpoint disjoint_dtrees_roots dts : Prop :=
match dts with
| DT_nil => True
| DT_cons dt' dts' => ~ In (get_dtree_root dt') (get_dtrees_roots dts') /\
                      disjoint_dtrees_roots dts'
end.

Inductive disjoint_children_dtree : DTree -> Prop :=
| Dj_DT_node : forall p dts             
               (Hwfdts: disjoint_children_dtrees dts),
               disjoint_children_dtree (DT_node p dts)
with disjoint_children_dtrees : DTrees -> Prop :=
| Dj_DT_nil : disjoint_children_dtrees DT_nil
| Dj_DT_cons : forall dt dts (Hwfdt: disjoint_children_dtree dt) 
               (Hwfdts: disjoint_children_dtrees dts)
               (Hdisj: disjoint_dtrees_roots (DT_cons dt dts)),
               disjoint_children_dtrees (DT_cons dt dts)
.

Definition dtree_is_sound (dt:DTree) (idom: A -> A -> Prop): Prop :=
  forall p ch (Hedge: is_dtree_edge dt p ch = true),
    exists chain, is_chain_edge chain p ch /\ 
    Sorted idom chain /\ NoDup chain.

Definition dtrees_is_sound (dts:DTrees) (idom: A -> A -> Prop) : Prop :=
  forall p ch (Hedge: is_dtrees_edge dts p ch = true),
    exists chain, is_chain_edge chain p ch /\ 
    Sorted idom chain /\ NoDup chain.

Fixpoint in_children (dt: DTree) dts : Prop :=
match dts with
| DT_nil => False
| DT_cons dt' dts' => dt = dt' \/ in_children dt dts'
end.

Require Import Dipaths.

Definition dvertexes (dt: DTree) : V_set := 
fun (v:Vertex) => let '(index n) := v in In n (dtree_dom dt).

Definition darcs (dt: DTree) : A_set := 
fun (arc:Arc) =>
  let '(A_ends (index n2) (index n1)) := arc in
  is_dtree_edge dt n1 n2 = true.

Definition dtree_walk (dt: DTree) (n:A) : Prop :=
  exists vl, exists al, 
    D_walk (dvertexes dt) (darcs dt) (index n) (index (get_dtree_root dt)) vl al.

Lemma DT_cons_hd_extends_darcs: forall l1 d dts (x : Arc)
  (Hinx: darcs (DT_node l1 dts) x), darcs (DT_node l1 (DT_cons d dts)) x.
Proof.
  intros.
  destruct x as [[a] [b]]. simpl in *.
  destruct_if.
    rewrite H0.
    destruct d.
    destruct_if.
      destruct_if.
      destruct_if.
  
      rewrite H1.
      destruct_if; auto with datatypes v62.
  
    rewrite H0. auto with datatypes v62.
Qed.

Lemma DT_cons_hd_extends_dvertexes: forall l1 d dts (x : Vertex)
  (Hinx: dvertexes (DT_node l1 dts) x), dvertexes (DT_node l1 (DT_cons d dts)) x.
Proof.
  intros.
  destruct x as [x]. simpl in *.
  apply set_add_elim in Hinx.
  destruct Hinx; subst.
    apply set_add_intro2; auto.
  
    apply set_add_intro1.
    apply set_union_intro; auto.
Qed.

Lemma DT_cons_tl_extends_dvertexes: forall l1 d dts (x : Vertex)
  (Hinx: dvertexes d x), dvertexes (DT_node l1 (DT_cons d dts)) x.
Proof.
  intros.
  destruct x as [x].
  simpl in *.
  apply set_add_intro1.
  apply set_union_intro; auto.
Qed.

Lemma DT_cons_tl_extends_darcs: forall l1 d dts (x : Arc)
  (Hinx: darcs d x), darcs (DT_node l1 (DT_cons d dts)) x.
Proof.
  intros.
  destruct x as [[a] [b]]. simpl in *.
  rewrite Hinx. 
  destruct_if.
  destruct d.
  destruct_if.
Qed.

Lemma get_dtree_root_in_dtree_dom: forall dt,
  In (get_dtree_root dt) (dtree_dom dt).
Proof.
  destruct dt; simpl.
  apply set_add_intro2; auto.
Qed.

Lemma dtree_child_walk__dtree_walk: forall l1 l2 dt dts 
  (Hinch : in_children dt dts)
  (Hwk : dtree_walk dt l2),
  dtree_walk (DT_node l1 dts) l2.
Proof.
  induction dts; simpl; intros.
    tauto.

    destruct Hinch as [Hinch | Hinch]; subst.
      destruct Hwk as [vl [al Hwk]].
      exists (vl++[index l1]).
      exists (al++[A_ends (index (get_dtree_root d)) (index l1)]).
      apply DWalk_append with (y:=index (get_dtree_root d)); auto.
        eapply D_walk_sub in Hwk; eauto.
         apply DT_cons_tl_extends_dvertexes.
         apply DT_cons_tl_extends_darcs.

        simpl.
        apply DW_step; simpl.
          constructor; simpl.
            apply set_add_intro2; auto.
          apply set_add_intro1; auto.
            apply set_union_intro. left.
            apply get_dtree_root_in_dtree_dom.

          destruct_if.
          destruct d. simpl.
          destruct_if.
          destruct_if. congruence.
 
       apply IHdts in Hinch; auto.
       destruct Hinch as [vl [al Hinch]].
       exists vl. exists al.
       simpl in *.
       eapply D_walk_sub in Hinch; eauto.
         apply DT_cons_hd_extends_dvertexes.
         apply DT_cons_hd_extends_darcs.
Qed.

Definition in_dtree_dom__is_dtree_walk_prop (dt:DTree) :=
  forall l0 (Hin: In l0 (dtree_dom dt)), dtree_walk dt l0.

Definition in_dtrees_dom__is_dtrees_walk_prop (dts:DTrees) :=
  forall l0 (Hin: In l0 (dtrees_dom dts)), 
  exists dt, in_children dt dts /\ dtree_walk dt l0.

Lemma in_dtree_dom__is_dtree_walk_mutrec :
  (forall dt, in_dtree_dom__is_dtree_walk_prop dt) *
  (forall dts, in_dtrees_dom__is_dtrees_walk_prop dts).
Proof.
  apply dtree_mutrec;
    unfold in_dtree_dom__is_dtree_walk_prop, in_dtrees_dom__is_dtrees_walk_prop;
    simpl; intros; try tauto.
  Case "DT_node".
    apply set_add_elim in Hin.
    destruct Hin as [Hin | Hin]; subst.
      exists V_nil. exists A_nil. simpl.
      constructor; auto.
        simpl. apply set_add_intro2; auto.

      apply H in Hin.
      destruct Hin as [dt [J1 J2]].
      eapply dtree_child_walk__dtree_walk; eauto.
  Case "DT_cons".
    apply set_union_elim in Hin.
    destruct Hin as [Hin | Hin]; eauto.
      apply H0 in Hin. 
      destruct Hin as [dt [J1 J2]].
      eauto.
Qed.

Lemma in_dtree_dom__is_dtree_walk: forall dt l0 (Hin: In l0 (dtree_dom dt)),
  dtree_walk dt l0.
Proof.
  intros.
  destruct in_dtree_dom__is_dtree_walk_mutrec as [J1 J2].
  apply J1; auto.
Qed.

Lemma in_dtrees_dom__is_dtree_walk: forall dts l0 (Hin: In l0 (dtrees_dom dts)),
  exists dt, in_children dt dts /\ dtree_walk dt l0.
Proof.
  intros.
  destruct in_dtree_dom__is_dtree_walk_mutrec as [J1 J2].
  apply J2; auto.
Qed.

Lemma in_children__in_children_roots: forall dt dts (Hin: in_children dt dts),
  in_children_roots (get_dtree_root dt) dts = true.
Proof.
  induction dts as [|[] dts]; simpl; intros; auto.
    destruct_if.
    destruct Hin as [Hin | HIn]; subst; simpl in *; auto.
Qed.

Fixpoint forall_parent_children (R:A -> A -> Prop) (p:A) (dts:DTrees) 
  : Prop :=
match dts with
| DT_nil => True
| DT_cons dt dts' => R p (get_dtree_root dt) /\ 
                     forall_parent_children R p dts'
end.

Lemma forall_parent_children__in_children: forall R p dt dts
  (Hforall: forall_parent_children R p dts)
  (Hin: in_children dt dts),
  R p (get_dtree_root dt).
Proof.
  induction dts; simpl; intros.
    tauto.
    destruct Hin as [Hin | Hin]; subst; tauto.
Qed.

Lemma in_children__forall_parent_children: forall (R:A->A->Prop) p dts
  (Hp: forall dt (Hin: in_children dt dts), R p (get_dtree_root dt)),
  forall_parent_children R p dts.
Proof.
  induction dts; simpl; intros; auto.
Qed.

Lemma in_children__is_dtree_edge: forall l0 dt dts (Hin : in_children dt dts),
  is_dtree_edge (DT_node l0 dts) l0 (get_dtree_root dt) = true.
Proof.
  induction dts as [|[] dts]; simpl; intros.
    tauto.

    destruct Hin as [Hin | Hin]; subst; simpl in *.
      repeat destruct_if.

      repeat destruct_if;
        rewrite IHdts; auto with datatypes v62.
Qed.

Lemma dtree_edge_sorted: forall R dt p ch
  (Hp : dtree_is_sound dt R) (Hedge: is_dtree_edge dt p ch = true),
  R p ch.
Proof.
  intros.
  apply Hp in Hedge.
  destruct Hedge as [chain [J1 [J2 J3]]].
  eapply chain_edge_sorted; eauto.
Qed.

Lemma DT_node_is_sound_inv: forall R l0 dts
  (Hp : dtree_is_sound (DT_node l0 dts) R),
  dtrees_is_sound dts R /\ forall_parent_children R l0 dts.
Proof.
  intros.
  unfold dtree_is_sound, dtrees_is_sound in *.
  split.
    intros. apply Hp. simpl.
    rewrite Hedge.
    destruct (Hdec p l0); subst; auto.
    destruct (in_children_roots ch dts); auto.

    apply in_children__forall_parent_children.
    intros dt Hin.
    apply in_children__is_dtree_edge with (l0:=l0) in Hin.
    eapply dtree_edge_sorted; eauto.
Qed.

Lemma DT_cons_is_sound_inv: forall idom dt dts
  (Hp : dtrees_is_sound (DT_cons dt dts) idom),
  dtree_is_sound dt idom /\ dtrees_is_sound dts idom.
Proof.
  unfold dtree_is_sound, dtrees_is_sound in *.
  intros.
  split; intros.
    apply Hp. apply is_dtrees_egde_cons_intro; auto.
    apply Hp. apply is_dtrees_egde_cons_intro; auto.
Qed.

Lemma dtrees_is_sound__dtree_is_sound: forall dt idom dts
  (H: dtrees_is_sound dts idom) (Hin: in_children dt dts),
  dtree_is_sound dt idom.
Proof.
  unfold dtree_is_sound, dtrees_is_sound in *.
  induction dts; simpl; intros.
    tauto.

    destruct Hin as [Hin | Hin]; subst.
      apply H. rewrite Hedge. auto.
 
      apply IHdts; auto.
        intros p0 ch0 Hedge0.
        apply H. rewrite Hedge0. auto with datatypes v62.
Qed.

Lemma notin_get_dtrees_roots__neq: forall a dt dts
  (Hnotin: ~ In a (get_dtrees_roots dts))
  (Hin: in_children dt dts),
  a <> get_dtree_root dt.
Proof.
  induction dts; simpl; intros.
    tauto.

    destruct Hin as [Hin | Hin]; subst.
      intro EQ. subst.
      apply Hnotin. apply set_add_intro2; auto.

      intro EQ. subst. 
      apply IHdts; auto.
        intro J. apply Hnotin. apply set_add_intro1; auto.
Qed.

Lemma dtree_walk__clos_refl_trans_idom: forall idom dt l1 (Hwk: dtree_walk dt l1)
  (Hsound: dtree_is_sound dt idom),
  (clos_refl_trans A idom) (get_dtree_root dt) l1.
Proof.
  intros.
  destruct Hwk as [vl [al Hwk]].
  remember (index l1) as v1.
  remember (index (get_dtree_root dt)) as ve.
  generalize dependent l1.
  generalize dependent (get_dtree_root dt).
  induction Hwk; simpl; intros; subst.
    inv Heqv1.
    apply rt_refl.

    destruct y as [y].
    apply rt_trans with (y:=y); eauto.
      apply rt_step.
      eapply dtree_edge_sorted in Hsound; eauto.
Qed.

Lemma dtree_walk__clos_trans_idom: forall idom dt a l1 dts 
  (Hwk: dtree_walk dt l1)
  (Hsound: dtree_is_sound (DT_node a dts) idom)
  (Hinch : in_children dt dts),
  (clos_trans A idom) a l1.
Proof.
  intros.
  apply DT_node_is_sound_inv in Hsound. destruct Hsound.
  apply dtree_walk__clos_refl_trans_idom with (idom:=idom )in Hwk; 
    eauto using dtrees_is_sound__dtree_is_sound.
  eapply step_clos_refl_trans__clos_trans; eauto.
    eapply forall_parent_children__in_children; eauto.
Qed.

End DTree.

Implicit Arguments dtree_insert [A].
Implicit Arguments dtrees_insert [A].
Implicit Arguments DTree [A].
Implicit Arguments DTrees [A].
Implicit Arguments DT_node [A].
Implicit Arguments DT_nil [A].
Implicit Arguments DT_cons [A].
Implicit Arguments create_dtree_from_chain [A].
Implicit Arguments is_dtree_edge [A].
Implicit Arguments is_dtrees_edge [A].
Implicit Arguments is_chain_edge [A].
Implicit Arguments chain_connects_dtree [A]. 
Implicit Arguments 
  fold_left_create_dtree_from_chain__is_dtree_edge__is_chain_edge [A].
Implicit Arguments get_dtree_root [A].
Implicit Arguments in_children_roots [A].
Implicit Arguments dtree_dom [A].
Implicit Arguments dtrees_dom [A].
Implicit Arguments in_children [A].
Implicit Arguments dtree_is_sound [A].
Implicit Arguments dtrees_is_sound [A].
Implicit Arguments disjoint_children_dtree [A].
Implicit Arguments disjoint_children_dtrees [A].
Implicit Arguments uniq_dtree [A].
Implicit Arguments uniq_dtrees [A].
Implicit Arguments forall_parent_children [A].
Implicit Arguments disjoint_dtrees [A].
Implicit Arguments disjoint_dtrees_roots [A].
Implicit Arguments dtree_walk [A].

Require Import Maps.

Module DTreeProps (T:TREE).

Module TCfg := Cfg(T).

Module XTree := More_Tree_Properties(T).

Section create_dtree__wf_dtree.

Variable succs: T.t (list T.elt).
Variable entry: T.elt.
Hypothesis Hdec: forall x y:T.elt, {x = y} + {x <> y}.

Inductive reachable_dtree : @DTree T.elt -> Prop :=
| Rd_DT_node : forall p dts
            (Hrd: TCfg.reachable succs entry p) 
            (Hwfdts: reachable_dtrees dts),
            reachable_dtree (DT_node p dts)
with reachable_dtrees : @DTrees T.elt -> Prop :=
| Rd_DT_nil : reachable_dtrees DT_nil
| Rd_DT_cons : forall dt dts (Hwfdt: reachable_dtree dt) 
                 (Hwfdts: reachable_dtrees dts),
                 reachable_dtrees (DT_cons dt dts)
.

Lemma reachable_dtree__reachable_root: forall d 
  (Hreach: reachable_dtree d),
  TCfg.reachable succs entry (get_dtree_root d).
Proof.
  intros. inv Hreach. simpl. auto.
Qed.

Lemma reachable_dtrees__reachable_root: forall dt dts
  (Hwfdts : reachable_dtrees dts) (Hinchs : in_children dt dts),
  TCfg.reachable succs entry (get_dtree_root dt).
Proof.
  induction 1; simpl; intros.
    tauto.

    destruct Hinchs as [EQ | Hinchs]; subst; auto.
      apply reachable_dtree__reachable_root; auto.
Qed.

Import AtomSet.
Import ListSet.

Definition in_dom_tree_is_reachable_prop (dt:DTree) :=
  forall (Hrd: reachable_dtree dt) x (Hp: In x (dtree_dom Hdec dt)), 
    TCfg.reachable succs entry x.

Definition in_dom_trees_is_reachable_prop (dts:DTrees) :=
  forall (Hrd: reachable_dtrees dts) x (Hp: In x (dtrees_dom Hdec dts)), 
    TCfg.reachable succs entry x.

Lemma in_dom_tree_is_reachable_mutrec :
  (forall dt, in_dom_tree_is_reachable_prop dt) *
  (forall dts, in_dom_trees_is_reachable_prop dts).
Proof.
  apply dtree_mutrec;
    unfold in_dom_tree_is_reachable_prop, in_dom_trees_is_reachable_prop;
    simpl; intros; inv Hrd.
  Case "NODE".
    unfold dtree_dom in Hp.
    apply set_add_elim in Hp.
    destruct Hp as [Hp | Hp]; subst; auto.
  Case "NIL".
    tauto.
  Case "CONS".
    unfold dtrees_dom in Hp.
    apply set_union_elim in Hp.
    destruct Hp as [Hp | Hp]; auto.
Qed.

Lemma inter_reachable_dtree_is_reachable: forall dt dts
  (Hwfdt : reachable_dtree dt) (Hwfdts : reachable_dtrees dts) (x : T.elt) 
  (Hinx : In x (set_inter Hdec (dtree_dom Hdec dt) (dtrees_dom Hdec dts))),
  TCfg.reachable succs entry x.
Proof.
  intros. 
  destruct in_dom_tree_is_reachable_mutrec as [J1 J2].
  unfold in_dom_tree_is_reachable_prop, in_dom_trees_is_reachable_prop in *.
  apply set_inter_elim in Hinx.
  destruct Hinx; eauto.
Qed.

Definition idom := TCfg.imm_domination succs entry.
Definition sdom := TCfg.strict_domination succs entry.

Inductive wf_dtree : @DTree T.elt -> Prop :=
| Wf_DT_node : forall p dts
               (Hrd: TCfg.reachable succs entry p) 
               (Hnotin: ~ In p (dtrees_dom Hdec dts))
               (Hdisj: disjoint_dtrees Hdec dts)
               (Hidom: forall_parent_children idom p dts)
               (Hwfdts: wf_dtrees dts),
               wf_dtree (DT_node p dts)
with wf_dtrees : @DTrees T.elt -> Prop :=
| Wf_DT_nil : wf_dtrees DT_nil
| Wf_DT_cons : forall dt dts 
               (Hwfdt: wf_dtree dt) 
               (Hwfdts: wf_dtrees dts),
               wf_dtrees (DT_cons dt dts)
.

Hypothesis entry_has_no_preds : forall a0
  (Hin: In entry (XTree.successors_list succs a0)),
  False.

Lemma dtree_walk__sdom: forall dt a l1 dts 
  (Hwk: dtree_walk Hdec dt l1)
  (Hsound: dtree_is_sound Hdec (DT_node a dts) idom)
  (Hinch : in_children dt dts),
  sdom a l1.
Proof.
  intros.
  apply TCfg.clos_trans_idom__sdom; auto.
  eapply dtree_walk__clos_trans_idom with (idom:=idom) in Hwk; eauto.
Qed.

Definition create_dtree__wf_dtree_prop (dt:DTree) :=
  forall (Hp: dtree_is_sound Hdec dt idom) (Hdj: disjoint_children_dtree Hdec dt)
    (Hrd: reachable_dtree dt), 
    wf_dtree dt.

Definition create_dtree__wf_dtrees_prop (dts:DTrees) :=
  forall (Hp: dtrees_is_sound Hdec dts idom) 
    (Hdj: disjoint_children_dtrees Hdec dts)
    (Hrd: reachable_dtrees dts)
    (Hidom: exists p, forall_parent_children idom p dts),
    wf_dtrees dts /\ disjoint_dtrees Hdec dts.

Lemma create_dtree__wf_dtree_mutrec :
  (forall dt, create_dtree__wf_dtree_prop dt) *
  (forall dts, create_dtree__wf_dtrees_prop dts).
Proof.
  apply dtree_mutrec;
    unfold create_dtree__wf_dtree_prop, create_dtree__wf_dtrees_prop;
    simpl; intros.
  Case "DT_node".
    assert (dtrees_is_sound Hdec d idom /\
            forall_parent_children idom a d) as Hp'.
      apply DT_node_is_sound_inv in Hp; auto.
    inv Hdj. inv Hrd.
    assert (exists p : T.elt, forall_parent_children idom p d) as Hsdom.
      exists a. tauto.
    constructor; try solve [auto | eapply H; eauto | tauto].
    SCase "1".
      destruct (In_dec Hdec a (dtrees_dom Hdec d)) as [Hin | Hnotin]; 
        auto.  
      elimtype False.
      apply in_dtrees_dom__is_dtree_walk in Hin.
      destruct Hin as [dt [Hinch Hwk]].
      destruct Hp' as [J1 J2].
      assert (sdom a a) as Hfalse.
        eapply dtree_walk__sdom with (a:=a) in Hwk; eauto.
      apply TCfg.sdom_isnt_refl in Hfalse; auto.

  Case "DT_nil".
    split; auto.
      constructor.
  Case "DT_cons".
    inv Hdj. inv Hrd.
    assert (Hp':=Hp).
    apply DT_cons_is_sound_inv in Hp'.   
    destruct Hp' as [Hp1 Hps2]. 
    assert (Hsd1:=Hp1). assert (Hsds2:=Hps2).
    destruct Hidom as [p [Hidom1 Hidoms2]].
    apply_clear H0 in Hps2; eauto. destruct Hps2 as [Huniqs Hdisjs].
    apply_clear H in Hp1. 
    split.
    SCase "uniq".
      constructor; eauto.
    SCase "disjoint".
      split; auto.
        split; intros x Hinx; tinv Hinx.
        elimtype False.
        assert (J:=Hinx).
        apply set_inter_elim in J.
        destruct J as [Hin1 Hin2].
        apply in_dtree_dom__is_dtree_walk in Hin1.
        apply in_dtrees_dom__is_dtree_walk in Hin2.
        destruct Hdisj as [Hnotin _].
        destruct Hin2 as [dt [Hinchs Hwk2]].
        assert (idom p (get_dtree_root dt)) as Hsdom2.
          eapply forall_parent_children__in_children; eauto.
        eapply dtree_walk__clos_refl_trans_idom in Hin1; eauto.
        assert (dtree_is_sound Hdec dt idom) as Hsd2.
          apply DT_cons_is_sound_inv in Hp.
          destruct Hp as [Hp1' Hp2'].
          eapply dtrees_is_sound__dtree_is_sound; eauto.
        eapply dtree_walk__clos_refl_trans_idom in Hwk2; eauto.
        assert (get_dtree_root d <> get_dtree_root dt) as Hneq.
          eapply notin_get_dtrees_roots__neq; eauto.
        assert (sdom (get_dtree_root d) (get_dtree_root dt) \/
                sdom (get_dtree_root dt) (get_dtree_root d)) as Hdec0.
          eapply TCfg.rt_idom__sdom_ordered; 
            eauto using inter_reachable_dtree_is_reachable.
        eapply TCfg.idom_injective in Hdec0; 
          eauto using reachable_dtrees__reachable_root,
                      reachable_dtree__reachable_root.
Qed.

Lemma create_dtree__wf_dtree: forall (dt:DTree) 
  (Hp: dtree_is_sound Hdec dt idom) (Hdj: disjoint_children_dtree Hdec dt)
  (Hrd: reachable_dtree dt), 
  wf_dtree dt.
Proof.
  intros.
  destruct create_dtree__wf_dtree_mutrec as [J1 J2].
  unfold create_dtree__wf_dtree_prop in J1; auto.
Qed.

Definition wf_dtree__uniq_dtree_prop (dt:DTree) :=
  forall (Hp: wf_dtree dt), uniq_dtree Hdec dt.

Definition wf_dtree__uniq_dtrees_prop (dts:DTrees) :=
  forall (Hp: wf_dtrees dts), uniq_dtrees Hdec dts.

Lemma wf_dtree__uniq_dtree_mutrec :
  (forall dt, wf_dtree__uniq_dtree_prop dt) *
  (forall dts, wf_dtree__uniq_dtrees_prop dts).
Proof.
  apply dtree_mutrec;
    unfold wf_dtree__uniq_dtree_prop, wf_dtree__uniq_dtrees_prop;
    simpl; intros; inv Hp; constructor; auto.
Qed.

Lemma wf_dtree__wf_dtree: forall (dt:DTree) (Hp: wf_dtree dt),
  uniq_dtree Hdec dt.
Proof.
  intros.
  destruct wf_dtree__uniq_dtree_mutrec as [J1 J2].
  unfold wf_dtree__uniq_dtree_prop in J1; auto.
Qed.

End create_dtree__wf_dtree.

End DTreeProps.
