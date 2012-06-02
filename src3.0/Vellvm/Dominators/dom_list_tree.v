Require Import Coqlib.
Require Import Maps.
Require Import syntax.
Require Import infrastructure_props.
Require Import Metatheory.
Require Import Program.Tactics.
Require Import dom_tree.
Require Import push_iter.

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

Definition create_dtree (pe:positive) (rd:list positive) 
  (res: positive -> LDoms.t) : DTree :=
let chains := compute_sdom_chains res rd in
create_dtree_from_chains positive_eq_dec pe chains.

Lemma create_dtree__wf_dtree_aux: forall pe rd res dt,
  create_dtree pe rd res = dt ->
  let chains := compute_sdom_chains res rd in
  forall p0 ch0,
    (is_dtree_edge positive_eq_dec dt p0 ch0 = true ->
      exists l0, exists chain0,
      List.In (l0, chain0) chains /\ is_chain_edge chain0 p0 ch0) /\
    ((exists l0, exists chain0,
      List.In (l0, chain0) chains /\
      chain_connects_dtree (DT_node pe DT_nil) chain0 /\
     is_chain_edge chain0 p0 ch0) -> 
     is_dtree_edge positive_eq_dec dt p0 ch0 = true).
Proof.
  unfold create_dtree.
  intros. subst.
  apply create_dtree_from_chains__is_dtree_edge__is_chain_edge.
Qed.

Lemma compute_sdom_chains_aux_spec: forall 
  res l0 chain0 bd acc
  (H1: forall l0 chain0
       (Hin: List.In (l0, chain0) acc),
       exists dts0, 
         res l0 = Some dts0 /\
         chain0 = rev (l0 :: dts0))
  (H2: In (l0, chain0) (compute_sdom_chains_aux res bd acc)),
  (exists dts0,
    res l0 = Some dts0 /\
    chain0 = rev (l0 :: dts0)) /\ (In l0 bd \/ In (l0, chain0) acc).
Proof.
  induction bd; intros; eauto.
    simpl in H2.
    remember (res a) as R.
    destruct R.
    Case "1".
      apply IHbd in H2.
      SCase "1.1".
        destruct H2 as [J1 J2].
        split; auto.
          simpl. 
          destruct J2 as [J2 | J2]; auto.
          destruct_in J2; auto.
          inv J2. auto.
      SCase "1.s".
        intros. 
        destruct_in Hin; eauto.
        inv Hin. 
        exists l. split; auto. 
    Case "2".
      apply IHbd in H2; auto.
      destruct H2 as [J1 J2].
      split; auto.
        simpl. 
        destruct J2 as [J2 | J2]; auto.
Qed.

Lemma compute_sdom_chains_spec: forall res rd l0 chain,
  In (l0, chain) (compute_sdom_chains res rd) ->
  (exists dts0,
    res l0 = Some dts0 /\
    chain = rev (l0 :: dts0)) /\ In l0 rd.
Proof.
  intros.
  unfold compute_sdom_chains in H.
  apply compute_sdom_chains_aux_spec in H.
    destruct H as [H1 [H2 | H2]]; tauto.
    simpl. intros. tauto.
Qed.

Lemma compute_sdom_chains_aux_spec': forall res l0 dts0 rd acc
  (Hin: (res l0 = Some dts0 /\ In l0 rd) \/ In (l0, rev (l0 :: dts0)) acc),
  In (l0, rev (l0 :: dts0)) (compute_sdom_chains_aux res rd acc).
Proof.
  induction rd; simpl; intros.
    tauto.
  
    destruct Hin as [[Hsome [EQ | Hin]] | Hin]; subst.
      rewrite Hsome.
      apply IHrd; simpl; auto.

      destruct (res a); apply IHrd; simpl; auto.
      destruct (res a); apply IHrd; simpl; auto.
Qed.

Lemma compute_sdom_chains_spec': forall res rd l0 dts0,
  res l0 = Some dts0 -> In l0 rd ->
  In (l0, rev (l0 :: dts0)) (compute_sdom_chains res rd).
Proof.
  unfold compute_sdom_chains.
  intros.
  apply compute_sdom_chains_aux_spec'; auto.
Qed.

Lemma create_dtree__disjoint_children_dtree: forall pe rd res,
  disjoint_children_dtree positive_eq_dec (create_dtree pe rd res).
Proof.
  unfold create_dtree. intros.
  apply create_dtree_from_chains__disjoint_children_dtree.
Qed.

Require Import cfg.

Section create_dtree__wf_dtree.

Variable dts: PMap.t LDoms.t.
Variable psuccs: PTree.t (list positive).
Variable pe ni: positive.
Hypothesis Hanalyze: pdom_analyze psuccs pe ni = dts.
Variable res: positive -> LDoms.t.
Hypothesis Hquery: res = fun p:positive => PMap.get p dts.
Variable rd: list positive.
Hypothesis Hreach: forall p, PCfg.reachable psuccs pe p <-> List.In p rd.
Variable dt: @DTree positive.
Hypothesis Hdtree: create_dtree pe rd res = dt.
Hypothesis wf_entrypoints: in_cfg psuccs pe.
Definition entrypoints := (pe, LDoms.top) :: nil.
Definition predecessors := XPTree.make_predecessors psuccs.
Hypothesis wf_order: forall n (Hneq: n <> pe)
  (Hincfg: XPTree.in_cfg psuccs n),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.
Hypothesis Hok: (ni >= Termination.num_iters psuccs)%positive.
Hypothesis Hnopred: (XPTree.make_predecessors psuccs) ??? pe = nil.

Lemma dtree_edge_iff_idom: forall p0 ch0,
  is_dtree_edge positive_eq_dec dt p0 ch0 = true <-> 
    (PCfg.imm_domination psuccs pe p0 ch0 /\ PCfg.reachable psuccs pe ch0).
Proof.
  intros.
  assert (J:=Hdtree).
  apply create_dtree__wf_dtree_aux with (p0:=p0)(ch0:=ch0) in J; auto.
  destruct J as [Hdtree1 Hdtree2].
  split; intro J.
  Case "1".
    apply Hdtree1 in J.
    destruct J as [l0 [chain0 [Hin Hedge]]].
    apply compute_sdom_chains_spec in Hin.    
    destruct Hin as [[dts0 [Hin Heq]] ?]; subst chain0.
    assert (Sorted (PCfg.imm_domination psuccs pe) (rev (l0::dts0))) 
      as Hsort.
      subst. eapply IdomSorted.dom__imm_sorted; eauto.
    split.
    SCase "1.1".
      eapply chain_edge_sorted; eauto.
    SCase "1.2".
      simpl in Hedge.
      apply is_chain_edge__inv in Hedge.
      destruct Hedge as [Hin1 [Hin2 Hnnil]].
      apply rev_non_nil in Hnnil.      
      subst dts res.
      assert (Hreach0:=Hin).
      apply PDomProps.nonempty_is_reachable in Hreach0; auto.
      destruct_in Hin2.
        apply in_rev in Hin2.
        eapply PDomProps.in_dom__reachable; eauto.

        destruct_in Hin2.
  Case "2".
    apply Hdtree2.
    destruct J as [J1 J2].
    eapply IdomSorted.imm_dom__at_head in J1; eauto.
    destruct J1 as [dts0 J1].
    rewrite Hanalyze in J1.
    exists ch0. exists (rev (ch0::p0::dts0)).
    split.
    SCase "2.1".
      apply compute_sdom_chains_spec'; subst; auto.
        apply Hreach; auto.
    split.
    SCase "2.2".
      subst dts.
      apply IdomSorted.entry__at_last in J1; try congruence; auto.
      destruct J1 as [dts' J1].
      unfold PTree.elt in *.
      rewrite J1.
      rewrite_env ((ch0 :: dts') ++ pe :: nil).
      rewrite rev_unit.
      simpl. 
      case_eq (rev dts' ++ ch0 :: nil); auto.
        intro J. contradict J. auto with datatypes v62.
    SCase "2.3".
      simpl. simpl_env.
      apply is_chain_edge_tail; simpl; auto.
Qed.

Lemma create_dtree___reachable_dtree:
  PDProps.reachable_dtree psuccs pe dt.
Proof.
  subst dt.
  unfold create_dtree.
  apply PDProps.create_dtree_from_chains__reachable_dtree; auto.
    apply Forall_forall.
    intros [x xs] Hinx.
    apply compute_sdom_chains_spec in Hinx.
    destruct Hinx as [[dts0 [Hget Heq]] Hinrd]. 
    simpl.
    intros p Hinp. subst.
    simpl in Hinp.
    destruct_in Hinp.
      apply in_rev in Hinp.
      eapply PDomProps.in_dom__reachable; eauto.
    
      destruct_in Hinp.
      apply Hreach; auto.
Qed.

Lemma create_dtree__wf_dtree: PDProps.wf_dtree psuccs pe positive_eq_dec dt.
Proof.
  apply PDProps.create_dtree__wf_dtree; eauto using XPTree.no_preds__notin_succs.
  Case "1".
    intros p ch Hedge.
    assert (J:=Hdtree).
    apply create_dtree__wf_dtree_aux with (p0:=p)(ch0:=ch) in J; auto.
    destruct J as [Hdtree1 _].
    apply_clear Hdtree1 in Hedge.
    destruct Hedge as [l0 [chain0 [Hin Hedge]]].
    exists chain0.
    split; auto.
      apply compute_sdom_chains_spec in Hin.    
      destruct Hin as [[dts0 [Hin Heq]] ?]; subst chain0.
      subst. eapply IdomSorted.dom__imm_sorted; eauto.
  Case "2".
    subst dt. apply create_dtree__disjoint_children_dtree.
  Case "3".
    apply create_dtree___reachable_dtree.
Qed.

End create_dtree__wf_dtree.

