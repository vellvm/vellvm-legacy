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
fold_left 
  (fun acc elt => 
   let '(_, chain):=elt in create_dtree_from_chain positive_eq_dec acc chain)
  chains (DT_node pe DT_nil).

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
  destruct (fold_left_create_dtree_from_chain__is_dtree_edge__is_chain_edge
    positive_eq_dec p0 ch0 (compute_sdom_chains res rd) 
    (DT_node pe DT_nil)) 
    as [J1 J2].
  split; intros J; auto.
    apply J1 in J.
    destruct J as [J | J]; auto.
      simpl in J. destruct (positive_eq_dec p0 pe); tinv J.
Qed.

Lemma compute_sdom_chains_aux_spec: forall 
  res l0 chain0 bd acc
  (H1: forall l0 chain0
       (Hin: List.In (l0, chain0) acc),
       exists dts0, 
         res l0 = Some dts0 /\
         chain0 = rev (l0 :: dts0))
  (H2: In (l0, chain0) (compute_sdom_chains_aux res bd acc)),
  exists dts0,
    res l0 = Some dts0 /\
    chain0 = rev (l0 :: dts0).
Proof.
  induction bd; intros; eauto.
    simpl in H2.
    remember (res a) as R.
    destruct R; eauto.
    apply IHbd in H2; auto.
    intros. 
    destruct_in Hin; eauto.
    inv Hin. 
    exists l. split; auto. 
Qed.

Lemma compute_sdom_chains_spec: forall res rd l0 chain,
  In (l0, chain) (compute_sdom_chains res rd) ->
  exists dts0,
    res l0 = Some dts0 /\
    chain = rev (l0 :: dts0).
Proof.
  intros.
  unfold compute_sdom_chains in H.
  eapply compute_sdom_chains_aux_spec in H; eauto.
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

Section create_dtree__wf_dtree.

Variable dts: PMap.t LDoms.t.
Variable psuccs: PTree.t (list positive).
Variable pe: positive.
Hypothesis Hanalyze: pdom_analyze psuccs pe = dts.
Variable res: positive -> LDoms.t.
Hypothesis Hquery: res = fun p:positive => PMap.get p dts.
Variable rd: list positive.
Hypothesis Hreach: forall p, PCfg.reachable psuccs pe p -> List.In p rd.
Variable dt: @DTree positive.
Hypothesis Hdtree: create_dtree pe rd res = dt.
Hypothesis wf_entrypoints: in_cfg psuccs pe.
Definition entrypoints := (pe, LDoms.top) :: nil.
Definition predecessors := XPTree.make_predecessors psuccs.
Hypothesis wf_order: forall n (Hneq: n <> pe)
  (Hincfg: XPTree.in_cfg psuccs n),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.
Hypothesis Hok: pdom_analysis_is_successful psuccs pe.
Hypothesis Hnopred: (XPTree.make_predecessors psuccs) ??? pe = nil.

Lemma create_dtree__wf_dtree: forall p0 ch0,
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
    destruct Hin as [dts0 [Hin Heq]]; subst chain0.
    assert (Sorted (PCfg.imm_domination psuccs pe) (rev (l0::dts0))) 
      as Hsort.
      subst. apply IdomSorted.dom__imm_sorted; auto.
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
      apply UnreachableDoms.nonempty_is_reachable in Hreach0; auto.
      destruct_in Hin2.
        apply in_rev in Hin2.
        eapply DomsInParents.in_dom__reachable; eauto.

        destruct_in Hin2.
  Case "2".
    apply Hdtree2.
    destruct J as [J1 J2].
    apply IdomSorted.imm_dom__at_head in J1; auto.
    destruct J1 as [dts0 J1].
    rewrite Hanalyze in J1.
    exists ch0. exists (rev (ch0::p0::dts0)).
    split.
    SCase "2.1".
      apply compute_sdom_chains_spec'; subst; auto.
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

End create_dtree__wf_dtree.

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
with dtrees_dom (dts: @DTrees positive) : positives :=
match dts with
| DT_nil => PositiveSetImpl.empty
| DT_cons dt0 dts0 => union (dtree_dom dt0) (dtrees_dom dts0)
end.

Definition in_dtree_dom__in_dtree_insert_dom_prop (dt:DTree) :=
forall i0 p ch tl,
  In i0 (dtree_dom dt) -> 
  In i0 (dtree_dom (dtree_insert positive_eq_dec dt p ch tl)).

Definition in_dtrees_dom__in_dtrees_insert_dom_prop (dts:DTrees) :=
forall i0 ch tl,
  In i0 (dtrees_dom dts) -> 
  In i0 (dtrees_dom (dtrees_insert positive_eq_dec dts ch tl)).

Lemma in_dtree_dom__in_dtree_insert_dom_mutrec :
  (forall dt, in_dtree_dom__in_dtree_insert_dom_prop dt) *
  (forall dts, in_dtrees_dom__in_dtrees_insert_dom_prop dts).
Proof.
  apply dtree_mutrec;
    unfold in_dtree_dom__in_dtree_insert_dom_prop,
           in_dtrees_dom__in_dtrees_insert_dom_prop;
    simpl; intros.
  Case "DT_node".
  destruct (positive_eq_dec p a); subst; simpl; auto.
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
  In i0 (dtree_dom dt) -> 
  In i0 (dtree_dom (dtree_insert positive_eq_dec dt p ch tl)).
Proof.
  destruct in_dtree_dom__in_dtree_insert_dom_mutrec as [H _].
  unfold in_dtree_dom__in_dtree_insert_dom_prop in H. auto.
Qed.

