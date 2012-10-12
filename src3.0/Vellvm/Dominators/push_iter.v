Require Import Coqlib.
Require Import Iteration.
Require Import Maps.
Require Import syntax.
Require Import infrastructure_props.
Require Import Metatheory.
Require Import Program.Tactics.
Require Import dom_libs.
Require Import dfs.

(* When the Kildall's algorithm propogates, it ``pushes'' data from a node to its
   successors. *)
Module Weak_Succ_Dataflow_Solver (NS: PNODE_SET) (L: LATTICEELT).

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
      let m := start_state_in rem in 
      PMap.set n (fst (L.lub m ?? n v)) m
  end.

Definition start_state :=
  mkstate (start_state_in entrypoints) (NS.initial successors).

(** [propagate_succ] corresponds, in the pseudocode,
  to the body of the [for] loop iterating over all successors. *)

Definition propagate_succ (s: state) (out: L.t) (n: positive) :=
  let oldl := s.(st_in) ?? n in
  let '(newl, changed) := L.lub oldl out in
  if changed
  then mkstate (PMap.set n newl s.(st_in)) (NS.add n s.(st_wrk))
  else s.

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

Definition fixpoint num_iterations : option (PMap.t L.t) :=
  PrimIter.iter _ _ step num_iterations start_state.

End Kildall.

End Weak_Succ_Dataflow_Solver.

(***************************************************)
(* Instantiate Weak_Succ_Dataflow_Solver for computing dominators:
   1) a merge function for nodes sorted by less-than
   2) a worklist that always picks maximal node. *)

Module LDoms := Doms (MergeLt).
Module DomDS := Weak_Succ_Dataflow_Solver (PNodeSetMax) (LDoms).
Module DomMap := LATTICEELT_MAP (LDoms).

(***************************************************)
(* Properties of propagate_succ_list *)

Lemma propagate_succ_list_st_in_aux: forall out sc st2 scs st1 (Hnotin: ~ In sc scs)
  (Heq: (DomDS.st_in st1) ?? sc = (DomDS.st_in st2) ?? sc),
  (DomDS.st_in (DomDS.propagate_succ_list st1 out scs)) ?? sc = 
    (DomDS.st_in st2) ?? sc.
Proof.
  induction scs as [|sc' scs' IHscs']; simpl; intros; auto.
    rewrite IHscs'; auto.
    unfold DomDS.propagate_succ.
    destruct_let. destruct_if. simpl.
    rewrite PMap.gso; auto.
Qed.

Lemma propagate_succ_list_st_in: forall out sc scs st (Hnotin: ~ In sc scs),
  (DomDS.st_in (DomDS.propagate_succ_list st out scs)) ?? sc = 
    (DomDS.st_in st) ?? sc.
Proof. 
  intros. apply propagate_succ_list_st_in_aux; auto.
Qed.

Lemma propagate_succ_incr_worklist:
  forall st out n x,
  PNodeSetMax.In x st.(DomDS.st_wrk) -> 
  PNodeSetMax.In x (DomDS.propagate_succ st out n).(DomDS.st_wrk).
Proof.
  intros. unfold DomDS.propagate_succ.
  destruct_let. destruct_if. simpl. 
  rewrite PNodeSetMax.add_spec. auto.
Qed.

Lemma propagate_succ_list_incr_worklist:
  forall out scs st x,
  PNodeSetMax.In x st.(DomDS.st_wrk) -> 
  PNodeSetMax.In x (DomDS.propagate_succ_list st out scs).(DomDS.st_wrk).
Proof.
  induction scs; simpl; intros.
  auto.
  apply IHscs. apply propagate_succ_incr_worklist. auto.
Qed.

Lemma propagate_succ_bot_inv: forall st out sc n
  (Hnone: (DomDS.st_in (DomDS.propagate_succ st out sc)) ?? n = None),
  (DomDS.st_in st) ?? n = None.
Proof.
  unfold DomDS.propagate_succ.
  intros.
  destruct_let. destruct_if; auto.
    destruct (positive_eq_dec sc n); subst.
      rewrite PMap.gss in H0.
      rewrite PMap.gss.
      subst.
      eapply LDoms.lub_bot_invl; eauto.

      rewrite PMap.gso in H0; auto.
      rewrite PMap.gso; auto.
Qed.

Lemma propagate_succ_nonbot_inv: forall n sc st out 
  (Hacc: (DomDS.st_in st) ?? n <> None),
  (DomDS.st_in (DomDS.propagate_succ st out sc)) ?? n <> None.
Proof.
  intros.
  intro J.
  apply propagate_succ_bot_inv in J. auto.
Qed.

Lemma propagate_succ_list_nonbot_inv: forall n scs st out 
  (Hacc: (DomDS.st_in st) ?? n <> None),
  (DomDS.st_in (DomDS.propagate_succ_list st out scs)) ?? n <> None.
Proof.
  induction scs as [|sc' scs' IHscs']; simpl; intros;
    eauto using propagate_succ_nonbot_inv.
Qed.

Lemma propagate_succ_nonbot: forall (sc : positive) (st : DomDS.state)
  (out : option (list positive)) (Hnonbot : out <> None),
  (DomDS.st_in (DomDS.propagate_succ st out sc)) ?? sc <> None.
Proof.
  intros.
  unfold DomDS.propagate_succ.
  destruct_let. destruct_if; simpl.
    symmetry in HeqR.
    rewrite PMap.gss.
    eapply LDoms.lub_nonbot_spec in HeqR; eauto.

    eapply LDoms.Lub_unchanged_rnonbot__lnonbot; eauto.
Qed.

Lemma propagate_succ_list_nonbot_aux: forall sc scs scs2 scs1 st out
  (Hnonbot: out <> None) (Hin: In sc scs2) (Heq: scs = scs1 ++ scs2)
  (Hacc: forall a, In a scs1 -> (DomDS.st_in st) ?? a <> None),
  (DomDS.st_in (DomDS.propagate_succ_list st out scs2)) ?? sc <> None.
Proof.
  induction scs2 as [|sc2' scs2' IHscs2']; simpl; intros.
    tauto.
    
    destruct Hin as [Hin | Hin]; subst. 
      apply propagate_succ_list_nonbot_inv.
        apply propagate_succ_nonbot; auto.

      apply IHscs2' with (scs2:=scs1++[sc2']); auto.
        simpl_env. auto.

        intros a Hina.     
        destruct (positive_eq_dec sc2' a); subst.
          apply propagate_succ_nonbot; auto.

          apply propagate_succ_nonbot_inv.
          destruct_in Hina; auto.
          simpl in Hina.
          destruct Hina as [Hina | Hina]; try tauto.
Qed.

Lemma propagate_succ_list_nonbot: forall sc scs st out
  (Hnonbot: out <> None) (Hin: In sc scs),
  (DomDS.st_in (DomDS.propagate_succ_list st out scs)) ?? sc <> None.
Proof.
  intros. apply propagate_succ_list_nonbot_aux with (scs:=scs)(scs1:=nil); auto.
Qed.

Lemma propagate_succ_records_changes:
  forall st out n s,
  let st' := DomDS.propagate_succ st out n in
  PNodeSetMax.In s st'.(DomDS.st_wrk) \/ 
  st'.(DomDS.st_in)??s = st.(DomDS.st_in)??s.
Proof.
  simpl. intros. unfold DomDS.propagate_succ.
  destruct_let. destruct_if.
  case (positive_eq_dec s n); intro.
    subst s. left. simpl. rewrite PNodeSetMax.add_spec. auto.
    right. simpl. apply PMap.gso. auto.
Qed.

Lemma propagate_succ_list_records_changes:
  forall out scs st s,
  let st' := DomDS.propagate_succ_list st out scs in
  PNodeSetMax.In s st'.(DomDS.st_wrk) \/ 
  st'.(DomDS.st_in)??s = st.(DomDS.st_in)??s.
Proof.
  induction scs; simpl; intros.
  right; auto.
  elim (propagate_succ_records_changes st out a s); intro.
  left. apply propagate_succ_list_incr_worklist. auto.
  rewrite <- H. auto.
Qed.

Lemma propagate_succ_spec:
  forall st out n,
  let st' := DomDS.propagate_succ st out n in
  (LDoms.eq st'.(DomDS.st_in)??n (fst (LDoms.lub st.(DomDS.st_in)??n out))) /\
  (forall s, n <> s -> st'.(DomDS.st_in)??s = st.(DomDS.st_in)??s).
Proof.
  unfold DomDS.propagate_succ; intros; simpl.
  destruct_let. 
  destruct_if; simpl.
    split.
      rewrite PMap.gss. apply LDoms.eq_refl.
      intros. rewrite PMap.gso; auto.

    split; auto.
      symmetry in HeqR.
      assert (J:=HeqR).
      apply LDoms.lub_unchanged_eq_left in J. subst.
      apply LDoms.eq_refl.
Qed.

Lemma propagate_succ_records_unchanges:
  forall st out n st' (Heq: st' = DomDS.propagate_succ st out n) bd
  (H: DomMap.eq bd st.(DomDS.st_in) st'.(DomDS.st_in)) (Hin: In n bd),
  st.(DomDS.st_wrk) = st'.(DomDS.st_wrk).
Proof.
  unfold DomDS.propagate_succ.
  intros. 
  case_eq (LDoms.lub (DomDS.st_in st) ?? n out).
  intros newl ch Heq'.
  rewrite Heq' in *.
  destruct_if; subst; auto.
  simpl in *.
  apply LDoms.lub_changed_neq_left in Heq'.
  assert (J:=H n).
  rewrite PMap.gss in J.
  rewrite J in Heq'; auto.
  congruence.
Qed.

(* Properties of DomMap.in_incr *)
Lemma DomMap_eq_incr_incr__eq_eq: forall bd dm1 dm2 dm3 (Heq13: DomMap.eq bd dm1 dm3)
  (Hincr12: DomMap.in_incr dm1 dm2) (Hincr23: DomMap.in_incr dm2 dm3),
  DomMap.eq bd dm1 dm2 /\ DomMap.eq bd dm2 dm3.
Proof.
  intros.
  split.
    intros x Hinx.
    apply Heq13 in Hinx.
    assert (J1:=Hincr12 x).
    assert (J2:=Hincr23 x).
    unfold LDoms.eq.
    destruct (dm2 ?? x) as [x2|]; simpl in *.
      destruct (dm1 ?? x) as [x1|]; simpl in *.
        destruct (dm3 ?? x) as [x3|]; simpl in *; try tauto.
          inv Hinx. 
          eapply sublist_antisymm in J1; subst; eauto.
        destruct (dm3 ?? x) as [x3|]; simpl in *; try tauto.
          inv Hinx. 
      destruct (dm1 ?? x) as [x1|]; simpl in *; try tauto.

    intros x Hinx.
    apply Heq13 in Hinx.
    assert (J1:=Hincr12 x).
    assert (J2:=Hincr23 x).
    unfold LDoms.eq.
    destruct (dm3 ?? x) as [x3|]; simpl in *.
      destruct (dm1 ?? x) as [x1|]; simpl in *.
        destruct (dm2 ?? x) as [x2|]; simpl in *; try tauto.
          inv Hinx. 
          eapply sublist_antisymm in J1; subst; eauto.
        destruct (dm2 ?? x) as [x2|]; simpl in *; try tauto.
          inv Hinx. 
      destruct (dm2 ?? x) as [x1|]; simpl in *; try tauto.
Qed.

(***************************************************)
(* All elements in a worklist must be in the CFG. *)

Module WorklistProps. Section WorklistProps.

Variable successors: PTree.t (list positive).
Definition in_cfg := XPTree.in_cfg successors.

Definition wf_state (st: DomDS.state) : Prop :=
 forall n (Hinwrk: PNodeSetMax.In n st.(DomDS.st_wrk)), in_cfg n.

Lemma wf_state_pick_in_cfg: forall st (WF : wf_state st) n rem
  (Hpick : Some (n, rem) = PNodeSetMax.pick (DomDS.st_wrk st)),
  in_cfg n.
Proof.
  intros.
  symmetry_ctx.
  apply PNodeSetMax.pick_in in Hpick.
  apply WF in Hpick; auto.
Qed.

Lemma propagate_succ_list_wf_state_aux: forall (p : PositiveSet.elt) 
  out scs (st : DomDS.state) (Hwf : wf_state st)
  (Hinscs: forall sc, In sc scs -> In sc successors ??? p),
  wf_state (DomDS.propagate_succ_list st out scs).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs; auto.
      unfold DomDS.propagate_succ.
      destruct_let. 
      destruct_if; auto.
        intros n Hinwrk. simpl in *.
        destruct (positive_eq_dec n a); subst.
          eapply XPTree.in_succ__in_cfg; eauto.
          apply PositiveSet.add_3 in Hinwrk; auto.
Qed.

Lemma propagate_succ_list_wf_state: forall st (Hwf: wf_state st) rem p 
  (Hpick: PNodeSetMax.pick (DomDS.st_wrk st) = Some (p, rem)),
  wf_state 
    (DomDS.propagate_succ_list 
      {| DomDS.st_in := DomDS.st_in st; DomDS.st_wrk := rem |}
      (LDoms.transfer p (DomDS.st_in st) ?? p) successors ??? p).
Proof.
  intros.
  assert 
    (wf_state {| DomDS.st_in := DomDS.st_in st; DomDS.st_wrk := rem |}) 
    as Hwf'.
    intros n Hin. simpl in *.
    apply PNodeSetMax.pick_some with (n':=n) in Hpick.
    apply Hwf. tauto.
  apply PNodeSetMax.pick_in in Hpick.
  apply Hwf in Hpick.
  eapply propagate_succ_list_wf_state_aux; eauto.
Qed.

Lemma step_wf_state: forall (st st': DomDS.state)
  (Hstep: DomDS.step successors LDoms.transfer st = inr st'),
  wf_state st -> wf_state st'.
Proof.
  unfold DomDS.step.
  intros.
  remember (PNodeSetMax.pick (DomDS.st_wrk st)) as R.
  destruct R as [ [n rem] | ]; inv Hstep.
  apply propagate_succ_list_wf_state; auto.
Qed.

Lemma in_parents_of_tree__in_initial: forall p
  (Hin : In p (XPTree.parents_of_tree successors)),
  PNodeSetMax.In p (PNodeSetMax.initial successors).
Proof.
  intros.
  apply XPTree.parents_of_tree__in_successors in Hin.
  destruct_conjs.
  eapply PNodeSetMax.initial_spec; eauto.
Qed.

Variable entrypoints: list (positive * LDoms.t).

Lemma entrypoints_wf_state:
  wf_state (DomDS.mkstate (DomDS.start_state_in entrypoints) 
                          (PNodeSetMax.initial successors)).
Proof.
  intros x Hin.
  simpl in *.
  apply PNodeSetMax.initial_spec' in Hin.
  apply XPTree.parents_of_tree__in_successors in Hin.
  apply XPTree.in_parents_of_tree__in_cfg; auto.
Qed.

End WorklistProps. End WorklistProps.

(*******************************************************************)
(* Suppose that for each node, dfs numbering gives at least one predecessor
   of the node a larger number than the node.
   Initially, if a node's dominator set is full, then there must exist 
   at least one predecessor in the worklist that has a larger PO-number. *)

Module InitOrder. Section InitOrder.

Variable successors: PTree.t (list positive).
Definition predecessors := XPTree.make_predecessors successors.
Definition in_cfg := XPTree.in_cfg successors.

Definition wf_state (st: DomDS.state) : Prop :=
forall n (Hincfg: in_cfg n),
  match (st.(DomDS.st_in)) ?? n with
  | None => 
      exists p, 
        In p (predecessors ??? n) /\ (p > n)%positive /\ 
        PNodeSetMax.In p st.(DomDS.st_wrk)
  | Some _ => True
  end.

Lemma max_of_worklist_isnt_bot: forall st (Hwf: wf_state st) n rem
  (Hinprt: WorklistProps.wf_state successors st)
  (Hpick: PNodeSetMax.pick (DomDS.st_wrk st) = Some (n, rem)),
  (st.(DomDS.st_in)) ?? n <> None.
Proof.
  intros.
  assert (Hin:=Hpick).
  apply PNodeSetMax.pick_in in Hin.
  apply PNodeSetMax.pick_max in Hpick.
  apply Hinprt in Hin. 
  apply Hwf in Hin.
  intro Hget.
  rewrite Hget in Hin.
  destruct_conjs.
  eapply PositiveSet.max_elt_2 in Hpick; eauto.
  apply Hpick. apply ZC1 in H0; auto.
Qed.

Lemma propagate_succ_list_wf_state: forall st (Hwf: wf_state st) 
  (Hinprt: WorklistProps.wf_state successors st) rem p 
  (Hpick: PNodeSetMax.pick (DomDS.st_wrk st) = Some (p, rem)),
  wf_state 
    (DomDS.propagate_succ_list 
      {| DomDS.st_in := DomDS.st_in st; DomDS.st_wrk := rem |}
      (LDoms.transfer p (DomDS.st_in st) ?? p) successors ??? p).
Proof.
  intros.
  assert (Hnonbot:=Hpick).
  apply max_of_worklist_isnt_bot in Hnonbot; auto.
  apply LDoms.transfer_nonbot with (p:=p) in Hnonbot.
  intros n Hincfg.
  match goal with
  | |- match ?e with
       | Some _ => _
       | None => _
       end => remember e as R; destruct R; auto; symmetry in HeqR
  end.
  destruct (In_dec positive_eq_dec n (successors ??? p)) as [Hin | Hnotin].
    contradict HeqR.
    eapply propagate_succ_list_nonbot; eauto.

    rewrite propagate_succ_list_st_in in HeqR; auto.
    apply Hwf in Hincfg. simpl in HeqR.
    fill_holes_in_ctx.
    destruct Hincfg as [p' [J1 [J2 J3]]].
    destruct (positive_eq_dec p p'); subst.
      apply XPTree.make_predecessors_correct' in J1. 
      tauto.

      exists p'.
      repeat split; auto.
        apply propagate_succ_list_incr_worklist. 
        simpl.
        apply PNodeSetMax.pick_remove in Hpick. subst.
        apply PositiveSet.remove_2; auto.
Qed.

Lemma pick_gt_bot_successors: forall st 
  (Hinprt: WorklistProps.wf_state successors st)
  (Hwf: wf_state st) p rem
  (Hpick: PNodeSetMax.pick (DomDS.st_wrk st) = Some (p, rem)),
  forall sc (Hinscs: In sc (successors ??? p)) 
    (Hbot: (DomDS.st_in st) ?? sc = None),
    (p > sc)%positive.
Proof.
  intros.
  assert (Hnonbot:=Hpick).
  eapply max_of_worklist_isnt_bot in Hnonbot; eauto.
  destruct (positive_eq_dec p sc); subst.
    congruence.

    assert (in_cfg sc) as Hincfg.
      apply PNodeSetMax.pick_in in Hpick. 
      apply Hinprt in Hpick.
      eapply XPTree.in_succ__in_cfg; eauto.
    apply Hwf in Hincfg.
    rewrite Hbot in Hincfg.
    destruct_conjs.
    apply PNodeSetMax.pick_max in Hpick.
    eapply PositiveSet.max_elt_2 in Hpick; eauto.
      apply Pnlt__Pgt_Peq in Hpick.
      destruct Hpick as [Hpick | Hpick]; subst; auto.
      eapply Pgt_trans; eauto.
Qed.

Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Lemma entrypoints_wf_state: forall
  (wf_order: forall n (Hneq: n <> entrypoint) (Hincfg: in_cfg n),
    exists p, In p (predecessors ??? n) /\ (p > n)%positive),
  wf_state (DomDS.mkstate (DomDS.start_state_in entrypoints) 
                          (PNodeSetMax.initial successors)).
Proof.
  intros. 
  intros n Hincfg; simpl.
  destruct (positive_eq_dec n entrypoint) as [|n0]; subst.
    rewrite PMap.gss. 
    rewrite PMap.gi; simpl; auto.

    rewrite PMap.gso; auto. 
    rewrite PMap.gi; simpl.
    apply wf_order in n0; auto.
    destruct n0 as [p [J1 J2]].
    exists p.
    repeat split; auto.
      apply XPTree.in_pred__in_parents in J1; auto.
      apply WorklistProps.in_parents_of_tree__in_initial; auto.
Qed.

End InitOrder. End InitOrder.

(***************************************************)

Module Mono. Section Mono.

(** ** Monotonicity properties *)

(** We first show that the [st_in] part of the state evolves monotonically:
  at each step, the values of the [st_in[n]] either remain the same or
  increase with respect to the [L.ge] ordering. *)

Variable successors: PTree.t (list positive).
Definition in_cfg := XPTree.in_cfg successors.

Lemma propagate_succ_wf:
  forall st out n,
  DomMap.in_incr st.(DomDS.st_in) (DomDS.propagate_succ st out n).(DomDS.st_in).
Proof.
  unfold DomMap.in_incr, DomDS.propagate_succ; simpl; intros.
  destruct_let. 
  destruct_if.
    simpl. 
    case (positive_eq_dec n n0); intro; subst.
      rewrite PMap.gss. 
      eapply LDoms.ge_lub_left; eauto.

      rewrite PMap.gso; auto. apply LDoms.ge_refl. 

    simpl.
    apply LDoms.ge_refl. 
Qed.

Lemma propagate_succ_list_wf:
  forall out scs st,
  DomMap.in_incr st.(DomDS.st_in) 
                 (DomDS.propagate_succ_list st out scs).(DomDS.st_in).
Proof.
  induction scs; simpl; intros.
    apply DomMap.in_incr_refl.

    apply DomMap.in_incr_trans with 
      (DomDS.propagate_succ st out a).(DomDS.st_in).
    apply propagate_succ_wf. auto.
Qed.

Lemma step_wf: forall (st st': DomDS.state)
  (Hstep: DomDS.step successors LDoms.transfer st = inr st'),
  DomMap.in_incr (DomDS.st_in st) (DomDS.st_in st').
Proof.
  unfold DomDS.step.
  intros.
  remember (PNodeSetMax.pick (DomDS.st_wrk st)) as R.
  destruct R as [ [n rem] | ]; inv Hstep.
  change st.(DomDS.st_in) with 
     (DomDS.mkstate st.(DomDS.st_in) rem).(DomDS.st_in).
  apply propagate_succ_list_wf; auto.
Qed.

Variable entrypoints: list (positive * LDoms.t).

Lemma fixpoint_wf:
  forall res ni
  (Hfix: DomDS.fixpoint successors LDoms.transfer entrypoints ni = Some res),
  DomMap.in_incr (DomDS.start_state_in entrypoints) res.
Proof.
  unfold DomDS.fixpoint; intros.
  eapply (PrimIter.iter_prop _ _ (DomDS.step successors LDoms.transfer)
    (fun st => 
       DomMap.in_incr (DomDS.start_state_in entrypoints) st.(DomDS.st_in))
    (fun res => DomMap.in_incr (DomDS.start_state_in entrypoints) res)); eauto.
  Case "1".
    intros st INCR. 
    unfold DomDS.step.
    remember (PNodeSetMax.pick (DomDS.st_wrk st)) as R.
    destruct R as [ [n rem] | ]; auto.
      apply DomMap.in_incr_trans with st.(DomDS.st_in); auto.
        change st.(DomDS.st_in) with 
          (DomDS.mkstate st.(DomDS.st_in) rem).(DomDS.st_in).
        apply propagate_succ_list_wf; auto.

  Case "2".
    apply DomMap.in_incr_refl.
Qed.

Lemma propagate_succ_list_records_unchanges:
  forall out bd scs (Hinc: incl scs bd)
  st st' (Heq: st' = DomDS.propagate_succ_list st out scs)
  (H: DomMap.eq bd st.(DomDS.st_in) st'.(DomDS.st_in)),
  st.(DomDS.st_wrk) = st'.(DomDS.st_wrk).
Proof.
  induction scs; simpl; intros; subst; auto.
    assert (J1:=Mono.propagate_succ_wf st out a).
    assert (J2:=Mono.propagate_succ_list_wf out scs (DomDS.propagate_succ st out a)).
    eapply DomMap_eq_incr_incr__eq_eq in H; eauto.
    destruct H.
    transitivity (DomDS.st_wrk (DomDS.propagate_succ st out a)).
      eapply propagate_succ_records_unchanges; eauto with datatypes v62.
      apply IHscs; eauto with datatypes v62.
Qed.

End Mono. End Mono.

(***************************************************)
(* Dominators of a node must be parents of the node. *)

Module DomsInParents. Section DomsInParents.

Variable asuccs: PTree.t (list positive).
Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Definition wf_dom (res: LDoms.t) : Prop :=
  match res with
  | Some ns0 => incl ns0 (XPTree.parents_of_tree asuccs)
  | None => True
  end.

Definition wf_doms (res: PMap.t LDoms.t) : Prop := 
  forall l0, wf_dom (res ?? l0).

Lemma start_wf_doms:
  wf_doms (DomDS.st_in (DomDS.start_state asuccs entrypoints)).
Proof.
  simpl. intros l0.
  rewrite PMap.gsspec.
  rewrite PMap.gi. simpl. 
  destruct_if; simpl.
    intros x Hinx. inv Hinx.
    rewrite PMap.gi. simpl. auto.
Qed.

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma wf_dom_eq: forall dt1 dt2 (Heq: LDoms.eq dt1 dt2) (Hwf: wf_dom dt2),
  wf_dom dt1.
Proof.
  unfold wf_dom.
  intros.
  destruct dt1; destruct dt2; inv Heq; auto.
Qed.

Lemma propagate_succ_wf_doms: forall st n out,
  wf_dom out ->
  wf_doms st.(DomDS.st_in) ->
  wf_doms (DomDS.propagate_succ st out n).(DomDS.st_in).
Proof.
  unfold wf_doms.
  intros.
  destruct (propagate_succ_spec st out n) as [J1 J2].
  destruct (positive_eq_dec n l0); subst.
    apply wf_dom_eq in J1; auto.
    assert (J:=H0 l0).
    clear - J H.
    unfold wf_dom in *.
    case_eq (LDoms.lub (DomDS.st_in st) ?? l0 out).
    intros t b Heq.
    assert (Heq':=Heq).
    apply LDoms.ge_lub_left in Heq'.
    destruct out as [x|]; destruct ((DomDS.st_in st) ?? l0) as [y|]; 
      try solve [inv Heq; simpl; auto].
    destruct t; tinv Heq'.
    simpl in *.
    intros p Hin.
    apply J. eauto with sublist.

    rewrite J2; auto.
Qed.

Lemma propagate_succ_list_wf_doms:
  forall scs st out (Hsc: scs <> nil -> wf_dom out),
  wf_doms st.(DomDS.st_in) ->
  wf_doms (DomDS.propagate_succ_list st out scs).(DomDS.st_in).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs; auto.
      intro J. apply Hsc. congruence.
      apply propagate_succ_wf_doms; auto.
        apply Hsc. congruence.
Qed.

Lemma pick_wf_doms:
  forall st n rem,
  PNodeSetMax.pick st.(DomDS.st_wrk) = Some(n, rem) ->
  wf_doms st.(DomDS.st_in) ->
  wf_doms (DomDS.propagate_succ_list
             (DomDS.mkstate st.(DomDS.st_in) rem)
             (LDoms.transfer n st.(DomDS.st_in)??n)
             (asuccs???n)).(DomDS.st_in).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_wf_doms; auto.
    intro Hnnil.
    assert (J:=GOOD n). simpl in J.
    unfold wf_dom. unfold wf_dom in J.    
    destruct (st_in ?? n); simpl; auto.
    intros x Hin.
    destruct_in Hin; auto.
      apply XPTree.nonleaf_is_parent; auto.
Qed.

Lemma step_wf_doms: forall (st st': DomDS.state)
  (Hstep: DomDS.step asuccs LDoms.transfer st = inr st'),
  wf_doms st.(DomDS.st_in) -> wf_doms st'.(DomDS.st_in).
Proof.
  unfold DomDS.step.
  intros.
  remember (PNodeSetMax.pick (DomDS.st_wrk st)) as R.
  destruct R as [ [n rem] | ]; inv Hstep.
  apply pick_wf_doms; auto.
Qed.

Theorem fixpoint_wf: forall res ni,
  DomDS.fixpoint asuccs LDoms.transfer entrypoints ni = Some res ->
  wf_doms res.
Proof.
  unfold DomDS.fixpoint. intros res ni PI. pattern res.
  eapply (PrimIter.iter_prop _ _ (DomDS.step _ _)
    (fun st => wf_doms st.(DomDS.st_in))); eauto.
    intros st GOOD. unfold DomDS.step.
    caseEq (PNodeSetMax.pick st.(DomDS.st_wrk)); auto.
    intros [n rem] PICK.
    apply pick_wf_doms; auto.

    apply start_wf_doms.
Qed.

Lemma dom_fix_in_bound: forall res ni
  (Hfix: DomDS.fixpoint asuccs LDoms.transfer
           entrypoints ni = Some res),
  forall l0 ns0 (Hget: res ?? l0 = Some ns0) n (Hin: In n ns0),
    In n (XPTree.parents_of_tree asuccs).
Proof.
  intros.
  apply fixpoint_wf in Hfix; auto.
  assert (J:=Hfix l0).
  unfold wf_dom in J.
  rewrite Hget in J. auto.
Qed.

End DomsInParents. End DomsInParents.

(******************************************************)
(* Nodes that are not in CFG are dominated by any nodes. *)

Module NonCFGIsBot. Section NonCFGIsBot.

Variable successors: PTree.t (list positive).
Definition in_cfg := XPTree.in_cfg successors.

Definition wf_doms (dmap: PMap.t LDoms.t) : Prop :=
forall n (Hnotin: ~ in_cfg n), dmap ?? n = None.

Lemma propagate_succ_list_wf_doms: forall (st : DomDS.state)
  (Hwf : wf_doms (DomDS.st_in st)) (p : PositiveSet.elt),
  wf_doms
    (DomDS.st_in 
      (DomDS.propagate_succ_list
        st (LDoms.transfer p (DomDS.st_in st) ?? p) successors ??? p)).
Proof.
  intros.
  intros n Hnotin.
  rewrite propagate_succ_list_st_in; auto.
  intro J. apply Hnotin.
  eapply XPTree.in_succ__in_cfg; eauto.
Qed.

Variable entrypoint: positive.
Hypothesis wf_entrypoints: in_cfg entrypoint.
Variable init: LDoms.t.
Definition entrypoints := (entrypoint, init) :: nil.

Lemma entrypoints_wf_doms:
  wf_doms (DomDS.start_state_in entrypoints).
Proof.
  simpl.
  intros x Hnotin.
  rewrite PMap.gsspec.
  rewrite PMap.gi.
  destruct_if.
    congruence.    
    repeat rewrite PMap.gi. simpl. auto.
Qed.

End NonCFGIsBot. End NonCFGIsBot.

(***************************************************)
(* A node's dominators' PO-number must be larger than the node's. *)

Module LtDoms. Section LtDoms.

Variable successors: PTree.t (list positive).

Definition wf_doms (dmap: PMap.t LDoms.t) : Prop :=
forall n,
  match dmap ?? n with
  | None => True
  | Some sdms =>
      List.Forall (Plt n) sdms
  end.

Lemma lub_transfer_stable: forall dmap (Hwf: wf_doms dmap) p r changed
  (Heq: LDoms.lub dmap ?? p (LDoms.transfer p dmap ?? p) = (r, changed)),
  dmap ?? p = r.
Proof.
  intros.
  assert (J:=Hwf p).
  destruct (dmap ?? p); auto.    
    simpl in Heq.
    rewrite LDoms.merge_cmp_cons in Heq; auto.
    congruence.

    simpl in Heq. congruence.
Qed.

Lemma propagate_succ_self_stable: forall st n p 
  (Hwf: wf_doms (DomDS.st_in st)),
  (DomDS.st_in st) ?? p = 
  (DomDS.st_in 
    (DomDS.propagate_succ st (LDoms.transfer p (DomDS.st_in st) ?? p) n)) ?? p.
Proof.
  destruct st as [dmap rem]. simpl.
  intros.
  unfold DomDS.propagate_succ. simpl.
  destruct_let. destruct_if. simpl.
  case (positive_eq_dec n p); intro; subst.
    rewrite PMap.gss. eapply lub_transfer_stable; eauto.
    rewrite PMap.gso; auto. 
Qed.

Lemma propagate_succ_wf_doms:
  forall st p n 
  (Hwf: wf_doms st.(DomDS.st_in))
  (Horder: (DomDS.st_in st) ?? n = None -> (p > n)%positive),
  wf_doms
    (DomDS.propagate_succ st (LDoms.transfer p (st.(DomDS.st_in)??p)) n).(DomDS.st_in).
Proof.
  intros.
  unfold DomDS.propagate_succ.
  destruct_let. destruct_if. simpl.
  intros x.
  case (positive_eq_dec n x); intro; subst.
  Case "1".
    rewrite PMap.gss. 
    assert (G:=Hwf x).
    assert (J:=LDoms.ge_lub_left 
                 (DomDS.st_in st) ?? x 
                 (LDoms.transfer p (DomDS.st_in st) ?? p)).
    remember ((DomDS.st_in st) ?? x) as R.
    destruct R.
    SCase "1.1".
      eapply LDoms.ge_Forall; eauto.
    SCase "1.2".     
      remember ((DomDS.st_in st) ?? p) as R.
      destruct R.
        simpl in HeqR. uniq_result.
        assert (G':=Hwf p).
        fill_holes_in_ctx.
        constructor.
          apply ZC1. apply Horder. auto.
          eapply order_lt_order in G'; eauto.  

        simpl in HeqR. congruence.

  Case "2".
    rewrite PMap.gso; auto. 
    apply Hwf; auto.
Qed.

Lemma propagate_succ_list_wf_doms_aux: forall 
  p scs st (Hwf: wf_doms (DomDS.st_in st))
  (Horder: forall n (Hin: In n scs) (Hbot: (DomDS.st_in st) ?? n = None),
             (p > n)%positive),
  wf_doms
    (DomDS.st_in
       (DomDS.propagate_succ_list 
          st (LDoms.transfer p (DomDS.st_in st) ?? p) scs)).
Proof.
  induction scs as [|sc scs]; simpl; intros; auto.
    rewrite propagate_succ_self_stable at 2; auto.
    apply IHscs; auto using propagate_succ_wf_doms.
       intros. apply propagate_succ_bot_inv in Hbot. auto.
Qed.

Definition wf_state st : Prop := 
WorklistProps.wf_state successors st /\
InitOrder.wf_state successors st /\
wf_doms (st.(DomDS.st_in)).

Hint Unfold wf_state.

Lemma propagate_succ_list_wf_doms: forall (st : DomDS.state)
  (Hwf : wf_state st)
  (rem : PositiveSet.t) (p : PositiveSet.elt)
  (Hpick : PNodeSetMax.pick (DomDS.st_wrk st) = Some (p, rem)),
  wf_doms
    (DomDS.st_in 
      (DomDS.propagate_succ_list
        {| DomDS.st_in := DomDS.st_in st; DomDS.st_wrk := rem |}
        (LDoms.transfer p (DomDS.st_in st) ?? p) successors ??? p)).
Proof.
  intros.
  destruct Hwf as [? [? ?]].
  change st.(DomDS.st_in) with 
    (DomDS.mkstate st.(DomDS.st_in) rem).(DomDS.st_in).
  apply propagate_succ_list_wf_doms_aux; auto.
    intros. eapply InitOrder.pick_gt_bot_successors in Hpick; eauto.
Qed.

Lemma propagate_succ_list_wf_state: forall st (Hwf: wf_state st) rem p 
  (Hpick: PNodeSetMax.pick (DomDS.st_wrk st) = Some (p, rem)),
  wf_state 
    (DomDS.propagate_succ_list 
      {| DomDS.st_in := DomDS.st_in st; DomDS.st_wrk := rem |}
      (LDoms.transfer p (DomDS.st_in st) ?? p) successors ??? p).
Proof.
  intros.
  destruct Hwf as [Hwf1 [Hwf2 Hwf3]].
  split. apply WorklistProps.propagate_succ_list_wf_state; auto.
  split. apply InitOrder.propagate_succ_list_wf_state; auto.
         apply propagate_succ_list_wf_doms; auto.
Qed.

Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Definition predecessors := XPTree.make_predecessors successors.

Hypothesis wf_order: forall n (Hneq: n <> entrypoint) 
  (Hincfg: XPTree.in_cfg successors n),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.

Lemma entrypoints_wf_doms:
  wf_doms (DomDS.start_state_in entrypoints).
Proof.
  simpl.
  intros x.
  rewrite PMap.gsspec.
  rewrite PMap.gi.
  destruct_if.
    simpl. auto.
    repeat rewrite PMap.gi. simpl. auto.
Qed.

Lemma entrypoints_wf_state:
  wf_state (DomDS.mkstate (DomDS.start_state_in entrypoints) 
                          (PNodeSetMax.initial successors)).
Proof.
  split. apply WorklistProps.entrypoints_wf_state.
  split. apply InitOrder.entrypoints_wf_state; auto.
         apply entrypoints_wf_doms.
Qed.

Lemma wf_state__wf_doms: forall st (Hwf: wf_state st), wf_doms st.(DomDS.st_in).
Proof. unfold wf_state. tauto. Qed.

Lemma fixpoint_wf:
  forall res ni
  (Hfix: DomDS.fixpoint successors LDoms.transfer entrypoints ni = Some res),
  wf_doms res.
Proof.
  unfold DomDS.fixpoint; intros.
  eapply (PrimIter.iter_prop _ _ (DomDS.step successors LDoms.transfer)
    (fun st => wf_state st)
    (fun res => wf_doms res)); eauto.
  Case "1".
    intros st WF. unfold DomDS.step.
    remember (PNodeSetMax.pick (DomDS.st_wrk st)) as R.
    destruct R as [ [n rem] | ]; auto using 
      wf_state__wf_doms, propagate_succ_list_wf_state.

  Case "2".
    auto using entrypoints_wf_state.
Qed.

End LtDoms. End LtDoms.

(***************************************************)
(* A node's dominators are sorted by less-than. *)

Require Import Sorted.

Module SortedDoms. Section SortedDoms.

Variable successors: PTree.t (list positive).

Definition wf_dom (dms: LDoms.t) : Prop :=
  match dms with
  | None => True
  | Some sdms => Sorted Plt sdms
  end.

Definition wf_doms (dmap: PMap.t LDoms.t) : Prop :=
forall n,
  match dmap ?? n with
  | None => True
  | Some sdms => Sorted Plt (n::sdms)
  end.

Lemma wf_doms__wf_transfer_dom: forall dms p (Hwf:wf_doms dms), 
  wf_dom (LDoms.transfer p dms ?? p).
Proof.
  intros.
  assert (J:=Hwf p). unfold wf_dom.
  destruct (dms ?? p); auto.
Qed.

Lemma wf_doms__wf_dom: forall dms n (Hwf:wf_doms dms), wf_dom dms??n.
Proof.
  intros.
  assert (J:=Hwf n). unfold wf_dom.
  destruct (dms ?? n); auto.
  inv J; auto.
Qed.

Lemma propagate_succ_wf_doms:
  forall st p n (Hwflt: LtDoms.wf_doms st.(DomDS.st_in)) 
  (Hwf: wf_doms st.(DomDS.st_in))
  (Horder: (DomDS.st_in st) ?? n = None -> (p > n)%positive),
  wf_doms
    (DomDS.propagate_succ st 
      (LDoms.transfer p (st.(DomDS.st_in)??p)) n).(DomDS.st_in).
Proof.
  intros.
  unfold DomDS.propagate_succ.
  destruct_let. destruct_if. simpl.
  intros x.
  case (positive_eq_dec n x); intro; subst.
  Case "1".
    rewrite PMap.gss.
    assert (Hincfg:=Hwf x). 
    assert (Hlt:=Hwflt x).
    assert (J:=LDoms.ge_lub_left 
                 (DomDS.st_in st) ?? x 
                 (LDoms.transfer p (DomDS.st_in st) ?? p)).
    remember ((DomDS.st_in st) ?? x) as R.
    destruct R.
    SCase "1.1".
      symmetry in HeqR.
      apply_clear J in HeqR.
      destruct t as [out|]; auto.
        eapply sublist_cons_sorted; eauto.
          unfold Relations_1.Transitive. eauto with positive.

    SCase "1.2".
      remember ((DomDS.st_in st) ?? p) as R.
      destruct R.
        simpl in HeqR. uniq_result.
        assert (Hin:=Hwf p).
        fill_holes_in_ctx.
        constructor; auto.
          constructor.
          apply ZC1. apply Horder. auto.

        simpl in HeqR. inv HeqR.

  Case "2".
    rewrite PMap.gso; auto. 
    apply Hwf; auto.
Qed.

Lemma propagate_succ_list_wf_doms_aux: forall 
  p scs st (Hwf: wf_doms (DomDS.st_in st))
  (Hwflt: LtDoms.wf_doms st.(DomDS.st_in)) 
  (Horder: forall n (Hin: In n scs) (Hbot: (DomDS.st_in st) ?? n = None),
             (p > n)%positive),
  wf_doms
    (DomDS.st_in
       (DomDS.propagate_succ_list 
          st (LDoms.transfer p (DomDS.st_in st) ?? p) scs)).
Proof.
  induction scs as [|sc scs]; simpl; intros; auto.
    rewrite LtDoms.propagate_succ_self_stable at 2; eauto.
    apply IHscs; 
       eauto using propagate_succ_wf_doms, LtDoms.propagate_succ_wf_doms.
       intros. apply propagate_succ_bot_inv in Hbot. auto.
Qed.

Definition wf_state st : Prop := 
WorklistProps.wf_state successors st /\
InitOrder.wf_state successors st /\
LtDoms.wf_doms (st.(DomDS.st_in)) /\
wf_doms (st.(DomDS.st_in)).

Hint Unfold wf_state.

Lemma propagate_succ_list_wf_doms: forall (st : DomDS.state)
  (Hwf : wf_state st)
  (rem : PositiveSet.t) (p : PositiveSet.elt)
  (Hpick : PNodeSetMax.pick (DomDS.st_wrk st) = Some (p, rem)),
  wf_doms
    (DomDS.st_in 
      (DomDS.propagate_succ_list
        {| DomDS.st_in := DomDS.st_in st; DomDS.st_wrk := rem |}
        (LDoms.transfer p (DomDS.st_in st) ?? p) successors ??? p)).
Proof.
  intros.
  destruct Hwf as [? [? [? ?]]].
  change st.(DomDS.st_in) with 
    (DomDS.mkstate st.(DomDS.st_in) rem).(DomDS.st_in).
  apply propagate_succ_list_wf_doms_aux; auto.
    intros. eapply InitOrder.pick_gt_bot_successors in Hpick; eauto.
Qed.

Lemma propagate_succ_list_wf_state: forall st (Hwf: wf_state st) rem p 
  (Hpick: PNodeSetMax.pick (DomDS.st_wrk st) = Some (p, rem)),
  wf_state 
    (DomDS.propagate_succ_list 
      {| DomDS.st_in := DomDS.st_in st; DomDS.st_wrk := rem |}
      (LDoms.transfer p (DomDS.st_in st) ?? p) successors ??? p).
Proof.
  intros.
  destruct Hwf as [Hwf1 [Hwf2 [Hwf3 Hwf4]]].
  split. apply WorklistProps.propagate_succ_list_wf_state; auto.
  split. apply InitOrder.propagate_succ_list_wf_state; auto.
  split. apply LtDoms.propagate_succ_list_wf_doms; auto; split; auto.
         apply propagate_succ_list_wf_doms; auto.
Qed.

Lemma step_wf_state: forall (st st': DomDS.state) (Hwf: wf_state st)
  (Hstep: DomDS.step successors LDoms.transfer st = inr st'),
  wf_state st -> wf_state st'.
Proof.
  unfold DomDS.step.
  intros.
  remember (PNodeSetMax.pick (DomDS.st_wrk st)) as R.
  destruct R as [ [n rem] | ]; inv Hstep.
  apply propagate_succ_list_wf_state; auto.
Qed.

Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Definition predecessors := XPTree.make_predecessors successors.

Hypothesis wf_order: forall n (Hneq: n <> entrypoint)
  (Hincfg: XPTree.in_cfg successors n),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.

Lemma entrypoints_wf_doms:
  wf_doms (DomDS.start_state_in entrypoints).
Proof.
  simpl.
  intros x.
  rewrite PMap.gsspec.
  rewrite PMap.gi.
  destruct_if.
    simpl. auto.
    repeat rewrite PMap.gi. simpl. auto.
Qed.

Lemma entrypoints_wf_state:
  wf_state (DomDS.mkstate (DomDS.start_state_in entrypoints) 
                          (PNodeSetMax.initial successors)).
Proof.
  split. apply WorklistProps.entrypoints_wf_state.
  split. apply InitOrder.entrypoints_wf_state; auto.
  split. apply LtDoms.entrypoints_wf_state; auto.
         apply entrypoints_wf_doms.
Qed.

Lemma wf_state__wf_doms: forall st (Hwf: wf_state st), wf_doms st.(DomDS.st_in).
Proof. unfold wf_state. tauto. Qed.

Lemma fixpoint_wf:
  forall res ni
  (Hfix: DomDS.fixpoint successors LDoms.transfer entrypoints ni = Some res),
  wf_doms res.
Proof.
  unfold DomDS.fixpoint; intros.
  eapply (PrimIter.iter_prop _ _ (DomDS.step successors LDoms.transfer)
    (fun st => wf_state st)
    (fun res => wf_doms res)); eauto.
  Case "1".
    intros st WF. unfold DomDS.step.
    remember (PNodeSetMax.pick (DomDS.st_wrk st)) as R.
    destruct R as [ [n rem] | ]; auto using 
      wf_state__wf_doms, propagate_succ_list_wf_state.

  Case "2".
    auto using entrypoints_wf_state.
Qed.

End SortedDoms. End SortedDoms.

(***************************************************)

Module Inequations. Section Inequations.

(** ** Correctness invariant *)

(** The following invariant is preserved at each iteration of Kildall's
  algorithm: for all program points [n], either
  [n] is in the worklist, or the inequations associated with [n]
  ([st_in[s] >= transf n st_in[n]] for all successors [s] of [n])
  hold.  In other terms, the worklist contains all nodes that do not
  yet satisfy their inequations. *)

Variable successors: PTree.t (list positive).

Definition good_state (st: DomDS.state) : Prop :=
  forall n,
  PNodeSetMax.In n st.(DomDS.st_wrk) \/
  (forall s, In s (successors???n) ->
             LDoms.ge st.(DomDS.st_in)??s 
                      (LDoms.transfer n st.(DomDS.st_in)??n)).

Lemma propagate_succ_charact:
  forall st out n (Hwf: SortedDoms.wf_doms st.(DomDS.st_in)),
  let st' := DomDS.propagate_succ st out n in
  LDoms.ge st'.(DomDS.st_in)??n out /\
  (forall s, n <> s -> st'.(DomDS.st_in)??s = st.(DomDS.st_in)??s).
Proof.
  unfold DomDS.propagate_succ; intros; simpl.
  destruct_let.
  destruct_if.
    simpl.
    split.
      rewrite PMap.gss.
      eapply LDoms.ge_lub_right; eauto.

      intros. rewrite PMap.gso; auto.

    split; auto.
      symmetry in HeqR.
      assert (J:=HeqR).
      apply LDoms.lub_unchanged_eq_left in J. subst.
      eapply LDoms.ge_lub_right; eauto.
Qed.

Lemma propagate_succ_list_charact:
  forall p scs st (Hwf: SortedDoms.wf_doms (DomDS.st_in st)) 
                  (Hwf0: LtDoms.wf_doms (DomDS.st_in st))
  (Horder: forall n (Hin: In n scs) (Hbot: (DomDS.st_in st) ?? n = None),
             (p > n)%positive),
  let out := LDoms.transfer p (DomDS.st_in st) ?? p in
  let st' := DomDS.propagate_succ_list st out scs in
  forall s,
  (In s scs -> LDoms.ge st'.(DomDS.st_in)??s out) /\
  (~(In s scs) -> st'.(DomDS.st_in)??s = st.(DomDS.st_in)??s).
Proof.
  induction scs; simpl; intros.
  tauto.
  
  set (out:=LDoms.transfer p (DomDS.st_in st) ?? p).
  set (st':=DomDS.propagate_succ st out a).
  assert (LtDoms.wf_doms (DomDS.st_in st')) as Hwf0'.
    apply LtDoms.propagate_succ_wf_doms; auto.
  assert (SortedDoms.wf_doms (DomDS.st_in st')) as Hwf'.
    apply SortedDoms.propagate_succ_wf_doms; auto.
  assert (forall (n : positive) (Hin: In n scs) 
            (Hbot: (DomDS.st_in st') ?? n = None), (p > n)%positive) as Horder'.
    intros. apply propagate_succ_bot_inv in Hbot. auto.
  generalize (IHscs st' Hwf' Hwf0' Horder' s). intros [A B].
  generalize (propagate_succ_charact st out a Hwf). intros [C D].
  split; intros.
  Case "1".
    elim H; intro.
    SCase "1.1".
      subst s.
      apply LDoms.ge_trans with (DomDS.propagate_succ st out a).(DomDS.st_in)??a.
        apply Mono.propagate_succ_list_wf. assumption.
    SCase "1.2".
      subst out st'.
      repeat (rewrite <- LtDoms.propagate_succ_self_stable in A at 1; auto).
  Case "2".
    transitivity (DomDS.propagate_succ st out a).(DomDS.st_in)??s.
      subst out st'.
      repeat (rewrite <- LtDoms.propagate_succ_self_stable in B at 1; auto).

      subst out st'.
      repeat (rewrite <- LtDoms.propagate_succ_self_stable in D at 1; auto).
      apply D. tauto.
Qed.

Lemma step_state_good:
  forall st n rem (Hwf: SortedDoms.wf_state successors st),
  PNodeSetMax.pick st.(DomDS.st_wrk) = Some(n, rem) ->
  good_state st ->
  good_state (DomDS.propagate_succ_list (DomDS.mkstate st.(DomDS.st_in) rem)
                                        (LDoms.transfer n st.(DomDS.st_in)??n)
                                        (successors???n)).
Proof.
  unfold good_state. intros st n rem Hwf WKL GOOD x.
  generalize (PNodeSetMax.pick_some _ _ _ WKL); intro PICK.
  set (out := LDoms.transfer n st.(DomDS.st_in)??n).
  elim (propagate_succ_list_records_changes
          out (successors???n) (DomDS.mkstate st.(DomDS.st_in) rem) x).
  intro; left; auto.

  destruct Hwf as [Hwf1 [Hwf2 [Hwf3 Hwf4]]].
  assert (Horder: forall sc (Hin: In sc (successors???n)) 
             (Hbot: (DomDS.st_in st) ?? sc = None),
             (n > sc)%positive).
    eapply InitOrder.pick_gt_bot_successors; eauto.

  simpl; intros EQ. rewrite EQ.
  case (positive_eq_dec x n); intro.
  (* Case 1: x = n *)
  subst x.
  right; intros.
  elim (propagate_succ_list_charact n (successors???n)
          (DomDS.mkstate st.(DomDS.st_in) rem) Hwf4 Hwf3 Horder s); 
    intros.
    auto.
  (* Case 2: x <> n *)
  elim (GOOD x); intro.
  (* Case 2.1: x was already in worklist, still is *)
  left. apply propagate_succ_list_incr_worklist.
  simpl. rewrite PICK in H. elim H; intro. congruence. auto.
  (* Case 2.2: x was not in worklist *)
  right; intros.
  case (In_dec positive_eq_dec s (successors???n)); intro.
  (* Case 2.2.1: s is a successor of n, it may have increased *)
  apply LDoms.ge_trans with st.(DomDS.st_in)??s; auto.
  change st.(DomDS.st_in)??s with 
    (DomDS.mkstate st.(DomDS.st_in) rem).(DomDS.st_in)??s.
  apply Mono.propagate_succ_list_wf.
  (* Case 2.2.2: s is not a successor of n, it did not change *)
  elim (propagate_succ_list_charact n (successors???n)
          (DomDS.mkstate st.(DomDS.st_in) rem) Hwf4 Hwf3 Horder s); intros.
  subst out. simpl in H2. rewrite H2; auto. 
Qed.

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Lemma start_state_good:
  good_state (DomDS.start_state successors entrypoints).
Proof.
  unfold good_state, DomDS.start_state; intros.
  case_eq (successors ? n); intros.
  left; simpl. eapply PNodeSetMax.initial_spec. eauto.
  unfold XPTree.successors_list. rewrite H. right; intros. contradiction.
Qed.

(** ** Correctness of the solution returned by [iterate]. *)

(** As a consequence of the [good_state] invariant, the result of
  [fixpoint], if defined, is a solution of the dataflow inequations,
  since [st_wrk] is empty when the iteration terminates. *)

Definition predecessors := XPTree.make_predecessors successors.

Hypothesis wf_order: forall n (Hneq: n <> entrypoint)
  (Hincfg: XPTree.in_cfg successors n),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.

Theorem fixpoint_solution:
  forall res ni n s,
  DomDS.fixpoint successors LDoms.transfer entrypoints ni = Some res ->
  In s (successors???n) ->
  LDoms.ge res??s (LDoms.transfer n res??n).
Proof.
  assert (forall res ni, 
          DomDS.fixpoint successors LDoms.transfer entrypoints ni = Some res ->
          forall n s,
          In s successors???n ->
          LDoms.ge res??s (LDoms.transfer n res??n)) as J.
    unfold DomDS.fixpoint. intros res ni PI. pattern res.
    eapply (PrimIter.iter_prop _ _ (DomDS.step successors LDoms.transfer) 
            (fun st => SortedDoms.wf_state successors st /\ good_state st )); 
      eauto 1.
    Case "1".
      intros st [WF GOOD]. unfold DomDS.step.
      caseEq (PNodeSetMax.pick st.(DomDS.st_wrk)).
      SCase "1.1".
        intros [n rem] PICK. 
        split.
          apply SortedDoms.propagate_succ_list_wf_state; auto.       
          apply step_state_good; auto.
      SCase "1.2".
        intros.
        elim (GOOD n); intro.
        elim (PNodeSetMax.pick_none _ n H). auto.
        auto.

    Case "2".
      split.
        apply SortedDoms.entrypoints_wf_state; auto.
        apply start_state_good.
  eauto.
Qed.

(** As a consequence of the monotonicity property, the result of
  [fixpoint], if defined, is pointwise greater than or equal the
  initial mapping.  Therefore, it satisfies the additional constraints
  stated in [entrypoints]. *)

Lemma start_state_in_entry:
  forall ep n v,
  In (n, v) ep ->
  LDoms.ge (DomDS.start_state_in ep)??n v.
Proof.
  induction ep; simpl; intros.
  elim H.
  elim H; intros.
    subst a. rewrite PMap.gss.
    apply LDoms.ge_lub_right'.

    destruct a. 
    rewrite PMap.gsspec; auto.
    destruct_if.
    destruct H as [H | H].
      inv H.
      apply LDoms.ge_lub_right'.
  
      apply LDoms.ge_trans with (DomDS.start_state_in ep)??p; auto.
        apply LDoms.ge_lub_left'. 
Qed.

Theorem fixpoint_entry:
  forall res ni n v,
  DomDS.fixpoint successors LDoms.transfer entrypoints ni = Some res ->
  In (n, v) entrypoints ->
  LDoms.ge res??n v.
Proof.
  intros.
  apply LDoms.ge_trans with (DomDS.start_state_in entrypoints)??n.
    apply Mono.fixpoint_wf in H. apply H.
    apply start_state_in_entry. auto.
Qed.

End Inequations. End Inequations.

(***************************************************)
(* Define the interfaces of computing dominators. *)

Require Import Dipaths.
Require Import cfg.

Section Domination.

Variable successors: PTree.t (list positive).
Definition in_cfg := XPTree.in_cfg successors.

Definition member (n:positive) (odms: LDoms.t) : Prop :=
match odms with
| Some dms => In n dms
| None => in_cfg n
end.

(* transfer --> Cfg.add ? *)

Lemma add_member2: forall (n1 n2 : positive) dms
  (Hin: member n1 dms),
  member n1 (LDoms.transfer n2 dms).
Proof.
  destruct dms as [dms|]; simpl; intros; auto.
Qed.

Lemma member_transfer_inv: forall (n1 n2 : positive) (Hneq: n1 <> n2) dms
  (Hin: member n1 (LDoms.transfer n2 dms)),
  member n1 dms.
Proof.
  destruct dms as [dms|]; simpl; intros; auto.
    destruct Hin. congruence. auto.
Qed.

Lemma member_lub: forall n x y (Hinx: member n x) 
  (Hiny: member n y) (Hsx: SortedDoms.wf_dom x) (Hsy: SortedDoms.wf_dom y),
  member n (fst (LDoms.lub x y)).
Proof.
  destruct x as [x|]; destruct y as [y|]; simpl; auto.
    intros.
    destruct_let. simpl.
    symmetry in HeqR.
    apply MergeLt.merge_inter in HeqR; auto using Plt_Sorted__StronglySorted.
    apply in_rev.
    apply HeqR.
    apply ListSet.set_inter_intro; auto.
Qed.

Lemma add_member1: forall n x (Hin: in_cfg n),
  member n (LDoms.transfer n x).
Proof.
  destruct x as [x|]; simpl; intros; auto.
Qed.

Lemma member_dec: forall n x,
  member n x \/ ~ member n x.
Proof.
  destruct x as [x|]; simpl.
    destruct (List.In_dec positive_eq_dec n x); auto.
    apply XPTree.in_cfg_dec; auto using positive_eq_dec.
Qed.

Lemma ge_elim : forall a (Hin: in_cfg a) x y 
  (Hge1: LDoms.ge x y) (Hge2: member a x), 
  member a y.
Proof.
  destruct x as [x|]; destruct y as [y|]; simpl; eauto with sublist.
    tauto.
Qed.

Variable entrypoint: positive.
Variable num_iters: positive.

(* The main interface *)
Definition pdom_analyze : PMap.t LDoms.t :=
match DomDS.fixpoint successors LDoms.transfer 
              ((entrypoint, LDoms.top) :: nil) num_iters with
| None => PMap.init LDoms.top
| Some res => res
end.

Definition adomination (n1 n2:positive) : Prop :=
member n1 (LDoms.transfer n2 (pdom_analyze ?? n2)).

Definition strict_adomination (n1 n2:positive) : Prop :=
member n1 (pdom_analyze ?? n2).

Lemma sadom__adom: forall n1 n2
  (Hsdom: strict_adomination n1 n2), adomination n1 n2.
Proof.
  unfold strict_adomination, adomination. intros.
  eapply add_member2; eauto.
Qed.

Lemma adom__sadom: forall n1 n2 (Hneq: n1 <> n2)
  (Hdom: adomination n1 n2), strict_adomination n1 n2.
Proof.
  unfold strict_adomination, adomination. intros.
  eapply member_transfer_inv; eauto.
Qed.

End Domination.

(***************************************************)
(* Properties of entry points *)

Section StartStateIn.

Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Lemma dom_entry_start_state_in:
  forall n v,
  In (n, v) entrypoints ->
  (DomDS.start_state_in entrypoints)??n = v.
Proof.
  intros. simpl in *.
  destruct H as [H | H]; inv H.
  rewrite PMap.gss. rewrite PMap.gi.
  simpl. auto.
Qed.

Lemma dom_nonentry_start_state_in:
  forall n,
  n <> entrypoint ->
  (DomDS.start_state_in entrypoints)??n = LDoms.bot.
Proof.
  intros. simpl in *.
  rewrite PMap.gi. rewrite PMap.gso; auto. rewrite PMap.gi. auto.
Qed.

End StartStateIn.

(***********************************************************)

Section NoDupA_More.

Variable A:Type.
Variable Hdec: forall x y : A, {x = y} + {x <> y}.
Definition eqa := fun (x y:A) => x = y.

Lemma NoDupA_remove_notin_length: forall
  a ls2 (Hndp2 : NoDupA eqa ls2)
  (Hin : ~ InA eqa a ls2),
  (length (removeA Hdec a ls2)) = length ls2.
Proof.
  induction 1; simpl; intros; auto.
    destruct_if.
      contradict Hin. simpl. constructor. reflexivity.

      simpl. 
      rewrite IHHndp2; auto.
Qed.

Lemma NoDupA_remove_in_length: forall a ls2 (Hndp2 : NoDupA eqa ls2)
  (Hin : InA eqa a ls2),
  S (length (removeA Hdec a ls2)) = length ls2.
Proof.
  induction 1; simpl; intros.
    inv Hin.

    destruct_if.
      rewrite NoDupA_remove_notin_length; auto.
      simpl. rewrite IHHndp2; auto.
        inv Hin; auto.
          inv H1. congruence.
Qed.

Lemma removeA_in_iff: forall (a1 : A) (ls1 ls2 : list A)
  (Heq : forall x : A, InA eqa x (a1 :: ls1) <-> InA eqa x ls2)
  (Hnotin : ~ InA eqa a1 ls1),
  forall x : A, InA eqa x ls1 <-> InA eqa x (removeA (eqA:=eqa) Hdec a1 ls2).
Proof.
  intros.
  split; intro Hinx.
    assert (x <> a1) as Heq1.
      intro EQ. subst. auto.
    apply removeA_InA; auto.
    split; auto.
      apply Heq. apply InA_cons_tl; auto.
  
    apply removeA_InA in Hinx; auto.
    destruct Hinx.
    apply Heq in H.
    inv H; auto.
      inv H2. congruence.
Qed.

Lemma NoDupA_eq_length: forall ls1 ls2 (Hndp2: NoDupA eqa ls2)
  (Heq: forall x, InA eqa x ls1 <-> InA eqa x ls2) 
  (Hndp1: NoDupA eqa ls1),
  length ls1 = length ls2.
Proof.
  induction ls1 as [|a1 ls1]; simpl; intros.
    destruct ls2 as [|a2 ls2]; simpl; try solve [omega].
      assert (InA eqa a2 (a2::ls2)) as Hin.
        constructor. reflexivity.
      apply Heq in Hin. inv Hin.

    inv Hndp1.
    assert (Heq':forall x, InA eqa x ls1 <-> 
                           InA eqa x (removeA (eqA:=eqa) Hdec a1 ls2)).
      apply removeA_in_iff; auto.
    apply IHls1 in Heq'; auto.
      rewrite Heq'. 
      apply NoDupA_remove_in_length; auto.
        apply Heq. constructor. reflexivity.
      apply removeA_NoDupA; auto.
Qed.

Lemma NoDupA_remove_length: forall a ls2 (Hndp2: NoDupA eqa ls2)
  (Hin: InA eqa a ls2) ls1 (Hnotin: ~ InA eqa a ls1)   
  (Hinc: forall x, ~ eq x a -> (InA eqa x ls2 <-> InA eqa x ls1)) 
  (Hndp1: NoDupA eqa ls1),
  (S (length ls1) = length ls2)%nat.
Proof.
  intros.
  assert (Heq: forall x, InA eqa x ls1 <-> 
                         InA eqa x (removeA (eqA:=eqa) Hdec a ls2)).
    intros x.
    split; intro Hinx.
      assert (x <> a) as Heq.
        intro EQ. subst. auto.
      apply Hinc in Hinx; auto.
      apply removeA_InA; auto.

      apply removeA_InA in Hinx; auto.
      destruct Hinx.
      apply Hinc; auto.
  apply NoDupA_eq_length in Heq; auto.
    rewrite Heq. apply NoDupA_remove_in_length; auto.
    apply removeA_NoDupA; auto.
Qed.

Lemma NoDupA_add_length: forall a ls2 (Hndp2: NoDupA eqa ls2)
  ls1 (Heq: forall x, InA eqa x ls2 <-> eqa x a \/ InA eqa x ls1)
  (Hndp1: NoDupA eqa ls1),
  (length ls2 <= S (length ls1))%nat.
Proof.
  intros.
  destruct (InA_dec (eqA:=eqa) Hdec a ls1).
  Case "1".
    assert (Heq': forall x, InA eqa x ls1 <-> InA eqa x ls2).
      intros x.
      split; intro J.
        apply Heq; auto.

        apply Heq in J.
        destruct J as [J | J]; auto.
          inv J. auto.
    apply NoDupA_eq_length in Heq'; auto.
    omega.
  Case "2".
    assert (Hinc: forall x, ~ eq x a -> (InA eqa x ls2 <-> InA eqa x ls1)).
      intros.
      split; intro J.
        apply Heq in J.
        destruct J as [J | J]; auto.
          congruence.

        apply Heq; auto.
    apply NoDupA_remove_length in Hinc; auto.
      omega.
      apply Heq. left. reflexivity.
Qed.

Lemma NoDupA__NoDup: forall ls1 (Hndp: NoDupA eqa ls1),
  NoDup ls1.
Proof.
  induction 1.
    constructor.

    constructor; auto.
      intro J. apply H. apply In_InA; auto.
Qed.

End NoDupA_More.

Definition DomMap_gt bd dm1 dm2 : Prop :=
DomMap.in_incr dm1 dm2 /\ exists n, In n bd /\ LDoms.gt (dm2 ?? n) (dm1 ?? n).

Lemma remove_cardinal: forall n s (Hin: PositiveSet.In n s),
(S (PositiveSet.cardinal (PositiveSet.remove n s)) = (PositiveSet.cardinal s))%nat.
Proof.
  intros.
  repeat rewrite PositiveSet.cardinal_1.
  assert (J1:=PositiveSet.elements_3w s).
  assert (J2:=PositiveSet.elements_3w (PositiveSet.remove n s)).
  apply PositiveSet.elements_1 in Hin.
  eapply NoDupA_remove_length; eauto using positive_eq_dec.
    intro J.
    apply PositiveSet.elements_2 in J.
    revert J.
    apply PositiveSet.remove_1; auto.

    intros x Hnotin.
    split; intros Hinx.
      apply PositiveSet.elements_1.
      apply PositiveSet.elements_2 in Hinx.
      apply PositiveSet.remove_2; auto.

      apply PositiveSet.elements_1.
      apply PositiveSet.elements_2 in Hinx.
      apply PositiveSet.remove_3 in Hinx; auto.
Qed.

Lemma add_cardinal: forall n s,
(PositiveSet.cardinal (PositiveSet.add n s) <= S (PositiveSet.cardinal s))%nat.
Proof.
  intros.
  repeat rewrite PositiveSet.cardinal_1.
  assert (J1:=PositiveSet.elements_3w s).
  assert (J2:=PositiveSet.elements_3w (PositiveSet.add n s)).
  eapply NoDupA_add_length with (a:=n); eauto using positive_eq_dec.
    intros x.
    split; intros Hinx.
      apply PositiveSet.elements_2 in Hinx.
      destruct (positive_eq_dec x n); auto.
        right.
        apply PositiveSet.elements_1.
        eapply PositiveSet.add_3 in Hinx; eauto.

      apply PositiveSet.elements_1.
      destruct Hinx as [Hinx | Hinx]; subst.
        apply PositiveSet.add_1; auto.

        apply PositiveSet.elements_2 in Hinx.
        apply PositiveSet.add_2; auto.
Qed.

(***********************************************************)
(* Prove that the analyis must terminate. *)

Module Termination. Section Termination.

Variable successors: PTree.t (list positive).
Definition in_cfg := XPTree.in_cfg successors.

Definition elements_of_cfg : list positive := 
  XPTree.elements_of_cfg successors positive_eq_dec.

Definition psize_of_cfg := (plength elements_of_cfg + 2)%positive.

Definition num_of_doms_fun (dmap: PMap.t LDoms.t) (acc p:positive) : positive :=
  Pplus acc (match dmap ?? p with
             | None => psize_of_cfg
             | Some x => plength x
             end).

Definition num_of_doms (dmap: PMap.t LDoms.t) : positive :=
fold_left (num_of_doms_fun dmap) elements_of_cfg 1%positive.

Definition num_iters := Pcubeplus psize_of_cfg.
Definition psize_of_worklist (wrk: PNodeSetMax.t) : positive :=
(P_of_succ_nat (PositiveSet.cardinal wrk) + 1)%positive.

Definition num_iters_aux (st: DomDS.state) := 
(psize_of_cfg * (num_of_doms (st.(DomDS.st_in))) + 
  psize_of_worklist (st.(DomDS.st_wrk)))%positive.

Lemma elements_of_cfg__lt__psize_of_cfg:
  (plength elements_of_cfg < psize_of_cfg)%positive.
Proof.
  unfold psize_of_cfg. zify; omega.
Qed.

Lemma psize_of_worklist_ge_one: forall wrk,
  (psize_of_worklist wrk > 1)%positive.
Proof.
  unfold psize_of_worklist.
  intros. zify. omega.
Qed.

Hint Unfold num_iters_aux.

Lemma num_iters_aux_gt_one: forall st, (num_iters_aux st > 1)%positive.
Proof.
  intros.
  autounfold.  
  assert (J:=psize_of_worklist_ge_one (DomDS.st_wrk st)).
  zify. omega.
Qed.

Lemma stable_step_decreases_wrk: forall st st'
  (Hstep : DomDS.step successors LDoms.transfer st = inr st')
  (Heq: DomMap.eq elements_of_cfg (st.(DomDS.st_in)) (st'.(DomDS.st_in))),
  exists n, PNodeSetMax.pick st.(DomDS.st_wrk) = Some (n, st'.(DomDS.st_wrk)).
Proof.
  unfold DomDS.step.
  intros.
  case_eq (PNodeSetMax.pick st.(DomDS.st_wrk)).
    intros [max rem] Hpick.
    rewrite Hpick in *. exists max.
    inv Hstep.
    erewrite <- Mono.propagate_succ_list_records_unchanges; eauto.
      simpl. auto.
      apply XPTree.succs_in_elements_of_cfg.

    intros Hpick.
    rewrite Hpick in *. congruence.
Qed.

Lemma stable_step_num_of_doms: forall dm1 dm2 
  (Heq : DomMap.eq elements_of_cfg dm1 dm2),
  num_of_doms dm1 = num_of_doms dm2.
Proof.
  unfold num_of_doms.
  intros.
  revert Heq.
  generalize 1%positive as p.
  generalize elements_of_cfg as l.
  induction l as [|a l]; simpl; auto.
    intros.
    rewrite IHl. 
      f_equal.
      unfold num_of_doms_fun.
      f_equal.
      unfold DomMap.eq in Heq.
      unfold LDoms.eq in Heq.
      rewrite Heq; simpl; auto.

      intros x Hinx.
      apply Heq. simpl; auto.
Qed.

Lemma stable_step_psize_of_worklist: forall wrk wrk' max
  (Hpick : PNodeSetMax.pick wrk = Some (max, wrk')),
  Ppred (psize_of_worklist wrk) = psize_of_worklist wrk'.
Proof.
  intros.
  assert (Hin:=Hpick).
  apply PNodeSetMax.pick_in in Hin.
  apply PNodeSetMax.pick_remove in Hpick.
  rewrite Hpick.
  unfold psize_of_worklist.
  apply remove_cardinal in Hin.
  zify. omega.
Qed.

Lemma Pplus_pminus_spec1: forall p1 p2 p3, 
  (p2 > p3)%positive -> (p1 + (p2 - p3) = p1 + p2 - p3)%positive.
Proof.
  intros. zify. omega.
Qed.

Lemma stable_step_num_iters_aux: forall (st st': DomDS.state)
  (max : PositiveSet.elt)
  (Hpick : PNodeSetMax.pick (DomDS.st_wrk st) = Some (max, DomDS.st_wrk st'))
  (Heq : DomMap.eq elements_of_cfg (DomDS.st_in st) (DomDS.st_in st')),
  num_iters_aux st' = Ppred (num_iters_aux st).
Proof.
  intros.
  autounfold.
  erewrite <- stable_step_num_of_doms; eauto.
  erewrite <- stable_step_psize_of_worklist; eauto.
  repeat rewrite Ppred_minus.
  apply Pplus_pminus_spec1.
    apply psize_of_worklist_ge_one.
Qed.

Lemma propagate_succ_wrk_range:
  forall st out n st' (Heq: st' = DomDS.propagate_succ st out n),
  (psize_of_worklist st'.(DomDS.st_wrk) <=
    (psize_of_worklist st.(DomDS.st_wrk) + 1)%positive)%positive.
Proof.
  unfold DomDS.propagate_succ.
  intros. 
  case_eq (LDoms.lub (DomDS.st_in st) ?? n out).
  intros newl ch Heq'.
  rewrite Heq' in *.
  destruct_if; subst.
    simpl.
    unfold psize_of_worklist, PNodeSetMax.add.
    assert (J:=add_cardinal n (DomDS.st_wrk st)).
    zify; omega.

    zify; omega.
Qed.

Lemma propagate_succ_list_wrk_range:
  forall out scs st st' (Heq: st' = DomDS.propagate_succ_list st out scs),
  (psize_of_worklist st'.(DomDS.st_wrk) <=
    (psize_of_worklist st.(DomDS.st_wrk) + plength scs)%positive)%positive.
Proof.
  induction scs; simpl; intros; subst.
    zify; omega.

    assert
      (psize_of_worklist (DomDS.propagate_succ st out a).(DomDS.st_wrk) <=
        (psize_of_worklist st.(DomDS.st_wrk) + 1)%positive)%positive as J1.
      eapply propagate_succ_wrk_range; eauto.
    assert (DomDS.propagate_succ_list (DomDS.propagate_succ st out a) out scs = 
            DomDS.propagate_succ_list  (DomDS.propagate_succ st out a) out scs) 
      as J2. auto.
    apply IHscs in J2. unfold plength in *. simpl.
    zify; omega.
Qed.

Lemma NoDup_incl_length: forall A (Hdec:forall (x y:A), {x=y}+{x<>y})
  (ls1:list A) (Hnp1: NoDup ls1) ls2
  (Hnp2: NoDup ls2) (Hincl: incl ls1 ls2),
  (length ls1 <= length ls2)%nat.
Proof.
  induction 2; simpl; intros.
    omega.

    assert (incl l (List.remove Hdec x ls2)) as Hinc.
      apply remove_notin_incl; auto.
        eauto with datatypes v62.
    apply IHHnp1 in Hinc; auto.
      assert (In x ls2) as Hin. 
        eauto with datatypes v62.
      apply remove_in_length with (Hdec:=Hdec) in Hin.
      omega. 

      apply NoDup_remove; auto.
Qed.

Lemma wrk_in_cfg__psize_of_worklist_lt_psize_of_cfg: forall st
  (Hwf : WorklistProps.wf_state successors st),
  (psize_of_worklist st.(DomDS.st_wrk) < psize_of_cfg)%positive.
Proof.
  intros.
  unfold  WorklistProps.wf_state in Hwf.
  unfold psize_of_worklist, psize_of_cfg.
  rewrite PositiveSet.cardinal_1.
  assert (length (PositiveSet.elements (DomDS.st_wrk st)) <=
            length elements_of_cfg)%nat as Hle.
    eapply NoDup_incl_length; eauto using positive_eq_dec.
    Case "1".
      apply NoDupA__NoDup.
      apply PositiveSet.elements_3w.
    Case "2".
      apply remove_redundancy_NoDup; auto.
    Case "3".
      intros x Hinx. 
      assert (InA PositiveSet.E.eq x (PositiveSet.elements (DomDS.st_wrk st))) 
        as Hinx'.
        apply InA_alt. unfold PositiveSet.E.eq. eauto.
      apply PositiveSet.elements_2 in Hinx'.
      apply Hwf in Hinx'.
      apply remove_redundancy_in; auto.
      apply in_or_app. auto.
  unfold plength. zify; omega.     
Qed.

Lemma instable_step_wrk_range: forall st st'
  (Hwf: WorklistProps.wf_state successors st)
  (Hstep : DomDS.step successors LDoms.transfer st = inr st'),
  (psize_of_worklist st'.(DomDS.st_wrk) <
    psize_of_worklist st.(DomDS.st_wrk) + psize_of_cfg)%positive.
Proof.
  intros.
  apply WorklistProps.step_wf_state in Hstep; auto.
  apply wrk_in_cfg__psize_of_worklist_lt_psize_of_cfg in Hstep.
  zify; omega.
Qed.

Lemma ge__gt_or_eq: forall x y (Hsort: SortedDoms.wf_dom y) (Hge: LDoms.ge x y),
  LDoms.eq x y \/ LDoms.gt x y.
Proof.
  unfold LDoms.ge, LDoms.gt.
  intros.
  destruct x as [x|].
    destruct y as [y|]; auto.
      simpl in Hsort.
      apply Plt_Sorted__StronglySorted in Hsort.
      apply Plt_StronglySorted_NoDup in Hsort.
      assert (J:=Hge).
      apply sublist__eq_or_exact in J; auto.
      destruct J as [EQ | [e [Hin Hnotin]]]; subst.
        left. reflexivity.
        right. split; eauto.
    left.
    destruct y as [y|]; try tauto.
      reflexivity.
Qed.

Lemma DomMap_in_incr__gt_or_eq: forall dm1 dm2 
  (Hsort: SortedDoms.wf_doms dm1)
  (Hincr: DomMap.in_incr dm1 dm2) bd,
  DomMap.eq bd dm1 dm2 \/ DomMap_gt bd dm1 dm2.
Proof.
  induction bd; simpl; intros.
    left.
    intros x Hinx. tauto.

    assert (G:=Hincr a).
    assert (G':=Hsort).
    eapply SortedDoms.wf_doms__wf_dom with (n:=a) in G'; eauto.
    destruct (ge__gt_or_eq (dm2??a) (dm1??a)) as [J | J]; auto.
      destruct IHbd as [IHbd | IHbd].
        left.
        intros x Hinx.
        destruct_in Hinx.
          apply IHbd in Hinx; auto.
       
       right.
       split; auto.
         destruct IHbd as [_ [n [J1 J2]]]. 
         exists n.
         simpl; auto.

     right.
     split; auto.
       exists a.
       simpl; auto.
Qed.

Definition doms_lt_psize_of_cfg (dm2:PMap.t LDoms.t) :=
  forall (p2:positive) sds2 
    (Heq: dm2 ?? p2 = Some sds2), (plength sds2 < psize_of_cfg)%positive.

Lemma ge__num_of_doms_fun__le_le: forall (dm1 dm2:PMap.t LDoms.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  (p2 p1 : positive) (Hle : (p2 <= p1)%positive) a
  (J : LDoms.ge dm2 ?? a dm1 ?? a),
  (num_of_doms_fun dm2 p2 a <= num_of_doms_fun dm1 p1 a)%positive.
Proof.
  intros.
  unfold num_of_doms_fun.
  unfold LDoms.ge in J.
  case_eq (dm1 ?? a).
    intros l0 Heq0. rewrite Heq0 in *.
    case_eq (dm2 ?? a).
      intros l1 Heq1. rewrite Heq1 in *.
      apply sublist_length in J; auto using positive_eq_dec.
      unfold plength. zify; omega.
  
      intros Heq1. rewrite Heq1 in *. tauto.
  
    intros Heq0. rewrite Heq0 in *. 
    case_eq (dm2 ?? a).
      intros l1 Heq1. rewrite Heq1 in *.
      apply Hincfg in Heq1.
      zify; omega.
  
      intros Heq1. rewrite Heq1 in *.
      zify; omega.
Qed.

Lemma ge__num_of_doms_fun__lt_lt: forall (dm1 dm2:PMap.t LDoms.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  (p2 p1 : positive) (Hle : (p2 < p1)%positive) a
  (J : LDoms.ge dm2 ?? a dm1 ?? a),
  (num_of_doms_fun dm2 p2 a < num_of_doms_fun dm1 p1 a)%positive.
Proof.
  intros.
  unfold num_of_doms_fun.
  unfold LDoms.ge in J.
  case_eq (dm1 ?? a).
    intros l0 Heq0. rewrite Heq0 in *.
    case_eq (dm2 ?? a).
      intros l1 Heq1. rewrite Heq1 in *.
      apply sublist_length in J; auto using positive_eq_dec.
      unfold plength. zify; omega.
  
      intros Heq1. rewrite Heq1 in *. tauto.
  
    intros Heq0. rewrite Heq0 in *. 
    case_eq (dm2 ?? a).
      intros l1 Heq1. rewrite Heq1 in *.
      apply Hincfg in Heq1.
      zify; omega.
  
      intros Heq1. rewrite Heq1 in *.
      zify; omega.
Qed.

Lemma ge__num_of_doms_fun__lt_le: forall (dm1 dm2:PMap.t LDoms.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  (p2 p1 : positive) (Hle : (p2 < p1)%positive) a
  (J : LDoms.ge dm2 ?? a dm1 ?? a),
  (num_of_doms_fun dm2 p2 a <= num_of_doms_fun dm1 p1 a)%positive.
Proof.
  intros.
  eapply ge__num_of_doms_fun__lt_lt in J; eauto.
  zify; omega.
Qed.

Lemma incr_num_of_doms: forall (dm1 dm2:PMap.t LDoms.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  (Hlt : DomMap.in_incr dm1 dm2) bd p2 p1 (Hle: (p2 < p1)%positive),
  (fold_left (num_of_doms_fun dm2) bd p2 <
    fold_left (num_of_doms_fun dm1) bd p1)%positive.
Proof.
  unfold num_of_doms.
  intros dm1 dm2 Hincfg.
  induction bd as [|a bd]; simpl; intros; auto.
    apply IHbd; auto.
      assert (J:=Hlt a).
      apply ge__num_of_doms_fun__lt_lt; auto.
Qed.

Lemma gt__num_of_doms_fun__le_lt: forall (dm1 dm2:PMap.t LDoms.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  (p2 p1 : positive) (Hle : (p2 <= p1)%positive) a
  (J : LDoms.gt dm2 ?? a dm1 ?? a),
  (num_of_doms_fun dm2 p2 a < num_of_doms_fun dm1 p1 a)%positive.
Proof.
  intros.
  unfold num_of_doms_fun.
  unfold LDoms.gt in J.
  case_eq (dm1 ?? a).
    intros l0 Heq0. rewrite Heq0 in *.
    case_eq (dm2 ?? a).
      intros l1 Heq1. rewrite Heq1 in *.
      destruct J as [J J'].
      apply exact_sublist_length in J; auto using positive_eq_dec.
      unfold plength. zify; omega.
  
      intros Heq1. rewrite Heq1 in *. tauto.
  
    intros Heq0. rewrite Heq0 in *. 
    case_eq (dm2 ?? a).
      intros l1 Heq1. rewrite Heq1 in *.
      apply Hincfg in Heq1.
      zify; omega.
  
      intros Heq1. rewrite Heq1 in *.
      zify; omega.
Qed.

Lemma gt__num_of_doms__le_lt: forall (dm1 dm2:PMap.t LDoms.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  bd (Hlt : DomMap_gt bd dm1 dm2) p2 p1 (Hle: (p2 <= p1)%positive),
  (fold_left (num_of_doms_fun dm2) bd p2 <
    fold_left (num_of_doms_fun dm1) bd p1)%positive.
Proof.
  intros dm1 dm2 Hincfg.
  unfold DomMap_gt.
  induction bd as [|a bd]; simpl; intros.
    destruct_conjs. tauto.

    destruct Hlt as [Hincr [n [Hin Hlt]]].
    destruct Hin as [Hin | Hin]; subst.
      eapply gt__num_of_doms_fun__le_lt in Hlt; eauto.
      apply incr_num_of_doms; auto.

      apply IHbd; eauto.
      eapply ge__num_of_doms_fun__le_le; eauto.
Qed.

Lemma gt_num_of_doms: forall (dm1 dm2:PMap.t LDoms.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  (Hlt : DomMap_gt elements_of_cfg dm1 dm2),
  (num_of_doms dm2 < num_of_doms dm1)%positive.
Proof.
  unfold num_of_doms.
  intros.
  apply gt__num_of_doms__le_lt; auto.
    zify; omega.
Qed.

Lemma instable_step_num_iters_aux: forall (st st': DomDS.state)
  (Hwf: WorklistProps.wf_state successors st)
  (Hincfg: doms_lt_psize_of_cfg (st'.(DomDS.st_in)))
  (Hstep : DomDS.step successors LDoms.transfer st = inr st')
  (Hlt : DomMap_gt elements_of_cfg (DomDS.st_in st) (DomDS.st_in st')),
  (num_iters_aux st' + 1 <= (num_iters_aux st))%positive.
Proof.
  intros.
  autounfold.
  apply gt_num_of_doms in Hlt; auto.
  apply instable_step_wrk_range in Hstep; auto.
  revert Hlt Hstep.
  generalize (num_of_doms (DomDS.st_in st')) as A. 
  generalize (num_of_doms (DomDS.st_in st)) as B.
  generalize (psize_of_worklist (DomDS.st_wrk st)) as C. 
  generalize (psize_of_worklist (DomDS.st_wrk st')) as D.
  generalize (psize_of_cfg) as E.
  intros.
  assert (E * A + E = E * (A + 1))%positive as J2.
    rewrite Pmult_plus_distr_l.
    zify. omega.
  assert (E * (A + 1) <= E * B)%positive as J4.
    zify.
    apply Zmult_le_compat_l; omega.
  zify. omega.
Qed.

Lemma doms_in_parants__doms_lt_psize_of_cfg: forall dms
  (Hsort: SortedDoms.wf_doms dms)
  (Hwf : DomsInParents.wf_doms successors dms),
  doms_lt_psize_of_cfg dms.
Proof.
  intros.
  intros n sds Hget.
  assert (J:=Hwf n). 
  assert (J':=Hsort n). 
  rewrite Hget in J. simpl in J.
  rewrite Hget in J'. simpl in J'.
  unfold psize_of_cfg.
  assert (length sds <= length elements_of_cfg)%nat as Hle.
    eapply NoDup_incl_length; eauto using positive_eq_dec.
    Case "1".
      apply Plt_Sorted__StronglySorted in J'.
      inv J'.
      apply Plt_StronglySorted_NoDup; auto.
    Case "2".
      apply remove_redundancy_NoDup; auto.
    Case "3".
      intros x Hinx. 
      apply remove_redundancy_in; auto.
      apply in_or_app. auto.
  unfold plength. zify; omega.     
Qed.

Definition fixpoint_iter_P := 
  (fun ni => 
     forall st 
     (Hbound: (ni >= num_iters_aux st)%positive)
     (Hwf1: DomsInParents.wf_doms successors (DomDS.st_in st))
     (Hwf2: SortedDoms.wf_state successors st),
     exists res : PMap.t LDoms.t,
       PrimIter.iter DomDS.state (PMap.t LDoms.t)
         (DomDS.step successors LDoms.transfer) ni
         st = Some res).

Lemma fixpoint_iter: forall ni, fixpoint_iter_P ni.
Proof.
  apply (well_founded_ind Plt_wf fixpoint_iter_P). 
  unfold fixpoint_iter_P. intros.
  rewrite PrimIter.unroll_iter.
  unfold PrimIter.iter_step. 
  case (peq x 1); intro.
  Case "x=1".
    subst x.
    contradict Hbound.    
    assert (J:=num_iters_aux_gt_one st).
    zify; omega.

  Case "x<>1".
    case_eq (DomDS.step successors LDoms.transfer st); eauto.
    intros st' Hstep.
    assert (DomsInParents.wf_doms successors (DomDS.st_in st')) as Hwf1'.
      eapply DomsInParents.step_wf_doms; eauto.
    assert (SortedDoms.wf_state successors st') as Hwf2'.
      eapply SortedDoms.step_wf_state; eauto.
    apply H; auto.
    SCase "1".
      apply Ppred_Plt; auto. 
    SCase "2".
      destruct Hwf2 as [Hwf21 [_ [_ Hwf24]]].
      destruct Hwf2' as [_ [_ [_ Hwf24']]].
      assert (Hmono:=Hstep).
      apply Mono.step_wf in Hmono.
      apply DomMap_in_incr__gt_or_eq with (bd:=elements_of_cfg) in Hmono; auto.
      destruct Hmono as [Heq | Hgt].
      SSCase "2.1".
        apply stable_step_decreases_wrk in Hstep; auto.
        destruct Hstep as [max Hpick].
        erewrite stable_step_num_iters_aux; eauto.
        clear - Hbound n. zify; omega.
      SSCase "2.2".
        eapply instable_step_num_iters_aux in Hgt; eauto.
        SSSCase "2.2.1".
          zify; omega.
        SSSCase "2.2.2".
          apply doms_in_parants__doms_lt_psize_of_cfg; auto. 
Qed.

Lemma doms_lt_psize_of_cfg__num_of_doms: forall dms 
  (Hwf: doms_lt_psize_of_cfg dms) bd (p:positive),
  (plength bd * psize_of_cfg + p >=
    fold_left (num_of_doms_fun dms) bd p)%positive.
Proof.
  unfold plength.
  induction bd; simpl; intros.
    zify; omega.
    
    assert (J:=IHbd (num_of_doms_fun dms p a)%positive).
    assert (num_of_doms_fun dms p a <= p + psize_of_cfg)%positive as J'.
      unfold num_of_doms_fun.
      case_eq (dms ?? a).
        intros l Heq.
        apply Hwf in Heq. zify; omega.

        intros Heq. zify; omega.
        revert J J'.
        generalize (P_of_succ_nat (length bd)) as B.
        generalize (psize_of_cfg) as D.
        intros.
        assert (Psucc B = (B + 1))%positive as EQ.
          zify; omega.
        rewrite EQ. clear EQ. 
        assert ((B + 1) * D = B * D + D)%positive as EQ.
          rewrite Pmult_plus_distr_r.
          zify; omega.
        zify ; omega.
Qed.

Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Lemma entry_psize_of_worklist:
  (psize_of_cfg >=
     psize_of_worklist
       (DomDS.st_wrk (DomDS.start_state successors entrypoints)))%positive.
Proof.
  assert (J:=WorklistProps.entrypoints_wf_state successors entrypoints).
  apply wrk_in_cfg__psize_of_worklist_lt_psize_of_cfg in J.
  simpl in *. zify; omega.
Qed.

Definition predecessors := XPTree.make_predecessors successors.

Hypothesis wf_order: forall n (Hneq: n <> entrypoint)
  (Hincfg: XPTree.in_cfg successors n),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.

Lemma entry_num_of_doms:
  (psize_of_cfg * psize_of_cfg >=
   num_of_doms (DomDS.st_in (DomDS.start_state successors entrypoints)))%positive.
Proof.
  unfold num_of_doms.
  assert (J:=elements_of_cfg__lt__psize_of_cfg).
  assert (doms_lt_psize_of_cfg 
           (DomDS.st_in (DomDS.start_state successors entrypoints))) as J'.
    assert (G:=SortedDoms.entrypoints_wf_state successors entrypoint wf_order).
    assert (G':=DomsInParents.start_wf_doms successors entrypoint).
    destruct G as [_ [_ [_ G]]].
    apply doms_in_parants__doms_lt_psize_of_cfg; auto.
  apply doms_lt_psize_of_cfg__num_of_doms 
    with (p:=xH)(bd:=elements_of_cfg) in J'.
  revert J J'.
  generalize (fold_left
               (num_of_doms_fun
                  (DomDS.st_in (DomDS.start_state successors entrypoints)))
               elements_of_cfg xH).
  generalize (plength elements_of_cfg).
  generalize (psize_of_cfg).
  intros A B C. intros.
  assert (B * A + A = (B+1) * A)%positive.
    rewrite Pmult_plus_distr_r.
    zify; omega.
  assert ((B+1) * A <= A * A)%positive.
    zify.
    apply Zmult_le_compat_r; omega.
  zify; omega.
Qed.

Lemma num_iters__ge__num_iters_aux: 
  (num_iters >= 
    num_iters_aux (DomDS.start_state successors entrypoints))%positive.
Proof.
  unfold num_iters, num_iters_aux, Pcubeplus. 
  assert (J1:=entry_num_of_doms).
  assert (J2:=entry_psize_of_worklist).
  revert J1 J2.
  generalize 
    (num_of_doms (DomDS.st_in (DomDS.start_state successors entrypoints))) 
    as C.
  intros C. intros.
  assert (psize_of_cfg * (psize_of_cfg * psize_of_cfg) >= psize_of_cfg * C)%positive.
    zify. apply Zmult_ge_compat_l; omega.
  zify. omega.
Qed.

Lemma fixpoint_wf: forall ni (Hge: (ni >= num_iters)%positive),
  exists res, 
    DomDS.fixpoint successors LDoms.transfer entrypoints ni = Some res.
Proof.
  intros.
  apply fixpoint_iter.
  Case "1".
    assert (J:=num_iters__ge__num_iters_aux).
    zify. omega.
  Case "2". eapply DomsInParents.start_wf_doms; eauto.
  Case "3". eapply SortedDoms.entrypoints_wf_state; eauto.
Qed.

End Termination. End Termination.

Ltac termination_tac :=
match goal with
| Hlarge_enough: (?ni >= Termination.num_iters ?successors)%positive |- _ =>
    let J:=fresh "J" in 
    assert (J:=Hlarge_enough);
    eapply Termination.fixpoint_wf in J; eauto;
    destruct J as [dms Hfix_tmn];
    unfold Termination.entrypoints in Hfix_tmn;
    rewrite Hfix_tmn in *
end.

(***************************************************)
(* Unreachable nodes are dominated by any nodes. *)

Module UnreachableDoms. Section UnreachableDoms.

Variable successors: PTree.t (list positive).
Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Definition wf_doms (res: PMap.t LDoms.t) : Prop :=
  forall n0 (Hunreach: ~ PCfg.reachable successors entrypoint n0) 
    (Hneq: n0 <> entrypoint),
    LDoms.eq res??n0 LDoms.bot.

Lemma start_wf_doms:
  wf_doms (DomDS.st_in (DomDS.start_state successors entrypoints)).
Proof.
  intros n0 Hunreach Hneq. simpl.
  eapply dom_nonentry_start_state_in in Hneq; eauto.
Qed.

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma propagate_succ_wf_doms: forall st n out
  (Hp: ~ PCfg.reachable successors entrypoint n -> 
       n <> entrypoint -> LDoms.eq out LDoms.bot)
  (Hwf: wf_doms st.(DomDS.st_in)),
  wf_doms (DomDS.propagate_succ st out n).(DomDS.st_in).
Proof.
  unfold wf_doms.
  intros.
  destruct (propagate_succ_spec st out n) as [J1 J2].
  assert (Hunreach':=Hunreach).
  apply Hwf in Hunreach; auto.
  destruct (positive_eq_dec n n0); subst.
    apply Hp in Hunreach'; auto.
    apply LDoms.eq_trans with
      (y:=fst (LDoms.lub (DomDS.st_in st) ?? n0 out)); auto.
    rewrite Hunreach'. rewrite Hunreach. simpl. apply LDoms.eq_refl.

    rewrite J2; auto.
Qed.

Lemma propagate_succ_list_wf_doms: forall scs st out
  (H: forall s, In s scs ->
             ~ PCfg.reachable successors entrypoint s -> s <> entrypoint ->
             LDoms.eq out LDoms.bot)
  (Hwf: wf_doms st.(DomDS.st_in)),
  wf_doms (DomDS.propagate_succ_list st out scs).(DomDS.st_in).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs.
      intros. apply H with (s:=s); auto.
      apply propagate_succ_wf_doms; auto.
        intros J1 J2. eapply H; eauto.
Qed.

Hypothesis wf_entrypoints: in_cfg successors entrypoint.

Lemma step_wf_doms:
  forall st n rem
  (WKL: PNodeSetMax.pick st.(DomDS.st_wrk) = Some(n, rem))
  (GOOD: wf_doms st.(DomDS.st_in)),
  wf_doms (DomDS.propagate_succ_list
                                  (DomDS.mkstate st.(DomDS.st_in) rem)
                                  (LDoms.transfer n st.(DomDS.st_in)??n)
                                  (successors???n)).(DomDS.st_in).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_wf_doms; auto.
  intros s Hin Hunreach.
  destruct (PCfg.reachable_dec successors entrypoint n).
  Case "1".
    apply PCfg.reachable_succ with (sc:=s) in H; auto.
    congruence.
  Case "2".
    apply GOOD in H. simpl in H.
    intros Hneq.
    destruct (positive_eq_dec n entrypoint); subst.
    SCase "2.1".
      contradict Hunreach.
      unfold reachable.
      exists (index entrypoint::nil). 
      exists (A_ends (index s) (index entrypoint)::nil).
      constructor; auto.
        constructor; auto.
        eapply XPTree.in_succ__in_cfg; eauto.

    SCase "2.2".
      rewrite H; auto. simpl. 
      unfold LDoms.eq, LDoms.bot. auto.
Qed.

Variable ni:positive.

Theorem fixpoint_wf: forall res,
  DomDS.fixpoint successors LDoms.transfer entrypoints ni = Some res ->
  wf_doms res.
Proof.
  unfold DomDS.fixpoint. intros res PI. pattern res.
  eapply (PrimIter.iter_prop _ _ (DomDS.step successors LDoms.transfer)
    (fun st => wf_doms st.(DomDS.st_in))); eauto.
    intros st GOOD. unfold DomDS.step.
    caseEq (PNodeSetMax.pick st.(DomDS.st_wrk)); auto.
    intros [n rem] PICK.
    apply step_wf_doms; auto.

    apply start_wf_doms.
Qed.

Lemma fixpoint_reachable: forall n res dts
  (Hfix: DomDS.fixpoint successors LDoms.transfer entrypoints ni = Some res)
  (Hdom: res ?? n = Some dts),
  PCfg.reachable successors entrypoint n.
Proof.
  intros.
  destruct (positive_eq_dec n entrypoint); subst.
    apply PCfg.reachable_entry; auto.
    destruct (PCfg.reachable_dec successors entrypoint n) as [H|H]; auto.
      apply fixpoint_wf in Hfix.
      assert (J:=Hfix n). 
      apply J in H; auto.
      rewrite Hdom in H. inv H.
Qed.

End UnreachableDoms. End UnreachableDoms.

(***************************************************)
(* The entry point dominates all other nodes. *)

Module EntryDomsOthers. Section EntryDomsOthers.

Variable successors: PTree.t (list positive).
Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.
Definition predecessors := XPTree.make_predecessors successors.

Definition wf_doms (res: PMap.t LDoms.t) : Prop :=
  forall n0 (Hneq: n0 <> entrypoint), member successors entrypoint res??n0.

Hypothesis wf_entrypoints: in_cfg successors entrypoint.

Lemma start_wf_doms:
  wf_doms (DomDS.st_in (DomDS.start_state successors entrypoints)).
Proof.
  intros n0 Hneq.
  apply dom_nonentry_start_state_in in Hneq.
  unfold DomDS.start_state. simpl in *. rewrite Hneq.
  simpl. auto.
Qed.

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma propagate_succ_wf_doms: forall st n out
  (Hsorted_doms: SortedDoms.wf_doms st.(DomDS.st_in)) 
  (Hsorted_out: SortedDoms.wf_dom out)
  (Hin: member successors entrypoint out)
  (Hwf: wf_doms st.(DomDS.st_in)),
  wf_doms (DomDS.propagate_succ st out n).(DomDS.st_in).
Proof.
  unfold wf_doms.
  intros.
  destruct (propagate_succ_spec st out n) as [J1 J2].
  apply Hwf in Hneq.
  destruct (positive_eq_dec n n0); subst.
    rewrite J1. 
    apply member_lub; auto using SortedDoms.wf_doms__wf_dom.

    rewrite J2; auto.
Qed.

Lemma propagate_succ_list_wf_doms:
  forall p scs st (Hwf: SortedDoms.wf_doms (DomDS.st_in st)) 
                  (Hwf0: LtDoms.wf_doms (DomDS.st_in st))
  (Horder: forall n (Hin: In n scs) (Hbot: (DomDS.st_in st) ?? n = None),
             (p > n)%positive),
  let out := LDoms.transfer p (DomDS.st_in st) ?? p in
  member successors entrypoint out ->
  wf_doms st.(DomDS.st_in) ->
  wf_doms (DomDS.propagate_succ_list st out scs).(DomDS.st_in).
Proof.
  induction scs as [|a scs]; simpl; intros; auto.

  set (out:=LDoms.transfer p (DomDS.st_in st) ?? p).
  set (st':=DomDS.propagate_succ st out a).
  assert (LtDoms.wf_doms (DomDS.st_in st')) as Hwf0'.
    apply LtDoms.propagate_succ_wf_doms; auto.
  assert (SortedDoms.wf_doms (DomDS.st_in st')) as Hwf'.
    apply SortedDoms.propagate_succ_wf_doms; auto.
  assert (SortedDoms.wf_dom (LDoms.transfer p (DomDS.st_in st) ?? p)) 
    as Hsorted_out.
    apply SortedDoms.wf_doms__wf_transfer_dom; auto.
  assert (forall (n : positive) (Hin: In n scs) 
            (Hbot: (DomDS.st_in st') ?? n = None), (p > n)%positive) as Horder'.
    intros. apply propagate_succ_bot_inv in Hbot. auto.
  assert (H':=H). 
  rewrite LtDoms.propagate_succ_self_stable with (n:=a) in H'; auto.
  generalize (IHscs st' Hwf' Hwf0' Horder' H'). intros A.
  generalize (propagate_succ_wf_doms st a out Hwf). intros C.
  subst out st'. 
  repeat (rewrite <- LtDoms.propagate_succ_self_stable in A at 1; auto).
Qed.

Lemma step_wf_doms:
  forall st n rem (Hwf: SortedDoms.wf_state successors st),
  PNodeSetMax.pick st.(DomDS.st_wrk) = Some(n, rem) ->
  wf_doms st.(DomDS.st_in) ->
  wf_doms (DomDS.propagate_succ_list
             (DomDS.mkstate st.(DomDS.st_in) rem)
             (LDoms.transfer n st.(DomDS.st_in)??n)
             (successors???n)).(DomDS.st_in).
Proof.
  intros st n rem Hwf WKL GOOD.

  destruct Hwf as [Hwf1 [Hwf2 [Hwf3 Hwf4]]].
  assert (Horder: forall sc (Hin: In sc (successors???n)) 
             (Hbot: (DomDS.st_in st) ?? sc = None),
             (n > sc)%positive).
    eapply InitOrder.pick_gt_bot_successors; eauto.
  destruct st. simpl.
  apply propagate_succ_list_wf_doms; auto.
    simpl in *.
    destruct (positive_eq_dec n entrypoint); subst.     
      apply add_member1; auto.

      apply GOOD in n0.
      apply add_member2; auto.
Qed.

Hypothesis wf_order: forall n (Hneq: n <> entrypoint)
  (Hincfg: XPTree.in_cfg successors n),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.

Theorem fixpoint_wf_doms: forall res ni,
  DomDS.fixpoint successors LDoms.transfer entrypoints ni = Some res ->
  wf_doms res.
Proof.
  unfold DomDS.fixpoint. intros res ni PI. pattern res.
  eapply (PrimIter.iter_prop _ _ (DomDS.step successors LDoms.transfer)
    (fun st => SortedDoms.wf_state successors st /\
               wf_doms st.(DomDS.st_in))); eauto.
  Case "1".
    intros st [WF GOOD]. unfold DomDS.step.
    caseEq (PNodeSetMax.pick st.(DomDS.st_wrk)); auto.
    intros [n rem] PICK.
    split.
      apply SortedDoms.propagate_succ_list_wf_state; auto.       
      apply step_wf_doms; auto.
  Case "2".   
    split.
      apply SortedDoms.entrypoints_wf_state; auto.
      apply start_wf_doms.
Qed.

End EntryDomsOthers. End EntryDomsOthers.

(***************************************************)
(* The completeness of the analysis. *)

(* Inequations, EntryDomsOthers and DomComplete should be 
   generalized by parametering SortedDoms and LtDoms *)
Module DomComplete. Section DomComplete.

Variable successors: PTree.t (list positive).
Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.
Definition predecessors := XPTree.make_predecessors successors.

Hint Unfold predecessors.

Definition non_sdomination (n1 n2:positive) : Prop :=
  PCfg.non_sdomination successors entrypoint n1 n2.

Definition wf_doms (res: PMap.t LDoms.t) : Prop :=
  forall n1 n2 (Hincfg: PCfg.vertexes successors (index n1)) 
    (Hnotdom: ~ member successors n1 res??n2),
    non_sdomination n1 n2.

Hypothesis wf_entrypoints: in_cfg successors entrypoint.

Lemma start_wf_doms:
  wf_doms (DomDS.st_in (DomDS.start_state successors entrypoints)).
Proof.
  intros n1 n2 Hin Hnotin.
  destruct (positive_eq_dec n2 entrypoint); try subst n2.
    unfold non_sdomination.
    exists V_nil. exists A_nil.
    split.
      constructor. simpl. tauto.
      intro J. inv J.

    eapply dom_nonentry_start_state_in in n; eauto.
    contradict Hnotin. simpl in *. rewrite n. auto.
Qed.

Hint Resolve positive_eq_dec: positive.

Lemma non_sdomination_refl : forall n1
  (Hneq: n1 <> entrypoint) (Hreach: PCfg.reachable successors entrypoint n1),
  non_sdomination n1 n1.
Proof.
  unfold reachable, non_sdomination. 
  intros.
  apply PCfg.non_sdomination_refl; auto with positive.
Qed.

Lemma propagate_succ_wf_doms: forall st p n out
  (Hsorted_doms: SortedDoms.wf_doms st.(DomDS.st_in)) 
  (Hsorted_out: SortedDoms.wf_dom out)
  (Hinpds: In p predecessors???n)
  (Hout: LDoms.ge (LDoms.transfer p st.(DomDS.st_in)??p) out)
  (Hdom: wf_doms st.(DomDS.st_in)),
  wf_doms (DomDS.propagate_succ st out n).(DomDS.st_in).
Proof.
  unfold wf_doms. intros.
  destruct (@propagate_succ_spec st out n) as [J1 J2].
  destruct (positive_eq_dec n n2) as [Heq | Hneq]; subst.
  Case "n=n2".
    destruct (member_dec successors n1 (DomDS.st_in st) ?? n2)
      as [Hin12 | Hnotin12]; auto.
    assert (Hnotlub12:=Hnotdom).
    rewrite J1 in Hnotlub12; auto.
    clear J1 J2.
    destruct (member_dec successors n1 out) as [Hinout | Hnotout]; auto.
    SCase "l1 in out".
      contradict Hnotlub12. 
      apply member_lub; auto using SortedDoms.wf_doms__wf_dom.
    SCase "l1 notin out".
      assert (~ member successors n1 (LDoms.transfer p (DomDS.st_in st) ?? p))
        as Hnotintransf.
        intro J. apply Hnotout.
        eapply ge_elim in Hout; eauto.
      assert (n1 <> p /\ ~ member successors n1 (DomDS.st_in st)??p) as J.
        split; intro J; subst; apply Hnotintransf.
          apply add_member1; auto.
          apply add_member2; auto.
      clear Hnotintransf.
      destruct J as [Hneq J].
      apply Hdom in J; auto.
      destruct J as [vl [al [J1 J2]]].
      exists (index p::vl). exists (A_ends (index n2) (index p)::al).
      split.
      SSCase "1".
        apply XPTree.make_predecessors_correct' in Hinpds.
        constructor; auto.
          eapply XPTree.in_succ__in_cfg; eauto.

      SSCase "2".
        intro J. simpl in J.
        destruct J as [J | J]; auto.
          inv J. auto.
  Case "n<>n2".
    rewrite J2 in Hnotdom; auto.
Qed.

Lemma propagate_succ_list_wf_doms:
  forall p scs st (Hwf: SortedDoms.wf_doms (DomDS.st_in st)) 
                  (Hwf0: LtDoms.wf_doms (DomDS.st_in st))
  (Horder: forall n (Hin: In n scs) (Hbot: (DomDS.st_in st) ?? n = None),
             (p > n)%positive),
  let out := LDoms.transfer p (DomDS.st_in st) ?? p in
  (forall s, In s scs -> In p predecessors???s) ->
  wf_doms st.(DomDS.st_in) ->
  wf_doms (DomDS.propagate_succ_list st out scs).(DomDS.st_in).
Proof.
  induction scs as [|a scs]; simpl; intros; auto.

  set (out:=LDoms.transfer p (DomDS.st_in st) ?? p).
  set (st':=DomDS.propagate_succ st out a).
  assert (LtDoms.wf_doms (DomDS.st_in st')) as Hwf0'.
    apply LtDoms.propagate_succ_wf_doms; auto.
  assert (SortedDoms.wf_doms (DomDS.st_in st')) as Hwf'.
    apply SortedDoms.propagate_succ_wf_doms; auto.
  assert (SortedDoms.wf_dom (LDoms.transfer p (DomDS.st_in st) ?? p)) 
    as Hsorted_out.
    apply SortedDoms.wf_doms__wf_transfer_dom; auto.
  assert (forall (n : positive) (Hin: In n scs) 
            (Hbot: (DomDS.st_in st') ?? n = None), (p > n)%positive) as Horder'.
    intros. apply propagate_succ_bot_inv in Hbot. auto.
  assert (forall s : positive, In s scs -> In p predecessors ??? s) as H' 
    by auto.
  generalize (IHscs st' Hwf' Hwf0' Horder' H'). intros A.
  generalize (propagate_succ_wf_doms st p a out Hwf). intros C.
  subst out st'. 
  repeat (rewrite <- LtDoms.propagate_succ_self_stable in A at 1; 
            auto using LDoms.ge_refl).
Qed.

Lemma step_wf_doms:
  forall st n rem (Hwf: SortedDoms.wf_state successors st),
  PNodeSetMax.pick st.(DomDS.st_wrk) = Some(n, rem) ->
  wf_doms st.(DomDS.st_in) ->
  wf_doms (DomDS.propagate_succ_list
                                 (DomDS.mkstate st.(DomDS.st_in) rem)
                                 (LDoms.transfer n st.(DomDS.st_in)??n)
                                 (successors???n)).(DomDS.st_in).
Proof.
  intros st n rem Hwf WKL GOOD.
  destruct Hwf as [Hwf1 [Hwf2 [Hwf3 Hwf4]]].
  assert (Horder: forall sc (Hin: In sc (successors???n)) 
             (Hbot: (DomDS.st_in st) ?? sc = None),
             (n > sc)%positive).
    eapply InitOrder.pick_gt_bot_successors; eauto.
  destruct st. simpl.
  apply propagate_succ_list_wf_doms; auto.
    apply XPTree.make_predecessors_correct.
Qed.

Hypothesis wf_order: forall n (Hneq: n <> entrypoint)
  (Hincfg: XPTree.in_cfg successors n),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.

Theorem fixpoint_wf: forall res ni,
  DomDS.fixpoint successors LDoms.transfer entrypoints ni = Some res ->
  wf_doms res.
Proof.
  unfold DomDS.fixpoint. intros res ni PI. pattern res.
  eapply (PrimIter.iter_prop _ _ (DomDS.step successors LDoms.transfer)
    (fun st => SortedDoms.wf_state successors st /\
               wf_doms st.(DomDS.st_in))); eauto.
  Case "1".
    intros st [WF GOOD]. unfold DomDS.step.
    caseEq (PNodeSetMax.pick st.(DomDS.st_wrk)); auto.
    intros [n rem] PICK. 
    split.
      apply SortedDoms.propagate_succ_list_wf_state; auto.       
      apply step_wf_doms; auto.
  Case "2".   
    split.
      apply SortedDoms.entrypoints_wf_state; auto.
      apply start_wf_doms.
Qed.

End DomComplete. End DomComplete.

(*****************************************************************)
(*The soundness of the analysis. *)

Require Import Program.Equality.

Module DomSound. Section DomSound.

Variable successors: PTree.t (list positive).
Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.
Variable ni: positive.

Lemma adom_entrypoint:
  (pdom_analyze successors entrypoint ni) ?? entrypoint = Some nil.
Proof.
  unfold pdom_analyze.
  caseEq (DomDS.fixpoint successors LDoms.transfer
           ((entrypoint, LDoms.top) :: nil) ni).
    intros res H.
    eapply Inequations.fixpoint_entry with (n:=entrypoint) in H; simpl; eauto.
    destruct (res ?? entrypoint); inv H; auto.
 
    intros H. rewrite PMap.gi. auto.
Qed.

Definition predecessors := XPTree.make_predecessors successors.

Hypothesis wf_order: forall n (Hincfg: XPTree.in_cfg successors n) 
  (Hneq: n <> entrypoint),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.

Lemma sadom_adom_successors: forall n1 n2 p2 (Hsc : In n2 successors ??? p2)
  (Hincfg : in_cfg successors n1)
  (Hadom : strict_adomination successors entrypoint ni n1 n2),
  adomination successors entrypoint ni n1 p2.
Proof.
  intros.
  unfold adomination, strict_adomination, pdom_analyze in *.
  remember (DomDS.fixpoint successors LDoms.transfer
                   ((entrypoint, LDoms.top) :: nil) ni) as R.
  destruct R as [res|]; simpl in *.
    symmetry in HeqR.
    apply Inequations.fixpoint_solution with (n:=p2)(s:=n2) in HeqR; auto.
    destruct (res ?? n2) as [dms2|]; simpl in *.
      destruct (LDoms.transfer p2 res ?? p2); simpl; auto.
        eapply sublist_In; eauto.
      
      destruct (LDoms.transfer p2 res ?? p2); simpl; auto.
        tauto.

    rewrite PMap.gi in Hadom. simpl in Hadom.
    destruct Hadom; subst; tauto.
Qed.

Lemma adom_successors: forall n1 n2 p2 (Hsc : In n2 successors ??? p2)
  (Hincfg : in_cfg successors n1)
  (Hadom : adomination successors entrypoint ni n1 n2)
  (Hneq : n1 <> n2),
  adomination successors entrypoint ni n1 p2.
Proof.
  intros. eapply sadom_adom_successors; eauto using adom__sadom.
Qed.

Lemma adom_is_sound : forall n1 n2 (Hincfg: in_cfg successors n1)
  (Hadom: adomination successors entrypoint ni n1 n2),
  PCfg.domination successors entrypoint n1 n2.
Proof.
  intros.
  intros vl al Hreach.
  remember (PCfg.vertexes successors) as A.
  remember (PCfg.arcs successors) as B.
  unfold PTree.elt in *.
  remember (index n2) as C.
  remember (index entrypoint) as D.
  generalize dependent n2.
  induction Hreach; intros; subst.
  Case "base".
    inversion HeqC; subst n2.
    unfold adomination in Hadom.
    rewrite adom_entrypoint in Hadom.
    simpl in Hadom. destruct Hadom as [Hadom | Hadom]; tinv Hadom; auto.

  Case "ind".
    destruct y as [p2].
    destruct (positive_eq_dec n1 n2); subst; auto.
    left.
    assert (In (index n1) vl \/ n1 = p2) as Hin.
      apply IHHreach; auto.
      eapply adom_successors; eauto.
    simpl.
    destruct Hin; subst; eauto.
Qed.

Lemma sadom_is_sound : forall n1 n2 (Hincfg: in_cfg successors n1)
  (Hsadom: strict_adomination successors entrypoint ni n1 n2),
  PCfg.strict_domination successors entrypoint n1 n2.
Proof.
  intros. assert (Hadom:=Hsadom).
  apply sadom__adom in Hadom.
  apply adom_is_sound in Hadom; auto.
  intros vl al Hreach.
  assert (Hw':=Hreach).
  apply DWalk_to_dpath in Hreach; auto using positive_eq_dec.
  destruct Hreach as [vl0 [al0 Hp]].
  destruct (positive_eq_dec n1 n2); subst.
  Case "n1=n2".
    unfold PCfg.domination in *.
    destruct (positive_eq_dec n2 entrypoint); subst.
    SCase "n2=entry".
      unfold strict_adomination in Hsadom.
      rewrite adom_entrypoint in Hsadom.
      inv Hsadom.
    SCase "n2<>entry".
      inv Hp; try congruence.
      destruct y as [p2].
      assert (adomination successors entrypoint ni n2 p2) as J.
        eapply sadom_adom_successors; eauto.
      eapply adom_is_sound in J; eauto.
      unfold domination in J.
      assert (Hw:=H).
      apply D_path_isa_walk in Hw.
      apply J in Hw.
      destruct Hw as [Hw | Hw]; subst; auto.
        apply H4 in Hw. inv Hw; try congruence.
        elimtype False. auto.
  Case "n1<>n2".
    apply Hadom in Hw'.
    split; auto. destruct Hw'; subst; auto. congruence.
Qed.

Lemma sadom_isnt_refl : forall n1 n2 (Hincfg: in_cfg successors n1)
  (Hreach : PCfg.reachable successors entrypoint n2)
  (Hsadom: strict_adomination successors entrypoint ni n1 n2),
  n1 <> n2.
Proof.
  intros.
  eapply sadom_is_sound in Hsadom; eauto.
  destruct Hreach as [vl [al Hreach]].
  apply Hsadom in Hreach. tauto.
Qed.

Lemma reachable_isnt_bot : forall n 
  (Hreach : PCfg.reachable successors entrypoint n),
  (pdom_analyze successors entrypoint ni) ?? n <> LDoms.bot.
Proof.
  intros.
  destruct Hreach as [vl [al Hreach]].
  remember (PCfg.vertexes successors) as A.
  remember (PCfg.arcs successors) as B.
  unfold PTree.elt in *.
  remember (index n) as C.
  remember (index entrypoint) as D.
  generalize dependent n.
  induction Hreach; intros; subst.
  Case "base".
    inversion HeqC; subst n.
    rewrite adom_entrypoint. unfold LDoms.bot. congruence.

  Case "ind".
    destruct y as [p2].
    assert (index p2 = index p2) as Hdom. auto.
    apply_clear IHHreach in Hdom; auto.
    unfold pdom_analyze in *.
    case_eq (DomDS.fixpoint successors LDoms.transfer
              ((entrypoint, LDoms.top) :: nil) ni).
    SCase "1".
      intros res Hfix.
      rewrite Hfix in Hdom.
      apply Inequations.fixpoint_solution with (n:=p2)(s:=n) in Hfix; auto.
      unfold LDoms.bot in *.
      destruct (res ?? p2); try congruence.
      simpl in Hfix.
      destruct (res ?? n); inv Hfix; congruence.

    SCase "2".
      intro Hfix.
      rewrite PMap.gi. 
      unfold LDoms.top, LDoms.bot.
      congruence.
Qed.

End DomSound. End DomSound.

(***************************************************************)
(* Prove that pdom_analyze satisfies the specification defined in dom_type.v. *) 
Module PDomProps. Section PDomProps.

Variable successors: PTree.t (list positive).
Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.
Variable ni: positive.

Lemma dom_in_parants: forall (dts : list positive) n
  (Hdom : (pdom_analyze successors entrypoint ni) ?? n = Some dts)
  (p : positive) (Hinp : In p dts),
  In p (XPTree.parents_of_tree successors).
Proof.
  unfold pdom_analyze  in *.
  intros.
  case_eq (DomDS.fixpoint successors LDoms.transfer
             ((entrypoint, LDoms.top) :: nil) ni).
    intros res Heq.
    rewrite Heq in Hdom.
    apply DomsInParents.fixpoint_wf in Heq.
    assert (J:=Heq n). rewrite Hdom in J.
    simpl in J.
    eauto with datatypes v62.

    intros Heq.
    rewrite Heq in Hdom.
    rewrite PMap.gi in Hdom. inv Hdom. inv Hinp.
Qed.

Lemma dom_in_cfg: forall (dts : list positive) n
  (Hdom : (pdom_analyze successors entrypoint ni) ?? n = Some dts)
  (p : positive) (Hinp : In p dts),
  XPTree.in_cfg successors p.
Proof.
  intros. left. eapply dom_in_parants; eauto.
Qed.

Hypothesis Hlarge_enough: (ni >= Termination.num_iters successors)%positive.

Hypothesis wf_entrypoints: in_cfg successors entrypoint.
Definition predecessors := XPTree.make_predecessors successors.
Hypothesis wf_order: forall n (Hincfg: XPTree.in_cfg successors n) 
  (Hneq: n <> entrypoint),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.

Lemma dom_unreachable: forall n3 
  (Hunreach: ~ PCfg.reachable successors entrypoint n3),
  LDoms.eq ((pdom_analyze successors entrypoint ni) ?? n3) LDoms.bot.
Proof.
  intros.
  destruct (positive_eq_dec n3 entrypoint); subst.
  Case "1".
    contradict Hunreach. 
    apply PCfg.reachable_entry; auto.    
  Case "2".
    unfold strict_adomination, pdom_analyze in *.
    termination_tac.
    eapply UnreachableDoms.fixpoint_wf in Hfix_tmn; eauto.
Qed.

Lemma nonempty_is_reachable: forall n dts
  (Hdom: (pdom_analyze successors entrypoint ni) ?? n = Some dts)
  (Hnonempty: dts <> nil),
  PCfg.reachable successors entrypoint n.
Proof.
  intros.
  destruct (PCfg.reachable_dec successors entrypoint n) as [H|H]; auto.
    apply dom_unreachable in H; auto.
    rewrite Hdom in H. inv H.
Qed.

Lemma in_dom__reachable: forall
  (dts : list positive) n
  (Hdom : (pdom_analyze successors entrypoint ni) ?? n = Some dts)
  (p : positive) (Hinp : In p dts),
  PCfg.reachable successors entrypoint p.
Proof.
  intros. 
  assert (Hincfg:=Hdom).
  eapply dom_in_cfg in Hincfg; eauto.
  assert (Hreach:=Hdom).
  apply nonempty_is_reachable in Hreach; auto.
    assert (PCfg.strict_domination successors entrypoint p n) as Hsdom.
      apply DomSound.sadom_is_sound with (ni:=ni); auto.
        unfold strict_adomination. rewrite Hdom; auto.
    eapply PCfg.sdom_reachable; eauto using positive_eq_dec.

    intro Eq. subst. tauto.
Qed.

Lemma pdom_in_bound: forall p dts
  (Hdom: (pdom_analyze successors entrypoint ni) ?? p = Some dts) dt
  (Hin: In dt dts),
  In dt (XPTree.parents_of_tree successors).
Proof.
  unfold pdom_analyze.
  intros.
  case_eq (DomDS.fixpoint successors LDoms.transfer 
             ((entrypoint, LDoms.top) :: nil) ni).
    intros res Hfix. rewrite Hfix in Hdom.
    eapply DomsInParents.dom_fix_in_bound; eauto.

    intros Hfix. rewrite Hfix in Hdom.
    rewrite PMap.gi in Hdom. inv Hdom. tauto.
Qed.

Lemma entrypoint_in_nonempty: forall n dts
  (Hdom: (pdom_analyze successors entrypoint ni) ?? n = Some dts)
  (Hnonempty: dts <> nil),
  In entrypoint dts.
Proof.
  intros.
  destruct (positive_eq_dec n entrypoint) as [Heq | Hneq]; subst.
    rewrite DomSound.adom_entrypoint in Hdom.
    congruence.

    unfold pdom_analyze in *.
    caseEq (DomDS.fixpoint successors LDoms.transfer
             ((entrypoint, LDoms.top) :: nil) ni).
      intros res H. rewrite H in Hdom.
      apply EntryDomsOthers.fixpoint_wf_doms in H; auto.
      apply H in Hneq. rewrite Hdom in Hneq. simpl in Hneq. auto.
 
      intros H. rewrite H in Hdom.
      rewrite PMap.gi in Hdom. inv Hdom. congruence.
Qed.

Lemma sadom_is_complete: forall n1 n2 (Hincfg: in_cfg successors n1)
  (Hsdom: PCfg.strict_domination successors entrypoint n1 n2),
  strict_adomination successors entrypoint ni n1 n2.
Proof.
  intros. 
  unfold strict_adomination, pdom_analyze in *.
  termination_tac.
  eapply DomComplete.fixpoint_wf in Hfix_tmn; eauto.
  Case "1".
    unfold DomComplete.wf_doms in Hfix_tmn.
    destruct (member_dec successors n1 dms ?? n2); auto.
    apply Hfix_tmn with (n2:=n2) in Hincfg; auto.
    SCase "1.1".
      unfold DomComplete.non_sdomination in Hincfg.
      destruct Hincfg as [vl [al [J1 J2]]].
      unfold strict_domination in Hsdom.
      apply Hsdom in J1.
      destruct J1; subst; congruence.
Qed.

End PDomProps. End PDomProps.

(**************************************************************)
(* Dominators are sorted by immediate-domination relations.   *)
Require Import dom_decl.

Module IdomSorted. Section IdomSorted.

Variable successors: PTree.t (list positive).
Variable entrypoint: positive.
Hypothesis wf_entrypoints: in_cfg successors entrypoint.

Definition entrypoints := (entrypoint, LDoms.top) :: nil.
Definition predecessors := XPTree.make_predecessors successors.

Hypothesis wf_order: forall n (Hneq: n <> entrypoint)
  (Hincfg: XPTree.in_cfg successors n),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.

Variable ni: positive.
Hypothesis Hlarge_enough: (ni >= Termination.num_iters successors)%positive.

Lemma Forall_Pgt__Forall_sdom: forall (n : positive) (res : PMap.t LDoms.t)
  (Hfix : DomDS.fixpoint successors LDoms.transfer
           ((entrypoint, LDoms.top) :: nil) ni = Some res)
  (Hreach : PCfg.reachable successors entrypoint n)
  (Hsort : SortedDoms.wf_doms res) 
  (a : positive)
  (l : list positive)
  (Hsortn : StronglySorted Pgt l)
  (H : Forall (Pgt a) l)
  (Hpn : forall dt : positive,
         In dt (a :: l) ->
         PCfg.strict_domination successors entrypoint dt n /\
         PCfg.reachable successors entrypoint dt /\ in_cfg successors dt),
  Forall (PCfg.strict_domination successors entrypoint a) l.
Proof.
  intros.
  induction H; auto.
    constructor.
    Case "1".
      clear IHForall.
      assert (PCfg.strict_domination successors entrypoint a x \/ 
              PCfg.strict_domination successors entrypoint x a) as Horder.
        assert (PCfg.strict_domination successors entrypoint a n) 
          as Hsdom_an.
          apply Hpn; auto with datatypes v62.
        assert (PCfg.strict_domination successors entrypoint x n) 
          as Hsdom_xn.
          apply Hpn; auto with datatypes v62.
        eapply PCfg.sdom_ordered; eauto using positive_eq_dec with positive.
      destruct Horder as [Hsdom_ax | Hsdom_xa]; auto.
      elimtype False.
      eapply PDomProps.sadom_is_complete in Hsdom_xa; eauto.
      SCase "1.1".
        unfold strict_adomination, pdom_analyze in Hsdom_xa.
        rewrite Hfix in Hsdom_xa.
        assert (Hsorta:=Hsort a).
        remember (res ?? a) as R.
        destruct R; simpl in Hsdom_xa.
        SSCase "1.1.1".
          apply Plt_Sorted__StronglySorted in Hsorta.
          inv Hsorta.
          eapply Forall_forall in H4; eauto.
          inv H4. rewrite H in H2. congruence.
        SSCase "1.1.2".  
          assert (PCfg.reachable successors entrypoint a) as Hreacha. 
            apply Hpn. simpl. auto.
          apply DomSound.reachable_isnt_bot with (ni:=ni) in Hreacha; auto.
          unfold pdom_analyze in Hreacha.
          rewrite Hfix in Hreacha. rewrite <- HeqR in Hreacha. auto.
      SCase "1.2".   
        apply Hpn. simpl. auto.
    Case "2".   
      apply IHForall.            
        apply StronglySorted_inv in Hsortn. tauto.
        intros. apply Hpn. destruct_in H1; simpl; auto.
Qed.

Lemma Pgt_sorted__sdom_sorted: forall (n : positive) (dts : list positive)
  (res : PMap.t LDoms.t)
  (Hfix : DomDS.fixpoint successors LDoms.transfer
           ((entrypoint, LDoms.top) :: nil) ni = Some res)
  (Hreach : PCfg.reachable successors entrypoint n)
  (Hsort : SortedDoms.wf_doms res)
  (Hsortn : StronglySorted Pgt dts)
  (Hpn : forall dt : positive,
         In dt dts ->
         PCfg.strict_domination successors entrypoint dt n /\
         PCfg.reachable successors entrypoint dt /\ in_cfg successors dt),
  (StronglySorted (PCfg.strict_domination successors entrypoint) dts).
Proof.
  intros.  
  induction Hsortn.
    constructor.
    
    constructor.
      apply IHHsortn. 
        intros. apply Hpn. simpl. auto.
      eapply Forall_Pgt__Forall_sdom; eauto.      
Qed.

Lemma dom__sdom_sorted_aux: forall n dts
  (Hdom: (pdom_analyze successors entrypoint ni) ?? n = Some dts),
  StronglySorted (PCfg.strict_domination successors entrypoint) (rev dts).
Proof.
  unfold pdom_analyze.
  intros.
  case_eq (DomDS.fixpoint successors LDoms.transfer 
            ((entrypoint, LDoms.top) :: nil) ni).
    intros res Hfix. rewrite Hfix in Hdom.    
    assert (PCfg.reachable successors entrypoint n) as Hreach.
      destruct (PCfg.reachable_dec successors entrypoint n) as [H|H]; auto.
      apply PDomProps.dom_unreachable with (ni:=ni) in H; auto.
        unfold pdom_analyze in H. rewrite Hfix in H. rewrite Hdom in H. inv H.

    assert (forall dt, In dt (rev dts) ->
                       PCfg.strict_domination successors entrypoint dt n /\
                       PCfg.reachable successors entrypoint dt /\
                       in_cfg successors dt) as Hpn.
      intros dt Hin. apply in_rev in Hin.
      assert (PCfg.strict_domination successors entrypoint dt n) as Hsound.
        apply DomSound.sadom_is_sound with (ni:=ni); auto.
          apply DomsInParents.fixpoint_wf in Hfix.
            assert (J:=Hfix n). rewrite Hdom in J. simpl in J.
            left. eauto with datatypes v62.

          unfold strict_adomination, pdom_analyze. rewrite Hfix.
          rewrite Hdom. auto.
      split; auto.
      split. 
        eapply PCfg.sdom_reachable; eauto using positive_eq_dec.
        apply DomsInParents.fixpoint_wf in Hfix.
          assert (J:=Hfix n). rewrite Hdom in J. simpl in J.
          left. eauto with datatypes v62.

    assert (Hsort:=Hfix).
    apply SortedDoms.fixpoint_wf in Hsort; auto.
    assert (Hsortn:=Hsort).
    apply SortedDoms.wf_doms__wf_dom with (n:=n) in Hsortn.
    rewrite Hdom in Hsortn. simpl in Hsortn.
    apply Plt_Sorted__rev_Pgt_Sorted in Hsortn.
    apply Pgt_Sorted__StronglySorted in Hsortn.

    eapply Pgt_sorted__sdom_sorted; eauto.
              
    intros Hfix. rewrite Hfix in Hdom.
    rewrite PMap.gi in Hdom. inv Hdom. simpl. constructor.
Qed.

Lemma dom__sdom_sorted: forall n dts
  (Hdom: (pdom_analyze successors entrypoint ni) ?? n = Some dts),
  StronglySorted (PCfg.strict_domination successors entrypoint) 
    (rev (n::dts)).
Proof.
  intros.
  assert (J:=Hdom).
  apply dom__sdom_sorted_aux in J.
  simpl.
  apply StronglySorted_rev_cons; auto.
    apply Forall_forall.
    intros x Hinx. apply in_rev in Hinx.
    apply DomSound.sadom_is_sound with (ni:=ni); auto.
      eapply PDomProps.dom_in_cfg; eauto.
      unfold strict_adomination. rewrite Hdom. simpl. auto.
Qed.

Hypothesis Hnopred: (XPTree.make_predecessors successors) ??? entrypoint = nil.

Lemma sdom_sorted__imm_sorted: forall n dts dts0
  (Hcomplete: forall n' 
                (Hsdom: PCfg.strict_domination successors entrypoint n' n),
                In n' (dts0++dts))
  (Hsound : forall dt (Hin: In dt (dts0++dts)),
              PCfg.reachable successors entrypoint dt)
  (Hsdsort : StronglySorted (PCfg.strict_domination successors entrypoint)
              (dts0++dts++[n])),
  Sorted (PCfg.imm_domination successors entrypoint) (dts++[n]).
Proof.
  induction dts as [|a dts]; simpl; intros.
  Case "base".
    constructor; auto.
  Case "ind".
    constructor.
    SCase "IH".
      simpl_env in Hsdsort.
      apply IHdts with (dts0:=dts0++[a]); simpl_env; auto.
    SCase "Main".
      destruct dts as [|b dts]; constructor.
      SSCase "1".
        assert (J:=Hsdsort).
        apply StronglySorted_split in J.      
        destruct J as [J1 J2].
        inv J2. inv H2.
        split; auto.
          intros l0 Hsdom.
          apply Hcomplete in Hsdom.
          destruct_in Hsdom.
          SSSCase "1.1".
            apply StronglySorted__R_front_back with (a1:=l0)(a2:=a) in Hsdsort; 
              simpl; auto.
            eapply PCfg.sdom_dom; eauto using positive_eq_dec.
          SSSCase "1.2".
            destruct_in Hsdom; subst; try tauto.
            eapply PCfg.dom_is_refl; eauto using positive_eq_dec.
      SSCase "2".
        assert (J:=Hsdsort).
        apply StronglySorted_split in J.      
        destruct J as [J1 J2].
        inv J2. inv H2.
        split; auto.
          intros l0 Hsdom.
          assert (PCfg.strict_domination successors entrypoint l0 n) as Hsdom'.
            rewrite_env ((dts0++a::(b::dts)) ++ [n]) in Hsdsort.
            apply StronglySorted__R_front_back with (a1:=b)(a2:=n) in Hsdsort; 
              simpl; auto with datatypes v62.
            eapply PCfg.sdom_tran; 
              eauto using positive_eq_dec, XPTree.no_preds__notin_succs.
          apply Hcomplete in Hsdom'.
          destruct_in Hsdom'.
          SSSCase "2.1".
            apply StronglySorted__R_front_back with (a1:=l0)(a2:=a) in Hsdsort; 
              simpl; auto. 
            eapply PCfg.sdom_dom; eauto using positive_eq_dec.
          SSSCase "2.2".
            destruct_in Hsdom'.
            SSSSCase "2.2.1".
              eapply PCfg.dom_is_refl; eauto using positive_eq_dec.
            SSSSCase "2.2.2".
              destruct Hsdom'; subst.
              SSSSSCase "2.2.2.1".
                eapply PCfg.sdom_isnt_refl in Hsdom; eauto using positive_eq_dec.
                  congruence.
                  apply Hsound; auto with datatypes v62.
              SSSSSCase "2.2.2.2".
                assert (PCfg.strict_domination successors entrypoint b l0) 
                  as Hsdom''.
                 rewrite_env ((dts0++[a]++[b])++(dts ++ [n])) in Hsdsort.
                 apply StronglySorted__R_front_back with (a1:=b)(a2:=l0) in Hsdsort; 
                   simpl; auto.
                   apply in_or_app. simpl. auto.
                   xsolve_in_list.
                assert (PCfg.strict_domination successors entrypoint l0 l0) as 
                  Hsdom0.
                  eapply PCfg.sdom_tran; 
                    eauto using positive_eq_dec, XPTree.no_preds__notin_succs.
                eapply PCfg.sdom_isnt_refl in Hsdom0; eauto using positive_eq_dec.
                  congruence.
                  apply Hsound; auto with datatypes v62.
Qed.

Lemma dom__imm_sorted: forall n dts
  (Hdom: (pdom_analyze successors entrypoint ni) ?? n = Some dts),
  Sorted (PCfg.imm_domination successors entrypoint) (rev (n::dts)).
Proof.
  intros.
  assert (Hsdsort:=Hdom).
  apply dom__sdom_sorted in Hsdsort.
  unfold pdom_analyze in Hdom.
  intros.
  case_eq (DomDS.fixpoint successors LDoms.transfer 
            ((entrypoint, LDoms.top) :: nil) ni).
  Case "1".
    intros res Hfix. rewrite Hfix in Hdom.    
    simpl.
    apply sdom_sorted__imm_sorted with (dts0:=nil); simpl; auto.
    SCase "1.1".
      intros n' Hsdom.
      apply PDomProps.sadom_is_complete with (ni:=ni) in Hsdom; auto.
        unfold strict_adomination, pdom_analyze in Hsdom.
        rewrite Hfix in Hsdom. rewrite Hdom in Hsdom. simpl in Hsdom.
        apply in_rev in Hsdom; auto.

        eapply UnreachableDoms.fixpoint_reachable in Hfix; eauto.
        eapply PCfg.sdom_of_reachable_is_in_cfg; eauto using positive_eq_dec.
    SCase "1.2".
      intros dt Hin. apply in_rev in Hin.
      eapply PDomProps.in_dom__reachable with (dts:=dts); 
         try solve [congruence | eauto with datatypes v62].
        unfold pdom_analyze. rewrite Hfix. eauto.

  Case "2".
    intros Hfix. rewrite Hfix in Hdom.
    rewrite PMap.gi in Hdom. inv Hdom. simpl. 
      constructor; auto.
Qed.

Lemma imm_dom__at_head: forall im n
  (Hidom: PCfg.imm_domination successors entrypoint im n) 
  (Hreach: PCfg.reachable successors entrypoint n),
  exists dts, 
    (pdom_analyze successors entrypoint ni) ?? n = Some (im::dts).
Proof.
  intros.
  assert (Hnonbot := Hreach).
  apply DomSound.reachable_isnt_bot with (ni:=ni) in Hnonbot; auto.
  case_eq ((pdom_analyze successors entrypoint ni) ?? n);
    try solve [intro Heq; rewrite Heq in Hnonbot;  
               unfold LDoms.bot in Hnonbot; congruence].
  intros dts Heq.
  assert (Hsort:=Heq).
  apply dom__sdom_sorted in Hsort.
  destruct Hidom as [Hsdom Hmin].
  apply PDomProps.sadom_is_complete with (ni:=ni) in Hsdom; auto.
  Case "1".
    unfold strict_adomination, pdom_analyze in *.
    termination_tac.
    rewrite Heq in *. simpl in Hsdom.
    destruct dts as [|a dts]; try tauto.
    destruct_in Hsdom; subst; eauto.
    simpl in Hsort. 
    assert (J:=Hsort).
    apply StronglySorted__R_front_back with (a1:=a)(a2:=n) in J; 
      simpl; auto with datatypes v62.
    simpl_env in Hsort.
    apply in_rev in Hsdom.
    apply StronglySorted__R_front_back with (a1:=im)(a2:=a) in Hsort; 
      simpl; auto with datatypes v62.
    apply Hmin in J.
    assert (PCfg.reachable successors entrypoint a) as Hreacha.
      eapply PDomProps.in_dom__reachable with (dts:=a::dts)(ni:=ni); 
         try solve [congruence | eauto with datatypes v62].
      unfold pdom_analyze. rewrite Hfix_tmn. eauto.
    eapply PCfg.dom_acyclic in Hsort;
      eauto using positive_eq_dec, XPTree.no_preds__notin_succs.
      tauto.
  Case "2".
    eapply PCfg.sdom_of_reachable_is_in_cfg; eauto using positive_eq_dec.
Qed.

Lemma entry__at_last: forall dts n
  (Hdom: (pdom_analyze successors entrypoint ni) ?? n = Some dts)
  (Hnnil: dts <> nil),
  exists dts', dts = dts'++[entrypoint].
Proof.
  intros.
  assert (J:=Hdom).
  apply PDomProps.entrypoint_in_nonempty in J; auto.
  assert (Hsort:=Hdom).
  apply dom__sdom_sorted in Hsort.
  simpl in Hsort.
  destruct dts as [|hd dts]; try congruence.
  destruct (cons_last _ hd dts) as [pre [last J']]. 
  rewrite J' in *. 
  rewrite_env (rev (pre ++ last :: nil)) in Hsort.
  rewrite rev_unit in Hsort.
  simpl_env in Hsort.
  destruct (positive_eq_dec last entrypoint); subst; eauto.
  elimtype False.
  destruct_in J. 
    apply in_rev in J.
    apply StronglySorted__R_front_back with (a1:=last)(a2:=entrypoint) in Hsort; 
      simpl; auto with datatypes v62.
      apply PCfg.noone_sdom_entry in Hsort; auto.
    destruct_in J.
Qed.

End IdomSorted. End IdomSorted.

