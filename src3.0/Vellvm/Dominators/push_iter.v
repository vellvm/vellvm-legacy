Require Export Coqlib.
Require Export Iteration.
Require Export Maps.
Require Import syntax.
Require Import infrastructure_props.
Require Import Metatheory.
Require Import Program.Tactics.
Require Import dom_libs.
Require Import dfs.

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

Definition fixpoint : option (PMap.t L.t) :=
  PrimIter.iterate _ _ step start_state.

End Kildall.

End Weak_Succ_Dataflow_Solver.

Module LDoms := Doms (MergeLt).
Module DomDS := Weak_Succ_Dataflow_Solver (PNodeSetMax) (LDoms).

Require analysis.
Require Import infrastructure.
Import LLVMsyntax.

Definition dom_analyze (f: fdef) : PMap.t LDoms.t :=
  let asuccs := analysis.successors f in
  match LLVMinfra.getEntryBlock f with
  | Some (block_intro le _ _ _) =>
      let '(mkPO _ a2p) := dfs asuccs le 1%positive in
      let psuccs := asuccs_psuccs a2p asuccs in
      match ATree.get le a2p with
      | Some pe => 
        match DomDS.fixpoint psuccs LDoms.transfer ((pe, LDoms.top) :: nil) with
        | None => (PMap.set pe LDoms.top (PMap.init LDoms.bot))
        | Some res => res
        end
      | None => PMap.init LDoms.bot
      end
  | None => PMap.init LDoms.bot
  end.

Module DomMap := LATTICEELT_MAP (LDoms).

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

Lemma in_parents_of_tree__in_initial: forall p
  (Hin : In p (XPTree.parents_of_tree successors)),
  PNodeSetMax.In p (PNodeSetMax.initial successors).
Proof.
  intros.
  apply XPTree.parents_of_tree__in_successors in Hin.
  destruct_conjs.
  eapply PNodeSetMax.initial_spec; eauto.
Qed.

Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.

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

Module InitOrder. Section InitOrder.

Variable successors: PTree.t (list positive).
Variable entrypoint: positive.
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
  apply Hpick. apply ZC1; auto.
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

Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Lemma entrypoints_wf_state: forall
  (wf_order: forall n (Hneq: n <> entrypoint),
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

Module Mono. Section Mono.

(** ** Monotonicity properties *)

(** We first show that the [st_in] part of the state evolves monotonically:
  at each step, the values of the [st_in[n]] either remain the same or
  increase with respect to the [L.ge] ordering. *)

Variable successors: PTree.t (list positive).
Definition in_cfg := XPTree.in_cfg successors.

Lemma propagate_succ_incr:
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

Lemma propagate_succ_list_incr:
  forall out scs st,
  DomMap.in_incr st.(DomDS.st_in) 
                 (DomDS.propagate_succ_list st out scs).(DomDS.st_in).
Proof.
  induction scs; simpl; intros.
    apply DomMap.in_incr_refl.

    apply DomMap.in_incr_trans with 
      (DomDS.propagate_succ st out a).(DomDS.st_in).
    apply propagate_succ_incr. auto.
Qed.

Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Lemma fixpoint_incr:
  forall res
  (Hfix: DomDS.fixpoint successors LDoms.transfer entrypoints = Some res),
  DomMap.in_incr (DomDS.start_state_in entrypoints) res.
Proof.
  unfold DomDS.fixpoint; intros.
  eapply (PrimIter.iterate_prop _ _ (DomDS.step successors LDoms.transfer)
    (fun st => 
       DomMap.in_incr (DomDS.start_state_in entrypoints) st.(DomDS.st_in))
    (fun res => DomMap.in_incr (DomDS.start_state_in entrypoints) res)); eauto.
  Case "1".
    intros st INCR. unfold DomDS.step.
    remember (PNodeSetMax.pick (DomDS.st_wrk st)) as R.
    destruct R as [ [n rem] | ]; auto.
      apply DomMap.in_incr_trans with st.(DomDS.st_in); auto.
        change st.(DomDS.st_in) with 
          (DomDS.mkstate st.(DomDS.st_in) rem).(DomDS.st_in).
        apply propagate_succ_list_incr; auto.

  Case "2".
    apply DomMap.in_incr_refl.
Qed.

End Mono. End Mono.

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
Definition entrypoints := (entrypoint, LDoms.top) :: nil.

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

Hypothesis wf_order: forall n (Hneq: n <> entrypoint),
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

Lemma fixpoint_incr:
  forall res
  (Hfix: DomDS.fixpoint successors LDoms.transfer entrypoints = Some res),
  wf_doms res.
Proof.
  unfold DomDS.fixpoint; intros.
  eapply (PrimIter.iterate_prop _ _ (DomDS.step successors LDoms.transfer)
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

Variable entrypoint: positive.
Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Definition predecessors := XPTree.make_predecessors successors.

Hypothesis wf_order: forall n (Hneq: n <> entrypoint),
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

Lemma fixpoint_incr:
  forall res
  (Hfix: DomDS.fixpoint successors LDoms.transfer entrypoints = Some res),
  wf_doms res.
Proof.
  unfold DomDS.fixpoint; intros.
  eapply (PrimIter.iterate_prop _ _ (DomDS.step successors LDoms.transfer)
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
        apply Mono.propagate_succ_list_incr. assumption.
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
  apply Mono.propagate_succ_list_incr.
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

Hypothesis wf_order: forall n (Hneq: n <> entrypoint),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.

Theorem fixpoint_solution:
  forall res n s,
  DomDS.fixpoint successors LDoms.transfer entrypoints = Some res ->
  In s (successors???n) ->
  LDoms.ge res??s (LDoms.transfer n res??n).
Proof.
  assert (forall res, 
          DomDS.fixpoint successors LDoms.transfer entrypoints = Some res ->
          forall n s,
          In s successors???n ->
          LDoms.ge res??s (LDoms.transfer n res??n)) as J.
    unfold DomDS.fixpoint. intros res PI. pattern res.
    eapply (PrimIter.iterate_prop _ _ (DomDS.step successors LDoms.transfer) 
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
  forall res n v,
  DomDS.fixpoint successors LDoms.transfer entrypoints = Some res ->
  In (n, v) entrypoints ->
  LDoms.ge res??n v.
Proof.
  intros.
  apply LDoms.ge_trans with (DomDS.start_state_in entrypoints)??n.
    apply Mono.fixpoint_incr in H. apply H.
    apply start_state_in_entry. auto.
Qed.

End Inequations. End Inequations.

(*
(** ** Preservation of a property over solutions *)

Variable P: L.t -> Prop.
Hypothesis P_bot: P L.bot.
Hypothesis P_lub: forall x y, P x -> P y -> P (L.lub x y).
Hypothesis P_transf: forall pc x, P x -> P (transf pc x).
Hypothesis P_entrypoints: forall n v, In (n, v) entrypoints -> P v.

Theorem fixpoint_invariant:
  forall res pc,
  fixpoint = Some res ->
  P res!!pc.
Proof.
  assert (forall ep,
          (forall n v, In (n, v) ep -> P v) ->
          forall pc, P (start_state_in ep)!!pc).
    induction ep; intros; simpl.
    rewrite AMap.gi. auto.
    simpl in H.
    assert (P (start_state_in ep)!!pc). apply IHep. eauto.
    destruct a as [n v]. rewrite AMap.gsspec. destruct (eq_atom_dec pc n).
    apply P_lub. subst. auto. eapply H. left; reflexivity. auto.
  set (inv := fun st => forall pc, P (st.(st_in)!!pc)).
  assert (forall st v n, inv st -> P v -> inv (propagate_succ st v n)).
    unfold inv, propagate_succ. intros.
    destruct (LAT.beq (st_in st)!!n (LAT.lub (st_in st)!!n v)).
    auto. simpl. rewrite AMap.gsspec. destruct (eq_atom_dec pc n).
    apply P_lub. subst n; auto. auto.
    auto.
  assert (forall l st v, inv st -> P v -> inv (propagate_succ_list st v l)).
    induction l; intros; simpl. auto.
    apply IHl; auto.
  assert (forall res, fixpoint = Some res -> forall pc, P res!!pc).
    unfold fixpoint. intros res0 RES0. pattern res0.
    eapply (PrimIter.iterate_prop _ _ step inv).
    intros. unfold step. destruct (NS.pick (st_wrk a)) as [[n rem] | ].
    apply H1. auto. apply P_transf. apply H2.
    assumption.
    eauto.
    unfold inv, start_state; simpl. auto.
  intros. auto.
Qed.
*)

(*
Hypothesis wf_entrypoints:
  predecessors ??? entrypoint = nil /\
  forall n (Hcfg: in_cfg n), (n <= entrypoint)%positive.
*)

