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
      let m := start_state_in rem in PMap.set n (L.lub m ?? n v) m
  end.

Definition start_state :=
  mkstate (start_state_in entrypoints) (NS.initial successors).

(** [propagate_succ] corresponds, in the pseudocode,
  to the body of the [for] loop iterating over all successors. *)

Definition propagate_succ (s: state) (out: L.t) (n: positive) :=
  let oldl := s.(st_in) ?? n in
  let newl := L.lub oldl out in
  if L.beq oldl newl
  then s
  else mkstate (PMap.set n newl s.(st_in)) (NS.add n s.(st_wrk)).

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
    destruct_if; simpl.
      rewrite PMap.gso; auto.
Qed.

Lemma propagate_succ_list_st_in: forall out sc scs st (Hnotin: ~ In sc scs),
  (DomDS.st_in (DomDS.propagate_succ_list st out scs)) ?? sc = 
    (DomDS.st_in st) ?? sc.
Proof. 
  intros. apply propagate_succ_list_st_in_aux; auto.
Qed.

Lemma propagate_succ_list_st_wrk: forall out scs st,
  PositiveSet.Subset (DomDS.st_wrk st)
    (DomDS.st_wrk (DomDS.propagate_succ_list st out scs)).
Proof.
  induction scs; simpl; intros.
    intro x; auto.
    intros x Hin.
    apply IHscs.
    unfold DomDS.propagate_succ.
    destruct_if; simpl.
      apply PositiveSet.add_2; auto.
Qed.

Lemma propagate_succ_bot_inv: forall st out sc n
  (Hnone: (DomDS.st_in (DomDS.propagate_succ st out sc)) ?? n = None),
  (DomDS.st_in st) ?? n = None.
Proof.
  unfold DomDS.propagate_succ.
  intros.
  destruct_if; auto.
    destruct (positive_eq_dec sc n); subst.
      rewrite PMap.gss in H0.
      rewrite PMap.gss.
      rewrite H0.
      apply LDoms.lub_bot_inv in H0. tauto.

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
  destruct_if; simpl.
    symmetry in HeqR.
    apply LDoms.beq_correct in HeqR.
    apply LDoms.Leq_nonbot_inv_r in HeqR; auto.
    apply LDoms.lub_nonbot_spec; auto.
   
    rewrite PMap.gss.
    apply LDoms.lub_nonbot_spec; auto.
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

Ltac fill_holes_in_ctx :=
repeat match goal with
| H: match ?e with
     | Some _ => _
     | None => _
     end |- _ =>
  match goal with
  | H1: _ = e |- _ => rewrite <- H1 in H
  | H1: e = _ |- _ => rewrite H1 in H
  end
end.

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
        apply propagate_succ_list_st_wrk. 
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
Variable entrypoint: positive.
Definition in_cfg := XPTree.in_cfg successors.

Lemma propagate_succ_incr:
  forall st p n,
  DomMap.in_incr 
    st.(DomDS.st_in) 
    (DomDS.propagate_succ st (LDoms.transfer p (st.(DomDS.st_in)??p)) n).(DomDS.st_in).
Proof.
  unfold DomMap.in_incr, DomDS.propagate_succ; simpl; intros.
  destruct_if.
    apply LDoms.ge_refl. 

    simpl. 
    case (positive_eq_dec n n0); intro; subst.
      rewrite PMap.gss. apply LDoms.ge_lub_left; auto.
      rewrite PMap.gso; auto. apply LDoms.ge_refl. 
Qed.

Definition wf_doms (dmap: PMap.t LDoms.t) : Prop :=
forall n (Hincfg: in_cfg n),
  match dmap ?? n with
  | None => True
  | Some sdms =>
      List.Forall (Plt n) sdms
  end.

Lemma lub_transfer_stable: forall dmap (Hwf: wf_doms dmap) p (Hincfg: in_cfg p),
  dmap ?? p = LDoms.lub dmap ?? p (LDoms.transfer p dmap ?? p).
Proof.
  intros.
  apply Hwf in Hincfg.
  destruct (dmap ?? p); auto.    
    simpl. f_equal. 
    apply LDoms.merge_cmp_cons. tauto.
Qed.

Lemma propagate_succ_self_stable: forall st n p 
  (Hwf: wf_doms (DomDS.st_in st)) (Hincfg: in_cfg p),
  (DomDS.st_in st) ?? p = 
  (DomDS.st_in 
    (DomDS.propagate_succ st (LDoms.transfer p (DomDS.st_in st) ?? p) n)) ?? p.
Proof.
  destruct st as [dmap rem]. simpl.
  intros.
  unfold DomDS.propagate_succ. simpl.
  destruct_if. simpl.
  case (positive_eq_dec n p); intro; subst.
    rewrite PMap.gss. apply lub_transfer_stable; auto.
    rewrite PMap.gso; auto. 
Qed.

Lemma propagate_succ_wf_doms:
  forall st p n 
  (Hwf: wf_doms st.(DomDS.st_in)) (Hin: in_cfg p)
  (Horder: (DomDS.st_in st) ?? n = None -> (p > n)%positive),
  wf_doms
    (DomDS.propagate_succ st (LDoms.transfer p (st.(DomDS.st_in)??p)) n).(DomDS.st_in).
Proof.
  intros.
  unfold DomDS.propagate_succ.
  destruct_if. simpl.
  intros x Hincfg.
  case (positive_eq_dec n x); intro; subst.
    rewrite PMap.gss. 
    apply Hwf in Hincfg. 
    assert (J:=LDoms.ge_lub_left (DomDS.st_in st) x p).
    remember ((DomDS.st_in st) ?? x) as R.
    destruct R.
      eapply LDoms.ge_Forall; eauto.
      
      remember ((DomDS.st_in st) ?? p) as R.
      destruct R; auto.
        simpl.
        apply Hwf in Hin.
        fill_holes_in_ctx.
        constructor.
          apply ZC1. apply Horder. auto.
          eapply order_lt_order in Hin; eauto.  

    rewrite PMap.gso; auto. 
    apply Hwf in Hincfg; auto.
Qed.

Lemma propagate_succ_list_incr_aux:
  forall p (Hincfg: in_cfg p) scs st (Hwf: wf_doms (DomDS.st_in st))
  (Horder: forall n (Hin: In n scs) (Hbot: (DomDS.st_in st) ?? n = None),
             (p > n)%positive),
  DomMap.in_incr 
    st.(DomDS.st_in) 
    (DomDS.propagate_succ_list 
      st (LDoms.transfer p (st.(DomDS.st_in)??p)) scs).(DomDS.st_in).
Proof.
  induction scs as [|sc scs]; simpl; intros.
    apply DomMap.in_incr_refl.
  
    apply DomMap.in_incr_trans with 
      (DomDS.propagate_succ 
        st (LDoms.transfer p (st.(DomDS.st_in)??p)) sc).(DomDS.st_in).
      apply propagate_succ_incr; auto.

      rewrite propagate_succ_self_stable at 3; auto.
      apply IHscs; auto using propagate_succ_wf_doms.
         intros. apply propagate_succ_bot_inv in Hbot. auto.
Qed.

Lemma propagate_succ_list_wf_doms_aux: forall 
  p (Hin: in_cfg p) scs st (Hwf: wf_doms (DomDS.st_in st))
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
    eapply WorklistProps.wf_state_pick_in_cfg; eauto.
    intros. eapply InitOrder.pick_gt_bot_successors in Hpick; eauto.
Qed.

Lemma propagate_succ_list_incr: forall st (Hwf: wf_state st)
  (rem : PositiveSet.t) (p : PositiveSet.elt)
  (Hpick : PNodeSetMax.pick (DomDS.st_wrk st) = Some (p, rem)),
  DomMap.in_incr 
    st.(DomDS.st_in) 
    (DomDS.propagate_succ_list 
      {| DomDS.st_in := DomDS.st_in st; DomDS.st_wrk := rem |}
      (LDoms.transfer p (st.(DomDS.st_in)??p))
      (successors ??? p)).(DomDS.st_in).
Proof.
  intros.
  destruct Hwf as [? [? ?]].
  change st.(DomDS.st_in) with 
    (DomDS.mkstate st.(DomDS.st_in) rem).(DomDS.st_in).
  apply propagate_succ_list_incr_aux; auto.
    eapply WorklistProps.wf_state_pick_in_cfg; eauto.
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

Definition entrypoints := (entrypoint, LDoms.top) :: nil.

Definition predecessors := XPTree.make_predecessors successors.

Hypothesis wf_order: forall n (Hneq: n <> entrypoint),
  exists p, In p (predecessors ??? n) /\ (p > n)%positive.

Lemma entrypoints_wf_doms:
  wf_doms (DomDS.start_state_in entrypoints).
Proof.
  simpl.
  intros x Hincfg.
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
  DomMap.in_incr (DomDS.start_state_in entrypoints) res /\
    wf_doms res.
Proof.
  unfold DomDS.fixpoint; intros.
  eapply (PrimIter.iterate_prop _ _ (DomDS.step successors LDoms.transfer)
    (fun st => 
       DomMap.in_incr (DomDS.start_state_in entrypoints) st.(DomDS.st_in) /\
       wf_state st)
    (fun res => DomMap.in_incr (DomDS.start_state_in entrypoints) res /\
                wf_doms res)); eauto.
  Case "1".
    intros st [INCR WF]. unfold DomDS.step.
    remember (PNodeSetMax.pick (DomDS.st_wrk st)) as R.
    destruct R as [ [n rem] | ]; auto using wf_state__wf_doms.
      split; auto using propagate_succ_list_wf_state.
        apply DomMap.in_incr_trans with st.(DomDS.st_in); auto.
          apply propagate_succ_list_incr; auto.

  Case "2".
    split; auto using entrypoints_wf_state.
      apply DomMap.in_incr_refl.
Qed.

End Mono. End Mono.

(*
Hypothesis wf_entrypoints:
  predecessors ??? entrypoint = nil /\
  forall n (Hcfg: in_cfg n), (n <= entrypoint)%positive.
*)

(*
(** ** Correctness invariant *)

(** The following invariant is preserved at each iteration of Kildall's
  algorithm: for all program points [n], either
  [n] is in the worklist, or the inequations associated with [n]
  ([st_in[s] >= transf n st_in[n]] for all successors [s] of [n])
  hold.  In other terms, the worklist contains all nodes that do not
  yet satisfy their inequations. *)

Definition good_state (st: state) : Prop :=
  forall n,
  NS.In n st.(st_wrk) \/
  (forall s, In s (successors!!!n) ->
             L.ge st.(st_in)!!s (transf n st.(st_in)!!n)).

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma start_state_good:
  good_state start_state.
Proof.
  unfold good_state, start_state; intros.
  case_eq (successors!n); intros.
  left; simpl. eapply NS.initial_spec. eauto.
  unfold successors_list. rewrite H. right; intros. contradiction.
Qed.

Lemma propagate_succ_charact:
  forall st out n,
  let st' := propagate_succ st out n in
  L.ge st'.(st_in)!!n out /\
  (forall s, n <> s -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  unfold propagate_succ; intros; simpl.
  predSpec L.beq L.beq_correct
           ((st_in st) !! n) (L.lub (st_in st) !! n out).
  split.
  eapply L.ge_trans. apply L.ge_refl. apply H; auto.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl.
  apply L.ge_lub_left.
  auto.

  simpl. split.
  rewrite AMap.gss.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl.
  apply L.ge_lub_left.
  intros. rewrite AMap.gso; auto.
Qed.

Lemma propagate_succ_list_charact:
  forall out scs st,
  let st' := propagate_succ_list st out scs in
  forall s,
  (In s scs -> L.ge st'.(st_in)!!s out) /\
  (~(In s scs) -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  induction scs; simpl; intros.
  tauto.
  generalize (IHscs (propagate_succ st out a) s). intros [A B].
  generalize (propagate_succ_charact st out a). intros [C D].
  split; intros.
  elim H; intro.
  subst s.
  apply L.ge_trans with (propagate_succ st out a).(st_in)!!a.
  apply propagate_succ_list_incr. assumption.

  apply A. auto.
  transitivity (propagate_succ st out a).(st_in)!!s.
  apply B. tauto.
  apply D. tauto.
Qed.

Lemma propagate_succ_incr_worklist:
  forall st out n x,
  NS.In x st.(st_wrk) -> NS.In x (propagate_succ st out n).(st_wrk).
Proof.
  intros. unfold propagate_succ.
  case (L.beq (st_in st) !! n (L.lub (st_in st) !! n out)).
  auto.
  simpl. rewrite NS.add_spec. auto.
Qed.

Lemma propagate_succ_list_incr_worklist:
  forall out scs st x,
  NS.In x st.(st_wrk) -> NS.In x (propagate_succ_list st out scs).(st_wrk).
Proof.
  induction scs; simpl; intros.
  auto.
  apply IHscs. apply propagate_succ_incr_worklist. auto.
Qed.

Lemma propagate_succ_records_changes:
  forall st out n s,
  let st' := propagate_succ st out n in
  NS.In s st'.(st_wrk) \/ st'.(st_in)!!s = st.(st_in)!!s.
Proof.
  simpl. intros. unfold propagate_succ.
  case (L.beq (st_in st) !! n (L.lub (st_in st) !! n out)).
  right; auto.
  case (eq_atom_dec s n); intro.
  subst s. left. simpl. rewrite NS.add_spec. auto.
  right. simpl. apply AMap.gso. auto.
Qed.

Lemma propagate_succ_list_records_changes:
  forall out scs st s,
  let st' := propagate_succ_list st out scs in
  NS.In s st'.(st_wrk) \/ st'.(st_in)!!s = st.(st_in)!!s.
Proof.
  induction scs; simpl; intros.
  right; auto.
  elim (propagate_succ_records_changes st out a s); intro.
  left. apply propagate_succ_list_incr_worklist. auto.
  rewrite <- H. auto.
Qed.

Lemma step_state_good:
  forall st n rem,
  NS.pick st.(st_wrk) = Some(n, rem) ->
  good_state st ->
  good_state (propagate_succ_list (mkstate st.(st_in) rem)
                                  (transf n st.(st_in)!!n)
                                  (successors!!!n)).
Proof.
  unfold good_state. intros st n rem WKL GOOD x.
  generalize (NS.pick_some _ _ _ WKL); intro PICK.
  set (out := transf n st.(st_in)!!n).
  elim (propagate_succ_list_records_changes
          out (successors!!!n) (mkstate st.(st_in) rem) x).
  intro; left; auto.

  simpl; intros EQ. rewrite EQ.
  case (eq_atom_dec x n); intro.
  (* Case 1: x = n *)
  subst x.
  right; intros.
  elim (propagate_succ_list_charact out (successors!!!n)
          (mkstate st.(st_in) rem) s); intros.
  auto.
  (* Case 2: x <> n *)
  elim (GOOD x); intro.
  (* Case 2.1: x was already in worklist, still is *)
  left. apply propagate_succ_list_incr_worklist.
  simpl. rewrite PICK in H. elim H; intro. congruence. auto.
  (* Case 2.2: x was not in worklist *)
  right; intros.
  case (In_dec eq_atom_dec s (successors!!!n)); intro.
  (* Case 2.2.1: s is a successor of n, it may have increased *)
  apply L.ge_trans with st.(st_in)!!s.
  change st.(st_in)!!s with (mkstate st.(st_in) rem).(st_in)!!s.
  apply propagate_succ_list_incr.
  auto.
  (* Case 2.2.2: s is not a successor of n, it did not change *)
  elim (propagate_succ_list_charact out (successors!!!n)
          (mkstate st.(st_in) rem) s); intros.
  rewrite H2. simpl. auto. auto.
Qed.

(** ** Correctness of the solution returned by [iterate]. *)

(** As a consequence of the [good_state] invariant, the result of
  [fixpoint], if defined, is a solution of the dataflow inequations,
  since [st_wrk] is empty when the iteration terminates. *)

Theorem fixpoint_solution:
  forall res n s,
  fixpoint = Some res ->
  In s (successors!!!n) ->
  L.ge res!!s (transf n res!!n).
Proof.
  assert (forall res, fixpoint = Some res ->
          forall n s,
          In s successors!!!n ->
          L.ge res!!s (transf n res!!n)).
  unfold fixpoint. intros res PI. pattern res.
  eapply (PrimIter.iterate_prop _ _ step good_state).

  intros st GOOD. unfold step.
  caseEq (NS.pick st.(st_wrk)).
  intros [n rem] PICK. apply step_state_good; auto.
  intros.
  elim (GOOD n); intro.
  elim (NS.pick_none _ n H). auto.
  auto.

  eauto. apply start_state_good. eauto.
Qed.

(** As a consequence of the monotonicity property, the result of
  [fixpoint], if defined, is pointwise greater than or equal the
  initial mapping.  Therefore, it satisfies the additional constraints
  stated in [entrypoints]. *)

Lemma start_state_in_entry:
  forall ep n v,
  In (n, v) ep ->
  L.ge (start_state_in ep)!!n v.
Proof.
  induction ep; simpl; intros.
  elim H.
  elim H; intros.
  subst a. rewrite AMap.gss.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl.
  apply L.ge_lub_left.
  destruct a. rewrite AMap.gsspec. case (eq_atom_dec n a); intro.
  subst a. apply L.ge_trans with (start_state_in ep)!!n.
  apply L.ge_lub_left. auto.
  auto.
Qed.

Theorem fixpoint_entry:
  forall res n v,
  fixpoint = Some res ->
  In (n, v) entrypoints ->
  L.ge res!!n v.
Proof.
  intros.
  apply L.ge_trans with (start_state_in entrypoints)!!n.
  apply fixpoint_incr. auto.
  apply start_state_in_entry. auto.
Qed.

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

