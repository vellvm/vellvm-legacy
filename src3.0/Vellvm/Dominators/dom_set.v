Require Import List.
Require Import ListSet.
Require Import Coqlib.
Require Import Metatheory.
Require Import Maps.
Require Import Lattice.
Require Import Kildall.
Require Import Iteration.
Require Export cfg.
Require Export reach.
Require Export dom_decl.
Require Import dom_type.
Require Import Dipaths.

Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Import LLVMsyntax.
Import LLVMinfra.

Module AlgDom : ALGDOM.

Definition transfer (lbl: l) (before: Dominators.t) :=
  Dominators.add before lbl.

(** The static analysis itself is then an instantiation of Kildall's
  generic solver for forward dataflow inequations. [analyze f]
  returns a mapping from program points to mappings of pseudo-registers
  to approximations.  It can fail to reach a fixpoint in a reasonable
  number of iterations, in which case [None] is returned. *)

Module DomDS := Dataflow_Solver_Var_Top(AtomNodeSet).

(***************************************************)

Module WorklistProps. Section WorklistProps.

Variable successors: ATree.t (list atom).
Definition in_cfg := XATree.in_cfg successors.

Definition wf_state (st: DomDS.state) : Prop :=
  (forall n (Hinwrk: AtomNodeSet.In n st.(DomDS.st_wrk)), in_cfg n) /\
  NoDup (st.(DomDS.st_wrk)).

Lemma wf_state_pick_in_cfg: forall st (WF : wf_state st) n rem
  (Hpick : Some (n, rem) = AtomNodeSet.pick (DomDS.st_wrk st)),
  in_cfg n.
Proof.
  intros.
  symmetry_ctx.
  apply AtomNodeSet.pick_in in Hpick.
  apply WF in Hpick; auto.
Qed.

Lemma wf_state_pick_NoDup: forall st (WF : wf_state st) n rem
  (Hpick : Some (n, rem) = AtomNodeSet.pick (DomDS.st_wrk st)),
  NoDup rem.
Proof.
  intros.
  unfold AtomNodeSet.pick in Hpick.
  case_eq (DomDS.st_wrk st).
    intro Heq. rewrite Heq in *. congruence.

    intros a l0 Heq. rewrite Heq in *. inv Hpick.
    destruct WF as [_ WF]. 
    rewrite Heq in WF. inv WF.
    apply AtomSet.set_remove_NoDup; auto.
Qed.

Lemma propagate_succ_list_wf_state_aux: forall p
  out scs (st : DomDS.state) (Hwf : wf_state st)
  (Hinscs: forall sc, In sc scs -> In sc successors !!! p),
  wf_state (DomDS.propagate_succ_list st out scs).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs; auto.
    Case "1".
      unfold DomDS.propagate_succ.
      destruct_if; auto.
      split; simpl.
      SCase "1.1".
        intros n Hinwrk. 
        unfold AtomNodeSet.In, AtomNodeSet.add in Hinwrk.
        apply set_add_elim in Hinwrk.
        destruct Hinwrk as [Hinwrk | Hinwrk]; subst.
          eapply XATree.in_succ__in_cfg; eauto.
          apply Hwf; auto.
      SCase "1.2".
        apply AtomSet.set_add_NoDup. apply Hwf.
Qed.

Lemma propagate_succ_list_wf_state: forall st (Hwf: wf_state st) rem p 
  (Hpick: AtomNodeSet.pick (DomDS.st_wrk st) = Some (p, rem)),
  wf_state 
    (DomDS.propagate_succ_list 
      {| DomDS.st_in := DomDS.st_in st; DomDS.st_wrk := rem |}
      (transfer p (DomDS.st_in st) !! p) successors !!! p).
Proof.
  intros.
  assert 
    (wf_state {| DomDS.st_in := DomDS.st_in st; DomDS.st_wrk := rem |}) 
    as Hwf'.
    split; simpl.
      intros n Hin. simpl in *.
      apply AtomNodeSet.pick_some with (n':=n) in Hpick.
      apply Hwf. tauto.

      eapply wf_state_pick_NoDup; eauto.
  eapply propagate_succ_list_wf_state_aux; eauto.
Qed.

Lemma step_wf_state: forall (st st': DomDS.state)
  (Hstep: DomDS.step successors transfer st = inr st'),
  wf_state st -> wf_state st'.
Proof.
  unfold DomDS.step.
  intros.
  remember (AtomNodeSet.pick (DomDS.st_wrk st)) as R.
  destruct R as [ [n rem] | ]; inv Hstep.
  apply propagate_succ_list_wf_state; auto.
Qed.

Lemma in_parents_of_tree__in_initial: forall p
  (Hin : In p (XATree.parents_of_tree successors)),
  AtomNodeSet.In p (AtomNodeSet.initial successors).
Proof.
  intros.
  apply XATree.parents_of_tree__in_successors in Hin.
  destruct Hin as [s Hin].
  eapply AtomNodeSet.initial_spec; eauto.
Qed.

Variable entrypoints: list (atom * DomDS.L.t).

Lemma entrypoints_wf_state:
  wf_state (DomDS.mkstate (DomDS.start_state_in entrypoints) 
                          (AtomNodeSet.initial successors)).
Proof.
  split.
    intros x Hin.
    simpl in *.
    apply AtomNodeSet.initial_spec' in Hin.
    apply XATree.parents_of_tree__in_successors in Hin.
    apply XATree.in_parents_of_tree__in_cfg; auto.

    simpl. apply AtomNodeSet.NoDup__initial.
Qed.

End WorklistProps. End WorklistProps.

(**************************************************************)

Module DomsInParents. Section DomsInParents.

Variable succs : ATree.t (list l).
Definition transf := transfer.
Definition top := Dominators.top.
Definition bot := Dominators.bot.
Variable entry: l.
Definition entrypoints : list (atom * DomDS.L.t) := (entry, Dominators.top)::nil.

Definition wf_dom (res: DomDS.L.t) : Prop :=
  match res with
  | Some ns0 => incl ns0 (XATree.parents_of_tree succs)
  | None => True
  end.

Definition wf_doms (res: AMap.t DomDS.L.t) : Prop := 
  forall l0, wf_dom (res !! l0).

Lemma start_wf_doms:
  wf_doms (DomDS.st_in (DomDS.start_state succs entrypoints)).
Proof.
  simpl. intros l0.
  rewrite AMap.gsspec.
  rewrite AMap.gi. simpl. 
  destruct_if; simpl.
    intros x Hinx. inv Hinx.
    rewrite AMap.gi. simpl. auto.
Qed.

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma wf_dom_eq: forall dt1 dt2 (Heq: DomDS.L.eq dt1 dt2) (Hwf: wf_dom dt2),
  wf_dom dt1.
Proof.
  unfold wf_dom.
  intros.
  destruct dt1; destruct dt2; tinv Heq; auto.
    elim Heq. intros. eauto with datatypes v62.
Qed.

Lemma propagate_succ_wf_doms: forall st n out,
  wf_dom out ->
  wf_doms st.(DomDS.st_in) ->
  wf_doms (DomDS.propagate_succ st out n).(DomDS.st_in).
Proof.
  unfold wf_doms.
  intros.
  destruct (@DomDS.propagate_succ_spec st out n) as [J1 J2].
  destruct (eq_atom_dec n l0); subst.
    apply wf_dom_eq in J1; auto.
    assert (J:=H0 l0).
    clear - J H.
    unfold wf_dom in *.
    destruct out, (DomDS.st_in st) !! l0; simpl; auto.
      apply AtomSet.incl_inter_left; auto.

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
  AtomNodeSet.pick st.(DomDS.st_wrk) = Some(n, rem) ->
  wf_doms st.(DomDS.st_in) ->
  wf_doms (DomDS.propagate_succ_list
             (DomDS.mkstate st.(DomDS.st_in) rem)
             (transf n st.(DomDS.st_in)!!n)
             (succs!!!n)).(DomDS.st_in).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_wf_doms; auto.
    intro Hnnil.
    assert (J:=GOOD n). simpl in J.
    unfold wf_dom. unfold wf_dom in J.    
    destruct (st_in !! n); simpl; auto.
    intros x Hin.
    destruct_in Hin; auto.
      apply XATree.nonleaf_is_parent; auto.
Qed.

Lemma step_wf_doms: forall (st st': DomDS.state)
  (Hstep: DomDS.step succs transfer st = inr st'),
  wf_doms st.(DomDS.st_in) -> wf_doms st'.(DomDS.st_in).
Proof.
  unfold DomDS.step.
  intros.
  remember (AtomNodeSet.pick (DomDS.st_wrk st)) as R.
  destruct R as [ [n rem] | ]; inv Hstep.
  apply pick_wf_doms; auto.
Qed.

Theorem fixpoint_wf: forall res ni,
  DomDS.fixpoint succs transf entrypoints ni = Some res ->
  wf_doms res.
Proof.
  unfold DomDS.fixpoint. intros res ni PI. pattern res.
  eapply (PrimIter.iter_prop _ _ (DomDS.step _ _)
    (fun st => wf_doms st.(DomDS.st_in))); eauto.
    intros st GOOD. unfold DomDS.step.
    caseEq (AtomNodeSet.pick st.(DomDS.st_wrk)); auto.
    intros [n rem] PICK.
    apply pick_wf_doms; auto.

    apply start_wf_doms.
Qed.

End DomsInParents. End DomsInParents.

(**************************************************************)

Module Termination. Section Termination.

Variable successors: ATree.t (list atom).
Definition in_cfg := XATree.in_cfg successors.

Definition elements_of_cfg : list atom := 
  XATree.elements_of_cfg successors eq_atom_dec.

Definition psize_of_cfg := (plength elements_of_cfg + 2)%positive. (*same*)

Definition psize_of_dom (dms: DomDS.L.t) : positive :=
  match dms with
  | None => psize_of_cfg
  | Some x => plength (AtomSet.elements_of_set eq_atom_dec x)
  end.

Definition num_of_doms_fun (dmap: AMap.t DomDS.L.t) (acc:positive) (a:atom) 
  : positive :=
  Pplus acc (psize_of_dom (dmap !! a)).

Definition num_of_doms (dmap: AMap.t DomDS.L.t) : positive := (*same*)
fold_left (num_of_doms_fun dmap) elements_of_cfg 1%positive.

Definition num_iters := Pcubeplus psize_of_cfg. (* same *)
Definition psize_of_worklist (wrk: AtomNodeSet.t) : positive :=
(plength wrk + 1)%positive.

Definition num_iters_aux (st: DomDS.state) := 
(psize_of_cfg * (num_of_doms (st.(DomDS.st_in))) + 
  psize_of_worklist (st.(DomDS.st_wrk)))%positive.

Lemma elements_of_cfg__lt__psize_of_cfg: (*same*)
  (plength elements_of_cfg < psize_of_cfg)%positive.
Proof.
  unfold psize_of_cfg. zify; omega.
Qed.

Lemma psize_of_worklist_ge_one: forall wrk, (*same*)
  (psize_of_worklist wrk > 1)%positive.
Proof.
  unfold psize_of_worklist.
  intros. zify. omega.
Qed.

Hint Unfold num_iters_aux.

Lemma num_iters_aux_gt_one: forall st, (num_iters_aux st > 1)%positive. (*same*)
Proof.
  intros.
  autounfold.  
  assert (J:=psize_of_worklist_ge_one (DomDS.st_wrk st)).
  zify. omega.
Qed.

Definition DomMap_eq bd (in1 in2: AMap.t DomDS.L.t) : Prop := (*same*)
  forall n (Hin: In n bd),  DomDS.L.eq in2!!n in1!!n.

Lemma propagate_succ_records_unchanges: (*almost same*)
  forall st out n st' (Heq: st' = DomDS.propagate_succ st out n) bd
  (H: DomMap_eq bd st.(DomDS.st_in) st'.(DomDS.st_in)) (Hin: In n bd),
  st.(DomDS.st_wrk) = st'.(DomDS.st_wrk).
Proof.
  unfold DomDS.propagate_succ.
  intros. 
  case_eq (DomDS.L.lub (DomDS.st_in st) !! n out).
    intros newl Heq'.
    rewrite Heq' in *.
    destruct_if; subst; auto.
    symmetry in HeqR.
    apply DomDS.L.beq_correct' in HeqR.
    assert (J:=H n Hin). simpl in *.
    rewrite AMap.gss in J.
    apply DomDS.L.eq_sym in J.
    congruence.

    intros Heq'.
    rewrite Heq' in *.
    assert (G:=DomDS.L.ge_lub_left (DomDS.st_in st) !! n out).
    rewrite Heq' in G. 
    destruct ((DomDS.st_in st) !! n); inv G.
    unfold DomDS.L.beq. 
    destruct (DomDS.L.eq_dec None None) as [|n0]; auto.
      contradict n0. apply DomDS.L.eq_refl.
Qed.

Lemma DomMap_eq_incr_incr__eq_eq: forall bd dm1 dm2 dm3 (Heq13: DomMap_eq bd dm1 dm3)
  (Hincr12: DomDS.in_incr dm1 dm2) (Hincr23: DomDS.in_incr dm2 dm3),
  DomMap_eq bd dm1 dm2 /\ DomMap_eq bd dm2 dm3.  (*almost same*)
Proof.
  intros.
  split.
    intros x Hinx.
    apply Heq13 in Hinx.
    assert (J1:=Hincr12 x).
    assert (J2:=Hincr23 x).
    unfold DomDS.L.eq.
    destruct (dm2 !! x) as [x2|]; simpl in *; auto.
      destruct (dm1 !! x) as [x1|]; simpl in *.
        destruct (dm3 !! x) as [x3|]; simpl in *; try tauto.
          split; auto.
             destruct Hinx. eauto with datatypes v62.
        destruct (dm3 !! x) as [x3|]; simpl in *; try tauto.

    intros x Hinx.
    apply Heq13 in Hinx.
    assert (J1:=Hincr12 x).
    assert (J2:=Hincr23 x).
    unfold DomDS.L.eq.
    destruct (dm3 !! x) as [x3|]; simpl in *; auto.
      destruct (dm1 !! x) as [x1|]; simpl in *.
        destruct (dm2 !! x) as [x2|]; simpl in *; try tauto.
          split; auto.
             destruct Hinx. eauto with datatypes v62.
        destruct (dm2 !! x) as [x2|]; simpl in *; try tauto.
Qed.

Lemma propagate_succ_list_records_unchanges: (*almost same*)
  forall out bd scs (Hinc: incl scs bd)
  st st' (Heq: st' = DomDS.propagate_succ_list st out scs)
  (H: DomMap_eq bd st.(DomDS.st_in) st'.(DomDS.st_in)),
  st.(DomDS.st_wrk) = st'.(DomDS.st_wrk).
Proof.
  induction scs; simpl; intros; subst; auto.
    assert (J1:=DomDS.propagate_succ_incr st out a).
    assert (J2:=DomDS.propagate_succ_list_incr out scs (DomDS.propagate_succ st out a)).
    eapply DomMap_eq_incr_incr__eq_eq in H; eauto.
    destruct H.
    transitivity (DomDS.st_wrk (DomDS.propagate_succ st out a)).
      eapply propagate_succ_records_unchanges; eauto with datatypes v62.
      apply IHscs; eauto with datatypes v62.
Qed.

Lemma stable_step_decreases_wrk: forall st st' (*same*)
  (Hstep : DomDS.step successors transfer st = inr st')
  (Heq: DomMap_eq elements_of_cfg (st.(DomDS.st_in)) (st'.(DomDS.st_in))),
  exists n, AtomNodeSet.pick st.(DomDS.st_wrk) = Some (n, st'.(DomDS.st_wrk)).
Proof.
  unfold DomDS.step.
  intros.
  case_eq (AtomNodeSet.pick st.(DomDS.st_wrk)).
    intros [max rem] Hpick.
    rewrite Hpick in *. exists max.
    inv Hstep.
    erewrite <- propagate_succ_list_records_unchanges; eauto.
      simpl. auto.
      apply XATree.succs_in_elements_of_cfg.

    intros Hpick.
    rewrite Hpick in *. congruence.
Qed.

Lemma dom_eq__psize_of_dom: forall sdms1 sdms2 (Heq: DomDS.L.eq sdms1 sdms2),
  psize_of_dom sdms1 = psize_of_dom sdms2.
Proof.
  destruct sdms1 as [x|]; destruct sdms2 as [y|]; simpl; intros; try tauto.
  destruct Heq as [J1 J2].
  apply AtomSet.length_incl_elements_of_set with (Hdec:=eq_atom_dec) in J1.
  apply AtomSet.length_incl_elements_of_set with (Hdec:=eq_atom_dec) in J2.
  unfold plength. 
  zify. omega.
Qed.

Lemma stable_step_num_of_doms: forall dm1 dm2 (* almost same *)
  (Heq : DomMap_eq elements_of_cfg dm1 dm2),
  num_of_doms dm1 = num_of_doms dm2.
Proof.
  unfold num_of_doms.
  intros.
  revert Heq.
  generalize 1%positive as p.
  generalize elements_of_cfg as l0.
  induction l0 as [|a l0]; simpl; auto.
    intros.
    rewrite IHl0. 
      f_equal.
      unfold num_of_doms_fun.
      f_equal.
      apply dom_eq__psize_of_dom.
      apply DomDS.L.eq_sym.
      apply Heq; simpl; auto.

      intros x Hinx.
      apply Heq. simpl; auto.
Qed.

Lemma stable_step_psize_of_worklist: forall wrk wrk' max (* almost same *)
  (Hpick : AtomNodeSet.pick wrk = Some (max, wrk')),
  (psize_of_worklist wrk >= psize_of_worklist wrk' + 1)%positive.
Proof.
  unfold AtomNodeSet.pick.
  intros.
  destruct wrk; inv Hpick.
  assert (J:=@AtomSet.set_remove_length _ eq_atom_dec max wrk).
  unfold psize_of_worklist. unfold plength. simpl.
  zify. omega.
Qed.

Lemma Pplus_pminus_spec1: forall p1 p2 p3, (* same *)
  (p2 > p3)%positive -> (p1 + (p2 - p3) = p1 + p2 - p3)%positive.
Proof.
  intros. zify. omega.
Qed.

Lemma stable_step_num_iters_aux: forall (st st': DomDS.state) max (* almost same *)
  (Hpick : AtomNodeSet.pick (DomDS.st_wrk st) = Some (max, DomDS.st_wrk st'))
  (Heq : DomMap_eq elements_of_cfg (DomDS.st_in st) (DomDS.st_in st')),
  (num_iters_aux st >= num_iters_aux st' + 1)%positive.
Proof.
  intros.
  autounfold.
  apply stable_step_num_of_doms in Heq.
  apply stable_step_psize_of_worklist in Hpick.
  rewrite Heq. clear Heq.
  zify. omega.
Qed.

Lemma propagate_succ_wrk_range:  (* almost same *)
  forall st out n st' (Heq: st' = DomDS.propagate_succ st out n),
  (psize_of_worklist st'.(DomDS.st_wrk) <=
    (psize_of_worklist st.(DomDS.st_wrk) + 1)%positive)%positive.
Proof.
  unfold DomDS.propagate_succ.
  intros. 
  destruct_if.
    zify; omega.

    simpl.
    assert (J:=@AtomSet.set_add_length _ eq_atom_dec n (DomDS.st_wrk st)).
    unfold psize_of_worklist, AtomNodeSet.add, plength.
    zify; omega.
Qed.

Lemma propagate_succ_list_wrk_range:  (* same *)
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

Lemma wrk_in_cfg__psize_of_worklist_lt_psize_of_cfg: forall st
  (Hwf : WorklistProps.wf_state successors st),
  (psize_of_worklist st.(DomDS.st_wrk) < psize_of_cfg)%positive.
Proof.
  intros.
  unfold  WorklistProps.wf_state in Hwf.
  unfold psize_of_worklist, psize_of_cfg.
  destruct Hwf as [Hwf1 Hwf2].
  assert (length (DomDS.st_wrk st) <= length elements_of_cfg)%nat as Hle.
    eapply NoDup_incl_length; eauto using eq_atom_dec.
    Case "1".
      apply remove_redundancy_NoDup; auto.
    Case "2".
      intros x Hinx. 
      apply Hwf1 in Hinx.
      apply remove_redundancy_in; auto.
      apply in_or_app. auto.
  unfold plength. zify; omega.     
Qed.

Lemma instable_step_wrk_range: forall st st'
  (Hwf: WorklistProps.wf_state successors st)
  (Hstep : DomDS.step successors transfer st = inr st'),
  (psize_of_worklist st'.(DomDS.st_wrk) <
    psize_of_worklist st.(DomDS.st_wrk) + psize_of_cfg)%positive.
Proof.
  intros.
  apply WorklistProps.step_wf_state in Hstep; auto.
  apply wrk_in_cfg__psize_of_worklist_lt_psize_of_cfg in Hstep.
  zify; omega.
Qed.

Definition DomMap_gt bd dm1 dm2 : Prop :=
DomDS.in_incr dm1 dm2 /\ exists n, In n bd /\ DomDS.L.gt (dm2 !! n) (dm1 !! n).

Lemma DomMap_in_incr__gt_or_eq: forall dm1 dm2 
  (Hincr: DomDS.in_incr dm1 dm2) bd,
  DomMap_eq bd dm1 dm2 \/ DomMap_gt bd dm1 dm2.
Proof.
  induction bd; simpl; intros.
    left.
    intros x Hinx. tauto.

    assert (G:=Hincr a).
    destruct (DomDS.L.ge__gt_or_eq (dm2!!a) (dm1!!a)) as [J | J]; auto.
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

Definition doms_lt_psize_of_cfg (dm2:AMap.t DomDS.L.t) :=
  forall p2 dms2 (Hget2: (dm2 !! p2) = Some dms2),
    (psize_of_dom (Some dms2) < psize_of_cfg)%positive.

Lemma ge__num_of_doms_fun__le_le: forall (dm1 dm2:AMap.t DomDS.L.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  (p2 p1 : positive) (Hle : (p2 <= p1)%positive) a
  (J : DomDS.L.ge dm2 !! a dm1 !! a),
  (num_of_doms_fun dm2 p2 a <= num_of_doms_fun dm1 p1 a)%positive.
Proof.
  intros.
  unfold num_of_doms_fun.
  unfold DomDS.L.ge in J.
  case_eq (dm1 !! a).
    intros l0 Heq0. rewrite Heq0 in *.
    case_eq (dm2 !! a).
      intros l1 Heq1. rewrite Heq1 in *. simpl in J.
      apply AtomSet.length_incl_elements_of_set with (Hdec:=eq_atom_dec) in J; 
        auto.
      unfold psize_of_dom, plength. zify; omega.
  
      intros Heq1. rewrite Heq1 in *. tauto.
  
    intros Heq0. rewrite Heq0 in *. 
    case_eq (dm2 !! a).
      intros l1 Heq1. rewrite Heq1 in *.
      apply Hincfg in Heq1. simpl in *.
      zify; omega.
  
      intros Heq1. rewrite Heq1 in *.
      zify; omega.
Qed.

Lemma ge__num_of_doms_fun__lt_lt: forall (dm1 dm2:AMap.t DomDS.L.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  (p2 p1 : positive) (Hle : (p2 < p1)%positive) a
  (J : DomDS.L.ge dm2 !! a dm1 !! a),
  (num_of_doms_fun dm2 p2 a < num_of_doms_fun dm1 p1 a)%positive.
Proof.
  intros.
  unfold num_of_doms_fun.
  unfold DomDS.L.ge in J.
  case_eq (dm1 !! a).
    intros l0 Heq0. rewrite Heq0 in *.
    case_eq (dm2 !! a).
      intros l1 Heq1. rewrite Heq1 in *.
      apply AtomSet.length_incl_elements_of_set with (Hdec:=eq_atom_dec) in J; 
        auto.
      unfold psize_of_dom, plength. zify; omega.
  
      intros Heq1. rewrite Heq1 in *. tauto.
  
    intros Heq0. rewrite Heq0 in *. 
    case_eq (dm2 !! a).
      intros l1 Heq1. rewrite Heq1 in *.
      apply Hincfg in Heq1. simpl in *.
      zify; omega.
  
      intros Heq1. rewrite Heq1 in *.
      zify; omega.
Qed.

Lemma ge__num_of_doms_fun__lt_le: forall (dm1 dm2:AMap.t DomDS.L.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  (p2 p1 : positive) (Hle : (p2 < p1)%positive) a
  (J : DomDS.L.ge dm2 !! a dm1 !! a),
  (num_of_doms_fun dm2 p2 a <= num_of_doms_fun dm1 p1 a)%positive.
Proof.
  intros.
  eapply ge__num_of_doms_fun__lt_lt in J; eauto.
  zify; omega.
Qed.

Lemma incr_num_of_doms: forall (dm1 dm2:AMap.t DomDS.L.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  (Hlt : DomDS.in_incr dm1 dm2) bd p2 p1 (Hle: (p2 < p1)%positive),
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

Lemma gt__num_of_doms_fun__le_lt: forall (dm1 dm2:AMap.t DomDS.L.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  (p2 p1 : positive) (Hle : (p2 <= p1)%positive) a
  (J : DomDS.L.gt dm2 !! a dm1 !! a),
  (num_of_doms_fun dm2 p2 a < num_of_doms_fun dm1 p1 a)%positive.
Proof.
  intros.
  unfold num_of_doms_fun.
  unfold DomDS.L.gt in J.
  case_eq (dm1 !! a).
    intros l0 Heq0. rewrite Heq0 in *.
    case_eq (dm2 !! a).
      intros l1 Heq1. rewrite Heq1 in *.
      destruct J as [J J'].
      apply AtomSet.length_exact_incl_elements_of_set 
        with (Hdec:=eq_atom_dec) in J'; auto.
      unfold psize_of_dom, plength.
      zify; omega.
  
      intros Heq1. rewrite Heq1 in *. tauto.
  
    intros Heq0. rewrite Heq0 in *. 
    case_eq (dm2 !! a).
      intros l1 Heq1. rewrite Heq1 in *.
      apply Hincfg in Heq1. simpl in *.
      zify; omega.
  
      intros Heq1. rewrite Heq1 in *.
      zify; omega.
Qed.

Lemma gt__num_of_doms__le_lt: forall (dm1 dm2:AMap.t DomDS.L.t)
  (Hincfg: doms_lt_psize_of_cfg dm2)
  bd (Hlt : DomMap_gt bd dm1 dm2) p2 p1 (Hle: (p2 <= p1)%positive),
  (fold_left (num_of_doms_fun dm2) bd p2 <
    fold_left (num_of_doms_fun dm1) bd p1)%positive.
Proof.
  intros dm1 dm2 Hincfg.
  unfold DomMap_gt.
  induction bd as [|a bd]; simpl; intros.
    destruct Hlt as [J1 [J2 J3]]. tauto.

    destruct Hlt as [Hincr [n [Hin Hlt]]].
    destruct Hin as [Hin | Hin]; subst.
      eapply gt__num_of_doms_fun__le_lt in Hlt; eauto.
      apply incr_num_of_doms; auto.

      apply IHbd; eauto.
      eapply ge__num_of_doms_fun__le_le; eauto.
Qed.

Lemma gt_num_of_doms: forall (dm1 dm2:AMap.t DomDS.L.t)
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
  (Hstep : DomDS.step successors transfer st = inr st')
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
  (Hwf : DomsInParents.wf_doms successors dms),
  doms_lt_psize_of_cfg dms.
Proof.
  intros.
  intros n sds Hget2.
  assert (J:=Hwf n). rewrite Hget2 in J. simpl in J.
  simpl.
  assert (length (AtomSet.elements_of_set eq_atom_dec sds) <= 
            length elements_of_cfg)%nat as Hle.
    eapply NoDup_incl_length; eauto using eq_atom_dec.
    Case "1".
      apply remove_redundancy_NoDup.
    Case "2".
      apply remove_redundancy_NoDup; auto.
    Case "3".
      intros x Hinx. 
      apply remove_redundancy_in with (Hdec:=eq_atom_dec) in Hinx; auto.
      apply remove_redundancy_in.
      apply in_or_app. auto.
  unfold psize_of_cfg, plength. zify; omega.     
Qed.

Definition fixpoint_iter_P := 
  (fun ni => 
     forall st 
     (Hbound: (ni >= num_iters_aux st)%positive)
     (Hwf1: DomsInParents.wf_doms successors (DomDS.st_in st))
     (Hwf2: WorklistProps.wf_state successors st),
     exists res : AMap.t DomDS.L.t,
       PrimIter.iter DomDS.state (AMap.t DomDS.L.t)
         (DomDS.step successors transfer) ni
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
    case_eq (DomDS.step successors transfer st); eauto.
    intros st' Hstep.
    assert (DomsInParents.wf_doms successors (DomDS.st_in st')) as Hwf1'.    
      eapply DomsInParents.step_wf_doms; eauto.
    assert (WorklistProps.wf_state successors st') as Hwf2'.
      eapply WorklistProps.step_wf_state; eauto.
    apply H; auto.
    SCase "1".
      apply Ppred_Plt; auto. 
    SCase "2".
      assert (Hmono:=Hstep).
      apply DomDS.step_incr in Hmono.
      apply DomMap_in_incr__gt_or_eq with (bd:=elements_of_cfg) in Hmono; auto.
      destruct Hmono as [Heq | Hgt].
      SSCase "2.1".
        apply stable_step_decreases_wrk in Hstep; auto.
        destruct Hstep as [max Hpick].
        eapply stable_step_num_iters_aux in Heq; eauto.
        clear - Hbound n Heq. zify; omega.
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
      case_eq (dms !! a).
        intros l Heq.
        apply Hwf in Heq. zify; omega.

        intros Heq. simpl. zify; omega.
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
    zify; omega.
Qed.

Variable entrypoint: atom.
Definition entrypoints := (entrypoint, DomDS.L.top) :: nil.

Lemma entry_psize_of_worklist:
  (psize_of_cfg >=
     psize_of_worklist
       (DomDS.st_wrk (DomDS.start_state successors entrypoints)))%positive.
Proof.
  assert (J:=WorklistProps.entrypoints_wf_state successors entrypoints).
  apply wrk_in_cfg__psize_of_worklist_lt_psize_of_cfg in J.
  simpl in *. zify; omega.
Qed.

Lemma entry_num_of_doms:
  (psize_of_cfg * psize_of_cfg >=
   num_of_doms (DomDS.st_in (DomDS.start_state successors entrypoints)))%positive.
Proof.
  unfold num_of_doms.
  assert (J:=elements_of_cfg__lt__psize_of_cfg).
  assert (doms_lt_psize_of_cfg 
           (DomDS.st_in (DomDS.start_state successors entrypoints))) as J'.
    assert (G:=WorklistProps.entrypoints_wf_state successors entrypoints).
    assert (G':=DomsInParents.start_wf_doms successors entrypoint).
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
    DomDS.fixpoint successors transfer entrypoints ni = Some res.
Proof.
  intros.
  apply fixpoint_iter.
  Case "1".
    assert (J:=num_iters__ge__num_iters_aux).
    zify. omega.
  Case "2". eapply DomsInParents.start_wf_doms; eauto.
  Case "3". eapply WorklistProps.entrypoints_wf_state; eauto.
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

(*********************************************************************)

Definition dom_analyze (f: fdef) : AMap.t Dominators.t :=
  let '(fdef_intro _ bs) := f in
  let top := Dominators.top in
  match getEntryBlock f with
  | Some (le, _) =>
      match DomDS.fixpoint (successors_blocks bs) transfer
        ((le, top) :: nil) (num_iters f) with
      | None => AMap.init top
      | Some res => res
      end
  | None => AMap.init top
  end.

Section Num_iters__is__large_enough.

Variable f:fdef.
Hypothesis Huniq: uniqFdef f.
Hypothesis branches_in_bound_fdef: forall p ps0 cs0 tmn0 l2
  (J3 : blockInFdefB (p, stmts_intro ps0 cs0 tmn0) f)
  (J4 : In l2 (successors_terminator tmn0)),
  In l2 (bound_fdef f).

Lemma num_iters__is__large_enough:
  (num_iters f >= Termination.num_iters (successors f))%positive.
Proof.
  intros. 
  assert (NoDup (XATree.elements_of_cfg (successors f) eq_atom_dec)) as Hpnodup.
    apply remove_redundancy_NoDup; auto.
  assert (NoDup (bound_fdef f)) as Hnodupf.
    apply uniqFdef__NoDup_bounds_fdef; auto.
  assert (J:=elements_of_acfg__eq__bound).
  eapply AtomSet.NoDup_set_eq_length_eq in J; eauto using eq_atom_dec.
  destruct f as [? bs]. simpl.
  unfold num_iters, Termination.num_iters, pnum_of_blocks_in_fdef,
         Termination.psize_of_cfg.
  repeat rewrite plength_of_blocks__eq__P_of_plus_nat.
  apply Pcubeplus_ge.
  unfold Termination.elements_of_cfg, plength.
  simpl in *. unfold ATree.elt in *. rewrite <- J.
  rewrite <- P_of_plus_one_nat__P_of_succ_nat.
  change 3%positive with (2+1)%positive.
  rewrite <- P_of_plus_nat_Pplus_commut.
  zify. omega.
Qed.

End Num_iters__is__large_enough.

Ltac termination_tac2 :=
let foo pe :=
  match goal with
  | Huniq : uniqFdef ?f |- _ =>
    let J := fresh "J" in
    let dms := fresh "dms" in
    let Hfix_tmn := fresh "Hfix_tmn" in
    assert (J:=Huniq);
    apply num_iters__is__large_enough in J; auto;
    eapply Termination.fixpoint_wf with (entrypoint:=pe) in J; 
      try solve [eauto];
    unfold Termination.entrypoints in J;
    destruct J as [dms Hfix_tmn]; simpl in Hfix_tmn; unfold l in *;
    rewrite Hfix_tmn in *
  end in
match goal with
| |- context [DomDS.fixpoint (successors_blocks _) _ 
               ((?pe, _)::_) ?ni] => foo pe
| _: context [DomDS.fixpoint (successors_blocks _) _ 
             ((?pe, _)::_) ?ni] |- _ => foo pe
end.

Definition bound_dom bd (res: Dominators.t) : set atom :=
match res with
| Some dts2 => dts2
| None => bd
end.

Definition sdom f : atom -> set atom :=
let dt := dom_analyze f in
let b := bound_fdef f in
fun l0 => bound_dom b (dt !! l0).

Import AtomSet.

Lemma dom_entrypoint : forall f l0 s0
  (Hentry : getEntryBlock f = Some (l0, s0)),
  sdom f l0 = nil.
Proof.
  intros.
  unfold sdom, dom_analyze.
  destruct f as [f b].
  rewrite Hentry.
  remember (DomDS.fixpoint (successors_blocks b)
              transfer ((l0, Dominators.top) :: nil) 
              (num_iters (fdef_intro f b))) as R1.
  destruct R1; subst.
  SCase "analysis is done".
    symmetry in HeqR1.
    apply DomDS.fixpoint_entry with (n:=l0)(v:=Some nil) in HeqR1; simpl; eauto.
    unfold DomDS.L.ge, DomDS.L.sub in HeqR1.
    destruct (t !! l0); try tauto.
      apply incl_empty_inv in HeqR1; subst; auto.

  SCase "analysis fails".
    rewrite AMap.gi. auto.
Qed.

Module EntryDomsOthers. Section EntryDomsOthers.

Variable bs : blocks.
Definition predecessors := XATree.make_predecessors (successors_blocks bs).
Definition transf := transfer.
Definition top := Dominators.top.
Definition bot := Dominators.bot.
Variable entry: l.
Variable entrypoints: list (atom * DomDS.L.t).

Hypothesis wf_entrypoints:
  match bs with
  | (l0, _) :: _ => l0 = entry
  | _ => False
  end /\
  exists v, [(entry, v)] = entrypoints /\ Dominators.eq v top.

Lemma dom_entry_start_state_in:
  forall n v,
  In (n, v) entrypoints ->
  Dominators.eq (DomDS.start_state_in entrypoints)!!n v.
Proof.
  destruct wf_entrypoints as [_ J]. clear wf_entrypoints.
  destruct J as [v [Heq J]]; subst. simpl.
  intros.
  destruct H as [H | H]; inv H.
  rewrite AMap.gss. rewrite AMap.gi.
  apply Dominators.eq_trans with (y:=DomDS.L.lub v0 bot).
    apply Dominators.lub_commut.
    apply Dominators.lub_preserves_ge.
    apply Dominators.ge_compat with (x:=top)(y:=bot).
      apply Dominators.eq_sym; auto.
      apply Dominators.eq_refl.
      apply Dominators.ge_bot.
Qed.

Lemma dom_nonentry_start_state_in:
  forall n,
  n <> entry ->
  Dominators.eq (DomDS.start_state_in entrypoints)!!n bot.
Proof.
  destruct wf_entrypoints as [_ J]. clear wf_entrypoints.
  destruct J as [v [Heq J]]; subst. simpl.
  intros.
  rewrite AMap.gi. rewrite AMap.gso; auto. rewrite AMap.gi.
  apply Dominators.eq_refl.
Qed.

Lemma transf_mono: forall p x y,
  Dominators.ge x y -> Dominators.ge (transf p x) (transf p y).
Proof.
  unfold transf, transfer. intros.
  apply Dominators.add_mono; auto.
Qed.

Definition lub_of_preds (res: AMap.t DomDS.L.t) (n:atom) : DomDS.L.t :=
  Dominators.lubs (List.map (fun p => transf p res!!p)
    (predecessors!!!n)).

Definition entry_doms_others (res: AMap.t DomDS.L.t) : Prop :=
  forall l0, l0 <> entry -> Dominators.member entry res!!l0.

Lemma start_entry_doms_others:
  entry_doms_others
    (DomDS.st_in (DomDS.start_state (successors_blocks bs) entrypoints)).
Proof.
  intros l0 Hneq.
  apply dom_nonentry_start_state_in in Hneq.
  unfold DomDS.start_state. simpl.
  apply Dominators.member_eq with (x2:=bot); auto.
  destruct wf_entrypoints as [J _]. unfold bot.
  destruct bs; tinv J.
  destruct b; subst. simpl. auto.
Qed.

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma propagate_succ_entry_doms_others: forall st n out,
  Dominators.member entry out ->
  entry_doms_others st.(DomDS.st_in) ->
  entry_doms_others (DomDS.propagate_succ st out n).(DomDS.st_in).
Proof.
  unfold entry_doms_others.
  intros.
  destruct (@DomDS.propagate_succ_spec st out n) as [J1 J2].
  apply H0 in H1.
  destruct (eq_atom_dec n l0); subst.
    apply Dominators.member_eq with (a:=entry) in J1; auto.
    apply Dominators.member_lub; auto.

    rewrite J2; auto.
Qed.

Lemma propagate_succ_list_entry_doms_others:
  forall scs st out,
  Dominators.member entry out ->
  entry_doms_others st.(DomDS.st_in) ->
  entry_doms_others (DomDS.propagate_succ_list st out scs).(DomDS.st_in).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs; auto.
    apply propagate_succ_entry_doms_others; auto.
Qed.

Lemma step_entry_doms_others:
  forall st n rem,
  AtomNodeSet.pick st.(DomDS.st_wrk) = Some(n, rem) ->
  entry_doms_others st.(DomDS.st_in) ->
  entry_doms_others (DomDS.propagate_succ_list
                                  (DomDS.mkstate st.(DomDS.st_in) rem)
                                  (transf n st.(DomDS.st_in)!!n)
                                  ((successors_blocks bs)!!!n)).(DomDS.st_in).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_entry_doms_others; auto.
    simpl in *.
    unfold transf, transfer.
    destruct (eq_atom_dec n entry); subst.
      apply Dominators.add_member1.
      destruct wf_entrypoints as [J _].
      destruct bs; tinv J.
      destruct b; subst. simpl. auto.

      apply GOOD in n0.
      apply Dominators.add_member2; auto.
Qed.

Theorem dom_entry_doms_others: forall res ni,
  DomDS.fixpoint (successors_blocks bs) transf entrypoints ni = Some res ->
  entry_doms_others res.
Proof.
  unfold DomDS.fixpoint. intros res ni PI. pattern res.
  eapply (PrimIter.iter_prop _ _ (DomDS.step _ _)
    (fun st => entry_doms_others st.(DomDS.st_in))); eauto.
  intros st GOOD. unfold DomDS.step.
  caseEq (AtomNodeSet.pick st.(DomDS.st_wrk)); auto.
  intros [n rem] PICK.
  apply step_entry_doms_others; auto.
    apply start_entry_doms_others.
Qed.

Lemma dom_solution_ge: forall res ni,
  DomDS.fixpoint (successors_blocks bs) transf entrypoints ni = Some res ->
  forall n,
  Dominators.ge res!!n (lub_of_preds res n).
Proof.
  intros.
  apply Dominators.lubs_spec3.
  intros.
  apply in_map_iff in H0.
  destruct H0 as [x [J1 J2]]; subst.
  eapply DomDS.fixpoint_solution; eauto.
  apply XATree.make_predecessors_correct'; auto.
Qed.

End EntryDomsOthers. End EntryDomsOthers.

Definition branchs_in_fdef f :=
  forall (p : l) (ps0 : phinodes) (cs0 : cmds) 
         (tmn0 : terminator) (l2 : l),
  blockInFdefB (p, stmts_intro ps0 cs0 tmn0) f ->
  In l2 (successors_terminator tmn0) -> In l2 (bound_fdef f).

Lemma dom_in_bound: forall successors le t ni
  (Hfix: DomDS.fixpoint successors transfer
            ((le, Dominators.top) :: nil) ni = Some t),
  forall l0 ns0 (Hget: t !! l0 = Some ns0) n (Hin: In n ns0),
    In n (XATree.parents_of_tree successors).
Proof.
  intros.
  apply DomsInParents.fixpoint_wf in Hfix; auto.
  assert (J:=Hfix l0).
  unfold DomsInParents.wf_dom in J.
  rewrite Hget in J. auto.
Qed.

Lemma dom_in_bound_blocks: forall bs le t ni
  (Hfix: DomDS.fixpoint (successors_blocks bs) transfer
            ((le, Dominators.top) :: nil) ni = Some t),
  forall l0 ns0 (Hget: t !! l0 = Some ns0), incl ns0 (bound_blocks bs).
Proof.
  intros.
  intros x Hinx.
  apply in_parents__in_bound.
  eapply dom_in_bound; eauto.
Qed.

Lemma sdom_in_bound: forall fh bs l5, 
  incl (sdom (fdef_intro fh bs) l5) (bound_blocks bs).
Proof.
  intros.
  unfold sdom, dom_analyze.
  destruct (getEntryBlock (fdef_intro fh bs)) as [[]|]; simpl. 
    remember (DomDS.fixpoint (successors_blocks bs) transfer
                ((l0, Dominators.top) :: nil) 
                (num_iters (fdef_intro fh bs))) as R.
    destruct R.
      symmetry in HeqR.
      remember (t !! l5) as R.
      destruct R; simpl; auto with datatypes v62.
        eapply dom_in_bound_blocks; eauto.

      rewrite AMap.gi. simpl. intros x Hin. inv Hin.
    rewrite AMap.gi. simpl. intros x Hin. inv Hin.
Qed.

Lemma dom_successors : forall
  (l3 : l) (l' : l) f
  (contents3 contents': ListSet.set atom)
  (Hinscs : In l' (successors f) !!! l3)
  (Heqdefs3 : contents3 = sdom f l3)
  (Heqdefs' : contents' = sdom f l'),
  incl contents' (l3 :: contents3).
Proof.
  intros. 
  unfold sdom, dom_analyze in *.
  remember (getEntryBlock f) as R.
  destruct f as [fh bs].
  destruct R as [[le []]|].
  Case "entry is good".
    remember (DomDS.fixpoint (successors_blocks bs)
                transfer ((le, Dominators.top) :: nil)
                (num_iters (fdef_intro fh bs))) as R1.
    destruct R1; subst.
    SCase "analysis is done".
      symmetry in HeqR1.
      assert (Hinbd: forall l0 ns0 (Hget: t !! l0 = Some ns0), 
                     incl ns0 (bound_blocks bs)).
        eapply dom_in_bound_blocks; eauto.
      apply DomDS.fixpoint_solution with (s:=l')(n:=l3) in HeqR1; eauto.
      unfold transfer, DomDS.L.ge, DomDS.L.sub, Dominators.add in HeqR1.
      remember (t !! l') as R2.
      remember (t !! l3) as R3.
      destruct R2 as [els2|]; destruct R3 as [els3|]; 
        simpl; try solve [auto with datatypes v62 | tauto].
        symmetry in HeqR2.
        apply Hinbd in HeqR2. auto with datatypes v62.

    SCase "analysis fails".
      repeat rewrite AMap.gi. simpl. auto with datatypes v62.

  Case "entry is wrong".
    subst. repeat rewrite AMap.gi. simpl. auto with datatypes v62.
Qed.

Module DomComplete. Section DomComplete.

Variable fh : fheader.
Variable bs : blocks.
Definition predecessors := XATree.make_predecessors (successors_blocks bs).
Definition transf := transfer.
Definition top := Dominators.top.
Definition bot := Dominators.bot.
Variable entry: l.
Variable entrypoints: list (atom * DomDS.L.t).

Hypothesis wf_entrypoints:
  match bs with
  | (l0, _) :: _ => l0 = entry
  | _ => False
  end /\
  exists v, [(entry, v)] = entrypoints /\ Dominators.eq v top.

Definition non_sdomination (l1 l2:l) : Prop :=
  ACfg.non_sdomination (successors (fdef_intro fh bs)) entry l1 l2.

Definition non_sdomination_prop (res: AMap.t DomDS.L.t) : Prop :=
  forall l1 l2,
    vertexes_fdef (fdef_intro fh bs) (index l1) ->
    ~ Dominators.member l1 res!!l2 ->
    non_sdomination l1 l2.

Lemma start_non_sdomination:
  non_sdomination_prop
    (DomDS.st_in (DomDS.start_state (successors_blocks bs) entrypoints)).
Proof.
  intros l1 l2 Hin Hnotin.
  destruct (eq_atom_dec l2 entry); try subst l2.
    unfold non_sdomination.
    exists V_nil. exists A_nil.
    split.
      constructor.
      destruct wf_entrypoints as [J _].
      destruct bs; tinv J.
      destruct b; subst.
      eapply entry_in_vertexes; simpl; eauto.

      intro J. inv J.

    eapply EntryDomsOthers.dom_nonentry_start_state_in in n; eauto.
    contradict Hnotin.
    unfold DomDS.start_state. simpl.
    apply Dominators.member_eq with (x2:=bot); simpl; auto.
Qed.

Lemma non_sdomination_refl : forall l1,
  l1 <> entry ->
  reachable (fdef_intro fh bs) l1 ->
  non_sdomination l1 l1.
Proof.
  unfold reachable, non_sdomination. 
  intros.
  destruct bs as [|[]]; simpl in *; try congruence.
  destruct wf_entrypoints as [Heq _]; subst.
  apply ACfg.non_sdomination_refl; auto.
Qed.

Lemma propagate_succ_non_sdomination: forall st p n out
  (Hinpds: In p predecessors!!!n)
  (Hout: Dominators.ge (transf p st.(DomDS.st_in)!!p) out)
  (Hdom: non_sdomination_prop st.(DomDS.st_in)),
  non_sdomination_prop (DomDS.propagate_succ st out n).(DomDS.st_in).
Proof.
  unfold non_sdomination_prop. intros.
  destruct (@DomDS.propagate_succ_spec st out n) as [J1 J2].
  destruct (eq_atom_dec n l2) as [Heq | Hneq]; subst.
  Case "n=l2".
    destruct (Dominators.member_dec l1 (DomDS.st_in st) !! l2)
      as [Hin12 | Hnotin12]; auto.
    assert (~ Dominators.member l1
      (DomDS.L.lub (DomDS.st_in st) !! l2 out)) as Hnotlub12.
      intro J. apply H0.
      eapply Dominators.member_eq; eauto.
    clear J1 J2.
    destruct (Dominators.member_dec l1 out) as [Hinout | Hnotout]; auto.
    SCase "l1 in out".
      contradict Hnotlub12. apply Dominators.lub_intro; auto.
    SCase "l1 notin out".
      assert (~ Dominators.member l1 (transf p (DomDS.st_in st) !! p))
        as Hnotintransf.
        intro J. apply Hnotout.
        eapply Dominators.ge_elim in Hout; eauto.
      unfold transf, transfer in Hnotintransf.
      assert (l1 <> p /\ ~ Dominators.member l1 (DomDS.st_in st)!!p)
        as J.
        split; intro J; subst; apply Hnotintransf.
          apply Dominators.add_member1; auto.
          apply Dominators.add_member2; auto.
      clear Hnotintransf.
      destruct J as [Hneq J].
      apply Hdom in J; auto.
      destruct J as [vl [al [J1 J2]]].
      exists (index p::vl). exists (A_ends (index l2) (index p)::al).
      split.
      SSCase "1".
        apply XATree.make_predecessors_correct' in Hinpds.
        change (successors_blocks bs) with (successors (fdef_intro fh bs))
          in Hinpds.
        constructor; eauto.
          eapply XATree.in_succ__in_cfg; eauto.

      SSCase "2".
          intro J. simpl in J.
          destruct J as [J | J]; auto.
            inv J. auto.
  Case "n<>l2".
    rewrite J2 in H0; auto.
Qed.

Lemma propagate_succ_list_non_sdomination_aux:
  forall p scs st out,
  (forall s, In s scs -> In p predecessors!!!s) ->
  non_sdomination_prop st.(DomDS.st_in) ->
  Dominators.ge (transf p st.(DomDS.st_in)!!p) out ->
  non_sdomination_prop (DomDS.propagate_succ_list st out scs).(DomDS.st_in).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs; auto.
      eapply propagate_succ_non_sdomination; eauto.
      apply Dominators.ge_trans with (y:=transf p (DomDS.st_in st) !! p);
        auto.
        eapply EntryDomsOthers.transf_mono; eauto.
        destruct (@DomDS.propagate_succ_spec st out a) as [J1 J2].
        destruct (eq_atom_dec a p); subst.
          apply Dominators.ge_trans with
            (y:=Dominators.lub (DomDS.st_in st) !! p out).
            apply Dominators.ge_refl; auto.
            apply Dominators.ge_lub_left.
          rewrite J2; auto.
            apply Dominators.ge_refl'.
Qed.

Lemma propagate_succ_list_non_sdomination:
  forall p scs st,
  (forall s, In s scs -> In p predecessors!!!s) ->
  non_sdomination_prop st.(DomDS.st_in) ->
  non_sdomination_prop (DomDS.propagate_succ_list st
    (transf p st.(DomDS.st_in)!!p) scs).(DomDS.st_in).
Proof.
  intros.
  eapply propagate_succ_list_non_sdomination_aux; eauto.
    apply Dominators.ge_refl'.
Qed.

Lemma step_non_sdomination:
  forall st n rem,
  AtomNodeSet.pick st.(DomDS.st_wrk) = Some(n, rem) ->
  non_sdomination_prop st.(DomDS.st_in) ->
  non_sdomination_prop (DomDS.propagate_succ_list 
                                 (DomDS.mkstate st.(DomDS.st_in) rem)
                                 (transf n st.(DomDS.st_in)!!n)
                                 ((successors_blocks bs)!!!n)).(DomDS.st_in).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_non_sdomination; auto.
    apply XATree.make_predecessors_correct.
Qed.

Theorem dom_non_sdomination: forall res ni,
  DomDS.fixpoint (successors_blocks bs) transf entrypoints ni = Some res ->
  non_sdomination_prop res.
Proof.
  unfold DomDS.fixpoint. intros res ni PI. pattern res.
  eapply (PrimIter.iter_prop _ _ (DomDS.step _ _)
    (fun st => non_sdomination_prop st.(DomDS.st_in))); eauto.
    intros st GOOD. unfold DomDS.step.
    caseEq (AtomNodeSet.pick st.(DomDS.st_wrk)); auto.
    intros [n rem] PICK. apply step_non_sdomination; auto.

    apply start_non_sdomination.
Qed.

End DomComplete. End DomComplete.

Section sdom_is_complete.

Variable f:fdef.
Hypothesis branches_in_bound_fdef: branchs_in_fdef f.

Lemma sdom_is_complete: forall
  (l3 : l) (l' : l) s3 s'
  (HuniqF : uniqFdef f)
  (HBinF' : blockInFdefB (l', s') f = true)
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hsdom: strict_domination f l' l3),
  In l' (sdom f l3).
Proof.
  intros. 
  unfold sdom, dom_analyze in *. 
  destruct f as [fh bs].
  assert (Hentry:=Hsdom). apply DecDom.strict_domination__getEntryLabel in Hentry.
  destruct Hentry as [e Hentry].
  apply getEntryLabel__getEntryBlock in Hentry.
  destruct Hentry as [[le []] [Hentry Heq]]; subst e.
  rewrite Hentry.
  termination_tac2.
  eapply DomComplete.dom_non_sdomination with (entry:=le) in Hfix_tmn; eauto.
    SSCase "1".
      unfold DomComplete.non_sdomination_prop in Hfix_tmn.
      assert (vertexes_fdef (fdef_intro fh bs) (index l')) as J.
        apply blockInFdefB_in_vertexes in HBinF'; auto.
      destruct (Dominators.member_dec l' (dms!!l3)).
      SSSCase "1".
        unfold Dominators.member in H.
        destruct (dms!!l3); auto.
          apply blockInFdefB_in_bound_fdef in HBinF'. auto.

      SSSCase "2".
        apply Hfix_tmn with (l2:=l3) in J; auto.
          unfold DomComplete.non_sdomination in J.
          destruct J as [vl [al [J1 J2]]].
          unfold strict_domination in Hsdom. autounfold with cfg in Hsdom.
          rewrite Hentry in Hsdom.
          simpl in Hsdom.
          apply Hsdom in J1.
          destruct J1; subst; congruence.

    SSCase "2".
      split.
        simpl in *.
        destruct bs; uniq_result; auto.

        exists Dominators.top. 
        split; auto. simpl. apply set_eq_refl.
Qed.

End sdom_is_complete.

Module UnreachableDoms. Section UnreachableDoms.

Variable fh : fheader.
Variable bs : blocks.
Definition predecessors := XATree.make_predecessors (successors_blocks bs).
Definition transf := transfer.
Definition top := Dominators.top.
Definition bot := Dominators.bot.
Variable entry: l.
Variable entrypoints: list (atom * DomDS.L.t).

Hypothesis wf_entrypoints:
  match bs with
  | (l0, _) :: _ => l0 = entry
  | _ => False
  end /\
  exists v, [(entry, v)] = entrypoints /\ Dominators.eq v top.

Definition unreachable_doms (res: AMap.t DomDS.L.t) : Prop :=
  forall l0, ~ reachable (fdef_intro fh bs) l0 -> l0 <> entry ->
  Dominators.eq res!!l0 bot.

Lemma start_unreachable_doms:
  unreachable_doms
    (DomDS.st_in (DomDS.start_state (successors_blocks bs) entrypoints)).
Proof.
  intros l0 Hunreach Heq.
  unfold DomDS.start_state. simpl.
  eapply EntryDomsOthers.dom_nonentry_start_state_in in Heq; eauto.
Qed.

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma propagate_succ_unreachable_doms: forall st n out,
  (~ reachable (fdef_intro fh bs) n -> n <> entry -> 
   Dominators.eq out bot) ->
  unreachable_doms st.(DomDS.st_in) ->
  unreachable_doms (DomDS.propagate_succ st out n).(DomDS.st_in).
Proof.
  unfold unreachable_doms.
  intros.
  destruct (@DomDS.propagate_succ_spec st out n) as [J1 J2].
  assert (H':=H1).
  apply H0 in H1; auto.
  destruct (eq_atom_dec n l0); subst.
    apply H in H'; auto.
    apply Dominators.eq_trans with
      (y:=DomDS.L.lub (DomDS.st_in st) !! l0 out); auto.
    apply Dominators.eq_trans with (y:=DomDS.L.lub bot bot); auto.
       apply Dominators.lub_compat_eq; auto.
       apply Dominators.eq_sym. apply Dominators.lub_refl.

    rewrite J2; auto.
Qed.

Lemma propagate_succ_list_unreachable_doms:
  forall scs st out,
  (forall s, In s scs ->
             ~ reachable (fdef_intro fh bs) s -> s <> entry ->
             Dominators.eq out bot) ->
  unreachable_doms st.(DomDS.st_in) ->
  unreachable_doms (DomDS.propagate_succ_list st out scs).(DomDS.st_in).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs.
      intros. apply H with (s:=s); auto.
      apply propagate_succ_unreachable_doms; auto.
        intros J1 J2. eapply H; eauto.
Qed.

Hypothesis UniqF: uniqFdef (fdef_intro fh bs).

Lemma step_unreachable_doms:
  forall st n rem,
  AtomNodeSet.pick st.(DomDS.st_wrk) = Some(n, rem) ->
  unreachable_doms st.(DomDS.st_in) ->
  unreachable_doms (DomDS.propagate_succ_list 
                                  (DomDS.mkstate st.(DomDS.st_in) rem)
                                  (transf n st.(DomDS.st_in)!!n)
                                  ((successors_blocks bs)!!!n)).(DomDS.st_in).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_unreachable_doms; auto.
  intros s Hin Hunreach.
    destruct (reachable_dec (fdef_intro fh bs) n).
    Case "reach".
      assert(exists ps0, exists cs0, exists tmn0,
        blockInFdefB (n, stmts_intro ps0 cs0 tmn0) (fdef_intro fh bs) /\
        In s (successors_terminator tmn0)) as J.
        apply successors__blockInFdefB; auto.
      destruct J as [ps0 [cs0 [tmn0 [J1 J2]]]].
      eapply DecRD.reachable_successors with (l1:=s) in H; eauto.
        congruence.
        eapply XATree.in_succ__in_cfg; eauto.

    Case "unreach".
      apply GOOD in H. simpl in H.
      unfold transf, transfer.
      intros.
      destruct (eq_atom_dec n entry); subst.
        assert (exists ps0, exists cs0, exists tmn0,
          blockInFdefB (entry, stmts_intro ps0 cs0 tmn0) (fdef_intro fh bs) /\
          In s (successors_terminator tmn0)) as J.
          apply successors__blockInFdefB; auto.
        destruct J as [ps0 [cs0 [tmn0 [J1 J2]]]].
        contradict Hunreach.
        unfold reachable. 
        destruct wf_entrypoints as [J _].
        destruct bs as [|b ?]; tinv J. 
        destruct b as [l5 ? ? ?]. subst entry. 
Local Opaque successors. 
        simpl. clear J.
        exists (index l5::nil). exists (A_ends (index s) (index l5)::nil).
        constructor; eauto.
          constructor.
            eapply entry_in_vertexes; simpl; eauto.
          eapply XATree.in_succ__in_cfg; eauto.
      apply Dominators.eq_trans with (y:=Dominators.add (Dominators.bot) n).
        apply Dominators.add_eq; auto.
        apply Dominators.add_bot.
Transparent successors.
Qed.

Theorem dom_unreachable_doms: forall res ni,
  DomDS.fixpoint (successors_blocks bs) transf entrypoints ni = Some res ->
  unreachable_doms res.
Proof.
  unfold DomDS.fixpoint. intros res ni PI. pattern res.
  eapply (PrimIter.iter_prop _ _ (DomDS.step _ _)
    (fun st => unreachable_doms st.(DomDS.st_in))); eauto.
  intros st GOOD. unfold DomDS.step.
  caseEq (AtomNodeSet.pick st.(DomDS.st_wrk)); auto.
  intros [n rem] PICK.
  apply step_unreachable_doms; auto.
    apply start_unreachable_doms.
Qed.

End UnreachableDoms. End UnreachableDoms. 

Section dom_unreachable.

Variable f:fdef.
Hypothesis branches_in_bound_fdef: branchs_in_fdef f.
Hypothesis Hhasentry: getEntryBlock f <> None.

Lemma dom_unreachable: forall
  (l3 : l) s3
  (HuniqF: uniqFdef f)
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hunreach: ~ reachable f l3),
  sdom f l3 = bound_fdef f.
Proof.
  intros.
  case_eq (getEntryBlock f); try congruence.
  intros [l0 [p c t]] Hentry. 
  match goal with | H1: getEntryBlock _ = _ |- _ =>
    assert (J:=H1); apply dom_entrypoint in H1 end.
  destruct f as [fh bs].
  destruct (id_dec l3 l0); subst.
  Case "l3=l0".
    contradict Hunreach.
    eapply reachable_entrypoint; eauto.
  Case "l3<>l0".
    unfold sdom, dom_analyze in *.
    match goal with | H1: getEntryBlock _ = _ |- _ => rewrite H1 in * end.
    termination_tac2.
    eapply UnreachableDoms.dom_unreachable_doms with (entry:=l0) in Hfix_tmn;
      eauto.
    SCase "1".
      apply Hfix_tmn in n; auto.
      simpl. destruct dms !! l3; tinv n. auto.
    SCase "2".
      split.
        simpl in J.
        destruct bs; uniq_result; auto.

        exists Dominators.top. 
        split; auto. simpl. apply set_eq_refl.
Qed.

End dom_unreachable.

Section pres_dom.

Variable ftrans: fdef -> fdef.
Variable btrans: block -> block.

Hypothesis ftrans_spec: forall fh bs, 
  ftrans (fdef_intro fh bs) = fdef_intro fh (List.map btrans bs).

Hypothesis btrans_eq_label: forall b, getBlockLabel b = getBlockLabel (btrans b).

Lemma pres_getEntryBlock : forall f b
  (Hentry : getEntryBlock f = Some b),
  getEntryBlock (ftrans f) = Some (btrans b).
Proof.
  intros. destruct f as [fh bs]. rewrite ftrans_spec.
  destruct bs; inv Hentry; auto.
Qed.

Lemma pres_getEntryBlock_None : forall f
  (Hentry : getEntryBlock f = None),
  getEntryBlock (ftrans f) = None.
Proof.
  intros. destruct f as [fh bs]. rewrite ftrans_spec.
  destruct bs; inv Hentry; auto.
Qed.

Lemma pres_bound_blocks : forall bs,
  bound_blocks bs = bound_blocks (List.map btrans bs).
Proof.
  induction bs as [|a bs]; simpl; auto.
    assert (J:=btrans_eq_label a);
    remember (btrans a) as R.
    destruct R as [l1 ? ? ?]; destruct a; simpl in *; subst l1.
    congruence.
Qed.

Hypothesis btrans_eq_tmn: forall b, 
  terminator_match (getTerminator b) (getTerminator (btrans b)).

Lemma pres_successors_blocks : forall bs,
  successors_blocks bs = successors_blocks (List.map btrans bs).
Proof.
  induction bs as [|b bs]; simpl; auto.
    assert (J:=btrans_eq_tmn b).
    assert (J':=btrans_eq_label b).
    remember (btrans b) as R.
    destruct R as [l1 []]; destruct b as [? []]; simpl in *; subst l1.
    rewrite IHbs. 
    terminator_match_tac.
Qed.

Lemma pres_num_iters: forall f, num_iters f = num_iters (ftrans f).
Proof.
  destruct f as [fh bs]. 
  rewrite ftrans_spec. unfold num_iters. simpl.
  f_equal.
  generalize 3%positive.
  induction bs; simpl; intros; auto.
Qed.

Lemma pres_sdom: forall (f : fdef) (l5 l0 : l),
  ListSet.set_In l5 (AlgDom.sdom f l0) <->
  ListSet.set_In l5 (AlgDom.sdom (ftrans f) l0).
Proof.
  intros.
  unfold AlgDom.sdom, AlgDom.dom_analyze. destruct f as [fh bs]. 
  case_eq (getEntryBlock (fdef_intro fh bs)).
    intros b Hentry.
    apply pres_getEntryBlock in Hentry; eauto.
    assert (J:=btrans_eq_label b);
    remember (btrans b) as R.
    destruct R as [l1 ? ? ?]; destruct b; simpl in *; subst l1.
    rewrite Hentry. rewrite <- pres_num_iters.
    rewrite ftrans_spec. simpl.
    rewrite <- pres_bound_blocks.
    rewrite <- pres_successors_blocks. split; eauto.

    intros Hentry.
    apply pres_getEntryBlock_None in Hentry; eauto.
    rewrite Hentry. rewrite ftrans_spec. simpl.
    rewrite <- pres_bound_blocks. split; auto.
Qed.

End pres_dom.

End AlgDom.

Module AlgDomProps := AlgDom_Properties (AlgDom).
