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

Definition dom_analyze (f: fdef) : AMap.t Dominators.t :=
  let '(fdef_intro _ bs) := f in
  let top := Dominators.top in
  match getEntryBlock f with
  | Some (block_intro le _ _ _) =>
      match DomDS.fixpoint (successors_blocks bs) transfer
        ((le, top) :: nil) with
      | None => AMap.init top
      | Some res => res
      end
  | None => AMap.init top
  end.

Definition dom_analysis_is_successful (f: fdef) : Prop :=
  let '(fdef_intro _ bs) := f in
  let top := Dominators.top in
  match getEntryBlock f with
  | Some (block_intro le _ _ _) =>
      match DomDS.fixpoint (successors_blocks bs) transfer
        ((le, top) :: nil) with
      | None => False
      | Some res => True
      end
  | None => False
  end.

Definition bound_dom bd (res: Dominators.t) : set atom :=
match res with
| Some dts2 => dts2
| None => bd
end.

Definition dom_query f : atom -> set atom :=
let dt := dom_analyze f in
let b := bound_fdef f in
fun l0 => bound_dom b (dt !! l0).

Import AtomSet.

Lemma dom_entrypoint : forall f l0 ps cs tmn
  (Hentry : getEntryBlock f = Some (block_intro l0 ps cs tmn)),
  dom_query f l0 = nil.
Proof.
  intros.
  unfold dom_query, dom_analyze.
  destruct f as [f b].
  rewrite Hentry.
  remember (DomDS.fixpoint (successors_blocks b)
                transfer ((l0, Dominators.top) :: nil)) as R1.
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
  | block_intro l0 _ _ _ :: _ => l0 = entry
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

Theorem dom_entry_doms_others: forall res,
  DomDS.fixpoint (successors_blocks bs) transf entrypoints = Some res ->
  entry_doms_others res.
Proof.
  unfold DomDS.fixpoint. intros res PI. pattern res.
  eapply (PrimIter.iterate_prop _ _ (DomDS.step _ _)
    (fun st => entry_doms_others st.(DomDS.st_in))); eauto.
  intros st GOOD. unfold DomDS.step.
  caseEq (AtomNodeSet.pick st.(DomDS.st_wrk)); auto.
  intros [n rem] PICK.
  apply step_entry_doms_others; auto.
    apply start_entry_doms_others.
Qed.

Lemma dom_solution_ge: forall res,
  DomDS.fixpoint (successors_blocks bs) transf entrypoints = Some res ->
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

Section entry_doms_others.

Variable f:fdef.

Lemma entry_doms_others: forall
  entry
  (Hex: dom_analysis_is_successful f)
  (H: getEntryLabel f = Some entry),
  (forall b (H0: b <> entry /\ reachable f b),
     ListSet.set_In entry (AlgDom.dom_query f b)).
Proof.
  intros.
  destruct H0 as [J1 J2].
  unfold dom_query, dom_analyze.
  unfold dom_analysis_is_successful in Hex.
  destruct f as [fh b0].
  remember (getEntryBlock (fdef_intro fh b0)) as R.
  destruct R as [[l1 p c t]|]; try tauto.
  destruct b0 as [|b0 b2]; inv HeqR.
  inv H.
  remember (
      DomDS.fixpoint 
           (successors_blocks (block_intro entry p c t :: b2))
           transfer
           ((entry, Dominators.top) :: nil)) as R.
  destruct R; try tauto.
  symmetry in HeqR.
  eapply EntryDomsOthers.dom_entry_doms_others with (entry:=entry) in HeqR; 
    eauto.
  Case "1".
    unfold EntryDomsOthers.entry_doms_others in HeqR.
    apply HeqR in J1.
    unfold Dominators.member in J1.
    destruct (t0 !! b); simpl; auto.

  Case "2".
    split; auto.
      exists Dominators.top.
      simpl.
      split; auto.
        split; intros x Hin; auto.
Qed.

End entry_doms_others.

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
      apply incl_inter_left; auto.

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

Lemma step_wf_doms:
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

Theorem fixpoint_wf: forall res,
  DomDS.fixpoint succs transf entrypoints = Some res ->
  wf_doms res.
Proof.
  unfold DomDS.fixpoint. intros res PI. pattern res.
  eapply (PrimIter.iterate_prop _ _ (DomDS.step _ _)
    (fun st => wf_doms st.(DomDS.st_in))); eauto.
    intros st GOOD. unfold DomDS.step.
    caseEq (AtomNodeSet.pick st.(DomDS.st_wrk)); auto.
    intros [n rem] PICK.
    apply step_wf_doms; auto.

    apply start_wf_doms.
Qed.

End DomsInParents. End DomsInParents.

Lemma dom_in_bound: forall successors le t
  (Hfix: DomDS.fixpoint successors transfer
            ((le, Dominators.top) :: nil) = Some t),
  forall l0 ns0 (Hget: t !! l0 = Some ns0) n (Hin: In n ns0),
    In n (XATree.parents_of_tree successors).
Proof.
  intros.
  apply DomsInParents.fixpoint_wf in Hfix; auto.
  assert (J:=Hfix l0).
  unfold DomsInParents.wf_dom in J.
  rewrite Hget in J. auto.
Qed.

Lemma dom_in_bound_blocks: forall bs le t
  (Hfix: DomDS.fixpoint (successors_blocks bs) transfer
            ((le, Dominators.top) :: nil) = Some t),
  forall l0 ns0 (Hget: t !! l0 = Some ns0), incl ns0 (bound_blocks bs).
Proof.
  intros.
  intros x Hinx.
  apply in_parents__in_bound.
  eapply dom_in_bound; eauto.
Qed.

Lemma dom_query_in_bound: forall fh bs l5, 
  incl (dom_query (fdef_intro fh bs) l5) (bound_blocks bs).
Proof.
  intros.
  unfold dom_query, dom_analyze.
  destruct (getEntryBlock (fdef_intro fh bs)) as [[]|]; simpl. 
    remember (DomDS.fixpoint (successors_blocks bs) transfer
                ((l0, Dominators.top) :: nil)) as R.
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
  (Heqdefs3 : contents3 = dom_query f l3)
  (Heqdefs' : contents' = dom_query f l'),
  incl contents' (l3 :: contents3).
Proof.
  intros. 
  unfold dom_query, dom_analyze in *.
  remember (getEntryBlock f) as R.
  destruct f as [fh bs].
  destruct R as [[le ? ? ?]|].
  Case "entry is good".
    remember (DomDS.fixpoint (successors_blocks bs)
                transfer ((le, Dominators.top) :: nil)) as R1.
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
  | block_intro l0 _ _ _ :: _ => l0 = entry
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

Theorem dom_non_sdomination: forall res,
  DomDS.fixpoint (successors_blocks bs) transf entrypoints = Some res ->
  non_sdomination_prop res.
Proof.
  unfold DomDS.fixpoint. intros res PI. pattern res.
  eapply (PrimIter.iterate_prop _ _ (DomDS.step _ _)
    (fun st => non_sdomination_prop st.(DomDS.st_in))); eauto.
    intros st GOOD. unfold DomDS.step.
    caseEq (AtomNodeSet.pick st.(DomDS.st_wrk)); auto.
    intros [n rem] PICK. apply step_non_sdomination; auto.

    apply start_non_sdomination.
Qed.

End DomComplete. End DomComplete.

Section sdom_is_complete.

Variable f:fdef.

Lemma sdom_is_complete: forall
  (l3 : l) (l' : l) ps cs tmn ps' cs' tmn'
  (HuniqF : uniqFdef f)
  (Hsucc: dom_analysis_is_successful f)
  (HBinF' : blockInFdefB (block_intro l' ps' cs' tmn') f = true)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hsdom: strict_domination f l' l3),
  In l' (dom_query f l3).
Proof.
  intros. 
  unfold dom_analysis_is_successful, 
         dom_query, dom_analyze in *. 
  destruct f as [fh bs].
  remember (getEntryBlock (fdef_intro fh bs)) as R.
  destruct R as [[le ? ? ?] | ]; try tauto.
  remember (DomDS.fixpoint 
                  (successors_blocks bs)
                  transfer
                  ((le, Dominators.top) :: nil)) as R.
  destruct R; try tauto.
      symmetry in HeqR0.
      eapply DomComplete.dom_non_sdomination with (entry:=le) in HeqR0; eauto.
      SSCase "1".
        Focus.
        unfold DomComplete.non_sdomination_prop in HeqR0.
        assert (vertexes_fdef (fdef_intro fh bs) (index l')) as J.
          apply blockInFdefB_in_vertexes in HBinF'; auto.
        destruct (Dominators.member_dec l' (t!!l3)).
        SSSCase "1".
          unfold Dominators.member in H.
          destruct (t!!l3); auto.
            apply blockInFdefB_in_bound_fdef in HBinF'. auto.

        SSSCase "2".
          apply HeqR0 with (l2:=l3) in J; auto.
            unfold DomComplete.non_sdomination in J.
            destruct J as [vl [al [J1 J2]]].
            unfold strict_domination in Hsdom. autounfold with cfg in Hsdom.
            rewrite <- HeqR in Hsdom.
            simpl in Hsdom.
            apply Hsdom in J1.
            destruct J1; subst; congruence.
        Unfocus.

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
  | block_intro l0 _ _ _ :: _ => l0 = entry
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
        blockInFdefB (block_intro n ps0 cs0 tmn0) (fdef_intro fh bs) /\
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
          blockInFdefB (block_intro entry ps0 cs0 tmn0) (fdef_intro fh bs) /\
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

Theorem dom_unreachable_doms: forall res,
  DomDS.fixpoint (successors_blocks bs) transf entrypoints = Some res ->
  unreachable_doms res.
Proof.
  unfold DomDS.fixpoint. intros res PI. pattern res.
  eapply (PrimIter.iterate_prop _ _ (DomDS.step _ _)
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

Hypothesis Hhasentry: getEntryBlock f <> None.

Lemma dom_unreachable: forall
  (l3 : l) (l' : l) ps cs tmn
  (Hsucc: dom_analysis_is_successful f)
  (HuniqF: uniqFdef f)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hunreach: ~ reachable f l3),
  dom_query f l3 = bound_fdef f.
Proof.
  intros.
  case_eq (getEntryBlock f); try congruence.
  intros [l0 p c t] Hentry. 
  match goal with | H1: getEntryBlock _ = _ |- _ =>
    assert (J:=H1); apply dom_entrypoint in H1 end.
  destruct f as [fh bs].
  destruct (id_dec l3 l0); subst.
  Case "l3=l0".
    contradict Hunreach.
    eapply reachable_entrypoint; eauto.
  Case "l3<>l0".
    unfold dom_query, dom_analyze, dom_analysis_is_successful in *.
    match goal with | H1: getEntryBlock _ = _ |- _ => rewrite H1 in * end.
    remember (DomDS.fixpoint 
                  (successors_blocks bs)
                  transfer
                  ((l0, Dominators.top) :: nil)) as R.
    destruct R; try tauto.
      symmetry in HeqR.
      eapply UnreachableDoms.dom_unreachable_doms with (entry:=l0) in HeqR;
        eauto.
      SCase "1".
        apply HeqR in n; auto.
        simpl. destruct t0 !! l3; tinv n. auto.
      SCase "2".
        split.
          simpl in J.
          destruct bs; uniq_result; auto.

          exists Dominators.top. 
          split; auto. simpl. apply set_eq_refl.
Qed.

End dom_unreachable.

Section sound_acyclic.

Variable f : fdef.
Hypothesis Hhasentry: getEntryBlock f <> None.

Lemma dom_is_sound : forall
  (l3 : l) (l' : l) ps cs tmn
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : In l' (l3::(dom_query f l3))),
  domination f l' l3.
Proof.
  unfold domination. autounfold with cfg.
  intros. destruct f as [fh bs].
  remember (getEntryBlock (fdef_intro fh bs)) as R.
  destruct R; try congruence. clear Hhasentry.
  destruct b as [l5 ps5 cs5 t5].
  intros vl al Hreach.
  generalize dependent ps.
  generalize dependent cs.
  generalize dependent tmn.
  remember (ACfg.vertexes (successors (fdef_intro fh bs))) as Vs.
  remember (ACfg.arcs (successors (fdef_intro fh bs))) as As.
  unfold ATree.elt, l in *.
  remember (index l3) as v0.
  remember (index l5) as v1.
  generalize dependent bs.
  generalize dependent l3.
  generalize dependent l5.
  induction Hreach; intros; subst.
    inv Heqv0. symmetry in HeqR.
    apply dom_entrypoint in HeqR.
    rewrite HeqR in Hin.
    simpl in Hin. destruct Hin as [Hin | Hin]; tinv Hin; auto.

    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0,
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) (fdef_intro fh bs) /\
      In l3 (successors_terminator tmn0)) as J.
      eapply successors__blockInFdefB; eauto.
    destruct J as [ps0 [cs0 [tmn0 [HBinF'' Hinsucc]]]].
    remember ((dom_analyze (fdef_intro fh bs)) !! a0) as R0.
    destruct (id_dec l' l3); subst; auto.
    left.
    assert (In l'
      (a0 :: (dom_query (fdef_intro fh bs) a0))) as J.
      assert (incl (dom_query (fdef_intro fh bs) l3)
                   (a0 :: (dom_query (fdef_intro fh bs) a0))) as Hinc.
        eapply dom_successors; eauto.
      simpl in Hin. destruct Hin; try congruence.
      apply Hinc; auto.
    eapply IHHreach in J; eauto.
    simpl.
    destruct J as [J | J]; subst; eauto.
Qed.

End sound_acyclic.

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
  terminator_match (getBlockTmn b) (getBlockTmn (btrans b)).

Lemma pres_successors_blocks : forall bs,
  successors_blocks bs = successors_blocks (List.map btrans bs).
Proof.
  induction bs as [|b bs]; simpl; auto.
    assert (J:=btrans_eq_tmn b).
    assert (J':=btrans_eq_label b).
    remember (btrans b) as R.
    destruct R as [l1 ? ? ?]; destruct b; simpl in *; subst l1.
    rewrite IHbs. 
    terminator_match_tac.
Qed.

Lemma pres_dom_query: forall (f : fdef) (l5 l0 : l),
  ListSet.set_In l5 (AlgDom.dom_query f l0) <->
  ListSet.set_In l5 (AlgDom.dom_query (ftrans f) l0).
Proof.
  intros.
  unfold AlgDom.dom_query, AlgDom.dom_analyze. destruct f as [fh bs]. 
  case_eq (getEntryBlock (fdef_intro fh bs)).
    intros b Hentry.
    apply pres_getEntryBlock in Hentry; eauto.
    assert (J:=btrans_eq_label b);
    remember (btrans b) as R.
    destruct R as [l1 ? ? ?]; destruct b; simpl in *; subst l1.
    rewrite Hentry. rewrite ftrans_spec. simpl.
    rewrite <- pres_bound_blocks.
    rewrite <- pres_successors_blocks. split; eauto.

    intros Hentry.
    apply pres_getEntryBlock_None in Hentry; eauto.
    rewrite Hentry. rewrite ftrans_spec. simpl.
    rewrite <- pres_bound_blocks. split; auto.
Qed.

Lemma pres_dom_analysis_is_successful : forall f,
  AlgDom.dom_analysis_is_successful f <-> 
    AlgDom.dom_analysis_is_successful (ftrans f).
Proof.
  unfold AlgDom.dom_analysis_is_successful.
  destruct f as [fh bs]. 
  case_eq (getEntryBlock (fdef_intro fh bs)).
    intros b Hentry.
    apply pres_getEntryBlock in Hentry; eauto.
    assert (J:=btrans_eq_label b);
    remember (btrans b) as R.
    destruct R as [l1 ? ? ?]; destruct b; simpl in *; subst l1.
    rewrite Hentry. rewrite ftrans_spec. simpl.
    rewrite <- pres_successors_blocks. split; eauto.

    intros Hentry.
    apply pres_getEntryBlock_None in Hentry; eauto.
    rewrite Hentry. rewrite ftrans_spec. simpl.
    split; auto.
Qed.

End pres_dom.

End AlgDom.

Module AlgDomProps := AlgDom_Properties (AlgDom).
