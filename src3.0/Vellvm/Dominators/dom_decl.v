Require Import List.
Require Import ListSet.
Require Import Coqlib.
Require Import Metatheory.
Require Import Maps.
Require Import Lattice.
Require Import Kildall.
Require Import Iteration.
Require Import cfg.
Require Import reach.
Require Import Dipaths.

Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Import LLVMsyntax.
Import LLVMinfra.

Module DecDom.

Lemma sdom_isnt_refl: forall f l1 l2 (Hreach: reachable f l2)
  (Hdom12 : strict_domination f l1 l2),
  l1 <> l2.
Proof.
  unfold reachable, strict_domination.
  intros.
  destruct (getEntryBlock f) as [[]|]; tinv Hreach.
  destruct Hreach as [vl [al Hreach]].
  apply Hdom12 in Hreach. 
  tauto.
Qed.

Lemma dom_tran: forall (f:fdef) (l1 l2 l3:l),
  domination f l1 l2 -> domination f l2 l3 -> domination f l1 l3.
Proof.
  unfold domination. autounfold with cfg.
  intros.
  destruct (getEntryBlock f); tinv H.
  destruct b.
  intros vl al Hw.
  destruct (id_dec l1 l3); auto.
  left.
  assert (Hw':=Hw).
  apply H0 in Hw'.
  destruct Hw' as [Hw' | Hw']; subst.
    apply DW_extract with (x:=index l2)(eq_a_dec:=eq_atom_dec) in Hw; 
      simpl; auto.
    destruct Hw as [al' Hw].
    assert (Hw'':=Hw).
    apply H in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; auto.
    destruct (id_dec l1 l2); subst; auto.
    apply V_extract_spec in Hw''; try congruence.
    simpl in Hw''. 
    destruct Hw'' as [Hw'' | Hw'']; auto.
      uniq_result. congruence.

    assert (Hw'':=Hw).
    apply H in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; congruence.
Qed.

Lemma everything_dominates_unreachable_blocks :
  forall f l1 l2 (Hreach: ~ reachable f l2)
  (Hentry: getEntryBlock f <> None),
  domination f l1 l2.
Proof.
  unfold reachable, domination. autounfold with cfg.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b.
  intros.
  contradict Hreach. eauto.
Qed.

Lemma everything_sdominates_unreachable_blocks :
  forall f l1 l2 (Hreach: ~ reachable f l2)
  (Hentry: getEntryBlock f <> None),
  strict_domination f l1 l2.
Proof.
  unfold reachable, strict_domination. autounfold with cfg.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b.
  intros.
  contradict Hreach. eauto.
Qed.

Lemma sdom_reachable : forall f l1 l2,
  reachable f l2 -> strict_domination f l1 l2 -> reachable f l1.
Proof.
  unfold reachable, strict_domination, domination.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b.
  destruct H as [vl [al H]].
  assert (H':=H).
  apply H0 in H'. destruct H' as [J1 J2].
  apply DW_extract with (x:=index l1)(eq_a_dec:=eq_atom_dec) in H; 
    simpl; auto.
  destruct H as [al' H].
  exists (V_extract eq_atom_dec (index l1) (index l2 :: vl)). exists al'.
  auto.
Qed.

Lemma dom_reachable : forall f l1 l2,
  reachable f l2 -> domination f l1 l2 -> reachable f l1.
Proof.
  unfold reachable, domination.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b.
  destruct H as [vl [al H]].
  assert (H':=H).
  apply H0 in H'.
  apply DW_extract with (x:=index l1)(eq_a_dec:=eq_atom_dec) in H; simpl; auto.
    destruct H as [al' H].
    exists (V_extract eq_atom_dec (index l1) (index l2 :: vl)). exists al'. auto.

    destruct H' as [H' | H']; subst; auto.
Qed.

Lemma sdom_dom: forall f l1 l2,
  strict_domination f l1 l2 -> domination f l1 l2.
Proof.
  unfold strict_domination, domination. autounfold with cfg.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b. intros. apply H in H0. destruct H0; auto.
Qed.

Lemma dom_sdom: forall f l1 l2,
  domination f l1 l2 -> l1 <> l2 -> strict_domination f l1 l2.
Proof.
  unfold strict_domination, domination. autounfold with cfg.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b. intros. apply H in H1.
  destruct H1 as [H1 | H1]; subst; auto.
    congruence.
Qed.

Lemma domination_has_entry: forall f l1 l2 (Hdom: domination f l1 l2),
  getEntryBlock f <> None.
Proof.
  intros.
  unfold domination in Hdom.
  intro EQ. rewrite EQ in Hdom. auto.
Qed.

Section dom_acyclic_tran.

Variable f:fdef.

Hypothesis getEntryBlock_inv : forall
  (l3 : l)
  (l' : l)
  (ps : phinodes)
  (cs : cmds)
  (tmn : terminator)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hsucc : In l' (successors_terminator tmn)) a ps0 cs0 tmn0
  (H : getEntryBlock f = Some (block_intro a ps0 cs0 tmn0)),
  l' <> a.

Lemma dom_acyclic: forall (l1 l2:l)
  (H: reachable f l2) (H0: strict_domination f l1 l2),
  ~ domination f l2 l1.
Proof.
  unfold reachable, strict_domination, domination.
  intros. 
  remember (getEntryBlock f) as R.
  destruct R; auto. 
  destruct b as [l0 ? ? ?].
  destruct H as [vl [al Hw]].
  apply DWalk_to_dpath in Hw; auto.
  destruct Hw as [vl0 [al0 Hp]].
  assert (Hw:=Hp).
  apply D_path_isa_walk in Hw.
  assert (Hw':=Hw).
  apply H0 in Hw'.
  destruct Hw' as [J1 J2].
  intros J.
  apply DW_extract with (x:=index l1)(eq_a_dec:=eq_atom_dec) in Hw; 
    simpl; auto.
  destruct Hw as [al' Hw].
  assert (Hw'':=Hw).
  apply J in Hw''.
  destruct Hw'' as [Hw'' | Hw'']; subst; auto.
  apply V_extract_spec' in Hw''; try congruence.
  inv Hp.
    inv Hw''.

    simpl in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; try congruence.
    apply H5 in Hw''. inv Hw''.
    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0,
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) f /\
      In l0 (successors_terminator tmn0)) as J'.
      eapply successors__blockInFdefB; eauto.
    destruct J' as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
    symmetry in HeqR. destruct f.
    eapply getEntryBlock_inv in Hinsucc; eauto.
Qed.

Lemma sdom_tran1: forall (l1 l2 l3:l),
  strict_domination f l1 l2 -> domination f l2 l3 -> strict_domination f l1 l3.
Proof.
  intros.
  destruct (id_dec l1 l3); subst.
    destruct (@reachable_dec f l3).
      eapply dom_acyclic in H; eauto.
        contradict H; auto.
        apply dom_reachable in H0; auto.

      apply everything_sdominates_unreachable_blocks; auto.
        eapply domination_has_entry; eauto.

    apply sdom_dom in H.
    apply dom_sdom; eauto using dom_tran.
Qed.

Lemma sdom_tran2: forall (l1 l2 l3:l),
  domination f l1 l2 -> strict_domination f l2 l3 -> strict_domination f l1 l3.
Proof.
  intros.
  destruct (id_dec l1 l3); subst.
    destruct (@reachable_dec f l3).
      eapply dom_acyclic in H0; eauto.
      contradict H0; auto.

      apply everything_sdominates_unreachable_blocks; auto.
        eapply domination_has_entry; eauto.

    apply sdom_dom in H0.
    apply dom_sdom; eauto using dom_tran.
Qed.

Lemma sdom_tran: forall (l1 l2 l3:l),
  strict_domination f l1 l2 -> strict_domination f l2 l3 ->
  strict_domination f l1 l3.
Proof.
  intros. apply sdom_dom in H0. eapply sdom_tran1; eauto.
Qed.

End dom_acyclic_tran.

Lemma sdom_dec : forall f l1 l2,
  strict_domination f l1 l2 \/ ~ strict_domination f l1 l2.
Proof. intros. tauto. Qed. (* classic logic *)

Import Classical_Pred_Type.

Lemma non_sdom__inv: forall f l1 l2 be (Hentry: getEntryBlock f = Some be)
  (Hnsdom: ~ strict_domination f l1 l2),
  exists vl, exists al, D_walk (vertexes_fdef f) (arcs_fdef f) 
    (index l2) (index (getBlockLabel be)) vl al /\
    ~ (In (index l1) vl /\ l1 <> l2).
Proof.
  intros.
  unfold strict_domination, domination in Hnsdom. 
  autounfold with cfg in Hnsdom.
  rewrite Hentry in Hnsdom.
  destruct be. subst.
  apply not_all_ex_not in Hnsdom. 
  destruct Hnsdom as [vl Hnsdom].
  apply not_all_ex_not in Hnsdom. 
  destruct Hnsdom as [al Hnsdom].
  exists vl. exists al.
  tauto.
Qed.

Lemma sdom_ordered : forall f l1 l2 l3
  (Hneq: l1 <> l2) (Hreach: reachable f l3)
  (Hsdom: strict_domination f l1 l3)
  (Hsdom': strict_domination f l2 l3),
  strict_domination f l1 l2 \/ strict_domination f l2 l1.
Proof.
  intros.
  destruct (sdom_dec f l1 l2) as [|Hnsdom12]; auto.
  destruct (sdom_dec f l2 l1) as [|Hnsdom21]; auto.
  contradict Hsdom. intro Hsdom.
  unfold strict_domination, reachable in Hsdom, Hsdom', Hreach. 
  autounfold with cfg in Hsdom, Hsdom'.
  remember (getEntryBlock f) as entry.
  destruct entry as [[l0 ? ? ?]|]; try congruence.
  destruct Hreach as [vl [al Hreach]].
  assert (Hw:=Hreach).
  apply Hsdom in Hw.
  destruct Hw as [Hin Hneq13].
  assert (Hw:=Hreach).
  apply Hsdom' in Hw.
  destruct Hw as [Hin' Heq23].

  (* on Hw, we need to figuire the closest one to l3 in l1 and l2,
     suppose l1 is, then we split hw at l1, so l2 cannot be in the part
     from l3 to l1.
  *)
  assert (Hw:=Hreach).
  assert (vl <> V_nil) as Hnqnil.
    destruct vl; auto.
      intro J. inv J.
  apply DW_cut with (x:=index l1) (w:=index l2) in Hw; try congruence;
    simpl; auto.
  destruct Hw as [al1 [al2 [vl1 [vl2
    [[J1 [J2 [J3 [J4 J5]]]]|[J1 [J2 [J3 [J4 J5]]]]]]]]]; subst.
  Case "1".
  eapply non_sdom__inv in Hnsdom21; eauto.
  destruct Hnsdom21 as [vl1' [al1' [J1' J2']]].

  assert ((D_walk (vertexes_fdef f) (arcs_fdef f) (index l3) (index l0)
    (vl1++vl1') (al1++al1') * ~ In (index l2) (vl1++vl1'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5 Hneq.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hsdom' in J3.
  destruct J3 as [Hin'' Heq]; auto.

  Case "2".
  eapply non_sdom__inv in Hnsdom12; eauto.
  destruct Hnsdom12 as [vl2' [al2' [J1' J2']]].

  assert ((D_walk (vertexes_fdef f) (arcs_fdef f) (index l3) (index l0)
    (vl1++vl2') (al1++al2') * ~ In (index l1) (vl1++vl2'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5 Hneq.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hsdom in J3.
  destruct J3 as [Hin'' Heq]; auto.
Qed.

End DecDom.
