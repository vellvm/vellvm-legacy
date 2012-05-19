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
Require Import Dipaths.

Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Import LLVMsyntax.
Import LLVMinfra.

Module DecDom.

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
  destruct H0 as [J1 J2].
  assert (Hw':=Hw).
  apply J1 in Hw'.
  destruct Hw' as [Hw' | Hw']; subst; try congruence.
  intros J.
  apply DW_extract with (x:=index l1)(eq_a_dec:=eq_atom_dec) in Hw; 
    simpl; auto.
  destruct Hw as [al' Hw].
  assert (Hw'':=Hw).
  apply J in Hw''.
  destruct Hw'' as [Hw'' | Hw'']; subst; auto.
  apply V_extract_spec' in Hw''; try congruence.
  inv Hp.
    inv Hw'.

    simpl in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; try congruence.
    apply H4 in Hw''. inv Hw''.
    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0,
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) f /\
      In l0 (successors_terminator tmn0)) as J'.
      eapply successors__blockInFdefB; eauto.
    destruct J' as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
    symmetry in HeqR. 
    eapply getEntryBlock_inv in Hinsucc; eauto.
Qed.

Lemma sdom_tran1: forall (l1 l2 l3:l) (Hreach: reachable f l2),
  strict_domination f l1 l2 -> domination f l2 l3 -> strict_domination f l1 l3.
Proof.
  intros.
  destruct (id_dec l1 l3); subst.
    eapply dom_acyclic in H; eauto.
    contradict H; auto.

    destruct H.
    split; eauto using dom_tran.
Qed.

Lemma sdom_tran2: forall (l1 l2 l3:l) (Hreach: reachable f l3),
  domination f l1 l2 -> strict_domination f l2 l3 -> strict_domination f l1 l3.
Proof.
  intros.
  destruct (id_dec l1 l3); subst.
    eapply dom_acyclic in H0; eauto.
    contradict H0; auto.

    destruct H0.
    split; eauto using dom_tran.
Qed.

Lemma sdom_tran: forall (l1 l2 l3:l) (Hreach: reachable f l2),
  strict_domination f l1 l2 -> strict_domination f l2 l3 ->
  strict_domination f l1 l3.
Proof.
  intros. destruct H0. eapply sdom_tran1; eauto.
Qed.

End dom_acyclic_tran.

Lemma sdom_reachable : forall f l1 l2,
  reachable f l2 -> strict_domination f l1 l2 -> reachable f l1.
Proof.
  unfold reachable, strict_domination, domination.
  intros.
  destruct H0 as [J1 J2].
  destruct (getEntryBlock f); try congruence.
  destruct b.
  destruct H as [vl [al H]].
  assert (H':=H).
  apply J1 in H'.
  assert (In (index l1) vl) as Hin.
    destruct H' as [H' | H']; subst; auto; congruence.
  apply DW_extract with (x:=index l1)(eq_a_dec:=eq_atom_dec) in H; 
    simpl; auto.
  destruct H as [al' H].
  exists (V_extract eq_atom_dec (index l1) (index l2 :: vl)). exists al'.
  auto.
Qed.

Lemma dom_reachable : forall f l1 l2,
  reachable f l2 -> domination f l1 l2 -> reachable f l1.
Proof.
  intros.
  destruct (id_dec l1 l2); subst; auto.
  eapply sdom_reachable; eauto. split; auto.
Qed.

Lemma sdom_dec : forall f l1 l2,
  strict_domination f l1 l2 \/ ~ strict_domination f l1 l2.
Proof. intros. tauto. Qed. (* classic logic *)

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

Lemma tauto_helper : forall A B:Prop,
  A -> ~ (B /\ A) -> ~ B.
Proof. tauto. Qed.

Import Classical_Pred_Type.

Lemma sdom_ordered : forall f l1 l2 l3
  (Hneq: l1 <> l2) (Hreach: reachable f l3)
  (Hsdom: strict_domination f l1 l3)
  (Hsdom': strict_domination f l2 l3),
  strict_domination f l1 l2 \/ strict_domination f l2 l1.
Proof.
  intros.
  destruct (sdom_dec f l1 l2); auto.
  destruct (sdom_dec f l2 l1); auto.
  contradict Hsdom'. intro Hsdom'.
  unfold strict_domination in *.
  destruct Hsdom as [Hdom Hneq1].
  destruct Hsdom' as [Hdom' Hneq2].
  unfold domination, reachable in *. autounfold with cfg in *.
  destruct (getEntryBlock f); auto.
  destruct b as [l0 ? ? ?].
  destruct Hreach as [vl [al Hreach]].
  assert (Hw:=Hreach).
  apply Hdom in Hw.
  destruct Hw as [Hin | Heq]; try congruence.
  assert (Hw:=Hreach).
  apply Hdom' in Hw.
  destruct Hw as [Hin' | Heq]; try congruence.

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
  assert (exists vl:V_list, exists al:A_list,
    D_walk (vertexes_fdef f) (arcs_fdef f) (index l1) (index l0) vl al /\
    ~ In (index l2) vl) as J.
    clear - Hneq H0.
    apply tauto_helper in H0; auto.
    apply not_all_ex_not in H0. (* can we remove the classic lemma? *)
    destruct H0 as [vl H0].
    apply not_all_ex_not in H0.
    destruct H0 as [al H0].
    exists vl. exists al.
    tauto.
  destruct J as [vl1' [al1' [J1' J2']]].

  assert ((D_walk (vertexes_fdef f) (arcs_fdef f) (index l3) (index l0)
    (vl1++vl1') (al1++al1') * ~ In (index l2) (vl1++vl1'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hdom' in J3.
  destruct J3 as [Hin'' | Heq]; try congruence; auto.

  Case "2".
  assert (exists vl:V_list, exists al:A_list,
    D_walk (vertexes_fdef f) (arcs_fdef f) (index l2) (index l0) vl al /\
    ~ In (index l1) vl) as J.
    clear - Hneq H.
    apply tauto_helper in H; auto.
    apply not_all_ex_not in H.
    destruct H as [vl H].
    apply not_all_ex_not in H.
    destruct H as [al H].
    exists vl. exists al.
    tauto.
  destruct J as [vl2' [al2' [J1' J2']]].

  assert ((D_walk (vertexes_fdef f) (arcs_fdef f) (index l3) (index l0)
    (vl1++vl2') (al1++al2') * ~ In (index l1) (vl1++vl2'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hdom in J3.
  destruct J3 as [Hin'' | Heq]; try congruence; auto.
Qed.

Lemma non_sdom__inv: forall f l1 l2 be (Hentry: getEntryBlock f = Some be)
  (Hnsdom: ~ strict_domination f l1 l2),
  l1 = l2 \/ 
  exists vl, exists al, D_walk (vertexes_fdef f) (arcs_fdef f) 
    (index l2) (index (getBlockLabel be)) vl al /\
    ~ In (index l1) vl.
Proof.
  intros.
  destruct (l_dec l1 l2); subst; auto.
  right.
  assert (
   (exists p : (V_list * A_list),
      D_walk (vertexes_fdef f) (arcs_fdef f) (index l2)
        (index (getBlockLabel be)) (fst p) (snd p) /\ 
        ~ In (index l1) (fst p)) ->
   exists vl : V_list,
     exists al : A_list,
       D_walk (vertexes_fdef f) (arcs_fdef f) (index l2)
         (index (getBlockLabel be)) vl al /\ ~ In (index l1) vl
  ) as G.
    intros [[vl al] J]. eauto.
  apply G. clear G.
  apply Classical_Pred_Type.not_all_not_ex.
  intro J.
  apply Hnsdom.
  unfold strict_domination, domination.
  fill_ctxhole.
  split; auto.
    destruct be.
    intros vl al Hwalk.
    left.
    destruct (In_dec (V_eq_dec eq_atom_dec) (index l1) vl); auto.
      assert (G:=J (vl,al)). clear J.
      contradict G. auto.
Qed.

End DecDom.
