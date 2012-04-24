Require Import vellvm.
Require Import Lattice.
Require Import Maps.
Require Import ListSet.
Require Import dtree.
Require Import Sorted.

Lemma sorted_append: forall A (R:A -> A -> Prop) a (l1:list A),
  (forall a1 l1',
    l1 = l1'++a1::nil -> R a1 a) ->
  Sorted R l1 -> Sorted R (l1 ++ a :: nil).
Proof.
  induction l1; intros; simpl; auto.
    inv H0.
    constructor; auto.
      apply IHl1; auto.
        intros. subst.
        apply H with (l1'0:=a0 :: l1'); auto.
      inv H4; simpl; auto.
      constructor.
        apply H with (l1':=nil); auto.
Qed.

Lemma HdRel_insert: forall A (R:A -> A -> Prop) a a0 l2 l1
  (H : forall (a1 : A) (l1' : list A), a :: l1 = l1' ++ a1 :: nil -> R a1 a0)
  (H5 : HdRel R a (l1 ++ l2)),
  HdRel R a (l1 ++ a0 :: l2).
Proof.
  induction l1; simpl; intros.
    constructor.
      apply H with (l1':=nil); auto.
    inv H5. constructor; auto.
Qed.

Lemma sorted_insert: forall A (R:A -> A -> Prop) (l2 l1:list A) a,
  (forall a1 l1', l1 = l1'++a1::nil -> R a1 a) ->
  (forall a2 l2', l2 = a2::l2' -> R a a2) ->
  Sorted R (l1 ++ l2) -> Sorted R (l1 ++ a :: l2).
Proof.
  induction l1; simpl; intros.
    constructor; auto.
      destruct l2; constructor.
        eapply H0; eauto.

    inv H1.
    constructor.
      apply IHl1; auto.
        intros. subst.
        apply H with (l1'0:=a::l1'); eauto.
        apply HdRel_insert; auto.
Qed.

Lemma gt_dom_prop_trans : forall S M f l1 l2 l3
  (HwfF: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF1: In l1 (bound_fdef f))
  (HBinF2: In l2 (bound_fdef f))
  (HBinF3: In l3 (bound_fdef f))
  (H1 : gt_dom_prop (bound_fdef f) (dom_analyze f) l1 l2)
  (H2 : gt_dom_prop (bound_fdef f) (dom_analyze f)  l2 l3),
  gt_dom_prop (bound_fdef f) (dom_analyze f) l1 l3.
Proof.
  unfold gt_dom_prop, gt_sdom.
  intros.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R2.
  remember (Maps.AMap.get l3 (dom_analyze f)) as R3.
  destruct R2. destruct R3.
  apply In_bound_fdef__blockInFdefB in HBinF1.
  apply In_bound_fdef__blockInFdefB in HBinF2.
  apply In_bound_fdef__blockInFdefB in HBinF3.
  destruct HBinF1 as [ps1 [cs1 [tmn1 HBinF1]]].
  destruct HBinF2 as [ps2 [cs2 [tmn2 HBinF2]]].
  destruct HBinF3 as [ps3 [cs3 [tmn3 HBinF3]]].
  destruct (l_dec l1 l3); auto.
  destruct H2 as [H2 | H2]; subst; auto.
  Case "l2 in sdom(l3)".
    destruct (in_dec l_dec l2 bs_contents0); inv H2.
    left.
    assert (domination f l2 l3) as Hdom23.
      eapply dom_is_sound; eauto.
        rewrite <- HeqR3. simpl. auto.
    destruct H1 as [H1 | H1]; subst.
    SCase "l1 in sdom(l2)".
      destruct (in_dec l_dec l1 bs_contents); inv H1.
      assert (domination f l1 l2) as Hdom12.
        eapply dom_is_sound; eauto.
          rewrite <- HeqR2. simpl. auto.
      assert (strict_domination f l1 l3) as Hsdom13.
        split; auto.
          eapply dom_tran; eauto.
      eapply sdom_is_complete in Hsdom13; eauto.
        rewrite <- HeqR3 in Hsdom13. simpl in *.
        destruct (in_dec l_dec l1 bs_contents0); auto.

        rewrite <- HeqR3. simpl.
        destruct bs_contents0; auto.
          intro J. inv J.

    SCase "l1=l2".
      assert (strict_domination f l2 l3) as Hsdom23.
        split; auto.
      eapply sdom_is_complete in Hsdom23; eauto.
        destruct (in_dec l_dec l2 bs_contents0); auto.

        rewrite <- HeqR3. simpl.
        destruct bs_contents0; auto.
          intro J. inv J.

  Case "l2=l3".
    rewrite <- HeqR3 in HeqR2. inv HeqR2; auto.
Qed.

Lemma gt_sdom_prop_trans : forall S M f l1 l2 l3
  (HwfF: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF1: In l1 (bound_fdef f))
  (HBinF2: In l2 (bound_fdef f))
  (HBinF3: In l3 (bound_fdef f))
  (H1 : gt_sdom (bound_fdef f) (dom_analyze f) l1 l2 = true)
  (H2 : gt_sdom (bound_fdef f) (dom_analyze f)  l2 l3 = true),
  gt_sdom (bound_fdef f) (dom_analyze f)  l1 l3 = true.
Proof.
  unfold gt_sdom.
  intros.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R1.
  remember (Maps.AMap.get l3 (dom_analyze f)) as R2.
  destruct R1. destruct R2.
  destruct (in_dec l_dec l2 bs_contents0); inv H2.
  destruct (in_dec l_dec l1 bs_contents); inv H1.
  apply In_bound_fdef__blockInFdefB in HBinF1.
  apply In_bound_fdef__blockInFdefB in HBinF2.
  apply In_bound_fdef__blockInFdefB in HBinF3.
  destruct HBinF1 as [ps1 [cs1 [tmn1 HBinF1]]].
  destruct HBinF2 as [ps2 [cs2 [tmn2 HBinF2]]].
  destruct HBinF3 as [ps3 [cs3 [tmn3 HBinF3]]].
  destruct (reachable_dec f l3).
    assert (strict_domination f l2 l3) as Hsdom23.
      eapply sdom_is_sound; eauto.
        rewrite <- HeqR2. simpl. auto.
    assert (reachable f l2) as Hreach2.
      apply sdom_reachable in Hsdom23; auto.
    assert (strict_domination f l1 l2) as Hsdom12.
      eapply sdom_is_sound; eauto.
        rewrite <- HeqR1. simpl. auto.
    assert (strict_domination f l1 l3) as Hsdom13.
      eapply sdom_tran with (l2:=l2); eauto.
    eapply sdom_is_complete in Hsdom13; eauto.
      rewrite <- HeqR2 in Hsdom13. simpl in *.
      destruct (in_dec l_dec l1 bs_contents0); auto.

      rewrite <- HeqR2. simpl.
      destruct bs_contents0; auto.
        intro J. inv J.

    eapply dom_unreachable in H; eauto.
      rewrite <- HeqR2 in H. simpl in H.
      destruct H.
      apply blockInFdefB_in_vertexes in HBinF1.
      unfold vertexes_fdef in HBinF1.
      apply H0 in HBinF1.
      destruct (in_dec l_dec l1 bs_contents0); auto.

      rewrite <- HeqR2. simpl. intro J. subst. inv i0.
Qed.

(*
Lemma sdom_ordered : forall f l1 l2 l3
  (Hneq: l1 <> l2) (Hreach: reachable f l3)
  (Hsdom: strict_domination f l1 l3)
  (Hsdom': strict_domination f l2 l3),
  strict_domination f l1 l2 \/ strict_domination f l2 l1.

Lemma sdom_is_sound : forall
  ifs S M (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef ifs S M f) (HuniqF : uniqFdef f) (Hreach : reachable f l3)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin :
    In l' (DomDS.L.bs_contents _ ((dom_analyze f) !! l3))),
  strict_domination f l' l3.
Proof.
Lemma sdom_is_complete: forall
  ifs S M (f : fdef) (l3 : l) (l' : l) ps cs tmn ps' cs' tmn'
  (HwfF : wf_fdef ifs S M f) (HuniqF : uniqFdef f)
  (HBinF' : blockInFdefB (block_intro l' ps' cs' tmn') f = true)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hsdom: strict_domination f l' l3)
  (Hnempty: DomDS.L.bs_contents _ ((dom_analyze f) !! l3) <> nil),
  In l' (DomDS.L.bs_contents _ ((dom_analyze f) !! l3)).
Proof.

*)

Lemma gt_dom_dec_aux: forall S M f (HwfF: wf_fdef S M f) 
  (Huniq: uniqFdef f) l1 l2 l3
  (Hreach: reachable f l3)
  (HBinF1: In l1 (bound_fdef f))
  (HBinF2: In l2 (bound_fdef f))
  (HBinF3: In l3 (bound_fdef f)),
  gt_sdom (bound_fdef f) (dom_analyze f) l1 l3 ->
  gt_sdom (bound_fdef f) (dom_analyze f) l2 l3 ->
  gt_dom_prop (bound_fdef f) (dom_analyze f) l1 l2 \/
  gt_dom_prop (bound_fdef f) (dom_analyze f) l2 l1.
Proof.
  unfold gt_dom_prop, gt_sdom. intros.
  destruct (l_dec l1 l2); auto.
  remember ((dom_analyze f) !! l3 ) as R3.
  remember ((dom_analyze f) !! l2 ) as R2.
  remember ((dom_analyze f) !! l1 ) as R1.
  destruct R1, R2, R3.
  destruct (in_dec l_dec l1 bs_contents1); inv H.
  destruct (in_dec l_dec l2 bs_contents1); inv H0.
  apply In_bound_fdef__blockInFdefB in HBinF1.
  apply In_bound_fdef__blockInFdefB in HBinF2.
  apply In_bound_fdef__blockInFdefB in HBinF3.
  destruct HBinF1 as [ps1 [cs1 [tmn1 HBinF1]]].
  destruct HBinF2 as [ps2 [cs2 [tmn2 HBinF2]]].
  destruct HBinF3 as [ps3 [cs3 [tmn3 HBinF3]]].
  assert (strict_domination f l1 l3) as Hsdom13.
    eapply sdom_is_sound; eauto.
      rewrite <- HeqR3. simpl. auto.
  assert (strict_domination f l2 l3) as Hsdom23.
    eapply sdom_is_sound; eauto.
      rewrite <- HeqR3. simpl. auto.
  assert (exists entry, getEntryLabel f = Some entry) as Hentry.
    inv HwfF.
    match goal with
    | H1: getEntryBlock _ = Some _ |- _ => 
      clear - H1; simpl in *;
      destruct blocks5; inv H1; destruct block5; eauto
    end.
  destruct Hentry as [entry Hentry].
  assert (reachable f l2) as Hreach2.
    apply sdom_reachable in Hsdom23; auto.
  assert (reachable f l1) as Hreach1.
    apply sdom_reachable in Hsdom13; auto.
  destruct (l_dec l1 entry); subst.
    left. left.
    assert (
      match (AMap.get l2 (dom_analyze f)) with
      | Dominators.mkBoundedSet dts _ => In entry dts
      end) as G.
      eapply dom_analysis__entry_doms_others; eauto.
        rewrite <- HeqR2 in G.
        destruct (in_dec l_dec entry bs_contents0); auto.
  destruct (l_dec l2 entry); subst.
    right. left.
    assert (
      match (AMap.get l1 (dom_analyze f)) with
      | Dominators.mkBoundedSet dts _ => In entry dts
      end) as G.
      eapply dom_analysis__entry_doms_others; eauto.
        rewrite <- HeqR1 in G.
        destruct (in_dec l_dec entry bs_contents); auto.
  eapply sdom_ordered with (l1:=l2) in Hsdom13; eauto.
  destruct Hsdom13 as [Hsdom21 | Hsdom12].
    right.
    eapply sdom_is_complete in Hsdom21; eauto.
      rewrite <- HeqR1 in Hsdom21. simpl in Hsdom21.
      destruct (in_dec l_dec l2 bs_contents); simpl; auto.

      rewrite <- HeqR1. simpl.
      assert (
        match (AMap.get l1 (dom_analyze f)) with
        | Dominators.mkBoundedSet dts _ => In entry dts
        end) as G.
        eapply dom_analysis__entry_doms_others; eauto.
          rewrite <- HeqR1 in G. intro J. subst. inv G.

    left.
    eapply sdom_is_complete in Hsdom12; eauto.
      rewrite <- HeqR2 in Hsdom12. simpl in Hsdom12.
      destruct (in_dec l_dec l1 bs_contents0); simpl; auto.

      rewrite <- HeqR2. simpl.
      assert (
        match (AMap.get l2 (dom_analyze f)) with
        | Dominators.mkBoundedSet dts _ => In entry dts
        end) as G.
        eapply dom_analysis__entry_doms_others; eauto.
          rewrite <- HeqR2 in G. intro J. subst. inv G.
Qed.

Lemma gt_dom_dec: forall S M f (HwfF: wf_fdef S M f) 
  (Huniq: uniqFdef f) l1 l2 l3
  (Hreach: reachable f l3)
  (HBinF1: In l1 (bound_fdef f))
  (HBinF2: In l2 (bound_fdef f))
  (HBinF3: In l3 (bound_fdef f)),
  gt_dom_prop (bound_fdef f) (dom_analyze f) l1 l3 ->
  gt_dom_prop (bound_fdef f) (dom_analyze f) l2 l3 ->
  gt_dom_prop (bound_fdef f) (dom_analyze f) l1 l2 \/
  gt_dom_prop (bound_fdef f) (dom_analyze f) l2 l1.
Proof.
  intros.
  destruct H as [H | H]; subst; auto.
  destruct H0 as [H0 | H0]; subst.
    eapply gt_dom_dec_aux; eauto.
    left. left. auto.
Qed.

Lemma gt_sdom_dec: forall S M f (HwfF: wf_fdef S M f) 
  (Huniq: uniqFdef f) l1 l2 l3
  (Hneq: l1 <> l2)
  (Hreach: reachable f l3)
  (HBinF1: In l1 (bound_fdef f))
  (HBinF2: In l2 (bound_fdef f))
  (HBinF3: In l3 (bound_fdef f)),
  gt_sdom (bound_fdef f) (dom_analyze f) l1 l3 ->
  gt_sdom (bound_fdef f) (dom_analyze f) l2 l3 ->
  gt_sdom (bound_fdef f) (dom_analyze f) l1 l2 \/
  gt_sdom (bound_fdef f) (dom_analyze f) l2 l1.
Proof.
  intros.
  apply gt_dom_dec with (l1:=l1) (l2:=l2) (l3:=l3) in HwfF; auto.
    destruct HwfF as [[J | J] | [J | J]]; subst; auto; try congruence.
    left. auto.
    left. auto.
Qed.

Lemma insert_sort_sdom_iter_safe: forall bd res l0 suffix l1 prefix,
  (In l0 (prefix ++ suffix) \/ l0 = l1) <->
  In l0 (insert_sort_sdom_iter bd res l1 prefix suffix).
Proof.
  induction suffix; simpl; intros.
    split; intro J.
      apply in_or_app.
      destruct J as [J | J]; subst.
        left. simpl_env in J. apply in_rev in J; auto.
        right. simpl. auto.

      apply in_app_or in J. simpl in J. simpl_env.
      destruct J as [J | [J | J]]; subst; auto.
        left. apply in_rev in J; auto.
        tauto.

    simpl_env. simpl.
    split; intro J.
      destruct (gt_sdom bd res l1 a).
        destruct J as [J | J]; subst.
          apply in_app_or in J. simpl in J.
          apply in_or_app. simpl.
          destruct J as [J | [J | J]]; subst; auto.
            apply in_rev in J; auto.

          apply in_or_app. simpl. auto.
        apply IHsuffix.
          destruct J as [J | J]; auto.
          left. simpl.
          apply in_app_or in J. simpl in J.
          destruct J as [J | [J | J]]; subst; auto.
            right. apply in_or_app; auto.
            right. apply in_or_app; auto.

      destruct (gt_sdom bd res l1 a).
        apply in_app_or in J. simpl in J.
        destruct J as [J | [J | [J | J]]]; subst; auto.
          left. apply in_or_app. simpl.
          apply in_rev in J; auto.

          left. apply in_or_app. simpl. auto.
          left. apply in_or_app. simpl. auto.
        apply IHsuffix in J.
          destruct J as [J | J]; auto.
          left. apply in_or_app. simpl.
          apply in_app_or in J. simpl in J.
          destruct J as [[J | J] | J]; subst; auto.
Qed.

Lemma insert_sort_sdom_safe: forall bd res data acc l0,
  (In l0 acc \/ In l0 data) <-> In l0 (insert_sort_sdom bd res data acc).
Proof.
  induction data; simpl; intros; auto.
    split; tauto.

    split; intro.
      apply IHdata.
      destruct H as [H | [H | H]]; subst; auto.
        left.
        apply insert_sort_sdom_iter_safe; auto.

        left.
        apply insert_sort_sdom_iter_safe; auto.

      apply IHdata in H.
      destruct H as [H | H]; auto.
      apply insert_sort_sdom_iter_safe in H.
      destruct H; auto.
Qed.

Lemma sort_sdom_safe: forall bd res input l0,
  In l0 (sort_sdom bd res input) <-> In l0 input.
Proof.
  intros.
  unfold sort_sdom.
  destruct (@insert_sort_sdom_safe bd res input nil l0) as [J1 J2].
  split; intro; auto.
    apply J2 in H. destruct H as [H | H]; auto. inv H.
Qed.

Lemma insert_sort_sdom_iter_sorted: forall S M f (HwfF: wf_fdef S M f) 
  (Huniq: uniqFdef f) l3 (Hin3: In l3 (bound_fdef f)) (Hreach: reachable f l3)
  l0 (Hin0: In l0 (bound_fdef f))
  (Hsd03: gt_dom_prop (bound_fdef f) (dom_analyze f) l0 l3) suffix prefix
  (G: forall l', In l' (prefix ++ suffix) ->
      gt_dom_prop (bound_fdef f) (dom_analyze f) l' l3 /\ In l' (bound_fdef f)),
  Sorted (gt_dom_prop (bound_fdef f) (dom_analyze f))
    (List.rev prefix ++ suffix) ->
  (forall l1 prefix', prefix = l1 :: prefix' ->
      gt_dom_prop (bound_fdef f) (dom_analyze f) l1 l0) ->
  Sorted (gt_dom_prop (bound_fdef f) (dom_analyze f))
    (insert_sort_sdom_iter (bound_fdef f) (dom_analyze f) l0 prefix suffix).
Proof.
  induction suffix; simpl; intros.
    simpl_env in *.
    apply sorted_append; auto.
      intros.
      apply H0 with (prefix':=rev l1'); auto.
        rewrite <- rev_involutive at 1.
        rewrite H1. rewrite rev_unit. auto.

    remember (gt_sdom (bound_fdef f) (dom_analyze f) l0 a) as R.
    destruct R.
      simpl_env. simpl.
      apply sorted_insert; auto.
        intros.
        apply H0 with (prefix':=rev l1'); auto.
          rewrite <- rev_involutive at 1.
          rewrite H1. rewrite rev_unit. auto.

        intros.
        inv H1.
        unfold gt_dom_prop. auto.

      apply IHsuffix.
        intros. apply G.
        apply in_or_app. simpl.
        apply in_app_or in H1. simpl in H1.
        destruct H1 as [[H1 | H1] | H1]; auto.

        simpl. simpl_env. simpl. auto.

        intros. inv H1.
        assert (gt_dom_prop (bound_fdef f) (dom_analyze f) l1 l0 \/
                gt_dom_prop (bound_fdef f) (dom_analyze f) l0 l1) as J.
          assert (In l1 (prefix'++l1::suffix)) as Hin1. apply in_middle.
          apply G in Hin1. destruct Hin1 as [J1 J2].
          eapply gt_dom_dec; eauto.
        destruct J; auto.
        unfold gt_dom_prop in H1. unfold gt_dom_prop.
        destruct (l_dec l0 l1); auto.
        destruct H1 as [H1 | H1]; auto.
        rewrite <- HeqR in H1. congruence.
Qed.

Lemma insert_sort_sdom_sorted: forall S M f (HwfF: wf_fdef S M f) 
  (Huniq: uniqFdef f) l3 (Hin3: In l3 (bound_fdef f)) (Hreach: reachable f l3)
  data acc
  (G: forall l', In l' (data++acc) ->
      gt_dom_prop (bound_fdef f) (dom_analyze f) l' l3 /\ In l' (bound_fdef f)),
  Sorted (gt_dom_prop (bound_fdef f) (dom_analyze f)) acc ->
  Sorted (gt_dom_prop (bound_fdef f) (dom_analyze f))
         (insert_sort_sdom (bound_fdef f) (dom_analyze f) data acc).
Proof.
  induction data; simpl; intros; auto.
    apply IHdata.
      intros. apply G.
      apply in_app_or in H0.
      destruct H0 as [H0 | H0].
        right. apply in_or_app; auto.
        apply insert_sort_sdom_iter_safe in H0.
        destruct H0 as [H0 | H0]; auto.
          right. apply in_or_app. simpl_env in H0. auto.

      assert (a = a \/ In a (data++acc)) as Hin. auto.
      apply G in Hin. destruct Hin as [J1 J2].
      eapply insert_sort_sdom_iter_sorted with (l3:=l3); eauto.
        intros. apply G. right. apply in_or_app. simpl_env in H0. auto.

        intros. inv H0.
Qed.

Lemma sort_sdom_sorted: forall S M f (HwfF: wf_fdef S M f) 
  (Huniq: uniqFdef f) l3 (Hin3: In l3 (bound_fdef f)) (Hreach: reachable f l3)
  input
  (G: forall l', In l' input ->
      gt_dom_prop (bound_fdef f) (dom_analyze f) l' l3 /\ In l' (bound_fdef f)),
  Sorted (gt_dom_prop (bound_fdef f) (dom_analyze f))
         (sort_sdom (bound_fdef f) (dom_analyze f) input).
Proof.
  intros. unfold sort_sdom.
  eapply insert_sort_sdom_sorted; simpl_env; eauto.
Qed.

Lemma remove_redundant_safe: forall l0 input,
  In l0 (remove_redundant input) <-> In l0 input.
Proof.
  induction input; simpl.
    split; auto.

    destruct input.
      simpl. split; auto.

      destruct IHinput as [J1 J2].
      destruct (l_dec a l1); subst.
        split; intros.
          apply J1 in H.
            simpl in H. simpl.
            destruct H; auto.

          apply J2.
            simpl in H. simpl.
            destruct H as [H | [H | H]]; auto.

        split; intros.
          Local Opaque remove_redundant.
          simpl in H.
          destruct H as [H | H]; auto.

          simpl.
          destruct H as [H | H]; auto.
          Transparent remove_redundant.
Qed.

Lemma remove_redundant_HdRel: forall R a input,
  HdRel R a input ->
  HdRel R a (remove_redundant input).
Proof.
  induction input; simpl; intros; auto.
    destruct input; auto.
      inv H.
      destruct (l_dec a0 l0); subst.
        apply IHinput. apply HdRel_cons; auto.
        apply HdRel_cons; auto.
Qed.

Lemma remove_redundant_In: forall a input,
  In a (remove_redundant input) -> In a input.
Proof.
  induction input; simpl; intros; auto.
    destruct input; auto.
      destruct (l_dec a0 l0); subst.
        apply IHinput in H; auto.

        Local Opaque remove_redundant.
        simpl in H.
        destruct H as [H | H]; auto.
        Transparent remove_redundant.
Qed.

Lemma remove_redundant_sorted: forall R input,
  Sorted R input -> Sorted R (remove_redundant input).
Proof.
  induction input; intros; simpl; auto.
    destruct input; auto.
      inv H.
      apply IHinput in H2.
      destruct (l_dec a l0); subst; auto.
        apply Sorted_cons; auto.
          apply remove_redundant_HdRel; auto.
Qed.

Lemma remove_redundant_NoDup: forall (R:l -> l -> Prop) input
  (P0:forall a b c,
        In a input ->
        In b input ->
        In c input -> a <> b -> R a b -> R b c -> a <> c),
  StronglySorted R input ->
  NoDup (remove_redundant input).
Proof.
  induction input; intros; simpl; auto.
    destruct input; auto.
      inv H.
      assert (H2':=H2).
      apply IHinput in H2.
        destruct (l_dec a l0); subst; auto.
          apply NoDup_cons; auto.
          intro J.
          apply remove_redundant_In in J.
          simpl in J.
          destruct J as [J | J]; subst.
            congruence.

            eapply Forall_forall with (x:=l0) in H3; simpl; eauto.
            inv H2'.
            eapply Forall_forall with (x:=a) in H4; eauto.
            apply P0 with (c:=a) in H3; simpl; auto.

        intros. apply P0 with (b:=b); simpl; auto.
Qed.

Lemma remove_redundant_NoDup': forall R input
  (P0:forall a, In a input -> ~ R a a),
  StronglySorted R input ->
  NoDup (remove_redundant input).
Proof.
  induction input; intros; simpl; auto.
    destruct input; auto.
      inv H.
      apply IHinput in H2.
        destruct (l_dec a l0); subst; auto.
          apply NoDup_cons; auto.
          intro J.
          apply remove_redundant_In in J.
          eapply Forall_forall in H3; eauto.
          revert H3. apply P0. simpl. auto.
        intros. apply P0. simpl. simpl in H.
        destruct H; auto.
Qed.

Lemma gt_sdom_prop_irrefl: forall S M f (HwfF : wf_fdef S M f) 
  (HuniqF: uniqFdef f) a (Hreach : reachable f a),
  gt_sdom (bound_fdef f) (dom_analyze f) a a = false.
Proof.
  unfold gt_sdom.
  intros.
  remember ((dom_analyze f) !! a) as R.
  destruct R.
  assert (J:=Hreach).
  apply reachable__in_bound in Hreach.
  apply In_bound_fdef__blockInFdefB in Hreach.
  destruct Hreach as [ps [cs [tnn HBinF]]].
  destruct (in_dec l_dec a bs_contents); simpl; auto.
  eapply sdom_is_sound with (l':=a) in HBinF; eauto.
    destruct HBinF. congruence.
    rewrite <- HeqR. auto.
Qed.

Lemma Sorted_HdRel__Forall: forall A (R : A -> A -> Prop) l0 (H0 : Sorted R l0),
  forall a : A,
  (forall x y z : A,
   In x (a :: l0) ->
   In y (a :: l0) -> In z (a :: l0) -> R x y -> R y z -> R x z) ->
  HdRel R a l0 -> Forall (R a) l0.
Proof.
  induction l0; simpl; intros.
    apply Forall_forall.
    intros. inv H2.

    apply Forall_forall.
    intros.
    simpl in H2.
    inv H1.
    destruct H2 as [H2 | H2]; subst; auto.
    inv H0.
    apply IHl0 in H6; auto.
      eapply Forall_forall in H6; eauto.
      apply H with (y:=a); auto.

      intros.
      eapply H with (y:=y); simpl; eauto.
Qed.

Lemma strict_Sorted_StronglySorted : forall A (R:A -> A -> Prop) data,
  (forall x y z,
     In x data -> In y data -> In z data ->
     R x y -> R y z -> R x z) ->
  Sorted R data -> StronglySorted R data.
Proof.
  intros.
  induction H0; constructor.
    apply IHSorted.
      intros. eapply H with (y:=y); simpl; eauto.
      apply Sorted_HdRel__Forall in H; auto.
Qed.

Lemma compute_sdom_chains_aux__dom : forall bd res l0 chain0 rd acc,
  In (l0, chain0) (compute_sdom_chains_aux bd res rd acc) ->
  In l0 rd \/ In (l0, chain0) acc.
Proof.
  induction rd; simpl; intros; auto.
    destruct (res !! a).
    apply IHrd in H.
    destruct H as [H | H]; auto.
    simpl in H.
    destruct H as [H | H]; auto.
    inv H; auto.
Qed.

Lemma compute_sdom_chains__dom : forall bd res rd l0 chain0,
  In (l0, chain0) (compute_sdom_chains bd res rd) -> In l0 rd.
Proof.
  unfold compute_sdom_chains.
  intros.
  apply compute_sdom_chains_aux__dom in H.
  destruct H as [H | H]; auto.
  inv H.
Qed.

Lemma compute_sdom_chains_aux_sorted__helper: forall bd0 bd bs_contents res x
  (bs_bound : incl bs_contents bd0) (l1 : l) (Hinc : incl (l1 :: bd) bd0)
  (H1 : In x (sort_sdom bd0 res (l1 :: bs_contents))),
  In x bd0.
Proof.
  intros.
  apply sort_sdom_safe in H1.
  simpl in H1.
  destruct H1 as [H1 | H1]; subst.
    apply Hinc. simpl; auto.
    apply bs_bound. auto.
Qed.

Lemma gt_sdom_prop_trans1 : forall S M f l1 l2 l3
  (HwfF: wf_fdef S M f) (Huniq: uniqFdef f) (Hreach: reachable f l3)
  (HBinF1: In l1 (bound_fdef f))
  (HBinF2: In l2 (bound_fdef f))
  (HBinF3: In l3 (bound_fdef f))
  (H1 : gt_sdom (bound_fdef f) (dom_analyze f) l1 l2 = true)
  (H2 : gt_dom_prop (bound_fdef f) (dom_analyze f) l2 l3),
  gt_sdom (bound_fdef f) (dom_analyze f) l1 l3 = true.
Proof.
  unfold gt_dom_prop, gt_sdom.
  intros.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R2.
  remember (Maps.AMap.get l3 (dom_analyze f)) as R3.
  destruct R2. destruct R3.
  destruct (in_dec l_dec l1 bs_contents); inv H1.
  apply In_bound_fdef__blockInFdefB in HBinF1.
  apply In_bound_fdef__blockInFdefB in HBinF2.
  apply In_bound_fdef__blockInFdefB in HBinF3.
  destruct HBinF1 as [ps1 [cs1 [tmn1 HBinF1]]].
  destruct HBinF2 as [ps2 [cs2 [tmn2 HBinF2]]].
  destruct HBinF3 as [ps3 [cs3 [tmn3 HBinF3]]].
  assert (domination f l2 l3) as Hdom23.
    eapply dom_is_sound; eauto.
      rewrite <- HeqR3. simpl.
      destruct H2 as  [H2 | H2]; auto.
        destruct (in_dec l_dec l2 bs_contents0); inv H2; auto.
  assert (reachable f l2) as Hreach2.
     apply dom_reachable in Hdom23; auto.
  assert (strict_domination f l1 l2) as Hsdom12.
    eapply sdom_is_sound; eauto.
      rewrite <- HeqR2. simpl. auto.
  eapply sdom_tran1 with (l3:=l3) in Hsdom12; eauto.
  eapply sdom_is_complete in Hsdom12; eauto.
    rewrite <- HeqR3 in Hsdom12. simpl in Hsdom12.
    destruct (in_dec l_dec l1 bs_contents0); auto.

    rewrite <- HeqR3. simpl.
    destruct H2 as [H2 | H2]; subst.
      destruct bs_contents0.
        inv H2.
        intro J. inv J.

      rewrite <- HeqR3 in HeqR2. inv HeqR2.
      destruct bs_contents0.
        inv i0.
        intro J. inv J.
Qed.

Lemma compute_sdom_chains_aux_sorted: forall S M f 
  (HwfF: wf_fdef S M f) (Huniq: uniqFdef f)
  l0 chain0 bd (Hinc: incl bd (bound_fdef f))
  (Hreach: forall x, In x bd -> reachable f x) acc,
  (forall l0 chain0, In (l0, chain0) acc ->
    Sorted (gt_dom_prop (bound_fdef f) (dom_analyze f)) chain0 /\
    NoDup chain0) ->
  In (l0, chain0)
    (compute_sdom_chains_aux (bound_fdef f) (dom_analyze f) bd acc) ->
  Sorted (gt_dom_prop (bound_fdef f) (dom_analyze f)) chain0 /\ NoDup chain0.
Proof.
  induction bd; simpl; intros; eauto.
    remember ((dom_analyze f) !! a) as R.
    destruct R.
    apply IHbd in H0; auto.
      simpl_env in Hinc.
      apply AtomSet.incl_app_invr in Hinc; auto.

      intros.
      destruct H1 as [H1 | H1]; eauto.
      inv H1.
      assert (In l1 (bound_fdef f)) as G1.
        apply Hinc; simpl; auto.
      assert (forall l' : l,
        In l' (l1 :: bs_contents) ->
        gt_dom_prop (bound_fdef f) (dom_analyze f) l' l1 /\ In l' (bound_fdef f))
        as G2.
        intros l' Hin.
        simpl in Hin.
        destruct Hin as [EQ | Hin]; subst.
          unfold gt_dom_prop. split; auto.

          split.
            unfold gt_dom_prop, gt_sdom.
            rewrite <- HeqR.
            destruct (in_dec l_dec l' bs_contents); simpl; auto.

            apply bs_bound; auto.
      split.
        apply remove_redundant_sorted; auto.
          eapply sort_sdom_sorted; eauto.

        apply remove_redundant_NoDup with
          (R:=gt_dom_prop (bound_fdef f) (dom_analyze f)); auto.
          intros.
          destruct H5; subst; try congruence.
          assert (reachable f c) as Hreachc.
            apply sort_sdom_safe in H3.
              simpl in H3.
              destruct H3 as [H3 | H3]; subst.
                apply Hreach; auto.

                assert (reachable f l1) as Hreach1. apply Hreach; auto.
                eapply sdom_reachable; eauto.
                  assert (In l1 (bound_fdef f)) as Hin.
                    apply Hinc; simpl; auto.
                  apply In_bound_fdef__blockInFdefB in Hin.
                  destruct Hin as [ps [cs [tmn HBinF]]].
                  eapply sdom_is_sound; eauto.
                    rewrite <- HeqR. auto.
          eapply gt_sdom_prop_trans1 with (l1:=a) in H6;
            eauto using compute_sdom_chains_aux_sorted__helper.
            intro EQ; subst.
            apply gt_sdom_prop_irrefl with (a:=c) in HwfF; auto.
            rewrite HwfF in H6. congruence.

          apply strict_Sorted_StronglySorted.
            intros.
            eapply gt_dom_prop_trans with (l2:=y);
              eauto using compute_sdom_chains_aux_sorted__helper.
            eapply sort_sdom_sorted; eauto.
Qed.

Lemma NoDup_gt_dom_prop_sorted__gt_dsom_prop_sorted: forall f chain
  (Hsorted: Sorted (gt_dom_prop (bound_fdef f) (dom_analyze f)) chain)
  (Huniq: NoDup chain),
  Sorted (gt_sdom_prop (bound_fdef f) (dom_analyze f)) chain.
Proof.
  intros.
  induction Hsorted; simpl; intros; auto.
    inv Huniq.
    constructor; auto.
      inv H; auto.
      constructor.
        destruct H0; subst; auto.
          contradict H2; simpl; auto.
Qed.

Lemma compute_sdom_chains_sorted: forall S M f 
  (HwfF: wf_fdef S M f) (Huniq: uniqFdef f)
  rd (Hinc: incl rd (bound_fdef f)) (Hreach: forall x, In x rd -> reachable f x)
  l0 chain,
  In (l0, chain) (compute_sdom_chains (bound_fdef f) (dom_analyze f) rd) ->
  Sorted (gt_sdom_prop (bound_fdef f) (dom_analyze f)) chain /\ NoDup chain.
Proof.
  intros.
  unfold compute_sdom_chains in H.
  eapply compute_sdom_chains_aux_sorted in H; eauto.
    destruct H as [H1 H2].
    split; auto.
      apply NoDup_gt_dom_prop_sorted__gt_dsom_prop_sorted; auto.

    simpl. intros. tauto.
Qed.

Lemma compute_sdom_chains_aux_safe: forall bd0 (res:AMap.t (Dominators.t bd0))
  l0 l1 chain0 dts0 P0 bd acc,
  (forall l0 l1 chain0 dts0 P0,
    In (l0, chain0) acc ->
    AMap.get l0 res = Dominators.mkBoundedSet _ dts0 P0 ->
    (In l1 chain0 <-> In l1 (l0 :: dts0))) ->
  In (l0, chain0) (compute_sdom_chains_aux bd0 res bd acc) ->
  AMap.get l0 res = Dominators.mkBoundedSet _ dts0 P0 ->
  (In l1 chain0 <-> In l1 (l0 :: dts0)).
Proof.
  induction bd; intros; eauto.
    simpl in H0.
    remember (@AMap.get (Dominators.t bd0) a res) as R.
    destruct R.
    apply IHbd in H0; auto.
    intros. simpl in H2.
    destruct H2 as [H2 | H2]; eauto.
    inv H2. rewrite H3 in HeqR. inv HeqR.
    destruct (@remove_redundant_safe l3 (sort_sdom bd0 res (l2 :: dts1)))
      as [J1 J2].
    destruct (@sort_sdom_safe bd0 res (l2 :: dts1) l3) as [J3 J4].
    split; eauto.
Qed.

Lemma compute_sdom_chains_safe: forall bd res rd l0 chain l1 dts0 P0,
  In (l0, chain) (compute_sdom_chains bd res rd) ->
  AMap.get l0 res = Dominators.mkBoundedSet _ dts0 P0 ->
  (In l1 chain <-> In l1 (l0 :: dts0)).
Proof.
  intros.
  unfold compute_sdom_chains in H.
  eapply compute_sdom_chains_aux_safe in H; eauto.
  simpl. intros. tauto.
Qed.

Lemma compute_sdom_chains__in_bound: forall l0 chain0 bd res rd
  (Hinc: incl rd bd),
  In (l0, chain0) (compute_sdom_chains bd res rd) ->
  incl chain0 bd.
Proof.
  intros.
  remember (AMap.get l0 res) as R. destruct R.
  intros x Hin.
  assert (H':=H).
  eapply compute_sdom_chains_safe in H; eauto.
  eapply H in Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; subst; auto.
  apply compute_sdom_chains__dom in H'; auto.
Qed.

Lemma gt_sdom_prop_entry: forall f l1 entry
  (H: getEntryLabel f = ret entry)
  (H4: gt_sdom_prop (bound_fdef f) (dom_analyze f) l1 entry),
  False.
Proof.
  intros.
  unfold gt_sdom_prop, gt_sdom in H4.
  remember ((dom_analyze f) !! entry) as R.
  destruct R.
  assert (exists ps, exists cs, exists tmn,
    getEntryBlock f = Some (block_intro entry ps cs tmn)) as Hentry.
    destruct f as [fh bs]. destruct bs; tinv H.
    destruct b; inv H; simpl; eauto.
  destruct Hentry as [ps [cs [tmn Hentry]]].
  apply dom_entrypoint in Hentry.
  rewrite <- HeqR in Hentry. simpl in Hentry. subst.
  inv H4.
Qed.

Lemma entry_in_compute_sdom_chains: forall entry l0 chain0 bd res rd
  (H:forall b, b <> entry /\ In b rd ->
     match (AMap.get b res) with
     | Dominators.mkBoundedSet dts _ => dts <> nil -> In entry dts
     end)
  (H0:In (l0, chain0) (compute_sdom_chains bd res rd))
  (Huniq:NoDup chain0)
  (G:(length chain0 > 1)%nat),
  In entry chain0.
Proof.
  intros.
  assert (H0':=H0).
  apply compute_sdom_chains__dom in H0'.
  remember (AMap.get l0 res) as R.
  destruct R.
  assert (H1':=H0).
  eapply compute_sdom_chains_safe with (l1:=entry) in H0; eauto.
  apply H0.
  simpl.
  destruct (l_dec l0 entry); subst; auto.
    assert (l0 <> entry /\ In l0 rd) as J.
      auto.
    apply H in J. rewrite <- HeqR in J.
    right.
    apply J.
    destruct bs_contents.
      destruct chain0; tinv G.
      destruct chain0; try solve [contradict G; simpl; clear; omega].
      assert (H2':=H1').
      eapply compute_sdom_chains_safe with (l1:=l1) in H1'; eauto.
      eapply compute_sdom_chains_safe with (l1:=l2) in H2'; eauto.
      assert (In l1 (l1 :: l2 :: chain0)) as Hin1. simpl. auto.
      assert (In l2 (l1 :: l2 :: chain0)) as Hin2. simpl. auto.
      apply H1' in Hin1.
      apply H2' in Hin2.
      simpl in Hin1, Hin2.
      destruct Hin1; subst; try tauto.
      destruct Hin2; subst; try tauto.
      inv Huniq. contradict H3; simpl; auto.

      congruence.
Qed.

Lemma entry_is_head_of_compute_sdom_chains: forall S M f 
  (HwfF: wf_fdef S M f) (Huniq: uniqFdef f) entry rd l0 chain0
  (H:getEntryLabel f = Some entry)
  (H0:reachablity_analysis f = Some rd)
  (H1:In (l0, chain0)
    (compute_sdom_chains (bound_fdef f) (dom_analyze f) rd))
  (G:(length chain0 > 1)%nat),
  exists chain0', chain0 = entry :: chain0'.
Proof.
  intros.
  assert (forall b,
    b <> entry /\ In b rd ->
    match (AMap.get b (dom_analyze f)) with
    | Dominators.mkBoundedSet dts _ => dts <> nil -> In entry dts
    end) as J.
    intros b Hp.
    destruct Hp as [Hp1 Hp2].
    eapply reachablity_analysis__reachable in Hp2; eauto.
    eapply dom_analysis__entry_doms_others in H; eauto.
    destruct ((dom_analyze f) !! b); auto.
      
  assert (J0:=H0).
  apply reachablity_analysis__in_bound in H0.
  assert (forall x : atom, In x rd -> reachable f x) as W.
    intros. eapply reachablity_analysis__reachable; eauto.
  assert (J1:=H1).
  eapply compute_sdom_chains_sorted in J1; eauto.
  destruct J1 as [J1 J2].
  assert (H1':=H1).
  apply entry_in_compute_sdom_chains with (entry:=entry) in H1'; auto.
  apply compute_sdom_chains__in_bound in H1; auto.
  destruct chain0.
    inv H1'.

    simpl in H1'.
    destruct (l_dec l1 entry); subst; eauto.
    destruct H1' as [Heq | H1']; subst.
      congruence.

      apply strict_Sorted_StronglySorted in J1; auto.
        inv J1.
        inv J2.
        eapply Forall_forall in H5; eauto.
        apply gt_sdom_prop_entry in H5; tauto.

        intros.
        eapply gt_sdom_prop_trans with (l2:=y); eauto.
Qed.

Lemma compute_sdom_chains__wf_chain: forall S M f 
  (HwfF: wf_fdef S M f) (Huniq: uniqFdef f) l0 chain0 entry rd,
  getEntryLabel f = Some entry ->
  reachablity_analysis f =  Some rd ->
  In (l0, chain0) (compute_sdom_chains (bound_fdef f) (dom_analyze f) rd) ->
  wf_chain f (DT_node entry DT_nil) chain0.
Proof.
  intros.
  destruct chain0; simpl; auto.
  destruct chain0; simpl; auto.
  assert (H1':=H1).
  eapply entry_is_head_of_compute_sdom_chains in H1';
    simpl; try solve [eauto | omega].
  destruct H1' as [chain0' H1']; subst; simpl.
  inv H1'.
  split; auto.
    eapply compute_sdom_chains_sorted;
      eauto using reachablity_analysis__in_bound.
      intros. eapply reachablity_analysis__reachable; eauto.
Qed.

Lemma dtrees_insert__in_children_roots: forall ch p0 ch0 dts,
  in_children_roots ch dts = in_children_roots ch (dtrees_insert dts p0 ch0).
Proof.
  induction dts; simpl; auto.
    rewrite <- IHdts.
    destruct d. simpl.
    destruct (l_dec l0 ch); subst.
      destruct (id_dec p0 ch); subst.
        destruct (in_children_roots ch0 d);
          destruct (l_dec ch ch); auto; try congruence.
        destruct (l_dec ch ch); auto; try congruence.
      destruct (id_dec p0 l0); subst.
        destruct (in_children_roots ch0 d);
          destruct (l_dec l0 ch); auto; try congruence.
        destruct (l_dec l0 ch); auto; try congruence.
Qed.

Definition dtree_insert__is_dtree_edge_prop (dt:DTree) :=
forall p ch p0 ch0,
  is_dtree_edge (dtree_insert dt p ch) p0 ch0 <->
  is_dtree_edge dt p0 ch0 \/ (p `in` dtree_dom dt /\ p = p0 /\ ch = ch0).

Definition dtrees_insert__is_dtrees_edge_prop (dts:DTrees) :=
forall p ch p0 ch0,
  is_dtrees_edge (dtrees_insert dts p ch) p0 ch0 <->
  is_dtrees_edge dts p0 ch0 \/ (p `in` dtrees_dom dts /\ p = p0 /\ ch = ch0).

Lemma dtree_insert__is_dtree_edge_mutrec :
  (forall dt, dtree_insert__is_dtree_edge_prop dt) *
  (forall dts, dtrees_insert__is_dtrees_edge_prop dts).
Proof.
  apply dtree_mutrec;
    unfold dtree_insert__is_dtree_edge_prop, dtrees_insert__is_dtrees_edge_prop;
    simpl; intros.

  Case "1".
    destruct (id_dec p l0); subst.
    SCase "1.1".
      destruct (id_dec p0 l0); subst.
      SSCase "1.1.1".
        remember (in_children_roots ch d) as R.
        destruct R; simpl.
        SSSCase "1.1.1.1".
          destruct (id_dec l0 l0); try congruence.
          split; intro J; auto.
            destruct J as [J | [J1 [J2 J3]]]; subst; auto.
            rewrite <- HeqR. reflexivity.

        SSSCase "1.1.1.2".
          destruct (id_dec l0 l0); try congruence.
          destruct (l_dec ch ch0); subst.
          SSSSCase "1.1.1.2.1".
            split; auto.
              intros. reflexivity.
          SSSSCase "1.1.1.2.2".
            destruct (in_children_roots ch0 d).
              split; auto.
                intros.
                destruct H0 as [H0 | [J1 J2]]; subst; auto; try congruence.
              destruct (id_dec l0 ch); subst.
                split; intros.
                  apply orb_true_iff in H0.
                  destruct H0; auto; try congruence.

                  apply orb_true_iff.
                  destruct H0 as [H0 | [J1 [J2 J3]]]; subst; auto.
                split; intros.
                  apply orb_true_iff in H0.
                  destruct H0; auto; try congruence.

                  apply orb_true_iff.
                  destruct H0 as [H0 | [J1 [J2 J3]]]; subst; auto.
      SSCase "1.1.2".
        remember (in_children_roots ch d) as R.
        destruct R; simpl.
        SSSCase "1.1.2.1".
          destruct (id_dec p0 l0); try congruence.
          split; intro J; auto.
            destruct J as [J | [J1 [J2 J3]]]; subst; auto.
              congruence.
        SSSCase "1.1.2.2".
          destruct (id_dec p0 l0); try congruence.
          destruct (l_dec p0 ch); subst.
          SSSSCase "1.1.2.2.1".
            destruct (id_dec ch ch); try congruence.
            split; intros.
              apply orb_true_iff in H0.
              destruct H0; auto; try congruence.

              apply orb_true_iff.
              destruct H0 as [H0 | [J1 [J2 J3]]]; subst; auto.

          SSSSCase "1.1.2.2.2".
            destruct (id_dec p0 ch); subst; try congruence.
            split; intros.
              apply orb_true_iff in H0.
              destruct H0; auto; try congruence.

              apply orb_true_iff.
              destruct H0 as [H0 | [J1 [J2 J3]]]; subst; auto.

    SCase "1.2".
      simpl.
      rewrite <- dtrees_insert__in_children_roots.
      destruct (id_dec p0 l0); subst.
      SSCase "1.2.1".
        remember (in_children_roots ch0 d) as R.
        destruct R; simpl.
        SSSCase "1.2.1.1".
          split; intro J; auto.
            reflexivity.
        SSSCase "1.2.1.2".
          split; intro J.
            apply H in J.
            destruct J as [J | [J1 [J2 J3]]]; subst; auto.

            apply H.
            destruct J as [J | [J1 [J2 J3]]]; subst; auto.
              congruence.
      SSCase "1.2.2".
        split; intro J; auto.
          apply H in J.
          destruct J as [J | [J1 [J2 J3]]]; subst; auto.

          apply H.
          destruct J as [J | [J1 [J2 J3]]]; subst; auto.
            right. fsetdec.

  Case "2".
    split; intros J.
       congruence.
       destruct J as [J | [J1 [J2 J3]]]; subst; auto.
         fsetdec.

  Case "3".
    split; intros J.
      apply orb_true_iff in J.
      destruct J as [J | J].
        apply H in J.
        destruct J as [J | [J1 [J2 J3]]]; subst.
          left. apply orb_true_iff. auto.
          right. fsetdec.

        apply H0 in J.
        destruct J as [J | [J1 [J2 J3]]]; subst.
          left. apply orb_true_iff. auto.
          right. fsetdec.

      apply orb_true_iff.
      destruct J as [J | [J1 [J2 J3]]]; subst.
        apply orb_true_iff in J.
        destruct J as [J | J].
          left. apply H; auto.
          right. apply H0; auto.

        assert (p0 `in` (dtree_dom d) \/ p0 `in` (dtrees_dom d0)) as J.
          fsetdec.
        destruct J as [J | J].
          left. apply H; auto.
          right. apply H0; auto.
Qed.

Lemma dtree_insert__is_dtree_edge : forall p ch p0 ch0 dt ,
  is_dtree_edge (dtree_insert dt p ch) p0 ch0 <->
  is_dtree_edge dt p0 ch0 \/ (p `in` dtree_dom dt /\ p = p0 /\ ch = ch0).
Proof.
  destruct (dtree_insert__is_dtree_edge_mutrec).
  unfold dtree_insert__is_dtree_edge_prop in *.
  eauto.
Qed.

Definition dtree_insert__in_dtree_dom_prop (dt:DTree) :=
forall p ch,
  p `in` dtree_dom dt -> is_dtree_edge (dtree_insert dt p ch) p ch.

Definition dtrees_insert__in_dtrees_dom_prop (dts:DTrees) :=
forall p ch,
  p `in` dtrees_dom dts ->is_dtrees_edge (dtrees_insert dts p ch) p ch.

Lemma dtree_insert__in_dtree_dom_mutrec :
  (forall dt, dtree_insert__in_dtree_dom_prop dt) *
  (forall dts, dtrees_insert__in_dtrees_dom_prop dts).
Proof.
  apply dtree_mutrec;
    unfold dtree_insert__in_dtree_dom_prop,
           dtrees_insert__in_dtrees_dom_prop;
    simpl; intros.

  destruct (id_dec p l0); subst; simpl.
    remember (in_children_roots ch d) as R.
    destruct R; simpl.
      rewrite <- HeqR.
      destruct (id_dec l0 l0); try congruence.

      rewrite <- HeqR.
      destruct (id_dec l0 l0); try congruence.
      destruct (l_dec ch ch); try congruence.

    destruct (id_dec p l0); subst; try congruence.
      apply H.
      assert (p = l0 \/ p `in` dtrees_dom d) as J.
        clear - H0. fsetdec.
      destruct J as [J | J]; subst; auto; try congruence.

  contradict H. auto.

  assert (p `in` (dtree_dom d) \/ p `in` (dtrees_dom d0)) as J.
    fsetdec.
  apply orb_true_iff.
    destruct J as [J | J].
      left. apply H; auto.
      right. apply H0; auto.
Qed.

Lemma dtree_insert__in_dtree_dom: forall dt p ch,
  p `in` dtree_dom dt -> is_dtree_edge (dtree_insert dt p ch) p ch.
Proof.
  destruct dtree_insert__in_dtree_dom_mutrec as [H _].
  unfold dtree_insert__in_dtree_dom_prop in H. auto.
Qed.

Definition is_dtree_edge__in_dtree_dom_prop (dt:DTree) :=
forall p ch, is_dtree_edge dt p ch ->
  p `in` dtree_dom dt /\ ch `in` dtree_dom dt.

Definition is_dtrees_edge__in_dtrees_dom_prop (dts:DTrees) :=
forall p ch, is_dtrees_edge dts p ch ->
  p `in` dtrees_dom dts /\ ch `in` dtrees_dom dts.

Lemma in_children_roots__dtrees_dom: forall ch dts,
  in_children_roots ch dts -> ch `in` dtrees_dom dts.
Proof.
  induction dts; simpl; intros.
    congruence.

    destruct d.
    destruct (l_dec l0 ch); subst; simpl; eauto.
Qed.

Lemma is_dtree_edge__in_dtree_dom_mutrec :
  (forall dt, is_dtree_edge__in_dtree_dom_prop dt) *
  (forall dts, is_dtrees_edge__in_dtrees_dom_prop dts).
Proof.
  apply dtree_mutrec;
    unfold is_dtree_edge__in_dtree_dom_prop,
           is_dtrees_edge__in_dtrees_dom_prop;
    simpl; intros.

  destruct (id_dec p l0); subst; simpl.
    remember (in_children_roots ch d) as R.
    destruct R; simpl.
      symmetry in HeqR.
      apply in_children_roots__dtrees_dom in HeqR. fsetdec.

      apply H in H0. destruct H0 as [J1 J2]. auto.

    apply H in H0. destruct H0 as [J1 J2]. auto.

  congruence.

  apply orb_true_iff in H1.
  destruct H1 as [J | J].
    apply H in J. destruct J; auto.
    apply H0 in J. destruct J; auto.
Qed.

Lemma is_dtree_edge__in_dtree_dom: forall dt p ch,
  is_dtree_edge dt p ch ->
  p `in` dtree_dom dt /\ ch `in` dtree_dom dt.
Proof.
  destruct is_dtree_edge__in_dtree_dom_mutrec as [H1 _].
  unfold is_dtree_edge__in_dtree_dom_prop in H1.
  auto.
Qed.

Lemma dtree_insert__ch_in_dtree_dom: forall dt p ch,
  p `in` dtree_dom dt -> ch `in` dtree_dom (dtree_insert dt p ch).
Proof.
  intros.
  eapply is_dtree_edge__in_dtree_dom.
  eapply dtree_insert__in_dtree_dom; eauto.
Qed.

Lemma create_dtree_from_chain__is_dtree_edge__is_chain_edge:
  forall p0 ch0 chain dt,
  (is_dtree_edge (create_dtree_from_chain dt chain) p0 ch0 ->
   is_dtree_edge dt p0 ch0 \/is_chain_edge chain p0 ch0) /\
  (is_dtree_edge dt p0 ch0 \/
   (chain_connects_dtree dt chain /\ is_chain_edge chain p0 ch0) ->
   is_dtree_edge (create_dtree_from_chain dt chain) p0 ch0).
Proof.
  induction chain; simpl; intros.
    split; intros; tauto.

    destruct chain.
      tauto.

      split; intros.
        apply IHchain in H.
        destruct H as [H | H]; auto.
        apply dtree_insert__is_dtree_edge in H.
        destruct H as [H | [H [H1 H2]]]; subst; auto.

        apply IHchain.
        destruct H as [H | [H [[H1 H2] | H1]]]; subst.
          left. apply dtree_insert__is_dtree_edge; auto.
          left. apply dtree_insert__is_dtree_edge; auto.
          right. split; auto.
            destruct chain; simpl in *; auto.
            apply dtree_insert__ch_in_dtree_dom; auto.
Qed.

Definition dtree_insert__in_dtree_dom_prop' (dt:DTree) :=
forall i0 p ch,
  i0 `in` dtree_dom dt -> i0 `in` dtree_dom (dtree_insert dt p ch).

Definition dtrees_insert__in_dtrees_dom_prop' (dts:DTrees) :=
forall i0 p ch,
  i0 `in` dtrees_dom dts -> i0 `in` dtrees_dom (dtrees_insert dts p ch).

Lemma dtree_insert__in_dtree_dom_mutrec' :
  (forall dt, dtree_insert__in_dtree_dom_prop' dt) *
  (forall dts, dtrees_insert__in_dtrees_dom_prop' dts).
Proof.
  apply dtree_mutrec;
    unfold dtree_insert__in_dtree_dom_prop',
           dtrees_insert__in_dtrees_dom_prop';
    simpl; intros.

  destruct (id_dec p l0); subst; simpl.
    remember (in_children_roots ch d) as R.
    destruct R; simpl.
      fsetdec.
      fsetdec.

    assert (i0 = l0 \/ i0 `in` dtrees_dom d) as J.
      clear - H0. fsetdec.
    destruct J as [J | J]; subst; auto; try congruence.

  contradict H. auto.

  assert (i0 `in` (dtree_dom d) \/ i0 `in` (dtrees_dom d0)) as J.
    fsetdec.
  destruct J as [J | J]; eauto.
Qed.

Lemma dtree_insert__in_dtree_dom': forall dt i0 p ch,
  i0 `in` dtree_dom dt -> i0 `in` dtree_dom (dtree_insert dt p ch).
Proof.
  destruct dtree_insert__in_dtree_dom_mutrec' as [H _].
  unfold dtree_insert__in_dtree_dom_prop' in H. auto.
Qed.

Lemma create_dtree_from_chain__chain_connects_dtree: forall chain0 chain dt,
  chain_connects_dtree dt chain0 ->
  chain_connects_dtree (create_dtree_from_chain dt chain) chain0.
Proof.
  induction chain; simpl; intros; auto.
    destruct chain; auto.
    apply IHchain.
    destruct chain0; simpl in *; intros; auto.
    destruct chain0; auto.
    eapply dtree_insert__in_dtree_dom'; eauto.
Qed.

Lemma fold_left_create_dtree_from_chain__is_dtree_edge__is_chain_edge:
  forall p0 ch0 chains dt,
  (is_dtree_edge
    (fold_left
      (fun (acc : DTree) (elt : l * list id) =>
       let '(_, chain) := elt in create_dtree_from_chain acc chain)
     chains dt) p0 ch0 ->
  (is_dtree_edge dt p0 ch0 \/
   exists l0, exists chain0,
     In (l0, chain0) chains /\ is_chain_edge chain0 p0 ch0)) /\
  ((is_dtree_edge dt p0 ch0 \/
   exists l0, exists chain0,
     In (l0, chain0) chains /\ chain_connects_dtree dt chain0 /\
     is_chain_edge chain0 p0 ch0) ->
   is_dtree_edge
    (fold_left
      (fun (acc : DTree) (elt : l * list id) =>
       let '(_, chain) := elt in create_dtree_from_chain acc chain)
     chains dt) p0 ch0).
Proof.
  induction chains; simpl; intros.
    split; intro J; auto.
      destruct J as [H | [l0 [chn0 [J1 J2]]]]; auto.
        inv J1.

    destruct a.
    destruct (IHchains (create_dtree_from_chain dt l1)) as [J1 J2].
    clear IHchains.
    split; intros J.
      apply J1 in J.
      destruct J as [J | [l2 [chain2 [J3 J4]]]].
        apply create_dtree_from_chain__is_dtree_edge__is_chain_edge in J.
        destruct J as [J | J]; auto.
          right. exists l0. exists l1. auto.
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

Lemma create_dtree__wf_dtree: forall f dt,
  create_dtree f = Some dt ->
  match getEntryLabel f, reachablity_analysis f with
  | Some root, Some rd =>
      let dt' := dom_analyze f in
      let b := bound_fdef f in
      let chains := compute_sdom_chains b dt' rd in
      forall p0 ch0,
        (is_dtree_edge dt p0 ch0 ->
         exists l0, exists chain0,
           In (l0, chain0) chains /\ is_chain_edge chain0 p0 ch0) /\
        ((exists l0, exists chain0,
           In (l0, chain0) chains /\
           chain_connects_dtree (DT_node root DT_nil) chain0 /\
           is_chain_edge chain0 p0 ch0) -> is_dtree_edge dt p0 ch0)
  | _, _ => False
  end.
Proof.
  unfold create_dtree.
  intros.
  remember (getEntryLabel f) as R.
  destruct R; tinv H.
  remember (reachablity_analysis f) as R.
  destruct R; inv H.
  intros.
  destruct (@fold_left_create_dtree_from_chain__is_dtree_edge__is_chain_edge
    p0 ch0 (compute_sdom_chains (bound_fdef f) (dom_analyze f) l1)
    (DT_node l0 DT_nil)) as [J1 J2].
  split; intros J; auto.
    apply J1 in J.
    destruct J as [J | J]; auto.
      simpl in J. destruct (id_dec p0 l0); tinv J.
Qed.

