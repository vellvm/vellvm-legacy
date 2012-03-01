Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Maps.
Require Import opsem_props.
Require Import promotable_props.
Require Import primitives.
Require Import palloca_props.
Require Import memory_props.
Require Import program_sim.
Require Import trans_tactic.
Require Import dae.
Require Import list_facts.

Section uniqueness.

(* Removing an id from an fdef preserves uniqueness *)

Hint Resolve sl_nil sublist_refl.

Lemma remove_block__blockLocs__sublist :
  forall (id1 : id) (bs : blocks),
    sublist (getBlocksLocs (List.map (remove_block id1) bs))
    (getBlocksLocs bs).
Proof.
  intros id1 bs. induction bs as [|[lab phis cmds tmn] bs]. apply sl_nil.
  simpl. repeat apply sublist_app; trivial; clear IHbs.
  apply sublist_map. apply filter_sublist.
  induction cmds as [|cmd cmds]. apply sl_nil.
  simpl. destruct (id_dec (getCmdLoc cmd) id1); simpl;
  [apply sl_cons_r|apply sl_cons]; trivial.
Qed.

Lemma remove_block__uniqBlocks :
  forall (id1 : id) (bs : blocks),
    uniqBlocks bs -> uniqBlocks (List.map (remove_block id1) bs).
Proof.
  intros id1 bs H.
  split; [destruct H as [H _] | destruct H as [_ H]];
    apply (NoDup_sublist _ _ _ H); clear H;
      [|apply remove_block__blockLocs__sublist].
  induction bs as [|[lab phis cmds tmn] bs]; simpl;
    [apply sl_nil|apply sl_cons]; trivial.
Qed.

Lemma remove_fdef__uniqFdef :
  forall (id1 : id) (f : fdef),
    uniqFdef f -> uniqFdef (remove_fdef id1 f).
Proof.
  intros id1 f H.
  destruct f as [[att rtyp idf fas fvas] bs].
  destruct H as [Hbsuniq HNoDup].
  simpl. split. apply remove_block__uniqBlocks. trivial.
  apply NoDup_split' in HNoDup. destruct HNoDup as [Hfas [Hbs Hin]].
  apply NoDup_app. trivial.
    apply NoDup_sublist with (getBlocksLocs bs). trivial.
    apply remove_block__blockLocs__sublist.

    intros id' H1 H2. clear Hbsuniq. apply (Hin id' H1).
    clear H1. generalize id' H2. clear id' H2.
    apply sublist_In. apply remove_block__blockLocs__sublist.
Qed.

End uniqueness.

Section product_well_formedness.

(* Products are well-formed independently of each other. Therefore,
   changing just one product in a module shouldn't interfere with the
   others. *)

Lemma wf_prod_split :
  forall (sys : system)
    (m : module) (ps1 ps2 : products),
    wf_prods sys m (ps1 ++ ps2) ->
    wf_prods sys m ps1 /\ wf_prods sys m ps2.
Proof.
  induction ps1 as [|p ps1]. split. constructor. trivial.
  intros ps2 Hwf. inversion Hwf as [|? ? ? ? Hwfps Hwfp]. subst.
  clear Hwf. apply IHps1 in Hwfps. destruct Hwfps as [Hps1 Hps2].
  split; trivial.
  apply wf_prods_cons; trivial.
Qed.

Lemma in_module_wf_prods :
  forall (sys : system) (m : module) (ps : products),
    (forall p : product, InProductsB p ps -> wf_prod sys m p) ->
    wf_prods sys m ps.
Proof.
  induction ps as [|p ps]. intros. constructor.
  intros H. apply wf_prods_cons.

    apply IHps. intros p' Hin. apply H. simpl.
    apply orb_true_intro. right. trivial.

    apply H. apply orb_true_intro. left. apply productEqB_refl.
Qed.

End product_well_formedness.

Lemma InProductsB_In : forall (p : product) (ps : products),
  InProductsB p ps = true <-> In p ps.
Proof.
  intros p ps. split; induction ps as [|p' ps]; try discriminate.

    intros H. simpl in H. apply orb_true_elim in H.
    destruct H as [H | H].

      left. apply productEqB_inv in H. auto.

      right. apply IHps. trivial.

    intros H. inversion H.

    intros H. apply orb_true_intro. destruct H as [H | H].

      left. rewrite H. apply productEqB_refl.

      right. apply IHps. trivial.
Qed.

Lemma dae_wfS: forall
  (id0 : id) (f :fdef) (pinfo : PhiInfo)
  (los : layouts) (nts : namedts) (Ps1 Ps2 : list product)
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Heq1: f = PI_f pinfo) (Heq2: id0 = PI_id pinfo),
  wf_system
    [module_intro los nts (Ps1 ++ product_fdef (remove_fdef id0 f) :: Ps2)].
Proof.
(*
   TODO: port to 3.0

  intros. apply wf_system_intro.

    apply wf_modules_cons; [|apply wf_modules_nil].
    constructor.

      constructor.
      inversion HwfS as [ms H _]. subst.
      inversion H as [|sys m ms Hm Hms]. subst.
      inversion Hm as [? ? ? ? Hnames Hin Hprods]. subst.
      inversion Hnames as [? ? ? Hty Htarget]. subst.

      left. trivial.

      apply in_module_wf_prods. intros p Hin.
      unfold is_true in Hin. rewrite InProductsB_In in Hin.
      apply in_app in Hin.
      assert (Hin' : (In p Ps1 \/ In p Ps2) \/
        (product_fdef (remove_fdef id0 f)) = p).

        destruct Hin as [Hin | [Hin | Hin]]; auto.

      clear Hin. destruct Hin' as [Hp | Hp].

        match goal with
          | H : wf_system nil [?m] |- _ =>
            match m with
              | module_intro _ _ ?ps =>
                assert (wf_prod nil [m] m p);
                [apply wf_prods__wf_prod with ps | idtac]
            end
        end.

          inversion HwfS. inversion H. inversion H7. trivial.

          rewrite InProductsB_In. rewrite in_app.
          destruct Hp; auto. repeat right. trivial.

        clear HwfS Hp. admit.

        subst p. apply wf_prod_function_def. apply wf_g_intro.
        match goal with
          | H : wf_system nil [?m] |- _ =>
            assert (Hf : wf_fdef nil [m] m f)
        end.

          apply wf_system__wf_fdef. trivial.

            simpl. rewrite moduleEqB_refl. trivial.

            simpl. rewrite InProductsB_In. rewrite in_app. right.
            left. trivial.

        admit.

    split; simpl; trivial.
    inversion HwfS as [ins sys _ H]. subst ins sys.
    destruct H as [[Huniq [H1 H2]] _]. repeat split; trivial; clear H1.

      clear H2. apply Forall_forall. intros p Hin.
      unfold uniqProducts in Huniq. rewrite Forall_forall in Huniq.
      rewrite in_app in Hin.
      destruct Hin as [Hin | [Hin | Hin]].

        apply Huniq; rewrite in_app; left; trivial.

        rewrite <- Hin. apply remove_fdef__uniqFdef.
        match goal with
          | H : wf_system nil [?m] |- _ =>
            apply (uniqSystem__uniqFdef [m] f m)
        end. inversion HwfS. subst. trivial.
        apply andb_true_intro. split.

          compute. apply orb_true_intro. left. apply moduleEqB_refl.

          simpl. rewrite InProductsB_In. rewrite in_app.
          right. left. trivial.

        apply Huniq. rewrite in_app. right. right. trivial.

      clear Huniq. unfold getProductsIDs in *. rewrite List.map_app in *.
      apply NoDup_split' in H2.
      destruct H2 as [H1 [H Hdis]].
      simpl in H. inversion H as [|i l Hnin]. subst i l. clear H.
      destruct f as [[] ?]. simpl in *.
      apply NoDup_app; trivial.
      apply NoDup_cons; trivial.
Qed.
*)
Admitted.