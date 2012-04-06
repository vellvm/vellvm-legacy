Require Import vellvm.
Require Import genericvalues_inject.
Require Import palloca_props.

Structure FunSim := mkFunSim {
fsim: fdef -> fdef -> Prop;
eq_fheader: forall f1 f2
  (H: fsim f1 f2), fheaderOfFdef f1 = fheaderOfFdef f2;
det_right: forall f f1 f2,
  fsim f f1 -> fsim f f2 -> f1 = f2
}.

Module TopSim.

Section TopSim.

Context `{FSim : FunSim}.

Definition products_simulation Ps1 Ps2: Prop :=
List.Forall2
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => FSim.(fsim) f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation S1 S2: Prop :=
List.Forall2
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\
       products_simulation Ps1 Ps2
   end) S1 S2.

Definition module_simulation (M1 M2: module) : Prop :=
match M1, M2 with
| module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
    los1 = los2 /\ nts1 = nts2 /\ 
    products_simulation Ps1 Ps2
end.

Lemma fdef_simulation__inv: forall f1 f2,
  FSim.(fsim) f1 f2 -> getFdefID f1 = getFdefID f2.
Proof.
  intros.
  apply FSim.(eq_fheader) in H.
  destruct f1 as [[]]; destruct f2 as [[]]; inv H; auto.
Qed.

Lemma products_simulation__fdef_simulation_l2r : forall fid Ps1 Ps2
  (Hsim: products_simulation Ps1 Ps2) f1,
  lookupFdefViaIDFromProducts Ps1 fid = Some f1 ->
  exists f2,
    lookupFdefViaIDFromProducts Ps2 fid = Some f2 /\
    FSim.(fsim) f1 f2.
Proof.
  intros fid Ps1 Ps2 Hsim.
  induction Hsim; simpl; intros.
    inv H.

    destruct x as [?|?|f];
    destruct y as [?|?|f0]; inv H0; eauto; try congruence.
    destruct (getFdefID f == fid); subst.
      inv H2. simpl.
      destruct (getFdefID f0 == getFdefID f1); eauto.
        apply IHHsim. simpl.
        destruct f0 as [[]], f1 as [[]].
        apply fdef_simulation__inv in H.
        contradict n; auto.
    simpl.
    destruct (getFdefID f0 == fid); subst; auto.
      destruct f0 as [[]], f as [[]].
      apply fdef_simulation__inv in H.
      contradict n; auto.
Qed.

Lemma products_simulation__fdef_simulation_r2l : forall fid f2 Ps1 Ps2,
  products_simulation Ps1 Ps2 ->
  lookupFdefViaIDFromProducts Ps2 fid = ret f2 ->
  exists f1,
    lookupFdefViaIDFromProducts Ps1 fid = ret f1 /\
    FSim.(fsim) f1 f2.
Proof.
  induction Ps1; simpl; intros Ps2 J1 J2.
    inv J1. inv J2.

    inv J1. simpl in J2.
    remember (lookupFdefViaIDFromProduct y fid) as R.
    destruct R; inv J2.
      destruct a as [?|f0|f0]; subst; tinv HeqR.
      destruct y as [?|?|f5]; subst; tinv HeqR.
      simpl in HeqR. simpl.
      destruct (getFdefID f5 == fid); inv HeqR.
      exists f0.
      split; auto.
        apply fdef_simulation__inv in H1.
        destruct (getFdefID f0 == getFdefID f5); auto.
        rewrite H1 in n. congruence.

      destruct a as [?|f0|f0]; subst; simpl; try eapply IHPs1; eauto.  
      destruct y as [?|?|f5]; subst; tinv H1.
      simpl in *.
      destruct (getFdefID f5 == fid); inv HeqR.
      eapply IHPs1 in H0; eauto.
      destruct H0 as [f1 [J1 J2]].
      exists f1.
      split; auto.
        apply fdef_simulation__inv in H1.
        rewrite H1.
        destruct (getFdefID f5 == fid); auto.
          subst. congruence.
Qed.

Lemma products_simulation__fdef_simulation : forall fid Ps1 Ps2
  (Hsim: products_simulation Ps1 Ps2) f1 f2,
  lookupFdefViaIDFromProducts Ps2 fid = Some f2 ->
  lookupFdefViaIDFromProducts Ps1 fid = Some f1 ->
  FSim.(fsim) f1 f2.
Proof.
  intros.
  eapply products_simulation__fdef_simulation_r2l in H; eauto.
  destruct H as [f1' [H1 H2]].
  uniq_result. auto.
Qed.

Lemma products_simulation__fdef_None_r2l : forall fid Ps1 Ps2,
  products_simulation Ps1 Ps2 ->
  lookupFdefViaIDFromProducts Ps2 fid = merror ->
  lookupFdefViaIDFromProducts Ps1 fid = merror.
Proof.
  intros.
  remember (lookupFdefViaIDFromProducts Ps1 fid) as R.
  destruct R; auto. symmetry_ctx.
  eapply products_simulation__fdef_simulation_l2r in HeqR; eauto.
  destruct HeqR as [f2 [J1 J2]].
  congruence.
Qed.

Lemma products_simulation__fdef_None_l2r : forall fid Ps1 Ps2,
  products_simulation Ps1 Ps2 ->
  lookupFdefViaIDFromProducts Ps1 fid = merror ->
  lookupFdefViaIDFromProducts Ps2 fid = merror.
Proof.
  intros.
  remember (lookupFdefViaIDFromProducts Ps2 fid) as R.
  destruct R; auto. symmetry_ctx.
  eapply products_simulation__fdef_simulation_r2l in HeqR; eauto.
  destruct HeqR as [f2 [J1 J2]].
  congruence.
Qed.

Lemma products_simulation__fdec_eq : forall fid Ps1 Ps2,
  products_simulation Ps1 Ps2 ->
  lookupFdecViaIDFromProducts Ps1 fid =
    lookupFdecViaIDFromProducts Ps2 fid.
Proof.
  induction 1; simpl; auto.
    rewrite IHForall2.
    destruct x; subst; auto.
    destruct y; subst; auto.
    congruence.
Qed.

Lemma products_simulation__fdec_r2l : forall fid f Ps1 Ps2,
  products_simulation Ps1 Ps2 ->
  lookupFdecViaIDFromProducts Ps2 fid = ret f ->
  lookupFdecViaIDFromProducts Ps1 fid = ret f.
Proof.
  intros.
  erewrite products_simulation__fdec_eq; eauto. 
Qed.

Lemma products_simulation__fdec_l2r : forall fid f Ps1 Ps2,
  products_simulation Ps1 Ps2 ->
  lookupFdecViaIDFromProducts Ps1 fid = ret f ->
  lookupFdecViaIDFromProducts Ps2 fid = ret f.
Proof.
  intros.
  erewrite <- products_simulation__fdec_eq; eauto. 
Qed.

Lemma system_simulation__fdef_simulation_r2l : forall fid f2 S1 S2
  (Hssim: system_simulation S1 S2)
  (Hlkup: lookupFdefViaIDFromSystem S2 fid = ret f2),
  exists f1, 
    lookupFdefViaIDFromSystem S1 fid = ret f1 /\
    FSim.(fsim) f1 f2.
Proof.
  induction 1; simpl; intros.
    inv Hlkup.

    match goal with
    | H: match ?x with
         | module_intro _ _ _ => 
             match ?y with | module_intro _ _ _ => _ end
         end |- _ => 
        destruct x as [los1 nts1 Ps1]; destruct y as [los2 nts2 Ps2];
        destruct H as [J1 [J2 J3]]; subst
    end.
    simpl in *.

   destruct_match.
     eapply products_simulation__fdef_simulation_r2l in HeqR; eauto.
     destruct HeqR as [f1 [J1 J2]].
     fill_ctxhole. eauto.

     symmetry in HeqR.
     eapply products_simulation__fdef_None_r2l in HeqR; eauto.
     fill_ctxhole. eauto.
Qed.

Lemma products_simulation__eq_getFdefsIDs: forall Ps1 Ps2
  (Hpsim: products_simulation Ps1 Ps2),
  getFdefsIDs Ps1 = getFdefsIDs Ps2.
Proof.
  intros.
  induction Hpsim; intros; auto.
    destruct x; subst; simpl; auto.
    destruct y; tinv H.
    destruct fdef5 as [[]]. destruct fdef0 as [[]]. 
    apply fdef_simulation__inv in H. congruence.
Qed.

Lemma products_fdef_simulation__InProductsB_forward: forall f1 f2 Ps1 Ps2,
  products_simulation Ps1 Ps2 ->
  InProductsB (product_fdef f1) Ps1 = true ->
  FSim.(fsim) f1 f2 ->
  InProductsB (product_fdef f2) Ps2 = true.
Proof.
  induction 1; simpl; intros; auto.
    destruct x; subst; simpl.
      rewrite productNEqB_intro in H1; try congruence.
      rewrite productNEqB_intro; try congruence.
      rewrite orb_false_l in H1.
      rewrite orb_false_l. auto.

      rewrite productNEqB_intro in H1; try congruence.
      rewrite productNEqB_intro; try congruence.
      rewrite orb_false_l in H1.
      rewrite orb_false_l. auto.

      destruct y; tinv H.
      apply orb_true_iff in H1.
      destruct H1 as [H1 | H1].
        apply productEqB_inv in H1. inv H1.
        erewrite FSim.(det_right) with (f1:=fdef0)(f2:=f2)(f:=fdef5); eauto.
        rewrite productEqB_refl. auto.

        rewrite IHForall2; auto.
        apply orb_true_r.
Qed.

Lemma system_simulation__getParentOfFdefFromSystem: forall S1 S2 f1 f2 m2
  fid (Hsim: system_simulation S1 S2)
  (Hfsim: FSim.(fsim) f1 f2)
  (Hparent: getParentOfFdefFromSystem f2 S2 = Some m2)
  (Hlkup: lookupFdefViaIDFromSystem S1 fid = ret f1),
  exists m1, getParentOfFdefFromSystem f1 S1 = Some m1 /\
             module_simulation m1 m2.
Proof.
  intros.
  assert (J:=Hlkup).
  apply lookupFdefViaIDFromSystem_ideq in J. subst.
  induction Hsim; simpl in *; intros.
    congruence.

    match goal with
    | H: match ?x with
         | module_intro _ _ _ => 
             match ?y with | module_intro _ _ _ => _ end
         end |- _ => 
        destruct x as [los1 nts1 Ps1]; destruct y as [los2 nts2 Ps2];
        destruct H as [J1 [J2 J3]]; subst
    end.
    simpl in *.
    assert (J:=Hfsim).
    apply fdef_simulation__inv in J.
    destruct_if.
      destruct_match; simpl in e.       
        exists (module_intro los2 nts2 Ps1).
        split; simpl; auto.
          match goal with
          | |- (if ?e then _ else _ ) = _ => destruct e; auto
          end.
          simpl in e0. 
          apply lookupFdefViaIDFromProducts__InProductsB in HeqR0.
          congruence.

          match goal with
          | e: InProductsB (product_fdef ?f2) ?Ps2 = true,
            HeqR0: None = lookupFdefViaIDFromProducts ?Ps1 (getFdefID ?f1),
            J3: products_simulation ?Ps1 ?Ps2,
            J: getFdefID ?f1 = getFdefID ?f2 |- _ =>
            symmetry in HeqR0;
            apply lookupFdefViaIDFromProducts__notin_getFdefsIDs in HeqR0;
            assert (Hin:=e);  
            apply InProductsB__in_getFdefsIDs in Hin;
            apply products_simulation__eq_getFdefsIDs in J3;
            simpl in Hin; rewrite J in HeqR0; congruence
          end.

      simpl in e.       
      destruct_match.
        apply lookupFdefViaIDFromProducts__InProductsB in HeqR0.
        eapply products_fdef_simulation__InProductsB_forward in HeqR0; eauto.
        congruence.

        apply IHHsim in H0; auto.
        destruct H0 as [m1 [J1 J2]].
        exists m1.
          split; auto. 
          match goal with
          | |- (if ?e then _ else _ ) = _ => destruct e; auto
          end.
          simpl in e0. 
          assert (Hin:=e0).  
          apply InProductsB__in_getFdefsIDs in Hin.
          symmetry in HeqR0.
          apply lookupFdefViaIDFromProducts__notin_getFdefsIDs in HeqR0.
          simpl in Hin. rewrite J in HeqR0. congruence.
Qed.

Lemma genGlobalAndInitMem_spec_aux: forall td ps1 ps2 ,
  products_simulation ps1 ps2 ->
  forall gl fs M gl2 fs2 M2,
  OpsemAux.genGlobalAndInitMem td ps2 gl fs M =
    ret (gl2, fs2, M2) ->
  exists gl1, exists fs1, exists M1,
    OpsemAux.genGlobalAndInitMem td ps1 gl fs M =
      ret (gl1, fs1, M1) /\ gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2.
Proof.
  induction 1; intros.
    fill_ctxhole. eauto 7.

    destruct x; subst; simpl in *.
      match goal with
      | g:gvar |- _ => destruct g
      end; inv_mbind; try destruct_let; eauto.
        destruct fdec5 as [[]].
        inv_mbind. eauto.

      destruct fdef5 as [[]].
      destruct y; simpl in *; tinv H.
      destruct fdef5 as [[]].
      inv_mbind. 
      apply FSim.(eq_fheader) in H.
      inv H. symmetry_ctx. fill_ctxhole. eauto.
Qed.

Lemma genGlobalAndInitMem_spec: forall td ps1 ps2 gl2 fs2 M2,
  OpsemAux.genGlobalAndInitMem td ps2 nil nil Mem.empty =
    ret (gl2, fs2, M2) ->
  products_simulation ps1 ps2 ->
  exists gl1, exists fs1, exists M1,
    OpsemAux.genGlobalAndInitMem td ps1 nil nil Mem.empty =
      ret (gl1, fs1, M1) /\ gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2.
Proof.
  intros.
  eapply genGlobalAndInitMem_spec_aux; eauto.
Qed.

Lemma lookupFdefViaPtr__simulation_None_l2r : forall Ps1 Ps2 fptr fs,
  OpsemAux.lookupFdefViaPtr Ps2 fs fptr = None ->
  products_simulation Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs fptr = None.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptr) as R2.
  destruct R2 as [fid|]; simpl in *; auto.
  eapply products_simulation__fdef_None_r2l; eauto.
Qed.

Lemma lookupFdefViaPtr__simulation_None_r2l : forall Ps1 Ps2 fptr fs,
  OpsemAux.lookupFdefViaPtr Ps1 fs fptr = None ->
  products_simulation Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps2 fs fptr = None.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptr) as R2.
  destruct R2 as [fid|]; simpl in *; auto.
  eapply products_simulation__fdef_None_l2r; eauto.
Qed.

Lemma products_simulation__fdec_None_r2l : forall fid Ps1 Ps2,
  products_simulation Ps1 Ps2 ->
  lookupFdecViaIDFromProducts Ps2 fid = None ->
  lookupFdecViaIDFromProducts Ps1 fid = None.
Proof.
  intros.
  erewrite products_simulation__fdec_eq; eauto. 
Qed.

Lemma products_simulation__fdec_None_l2r : forall fid Ps1 Ps2,
  products_simulation Ps1 Ps2 ->
  lookupFdecViaIDFromProducts Ps1 fid = None ->
  lookupFdecViaIDFromProducts Ps2 fid = None.
Proof.
  intros.
  erewrite <- products_simulation__fdec_eq; eauto. 
Qed.

Lemma lookupExFdecViaPtr__simulation_None_r2l : forall Ps1 Ps2 fptr fs,
  OpsemAux.lookupExFdecViaPtr Ps2 fs fptr = None ->
  products_simulation Ps1 Ps2 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs fptr = None.
Proof.
  intros.
  unfold OpsemAux.lookupExFdecViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptr) as R2.
  destruct R2 as [fid|]; simpl in *; auto.
  remember (lookupFdefViaIDFromProducts Ps2 fid) as R.
  destruct R as [fid'|].
    symmetry_ctx.
    eapply products_simulation__fdef_simulation_r2l in HeqR; eauto.
    destruct HeqR as [f1 [J1 J2]].
    fill_ctxhole. auto.
    erewrite products_simulation__fdef_None_r2l; eauto.

  eapply products_simulation__fdec_None_r2l; eauto.
Qed.

Lemma lookupFdefViaPtr__simulation : forall Ps1 Ps2 fptr f1 f2 fs,
  OpsemAux.lookupFdefViaPtr Ps2 fs fptr = Some f2 ->
  products_simulation Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs fptr = Some f1 ->
  FSim.(fsim) f1 f2.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptr) as R2.
  destruct R2 as [fid|]; inv H1. simpl in H.
  eapply products_simulation__fdef_simulation in H0; eauto.
Qed.

Lemma lookupFdefViaPtr_inj__simulation_l2r' : forall Ps1 Ps2 fptr1 fptr2 f1 fs1
  fs2 mi,
  OpsemAux.ftable_simulation mi fs1 fs2 ->
  products_simulation Ps1 Ps2 ->
  gv_inject mi fptr1 fptr2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs1 fptr1 = Some f1 ->
  exists f2, 
    OpsemAux.lookupFdefViaPtr Ps2 fs2 fptr2 = Some f2 /\ FSim.(fsim) f1 f2.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs1 fptr1) as R1.
  destruct R1 as [fid1|]; inv H2.
  eapply products_simulation__fdef_simulation_l2r in H0; eauto.
  destruct H0 as [f2 [J1 J2]].
  exists f2. 
  unfold OpsemAux.ftable_simulation in H.
  erewrite H in HeqR1; eauto. rewrite <- HeqR1. simpl. auto.
Qed.

Lemma lookupFdefViaPtr_inj__simulation : forall Ps1 Ps2 fptr1 fptr2 f1 f2 fs1
  fs2 mi,
  OpsemAux.ftable_simulation mi fs1 fs2 ->
  OpsemAux.lookupFdefViaPtr Ps2 fs2 fptr2 = Some f2 ->
  products_simulation Ps1 Ps2 ->
  gv_inject mi fptr1 fptr2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs1 fptr1 = Some f1 ->
  FSim.(fsim) f1 f2.
Proof.
  intros.
  eapply lookupFdefViaPtr_inj__simulation_l2r' in H1; eauto.
  destruct H1 as [f2' [J1 J2]].
  uniq_result. auto.
Qed.

Lemma products_simulation__fdec_simulation_l2r : forall fid Ps1 Ps2
  (Hsim: products_simulation Ps1 Ps2) f1,
  lookupFdecViaIDFromProducts Ps1 fid = Some f1 ->
  lookupFdecViaIDFromProducts Ps2 fid = Some f1.
Proof.
  intros fid Ps1 Ps2 Hsim.
  induction Hsim; simpl; intros; auto.
    destruct x as [?|f|?]; destruct y as [?|f0|?]; subst; simpl; tinv H; auto.
    inv H. simpl in H0.
    destruct (getFdecID f0 == fid); subst; auto.
Qed.

Lemma products_simulation__fdec_simulation : forall fid Ps1 Ps2
  (Hsim: products_simulation Ps1 Ps2) f1 f2,
  lookupFdecViaIDFromProducts Ps2 fid = Some f2 ->
  lookupFdecViaIDFromProducts Ps1 fid = Some f1 ->
  f1 = f2.
Proof.
  intros.
  eapply products_simulation__fdec_simulation_l2r in Hsim; eauto. 
  congruence.
Qed.

Lemma lookupFdefViaPtr_inj__simulation_l2r : forall Ps1 Ps2 fptr1 fptr2 f1
  fs1 fs2 mi f2,
  products_simulation Ps1 Ps2 ->
  OpsemAux.ftable_simulation mi fs1 fs2 ->
  gv_inject mi fptr1 fptr2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs1 fptr1 = Some f1 ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs2 fptr2 = Some f2 ->
  False.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs1 fptr1) as R1.
  destruct R1 as [fid1|]; inv H2.
  unfold OpsemAux.lookupExFdecViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs2 fptr2) as R2.
  destruct R2 as [fid2|]; inv H3.
  remember (lookupFdefViaIDFromProducts Ps2 fid2) as R3.
  destruct R3; inv H4.
  eapply products_simulation__fdef_simulation_l2r in H5; eauto.
  destruct H5 as [f2' [J1 J2]].
  unfold OpsemAux.ftable_simulation in H0.
  erewrite H0 in HeqR1; eauto.
  rewrite <- HeqR1 in HeqR2. inv HeqR2.
  rewrite J1 in HeqR3. inv HeqR3.
Qed.

Lemma lookupExFdecViaPtr_inj__simulation_l2r' : forall Ps1 Ps2 fptr1 fptr2 f1
  fs1 fs2 mi,
  products_simulation Ps1 Ps2 ->
  OpsemAux.ftable_simulation mi fs1 fs2 ->
  gv_inject mi fptr1 fptr2 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs1 fptr1 = Some f1 ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs2 fptr2 = Some f1.
Proof.
  intros.
  unfold OpsemAux.lookupExFdecViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs1 fptr1) as R1.
  destruct R1 as [fid1|]; inv H2.
  remember (lookupFdefViaIDFromProducts Ps1 fid1) as R3.
  destruct R3; tinv H4. symmetry_ctx.
  unfold OpsemAux.ftable_simulation in H0.
  erewrite H0 in HeqR1; eauto.
  rewrite HeqR1. simpl.
  assert (H':=H).
  eapply products_simulation__fdef_None_l2r in H'; eauto.
  fill_ctxhole.
  eapply products_simulation__fdec_simulation_l2r in H; eauto.
  congruence.
Qed.

Lemma lookupExFdecViaPtr_inj__simulation : forall Ps1 Ps2 fptr1 fptr2 f1
  f2 fs1 fs2 mi,
  products_simulation Ps1 Ps2 ->
  OpsemAux.ftable_simulation mi fs1 fs2 ->
  gv_inject mi fptr1 fptr2 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs1 fptr1 = Some f1 ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs2 fptr2 = Some f2 ->
  f1 = f2.
Proof.
  intros.
  eapply lookupExFdecViaPtr_inj__simulation_l2r' in H0; eauto.
  congruence.
Qed.

Lemma lookupFdefViaPtr_inj__simulation_r2l : forall Ps1 Ps2 fptr1 fptr2 f1
  fs1 fs2 mi f2,
  products_simulation Ps1 Ps2 ->
  OpsemAux.ftable_simulation mi fs1 fs2 ->
  gv_inject mi fptr1 fptr2 ->
  OpsemAux.lookupFdefViaPtr Ps2 fs2 fptr2 = Some f2 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs1 fptr1 = Some f1 ->
  False.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs2 fptr2) as R1.
  destruct R1 as [fid2|]; inv H2.
  unfold OpsemAux.lookupExFdecViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs1 fptr1) as R2.
  destruct R2 as [fid1|]; inv H3.
  remember (lookupFdefViaIDFromProducts Ps1 fid1) as R3.
  destruct R3; inv H4.
  eapply products_simulation__fdef_simulation_r2l in H5; eauto.
  destruct H5 as [f2' [J1 J2]].
  unfold OpsemAux.ftable_simulation in H0.
  erewrite H0 in HeqR2; eauto.
  rewrite <- HeqR2 in HeqR1. inv HeqR1.
  rewrite J1 in HeqR3. inv HeqR3.
Qed.

Lemma lookupFdefViaPtr__simulation_l2r : forall Ps1 Ps2 fptr f1 fs,
  products_simulation Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs fptr = Some f1 ->
  exists f2,
    OpsemAux.lookupFdefViaPtr Ps2 fs fptr = Some f2 /\
    FSim.(fsim) f1 f2.
Proof.
  unfold OpsemAux.lookupFdefViaPtr.
  intros. 
  destruct (OpsemAux.lookupFdefViaGVFromFunTable fs fptr); tinv H0.
  simpl in H0.
  eapply products_simulation__fdef_simulation_l2r in H0; eauto.
Qed.

Lemma lookupExFdecViaPtr__simulation_l2r : forall Ps1 Ps2 fptr f fs,
  products_simulation Ps1 Ps2 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs fptr = Some f ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs fptr = Some f.
Proof.
  unfold OpsemAux.lookupExFdecViaPtr.
  intros. 
  destruct (OpsemAux.lookupFdefViaGVFromFunTable fs fptr); tinv H0.
  simpl in H0. simpl.
  remember (lookupFdefViaIDFromProducts Ps1 i0) as R.
  destruct R; tinv H0.
  erewrite products_simulation__fdef_None_l2r; eauto.
  erewrite products_simulation__fdec_l2r; eauto.
Qed.

Lemma lookupFdefViaPtr__simulation_r2l : forall Ps1 Ps2 fptr f2 fs,
  products_simulation Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps2 fs fptr = Some f2 ->
  exists f1,
    OpsemAux.lookupFdefViaPtr Ps1 fs fptr = Some f1 /\
    FSim.(fsim) f1 f2.
Proof.
  unfold OpsemAux.lookupFdefViaPtr.
  intros. 
  destruct (OpsemAux.lookupFdefViaGVFromFunTable fs fptr); tinv H0.
  simpl in H0.
  eapply products_simulation__fdef_simulation_r2l in H0; eauto.
Qed.

Lemma lookupExFdecViaPtr__simulation_r2l : forall Ps1 Ps2 fptr f fs,
  products_simulation Ps1 Ps2 ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs fptr = Some f ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs fptr = Some f.
Proof.
  unfold OpsemAux.lookupExFdecViaPtr.
  intros. 
  destruct (OpsemAux.lookupFdefViaGVFromFunTable fs fptr); tinv H0.
  simpl in H0. simpl.
  remember (lookupFdefViaIDFromProducts Ps2 i0) as R.
  destruct R; tinv H0.
  erewrite products_simulation__fdef_None_r2l; eauto.
  erewrite products_simulation__fdec_r2l; eauto.
Qed.

End TopSim.

End TopSim.
