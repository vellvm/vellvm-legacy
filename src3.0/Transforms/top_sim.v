Require Import vellvm.
Require Import genericvalues_inject.
Require Import palloca_props.
Require Import primitives.

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

Module RemoveSim.

Section RemoveSim.

Variable (F0:fdef) (ID0:id).

Definition fdef_simulation f1 f2 : Prop :=
  if (fdef_dec F0 f1) then
    remove_fdef ID0 f1 = f2
  else f1 = f2.

Definition cmds_simulation f1 cs1 cs2 : Prop :=
  if (fdef_dec F0 f1) then
    remove_cmds ID0 cs1 = cs2
  else cs1 = cs2.

Definition block_simulation f1 b1 b2 : Prop :=
  if (fdef_dec F0 f1) then
    remove_block ID0 b1 = b2
  else b1 = b2.

Lemma fdef_simulation__eq_fheader: forall f1 f2
  (H: fdef_simulation f1 f2),
  fheaderOfFdef f1 = fheaderOfFdef f2.
Proof.
  unfold fdef_simulation.
  intros.
  destruct (fdef_dec F0 f1); inv H; auto.
    destruct f1 as [fh b]; simpl; auto.
Qed.

Lemma fdef_simulation__det_right: forall f1 f2 f2',
  fdef_simulation f1 f2 ->
  fdef_simulation f1 f2' ->
  f2 = f2'.
Proof.
  unfold fdef_simulation.
  intros.
  destruct_if; congruence.
Qed.

Lemma cmds_simulation_elim_cons_inv: forall c (cs1 : list cmd)
  (cs2 : cmds) (Heq : ID0 = getCmdLoc c)
  (Hcssim2 : cmds_simulation F0 (c :: cs1) cs2),
  cmds_simulation F0 cs1 cs2.
Proof.
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec F0 F0); try congruence.
  simpl in *. rewrite Heq in Hcssim2.
  destruct (id_dec (getCmdLoc c) (getCmdLoc c)); simpl in *; try congruence.
Qed.

Lemma cmds_simulation_nil_inv: forall f1 cs,
  cmds_simulation f1 nil cs -> cs = nil.
Proof.
  unfold cmds_simulation. simpl.
  intros. destruct (fdef_dec F0 f1); auto.
Qed.

Lemma cmds_simulation_nelim_cons_inv: forall F c cs2 cs',
  cmds_simulation F (c :: cs2) cs' ->
  F0 <> F \/ ID0 <> getCmdLoc c ->
  exists cs2',
    cs' = c :: cs2' /\ cmds_simulation F cs2 cs2'.
Proof.
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec F0 F); subst; simpl; eauto.
  destruct (id_dec (getCmdLoc c) ID0); subst; simpl; eauto.
  destruct H0; congruence.
Qed.

Lemma cmds_simulation_nelim_cons_inv': forall F c cs2 cs',
  cmds_simulation F (c :: cs2) cs' ->
  (F0 = F -> getCmdLoc c <> ID0) ->
  exists cs2',
    cs' = c :: cs2' /\ cmds_simulation F cs2 cs2'.
Proof.
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec F0 F); subst; simpl; eauto.
  destruct (id_dec (getCmdLoc c) ID0); subst; simpl; eauto.
  assert (F=F) as EQ. auto.
  apply H0 in EQ. congruence.
Qed.

Lemma fdef_sim__block_sim : forall f1 f2 l0 b1 b2,
  fdef_simulation f1 f2 ->
  lookupBlockViaLabelFromFdef f1 l0 = Some b1 ->
  lookupBlockViaLabelFromFdef f2 l0 = Some b2 ->
  block_simulation f1 b1 b2.
Proof.
  intros.
  unfold fdef_simulation in H.
  unfold block_simulation.
  destruct (fdef_dec F0 f1); subst.
    destruct f1. simpl in *.
    eapply fdef_sim__lookupAL_genLabel2Block_remove_block; eauto.

    uniq_result. auto.
Qed.

Definition phis_simulation (f1:fdef) ps1 ps2 : Prop :=
  if (fdef_dec F0 f1) then remove_phinodes ID0 ps1 = ps2
  else ps1 = ps2.

Lemma block_simulation_inv : forall F l1 ps1 cs1 tmn1 l2 ps2 cs2
  tmn2,
  block_simulation F (block_intro l1 ps1 cs1 tmn1)
    (block_intro l2 ps2 cs2 tmn2) ->
  l1 = l2 /\ phis_simulation F ps1 ps2 /\
  cmds_simulation F cs1 cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold block_simulation, cmds_simulation, phis_simulation in *.
  destruct (fdef_dec F0 F); inv H; auto.
Qed.

Lemma fdef_simulation_inv: forall fh1 fh2 bs1 bs2,
  fdef_simulation (fdef_intro fh1 bs1) (fdef_intro fh2 bs2) ->
  fh1 = fh2 /\
  List.Forall2
    (fun b1 b2 => block_simulation (fdef_intro fh1 bs1) b1 b2) bs1 bs2.
Proof.
  intros.
  unfold fdef_simulation in H.
  unfold block_simulation.
  destruct (fdef_dec F0 (fdef_intro fh1 bs1)).
    simpl in H. clear e. inv H.
    split; auto.
      clear.
      induction bs1; simpl; constructor; auto.

    inv H.
    split; auto.
      clear.
      induction bs2; simpl; constructor; auto.
Qed.

Lemma getEntryBlock__simulation: forall f1 f2 b2,
  getEntryBlock f2 = Some b2 ->
  fdef_simulation f1 f2 ->
  exists b1, getEntryBlock f1 = Some b1 /\ 
    block_simulation f1 b1 b2.
Proof.
  unfold fdef_simulation.
  unfold block_simulation.
  intros.
  destruct (fdef_dec F0 f1); inv H0; eauto.
    remember f1 as R1.
    destruct R1 as [[? ? ? a ?] b]; simpl in *.
    destruct b; simpl in *; inv H.
    exists b. 
    split; auto.
Qed.

Lemma fdef_simulation__entry_block_simulation: forall F1 F2 B1 B2,
  fdef_simulation F1 F2 ->
  getEntryBlock F1 = ret B1 ->
  getEntryBlock F2 = ret B2 ->
  block_simulation F1 B1 B2.
Proof.
  intros.
  eapply getEntryBlock__simulation in H1; eauto.
  destruct H1 as [b1 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma block_simulation__getValueViaBlockFromValuels: forall F B1 B2 l0,
  block_simulation F B1 B2 ->
  getValueViaBlockFromValuels l0 B1 = getValueViaBlockFromValuels l0 B2.
Proof.
  destruct B1, B2; simpl; intros.
  unfold block_simulation in H.
  destruct (fdef_dec F0 F); subst.
    simpl in H. inv H. auto.
    inv H. auto.
Qed.

Lemma phis_simulation_inv: forall F ps1 ps2 l1 cs1 tmn1
  (HBinF: blockInFdefB (block_intro l1 ps1 cs1 tmn1) F = true)
  (Hnotin: F0 = F -> ~ In ID0 (getPhiNodesIDs ps1)),
  phis_simulation F ps1 ps2 -> ps1 = ps2.
Proof.
  unfold phis_simulation.
  intros.
  destruct (fdef_dec F0 F); subst; auto.
  apply remove_phinodes_stable; auto.
Qed.

Definition removable_State (St:@Opsem.State DGVs) : Prop :=
match St with
| Opsem.mkState
    (Opsem.mkEC f b (c :: cs) tmn lc als::_) _ =>
    if (fdef_dec F0 f) then
      if (id_dec ID0 (getCmdLoc c)) then True else False
    else False
| _ => False
end.

Lemma removable_State_dec : forall St,
  removable_State St \/ ~ removable_State St.
Proof.
  destruct St.
  destruct ECS as [|[]]; auto.
  destruct CurCmds; auto.
  simpl.
  destruct (fdef_dec F0 CurFunction); auto.
  destruct (id_dec ID0 (getCmdLoc c)); auto.
Qed.

Lemma not_removable_State_inv: forall St,
  ~ removable_State St ->
  match St with
  | {| Opsem.ECS := {| Opsem.CurFunction := F;
                       Opsem.CurBB := _;
                       Opsem.CurCmds := c :: _;
                       Opsem.Terminator := _;
                       Opsem.Locals := _;
                       Opsem.Allocas := _ |} :: _;
       Opsem.Mem := Mem |} => F0 <> F \/ ID0 <> getCmdLoc c
  | _ => True
  end.
Proof.
  intros.
  destruct St; auto.
  destruct ECS; auto.
  destruct e; auto.
  destruct CurCmds; auto.
  simpl in H.
  destruct (fdef_dec F0 CurFunction); subst; auto.
  destruct (id_dec ID0 (getCmdLoc c)); subst; auto.
Qed.

Lemma removable_State__non_removable_State: forall f b c cs1 tmn lc als
  ES1 lc' als' Mem Mem' (Hnodup: NoDup (getCmdsLocs (c::cs1)))
  (Hrem : removable_State
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f;
                        Opsem.CurBB := b;
                        Opsem.CurCmds := c :: cs1;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: ES1;
           Opsem.Mem := Mem |}),
  ~ removable_State
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f;
                        Opsem.CurBB := b;
                        Opsem.CurCmds := cs1;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc';
                        Opsem.Allocas := als' |} :: ES1;
           Opsem.Mem := Mem' |}.
Proof.
  simpl. intros.
  destruct_if; auto.
  destruct_if; auto.
  destruct cs1; auto.
  destruct_if; auto.
  inv Hnodup. inv H2. intro J. apply H1. simpl. left. congruence.
Qed.

Lemma removable_State__isnt__final: forall cfg St
  (Hrm: removable_State St),
  Opsem.s_isFinialState cfg St = None.
Proof.
  intros.
  destruct St as [Es Mem].
  destruct cfg.
  destruct Es as [|[] Es]; tinv Hrm.
  simpl in *.
  destruct CurCmds; tauto.
Qed.

Lemma removable_State_inv: forall F b c cs tmn lc als ECs Mem,
  removable_State
    {| Opsem.ECS := {| Opsem.CurFunction := F;
                       Opsem.CurBB := b;
                       Opsem.CurCmds := c :: cs;
                       Opsem.Terminator := tmn;
                       Opsem.Locals := lc;
                       Opsem.Allocas := als |} :: ECs;
       Opsem.Mem := Mem |} ->
  F0 = F /\ ID0 = getCmdLoc c.
Proof.
  simpl.
  intros.
  destruct_if.
  destruct_if. auto.
Qed.

Lemma cmds_simulation_nil_inv' : forall
  (f1 : fdef) (cs1 : list cmd) b1 tmn1 lc1 als1 ECS Mem1
  (Hnrem : ~
          removable_State
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := f1;
                         Opsem.CurBB := b1;
                         Opsem.CurCmds := cs1;
                         Opsem.Terminator := tmn1;
                         Opsem.Locals := lc1;
                         Opsem.Allocas := als1 |} :: ECS;
            Opsem.Mem := Mem1 |}),
  cmds_simulation f1 cs1 nil -> cs1 = nil.
Proof.
  simpl.
  unfold cmds_simulation. intros.
  destruct_if; auto.
  destruct cs1; auto.
  destruct_if; try tauto.
  simpl in H1.
  destruct (id_dec (getCmdLoc c) ID0); simpl in *; congruence.
Qed.

Lemma cmds_simulation_cons_inv' : forall 
  (f1 : fdef) b1 lc1 cs tmn1 als1 c cs2 ECS Mem1
  (Hnrem : ~
          removable_State
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := f1;
                         Opsem.CurBB := b1;
                         Opsem.CurCmds := cs;
                         Opsem.Terminator := tmn1;
                         Opsem.Locals := lc1;
                         Opsem.Allocas := als1 |} :: ECS;
            Opsem.Mem := Mem1 |}),
  cmds_simulation f1 cs (c::cs2) -> 
   exists cs1, 
     cs = c::cs1 /\
     cmds_simulation f1 cs1 cs2.
Proof.
  simpl.
  unfold cmds_simulation. intros.
  destruct_if; eauto.
  destruct cs; inv H1.
  destruct (id_dec ID0 (getCmdLoc c0)); try tauto.
  destruct (id_dec (getCmdLoc c0) ID0); simpl in *; try congruence.
  inv H0. eauto.
Qed.

End RemoveSim.

End RemoveSim.

Hint Unfold RemoveSim.fdef_simulation RemoveSim.cmds_simulation 
  RemoveSim.block_simulation RemoveSim.phis_simulation
  RemoveSim.removable_State.

