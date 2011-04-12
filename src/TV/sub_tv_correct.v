Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import opsem_pp.
Require Import trace.
Require Import symexe_def.
Require Import symexe_lib.
Require Import symexe_complete.
Require Import symexe_sound.
Require Import seop_llvmop.
Require Import assoclist.
Require Import ssa_props.
Require Import sub_tv_dec.
Require Import sub_tv_infer.
Require Import sub_tv.
Require Import Coq.Bool.Sumbool.
Require Import symexe_tactic.

Export SimpleSE.

(* subAL *)

Definition subAL X lc1 lc2 := 
  forall i, i `in` dom lc1 -> lookupAL X lc1 i = lookupAL X lc2 i.

Notation "lc1 <<<= lc2" := (subAL _ lc1 lc2) (at level 70, no associativity).

Lemma lookupAL_app1 : forall X (lc1:list (atom*X)) lc2 i,
  i `in` dom lc1 ->
  lookupAL X lc1 i = lookupAL X (lc1++lc2) i.
Proof.
  induction lc1; intros lc2 i Hi_in_lc1.
    fsetdec.
    destruct a as (id, elt); simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i id); auto.
      apply IHlc1. fsetdec.
Qed.    

Lemma lookupAL_app2 : forall X lc1 (lc2:list (atom*X)) i,
  i `notin` dom lc1 ->
  lookupAL X lc2 i = lookupAL X (lc1++lc2) i.
Proof.
  induction lc1; intros lc2 i Hi_notin_lc1; auto.
    destruct a as (id, elt); simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i id); subst; eauto.
      fsetdec.
Qed.    

Lemma subAL_app1 : forall X (lc1:list (atom*X)) lc2 lc,
  lc1 <<<= lc ->
  lc2 <<<= lc ->
  lc1 ++ lc2 <<<= lc.
Proof.
  intros X lc1 lc2 lc Hlc1_sub_lc Hlc2_sub_lc.
  intros i i_in_lc12.
  simpl_env in i_in_lc12.
  apply in_dom_app_inv in i_in_lc12.
  assert (i `in`  dom lc1 \/ i `notin` dom lc1) as i_in_lc1_dec. fsetdec.
  destruct i_in_lc1_dec as [i_in_lc1 | i_notin_lc1].
    rewrite <- Hlc1_sub_lc; auto.
    rewrite <- lookupAL_app1; auto.

    destruct i_in_lc12 as [i_in_lc1 | i_in_lc2].
      fsetdec.
      rewrite <- lookupAL_app2; auto.
Qed.

Lemma lookupALs_tail : forall X l2b l2b' l0,
  l0 `notin` dom l2b ->
  lookupAL X (l2b++l2b') l0 = lookupAL _ l2b' l0.
Proof.
  intros.
  induction l2b; auto.
    destruct a. simpl in *.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l0 a); subst; auto.
      fsetdec.
Qed.

Lemma subAL_app2 : forall X (lc1:list (atom*X)) lc2 lc,
  lc1 <<<= lc ->
  disjoint lc1 lc2 ->
  ~ lc2 <<<= lc ->
  ~ lc1 ++ lc2 <<<= lc.
Proof.
  intros X lc1 lc2 lc Hlc1_sub_lc Hdisj Hlc2_nsub_lc Hlc12_sub_lc.
  apply Hlc2_nsub_lc.
  intros i i_in_lc2.
    assert (i `notin` dom lc1) as i_notin_lc1. solve_uniq.
    assert (i `in` dom (lc1++lc2)) as i_in_lc12. simpl_env. fsetdec.
    apply Hlc12_sub_lc in i_in_lc12.
    erewrite lookupALs_tail in i_in_lc12; eauto.
Qed.
    
(* subAL *)

Lemma getOperandValue_subAL : forall lc1 gl lc2 v TD gv,
  subAL _ lc1 lc2 ->
  getOperandValue TD v lc1 gl = Some gv ->
  getOperandValue TD v lc1 gl = getOperandValue TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD gv Hnon_none HeqAL.
  unfold getOperandValue in *.
  destruct v; auto.
    apply lookupAL_Some_indom in HeqAL. eauto.
Qed.

Lemma subAL_updateAddAL : forall X lc1 lc2 id0 gv0,
  subAL X lc1 lc2 ->
  subAL _ (updateAddAL _ lc1 id0 gv0) (updateAddAL _ lc2 id0 gv0).
Proof.
  unfold subAL. 
  intros.
  rewrite updateAddAL_dom_eq in H0.
  destruct (id0==i0); subst.
    rewrite lookupAL_updateAddAL_eq; auto.
    rewrite lookupAL_updateAddAL_eq; auto.

    assert (i0 `in` dom lc1) as Hi0_in_lc1. fsetdec.
    assert (J:=H i0 Hi0_in_lc1).
    erewrite <- lookupAL_updateAddAL_neq; eauto.
    erewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma subAL_callUpdateLocals : forall TD noret0 rid rt oResult lc1 lc2 gl lc1' lc2',
  subAL _ lc1 lc1' ->
  subAL _ lc2 lc2' ->
  subAL _ (callUpdateLocals TD noret0 rid rt oResult lc1 lc2 gl)
         (callUpdateLocals TD noret0 rid rt oResult lc1' lc2' gl).
Proof.
  intros TD noret0 rid rt oResult lc1 lc2 gl lc1' lc2' H1 H2.
    unfold callUpdateLocals.
    destruct noret0; auto.
      destruct (rt=t=typ_void); auto.
        destruct oResult; simpl; auto.
          destruct v; simpl.
            remember (lookupAL _ lc2 i0) as Lookup.
            destruct Lookup as [gr | _].
              rewrite H2 in HeqLookup; eauto using lookupAL_Some_indom.
              rewrite <- HeqLookup. apply subAL_updateAddAL; auto.

              (* We should prove that if oResult is Some, i0 in lc2. *)
              admit.

          destruct (const2GV TD gl c); auto using subAL_updateAddAL.
Qed.

Lemma subAL_refl : forall X lc,
  subAL X lc lc.
Proof. unfold subAL. auto. Qed.

Lemma subAL_getIncomingValuesForBlockFromPHINodes : forall TD ps B gl lc lc',
  subAL _ lc lc' ->
  getIncomingValuesForBlockFromPHINodes TD ps B gl lc =
  getIncomingValuesForBlockFromPHINodes TD ps B gl lc'.
Proof.
  induction ps; intros; simpl; auto.
    destruct a; auto.
    destruct (getValueViaBlockFromValuels l0 B); auto.
    destruct v; erewrite IHps; eauto.
      (* We should redefine getIncomingValuesForBlockFromPHINodes to be partial. 
         If we cannot find any incoming value, we should return None. *)
      assert (i1 `in` dom lc) as J. admit. 
      rewrite H; auto.
Qed.

Lemma subAL_updateValuesForNewBlock : forall vs lc lc',
  subAL _ lc lc' ->
  subAL _ (updateValuesForNewBlock vs lc) (updateValuesForNewBlock vs lc').
Proof.
  induction vs; intros; simpl; auto.
    destruct a.
    destruct o; auto using subAL_updateAddAL.
Qed.

Lemma subAL_switchToNewBasicBlock : forall TD B1 B2 gl lc lc',
  subAL _ lc lc' ->
  subAL _ (switchToNewBasicBlock TD B1 B2 gl lc) (switchToNewBasicBlock TD B1 B2 gl lc').
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite subAL_getIncomingValuesForBlockFromPHINodes; eauto.
  apply subAL_updateValuesForNewBlock; auto.
Qed.

Lemma subAL_exCallUpdateLocals : forall noret0 rid rt oResult lc lc',
  subAL _ lc lc' ->
  subAL _ (exCallUpdateLocals noret0 rid rt oResult lc)
         (exCallUpdateLocals noret0 rid rt oResult lc').
Proof.
  intros noret0 rid rt oResult lc lc' H1.
    unfold exCallUpdateLocals.
    destruct noret0; auto.
      destruct (rt=t=typ_void); auto.
        destruct oResult; simpl; auto using subAL_updateAddAL.
Qed.

Lemma subAL_lookupExFdecViaGV : forall gl TD Ps lc lc' fs fv gv,
  subAL _ lc lc' ->
  lookupExFdecViaGV TD Ps gl lc fs fv = Some gv ->
  lookupExFdecViaGV TD Ps gl lc fs fv = lookupExFdecViaGV TD Ps gl lc' fs fv.
Proof.
  intros.
  unfold lookupExFdecViaGV in *.
  assert (exists gv, getOperandValue TD fv lc gl = Some gv) as J.
    destruct (getOperandValue TD fv lc gl); eauto.
      inversion H0.
  destruct J as [gv' J].
  erewrite getOperandValue_subAL; eauto.
Qed.

Lemma subAL_lookupExFdefViaGV : forall gl TD Ps lc lc' fs fv gv,
  subAL _ lc lc' ->
  lookupFdefViaGV TD Ps gl lc fs fv = Some gv ->
  lookupFdefViaGV TD Ps gl lc fs fv = lookupFdefViaGV TD Ps gl lc' fs fv.
Proof.
  intros.
  unfold lookupFdefViaGV in *.
  assert (exists gv, getOperandValue TD fv lc gl = Some gv) as J.
    destruct (getOperandValue TD fv lc gl); eauto.
      inversion H0.
  destruct J as [gv' J].
  erewrite getOperandValue_subAL; eauto.
Qed.

Lemma subAL_params2OpGVs : forall lp TD lc gl lc',
  subAL _ lc lc' ->
  params2OpGVs TD lp lc gl = params2OpGVs TD lp lc' gl.
Proof.
  induction lp; intros; simpl; auto.
    destruct a.
    destruct v; simpl.
      (* We should redefine params2OpGVs to be partial. 
         If we cannot find any param value, we should return None. *)
      assert (i0 `in` dom lc) as J. admit. 
      rewrite H; auto. erewrite IHlp; eauto.
      erewrite IHlp; eauto.
Qed.

Lemma subAL_params2GVs : forall lp TD lc gl lc',
  subAL _ lc lc' ->
  params2GVs TD lp lc gl = params2GVs TD lp lc' gl.
Proof.
  induction lp; intros; simpl; auto.
    destruct a.
    unfold params2GVs.
    erewrite subAL_params2OpGVs; eauto.
Qed.

Lemma subAL_initLocals : forall la lp TD lc gl lc',
  subAL _ lc lc' ->
  subAL _ (initLocals la (params2GVs TD lp lc gl)) (initLocals la (params2GVs TD lp lc' gl)).
Proof.
  intros. erewrite subAL_params2GVs; eauto using subAL_refl.
  (* This lemma will be broken if we fix subAL_params2GVs 
     The problem is that the Fdef rule should check that params2GVs lp = Some ... *)
Qed.

Lemma BOP_subAL : forall lc1 gl lc2 bop0 sz0 v1 v2 TD gv,
  subAL _ lc1 lc2 ->
  BOP TD lc1 gl bop0 sz0 v1 v2 = Some gv ->
  BOP TD lc1 gl bop0 sz0 v1 v2 = BOP TD lc2 gl bop0 sz0 v1 v2.
Proof.
  intros lc1 gl lc2 bop0 sz0 v1 v2 TD gv HsubEnv Hsome.
  apply BOP_inversion in Hsome.
  destruct Hsome as [gv1 [gv2 [Hsome1 [Hsome2 _]]]].
  unfold BOP in *.
  erewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1); eauto.
  erewrite getOperandValue_subAL with (lc2:=lc2)(v:=v2); eauto.
Qed.

Lemma FBOP_subAL : forall lc1 gl lc2 fbop0 fp0 v1 v2 TD gv,
  subAL _ lc1 lc2 ->
  FBOP TD lc1 gl fbop0 fp0 v1 v2 = Some gv ->
  FBOP TD lc1 gl fbop0 fp0 v1 v2 = FBOP TD lc2 gl fbop0 fp0 v1 v2.
Proof.
  intros lc1 gl lc2 fbop0 fp0 v1 v2 TD gv HsubEnv Hsome.
  apply FBOP_inversion in Hsome.
  destruct Hsome as [gv1 [gv2 [Hsome1 [Hsome2 _]]]].
  unfold FBOP in *.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1)(gv:=gv1); auto.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v2)(gv:=gv2); auto.
Qed.

Lemma getOperandPtr_subAL : forall lc1 gl lc2 v TD gv,
  subAL _ lc1 lc2 ->
  getOperandPtr TD v lc1 gl = Some gv ->
  getOperandPtr TD v lc1 gl = getOperandPtr TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD gv HsubEnv Hsome.
  apply getOperandPtr_inversion in Hsome.
  destruct Hsome as [gv0 [Hsome _]].
  unfold getOperandPtr in *.
  erewrite getOperandValue_subAL; eauto.
Qed.

Lemma getOperandInt_subAL : forall lc1 gl lc2 sz v TD gv,
  subAL _ lc1 lc2 ->
  getOperandInt TD sz v lc1 gl = Some gv ->
  getOperandInt TD sz v lc1 gl = getOperandInt TD sz v lc2 gl.
Proof.
  intros lc1 gl lc2 sz0 v TD gv HsubAL Hsome.
  apply getOperandInt_inversion in Hsome.
  destruct Hsome as [gv0 [Hsome _]].
  unfold getOperandInt in *.
  erewrite getOperandValue_subAL; eauto.
Qed.

Lemma getOperandPtrInBits_subAL : forall lc1 gl lc2 sz v TD gv,
  subAL _ lc1 lc2 ->
  getOperandValue TD v lc1 gl = Some gv ->
  getOperandPtrInBits TD sz v lc1 gl = getOperandPtrInBits TD sz v lc2 gl.
Proof.
  intros lc1 gl lc2 sz0 v TD gv HsubAL Hsome.
  unfold getOperandPtrInBits in *.
  erewrite getOperandValue_subAL; eauto.
Qed.

Lemma CAST_subAL : forall lc1 gl lc2 op t1 v1 t2 TD gv,
  subAL _ lc1 lc2 ->
  CAST TD lc1 gl op t1 v1 t2 = Some gv ->
  CAST TD lc1 gl op t1 v1 t2 = CAST TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD gv HsubAL Hsome.
  apply CAST_inversion in Hsome.
  destruct Hsome as [gv1 [Hsome _]].
  unfold CAST in *.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1)(gv:=gv1); auto.
Qed.

Lemma TRUNC_subAL : forall lc1 gl lc2 op t1 v1 t2 TD gv,
  subAL _ lc1 lc2 ->
  TRUNC TD lc1 gl op t1 v1 t2 = Some gv ->
  TRUNC TD lc1 gl op t1 v1 t2 = TRUNC TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD gv HsubAL Hsome.
  apply TRUNC_inversion in Hsome.
  destruct Hsome as [gv1 [Hsome _]].
  unfold TRUNC in *.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1)(gv:=gv1); auto.
Qed.

Lemma EXT_subAL : forall lc1 gl lc2 op t1 v1 t2 TD gv,
  subAL _ lc1 lc2 ->
  EXT TD lc1 gl op t1 v1 t2 = Some gv ->
  EXT TD lc1 gl op t1 v1 t2 = EXT TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD gv HsubAL Hsome.
  apply EXT_inversion in Hsome.
  destruct Hsome as [gv1 [Hsome _]].
  unfold EXT in *.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1)(gv:=gv1); auto.
Qed.

Lemma ICMP_subAL : forall lc1 gl lc2 cond t v1 v2 TD gv,
  subAL _ lc1 lc2 ->
  ICMP TD lc1 gl cond t v1 v2 = Some gv ->
  ICMP TD lc1 gl cond t v1 v2 = ICMP TD lc2 gl cond t v1 v2.
Proof.
  intros lc1 gl lc2 cond0 t v1 v2 TD gv HsubAL Hsome.
  apply ICMP_inversion in Hsome.
  destruct Hsome as [gv1 [gv2 [Hsome1 [Hsome2 _]]]].
  unfold ICMP in *.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1)(gv:=gv1); auto.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v2)(gv:=gv2); auto.
Qed.

Lemma FCMP_subAL : forall lc1 gl lc2 cond fp v1 v2 TD gv,
  subAL _ lc1 lc2 ->
  FCMP TD lc1 gl cond fp v1 v2 = Some gv ->
  FCMP TD lc1 gl cond fp v1 v2 = FCMP TD lc2 gl cond fp v1 v2.
Proof.
  intros lc1 gl lc2 cond0 fp v1 v2 TD gv HsubAL Hsome.
  apply FCMP_inversion in Hsome.
  destruct Hsome as [gv1 [gv2 [Hsome1 [Hsome2 _]]]].
  unfold FCMP in *.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1)(gv:=gv1); auto.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v2)(gv:=gv2); auto.
Qed.

Lemma intValues2Nats_subAL : forall l0 lc1 gl lc2 TD zs,
  subAL _ lc1 lc2 ->
  intValues2Nats TD l0 lc1 gl = Some zs ->
  intValues2Nats TD l0 lc1 gl = intValues2Nats TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD zs HsubAL Hsome; simpl in *; auto.
    assert (exists gv, getOperandValue TD v lc1 gl = Some gv) as J.
      destruct (getOperandValue TD v lc1 gl); eauto.
        inversion Hsome.
    destruct J as [gv J].
    erewrite getOperandValue_subAL with (lc2:=lc2)(v:=v); eauto.
      rewrite J in Hsome.
      destruct (GV2int TD Size.ThirtyTwo gv); try solve [inversion Hsome].
      assert (exists zs', intValues2Nats TD l0 lc1 gl = Some zs') as J'.
        destruct (intValues2Nats TD l0 lc1 gl); eauto.
      destruct J' as [gv' J'].
      erewrite IHl0; eauto.
Qed.

Lemma values2GVs_subAL : forall l0 lc1 gl lc2 TD gvs,
  subAL _ lc1 lc2 ->
  values2GVs TD l0 lc1 gl = Some gvs ->
  values2GVs TD l0 lc1 gl = values2GVs TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD gvs HsubAL Hsome; simpl in *; auto.
    assert (exists gv, getOperandValue TD v lc1 gl = Some gv) as J.
      destruct (getOperandValue TD v lc1 gl); eauto.
        inversion Hsome.
    destruct J as [gv J].
    erewrite getOperandValue_subAL with (lc2:=lc2)(v:=v); eauto.
      rewrite J in Hsome.
      assert (exists gvs', values2GVs TD l0 lc1 gl = Some gvs') as J'.
        destruct (values2GVs TD l0 lc1 gl); eauto.
      destruct J' as [gvs' J'].
      erewrite IHl0; eauto.
Qed.

(* subEnv *)

Lemma dbCmd_subEnv : forall TD c lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1',
  dbCmd TD gl lc1 als1 Mem1 c lc2 als2 Mem2 tr ->
  subAL _ lc1 lc1' ->
  exists lc2', 
    dbCmd TD gl lc1' als1 Mem1 c lc2' als2 Mem2 tr /\
    subAL _ lc2 lc2'.
Proof.
  intros TD c lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1' HdbCmd HsubEnv.
  (dbCmd_cases (inversion HdbCmd) Case); subst.
Case "dbBop".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  erewrite BOP_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbFBop".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  erewrite FBOP_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbExtractValue".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv').
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 
  split; eauto using subAL_updateAddAL.
  
Case "dbInsertValue".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv'').
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 
  erewrite getOperandValue_subAL with (lc2:=lc1') in H0; eauto. 
  split; eauto using subAL_updateAddAL.

Case "dbMalloc".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 (blk2GV TD mb)).
  erewrite getOperandValue_subAL with (lc2:=lc1') in H0; eauto. 
  split; eauto using subAL_updateAddAL.

Case "dbFree".
  exists lc1'.
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 

Case "dbAlloca".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 (blk2GV TD mb)).
  erewrite getOperandValue_subAL with (lc2:=lc1') in H0; eauto. 
  split; eauto using subAL_updateAddAL.

Case "dbLoad".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv).
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 
  split; eauto using subAL_updateAddAL.

Case "dbStore".
  exists lc1'.
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 
  erewrite getOperandValue_subAL with (lc2:=lc1') in H0; eauto. 

Case "dbGEP".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 mp').
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 
  erewrite values2GVs_subAL with (lc2:=lc1') in H0; eauto. 
(* rewrite GEP_eqAL with (lc2:=lc1') in H0; auto. *)
  split; eauto using subAL_updateAddAL.

Case "dbTrunc".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  erewrite TRUNC_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbExt".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  erewrite EXT_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbCast".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  erewrite CAST_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbIcmp".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  erewrite ICMP_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbFcmp".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  erewrite FCMP_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbSelect".
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 
  erewrite getOperandValue_subAL with (lc2:=lc1') in H0; eauto. 
  erewrite getOperandValue_subAL with (lc2:=lc1') in H1; eauto. 
  assert (HupdateEnv:=HsubEnv).
  exists (if isGVZero TD cond0 then updateAddAL _ lc1' id0 gv2 else updateAddAL _ lc1' id0 gv1).
  split; auto.
    destruct (isGVZero TD cond0); auto using subAL_updateAddAL.

Case "dbLib".
  admit.
Qed.

Lemma dbCmds_subEnv : forall TD cs lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1',
  dbCmds TD gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr ->
  subAL _ lc1 lc1' ->
  exists lc2', 
    dbCmds TD gl lc1' als1 Mem1 cs lc2' als2 Mem2 tr /\
    subAL _ lc2 lc2'.
Proof.
  intros TD cs lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1' HdbCmds HsubEnv.
  generalize dependent lc1'.
  induction HdbCmds; intros.
    exists lc1'. split; auto.

    apply dbCmd_subEnv with (lc1':=lc1') in H; auto.
    destruct H as [lc2' [HdbCmd HsubEnv']].
    apply IHHdbCmds in HsubEnv'; auto.
    destruct HsubEnv' as [lc3' [HdbCmds' HsubEnv'']].
    exists lc3'.
    split; eauto.
Qed.

Lemma dbTerminator_subEnv : forall TD F gl lc1 tmn lc2 tr lc1' B B',
  dbTerminator TD F gl B lc1 tmn B' lc2 tr ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbTerminator TD F gl B lc1' tmn B' lc2' tr /\
    subAL _ lc2 lc2'.
Proof.
  intros TD F gl lc1 tmn lc2 tr lc1' B B' HdbTerminator HsubAL.
  inversion HdbTerminator; subst.
    exists (switchToNewBasicBlock TD (block_intro l' ps' sbs' tmn') B gl lc1').
    split.
      apply dbBranch with (c:=c); auto.
        erewrite <- getOperandValue_subAL; eauto.
      apply subAL_switchToNewBasicBlock; auto.     
  
    exists (switchToNewBasicBlock TD (block_intro l' ps' sbs' tmn') B gl lc1').
    split.
      apply dbBranch_uncond; auto.
      apply subAL_switchToNewBasicBlock; auto.
Qed.     

Definition dbCall_subEnv_prop S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr
  (db:dbCall S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr) := 
  forall lc1',
  subAL _ lc1 lc1' ->
  exists lc2',
    dbCall S TD Ps fs gl lc1' Mem0 call0 lc2' Mem' tr /\
    subAL _ lc2 lc2'.
Definition dbSubblock_subEnv_prop S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr
  (db:dbSubblock S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr) :=
  forall lc1',
  subAL _ lc1 lc1' ->
  exists lc2',
    dbSubblock S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    subAL _ lc2 lc2'.
Definition dbSubblocks_subEnv_prop S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr
  (db:dbSubblocks S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr) :=
  forall lc1',
  subAL _ lc1 lc1' ->
  exists lc2',
    dbSubblocks S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    subAL _ lc2 lc2'.
Definition dbBlock_subEnv_prop S TD Ps fs gl F arg state1 state2 tr
  (db:dbBlock S TD Ps fs gl F arg state1 state2 tr) :=
  forall B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  state1 = mkState (mkEC B1 lc1 als) Mem ->
  state2 = mkState (mkEC B1' lc2 als') Mem' ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbBlock S TD Ps fs gl F arg 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    subAL _ lc2 lc2'.
Definition dbBlocks_subEnv_prop S TD Ps fs gl F lp state1 state2 tr
  (db:dbBlocks S TD Ps fs gl F lp state1 state2 tr) :=
  forall B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  state1 = mkState (mkEC B1 lc1 als) Mem ->
  state2 = mkState (mkEC B1' lc2 als') Mem' ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbBlocks S TD Ps fs gl F lp 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    subAL _ lc2 lc2'.
Definition dbFdef_subEnv_prop fv rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr
  (db:dbFdef fv rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr) :=
  forall fid la lb lc1',
  lookupFdefViaGV TD Ps gl lc1 fs fv = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbFdef fv rt lp S TD Ps lc1' gl fs Mem lc2' als' Mem' B' Rid oResult tr /\
    subAL _ lc2 lc2'.

Lemma db_subEnv :
  (forall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db, 
     dbCall_subEnv_prop S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db,
     dbSubblock_subEnv_prop S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db,
     dbSubblocks_subEnv_prop S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl F arg state1 state2 tr db,
     dbBlock_subEnv_prop S TD Ps fs gl F arg state1 state2 tr db) /\
  (forall S TD Ps fs gl F lp state1 state2 tr db,
     dbBlocks_subEnv_prop S TD Ps fs gl F lp state1 state2 tr db) /\
  (forall fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db,
     dbFdef_subEnv_prop fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db).
Proof.
(db_mutind_cases
  apply db_mutind with
    (P  := dbCall_subEnv_prop)
    (P0 := dbSubblock_subEnv_prop)
    (P1 := dbSubblocks_subEnv_prop)
    (P2 := dbBlock_subEnv_prop)
    (P3 := dbBlocks_subEnv_prop)
    (P4 := dbFdef_subEnv_prop) Case);
  unfold dbCall_subEnv_prop, 
         dbSubblock_subEnv_prop, dbSubblocks_subEnv_prop,
         dbBlock_subEnv_prop, dbBlocks_subEnv_prop,
         dbFdef_subEnv_prop; intros; subst; auto.
Case "dbCall_internal".
  inversion d; subst.
    apply H with (lc1':=lc1') in H1; auto. clear H.
    destruct H1 as [lc2' [HdbBlocks HeqEnv]].
    exists (callUpdateLocals TD noret0 rid rt (Some Result) lc1' lc2' gl).
    split; eauto using dbCall_internal, subAL_callUpdateLocals.

    apply H with (lc1':=lc1') in H1; auto. clear H.
    destruct H1 as [lc2' [HdbBlocks HeqEnv]].
    exists (callUpdateLocals TD noret0 rid rt None lc1' lc2' gl).
    split; eauto using dbCall_internal, subAL_callUpdateLocals.

Case "dbCall_external".
  exists (exCallUpdateLocals noret0 rid rt oresult lc1').
  split; eauto using subAL_exCallUpdateLocals.
    eapply dbCall_external; eauto.
      erewrite <- subAL_lookupExFdecViaGV; eauto.
    rewrite <- subAL_params2GVs with (lc:=lc); auto.

Case "dbSubblock_intro".
  apply dbCmds_subEnv with (lc1':=lc1') in d; auto.
  destruct d as [lc2' [HdbCmds HsubEnv2]].
  apply H in HsubEnv2. clear H.
  destruct HsubEnv2 as [lc3' [HdbCall HsubEnv3]].
  exists lc3'.
  split; eauto.

Case "dbSubblocks_nil".
  exists lc1'. split; auto.
 
Case "dbSubblocks_cons".
  apply H in H1. clear H.
  destruct H1 as [lc2' [HdbSubblock Heq2]].
  apply H0 in Heq2. clear H0.
  destruct Heq2 as [lc3' [HdbSubblocks Heq3]].
  exists lc3'. split; eauto.

Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  apply H in H2. clear H.
  destruct H2 as [lc2' [HdbSubblocks Heq2]].
  apply dbCmds_subEnv with (lc1':=lc2') in d0; auto.
  destruct d0 as [lc3' [HdbCmds Heq3]].
  apply dbTerminator_subEnv with (lc1':=lc3') in d1; auto.
  destruct d1 as [lc5' [HdbTerminator Heq5]].
  exists lc5'. split; eauto.

Case "dbBlocks_nil".
  inversion H0; subst. clear H0.
  exists lc1'. split; auto.
 
Case "dbBlocks_cons".
  inversion d; subst.
  apply H with (B1:=block_intro l0 ps (cs++cs') tmn)(als0:=als)(Mem:=Mem0) 
               (B1':=B')(als':=als3)(Mem':=Mem3)(lc3:=lc5) in H3; auto.
  clear H.
  destruct H3 as [lc5' [HdbBlock Heq5]].
  apply H0 with (als'0:=als')(als:=als3)(Mem:=Mem3)(Mem'0:=Mem')(lc3:=lc2)(B1:=B')(B1'0:=B1') in Heq5; auto.
  clear H0.
  destruct Heq5 as [lc2' [HdbBlocks Heq2]].
  exists lc2'. split; eauto.

Case "dbFdef_func".
  rewrite e in H1. inversion H1; subst. clear H1.
  assert (J:=@subAL_initLocals la0 lp TD lc gl lc1' H2).
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(als:=nil)(Mem:=Mem0)(lc3:=lc1)
               (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result))(als':=als1)(Mem':=Mem1) in J; auto.
  clear H. destruct J as [lc2' [HdbBlocks Hsub2]].
  rewrite subAL_params2GVs with (lc':=lc1') in HdbBlocks; eauto.
  apply H0 in Hsub2. clear H0.
  destruct Hsub2 as [lc3' [Hsubblocks Hsub3]].
  apply dbCmds_subEnv with (lc1':=lc3') in d1; auto.
  destruct d1 as [lc4' [HdbCmds Hsub4]].
  exists lc4'. split; eauto.
    eapply dbFdef_func; eauto.
      erewrite <- subAL_lookupExFdefViaGV; eauto.

Case "dbFdef_proc".
  rewrite e in H1. inversion H1; subst. clear H1.
  assert (J:=@subAL_initLocals la0 lp TD lc gl lc1' H2).
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(als:=nil)(Mem:=Mem0)(lc3:=lc1)
               (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return_void rid))(als':=als1)(Mem':=Mem1) in J; auto.
  clear H. destruct J as [lc2' [HdbBlocks Hsub2]].
  rewrite subAL_params2GVs with (lc':=lc1') in HdbBlocks; eauto.
  apply H0 in Hsub2. clear H0.
  destruct Hsub2 as [lc3' [Hsubblocks Hsub3]].
  apply dbCmds_subEnv with (lc1':=lc3') in d1; auto.
  destruct d1 as [lc4' [HdbCmds Hsub4]].
  exists lc4'. split; eauto.
    eapply dbFdef_proc; eauto.
      erewrite <- subAL_lookupExFdefViaGV; eauto.
Qed.

Lemma dbCall_subEnv : forall S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr lc1',
  dbCall S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbCall S TD Ps fs gl lc1' Mem0 call0 lc2' Mem' tr /\
    subAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_subEnv as [J _].
  unfold dbCall_subEnv_prop in J. eauto.
Qed.

Lemma dbSubblock_subEnv : forall S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr lc1',
  dbSubblock S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbSubblock S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    subAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_subEnv as [_ [J _]].
  unfold dbSubblock_subEnv_prop in J. eauto.
Qed.

Lemma dbSubblocks_subEnv : forall S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr lc1',
  dbSubblocks S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbSubblocks S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    subAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_subEnv as [_ [_ [J _]]].
  unfold dbSubblocks_subEnv_prop in J. eauto.
Qed.

Lemma dbBlock_subEnv : forall S TD Ps fs gl F arg tr B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  dbBlock S TD Ps fs gl F arg 
    (mkState (mkEC B1 lc1 als) Mem) 
    (mkState (mkEC B1' lc2 als') Mem') 
    tr ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbBlock S TD Ps fs gl F arg 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    subAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_subEnv as [_ [_ [_ [J _]]]].
  unfold dbBlock_subEnv_prop in J. eauto.
Qed.

Lemma dbBlocks_subEnv : forall S TD Ps fs gl F lp tr B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  dbBlocks S TD Ps fs gl F lp
    (mkState (mkEC B1 lc1 als) Mem)
    (mkState (mkEC B1' lc2 als') Mem')
    tr ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbBlocks S TD Ps fs gl F lp 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    subAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_subEnv as [_ [_ [_ [_ [J _]]]]].
  unfold dbBlocks_subEnv_prop in J. eauto.
Qed.

Lemma dbFdef_subEnv : forall fv fid rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr la lb lc1',
  dbFdef fv rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr ->
  lookupFdefViaGV TD Ps gl lc1 fs fv = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbFdef fv rt lp S TD Ps lc1' gl fs Mem lc2' als' Mem' B' Rid oResult tr /\
    subAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_subEnv as [_ [_ [_ [_ [_ J]]]]].
  unfold dbFdef_subEnv_prop in J. eauto.
Qed.

Definition smap_sub_prop Ps1 Ps2 fid sm1 sm2 := 
  forall i st1,
    lookupAL _ sm1 i = Some st1 ->
    exists st2, lookupAL _ sm2 (rename_id fid i) = Some st2 /\ 
      tv_sterm Ps1 Ps2 fid st1 st2 = true.

Lemma smap_sub_prop_app1 : forall Ps1 Ps2 fid sm1 sm2 sm,
  smap_sub_prop Ps1 Ps2 fid sm1 sm ->
  smap_sub_prop Ps1 Ps2 fid sm2 sm ->
  smap_sub_prop Ps1 Ps2 fid (sm1 ++ sm2) sm.
Admitted.

Lemma smap_sub_prop_app3 : forall Ps1 Ps2 fid sm1 sm2 sm,
  smap_sub_prop Ps1 Ps2 fid (sm1 ++ sm2) sm ->
  smap_sub_prop Ps1 Ps2 fid sm1 sm ->
  disjoint sm1 sm2 ->
  smap_sub_prop Ps1 Ps2 fid sm2 sm.
Admitted.

Lemma tv_smap__is__correct : forall Ps1 Ps2 fid (sm1 sm2:smap), 
  uniq sm1 -> 
  (tv_smap Ps1 Ps2 fid sm1 sm2 = true <-> smap_sub_prop Ps1 Ps2 fid sm1 sm2).
Proof.
  induction sm1; simpl.  
    intros. 
    split; auto. 
      intros Ht i st1 i_in_nil. inversion i_in_nil. 

    intros sm2 Huniq. 
    destruct a as [id st1].
    remember (lookupAL _ sm2 (rename_id fid id)) as Lookup.
    destruct Lookup as [st2 | ].
    Case "id_in_sm2".
      remember (tv_sterm Ps1 Ps2 fid st1 st2) as B.
      destruct B; subst; simpl.
      SCase "st1 = st2".
        destruct_uniq.
        simpl_env.
        assert (smap_sub_prop Ps1 Ps2 fid [(id,st1)] sm2) as Hid_sub_sm2.
          intros i st Hi_in_dom. simpl in *.
          destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i id);
            inversion Hi_in_dom; subst.
            rewrite <- HeqLookup; auto.
            exists st2. auto. 
        destruct (@IHsm1 sm2 Huniq) as [J1 J2].
        split; intro J.
          apply smap_sub_prop_app1; auto.
          apply J2. eapply smap_sub_prop_app3; eauto.

      SCase "st1 <> st2".
        split; intro J. 
          inversion J.
          assert (H:=@J id). simpl in H.
          destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id id); auto.  
            rewrite <- HeqLookup in H. 
            destruct (@H st1) as [st4 [J1 J2]]; auto.
            inversion J1; subst.
            rewrite J2 in HeqB. inversion HeqB.

    Case "id_notin_sm2".
      split; intro J. 
        inversion J.
        assert (H:=@J id). simpl in H.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id id); auto. 
          rewrite <- HeqLookup in H. 
          destruct (@H st1) as [st4 [J1 J2]]; auto.
          inversion J1; subst.
Qed.

Lemma tv_cmds__is__correct : 
  forall TD Ps1 Ps2 fid nbs nbs' lc1 als1 gl Mem1 lc2 als2 Mem2 tr,
  uniq lc1 ->  
  wf_nbranchs nbs' ->
  tv_cmds Ps1 Ps2 fid nbs nbs' ->
  dbCmds TD gl lc1 als1 Mem1 (nbranchs2cmds nbs) lc2 als2 Mem2 tr ->
  exists slc,
    dbCmds TD gl lc1 als1 Mem1 (nbranchs2cmds nbs') slc als2 Mem2 tr /\
    subAL _ lc2 slc.
Proof.
  intros Ps1 Ps2 TD fid nbs nbs' lc1 als1 gl Mem1 lc2 als2 Mem2 tr Huniqc Wf Htv_cmds HdbCmds.
  assert (Uniqs:=HdbCmds).
  apply se_dbCmds_preservation in Uniqs; auto.
  apply op_cmds__satisfy__se_cmds in HdbCmds; auto.
  sumbool_simpl.
Admitted.
(*
  apply se_cmds__denote__op_cmds in HdbCmds; auto.
    destruct HdbCmds as [slc [HdbCmds Heq]].
    apply dbCmds_subEnv with (lc1':=se_cmds sstate_init nbs') in HdbCmds.


  rewrite Htv_cmds in HdbCmds.
  apply se_cmds__denote__op_cmds; auto.
Qed.
*)

Lemma lookup_tv_blocks__tv_block : forall nts1 Ps1 Ps2 fid lb1 lb2 l0 B1,
  uniqBlocks lb1 ->
  uniqBlocks lb2 ->
  tv_blocks nts1 Ps1 Ps2 fid lb1 lb2 ->
  lookupAL _ (genLabel2Block_blocks lb1) l0 = Some B1 ->
  exists B2, exists n,
    tv_block nts1 Ps1 Ps2 fid B1 B2 /\
    nth_error lb1 n = Some B1 /\
    nth_error lb2 n = Some B2 /\
    lookupAL _ (genLabel2Block_blocks lb2) l0 = Some B2.
Proof.
  induction lb1; intros; simpl in *.
    inversion H2.

    destruct lb2.
      inversion H1.

      bdestruct H1 as J1 J2.
      assert (K:=H).
      apply uniqBlocks__uniqLabel2Block in H.
      apply mergeALs_inv in H2; auto.
      destruct H2 as [H2 | H2].
        exists b. exists 0.
        assert (J:=H2).
        apply genLabel2Block_block_inv in J. subst.
        simpl. repeat (split; auto).
          apply uniqBlocks__uniqLabel2Block in H0.
          apply mergeALs_app; auto.
            left.
            unfold genLabel2Block_block in *.
            destruct B1.
            destruct b. simpl in *.
            unfold tv_block in J1.
            destruct (cmds2sbs c).
            destruct (cmds2isbs nts1 Ps1 c0).
            admit.
(*
            bdestruct5 J1 as J11 J12 J13 J14 J15.
            sumbool_subst.
            destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l2); inversion H2; subst; auto.
*)

        simpl_env in K. apply uniqBlocks_inv in K. destruct K.
        assert (K':=H0). apply uniqBlocks__uniqLabel2Block in K'.
        simpl_env in H0. apply uniqBlocks_inv in H0. destruct H0.
        apply IHlb1 with (lb2:=lb2) in H2; auto.
        destruct H2 as [B2 [n [H8 [H6 [H5 H7]]]]].
        exists B2. exists (S n). simpl. repeat (split; auto).
          apply mergeALs_app; auto.
Qed.        

Lemma tv_blocks_nth_Some_inv : forall nts1 Ps1 Ps2 fid lb1 lb2 n B1,
  uniqBlocks lb1 ->
  uniqBlocks lb2 ->
  tv_blocks nts1 Ps1 Ps2 fid lb1 lb2 ->
  nth_error lb1 n = Some B1 ->
  exists B2, 
    nth_error lb2 n = Some B2 /\ tv_block nts1 Ps1 Ps2 fid B1 B2.
Proof.
  intros nts1 Ps1 Ps2 fid lb1 lb2 n B1 H H0 H1 H2.
  assert (J:=H2).
  apply nth_error__lookupAL_genLabel2Block_blocks in H2; auto.
  destruct H2 as [l0 H2].
  apply lookup_tv_blocks__tv_block with (l0:=l0)(B1:=B1) in H1; auto.
  destruct H1 as [B2 [n' [J1 [J2 [J3 J4]]]]].
  apply uniqBlocks__uniq_nth_error with (n':=n) in J2; auto.
  subst.
  exists B2. split; auto.
Qed.

Lemma lookup_tv_fdef__tv_block : forall nts1 Ps1 Ps2 fh1 fh2 lb1 lb2 l0 B1,
  uniqBlocks lb1 ->
  uniqBlocks lb2 ->
  tv_fdef nts1 Ps1 Ps2 (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) ->
  lookupBlockViaLabelFromFdef (fdef_intro fh1 lb1) l0 = Some B1 ->
  exists B2, exists n,
    tv_block nts1 Ps1 Ps2 (getFdefID (fdef_intro fh1 lb1)) B1 B2 /\
    nth_error lb1 n = Some B1 /\
    nth_error lb2 n = Some B2 /\
    lookupBlockViaLabelFromFdef (fdef_intro fh2 lb2) l0 = Some B2.
Proof.
  intros nts1 Ps1 Ps2 fh1 fh2 lb1 lb2 l0 B1 H H0 H1 H2.
  destruct fh1 as [t1 fid1 a1].
  bdestruct H1 as EQ Htv_blocks.
  sumbool_subst.
  unfold lookupBlockViaLabelFromFdef in H2.
  unfold genLabel2Block_fdef in H2.
  eapply lookup_tv_blocks__tv_block; eauto.
Qed.

Lemma tv_block__inv : forall nts1 Ps1 Ps2 fid B1 B2,
  tv_block nts1 Ps1 Ps2 fid B1 B2 ->
  getBlockLabel B1 = getBlockLabel B2 /\
  tv_phinodes fid (getPhiNodesFromBlock B1) (getPhiNodesFromBlock B2) /\
  getTerminatorFromBlock B1 = getTerminatorFromBlock B2.
Proof.
  intros nts1 Ps1 Ps2 fid B1 B2 H.
  destruct B1.
  destruct B2. simpl in *.
  unfold tv_block in H.
  destruct (cmds2sbs c).
  destruct (cmds2isbs nts1 Ps1 c0).
    admit.
(*
  bdestruct5 H as J1 J2 J3 J4 J5.
  sumbool_subst.
  split; auto.
*)
Qed.
 
Definition phinodes_sub_prop fid (ps1 ps2:phinodes) :=
  forall i p1,
    lookupPhinode ps1 i = Some p1 ->
    exists p2, 
      lookupPhinode ps2 (rename_id fid i) = Some p2 /\ 
      tv_phinode fid p1 p2 = true.

Lemma phinodes_sub_prop_app1 : forall fid ps1 ps2 ps,
  phinodes_sub_prop fid ps1 ps -> 
  phinodes_sub_prop fid ps2 ps ->
  phinodes_sub_prop fid (ps1++ps2) ps.
Proof.
Admitted.

Lemma phinodes_sub_prop_app2 : forall fid ps1 ps2 ps,
  phinodes_sub_prop fid ps1 ps -> 
  phinodes_sub_prop fid (ps1++ps2) ps ->
  NoDup (getPhiNodesIDs (ps1++ps2)) ->
  phinodes_sub_prop fid ps2 ps.
Admitted.

Lemma tv_phinodes__is__correct: forall fid ps1 ps2, 
  NoDup (getPhiNodesIDs ps1) ->
  (tv_phinodes fid ps1 ps2 = true <-> phinodes_sub_prop fid ps1 ps2).
Proof.
  induction ps1; simpl.
    intros.
    split; auto.
      intros Ht id1 p1 Hindom. inversion Hindom.

    intros ps2 Huniq.
    simpl in Huniq.
    rewrite_env (nil ++ getPhiNodeID a :: getPhiNodesIDs ps1) in Huniq.
    assert (Hnotindom:=Huniq).
    apply NoDup_remove_2 in Hnotindom.
    assert (Huniq':=Huniq).
    apply NoDup_remove_1 in Huniq'.
    simpl_env in *.
    destruct a as [i1 t1 vs1].
    remember (lookupPhinode ps2 i1) as Lookup.
    admit.
(*
    destruct Lookup as [p2 | ].
      remember (tv_phinode fid (insn_phi i1 t1 vs1) p2) as R.
      destruct R; subst; simpl.
        assert (phinodes_sub_prop fid [insn_phi i1 t1 vs1] ps2) as i1_sub_ps2.
          intros i p1 Hi_in_dom. simpl in *.
          destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) i i1);
            inversion Hi_in_dom; subst.
            exists p2.            
            rewrite <- HeqLookup; split; auto.
        destruct (@IHps1 ps2 Huniq') as [J1 J2].
        simpl_env.
        split; intro J.
          apply phinodes_sub_prop_app1; auto.
          apply J2. 
          apply phinodes_sub_prop_app2 with (ps1:=[insn_phi i1 t1 vs1]); auto.

        split; intro J. 
          inversion J.
          assert (H:=@J i1). simpl in H.
          destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) i1 i1); auto.
            rewrite <- HeqLookup in H. 
            destruct (@H (insn_phi i1 t1 vs1)) as [p3 [J1 J2]]; auto.
            inversion J1; subst.
            rewrite <- HeqR in J2. inversion J2.
      split; intro J. 
        inversion J.
        assert (H:=@J i1). simpl in H.
        destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) i1 i1); auto.
          rewrite <- HeqLookup in H.
          destruct (@H (insn_phi i1 t1 vs1)) as [p3 [J1 J2]]; auto.
          inversion J1.
*)
Qed.

Lemma NoDup_inv : forall A (l1 l2:list A),
  NoDup (l1++l2) -> NoDup l1 /\ NoDup l2.
Proof.
  induction l1; intros l2 Huniq. auto using NoDup_nil.
    inversion Huniq; subst.
    apply IHl1 in H2.
    destruct H2 as [H21 H22].
    split; auto.    
     apply NoDup_cons; auto.
       intro Ha_in_l1.
       apply H1.
         apply in_app_iff; auto.
Qed.

(*
Lemma tv_getIncomingValuesForBlockFromPHINodes : forall ps1 TD B1 ps2 B2,
  tv_block B1 B2 ->
  tv_phinodes ps1 ps2 ->
  getIncomingValuesForBlockFromPHINodes TD ps1 B1 =
  getIncomingValuesForBlockFromPHINodes TD ps2 B2 .
Proof.
  induction ps1; intros TD B1 ps2 B2 H H0.
    destruct ps2; simpl in *; auto.
      inversion H0.

    destruct ps2; simpl in *.
      inversion H0.

      bdestruct H0 as J1 H1.
      sumbool_subst.
      apply IHps1 with (B1:=B1)(B2:=B2) (TD:=TD) in H1; auto.
      rewrite H1.
      apply tv_block__inv in H.
      destruct H as [H _].
      destruct B1.
      destruct B2.
      simpl in *. subst.
      destruct p. simpl. auto.
Qed.     

Lemma tv_switchToNewBasicBlock : forall TD l1 ps1 sbs1 tmn1 B1 l2 ps2 sbs2 tmn2 B2 lc gl,
  tv_block B1 B2 ->
  tv_block (block_intro l1 ps1 sbs1 tmn1) (block_intro l2 ps2 sbs2 tmn2) ->
  switchToNewBasicBlock TD (block_intro l1 ps1 sbs1 tmn1) B1 gl lc =
  switchToNewBasicBlock TD (block_intro l2 ps2 sbs2 tmn2) B2 gl lc.
Proof.
  unfold switchToNewBasicBlock.
  intros.
  apply tv_block__inv in H0.
  destruct H0 as [_ [H0 _]].
  erewrite tv_getIncomingValuesForBlockFromPHINodes; simpl; eauto.
Qed.

Lemma tv_terminator__is__correct : forall TD fh1 lb1 fh2 lb2 B1 B2 lc gl tmn B1' lc' tr,
  uniqFdef (fdef_intro fh1 lb1) ->
  uniqFdef (fdef_intro fh2 lb2) ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) ->
  tv_block B1 B2 ->
  dbTerminator TD (fdef_intro fh1 lb1) gl B1 lc tmn B1' lc' tr ->
  exists B2', exists n,
    tv_block B1' B2' /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    dbTerminator TD (fdef_intro fh2 lb2) gl B2 lc tmn B2' lc' tr.
Proof.
  intros TD fh1 lb1 fh2 lb2 B1 B2 lc gl tmn B1' lc' tr HuniqF1 HuniqF2 Htv_fdef Htv_block HdbTerminator.
  inversion HdbTerminator; subst.
    remember (isGVZero TD c) as R.
    destruct R; subst.
      assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' /\ 
                                  nth_error lb1 n = Some (block_intro l' ps' sbs' tmn') /\
                                  nth_error lb2 n = Some B2' /\
                                  lookupBlockViaLabelFromFdef (fdef_intro fh2 lb2) l2 = Some B2') as J.
        eapply lookup_tv_fdef__tv_block; eauto.
      destruct J as [B2' [n [J1 [J2 [J3 J4]]]]].
      exists B2'. exists n. split; auto. split; auto. split; auto.
      destruct B2' as [l2' ps2' sbs2' tmn2'].
      eapply dbBranch; eauto.
        rewrite <- HeqR. auto.
        eapply tv_switchToNewBasicBlock; eauto.
    
      assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' /\ 
                                  nth_error lb1 n = Some (block_intro l' ps' sbs' tmn') /\
                                  nth_error lb2 n = Some B2' /\
                                  lookupBlockViaLabelFromFdef (fdef_intro fh2 lb2) l1 = Some B2') as J.
        eapply lookup_tv_fdef__tv_block; eauto.
      destruct J as [B2' [n' [J1 [J2 [J3 J4]]]]].
      exists B2'. exists n'. split; auto. split; auto. split; auto.
      destruct B2' as [l2' ps2' sbs2' tmn2'].
      apply dbBranch with (c:=c); auto.
        rewrite <- HeqR. auto.
        eapply tv_switchToNewBasicBlock; eauto.

    assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' /\ 
                                  nth_error lb1 n = Some (block_intro l' ps' sbs' tmn') /\
                                  nth_error lb2 n = Some B2' /\
                                  lookupBlockViaLabelFromFdef (fdef_intro fh2 lb2) l0 = Some B2') as J.
      eapply lookup_tv_fdef__tv_block; eauto.
    destruct J as [B2' [n [J1 [J2 [J3 J4]]]]].
    exists B2'. exists n. split; auto. split; auto. split; auto.
    destruct B2' as [l2' ps2' sbs2' tmn2'].
    apply dbBranch_uncond; auto.
      eapply tv_switchToNewBasicBlock; eauto.
Qed.
*)

Definition products_sub_prop nts1 (Ps1 Ps2:products) := forall id1, 
  In id1 (getProductsIDs Ps1) ->
  (forall fdec1,
    lookupFdecViaIDFromProducts Ps1 id1 = Some fdec1 ->
    exists fdec2,
      lookupFdecViaIDFromProducts Ps2 (rename_fid id1) = Some fdec2 /\ 
      tv_fdec nts1 fdec1 fdec2 = true)
  /\
  (forall fdef1,
    lookupFdefViaIDFromProducts Ps1 id1 = Some fdef1 ->
    exists fdef2,
      lookupFdefViaIDFromProducts Ps2 (rename_fid id1) = Some fdef2 /\ 
      tv_fdef nts1 Ps1 Ps2 fdef1 fdef2 = true)
  /\
  (forall gv1,
    lookupGvarViaIDFromProducts Ps1 id1 = Some gv1 ->
    exists gv2,
      lookupGvarViaIDFromProducts Ps2 id1 = Some gv2 /\ 
      sumbool2bool _ _ (gvar_dec gv1 gv2) = true).

Lemma products_sub_prop_app1 : forall nts1 Ps1 Ps2 Ps,
  products_sub_prop nts1 Ps1 Ps -> 
  products_sub_prop nts1 Ps2 Ps ->
  products_sub_prop nts1 (Ps1++Ps2) Ps.
Admitted.

Lemma products_sub_prop_app2 : forall nts1 Ps1 Ps2 Ps,
  products_sub_prop nts1 Ps1 Ps -> 
  products_sub_prop nts1 (Ps1++Ps2) Ps ->
  NoDup (getProductsIDs (Ps1++Ps2)) ->
  products_sub_prop nts1 Ps2 Ps.
Admitted.

Lemma tv_products__is__correct: forall nts1 Ps1 Ps2, 
  NoDup (getProductsIDs Ps1) ->
  (tv_products nts1 Ps1 Ps1 Ps2 = true <-> products_sub_prop nts1 Ps1 Ps2).
Proof.
  induction Ps1; simpl.
    intros.
    split; auto.
      intros Ht id1 Hindom. inversion Hindom.

    intros Ps2 Huniq.
    simpl in Huniq.
    rewrite_env (nil ++ getProductID a :: getProductsIDs Ps1) in Huniq.
    assert (Hnotindom:=Huniq).
    apply NoDup_remove_2 in Hnotindom.
    assert (Huniq':=Huniq).
    apply NoDup_remove_1 in Huniq'.
    simpl_env in *.
    destruct a as [g1 | f1 | f1].
    Case "gvar".
      remember (lookupGvarViaIDFromProducts Ps2 (getGvarID g1)) as Lookup.
      destruct Lookup as [g2 | ].
      SCase "gid in Ps2".
        destruct (gvar_dec g1 g2); subst.
        SSCase "g1 = g2".
          assert (products_sub_prop nts1 [product_gvar g2] Ps2) as Hg2_sub_Ps2.
            intros i Hi_in_dom. simpl. 
            repeat split; try solve [intros a Hlookup; inversion Hlookup].
            intros gv1 Hlookup.
            destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getGvarID g2) i); inversion Hlookup; subst.
              exists gv1. split; auto.
              destruct (gvar_dec gv1 gv1); simpl; auto.
          destruct (@IHPs1 Ps2 Huniq') as [J1 J2].
          split; intro J.
            apply products_sub_prop_app1; auto.
              admit.

            admit.
(*
            apply J2. 
            apply products_sub_prop_app2 with (Ps1:=[product_gvar g2]); auto.
*)
          
        SSCase "g1 <> g2".
          split; intro J.
            inversion J.

            assert (In (getGvarID g1) (getProductsIDs ([product_gvar g1]++Ps1))) 
              as Hindom. 
              simpl. auto.
            assert (H:=@J (getGvarID g1) Hindom). simpl in H.
            destruct H as [_ [_ H3]].
            destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getGvarID g1) (getGvarID g1)) as [e | n']; try solve [contradict n'; auto].
            destruct (@H3 g1) as [gv2 [J1 J2]]; auto.
            rewrite <- HeqLookup in J1. inversion J1; subst.
            destruct (gvar_dec g1 gv2); subst; auto.

      SCase "gid notin Ps2".
        split; intro J.
          inversion J.

          assert (In (getGvarID g1) (getProductsIDs ([product_gvar g1]++Ps1))) 
            as Hindom. 
            simpl. auto.
          assert (H:=@J (getGvarID g1) Hindom). simpl in H.
          destruct H as [H1 [H2 H3]].
          destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getGvarID g1) (getGvarID g1)) as [e | n']; try solve [contradict n'; auto].
          destruct (@H3 g1) as [gv2 [J1 J2]]; auto.       
          rewrite <- HeqLookup in J1. inversion J1.
        
    Case "fdec". admit.
(*
      remember (lookupFdecViaIDFromProducts Ps2 (rename_fid (getFdecID f1))) as Lookup.
      destruct Lookup as [f2 | ].
      SCase "fid in Ps2".
        remember (tv_fdec Ps1 f1 f2) as R.
        destruct R; subst.
        SSCase "f1 = f2".
          assert (products_sub_prop [product_fdec f1] Ps2) as Hf2_sub_Ps2.
            intros i Hi_in_dom. simpl. 
            repeat split; try solve [intros a Hlookup; inversion Hlookup].
            intros fdec1 Hlookup.
            destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdecID f1) i); inversion Hlookup; subst.
              exists f2. split; auto.
          destruct (@IHPs1 Ps2 Huniq') as [J1 J2].
          split; intro J.
            apply products_sub_prop_app1; auto.
 
            apply J2.
            apply products_sub_prop_app2 with (Ps1:=[product_fdec f1]); auto.
          
        SSCase "f1 <> f2".
          split; intro J.
            inversion J.

            assert (In (getFdecID f1) (getProductsIDs ([product_fdec f1]++Ps1))) 
              as Hindom. 
              simpl. auto.
            assert (H:=@J (getFdecID f1) Hindom). simpl in H.
            destruct H as [H1 _].
            destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdecID f1) (getFdecID f1)) as [e | n']; try solve [contradict n'; auto].
            destruct (@H1 f1) as [fdec2 [J1 J2]]; auto.
            rewrite <- HeqLookup in J1. inversion J1; subst.
            rewrite J2 in HeqR. inversion HeqR.

      SCase "fid notin Ps2".
          split; intro J.
            inversion J.

          assert (In (getFdecID f1) (getProductsIDs ([product_fdec f1]++Ps1))) 
            as Hindom. 
            simpl. auto.
          assert (H:=@J (getFdecID f1) Hindom). simpl in H.
          destruct H as [H1 ].
          destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdecID f1) (getFdecID f1)) as [e | n']; try solve [contradict n'; auto].
          destruct (@H1 f1) as [fdec2 [J1 J2]]; auto.       
          rewrite <- HeqLookup in J1. inversion J1.
*)

    Case "fdef". admit.
(*
      remember (lookupFdefViaIDFromProducts Ps2 (rename_fid (getFdefID f1))) as Lookup.
      destruct Lookup as [f2 | ].
      SCase "fid in Ps2".
        remember (tv_fdef Ps1 f1 f2) as R.
        destruct R; subst.
        SSCase "f1 = f2".
          assert (products_sub_prop [product_fdef f1] Ps2) as Hf2_sub_Ps2.
            intros i Hi_in_dom. simpl. 
            repeat split; try solve [intros a Hlookup; inversion Hlookup].
            intros fdef1 Hlookup.
            destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdefID f1) i); inversion Hlookup; subst.
              exists f2. split; auto.
                admit.
          destruct (@IHPs1 Ps2 Huniq') as [J1 J2].
          split; intro J.
            apply products_sub_prop_app1; auto.
              admit.

            admit.
(* 
            apply J2.
            apply products_sub_prop_app2 with (Ps1:=[product_fdef f1]); auto.
*)
          
        SSCase "f1 <> f2".
          split; intro J.
            inversion J. admit.

            assert (In (getFdefID f1) (getProductsIDs ([product_fdef f1]++Ps1))) 
              as Hindom. 
              simpl. auto.
            assert (H:=@J (getFdefID f1) Hindom). simpl in H.
            destruct H as [_ [H2 _]].
            destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdefID f1) (getFdefID f1)) as [e | n']; try solve [contradict n'; auto].
            destruct (@H2 f1) as [fdec2 [J1 J2]]; auto.
            rewrite <- HeqLookup in J1. inversion J1; subst.
            admit.
(*          rewrite J2 in HeqR. inversion HeqR. *)

      SCase "fid notin Ps2".
          split; intro J.
            inversion J.

          assert (In (getFdefID f1) (getProductsIDs ([product_fdef f1]++Ps1))) 
            as Hindom. 
            simpl. auto.
          assert (H:=@J (getFdefID f1) Hindom). simpl in H.
          destruct H as [_ [H2 _]].
          destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdefID f1) (getFdefID f1)) as [e | n']; try solve [contradict n'; auto].
          destruct (@H2 f1) as [fdef2 [J1 J2]]; auto.       
          rewrite <- HeqLookup in J1. inversion J1.
*)
Qed.

Lemma tv_products__lookupFdefViaIDFromProducts : 
  forall nts1 Ps1 Ps2 fid1 rt la1 lb1,
  tv_products nts1 Ps1 Ps1 Ps2 = true ->
  lookupFdefViaIDFromProducts Ps1 fid1 = Some (fdef_intro (fheader_intro rt fid1 la1) lb1) ->
  exists la2, exists lb2,
    lookupFdefViaIDFromProducts Ps2 (rename_fid fid1) = Some (fdef_intro (fheader_intro rt (rename_fid fid1) la2) lb2) /\
    prefix _ la1 la2 /\
    tv_blocks nts1 Ps1 Ps2 fid1 lb1 lb2.
Proof.
  induction Ps1; intros Ps2 fid1 tr la1 lb1 Htv Hlookup.
    inversion Hlookup.

    (product_cases (destruct a) Case); simpl in Htv, Hlookup.
    Case "product_gvar".
      destruct (lookupGvarViaIDFromProducts Ps2 (getGvarID g)); try solve [inversion Htv].
      bdestruct Htv as H1 H2.
      admit.
(*      apply IHPs1; auto. *)
 
    Case "product_fdec".
      destruct (lookupFdecViaIDFromProducts Ps2 (rename_fid (getFdecID f))); 
        try solve [inversion Htv].
      bdestruct Htv as H1 H2.
      admit.
(*      apply IHPs1; auto. *)

    Case "product_fdef".
      remember (lookupFdefViaIDFromProducts Ps2 (rename_fid (getFdefID f))) as R.
      destruct R; try solve [inversion Htv].
      bdestruct Htv as H1 H2.
      destruct f as [[t1 fid10 a1] b1].
      destruct f0 as [[t2 fid20 a2] b2].
      unfold tv_fdef in H1. unfold tv_fheader in H1.
(*
      bdestruct4 H1 as EQ1 Hfid Hargs Hblock.
      sumbool_subst.
      simpl in *.
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) fid10 fid1); subst.
        assert (fid20 = rename_fid fid1) as EQ.
          symmetry in HeqR.
          apply lookupFdefViaIDFromProducts_ideq in HeqR; auto.
        inversion Hlookup. subst. 
        exists a2. exists b2. split; auto.

        apply IHPs1 with (Ps2:=Ps2) in Hlookup; auto.
*)
        admit.
Qed.

(*
Lemma tv_products__lookupFdefViaGV : forall Ps1 Ps2 fv1 fid1 rt la1 lb1 TD gl lc fs,
  tv_products Ps1 Ps2 = true ->
  lookupFdefViaGV TD Ps1 gl lc fs fv1 = Some (fdef_intro (fheader_intro rt fid1 la1) lb1) ->
  exists fv2, exists fid2, exists la2, exists lb2,
    lookupFdefViaGV TD Ps2 gl lc fs fv2 = Some (fdef_intro (fheader_intro rt fid2 la2) lb2) /\
    rename_fv fv1 fv2 /\
    prefix _ la1 la2 /\
    tv_blocks lb1 lb2.
Proof.
  intros.
  unfold lookupFdefViaGV in *.
  destruct (getOperandValue TD fv lc gl); try solve [inversion H0].
  destruct (lookupFdefViaGVFromFunTable fs g); try solve [inversion H0].
  assert (J:=H0). 
  apply lookupFdefViaIDFromProducts_ideq in J; subst.
  eapply tv_products__lookupFdefViaIDFromProducts; eauto.
Qed.

Lemma tv_products__lookupFdecViaIDFromProducts : forall Ps1 Ps2 fid,
  tv_products Ps1 Ps2 = true ->
  lookupFdecViaIDFromProducts Ps1 fid = lookupFdecViaIDFromProducts Ps2 (rename_fid fid).
Proof.
  induction Ps1; intros Ps2 fid Htv.
    destruct Ps2; inversion H; auto.

    (product_cases (destruct a) Case); simpl in H.
    Case "product_gvar".
      destruct Ps2; try solve [inversion H].
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.
      apply IHPs1 with (fid:=fid) in H2; auto.
 
    Case "product_fdec".
      destruct Ps2; try solve [inversion H].
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.
      sumbool_subst.
      simpl.
      rewrite IHPs1 with (Ps2:=Ps2); auto.

    Case "product_fdef".
      destruct Ps2; try solve [inversion H].
      simpl in *.
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.    
      simpl in *.
      rewrite IHPs1 with (Ps2:=Ps2); auto.
Qed.

Lemma tv_products__lookupFdefViaIDFromProducts_None : forall Ps1 Ps2 fid,
  tv_products Ps1 Ps2 = true ->
  lookupFdefViaIDFromProducts Ps1 fid = None ->
  lookupFdefViaIDFromProducts Ps2 (rename_fid fid) = None.
Proof.
  induction Ps1; intros Ps2 fid Htv Hlookup.
    destruct Ps2; inversion H; auto.

    (product_cases (destruct a) Case); simpl in H.
    Case "product_gvar".
      destruct Ps2; try solve [inversion H].
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.
      apply IHPs1 with (fid:=fid) in H2; auto.
 
    Case "product_fdec".
      destruct Ps2; try solve [inversion H].
      simpl in *.
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.    
      simpl in *.
      rewrite IHPs1 with (Ps2:=Ps2); auto.

    Case "product_fdef".
      destruct Ps2; try solve [inversion H].
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.
      destruct f. destruct f0.
      destruct f. destruct f0.
      unfold tv_fdef in H1.
      bdestruct H1 as H1 H3.
      sumbool_subst.
      inversion H1; subst.
      simpl in *.
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) i1 fid); subst; auto.
        inversion H0.      
Qed.

Lemma tv_products__lookupFdefViaGV_None : forall Ps1 Ps2 fv TD gl lc fs,
  tv_products Ps1 Ps2 ->
  lookupFdefViaGV TD Ps1 gl lc fs fv = None ->
  lookupFdefViaGV TD Ps2 gl lc fs fv = None.
Proof.
  intros.
  unfold lookupFdefViaGV in *.
  destruct (getOperandValue TD fv lc gl); auto.
  destruct (lookupFdefViaGVFromFunTable fs g); auto.
  eapply tv_products__lookupFdefViaIDFromProducts_None; eauto.
Qed.

Lemma tv_products__lookupExFdecViaGV : forall Ps1 Ps2 TD gl lc fs fv,
  tv_products Ps1 Ps2 ->
  lookupExFdecViaGV TD Ps1 gl lc fs fv = lookupExFdecViaGV TD Ps2 gl lc fs fv.
Proof.
  intros.
  unfold lookupExFdecViaGV.
  destruct (getOperandValue TD fv lc gl); auto.
  destruct (lookupFdefViaGVFromFunTable fs g); auto.
  remember (lookupFdefViaIDFromProducts Ps1 i0) as R.
  symmetry in HeqR.
  destruct R.  
    destruct f. destruct f.
    assert (H1:=HeqR).
    apply lookupFdefViaIDFromProducts_ideq in H1; subst.
    apply tv_products__lookupFdefViaIDFromProducts with (Ps2:=Ps2) in HeqR; auto.
    destruct HeqR as [lb2 [J1 J2]].
    rewrite J1. auto.

    apply tv_products__lookupFdefViaIDFromProducts_None with (Ps2:=Ps2) in HeqR; auto.
    rewrite HeqR.
    apply tv_products__lookupFdecViaIDFromProducts; auto.
Qed.
*)

(*
Definition tv_dbCall__is__correct_prop S1 TD Ps1 fs gl lc Mem0 call0 lc' Mem' tr
  (db:dbCall S1 TD Ps1 fs gl lc Mem0 call0 lc' Mem' tr) :=
  forall S2 Ps2 los nts,
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro los nts Ps1) S1 ->
  moduleInSystem (module_intro los nts Ps2) S2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  TD = (los, nts) ->
  exists slc, 
    dbCall S2 TD Ps2 fs gl lc Mem0 call0 slc Mem' tr /\
    subAL _ slc lc'.
Definition tv_subblock__is__correct_prop S1 TD Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr
  (db:dbSubblock S1 TD Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr) :=
  forall S2 Ps2 cs2 sb1 sb2 los nts,
  uniq lc ->
  cmds2sbs cs1 = (sb1::nil, nil) ->
  cmds2sbs cs2 = (sb2::nil, nil) ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro los nts Ps1) S1 ->
  moduleInSystem (module_intro los nts Ps2) S2 ->
  wf_subblock sb2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_subblock sb1 sb2 ->
  TD = (los, nts) ->
  exists slc,
    dbSubblock S2 TD Ps2 fs gl lc als Mem cs2 slc als' Mem' tr /\
    subAL _ slc lc'.
Definition tv_subblocks__is__correct_prop S1 TD Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr
  (db:dbSubblocks S1 TD Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr) :=
  forall S2 Ps2 sbs1 sbs2 cs2 los nts,
  uniq lc ->
  cmds2sbs cs1 = (sbs1, nil) ->
  cmds2sbs cs2 = (sbs2, nil) ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro los nts Ps1) S1 ->
  moduleInSystem (module_intro los nts Ps2) S2 ->
  wf_subblocks sbs2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_subblocks sbs1 sbs2 ->
  TD = (los, nts) ->
  exists slc,
    dbSubblocks S2 TD Ps2 fs gl lc als Mem cs2 slc als' Mem' tr /\
    subAL _ slc lc'.
Definition tv_block__is__correct_prop S1 TD Ps1 fs gl F1 arg state1 state2 tr
  (db:dbBlock S1 TD Ps1 fs gl F1 arg state1 state2 tr) :=
  forall S2 Ps2 fh1 lb1 fh2 lb2 B1 lc als Mem B1' lc' als' Mem' B2 los nts,
  state1 = mkState (mkEC B1 lc als) Mem ->
  state2 = mkState (mkEC B1' lc' als') Mem' ->
  F1 = fdef_intro fh1 lb1 ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  productInSystemModuleB (product_fdef (fdef_intro fh1 lb1)) S1 (module_intro los nts Ps1) ->
  productInSystemModuleB (product_fdef (fdef_intro fh2 lb2)) S2 (module_intro los nts Ps2) ->
  wf_block B2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) ->
  tv_block B1 B2 ->
  TD = (los, nts) ->
  exists B2', exists n,
  exists slc, 
    dbBlock S2 TD Ps2 fs gl (fdef_intro fh2 lb2) arg 
      (mkState (mkEC B2 lc als) Mem) 
      (mkState (mkEC B2' slc als') Mem')
      tr /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' /\
    subAL _ slc lc'.
Definition tv_blocks__is__correct_prop S1 TD Ps1 fs gl F1 lp state1 state2 tr
  (db:dbBlocks S1 TD Ps1 fs gl F1 lp state1 state2 tr) :=
  forall S2 Ps2 fh1 lb1 fh2 lb2 lc n tmn1
                            l1 ps1 cs1 ps1' l1' als
                            lc' Mem Mem' als' tmn1' cs1' los nts,
  state1 = (mkState (mkEC (block_intro l1 ps1 cs1 tmn1) lc als) Mem) ->
  state2 = (mkState (mkEC (block_intro l1' ps1' cs1' tmn1') lc' als') Mem') ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  productInSystemModuleB (product_fdef (fdef_intro fh1 lb1)) S1 (module_intro los nts Ps1) ->
  productInSystemModuleB (product_fdef (fdef_intro fh2 lb2)) S2 (module_intro los nts Ps2) ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  F1 = fdef_intro fh1 lb1 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) ->
  tv_blocks lb1 lb2 ->
  nth_error lb1 n = Some (block_intro l1 ps1 cs1 tmn1) ->
  TD = (los, nts) ->
  exists l2, exists ps2, exists cs2, exists tmn2, 
  exists l2', exists ps2', exists cs2', exists tmn2', exists n',
  exists slc, 
    nth_error lb2 n = Some (block_intro l2 ps2 cs2 tmn2) /\
    nth_error lb1 n' = Some (block_intro l1' ps1' cs1' tmn1') /\
    nth_error lb2 n' = Some (block_intro l2' ps2' cs2' tmn2') /\
    tv_block (block_intro l1 ps1 cs1 tmn1) (block_intro l2 ps2 cs2 tmn2) /\
    tv_block (block_intro l1' ps1' cs1' tmn1') (block_intro l2' ps2' cs2' tmn2') /\
    dbBlocks S2 TD Ps2 fs gl (fdef_intro fh2 lb2) lp
      (mkState (mkEC (block_intro l2 ps2 cs2 tmn2) lc als) Mem)
      (mkState (mkEC (block_intro l2' ps2' cs2' tmn2') slc als') Mem')
      tr /\
    subAL _ slc lc'.
Definition tv_fdef__is__correct_prop fv rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B1' Rid oResult tr
  (db:dbFdef fv rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B1' Rid oResult tr) :=
  forall fid Ps2 S2 la lb1 los nts,
  lookupFdefViaGV TD Ps1 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro los nts Ps1) S1 ->
  moduleInSystem (module_intro los nts Ps2) S2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  TD = (los, nts) ->
  exists lb2, exists B2', exists n,
  exists slc, 
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' /\
    lookupFdefViaGV TD Ps2 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2 /\
    dbFdef fv rt lp S2 TD Ps2 lc gl fs Mem slc als' Mem' B2' Rid oResult tr /\
    subAL _ slc lc'.

Lemma tv__is__correct :
  (forall S1 TD Ps1 fs gl lc Mem0 call0 lc' Mem' tr db, 
     tv_dbCall__is__correct_prop S1 TD Ps1 fs gl lc Mem0 call0 lc' Mem' tr db) /\
  (forall S1 TD Ps1 fs gl lc als Mem sb1 lc' als' Mem' tr db,
     tv_subblock__is__correct_prop S1 TD Ps1 fs gl lc als Mem sb1 lc' als' Mem' tr db) /\
  (forall S1 TD Ps1 fs gl lc als Mem sbs1 lc' als' Mem' tr db,
     tv_subblocks__is__correct_prop S1 TD Ps1 fs gl lc als Mem sbs1 lc' als' Mem' tr db) /\
  (forall S1 TD Ps1 fs gl F1 arg state1 state2 tr db,
     tv_block__is__correct_prop S1 TD Ps1 fs gl F1 arg state1 state2 tr db) /\
  (forall S1 TD Ps1 fs gl F1 lp state1 state2 tr db,
     tv_blocks__is__correct_prop S1 TD Ps1 fs gl F1 lp state1 state2 tr db) /\
  (forall fv rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B' Rid oResult tr db,
     tv_fdef__is__correct_prop fv rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B' Rid oResult tr db).
Proof.
(db_mutind_cases
  apply db_mutind with
    (P  := tv_dbCall__is__correct_prop)
    (P0 := tv_subblock__is__correct_prop)
    (P1 := tv_subblocks__is__correct_prop)
    (P2 := tv_block__is__correct_prop)
    (P3 := tv_blocks__is__correct_prop)
    (P4 := tv_fdef__is__correct_prop) Case);
  unfold tv_dbCall__is__correct_prop, 
         tv_subblock__is__correct_prop, tv_subblocks__is__correct_prop,
         tv_block__is__correct_prop, tv_blocks__is__correct_prop,
         tv_fdef__is__correct_prop.
Case "dbCall_internal".
  intros S TD Ps lc gl fs rid noret0 tailc0 rt fid lp Rid oResult tr lc' Mem0 
    Mem' als' Mem'' B' d H e HisCall S2 Ps2 los nts H0 H1 H2 H3 H4 H5 H6 HH.
  inversion d; subst.
    eapply H with (S2:=S2)(Ps2:=Ps2) in H7; eauto.
    clear H.
    destruct H7 as [lb2 [B2' [n [slc [J1 [J2 [J3 [J4 [J5 [J6 HeqEnv]]]]]]]]]].
    exists (callUpdateLocals (los, nts) noret0 rid rt (Some Result) lc slc gl).
    split; eauto using subAL_callUpdateLocals, subAL_refl.

    eapply H with (S2:=S2)(Ps2:=Ps2) in H7; eauto.
    clear H.
    destruct H7 as [lb2 [B2' [n [slc [J1 [J2 [J3 [J4 [J5 [J6 HeqEnv]]]]]]]]]].
    exists (callUpdateLocals (los, nts) noret0 rid rt None lc slc gl).
    split; eauto using subAL_callUpdateLocals, subAL_refl.

Case "dbCall_external". admit.
(*
  intros S TD Ps lc gl fs rid noret0 tailc0 fv fid lp rt la Mem0 oresult Mem'
         H HisCall S2 Ps2 los nts H0 H1 H2 H3 H4 H5 H6 H7.
  exists (exCallUpdateLocals noret0 rid rt oresult lc).
  split; auto using subAL_exCallUpdateLocals, subAL_refl.
    apply dbCall_external with (fid:=fid)(la:=la); auto.
      rewrite <- tv_products__lookupExFdecViaGV with (Ps1:=Ps); auto.
*)
Case "dbSubblock_intro".
  intros S TD Ps lc1 als1 gl fs Mem1 cs call0 lc2 als2 Mem2 tr1 lc3 Mem3 tr2 d 
    d0 H S2 Ps2 cs2 sb1 sb2 los nts H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
  unfold tv_subblock in H10.
  destruct sb1.
  destruct sb2.
  apply cmds2sb_inv in H1.
  destruct H1 as [cs' [call1 [J1 [J2 J3]]]].
  apply cmds2nbs__nbranchs2cmds in J2.
  apply app_inj_tail in J1.
  destruct J1; subst.
  apply cmds2sb_inv in H2.
  destruct H2 as [cs2' [call0 [J1 [J2 J3]]]]; subst.
  apply cmds2nbs__nbranchs2cmds in J2.
  admit.
(*
  bdestruct H10 as EQ1 EQ2.
  sumbool_subst.
  inversion H7; subst.
  assert (uniq lc2) as J.
    apply se_dbCmds_preservation in d; auto.
  apply tv_cmds__is__correct with (nbs':=NBs1) in d; 
    try solve [eauto using eq_sumbool2bool_true | apply eq_sumbool2bool_true; auto].
  destruct d as [lc2' [Hcmds Hsub2]].
  apply H in H6; auto. clear H.
  destruct H6 as [lc3' [HdbCall Hsub3]].  
  apply dbCall_subEnv with (lc1':=lc2') in HdbCall; auto using eqAL_sym.
  destruct HdbCall as [lc3'' [HdbCall Hsub3']].
  exists lc3''. split; eauto using eqAL_trans, eqAL_sym.
*)

Case "dbSubblocks_nil".
  intros S TD Ps lc als gl fs Mem0 S2 Ps2 sbs1 sbs2 cs2 los nts H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  simpl in H0. inversion H0; subst.
  destruct sbs2;try solve [auto | simpl in H9; inversion H9].
    apply cmds2sbs_nil_inv in H1; subst.
    exists lc. split; auto using subAL_refl.

Case "dbSubblocks_cons".
  intros S TD Ps lc1 als1 gl fs Mem1 lc2 als2 Mem2 lc3 als3 Mem3 cs cs' t1 t2 d H d0 H0 S2
         Ps2 sbs1 sbs2 cs2 los nts H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
  assert (Hcs2sb := d).
  apply dbSubblock__cmds2sb in Hcs2sb.
  destruct Hcs2sb as [sb Hcs2sb].
  assert (Hcs'2sbs := d0).
  apply dbSubblocks__cmds2sbs in Hcs'2sbs.
  destruct Hcs'2sbs as [sbs Hcs'2sbs].
  apply cmds_cons2sbs_inv with (sb:=sb)(sbs':=sbs) in H2; auto.
  subst.
  simpl in H11.
  destruct sbs2 ; try solve [inversion H11].
  bdestruct H11 as H2 H12.
  apply cmds2sbs_cons_inv in H3.
  destruct H3 as [cs21 [cs22 [cs212s [cs222sbs2 EQ]]]]; subst.
  inversion_clear H8; subst.
  eapply H with (S2:=S2)(Ps2:=Ps2)(cs2:=cs21) in H2; eauto.
  clear H. destruct H2 as [lc2' [HdbSubblock Heq2]].
  assert (uniq lc2) as Uniqc2.
    apply se_dbSubblock_preservation in d; auto.
  eapply H0 with (S2:=S2)(Ps2:=Ps2)(cs2:=cs22) in H12; eauto.
  clear H0. destruct H12 as [lc3' [HdbSubblocks Heq3]].
  apply dbSubblocks_subEnv with (lc1':=lc2') in HdbSubblocks; auto using eqAL_sym.
  destruct HdbSubblocks as [lc3'' [HdbSubblocks Heq3']].
  exists lc3''. split; eauto using eqAL_trans, eqAL_sym.
    admit. admit.

Case "dbBlock_intro".
  intros S TD Ps F tr1 tr2 l0 ps cs cs' tmn gl fs lc1 als1 Mem1 lc2 als2 Mem2 lc3 als3 Mem3 lc4 B' arg0 tr3 d H d0 d1
         S2 Ps2 fh1 lb1 fh2 lb2 B1 lc als Mem0 B1' lc' als' Mem' B2 los nts H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13; subst.
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  destruct B2 as [l2 ps2 cs2 tmn2].
  unfold tv_block in H12.
  remember (cmds2sbs (cs++cs')) as R1.
  remember (cmds2sbs cs2) as R2.
  destruct R1 as [sbs1 nbs1].
  destruct R2 as [sbs2 nbs2].
  bdestruct5 H12 as EQ1 Htv_phinodes Htv_subblocks Htv_cmds EQ2.
  sumbool_subst.

  assert (Hcs2sbs1 := d).
  apply dbSubblocks__cmds2sbs in Hcs2sbs1.
  destruct Hcs2sbs1 as [sbs Hcs2sbs1].
  assert (Hcs2nbs1 := d0).
  apply dbCmds__cmds2nbs in Hcs2nbs1.
  destruct Hcs2nbs1 as [nbs Hcs2nbs1].
 
  assert (J:=HeqR1).
  symmetry in J.
  apply cmds_rcons2sbs_inv with (sbs:=sbs)(nbs:=nbs) in J; auto using cmds2nbranchs__cmds2nbs.
  destruct J; subst.

  assert (J:=HeqR2).
  symmetry in J.
  apply cmds2sbs_inv in J.
  destruct J as [cs1 [cs3 [EQ [Hcs12sbs2 Hcs32nbs2]]]]; subst.
  inversion H8; subst. clear H8.

  apply cmds_rcons2sbs_inv with (sbs:=sbs2)(nbs:=nbs2) in H12; auto.
  destruct H12; subst.
  assert (J:=Htv_subblocks).
  assert (moduleInSystem (module_intro los nts Ps) S) as MinS.
    apply productInSystemModuleB_inv in H6.    
    destruct H6; auto.
  assert (moduleInSystem (module_intro los nts Ps2) S2) as M2inS2.
    apply productInSystemModuleB_inv in H7.    
    destruct H7; auto.
  eapply H with (S2:=S2)(Ps2:=Ps2)(cs2:=cs1) in J; eauto.
  clear H.
  destruct J as [lc2' [Hsubblocks Heq2]].

  apply cmds2nbs__nbranchs2cmds in Hcs2nbs1. subst.
  apply cmds2nbs__nbranchs2cmds in Hcs32nbs2. subst.
  assert (uniq lc2) as Uniqc2.
    apply se_dbSubblocks_preservation in d; auto.
  apply tv_cmds__is__correct with (nbs':=nbs2) in d0; auto.
  destruct d0 as [lc3' [HdbCmds Heq3]].
  admit.
(*
  apply tv_terminator__is__correct with (B2:=block_intro l2 ps2 (cs1++nbranchs2cmds nbs2) tmn2)(fh2:=fh2)(lb2:=lb2) in d1; auto.
    destruct d1 as [B2' [n [Htv_block1'2' [J2 [J3 Hdb]]]]].
    exists B2'. exists n. 
    
    apply dbCmds_eqEnv with (lc1':=lc2') in HdbCmds; auto using eqAL_sym.
    destruct HdbCmds as [lc2'' [HdbCmds Heq2']].

    apply dbTerminator_eqEnv with (lc1':=lc2'') in Hdb; eauto using eqAL_sym, eqAL_trans.
    destruct Hdb as [lc3'' [HdbTerminator Heq3']].

    exists lc3''. 
    split; eauto using eqAL_trans, eqAL_sym.

    apply uniqSystem__uniqFdef with (S:=S)(M:=module_intro los nts Ps); auto.
    apply uniqSystem__uniqFdef with (S:=S2)(M:=module_intro los nts Ps2); auto.

    unfold tv_block.
    rewrite <- HeqR1.
    rewrite <- HeqR2.
    repeat_bsplit.
*)
Case "dbBlocks_nil". 
  intros S TD Ps fs gl F arg0 state S2 Ps2 fh1 lb1 fh2 lb2 lc n tmn1 l1 ps1 cs1
         ps1' l1' als lc' Mem0 Mem' als' tmn1' cs1' los nts H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12; subst.
  inversion H0; subst. clear H0.
  apply uniqSystem__uniqFdef in H4; auto.
  apply uniqSystem__uniqFdef in H5; auto.
  apply tv_blocks_nth_Some_inv with (n:=n)(B1:=block_intro l1' ps1' cs1' tmn1') in H10; auto.
  destruct H10 as [[l2 ps2 cs2 tmn2] [Hnth_error2 Htv_block]].
  exists l2. exists ps2. exists cs2. exists tmn2.
  exists l2. exists ps2. exists cs2. exists tmn2. 
  exists n. exists lc'.
  repeat (split; auto).

Case "dbBlocks_cons".
  intros S TD Ps fs gl F arg0 S1 S2 S3 t1 t2 d H d0 H0 S0 Ps2 fh1 lb1 fh2 lb2 lc n tmn1 l1
         ps1 cs1 ps1' l1' als lc' Mem0 Mem' als' tmn1' cs1' los nts H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14; subst.
  inversion d; subst.
  assert (J:=H12).  
  assert (uniqF1:=H6).
  assert (uniqF2:=H7).
  apply uniqSystem__uniqFdef in uniqF1; auto.
  apply uniqSystem__uniqFdef in uniqF2; auto.
  apply tv_blocks_nth_Some_inv with (n:=n)(B1:=block_intro l1 ps1 (cs++cs') tmn1) in J; auto.
  destruct J as [[l2 ps2 cs2 tmn2] [Hnth_error2 Htv_block12]].
  assert (J:=Htv_block12).
  eapply H with (S2:=S0)(Ps2:=Ps2)(fh3:=fh2)(lb3:=lb2)(fh2:=fh1)(lb2:=lb1)(Mem:=Mem0)(B1':=B')(lc':=lc4)(als':=als3)(Mem':=Mem3)(als0:=als)(lc0:=lc) in J; eauto.
    destruct J as [B2' [n' [lc4' [Hdb [J1 [J2 [Htv_block12' Heq4]]]]]]].
    clear H.
    destruct B' as [l3 ps3 cs3 tmn3].
    assert (uniq lc4) as Uniqc4.
      apply se_dbBlock_preservation in d; 
        eauto using productInSystemModuleB_nth_error__blockInSystemModuleFdef.
      destruct d as [L _]; auto.
    eapply H0 with (S2:=S0)(Ps2:=Ps2)(fh2:=fh1)(fh3:=fh2)(n:=n')(tmn1:=tmn3) (lc:=lc4)
      (l1:=l3)(ps1:=ps3)(cs1:=cs3)(ps1'0:=ps1')(l1'0:=l1')(als:=als3)(lc'0:=lc')
      (Mem:=Mem3)(Mem'0:=Mem')(als'0:=als')(tmn1'0:=tmn1')(cs1'0:=cs1') in H12; eauto.
    destruct H12 as [l4 [ps4 [cs4 [tmn4 [l4' [ps4' [cs4' [tmn4' [n'' [lc2' [J3 [J4 [J5 [J6 [J7 [J8 Heq2]]]]]]]]]]]]]]]].
    clear H0.

    admit. admit.
(*
    apply dbBlocks_eqEnv with (lc1':=lc4') in J8; auto using eqAL_sym.
    destruct J8 as [lc2'' [HdbBlocks Heq2']].

    exists l2. exists ps2. exists cs2. exists tmn2.
    exists l4'. exists ps4'. exists cs4'. exists tmn4'.
    exists n''. exists lc2''.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.

    rewrite J2 in J3.
    inversion J3; subst. clear J3.
    split; eauto using eqAL_sym, eqAL_trans.

    apply uniqFdef__wf_block with (fh:=fh2)(lb:=lb2)(n:=n); eauto using uniqSystem__uniqFdef.
*)
Case "dbFdef_func". admit.
(*
    intros S TD Ps gl fs fv fid lp lc rid l1 ps1 cs1 tmn1 rt la lb Result lc1 tr1 Mem0 Mem1 als1
           l2 ps2 cs21 cs22 lc2 als2 Mem2 tr2 lc3 als3 Mem3 tr3 e e0 d H d0 H0 d1
           fid0 Ps2 S2 la0 lb1 los nts H1 H2 H3 H4 H5 H6 H7 H8 H9.
    rewrite H1 in e. inversion e; subst. clear e.
    assert (exists lb2, lookupFdefViaGV (los, nts) Ps2 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
                        tv_blocks lb lb2) as J.
      apply tv_products__lookupFdefViaGV with (Ps1:=Ps); auto.
    destruct J as [lb2 [H10 H11]].
    assert (uniq (initLocals la (params2GVs (los, nts) lp lc gl))) as uniqInitLocals.
      apply initLocals_uniq.
    assert (Htv_blocks:=H11).
    eapply H with (S2:=S2)(Ps2:=Ps2)(fh1:=fheader_intro rt fid la)(fh2:=fheader_intro rt fid la)(n:=0)
      (ps1':=ps2)(l1':=l2)(als:=nil)(lc':=lc1) (lc0:=initLocals la (params2GVs (los, nts) lp lc gl))
      (Mem:=Mem0)(Mem':=Mem1)(als':=als1)(tmn1':=insn_return rid rt Result)(cs1':=cs21++cs22) 
      (ps3:=ps1)(cs2:=cs1)(tmn2:=tmn1)(l3:=l1)in H11; eauto.
      clear H.
      destruct H11 as [l3 [ps3 [cs3 [tmn2 [l2' [ps2' [cs2' [tmn2' [n' [lc1' [J1 [J2 [J3 [J4 [J5 [J6 Heq1]]]]]]]]]]]]]]]].

      exists lb2. exists (block_intro l2' ps2' cs2' tmn2'). exists n'.

      assert (J5':=J5).
      unfold tv_block in J5.
      remember (cmds2sbs (cs21++cs22)) as R1.
      remember (cmds2sbs cs2') as R2.
      destruct R1 as [sbs1 nbs1].
      destruct R2 as [sbs2 nbs2].
      bdestruct5 J5 as EQ1 Htv_phinodes Htv_subblocks Htv_cmds EQ2.
      sumbool_subst.

      assert (Hcs21sbs1 := d0).
      apply dbSubblocks__cmds2sbs in Hcs21sbs1.
      destruct Hcs21sbs1 as [sbs Hcs21sbs1].
      assert (Hcs22nbs1 := d1).
      apply dbCmds2nbranchs in Hcs22nbs1.
      destruct Hcs22nbs1 as [nbs Hcs22nbs1].

      assert (J:=HeqR1).
      symmetry in J.
      apply cmds_rcons2sbs_inv with (sbs:=sbs)(nbs:=nbs) in J; auto using cmds2nbranchs__cmds2nbs.
      destruct J; subst.

      assert (J:=HeqR2).
      symmetry in J.
      apply cmds2sbs_inv in J.
      destruct J as [cs41 [cs42 [EQ [Hcs41sbs2 Hcs42nbs2]]]]; subst.

      assert (J:=HeqR2).
      symmetry in J.
      apply cmds_rcons2sbs_inv with (sbs:=sbs2)(nbs:=nbs2) in J; auto.
      destruct J; subst. clear H H9.

      assert (uniq lc1) as Uniqc1.
        apply se_dbBlocks_preservation in d; auto.
          destruct d as [U1 _]; auto.
          apply productInSystemModuleB_nth_error__blockInSystemModuleFdef with (n:=0); 
            eauto using lookupFdefViaGVInSystem.
      assert (wf_subblocks sbs2 /\ wf_nbranchs nbs2) as J.
        apply uniqCmds___wf_subblocks_wf_nbranchs with (cs:=cs41++cs42); auto.
          clear - J6 J1 H10 H6 H2 H1 H4.
          apply se_dbBlocks_preservation in J6; auto using initLocals_uniq.
          destruct J6 as [uinqc1 Bin].
          apply blockInSystemModuleFdef_inv in Bin.
          destruct Bin as [J2 [J3 [J4 J5]]].
          apply uniqSystem__uniqFdef in J5; auto.

          apply blockInFdefB__exists_nth_error in J2.       
          destruct J2 as [n J2].
          apply uniqFdef__uniqBlock with (n:=n)(l1:=l2')(ps1:=ps2')(cs1:=cs41++cs42)(tmn1:=insn_return rid rt Result) in J5; auto.

          eapply productInSystemModuleB_nth_error__blockInSystemModuleFdef; 
            eauto using lookupFdefViaGVInSystem.
      destruct J as [wf_sbs2 wf_nbs2].
      eapply H0 with (S2:=S2)(Ps2:=Ps2)(cs2:=cs41) in Htv_subblocks; eauto.
        clear H0.
        destruct Htv_subblocks as [lc2' [HdbSubblocks Heq2]].

        apply cmds2nbranchs__nbranchs2cmds in Hcs22nbs1. subst.
        apply cmds2nbs__nbranchs2cmds in Hcs42nbs2. subst.
        assert (uniq lc2) as Uniqc2.
          apply se_dbSubblocks_preservation in d0; auto.
        apply tv_cmds__is__correct with (nbs':=nbs2) in d1; auto.
        destruct d1 as [lc3' [HdbCmds Heq3]].

        apply dbSubblocks_eqEnv with (lc1':=lc1') in HdbSubblocks; auto using eqAL_sym.
        destruct HdbSubblocks as [lc2'' [HdbSubblocks Heq2']].

        apply dbCmds_eqEnv with (lc1':=lc2'') in HdbCmds; eauto using eqAL_sym, eqAL_trans.
        destruct HdbCmds as [lc3'' [HdbCmds Heq3']].

        exists lc3''.
        split; auto. split; auto.
        split; auto.
        split; auto.
        split; auto.
        split; eauto using eqAL_trans, eqAL_sym.

      eapply lookupFdefViaGVInSystem; eauto.
      eapply lookupFdefViaGVInSystem; eauto.

      unfold tv_fdef.
      repeat_bsplit.
*)
Case "dbFdef_proc". admit.
(*
    intros S TD Ps gl fs fv fid lp lc rid l1 ps1 cs1 tmn1 rt la lb lc1 tr1 Mem0 Mem1 als1
           l2 ps2 cs21 cs22 lc2 als2 Mem2 tr2 lc3 als3 Mem3 tr3 e e0 d H d0 H0 d1
           fid0 Ps2 S2 la0 lb1 los nts H1 H2 H3 H4 H5 H6 H7 H8 H9.
    rewrite H1 in e. inversion e; subst. clear e.
    assert (exists lb2, lookupFdefViaGV (los, nts) Ps2 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
                        tv_blocks lb lb2) as J.
      apply tv_products__lookupFdefViaGV with (Ps1:=Ps); auto.
    destruct J as [lb2 [H10 H11]].
    assert (uniq (initLocals la (params2GVs (los, nts) lp lc gl))) as uniqInitLocals.
      apply initLocals_uniq.
    assert (Htv_blocks:=H11).
    eapply H with (S2:=S2)(Ps2:=Ps2)(fh1:=fheader_intro rt fid la)(fh2:=fheader_intro rt fid la)(n:=0)
      (ps1':=ps2)(l1':=l2)(als:=nil)(lc':=lc1)(lc0:=(initLocals la (params2GVs (los, nts) lp lc gl)))
      (Mem:=Mem0)(Mem':=Mem1)(als':=als1)(tmn1':=insn_return_void rid)(cs1':=cs21++cs22) 
      (ps3:=ps1)(cs2:=cs1)(tmn2:=tmn1)(l3:=l1)in H11; eauto.
      clear H.
      destruct H11 as [l3 [ps3 [cs3 [tmn2 [l2' [ps2' [cs2' [tmn2' [n' [lc1' [J1 [J2 [J3 [J4 [J5 [J6 Heq1]]]]]]]]]]]]]]]].

      exists lb2. exists (block_intro l2' ps2' cs2' tmn2'). exists n'.

      assert (J5':=J5).
      unfold tv_block in J5.
      remember (cmds2sbs (cs21++cs22)) as R1.
      remember (cmds2sbs cs2') as R2.
      destruct R1 as [sbs1 nbs1].
      destruct R2 as [sbs2 nbs2].
      bdestruct5 J5 as EQ1 Htv_phinodes Htv_subblocks Htv_cmds EQ2.
      sumbool_subst.

      assert (Hcs21sbs1 := d0).
      apply dbSubblocks__cmds2sbs in Hcs21sbs1.
      destruct Hcs21sbs1 as [sbs Hcs21sbs1].
      assert (Hcs22nbs1 := d1).
      apply dbCmds2nbranchs in Hcs22nbs1.
      destruct Hcs22nbs1 as [nbs Hcs22nbs1].

      assert (J:=HeqR1).
      symmetry in J.
      apply cmds_rcons2sbs_inv with (sbs:=sbs)(nbs:=nbs) in J; auto using cmds2nbranchs__cmds2nbs.
      destruct J; subst.

      assert (J:=HeqR2).
      symmetry in J.
      apply cmds2sbs_inv in J.
      destruct J as [cs41 [cs42 [EQ [Hcs41sbs2 Hcs42nbs2]]]]; subst.

      assert (J:=HeqR2).
      symmetry in J.
      apply cmds_rcons2sbs_inv with (sbs:=sbs2)(nbs:=nbs2) in J; auto.
      destruct J; subst. clear H H9.

      assert (uniq lc1) as Uniqc1.
        apply se_dbBlocks_preservation in d; auto.
          destruct d as [U1 _]; auto.
          apply productInSystemModuleB_nth_error__blockInSystemModuleFdef with (n:=0); 
            eauto using lookupFdefViaGVInSystem.
      assert (wf_subblocks sbs2 /\ wf_nbranchs nbs2) as J.
        apply uniqCmds___wf_subblocks_wf_nbranchs with (cs:=cs41++cs42); auto.
          clear - J6 J1 H10 H6 H2 H1 H4.
          apply se_dbBlocks_preservation in J6; auto using initLocals_uniq.
          destruct J6 as [uinqc1 Bin].
          apply blockInSystemModuleFdef_inv in Bin.
          destruct Bin as [J2 [J3 [J4 J5]]].
          apply uniqSystem__uniqFdef in J5; auto.

          apply blockInFdefB__exists_nth_error in J2.       
          destruct J2 as [n J2].
          apply uniqFdef__uniqBlock with (n:=n)(l1:=l2')(ps1:=ps2')(cs1:=cs41++cs42)(tmn1:=insn_return_void rid) in J5; auto.

          eapply productInSystemModuleB_nth_error__blockInSystemModuleFdef; 
            eauto using lookupFdefViaGVInSystem.
      destruct J as [wf_sbs2 wf_nbs2].
      eapply H0 with (S2:=S2)(Ps2:=Ps2)(cs2:=cs41) in Htv_subblocks; eauto.
        clear H0.
        destruct Htv_subblocks as [lc2' [HdbSubblocks Heq2]].

        apply cmds2nbranchs__nbranchs2cmds in Hcs22nbs1. subst.
        apply cmds2nbs__nbranchs2cmds in Hcs42nbs2. subst.
        assert (uniq lc2) as Uniqc2.
          apply se_dbSubblocks_preservation in d0; auto.
        apply tv_cmds__is__correct with (nbs':=nbs2) in d1; auto.
        destruct d1 as [lc3' [HdbCmds Heq3]].

        apply dbSubblocks_eqEnv with (lc1':=lc1') in HdbSubblocks; auto using eqAL_sym.
        destruct HdbSubblocks as [lc2'' [HdbSubblocks Heq2']].

        apply dbCmds_eqEnv with (lc1':=lc2'') in HdbCmds; eauto using eqAL_sym, eqAL_trans.
        destruct HdbCmds as [lc3'' [HdbCmds Heq3']].

        exists lc3''.
        split; auto. split; auto.
        split; auto.
        split; auto. split; auto.
        split; eauto using eqAL_trans, eqAL_sym.

      eapply lookupFdefViaGVInSystem; eauto.
      eapply lookupFdefViaGVInSystem; eauto.

      unfold tv_fdef.
      repeat_bsplit.
*)
Qed.   

Lemma tv_dbCall__is__correct : forall S1 los nts Ps1 fs gl lc Mem0 call0 lc' Mem' tr S2 Ps2,
  dbCall S1 (los, nts) Ps1 fs gl lc Mem0 call0 lc' Mem' tr ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro los nts Ps1) S1 ->
  moduleInSystem (module_intro los nts Ps2) S2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists slc,
    dbCall S2 (los, nts) Ps2 fs gl lc Mem0 call0 slc Mem' tr /\
    subAL _ slc lc'.
Proof.
  intros.
  destruct tv__is__correct as [J _].
  unfold tv_dbCall__is__correct_prop in J.
  eapply J; eauto.
Qed.

Definition tv_subblock__is__correct : forall S1 los nts Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr S2 Ps2 cs2 sb1 sb2,
  dbSubblock S1 (los, nts) Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr ->
  uniq lc ->
  cmds2sbs cs1 = (sb1::nil, nil) ->
  cmds2sbs cs2 = (sb2::nil, nil) ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro los nts Ps1) S1 ->
  moduleInSystem (module_intro los nts Ps2) S2 ->
  wf_subblock sb2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_subblock sb1 sb2 ->
  exists slc,
    dbSubblock S2 (los, nts) Ps2 fs gl lc als Mem cs2 slc als' Mem' tr /\
    subAL _ slc lc'.
Proof.
  intros.
  destruct tv__is__correct as [_ [J _]].
  unfold tv_subblock__is__correct_prop in J.
  eapply J; eauto.
Qed.

Lemma tv_subblocks__is__correct : forall S1 los nts Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr S2 Ps2 sbs1 sbs2 cs2,
  dbSubblocks S1 (los, nts) Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr ->
  uniq lc ->
  cmds2sbs cs1 = (sbs1, nil) ->
  cmds2sbs cs2 = (sbs2, nil) ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro los nts Ps1) S1 ->
  moduleInSystem (module_intro los nts Ps2) S2 ->
  wf_subblocks sbs2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_subblocks sbs1 sbs2 ->
  exists slc, 
    dbSubblocks S2 (los, nts) Ps2 fs gl lc als Mem cs2 slc als' Mem' tr /\
    subAL _ slc lc'.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [J _]]].
  unfold tv_subblocks__is__correct_prop in J.
  eapply J; eauto.
Qed.

Lemma tv_block__is__correct : forall S1 los nts Ps1 arg tr
  S2 Ps2 fh1 lb1 fh2 lb2 B1 lc als gl fs Mem B1' lc' als' Mem' B2,
  dbBlock S1 (los, nts) Ps1 fs gl (fdef_intro fh1 lb1) arg (mkState (mkEC B1 lc als) Mem) (mkState (mkEC B1' lc' als') Mem') tr ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  productInSystemModuleB (product_fdef (fdef_intro fh1 lb1)) S1 (module_intro los nts Ps1) ->
  productInSystemModuleB (product_fdef (fdef_intro fh2 lb2)) S2 (module_intro los nts Ps2) ->
  wf_block B2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) ->
  tv_block B1 B2 ->
  exists B2', exists n, exists slc,
    dbBlock S2 (los, nts) Ps2 fs gl (fdef_intro fh2 lb2) arg 
      (mkState (mkEC B2 lc als) Mem) 
      (mkState (mkEC B2' slc als') Mem')
      tr /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' /\ 
    subAL _ slc lc'.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [_ [J _]]]].
  unfold tv_block__is__correct_prop in J.
  eapply J with (state1:=(mkState (mkEC B1 lc als) Mem0))(state2:=(mkState (mkEC B1' lc' als') Mem'))(F1:=(fdef_intro fh1 lb1)); eauto.
Qed.

Lemma tv_blocks__is__correct : forall S1 los nts Ps1 lp tr
  S2 Ps2 fh1 lb1 fh2 lb2 fs gl lc n tmn1
                            l1 ps1 sbs1 ps1' l1' als
                            lc' Mem Mem' als' tmn1' sbs1',
  dbBlocks S1 (los, nts) Ps1 fs gl (fdef_intro fh1 lb1) lp (mkState (mkEC (block_intro l1 ps1 sbs1 tmn1) lc als) Mem) (mkState (mkEC (block_intro l1' ps1' sbs1' tmn1') lc' als') Mem') tr ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  productInSystemModuleB (product_fdef (fdef_intro fh1 lb1)) S1 (module_intro los nts Ps1) ->
  productInSystemModuleB (product_fdef (fdef_intro fh2 lb2)) S2 (module_intro los nts Ps2) ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) ->
  tv_blocks lb1 lb2 ->
  nth_error lb1 n = Some (block_intro l1 ps1 sbs1 tmn1) ->
  exists l2, exists ps2, exists sbs2, exists tmn2, 
  exists l2', exists ps2', exists sbs2', exists tmn2', exists n',
  exists slc,
    nth_error lb2 n = Some (block_intro l2 ps2 sbs2 tmn2) /\
    nth_error lb1 n' = Some (block_intro l1' ps1' sbs1' tmn1') /\
    nth_error lb2 n' = Some (block_intro l2' ps2' sbs2' tmn2') /\
    tv_block (block_intro l1 ps1 sbs1 tmn1) (block_intro l2 ps2 sbs2 tmn2) /\
    tv_block (block_intro l1' ps1' sbs1' tmn1') (block_intro l2' ps2' sbs2' tmn2') /\
    dbBlocks S2 (los, nts) Ps2 fs gl (fdef_intro fh2 lb2) lp
      (mkState (mkEC (block_intro l2 ps2 sbs2 tmn2) lc als) Mem)
      (mkState (mkEC (block_intro l2' ps2' sbs2' tmn2') slc als') Mem')
      tr /\
    subAL _ slc lc'.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [_ [_ [J _]]]]].
  unfold tv_blocks__is__correct_prop in J.
  eapply J with (state1:=(mkState (mkEC (block_intro l1 ps1 sbs1 tmn1) lc als) Mem0))(state2:=(mkState (mkEC (block_intro l1' ps1' sbs1' tmn1') lc' als') Mem'))(F1:=(fdef_intro fh1 lb1)); eauto.
Qed.

Lemma _tv_fdef__is__correct : forall fv rt lp S1 los nts Ps1 lc gl fs Mem lc' als' Mem' B1' Rid oResult tr
  fid Ps2 S2 la lb1,
  dbFdef fv rt lp S1 (los, nts) Ps1 lc gl fs Mem lc' als' Mem' B1' Rid oResult tr ->
  lookupFdefViaGV (los, nts) Ps1 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro los nts Ps1) S1 ->
  moduleInSystem (module_intro los nts Ps2) S2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists lb2, exists B2', exists n, exists slc,
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' /\
    lookupFdefViaGV (los, nts) Ps2 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2 /\
    dbFdef fv rt lp S2 (los, nts) Ps2 lc gl fs Mem slc als' Mem' B2' Rid oResult tr /\
    subAL _ slc lc'.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [_ [_ [_ J]]]]].
  unfold tv_fdef__is__correct_prop in J.
  eapply J; eauto.
Qed.

Lemma tv_fdef__is__correct : forall ECs fv rt lp S1 los nts Ps1 lc gl fs Mem lc' als' Mem' B1' Rid oResult tr
  fid Ps2 S2 la lb1,
  LLVMopsem.dbFdef fv rt lp S1 (los, nts) Ps1 ECs lc gl fs Mem lc' als' Mem' B1' Rid oResult tr ->
  uniq gl ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro los nts Ps1) S1 ->
  moduleInSystem (module_intro los nts Ps2) S2 ->
  lookupFdefViaGV (los, nts) Ps1 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists lb2, exists B2', exists n, exists slc,
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' /\
    lookupFdefViaGV (los, nts) Ps2 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2 /\
    LLVMopsem.dbFdef fv rt lp S2 (los, nts) Ps2 ECs lc gl fs Mem slc als' Mem' B2' Rid oResult tr /\
    subAL _ slc lc'.
Proof.
  intros.
  apply llvmop_dbFdef__seop_dbFdef in H; auto.
  apply _tv_fdef__is__correct with (fid:=fid)(Ps2:=Ps2)(S2:=S2)(la:=la)(lb1:=lb1) in H; auto.
  destruct H as [lb2 [B2' [n [slc [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]]]]]].
  exists lb2. exists B2'. exists n. exists slc.
  repeat (split; auto).
    apply seop_dbFdef__llvmop_dbFdef; auto.
Qed.
*)

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)

