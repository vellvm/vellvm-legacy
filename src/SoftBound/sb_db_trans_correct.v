Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import sb_db_trans.
Require Import ssa_def.
Require Import ssa_lib.
Require Import trace.
Require Import Memory.
Require Import genericvalues.
Require Import alist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import sb_def.
Require Import symexe_def.
Require Import sb_tactic.
Require Import sub_tv.
Require Import sb_db_pp.
Require Import symexe_tactic.
Require Import ssa_dynamic.
Require Import symexe_lib.
Require Import sb_metadata.

Import SBpass.

Lemma in_codom_of_rmap : forall rm2 pid bid eid,
  lookupAL (id * id) rm2 pid = ret (bid, eid) ->
  bid `in` codom rm2 /\ eid `in` codom rm2.
Proof.
  induction rm2; intros pid bid eid J.
    inversion J.  

    simpl in J.
    destruct a.
    destruct (pid == a); subst.
      inv J.
      simpl. auto.

      apply IHrm2 in J.
      destruct J as [J1 J2].
      simpl. destruct p.
      auto.
Qed.

Lemma reg_simulation__updateAddAL : forall mi TD gl M1 M2 rm1 rm2 lc1 lc2 i0 gv 
    gv',
  reg_simulation mi TD gl rm1 rm2 M1 M2 lc1 lc2 ->
  i0 `notin` codom rm2 ->
  gv_inject mi gv gv' ->
  reg_simulation mi TD gl rm1 rm2 M1 M2 (updateAddAL GenericValue lc1 i0 gv)
    (updateAddAL GenericValue lc2 i0 gv').
Proof.
  intros mi TD gl M1 M2 rm1 rm2 lc1 lc2 i0 gv gv' Hsim Hnotin. 
  destruct Hsim as [J1 J2].    
  split.
    intros i1 gv1 J.
    destruct (id_dec i0 i1); subst.
      rewrite lookupAL_updateAddAL_eq in *; auto.
      inv J.
      exists gv'. auto.
    
      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.

    intros vp bgv1 egv1 mt J.
    apply J2 in J. 
    destruct J as [t2 [bv2 [ev2 [bgv2 [egv2 [J11 [J12 [J13 [J14 J15]]]]]]]]].
    exists t2. exists bv2. exists ev2. exists bgv2. exists egv2.
    split; auto.
    destruct vp as [pid |]; simpl in J11.
      case_eq (lookupAL (id * id) rm2 pid).
        intros [bid eid] J.
        rewrite J in J11.    
        inv J11.
        simpl.
        assert (J':=J).
        apply in_codom_of_rmap in J'.    
        destruct J' as [J16 J17].      
        rewrite <- lookupAL_updateAddAL_neq; try solve [fsetdec].
        rewrite <- lookupAL_updateAddAL_neq; try solve [fsetdec].
        repeat (split; auto).

        intro J.
        rewrite J in J11. inversion J11.

      case_eq (SoftBound.get_const_metadata c).
        intros [[bid eid] mt'] J.
        rewrite J in J11.
        inv J11.
        simpl in *.
        repeat (split; auto).

        intro J.  rewrite J in J11.
        destruct (Constant.getTyp c); inv J11.
        simpl in *.
        repeat (split; auto).
Qed.

Lemma zeroconst2GV__gv_inject_refl : forall TD t gv mi,
  zeroconst2GV TD t = Some gv ->
  gv_inject mi gv gv.
Admitted.

(*Lemma gv_inject__eq__sizeGenericValue : forall mi gv1 gv2,
  gv_inject mi gv1 gv2 ->
  sizeGenericValue gv1 = sizeGenericValue gv2.
Admitted.*)

Lemma val_list_inject_app : forall mi vs1 vs1' vs2 vs2',
  val_list_inject mi vs1 vs2 ->
  val_list_inject mi vs1' vs2' ->
  val_list_inject mi (vs1++vs1') (vs2++vs2').
Admitted.

Lemma gv_inject_app : forall mi gv1 gv1' gv2 gv2',
  gv_inject mi gv1 gv2 ->
  gv_inject mi gv1' gv2' ->
  gv_inject mi (gv1++gv1') (gv2++gv2').
Admitted.

Lemma global_gv_inject_refl_aux : forall maxb mi Mem1 Mem2 gv,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_global maxb gv ->
  gv_inject mi gv gv.
Proof.
  unfold gv_inject.
  induction gv; intros; simpl; auto.
    destruct a.
    remember (split gv) as R.
    destruct R.
    split; auto.
      destruct v; simpl in *; try solve 
        [destruct (@IHgv H H0) as [J _]; eauto].

        destruct H0 as [H1 H2].
        destruct (@IHgv H H2) as [J _].
        inversion H.
        apply mi_globals0 in H1.
        apply val_cons_inject; auto.
          apply val_inject_ptr with (delta:=0); auto.
            rewrite Int.add_zero; auto.
Qed.

Lemma wf_globals__wf_global : forall mgb gl gv i0,
  wf_globals mgb gl ->
  ret gv = lookupAL GenericValue gl i0 ->
  wf_global mgb gv.
Proof.
  induction gl; intros.
    inversion H0.

    destruct a. simpl in *.
    destruct H as [J1 J2].
    destruct (i0 == i1); subst; eauto.
      inv H0; auto.
Qed.      

Lemma global_gv_inject_refl : forall maxb mi Mem1 Mem2 gl i0 gv,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_globals maxb gl ->
  lookupAL _ gl i0 = Some gv ->
  gv_inject mi gv gv.
Proof.
  intros. 
  eapply global_gv_inject_refl_aux; eauto.
    eapply wf_globals__wf_global; eauto.
Qed.
    
Lemma simulation__mtrunc : forall mi TD top t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mtrunc TD top t1 gv1 t2 = Some gv2 ->
  exists gv2',
    mtrunc TD top t1 gv1' t2 = Some gv2' /\
    gv_inject mi gv2 gv2'.
Admitted.

Lemma simulation__mext : forall mi TD eop t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mext TD eop t1 gv1 t2 = Some gv2 ->
  exists gv2',
    mext TD eop t1 gv1' t2 = Some gv2' /\
    gv_inject mi gv2 gv2'.
Admitted.

Lemma simulation__mbop : forall mi TD op bsz gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mbop TD op bsz gv1 gv2 = Some gv3 ->
  exists gv3',
    mbop TD op bsz gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__mfbop : forall mi TD op fp gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfbop TD op fp gv1 gv2 = Some gv3 ->
  exists gv3',
    mfbop TD op fp gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__mcast : forall mi TD Mem1 Mem2 op t1 gv1 gv1' t2 gv2,
  gv_inject mi gv1 gv1' ->
  Mem.mem_inj mi Mem1 Mem2 ->  
  mcast TD Mem1 op t1 gv1 t2 = Some gv2 ->
  exists gv2',
    mcast TD Mem2 op t1 gv1' t2 = Some gv2' /\
    gv_inject mi gv2 gv2'.
Admitted.

Lemma simulation__micmp : forall mi TD Mem1 Mem2 c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  Mem.mem_inj mi Mem1 Mem2 ->  
  micmp TD Mem1 c t gv1 gv2 = Some gv3 ->
  exists gv3',
    micmp TD Mem2 c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__mfcmp : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfcmp TD c t gv1 gv2 = Some gv3 ->
  exists gv3',
    mfcmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__GV2ptr : forall mi TD gv1 gv1' v,
  gv_inject mi gv1 gv1' ->
  GV2ptr TD (getPointerSize TD) gv1 = Some v ->
  exists v',
    GV2ptr TD (getPointerSize TD) gv1' = Some v' /\
    Values.val_inject mi v v'.
Admitted.

Lemma simulation__mgep : forall mi TD v v' v0 t0 l1,
  Values.val_inject mi v v' ->
  mgep TD t0 v l1 = Some v0 ->
  exists v0',
    mgep TD t0 v' l1 = Some v0' /\
    Values.val_inject mi v0 v0'.
Admitted.
   
Lemma gv_inject__eq__isGVZero : forall mi TD gv gv',
  gv_inject mi gv gv' ->
  isGVZero TD gv = isGVZero TD gv'.
Admitted.

Lemma simulation__extractGenericValue : forall mi gv1 gv1' TD t1 l0 gv,
  gv_inject mi gv1 gv1' ->
  extractGenericValue TD t1 gv1 l0 = Some gv ->
  exists gv',
    extractGenericValue TD t1 gv1' l0 = Some gv' /\
    gv_inject mi gv gv'.
Admitted.

Lemma simulation__insertGenericValue : forall mi gv1 gv1' TD t1 l0 gv t2 gv2 
                                              gv2',
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  insertGenericValue TD t1 gv1 l0 t2 gv2 = Some gv ->
  exists gv',
    insertGenericValue TD t1 gv1' l0 t2 gv2' = Some gv' /\
    gv_inject mi gv gv'.
Admitted.

Lemma gv_inject_uninits : forall mi n, gv_inject mi (uninits n) (uninits n).
Admitted.

Definition sb_mem_inj__const2GV_prop (c:const) := forall maxb mi Mem1 Mem2 TD gl 
    gv t,
  Mem.mem_inj mi Mem1 Mem2 ->
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_globals maxb gl -> 
  _const2GV TD Mem1 gl c = Some (gv,t) ->
  exists gv',
    _const2GV TD Mem2 gl c = Some (gv',t) /\
    gv_inject mi gv gv'.

Definition sb_mem_inj__list_const2GV_prop (lc:list_const) := 
  forall maxb mi Mem1 Mem2 TD gl,
  Mem.mem_inj mi Mem1 Mem2 ->
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_globals maxb gl -> 
  (forall gv, 
    _list_const_arr2GV TD Mem1 gl lc = Some gv ->
    exists gv',
      _list_const_arr2GV TD Mem2 gl lc = Some gv' /\
      gv_inject mi gv gv'
  ) /\
  (forall gv t a, 
    _list_const_struct2GV TD Mem1 gl lc = Some (gv,t,a) ->
    exists gv',
      _list_const_struct2GV TD Mem2 gl lc = Some (gv',t,a) /\
      gv_inject mi gv gv'
  ).

Lemma sb_mem_inj__const2GV_mutrec :
  (forall c, sb_mem_inj__const2GV_prop c) *
  (forall lc, sb_mem_inj__list_const2GV_prop lc).
Proof.
  apply const_mutrec; 
    unfold sb_mem_inj__const2GV_prop, sb_mem_inj__list_const2GV_prop;
    intros; simpl in *; eauto.
Case "zero".
  remember (zeroconst2GV TD t) as R.
  destruct R; inv H2.
  exists gv. split; eauto using zeroconst2GV__gv_inject_refl.
Case "int".
  inv H2.
  exists (val2GV TD
            (Vint (Size.to_nat s - 1)
               (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z i0)))
            (AST.Mint (Size.to_nat s - 1))).
  split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].
Case "float".
  destruct f; inv H2.
    exists (val2GV TD (Vfloat f0) AST.Mfloat32).
    split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].

    exists (val2GV TD (Vfloat f0) AST.Mfloat64).
    split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].
Case "undef".
  remember (getTypeSizeInBits TD t) as R.
  destruct R; inv H2.
  exists (val2GV TD Vundef (AST.Mint (n - 1))).
  split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].
Case "null".
  inv H2.
  exists (val2GV TD (Vptr Mem.nullptr (Int.repr 31 0)) (AST.Mint 31)).
  split; auto. 
    unfold val2GV, gv_inject; simpl.
    split; auto.
      apply val_cons_inject; auto.
      apply val_inject_ptr with (delta:=0); auto.
      destruct H0. auto.
Case "arr". 
  eapply H with (TD:=TD)(gl:=gl) in H2; eauto.
  destruct H2; eauto.
  remember (_list_const_arr2GV TD Mem1 gl l0) as R.
  destruct R; inv H3.
  destruct (@H2 gv) as [gv' [J1 J2]]; auto.
  exists gv'. rewrite J1; auto.

Case "struct". 
  eapply H with (TD:=TD)(gl:=gl) in H2; eauto.
  destruct H2 as [H00 H01].
  remember (_list_const_struct2GV TD Mem1 gl l0) as R.
  destruct R as [[[gv1 t1] a1]|]; inv H3.
  destruct (@H01 gv1 t1 a1) as [gv' [H02 H03]]; auto.
  rewrite H02; auto.
  destruct (getTypeAllocSize TD (typ_struct t1)); try solve [inv H4].
  destruct l0; inv H4.
    exists (uninits s).
    split; auto. 
      apply gv_inject_uninits.

    exists (gv' ++ uninits (a1 - s)).
    split; auto.
      apply gv_inject_app; auto.
        apply gv_inject_uninits.

Case "gid".
  remember (lookupAL GenericValue gl i0) as R.
  destruct R; inv H2.
  exists gv. split; eauto using global_gv_inject_refl.
Case "trunc".
  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1']|]; inv H3.
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  rewrite J1.
  remember (mtrunc TD t t1' gv1 t0) as R1.
  destruct R1; inv H5.
  symmetry in HeqR1.
  eapply simulation__mtrunc in HeqR1; eauto.
  destruct HeqR1 as [gv2' [J3 J4]].
  rewrite J3.
  exists gv2'. split; auto.
Case "ext".
  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1']|]; inv H3.
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  rewrite J1.
  remember (mext TD e t1' gv1 t) as R1.
  destruct R1; inv H5.
  symmetry in HeqR1.
  eapply simulation__mext in HeqR1; eauto.
  destruct HeqR1 as [gv2' [J3 J4]].
  rewrite J3.
  exists gv2'. split; auto.
Case "cast".
  remember (_const2GV TD Mem1 gl c0) as R.
  destruct R as [[gv1 t1']|]; inv H3.
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  rewrite J1.
  remember (mcast TD Mem1 c t1' gv1 t) as R1.
  destruct R1; inv H5.
  symmetry in HeqR1.
  eapply simulation__mcast in HeqR1; eauto.
  destruct HeqR1 as [gv2' [J3 J4]].
  rewrite J3.
  exists gv2'. split; auto.
Case "gep".
  remember (_const2GV TD Mem1 gl c) as R1.
  destruct R1 as [[gv1 t1]|]; inv H4.
  destruct t1; inv H6.
  remember (getConstGEPTyp l0 (typ_pointer t1)) as R2.
  destruct R2; inv H5.
  remember (GV2ptr TD (getPointerSize TD) gv1) as R3.
  destruct R3; inv H6.
    remember (intConsts2Nats TD l0) as R4.
    destruct R4; inv H5.
      remember (mgep TD t1 v l1) as R5.
      destruct R5; inv H6.
      symmetry in HeqR1.
      eapply H in HeqR1; eauto.
      destruct HeqR1 as [gv1' [J1 J2]].
      rewrite J1.
      symmetry in HeqR3.
      eapply simulation__GV2ptr in HeqR3; eauto.
      destruct HeqR3 as [v' [J3 J4]].
      rewrite J3.  
      symmetry in HeqR5.
      eapply simulation__mgep in HeqR5; eauto.
      destruct HeqR5 as [v0' [J5 J6]].
      rewrite <- HeqR2. rewrite J5.
      exists (ptr2GV TD v0').
      split; auto.
        unfold ptr2GV, val2GV, gv_inject. simpl. auto.

      admit. admit. admit.

  remember (_const2GV TD Mem1 gl c) as R2.
  destruct R2 as [[gv2 t2]|]; inv H5.
  remember (_const2GV TD Mem1 gl c0) as R3.
  destruct R3 as [[gv3 t3]|]; inv H7.
  remember (_const2GV TD Mem1 gl c2) as R4.
  destruct R4 as [[gv4 t4]|]; inv H6.
  symmetry in HeqR2. 
  eapply H in HeqR2; eauto.
  destruct HeqR2 as [gv2' [J1 J2]].
  rewrite J1.
  symmetry in HeqR3. 
  eapply H0 in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H1 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  erewrite <- gv_inject__eq__isGVZero; eauto.
  destruct (isGVZero TD gv2); inv H7.
    exists gv4'. split; auto.
    exists gv3'. split; auto.

  remember (_const2GV TD Mem1 gl c0) as R3.
  destruct R3 as [[gv3 t3]|]; inv H4.
  remember (_const2GV TD Mem1 gl c2) as R4.
  destruct R4 as [[gv4 t4]|]; inv H6.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  remember (micmp TD Mem1 c t3 gv3 gv4) as R1.
  destruct R1; inv H5.
  symmetry in HeqR1.
  eapply simulation__micmp in HeqR1; eauto.
  destruct HeqR1 as [gv' [J7 J8]].
  rewrite J7.
  exists gv'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R3.
  destruct R3 as [[gv3 t3]|]; inv H4.
  destruct t3; inv H6.
  remember (_const2GV TD Mem1 gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; inv H5.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  remember (mfcmp TD f f0 gv3 gv4) as R1.
  destruct R1; inv H6.
  symmetry in HeqR1.
  eapply simulation__mfcmp in HeqR1; eauto.
  destruct HeqR1 as [gv' [J7 J8]].
  rewrite J7.
  exists gv'. split; auto.
     
  admit. admit.
(*
  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1]|]; inv H4.
  remember (Constant.getTyp c) as R1.
  destruct R1; inv H6.       
  remember (getSubTypFromConstIdxs l0 t0) as R2.
  destruct R2; inv H5.   
  remember (extractGenericValue TD t1 gv1 l0) as R3.
  destruct R3; inv H6.   
  symmetry in HeqR. 
  eapply H in HeqR; eauto.
  destruct HeqR as [gv1' [J1 J2]].
  rewrite J1.
  symmetry in HeqR3.
  eapply simulation__extractGenericValue in HeqR3; eauto.
  destruct HeqR3 as [gv' [J3 J4]].
  rewrite J3.
  exists gv'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1]|]; inv H5.
  remember (_const2GV TD Mem1 gl c0) as R2.
  destruct R2 as [[gv2 t2]|]; inv H7.
  remember (Constant.getTyp c0) as R1.
  destruct R1; inv H6.       
  remember (insertGenericValue TD t1 gv1 l0 t2 gv2) as R3.
  destruct R3; inv H7.   
  symmetry in HeqR. 
  eapply H in HeqR; eauto.
  destruct HeqR as [gv1' [J1 J2]].
  rewrite J1.
  symmetry in HeqR2. 
  eapply H0 in HeqR2; eauto.
  destruct HeqR2 as [gv2' [J3 J4]].
  rewrite J3.
  symmetry in HeqR3.
  eapply simulation__insertGenericValue in HeqR3; eauto.
  destruct HeqR3 as [gv' [J5 J6]].
  rewrite J5.
  exists gv'. split; auto.
*)

  remember (_const2GV TD Mem1 gl c) as R3.
  destruct R3 as [[gv3 t3]|]; inv H4.
  destruct t3; inv H6.
  remember (_const2GV TD Mem1 gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; inv H5.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  remember (mbop TD b s gv3 gv4) as R1.
  destruct R1; inv H6.
  symmetry in HeqR1.
  eapply simulation__mbop in HeqR1; eauto.
  destruct HeqR1 as [gv' [J7 J8]].
  rewrite J7.
  exists gv'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R3.
  destruct R3 as [[gv3 t3]|]; inv H4.
  destruct t3; inv H6.
  remember (_const2GV TD Mem1 gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; inv H5.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  remember (mfbop TD f f0 gv3 gv4) as R1.
  destruct R1; inv H6.
  symmetry in HeqR1.
  eapply simulation__mfbop in HeqR1; eauto.
  destruct HeqR1 as [gv' [J7 J8]].
  rewrite J7.
  exists gv'. split; auto.

  split.
    intros gv J.
    inv J.
    exists nil. unfold gv_inject. simpl. split; auto.
 
    intros gv t a J.
    inv J.
    exists nil. unfold gv_inject. simpl. split; auto.  

  assert (H1':=H3).
  eapply H0 with (TD:=TD)(gl:=gl) in H1'; eauto.
  destruct H1' as [H10 H11].
  split; intros.
    remember (_list_const_arr2GV TD Mem1 gl l0) as R3.
    destruct R3 as [gv3|]; inv H4.
    remember (_const2GV TD Mem1 gl c) as R4.
    destruct R4 as [[gv4 t4]|]; inv H6.
    symmetry in HeqR4.
    eapply H in HeqR4; eauto.
    destruct HeqR4 as [gv4' [J1 J2]].
    rewrite J1.
    destruct (@H10 gv3) as [gv3' [J3 J4]]; auto.
    rewrite J3.
    destruct (getTypeStoreSize TD t4); try solve [inv H5].
    destruct (getTypeAllocSize TD t4); inv H5.
    exists ((gv3' ++ gv4') ++ uninits (s - n)).
    split; auto.    
      apply gv_inject_app.
        apply gv_inject_app; auto.
          apply gv_inject_uninits.

    remember (_list_const_struct2GV TD Mem1 gl l0) as R3.
    destruct R3 as [[[gv3 t3] a3]|]; inv H4.
    remember (_const2GV TD Mem1 gl c) as R4.
    destruct R4 as [[gv4 t4]|]; inv H6.
    symmetry in HeqR4.
    eapply H in HeqR4; eauto.
    destruct HeqR4 as [gv4' [J1 J2]].
    rewrite J1.
    symmetry in HeqR3.
    destruct (@H11 gv3 t3 a3) as [gv3' [J3 J4]]; auto.
    rewrite J3.
    destruct (getTypeStoreSize TD t4); inv H5.
    destruct (getTypeAllocSize TD t4); inv H6.
    exists (gv3' ++ gv4' ++ uninits (s - n)).
    split; auto.
      apply gv_inject_app; auto.
        apply gv_inject_app; auto.
          apply gv_inject_uninits.
Qed.

Lemma sb_mem_inj___const2GV : forall maxb mi Mem1 Mem2 TD gl c gv t,
  Mem.mem_inj mi Mem1 Mem2 ->
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_globals maxb gl -> 
  _const2GV TD Mem1 gl c = Some (gv,t) ->
  exists gv',
    _const2GV TD Mem2 gl c = Some (gv',t) /\
    gv_inject mi gv gv'.
Proof.
  destruct sb_mem_inj__const2GV_mutrec as [J _].
  unfold sb_mem_inj__const2GV_prop in J. eauto.
Qed.

Lemma sb_mem_inj__const2GV : forall maxb mi Mem Mem' TD gl c gv,
  Mem.mem_inj mi Mem Mem' ->
  wf_sb_mi maxb mi Mem Mem' ->
  wf_globals maxb gl -> 
  const2GV TD Mem gl c = Some gv ->
  exists gv',
    const2GV TD Mem' gl c = Some gv' /\
    gv_inject mi gv gv'.
Proof.
  intros.
  unfold const2GV in *.
  remember (_const2GV TD Mem0 gl c) as R.
  destruct R; try solve [inversion H2].
  destruct p.
  inv H2.
  symmetry in HeqR.
  eapply sb_mem_inj___const2GV in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  exists gv'. rewrite J1. auto.
Qed.

Lemma simulation__getOperandValue : forall maxb mi rm rm2 lc lc2 TD MM Mem Mem2 
    gl v gv mgb,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl rm rm2 Mem Mem2 lc lc2 ->
  mem_simulation mi TD mgb MM Mem Mem2 ->
  getOperandValue TD Mem v lc gl = ret gv ->
  exists gv', 
    getOperandValue TD Mem2 v lc2 gl = ret gv' /\
    gv_inject mi gv gv'.
Proof.
  intros maxb mi rm rm2 lc lc2 TD MM Mem Mem2 gl v gv mgb Hwfg H0 H1 H2 H3.
  unfold getOperandValue in *.
  destruct v.
    destruct H1 as [H1 _]; auto.

    destruct H2 as [H2 _].
    eapply sb_mem_inj__const2GV; eauto.
Qed.

Lemma simulation__BOP : forall maxb mi rm rm2 lc lc2 TD MM Mem Mem2 gl bop0 sz0 
    v1 v2 gv3 mgb,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl rm rm2 Mem Mem2 lc lc2 ->
  mem_simulation mi TD mgb MM Mem Mem2 ->
  BOP TD Mem lc gl bop0 sz0 v1 v2 = ret gv3 ->
  exists gv3',
    BOP TD Mem2 lc2 gl bop0 sz0 v1 v2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi rm rm2 lc lc2 TD MM Mem Mem2 gl bop0 sz0 v1 v2 gv3 mgb Hwfg H0 
    H1 H2 H3.
  unfold BOP in *.
  remember (getOperandValue TD Mem v1 lc gl) as R1.
  destruct R1; inv H3.
  remember (getOperandValue TD Mem v2 lc gl) as R2.
  destruct R2; inv H4.
  symmetry in HeqR1.
  eapply simulation__getOperandValue in HeqR1; eauto.
  destruct HeqR1 as [g' [J1 J2]].
  rewrite J1.
  symmetry in HeqR2.
  eapply simulation__getOperandValue in HeqR2; eauto.
  destruct HeqR2 as [g0' [J3 J4]].
  rewrite J3.
  eapply simulation__mbop in H3; eauto.
Qed.

Lemma lookupAL_wf_globals : forall mgb gl g ofs b i0 TD,
  wf_globals mgb gl ->
  0 <= mgb ->
  GV2val TD g = ret Vptr b ofs ->
  ret g = lookupAL GenericValue gl i0 ->
  b <= mgb.
Proof.
  induction gl; intros.
    inversion H2.

    destruct a. simpl in *.
    destruct H as [J1 J2].
    destruct (i0 == i1); subst; eauto.
      inv H2.
      unfold GV2val in H1.
      destruct g0; inv H1.
      destruct p.
      destruct g0; inv H2.
      simpl in J1.
      destruct J1; auto.
Qed.      

Lemma const2GV_lt_nextblock_aux : forall TD Mem mgb gl c g t b ofs,
  wf_const c -> 
  wf_globals mgb gl ->
  0 <= mgb ->
  _const2GV TD Mem gl c = Some (g, t) -> 
  GV2val TD g = Some (Vptr b ofs) ->
  b <= mgb.
Admitted.
(*
Proof.
  intros TD Mem mgb gl c g t b ofs Hwfc Hwfg Hblock Hc2g Hg2v.
  generalize dependent b.
  generalize dependent ofs.
  generalize dependent t.
  generalize dependent g.
  induction c; intros; simpl in *; try solve [
      inv Hc2g; unfold GV2val, val2GV, ptr2GV in Hg2v; inv Hg2v
    ].

    admit. (* zero *)

    destruct f; inv Hc2g; unfold GV2val, val2GV, ptr2GV in Hg2v; inv Hg2v.

    destruct (getTypeSizeInBits TD t); inv Hc2g.
    unfold GV2val, val2GV, ptr2GV in Hg2v.
    inv Hg2v.

    inv Hc2g; unfold GV2val, val2GV, ptr2GV in Hg2v; inv Hg2v.
    assert (J:=@Mem.nextblock_pos Mem).
    unfold Mem.nullptr. auto with zarith.

    admit. (*arr*)
    admit. (*struct*)

    remember (lookupAL GenericValue gl i0) as R.
    destruct R; inv Hc2g.
    eauto using lookupAL_wf_globals.

    remember (_const2GV TD Mem gl c) as R.
    destruct R; inv Hc2g.
    destruct p.
    unfold mtrunc in H0.
    remember (GV2val TD g0) as R'.
    destruct R'; inv H0.
    destruct v; inv H1.
      destruct t2; inv H0.
        destruct t0; inv H1.
        destruct (eq_nat_dec wz s0); inv Hg2v.   
          unfold GV2val, val2GV, ptr2GV in Hg2v.
          destruct (le_lt_dec s s0); inv Hg2v.
      destruct t2; inv H0.
        destruct t0; inv H1.
        destruct (floating_point_order f1 f0); inv H0.   
        destruct f1; inv H1; unfold GV2val, val2GV, ptr2GV in Hg2v; inv Hg2v.

    remember (_const2GV TD Mem gl c) as R.
    destruct R; inv Hc2g.
    destruct p.
    unfold mext in H0.
    remember (GV2val TD g0) as R'.
    destruct t1; inv H0.
      destruct t; inv H1.
        remember (GV2val TD g0) as R'.
        destruct R'; inv H0.
        destruct v; inv H1.
        destruct e; inv H0; unfold GV2val, val2GV, ptr2GV in Hg2v; inv Hg2v.
      destruct t; inv H1.
        destruct (floating_point_order f f0); inv H0.   
        remember (GV2val TD g0) as R'.
        destruct R'; inv H1.
        destruct v; inv H0.
        destruct e; inv H1.
        rewrite Hg2v in HeqR'. inversion HeqR'.

    remember (_const2GV TD Mem gl c0) as R.
    destruct R; inv Hc2g.
    destruct p.
    unfold mcast in H0.
    destruct Hwfc as [Hwfc1 Hwfc2].
    destruct c.
      destruct t1; inv H0.
        destruct t; inv H1; eauto.
        destruct t; inv H1; eauto.
      destruct t1; inv H0.
        destruct t; inv H1; eauto.
        destruct t; inv H1; eauto.
      destruct t1; inv H0.
        destruct t; inv H1; eauto.
        destruct t; inv H1; eauto.
      destruct t1; inv H0.
        destruct t; inv H1; eauto.
        destruct t; inv H1; eauto.
      destruct t1; inv H0.
        destruct t; inv H1.
          remember (GV2val TD g0) as R'.
          destruct R'; inv H0.
          destruct v; inv H1.
          destruct (Mem.ptr2int Mem b0 0); inv H0; 
            unfold GV2val, val2GV, ptr2GV in Hg2v; inv Hg2v.

          unfold GV2val, val2GV, ptr2GV in Hg2v; inv Hg2v.
      contradict Hwfc1; auto.
      destruct t1; inv H0.
        destruct t; inv H1; eauto.
        destruct t; inv H1; eauto.

    destruct (Constant.getTyp c); inv Hc2g.
      destruct t0; inv H0.
      remember (_const2GV TD Mem gl c) as R.
      destruct R; inv H1.
      destruct p.
      destruct (getConstGEPTyp l0 (typ_pointer t0)); inv H0.
      remember (GV2ptr TD (getPointerSize TD) g0) as R'.
      destruct R'; inv H1.
      destruct (intConsts2Nats TD l0); inv H0.
      admit. (*gep*)

    remember (_const2GV TD Mem gl c2) as R1.
    destruct R1; inv Hc2g.
    destruct p.
    remember (_const2GV TD Mem gl c3) as R2.
    destruct R2; inv H0.
    remember (_const2GV TD Mem gl c4) as R3.
    destruct R3; inv H1.
    destruct Hwfc as [Hwfc2 [Hwfc3 Hwfc4]].
    destruct (isGVZero TD g0); inv H0; eauto.

    remember (_const2GV TD Mem gl c3) as R2.
    destruct R2; inv Hc2g.
    destruct p.
    remember (_const2GV TD Mem gl c4) as R3.
    destruct R3; inv H0.
    destruct p.
    unfold micmp in H1.
    destruct t0; inv H1.
    remember (GV2val TD g0) as R.
    destruct R; inv H0.
    destruct v; inv H1.
    remember (GV2val TD g1) as R'.   
    destruct R'; inv H0.
    destruct v; inv H1.
    admit. (*cmp*)

    admit. (*fcmp*)

    admit. (*extractvalue*)
    admit. (*insertvalue*)

    remember (_const2GV TD Mem gl c2) as R1.
    destruct R1; inv Hc2g.
    destruct p.
    destruct t0; inv H0. 
    remember (_const2GV TD Mem gl c3) as R2.
    destruct R2; inv H1.
    destruct p.
    admit. (*bop*)

    admit. (*fbop*)
Qed.
*)

Lemma const2GV__malloc_aux : forall TD Mem lo hi Mem' mb gl c mgb,
  wf_const c ->
  wf_globals mgb gl ->
  0 <= mgb < Mem.nextblock Mem ->
  Mem.alloc Mem lo hi = (Mem', mb) ->
  _const2GV TD Mem gl c = _const2GV TD Mem' gl c.
Proof.
  intros TD Mem lo hi Mem' mb gl c mgb Hwfc Hwfg Hmgb Halloc.
  induction c; simpl in *; subst; 
    try destruct Hwfc as [Hwfc1 [Hwfc2 Hwfc3]];
    try destruct Hwfc as [Hwfc1 Hwfc2];
    try solve 
    [ auto | rewrite IHc; auto | 
      rewrite IHc1; auto; rewrite IHc2; auto |
      rewrite IHc1; auto; rewrite IHc2; auto; rewrite IHc3; auto ].
    admit. (*arr*)
    admit. (*struct*)

    rewrite IHc; auto.
    destruct (_const2GV TD Mem' gl c0); auto.
    destruct p.
    unfold mcast, mptrtoint.
    destruct t0; auto.
      destruct c; auto.
        contradict Hwfc1; auto.
      destruct c; auto.
        destruct t; auto.
          remember (GV2val TD g) as R.
          destruct R; auto.
            destruct v; auto.
              erewrite Mem.ptr2int_alloc; eauto.
                assert (J:=Hwfc2).
                apply IHc in J.
                destruct Hmgb.
                eapply const2GV_lt_nextblock_aux in J; eauto with zarith.
                  clear - H0 J. eauto with zarith.

    admit.
Qed.  

Lemma const2GV__malloc : forall TD Mem lo hi Mem' mb gl c mgb ,
  wf_const c ->
  wf_globals mgb gl ->
  0 <= mgb < Mem.nextblock Mem ->
  Mem.alloc Mem lo hi = (Mem', mb) ->
  const2GV TD Mem gl c = const2GV TD Mem' gl c.
Proof.
  intros TD Mem lo hi Mem' mb gl c mgb Hwfc Hwfg Hmgb Halloc.
  unfold const2GV.
  erewrite const2GV__malloc_aux; eauto.
Qed.

Lemma alloc_getOperandValue_inv : forall Mem2 lo hi Mem2' mb2 TD v lc2 gl mgb,
  wf_value v ->
  wf_globals mgb gl ->
  0 <= mgb < Mem.nextblock Mem2 ->
  Mem.alloc Mem2 lo hi = (Mem2', mb2) ->
  getOperandValue TD Mem2 v lc2 gl = getOperandValue TD Mem2' v lc2 gl.
Proof.
  intros Mem2 lo hi Mem2' mb2 TD v lc2 gl mgb Hwfv Hwfg Hmgb Halloc.
  destruct v as [vid | ]; simpl in *; eauto using const2GV__malloc.
Qed.

Lemma malloc_getOperandValue_inv : 
  forall Mem2 tsz gn a0 Mem2' TD v lc2 gl mb2 mgb,
  wf_value v ->
  wf_globals mgb gl ->
  0 <= mgb < Mem.nextblock Mem2 ->
  malloc TD Mem2 tsz gn a0 = Some (Mem2', mb2) ->
  getOperandValue TD Mem2 v lc2 gl = getOperandValue TD Mem2' v lc2 gl.
Proof.
  intros Mem2 tsz gn a0 Mem2' TD v lc2 gl mb2 mgb Hwfv Hwfg Hmgb Hmalloc.
  unfold malloc in Hmalloc.
  remember (GV2int TD Size.ThirtyTwo gn) as R.
  destruct R; inv Hmalloc.
  case_eq (Mem.alloc Mem2 0 (Size.to_Z tsz * z)).
  intros m b Halloc.
  eapply alloc_getOperandValue_inv; eauto.
Qed.

Lemma gv_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  gv_inject f1 v v' ->
  gv_inject f2 v v'.
Proof.
  intros. 
  unfold gv_inject in *.
  destruct (split v).
  destruct (split v').
  destruct H0.
  split; eauto using val_list_inject_incr.
Qed.

Lemma mem_simulation__malloc : forall mi TD MM Mem Mem2 tsz gn align0 Mem' mb 
    mgb,
  wf_sb_mi mgb mi Mem Mem2 ->
  mem_simulation mi TD mgb MM Mem Mem2 ->
  malloc TD Mem tsz gn align0 = ret (Mem', mb) ->
  exists mi', exists Mem2', exists mb',
    malloc TD Mem2 tsz gn align0 = ret (Mem2', mb') /\
    wf_sb_mi mgb mi' Mem' Mem2' /\
    mem_simulation mi' TD mgb MM Mem' Mem2' /\
    Values.inject_incr mi mi' /\
    mi' mb = Some (mb', 0) /\
    (forall b, b <> mb -> mi b = mi' b).
Proof.
  intros mi TD MM Mem Mem2 tsz gn align0 Mem' mb mgb Hwfmi Hmsim Halloc.
  destruct Hmsim as [H1 [Hmgb H2]].
  unfold malloc in *.
  remember (GV2int TD Size.ThirtyTwo gn) as R.
  destruct R; try solve [inversion Halloc].
  remember (Mem.alloc Mem 0 (Size.to_Z tsz * z)) as R1.
  destruct R1 as [Mem1 mb1].
  inv Halloc.
  remember (Mem.alloc Mem2 0 (Size.to_Z tsz * z)) as R2.
  destruct R2 as [Mem2' mb2].
  exists (fun b => if zeq b mb then Some (mb2,0%Z) else mi b).
  exists Mem2'. exists mb2.
  split; auto.
  assert (inject_incr mi (fun b : Z => if zeq b mb then ret (mb2, 0) else mi b))
    as Hinject_incr.
    unfold inject_incr.
    intros b b' d H.
    destruct (zeq b mb); subst; auto.
      clear - Hwfmi H HeqR1.
      symmetry in HeqR1.
      apply Mem.alloc_result in HeqR1. subst.
      destruct Hwfmi.
      assert (mi (Mem.nextblock Mem) = None) as J.
        apply Hmap3; auto with zarith.
      rewrite H in J. inversion J.

  split; auto.
  Case "wfmi".
    clear - Hwfmi Hmgb HeqR2 HeqR1.
    inversion Hwfmi.
    symmetry in HeqR2, HeqR1. 
    assert (J:=HeqR2).
    apply Mem.nextblock_alloc in HeqR2.
    split.
    SCase "no_overlap".
      clear - Hno_overlap0 J Hmap4.
      unfold meminj_no_overlap in *.
      intros.      
      destruct (zeq b1 mb); subst.
        destruct (zeq b2 mb); subst.
          contradict H; auto.

          inv H0.
          apply Hmap4 in H1.
          apply Mem.alloc_result in J.
          subst. clear - H1. intro J. subst. contradict H1; zauto.
        destruct (zeq b2 mb); subst; eauto.
          inv H1.
          apply Hmap4 in H0.
          apply Mem.alloc_result in J.
          subst. clear - H0. intro J. subst. contradict H0; zauto.
    SCase "null".
      destruct (zeq Mem.nullptr mb); subst; auto.
        apply Mem.alloc_result in HeqR1.
        assert(J':=@Mem.nextblock_pos Mem).
        rewrite <- HeqR1 in J'.
        unfold Mem.nullptr in J'.
        contradict J'; zauto.
    SCase "map1".
      intros b H2.
      assert (J':=HeqR1).
      apply Mem.alloc_result in J'.
      apply Mem.nextblock_alloc in HeqR1.
      rewrite HeqR1 in H2.
      destruct (zeq b mb); subst; zeauto.
        contradict H2; zauto.
    SCase "map2".
      intros b1 b delta2 J'.
      rewrite HeqR2.
      destruct (zeq b1 mb); subst; zeauto.
        inv J'.
        apply Mem.alloc_result in J.
        subst.
        auto with zarith.
    SCase "freeblocks".
      intros b J'.
      destruct (zeq b mb); subst.
        apply Mem.valid_new_block in HeqR1.
        contradict HeqR1; auto.

        apply mi_freeblocks0.
          intro J1. apply J'.
          eapply Mem.valid_block_alloc; eauto.
    SCase "mappedblocks".
      intros b b' delta J'.
      destruct (zeq b mb); subst.
        inv J'.            
        apply Mem.valid_new_block in J; auto.
        eapply Mem.valid_block_alloc; eauto.
    SCase "range_block".
      intros b b' delta J'.
      destruct (zeq b mb); inv J'; subst; eauto.
    SCase "bounds".
      intros b b' delta J'.
      erewrite Mem.bounds_alloc; eauto.
      erewrite Mem.bounds_alloc with (m2:=Mem2'); eauto.
      unfold eq_block.
      destruct (zeq b mb); subst.
        inv J'.
        destruct (zeq b' b'); subst; auto.
          contradict n; auto.      

        destruct (zeq b' mb2); subst; eauto.
          apply Hmap4 in J'.
          apply Mem.alloc_result in J.
          rewrite J in J'. contradict J'; zauto.
    SCase "globals".
      intros b J'.
      destruct (zeq b mb); subst; eauto.
        assert (J'':=J').
        apply mi_globals0 in J'.
        destruct (valid_block_dec Mem mb).
          apply Mem.fresh_block_alloc in HeqR1.
          contradict HeqR1; auto.
     
          apply mi_freeblocks0 in n.        
          rewrite n in J'. inversion J'.
 
  split; auto.
  Case "msim".
    split.    
    SCase "msim1".
      clear H2.
      destruct H1.
      apply Mem.mk_mem_inj.
      SSCase "mi_access".
        intros b1 b2 d c ofs p J1 J2.
        destruct (zeq b1 mb); subst; inv J1.
        SSSCase "b1=mb".
          symmetry in HeqR1.
          symmetry in HeqR2.
          destruct J2 as [J21 J22].
          assert (0 <= ofs /\ ofs + size_chunk c <= Size.to_Z tsz * z) as EQ.
            destruct (Z_le_dec 0 ofs).
              destruct (Z_le_dec (ofs + size_chunk c) (Size.to_Z tsz * z)); auto.
                apply Mem.perm_alloc_3 with (ofs:=ofs+size_chunk c-1) (p:=p) in 
                  HeqR1; auto with zarith.
                unfold Mem.range_perm in J21.
                assert (ofs <= ofs + size_chunk c - 1 < ofs + size_chunk c) as J.
                  assert (J':=@Memdata.size_chunk_pos c).
                  auto with zarith.
                apply J21 in J.           
                contradict J; auto. 
              apply Mem.perm_alloc_3 with (ofs:=ofs) (p:=p) in HeqR1; 
                auto with zarith.
              unfold Mem.range_perm in J21.
              assert (ofs <= ofs < ofs + size_chunk c) as J.
                assert (J':=@Memdata.size_chunk_pos c).
                auto with zarith.
              apply J21 in J.           
              contradict J; auto. 

          apply Mem.valid_access_alloc_same with (chunk:=c)(ofs:=ofs+0) in HeqR2;
            auto with zarith.
            eapply Mem.valid_access_implies; eauto using perm_F_any.

        SSSCase "b1<>mb".
          eapply Mem.valid_access_alloc_other; eauto.
          eapply Mem.valid_access_alloc_inv with (b:=mb)(lo:=0)
            (hi:=Size.to_Z tsz * z)(p:=p) in J2; eauto.
          destruct (eq_block); subst; try solve [eauto | contradict n; auto].

      SSCase "mi_memval".
Transparent Mem.alloc.
        intros b1 ofs b2 d J1 J2.
        injection HeqR1. intros NEXT MEM.
        injection HeqR2. intros NEXT2 MEM2.
        destruct Mem2. destruct Mem2'. destruct Mem. destruct Mem'. 
        inv MEM.
        inv MEM2. clear HeqR1 HeqR2.
        simpl in *.
        unfold Mem.perm in *. simpl in *.
        clear maxaddress_pos0 conversion_props0 maxaddress_pos2 
              conversion_props2.
        unfold update.     
        destruct (zeq b1 nextblock1); subst; inv J1.
        SSSCase "b1=nextblock1".
          destruct (zeq b2 b2) as [e | n]; 
            try solve [contradict n; auto].
          apply memval_inject_undef.

        SSSCase "b1<>mb".
          destruct (zeq b2 nextblock); subst.
            clear - H0 Hwfmi.
            destruct Hwfmi. simpl in *.
            apply Hmap4 in H0.
            contradict H0; auto with zarith.

            apply Memdata.memval_inject_incr with (f:=mi); auto.
              apply mi_memval; auto.
                clear - J2 n.
                unfold update in J2.
                destruct (zeq b1 nextblock1); subst; 
                  try solve [auto | contradict n; auto].

Global Opaque Mem.alloc.

    split.
    SCase "mgb".
      clear - Hmgb HeqR2.
      symmetry in HeqR2.
      apply Mem.nextblock_alloc in HeqR2.
      rewrite HeqR2.
      auto with zarith.

    SCase "msim2".
      clear H1.
      intros lc2 gl b ofs bgv egv als addrb0 addre0 bid0 eid0 v pgv' Hwfv Hwfg 
        J1 J2 J3.
      erewrite <- alloc_getOperandValue_inv with (Mem2:=Mem2) in J3; eauto.
        assert (gv_inject mi (ptr2GV TD (Vptr b ofs)) pgv') as W.
          clear - Hwfv Hwfg J3 HeqR2 J2 Hmgb.
          admit. (* from J3 HeqR2 J2 *)
        apply H2 with (lc2:=lc2)(gl:=gl)(als:=als)(addrb:=addrb0)(addre:=addre0)
          (bid0:=bid0)(eid0:=eid0)(v:=v)(pgv':=pgv') in J1; eauto.
        destruct J1 as 
          [bgv' [egv' [Mem21 [J37 [J33 [J34 J35]]]]]].
        clear H2.
        assert (exists Mem21', 
          dbCmds TD gl lc2 als Mem2'
             (insn_call fake_id true sb_call_attrs get_mmetadata_typ 
                get_mmetadata_fn
                ((p8, v)
                 :: (p8, value_id addrb0) :: (p8, value_id addre0) :: nil)
              :: insn_load bid0 p8 (value_id addrb0) Align.Zero
                 :: insn_load eid0 p8 (value_id addre0) Align.Zero :: nil)
             (updateAddAL GenericValue
               (updateAddAL GenericValue lc2 bid0 bgv') eid0 egv') 
             als Mem21' trace_nil /\
          Mem.mem_inj inject_id Mem2' Mem21') as J'.
          eapply get_mmetadata_fn__alloc; eauto.

        destruct J' as [Mem21' [J1' J2']].
        exists bgv'. exists egv'. exists Mem21'.
        split; auto.
        split; eauto using gv_inject_incr.

  split; auto.
  split.
    destruct (zeq mb mb); auto.
      contradict n; auto.

    intros.
    destruct (zeq b mb); subst; auto.
      contradict H; auto.
Qed.

Lemma veq_refl : forall M v, veq M v v = true.
Proof.
  destruct v; simpl; auto.
Admitted.

Lemma gveq_refl : forall M gv, gveq M gv gv = true.
Admitted.

Lemma gveq__GV2val__veq : forall M gv1 gv2 TD v1, 
  gveq M gv1 gv2 = true ->
  GV2val TD gv1 = Some v1 ->
  exists v2, GV2val TD gv2 = Some v2 /\ veq M v1 v2.
Proof.
  intros M gv1 gv2 TD v1 H1 H2.
  unfold GV2val in H2.
  destruct gv1; inv H2.
  destruct p.
  destruct gv1; inv H0.
  simpl in H1.
  destruct gv2; inv H1.
  destruct p.
  bdestruct3 H0 as H1 H2 H3.
  destruct gv2.
    exists v. simpl. auto.
    inversion H3.
Qed.

Lemma simulation__eq__GV2int : forall mi gn gn' TD,
  gv_inject mi gn gn' ->
  GV2int TD Size.ThirtyTwo gn = GV2int TD Size.ThirtyTwo gn'.
Admitted.

Lemma simulation__mload : forall mi TD MM Mem0 Mem2 gvp align0 gv t gvp2 mgb,
  wf_sb_mi mgb mi Mem0 Mem2 ->
  mem_simulation mi TD mgb MM Mem0 Mem2 ->
  mload TD Mem0 gvp t align0 = ret gv ->
  gv_inject mi gvp gvp2 ->
  exists gv2, mload TD Mem2 gvp2 t align0 = ret gv2 /\ gv_inject mi gv gv2.
Proof.
  intros mi TD MM Mem0 Mem2 gvp align0 gv t gvp2 mgb Hwfmi Hmsim Hmload Hginject.
  unfold mload in *.
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion Hmload].
  destruct v; try solve [inversion Hmload].
  remember (typ2memory_chunk t) as R'.
  destruct R'; try solve [inversion Hmload].
  remember (Mem.load m Mem0 b (Int.signed 31 i0)) as R1.
  destruct R1; try solve [inversion Hmload].
  unfold GV2ptr in *.
  destruct gvp; inv HeqR.
  destruct p.
  destruct v0; inv H0.
  destruct gvp; inv H1.
  unfold gv_inject in *.
  simpl in Hginject.
  remember (split gvp2) as R2.
  destruct R2; simpl in Hginject.
  destruct Hginject as [J1 J2].
  inversion J1; subst.
  inversion H3; subst.
  inversion H1; subst.
  destruct gvp2; try solve [inversion HeqR2].
  destruct p. simpl in HeqR2.
  remember (split gvp2) as R3.
  destruct R3; inv HeqR2.
  destruct gvp2.
    inv Hmload.
    symmetry in HeqR1.
    destruct Hmsim as [Hmsim _].
    eapply Mem.load_inj in HeqR1; eauto.
    destruct HeqR1 as [v2 [J2 J3]].
    exists (val2GV TD v2 m).
    split.
      inversion_clear Hwfmi.
      apply mi_range_block0 in H2. subst.
      rewrite Int.add_zero.
      assert (Int.signed 31 i1 + 0 = Int.signed 31 i1) as EQ. zauto.
      rewrite EQ in J2. rewrite J2. auto.

      unfold val2GV. simpl. 
      split; auto.

    destruct p. simpl in HeqR3. destruct (split gvp2). inversion HeqR3.
Qed.

Lemma const2GV__gv_inject_refl : forall TD M gl c gv mi,
  const2GV TD M gl c = Some gv ->
  gv_inject mi gv gv.
Admitted.

Lemma notin_codom__neq : forall rm d id0 id1 bid eid,
  AtomSetImpl.inter d (codom rm) [<=] {} ->
  id0 `in` d ->
  Some (bid, eid) = lookupAL _ rm id1 ->
  id0 <> bid /\ id0 <> eid.
Proof.
  induction rm; intros d id0 id1 bid eid J1 J2 J3.
    inversion J3.

    destruct a. destruct p. simpl in *.
    destruct (id1 == i0); subst.
      inv J3. clear IHrm. fsetdec.
      eapply IHrm in J3; eauto.
        clear - J1. fsetdec.
Qed.

Lemma getOperandValue_eq_fresh_id : forall tmp TD Mem2 v lc2 gl gvp2,
  id_fresh_in_value v tmp ->
  getOperandValue TD Mem2 v lc2 gl = 
    getOperandValue TD Mem2 v (updateAddAL GenericValue lc2 tmp gvp2) gl.
Proof.
  intros.
  destruct v; simpl; auto.
    rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma notin_codom__neq' : forall rm d id1 bid eid,
  AtomSetImpl.inter d (codom rm) [<=] {} ->
  Some (bid, eid) = lookupAL _ rm id1 ->
  bid `notin` d /\ eid `notin` d.
Proof.
  induction rm; intros d id1 bid eid J1 J2.
    inversion J2.

    destruct a. destruct p. simpl in *.
    destruct (id1 == i0); subst.
      inv J2. clear IHrm. fsetdec.
      eapply IHrm in J2; eauto.
        clear - J1. fsetdec.
Qed.

Lemma ids2atoms_dom : forall x d,
  In x d <-> x `in` ids2atoms d.
Proof.
  induction d.
    split; intro J.
      inversion J.
      contradict J; fsetdec.
    split; simpl; intro J.
      destruct J as [J | J]; subst; auto.
        apply IHd in J. auto.

      assert (x `in` (singleton a) \/ x `in` (ids2atoms d)) as H.
        fsetdec.
      destruct H as [H | H]; try fsetdec.
        apply IHd in H. auto.
Qed.

Lemma tmp_is_fresh : forall i0 d ex_ids tmp ex_ids',
  i0 `in` d ->
  d [<=] ids2atoms ex_ids ->
  (tmp, ex_ids') = mk_tmp ex_ids ->
  i0 <> tmp.
Proof.
  intros. unfold mk_tmp in H1.
  destruct (atom_fresh_for_list ex_ids).
  inv H1.
  assert (x `notin` ids2atoms ex_ids) as J.
    intro H1. apply n.
    apply ids2atoms_dom; auto.              
  fsetdec.
Qed.

Lemma rmap_lookupAL : forall rm bid eid id1,
  ret (bid, eid) = lookupAL (id * id) rm id1 ->
  bid `in` codom rm /\ eid `in` codom rm /\ id1 `in` dom rm.
Proof.
  induction rm; intros.
    inversion H.
    destruct a. destruct p. simpl in *.
    destruct (id1 == a); subst.
      inv H. fsetdec.
      apply IHrm in H. fsetdec.
Qed.

Lemma rm_codom_disjoint_spec : forall rm pid bid eid,
  rm_codom_disjoint rm ->
  Some (bid, eid) = lookupAL _ rm pid ->
  bid <> eid /\ bid <> pid /\ eid <> pid.
Proof.
  induction rm; intros. 
    inversion H0.
    destruct a. destruct p. simpl in *.
    destruct (pid == i0); subst.
      inv H0. destruct H as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
      repeat split; auto.

      destruct H as [_ [_ [_ [_ [_ [_ H]]]]]].
      eapply IHrm in H; eauto.
Qed.

Lemma rm_codom_disjoint_spec' : forall rm bid1 eid1 id1 bid2 eid2 id2,
  rm_codom_disjoint rm ->
  ret (bid1, eid1) = lookupAL (id * id) rm id1 ->
  ret (bid2, eid2) = lookupAL (id * id) rm id2 ->
  id1 <> id2 ->
  bid1 <> bid2 /\ bid1 <> eid2 /\ bid1 <> id2 /\ bid1 <> id1 /\
  eid1 <> bid2 /\ eid1 <> eid2 /\ eid1 <> id1 /\ eid1 <> id2 /\
  bid2 <> id1 /\ eid2 <> id1.
Proof.
  induction rm; intros.
    inversion H0.
    destruct a. destruct p. simpl in *.
    destruct H as [H8 [H9 [H3 [H4 [H5 [H6 H7]]]]]].
    destruct (id1 == i0); subst.
      destruct (id2 == i0); subst.
        contradict H2; auto.

        inv H0.
        eapply rm_codom_disjoint_spec in H7; eauto.
        apply rmap_lookupAL in H1.
        destruct H1 as [H11 [H12 H13]].
        destruct H7 as [H0 [H1 H10]].
        repeat (split; auto). 
          clear - H5 H11. fsetdec.
          clear - H5 H12. fsetdec.
          clear - H5 H13. fsetdec.
          clear - H6 H11. fsetdec.
          clear - H6 H12. fsetdec.
          clear - H6 H13. fsetdec.
          clear - H11 H4. fsetdec.
          clear - H12 H4. fsetdec.
      destruct (id2 == i0); subst; eauto.
        inv H1.
        eapply rm_codom_disjoint_spec in H7; eauto.
        destruct H7 as [H1 [H7 H10]].
        apply rmap_lookupAL in H0.
        destruct H0 as [H11 [H12 H13]].
        repeat (split; auto). 
          clear - H5 H11. fsetdec.
          clear - H6 H11. fsetdec.
          clear - H4 H11. fsetdec.
          clear - H5 H12. fsetdec.
          clear - H6 H12. fsetdec.
          clear - H4 H12. fsetdec.
          clear - H5 H13. fsetdec.
          clear - H6 H13. fsetdec.
Qed.

Lemma tmp_is_fresh' : forall id1 ex_ids tmp ex_ids' bid eid rm,
  codom rm [<=] ids2atoms ex_ids ->
  Some (bid, eid) = lookupAL _ rm id1 ->
  (tmp, ex_ids') = mk_tmp ex_ids ->
  bid <> tmp /\ eid <> tmp.
Proof.
  intros. unfold mk_tmp in H1.
  destruct (atom_fresh_for_list ex_ids).
  inv H1.
  assert (x `notin` ids2atoms ex_ids) as J.
    intro H1. apply n.
    apply ids2atoms_dom; auto.              
  apply rmap_lookupAL in H0.
  fsetdec.
Qed.

Lemma wf_fresh__mk_tmp : forall ex_ids c rm2 ptmp ex_ids1,
  wf_fresh ex_ids c rm2 ->
  (ptmp, ex_ids1) = mk_tmp ex_ids ->
  wf_fresh ex_ids1 c rm2.
Proof.
  intros.
  destruct H as [J1 [J2 [J3 J4]]].
  split; auto.
  split; auto.
  split; auto.
    unfold mk_tmp in H0.
    destruct (atom_fresh_for_list ex_ids).
    inv H0.
    simpl.
    assert (x `notin` ids2atoms ex_ids) as J.
      intro H1. apply n.
      apply ids2atoms_dom; auto.              
    fsetdec.
Qed.

Lemma trans_nbranch__is__correct__dbMalloc : forall 
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (id0 : atom)
  (t : typ)
  (v : value)
  (align0 : align)
  (Hnontemp : unsupported_cmd (insn_malloc id0 t v align0))
  (Hnotin : wf_fresh ex_ids (insn_malloc id0 t v align0) rm2)
  (isntcall : isCall (insn_malloc id0 t v align0) = false)
  (Htrans : trans_nbranch ex_ids tmps optaddrb optaddre rm2
             (mkNB (insn_malloc id0 t v align0) isntcall) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (rm : AssocList SoftBound.metadata)
  (lc : GVMap)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : SoftBound.mmetadata)
  mgb
  (Hwfmi : wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : mem_simulation mi TD mgb MM Mem0 Mem2)
  (gl : GVMap)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (gn : GenericValue)
  (als : list mblock)
  (Mem' : mem)
  (tsz : sz)
  (mb : mblock)
  (lc' : GVMap)
  (rm' : SoftBound.rmetadata)
  (n : Z)
  (Hwfv : wf_value v)
  (Hwfg : wf_globals mgb gl)
  (H : getTypeAllocSize TD t = ret tsz)
  (H0 : getOperandValue TD Mem0 v lc gl = ret gn)
  (H1 : malloc TD Mem0 tsz gn align0 = ret (Mem', mb))
  (H2 : GV2int TD Size.ThirtyTwo gn = ret n)
  (H3 : SoftBound.prop_reg_metadata lc rm id0 (blk2GV TD mb)
         {|
         SoftBound.md_base := SoftBound.base2GV TD mb;
         SoftBound.md_bound := SoftBound.bound2GV TD mb tsz n |} = 
       (lc', rm')),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         wf_sb_mi mgb mi' Mem' Mem2' /\
         reg_simulation mi' TD gl rm' rm2 Mem' Mem2' lc' lc2' /\
         mem_simulation mi' TD mgb MM Mem' Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  simpl in Htrans.
  remember (lookupAL (id * id) rm2 id0) as R1.
  destruct R1; try solve [inversion Htrans].
  destruct p as [bid eid].
  remember (mk_tmp ex_ids) as R2.
  destruct R2 as [tmp ex_ids''].
  inv Htrans.
  invert_prop_reg_metadata.
  assert (Hmalloc:=H1).
  apply mem_simulation__malloc with (MM:=MM)(mgb:=mgb)(Mem2:=Mem2)(mi:=mi) in H1;
    auto.
  destruct H1 as [mi' [Mem2' [mb' [H11 [H16 [H12 [H13 [H14 H15]]]]]]]].
  exists 
    (updateAddAL _ 
      (updateAddAL _ 
        (updateAddAL _ 
          (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
          bid (SoftBound.base2GV TD mb'))
        tmp (SoftBound.bound2GV TD mb' tsz n))
      eid (SoftBound.bound2GV TD mb' tsz n)).
  exists Mem2'. exists mi'.
  split.
  SCase "dbCmds".
    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))(als2:=als)
      (Mem2:=Mem2'); auto.
      eapply simulation__getOperandValue with (mi:=mi)(MM:=MM)(Mem2:=Mem2) in H0;
        eauto.
      destruct H0 as [gn' [H00 H01]].
      unfold malloc in H11.
      erewrite simulation__eq__GV2int in H11; eauto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
              bid (SoftBound.base2GV TD mb')
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl.
        rewrite lookupAL_updateAddAL_eq.
        auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL _
                (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
                 bid (SoftBound.base2GV TD mb'))
               tmp (SoftBound.bound2GV TD mb' tsz n)
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.

      assert (exists gn', getOperandValue TD Mem2' v lc2 gl = ret gn' /\
              GV2int TD Size.ThirtyTwo gn = GV2int TD Size.ThirtyTwo gn') as H4.
        eapply simulation__getOperandValue with (MM:=MM)(Mem2:=Mem2) in H0
          ; eauto.
        destruct H0 as [gv' [H00 H01]].
        destruct Hmsim as [_ [Hmsim _]].
        rewrite malloc_getOperandValue_inv with (tsz:=tsz)(gn:=gn)(a0:=align0)
         (Mem2':=Mem2')(mb2:=mb')(mgb:=mgb) in H00; auto.
        exists gv'. split; auto.
          rewrite simulation__eq__GV2int with (mi:=mi)(gn':=gv'); eauto.
      destruct H4 as [gn' [H41 H42]].
      apply SimpleSE.dbGEP with (mp:=blk2GV TD mb')(vidxs:=[gn']); auto.
        simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.

          clear - Hnotin HeqR1.
          destruct Hnotin as [Hnotin _]. 
          unfold getCmdIDs in Hnotin. simpl in Hnotin.
          eapply notin_codom__neq with (rm:=rm2)(id0:=id0)(id1:=id0)(bid:=bid)
            (eid:=eid) in HeqR1; eauto.

        simpl.
        assert(getOperandValue TD Mem2' v
          (updateAddAL _ (updateAddAL _ lc2 id0 (blk2GV TD mb'))
          bid (SoftBound.base2GV TD mb')) gl = 
          getOperandValue TD Mem2' v lc2 gl) as EQ'.
          clear - Hnotin HeqR1. 
          destruct Hnotin as [Hnotin1 [Hnotin2 _ ]]. simpl in Hnotin2.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite <- getOperandValue_eq_fresh_id; auto.
              destruct v; simpl in *; auto.
            unfold getCmdIDs in Hnotin1. simpl in Hnotin1.
            eapply notin_codom__neq' in HeqR1; eauto.
              destruct v; simpl in *; fsetdec.

        rewrite EQ'. clear EQ'.
        rewrite H41. auto.

        unfold SoftBound.bound2GV, GEP, blk2GV, GV2ptr, ptr2GV, val2GV.
        simpl.
        rewrite <- H42. rewrite H2.
        unfold mgetoffset, typ2utyp. destruct TD.
        assert (exists ut, 
(*          typ2utyp_aux (gen_utyp_maps (rev n0)) (typ_array 0%nat t) = Some *)
          typ2utyp_aux (subst_nts_by_nts n0 n0) (typ_array 0%nat t) = Some
            (typ_array 0%nat ut) /\
          getTypeAllocSize (l0, n0) ut = getTypeAllocSize (l0, n0) t) as EQ1.
          admit.
        destruct EQ1 as [ut [EQ1 EQ2]].
        rewrite EQ1. simpl.
        rewrite EQ2. rewrite H. simpl.
        rewrite Int.add_commut.
        rewrite Int.add_zero. auto.

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL _
                (updateAddAL _
                  (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
                   bid (SoftBound.base2GV TD mb'))
                 tmp (SoftBound.bound2GV TD mb' tsz n))
               eid (SoftBound.bound2GV TD mb' tsz n)
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl.
        rewrite lookupAL_updateAddAL_eq; auto.

  split; auto.
  split; auto.
  SCase "rsim".
    split.
    SSCase "rsim1".
      clear - Hnotin Hrsim H13 H14 H15 subcase HeqR2 HeqR1.
      intros i0 gv1 J.
      destruct (id_dec id0 i0); subst.
      SSSCase "id0 = i0".
        rewrite lookupAL_updateAddAL_eq in J.
        inv J.
        exists (blk2GV TD mb').
        split.
          clear - Hnotin HeqR1 HeqR2.
          destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]]. 
          unfold getCmdIDs in *. simpl in *.
          rewrite <- lookupAL_updateAddAL_neq.
            rewrite <- lookupAL_updateAddAL_neq.
              rewrite <- lookupAL_updateAddAL_neq.
                rewrite lookupAL_updateAddAL_eq; auto.
                eapply notin_codom__neq with (rm:=rm2)(id0:=i0)(id1:=i0)
                  (bid:=bid)(eid:=eid) in HeqR1; eauto.
              eapply tmp_is_fresh; eauto. fsetdec.
            eapply notin_codom__neq with (rm:=rm2)(id0:=i0)(id1:=i0)(bid:=bid)
              (eid:=eid) in HeqR1; eauto.
 
          unfold gv_inject, blk2GV, ptr2GV, val2GV.
          simpl.
          split; eauto.
           
      SSSCase "id0 <> i0".
        rewrite <- lookupAL_updateAddAL_neq in J; auto.
        destruct Hrsim as [J1 _].
        apply J1 in J.
        destruct J as [gv2 [J J2]].
        exists gv2.
        split.
          admit. (* i0 <> bid eid tmp, need to fix simulation relation for 
                    freshness *)
          eapply gv_inject_incr; eauto.

    SSCase "rsim2".
      intros vp bgv1 egv1 mt J.
      unfold SoftBound.get_reg_metadata in J.
      destruct vp as [pid | ]; simpl.
      SSSCase "vp = pid".
        destruct (id_dec id0 pid); subst.
        SSSSCase "id0 = pid".
          rewrite <- HeqR1.
          rewrite lookupAL_updateAddAL_eq in J.
          inv J.
          exists p8. exists (value_id bid). exists (value_id eid).
          exists (SoftBound.base2GV TD mb').
          exists (SoftBound.bound2GV TD mb' tsz n).
          split; auto.
          split.
            clear - Hnotin HeqR1 HeqR2.
            destruct Hnotin as [Hnotin1 [Hnotin2 [Hnotin3 Hnotin4]]]. 
            unfold getCmdIDs in *.
            simpl in *.
            simpl.
            rewrite <- lookupAL_updateAddAL_neq.
              rewrite <- lookupAL_updateAddAL_neq.
                rewrite lookupAL_updateAddAL_eq; auto.
                eapply tmp_is_fresh' with (tmp:=tmp) in HeqR1; eauto. fsetdec.
              eapply rm_codom_disjoint_spec in HeqR1; eauto.

          split. simpl. rewrite lookupAL_updateAddAL_eq; auto.

          unfold gv_inject, SoftBound.base2GV, blk2GV, ptr2GV, val2GV.
          simpl. clear - H14.
          split. 
            split; auto.
            apply val_cons_inject; eauto.
          split; auto.
            apply val_cons_inject; eauto.
              eapply val_inject_ptr; eauto.
                rewrite Int.add_zero. auto.

        SSSSCase "id0 <> pid".
          rewrite <- lookupAL_updateAddAL_neq in J; auto.
          destruct Hrsim as [_ Hrsim].
          destruct (@Hrsim (value_id pid) bgv1 egv1 mt) as 
            [t2 [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]]; auto.
          exists t2. exists bv2. exists ev2. exists bgv2. exists egv2.
          simpl in J1.
          split; auto.
          remember (lookupAL (id * id) rm2 pid) as R.
          destruct R; inv J1. destruct p; inv H4.
          destruct Hnotin as [Hnotin1 [Hnotin2 [Hnotin3 Hnotin4]]]. 
          eapply rm_codom_disjoint_spec' with (id1:=id0)(id2:=pid) in Hnotin4; 
            eauto.
          destruct Hnotin4 as [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [G9 G10]]]]]]]]]. 
          simpl.
          split.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
              eapply tmp_is_fresh' with (tmp:=tmp) in HeqR; eauto. 
                clear - Hnotin3. fsetdec.

          split.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
              eapply tmp_is_fresh' with (tmp:=tmp) in HeqR; eauto. 
                clear - Hnotin3. fsetdec.

          split; eauto using gv_inject_incr.

      SSSCase "vp = c".
        assert (exists t, Constant.getTyp c = Some t) as J'.
          admit. (* wfc *)
        destruct J' as [t0 J'].
        rewrite J'.
        remember (SoftBound.get_const_metadata c) as R.
        destruct R as [[[c0 c2] mt']|].
          remember (const2GV TD Mem' gl c0) as R1.
          destruct R1; try solve [inversion J]. simpl in J.
          remember (const2GV TD Mem' gl c2) as R2.
          destruct R2; try solve [inversion J]. simpl in J.
          inv J.
          exists t0. exists (value_const c0). exists (value_const c2). simpl.
          symmetry in HeqR3, HeqR0.
          destruct H12 as [H12 _].
          eapply sb_mem_inj__const2GV with (Mem':=Mem2') in HeqR3; eauto.
          eapply sb_mem_inj__const2GV with (Mem':=Mem2') in HeqR0; eauto.
          destruct HeqR3 as [egv2 [HeqR3 HeqR3']].         
          destruct HeqR0 as [bgv2 [HeqR0 HeqR0']].         
          exists bgv2. exists egv2. 
          split; auto.
            clear - J' HeqR. admit.

          inv J.
          exists t0. exists (value_const (const_null t0)).
          exists (value_const (const_null t0)). exists null. exists null.
          simpl. unfold gv_inject. unfold const2GV. simpl. unfold null. 
          unfold val2GV.
          inversion H16.
          repeat (split; eauto).

Qed.

Lemma getTypeAllocSize_pos : forall TD t s,
  getTypeAllocSize TD t = Some s ->
  Size.to_Z s > 0.
(* wft *)
Admitted.

Lemma trans_nbranch__is__correct__dbLoad_nptr__case : forall b0 i1 TD s t
  b b1 i0 i2,
  ret Vptr b0 i1 = GV2ptr TD (getPointerSize TD) null ->
  ret Vptr b1 i2 = GV2ptr TD (getPointerSize TD) null  ->
  ret s = getTypeAllocSize TD t ->
  zeq b b0 && zeq b0 b1 && zle (Int.signed 31 i1) (Int.signed 31 i0) &&
  zle (Int.signed 31 i0 + Size.to_Z s) (Int.signed 31 i2) ->
  False.
Proof.  
  intros.
  simpl in *.
  inv H. inv H0.
  unfold Mem.nullptr in H2.
  rewrite Int.signed_repr with (z:=0) in H2.
    bdestruct4 H2 as H2 H3 H4 H5.
    symmetry in H1.    
    apply getTypeAllocSize_pos in H1.
    assert (0 <= Int.signed 31 i0) as J.
      destruct (zle 0 (Int.signed 31 i0)); zauto.
        simpl in H4. inversion H4.
    assert ((Int.signed 31 i0 + Size.to_Z s) <= 0) as J'.
      destruct (zle (Int.signed 31 i0 + Size.to_Z s) 0); zauto.
        simpl in H5. inversion H5.
    contradict J'; zauto.

    assert (J1:=@Int.min_signed_neg 31).
    assert (J2:=@Int.max_signed_pos 31).
    zeauto.
Qed.

Lemma get_reg_metadata__fresh : forall
  (rm2 : rmap)
  (ex_ids : ids)
  c
  (Hnotin : wf_fresh ex_ids c rm2)
  (t2 : typ)
  (bv2 : value)
  (ev2 : value)
  (ptmp : id)
  (ex_ids1 : ids)
  (HeqR1 : (ptmp, ex_ids1) = mk_tmp ex_ids)
  vp
  (J1 : get_reg_metadata rm2 vp = ret (t2, bv2, ev2)),
  id_fresh_in_value bv2 ptmp /\ id_fresh_in_value ev2 ptmp.
Proof.
  intros.
  destruct vp; simpl in *.
  remember (lookupAL (id * id) rm2 i0) as R.
  destruct R; inv J1.
  destruct p; inv H0; simpl.
  destruct Hnotin as [_ [_ [Hnotin _ ]]].
  eapply tmp_is_fresh' with (tmp:=ptmp) in HeqR; eauto. fsetdec.
  
  destruct (SoftBound.get_const_metadata c0) as [[[bc ec] mt]|].
    inv J1; simpl; auto.
    destruct (Constant.getTyp c0); inv J1; simpl; auto.
Qed.            

Lemma get_reg_metadata_fresh' : forall vp rm2 ex_ids
  (Hnotin1 : AtomSetImpl.inter (getValueID vp) (codom rm2)[<=]empty)
  (Hnotin2 : union (getValueID vp) (codom rm2)[<=] ids2atoms ex_ids)
  (ptmp : id)
  (ex_ids1 : ids)
  (HeqR1 : (ptmp, ex_ids1) = mk_tmp ex_ids),
  id_fresh_in_value vp ptmp.
Proof.
  intros.
  destruct vp; simpl in *; auto.
    apply tmp_is_fresh with (i0:=i0)(d:=singleton i0) in HeqR1; auto.
      clear - Hnotin2. fsetdec.
Qed.

Lemma wf_fresh__mk_tmp' : forall ex_ids vp rm2 ptmp ex_ids1,
 union (getValueID vp) (codom rm2)[<=] ids2atoms ex_ids ->
 (ptmp, ex_ids1) = mk_tmp ex_ids ->
 union (getValueID vp) (codom rm2)[<=] ids2atoms ex_ids1.
Proof.
  intros.
    unfold mk_tmp in H0.
    destruct (atom_fresh_for_list ex_ids).
    inv H0.
    simpl.
    assert (x `notin` ids2atoms ex_ids) as J.
      intro H1. apply n.
      apply ids2atoms_dom; auto.              
    fsetdec.
Qed.

Lemma get_reg_metadata_fresh'' : forall
  (rm2 : rmap)
  (ex_ids : ids)
  (id0 : id)
  (t : typ)
  (vp : value)
  (align0 : align)
  (Hnotin : wf_fresh ex_ids (insn_load id0 t vp align0) rm2)
  (vp0 : value)
  (t0 : typ)
  (bv0 : value)
  (ev0 : value)
  (J11 : get_reg_metadata rm2 vp0 = ret (t0, bv0, ev0)),
  id_fresh_in_value bv0 id0 /\ id_fresh_in_value ev0 id0.
Proof.
  intros.
  destruct Hnotin as [Hnotin _].          
  destruct vp0; simpl in J11.
    remember (lookupAL (id * id) rm2 i0) as R.
    destruct R as [[bid eid]|]; inv J11.
    simpl.
    apply rmap_lookupAL in HeqR.
    destruct HeqR as [J1 [J2 _]].
    unfold getCmdIDs in Hnotin. simpl in Hnotin.
    clear - Hnotin J2 J1. fsetdec.
  
    destruct (SoftBound.get_const_metadata c) as [[[be ec] m1]|].
      inv J11; simpl; auto.
      destruct (Constant.getTyp c); inv J11; simpl; auto.
Qed.

Lemma trans_nbranch__is__correct__dbLoad_nptr : forall
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (id0 : id)
  (t : typ)
  (vp : value)
  (align0 : align)
  (Hnontemp : unsupported_cmd (insn_load id0 t vp align0))
  (Hnotin : wf_fresh ex_ids (insn_load id0 t vp align0) rm2)
  (isntcall : isCall (insn_load id0 t vp align0) = false)
  (Htrans : trans_nbranch ex_ids tmps optaddrb optaddre rm2
             (mkNB (insn_load id0 t vp align0) isntcall ) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (rm : SoftBound.rmetadata)
  (lc : GVMap)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : SoftBound.mmetadata)
  mgb
  (Hwfmi : wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : mem_simulation mi TD mgb MM Mem0 Mem2)
  (gl : GVMap)
  (Hwfg : wf_globals mgb gl)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (als : list mblock)
  (gvp : GenericValue)
  (md : SoftBound.metadata)
  (gv : GenericValue)
  mt0
  (H : SoftBound.get_reg_metadata TD Mem0 gl rm vp = Some (md,mt0))
  (H0 : getOperandValue TD Mem0 vp lc gl = ret gvp)
  (H1 : SoftBound.assert_mptr TD t gvp md)
  (H2 : mload TD Mem0 gvp t align0 = ret gv)
  (H3 : ~ isPointerTyp t),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         wf_sb_mi mgb mi' Mem0 Mem2' /\
         reg_simulation mi' TD gl rm rm2 Mem0 Mem2' 
           (updateAddAL GenericValue lc id0 gv) lc2' /\
         mem_simulation mi' TD mgb MM Mem0 Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  simpl in Htrans.
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
  remember (isPointerTypB t) as R4.
  destruct R4.
  SCase "t is ptr".
    unfold isPointerTyp in H3.
    rewrite <- HeqR4 in H3.
    contradict H3; auto.

  SCase "t isnt ptr".
  inv Htrans.
  assert (J:=H1).
  unfold SoftBound.assert_mptr in J.
  destruct md as [md_base md_bound].
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (getTypeAllocSize TD t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gvp2 [H00 H01]].            
  eapply simulation__mload in H2; eauto.
  destruct H2 as [gv2 [H21 H22]].
  destruct Hrsim as [Hrsim1 Hrsim2].
  assert (HeqR8':=H).
  apply Hrsim2 in HeqR8'.      
  destruct HeqR8' as [t2 [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]].
  exists 
       (updateAddAL _ 
        (updateAddAL _ 
          (updateAddAL _ 
           (updateAddAL GenericValue lc2 ptmp gvp2)
           btmp bgv2)
          etmp egv2)
        id0 gv2).
  exists Mem2. exists mi.
  split.
    SSCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H00.
        rewrite H00. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite J2. simpl. admit. (* given wf typ, t0 must be of ptr. *)

          clear - HeqR1 Hnotin J1.
          eapply get_reg_metadata__fresh in Hnotin; eauto.
          destruct Hnotin; auto.

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite J3. simpl. admit. (* given wf typ, t0 must be of ptr. *)
  
            clear - HeqR1 Hnotin J1.
            eapply get_reg_metadata__fresh in Hnotin; eauto.
            destruct Hnotin; auto.
   
          clear - HeqR1 Hnotin J1 HeqR2.
          eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids1)
            (c:=insn_load id0 t vp align0) in J1; eauto.
            destruct J1; auto.
            eapply wf_fresh__mk_tmp; eauto.  

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
       clear - H00 J2 J3 J4 J5 J H00 H01 HeqR0 HeqR5 HeqR6 HeqR7.
       eapply assert_mptr_fn__ok with (b:=b)(b0:=b0)(b1:=b1); eauto.

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ 
        (updateAddAL _ lc2 ptmp gvp2) btmp bgv2) etmp egv2) id0 gv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbLoad with (mp:=gvp2); auto.
        clear - J1 Hnotin HeqR1 HeqR2 HeqR3 H00.
        destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]].
        unfold getCmdIDs in *. simpl in *.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.
          eapply get_reg_metadata_fresh' with (rm2:=rm2)(ex_ids:=ex_ids1); 
            eauto; try fsetdec.
            eapply wf_fresh__mk_tmp'; eauto; try fsetdec.
          eapply get_reg_metadata_fresh' with (rm2:=rm2)(ex_ids:=ex_ids2); 
            eauto; try fsetdec.
            eapply wf_fresh__mk_tmp' with (ptmp:=btmp)(ex_ids:=ex_ids1); 
              eauto; try fsetdec.
            eapply wf_fresh__mk_tmp'; eauto; try fsetdec.

  split; auto.
  split; auto.
    SSCase "rsim".
    split.
      SSSCase "rsim1".
      clear - Hrsim1 H22 subcase subsubcase.
      intros i0 gv1 J.
      destruct (id_dec id0 i0); subst.
        rewrite lookupAL_updateAddAL_eq in J.
        inv J.
        exists gv2.
        split; auto.
          rewrite lookupAL_updateAddAL_eq; auto.
 
        rewrite <- lookupAL_updateAddAL_neq in J; auto.
        apply Hrsim1 in J.
        destruct J as [gv2' [J J2]].
        exists gv2'.
        split; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
          admit. (* i0 <> bid eid tmp *)

      SSSCase "rsim2".
      intros vp0 bgv1 egv1 mt1 J6.
      apply Hrsim2 in J6.
      destruct J6 as [t0 [bv0 [ev0 [bgv0 [egv0 [J11 [J21 [J31 [J41 J51]]]]]]]]].
      exists t0. exists bv0. exists ev0. exists bgv0. exists egv0.
      split; auto.
      split.
        clear - HeqR1 Hnotin J11 J21 HeqR2 HeqR3.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite <- getOperandValue_eq_fresh_id.
              rewrite <- getOperandValue_eq_fresh_id; auto.
                eapply get_reg_metadata__fresh in Hnotin; eauto.
                destruct Hnotin; auto.
              eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids1)
                (c:=insn_load id0 t vp align0) in J11; eauto.
              destruct J11; auto.
              eapply wf_fresh__mk_tmp; eauto.  
            eapply get_reg_metadata__fresh with (ptmp:=etmp)(ex_ids:=ex_ids2)
              (c:=insn_load id0 t vp align0) in J11; eauto.
            destruct J11; auto.
            eapply wf_fresh__mk_tmp with (ex_ids:=ex_ids1); eauto.  
            eapply wf_fresh__mk_tmp; eauto.
          eapply get_reg_metadata_fresh'' in Hnotin; eauto.
          destruct Hnotin; auto.
       
      split.
        clear - HeqR1 Hnotin J11 J31 HeqR2 HeqR3.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite <- getOperandValue_eq_fresh_id.
              rewrite <- getOperandValue_eq_fresh_id; auto.
                eapply get_reg_metadata__fresh in Hnotin; eauto.
                destruct Hnotin; auto.
              eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids1)
                (c:=insn_load id0 t vp align0) in J11; eauto.
              destruct J11; auto.
              eapply wf_fresh__mk_tmp; eauto.  
            eapply get_reg_metadata__fresh with (ptmp:=etmp)(ex_ids:=ex_ids2)
              (c:=insn_load id0 t vp align0) in J11; eauto.
            destruct J11; auto.
            eapply wf_fresh__mk_tmp with (ex_ids:=ex_ids1); eauto.  
            eapply wf_fresh__mk_tmp; eauto.
          eapply get_reg_metadata_fresh'' in Hnotin; eauto.
          destruct Hnotin; auto.

      split; auto.
Qed.

Lemma mload_inversion : forall Mem2 t align0 TD gvp2 
  (gv2 : GenericValue)
  (H21 : mload TD Mem2 gvp2 t align0 = ret gv2),
  exists b : Values.block, exists ofs : int32, gvp2 = ptr2GV TD (Vptr b ofs).
Proof.
  intros.
    unfold mload in H21.
    remember (GV2ptr TD (getPointerSize TD) gvp2) as R.
    destruct R; try solve [inversion H21].
    destruct v; try solve [inversion H21].
    unfold GV2ptr in HeqR.
    destruct gvp2; try solve [inversion HeqR].
    destruct p.
    destruct v; try solve [inversion HeqR].
    destruct gvp2; inv HeqR.
    exists b0. exists i1. 
    unfold ptr2GV, val2GV.
    admit. (* we should check alignment too *)      
Qed.


Lemma ids2atoms_mk_tmp : forall d ex_ids ptmp ex_ids2, 
  d [<=] ids2atoms ex_ids ->
  (ptmp, ex_ids2) = mk_tmp ex_ids ->
  d [<=] ids2atoms ex_ids2.
Proof.
  intros.
    unfold mk_tmp in H0.
    destruct (atom_fresh_for_list ex_ids).
    inv H0.
    simpl.
    assert (x `notin` ids2atoms ex_ids) as J.
      intro H1. apply n.
      apply ids2atoms_dom; auto.              
    fsetdec.
Qed.

Lemma trans_nbranch__is__correct__dbLoad_ptr: forall
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (addrb : id)
  (addre : id)
  (mi : meminj)
  (id0 : atom)
  (t : typ)
  (vp : value)
  (align0 : align)
  (Hnontemp : unsupported_cmd (insn_load id0 t vp align0))
  (Hnotin : wf_fresh ex_ids (insn_load id0 t vp align0) rm2)
  (mt : typ)
  (bv : value)
  (ev : value)
  (HeqR : ret (mt, bv, ev) = get_reg_metadata rm2 vp)
  (ptmp : id)
  (ex_ids2 : ids)
  (HeqR1 : (ptmp, ex_ids2) = mk_tmp ex_ids)
  (btmp : id)
  (ex_ids3 : ids)
  (HeqR2 : (btmp, ex_ids3) = mk_tmp ex_ids2)
  (etmp : id)
  (HeqR4 : true = isPointerTypB t)
  (bid0 : id)
  (eid0 : id)
  (HeqR5 : ret (bid0, eid0) = lookupAL (id * id) rm2 id0)
  (rm : SoftBound.rmetadata)
  (lc : GVMap)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : Values.block -> int32 -> monad SoftBound.metadata)
  mgb
  (Hwfmi : wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : mem_simulation mi TD mgb MM Mem0 Mem2)
  (gl : GVMap)
  (Hwfg : wf_globals mgb gl)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (als : list mblock)
  (gvp : GenericValue)
  (md : SoftBound.metadata)
  (gv : GenericValue)
  (lc' : GVMap)
  (rm' : SoftBound.rmetadata)
  (Hwfv : wf_value vp)
  (Hwfg : wf_globals mgb gl)
  mt0
  (H : SoftBound.get_reg_metadata TD Mem0 gl rm vp = ret (md,mt0))
  (H0 : getOperandValue TD Mem0 vp lc gl = ret gvp)
  (H1 : SoftBound.assert_mptr TD t gvp md)
  (H2 : mload TD Mem0 gvp t align0 = ret gv)
  (H3 : isPointerTyp t)
  (HeqR3 : (etmp, ex_ids') = mk_tmp ex_ids3)
  (H5 : SoftBound.prop_reg_metadata lc rm id0 gv
         (SoftBound.get_mem_metadata TD MM gvp) = (lc', rm')),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2
           (insn_cast ptmp castop_bitcast (typ_pointer t) vp p8
            :: insn_cast btmp castop_bitcast mt bv p8
               :: insn_cast etmp castop_bitcast mt ev p8
                  :: insn_call fake_id true sb_call_attrs assert_mptr_typ assert_mptr_fn
                       ((p8, value_id btmp)
                        :: (p8, value_id etmp)
                           :: (p8, value_id ptmp)
                              :: (i32, type_size t) :: (i32, vint1) :: nil)
                     :: insn_load id0 t vp align0
                        :: insn_call fake_id true sb_call_attrs get_mmetadata_typ
                             get_mmetadata_fn
                             ((p8, value_id ptmp)

                              :: (pp8, value_id addrb)
                                 :: (pp8, value_id addre)
                                    :: (p8, vnullp8)
                                       :: (i32, vint1)
                                          :: (p32, vnullp32) :: nil)
                           :: insn_load bid0 p8 (value_id addrb) Align.Zero
                              :: insn_load eid0 p8 
                                   (value_id addre) Align.Zero :: nil) lc2'
           als Mem2' trace_nil /\
         wf_sb_mi mgb mi' Mem0 Mem2' /\
         reg_simulation mi' TD gl rm' rm2 Mem0 Mem2' lc' lc2' /\
         mem_simulation mi' TD mgb MM Mem0 Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  assert (J:=H1).
  unfold SoftBound.assert_mptr in J.
  destruct md as [md_base md_bound].
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (getTypeAllocSize TD t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gvp2 [H00 H01]].            
  unfold SoftBound.get_reg_metadata in H.
  assert (H2':=H2).
  eapply simulation__mload in H2'; eauto.
  destruct H2' as [gv2 [H21 H22]].
  destruct Hrsim as [Hrsim1 Hrsim2].
  case_eq (SoftBound.get_mem_metadata TD MM gvp).
  intros mb_base0 md_bound0 JJ.
  assert (Hmsim':=Hmsim).
  destruct Hmsim' as [Hmsim1 Hmsim2].
  assert (JJ':=JJ).
  assert (exists b, exists ofs, gvp = ptr2GV TD (Vptr b ofs)) as EQ.
    clear - H2.
    eapply mload_inversion; eauto.
  destruct EQ as [pb [pofs EQ]]. subst.
  eapply Hmsim2 with (als:=als)(addrb:=addrb)(addre:=addre)(bid0:=bid0)
    (eid0:=eid0) in JJ'; eauto.
  destruct JJ' as [bgv' [egv' [Mem2' [JJ1 [JJ2 [JJ3 [JJ4 JJ5]]]]]]].
  assert (HeqR9':=H).
  apply Hrsim2 in HeqR9'.      
  destruct HeqR9' as [t2 [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]].
  exists 
       (updateAddAL _ 
        (updateAddAL _ 
         (updateAddAL _ 
          (updateAddAL _ 
            (updateAddAL _ 
             (updateAddAL GenericValue lc2 ptmp gvp2)
              btmp bgv2)
             etmp egv2)
            id0 gv2)
           bid0 bgv')
          eid0 egv').
  exists Mem2. exists mi.
  split.
  SCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H00.
        rewrite H00. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite J2. simpl. admit. (* given wf typ, t0 must be of ptr. *)

          clear - HeqR1 Hnotin J1.
          eapply get_reg_metadata__fresh in Hnotin; eauto.
          destruct Hnotin; auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite J3. simpl. admit. (* given wf typ, t0 must be of ptr. *)

            clear - HeqR1 Hnotin J1.
            eapply get_reg_metadata__fresh in Hnotin; eauto.
            destruct Hnotin; auto.
   
          clear - HeqR1 Hnotin J1 HeqR2.
          eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids2)
            (c:=insn_load id0 t vp align0) in J1; eauto.
            destruct J1; auto.
            eapply wf_fresh__mk_tmp; eauto.  

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
       clear - H00 J2 J3 J4 J5 J H00 H01 HeqR0 HeqR8 HeqR7 HeqR6.
       eapply assert_mptr_fn__ok with (b:=b)(b0:=b0)(b1:=b1); eauto.

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ 
        (updateAddAL _ lc2 ptmp gvp2) btmp bgv2) etmp egv2) id0 gv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbLoad with (mp:=gvp2); auto.
        clear - J1 Hnotin HeqR1 HeqR2 HeqR3 H00.
        destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]].
        unfold getCmdIDs in *. simpl in *.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.
          eapply get_reg_metadata_fresh' with (rm2:=rm2)(ex_ids:=ex_ids2); 
            eauto; try fsetdec.
            eapply wf_fresh__mk_tmp'; eauto; try fsetdec.
          eapply get_reg_metadata_fresh' with (rm2:=rm2)(ex_ids:=ex_ids3); 
            eauto; try fsetdec.
            eapply wf_fresh__mk_tmp' with (ptmp:=btmp)(ex_ids:=ex_ids2); 
              eauto; try fsetdec.
            eapply wf_fresh__mk_tmp'; eauto; try fsetdec.

    clear - JJ1 H00.
    eapply get_mmetadata_fn__weaken; eauto.

  split; auto.
  split; auto.
  SCase "rsim".

    unfold SoftBound.get_mem_metadata, SoftBound.prop_reg_metadata in H5.  
    split.
    SSCase "rsim1".
      clear - Hrsim1 H5 H22.
      inv H5.
      intros i0 gv1 J.
      destruct (id_dec id0 i0); subst.
        rewrite lookupAL_updateAddAL_eq in J.
        inv J.
        exists gv2.
        split; auto.
          admit. (* i0 <> bid eid tmp *)
 
        rewrite <- lookupAL_updateAddAL_neq in J; auto.
        apply Hrsim1 in J.
        destruct J as [gv2' [J J2]].
        exists gv2'.
        split; auto.
          admit. (* i0 <> bid eid tmp *)

    SSCase "rsim2".
      clear Hrsim1 Hmsim1 Hmsim2 J1 J2 J3 J4 J5.
      inv H5.
      intros vp0 bgv1 egv1 mt1 J6.
      destruct vp0 as [pid | ]; simpl in *.
      SSSCase "vp = pid".
        destruct (id_dec id0 pid); subst.
        SSSSCase "id0 = pid".
          rewrite <- HeqR5.
          rewrite lookupAL_updateAddAL_eq in J6.
          exists p8. exists (value_id bid0). exists (value_id eid0).
          exists bgv'. exists egv'.
          split; auto.
          split.
            simpl.
            rewrite <- lookupAL_updateAddAL_neq.
              rewrite lookupAL_updateAddAL_eq; auto.
              clear - Hnotin HeqR5.
              destruct Hnotin as [_ [_ [_ Hnotin]]].
              eapply rm_codom_disjoint_spec with (pid:=pid)(bid:=bid0)(eid:=eid0)
                in Hnotin; eauto.

          split. simpl.
            rewrite lookupAL_updateAddAL_eq; auto.

          clear - HeqR0 JJ JJ2 JJ3 J6.
          unfold SoftBound.get_mem_metadata in JJ.
          unfold GV2ptr, ptr2GV, val2GV in JJ.
          inv HeqR0.
          rewrite JJ in J6. inv J6.
          split; auto.

        SSSSCase "id0 <> pid".
          rewrite <- lookupAL_updateAddAL_neq in J6; auto.
          destruct (@Hrsim2 (value_id pid) bgv1 egv1 mt1) as 
            [t0 [bv0 [ev0 [bgv0 [egv0 [J1 [J2 [J3 [J4 J5]]]]]]]]]; auto.
          exists t0. exists bv0. exists ev0. exists bgv0. exists egv0.
          simpl in J1.
          split; auto.
          remember (lookupAL (id * id) rm2 pid) as R.
          destruct R as [[bid eid]|]; inv J1. 
          simpl. simpl in J2.
          destruct Hnotin as [Hnotin1 [Hnotin2 [Hnotin3 Hnotin4]]]. 
          eapply rm_codom_disjoint_spec' with (id1:=id0)(id2:=pid) in Hnotin4; 
            eauto.
          destruct Hnotin4 as [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [G9 G10]]]]]]]]].
          split. 
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
              eapply tmp_is_fresh' with (tmp:=ptmp) in HeqR9; eauto. 
                clear - Hnotin3. fsetdec.
              eapply tmp_is_fresh' with (tmp:=btmp) in HeqR9; eauto. 
                apply ids2atoms_mk_tmp with (ptmp:=ptmp)(ex_ids:=ex_ids); auto.  
                clear - Hnotin3. fsetdec.
              eapply tmp_is_fresh' with (tmp:=etmp) in HeqR9; eauto. 
                apply ids2atoms_mk_tmp with (ptmp:=btmp)(ex_ids:=ex_ids2); auto.
                apply ids2atoms_mk_tmp with (ptmp:=ptmp)(ex_ids:=ex_ids); auto.  
                clear - Hnotin3. fsetdec.

          split.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
              eapply tmp_is_fresh' with (tmp:=ptmp) in HeqR9; eauto. 
                clear - Hnotin3. fsetdec.
              eapply tmp_is_fresh' with (tmp:=btmp) in HeqR9; eauto. 
                apply ids2atoms_mk_tmp with (ptmp:=ptmp)(ex_ids:=ex_ids); auto.  
                clear - Hnotin3. fsetdec.
              eapply tmp_is_fresh' with (tmp:=etmp) in HeqR9; eauto. 
                apply ids2atoms_mk_tmp with (ptmp:=btmp)(ex_ids:=ex_ids2); auto.
                apply ids2atoms_mk_tmp with (ptmp:=ptmp)(ex_ids:=ex_ids); auto.  
                clear - Hnotin3. fsetdec.

          split; auto.

      SSSCase "vp = c".
        assert (exists t, Constant.getTyp c = Some t) as J'.
          admit. (* wfc *)
        destruct J' as [t0 J'].
        rewrite J'.
        remember (SoftBound.get_const_metadata c) as R.
        destruct R as [[[c0 c2] ct]|].
          remember (const2GV TD Mem0 gl c0) as R1.
          destruct R1; try solve [inversion J6]. simpl in J6.
          remember (const2GV TD Mem0 gl c2) as R2.
          destruct R2; try solve [inversion J6]. simpl in J6.
          inv J6.
          exists t0. exists (value_const c0). exists (value_const c2).
          simpl.
          symmetry in HeqR11, HeqR10.
          destruct Hmsim as [Hmsim _].
          eapply sb_mem_inj__const2GV with (Mem':=Mem2) in HeqR11; eauto.
          eapply sb_mem_inj__const2GV with (Mem':=Mem2) in HeqR10; eauto.
          destruct HeqR11 as [egv0 [HeqR11 HeqR11']].         
          destruct HeqR10 as [bgv0 [HeqR10 HeqR10']].         
          exists bgv0. exists egv0. 
          split; auto.
            clear - J' HeqR9. admit.

          inv J6.
          exists t0. exists (value_const (const_null t0)).
          exists (value_const (const_null t0)). exists null. exists null.
          simpl. unfold gv_inject. unfold const2GV. simpl. unfold null. 
          unfold val2GV.
          inversion Hwfmi.
          repeat (split; eauto).
Qed.

Lemma const2GV__mstore' : forall TD Mem chk b ofs v Mem' gl c,
  Mem.store chk Mem b ofs v = Some Mem' ->
  _const2GV TD Mem gl c = _const2GV TD Mem' gl c.
Proof.
  intros TD Mem chk b ofs v Mem' gl c Hstore.
  induction c; simpl in *; try solve 
    [ auto | rewrite IHc; auto | 
      rewrite IHc1; rewrite IHc2; auto |
      rewrite IHc1; rewrite IHc2; rewrite IHc3; auto ].
    admit.
    admit.
    rewrite IHc.
    destruct (_const2GV TD Mem' gl c0); auto.
    destruct p.
    unfold mcast, mptrtoint.
    destruct t0; auto.
      destruct c; auto.
        destruct t; auto.
          destruct (GV2val TD g); auto.
            destruct v0; auto.
              erewrite Mem.int2ptr_store; eauto.
      destruct c; auto.
        destruct t; auto.
          destruct (GV2val TD g); auto.
            destruct v0; auto.
              erewrite Mem.ptr2int_store; eauto.
    admit.
Qed.  

Lemma const2GV__mstore : forall TD Mem gvp t gv align0 Mem' gl c,
  mstore TD Mem gvp t gv align0 = Some Mem' ->
  const2GV TD Mem gl c = const2GV TD Mem' gl c.
Proof.
  intros TD Mem gvp t gv align0 Mem' gl c Hmstore. unfold const2GV.
  unfold mstore in Hmstore.
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion Hmstore].  
  destruct v; try solve [inversion Hmstore].  
  remember (typ2memory_chunk t) as R1.
  destruct R1; try solve [inversion Hmstore].  
  remember (GV2val TD gv) as R2.
  destruct R2; try solve [inversion Hmstore].  
  erewrite const2GV__mstore'; eauto.
Qed.

Lemma getOperandValue__mstore : forall TD Mem gvp t gv align0 Mem' gl lc v,
  mstore TD Mem gvp t gv align0 = Some Mem' ->
  getOperandValue TD Mem v lc gl = getOperandValue TD Mem' v lc gl.
Proof.
  intros TD Mem gvp t gv align0 Mem' gl lc v Hmstore.
  destruct v as [vid |]; simpl; auto.
    erewrite const2GV__mstore; eauto.
Qed.

Lemma simulation__mstore : forall mi TD MM Mem0 Mem2 gvp align0 gv t gvp2 gv2
                                  Mem0' mgb,
  wf_sb_mi mgb mi Mem0 Mem2 ->
  mem_simulation mi TD mgb MM Mem0 Mem2 ->
  mstore TD Mem0 gvp t gv align0 = ret Mem0' ->
  gv_inject mi gvp gvp2 ->
  gv_inject mi gv gv2 ->
  exists Mem2', 
    mstore TD Mem2 gvp2 t gv2 align0 = ret Mem2' /\ 
    wf_sb_mi mgb mi Mem0 Mem2' /\
    mem_simulation mi TD mgb MM Mem0' Mem2'.
Proof.
  intros mi TD MM Mem0 Mem2 gvp align0 gv t gvp2 gv2 Mem0' mgb Hwfmi Hmsim 
    Hmstore Hginject1 Hginject2.
  assert (Hmstore':=Hmstore).
  unfold mstore in Hmstore.
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion Hmstore].
  destruct v; try solve [inversion Hmstore].
  remember (typ2memory_chunk t) as R'.
  destruct R'; try solve [inversion Hmstore].
  remember (GV2val TD gv) as R1.
  destruct R1; try solve [inversion Hmstore].
  unfold GV2ptr in *.
  destruct gvp; inv HeqR.
  destruct p.
  destruct v0; inv H0.
  destruct gvp; inv H1.
  unfold gv_inject in *.
  simpl in Hginject1.
  remember (split gvp2) as R2.
  destruct R2; simpl in Hginject1.
  destruct Hginject1 as [J1 J2].
  inversion J1; subst.
  inversion H3; subst.
  inversion H1; subst.
  destruct gvp2; try solve [inversion HeqR2].
  destruct p. simpl in HeqR2.
  remember (split gvp2) as R3.
  destruct R3; inv HeqR2.
  destruct gvp2.
    unfold GV2val in *.
    destruct gv; inv HeqR1.
    destruct p.
    destruct gv; inv H0.
    simpl in Hginject2.    
    remember (split gv2) as R3.
    destruct R3; simpl in Hginject2.
    destruct Hginject2 as [J3 J4].
    inversion J3; subst. 
    inversion H6; subst.
    destruct gv2; try solve [inversion HeqR0].
    destruct p. simpl in HeqR0.
    remember (split gv2) as R4.
    destruct R4; inv HeqR0.
      inv Hmstore.
      destruct Hmsim as [Hmsim1 [Hmgb Hmsim2]].
      eapply Mem.store_mapped_inj with (f:=mi)(m2:=Mem2) in H0; 
        try solve [eauto | 
          inversion Hwfmi; eauto using meminj_no_overlap__implies].
      destruct H0 as [Mem2' [J2 J4]].
      exists Mem2'.
      destruct gv2.
        assert ( mstore TD Mem2
          ((Vptr b2 (Int.add 31 i1 (Int.repr 31 delta)), m1) :: nil) t
          ((v, m2) :: nil) align0 = ret Mem2') as J.
          unfold mstore. simpl. rewrite <- HeqR'.
          clear - J2 Hwfmi H2.
          inversion_clear Hwfmi.
          apply mi_range_block0 in H2. subst.
          rewrite Int.add_zero.
          assert (Int.signed 31 i1 + 0 = Int.signed 31 i1) as EQ. zauto.
          rewrite EQ in J2. rewrite J2. auto.
        split; auto.
        split.
        Case "wf_sb_mi".
          clear - Hwfmi J2.
          inversion Hwfmi.
          split; auto.
          SCase "Hmap4".
            intros b1 b0 delta2 J.
            apply Hmap4 in J.
            apply Mem.nextblock_store in J2.
            rewrite J2. auto.
          SCase "mi_mappedblocks0".
            intros b b' delta0 J.
            eapply Mem.store_valid_block_1; eauto.
          SCase "mi_reange_blocks0".
            intros b b' delta0 J.
            erewrite Mem.bounds_store with (m2:=Mem2'); eauto.

        Case "msim".
          split; auto.
          split.
            clear - Hmgb J2.
            apply Mem.nextblock_store in J2.
            rewrite J2. auto.
        
            clear Hmsim1.
            intros lc2 gl b ofs bgv egv als addrb addre bid0 eid0 v1 pgv' Hwfv 
              Hwfg G1 G2 G3.
            assert (G3':=G3).
            erewrite <- getOperandValue__mstore with (Mem:=Mem2)(t:=t)
            (gvp:=(Vptr b2 (Int.add 31 i1 (Int.repr 31 delta)), m1) :: nil)
            (gv:=(v, m2) :: nil)(align0:=align0) in G3'; eauto.
            apply Hmsim2 with (bgv:=bgv)(egv:=egv)(als:=als)(addrb:=addrb)
             (addre:=addre)(bid0:=bid0)(eid0:=eid0)(b:=b)(ofs:=ofs) in G3'; auto.
            destruct G3' as [bgv' [egv' [Mem3 [G4 [G5 [G6 G7]]]]]].
            exists bgv'. exists egv'.
            eapply get_mmetadata_fn__prop in G4; eauto.
            destruct G4 as [Mem3' [G41 G42]].
            exists Mem3'. split; auto.

      destruct p. simpl in HeqR4. destruct (split gv2). inversion HeqR4.
    destruct p. simpl in HeqR3. destruct (split gvp2). inversion HeqR3.
Qed.

Lemma get_const_metadata__wfc : forall c bc ec mt,
  SoftBound.get_const_metadata c = Some ((bc, ec), mt) ->
  wf_const bc /\ wf_const ec.
Proof.
  induction c; intros bc ec mt J; simpl in J; try solve [inversion J | auto].
    destruct t; inv J; simpl; auto.
      eapply IHc; eauto.
Qed.

Lemma mstore__get_reg_metadata : forall TD Mem0 gvp t gv align0 Mem' gl rm vp0,
  mstore TD Mem0 gvp t gv align0 = ret Mem' ->
  SoftBound.get_reg_metadata TD Mem0 gl rm vp0 =
    SoftBound.get_reg_metadata TD Mem' gl rm vp0.
Proof.
  intros TD Mem0 gvp t gv align0 Mem' gl rm vp0 Hmstore.
  unfold SoftBound.get_reg_metadata.
  destruct vp0; auto.
  destruct (SoftBound.get_const_metadata c) as [[[bc ec] t0]|]; auto.  
    erewrite const2GV__mstore; eauto.
    erewrite const2GV__mstore with (Mem:=Mem0); eauto.
Qed.

Lemma trans_nbranch__is__correct__dbStore_nptr: forall
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (sid : id)
  (t : typ)
  (v : value)
  (vp : value)
  (align0 : align)
  (Hnontemp : unsupported_cmd (insn_store sid t v vp align0))
  (Hnotin : wf_fresh ex_ids (insn_store sid t v vp align0) rm2)
  (isntcall : isCall (insn_store sid t v vp align0) = false)
  (Htrans : trans_nbranch ex_ids tmps optaddrb optaddre rm2
             (mkNB (insn_store sid t v vp align0) isntcall) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (rm : SoftBound.rmetadata)
  (lc : GVMap)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : SoftBound.mmetadata)
  mgb
  (Hwfmi: wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : mem_simulation mi TD mgb MM Mem0 Mem2)
  (gl : GVMap)
  (Hwfg : wf_globals mgb gl)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (als : list mblock)
  (gv : GenericValue)
  (gvp : GenericValue)
  (md : SoftBound.metadata)
  (Mem' : mem)
  mt0
  (H : SoftBound.get_reg_metadata TD Mem0 gl rm vp = Some (md,mt0))
  (H0 : getOperandValue TD Mem0 v lc gl = ret gv)
  (H1 : getOperandValue TD Mem0 vp lc gl = ret gvp)
  (H2 : SoftBound.assert_mptr TD t gvp md)
  (H3 : mstore TD Mem0 gvp t gv align0 = ret Mem')
  (H4 : ~ isPointerTyp t),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         wf_sb_mi mgb mi' Mem' Mem2' /\
         reg_simulation mi' TD gl rm rm2 Mem' Mem2' lc lc2' /\
         mem_simulation mi' TD mgb MM Mem' Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  simpl in Htrans.
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
  remember (isPointerTypB t) as R4.
  destruct R4.
  SCase "t is ptr".
    unfold isPointerTyp in H4.
    rewrite <- HeqR4 in H4.
    contradict H4; auto.

  SCase "t isnt ptr".
  inv Htrans.
  assert (J:=H2).
  unfold SoftBound.assert_mptr in J.
  destruct md as [md_base md_bound].

  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (getTypeAllocSize TD t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gv2 [H00 H01]].            
  eapply simulation__getOperandValue in H1; eauto.
  destruct H1 as [gvp2 [H10 H11]].            
  unfold SoftBound.get_reg_metadata in H.
  assert (Hmstore:=H3).
  eapply simulation__mstore in H3; eauto.
  destruct H3 as [Mem2' [H31 [H33 H32]]].
  destruct Hrsim as [Hrsim1 Hrsim2].
  assert (HeqR8':=H).
  apply Hrsim2 in HeqR8'.      
  destruct HeqR8' as [t2 [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]].
  exists 
        (updateAddAL _ 
          (updateAddAL _ 
           (updateAddAL GenericValue lc2 ptmp gvp2)
           btmp bgv2)
          etmp egv2).
  exists Mem2'. exists mi.
  split.
  SSCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H10.
        rewrite H10. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite J2. simpl. admit. (* given wf typ, t0 must be of ptr. *)

          clear - HeqR1 Hnotin J1.
          eapply get_reg_metadata__fresh in Hnotin; eauto.
          destruct Hnotin; auto.

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite J3. simpl. admit. (* given wf typ, t0 must be of ptr. *)

            clear - HeqR1 Hnotin J1.
            eapply get_reg_metadata__fresh in Hnotin; eauto.
            destruct Hnotin; auto.
   
          clear - HeqR1 Hnotin J1 HeqR2.
          eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids1)
            (c:=insn_store sid t v vp align0) in J1; eauto.
            destruct J1; auto.
            eapply wf_fresh__mk_tmp; eauto.  

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
       clear - H00 J1 J2 J3 J4 J5 J H10 H11 HeqR0 HeqR5 HeqR6 HeqR7.
       eapply assert_mptr_fn__ok with (b:=b)(b0:=b0)(b1:=b1); eauto.

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL _ (updateAddAL _ 
      (updateAddAL _ lc2 ptmp gvp2) btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2'); auto.
      apply SimpleSE.dbStore with (mp2:=gvp2)(gv1:=gv2); auto.
        clear - J1 Hnotin HeqR1 HeqR2 HeqR3 H00.
        destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]].
        unfold getCmdIDs in *. simpl in *.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.
          eapply get_reg_metadata_fresh' with (rm2:=rm2)(ex_ids:=ex_ids1); 
            eauto; try fsetdec.
            eapply wf_fresh__mk_tmp'; eauto; try fsetdec.
          eapply get_reg_metadata_fresh' with (rm2:=rm2)(ex_ids:=ex_ids2); 
            eauto; try fsetdec.
            eapply wf_fresh__mk_tmp' with (ptmp:=btmp)(ex_ids:=ex_ids1); 
              eauto; try fsetdec.
            eapply wf_fresh__mk_tmp'; eauto; try fsetdec.

        clear - J1 Hnotin HeqR1 HeqR2 HeqR3 H10.
        destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]].
        unfold getCmdIDs in *. simpl in *.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.
          eapply get_reg_metadata_fresh' with (rm2:=rm2)(ex_ids:=ex_ids1); 
            eauto; try fsetdec.
            eapply wf_fresh__mk_tmp'; eauto; try fsetdec.
          eapply get_reg_metadata_fresh' with (rm2:=rm2)(ex_ids:=ex_ids2); 
            eauto; try fsetdec.
            eapply wf_fresh__mk_tmp' with (ptmp:=btmp)(ex_ids:=ex_ids1); 
              eauto; try fsetdec.
            eapply wf_fresh__mk_tmp'; eauto; try fsetdec.

  split.
  SSCase "wfmi".
    clear - H33 H31 Hmstore Hwfmi.
    inversion H33.
    unfold mstore in Hmstore.
    destruct (GV2ptr TD (getPointerSize TD) gvp); try solve [inversion Hmstore].
    destruct v; try solve [inversion Hmstore].
    destruct (typ2memory_chunk t); try solve [inversion Hmstore].
    destruct (GV2val TD gv); try solve [inversion Hmstore].
    erewrite <- Mem.nextblock_store with (m1:=Mem0) in Hmap3; eauto.
    split; auto.
    SSSCase "mi_bounds".
      intros b1 b2 delta J.
      erewrite Mem.bounds_store with (m1:=Mem0); eauto.

  split; auto.
  SSCase "rsim".
    split.
    SSSCase "rsim1".
      clear - Hrsim1 subcase subsubcase.
      intros i0 gv1 J.
      apply Hrsim1 in J.
      destruct J as [gv2' [J J2]].
      exists gv2'.
      split; auto.
        admit. (* i0 <> bid eid tmp *)

    SSSCase "rsim2".
      intros vp0 bgv1 egv1 mt1 J6.
      erewrite <- mstore__get_reg_metadata in J6; eauto.
      apply Hrsim2 in J6.
      destruct J6 as [t0 [bv0 [ev0 [bgv0 [egv0 [J11 [J21 [J31 [J41 J51]]]]]]]]].
      exists t0. exists bv0. exists ev0. exists bgv0. exists egv0.
      split; auto.
      split.
        erewrite getOperandValue__mstore in J21; eauto.
        clear - HeqR1 Hnotin J11 J21 HeqR2 HeqR3.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite <- getOperandValue_eq_fresh_id; auto.
              eapply get_reg_metadata__fresh in Hnotin; eauto.
              destruct Hnotin; auto.
            eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids1)
              (c:=(insn_store sid t v vp align0)) in J11; eauto.
            destruct J11; auto.
            eapply wf_fresh__mk_tmp; eauto.  
          eapply get_reg_metadata__fresh with (ptmp:=etmp)(ex_ids:=ex_ids2)
            (c:=(insn_store sid t v vp align0)) in J11; eauto.
          destruct J11; auto.
          eapply wf_fresh__mk_tmp with (ex_ids:=ex_ids1); eauto.  
          eapply wf_fresh__mk_tmp; eauto.
       
      split.
        erewrite getOperandValue__mstore in J31; eauto.
        clear - HeqR1 Hnotin J11 J31 HeqR2 HeqR3.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite <- getOperandValue_eq_fresh_id; auto.
              eapply get_reg_metadata__fresh in Hnotin; eauto.
              destruct Hnotin; auto.
            eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids1)
              (c:=(insn_store sid t v vp align0)) in J11; eauto.
            destruct J11; auto.
            eapply wf_fresh__mk_tmp; eauto.  
          eapply get_reg_metadata__fresh with (ptmp:=etmp)(ex_ids:=ex_ids2)
            (c:=(insn_store sid t v vp align0)) in J11; eauto.
          destruct J11; auto.
          eapply wf_fresh__mk_tmp with (ex_ids:=ex_ids1); eauto.  
          eapply wf_fresh__mk_tmp; eauto.

      split; auto.
Qed.

Lemma memval_inject_trans : forall mi mv1 mv2 mv3,
  memval_inject mi mv1 mv2 ->
  memval_inject inject_id mv2 mv3 ->
  memval_inject mi mv1 mv3.
Proof.
  unfold inject_id.
  intros mi mv1 mv2 mv3 H1 H2.
  inv H1; inv H2; try solve [apply memval_inject_undef; auto].
    apply memval_inject_byte.

    inv H5.
    eapply memval_inject_ptr; eauto.
      rewrite Int.add_zero. auto.

    apply memval_inject_inttoptr; auto.
Qed.

Lemma simulation__set_mmetadata_fn : forall lc2 gl b ofs bgv egv als  
    pgv' bgv' egv' mi ptmp bv0 ev0 MM1 Mem1 Mem2 TD rm v gmb mt,  
  mem_simulation mi TD gmb MM1 Mem1 Mem2 ->
  SoftBound.get_reg_metadata TD Mem1 gl rm v = Some (SoftBound.mkMD bgv egv, mt)
    -> 
  lookupAL _ lc2 ptmp = Some pgv' ->
  getOperandValue TD Mem2 bv0 lc2 gl = Some bgv' ->
  getOperandValue TD Mem2 ev0 lc2 gl = Some egv' ->
  gv_inject mi (ptr2GV TD (Vptr b ofs)) pgv' ->
  gv_inject mi bgv bgv' ->
  gv_inject mi egv egv' ->
  exists Mem2',
    SimpleSE.dbCmd TD gl lc2 als Mem2
      (insn_call fake_id true sb_call_attrs set_mmetadata_typ set_mmetadata_fn
        ((p8, value_id ptmp) :: (p8, bv0) :: (p8, ev0) :: (p8, vnullp8) :: 
         (i32, vint1) :: (i32, vint1) :: nil)) 
      lc2 als Mem2' trace_nil /\
      mem_simulation mi TD gmb
        (SoftBound.set_mem_metadata TD MM1 (ptr2GV TD (Vptr b ofs)) 
        (SoftBound.mkMD bgv egv)) Mem1 Mem2'.
Proof.
  intros lc2 gl b ofs bgv egv als pgv' bgv' egv' mi ptmp bv0 ev0 MM1 Mem1 Mem2 TD
    rm v gmb mt Hmsim Hgetm Hlookup Hgetb Hgete Hinjp Hinjb Hinje.
  destruct (@set_mmetadata_fn__prop TD gl lc2 als Mem2 ptmp pgv' bv0 ev0 Hlookup)
    as [Mem2' [J [JW JW']]].
  exists Mem2'.
  split; auto.
  destruct Hmsim as [Hmsim1 [Hmgb Hmsim2]].
  split. 
    clear - Hmsim1 JW.
    inversion Hmsim1. inversion JW.
    unfold inject_id in *.
    split.
      intros b1 b2 delta chunk ofs p J1 J2.
      eapply mi_access in J2; eauto.
      assert (ofs + delta = ofs + delta + 0) as EQ.
        auto with zarith.
      rewrite EQ.
      eapply mi_access0 in J2; eauto.

      intros b1 ofs b2 delta J1 J2.
      assert (Jperm:=J2).
      eapply mi_memval in J2; eauto.
      apply Mem.perm_inj with (f:=mi)(delta:=delta)(m2:=Mem2)(b2:=b2) in Jperm;
        auto.     
      eapply mi_memval0 in Jperm; eauto.
      clear - J2 Jperm.
      assert (ofs + delta + 0 = ofs + delta) as EQ. auto with zarith.
      rewrite EQ in Jperm.
      eapply memval_inject_trans; unfold inject_id; eauto.

  split.
    clear - JW' Hmgb.
    eauto with zarith.

    clear Hmsim1.
    intros lc0 gl0 b0 ofs0 bgv0 egv0 als0 addrb addre bid0 eid0 v0 pgv'0 Hwf Hwfg
      J1 J2 J3.
    assert (getOperandValue TD Mem2 v0 lc0 gl0 = ret pgv'0) as G.
      clear - J3 J.
      erewrite <- set_mmetadata_fn__getOperandValue; eauto.

    unfold SoftBound.set_mem_metadata, SoftBound.get_mem_metadata, GV2ptr, 
      ptr2GV, val2GV in J1.
    destruct (zeq b0 b); subst; simpl in J1.
      destruct (Int.eq_dec 31 ofs ofs0); subst; simpl in J1.
        inv J1.      
        exists bgv'. exists egv'.
        clear - J Hinjb Hinje Hlookup Hgetb Hgete J3 J2 Hinjp. 
        eapply get_set_mmetadata_fn with (b:=b)(addrb:=addrb)(addre:=addre)(bid0:=bid0)(eid0:=eid0)(als0:=als0) in J; eauto.
        destruct J as [Mem2'0 [J1 J4]].
        exists Mem2'0. split; auto.       

        assert (G':=G).
        apply Hmsim2 with (b:=b)(ofs:=ofs0)(bgv:=bgv0)(egv:=egv0)(als:=als0)
          (addrb:=addrb)(addre:=addre)(bid0:=bid0)(eid0:=eid0) in G'; auto.
          destruct G' as [bgv0' [egv0' [Mem3' [G1 [G2 [G3 G4]]]]]]. 
          exists bgv0'.  exists egv0'.
            clear - J G G2 G3 G4 J2 n J3 Hlookup Hinjp.
            admit. (* get_mmetadata_fn__prop1 *) 

      assert (G':=G).
      apply Hmsim2 with (b:=b0)(ofs:=ofs0)(bgv:=bgv0)(egv:=egv0)(als:=als0)
        (addrb:=addrb)(addre:=addre)(bid0:=bid0)(eid0:=eid0) in G'; auto.
        destruct G' as [bgv0' [egv0' [Mem3' [G1 [G2 [G3 G4]]]]]]. 
        exists bgv0'.  exists egv0'.
        clear - J G G2 G3 G4 J2 n J3 Hlookup Hinjp.
        admit. (* get_mmetadata_fn__prop1 *) 
Qed.

Lemma mstore_inversion : forall Mem2 t align0 TD gvp2 Mem2'
  (gv2 : GenericValue)
  (H21 : mstore TD Mem2 gvp2 t gv2 align0 = ret Mem2'),
  exists b : Values.block, exists ofs : int32, gvp2 = ptr2GV TD (Vptr b ofs).
Proof.
  intros.
  unfold mstore in H21.
  remember (GV2ptr TD (getPointerSize TD) gvp2) as R.
  destruct R; try solve [inversion H21].
  destruct v; try solve [inversion H21].
  unfold GV2ptr in HeqR.
  destruct gvp2; try solve [inversion HeqR].
  destruct p.
  destruct v; try solve [inversion HeqR].
  destruct gvp2; inv HeqR.
  exists b0. exists i1. 
  unfold ptr2GV, val2GV.
  admit. (* we should check alignment too *)      
Qed.

Lemma trans_nbranch__is__correct__dbStore_ptr : forall
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (sid : id)
  (t : typ)
  (v : value)
  (vp : value)
  (align0 : align)
  (Hnontemp : unsupported_cmd (insn_store sid t v vp align0))
  (Hnotin : wf_fresh ex_ids (insn_store sid t v vp align0) rm2)
  (isntcall : isCall (insn_store sid t v vp align0) = false)
  (Htrans : trans_nbranch ex_ids tmps optaddrb optaddre rm2
             (mkNB (insn_store sid t v vp align0) isntcall) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (rm : SoftBound.rmetadata)
  (lc : GVMap)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : SoftBound.mmetadata)
  mgb
  (Hwfmi: wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : mem_simulation mi TD mgb MM Mem0 Mem2)
  (gl : GVMap)
  (Hwfg : wf_globals mgb gl)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (als : list mblock)
  (gv : GenericValue)
  (gvp : GenericValue)
  (md : SoftBound.metadata)
  (Mem' : mem)
  (md' : SoftBound.metadata)
  (MM' : SoftBound.mmetadata)
  mt1
  (H : SoftBound.get_reg_metadata TD Mem0 gl rm vp = ret (md,mt1))
  (H0 : getOperandValue TD Mem0 v lc gl = ret gv)
  (H1 : getOperandValue TD Mem0 vp lc gl = ret gvp)
  (H2 : SoftBound.assert_mptr TD t gvp md)
  (H3 : mstore TD Mem0 gvp t gv align0 = ret Mem')
  (H4 : isPointerTyp t)
  mt2
  (H5 : SoftBound.get_reg_metadata TD Mem0 gl rm v = ret (md',mt2))
  (H6 : SoftBound.set_mem_metadata TD MM gvp md' = MM'),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         wf_sb_mi mgb mi' Mem' Mem2' /\
         reg_simulation mi' TD gl rm rm2 Mem' Mem2' lc lc2' /\
         mem_simulation mi' TD mgb MM' Mem' Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  simpl in Htrans.
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids2].
  remember (mk_tmp ex_ids2) as R2. 
  destruct R2 as [btmp ex_ids3].
  remember (mk_tmp ex_ids3) as R3. 
  destruct R3 as [etmp ex_ids4].
  remember (isPointerTypB t) as R4.
  destruct R4.
  SCase "t is ptr".
    remember (get_reg_metadata rm2 v) as R5.
    destruct R5; try solve [inversion Htrans].
    destruct p as [[mt0 bv0] ev0].
    inv Htrans.

  assert (J:=H2).
  unfold SoftBound.assert_mptr in J.
  destruct md as [md_base md_bound].
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (getTypeAllocSize TD t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gv2 [H00 H01]].            
  eapply simulation__getOperandValue in H1; eauto.
  destruct H1 as [gvp2 [H10 H11]].            
  unfold SoftBound.get_reg_metadata in H.
  assert (H3':=H3).
  eapply simulation__mstore in H3'; eauto.
  destruct H3' as [Mem2' [H31 [H33 H32]]].
  destruct Hrsim as [Hrsim1 Hrsim2].

  destruct md' as [md_base' md_bound'].
  assert (HeqR9':=H).
  apply Hrsim2 in HeqR9'.      
  destruct HeqR9' as [t2 [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]].
  assert (H5':=H5).      
  apply Hrsim2 in H5'.
  destruct H5' as [t2' [bv2' [ev2' [bgv2' [egv2' [J1' [J2' [J3' [J4' J5']]]]]]]]].
  simpl in HeqR5.
  rewrite J1' in HeqR5.
  inv HeqR5.

  assert (exists Mem2'',
    SimpleSE.dbCmd TD gl 
      (updateAddAL _ (updateAddAL _ (updateAddAL GenericValue lc2 ptmp gvp2)
        btmp bgv2) etmp egv2)
      als Mem2'
      (insn_call fake_id true sb_call_attrs set_mmetadata_typ set_mmetadata_fn
        ((p8, value_id ptmp) :: 
         (p8, bv2') :: 
         (p8, ev2') :: (p8, vnullp8) :: 
         (i32, vint1) :: (i32, vint1) :: nil)) 
      (updateAddAL _ (updateAddAL _ (updateAddAL GenericValue lc2 ptmp gvp2)
        btmp bgv2) etmp egv2)
      als Mem2'' trace_nil /\
      mem_simulation mi TD mgb
        (SoftBound.set_mem_metadata TD MM gvp 
          (SoftBound.mkMD md_base' md_bound')) 
        Mem' Mem2'') as W.
    assert (exists b : Values.block, exists ofs : int32, 
      gvp = ptr2GV TD (Vptr b ofs)) as EQ.
      clear - H11 H31 H3.
      eapply mstore_inversion; eauto.
    destruct EQ as [b2 [ofs2 EQ]]. subst.
    apply simulation__set_mmetadata_fn with (pgv':=gvp2)(bgv':=bgv2')
      (egv':=egv2')(rm:=rm)(v:=v)(mt:=t2'); simpl; auto.
      clear - H5 H3 J1'.
      destruct v; simpl in *; auto.
        destruct (lookupAL (id * id) rm2 i0) as [[bid eid]|]; inv J1'; auto.
        destruct (lookupAL _ rm i0) as [md|]; inv H5; auto.

        destruct (SoftBound.get_const_metadata c) as [[[c0 c2] ct]|].
          remember (const2GV TD Mem0 gl c0) as R.
          destruct R; try solve [inv H5; auto].
          remember (const2GV TD Mem0 gl c2) as R'.
          destruct R'; try solve [inv H5; auto].
          simpl in *.
          inv H5. inv J1'.
          erewrite <- const2GV__mstore with (Mem:=Mem0); eauto.
          rewrite <- HeqR'.
          erewrite <- const2GV__mstore with (Mem:=Mem0); eauto.
          rewrite <- HeqR.
          simpl. auto.
      
          inv H5. 
          remember (Constant.getTyp c) as R.
          destruct R; inv J1'; auto.
            admit.           
    
      clear - HeqR1 HeqR2 HeqR3.
      rewrite <- lookupAL_updateAddAL_neq.
      rewrite <- lookupAL_updateAddAL_neq.
      rewrite lookupAL_updateAddAL_eq; auto.
        unfold mk_tmp in *.
        destruct (atom_fresh_for_list ex_ids); inv HeqR1.
        destruct (atom_fresh_for_list (x::ex_ids)); inv HeqR2.
        simpl in n0.
        intro J. apply n0. auto.

        unfold mk_tmp in *.
        destruct (atom_fresh_for_list ex_ids); inv HeqR1.
        destruct (atom_fresh_for_list (x::ex_ids)); inv HeqR2.
        destruct (atom_fresh_for_list (x0::x::ex_ids)); inv HeqR3.
        simpl in n1.
        intro J. apply n1. auto.

      clear - J2' H31 J1' Hnotin HeqR1 HeqR2 HeqR3.
      rewrite <- getOperandValue_eq_fresh_id.
      rewrite <- getOperandValue_eq_fresh_id.
      rewrite <- getOperandValue_eq_fresh_id.
        erewrite <- getOperandValue__mstore; eauto.

        eapply get_reg_metadata__fresh with (rm2:=rm2)
          (c:=insn_store sid t v vp align0) in J1'; 
          eauto; try fsetdec. destruct J1'; auto.

        eapply get_reg_metadata__fresh with (rm2:=rm2)
          (c:=insn_store sid t v vp align0)(ptmp:=btmp)(ex_ids:=ex_ids2) in J1'; 
          eauto; try fsetdec. destruct J1'; auto.
          eapply wf_fresh__mk_tmp; eauto.  

        eapply get_reg_metadata__fresh with (rm2:=rm2)
          (c:=insn_store sid t v vp align0)(ptmp:=etmp)(ex_ids:=ex_ids3) in J1'; 
          eauto; try fsetdec. destruct J1'; auto.
          eapply wf_fresh__mk_tmp with (ex_ids:=ex_ids2); eauto.  
          eapply wf_fresh__mk_tmp; eauto.  

      clear - J3' H31 J1' Hnotin HeqR1 HeqR2 HeqR3.
      rewrite <- getOperandValue_eq_fresh_id.
      rewrite <- getOperandValue_eq_fresh_id.
      rewrite <- getOperandValue_eq_fresh_id.
        erewrite <- getOperandValue__mstore; eauto.

        eapply get_reg_metadata__fresh with (rm2:=rm2)
          (c:=insn_store sid t v vp align0) in J1'; 
          eauto; try fsetdec. destruct J1'; auto.

        eapply get_reg_metadata__fresh with (rm2:=rm2)
          (c:=insn_store sid t v vp align0)(ptmp:=btmp)(ex_ids:=ex_ids2) in J1'; 
          eauto; try fsetdec. destruct J1'; auto.
          eapply wf_fresh__mk_tmp; eauto.  

        eapply get_reg_metadata__fresh with (rm2:=rm2)
          (c:=insn_store sid t v vp align0)(ptmp:=etmp)(ex_ids:=ex_ids3) in J1'; 
          eauto; try fsetdec. destruct J1'; auto.
          eapply wf_fresh__mk_tmp with (ex_ids:=ex_ids2); eauto.  
          eapply wf_fresh__mk_tmp; eauto.  

  destruct W as [Mem2'' [W1 W2]].

  exists 
          (updateAddAL _ 
            (updateAddAL _ 
             (updateAddAL GenericValue lc2 ptmp gvp2)
              btmp bgv2)
             etmp egv2).
  exists Mem2''. exists mi.
  split.
    SSCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H10.
        rewrite H10. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite J2. simpl. admit. (* given wf typ, t0 must be of ptr. *)

          clear - HeqR1 Hnotin J1.
          eapply get_reg_metadata__fresh in Hnotin; eauto.
          destruct Hnotin; auto.

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite J3. simpl. admit. (* given wf typ, t0 must be of ptr. *)

            clear - HeqR1 Hnotin J1.
            eapply get_reg_metadata__fresh in Hnotin; eauto.
            destruct Hnotin; auto.
   
          clear - HeqR1 Hnotin J1 HeqR2.
          eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids2)
            (c:=insn_store sid t v vp align0) in J1; eauto.
            destruct J1; auto.
            eapply wf_fresh__mk_tmp; eauto.  

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
       clear - H00 J1 J2 J3 J4 J5 J H10 H11 HeqR0 HeqR6 HeqR7 HeqR8.
       eapply assert_mptr_fn__ok with (b:=b)(b0:=b0)(b1:=b1); eauto.

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)(als2:=als)(Mem2:=Mem2'); auto.
      apply SimpleSE.dbStore with (mp2:=gvp2)(gv1:=gv2); auto.
        clear - J1 Hnotin HeqR1 HeqR2 HeqR3 H00.
        destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]].
        unfold getCmdIDs in *. simpl in *.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.
          eapply get_reg_metadata_fresh' with (rm2:=rm2)(ex_ids:=ex_ids2); 
            eauto; try fsetdec.
            eapply wf_fresh__mk_tmp'; eauto; try fsetdec.
          eapply get_reg_metadata_fresh' with (rm2:=rm2)(ex_ids:=ex_ids3); 
            eauto; try fsetdec.
            eapply wf_fresh__mk_tmp' with (ptmp:=btmp)(ex_ids:=ex_ids2); 
              eauto; try fsetdec.
            eapply wf_fresh__mk_tmp'; eauto; try fsetdec.

        clear - J1 Hnotin HeqR1 HeqR2 HeqR3 H10.
        destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]].
        unfold getCmdIDs in *. simpl in *.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.
          eapply get_reg_metadata_fresh' with (rm2:=rm2)(ex_ids:=ex_ids2); 
            eauto; try fsetdec.
            eapply wf_fresh__mk_tmp'; eauto; try fsetdec.
          eapply get_reg_metadata_fresh' with (rm2:=rm2)(ex_ids:=ex_ids3); 
            eauto; try fsetdec.
            eapply wf_fresh__mk_tmp' with (ptmp:=btmp)(ex_ids:=ex_ids2); 
              eauto; try fsetdec.
            eapply wf_fresh__mk_tmp'; eauto; try fsetdec.

    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)(als2:=als)(Mem2:=Mem2''); auto.

  split.
  SSCase "wfmi".
    clear - H33 H31 H3 Hwfmi W1.
    inversion H33.
    unfold mstore in H3.
    destruct (GV2ptr TD (getPointerSize TD) gvp); try solve [inversion H3].
    destruct v; try solve [inversion H3].
    destruct (typ2memory_chunk t); try solve [inversion H3].
    destruct (GV2val TD gv); try solve [inversion H3].
    erewrite <- Mem.nextblock_store with (m1:=Mem0) in Hmap3; eauto.
    apply set_mmetadata_fn__prop' in W1.
    destruct W1 as [W1 [W2 W3]].
    split; auto.
    SSSCase "Hmap4".
      intros b1 b2 delta2 J.
      apply Hmap4 in J.
      eauto with zarith.
    SSSCase "mappedblocks0".
      intros b1 b2 delta J.
      apply mi_mappedblocks0 in J.
      eauto.
    SSSCase "bounds0".
      intros b1 b2 delta J.
      apply mi_bounds0 in J.
      rewrite <- W3.
      erewrite Mem.bounds_store with (m1:=Mem0); eauto.

  split; auto.
    SSCase "rsim".

    split.
      SSSSCase "rsim1".
      clear - Hrsim1 subcase subsubcase.
      intros i0 gv1 J.
      apply Hrsim1 in J.
      destruct J as [gv2' [J J2]].
      exists gv2'.
      split; auto.
        admit. (* i0 <> bid eid tmp *)

      SSSSCase "rsim2".
      intros vp0 bgv1 egv1 mt1' J6.
      erewrite <- mstore__get_reg_metadata in J6; eauto.
      apply Hrsim2 in J6.
      destruct J6 as [t0 [bv0 [ev0 [bgv0 [egv0 [J11 [J21 [J31 [J41 J51]]]]]]]]].
      exists t0. exists bv0. exists ev0. exists bgv0. exists egv0.
      split; auto.
      erewrite getOperandValue__mstore in J21; eauto.
      erewrite getOperandValue__mstore in J31; eauto.
      erewrite <- set_mmetadata_fn__getOperandValue in J21; eauto.
      erewrite <- set_mmetadata_fn__getOperandValue in J31; eauto.
      split.
        clear - HeqR1 Hnotin J11 J21 HeqR2 HeqR3.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite <- getOperandValue_eq_fresh_id; auto.
              eapply get_reg_metadata__fresh in Hnotin; eauto.
              destruct Hnotin; auto.
            eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids2)
              (c:=(insn_store sid t v vp align0)) in J11; eauto.
            destruct J11; auto.
            eapply wf_fresh__mk_tmp; eauto.  
          eapply get_reg_metadata__fresh with (ptmp:=etmp)(ex_ids:=ex_ids3)
            (c:=(insn_store sid t v vp align0)) in J11; eauto.
          destruct J11; auto.
          eapply wf_fresh__mk_tmp with (ex_ids:=ex_ids2); eauto.  
          eapply wf_fresh__mk_tmp; eauto.
       
      split.
        clear - HeqR1 Hnotin J11 J31 HeqR2 HeqR3.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite <- getOperandValue_eq_fresh_id; auto.
              eapply get_reg_metadata__fresh in Hnotin; eauto.
              destruct Hnotin; auto.
            eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids2)
              (c:=(insn_store sid t v vp align0)) in J11; eauto.
            destruct J11; auto.
            eapply wf_fresh__mk_tmp; eauto.  
          eapply get_reg_metadata__fresh with (ptmp:=etmp)(ex_ids:=ex_ids3)
            (c:=(insn_store sid t v vp align0)) in J11; eauto.
          destruct J11; auto.
          eapply wf_fresh__mk_tmp with (ex_ids:=ex_ids2); eauto.  
          eapply wf_fresh__mk_tmp; eauto.

      split; auto.

  SCase "t isnt ptr".
    unfold isPointerTyp in H4.
    rewrite H4 in HeqR4.
    inversion HeqR4.
Qed.

Lemma trans_nbranch__is__correct__dbLoad_abort : forall
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (id0 : id)
  (t : typ)
  (vp : value)
  (align0 : align)
  (Hnontemp : unsupported_cmd (insn_load id0 t vp align0))
  (Hnotin : wf_fresh ex_ids (insn_load id0 t vp align0) rm2)
  (isntcall : isCall (insn_load id0 t vp align0) = false)
  (Htrans : trans_nbranch ex_ids tmps optaddrb optaddre rm2
             (mkNB (insn_load id0 t vp align0) isntcall) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (rm : SoftBound.rmetadata)
  (lc : GVMap)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : SoftBound.mmetadata)
  mgb
  (Hwfmi : wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : mem_simulation mi TD mgb MM Mem0 Mem2)
  (gl : GVMap)
  (Hwfg : wf_globals mgb gl)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (als : list mblock)
  (gvp : GenericValue)
  (md : SoftBound.metadata)
  mt0
  (H : SoftBound.get_reg_metadata TD Mem0 gl rm vp = ret (md,mt0))
  (H0 : getOperandValue TD Mem0 vp lc gl = ret gvp)
  (H1 : ~ SoftBound.assert_mptr TD t gvp md),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         wf_sb_mi mgb mi' Mem0 Mem2' /\
         reg_simulation mi' TD gl rm rm2 Mem0 Mem2' lc lc2' /\
         mem_simulation mi' TD mgb MM Mem0 Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  simpl in Htrans.
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
  remember (isPointerTypB t) as R4.
  destruct R4.
  SCase "t is ptr".
    admit.

  SCase "t isnt ptr".
  inv Htrans.
  assert (J:=H1).
  destruct md as [md_base md_bound].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gvp2 [H00 H01]].            
  destruct Hrsim as [Hrsim1 Hrsim2].
  unfold SoftBound.get_reg_metadata in H.
  assert (HeqR8':=H).
  apply Hrsim2 in HeqR8'.      
  destruct HeqR8' as [t2 [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]].
  exists 
        (updateAddAL _ 
          (updateAddAL _ 
           (updateAddAL GenericValue lc2 ptmp gvp2)
           btmp bgv2)
          etmp egv2).
  exists Mem2. exists mi.
  split.
    SSCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H00.
        rewrite H00. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite J2. simpl. admit. (* given wf typ, t0 must be of ptr. *)

          clear - HeqR1 Hnotin J1.
          eapply get_reg_metadata__fresh in Hnotin; eauto.
          destruct Hnotin; auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite J3. simpl. admit. (* given wf typ, t0 must be of ptr. *)

            clear - HeqR1 Hnotin J1.
            eapply get_reg_metadata__fresh in Hnotin; eauto.
            destruct Hnotin; auto.
   
          clear - HeqR1 Hnotin J1 HeqR2.
          eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids1)
            (c:=insn_load id0 t vp align0) in J1; eauto.
            destruct J1; auto.
            eapply wf_fresh__mk_tmp; eauto.  
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
       clear - H00 J1 J2 J3 J4 J5 J H00 H01.
       admit. (* assert_mptr_fn' axiom. *)
    admit. (* unreachable, if dbCmds support abort. *)

  split; auto.
  split; auto.
    SSCase "rsim".

    split.
      SSSCase "rsim1".
      clear - Hrsim1 subcase subsubcase.
      intros i0 gv1 J.
      apply Hrsim1 in J.
      destruct J as [gv2' [J J2]].
      exists gv2'.
      split; auto.
        admit. (* i0 <> bid eid tmp *)

      SSSCase "rsim2".
      intros vp0 bgv1 egv1 mt1 J6.
      apply Hrsim2 in J6.
      destruct J6 as [t0 [bv0 [ev0 [bgv0 [egv0 [J11 [J21 [J31 [J41 J51]]]]]]]]].
      exists t0. exists bv0. exists ev0. exists bgv0. exists egv0.
      split; auto.
      split.
        clear - HeqR1 Hnotin J11 J21 HeqR2 HeqR3.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite <- getOperandValue_eq_fresh_id; auto.
              eapply get_reg_metadata__fresh in Hnotin; eauto.
              destruct Hnotin; auto.
            eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids1)
              (c:=(insn_load id0 t vp align0)) in J11; eauto.
            destruct J11; auto.
            eapply wf_fresh__mk_tmp; eauto.  
          eapply get_reg_metadata__fresh with (ptmp:=etmp)(ex_ids:=ex_ids2)
            (c:=(insn_load id0 t vp align0)) in J11; eauto.
          destruct J11; auto.
          eapply wf_fresh__mk_tmp with (ex_ids:=ex_ids1); eauto.  
          eapply wf_fresh__mk_tmp; eauto.

      split.
        clear - HeqR1 Hnotin J11 J31 HeqR2 HeqR3.
        rewrite <- getOperandValue_eq_fresh_id.
          rewrite <- getOperandValue_eq_fresh_id.
            rewrite <- getOperandValue_eq_fresh_id; auto.
              eapply get_reg_metadata__fresh in Hnotin; eauto.
              destruct Hnotin; auto.
            eapply get_reg_metadata__fresh with (ptmp:=btmp)(ex_ids:=ex_ids1)
              (c:=(insn_load id0 t vp align0)) in J11; eauto.
            destruct J11; auto.
            eapply wf_fresh__mk_tmp; eauto.  
          eapply get_reg_metadata__fresh with (ptmp:=etmp)(ex_ids:=ex_ids2)
            (c:=(insn_load id0 t vp align0)) in J11; eauto.
          destruct J11; auto.
          eapply wf_fresh__mk_tmp with (ex_ids:=ex_ids1); eauto.  
          eapply wf_fresh__mk_tmp; eauto.

      split; auto.
Qed.

Lemma const2GV__free' : forall TD Mem0 b lo hi Mem' gl c,
  Mem.free Mem0 b lo hi = ret Mem' ->
  _const2GV TD Mem0 gl c = _const2GV TD Mem' gl c.
Proof.
  intros TD Mem0 b lo hi Mem' gl c Hfree.
  induction c; simpl in *; try solve 
    [ auto | rewrite IHc; auto | 
      rewrite IHc1; rewrite IHc2; auto |
      rewrite IHc1; rewrite IHc2; rewrite IHc3; auto ].
    admit.
    admit.
    rewrite IHc.
    destruct (_const2GV TD Mem' gl c0); auto.
    destruct p.
    unfold mcast, mptrtoint.
    destruct t0; auto.
      destruct c; auto.
        destruct t; auto.
          destruct (GV2val TD g); auto.
            destruct v; auto.
              erewrite Mem.int2ptr_free; eauto.
      destruct c; auto.
        destruct t; auto.
          destruct (GV2val TD g); auto.
            destruct v; auto.
              erewrite Mem.ptr2int_free; eauto.
    admit.
Qed.  

Lemma const2GV__free : forall TD Mem0 b lo hi Mem' gl c,
  Mem.free Mem0 b lo hi = ret Mem' ->
  const2GV TD Mem0 gl c = const2GV TD Mem' gl c.
Proof.
  intros TD Mem0 b lo hi Mem' gl c Hfree. unfold const2GV.
  erewrite const2GV__free'; eauto.
Qed.

Lemma getOperandValue__free : forall TD Mem0 b lo hi Mem' gl lc v,
  Mem.free Mem0 b lo hi = ret Mem' ->
  getOperandValue TD Mem0 v lc gl = getOperandValue TD Mem' v lc gl.
Proof.
  intros TD Mem0 b lo hi Mem' gl lc v Hmstore.
  destruct v as [vid |]; simpl; auto.
    erewrite const2GV__free; eauto.
Qed.

Lemma free__get_reg_metadata : forall TD Mem0 b lo hi Mem' gl rm vp0,
  Mem.free Mem0 b lo hi = ret Mem' ->
  SoftBound.get_reg_metadata TD Mem0 gl rm vp0 =
    SoftBound.get_reg_metadata TD Mem' gl rm vp0.
Proof.
  intros TD Mem0 b lo hi Mem' gl rm vp0 Hfree.
  unfold SoftBound.get_reg_metadata.
  destruct vp0; auto.
  destruct (SoftBound.get_const_metadata c) as [[[bc ec] t]|]; auto.  
  erewrite const2GV__free; eauto.
  erewrite const2GV__free with (Mem0:=Mem0); eauto.
Qed.

Lemma trans_nbranch__is__correct__dbFree : forall
  (lc2 : GVMap)
  (Mem2 : Mem.mem_)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (mgb : Z)
  (fid : id)
  (t : typ)
  (v : value)
  (gl : GVMap)
  (Hwfg : wf_globals mgb gl)
  (Hnotin : wf_fresh ex_ids (insn_free fid t v) rm2)
  (isntcall : isCall (insn_free fid t v) = false)
  (Htrans : trans_nbranch ex_ids tmps optaddrb optaddre rm2 
              (mkNB (insn_free fid t v) isntcall) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (Mem0 : mem)
  (Hwfmi : wf_sb_mi mgb mi Mem0 Mem2)
  (TD : TargetData)
  (rm : SoftBound.rmetadata)
  (lc : GVMap)
  (Hrsim : reg_simulation mi TD gl rm rm2 Mem0 Mem2 lc lc2)
  (MM : SoftBound.mmetadata)
  (Hmsim : mem_simulation mi TD mgb MM Mem0 Mem2)
  (als : list mblock)
  (Mem' : mem)
  (mptr0 : GenericValue)
  (H : getOperandValue TD Mem0 v lc gl = ret mptr0)
  (H0 : free TD Mem0 mptr0 = ret Mem'),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         wf_sb_mi mgb mi' Mem' Mem2' /\
         reg_simulation mi' TD gl rm rm2 Mem' Mem2' lc lc2' /\
         mem_simulation mi' TD mgb MM Mem' Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  inv Htrans.
  unfold free in H0.
  remember (GV2ptr TD (getPointerSize TD) mptr0) as R0.
  destruct R0; try solve [inversion H0].
  destruct v0; try solve [inversion H0].
  remember (zeq (Int.signed 31 i0) 0) as R1.
  destruct R1; try solve [inversion H0].
  remember (Mem.bounds Mem0 b) as R2.  
  destruct R2 as [lo hi].
  eapply simulation__getOperandValue in H; eauto.
  destruct H as [mptr0' [H1 H2]].
  symmetry in HeqR0.
  eapply simulation__GV2ptr in HeqR0; eauto.
  destruct HeqR0 as [v' [J1 J2]].
  inv J2.
  destruct Hmsim as [Hmsim1 [Hmgb Hmsim2]].  
  assert ({ Mem2':Mem.mem | Mem.free Mem2 b2 (lo+delta) (hi+delta) = ret Mem2'}) 
    as J.
    apply Mem.range_perm_free.
    apply Mem.free_range_perm in H0.
    clear - H0 Hmsim1 H4.
    unfold Mem.range_perm in *.
    intros ofs J.
    assert (lo <= ofs - delta < hi) as J'.
      auto with zarith.
    apply H0 in J'.
    eapply Mem.perm_inj in J'; eauto.
    assert (ofs - delta + delta = ofs) as EQ. auto with zarith.
    rewrite EQ in J'. auto.
  destruct J as [Mem2' J].
  exists lc2. exists Mem2'. exists mi.
  split.
  SCase "dbCmds".
    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    eapply SimpleSE.dbCmds_cons; eauto.
      apply SimpleSE.dbFree with (mptr:=mptr0'); auto.
        unfold free.     
        rewrite J1.
        inversion_clear Hwfmi.
        assert (H4':=H4).
        apply mi_range_block0 in H4'. subst.
        rewrite Int.add_zero.
        destruct (zeq (Int.signed 31 i0) 0).
          apply mi_bounds0 in H4.
          rewrite <- H4. rewrite <- HeqR2.   
          assert (lo + 0 = lo) as EQ''. auto with zarith. 
          rewrite EQ'' in J. clear EQ''.
          assert (hi + 0 = hi) as EQ''. auto with zarith.
          rewrite EQ'' in J. clear EQ''.
          auto.

          clear - e n. contradict e; auto.          

  split.
  SCase "wfmi".
    clear - Hwfmi H0 J H4.
    inversion_clear Hwfmi.
    split; eauto with mem.
    SSCase "Hmap3".
      intros. erewrite Mem.nextblock_free in H; eauto.
    SSCase "Hmap4".
      intros. erewrite Mem.nextblock_free; eauto.
    SSCase "bounds".
      intros. apply mi_bounds0 in H. 
      erewrite Mem.bounds_free; eauto.
      erewrite Mem.bounds_free with (m2:=Mem2'); eauto.

  split. 
  SCase "rsim".
    destruct Hrsim as [Hrsim1 Hrsim2].
    split; auto.
    SSCase "rsim2".
      clear - Hrsim2 J H4 H0.
      intros vp bgv1 egv1 mt1 J1.
      erewrite <- free__get_reg_metadata in J1; eauto.
      apply Hrsim2 in J1. 
      destruct J1 as [t2 [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]].
      erewrite getOperandValue__free in J2; eauto.
      erewrite getOperandValue__free in J3; eauto.
      exists t2. exists bv2. exists ev2. exists bgv2. exists egv2.
      split; auto.

  split; auto.
  SCase "msim".
    split.
      clear - Hmsim1 Hwfmi H0 J H4.
      assert (J':=Hmsim1).
      eapply Mem.free_left_inj in J'; eauto.
      eapply Mem.free_right_inj in J'; eauto.
      intros b1 delta0 ofs p H1 H2 H3.
      destruct (Values.eq_block b b1); subst.
        rewrite H1 in H4. inv H4.
        apply Mem.perm_free_2 with (p:=p)(ofs:=ofs) in H0; eauto with zarith.

        destruct Hwfmi.
        unfold meminj_no_overlap in Hno_overlap0.
        apply Hno_overlap0 with (b1':=b2)(b2':=b2)(delta1:=delta)(delta2:=delta0)
          in n; auto.

    split.
      clear - Hmgb J.
      apply Mem.nextblock_free in J.
      rewrite J. auto.
  
      clear Hmsim1 Hmgb.
      intros lc0 gl0 b0 ofs bgv egv als0 addrb addre bid0 eid0 v1 pgv' Hwfv 
        Hwfg0 G1 G2 G3.
      assert (G3':=G3).
      erewrite <- getOperandValue__free in G3'; eauto.
      apply Hmsim2 with (bgv:=bgv)(egv:=egv)(als:=als0)(addrb:=addrb)
       (addre:=addre)(bid0:=bid0)(eid0:=eid0)(b:=b0)(ofs:=ofs) in G3'; auto.
      destruct G3' as [bgv' [egv' [Mem3 [G4 [G5 [G6 G7]]]]]].
      exists bgv'. exists egv'.
      eapply get_mmetadata_fn__prop' in G4; eauto.
      destruct G4 as [Mem3' [G41 G42]].
      exists Mem3'. split; auto.
Qed.

Lemma trans_nbranch__is__correct : forall c TD lc1 rm1 als gl Mem1 MM1 lc1' als' 
    Mem1' MM1' tr lc2 Mem2 rm2 rm1' cs ex_ids tmps ex_ids' tmps' r
    optaddrb optaddre optaddrb' optaddre' mi mgb (isntcall : isCall c = false),  
  wf_cmd c ->
  wf_globals mgb gl ->
  unsupported_cmd c ->
  wf_fresh ex_ids c rm2 ->
  trans_nbranch ex_ids tmps optaddrb optaddre rm2 (mkNB c isntcall) = 
    Some (ex_ids', tmps', cs, optaddrb', optaddre') ->
  wf_sb_mi mgb mi Mem1 Mem2 ->
  reg_simulation mi TD gl rm1 rm2 Mem1 Mem2 lc1 lc2 ->
  mem_simulation mi TD mgb MM1 Mem1 Mem2 ->
  SoftBound.dbCmd TD gl lc1 rm1 als Mem1 MM1 c lc1' rm1' als' Mem1' MM1' tr r ->
  exists lc2', exists Mem2', exists mi',
    SimpleSE.dbCmds TD gl lc2 als Mem2 cs lc2' als' Mem2' tr /\
    wf_sb_mi mgb mi' Mem1' Mem2' /\
    reg_simulation mi' TD gl rm1' rm2 Mem1' Mem2' lc1' lc2' /\
    mem_simulation mi' TD mgb MM1' Mem1' Mem2' /\
    Values.inject_incr mi mi'.
Proof.
  intros c TD lc1 rm1 als gl Mem1 MM1 lc1' als' Mem1' MM1' tr lc2 Mem2 rm2 rm1' 
    cs ex_ids tmps ex_ids' tmps' r optaddrb optaddre optaddrb' optaddre' mi mgb
    isntcall Hwfc Hwfg Hnontemp Hnotin Htrans Hwfmi Hrsim Hmsim HdbCmd.
  (sb_dbCmd_cases (destruct HdbCmd) Case); 
    simpl in Hwfc; try solve [inversion Hnontemp].

Case "dbBop".
  inv Htrans.
  eapply simulation__BOP in H; eauto.
  destruct H as [gv3' [H1 H2]].
  exists (updateAddAL GenericValue lc2 id0 gv3'). exists Mem2. exists mi.
  split.
   assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
   rewrite EQ.
   eapply SimpleSE.dbCmds_cons; eauto.
     apply SimpleSE.dbBop; auto.
  split; auto.
  split; auto.
    destruct Hnotin as [Hnotin _]. 
    unfold getCmdIDs in Hnotin. simpl in Hnotin.
    apply reg_simulation__updateAddAL; try solve [auto | fsetdec].

admit. admit. admit.

Case "dbMalloc".
  eapply trans_nbranch__is__correct__dbMalloc; eauto.

Case "dbMalloc_error".
  admit.    

Case "dbFree".
  eapply trans_nbranch__is__correct__dbFree; eauto.

Case "dbFree_error".
  admit. 

Case "dbAlloca".
  admit. 

Case "dbAlloca_error".
  admit. 

Case "dbLoad_nptr".
  eapply trans_nbranch__is__correct__dbLoad_nptr; eauto.

Case "dbLoad_ptr".
  simpl in Htrans.
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt1 bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids2].
  remember (mk_tmp ex_ids2) as R2. 
  destruct R2 as [btmp ex_ids3].
  remember (mk_tmp ex_ids3) as R3. 
  destruct R3 as [etmp ex_ids4].
  remember (isPointerTypB t) as R4.
  destruct R4.
  SCase "t is ptr".
    remember (lookupAL (id * id) rm2 id0) as R5.
    destruct R5; try solve [inversion Htrans].
    destruct p as [bid0 eid0].
    destruct optaddrb as [addrb | ].
      destruct optaddre as [addre | ]; inv Htrans.
        eapply trans_nbranch__is__correct__dbLoad_ptr; eauto.

      destruct optaddre as [addre | ]; inv Htrans.
        remember (mk_tmp ex_ids4) as W0.
        destruct W0 as [addrb ex_ids0].
        remember (mk_tmp ex_ids0) as W1.
        destruct W1 as [addre ex_ids1].
        inv H7.
        eapply trans_nbranch__is__correct__dbLoad_ptr; eauto. 

  SCase "t isnt ptr".
    unfold isPointerTyp in H3.
    rewrite <- HeqR4 in H3.
    inversion H3.

Case "dbLoad_error1".
admit. 

Case "dbLoad_error2".
admit. 

Case "dbLoad_error3".
admit.

Case "dbLoad_abort".
  eapply trans_nbranch__is__correct__dbLoad_abort; eauto.

Case "dbStore_nptr".
  eapply trans_nbranch__is__correct__dbStore_nptr; eauto.

Case "dbStore_ptr".
  eapply trans_nbranch__is__correct__dbStore_ptr; eauto.

Case "dbStore_error1".
  admit. 
  
Case "dbStore_error2".
  admit.
 
Case "dbStore_error3".
  admit.

Case "dbStore_abort".
  simpl in Htrans.
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt1 bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
  remember (isPointerTypB t) as R4.
  destruct R4.
    remember (get_reg_metadata rm2 v) as R5.
    destruct R5; try solve [inversion Htrans].
    destruct p as [bv0 ev0].
    inv Htrans.
    admit.

    inv Htrans.
    admit.

Case "dbGEP".

Admitted.

Lemma trans_nbranchs__is__correct : forall nbs TD lc1 rm1 als gl Mem1 MM1 lc1' 
    als' Mem1' MM1' tr lc2 Mem2 rm2 rm1' cs' ex_ids tmps ex_ids' tmps' r mgb
    optaddrb optaddre optaddrb' optaddre' mi, 
  wf_cmds (nbranchs2cmds nbs) ->
  wf_globals mgb gl ->
  unsupported_cmds (nbranchs2cmds nbs) ->
  wf_freshs ex_ids (nbranchs2cmds nbs) rm2 ->
  trans_nbranchs ex_ids tmps optaddrb optaddre rm2 nbs = 
    Some (ex_ids', tmps', cs', optaddrb', optaddre') ->
  wf_sb_mi mgb mi Mem1 Mem2 ->
  reg_simulation mi TD gl rm1 rm2 Mem1 Mem2 lc1 lc2 ->
  mem_simulation mi TD mgb MM1 Mem1 Mem2 ->
  SoftBound.dbCmds TD gl lc1 rm1 als Mem1 MM1 (nbranchs2cmds nbs) lc1' rm1' als'
    Mem1' MM1' tr r ->
  exists lc2', exists Mem2', exists mi',
    SimpleSE.dbCmds TD gl lc2 als Mem2 cs' lc2' als' Mem2' tr /\
    wf_sb_mi mgb mi' Mem1' Mem2' /\
    reg_simulation mi' TD gl rm1' rm2 Mem1' Mem2' lc1' lc2' /\
    mem_simulation mi' TD mgb MM1' Mem1' Mem2' /\
    Values.inject_incr mi mi'.
Proof.
  induction nbs; intros; simpl in *.
    inv H3.
    exists lc2. exists Mem2. exists mi.
    inv H7.
    split; auto.

    destruct a as [c isntcall]. simpl in H, H1, H2.
    destruct H as [J1 J2].
    destruct H1 as [J3 J4].
    destruct H2 as [J5 J6].
    remember (trans_nbranch ex_ids tmps optaddrb optaddre rm2 
      {| nbranching_cmd := c; notcall := isntcall |}) as R.
    destruct R as [[[[[ex_ids1 tmps1] cs1] optaddrb1] optaddre1] |];
      try solve [inversion H3].
    remember (trans_nbranchs ex_ids1 tmps1 optaddrb1 optaddre1 rm2 nbs) as R.
    destruct R as [[[[[ex_ids2 tmps2] cs2] optaddrb2] optaddre2] |]; inv H3.
    inv H7.
      eapply trans_nbranch__is__correct in H13; eauto.
      destruct H13 as [lc2' [Mem2' [mi' [J7 [J8 [J9 [J10 J11]]]]]]].
      assert (wf_freshs ex_ids1 (nbranchs2cmds nbs) rm2) as J13.
        clear - HeqR J6. 
        admit. (* fresh *)
      eapply IHnbs with (cs':=cs2)(ex_ids:=ex_ids1) in H21; eauto.
      destruct H21 as 
        [lc2'' [Mem2'' [mi'' [J7' [J8' [J9' [J10' J11']]]]]]].
      simpl.
      exists lc2''. exists Mem2''. exists mi''.
      split.
        clear - J7 J7'.
        admit. (* dbCmds appending *)
      split; auto.
      split; auto.
      split; auto.
        eapply inject_incr_trans; eauto.

      eapply trans_nbranch__is__correct with (tmps:=tmps)(tmps':=tmps1)(cs:=cs1)
        (ex_ids':=ex_ids1)(optaddrb:=optaddrb)(optaddre:=optaddre)
        (isntcall:=isntcall)(optaddrb':=optaddrb1)(optaddre':=optaddre1) in H13;
        eauto.
      destruct H13 as [lc2' [Mem2' [mi' [J7 [J8 [J9 [J10 J11]]]]]]].
      exists lc2'. exists Mem2'. exists mi'.
      split; auto.
        clear - J7 H21.
        admit. (* dbCmds should support error *)
Qed.

Definition trans_call__is__correct_prop S1 TD Ps1 fs gl lc1 rm1 Mem1 MM1 call1 
  lc1' rm1' Mem1' MM1' tr r 
(db:SoftBound.dbCall S1 TD Ps1 fs gl lc1 rm1 Mem1 MM1 call1 lc1' rm1' Mem1' MM1' 
  tr r) :=
  forall lc2 Mem2 rm2 cs' ex_ids tmps ex_ids' tmps' mgb
    optaddrb optaddre optaddrb' optaddre' mi als iscall1 Ps2 S2 los nts, 
  wf_cmd call1 ->
  wf_globals mgb gl ->
  wf_fresh ex_ids call1 rm2 ->
  TD = (los, nts) ->
  trans_products nts Ps1 = Some Ps2 ->
  trans_system S1 = Some S2 ->
  trans_call ex_ids tmps optaddrb optaddre rm2 call1 iscall1 = 
    Some (ex_ids', tmps', cs', optaddrb', optaddre') ->
  wf_sb_mi mgb mi Mem1 Mem2 ->
  reg_simulation mi TD gl rm1 rm2 Mem1 Mem2 lc1 lc2 ->
  mem_simulation mi TD mgb MM1 Mem1 Mem2 ->
  exists lc2', exists Mem2', exists mi',
    SimpleSE.dbSubblock S2 TD Ps2 fs gl lc2 als Mem2 cs' lc2' als Mem2' tr /\
    wf_sb_mi mgb mi' Mem1' Mem2' /\
    reg_simulation mi' TD gl rm1' rm2 Mem1' Mem2' lc1' lc2' /\
    mem_simulation mi' TD mgb MM1' Mem1' Mem2' /\
    Values.inject_incr mi mi'.

Fixpoint alloca_simulation (mi:meminj) (als1 als2:list mblock) : Prop :=
match als1 with
| nil => True
| b1::als1' => 
    match mi b1 with
    | Some (b2, 0) => In b2 als2
    | _ => False
    end
end.

Definition trans_subblock__is__correct_prop S1 TD Ps1 fs gl lc1 rm1 als1 Mem1 MM1
  cs lc1' rm1' als1' Mem1' MM1' tr r
(db:SoftBound.dbSubblock S1 TD Ps1 fs gl lc1 rm1 als1 Mem1 MM1 cs lc1' rm1' als1'
  Mem1' MM1' tr r) :=
  forall lc2 Mem2 rm2 cs' ex_ids tmps ex_ids' tmps' mgb optaddrb optaddre 
    optaddrb' optaddre' mi als2 sb los nts Ps2 S2, 
  unsupported_cmds cs ->
  wf_cmds cs ->
  wf_globals mgb gl ->
  wf_freshs ex_ids cs rm2 ->
  cmds2sbs cs = (sb::nil, nil) ->
  TD = (los, nts) ->
  trans_products nts Ps1 = Some Ps2 ->
  trans_system S1 = Some S2 ->
  trans_subblock ex_ids tmps optaddrb optaddre rm2 sb = 
    Some (ex_ids', tmps', optaddrb', optaddre', cs') ->
  wf_sb_mi mgb mi Mem1 Mem2 ->
  reg_simulation mi TD gl rm1 rm2 Mem1 Mem2 lc1 lc2 ->
  mem_simulation mi TD mgb MM1 Mem1 Mem2 ->
  alloca_simulation mi als1 als2 ->
  exists lc2', exists Mem2', exists mi', exists als2',
    SimpleSE.dbSubblock S2 TD Ps2 fs gl lc2 als2 Mem2 cs' lc2' als2' Mem2' tr /\
    wf_sb_mi mgb mi' Mem1' Mem2' /\
    reg_simulation mi' TD gl rm1' rm2 Mem1' Mem2' lc1' lc2' /\
    mem_simulation mi' TD mgb MM1' Mem1' Mem2' /\
    alloca_simulation mi als1' als2' /\
    Values.inject_incr mi mi'.

Definition trans_subblocks__is__correct_prop S1 TD Ps1 fs gl lc1 rm1 als1 Mem1 
  MM1 cs lc1' rm1' als1' Mem1' MM1' tr r 
(db:SoftBound.dbSubblocks S1 TD Ps1 fs gl lc1 rm1 als1 Mem1 MM1 cs lc1' rm1' 
  als1' Mem1' MM1' tr r) :=
  forall lc2 Mem2 rm2 cs' ex_ids tmps ex_ids' tmps' mgb optaddrb optaddre 
    optaddrb' optaddre' mi als2 sbs S2 Ps2 los nts, 
  unsupported_cmds cs ->
  wf_cmds cs ->
  wf_globals mgb gl ->
  wf_freshs ex_ids cs rm2 ->
  cmds2sbs cs = (sbs, nil) ->
  TD = (los, nts) ->
  trans_products nts Ps1 = Some Ps2 ->
  trans_system S1 = Some S2 ->
  trans_subblocks ex_ids tmps optaddrb optaddre rm2 sbs = 
    Some (ex_ids', tmps', optaddrb', optaddre', cs') ->
  wf_sb_mi mgb mi Mem1 Mem2 ->
  reg_simulation mi TD gl rm1 rm2 Mem1 Mem2 lc1 lc2 ->
  mem_simulation mi TD mgb MM1 Mem1 Mem2 ->
  alloca_simulation mi als1 als2 ->
  (cs = nil) \/
  (exists lc2', exists Mem2', exists mi', exists als2',
    SimpleSE.dbSubblocks S2 TD Ps2 fs gl lc2 als2 Mem2 cs' lc2' als2' Mem2' tr /\
    wf_sb_mi mgb mi' Mem1' Mem2' /\
    reg_simulation mi' TD gl rm1' rm2 Mem1' Mem2' lc1' lc2' /\
    mem_simulation mi' TD mgb MM1' Mem1' Mem2' /\
    alloca_simulation mi als1' als2' /\
    Values.inject_incr mi mi').

Definition trans_block__is__correct_prop S1 TD Ps1 fs gl F1 state1 state1' tr r
  (db:SoftBound.dbBlock S1 TD Ps1 fs gl F1 state1 state1' tr r) :=
  forall B1 lc1 rm1 als1 Mem1 MM1 B1' lc1' als1' Mem1' MM1' lc2 Mem2 rm2 rm1'
    ex_ids tmps ex_ids' tmps' mgb optaddrb optaddre optaddrb' optaddre' mi 
    B2 als2 S2 Ps2 los nts fh1 lb1 fh2 lb2, 
  state1 = SoftBound.mkState (SoftBound.mkEC B1 lc1 rm1 als1) Mem1 MM1 ->
  state1' = SoftBound.mkState (SoftBound.mkEC B1' lc1' rm1' als1') Mem1' MM1' ->
  F1 = fdef_intro fh1 lb1 ->
  wf_globals mgb gl ->
  productInSystemModuleB (product_fdef F1) S1 (module_intro los nts Ps1) ->
  TD = (los, nts) ->
  trans_products nts Ps1 = Some Ps2 ->
  trans_system S1 = Some S2 ->
  trans_block ex_ids tmps optaddrb optaddre rm2 B1 = 
    Some (ex_ids', tmps', optaddrb', optaddre', B2) ->
  trans_fdef nts F1 = Some (fdef_intro fh2 lb2) ->
  wf_sb_mi mgb mi Mem1 Mem2 ->
  reg_simulation mi TD gl rm1 rm2 Mem1 Mem2 lc1 lc2 ->
  mem_simulation mi TD mgb MM1 Mem1 Mem2 ->
  alloca_simulation mi als1 als2 ->
  exists lc2', exists Mem2', exists mi', exists B2', exists als2', exists n,
    SimpleSE.dbBlock S2 TD Ps2 fs gl (fdef_intro fh2 lb2)
     (SimpleSE.mkState (SimpleSE.mkEC B2 lc2 als2) Mem2)
     (SimpleSE.mkState (SimpleSE.mkEC B2' lc2' als2') Mem2') tr /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    trans_block ex_ids tmps optaddrb optaddre rm2 B1' = 
      Some (ex_ids', tmps', optaddrb', optaddre', B2') /\
    wf_sb_mi mgb mi' Mem1' Mem2' /\
    reg_simulation mi' TD gl rm1' rm2 Mem1' Mem2' lc1' lc2' /\
    mem_simulation mi' TD mgb MM1' Mem1' Mem2' /\
    alloca_simulation mi als1' als2' /\
    Values.inject_incr mi mi'.

Definition trans_blocks__is__correct_prop S1 TD Ps1 fs gl F1 state1 state1' tr r
  (db:SoftBound.dbBlocks S1 TD Ps1 fs gl F1 state1 state1' tr r) :=
  forall B1 lc1 rm1 als1 Mem1 MM1 B1' lc1' als1' Mem1' MM1' lc2 Mem2 rm2 rm1'
    ex_ids tmps ex_ids' tmps' mgb optaddrb optaddre optaddrb' optaddre' mi
    Ps2 S2 als2 los nts fh1 lb1 fh2 lb2 n, 
  state1 = SoftBound.mkState (SoftBound.mkEC B1 lc1 rm1 als1) Mem1 MM1 ->
  state1' = SoftBound.mkState (SoftBound.mkEC B1' lc1' rm1' als1') Mem1' MM1' ->
  wf_globals mgb gl ->
  productInSystemModuleB (product_fdef F1) S1 (module_intro los nts Ps1) ->
  TD = (los, nts) ->
  trans_products nts Ps1 = Some Ps2 ->
  trans_system S1 = Some S2 ->
  trans_blocks ex_ids tmps optaddrb optaddre rm2 lb1 = 
    Some (ex_ids', tmps', optaddrb', optaddre', lb2) ->
  trans_fdef nts F1 = Some (fdef_intro fh2 lb2) ->
  F1 = fdef_intro fh1 lb1 ->
  nth_error lb1 n = Some B1 ->
  wf_sb_mi mgb mi Mem1 Mem2 ->
  reg_simulation mi TD gl rm1 rm2 Mem1 Mem2 lc1 lc2 ->
  mem_simulation mi TD mgb MM1 Mem1 Mem2 ->
  alloca_simulation mi als1 als2 ->
  exists lc2', exists Mem2', exists mi', exists B2, exists B2', exists als2', 
    exists n',
    SimpleSE.dbBlocks S2 TD Ps2 fs gl (fdef_intro fh2 lb2)
     (SimpleSE.mkState (SimpleSE.mkEC B2 lc2 als2) Mem2)
     (SimpleSE.mkState (SimpleSE.mkEC B2' lc2' als2') Mem2') tr /\
    nth_error lb2 n = Some B2 /\
    nth_error lb1 n' = Some B1' /\
    nth_error lb2 n' = Some B2' /\
    trans_block ex_ids tmps optaddrb optaddre rm2 B1 = 
      Some (ex_ids', tmps', optaddrb', optaddre', B2) /\
    trans_block ex_ids tmps optaddrb optaddre rm2 B1' = 
      Some (ex_ids', tmps', optaddrb', optaddre', B2') /\
    wf_sb_mi mgb mi' Mem1' Mem2' /\
    reg_simulation mi' TD gl rm1' rm2 Mem1' Mem2' lc1' lc2' /\
    mem_simulation mi' TD mgb MM1' Mem1' Mem2' /\
    alloca_simulation mi als1' als2' /\
    Values.inject_incr mi mi'.

Definition trans_fdef__is__correct_prop fv rt lp S1 TD Ps1 lc1 rm1 gl fs Mem1 
  MM1 lc1' rm1' als1' Mem1' MM1' B1' Rid oResult tr r
  (db:SoftBound.dbFdef fv rt lp S1 TD Ps1 lc1 rm1 gl fs Mem1 MM1 lc1' rm1' als1'
    Mem1' MM1' B1' Rid oResult tr r) :=
  forall Ps2 S2 lc2 Mem2 rm2 rm1' mgb mi los nts fd1 lb1 fd2 lb2 ex_ids 
    tmps optaddrb optaddre ex_ids' tmps' optaddrb' optaddre',
  LLVMopsem.lookupFdefViaGV TD Mem1 Ps1 gl lc1 fs fv = 
    Some (fdef_intro fd1 lb1) ->
  moduleInSystem (module_intro los nts Ps1) S1 ->
  wf_globals mgb gl ->
  TD = (los, nts) ->
  trans_products nts Ps1 = Some Ps2 ->
  trans_system S1 = Some S2 ->
  trans_fdef nts (fdef_intro fd1 lb1) = Some ((fdef_intro fd2 lb2)) ->
  wf_sb_mi mgb mi Mem1 Mem2 ->
  reg_simulation mi TD gl rm1 rm2 Mem1 Mem2 lc1 lc2 ->
  mem_simulation mi TD mgb MM1 Mem1 Mem2 ->
  exists lc2', exists Mem2', exists mi', exists B2', exists als2', exists n,
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    trans_block ex_ids tmps optaddrb optaddre rm2 B1' = 
      Some (ex_ids', tmps', optaddrb', optaddre', B2') /\
    LLVMopsem.lookupFdefViaGV TD Mem2 Ps2 gl lc2 fs fv = 
      Some (fdef_intro fd1 lb2) /\
    trans_blocks ex_ids tmps optaddrb optaddre rm2 lb1 = 
      Some (ex_ids', tmps', optaddrb', optaddre', lb2) /\
    dbFdef fv rt lp S2 TD Ps2 lc2 gl fs Mem2 lc2' als2' Mem2' B2' Rid oResult 
      tr /\
    wf_sb_mi mgb mi' Mem1' Mem2' /\
    reg_simulation mi' TD gl rm1' rm2 Mem1' Mem2' lc1' lc2' /\
    mem_simulation mi' TD mgb MM1' Mem1' Mem2' /\
    Values.inject_incr mi mi'.
    
Axiom callLib__is__defined : forall Mem fid gvs,
  callLib Mem fid gvs <> None <-> isCallLib fid = true.

Lemma dbCmd_isNotCallInst : forall TD lc rm als gl Mem1 MM1 c lc' rm' als' Mem2 
    MM2 tr r,
  SoftBound.dbCmd TD gl lc rm als Mem1 MM1 c lc' rm' als' Mem2 MM2 tr r ->
  isCall c = false.
Admitted.
(*Proof.
  intros TD lc rm als gl Mem1 MM1 c lc' rm' als' Mem2 MM2 tr r HdbCmd.
  induction HdbCmd; auto.
    simpl.
    assert (isCallLib fid = true) as J.
      eapply callLib__is__defined with (Mem:=Mem0) (gvs:=gvs).
      rewrite H0. intro J. inversion J.
    rewrite J. auto.

    simpl.
    assert (isCallLib fid = true) as J.
      eapply callLib__is__defined with (Mem:=Mem0) 
        (gvs:=params2GVs TD Mem0 lp lc gl).
      rewrite H. intro J. inversion J.
    rewrite J. auto.
Qed.
*)

Definition dbCmd2nbranch : forall TD lc rm als gl Mem1 MM1 c lc' rm' als' Mem2 
  MM2 tr r, 
  SoftBound.dbCmd TD gl lc rm als Mem1 MM1 c lc' rm' als' Mem2 MM2 tr r ->
  exists nb, cmd2nbranch c = Some nb.
Proof.
  intros.
  apply dbCmd_isNotCallInst in H.
  unfold cmd2nbranch.
  destruct (isCall_dec).
    exists (mkNB c e). auto.
    rewrite H in e. inversion e.
Qed.

Definition dbCmds__cmds2nbs : forall TD lc rm als gl Mem1 MM1 cs lc' rm' als' 
    Mem2 MM2 tr r, 
  SoftBound.dbCmds TD gl lc rm als Mem1 MM1 cs lc' rm' als' Mem2 MM2 tr r ->
  r <> SoftBound.rok \/ exists nbs, cmds2sbs cs = (nil, nbs).
Proof.
  intros.
  induction H; simpl.
    right. exists nil. auto.

    destruct IHdbCmds as [J | [nbs J]]; auto.
      destruct (isCall_dec c).
        rewrite J. right. exists (mkNB c e::nbs). auto.
        apply dbCmd_isNotCallInst in H.
        rewrite e in H. inversion H.

    left. destruct r; try solve [intro J; inversion J | inversion H0].
Qed.

Lemma dbCall_isCall : forall S TD Ps lc rm gl fs Mem1 MM1 c lc' rm' Mem2 MM2 tr
    r,
  SoftBound.dbCall S TD Ps fs gl lc rm Mem1 MM1 c lc' rm' Mem2 MM2 tr r ->
  isCall c = true.
Proof.
  intros S TD Ps lc rm gl fs Mem1 MM1 c lc' rm' Mem2 MM2 tr r HdbCall.
  induction HdbCall; auto.
Qed.

Lemma dbSubblock__cmds2sb : forall S TD Ps fs gl lc1 rm1 als1 Mem1 MM1 cs lc2 rm2
    als2 Mem2 MM2 tr r,
  SoftBound.dbSubblock S TD Ps fs gl lc1 rm1 als1 Mem1 MM1 cs lc2 rm2 als2 Mem2 
    MM2 tr r ->
  r <> SoftBound.rok \/ exists sb, cmds2sbs cs = (sb::nil, nil).
Proof.
  intros.
  inversion H; subst.
    apply dbCmds__cmds2nbs in H0.
    destruct H0 as [H0 | [nbs H0]]; auto.
    remember (isCall_dec call0) as R.
    destruct R.
      apply dbCall_isCall in H1.
      rewrite e in H1. inversion H1.

      right. exists (mkSB nbs call0 e).
      apply cmdscall2sbs; auto.

    left. destruct r; try solve [intro J; inversion J | inversion H1].
Qed.

Lemma dbSubblocks__cmds2sbs : forall S TD Ps fs gl lc1 rm1 als1 Mem1 MM1 cs lc2 
    rm2 als2 Mem2 MM2 tr r,
  SoftBound.dbSubblocks S TD Ps fs gl lc1 rm1 als1 Mem1 MM1 cs lc2 rm2 als2 Mem2
    MM2 tr r ->
  r <> SoftBound.rok \/ exists sbs, cmds2sbs cs = (sbs, nil).
Proof.
  intros.
  induction H; simpl.
    right. exists nil. auto.

    apply dbSubblock__cmds2sb in H.
    destruct H as [H | [sb H]]; auto.
    destruct IHdbSubblocks as [H1 | [sbs H1]]; auto.
    right. exists (sb::sbs). apply cmds_cons2sbs; auto.

    left. destruct r; try solve [intro J; inversion J | inversion H0].
Qed.

Lemma trans_terminator__is__correct : forall M1 fh1 lb1 fh2 lb2 B1 B2 lc1 gl tmn
    B1' lc1' tr rm1 ex_ids tmps optb opte ex_ids' tmps' optb' opte' los nts rm2
    M2 MM1 mi mgb lc2,
  trans_fdef nts (fdef_intro fh1 lb1) = Some (fdef_intro fh2 lb2) ->
  trans_block ex_ids tmps optb opte rm2 B1 = 
    Some (ex_ids', tmps', optb', opte', B2) ->
  dbTerminator (los, nts) M1 (fdef_intro fh1 lb1) gl B1 lc1 tmn B1' lc1' tr ->
  wf_sb_mi mgb mi M1 M2 ->
  reg_simulation mi (los, nts) gl rm1 rm2 M1 M2 lc1 lc2 ->
  mem_simulation mi (los, nts) mgb MM1 M1 M2 ->
  exists B2', exists n, exists lc2',
    trans_block ex_ids tmps optb opte rm2 B1' = 
      Some (ex_ids', tmps', optb', opte', B2') /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    reg_simulation mi (los, nts) gl rm1 rm2 M1 M2 lc1' lc2' /\
    dbTerminator (los, nts) M2 (fdef_intro fh2 lb2) gl B2 lc2 tmn B2' lc2' tr.
Admitted.

Lemma trans_blocks_nth_Some_inv : forall lb1 lb2 n B1 ex_ids tmps optb opte rm2
    ex_ids' tmps' optb' opte',
  trans_blocks ex_ids tmps optb opte rm2 lb1 = 
    Some (ex_ids', tmps', optb', opte', lb2) ->
  nth_error lb1 n = Some B1 ->
  exists B2, 
    nth_error lb2 n = Some B2 /\ 
    trans_block ex_ids tmps optb opte rm2 B1 = 
      Some (ex_ids', tmps', optb', opte', B2).
Admitted.

Lemma trans__is__correct :
  (forall S1 TD Ps1 fs gl lc1 rm1 Mem1 MM1 call1 lc1' rm1' Mem1' MM1' tr r db, 
     trans_call__is__correct_prop S1 TD Ps1 fs gl lc1 rm1 Mem1 MM1 call1 lc1' 
       rm1' Mem1' MM1' tr r db) 
    /\
  (forall S1 TD Ps1 fs gl lc1 rm1 als1 Mem1 MM1 sb lc1' rm1' als1' Mem1' MM1' tr 
       r db,
     trans_subblock__is__correct_prop S1 TD Ps1 fs gl lc1 rm1 als1 Mem1 MM1 sb 
       lc1' rm1' als1' Mem1' MM1' tr r db) /\
  (forall S1 TD Ps1 fs gl lc1 rm1 als1 Mem1 MM1 sbs lc1' rm1' als1' Mem1' MM1' 
       tr r db,
     trans_subblocks__is__correct_prop S1 TD Ps1 fs gl lc1 rm1 als1 Mem1 MM1 sbs 
       lc1' rm1' als1' Mem1' MM1' tr r db) /\
  (forall S1 TD Ps1 fs gl F1 state1 state1' tr r db,
     trans_block__is__correct_prop S1 TD Ps1 fs gl F1 state1 state1' tr r db) /\
  (forall S1 TD Ps1 fs gl F1 state1 state1' tr r db,
     trans_blocks__is__correct_prop S1 TD Ps1 fs gl F1 state1 state1' tr r db) /\
  (forall fv rt lp S1 TD Ps1 lc1 rm1 gl fs Mem1 MM1 lc1' rm1' als1' Mem1' MM1' 
       B1' Rid oResult tr r db,
     trans_fdef__is__correct_prop fv rt lp S1 TD Ps1 lc1 rm1 gl fs Mem1 MM1 lc1' 
       rm1' als1' Mem1' MM1' B1' Rid oResult tr r db).
Proof.
(sb_db_mutind_cases
  apply SoftBound.sb_db_mutind with
    (P  := trans_call__is__correct_prop)
    (P0 := trans_subblock__is__correct_prop)
    (P1 := trans_subblocks__is__correct_prop)
    (P2 := trans_block__is__correct_prop)
    (P3 := trans_blocks__is__correct_prop)
    (P4 := trans_fdef__is__correct_prop) Case);
  unfold trans_call__is__correct_prop, 
         trans_fdef__is__correct_prop, trans_subblock__is__correct_prop,
         trans_subblocks__is__correct_prop, 
         trans_block__is__correct_prop,
         trans_blocks__is__correct_prop.

Focus. Case "dbCall_internal". admit. (* unsupported *) Unfocus.
Focus. Case "dbCall_external". admit. (* unsupported *) Unfocus.
Focus. Case "dbCall_internal_error1". admit. (* unsupported *) Unfocus.
Focus. Case "dbCall_internal_error2". admit. (* unsupported *) Unfocus.
Focus. Case "dbCall_external_error1". admit. (* unsupported *) Unfocus.
Focus. Case "dbCall_external_error2". admit. (* unsupported *) Unfocus.
Focus.
Case "dbSubblock_ok".
  intros S1 TD Ps1 lc1 rm1 als1 gl fs Mem1 MM1 cs call0 lc2 rm2 als2 Mem2 MM2 
    tr1 lc3 rm3 Mem3 MM3 tr2 r Hcmds Hcall IH lc0 Mem0 rm0 cs' ex_ids tmps 
    ex_ids' tmps' mgb optaddrb optaddre optaddrb' optaddre' mi als0 sb los nts 
    Ps2 S2 Hunspt Hwfcs Hwfg Hfreshs Hc2s Heq HtransPs HtransS HtransSB Hwfmi 
    Hrsim Hmsim Hasim.
  unfold trans_subblock in HtransSB.
  destruct sb.
  remember (trans_nbranchs ex_ids tmps optaddrb optaddre rm0 NBs0) as R1.
  destruct R1 as [[[[[ex_ids1 tmps1] cs1] optaddrb1] optaddre1] | ];
    try solve [inversion HtransSB].
  remember (trans_call ex_ids1 tmps1 optaddrb1 optaddre1 rm0 call_cmd0
           call_cmd_isCall0) as R2.
  destruct R2 as [[[[[ex_ids2 tmps2] cs2] optaddrb2] optaddre2]|]; inv HtransSB.
  assert (wf_cmds cs /\ wf_cmd call0) as Hwfcs'.    
    clear - Hwfcs. admit. (* wf_cmds *)
  destruct Hwfcs' as [Hwfcs1 Hwfc2].
  assert (unsupported_cmds cs /\ unsupported_cmd call0) as Hunspts'.    
    clear - Hunspt. admit. (* unspt *)
  destruct Hunspts' as [Hunspts1 Hunspt2].
  assert (wf_freshs ex_ids cs rm0 /\ wf_fresh ex_ids1 call0 rm0) as Hfreshs'.
    clear - Hfreshs. admit. (* fresh *)
  destruct Hfreshs' as [Hfreshs1 Hfresh2].
  apply cmds2sb_inv in Hc2s.
  destruct Hc2s as [cs' [call1 [J1 [J2 J3]]]].
  apply cmds2nbs__nbranchs2cmds in J2.
  apply app_inj_tail in J1.
  destruct J1; subst. simpl in *.
  eapply trans_nbranchs__is__correct in Hcmds; eauto.
  destruct Hcmds as [lc2' [Mem2' [mi' [J4 [J5 [J6 [J7 J8]]]]]]].
  symmetry in HeqR2. 
  eapply IH with (als:=als2) in HeqR2; eauto.
  destruct HeqR2 as [lc2'' [Mem2'' [mi'' [J4' [J5' [J6' [J7' J8']]]]]]].
  exists lc2''. exists Mem2''. exists mi''. exists als2.
  split. 
    clear - J4 J4'.
    inv J4'.
    assert (cs1 ++ cs ++ call0 :: nil = (cs1 ++ cs) ++ call0 :: nil) as EQ.
      simpl_env. auto.
    rewrite EQ.
    rewrite trace_app_commute.
    eapply dbSubblock_intro; eauto.
      admit. (* dbCmds++ and als *)
  split; auto.
  split; auto.
  split; auto.
  split.
    admit. (*als*)
    clear - J8 J8'. apply inject_incr_trans with (f2:=mi'); auto.
Unfocus.

Focus.
Case "dbSubblock_error". admit.
Unfocus.

Focus.
Case "dbSubblocks_nil".
  auto.
Unfocus.

Focus.
Case "dbSubblocks_cons".
  intros S TD Ps lc1 rm1 als1 gl fs Mem1 MM1 lc2 rm2 als2 Mem2 MM2 lc3 als3 rm3
    Mem3 MM3 cs cs' t1 t2 r Hsubblock IH1 Hsubblocks IH2 lc0 Mem0 rm0 cs'0 
    ex_ids tmps ex_ids' tmps' mgb optaddrb optaddre optaddrb' optaddre' mi als0
    sbs S2 Ps2 los nts Hunspt Hwfcs Hwfg Hfreshs Hc2s Heq HtransPS HtransS 
    HtransSB Hwfmi Hrsim Hmsim Hasim.
  assert (Hcs2sb := Hsubblock).
  apply dbSubblock__cmds2sb in Hcs2sb.
  destruct Hcs2sb as [J | [sb Hcs2sb]]. contradict J; auto.
  assert (Hcs'2sbs := Hsubblocks).
  apply dbSubblocks__cmds2sbs in Hcs'2sbs.
  destruct Hcs'2sbs as [J | [sbs' Hcs'2sbs]].
    admit. (* symexe_op should support error *)
  apply cmds_cons2sbs_inv with (sb:=sb)(sbs':=sbs') in Hc2s; auto.
  subst.
  simpl in HtransSB.
  remember (trans_subblock ex_ids tmps optaddrb optaddre rm0 sb) as R1.
  destruct R1 as [[[[[ex_ids1 tmps1] optaddrb1] optaddre1] cs1] |]; 
    try solve [inversion HtransSB].
  remember (trans_subblocks ex_ids1 tmps1 optaddrb1 optaddre1 rm0 sbs') as R2.
  destruct R2 as [[[[[ex_ids2 tmps2] optaddrb2] optaddre2] cs2] |]; inv HtransSB.
  symmetry in HeqR1, HeqR2.
  assert (unsupported_cmds cs /\ unsupported_cmds cs') as J.
    clear - Hunspt. admit.
  destruct J as [Hunspt1 Hunspt2].
  assert (wf_cmds cs /\ wf_cmds cs') as J.
    clear - Hwfcs. admit.
  destruct J as [Hwfc1 Hwfc2].
  assert (wf_freshs ex_ids cs rm0 /\ wf_freshs ex_ids1 cs' rm0) as J.
    clear - Hfreshs. admit.
  destruct J as [Hfreshs1 Hfreshs2].
  eapply IH1 in HeqR1; eauto.
  destruct HeqR1 as [lc2' [Mem2' [mi' [als2' [J1 [J2 [J3 [J4 [J5 J6]]]]]]]]].
  assert (HtransSBs':=HeqR2).
  assert (alloca_simulation mi' als2 als2') as W.
    admit. (*als*)
  eapply IH2 with (als4:=als2') in HeqR2; eauto.
  destruct HeqR2 as 
    [ | [lc2'' [Mem2'' [mi'' [als2'' [J1' [J2' [J3' [J4' [J5' J6']]]]]]]]]].
  SSCase "1".
     subst. right. clear IH2 IH1.
     simpl in Hcs'2sbs. inv Hcs'2sbs.
     simpl in HtransSBs'. inv HtransSBs'. simpl_env.
     exists lc2'. exists Mem2'. exists mi'. exists als2'.
     inv Hsubblocks.
       rewrite_env (cs1++nil).
       split; eauto.
         
       admit. (* to prove: dbSubblocks changes nothing for nil cmds *)
       admit. (* error symexe op *)
  SSCase "2".
     right. clear IH2 IH1.
     exists lc2''. exists Mem2''. exists mi''. exists als2''.
     split; eauto.
     split; auto.
     split; auto.
     split; auto.
     split. admit. (*als*)
       clear - J6 J6'. apply inject_incr_trans with (f2:=mi'); auto.
Unfocus.

Focus. Case "dbSubblocks_cons_error". admit. Unfocus.

Focus. Case "dbBlock_ok".
  intros S TD Ps F tr1 tr2 l0 ps cs cs' tmn gl fs lc1 rm als1 Mem1 MM1 lc2 rm2
    als2 Mem2 MM2 lc3 rm3 als3 Mem3 MM3 lc4 B' tr3 Hsubblocks IH1 Hcmds
    Htmn B1 lc0 rm0 als0 Mem0 MM0 B1' lc1' als1' Mem1' MM1' lc5 Mem4 rm5 rm1' 
    ex_ids tmps ex_ids' tmps' mgb optaddrb optaddre optaddrb' optaddre' mi B2
    als4 S2 Ps2 los nts fh1 lb1 fh2 lb2 Heq Heq' Heq''' Hwfg Hinc Heq'' HtransPs 
    HtransS HtransB HtransF Hwfmi Hrim Hmsim Hasim.
  inv Heq. inv Heq'.
  assert (HtransB':=HtransB).
  simpl in HtransB.

  remember (cmds2sbs (cs++cs')) as R1.
  destruct R1 as [sbs1 nbs1].
  remember (trans_phinodes rm5 ps) as R2.
  destruct R2 as [ps2 |]; try solve [inversion HtransB].
  remember (trans_subblocks ex_ids tmps optaddrb optaddre rm5 sbs1) as R3.
  destruct R3 as [[[[[ex_ids1 tmps1] optaddrb1] optaddre1] cs1] |]; 
    try solve [inversion HtransB].
  remember (trans_nbranchs ex_ids1 tmps1 optaddrb1 optaddre1 rm5 nbs1) as R4.
  destruct R4 as [[[[[ex_ids2 tmps2] cs2] optaddrb2] optaddre2] |]; inv HtransB.
  assert (Hcs2sbs1 := Hsubblocks).
  apply dbSubblocks__cmds2sbs in Hcs2sbs1.
  destruct Hcs2sbs1 as [J | [sbs Hcs2sbs1]].
    contradict J; auto.
  assert (Hcs2nbs1 := Hcmds).
  apply dbCmds__cmds2nbs in Hcs2nbs1.
  destruct Hcs2nbs1 as [J | [nbs Hcs2nbs1]].
    contradict J; auto.
  apply cmds2nbs__nbranchs2cmds in Hcs2nbs1. subst.
  assert (J:=HeqR1).
  symmetry in J.
  assert (cmds2sbs (nbranchs2cmds nbs) = (nil, nbs)) as EQ.
    admit.
  apply cmds_rcons2sbs_inv with (sbs:=sbs)(nbs:=nbs) in J; 
    auto using cmds2nbranchs__cmds2nbs.
  destruct J; subst.

  symmetry in HeqR4, HeqR3, HeqR2.
  assert (unsupported_cmds cs /\ unsupported_cmds (nbranchs2cmds nbs)) as J.
    admit.
  destruct J as [Hunspt1 Hunspt2].
  assert (wf_cmds cs /\ wf_cmds (nbranchs2cmds nbs)) as J.
    admit.
  destruct J as [Hwfc1 Hwfc2].
  assert (wf_freshs ex_ids cs rm5 /\ wf_freshs ex_ids1 (nbranchs2cmds nbs) rm5) 
    as J.
    admit.
  destruct J as [Hfreshs1 Hfreshs2].
  assert (HtransSBs:=HeqR3).
  eapply IH1 in HeqR3; eauto. clear IH1.
  destruct HeqR3 as 
    [ | [lc2' [Mem2' [mi' [als2' [J1 [J2 [J3 [J4 [J5 J6]]]]]]]]]]; subst.
  SCase "cs=nil".
    simpl in Hcs2sbs1. inv Hcs2sbs1.
    simpl in HtransSBs. inv HtransSBs. simpl_env.
    inv Hsubblocks. 
    SSCase "1".
      assert (HtransCmds:=HeqR4).
      eapply trans_nbranchs__is__correct with (als:=als2) in HeqR4; eauto.
      destruct HeqR4 as [lc2' [Mem2' [mi' [J1 [J2 [J3 [J4 J5]]]]]]].
      eapply trans_terminator__is__correct in Htmn; eauto.
      destruct Htmn as [B2' [n [lc2'' [J6 [J7 [J8 [J9 J10]]]]]]].
      exists lc2''. exists Mem2'. exists mi'. exists B2'. exists als1'. exists n.
      split.
        clear - J1 J10.
        rewrite_env (nil++cs2).
        eapply dbBlock_intro; eauto.
          admit. (*als*)       
      split; auto.
      split; auto.
      split; auto.
      split; auto.
      split; auto.
      split; auto.
      split; auto.   
        admit. (*als*)

    SSCase "2".
       admit. (* everything should be nil *)
    SSCase "3".
       inversion H11.

  SCase "cs<>nil".
    assert (HtransCmds:=HeqR4).
    eapply trans_nbranchs__is__correct with (als:=als2) in HeqR4; eauto.
    destruct HeqR4 as [lc2'' [Mem2'' [mi'' [J1' [J2' [J3' [J4' J5']]]]]]].
    eapply trans_terminator__is__correct in Htmn; eauto.
    destruct Htmn as [B2' [n [lc2''' [J6' [J7' [J8' [J9' J10']]]]]]].
    exists lc2'''. exists Mem2''. exists mi''. exists B2'. exists als1'.
    exists n.
    split.
      clear - J1 J1' J10'.
      eapply dbBlock_intro; eauto.
        admit. (*als*)       
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.
      admit. (*als*)
      clear - J6 J5'. apply inject_incr_trans with (f2:=mi'); auto.
Unfocus.

Focus. Case "dbBlock_error1". admit. Unfocus.
Focus. Case "dbBlock_error2". admit. Unfocus.
Focus.
Case "dbBlocks_nil".
  intros S TD Ps gl fs F st B1 lc1 rm1 als1 Mem1 MM1 B1' lc1' als1' Mem1' MM1'
    lc2 Mem2 rm2 rm1' ex_ids tmps ex_ids' tmps' mgb optb opte optb' opte' mi
    Ps2 S2 als2 los nts fh1 lb1 fh2 lb2 n Heq1 Heq2 Hwfg Hinc0 Heq3 HtransPs 
    HtransS HtransBs HtransF Heq4 Hinc Hwfmi Hrsim Hmsim Hasim. subst.
  inv Heq2.
  eapply trans_blocks_nth_Some_inv in HtransBs; eauto.
  destruct HtransBs as [B2 [Hinc' HtransBs]].
  exists lc2. exists Mem2. exists mi. exists B2. exists B2. exists als2. 
  exists n.
  repeat (split; auto).
Unfocus.

Focus.
Case "dbBlocks_cons".
  intros S TD Ps gl fs F S1 S2 S3 t1 t2 r Hblock IH1 Hblocks IH2 B1 lc1 rm1 als1
    Mem1 MM1 B1' lc1' als1' Mem1' MM1' lc2 Mem2 rm2 rm1' ex_ids tmps ex_ids' 
    tmps' mgb optb opte optb' opte' mi Ps2 S0 als2 los nts fh1 lb1 fh2 lb2 n
    Heq1 Heq2 Hwfg Hinc0 Heq3 HtransPs HtransS HtransBs HtransF Heq4 Hinc Hwfmi 
    Hrsim Hmsim Hasim. 
  inv Heq1.
  assert (J:=HtransBs).
  eapply trans_blocks_nth_Some_inv in J; eauto.
  destruct J as [B2 [Hinc' HtransB]].
  destruct S2 as [[B1'' lc1'' rm1'' als''] Mem1'' MM1''].
  assert (J:=HtransB).
  eapply IH1 in J; eauto. clear IH1.
  destruct J as [lc2' [Mem2' [mi' [B2' [als2' [n' [J1 [J2 [J3 [J4 [J5 [J6 
    [J7 [J8 J9]]]]]]]]]]]]]].
  assert (alloca_simulation mi' als'' als2') as W.
    admit.
  eapply IH2 with (als2:=als2') in HtransBs; eauto. clear IH2.
  destruct HtransBs as [lc2'' [Mem2'' [mi'' [B2''' [B2'' [als2'' [n'' [J1' [J2' 
    [J3' [J4' [J5' [J6' [J7' [J8' [J9' [J10' J11']]]]]]]]]]]]]]]]].
  exists lc2''. exists Mem2''. exists mi''. exists B2. exists B2''.
  exists als2''. exists n''.
  split.
    clear - J1 J3 J1' J2'.
    rewrite J3 in J2'. inv J2'.
    eauto.
  repeat (split; auto).
    admit. (*als*)
    clear - J9 J11'. apply inject_incr_trans with (f2:=mi'); auto.
Unfocus.

Focus. Case "dbBlocks_cons_error". admit. Unfocus.
Focus. Case "dbFdef_func". admit. Unfocus.
Focus. Case "dbFdef_func_error1". admit. Unfocus.
Focus. Case "dbFdef_func_error2". admit. Unfocus.
Focus. Case "dbFdef_func_error3". admit. Unfocus.
Focus. Case "dbFdef_func_error4". admit. Unfocus.
Focus. Case "dbFdef_func_error5". admit. Unfocus.
Focus. Case "dbFdef_proc". admit. Unfocus.
Focus. Case "dbFdef_proc_error1". admit. Unfocus.
Focus. Case "dbFdef_proc_error2". admit. Unfocus.
Focus. Case "dbFdef_proc_error3". admit. Unfocus.
Focus. Case "dbFdef_proc_error4". admit. Unfocus.
Focus. Case "dbFdef_proc_error5". admit. Unfocus.

Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)

