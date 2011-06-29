Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import ssa_def.
Require Import ssa_lib.
Require Import ssa_dynamic.
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
Require Import sb_ds_def.
Require Import sb_ds_trans.
Require Import sb_ds_metadata.
Require Import ssa_static.
Require Import ssa_props.
Require Import ssa_wf.
Import SB_ds_pass.
Require Import sb_ds_sim.
Require Import sb_ds_trans_axioms.

Ltac zauto := auto with zarith.
Ltac zeauto := eauto with zarith.




(***************************)

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

Lemma reg_simulation__updateAddAL_lc : forall mi TD gl f1 rm1 rm2 lc1 lc2 i0 gv 
    gv',
  reg_simulation mi TD gl f1 rm1 rm2 lc1 lc2 ->
  In i0 (getFdefLocs f1) ->
  i0 `notin` codom rm2 ->
  gv_inject mi gv gv' ->
  reg_simulation mi TD gl f1 rm1 rm2 (updateAddAL GenericValue lc1 i0 gv)
    (updateAddAL GenericValue lc2 i0 gv').
Proof.
  intros mi TD gl f1 rm1 rm2 lc1 lc2 i0 gv gv' Hsim Hin Hnotin. 
  destruct Hsim as [J1 J2].    
  split.
    intros i1 gv1 J.
    destruct (id_dec i0 i1); subst.
      rewrite lookupAL_updateAddAL_eq in *; auto.
      inv J. exists gv'. auto.
    
      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.

    intros vp bgv1 egv1 J.
    apply J2 in J. 
    destruct J as [bv2 [ev2 [bgv2 [egv2 [J11 [J12 [J13 [J14 J15]]]]]]]].
    exists bv2. exists ev2. exists bgv2. exists egv2.
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

      case_eq (get_const_metadata c).
        intros [bc ec] J.
        rewrite J in J11.
        inv J11.
        simpl in *.
        repeat (split; auto).

        intro J.  rewrite J in J11.
        inv J11. simpl in *.
        repeat (split; auto).
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
  eauto using val_list_inject_incr.
Qed.

Lemma inject_incr__preserves__reg_simulation : forall mi TD fl F rm1 rm2 lc1 lc2
    mi',
  reg_simulation mi TD fl F rm1 rm2 lc1 lc2 ->
  inject_incr mi mi' ->
  reg_simulation mi' TD fl F rm1 rm2 lc1 lc2.
Proof.
  intros mi TD fl F rm1 rm2 lc1 lc2 mi' Hrsim Hinc.
  destruct Hrsim as [J1 J2].
  split.
    intros. apply J1 in H. destruct H as [gv2 [H1 H2]].
    exists gv2. split; eauto using gv_inject_incr.

    intros. apply J2 in H. 
    destruct H as [bv2 [ev2 [bgv2 [egv2 [H1 [H2 [H3 [H4 H5]]]]]]]].
    exists bv2. exists ev2. exists bgv2. exists egv2.
    repeat (split; eauto using gv_inject_incr).
Qed.

Lemma val_list_inject_app : forall mi vs1 vs1' vs2 vs2',
  val_list_inject mi vs1 vs2 ->
  val_list_inject mi vs1' vs2' ->
  val_list_inject mi (vs1++vs1') (vs2++vs2').
Proof.
  induction vs1; destruct vs2; simpl; intros; inv H; auto.
Qed.

Lemma gv_inject_app : forall mi gv1 gv1' gv2 gv2',
  gv_inject mi gv1 gv2 ->
  gv_inject mi gv1' gv2' ->
  gv_inject mi (gv1++gv1') (gv2++gv2').
Proof.
  unfold gv_inject.
  induction gv1; destruct gv2; simpl; intros; auto.  
    destruct p. destruct (split gv2). inv H.
    destruct a. destruct (split gv1). inv H.

    destruct a. remember (split gv1) as R3. destruct R3.
    destruct p. remember (split gv2) as R4. destruct R4. 
    inv H.
    remember (split (gv1 ++ gv1')) as R1. destruct R1.
    remember (split (gv2 ++ gv2')) as R2. destruct R2.
    apply val_cons_inject; auto.
      assert (J:=@IHgv1 gv1' gv2 gv2').
      rewrite <- HeqR4 in J.
      rewrite <- HeqR1 in J.
      rewrite <- HeqR2 in J.
      eapply J; eauto.
Qed.

Definition zeroconst2GV__gv_inject_refl_prop (t:typ) := 
  forall maxb mi Mem1 Mem2 gv TD, 
  wf_sb_mi maxb mi Mem1 Mem2 ->
  zeroconst2GV TD t = Some gv ->
  gv_inject mi gv gv.
  
Definition zeroconsts2GV__gv_inject_refl_prop (lt:list_typ) := 
  forall maxb mi Mem1 Mem2 gv TD n, 
  wf_sb_mi maxb mi Mem1 Mem2 ->
  zeroconsts2GV TD lt = Some (gv,n) ->
  gv_inject mi gv gv.

Ltac tinv H := try solve [inv H].
  
Lemma gv_inject__repeatGV : forall mi gv1 gv2 n,
  gv_inject mi gv1 gv2 -> 
  gv_inject mi (repeatGV gv1 n) (repeatGV gv2 n).
Proof.
  induction n; intros.
    unfold gv_inject. simpl. auto.
    simpl. eapply gv_inject_app; eauto.
Qed.

Lemma gv_inject_uninits : forall mi n, gv_inject mi (uninits n) (uninits n).
Proof.
  unfold uninits.
  induction n.
    unfold gv_inject. simpl; auto.
    simpl. simpl_env. apply gv_inject_app; auto.
      unfold gv_inject. simpl; auto.
Qed.

Lemma zeroconst2GV__gv_inject_refl_mutrec :
  (forall t, zeroconst2GV__gv_inject_refl_prop t) *
  (forall lt, zeroconsts2GV__gv_inject_refl_prop lt).
Proof.
  apply typ_mutrec; 
    unfold zeroconst2GV__gv_inject_refl_prop, 
           zeroconsts2GV__gv_inject_refl_prop; 
    intros; simpl in *; 
    try solve [unfold gv_inject; simpl in *; eauto | 
               inversion H0 | inversion H1 | inversion H2].

  unfold gv_inject.
  inv H0. simpl. 
  apply val_cons_inject; auto.

  unfold gv_inject.
  destruct f; inv H0; simpl; apply val_cons_inject; auto.

  remember (zeroconst2GV TD t) as R.
  destruct R; tinv H1.
  destruct (getTypeStoreSize TD t); tinv H1.
  destruct (getTypeAllocSize TD t); inv H1.
  simpl. symmetry in HeqR.
  eapply H in HeqR; eauto.
  apply gv_inject__repeatGV.
  apply gv_inject_app; auto.
    apply gv_inject_uninits.

  remember (zeroconsts2GV TD l0) as R.
  destruct R as [[gv0 tsz]|]; tinv H1.
  destruct (getTypeAllocSize TD (typ_struct l0)); inv H1.
  destruct l0; inv H3.
    apply gv_inject_uninits.
    symmetry in HeqR.
    eapply H in HeqR; eauto.
    apply gv_inject_app; auto.
      apply gv_inject_uninits.
 
  inv H1. unfold gv_inject. simpl.
  apply val_cons_inject; auto.
    inv H0. 
    eapply val_inject_ptr; eauto.

  inv H0. unfold gv_inject. simpl. auto.


  remember (zeroconsts2GV TD l0) as R.
  destruct R as [[gv1 tsz]|]; tinv H2.
  remember (zeroconst2GV TD t) as R1.
  destruct R1 as [gv2|]; tinv H2.
  destruct (getTypeStoreSize TD t); inv H2.
  destruct (getTypeAllocSize TD t); inv H4.
  symmetry in HeqR.
  eapply H0 in HeqR; eauto.
  symmetry in HeqR1.
  eapply H in HeqR1; eauto.
  apply gv_inject_app; auto.
  apply gv_inject_app; auto.
    apply gv_inject_uninits.
Qed.

Lemma zeroconst2GV__gv_inject_refl : forall maxb mi Mem1 Mem2 gv TD t, 
  wf_sb_mi maxb mi Mem1 Mem2 ->
  zeroconst2GV TD t = Some gv ->
  gv_inject mi gv gv.
Proof.
  intros.  
  destruct zeroconst2GV__gv_inject_refl_mutrec as [J _].
  unfold zeroconst2GV__gv_inject_refl_prop in J.
  eauto.
Qed. 

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
      destruct v; simpl in *; try solve 
        [assert (J:=@IHgv H H0); eauto].

        destruct H0 as [H1 H2].
        assert (J:=(@IHgv H H2)).
        inversion H.
        apply mi_globals in H1.
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
    
Lemma gv_inject_nil_inv : forall mi gv2,
  gv_inject mi nil gv2 -> gv2 = nil.
Proof.
  intros.   
  destruct gv2; eauto.
  unfold gv_inject in H. simpl in H. destruct p. destruct (split gv2). inv H.
Qed.    

Lemma gv_inject_nil_inv' : forall mi gv1,
  gv_inject mi gv1 nil -> gv1 = nil.
Proof.
  intros.   
  destruct gv1; eauto.
  unfold gv_inject in H. simpl in H. destruct p. destruct (split gv1). inv H.
Qed.    

Lemma gv_inject_cons_inv : forall mi g1 gv1 gv2,
  gv_inject mi (g1::gv1) gv2 -> 
  exists gv2', exists v1, exists m1, exists v2, exists m2, 
    gv2 = (v2,m2)::gv2' /\ gv_inject mi gv1 gv2' /\ val_inject mi v1 v2 /\
    g1 = (v1,m1).
Proof.
  intros.   
  destruct gv2; eauto.
    apply gv_inject_nil_inv' in H. inv H.
    unfold gv_inject in H. simpl in H. destruct g1. 
    remember (split gv1) as R1.  destruct R1. destruct p.
    remember (split gv2) as R2.  destruct R2. 
    inv H. exists gv2. exists v. exists m. exists v0. exists m0.
    unfold gv_inject. rewrite <- HeqR1. rewrite <- HeqR2.
    split; auto.
Qed.    

Lemma gv_inject__val_inject : forall mi gv1 gv2 TD,
  gv_inject mi gv1 gv2 ->
  exists v1, exists v2,
    GV2val TD gv1 = Some v1 /\ GV2val TD gv2 = Some v2 /\ val_inject mi v1 v2.
Proof.
  intros.
  unfold GV2val in *.
  destruct gv1.
    apply gv_inject_nil_inv in H. subst. eauto.

    apply gv_inject_cons_inv in H.
    destruct H as [gv2' [v1' [m1 [v2 [m2 [J1 [J2 [J3 J4]]]]]]]]; subst.
    destruct gv1.
      apply gv_inject_nil_inv in J2. subst. eauto.
  
      apply gv_inject_cons_inv in J2.
      destruct J2 as [gv3 [v2' [m2' [v3 [m3 [J1 [J2 [J5 J4]]]]]]]]; subst.
      eauto.
Qed.

Lemma gv_inject_gundef : forall mi, gv_inject mi gundef gundef.
Proof.
  intros. unfold gundef. apply gv_inject_uninits.
Qed.

(*
Lemma simulation__mtrunc : forall mi TD top t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mtrunc TD top t1 gv1 t2 = Some gv2 ->
  mtrunc TD top t1 gv1 t2 = mtrunc TD top t1 gv1' t2 \/
  exists gv2',
    mtrunc TD top t1 gv1' t2 = Some gv2' /\
    gv_inject mi gv2 gv2'.  
Proof.
  intros.
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v2 [J1 [J2 J3]]]].
  unfold mtrunc.
  rewrite J1. rewrite J2.
  inv J3; auto.
    right. 
    unfold mtrunc in H0. rewrite J1 in H0.
    inv H0.
    destruct v2; try solve [exists gundef; auto using gv_inject_gundef].
    destruct t1; try solve [exists gundef; auto using gv_inject_gundef].
    destruct t2; try solve [exists gundef; auto using gv_inject_gundef].
     
Admitted.
*)

Lemma simulation__mtrunc : forall mi TD top t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mtrunc TD top t1 gv1 t2 = Some gv2 ->
  exists gv2',
    mtrunc TD top t1 gv1' t2 = Some gv2' /\
    gv_inject mi gv2 gv2'.
Proof.
  intros.
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v2 [J1 [J2 J3]]]].
  unfold mtrunc in *.
  rewrite J1 in H0. rewrite J2.
  unfold gv_inject.
  inv J3; simpl; eauto.
    destruct t1; simpl; eauto.
      destruct t2; inv H0; simpl; eauto.

  intros.
 
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
  mcast TD op t1 gv1 t2 = Some gv2 ->
  exists gv2',
    mcast TD op t1 gv1' t2 = Some gv2' /\
    gv_inject mi gv2 gv2'.
Admitted.

Lemma simulation__micmp : forall mi TD Mem1 Mem2 c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  Mem.mem_inj mi Mem1 Mem2 ->  
  micmp TD c t gv1 gv2 = Some gv3 ->
  exists gv3',
    micmp TD c t gv1' gv2' = Some gv3' /\
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

(*
Definition sb_mem_inj__const2GV_prop (c:const) := forall maxb mi Mem1 Mem2 TD gl 
    gv t,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_globals maxb gl -> 
  _const2GV TD gl c = Some (gv,t) ->
  exists gv',
    _const2GV TD gl c = Some (gv',t) /\
    gv_inject mi gv gv'.

Definition sb_mem_inj__list_const2GV_prop (lc:list_const) := 
  forall maxb mi Mem1 Mem2 TD gl,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_globals maxb gl -> 
  (forall gv, 
    _list_const_arr2GV TD gl lc = Some gv ->
    exists gv',
      _list_const_arr2GV TD gl lc = Some gv' /\
      gv_inject mi gv gv'
  ) /\
  (forall gv t a, 
    _list_const_struct2GV TD gl lc = Some (gv,t,a) ->
    exists gv',
      _list_const_struct2GV TD gl lc = Some (gv',t,a) /\
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
  destruct R; inv H1.
  exists gv. split; eauto using zeroconst2GV__gv_inject_refl.
Case "int".
  inv H1.
  exists (val2GV TD
            (Vint (Size.to_nat s - 1)
               (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z i0)))
            (AST.Mint (Size.to_nat s - 1))).
  split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].
Case "float".
  destruct f; inv H1.
    exists (val2GV TD (Vfloat f0) AST.Mfloat32).
    split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].

    exists (val2GV TD (Vfloat f0) AST.Mfloat64).
    split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].
Case "undef".
  remember (getTypeSizeInBits TD t) as R.
  destruct R; inv H1.
  exists (val2GV TD Vundef (AST.Mint (n - 1))).
  split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].
Case "null".
  inv H1.
  exists (val2GV TD (Vptr Mem.nullptr (Int.repr 31 0)) (AST.Mint 31)).
  split; auto. 
    unfold val2GV, gv_inject; simpl.
    split; auto.
      apply val_cons_inject; auto.
      apply val_inject_ptr with (delta:=0); auto.
      destruct H. auto.
Case "arr". 
  eapply H with (TD:=TD)(gl:=gl) in H1; eauto.
  destruct H1; eauto.
  remember (_list_const_arr2GV TD gl l0) as R.
  destruct R; inv H2.
  destruct (@H1 gv) as [gv' [J1 J2]]; auto.
  exists gv'. inv J1. auto.

Case "struct". 
  eapply H with (TD:=TD)(gl:=gl) in H1; eauto.
  destruct H1 as [H00 H01].
  remember (_list_const_struct2GV TD gl l0) as R.
  destruct R as [[[gv1 t1] a1]|]; inv H2.
  destruct (@H01 gv1 t1 a1) as [gv' [H02 H03]]; auto.
  inv H02.
  destruct (getTypeAllocSize TD (typ_struct t1)); try solve [inv H3].
  destruct l0; inv H3.
    exists (uninits s).
    split; auto. 
      apply gv_inject_uninits.

    exists (gv' ++ uninits (a1 - s)).
    split; auto.
      apply gv_inject_app; auto.
        apply gv_inject_uninits.

Case "gid".
  remember (lookupAL GenericValue gl i0) as R.
  destruct R; inv H1.
  exists gv. split; eauto using global_gv_inject_refl.
Case "trunc".
  remember (_const2GV TD gl c) as R.
  destruct R as [[gv1 t1']|]; try solve [inv H2].
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  remember (mtrunc TD t t1' gv1 t0) as R1.
  destruct R1; inv H2.
  symmetry in HeqR1.
  eapply simulation__mtrunc in HeqR1; eauto.
  destruct HeqR1 as [gv2' [J3 J4]].
  exists gv. split; auto.
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
*)

Lemma sb_mem_inj__const2GV : forall maxb mi Mem Mem' TD gl c gv,
  wf_sb_mi maxb mi Mem Mem' ->
  wf_globals maxb gl -> 
  const2GV TD gl c = Some gv ->
  gv_inject mi gv gv.
Admitted.

Lemma simulation__getOperandValue : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 
    gl F v gv,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  getOperandValue TD v lc gl = ret gv ->
  exists gv', 
    getOperandValue TD v lc2 gl = ret gv' /\
    gv_inject mi gv gv'.
Proof.
  intros maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F v gv Hwfg H0 H1 H2.
  unfold getOperandValue in *.
  destruct H1 as [H1 _].
  destruct v.
    apply H1 in H2. auto.

    exists gv. split; auto. eapply sb_mem_inj__const2GV; eauto.
Qed.

Lemma simulation__BOP : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F bop0 sz0 
    v1 v2 gv3,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  BOP TD lc gl bop0 sz0 v1 v2 = ret gv3 ->
  exists gv3',
    BOP TD lc2 gl bop0 sz0 v1 v2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F bop0 sz0 v1 v2 gv3 Hwfg H0 
    H1 H3.
  unfold BOP in *.
  remember (getOperandValue TD v1 lc gl) as R1.
  destruct R1; inv H3.
  remember (getOperandValue TD v2 lc gl) as R2.
  destruct R2; inv H2.
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

Lemma const2GV_lt_nextblock_aux : forall TD mgb gl c g t b ofs,
  wf_globals mgb gl ->
  0 <= mgb ->
  _const2GV TD gl c = Some (g, t) -> 
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

Lemma trans_cmds_inv : forall ex_ids1 rm2 c cs ex_ids2 cs',
  trans_cmds ex_ids1 rm2 (c :: cs) = ret (ex_ids2, cs') ->
  exists ex_ids3, exists cs1', exists cs2',
  trans_cmd ex_ids1 rm2 c = ret (ex_ids3, cs1') /\
  trans_cmds ex_ids3 rm2 cs = ret (ex_ids2, cs2') /\  
  cs1' ++ cs2' = cs'.
Proof.
  intros. simpl in H.
  destruct (trans_cmd ex_ids1 rm2 c) as [[ex_ids3 cs1]|]; 
    try solve [inversion H].
  remember (trans_cmds ex_ids3 rm2 cs) as R.
  destruct R as [[ex_ids4 cs2]|]; inv H.
  exists ex_ids3. exists cs1. exists cs2. eauto.
Qed.


Lemma gv_inject_ptr_inv : forall mi b ofs gv' cm,
  gv_inject mi ((Vptr b ofs,cm)::nil) gv' ->
  exists b', exists ofs', exists cm,
    gv' = (Vptr b' ofs', cm)::nil /\
    val_inject mi (Vptr b ofs) (Vptr b' ofs').
Proof.
  intros mi b ofs gv' cm J .
  unfold gv_inject in J.
  simpl in J.
  destruct gv'; simpl in J.
    inv J.

    destruct p; simpl in J. 
    destruct gv'; simpl in J.    
      inv J. 
      inv H2. exists b2. exists (Int.add 31 ofs (Int.repr 31 delta)). exists m.
      split; eauto.

      destruct p. destruct (split gv'). 
      inv J. inv H4.
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
  destruct Hmsim as [H1 [Hmgb [Hzeroout H2]]].
  unfold malloc in *.
  remember (GV2int TD Size.ThirtyTwo gn) as R.
  destruct R; try solve [inversion Halloc].
  remember (Mem.alloc Mem 0 (Size.to_Z tsz * z)) as R1.
  destruct R1 as [Mem1 mb1].
  destruct (zle 0 (Size.to_Z tsz * z)); inv Halloc.
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
      destruct Hwfmi as [_ _ Hmap1 _].
      assert (mi (Mem.nextblock Mem) = None) as J.
        apply Hmap1; auto with zarith.
      rewrite H in J. inversion J.

  split; auto.
  Case "wfmi".
    clear - Hwfmi Hmgb HeqR2 HeqR1.
    destruct Hwfmi as [Hno_overlap Hnull Hmap1 Hmap2 mi_freeblocks 
      mi_mappedblocks mi_range_block mi_bounds mi_globals].
    symmetry in HeqR2, HeqR1. 
    assert (J:=HeqR2).
    apply Mem.nextblock_alloc in HeqR2.
    split.
    SCase "no_overlap".
      clear - Hno_overlap J Hmap2.
      unfold meminj_no_overlap in *.
      intros.      
      destruct (zeq b1 mb); subst.
        destruct (zeq b2 mb); subst.
          contradict H; auto.

          inv H0.
          apply Hmap2 in H1.
          apply Mem.alloc_result in J.
          subst. clear - H1. intro J. subst. contradict H1; zauto.
        destruct (zeq b2 mb); subst; eauto.
          inv H1.
          apply Hmap2 in H0.
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

        apply mi_freeblocks.
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
          apply Hmap2 in J'.
          apply Mem.alloc_result in J.
          rewrite J in J'. contradict J'; zauto.
    SCase "globals".
      intros b J'.
      destruct (zeq b mb); subst; eauto.
        assert (J'':=J').
        apply mi_globals in J'.
        destruct (valid_block_dec Mem mb).
          apply Mem.fresh_block_alloc in HeqR1.
          contradict HeqR1; auto.
     
          apply mi_freeblocks in n.        
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
            apply Hmap2 in H0.
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

    split.
    SCase "zeroout".
      clear - Hzeroout HeqR1.
      symmetry in HeqR1.
      apply Mem.nextblock_alloc in HeqR1. intros.
      rewrite HeqR1 in H. 
      apply Hzeroout; auto with zarith.

    SCase "msim2".
      clear H1.
      intros lc2 gl b ofs bgv egv als bid0 eid0 pgv' fs F B cs tmn S Ps EC v cm 
        Hwfg J1 J2 J3.
        apply gv_inject_ptr_inv in J2.
        destruct J2 as [b' [ofs' [cm' [J5 J6]]]].
        inv J6.
        destruct (zeq b mb); subst; inv H3.
          clear H2.
          exists null. exists null.
          unfold get_mem_metadata, ptr2GV, val2GV, GV2ptr in J1.
          assert (mb >= Mem.nextblock Mem) as GE.
            symmetry in HeqR1.
            apply Mem.alloc_result in HeqR1.
            subst. omega.
          rewrite Hzeroout in J1; auto. inv J1.
          assert (gv_inject (fun b : Z => if zeq b mb then ret (b', 0) else mi b)
            null null) as Hinject_null.
            unfold gv_inject. simpl.
              apply val_cons_inject; auto.
                inv Hwfmi.
                apply val_inject_ptr with (delta:=0).
                  destruct (zeq Mem.nullptr mb); subst; auto.
                    symmetry in HeqR1.
                    apply Mem.alloc_result in HeqR1.
                    assert(J':=@Mem.nextblock_pos Mem).
                    rewrite <- HeqR1 in J'.
                    unfold Mem.nullptr in J'.
                    contradict J'; zauto.
                  rewrite Int.add_zero; auto.
          split; auto.
            eapply get_mmetadata_fn__alloc__zeroout; 
              unfold ptr2GV, val2GV; eauto.

          assert (gv_inject mi ((Vptr b ofs,cm')::nil) 
            ((Vptr b' (Int.add 31 ofs (Int.repr 31 delta)),cm') :: nil)) as W.
            clear - Hwfg J3 HeqR2 Hmgb n H0.
            unfold ptr2GV, val2GV. unfold gv_inject. simpl.
              apply val_cons_inject; auto.
              apply val_inject_ptr with (delta:=delta); auto.
            
          assert (get_mem_metadata TD MM ((Vptr b ofs, cm') :: nil) =
            {| md_base := bgv; md_bound := egv |}) as J1'.
            clear - J1. unfold get_mem_metadata in *. simpl in *. auto.

          eapply H2 with (lc2:=lc2)(gl:=gl)(als:=als)(bid0:=bid0)(eid0:=eid0)
            (v:=v)(fs:=fs)(F:=F)(B:=B)(cs:=cs)(tmn:=tmn)(S:=S)
            (Ps:=Ps)(EC:=EC)in J1'; eauto.
          destruct J1' as [bgv' [egv' [J37 [J33 J34]]]].
          clear H2.
          exists bgv'. exists egv'. 
          split.
            eapply get_mmetadata_fn__alloc__preserve; eauto.
            split; eauto using gv_inject_incr.

  split; auto.
  split.
    destruct (zeq mb mb); auto.
      contradict n; auto.
    intros.
    destruct (zeq b mb); subst; auto.
      contradict H; auto.
Qed.

Ltac invert_prop_reg_metadata :=
  match goal with
  | [H : SBopsem.prop_reg_metadata _ _ _ _ _ = (_, _) |- _ ] =>
      inv H; subst; eauto
  end.

Lemma reg_simulation__updateAddAL_md : forall mi TD gl f1 rm1 rm2 lc1 lc2 id0 
    bgv1 bgv2 egv1 egv2 bid eid c ex_ids3 mgb M1 M2
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl),
  reg_simulation mi TD gl f1 rm1 rm2 lc1 lc2 ->
  wf_fresh ex_ids3 c rm2 ->
  getCmdID c = Some id0 ->
  ret (bid, eid) = lookupAL (id * id) rm2 id0 ->
  gv_inject mi bgv1 bgv2 ->
  gv_inject mi egv1 egv2 ->
  reg_simulation mi TD gl f1 
    (updateAddAL _ rm1 id0 (mkMD bgv1 egv1)) rm2 lc1
    (updateAddAL _ (updateAddAL _ lc2 bid bgv2) eid egv2).
Proof.
  intros mi TD gl f1 rm1 rm2 lc1 lc2 id0 bgv1 bgv2 egv1 egv2 bid eid c ex_ids3
    mgb M1 M2 Hwfmi Hwfg Hrsim Hnotin Hid HeqR1 Hbinj Heinj.
  split.
  SSCase "rsim1".
      intros i0 gv1 J.
      destruct Hrsim as [J1 _].
      apply J1 in J.
      destruct J as [gv2 [J J2]].
      exists gv2.
        split; auto.
          admit. (* i0 <> bid eid tmp, need to fix simulation relation for 
                    freshness *)
  SSCase "rsim2".
      intros vp bgv0 egv0 J.
      unfold SBopsem.get_reg_metadata in J.
      destruct vp as [pid | ]; simpl.
      SSSCase "vp = pid".
        destruct (id_dec id0 pid); subst.
        SSSSCase "id0 = pid".
          rewrite <- HeqR1.
          rewrite lookupAL_updateAddAL_eq in J.
          inv J.
          exists (value_id bid). exists (value_id eid).
          exists bgv2. exists egv2.
          split; auto.
          split.
            clear - Hnotin HeqR1.
            destruct Hnotin as [Hnotin1 [Hnotin2 [Hnotin3 Hnotin4]]]. 
            unfold getCmdIDs in *.
            simpl in *.
            simpl.
            rewrite <- lookupAL_updateAddAL_neq.
              rewrite lookupAL_updateAddAL_eq; auto.
              eapply rm_codom_disjoint_spec in HeqR1; eauto.

          split. simpl. rewrite lookupAL_updateAddAL_eq; auto.
          split; auto.

        SSSSCase "id0 <> pid".
          rewrite <- lookupAL_updateAddAL_neq in J; auto.
          destruct Hrsim as [_ Hrsim].
          destruct (@Hrsim (value_id pid) bgv0 egv0) as 
            [bv2 [ev2 [bgv2' [egv2' [J1 [J2 [J3 [J4 J5]]]]]]]]; auto.
          exists bv2. exists ev2. exists bgv2'. exists egv2'.
          simpl in J1.
          split; auto.
          remember (lookupAL (id * id) rm2 pid) as R.
          destruct R; inv J1. destruct p; inv H0.
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

      SSSCase "vp = c".
        remember (get_const_metadata c0) as R.
        destruct R as [[c1 c2]|].
          remember (const2GV TD gl c1) as R1.
          destruct R1; try solve [inversion J]. simpl in J.
          remember (const2GV TD gl c2) as R2.
          destruct R2; try solve [inversion J]. simpl in J.
          inv J.
          exists (value_const c1). exists (value_const c2). simpl.
          exists bgv0. exists egv0. 
          repeat (split; eauto using sb_mem_inj__const2GV).

          inv J.
          exists vnullp8. exists vnullp8. exists null. exists null.
          simpl. unfold gv_inject. unfold const2GV. simpl. unfold null. 
          unfold val2GV.
          inv Hwfmi.
          repeat (split; eauto).
Qed.


Lemma reg_simulation__updateAddAL_tmp : forall mi TD gl f1 rm1 rm2 lc1 lc2 tmp
   tgv c ex_ids3 ex_ids5 mgb M1 M2
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl),
  reg_simulation mi TD gl f1 rm1 rm2 lc1 lc2 ->
  wf_fresh ex_ids3 c rm2 ->
  (tmp, ex_ids5) = mk_tmp ex_ids3 ->
  reg_simulation mi TD gl f1 rm1 rm2 lc1 (updateAddAL _ lc2 tmp tgv).
Proof.
  intros mi TD gl f1 rm1 rm2 lc1 lc2 tmp tgv c ex_ids3 ex_ids5 mgb M1 M2 Hwfmi 
    Hwfg Hrsim Hnotin HeqR2.
    split.
    SSCase "rsim1".
      intros i0 gv1 J.
      destruct Hrsim as [J1 _].
      apply J1 in J.
      destruct J as [gv2 [J J2]].
      exists gv2.
      split; auto.
        admit. (* i0 <> bid eid tmp, need to fix simulation relation for 
                    freshness *)
 
    SSCase "rsim2".
      intros vp bgv1 egv1 J.
      unfold SBopsem.get_reg_metadata in J.
      destruct vp as [pid | ]; simpl.
      SSSCase "vp = pid".
          destruct Hrsim as [_ Hrsim].
          destruct (@Hrsim (value_id pid) bgv1 egv1) as 
            [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]; auto.
          exists bv2. exists ev2. exists bgv2. exists egv2.
          simpl in J1.
          split; auto.
          remember (lookupAL (id * id) rm2 pid) as R.
          destruct R; inv J1. destruct p; inv H0.
          destruct Hnotin as [Hnotin1 [Hnotin2 [Hnotin3 Hnotin4]]]. 
          simpl.
          rewrite <- lookupAL_updateAddAL_neq; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
            eapply tmp_is_fresh' with (tmp:=tmp) in HeqR; eauto. 
              clear - Hnotin3. fsetdec.
            eapply tmp_is_fresh' with (tmp:=tmp) in HeqR; eauto. 
              clear - Hnotin3. fsetdec.

      SSSCase "vp = c".
        remember (get_const_metadata c0) as R.
        destruct R as [[c1 c2]|].
          remember (const2GV TD gl c1) as R1.
          destruct R1; try solve [inversion J]. simpl in J.
          remember (const2GV TD gl c2) as R2.
          destruct R2; try solve [inversion J]. simpl in J.
          inv J.
          exists (value_const c1). exists (value_const c2). simpl.
          exists bgv1. exists egv1. 
          repeat (split; eauto using sb_mem_inj__const2GV).

          inv J.
          exists vnullp8. exists vnullp8. exists null. exists null.
          simpl. unfold gv_inject. unfold const2GV. simpl. unfold null. 
          unfold val2GV.
          inv Hwfmi.
          repeat (split; eauto).
Qed.

Lemma mem_simulation__free : forall mi TD MM Mem0 M2 Mem' mgb hi lo
  (b2 : Values.block) (delta : Z) blk,
  wf_sb_mi mgb mi Mem0 M2 ->
  mem_simulation mi TD mgb MM Mem0 M2 ->
  Mem.free Mem0 blk lo hi = ret Mem' ->
  (lo, hi) = Mem.bounds Mem0 blk ->
  mi blk = ret (b2, delta) ->
  exists Mem2',
    Mem.free M2 b2 (lo+delta) (hi+delta) = ret Mem2' /\
    wf_sb_mi mgb mi Mem' Mem2' /\
    mem_simulation mi TD mgb MM Mem' Mem2'.
Proof.
  intros mi TD MM Mem0 M2 Mem' mgb hi lo b2 delta blk Hwfmi HsimM H0
    HeqR2 H4.

  destruct HsimM as [Hmsim1 [Hmgb [Hzeroout Hmsim2]]].  
  assert ({ Mem2':Mem.mem | Mem.free M2 b2 (lo+delta) (hi+delta) = ret Mem2'}) 
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
  exists Mem2'. split; auto.
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
      intros. apply mi_bounds in H. 
      erewrite Mem.bounds_free; eauto.
      erewrite Mem.bounds_free with (m2:=Mem2'); eauto.

  SCase "msim".
    split.
      clear - Hmsim1 Hwfmi H0 J H4.
      assert (J':=Hmsim1).
      eapply Mem.free_left_inj in J'; eauto.
      eapply Mem.free_right_inj in J'; eauto.
      intros b1 delta0 ofs p H1 H2 H3.
      destruct (Values.eq_block blk b1); subst.
        rewrite H1 in H4. inv H4.
        apply Mem.perm_free_2 with (p:=p)(ofs:=ofs) in H0; eauto with zarith.

        destruct Hwfmi.
        unfold meminj_no_overlap in Hno_overlap.
        apply Hno_overlap with (b1':=b2)(b2':=b2)(delta1:=delta)(delta2:=delta0)
          in n; auto.

    split.
      clear - Hmgb J.
      apply Mem.nextblock_free in J.
      rewrite J. auto.
  
    split.
      clear - Hzeroout H0. intros.
      apply Mem.nextblock_free in H0.
      apply Hzeroout.
      rewrite <- H0. auto.

      clear Hmsim1 Hmgb.
      intros lc0 gl0 b0 ofs bgv egv als0 bid0 eid0 pgv' fs F B0 cs0 tmn S0 Ps0
        EC0 v1 cm Hwfg0 G1 G2 G3.
      assert (G3':=G3).
      eapply Hmsim2 with (bgv:=bgv)(egv:=egv)(als:=als0)
        (bid0:=bid0)(eid0:=eid0)(b:=b0)(ofs:=ofs) in G3'; eauto.
      destruct G3' as [bgv' [egv' [G4 [G5 G6]]]].
      exists bgv'. exists egv'.
      split; auto.
        eapply free_doesnt_change_gmmd; eauto.
Qed.

Lemma free_allocas_sim : forall TD mi mgb als1 M1 als2 M2 M1' MM,
  free_allocas TD M1 als1 = Some M1' ->
  mem_simulation mi TD mgb MM M1 M2 ->
  wf_sb_mi mgb mi M1 M2 ->
  als_simulation mi als1 als2 ->
  exists M2', free_allocas TD M2 als2 = Some M2' /\ 
    mem_simulation mi TD mgb MM M1' M2' /\
    wf_sb_mi mgb mi M1' M2'.
Proof.
  induction als1; simpl; intros.
    destruct als2; simpl; inv H2.
      inv H. eauto.

    destruct als2; simpl; inv H2.
    remember (free TD M1 (blk2GV TD a)) as R.
    destruct R as [Mem'|]; try solve [inv H].
    symmetry in HeqR.
    apply free_inv in HeqR.
    destruct HeqR as [blk [ofs [hi [lo [J1 [J2 [J3 J4]]]]]]].
    unfold blk2GV, free, GV2ptr, ptr2GV, val2GV in J1.
    inv J1.   
    eapply mem_simulation__free with (b2:=m)(delta:=0) in J4; eauto.
    destruct J4 as [Mem2' [J4 [J5 J6]]].
    unfold blk2GV, free, GV2ptr, ptr2GV, val2GV.
    simpl. 
    inv H1.
    erewrite <- mi_bounds; eauto.
    rewrite <- J3. 
    assert (lo+0=lo) as Eq1. zauto.
    assert (hi+0=hi) as Eq2. zauto. 
    rewrite <- Eq1. rewrite <- Eq2.
    rewrite J4. eauto.
Qed.

Lemma simulation__eq__GV2int : forall mi gn gn' TD,
  gv_inject mi gn gn' ->
  GV2int TD Size.ThirtyTwo gn = GV2int TD Size.ThirtyTwo gn'.
Admitted.

Lemma getOperandValue_eq_fresh_id : forall tmp TD v lc2 gl gvp2,
  id_fresh_in_value v tmp ->
  getOperandValue TD v lc2 gl = 
    getOperandValue TD v (updateAddAL GenericValue lc2 tmp gvp2) gl.
Proof.
  intros.
  destruct v; simpl; auto.
    rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma inject_incr__preserves__als_simulation : forall mi mi' als1 als2,
  als_simulation mi als1 als2 ->
  inject_incr mi mi' ->
  als_simulation mi' als1 als2.
Proof.
  induction als1; destruct als2; simpl; intros; auto.
    destruct H.
    split; eauto.
Qed.

Lemma inject_incr__preserves__sbEC_simulate_EC_tail : forall mi mi' TD gl Ps
    EC1 EC2,
  inject_incr mi mi' ->
  sbEC_simulates_EC_tail TD Ps gl mi EC1 EC2 ->
  sbEC_simulates_EC_tail TD Ps gl mi' EC1 EC2.
Proof.
  intros.
  destruct EC1. destruct EC2.
  destruct TD as [los nts]. destruct CurFunction0. destruct CurFunction1.
  destruct CurCmds0; try solve [inv H0].
  destruct c; try solve [inv H0].
  destruct H0 as [J0 [J1 [J2 [Htfdef [Heq0 [Hasim [Hnth [Heqb1 [Heqb2 [ex_ids 
    [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [cs24 [Hgenmeta [Hrsim [Hinc [Hcall 
    [Hfresh [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]]]]; subst.
  eapply inject_incr__preserves__als_simulation in Hasim; eauto.
  eapply inject_incr__preserves__reg_simulation in Hrsim; eauto.
  repeat (split; auto).
  exists ex_ids. exists rm2. exists ex_ids3. exists ex_ids4. exists cs22.
  exists cs23. exists cs24.
  repeat (split; auto).
Qed.

Lemma inject_incr__preserves__sbECs_simulate_ECs_tail : forall mi mi' TD gl Ps
    ECs1 ECs2,
  inject_incr mi mi' ->
  sbECs_simulate_ECs_tail TD Ps gl mi ECs1 ECs2 ->
  sbECs_simulate_ECs_tail TD Ps gl mi' ECs1 ECs2.
Proof.
  induction ECs1; destruct ECs2; simpl; intros; auto.
    destruct H0.
    split; eauto using inject_incr__preserves__sbEC_simulate_EC_tail.
Qed.

Lemma cmds_at_block_tail_next : forall B c cs tmn2,
  (exists l1, exists ps1, exists cs11, B = 
    block_intro l1 ps1 (cs11 ++ c :: cs) tmn2) ->
  exists l1, exists ps1, exists cs11, B = block_intro l1 ps1 (cs11 ++ cs) tmn2.
Proof.
  intros.
  destruct H as [l1 [ps1 [cs11 H]]]; subst.
  exists l1. exists ps1. exists (cs11 ++ [c]). simpl_env. auto.
Qed.

Lemma reg_simulation__updateAddAL_prop : forall mi TD gl f1 rm1 rm2 lc1 lc2  
    bgv1 bgv2 egv1 egv2 bid eid c ex_ids3 mgb M1 M2 id0 gv1 gv2
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl),
  reg_simulation mi TD gl f1 rm1 rm2 lc1 lc2 ->
  wf_fresh ex_ids3 c rm2 ->
  getCmdID c = Some id0 ->
  ret (bid, eid) = lookupAL (id * id) rm2 id0 ->
  In id0 (getFdefLocs f1) ->
  id0 `notin` codom rm2 ->
  gv_inject mi gv1 gv2 ->
  gv_inject mi bgv1 bgv2 ->
  gv_inject mi egv1 egv2 ->
  reg_simulation mi TD gl f1 
    (updateAddAL _ rm1 id0 (mkMD bgv1 egv1)) rm2 
    (updateAddAL GenericValue lc1 id0 gv1)
    (updateAddAL _ (updateAddAL _ 
      (updateAddAL GenericValue lc2 id0 gv2) bid bgv2) eid egv2).
Proof.
  intros.
  eapply reg_simulation__updateAddAL_md; eauto.
  eapply reg_simulation__updateAddAL_lc; eauto.
Qed.


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
  inversion Hginject; subst.
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
      apply mi_range_block in H2. subst.
      rewrite Int.add_zero.
      assert (Int.signed 31 i1 + 0 = Int.signed 31 i1) as EQ. zauto.
      rewrite EQ in J2. rewrite J2. auto.

      unfold val2GV. simpl. 
      auto.

    destruct p. simpl in HeqR3. destruct (split gvp2). inversion HeqR3.
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
  (J1 : SB_ds_pass.get_reg_metadata rm2 vp = ret (bv2, ev2)),
  id_fresh_in_value bv2 ptmp /\ id_fresh_in_value ev2 ptmp.
Proof.
  intros.
  destruct vp; simpl in *.
  remember (lookupAL (id * id) rm2 i0) as R.
  destruct R; inv J1.
  destruct p; inv H0; simpl.
  destruct Hnotin as [_ [_ [Hnotin _ ]]].
  eapply tmp_is_fresh' with (tmp:=ptmp) in HeqR; eauto. fsetdec.
  
  destruct (SBopsem.get_const_metadata c0) as [[bc ec]|].
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
  (J11 : get_reg_metadata rm2 vp0 = ret (bv0, ev0)),
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
  
    destruct (SBopsem.get_const_metadata c) as [[be ec]|].
      inv J11; simpl; auto.
      destruct (Constant.getTyp c); inv J11; simpl; auto.
Qed.

Axiom store_doesnt_change_gmmd : forall M2 b2 ofs v0 Mem2' lc2 gl als
   bid0 eid0 bgv' egv' fs F B cs tmn S Ps EC TD v ck,
  Mem.store ck M2 b2 ofs v0 = ret Mem2' ->
  LLVMopsem.dsop_star 
    (LLVMopsem.mkState S TD Ps 
      ((LLVMopsem.mkEC F B 
        (insn_call bid0 false attrs gmb_typ gmb_fn 
                       ((p8,v)::
                        (p8,vnullp8)::
                        (i32,vint1)::
                        (p32,vnullp32)::
                        nil)::
         insn_call eid0 false attrs gme_typ gme_fn 
                       ((p8,v)::
                        (p8,vnullp8)::
                        (i32,vint1)::
                        (p32,vnullp32)::
                        nil)::
         cs) 
        tmn lc2 als)
        ::EC) gl fs M2)
    (LLVMopsem.mkState S TD Ps 
       ((LLVMopsem.mkEC F B cs tmn 
         (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als)::EC) 
        gl fs M2)
    trace_nil ->
  LLVMopsem.dsop_star 
    (LLVMopsem.mkState S TD Ps 
      ((LLVMopsem.mkEC F B 
        (insn_call bid0 false attrs gmb_typ gmb_fn 
                       ((p8,v)::
                        (p8,vnullp8)::
                        (i32,vint1)::
                        (p32,vnullp32)::
                        nil)::
         insn_call eid0 false attrs gme_typ gme_fn 
                       ((p8,v)::
                        (p8,vnullp8)::
                        (i32,vint1)::
                        (p32,vnullp32)::
                        nil)::
         cs) 
        tmn lc2 als)
        ::EC) gl fs Mem2')
    (LLVMopsem.mkState S TD Ps 
       ((LLVMopsem.mkEC F B cs tmn 
         (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als)::EC) 
        gl fs Mem2')
    trace_nil.

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
  inversion Hginject1; subst.
  inversion H3; subst.
  inversion H1; subst.
  destruct gvp2; try solve [inversion HeqR2].
  destruct p. simpl in HeqR2.
  remember (split gvp2) as R3.
  destruct R3; inv HeqR2.
  destruct gvp2.
    unfold GV2val in *.

    assert (exists v2, GV2val TD gv2 = Some v2 /\ val_inject mi v v2) as Hvinj.
      clear - HeqR1 Hginject2.
      unfold GV2val.
      destruct gv; simpl in *; inv HeqR1.
        destruct gv2. exists Vundef. split; auto.
          destruct p; simpl in *. 
          destruct (split gv2); simpl in *.
          inv Hginject2. 
        destruct p; simpl in *. 
        destruct gv; inv H0; simpl in *. 
          destruct gv2; simpl in *.
            inv Hginject2. 

            destruct p; simpl in *. 
            destruct gv2. 
              simpl in *. inv Hginject2. eauto.
              destruct p. simpl in *.
              destruct (split gv2). inv Hginject2. inv H4.
             
          destruct p. destruct (split gv).
          destruct gv2; simpl in *. 
            inv Hginject2. 

            destruct p; simpl in *. 
            destruct gv2; simpl in *. 
              inv Hginject2. inv H4.
              exists Vundef. split; auto.
    destruct Hvinj as [v2 [Hg2v Hvinj]].
    assert (H0:=Hmstore).
    destruct Hmsim as [Hmsim1 [Hmgb [Hzero Hmsim2]]].
    eapply Mem.store_mapped_inj with (f:=mi)(m2:=Mem2) in H0; 
      try solve [eauto | 
        inversion Hwfmi; eauto using meminj_no_overlap__implies].
    destruct H0 as [Mem2' [J2 J4]].
    exists Mem2'.
    assert ( mstore TD Mem2
      ((Vptr b2 (Int.add 31 i1 (Int.repr 31 delta)), m1) :: nil) t
      gv2 align0 = ret Mem2') as J.
      unfold mstore. simpl. rewrite <- HeqR'. rewrite Hg2v.
      clear - J2 Hwfmi H2.
      inversion_clear Hwfmi.
      apply mi_range_block in H2. subst.
      rewrite Int.add_zero.
      assert (Int.signed 31 i1 + 0 = Int.signed 31 i1) as EQ. zauto.
      rewrite EQ in J2. auto.
    split; auto.
    split.
    Case "wf_sb_mi".
      clear - Hwfmi J2.
      inversion Hwfmi.
      split; auto.
      SCase "Hmap4".
        intros b1 b0 delta2 J.
        apply Hmap2 in J.
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
      split; auto.
        clear - Hzero Hmstore.
        apply Mem.nextblock_store in Hmstore. intros.
        apply Hzero. rewrite <- Hmstore. auto.
    
        clear Hmsim1.
        intros lc2 gl b ofs bgv egv als bid0 eid0 pgv' fs F B cs tmn S Ps EC
          v1 cm Hwfg G1 G2 G3.
        assert (G3':=G3).
        eapply Hmsim2 with (bgv:=bgv)(egv:=egv)(als:=als)
          (bid0:=bid0)(eid0:=eid0)(b:=b)(ofs:=ofs) in G3'; eauto.
        destruct G3' as [bgv' [egv' [G4 [G5 G6]]]].
        exists bgv'. exists egv'.
        eapply store_doesnt_change_gmmd in G4; eauto.

    destruct p. simpl in HeqR3. destruct (split gvp2). inversion HeqR3.
Qed.

Lemma mload_inversion : forall Mem2 t align0 TD gvp2 
  (gv2 : GenericValue)
  (H21 : mload TD Mem2 gvp2 t align0 = ret gv2),
  exists b, exists ofs, exists m, gvp2 = (Vptr b ofs,m)::nil.
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
  unfold ptr2GV, val2GV. eauto.
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

Lemma mstore_inversion : forall Mem2 t align0 TD gvp2 Mem2'
  (gv2 : GenericValue)
  (H21 : mstore TD Mem2 gvp2 t gv2 align0 = ret Mem2'),
  exists b, exists ofs, exists cm, gvp2 = (Vptr b ofs,cm)::nil.
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
  exists b0. exists i1.  eauto.
Qed.

Lemma prop_metadata_inv : forall ex_ids3 rm2 c vp id0 ex_ids5 cs1',
  prop_metadata ex_ids3 rm2 c vp id0 = ret (ex_ids5, cs1') ->
  exists bv, exists ev, exists bid0, exists eid0,
     get_reg_metadata rm2 vp = Some (bv, ev) /\
     lookupAL _ rm2 id0 = Some (bid0, eid0) /\
     ex_ids5 = ex_ids3 /\ 
     cs1' = c :: insn_cast bid0 castop_bitcast p8 bv p8
              :: insn_cast eid0 castop_bitcast p8 ev p8 :: nil.
Proof.
  intros.
  unfold prop_metadata in H.
  destruct (get_reg_metadata rm2 vp) as [[bv ev]|]; try solve [inversion H].
  destruct (lookupAL _ rm2 id0) as [[bid0 eid0]|]; inv H.
  exists bv. exists ev. exists bid0. exists eid0. split; auto.
Qed.

Fixpoint gvs_inject mi gvs1 gvs2 : Prop :=
match (gvs1, gvs2) with
| (nil, nil) => True
| (gv1::gvs1', gv2::gvs2') => gv_inject mi gv1 gv2 /\ gvs_inject mi gvs1' gvs2'
| _ => False
end.

Lemma simulation__GEP : forall maxb mi TD Mem Mem2 inbounds0
    vidxs vidxs' gvp1 gvp gvp' t,
  wf_sb_mi maxb mi Mem Mem2 ->
  gv_inject mi gvp gvp' ->
  gvs_inject mi vidxs vidxs' ->
  GEP TD t gvp vidxs inbounds0 = ret gvp1 ->
  exists gvp2,
    GEP TD t gvp' vidxs' inbounds0 = ret gvp2 /\
    gv_inject mi gvp1 gvp2.
Admitted.

Lemma simulation__values2GVs : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 
    gl F idxs gvs,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  values2GVs TD idxs lc gl = ret gvs ->
  exists gvs', 
    values2GVs TD idxs lc2 gl = ret gvs' /\
    gvs_inject mi gvs gvs'.
Admitted.

Lemma simulation__TRUNC : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F t1 
    v1 gv3 op t2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  TRUNC TD lc gl op t1 v1 t2 = ret gv3 ->
  exists gv3',
    TRUNC TD lc2 gl op t1 v1 t2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.


Lemma simulation__EXT : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F t1 
    v1 gv3 op t2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  EXT TD lc gl op t1 v1 t2 = ret gv3 ->
  exists gv3',
    EXT TD lc2 gl op t1 v1 t2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.


Lemma simulation__CAST : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F t1 
    v1 gv3 op t2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  CAST TD lc gl op t1 v1 t2 = ret gv3 ->
  exists gv3',
    CAST TD lc2 gl op t1 v1 t2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__ICMP : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F t1 
    v1 gv3 cond0 v2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  ICMP TD lc gl cond0 t1 v1 v2 = ret gv3 ->
  exists gv3',
    ICMP TD lc2 gl cond0 t1 v1 v2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__FCMP : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F fp 
    v1 gv3 fcond0 v2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  FCMP TD lc gl fcond0 fp v1 v2 = ret gv3 ->
  exists gv3',
    FCMP TD lc2 gl fcond0 fp v1 v2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__isGVZero : forall mi c c' TD,
  gv_inject mi c c' ->
  isGVZero TD c = isGVZero TD c'.
Admitted.



(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)

