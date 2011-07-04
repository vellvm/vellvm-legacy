Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import Ensembles.
Require Import ssa_dynamic.
Require Import Floats.
Require Import ndopsem.

Export NDopsem.
Export LLVMopsem.

Definition instantiate_gv (gv:GenericValue) (gvs:GVs) : Prop :=
match gv with
| (Vundef, _)::nil => Inhabited _ gvs
| _ => Same_set _ (Singleton GenericValue gv) gvs
end.

Fixpoint instantiate_locals (lc1 : GVMap) (lc2 : GVsMap) : Prop :=
match lc1, lc2 with
| nil, nil => True
| (id1,gv1)::lc1', (id2,gvs2)::lc2' => 
    id1=id2 /\ instantiate_gv gv1 gvs2 /\ instantiate_locals lc1' lc2'
| _, _ => False
end.

Definition instantiate_EC (ec1 : LLVMopsem.ExecutionContext) 
  (ec2 : NDopsem.ExecutionContext) : Prop :=
match ec1, ec2 with
| LLVMopsem.mkEC f1 b1 cs1 tmn1 lc1 als1, NDopsem.mkEC f2 b2 cs2 tmn2 lc2 als2 =>
    f1 = f2 /\ b1 = b2 /\ cs1 = cs2 /\ tmn1 = tmn2 /\
    instantiate_locals lc1 lc2 /\ als1 = als2
end.

Fixpoint instantiate_ECs (ecs1 : LLVMopsem.ECStack) (ecs2 : NDopsem.ECStack) 
  : Prop :=
match ecs1, ecs2 with
| nil, nil => True
| ec1::ecs1', ec2::ecs2' => instantiate_EC ec1 ec2 /\ instantiate_ECs ecs1' ecs2'
| _, _ => False
end.

Definition instantiate_State (st1 : LLVMopsem.State) (st2 : NDopsem.State) 
  : Prop :=
match st1, st2 with
| LLVMopsem.mkState s1 td1 ps1 ecs1 gl1 fs1 M1,
  NDopsem.mkState s2 td2 ps2 ecs2 gl2 fs2 M2 =>
    s1 = s2 /\ td1 = td2 /\ ps1 = ps2 /\ instantiate_ECs ecs1 ecs2 /\ gl1 = gl2
    /\ fs1 = fs2 /\ M1 = M2
end.

Ltac simpl_nd_llvmds :=
  match goal with
  | [Hsim : instantiate_State {| ECS := _::_::_ |} ?st2 |- _ ] =>
     destruct st2 as [S' TD' Ps' ECs' gl' fs' M'];
     destruct Hsim as [eq1 [eq2 [eq3 [Hsim [eq4 [eq5 eq6]]]]]]; subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' als1'] ECs']; 
       try solve [inversion Hsim];
     simpl in Hsim; destruct Hsim as [Hsim1 Hsim2];
     destruct ECs' as [|[f2' b2' cs2' tmn2' lc2' als2'] ECs'];
       try solve [inversion Hsim2];
     destruct Hsim2 as [Hsim2 Hsim3];
     destruct Hsim1 as [J1 [J2 [J3 [J4 [Hsim1 J6]]]]]; subst;
     destruct Hsim2 as [J1 [J2 [J3 [J4 [Hsim2 J6]]]]]; subst
  | [Hsim : instantiate_State {| ECS := _::_|} ?st2 |- _ ] =>
     destruct st2 as [S' TD' Ps' ECs' gl' fs' M'];
     destruct Hsim as [eq1 [eq2 [eq3 [Hsim [eq4 [eq5 eq6]]]]]]; subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' als1'] ECs']; 
       try solve [inversion Hsim];
     simpl in Hsim; destruct Hsim as [Hsim1 Hsim2];
     destruct Hsim1 as [J1 [J2 [J3 [J4 [Hsim1 J6]]]]]; subst
  end.

Lemma instantiate_locals__lookup : forall lc1 lc2 id1 gv1,
  instantiate_locals lc1 lc2 -> 
  lookupAL _ lc1 id1 = Some gv1 ->
  exists gvs2, lookupAL _ lc2 id1 = Some gvs2 /\ instantiate_gv gv1 gvs2.
Proof.
  induction lc1; destruct lc2; simpl; intros id1 gv1 Hinst Hlk.  
    inv Hlk.
    inv Hinst.
    destruct a. inv Hinst.     

    destruct a. destruct p.
    destruct Hinst as [J1 [J2 J3]]; subst.
    destruct (id1 == i1); subst; eauto.
      inv Hlk. eauto.
Qed.

Lemma same_singleton_set : forall gv,
  Same_set GenericValue (Singleton _ gv) (Singleton _ gv).
Proof.
  unfold Same_set, Included. auto.
Qed.

Lemma instantiate_gv__gv2gvs : forall gv, instantiate_gv gv ($ gv $).
Proof.
  intros.
  assert (J:=@gv2gvs__inhabited gv).
  destruct gv; simpl; auto using same_singleton_set.
    destruct p; simpl.
    destruct v; simpl; auto using same_singleton_set.     
    destruct gv; simpl; auto using same_singleton_set.     
Qed.

Lemma instantiate_locals__getOperandValue : forall TD v lc1 lc2 gl gv1,
  instantiate_locals lc1 lc2 -> 
  getOperandValue TD v lc1 gl = Some gv1 ->
  exists gvs2, NDopsem.getOperandValue TD v lc2 gl = Some gvs2 /\
    instantiate_gv gv1 gvs2.
Proof.
  intros.
  destruct v; simpl in *.
    eapply instantiate_locals__lookup; eauto.
    exists ($ gv1 $). unfold mmap. rewrite H0. simpl. 
    auto using instantiate_gv__gv2gvs.
Qed.

Ltac tinv H := try solve [inv H].

Lemma instantiate_locals__updateAddAL : forall gv3 gvs3',
  instantiate_gv gv3 gvs3' ->
  forall lc1 lc2 id0,
  instantiate_locals lc1 lc2 -> 
  instantiate_locals (updateAddAL GenericValue lc1 id0 gv3)
    (updateAddAL GVs lc2 id0 gvs3').
Proof.
  induction lc1; destruct lc2; simpl; intros id0 H1; auto.
    inv H1.  
    destruct a. inv H1.
    destruct a. destruct p. destruct H1 as [eq [H1 H2]]; subst.
    destruct (id0 == i1); subst; simpl.
      split; auto.
      split; auto.
Qed.   

Lemma instantiate_locals__returnUpdateLocals : forall TD lc1 lc2 lc1' lc2' Result
    gl lc1'' c,
  instantiate_locals lc1 lc2 -> 
  instantiate_locals lc1' lc2' -> 
  returnUpdateLocals TD c Result lc1 lc1' gl = ret lc1'' ->
  exists lc2'', 
    NDopsem.returnUpdateLocals TD c Result lc2 lc2' gl = ret lc2'' /\
    instantiate_locals lc1'' lc2''. 
Proof.
  intros.
  unfold returnUpdateLocals in H1.
  remember (getOperandValue TD Result lc1 gl) as R.
  destruct R; tinv H1.
  symmetry in HeqR.
  eapply instantiate_locals__getOperandValue in HeqR; eauto.
  destruct HeqR as [gvs2 [J1 J2]].
  unfold NDopsem.returnUpdateLocals.
  rewrite J1. 
  destruct (getCallerReturnID c); inv H1; eauto.
    exists (updateAddAL GVs lc2' i0 gvs2).   
    split; auto using instantiate_locals__updateAddAL.
Qed.

Lemma instantiate_locals__getIncomingValuesForBlockFromPHINodes : forall TD b
    gl lc1 lc2 (Hlc : instantiate_locals lc1 lc2) ps re1,  
  getIncomingValuesForBlockFromPHINodes TD ps b gl lc1 = Some re1 ->
  exists re2,
    NDopsem.getIncomingValuesForBlockFromPHINodes TD ps b gl lc2 = Some re2 /\
    instantiate_locals re1 re2.
Proof.
  induction ps; simpl; intros.  
    inv H. exists nil. simpl. auto.

    destruct a.
    destruct (getValueViaBlockFromValuels l0 b); tinv H.
    remember (getOperandValue TD v lc1 gl) as R.
    destruct R; tinv H.
    symmetry in HeqR.  
    eapply instantiate_locals__getOperandValue in HeqR; eauto.
    destruct HeqR as [gvs2 [J1 J2]].
    remember (getIncomingValuesForBlockFromPHINodes TD ps b gl lc1) as R1.
    destruct R1; inv H.  
    rewrite J1.
    symmetry in HeqR1.
    destruct (@IHps l1) as [re2 [J3 J4]]; auto.
    rewrite J3. 
    exists ((i0, gvs2) :: re2). simpl. auto.
Qed.

Lemma instantiate_locals__updateValuesForNewBlock : forall lc1 lc2 re1 re2,
  instantiate_locals lc1 lc2 ->
  instantiate_locals re1 re2 ->
  instantiate_locals (updateValuesForNewBlock re1 lc1)
     (NDopsem.updateValuesForNewBlock re2 lc2).
Proof.
  induction re1; destruct re2; simpl; intros; auto.
    inv H0.
    destruct a. inv H0.
    destruct a. destruct p. destruct H0 as [eq [J1 J2]]; subst.
    apply instantiate_locals__updateAddAL; auto.    
Qed.

Lemma instantiate_locals__switchToNewBasicBlock : forall TD lc1 lc2 gl lc1' b b',
  instantiate_locals lc1 lc2 -> 
  switchToNewBasicBlock TD b' b gl lc1 = Some lc1' ->
  exists lc2', NDopsem.switchToNewBasicBlock TD b' b gl lc2 = Some lc2' /\
    instantiate_locals lc1' lc2'. 
Proof.
  intros.
  unfold switchToNewBasicBlock in H0.
  unfold NDopsem.switchToNewBasicBlock.
  remember (getIncomingValuesForBlockFromPHINodes TD (getPHINodesFromBlock b') b
           gl lc1) as R.
  destruct R; inv H0.
  symmetry in HeqR.
  eapply instantiate_locals__getIncomingValuesForBlockFromPHINodes in HeqR; eauto.
  destruct HeqR as [re2 [J1 J2]].
  rewrite J1.
  exists (NDopsem.updateValuesForNewBlock re2 lc2).
  split; auto using instantiate_locals__updateValuesForNewBlock.
Qed.

Lemma instantiate_gv__inhabited : forall gv gvs,
  instantiate_gv gv gvs -> Inhabited _ gvs.
Proof.
  intros.
  destruct gv; simpl in *.
    apply Extensionality_Ensembles in H. subst.
    apply singleton_inhabited.

    destruct p.
    destruct v; try solve [auto |
      apply Extensionality_Ensembles in H; subst; apply singleton_inhabited].
    destruct gv; try solve [auto |
      apply Extensionality_Ensembles in H; subst; apply singleton_inhabited].
Qed.

Lemma mbop_is_total : forall TD bop0 sz0 x y, 
  exists z, mbop TD bop0 sz0 x y = Some z.
Proof.
  intros.
  unfold mbop.
  destruct (GV2val TD x); eauto.
  destruct v; eauto.
  destruct (GV2val TD y); eauto.
  destruct v; eauto.
  destruct (eq_nat_dec (wz + 1) (Size.to_nat sz0)); eauto.
  destruct bop0; eauto.
Qed.

Lemma instantiate_gv__mbop__helper : forall x xs y ys TD bop0 sz0
  (H0 : instantiate_gv x xs)
  (H1 : instantiate_gv y ys),
   Inhabited GenericValue
     (fun gv3 : GenericValue =>
      exists gv1 : GenericValue,
        exists gv2 : GenericValue,
          exists gv3' : GenericValue,
            gv1 @ xs /\
            gv2 @ ys /\ mbop TD bop0 sz0 gv1 gv2 = ret gv3' /\ gv3 @ $ gv3' $).
Proof.
  intros.
  apply instantiate_gv__inhabited in H0. inv H0.
  apply instantiate_gv__inhabited in H1. inv H1.
  destruct (@mbop_is_total TD bop0 sz0 x0 x1) as [z J].
  assert (J1:=@gv2gvs__inhabited z). inv J1.
  exists x2. unfold Ensembles.In. exists x0. exists x1. exists z.
  split; auto. 
Qed.

Lemma instantiate_gv__mbop : forall TD bop0 sz0 x y z xs ys,
  mbop TD bop0 sz0 x y = Some z ->
  instantiate_gv x xs ->
  instantiate_gv y ys ->
  instantiate_gv z (lift_op2 (mbop TD bop0 sz0) xs ys).
Proof.
  intros. unfold lift_op2. 
  destruct x; try solve [inv H; simpl; 
      eapply instantiate_gv__mbop__helper; eauto].
  destruct p.
  destruct x; try solve [inv H; simpl; 
      eapply instantiate_gv__mbop__helper; eauto].
  destruct v; try solve [inv H; simpl; 
      eapply instantiate_gv__mbop__helper; eauto].
  destruct y; try solve [inv H; simpl; 
      eapply instantiate_gv__mbop__helper; eauto].
  destruct p.
  destruct y; try solve [inv H; simpl; 
      eapply instantiate_gv__mbop__helper; eauto].
  destruct v; try solve [inv H; simpl; 
      eapply instantiate_gv__mbop__helper; eauto].
  apply Extensionality_Ensembles in H0. subst.
  apply Extensionality_Ensembles in H1. subst.
  assert (J1:=@gv2gvs__inhabited z). inv J1.

  assert (exists v, exists c, z = (v,c)::nil) as EQ.
    unfold mbop in H.
    destruct (GV2val TD ((Vint wz i0, m) :: nil));
      try solve [inv H; unfold gundef; simpl; eauto].
    destruct v; try solve [inv H; unfold gundef; simpl; eauto].
    destruct (eq_nat_dec (wz1 + 1) (Size.to_nat sz0));
      try solve [inv H; unfold gundef; simpl; eauto].
    destruct (GV2val TD ((Vint wz0 i1, m0) :: nil));
      try solve [inv H; unfold gundef; simpl; eauto].
    destruct v; try solve [inv H; unfold gundef; simpl; eauto].
    unfold val2GV in *.
    destruct bop0; try solve [inv H; unfold gundef; simpl; eauto].
    
  destruct EQ as [v [c EQ]]. subst.
  simpl.   
  destruct v.
    exists x. exists ((Vint wz i0, m) :: nil). exists ((Vint wz0 i1, m0) :: nil).
    exists ((Vundef, c) :: nil). 
    repeat (split; try solve [auto | constructor]).

    unfold Same_set, Included.
    split; intros.
      inv H1. unfold Ensembles.In. 
      exists ((Vint wz i0, m) :: nil). exists ((Vint wz0 i1, m0) :: nil).
      exists ((Vint wz1 i2, c) :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2.
      rewrite H in J3. inv J3. inv J4. constructor.

    unfold Same_set, Included.
    split; intros.
      inv H1. unfold Ensembles.In. 
      exists ((Vint wz i0, m) :: nil). exists ((Vint wz0 i1, m0) :: nil).
      exists ((Vfloat f, c) :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2.
      rewrite H in J3. inv J3. inv J4. constructor.

    unfold Same_set, Included.
    split; intros.
      inv H0. unfold Ensembles.In. 
      exists ((Vint wz i0, m) :: nil). exists ((Vint wz0 i1, m0) :: nil).
      exists ((Vptr b i2, c) :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2.
      rewrite H in J3. inv J3. inv J4. constructor.

    unfold Same_set, Included.
    split; intros.
      inv H0. unfold Ensembles.In. 
      exists ((Vint wz i0, m) :: nil). exists ((Vint wz0 i1, m0) :: nil).
      exists ((Vinttoptr i2, c) :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2.
      rewrite H in J3. inv J3. inv J4. constructor.
Qed.

Lemma instantiate_locals__BOP : forall TD lc1 lc2 gl v1 v2 gv3 bop sz,
  instantiate_locals lc1 lc2 -> 
  BOP TD lc1 gl bop sz v1 v2 = Some gv3 ->
  exists gvs3', NDopsem.BOP TD lc2 gl bop sz v1 v2 = Some gvs3' /\
    instantiate_gv gv3 gvs3'.
Proof.
  intros.
  apply BOP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]].
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold NDopsem.BOP.
  rewrite H1. rewrite H3.
  exists (lift_op2 (mbop TD bop0 sz0) gvs1 gvs2).
  split; eauto using instantiate_gv__mbop.
Qed.
  
Lemma mfbop_is_total : forall TD fbop0 fp x y, 
  exists z, mfbop TD fbop0 fp x y = Some z.
Proof.
  intros.
  unfold mfbop.
  destruct (GV2val TD x); eauto.
  destruct v; eauto.
  destruct (GV2val TD y); eauto.
  destruct v; eauto.
  destruct fp; eauto.
Qed.

Lemma instantiate_gv__mfbop__helper : forall x xs y ys TD fbop0 fp
  (H0 : instantiate_gv x xs)
  (H1 : instantiate_gv y ys),
   Inhabited GenericValue
     (fun gv3 : GenericValue =>
      exists gv1 : GenericValue,
        exists gv2 : GenericValue,
          exists gv3' : GenericValue,
            gv1 @ xs /\
            gv2 @ ys /\ mfbop TD fbop0 fp gv1 gv2 = ret gv3' /\ gv3 @ $ gv3' $).
Proof.
  intros.
  apply instantiate_gv__inhabited in H0. inv H0.
  apply instantiate_gv__inhabited in H1. inv H1.
  destruct (@mfbop_is_total TD fbop0 fp x0 x1) as [z J].
  assert (J1:=@gv2gvs__inhabited z). inv J1.
  exists x2. unfold Ensembles.In. exists x0. exists x1. exists z.
  split; auto. 
Qed.

Lemma instantiate_gv__mfbop : forall TD fbop0 fp x y z xs ys,
  mfbop TD fbop0 fp x y = Some z ->
  instantiate_gv x xs ->
  instantiate_gv y ys ->
  instantiate_gv z (lift_op2 (mfbop TD fbop0 fp) xs ys).
Proof.
  intros. unfold lift_op2.
  destruct x; try solve [inv H; destruct fp; simpl; 
      eapply instantiate_gv__mfbop__helper; eauto].
  destruct p.
  destruct x; try solve [inv H; destruct fp; simpl; 
      eapply instantiate_gv__mfbop__helper; eauto].
  destruct v; try solve [inv H; destruct fp; simpl; 
      eapply instantiate_gv__mfbop__helper; eauto].
  destruct y; try solve [inv H; destruct fp; simpl; 
      eapply instantiate_gv__mfbop__helper; eauto].
  destruct p.
  destruct y; try solve [inv H; destruct fp; simpl; 
      eapply instantiate_gv__mfbop__helper; eauto].
  destruct v; try solve [inv H; destruct fp; simpl; 
      eapply instantiate_gv__mfbop__helper; eauto].
  apply Extensionality_Ensembles in H0. subst.
  apply Extensionality_Ensembles in H1. subst.
  assert (J1:=@gv2gvs__inhabited z). inv J1.

  assert (exists v, exists c, z = (v,c)::nil) as EQ.
    unfold mfbop in H.
    destruct (GV2val TD ((Vfloat f, m) :: nil));
      try solve [inv H; destruct fp; unfold gundef, uninits; simpl; eauto].
    destruct v; try solve 
      [inv H; destruct fp; unfold gundef, uninits; simpl; eauto].
    destruct (GV2val TD ((Vfloat f0, m0) :: nil));
      try solve [inv H; destruct fp; unfold gundef, uninits; simpl; eauto].
    destruct v; try solve 
      [inv H; destruct fp; unfold gundef, uninits; simpl; eauto].
    unfold val2GV in *.
    destruct fp; destruct fbop0; 
      try solve [inv H; unfold gundef, uninits; simpl; eauto].
    
  destruct EQ as [v [c EQ]]. subst.
  simpl.   
  destruct v.
    exists x. exists ((Vfloat f, m) :: nil). exists ((Vfloat f0, m0) :: nil).
    exists ((Vundef, c) :: nil). 
    repeat (split; try solve [auto | constructor]).

    unfold Same_set, Included.
    split; intros.
      inv H1. unfold Ensembles.In. 
      exists ((Vfloat f, m) :: nil). exists ((Vfloat f0, m0) :: nil).
      exists ((Vint wz i0, c) :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2.
      rewrite H in J3. inv J3. inv J4. constructor.

    unfold Same_set, Included.
    split; intros.
      inv H1. unfold Ensembles.In. 
      exists ((Vfloat f, m) :: nil). exists ((Vfloat f0, m0) :: nil).
      exists ((Vfloat f1, c) :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2.
      rewrite H in J3. inv J3. inv J4. constructor.

    unfold Same_set, Included.
    split; intros.
      inv H0. unfold Ensembles.In. 
      exists ((Vfloat f, m) :: nil). exists ((Vfloat f0, m0) :: nil).
      exists ((Vptr b i0, c) :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2.
      rewrite H in J3. inv J3. inv J4. constructor.

    unfold Same_set, Included.
    split; intros.
      inv H0. unfold Ensembles.In. 
      exists ((Vfloat f, m) :: nil). exists ((Vfloat f0, m0) :: nil).
      exists ((Vinttoptr i0, c) :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2.
      rewrite H in J3. inv J3. inv J4. constructor.
Qed.

Lemma instantiate_locals__FBOP : forall TD lc1 lc2 gl v1 v2 gv3 fbop fp,
  instantiate_locals lc1 lc2 -> 
  FBOP TD lc1 gl fbop fp v1 v2 = Some gv3 ->
  exists gvs3', NDopsem.FBOP TD lc2 gl fbop fp v1 v2 = Some gvs3' /\
    instantiate_gv gv3 gvs3'.
Proof.
  intros.
  apply FBOP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]].
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold NDopsem.FBOP.
  rewrite H1. rewrite H3.
  exists (lift_op2 (mfbop TD fbop0 fp) gvs1 gvs2).
  split; eauto using instantiate_gv__mfbop.
Qed.

Lemma micmp_is_total : forall TD c t x y, 
  exists z, micmp TD c t x y = Some z.
Proof.
  intros.
  unfold micmp, micmp_int.
  destruct t; eauto.
  destruct (GV2val TD x); eauto.
  destruct v; eauto.
  destruct (GV2val TD y); eauto.
  destruct v; eauto.
  destruct c; eauto.
Qed.

Lemma instantiate_gv__micmp__helper : forall x xs y ys TD c t
  (H0 : instantiate_gv x xs)
  (H1 : instantiate_gv y ys),
   Inhabited GenericValue
     (fun gv3 : GenericValue =>
      exists gv1 : GenericValue,
        exists gv2 : GenericValue,
          exists gv3' : GenericValue,
            gv1 @ xs /\
            gv2 @ ys /\ micmp TD c t gv1 gv2 = ret gv3' /\ gv3 @ $ gv3' $).
Proof.
  intros.
  apply instantiate_gv__inhabited in H0. inv H0.
  apply instantiate_gv__inhabited in H1. inv H1.
  destruct (@micmp_is_total TD c t x0 x1) as [z J].
  assert (J1:=@gv2gvs__inhabited z). inv J1.
  exists x2. unfold Ensembles.In. exists x0. exists x1. exists z.
  split; auto. 
Qed.

Lemma instantiate_gv__micmp : forall TD c t x y z xs ys,
  micmp TD c t x y = Some z ->
  instantiate_gv x xs ->
  instantiate_gv y ys ->
  instantiate_gv z (lift_op2 (micmp TD c t) xs ys).
Proof.
  intros. unfold lift_op2.
  unfold micmp in H.
Opaque micmp.
  destruct t; try solve [inv H; simpl; 
      eapply instantiate_gv__micmp__helper; eauto].
  destruct x; try solve [inv H; simpl; 
      eapply instantiate_gv__micmp__helper; eauto].
  destruct p.
  destruct x; try solve [inv H; simpl; 
      eapply instantiate_gv__micmp__helper; eauto].
  destruct v; try solve [inv H; simpl; 
      eapply instantiate_gv__micmp__helper; eauto].
  destruct y; try solve [inv H; simpl; 
      eapply instantiate_gv__micmp__helper; eauto].
  destruct p.
  destruct y; try solve [inv H; simpl; 
      eapply instantiate_gv__micmp__helper; eauto].
  destruct v; try solve [inv H; simpl; 
      eapply instantiate_gv__micmp__helper; eauto].
  apply Extensionality_Ensembles in H0. subst.
  apply Extensionality_Ensembles in H1. subst.
  assert (J1:=@gv2gvs__inhabited z). inv J1.
Transparent micmp.
  assert (exists v, exists c, z = (v,c)::nil) as EQ.
    unfold micmp_int in H.
    destruct (GV2val TD ((Vint wz i0, m) :: nil));
      try solve [inv H; unfold gundef; simpl; eauto].
    destruct v; try solve [inv H; unfold gundef; simpl; eauto].
    destruct (GV2val TD ((Vint wz0 i1, m0) :: nil));
      try solve [inv H; unfold gundef; simpl; eauto].
    destruct v; try solve [inv H; unfold gundef; simpl; eauto].
    unfold val2GV in *.
    destruct c; try solve [inv H; unfold gundef; simpl; eauto].
    
  destruct EQ as [v [c' EQ]]. subst.
  simpl.   
  destruct v.
    exists x. exists ((Vint wz i0, m) :: nil). exists ((Vint wz0 i1, m0) :: nil).
    exists ((Vundef, c') :: nil). 
    repeat (split; try solve [auto | constructor]).

    unfold Same_set, Included.
    split; intros.
      inv H1. unfold Ensembles.In.
      exists ((Vint wz i0, m) :: nil). exists ((Vint wz0 i1, m0) :: nil). 
      exists ((Vint wz1 i2, c') :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2.
      rewrite H in J3. inv J3. inv J4. constructor.

    unfold Same_set, Included.
    split; intros.
      inv H1. unfold Ensembles.In. 
      exists ((Vint wz i0, m) :: nil). exists ((Vint wz0 i1, m0) :: nil). 
      exists ((Vfloat f, c') :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2.
      rewrite H in J3. inv J3. inv J4. constructor.

    unfold Same_set, Included.
    split; intros.
      inv H0. unfold Ensembles.In. 
      exists ((Vint wz i0, m) :: nil). exists ((Vint wz0 i1, m0) :: nil). 
      exists ((Vptr b i2, c') :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2.
      rewrite H in J3. inv J3. inv J4. constructor.

    unfold Same_set, Included.
    split; intros.
      inv H0. unfold Ensembles.In. 
      exists ((Vint wz i0, m) :: nil). exists ((Vint wz0 i1, m0) :: nil). 
      exists ((Vinttoptr i2, c') :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2.
      rewrite H in J3. inv J3. inv J4. constructor.
Qed.

Lemma instantiate_locals__ICMP : forall TD lc1 lc2 gl v1 v2 gv3 c t,
  instantiate_locals lc1 lc2 -> 
  ICMP TD lc1 gl c t v1 v2 = Some gv3 ->
  exists gvs3', NDopsem.ICMP TD lc2 gl c t v1 v2 = Some gvs3' /\
    instantiate_gv gv3 gvs3'.
Proof.
  intros.
  apply ICMP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]].
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold NDopsem.ICMP.
  rewrite H1. rewrite H3.
  exists (lift_op2 (micmp TD c t) gvs1 gvs2).
  split; eauto using instantiate_gv__micmp.
Qed.

Lemma mfcmp_is_total : forall TD c t x y, 
  exists z, mfcmp TD c t x y = Some z.
Proof.
  intros.
  unfold mfcmp.
  destruct (GV2val TD x); eauto.
  destruct v; eauto.
  destruct (GV2val TD y); eauto.
  destruct v; eauto.
  destruct t; destruct c; eauto.
Qed.

Lemma instantiate_gv__mfcmp__helper : forall x xs y ys TD c t
  (H0 : instantiate_gv x xs)
  (H1 : instantiate_gv y ys),
   Inhabited GenericValue
     (fun gv3 : GenericValue =>
      exists gv1 : GenericValue,
        exists gv2 : GenericValue,
          exists gv3' : GenericValue,
            gv1 @ xs /\
            gv2 @ ys /\ mfcmp TD c t gv1 gv2 = ret gv3' /\ gv3 @ $ gv3' $).
Proof.
  intros.
  apply instantiate_gv__inhabited in H0. inv H0.
  apply instantiate_gv__inhabited in H1. inv H1.
  destruct (@mfcmp_is_total TD c t x0 x1) as [z J].
  assert (J1:=@gv2gvs__inhabited z). inv J1.
  exists x2. unfold Ensembles.In. exists x0. exists x1. exists z.
  split; auto. 
Qed.

Lemma instantiate_gv__mfcmp : forall TD c t x y z xs ys,
  mfcmp TD c t x y = Some z ->
  instantiate_gv x xs ->
  instantiate_gv y ys ->
  instantiate_gv z (lift_op2 (mfcmp TD c t) xs ys).
Proof.
  intros. unfold lift_op2.
  unfold mfcmp in H.
Opaque mfcmp.
  destruct x; try solve [inv H; simpl; 
      eapply instantiate_gv__mfcmp__helper; eauto].
  destruct p.
  destruct x; try solve [inv H; simpl; 
      eapply instantiate_gv__mfcmp__helper; eauto].
  destruct v; try solve [inv H; simpl; 
      eapply instantiate_gv__mfcmp__helper; eauto].
  destruct y; try solve [inv H; simpl; 
      eapply instantiate_gv__mfcmp__helper; eauto].
  destruct p.
  destruct y; try solve [inv H; simpl; 
      eapply instantiate_gv__mfcmp__helper; eauto].
  destruct v; try solve [inv H; simpl; 
      eapply instantiate_gv__mfcmp__helper; eauto].
  simpl in H.
  apply Extensionality_Ensembles in H0. subst.
  apply Extensionality_Ensembles in H1. subst.
  assert (J1:=@gv2gvs__inhabited z). inv J1.
Transparent mfcmp.
  assert (exists v, exists c, z = (v,c)::nil) as EQ.
    unfold val2GV in *.
    destruct t; destruct c; try solve [inv H; unfold gundef; simpl; eauto].
  destruct EQ as [v [c' EQ]]. subst.
  unfold mfcmp.
  simpl.   
  destruct v.
    exists x. exists ((Vfloat f, m) :: nil). exists ((Vfloat f0, m0) :: nil).
    exists ((Vundef, c') :: nil). 
    repeat (split; try solve [auto | constructor]).

    unfold Same_set, Included.
    split; intros.
      inv H1. unfold Ensembles.In.
      exists ((Vfloat f, m) :: nil). exists ((Vfloat f0, m0) :: nil).
      exists ((Vint wz i0, c') :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2. simpl in J3.
      rewrite H in J3. inv J3. inv J4. constructor.

    unfold Same_set, Included.
    split; intros.
      inv H1. unfold Ensembles.In. 
      exists ((Vfloat f, m) :: nil). exists ((Vfloat f0, m0) :: nil).
      exists ((Vfloat f1, c') :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2. simpl in J3.
      rewrite H in J3. inv J3. inv J4. constructor.

    unfold Same_set, Included.
    split; intros.
      inv H0. unfold Ensembles.In. 
      exists ((Vfloat f, m) :: nil). exists ((Vfloat f0, m0) :: nil).
      exists ((Vptr b i0, c') :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2. simpl in J3.
      rewrite H in J3. inv J3. inv J4. constructor.

    unfold Same_set, Included.
    split; intros.
      inv H0. unfold Ensembles.In. 
      exists ((Vfloat f, m) :: nil). exists ((Vfloat f0, m0) :: nil).
      exists ((Vinttoptr i0, c') :: nil). 
      repeat (split; try solve [auto | constructor]).

      inv H1. unfold Ensembles.In. 
      destruct H2 as [gv2 [gv3 [J1 [J2 [J3 J4]]]]].
      inv J1. inv J2. simpl in J3.
      rewrite H in J3. inv J3. inv J4. constructor.
Qed.

Lemma instantiate_locals__FCMP : forall TD lc1 lc2 gl v1 v2 gv3 c t,
  instantiate_locals lc1 lc2 -> 
  FCMP TD lc1 gl c t v1 v2 = Some gv3 ->
  exists gvs3', NDopsem.FCMP TD lc2 gl c t v1 v2 = Some gvs3' /\
    instantiate_gv gv3 gvs3'.
Proof.
  intros.
  apply FCMP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]].
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold NDopsem.FCMP.
  rewrite H1. rewrite H3.
  exists (lift_op2 (mfcmp TD c t) gvs1 gvs2).
  split; eauto using instantiate_gv__mfcmp.
Qed.

Fixpoint instantiate_gvs (l1 : list GenericValue) (l2 : list GVs) :=
match l1, l2 with
| nil, nil => True
| gv1::l1', gvs2::l2' => instantiate_gv gv1 gvs2 /\ instantiate_gvs l1' l2'
| _, _ => False
end.

Lemma instantiate_locals__values2GVs : forall TD lc1 lc2 gl idxs vidxs,
  instantiate_locals lc1 lc2 -> 
  values2GVs TD idxs lc1 gl = Some vidxs ->
  exists vidxss, NDopsem.values2GVs TD idxs lc2 gl = Some vidxss /\
    instantiate_gvs vidxs vidxss.
Proof.
  induction idxs; simpl; intros.
    inv H0. exists nil. simpl. auto.

    remember (getOperandValue TD v lc1 gl) as R.
    destruct R; tinv H0.
    remember (values2GVs TD idxs lc1 gl) as R1.
    destruct R1; inv H0.
    symmetry in HeqR.
    eapply instantiate_locals__getOperandValue in HeqR; eauto.
    destruct HeqR as [gvs2 [H3 H4]].
    destruct (@IHidxs l0) as [vidxss [J1 J2]]; auto.
    rewrite H3. rewrite J1. exists (gvs2 :: vidxss). simpl. split; auto.
Qed.

Definition defined_gv (gv:GenericValue) : Prop :=
match gv with
| (v,_)::_ => v <> Vundef
| _ => True
end.

Fixpoint defined_gvs (gvs:list GenericValue) : Prop :=
match gvs with
| gv::gvs' => defined_gv gv /\ defined_gvs gvs'
| nil => True
end.

Lemma GV2ptr__defined_gv : forall TD sz ptr v, 
  GV2ptr TD sz ptr = Some v -> defined_gv ptr.
Proof.
  intros.  
  unfold GV2ptr in H.
  destruct ptr; tinv H.
  destruct p.
  destruct v0; tinv H.
  destruct ptr; inv H.
  simpl. congruence.
Qed.

Lemma defined_gv__instantiate_gv : forall gv gvs,
  defined_gv gv -> instantiate_gv gv gvs -> gv @ gvs.
Proof.
  destruct gv; simpl; intros.
    apply Extensionality_Ensembles in H0. subst. 
    constructor.

    destruct p.
    destruct v; try solve [
      contradict H; auto |
      apply Extensionality_Ensembles in H0; subst; constructor
    ].
Qed.      

Lemma defined_gv__same_singleton : forall gv gvs,
  defined_gv gv -> instantiate_gv gv gvs -> (Singleton GenericValue gv) = gvs.
Proof.
  destruct gv; simpl; intros.
    apply Extensionality_Ensembles in H0. auto.

    destruct p.
    destruct v; try solve [
      contradict H; auto |
      apply Extensionality_Ensembles in H0; auto
    ].
Qed.      

Lemma GV2int__defined_gv : forall TD sz gv v, 
  GV2int TD sz gv = Some v -> defined_gv gv.
Proof.
  intros.  
  unfold GV2int in H.
  destruct gv; tinv H.
  destruct p.
  destruct v0; tinv H.
  destruct gv; inv H.
  simpl. congruence.
Qed.

Lemma GVs2Nats__defined_gvs : forall TD vidxs idxs, 
  GVs2Nats TD vidxs = Some idxs -> defined_gvs vidxs.
Proof.
  induction vidxs; simpl; intros; auto.
  
  remember (GV2int TD Size.ThirtyTwo a) as R.
  destruct R; tinv H.
  remember (GVs2Nats TD vidxs) as R1.
  destruct R1; inv H.
  symmetry in HeqR.
  apply GV2int__defined_gv in HeqR.
  split; eauto.
Qed.

Lemma defined_gvs__instantiate_gvs : forall gv gvs,
  defined_gvs gv -> instantiate_gvs gv gvs -> gv @@ gvs.
Proof.
  induction gv; intros.
    destruct gvs; inv H0.
    simpl. auto.

    simpl in H0.
    destruct gvs; inv H0.
    simpl. simpl in H. destruct H.
    apply defined_gv__instantiate_gv in H1; auto.
Qed.

Fixpoint singletons (l1 : list GenericValue) (l2 : list GVs) :=
match l1, l2 with
| nil, nil => True
| gv1::l1', gvs2::l2' => (Singleton GenericValue gv1) = gvs2 /\ 
                            singletons l1' l2'
| _, _ => False
end.

Lemma defined_gvs__same_singleton : forall gv gvs,
  defined_gvs gv -> instantiate_gvs gv gvs -> singletons gv gvs.
Proof.
  induction gv; intros.
    destruct gvs; inv H0.
    simpl. auto.

    simpl in H0.
    destruct gvs; inv H0.
    simpl. simpl in H. destruct H.
    apply defined_gv__same_singleton in H1; auto.
Qed.

Lemma singletons_spec : forall gv1 gvs gv2,
  singletons gv1 gvs -> gv2 @@ gvs -> gv1 = gv2.
Proof.
  induction gv1; simpl; intros.
    destruct gvs; inv H.
    destruct gv2; inv H0; auto.

    destruct gvs; inv H.
    destruct gv2; simpl in H0; inv H0.
    inv H. eapply IHgv1 in H2; eauto.
    subst. auto.
Qed.

Lemma GEP_is_total : forall TD t mp vidxs inbounds0,
  exists mp', LLVMgv.GEP TD t mp vidxs inbounds0 = ret mp'.
Proof.
  intros. unfold LLVMgv.GEP. 
  destruct (GV2ptr TD (getPointerSize TD) mp); eauto.
  destruct (GVs2Nats TD vidxs); eauto.
  destruct (mgep TD t v l0); eauto.
Qed.

Lemma instantiate_gvs__inhabited : forall gv gvs,
  instantiate_gvs gv gvs -> exists gv1, gv1 @@ gvs.
Proof.
  induction gv; simpl in *; intros.
    destruct gvs; inv H.
    exists nil. simpl. auto.

    destruct gvs; inv H.
    destruct (@IHgv gvs) as [gv1 J]; auto.
    apply instantiate_gv__inhabited in H0.
    inv H0.
    exists (x::gv1). simpl. auto.
Qed.    

Lemma instantiate_locals__GEP_helper : forall vidxs vidxss mp1 mps2 TD t
  inbounds (Hinst1 : instantiate_gvs vidxs vidxss)
  (Hinst2 : instantiate_gv mp1 mps2),
   Inhabited GenericValue
     (fun gv : GenericValue =>
      exists ma : GenericValue,
        exists vidxs0 : list GenericValue, exists gv',
          ma @ mps2 /\
          vidxs0 @@ vidxss /\ GEP TD t ma vidxs0 inbounds = ret gv' /\
          gv @ $ gv' $ ).
Proof.
  intros.
  apply instantiate_gvs__inhabited in Hinst1. destruct Hinst1 as [gv1 Hinst1].
  apply instantiate_gv__inhabited in Hinst2. inv Hinst2.
  destruct (@GEP_is_total TD t x gv1 inbounds0) as [gv2 J].
  assert (J1:=@gv2gvs__inhabited gv2). inv J1.
  exists x0. unfold Ensembles.In. exists x. exists gv1. exists gv2.
  split; auto. 
Qed.  

Lemma instantiate_locals__GEP : forall TD t mp1 mp1' vidxs vidxss inbounds mps2,
  instantiate_gvs vidxs vidxss ->
  instantiate_gv mp1 mps2 ->
  GEP TD t mp1 vidxs inbounds = Some mp1' ->
  exists mps2', NDopsem.GEP TD t mps2 vidxss inbounds = Some mps2' /\ 
    instantiate_gv mp1' mps2'.
Proof.
  intros TD t mp1 mp1' vidxs vidxss inbounds mps2 Hinst1 Hinst2 Hgep.
  unfold NDopsem.GEP.
  exists (fun gv : GenericValue =>
        exists ma : GenericValue,
          exists vidxs0 : list GenericValue,
            exists gv' : GenericValue,
              ma @ mps2 /\
              vidxs0 @@ vidxss /\
              GEP TD t ma vidxs0 inbounds = ret gv' /\ gv @ $ gv' $).
  split; auto. 
  unfold GEP in Hgep.
  remember (GV2ptr TD (getPointerSize TD) mp1) as R.
  destruct R; try solve [inv Hgep; simpl; 
      eapply instantiate_locals__GEP_helper; eauto].
  remember (GVs2Nats TD vidxs) as R1.
  destruct R1; try solve [inv Hgep; simpl; 
      eapply instantiate_locals__GEP_helper; eauto].
  remember (mgep TD t v l0) as R2.
  destruct R2; try solve [inv Hgep; simpl; 
      eapply instantiate_locals__GEP_helper; eauto].
  inv Hgep. 
  unfold mgep in HeqR2.
  destruct v; tinv HeqR2.
  destruct l0; tinv HeqR2.
  remember (mgetoffset TD (typ_array 0%nat t) (z :: l0)) as R3.
  destruct R3 as [[o ?]|]; inv HeqR2.
  unfold ptr2GV, val2GV. simpl.
  symmetry in HeqR.
  assert (J:=HeqR).
  apply GV2ptr__defined_gv in J. 
  apply defined_gv__same_singleton in Hinst2; auto. subst.
  symmetry in HeqR1.
  assert (J1:=HeqR1).
  apply GVs2Nats__defined_gvs in J1. 
  assert (J9:=Hinst1).
  apply defined_gvs__instantiate_gvs in J9; auto. 
  apply defined_gvs__same_singleton in Hinst1; auto. 
  unfold Same_set, Included.
  split; intros.
    inv H. unfold Ensembles.In.
    exists mp1.
    exists vidxs. 
    exists ((Vptr b (Int.add 31 i0 o), AST.Mint (getPointerSize TD - 1)) :: nil).
    repeat (split; auto).
    unfold GEP. rewrite HeqR. rewrite HeqR1. unfold mgep.
    rewrite <- HeqR3. unfold ptr2GV, val2GV. auto.

    inv H. destruct H0 as [A [B [J1' [J2 [J3 J4]]]]].
    eapply singletons_spec in Hinst1; eauto. subst.
    inv J1'. unfold GEP in J3.
    rewrite HeqR in J3. rewrite HeqR1 in J3. unfold mgep in J3.
    rewrite <- HeqR3 in J3. inv J3. inv J4.
    unfold ptr2GV, val2GV. 
    unfold Ensembles.In. constructor.
Qed.

Lemma mget'_is_total : forall TD ofs t' x, 
  exists z, mget' TD ofs t' x = Some z.
Proof.
  intros.
  unfold mget'. unfold mget.
  destruct (getTypeStoreSize TD t'); simpl; eauto.
  destruct (splitGenericValue x (Int.signed 31 ofs)); eauto.
  destruct p.  
  destruct (splitGenericValue g0 (Z_of_nat n)); eauto.
  destruct p. eauto.
Qed.

Lemma instantiate_gv__mget'__helper : forall x xs TD ofs t'
  (H0 : instantiate_gv x xs),
   Inhabited GenericValue
     (fun gv2 : GenericValue =>
      exists gv1 : GenericValue,
        exists gv2' : GenericValue,
          gv1 @ xs /\ mget' TD ofs t' gv1 = ret gv2' /\ gv2 @ $ gv2' $).
Proof.
  intros.
  apply instantiate_gv__inhabited in H0. inv H0.
  destruct (@mget'_is_total TD ofs t' x0) as [z J].
  assert (J1:=@gv2gvs__inhabited z). inv J1.
  exists x1. unfold Ensembles.In. exists x0. exists z.
  split; auto. 
Qed.

Lemma defined_gv__spec1 : forall gv,
  defined_gv gv -> gv @ ($ gv $).
Proof.
  destruct gv; simpl; intros.
    unfold Ensembles.In. constructor.

    destruct p.
    destruct v; try solve [
      contradict H; auto |
      unfold Ensembles.In; constructor
    ].
Qed.      

Lemma defined_gv__spec2 : forall gv,
  defined_gv gv -> $ gv $ = Singleton _ gv.
Proof.
  destruct gv; simpl; intros; auto.
    destruct p.
    destruct v; try solve [
      contradict H; auto | auto
    ].
Qed.      

Lemma instantiate_gv__mget'__helper2 : forall TD ofs t' x gv,
  mget' TD ofs t' x = ret gv ->
  defined_gv gv ->
   Same_set GenericValue (Singleton GenericValue gv)
     (fun gv2 : GenericValue =>
      exists gv1 : GenericValue, exists gv2' : GenericValue,
        gv1 @ Singleton GenericValue x /\
        mget' TD ofs t' gv1 = ret gv2' /\ gv2 @ $ gv2' $).
Proof.
  intros.
    unfold Same_set, Included.    
    split; intros.
      inv H1. unfold Ensembles.In. exists x. exists x0.
      split; auto. constructor. split; auto. apply defined_gv__spec1; auto.

      inv H1. destruct H2 as [A [J1 [J2 J3]]].
      inv J1. rewrite J2 in H. inv H. 
      apply defined_gv__spec2 in H0. rewrite H0 in J3. inv J3. 
      unfold Ensembles.In. constructor.
Qed.  

Lemma instantiate_gv__mget'__helper3 : forall TD ofs t' x z xs n
  (HeqR : ret n = getTypeStoreSize TD t')
  (g : GenericValue)
  (gvr : GenericValue)
  (HeqR1 : ret (g, gvr) = splitGenericValue x (Int.signed 31 ofs))
  (gvrl : GenericValue)
  (H0 : Same_set _ (Singleton _ x) xs)
  (HeqR2 : ret (z, gvrl) = splitGenericValue gvr (Z_of_nat n)),
   instantiate_gv z
     (fun gv2 : GenericValue =>
      exists gv1 : GenericValue, exists gv2' : GenericValue,
        gv1 @ xs /\ mget' TD ofs t' gv1 = ret gv2' /\ gv2 @ $ gv2'$).
Proof.
  intros.
  assert (mget' TD ofs t' x = ret z) as J.
    unfold mget'. unfold mget.
    rewrite <- HeqR. simpl.
    rewrite <- HeqR1. rewrite <- HeqR2. split; auto. 
  apply Extensionality_Ensembles in H0. subst. 
  assert (J1:=@gv2gvs__inhabited z). inv J1.
  destruct z; simpl.
    eapply instantiate_gv__mget'__helper2; simpl; eauto.

    destruct p.
    destruct v.
      destruct z.
        exists x0. unfold Ensembles.In. exists x. exists ((Vundef, m) :: nil).
        split. constructor. split; auto.

        simpl in H. inv H.
        unfold Same_set, Included.    
        split; intros.
          inv H. unfold Ensembles.In. exists x. exists ((Vundef, m) :: p :: z).
          split. constructor. simpl. split; auto. constructor.

          inv H. destruct H0 as [A [J1 [J2 J3]]].
          inv J1. rewrite J2 in J. inv J. inv J3.  constructor.
      eapply instantiate_gv__mget'__helper2; simpl; 
        try solve [eauto | congruence].
      eapply instantiate_gv__mget'__helper2; simpl; 
        try solve [eauto | congruence].
      eapply instantiate_gv__mget'__helper2; simpl; 
        try solve [eauto | congruence].
      eapply instantiate_gv__mget'__helper2; simpl; 
        try solve [eauto | congruence].
Qed.

Lemma instantiate_gv__mget' : forall TD ofs t' x z xs,
  mget' TD ofs t' x = Some z ->
  defined_gv x ->
  instantiate_gv x xs ->
  instantiate_gv z (lift_op1 (mget' TD ofs t') xs).
Proof.
  intros TD ofs t' x z xs H G H0. unfold lift_op1. 
  unfold mget', mget in H.
Opaque mget'. 
  remember (getTypeStoreSize TD t') as R.
  destruct R; try solve [
    destruct t'; try solve [
      inv H; simpl; eapply instantiate_gv__mget'__helper; eauto |
      destruct f; try solve [inv H; simpl; 
        eapply instantiate_gv__mget'__helper; eauto]
    ]
  ].
  simpl in H.
  remember (splitGenericValue x (Int.signed 31 ofs)) as R1.
  destruct R1 as [[? gvr]|]; try solve [
    destruct t'; try solve [
      inv H; simpl; eapply instantiate_gv__mget'__helper; eauto |
      destruct f; try solve [inv H; simpl; 
        eapply instantiate_gv__mget'__helper; eauto]
    ]
  ].
  remember (splitGenericValue gvr (Z_of_nat n)) as R2.
  destruct R2 as [[? gvrl]|]; try solve [
    destruct t'; try solve [
      inv H; simpl; eapply instantiate_gv__mget'__helper; eauto |
      destruct f; try solve [inv H; simpl; 
        eapply instantiate_gv__mget'__helper; eauto]
    ]
  ].
  inv H. 

  destruct x.
    eapply instantiate_gv__mget'__helper3; eauto.
    destruct p.
    destruct v.
      destruct x.      
        simpl in G. contradict G; auto.
        eapply instantiate_gv__mget'__helper3; eauto.
      eapply instantiate_gv__mget'__helper3; eauto.
      eapply instantiate_gv__mget'__helper3; eauto.
      eapply instantiate_gv__mget'__helper3; eauto.
      eapply instantiate_gv__mget'__helper3; eauto.

Transparent mget'. 
Qed.    

Lemma instantiate_locals__extractGenericValue : forall TD lc1 lc2 t gv2
    cidxs gv1 gvs1,
  instantiate_locals lc1 lc2 -> 
  instantiate_gv gv1 gvs1 ->
  extractGenericValue TD t gv1 cidxs = Some gv2 ->
  defined_gv gv1 ->
  exists gvs2, NDopsem.extractGenericValue TD t gvs1 cidxs = Some gvs2 
    /\ instantiate_gv gv2 gvs2.
Proof.
  intros.
  unfold extractGenericValue in H1.
  unfold NDopsem.extractGenericValue.
  destruct (intConsts2Nats TD cidxs); inv H1.
    destruct (mgetoffset TD t l0) as [[]|]; inv H4.
      exists (lift_op1 (mget' TD i0 t0) gvs1).
      split; auto.
        eapply instantiate_gv__mget'; eauto.
      exists ($ uninits 1 $). split; auto using instantiate_gv__gv2gvs.
    exists ($ uninits 1 $). split; auto using instantiate_gv__gv2gvs.
Qed.

Lemma mset'_is_total : forall (TD : TargetData) (ofs : int32) (t1 t2 : typ) 
  (x y: GenericValue),
  exists z : GenericValue, mset' TD ofs t1 t2 x y = ret z.
Proof.
  intros.
  unfold mset'.
  destruct (mset TD x ofs t2 y); eauto.
Qed.  

Lemma instantiate_gv__mset'__helper : forall x xs y ys TD ofs t1 t2
  (H0 : instantiate_gv x xs) (H1 : instantiate_gv y ys),
   Inhabited GenericValue
     (fun gv3 : GenericValue =>
      exists gv1 : GenericValue, exists gv2 : GenericValue,
        exists gv3' : GenericValue,
          gv1 @ xs /\ gv2 @ ys /\ 
          mset' TD ofs t1 t2 gv1 gv2 = ret gv3' /\ gv3 @ $ gv3' $).
Proof.
  intros.
  apply instantiate_gv__inhabited in H0. inv H0.
  apply instantiate_gv__inhabited in H1. inv H1.
  destruct (@mset'_is_total TD ofs t1 t2 x0 x1) as [z J].
  assert (J1:=@gv2gvs__inhabited z). inv J1.
  exists x2. unfold Ensembles.In. exists x0. exists x1. exists z.
  repeat (split; auto). 
Qed.

Lemma instantiate_gv__mset' : forall TD ofs t1 t2 x y z xs ys,
  mset' TD ofs t1 t2 x y = Some z ->
  defined_gv x ->
  defined_gv y ->
  instantiate_gv x xs ->
  instantiate_gv y ys ->
  instantiate_gv z (lift_op2 (mset' TD ofs t1 t2) xs ys).
Proof.
  intros TD ofs t1 t2 x y z xs ys H G G' H0 H1. unfold lift_op2. 
  unfold mset', mset in H.
Opaque mset'. 
  remember (getTypeStoreSize TD t2) as R.
  destruct R; try solve [
    destruct t1; try solve [
      inv H; simpl; eapply instantiate_gv__mset'__helper; eauto |
      destruct f; try solve [inv H; simpl; 
        eapply instantiate_gv__mset'__helper; eauto]
    ]
  ].
  simpl in H.
  remember (n =n= length y) as R0.
  destruct R0; try solve [
    destruct t1; try solve [
      inv H; simpl; eapply instantiate_gv__mset'__helper; eauto |
      destruct f; try solve [inv H; simpl; 
        eapply instantiate_gv__mset'__helper; eauto]
    ]
  ].
  remember (splitGenericValue x (Int.signed 31 ofs)) as R1.
  destruct R1 as [[? gvr]|]; try solve [
    destruct t1; try solve [
      inv H; simpl; eapply instantiate_gv__mset'__helper; eauto |
      destruct f; try solve [inv H; simpl; 
        eapply instantiate_gv__mset'__helper; eauto]
    ]
  ].
  remember (splitGenericValue gvr (Z_of_nat n)) as R2.
  destruct R2 as [[? gvrl]|]; try solve [
    destruct t1; try solve [
      inv H; simpl; eapply instantiate_gv__mset'__helper; eauto |
      destruct f; try solve [inv H; simpl; 
        eapply instantiate_gv__mset'__helper; eauto]
    ]
  ].
  inv H. 
  apply defined_gv__same_singleton in H0; auto. subst.
  apply defined_gv__same_singleton in H1; auto. subst.
Transparent mset'. 
 
  assert (mset' TD ofs t1 t2 x y = Some (g ++ y ++ gvrl)) as J.
    unfold mset', mset.
    rewrite <- HeqR. simpl. rewrite <- HeqR0. rewrite <- HeqR1. rewrite <- HeqR2.
    auto.
  assert (J1:=@gv2gvs__inhabited (g ++ y ++ gvrl)). inv J1.
  destruct (g ++ y ++ gvrl).
    simpl. unfold Same_set, Included.
    inv H.
    split; intros.
      inv H. unfold Ensembles.In. exists x. exists y. exists nil. simpl.
      split. constructor. split. constructor. split; auto. constructor.

      inv H. destruct H0 as [A [B [J1 [J2 [J3 J4]]]]]. inv J1. inv J2. 
      rewrite J3 in J. inv J. inv J4. unfold Ensembles.In. constructor.
    destruct p.
    destruct v.
      destruct l0.
        simpl. exists x0. unfold Ensembles.In. exists x. exists y.
        exists ((Vundef, m) :: nil). split. constructor. split. constructor.
        split; auto.

    simpl. unfold Same_set, Included.
    inv H.
    split; intros.
      inv H. unfold Ensembles.In. exists x. exists y. 
      exists ((Vundef, m) :: p :: l0). simpl.
      split. constructor. split. constructor. split; auto. constructor.

      inv H. destruct H0 as [A [B [J1 [J2 [J3 J4]]]]]. inv J1. inv J2. 
      rewrite J3 in J. inv J. inv J4. unfold Ensembles.In. constructor.

    simpl. unfold Same_set, Included.
    inv H.
    split; intros.
      inv H. unfold Ensembles.In. exists x. exists y. 
      exists ((Vint wz i0, m) :: l0). simpl.
      split. constructor. split. constructor. split; auto. constructor.

      inv H. destruct H0 as [A [B [J1 [J2 [J3 J4]]]]]. inv J1. inv J2. 
      rewrite J3 in J. inv J. inv J4. unfold Ensembles.In. constructor.

    simpl. unfold Same_set, Included.
    inv H.
    split; intros.
      inv H. unfold Ensembles.In. exists x. exists y. 
      exists ((Vfloat f, m) :: l0). simpl.
      split. constructor. split. constructor. split; auto. constructor.

      inv H. destruct H0 as [A [B [J1 [J2 [J3 J4]]]]]. inv J1. inv J2. 
      rewrite J3 in J. inv J. inv J4. unfold Ensembles.In. constructor.

    simpl. unfold Same_set, Included.
    inv H.
    split; intros.
      inv H. unfold Ensembles.In. exists x. exists y. 
      exists ((Vptr b i0, m) :: l0). simpl.
      split. constructor. split. constructor. split; auto. constructor.

      inv H. destruct H0 as [A [B [J1 [J2 [J3 J4]]]]]. inv J1. inv J2. 
      rewrite J3 in J. inv J. inv J4. unfold Ensembles.In. constructor.

    simpl. unfold Same_set, Included.
    inv H.
    split; intros.
      inv H. unfold Ensembles.In. exists x. exists y. 
      exists ((Vinttoptr i0, m) :: l0). simpl.
      split. constructor. split. constructor. split; auto. constructor.

      inv H. destruct H0 as [A [B [J1 [J2 [J3 J4]]]]]. inv J1. inv J2. 
      rewrite J3 in J. inv J. inv J4. unfold Ensembles.In. constructor.
Qed.    

Lemma instantiate_locals__insertGenericValue : forall TD lc1 lc2 t1 t2 gv2 
    cidxs gv1 gvs1 gvs2 gv3,
  instantiate_locals lc1 lc2 -> 
  instantiate_gv gv1 gvs1 ->
  instantiate_gv gv2 gvs2 ->
  insertGenericValue TD t1 gv1 cidxs t2 gv2 = Some gv3 ->
  defined_gv gv1 ->
  defined_gv gv2 ->
  exists gvs3, NDopsem.insertGenericValue TD t1 gvs1 cidxs t2 gvs2 = Some gvs3
    /\ instantiate_gv gv3 gvs3.
Proof.
  intros.
  unfold insertGenericValue in H2.
  unfold NDopsem.insertGenericValue.
  destruct (intConsts2Nats TD cidxs); inv H2.
    destruct (mgetoffset TD t1 l0) as [[]|]; inv H6.
      exists (lift_op2 (mset' TD i0 t1 t2) gvs1 gvs2).
      split; auto.
        eapply instantiate_gv__mset'; eauto.
      exists ($ gundef t1 $). split; auto using instantiate_gv__gv2gvs.
    exists ($ gundef t1 $). split; auto using instantiate_gv__gv2gvs.
Qed.

Lemma mcast_is_total : forall TD cop0 t1 t2 x, 
  exists z, mcast TD cop0 t1 t2 x = Some z.
Proof.
  intros.
  unfold mcast, mbitcast.
  destruct cop0; destruct t1; destruct t2; eauto.
Qed.

Lemma instantiate_gv__mcast__helper : forall x xs TD op t1 t2
  (H0 : instantiate_gv x xs),
   Inhabited GenericValue
     (fun gv2 : GenericValue =>
      exists gv1 : GenericValue,
        exists gv2' : GenericValue,
            gv1 @ xs /\ mcast TD op t1 t2 gv1 = ret gv2' /\ gv2 @ $ gv2' $).
Proof.
  intros.
  apply instantiate_gv__inhabited in H0. inv H0.
  destruct (@mcast_is_total TD op t1 t2 x0) as [z J].
  assert (J1:=@gv2gvs__inhabited z). inv J1.
  exists x1. unfold Ensembles.In. exists x0. exists z.
  split; auto. 
Qed.

Lemma instantiate_gv__mcast__helper2 : forall z xs
  (H0 : instantiate_gv z xs),
   instantiate_gv z
     (fun gv2 : GenericValue =>
      exists gv1 : GenericValue,
        exists gv2' : GenericValue,
          gv1 @ xs /\ ret gv1 = ret gv2' /\ gv2 @ $ gv2' $).
Proof.
  intros.
  destruct z.
    apply Extensionality_Ensembles in H0. subst. 
    simpl. 
    unfold Same_set, Included.
    split; intros.
      inv H. unfold Ensembles.In. exists nil. exists nil. simpl.
      split. constructor. split; auto. constructor. 

      inv H. destruct H0 as [A [J1 [J2 J3]]]. inv J1. inv J2. inv J3.
      unfold Ensembles.In. constructor.

    destruct p. 
    destruct v; simpl in *.
      destruct z.
        inv H0.  
        assert (J:=@gv2gvs__inhabited x). inv J.
        exists x0. unfold Ensembles.In. exists x. exists x.
        split; auto.
             
        apply Extensionality_Ensembles in H0. subst. 
        unfold Same_set, Included.
        split; intros.
          inv H. unfold Ensembles.In. exists ((Vundef, m) :: p :: z). 
          exists ((Vundef, m) :: p :: z). simpl.
          split. constructor. split; auto. constructor. 

          inv H. destruct H0 as [A [J1 [J2 J3]]]. inv J1. inv J2. inv J3.
          constructor.
   
     apply Extensionality_Ensembles in H0. subst. 
     unfold Same_set, Included.
     split; intros.
        inv H. unfold Ensembles.In. exists ((Vint wz i0, m) :: z). 
        exists ((Vint wz i0, m) :: z). simpl.
        split. constructor. split; auto. constructor. 

        inv H. destruct H0 as [A [J1 [J2 J3]]]. inv J1. inv J2. inv J3.
        constructor.

     apply Extensionality_Ensembles in H0. subst. 
     unfold Same_set, Included.
     split; intros.
        inv H. unfold Ensembles.In. exists ((Vfloat f, m) :: z). 
        exists ((Vfloat f, m) :: z). simpl.
        split. constructor. split; auto. constructor. 

        inv H. destruct H0 as [A [J1 [J2 J3]]]. inv J1. inv J2. inv J3.
        constructor.

     apply Extensionality_Ensembles in H0. subst. 
     unfold Same_set, Included.
     split; intros.
        inv H. unfold Ensembles.In. exists ((Vptr b i0, m) :: z). 
        exists ((Vptr b i0, m) :: z). simpl.
        split. constructor. split; auto. constructor. 

        inv H. destruct H0 as [A [J1 [J2 J3]]]. inv J1. inv J2. inv J3.
        constructor.

     apply Extensionality_Ensembles in H0. subst. 
     unfold Same_set, Included.
     split; intros.
        inv H. unfold Ensembles.In. exists ((Vinttoptr i0, m) :: z). 
        exists ((Vinttoptr i0, m) :: z). simpl.
        split. constructor. split; auto. constructor. 

        inv H. destruct H0 as [A [J1 [J2 J3]]]. inv J1. inv J2. inv J3.
        constructor.
Qed.

Lemma instantiate_gv__mcast : forall TD cop0 t1 t2 x z xs,
  mcast TD cop0 t1 t2 x = Some z ->
  instantiate_gv x xs ->
  instantiate_gv z (lift_op1 (mcast TD cop0 t1 t2) xs).
Proof.
  intros. unfold lift_op1. 
  unfold mcast, mbitcast in H.
Opaque mcast. 
  destruct cop0; try solve [inv H; simpl; 
      eapply instantiate_gv__mcast__helper; eauto];
    destruct t1; destruct t2; try solve [    
      inv H; destruct f; 
        try solve [simpl; eapply instantiate_gv__mcast__helper; eauto] |
      inv H; destruct f0; 
        try solve [simpl; eapply instantiate_gv__mcast__helper; eauto] |
      inv H; try solve [simpl; eapply instantiate_gv__mcast__helper; eauto]
    ].
Transparent mcast. 
    inv H; unfold mcast, mbitcast; apply instantiate_gv__mcast__helper2; auto.
    inv H; unfold mcast, mbitcast; apply instantiate_gv__mcast__helper2; auto.
    inv H; unfold mcast, mbitcast; apply instantiate_gv__mcast__helper2; auto.
    inv H; unfold mcast, mbitcast; apply instantiate_gv__mcast__helper2; auto.
    inv H; unfold mcast, mbitcast; apply instantiate_gv__mcast__helper2; auto.
    inv H; unfold mcast, mbitcast; apply instantiate_gv__mcast__helper2; auto.
    inv H; unfold mcast, mbitcast; apply instantiate_gv__mcast__helper2; auto.
    inv H; unfold mcast, mbitcast; apply instantiate_gv__mcast__helper2; auto.
    inv H; unfold mcast, mbitcast; apply instantiate_gv__mcast__helper2; auto.
    inv H; unfold mcast, mbitcast; apply instantiate_gv__mcast__helper2; auto.
Qed.    

Lemma instantiate_locals__CAST : forall TD lc1 lc2 gl t1 v1 t2 gv2 castop0,
  instantiate_locals lc1 lc2 -> 
  CAST TD lc1 gl castop0 t1 v1 t2 = Some gv2 ->
  exists gvs2', NDopsem.CAST TD lc2 gl castop0 t1 v1 t2 = Some gvs2' 
    /\ instantiate_gv gv2 gvs2'.
Proof.
  intros.
  apply CAST_inversion in H0.
  destruct H0 as [gv1 [J1 J2]].
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  unfold NDopsem.CAST.
  rewrite H1.
  exists (lift_op1 (mcast TD castop0 t1 t2) gvs1).
  split; eauto using instantiate_gv__mcast.
Qed.

Lemma mtrunc_is_total : forall TD top0 t1 t2 x, 
  exists z, mtrunc TD top0 t1 t2 x = Some z.
Proof.
  intros.
  unfold mtrunc.
  destruct (GV2val TD x); eauto.
  destruct v; destruct t1; destruct t2; eauto.
  destruct (floating_point_order f1 f0); eauto.
  destruct f1; eauto.
Qed.

Lemma instantiate_gv__mtrunc__helper : forall x xs TD op t1 t2
  (H0 : instantiate_gv x xs),
   Inhabited GenericValue
     (fun gv2 : GenericValue =>
      exists gv1 : GenericValue,
        exists gv2' : GenericValue,
            gv1 @ xs /\ mtrunc TD op t1 t2 gv1 = ret gv2' /\ gv2 @ $ gv2' $).
Proof.
  intros.
  apply instantiate_gv__inhabited in H0. inv H0.
  destruct (@mtrunc_is_total TD op t1 t2 x0) as [z J].
  assert (J1:=@gv2gvs__inhabited z). inv J1.
  exists x1. unfold Ensembles.In. exists x0. exists z.
  split; auto. 
Qed.

Lemma instantiate_gv__mtrunc : forall TD top0 t1 t2 x z xs,
  mtrunc TD top0 t1 t2 x = Some z ->
  instantiate_gv x xs ->
  instantiate_gv z (lift_op1 (mtrunc TD top0 t1 t2) xs).
Proof.
  intros. unfold lift_op1. 
  unfold mtrunc in H.
Opaque mtrunc. 
  destruct x; try solve [
    destruct t2; try solve [
      inv H; simpl; eapply instantiate_gv__mtrunc__helper; eauto |
      destruct f; try solve [inv H; simpl; 
        eapply instantiate_gv__mtrunc__helper; eauto]
    ]
  ].
  destruct p.
  destruct x; try solve [
    destruct t2; try solve [
      inv H; simpl; eapply instantiate_gv__mtrunc__helper; eauto |
      destruct f; try solve [inv H; simpl; 
        eapply instantiate_gv__mtrunc__helper; eauto]
    ]
  ].
  simpl in H.
  destruct v; try solve [
    destruct t2; try solve [
      inv H; simpl; eapply instantiate_gv__mtrunc__helper; eauto |
      destruct f; try solve [inv H; simpl; 
        eapply instantiate_gv__mtrunc__helper; eauto]
    ] |
    destruct t1; destruct t2; try solve [
      inv H; simpl; eapply instantiate_gv__mtrunc__helper; eauto |
      destruct f0; try solve [inv H; simpl; 
        eapply instantiate_gv__mtrunc__helper; eauto]
    ]
  ].

    destruct t1; destruct t2; try solve [
      inv H; simpl; eapply instantiate_gv__mtrunc__helper; eauto |
      destruct f; try solve [inv H; simpl; 
        eapply instantiate_gv__mtrunc__helper; eauto] |
      destruct f0; try solve [inv H; simpl; 
        eapply instantiate_gv__mtrunc__helper; eauto]
    ]. 

Transparent mtrunc. 
      inv H.
      unfold val2GV.
      destruct (le_lt_dec wz s0); simpl.
        eapply instantiate_gv__mtrunc__helper; eauto.

        apply Extensionality_Ensembles in H0. subst. 
        unfold Same_set, Included.
        split; intros.
          inv H. unfold Ensembles.In.
          exists ((Vint wz i0, m) :: nil). 
          unfold mtrunc. simpl.
          destruct (le_lt_dec wz s0); simpl.
            contradict l1. omega.
            unfold val2GV.
            exists ((Vint s0 (Int.repr s0 (Int.unsigned wz i0)), AST.Mint s0) :: nil).                    
            simpl. split. constructor. split; auto. constructor.

          inv H. destruct H0 as [gv2' [J1 [J2 J3]]].
          inv J1. unfold mtrunc in J2. simpl in J2. inv J2.
          destruct (le_lt_dec wz s0); simpl.
            contradict l1. omega.
            unfold val2GV in J3. inv J3.
            constructor.

    destruct t1; destruct t2; try solve [
      inv H; simpl; eapply instantiate_gv__mtrunc__helper; eauto |
      destruct f0; try solve [inv H; simpl; 
        eapply instantiate_gv__mtrunc__helper; eauto]
    ]. 

      remember (floating_point_order f1 f0) as R.
      destruct R; destruct f1; try solve [
        inv H; simpl; eapply instantiate_gv__mtrunc__helper; eauto].
      apply Extensionality_Ensembles in H0. subst. inv H.
      unfold val2GV. simpl.
      unfold Same_set, Included.
      split; intros.
        inv H. unfold Ensembles.In.
        exists ((Vfloat f, m) :: nil). 
        unfold mtrunc. simpl. rewrite <- HeqR.
        unfold val2GV.
        exists ((Vfloat f, AST.Mfloat32) :: nil).                    
        simpl. split. constructor. split; auto. constructor.

        inv H. destruct H0 as [gv2' [J1 [J2 J3]]].
        inv J1. unfold mtrunc in J2. simpl in J2. 
        rewrite <- HeqR in J2. inv J2. inv J3.
        constructor.

     inv H.
     apply Extensionality_Ensembles in H0. subst. simpl.
     unfold Same_set, Included.
     split; intros.
       inv H. unfold Ensembles.In.
       exists ((Vfloat f, m) :: nil). 
       unfold mtrunc. simpl. rewrite <- HeqR.
       unfold val2GV.
       exists ((Vfloat f, AST.Mfloat64) :: nil).                    
       simpl. split. constructor. split; auto. constructor.

       inv H. destruct H0 as [gv2' [J1 [J2 J3]]].
       inv J1. unfold mtrunc in J2. simpl in J2. 
       rewrite <- HeqR in J2. inv J2. inv J3.
       constructor.     
Qed.    

Lemma instantiate_locals__TRUNC : forall TD lc1 lc2 gl t1 v1 t2 gv2 top0,
  instantiate_locals lc1 lc2 -> 
  TRUNC TD lc1 gl top0 t1 v1 t2 = Some gv2 ->
  exists gvs2', NDopsem.TRUNC TD lc2 gl top0 t1 v1 t2 = Some gvs2' 
    /\ instantiate_gv gv2 gvs2'.
Proof.
  intros.
  apply TRUNC_inversion in H0.
  destruct H0 as [gv1 [J1 J2]].
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  unfold NDopsem.TRUNC.
  rewrite H1.
  exists (lift_op1 (mtrunc TD top0 t1 t2) gvs1).
  split; eauto using instantiate_gv__mtrunc.
Qed.

Lemma mext_is_total : forall TD eop0 t1 t2 x, 
  exists z, mext TD eop0 t1 t2 x = Some z.
Proof.
  intros.
  unfold mext.
  destruct (GV2val TD x); eauto.
  destruct t1; destruct t2; try solve [
    destruct v; destruct eop0; 
      try solve [eauto | destruct (floating_point_order f f0); eauto]
  ].

  destruct t1; destruct t2; 
    try solve [destruct (floating_point_order f f0); eauto | eauto].
Qed.

Lemma instantiate_gv__mext__helper : forall x xs TD op t1 t2
  (H0 : instantiate_gv x xs),
   Inhabited GenericValue
     (fun gv2 : GenericValue =>
      exists gv1 : GenericValue,
        exists gv2' : GenericValue,
            gv1 @ xs /\ mext TD op t1 t2 gv1 = ret gv2' /\ gv2 @ $ gv2' $).
Proof.
  intros.
  apply instantiate_gv__inhabited in H0. inv H0.
  destruct (@mext_is_total TD op t1 t2 x0) as [z J].
  assert (J1:=@gv2gvs__inhabited z). inv J1.
  exists x1. unfold Ensembles.In. exists x0. exists z.
  split; auto. 
Qed.

Lemma instantiate_gv__mext : forall TD eop0 t1 t2 x z xs,
  mext TD eop0 t1 t2 x = Some z ->
  instantiate_gv x xs ->
  instantiate_gv z (lift_op1 (mext TD eop0 t1 t2) xs).
Proof.
  intros. unfold lift_op1. 
  unfold mext in H.
Opaque mext. 
  destruct t1; destruct t2; try solve [
    inv H; simpl; eapply instantiate_gv__mext__helper; eauto |
    inv H; destruct f; simpl; eapply instantiate_gv__mext__helper; eauto
  ].

  destruct x; try solve 
    [inv H; simpl; eapply instantiate_gv__mext__helper; eauto].
  destruct p.
  destruct x; try solve 
    [inv H; simpl; eapply instantiate_gv__mext__helper; eauto].
  destruct v; try solve 
    [inv H; simpl; eapply instantiate_gv__mext__helper; eauto].
  destruct eop0; try solve 
    [inv H; simpl; eapply instantiate_gv__mext__helper; eauto].

Transparent mext. 
    inv H.
    apply Extensionality_Ensembles in H0. subst. simpl.
    unfold Same_set, Included.
    split; intros.
      inv H. unfold Ensembles.In. 
      exists ((Vint wz i0, m) :: nil).
      exists (val2GV TD (Vint wz (Int.zero_ext wz (Size.to_Z s0) i0))
          (AST.Mint (Size.to_nat s0 - 1))).  
      split. constructor.
      unfold mext. simpl. split; auto. constructor.

      inv H. destruct H0 as [gv2' [J1 [J2 J3]]].
      inv J1. unfold mext in J2. simpl in J2. inv J2. inv J3.
      constructor.

Transparent mext. 
    inv H.
    apply Extensionality_Ensembles in H0. subst. simpl.
    unfold Same_set, Included.
    split; intros.
      inv H. unfold Ensembles.In. 
      exists ((Vint wz i0, m) :: nil).
      exists (val2GV TD (Vint wz (Int.sign_ext wz (Size.to_Z s0) i0))
          (AST.Mint (Size.to_nat s0 - 1))).  
      split. constructor.
      unfold mext. simpl. split; auto. constructor.

      inv H. destruct H0 as [gv2' [J1 [J2 J3]]].
      inv J1. unfold mext in J2. simpl in J2. inv J2. inv J3.
      constructor.

  remember (floating_point_order f f0) as R.
  destruct R; simpl; try solve [
    destruct f0; inv H; simpl; eapply instantiate_gv__mext__helper; eauto
  ].
  destruct x; try solve 
    [inv H; destruct f0; simpl; eapply instantiate_gv__mext__helper; eauto].
  destruct p.
  destruct x; try solve 
    [inv H; destruct f0; simpl; eapply instantiate_gv__mext__helper; eauto].
  destruct v; try solve 
    [inv H; destruct f0; simpl; eapply instantiate_gv__mext__helper; eauto].
  destruct eop0; try solve 
    [inv H; destruct f0; simpl; eapply instantiate_gv__mext__helper; eauto].

Transparent mext. 
    inv H.
    apply Extensionality_Ensembles in H0. subst. simpl.
    unfold Same_set, Included.
    split; intros.
      inv H. unfold Ensembles.In. 
      exists ((Vfloat f1, m) :: nil).
      exists ((Vfloat f1, m) :: nil).
      split. constructor.
      unfold mext. simpl. rewrite <- HeqR. split; auto. constructor.

      inv H. destruct H0 as [gv2' [J1 [J2 J3]]].
      inv J1. unfold mext in J2. rewrite <- HeqR in J2. inv J2. inv J3.
      constructor.
Qed.    

Lemma instantiate_locals__EXT : forall TD lc1 lc2 gl t1 v1 t2 gv2 top0,
  instantiate_locals lc1 lc2 -> 
  EXT TD lc1 gl top0 t1 v1 t2 = Some gv2 ->
  exists gvs2', NDopsem.EXT TD lc2 gl top0 t1 v1 t2 = Some gvs2' 
    /\ instantiate_gv gv2 gvs2'.
Proof.
  intros.
  apply EXT_inversion in H0.
  destruct H0 as [gv1 [J1 J2]].
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  unfold NDopsem.EXT.
  rewrite H1.
  exists (lift_op1 (mext TD top0 t1 t2) gvs1).
  split; eauto using instantiate_gv__mext.
Qed.

Lemma lookupFdefViaGV_inversion : forall TD Ps gl lc fs fv f,
  lookupFdefViaGV TD Ps gl lc fs fv = Some f ->
  exists fptr, exists fn,
    getOperandValue TD fv lc gl = Some fptr /\
    lookupFdefViaGVFromFunTable fs fptr = Some fn /\
    lookupFdefViaIDFromProducts Ps fn = Some f.
Proof.
  intros.
  unfold lookupFdefViaGV in H.
  destruct (getOperandValue TD fv lc gl); tinv H.
  simpl in H. exists g.
  destruct (lookupFdefViaGVFromFunTable fs g); tinv H.
  simpl in H. exists i0. eauto.
Qed.  

Lemma lookupFdefViaPtr_inversion : forall Ps fs fptr f,
  lookupFdefViaPtr Ps fs fptr = Some f ->
  exists fn,
    lookupFdefViaGVFromFunTable fs fptr = Some fn /\
    lookupFdefViaIDFromProducts Ps fn = Some f.
Proof.
  intros.
  unfold lookupFdefViaPtr in H.
  destruct (lookupFdefViaGVFromFunTable fs fptr); tinv H.
  simpl in H. exists i0. eauto.
Qed.  

Lemma instantiate_locals__params2GVs : forall TD lc1 lc2 gl 
  (Hlc:instantiate_locals lc1 lc2) lp gvs1,
  params2GVs TD lp lc1 gl = Some gvs1 ->
  exists gvss2, NDopsem.params2GVs TD lp lc2 gl = Some gvss2 /\
    instantiate_gvs gvs1 gvss2.
Proof.
  induction lp; simpl; intros.
    inv H. exists nil. simpl. auto.

    destruct a.
    remember (getOperandValue TD v lc1 gl) as R1.
    destruct R1; tinv H.
    remember (params2GVs TD lp lc1 gl) as R2.
    destruct R2; tinv H.
    inv H.
    symmetry in HeqR1.
    eapply instantiate_locals__getOperandValue in HeqR1; eauto.
    destruct HeqR1 as [gvs2 [H3 H4]].
    destruct (@IHlp l0) as [gvsss2 [J1 J2]]; auto.
    rewrite H3. rewrite J1. exists (gvs2 :: gvsss2). simpl. split; auto.
Qed.

Lemma instantiate_locals__initializeFrameValues : forall lc1 lc2
  (H2: instantiate_locals lc1 lc2) la gvs1 gvs2 (H1 : instantiate_gvs gvs1 gvs2),
  instantiate_locals (_initializeFrameValues la gvs1 lc1)
                     (NDopsem._initializeFrameValues la gvs2 lc2).
Proof.
  induction la; simpl; intros; auto.
    destruct a. destruct p.
    destruct gvs1; simpl.
      destruct gvs2; inv H1.
      apply instantiate_locals__updateAddAL; auto using instantiate_gv__gv2gvs. 
        apply IHla. simpl. auto.

      simpl in H1.
      destruct gvs2; inv H1.
      apply instantiate_locals__updateAddAL; auto.
Qed.           

Lemma instantiate_locals__initLocals : forall gvs1 gvss2 
  (H : instantiate_gvs gvs1 gvss2) la,
  instantiate_locals (initLocals la gvs1) (NDopsem.initLocals la gvss2).
Proof.
  unfold initLocals, NDopsem.initLocals.
  intros.
  apply instantiate_locals__initializeFrameValues; simpl; auto.
Qed.

Lemma defined_gv_dec : forall gv, defined_gv gv \/ ~ defined_gv gv.
Proof.
  destruct gv; simpl; auto.
    destruct p; simpl; auto.
    destruct v; simpl; try solve [left; congruence].
      right. intro J. contradict J; auto.
Qed.      

Lemma defined_gvs_dec : forall gvs, defined_gvs gvs \/ ~ defined_gvs gvs.
Proof.
  induction gvs; simpl; auto.
    destruct IHgvs as [IHgvs | IHgvs].
      destruct (@defined_gv_dec a) as [J | J]; auto.
        right. intros [J1 J2]. congruence.
      right. intros [J1 J2]. congruence.
Qed.

Lemma malloc__defined_gv : forall TD M tsz gn align0 M' mb,
  malloc TD M tsz gn align0 = Some (M', mb) ->
  defined_gv gn.
Proof.
  intros.
  apply malloc_inv in H.
  destruct H as [n [J1 [J2 J3]]].
  unfold GV2int in J1.
  destruct gn; tinv J1.
  destruct p.
  destruct v; tinv J1. simpl. congruence.
Qed. 
  
Lemma free__defined_gv : forall TD M ptr M',
  free TD M ptr = Some M' ->
  defined_gv ptr.
Proof.
  intros.
  apply free_inv in H.
  destruct H as [blk [ofs [hi [lo [J1 [J2 [J3 J4]]]]]]].
  unfold GV2ptr in J1.
  destruct ptr; tinv J1.
  destruct p.
  destruct v; tinv J1. simpl. congruence.
Qed. 

Lemma mload_inv : forall Mem2 t align0 TD gvp2 
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

Lemma mload__defined_gv : forall TD M ptr t a gv,
  mload TD M ptr t a = Some gv ->
  defined_gv ptr.
Proof.
  intros.
  apply mload_inv in H.
  destruct H as [blk [ofs [m J1]]].
  inv J1. simpl. congruence.
Qed. 

Lemma mstore__defined_gv : forall TD M ptr t a gv M',
  mstore TD M ptr t gv a = Some M' ->
  defined_gv ptr.
Proof.
  intros.
  apply store_inv in H.
  destruct H as [blk [ofs [c [v0 [J1 [J2 [J3 J4]]]]]]].
  unfold GV2ptr in J1. 
  destruct ptr; tinv J1.
  destruct p.
  destruct v; tinv J1.
  destruct ptr; inv J1.
  simpl. congruence.
Qed. 

Lemma lookupExFdecViaGV_inversion : forall TD Ps gl lc fs fv f,
  lookupExFdecViaGV TD Ps gl lc fs fv = Some f ->
  exists fptr, exists fn,
    getOperandValue TD fv lc gl = Some fptr /\
    lookupFdefViaGVFromFunTable fs fptr = Some fn /\
    lookupFdefViaIDFromProducts Ps fn = None /\
    lookupFdecViaIDFromProducts Ps fn = Some f.
Proof.
  intros.
  unfold lookupExFdecViaGV in H.
  destruct (getOperandValue TD fv lc gl); tinv H.
  simpl in H. exists g.
  destruct (lookupFdefViaGVFromFunTable fs g); tinv H.
  simpl in H. exists i0. 
  destruct (lookupFdefViaIDFromProducts Ps i0); tinv H.
  eauto.
Qed.  

Lemma lookupExFdecViaPtr_inversion : forall Ps fs fptr f,
  lookupExFdecViaPtr Ps fs fptr = Some f ->
  exists fn,
    lookupFdefViaGVFromFunTable fs fptr = Some fn /\
    lookupFdefViaIDFromProducts Ps fn = None /\
    lookupFdecViaIDFromProducts Ps fn = Some f.
Proof.
  intros.
  unfold lookupExFdecViaPtr in H.
  destruct (lookupFdefViaGVFromFunTable fs fptr); tinv H.
  simpl in H. exists i0.
  destruct (lookupFdefViaIDFromProducts Ps i0); tinv H.
  eauto.
Qed.  

Lemma instantiate_locals__exCallUpdateLocals : forall lc1 lc2 lc1' rid oResult 
    nr,
  instantiate_locals lc1 lc2 -> 
  exCallUpdateLocals nr rid oResult lc1 = ret lc1' ->
  exists lc2', 
    NDopsem.exCallUpdateLocals nr rid oResult lc2 = ret lc2' /\
    instantiate_locals lc1' lc2'. 
Proof.
  intros.
  unfold exCallUpdateLocals in H0.
  unfold NDopsem.exCallUpdateLocals.
  destruct nr; inv H0; eauto.
  destruct oResult; inv H2; eauto.
  exists (updateAddAL GVs lc2 rid ($ g $)).
  split; auto.
    apply instantiate_locals__updateAddAL; auto using instantiate_gv__gv2gvs.
Qed.

Definition undef_state St : Prop :=
  match St with 
  | {| CurTargetData := TD;
       ECS := {| CurCmds := nil;
                 Terminator := insn_br _ Cond _ _;
                 Locals := lc |} :: _;
       Globals := gl |} =>
     match getOperandValue TD Cond lc gl with
     | ret c => ~ defined_gv c 
     | _ => False
     end
  | {| CurTargetData := TD;
       ECS := {| CurCmds := insn_store _ _ v _ _::_;
                 Locals := lc |} :: _;
       Globals := gl |} =>
     match getOperandValue TD v lc gl with
     | ret gv => ~ defined_gv gv 
     | _ => False
     end
  | {| CurTargetData := TD;
       ECS := {| CurCmds := insn_call _ _ _ _ fv lp::_;
                 Locals := lc |} :: _;
       Globals := gl |} =>
     match getOperandValue TD fv lc gl, params2GVs TD lp lc gl with
     | ret gv, ret gvs => ~ defined_gv gv \/ ~ defined_gvs gvs
     | _, _ => False
     end
  |  {| CurTargetData := TD;
       ECS := {| CurCmds := insn_select _ v _ _ _::_;
                 Locals := lc |} :: _;
       Globals := gl |} =>
     match getOperandValue TD v lc gl with
     | ret gv => ~ defined_gv gv 
     | _ => False
     end
  |  {| CurTargetData := TD;
       ECS := {| CurCmds := insn_extractvalue _ _ v _::_;
                 Locals := lc |} :: _;
       Globals := gl |} =>
     match getOperandValue TD v lc gl with
     | ret gv => ~ defined_gv gv 
     | _ => False
     end
  |  {| CurTargetData := TD;
       ECS := {| CurCmds := insn_insertvalue _ _ v1 _ v2 _ ::_;
                 Locals := lc |} :: _;
       Globals := gl |} =>
     match getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl with
     | ret gv1, ret gv2 => ~ defined_gv gv1 \/ ~ defined_gv gv2  
     | _, _ => False
     end
  | _ => False
  end.

Lemma instantiate_dsInsn : forall st1 st2 st1' tr,
  instantiate_State st1 st2 ->
  LLVMopsem.dsInsn st1 st1' tr ->
  (exists st2', sInsn st2 st2' tr /\ instantiate_State st1' st2') \/
  undef_state st1.
Proof.
  intros st1 st2 st1' tr Hsim Hop.  
  (dsInsn_cases (induction Hop) Case).
Case "dsReturn". simpl_nd_llvmds. 
  eapply instantiate_locals__returnUpdateLocals in H1; eauto.
  destruct H1 as [lc2'' [H1 H2]].
  left. exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f2' b2' cs' tmn2' lc2'' als2')::ECs') gl' fs' Mem').
  split; eauto.
    repeat (split; auto).
Case "dsReturnVoid". simpl_nd_llvmds. 
  left. exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f2' b2' cs' tmn2' lc2' als2')::ECs') gl' fs' Mem').
  split; eauto.
    repeat (split; auto).
Case "dsBranch". simpl_nd_llvmds. 
  simpl. rewrite H.
  destruct (@defined_gv_dec c) as [Hdet | Hndet]; auto.
  left.
  eapply instantiate_locals__switchToNewBasicBlock in H1; eauto.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  destruct H1 as [lc2' [J3 J4]].
  apply defined_gv__instantiate_gv in J2; auto.   
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' (block_intro l' ps' cs' tmn') cs' tmn' lc2' als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto).
Case "dsBranch_uncond". simpl_nd_llvmds. 
  eapply instantiate_locals__switchToNewBasicBlock in H0; eauto.
  destruct H0 as [lc2' [J1 J2]]. left.
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' (block_intro l' ps' cs' tmn') cs' tmn' lc2' als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto).
Case "dsBop". simpl_nd_llvmds. 
  eapply instantiate_locals__BOP in H; eauto.
  destruct H as [gvs3' [J1 J2]]. left.
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsFBop". simpl_nd_llvmds. 
  eapply instantiate_locals__FBOP in H; eauto.
  destruct H as [gvs3' [J1 J2]]. left.
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsExtractValue". simpl_nd_llvmds. 
  simpl. rewrite H.
  destruct (@defined_gv_dec gv) as [Hdet | Hndet]; auto.
  left.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs [J1 J2]].
  eapply instantiate_locals__extractGenericValue in H0; eauto.
  destruct H0 as [gvs' [J3 J4]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsInsertValue". simpl_nd_llvmds. 
  simpl. rewrite H. rewrite H0.
  destruct (@defined_gv_dec gv) as [Hdet | Hndet]; auto.
  destruct (@defined_gv_dec gv') as [Hdet' | Hndet']; auto.
  left.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs' [J1' J2']].
  eapply instantiate_locals__insertGenericValue in H1; eauto.
  destruct H1 as [gvs'' [J3 J4]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs'') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsMalloc". simpl_nd_llvmds. 
  assert (J:=H1).
  apply malloc__defined_gv in J.
  left.
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gns [J1 J2]].
  apply defined_gv__instantiate_gv in J2; auto.   
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' 
      (updateAddAL _ lc1' id0 ($ (blk2GV TD' mb) $)) 
    als1')::ECs') gl' fs' Mem').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              instantiate_gv__gv2gvs).
Case "dsFree". simpl_nd_llvmds. 
  assert (J:=H0).
  apply free__defined_gv in J.
  left.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs [J1 J2]].
  apply defined_gv__instantiate_gv in J2; auto.   
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' lc1'
    als1')::ECs') gl' fs' Mem').
  split; eauto. 
    repeat (split; auto).
Case "dsAlloca". simpl_nd_llvmds. 
  assert (J:=H1).
  apply malloc__defined_gv in J.
  left.
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gns [J1 J2]].
  apply defined_gv__instantiate_gv in J2; auto.   
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' 
      (updateAddAL _ lc1' id0 ($ (blk2GV TD' mb) $)) 
    (mb::als1'))::ECs') gl' fs' Mem').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              instantiate_gv__gv2gvs).
Case "dsLoad". simpl_nd_llvmds.
  assert (J:=H0).
  apply mload__defined_gv in J.
  left.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  apply defined_gv__instantiate_gv in J2; auto.   
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 ($ gv $))
    als1')::ECs') gl' fs' M').
  split; eauto. 
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              instantiate_gv__gv2gvs).
Case "dsStore". simpl_nd_llvmds.
  assert (J:=H1).
  apply mstore__defined_gv in J.
  simpl. rewrite H.
  destruct (@defined_gv_dec gv1) as [Hdet | Hndet]; auto.
  left.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  apply defined_gv__instantiate_gv in J2; auto.   
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [mps2 [J3 J4]].
  apply defined_gv__instantiate_gv in J4; auto.   
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' lc1' als1')::ECs') gl' fs' Mem').
  split; eauto. 
    repeat (split; auto).
Case "dsGEP". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [mps [J1 J2]].
  eapply instantiate_locals__values2GVs in H0; eauto.
  destruct H0 as [vidxss [J3 J4]].
  eapply instantiate_locals__GEP in H1; eauto.
  destruct H1 as [mps2' [J5 J6]]. left.
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 mps2') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsTrunc". simpl_nd_llvmds. left.
  eapply instantiate_locals__TRUNC in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsExt". simpl_nd_llvmds. left.
  eapply instantiate_locals__EXT in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsCast". simpl_nd_llvmds. left.
  eapply instantiate_locals__CAST in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsIcmp". simpl_nd_llvmds. 
  eapply instantiate_locals__ICMP in H; eauto.
  destruct H as [gvs3' [J1 J2]]. left.
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsFcmp". simpl_nd_llvmds. 
  eapply instantiate_locals__FCMP in H; eauto.
  destruct H as [gvs3' [J1 J2]]. left.
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsSelect". simpl_nd_llvmds. 
  simpl. rewrite H.
  destruct (@defined_gv_dec c) as [Hdet | Hndet]; auto.
  left.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs0' [J1 J2]].
  apply defined_gv__instantiate_gv in J2; auto.   
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs1' [J3 J4]].
  eapply instantiate_locals__getOperandValue in H1; eauto.
  destruct H1 as [gvs2' [J5 J6]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (if isGVZero TD' c 
                                     then updateAddAL _ lc1' id0 gvs2' 
                                     else updateAddAL _ lc1' id0 gvs1') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto).
      destruct (isGVZero TD' c); auto using instantiate_locals__updateAddAL.
Case "dsCall". simpl_nd_llvmds. 
  apply lookupFdefViaGV_inversion in H.
  destruct H as [fptr [fn [J1 [J2 J3]]]].
  simpl. rewrite J1. rewrite H1.
  destruct (@defined_gv_dec fptr) as [Hdet | Hndet]; auto.
  left.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs2 [J11 J12]].
  apply defined_gv__instantiate_gv in J12; auto.   
  eapply instantiate_locals__params2GVs in H1; eauto.
  destruct H1 as [gvss2 [H11 H12]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                       (block_intro l' ps' cs' tmn') cs' tmn' 
                       (NDopsem.initLocals la gvss2) 
                       nil)::
     (NDopsem.mkEC f1' b1' (insn_call rid noret0 ca ft fv lp :: cs) tmn1' 
      lc1' als1') ::ECs') gl' fs' M').
  split.
    eapply sCall; eauto.
      unfold lookupFdefViaPtr. 
      rewrite J2. simpl. rewrite J3. auto.
    repeat (split; auto using instantiate_locals__initLocals).
Case "dsExCall". simpl_nd_llvmds. 
  apply lookupExFdecViaGV_inversion in H.
  destruct H as [fptr [fn [J1 [J2 [J3 J4]]]]].
  simpl. rewrite J1. rewrite H0.
  destruct (@defined_gv_dec fptr) as [Hdet | Hndet]; auto.
  destruct (@defined_gvs_dec gvs) as [Hdet' | Hndet']; auto.
  left.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs2 [J11 J12]].
  apply defined_gv__instantiate_gv in J12; auto.   
  eapply instantiate_locals__params2GVs in H0; eauto.
  destruct H0 as [gvss2 [H11 H12]].
  apply defined_gvs__instantiate_gvs in H12; auto.
  eapply instantiate_locals__exCallUpdateLocals in H2; eauto.
  destruct H2 as [lc2' [H21 H22]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' lc2' als1') ::ECs') gl' fs' Mem').
  split.
    eapply sExCall; eauto.
      unfold lookupExFdecViaPtr. 
      rewrite J2. simpl. rewrite J3. rewrite J4. eauto.
    repeat (split; auto using instantiate_locals__initLocals).
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
