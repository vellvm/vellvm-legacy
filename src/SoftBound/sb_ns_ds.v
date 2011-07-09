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
Require Import sb_ns_def.
Require Import ndopsem_dsop.

Export SBnsop.
Export SBopsem.

Definition instantiate_EC (ec1 : SBopsem.ExecutionContext) 
  (ec2 : SBnsop.ExecutionContext) : Prop :=
match ec1, ec2 with
| SBopsem.mkEC f1 b1 cs1 tmn1 lc1 rm1 als1, 
  SBnsop.mkEC f2 b2 cs2 tmn2 lc2 rm2 als2 =>
    f1 = f2 /\ b1 = b2 /\ cs1 = cs2 /\ tmn1 = tmn2 /\
    instantiate_locals lc1 lc2 /\ rm1 = rm2 /\ als1 = als2
end.

Fixpoint instantiate_ECs (ecs1 : SBopsem.ECStack) (ecs2 : SBnsop.ECStack) 
  : Prop :=
match ecs1, ecs2 with
| nil, nil => True
| ec1::ecs1', ec2::ecs2' => instantiate_EC ec1 ec2 /\ instantiate_ECs ecs1' ecs2'
| _, _ => False
end.

Definition instantiate_State (st1 : SBopsem.State) (st2 : SBnsop.State) 
  : Prop :=
match st1, st2 with
| SBopsem.mkState s1 td1 ps1 ecs1 gl1 fs1 M1 MM1,
  SBnsop.mkState s2 td2 ps2 ecs2 gl2 fs2 M2 MM2 =>
    s1 = s2 /\ td1 = td2 /\ ps1 = ps2 /\ instantiate_ECs ecs1 ecs2 /\ gl1 = gl2
    /\ fs1 = fs2 /\ M1 = M2 /\ MM1 = MM2
end.

Lemma instantiate_locals__returnResult : forall TD rt Result lc1 lc2 gl gv1 rm 
    md,
  instantiate_locals lc1 lc2 -> 
  SBopsem.returnResult TD rt Result lc1 rm gl = Some (gv1, md) ->
  exists gv2, 
    SBnsop.returnResult TD rt Result lc2 rm gl = Some (gv2, md) /\
    instantiate_gv gv1 gv2.
Proof.
  intros.  
  unfold SBopsem.returnResult in H0.
  remember (getOperandValue TD Result lc1 gl) as R.
  destruct R; tinv H0.
  symmetry in HeqR.
  eapply instantiate_locals__getOperandValue in HeqR; eauto.
  destruct HeqR as [gvs2 [J1 J2]].
  unfold SBnsop.returnResult.
  rewrite J1. 
  destruct (isPointerTypB rt); inv H0; eauto.
  destruct (get_reg_metadata TD gl rm Result); inv H2.
  exists gvs2. split; auto using instantiate_locals__updateAddAL.
Qed.

Lemma instantiate_locals__returnUpdateLocals : forall TD lc1 lc2 lc1' lc2' Result
    gl lc1'' c rm rm' rt rm'',
  instantiate_locals lc1 lc2 -> 
  instantiate_locals lc1' lc2' -> 
  SBopsem.returnUpdateLocals TD c rt Result lc1 lc1' rm rm' gl = 
    ret (lc1'',rm'') ->
  exists lc2'', 
    SBnsop.returnUpdateLocals TD c rt Result lc2 lc2' rm rm' gl = 
      ret (lc2'',rm'') /\
    instantiate_locals lc1'' lc2''. 
Proof.
  intros.
  unfold SBopsem.returnUpdateLocals in H1.
  remember (returnResult TD rt Result lc1 rm gl) as R.
  destruct R as [[gr md]|]; tinv H1.
  symmetry in HeqR.
  eapply instantiate_locals__returnResult in HeqR; eauto.
  destruct HeqR as [gvs2 [J1 J2]].
  unfold SBnsop.returnUpdateLocals.
  rewrite J1. 
  destruct c; inv H1; eauto.
  destruct n; inv H3.
    exists lc2'. split; auto.
    destruct (SBopsem.isReturnPointerTypB t); inv H2.
      exists (updateAddAL GVs lc2' i0 gvs2).   
      split; auto using instantiate_locals__updateAddAL.

      exists (updateAddAL GVs lc2' i0 gvs2).   
      split; auto using instantiate_locals__updateAddAL.
Qed.

Fixpoint instantiate_localms (lcm1 : list (id*GenericValue*option metadata)) 
  (lcm2 : list (id*GVs*option metadata)) : Prop :=
match lcm1, lcm2 with
| nil, nil => True
| (id1,gv1,omd1)::lcm1', (id2,gvs2,omd2)::lcm2' => 
    id1=id2 /\ instantiate_gv gv1 gvs2 /\ instantiate_localms lcm1' lcm2' /\ 
    omd1 = omd2
| _, _ => False
end.

Lemma instantiate_locals__getIncomingValuesForBlockFromPHINodes : forall TD b
    gl lc1 lc2 (Hlc : instantiate_locals lc1 lc2) ps re1 rm,  
  SBopsem.getIncomingValuesForBlockFromPHINodes TD ps b gl lc1 rm = Some re1 ->
  exists re2,
    SBnsop.getIncomingValuesForBlockFromPHINodes TD ps b gl lc2 rm = Some re2 /\
    instantiate_localms re1 re2.
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
    remember (getIncomingValuesForBlockFromPHINodes TD ps b gl lc1 rm) as R1.
    destruct R1; inv H.  
    rewrite J1.
    symmetry in HeqR1.
    destruct (@IHps l1 rm) as [re2 [J3 J4]]; auto.
    rewrite J3. 
    destruct (isPointerTypB t); inv H1.
      destruct (get_reg_metadata TD gl rm v); inv H0.
      exists ((i0, gvs2, ret m) :: re2). simpl. auto.

      exists ((i0, gvs2, merror) :: re2). simpl. auto.
Qed.

Lemma instantiate_locals__updateValuesForNewBlock : forall lc1 lc2 re1 re2 rm 
    lc1' rm',
  instantiate_locals lc1 lc2 ->
  instantiate_localms re1 re2 ->
  SBopsem.updateValuesForNewBlock re1 lc1 rm = (lc1', rm') ->
  exists lc2', 
    SBnsop.updateValuesForNewBlock re2 lc2 rm = (lc2', rm') /\
    instantiate_locals lc1' lc2'.
Proof.
  induction re1; destruct re2; simpl; intros; auto.
    inv H1. eauto.
    inv H0.
    destruct a. destruct p. inv H0.

    destruct a. destruct p0. destruct p. destruct p.
    destruct H0 as [eq [J1 [J2 eq']]]; subst.
    remember (updateValuesForNewBlock re1 lc1 rm) as R.
    destruct R as [lc' rm''].
    symmetry in HeqR. eapply IHre1 in HeqR; eauto.
    destruct HeqR as [lc2' [J3 J4]].
    rewrite J3.
    destruct o0; inv H1.
      exists (updateAddAL _ lc2' i1 g0). 
      split; auto using instantiate_locals__updateAddAL.

      exists (updateAddAL _ lc2' i1 g0). 
      split; auto using instantiate_locals__updateAddAL.
Qed.

Lemma instantiate_locals__switchToNewBasicBlock : forall TD lc1 lc2 gl lc1' b b'
    rm rm',
  instantiate_locals lc1 lc2 -> 
  SBopsem.switchToNewBasicBlock TD b' b gl lc1 rm = Some (lc1',rm') ->
  exists lc2', SBnsop.switchToNewBasicBlock TD b' b gl lc2 rm = Some (lc2',rm') 
    /\ instantiate_locals lc1' lc2'. 
Proof.
  intros.
  unfold switchToNewBasicBlock in H0.
  unfold SBnsop.switchToNewBasicBlock.
  remember (getIncomingValuesForBlockFromPHINodes TD (getPHINodesFromBlock b') b
           gl lc1 rm) as R.
  destruct R; inv H0.
  symmetry in HeqR.
  eapply instantiate_locals__getIncomingValuesForBlockFromPHINodes in HeqR; eauto.
  destruct HeqR as [re2 [J1 J2]].
  rewrite J1.
  eapply instantiate_locals__updateValuesForNewBlock in H2; eauto.
  destruct H2 as [lc2' [J3 J4]].
  rewrite J3. eauto.
Qed.

Fixpoint instantiate_gvms (l1 : list (GenericValue * option metadata)) 
  (l2 : list (GVs * option metadata)) :=
match l1, l2 with
| nil, nil => True
| (gv1,omd1)::l1', (gvs2,omd2)::l2' => 
    instantiate_gv gv1 gvs2 /\ omd1 = omd2 /\ instantiate_gvms l1' l2'
| _, _ => False
end.

Lemma instantiate_locals__params2GVs : forall TD lc1 lc2 gl rm
  (Hlc:instantiate_locals lc1 lc2) lp gvms1,
  SBopsem.params2GVs TD lp lc1 gl rm = Some gvms1 ->
  exists gvsms2, SBnsop.params2GVs TD lp lc2 gl rm = Some gvsms2 /\
    instantiate_gvms gvms1 gvsms2.
Proof.
  induction lp; simpl; intros.
    inv H. exists nil. simpl. auto.

    destruct a.
    remember (getOperandValue TD v lc1 gl) as R1.
    destruct R1; tinv H.
    remember (params2GVs TD lp lc1 gl rm) as R2.
    destruct R2; tinv H.
    inv H.
    symmetry in HeqR1.
    eapply instantiate_locals__getOperandValue in HeqR1; eauto.
    destruct HeqR1 as [gvs2 [H3 H4]].
    destruct (@IHlp l0) as [gvsss2 [J1 J2]]; auto.
    rewrite H3. rewrite J1. 
    destruct (isPointerTypB t); inv H1.
      exists ((gvs2, get_reg_metadata TD gl rm v) :: gvsss2). simpl. split; auto.
      exists ((gvs2, merror) :: gvsss2). simpl. split; auto.
Qed.

Lemma instantiate_locals__initializeFrameValues : forall lc1 lc2 rm
  (H2: instantiate_locals lc1 lc2) la gvs1 gvs2 lc1' rm'
  (H1 : instantiate_gvms gvs1 gvs2),
  _initializeFrameValues la gvs1 lc1 rm = (lc1', rm') ->
  exists lc2', 
    SBnsop._initializeFrameValues la gvs2 lc2 rm = (lc2', rm') /\
    instantiate_locals lc1' lc2'.
Proof.
  induction la; simpl; intros; auto.
    inv H. eauto.

    destruct a. destruct p.
    destruct gvs1; simpl.
      remember (_initializeFrameValues la nil lc1 rm) as R.
      destruct R as [lc1'' rm''].
      destruct gvs2; inv H1.
      symmetry in HeqR.
      apply IHla with (gvs2:=nil) in HeqR; simpl; eauto.
      destruct HeqR as [lc2' [J1 J2]].
      rewrite J1.
      destruct (isPointerTypB t); inv H.
        unfold SBnsop.prop_reg_metadata.
        exists (updateAddAL GVs lc2' i0 ($ gundef t # t $)). 
        split; auto.
          apply instantiate_locals__updateAddAL; 
            auto using instantiate_gv__gv2gvs. 

        exists (updateAddAL GVs lc2' i0 ($ gundef t # t $)). 
        split; auto.
          apply instantiate_locals__updateAddAL; 
            auto using instantiate_gv__gv2gvs. 

      destruct p.
      simpl in H1.
      destruct gvs2; tinv H1. 
      destruct p. destruct H1 as [J1 [J2 J3]]; subst.
      remember (_initializeFrameValues la gvs1 lc1 rm) as R.
      destruct R as [lc1'' rm''].
      symmetry in HeqR.
      eapply IHla in HeqR; simpl; eauto.
      destruct HeqR as [lc2' [J1' J2']].
      rewrite J1'.
      unfold SBnsop.prop_reg_metadata.
      destruct (isPointerTypB t); inv H.
        destruct o0; inv H1.
          exists (updateAddAL GVs lc2' i0 g0). 
          split; auto using instantiate_locals__updateAddAL.

          exists (updateAddAL GVs lc2' i0 g0). 
          split; auto using instantiate_locals__updateAddAL.
        exists (updateAddAL GVs lc2' i0 g0). 
        split; auto using instantiate_locals__updateAddAL.
Qed.           

Lemma instantiate_locals__initLocals : forall gvs1 gvss2 lc1 rm
  (H : instantiate_gvms gvs1 gvss2) la,
  initLocals la gvs1 = (lc1, rm) ->
  exists lc2, 
    SBnsop.initLocals la gvss2 = (lc2, rm) /\ instantiate_locals lc1 lc2.
Proof.
  unfold initLocals, SBnsop.initLocals.
  intros.
  eapply instantiate_locals__initializeFrameValues; eauto.
    simpl. auto.
Qed.

Lemma instantiate_locals__exCallUpdateLocals : forall lc1 lc2 lc1' rid oResult 
    nr ft rm rm',
  instantiate_locals lc1 lc2 -> 
  SBopsem.exCallUpdateLocals ft nr rid oResult lc1 rm = ret (lc1',rm') ->
  exists lc2', 
    SBnsop.exCallUpdateLocals ft nr rid oResult lc2 rm = ret (lc2',rm') /\
    instantiate_locals lc1' lc2'. 
Proof.
  intros.
  unfold SBopsem.exCallUpdateLocals in H0.
  unfold SBnsop.exCallUpdateLocals.
  destruct nr; inv H0; eauto.
  destruct oResult; inv H2; eauto.
  destruct ft; inv H1; 
    eauto using instantiate_locals__updateAddAL, instantiate_gv__gv2gvs.
  destruct ft; inv H2; 
    eauto using instantiate_locals__updateAddAL, instantiate_gv__gv2gvs.
Qed.

Ltac simpl_nd_sbds :=
  match goal with
  | [Hsim : instantiate_State {| ECS := _::_::_ |} ?st2 |- _ ] =>
     destruct st2 as [S' TD' Ps' ECs' gl' fs' M' MM'];
     destruct Hsim as [eq1 [eq2 [eq3 [Hsim [eq4 [eq5 [eq6 eq7]]]]]]]; subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' rm1' als1'] ECs']; 
       try solve [inversion Hsim];
     simpl in Hsim; destruct Hsim as [Hsim1 Hsim2];
     destruct ECs' as [|[f2' b2' cs2' tmn2' lc2' rm2' als2'] ECs'];
       try solve [inversion Hsim2];
     destruct Hsim2 as [Hsim2 Hsim3];
     destruct Hsim1 as [J1 [J2 [J3 [J4 [Hsim1 [J6 J7]]]]]]; subst;
     destruct Hsim2 as [J1 [J2 [J3 [J4 [Hsim2 [J6 J7]]]]]]; subst
  | [Hsim : instantiate_State {| ECS := _::_|} ?st2 |- _ ] =>
     destruct st2 as [S' TD' Ps' ECs' gl' fs' M' MM'];
     destruct Hsim as [eq1 [eq2 [eq3 [Hsim [eq4 [eq5 [eq6 eq7]]]]]]]; subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' rm1' als1'] ECs']; 
       try solve [inversion Hsim];
     simpl in Hsim; destruct Hsim as [Hsim1 Hsim2];
     destruct Hsim1 as [J1 [J2 [J3 [J4 [Hsim1 [J6 J7]]]]]]; subst
  end.

Hint Constructors SBnsop.nsInsn.

Lemma instantiate_dsInsn : forall st1 st2 st1' tr,
  instantiate_State st1 st2 ->
  SBopsem.dsInsn st1 st1' tr ->
  (exists st2', SBnsop.nsInsn st2 st2' tr /\ instantiate_State st1' st2').
Proof.
  intros st1 st2 st1' tr Hsim Hop.  
  (sb_dsInsn_cases (induction Hop) Case).
Case "dsReturn". simpl_nd_sbds. 
  eapply instantiate_locals__returnUpdateLocals in H1; eauto.
  destruct H1 as [lc2'' [H1 H2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f2' b2' cs' tmn2' lc2'' rm'' als2')::ECs') gl' fs' Mem' MM').
  split; eauto.
    repeat (split; auto).
Case "dsReturnVoid". simpl_nd_sbds. 
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f2' b2' cs' tmn2' lc2' rm2' als2')::ECs') gl' fs' Mem' MM').
  split; eauto.
    repeat (split; auto).
Case "dsBranch". simpl_nd_sbds. 
  eapply instantiate_locals__switchToNewBasicBlock in H1; eauto.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  destruct H1 as [lc2' [J3 J4]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' (block_intro l' ps' cs' tmn') cs' tmn' lc2' rm' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto).
Case "dsBranch_uncond". simpl_nd_sbds. 
  eapply instantiate_locals__switchToNewBasicBlock in H0; eauto.
  destruct H0 as [lc2' [J1 J2]]. 
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' (block_intro l' ps' cs' tmn') cs' tmn' lc2' rm' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto).
Case "dsBop". simpl_nd_sbds. 
  eapply instantiate_locals__BOP in H; eauto.
  destruct H as [gvs3' [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') rm1' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsFBop". simpl_nd_sbds. 
  eapply instantiate_locals__FBOP in H; eauto.
  destruct H as [gvs3' [J1 J2]]. 
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') rm1' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsExtractValue". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs [J1 J2]].
  eapply instantiate_locals__extractGenericValue in H0; eauto.
  destruct H0 as [gvs' [J3 J4]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs') rm1' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsInsertValue". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs' [J1' J2']].
  eapply instantiate_locals__insertGenericValue in H1; eauto.
  destruct H1 as [gvs'' [J3 J4]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs'') rm1' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsMalloc". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gns [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' 
      (updateAddAL _ lc1' id0 ($ (blk2GV TD' mb) # typ_pointer t $)) 
    rm' als1')::ECs') gl' fs' Mem' MM').
  inv H3.
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              instantiate_gv__gv2gvs).
Case "dsFree". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' lc1' rm1'
    als1')::ECs') gl' fs' Mem' MM').
  split; eauto. 
    repeat (split; auto).
Case "dsAlloca". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gns [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' 
      (updateAddAL _ lc1' id0 ($ (blk2GV TD' mb) # typ_pointer t $)) rm'
    (mb::als1'))::ECs') gl' fs' Mem' MM').
  inv H3.
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              instantiate_gv__gv2gvs).
Case "dsLoad_nptr". simpl_nd_sbds.
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs2 [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 ($ gv # t $))
    rm1' als1')::ECs') gl' fs' M' MM').
  split; eauto. 
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              instantiate_gv__gv2gvs).
Case "dsLoad_ptr". simpl_nd_sbds.
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs2 [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 ($ gv # t $))
    rm' als1')::ECs') gl' fs' M' MM').
  inv H5.
  split; eauto. 
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              instantiate_gv__gv2gvs).
Case "dsStore_nptr". simpl_nd_sbds.
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs2 [J1 J2]].
  eapply instantiate_locals__getOperandValue in H1; eauto.
  destruct H1 as [mps2 [J3 J4]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' lc1' rm1' als1')::ECs') gl' fs' Mem' MM').
  split; eauto. 
    repeat (split; auto).
Case "dsStore_ptr". 
  rename MM' into MM0. simpl_nd_sbds.
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs2 [J1 J2]].
  eapply instantiate_locals__getOperandValue in H1; eauto.
  destruct H1 as [mps2 [J3 J4]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' lc1' rm1' als1')::ECs') gl' fs' Mem' 
      (set_mem_metadata TD' MM' gvp md')).
  split; eauto. 
    repeat (split; auto).
Case "dsGEP". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [mps [J1 J2]].
  eapply instantiate_locals__values2GVs in H1; eauto.
  destruct H1 as [vidxss [J3 J4]].
  eapply instantiate_locals__GEP in H2; eauto.
  destruct H2 as [mps2' [J5 J6]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 mps2') rm' als1')
      ::ECs') gl' fs' M' MM').
  inv H3.
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsTrunc". simpl_nd_sbds.
  eapply instantiate_locals__TRUNC in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') rm1' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsExt". simpl_nd_sbds. 
  eapply instantiate_locals__EXT in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') rm1' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsBitcast_nptr". simpl_nd_sbds. 
  eapply instantiate_locals__CAST in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') rm1' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsBitcast_ptr". simpl_nd_sbds. 
  eapply instantiate_locals__CAST in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') rm' als1')
      ::ECs') gl' fs' M' MM').
  inv H2.
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsInttoptr". simpl_nd_sbds. 
  eapply instantiate_locals__CAST in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') rm' als1')
      ::ECs') gl' fs' M' MM').
  inv H0.
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsOthercast". simpl_nd_sbds. 
  eapply instantiate_locals__CAST in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') rm1' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsIcmp". simpl_nd_sbds. 
  eapply instantiate_locals__ICMP in H; eauto.
  destruct H as [gvs3' [J1 J2]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') rm1' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsFcmp". simpl_nd_sbds. 
  eapply instantiate_locals__FCMP in H; eauto.
  destruct H as [gvs3' [J1 J2]]. 
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') rm1' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsSelect_nptr". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs0' [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs1' [J3 J4]].
  eapply instantiate_locals__getOperandValue in H1; eauto.
  destruct H1 as [gvs2' [J5 J6]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (if isGVZero TD' c 
                                   then updateAddAL _ lc1' id0 gvs2' 
                                   else updateAddAL _ lc1' id0 gvs1') rm1' als1')
      ::ECs') gl' fs' M' MM').
  split; eauto.
    repeat (split; auto).
      destruct (isGVZero TD' c); auto using instantiate_locals__updateAddAL.
Case "dsSelect_ptr". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs0' [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs1' [J3 J4]].
  eapply instantiate_locals__getOperandValue in H1; eauto.
  destruct H1 as [gvs2' [J5 J6]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' (if isGVZero TD' c 
                                   then updateAddAL _ lc1' id0 gvs2' 
                                   else updateAddAL _ lc1' id0 gvs1') rm' als1')
      ::ECs') gl' fs' M' MM').
  split.
    eapply SBnsop.nsSelect_ptr; eauto.
      destruct (isGVZero TD' c); inv H5; eauto.
  repeat (split; auto).
    destruct (isGVZero TD' c); inv H5; 
      auto using instantiate_locals__updateAddAL.
Case "dsCall". simpl_nd_sbds. 
  apply lookupFdefViaGV_inversion in H.
  destruct H as [fptr [fn [J1 [J2 J3]]]].
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs2 [J11 J12]].
  eapply instantiate_locals__params2GVs in H1; eauto.
  destruct H1 as [gvss2 [H11 H12]].
  eapply instantiate_locals__initLocals in H2; eauto.
  destruct H2 as [lc2' [H21 H22]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                       (block_intro l' ps' cs' tmn') cs' tmn' 
                       lc2' rm'
                       nil)::
     (SBnsop.mkEC f1' b1' (insn_call rid noret0 ca ft fv lp :: cs) tmn1' 
      lc1' rm1' als1') ::ECs') gl' fs' M' MM').
  split.
    eapply SBnsop.nsCall; eauto.
      unfold lookupFdefViaPtr. 
      rewrite J2. simpl. rewrite J3. auto.
    repeat (split; auto).
Case "dsExCall". simpl_nd_sbds. 
  apply lookupExFdecViaGV_inversion in H.
  destruct H as [fptr [fn [J1 [J2 [J3 J4]]]]].
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs2 [J11 J12]].
  eapply ndopsem_dsop.instantiate_locals__params2GVs in H0; eauto.
  destruct H0 as [gvss2 [H11 H12]].
  eapply instantiate_locals__exCallUpdateLocals in H2; eauto.
  destruct H2 as [lc2' [H21 H22]].
  exists (SBnsop.mkState S' TD' Ps' 
    ((SBnsop.mkEC f1' b1' cs tmn1' lc2' rm' als1') ::ECs') gl' fs' Mem' MM').
  split.
    eapply SBnsop.nsExCall; eauto.
      unfold lookupExFdecViaPtr. 
      rewrite J2. simpl. rewrite J3. rewrite J4. eauto.
    repeat (split; auto).
Qed.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)

