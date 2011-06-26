Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa/compcert".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Export targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import genericvalues.
Require Import trace.
Require Import ssa_props.
Require Import alist.
Require Import sb_ds_def.
Require Import ssa_dynamic.

Export LLVMsyntax.
Export LLVMlib.

Definition sbEC_simulates_EC (sbEC:SBopsem.ExecutionContext) 
  (EC:LLVMopsem.ExecutionContext) : Prop :=
  match (sbEC, EC) with
  | (SBopsem.mkEC f1 b1 cs1 tmn1 lc1 rm1 als1, 
     LLVMopsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       f1 = f2 /\ b1 = b2 /\ cs1 = cs2 /\ tmn1 = tmn2 /\ lc1 = lc2 /\
       als1 = als2
  end.

Fixpoint sbECs_simulate_ECs (sbECs:SBopsem.ECStack) (ECs:LLVMopsem.ECStack) 
  : Prop :=
  match sbECs, ECs with
  | nil, nil => True
  | sbEC::sbECs', EC::ECs' => 
      sbEC_simulates_EC sbEC EC /\ sbECs_simulate_ECs sbECs' ECs'
  | _, _ => False
  end.

Definition sbState_simulates_State (sbSt:SBopsem.State) (St:LLVMopsem.State) 
  : Prop :=
  match (sbSt, St) with
  | (SBopsem.mkState S1 TD1 Ps1 ECs1 gl1 fs1 M1 MM1,
     LLVMopsem.mkState S2 TD2 Ps2 ECs2 gl2 fs2 M2) =>
      S1 = S2 /\ TD1 = TD2 /\ Ps1 = Ps2 /\ sbECs_simulate_ECs ECs1 ECs2 /\
      gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2
  end.

Lemma returnUpdateLocals_sim : forall TD' Mem' c' rt Result lc1' lc2' rm rm' gl' 
    lc'' rm'', 
  SBopsem.returnUpdateLocals TD' Mem' c' rt Result lc1' lc2' rm rm' gl' = 
    ret (lc'', rm'') ->
  returnUpdateLocals TD' Mem' c' Result lc1' lc2' gl' = ret lc''.
Proof.
  intros.  
  unfold SBopsem.returnUpdateLocals, SBopsem.returnResult in H.
  unfold returnUpdateLocals.
  destruct (getOperandValue TD' Mem' Result lc1' gl'); 
    try solve [inversion H; auto].
  destruct (isPointerTypB rt); try solve [inversion H; auto].
    destruct (SBopsem.get_reg_metadata TD' Mem' gl' rm Result) as [[md ?]|]; 
      try solve [inversion H; auto].
    destruct c'; try solve [inversion H; auto].
    destruct n; try solve [inversion H; auto].
    unfold SBopsem.prop_reg_metadata in H.  
    destruct t; try solve [inversion H; auto].
    destruct t; try solve [inversion H; auto].

    destruct c'; try solve [inversion H; auto].
    destruct n; try solve [inversion H; auto].
    unfold SBopsem.prop_reg_metadata in H.  
    destruct t; try solve [inversion H; auto].
    destruct t; try solve [inversion H; auto].
Qed.

Lemma exCallUpdateLocals_sim : forall ft noret rid oResult lc rm lc'' rm'', 
  SBopsem.exCallUpdateLocals ft noret rid oResult lc rm = ret (lc'', rm'') ->
  exCallUpdateLocals noret rid oResult lc = ret lc''.
Proof.
  intros.  
  unfold SBopsem.exCallUpdateLocals in H.
  unfold exCallUpdateLocals.
  destruct noret0; try solve [inversion H; auto].
  destruct oResult; try solve [inversion H; auto].
  destruct ft; try solve [inversion H; auto].
  destruct ft; inversion H; auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_sim : forall ps TD' M' b1' gl' lc1'
    rm l1,
  SBopsem.getIncomingValuesForBlockFromPHINodes TD' M' ps b1' gl' lc1' rm =
    Some l1 ->
  exists l2, exists l3, 
    getIncomingValuesForBlockFromPHINodes TD' M' ps b1' gl' lc1' = Some l2 /\ 
    split l1 = (l2, l3).
Proof.
  induction ps; simpl; intros.
    inversion H; subst.
    exists nil. exists nil. eauto.

    destruct a. unfold SBopsem.get_reg_metadata in H.
    destruct (getValueViaBlockFromValuels l0 b1'); try solve [inversion H].
    remember (getOperandValue TD' M' v lc1' gl') as R0.
    destruct R0; try solve [inversion H].
    remember (SBopsem.getIncomingValuesForBlockFromPHINodes TD' M' ps b1' gl'
          lc1' rm) as R.
    destruct R; try solve [inversion H].
    symmetry in HeqR.
    apply IHps in HeqR.
    destruct HeqR as [l3 [l4 [J1 J2]]].
    rewrite J1.
    destruct (isPointerTypB t); inversion H; subst; clear H.
      destruct v; simpl in *.
        destruct (lookupAL SBopsem.metadata rm i1); inversion H1; subst.
          rewrite <- HeqR0. simpl. rewrite J2. eauto.

        rewrite <- HeqR0.
        destruct (
          match SBopsem.get_const_metadata c with
         | ret (bc, ec) =>
             do gvb <- const2GV TD' M' gl' bc;
             (do gve <- const2GV TD' M' gl' ec;
              ret {| SBopsem.md_base := gvb; SBopsem.md_bound := gve |})
         | merror =>
             ret {| SBopsem.md_base := null; SBopsem.md_bound := null |}
         end
        ) as [md|]; inversion H1; subst; simpl; eauto.
          rewrite J2. eauto.

      simpl. rewrite J2.
      destruct v; simpl in *.
        rewrite <- HeqR0. eauto.
        rewrite <- HeqR0. eauto.
Qed.

Lemma updateValuesForNewBlock_sim : forall l0 lc1' rm lc' rm' l2 l3,
  SBopsem.updateValuesForNewBlock l0 lc1' rm = (lc', rm') ->
  split l0 = (l2, l3) ->
  updateValuesForNewBlock l2 lc1' = lc'.
Proof.
  induction l0; simpl; intros.   
    inversion H0; subst.
    inversion H; subst.
    simpl; auto.

    destruct a. destruct p. 
    remember (SBopsem.updateValuesForNewBlock l0 lc1' rm) as R.
    destruct R.
    remember (split l0) as R1.
    destruct R1. inversion H0; subst.
    simpl. unfold SBopsem.prop_reg_metadata in H.
    destruct o.
      inversion H; subst.
      erewrite IHl0 with (lc1':=lc1'); eauto.

      inversion H; subst.
      erewrite IHl0 with (lc1':=lc1'); eauto.
Qed.

Lemma switchToNewBasicBlock_sim : forall TD' M' b' b1' gl' lc1' rm lc' rm',
  SBopsem.switchToNewBasicBlock TD' M' b' b1' gl' lc1' rm = ret (lc', rm') ->
  switchToNewBasicBlock TD' M' b' b1' gl' lc1' = ret lc'.
Proof.
  intros.
  unfold SBopsem.switchToNewBasicBlock in H.
  unfold switchToNewBasicBlock.
  remember (SBopsem.getIncomingValuesForBlockFromPHINodes TD' M'
    (getPHINodesFromBlock b') b1' gl' lc1' rm) as R.
  destruct R; try solve [inversion H].
  symmetry in HeqR.
  apply getIncomingValuesForBlockFromPHINodes_sim in HeqR.
  destruct HeqR as [l2 [l3 [J1 J2]]].
  rewrite J1.
  inversion H; subst.
  eapply updateValuesForNewBlock_sim in H1; eauto.
  rewrite H1. auto.
Qed.

Lemma params2GVs_sim : forall lp gl' TD' M' lc1' rm ogvs,
  SBopsem.params2GVs TD' M' lp lc1' gl' rm = ret ogvs ->
  exists gvs, exists l2, params2GVs TD' M' lp lc1' gl' = ret gvs /\
    split ogvs = (gvs, l2).
Proof.
  induction lp; simpl; intros.
    inversion H; subst. 
    exists nil. exists nil. auto.

    destruct a.
    destruct (getOperandValue TD' M' v lc1' gl'); try solve [inversion H; subst].
    remember (SBopsem.params2GVs TD' M' lp lc1' gl' rm) as R.
    destruct R; try solve [inversion H].
    symmetry in HeqR.
    apply IHlp in HeqR; auto.      
    destruct HeqR as [gvs [l2 [J1 J2]]].
    destruct (isPointerTypB t); inversion H; subst; 
      simpl; rewrite J2; rewrite J1; eauto.
Qed.

Lemma initializeFrameValues_sim : forall la rm ogvs lc lc' rm' gvs l2,
  SBopsem._initializeFrameValues la ogvs lc rm = (lc', rm') -> 
  split ogvs = (gvs, l2) ->  
  _initializeFrameValues la gvs lc = lc'.
Proof.
  induction la; simpl; intros.
    inversion H; subst; auto.

    destruct a. destruct p.
    destruct ogvs.
      simpl in H0. inversion H0; subst.
      remember (SBopsem._initializeFrameValues la nil lc rm) as R.
      destruct R as [lc1 rm1].
      unfold SBopsem.prop_reg_metadata in H.     
      symmetry in HeqR.
      eapply IHla in HeqR; eauto.
      destruct (isPointerTypB t); inversion H; subst; auto.

      destruct p.
      simpl in H0. 
      remember (split ogvs) as R'.
      destruct R'.
      inversion H0; subst.
      remember (SBopsem._initializeFrameValues la ogvs lc rm) as R.
      destruct R as [lc1 rm1].
      symmetry in HeqR.
      eapply IHla in HeqR; eauto.
      destruct (isPointerTypB t); try solve [inversion H; subst; auto].
        unfold SBopsem.prop_reg_metadata in H.
        destruct o; try solve [inversion H; subst; auto].
Qed.

Lemma initLocals_params2GVs_sim : forall lp gl' TD' M' lc1' rm ogvs la lc' rm',
  SBopsem.params2GVs TD' M' lp lc1' gl' rm = ret ogvs ->
  SBopsem.initLocals la ogvs rm = (lc', rm') -> 
  exists gvs, params2GVs TD' M' lp lc1' gl' = ret gvs /\
    initLocals la gvs = lc'.
Proof.
  unfold SBopsem.initLocals, initLocals.
  intros.
  apply params2GVs_sim in H.
  destruct H as [gvs [l2 [J1 J2]]].
  exists gvs.
  split; eauto using initializeFrameValues_sim.
Qed.

Ltac simpl_sbds_llvmds :=
  match goal with
  | [Hsim : sbState_simulates_State 
           {|
           SBopsem.CurSystem := _;
           SBopsem.CurTargetData := _;
           SBopsem.CurProducts := _;
           SBopsem.ECS := _::_::_;
           SBopsem.Globals := _;
           SBopsem.FunTable := _;
           SBopsem.Mem := _;
           SBopsem.Mmap := _ |} ?St |- _ ] =>
     destruct St as [S' TD' Ps' ECs' gl' fs' M'];
     destruct Hsim as [Hsim1 [Hims2 [Hsim3 [Hsim4 [Hsim5 [Hsim6 Hsim7]]]]]]; 
       subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' als1'] ECs']; 
       try solve [inversion Hsim4];
     simpl in Hsim4; destruct Hsim4 as [Hsim41 Hsim42];
     destruct ECs' as [|[f2' b2' cs2' tmn2' lc2' als2'] ECs'];
       try solve [inversion Hsim42];
     destruct Hsim42 as [Hsim42 Hsim43];
     destruct Hsim41 as [J1 [J2 [J3 [J4 [J5 J6]]]]]; subst;
     destruct Hsim42 as [J1 [J2 [J3 [J4 [J5 J6]]]]]; subst
  | [Hsim : sbState_simulates_State 
           {|
           SBopsem.CurSystem := _;
           SBopsem.CurTargetData := _;
           SBopsem.CurProducts := _;
           SBopsem.ECS := _::_;
           SBopsem.Globals := _;
           SBopsem.FunTable := _;
           SBopsem.Mem := _;
           SBopsem.Mmap := _ |} ?St |- _ ] =>
     destruct St as [S' TD' Ps' ECs' gl' fs' M'];
     destruct Hsim as [Hsim1 [Hims2 [Hsim3 [Hsim4 [Hsim5 [Hsim6 Hsim7]]]]]]; 
       subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' als1'] ECs']; 
       try solve [inversion Hsim4];
     simpl in Hsim4; destruct Hsim4 as [Hsim41 Hsim42];
     destruct Hsim41 as [J1 [J2 [J3 [J4 [J5 J6]]]]]; subst
  end.

Ltac invert_prop_reg_metadata :=
  match goal with
  | [H : SBopsem.prop_reg_metadata _ _ _ _ _ = (_, _) |- _ ] =>
      inversion H; subst; eauto
  end.

Lemma sbds__llvmds : forall sbSt St sbSt' tr,
  sbState_simulates_State sbSt St ->
  SBopsem.dsInsn sbSt sbSt' tr ->
  exists St', 
    LLVMopsem.dsInsn St St' tr /\
    sbState_simulates_State sbSt' St'.
Proof.
  intros sbSt St sbSt' tr Hsim HdsInsn.
  generalize dependent St.
  (sb_dsInsn_cases (induction HdsInsn) Case); intros; simpl_sbds_llvmds; 
    try invert_prop_reg_metadata.
  Case "dsReturn". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f2';
                 CurBB := b2';
                 CurCmds := cs';
                 Terminator := tmn2';
                 Locals := lc'';
                 Allocas := als2' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto using returnUpdateLocals_sim).
  Case "dsReturnVoid". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f2';
                 CurBB := b2';
                 CurCmds := cs';
                 Terminator := tmn2';
                 Locals := lc2';
                 Allocas := als2' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto).
  Case "dsBranch". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := block_intro l' ps' cs' tmn';
                 CurCmds := cs';
                 Terminator := tmn';
                 Locals := lc';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto using switchToNewBasicBlock_sim).
  Case "dsBranch_uncond". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := block_intro l' ps' cs' tmn';
                 CurCmds := cs';
                 Terminator := tmn';
                 Locals := lc';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto using switchToNewBasicBlock_sim).
  Case "dsBop". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv3;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsFBop". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv3;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsExtractValue". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsInsertValue". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv'';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsMalloc". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 (blk2GV TD' mb);
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto).
  Case "dsFree". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := lc1';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto).
  Case "dsAlloca". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 (blk2GV TD' mb);
                 Allocas := mb::als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto).
  Case "dsLoad_nptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsLoad_ptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsStore_nptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := lc1';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto).
  Case "dsStore_ptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := lc1';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto).
  Case "dsGEP". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gvp';
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsTrunc". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv2;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsExt". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv2;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsBitcast_nptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv2;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsBitcast_ptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv2;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsInttoptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv2;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsOthercast". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv2;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsIcmp". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv3;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsFcmp". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := updateAddAL _ lc1' id0 gv3;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsSelect_nptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := if isGVZero TD' c
                           then updateAddAL GenericValue lc1' id0 gv2
                           else updateAddAL GenericValue lc1' id0 gv1;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsSelect_ptr". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := if isGVZero TD' c
                           then updateAddAL GenericValue lc1' id0 gv2
                           else updateAddAL GenericValue lc1' id0 gv1;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
       destruct (isGVZero TD' c); invert_prop_reg_metadata; auto.
  Case "dsCall". 
     eapply initLocals_params2GVs_sim in H1; eauto.
     destruct H1 as [gvs [J1 J2]].
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := fdef_intro (fheader_intro fa rt fid la va) lb;
                 CurBB := block_intro l' ps' cs' tmn';
                 CurCmds := cs';
                 Terminator := tmn';
                 Locals := (initLocals la gvs);
                 Allocas := nil |} ::
              {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := insn_call rid noret0 ca ft fv lp :: cs;
                 Terminator := tmn1';
                 Locals := lc1' ;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsExCall". 
     exists {|
       CurSystem := S';
       CurTargetData := TD';
       CurProducts := Ps';
       ECS := {| CurFunction := f1';
                 CurBB := b1';
                 CurCmds := cs;
                 Terminator := tmn1';
                 Locals := lc' ;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := Mem' |}.
     repeat (split; eauto using exCallUpdateLocals_sim).
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)

