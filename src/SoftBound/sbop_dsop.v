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

Definition sbEC_simulates_EC (sbEC:SoftBound.ExecutionContext) 
  (EC:LLVMopsem.ExecutionContext) : Prop :=
  match (sbEC, EC) with
  | (SoftBound.mkEC f1 b1 cs1 tmn1 lc1 rm1 als1, 
     LLVMopsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       f1 = f2 /\ b1 = b2 /\ cs1 = cs2 /\ tmn1 = tmn2 /\ lc1 = lc2 /\
       als1 = als2
  end.

Fixpoint sbECs_simulate_ECs (sbECs:SoftBound.ECStack) (ECs:LLVMopsem.ECStack) 
  : Prop :=
  match sbECs, ECs with
  | nil, nil => True
  | sbEC::sbECs', EC::ECs' => 
      sbEC_simulates_EC sbEC EC /\ sbECs_simulate_ECs sbECs' ECs'
  | _, _ => False
  end.

Definition sbState_simulates_State (sbSt:SoftBound.State) (St:LLVMopsem.State) 
  : Prop :=
  match (sbSt, St) with
  | (SoftBound.mkState S1 TD1 Ps1 ECs1 gl1 fs1 M1 MM1,
     LLVMopsem.mkState S2 TD2 Ps2 ECs2 gl2 fs2 M2) =>
      S1 = S2 /\ TD1 = TD2 /\ Ps1 = Ps2 /\ sbECs_simulate_ECs ECs1 ECs2 /\
      gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2
  end.

Lemma returnUpdateLocals_sim : forall TD' Mem' c' Result lc1' lc2' rm rm' gl' 
    lc'' rm'', 
  SoftBound.returnUpdateLocals TD' Mem' c' Result lc1' lc2' rm rm' gl' = 
    ret (lc'', rm'') ->
  returnUpdateLocals TD' Mem' c' Result lc1' lc2' gl' = ret lc''.
Proof.
  intros.  
  unfold SoftBound.returnUpdateLocals in H.
  unfold returnUpdateLocals.
  destruct (getCallerReturnID c'); try solve [inversion H; auto].
  destruct (getOperandValue TD' Mem' Result lc1' gl'); 
    try solve [inversion H; auto].
  unfold SoftBound.prop_reg_metadata in H.
  destruct (SoftBound.get_reg_metadata TD' Mem' gl' rm Result); 
    inversion H; auto.
  destruct p. inversion H1; auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_sim : forall ps TD' M' b1' gl' lc1'
    rm l1,
  SoftBound.getIncomingValuesForBlockFromPHINodes TD' M' ps b1' gl' lc1' rm =
    Some l1 ->
  exists l2, exists l3, 
    getIncomingValuesForBlockFromPHINodes TD' M' ps b1' gl' lc1' = Some l2 /\ 
    split l1 = (l2, l3).
Proof.
  induction ps; simpl; intros.
    inversion H; subst.
    exists nil. exists nil. eauto.

    destruct a. unfold SoftBound.get_reg_metadata in H.
    destruct (getValueViaBlockFromValuels l0 b1'); try solve [inversion H].
    remember (getOperandValue TD' M' v lc1' gl') as R0.
    destruct R0; try solve [inversion H].
    remember (SoftBound.getIncomingValuesForBlockFromPHINodes TD' M' ps b1' gl'
          lc1' rm) as R.
    destruct R; try solve [inversion H].
    symmetry in HeqR.
    apply IHps in HeqR.
    destruct HeqR as [l3 [l4 [J1 J2]]].
    rewrite J1.
    inversion H; subst. clear H. simpl. rewrite J2.
    destruct v; simpl in *.
      rewrite <- HeqR0. eauto.
      rewrite <- HeqR0. eauto.
Qed.

Lemma updateValuesForNewBlock_sim : forall l0 lc1' rm lc' rm' l2 l3,
  SoftBound.updateValuesForNewBlock l0 lc1' rm = (lc', rm') ->
  split l0 = (l2, l3) ->
  updateValuesForNewBlock l2 lc1' = lc'.
Proof.
  induction l0; simpl; intros.   
    inversion H0; subst.
    inversion H; subst.
    simpl; auto.

    destruct a. destruct p. 
    remember (SoftBound.updateValuesForNewBlock l0 lc1' rm) as R.
    destruct R.
    remember (split l0) as R1.
    destruct R1. inversion H0; subst.
    simpl. unfold SoftBound.prop_reg_metadata in H.
    destruct o.
      destruct p. inversion H; subst.
      erewrite IHl0 with (lc1':=lc1'); eauto.

      inversion H; subst.
      erewrite IHl0 with (lc1':=lc1'); eauto.
Qed.

Lemma switchToNewBasicBlock_sim : forall TD' M' b' b1' gl' lc1' rm lc' rm',
  SoftBound.switchToNewBasicBlock TD' M' b' b1' gl' lc1' rm = ret (lc', rm') ->
  switchToNewBasicBlock TD' M' b' b1' gl' lc1' = ret lc'.
Proof.
  intros.
  unfold SoftBound.switchToNewBasicBlock in H.
  unfold switchToNewBasicBlock.
  remember (SoftBound.getIncomingValuesForBlockFromPHINodes TD' M'
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
  SoftBound.params2GVs TD' M' lp lc1' gl' rm = ret ogvs ->
  exists gvs, exists l2, params2GVs TD' M' lp lc1' gl' = ret gvs /\
    split ogvs = (gvs, l2).
Proof.
  induction lp; simpl; intros.
    inversion H; subst. 
    exists nil. exists nil. auto.

    destruct a.
    destruct (getOperandValue TD' M' v lc1' gl'); try solve [inversion H; subst].
    remember (SoftBound.params2GVs TD' M' lp lc1' gl' rm) as R.
    destruct R; inversion H; subst.
      symmetry in HeqR.
      apply IHlp in HeqR; auto.      
      destruct HeqR as [gvs [l2 [J1 J2]]].
      simpl. rewrite J2. rewrite J1.
      eauto.
Qed.

Lemma initializeFrameValues_sim : forall la rm ogvs lc lc' rm' gvs l2,
  SoftBound._initializeFrameValues la ogvs lc rm = (lc', rm') -> 
  split ogvs = (gvs, l2) ->  
  _initializeFrameValues la gvs lc = lc'.
Proof.
  induction la; simpl; intros.
    inversion H; subst; auto.

    destruct a.
    destruct ogvs.
      simpl in H0. inversion H0; subst.
      remember (SoftBound._initializeFrameValues la nil lc rm) as R.
      destruct R.      
      symmetry in HeqR.
      eapply IHla in HeqR; eauto.
      inversion H; subst; auto.

      destruct p0.
      simpl in H0. 
      remember (split ogvs) as R'.
      destruct R'.
      inversion H0; subst.
      remember (SoftBound._initializeFrameValues la ogvs lc rm) as R.
      destruct R.      
      symmetry in HeqR.
      eapply IHla in HeqR; eauto.
      unfold SoftBound.prop_reg_metadata in H.
      destruct o; inversion H; subst; auto.
        destruct p0; inversion H; subst; auto.
Qed.

Lemma initLocals_params2GVs_sim : forall lp gl' TD' M' lc1' rm ogvs la lc' rm',
  SoftBound.params2GVs TD' M' lp lc1' gl' rm = ret ogvs ->
  SoftBound.initLocals la ogvs rm = (lc', rm') -> 
  exists gvs, params2GVs TD' M' lp lc1' gl' = ret gvs /\
    initLocals la gvs = lc'.
Proof.
  unfold SoftBound.initLocals, initLocals.
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
           SoftBound.CurSystem := _;
           SoftBound.CurTargetData := _;
           SoftBound.CurProducts := _;
           SoftBound.ECS := _::_::_;
           SoftBound.Globals := _;
           SoftBound.FunTable := _;
           SoftBound.Mem := _;
           SoftBound.Mmap := _ |} ?St |- _ ] =>
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
           SoftBound.CurSystem := _;
           SoftBound.CurTargetData := _;
           SoftBound.CurProducts := _;
           SoftBound.ECS := _::_;
           SoftBound.Globals := _;
           SoftBound.FunTable := _;
           SoftBound.Mem := _;
           SoftBound.Mmap := _ |} ?St |- _ ] =>
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
  | [H : SoftBound.prop_reg_metadata _ _ _ _ _ = (_, _) |- _ ] =>
      inversion H; subst; eauto
  end.

Definition memory_violation_abort sbSt : Prop :=
  match sbSt with
  | {| SoftBound.CurTargetData := TD;
       SoftBound.ECS := {| SoftBound.CurCmds := insn_load _ t vp _ :: cs;
                           SoftBound.Locals := lc;
                           SoftBound.Rmap := rm
                         |} :: _;
        SoftBound.Globals := gl;
        SoftBound.Mem := Mem0 |} => 
      match SoftBound.get_reg_metadata TD Mem0 gl rm vp, 
            getOperandValue TD Mem0 vp lc gl with
      | ret (md, mt), ret gvp => ~ SoftBound.assert_mptr TD t gvp md
      | _, _ => False
      end
  | {| SoftBound.CurTargetData := TD;
       SoftBound.ECS := {| SoftBound.CurCmds := insn_store _ t v vp _ :: cs;
                           SoftBound.Locals := lc;
                           SoftBound.Rmap := rm
                         |} :: _;
        SoftBound.Globals := gl;
        SoftBound.Mem := Mem0 |} => 
      match SoftBound.get_reg_metadata TD Mem0 gl rm vp, 
            getOperandValue TD Mem0 vp lc gl with
      | ret (md, mt), ret gvp => ~ SoftBound.assert_mptr TD t gvp md
      | _, _ => False
      end
  | _ => False
  end.

Lemma sbds__llvmds : forall sbSt St sbSt' tr,
  sbState_simulates_State sbSt St ->
  SoftBound.dsInsn sbSt sbSt' tr ->
  memory_violation_abort sbSt \/
  exists St', 
    LLVMopsem.dsInsn St St' tr /\
    sbState_simulates_State sbSt' St'.
Proof.
  intros sbSt St sbSt' tr Hsim HdsInsn.
  generalize dependent St.
  (sb_dsInsn_cases (induction HdsInsn) Case); intros; simpl_sbds_llvmds; 
    try invert_prop_reg_metadata.
  Case "dsReturn". right.
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
  Case "dsReturnVoid". right.
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
  Case "dsBranch". right.
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
  Case "dsBranch_uncond". right.
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
  Case "dsBop". right.
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
  Case "dsFBop". right.
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
  Case "dsExtractValue". right.
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
  Case "dsInsertValue". right.
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
  Case "dsMalloc". right.
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
  Case "dsFree". right.
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
  Case "dsAlloca". right.
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
  Case "dsLoad_nptr". right.
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
  Case "dsLoad_ptr". right.
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
  Case "dsLoad_abort".
     left. simpl. rewrite H. rewrite H0. auto.
  Case "dsStore_nptr". right.
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
  Case "dsStore_ptr". right.
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
  Case "dsStore_abort".
     left. simpl. rewrite H. rewrite H1. auto.
  Case "dsGEP". right.
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
  Case "dsTrunc". right.
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
  Case "dsExt". right.
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
  Case "dsBitcast_nptr". right.
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
  Case "dsBitcast_ptr". right.
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
  Case "dsInttoptr". right.
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
  Case "dsOthercast". right.
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
  Case "dsIcmp". right.
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
  Case "dsFcmp". right.
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
  Case "dsSelect_nptr". right.
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
  Case "dsSelect_ptr". right.
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
  Case "dsCall". right.
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
                 CurCmds := insn_call rid noret0 ca rt fv lp :: cs;
                 Terminator := tmn1';
                 Locals := lc1' ;
                 Allocas := als1' |} :: ECs';
       Globals := gl';
       FunTable := fs';
       Mem := M' |}.
     repeat (split; eauto).
  Case "dsExCall". right.
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
     repeat (split; eauto).
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)

