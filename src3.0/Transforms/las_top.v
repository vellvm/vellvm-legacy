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
Require Import alive_store.
Require Import id_rhs_val.
Require Import mem2reg.
Require Import program_sim.
Require Import memory_props.
Require Import trans_tactic.
Require Import top_sim.
Require Import las.
Require Import las_wfS.

(* similar to phinode_bsim *)
Lemma s_genInitState__las_State_simulation: forall pinfo lasinfo S1 S2 main
  VarArgs cfg2 IS2 
  (Hssim: system_simulation pinfo lasinfo S1 S2)
  (Hinit: Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2)),
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo lasinfo cfg1 IS1 cfg2 IS2.
Proof.
  unfold Opsem.s_genInitState.
  intros.
  inv_mbind'.
  destruct m as [los nts ps].
  inv_mbind'.
  destruct b as [l0 ps0 cs0 tmn0].
  destruct f as [[fa rt fid la va] bs].
  inv_mbind'. symmetry_ctx.
  assert (HlkF2FromS2:=HeqR).
  eapply TopSim.system_simulation__fdef_simulation_r2l in HeqR; eauto.
  destruct HeqR as [f1 [HlkF1fromS1 Hfsim]]. simpl in Hfsim.
  fill_ctxhole.
  eapply TopSim.system_simulation__getParentOfFdefFromSystem in HeqR0; eauto.
  destruct HeqR0 as [m1 [J1 J2]].
  fill_ctxhole. destruct m1 as [los1 nts1 ps1].
  destruct J2 as [J2 [J3 J4]]; subst.
  eapply TopSim.genGlobalAndInitMem_spec in HeqR1; eauto.
  destruct HeqR1 as [gl1 [fs1 [M1 [HeqR1 [EQ1 [EQ2 EQ3]]]]]]; subst.
  fill_ctxhole.
  assert (J:=HeqR2).
  eapply getEntryBlock__simulation in J; eauto.
  destruct J as [b1 [J5 J6]].
  fill_ctxhole.
  destruct b1 as [l2 ps2 cs2 tmn2].
  destruct f1 as [[fa1 rt1 fid1 la1 va1] bs1].
  assert (J:=Hfsim).
  apply fdef_simulation__eq_fheader in J.
  inv J.
  fill_ctxhole.
  match goal with
  | |- exists _:_, exists _:_, Some (?A, ?B) = _ /\ _ => exists A; exists B
  end.
  match goal with 
  | H: getParentOfFdefFromSystem _ _ = _ |- _ =>
    apply getParentOfFdefFromSystem__moduleInProductsInSystemB in H;
    destruct H as [HMinS HinPs]
  end.
  assert (J:=J6).
  apply block_simulation_inv in J.
  destruct J as [J1 [J2 [J3 J7]]]; subst.
  assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0)
           (fdef_intro (fheader_intro fa rt fid la va) bs) = true) as HBinF.
    apply entryBlockInFdef; auto.
  repeat (split; auto).
    exists l0. exists ps2. exists nil. auto.
    exists l0. exists ps0. exists nil. auto.
Qed.

Lemma cmds_simulation_nil_inv' : forall (pinfo : PhiInfo) 
  (lasinfo : LASInfo pinfo) (f1 : fdef) (cs : list cmd),
  cmds_simulation pinfo lasinfo f1 cs nil -> cs = nil.
Proof.
  unfold cmds_simulation. intros.
  destruct_if; auto.
    destruct cs; inv H1; auto.
Qed.

Lemma cmds_simulation_cons_inv' : forall (pinfo : PhiInfo) 
  (lasinfo : LASInfo pinfo) (f1 : fdef) (cs : list cmd) c2 cs2,
  cmds_simulation pinfo lasinfo f1 cs (c2::cs2) -> 
  exists c1, exists cs1, 
    cs = c1::cs1 /\
    cmd_simulation pinfo lasinfo f1 c1 c2 /\
    cmds_simulation pinfo lasinfo f1 cs1 cs2.
Proof.
  unfold cmds_simulation, cmd_simulation. intros.
  destruct_if; eauto.
    destruct cs; inv H1; eauto.
Qed.

Inductive tmn_simulation' (pinfo:PhiInfo) (lasinfo:LASInfo pinfo) (F:fdef) 
  : terminator -> terminator -> Prop :=
| tmn_simulation_return : forall id0 t0 v v',
    value_simulation pinfo lasinfo F v v' ->
    tmn_simulation' pinfo lasinfo F (insn_return id0 t0 v) (insn_return id0 t0 v')
| tmn_simulation_return_void : forall id0,
    tmn_simulation' pinfo lasinfo F (insn_return_void id0) (insn_return_void id0)
| tmn_simulation_br : forall id0 v v' l1 l2,
    value_simulation pinfo lasinfo F v v' ->
    tmn_simulation' pinfo lasinfo F (insn_br id0 v l1 l2) (insn_br id0 v' l1 l2)
| tmn_simulation_br_uncond : forall id0 l0,
    tmn_simulation' pinfo lasinfo F (insn_br_uncond id0 l0) 
                                    (insn_br_uncond id0 l0)
| tmn_simulation_unreachable : forall id0,
    tmn_simulation' pinfo lasinfo F (insn_unreachable id0) 
                                    (insn_unreachable id0)
.

Lemma tmn_simulation'__refl: forall pinfo lasinfo F t,
  PI_f pinfo <> F ->
  tmn_simulation' pinfo lasinfo F t t.
Proof.
  intros.
  destruct t; constructor; auto using value_simulation__refl.
Qed.

Lemma tmn_simulation__tmn_simulation': forall pinfo lasinfo F t t'
  (Htsim: tmn_simulation pinfo lasinfo F t t'),
  tmn_simulation' pinfo lasinfo F t t'.
Proof.
  unfold tmn_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto using tmn_simulation'__refl.
    destruct t; simpl;
    constructor; try solve [
      unfold value_simulation;
      destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence; auto
    ].
Qed.

Ltac inTmnOp_isnt_stuck v H3 Hwfcfg1 Hwfpp1 :=
match type of Hwfpp1 with
| OpsemPP.wf_State 
              {|
              OpsemAux.CurSystem := _;
              OpsemAux.CurTargetData := ?td;
              OpsemAux.CurProducts := _;
              OpsemAux.Globals := ?gl;
              OpsemAux.FunTable := _ |}
    {| Opsem.ECS := {| Opsem.CurFunction := _;
                       Opsem.CurBB := ?b;
                       Opsem.CurCmds := nil;
                       Opsem.Terminator := ?tmn;
                       Opsem.Locals := ?lc;
                       Opsem.Allocas := _
                     |} :: _;
       Opsem.Mem := _ |}  =>
    let G := fresh "G" in
    let gvs := fresh "gvs" in
    assert (exists gvs, Opsem.getOperandValue td v lc gl = Some gvs) as G; 
      try solve [
        destruct H3 as [l5 [ps2 [cs21 H3]]]; subst;
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as 
          [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
        inv_mbind;
        eapply OpsemPP.getOperandValue_inTmnOperans_isnt_stuck; eauto 1;
          simpl; auto
      ];
    destruct G as [gvs G]
end.

Ltac tmnOps_eq H3 Hwfcfg1 Hwfpp1 HwfS1 :=
      destruct H3 as [l1 [ps1 [cs11 H3]]]; subst;
      destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
      destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
      destruct HwfS1 as [HwfS1 _];
      unfold wf_ExecutionContext, inscope_of_ec in HwfS1;
      inv_mbind;
      eapply getOperandValue_inTmnOperands_sim; 
        eauto 2 using wf_system__wf_fdef, wf_system__uniqFdef; simpl; auto.

Lemma s_isFinialState__las_State_simulation: forall
  pinfo lasinfo cfg1 FS1 cfg2 FS2
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hwfcfg2: OpsemPP.wf_Config cfg2) (Hwfpp2: OpsemPP.wf_State cfg2 FS2) 
  (HwfS1: id_rhs_val.wf_State (value_id (LAS_lid pinfo lasinfo)) 
           (LAS_value pinfo lasinfo) (PI_f pinfo) cfg1 FS1)
  (Hstsim : State_simulation pinfo lasinfo cfg1 FS1 cfg2 FS2),
  Opsem.s_isFinialState cfg1 FS1 = Opsem.s_isFinialState cfg2 FS2.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  destruct cfg2 as [S2 [los2 nts2] gl2 fs2].
  destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
  destruct FS1 as [[|[? ? cs1 ? ?] ES1]]; 
  destruct FS2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
    auto |
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst; inv Hstsim
  ].
  destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst.
  inv X. simpl.
  destruct Hstsim as [Hstsim Hstsim'].
  fold ECs_simulation in Hstsim'.
  destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst.
  destruct cs1, cs2; try solve [
    auto |
    apply cmds_simulation_nil_inv in Hstsim; try congruence |
    apply cmds_simulation_nil_inv' in Hstsim; try congruence
  ].
  apply tmn_simulation__tmn_simulation' in Htmn.
  inv Htmn; auto.
    destruct ES1, ES2; try solve [auto | inv Hstsim'].
      inTmnOp_isnt_stuck v H3 Hwfcfg1 Hwfpp1.
      inTmnOp_isnt_stuck v' H4 Hwfcfg2 Hwfpp2.
      rewrite G. rewrite G0.
      f_equal.
      tmnOps_eq H3 Hwfcfg1 Hwfpp1 HwfS1.

    destruct ES1, ES2; try solve [auto | inv Hstsim'].
Qed.

Ltac undefined_state__State_simulation_r2l_tac1 :=
  match goal with
  | Hstsim: State_simulation _ _ _ ?St1 _ ?St2 |- _ =>
    destruct St2 as [[|[? ? [|CurCmds] [] ?] [|[]]] ?]; try tauto;
    destruct CurCmds; try tauto;
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X;
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [Hstsim Hstsim'];
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
    destruct Hstsim' as [Hstsim' _];
    destruct Hstsim' as [? [? [? [? [? [? [? Hstsim']]]]]]]; subst;
   simpl
  end.

Ltac undefined_state__State_simulation_r2l_tac3 :=
  match goal with
  | Hstsim: State_simulation _ _ _ ?St1 _ ?St2 |- _ =>
    destruct St2 as [[|[? [? ? ? tmn] CurCmds tmn' ?] ?] ?]; try tauto;
    destruct tmn; try tauto;
    destruct CurCmds; try tauto;
    destruct tmn'; try tauto;
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? H3]]]]]; subst;
    inv X;
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [Hstsim _];
    destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
    let l5 := fresh "l5" in
    destruct H3 as [l5 [ps5 [cs5 EQ]]]; subst
  end.

Ltac undefined_state__State_simulation_r2l_tac41 :=
  match goal with
  | Hstsim: State_simulation _ _ _ ?St1 ?cfg2 ?St2 |- _ =>
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X;
    destruct ECS as [|[? ? ? ? Locals0] ECS]; try tauto;
    destruct Hstsim as [Hstsim _];
    destruct Hstsim as [? [? [? [? [H4 [H5 [? Hstsim]]]]]]]; subst
  end. 

Ltac undefined_state__la_State_simulation_r2l_tac42 := 
repeat match goal with
| Hwfcfg1: OpsemPP.wf_Config ?cfg1, Hwfpp1: OpsemPP.wf_State ?cfg1 ?St1, 
  HwfS1: wf_State _ _ _ ?cfg1 ?St1, 
  Hvsim: value_simulation _ _ _ ?v0 ?v,
  _: ret ?gn = Opsem.getOperandValue ?td ?v ?Locals ?fs2,
  _: block_simulation _ _ _ ?b _,
  H4: exists _:_, exists _:_, exists _:_, ?b = _ |- _ =>
    let G := fresh "G" in
    let gvs := fresh "gvs" in
    assert (exists gvs, Opsem.getOperandValue td
       v0 Locals fs2 = Some gvs) as G; try solve [
      destruct H4 as [l5 [ps2 [cs21 H4]]]; subst;
      destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
      destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
      inv_mbind;
      eapply OpsemPP.getOperandValue_inCmdOps_isnt_stuck; eauto 1; simpl; auto
    ];
    destruct G as [gvs G];
    assert (gvs = gn) as EQ; try solve [
      destruct H4 as [l1 [ps1 [cs11 H4]]]; subst;
      destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
      destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
      destruct HwfS1 as [HwfS1 _];
      unfold wf_ExecutionContext, inscope_of_ec in HwfS1;
      inv_mbind;
      eapply getOperandValue_inCmdOperands_sim; 
        eauto 2 using wf_system__wf_fdef, wf_system__uniqFdef; simpl; auto
    ];
    subst;
    clear Hvsim
end.

Ltac undefined_state__la_State_simulation_r2l_tac43 := 
      match goal with
      | Hstsim: cmds_simulation _ _ _ _ (_::_) |- _ =>
      apply cmds_simulation_cons_inv' in Hstsim; subst;
      destruct Hstsim as [c1' [cs2' [J1 [J2 J3]]]]; subst;
      apply cmd_simulation__cmd_simulation' in J2;
      inv J2;
      undefined_state__la_State_simulation_r2l_tac42
     end.

Lemma undefined_state__las_State_simulation_r2l: forall pinfo lasinfo cfg1 St1 
  cfg2 St2 (Hstsim : State_simulation pinfo lasinfo cfg1 St1 cfg2 St2)
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (HwfS1: id_rhs_val.wf_State (value_id (LAS_lid pinfo lasinfo)) 
           (LAS_value pinfo lasinfo) (PI_f pinfo) cfg1 St1)
  (Hundef: OpsemPP.undefined_state cfg2 St2), OpsemPP.undefined_state cfg1 St1.
Proof.
  intros.
  unfold OpsemPP.undefined_state in Hundef.
  destruct cfg2 as [S2 [los2 nts2] gl2 fs2].
  destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
  repeat match goal with
  | Hundef : _ \/ _ |- _ => destruct Hundef as [Hundef | Hundef]
  end.
  Case "1".

    undefined_state__State_simulation_r2l_tac1.
    apply cmds_simulation_nil_inv' in Hstsim; subst.
    apply cmds_simulation_cons_inv' in Hstsim'.
    destruct Hstsim' as [c1' [cs1' [J1 [J2 J3]]]]; subst.
    left. 
    unfold tmn_simulation in Htmn. 
    destruct_if; subst; simpl; auto.
    match goal with
    | H11: subst_tmn _ _ ?tmn = insn_return _ _ _ |- _ => 
      destruct tmn; inv H11; auto
    end.

  Case "2".
    undefined_state__State_simulation_r2l_tac1.
    apply cmds_simulation_nil_inv' in Hstsim; subst.
    apply cmds_simulation_cons_inv' in Hstsim'.
    destruct Hstsim' as [c1' [cs1' [J1 [J2 J3]]]]; subst.
    right. left.
    assert (getCallerReturnID c = getCallerReturnID c1') as EQ.
      unfold cmd_simulation in J2. subst. clear.
      destruct_if; auto.
      destruct c1'; auto.
    rewrite <- EQ.
    clear - Htmn Hundef.
    unfold tmn_simulation in Htmn. 
    destruct (fdef_dec (PI_f pinfo) CurFunction1); subst; simpl; auto.
    match goal with
    | H11: subst_tmn _ _ ?tmn = insn_return_void _ |- _ => 
      destruct tmn; inv H11; auto
    end.

  Case "3".

    undefined_state__State_simulation_r2l_tac3.
    apply cmds_simulation_nil_inv' in Hstsim. subst.
    right. right. left.
    simpl. 
    unfold tmn_simulation in Htmn. 
    destruct_if; subst; simpl; auto.
    match goal with
    | H11: subst_tmn _ _ ?tmn = insn_unreachable _ |- _ => 
      destruct tmn; inv H11; auto
    end.

  Case "4".

    right; right; right; left;
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' Locals] ?] ?]; try solve [
      tauto |

      inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind;
      undefined_state__State_simulation_r2l_tac41;
      undefined_state__la_State_simulation_r2l_tac43;
        repeat fill_ctxhole; exists gn; fill_ctxhole; auto
    ].

  Case "5".
    right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__la_State_simulation_r2l_tac43.
    repeat fill_ctxhole; exists gn; fill_ctxhole; auto.

  Case "6".
    right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gvs [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__la_State_simulation_r2l_tac43. 
    repeat fill_ctxhole; exists gvs; fill_ctxhole; auto.

  Case "7".
    right. right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gv [mgv [EQ1 [EQ2 Hundef]]]]; 
      inv EQ1; inv EQ2; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__la_State_simulation_r2l_tac43. 
    repeat fill_ctxhole; exists gv; exists mgv; fill_ctxhole; auto.

  Case "8".
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    right; right; right; right. right. right. right.
    undefined_state__State_simulation_r2l_tac41.
    inv_mbind.
    destruct Hundef as [fptr [EQ Hundef]]; inv EQ.
    inv_mbind.
    apply cmds_simulation_cons_inv' in Hstsim; subst;
    destruct Hstsim as [c1' [cs2' [J1 [J2 J3]]]]; subst.
    apply cmd_simulation__cmd_simulation' in J2;
    inv J2.  
    undefined_state__la_State_simulation_r2l_tac42.
    repeat fill_ctxhole.
    exists fptr. split; auto.
    remember (OpsemAux.lookupExFdecViaPtr gl2 FunTable fptr) as R.
    destruct R as [[[]]|].
      inv_mbind.
      destruct Hundef as [gvs0 [EQ Hundef]].
      dgvs_instantiate_inv.
      assert (exists gvs, 
                Opsem.params2GVs (los2,nts2) lp0 Locals fs2 = Some gvs) as G'.
        destruct H4 as [l5 [ps2 [cs21 H4]]]; subst.
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]].
        inv_mbind.
        eapply OpsemPP.params2GVs_isnt_stuck; eauto 1; simpl; auto.
          exists nil. auto.
      destruct G' as [gvs' G'].
      assert (gvs' = l1) as EQ.
        destruct H4 as [l5 [ps1 [cs11 H4]]]; subst;
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
        destruct HwfS1 as [HwfS1 _];
        unfold wf_ExecutionContext, inscope_of_ec in HwfS1;
        inv_mbind.
        eapply params2GVs_sim; 
          eauto 2 using wf_system__wf_fdef, wf_system__uniqFdef; 
            try solve [simpl; auto].
      subst.
      repeat fill_ctxhole.
      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_r2l; eauto.
      simpl.
      exists l1. split; auto.
    
      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_None_r2l; eauto.
Qed.

Lemma las_is_bsim : forall pinfo lasinfo Cfg1 St1 Cfg2 St2 St2' tr2 
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hwfcfg2: OpsemPP.wf_Config Cfg2) (Hwfpp2: OpsemPP.wf_State Cfg2 St2) 
  (HwfS1: id_rhs_val.wf_State (value_id (LAS_lid pinfo lasinfo)) 
           (LAS_value pinfo lasinfo) (PI_f pinfo) Cfg1 St1)
  (Hsim: State_simulation pinfo lasinfo Cfg1 St1 Cfg2 St2)
  (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2)
  (Hsubst: substable_values (OpsemAux.CurTargetData Cfg1) (OpsemAux.Globals Cfg1)
             (PI_f pinfo) (value_id (LAS_lid pinfo lasinfo))
             (LAS_value pinfo lasinfo)) stinfo Hp
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo)
  (Halst: alive_store.wf_State pinfo stinfo Cfg1 St1)
  (Hok: ~ sop_goeswrong Cfg1 St1),
  exists St1', 
    Opsem.sInsn Cfg1 St1 St1' tr2 /\
    State_simulation pinfo lasinfo Cfg1 St1' Cfg2 St2'.
Proof.
  intros.
  assert (Hnfinal1: Opsem.s_isFinialState Cfg1 St1 = merror).
    remember (Opsem.s_isFinialState Cfg1 St1) as R.
    destruct R; auto.
    apply s_isFinialState__las_State_simulation in Hsim; 
      try solve [auto | congruence].
      contradict Hop2.
      apply s_isFinialState__stuck. congruence.
  assert (J:=Hwfpp).
  apply OpsemPP.progress in J; auto.
  destruct J as [Hfinal1 | [[IS1'' [tr0 Hop1]] | Hundef1]]; try congruence.
    assert (OpsemPP.wf_State Cfg1 IS1'') as Hwfpp''.
      apply OpsemPP.preservation in Hop1; auto.
    assert (vev_State (value_id (LAS_lid pinfo lasinfo))
             (LAS_value pinfo lasinfo) (PI_f pinfo) Cfg1 St1) as Hvev.
      eapply las__alive_store__vev; eauto.
    assert (id_rhs_val.wf_State (value_id (LAS_lid pinfo lasinfo)) 
           (LAS_value pinfo lasinfo) (PI_f pinfo) Cfg1 IS1'') as HwfS1'.
      eapply id_rhs_val.preservation in Hop1; eauto.
    eapply las_is_sim in Hsim; eauto.
    destruct Hsim as [Hsim EQ]; subst.
    exists IS1''. 
    split; eauto.

    apply undefined_state__stuck' in Hundef1.
    contradict Hok.
    apply nonfinal_stuck_state_goes_wrong; auto.
Qed.

Lemma sop_star__las_State_simulation: forall pinfo lasinfo cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo)
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfcfg2: OpsemPP.wf_Config cfg2) 
  (Hwfpp1: OpsemPP.wf_State cfg1 IS1) (Hwfpp2: OpsemPP.wf_State cfg2 IS2) 
  (HwfS1: id_rhs_val.wf_State (value_id (LAS_lid pinfo lasinfo)) 
           (LAS_value pinfo lasinfo) (PI_f pinfo) cfg1 IS1) stinfo Hp
  (Hsubst: substable_values (OpsemAux.CurTargetData cfg1) (OpsemAux.Globals cfg1)
             (PI_f pinfo) (value_id (LAS_lid pinfo lasinfo))
             (LAS_value pinfo lasinfo))
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo)
  (Halst: alive_store.wf_State pinfo stinfo cfg1 IS1)
  (Hstsim : State_simulation pinfo lasinfo cfg1 IS1 cfg2 IS2) maxb
  (Hless: 0 <= maxb) (Hwfgs: MemProps.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\
    State_simulation pinfo lasinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent cfg1.
  generalize dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    eapply las_is_bsim in Hstsim; eauto.
    destruct Hstsim as [St1' [Hop1 Hstsim]].
    assert (OpsemPP.wf_State cfg1 St1') as Hwfpp1'.
      apply OpsemPP.preservation in Hop1; auto.
    assert (vev_State (value_id (LAS_lid pinfo lasinfo))
             (LAS_value pinfo lasinfo) (PI_f pinfo) cfg1 IS1) as Hvev.
      eapply las__alive_store__vev; eauto.
    assert (id_rhs_val.wf_State (value_id (LAS_lid pinfo lasinfo))
             (LAS_value pinfo lasinfo) (PI_f pinfo) cfg1 St1') as HwfS1'.
      eapply id_rhs_val.preservation in Hop1; eauto.
    assert (alive_store.wf_State pinfo stinfo cfg1 St1') as Halst'.
      eapply alive_store.preservation in Hop1; eauto.
    assert (Promotability.wf_State maxb pinfo cfg1 St1') as Hnoalias'.
      eapply Promotability.preservation in Hop1; eauto.
    eapply IHHopstar in Hstsim; 
      eauto using sop_goeswrong__step, (@OpsemPP.preservation DGVs).
    destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
    exists FS1.
    split; eauto.
Qed.

Lemma sop_plus__las_State_simulation: forall pinfo lasinfo cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo)
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfcfg2: OpsemPP.wf_Config cfg2) 
  (Hwfpp1: OpsemPP.wf_State cfg1 IS1) (Hwfpp2: OpsemPP.wf_State cfg2 IS2) 
  (HwfS1: id_rhs_val.wf_State (value_id (LAS_lid pinfo lasinfo)) 
           (LAS_value pinfo lasinfo) (PI_f pinfo) cfg1 IS1) stinfo Hp
  (Hsubst: substable_values (OpsemAux.CurTargetData cfg1) (OpsemAux.Globals cfg1)
             (PI_f pinfo) (value_id (LAS_lid pinfo lasinfo))
             (LAS_value pinfo lasinfo))
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo)
  (Halst: alive_store.wf_State pinfo stinfo cfg1 IS1)
  (Hstsim : State_simulation pinfo lasinfo cfg1 IS1 cfg2 IS2) maxb
  (Hless: 0 <= maxb) (Hwfgs: MemProps.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hopplus : Opsem.sop_plus cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, Opsem.sop_plus cfg1 IS1 FS1 tr /\
    State_simulation pinfo lasinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  inv Hopplus.
  eapply las_is_bsim in Hstsim; eauto.
  destruct Hstsim as [St1' [Hop1 Hstsim']].
  assert (wf_State (value_id (LAS_lid pinfo lasinfo)) (LAS_value pinfo lasinfo)
     (PI_f pinfo) cfg1 St1') as HwfS1'.
    eapply id_rhs_val.preservation in Hop1; eauto.
      eapply las__alive_store__vev; eauto.
  eapply sop_star__las_State_simulation in Hstsim'; eauto using
    palloca_props.preservation, Promotability.preservation,
    (@OpsemPP.preservation DGVs), sop_goeswrong__step,
    alive_store.preservation.
  destruct Hstsim' as [FS1 [Hopstar Hstsim']].
  exists FS1. 
  split; eauto.
Qed.

Lemma vev_State_preservation : forall pinfo lasinfo cfg IS maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg))
  (Halias: Promotability.wf_State maxb pinfo cfg IS) (Hwfpi: WF_PhiInfo pinfo)
  stinfo Hp (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo)
  (Halst: alive_store.wf_State pinfo stinfo cfg IS)
  (Hwfcfg : OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg IS) 
  (Hvev: vev_State (value_id (LAS_lid pinfo lasinfo))
               (LAS_value pinfo lasinfo) (PI_f pinfo) cfg IS)
  IS' tr  (Hstep: Opsem.sInsn cfg IS IS' tr),
  vev_State (value_id (LAS_lid pinfo lasinfo))
               (LAS_value pinfo lasinfo) (PI_f pinfo) cfg IS'.
Proof.
  intros.
  eapply las__alive_store__vev; eauto.
    apply OpsemPP.preservation in Hstep; auto.
    eapply alive_store.preservation in Hstep; eauto.
Qed.

Lemma id_rhs_val_preservation_star : forall v1 v2 F pinfo lasinfo cfg IS IS' tr
  (Heq1: v1 = value_id (LAS_lid pinfo lasinfo))
  (Heq2: v2 = LAS_value pinfo lasinfo) (Heq3: F = PI_f pinfo) maxb (Hle: 0 <= maxb)
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg))
  (Halias: Promotability.wf_State maxb pinfo cfg IS) (Hwfpi: WF_PhiInfo pinfo)
  stinfo Hp (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo)
  (Halst: alive_store.wf_State pinfo stinfo cfg IS)
  (Hvals : substable_values (OpsemAux.CurTargetData cfg) (OpsemAux.Globals cfg)
             F v1 v2) (Hvev: vev_State v1 v2 F cfg IS) 
  (Hwfcfg : OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg IS) 
  (HwfS1: id_rhs_val.wf_State v1 v2 F cfg IS) (Hstar: Opsem.sop_star cfg IS IS' tr),
  id_rhs_val.wf_State v1 v2 F cfg IS'.
Proof.
  intros. subst.
  induction Hstar; auto.
    apply IHHstar; auto.
      eapply Promotability.preservation; eauto.
      eapply alive_store.preservation; eauto.
      eapply OpsemPP.preservation; eauto.
      eapply vev_State_preservation; eauto.
      eapply id_rhs_val.preservation; eauto.
Qed.  

Lemma id_rhs_val_preservation_plus : forall v1 v2 F pinfo lasinfo cfg IS IS' tr
  (Heq1: v1 = value_id (LAS_lid pinfo lasinfo))
  (Heq2: v2 = LAS_value pinfo lasinfo) (Heq3: F = PI_f pinfo) maxb (Hle: 0 <= maxb)
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg))
  (Halias: Promotability.wf_State maxb pinfo cfg IS) (Hwfpi: WF_PhiInfo pinfo)
  stinfo Hp (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo)
  (Halst: alive_store.wf_State pinfo stinfo cfg IS)
  (Hvals : substable_values (OpsemAux.CurTargetData cfg) (OpsemAux.Globals cfg)
             F v1 v2) (Hvev: vev_State v1 v2 F cfg IS) 
  (Hwfcfg : OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg IS) 
  (HwfS1: id_rhs_val.wf_State v1 v2 F cfg IS) (Hplus: Opsem.sop_plus cfg IS IS' tr),
  id_rhs_val.wf_State v1 v2 F cfg IS'.
Proof.
  intros.
  apply OpsemProps.sop_plus__implies__sop_star in Hplus.
  eapply id_rhs_val_preservation_star; eauto.
Qed.

Lemma sop_div__las_State_simulation: forall pinfo lasinfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpi: WF_PhiInfo pinfo)
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfcfg2: OpsemPP.wf_Config cfg2) 
  (Hwfpp1: OpsemPP.wf_State cfg1 IS1) (Hwfpp2: OpsemPP.wf_State cfg2 IS2) 
  (HwfS1: id_rhs_val.wf_State (value_id (LAS_lid pinfo lasinfo))
           (LAS_value pinfo lasinfo) (PI_f pinfo) cfg1 IS1) stinfo Hp
  (Hsubst: substable_values (OpsemAux.CurTargetData cfg1) (OpsemAux.Globals cfg1)
             (PI_f pinfo) (value_id (LAS_lid pinfo lasinfo))
             (LAS_value pinfo lasinfo))
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo)
  (Halst: alive_store.wf_State pinfo stinfo cfg1 IS1)
  (Hstsim : State_simulation pinfo lasinfo cfg1 IS1 cfg2 IS2) maxb
  (Hless: 0 <= maxb) (Hwfgs: MemProps.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hstsim : State_simulation pinfo lasinfo cfg1 IS1 cfg2 IS2)
  (Hdiv : Opsem.sop_diverges cfg2 IS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  Opsem.sop_diverges cfg1 IS1 tr.
Proof.
  cofix CIH.
  intros.
  inv Hdiv.
  eapply sop_plus__las_State_simulation in Hstsim; eauto 1.
  destruct Hstsim as [FS1 [Hopplus Hstsim']].
  econstructor; eauto.
  assert (wf_State (value_id (LAS_lid pinfo lasinfo)) (LAS_value pinfo lasinfo)
     (PI_f pinfo) cfg1 FS1) as HwfS1'.
    eapply id_rhs_val_preservation_plus; eauto.
      eapply las__alive_store__vev; eauto.
  eapply CIH in Hstsim'; eauto using
    palloca_props.preservation_plus, Promotability.preservation_plus,
    (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus,
    alive_store.preservation_plus.
Qed.

Lemma find_st_ld__lasinfo: forall l0 ps0 cs0 tmn0 i0 v cs (pinfo:PhiInfo) dones
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo)) 
  (Hwfpi: WF_PhiInfo pinfo)
  s m (HwfF: wf_fdef s m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo))
  (HBinF : blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true),
  exists lasinfo:LASInfo pinfo,
    LAS_lid pinfo lasinfo = i1 /\
    LAS_sid pinfo lasinfo = i0 /\
    LAS_value pinfo lasinfo = v /\
    LAS_block pinfo lasinfo = (block_intro l0 ps0 cs0 tmn0).
Proof.
  intros.
  assert (exists tail, exists lalign, exists salign, 
            las i1 i0 lalign salign v tail (block_intro l0 ps0 cs0 tmn0) pinfo)
    as Hlas. 
    unfold las.
    apply find_init_stld_inl_spec in Hst.
    destruct Hst as [cs1 [ty1 [al1 Hst]]]; subst.
    apply find_next_stld_inl_spec in Hld.
    destruct Hld as [cs2 [cs3 [tl2 [al2 [Hld J]]]]]; subst.
    exists cs2. exists al2. exists al1.
    split; auto.
    split; auto.
    exists cs1. exists cs3.
      assert (J':=HBinF).
      eapply WF_PhiInfo_spec24 in J'; eauto.
      match goal with
      | H1 : context [?A ++ ?b :: ?C ++ ?d :: ?E] |- _ =>
        rewrite_env ((A ++ b :: C) ++ d :: E) in H1;
        eapply WF_PhiInfo_spec23 in H1; eauto
      end.
      subst. auto.
  destruct Hlas as [tail [lal [sal Hlas]]].
  exists 
    (mkLASInfo pinfo i1 i0 lal sal v tail (block_intro l0 ps0 cs0 tmn0) Hlas).
  auto.
Qed.

Lemma las_sim: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo)
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  S2 (Heq2: S2=[module_intro los nts
                (Ps1 ++
                  product_fdef
                    (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
                  :: Ps2)])
  (Hok: defined_program S2 main VarArgs)
  (HwfS : wf_system S2)
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (subst_fdef i1 v
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) :: Ps2)]
    S2 main VarArgs.
Proof.
  intros. subst.
  assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true)
    as HBinF.
    rewrite Heq. simpl. apply InBlocksB_middle.
  assert (wf_fdef [module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)]
            (module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)) 
            (PI_f pinfo) /\ uniqFdef (PI_f pinfo)) as J.
    rewrite Heq in *.
    apply wf_single_system__wf_uniq_fdef; auto.
  destruct J as [HwfF HuniqF].
  eapply find_st_ld__lasinfo in HBinF; eauto.
  destruct HBinF as [lasinfo [J1 [J2 [J3 J4]]]]; subst.

  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation pinfo lasinfo
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (subst_fdef (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo)
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))
         :: Ps2)]) as Hssim.
    constructor; auto.
    repeat split; auto.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    unfold TopSim.products_simulation. unfold fsim. unfold Fsim.
    apply uniq_products_simulation; auto.

Ltac las_sim_init :=
match goal with
| H: Opsem.s_genInitState [module_intro ?los ?nts _] _ _ _ = Some (?cfg, ?IS),  
  pinfo: PhiInfo, lasinfo: LASInfo _
  |- _ =>
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg IS) as Hwfst';
      try solve [eapply s_genInitState__opsem_wf in H; eauto using las_wfS];
    eapply s_genInitState__las_State_simulation in H; eauto;
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]];
    assert (OpsemPP.wf_Config cfg1 /\ OpsemPP.wf_State cfg1 IS1) as Hwfst;
      try solve [eapply s_genInitState__opsem_wf; eauto];
    assert (substable_values (OpsemAux.CurTargetData cfg1) (OpsemAux.Globals cfg1)
      (PI_f pinfo) (value_id (LAS_lid pinfo lasinfo)) (LAS_value pinfo lasinfo)) 
      as Hdom; try solve [
      assert ((los,nts) = OpsemAux.CurTargetData cfg1) as EQ;
        try solve [eapply s_genInitState__targedata; eauto];
      rewrite <- EQ;
      eapply LAS_substable_values; eauto
      ];
    assert (id_rhs_val.wf_State (value_id (LAS_lid pinfo lasinfo))
              (LAS_value pinfo lasinfo) (PI_f pinfo) cfg1 IS1) as Hisrhsval;
      try solve [eapply s_genInitState__id_rhs_val; eauto];
    assert (exists maxb,
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom;
      try solve [eapply Promotability.s_genInitState__wf_globals_promotable; eauto];
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]];
    remember (lasinfo__stinfo pinfo lasinfo) as R;
    destruct R as [stinfo Hp];
    assert (alive_store.wf_State pinfo stinfo cfg1 IS1) as Halst;
      try solve [eapply s_genInitState__alive_store; eauto]
end.

Ltac las_sim_end :=
 match goal with
| Hstsim' : State_simulation ?pinfo ?lasinfo ?cfg1 ?FS1 ?cfg ?FS,
  Hopstar1 : Opsem.sop_star ?cfg1 _ ?FS1 _ |- _ =>
    assert (OpsemPP.wf_State cfg FS) as Hwfst''; 
      try solve [eapply OpsemPP.preservation_star; eauto; try tauto];
    assert (OpsemPP.wf_State cfg1 FS1) as Hwfst1'';
      try solve [eapply OpsemPP.preservation_star; eauto; try tauto];
    assert (wf_State (value_id (LAS_lid pinfo lasinfo)) (LAS_value pinfo lasinfo)
      (PI_f pinfo) cfg1 FS1); try solve [
      eapply id_rhs_val_preservation_star in Hopstar1; eauto; try solve [
        tauto |
        eapply las__alive_store__vev; eauto; try tauto
      ]
    ]
end.

  constructor; auto.
    intros tr t Hconv.
    inv Hconv.
    las_sim_init.
    eapply sop_star__las_State_simulation in Hstsim; 
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    las_sim_end.
    match goal with
    | Hstsim' : State_simulation _ _ _ _ ?cfg ?FS,
      H: Opsem.s_isFinialState ?cfg ?FS = _ |- _ =>
      eapply s_isFinialState__las_State_simulation in Hstsim'; eauto; try tauto;
      rewrite <- Hstsim' in H
    end.
    exists t. split; auto using result_match_relf. econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    las_sim_init.
    eapply sop_div__las_State_simulation in Hstsim;  
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.

    intros tr t Hgowrong.
    inv Hgowrong.
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg t) as HwfSt.
      eapply s_genInitState__opsem_wf in H; eauto using las_wfS.
      destruct H as [Hcfg2 HwfSt2].
      apply OpsemPP.preservation_star in H0; auto.
    assert (OpsemPP.undefined_state cfg t) as Hundef.
      apply stuck__undefined_state in H2; try solve [auto | tauto].
    las_sim_init.
    eapply sop_star__las_State_simulation in Hstsim;
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    assert (Hprom':=Hprom).
    eapply Promotability.preservation_star in Hprom'; eauto; try tauto.
    las_sim_end.
    assert (OpsemPP.undefined_state cfg1 FS1) as Hundef'.
      eapply undefined_state__las_State_simulation_r2l in Hundef; 
        try solve [eauto | tauto].
    assert (Opsem.s_isFinialState cfg1 FS1 = merror) as Hfinal'.
      erewrite <- s_isFinialState__las_State_simulation in H2; 
        try solve [eauto | tauto].
    apply undefined_state__stuck' in Hundef'.
    exists tr. exists FS1.
    econstructor; eauto.
Qed.
