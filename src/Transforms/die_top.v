Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Maps.
Require Import opsem_props.
Require Import primitives.
Require Import memory_sim.
Require Import memory_props.
Require Import program_sim.
Require Import palloca_props.
Require Import top_sim.
Require Import trans_tactic.
Require Import die.
Require Import die_wfS.

(* This file proves that DIE refines programs by top_sim. *)

Lemma s_genInitState__die_State_simulation':
  forall diinfo S1 S2 main VarArgs cfg2 IS2,
  system_simulation diinfo S1 S2 ->
  Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2) ->
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation diinfo cfg1 IS1 cfg2 IS2 /\
    genericvalues_inject.wf_globals (Mem.nextblock (Opsem.Mem IS1) - 1) 
      (OpsemAux.Globals cfg1).
Proof.
  s_genInitState__State_simulation_tac.
  assert (J:=HeqR2).
  eapply RemoveSim.getEntryBlock__simulation in J; eauto.
  destruct J as [b1 [J5 J6]].
  fill_ctxhole.
  destruct b1 as [l2 [ps2 cs2 tmn2]].
  assert (J:=Hfsim).
  apply RemoveSim.fdef_simulation__eq_fheader in J.
  inv J.
  fill_ctxhole. eauto.
  match goal with
  | |- exists _:_, exists _:_, Some (?A, ?B) = _ /\ _ => exists A; exists B
  end.
  assert (J:=J6).
  apply RemoveSim.block_simulation_inv in J.
  destruct J as [J1 [J2 [J3 J7]]]; subst.
  split; auto.
  eapply genGlobalAndInitMem__wf_globals_Mem in HeqR1; eauto.
  destruct HeqR1 as [J7 [J8 [J9 [J10 [J11 [J12 [J13 J14]]]]]]].
  repeat (split; auto).
    exists l0. exists ps2. exists nil. auto.
    exists l0. exists ps0. exists nil. auto.
      unfold reg_simulation.
      destruct_if.
    simpl.
    apply MemProps.redundant__wf_globals; auto. 
    tauto.
Qed.

Lemma s_genInitState__die_State_simulation:
  forall diinfo S1 S2 main VarArgs cfg2 IS2
  (Hstsim: system_simulation diinfo S1 S2)
  (Hinit: Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2)),
  exists maxb, exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation diinfo cfg1 IS1 cfg2 IS2 /\
    genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1) /\
    0 <= maxb.
Proof.
  intros.
  eapply s_genInitState__die_State_simulation' in Hinit; eauto.
  destruct Hinit as [cfg1 [IS1 [J1 [J2 J3]]]].
  exists (Mem.nextblock (Opsem.Mem IS1) - 1).
  exists cfg1. exists IS1.
  split; auto.
  split; auto.
  split; auto.
    assert (J:=Mem.nextblock_pos (Opsem.Mem IS1)).
    omega.
Qed.

Ltac s_isFinialState__die_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal := 
  destruct cfg2 as [S2 [los2 nts2] gl2 fs2];
  destruct cfg1 as [S1 [los1 nts1] gl1 fs1];
  destruct FS1 as [[|[? ? cs1 ? ?] ES1]]; 
  destruct FS2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
    eauto 3 using result_match_relf |
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst; inv Hstsim
  ];
  destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
  inv X; simpl;
  destruct Hstsim as [Hstsim Hstsim'];
  fold ECs_simulation in Hstsim';
  destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
  destruct cs1, cs2; try solve [
    eauto 3 using result_match_relf |
    apply RemoveSim.cmds_simulation_nil_inv in Hstsim; try congruence |
    inv Hfinal
  ].

Ltac find_uniq_wf_fdef F :=
match goal with
| H1: InProductsB (product_fdef F) ?Ps = true,
  H2: moduleInSystemB (module_intro ?los ?nts ?Ps) ?S = true,
  H3: wf_system ?S |- _ =>
  let HwfF:=fresh "HwfF" in
  let HuniqF:=fresh "HuniqF" in
  assert (HwfF: wf_fdef S (module_intro los nts Ps) F) by 
    eauto 2 using wf_system__wf_fdef;
  assert (HuniqF: uniqFdef F) by eauto 2 using wf_system__uniqFdef
end.

Lemma s_isFinialState__die_State_simulation_l2r:
  forall diinfo cfg1 FS1 cfg2 FS2 r1
  (Hwfcfg2: OpsemPP.wf_Config cfg2) (Hwfpp2: OpsemPP.wf_State cfg2 FS2) 
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hnuse: runused_in_fdef (DI_id diinfo) (DI_f diinfo))
  (Hstsim : State_simulation diinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 = ret r1),
  Opsem.s_isFinialState cfg2 FS2 = ret r1.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__die_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
  destruct Terminator0; eauto 3 using result_match_relf.
    destruct ES1, ES2; try solve [eauto 3 using result_match_relf | inv Hstsim'].
      simpl in Hfinal.
      inTmnOp_isnt_stuck value5 H4 Hwfcfg2 Hwfpp2.
      destruct H3 as [l5 [ps2 [cs21 H3]]]; subst;
      destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
      destruct Hwfpp1 as 
          [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [_ _]]]]] _]].
      erewrite <- simulation__getOperandValue; eauto.
      eauto 3 using result_match_relf.
        find_uniq_wf_fdef CurFunction.
        value_doesnt_use_did_tac.

    destruct ES1, ES2; try solve [eauto 3 using result_match_relf | inv Hstsim'].
Qed.

Lemma s_isFinialState__die_State_simulation_l2r':
  forall diinfo cfg1 FS1 cfg2 FS2 
  (Hwfcfg2: OpsemPP.wf_Config cfg2) (Hwfpp2: OpsemPP.wf_State cfg2 FS2) 
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hnuse: runused_in_fdef (DI_id diinfo) (DI_f diinfo))
  (Hstsim : State_simulation diinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 <> None),
  Opsem.s_isFinialState cfg2 FS2 <> None.
Proof.
  intros.
  remember (Opsem.s_isFinialState cfg1 FS1) as R.
  destruct R; try congruence.
  symmetry_ctx.
  eapply s_isFinialState__die_State_simulation_l2r in Hstsim; eauto.
  destruct Hstsim as [r2 [Hstim Hinj]].
  congruence.
Qed.

Lemma s_isFinialState__die_State_simulation_None_r2l:
  forall diinfo cfg1 FS1 cfg2 FS2
  (Hwfcfg2: OpsemPP.wf_Config cfg2) (Hwfpp2: OpsemPP.wf_State cfg2 FS2) 
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hnuse: runused_in_fdef (DI_id diinfo) (DI_f diinfo))
  (Hstsim : State_simulation diinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = None),
  Opsem.s_isFinialState cfg1 FS1 = None.
Proof.
  intros.
  remember (Opsem.s_isFinialState cfg1 FS1) as R.
  destruct R; try congruence.
  contradict Hfinal.
  eapply s_isFinialState__die_State_simulation_l2r' in Hstsim; eauto.
    congruence.
Qed.

Lemma s_isFinialState__die_State_simulation_r2l':
  forall dinfo cfg1 FS1 cfg2 FS2 r2  
  (Hnuse: runused_in_fdef (DI_id dinfo) (DI_f dinfo))
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hstsim : State_simulation dinfo cfg1 FS1 cfg2 FS2)
  (Hnrem: ~removable_State dinfo FS1) 
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r2),
  Opsem.s_isFinialState cfg1 FS1 = ret r2.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__die_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
    destruct Terminator0; eauto 3 using result_match_relf.
      destruct ES1, ES2;try solve [eauto 3 using result_match_relf|inv Hstsim'].
        simpl in Hfinal.
        inTmnOp_isnt_stuck value5 H3 Hwfcfg1 Hwfpp1.
        destruct H3 as [l5 [ps2 [cs21 H3]]]; subst;
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as 
          [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [_ _]]]]] _]].
        erewrite simulation__getOperandValue; eauto.
        eauto 3 using result_match_relf.
          find_uniq_wf_fdef CurFunction.
          value_doesnt_use_did_tac.

      destruct ES1, ES2;try solve [eauto 3 using result_match_relf|inv Hstsim'].

   unfold removable_State in Hnrem.
   apply RemoveSim.not_removable_State_inv in Hnrem.
   apply RemoveSim.cmds_simulation_nelim_cons_inv in Hstsim; auto. 
   destruct Hstsim as [cs2' [J1 Hstsim]]; congruence.
Qed.

Lemma removable_State__non_removable_State' : forall dinfo f1 b1 c1 cs1 tmn1
  lc1 als1 ES1 M1 IS1'' tr0 Cfg1
  (Hex: exists l0, exists ps0, exists cs0, 
          b1 = (l0, stmts_intro ps0 (cs0 ++ c1 :: cs1) tmn1))
  (Huniq: uniqFdef f1) (HBinF: blockInFdefB b1 f1 = true)
  (Hrm : RemoveSim.removable_State (DI_f dinfo) (DI_id dinfo)
          {|
          Opsem.ECS := {|
                       Opsem.CurFunction := f1;
                       Opsem.CurBB := b1;
                       Opsem.CurCmds := c1 :: cs1;
                       Opsem.Terminator := tmn1;
                       Opsem.Locals := lc1;
                       Opsem.Allocas := als1 |} :: ES1;
          Opsem.Mem := M1 |})
  (Hop1 : Opsem.sInsn Cfg1
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f1;
                        Opsem.CurBB := b1;
                        Opsem.CurCmds := c1 :: cs1;
                        Opsem.Terminator := tmn1;
                        Opsem.Locals := lc1;
                        Opsem.Allocas := als1 |} :: ES1;
           Opsem.Mem := M1 |} IS1'' tr0),
  tr0 = E0 /\ ~ removable_State dinfo IS1''.
Proof.
  intros.
  assert (pure_insn (insn_cmd c1)) as Hpure.
    simpl in Hrm.
    destruct_if.
    destruct_dec; try tauto.
    apply (DI_pure dinfo); auto.
      destruct Hex as [l0 [ps0 [cs0 Hex]]]; subst.
      rewrite e0.
      solve_lookupCmdViaIDFromFdef.
  assert (NoDup (getCmdsLocs (c1 :: cs1))) as Hnodup.
    destruct Hex as [l0 [ps0 [cs0 Hex]]]; subst.
    apply uniqFdef__uniqBlockLocs in HBinF; auto.
    simpl in HBinF. split_NoDup. simpl_locs_in_ctx.
    split_NoDup. auto.
  inv Hop1; try solve [
    inv Hpure |
    split; try solve
      [auto | eapply RemoveSim.removable_State__non_removable_State; eauto]
  ].
Qed.

Lemma die_is_bsim_removable_steps : forall dinfo Cfg1 St1 Cfg2 St2
  (Hnuse: runused_in_fdef (DI_id dinfo) (DI_f dinfo))
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hsim: State_simulation dinfo Cfg1 St1 Cfg2 St2)
  (Hok: ~ sop_goeswrong Cfg1 St1),
  exists St1',
    Opsem.sop_star Cfg1 St1 St1' E0 /\
    State_simulation dinfo Cfg1 St1' Cfg2 St2 /\
    ~ removable_State dinfo St1'.
Proof.
  intros.
  destruct (@RemoveSim.removable_State_dec (DI_f dinfo) (DI_id dinfo) St1) 
    as [Hrm | Hnrm]; try solve  [exists St1; split; auto].
  destruct St1 as [[|[f1 b1 [|c1 cs1] tmn1 lc1 als1] ES1] M1]; tinv Hrm.
  assert (J:=Hwfpp).
  apply OpsemPP.progress in J; auto.
  assert (Hnfinal1:=Hrm).
  apply RemoveSim.removable_State__isnt__final with (cfg:=Cfg1) in Hnfinal1.
  destruct J as [Hfinal1 | [[IS1'' [tr0 Hop1]] | Hundef1]]; try congruence.
    eapply die_is_sim in Hsim; eauto.
    destruct Hsim as [Hstsim1 _].
    assert (tr0 = E0 /\ ~ removable_State dinfo IS1'') as Hnrm.
      apply wf_State__uniqECs in Hwfpp; auto.
      inv Hwfpp. destruct H1 as [J1 [J2 J3]]. simpl in *.
      eapply removable_State__non_removable_State' in Hop1; eauto.
    destruct Hnrm as [EQ Hnrm]; subst.
    eapply Hstsim1 in Hrm; eauto.
    destruct Hrm as [Hstsim EQ]; subst.
    exists IS1''.
    split; auto. 
      apply OpsemProps.sInsn__implies__sop_star; auto.

    apply undefined_state__stuck' in Hundef1.
    contradict Hok. 
    apply nonfinal_stuck_state_goes_wrong; auto.
Qed.

Lemma die_is_bsim_unremovable_step : forall dinfo Cfg1 IS1 Cfg2 IS2
  (Hnuse: runused_in_fdef (DI_id dinfo) (DI_f dinfo))
  (Hok : ~ sop_goeswrong Cfg1 IS1)
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 IS1)
  (Hnrm: ~ removable_State dinfo IS1)
  (Hstsim : State_simulation dinfo Cfg1 IS1 Cfg2 IS2) IS2' tr2
  (Hop2: Opsem.sInsn Cfg2 IS2 IS2' tr2)
  (Hwfcfg2: OpsemPP.wf_Config Cfg2) (Hwfpp2: OpsemPP.wf_State Cfg2 IS2),
  exists IS1' : Opsem.State,
    Opsem.sInsn Cfg1 IS1 IS1' tr2 /\
    State_simulation dinfo Cfg1 IS1' Cfg2 IS2'.
Proof.
  intros.
  assert (Hnfinal1: Opsem.s_isFinialState Cfg1 IS1 = merror).
    remember (Opsem.s_isFinialState Cfg1 IS1) as R.
    destruct R; auto.
    apply s_isFinialState__die_State_simulation_l2r' in Hstsim; 
      try solve [auto | congruence].
      contradict Hop2; eauto using s_isFinialState__stuck.
  assert (J:=Hwfpp).
  apply OpsemPP.progress in J; auto.
  destruct J as [Hfinal1 | [[IS1'' [tr0 Hop1]] | Hundef1]]; try congruence.
    assert (OpsemPP.wf_State Cfg1 IS1'') as Hwfpp''.
      apply OpsemPP.preservation in Hop1; auto.
    eapply die_is_sim in Hstsim; eauto.
    destruct Hstsim as [Hstsim1 Hstsim2].
    eapply Hstsim2 in Hnrm; eauto.
    destruct Hnrm as [Hstsim EQ]; subst.
    exists IS1''. 
    split; eauto.

    apply undefined_state__stuck' in Hundef1.
    contradict Hok.
    apply nonfinal_stuck_state_goes_wrong; auto.
Qed.

Lemma die_is_bsim : forall dinfo Cfg1 St1 Cfg2 St2
  (Hnuse: runused_in_fdef (DI_id dinfo) (DI_f dinfo))
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hsim: State_simulation dinfo Cfg1 St1 Cfg2 St2)
  (Hok: ~ sop_goeswrong Cfg1 St1)
  St2' tr2 (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2)
  (Hwfcfg2: OpsemPP.wf_Config Cfg2) (Hwfpp2: OpsemPP.wf_State Cfg2 St2),
  exists St1',
    Opsem.sop_plus Cfg1 St1 St1' tr2 /\
    State_simulation dinfo Cfg1 St1' Cfg2 St2'.
Proof.
  intros.
  eapply die_is_bsim_removable_steps in Hsim; eauto.
  destruct Hsim as [St1' [Hopstar [Hstsim Hnrm]]].
  eapply die_is_bsim_unremovable_step in Hstsim; eauto 2 using
      (@OpsemPP.preservation_star DGVs), sop_goeswrong__star.
  destruct Hstsim as [FS1 [Hopplus1 Hstsim]].
  exists FS1.
  split; auto.
    rewrite <- E0_left. 
    eapply OpsemProps.sop_star_plus__implies__sop_plus; eauto.
    apply OpsemProps.sInsn__implies__sop_plus; auto.
Qed.

Lemma s_isFinialState__die_State_simulation_r2l:
  forall diinfo cfg1 FS1 cfg2 FS2 r2
  (Hnuse: runused_in_fdef (DI_id diinfo) (DI_f diinfo))
  (Hwfcfg: OpsemPP.wf_Config cfg1) (Hwfpp: OpsemPP.wf_State cfg1 FS1)
  (Hstsim : State_simulation diinfo cfg1 FS1 cfg2 FS2)
  (Hok: ~ sop_goeswrong cfg1 FS1)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r2),
  exists FS1', 
    Opsem.sop_star cfg1 FS1 FS1' E0 /\
    State_simulation diinfo cfg1 FS1' cfg2 FS2 /\
   Opsem.s_isFinialState cfg1 FS1' = ret r2.
Proof.
  intros.
  eapply die_is_bsim_removable_steps in Hstsim; eauto.
  destruct Hstsim as [FS1' [Hopstar [Hstsim Hnrm]]].
  exists FS1'.
  split; auto.
  split; auto.
    eapply s_isFinialState__die_State_simulation_r2l' in Hstsim; 
      eauto using (@OpsemPP.preservation_star DGVs).
Qed.

Ltac undefined_state__State_simulation_r2l_tac1 :=
  match goal with
  | Hstsim: State_simulation _ _ ?St1 _ ?St2 |- _ =>
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
  | Hstsim: State_simulation _ _ ?St1 _ ?St2 |- _ =>
    destruct St2 as [[|[? [? [? ? tmn]] CurCmds tmn' ?] ?] ?]; try tauto;
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
  | Hstsim: State_simulation _ _ ?St1 ?cfg2 ?St2 |- _ =>
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X;
    destruct ECS as [|[? ? ? ? Locals0] ECS]; try tauto;
    destruct Hstsim as [Hstsim _];
    destruct Hstsim as [? [? [? [? [H4 [H5 [? Hstsim]]]]]]]; subst
  end. 

Ltac undefined_state__d_State_simulation_r2l_tac43 := 
      match goal with
      | Hstsim: cmds_simulation _ _ _ (_::_) |- _ =>
      eapply RemoveSim.cmds_simulation_cons_inv' in Hstsim; eauto; subst;
      destruct Hstsim as [c1' [J2 J3]]; subst
     end.

Ltac undefined_state__d_State_simulation_r2l_tac42 v' := 
match goal with
| Hwfcfg1: OpsemPP.wf_Config ?cfg1, Hwfpp1: OpsemPP.wf_State ?cfg1 ?St1, 
  H2: ret ?gn = Opsem.getOperandValue ?td v' ?Locals ?fs2,
  _: reg_simulation _ ?f ?Locals0 ?Locals,
  _: block_simulation _ ?f ?b _,
  H4: exists _:_, exists _:_, exists _:_, ?b = _ |- _ =>
    let G := fresh "G" in
    let gvs := fresh "gvs" in
    let EQ := fresh "EQ" in
    assert (exists gvs, Opsem.getOperandValue td
      v' Locals0 fs2 = Some gvs) as G; try solve [
      destruct H4 as [l5 [ps2 [cs21 H4]]]; subst;
      destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
      destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
      inv_mbind;
      eapply OpsemPP.getOperandValue_inCmdOps_isnt_stuck; eauto 1; simpl; auto
    ];
    destruct G as [gvs G]; symmetry in H2;
    assert (gvs = gn) as EQ; try solve [
      destruct H4 as [l1 [ps1 [cs11 H4]]]; subst;
      destruct Hwfcfg1 as [_ [_ [Hwfs1 HmInS1]]];
      destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 _]]] _]];
      match goal with
      | H1 : Opsem.getOperandValue _ v' ?Locals0 _ = ret _ |- _ =>
        erewrite simulation__getOperandValue in H1; try solve [
          eauto 2 | find_uniq_wf_fdef f; value_doesnt_use_did_tac
        ];
        uniq_result; auto
      end
    ]; subst
end.

Lemma stacked_frame__unremovable: forall cfg EC1 EC2 ECS Mem0 dinfo
  (Huniq: uniqEC EC2)
  (HBinF: match Opsem.CurBB EC1 with 
   | (_, stmts_intro _ _ (insn_return _ _ _)) => True
   | (_, stmts_intro _ _ (insn_return_void _)) => True
   | _ => False
   end)
  (Hwfpp1 : OpsemPP.wf_State cfg
             {| Opsem.ECS := EC1 :: EC2 :: ECS; Opsem.Mem := Mem0 |}),
  ~ removable_State dinfo
     {| Opsem.ECS := EC2 :: ECS; Opsem.Mem := Mem0 |}.
Proof.
  intros.
  destruct Huniq as [J1 [J2 J3]].
  destruct J3 as [l1 [ps0 [cs0 J3]]]; subst.
  destruct EC1, EC2; simpl in *. destruct cfg. destruct CurTargetData.
  destruct Hwfpp1 as 
     [_ [[_ [HbInF1 [_ [_ [_ _]]]]] [_ Hiscall]]].
  apply Hiscall in HbInF1.
  destruct CurBB as [? [? ? []]]; tinv HBinF;
    destruct CurCmds0 as [|[]]; try solve [
      inv HbInF1 |
      simpl; destruct_if; destruct_if;
      eapply dont_remove_impure_cmd with (dinfo:=dinfo) in J2; 
        eauto using in_middle; simpl; auto;
      simpl in J2; tauto
    ].
Qed.

Lemma undefined_state__die_State_simulation_r2l': forall dinfo cfg1 St1 cfg2
  St2 (Hstsim : State_simulation dinfo cfg1 St1 cfg2 St2) maxb
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hnuse: runused_in_fdef (DI_id dinfo) (DI_f dinfo))
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (Hnrem: ~removable_State dinfo St1) 
  (Hundef: OpsemPP.undefined_state cfg2 St2),
  OpsemPP.undefined_state cfg1 St1.
Proof.
  unfold removable_State.
  intros.
  assert (HuniqECs:=Hwfpp1). apply wf_State__uniqECs in HuniqECs; auto.
  unfold OpsemPP.undefined_state in Hundef.
  destruct cfg2 as [S2 [los2 nts2] gl2 fs2].
  destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
  repeat match goal with
  | Hundef : _ \/ _ |- _ => destruct Hundef as [Hundef | Hundef]
  end.
  Case "1".

    undefined_state__State_simulation_r2l_tac1.
    eapply RemoveSim.cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    assert (Hnrem' : ~
          removable_State dinfo
            {|
            Opsem.ECS := {|
                            Opsem.CurFunction := CurFunction2;
                            Opsem.CurBB := CurBB2;
                            Opsem.CurCmds := CurCmds1;
                            Opsem.Terminator := Terminator;
                            Opsem.Locals := Locals2;
                            Opsem.Allocas := Allocas0 |} :: ECS;
            Opsem.Mem := Mem |}).
      clear - Hwfpp1 H3 HuniqECs.
      destruct H3 as [l5 [ps5 [cs5 H5]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto; find_uniqEC.
    eapply RemoveSim.cmds_simulation_cons_inv' in Hnrem'; eauto.
    destruct Hnrem' as [cs1' [J1 J3]]; subst. auto.

  Case "2".
    undefined_state__State_simulation_r2l_tac1.
    eapply RemoveSim.cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    assert (Hnrem' : ~
          removable_State dinfo
            {|
            Opsem.ECS := {|
                            Opsem.CurFunction := CurFunction2;
                            Opsem.CurBB := CurBB2;
                            Opsem.CurCmds := CurCmds1;
                            Opsem.Terminator := Terminator;
                            Opsem.Locals := Locals2;
                            Opsem.Allocas := Allocas0 |} :: ECS;
            Opsem.Mem := Mem |}).
      clear - Hwfpp1 H3 HuniqECs.
      destruct H3 as [l5 [ps5 [cs5 H5]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto; find_uniqEC.
    eapply RemoveSim.cmds_simulation_cons_inv' in Hnrem'; eauto.
    destruct Hnrem' as [cs1' [J1 J3]]; subst.
    right. left. 
    destruct Hundef as [Hundef | Hundef]; auto.

  Case "3".
    undefined_state__State_simulation_r2l_tac3.
    eapply RemoveSim.cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    right. right. left. auto.

  Case "4".
    right; right; right; left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' Locals] ?] ?]; try solve [
      tauto |
      inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind;
      undefined_state__State_simulation_r2l_tac41;
      undefined_state__d_State_simulation_r2l_tac43;
      undefined_state__d_State_simulation_r2l_tac42 value5; 
      repeat fill_ctxhole; exists gn; split; auto;
      fill_ctxhole; auto
    ].

  Case "5".
    right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43.
    undefined_state__d_State_simulation_r2l_tac42 value5.
    repeat fill_ctxhole; exists gn. split; auto.
    fill_ctxhole; auto.
   
  Case "6".
    right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gvs [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43. 
    undefined_state__d_State_simulation_r2l_tac42 value1.
    repeat fill_ctxhole; exists gvs. split; auto.
    fill_ctxhole; auto.

  Case "7".
    right. right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gv [mgv [EQ1 [EQ2 Hundef]]]]; 
      inv EQ1; inv EQ2; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43. 
    undefined_state__d_State_simulation_r2l_tac42 value1.
    undefined_state__d_State_simulation_r2l_tac42 value2.
    repeat fill_ctxhole; exists gv; exists mgv.
    split; auto.
    fill_ctxhole; auto.

  Case "8".
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    right; right; right; right. right. right. right.
    undefined_state__State_simulation_r2l_tac41.
    inv_mbind.
    destruct Hundef as [fptr [EQ Hundef]]; inv EQ.
    inv_mbind.
    eapply RemoveSim.cmds_simulation_cons_inv' in Hstsim; subst; eauto.
    destruct Hstsim as [cs2' [J1 J2]]; subst.
    undefined_state__d_State_simulation_r2l_tac42 value0.
    repeat fill_ctxhole.
    exists fptr. split; auto.
    remember (OpsemAux.lookupExFdecViaPtr gl2 FunTable fptr) as R.
    destruct R as [[[]]|].
      inv_mbind.
      destruct Hundef as [gvs0 [EQ' Hundef]].
      dgvs_instantiate_inv.
      assert (exists gvs, 
                Opsem.params2GVs (los2,nts2) params5 Locals0 fs2 = Some gvs) as G'.
        destruct H4 as [l5 [ps2 [cs21 H4]]]; subst.
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]].
        inv_mbind.
        eapply OpsemPP.params2GVs_isnt_stuck; eauto 1; simpl; auto.
          exists nil. auto.
      destruct G' as [gvs' G'].
      assert (gvs' = l1) as EQ2.
        erewrite reg_simulation__params2GVs in G'; eauto.  
          symmetry_ctx. uniq_result. auto.

          destruct H4 as [l5 [ps1 [cs11 H4]]]; subst;
          destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
          destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
          find_uniq_wf_fdef CurFunction0;
          eapply conditional_runused_in_fdef__used_in_params; destruct dinfo; eauto 1.

      subst.
      repeat fill_ctxhole.
      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_r2l; eauto.
      simpl.
      exists l1. split; auto.
        destruct (callExternalOrIntrinsics (los2, nts2) fs2 Mem id0 typ0
               (args2Typs args5) deckind5 l1) as [[[]]|]; auto.
        remember (Opsem.exCallUpdateLocals (los2, nts2) typ5 noret5 id5 o Locals) 
          as R.
        destruct R; tinv Hundef.
          unfold Opsem.exCallUpdateLocals in *.
          destruct_if.
          destruct o; auto.
          destruct (fit_gv (los2, nts2) typ5 g); auto.
            congruence.
    
      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_None_r2l; eauto.
Qed.

Lemma undefined_state__die_State_simulation_r2l: forall dinfo cfg1 St1 cfg2 maxb
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hnuse: runused_in_fdef (DI_id dinfo) (DI_f dinfo))
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  St2 (Hstsim : State_simulation dinfo cfg1 St1 cfg2 St2)
  (Hundef: OpsemPP.undefined_state cfg2 St2)
  (Hok: ~ sop_goeswrong cfg1 St1),
  exists St1',
    Opsem.sop_star cfg1 St1 St1' E0 /\
    State_simulation dinfo cfg1 St1' cfg2 St2 /\
    OpsemPP.undefined_state cfg1 St1'.
Proof.
  intros.
  eapply die_is_bsim_removable_steps in Hstsim; eauto.
  destruct Hstsim as [FS1' [Hopstar [Hstsim Hnrm]]].
  exists FS1'. 
  split; auto.
  split; auto.
    eapply undefined_state__die_State_simulation_r2l' in Hstsim; 
      eauto using (@OpsemPP.preservation_star DGVs).
Qed.

Lemma sop_star__die_State_simulation: forall diinfo cfg1 IS1 cfg2 IS2 tr FS2 
  (Hwfpp1: OpsemPP.wf_State cfg1 IS1) (Hwfcfg1: OpsemPP.wf_Config cfg1)
  (Hwfpp2: OpsemPP.wf_State cfg2 IS2) (Hwfcfg2: OpsemPP.wf_Config cfg2) maxb
  (Hwfg: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hless: 0 <= maxb) (Hnuse: runused_in_fdef (DI_id diinfo) (DI_f diinfo))
  (Hstsim : State_simulation diinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\
    State_simulation diinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent cfg1.
  generalize dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    assert (forall IS1'
            (Hok' : ~ sop_goeswrong cfg1 IS1')
            (Hwfpp': OpsemPP.wf_State cfg1 IS1')
            (Hnrm': ~ removable_State diinfo IS1')
            (Hstsim' : State_simulation diinfo cfg1 IS1' cfg2 state1),
            exists FS1 : Opsem.State,
              Opsem.sop_star cfg1 IS1' FS1 (tr1 ** tr2) /\
              State_simulation diinfo cfg1 FS1 cfg2 state3) as W1.
      clear - H Hopstar IHHopstar Hwfcfg1 Hless Hwfg Hnuse Hwfcfg2
              Hwfpp2. 
      intros.
      assert (Hwfpp2':=H). apply OpsemPP.preservation in Hwfpp2'; auto.
      eapply die_is_bsim in H; eauto 2.
      destruct H as [St1' [Hplus1 Hstsim]].
      eapply IHHopstar in Hstsim;
        eauto using (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
      destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
      exists FS1.
      split; auto.
        eapply OpsemProps.sop_star_trans; eauto.
        apply OpsemProps.sop_plus__implies__sop_star; eauto.

    eapply die_is_bsim_removable_steps in Hstsim;
      eauto using (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
    destruct Hstsim as [St1' [Hopstar1 [Hstsim Hnrm]]].
    eapply OpsemPP.preservation_star in Hwfpp1; eauto.
    eapply sop_goeswrong__star in Hok; eauto.
    eapply W1 in Hstsim; eauto.
    destruct Hstsim as [FS1 [Hopstar'' Hstsim]].
    exists FS1.
    split; auto.
      clear - Hopstar1 Hopstar''.
      rewrite <- E0_left.
      eapply OpsemProps.sop_star_trans; eauto.
Qed.

Lemma sop_plus__die_State_simulation: forall dinfo cfg1 IS1 cfg2 IS2 tr
  FS2 maxb
  (Hwfpp1: OpsemPP.wf_State cfg1 IS1) (Hwfcfg1: OpsemPP.wf_Config cfg1)
  (Hwfpp2: OpsemPP.wf_State cfg2 IS2) (Hwfcfg2: OpsemPP.wf_Config cfg2)
  (Hwfg: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hless: 0 <= maxb) (Hnuse: runused_in_fdef (DI_id dinfo) (DI_f dinfo))
  (Hstsim : State_simulation dinfo cfg1 IS1 cfg2 IS2)
  (Hopplus : Opsem.sop_plus cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, Opsem.sop_plus cfg1 IS1 FS1 tr /\
    State_simulation dinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  inv Hopplus.
  assert (Hwfpp2':=H). apply OpsemPP.preservation in Hwfpp2'; auto.
  eapply die_is_bsim with (Cfg1:=cfg1) in H; eauto.
  destruct H as [St1' [Hplus1 Hstsim']].
  eapply sop_star__die_State_simulation in Hstsim'; eauto using
    (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
  destruct Hstsim' as [FS1 [Hopstar Hstsim']].
  exists FS1.
  split; auto.
    eapply OpsemProps.sop_plus_star__implies__sop_plus; eauto.
Qed.

Lemma sop_div__die_State_simulation: forall dinfo cfg1 IS1 cfg2 IS2 tr maxb
  (Hwfpp1: OpsemPP.wf_State cfg1 IS1) (Hwfcfg1: OpsemPP.wf_Config cfg1)
  (Hwfpp2: OpsemPP.wf_State cfg2 IS2) (Hwfcfg2: OpsemPP.wf_Config cfg2)
  (Hwfg: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hless: 0 <= maxb) (Hnuse: runused_in_fdef (DI_id dinfo) (DI_f dinfo))
  (Hstsim : State_simulation dinfo cfg1 IS1 cfg2 IS2)
  (Hdiv : Opsem.sop_diverges cfg2 IS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  Opsem.sop_diverges cfg1 IS1 tr.
Proof.
  cofix CIH.
  intros.
  inv Hdiv.
  eapply sop_plus__die_State_simulation in Hstsim; eauto 1.
  destruct Hstsim as [FS1 [Hopplus Hstsim']].
  econstructor; eauto.
  eapply CIH in Hstsim'; eauto using
    (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
Qed.

Require Import Program.Tactics.

(* The main result *)
Lemma die_sim: forall id0 f dinfo los nts Ps1 Ps2 main VarArgs
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hok: defined_program [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
          main VarArgs)
  (Heq1: f = DI_f dinfo) (Heq2: id0 = DI_id dinfo),
  program_sim
    [module_intro los nts
      (Ps1 ++  product_fdef (remove_fdef id0 f) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Proof.
  intros. subst.
  assert (Hnuse: runused_in_fdef (DI_id dinfo) (DI_f dinfo)).  
    destruct dinfo. auto.
  set (wf_prop1 := fun cfg st =>
         OpsemPP.wf_Config cfg /\ @OpsemPP.wf_State DGVs cfg st /\
         exists maxb,
           genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg) /\
           0 <= maxb).
  set (wf_prop2 := fun cfg st =>
         OpsemPP.wf_Config cfg /\ @OpsemPP.wf_State DGVs cfg st).
  set (st_sim := fun cfg1 st1 cfg2 st2 => 
          State_simulation dinfo cfg1 st1 cfg2 st2).
  set (sys_sim := fun s1 s2 => system_simulation dinfo s1 s2).
  apply top_sim with (ftrans:=remove_fdef (DI_id dinfo)) 
    (wf_prop1:=wf_prop1) (wf_prop2:=wf_prop2) (state_simulation:=st_sim)
    (system_simulation:=sys_sim); 
     try solve [auto | unfold wf_prop1; tauto | unfold wf_prop2; tauto |
      unfold wf_prop1, wf_prop2; intros; destruct_conjs; try solve [
        eauto 6 using (@OpsemPP.preservation_star DGVs) |
        eapply sop_star__die_State_simulation; eauto |
        eapply s_isFinialState__die_State_simulation_r2l; eauto |
        eapply sop_div__die_State_simulation; eauto |
        eapply undefined_state__die_State_simulation_r2l; eauto |
        eapply s_isFinialState__die_State_simulation_None_r2l; eauto
      ] |
      top_sim_syssim_tac fsim Fsim
    ].

    intros. subst.
    assert (OpsemPP.wf_Config cfg2 /\ OpsemPP.wf_State cfg2 IS2) as Hwfst'.
      eapply s_genInitState__opsem_wf in Hinit; eauto using die_wfS.
    eapply s_genInitState__die_State_simulation in Hinit; eauto.
    destruct Hinit as [maxb [cfg1 [IS1 [Hinit1 [Hstsim [Hwfg Hless]]]]]].
    assert (OpsemPP.wf_Config cfg1/\ OpsemPP.wf_State cfg1 IS1) as Hwfst.
      eapply s_genInitState__opsem_wf; eauto.
    destruct Hwfst.
    unfold wf_prop1, wf_prop2.
    eauto 10.
Qed.
