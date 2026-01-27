Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import opsem_props.
Require Import promotable_props.
Require Import primitives.
Require Import palloca_props.
Require Import memory_props.
Require Import memory_sim.
Require Import genericvalues_inject.
Require Import program_sim.
Require Import trans_tactic.
Require Import top_sim.
Require Import dae_defs.
Require Import dae.
Require Import dae_wfS.

(* This file proves that DAE refines programs by top_sim. *)

Lemma s_genInitState__dae_State_simulation': forall pinfo S1 S2 main VarArgs cfg2
  IS2 (Hssym: system_simulation pinfo S1 S2) (HwfS: wf_system S1) 
  (Hwfpi: WF_PhiInfo pinfo)
  (Hinit: Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2)),
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo (Mem.nextblock (Opsem.Mem IS1) - 1)
      (MemProps.inject_init (Mem.nextblock (Opsem.Mem IS1) - 1)) cfg1 IS1 cfg2 IS2 /\
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
  split.
    simpl.
    repeat (split; auto).
    exists l0. exists ps2. exists nil. auto.
    exists l0. exists ps0. exists nil. auto.
      unfold reg_simulation.
      destruct_if.
        intros.
        destruct_if.
          intros. uniq_result. eauto.
        intros. uniq_result. eauto.
        
      intros.
      contradict H. 
      unfold isnt_alloca_in_ECs, is_alloca_in_EC.
      intros. simpl in Hin.
      destruct Hin as [HIn | Hin]; try tauto.
      inv HIn. 
      destruct_if.
      assert (lookupAL (GVsT DGVs) lc (PI_id pinfo) = None) as Hnoin.
        assert (Huniq: uniqFdef (PI_f pinfo)).
          rewrite e.
          eauto using wf_system__uniqFdef.
        eapply WF_PhiInfo__pid_isnt_in_init; eauto.
          rewrite e. eauto.
      fill_ctxhole. auto.

    simpl.
    apply MemProps.redundant__wf_globals; auto. 
    tauto.
Qed.

Lemma s_genInitState__dae_State_simulation: forall pinfo S1 S2 main VarArgs cfg2
  IS2 (Hssym: system_simulation pinfo S1 S2) (HwfS: wf_system S1) 
  (Hwfpi: WF_PhiInfo pinfo)
  (Hinit: Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2)),
  exists maxb, exists mi, exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo maxb mi cfg1 IS1 cfg2 IS2 /\
    genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1) /\
    MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\
    0 <= maxb /\
    Promotability.wf_State maxb pinfo cfg1 IS1.
Proof.
  intros.
  eapply s_genInitState__dae_State_simulation' in Hinit; eauto.
  destruct Hinit as [cfg1 [IS1 [J1 [J2 J3]]]].
  exists (Mem.nextblock (Opsem.Mem IS1) - 1).
  exists (MemProps.inject_init (Mem.nextblock (Opsem.Mem IS1) - 1)).
  exists cfg1. exists IS1.
  split; auto.
  split; auto.
  split; auto.
    eapply Promotability.s_genInitState__wf_globals_promotable' with (S:=S1)
      (main:=main)(VarArgs:=VarArgs); eauto.
Qed.

Ltac s_isFinialState__dae_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal := 
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

Lemma s_isFinialState__dae_State_simulation_l2r: forall maxb mi pinfo cfg1 FS1 cfg2
  FS2 r1
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hwfcfg2: OpsemPP.wf_Config cfg2) (Hwfpp2: OpsemPP.wf_State cfg2 FS2) 
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hstsim : State_simulation pinfo maxb mi cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 = ret r1),
  exists r2, Opsem.s_isFinialState cfg2 FS2 = ret r2 /\ result_match r1 r2.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__dae_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
  destruct Terminator0; eauto 3 using result_match_relf.
    destruct ES1, ES2; try solve [eauto 3 using result_match_relf | inv Hstsim'].
      simpl in Hfinal.
      inTmnOp_isnt_stuck value5 H6 Hwfcfg2 Hwfpp2.
      destruct H2 as [_ [_ H2]].
      destruct H5 as [l5 [ps2 [cs21 H5]]]; subst;
      destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
      destruct Hwfpp1 as 
          [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [_ _]]]]] _]].
      assert (wf_value S1 (module_intro los2 nts2 gl1) CurFunction value5 typ5) 
        as Hwft.
        get_wf_value_for_simop'. eauto.
      assert (value_doesnt_use_pid pinfo CurFunction value5) as Hnotin.
        eapply conditional_used_in_fdef__used_in_tmn_value; eauto 1; simpl; auto.
      eapply simulation__getOperandValue in H7; eauto.
      apply gv_inject__result_match in H7. eauto.

    destruct ES1, ES2; try solve [eauto 3 using result_match_relf | inv Hstsim'].
Qed.

Lemma s_isFinialState__dae_State_simulation_l2r': forall maxb mi pinfo cfg1 FS1 cfg2
  FS2 
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hwfcfg2: OpsemPP.wf_Config cfg2) (Hwfpp2: OpsemPP.wf_State cfg2 FS2) 
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hstsim : State_simulation pinfo maxb mi cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 <> None),
  Opsem.s_isFinialState cfg2 FS2 <> None.
Proof.
  intros.
  remember (Opsem.s_isFinialState cfg1 FS1) as R.
  destruct R; try congruence.
  symmetry_ctx.
  eapply s_isFinialState__dae_State_simulation_l2r in Hstsim; eauto.
  destruct Hstsim as [r2 [Hstim Hinj]].
  congruence.
Qed.

Lemma s_isFinialState__dae_State_simulation_None_r2l:
  forall pinfo cfg1 FS1 cfg2 FS2 maxb mi
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hwfcfg2: OpsemPP.wf_Config cfg2) (Hwfpp2: OpsemPP.wf_State cfg2 FS2) 
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hstsim : State_simulation pinfo maxb mi cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = None),
  Opsem.s_isFinialState cfg1 FS1 = None.
Proof.
  intros.
  remember (Opsem.s_isFinialState cfg1 FS1) as R.
  destruct R; try congruence.
  contradict Hfinal.
  eapply s_isFinialState__dae_State_simulation_l2r' in Hstsim; eauto.
    congruence.
Qed.

Lemma s_isFinialState__dae_State_simulation_r2l':
  forall pinfo cfg1 FS1 cfg2 FS2 r2 maxb mi 
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hstsim : State_simulation pinfo maxb mi cfg1 FS1 cfg2 FS2)
  (Hnrem: ~removable_State pinfo FS1) 
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r2),
  exists r1, Opsem.s_isFinialState cfg1 FS1 = ret r1 /\ result_match r1 r2.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__dae_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
    destruct Terminator0; eauto 3 using result_match_relf.
      destruct ES1, ES2;try solve [eauto 3 using result_match_relf|inv Hstsim'].
        simpl in Hfinal.
        inTmnOp_isnt_stuck value5 H5 Hwfcfg1 Hwfpp1.
        destruct H2 as [_ [_ H2]].
        destruct H5 as [l5 [ps2 [cs21 H5]]]; subst;
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as 
          [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [_ _]]]]] _]].
        assert (wf_value S1 (module_intro los2 nts2 gl1) CurFunction value5 typ5) 
          as Hwft.
          get_wf_value_for_simop'. eauto.
        assert (value_doesnt_use_pid pinfo CurFunction value5) as Hnotin.
          eapply conditional_used_in_fdef__used_in_tmn_value; eauto 1; simpl; auto.
        eapply simulation__getOperandValue in H7; eauto.
        apply gv_inject__result_match in H7. eauto.

      destruct ES1, ES2; 
        try solve [eauto 3 using result_match_relf | inv Hstsim'].

   unfold removable_State in Hnrem.
   apply RemoveSim.not_removable_State_inv in Hnrem.
   apply RemoveSim.cmds_simulation_nelim_cons_inv in Hstsim; auto. 
   destruct Hstsim as [cs2' [J1 Hstsim]]; congruence.
Qed.

Lemma dae_is_bsim_removable_steps : forall maxb pinfo Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) mi 
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals Cfg1))
  (Hinbd: 0 <= maxb) (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1)
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hsim: State_simulation pinfo maxb mi Cfg1 St1 Cfg2 St2)
  (Hok: ~ sop_goeswrong Cfg1 St1),
  exists St1', exists mi',
    Opsem.sop_star Cfg1 St1 St1' E0 /\
    State_simulation pinfo maxb mi' Cfg1 St1' Cfg2 St2 /\
    ~ removable_State pinfo St1' /\
    Values.inject_incr mi mi'.
Proof.
  intros.
  destruct (@RemoveSim.removable_State_dec (PI_f pinfo) (PI_id pinfo) St1) 
    as [Hrm | Hnrm]; try solve 
      [exists St1; exists mi; split; auto using inject_incr_refl].
  destruct St1 as [[|[f1 b1 [|c1 cs1] tmn1 lc1 als1] ES1] M1]; tinv Hrm.
  assert (J:=Hwfpp).
  apply OpsemPP.progress in J; auto.
  assert (Hnfinal1:=Hrm).
  apply RemoveSim.removable_State__isnt__final with (cfg:=Cfg1) in Hnfinal1.
  destruct J as [Hfinal1 | [[IS1'' [tr0 Hop1]] | Hundef1]]; try congruence.
    eapply dae_is_sim in Hsim; eauto.
    destruct Hsim as [Hstsim1 _].
    assert (~ removable_State pinfo IS1'') as Hnrm.
      assert (c1 = insn_alloca (PI_id pinfo) (PI_typ pinfo) 
               (PI_num pinfo) (PI_align pinfo)) as EQ.
        destruct Cfg1 as [? [] ? ?].
        destruct Hwfcfg as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp as 
          [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [_ [l1 [ps1 [cs1' EQ]]]]]]]] _]]; 
          subst.
        apply RemoveSim.removable_State_inv in Hrm; auto. destruct Hrm; subst.
        eapply WF_PhiInfo_spec1'; eauto 2 using wf_system__uniqFdef.
      subst.
      inv Hop1.
      eapply RemoveSim.removable_State__non_removable_State; eauto.
        apply wf_State__wfECs_inv in Hwfpp; auto.
        simpl in Hwfpp. clear - Hwfpp.
        inv Hwfpp. 
        destruct H1 as [A [B [C [l0 [ps0 [cs0 D]]]]]]. simpl in *. subst.
        apply uniqFdef__uniqBlockLocs in B; auto. simpl in B.
        split_NoDup. simpl_locs_in_ctx. split_NoDup. simpl_locs_in_ctx. auto.
    eapply Hstsim1 in Hrm; eauto.
    destruct Hrm as [mi' [Hstsim [EQ Hinc]]]; subst.
    exists IS1''. exists mi'.
    split; auto. 
      apply OpsemProps.sInsn__implies__sop_star; auto.

    apply undefined_state__stuck' in Hundef1.
    contradict Hok. 
    apply nonfinal_stuck_state_goes_wrong; auto.
Qed.

Lemma dae_is_bsim_unremovable_step : forall maxb pinfo Cfg1 IS1 Cfg2 IS2
  (Hwfpi: WF_PhiInfo pinfo) mi 
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals Cfg1))
  (Hinbd: 0 <= maxb) (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hok : ~ sop_goeswrong Cfg1 IS1)
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 IS1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hnrm: ~ removable_State pinfo IS1)
  (Hstsim : State_simulation pinfo maxb mi Cfg1 IS1 Cfg2 IS2) IS2' tr2
  (Hop2: Opsem.sInsn Cfg2 IS2 IS2' tr2)
  (Hwfcfg2: OpsemPP.wf_Config Cfg2) (Hwfpp2: OpsemPP.wf_State Cfg2 IS2),
  exists IS1' : Opsem.State, exists mi',
    Opsem.sInsn Cfg1 IS1 IS1' tr2 /\
    State_simulation pinfo maxb mi' Cfg1 IS1' Cfg2 IS2' /\
    inject_incr mi mi'.
Proof.
  intros.
  assert (Hnfinal1: Opsem.s_isFinialState Cfg1 IS1 = merror).
    remember (Opsem.s_isFinialState Cfg1 IS1) as R.
    destruct R; auto.
    apply s_isFinialState__dae_State_simulation_l2r' in Hstsim; 
      try solve [auto | congruence].
      contradict Hop2; eauto using s_isFinialState__stuck.
  assert (J:=Hwfpp).
  apply OpsemPP.progress in J; auto.
  destruct J as [Hfinal1 | [[IS1'' [tr0 Hop1]] | Hundef1]]; try congruence.
    assert (OpsemPP.wf_State Cfg1 IS1'') as Hwfpp''.
      apply OpsemPP.preservation in Hop1; auto.
    assert (Promotability.wf_State maxb pinfo Cfg1 IS1'') as Hnoalias''.
      eapply Promotability.preservation in Hop1; eauto.
    assert (palloca_props.wf_State pinfo IS1'') as Hpalloca''.
      eapply palloca_props.preservation in Hop1; eauto.
    eapply dae_is_sim in Hstsim; eauto.
    destruct Hstsim as [Hstsim1 Hstsim2].
    eapply Hstsim2 in Hnrm; eauto.
    destruct Hnrm as [mi' [Hstsim [EQ Hincr]]]; subst.
    exists IS1''. exists mi'.
    split; eauto.

    apply undefined_state__stuck' in Hundef1.
    contradict Hok.
    apply nonfinal_stuck_state_goes_wrong; auto.
Qed.

Lemma dae_is_bsim : forall maxb pinfo Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) mi 
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals Cfg1))
  (Hinbd: 0 <= maxb) (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1)
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hsim: State_simulation pinfo maxb mi Cfg1 St1 Cfg2 St2)
  (Hok: ~ sop_goeswrong Cfg1 St1)
  St2' tr2 (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2)
  (Hwfcfg2: OpsemPP.wf_Config Cfg2) (Hwfpp2: OpsemPP.wf_State Cfg2 St2),
  exists St1', exists mi',
    Opsem.sop_plus Cfg1 St1 St1' tr2 /\
    State_simulation pinfo maxb mi' Cfg1 St1' Cfg2 St2' /\
    inject_incr mi mi'.
Proof.
  intros.
  eapply dae_is_bsim_removable_steps in Hsim; eauto.
  destruct Hsim as [St1' [mi' [Hopstar [Hstsim [Hnrm Hinc]]]]].
  eapply dae_is_bsim_unremovable_step in Hstsim; eauto 2 using
      palloca_props.preservation_star, Promotability.preservation_star,
      (@OpsemPP.preservation_star DGVs), sop_goeswrong__star.
  destruct Hstsim as [FS1 [mi'' [Hopplus1 [Hstsim Hinc']]]].
  exists FS1. exists mi''.
  split.
    rewrite <- E0_left. 
    eapply OpsemProps.sop_star_plus__implies__sop_plus; eauto.
    apply OpsemProps.sInsn__implies__sop_plus; auto.
  split; eauto using inject_incr_trans.
Qed.

Lemma s_isFinialState__dae_State_simulation_r2l:
  forall pinfo cfg1 FS1 cfg2 FS2 r2 maxb mi 
  (Hwfpi: WF_PhiInfo pinfo)
  (Hinbd: 0 <= maxb) (Halias: Promotability.wf_State maxb pinfo cfg1 FS1)
  (Hpalloca: palloca_props.wf_State pinfo FS1)
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hwfcfg2: OpsemPP.wf_Config cfg2) (Hwfpp2: OpsemPP.wf_State cfg2 FS2) 
  (Hstsim : State_simulation pinfo maxb mi cfg1 FS1 cfg2 FS2)
  (Hwfgs: MemProps.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r2)
  (Hok: ~ sop_goeswrong cfg1 FS1),
  exists FS1', exists mi', 
    Opsem.sop_star cfg1 FS1 FS1' E0 /\
    State_simulation pinfo maxb mi' cfg1 FS1' cfg2 FS2 /\
    Values.inject_incr mi mi' /\
  exists r1,
    Opsem.s_isFinialState cfg1 FS1' = ret r1 /\
    result_match r1 r2.
Proof.
  intros.
  eapply dae_is_bsim_removable_steps in Hstsim; eauto.
  destruct Hstsim as [FS1' [mi' [Hopstar [Hstsim [Hnrm Hincr]]]]].
  exists FS1'. exists mi'.
  split; auto.
  split; auto.
  split; auto.
    eapply s_isFinialState__dae_State_simulation_r2l' in Hstsim; 
      eauto using (@OpsemPP.preservation_star DGVs).
Qed.

Ltac undefined_state__State_simulation_r2l_tac1 :=
  match goal with
  | Hstsim: State_simulation _ _ _ _ ?St1 _ ?St2 |- _ =>
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
  | Hstsim: State_simulation _ _ _ _ ?St1 _ ?St2 |- _ =>
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
  | Hstsim: State_simulation _ _ _ _ ?St1 ?cfg2 ?St2 |- _ =>
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
  _: ret ?gn = Opsem.getOperandValue ?td v' ?Locals ?fs2,
  H2: mem_simulation _ _ _ _ _ _,
  _: reg_simulation _ ?mi ?f ?Locals0 ?Locals,
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
    destruct G as [gvs G];
    assert (gv_inject mi gvs gn) as EQ; try solve [
      destruct H4 as [l1 [ps1 [cs11 H4]]]; subst;
      destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
      destruct Hwfpp1 as [_ [[_ [HbInF1 [HfInPs1 _]]] _]];
      destruct H2 as [H21 [H22 H23]];
      eapply simulation__getOperandValue with (v:=v'); try solve [
        eauto |
        eapply conditional_used_in_fdef__used_in_cmd_value; eauto using in_middle;
          simpl; auto |
        eapply wf_system__wf_fdef in HfInPs1; eauto;
        eapply wf_fdef__wf_cmd in HbInF1; eauto using in_middle;
        inv HbInF1; eauto 2
      ]
    ]
end.

Lemma stacked_frame__unremovable: forall cfg EC1 EC2 ECS Mem0 pinfo
  (Huniq: uniqEC EC2) (Hwfpi: WF_PhiInfo pinfo)
  (HBinF: match Opsem.CurBB EC1 with 
   | (_, stmts_intro _ _ (insn_return _ _ _)) => True
   | (_, stmts_intro _ _ (insn_return_void _)) => True
   | _ => False
   end)
  (Hwfpp1 : OpsemPP.wf_State cfg
             {| Opsem.ECS := EC1 :: EC2 :: ECS; Opsem.Mem := Mem0 |}),
  ~ removable_State pinfo
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
      eapply WF_PhiInfo_spec1' in J2; 
        eauto using in_middle; simpl; auto; 
      congruence
    ].
Qed.

Lemma undefined_state__dae_State_simulation_r2l': forall pinfo maxb mi cfg1 St1 cfg2
  St2 (Hstsim : State_simulation pinfo maxb mi cfg1 St1 cfg2 St2)
  (Hwfpi: WF_PhiInfo pinfo)
  (Hinbd: 0 <= maxb) (Halias: Promotability.wf_State maxb pinfo cfg1 St1)
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (Hnrem: ~removable_State pinfo St1) 
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
          removable_State pinfo
            {|
            Opsem.ECS := {|
                            Opsem.CurFunction := CurFunction2;
                            Opsem.CurBB := CurBB2;
                            Opsem.CurCmds := CurCmds1;
                            Opsem.Terminator := Terminator;
                            Opsem.Locals := Locals2;
                            Opsem.Allocas := Allocas2 |} :: ECS;
            Opsem.Mem := Mem0 |}).
      clear - Hwfpp1 H5 HuniqECs Hwfpi.
      destruct H5 as [l5 [ps5 [cs5 H5]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto; find_uniqEC.
    eapply RemoveSim.cmds_simulation_cons_inv' in Hnrem'; eauto.
    destruct Hnrem' as [cs1' [J1 J3]]; subst.
    left. 
    remember (free_allocas (los2, nts2) Mem0 Allocas1) as R.
    destruct R; auto.
    symmetry in HeqR. simpl in H2.
    eapply mem_simulation__free_allocas_l2r in HeqR; eauto.
    destruct HeqR as [M2' [Hfree [Hmsim']]].
    congruence.


  Case "2".
    undefined_state__State_simulation_r2l_tac1.
    eapply RemoveSim.cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    assert (Hnrem' : ~
          removable_State pinfo
            {|
            Opsem.ECS := {|
                            Opsem.CurFunction := CurFunction2;
                            Opsem.CurBB := CurBB2;
                            Opsem.CurCmds := CurCmds1;
                            Opsem.Terminator := Terminator;
                            Opsem.Locals := Locals2;
                            Opsem.Allocas := Allocas2 |} :: ECS;
            Opsem.Mem := Mem0 |}).
      clear - Hwfpp1 H5 HuniqECs Hwfpi.
      destruct H5 as [l5 [ps5 [cs5 H5]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto; find_uniqEC.
    eapply RemoveSim.cmds_simulation_cons_inv' in Hnrem'; eauto.
    destruct Hnrem' as [cs1' [J1 J3]]; subst.
    right. left. 
    destruct Hundef as [Hundef | Hundef]; auto.
    left.
    remember (free_allocas (los2, nts2) Mem0 Allocas1) as R.
    destruct R; auto.
    symmetry in HeqR. simpl in H2.
    eapply mem_simulation__free_allocas_l2r in HeqR; eauto.
    destruct HeqR as [M2' [Hfree [Hmsim']]].
    congruence.

  Case "3".
    undefined_state__State_simulation_r2l_tac3.
    eapply RemoveSim.cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    right. right. left.
    destruct H5 as [l6 [ps6 [cs6 H5]]]; subst. auto.

  Case "4".
    right; right; right; left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' Locals] ?] ?]; try solve [
      tauto |
      inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind;
      undefined_state__State_simulation_r2l_tac41;
      undefined_state__d_State_simulation_r2l_tac43;
      undefined_state__d_State_simulation_r2l_tac42 value5;
      repeat fill_ctxhole; exists gvs; split; auto;
      remember (malloc (los2, nts2) Mem0 s gvs align5) as R;
      destruct R as [[]|]; auto;
      symmetry in HeqR2;
      eapply mem_simulation__malloc_l2r' in HeqR2; eauto 2;
      destruct HeqR2 as [Mem2' [mi' [mb2 [J1 [J2 [J13 J4]]]]]]; congruence
    ].

  Case "5".
    right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43.
    undefined_state__d_State_simulation_r2l_tac42 value5.
    repeat fill_ctxhole; exists gvs. split; auto.
    remember (free (los2, nts2) Mem0 gvs) as R.
    destruct R; auto.
    symmetry in HeqR1. simpl in H2.
    eapply mem_simulation__free_l2r in HeqR1; eauto.
    destruct HeqR1 as [M2' [Hfree [Hmsim']]].
    congruence.
   
  Case "6".
    right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gvs [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43. 
    undefined_state__d_State_simulation_r2l_tac42 value1.
    repeat fill_ctxhole; exists gvs0. split; auto.
    remember (mload (los2, nts2) Mem0 gvs0 typ5 align5) as R.
    destruct R; auto.
    symmetry in HeqR1. simpl in H2.
    eapply simulation__mload_l2r in HeqR1; eauto.
    destruct HeqR1 as [gv2 [Hload Hinj]].
    congruence.

  Case "7".
    right. right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gv [mgv [EQ1 [EQ2 Hundef]]]]; 
      inv EQ1; inv EQ2; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43. 
    undefined_state__d_State_simulation_r2l_tac42 value1.
    undefined_state__d_State_simulation_r2l_tac42 value2.
    repeat fill_ctxhole; exists gvs; exists gvs0.
    split; auto.
    remember (mstore (los2, nts2) Mem0 gvs0 typ5 gvs align5) as R.
    destruct R; auto.
    symmetry in HeqR2. simpl in H2.
    eapply simulation__mstore_l2r in HeqR2; eauto.
    destruct HeqR2 as [M2' [Hstore Hinj]].
    congruence.

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
      destruct H4 as [l1 [ps1 [cs11 H4]]]; subst.
      destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]].
      destruct Hwfpp1 as [_ [[_ [HbInF1 [HfInPs1 _]]] _]].
      destruct H2 as [H21 [H22 H23]].
      assert (exists t, wf_value S1 (module_intro los2 nts2 gl1) CurFunction0 value0 t) 
        as Hwfv.
        eapply wf_system__wf_fdef in HfInPs1; eauto.
        eapply wf_fdef__wf_cmd in HbInF1; eauto using in_middle.
        eapply wf_cmd__wf_value in HbInF1; eauto; simpl; auto.
      destruct Hwfv as [tv Hwfv].
      eapply simulation__getOperandValue with (v:=value0); try solve [
        eauto 2 |
        eapply conditional_used_in_fdef__used_in_cmd_value; eauto 4 using in_middle;
          simpl; auto
      ].
    repeat fill_ctxhole.
    exists gvs. split; auto.
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
      assert (Forall2 (fun gv1 gv2 : GenericValue => gv_inject mi gv1 gv2) gvs' l1) 
        as EQ2.
        destruct H4 as [l5 [ps1 [cs11 H4]]]; subst;
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
        inv_mbind. destruct H2 as [_ [_ H2]].
        eapply wf_system__wf_fdef in HfInPs1; eauto.
        assert (Hwfc:=HbInF1).
        eapply wf_fdef__wf_cmd in Hwfc; eauto using in_middle.
        inv Hwfc.
        find_wf_value_list.
        eapply reg_simulation__params2GVs; 
          eauto 2 using wf_system__wf_fdef, wf_system__uniqFdef; 
            try solve [simpl; auto].
          eapply conditional_used_in_fdef__used_in_params; eauto 1.
      repeat fill_ctxhole.
      remember (OpsemAux.lookupFdefViaPtr gl1 FunTable0 gvs) as R.
      destruct R.
        eapply TopSim.lookupFdefViaPtr_inj__simulation_l2r in H; eauto.
        remember (OpsemAux.lookupExFdecViaPtr gl1 FunTable0 gvs) as R.
        destruct R; auto. 
        eapply TopSim.lookupExFdecViaPtr_inj__simulation_l2r' in H; eauto.
        rewrite <- HeqR1 in H. inv H. 
        exists gvs'. split; auto.
        remember (callExternalOrIntrinsics (los2, nts2) fs2 Mem0 id0 typ0
          (args2Typs args5) deckind5 gvs') as R.
        destruct R as [[[]]|]; auto.
        remember (Opsem.exCallUpdateLocals (los2, nts2) typ5 noret5 id5 o Locals0) as R.
        destruct R; auto.
        simpl in H2.
        eapply callExternalFunction__mem_simulation_l2r in H2; eauto.
        destruct H2 as [tr2 [M2' [lc2' [oresult2 [mi' 
          [W1 [W2 [W3 [W4 [W5 [W6 [W7 [W8 W9]]]]]]]]]]]]]; subst.
        rewrite W1 in Hundef. rewrite W2 in Hundef. auto.

      remember (OpsemAux.lookupFdefViaPtr gl1 FunTable0 gvs) as R.
      destruct R.
        eapply TopSim.lookupFdefViaPtr_inj__simulation_l2r' in H; eauto.
        destruct H as [f2 [J1 J3]]. congruence.

        remember (OpsemAux.lookupExFdecViaPtr gl1 FunTable0 gvs) as R.
        destruct R; auto. 
        eapply TopSim.lookupExFdecViaPtr_inj__simulation_l2r' in H; eauto.
        rewrite <- HeqR1 in H. inv H. 
Qed.

Lemma undefined_state__dae_State_simulation_r2l: forall pinfo cfg1 St1 cfg2
  St2 maxb mi 
  (Hwfpi: WF_PhiInfo pinfo)
  (Hinbd: 0 <= maxb) (Halias: Promotability.wf_State maxb pinfo cfg1 St1)
  (Hwfgl: MemProps.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (Hwfcfg2: OpsemPP.wf_Config cfg2) (Hwfpp2: OpsemPP.wf_State cfg2 St2) 
  (Hstsim : State_simulation pinfo maxb mi cfg1 St1 cfg2 St2)
  (Hundef: OpsemPP.undefined_state cfg2 St2)
  (Hok: ~ sop_goeswrong cfg1 St1),
  exists St1', exists mi',
    Opsem.sop_star cfg1 St1 St1' E0 /\
    State_simulation pinfo maxb mi' cfg1 St1' cfg2 St2 /\
    OpsemPP.undefined_state cfg1 St1' /\
    Values.inject_incr mi mi'.
Proof.
  intros.
  eapply dae_is_bsim_removable_steps in Hstsim; eauto.
  destruct Hstsim as [FS1' [mi' [Hopstar [Hstsim [Hnrm Hincr]]]]].
  exists FS1'. exists mi'.
  split; auto.
  split; auto.
    eapply undefined_state__dae_State_simulation_r2l' in Hstsim; 
      eauto using (@OpsemPP.preservation_star DGVs),
        Promotability.preservation_star, palloca_props.preservation_star.
Qed.

Lemma sop_star__dae_State_simulation: forall pinfo mi cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) maxb
  (Hwfpp1: OpsemPP.wf_State cfg1 IS1) (Hwfcfg1: OpsemPP.wf_Config cfg1)
  (Hwfpp2: OpsemPP.wf_State cfg2 IS2) (Hwfcfg2: OpsemPP.wf_Config cfg2)
  (Hwfg: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hless: 0 <= maxb) (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgs: MemProps.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hstsim : State_simulation pinfo maxb mi cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, exists mi', Opsem.sop_star cfg1 IS1 FS1 tr /\
    State_simulation pinfo maxb mi' cfg1 FS1 cfg2 FS2 /\
    inject_incr mi mi'.
Proof.
  intros.
  generalize dependent cfg1.
  generalize dependent IS1.
  generalize dependent mi.
  induction Hopstar; intros.
    exists IS1. exists mi. split; auto.

    assert (forall IS1' mi0
            (Hok' : ~ sop_goeswrong cfg1 IS1')
            (Hwfpp': OpsemPP.wf_State cfg1 IS1')
            (Hnoalias': Promotability.wf_State maxb pinfo cfg1 IS1')
            (Hpalloca': palloca_props.wf_State pinfo IS1')
            (Hnrm': ~ removable_State pinfo IS1')
            (Hstsim' : State_simulation pinfo maxb mi0 cfg1 IS1' cfg2 state1),
            exists FS1 : Opsem.State, exists mi',
              Opsem.sop_star cfg1 IS1' FS1 (tr1 ** tr2) /\
              State_simulation pinfo maxb mi' cfg1 FS1 cfg2 state3 /\
              inject_incr mi0 mi') as W1.
      clear - H Hopstar IHHopstar Hwfcfg1 Hwfpi Hless Hwfg Hnuse Hwfgs Hwfcfg2
              Hwfpp2. 
      intros.
      assert (Hwfpp2':=H). apply OpsemPP.preservation in Hwfpp2'; auto.
      eapply dae_is_bsim in H; eauto 2.
      destruct H as [St1' [mi' [Hplus1 [Hstsim Hinc]]]].
      eapply IHHopstar in Hstsim;
        eauto using palloca_props.preservation_plus, Promotability.preservation_plus,
        (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
      destruct Hstsim as [FS1 [mi'' [Hopstar1 [Hstsim Hinc']]]].
      exists FS1. exists mi''.
      split.
        eapply OpsemProps.sop_star_trans; eauto.
        apply OpsemProps.sop_plus__implies__sop_star; eauto.
      split; eauto using inject_incr_trans.

    eapply dae_is_bsim_removable_steps in Hstsim;
      eauto using palloca_props.preservation_plus, Promotability.preservation_plus,
      (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
    destruct Hstsim as [St1' [mi' [Hopstar1 [Hstsim [Hnrm Hinc]]]]].
    eapply palloca_props.preservation_star in Hpalloca; eauto.
    eapply Promotability.preservation_star in Hnoalias; eauto.
    eapply OpsemPP.preservation_star in Hwfpp1; eauto.
    eapply sop_goeswrong__star in Hok; eauto.
    eapply W1 in Hstsim; eauto.
    destruct Hstsim as [FS1 [mi'' [Hopstar'' [Hstsim Hinc'']]]].
    exists FS1. exists mi''.
    split.
      clear - Hopstar1 Hopstar''.
      rewrite <- E0_left.
      eapply OpsemProps.sop_star_trans; eauto.
    split; eauto using inject_incr_trans.
Qed.

Lemma sop_plus__dae_State_simulation: forall pinfo mi cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) maxb
  (Hwfpp1: OpsemPP.wf_State cfg1 IS1) (Hwfcfg1: OpsemPP.wf_Config cfg1)
  (Hwfpp2: OpsemPP.wf_State cfg2 IS2) (Hwfcfg2: OpsemPP.wf_Config cfg2)
  (Hwfg: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hless: 0 <= maxb) (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgs: MemProps.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hstsim : State_simulation pinfo maxb mi cfg1 IS1 cfg2 IS2)
  (Hopplus : Opsem.sop_plus cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, exists mi', Opsem.sop_plus cfg1 IS1 FS1 tr /\
    State_simulation pinfo maxb mi' cfg1 FS1 cfg2 FS2 /\
    inject_incr mi mi'.
Proof.
  intros.
  inv Hopplus.
  assert (Hwfpp2':=H). apply OpsemPP.preservation in Hwfpp2'; auto.
  eapply dae_is_bsim in H; eauto.
  destruct H as [St1' [mi' [Hplus1 [Hstsim' Hinc]]]].
  eapply sop_star__dae_State_simulation in Hstsim'; eauto using
    palloca_props.preservation_plus, Promotability.preservation_plus,
    (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
  destruct Hstsim' as [FS1 [mi'' [Hopstar [Hstsim' Hinc']]]].
  exists FS1. exists mi''.
  split.
    eapply OpsemProps.sop_plus_star__implies__sop_plus; eauto.
  split; eauto using inject_incr_trans.
Qed.

Lemma sop_div__dae_State_simulation: forall pinfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpi: WF_PhiInfo pinfo) maxb mi
  (Hwfpp1: OpsemPP.wf_State cfg1 IS1) (Hwfcfg1: OpsemPP.wf_Config cfg1)
  (Hwfpp2: OpsemPP.wf_State cfg2 IS2) (Hwfcfg2: OpsemPP.wf_Config cfg2)
  (Hwfg: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hless: 0 <= maxb) (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgs: MemProps.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hstsim : State_simulation pinfo maxb mi cfg1 IS1 cfg2 IS2)
  (Hdiv : Opsem.sop_diverges cfg2 IS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  Opsem.sop_diverges cfg1 IS1 tr.
Proof.
  cofix CIH.
  intros.
  inv Hdiv.
  eapply sop_plus__dae_State_simulation in Hstsim; eauto 1.
  destruct Hstsim as [FS1 [mi' [Hopplus [Hstsim' Hinc]]]].
  econstructor; eauto.
  eapply CIH in Hstsim'; eauto using
    palloca_props.preservation_plus, Promotability.preservation_plus,
    (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
Qed.

(* The main result *)
Lemma dae_sim: forall id0 f pinfo los nts Ps1 Ps2 main VarArgs
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hok: defined_program [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
          main VarArgs)
  (Heq1: f = PI_f pinfo) (Heq2: id0 = PI_id pinfo),
  program_sim
    [module_intro los nts
      (Ps1 ++  product_fdef (remove_fdef id0 f) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Proof.
  intros. subst.
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation pinfo
    [module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2)]
    [module_intro los nts
      (Ps1 ++ product_fdef (remove_fdef (PI_id pinfo) (PI_f pinfo)) :: Ps2)])
    as Hssim.
    constructor; auto.
    repeat split; auto.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    unfold TopSim.products_simulation. simpl. unfold system_simulation.
    apply uniq_products_simulation; auto.

Ltac dae_sim_init :=
match goal with
| H: Opsem.s_genInitState [module_intro ?los ?nts _] _ _ _ = Some (?cfg, ?IS), 
  pinfo: PhiInfo |- _ =>
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg IS) as Hwfst';
      try solve [eapply s_genInitState__opsem_wf in H; eauto using dae_wfS];
    eapply s_genInitState__dae_State_simulation in H; eauto;
    destruct H as
      [maxb [mi [cfg1 [IS1 [Hinit1 [Hstsim [Hwfg [Hwfgs [Hless Hprom]]]]]]]]];
    assert (OpsemPP.wf_Config cfg1/\ OpsemPP.wf_State cfg1 IS1) as Hwfst;
      try solve [eapply s_genInitState__opsem_wf; eauto];
    assert (palloca_props.wf_State pinfo IS1) as Hpalloca;
      try solve [eapply palloca_props.s_genInitState__palloca; eauto]
end.

Ltac dae_sim_end :=
 match goal with
| Hstsim' : State_simulation ?pinfo ?maxb _ ?cfg1 ?FS1 ?cfg ?FS,
  Hopstar1 : Opsem.sop_star ?cfg1 _ ?FS1 _ |- _ =>
    assert (OpsemPP.wf_State cfg FS) as Hwfst''; 
      try solve [eapply OpsemPP.preservation_star; eauto; try tauto];
    assert (OpsemPP.wf_State cfg1 FS1) as Hwfst1'';
      try solve [eapply OpsemPP.preservation_star; eauto; try tauto];
    assert (palloca_props.wf_State pinfo FS1); try solve 
      [eapply palloca_props.preservation_star in Hopstar1; eauto; try tauto];
    assert (Promotability.wf_State maxb pinfo cfg1 FS1) as Hprom'; try solve [
      eapply Promotability.preservation_star in Hopstar1; eauto; try tauto
    ]
end.

  constructor; auto.
    intros tr t Hconv.
    inv Hconv.
    dae_sim_init.
    eapply sop_star__dae_State_simulation in Hstsim;
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [mi' [Hopstar1 [Hstsim' Hinc]]]].
    dae_sim_end.
    eapply s_isFinialState__dae_State_simulation_r2l in Hstsim'; 
      eauto using sop_goeswrong__star, defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim' 
      as [FS1' [mi'' [Hopstar1' [Hstsim'' [Hinc' [r1 [Hfinal Hrmatch]]]]]]].
    assert (Opsem.sop_star cfg1 IS1 FS1' tr) as Hopstar1''.
      rewrite <- E0_right.
      eapply OpsemProps.sop_star_trans; eauto.
    exists r1. 
    split; auto using result_match_symm. 
      econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    dae_sim_init.
    eapply sop_div__dae_State_simulation in Hstsim; 
      try solve [eauto using defined_program__doesnt__go_wrong| tauto].
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.

    intros tr t Hgowrong.
    inv Hgowrong.
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg t) as HwfSt.
      eapply s_genInitState__opsem_wf in H; eauto using dae_wfS.
      destruct H as [Hcfg2 HwfSt2].
      apply OpsemPP.preservation_star in H0; auto.
    assert (OpsemPP.undefined_state cfg t) as Hundef.
      apply stuck__undefined_state in H2; try solve [auto | tauto].
    dae_sim_init.
    eapply sop_star__dae_State_simulation in Hstsim; eauto;
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [mi' [Hopstar1 [Hstsim' Hinc]]]].
    dae_sim_end.
    assert (Hundef':=Hundef).
    eapply undefined_state__dae_State_simulation_r2l in Hundef'; 
      try solve [eauto using sop_goeswrong__star, defined_program__doesnt__go_wrong | tauto].
    destruct Hundef' as [FS1' [mi'' [Hopstar2 [Hsim [Hundef' Hinc']]]]].
    assert (Opsem.s_isFinialState cfg1 FS1' = merror) as Hfinal'.
      apply OpsemPP.preservation_star in Hopstar2; auto; try tauto.
      eapply s_isFinialState__dae_State_simulation_None_r2l in H2; 
        try solve [eauto | tauto].
    apply undefined_state__stuck' in Hundef'.
    rewrite <- E0_right with (t:=tr). exists FS1'.
    econstructor; eauto using (@OpsemProps.sop_star_trans DGVs).   
Qed.
