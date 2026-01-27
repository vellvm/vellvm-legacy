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
Require Import vmem2reg.
Require Import program_sim.
Require Import trans_tactic.
Require Import sas_msim.
Require Import memory_sim.
Require Import top_sim.
Require Import sas.
Require Import sas_wfS.

(* This file proves that SAS refines programs by top_sim. *)

Lemma s_genInitState__sas_State_simulation: forall pinfo sasinfo S1 S2 main
  VarArgs cfg2 IS2 (Hssim: system_simulation pinfo sasinfo S1 S2)
  (Hwfpi: WF_PhiInfo pinfo) (HwfS1: wf_system S1) Ps1 Ps2 los0 nts0 f0
  (Heq1: PI_f pinfo = f0)
  (Heq2: S1 = [module_intro los0 nts0
                (Ps1 ++ product_fdef f0 :: Ps2)])
  (Hinit: Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2)),
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo sasinfo cfg1 IS1 cfg2 IS2.
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
  apply block_simulation_inv in J; 
    eauto using entryBlockInFdef, wf_system__uniqFdef.
  destruct J as [J1 [J2 [J3 J7]]]; subst.
  split; auto.
  eapply genGlobalAndInitMem__wf_globals_Mem in HeqR1; eauto.
  destruct HeqR1 as [J7 [J8 [J9 [J10 [J11 [J12 [J13 J14]]]]]]].
  repeat (split; auto).
    exists l0. exists ps0. exists nil. auto.
    exists l0. exists ps0. exists nil. auto.

    unfold sas_mem_inj. 
    assert (exists tsz, getTypeStoreSize (OpsemAux.initTargetData los nts Mem.empty)
             (PI_typ pinfo) = Some tsz) as Htsz.
      simpl in HMinS. apply orb_true_elim in HMinS. 
      destruct HMinS as [HMinS | HMinS]; try congruence.
      uniq_result.
      apply wf_single_system__wf_uniq_fdef in HwfS1; auto.
      destruct HwfS1 as [HwfF_pi Huniq_pi].
      apply WF_PhiInfo_spec21 in HwfF_pi; auto.
      unfold OpsemAux.initTargetData.
      apply wf_typ__getTypeSizeInBits_and_Alignment in HwfF_pi.
      destruct HwfF_pi as [sz [al [J1 _]]].
      apply getTypeSizeInBits_and_Alignment__getTypeStoreSize in J1.
      eauto.
    destruct Htsz as [tsz Htsz]. fill_ctxhole.
    intros.
    eapply SASmsim.from_MoreMem_inj; eauto.
Qed.

Ltac s_isFinialState__sas_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal := 
  destruct cfg2 as [S2 [los2 nts2] gl2 fs2];
  destruct cfg1 as [S1 [los1 nts1] gl1 fs1];
  destruct FS1 as [[|[? ? cs1 ? ?] ES1]]; 
  destruct FS2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
    auto | congruence |
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst; inv Hstsim
  ];
  destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
  inv X; simpl;
  destruct Hstsim as [Hstsim Hstsim'];
  fold ECs_simulation in Hstsim';
  destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
  destruct cs1, cs2; try solve [
    auto |
    apply RemoveSim.cmds_simulation_nil_inv in Hstsim; try congruence |
    inv Hfinal
  ].

Lemma s_isFinialState__sas_State_simulation_l2r: forall pinfo sasinfo cfg1 FS1 cfg2
  FS2 r (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 = ret r),
  Opsem.s_isFinialState cfg2 FS2 = ret r.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__sas_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
  destruct Terminator0; auto.
    destruct ES1, ES2; try solve [auto | inv Hstsim'].
    destruct ES1, ES2; try solve [auto | inv Hstsim'].
Qed.

Lemma s_isFinialState__sas_State_simulation_l2r': forall pinfo sasinfo cfg1 FS1 cfg2
  FS2 (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 <> None),
  Opsem.s_isFinialState cfg2 FS2 <> None.
Proof.
  intros.
  remember (Opsem.s_isFinialState cfg1 FS1) as R.
  destruct R; try congruence.
  symmetry_ctx.
  eapply s_isFinialState__sas_State_simulation_l2r in Hstsim; eauto.
  congruence.
Qed.

Lemma s_isFinialState__sas_State_simulation_None_r2l:
  forall pinfo sasinfo cfg1 FS1 cfg2 FS2
  (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = None),
  Opsem.s_isFinialState cfg1 FS1 = None.
Proof.
  intros.
  remember (Opsem.s_isFinialState cfg1 FS1) as R.
  destruct R; try congruence.
  contradict Hfinal.
  eapply s_isFinialState__sas_State_simulation_l2r' in Hstsim; eauto.
    congruence.
Qed.

Lemma s_isFinialState__sas_State_simulation_r2l':
  forall pinfo sasinfo cfg1 FS1 cfg2 FS2 r
  (Hnrem: ~removable_State pinfo sasinfo FS1) 
  (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r),
  Opsem.s_isFinialState cfg1 FS1 = ret r.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__sas_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
    destruct Terminator0; auto.
      destruct ES1, ES2; try solve [auto | inv Hstsim'].
      destruct ES1, ES2; try solve [auto | inv Hstsim'].

   unfold removable_State in Hnrem.
   apply RemoveSim.not_removable_State_inv in Hnrem.
   apply RemoveSim.cmds_simulation_nelim_cons_inv in Hstsim; auto. 
     destruct Hstsim as [cs2' [J1 Hstsim]]; congruence.
Qed.

Lemma sas_is_bsim_removable_steps : forall maxb pinfo sasinfo Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo)  
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1)
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hsim: State_simulation pinfo sasinfo Cfg1 St1 Cfg2 St2)
  (Hok: ~ sop_goeswrong Cfg1 St1),
  exists St1',
    Opsem.sop_star Cfg1 St1 St1' E0 /\
    State_simulation pinfo sasinfo Cfg1 St1' Cfg2 St2 /\
    ~ removable_State pinfo sasinfo St1'.
Proof.
  intros.
  destruct (@RemoveSim.removable_State_dec (PI_f pinfo)
               (SAS_sid1 pinfo sasinfo) St1) as [Hrm | Hnrm]; eauto.
  destruct St1 as [[|[f1 b1 [|c1 cs1] tmn1 lc1 als1] ES1] M1]; tinv Hrm.
  assert (J:=Hwfpp).
  apply OpsemPP.progress in J; auto.
  assert (Hnfinal1:=Hrm).
  apply RemoveSim.removable_State__isnt__final with (cfg:=Cfg1) in Hnfinal1.
  destruct J as [Hfinal1 | [[IS1'' [tr0 Hop1]] | Hundef1]]; try congruence.
    eapply sas_is_sim in Hsim; eauto.
    destruct Hsim as [Hstsim1 _].
    assert (~ removable_State pinfo sasinfo IS1'') as Hnrm.
      destruct Cfg1 as [? [] ? ?]. simpl in Hwfpp. 
      destruct Hwfpp as [_ [[_ [HBinF [A [_ [_ [l1 [ps1 [cs1' Hex]]]]]]]] _]]; 
        subst.
      destruct Hwfcfg as [_ [_ [HwfS C]]].
      eapply wf_system__uniqFdef in HwfS; eauto.
      assert (c1 = insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
                (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) 
                (SAS_align1 pinfo sasinfo)) as EQ.
        simpl in Hrm. repeat destruct_if.
        eapply lookup_SAS_lid1__store with (sasinfo:=sasinfo) in HBinF; 
          eauto using in_middle.
      subst.
      inv Hop1. 
      eapply RemoveSim.removable_State__non_removable_State; eauto.
        clear - HwfS HBinF.
        apply uniqFdef__uniqBlockLocs in HBinF; auto.
        simpl in HBinF. split_NoDup. simpl_locs_in_ctx. split_NoDup. auto.
    eapply Hstsim1 in Hrm; eauto.
    destruct Hrm as [Hstsim EQ]; subst.
    exists IS1''.
    split; auto. 
      apply OpsemProps.sInsn__implies__sop_star; auto.

    apply undefined_state__stuck' in Hundef1.
    contradict Hok. 
    apply nonfinal_stuck_state_goes_wrong; auto.
Qed.

Lemma sas_is_bsim_unremovable_step : forall maxb pinfo sasinfo Cfg1 IS1 Cfg2 IS2
  (Hwfpi: WF_PhiInfo pinfo) (Hless: 0 <= maxb)
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hok : ~ sop_goeswrong Cfg1 IS1)
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 IS1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hnrm: ~ removable_State pinfo sasinfo IS1)
  (Hstsim : State_simulation pinfo sasinfo Cfg1 IS1 Cfg2 IS2) IS2' tr2
  (Hop2: Opsem.sInsn Cfg2 IS2 IS2' tr2),
  exists IS1' : Opsem.State,
    Opsem.sInsn Cfg1 IS1 IS1' tr2 /\
    State_simulation pinfo sasinfo Cfg1 IS1' Cfg2 IS2'.
Proof.
  intros.
  assert (Hnfinal1: Opsem.s_isFinialState Cfg1 IS1 = merror).
    remember (Opsem.s_isFinialState Cfg1 IS1) as R.
    destruct R; auto.
    apply s_isFinialState__sas_State_simulation_l2r' in Hstsim; 
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
    eapply sas_is_sim in Hstsim; eauto.
    destruct Hstsim as [Hstsim1 Hstsim2].
    eapply Hstsim2 in Hnrm; eauto.
    destruct Hnrm as [Hstsim EQ]; subst.
    exists IS1''. 
    split; eauto.

    apply undefined_state__stuck' in Hundef1.
    contradict Hok.
    apply nonfinal_stuck_state_goes_wrong; auto.
Qed.

Lemma sas_is_bsim : forall maxb pinfo sasinfo Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) (Hless: 0 <= maxb)
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1)
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hsim: State_simulation pinfo sasinfo Cfg1 St1 Cfg2 St2)
  (Hok: ~ sop_goeswrong Cfg1 St1)
  St2' tr2 (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2),
  exists St1',
    Opsem.sop_plus Cfg1 St1 St1' tr2 /\
    State_simulation pinfo sasinfo Cfg1 St1' Cfg2 St2'.
Proof.
  intros.
  eapply sas_is_bsim_removable_steps in Hsim; eauto.
  destruct Hsim as [St1' [Hopstar [Hstsim Hnrm]]].
  eapply sas_is_bsim_unremovable_step in Hstsim; eauto 2 using
      palloca_props.preservation_star, Promotability.preservation_star,
      (@OpsemPP.preservation_star DGVs), sop_goeswrong__star.
  destruct Hstsim as [FS1 [Hopplus1 Hstsim]].
  exists FS1.
  split; auto. 
    rewrite <- E0_left. 
    eapply OpsemProps.sop_star_plus__implies__sop_plus; eauto.
    apply OpsemProps.sInsn__implies__sop_plus; auto.
Qed.

Lemma s_isFinialState__sas_State_simulation_r2l:
  forall pinfo sasinfo cfg1 FS1 cfg2 FS2 r
  (Hwfpi: WF_PhiInfo pinfo) maxb
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) 
  (Hwfcfg: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 FS1) 
  (Hpalloca: palloca_props.wf_State pinfo FS1) 
  (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r)
  (Hok: ~ sop_goeswrong cfg1 FS1),
  exists FS1',
    Opsem.sop_star cfg1 FS1 FS1' E0 /\
    State_simulation pinfo sasinfo cfg1 FS1' cfg2 FS2 /\
    Opsem.s_isFinialState cfg1 FS1' = ret r.
Proof.
  intros.
  eapply sas_is_bsim_removable_steps in Hstsim; eauto.
  destruct Hstsim as [FS1' [Hopstar [Hstsim Hnrm]]].
  exists FS1'.
  split; auto.
  split; auto.
    eapply s_isFinialState__sas_State_simulation_r2l' in Hstsim; eauto.
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
    destruct St2 as [[|[? [? [? ? tmn]] CurCmds tmn' ?] ?] ?]; try tauto;
    destruct tmn; try tauto;
    destruct CurCmds; try tauto;
    destruct tmn'; try tauto;
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? H3]]]]]; subst;
    inv X;
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [Hstsim _];
    destruct Hstsim as [? [Htmn [? [? [H8 [? [? Hstsim]]]]]]]; subst;
    let l5 := fresh "l5" in
    destruct H8 as [l5 [ps5 [cs5 EQ]]]; subst
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

Ltac undefined_state__d_State_simulation_r2l_tac43 := 
      match goal with
      | Hstsim: cmds_simulation _ _ _ _ (_::_) |- _ =>
      eapply RemoveSim.cmds_simulation_cons_inv' in Hstsim; eauto; subst;
      destruct Hstsim as [c1' [J2 J3]]; subst
     end.

Lemma stacked_frame__unremovable: forall cfg EC1 EC2 ECS Mem0 pinfo sasinfo
  (Huniq: uniqEC EC2) 
  (HBinF: match Opsem.CurBB EC1 with 
   | (_, stmts_intro _ _ (insn_return _ _ _)) => True
   | (_, stmts_intro _ _ (insn_return_void _)) => True
   | _ => False
   end)
  (Hwfpp1 : OpsemPP.wf_State cfg
             {| Opsem.ECS := EC1 :: EC2 :: ECS; Opsem.Mem := Mem0 |}),
  ~ removable_State pinfo sasinfo
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
      eapply unstore_loc__neq__SAS_sid1 in J2; 
        eauto 4 using in_middle; simpl; auto
    ].
Qed.

Lemma mem_simulation__malloc_l2r': forall (pinfo : PhiInfo) sasinfo TD ECs M1 M2
  (Hmsim : mem_simulation pinfo sasinfo TD ECs M1 M2) (Huniq: uniqECs ECs)
  (Mem'0 : mem) (tsz0 : sz) align0 gn mb M1'
  (H2 : malloc TD M1 tsz0 gn align0 = ret (M1', mb)),
  exists M2',
     malloc TD M2 tsz0 gn align0 = ret (M2', mb).
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmim3 Hmsim2]].
  unfold sas_mem_inj in *.
  inv_mbind. 
  destruct (@in_SAS_tails_ex pinfo sasinfo TD ECs Huniq) as [ombs J].
  apply_clear Hmsim2 in J.
  apply malloc_inv in H2. destruct H2 as [n0 [J1 [J2 J3]]].
  unfold malloc. fill_ctxhole.
  destruct_if; try congruence.
  remember (Mem.alloc M2 0 (Size.to_Z tsz0 * n0)) as R.
  destruct R as [M2' mb2].
  exists M2'.
  apply Mem.alloc_result in J3.
  symmetry in HeqR1.
  apply Mem.alloc_result in HeqR1.
  f_equal. f_equal.
  congruence.
Qed.

Lemma mem_simulation__mload_l2r: forall td gv M1 mp t align0 M2 ECs pinfo
  (H1 : mload td M1 mp t align0 = ret gv) sasinfo (Huniq: uniqECs ECs)
  (Hmsim : mem_simulation pinfo sasinfo td ECs M1 M2),
  exists gv0, mload td M2 mp t align0 = ret gv0.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  apply mload_inv in H1.
  destruct H1 as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold sas_mem_inj in Hmsim2.
  inv_mbind. 
  destruct (@in_SAS_tails_ex pinfo sasinfo td ECs Huniq) as [ombs J].
  apply_clear Hmsim2 in J.
  unfold mload. repeat fill_ctxhole. simpl.
  eapply SASmsim.mload_aux_inj_ex with (b2:=b)(delta:=0) in J; eauto.
  replace (Int.signed 31 ofs + 0) with (Int.signed 31 ofs)  in J by omega.
  destruct J as [gv2 J]; eauto.
Qed.

Lemma mem_simulation__mstore_l2r: forall td M1 mp2 t gv1 align0 M1' M2 ECs
  (H3 : mstore td M1 mp2 t gv1 align0 = ret M1') pinfo sasinfo 
  (Huniq: uniqECs ECs)
  (Hmsim : mem_simulation pinfo sasinfo td ECs M1 M2),
  exists M2', 
    mstore td M2 mp2 t gv1 align0 = ret M2'.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  apply mstore_inversion in H3.
  destruct H3 as [b [ofs [cm [J1 J2]]]]; subst.
  unfold sas_mem_inj in *.
  inv_mbind.
  destruct (@in_SAS_tails_ex pinfo sasinfo td ECs Huniq) as [ombs J].
  apply_clear Hmsim2 in J.
  unfold mstore. simpl. 
  eapply SASmsim.mstore_aux_inject_id_mapped_inj in J; eauto.
  destruct J as [gv2 [J1 J4]]; eauto.
Qed.

Lemma mem_simulation__free_allocas_l2r : forall TD ECs1 pinfo sasinfo EC EC'
  (Hp: forall omb,
       in_SAS_tail pinfo sasinfo omb TD EC' ->
       in_SAS_tail pinfo sasinfo omb TD EC)
  als Mem1 Mem2 Mem1'  (Huniq: uniqECs (EC::ECs1))
  (Hmsim : mem_simulation pinfo sasinfo TD (EC :: ECs1) Mem1 Mem2)
  (Hmlc: free_allocas TD Mem1 als = ret Mem1'),
  exists Mem2',
    free_allocas TD Mem2 als = ret Mem2' /\
    mem_simulation pinfo sasinfo TD (EC' :: ECs1) Mem1' Mem2'.
Proof.
  induction als; simpl; intros.
    uniq_result. exists Mem2. 
    split; auto.
      eapply mem_simulation__replace_head; eauto.

    inv_mbind.
    eapply mem_simulation__free_l2r with (Mem1':=m)(EC':=EC) in Hmsim; eauto.
    destruct Hmsim as [Mem2' [J1 J2]].
    rewrite J1.
    eapply IHals in J2; eauto.
Qed.

Lemma undefined_state__sas_State_simulation_r2l': forall pinfo cfg1 St1 cfg2
  St2 sasinfo 
  (Hwfpp1: OpsemPP.wf_State cfg1 St1) (Hwfcfg1: OpsemPP.wf_Config cfg1) 
  (Hstsim : State_simulation pinfo sasinfo cfg1 St1 cfg2 St2)
  (Hnrem: ~removable_State pinfo sasinfo St1) 
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
          removable_State pinfo sasinfo 
            {|
            Opsem.ECS := {|
                            Opsem.CurFunction := CurFunction2;
                            Opsem.CurBB := CurBB2;
                            Opsem.CurCmds := CurCmds1;
                            Opsem.Terminator := Terminator;
                            Opsem.Locals := Locals0;
                            Opsem.Allocas := Allocas0 |} :: ECS;
            Opsem.Mem := Mem0 |}).
      clear - Hwfpp1 H4 HuniqECs.
      destruct H4 as [l5 [ps5 [cs5 H4]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto; find_uniqEC.
    eapply RemoveSim.cmds_simulation_cons_inv' in Hnrem'; eauto.
    destruct Hnrem' as [cs1' [J1 J3]]; subst.
    left. 
    remember (free_allocas (los2, nts2) Mem0 Allocas) as R.
    destruct R; auto.
    symmetry in HeqR. simpl in H2.
    eapply mem_simulation__free_allocas_l2r in HeqR; eauto.
    destruct HeqR as [M2' [Hfree [Hmsim']]].
    congruence.

  Case "2".
    undefined_state__State_simulation_r2l_tac1.
    eapply RemoveSim.cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    assert (Hnrem' : ~
          removable_State pinfo sasinfo
            {|
            Opsem.ECS := {|
                            Opsem.CurFunction := CurFunction2;
                            Opsem.CurBB := CurBB2;
                            Opsem.CurCmds := CurCmds1;
                            Opsem.Terminator := Terminator;
                            Opsem.Locals := Locals0;
                            Opsem.Allocas := Allocas0 |} :: ECS;
            Opsem.Mem := Mem0 |}).
      clear - Hwfpp1 H4 HuniqECs.
      destruct H4 as [l5 [ps5 [cs5 H4]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto; find_uniqEC.
    eapply RemoveSim.cmds_simulation_cons_inv' in Hnrem'; eauto.
    destruct Hnrem' as [cs1' [J1 J3]]; subst.
    right. left. 
    destruct Hundef as [Hundef | Hundef]; auto.
    left.
    remember (free_allocas (los2, nts2) Mem0 Allocas) as R.
    destruct R; auto.
    symmetry in HeqR. simpl in H2.
    eapply mem_simulation__free_allocas_l2r in HeqR; eauto.
    destruct HeqR as [M2' [Hfree [Hmsim']]].
    congruence.

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
      repeat fill_ctxhole; exists gn; split; auto;
      match goal with 
        | |- context[?t] =>
          match type of t with 
            | option _ =>
              remember t as R
          end
      end;
      destruct R as [[]|]; auto;
      symmetry in HeqR2;
      eapply mem_simulation__malloc_l2r' in HeqR2; eauto 2;
      destruct HeqR2 as [Mem2' J4]; congruence
    ].

  Case "5".
    right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43.
    repeat fill_ctxhole; exists gn. split; auto.
    remember (free (los2, nts2) Mem0 gn) as R.
    destruct R; auto.
    symmetry in HeqR1. simpl in H2.
    eapply mem_simulation__free_l2r' in HeqR1; eauto.
    destruct HeqR1 as [M2' Hfree].
    congruence.
   
  Case "6".
    right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gvs [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43. 
    repeat fill_ctxhole; exists gvs. split; auto;
    match goal with 
      | |- context[?t] =>
        match type of t with 
          | option _ =>
            remember t as R
        end
    end;
    destruct R; auto.
    symmetry in HeqR1. simpl in H2.
    eapply mem_simulation__mload_l2r in HeqR1; eauto.
    destruct HeqR1 as [gv2 Hload].
    congruence.

  Case "7".
    right. right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gv [mgv [EQ1 [EQ2 Hundef]]]]; 
      inv EQ1; inv EQ2; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43. 
    repeat fill_ctxhole; exists gv; exists mgv.
    split; auto.
    match goal with 
      | |- context[?t] =>
        match type of t with 
          | option _ =>
            remember t as R
        end
    end;
    destruct R; auto.
    symmetry in HeqR2. simpl in H2.
    eapply mem_simulation__mstore_l2r in HeqR2; eauto.
    destruct HeqR2 as [M2' Hstore].
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
    repeat fill_ctxhole.
    exists fptr. split; auto.
    remember (OpsemAux.lookupExFdecViaPtr gl2 FunTable fptr) as R.
    destruct R as [[[]]|].
      inv_mbind.
      destruct Hundef as [gvs0 [EQ' Hundef]].
      dgvs_instantiate_inv.
      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_r2l; eauto.
      simpl.
      exists l1. split; auto.
      match goal with 
        | |- context[?t] =>
          match type of t with 
            | option _ =>
              remember t as R
          end
      end;
      destruct R as [[[]]|]; auto.
      match goal with 
        | |- context[?t] =>
          match type of t with 
            | option _ =>
              remember t as R
          end
      end;
      destruct R; auto.
      eapply callExternalFunction__mem_simulation_l2r in H2; eauto.
        destruct H2 as [M2' [oresult2 [tr2 [W1 [W2 [W3 W4]]]]]]; subst.
        rewrite W1 in Hundef. rewrite <- HeqR4 in Hundef. auto.

      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_None_r2l; eauto.
Qed.

Lemma undefined_state__sas_State_simulation_r2l: forall pinfo sasinfo cfg1 St1 cfg2
  St2 
  (Hwfpi: WF_PhiInfo pinfo) maxb (Hle: 0 <= maxb)
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) 
  (Hwfcfg: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 St1) 
  (Hpalloca: palloca_props.wf_State pinfo St1) 
  (Hstsim : State_simulation pinfo sasinfo cfg1 St1 cfg2 St2)
  (Hundef: OpsemPP.undefined_state cfg2 St2)
  (Hok: ~ sop_goeswrong cfg1 St1),
  exists St1', 
    Opsem.sop_star cfg1 St1 St1' E0 /\
    State_simulation pinfo sasinfo cfg1 St1' cfg2 St2 /\
    OpsemPP.undefined_state cfg1 St1'.
Proof.
  intros.
  eapply sas_is_bsim_removable_steps in Hstsim; eauto.
  destruct Hstsim as [FS1' [Hopstar [Hstsim Hnrm]]].
  exists FS1'.
  split; auto.
  split; auto.
    eapply undefined_state__sas_State_simulation_r2l' in Hstsim; 
      eauto using (@OpsemPP.preservation_star DGVs).
Qed.

Lemma sop_star__sas_State_simulation: forall pinfo sasinfo cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) 
  (Hwfcfg: OpsemPP.wf_Config cfg1) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1) 
  (Hstsim : State_simulation pinfo sasinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\
    State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent cfg1.
  generalize dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    assert (forall IS1'
            (Hok' : ~ sop_goeswrong cfg1 IS1')
            (Hwfpp': OpsemPP.wf_State cfg1 IS1')
            (Hnoalias': Promotability.wf_State maxb pinfo cfg1 IS1')
            (Hpalloca': palloca_props.wf_State pinfo IS1')
            (Hnrm': ~ removable_State pinfo sasinfo IS1')
            (Hstsim' : State_simulation pinfo sasinfo cfg1 IS1' cfg2 state1),
            exists FS1 : Opsem.State,
              Opsem.sop_star cfg1 IS1' FS1 (tr1 ** tr2) /\
              State_simulation pinfo sasinfo cfg1 FS1 cfg2 state3) as W1.
      clear - H Hopstar IHHopstar Hwfcfg Hwfpi Hless Hwfg. 
      intros.
      eapply sas_is_bsim in H; eauto.
      destruct H as [St1' [Hplus1 Hstsim]].
      eapply IHHopstar in Hstsim;
        eauto using palloca_props.preservation_plus, Promotability.preservation_plus,
        (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
      destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
      exists FS1. split; eauto.
        eapply OpsemProps.sop_star_trans; eauto.
        apply OpsemProps.sop_plus__implies__sop_star; eauto.

    eapply sas_is_bsim_removable_steps in Hstsim; eauto.
    destruct Hstsim as [St1' [Hopstar1 [Hstsim Hnrm]]].
    eapply palloca_props.preservation_star in Hpalloca; eauto.
    eapply Promotability.preservation_star in Hnoalias; eauto.
    eapply OpsemPP.preservation_star in Hwfpp; eauto.
    eapply sop_goeswrong__star in Hok; eauto.
    eapply W1 in Hstsim; eauto.
    destruct Hstsim as [FS1 [Hopstar'' Hstsim]].
    exists FS1.
    split; auto.
      clear - Hopstar1 Hopstar''.
      rewrite <- E0_left.
      eapply OpsemProps.sop_star_trans; eauto.
Qed.

Lemma sop_plus__sas_State_simulation: forall pinfo sasinfo cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) (Hwfcfg: OpsemPP.wf_Config cfg1)
  (Hwfpp: OpsemPP.wf_State cfg1 IS1) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hstsim : State_simulation pinfo sasinfo cfg1 IS1 cfg2 IS2)
  (Hopplus : Opsem.sop_plus cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, Opsem.sop_plus cfg1 IS1 FS1 tr /\
    State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  inv Hopplus.
  eapply sas_is_bsim in H; eauto.
  destruct H as [St1' [Hplus1 Hstsim']].
  eapply sop_star__sas_State_simulation in Hstsim'; eauto using
    palloca_props.preservation_plus, Promotability.preservation_plus,
    (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
  destruct Hstsim' as [FS1 [Hopstar Hstsim']].
  exists FS1. 
  split; auto.
    eapply OpsemProps.sop_plus_star__implies__sop_plus; eauto.
Qed.

Lemma sop_div__sas_State_simulation: forall pinfo laainfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)  (Hwfcfg: OpsemPP.wf_Config cfg1)
  (Hstsim : State_simulation pinfo laainfo cfg1 IS1 cfg2 IS2)
  (Hdiv : Opsem.sop_diverges cfg2 IS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  Opsem.sop_diverges cfg1 IS1 tr.
Proof.
  cofix CIH.
  intros.
  inv Hdiv.
  eapply sop_plus__sas_State_simulation in Hstsim; eauto 1.
  destruct Hstsim as [FS1 [Hopplus Hstsim']].
  econstructor; eauto.
  eapply CIH; eauto using
    palloca_props.preservation_plus, Promotability.preservation_plus,
    (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
Qed.

Require Import Program.Tactics.

(* The main result *)
Lemma sas_sim: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds)
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  S2 (Heq2: S2 = [module_intro los nts
                   (Ps1 ++
                     product_fdef
                     (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)) :: Ps2)])
  (Hok: defined_program S2 main VarArgs)
  (HwfS : wf_system S2),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
           (List.map (remove_block i0)
             (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))) :: Ps2)]
    S2 main VarArgs.
Proof.
  intros. 
  assert (blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) (PI_f pinfo) = true)
    as HBinF.
    rewrite Heq. simpl. apply InBlocksB_middle.
  assert (wf_fdef [module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)]
            (module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)) 
            (PI_f pinfo) /\ uniqFdef (PI_f pinfo)) as J.
    rewrite Heq in *. subst.
    apply wf_single_system__wf_uniq_fdef; auto.
  destruct J as [HwfF HuniqF].
  eapply find_st_ld__sasinfo in HBinF; eauto.
  destruct HBinF as [sasinfo [J1 [J2 [J3 [J4 J5]]]]]; subst.
  subst.
  change (fdef_intro fh
             (List.map (remove_block (SAS_sid1 pinfo sasinfo))
                (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))) with
    (remove_fdef (SAS_sid1 pinfo sasinfo)
      (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))).
  set (wf_prop1 := fun cfg st =>
         OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg st /\
         palloca_props.wf_State pinfo st /\
         exists maxb,
           MemProps.wf_globals maxb (OpsemAux.Globals cfg) /\ 0 <= maxb /\
           Promotability.wf_State maxb pinfo cfg st).
  set (wf_prop2 := fun cfg st =>
         OpsemPP.wf_Config cfg /\ @OpsemPP.wf_State DGVs cfg st).
  set (st_sim := fun cfg1 st1 cfg2 st2 => 
          State_simulation pinfo sasinfo cfg1 st1 cfg2 st2).
  set (sys_sim := fun s1 s2 => system_simulation pinfo sasinfo s1 s2).
  apply top_sim with (ftrans:=remove_fdef (SAS_sid1 pinfo sasinfo)) 
    (wf_prop1:=wf_prop1) (wf_prop2:=wf_prop2) (state_simulation:=st_sim)
    (system_simulation:=sys_sim);
     try solve [auto | unfold wf_prop1; tauto | unfold wf_prop2; tauto |
      unfold wf_prop1, wf_prop2; intros; destruct_conjs; try solve [
        eauto 10 using Promotability.preservation_star, 
          palloca_props.preservation_star, (@OpsemPP.preservation_star DGVs) |
        eapply sop_star__sas_State_simulation; eauto |
        eapply s_isFinialState__sas_State_simulation_r2l; eauto |
        eapply sop_div__sas_State_simulation; eauto |
        eapply undefined_state__sas_State_simulation_r2l; eauto |
        eapply s_isFinialState__sas_State_simulation_None_r2l; eauto
      ] |
      top_sim_syssim_tac fsim Fsim
    ].

    intros. subst.
    assert (OpsemPP.wf_Config cfg2 /\ OpsemPP.wf_State cfg2 IS2) as Hwfst'.
      eapply s_genInitState__opsem_wf in Hinit; eauto.
        eapply sas_wfS; eauto.
    eapply s_genInitState__sas_State_simulation in Hinit; eauto.
    destruct Hinit as [cfg1 [IS1 [Hinit1 Hstsim]]].
    assert (OpsemPP.wf_Config cfg1 /\ OpsemPP.wf_State cfg1 IS1) as Hwfst.
      eapply s_genInitState__opsem_wf; eauto.
    destruct Hwfst.
    assert (exists maxb,
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom.
      eapply Promotability.s_genInitState__wf_globals_promotable; eauto.
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]].
    assert (palloca_props.wf_State pinfo IS1) as Hpalloca.
      eapply palloca_props.s_genInitState__palloca; eauto.
    unfold wf_prop1, wf_prop2.
    eauto 12.
Qed.
