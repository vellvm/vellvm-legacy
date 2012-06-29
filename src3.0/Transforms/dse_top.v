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
Require Import vmem2reg.
Require Import memory_props.
Require Import program_sim.
Require Import sas_msim.
Require Import trans_tactic.
Require Import top_sim.
Require Import dse.
Require Import dse_wfS.

Lemma s_genInitState__dse_State_simulation: forall pinfo S1 S2 main VarArgs cfg2
  IS2 (Hssim: system_simulation pinfo S1 S2) (Hwfpi: WF_PhiInfo pinfo)
  (HwfS1: wf_system S1) Ps1 Ps2 los0 nts0 f0
  (Heq1: PI_f pinfo = f0)
  (Heq2: S1 = [module_intro los0 nts0 (Ps1 ++ product_fdef f0 :: Ps2)])
  (Hinit: Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2)),
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo cfg1 IS1 cfg2 IS2.
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
  fill_ctxhole. eauto.
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
  split; auto.
  eapply genGlobalAndInitMem__wf_globals_Mem in HeqR1; eauto.
  destruct HeqR1 as [J7 [J8 [J9 [J10 [J11 [J12 [J13 J14]]]]]]].
  repeat (split; auto).
    exists l0. exists ps0. exists nil. auto.
    exists l0. exists ps0. exists nil. auto.

    unfold dse_mem_inj. 
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

Ltac s_isFinialState__dse_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal := 
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
    apply cmds_simulation_nil_inv in Hstsim; try congruence |
    inv Hfinal
  ].

Lemma s_isFinialState__dse_State_simulation_l2r: forall pinfo cfg1 FS1 cfg2
  FS2 r  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 = ret r),
  Opsem.s_isFinialState cfg2 FS2 = ret r.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__dse_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
  destruct Terminator0; auto.
    destruct ES1, ES2; try solve [auto | inv Hstsim'].
    destruct ES1, ES2; try solve [auto | inv Hstsim'].
Qed.

Lemma s_isFinialState__dse_State_simulation_l2r': forall pinfo cfg1 FS1 cfg2
  FS2 (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 <> None),
  Opsem.s_isFinialState cfg2 FS2 <> None.
Proof.
  intros.
  remember (Opsem.s_isFinialState cfg1 FS1) as R.
  destruct R; try congruence.
  symmetry_ctx.
  eapply s_isFinialState__dse_State_simulation_l2r in Hstsim; eauto.
  congruence.
Qed.

Lemma s_isFinialState__dse_State_simulation_None_r2l:
  forall pinfo cfg1 FS1 cfg2 FS2
  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = None),
  Opsem.s_isFinialState cfg1 FS1 = None.
Proof.
  intros.
  remember (Opsem.s_isFinialState cfg1 FS1) as R.
  destruct R; try congruence.
  contradict Hfinal.
  eapply s_isFinialState__dse_State_simulation_l2r' in Hstsim; eauto.
    congruence.
Qed.

Lemma not_removable_State_inv: forall pinfo St,
  ~ removable_State pinfo St ->
  match St with
  | {| Opsem.ECS := {| Opsem.CurFunction := F;
                       Opsem.CurBB := _;
                       Opsem.CurCmds := c :: _;
                       Opsem.Terminator := _;
                       Opsem.Locals := _;
                       Opsem.Allocas := _ |} :: _;
       Opsem.Mem := Mem |} => PI_f pinfo = F -> 
                              store_in_cmd (PI_id pinfo) c = false
  | _ => True
  end.
Proof.
  intros.
  destruct St; auto.
  destruct ECS; auto.
  destruct e; auto.
  destruct CurCmds; auto.
  simpl in H.
  destruct c; try tauto.
  destruct value2; try tauto.
  intros.
  destruct (fdef_dec (PI_f pinfo) CurFunction); try congruence.
  simpl.
  destruct (id_dec (PI_id pinfo) id0); subst; try tauto. 
  destruct (id_dec id0 (PI_id pinfo)); subst; tauto.
Qed.

Lemma s_isFinialState__dse_State_simulation_r2l':
  forall pinfo cfg1 FS1 cfg2 FS2 r
  (Hnrem: ~removable_State pinfo FS1) 
  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r),
  Opsem.s_isFinialState cfg1 FS1 = ret r.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__dse_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
    destruct Terminator0; auto.
      destruct ES1, ES2; try solve [auto | inv Hstsim'].
      destruct ES1, ES2; try solve [auto | inv Hstsim'].

   apply not_removable_State_inv in Hnrem.
   apply cmds_simulation_nelim_cons_inv in Hstsim; auto. 
   destruct Hstsim as [cs2' [J1 Hstsim]]; congruence.
Qed.

Lemma split_cmds_by_P: forall P (cs:cmds),
  exists cs1, exists cs2, 
    cs = cs1 ++ cs2 /\
    List.Forall (fun c => P c = true) cs1 /\
    match cs2 with 
    | nil => True
    | c2::_ => P c2 = false
    end.
Proof.
  induction cs.
    exists nil. exists nil. auto.

    destruct IHcs as [cs1 [cs2 [J1 [J2 J3]]]]; subst.
    remember (P a) as R.
    destruct R.
      exists (a::cs1). exists cs2.
      simpl_env.
      split; auto.
      split; auto.
        simpl. constructor; auto.
     
      exists nil. exists (a::cs1++cs2).
      split; auto.
Qed.

Fixpoint removable_cmds pinfo f b cs1 cs2 tmn ES1 : Prop :=
match cs1 with
| nil => True
| c1::cs1' =>
    (forall lc' als' Mem',
    removable_State pinfo
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f;
                        Opsem.CurBB := b;
                        Opsem.CurCmds := c1::cs1'++cs2;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc';
                        Opsem.Allocas := als' |} :: ES1;
           Opsem.Mem := Mem' |}) /\
    removable_cmds pinfo f b cs1' cs2 tmn ES1
end.

Lemma removable_cmds_intro: forall pinfo tmn ES1 b cs2 cs1
  (J2 : Forall (fun c : cmd => store_in_cmd (PI_id pinfo) c = true) cs1),
  removable_cmds pinfo (PI_f pinfo) b cs1 cs2 tmn ES1.
Proof.
  induction 1; simpl; auto.
    split; auto.
      intros.
      destruct x; tinv H.
      destruct value2; tinv H.
      simpl in H.
      destruct_if.
      destruct_if.
      destruct (id_dec id0 (PI_id pinfo)); auto. inv H.
Qed.

Lemma removable_State__non_removable_State: forall pinfo f b tmn ES1 c cs1 lc 
  als Mem
  (Hrem : removable_State pinfo
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f;
                        Opsem.CurBB := b;
                        Opsem.CurCmds := c :: cs1;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: ES1;
           Opsem.Mem := Mem |}),
  exists cs11, exists cs12,
    c :: cs1 = cs11 ++ cs12 /\
    removable_cmds pinfo f b cs11 cs12 tmn ES1 /\
    forall lc' als' Mem',
    ~ removable_State pinfo
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f;
                        Opsem.CurBB := b;
                        Opsem.CurCmds := cs12;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc';
                        Opsem.Allocas := als' |} :: ES1;
           Opsem.Mem := Mem' |}.
Proof.
  simpl. intros.
  destruct (split_cmds_by_P (store_in_cmd (PI_id pinfo)) cs1)
    as [cs11 [cs12 [J1 [J2 J3]]]]; subst.
  exists (c::cs11). exists cs12.
  destruct c; try tauto.
  destruct value2; try tauto.
  destruct_if; try tauto.
  destruct_if; try tauto.
  split; auto.
  split.
    apply removable_cmds_intro.
    constructor; simpl; auto.
      destruct (id_dec (PI_id pinfo) (PI_id pinfo)); auto.

    intros.
    destruct cs12; auto.
    destruct c; auto.
    destruct value2; auto.
    simpl in J3.
    destruct_if; auto.
    destruct (id_dec (PI_id pinfo) (PI_id pinfo)); auto.
      inv J3.
Qed.

Lemma removable_State__isnt__final: forall pinfo cfg St
  (Hrm: removable_State pinfo St),
  Opsem.s_isFinialState cfg St = None.
Proof.
  intros.
  destruct St as [Es Mem].
  destruct cfg.
  destruct Es as [|[] Es]; tinv Hrm.
  simpl in *.
  destruct CurCmds; tauto.
Qed.

Lemma dse_removable_cmds : forall maxb pinfo Cfg1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) (Hle: 0 <= maxb)
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfcfg: OpsemPP.wf_Config Cfg1) 
  f1 b1 cs12 lc1 tmn1 als1 ES1 cs11 
  St1 (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hrm: removable_cmds pinfo f1 b1 cs11 cs12 tmn1 ES1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1)
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hsim: State_simulation pinfo Cfg1 St1 Cfg2 St2) 
  (Hok: ~ sop_goeswrong Cfg1 St1) Mem1
  (Heq1: St1 = {|Opsem.ECS := {|
                        Opsem.CurFunction := f1;
                        Opsem.CurBB := b1;
                        Opsem.CurCmds := cs11++cs12;
                        Opsem.Terminator := tmn1;
                        Opsem.Locals := lc1;
                        Opsem.Allocas := als1 |} :: ES1;
                 Opsem.Mem := Mem1 |}),
  exists Mem1', 
    Opsem.sop_star Cfg1 St1 
     {|Opsem.ECS := {|  Opsem.CurFunction := f1;
                        Opsem.CurBB := b1;
                        Opsem.CurCmds := cs12;
                        Opsem.Terminator := tmn1;
                        Opsem.Locals := lc1;
                        Opsem.Allocas := als1 |} :: ES1;
       Opsem.Mem := Mem1' |} E0 /\
   State_simulation pinfo Cfg1
     {|Opsem.ECS := {|  Opsem.CurFunction := f1;
                        Opsem.CurBB := b1;
                        Opsem.CurCmds := cs12;
                        Opsem.Terminator := tmn1;
                        Opsem.Locals := lc1;
                        Opsem.Allocas := als1 |} :: ES1;
       Opsem.Mem := Mem1' |} Cfg2 St2.
Proof.
  induction cs11; intros; subst.
    exists Mem1. split; auto.

    destruct Hrm as [Hrm1 Hrm2].
    assert (Opsem.s_isFinialState Cfg1 
      {|Opsem.ECS := {|
                    Opsem.CurFunction := f1;
                    Opsem.CurBB := b1;
                    Opsem.CurCmds := (a :: cs11) ++ cs12;
                    Opsem.Terminator := tmn1;
                    Opsem.Locals := lc1;
                    Opsem.Allocas := als1 |} :: ES1;
        Opsem.Mem := Mem1 |} = None) as Hnfinal.
    eapply removable_State__isnt__final; eauto.

    eapply dse_is_sim in Hsim; eauto.
    destruct Hsim as [Hsim _].
    assert (J:=Hwfpp).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]]; try congruence.
      SSCase "step".
      assert (Hop1':=Hop1).
      apply_clear Hsim in Hop1'; auto.
      destruct Hop1' as [J1 J2]; subst.
      assert (Hwfpp':=Hop1).
      apply OpsemPP.preservation in Hwfpp'; auto.     
      assert (Hprom':=Hop1).
      eapply Promotability.preservation in Hprom'; eauto.     
      assert (Hpalloca':=Hop1).
      eapply palloca_props.preservation in Hpalloca'; eauto.     
      assert (exists m, IS1' =
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f1;
                        Opsem.CurBB := b1;
                        Opsem.CurCmds := cs11 ++ cs12;
                        Opsem.Terminator := tmn1;
                        Opsem.Locals := lc1;
                        Opsem.Allocas := als1 |} :: ES1;
           Opsem.Mem := m |}) as Heq.
        assert (K:=Hrm1 nil nil Mem1).
        simpl in K.
        destruct a; try tauto.
        inv Hop1. eauto.
      destruct Heq as [m Heq]; subst.
      eapply_clear IHcs11 in J1; eauto using sop_goeswrong__step.
      destruct J1 as [Mem1' [J1 J2]].
      exists Mem1'.
      split; auto.
        rewrite <- E0_left. econstructor; eauto.
     
      SSCase "stuck".
      clear - Hundef1 Hok Hnfinal.
      apply undefined_state__stuck' in Hundef1.
      contradict Hok.
      exists {|Opsem.ECS := {|
                  Opsem.CurFunction := f1;
                  Opsem.CurBB := b1;
                  Opsem.CurCmds := (a::cs11) ++ cs12;
                  Opsem.Terminator := tmn1;
                  Opsem.Locals := lc1;
                  Opsem.Allocas := als1 |} :: ES1;
               Opsem.Mem := Mem1|}.
      exists E0.
      split; auto.
Qed.

Lemma s_isFinialState__dse_State_simulation_r2l:
  forall pinfo cfg1 FS1 cfg2 FS2 r maxb
  (Hwfpi: WF_PhiInfo pinfo) (Hle: 0 <= maxb)
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) 
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 FS1)
  (Hpalloca: palloca_props.wf_State pinfo FS1)
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r)
  (Hok: ~ sop_goeswrong cfg1 FS1),
  exists FS1', 
    Opsem.sop_star cfg1 FS1 FS1' E0 /\
    State_simulation pinfo cfg1 FS1' cfg2 FS2 /\
    Opsem.s_isFinialState cfg1 FS1' = ret r.
Proof.
  intros.
  destruct (removable_State_dec pinfo FS1) as [Hrem | Hnrem].
Case "removable".
    assert (G:=Hstsim).
    destruct cfg2 as [S2 [los2 nts2] gl2 fs2];
    destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
    destruct FS1 as [[|[? ? cs1 ? ?] ES1]];
    destruct FS2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
      auto |
      destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst; inv Hstsim |
      inv Hrem
    ].
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X; simpl;
    destruct Hstsim as [Hstsim Hstsim'];
    fold ECs_simulation in Hstsim'.
    destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
    destruct cs1, cs2; try solve [
      auto |
      apply cmds_simulation_nil_inv in Hstsim; try congruence |
      inv Hfinal |
      inv Hrem
    ].
    apply removable_State__non_removable_State in Hrem.
    destruct Hrem as [cs11 [cs12 [J1 [J2 J3]]]].
    rewrite J1 in *.
    eapply dse_removable_cmds in G; eauto.
    destruct G as [Mem1' [G1 G2]].
    exists 
       {|Opsem.ECS := {|
                      Opsem.CurFunction := CurFunction;
                      Opsem.CurBB := CurBB;
                      Opsem.CurCmds := cs12;
                      Opsem.Terminator := Terminator0;
                      Opsem.Locals := Locals0;
                      Opsem.Allocas := Allocas0 |} :: ES1;
         Opsem.Mem := Mem1' |}.
    split; auto.
      split.
        unfold State_simulation in G2. auto.
        eapply s_isFinialState__dse_State_simulation_r2l' in G2; eauto.

Case "unremovable".
    assert (J:=Hstsim).
    eapply s_isFinialState__dse_State_simulation_r2l' in Hstsim; eauto.
Qed.

Lemma cmds_simulation_nil_inv' : forall (pinfo : PhiInfo) 
  (f1 : fdef) (cs1 : list cmd) b1 tmn1 lc1 als1 ECS Mem1
  (Hnrem : ~
          removable_State pinfo
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := f1;
                         Opsem.CurBB := b1;
                         Opsem.CurCmds := cs1;
                         Opsem.Terminator := tmn1;
                         Opsem.Locals := lc1;
                         Opsem.Allocas := als1 |} :: ECS;
            Opsem.Mem := Mem1 |}),
  cmds_simulation pinfo f1 cs1 nil -> cs1 = nil.
Proof.
  simpl.
  unfold cmds_simulation. intros.
  destruct_if; auto.
  destruct cs1; auto.
  simpl in *.
  destruct c; try congruence.
  destruct value2; try congruence.
  destruct_if; try tauto.
Qed.

Lemma cmds_simulation_cons_inv' : forall (pinfo : PhiInfo) 
  (f1 : fdef) b1 lc1 cs tmn1 als1 c cs2 ECS Mem1
  (Hnrem : ~
          removable_State pinfo
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := f1;
                         Opsem.CurBB := b1;
                         Opsem.CurCmds := cs;
                         Opsem.Terminator := tmn1;
                         Opsem.Locals := lc1;
                         Opsem.Allocas := als1 |} :: ECS;
            Opsem.Mem := Mem1 |}),
  cmds_simulation pinfo f1 cs (c::cs2) -> 
   exists cs1, 
     cs = c::cs1 /\
     cmds_simulation pinfo f1 cs1 cs2.
Proof.
  simpl.
  unfold cmds_simulation. intros.
  destruct_if; eauto.
  destruct cs; tinv H1.
  simpl in *.
  destruct c0; inv H1; eauto.
  destruct value2; inv H0; eauto.
  destruct_if; try tauto. eauto.
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
    destruct St2 as [[|[? [? ? ? tmn] CurCmds tmn' ?] ?] ?]; try tauto;
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
      eapply cmds_simulation_cons_inv' in Hstsim; eauto; subst;
      destruct Hstsim as [c1' [J2 J3]]; subst
     end.

Lemma stacked_frame__unremovable: forall cfg EC1 EC2 ECS Mem0 pinfo
  (HBinF: match Opsem.CurBB EC1 with 
   | block_intro _ _ _ (insn_return _ _ _) => True
   | block_intro _ _ _ (insn_return_void _) => True
   | _ => False
   end)
  (Hwfpp1 : OpsemPP.wf_State cfg
             {| Opsem.ECS := EC1 :: EC2 :: ECS; Opsem.Mem := Mem0 |}),
  ~ removable_State pinfo
     {| Opsem.ECS := EC2 :: ECS; Opsem.Mem := Mem0 |}.
Proof.
  intros.
  destruct EC1, EC2; simpl in *. destruct cfg. destruct CurTargetData.
  destruct Hwfpp1 as 
     [_ [[_ [HbInF1 [_ [_ [_ _]]]]] [_ Hiscall]]].
  apply Hiscall in HbInF1.
  destruct CurBB as [? ? ? []]; tinv HBinF.
    destruct CurCmds0 as [|[]]; tinv HbInF1. tauto.
    destruct CurCmds0 as [|[]]; tinv HbInF1. tauto.
Qed.

Lemma mem_simulation__malloc_l2r': forall (pinfo : PhiInfo) TD ECs M1 M2
  (Hmsim : mem_simulation pinfo TD ECs M1 M2)
  (Mem'0 : mem) (tsz0 : sz) align0 gn mb M1'
  (H2 : malloc TD M1 tsz0 gn align0 = ret (M1', mb)),
  exists M2',
     malloc TD M2 tsz0 gn align0 = ret (M2', mb).
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmim3 Hmsim2]].
  unfold dse_mem_inj in *.
  inv_mbind. 
  destruct (@no_alias_head_tail_ex pinfo ECs) as [ombs J].
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
  (H1 : mload td M1 mp t align0 = ret gv)
  (Hmsim : mem_simulation pinfo td ECs M1 M2),
  exists gv0, mload td M2 mp t align0 = ret gv0.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  apply mload_inv in H1.
  destruct H1 as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold dse_mem_inj in Hmsim2.
  inv_mbind. 
  destruct (@no_alias_head_tail_ex pinfo ECs) as [ombs J].
  apply_clear Hmsim2 in J.
  unfold mload. repeat fill_ctxhole. simpl.
  eapply SASmsim.mload_aux_inj_ex with (b2:=b)(delta:=0) in J; eauto.
  replace (Int.signed 31 ofs + 0) with (Int.signed 31 ofs)  in J by omega.
  destruct J as [gv2 J]; eauto.
Qed.

Lemma mem_simulation__mstore_l2r: forall td M1 mp2 t gv1 align0 M1' M2 ECs
  (H3 : mstore td M1 mp2 t gv1 align0 = ret M1') pinfo
  (Hmsim : mem_simulation pinfo td ECs M1 M2),
  exists M2', 
    mstore td M2 mp2 t gv1 align0 = ret M2'.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  apply mstore_inversion in H3.
  destruct H3 as [b [ofs [cm [J1 J2]]]]; subst.
  unfold dse_mem_inj in *.
  inv_mbind.
  destruct (@no_alias_head_tail_ex pinfo ECs) as [ombs J].
  apply_clear Hmsim2 in J.
  unfold mstore. simpl. 
  eapply SASmsim.mstore_aux_inject_id_mapped_inj in J; eauto.
  destruct J as [gv2 [J1 J4]]; eauto.
Qed.

Lemma undefined_state__dse_State_simulation_r2l': forall pinfo cfg1 St1 cfg2
  St2 
  (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (Hstsim : State_simulation pinfo cfg1 St1 cfg2 St2)
  (Hnrem: ~removable_State pinfo St1) 
  (Hundef: OpsemPP.undefined_state cfg2 St2),
  OpsemPP.undefined_state cfg1 St1.
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
    eapply cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    assert (Hnrem' : ~
          removable_State pinfo
            {|
            Opsem.ECS := {|
                            Opsem.CurFunction := CurFunction2;
                            Opsem.CurBB := CurBB2;
                            Opsem.CurCmds := CurCmds1;
                            Opsem.Terminator := Terminator;
                            Opsem.Locals := Locals0;
                            Opsem.Allocas := Allocas0 |} :: ECS;
            Opsem.Mem := Mem0 |}).
      clear - Hwfpp1 H4.
      destruct H4 as [l5 [ps5 [cs5 H4]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto.
    eapply cmds_simulation_cons_inv' in Hnrem'; eauto.
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
    eapply cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    assert (Hnrem' : ~
          removable_State pinfo
            {|
            Opsem.ECS := {|
                            Opsem.CurFunction := CurFunction2;
                            Opsem.CurBB := CurBB2;
                            Opsem.CurCmds := CurCmds1;
                            Opsem.Terminator := Terminator;
                            Opsem.Locals := Locals0;
                            Opsem.Allocas := Allocas0 |} :: ECS;
            Opsem.Mem := Mem0 |}).
      clear - Hwfpp1 H4.
      destruct H4 as [l5 [ps5 [cs5 H4]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto.
    eapply cmds_simulation_cons_inv' in Hnrem'; eauto.
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
    eapply cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    right. right. left. auto.

  Case "4".
    right; right; right; left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' Locals] ?] ?]; try solve [
      tauto |
      inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind;
      undefined_state__State_simulation_r2l_tac41;
      undefined_state__d_State_simulation_r2l_tac43;
      repeat fill_ctxhole; exists gn; split; auto;
      remember (malloc (los2, nts2) Mem0 s gn align5) as R;
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
    repeat fill_ctxhole; exists gvs. split; auto.
    remember (mload (los2, nts2) Mem0 gvs typ5 align5) as R.
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
    remember (mstore (los2, nts2) Mem0 mgv typ5 gv align5) as R.
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
    eapply cmds_simulation_cons_inv' in Hstsim; subst; eauto.
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
      remember (callExternalOrIntrinsics (los2, nts2) fs2 Mem0 id0 typ0
          (args2Typs args5) deckind5 l1) as R.
      destruct R as [[[]]|]; auto.
      remember (Opsem.exCallUpdateLocals (los2, nts2) typ5 noret5 id5 o Locals) as R.
      destruct R; auto.
      eapply callExternalFunction__mem_simulation_l2r in H2; eauto.
        destruct H2 as [M2' [oresult2 [tr2 [W1 [W2 [W3 W4]]]]]]; subst.
        rewrite W1 in Hundef. rewrite <- HeqR4 in Hundef. auto.

      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_None_r2l; eauto.
Qed.

Lemma undefined_state__dse_State_simulation_r2l: forall pinfo cfg1 St1 cfg2
  St2 (Hwfpi: WF_PhiInfo pinfo) maxb (Hle: 0 <= maxb)
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) 
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 St1)
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (Hstsim : State_simulation pinfo cfg1 St1 cfg2 St2)
  (Hundef: OpsemPP.undefined_state cfg2 St2)
  (Hok: ~ sop_goeswrong cfg1 St1),
  exists St1', 
    Opsem.sop_star cfg1 St1 St1' E0 /\
    State_simulation pinfo cfg1 St1' cfg2 St2 /\
    OpsemPP.undefined_state cfg1 St1'.
Proof.
  intros.
  destruct (removable_State_dec pinfo St1) as [Hrem | Hnrem].
Case "removable".
    assert (G:=Hstsim).
    destruct cfg2 as [S2 [los2 nts2] gl2 fs2];
    destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
    destruct St1 as [[|[? ? cs1 ? ?] ES1]];
    destruct St2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
      auto |
      destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst; inv Hstsim |
      inv Hrem
    ].
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X; simpl;
    destruct Hstsim as [Hstsim Hstsim'];
    fold ECs_simulation in Hstsim'.
    destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst.
    destruct cs1; try solve [
      auto |
      apply cmds_simulation_nil_inv in Hstsim; try congruence |
      inv Hrem
    ].
    apply removable_State__non_removable_State in Hrem.
    destruct Hrem as [cs11 [cs12 [J1 [J2 J3]]]].
    rewrite J1 in *.
    eapply dse_removable_cmds in G; eauto.
    destruct G as [Mem1' [G1 G2]].
    exists 
       {|Opsem.ECS := {|
                      Opsem.CurFunction := CurFunction;
                      Opsem.CurBB := CurBB;
                      Opsem.CurCmds := cs12;
                      Opsem.Terminator := Terminator0;
                      Opsem.Locals := Locals0;
                      Opsem.Allocas := Allocas0 |} :: ES1;
         Opsem.Mem := Mem1' |}.
    split; auto.
      split.
        unfold State_simulation in G2. auto.
        eapply undefined_state__dse_State_simulation_r2l' in G2; eauto.
          eapply OpsemPP.preservation_star; eauto.

Case "unremovable".
    assert (J:=Hstsim).
    eapply undefined_state__dse_State_simulation_r2l' in Hstsim; eauto.
Qed.

Lemma dse_is_bsim : forall maxb pinfo Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) (Hless: 0 <= maxb)
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1)
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hsim: State_simulation pinfo Cfg1 St1 Cfg2 St2)
  (Hok: ~ sop_goeswrong Cfg1 St1)
  St2' tr2 (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2),
  exists St1',
    Opsem.sop_plus Cfg1 St1 St1' tr2 /\
    State_simulation pinfo Cfg1 St1' Cfg2 St2'.
Proof.
  intros.
  assert (forall IS1'
            (Hok' : ~ sop_goeswrong Cfg1 IS1')
            (Hwfpp': OpsemPP.wf_State Cfg1 IS1')
            (Hnoalias': Promotability.wf_State maxb pinfo Cfg1 IS1')
            (Hpalloca': palloca_props.wf_State pinfo IS1')
            (Hnrm': ~ removable_State pinfo IS1')
            (Hstsim' : State_simulation pinfo Cfg1 IS1' Cfg2 St2),
            exists FS1 : Opsem.State,
              Opsem.sop_plus Cfg1 IS1' FS1 tr2 /\
              State_simulation pinfo Cfg1 FS1 Cfg2 St2') as W1.
    clear - Hop2 Hwfcfg Hwfpi Hless Hwfg Hnld.
    intros.
    assert (Hnfinal1: Opsem.s_isFinialState Cfg1 IS1' = merror).
      remember (Opsem.s_isFinialState Cfg1 IS1') as R.
      destruct R; auto.
      apply s_isFinialState__dse_State_simulation_l2r' in Hstsim'; 
        try solve [auto | congruence].
        contradict Hop2; eauto using s_isFinialState__stuck.
    assert (J:=Hwfpp').
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1'' [tr0 Hop1]] | Hundef1]]; try congruence.
      assert (OpsemPP.wf_State Cfg1 IS1'') as Hwfpp''.
        apply OpsemPP.preservation in Hop1; auto.
      assert (Promotability.wf_State maxb pinfo Cfg1 IS1'') as Hnoalias''.
        eapply Promotability.preservation in Hop1; eauto.
      assert (palloca_props.wf_State pinfo IS1'') as Hpalloca''.
        eapply palloca_props.preservation in Hop1; eauto.
      eapply dse_is_sim in Hstsim'; eauto.
      destruct Hstsim' as [Hstsim1 Hstsim2].
      eapply Hstsim2 in Hnrm'; eauto.
      destruct Hnrm' as [Hstsim EQ]; subst.
      exists IS1''. 
      split; eauto.
        apply OpsemProps.sInsn__implies__sop_plus; auto.

      apply undefined_state__stuck' in Hundef1.
      contradict Hok'. exists IS1'. exists E0. split; auto.

  destruct (@removable_State_dec pinfo St1) as [Hrm | Hnrm]; eauto.
  destruct St1 as [[|[f1 b1 [|c1 cs1] tmn1 lc1 als1] ES1] M1]; tinv Hrm.
  apply removable_State__non_removable_State in Hrm.
  destruct Hrm as [cs11 [cs12 [J1 [J2 J3]]]].
  rewrite J1 in *.
  eapply dse_removable_cmds in Hsim; eauto.
  destruct Hsim as [M1' [Hopstar' Hstsim]].
  assert (Hnrm:=@J3 lc1 als1 M1'). clear J3.
  eapply palloca_props.preservation_star in Hpalloca; eauto.
  eapply Promotability.preservation_star in Hnoalias; eauto.
  eapply OpsemPP.preservation_star in Hwfpp; eauto.
  eapply sop_goeswrong__star in Hok; eauto.
  eapply W1 in Hstsim; eauto.
  destruct Hstsim as [FS1 [Hopplus'' Hstsim]].
  exists FS1.
  split; auto.
    clear - Hopstar' Hopplus''.
    rewrite <- E0_left.
    eapply OpsemProps.sop_star_plus__implies__sop_plus; eauto.
Qed.

Lemma sop_star__dse_State_simulation: forall pinfo  cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) (Hwfcfg: OpsemPP.wf_Config cfg1)
  (Hwfpp: OpsemPP.wf_State cfg1 IS1)
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hstsim : State_simulation pinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\
    State_simulation pinfo cfg1 FS1 cfg2 FS2.
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
            (Hnrm': ~ removable_State pinfo IS1')
            (Hstsim' : State_simulation pinfo cfg1 IS1' cfg2 state1),
            exists FS1 : Opsem.State,
              Opsem.sop_star cfg1 IS1' FS1 (tr1 ** tr2) /\
              State_simulation pinfo cfg1 FS1 cfg2 state3) as W1.
      clear - H Hopstar IHHopstar Hwfcfg Hwfpi Hless Hwfg Hnld. 
      intros.
      eapply dse_is_bsim in H; eauto.
      destruct H as [St1' [Hplus1 Hstsim]].
      eapply IHHopstar in Hstsim;
        eauto using palloca_props.preservation_plus, Promotability.preservation_plus,
        (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
      destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
      exists FS1. split; eauto.
        eapply OpsemProps.sop_star_trans; eauto.
        apply OpsemProps.sop_plus__implies__sop_star; eauto.

    destruct (@removable_State_dec pinfo IS1) as [Hrm | Hnrm]; eauto.
    destruct IS1 as [[|[f1 b1 [|c1 cs1] tmn1 lc1 als1] ES1] M1]; tinv Hrm.
    apply removable_State__non_removable_State in Hrm.
    destruct Hrm as [cs11 [cs12 [J1 [J2 J3]]]].
    rewrite J1 in *.
    eapply dse_removable_cmds in Hstsim; eauto.
    destruct Hstsim as [M1' [Hopstar' Hstsim]].
    assert (Hnrm:=@J3 lc1 als1 M1'). clear J3.
    eapply palloca_props.preservation_star in Hpalloca; eauto.
    eapply Promotability.preservation_star in Hnoalias; eauto.
    eapply OpsemPP.preservation_star in Hwfpp; eauto.
    eapply sop_goeswrong__star in Hok; eauto.
    eapply W1 in Hstsim; eauto.
    destruct Hstsim as [FS1 [Hopstar'' Hstsim]].
    exists FS1.
    split; auto.
      clear - Hopstar' Hopstar''.
      rewrite <- E0_left.
      eapply OpsemProps.sop_star_trans; eauto.
Qed.

Lemma sop_plus__dse_State_simulation: forall pinfo  cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) (Hwfcfg: OpsemPP.wf_Config cfg1)
  (Hwfpp: OpsemPP.wf_State cfg1 IS1)
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hstsim : State_simulation pinfo cfg1 IS1 cfg2 IS2)
  (Hopplus : Opsem.sop_plus cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, Opsem.sop_plus cfg1 IS1 FS1 tr /\
    State_simulation pinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  inv Hopplus.
  eapply dse_is_bsim in H; eauto.
  destruct H as [St1' [Hplus1 Hstsim']].
  eapply sop_star__dse_State_simulation in Hstsim'; eauto using
    palloca_props.preservation_plus, Promotability.preservation_plus,
    (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
  destruct Hstsim' as [FS1 [Hopstar Hstsim']].
  exists FS1. 
  split; auto.
    eapply OpsemProps.sop_plus_star__implies__sop_plus; eauto.
Qed.

Section TOPSIM.

Variables (pinfo:PhiInfo) (cfg1:OpsemAux.Config) (IS1:@Opsem.State DGVs) 
          (cfg2:OpsemAux.Config) (IS2:@Opsem.State DGVs) (maxb:Values.block).

Hypothesis (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfcfg: OpsemPP.wf_Config cfg1) (Hwfpp: OpsemPP.wf_State cfg1 IS1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hok : ~ sop_goeswrong cfg1 IS1)
  (Hstsim : State_simulation pinfo cfg1 IS1 cfg2 IS2).

Lemma sop_div__dse_State_simulation: forall
  tr (Hdiv : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Proof.
  repeat match goal with
  | H:_ |- _ => generalize dependent H; clear H
  end. 
  cofix CIH.
  intros.
  inv Hdiv.
  eapply sop_plus__dse_State_simulation in Hstsim; eauto 1.
  destruct Hstsim as [FS1 [Hopplus Hstsim']].
  econstructor; eauto.
  eapply CIH; eauto using
    palloca_props.preservation_plus, Promotability.preservation_plus,
    (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus.
Qed.

End TOPSIM.

Lemma dse_sim: forall (pinfo:PhiInfo) f pid Ps1 Ps2 los nts main
  VarArgs (Heq1: PI_id pinfo = pid) (Heq2: PI_f pinfo = f)
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hok: defined_program [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
          main VarArgs)
  (Hnld: load_in_fdef pid f = false),
  program_sim
    [module_intro los nts
      (Ps1 ++  product_fdef (elim_dead_st_fdef pid f) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Proof.
  intros. subst.
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation pinfo
    [module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2)]
    [module_intro los nts
      (Ps1 ++ product_fdef (elim_dead_st_fdef (PI_id pinfo) (PI_f pinfo))
       :: Ps2)]) as Hssim.
    constructor; auto.
    repeat split; auto.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    unfold TopSim.products_simulation. simpl. unfold system_simulation.
    apply uniq_products_simulation; auto.

Ltac dse_sim_init :=
match goal with
| H: Opsem.s_genInitState [module_intro ?los ?nts _] _ _ _ = Some (?cfg, ?IS), 
  pinfo: PhiInfo |- _ =>
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg IS) as Hwfst';
      try solve [eapply s_genInitState__opsem_wf in H; eauto using dse_wfS];
    eapply s_genInitState__dse_State_simulation in H; eauto;
    destruct H as [cfg1 [IS1 [Hinit1 Hstsim]]];
    assert (OpsemPP.wf_Config cfg1/\ OpsemPP.wf_State cfg1 IS1) as Hwfst;
      try solve [eapply s_genInitState__opsem_wf; eauto];
    assert (exists maxb,
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom;
      try solve [eapply Promotability.s_genInitState__wf_globals_promotable; eauto];
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]];
    assert (palloca_props.wf_State pinfo IS1) as Hpalloca;
      try solve [eapply palloca_props.s_genInitState__palloca; eauto]
end.

Ltac dse_sim_end :=
match goal with
| Hstsim' : State_simulation ?pinfo ?cfg1 ?FS1 ?cfg ?FS,
  Hopstar1 : Opsem.sop_star ?cfg1 _ ?FS1 _,
  Hwfg: MemProps.wf_globals ?maxb _  |- _ =>
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
    dse_sim_init.
    eapply sop_star__dse_State_simulation in Hstsim;
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    dse_sim_end.
    eapply s_isFinialState__dse_State_simulation_r2l in Hstsim';
      eauto using sop_goeswrong__star, defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim' as [FS1' [Hopstar1' [Hstsim'' Hfinal]]].
    assert (Opsem.sop_star cfg1 IS1 FS1' tr) as Hopstar1''.
      rewrite <- E0_right.
      eapply OpsemProps.sop_star_trans; eauto.
    exists t. split; auto using result_match_relf. econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    dse_sim_init.
    eapply sop_div__dse_State_simulation in Hstsim; 
      try solve [eauto using defined_program__doesnt__go_wrong| tauto].
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.

    intros tr t Hgowrong.
    inv Hgowrong.
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg t) as HwfSt.
      eapply s_genInitState__opsem_wf in H; eauto using dse_wfS.
      destruct H as [Hcfg2 HwfSt2].
      apply OpsemPP.preservation_star in H0; auto.
    assert (OpsemPP.undefined_state cfg t) as Hundef.
      apply stuck__undefined_state in H2; try solve [auto | tauto].
    dse_sim_init.
    eapply sop_star__dse_State_simulation in Hstsim; 
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    dse_sim_end.
    assert (Hundef':=Hundef).
    eapply undefined_state__dse_State_simulation_r2l in Hundef'; 
      try solve [eauto using sop_goeswrong__star, defined_program__doesnt__go_wrong | tauto].
    destruct Hundef' as [FS1' [Hopstar2 [Hsim Hundef']]].
    assert (Opsem.s_isFinialState cfg1 FS1' = merror) as Hfinal'.
      apply OpsemPP.preservation_star in Hopstar2; auto; try tauto.
      eapply s_isFinialState__dse_State_simulation_None_r2l in H2; 
        try solve [eauto | tauto].
    apply undefined_state__stuck' in Hundef'.
    rewrite <- E0_right with (t:=tr). exists FS1'.
    econstructor; eauto using (@OpsemProps.sop_star_trans DGVs).   
Qed.
