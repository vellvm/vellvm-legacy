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
Require Import sb_ds_trans_lib.
Require Import genericvalues_inject.
Require Import sb_metadata.
Require Import program_sim.
Require Import trans_tactic.
Require Import top_sim.
Require Import dae_defs.
Require Import dae.
Require Import dae_wfS.

Lemma s_genInitState__dae_State_simulation': forall pinfo S1 S2 main VarArgs cfg2
  IS2 (Hssym: system_simulation pinfo S1 S2)
  (Hinit: Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2)),
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo (Mem.nextblock (Opsem.Mem IS1) - 1)
      (MemProps.inject_init (Mem.nextblock (Opsem.Mem IS1) - 1)) cfg1 IS1 cfg2 IS2 /\
    genericvalues_inject.wf_globals (Mem.nextblock (Opsem.Mem IS1) - 1) 
      (OpsemAux.Globals cfg1).
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
        admit. (* pld <> args *)
      fill_ctxhole. auto.

    simpl.
    apply MemProps.redundant__wf_globals; auto. 
    tauto.
Qed.

Lemma s_genInitState__dae_State_simulation: forall pinfo S1 S2 main VarArgs cfg2
  IS2 (Hssym: system_simulation pinfo S1 S2)
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

Ltac s_isFinialState__dae_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal := 
  destruct cfg2 as [S2 [los2 nts2] gl2 fs2];
  destruct cfg1 as [S1 [los1 nts1] gl1 fs1];
  destruct FS1 as [[|[? ? cs1 ? ?] ES1]]; 
  destruct FS2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
    auto |
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

Lemma s_isFinialState__dae_State_simulation_l2r: forall maxb mi pinfo cfg1 FS1 cfg2
  FS2 r 
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hwfcfg2: OpsemPP.wf_Config cfg2) (Hwfpp2: OpsemPP.wf_State cfg2 FS2) 
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hstsim : State_simulation pinfo maxb mi cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 = ret r),
  Opsem.s_isFinialState cfg2 FS2 = ret r.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__dae_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
  destruct Terminator0; auto.
    destruct ES1, ES2; try solve [auto | inv Hstsim'].
      simpl in Hfinal.
      inTmnOp_isnt_stuck value5 H6 Hwfcfg2 Hwfpp2.
      destruct H2 as [_ [_ H2]].
      assert (wf_value S2 (module_intro los2 nts2 gl2) CurFunction value5 typ5) as Hwft.
        admit. (* wf *)
      assert (value_doesnt_use_pid pinfo CurFunction value5) as Hnotin.
        destruct H5 as [l5 [ps2 [cs21 H5]]]; subst;
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as 
          [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]].
        eapply used_in_fdef__tmn_value_doesnt_use_pid; eauto 1; simpl; auto.
      eapply simulation__getOperandValue in H7; eauto.
      admit. (* main sig *)

    destruct ES1, ES2; try solve [auto | inv Hstsim'].
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
  forall pinfo cfg1 FS1 cfg2 FS2 r maxb mi 
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hstsim : State_simulation pinfo maxb mi cfg1 FS1 cfg2 FS2)
  (Hnrem: ~removable_State pinfo FS1) 
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r),
  Opsem.s_isFinialState cfg1 FS1 = ret r.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__dae_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
    destruct Terminator0; auto.
      destruct ES1, ES2; try solve [auto | inv Hstsim'].
        simpl in Hfinal.
        inTmnOp_isnt_stuck value5 H5 Hwfcfg1 Hwfpp1.
        destruct H2 as [_ [_ H2]].
        assert (wf_value S1 (module_intro los2 nts2 gl1) CurFunction value5 typ5) as Hwft.
          admit. (* wf *)
        assert (value_doesnt_use_pid pinfo CurFunction value5) as Hnotin.
          destruct H5 as [l5 [ps2 [cs21 H5]]]; subst;
          destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
          destruct Hwfpp1 as 
            [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]].
          eapply used_in_fdef__tmn_value_doesnt_use_pid; eauto 1; simpl; auto.
        eapply simulation__getOperandValue in H7; eauto.
        admit. (* main sig *)

      destruct ES1, ES2; try solve [auto | inv Hstsim'].

   apply not_removable_State_inv in Hnrem.
   apply cmds_simulation_nelim_cons_inv in Hstsim; auto. 
   destruct Hstsim as [cs2' [J1 Hstsim]]; congruence.
Qed.

Lemma removable_State__non_removable_State: forall pinfo f b c cs1 tmn lc als
  ES1 lc' als' Mem Mem' (Hnodup: NoDup (getCmdsLocs (c::cs1)))
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
  ~ removable_State pinfo
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f;
                        Opsem.CurBB := b;
                        Opsem.CurCmds := cs1;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc';
                        Opsem.Allocas := als' |} :: ES1;
           Opsem.Mem := Mem' |}.
Proof.
  simpl. intros.
  destruct_if; auto.
  destruct_if; auto.
  destruct cs1; auto.
  destruct_if; auto.
  inv Hnodup. inv H2. intro J. apply H1. simpl. left. congruence.
Qed.

Lemma s_isFinialState__dae_State_simulation_r2l:
  forall pinfo cfg1 FS1 cfg2 FS2 r maxb mi 
  (Hwfpi: WF_PhiInfo pinfo)
  (Hinbd: 0 <= maxb) (Halias: Promotability.wf_State maxb pinfo cfg1 FS1)
  (Hpalloca: palloca_props.wf_State pinfo FS1)
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))  
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hwfcfg2: OpsemPP.wf_Config cfg2) (Hwfpp2: OpsemPP.wf_State cfg2 FS2) 
  (Hstsim : State_simulation pinfo maxb mi cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r)
  (Hok: ~ sop_goeswrong cfg1 FS1),
  exists FS1', exists mi',
    Opsem.sop_star cfg1 FS1 FS1' E0 /\
    State_simulation pinfo maxb mi' cfg1 FS1' cfg2 FS2 /\
    Opsem.s_isFinialState cfg1 FS1' = ret r /\
    Values.inject_incr mi mi'.
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

    assert (G':=G). 
    apply dae_is_sim in G; auto.
    destruct G as [G _].
    remember 
            (Opsem.s_isFinialState {|           
              OpsemAux.CurSystem := S1;
              OpsemAux.CurTargetData := (los2, nts2);
              OpsemAux.CurProducts := gl1;
              OpsemAux.Globals := fs2;
              OpsemAux.FunTable := FunTable0 |}
              {|
              Opsem.ECS := {|
                           Opsem.CurFunction := CurFunction;
                           Opsem.CurBB := CurBB;
                           Opsem.CurCmds := c :: cs1;
                           Opsem.Terminator := Terminator0;
                           Opsem.Locals := Locals;
                           Opsem.Allocas := Allocas |} :: ES1;
              Opsem.Mem := Mem |}) as R.
    destruct R.
    SCase "isFinal".
      exists ({|
         Opsem.ECS := {|
                      Opsem.CurFunction := CurFunction;
                      Opsem.CurBB := CurBB;
                      Opsem.CurCmds := c :: cs1;
                      Opsem.Terminator := Terminator0;
                      Opsem.Locals := Locals;
                      Opsem.Allocas := Allocas |} :: ES1;
         Opsem.Mem := Mem |}). exists mi.
      split; auto.
      split.
        unfold State_simulation in G'. auto.
      split; auto.
        eapply s_isFinialState__dae_State_simulation_l2r in G'; eauto.
        uniq_result. auto.

    SCase "isntFinal".
    assert (J:=Hwfpp1).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]]; try congruence.
      SSCase "step".
      clear G'.
      assert (Hop1':=Hop1).
      apply_clear G in Hop1'; auto.
      destruct Hop1' as [mi' [J1 [J2 J3]]]; subst.
      assert (Hop1':=Hop1).
      apply OpsemPP.preservation in Hop1'; auto.     
      assert (J1':=J1).
      eapply s_isFinialState__dae_State_simulation_r2l' in J1; eauto.
        exists IS1'. exists mi'.
        split.
          apply OpsemProps.sInsn__implies__sop_star; auto.
        split.
          unfold State_simulation in J1'. auto.
        split; auto.

        assert (exists v,
          c = insn_alloca (PI_id pinfo) (PI_typ pinfo) v (PI_align pinfo)) as EQ.
          admit. (* uniqness *)
        destruct EQ as [v EQ]; subst.
        inv Hop1.
        eapply removable_State__non_removable_State; eauto.
          admit. (* uniqness *)

      SSCase "stuck".
      clear - Hundef1 Hok HeqR.
      apply undefined_state__stuck' in Hundef1.
      contradict Hok.
      exists {|Opsem.ECS := {|
                  Opsem.CurFunction := CurFunction;
                  Opsem.CurBB := CurBB;
                  Opsem.CurCmds := c :: cs1;
                  Opsem.Terminator := Terminator0;
                  Opsem.Locals := Locals;
                  Opsem.Allocas := Allocas |} :: ES1;
               Opsem.Mem := Mem |}.
      exists E0.
      split; auto.

Case "unremovable".
    assert (J:=Hstsim).
    eapply s_isFinialState__dae_State_simulation_r2l' in Hstsim; eauto.
    exists FS1. exists mi. 
    split; auto. 
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
  destruct_if; try tauto.
  simpl in H1.
  destruct ((id_dec (getCmdLoc c) (PI_id pinfo))); simpl in *; congruence.
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
  destruct cs; inv H1.
  destruct (id_dec (PI_id pinfo) (getCmdLoc c0)); try tauto.
  destruct (id_dec (getCmdLoc c0) (PI_id pinfo)); simpl in *; try congruence.
  inv H0. eauto.
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
      eapply cmds_simulation_cons_inv' in Hstsim; eauto; subst;
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
        eapply used_in_fdef__cmd_value_doesnt_use_pid; eauto using in_middle;
          simpl; auto |
        eapply wf_system__wf_fdef in HfInPs1; eauto;
        eapply wf_fdef__wf_cmd in HbInF1; eauto using in_middle;
        inv HbInF1; eauto 2
      ]
    ]
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
    destruct CurCmds0 as [|[]]; tinv HbInF1.
      simpl. admit. (*uniqness*)
    destruct CurCmds0 as [|[]]; tinv HbInF1.
      simpl. admit. (*uniqness*)
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
                            Opsem.Locals := Locals2;
                            Opsem.Allocas := Allocas2 |} :: ECS;
            Opsem.Mem := Mem0 |}).
      clear - Hwfpp1 H5.
      destruct H5 as [l5 [ps5 [cs5 H5]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto.
    eapply cmds_simulation_cons_inv' in Hnrem'; eauto.
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
    eapply cmds_simulation_nil_inv' in Hstsim; eauto; subst.
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
      clear - Hwfpp1 H5.
      destruct H5 as [l5 [ps5 [cs5 H5]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto.
    eapply cmds_simulation_cons_inv' in Hnrem'; eauto.
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
    eapply cmds_simulation_nil_inv' in Hstsim; eauto; subst.
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
    eapply cmds_simulation_cons_inv' in Hstsim; subst; eauto.
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
        eapply used_in_fdef__cmd_value_doesnt_use_pid; eauto 4 using in_middle;
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
          eapply used_in_fdef__params_dont_use_pid; eauto 1.
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

    assert (G':=G). 
    apply dae_is_sim in G; auto.
    destruct G as [G _].
    remember 
            (Opsem.s_isFinialState {|           
              OpsemAux.CurSystem := S1;
              OpsemAux.CurTargetData := (los2, nts2);
              OpsemAux.CurProducts := gl1;
              OpsemAux.Globals := fs2;
              OpsemAux.FunTable := FunTable0 |}
              {|
              Opsem.ECS := {|
                           Opsem.CurFunction := CurFunction;
                           Opsem.CurBB := CurBB;
                           Opsem.CurCmds := c :: cs1;
                           Opsem.Terminator := Terminator0;
                           Opsem.Locals := Locals;
                           Opsem.Allocas := Allocas |} :: ES1;
              Opsem.Mem := Mem |}) as R.
    destruct R.
    SCase "isFinal".
      simpl in HeqR. congruence.

    SCase "isntFinal".
    assert (J:=Hwfpp1).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]]; try congruence.
      SSCase "step".
      clear G'.
      assert (Hop1':=Hop1).
      apply_clear G in Hop1'; auto.
      destruct Hop1' as [mi' [J1 [J2 J3]]]; subst.
      assert (Hop1':=Hop1).
      apply OpsemPP.preservation in Hop1'; auto.     
      assert (Hop1'':=Hop1).
      eapply Promotability.preservation in Hop1''; eauto.
      assert (Hop1''':=Hop1).
      eapply palloca_props.preservation in Hop1'''; eauto.
      assert (J1':=J1).
      eapply undefined_state__dae_State_simulation_r2l' in J1; eauto.
        exists IS1'. exists mi'.
        split.
          apply OpsemProps.sInsn__implies__sop_star; auto.
        split.
          unfold State_simulation in J1'. auto.
        split; auto.

        assert (exists v,
          c = insn_alloca (PI_id pinfo) (PI_typ pinfo) v (PI_align pinfo)) as EQ.
          admit. (* uniqness *)
        destruct EQ as [v EQ]; subst.
        inv Hop1.
        eapply removable_State__non_removable_State; eauto.
          admit. (* uniqness *)
 
      SSCase "stuck".
      clear - Hundef1 Hok HeqR.
      apply undefined_state__stuck' in Hundef1.
      contradict Hok.
      exists {|Opsem.ECS := {|
                  Opsem.CurFunction := CurFunction;
                  Opsem.CurBB := CurBB;
                  Opsem.CurCmds := c :: cs1;
                  Opsem.Terminator := Terminator0;
                  Opsem.Locals := Locals;
                  Opsem.Allocas := Allocas |} :: ES1;
               Opsem.Mem := Mem |}.
      exists E0.
      split; auto.

Case "unremovable".
    assert (J:=Hstsim).
    eapply undefined_state__dae_State_simulation_r2l' in Hstsim; eauto.
    exists St1. exists mi. 
    split; auto. 
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

    assert (forall (Hfinal1: Opsem.s_isFinialState cfg1 IS1 <> merror),
            exists FS1 : Opsem.State, exists mi',
              Opsem.sop_star cfg1 IS1 FS1 (tr1 ** tr2) /\
              State_simulation pinfo maxb mi' cfg1 FS1 cfg2 state3 /\
              inject_incr mi mi') as W.
      intros.
      apply s_isFinialState__dae_State_simulation_l2r' in Hstsim; auto.
      contradict H; eauto using s_isFinialState__stuck.
    assert (J:=Hwfpp1).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]]; auto.
      assert (OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
        apply OpsemPP.preservation in Hop1; auto.
      assert (Promotability.wf_State maxb pinfo cfg1 IS1') as Hnoalias'.
        eapply Promotability.preservation in Hop1; eauto.
      assert (palloca_props.wf_State pinfo IS1') as Hpalloca'.
        eapply palloca_props.preservation in Hop1; eauto.
      eapply dae_is_sim in Hstsim; eauto; try tauto.
      destruct Hstsim as [Hstsim1 Hstsim2].
      destruct (@removable_State_dec pinfo IS1) as [Hrm | Hnrm].
        eapply Hstsim1 in Hrm; eauto.
        destruct Hrm as [Hstsim EQ]; subst.
        admit. (* we should do induction on the measure of State_simulation *)

        eapply Hstsim2 in Hnrm; eauto.
        destruct Hnrm as [mi' [Hstsim [EQ Hinc]]]; subst.
        eapply IHHopstar in Hstsim;
          eauto using sop_goeswrong__step, (@OpsemPP.preservation DGVs).
        destruct Hstsim as [FS1 [mi'' [Hopstar1 [Hstsim Hinc']]]].
        exists FS1. exists mi''.
        split; eauto.
        split; eauto.
          eapply inject_incr_trans; eauto.

      apply undefined_state__stuck' in Hundef1.
      remember (Opsem.s_isFinialState cfg1 IS1) as R.
      destruct R.
        apply W; congruence.
        contradict Hok. exists IS1. exists E0. split; auto.
Qed.

Lemma sop_div__dae_State_simulation: forall pinfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) maxb mi
  (Hwfg: genericvalues_inject.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hless: 0 <= maxb) (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfgs: MemProps.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hstsim : State_simulation pinfo maxb mi cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Admitted. (* sop div *)

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
    destruct Hstsim' as [FS1' [mi'' [Hopstar1' [Hstsim'' [Hfinal Hinc']]]]].
    assert (Opsem.sop_star cfg1 IS1 FS1' tr) as Hopstar1''.
      rewrite <- E0_right.
      eapply OpsemProps.sop_star_trans; eauto.
    econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    dae_sim_init.
    eapply sop_div__dae_State_simulation in Hstsim; try solve [eauto | tauto].
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
    exists (tr**E0). exists FS1'.
    econstructor; eauto using (@OpsemProps.sop_star_trans DGVs).   
Qed.
