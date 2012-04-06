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
Require Import mem2reg.
Require Import program_sim.
Require Import trans_tactic.
Require Import sas_msim.
Require Import memory_sim.
Require Import top_sim.
Require Import sas.
Require Import sas_wfS.

Lemma s_genInitState__sas_State_simulation: forall pinfo sasinfo S1 S2 main
  VarArgs cfg2 IS2 (Hssim: system_simulation pinfo sasinfo S1 S2)
  (Hwfpi: WF_PhiInfo pinfo) (HwfS1: wf_system S1)
  (Hinit: Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2)),
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo sasinfo cfg1 IS1 cfg2 IS2.
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
  apply block_simulation_inv in J; 
    eauto using entryBlockInFdef, wf_system__uniqFdef.
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

    unfold sas_mem_inj. 
    assert (exists tsz, getTypeStoreSize (OpsemAux.initTargetData los nts Mem.empty)
             (PI_typ pinfo) = Some tsz) as Htsz.
      admit. (* When dse runs PI_f must be in the system, see mem2reg_correct *)
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
    apply cmds_simulation_nil_inv in Hstsim; try congruence |
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

Lemma not_removable_State_inv: forall pinfo sasinfo St,
  ~ removable_State pinfo sasinfo St ->
  match St with
  | {| Opsem.ECS := {| Opsem.CurFunction := F;
                       Opsem.CurBB := _;
                       Opsem.CurCmds := c :: _;
                       Opsem.Terminator := _;
                       Opsem.Locals := _;
                       Opsem.Allocas := _ |} :: _;
       Opsem.Mem := Mem |} => 
       PI_f pinfo <> F \/ 
       match c with
       | insn_store sid _ _ _ _ => sid <> SAS_sid1 pinfo sasinfo
       | _ => True
       end
  | _ => True
  end.
Proof.
  intros.
  destruct St; auto.
  destruct ECS; auto.
  destruct e; auto.
  destruct CurCmds; auto.
  destruct c; auto.
  simpl in H.
  destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
  destruct (id_dec i0 (SAS_sid1 pinfo sasinfo)); subst; auto.
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

   apply not_removable_State_inv in Hnrem.
   apply cmds_simulation_nelim_cons_inv in Hstsim; auto. 
     destruct Hstsim as [cs2' [J1 Hstsim]]; congruence.
     admit. (* removable_State may check if getCmdLoc <> sid1 directly,
               otherwise, we need uniqness
               The current removable_State only checks id when c is store, 
               but cmds_simulation_nelim_cons_inv uses getCmdLoc,
               Changing the definition may simplify proofs.
               Refer to dae's removable_State *)
Qed.

Lemma removable_State__non_removable_State: forall pinfo sasinfo f b c cs1 tmn lc
  als ES1 lc' als' Mem Mem' (Hnodup: NoDup (getCmdsLocs (c::cs1)))
  (Hrem : removable_State pinfo sasinfo 
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f;
                        Opsem.CurBB := b;
                        Opsem.CurCmds := c :: cs1;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: ES1;
           Opsem.Mem := Mem |}),
  ~ removable_State pinfo sasinfo 
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
  destruct c; try tauto.
  destruct_if; auto.
  destruct_if; auto.
  destruct cs1; auto.
  destruct c; auto.
  destruct_if; auto.
  inv Hnodup. inv H2. intro J. apply H1. simpl. left. congruence.
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
  destruct (removable_State_dec pinfo sasinfo FS1) as [Hrem | Hnrem].
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
    eapply sas_is_sim in G; eauto.
    destruct G as [G _].
    remember 
            (Opsem.s_isFinialState {|           
              OpsemAux.CurSystem := S1;
              OpsemAux.CurTargetData := (los2, nts2);
              OpsemAux.CurProducts := gl1;
              OpsemAux.Globals := fs2;
              OpsemAux.FunTable := FunTable |}
              {|
              Opsem.ECS := {|
                           Opsem.CurFunction := CurFunction;
                           Opsem.CurBB := CurBB;
                           Opsem.CurCmds := c :: cs1;
                           Opsem.Terminator := Terminator0;
                           Opsem.Locals := Locals0;
                           Opsem.Allocas := Allocas0 |} :: ES1;
              Opsem.Mem := Mem |}) as R.
    destruct R.
    SCase "isFinal".
      exists ({|
         Opsem.ECS := {|
                      Opsem.CurFunction := CurFunction;
                      Opsem.CurBB := CurBB;
                      Opsem.CurCmds := c :: cs1;
                      Opsem.Terminator := Terminator0;
                      Opsem.Locals := Locals0;
                      Opsem.Allocas := Allocas0 |} :: ES1;
         Opsem.Mem := Mem |}). 
      split; auto.
      split.
        unfold State_simulation in G'. auto.
        eapply s_isFinialState__sas_State_simulation_l2r in G'; eauto.
        uniq_result. auto.

    SCase "isntFinal".
    assert (J:=Hwfpp1).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]]; try congruence.
      SSCase "step".
      clear G'.
      assert (Hop1':=Hop1).
      apply_clear G in Hop1'; auto.
      destruct Hop1' as [J1 J2]; subst.
      assert (Hop1':=Hop1).
      apply OpsemPP.preservation in Hop1'; auto.     
      assert (J1':=J1).
      eapply s_isFinialState__sas_State_simulation_r2l' in J1; eauto.
        exists IS1'.
        split.
          apply OpsemProps.sInsn__implies__sop_star; auto.
        split.
          unfold State_simulation in J1'. auto.
          auto.

        assert (
          c = insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
                (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) 
                (PI_align pinfo)) as EQ.
          admit. (* uniqness *)
        subst.
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
                  Opsem.Locals := Locals0;
                  Opsem.Allocas := Allocas0 |} :: ES1;
               Opsem.Mem := Mem |}.
      exists E0.
      split; auto.

Case "unremovable".
    assert (J:=Hstsim).
    eapply s_isFinialState__sas_State_simulation_r2l' in Hstsim; eauto.
Qed.

Lemma cmds_simulation_nil_inv' : forall (pinfo : PhiInfo) sasinfo
  (f1 : fdef) (cs1 : list cmd) b1 tmn1 lc1 als1 ECS Mem1
  (Hnrem : ~
          removable_State pinfo sasinfo
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := f1;
                         Opsem.CurBB := b1;
                         Opsem.CurCmds := cs1;
                         Opsem.Terminator := tmn1;
                         Opsem.Locals := lc1;
                         Opsem.Allocas := als1 |} :: ECS;
            Opsem.Mem := Mem1 |}),
  cmds_simulation pinfo sasinfo f1 cs1 nil -> cs1 = nil.
Proof.
  simpl.
  unfold cmds_simulation. intros.
  destruct_if; auto.
  destruct cs1; auto.
  simpl in *.
  admit. (* see the comments in s_isFinialState__sas_State_simulation_r2l' *)
Qed.

Lemma cmds_simulation_cons_inv' : forall (pinfo : PhiInfo) sasinfo
  (f1 : fdef) b1 lc1 cs tmn1 als1 c cs2 ECS Mem1
  (Hnrem : ~
          removable_State pinfo sasinfo
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := f1;
                         Opsem.CurBB := b1;
                         Opsem.CurCmds := cs;
                         Opsem.Terminator := tmn1;
                         Opsem.Locals := lc1;
                         Opsem.Allocas := als1 |} :: ECS;
            Opsem.Mem := Mem1 |}),
  cmds_simulation pinfo sasinfo f1 cs (c::cs2) -> 
   exists cs1, 
     cs = c::cs1 /\
     cmds_simulation pinfo sasinfo f1 cs1 cs2.
Proof.
  simpl.
  unfold cmds_simulation. intros.
  destruct_if; eauto.
  destruct cs; tinv H1.
  simpl in *.
  admit. (* see the comments in s_isFinialState__sas_State_simulation_r2l' *)
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
    destruct Hstsim as [? [Htmn [? [? [H8 [? [? Hstsim]]]]]]]; subst;
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
      eapply cmds_simulation_cons_inv' in Hstsim; eauto; subst;
      destruct Hstsim as [c1' [J2 J3]]; subst
     end.

Lemma stacked_frame__unremovable: forall cfg EC1 EC2 ECS Mem0 pinfo sasinfo
  (HBinF: match Opsem.CurBB EC1 with 
   | block_intro _ _ _ (insn_return _ _ _) => True
   | block_intro _ _ _ (insn_return_void _) => True
   | _ => False
   end)
  (Hwfpp1 : OpsemPP.wf_State cfg
             {| Opsem.ECS := EC1 :: EC2 :: ECS; Opsem.Mem := Mem0 |}),
  ~ removable_State pinfo sasinfo
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

Lemma mem_simulation__malloc_l2r': forall (pinfo : PhiInfo) sasinfo TD ECs M1 M2
  (Hmsim : mem_simulation pinfo sasinfo TD ECs M1 M2)
  (Mem'0 : mem) (tsz0 : sz) align0 gn mb M1'
  (H2 : malloc TD M1 tsz0 gn align0 = ret (M1', mb)),
  exists M2',
     malloc TD M2 tsz0 gn align0 = ret (M2', mb).
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmim3 Hmsim2]].
  unfold sas_mem_inj in *.
  inv_mbind. 
  destruct (@in_SAS_tails_ex pinfo sasinfo TD ECs) as [ombs J].
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
  (H1 : mload td M1 mp t align0 = ret gv) sasinfo
  (Hmsim : mem_simulation pinfo sasinfo td ECs M1 M2),
  exists gv0, mload td M2 mp t align0 = ret gv0.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  apply mload_inv in H1.
  destruct H1 as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold sas_mem_inj in Hmsim2.
  inv_mbind. 
  destruct (@in_SAS_tails_ex pinfo sasinfo td ECs) as [ombs J].
  apply_clear Hmsim2 in J.
  unfold mload. repeat fill_ctxhole. simpl.
  eapply SASmsim.mload_aux_inj_ex with (b2:=b)(delta:=0) in J; eauto.
  replace (Int.signed 31 ofs + 0) with (Int.signed 31 ofs)  in J by omega.
  destruct J as [gv2 J]; eauto.
Qed.

Lemma mem_simulation__mstore_l2r: forall td M1 mp2 t gv1 align0 M1' M2 ECs
  (H3 : mstore td M1 mp2 t gv1 align0 = ret M1') pinfo sasinfo
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
  destruct (@in_SAS_tails_ex pinfo sasinfo td ECs) as [ombs J].
  apply_clear Hmsim2 in J.
  unfold mstore. simpl. 
  eapply SASmsim.mstore_aux_inject_id_mapped_inj in J; eauto.
  destruct J as [gv2 [J1 J4]]; eauto.
Qed.

Lemma mem_simulation__free_allocas_l2r : forall TD ECs1 pinfo sasinfo EC EC'
  (Hp: forall omb,
       in_SAS_tail pinfo sasinfo omb TD EC' ->
       in_SAS_tail pinfo sasinfo omb TD EC)
  als Mem1 Mem2 Mem1'
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
  (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (Hstsim : State_simulation pinfo sasinfo cfg1 St1 cfg2 St2)
  (Hnrem: ~removable_State pinfo sasinfo St1) 
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
      remember (malloc (los2, nts2) Mem0 s gn a) as R;
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
    remember (mload (los2, nts2) Mem0 gvs t a) as R.
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
    remember (mstore (los2, nts2) Mem0 mgv t gv a) as R.
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
      remember (callExternalOrIntrinsics (los2, nts2) fs2 Mem0 i1 t0 
          (args2Typs a) d l1) as R.
      destruct R as [[[]]|]; auto.
      remember (Opsem.exCallUpdateLocals (los2, nts2) t n i0 o Locals) as R.
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
  destruct (removable_State_dec pinfo sasinfo St1) as [Hrem | Hnrem].
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
    eapply sas_is_sim in G; eauto.
    destruct G as [G _].
    remember 
            (Opsem.s_isFinialState {|           
              OpsemAux.CurSystem := S1;
              OpsemAux.CurTargetData := (los2, nts2);
              OpsemAux.CurProducts := gl1;
              OpsemAux.Globals := fs2;
              OpsemAux.FunTable := FunTable |}
              {|
              Opsem.ECS := {|
                           Opsem.CurFunction := CurFunction;
                           Opsem.CurBB := CurBB;
                           Opsem.CurCmds := c :: cs1;
                           Opsem.Terminator := Terminator0;
                           Opsem.Locals := Locals0;
                           Opsem.Allocas := Allocas0 |} :: ES1;
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
      destruct Hop1' as [J1 J2]; subst.
      assert (Hop1':=Hop1).
      apply OpsemPP.preservation in Hop1'; auto.     
      assert (Hop1'':=Hop1).
      eapply Promotability.preservation in Hop1''; eauto.
      assert (Hop1''':=Hop1).
      eapply palloca_props.preservation in Hop1'''; eauto.
      assert (J1':=J1).
      eapply undefined_state__sas_State_simulation_r2l' in J1; eauto.
        exists IS1'.
        split.
          apply OpsemProps.sInsn__implies__sop_star; auto.
        split; auto.
          unfold State_simulation in J1'. auto.

        assert (
          c = insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
                (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) 
                (PI_align pinfo)) as EQ.
          admit. (* uniqness *)
        subst.
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
                  Opsem.Locals := Locals0;
                  Opsem.Allocas := Allocas0 |} :: ES1;
               Opsem.Mem := Mem |}.
      exists E0.
      split; auto.

Case "unremovable".
    assert (J:=Hstsim).
    eapply undefined_state__sas_State_simulation_r2l' in Hstsim; eauto.
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

    assert (forall (Hfinal1: Opsem.s_isFinialState cfg1 IS1 <> merror),
            exists FS1 : Opsem.State,
              Opsem.sop_star cfg1 IS1 FS1 (tr1 ** tr2) /\
              State_simulation pinfo sasinfo cfg1 FS1 cfg2 state3) as W.
      intros.
      apply s_isFinialState__sas_State_simulation_l2r' in Hstsim; auto.
      contradict H; eauto using s_isFinialState__stuck.
    assert (J:=Hwfpp).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]]; auto.
      assert (OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
        apply OpsemPP.preservation in Hop1; auto.
      assert (Promotability.wf_State maxb pinfo cfg1 IS1') as Hnoalias'.
        eapply Promotability.preservation in Hop1; eauto; try tauto.
      assert (palloca_props.wf_State pinfo IS1') as Hpalloca'.
        eapply palloca_props.preservation in Hop1; eauto.
      eapply sas_is_sim in Hstsim; eauto.
      destruct Hstsim as [Hstsim1 Hstsim2].
      destruct (@removable_State_dec pinfo sasinfo IS1) as [Hrm | Hnrm].
        eapply Hstsim1 in Hrm; eauto.
        destruct Hrm as [Hstsim EQ]; subst.
        admit. (* we should do induction on the measure of State_simulation *)

        eapply Hstsim2 in Hnrm; eauto.
        destruct Hnrm as [Hstsim EQ]; subst.
        eapply IHHopstar in Hstsim;
          eauto using sop_goeswrong__step, (@OpsemPP.preservation DGVs).
        destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
        exists FS1.
        split; eauto.

      apply undefined_state__stuck' in Hundef1.
      remember (Opsem.s_isFinialState cfg1 IS1) as R.
      destruct R.
        apply W; congruence.
        contradict Hok. exists IS1. exists E0. split; auto.
Qed.

Lemma sop_div__sas_State_simulation: forall pinfo laainfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hstsim : State_simulation pinfo laainfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Admitted. (* sop div *)

Lemma find_st_ld__sasinfo: forall l0 ps0 cs0 tmn0 i0 v cs (pinfo:PhiInfo) dones
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones) v0
  (i1 : id) (Hld : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (HBinF : blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true),
  exists sasinfo:SASInfo pinfo,
    SAS_sid1 pinfo sasinfo = i0 /\
    SAS_sid2 pinfo sasinfo = i1 /\
    SAS_value1 pinfo sasinfo = v /\
    SAS_value2 pinfo sasinfo = v0 /\
    SAS_block pinfo sasinfo = (block_intro l0 ps0 cs0 tmn0).
Admitted. (* sasinfo *)

Lemma sas_sim: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds)
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  S2 (Heq2: S2 = [module_intro los nts
                   (Ps1 ++
                     product_fdef
                     (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)])
  (Hok: defined_program S2 main VarArgs)
  (HwfS : wf_system S2),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
           (List.map (remove_block i0)
             (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) :: Ps2)]
    S2 main VarArgs.
Proof.
  intros.
  assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true)
    as HBinF.
    rewrite Heq. simpl. apply InBlocksB_middle.
  eapply find_st_ld__sasinfo in HBinF; eauto.
  destruct HBinF as [sasinfo [J1 [J2 [J3 [J4 J5]]]]]; subst.
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation pinfo sasinfo
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (remove_fdef (SAS_sid1 pinfo sasinfo)
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))
         :: Ps2)]) as Hssim.
    constructor; auto.
    repeat split; auto.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    unfold TopSim.products_simulation. unfold fsim. unfold Fsim.
    apply uniq_products_simulation; auto.

Ltac sas_sim_init :=
match goal with
| H: Opsem.s_genInitState [module_intro ?los ?nts _] _ _ _ = Some (?cfg, ?IS), 
  pinfo: PhiInfo |- _ =>
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg IS) as Hwfst';
      try solve [eapply s_genInitState__opsem_wf in H; eauto using sas_wfS];
    eapply s_genInitState__sas_State_simulation in H; eauto;
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]];
    assert (OpsemPP.wf_Config cfg1 /\ OpsemPP.wf_State cfg1 IS1) as Hwfst;
      try solve [eapply s_genInitState__opsem_wf; eauto];
    assert (exists maxb,
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom;
      try solve [eapply Promotability.s_genInitState__wf_globals_promotable; eauto];
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]];
    assert (palloca_props.wf_State pinfo IS1) as Hpalloca;
      try solve [eapply palloca_props.s_genInitState__palloca; eauto]
end.

Ltac sas_sim_end :=
match goal with
| Hstsim' : State_simulation ?pinfo _ ?cfg1 ?FS1 ?cfg ?FS,
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
    sas_sim_init.
    eapply sop_star__sas_State_simulation in Hstsim; 
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    sas_sim_end.
    eapply s_isFinialState__sas_State_simulation_r2l in Hstsim';
      eauto using sop_goeswrong__star, defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim' as [FS1' [Hopstar1' [Hstsim'' Hfinal]]].
    assert (Opsem.sop_star cfg1 IS1 FS1' tr) as Hopstar1''.
      rewrite <- E0_right.
      eapply OpsemProps.sop_star_trans; eauto.
    econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    sas_sim_init.
    eapply sop_div__sas_State_simulation in Hstsim; eauto; try tauto.
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.

    intros tr t Hgowrong.
    inv Hgowrong.
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg t) as HwfSt.
      eapply s_genInitState__opsem_wf in H; eauto using sas_wfS.
      destruct H as [Hcfg2 HwfSt2].
      apply OpsemPP.preservation_star in H0; auto.
    assert (OpsemPP.undefined_state cfg t) as Hundef.
      apply stuck__undefined_state in H2; try solve [auto | tauto].
    sas_sim_init.
    eapply sop_star__sas_State_simulation in Hstsim;
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    sas_sim_end.
    assert (Hundef':=Hundef).
    eapply undefined_state__sas_State_simulation_r2l in Hundef'; 
      try solve [eauto using sop_goeswrong__star, defined_program__doesnt__go_wrong | tauto].
    destruct Hundef' as [FS1' [Hopstar2 [Hsim Hundef']]].
    assert (Opsem.s_isFinialState cfg1 FS1' = merror) as Hfinal'.
      apply OpsemPP.preservation_star in Hopstar2; auto; try tauto.
      eapply s_isFinialState__sas_State_simulation_None_r2l in H2; 
        try solve [eauto | tauto].
    apply undefined_state__stuck' in Hundef'.
    exists (tr**E0). exists FS1'.
    econstructor; eauto using (@OpsemProps.sop_star_trans DGVs).   
Qed.

