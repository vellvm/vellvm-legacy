Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import primitives.
Require Import mem2reg.
Require Import opsem_props.
Require Import promotable_props.
Require Import palloca_props.
Require Import program_sim.
Require Import memory_props.
Require Import trans_tactic.
Require Import top_sim.
Require Import phiplacement_bsim_defs.
Require Import phiplacement_bsim.
Require Import phiplacement_bsim_wfS.

Import Promotability.

Lemma s_genInitState__phiplacement_State_simulation: 
  forall pinfo S1 S2 main VarArgs cfg2 IS2
  (Hwfs1: wf_system S1) (Hwfphi: WF_PhiInfo pinfo)
  (Hssim: system_simulation pinfo S1 S2)
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
  apply block_simulation__inv in J.
  destruct J; subst.
  assert (blockInFdefB (block_intro l0 ps2 cs2 tmn0)
           (fdef_intro (fheader_intro fa rt fid la va) bs1) = true) as HBinF.
    apply entryBlockInFdef; auto.
  repeat (split; auto).
    exists l0. exists ps2. exists nil. auto.
    exists l0. exists ps0. exists nil. auto.
    apply reg_simulation_refl.
    eapply entry_cmds_simulation; eauto using 
      wf_system__wf_fdef, wf_system__uniqFdef.
Qed.

Lemma s_isFinialState__phiplacement_State_simulation_r2l:
  forall pinfo cfg1 FS1 cfg2 FS2 r
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r),
  Opsem.s_isFinialState cfg1 FS1 = ret r.
Proof.
  destruct cfg1, cfg2, FS1, FS2.
  destruct CurTargetData as [los nts].
  simpl. intros.
  destruct ECS0 as [|[]]; tinv Hfinal.
  destruct Hstsim as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 J9]]]]]]]]; subst.
  destruct ECS as [|[]]; tinv J6.
  destruct J6 as [J61 J62].
  destruct CurCmds; tinv Hfinal. 
  unfold EC_simulation_head in J61.
  destruct J61 as [G1 [G2 [G3 [G4 [G5 [G6 [
                    [? [? [? G7]]] [
                    [? [? [? G8]]] [G9 G10]]]]]]]]]; subst.
  apply cmds_simulation_nil_inv in G10. subst.
  assert (HwfF := J1).
  eapply wf_system__wf_fdef with (f:=CurFunction0) in HwfF; eauto.
  destruct Terminator; tinv Hfinal; 
    destruct ECS0; tinv Hfinal; destruct ECS; tinv J62.

    erewrite simulation__getOperandValue with (lc2:=Locals); eauto;
      match goal with
      | _:blockInFdefB (block_intro ?l0 ?ps ?cs ?tmn) _ = _ |- _ =>
        eapply original_values_arent_tmps with 
          (instr:=insn_terminator tmn)
          (B:=block_intro l0 ps cs tmn); eauto;
          try solve [
            simpl; apply andb_true_iff;
            split; try solve [auto | apply terminatorEqB_refl] |
            simpl; auto
          ]
      end.

    assumption.
Qed.

Lemma simulation__lookup_pid: forall pinfo Locals Locals0
  (Huniq : uniqFdef (PI_f pinfo)) (Hwfpi : WF_PhiInfo pinfo)
  (Hsim: reg_simulation pinfo (PI_f pinfo) Locals Locals0),
  lookupAL _ Locals (PI_id pinfo) = lookupAL _ Locals0 (PI_id pinfo).
Proof.
  intros.
  eapply simulation__lookupAL; eauto.
    destruct_if; try congruence.
    eapply WF_PhiInfo_spec18; auto.
Qed.

Lemma cmds_simulation_nil_inv': forall pinfo TD Mem0 Locals0 F l1 ps1
  cs1 tmn1 cs
  (Hsim: cmds_simulation pinfo TD Mem0 Locals0 F
           (block_intro l1 ps1 cs1 tmn1) nil cs),
  if (fdef_dec (PI_f pinfo) F) then
    forall c (Hin: In c cs),
      exists i1, exists i2, exists i3, 
      ret (i1, i2, i3) = (PI_newids pinfo) ! l1 /\
      (c = insn_store i3 (PI_typ pinfo) (value_id i2)
              (value_id (PI_id pinfo)) (PI_align pinfo) \/
       c = insn_load i1 (PI_typ pinfo) (value_id (PI_id pinfo))
              (PI_align pinfo))
  else cs = nil.
Proof.
  intros.
  unfold cmds_simulation in Hsim.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  intros.
  remember ((PI_newids pinfo) ! l1) as R.
  destruct R as [[[i1 i2] i3]|]; subst; tinv Hin.
  exists i1. exists i2. exists i3.
  split; auto.
  destruct Hsim as [J1 [J2 _]].
  remember ((PI_preds pinfo) ! l1) as R1.
  remember ((PI_succs pinfo) ! l1) as R2.

Ltac cmds_simulation_nil_inv'_tac :=
match goal with
| Hin: In _ ?cs, HeqR2 : ?R2 = (PI_succs _) ! _ |- _ =>
  destruct R2 as [[]|]; tinv Hin; simpl in Hin; 
     destruct Hin as [Hin | Hin]; auto; try tauto;
     try solve [destruct Hin as [Hin | Hin]; auto; try tauto]
end.

  destruct (list_eq_dec cmd_dec cs1 nil) as [e | n].
    clear J2. apply_clear J1 in e. 
    destruct e as [e _].

    destruct e as [e | [[_ e] | [_ [_ e]]]]; subst cs.
      destruct R1 as [[]|]; cmds_simulation_nil_inv'_tac.
      cmds_simulation_nil_inv'_tac.
      inv Hin.
    
    clear J1. apply_clear J2 in n.  
    destruct n as [J3 | [J3 [J4 J5]]]; subst cs; tinv Hin.
    cmds_simulation_nil_inv'_tac.
Qed.

Lemma block_sim__pres__blockInFdefB: forall pinfo f1 f2 b1 b2
  (Hwfpi: WF_PhiInfo pinfo) (Hfsim: fdef_simulation pinfo f1 f2)
  (Hbsim: block_simulation pinfo f1 b1 b2) (HBinF: blockInFdefB b1 f1),
  blockInFdefB b2 f2.
Proof.
  unfold fdef_simulation, block_simulation.
  destruct f1 as [f b], f2. simpl.
  intros. 
  destruct (fdef_dec (PI_f pinfo) (fdef_intro f b)); subst.
    destruct f as [f t i0 a v]. 
    remember (gen_fresh_ids (PI_rd pinfo) (getArgsIDs a ++ getBlocksLocs b)) 
      as R.
    destruct R. 
    inv Hfsim.
    unfold phinodes_placement_blocks, PI_newids, getFdefLocs.
    rewrite e. rewrite <- HeqR.
    apply InBlocksB_map; auto.

    inv Hfsim. auto.
Qed.

Lemma s_isFinialState__phiplacement_State_simulation_None_r2l:
  forall pinfo cfg1 FS1 cfg2 FS2 maxb
  (Hwfpi: WF_PhiInfo pinfo) (Hundef: @OpsemPP.undefined_state DGVs cfg2 FS2)
  (Hpp: @OpsemPP.wf_State DGVs cfg2 FS2) (Hcfg: OpsemPP.wf_Config cfg2)
  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 FS1)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = None),
  Opsem.s_isFinialState cfg1 FS1 = None.
Proof.
  destruct cfg1, cfg2, FS1, FS2.
  destruct CurTargetData as [los nts].
  simpl. intros.
  destruct Hstsim as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 J9]]]]]]]]; subst.
  destruct ECS as [|[]]; tinv J6; auto.
  destruct ECS0 as [|[]]; tinv J6.
  destruct J6 as [J61 J62].
  destruct CurCmds; auto.
  unfold EC_simulation_head in J61.
  destruct J61 as [G1 [G2 [G3 [G4 [G5 [G6 [
                    [? [? [? G7]]] [
                    [? [? [? G8]]] [G9 G10]]]]]]]]]; subst.
  destruct CurCmds0.
    assert (HwfF := J1).
    eapply wf_system__wf_fdef with (f:=CurFunction) in HwfF; eauto.
    destruct Terminator0; try solve [
      auto |
      destruct ECS; auto;
      destruct ECS0; tinv J62; try solve [
        auto |
        erewrite simulation__getOperandValue with (lc2:=Locals0); eauto;
        match goal with
        | _:blockInFdefB (block_intro ?l0 ?ps ?cs ?tmn) _ = _ |- _ =>
          eapply original_values_arent_tmps with 
            (instr:=insn_terminator tmn)
            (B:=block_intro l0 ps cs tmn); eauto;
            try solve [
              simpl; apply andb_true_iff;
              split; try solve [auto | apply terminatorEqB_refl] |
              simpl; auto
          ]
        end
      ]
   ].

  destruct Hnoalias as [Hnoalias _].
  simpl in Hnoalias. destruct Hnoalias as [[Hnoalias _] _].
  apply cmds_simulation_nil_inv' in G10.
  destruct_if; try congruence.
  assert (Huniq: uniqFdef (PI_f pinfo)). 
    rewrite e. eauto using wf_system__uniqFdef.
   
Ltac s_isFinialState__phiplacement_State_simulation'_tac :=
repeat match goal with
| Hundef: _ \/ _ |- _ => destruct Hundef as [Hundef | Hundef]; try tauto
| Hundef: match ?Terminator0 with
          | insn_return _ _ _ => False
          | insn_return_void _ => False
          | insn_br _ _ _ _ => False
          | insn_br_uncond _ _ => False
          | insn_unreachable _ => False
          end |- _ => 
   destruct Terminator0; try tauto
| Hundef: match _ with
          | Some _ => _
          | None => _
          end |- _ =>
  inv_mbind;
  try (destruct Hundef as [gv1 [gv2 [J13 [J14 J15]]]]; inv J13; inv J14);
  try (destruct Hundef as [gv [J13 J14]]; inv J13);
  inv_mbind;
  elimtype False; try solve [
    eapply WF_PhiInfo_spec190; 
      try solve [eauto | erewrite simulation__lookup_pid; eauto]
  ]
end.

  destruct (@G10 c) as [i1 [i2 [i3 [J11 [J12 | J12]]]]]; subst; simpl; auto.
    s_isFinialState__phiplacement_State_simulation'_tac.
      eapply WF_PhiInfo_spec200; 
        try solve [eauto using wf_system__wf_fdef | 
                   erewrite simulation__lookup_pid; eauto].

      destruct Hpp as [_ [Hpp _]].
      simpl in Hpp.
      destruct Hpp as [_ [W1 [W2 [Hwflc _]]]].
      destruct Hcfg as [_ [Hwfg [Hwfs W3]]].
      symmetry in HeqR0.
      eapply OpsemPP.getOperandValue__wf_gvs with (t:=PI_typ pinfo)
        (ps:=CurProducts0) in HeqR0; eauto.
        inv HeqR0. apply H2. auto.
        eapply block_sim__pres__blockInFdefB in G6; eauto.
        eapply wf_system__wf_fdef in W2; eauto.
        eapply wf_fdef__wf_cmd in G6; eauto using in_middle.
        inv G6; auto.

    s_isFinialState__phiplacement_State_simulation'_tac.
Qed.

Section TOPSIM.

Variables (pinfo:PhiInfo) (cfg1:OpsemAux.Config) (IS1:@Opsem.State DGVs) 
          (cfg2:OpsemAux.Config) (IS2:@Opsem.State DGVs) 
          (maxb:Values.block).

Hypothesis (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfcfg: OpsemPP.wf_Config cfg1) (Hwfpp: OpsemPP.wf_State cfg1 IS1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hinbd: 0 <= maxb)
  (Hstsim : State_simulation pinfo cfg1 IS1 cfg2 IS2).

Lemma sop_star__phiplacement_State_simulation: 
  forall FS2 tr (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\ 
    State_simulation pinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent IS1. clear dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    eapply phinodes_placement_is_bsim' with (St2':=state2) in Hstsim; eauto.
    destruct Hstsim as [IS1' [Hopstar' Hstsim']].
    assert (OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
      apply OpsemPP.preservation_star in Hopstar'; auto.
    assert (Promotability.wf_State maxb pinfo cfg1 IS1') as Hnoalias'.
      eapply Promotability.preservation_star in Hopstar'; eauto; try tauto.
    eapply IHHopstar in Hstsim'; eauto; try tauto.
    destruct Hstsim' as [FS1 [Hopstar1 Hstsim']].
    exists FS1.
    split; eauto.
      eapply OpsemProps.sop_star_trans; eauto.
Qed.

Lemma sop_div'__phiplacement_State_simulation__sop_wf_div: forall
  tr (Hdiv : Opsem.sop_diverges' cfg2 IS2 tr),
  Opsem.sop_wf_diverges nat lt cfg1 (measure IS2) IS1 tr.
Proof.
  repeat match goal with
  | H:_ |- _ => generalize dependent H; clear H
  end. 
  cofix CIH.
  intros.
  inv Hdiv.
  eapply phinodes_placement_is_bsim with (St2':=state2) in Hstsim; eauto.
  destruct Hstsim as [[St1' [J1 J2]] | [St1' [J1 [J2 J3]]]].    
    assert (OpsemPP.wf_State cfg1 St1') as Hwfpp'.
      apply OpsemPP.preservation_plus in J1; auto.
    assert (Promotability.wf_State maxb pinfo cfg1 St1') as Hnoalias'.
      eapply Promotability.preservation_plus in J1; eauto; try tauto.
    eapply CIH in J2; eauto; try tauto.
    eapply Opsem.sop_wf_diverges_plus; eauto.

    assert (OpsemPP.wf_State cfg1 St1') as Hwfpp'.
      apply OpsemPP.preservation_star in J1; auto.
    assert (Promotability.wf_State maxb pinfo cfg1 St1') as Hnoalias'.
      eapply Promotability.preservation_star in J1; eauto; try tauto.
    eapply CIH in J3; eauto; try tauto.
    eapply Opsem.sop_wf_diverges_star with (m2:=measure state2); eauto.
Qed.

Lemma sop_div__phiplacement_State_simulation: forall 
  tr (Hdiv : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Proof.
  intros.
  apply OpsemProps.sop_diverges__sop_diverges' in Hdiv.
  eapply sop_div'__phiplacement_State_simulation__sop_wf_div in Hdiv; eauto.
  eapply (@OpsemProps.sop_wf_diverges__sop_diverges DGVs nat lt); 
    eauto using lt_wf.
Qed.

End TOPSIM.

Lemma uniq_products_phiplacement_simulation: forall f Ps2 rd pid ty 
  al pinfo
  (EQ1: PI_f pinfo = f) (EQ2: PI_rd pinfo = rd) (EQ3: PI_id pinfo = pid)
  (EQ4: PI_typ pinfo = ty) (EQ5: PI_align pinfo = al) Ps1,
  NoDup (getProductsIDs (Ps1 ++ product_fdef f :: Ps2)) ->
  Forall2
     (fun P1 P2 : product =>
      match P1, P2 with
      | product_fdef f1, product_fdef f2 => fdef_simulation pinfo f1 f2
      | _, _ => P1 = P2
      end)
     (Ps1 ++ product_fdef f :: Ps2)
     (Ps1 ++
      product_fdef
        (phinodes_placement f rd pid ty al (successors f)
           (make_predecessors (successors f))) :: Ps2).
Proof.
  induction Ps1; simpl; intros; subst.
    constructor.
      unfold fdef_simulation. 
      destruct pinfo. subst. simpl in *.
      destruct (fdef_dec PI_f PI_f); try congruence.
        unfold PI_preds. simpl.
        unfold PI_succs. simpl. auto.

      inv H.
      induction Ps2; auto.
        inv H3.
        constructor.
          destruct a; auto.      
            unfold fdef_simulation. 
            destruct (fdef_dec (PI_f pinfo) fdef5); try congruence.
              subst.
              contradict H2.
              simpl. auto.
          apply IHPs2; auto.
            intro J. apply H2. simpl. auto.

    inv H.
    constructor; auto.
      destruct a; auto.      
      unfold fdef_simulation. 
      destruct (fdef_dec (PI_f pinfo) fdef5); try congruence.
        subst.
        contradict H2.
        rewrite getProductsIDs_app. simpl.
        apply In_middle.
Qed.

Ltac uniq_result :=
repeat match goal with
| H1 : ?f ?a ?b ?c ?d = _,
  H2 : ?f ?a ?b ?c ?d = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a ?b ?c = _,
  H2 : ?f ?a ?b ?c = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a ?b = _,
  H2 : ?f ?a ?b = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a = _,
  H2 : ?f ?a = _ |- _ =>
  rewrite H1 in H2; inv H2
| H : ?f _ = ?f _ |- _ => inv H
| H : ?f _ _ = ?f _ _ |- _ => inv H
| H : ?f _ _ _ = ?f _ _ _ |- _ => inv H
| H : ?f _ _ _ _ = ?f _ _ _ _ |- _ => inv H
| H : ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ => inv H
| H : False |- _ => inv H
| H : (_, _) = (_, _) |- _ => inv H
end.

Lemma simulation__exCallUpdateLocals_None: forall pinfo F1 lc1 lc2 td rt noret0 rid
  oresult (Hrsim: reg_simulation pinfo F1 lc1 lc2)
  (Hexcall: Opsem.exCallUpdateLocals td rt noret0 rid oresult lc2 = None),
  Opsem.exCallUpdateLocals td rt noret0 rid oresult lc1 = None.
Proof.
  unfold Opsem.exCallUpdateLocals in *.
  intros.
  destruct noret0; inv Hexcall.
  destruct oresult; auto.
  destruct (fit_gv td rt g); auto.
    congruence.
Qed.

Lemma undefined_state__phinodes_placement_simulation_r2l: forall pinfo cfg1 St1 
  cfg2 St2 (Hwfpi: WF_PhiInfo pinfo) maxb
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 St1)
  (Hundef: OpsemPP.undefined_state cfg2 St2) (Hwfpp: OpsemPP.wf_State cfg2 St2) 
  (Hwfcfg: OpsemPP.wf_Config cfg2)
  (Hsim: State_simulation pinfo cfg1 St1 cfg2 St2),
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

Ltac phinodes_placement_undef_tac10:=
      match goal with 
      | H15: exists _:_, exists _:_, exists _:_, ?b = block_intro _ _ _ ?tmn |-
         exists _:_, exists _:_, exists _:_, exists _:_,  
           ?b = block_intro _ _ _ _ =>
         destruct H15 as [A [B [C H15]]]; subst;
         exists A; exists B; exists C; exists tmn; auto
      end.

Ltac phinodes_placement_undef_tac0:=
  match goal with 
  | Hsim: cmds_simulation _ _ _ _ _ _ _ (_::_) |- _ =>
    apply cmds_simulation_non_ldst_cons_inv in Hsim; try solve [
      simpl; auto | phinodes_placement_undef_tac10
    ];
    destruct Hsim as [cs1' [EQ1 Hsim]]; subst
  end.

Ltac phinodes_placement_undef_tac1:=
  match goal with
  | Hsim: State_simulation _ _ ?St1 _ ?St2, 
    Hwfpp : OpsemPP.wf_State _ ?St2 |- _ =>
    destruct St2 as [[|[? ? [|CurCmds] [] ?] [|[]]] ?]; try tauto;
    destruct CurCmds; try tauto;
    destruct St1 as [ECS ?];
    destruct Hsim as [? [? [? [X [? [Hsim [? [? ?]]]]]]]]; subst;
    uniq_result;
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hsim as [Hsim Hsim'];
    destruct ECS as [|[] ECS]; try tauto;
    unfold EC_simulation_head in Hsim;
    destruct Hsim as [? [? [? [? [? [? [? [? [? Hsim]]]]]]]]]; subst;
    apply cmds_simulation_nil_inv in Hsim; subst;
    destruct Hwfpp as [_ [_ [_ Hwfpp]]];
    match goal with
    | H9: block_simulation _ _ ?CurBB1 ?CurBB, c: cmd,
      H11: exists _:_, exists _:_, exists _:_, ?CurBB = _ |- _ =>
      destruct H11 as [l2 [ps2 [cs21 H11]]]; subst;
      eapply block_sim__pres__blockInFdefB in H9; eauto;
      apply Hwfpp in H9;
      destruct c; tinv H9
    end;
    unfold ECs_simulation_tail in Hsim';
    unfold EC_simulation_tail in Hsim';
    destruct Hsim' as [[? [? [? [? [? [? [? [? [? Hsim']]]]]]]]] _]; subst;
    phinodes_placement_undef_tac0;
    simpl; auto
  end.

    phinodes_placement_undef_tac1.

  Case "2". phinodes_placement_undef_tac1.
  Case "3".

Ltac phinodes_placement_undef_tac2:=
  match goal with
  | Hsim: State_simulation _ _ ?St1 _ _ |- _ =>
    destruct St1 as [ECS ?];
    destruct Hsim as [? [? [? [X [? [Hsim [? [? ?]]]]]]]]; subst;
    uniq_result;
    destruct ECS as [|[? [? ? ? ?] ? ? ?]]; try tauto;
    destruct Hsim as [Hsim _];
    unfold EC_simulation_head in Hsim;
    destruct Hsim as [? [? [? [? [? [? [? [? [? Hsim]]]]]]]]]; subst
  end.

    destruct St2 as [[|[? [? ? ? tmn] CurCmds tmn' ?] ?] ?]; try tauto.
    destruct tmn; try tauto.
    destruct CurCmds; try tauto.
    destruct tmn'; try tauto.

    phinodes_placement_undef_tac2.
    apply cmds_simulation_nil_inv in Hsim; subst.
    simpl.
    apply block_simulation__inv in H8. destruct H8; subst. auto.

  Case "4".

Ltac phinodes_placement_undef_tac41 :=
  match goal with 
  | HbInF: block_simulation _ _ ?b _,
    H: exists _:_, exists _:_, exists _:_,
         ?b = block_intro _ _ (_ ++ ?c :: _) _ |- _ =>
    eapply original_values_arent_tmps with 
      (B:=b)(instr:=insn_cmd c); eauto 2 using wf_system__wf_fdef;
      try solve [simpl; auto |
                apply insnInFdefBlockB_intro; auto;
                destruct H as [l2 [ps1 [cs11 H]]]; inv H;
                simpl; solve_in_list]
  end.

Ltac phinodes_placement_undef_tac4 :=
simpl; symmetry_ctx;
erewrite simulation__getOperandValue; try solve 
  [eauto | phinodes_placement_undef_tac41].

Ltac phinodes_placement_undef_tac3 Hundef :=
match goal with
| Hwfpp: OpsemPP.wf_State _ ?St2 |- _ =>
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto;
      inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind;
      phinodes_placement_undef_tac2;
      phinodes_placement_undef_tac0;
      phinodes_placement_undef_tac4
end.

    phinodes_placement_undef_tac3 Hundef;
      repeat fill_ctxhole; right; right; right; left; exists gn;
      fill_ctxhole; auto.
 
  Case "5".
    phinodes_placement_undef_tac3 Hundef.
      repeat fill_ctxhole; right; right; right; right; left; exists gn;
      fill_ctxhole; auto.

  Case "6".
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
      inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind.
      phinodes_placement_undef_tac2.
      right; right; right; right. right. left.
      destruct (fdef_dec (PI_f pinfo) CurFunction0); subst.
        destruct (is_temporary_dec id5 (PI_newids pinfo)) as [e | n].
          apply cmds_simulation_same_tail_inv in Hsim; auto.
            destruct Hsim as 
              [lid [pid [sid [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]]; subst.
            inv EQ4.
            elimtype False.
            destruct Hnoalias as [Hnoalias _].
            simpl in Hnoalias. destruct Hnoalias as [[Hnoalias _] _].
            destruct_if; try congruence.
            eapply WF_PhiInfo_spec190; 
              try solve [eauto using wf_system__wf_fdef | 
                         erewrite simulation__lookup_pid; 
                           eauto using wf_system__uniqFdef].

            phinodes_placement_undef_tac10.

          apply cmds_simulation_same_cons_inv in Hsim; auto.
            destruct Hsim as [cs1' [EQ Hsim']]; subst.
            phinodes_placement_undef_tac4.
            repeat fill_ctxhole. 
            exists gn; fill_ctxhole; auto.

            phinodes_placement_undef_tac10.
           
        apply cmds_simulation_other_cons_inv in Hsim; auto.
        destruct Hsim as [cs1' [EQ Hsim']]; subst.
        phinodes_placement_undef_tac4.
          repeat fill_ctxhole. 
          exists gn; fill_ctxhole; auto.

  Case "7".
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
      inv_mbind; destruct Hundef as [gv [mgv [EQ1 [EQ2 Hundef]]]]; 
      inv EQ1; inv EQ2; inv_mbind.
      phinodes_placement_undef_tac2.
      right; right; right; right. right. right. left.
      destruct (fdef_dec (PI_f pinfo) CurFunction0); subst.
        destruct (is_temporary_dec id5 (PI_newids pinfo)) as [e | n].
          apply cmds_simulation_same_head_inv in Hsim; auto.
            destruct Hsim as 
              [l2 [ps1 [tmn1 [lid [pid [sid 
                [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]]]]]; subst.
            uniq_result.
            elimtype False.
            destruct Hnoalias as [Hnoalias _].
            simpl in Hnoalias. destruct Hnoalias as [[Hnoalias _] _].
            destruct_if; try congruence.
            eapply WF_PhiInfo_spec200; 
              try solve [eauto using wf_system__wf_fdef, wf_system__uniqFdef | 
                         erewrite simulation__lookup_pid; 
                           eauto using wf_system__uniqFdef].

                destruct Hwfpp as [_ [Hwfpp _]].
                simpl in Hwfpp.
                destruct Hwfpp as [_ [W1 [W2 [Hwflc _]]]].
                destruct Hwfcfg as [_ [Hwfg [W3 W4]]].
                symmetry in HeqR.
                eapply OpsemPP.getOperandValue__wf_gvs with (t:=PI_typ pinfo)
                  (ps:=gl2) in HeqR; eauto.
                  inv HeqR. apply H13. auto.
                  destruct H10 as [l3 [ps3 [cs3 H10]]]; subst.
                  eapply wf_system__wf_fdef in W4; eauto 2.
                  eapply wf_fdef__wf_cmd in W1; eauto using in_middle.
                  inv W1; auto.

            phinodes_placement_undef_tac10.

          apply cmds_simulation_same_cons_inv in Hsim; auto.
            destruct Hsim as [cs1' [EQ Hsim']]; subst.
            phinodes_placement_undef_tac4. fill_ctxhole.
            phinodes_placement_undef_tac4. fill_ctxhole.
            exists gv. exists mgv. fill_ctxhole; auto.
            phinodes_placement_undef_tac10.
           
        apply cmds_simulation_other_cons_inv in Hsim; auto.
          destruct Hsim as [cs1' [EQ Hsim']]; subst.
          phinodes_placement_undef_tac4. fill_ctxhole.
          phinodes_placement_undef_tac4. fill_ctxhole.
          exists gv. exists mgv. fill_ctxhole; auto.

  Case "8".
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    phinodes_placement_undef_tac2.
    right; right; right; right. right. right. right.
    phinodes_placement_undef_tac0.
    phinodes_placement_undef_tac4. inv_mbind.
    exists g. split; auto.
    destruct Hundef as [fptr [EQ Hundef]]; inv EQ.
    inv_mbind. 
    erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.

    remember (OpsemAux.lookupExFdecViaPtr gl2 FunTable fptr) as R.
    destruct R as [[[]]|].
      assert (OpsemAux.lookupExFdecViaPtr gl1 FunTable fptr = 
        Some (fdec_intro (fheader_intro fnattrs5 typ0 id0 args5 varg0) deckind5)) as K.
        symmetry in HeqR1.
        eapply lookupExFdecViaPtr__simulation in HeqR1; eauto.
          tauto.
          phinodes_placement_undef_tac41.
      fill_ctxhole.
      inv_mbind.
      erewrite params2GVs__simulation; eauto.
        fill_ctxhole. exists l1.
        split; auto.
        destruct Hundef as [gvs [EQ Hundef]].
        dgvs_instantiate_inv.
        remember (callExternalOrIntrinsics (los2, nts2) fs2 Mem id0 typ0
                   (args2Typs args5) deckind5 l1) as R.
        destruct R as [[[]]|]; auto.
        inv_mbind.
        erewrite simulation__exCallUpdateLocals_None; eauto.

        match goal with
        | H9: block_simulation _ _ ?CurBB1 _,
          H11: exists _:_, exists _:_, exists _:_, ?CurBB1 = _ |- _ =>
           destruct H11 as [l3 [ps3 [cs31 H11]]]; inv H11
        end.
        eapply WF_PhiInfo_spec12; eauto 2 using wf_system__wf_fdef.

      erewrite TopSim.lookupExFdecViaPtr__simulation_None_r2l; eauto.
Qed.

Lemma phinodes_placement_sim: forall rd f Ps1 Ps2 los nts main VarArgs pid ty al
  num l0 ps0 cs0 tmn0 dones (Hreach: ret rd = reachablity_analysis f)
  (Hentry: getEntryBlock f = Some (block_intro l0 ps0 cs0 tmn0))
  (Hfind: find_promotable_alloca f cs0 dones = Some (pid, ty, num, al))
  (Hok: defined_program [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] 
          main VarArgs)
  (HwfS :
     wf_system 
       [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef (phinodes_placement f rd pid ty al (successors f)
                    (make_predecessors (successors f))) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Proof.
  intros.
  assert (Hfind':=Hfind).
  eapply find_promotable_alloca__WF_PhiInfo in Hfind; eauto.
  set (pinfo:={|PI_f := f; PI_rd := rd; PI_id := pid;
                PI_typ := ty; PI_num := num; PI_align := al |}).
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation pinfo
     [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
     [module_intro los nts
        (Ps1 ++
         product_fdef (phinodes_placement f rd pid ty al (successors f)
                      (make_predecessors (successors f))) :: Ps2)]) as Hssim.
    unfold system_simulation.
    constructor; auto.
    repeat split; auto.
    unfold products_simulation.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    unfold TopSim.products_simulation. simpl. unfold fdef_simulation.
    apply uniq_products_phiplacement_simulation; auto.

Ltac phinodes_placement_init := 
match goal with
| H: Opsem.s_genInitState ?s _ _ _ = _, _: WF_PhiInfo ?pinfo |- _ =>
    eapply s_genInitState__phiplacement_State_simulation in H; eauto;
    destruct H as [cfg1 [IS1 [Hinit1 Hstsim]]];
    assert (OpsemPP.wf_Config cfg1 /\ OpsemPP.wf_State cfg1 IS1) as Hwfst;
      try solve [eapply s_genInitState__opsem_wf; eauto];
    assert (exists maxb,
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom; 
      try solve [eapply s_genInitState__wf_globals_promotable; eauto; try tauto];
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]]
end.

  constructor; auto.
    intros tr t Hconv.
    inv Hconv.
    phinodes_placement_init. 
    eapply sop_star__phiplacement_State_simulation in Hstsim; eauto; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    eapply s_isFinialState__phiplacement_State_simulation_r2l in Hstsim'; eauto.
    exists t. split; auto using result_match_relf. econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    phinodes_placement_init.
    eapply sop_div__phiplacement_State_simulation in Hstsim; eauto; try tauto.
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.

    intros tr t Hgowrong.
    inv Hgowrong.
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg t) as HwfSt.
      eapply s_genInitState__opsem_wf in H; eauto using phinodes_placement_wfS.
      destruct H as [Hcfg2 HwfSt2].
      apply OpsemPP.preservation_star in H0; auto.
    assert (OpsemPP.undefined_state cfg t) as Hundef.
      apply stuck__undefined_state in H2; try solve [auto | tauto].
    phinodes_placement_init.
    eapply sop_star__phiplacement_State_simulation in Hstsim; eauto; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    eapply Promotability.preservation_star in Hprom; eauto; try tauto.
    assert (OpsemPP.undefined_state cfg1 FS1) as Hundef'.
      eapply undefined_state__phinodes_placement_simulation_r2l in Hundef; 
        try solve [eauto | tauto].
    assert (Opsem.s_isFinialState cfg1 FS1 = merror) as Hfinal'.
      eapply s_isFinialState__phiplacement_State_simulation_None_r2l in H2; 
        try solve [eauto | tauto].
        eapply phinodes_placement_wfS in HwfS; eauto.
    apply undefined_state__stuck' in Hundef'.
    exists tr. exists FS1.
    econstructor; eauto.
Qed.
