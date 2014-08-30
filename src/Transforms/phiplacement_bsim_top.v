Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import primitives.
Require Import vmem2reg.
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

(* This file proves that phinodes placement refines programs by top_sim. *)

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
  s_genInitState__State_simulation_tac.
  assert (J:=HeqR2).
  eapply getEntryBlock__simulation in J; eauto.
  destruct J as [b1 [J5 J6]].
  fill_ctxhole.
  destruct b1 as [l2 [ps2 cs2 tmn2]].
  assert (J:=Hfsim).
  apply fdef_simulation__eq_fheader in J.
  inv J.
  fill_ctxhole.
  match goal with
  | |- exists _:_, exists _:_, Some (?A, ?B) = _ /\ _ => exists A; exists B
  end.
  assert (J:=J6).
  apply block_simulation__inv in J.
  destruct J; subst.
  repeat (split; auto).
    exists l0. exists ps2. exists nil. auto.
    exists l0. exists ps0. exists nil. auto.
    apply reg_simulation_refl.
    eapply entry_cmds_simulation; eauto using 
      wf_system__wf_fdef, wf_system__uniqFdef.
Qed.

Lemma s_isFinialState__phiplacement_State_simulation_r2l:
  forall pinfo cfg1 FS1 cfg2 FS2 r
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hpp1: @OpsemPP.wf_State DGVs cfg1 FS1) 
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r),
  Opsem.s_isFinialState cfg1 FS1 = ret r.
Proof.
  destruct cfg1, cfg2, FS1, FS2.
  destruct CurTargetData as [los nts].
  simpl. intros.
  destruct ECS0 as [|[]]; tinv Hfinal.
  destruct Hstsim as [J4 [J5 [J6 [J7 [J8 J9]]]]]; subst.
  destruct ECS as [|[]]; tinv J6.
  destruct J6 as [J61 J62].
  destruct CurCmds; tinv Hfinal. 
  unfold EC_simulation_head in J61.
  destruct Hpp1 as [_ [[_ [HBinF [HinPs _]]] _]].
  destruct J61 as [G3 [G4 [G5 [G6 [
                    [? [? [? G7]]] [
                    [? [? [? G8]]] [G9 G10]]]]]]]; subst.
  apply cmds_simulation_nil_inv in G10. subst.
  destruct Hwfcfg1 as [_ [_ [J1 J2]]].
  assert (HwfF := J1).
  eapply wf_system__wf_fdef with (f:=CurFunction0) in HwfF; eauto.
  destruct Terminator; tinv Hfinal; 
    destruct ECS0; tinv Hfinal; destruct ECS; tinv J62.

    erewrite simulation__getOperandValue with (lc2:=Locals); eauto;
      match goal with
      | _:blockInFdefB (?l0, stmts_intro ?ps ?cs ?tmn) _ = _ |- _ =>
        eapply original_values_arent_tmps with 
          (instr:=insn_terminator tmn)
          (B:=(l0, stmts_intro ps cs tmn)); eauto;
          try solve [
            simpl; apply andb_true_iff;
            split; try solve [auto | apply terminatorEqB_refl] |
            simpl; auto
          ]
      end.

    assumption.
Qed.

Lemma s_isFinialState__phiplacement_State_simulation_r2l':
  forall pinfo cfg1 FS1 cfg2 FS2 r
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hpp1: @OpsemPP.wf_State DGVs cfg1 FS1) 
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r),
  exists FS1',
    Opsem.sop_star cfg1 FS1 FS1' E0 /\
    State_simulation pinfo cfg1 FS1' cfg2 FS2 /\
    Opsem.s_isFinialState cfg1 FS1' = ret r.
Proof.
  intros. exists FS1.
  split; eauto using s_isFinialState__phiplacement_State_simulation_r2l.
Qed.

Lemma s_isFinialState__phiplacement_State_simulation_None_r2l:
  forall pinfo cfg1 FS1 cfg2 FS2 maxb (Hwfcfg1: OpsemPP.wf_Config cfg1) 
  (Hwfpi: WF_PhiInfo pinfo) (Hundef: @OpsemPP.undefined_state DGVs cfg2 FS2)
  (Hpp1: @OpsemPP.wf_State DGVs cfg1 FS1)
  (Hpp2: @OpsemPP.wf_State DGVs cfg2 FS2) (Hcfg: OpsemPP.wf_Config cfg2)
  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 FS1)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = None),
  Opsem.s_isFinialState cfg1 FS1 = None.
Proof.
  destruct cfg1, cfg2, FS1, FS2.
  destruct CurTargetData as [los nts].
  simpl. intros.
  destruct Hstsim as [J4 [J5 [J6 [J7 [J8 J9]]]]]; subst.
  destruct Hwfcfg1 as [_ [_ [J1 J2]]].
  destruct ECS as [|[]]; tinv J6; auto.
  destruct ECS0 as [|[]]; tinv J6.
  destruct J6 as [J61 J62].
  destruct CurCmds; auto.
  unfold EC_simulation_head in J61.
  destruct Hpp1 as [_ [[_ [HBinF [HinPs _]]] _]].
  destruct J61 as [G3 [G4 [G5 [G6 [
                    [? [? [? G7]]] [
                    [? [? [? G8]]] [G9 G10]]]]]]]; subst.
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
        | _:blockInFdefB (?l0, stmts_intro ?ps ?cs ?tmn) _ = _ |- _ =>
          eapply original_values_arent_tmps with 
            (instr:=insn_terminator tmn)
            (B:=(l0, stmts_intro ps cs tmn)); eauto;
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

      destruct Hpp2 as [_ [Hpp2 _]].
      simpl in Hpp2.
      destruct Hpp2 as [_ [W1 [W2 [Hwflc _]]]].
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
        (phinodes_placement rd pid ty al (successors f)
           (XATree.make_predecessors (successors f)) f) :: Ps2).
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

Lemma undefined_state__phiplacement_State_simulation_r2l: forall pinfo cfg1 St1 
  cfg2 St2 (Hwfpi: WF_PhiInfo pinfo) maxb
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 St1)
  (Hundef: OpsemPP.undefined_state cfg2 St2) 
  (Hwfpp1: OpsemPP.wf_State cfg1 St1) (Hwfpp: OpsemPP.wf_State cfg2 St2) 
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfcfg: OpsemPP.wf_Config cfg2)
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
      | H15: exists _:_, exists _:_, exists _:_, ?b = (_, stmts_intro _ _ ?tmn) |-
         exists _:_, exists _:_, exists _:_, exists _:_,  
           ?b = (_, stmts_intro _ _ _) =>
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
    Hwfpp1 : OpsemPP.wf_State _ ?St1,
    Hwfpp : OpsemPP.wf_State _ ?St2 |- _ =>
    destruct St2 as [[|[? ? [|CurCmds] [] ?] [|[]]] ?]; try tauto;
    destruct CurCmds; try tauto;
    destruct St1 as [ECS ?];
    destruct Hsim as [X [? [Hsim [? [? ?]]]]]; subst;
    uniq_result;
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hsim as [Hsim Hsim'];
    destruct ECS as [|[] ECS]; try tauto;
    unfold EC_simulation_head in Hsim;
    destruct Hwfpp1 as [_ [[_ [HBinF [HinPs _]]] _]];
    destruct Hsim as [? [? [? [? [? [? [? Hsim]]]]]]]; subst;
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
    destruct Hsim' as [[? [? [? [? [? [? [? Hsim']]]]]]] _]; subst;
    phinodes_placement_undef_tac0;
    simpl; auto
  end.

    phinodes_placement_undef_tac1.

  Case "2". phinodes_placement_undef_tac1.
  Case "3".

Ltac phinodes_placement_undef_tac2:=
  match goal with
  | Hwfcfg1: OpsemPP.wf_Config ?cfg1,
    Hwfpp1 : OpsemPP.wf_State _ ?St1,
    Hsim: State_simulation _ ?cfg1 ?St1 _ _ |- _ =>
    destruct St1 as [ECS ?];
    destruct Hsim as [X [? [Hsim [? [? ?]]]]]; subst;
    destruct Hwfcfg1 as [_ [_ [Hwfs HMinS]]];
    uniq_result;
    destruct ECS as [|[? [? []] ? ? ?]]; try tauto;
    destruct Hsim as [Hsim _];
    unfold EC_simulation_head in Hsim;
    destruct Hwfpp1 as [_ [[_ [HBinF [HinPs _]]] _]];
    destruct Hsim as [? [? [? [Hbsim [Hbeq1 [Hbeq2 [? Hsim]]]]]]]; subst
  end.

    destruct St2 as [[|[? [? [? ? tmn]] CurCmds tmn' ?] ?] ?]; try tauto.
    destruct tmn; try tauto.
    destruct CurCmds; try tauto.
    destruct tmn'; try tauto.

    phinodes_placement_undef_tac2.
    apply cmds_simulation_nil_inv in Hsim; subst.
    simpl.
    apply block_simulation__inv in Hbsim. destruct Hbsim; subst. auto.

  Case "4".

Ltac phinodes_placement_undef_tac41 :=
  match goal with 
  | HbInF: block_simulation _ _ ?b _,
    H: exists _:_, exists _:_, exists _:_,
         ?b = (_, stmts_intro _ (_ ++ ?c :: _) _) |- _ =>
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
                  inv HeqR. 
                  match goal with
                  | H5: _ -> _ -> gv_chunks_match_typ _ _ _ |- _ => apply H5; auto
                  end.
                  destruct Hbeq2 as [l3 [ps3 [cs3 H10]]]; subst.
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
        fill_ctxhole. exists l2.
        split; auto.
        destruct Hundef as [gvs [EQ Hundef]].
        dgvs_instantiate_inv.
        remember (callExternalOrIntrinsics (los2, nts2) fs2 Mem id0 typ0
                   (args2Typs args5) deckind5 l2) as R.
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

Lemma undefined_state__phiplacement_State_simulation_r2l': forall pinfo cfg1 St1 
  cfg2 St2 (Hwfpi: WF_PhiInfo pinfo) maxb
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 St1)
  (Hundef: OpsemPP.undefined_state cfg2 St2) (Hwfpp: OpsemPP.wf_State cfg2 St2) 
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (Hwfcfg: OpsemPP.wf_Config cfg2)
  (Hsim: State_simulation pinfo cfg1 St1 cfg2 St2),
  exists St1', 
    Opsem.sop_star cfg1 St1 St1' E0 /\
    State_simulation pinfo cfg1 St1' cfg2 St2 /\
    OpsemPP.undefined_state cfg1 St1'.
Proof.
  intros. exists St1.
  split; eauto using undefined_state__phiplacement_State_simulation_r2l.
Qed.

Require Import Program.Tactics.

(* The main result *)
Lemma phinodes_placement_sim: forall rd f Ps1 Ps2 los nts main VarArgs pid ty al
  num l0 ps0 cs0 tmn0 dones (Hreach: ret rd = reachablity_analysis f)
  (Hentry: getEntryBlock f = Some (l0, stmts_intro ps0 cs0 tmn0))
  (Hfind: find_promotable_alloca f cs0 dones = Some (pid, ty, num, al))
  (Hok: defined_program [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] 
          main VarArgs)
  (HwfS :
     wf_system 
       [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef (phinodes_placement rd pid ty al (successors f)
                    (XATree.make_predecessors (successors f)) f) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Proof.
  intros.
  assert (Hfind':=Hfind).
  eapply find_promotable_alloca__WF_PhiInfo in Hfind; eauto.
  set (pinfo:={|PI_f := f; PI_rd := rd; PI_id := pid;
                PI_typ := ty; PI_num := num; PI_align := al |}).
  set (wf_prop1 := fun cfg st =>
         OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg st /\
         exists maxb,
           MemProps.wf_globals maxb (OpsemAux.Globals cfg) /\ 0 <= maxb /\
           Promotability.wf_State maxb pinfo cfg st).
  set (wf_prop2 := fun cfg st =>
         OpsemPP.wf_Config cfg /\ @OpsemPP.wf_State DGVs cfg st).
  set (st_sim := fun cfg1 st1 cfg2 st2 => 
          State_simulation pinfo cfg1 st1 cfg2 st2).
  set (sys_sim := fun s1 s2 => system_simulation pinfo s1 s2).
  apply top_sim with (ftrans:=phinodes_placement rd pid ty al (successors f)
                        (XATree.make_predecessors (successors f))) 
    (wf_prop1:=wf_prop1) (wf_prop2:=wf_prop2) (state_simulation:=st_sim)
    (system_simulation:=sys_sim); 
    try solve [auto | unfold wf_prop1; tauto | unfold wf_prop2; tauto |
      unfold wf_prop1, wf_prop2; intros; destruct_conjs; try solve [
        eauto 8 using Promotability.preservation_star, 
                      (@OpsemPP.preservation_star DGVs) |
        eapply sop_star__phiplacement_State_simulation; eauto |
        eapply s_isFinialState__phiplacement_State_simulation_r2l'; eauto |
        eapply sop_div__phiplacement_State_simulation; eauto |
        eapply undefined_state__phiplacement_State_simulation_r2l'; eauto |
        eapply s_isFinialState__phiplacement_State_simulation_None_r2l; eauto
      ] |
      top_sim_syssim_tac fsim Fsim
    ].

    intros. subst.
    assert (OpsemPP.wf_Config cfg2 /\ OpsemPP.wf_State cfg2 IS2) as Hwfst'.
      eapply s_genInitState__opsem_wf in Hinit; eauto.
        eapply phinodes_placement_wfS; eauto.
    eapply s_genInitState__phiplacement_State_simulation in Hinit; eauto.
    destruct Hinit as [cfg1 [IS1 [Hinit1 Hstsim]]].
    assert (OpsemPP.wf_Config cfg1 /\ OpsemPP.wf_State cfg1 IS1) as Hwfst.
      eapply s_genInitState__opsem_wf; eauto.
    destruct Hwfst.
    assert (exists maxb,
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom.
      eapply Promotability.s_genInitState__wf_globals_promotable; eauto.
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]].
    unfold wf_prop1, wf_prop2.
    eauto 12.
Qed.
