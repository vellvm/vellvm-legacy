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
Require Import memory_props.
Require Import program_sim.
Require Import trans_tactic.
Require Import top_sim.
Require Import phiplacement_bsim_defs.

Import Promotability.

Lemma phinodes_placement_is_correct__dsBranch: forall
  (pinfo : PhiInfo) (Cfg1 : OpsemAux.Config) (St1 : Opsem.State)
  (S : system) (TD : TargetData) (Ps : list product) (F : fdef) (B : block)
  (lc : Opsem.GVsMap) (gl : GVMap) (fs : GVMap) (bid : id) (Cond : value)
  (l1 : l) (l2 : l) (ECs : list Opsem.ExecutionContext) (Mem : mem)
  (als : list mblock) maxb EC1 Cfg1 Cfg2 (Hwfpi: WF_PhiInfo pinfo)
  (Heq1: Cfg2 = {| OpsemAux.CurSystem := S;
                   OpsemAux.CurTargetData := TD;
                   OpsemAux.CurProducts := Ps;
                   OpsemAux.Globals := gl;
                   OpsemAux.FunTable := fs |})
  (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1)
  (Heq2: EC1 = {| Opsem.CurFunction := F;
                  Opsem.CurBB := B;
                  Opsem.CurCmds := nil;
                  Opsem.Terminator := insn_br bid Cond l1 l2;
                  Opsem.Locals := lc;
                  Opsem.Allocas := als |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
            {| Opsem.ECS := EC1 :: ECs;
               Opsem.Mem := Mem |})
  (conds : GVsT DGVs) (c : GenericValue) (l' : l) (ps' : phinodes)
  (cs' : cmds) (tmn' : terminator) (lc' : Opsem.GVsMap)
  (H : Opsem.getOperandValue TD Cond lc gl = ret conds)
  (H0 : c @ conds)
  (H1 : ret block_intro l' ps' cs' tmn' =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1))
  (H2 : Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc =
       ret lc'),
  exists St1' : Opsem.State,
     Opsem.sop_plus Cfg1 St1 St1' E0 /\
     State_simulation pinfo Cfg1 St1' Cfg2
     {|Opsem.ECS := {| Opsem.CurFunction := F;
                       Opsem.CurBB := (block_intro l' ps' cs' tmn');
                       Opsem.CurCmds := cs';
                       Opsem.Terminator := tmn';
                       Opsem.Locals := lc';
                       Opsem.Allocas := als |} :: ECs;
       Opsem.Mem := Mem |}.
Proof.
  intros. subst.
  destruct_ctx_br.
  destruct Hwfpp as [_ [[Hreachb _] _]]; auto.

  assert (HuniqF:=HFinPs).
  eapply wf_system__uniqFdef in HuniqF; eauto.

  assert (exists b1,
    (if isGVZero (los, nts) c
     then lookupBlockViaLabelFromFdef F1 l2
     else lookupBlockViaLabelFromFdef F1 l1) = Some b1 /\
    block_simulation pinfo F1 b1 (block_intro l' ps' cs' tmn')) as Hfind.
    symmetry in H1.
    destruct (isGVZero (los, nts) c);
      eapply lookup_fdef_sim__block_sim in H1; eauto.
  destruct Hfind as [b1 [Hfind Htblock]].

  destruct Heqb1 as [l3 [ps3 [cs11 Heqb1]]]; subst.

  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.

  assert (isReachableFromEntry F1 b1) as Hreachb1.
    unfold isReachableFromEntry in *.
    destruct b1.
    destruct (isGVZero (los, nts) c); try solve [
      apply lookupBlockViaLabelFromFdef_inv in Hfind; auto;
      destruct Hfind as [Hfind _]; subst;
      eapply reachable_successors; eauto; simpl; auto].

  assert (Htcmds':=Htcmds).
  apply cmds_simulation_nil_inv in Htcmds'. subst.
  unfold cmds_simulation in Htcmds.

  assert (blockInFdefB b1 F1)as HBinF'.
    destruct F1 as [[f t i0 a v] bs].
    destruct HuniqF as [HuniqBlocks HuniqArgs].
    destruct b1.
    destruct (isGVZero (los,nts) c);
      apply genLabel2Block_blocks_inv with (f:=fheader_intro f t i0 a v)
        in Hfind; auto; destruct Hfind; eauto.

  assert (exists lc1',
    Opsem.switchToNewBasicBlock (los, nts) b1
      (block_intro l3 ps3 (cs11 ++ nil) (insn_br bid Cond l1 l2)) gl
      lc1 = ret lc1' /\
    reg_simulation pinfo F1 lc1' lc') as Hswitch1.
    eapply reg_simulation__switchToNewBasicBlock; eauto.

  destruct Hswitch1 as [lc1' [Hswitch1 Hrsim']].

  unfold block_simulation, phinodes_placement_block in *.

  assert (Opsem.getOperandValue (los, nts) Cond lc1 gl = ret conds) as Hget.
    erewrite simulation__getOperandValue with (lc2:=lc); eauto.
    apply original_values_arent_tmps with
      (instr:=insn_terminator (insn_br bid Cond l1 l2))
      (B:=block_intro l3 ps3 (cs11 ++ nil) (insn_br bid Cond l1 l2))
      (S:=S1) (m:=module_intro los nts Ps1); simpl; auto.
      apply andb_true_iff.
      split; auto.
        apply terminatorEqB_refl.

  destruct (fdef_dec (PI_f pinfo) F1) as [ e | n]; try subst F1.
  SCase "F is tranformed".
    assert ((PI_newids pinfo) ! l3 <> None) as Hreach.
      eapply reachable_blk_has_newids; subst; simpl; eauto.

    remember ((PI_newids pinfo) ! l3) as R.
    destruct R as [[[lid pid] sid]|]; try congruence.
    destruct Htcmds as [_ [_ Htcmds]].
    assert (exists sc, exists scs, (PI_succs pinfo) ! l3 = Some (sc::scs))
      as R2.
      apply WF_PhiInfo__succs in HBinF; subst; simpl; auto; congruence.

    destruct R2 as [sc [scs Heq]].
    rewrite Heq in *.
    assert ([insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo))
               (PI_align pinfo)] <> nil) as Hwft.
      intro J. inv J.
    apply_clear Htcmds in Hwft.

    destruct b1 as [l0 ps0 cs0 tmn0].
    unfold phinodes_placement_block in Htblock.
    assert ((PI_newids pinfo) ! l0 <> None) as Hreach'.
      eapply reachable_blk_has_newids; subst; simpl; eauto.
    remember ((PI_newids pinfo) ! l0) as R1.
    destruct R1 as [[[lid' pid'] sid']|]; try congruence.
    assert (exists prd, exists prds, (PI_preds pinfo) ! l0 = Some (prd::prds))
      as R2.
      eapply WF_PhiInfo__preds in HBinF; subst; simpl; eauto.
        simpl in HBinF.
        destruct (PI_f pinfo) as [[f t i0 a v] bs].
        destruct HuniqF as [HuniqBlocks HuniqArgs].
        destruct (isGVZero (los,nts) c);
          apply genLabel2Block_blocks_inv
            with (f:=fheader_intro f t i0 a v) in Hfind; auto;
            destruct Hfind; auto.

    destruct R2 as [prd [prds Heq']].
    simpl in H.
    rewrite Heq' in *.
    inversion Htblock; subst l' ps' cs' tmn'. clear Htblock.

    unfold wf_tmp_value in Hwft. simpl in Hwft.
    destruct Hwft as [gvsa [gv [Hlkp1 [Hld Hlk2]]]].

    assert (lookupAL _ lc' pid' = Some gv /\
            lookupAL (GVsT DGVs) lc' (PI_id pinfo) = ret gvsa) as Hswitch2.

      clear - Hbsim H2 Hrsim' Hlk2 HBinF' HuniqF Hwfpi HeqR1 Heq' HeqR Hfind
        HBinF Hlkp1.

      assert (exists ps3', exists cs3',
            B = block_intro l3 ps3'
                  (cs3'++[insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo))
                  (PI_align pinfo)])
                  (insn_br bid Cond l1 l2)) as EQ.
        clear - Hbsim.
        subst.
        destruct ((PI_preds pinfo) ! l3) as [[]|]; simpl_env; eauto.
        simpl.
        exists ([gen_phinode pid (PI_typ pinfo) (PI_newids pinfo)
          ([l0] ++ l4)] ++ ps3).
        exists
          ([insn_store sid (PI_typ pinfo) (value_id pid) (value_id (PI_id pinfo))
             (PI_align pinfo)] ++ cs11).
        simpl_env. auto.

      clear Hbsim.
      destruct EQ as [ps3' [cs3' EQ]]; subst B.
      eapply WF_PhiInfo_spec8 in Hfind; eauto.
      destruct Hfind as [succs [J1 J2]].
      eapply WF_PhiInfo__switchToNewBasicBlock; eauto.

    destruct Hswitch2 as [Hlka Hlkb].

    exists (Opsem.mkState
             ((Opsem.mkEC (PI_f pinfo) (block_intro l0 ps0 cs0 tmn0) cs0 tmn0
                lc1' als)::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_plus.
      econstructor; eauto.

    SSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next).
      SSSCase "bsim".
        autounfold with ppbsim. simpl.
        destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
        rewrite <- HeqR1. rewrite Heq'. auto.

      SSSCase "eq".
        exists l0. exists ps0. exists nil. auto.

      SSSCase "eq".
        exists l0.
        exists (gen_phinode pid' (PI_typ pinfo) (PI_newids pinfo) (prd :: prds)
                :: ps0).
        exists nil. simpl_env. auto.

      SSSCase "csim".
        autounfold with ppbsim.
        destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
        rewrite <- HeqR1. rewrite Heq'.
        split; intros.
          split; auto.
            intros.
            unfold wf_tmp_value. simpl.
            exists gvsa. exists gv. repeat split; auto.
        split; intros; congruence.

  SCase "F isnt tranformed".
    subst b1.

    exists (Opsem.mkState
             ((Opsem.mkEC F1 (block_intro l' ps' cs' tmn') cs' tmn' lc1' als)
              ::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_plus.
      econstructor; eauto.

    SSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next).
      SSSCase "bsim".
        apply block_simulation_neq_refl; auto.

      SSSCase "eq".
        exists l'. exists ps'. exists nil. auto.

      SSSCase "eq".
        exists l'. exists ps'. exists nil. simpl_env. auto.

      SSSCase "csim".
        apply cmds_simulation_neq_refl; auto.
Qed.

Lemma phinodes_placement_is_correct__dsBranch_uncond: forall
  (pinfo : PhiInfo) (Cfg1 : OpsemAux.Config) (St1 : Opsem.State)
  (S : system) (TD : TargetData) (Ps : list product) (F : fdef) (B : block)
  (lc : Opsem.GVsMap) (gl : GVMap) (fs : GVMap) (bid : id)
  (l0 : l) (ECs : list Opsem.ExecutionContext) (Mem : mem)
  (als : list mblock) maxb EC1 Cfg1 Cfg2 (Hwfpi: WF_PhiInfo pinfo)
  (Heq1: Cfg2 = {| OpsemAux.CurSystem := S;
                   OpsemAux.CurTargetData := TD;
                   OpsemAux.CurProducts := Ps;
                   OpsemAux.Globals := gl;
                   OpsemAux.FunTable := fs |})
  (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1)
  (Heq2: EC1 = {| Opsem.CurFunction := F;
                  Opsem.CurBB := B;
                  Opsem.CurCmds := nil;
                  Opsem.Terminator := insn_br_uncond bid l0;
                  Opsem.Locals := lc;
                  Opsem.Allocas := als |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
            {| Opsem.ECS := EC1 :: ECs;
               Opsem.Mem := Mem |})
  (l' : l) (ps' : phinodes)
  (cs' : cmds) (tmn' : terminator) (lc' : Opsem.GVsMap)
  (H1 : ret block_intro l' ps' cs' tmn' = lookupBlockViaLabelFromFdef F l0)
  (H2 : Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc =
       ret lc'),
  exists St1' : Opsem.State,
     Opsem.sop_plus Cfg1 St1 St1' E0 /\
     State_simulation pinfo Cfg1 St1' Cfg2
     {|Opsem.ECS := {| Opsem.CurFunction := F;
                       Opsem.CurBB := (block_intro l' ps' cs' tmn');
                       Opsem.CurCmds := cs';
                       Opsem.Terminator := tmn';
                       Opsem.Locals := lc';
                       Opsem.Allocas := als |} :: ECs;
       Opsem.Mem := Mem |}.
Proof.
  intros. subst.
  destruct_ctx_br.
  destruct Hwfpp as [_ [[Hreachb _] _]]; auto.

  assert (HuniqF:=HFinPs).
  eapply wf_system__uniqFdef in HuniqF; eauto.

  assert (exists b1,
    lookupBlockViaLabelFromFdef F1 l0 = Some b1 /\
    block_simulation pinfo F1 b1 (block_intro l' ps' cs' tmn')) as Hfind.
    symmetry in H1.
    eapply lookup_fdef_sim__block_sim in H1; eauto.
  destruct Hfind as [b1 [Hfind Htblock]].

  destruct Heqb1 as [l3 [ps3 [cs11 Heqb1]]]; subst.

  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.

  assert (isReachableFromEntry F1 b1) as Hreachb1.
    unfold isReachableFromEntry in *.
    destruct b1.
    apply lookupBlockViaLabelFromFdef_inv in Hfind; auto.
    destruct Hfind as [Hfind _]; subst.
    eapply reachable_successors; eauto; simpl; auto.

  assert (Htcmds':=Htcmds).
  apply cmds_simulation_nil_inv in Htcmds'. subst.
  unfold cmds_simulation in Htcmds.
  unfold block_simulation, phinodes_placement_block in *.

  assert (blockInFdefB b1 F1)as HBinF'.
    destruct F1 as [[f t i0 a v] bs].
    destruct HuniqF as [HuniqBlocks HuniqArgs].
    destruct b1.
    apply genLabel2Block_blocks_inv with (f:=fheader_intro f t i0 a v)
      in Hfind; auto; destruct Hfind; eauto.

  assert (exists lc1',
    Opsem.switchToNewBasicBlock (los, nts) b1
      (block_intro l3 ps3 (cs11 ++ nil) (insn_br_uncond bid l0)) gl
      lc1 = ret lc1' /\
    reg_simulation pinfo F1 lc1' lc') as Hswitch1.
    eapply reg_simulation__switchToNewBasicBlock; eauto.

  destruct Hswitch1 as [lc1' [Hswitch1 Hrsim']].

  destruct (fdef_dec (PI_f pinfo) F1) as [ e | n]; try subst F1.
  SCase "F is tranformed".
    assert ((PI_newids pinfo) ! l3 <> None) as Hreach.
      eapply reachable_blk_has_newids; subst; simpl; eauto.

    remember ((PI_newids pinfo) ! l3) as R.
    destruct R as [[[lid pid] sid]|]; try congruence.
    destruct Htcmds as [_ [_ Htcmds]].
    assert (exists sc, exists scs, (PI_succs pinfo) ! l3 = Some (sc::scs))
      as R2.
      apply WF_PhiInfo__succs in HBinF; subst; simpl; auto; congruence.

    destruct R2 as [sc [scs Heq]].
    rewrite Heq in *.
    assert ([insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo))
              (PI_align pinfo)] <> nil) as Hwft.
      intro J. inv J.
    apply_clear Htcmds in Hwft.

    destruct b1 as [l1 ps1 cs1 tmn1].
    unfold phinodes_placement_block in Htblock.
    assert ((PI_newids pinfo) ! l1 <> None) as Hreach'.
      eapply reachable_blk_has_newids; subst; simpl; eauto.

    remember ((PI_newids pinfo) ! l1) as R1.
    destruct R1 as [[[lid' pid'] sid']|]; try congruence.
    assert (exists prd, exists prds, (PI_preds pinfo) ! l1 = Some (prd::prds))
      as R2.
      eapply WF_PhiInfo__preds in HBinF; subst; simpl; eauto.
        simpl in HBinF.
        destruct (PI_f pinfo) as [[f t i0 a v] bs].
        destruct HuniqF as [HuniqBlocks HuniqArgs].
        apply genLabel2Block_blocks_inv
          with (f:=fheader_intro f t i0 a v) in Hfind; auto;
          destruct Hfind; auto.

    destruct R2 as [prd [prds Heq']].
    rewrite Heq' in *.
    inversion Htblock; subst l' ps' cs' tmn'. clear Htblock.

    unfold wf_tmp_value in Hwft. simpl in Hwft.
    destruct Hwft as [gvsa [gv [Hlkp1 [Hld Hlk2]]]].

    assert (lookupAL _ lc' pid' = Some gv /\
            lookupAL (GVsT DGVs) lc' (PI_id pinfo) = ret gvsa) as Hswitch2.

      clear - Hbsim H2 Hrsim' Hlk2 HBinF' HuniqF Hwfpi HeqR1 Heq' HeqR Hfind
        HBinF Hlkp1.

      assert (exists ps3', exists cs3',
            B = block_intro l3 ps3'
                  (cs3'++[insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo))
                  (PI_align pinfo)])
                  (insn_br_uncond bid l0)) as EQ.
        clear - Hbsim.
        subst.
        destruct ((PI_preds pinfo) ! l3) as [[]|]; simpl_env; eauto.
        simpl.
        exists ([gen_phinode pid (PI_typ pinfo) (PI_newids pinfo)
          ([l1] ++ l2)] ++ ps3).
        exists
          ([insn_store sid (PI_typ pinfo) (value_id pid) (value_id (PI_id pinfo))
             (PI_align pinfo)] ++ cs11).
        simpl_env. auto.

      clear Hbsim.
      destruct EQ as [ps3' [cs3' EQ]]; subst B.

      eapply WF_PhiInfo_spec9 in Hfind; eauto.
      destruct Hfind as [succs [J1 J2]].
      eapply WF_PhiInfo__switchToNewBasicBlock; eauto.

    destruct Hswitch2 as [Hlka Hlkb].

    exists (Opsem.mkState
             ((Opsem.mkEC (PI_f pinfo) (block_intro l1 ps1 cs1 tmn1) cs1 tmn1
              lc1' als)::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_plus.
      econstructor; eauto.

    SSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next).
      SSSCase "bsim".
        autounfold with ppbsim. simpl.
        destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
        rewrite <- HeqR1. rewrite Heq'. auto.

      SSSCase "eq".
        exists l1. exists ps1. exists nil. auto.

      SSSCase "eq".
        exists l1.
        exists (gen_phinode pid' (PI_typ pinfo) (PI_newids pinfo) (prd :: prds)
                  :: ps1).
        exists nil. simpl_env. auto.

      SSSCase "csim".
        autounfold with ppbsim.
        destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
        rewrite <- HeqR1. rewrite Heq'.
        split; intros.
          split; auto.
            intros.
            unfold wf_tmp_value. simpl.
            exists gvsa. exists gv. repeat split; auto.
        split; intros; congruence.

  SCase "F isnt tranformed".
    subst b1.

    exists (Opsem.mkState
             ((Opsem.mkEC F1 (block_intro l' ps' cs' tmn') cs' tmn' lc1' als)
              ::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_plus.
      econstructor; eauto.

    SSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next).
      SSSCase "bsim".
        apply block_simulation_neq_refl; auto.

      SSSCase "eq".
        exists l'. exists ps'. exists nil. auto.

      SSSCase "eq".
        exists l'. exists ps'. exists nil. simpl_env. auto.

      SSSCase "csim".
        apply cmds_simulation_neq_refl; auto.
Qed.

Ltac destruct_ctx_other :=
match goal with
| [Hsim : State_simulation _ ?Cfg1 ?St1
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           Opsem.ECS := {|
                          Opsem.CurFunction := ?F;
                          Opsem.CurBB := _;
                          Opsem.CurCmds := _::_;
                          Opsem.Terminator := _;
                          Opsem.Locals := _;
                          Opsem.Allocas := _ |} :: _;
           Opsem.Mem := _ |} |- _] =>
  destruct Cfg1 as [S1 TD1 Ps1 gl1 fs1];
  destruct St1 as [ECs1 M1];
  destruct TD1 as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Heq2
    [Heq3 Heq4]]]]]]]]; subst;
  destruct ECs1 as [|[F1 B1 cs1 tmn1 lc1 als1] ECs1];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct HsimEC as [HBinF [HFinPs [Htfdef [Heq0 [Heq1 [Hbsim [Heqb1 [Heqb2
    [Hrsim Htcmds]]]]]]]]]; subst
end.

Lemma phinodes_placement_is_correct__dsLoad: forall (maxb : Values.block) 
  (pinfo : PhiInfo)
  (Cfg1 : OpsemAux.Config) (St1 : Opsem.State) (Hwfpi : WF_PhiInfo pinfo)
  (Hnoalias : wf_State maxb pinfo Cfg1 St1) (S : system) (TD : TargetData)
  (Ps : list product) (F : fdef) (B : block) (lc : Opsem.GVsMap) (gl : GVMap)
  (fs : GVMap) (id0 : id) (t : typ) (align0 : align) (v : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (als : list mblock) Cfg2
  (EQ : Cfg2 = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := TD;
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := F;
                        Opsem.CurBB := B;
                        Opsem.CurCmds := insn_load id0 t v align0 :: cs;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: EC;
           Opsem.Mem := Mem |})
  (mps : GVsT DGVs) (mp : GenericValue) (gv : GenericValue)
  (H : Opsem.getOperandValue TD v lc gl = ret mps)
  (H0 : mp @ mps) (H1 : mload TD Mem mp t align0 = ret gv),
  (exists St1' : Opsem.State,
     Opsem.sop_plus Cfg1 St1 St1' E0 /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := cs;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := updateAddAL (GVsT DGVs) lc id0
                                      ($ gv # t $);
                    Opsem.Allocas := als |} :: EC;
       Opsem.Mem := Mem |}) \/
  (exists St1' : Opsem.State,
     Opsem.sop_star Cfg1 St1 St1' E0 /\
     lt (measure ({| Opsem.ECS := {|
                          Opsem.CurFunction := F;
                          Opsem.CurBB := B;
                          Opsem.CurCmds := cs;
                          Opsem.Terminator := tmn;
                          Opsem.Locals := updateAddAL (GVsT DGVs) lc id0
                                              ($ gv # t $);
                          Opsem.Allocas := als |} :: EC;
                     Opsem.Mem := Mem |}))
        (measure ({| Opsem.ECS := {|
                          Opsem.CurFunction := F;
                          Opsem.CurBB := B;
                          Opsem.CurCmds := insn_load id0 t v align0 :: cs;
                          Opsem.Terminator := tmn;
                          Opsem.Locals := lc;
                          Opsem.Allocas := als |} :: EC;
                     Opsem.Mem := Mem |})) /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := cs;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := updateAddAL (GVsT DGVs) lc id0
                                      ($ gv # t $);
                    Opsem.Allocas := als |} :: EC;
       Opsem.Mem := Mem |}).
Proof.
  intros. subst.
  destruct_ctx_other.
  assert (Heqb1':=Heqb1).
  destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.
  destruct (fdef_dec (PI_f pinfo) F1).
  Case "PI_f pinfo = F1".

    destruct (is_temporary_dec id0 (PI_newids pinfo)).
    SCase "is_temporary".
      apply cmds_simulation_same_tail_inv in Htcmds; eauto.
      destruct Htcmds as [lid [pid [sid [Heq1 [Heq2 [J1 [J2 [J3 J4]]]]]]]];
        subst.
      inv J2.

      right.
      exists 
        {| Opsem.ECS := {|
                    Opsem.CurFunction := PI_f pinfo;
                    Opsem.CurBB := block_intro l1 ps1 (cs11 ++ nil) tmn;
                    Opsem.CurCmds := nil;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := lc1;
                    Opsem.Allocas := als |} :: ECs1;
           Opsem.Mem := Mem |}. simpl.
      split.
      SSCase "opsem".
        constructor.
      split; auto.
      SSCase "sim".
        repeat (split; eauto 2 using cmds_at_block_tail_next).

        apply reg_simulation__updateAddAL_tmp; auto.

        unfold cmds_simulation. simpl in *.
        destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
        rewrite J1 in *.
        destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
        split.
        SSSCase "1".
          intros H3.
          apply app_eq_nil in H3.
          destruct H3; subst.
          split.
          SSSSCase "1.1".
            destruct ((PI_preds pinfo) ! l1) as [[]|];
              destruct ((PI_succs pinfo) ! l1) as [[]|]; try solve [
                auto |
                right; right; split; try solve [auto | intro J; inv J]
              ].
          SSSSCase "1.2".
            intros H3 H5.
            symmetry in H5.
            apply app_eq_nil in H5.
            destruct H5 as [J5 J6].
            rewrite J5 in H3. congruence.
        SSSCase "2".
          split.
          SSSSCase "2.1".
            intros H3.
            destruct ((PI_succs pinfo) ! l1) as [[]|]; auto.
              right; split; try solve [auto | intro J; inv J].
          SSSSCase "2.2".
            intros H3. intros.
            unfold wf_tmp_value. simpl.
            exists mp. exists gv.
            split.
              inv H0.
              assert ((PI_id pinfo) <> lid) as Hneq.
                eapply wf_system__uniqFdef with (f:=PI_f pinfo) in Hwfs; eauto.
                symmetry in J1.
                apply WF_PhiInfo_fresh in J1; auto.
                destruct J1; auto.

              rewrite <- lookupAL_updateAddAL_neq; auto.
            split; auto.
              rewrite lookupAL_updateAddAL_eq.
              erewrite mload_gv2gvs; eauto.

    SCase "isnt_temporary".
      apply cmds_simulation_same_cons_inv in Htcmds; eauto.
      destruct Htcmds as [cs1' [Heq Htcmds]]; subst.
      left.
      exists 
        (Opsem.mkState 
          ((Opsem.mkEC (PI_f pinfo) 
            (block_intro l1 ps1 (cs11 ++ insn_load id0 t v align0 :: cs1') tmn) 
            cs1' tmn (updateAddAL (GVsT DGVs) lc1 id0 ($ gv # t $)) als)
         ::ECs1) Mem).
      split.
      SSCase "opsem".
        apply OpsemProps.sInsn__implies__sop_plus.
        econstructor; eauto.
          erewrite simulation__getOperandValue; eauto.
            eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.
      SSCase "sim".
        repeat (split; eauto 2 using cmds_at_block_tail_next).
        apply reg_simulation__updateAddAL; auto.
        apply cmds_simulation__updateAddAL_neq; auto.
          eapply wf_system__uniqFdef with (f:=PI_f pinfo) in Hwfs; eauto.
          apply WF_PhiInfo_spec10 in HBinF; auto.

  Case "PI_f pinfo <> F1".
    apply cmds_simulation_other_cons_inv in Htcmds; auto.
    destruct Htcmds as [cs1' [Heq Htcmds]]; subst.
    left.
    exists 
      (Opsem.mkState 
        ((Opsem.mkEC F1
          (block_intro l1 ps1 (cs11 ++ insn_load id0 t v align0 :: cs1') tmn)
          cs1' tmn (updateAddAL (GVsT DGVs) lc1 id0 ($ gv # t $)) als)
       ::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_plus.
      econstructor; eauto.
        erewrite simulation__getOperandValue; eauto.
          eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.
    SSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next).
      apply reg_simulation__updateAddAL; auto.
      eapply cmds_simulation_other_stable; eauto.
Qed.

Lemma phinodes_placement_is_correct__dsStore: forall (maxb : Values.block)
  (pinfo : PhiInfo)
  (Cfg1 : OpsemAux.Config) (St1 : Opsem.State) (Hwfpi : WF_PhiInfo pinfo)
  (Hnoalias : wf_State maxb pinfo Cfg1 St1) (S : system) (TD : TargetData)
  (Ps : list product) (F : fdef) (B : block) (lc : Opsem.GVsMap) (gl : GVMap)
  (fs : GVMap) (sid : id) (t : typ) (align0 : align) (v1 v2 : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (als : list mblock) Cfg2
  (EQ : Cfg2 = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := TD;
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := F;
                        Opsem.CurBB := B;
                        Opsem.CurCmds := insn_store sid t v1 v2 align0 :: cs;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: EC;
           Opsem.Mem := Mem |})
  (mp2 : GenericValue) (gv1 : GenericValue) (Mem' : mem) (gvs1 : GVsT DGVs)
  (mps2 : GVsT DGVs) (H : Opsem.getOperandValue TD v1 lc gl = ret gvs1)
  (H0 : Opsem.getOperandValue TD v2 lc gl = ret mps2) (H1 : gv1 @ gvs1)
  (H2 : mp2 @ mps2) (H3 : mstore TD Mem mp2 t gv1 align0 = ret Mem'),
  (exists St1' : Opsem.State,
     Opsem.sop_plus Cfg1 St1 St1' E0 /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := cs;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := lc;
                    Opsem.Allocas := als |} :: EC;
       Opsem.Mem := Mem' |}) \/
  (exists St1' : Opsem.State,
     Opsem.sop_star Cfg1 St1 St1' E0 /\
     lt (measure ({| Opsem.ECS := {|
                          Opsem.CurFunction := F;
                          Opsem.CurBB := B;
                          Opsem.CurCmds := cs;
                          Opsem.Terminator := tmn;
                          Opsem.Locals := lc;
                          Opsem.Allocas := als |} :: EC;
                     Opsem.Mem := Mem' |}))
        (measure ({| Opsem.ECS := {|
                          Opsem.CurFunction := F;
                          Opsem.CurBB := B;
                          Opsem.CurCmds := insn_store sid t v1 v2 align0 :: cs;
                          Opsem.Terminator := tmn;
                          Opsem.Locals := lc;
                          Opsem.Allocas := als |} :: EC;
                     Opsem.Mem := Mem |})) /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := cs;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := lc;
                    Opsem.Allocas := als |} :: EC;
       Opsem.Mem := Mem' |}).
Proof.
  intros. subst.
  destruct_ctx_other.
  assert (Heqb1':=Heqb1).
  destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.
  destruct (fdef_dec (PI_f pinfo) F1).
  Case "PI_f pinfo = F1".

    destruct (is_temporary_dec sid (PI_newids pinfo)).
    SCase "is_temporary".
      apply cmds_simulation_same_head_inv in Htcmds; eauto.
      destruct Htcmds as [l2 [ps2 [tmn1 [lid [pid [sid0 [Heq1 [Heq2
                           [J1 [J2 [J3 J4]]]]]]]]]]]; subst.
      inv J1. inversion Heq1; subst l1 ps1 tmn.
      apply app_inv_tail_nil in H8; subst. simpl.
      right.
      exists 
        {| Opsem.ECS := {|
                    Opsem.CurFunction := PI_f pinfo;
                    Opsem.CurBB := block_intro l2 ps2 cs1 tmn1;
                    Opsem.CurCmds := cs1;
                    Opsem.Terminator := tmn1;
                    Opsem.Locals := lc1;
                    Opsem.Allocas := als |} :: ECs1;
           Opsem.Mem := Mem |}. simpl.
      split.
      SSCase "opsem".
        constructor.
      split; auto.
      SSCase "sim".
        repeat (split; eauto 2 using cmds_at_block_tail_next).

        SSSCase "cs sim".
          assert (NoDup (getBlockLocs B)) as Huniq.
           apply uniqFdef__block_simulation__uniqBlockLocs in Hbsim; auto.
             eapply wf_system__uniqFdef; eauto.

          autounfold with ppbsim in *.
          unfold phinodes_placement_block in Hbsim.
          destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
          destruct Heqb2 as [l2' [ps2' [cs21 Heqb2]]]; subst.
          rewrite Heq2 in *.
          destruct ((PI_preds pinfo) ! l2) as [[]|]; try congruence.
          inv Hbsim.
          assert (cs21 = nil) as EQ.
            clear - H8 Huniq.
            simpl in Huniq.
            simpl_env in Huniq.
            apply NoDup_split in Huniq.
            destruct Huniq as [_ Huniq].
            apply NoDup_split in Huniq.
            destruct Huniq as [_ Huniq].
            apply NoDup_split in Huniq.
            destruct Huniq as [Huniq _].
            rewrite getCmdsLocs_app in Huniq.
            apply infrastructure_props.NoDup_disjoint with (i0:=sid0) in Huniq;
              simpl; auto.
            destruct cs21; auto.
            inv H8.
            contradict Huniq; simpl; auto.

          subst.
          inv H8.
          split.
          SSSSCase "1".
            intros H5.
            split.
            SSSSSCase "1.1".
              right. left. split; auto. intro J; inv J.

            SSSSSCase "1.2".
              intros H6 H7.
              symmetry in H7. apply app_inv_tail_nil in H7. inv H7.

          SSSSCase "2".
            split.
            SSSSSCase "2.1".
              intros H5. congruence.
            SSSSSCase "2.2".
              intros H5 EQ1 EQ2.
              destruct ((PI_succs pinfo) ! l2') as [[]|]; try congruence.
              apply app_eq_nil in EQ2.
              destruct EQ2 as [_ EQ2]. congruence.

        SSSCase "tail sim".
        eapply ECs_simulation_tail_stable; eauto.

        SSSCase "Mem sim".
        destruct Hnoalias as [[[Hnoalias _] _] _].
        destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
        unfold wf_defs in Hnoalias.
        match goal with
        | Hrsim: reg_simulation _ _ ?lc1 ?lc2,
          H: Opsem.getOperandValue _ (value_id (PI_id _)) ?lc2 _ = _ |- _ =>
             assert (G:=H); 
             erewrite <- simulation__getOperandValue with (lc:=lc1) in G; eauto
        end.

          simpl in G.
          apply Hnoalias in G.
          destruct G as [[G _] _].
          eapply mload_mstore_same; eauto.

          destruct_if. apply WF_PhiInfo_spec18; eauto using wf_system__uniqFdef.

    SCase "isnt_temporary".
      apply cmds_simulation_same_cons_inv in Htcmds; eauto.
      destruct Htcmds as [cs1' [Heq Htcmds]]; subst.
      left.
      exists 
        (Opsem.mkState 
          ((Opsem.mkEC (PI_f pinfo) 
            (block_intro l1 ps1 (cs11 ++ insn_store sid t v1 v2 align0 :: cs1') 
              tmn) 
            cs1' tmn lc1 als)
         ::ECs1) Mem').
      split.
      SSCase "opsem".
        apply OpsemProps.sInsn__implies__sop_plus.
        erewrite <- simulation__getOperandValue in H; eauto.
        erewrite <- simulation__getOperandValue in H0; eauto.
        eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.
        eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.

      SSCase "sim".
        repeat (split; eauto 2 using cmds_at_block_tail_next).

        destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
        eapply cmds_simulation_stable; eauto.

        eapply ECs_simulation_tail_stable; eauto.

  Case "PI_f pinfo <> F1".
      apply cmds_simulation_other_cons_inv in Htcmds; eauto.
      destruct Htcmds as [cs1' [Heq Htcmds]]; subst.
      left.
      exists 
        (Opsem.mkState 
          ((Opsem.mkEC F1
            (block_intro l1 ps1 (cs11 ++ insn_store sid t v1 v2 align0 :: cs1')
              tmn)
            cs1' tmn lc1 als)
         ::ECs1) Mem').
      split.
      SSCase "opsem".
        apply OpsemProps.sInsn__implies__sop_plus.
        erewrite <- simulation__getOperandValue in H; eauto.
        erewrite <- simulation__getOperandValue in H0; eauto.
        eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.
        eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.

      SSCase "sim".
        repeat (split; eauto 2 using cmds_at_block_tail_next).

        eapply cmds_simulation_other_stable; eauto.

        eapply ECs_simulation_tail_stable; eauto.
Qed.

Ltac next_state :=
match goal with
| Hrsim: reg_simulation ?pinfo ?F1 ?lc1 ?lc |-
     exists St1' : Opsem.State,
     Opsem.sop_plus _
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := ?F1;
                    Opsem.CurBB := ?B1;
                    Opsem.CurCmds := _ :: ?cs1';
                    Opsem.Terminator := ?tmn;
                    Opsem.Locals := ?lc1;
                    Opsem.Allocas := _ |} :: ?ECs1;
       Opsem.Mem := _ |} St1' _ /\
     State_simulation ?pinfo _ St1' _
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := _;
                    Opsem.CurBB := _;
                    Opsem.CurCmds := _;
                    Opsem.Terminator := _;
                    Opsem.Locals := ?lc;
                    Opsem.Allocas := ?als' |} :: _;
       Opsem.Mem := ?Mem' |} =>
      exists
        (Opsem.mkState
          ((Opsem.mkEC F1 B1 cs1' tmn lc1 als')
         ::ECs1) Mem')

| Hrsim: reg_simulation ?pinfo ?F1 ?lc1 ?lc |-
     exists St1' : Opsem.State,
     Opsem.sop_plus _
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := ?F1;
                    Opsem.CurBB := ?B1;
                    Opsem.CurCmds := _ :: ?cs1';
                    Opsem.Terminator := ?tmn;
                    Opsem.Locals := ?lc1;
                    Opsem.Allocas := _ |} :: ?ECs1;
       Opsem.Mem := _ |} St1' _ /\
     State_simulation ?pinfo _ St1' _
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := _;
                    Opsem.CurBB := _;
                    Opsem.CurCmds := _;
                    Opsem.Terminator := _;
                    Opsem.Locals := updateAddAL (GVsT DGVs) ?lc ?id0 ?gv;
                    Opsem.Allocas := ?als' |} :: _;
       Opsem.Mem := ?Mem' |} =>
      exists
        (Opsem.mkState
          ((Opsem.mkEC F1 B1 cs1' tmn
            (updateAddAL (GVsT DGVs) lc1 id0 gv) als')
         ::ECs1) Mem')

| Hrsim: reg_simulation ?pinfo ?F1 ?lc1 ?lc |-
     exists St1' : Opsem.State,
     Opsem.sop_plus _
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := ?F1;
                    Opsem.CurBB := ?B1;
                    Opsem.CurCmds := _ :: ?cs1';
                    Opsem.Terminator := ?tmn;
                    Opsem.Locals := ?lc1;
                    Opsem.Allocas := _ |} :: ?ECs1;
       Opsem.Mem := _ |} St1' _ /\
     State_simulation ?pinfo _ St1' _
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := _;
                    Opsem.CurBB := _;
                    Opsem.CurCmds := _;
                    Opsem.Terminator := _;
                    Opsem.Locals := (if ?c
                                    then updateAddAL (GVsT DGVs) ?lc ?id0 ?gvs2
                                    else updateAddAL (GVsT DGVs) ?lc ?id0 ?gvs1);
                    Opsem.Allocas := ?als' |} :: _;
       Opsem.Mem := ?Mem' |} =>
      exists
        (Opsem.mkState
          ((Opsem.mkEC F1 B1 cs1' tmn
            (if c
             then updateAddAL (GVsT DGVs) lc1 id0 gvs2
             else updateAddAL (GVsT DGVs) lc1 id0 gvs1) als')
         ::ECs1) Mem')
end.

Ltac solve_step :=
match goal with
| Hrsim: reg_simulation ?pinfo ?F1 ?lc1 ?lc,
  H0: Opsem.getOperandValue _ _ ?lc _ = ret _ |- _ =>
  erewrite <- simulation__getOperandValue in H0; try solve [
    eauto |
    eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto
  ]
end.

Ltac solve_opsem :=
  apply OpsemProps.sInsn__implies__sop_plus; 
  econstructor; try solve [
    eauto |
    match goal with
    | Hrsim: reg_simulation _ _ ?lc1 ?lc2,
      H: Opsem.values2GVs ?td ?idxs ?lc2 ?gl = Some _ |-
         Opsem.values2GVs ?td ?idxs ?lc1 ?gl = Some _ =>
         erewrite values2GVs__simulation;
         try solve [eauto | eapply original_indxs_arent_tmps; eauto]
    end |
    unfold Opsem.BOP, Opsem.FBOP, Opsem.TRUNC, Opsem.EXT, Opsem.CAST,
      Opsem.ICMP, Opsem.FCMP in *;
    inv_mbind';
    symmetry_ctx;
    repeat solve_step;
    repeat match goal with
           | H : Opsem.getOperandValue ?td ?v ?lc ?gl = Some _ |-
             match Opsem.getOperandValue ?td ?v ?lc ?gl with
             | Some _ => _
             | None => _
             end = _ => rewrite H
           end; auto
  ].

Ltac solve_if_rsim :=
  match goal with
  | Hrsim : reg_simulation ?pinfo ?F1 ?lc1 ?lc2 |-
    reg_simulation ?pinfo ?F1
           (if ?c
            then updateAddAL (GVsT DGVs) ?lc1 ?id0 ?gvs2
            else updateAddAL (GVsT DGVs) ?lc1 ?id0 ?gvs1)
           (if ?c
            then updateAddAL (GVsT DGVs) ?lc2 ?id0 ?gvs2
            else updateAddAL (GVsT DGVs) ?lc2 ?id0 ?gvs1) =>
        destruct c;
          apply reg_simulation__updateAddAL; auto
  end.

Ltac solve_other_fun_case :=
match goal with
| n : PI_f ?pinfo <> ?F1,
  Htcmds : cmds_simulation ?pinfo _ _ _ ?F1 _ _ _ |- _ =>
    apply cmds_simulation_other_cons_inv in Htcmds; eauto;
    destruct Htcmds as [cs1' [Heq Htcmds]]; subst;
    next_state;
    split; try solve [
      solve_opsem |
      repeat (split; eauto 2 using cmds_at_block_tail_next); try solve [
        solve_if_rsim |
        apply reg_simulation__updateAddAL; auto |
        eapply cmds_simulation_other_stable; eauto |
        eapply ECs_simulation_tail_stable; eauto]
      ]
end.

Ltac solve_same_fun_ntmp_case :=
match goal with
| e : PI_f ?pinfo = ?F1,
  Htcmds : cmds_simulation ?pinfo _ _ _ ?F1 _ _ _ |- _ =>
    apply cmds_simulation_same_cons_inv in Htcmds; try solve [simpl; eauto];
    destruct Htcmds as [cs1' [Heq Htcmds]]; subst;
    next_state;
    split; try solve [
      solve_opsem |
      repeat (split; eauto 2 using cmds_at_block_tail_next); try solve [
        solve_if_rsim |
        apply reg_simulation__updateAddAL; auto |
        match goal with
        | Heqb2 : exists _, exists _, exists _, ?B = _,
          Hbsim : block_simulation _ _ _ ?B |-
          cmds_simulation _ _ _ _ _ _ _ _ =>
          destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst;
          eapply cmds_simulation_stable;
            eauto using original_ids_in_phi_arent_temporaries
        end |
        eapply ECs_simulation_tail_stable; eauto]
    ]
end.

Ltac phinodes_placement_is_correct__common :=
  destruct_ctx_other;
  match goal with
  | Heqb1 : exists _, exists _, exists _,
                ?B1 = block_intro _ _ (_ ++ ?cs1) ?tmn,
    HBinF : blockInFdefB ?B1 ?F1 = true,
    Hwfpi : WF_PhiInfo ?pinfo,
    Hwfs : wf_system _ |- _ =>
    assert (Heqb1':=Heqb1);
    destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst;
    assert (HwfF := Hwfs);
    eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto;
    destruct (fdef_dec (PI_f pinfo) F1); try solve [
      solve_same_fun_ntmp_case |
      solve_other_fun_case
    ]
  end.

Lemma phinodes_placement_is_correct__dsAlloca: forall (maxb: Values.block)
  (pinfo: PhiInfo)
  (Cfg1 : OpsemAux.Config) (St1 : Opsem.State) (Hwfpi : WF_PhiInfo pinfo)
  (Hnoalias : wf_State maxb pinfo Cfg1 St1) (S : system) (TD : TargetData)
  (Ps : list product) (F : fdef) (B : block) (lc : Opsem.GVsMap) (gl : GVMap)
  (fs : GVMap) (id0 : id) (t : typ) (align0 : align) (v : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (als : list mblock) Cfg2
  (EQ : Cfg2 = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := TD;
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := F;
                        Opsem.CurBB := B;
                        Opsem.CurCmds := insn_alloca id0 t v align0 :: cs;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: EC;
           Opsem.Mem := Mem |})
  (gns : GVsT DGVs) (gn : GenericValue) (Mem' : mem) (tsz : sz) (mb : mblock)
  (H : getTypeAllocSize TD t = ret tsz)
  (H0 : Opsem.getOperandValue TD v lc gl = ret gns)
  (H1 : gn @ gns) (H2 : malloc TD Mem tsz gn align0 = ret (Mem', mb)),
  exists St1' : Opsem.State,
     Opsem.sop_plus Cfg1 St1 St1' E0 /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := cs;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := updateAddAL (GVsT DGVs) lc id0
                                      ($ blk2GV TD mb # typ_pointer t $);
                    Opsem.Allocas := mb :: als |} :: EC;
       Opsem.Mem := Mem' |}.
Proof.
  intros. subst.
  phinodes_placement_is_correct__common.
Qed.

Lemma phinodes_placement_is_correct__dsMalloc: forall (maxb: Values.block)
  (pinfo: PhiInfo)
  (Cfg1 : OpsemAux.Config) (St1 : Opsem.State) (Hwfpi : WF_PhiInfo pinfo)
  (Hnoalias : wf_State maxb pinfo Cfg1 St1) (S : system) (TD : TargetData)
  (Ps : list product) (F : fdef) (B : block) (lc : Opsem.GVsMap) (gl : GVMap)
  (fs : GVMap) (id0 : id) (t : typ) (align0 : align) (v : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (als : list mblock) Cfg2
  (EQ : Cfg2 = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := TD;
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := F;
                        Opsem.CurBB := B;
                        Opsem.CurCmds := insn_malloc id0 t v align0 :: cs;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: EC;
           Opsem.Mem := Mem |})
  (gns : GVsT DGVs) (gn : GenericValue) (Mem' : mem) (tsz : sz) (mb : mblock)
  (H : getTypeAllocSize TD t = ret tsz)
  (H0 : Opsem.getOperandValue TD v lc gl = ret gns)
  (H1 : gn @ gns) (H2 : malloc TD Mem tsz gn align0 = ret (Mem', mb)),
  exists St1' : Opsem.State,
     Opsem.sop_plus Cfg1 St1 St1' E0 /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := cs;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := updateAddAL (GVsT DGVs) lc id0
                                      ($ blk2GV TD mb # typ_pointer t $);
                    Opsem.Allocas := als |} :: EC;
       Opsem.Mem := Mem' |}.
Proof.
  intros. subst.
  phinodes_placement_is_correct__common.
Qed.

Lemma phinodes_placement_is_correct__dsCall: forall (maxb : Values.block)
  (pinfo : PhiInfo) (Cfg1 : OpsemAux.Config) (St1 : Opsem.State)
  (Hwfpi : WF_PhiInfo pinfo) (Hnoalias : wf_State maxb pinfo Cfg1 St1)
  (S : system) (TD : TargetData) (Ps : products) (F : fdef) (B : block)
  (lc : Opsem.GVsMap) (gl : GVMap) (fs : GVMap) (rid : id) (noret0 : noret)
  (ca : clattrs) (fv : value) (lp : params) (cs : list cmd) (tmn : terminator)
  (EC : list Opsem.ExecutionContext) (Mem : mem) (als : list mblock) rt1 va1
  Cfg2
  (EQ : Cfg2 = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := TD;
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := F;
                        Opsem.CurBB := B;
                        Opsem.CurCmds := insn_call rid noret0 ca rt1 va1 fv lp
                                         :: cs;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: EC;
           Opsem.Mem := Mem |})
  (fid : id) (fptrs : GVsT DGVs) (fptr : GenericValue) (lc' : Opsem.GVsMap)
  (l' : l) (ps' : phinodes) (cs' : cmds) (tmn' : terminator) (rt : typ)
  (la : args) (va : varg) (lb : blocks) (fa : fnattrs) (gvs : list (GVsT DGVs))
  (H : Opsem.getOperandValue TD fv lc gl = ret fptrs)
  (H0 : fptr @ fptrs)
  (H1 : OpsemAux.lookupFdefViaPtr Ps fs fptr =
        ret fdef_intro (fheader_intro fa rt fid la va) lb)
  (H2 : getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) =
        ret block_intro l' ps' cs' tmn')
  (H3 : Opsem.params2GVs TD lp lc gl = ret gvs)
  (H4 : Opsem.initLocals TD la gvs = ret lc'),
  exists St1' : Opsem.State,
     Opsem.sop_plus Cfg1 St1 St1' E0 /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := fdef_intro
                                           (fheader_intro fa rt fid la va) lb;
                    Opsem.CurBB := block_intro l' ps' cs' tmn';
                    Opsem.CurCmds := cs';
                    Opsem.Terminator := tmn';
                    Opsem.Locals := lc';
                    Opsem.Allocas := nil |}
                    :: {|
                       Opsem.CurFunction := F;
                       Opsem.CurBB := B;
                       Opsem.CurCmds := insn_call rid noret0 ca rt1 va1 fv lp
                                        :: cs;
                       Opsem.Terminator := tmn;
                       Opsem.Locals := lc;
                       Opsem.Allocas := als |} :: EC;
       Opsem.Mem := Mem |}.
Proof.
  intros. subst.
  destruct_ctx_other.
  assert (Heqb1':=Heqb1).
  destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.
  destruct (fdef_dec (PI_f pinfo) F1).
  SCase "PI_f pinfo = F1".
    assert (Htcmds':=Htcmds).
    apply cmds_simulation_same_cons_inv in Htcmds'; try solve [simpl; eauto].
    destruct Htcmds' as [cs1' [Heq Htcmds']]; subst.

    assert (not_temporaries rid (PI_newids pinfo)) as Hnt.
      eapply WF_PhiInfo_spec11 in HBinF ; eauto.

    assert (if fdef_dec (PI_f pinfo) (PI_f pinfo)
            then value_has_no_tmps pinfo fv else True) as Hntmp.
      eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.
    inv H0.
    eapply lookupFdefViaPtr__simulation with (TD:=(los,nts))(gl:=gl) in H1;
      eauto.
    destruct H1 as [f1 [J1 [J2 J3]]].
    eapply getEntryBlock__simulation in H2; eauto.
    destruct H2 as [[l0 ps0 cs0 tmn0] [Hgetentry1 Hbsim1]].
    assert (
      if fdef_dec (PI_f pinfo) (PI_f pinfo) then
        fold_left
          (fun (acc : Prop) (p : typ * attributes * value) =>
           let '(_, v) := p in value_has_no_tmps pinfo v /\ acc) lp True
      else True) as Hntmp'.
      eapply WF_PhiInfo_spec12; eauto.

    erewrite <- params2GVs__simulation in H3; eauto.
    assert (J3':=J3).
    apply fdef_simulation__inv' in J3'.
    destruct J3' as [lb1' J3']; subst.
    exists
      (Opsem.mkState
        (
         (Opsem.mkEC (fdef_intro (fheader_intro fa rt fid la va) lb1')
           (block_intro l0 ps0 cs0 tmn0)
           cs0 tmn0 lc' nil)
         ::
         (Opsem.mkEC (PI_f pinfo)
           (block_intro l1 ps1
             (cs11 ++ insn_call rid noret0 ca rt1 va1 fv lp :: cs1') tmn)
           (insn_call rid noret0 ca rt1 va1 fv lp :: cs1') tmn lc1 als)
         ::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_plus. 
      econstructor; eauto.

    SSCase "sim".
      assert (Hbsim1':=Hbsim1).
      apply block_simulation__inv in Hbsim1'.
      destruct Hbsim1' as [Heq1 Heq2]; subst; auto.
      assert (
        InProductsB
          (product_fdef (fdef_intro (fheader_intro fa rt fid la va) lb1')) Ps1 =
          true) as Hin.
        eapply OpsemAux.lookupFdefViaPtr_inv; eauto.
      repeat (split; eauto 2 using cmds_at_block_tail_next).
        apply entryBlockInFdef; auto.
        exists l'. exists ps0. exists nil. auto.
        exists l'. exists ps'. exists nil. auto.
        apply reg_simulation_refl.
        eapply entry_cmds_simulation; 
          eauto using wf_system__uniqFdef, wf_system__wf_fdef.

  SCase "PI_f pinfo <> F1".
    assert (Htcmds':=Htcmds).
    apply cmds_simulation_other_cons_inv in Htcmds'; try solve [simpl; eauto].
    destruct Htcmds' as [cs1' [Heq Htcmds']]; subst.
    assert (if fdef_dec (PI_f pinfo) F1
            then value_has_no_tmps pinfo fv else True) as Hntmp.
      destruct (fdef_dec (PI_f pinfo) F1); auto; subst; try congruence.
    inv H0.
    eapply lookupFdefViaPtr__simulation with (TD:=(los,nts))(gl:=gl) in H1;
      eauto.
    destruct H1 as [f1 [J1 [J2 J3]]].
    eapply getEntryBlock__simulation in H2; eauto.
    destruct H2 as [[l0 ps0 cs0 tmn0] [Hgetentry1 Hbsim1]].
    assert (
      if fdef_dec (PI_f pinfo) F1 then
        fold_left
          (fun (acc : Prop) (p : typ * attributes * value) =>
           let '(_, v) := p in value_has_no_tmps pinfo v /\ acc) lp True
      else True) as Hntmp'.
      eapply WF_PhiInfo_spec12; eauto.

    erewrite <- params2GVs__simulation in H3; eauto.
    assert (J3':=J3).
    apply fdef_simulation__inv' in J3'.
    destruct J3' as [lb1' J3']; subst.
    exists
      (Opsem.mkState
        (
         (Opsem.mkEC (fdef_intro (fheader_intro fa rt fid la va) lb1')
           (block_intro l0 ps0 cs0 tmn0)
           cs0 tmn0 lc' nil)
         ::
         (Opsem.mkEC F1
           (block_intro l1 ps1
             (cs11 ++ insn_call rid noret0 ca rt1 va1 fv lp :: cs1') tmn)
           (insn_call rid noret0 ca rt1 va1 fv lp :: cs1') tmn lc1 als)
         ::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_plus. 
      econstructor; eauto.

    SSCase "sim".
      assert (Hbsim1':=Hbsim1).
      apply block_simulation__inv in Hbsim1'.
      destruct Hbsim1' as [Heq1 Heq2]; subst; auto.
      assert (
        InProductsB
          (product_fdef (fdef_intro (fheader_intro fa rt fid la va) lb1')) Ps1 =
          true) as Hin.
        eapply OpsemAux.lookupFdefViaPtr_inv; eauto.
      repeat (split; eauto 2 using cmds_at_block_tail_next).
        apply entryBlockInFdef; auto.
        exists l'. exists ps0. exists nil. auto.
        exists l'. exists ps'. exists nil. auto.
        apply reg_simulation_refl.
        eapply entry_cmds_simulation; 
          eauto using wf_system__uniqFdef, wf_system__wf_fdef.
Qed.

Lemma phinodes_placement_is_correct__dsExCall: forall (maxb : Values.block)
  (pinfo : PhiInfo) (Cfg1 : OpsemAux.Config) (St1 : Opsem.State)
  (Hwfpi : WF_PhiInfo pinfo) (Hnoalias : wf_State maxb pinfo Cfg1 St1)
  (S : system) (TD : TargetData) (Ps : products) (F : fdef) (B : block)
  (lc : Opsem.GVsMap) (gl : GVMap) (fs : GVMap) (rid : id) (noret0 : bool)
  (ca : clattrs) (fv : value) (lp : params) (cs : list cmd) (tmn : terminator)
  (EC : list Opsem.ExecutionContext) (Mem : mem) (als : list mblock)
  rt1 va1 Cfg2
  (EQ : Cfg2 = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := TD;
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := F;
                        Opsem.CurBB := B;
                        Opsem.CurCmds := insn_call rid noret0 ca rt1 va1 fv lp
                                         :: cs;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: EC;
           Opsem.Mem := Mem |})
  (fid : id) (rt : typ) (la : args) (oresult : monad GenericValue) (Mem' : mem)
  (lc' : Opsem.GVsMap) (va : varg) (fa : fnattrs) (gvs : list GenericValue)
  (fptr : GenericValue) (fptrs : GVsT DGVs) (gvss : list (GVsT DGVs))
  (H : Opsem.getOperandValue TD fv lc gl = ret fptrs) (H0 : fptr @ fptrs) dck
  (H1 : OpsemAux.lookupExFdecViaPtr Ps fs fptr =
        ret fdec_intro (fheader_intro fa rt fid la va) dck)
  (H2 : Opsem.params2GVs TD lp lc gl = ret gvss)
  (H3 : gvs @@ gvss) tr
  (H4 : callExternalOrIntrinsics TD gl Mem fid rt (args2Typs la) dck gvs = 
          ret (oresult, tr, Mem'))
  (H5 : Opsem.exCallUpdateLocals TD rt1 noret0 rid oresult lc = ret lc'),
  exists St1' : Opsem.State,
     Opsem.sop_plus Cfg1 St1 St1' tr /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := cs;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := lc';
                    Opsem.Allocas := als |} :: EC;
       Opsem.Mem := Mem' |}.
Proof.
  intros. subst.
  destruct_ctx_other.
  assert (Heqb1':=Heqb1);
  destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.
  eapply simulation__exCallUpdateLocals in H5; eauto.
  destruct H5 as [lc1' [J1 J2]].
  destruct (fdef_dec (PI_f pinfo) F1).
  Case "=".
    apply cmds_simulation_same_cons_inv in Htcmds; try solve [simpl; eauto];
    destruct Htcmds as [cs1' [Heq Htcmds]]; subst.
    exists
      (Opsem.mkState
        ((Opsem.mkEC
           (PI_f pinfo)
           (block_intro l1 ps1
             (cs11 ++ insn_call rid noret0 ca rt1 va1 fv lp :: cs1')
             tmn)
           cs1' tmn lc1' als)::ECs1) Mem').
    split.

      assert (if fdef_dec (PI_f pinfo) (PI_f pinfo)
            then value_has_no_tmps pinfo fv else True) as Hntmp.
        eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.
      inv H0.
      eapply lookupExFdecViaPtr__simulation with (TD:=(los,nts))(gl:=gl)
        (lc1:=lc1)(lc2:=lc) in H1; eauto.
      destruct H1 as [J3 J4].
      apply OpsemProps.sInsn__implies__sop_plus.
      econstructor; eauto.
        erewrite params2GVs__simulation with (lc2:=lc); eauto.
          eapply WF_PhiInfo_spec12; eauto.

      repeat (split; eauto 2 using cmds_at_block_tail_next); try solve [
        solve_if_rsim |
        apply reg_simulation__updateAddAL; auto |
        match goal with
        | Heqb2 : exists _, exists _, exists _, ?B = _,
          Hbsim : block_simulation _ _ _ ?B |-
          cmds_simulation _ _ _ _ _ _ _ _ =>
          destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst;
          eapply cmds_simulation_stable;
            eauto using original_ids_in_phi_arent_temporaries
        end |
        eapply ECs_simulation_tail_stable; eauto].

  Case "<>".
    apply cmds_simulation_other_cons_inv in Htcmds; eauto.
    destruct Htcmds as [cs1' [Heq Htcmds]]; subst.

    exists
      (Opsem.mkState
        ((Opsem.mkEC
           F1
           (block_intro l1 ps1
             (cs11 ++ insn_call rid noret0 ca rt1 va1 fv lp :: cs1')
             tmn)
           cs1' tmn lc1' als)::ECs1) Mem').
    split.

      assert (if fdef_dec (PI_f pinfo) F1
            then value_has_no_tmps pinfo fv else True) as Hntmp.
        destruct (fdef_dec (PI_f pinfo) F1); subst; auto; try congruence.
      inv H0.
      eapply lookupExFdecViaPtr__simulation with (TD:=(los,nts))(gl:=gl)
        (lc1:=lc1)(lc2:=lc) in H1; eauto.
      destruct H1 as [J3 J4].
      apply OpsemProps.sInsn__implies__sop_plus.
      econstructor; eauto.
        erewrite params2GVs__simulation with (lc2:=lc); eauto.
          destruct (fdef_dec (PI_f pinfo) F1); subst; auto; try congruence.

      repeat (split; eauto 2 using cmds_at_block_tail_next); try solve [
        solve_if_rsim |
        apply reg_simulation__updateAddAL; auto |
        eapply cmds_simulation_other_stable; eauto |
        eapply ECs_simulation_tail_stable; eauto].
Qed.

Lemma phinodes_placement_is_bsim : forall maxb pinfo Cfg1 St1 Cfg2 St2 St2' tr
  (Hwfpi: WF_PhiInfo pinfo)
  (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1)
  (Hsim: State_simulation pinfo Cfg1 St1 Cfg2 St2)
  (Hop: Opsem.sInsn Cfg2 St2 St2' tr),
  (exists St1',
    Opsem.sop_plus Cfg1 St1 St1' tr /\    
    State_simulation pinfo Cfg1 St1' Cfg2 St2') \/
  (exists St1',
    Opsem.sop_star Cfg1 St1 St1' tr /\
    lt (measure St2') (measure St2) /\
    State_simulation pinfo Cfg1 St1' Cfg2 St2').
Proof.
  intros.
  (sInsn_cases (induction Hop) Case);
    try apply noalias_State__noalias_EC in Hnoalias.

Case "sReturn".
Focus.
  destruct_ctx_return.
  apply cmds_simulation_nil_inv in Htcmds. subst.
  apply cmds_simulation_non_ldst_cons_inv in Htcmds';
    try solve [
      destruct Heqb1' as [l3 [ps3 [cs3 Heqb1']]]; subst; eauto |
      simpl; auto
    ].
  destruct Htcmds' as [cs1'0 [EQ Htcmds']]; subst.
  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.
  assert (if fdef_dec (PI_f pinfo) F1
          then value_has_no_tmps pinfo Result else True) as Hnontmp.
    apply original_values_arent_tmps with
      (instr:=insn_terminator (insn_return rid RetTy Result))(B:=B1)
      (S:=S1)(m:=module_intro los nts Ps1); 
      simpl; try solve [auto | solve_tmnInFdefBlockB].
  eapply returnUpdateLocals_rsim in H1; eauto.
  destruct H1 as [lc1'' [H1 Hrsim'']].
  left.
  exists 
    (Opsem.mkState ((Opsem.mkEC F1' B1' cs1'0 tmn' lc1'' als')::ECs1) Mem').
  split.
    rewrite <- (@E0_right E0).
    apply OpsemProps.sInsn__implies__sop_plus.
    constructor; auto.

    repeat (split; eauto 2 using cmds_at_block_tail_next).
      destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
      destruct Heqb2' as [l2 [ps2 [cs21 Heqb2']]]; subst.
      eapply cmds_simulation_stable; eauto.
      eapply ECs_simulation_tail_stable; eauto.
Unfocus.

Case "sReturnVoid".
Focus.
  destruct_ctx_return.
  apply cmds_simulation_nil_inv in Htcmds. subst.
  apply cmds_simulation_non_ldst_cons_inv in Htcmds';
    try solve [
      destruct Heqb1' as [l3 [ps3 [cs3 Heqb1']]]; subst; eauto |
      simpl; auto
    ].
  destruct Htcmds' as [cs1'0 [EQ Htcmds']]; subst.
  left.
  exists 
    (Opsem.mkState ((Opsem.mkEC F1' B1' cs1'0 tmn' lc1' als')::ECs1) Mem').
  split.
    rewrite <- (@E0_right E0).
    apply OpsemProps.sInsn__implies__sop_plus.
    constructor; auto.

    repeat (split; eauto 2 using cmds_at_block_tail_next).
      destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
      destruct Heqb2' as [l2 [ps2 [cs21 Heqb2']]]; subst.
      eapply cmds_simulation_stable; eauto.
      eapply ECs_simulation_tail_stable; eauto.
Unfocus.

Case "sBranch". 
  abstract (left; eapply phinodes_placement_is_correct__dsBranch; eauto).
Case "sBranch_uncond". 
  abstract (left; eapply phinodes_placement_is_correct__dsBranch_uncond; eauto). 
Case "sBop". abstract (left; phinodes_placement_is_correct__common).
Case "sFBop". abstract (left; phinodes_placement_is_correct__common).
Case "sExtractValue". abstract (left; phinodes_placement_is_correct__common).
Case "sInsertValue". abstract (left; phinodes_placement_is_correct__common).
Case "sMalloc". abstract (left; phinodes_placement_is_correct__common).
Case "sFree". abstract (left; phinodes_placement_is_correct__common).
Case "sAlloca". abstract (left; phinodes_placement_is_correct__common).
Case "sLoad". abstract (eapply phinodes_placement_is_correct__dsLoad; eauto).
Case "sStore". abstract (eapply phinodes_placement_is_correct__dsStore; eauto).
Case "sGEP". abstract (left; phinodes_placement_is_correct__common).
Case "sTrunc". abstract (left; phinodes_placement_is_correct__common).
Case "sExt". abstract (left; phinodes_placement_is_correct__common).
Case "sCast". abstract (left; phinodes_placement_is_correct__common).
Case "sIcmp". abstract (left; phinodes_placement_is_correct__common).
Case "sFcmp". abstract (left; phinodes_placement_is_correct__common).
Case "sSelect". abstract (left; phinodes_placement_is_correct__common).
Case "sCall". 
  abstract (left; eapply phinodes_placement_is_correct__dsCall; eauto).
Case "sExCall". 
  abstract (left; eapply phinodes_placement_is_correct__dsExCall; eauto).
Qed.

Lemma phinodes_placement_is_bsim' : forall maxb pinfo Cfg1 St1 Cfg2 St2 St2' tr
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hsim: State_simulation pinfo Cfg1 St1 Cfg2 St2)
  (Hop: Opsem.sInsn Cfg2 St2 St2' tr), 
  exists St1',
    Opsem.sop_star Cfg1 St1 St1' tr /\    
    State_simulation pinfo Cfg1 St1' Cfg2 St2'.
Proof.
  intros.
  eapply phinodes_placement_is_bsim in Hsim; eauto.
  destruct Hsim as [[St1' [J1 J2]] | [St1' [J1 [J2 J3]]]].
  exists St1'.
    split; auto.
      apply OpsemProps.sop_plus__implies__sop_star; auto.

    exists St1'.
    split; auto.
Qed.

