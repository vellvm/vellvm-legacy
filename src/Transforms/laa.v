Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
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
Require Import id_rhs_val.
Require Import palloca_props.
Require Import mem2reg.
Require Import program_sim.

Definition laa (lid: id) (cs2:cmds) (b:block) (pinfo:PhiInfo) : Prop :=         
blockInFdefB b (PI_f pinfo) = true /\
store_in_cmds (PI_id pinfo) cs2 = false /\
let '(block_intro _ _ cs _) := b in
exists cs1, exists cs3,
  cs = 
  cs1 ++ 
  insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo) (PI_align pinfo) :: 
  cs2 ++ 
  insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) (PI_align pinfo) :: 
  cs3.

Record LAAInfo (pinfo: PhiInfo) := mkLAAInfo {
  LAA_lid : id;
  LAA_tail : cmds;
  LAA_block : block;
  LAA_prop : laa LAA_lid LAA_tail LAA_block pinfo
}.

Notation "[! pinfo !]" := 
  (value_const (const_undef (PI_typ pinfo))) (at level 0).

Definition fdef_simulation (pinfo: PhiInfo) (laainfo: LAAInfo pinfo) f1 f2
  : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    subst_fdef (LAA_lid pinfo laainfo) [! pinfo !] f1 = f2
  else f1 = f2.

Definition cmds_simulation (pinfo: PhiInfo) (laainfo: LAAInfo pinfo) (f1:fdef)
  cs1 cs2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    List.map (subst_cmd (LAA_lid pinfo laainfo) [! pinfo !]) cs1 = cs2
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) (laainfo: LAAInfo pinfo) f1 b1 b2
  : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then
    subst_block (LAA_lid pinfo laainfo) [! pinfo !] b1 = b2
  else b1 = b2.

Definition products_simulation (pinfo: PhiInfo) (laainfo: LAAInfo pinfo) Ps1 Ps2
  : Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation pinfo laainfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) (laainfo: LAAInfo pinfo) S1 S2
  : Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation pinfo laainfo Ps1 Ps2
   end) S1 S2.

Definition phis_simulation (pinfo: PhiInfo) (laainfo: LAAInfo pinfo) (f1:fdef)
  ps1 ps2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    List.map (subst_phi (LAA_lid pinfo laainfo) [! pinfo !]) ps1 
      = ps2
  else ps1 = ps2.

Definition tmn_simulation (pinfo: PhiInfo) (laainfo: LAAInfo pinfo) (f1:fdef)
  t t': Prop :=
if (fdef_dec (PI_f pinfo) f1) then 
  subst_tmn (LAA_lid pinfo laainfo) [! pinfo !] t = t'
else t = t'.

Definition EC_simulation (pinfo: PhiInfo) (laainfo: LAAInfo pinfo) 
  (EC1 EC2:@Opsem.ExecutionContext DGVs) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation pinfo laainfo f1 f2 /\
       tmn_simulation pinfo laainfo f1 tmn1 tmn2 /\
       als1 = als2 /\
       block_simulation pinfo laainfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       lc1 = lc2 /\
       cmds_simulation pinfo laainfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (pinfo: PhiInfo) (laainfo: LAAInfo pinfo) 
  (ECs1 ECs2:@Opsem.ECStack DGVs) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation pinfo laainfo EC1 EC2 /\ 
    ECs_simulation pinfo laainfo ECs1' ECs2'
| _, _ => False
end.

Definition State_simulation (pinfo: PhiInfo) (laainfo: LAAInfo pinfo) 
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\ 
    products_simulation pinfo laainfo Ps1 Ps2 /\
    ECs_simulation pinfo laainfo ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2
end.

Lemma laa_is_sim : forall pinfo lasinfo Cfg1 St1 Cfg2 St2 St2' tr2 tr1 St1'
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (HwfS1: id_rhs_val.wf_State (value_id (LAA_lid pinfo lasinfo)) 
           [! pinfo !] (PI_f pinfo) Cfg1 St1)
  (Hsim: State_simulation pinfo lasinfo Cfg1 St1 Cfg2 St2)
  (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2) 
  (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
  State_simulation pinfo lasinfo Cfg1 St1' Cfg2 St2' /\ tr1 = tr2.
Proof.
Admitted.

(*
Local Opaque inscope_of_tmn inscope_of_cmd.

  intros.
  (sInsn_cases (destruct Hop1) Case).

Case "sReturn".

  destruct_ctx_return.

  assert (exists Result2,
    tmn2 = insn_return rid RetTy Result2 /\ 
    value_simulation pinfo lasinfo F Result Result2) as Hreturn.
    clear - Htsim2.
    unfold value_simulation, tmn_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Htsim2; eauto.
  destruct Hreturn as [Result2 [EQ Hvsim2]]; subst.

  inv Hop2.

  match goal with
  | H0 : free_allocas ?td ?M ?las = _,
    H26 : free_allocas ?td ?M ?las = _ |- _ =>
      rewrite H0 in H26; inv H26
  end.
  wfCall_inv.

  assert (lc'' = lc''0) as EQ.
    clear - H27 H1 Hcsim2' Hvsim2 Hinscope1' HwfSystem HmInS Hreach1 HBinF1 
      HFinPs1 Hwfg.
    unfold Opsem.returnUpdateLocals in H1, H27.
    inv_mbind'.
    destruct c1'; tinv H0.
    assert (i0 = i1 /\ n = n0 /\ t0 = t) as EQ.
      unfold cmd_simulation in Hcsim2';
      destruct (fdef_dec (PI_f pinfo) F'); inv Hcsim2'; auto.
    destruct EQ as [Heq1 [Heq2 Heq3]]; subst.
    destruct n0; try solve [inv H0; inv H2; auto].
    destruct t; tinv H0.
    inv_mbind'.
    remember (inscope_of_tmn F
                   (block_intro l3 ps3 (cs3 ++ nil)
                      (insn_return rid RetTy Result))
                   (insn_return rid RetTy Result)) as R.
    destruct R; tinv Hinscope1'.
    symmetry_ctx.
    eapply getOperandValue_inTmnOperands_sim in HeqR0; eauto
      using wf_system__wf_fdef; simpl; auto.
    subst. uniq_result. auto.
    
  subst.
  repeat (split; eauto 2 using cmds_at_block_tail_next).

Case "sReturnVoid".
  destruct_ctx_return.

  assert (tmn2 = insn_return_void rid) as Hreturn.
    clear - Htsim2.
    unfold value_simulation, tmn_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Htsim2; auto.
  subst.

  inv Hop2.

  match goal with
  | H0 : free_allocas ?td ?M ?las = _,
    H26 : free_allocas ?td ?M ?las = _ |- _ =>
      rewrite H0 in H26; inv H26
  end.
  wfCall_inv.
  repeat (split; eauto 2 using cmds_at_block_tail_next).

Case "sBranch".
Focus.

  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.

  assert (exists Cond2,
    tmn2 = insn_br bid Cond2 l1 l2 /\ 
    value_simulation pinfo lasinfo F Cond Cond2) as Hbr.
    clear - Htsim2.
    unfold value_simulation, tmn_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Htsim2; eauto.
  destruct Hbr as [Cond2 [EQ Hvsim2]]; subst.

  inv Hop2.
  uniq_result.
  remember (inscope_of_tmn F (block_intro l3 ps3 (cs31 ++ nil) 
             (insn_br bid Cond l1 l2)) (insn_br bid Cond l1 l2)) as R.
  destruct R; tinv Hinscope1'.

  assert (uniqFdef F) as HuniqF.
    eauto using wf_system__uniqFdef.
  assert (wf_fdef nil S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.
  assert (c = c0)as Heq.
    eapply getOperandValue_inTmnOperands_sim with (v:=Cond)(v':=Cond2); 
      try solve [eauto | simpl; auto].
  subst.
  assert (block_simulation pinfo lasinfo F 
           (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    clear - H22 H1 Hfsim2.
    destruct (isGVZero (los, nts) c0); eauto using fdef_sim__block_sim.
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq [Hpsim' [Hcssim' Htsim']]]; subst.

  assert (isReachableFromEntry F (block_intro l'0 ps' cs' tmn') /\
    In l'0 (successors_terminator (insn_br bid Cond l1 l2)) /\
    blockInFdefB (block_intro l'0 ps' cs' tmn') F = true) as J.
    symmetry in H1.
    destruct (isGVZero (los,nts) c0);
      assert (J:=H1);
      apply lookupBlockViaLabelFromFdef_inv in J; eauto;
      destruct J as [J H13']; subst;
      (repeat split; simpl; auto); try solve [
        auto | eapply reachable_successors; (eauto || simpl; auto)].
  destruct J as [Hreach' [Hsucc' HBinF1']].

  assert (lc' = lc'0) as Heq.
    eapply switchToNewBasicBlock_sim in Hbsim; eauto.
  subst.
  repeat (split; auto).
    exists l'0. exists ps'. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

Unfocus.

Case "sBranch_uncond".
Focus.

  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.

  assert (tmn2 = insn_br_uncond bid l0) as Hbr.
    clear - Htsim2.
    unfold value_simulation, tmn_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Htsim2; eauto.
  subst.

  inv Hop2.
  uniq_result.
  remember (inscope_of_tmn F (block_intro l3 ps3 (cs31 ++ nil) 
             (insn_br_uncond bid l0)) (insn_br_uncond bid l0)) as R.
  destruct R; tinv Hinscope1'.

  assert (uniqFdef F) as HuniqF.
    eauto using wf_system__uniqFdef.
  assert (wf_fdef nil S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.

  assert (block_simulation pinfo lasinfo F 
           (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    clear - H H16 Hfsim2.
    eauto using fdef_sim__block_sim.
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq [Hpsim' [Hcssim' Htsim']]]; subst.

  assert (isReachableFromEntry F (block_intro l'0 ps' cs' tmn') /\
    In l'0 (successors_terminator (insn_br_uncond bid l0)) /\
    blockInFdefB (block_intro l'0 ps' cs' tmn') F = true) as J.
    symmetry in H;
    assert (J:=H);
    apply lookupBlockViaLabelFromFdef_inv in J; eauto;
    destruct J as [J H13']; subst;
    (repeat split; simpl; auto); try solve [
      auto | eapply reachable_successors; (eauto || simpl; auto)].
  destruct J as [Hreach' [Hsucc' HBinF1']].

  assert (lc' = lc'0) as Heq.
    eapply switchToNewBasicBlock_sim in Hbsim; eauto.
  subst.
  repeat (split; auto).
    exists l'0. exists ps'. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

Unfocus.

Case "sBop".

  destruct_ctx_other.
  apply cmds_simulation_cons_inv in Hcssim2.
  destruct Hcssim2 as [c1' [cs3' [Heq [Hcsim2 Hcssim2]]]]; subst.

  assert (exists v1', exists v2',
    c1' = insn_bop id0 bop0 sz0 v1' v2' /\ 
    value_simulation pinfo lasinfo F v1 v1' /\
    value_simulation pinfo lasinfo F v2 v2') as Hcmd.
    clear - Hcsim2.
    unfold value_simulation, cmd_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Hcsim2; eauto.
  destruct Hcmd as [v1' [v2' [Heq [Hvsim1 Hvsim2]]]]; subst.
  inv Hop2.

  assert (wf_fdef nil S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.

  assert (gvs0 = gvs3) as Heq.
    unfold Opsem.BOP in *.
    inv_mbind'; inv_mfalse; app_inv; symmetry_ctx.

    match goal with
    | HeqR : Opsem.getOperandValue _ ?v1 _ _ = ret _, 
      HeqR' : Opsem.getOperandValue _ ?v1' _ _ = ret _, 
      HeqR0 : Opsem.getOperandValue _ ?v2 _ _ = ret _,
      HeqR0' : Opsem.getOperandValue _ ?v2' _ _ = ret _,
      Hvsim1 : value_simulation _ _ _ ?v1 ?v1',
      Hvsim2 : value_simulation _ _ _ ?v2 ?v2' |- _ => 
      eapply getOperandValue_inCmdOperands_sim with (v':=v1') in HeqR; 
        try (eauto || simpl; auto);
      eapply getOperandValue_inCmdOperands_sim with (v':=v2') in HeqR0; 
        try (eauto || simpl; auto);
      subst; uniq_result; auto
    end.

  subst.

  repeat (split; eauto 2 using cmds_at_block_tail_next').

Case "sFBop". admit.
Case "sExtractValue". admit.
Case "sInsertValue". admit.
Case "sMalloc". 

  destruct_ctx_other.
  apply cmds_simulation_cons_inv in Hcssim2.
  destruct Hcssim2 as [c1' [cs3' [Heq [Hcsim2 Hcssim2]]]]; subst.

  assert (exists v',
    c1' = insn_malloc id0 t v' align0 /\ 
    value_simulation pinfo lasinfo F v v') as Hcmd.
    clear - Hcsim2.
    unfold value_simulation, cmd_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Hcsim2; eauto.
  destruct Hcmd as [v' [Heq Hvsim]]; subst.
  inv Hop2.

  assert (wf_fdef nil S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.

  assert (gns = gns0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=v') in H0; 
      try (eauto || simpl; auto).
  subst.
  uniq_result.
  repeat (split; eauto 2 using cmds_at_block_tail_next').

Case "sFree". admit.
Case "sAlloca". admit.
Case "sLoad". admit.
Case "sStore". admit.
Case "sGEP". admit.
Case "sTrunc". admit.
Case "sExt". admit.
Case "sCast". admit.
Case "sIcmp". admit.
Case "sFcmp". admit.
Case "sSelect". admit.
Case "sCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_cons_inv in Hcssim2.
  destruct Hcssim2 as [c1' [cs3' [Heq [Hcsim2 Hcssim2]]]]; subst.

  assert (exists fv', exists lp',
    c1' = insn_call rid noret0 ca ft fv' lp' /\ 
    value_simulation pinfo lasinfo F fv fv' /\
    pars_simulation pinfo lasinfo F lp lp') as Hcmd.
    clear - Hcsim2.
    unfold value_simulation, cmd_simulation, pars_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Hcsim2; eauto.
  destruct Hcmd as [fv' [lp' [Heq [Hvsim Hpasim]]]]; subst.

  assert (wf_fdef nil S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.

  inv Hop2.

  SCase "SCall".

  uniq_result.

  assert (fptr = fptr0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=fv') in H; 
      try (eauto || simpl; auto).
  subst. clear H.

  assert (Hfsim1:=Hpsim).
  eapply lookupFdefViaPtr__simulation in Hfsim1; eauto.

  assert (Hbsim1:=Hfsim1).
  eapply fdef_simulation__entry_block_simulation in Hbsim1; eauto.
  assert (Hbsim1':=Hbsim1).
  apply block_simulation_inv in Hbsim1'.
  destruct Hbsim1' as [Heq' [Hpsim1' [Hcsim1' Htsim1']]]; subst.
  repeat (split; eauto 4).
    exists l'0. exists ps'. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    assert (gvs = gvs0) as EQ.
      inv_mfalse; symmetry_ctx.
      eapply params2GVs_sim; eauto.
    subst.
    clear - H4 H31 Hfsim1.
    apply fdef_simulation_inv in Hfsim1.
    destruct Hfsim1 as [Heq _]. inv Heq. uniq_result.
    auto.

  SCase "sExCall".

  uniq_result.

  assert (fptr = fptr0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=fv') in H; 
      try (eauto || simpl; auto).
  subst. clear H.
  clear - H28 H1 Hpsim.

  eapply lookupFdefViaPtr__simulation_l2r in H1; eauto.
  destruct H1 as [f2 [H1 H2]].
  apply OpsemAux.lookupExFdecViaPtr_inversion in H28.
  apply OpsemAux.lookupFdefViaPtr_inversion in H1.
  destruct H28 as [fn [J1 [J2 J3]]].
  destruct H1 as [fn' [J4 J5]].
  uniq_result.   

Case "sExCall". 

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_cons_inv in Hcssim2.
  destruct Hcssim2 as [c1' [cs3' [Heq [Hcsim2 Hcssim2]]]]; subst.

  assert (exists fv', exists lp',
    c1' = insn_call rid noret0 ca ft fv' lp' /\ 
    value_simulation pinfo lasinfo F fv fv' /\
    pars_simulation pinfo lasinfo F lp lp') as Hcmd.
    clear - Hcsim2.
    unfold value_simulation, cmd_simulation, pars_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Hcsim2; eauto.
  destruct Hcmd as [fv' [lp' [Heq [Hvsim Hpasim]]]]; subst.

  assert (wf_fdef nil S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.

  inv Hop2.

  SCase "SCall".

  uniq_result.

  assert (fptr = fptr0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=fv') in H; 
      try (eauto || simpl; auto).
  subst. clear H.
  clear - H29 H1 Hpsim.

  eapply lookupExFdecViaPtr__simulation_l2r in H1; eauto.
  apply OpsemAux.lookupExFdecViaPtr_inversion in H1.
  apply OpsemAux.lookupFdefViaPtr_inversion in H29.
  destruct H1 as [fn [J1 [J2 J3]]].
  destruct H29 as [fn' [J4 J5]].
  uniq_result.   

  SCase "sExCall".

  uniq_result.

  assert (fptr = fptr0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=fv') in H; 
      try (eauto || simpl; auto).
  subst. clear H.

  assert (Hlkdec:=Hpsim).
  eapply lookupExFdecViaPtr__simulation_l2r in Hlkdec; eauto.

  assert (gvss = gvss0) as EQ.
    inv_mfalse; symmetry_ctx.
    eapply params2GVs_sim; eauto.
  subst.
  uniq_result.

  repeat (split; eauto 2 using cmds_at_block_tail_next').

Transparent inscope_of_tmn inscope_of_cmd.

Qed.
*)

Lemma find_st_ld__laainfo: forall l0 ps0 cs0 tmn0 v cs (pinfo:PhiInfo) dones
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (HBinF : blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true),
  v = [! pinfo !] /\
  exists laainfo:LAAInfo pinfo,
    LAA_lid pinfo laainfo = i1 /\
    LAA_block pinfo laainfo = (block_intro l0 ps0 cs0 tmn0).
Admitted.

Lemma s_genInitState__laa_State_simulation: forall pinfo laainfo S1 S2 main 
  VarArgs cfg2 IS2,
  system_simulation pinfo laainfo S1 S2 ->
  Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2) ->
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo laainfo cfg1 IS1 cfg2 IS2.
Admitted.

Lemma s_isFinialState__laa_State_simulation: forall pinfo laainfo cfg1 FS1 cfg2 
  FS2 r (Hstsim : State_simulation pinfo laainfo cfg1 FS1 cfg2 FS2)
  (Hfinal: s_isFinialState cfg2 FS2 = ret r),
  s_isFinialState cfg1 FS1 = ret r.
Admitted.

Lemma opsem_s_isFinialState__laa_State_simulation: forall 
  pinfo laainfo cfg1 FS1 cfg2 FS2  
  (Hstsim : State_simulation pinfo laainfo cfg1 FS1 cfg2 FS2),
  Opsem.s_isFinialState FS1 = Opsem.s_isFinialState FS2.
Admitted.

Lemma undefined_state__laa_State_simulation: forall pinfo laainfo cfg1 St1 cfg2 
  St2 (Hstsim : State_simulation pinfo laainfo cfg1 St1 cfg2 St2),
  OpsemPP.undefined_state cfg1 St1 -> OpsemPP.undefined_state cfg2 St2.
Admitted.

Lemma sop_star__laa_State_simulation: forall pinfo laainfo cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) 
  (HwfS1: id_rhs_val.wf_State (value_id (LAA_lid pinfo laainfo)) 
           [! pinfo !] (PI_f pinfo) cfg1 IS1)
  (Hstsim : State_simulation pinfo laainfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\ 
    State_simulation pinfo laainfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent cfg1.
  generalize dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    assert (J:=Hwfpp).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]].
      apply opsem_s_isFinialState__laa_State_simulation in Hstsim.
      rewrite Hstsim in Hfinal1.
      contradict H; eauto using s_isFinialState__stuck.

      eapply laa_is_sim in Hstsim; eauto.
      destruct Hstsim as [Hstsim EQ]; subst.
      assert (OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
        admit. (* wf pp *)
      assert (id_rhs_val.wf_State (value_id (LAA_lid pinfo laainfo))
               [! pinfo !] (PI_f pinfo) cfg1 IS1') as HwfS1'.
        admit. (* wf pp *)
      eapply IHHopstar in Hstsim; eauto.
      destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
      exists FS1.
      split; eauto.

      eapply undefined_state__laa_State_simulation in Hstsim; eauto.
      contradict H; eauto using undefined_state__stuck.
Qed.

Lemma sop_div__laa_State_simulation: forall pinfo laainfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) 
  (HwfS1: id_rhs_val.wf_State (value_id (LAA_lid pinfo laainfo)) 
            [! pinfo !] (PI_f pinfo) cfg1 IS1)
  (Hstsim : State_simulation pinfo laainfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Admitted.

Lemma laa_sim: forall (los : layouts) (nts : namedts) (fh : fheader) 
  (dones : list id) (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (v : value)
  (cs : cmds) 
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo) 
  (HwfS : 
     wf_system nil
       [module_intro los nts 
         (Ps1 ++ 
          product_fdef 
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
  program_sim
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))
         :: Ps2)]
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
     main VarArgs.
Proof.
  intros.
  assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true)
    as HBinF.
    rewrite Heq. simpl. apply InBlocksB_middle.
  eapply find_st_ld__laainfo in HBinF; eauto.
  destruct HBinF as [EQ [laainfo [J1 J2]]]; subst.
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation pinfo laainfo
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (subst_fdef (LAA_lid pinfo laainfo) [! pinfo !]
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))
         :: Ps2)]) as Hssim.
    unfold system_simulation.
    constructor; auto.
    repeat split; auto.
    unfold products_simulation.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    apply uniq_products_simulation; auto.
  constructor.
    intros tr t Hconv.
    inv Hconv.
    eapply s_genInitState__laa_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]].    
    assert (OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    assert (id_rhs_val.wf_State (value_id (LAA_lid pinfo laainfo))
              [! pinfo !] (PI_f pinfo) cfg1 IS1) as Hisrhsval.
      eapply s_genInitState__id_rhs_val; eauto.
    eapply sop_star__laa_State_simulation in Hstsim; eauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    eapply s_isFinialState__laa_State_simulation in Hstsim'; eauto.
    econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    eapply s_genInitState__laa_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]].  
    assert (OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    assert (id_rhs_val.wf_State (value_id (LAA_lid pinfo laainfo))
              [! pinfo !] (PI_f pinfo) cfg1 IS1) as Hisrhsval.
      eapply s_genInitState__id_rhs_val; eauto.
    eapply sop_div__laa_State_simulation in Hstsim; eauto.
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
