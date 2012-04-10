Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Maps.
Require Import opsem_props.
Require Import primitives.
Require Import program_sim.
Require Import palloca_props.
Require Import top_sim.
Require Import trans_tactic.

Definition pure_cmd (c:cmd) : Prop :=
match c with
| insn_free _ _ _
| insn_alloca _ _ _ _
| insn_malloc _ _ _ _
| insn_store _ _ _ _ _
| insn_call _ _ _ _ _ _ _ => False
| _ => True
end.

Record DIInfo := mkDIInfo {
  DI_f : fdef;
  DI_id : id;
  DI_pure : forall c,
               lookupInsnViaIDFromFdef DI_f DI_id = Some (insn_cmd c) ->
               pure_cmd c;
  DI_unused : used_in_fdef DI_id DI_f = false
}.

Definition fdef_simulation (diinfo: DIInfo) f1 f2 : Prop :=
RemoveSim.fdef_simulation (DI_f diinfo) (DI_id diinfo) f1 f2.

Definition cmds_simulation (diinfo: DIInfo) (f1:fdef) cs1 cs2 : Prop :=
RemoveSim.cmds_simulation (DI_f diinfo) (DI_id diinfo) f1 cs1 cs2.

Definition block_simulation (diinfo: DIInfo) (f1:fdef) b1 b2 : Prop :=
RemoveSim.block_simulation (DI_f diinfo) (DI_id diinfo) f1 b1 b2.

Definition Fsim (diinfo: DIInfo) := mkFunSim 
(fdef_simulation diinfo)
(RemoveSim.fdef_simulation__eq_fheader (DI_f diinfo) (DI_id diinfo))
(RemoveSim.fdef_simulation__det_right (DI_f diinfo) (DI_id diinfo))
.

Definition products_simulation (diinfo: DIInfo) Ps1 Ps2 : Prop :=
@TopSim.products_simulation (Fsim diinfo) Ps1 Ps2.

Definition system_simulation (diinfo: DIInfo) S1 S2 : Prop :=
@TopSim.system_simulation (Fsim diinfo) S1 S2.

Definition reg_simulation (diinfo: DIInfo) (F1:fdef)
  (lc1 lc2:@Opsem.GVsMap DGVs) : Prop :=
  if (fdef_dec (DI_f diinfo) F1) then
    forall i0, i0 <> DI_id diinfo -> lookupAL _ lc1 i0 = lookupAL _ lc2 i0
  else
    lc1 = lc2.

Definition EC_simulation (diinfo: DIInfo) (EC1 EC2:@Opsem.ExecutionContext DGVs)
  : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1,
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation diinfo f1 f2 /\
       tmn1 = tmn2 /\
       als1 = als2 /\
       block_simulation diinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11,
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       reg_simulation diinfo f1 lc1 lc2 /\
       cmds_simulation diinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (diinfo: DIInfo) (ECs1 ECs2:@Opsem.ECStack DGVs)
  : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' =>
    EC_simulation diinfo EC1 EC2 /\ ECs_simulation diinfo ECs1' ECs2'
| _, _ => False
end.

Definition State_simulation (diinfo: DIInfo)
  (Cfg1:OpsemAux.Config) (St1:Opsem.State)
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\
    products_simulation diinfo Ps1 Ps2 /\
    ECs_simulation diinfo ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2
end.

Definition value_doesnt_use_did dinfo F v :=
  conditional_used_in_value (DI_f dinfo) F (DI_id dinfo) v.

(* go to *)
Ltac destruct_dec :=
match goal with
| |- context [id_dec ?b ?a] =>
  destruct (id_dec b a); subst; try congruence; auto
| _: context [id_dec ?b ?a] |- _ =>
  destruct (id_dec b a); subst; try congruence; auto
| _ : context [productInModuleB_dec ?p1 ?p2] |- _ =>
  destruct (productInModuleB_dec p1 p2); try congruence
end.

Lemma simulation__getOperandValue : forall dinfo lc lc2 los nts  
  gl F v (Hprop: value_doesnt_use_did dinfo F v)
  (Hrsim: reg_simulation dinfo F lc lc2),
  Opsem.getOperandValue (los,nts) v lc gl = 
    Opsem.getOperandValue (los,nts) v lc2 gl.
Proof.
  intros.
  unfold reg_simulation in Hrsim.
  unfold value_doesnt_use_did in Hprop.
  destruct (fdef_dec (DI_f dinfo) F); subst; auto.
    unfold Opsem.getOperandValue in *.
    destruct v; auto.
      destruct Hprop as [Hprop | Hprop]; try congruence.
      simpl in Hprop.
      destruct (id_dec (DI_id dinfo) id5); subst; auto.  
      destruct_dec. inv Hprop.
Qed.

Definition phis_simulation (dinfo: DIInfo) (f1:fdef) ps1 ps2 : Prop :=
RemoveSim.phis_simulation (DI_f dinfo) (DI_id dinfo) f1 ps1 ps2.

Lemma phis_simulation_inv: forall dinfo F ps1 ps2 l1 cs1 tmn1
  (HBinF: blockInFdefB (block_intro l1 ps1 cs1 tmn1) F = true),
  uniqFdef F ->
  phis_simulation dinfo F ps1 ps2 -> ps1 = ps2.
Proof.
  intros.
  eapply RemoveSim.phis_simulation_inv; eauto 1.
    intro. subst. admit. (* phicannot be removed *)
Qed.

(* regsim can also be generalized *)
Lemma reg_simulation_update_non_dead: forall dinfo F lc1 lc2 id0 gvs,
  DI_f dinfo <> F \/ DI_id dinfo <> id0 ->
  reg_simulation dinfo F lc1 lc2 ->
  reg_simulation dinfo F (updateAddAL (GVsT DGVs) lc1 id0 gvs)
    (updateAddAL (GVsT DGVs) lc2 id0 gvs).
Proof.
  unfold reg_simulation.
  intros.
  destruct (fdef_dec (DI_f dinfo) F); subst; intros; auto.
    assert (J:=@H0 i0). clear H0.
    destruct H as [H | H]; try congruence.
    destruct (id_dec id0 i0); subst.
      rewrite lookupAL_updateAddAL_eq; auto.
      rewrite lookupAL_updateAddAL_eq; auto.

      rewrite <- lookupAL_updateAddAL_neq; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_rsim : forall los nts B1 B2 gl F
  lc1' dinfo lc2' ps
  (Hnuse: DI_f dinfo <> F \/ ~ In (DI_id dinfo) (getPhiNodesIDs ps))
  (Hnuse': DI_f dinfo <> F \/
           fold_left
             (fun (re : bool) (p : phinode) => re || used_in_phi (DI_id dinfo) p)
           ps false = false)
  (l3 l0:list (id * GVsT DGVs))
  (HeqR0 : Opsem.getIncomingValuesForBlockFromPHINodes (los,nts) ps B1 gl lc1' =
           ret l3)
  (Hbsim2 : block_simulation dinfo F B1 B2)
  (Hrsim : reg_simulation dinfo F lc1' lc2')
  (HeqR : Opsem.getIncomingValuesForBlockFromPHINodes (los,nts) ps B2 gl lc2' =
          ret l0),
  reg_simulation dinfo F (Opsem.updateValuesForNewBlock l3 lc1')
     (Opsem.updateValuesForNewBlock l0 lc2').
Proof.
  induction ps as [|[i0 ? l0]]; simpl; intros.
    uniq_result. simpl. auto.

    inv_mbind'. symmetry_ctx. simpl.
    assert (DI_f dinfo <> F \/ DI_id dinfo <> i0) as J1.
      clear - Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
    assert (reg_simulation dinfo F
             (Opsem.updateValuesForNewBlock l1 lc1')
             (Opsem.updateValuesForNewBlock l2 lc2')) as J2.
      assert (DI_f dinfo <> F \/ ~ In (DI_id dinfo) (getPhiNodesIDs ps)) as J3.
        clear - Hnuse.
        destruct Hnuse as [Hnuse | Hnuse]; auto.
      assert (DI_f dinfo <> F \/
              fold_left
                (fun (re : bool) (p : phinode) =>
                  re || used_in_phi (DI_id dinfo) p)
                 ps false = false) as J4.
        clear - Hnuse'.
        destruct Hnuse' as [Hnuse' | Hnuse']; auto.
        right.
        assert (J:=Hnuse').
        apply fold_left_eq in J.
          rewrite J in Hnuse'. auto.
          intros. apply orb_false_iff in H. destruct H; auto.
      apply IHps; auto.
    erewrite RemoveSim.block_simulation__getValueViaBlockFromValuels in HeqR3; 
      eauto.
    erewrite simulation__getOperandValue in HeqR0; eauto.
      repeat uniq_result. 
      apply reg_simulation_update_non_dead; auto.

      destruct B2. simpl in HeqR3.
      assert (DI_f dinfo <> F \/ used_in_list_value_l (DI_id dinfo) l0 = false)
        as J3.
        clear - Hnuse'.
        destruct Hnuse' as [Hnuse' | Hnuse']; auto.
        right.
        apply fold_left_eq in Hnuse'; auto.
          intros. apply orb_false_iff in H. destruct H; auto.
      eapply conditional_used_in_getValueViaLabelFromValuels; eauto 1.
Qed.

Lemma switchToNewBasicBlock_rsim : forall los nts l1 l2 ps cs1 cs2 tmn1 tmn2 B1 
  B2 gl lc1 lc2 F dinfo lc1' lc2' 
  (Hnuse': DI_f dinfo <> F \/
           fold_left
             (fun (re : bool) (p : phinode) => re || used_in_phi (DI_id dinfo) p)
           ps false = false)
  (Huniq: uniqFdef F)
  (HBinF: blockInFdefB (block_intro l1 ps cs1 tmn1) F = true)
  (H23 : @Opsem.switchToNewBasicBlock DGVs (los,nts)
          (block_intro l1 ps cs1 tmn1) B1 gl lc1' =
         ret lc1)
  (Hbsim2 : block_simulation dinfo F B1 B2)
  (Hrsim: reg_simulation dinfo F lc1' lc2')
  (H2 : Opsem.switchToNewBasicBlock (los,nts)
         (block_intro l2 ps cs2 tmn2) B2 gl lc2' =
        ret lc2), reg_simulation dinfo F lc1 lc2.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in *. simpl in *.
  inv_mbind'. symmetry_ctx.
  eapply getIncomingValuesForBlockFromPHINodes_rsim; eauto.
    admit. (* phi isnt dead *)
Qed.

Definition list_value_doesnt_use_did dinfo F idxs :=
  conditional_used_in_list_value (DI_f dinfo) F (DI_id dinfo) idxs.

Definition params_dont_use_did dinfo F (ps:params) :=
  conditional_used_in_params (DI_f dinfo) F (DI_id dinfo) ps.

Lemma reg_simulation__params2GVs: forall dinfo F lc1 lc2 gl
  los nts (Hrsim: reg_simulation dinfo F lc1 lc2) 
  lp (Hnuse: params_dont_use_did dinfo F lp),
  Opsem.params2GVs (los,nts) lp lc1 gl =
    Opsem.params2GVs (los,nts) lp lc2 gl.
Proof.
  induction lp as [|[]]; intros; subst; simpl in *.
    auto.

    assert (params_dont_use_did dinfo F lp
             /\ value_doesnt_use_did dinfo F v) as J.
      unfold params_dont_use_did in Hnuse. unfold params_dont_use_did.
      unfold value_doesnt_use_did.
      destruct (fdef_dec (DI_f dinfo) F); subst; auto.
      destruct Hnuse as [Hnuse | Hnuse]; try congruence.
      simpl in Hnuse. assert (J:=Hnuse).
      apply fold_left_eq in Hnuse.
        rewrite Hnuse in J.
        binvf Hnuse as J1 J2.
        split; right; auto.

        intros. destruct b.
        binvf H as J1 J2. auto.
    destruct J as [J1 J2]. 
    erewrite simulation__getOperandValue; eauto.
    rewrite IHlp; auto.
Qed.

Definition args_dont_use_did dinfo F (la:list (typ * attributes * id)) :=
  conditional_used_in_args (DI_f dinfo) F (DI_id dinfo) la.

Lemma reg_simulation__initializeFrameValues: forall dinfo fa0 rt0 fid0 va0
    TD lb la2 la1 (gvs:list (GVsT DGVs)) lc1 lc2 lc1' lc2'
  (Hnuse: args_dont_use_did dinfo
            (fdef_intro (fheader_intro fa0 rt0 fid0 (la1++la2) va0) lb) la2),
  reg_simulation dinfo 
    (fdef_intro (fheader_intro fa0 rt0 fid0 (la1++la2) va0) lb) lc1 lc2 ->
  Opsem._initializeFrameValues TD la2 gvs lc1 = ret lc1' ->
  Opsem._initializeFrameValues TD la2 gvs lc2 = ret lc2' ->
  reg_simulation dinfo 
    (fdef_intro (fheader_intro fa0 rt0 fid0 (la1++la2) va0) lb) lc1' lc2'.
Proof.
  induction la2 as [|[[]]]; simpl; intros.
    uniq_result. auto.

    assert (args_dont_use_did dinfo
       (fdef_intro
          (fheader_intro fa0 rt0 fid0 ((la1 ++ [(t, a, i0)]) ++ la2) va0) lb)
       la2) as J.
      unfold args_dont_use_did. unfold args_dont_use_did in Hnuse.
      simpl_env. simpl_env in Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
      right.
      intros.
      eapply Hnuse; simpl; eauto.

    assert (DI_f dinfo <>
      fdef_intro (fheader_intro fa0 rt0 fid0 (la1 ++ (t, a, i0) :: la2) va0) lb\/
      DI_id dinfo <> i0) as J'.
      unfold args_dont_use_did in Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
      right.
      eapply Hnuse; simpl; eauto.

    rewrite_env ((la1 ++ [(t, a, i0)]) ++ la2) in H.
    destruct gvs; inv_mbind''; symmetry_ctx.
      eapply IHla2 in H; eauto.
        apply reg_simulation_update_non_dead; auto.
        simpl_env in *. auto.

      eapply IHla2 in H; eauto.
        apply reg_simulation_update_non_dead; auto.
        simpl_env in *. auto.
Qed.

Lemma reg_simulation_nil: forall dinfo F, reg_simulation dinfo F nil nil.
Proof.
  unfold reg_simulation.
  intros.
  destruct (fdef_dec (DI_f dinfo) F); subst; auto.
Qed.

Lemma reg_simulation__initLocals: forall dinfo F lc1 lc2 lp gl gvs1 gvs2 lc1'
  lc2' la los nts fa0 rt0 fid0 va0 lb 
  (Hnuse: params_dont_use_did dinfo F lp)
  (Hnuse': args_dont_use_did dinfo
            (fdef_intro (fheader_intro fa0 rt0 fid0 la va0) lb) la),
  reg_simulation dinfo F lc1 lc2 ->
  Opsem.params2GVs (los,nts) lp lc1 gl = ret gvs1 ->
  Opsem.params2GVs (los,nts) lp lc2 gl = ret gvs2 ->
  Opsem.initLocals (los,nts) la gvs1 = ret lc1' ->
  Opsem.initLocals (los,nts) la gvs2 = ret lc2' ->
  reg_simulation dinfo 
    (fdef_intro (fheader_intro fa0 rt0 fid0 la va0) lb) lc1' lc2'.
Proof.
  intros.
  erewrite reg_simulation__params2GVs in H0; eauto. 
  uniq_result.
  unfold Opsem.initLocals in *.
  rewrite_env (nil++la).
  eapply reg_simulation__initializeFrameValues; eauto.
  apply reg_simulation_nil; auto.
Qed.

Ltac destruct_ctx_other :=
match goal with
| Hwfcfg : OpsemPP.wf_Config
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |},
  Hwfpp : OpsemPP.wf_State
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |} _,
  Hsim : State_simulation _ _ _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]];
  destruct Hwfpp as
    [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]]
     [ _ HwfCall'
     ]]
    ]; subst;
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  simpl in Hsim;
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 Hmsim]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim Hstksim];
  unfold EC_simulation in Hecsim;
  destruct Hecsim as
      [Hfsim2 [Heq1 [Halsim2 [Hbsim2
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  assert (Heq3':=Heq3); destruct Heq3' as [l3 [ps1 [cs11 Heq3']]]; subst
end.

Ltac destruct_ctx_return :=
match goal with
| Hwfcfg : OpsemPP.wf_Config
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |},
  Hwfpp : OpsemPP.wf_State
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |} _,
  Hsim : State_simulation _ _ _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]];
  destruct Hwfpp as
    [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]]
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 _]]]
         _
       ]
       HwfCall'
     ]]
    ]; subst;
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  simpl in Hsim;
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 Hmsim]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim Hstksim];
  destruct ECs2 as [|[F3 B3 cs3 tmn3 lc3 als3] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim' Hstksim];
  unfold EC_simulation in Hecsim;
  destruct Hecsim as
      [Hfsim2 [Heq1 [Halsim2 [Hbsim2
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct Hecsim' as
      [Hfsim2' [Heq1' [Halsim2' [Hbsim2'
        [Heq3' [Heq4' [Hlcsim2' Hcssim2']]]]]]]; subst;
  apply RemoveSim.cmds_simulation_nil_inv in Hcssim2; subst;
  wfCall_inv
end.

Definition removable_State (dinfo: DIInfo) (St:@Opsem.State DGVs) : Prop :=
RemoveSim.removable_State (DI_f dinfo) (DI_id dinfo) St.

Lemma die_is_sim : forall diinfo Cfg1 St1 Cfg2 St2
  (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hsim: State_simulation diinfo Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State diinfo St1) St1' tr1
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1),
      State_simulation diinfo Cfg1 St1' Cfg2 St2 /\ tr1 = E0) /\
  (forall (Hnrem: ~removable_State diinfo St1) St1' St2' tr1 tr2
     (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2)
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1),
     State_simulation diinfo Cfg1 St1' Cfg2 St2' /\ tr1 = tr2).
Proof.

Local Opaque inscope_of_tmn inscope_of_cmd.

  intros.
  split; intros.
(*
Case "removable state". eapply dae_is_sim_removable_state; eauto.

Case "unremovable state".
  apply RemoveSim.not_removable_State_inv in Hnrem.
  (sInsn_cases (destruct Hop1) SCase).

SCase "sReturn".
Focus.

  destruct_ctx_return.
  assert (PI_f pinfo <> F' \/ PI_id pinfo <> getCmdLoc (insn_call i0 n c t0 v0 v p))
    as Hneq.
    WF_PhiInfo_spec10_tac.
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2'; auto.
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result.
  eapply free_allocas_return_sim in Hmsim; eauto.
  exists mi.
  repeat_solve.
    eapply returnUpdateLocals_als_simulation; eauto.

    eapply returnUpdateLocals_reg_simulation with (lc:=lc);
      eauto using mem_simulation__wf_sb_sim;
      try solve [get_wf_value_for_simop'; eauto].
      eapply conditional_used_in_fdef__used_in_tmn_value; eauto; simpl; auto.

Unfocus.

SCase "sReturnVoid".
Focus.
  destruct_ctx_return.
  assert (PI_f pinfo <> F' \/ PI_id pinfo <> getCmdLoc (insn_call i0 n c t0 v0 v p))
    as Hneq.
    WF_PhiInfo_spec10_tac.
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2'; auto.
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result.
  eapply free_allocas_return_void_sim in Hmsim; eauto.
  exists mi.
  repeat_solve.

Unfocus.

SCase "sBranch".
Focus.
  destruct_ctx_other.
  apply RemoveSim.cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    destruct Hmsim as [_ [_ Hwf_mi]].
    eapply simulation__getOperandValue in Hlcsim2;
      try solve [get_wf_value_for_simop'; eauto 2].
      erewrite simulation__isGVZero in H1; eauto.
      clear - H22 H1 Hfsim2.
      destruct (isGVZero (los, nts) c0); 
        eapply RemoveSim.fdef_sim__block_sim; eauto.

      eapply conditional_used_in_fdef__used_in_tmn_value; eauto; simpl; auto.

  assert (Hbsim':=Hbsim).
  apply RemoveSim.block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq1 [Hpssim' [Hcssim' Heq5]]]; subst.

  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  assert (blockInFdefB (block_intro l'0 ps' cs' tmn'0) F) as HBinF1'.
    solve_blockInFdefB.
  eapply phis_simulation_inv in Hpssim'; eauto 2.
  subst.

  assert (reg_simulation pinfo mi F lc' lc'0) as Hlcsim2'.
    assert (HBinF1'':=HBinF1').
    eapply wf_system__blockInFdefB__wf_block in HBinF1''; eauto.     
    inv HBinF1''.
    eapply switchToNewBasicBlock_rsim in Hbsim2;
      eauto using mem_simulation__wf_sb_sim, conditional_used_in_fdef__used_in_phis.
  assert (als_simulation pinfo mi F lc' als als2) as Halsim2'.
    eapply switchToNewBasicBlock_asim; eauto.
  exists mi.
  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    destruct Hmsim as [J1 [J2 J3]].
    split; auto.
    split; auto.
      intros blk J.
      apply J2.
      intro J4. apply J.
      simpl.
      eapply switchToNewBasicBlock_isnt_alloca_in_ECs; eauto; simpl; eauto.
Unfocus.

SCase "sBranch_uncond".
Focus.
  destruct_ctx_other.
  apply RemoveSim.cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    eapply RemoveSim.fdef_sim__block_sim; eauto.
  assert (Hbsim':=Hbsim).
  apply RemoveSim.block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq1 [Hpssim' [Hcssim' Heq5]]]; subst.

  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  assert (blockInFdefB (block_intro l'0 ps' cs' tmn'0) F) as HBinF1'.
    solve_blockInFdefB.
  eapply phis_simulation_inv in Hpssim'; eauto 2.
  subst.

  assert (reg_simulation pinfo mi F lc' lc'0) as Hlcsim2'.
    assert (HBinF1'':=HBinF1').
    eapply wf_system__blockInFdefB__wf_block in HBinF1''; eauto.     
    inv HBinF1''.
    eapply switchToNewBasicBlock_rsim in Hbsim2;
      eauto using mem_simulation__wf_sb_sim, conditional_used_in_fdef__used_in_phis.
  assert (als_simulation pinfo mi F lc' als als2) as Halsim2'.
    eapply switchToNewBasicBlock_asim; eauto.
  exists mi.
  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    destruct Hmsim as [J1 [J2 J3]].
    split; auto.
    split; auto.
      intros blk J.
      apply J2.
      intro J4. apply J. simpl.
      eapply switchToNewBasicBlock_isnt_alloca_in_ECs; eauto; simpl; eauto.
Unfocus.

SCase "sBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExtractValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sInsertValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sMalloc".
  abstract (destruct_ctx_other;
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  eapply simulation__getOperandValue with (lc2:=lc2) in H0;
    try simulation__getOperandValue_tac1;
  eapply mem_simulation__malloc in Hmsim; eauto 2; simpl in Hmsim;
  destruct Hmsim as [mi' [Hmsim [Hinc [Hprop1 Hprop2]]]];
  exists mi';
  repeat_solve; try solve [
    eapply als_simulation__malloc; eauto | 
    eapply reg_simulation__malloc; eauto |
    eapply inject_incr__preserves__ECs_simulation; 
      try solve [eauto | eapply malloc__isnt_alloca_in_ECs; eauto] |
    eapply OpsemAux.inject_incr__preserves__ftable_simulation; eauto
  ]).

SCase "sFree".
  abstract (destruct_ctx_other;
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  eapply simulation__getOperandValue with (lc2:=lc2) in H;
    try simulation__getOperandValue_tac1;
  eapply mem_simulation__free in Hmsim; eauto 2;
  exists mi;
  repeat_solve).

SCase "sAlloca".
  abstract (destruct_ctx_other;
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  eapply simulation__getOperandValue with (lc2:=lc2) in H0;
    try simulation__getOperandValue_tac1;
  eapply mem_simulation__malloc in Hmsim; eauto 2; simpl in Hmsim;
  destruct Hmsim as [mi' [Hmsim [Hinc [Hprop1 Hprop2]]]];
  exists mi';
  repeat_solve; try solve [
    eapply als_simulation__alloca; eauto | 
    eapply reg_simulation__malloc; eauto |
    eapply inject_incr__preserves__ECs_simulation; 
      try solve [eauto | eapply malloc__isnt_alloca_in_ECs; eauto] |
    eapply OpsemAux.inject_incr__preserves__ftable_simulation; eauto
  ]).

SCase "sLoad".
  abstract (destruct_ctx_other;
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  exists mi;
  repeat_solve; try solve [
    apply als_simulation_update_lc; auto |
    apply reg_simulation_update_non_palloca; try solve [
      auto |
      eapply simulation__mload; try solve [
        eauto 2 using mem_simulation__wf_sb_sim |
        simulation__getOperandValue_tac2
      ]
    ] |
    eapply mem_simulation__update_non_palloca; eauto; simpl; eauto
  ]).

SCase "sStore".
  abstract (destruct_ctx_other;
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  exists mi;
  repeat_solve; try solve [
    simpl; eapply simulation__mstore; try solve [
      eauto 2 using mem_simulation__wf_sb_sim |
      eapply simulation__getOperandValue; eauto using mem_simulation__wf_sb_sim;
        try solve [eapply conditional_used_in_fdef__used_in_cmd_value;
                     eauto using in_middle; simpl; auto |
                   get_wf_value_for_simop; eauto]
    ]
  ]).

SCase "sGEP". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sTrunc". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExt". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sCast". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sIcmp". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFcmp". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sSelect".
  destruct_ctx_other.
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.
  exists mi.
  repeat_solve.
    destruct (isGVZero (los,nts) c);
      apply als_simulation_update_lc; auto.
    erewrite simulation__isGVZero with (c':=c0);
      simulation__getOperandValue_tac2.
    destruct (isGVZero (los,nts) c0);
      apply reg_simulation_update_non_palloca; eauto; try solve [
        eapply simulation__getOperandValue;
        eauto using mem_simulation__wf_sb_sim;
        try solve [eapply conditional_used_in_fdef__used_in_cmd_value;
                     eauto using in_middle; simpl; auto|
                   get_wf_value_for_simop; eauto]
      ].
    destruct (isGVZero (los,nts) c);
      eapply mem_simulation__update_non_palloca; eauto; simpl; eauto.

SCase "sCall".
  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.
  inv Hop2; uniq_result.
  SSCase "SCall".

  assert (gv_inject mi fptr fptr0) as Hfptr_sim.
    assert (exists t, wf_value S (module_intro los nts Ps) F fv t) as G.
      assert (HBinF1':=HBinF1).
      eapply wf_system__wf_cmd in HBinF1'; eauto using in_middle.     
      inv HBinF1'. eauto.
    destruct G.
    simulation__getOperandValue_tac2.

  assert (Hfsim1:=Hpsim).
  eapply TopSim.lookupFdefViaPtr_inj__simulation in Hfsim1; eauto. 
  simpl in Hfsim1.
  assert (Hbsim1:=Hfsim1).
  eapply RemoveSim.fdef_simulation__entry_block_simulation in Hbsim1; eauto.
  assert (Hbsim1':=Hbsim1).
  apply RemoveSim.block_simulation_inv in Hbsim1'.
  destruct Hbsim1' as [Heq' [Hpsim1' [Hcsim1' Htsim1']]]; subst.
  exists mi.
    match goal with
    | H1: OpsemAux.lookupFdefViaPtr _ _ _ = Some ?F,
      _ : fdef_simulation _ ?F _ |- _ =>
      apply OpsemAux.lookupFdefViaPtr_inv in H1;
      eapply wf_system__uniqFdef in H1; eauto 2
    end.
  repeat_solve.
    exists l'0. exists ps'. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    apply RemoveSim.fdef_simulation_inv in Hfsim1.
    destruct Hfsim1 as [Hfhsim1 Hbssim1].
    inv Hfhsim1.
    assert (HBinF1':=HBinF1).
    eapply wf_system__wf_cmd in HBinF1'; eauto using in_middle.     
    inv HBinF1'.
    find_wf_value_list.  
    eapply reg_simulation__initLocals; try solve [
      eauto 2 using mem_simulation__wf_sb_sim, WF_PhiInfo__args_dont_use_pid |
      eapply conditional_used_in_fdef__used_in_params; eauto 1
    ].

    destruct Hmsim as [Hmsim1 [Hmsim2 Hmsim3]].
    split; auto.
    split; auto.
      intros blk J.
      apply Hmsim2.
      intro G. apply J.
      unfold isnt_alloca_in_ECs in *.
      intros. simpl in Hin.
      destruct Hin as [Hin | Hin].
        subst. simpl.
        inv Hin. eapply WF_PhiInfo__isnt_alloca_in_EC; eauto.

        apply G. simpl. auto.

  SSCase "sExCall".

  assert (gv_inject mi fptr fptr0) as Hfptr_sim.
    assert (exists t, wf_value S (module_intro los nts Ps) F fv t) as G.
      assert (HBinF1':=HBinF1).
      eapply wf_system__wf_cmd in HBinF1'; eauto using in_middle.     
      inv HBinF1'. eauto.
    destruct G.
    simulation__getOperandValue_tac2.

  eapply TopSim.lookupFdefViaPtr_inj__simulation_l2r in H1; eauto.
  uniq_result.

SCase "sExCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.
  inv Hop2; uniq_result.

  SSCase "SCall".

  assert (gv_inject mi fptr fptr0) as Hfptr_sim.
    assert (exists t, wf_value S (module_intro los nts Ps) F fv t) as G.
      assert (HBinF1':=HBinF1).
      eapply wf_system__wf_cmd in HBinF1'; eauto using in_middle.     
      inv HBinF1'. eauto.
    destruct G.
    simulation__getOperandValue_tac2.

  eapply TopSim.lookupFdefViaPtr_inj__simulation_r2l in H1; eauto.
  uniq_result.

  SSCase "sExCall".

  assert (gv_inject mi fptr fptr0) as Hfptr_sim.
    assert (exists t, wf_value S (module_intro los nts Ps) F fv t) as G.
      assert (HBinF1':=HBinF1).
      eapply wf_system__wf_cmd in HBinF1'; eauto using in_middle.     
      inv HBinF1'. eauto.
    destruct G.
    simulation__getOperandValue_tac2.

  eapply TopSim.lookupExFdecViaPtr_inj__simulation in Hfptr_sim; eauto.
  uniq_result.

  match goal with | H1 : fdec_intro _ _ = fdec_intro _ _ |- _ => inv H1 end.
  assert (List.Forall2 (fun gv1 => fun gv2 => gv_inject mi gv1 gv2) gvss gvss0)
    as Hparsim.
    assert (HBinF1':=HBinF1).
    eapply wf_system__wf_cmd in HBinF1'; eauto using in_middle.     
    inv HBinF1'.
    find_wf_value_list.  
    eapply reg_simulation__params2GVs; try solve [
      eauto 2 using mem_simulation__wf_sb_sim |
      eapply conditional_used_in_fdef__used_in_params; eauto 1
    ].
  eapply callExternalFunction__mem_simulation in Hmsim; eauto.
  destruct Hmsim as [EQ' [EQ [mi' [Hmsim [Hinc [J1 [J2 J3]]]]]]]; subst.
  exists mi'.
  repeat_solve.
    eapply inject_incr__preserves__ECs_simulation; eauto.
    eapply OpsemAux.inject_incr__preserves__ftable_simulation; eauto.

Transparent inscope_of_tmn inscope_of_cmd.

Qed.
*)
Admitted.

Lemma s_genInitState__die_State_simulation:
  forall diinfo S1 S2 main VarArgs cfg2 IS2,
  system_simulation diinfo S1 S2 ->
  Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2) ->
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation diinfo cfg1 IS1 cfg2 IS2.
Admitted.

Lemma s_isFinialState__die_State_simulation_l2r:
  forall diinfo cfg1 FS1 cfg2 FS2 r
  (Hstsim : State_simulation diinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 = ret r),
  Opsem.s_isFinialState cfg2 FS2 = ret r.
Admitted.

Lemma s_isFinialState__die_State_simulation_l2r':
  forall diinfo cfg1 FS1 cfg2 FS2
  (Hstsim : State_simulation diinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 <> None),
  Opsem.s_isFinialState cfg2 FS2 <> None.
Admitted.

Lemma s_isFinialState__die_State_simulation_r2l:
  forall diinfo cfg1 FS1 cfg2 FS2 r
  (Hstsim : State_simulation diinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r),
  exists FS1', 
    Opsem.sop_star cfg1 FS1 FS1' E0 /\
    State_simulation diinfo cfg1 FS1' cfg2 FS2 /\
    Opsem.s_isFinialState cfg1 FS1' = ret r.
Admitted.

Lemma s_isFinialState__die_State_simulation_None_r2l:
  forall diinfo cfg1 FS1 cfg2 FS2
  (Hstsim : State_simulation diinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = None),
  Opsem.s_isFinialState cfg1 FS1 = None.
Admitted.

Lemma undefined_state__die_State_simulation_r2l: forall diinfo cfg1 St1 cfg2
  St2 (Hstsim : State_simulation diinfo cfg1 St1 cfg2 St2),
  OpsemPP.undefined_state cfg2 St2 -> OpsemPP.undefined_state cfg1 St1.
Admitted.

Lemma undefined_state__die_State_simulation_l2r: forall diinfo cfg1 St1 cfg2
  St2 (Hstsim : State_simulation diinfo cfg1 St1 cfg2 St2),
  OpsemPP.undefined_state cfg1 St1 -> OpsemPP.undefined_state cfg2 St2.
Admitted.

Lemma sop_star__die_State_simulation: forall diinfo cfg1 IS1 cfg2 IS2 tr FS2 
  (Hwfcfg: OpsemPP.wf_Config cfg1) (Hwfpp: OpsemPP.wf_State cfg1 IS1) 
  (Hstsim : State_simulation diinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\
    State_simulation diinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    assert (J:=Hwfpp).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]].
      eapply s_isFinialState__die_State_simulation_l2r' in Hstsim; eauto 1.
      contradict H; eauto using s_isFinialState__stuck.

      assert (OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
        apply OpsemPP.preservation in Hop1; auto.
      eapply die_is_sim in Hstsim; eauto.
      destruct Hstsim as [Hstsim1 Hstsim2].
      destruct (@RemoveSim.removable_State_dec 
          (DI_f diinfo) (DI_id diinfo) IS1) as [Hrm | Hnrm].
        eapply Hstsim1 in Hrm; eauto.
        destruct Hrm as [Hstsim EQ]; subst.
        admit. (* we should do induction on the measure of State_simulation *)

        eapply Hstsim2 in Hnrm; eauto.
        destruct Hnrm as [Hstsim EQ]; subst.
        eapply IHHopstar in Hstsim; eauto.
        destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
        exists FS1.
        split; eauto.

      eapply undefined_state__die_State_simulation_l2r in Hstsim; eauto.
      contradict H; eauto using undefined_state__stuck.
Qed.

Lemma sop_div__die_State_simulation: forall diinfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpp: OpsemPP.wf_State cfg1 IS1)
  (Hstsim : State_simulation diinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Admitted.

Lemma die_wfS: forall id0 f diinfo los nts Ps1 Ps2
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq1: f = DI_f diinfo) (Heq2: id0 = DI_id diinfo),
  wf_system 
    [module_intro los nts (Ps1 ++  product_fdef (remove_fdef id0 f) :: Ps2)].
Admitted.

Lemma die_sim: forall id0 f diinfo los nts Ps1 Ps2 main VarArgs
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hok: defined_program [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] 
          main VarArgs)
  (Heq1: f = DI_f diinfo) (Heq2: id0 = DI_id diinfo),
  program_sim
    [module_intro los nts
      (Ps1 ++  product_fdef (remove_fdef id0 f) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Proof.
  intros. subst.
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation diinfo
    [module_intro los nts (Ps1 ++ product_fdef (DI_f diinfo) :: Ps2)]
    [module_intro los nts
      (Ps1 ++ product_fdef (remove_fdef (DI_id diinfo) (DI_f diinfo)) :: Ps2)])
    as Hssim.
    constructor; auto.
    repeat split; auto.    
    unfold TopSim.products_simulation. simpl. unfold system_simulation.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    apply uniq_products_simulation; auto.

  constructor; auto.
    intros tr t Hconv.
    inv Hconv.
    eapply s_genInitState__die_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit1 Hstsim]]].    
    assert (OpsemPP.wf_Config cfg1 /\ OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    eapply sop_star__die_State_simulation in Hstsim; eauto; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    eapply s_isFinialState__die_State_simulation_r2l in Hstsim'; eauto.
    destruct Hstsim' as [FS1' [Hopstar1' [Hstsim'' Hfinal]]].
    assert (Opsem.sop_star cfg1 IS1 FS1' tr) as Hopstar1''.
      rewrite <- E0_right.
      eapply OpsemProps.sop_star_trans; eauto.
    exists t. split; auto using result_match_relf. econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    eapply s_genInitState__die_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]].
    assert (OpsemPP.wf_State cfg1 IS1) as Hwfst.
      eapply s_genInitState__opsem_wf; eauto.
    eapply sop_div__die_State_simulation in Hstsim; eauto.
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.

    intros tr t Hgowrong.
    inv Hgowrong.
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg t) as HwfSt.
      eapply s_genInitState__opsem_wf in H; eauto using die_wfS.
      destruct H as [Hcfg2 HwfSt2].
      apply OpsemPP.preservation_star in H0; auto.
    assert (OpsemPP.undefined_state cfg t) as Hundef.
      apply stuck__undefined_state in H2; try solve [auto | tauto].
    eapply s_genInitState__die_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]].
    assert (OpsemPP.wf_Config cfg1 /\ OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    eapply sop_star__die_State_simulation in Hstsim; eauto; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    assert (OpsemPP.undefined_state cfg1 FS1) as Hundef'.
      eapply undefined_state__die_State_simulation_r2l in Hundef; 
        try solve [eauto | tauto].
    assert (Opsem.s_isFinialState cfg1 FS1 = merror) as Hfinal'.
      eapply s_isFinialState__die_State_simulation_None_r2l in H2; 
        try solve [eauto | tauto].
    apply undefined_state__stuck' in Hundef'.
    exists tr. exists FS1.
    econstructor; eauto.
Qed.

Lemma subst_fdef__diinfo: forall f id0 v0,
  exists diinfo:DIInfo, DI_f diinfo = subst_fdef id0 v0 f /\ DI_id diinfo = id0.
Admitted.

Lemma die_wfPI: forall id0 f diinfo los nts Ps1 Ps2 pinfo
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq1: f = DI_f diinfo) (Heq2: id0 = DI_id diinfo) (Heq3: f = PI_f pinfo),
  WF_PhiInfo (update_pinfo pinfo (remove_fdef id0 f)).
Admitted.

Lemma remove_successors : forall f id',
  successors f = successors (remove_fdef id' f).
Admitted.

Lemma remove_reachablity_analysis : forall f id',
  reachablity_analysis f = reachablity_analysis (remove_fdef id' f).
Admitted.

