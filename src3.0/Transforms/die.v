Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Maps.
Require Import opsem_props.
Require Import primitives.
Require Import memory_sim.
Require Import memory_props.
Require Import program_sim.
Require Import palloca_props.
Require Import top_sim.
Require Import trans_tactic.

Definition pure_cmd (instr:insn) : Prop :=
match instr with
| insn_cmd c =>
  match c with
  | insn_free _ _ _
  | insn_alloca _ _ _ _
  | insn_malloc _ _ _ _
  | insn_store _ _ _ _ _
  | insn_call _ _ _ _ _ _ _ => False
  | _ => True
  end
| _ => False
end.

Record DIInfo := mkDIInfo {
  DI_f : fdef;
  DI_id : id;
  DI_pure : forall instr,
               lookupInsnViaIDFromFdef DI_f DI_id = Some instr ->
               pure_cmd instr;
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

Lemma dont_remove_phinodes: forall (dinfo : DIInfo) (ps1 : phinodes)
  (l1 : l) (cs1 : cmds) (tmn1 : terminator)
  (HBinF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) (DI_f dinfo) = true)
  (H : uniqFdef (DI_f dinfo)),
  ~ In (DI_id dinfo) (getPhiNodesIDs ps1).
Proof.
  intros. intro Hin.
  eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef in Hin; eauto.
  destruct Hin as [p2 [Hin Heq]].
  apply (DI_pure dinfo) in Hin. auto.
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
    intro. subst. 
    eapply dont_remove_phinodes; eauto.
Qed.

(* regsim can also be generalized *)
Lemma reg_simulation_update: forall dinfo F lc1 lc2 id0 gvs,
  reg_simulation dinfo F lc1 lc2 ->
  reg_simulation dinfo F (updateAddAL (GVsT DGVs) lc1 id0 gvs)
    (updateAddAL (GVsT DGVs) lc2 id0 gvs).
Proof.
  unfold reg_simulation.
  intros.
  destruct (fdef_dec (DI_f dinfo) F); subst; intros; auto.
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
      apply reg_simulation_update; auto.

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
    destruct (fdef_dec (DI_f dinfo) F); subst; auto.
      right. eapply dont_remove_phinodes; eauto.
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
    TD lb la2 la1 (gvs:list (GVsT DGVs)) lc1 lc2 lc1' lc2',
  reg_simulation dinfo 
    (fdef_intro (fheader_intro fa0 rt0 fid0 (la1++la2) va0) lb) lc1 lc2 ->
  Opsem._initializeFrameValues TD la2 gvs lc1 = ret lc1' ->
  Opsem._initializeFrameValues TD la2 gvs lc2 = ret lc2' ->
  reg_simulation dinfo 
    (fdef_intro (fheader_intro fa0 rt0 fid0 (la1++la2) va0) lb) lc1' lc2'.
Proof.
  induction la2 as [|[[]]]; simpl; intros.
    uniq_result. auto.

    rewrite_env ((la1 ++ [(t, a, i0)]) ++ la2) in H.
    destruct gvs; inv_mbind''; symmetry_ctx.
      eapply IHla2 in H; eauto.
        apply reg_simulation_update; auto.
        simpl_env in *. auto.

      eapply IHla2 in H; eauto.
        apply reg_simulation_update; auto.
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
  (Hnuse: params_dont_use_did dinfo F lp),
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

Lemma reg_simulation_update_dead: forall (dinfo : DIInfo)
  (lc1 lc2 : Opsem.GVsMap) gv
  (Hlcsim2 : reg_simulation dinfo (DI_f dinfo) lc1 lc2),
  reg_simulation dinfo (DI_f dinfo)
    (updateAddAL (GVsT DGVs) lc1 (DI_id dinfo) gv) lc2.
Proof.
  intros.
  unfold reg_simulation in *.
  destruct (fdef_dec (DI_f dinfo) (DI_f dinfo)); try congruence.
  intros.
  assert (J:=@Hlcsim2 i0). clear Hlcsim2.
  rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma returnUpdateLocals_reg_simulation: forall dinfo F' lc' los nts i0 n
  c t0 v0 v p Result lc gl lc'' lc3 lc''0 lc2 F 
  (Hprop: DI_f dinfo <> F' \/ DI_id dinfo <> i0)
  (Hprop': value_doesnt_use_did dinfo F Result)
  (Hsim: reg_simulation dinfo F' lc' lc3)
  (Hsim': reg_simulation dinfo F lc lc2)
  (Hupdate: Opsem.returnUpdateLocals (los,nts) 
              (insn_call i0 n c t0 v0 v p) Result lc lc' gl = ret lc'')
  (Hupdate': Opsem.returnUpdateLocals (los,nts) 
               (insn_call i0 n c t0 v0 v p) Result lc2 lc3 gl = ret lc''0),
  reg_simulation dinfo F' lc'' lc''0.
Proof.
  intros.
  unfold Opsem.returnUpdateLocals in *.
  inv_mbind'. symmetry_ctx.
  erewrite <- simulation__getOperandValue in HeqR; eauto.
  destruct n; uniq_result; auto.
  inv_mbind'. inv H0.
  apply reg_simulation_update; auto.
Qed.

Lemma exCallUpdateLocals_reg_simulation: forall diinfo F lc1 lc2 lc1' lc2' td
  rt1 noret0 rid oresult0 (Hlcsim2 : reg_simulation diinfo F lc1 lc2)
  (H1: Opsem.exCallUpdateLocals td rt1 noret0 rid oresult0 lc1 = ret lc1')
  (H2: Opsem.exCallUpdateLocals td rt1 noret0 rid oresult0 lc2 = ret lc2'),
  reg_simulation diinfo F lc1' lc2'.
Proof.
  intros.
  unfold Opsem.exCallUpdateLocals in *.
  destruct_if.
    uniq_result. auto.
    inv_mbind; auto.
    inv H1.
    apply reg_simulation_update; auto.
Qed.

Lemma dont_remove_impure_cmd: forall (dinfo : DIInfo) (ps1 : phinodes)
  (l1 : l) (cs1 : cmds) (tmn1 : terminator) F c cs0
  (HBinF : blockInFdefB (block_intro l1 ps1 (cs0++c::cs1) tmn1) F = true)
  (H : uniqFdef F) (Hnok: ~ pure_cmd (insn_cmd c)),
  DI_f dinfo <> F \/ DI_id dinfo <> getCmdLoc c.
Proof.
  intros.
  destruct (fdef_dec (DI_f dinfo) F); subst; auto.
  right.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HBinF; eauto using in_middle.
  intro EQ. rewrite <- EQ in HBinF.
  apply (DI_pure dinfo) in HBinF. auto.
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
  Hsim : State_simulation _ _ _ ?Cfg2 ?St2 ,
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
  Hsim : State_simulation _ _ _ ?Cfg2 ?St2 ,
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

Lemma removable_State_inv': forall F0 ID0 St,
  RemoveSim.removable_State F0 ID0 St ->
  exists F, exists b, exists c, exists cs, exists tmn, exists lc, 
    exists als, exists ECs, exists M,
      St = {| Opsem.ECS := 
                {| Opsem.CurFunction := F;
                   Opsem.CurBB := b;
                   Opsem.CurCmds := c :: cs;
                   Opsem.Terminator := tmn;
                   Opsem.Locals := lc;
                   Opsem.Allocas := als |} :: ECs;
              Opsem.Mem := M |} /\
      F0 = F /\ ID0 = getCmdLoc c.
Proof.
  intros.
  destruct St as [[|[? ? [|] ? ?]] ?]; tinv H.
  apply RemoveSim.removable_State_inv in H. 
  eauto 11.
Qed.

Ltac solve_lookupCmdViaIDFromFdef:=
match goal with
| Huniq: uniqFdef ?f,
  H : blockInFdefB (block_intro _ _ (_++?c::_) _) ?f = true |- 
  lookupInsnViaIDFromFdef ?f (getCmdLoc ?c) = Some (insn_cmd ?c) =>
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef; 
    eauto 1 using in_middle
end.

Ltac repeat_solve :=
  repeat (match goal with
          | |- _ => split; eauto 2 using cmds_at_block_tail_next
          end).

Lemma die_is_sim_removable_state: forall (diinfo : DIInfo) 
  (Cfg1 : OpsemAux.Config) (St1 : Opsem.State) (Cfg2 : OpsemAux.Config)
  (St2 : Opsem.State) (Hwfpp : OpsemPP.wf_State Cfg1 St1)
  (Hsim : State_simulation diinfo Cfg1 St1 Cfg2 St2)
  (Hrem : removable_State diinfo St1) (Hwfcfg: OpsemPP.wf_Config Cfg1)
  (St1' : Opsem.State) (tr1 : trace)
  (Hop1 : Opsem.sInsn Cfg1 St1 St1' tr1),
  State_simulation diinfo Cfg1 St1' Cfg2 St2 /\ tr1 = E0.
Proof.
  intros. 
  apply removable_State_inv' in Hrem.
  destruct Hrem as [F1 [b1 [c1 [cs1 [tmn1 [lc1 [als1 [ECs1 [M1 
     [EQ1 [EQ2 Hdid]]]]]]]]]]]; subst.
  destruct Cfg1 as [S1 TD1 Ps1 gl1 fs1].
  destruct_ctx_other.
  assert (pure_cmd (insn_cmd c1)) as Hpure.
    apply (DI_pure diinfo); auto.
      eapply wf_system__uniqFdef in HFinPs1; eauto 1.
      rewrite Hdid.
      solve_lookupCmdViaIDFromFdef.
  inv Hop1; tinv Hpure;
    abstract (
      simpl in Hdid; subst;
      eapply RemoveSim.cmds_simulation_elim_cons_inv in Hcssim2; eauto;
       repeat_solve; try solve [
         eauto 2 using cmds_at_block_tail_next,
                       reg_simulation_update_dead |
         destruct_if; eauto using reg_simulation_update_dead
       ]
    ).
Qed.

Ltac value_doesnt_use_did_tac :=
match goal with
| |- value_doesnt_use_did ?diinfo _ _ =>
  try solve [
    eapply conditional_used_in_fdef__used_in_tmn_value; 
      destruct diinfo; eauto; simpl; auto |
    eapply conditional_used_in_fdef__used_in_cmd_value; 
      destruct diinfo; eauto 1 using in_middle; simpl; auto
  ]
| |- DI_f ?diinfo <> _ \/
     fold_left
       (fun (re : bool) (p : phinode) => re || used_in_phi (DI_id ?diinfo) p)
       _ false = false =>
  eapply conditional_used_in_fdef__used_in_phis; destruct diinfo; eauto
| |- list_value_doesnt_use_did ?diinfo _ _ =>
    eapply conditional_used_in_fdef__used_in_list_value; 
      destruct diinfo; eauto using in_middle; simpl; auto
end.  

Lemma simulation__values2GVs : forall lc lc2 los nts gl F idxs 
  dinfo (Hprop: list_value_doesnt_use_did dinfo F idxs),
  reg_simulation dinfo F lc lc2 ->
  Opsem.values2GVs (los,nts) idxs lc gl = Opsem.values2GVs (los,nts) idxs lc2 gl.
Proof.
  induction idxs as [|[]]; simpl; intros.
    auto.

    inv_mbind'. symmetry_ctx.
    assert (list_value_doesnt_use_did dinfo F idxs /\
            value_doesnt_use_did dinfo F v) as J.
      unfold list_value_doesnt_use_did in *.
      unfold value_doesnt_use_did in *.
      simpl in Hprop.
      destruct Hprop as [Hprop | Hprop]; auto.
      apply orb_false_iff in Hprop.
      destruct Hprop; auto.
    destruct J as [J1 J2].
    erewrite simulation__getOperandValue; eauto.
    erewrite IHidxs; eauto.
Qed.

Ltac simulation__getOperandValue_tac :=
match goal with
| Hrsim: reg_simulation  _ _ ?lc1 ?lc2,
  H1 : Opsem.values2GVs _ ?idxs ?lc1 _ = ret _,
  H2 : Opsem.values2GVs _ ?idxs ?lc2 _= ret _ |- _ =>
    erewrite simulation__values2GVs in H1; try solve [
      eauto 2 | value_doesnt_use_did_tac
    ];
    rewrite H1 in H2; inv H2; clear H1
| Hrsim: reg_simulation  _ _ ?lc1 ?lc2,
  H1 : Opsem.getOperandValue _ ?v ?lc1 _ = ret _,
  H2 : Opsem.getOperandValue _ ?v ?lc2 _ = ret _ |- _ =>
    erewrite simulation__getOperandValue in H1; try solve [
      eauto 2 | value_doesnt_use_did_tac
    ];
    rewrite H1 in H2; inv H2; clear H1
end.

Ltac die_is_sim_branch := 
  let foo diinfo b1 b2 f1 f2 :=
    assert (block_simulation diinfo f1 b1 b2) as Hbsim; try solve[
      try simulation__getOperandValue_tac;
      try destruct_if; eapply RemoveSim.fdef_sim__block_sim; eauto
    ];
    assert (Hbsim':=Hbsim);
    apply RemoveSim.block_simulation_inv in Hbsim';
    destruct Hbsim' as [Heq1 [Hpssim' [Hcssim' Heq5]]]; subst;
    assert (uniqFdef f1) as Huniq; try solve [eauto using wf_system__uniqFdef]
  in

  destruct_ctx_other;
  match goal with
  | Hcssim2: cmds_simulation _ _ nil _,
    Hop2: Opsem.sInsn _ _ _ _ |- _ =>
    apply RemoveSim.cmds_simulation_nil_inv in Hcssim2; subst;
    inv Hop2;
    uniq_result
  end;

  match goal with
  | H1: Some ?b1 = (if _ then lookupBlockViaLabelFromFdef ?f1 _ else _),
    H2: Some ?b2 = (if _ then lookupBlockViaLabelFromFdef ?f2 _ else _),
    Hfsim: fdef_simulation ?diinfo ?f1 ?f2
   |- _ => foo diinfo b1 b2 f1 f2
  | H1: Some ?b1 = lookupBlockViaLabelFromFdef ?f1 _,
    H2: Some ?b2 = lookupBlockViaLabelFromFdef ?f2 _,
    Hfsim: fdef_simulation ?diinfo ?f1 ?f2
   |- _ => foo diinfo b1 b2 f1 f2
  end;

  match goal with
  | Hfsim: fdef_simulation ?diinfo ?f1 ?f2,
    Hbsim: block_simulation ?diinfo ?f1 ?b1 ?b2,
    Hbsim2: block_simulation ?diinfo ?f1 ?b1' ?b2',
    Hpssim': RemoveSim.phis_simulation _ _ ?f1 _ _,
    _: Opsem.switchToNewBasicBlock _ ?b1 ?b1' _ _ = Some ?lc1',
    _: Opsem.switchToNewBasicBlock _ ?b2 ?b2' _ _ = Some ?lc2'
   |- _ =>
    assert (blockInFdefB b1 f1) as HBinF1'; try solve_blockInFdefB;
    eapply phis_simulation_inv in Hpssim'; eauto 2;
    subst;
    assert (reg_simulation diinfo f1 lc1' lc2') as Hlcsim2'; try solve [
      assert (HBinF1'':=HBinF1');
      eapply wf_system__blockInFdefB__wf_block in HBinF1''; eauto;
      inv HBinF1'';
      eapply switchToNewBasicBlock_rsim in Hbsim2;
        eauto 1; value_doesnt_use_did_tac
    ];
    repeat_solve;
    match goal with
    | |- exists _:_, exists _:_, exists _:_,
         block_intro ?l'0 ?ps'0 ?cs' ?tmn'0 =
         block_intro _ _ (_ ++ ?cs') ?tmn'0 =>
      exists l'0; exists ps'0; exists nil; auto
    end
  end.

Ltac die_is_sim_common_case :=
match goal with
| Hcssim2: cmds_simulation _ _ (_::_) _,
  Hop2: Opsem.sInsn _ _ _ _ |- _ =>
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  unfold Opsem.BOP, Opsem.FBOP, Opsem.TRUNC, Opsem.EXT, Opsem.CAST,
    Opsem.ICMP, Opsem.FCMP, Opsem.GEP in *; 
  inv_mbind; symmetry_ctx;
  repeat simulation__getOperandValue_tac; uniq_result;
  repeat_solve; try solve [
    try destruct_if;
    apply reg_simulation_update; auto
  ]
end.

Lemma die_is_sim : forall diinfo Cfg1 St1 Cfg2 St2
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) (Hwfcfg: OpsemPP.wf_Config Cfg1)
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

Case "removable state". eapply die_is_sim_removable_state; eauto.

Case "unremovable state".
  apply RemoveSim.not_removable_State_inv in Hnrem.
  (sInsn_cases (destruct Hop1) SCase).

SCase "sReturn".
Focus.

  destruct_ctx_return.
  assert (DI_f diinfo <> F' \/ 
          DI_id diinfo <> getCmdLoc (insn_call i0 n c t0 v0 v p))
    as Hneq.
    destruct Heq3' as [l1 [ps1 [cs11 Heq3']]]; subst.
    eapply dont_remove_impure_cmd; eauto 2 using in_middle, wf_system__uniqFdef.
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2'; auto.
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result.
  repeat_solve.
    eapply returnUpdateLocals_reg_simulation with (lc:=lc);
      eauto 1.
      value_doesnt_use_did_tac.

Unfocus.

SCase "sReturnVoid".
Focus.
  destruct_ctx_return.
  assert (DI_f diinfo <> F' \/ 
          DI_id diinfo <> getCmdLoc (insn_call i0 n c t0 v0 v p))
    as Hneq.
    destruct Heq3' as [l1 [ps1 [cs11 Heq3']]]; subst.
    eapply dont_remove_impure_cmd; eauto 2 using in_middle, wf_system__uniqFdef.
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2'; auto.
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result.
  repeat_solve.

Unfocus.

SCase "sBranch". abstract die_is_sim_branch.
SCase "sBranch_uncond". abstract die_is_sim_branch.
SCase "sBop". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sFBop". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sExtractValue". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sInsertValue". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sMalloc". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sFree". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sAlloca". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sLoad". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sStore". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sGEP". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sTrunc". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sExt". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sCast". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sIcmp". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sFcmp". abstract (destruct_ctx_other; die_is_sim_common_case).
SCase "sSelect". abstract (destruct_ctx_other; die_is_sim_common_case).

SCase "sCall".
  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.
  inv Hop2; uniq_result.
  SSCase "SCall".

  simulation__getOperandValue_tac.
  assert (Hfsim1:=Hpsim).
  eapply TopSim.lookupFdefViaPtr__simulation in Hfsim1; eauto. 
  simpl in Hfsim1.
  assert (Hbsim1:=Hfsim1).
  eapply RemoveSim.fdef_simulation__entry_block_simulation in Hbsim1; eauto.
  assert (Hbsim1':=Hbsim1).
  apply RemoveSim.block_simulation_inv in Hbsim1'.
  destruct Hbsim1' as [Heq' [Hpsim1' [Hcsim1' Htsim1']]]; subst.
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
    eapply reg_simulation__initLocals; try solve [
      eauto 2 |
      eapply conditional_used_in_fdef__used_in_params; destruct diinfo; eauto 1
    ].

  SSCase "sExCall".

  simulation__getOperandValue_tac.
  eapply TopSim.lookupFdefViaPtr__simulation_l2r in H1; eauto.
  destruct H1 as [f2 [H1 H2']].
  apply OpsemAux.lookupExFdecViaPtr_inversion in H29.
  apply OpsemAux.lookupFdefViaPtr_inversion in H1.
  destruct H29 as [fn [J1 [J2 J3]]].
  destruct H1 as [fn' [J4 J5]].
  uniq_result.

SCase "sExCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.
  inv Hop2; uniq_result.

  SSCase "SCall".

  simulation__getOperandValue_tac.
  match goal with
  | Hpsim: products_simulation _ ?Ps ?Ps2,
    H1: OpsemAux.lookupExFdecViaPtr ?Ps _ _ = _,
    H30: OpsemAux.lookupFdefViaPtr ?Ps2 _ _ = _ |- _ =>
    clear - H30 H1 Hpsim;
    eapply TopSim.lookupExFdecViaPtr__simulation_l2r in H1; eauto;
    simpl in H1;
    apply OpsemAux.lookupExFdecViaPtr_inversion in H1;
    apply OpsemAux.lookupFdefViaPtr_inversion in H30;
    destruct H1 as [fn [J1 [J2 J3]]];
    destruct H30 as [fn' [J4 J5]]
  end.
  uniq_result.

  SSCase "sExCall".

  simulation__getOperandValue_tac.
  assert (Hlkdec:=Hpsim).
  eapply TopSim.lookupExFdecViaPtr__simulation_l2r in Hlkdec; eauto.

  assert (gvss = gvss0) as EQ.
    inv_mfalse; symmetry_ctx.
    erewrite reg_simulation__params2GVs in H2; eauto.
      uniq_result. auto.
      eapply conditional_used_in_fdef__used_in_params; destruct diinfo; eauto 1.
  subst.
  uniq_result.
  repeat_solve.
    eapply exCallUpdateLocals_reg_simulation; eauto.

Transparent inscope_of_tmn inscope_of_cmd.

Qed.
(* The reg_simulation_update_non_palloca in dae_defs.v may not use to check
   if the updated id is dead or not, refer to the reg_simulation_update in this
   proof. Other lemmas that use it could be simplified too.
*)

