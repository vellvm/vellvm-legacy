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

Definition pure_cmd (c:cmd) : Prop :=
match c with
| insn_alloca _ _ _ _
| insn_malloc _ _ _ _
| insn_store _ _ _ _ _
| insn_call _ _ _ _ _ _ => False
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
  if (fdef_dec (DI_f diinfo) f1) then remove_fdef (DI_id diinfo) f1 = f2
  else f1 = f2.

Definition cmds_simulation (diinfo: DIInfo) (f1:fdef) cs1 cs2 : Prop :=
  if (fdef_dec (DI_f diinfo) f1) then remove_cmds (DI_id diinfo) cs1 = cs2
  else cs1 = cs2.

Definition block_simulation (diinfo: DIInfo) (f1:fdef) b1 b2 : Prop :=
  if (fdef_dec (DI_f diinfo) f1) then remove_block (DI_id diinfo) b1 = b2
  else b1 = b2.

Definition products_simulation (diinfo: DIInfo) Ps1 Ps2 : Prop :=
List.Forall2
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation diinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (diinfo: DIInfo) S1 S2 : Prop :=
List.Forall2
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\
       products_simulation diinfo Ps1 Ps2
   end) S1 S2.

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

Definition removable_State (diinfo: DIInfo) (St:@Opsem.State DGVs) : Prop :=
match St with
| Opsem.mkState
    (Opsem.mkEC f b (c :: cs) tmn lc als::_) _ =>
    if (fdef_dec (DI_f diinfo) f) then
      if (id_dec (DI_id diinfo) (getCmdLoc c)) then True else False
    else False
| _ => False
end.

Lemma removable_State_dec : forall diinfo St,
  removable_State diinfo St \/ ~ removable_State diinfo St.
Proof.
  destruct St.
  destruct ECS as [|[]]; auto.
  destruct CurCmds; auto.
  simpl.
  destruct (fdef_dec (DI_f diinfo) CurFunction); auto.
  destruct (id_dec (DI_id diinfo) (getCmdLoc c)); auto.
Qed.

Lemma die_is_sim : forall diinfo Cfg1 St1 Cfg2 St2
  (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hsim: State_simulation diinfo Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State diinfo St1) St1' tr1
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1),
      State_simulation diinfo Cfg1 St1' Cfg2 St2 /\ tr1 = trace_nil) /\
  (forall (Hnrem: ~removable_State diinfo St1) St1' St2' tr1 tr2
     (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2)
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1),
     State_simulation diinfo Cfg1 St1' Cfg2 St2' /\ tr1 = tr2).
Admitted.

Lemma s_genInitState__die_State_simulation:
  forall diinfo S1 S2 main VarArgs cfg2 IS2,
  die.system_simulation diinfo S1 S2 ->
  Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2) ->
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    die.State_simulation diinfo cfg1 IS1 cfg2 IS2.
Admitted.

Lemma s_isFinialState__die_State_simulation:
  forall diinfo cfg1 FS1 cfg2 FS2 r
  (Hstsim : die.State_simulation diinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: s_isFinialState cfg2 FS2 = ret r),
  s_isFinialState cfg1 FS1 = ret r.
Admitted.

Lemma opsem_s_isFinialState__die_State_simulation: forall
  diinfo cfg1 FS1 cfg2 FS2
  (Hstsim : die.State_simulation diinfo cfg1 FS1 cfg2 FS2),
  Opsem.s_isFinialState FS1 = Opsem.s_isFinialState FS2.
Admitted.

Lemma undefined_state__die_State_simulation: forall diinfo cfg1 St1 cfg2
  St2 (Hstsim : die.State_simulation diinfo cfg1 St1 cfg2 St2),
  OpsemPP.undefined_state cfg1 St1 -> OpsemPP.undefined_state cfg2 St2.
Admitted.

Lemma sop_star__die_State_simulation: forall diinfo cfg1 IS1 cfg2 IS2 tr FS2
  (Hwfpp: OpsemPP.wf_State cfg1 IS1)
  (Hstsim : die.State_simulation diinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\
    die.State_simulation diinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    assert (J:=Hwfpp).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]].
      apply opsem_s_isFinialState__die_State_simulation in Hstsim.
      rewrite Hstsim in Hfinal1.
      contradict H; eauto using s_isFinialState__stuck.

      assert (OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
        apply OpsemPP.preservation in Hop1; auto.
      eapply die_is_sim in Hstsim; eauto.
      destruct Hstsim as [Hstsim1 Hstsim2].
      destruct (@die.removable_State_dec diinfo IS1) as [Hrm | Hnrm].
        eapply Hstsim1 in Hrm; eauto.
        destruct Hrm as [Hstsim EQ]; subst.
        admit. (* we should do induction on the measure of State_simulation *)

        eapply Hstsim2 in Hnrm; eauto.
        destruct Hnrm as [Hstsim EQ]; subst.
        eapply IHHopstar in Hstsim; eauto.
        destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
        exists FS1.
        split; eauto.

      eapply undefined_state__die_State_simulation in Hstsim; eauto.
      contradict H; eauto using undefined_state__stuck.
Qed.

Lemma sop_div__die_State_simulation: forall diinfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpp: OpsemPP.wf_State cfg1 IS1)
  (Hstsim : die.State_simulation diinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Admitted.

Lemma die_sim: forall id0 f diinfo los nts Ps1 Ps2 main VarArgs
  (HwfS: wf_system nil [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq1: f = DI_f diinfo) (Heq2: id0 = DI_id diinfo),
  program_sim
    [module_intro los nts
      (Ps1 ++  product_fdef (remove_fdef id0 f) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Proof.
  intros. subst.
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (die.system_simulation diinfo
    [module_intro los nts (Ps1 ++ product_fdef (DI_f diinfo) :: Ps2)]
    [module_intro los nts
      (Ps1 ++ product_fdef (remove_fdef (DI_id diinfo) (DI_f diinfo)) :: Ps2)])
    as Hssim.
    unfold die.system_simulation.
    constructor; auto.
    repeat split; auto.
    unfold die.products_simulation.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    apply uniq_products_simulation; auto.

  constructor.
    intros tr t Hconv.
    inv Hconv.
    eapply s_genInitState__die_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit1 Hstsim]]].
    assert (OpsemPP.wf_State cfg1 IS1) as Hwfst.
      eapply s_genInitState__opsem_wf; eauto.
    eapply sop_star__die_State_simulation in Hstsim; eauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    eapply s_isFinialState__die_State_simulation in Hstsim'; eauto.
    econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    eapply s_genInitState__die_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]].
    assert (OpsemPP.wf_State cfg1 IS1) as Hwfst.
      eapply s_genInitState__opsem_wf; eauto.
    eapply sop_div__die_State_simulation in Hstsim; eauto.
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.
Qed.

Lemma subst_fdef__diinfo: forall f id0 v0,
  exists diinfo:DIInfo, DI_f diinfo = subst_fdef id0 v0 f /\ DI_id diinfo = id0.
Admitted.

Lemma die_wfS: forall id0 f diinfo los nts Ps1 Ps2
  (HwfS: wf_system nil [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq1: f = DI_f diinfo) (Heq2: id0 = DI_id diinfo),
  wf_system nil
    [module_intro los nts (Ps1 ++  product_fdef (remove_fdef id0 f) :: Ps2)].
Admitted.

Lemma die_wfPI: forall id0 f diinfo los nts Ps1 Ps2 pinfo
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system nil [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq1: f = DI_f diinfo) (Heq2: id0 = DI_id diinfo) (Heq3: f = PI_f pinfo),
  WF_PhiInfo (update_pinfo pinfo (remove_fdef id0 f)).
Admitted.

Lemma remove_successors : forall f id',
  successors f = successors (remove_fdef id' f).
Admitted.

Lemma remove_reachablity_analysis : forall f id',
  dtree.reachablity_analysis f = dtree.reachablity_analysis (remove_fdef id' f).
Admitted.
