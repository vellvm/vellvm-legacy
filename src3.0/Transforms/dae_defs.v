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
Require Import genericvalues_inject.
Require Import trans_tactic.
Require Import top_sim.

Definition fdef_simulation (pinfo: PhiInfo) f1 f2 : Prop :=
RemoveSim.fdef_simulation (PI_f pinfo) (PI_id pinfo) f1 f2.

Definition cmds_simulation (pinfo: PhiInfo) (f1:fdef) cs1 cs2 : Prop :=
RemoveSim.cmds_simulation (PI_f pinfo) (PI_id pinfo) f1 cs1 cs2.

Definition block_simulation (pinfo: PhiInfo) (f1:fdef) b1 b2 : Prop :=
RemoveSim.block_simulation (PI_f pinfo) (PI_id pinfo) f1 b1 b2.

Definition Fsim (pinfo: PhiInfo) := mkFunSim 
(fdef_simulation pinfo)
(RemoveSim.fdef_simulation__eq_fheader (PI_f pinfo) (PI_id pinfo))
(RemoveSim.fdef_simulation__det_right (PI_f pinfo) (PI_id pinfo))
.

Definition products_simulation (pinfo: PhiInfo) Ps1 Ps2 : Prop :=
@TopSim.products_simulation (Fsim pinfo) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) S1 S2 : Prop :=
@TopSim.system_simulation (Fsim pinfo) S1 S2.

Definition is_alloca_in_EC (pinfo: PhiInfo) F1 (lc1:@Opsem.GVsMap DGVs)
  (blk1: mblock) : bool :=
  if (fdef_dec (PI_f pinfo) F1) then
    match lookupAL _ lc1 (PI_id pinfo) with
    | Some ((Vptr b _,_)::nil) =>
        if (Z_eq_dec b blk1) then true
        else false
    | _ => false
    end
  else false.

Definition als_blk_simulation (pinfo: PhiInfo) (mi:MoreMem.meminj) F1
  (lc1:@Opsem.GVsMap DGVs) (blk1 blk2: mblock) : Prop :=
  if (is_alloca_in_EC pinfo F1 lc1 blk1) then mi blk1 = None
  else mi blk1 = Some (blk2, 0).

Fixpoint als_simulation (pinfo: PhiInfo) (mi:MoreMem.meminj) F1 lc1
  (als1 als2:list mblock) : Prop :=
  match (als1, als2) with
  | (nil, nil) => True
  | (b1::als1', _) =>
      if (is_alloca_in_EC pinfo F1 lc1 b1) then
        mi b1 = None /\ als_simulation pinfo mi F1 lc1 als1' als2
      else
        match als2 with
        | b2::als2' =>
           mi b1 = Some (b2, 0) /\ als_simulation pinfo mi F1 lc1 als1' als2'
        | _ => False
        end
  | _ => False
  end.

Definition reg_simulation (pinfo: PhiInfo) (mi:MoreMem.meminj) (F1:fdef)
  (lc1 lc2:@Opsem.GVsMap DGVs) : Prop :=
  if (fdef_dec (PI_f pinfo) F1) then
    forall i0,
      if (id_dec (PI_id pinfo) i0) then True
      else
        forall gv1 gv2,
          lookupAL _ lc1 i0 = Some gv1 ->
          lookupAL _ lc2 i0 = Some gv2 ->
          gv_inject mi gv1 gv2
  else
    forall i0 gv1 gv2,
      lookupAL _ lc1 i0 = Some gv1 ->
      lookupAL _ lc2 i0 = Some gv2 ->
      gv_inject mi gv1 gv2.

Definition EC_simulation (pinfo: PhiInfo) (mi:MoreMem.meminj)
  (EC1 EC2:@Opsem.ExecutionContext DGVs) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1,
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation pinfo f1 f2 /\
       tmn1 = tmn2 /\
       als_simulation pinfo mi f1 lc1 als1 als2 /\
       block_simulation pinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11,
         b1 = (l1, stmts_intro ps1 (cs11++cs1) tmn1))
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = (l2, stmts_intro ps2 (cs21++cs2) tmn2)) /\
       reg_simulation pinfo mi f1 lc1 lc2 /\
       cmds_simulation pinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (pinfo: PhiInfo) mi (ECs1 ECs2:@Opsem.ECStack DGVs)
  : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' =>
    EC_simulation pinfo mi EC1 EC2 /\ ECs_simulation pinfo mi ECs1' ECs2'
| _, _ => False
end.

Definition isnt_alloca_in_ECs (pinfo:PhiInfo) (ecs:list (fdef*Opsem.GVsMap))
  (blk:mblock) : Prop :=
  forall f lc (Hin: In (f,lc) ecs),
    is_alloca_in_EC pinfo f lc blk = false.

Definition strip_ECs (ecs:list (@Opsem.ExecutionContext DGVs))
  : list (fdef*Opsem.GVsMap) :=
List.map (fun ec => (Opsem.CurFunction ec, Opsem.Locals ec)) ecs.

Definition mem_simulation (pinfo:PhiInfo) mgb (mi:MoreMem.meminj)
  (ecs:list (fdef*Opsem.GVsMap)) Mem1 Mem2 : Prop :=
MoreMem.mem_inj mi Mem1 Mem2 /\
(forall blk, ~ isnt_alloca_in_ECs pinfo ecs blk -> mi blk = None) /\
wf_sb_mi mgb mi Mem1 Mem2.

Ltac repeat_solve :=
  repeat (match goal with
          | |- mem_simulation _ _ _ _ _ _ => idtac
          | |- _ => split; eauto 2 using cmds_at_block_tail_next
          end).

Definition State_simulation (pinfo: PhiInfo) mgb (mi:MoreMem.meminj)
  (Cfg1:OpsemAux.Config) (St1:Opsem.State)
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\
    products_simulation pinfo Ps1 Ps2 /\
    ECs_simulation pinfo mi ECs1 ECs2 /\
    gl1 = gl2 /\ OpsemAux.ftable_simulation mi fs1 fs2 /\
    mem_simulation pinfo mgb mi (strip_ECs ECs1) M1 M2
end.

Definition removable_State (pinfo: PhiInfo) (St:@Opsem.State DGVs) : Prop :=
RemoveSim.removable_State (PI_f pinfo) (PI_id pinfo) St.

Lemma reg_simulation_update_palloca: forall (pinfo : PhiInfo)
  (mi : MoreMem.meminj) TD (lc1 lc2 : Opsem.GVsMap)
  (Hlcsim2 : reg_simulation pinfo mi (PI_f pinfo) lc1 lc2)
  (mb : mblock) (mi' : MoreMem.meminj)
  (Hinc : inject_incr mi mi'),
  reg_simulation pinfo mi' (PI_f pinfo)
    (updateAddAL (GVsT DGVs) lc1 (PI_id pinfo)
       ($ blk2GV TD mb # typ_pointer (PI_typ pinfo) $)) lc2.
Proof.
  intros.
  unfold reg_simulation in *.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  intros.
  assert (J:=@Hlcsim2 i0). clear Hlcsim2.
  destruct (id_dec (PI_id pinfo) i0); subst; auto.
  intros.
  rewrite <- lookupAL_updateAddAL_neq in H; auto.
  eapply J in H; eauto.
  eapply gv_inject_incr; eauto.
Qed.

Lemma inject_incr__preserves__als_simulation: forall pinfo mi f lc1 als1 als2
  mi',
  als_simulation pinfo mi f lc1 als1 als2 ->
  (forall blk,
    is_alloca_in_EC pinfo f lc1 blk = true ->
    mi blk = None -> mi' blk = None) ->
  inject_incr mi mi' ->
  als_simulation pinfo mi' f lc1 als1 als2.
Proof.
  induction als1; destruct als2; simpl; intros; auto.
    remember (is_alloca_in_EC pinfo f lc1 a) as R.
    destruct R; auto.
    destruct H.
    split; eauto.

    remember (is_alloca_in_EC pinfo f lc1 a) as R.
    destruct R; destruct H; split; eauto.
Qed.

Lemma inject_incr__preserves__reg_simulation: forall pinfo mi f lc1 lc2 mi',
  reg_simulation pinfo mi f lc1 lc2 ->
  inject_incr mi mi' ->
  reg_simulation pinfo mi' f lc1 lc2.
Proof.
  intros pinfo mi f lc1 lc2 mi' Hrsim Hinc.
  unfold reg_simulation in *.
  destruct (fdef_dec (PI_f pinfo) f); subst.
    intros.
    assert (J:=@Hrsim i0).
    destruct (id_dec (PI_id pinfo) i0); subst; auto.
    intros. eapply J in H; eauto using gv_inject_incr.

    intros. eapply Hrsim in H; eauto using gv_inject_incr.
Qed.

Lemma inject_incr__preserves__EC_simulation: forall pinfo mi mi' EC1 EC2,
  EC_simulation pinfo mi EC1 EC2 ->
  (forall blk,
    is_alloca_in_EC pinfo (Opsem.CurFunction EC1) (Opsem.Locals EC1) blk
      = true ->
    mi blk = None -> mi' blk = None) ->
  inject_incr mi mi' ->
  EC_simulation pinfo mi' EC1 EC2.
Proof.
  intros.
  destruct EC1 as [f1 b1 cs1 tmn1 lc1 als1].
  destruct EC2 as [f2 b2 cs2 tmn2 lc2 als2].
  destruct f1. destruct f2.
  destruct b1; tinv H.
  unfold EC_simulation in H.
  destruct H as [Hfsim [Heq0 [Hasim [Hbsim [Heqb1 [Heqb2 [Hrsim Hcssim]]]]]]];
    subst.
  eapply inject_incr__preserves__als_simulation in Hasim; eauto.
  eapply inject_incr__preserves__reg_simulation in Hrsim; eauto.
  repeat (split; auto).
Qed.

Lemma inject_incr__preserves__ECs_simulation: forall pinfo mi mi' ECs1 ECs2,
  ECs_simulation pinfo mi ECs1 ECs2 ->
  (forall blk, ~ isnt_alloca_in_ECs pinfo (strip_ECs ECs1) blk ->
    mi blk = None -> mi' blk = None) ->
  inject_incr mi mi' ->
  ECs_simulation pinfo mi' ECs1 ECs2.
Proof.
  induction ECs1; destruct ECs2; simpl; intros; auto.
    destruct H as [J1 J2].
    split.
      eapply inject_incr__preserves__EC_simulation; eauto.
        intros.
        apply H0; auto.
        intro J.
        unfold isnt_alloca_in_ECs in J.
        assert (In (Opsem.CurFunction a, Opsem.Locals a)
          ((Opsem.CurFunction a, Opsem.Locals a)::strip_ECs ECs1)) as G.
          simpl. auto.
        apply J in G. uniq_result.

        apply IHECs1; auto.
        intros. apply H0; auto.
        intro J. apply H.
        unfold isnt_alloca_in_ECs in *.
        intros. apply J. simpl; auto.
Qed.

Lemma isnt_alloca_in_ECs_tail: forall pinfo (mi:MoreMem.meminj) EC1 EC2 ECs ,
  (forall blk,
    ~ isnt_alloca_in_ECs pinfo (EC1 :: EC2 :: ECs) blk -> mi blk = merror) ->
  (forall blk,
    ~ isnt_alloca_in_ECs pinfo (EC2 :: ECs) blk -> mi blk = merror).
Proof.
  intros.
  apply H; auto.
  intro J. apply H0.
  unfold isnt_alloca_in_ECs in J. unfold isnt_alloca_in_ECs.
  intros.
  apply J; auto.
  simpl. simpl in Hin. destruct Hin; auto.
Qed.

Lemma mem_simulation_tail: forall pinfo mgb mi EC1 EC2 ECs M1 M2,
  mem_simulation pinfo mgb mi (EC1 :: EC2 :: ECs) M1 M2 ->
  mem_simulation pinfo mgb mi (EC2 :: ECs) M1 M2.
Proof.
  intros.
  destruct H as [J1 [J2 J3]].
  split; auto.
  split; auto.
    eapply isnt_alloca_in_ECs_tail; eauto.
Qed.

Lemma is_alloca_in_EC_update_lc: forall pinfo F lc id0 gvs0 blk,
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  is_alloca_in_EC pinfo F lc blk =
    is_alloca_in_EC pinfo F (updateAddAL (GVsT DGVs) lc id0 gvs0) blk.
Proof.
  intros.
  unfold is_alloca_in_EC in *.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  destruct H as [H | H]; try congruence.
  rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma isnt_alloca_in_ECs_update_non_palloca :
  forall pinfo lc1 lc2 ECs F (mi:MoreMem.meminj) gvs3 id0,
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  updateAddAL (GVsT DGVs) lc1 id0 gvs3 = lc2 ->
  (forall blk:mblock,
    ~ isnt_alloca_in_ECs pinfo ((F, lc1) :: ECs) blk ->
    mi blk = merror) ->
  (forall blk:mblock,
    ~ isnt_alloca_in_ECs pinfo ((F, lc2) :: ECs) blk ->
    mi blk = merror).
Proof.
  intros. subst.
  apply H1. clear H1.
  intro J. apply H2. clear H2.
  unfold isnt_alloca_in_ECs in *.
  intros.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; subst.
    inv Hin.
    rewrite <- is_alloca_in_EC_update_lc; auto.
    apply J. simpl. auto.

    apply J. clear J. simpl. auto.
Qed.

Lemma als_simulation_update_lc: forall pinfo F lc mi id0 gvs0 als1 als2,
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  als_simulation pinfo mi F lc als1 als2 ->
  als_simulation pinfo mi F (updateAddAL (GVsT DGVs) lc id0 gvs0) als1 als2.
Proof.
  induction als1; destruct als2; simpl; auto.
    intros.
    rewrite <- is_alloca_in_EC_update_lc; auto.
    destruct (is_alloca_in_EC pinfo F lc a); auto.
    destruct H0 as [J1 J2].
    split; auto.

    intros.
    rewrite <- is_alloca_in_EC_update_lc; auto.
    destruct (is_alloca_in_EC pinfo F lc a); destruct H0 as [J1 J2]; split; auto.
Qed.

Lemma returnUpdateLocals_als_simulation: forall pinfo mi F' lc' als' als3 TD i0 n
  c t0 v0 v p Result lc gl2 lc'' (Hsim: als_simulation pinfo mi F' lc' als' als3)
  (Hprop: PI_f pinfo <> F' \/ PI_id pinfo <> i0)
  (Hupdate: Opsem.returnUpdateLocals TD (insn_call i0 n c t0 v0 v p) Result lc lc'
              gl2 = ret lc''),
  als_simulation pinfo mi F' lc'' als' als3.
Proof.
  intros.
  unfold Opsem.returnUpdateLocals in Hupdate.
  inv_mbind'.
  destruct n; inv H0; auto.
  inv_mbind'.
  apply als_simulation_update_lc; auto.
Qed.

Lemma reg_simulation_update_non_palloca: forall pinfo F lc1 lc2 mi id0 gvs0 gvs3,
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  reg_simulation pinfo mi F lc1 lc2 ->
  gv_inject mi gvs0 gvs3 ->
  reg_simulation pinfo mi F (updateAddAL (GVsT DGVs) lc1 id0 gvs0)
    (updateAddAL (GVsT DGVs) lc2 id0 gvs3).
Proof.
  unfold reg_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) F); subst; intros.
    assert (J:=@H0 i0). clear H0.
    destruct H as [H | H]; try congruence.
    destruct (id_dec (PI_id pinfo) i0); subst; auto.
    destruct (id_dec id0 i0); subst.
      rewrite lookupAL_updateAddAL_eq; auto.
      rewrite lookupAL_updateAddAL_eq; auto.
      intros. inv H2. inv H0. auto.

      rewrite <- lookupAL_updateAddAL_neq; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.

    assert (J:=@H0 i0). clear H0.
    destruct (id_dec id0 i0); subst.
      rewrite lookupAL_updateAddAL_eq in H2; auto.
      rewrite lookupAL_updateAddAL_eq in H3; auto.
      inv H2. inv H3. auto.

      rewrite <- lookupAL_updateAddAL_neq in H2; auto.
      rewrite <- lookupAL_updateAddAL_neq in H3; auto.
Qed.

Definition value_doesnt_use_pid pinfo F v :=
  conditional_used_in_value (PI_f pinfo) F (PI_id pinfo) v.

Lemma simulation__getOperandValue : forall pinfo maxb mi lc lc2 los nts Mem Mem2 
  gl F v gv gv' (Hprop: value_doesnt_use_pid pinfo F v) S Ps t
  (Hv: wf_value S (module_intro los nts Ps) F v t),
  wf_globals maxb gl ->
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  getOperandValue (los,nts) v lc gl = ret gv ->
  getOperandValue (los,nts) v lc2 gl = ret gv' ->
  gv_inject mi gv gv'.
Proof.
  intros.
  unfold getOperandValue in *.
  unfold reg_simulation in H1.
  destruct (fdef_dec (PI_f pinfo) F); subst.
    destruct Hprop as [Hprop | Hprop]; try congruence.
    destruct v as [i0|?]; simpl in Hprop.
      assert (J:=@H1 i0). clear H1.
      destruct (id_dec (PI_id pinfo) i0); subst; eauto.
        destruct (id_dec (PI_id pinfo) (PI_id pinfo));
          simpl in Hprop; try congruence.

      uniq_result. inv Hv. eapply sb_mem_inj__const2GV; eauto.

    destruct v; eauto.
      uniq_result. inv Hv. eapply sb_mem_inj__const2GV; eauto.
Qed.

Lemma simulation__lift_opt1: forall (mi : MoreMem.meminj) (TD : TargetData)
  (t : typ) (g1 g2 g2' g1': GVsT DGVs)
  (HeqR2 : lift_op1 DGVs (fit_gv TD t) g2 t = ret g2')
  (HeqR1 : lift_op1 DGVs (fit_gv TD t) g1 t = ret g1')
  (HeqR : gv_inject mi g1 g2),
  gv_inject mi g1' g2'.
Proof.
  intros.
Transparent lift_op1.
  unfold lift_op1 in *. simpl in *.
  unfold MDGVs.lift_op1 in *.
  unfold fit_gv in *.
  inv_mbind'. symmetry_ctx.
  erewrite gv_inject__same_size in H0; eauto.
  erewrite simulation__gv_chunks_match_typb in H0; eauto.
  destruct_if.
    inv HeqR2. auto.

    uniq_result.
    eapply gv_inject_gundef; eauto.
Opaque lift_op1.
Qed.

Lemma returnUpdateLocals_reg_simulation: forall pinfo mi F' lc' los nts i0 n
  c t0 v0 v p Result lc gl lc'' lc3 lc''0 lc2 F Mem1 Mem2 maxb S Ps rt
  (Hv: wf_value S (module_intro los nts Ps) F Result rt)
  (Hwfg: wf_globals maxb gl) (Hwfmi: wf_sb_mi maxb mi Mem1 Mem2)
  (Hprop: PI_f pinfo <> F' \/ PI_id pinfo <> i0)
  (Hprop': value_doesnt_use_pid pinfo F Result)
  (Hsim: reg_simulation pinfo mi F' lc' lc3)
  (Hsim': reg_simulation pinfo mi F lc lc2)
  (Hupdate: Opsem.returnUpdateLocals (los,nts) (insn_call i0 n c t0 v0 v p) Result lc
              lc' gl = ret lc'')
  (Hupdate': Opsem.returnUpdateLocals (los,nts) (insn_call i0 n c t0 v0 v p) Result 
               lc2 lc3 gl = ret lc''0),
  reg_simulation pinfo mi F' lc'' lc''0.
Proof.
  intros.
  unfold Opsem.returnUpdateLocals in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue in HeqR; eauto.
  destruct n; uniq_result; auto.
  inv_mbind'. symmetry_ctx.
  apply reg_simulation_update_non_palloca; auto.
  eapply simulation__lift_opt1; eauto.
Qed.

Definition phis_simulation (pinfo: PhiInfo) (f1:fdef) ps1 ps2 : Prop :=
RemoveSim.phis_simulation (PI_f pinfo) (PI_id pinfo) f1 ps1 ps2.

Lemma phis_simulation_inv: forall pinfo F ps1 ps2 l1 cs1 tmn1
  (HBinF: blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) F = true),
  WF_PhiInfo pinfo -> uniqFdef F ->
  phis_simulation pinfo F ps1 ps2 -> ps1 = ps2.
Proof.
  intros.
  eapply RemoveSim.phis_simulation_inv; eauto 1.
    intro. subst. WF_PhiInfo_spec6_tac.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_rsim : forall los nts B1 B2 gl F mi lc1'
  maxb Mem1 Mem2 S1 Ps B1'
  (Hwfg: wf_globals maxb gl) (Hwfmi: wf_sb_mi maxb mi Mem1 Mem2)
  pinfo lc2' ps
  (Hwfps: wf_phinodes S1 (module_intro los nts Ps) F B1' ps) 
  (Hnuse: PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps))
  (Hnuse': PI_f pinfo <> F \/
           fold_left
             (fun (re : bool) (p : phinode) => re || used_in_phi (PI_id pinfo) p)
           ps false = false)
  (l3 l0:list (id * GVsT DGVs))
  (HeqR0 : Opsem.getIncomingValuesForBlockFromPHINodes (los,nts) ps B1 gl lc1' =
           ret l3)
  (Hbsim2 : block_simulation pinfo F B1 B2)
  (Hrsim : reg_simulation pinfo mi F lc1' lc2')
  (HeqR : Opsem.getIncomingValuesForBlockFromPHINodes (los,nts) ps B2 gl lc2' =
          ret l0),
  reg_simulation pinfo mi F (Opsem.updateValuesForNewBlock l3 lc1')
     (Opsem.updateValuesForNewBlock l0 lc2').
Proof.
  induction ps as [|[i0 ? l0]]; simpl; intros.
    uniq_result. simpl. auto.

    inv Hwfps. inv_mbind'. symmetry_ctx. simpl.
    assert (PI_f pinfo <> F \/ PI_id pinfo <> i0) as J1.
      clear - Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
    assert (reg_simulation pinfo mi F
             (Opsem.updateValuesForNewBlock l1 lc1')
             (Opsem.updateValuesForNewBlock l2 lc2')) as J2.
      assert (PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps)) as J3.
        clear - Hnuse.
        destruct Hnuse as [Hnuse | Hnuse]; auto.
      assert (PI_f pinfo <> F \/
              fold_left
                (fun (re : bool) (p : phinode) =>
                  re || used_in_phi (PI_id pinfo) p)
                 ps false = false) as J4.
        clear - Hnuse'.
        destruct Hnuse' as [Hnuse' | Hnuse']; auto.
        right.
        assert (J:=Hnuse').
        apply fold_left_eq in J.
          rewrite J in Hnuse'. auto.
          intros. apply orb_false_iff in H. destruct H; auto.
      apply IHps; auto.
    assert (wf_value S1 (module_intro los nts Ps) F v typ5) as Hwft.
      match goal with
      | H5: wf_insn _ _ _ _ _ |- _ => inv H5;
        find_wf_value_list;
        match goal with
        | H2: wf_value_list _ |- _ => 
           eapply wf_value_list__getValueViaBlockFromValuels__wf_value in H2; 
             eauto
        end
      end.
    apply reg_simulation_update_non_palloca; auto.
      erewrite RemoveSim.block_simulation__getValueViaBlockFromValuels in HeqR3; eauto.
      rewrite HeqR3 in HeqR1. inv HeqR1.
      eapply simulation__getOperandValue with (lc:=lc1')(lc2:=lc2'); eauto.

      destruct B2. simpl in HeqR3.
      assert (PI_f pinfo <> F \/ used_in_list_value_l (PI_id pinfo) l0 = false)
        as J3.
        clear - Hnuse'.
        destruct Hnuse' as [Hnuse' | Hnuse']; auto.
        right.
        apply fold_left_eq in Hnuse'; auto.
          intros. apply orb_false_iff in H. destruct H; auto.
      eapply conditional_used_in_getValueViaLabelFromValuels; eauto.
Qed.

Lemma switchToNewBasicBlock_rsim : forall los nts l1 l2 ps cs1 cs2 tmn1 tmn2 B1 B2
  gl lc1 lc2 F pinfo mi lc1' lc2' maxb Mem1 Mem2 S1 B1' Ps
  (Hwfps: wf_phinodes S1 (module_intro los nts Ps) F B1' ps) 
  (Hwfg: wf_globals maxb gl) (Hwfmi: wf_sb_mi maxb mi Mem1 Mem2)
  (Hnuse': PI_f pinfo <> F \/
           fold_left
             (fun (re : bool) (p : phinode) => re || used_in_phi (PI_id pinfo) p)
           ps false = false)
  (Hwfp: WF_PhiInfo pinfo) (Huniq: uniqFdef F)
  (HBinF: blockInFdefB (l1, stmts_intro ps cs1 tmn1) F = true)
  (H23 : @Opsem.switchToNewBasicBlock DGVs (los,nts)
          (l1, stmts_intro ps cs1 tmn1) B1 gl lc1' =
         ret lc1)
  (Hbsim2 : block_simulation pinfo F B1 B2)
  (Hrsim: reg_simulation pinfo mi F lc1' lc2')
  (H2 : Opsem.switchToNewBasicBlock (los,nts)
         (l2, stmts_intro ps cs2 tmn2) B2 gl lc2' =
        ret lc2), reg_simulation pinfo mi F lc1 lc2.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in *. simpl in *.
  inv_mbind'. symmetry_ctx.
  eapply getIncomingValuesForBlockFromPHINodes_rsim; eauto.
    WF_PhiInfo_spec6_tac.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_asim:
  forall pinfo F als1 als2 lc mi gl B TD
  (Hsim: als_simulation pinfo mi F lc als1 als2) ps l1
  (Hnuse: PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps)),
  Opsem.getIncomingValuesForBlockFromPHINodes TD ps B gl lc = ret l1 ->
  als_simulation pinfo mi F (Opsem.updateValuesForNewBlock l1 lc) als1 als2.
Proof.
  induction ps as [|[i0 ? ?]]; simpl; intros.
    uniq_result. simpl. auto.

    inv_mbind'. symmetry_ctx. simpl.
    assert (PI_f pinfo <> F \/ PI_id pinfo <> i0) as J1.
      clear - Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
    assert (PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps)) as J2.
      clear - Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
    apply als_simulation_update_lc; auto.
Qed.

Lemma switchToNewBasicBlock_asim: forall pinfo F l0 ps0 cs0 tmn0 als1 als2 lc
  lc' mi gl B TD,
  WF_PhiInfo pinfo -> uniqFdef F ->
  blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) F = true ->
  als_simulation pinfo mi F lc als1 als2 ->
  Opsem.switchToNewBasicBlock TD (l0, stmts_intro ps0 cs0 tmn0) B gl lc =
    ret lc' ->
  als_simulation pinfo mi F lc' als1 als2.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in *. simpl in *.
  inv_mbind'. symmetry_ctx.
  eapply getIncomingValuesForBlockFromPHINodes_asim; eauto.
    WF_PhiInfo_spec6_tac.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_isnt_alloca_in_ECs :
  forall pinfo TD ECs F gl B blk ps lc1 l0
  (Hnuse: PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps)),
  Opsem.getIncomingValuesForBlockFromPHINodes TD ps B gl lc1 = ret l0 ->
  isnt_alloca_in_ECs pinfo ((F,lc1) :: ECs) blk ->
  isnt_alloca_in_ECs pinfo ((F,Opsem.updateValuesForNewBlock l0 lc1) :: ECs) blk.
Proof.
  induction ps as [|[]]; simpl; intros.
    uniq_result. simpl. auto.

    inv_mbind'. symmetry_ctx. simpl.
    assert (PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps)) as J.
      clear - Hnuse.
      destruct Hnuse; auto.
    apply IHps in HeqR1; auto. clear IHps.
    unfold isnt_alloca_in_ECs. unfold isnt_alloca_in_ECs in H0.
    intros.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
      inv Hin.
      rewrite <- is_alloca_in_EC_update_lc.
        apply HeqR1. simpl. auto.
        clear - Hnuse. destruct Hnuse; auto.
      apply H0. simpl. auto.
Qed.

Lemma switchToNewBasicBlock_isnt_alloca_in_ECs :
  forall pinfo TD ECs F gl B B' blk lc1 lc2,
  WF_PhiInfo pinfo -> uniqFdef F ->
  blockInFdefB B' F = true ->
  Opsem.switchToNewBasicBlock TD B' B gl lc1 = ret lc2 ->
  isnt_alloca_in_ECs pinfo ((F,lc1) :: ECs) blk ->
  isnt_alloca_in_ECs pinfo ((F,lc2) :: ECs) blk.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in *. simpl in *.
  inv_mbind'. symmetry_ctx.
  destruct B' as [? []]. simpl in *.
  eapply getIncomingValuesForBlockFromPHINodes_isnt_alloca_in_ECs; eauto.
    WF_PhiInfo_spec6_tac.
Qed.

Lemma Promotability_wf_EC__isnt_alloca_in_EC: forall maxb pinfo TD M1 f lc als,
  (if fdef_dec (PI_f pinfo) f
      then Promotability.wf_defs maxb pinfo TD M1 lc als
      else True) ->
  is_alloca_in_EC pinfo f lc (Mem.nextblock M1) = false.
Proof.
  intros.
  unfold is_alloca_in_EC.
  destruct (fdef_dec (PI_f pinfo) f); subst; auto.
  remember (lookupAL (GVsT DGVs) lc (PI_id pinfo)) as R.
  destruct R as [[]|]; auto.
  destruct p as [[]]; auto.
  destruct l0; auto.
  destruct (Z_eq_dec b (Mem.nextblock M1)); subst; auto.
  symmetry in HeqR.
  apply H in HeqR.
  destruct HeqR as [HeqR _].
  destruct HeqR as [_ [HeqR _]].
  destruct HeqR as [mb [J1 [J2 J3]]].
  rewrite simpl_blk2GV in J1.
  inv J1.
  contradict J3; omega.
Qed.

Lemma Promotability_wf_ECs__isnt_alloca_in_ECs: forall maxb pinfo TD M1 ECs1,
  Promotability.wf_ECStack maxb pinfo TD M1 ECs1 ->
  isnt_alloca_in_ECs pinfo (strip_ECs ECs1) (Mem.nextblock M1).
Proof.
  induction ECs1; simpl; intros.
    unfold isnt_alloca_in_ECs.
    intros. inv Hin.

    destruct H as [H1 [H2 H3]].
    unfold isnt_alloca_in_ECs in *.
    intros.
    simpl in Hin.
    destruct Hin as [Hin | Hin]; subst.
      inv Hin. destruct a. destruct H1.
      eapply Promotability_wf_EC__isnt_alloca_in_EC; eauto.

      apply IHECs1; simpl; auto.
Qed.

Lemma malloc__is_alloca_in_EC: forall maxb pinfo TD Mem f lc tsz0 gn align0 Mem'
  mb (mi mi':MoreMem.meminj) als
  (H1: if fdef_dec (PI_f pinfo) f
       then Promotability.wf_defs maxb pinfo TD Mem lc als
       else True)
  (H2: malloc TD Mem tsz0 gn align0 = ret (Mem', mb))
  (Hprop2 : forall b : mblock, b <> mb -> mi b = mi' b),
  forall blk : mblock,
    is_alloca_in_EC pinfo f lc blk= true ->
    mi blk = merror -> mi' blk = merror.
Proof.
  intros.
  destruct (zeq blk mb); subst.
    apply MemProps.malloc_result in H2. subst.
    eapply Promotability_wf_EC__isnt_alloca_in_EC in H1; eauto.
    rewrite H1 in H. inv H.

    rewrite <- Hprop2; auto.
Qed.

Lemma malloc__isnt_alloca_in_ECs: forall maxb pinfo TD Mem EC tsz0 gn align0 Mem'
  mb (mi mi':MoreMem.meminj) (H1: Promotability.wf_ECStack maxb pinfo TD Mem EC)
  (H2: malloc TD Mem tsz0 gn align0 = ret (Mem', mb))
  (Hprop2 : forall b : mblock, b <> mb -> mi b = mi' b),
  forall blk : mblock,
    ~ isnt_alloca_in_ECs pinfo (strip_ECs EC) blk ->
    mi blk = merror -> mi' blk = merror.
Proof.
  intros.
  destruct (zeq blk mb); subst.
    apply MemProps.malloc_result in H2. subst.
    contradict H.
    eapply Promotability_wf_ECs__isnt_alloca_in_ECs; eauto.

    rewrite <- Hprop2; auto.
Qed.

(*
  lookupAL _ lc1 (PI_id pinfo) = None is important.

  if p = alloca is in a loop, then at runtime,
    p can be assigned multiple times by p1, p2, p3...
    all of which will be erased, and should not have corresponding memory block
    in the transformed program.

  But, we can only keep track of the last one, the earlier ones will be
   over-written...

  In practice, a promotable allocation is always at the entry block, so
  before its first assignment, its value must be none. Therefore, we are fine.
*)
Lemma als_simulation_weaken_palloca:
  forall mi' mb mi pinfo lc1 ofs mc
  (Hlkup : lookupAL _ lc1 (PI_id pinfo) = None)
  (Hmi1 : mi' mb = merror)
  (Hmi2 : forall b : mblock, b <> mb -> mi b = mi' b)
  als1 als2
  (Hsim : als_simulation pinfo mi (PI_f pinfo) lc1 als1 als2)
  (Hfresh : forall al, In al als1 -> al <> mb),
  als_simulation pinfo mi' (PI_f pinfo)
    (updateAddAL _ lc1 (PI_id pinfo) ((Vptr mb ofs, mc) :: nil))
    als1 als2.
Proof.
  induction als1; simpl; intros; auto.
    unfold is_alloca_in_EC in *.
    rewrite Hlkup in Hsim.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    destruct (id_dec (PI_id pinfo) (PI_id pinfo)); try congruence.
    rewrite lookupAL_updateAddAL_eq.
    destruct (Z_eq_dec mb a); subst.
      assert (a <> a) as Hneq.
        apply Hfresh; auto.
      congruence.

      destruct als2; auto.
      destruct Hsim as [Hsim1 Hsim2].
      split.
        rewrite <- Hmi2; auto.
        apply IHals1; auto.
Qed.

Lemma als_simulation_update_palloca:
  forall mi' mb mi pinfo lc1 TD M1 tsz gn M1'
  (H21: malloc TD M1 tsz gn (PI_align pinfo) = Some (M1', mb))
  (Hlkup : lookupAL _ lc1 (PI_id pinfo) = None)
  (Hmi1 : mi' mb = merror)
  (Hmi2 : forall b : mblock, b <> mb -> mi b = mi' b) maxb
  als1 als2 (Hsim : als_simulation pinfo mi (PI_f pinfo) lc1 als1 als2) ECs1
  (Halsbd : forall al : Values.block,
            In al
              (als1 ++
               flat_map
                 (fun ec : @Opsem.ExecutionContext DGVs =>
                  let '{| Opsem.Allocas := als |} := ec in als) ECs1) ->
            maxb < al < Mem.nextblock M1),
  als_simulation pinfo mi' (PI_f pinfo)
    (updateAddAL _ lc1 (PI_id pinfo)
      ($ blk2GV TD mb # typ_pointer (PI_typ pinfo) $))
      (mb::als1) als2.
Proof.
  intros.
  simpl.
  unfold is_alloca_in_EC.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  destruct (id_dec (PI_id pinfo) (PI_id pinfo)); try congruence.
  rewrite lookupAL_updateAddAL_eq.
  rewrite simpl_blk2GV.
  destruct (Z_eq_dec mb mb); try congruence.
  split; auto.
    eapply als_simulation_weaken_palloca; eauto.
      apply MemProps.malloc_result in H21.
      intros. intro EQ. subst.
      assert (maxb < Mem.nextblock M1 < Mem.nextblock M1) as J.
        apply Halsbd. simpl.
        apply in_or_app; auto.
      contradict J. omega.
Qed.

Definition list_value_doesnt_use_pid pinfo F idxs :=
  conditional_used_in_list_value (PI_f pinfo) F (PI_id pinfo) idxs.

Lemma mem_simulation__wf_sb_sim: forall pinfo maxb mi ECs M1 M2,
  mem_simulation pinfo maxb mi ECs M1 M2 -> wf_sb_mi maxb mi M1 M2.
Proof.
  intros. destruct H as [_ [_ H]]; auto.
Qed.

Lemma reg_simulation__malloc: forall pinfo F lc1 lc2 mi id0 mi' mb1 mb2 TD
  t (Hprop1 : mi' mb1 = ret (mb2, 0)) (Hprop3 : inject_incr mi mi'),
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  reg_simulation pinfo mi F lc1 lc2 ->
  reg_simulation pinfo mi' F
    (updateAddAL (GVsT DGVs) lc1 id0 ($ blk2GV TD mb1 # typ_pointer t $))
    (updateAddAL (GVsT DGVs) lc2 id0 ($ blk2GV TD mb2 # typ_pointer t $)).
Proof.
  intros.
  apply reg_simulation_update_non_palloca; auto.
    eapply inject_incr__preserves__reg_simulation; eauto.

    repeat rewrite simpl_blk2GV.
    constructor; auto.
      assert (Int.repr 31 0 = Int.add 31 (Int.repr 31 0) (Int.repr 31 0))
        as EQ.
        rewrite Int.add_zero. auto.
      rewrite EQ at 2.
      econstructor; eauto.
Qed.

Definition params_dont_use_pid pinfo F (ps:params) :=
  conditional_used_in_params (PI_f pinfo) F (PI_id pinfo) ps.

Lemma reg_simulation__params2GVs: forall pinfo mi F lc1 lc2 gl
  los nts (Hrsim: reg_simulation pinfo mi F lc1 lc2) maxb Mem1 Mem2
  (Hwfg: wf_globals maxb gl) (Hwfmi: wf_sb_mi maxb mi Mem1 Mem2)
  Ps S tavl lp (Hnuse: params_dont_use_pid pinfo F lp) gvs1 gvs2
  (Heq: lp = (List.map
    (fun p : typ * attributes * value =>
      let '(typ_', attributes_', value_'') := p in
        (( typ_' ,  attributes_' ),  value_'' )  ) tavl))
  (Hv: wf_value_list 
    (List.map
      (fun p : typ * attributes * value =>
        let '(typ_', attributes_', value_'') := p in
         (S,(module_intro los nts Ps),F,value_'',typ_')) tavl)),
  Opsem.params2GVs (los,nts) lp lc1 gl = ret gvs1 ->
  Opsem.params2GVs (los,nts) lp lc2 gl = ret gvs2 ->
  List.Forall2 (fun gv1 => fun gv2 => gv_inject mi gv1 gv2) gvs1 gvs2.
Proof.
  induction tavl; intros; subst; simpl in *.
    uniq_result. constructor.

    simpl_prod.
    inv_mbind'. symmetry_ctx. 
    rewrite wf_value_list_cons_iff in Hv. destruct Hv.
    assert (params_dont_use_pid pinfo F
              (List.map
                  (fun p : typ * attributes * value =>
                   let '(typ_', attributes_', value_'') := p in
                        (typ_', attributes_', value_''))
                  tavl) /\ value_doesnt_use_pid pinfo F v) as J.
      unfold params_dont_use_pid in Hnuse. unfold params_dont_use_pid.
      unfold value_doesnt_use_pid.
      destruct (fdef_dec (PI_f pinfo) F); subst; auto.
      destruct Hnuse as [Hnuse | Hnuse]; try congruence.
      simpl in Hnuse. assert (J:=Hnuse).
      apply fold_left_eq in Hnuse.
        rewrite Hnuse in J.
        binvf Hnuse as J1 J2.
        split; right; auto.

        intros. destruct b.
        binvf H1 as J1 J2. auto.
    destruct J as [J1 J2].
    constructor; eauto.
      eapply simulation__getOperandValue; eauto.
Qed.

Lemma reg_simulation__initializeFrameValues: forall pinfo mi fa0 rt0 fid0 va0
    TD lb la2 la1 (gvs1 gvs2:list (GVsT DGVs)) lc1 lc2 lc1' lc2'
  (Hnuse: args_dont_use_pid pinfo
            (fdef_intro (fheader_intro fa0 rt0 fid0 (la1++la2) va0) lb) la2),
  List.Forall2 (fun gv1 => fun gv2 => gv_inject mi gv1 gv2) gvs1 gvs2 ->
  reg_simulation pinfo mi
    (fdef_intro (fheader_intro fa0 rt0 fid0 (la1++la2) va0) lb) lc1 lc2 ->
  Opsem._initializeFrameValues TD la2 gvs1 lc1 = ret lc1' ->
  Opsem._initializeFrameValues TD la2 gvs2 lc2 = ret lc2' ->
  reg_simulation pinfo mi
    (fdef_intro (fheader_intro fa0 rt0 fid0 (la1++la2) va0) lb) lc1' lc2'.
Proof.
  induction la2 as [|[[]]]; simpl; intros.
    uniq_result. auto.

    assert (args_dont_use_pid pinfo
       (fdef_intro
          (fheader_intro fa0 rt0 fid0 ((la1 ++ [(t, a, i0)]) ++ la2) va0) lb)
       la2) as J.
      unfold args_dont_use_pid. unfold args_dont_use_pid in Hnuse.
      simpl_env. simpl_env in Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
      right.
      intros.
      eapply Hnuse; simpl; eauto.

    assert (PI_f pinfo <>
      fdef_intro (fheader_intro fa0 rt0 fid0 (la1 ++ (t, a, i0) :: la2) va0) lb\/
      PI_id pinfo <> i0) as J'.
      unfold args_dont_use_pid in Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
      right.
      eapply Hnuse; simpl; eauto.

    rewrite_env ((la1 ++ [(t, a, i0)]) ++ la2) in H0.
    inv H; inv_mbind''; symmetry_ctx.
      eapply IHla2 in H0; eauto.
        apply reg_simulation_update_non_palloca; auto.
        simpl_env in *. auto.
        eapply gv_inject_gundef; eauto.

      eapply IHla2 in H0; eauto.
        apply reg_simulation_update_non_palloca; auto.
        simpl_env in *. auto.
        eapply simulation__lift_opt1; eauto.
Qed.

Lemma reg_simulation_nil: forall pinfo mi F, reg_simulation pinfo mi F nil nil.
Proof.
  unfold reg_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
    intros.
    destruct (id_dec (PI_id pinfo) i0); subst; auto.
    intros. inv H.

    intros. intros. inv H.
Qed.

Lemma reg_simulation__initLocals: forall pinfo mi F lc1 lc2 lp gl gvs1 gvs2 lc1'
  lc2' la los nts fa0 rt0 fid0 va0 lb Mem1 Mem2 maxb
  (Hwfg: wf_globals maxb gl) (Hwfmi: wf_sb_mi maxb mi Mem1 Mem2)
  (Hnuse: params_dont_use_pid pinfo F lp)
  (Hnuse': args_dont_use_pid pinfo
            (fdef_intro (fheader_intro fa0 rt0 fid0 la va0) lb) la) tavl S Ps
  (Heq: lp = (List.map 
    (fun p : typ * attributes * value =>
        let '(typ_', attributes_', value_'') := p in
          ((typ_' ,  attributes_' ),  value_'' )  ) tavl))
  (Hv: wf_value_list 
    (List.map
      (fun p : typ * attributes * value =>
        let '(typ_', attributes_', value_'') := p in
          (S,(module_intro los nts Ps),F,value_'',typ_')) tavl)),
  reg_simulation pinfo mi F lc1 lc2 ->
  Opsem.params2GVs (los,nts) lp lc1 gl = ret gvs1 ->
  Opsem.params2GVs (los,nts) lp lc2 gl = ret gvs2 ->
  Opsem.initLocals (los,nts) la gvs1 = ret lc1' ->
  Opsem.initLocals (los,nts) la gvs2 = ret lc2' ->
  reg_simulation pinfo mi
    (fdef_intro (fheader_intro fa0 rt0 fid0 la va0) lb) lc1' lc2'.
Proof.
  intros.
  eapply reg_simulation__params2GVs in H; eauto.
  unfold Opsem.initLocals in *.
  rewrite_env (nil++la).
  eapply reg_simulation__initializeFrameValues; eauto.
  apply reg_simulation_nil; auto.
Qed.

Lemma WF_PhiInfo__isnt_alloca_in_EC: forall pinfo fa rt fid va lb la blk lc gvs
  TD (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb)),
  WF_PhiInfo pinfo ->
  Opsem.initLocals TD la gvs = ret lc ->
  is_alloca_in_EC pinfo (fdef_intro (fheader_intro fa rt fid la va) lb) lc blk
    = false.
Proof.
  intros.
  eapply WF_PhiInfo__args_dont_use_pid with (la0:=la) in H; eauto 1.
  unfold is_alloca_in_EC.
  unfold args_dont_use_pid in H.
  destruct (fdef_dec (PI_f pinfo)
             (fdef_intro (fheader_intro fa rt fid la va) lb)); try congruence.
  rewrite e in H.
  destruct H as [H | H]; try congruence.
  erewrite OpsemProps.NotIn_getArgsIDs__NotIn_initLocals; eauto.
  clear - H.
  induction la as [|[]]; simpl; auto.
    intro J.
    destruct J as [J | J]; subst.
      destruct p.
      assert (In (t, a, PI_id pinfo) ((t, a, PI_id pinfo) :: la)) as J.
        simpl. auto.
      apply H in J. auto.

      apply IHla in J; auto.
      intros. eapply H; simpl; eauto.
Qed.
