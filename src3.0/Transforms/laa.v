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
Require Import alive_alloca.
Require Import subst_inv.
Require Import vmem2reg.
Require Import memory_props.
Require Import trans_tactic.
Require Import top_sim.
Require Import partitioning.

(* 
   The load can use a different alignment from (PI_align pinfo).
   See the comments in alive_store.
*)

Definition laa (lid: id) (lalign:align) (cs2:cmds) (b:block) (pinfo:PhiInfo) 
  : Prop :=
partitioning 
    (insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo) (PI_align pinfo))
    (insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) lalign)
    cs2 b pinfo
    (fun cs2 pinfo => store_in_cmds (PI_id pinfo) cs2 = false).

Record LAAInfo (pinfo: PhiInfo) := mkLAAInfo {
  LAA_lid : id;
  LAA_lalign : align;
  LAA_tail : cmds;
  LAA_block : block;
  LAA_prop : laa LAA_lid LAA_lalign LAA_tail LAA_block pinfo
}.

Ltac destruct_laainfo :=
match goal with
| laainfo: LAAInfo _ |- _ =>
  destruct laainfo as [LAA_lid0 LAA_lalign0 LAA_tail0
                       [LAA_l0 [LAA_ps0 LAA_cs0 LAA_tmn0]] LAA_prop0];
  destruct LAA_prop0 as 
    [LAA_BInF0 [LAA_stincmds0 [LAA_cs1 [LAA_cs3 LAA_EQ]]]]; subst; simpl
end.

Ltac destruct_laainfo' :=
match goal with
| laainfo: LAAInfo _ |- _ =>
  destruct laainfo as [LAA_lid0 LAA_lalign0 LAA_tail0
                       [LAA_l0 [LAA_ps0 LAA_cs0 LAA_tmn0]] LAA_prop0]; simpl
end.

Lemma lookup_LAA_lid__load: forall pinfo laainfo
  (Huniq: uniqFdef (PI_f pinfo)),
  lookupInsnViaIDFromFdef (PI_f pinfo) (LAA_lid pinfo laainfo) =
    ret insn_cmd
          (insn_load (LAA_lid pinfo laainfo) (PI_typ pinfo) 
             (value_id (PI_id pinfo)) (LAA_lalign pinfo laainfo)).
Proof.
  intros.
  destruct_laainfo'.
  eapply par_lookup_id2__c2 in LAA_prop0; eauto.
Qed.  

Lemma laa__alive_alloca: forall lid lalign cs2 b pinfo
  (H: laa lid lalign cs2 b pinfo),
  alive_alloca (cs2 ++
    [insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) lalign])
    b pinfo.
Proof.
  unfold laa. unfold alive_alloca.
  intros. destruct b as [? []].
  destruct H as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
  split; auto.
  split.
    apply store_in_cmds_merge.
    split; auto.

    exists cs1. exists cs3. simpl_env. auto.
Qed.

Lemma laainfo__alinfo: forall pinfo (laainfo: LAAInfo pinfo),
  { alinfo: AllocaInfo pinfo |
    AI_block pinfo alinfo = LAA_block pinfo laainfo /\
    AI_tail pinfo alinfo =
      LAA_tail pinfo laainfo ++
      [insn_load (LAA_lid pinfo laainfo) (PI_typ pinfo) (value_id (PI_id pinfo))
        (LAA_lalign pinfo laainfo)] }.
Proof.
  intros.
  destruct laainfo. simpl.
  apply laa__alive_alloca in LAA_prop0.
  exists (mkAllocaInfo
    pinfo
    (LAA_tail0 ++
     [insn_load LAA_lid0 (PI_typ pinfo) (value_id (PI_id pinfo))
        LAA_lalign0]) LAA_block0 LAA_prop0).
  auto.
Defined.

Notation "[! pinfo !]" :=
  (value_const (const_undef (PI_typ pinfo))) (at level 0).

Lemma LAA_block_spec: forall (pinfo : PhiInfo) (laainfo : LAAInfo pinfo)
  (CurCmds : list cmd) (Terminator : terminator) (l' : l) (ps' : phinodes)
  (cs' : list cmd) (Huniq: uniqFdef (PI_f pinfo))
  (HbInF : blockInFdefB
            (l', stmts_intro ps'
               (cs' ++
                insn_load (LAA_lid pinfo laainfo) (PI_typ pinfo)
                  (value_id (PI_id pinfo)) (LAA_lalign pinfo laainfo) :: CurCmds)
               Terminator) (PI_f pinfo) = true),
  (l', stmts_intro ps'
     (cs' ++
      insn_load (LAA_lid pinfo laainfo) (PI_typ pinfo)
        (value_id (PI_id pinfo)) (LAA_lalign pinfo laainfo) :: CurCmds) 
     Terminator) =
  LAA_block pinfo laainfo.
Proof.
  intros.
  destruct_laainfo'.
  eapply par_block_eq2 in HbInF; eauto.
Qed.  

Lemma LAA_lid__in_LAA_block_IDs: forall pinfo laainfo,
  In (LAA_lid pinfo laainfo) (getStmtsIDs (snd (LAA_block pinfo laainfo))).
Proof.
  intros.
  destruct_laainfo'.
  eapply par_id2__in_block_IDs in LAA_prop0; eauto.
Qed.

Lemma lookup_LAA_lid__LAA_block: forall pinfo laainfo 
  (Huniq: uniqFdef (PI_f pinfo)),
  lookupBlockViaIDFromFdef (PI_f pinfo) (LAA_lid pinfo laainfo)
    = Some (LAA_block pinfo laainfo).
Proof.
  intros.
  destruct_laainfo'.
  eapply par_lookup_id2__block in LAA_prop0; eauto.
Qed.

Lemma PI_id__dominates__LAA_lid: forall S m pinfo laainfo
  (HwfF: wf_fdef S m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo))
  (Hreach: isReachableFromEntry (PI_f pinfo) (LAA_block pinfo laainfo))
  (Hwfpi: WF_PhiInfo pinfo),
    valueDominates (PI_f pinfo) (value_id (PI_id pinfo)) 
      (value_id (LAA_lid pinfo laainfo)).
Proof.
  intros.
  assert (Hlksid:=@lookup_LAA_lid__LAA_block pinfo laainfo Huniq).
  destruct_laainfo. simpl in *.
  unfold idDominates.
  match goal with
  | LAS_BInF0: blockInFdefB ?b0 _ = true |- _ =>
    assert (J:=@inscope_of_id__total (PI_f pinfo) b0 LAA_lid0);
    remember (inscope_of_id (PI_f pinfo) b0 LAA_lid0) as R;
    destruct R; try congruence
  end.
  rewrite Hlksid. rewrite <- HeqR.
  match goal with
  | H : context [_++_::_++?c0::_] |- _ =>
      eapply cmd_operands__in_scope' with (c:=c0) in HeqR; eauto 1; 
        try solve [simpl; auto | solve_in_list]
  end.
Qed.

Lemma LAA_block__reachable: forall (pinfo : PhiInfo) (laainfo : LAAInfo pinfo)
  (Huniq : uniqFdef (PI_f pinfo))
  (Hreach : isReachableFromEntry (PI_f pinfo) (LAA_block pinfo laainfo)),
  forall b2 : block,
    lookupBlockViaIDFromFdef (PI_f pinfo) (LAA_lid pinfo laainfo) = ret b2 ->
    isReachableFromEntry (PI_f pinfo) b2.
Proof.
  intros.
  rewrite lookup_LAA_lid__LAA_block in H; auto.
  inv H. auto.
Qed.

Lemma laa__alive_alloca__vev_EC: forall pinfo laainfo los nts M gl ps ec s 
  (Hwfs: wf_system s) (Hwfg: wf_global (los,nts) s gl) (Hwfpi: WF_PhiInfo pinfo)
  (HmInS: moduleInSystemB (module_intro los nts ps) s = true)
  (Hwfpp: OpsemPP.wf_ExecutionContext (los,nts) ps ec) alinfo Hp
  (Hlaa2al : exist _ alinfo Hp = laainfo__alinfo pinfo laainfo),
  alive_alloca.wf_ExecutionContext pinfo alinfo (los,nts) M gl ec ->
  vev_ExecutionContext (value_id (LAA_lid pinfo laainfo))
    [! pinfo !] (PI_f pinfo) (los,nts) M gl ec.
Proof.
  intros. clear Hlaa2al.
  destruct Hp as [J3 J4].
  intros.
  destruct ec. simpl in *.
  destruct CurCmds; auto.

  destruct Hwfpp as
    [Hreach [HbInF [HfInPs [_ [Hinscope [l' [ps' [cs' EQ]]]]]]]]; subst.

  remember (inscope_of_cmd CurFunction
                 (l', stmts_intro ps' (cs' ++ c :: CurCmds) Terminator) c) as R.
  destruct R; auto.

  assert (uniqFdef CurFunction) as Huniq.
    eapply wf_system__uniqFdef; eauto.
  assert (wf_fdef s (module_intro los nts ps) CurFunction) as HwfF.
    eapply wf_system__wf_fdef; eauto.

  assert (Hnodup:=HbInF).
  apply uniqFdef__blockInFdefB__nodup_cmds in Hnodup; auto.

  intros G1; subst.
  intro G1.

  remember (Opsem.getOperandValue (los,nts) [! pinfo !] Locals gl) as R.
  destruct R; auto.
  destruct (LAA_lid pinfo laainfo == getCmdLoc c); auto.

  assert (c = insn_load (LAA_lid pinfo laainfo) (PI_typ pinfo)
             (value_id (PI_id pinfo)) (LAA_lalign pinfo laainfo)) as EQ.
      eapply IngetCmdsIDs__lookupCmdViaIDFromFdef with (c1:=c) in HbInF; eauto
        using in_middle.
      apply lookup_LAA_lid__load with (laainfo:=laainfo) in Huniq; auto.
      congruence.
  subst.

  assert ((l', stmts_intro ps'
              (cs' ++ insn_load (LAA_lid pinfo laainfo)
                            (PI_typ pinfo) (value_id (PI_id pinfo))
                            (LAA_lalign pinfo laainfo) :: CurCmds) Terminator) =
              AI_block pinfo alinfo) as Heq.
    clear H Hinscope HeqR Hreach.
    transitivity (LAA_block pinfo laainfo); auto.
    eapply LAA_block_spec; eauto.

  assert (alive_alloca.wf_defs pinfo alinfo (los,nts) M gl Locals) as G.
    clear Hinscope Hreach.
    apply H; auto.
      clear H.
      destruct alinfo. simpl in *. subst.
      destruct (LAA_block pinfo laainfo) as [? []].
      assert (AI_alive':=AI_alive).
      destruct AI_alive' as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
      inv Heq.
      assert (
          cs' = cs1 ++
                insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo)
                  (PI_align pinfo) :: (LAA_tail pinfo laainfo) /\
          CurCmds = cs3
          ) as EQ.
        clear - H2 Hnodup.
        match goal with
        | H: context [?A ++ ?b :: (?C ++ [?d]) ++ ?E] |- _ =>
           rewrite_env ((A ++ b :: C) ++ d :: E) in H
        end. 
        apply NoDup_cmds_split_middle in H2; auto.

      destruct EQ; subst. clear H2.
      unfold follow_alive_alloca. simpl.
      intros.
      assert (cs1 = cs0 /\ cs3 = cs2) as EQ.
        clear - H Hnodup.
        match goal with
        | H: ?A1 ++ ?b1 :: (?C1 ++ [?d1]) ++ ?E1 =
             ?A2 ++ ?b2 :: (?C2 ++ [?d2]) ++ ?E2 |- _ =>
          rewrite_env ((A1 ++ b1 :: C1) ++ d1 :: E1) in H;
          rewrite_env ((A2 ++ b2 :: C2) ++ d2 :: E2) in H
        end.
        apply NoDup_cmds_split_middle in H; auto.
        destruct H as [H1 H2].
        split; auto.
          apply app_inv_tail in H1; auto.

      destruct EQ; subst. clear H.
      exists (LAA_tail pinfo laainfo).
      exists ([insn_load (LAA_lid pinfo laainfo) (PI_typ pinfo)
                   (value_id (PI_id pinfo)) (LAA_lalign pinfo laainfo)]).
      auto.

  simpl.
  unfold alive_alloca.wf_defs in G.
  assert (exists gvsa, exists gvsv,
    lookupAL (GVsT DGVs) Locals (PI_id pinfo) = ret gvsa /\
    Opsem.getOperandValue (los,nts) [! pinfo !] Locals gl =
      ret gvsv) as G2.
    rewrite Heq in *. rewrite J3 in Hreach.
    clear - Hinscope HeqR HwfF Hwfg Huniq Hwfpi Heq HbInF Hreach.
    assert (List.In (PI_id pinfo) l0) as Hin.
      (* pid >> LAA_lid *)
      eapply PI_id__dominates__LAA_lid with (laainfo:=laainfo) in HwfF; eauto.
      simpl in HwfF.
      assert (forall b2 : block,
        lookupBlockViaIDFromFdef (PI_f pinfo) (LAA_lid pinfo laainfo) =
        ret b2 -> isReachableFromEntry (PI_f pinfo) b2) as Hreach'.
        apply LAA_block__reachable; auto.
      apply_clear HwfF in Hreach'.
      unfold idDominates in Hreach'. unfold inscope_of_cmd in HeqR. simpl in HeqR.
      inv_mbind. symmetry_ctx.
      assert (b = AI_block pinfo alinfo) as HeqB.
        eapply block_eq2 with (id1:=LAA_lid pinfo laainfo) ; eauto 1.
          solve_blockInFdefB.
          solve_in_list.

          rewrite <- Heq. simpl. apply in_or_app. right. apply in_or_app. left. 
          rewrite getCmdsLocs_app. simpl. solve_in_list.
      subst. congruence.

    eapply OpsemPP.wf_defs_elim in Hin; eauto.
    destruct Hin as [? [? [gvs1 [? [Hin ?]]]]].
    simpl.
    assert (wf_const s (los,nts) (const_undef (PI_typ pinfo)) (PI_typ pinfo)) 
      as Hwfc.
      constructor. eapply WF_PhiInfo_spec21; eauto.
    eapply (@OpsemPP.const2GV_isnt_stuck DGVs) in Hwfc; eauto.
    destruct Hwfc as [gvsv Hwfc]. 
    eauto.
  destruct G2 as [gvsa [gvsv [G3 G2]]].
  exists gvsa. exists gvsa. exists gvsv.
  split; auto.
  split; auto.
    rewrite G2 in HeqR0. inv HeqR0.
    eapply G in G2; eauto.
Qed.

(* it is same to laa's *)
Lemma laa__alive_alloca__vev_ECStack: forall pinfo laainfo los nts M gl ps s
  (Hwfs: wf_system s) stinfo Hp (Hwfg: wf_global (los,nts) s gl)
  (HmInS: moduleInSystemB (module_intro los nts ps) s = true)
  (Hlas2st : exist _ stinfo Hp = laainfo__alinfo pinfo laainfo)
  ECs (Hwfpp: OpsemPP.wf_ECStack (los,nts) ps ECs) (Hwfpi: WF_PhiInfo pinfo),
  alive_alloca.wf_ECStack pinfo stinfo (los,nts) M gl ECs ->
  vev_ECStack (value_id (LAA_lid pinfo laainfo)) [! pinfo !]
    (PI_f pinfo) (los,nts) M gl ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct H as [J1 J2].
    destruct Hwfpp as [HwfEC [HwfStk Hwfcall]].
    split; eauto.
      eapply laa__alive_alloca__vev_EC; eauto.
Qed.

(* it is same to laa's *)
Lemma laa__alive_alloca__vev: forall pinfo laainfo cfg S
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S) stinfo Hp
  (Hlas2st : exist _ stinfo Hp = laainfo__alinfo pinfo laainfo)
  (Hwfpi: WF_PhiInfo pinfo),
  alive_alloca.wf_State pinfo stinfo cfg S ->
  vev_State (value_id (LAA_lid pinfo laainfo)) [! pinfo !]
    (PI_f pinfo) cfg S.
Proof.
  intros.
  destruct cfg, S.
  destruct CurTargetData as [los nts].
  destruct Hwfcfg as [_ [Hwfg [Hwfs HmInS]]].
  destruct Hwfpp as [Hnempty Hstks].
  unfold alive_alloca.wf_State in H.
  simpl in H. simpl.
  eapply laa__alive_alloca__vev_ECStack; eauto.
Qed.
