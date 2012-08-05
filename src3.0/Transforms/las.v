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
Require Import palloca_props.
Require Import alive_store.
Require Import subst_inv.
Require Import vmem2reg.
Require Import memory_props.
Require Import trans_tactic.
Require Import top_sim.

(* We define a special las used by vmem2reg that only considers local commands.
   In general, it should be extended to the las defined w.r.t domination and
   memory dependency (which we are aiming in the future work)

   The current vmem2reg also does SAS eliminations before all loads are removed.
   For example,
     st v1 p; ...; st v2 p; ...
   if there are no other lds in the first ..., the first ``st v1 p'' can be
   removed.

   In practice, such a code after phiplacement may exist if the original code
   also does store to the promotable alloca.

   An alternative approach is that we only consider such elimination after all
   possible removed loads are removed, as what the paper presents. vmem2reg does
   not check if there are any unremoved loads in unreachable blocks. If so,
   some stores cannot be removed. We need to let vmem2reg ignore the loads of
   unreachable blocks to remove what SAS can eliminate.

   For this reason, here, we give the abstract properties that las needs to hold.
   The properties do not depend on the concrete design in vmem2reg, such as
   find_init_stld, find_next_stld, ... So the proofs can still work if we change
   vmem2reg. We should prove that the design in vmem2reg satisfy the properties.

   We allow the pair of load/store use different alignments from the 
   promotable's. See the comments in alive_store
 *)

Definition las (lid sid: id) (lalign salign: align) (v:value) (cs2:cmds) 
  (b:block) (pinfo:PhiInfo) : Prop :=
blockInFdefB b (PI_f pinfo) = true /\
store_in_cmds (PI_id pinfo) cs2 = false /\
let '(_, stmts_intro _ cs _) := b in
exists cs1, exists cs3,
  cs =
  cs1 ++
  insn_store sid (PI_typ pinfo) v (value_id (PI_id pinfo)) salign ::
  cs2 ++
  insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) lalign ::
  cs3.

Record LASInfo (pinfo: PhiInfo) := mkLASInfo {
  LAS_lid : id;
  LAS_sid : id;
  LAS_lalign : align;
  LAS_salign : align;
  LAS_value : value;
  LAS_tail : cmds;
  LAS_block : block;
  LAS_prop : las LAS_lid LAS_sid LAS_lalign LAS_salign LAS_value LAS_tail 
               LAS_block pinfo
}.

Ltac destruct_lasinfo :=
match goal with
| lasinfo: LASInfo _ |- _ =>
  destruct lasinfo as [LAS_lid0 LAS_sid0 LAS_lalign0 LAS_salign0 LAS_value0 
                       LAS_tail0 [LAS_l0 [LAS_ps0 LAS_cs0 LAS_tmn0]] LAS_prop0];
  destruct LAS_prop0 as 
    [LAS_BInF0 [LAS_stincmds0 [LAS_cs1 [LAS_cs3 LAS_EQ]]]]; subst; simpl
end.

Lemma lookup_LAS_lid__load: forall pinfo lasinfo
  (Huniq: uniqFdef (PI_f pinfo)),
  lookupInsnViaIDFromFdef (PI_f pinfo) (LAS_lid pinfo lasinfo) =
    ret insn_cmd
          (insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo) 
             (value_id (PI_id pinfo)) (LAS_lalign pinfo lasinfo)).
Proof.
  intros.
  destruct_lasinfo.
  match goal with 
  | H: context [?A1++?a2::?A3++?a4::?A5] |- _ =>
       rewrite_env ((A1++a2::A3)++a4::A5) in H;
       eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H; 
         eauto using in_middle
  end.
  auto.
Qed.  

Lemma LAS_lid__in_LAS_block_IDs: forall pinfo lasinfo,
  In (LAS_lid pinfo lasinfo) (getStmtsIDs (snd (LAS_block pinfo lasinfo))).
Proof.
  intros.
  destruct_lasinfo.
  apply in_or_app. right.
  rewrite getCmdsIDs_app. apply in_or_app. right.
  simpl.
  rewrite getCmdsIDs_app. apply in_or_app. right.
  simpl. auto.
Qed.

Lemma lookup_LAS_sid__store: forall pinfo lasinfo
  (Huniq: uniqFdef (PI_f pinfo)),
  lookupInsnViaIDFromFdef (PI_f pinfo) (LAS_sid pinfo lasinfo) =
    ret insn_cmd
      (insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo) 
        (LAS_value pinfo lasinfo) (value_id (PI_id pinfo)) 
        (LAS_salign pinfo lasinfo)).
Proof.
  intros.
  destruct_lasinfo.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in LAS_BInF0;eauto using in_middle.
  simpl in LAS_BInF0. auto.
Qed.

Lemma LAS_value_is_substing: forall S m pinfo lasinfo
  (Huniq : uniqFdef (PI_f pinfo)) (HwfF : wf_fdef S m (PI_f pinfo)),
  substing_value (PI_f pinfo) (LAS_value pinfo lasinfo).
Proof. 
  unfold substing_value. 
  intros.
  destruct_lasinfo.
  eapply wf_fdef__wf_cmd in LAS_BInF0; eauto using in_middle.
  inv LAS_BInF0. 
  destruct (LAS_value0) as [vid|]; auto.
  match goal with
  | H7: wf_value _ _ _ (value_id vid) _ |- _ => inv H7
  end.
  match goal with
  | H8: lookupTypViaIDFromFdef _ _ = _ |- _ => 
    apply lookupTypViaIDFromFdef_elim' in H8; auto;
    destruct H8 as [H8 | [instr [J1 [J2 J3]]]]; eauto
  end.
Qed.

Lemma LAS_value__exists: forall pinfo lasinfo s m 
  (HwfF: wf_fdef s m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo)),
  match LAS_value pinfo lasinfo with
  | value_id vid =>
      In vid (getArgsIDsOfFdef (PI_f pinfo)) \/
      (isReachableFromEntry (PI_f pinfo) (LAS_block pinfo lasinfo) ->
       exists instr, 
        lookupInsnViaIDFromFdef (PI_f pinfo) vid = ret instr /\
        getInsnID instr = Some vid)
  | _ => True
  end.
Proof.
  intros.
  destruct_lasinfo.
  eapply wf_fdef__wf_cmd in LAS_BInF0; eauto using in_middle.
  inv LAS_BInF0. 
  match goal with
  | H11: wf_insn_base _ _ _ |- _ => inv H11
  end.
  destruct (LAS_value0) as [vid|]; auto.
  find_wf_operand_list.
  match goal with
  | H5: getInsnOperands (insn_cmd ?c) = _, H6: wf_operand_list _,
    H: insnInFdefBlockB _ _ ?b = true |- _ =>
    apply wf_operand_list__elim with (f1:=PI_f pinfo)(b1:=b)
      (insn1:=insn_cmd c) (id1:=vid)
      in H6; try solve [
        auto |
        apply make_list_fdef_block_insn_id_spec; try solve 
          [match goal with
           | EQ: ?A = ?B |- In _ ?B => rewrite <- EQ; simpl; auto
           end]
        ];
    inv H6
  end.
  match goal with
  | H10: ( _ \/ _ ) \/ _ |- _ => 
    destruct H10 as [[[block' [H10 G]] | H10] | H10]; try solve 
      [eauto |
       right; intro;
       eapply lookupBlockViaIDFromFdef__lookupInsnViaIDFromFdef; eauto |
       right; intro; simpl in H10; congruence
      ]
  end.
Qed.

Lemma LAS_value_PI_id__dominate__LAS_sid: forall S m pinfo lasinfo
  (HwfF: wf_fdef S m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo))
  (Hreach: isReachableFromEntry (PI_f pinfo) (LAS_block pinfo lasinfo)) ids0
  (Hinscope: Some ids0 = inscope_of_id (PI_f pinfo) (LAS_block pinfo lasinfo) 
               (LAS_sid pinfo lasinfo)),
  value_in_scope (LAS_value pinfo lasinfo) ids0 /\
  value_in_scope (value_id (PI_id pinfo)) ids0.
Proof.
  intros.
Local Opaque inscope_of_id.
  destruct_lasinfo. simpl in *.
  unfold idDominates.
  destruct LAS_value0 as [LAS_vid0|]; simpl; split; try solve [
    auto |
    match goal with
    | HeqR : _ = inscope_of_id _ _ _, H : context [_++?c0::_++_::_] |- _ =>
      eapply cmd_operands__in_scope' with (c:=c0) in HeqR; eauto 1; 
        try solve [simpl; auto | solve_in_list]
    end
  ].
Transparent inscope_of_id.
Qed.

Lemma LAS_value__dominates__LAS_sid: forall S m pinfo lasinfo
  (HwfF: wf_fdef S m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo))
  (Hreach: isReachableFromEntry (PI_f pinfo) (LAS_block pinfo lasinfo)) ids0
  (Hinscope: Some ids0 = inscope_of_id (PI_f pinfo) (LAS_block pinfo lasinfo) 
               (LAS_sid pinfo lasinfo)),
  value_in_scope (LAS_value pinfo lasinfo) ids0.
Proof.
  intros.
  eapply LAS_value_PI_id__dominate__LAS_sid; eauto.
Qed.

Lemma PI_id__dominates__LAS_sid: forall S m pinfo lasinfo
  (HwfF: wf_fdef S m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo))
  (Hreach: isReachableFromEntry (PI_f pinfo) (LAS_block pinfo lasinfo)) ids0
  (Hinscope: Some ids0 = inscope_of_id (PI_f pinfo) (LAS_block pinfo lasinfo) 
               (LAS_sid pinfo lasinfo)),
  value_in_scope (value_id (PI_id pinfo)) ids0.
Proof.
  intros.
  eapply LAS_value_PI_id__dominate__LAS_sid; eauto.
Qed.

Lemma LAS_value_PI_id__dominate__LAS_lid: forall S m pinfo lasinfo
  (HwfF: wf_fdef S m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo)),
  valueDominates (PI_f pinfo) (LAS_value pinfo lasinfo) 
    (value_id (LAS_lid pinfo lasinfo)) /\
  valueDominates (PI_f pinfo) (value_id (PI_id pinfo)) 
    (value_id (LAS_lid pinfo lasinfo)).
Proof.
Local Opaque inscope_of_id.
  intros.
  assert (Hin:=@LAS_lid__in_LAS_block_IDs pinfo lasinfo).
  assert (Hlkst:=lookup_LAS_sid__store pinfo lasinfo Huniq).
  assert (Hsval:=@LAS_value__exists pinfo lasinfo _ _ HwfF Huniq).
  assert (Hidom12:=
            @LAS_value_PI_id__dominate__LAS_sid S m pinfo lasinfo HwfF 
              Huniq).
  destruct_lasinfo. simpl in *.
  unfold valueDominates, idDominates, id_in_reachable_block.
  match goal with
  | LAS_BInF0: blockInFdefB ?b0 _ = true |- _ =>
    rewrite inGetBlockIDs__lookupBlockViaIDFromFdef with (b:=b0); auto;
    assert (J:=@inscope_of_id__total (PI_f pinfo) b0 LAS_lid0);
    remember (inscope_of_id (PI_f pinfo) b0 LAS_lid0) as R;
    destruct R; try congruence;
    assert (J':=@inscope_of_id__total (PI_f pinfo) b0 LAS_sid0);
    remember (inscope_of_id (PI_f pinfo) b0 LAS_sid0) as R';
    destruct R'; try congruence;
    assert (NoDup (getStmtsLocs (snd b0))) as Hnodup; try solve [solve_NoDup]
  end.
  eapply inscope_of_id__append_cmds in HeqR; eauto.
  clear Hin.
  repeat match goal with
  | H: context [?A ++ ?b :: ?C ++ ?d :: ?E] |- _ =>
        rewrite_env ((A ++ b :: C) ++ d :: E) in H
  end. 
  destruct LAS_value0 as [LAS_vid0|]; try solve [simpl; auto];
    split; try solve [
      auto |
      intro Hreach0;
      match goal with
      | Hdom12: reachable ?f ?l0 -> _,
        Hreach0: forall _:_, Some (?l0, stmts_intro ?ps ?cs ?tmn) = _ -> 
                 isReachableFromEntry ?f _ |- _ =>
        assert (isReachableFromEntry f (l0, stmts_intro ps cs tmn)) as Hreach; 
        eauto; simpl in Hreach;
        simpl in Hdom12; edestruct Hdom12 as [Hdom1 Hdom2]; eauto;
        apply HeqR; solve_in_list
      end
   ].
Transparent inscope_of_id.
Qed.

Lemma LAS_value__dominates__LAS_lid: forall S m pinfo lasinfo
  (HwfF: wf_fdef S m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo)),
  valueDominates (PI_f pinfo) (LAS_value pinfo lasinfo) 
    (value_id (LAS_lid pinfo lasinfo)).
Proof.
  intros.
  eapply LAS_value_PI_id__dominate__LAS_lid; eauto.
Qed.

Lemma PI_id__dominates__LAS_lid: forall S m pinfo lasinfo
  (HwfF: wf_fdef S m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo)),
   valueDominates (PI_f pinfo) (value_id (PI_id pinfo)) 
      (value_id (LAS_lid pinfo lasinfo)).
Proof.
  intros.
  eapply LAS_value_PI_id__dominate__LAS_lid; eauto.
Qed.

Lemma LAS_substable_values : forall S los nts Ps gl pinfo lasinfo
  (Huniq: uniqFdef (PI_f pinfo)) 
  (HwfF: wf_fdef S (module_intro los nts Ps) (PI_f pinfo)),
  substable_values (los,nts) gl (PI_f pinfo) (value_id (LAS_lid pinfo lasinfo))
    (LAS_value pinfo lasinfo).
Proof.
  intros.
  split. simpl. rewrite lookup_LAS_lid__load; simpl; auto.
  split. eapply LAS_value_is_substing; eauto.
  split; auto.
    eapply LAS_value__dominates__LAS_lid; eauto.
Qed.

Lemma las__alive_store: forall lid sid lal sal v cs2 b pinfo,
  las lid sid lal sal v cs2 b pinfo ->
  alive_store sid sal v (cs2 ++
    [insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) lal]) b pinfo.
Proof.
  unfold las. unfold alive_store.
  intros. destruct b as [? []].
  destruct H as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
  split; auto.
  split.
    apply store_in_cmds_merge.
    split; auto.

    exists cs1. exists cs3. simpl_env. auto.
Qed.

Lemma lasinfo__stinfo: forall pinfo (lasinfo: LASInfo pinfo),
  { stinfo: StoreInfo pinfo |
    SI_id pinfo stinfo = LAS_sid pinfo lasinfo /\
    SI_align pinfo stinfo = LAS_salign pinfo lasinfo /\
    SI_value pinfo stinfo = LAS_value pinfo lasinfo /\
    SI_block pinfo stinfo = LAS_block pinfo lasinfo /\
    SI_tail pinfo stinfo =
      LAS_tail pinfo lasinfo ++
      [insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo) (value_id (PI_id pinfo))
        (LAS_lalign pinfo lasinfo)] }.
Proof.
  intros.
  destruct lasinfo. simpl.
  apply las__alive_store in LAS_prop0.
  exists (mkStoreInfo
    pinfo LAS_sid0 LAS_salign0 LAS_value0
    (LAS_tail0 ++
     [insn_load LAS_lid0 (PI_typ pinfo) (value_id (PI_id pinfo))
        LAS_lalign0]) LAS_block0 LAS_prop0).
  auto.
Defined.

Lemma LAS_block_spec: forall (pinfo : PhiInfo) (lasinfo : LASInfo pinfo)
  (CurCmds : list cmd) (Terminator : terminator) (l' : l) (ps' : phinodes)
  (cs' : list cmd) (Huniq: uniqFdef (PI_f pinfo))
  (Hnodup : NoDup
             (getCmdsLocs
                (cs' ++
                 insn_load (LAS_lid pinfo lasinfo) 
                   (PI_typ pinfo) (value_id (PI_id pinfo)) 
                   (LAS_lalign pinfo lasinfo) :: CurCmds)))
  (HbInF : blockInFdefB
            (l', stmts_intro ps'
               (cs' ++
                insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
                  (value_id (PI_id pinfo)) (LAS_lalign pinfo lasinfo) :: CurCmds)
               Terminator) (PI_f pinfo) = true),
  (l', stmts_intro ps'
     (cs' ++
      insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
        (value_id (PI_id pinfo)) (LAS_lalign pinfo lasinfo) :: CurCmds) Terminator) =
  LAS_block pinfo lasinfo.
Proof.
  intros.
  assert (In
    (LAS_lid pinfo lasinfo)
    (getStmtsIDs
      (stmts_intro ps'
        (cs' ++
          insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
          (value_id (PI_id pinfo)) (LAS_lalign pinfo lasinfo) :: CurCmds)
        Terminator))) as Hin.
    simpl.
    rewrite getCmdsIDs_app.
    simpl.
    rewrite_env ((getPhiNodesIDs ps' ++ getCmdsIDs cs') ++
                  LAS_lid pinfo lasinfo :: getCmdsIDs CurCmds).
    apply in_middle.
  
  apply inGetBlockIDs__lookupBlockViaIDFromFdef with
    (id1:=LAS_lid pinfo lasinfo) in HbInF; auto.
  clear Hin.
  destruct lasinfo. simpl in *.
  destruct LAS_block0 as [l1 [p ? t]].
  destruct LAS_prop0 as [J1 [J2 [cs1 [cs3 J3]]]]. subst.
  assert (In LAS_lid0
    (getStmtsIDs
      (stmts_intro p
         (cs1 ++
          insn_store LAS_sid0 (PI_typ pinfo)
            LAS_value0 (value_id (PI_id pinfo)) LAS_salign0
          :: (LAS_tail0 ++
              [insn_load LAS_lid0
                 (PI_typ pinfo) (value_id (PI_id pinfo))
                 LAS_lalign0] ++ cs3)) t))) as Hin.
    simpl.
    apply in_or_app. right.
    rewrite getCmdsIDs_app.
    apply in_or_app. right.
    simpl. rewrite getCmdsIDs_app.
    apply in_or_app. right. simpl. auto.
  
  eapply inGetBlockIDs__lookupBlockViaIDFromFdef with
    (id1:=LAS_lid0) in J1; eauto.
  rewrite HbInF in J1. inv J1. auto.
Qed.

Lemma lookup_LAS_lid__LAS_block: forall pinfo lasinfo
  (Huniq: uniqFdef (PI_f pinfo)),
  lookupBlockViaIDFromFdef (PI_f pinfo) (LAS_lid pinfo lasinfo) =
    ret (LAS_block pinfo lasinfo).
Proof.
  intros.
  apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
    apply LAS_lid__in_LAS_block_IDs.
    destruct_lasinfo. auto.
Qed.

Lemma LAS_block__reachable: forall (pinfo : PhiInfo) (lasinfo : LASInfo pinfo)
  (Huniq : uniqFdef (PI_f pinfo))
  (Hreach : isReachableFromEntry (PI_f pinfo) (LAS_block pinfo lasinfo)),
  id_in_reachable_block (PI_f pinfo) (LAS_lid pinfo lasinfo).
Proof.
  unfold id_in_reachable_block. intros.
  rewrite lookup_LAS_lid__LAS_block in H; auto.
  inv H. auto.
Qed.

Lemma las__alive_store__vev_EC: forall pinfo lasinfo los nts M gl ps ec s 
  (Hwfs: wf_system s)
  (HmInS: moduleInSystemB (module_intro los nts ps) s = true)
  (Hwfpp: OpsemPP.wf_ExecutionContext (los,nts) ps ec) stinfo Hp
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo),
  alive_store.wf_ExecutionContext pinfo stinfo (los,nts) M gl ec ->
  vev_ExecutionContext (value_id (LAS_lid pinfo lasinfo))
    (LAS_value pinfo lasinfo) (PI_f pinfo) (los,nts) M gl ec.
Proof.
  intros. clear Hlas2st.
  destruct Hp as [J1 [J5 [J2 [J3 J4]]]].
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
  remember (Opsem.getOperandValue (los,nts) (LAS_value pinfo lasinfo)
      Locals gl) as R.
  destruct R; auto.
  destruct (LAS_lid pinfo lasinfo == getCmdLoc c); auto.

  assert (c = insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
             (value_id (PI_id pinfo)) (LAS_lalign pinfo lasinfo)) as EQ.
      clear - HbInF J3 J1 J2 J4 e Huniq.
      eapply IngetCmdsIDs__lookupCmdViaIDFromFdef with (c1:=c) in HbInF; eauto
        using in_middle.
      apply lookup_LAS_lid__load with (lasinfo:=lasinfo) in Huniq; auto.
      congruence.
  subst.

  assert ((l', stmts_intro ps'
              (cs' ++ insn_load (LAS_lid pinfo lasinfo)
                            (PI_typ pinfo) (value_id (PI_id pinfo))
                            (LAS_lalign pinfo lasinfo) :: CurCmds) Terminator) =
              SI_block pinfo stinfo) as Heq.
    transitivity (LAS_block pinfo lasinfo); auto.
    eapply LAS_block_spec; eauto.

  assert (alive_store.wf_defs pinfo stinfo (los,nts) M gl Locals) as G.
    clear Hinscope Hreach.
    apply H; auto.
      clear H.
      destruct stinfo. simpl in *. subst.
      destruct (LAS_block pinfo lasinfo) as [? []].
      assert (SI_alive':=SI_alive).
      destruct SI_alive' as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
      inv Heq. 
      assert (
          cs' = cs1 ++
                insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
                  (LAS_value pinfo lasinfo) (value_id (PI_id pinfo))
                  (LAS_salign pinfo lasinfo) :: (LAS_tail pinfo lasinfo) /\
          CurCmds = cs3
          ) as EQ.
        clear - H2 Hnodup.
        match goal with
        | H2: _ = ?A ++ ?b :: (?C ++ [?d]) ++ ?E |- _ =>
          rewrite_env ((A ++ b :: C) ++ d :: E) in H2
        end.
        apply NoDup_cmds_split_middle in H2; auto.

      destruct EQ; subst. clear H2.
      unfold follow_alive_store. simpl.
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
      exists (LAS_tail pinfo lasinfo).
      exists ([insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
                   (value_id (PI_id pinfo)) (LAS_lalign pinfo lasinfo)]).
      auto.

  simpl.
  unfold alive_store.wf_defs in G.
  assert (exists gvsa, lookupAL (GVsT DGVs) Locals (PI_id pinfo) = ret gvsa) as G2.
    rewrite Heq in *. rewrite J3 in Hreach.
    clear - Hinscope HeqR HwfF Huniq Heq HbInF Hreach.
    assert (List.In (PI_id pinfo) l0) as Hin.
      (* pid >> LAS_lid *)
      eapply PI_id__dominates__LAS_lid with (lasinfo:=lasinfo) in HwfF; eauto.
      simpl in HwfF.
      assert (forall b2 : block,
        lookupBlockViaIDFromFdef (PI_f pinfo) (LAS_lid pinfo lasinfo) =
        ret b2 -> isReachableFromEntry (PI_f pinfo) b2) as Hreach'.
        apply LAS_block__reachable; auto.
      apply_clear HwfF in Hreach'.
      unfold idDominates in Hreach'. unfold inscope_of_cmd in HeqR. simpl in HeqR.
      inv_mbind. symmetry_ctx.
      assert (b = SI_block pinfo stinfo) as HeqB.
        eapply block_eq2 with (id1:=LAS_lid pinfo lasinfo) ; eauto 1.
          solve_blockInFdefB.
          solve_in_list.

          rewrite <- Heq. simpl. apply in_or_app. right. apply in_or_app. left. 
          rewrite getCmdsLocs_app. simpl. solve_in_list.
      subst. congruence.

    eapply OpsemPP.wf_defs_elim in Hin; eauto.
    destruct Hin as [? [? [gvs1 [? [Hin ?]]]]].
    eauto.
  destruct G2 as [gvsa G2].
  rewrite J2 in G. assert (G2':=G2).
  eapply G in G2; eauto.
  exists gvsa. exists gvsa. exists g.
  split; auto.
Qed.

Lemma las__alive_store__vev_ECStack: forall pinfo lasinfo los nts M gl ps s
  (Hwfs: wf_system s) stinfo Hp 
  (HmInS: moduleInSystemB (module_intro los nts ps) s = true)
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo)
  ECs (Hwfpp: OpsemPP.wf_ECStack (los,nts) ps ECs),
  alive_store.wf_ECStack pinfo stinfo (los,nts) M gl ECs ->
  vev_ECStack (value_id (LAS_lid pinfo lasinfo)) (LAS_value pinfo lasinfo)
    (PI_f pinfo) (los,nts) M gl ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct H as [J1 J2].
    destruct Hwfpp as [HwfEC [HwfStk Hwfcall]].
    split; eauto.
      eapply las__alive_store__vev_EC; eauto.
Qed.

Lemma las__alive_store__vev: forall pinfo lasinfo cfg S
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S) stinfo Hp
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo),
  alive_store.wf_State pinfo stinfo cfg S ->
  vev_State (value_id (LAS_lid pinfo lasinfo)) (LAS_value pinfo lasinfo)
    (PI_f pinfo) cfg S.
Proof.
  intros.
  destruct cfg, S.
  destruct CurTargetData as [los nts].
  destruct Hwfcfg as [_ [Hwfg [Hwfs HmInS]]].
  destruct Hwfpp as [Hnempty Hstks].
  unfold alive_store.wf_State in H.
  simpl in H. simpl.
  eapply las__alive_store__vev_ECStack; eauto.
Qed.

Lemma LAS_value_doms_LAS_lid__lid_in_tmn_scope____LAS_value_inscope: forall
  (s : system) (pinfo : PhiInfo) (lasinfo : LASInfo pinfo) (tmn : terminator)
  (l1 : l) (ps1 : phinodes) (cs1 : list cmd) (l0 : list atom) m
  (HwfF : wf_fdef s m (PI_f pinfo))
  (Huniq : uniqFdef (PI_f pinfo))
  (Hreach : isReachableFromEntry (PI_f pinfo) (l1, stmts_intro ps1 cs1 tmn))
  (Hreach': isReachableFromEntry (PI_f pinfo) (LAS_block pinfo lasinfo))
  (HbInF : blockInFdefB (l1, stmts_intro ps1 cs1 tmn) (PI_f pinfo) = true)
  (HeqR : ret l0 =
          inscope_of_tmn (PI_f pinfo) (l1, stmts_intro ps1 cs1 tmn) tmn)
  (Hin : In (LAS_lid pinfo lasinfo) l0),
  value_in_scope (LAS_value pinfo lasinfo) l0.
Proof.
  intros.
  assert (Hdom:=HwfF).
  apply LAS_value__dominates__LAS_lid with (lasinfo:=lasinfo) in Hdom; auto.
  assert (Hsval:=@LAS_value__exists pinfo lasinfo _ _ HwfF Huniq).
  destruct (LAS_value pinfo lasinfo); auto.
  simpl in Hdom. symmetry in HeqR.
  destruct Hsval as [Hinargs | [instr [Hlkc EQ]]]; subst; auto.
    eapply in_getArgsIDsOfFdef__inscope_of_tmn; eauto.

    assert (idDominates (PI_f pinfo) id5 (LAS_lid pinfo lasinfo)) as Hidom.
      apply Hdom. apply LAS_block__reachable; auto.
    eapply idDominates_inscope_of_tmn__inscope_of_tmn
        with (instr0:=insn_cmd 
               (insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo) 
                  (value_id (PI_id pinfo)) (LAS_lalign pinfo lasinfo))) 
      in HeqR; eauto 1.
      symmetry. apply lookup_LAS_lid__load; auto.
Qed.

Lemma LAS_block__reachable': forall (pinfo : PhiInfo) (lasinfo : LASInfo pinfo)
  (Huniq : uniqFdef (PI_f pinfo))
  (Hreach: id_in_reachable_block (PI_f pinfo) (LAS_lid pinfo lasinfo)),
  isReachableFromEntry (PI_f pinfo) (LAS_block pinfo lasinfo).
Proof.
  intros. apply Hreach. apply lookup_LAS_lid__LAS_block; auto.
Qed.

Lemma LAS_value_doms_LAS_lid__lid_in_cmd_scope____LAS_value_inscope: forall
  (s : system) (pinfo : PhiInfo) (lasinfo : LASInfo pinfo) (tmn : terminator)
  (l1 : l) (ps1 : phinodes) (cs1 : list cmd) (cs : list cmd) (c : cmd) m
  (l0 : list atom) (HwfF : wf_fdef s m (PI_f pinfo)) 
  (Huniq : uniqFdef (PI_f pinfo))
  (Hreach : isReachableFromEntry (PI_f pinfo)
             (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn))
  (Hreach': isReachableFromEntry (PI_f pinfo) (LAS_block pinfo lasinfo))
  (HbInF : blockInFdefB (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn) (PI_f pinfo) =
           true)
  (HeqR : ret l0 =
         inscope_of_cmd (PI_f pinfo)
           (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn) c)
  (Hin : In (LAS_lid pinfo lasinfo) l0),
  value_in_scope (LAS_value pinfo lasinfo) l0.
Proof.
  intros.
  assert (Hdom:=HwfF).
  apply LAS_value__dominates__LAS_lid with (lasinfo:=lasinfo) in Hdom; auto.
  assert (Hsval:=@LAS_value__exists pinfo lasinfo _ _ HwfF Huniq).
  destruct (LAS_value pinfo lasinfo); auto.
  simpl in Hdom. symmetry in HeqR.
  destruct Hsval as [Hinargs | [instr [Hlkc EQ]]]; subst; auto.
    eapply in_getArgsIDsOfFdef__inscope_of_cmd; eauto.

    assert (idDominates (PI_f pinfo) id5 (LAS_lid pinfo lasinfo)) as Hidom.
      apply Hdom. apply LAS_block__reachable; auto.
    eapply idDominates_inscope_of_cmd__inscope_of_cmd 
      with (c:=c)
           (instr0:=insn_cmd (insn_load (LAS_lid pinfo lasinfo) 
             (PI_typ pinfo) (value_id (PI_id pinfo)) 
             (LAS_lalign pinfo lasinfo))) in HeqR; 
      eauto 1.
      symmetry. apply lookup_LAS_lid__load; auto.
Qed.

