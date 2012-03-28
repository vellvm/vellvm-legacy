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
Require Import memory_props.
Require Import trans_tactic.

Import Promotability.

Definition alive_store (sid: id) (v:value) (cs2:cmds) (b:block) (pinfo:PhiInfo)
  : Prop :=
blockInFdefB b (PI_f pinfo) = true /\
store_in_cmds (PI_id pinfo) cs2 = false /\
let '(block_intro _ _ cs _) := b in
exists cs1, exists cs3,
  cs =
  cs1 ++
  insn_store sid (PI_typ pinfo) v (value_id (PI_id pinfo)) (PI_align pinfo) ::
  cs2 ++
  cs3.

Record StoreInfo (pinfo: PhiInfo) := mkStoreInfo {
  SI_id : id;
  SI_value : value;
  SI_tail : cmds;
  SI_block : block;
  SI_alive : alive_store SI_id SI_value SI_tail SI_block pinfo
}.

Lemma storeinfo_doesnt_use_promotable_allocas: forall pinfo stinfo
  (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo -> SI_value pinfo stinfo <> value_id (PI_id pinfo).
Proof.
  intros.
  destruct stinfo. simpl in *.
  destruct SI_block0.
  destruct SI_alive0 as [J1 [J2 [cs1 [cs2 J3]]]]; subst.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in J1; eauto using in_middle.
    apply WF_PhiInfo_spec3 in J1; auto.
    intro EQ; subst.
    assert (G:=@valueEqB_refl (value_id (PI_id pinfo))).
    destruct (valueEqB (value_id (PI_id pinfo)) (value_id (PI_id pinfo)));
      simpl in *; try congruence.
Qed.

Definition wf_defs (pinfo:PhiInfo) (stinfo: StoreInfo pinfo) TD M gl (lc:DGVMap)
  : Prop :=
forall gvsa gvsv
  (Hlkpa: lookupAL _ lc (PI_id pinfo) = Some gvsa)
  (Hlkpv: Opsem.getOperandValue TD (SI_value pinfo stinfo) lc gl
    = Some gvsv),
  mload TD M gvsa (PI_typ pinfo) (PI_align pinfo) = Some gvsv.

Definition follow_alive_store (pinfo:PhiInfo) (stinfo: StoreInfo pinfo)
  (cs:cmds) : Prop :=
let '(block_intro _ _ cs0 _) := SI_block pinfo stinfo in
forall cs1 cs3,
  cs0 =
    cs1 ++
    insn_store (SI_id pinfo stinfo) (PI_typ pinfo) (SI_value pinfo stinfo)
      (value_id (PI_id pinfo)) (PI_align pinfo) ::
    SI_tail pinfo stinfo ++
    cs3 ->
  (exists csa, exists csb,
    cs = csb ++ cs3 /\ SI_tail pinfo stinfo = csa ++ csb).

Lemma follow_alive_store_cons: forall pinfo stinfo c cs l0 ps0 cs0 tmn0
  (Huniq:uniqFdef (PI_f pinfo)),
  block_intro l0 ps0 (cs0++c::cs) tmn0 = SI_block pinfo stinfo ->
  store_in_cmd (PI_id pinfo) c = false ->
  follow_alive_store pinfo stinfo cs ->
  follow_alive_store pinfo stinfo (c::cs).
Proof.
  unfold follow_alive_store.
  intros.
  destruct stinfo. simpl in *.
  unfold alive_store in SI_alive0.
  destruct SI_block0.
  destruct SI_alive0 as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
  intros.
  assert (cs1 = cs2 /\ cs3 = cs4) as J.
    eapply uniqFdef_cmds_split_middle in H2; eauto.
    destruct H2 as [G1 G2].
    split; auto.
      apply app_inv_head in G2; auto.

  destruct J as [EQ1 EQ2]; subst. clear H2.
  edestruct H1 as [csa [csb [EQ1 EQ2]]]; eauto. clear H1.
  subst. inv H.
  anti_simpl_env.
  destruct csa.
    anti_simpl_env.
    simpl in H0.
    destruct (id_dec (PI_id pinfo) (PI_id pinfo)); simpl in H0; congruence.

    assert (exists csa', exists c2, [c0] ++ csa = csa' ++ [c2]) as EQ.
      apply head_tail_commut.
    destruct EQ as [csa' [c2 EQ]].
    simpl_env in H4.
    rewrite EQ in H4. anti_simpl_env.
    exists csa'. exists (c2::csb). simpl_env.
    rewrite_env (([c0] ++ csa) ++ csb).
    rewrite EQ. simpl_env.
    split; auto.
Qed.

Definition wf_ExecutionContext (pinfo:PhiInfo) (stinfo: StoreInfo pinfo) TD M gl
  (ec:Opsem.ExecutionContext) : Prop :=
Opsem.CurFunction ec = PI_f pinfo ->
Opsem.CurBB ec = SI_block pinfo stinfo ->
follow_alive_store pinfo stinfo (Opsem.CurCmds ec) ->
wf_defs pinfo stinfo TD M gl (Opsem.Locals ec).

Fixpoint wf_ECStack (pinfo:PhiInfo) (stinfo: StoreInfo pinfo) TD M gl
  (ecs:Opsem.ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' =>
    wf_ExecutionContext pinfo stinfo TD M gl ec /\
    wf_ECStack pinfo stinfo TD M gl ecs'
end.

Definition wf_State (pinfo:PhiInfo) (stinfo: StoreInfo pinfo)
  (cfg:OpsemAux.Config) (S:Opsem.State) : Prop :=
wf_ECStack pinfo stinfo (OpsemAux.CurTargetData cfg) (Opsem.Mem S)
  (OpsemAux.Globals cfg) (Opsem.ECS S).

Lemma free_allocas_preserves_wf_defs: forall pinfo TD Mem lc' als0 als Mem'
  gl stinfo maxb,
  Promotability.wf_defs maxb pinfo TD Mem lc' als0 ->
  wf_defs pinfo stinfo TD Mem gl lc' ->
  NoDup (als ++ als0) ->
  free_allocas TD Mem als = ret Mem' ->
  wf_defs pinfo stinfo TD Mem' gl lc'.
Proof.
  intros. unfold wf_defs in *. intros.
  assert (Hlkpa':=Hlkpa).
  eapply H0 in Hlkpa; eauto. clear H0.
  eapply H in Hlkpa'; eauto.
  destruct Hlkpa' as [J1 J2].
  destruct J1 as [_ [[mb [J1 [J3 J4]]] _]]; subst.
  eapply alist.NoDup_disjoint in H1; eauto.
  eapply free_allocas_preserves_mload; eauto.
Qed.

Lemma wf_defs_updateAddAL: forall pinfo stinfo TD M lc' i1 gv1 gl
  (Hwfpi: WF_PhiInfo pinfo) (Huniq: uniqFdef (PI_f pinfo))
  (HwfDef: wf_defs pinfo stinfo TD M gl lc')
  (Hneq: i1 <> PI_id pinfo)
  (Hnouse: used_in_value i1 (SI_value pinfo stinfo) = false),
  wf_defs pinfo stinfo TD M gl (updateAddAL _ lc' i1 gv1).
Proof.
  intros. unfold wf_defs in *. intros.
  rewrite <- lookupAL_updateAddAL_neq in Hlkpa; auto.
  eapply HwfDef; eauto.
  apply storeinfo_doesnt_use_promotable_allocas with (stinfo:=stinfo) in Hwfpi;
    auto.
  destruct (SI_value pinfo stinfo) as [i0|]; simpl in *; auto.
  destruct (id_dec i0 i1); simpl in Hnouse; try congruence.
  rewrite <- lookupAL_updateAddAL_neq in Hlkpv; auto.
Qed.

Lemma free_allocas_preserves_wf_ECStack: forall maxb pinfo stinfo td als gl ECs
  Mem Mem'
  (HwfECs : Promotability.wf_ECStack maxb pinfo td Mem ECs)
  (Hwfpi: WF_PhiInfo pinfo)
  (Hndup: NoDup (als ++ (flat_map
                  (fun ec : Opsem.ExecutionContext =>
                   let '{| Opsem.Allocas := als |} := ec in als)
                   ECs)))
  (Hwf: wf_ECStack pinfo stinfo td Mem gl ECs)
  (Hfrees: free_allocas td Mem als = ret Mem'),
  wf_ECStack pinfo stinfo td Mem' gl ECs.
Proof.
  induction ECs as [|[]]; simpl; intros; auto.
    destruct Hwf as [J1 J2].
    assert (Hndup' := Hndup).
    apply NoDup_strenthening in Hndup.
    destruct HwfECs as [[Hwfdefs _] [HwfECs _]].
    split; eauto.
      intros G1 G2 G3. simpl in G1, G2, G3. subst. simpl.
      apply J1 in G3; auto. simpl in G3.
      destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
      rewrite_env ((als ++ Allocas) ++
        flat_map
          (fun ec : Opsem.ExecutionContext =>
           let '{| Opsem.Allocas := als |} := ec in als) ECs) in Hndup'.
      apply NoDup_split in Hndup'. destruct Hndup'.
      eapply free_allocas_preserves_wf_defs in G3; eauto.
Qed.

Lemma follow_alive_store_at_beginning_false: forall (pinfo : PhiInfo)
  (stinfo : StoreInfo pinfo) (l' : l) (ps' : phinodes) (cs' : cmds)
  (tmn' : terminator)
  (J2 : block_intro l' ps' cs' tmn' = SI_block pinfo stinfo)
  (J3 : follow_alive_store pinfo stinfo cs'),
  False.
Proof.
  intros.
  unfold follow_alive_store in J3.
  rewrite <- J2 in J3.
  destruct stinfo. simpl in *.
  rewrite <- J2 in SI_alive0.
  destruct SI_alive0 as [_ [_ [cs1 [cs3 J]]]].
  assert (J':=J).
  apply J3 in J.
  destruct J as [csa [csb [EQ1 EQ2]]]; subst.
  anti_simpl_env.
Qed.

Ltac preservation_sBranch :=
match goal with
| HwfS1 : wf_State _ _ _ _ |- _ =>
  destruct HwfS1 as [_ HwfECs];
  simpl in HwfECs;
  fold wf_ECStack in HwfECs;
  split; try solve [
    auto |
    intros J1 J2 J3; simpl in *; subst;
    eapply follow_alive_store_at_beginning_false in J3; eauto;
    inv J3]
end.

Ltac destruct_stinfo :=
match goal with
| stinfo: StoreInfo _ |- _ =>
  destruct stinfo as [SI_id0 SI_value0 SI_tail0
                       [SI_l0 SI_ps0 SI_cs0 SI_tmn0] SI_prop0];
  simpl in *;
  destruct SI_prop0 as 
    [SI_BInF0 [SI_stincmds0 [SI_cs1 [SI_cs3 SI_EQ]]]]; subst; simpl
end.

Lemma alive_store_doesnt_use_its_followers_and_pid: forall l1 ps1 cs1' c cs tmn 
  id0 pinfo stinfo s m (Huniq: uniqFdef (PI_f pinfo)),
  wf_fdef s m (PI_f pinfo) -> 
  block_intro l1 ps1 (cs1' ++ c :: cs) tmn = SI_block pinfo stinfo ->
  getCmdID c = Some id0 ->
  follow_alive_store pinfo stinfo (c::cs) ->
  used_in_value id0 (SI_value pinfo stinfo) = false /\ id0 <> PI_id pinfo.
Proof.
  intros.
  assert (exists ids1, ret ids1 = 
    inscope_of_id (PI_f pinfo) (SI_block pinfo stinfo) (getCmdLoc c) /\
    In (SI_id pinfo stinfo) ids1) as Hinscope.
    admit. (* inscope_of_id should consider non-returned cmd *)
  assert (Hreach: isReachableFromEntry (PI_f pinfo) (SI_block pinfo stinfo)).
    admit. (* mem2reg should only work for reachable blocks *)
Local Opaque inscope_of_id isReachableFromEntry.
  unfold follow_alive_store in H2.
  rewrite <- H0 in H2.
  destruct_stinfo. inv H0.
  assert (J4':=H6).
  apply_clear H2 in H6.
  destruct H6 as [csa [csb [EQ1 EQ2]]]; subst.
  rewrite EQ1 in J4'. 
  anti_simpl_env. subst.
  simpl in SI_BInF0.
  assert (J1':=SI_BInF0).
  eapply wf_fdef__wf_cmd in SI_BInF0; eauto using in_middle.
  inv SI_BInF0.
  match goal with | H13: wf_insn_base _ _ _ |- _ => inv H13 end.
  destruct Hinscope as [ids1 [Hinscope Hin]].
  assert (H0':=H0).
  apply destruct_insnInFdefBlockB in H0'. destruct H0' as [HcInB HcInF].
  rewrite <- EQ1 in *. 
  assert (In c
     (SI_cs1 ++
      insn_store SI_id0 (PI_typ pinfo) SI_value0
        (value_id (PI_id pinfo)) (PI_align pinfo) :: 
      csa ++ c :: cs)) as Hin'.
    apply in_or_app. right. simpl. right. apply in_middle.
  eapply cmd_doesnt_use_nondom_operands 
    with (c1:=insn_store SI_id0 (PI_typ pinfo) SI_value0
                 (value_id (PI_id pinfo)) (PI_align pinfo))
    (b1:=block_intro SI_l0 SI_ps0
            (SI_cs1 ++
             insn_store SI_id0 (PI_typ pinfo) SI_value0
               (value_id (PI_id pinfo)) (PI_align pinfo) :: 
             csa ++ c :: cs) SI_tmn0)
    (l3:=SI_l0)(ps1:=SI_ps0)
    (cs:=SI_cs1 ++
             insn_store SI_id0 (PI_typ pinfo) SI_value0
               (value_id (PI_id pinfo)) (PI_align pinfo) :: 
             csa ++ c :: cs)(tmn1:=SI_tmn0) in Hinscope; eauto 1.
    clear - Hinscope H1.
    rewrite getCmdID__getCmdLoc with (id0:=id0) in Hinscope; auto.
    destruct SI_value0 as [i0|].
      simpl in Hinscope. simpl. 
      destruct (id_dec i0 id0); subst.
        tauto.
        destruct (id_dec id0 (PI_id pinfo)); subst; auto.
      simpl in Hinscope. simpl. 
      destruct (id_dec id0 (PI_id pinfo)); subst; auto.
      
    simpl_env. simpl. auto.
    simpl_env. simpl. solve_in_list.
Qed.

Lemma alive_store_doesnt_use_its_followers: forall l1 ps1 cs1' c cs tmn 
  id0 pinfo stinfo s m (Huniq: uniqFdef (PI_f pinfo)),
  wf_fdef s m (PI_f pinfo) -> 
  block_intro l1 ps1 (cs1' ++ c :: cs) tmn = SI_block pinfo stinfo ->
  getCmdID c = Some id0 ->
  follow_alive_store pinfo stinfo (c::cs) ->
  used_in_value id0 (SI_value pinfo stinfo) = false.
Proof.
  intros.
  eapply alive_store_doesnt_use_its_followers_and_pid in H0; eauto.
  tauto.
Qed.

Lemma preservation_return : forall maxb pinfo stinfo (HwfPI : WF_PhiInfo pinfo)
  F B rid RetTy Result lc F' B' c' cs' tmn' lc' EC Mem als als' cfg
  EC1 EC2
  (EQ1:EC1 = {| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := nil;
                Opsem.Terminator := insn_return rid RetTy Result;
                Opsem.Locals := lc;
                Opsem.Allocas := als |})
  (EQ2:EC2 = {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := c' :: cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc';
                Opsem.Allocas := als' |})
  (Hwfcfg : OpsemPP.wf_Config cfg)  
  (Hwfpp : OpsemPP.wf_State cfg
           {| Opsem.ECS := EC1 :: EC2 :: EC;
              Opsem.Mem := Mem |})
  (Hnoalias : Promotability.wf_State maxb pinfo cfg
           {| Opsem.ECS := EC1 :: EC2 :: EC;
              Opsem.Mem := Mem |})
  Mem' lc'' (H : Instruction.isCallInst c' = true)
  (H0 : free_allocas (OpsemAux.CurTargetData cfg) Mem als = ret Mem')
  (H1 : Opsem.returnUpdateLocals
          (OpsemAux.CurTargetData cfg) c'
            Result lc lc' (OpsemAux.Globals cfg) = ret lc'')
  (HwfS1 : wf_State pinfo stinfo cfg
            {| Opsem.ECS := EC1 :: EC2 :: EC;
               Opsem.Mem := Mem |}),
  wf_State pinfo stinfo cfg
     {| Opsem.ECS :=
             {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc'';
                Opsem.Allocas := als' |} :: EC;
        Opsem.Mem := Mem' |}.
Proof.
  intros. subst. destruct cfg as [S [los nts] Ps gl fs].

  destruct Hwfcfg as [_ [_ [HwfSystem HmInS]]].
  destruct Hwfpp as 
    [_ [_ 
     [
       [
         [_ [HBinF1 [HFinPs1 [_ [_ [l2 [ps2 [cs2' Heq2]]]]]]]]
         _
       ]
       _
     ]
    ]]; subst.

  destruct HwfS1 as [Hinscope1 [Hinscope2 HwfECs]]. simpl.
  simpl in Hinscope1, Hinscope2, HwfECs.
  fold wf_ECStack in HwfECs.

  destruct Hnoalias as
    [
      [_ [[[Hinscope2' _] [HwfECs' _]] _]]
      [[Hdisjals _] HwfM]
    ]. simpl in Hdisjals.
  fold Promotability.wf_ECStack in HwfECs'.

  split.
    SSCase "wf_EC".
    intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
    remember (getCmdID c') as R.
    destruct_cmd c'; try solve [inversion H].
    unfold wf_ExecutionContext in *. simpl in Hinscope1, Hinscope2.
    assert (J2':=J2).
    assert (uniqFdef (PI_f pinfo)) as Huniq. eauto using wf_system__uniqFdef.
    apply follow_alive_store_cons in J2; auto.
    assert (J2'':=J2).
    apply Hinscope2 in J2; auto.
    assert (NoDup (als ++ als')) as Hnodup.
      rewrite_env
        ((als ++ als') ++
          flat_map
            (fun ec : Opsem.ExecutionContext =>
             let '{| Opsem.Allocas := als |} := ec in als) EC) in Hdisjals.
      apply NoDup_split in Hdisjals.
      destruct Hdisjals; auto.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    eapply free_allocas_preserves_wf_defs in J2; eauto. clear Hnodup.
      unfold Opsem.returnUpdateLocals in H1. simpl in H1.
      remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
      destruct R1; try solve [inv H1].
      destruct R.
      SSSSSCase "c' defines a variable".
        destruct n; inv HeqR.
        remember (lift_op1 DGVs (fit_gv (los, nts) t0) g t0) as R2.
        destruct R2; inv H1.
        apply wf_defs_updateAddAL; auto.
          eapply WF_PhiInfo_spec10 in HBinF1; eauto.
          eapply alive_store_doesnt_use_its_followers;
            eauto using wf_system__wf_fdef.

      SSSSSCase "c' defines nothing".
        destruct n; inv HeqR. inv H1. auto.

    SSCase "wf_ECs".
      simpl.
      eapply free_allocas_preserves_wf_ECStack; eauto.
      apply NoDup_strenthening in Hdisjals; auto.
Qed.

Lemma preservation_return_void : forall maxb pinfo stinfo
  (HwfPI : WF_PhiInfo pinfo)
  F B rid lc F' B' c' cs' tmn' lc' EC Mem als als' cfg EC1 EC2
  (EQ1:EC1 = {| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := nil;
                Opsem.Terminator := insn_return_void rid;
                Opsem.Locals := lc;
                Opsem.Allocas := als |})
  (EQ2:EC2 = {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := c' :: cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc';
                Opsem.Allocas := als' |})
  (Hwfcfg : OpsemPP.wf_Config cfg)
  (Hwfpp : OpsemPP.wf_State cfg
           {| Opsem.ECS := EC1 :: EC2 :: EC;
              Opsem.Mem := Mem |})
  (Hnoalias : Promotability.wf_State maxb pinfo cfg
           {| Opsem.ECS := EC1 :: EC2 :: EC;
              Opsem.Mem := Mem |})
  Mem' (H : Instruction.isCallInst c' = true)
  (H0 : free_allocas (OpsemAux.CurTargetData cfg) Mem als = ret Mem')
  (HwfS1 : wf_State pinfo stinfo cfg
            {| Opsem.ECS := EC1 :: EC2 :: EC;
               Opsem.Mem := Mem |}),
  wf_State pinfo stinfo cfg
     {| Opsem.ECS :=
             {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc';
                Opsem.Allocas := als' |} :: EC;
        Opsem.Mem := Mem' |}.
Proof.
  intros. subst. destruct cfg as [S [los nts] Ps gl fs].
  destruct Hwfcfg as [_ [_ [HwfSystem HmInS]]].
  destruct Hwfpp as 
    [_ [_ 
     [
       [
         [_ [HBinF1 [HFinPs1 [_ [_ [l2 [ps2 [cs2' Heq2]]]]]]]]
         _
       ]
       _
     ]
    ]]; subst.

  destruct HwfS1 as [Hinscope1 [Hinscope2 HwfECs]]. simpl.
  simpl in Hinscope1, Hinscope2, HwfECs.
  fold wf_ECStack in HwfECs.

  destruct Hnoalias as
    [
      [_ [[[Hinscope2' _] [HwfECs' _]] _]]
      [[Hdisjals _] HwfM]
    ]. simpl in Hdisjals.
  fold Promotability.wf_ECStack in HwfECs'.

  split.
    SSCase "wf_EC".
    intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
    remember (getCmdID c') as R.
    destruct c'; try solve [inversion H].
    unfold wf_ExecutionContext in *. simpl in Hinscope1, Hinscope2.
    assert (J2':=J2).
    apply follow_alive_store_cons in J2; eauto using wf_system__uniqFdef.
    apply Hinscope2 in J2; auto.
    assert (NoDup (als ++ als')) as Hnodup.
      rewrite_env
        ((als ++ als') ++
          flat_map
            (fun ec : Opsem.ExecutionContext =>
             let '{| Opsem.Allocas := als |} := ec in als) EC) in Hdisjals.
      apply NoDup_split in Hdisjals.
      destruct Hdisjals; auto.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    eapply free_allocas_preserves_wf_defs in J2; eauto.

    SSCase "wf_ECs".
      simpl.
      eapply free_allocas_preserves_wf_ECStack; eauto.
      apply NoDup_strenthening in Hdisjals; auto.
Qed.

Lemma malloc_preserves_wf_EC_at_head : forall pinfo los nts Ps M
  (Hwfpi:WF_PhiInfo pinfo) s als'
  M' gl als lc t mb id0 align0 F gn tsz l1 ps1 cs1' cs tmn
  (HwfF: wf_fdef s (module_intro los nts Ps) F) (HuniqF: uniqFdef F)
  (Hal: malloc (los,nts) M tsz gn align0 = ret (M', mb)) stinfo c
  (HBinF: blockInFdefB
             (block_intro l1 ps1 (cs1' ++ c :: cs)
                tmn) F = true)
  (Hid : getCmdID c = Some id0)
  (Hnst : store_in_cmd (PI_id pinfo) c = false)
  (Hsort : match c with
           | insn_malloc _ _ _ _ | insn_alloca _ _ _ _ => True
           | _ => False
           end)
  (Hinscope : wf_ExecutionContext pinfo stinfo (los,nts) M gl
               {|
               Opsem.CurFunction := F;
               Opsem.CurBB := block_intro l1 ps1
                                (cs1' ++ c :: cs)
                                tmn;
               Opsem.CurCmds := c :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
  wf_ExecutionContext pinfo stinfo (los,nts) M' gl
    {|
    Opsem.CurFunction := F;
    Opsem.CurBB := block_intro l1 ps1
                      (cs1' ++ c :: cs) tmn;
    Opsem.CurCmds := cs;
    Opsem.Terminator := tmn;
    Opsem.Locals := updateAddAL (GVsT DGVs) lc id0
                       ($ blk2GV (los,nts) mb # typ_pointer t $);
    Opsem.Allocas := als' |}.
Proof.
  intros.
  intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
  assert (J2':=J2).
  apply follow_alive_store_cons in J2; auto.
  assert (Hfollow:=J2).
  assert (used_in_value id0 (SI_value pinfo stinfo) = false) as Hnuse.
    eapply alive_store_doesnt_use_its_followers; eauto.
  apply Hinscope in J2; auto. simpl in J2.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  apply wf_defs_updateAddAL with (i1:=id0)
    (gv1:=($ blk2GV (los,nts) mb # typ_pointer t $)) in J2; auto.
    intros gvsa gvsv Hlkpa Hlkpv.
    eapply J2 in Hlkpv; eauto.
    eapply malloc_preserves_mload; eauto.
      destruct (id_dec id0 (PI_id pinfo)); subst; auto.
      destruct_cmd c; tinv Hsort.
        apply getCmdLoc_getCmdID in Hid; subst.
        eapply WF_PhiInfo_spec10 in HBinF; eauto.

        inv Hid.
        clear - J2' J3 HwfF Hfollow HuniqF. 
        eapply alive_store_doesnt_use_its_followers_and_pid in J2'; simpl; eauto.
Qed.

Lemma malloc_preserves_wf_EC_in_tail : forall pinfo td M
  EC M' gl mb align0 gn tsz
  (Hal: malloc td M tsz gn align0 = ret (M', mb)) stinfo
  (Hinscope : wf_ExecutionContext pinfo stinfo td M gl EC),
  wf_ExecutionContext pinfo stinfo td M' gl EC.
Proof.
  intros.
  intros J1 J2 J3.
  apply Hinscope in J3; auto.
  intros gvsa gvsv Hlkpa Hlkpv.
  eapply J3 in Hlkpv; eauto.
  eapply malloc_preserves_mload; eauto.
Qed.

Lemma malloc_preserves_wf_ECStack_in_tail : forall pinfo stinfo TD M tsz gn
  align0 (Hwfpi: WF_PhiInfo pinfo) M' mb gl
  (Hmlc: malloc TD M tsz gn align0 = ret (M', mb)) ECs
  (Hwf: wf_ECStack pinfo stinfo TD M gl ECs),
  wf_ECStack pinfo stinfo TD M' gl ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct Hwf as [J1 J2].
    split; auto.
      eapply malloc_preserves_wf_EC_in_tail; eauto.
Qed.

Lemma free_preserves_wf_EC_in_tail : forall pinfo los nts M EC M' mptr0
  maxb gl (Hwfg: wf_globals maxb gl) Ps S F t
  (Hfree: free (los,nts) M mptr0 = ret M') stinfo mptrs v lc
  (Hwft: wf_value S (module_intro los nts Ps) F v t)
  (H : Opsem.getOperandValue (los,nts) v lc gl = ret mptrs)
  (H0 : mptr0 @ mptrs)
  (Hinscope : wf_ExecutionContext pinfo stinfo (los,nts) M gl EC)
  (Hht : wf_ECStack_head_in_tail maxb pinfo (los,nts) M lc EC),
  wf_ExecutionContext pinfo stinfo (los,nts) M' gl EC.
Proof.
  intros.
  intros J1 J2 J3.
  apply Hinscope in J3; auto.
  intros gvsa gvsv Hlkpa Hlkpv.
  eapply J3 in Hlkpv; eauto.
  eapply free_preserves_mload; eauto.
    eapply operand__no_alias_with__tail; eauto.
Qed.

Lemma free_preserves_wf_ECStack_in_tail : forall maxb pinfo stinfo los nts M
  (Hwfpi: WF_PhiInfo pinfo) M' gl mptr0 (Hwfg: wf_globals maxb gl)
  (Hfree: free (los,nts) M mptr0 = ret M') lc mptrs v t S Ps F
  (Hwft: wf_value S (module_intro los nts Ps) F v t)
  (H : Opsem.getOperandValue (los,nts) v lc gl = ret mptrs)
  (H0 : mptr0 @ mptrs) ECs
  (Hhts: wf_ECStack_head_tail maxb pinfo (los,nts) M lc ECs)
  (Hwf: wf_ECStack pinfo stinfo (los,nts) M gl ECs),
  wf_ECStack pinfo stinfo (los,nts) M' gl ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct Hwf as [J1 J2].
    apply wf_ECStack_head_tail_cons__inv in Hhts.
    destruct Hhts as [J3 J4].
    split; auto.
      eapply free_preserves_wf_EC_in_tail; eauto.
Qed.

Lemma preservation_pure_cmd_updated_case : forall (F : fdef)(B : block)
  (lc : DGVMap)(gv3 : GVsT DGVs) (cs : list cmd) (tmn : terminator) id0 c0 Mem0
  als ECs pinfo stinfo
  (HwfPI : WF_PhiInfo pinfo) (Hid : Some id0 = getCmdID c0) cfg maxb EC
  (Heq: EC = {| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := c0 :: cs;
                Opsem.Terminator := tmn;
                Opsem.Locals := lc;
                Opsem.Allocas := als |})
  (Hwfcfg : OpsemPP.wf_Config cfg)
  (Hwfpp : OpsemPP.wf_State cfg
           {| Opsem.ECS := EC :: ECs;
              Opsem.Mem := Mem0 |})
  (Hnoalias : Promotability.wf_State maxb pinfo cfg
           {| Opsem.ECS := EC :: ECs;
              Opsem.Mem := Mem0 |})
  (HwfS1 : wf_State pinfo stinfo cfg
            {| Opsem.ECS := EC :: ECs;
               Opsem.Mem := Mem0 |})
  (Hnst : store_in_cmd (PI_id pinfo) c0 = false)
  (Hneq :  F = PI_f pinfo ->
           B = SI_block pinfo stinfo ->
           follow_alive_store pinfo stinfo (c0 :: cs) ->
           (id0 <> PI_id pinfo /\
           used_in_value id0 (SI_value pinfo stinfo) = false)),
  wf_State pinfo stinfo cfg
     {|
     Opsem.ECS := {|
            Opsem.CurFunction := F;
            Opsem.CurBB := B;
            Opsem.CurCmds := cs;
            Opsem.Terminator := tmn;
            Opsem.Locals := updateAddAL (GVsT DGVs) lc id0 gv3;
            Opsem.Allocas := als |} :: ECs;
     Opsem.Mem := Mem0 |}.
Proof.
  intros. subst.
  destruct cfg as [S [los nts] Ps gl fs].
  destruct Hwfcfg as [_ [_ [HwfSystem HmInS]]].
  destruct Hwfpp as 
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]]
     [HwfEC0 HwfCall]
    ]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0.

  destruct HwfS1 as [Hinscope HwfECs]. simpl.
  simpl in Hinscope, HwfECs.
  fold wf_ECStack in HwfECs.

  destruct Hnoalias as
    [
      [[Hinscope2' _] [HwfECs' _]]
      [[Hdisjals _] HwfM]
    ]. simpl in Hdisjals.
  fold Promotability.wf_ECStack in HwfECs'.

  split; auto.
    intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
    unfold wf_ExecutionContext in *. simpl in Hinscope.
    assert (uniqFdef (PI_f pinfo)) as Huniq. eauto using wf_system__uniqFdef.
    assert (J2':=J2).
    apply follow_alive_store_cons in J2; auto.
    assert (J2'':=J2).
    apply Hinscope in J2; auto.
    destruct Hneq as [G1 G2]; auto.
    eapply wf_defs_updateAddAL; eauto.
Qed.

Lemma mstore_preserves_wf_EC_at_head: forall (maxb : Z) (pinfo : PhiInfo)
  (stinfo : StoreInfo pinfo) (S : system) los nts
  (Ps : list product) (gl : GVMap) (fs : GVMap) (Hwfg : wf_globals maxb gl)
  (F : fdef) (lc : Opsem.GVsMap) (sid : id) (t : typ) (align0 : align)
  (v1 : value) (v2 : value) (cs : list cmd) (tmn : terminator) (Mem : mem)
  (als : list mblock) (l1 : l) (ps1 : phinodes) (cs1' : list cmd)
  (mp2 : GenericValue) (gv1 : GenericValue) (Mem' : mem) (gvs1 : GVsT DGVs)
  (mps2 : GVsT DGVs) (Huniq: uniqFdef F)
  (H : Opsem.getOperandValue (los,nts) v1 lc gl = ret gvs1)
  (H0 : Opsem.getOperandValue (los,nts) v2 lc gl = ret mps2)
  (Hwft2: wf_value S (module_intro los nts Ps) F v2 (typ_pointer t))
  (Hwft1: wf_value S (module_intro los nts Ps) F v1 t)
  (Hwfgl: genericvalues.LLVMgv.wf_global (los, nts) S gl)
  (H1 : gv1 @ gvs1) (H2 : mp2 @ mps2)
  (H3 : mstore (los,nts) Mem mp2 t gv1 align0 = ret Mem')
  (Hwflc: OpsemPP.wf_lc (los,nts) F lc)
  (Hinscope' : if fdef_dec (PI_f pinfo) F
               then Promotability.wf_defs maxb pinfo (los,nts) Mem lc als
               else True)
  (Hinscope : wf_ExecutionContext pinfo stinfo (los,nts) Mem gl
               {|
               Opsem.CurFunction := F;
               Opsem.CurBB := block_intro l1 ps1
                                (cs1' ++ insn_store sid t v1 v2 align0 :: cs)
                                tmn;
               Opsem.CurCmds := insn_store sid t v1 v2 align0 :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
  wf_ExecutionContext pinfo stinfo (los,nts) Mem' gl
     {|
     Opsem.CurFunction := F;
     Opsem.CurBB := block_intro l1 ps1
                      (cs1' ++ insn_store sid t v1 v2 align0 :: cs) tmn;
     Opsem.CurCmds := cs;
     Opsem.Terminator := tmn;
     Opsem.Locals := lc;
     Opsem.Allocas := als |}.
Proof.
  intros.
  intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
  assert (J2':=J2).
  remember (store_in_cmd (PI_id pinfo) (insn_store sid t v1 v2 align0)) as R.
  destruct R.
    clear - J2 J3 HeqR H3 H2 H0 H1 H Hwflc Hwft1 Hwfgl.
    unfold follow_alive_store in J3.
    rewrite <- J2 in J3.
    destruct stinfo. simpl in *.
    assert (SI_alive0':=SI_alive0).
    rewrite <- J2 in SI_alive0'.
    destruct SI_alive0' as [G1 [G2 [cs1 [cs2 EQ]]]].
    assert (EQ':=EQ).
    apply J3 in EQ. clear J3.
    destruct EQ as [csa [csb [EQ1 EQ2]]]; subst.
    anti_simpl_env. 
    destruct csa.
      simpl_env in EQ'.
      apply app_inj_tail in EQ'.
      destruct EQ' as [EQ1 EQ2]; subst.
      inv EQ2.
      intros gvsa gvsv Hlkpa Hlkpv.
      simpl in *.
      rewrite H0 in Hlkpa. inv Hlkpa. inv H2. inv H1.
      rewrite Hlkpv in H. inv H.
      eapply MemProps.mstore_mload_same; eauto.
        eapply OpsemPP.getOperandValue__wf_gvs in Hlkpv; eauto.
        inv Hlkpv; eauto.

      assert (exists csa', exists c', [c] ++ csa = csa' ++ [c']) as EQ.
        apply head_tail_commut.
      destruct EQ as [csa' [c' EQ]].
      simpl_env in EQ'.
      rewrite EQ in EQ'.
      anti_simpl_env. rewrite_env (([c]++csa) ++ csb) in G2.
      rewrite EQ in G2.
      simpl_env in G2.
      apply store_in_cmds_app in G2.
      destruct G2 as [G2 G3].
      apply store_in_cmds_app in G3.
      destruct G3 as [G3 G4].
      unfold store_in_cmds in G3.
      simpl in G3.
      rewrite G3 in HeqR. congruence.

    clear Hwft1 Hwfgl.
    apply follow_alive_store_cons in J2; auto.
    apply Hinscope in J2; auto. simpl in J2.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    intros gvsa gvsv Hlkpa Hlkpv.
    eapply J2 in Hlkpv; eauto.
    eapply mstore_preserves_mload; eauto.
      eapply operand__no_alias_with__head; eauto.
        apply store_notin_cmd__wf_use_at_head in HeqR; auto.
Qed.

Lemma mstore_preserves_wf_EC_in_tail : forall pinfo los nts M EC M'
  maxb gl (Hwfg: wf_globals maxb gl) lc v1 v2 gvs1 gv1 mps2 mp2 align0 t
  (H : Opsem.getOperandValue (los,nts) v1 lc gl = ret gvs1)
  (H0 : Opsem.getOperandValue (los,nts) v2 lc gl = ret mps2)
  (H1 : gv1 @ gvs1) (H2 : mp2 @ mps2) F S Ps
  (H3 : mstore (los,nts) M mp2 t gv1 align0 = ret M') stinfo
  (Hinscope : wf_ExecutionContext pinfo stinfo (los,nts) M gl EC)
  (Hwft: wf_value S (module_intro los nts Ps) F v2 (typ_pointer t))
  (Hht : wf_ECStack_head_in_tail maxb pinfo (los,nts) M lc EC),
  wf_ExecutionContext pinfo stinfo (los,nts) M' gl EC.
Proof.
  intros.
  intros J1 J2 J3.
  apply Hinscope in J3; auto.
  intros gvsa gvsv Hlkpa Hlkpv.
  eapply J3 in Hlkpv; eauto.
  eapply mstore_preserves_mload; eauto.
    eapply operand__no_alias_with__tail; eauto.
Qed.

Lemma mstore_preserves_wf_ECStack_in_tail : forall maxb pinfo los nts M
  (Hwfpi: WF_PhiInfo pinfo) M' gl (Hwfg: wf_globals maxb gl)
  maxb gl (Hwfg: wf_globals maxb gl) lc v1 v2 gvs1 gv1 mps2 mp2 align0 t
  (H : Opsem.getOperandValue (los,nts) v1 lc gl = ret gvs1)
  (H0 : Opsem.getOperandValue (los,nts) v2 lc gl = ret mps2)
  (H1 : gv1 @ gvs1) (H2 : mp2 @ mps2)
  (H3 : mstore (los,nts) M mp2 t gv1 align0 = ret M') stinfo
  F S Ps
  (Hwft: wf_value S (module_intro los nts Ps) F v2 (typ_pointer t)) ECs
  (Hhts: wf_ECStack_head_tail maxb pinfo (los,nts) M lc ECs) 
  (Hwf: wf_ECStack pinfo stinfo (los,nts) M gl ECs),
  wf_ECStack pinfo stinfo (los,nts) M' gl ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct Hwf as [J1 J2].
    apply wf_ECStack_head_tail_cons__inv in Hhts.
    destruct Hhts as [J3 J4].
    split; auto.
      eapply mstore_preserves_wf_EC_in_tail with (gvs1:=gvs1)(mps2:=mps2)
        in H3; eauto.
Qed.

Lemma getOperandValue_updateAddAL_nouse: forall TD v lc rid v0 gl gvsv,
  Opsem.getOperandValue TD v (updateAddAL (GVsT DGVs) lc rid v0) gl = ret gvsv ->
  used_in_value rid v = false ->
  Opsem.getOperandValue TD v lc gl = ret gvsv.
Proof.
  intros.
  destruct v as [i0|]; simpl in *; auto.
  rewrite <- lookupAL_updateAddAL_neq in H; auto.
  destruct (id_dec i0 rid); auto.
    simpl in H0. congruence.
Qed.

Lemma callExternalFunction_preserves_wf_EC_in_tail : forall pinfo td M EC M' gl
  stinfo gvs fid oresult dck tret targs tr
  (Hcall: callExternalOrIntrinsics td gl M fid tret targs dck gvs = 
    ret (oresult, tr, M'))
  (Hinscope : wf_ExecutionContext pinfo stinfo td M gl EC),
  wf_ExecutionContext pinfo stinfo td M' gl EC.
Proof.
  intros.
  intros J1 J2 J3.
  apply Hinscope in J3; auto.
  intros gvsa gvsv Hlkpa Hlkpv.
  eapply J3 in Hlkpv; eauto.
  eapply MemProps.callExternalOrIntrinsics_preserves_mload; eauto.
Qed.

Lemma callExternalFunction_preserves_wf_ECStack_in_tail: forall Mem fid gvs
  oresult Mem' pinfo stinfo TD gl ECs dck tret targs tr,
  callExternalOrIntrinsics TD gl Mem fid tret targs dck gvs = 
    ret (oresult, tr, Mem') ->
  wf_ECStack pinfo stinfo TD Mem gl ECs ->
  wf_ECStack pinfo stinfo TD Mem' gl ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct H0.
    split; eauto.
      eapply callExternalFunction_preserves_wf_EC_in_tail; eauto.
Qed.

Lemma callExternalFunction_preserves_wf_ECStack_at_head: forall Mem fid gvs
  oresult Mem' pinfo stinfo gl rid noret0 ca rt1 va1 fv lp cs lc lc' als tmn
  cs1' l1 ps1 F s los nts dck Ps (Hwfpi : WF_PhiInfo pinfo) tret targs tr
  (HwfF: wf_fdef s (module_intro los nts Ps) F) (HuniqF: uniqFdef F)
  (H4 : callExternalOrIntrinsics (los,nts) gl Mem fid tret targs dck gvs 
          = ret (oresult, tr, Mem'))
  (H5 : Opsem.exCallUpdateLocals (los,nts) rt1 noret0 rid oresult lc = ret lc')
  (HBinF : blockInFdefB 
             (block_intro l1 ps1 (cs1' ++ insn_call rid noret0 ca rt1 va1 fv lp :: cs) tmn)
             F = true)
  (Hinscope : wf_ExecutionContext pinfo stinfo (los,nts) Mem gl
               {|
               Opsem.CurFunction := F;
               Opsem.CurBB := block_intro l1 ps1
                                (cs1' ++
                                 insn_call rid noret0 ca rt1 va1 fv lp :: cs) tmn;
               Opsem.CurCmds := insn_call rid noret0 ca rt1 va1 fv lp :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
   wf_ExecutionContext pinfo stinfo (los,nts) Mem' gl
     {|
     Opsem.CurFunction := F;
     Opsem.CurBB := block_intro l1 ps1
                      (cs1' ++ insn_call rid noret0 ca rt1 va1 fv lp :: cs) tmn;
     Opsem.CurCmds := cs;
     Opsem.Terminator := tmn;
     Opsem.Locals := lc';
     Opsem.Allocas := als |}.
Proof.
  intros.
  intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
  assert (J2':=J2).
  apply follow_alive_store_cons in J2; auto.
  apply Hinscope in J2; auto.
  simpl in J2.
  intros gvsa gvsv Hlka Hlkv.
  unfold Opsem.exCallUpdateLocals in H5.
  destruct noret0.
    inv H5.
    eapply J2 in Hlkv; eauto.
    eapply MemProps.callExternalOrIntrinsics_preserves_mload; eauto.

    destruct oresult; inv H5.
    remember (fit_gv (los,nts) rt1 g) as R.
    destruct R; inv H0.
    assert (rid <> PI_id pinfo) as Hneq.
      eapply WF_PhiInfo_spec10 in HBinF; eauto.
    rewrite <- lookupAL_updateAddAL_neq in Hlka; auto.
    assert (used_in_value rid (SI_value pinfo stinfo) = false) as Hnouse.
      eapply alive_store_doesnt_use_its_followers; eauto
        using wf_system__wf_fdef, follow_alive_store_cons.
    apply getOperandValue_updateAddAL_nouse in Hlkv; auto.
    eapply MemProps.callExternalOrIntrinsics_preserves_mload; eauto.
Qed.

Ltac destruct_ctx_other :=
match goal with
| Hwfcfg : OpsemPP.wf_Config ?cfg,
  Hwfpp : OpsemPP.wf_State ?cfg _,
  HwfS1 : wf_State _ _ _ _,
  Hnoalias : Promotability.wf_State _ _ _ _ |- _ =>
  destruct Hwfcfg as [_ [Hwfgl0 [HwfSystem HmInS]]];
  destruct Hwfpp as 
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [_ [l1 [ps1 [cs1' Heq1]]]]]]]]
     [HwfEC0 HwfCall]
    ]]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0;
  destruct HwfS1 as [Hinscope HwfECs]; simpl;
  simpl in Hinscope, HwfECs;
  fold wf_ECStack in HwfECs;
  destruct Hnoalias as
    [
      [[Hinscope' _] [HwfECs' HwfHT]]
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals;
  fold Promotability.wf_ECStack in HwfECs'
end.

Ltac preservation_malloc :=
  destruct_ctx_other;
  split; simpl; try solve [
    eapply malloc_preserves_wf_EC_at_head;
      eauto using wf_system__wf_fdef, wf_system__uniqFdef |
    eapply malloc_preserves_wf_ECStack_in_tail; eauto].

Ltac preservation_pure_cmd_updated_case_helper:=
  destruct_ctx_other;
  intros; subst;
  split; try
  eapply alive_store_doesnt_use_its_followers; try solve [
    eauto using wf_system__wf_fdef |
    match goal with
    | HBinF1 : blockInFdefB (block_intro _ _ (_ ++ _ :: _) _) _ = true |- _ =>
       eapply WF_PhiInfo_spec10 in HBinF1; eauto using wf_system__uniqFdef
    end].

Ltac preservation_pure_cmd_updated_case:=
  abstract (eapply preservation_pure_cmd_updated_case; eauto; try solve
    [simpl; auto | preservation_pure_cmd_updated_case_helper]).

Ltac free_preserves_wf_EC_at_head :=
  match goal with
| Hinscope: wf_ExecutionContext ?pinfo _ _ _ _ _ |- _ =>
  intros J1 J2 J3; simpl in J1, J2, J3; simpl; subst;
  assert (J2':=J2);
  apply follow_alive_store_cons in J2; eauto using wf_system__uniqFdef;
  apply Hinscope in J2; auto; simpl in J2;
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence;
  intros gvsa gvsv Hlkpa Hlkpv;
  eapply J2 in Hlkpv; eauto;
  eapply free_preserves_mload; try solve [
    eauto |
    eapply operand__no_alias_with__head; try solve [
      eauto | preservation_tac2 | get_wf_value_for_simop; eauto]
    ]
end.

Lemma preservation : forall maxb pinfo stinfo cfg S1 S2 tr
  (Hwfg: wf_globals maxb (OpsemAux.Globals cfg))
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (HsInsn: Opsem.sInsn cfg S1 S2 tr)
  (HwfS1: wf_State pinfo stinfo cfg S1), wf_State pinfo stinfo cfg S2.
Proof.
  intros.
  (sInsn_cases (induction HsInsn) Case); destruct TD as [los nts]; simpl HwfS1.

Case "sReturn". abstract (eapply preservation_return; eauto).
Case "sReturnVoid". abstract (eapply preservation_return_void; eauto).
Case "sBranch". abstract preservation_sBranch.
Case "sBranch_uncond". abstract preservation_sBranch.

Case "sBop". preservation_pure_cmd_updated_case.
Case "sFBop". preservation_pure_cmd_updated_case.
Case "sExtractValue". preservation_pure_cmd_updated_case.
Case "sInsertValue". preservation_pure_cmd_updated_case.

Case "sMalloc". abstract preservation_malloc.

Case "sFree".
  abstract
  (destruct_ctx_other;
   split; simpl; try solve [
    free_preserves_wf_EC_at_head |
    eapply free_preserves_wf_ECStack_in_tail; try solve [
      eauto | get_wf_value_for_simop; eauto]
   ]).

Case "sAlloca". abstract preservation_malloc.

Case "sLoad". preservation_pure_cmd_updated_case.

Case "sStore".
   abstract
   (destruct_ctx_other;
    split; simpl; try solve [
     eapply mstore_preserves_wf_EC_at_head; try solve [
       eauto using wf_system__uniqFdef |
       get_wf_value_for_simop; eauto
     ] |
     match goal with
     | _ : ?gv1 @ ?gvs1', _ : ?mp2 @ ?mps2',
       _ : mstore _ _ ?mp2 _ ?gv1 _ = _ |- _ =>
       eapply mstore_preserves_wf_ECStack_in_tail
         with (gvs1:=gvs1')(mps2:=mps2'); 
         try solve [eauto | get_wf_value_for_simop; eauto]
     end]).

Case "sGEP". preservation_pure_cmd_updated_case.
Case "sTrunc". preservation_pure_cmd_updated_case.
Case "sExt". preservation_pure_cmd_updated_case.
Case "sCast". preservation_pure_cmd_updated_case.
Case "sIcmp". preservation_pure_cmd_updated_case.
Case "sFcmp". preservation_pure_cmd_updated_case.
Case "sSelect". destruct (isGVZero (los, nts) c); preservation_pure_cmd_updated_case.

Case "sCall".
  abstract (
  destruct_ctx_other;
  split; try solve [
    intros J1 J2 J3; simpl in J1, J2, J3; simpl;
    eapply follow_alive_store_at_beginning_false in J2; eauto; inv J2 |
    split; auto]).

Case "sExCall".
  abstract (
  destruct_ctx_other;
  split; simpl; try solve [
    eapply callExternalFunction_preserves_wf_ECStack_at_head; eauto using
      wf_system__wf_fdef, wf_system__uniqFdef |
    eapply callExternalFunction_preserves_wf_ECStack_in_tail; eauto]).
Qed.

Lemma s_genInitState__alive_store: forall S main VarArgs cfg IS pinfo stinfo
  (HwfS : wf_system S) (Hwfpi: WF_PhiInfo pinfo) 
  (Hinit : @Opsem.s_genInitState DGVs S main VarArgs Mem.empty = ret (cfg, IS)),
  wf_State pinfo stinfo cfg IS.
Admitted.  (* WF init *)


