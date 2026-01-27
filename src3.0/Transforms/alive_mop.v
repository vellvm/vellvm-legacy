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

(* This file proves that in the same block if between a load follows a store 
   or an alloca there is no other store, the load must read the same value 
   stored by the store or the alloca. We call the store or the alloca mop
   for memory operation. *)

(* Check if the store or the alloca is for pinfo. *)
Definition store_or_alloca_of_pid (c:cmd) (pinfo:PhiInfo) : Prop := 
match c with
| insn_store _ t _ v _ => t = PI_typ pinfo /\ v = value_id (PI_id pinfo)
| insn_alloca id0 t0 v0 a0 =>
    id0 = PI_id pinfo /\ t0 = PI_typ pinfo /\
    v0 = PI_num pinfo /\ a0 = PI_align pinfo
| _ => False
end.

(* Check if the value v0 is written by the store, or undef created by the
   alloca. *)
Definition value_of_store_or_alloca (c:cmd) (v0:value) (pinfo:PhiInfo) : Prop := 
match c with
| insn_store _ _ v _ _ => v0 = v
| insn_alloca _ _ _ _ => v0 = value_const (const_undef (PI_typ pinfo))
| _ => False
end.

(* c in b is a store or an alloca with value v for pinfo.
   cs2 exactly follows c in b. *)
Definition alive_mop (v:value) (c:cmd) (cs2:cmds) (b:block) (pinfo:PhiInfo) 
  : Prop :=
blockInFdefB b (PI_f pinfo) = true /\
store_in_cmds (PI_id pinfo) cs2 = false /\
store_or_alloca_of_pid c pinfo /\
value_of_store_or_alloca c v pinfo /\
let '(_, stmts_intro _ cs _) := b in
exists cs1, exists cs3, cs = cs1 ++ c :: cs2 ++ cs3.

(* A record for alive memory operation. *)
Record MopInfo (pinfo: PhiInfo) := mkMopInfo {
  M_value : value;
  M_c : cmd;
  M_tail : cmds;
  M_block : block;
  M_alive : alive_mop M_value M_c M_tail M_block pinfo
}.

Ltac destruct_mopinfo :=
match goal with
| minfo: MopInfo _ |- _ =>
  destruct minfo as [M_v0 M_c0 M_tail0 [M_l0 [M_ps0 M_cs0 M_tmn0]] M_prop0];
  simpl in *;
  destruct M_prop0 as 
    [M_BInF0 [M_stincmds0 [M_mop [M_veq [M_cs1 [M_cs3 M_EQ]]]]]]; 
  subst; simpl
end.

(* This invariant says that the pinfo's value stored in memory equals to the 
   value of mop. *)
Definition wf_defs (pinfo:PhiInfo) minfo TD M gl (lc:DGVMap) : Prop :=
forall gvsa gvsv
  (Hlkpa: lookupAL _ lc (PI_id pinfo) = Some gvsa)
  (Hlkpv: Opsem.getOperandValue TD (M_value pinfo minfo) lc gl = Some gvsv),
  mload TD M gvsa (PI_typ pinfo) (PI_align pinfo) = Some gvsv.

(* cs is a chunk of commands following the mop. *)
Definition follow_alive_mop (pinfo:PhiInfo) minfo (cs:cmds) : Prop :=
let '(_, stmts_intro _ cs0 _) := M_block pinfo minfo in
forall cs1 cs3,
  cs0 = cs1 ++ M_c pinfo minfo :: M_tail pinfo minfo ++ cs3 ->
  (exists csa, exists csb,
    cs = csb ++ cs3 /\ M_tail pinfo minfo = csa ++ csb).

(* If the EC follows mop, then it must satisfy wf_defs. *)
Definition wf_ExecutionContext (pinfo:PhiInfo) minfo TD M gl
  (ec:Opsem.ExecutionContext) : Prop :=
Opsem.CurFunction ec = PI_f pinfo ->
Opsem.CurBB ec = M_block pinfo minfo ->
follow_alive_mop pinfo minfo (Opsem.CurCmds ec) ->
wf_defs pinfo minfo TD M gl (Opsem.Locals ec).

Fixpoint wf_ECStack (pinfo:PhiInfo) minfo TD M gl
  (ecs:Opsem.ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' =>
    wf_ExecutionContext pinfo minfo TD M gl ec /\
    wf_ECStack pinfo minfo TD M gl ecs'
end.

Definition wf_State (pinfo:PhiInfo) minfo
  (cfg:OpsemAux.Config) (S:Opsem.State) : Prop :=
wf_ECStack pinfo minfo (OpsemAux.CurTargetData cfg) (Opsem.Mem S)
  (OpsemAux.Globals cfg) (Opsem.ECS S).

(************************************************************)
(* Properties of follow_alive_mop *)

(* SSA ensures that the alive alloca cannot use pinfo; and
   Promotability ensures that the alive store cannot write pinfo into memory. *)
Lemma alive_mop_doesnt_use_promotable_allocas: forall pinfo minfo
  (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo -> 
  match (M_c pinfo minfo) with
  | insn_store _ _ v _ _ => v <> value_id (PI_id pinfo)
  | insn_alloca _ _ _ _ => used_in_cmd (PI_id pinfo) (M_c pinfo minfo) = false
  | _ => False
  end.
Proof.
  intros.
  destruct_mopinfo.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in M_BInF0; eauto using in_middle.
    apply WF_PhiInfo_spec3 in M_BInF0; auto.
    destruct M_c0; tinv M_mop; auto.
    intro EQ; subst.
    assert (G:=@valueEqB_refl (value_id (PI_id pinfo))).
    destruct (valueEqB (value_id (PI_id pinfo)) (value_id (PI_id pinfo)));
      simpl in *; try congruence.
Qed.

Lemma alive_mop_doesnt_use_its_followers_and_pid: forall l1 ps1 cs1' c cs tmn 
  id0 pinfo minfo s m (Huniq: uniqFdef (PI_f pinfo))
  (Hreach: isReachableFromEntry (PI_f pinfo) 
             (l1, stmts_intro ps1 (cs1' ++ c :: cs) tmn)) 
  (Hist: match (M_c pinfo minfo) with
         | insn_store _ _ _ _ _ => True
         | _ => False
         end),
  wf_fdef s m (PI_f pinfo) -> 
  (l1, stmts_intro ps1 (cs1' ++ c :: cs) tmn) = M_block pinfo minfo ->
  getCmdID c = Some id0 ->
  follow_alive_mop pinfo minfo (c::cs) ->
  used_in_value id0 (M_value pinfo minfo) = false /\ id0 <> PI_id pinfo.
Proof.
  intros.
Local Opaque isReachableFromEntry.
  unfold follow_alive_mop in H2.
  rewrite <- H0 in H2.
  destruct_mopinfo. inv H0.
  assert (J4':=H6).
  apply_clear H2 in H6.
  destruct H6 as [csa [csb [EQ1 EQ2]]]; subst.
  rewrite EQ1 in J4'. 
  anti_simpl_env. subst.
  simpl in M_BInF0.
  assert (J1':=M_BInF0).
  eapply wf_fdef__wf_cmd in M_BInF0; eauto using in_middle.
  destruct M_c0; tinv M_mop; tinv Hist.
  destruct M_mop; subst.
  simpl in M_veq; subst.
  inv M_BInF0.
  match goal with | H13: wf_insn_base _ _ _ |- _ => inv H13 end.
  assert (H0':=H0).
  apply destruct_insnInFdefBlockB in H0'. destruct H0' as [HcInB HcInF].
  rewrite <- EQ1 in *.
  find_wf_operand_list.
  match goal with
  | H4: wf_operand_list _, H1: getCmdID _ = _ |- _ =>
  eapply any_cmd_doesnt_use_following_operands 
    with (c1:=insn_store id5 (PI_typ pinfo) value1 
                (value_id (PI_id pinfo)) align5)
    (l3:=M_l0)(ps1:=M_ps0)
    (c:=c)
    (cs:=M_cs1 ++ insn_store id5 (PI_typ pinfo) value1 
                    (value_id (PI_id pinfo)) align5 :: 
         csa ++ c :: cs)(tmn1:=M_tmn0) in H4; eauto 1;
    clear - H4 H1;
    rewrite getCmdID__getCmdLoc with (id0:=id0) in H4; auto;
    destruct value1 as [i0|]; simpl in H4; simpl; try solve [
      destruct (id_dec i0 id0); subst; try solve [
        tauto |
        destruct (id_dec id0 (PI_id pinfo)); subst; auto
      ] |
      destruct (id_dec id0 (PI_id pinfo)); subst; auto
    ]
  end.
Qed.

Lemma alive_mop_doesnt_use_its_followers: forall l1 ps1 cs1' c cs tmn 
  id0 pinfo minfo s m (Huniq: uniqFdef (PI_f pinfo))
  (Hreach: isReachableFromEntry (PI_f pinfo) 
             (l1, stmts_intro ps1 (cs1' ++ c :: cs) tmn))
  (H: wf_fdef s m (PI_f pinfo))
  (H0: (l1, stmts_intro ps1 (cs1' ++ c :: cs) tmn) = M_block pinfo minfo)
  (H1: getCmdID c = Some id0)
  (H2: follow_alive_mop pinfo minfo (c::cs)),
  used_in_value id0 (M_value pinfo minfo) = false.
Proof.
  intros.
  destruct_mopinfo.
  destruct M_c0; tinv M_mop.
    simpl in M_veq; subst; auto.

    eapply alive_mop_doesnt_use_its_followers_and_pid in H2; simpl; eauto.
    tauto.
Qed.

Lemma follow_alive_mop_cons: forall pinfo minfo c cs l0 ps0 cs0 tmn0
  (Hneq: match M_c pinfo minfo, c with
         | insn_alloca _ _ _ _, insn_alloca _ _ _ _ => getCmdLoc c <> PI_id pinfo
         | _, _ => True
         end)
  (Huniq:uniqFdef (PI_f pinfo)),
  (l0, stmts_intro ps0 (cs0++c::cs) tmn0) = M_block pinfo minfo ->
  store_in_cmd (PI_id pinfo) c = false ->
  follow_alive_mop pinfo minfo cs ->
  follow_alive_mop pinfo minfo (c::cs).
Proof.
  unfold follow_alive_mop.
  intros.
  destruct_mopinfo. 
  intros.
  assert (M_cs1 = cs1 /\ M_cs3 = cs3) as J.
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
    destruct M_c0; tinv M_mop; destruct M_mop as [? ?]; subst.
      contradict Hneq; auto.

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

Lemma follow_alive_mop_at_beginning_false: forall (pinfo : PhiInfo)
  minfo (l' : l) (ps' : phinodes) (cs' : cmds)
  (tmn' : terminator)
  (J2 : (l', stmts_intro ps' cs' tmn') = M_block pinfo minfo)
  (J3 : follow_alive_mop pinfo minfo cs'),
  False.
Proof.
  intros.
  unfold follow_alive_mop in J3.
  rewrite <- J2 in J3.
  destruct_mopinfo.
  inv J2.
  destruct (J3 M_cs1 M_cs3) as [csa [csb [EQ1 EQ2]]]; subst; auto.
  anti_simpl_env.
Qed.

(************************************************************)
(* The following shows that wf_State is preserved by small-steps. *)

Lemma wf_defs_updateAddAL: forall pinfo minfo TD M lc' i1 gv1 gl
  (Hwfpi: WF_PhiInfo pinfo) (Huniq: uniqFdef (PI_f pinfo))
  (HwfDef: wf_defs pinfo minfo TD M gl lc')
  (Hneq: i1 <> PI_id pinfo)
  (Hnouse: used_in_value i1 (M_value pinfo minfo) = false),
  wf_defs pinfo minfo TD M gl (updateAddAL _ lc' i1 gv1).
Proof.
  intros. unfold wf_defs in *. intros.
  rewrite <- lookupAL_updateAddAL_neq in Hlkpa; auto.
  eapply HwfDef; eauto.
  eapply alive_mop_doesnt_use_promotable_allocas with (minfo:=minfo) in Hwfpi; 
    eauto.
  destruct (M_value pinfo minfo) as [i0|]; simpl in *; auto.
  destruct (id_dec i0 i1); simpl in Hnouse; try congruence.
  rewrite <- lookupAL_updateAddAL_neq in Hlkpv; auto.
Qed.

Lemma free_allocas_preserves_wf_defs: forall pinfo minfo TD Mem lc' als0 als Mem'
  gl maxb,
  Promotability.wf_defs maxb pinfo TD Mem lc' als0 ->
  wf_defs pinfo minfo TD Mem gl lc' ->
  NoDup (als ++ als0) ->
  free_allocas TD Mem als = ret Mem' ->
  wf_defs pinfo minfo TD Mem' gl lc'.
Proof.
  intros. unfold wf_defs in *. intros.
  assert (Hlkpa':=Hlkpa).
  eapply H0 in Hlkpa; eauto. clear H0.
  eapply H in Hlkpa'; eauto.
  destruct Hlkpa' as [J1 J2].
  destruct J1 as [_ [[mb [J1 [J3 J4]]] _]]; subst.
  eapply NoDup_disjoint in H1; eauto.
  eapply free_allocas_preserves_mload; eauto.
Qed.

Lemma free_allocas_preserves_wf_ECStack: forall maxb pinfo minfo td als gl ECs
  Mem Mem'
  (HwfECs : Promotability.wf_ECStack maxb pinfo td Mem ECs)
  (Hwfpi: WF_PhiInfo pinfo)
  (Hndup: NoDup (als ++ (flat_map
                  (fun ec : Opsem.ExecutionContext =>
                   let '{| Opsem.Allocas := als |} := ec in als)
                   ECs)))
  (Hwf: wf_ECStack pinfo minfo td Mem gl ECs)
  (Hfrees: free_allocas td Mem als = ret Mem'),
  wf_ECStack pinfo minfo td Mem' gl ECs.
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

Ltac preservation_sBranch :=
match goal with
| HwfS1 : wf_State _ _ _ _ |- _ =>
  destruct HwfS1 as [_ HwfECs];
  simpl in HwfECs;
  fold wf_ECStack in HwfECs;
  split; try solve [
    auto |
    intros J1 J2 J3; simpl in *; subst;
    eapply follow_alive_mop_at_beginning_false in J3; eauto;
    inv J3]
end.

Lemma preservation_return : forall maxb pinfo minfo (HwfPI : WF_PhiInfo pinfo)
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
  (HwfS1 : wf_State pinfo minfo cfg
            {| Opsem.ECS := EC1 :: EC2 :: EC;
               Opsem.Mem := Mem |}),
  wf_State pinfo minfo cfg
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
         [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l2 [ps2 [cs2' Heq2]]]]]]]]
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
    apply follow_alive_mop_cons in J2; 
      try solve [auto | destruct (M_c pinfo minfo); auto].
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
          eapply alive_mop_doesnt_use_its_followers;
            eauto using wf_system__wf_fdef.

      SSSSSCase "c' defines nothing".
        destruct n; inv HeqR. inv H1. auto.

    SSCase "wf_ECs".
      simpl.
      eapply free_allocas_preserves_wf_ECStack; eauto.
      apply NoDup_strenthening in Hdisjals; auto.
Qed.

Lemma preservation_return_void : forall maxb pinfo minfo
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
  (HwfS1 : wf_State pinfo minfo cfg
            {| Opsem.ECS := EC1 :: EC2 :: EC;
               Opsem.Mem := Mem |}),
  wf_State pinfo minfo cfg
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
         [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l2 [ps2 [cs2' Heq2]]]]]]]]
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
    apply follow_alive_mop_cons in J2; 
      try solve [eauto using wf_system__uniqFdef | 
                 destruct (M_c pinfo minfo); auto].
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
  (Hsz: getTypeAllocSize (los, nts) t = ret tsz)
  (Hal: malloc (los,nts) M tsz gn align0 = ret (M', mb)) minfo c
  (HBinF: blockInFdefB
             (l1, stmts_intro ps1 (cs1' ++ c :: cs)
                tmn) F = true)
  (Hid : getCmdID c = Some id0)
  (Hnst : store_in_cmd (PI_id pinfo) c = false)
  (Hsort : match c with
           | insn_malloc _ t0 _ _ | insn_alloca _ t0 _ _ => t = t0
           | _ => False
           end)
  (Hreach: isReachableFromEntry F
             (l1, stmts_intro ps1 (cs1' ++ c :: cs) tmn))
  (Hinscope : wf_ExecutionContext pinfo minfo (los,nts) M gl
               {|
               Opsem.CurFunction := F;
               Opsem.CurBB := (l1, stmts_intro ps1
                                (cs1' ++ c :: cs)
                                tmn);
               Opsem.CurCmds := c :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
  wf_ExecutionContext pinfo minfo (los,nts) M' gl
    {|
    Opsem.CurFunction := F;
    Opsem.CurBB := (l1, stmts_intro ps1
                      (cs1' ++ c :: cs) tmn);
    Opsem.CurCmds := cs;
    Opsem.Terminator := tmn;
    Opsem.Locals := updateAddAL (GVsT DGVs) lc id0
                       ($ blk2GV (los,nts) mb # typ_pointer t $);
    Opsem.Allocas := als' |}.
Proof.
  intros.
  intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
  assert (J2':=J2).
  remember (M_c pinfo minfo) as mc.
  destruct mc; try solve [subst; destruct_mopinfo; inv M_mop].
  Case "alloca".
    destruct (id_dec id0 (PI_id pinfo)); subst.
    SCase "id0 = PI_id pinfo".
      destruct_cmd c; tinv Hsort.
      SSCase "c = malloc".
        apply getCmdLoc_getCmdID in Hid; subst.
        eapply WF_PhiInfo_spec10 in HBinF; eauto.
          clear - Hid HBinF.
          contradict Hid; auto.
      
      SSCase "c = alloca".
        inv Hid.
        assert (wf_typ s (los,nts) t0) as Hwft.
          eapply wf_fdef__wf_cmd in HBinF; eauto using in_middle.
          inv HBinF. auto.
        clear - J2' J3 HwfF Hal Hsz Hwft HuniqF Hwfpi Heqmc. 
        destruct_mopinfo.
        simpl in M_veq.
        destruct M_mop as [? [? [? ?]]]; subst.
        unfold follow_alive_mop in J3. simpl in J3.
        destruct (J3 M_cs1 M_cs3) as [csa [csb [EQ1 EQ2]]]; subst; auto.
        unfold wf_defs. simpl. intros.
        rewrite lookupAL_updateAddAL_eq in Hlkpa. inv Hlkpa.
        simpl in Hlkpv. rewrite <- J2' in M_BInF0.
        anti_simpl_env.
        assert (t0 = PI_typ pinfo) as Heqt.
          simpl in M_BInF0.            
          apply WF_PhiInfo_spec1' in M_BInF0; auto.
            inv M_BInF0. auto.
        subst.
        eapply malloc_mload_undef; eauto.

   SCase "id0 <> PI_id pinfo".
     apply getCmdLoc_getCmdID in Hid. subst.
     apply follow_alive_mop_cons in J2; 
       try solve [auto | rewrite <- Heqmc; destruct c; auto].
     SSCase "1".
       apply Hinscope in J2; auto. simpl in J2.
       destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
       apply wf_defs_updateAddAL with (i1:=getCmdLoc c)
         (gv1:=($ blk2GV (los,nts) mb # typ_pointer t $)) in J2; auto.
       SSSCase "1.1".
         intros gvsa gvsv Hlkpa Hlkpv.
         eapply J2 in Hlkpv; eauto.
         eapply malloc_preserves_mload; eauto.
       SSSCase "1.2".
         destruct_mopinfo.
         simpl in M_veq.
         destruct M_mop; subst; auto.
     
  Case "store".
    apply follow_alive_mop_cons in J2; try solve [auto | rewrite <- Heqmc; auto].
    assert (Hfollow:=J2).
    assert (used_in_value id0 (M_value pinfo minfo) = false) as Hnuse.
      eapply alive_mop_doesnt_use_its_followers; eauto.
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
          eapply alive_mop_doesnt_use_its_followers_and_pid in J2'; simpl; 
            try solve [eauto | rewrite <- Heqmc; auto].
Qed.

Lemma malloc_preserves_wf_EC_in_tail : forall pinfo td M
  EC M' gl mb align0 gn tsz
  (Hal: malloc td M tsz gn align0 = ret (M', mb)) minfo
  (Hinscope : wf_ExecutionContext pinfo minfo td M gl EC),
  wf_ExecutionContext pinfo minfo td M' gl EC.
Proof.
  intros.
  intros J1 J2 J3.
  apply Hinscope in J3; auto.
  intros gvsa gvsv Hlkpa Hlkpv.
  eapply J3 in Hlkpv; eauto.
  eapply malloc_preserves_mload; eauto.
Qed.

Lemma malloc_preserves_wf_ECStack_in_tail : forall pinfo minfo TD M tsz gn
  align0 (Hwfpi: WF_PhiInfo pinfo) M' mb gl
  (Hmlc: malloc TD M tsz gn align0 = ret (M', mb)) ECs
  (Hwf: wf_ECStack pinfo minfo TD M gl ECs),
  wf_ECStack pinfo minfo TD M' gl ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct Hwf as [J1 J2].
    split; auto.
      eapply malloc_preserves_wf_EC_in_tail; eauto.
Qed.

Lemma free_preserves_wf_EC_in_tail : forall pinfo los nts M EC M' mptr0
  maxb gl (Hwfg: wf_globals maxb gl) Ps S F t
  (Hfree: free (los,nts) M mptr0 = ret M') minfo mptrs v lc
  (Hwft: wf_value S (module_intro los nts Ps) F v t)
  (H : Opsem.getOperandValue (los,nts) v lc gl = ret mptrs)
  (H0 : mptr0 @ mptrs)
  (Hinscope : wf_ExecutionContext pinfo minfo (los,nts) M gl EC)
  (Hht : wf_ECStack_head_in_tail maxb pinfo (los,nts) M lc EC),
  wf_ExecutionContext pinfo minfo (los,nts) M' gl EC.
Proof.
  intros.
  intros J1 J2 J3.
  apply Hinscope in J3; auto.
  intros gvsa gvsv Hlkpa Hlkpv.
  eapply J3 in Hlkpv; eauto.
  eapply free_preserves_mload; eauto.
    eapply operand__no_alias_with__tail; eauto.
Qed.

Lemma free_preserves_wf_ECStack_in_tail : forall maxb pinfo minfo los nts M
  (Hwfpi: WF_PhiInfo pinfo) M' gl mptr0 (Hwfg: wf_globals maxb gl)
  (Hfree: free (los,nts) M mptr0 = ret M') lc mptrs v t S Ps F
  (Hwft: wf_value S (module_intro los nts Ps) F v t)
  (H : Opsem.getOperandValue (los,nts) v lc gl = ret mptrs)
  (H0 : mptr0 @ mptrs) ECs
  (Hhts: wf_ECStack_head_tail maxb pinfo (los,nts) M lc ECs)
  (Hwf: wf_ECStack pinfo minfo (los,nts) M gl ECs),
  wf_ECStack pinfo minfo (los,nts) M' gl ECs.
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
  als ECs pinfo minfo
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
  (HwfS1 : wf_State pinfo minfo cfg
            {| Opsem.ECS := EC :: ECs;
               Opsem.Mem := Mem0 |})
  (Hnst : store_in_cmd (PI_id pinfo) c0 = false)
  (Hneq :  F = PI_f pinfo ->
           B = M_block pinfo minfo ->
           (id0 <> PI_id pinfo /\
            (follow_alive_mop pinfo minfo (c0 :: cs) ->
             used_in_value id0 (M_value pinfo minfo) = false))),
  wf_State pinfo minfo cfg
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
    destruct Hneq as [G1 G2]; auto.
    assert (J2':=J2).
    apply follow_alive_mop_cons in J2; auto.
      assert (J2'':=J2).
      apply Hinscope in J2; auto.
      eapply wf_defs_updateAddAL; eauto.

      destruct (M_c pinfo minfo); destruct c0; auto.
        inv Hid. auto.
Qed.

Lemma mstore_preserves_wf_EC_at_head: forall (maxb : Z) (pinfo : PhiInfo)
  minfo (S : system) los nts
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
  (Hinscope : wf_ExecutionContext pinfo minfo (los,nts) Mem gl
               {|
               Opsem.CurFunction := F;
               Opsem.CurBB := (l1, stmts_intro ps1
                                (cs1' ++ insn_store sid t v1 v2 align0 :: cs)
                                tmn);
               Opsem.CurCmds := insn_store sid t v1 v2 align0 :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
  wf_ExecutionContext pinfo minfo (los,nts) Mem' gl
     {|
     Opsem.CurFunction := F;
     Opsem.CurBB := (l1, stmts_intro ps1
                      (cs1' ++ insn_store sid t v1 v2 align0 :: cs) tmn);
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
    unfold follow_alive_mop in J3.
    rewrite <- J2 in J3.
    destruct_mopinfo.
    inv J2.
    assert (EQ':=H7).
    apply J3 in H7. clear J3.
    destruct H7 as [csa [csb [EQ1 EQ2]]]; subst.
    anti_simpl_env. 
    destruct csa.
      simpl_env in EQ'.
      apply app_inj_tail in EQ'.
      destruct EQ' as [EQ1 EQ2]; subst.
      intros gvsa gvsv Hlkpa Hlkpv.
      destruct M_mop; subst.
      simpl in *.
      rewrite H0 in Hlkpa. inv Hlkpa. inv H2. inv H1.
      rewrite Hlkpv in H. inv H.
      eapply MemProps.mstore_mload_same; eauto.
        eapply OpsemPP.getOperandValue__wf_gvs in Hlkpv; eauto.
        inv Hlkpv; eauto.

      elimtype False.
      assert (exists csa', exists c', [c] ++ csa = csa' ++ [c']) as EQ.
        apply head_tail_commut.
      destruct EQ as [csa' [c' EQ]].
      simpl_env in EQ'.
      rewrite EQ in EQ'.
      anti_simpl_env. rewrite_env (([c]++csa) ++ csb) in M_stincmds0.
      rewrite EQ in M_stincmds0.
      simpl_env in M_stincmds0.
      apply store_in_cmds_app in M_stincmds0.
      destruct M_stincmds0 as [G2 G3].
      apply store_in_cmds_app in G3.
      destruct G3 as [G3 G4].
      unfold store_in_cmds in G3.
      simpl in G3.
      rewrite G3 in HeqR. congruence.

    clear Hwft1 Hwfgl.
    apply follow_alive_mop_cons in J2; 
      try solve [auto | destruct (M_c pinfo minfo); auto].
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
  (H3 : mstore (los,nts) M mp2 t gv1 align0 = ret M') minfo
  (Hinscope : wf_ExecutionContext pinfo minfo (los,nts) M gl EC)
  (Hwft: wf_value S (module_intro los nts Ps) F v2 (typ_pointer t))
  (Hht : wf_ECStack_head_in_tail maxb pinfo (los,nts) M lc EC),
  wf_ExecutionContext pinfo minfo (los,nts) M' gl EC.
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
  (H3 : mstore (los,nts) M mp2 t gv1 align0 = ret M') minfo
  F S Ps
  (Hwft: wf_value S (module_intro los nts Ps) F v2 (typ_pointer t)) ECs
  (Hhts: wf_ECStack_head_tail maxb pinfo (los,nts) M lc ECs) 
  (Hwf: wf_ECStack pinfo minfo (los,nts) M gl ECs),
  wf_ECStack pinfo minfo (los,nts) M' gl ECs.
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
  minfo gvs fid oresult dck tret targs tr
  (Hcall: callExternalOrIntrinsics td gl M fid tret targs dck gvs = 
    ret (oresult, tr, M'))
  (Hinscope : wf_ExecutionContext pinfo minfo td M gl EC),
  wf_ExecutionContext pinfo minfo td M' gl EC.
Proof.
  intros.
  intros J1 J2 J3.
  apply Hinscope in J3; auto.
  intros gvsa gvsv Hlkpa Hlkpv.
  eapply J3 in Hlkpv; eauto.
  eapply MemProps.callExternalOrIntrinsics_preserves_mload; eauto.
Qed.

Lemma callExternalFunction_preserves_wf_ECStack_in_tail: forall Mem fid gvs
  oresult Mem' pinfo minfo TD gl ECs dck tret targs tr,
  callExternalOrIntrinsics TD gl Mem fid tret targs dck gvs = 
    ret (oresult, tr, Mem') ->
  wf_ECStack pinfo minfo TD Mem gl ECs ->
  wf_ECStack pinfo minfo TD Mem' gl ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct H0.
    split; eauto.
      eapply callExternalFunction_preserves_wf_EC_in_tail; eauto.
Qed.

Lemma callExternalFunction_preserves_wf_ECStack_at_head: forall Mem fid gvs
  oresult Mem' pinfo minfo gl rid noret0 ca rt1 va1 fv lp cs lc lc' als tmn
  cs1' l1 ps1 F s los nts dck Ps (Hwfpi : WF_PhiInfo pinfo) tret targs tr
  (HwfF: wf_fdef s (module_intro los nts Ps) F) (HuniqF: uniqFdef F)
  (H4 : callExternalOrIntrinsics (los,nts) gl Mem fid tret targs dck gvs 
          = ret (oresult, tr, Mem'))
  (H5 : Opsem.exCallUpdateLocals (los,nts) rt1 noret0 rid oresult lc = ret lc')
  (HBinF : blockInFdefB 
             (l1, stmts_intro ps1 
               (cs1' ++ insn_call rid noret0 ca rt1 va1 fv lp :: cs) tmn)
             F = true)
  (Hreach: isReachableFromEntry F
             (l1, stmts_intro ps1 
               (cs1' ++ insn_call rid false ca rt1 va1 fv lp :: cs) tmn))
  (Hinscope : wf_ExecutionContext pinfo minfo (los,nts) Mem gl
               {|
               Opsem.CurFunction := F;
               Opsem.CurBB := (l1, stmts_intro ps1
                                (cs1' ++
                                 insn_call rid noret0 ca rt1 va1 fv lp :: cs) tmn);
               Opsem.CurCmds := insn_call rid noret0 ca rt1 va1 fv lp :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
   wf_ExecutionContext pinfo minfo (los,nts) Mem' gl
     {|
     Opsem.CurFunction := F;
     Opsem.CurBB := (l1, stmts_intro ps1
                      (cs1' ++ insn_call rid noret0 ca rt1 va1 fv lp :: cs) tmn);
     Opsem.CurCmds := cs;
     Opsem.Terminator := tmn;
     Opsem.Locals := lc';
     Opsem.Allocas := als |}.
Proof.
  intros.
  intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
  assert (J2':=J2).
  apply follow_alive_mop_cons in J2; 
    try solve [auto | destruct (M_c pinfo minfo); auto].
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
    assert (used_in_value rid (M_value pinfo minfo) = false) as Hnouse.
      eapply alive_mop_doesnt_use_its_followers; eauto
        using wf_system__wf_fdef.
      eapply follow_alive_mop_cons;
        try solve [eauto | destruct (M_c pinfo minfo); auto].  
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
  eapply alive_mop_doesnt_use_its_followers; try solve [
    eauto using wf_system__wf_fdef |
    match goal with
    | HBinF1 : blockInFdefB (_, stmts_intro _ (_ ++ _ :: _) _) _ = true |- _ =>
       eapply WF_PhiInfo_spec10 in HBinF1; eauto using wf_system__uniqFdef
    end].

Ltac preservation_pure_cmd_updated_case:=
  abstract (eapply preservation_pure_cmd_updated_case; eauto; try solve
    [simpl; auto | preservation_pure_cmd_updated_case_helper]).

Ltac free_preserves_wf_EC_at_head :=
match goal with
| Hinscope: wf_ExecutionContext ?pinfo ?minfo _ _ _ _ |- _ =>
  intros J1 J2 J3; simpl in J1, J2, J3; simpl; subst;
  assert (J2':=J2); 
  apply follow_alive_mop_cons in J2; try solve
    [eauto using wf_system__uniqFdef | destruct (M_c pinfo minfo); auto];
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

(* The main result. *)
Lemma preservation : forall maxb pinfo minfo cfg S1 S2 tr
  (Hwfg: wf_globals maxb (OpsemAux.Globals cfg))
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (HsInsn: Opsem.sInsn cfg S1 S2 tr)
  (HwfS1: wf_State pinfo minfo cfg S1), wf_State pinfo minfo cfg S2.
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
    eapply follow_alive_mop_at_beginning_false in J2; eauto; inv J2 |
    split; auto]).

Case "sExCall".
  abstract (
  destruct_ctx_other;
  split; simpl; try solve [
    eapply callExternalFunction_preserves_wf_ECStack_at_head; eauto using
      wf_system__wf_fdef, wf_system__uniqFdef |
    eapply callExternalFunction_preserves_wf_ECStack_in_tail; eauto]).
Qed.

Lemma preservation_star : forall maxb pinfo minfo cfg S1 S2 tr
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg)) (Hle: 0 <= maxb)
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (Hstar: Opsem.sop_star cfg S1 S2 tr)
  (HwfS1: wf_State pinfo minfo cfg S1), 
  wf_State pinfo minfo cfg S2.
Proof.
  intros.
  induction Hstar; auto.
    apply IHHstar.
      apply OpsemPP.preservation in H; auto.
      eapply Promotability.preservation in H; eauto.
      eapply preservation in H; eauto.
Qed.  

Lemma preservation_plus : forall maxb pinfo minfo cfg S1 S2 tr
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg)) (Hle: 0 <= maxb)
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (Hplus: Opsem.sop_plus cfg S1 S2 tr)
  (HwfS1: wf_State pinfo minfo cfg S1), 
  wf_State pinfo minfo cfg S2.
Proof.
  intros.
  apply OpsemProps.sop_plus__implies__sop_star in Hplus.
  eapply preservation_star; eauto.
Qed.  

Lemma s_genInitState__alive_mop: forall S main VarArgs cfg IS pinfo minfo
  (HwfS : wf_system S) (Hwfpi: WF_PhiInfo pinfo) 
  (Hinit : @Opsem.s_genInitState DGVs S main VarArgs Mem.empty = ret (cfg, IS)),
  wf_State pinfo minfo cfg IS.
Proof.
  intros.
  simpl_s_genInitState. 
  split; simpl; auto.
  unfold wf_ExecutionContext. simpl.
  intros.
  unfold wf_defs.
  intros.
  apply getParentOfFdefFromSystem__moduleInProductsInSystemB in HeqR0.
  destruct HeqR0 as [J1 J2].
  rewrite H in *.
  eapply wf_system__uniqFdef in J1; eauto.
  replace a with (getArgsOfFdef (PI_f pinfo)) in HeqR3.
    erewrite WF_PhiInfo__pid_isnt_in_init in Hlkpa; eauto.
    congruence.

    rewrite <- H. auto.
Qed.
