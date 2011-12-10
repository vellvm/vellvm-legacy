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

Import Promotability.

(* We define a special las used by mem2reg that only considers local commands.
   In general, it should be extended to the las defined w.r.t domination and
   memory dependency (which we are aiming in the future work)

   The current mem2reg also does SAS eliminations before all loads are removed.
   For example,
     st v1 p; ...; st v2 p; ...
   if there are no other lds in the first ..., the first ``st v1 p'' can be 
   removed.

   In practice, such a code after phiplacement may exist if the original code 
   also does store to the promotable alloca. 

   An alternative approach is that we only consider such elimination after all
   possible removed loads are removed, as what the paper presents. mem2reg does
   not check if there are any unremoved loads in unreachable blocks. If so,
   some stores cannot be removed. We need to let mem2reg ignore the loads of
   unreachable blocks to remove what SAS can eliminate.

   For this reason, here, we give the abstract properties that las needs to hold.
   The properties do not depend on the concrete design in mem2reg, such as
   find_init_stld, find_next_stld, ... So the proofs can still work if we change
   mem2reg. We should prove that the design in mem2reg satisfy the properties.
 *)

Definition store_in_cmd (id':id) (c:cmd) : bool :=
match c with
| insn_store _ _ _ ptr _ => used_in_value id' ptr
| _ => false
end.

Definition store_in_cmds (id':id) (cs:cmds) : bool := 
(List.fold_left (fun re c => re || store_in_cmd id' c) cs false).

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

Lemma storeinfo_doesnt_use_promotable_allocas: forall pinfo stinfo,
  WF_PhiInfo pinfo -> SI_value pinfo stinfo <> value_id (PI_id pinfo).
Admitted.

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

Lemma follow_alive_store_cons: forall pinfo stinfo c cs l0 ps0 cs0 tmn0,
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
  assert (cs1 = cs2 /\ cs3 = cs4) as J. admit.
  destruct J as [EQ1 EQ2]; subst. clear H2.
  edestruct H1 as [csa [csb [EQ1 EQ2]]]; eauto. clear H1.
  subst. inv H.
  rewrite_env 
    (((cs2 ++
       insn_store SI_id0 (PI_typ pinfo) SI_value0 (value_id (PI_id pinfo))
         (PI_align pinfo) :: csa) ++ csb) ++ cs4) in H4.
  rewrite_env (((cs0 ++ [c]) ++ csb) ++ cs4) in H4.
  apply app_inv_tail in H4.
  apply app_inv_tail in H4.
  destruct csa.
    simpl_env in H4.
    apply app_inj_tail in H4.
    destruct H4 as [EQ1 EQ2]; subst.
    simpl in H0. 
    destruct (id_dec (PI_id pinfo) (PI_id pinfo)); simpl in H0; congruence.

    assert (exists csa', exists c2, [c0] ++ csa = csa' ++ [c2]) as EQ. admit.
    destruct EQ as [csa' [c2 EQ]].
    simpl_env in H4.
    rewrite EQ in H4.
    rewrite_env ((cs2 ++
      insn_store SI_id0 (PI_typ pinfo) SI_value0 (value_id (PI_id pinfo))
        (PI_align pinfo) :: csa') ++ [c2]) in H4.
    apply app_inj_tail in H4.
    destruct H4 as [EQ1 EQ2]; subst.
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
  destruct J1 as [[mb [J1 [J3 J4]]] _]; subst.
  eapply NoDup_disjoint in H1; eauto.
  eapply free_allocas_preserves_mload; eauto.
Qed.

Lemma wf_defs_updateAddAL: forall pinfo stinfo TD M lc' i1 gv1 gl
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfDef: wf_defs pinfo stinfo TD M gl lc') 
  (Hneq: i1 <> PI_id pinfo) 
  (Hnouse: used_in_value i1 (SI_value pinfo stinfo) = false),
  wf_defs pinfo stinfo TD M gl (updateAddAL _ lc' i1 gv1).
Proof.
  intros. unfold wf_defs in *. intros.
  rewrite <- lookupAL_updateAddAL_neq in Hlkpa; auto.
  eapply HwfDef; eauto.
  apply storeinfo_doesnt_use_promotable_allocas with (stinfo:=stinfo) in Hwfpi.
  destruct (SI_value pinfo stinfo); simpl in *; auto.
  destruct (id_dec i0 i1); simpl in Hnouse; try congruence.
  rewrite <- lookupAL_updateAddAL_neq in Hlkpv; auto.
Qed.

Lemma preservation : forall maxb pinfo stinfo cfg S1 S2 tr
  (Hwfpp: OpsemPP.wf_State cfg S1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (HsInsn: Opsem.sInsn cfg S1 S2 tr)
  (HwfS1: wf_State pinfo stinfo cfg S1), wf_State pinfo stinfo cfg S2.
Proof.
  intros.
  (sInsn_cases (induction HsInsn) Case); destruct TD as [los nts]; simpl HwfS1.

Case "sReturn". 
Focus.

  destruct Hwfpp as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [_ [_ [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC0 HwfCall]
       ]
       HwfCall'
     ]
    ]]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0.

  (*clear Hwfpp.*)
  destruct HwfS1 as [Hinscope1 [Hinscope2 HwfECs]]. simpl. 
  simpl in Hinscope1, Hinscope2, HwfECs.
  fold wf_ECStack in HwfECs.

  destruct Hnoalias as 
    [
      [[Hinscope1' Hwflc1] [[[Hinscope2' Hwflc2] [HwfECs' Hfr2]] Hfr1]] 
      [Hdisjals HwfM]
    ]. simpl. simpl in Hdisjals.
  split.
    SSCase "wf_EC".
    intros J1 J2 J3. simpl in J1, J2, J3. simpl. subst.
    remember (getCmdID c') as R.
    destruct c'; try solve [inversion H].
    unfold wf_ExecutionContext in *. simpl in Hinscope1, Hinscope2.
    assert (J2':=J2).
    apply follow_alive_store_cons in J2; auto.
    apply Hinscope2 in J2; auto.
    assert (NoDup (als ++ als')) as Hnodup.
      destruct Hdisjals as [Hdisjals _].
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
        destruct t; tinv H1.

        remember (lift_op1 DGVs (fit_gv (los, nts) t) g t) as R2.
        destruct R2; inv H1.
        apply wf_defs_updateAddAL; auto.
          admit. (* call <> alloca *)

          clear - J2' J3.
          admit. (* sid <> i0 *)
      SSSSSCase "c' defines nothing".
        destruct n; inv HeqR. inv H1. auto.

    SSCase "wf_ECs".
      simpl.
      eapply free_allocas_preserves_wf_ECStack; eauto.
      apply NoDup_strenthening in Hdisjals'; auto.

Transparent inscope_of_tmn inscope_of_cmd.

asdasdasdasdddddddddddddddd


  destruct cfg as [S1 TD1 Ps1 gl1 fs1].

  destruct St1 as [ECs1 M1];
  destruct TD1 as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Heq2 
    [Heq3 Heq4]]]]]]]]; subst;
  destruct ECs1 as [|[F1 B1 cs1 tmn1 lc1 als1] ECs1];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct ECs1 as [|[F1' B1' cs1' tmn1' lc1' als1'] ECs1];
    try solve [inversion HsimECs];
  destruct HsimECs as [HsimEC' HsimECs];
  destruct HsimEC as [HBinF [HFinPs [Htfdef [Heq0 [Heq1 [Hbsim [Heqb1 [Heqb2     
    [Hrsim Htcmds]]]]]]]]]; subst;
  destruct c'; try solve [inversion HsimEC'];
  destruct HsimEC' as [HBinF' [HFinPs' [Htfdef' [Heq0' [Heq1' [Hbsim' 
    [Heqb1' [Heqb2' [Hrsim' Htcmds']]]]]]]]]; subst;
  fold ECs_simulation_tail in HsimECs


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
      (ifs:=nil)(S:=S1)(m:=module_intro los nts Ps1); 
      simpl; try solve [auto | solve_tmnInFdefBlockB].
  eapply returnUpdateLocals_rsim in H1; eauto.
  destruct H1 as [lc1'' [H1 Hrsim'']].
  exists 
    (Opsem.mkState ((Opsem.mkEC F1' B1' cs1'0 tmn' lc1'' als')::ECs1) Mem').
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply OpsemProps.sInsn__implies__sop_star.
    constructor; auto.
  
    repeat (split; eauto 2 using cmds_at_block_tail_next).
      destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
      destruct Heqb2' as [l2 [ps2 [cs21 Heqb2']]]; subst.
      eapply cmds_simulation_stable; eauto.
      eapply ECs_simulation_tail_stable; eauto.
Unfocus.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
