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
Require Import memory_props.
Require Import mem2reg.
Require Import program_sim.
Require Import trans_tactic.

Definition sas (sid1 sid2: id) (v1 v2:value) (cs2:cmds) (b:block) 
  (pinfo:PhiInfo) : Prop :=         
blockInFdefB b (PI_f pinfo) = true /\
load_in_cmds (PI_id pinfo) cs2 = false /\
let '(block_intro _ _ cs _) := b in
exists cs1, exists cs3,
  cs = 
  cs1 ++ 
  insn_store sid1 (PI_typ pinfo) v1 (value_id (PI_id pinfo)) (PI_align pinfo) ::
  cs2 ++ 
  insn_store sid2 (PI_typ pinfo) v2 (value_id (PI_id pinfo)) (PI_align pinfo) ::
  cs3.

Record SASInfo (pinfo: PhiInfo) := mkSASInfo {
  SAS_sid1 : id;
  SAS_sid2 : id;
  SAS_value1 : value;
  SAS_value2 : value;
  SAS_tail : cmds;
  SAS_block : block;
  SAS_prop: sas SAS_sid1 SAS_sid2 SAS_value1 SAS_value2 SAS_tail SAS_block pinfo
}.

Definition fdef_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) f1 f2 
  : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_fdef (SAS_sid1 pinfo sasinfo) f1 = f2
  else f1 = f2.

Definition cmds_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) (f1:fdef) 
  cs1 cs2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_cmds (SAS_sid1 pinfo sasinfo) cs1 = cs2
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) (f1:fdef) 
  b1 b2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_block (SAS_sid1 pinfo sasinfo) b1 = b2
  else b1 = b2.

Definition products_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) Ps1 Ps2
  : Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation pinfo sasinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) S1 S2 
  : Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation pinfo sasinfo Ps1 Ps2
   end) S1 S2.

Definition EC_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  (EC1 EC2:@Opsem.ExecutionContext DGVs) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation pinfo sasinfo f1 f2 /\
       tmn1 = tmn2 /\
       als1 = als2 /\
       block_simulation pinfo sasinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       lc1 = lc2 /\
       cmds_simulation pinfo sasinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  (ECs1 ECs2:@Opsem.ECStack DGVs) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation pinfo sasinfo EC1 EC2 /\ 
    ECs_simulation pinfo sasinfo ECs1' ECs2'
| _, _ => False
end.

Definition cs_follow_dead_store (pinfo:PhiInfo) (sasinfo: SASInfo pinfo)
  (cs:cmds) : Prop :=
let '(block_intro _ _ cs0 _) := SAS_block pinfo sasinfo in
forall cs1 cs3, 
  cs0 = 
    cs1 ++ 
    insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
      (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) (PI_align pinfo) ::
    SAS_tail pinfo sasinfo ++ 
    cs3 ->
  (exists csa, exists csb, 
    cs = csb ++ cs3 /\ SAS_tail pinfo sasinfo = csa ++ csb).

Definition EC_follow_dead_store (pinfo:PhiInfo) (sasinfo: SASInfo pinfo)
  (ec:@Opsem.ExecutionContext DGVs) : Prop :=
Opsem.CurFunction ec = PI_f pinfo /\
Opsem.CurBB ec = SAS_block pinfo sasinfo /\
cs_follow_dead_store pinfo sasinfo (Opsem.CurCmds ec).

Definition undead_head_in_tail (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) ptr
  (ec0:@Opsem.ExecutionContext DGVs) : Prop :=
forall gvsa (Heq: Opsem.CurFunction ec0 = PI_f pinfo)
  (Hlkup: lookupAL _ (Opsem.Locals ec0) (PI_id pinfo) = Some gvsa),
  MemProps.no_alias ptr gvsa \/ ~ EC_follow_dead_store pinfo sasinfo ec0.

Definition undead_head_tail (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) ptr 
  (ecs':list Opsem.ExecutionContext) : Prop :=
  forall ec0 (Hin: In ec0 ecs'), undead_head_in_tail pinfo sasinfo ptr ec0.

Definition Mem_simulation (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) TD 
  (ecs1:list Opsem.ExecutionContext) Mem1 Mem2 : Prop :=
Mem.nextblock Mem1 = Mem.nextblock Mem2 /\
forall ptr ty al gvs1 gvs2 
  (Hnalias: undead_head_tail pinfo sasinfo ptr ecs1)
  (Hld1: mload TD Mem1 ptr ty al = Some gvs1)
  (Hld2: mload TD Mem2 ptr ty al = Some gvs2),
  gvs1 = gvs2.

Definition State_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\ 
    products_simulation pinfo sasinfo Ps1 Ps2 /\
    ECs_simulation pinfo sasinfo ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ Mem_simulation pinfo sasinfo TD1 ECs1 M1 M2
end.

Definition removable_State (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  (St:@Opsem.State DGVs) : Prop :=
match St with
| Opsem.mkState
    (Opsem.mkEC f b 
      (insn_store sid _ _ _ _ :: cs) 
      tmn lc als::_) _ => 
    if (fdef_dec (PI_f pinfo) f) then 
      if (id_dec sid (SAS_sid1 pinfo sasinfo)) 
      then True else False
    else False
| _ => False
end.

Lemma removable_State_dec : forall pinfo sasinfo St,
  removable_State pinfo sasinfo St \/ ~ removable_State pinfo sasinfo St.
Proof.
  destruct St. 
  destruct ECS as [|[]]; auto.
  destruct CurCmds; auto.
  simpl.
  destruct c; auto.
  destruct (fdef_dec (PI_f pinfo) CurFunction); auto.
  destruct (id_dec i0 (SAS_sid1 pinfo sasinfo)); auto.
Qed.

Ltac repeat_solve :=
  repeat (match goal with
          | |- Mem_simulation _ _ _ _ _ _ => idtac 
          | |- _ => split; eauto 2 using cmds_at_block_tail_next
          end).

Lemma mstore_removable_Mem_simulation: forall TD M1 mp2 gv1 a M1' pinfo lc2 gl2
  B1 cs1 tmn2 als2 ECs1 M2 t v sasinfo v0
  (Huniq: uniqFdef (PI_f pinfo))
  (HBinF1 : blockInFdefB B1 (PI_f pinfo) = true)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B1 =
               block_intro l1 ps1
                 (cs11 ++ insn_store (SAS_sid1 pinfo sasinfo) t v v0 a :: cs1)
                 tmn2)
  (H23: mstore TD M1 mp2 t gv1 a = ret M1')
  (H20 : @Opsem.getOperandValue DGVs TD v0 lc2 gl2 = ret mp2)
  (H19 : Opsem.getOperandValue TD v lc2 gl2 = ret gv1)
  (Hmsim: Mem_simulation pinfo sasinfo TD
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := insn_store (SAS_sid1 pinfo sasinfo) t v v0 a
                              :: cs1;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: ECs1) M1 M2),
  Mem_simulation pinfo sasinfo TD
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := cs1;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: ECs1) M1' M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 Hmsim2].
  split.
    apply MemProps.nextblock_mstore in H23.
    rewrite <- H23. auto.

    intros. 
    assert (In {|
               Opsem.CurFunction := PI_f pinfo;
               Opsem.CurBB := B1;
               Opsem.CurCmds := cs1;
               Opsem.Terminator := tmn2;
               Opsem.Locals := lc2;
               Opsem.Allocas := als2 |}
              ({|
               Opsem.CurFunction := PI_f pinfo;
               Opsem.CurBB := B1;
               Opsem.CurCmds := cs1;
               Opsem.Terminator := tmn2;
               Opsem.Locals := lc2;
               Opsem.Allocas := als2 |} :: ECs1)) as Hin. simpl. auto.
    apply Hnalias in Hin. 
    unfold undead_head_in_tail in Hin. simpl in Hin.
    assert (v0 = value_id (PI_id pinfo)) as EQ.
      admit. (* uniqness *)
    subst. simpl in H20.
    assert (Hlkup:=H20).
    apply Hin in H20; auto.
    destruct H20 as [Hnalias' | Hnfollow].
      eapply Hmsim2; eauto.
        unfold undead_head_tail. intros.
        simpl in Hin0.
        destruct Hin0 as [Hin0 | Hin0]; subst.
          unfold undead_head_in_tail. simpl.
          intros. rewrite Hlkup in Hlkup0. inv Hlkup0. auto.

          apply Hnalias. simpl. auto.

        apply MemProps.no_alias_sym in Hnalias'.
        eapply MemProps.mstore_preserves_mload_inv'; eauto.

      contradict Hnfollow.
      destruct Heq3 as [l1 [ps1 [cs11 Heq3]]]; subst.
      split; auto. simpl.
      assert (block_intro l1 ps1
               (cs11 ++
                insn_store (SAS_sid1 pinfo sasinfo) t v (value_id (PI_id pinfo)) 
                  a :: cs1) tmn2 = SAS_block pinfo sasinfo) as EQ.
        admit. (* uniqness *)
      split; auto.
        unfold cs_follow_dead_store.
        rewrite <- EQ.
        clear - HBinF1.
        intros.
        assert (cs11 = cs0 /\ cs1 = SAS_tail pinfo sasinfo ++ cs3 /\
                t = PI_typ pinfo /\ v = SAS_value1 pinfo sasinfo /\
                a = PI_align pinfo) as EQ.
          admit.
        destruct EQ as [EQ1 [EQ2 [EQ3 [EQ4 EQ5]]]]; subst.
        exists nil. exists (SAS_tail pinfo sasinfo). auto.
Qed.

Lemma cmds_simulation_elim_cons_inv: forall (pinfo : PhiInfo) sasinfo
  (t : typ) (v1 v2: value) (a : align) (cs1 : list cmd) (cs2 : cmds)
  (Hcssim2 : 
   cmds_simulation pinfo sasinfo (PI_f pinfo)
     (insn_store (SAS_sid1 pinfo sasinfo) t v1 v2 a :: cs1)
     cs2),
  cmds_simulation pinfo sasinfo (PI_f pinfo) cs1 cs2.
Proof.
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  simpl in *.
  destruct (id_dec (SAS_sid1 pinfo sasinfo) (SAS_sid1 pinfo sasinfo)); 
    simpl in *; try congruence.
Qed.


Lemma cmds_simulation_nil_inv: forall pinfo sasinfo f1 cs,
  cmds_simulation pinfo sasinfo f1 nil cs -> cs = nil.
Proof.
  unfold cmds_simulation. simpl.
  intros. destruct (fdef_dec (PI_f pinfo) f1); auto.
Qed.

Lemma cmds_simulation_nelim_cons_inv: forall pinfo sasinfo F c cs2 cs',
  cmds_simulation pinfo sasinfo F (c :: cs2) cs' ->
  (PI_f pinfo = F -> getCmdLoc c <> SAS_sid1 pinfo sasinfo) ->
  exists cs2', 
    cs' = c :: cs2' /\ cmds_simulation pinfo sasinfo F cs2 cs2'.
Proof.  
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); subst; simpl; eauto.
  assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
  apply H0 in EQ.
  destruct (id_dec (getCmdLoc c) (SAS_sid1 pinfo sasinfo)); 
    simpl in *; try congruence.
  eauto.
Qed.

Ltac destruct_ctx_return :=
match goal with
| Hwfpp : OpsemPP.wf_State
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |} _,
  Hnoalias : Promotability.wf_State _ _ _ _,
  Hsim : State_simulation _ _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfpp as 
    [Hwfg [HwfSystem [HmInS [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [ 
       [
         [Hreach2 [HBinF2 [HFinPs2 _]]]
         _
       ]
       HwfCall'
     ]]
    ]]]]; subst;
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
      [Hfsim2 [Heq1 [Heq2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct Hecsim' as 
      [Hfsim2' [Htsim2' [Heq2' [Hbsim2' 
        [Heq3' [Heq4' [Hlcsim2' Hcssim2']]]]]]]; subst;
  destruct Hnoalias as 
    [
      [[Hinscope1' _] [[[Hinscope2' _] [HwfECs' _]] _]] 
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals;
  fold Promotability.wf_ECStack in HwfECs';
  apply cmds_simulation_nil_inv in Hcssim2; subst;
  wfCall_inv;
  apply cmds_simulation_nelim_cons_inv in Hcssim2'; try solve [
    auto |
    try match goal with
        | |- _ = _ -> _ <> _ => admit
        end ];
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result
end.


Lemma cs_follow_dead_store_isnt_nil: forall pinfo sasinfo,
  cs_follow_dead_store pinfo sasinfo nil -> False.
Proof.
  intros.
  unfold cs_follow_dead_store in H.
  destruct sasinfo. simpl in *.
  destruct SAS_block0.
  destruct SAS_prop0 as [J1 [J4 [cs1 [cs2 EQ]]]].
  apply H in EQ.
  destruct EQ as [csa [csb [EQ1 EQ2]]].
  symmetry in EQ1.
  apply app_eq_nil in EQ1. destruct EQ1 as [EQ11 EQ12]. inv EQ12.
Qed.

Lemma undead_head_in_tail_nil: forall pinfo sasinfo ptr F B tmn lc als,
  undead_head_in_tail pinfo sasinfo ptr
    {| Opsem.CurFunction := F;
       Opsem.CurBB := B;
       Opsem.CurCmds := nil;
       Opsem.Terminator := tmn;
       Opsem.Locals := lc;
       Opsem.Allocas := als |}.
Proof.
  intros.
  unfold undead_head_in_tail. simpl. intros.
  right. intros [J1 [J2 J3]]. simpl in J1, J2, J3.
  eapply cs_follow_dead_store_isnt_nil; eauto.
Qed.

Lemma cs_follow_dead_store_tail: forall pinfo sasinfo c cs,
  getCmdLoc c <> SAS_sid2 pinfo sasinfo ->
  cs_follow_dead_store pinfo sasinfo (c :: cs) ->
  cs_follow_dead_store pinfo sasinfo cs.
Proof.
  unfold cs_follow_dead_store.
  destruct sasinfo. simpl. intros.
  destruct SAS_block0.
  intros. 
  destruct SAS_prop0 as [EQ1 [EQ2 [cs4 [cs2 EQ3]]]]; subst.
  assert (cs4 = cs1 /\ 
          cs3 = insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
                  (value_id (PI_id pinfo)) (PI_align pinfo) :: cs2) as EQ.
    admit. 
  destruct EQ as [EQ3 EQ4]; subst.
  edestruct H0 as [csa [csb [J1 J2]]]; subst; eauto.
  destruct csb.
    inv J1. contradict H; auto.

    inv J1. exists (csa++[c0]). exists csb. simpl_env. split; auto.
Qed.

Lemma EC_follow_dead_store_tail: forall pinfo sasinfo c cs B tmn3 lc1 als3 lc2 F,
  getCmdLoc c <> SAS_sid2 pinfo sasinfo ->
  ~ EC_follow_dead_store pinfo sasinfo
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc1;
         Opsem.Allocas := als3 |} ->
  ~ EC_follow_dead_store pinfo sasinfo
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := c :: cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc2;
         Opsem.Allocas := als3 |}.
Proof.
  intros.
  intro J. apply H0.
  destruct J as [J1 [J2 J3]]. simpl in *.
  split; auto.
  split; auto.
    simpl. 
    eapply cs_follow_dead_store_tail; eauto.
Qed.

Lemma cs_follow_dead_store_at_beginning_false: forall (pinfo : PhiInfo) 
  (sasinfo : SASInfo pinfo) (l' : l) (ps' : phinodes) (cs' : cmds) 
  (tmn' : terminator) 
  (J2 : block_intro l' ps' cs' tmn' = SAS_block pinfo sasinfo)
  (J3 : cs_follow_dead_store pinfo sasinfo cs'),
  False.
Proof.
  intros.
  unfold cs_follow_dead_store in J3.
  rewrite <- J2 in J3.
  destruct sasinfo. simpl in *.
  rewrite <- J2 in SAS_prop0.
  destruct SAS_prop0 as [_ [_ [cs1 [cs3 J]]]].
  assert (J':=J).
  apply J3 in J.
  destruct J as [csa [csb [EQ1 EQ2]]]; subst.
  rewrite_env (
    (cs1 ++
     insn_store SAS_sid3 (PI_typ pinfo) SAS_value3 
         (value_id (PI_id pinfo)) (PI_align pinfo) :: (csa ++ csb)) ++ 
     insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
            (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3
    ) in J'.
  apply app_inv_tail in J'. 
  rewrite_env (nil ++ csb) in J'.
  rewrite_env (
    (cs1 ++
       insn_store SAS_sid3 (PI_typ pinfo) SAS_value3 
         (value_id (PI_id pinfo)) (PI_align pinfo) :: 
       csa) ++ csb
    ) in J'.
  apply app_inv_tail in J'. 
  assert (
    In (insn_store SAS_sid3 (PI_typ pinfo) SAS_value3 
         (value_id (PI_id pinfo)) (PI_align pinfo)) nil) as Hin.
    rewrite J'. apply in_middle.
  inv Hin.
Qed.

Lemma cs_follow_dead_store_at_end_false: forall (pinfo : PhiInfo) 
  (sasinfo : SASInfo pinfo) (J3 : cs_follow_dead_store pinfo sasinfo nil),
  False.
Proof.
  intros.
  unfold cs_follow_dead_store in J3.
  destruct sasinfo. simpl in *. destruct SAS_block0.
  destruct SAS_prop0 as [_ [_ [cs1 [cs3 J]]]].
  assert (J':=J).
  apply J3 in J.
  destruct J as [csa [csb [EQ1 EQ2]]]; subst.
  assert (
    In (insn_store SAS_sid4 (PI_typ pinfo) SAS_value4 
         (value_id (PI_id pinfo)) (PI_align pinfo)) nil) as Hin.
    rewrite EQ1. apply in_middle.
  inv Hin.
Qed.

Lemma EC_follow_dead_store_at_end_false: forall pinfo sasinfo F B tmn lc2 als2,
   ~
   EC_follow_dead_store pinfo sasinfo
     {|
     Opsem.CurFunction := F;
     Opsem.CurBB := B;
     Opsem.CurCmds := nil;
     Opsem.Terminator := tmn;
     Opsem.Locals := lc2;
     Opsem.Allocas := als2 |}.
Proof.
  intros. intro J.
  destruct J as [J1 [J2 J3]]. simpl in *.
  eapply cs_follow_dead_store_at_end_false in J3; eauto.  
Qed.

Ltac destruct_ctx_other :=
match goal with
| Hwfpp : OpsemPP.wf_State
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |} _,
  Hnoalias : Promotability.wf_State _ _ _ _,
  Hsim : State_simulation _ _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfpp as 
    [Hwfg [HwfSystem [HmInS [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [ _ HwfCall'
     ]]
    ]]]]; subst;
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  simpl in Hsim;
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 Hmsim]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim Hstksim];
  unfold EC_simulation in Hecsim;
  destruct Hecsim as 
      [Hfsim2 [Heq1 [Heq2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct Hnoalias as 
    [
      [[Hinscope' _] [HwfECs' HwfHT]] 
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals;
  fold Promotability.wf_ECStack in HwfECs'
end.

Lemma fdef_sim__block_sim : forall pinfo sasinfo f1 f2 b1 b2 l0,
  fdef_simulation pinfo sasinfo f1 f2 ->
  lookupBlockViaLabelFromFdef f1 l0 = Some b1 ->
  lookupBlockViaLabelFromFdef f2 l0 = Some b2 ->
  block_simulation pinfo sasinfo f1 b1 b2.
Admitted.

Lemma remove_phinodes_eq: forall pinfo sasinfo l0 ps0 cs0 tmn0,
  WF_PhiInfo pinfo -> uniqFdef (PI_f pinfo) ->
  blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) ->
  remove_phinodes (SAS_sid1 pinfo sasinfo) ps0 = ps0.
Admitted.

Lemma block_simulation_inv : forall pinfo sasinfo F l1 ps1 cs1 tmn1 l2 ps2 cs2
  tmn2,
  WF_PhiInfo pinfo -> uniqFdef F ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F ->
  block_simulation pinfo sasinfo F (block_intro l1 ps1 cs1 tmn1)
    (block_intro l2 ps2 cs2 tmn2) ->
  l1 = l2 /\ ps1 = ps2 /\ 
  cmds_simulation pinfo sasinfo F cs1 cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold block_simulation, cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); inv H2; auto.
  erewrite remove_phinodes_eq; eauto.
Qed.

Lemma switchToNewBasicBlock_sim : forall TD l1 l2 ps cs1 cs2 tmn1 tmn2 B1 B2 
  gl lc lc1 lc2 F pinfo sasinfo 
  (H23 : @Opsem.switchToNewBasicBlock DGVs TD
          (block_intro l1 ps cs1 tmn1) B1 gl lc = 
         ret lc1)
  (Hbsim2 : block_simulation pinfo sasinfo F B1 B2)
  (H2 : Opsem.switchToNewBasicBlock TD
         (block_intro l2 ps cs2 tmn2) B2 gl lc = 
        ret lc2), lc1 = lc2.
Admitted.

Lemma switchToNewBasicBlock_Mem_simulation: forall (pinfo : PhiInfo) 
  (sasinfo : SASInfo pinfo) (gl2 : GVMap) (lc2 : Opsem.GVsMap) 
  (als2 : list mblock) (M2 : mem) (los : layouts) (nts : namedts) (F : fdef)
  (B : block) tmn 
  (EC : list Opsem.ExecutionContext) (Mem : mem) (cs' : cmds)
  (Hmsim : Mem_simulation pinfo sasinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := B;
             Opsem.CurCmds := nil;
             Opsem.Terminator := tmn;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: EC) Mem M2)
  (l'0 : l) (ps'0 : phinodes) (tmn'0 : terminator) (lc'0 : Opsem.GVsMap)
  (H2 : Opsem.switchToNewBasicBlock (los, nts)
         (block_intro l'0 ps'0 cs' tmn'0) B gl2 lc2 = 
        ret lc'0),
  Mem_simulation pinfo sasinfo (los, nts)
     ({|
      Opsem.CurFunction := F;
      Opsem.CurBB := block_intro l'0 ps'0 cs' tmn'0;
      Opsem.CurCmds := cs';
      Opsem.Terminator := tmn'0;
      Opsem.Locals := lc'0;
      Opsem.Allocas := als2 |} :: EC) Mem M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 Hmsim2].
  split; auto.
    intros.
    eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); eauto.
    unfold undead_head_tail in *.
    intros.
    simpl in Hin.
    destruct Hin as [Hin | Hin]; subst.
      unfold undead_head_in_tail in *. simpl in *. intros. 
      right. apply EC_follow_dead_store_at_end_false.
 
      apply Hnalias; simpl; auto.
Qed.
    
Lemma sas_is_sim : forall maxb pinfo (sasinfo: SASInfo pinfo) Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hsim: State_simulation pinfo sasinfo Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State pinfo sasinfo St1) St1' tr1 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     State_simulation pinfo sasinfo Cfg1 St1' Cfg2 St2 /\ tr1 = trace_nil) /\
  (forall (Hnrem: ~removable_State pinfo sasinfo St1) St1' St2' tr1 tr2
     (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2) 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     State_simulation pinfo sasinfo Cfg1 St1' Cfg2 St2' /\ tr1 = tr2).
Proof.

Local Opaque inscope_of_tmn inscope_of_cmd.

  intros.
  split; intros.
Case "removable state".
  
  destruct Cfg1 as [S1 [los nts] Ps1 gl1 fs1].
  destruct St1 as [ECs1 M1].
  destruct ECs1 as [|[F1 B1 [|[] cs1] tmn1 lc1 als1] ECs1]; tinv Hrem.
  simpl in Hrem.
  destruct (fdef_dec (PI_f pinfo) F1); subst; tinv Hrem.
  destruct (id_dec i0 (SAS_sid1 pinfo sasinfo)); subst; tinv Hrem.
  
  destruct Hwfpp as 
    [Hwfg [HwfSystem [HmInS [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [HwfECs Hwfcall]]
    ]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs.

  destruct Hnoalias as 
    [
      [[Hinscope' _] [HwfECs' HwfHT]] 
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals.
  fold Promotability.wf_ECStack in HwfECs'.

  inv Hop1.

  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2].
  destruct St2 as [ECs2 M2].

  simpl in Hsim.
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 Hmsim]]]]]; subst.
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim.
  destruct Hstksim as [Hecsim Hstksim].
  unfold EC_simulation in Hecsim.
  destruct Hecsim as 
      [Hfsim2 [Heq1 [Heq2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst.

  uniq_result.
  repeat_solve.
    eapply cmds_simulation_elim_cons_inv; eauto.
    eapply mstore_removable_Mem_simulation in Hmsim; 
      eauto using wf_system__uniqFdef.

Case "unremovable state".
  (sInsn_cases (destruct Hop1) SCase).

SCase "sReturn".
Focus.
  destruct_ctx_return.
  repeat_solve.

    clear - H26 Hmsim H0 H1 Hinscope1' HBinF2 Heq3'.
    destruct Hmsim as [Hmsim1 Hmsim2].
    split.
      apply MemProps.nextblock_free_allocas in H0.
      apply MemProps.nextblock_free_allocas in H26.
      rewrite <- H0. rewrite <- H26. auto.

      intros.
      eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al);
        eauto using MemProps.free_allocas_preserves_mload_inv.
      unfold undead_head_tail. simpl.
      intros.
      destruct Hin as [Hin | [Hin | Hin]]; subst.
        apply undead_head_in_tail_nil.

        unfold undead_head_in_tail. simpl.
        assert (In {| Opsem.CurFunction := F';
                      Opsem.CurBB := B';
                      Opsem.CurCmds := cs';
                      Opsem.Terminator := tmn3;
                      Opsem.Locals := lc''0;
                      Opsem.Allocas := als3 |}
                   ({| Opsem.CurFunction := F';
                       Opsem.CurBB := B';
                       Opsem.CurCmds := cs';
                       Opsem.Terminator := tmn3;
                       Opsem.Locals := lc''0;
                       Opsem.Allocas := als3 |} :: EC)) as Hin.
          simpl. auto.
        apply Hnalias in Hin.
        unfold undead_head_in_tail in Hin. simpl in Hin.
        intros. subst.
        assert (lookupAL (GVsT DGVs) lc''0 (PI_id pinfo) = ret gvsa) as Hlkup'.
          admit. (* rid <> pid *)
        apply Hin in Hlkup'; auto.
        destruct Hlkup' as [Hlkup' | Hlkup']; auto.
        right.
        eapply EC_follow_dead_store_tail; eauto.
          admit. (* uniqness *)

        apply Hnalias; simpl; auto.     
Unfocus.
      
SCase "sReturnVoid".
Focus.
  destruct_ctx_return.
  repeat_solve.

    clear - H24 Hmsim H0 Hinscope1'.
    destruct Hmsim as [Hmsim1 Hmsim2].
    split.
      apply MemProps.nextblock_free_allocas in H0.
      apply MemProps.nextblock_free_allocas in H24.
      rewrite <- H0. rewrite <- H24. auto.

      intros.
      eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al);
        eauto using MemProps.free_allocas_preserves_mload_inv.
      unfold undead_head_tail. simpl.
      intros.
      destruct Hin as [Hin | [Hin | Hin]]; subst.
        apply undead_head_in_tail_nil.

        unfold undead_head_in_tail. simpl.
        assert (In {| Opsem.CurFunction := F';
                      Opsem.CurBB := B';
                      Opsem.CurCmds := cs';
                      Opsem.Terminator := tmn3;
                      Opsem.Locals := lc3;
                      Opsem.Allocas := als3 |}
                   ({| Opsem.CurFunction := F';
                       Opsem.CurBB := B';
                       Opsem.CurCmds := cs';
                       Opsem.Terminator := tmn3;
                       Opsem.Locals := lc3;
                       Opsem.Allocas := als3 |} :: EC)) as Hin.
          simpl. auto.
        apply Hnalias in Hin.
        unfold undead_head_in_tail in Hin. simpl in Hin.
        intros. subst.
        apply Hin in Hlkup; auto.
        destruct Hlkup as [Hlkup | Hlkup]; auto.
        right.
        eapply EC_follow_dead_store_tail; eauto.
          admit. (* uniqness *)

        apply Hnalias; simpl; auto.     
Unfocus.

SCase "sBranch".
Focus.

  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo sasinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    clear - H22 H1 Hfsim2.
    destruct (isGVZero (los, nts) c); eauto using fdef_sim__block_sim.  
  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  assert (blockInFdefB (block_intro l' ps' cs' tmn') F) as HBinF1'.
    admit.
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'; auto.
  destruct Hbsim' as [Heq1 [Heq2 [Hcssim' Heq5]]]; subst.

  assert (lc' = lc'0) as Heq.
    clear - H2 H23 Hbsim2.
    eapply switchToNewBasicBlock_sim in Hbsim2; eauto.
  subst.

  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.
  
    clear - H2 Hmsim.
    eapply switchToNewBasicBlock_Mem_simulation; eauto.

Unfocus.

SCase "sBranch_uncond".
Focus.
  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo sasinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    eauto using fdef_sim__block_sim.         
  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  assert (blockInFdefB (block_intro l' ps' cs' tmn') F) as HBinF1'.
    admit.  
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'; auto.
  destruct Hbsim' as [Heq1 [Heq2 [Hcssim' Heq5]]]; subst.

  assert (lc' = lc'0) as Heq.
    clear - H0 H17 Hbsim2.
    eapply switchToNewBasicBlock_sim in Hbsim2; eauto.
  subst.

  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.
  
    clear - H0 Hmsim.
    eapply switchToNewBasicBlock_Mem_simulation; eauto.

Unfocus.

Admitted.
(*

SCase "sBop". 
(*
Lemma mem_simulation_update_locals : 
  forall pinfo sasinfo TD EC1 EC2 ECs M1 M2
  (EQ: Opsem.CurFunction EC1 = Opsem.CurFunction EC2)
  (Hp: forall gvsa
   (Hlkup: lookupAL (GVsT DGVs) (Opsem.Locals EC1) (PI_id pinfo) = ret gvsa),
   lookupAL (GVsT DGVs) (Opsem.Locals EC2) (PI_id pinfo) = ret gvsa)
  (Hmsim: Mem_simulation pinfo sasinfo TD (EC1 :: ECs) M1 M2),
  Mem_simulation pinfo sasinfo TD (EC2 :: ECs) M1 M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 Hmsim2].
  split; auto.
    intros.
    eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); eauto.
Admitted.    
*)
abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExtractValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sInsertValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sMalloc". 
 
  destruct_ctx_other.
 
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  assert (mb0 = mb) as EQ.
    destruct Hmsim as [Hmsim _].
    apply MemProps.malloc_result in H25.
    apply MemProps.malloc_result in H2. subst. auto.
  subst.
  repeat_solve.

    destruct Hmsim as [Hmsim1 Hmsim2].
    split; auto.
      apply MemProps.nextblock_malloc in H2.
      apply MemProps.nextblock_malloc in H25.
      rewrite <- H2. rewrite <- H25. rewrite Hmsim1. auto.

      intros.
      eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); eauto.
      eapply no_alias_head_tail_update in Hnalias; eauto; simpl; auto.
        intros. admit. (* id <> palloca *)

        (* two cases, if ptr is mb or not, 
           malloc_preserves_mload_inv needs to be extended. *)
        admit. admit.

SCase "sFree". 

  destruct_ctx_other.
 
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    destruct Hmsim as [Hmsim1 Hmsim2].
    split; auto.
      apply MemProps.nextblock_free in H1.
      apply MemProps.nextblock_free in H22.
      rewrite <- H1. rewrite <- H22. rewrite Hmsim1. auto.

      intros.
      eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); 
        eauto using MemProps.free_preserves_mload_inv.
      eapply no_alias_head_tail_irrel in Hnalias; eauto; simpl; auto.

SCase "sAlloca". 

  destruct_ctx_other.
 
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  assert (mb0 = mb) as EQ.
    destruct Hmsim as [Hmsim _].
    apply MemProps.malloc_result in H25.
    apply MemProps.malloc_result in H2. subst. auto.
  subst.
  repeat_solve.

    destruct Hmsim as [Hmsim1 Hmsim2].
    split; auto.
      apply MemProps.nextblock_malloc in H2.
      apply MemProps.nextblock_malloc in H25.
      rewrite <- H2. rewrite <- H25. rewrite Hmsim1. auto.

      intros.
      eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); eauto.
      eapply no_alias_head_tail_update in Hnalias; eauto; simpl; auto.
        intros.
        admit. (* if id = palloca, then lc2 cannot contain pid *)

        (* two cases, if ptr is mb or not, 
           malloc_preserves_mload_inv needs to be extended. *)
        admit. admit. 

SCase "sLoad". 
  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  assert (gv = gv0) as EQ.
    admit. (* no load from pid *)
  subst.
  repeat_solve.

    eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
      simpl. intros.
      admit. (* lid <> pid *)

SCase "sStore". 

  destruct_ctx_other.
 
  assert (PI_f pinfo = F -> 
          store_in_cmd (PI_id pinfo) (insn_store sid t v1 v2 align0) = false)
         as J.
    clear - Hnrem. simpl in Hnrem.
    destruct v2; auto.
    intros. subst.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    simpl.
    destruct (id_dec i0 (PI_id pinfo)); subst; auto.
    destruct (id_dec (PI_id pinfo) (PI_id pinfo)); try congruence.
    contradict Hnrem; auto.
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    destruct Hmsim as [Hmsim1 Hmsim2].
    split; auto.
      apply MemProps.nextblock_mstore in H3.
      apply MemProps.nextblock_mstore in H28.
      rewrite <- H3. rewrite <- H28. rewrite Hmsim1. auto.

      intros.
      eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); eauto.
      eapply no_alias_head_tail_irrel in Hnalias; eauto; simpl; auto.
        (* two cases, if ptr overlaps with stored ptr or not *)
        admit. admit.

SCase "sGEP". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sTrunc". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExt". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sCast". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sIcmp". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFcmp". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sSelect". 
  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    destruct (isGVZero (los,nts) c).
      eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
        simpl. intros.
        admit. (* lid <> pid *)
      eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
        simpl. intros.
        admit. (* lid <> pid *)

SCase "sCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.

  inv Hop2.

  SSCase "SCall".

  uniq_result.
  assert (Hfsim1:=Hpsim).
  eapply lookupFdefViaPtr__simulation in Hfsim1; eauto.

  assert (Hbsim1:=Hfsim1).
  eapply fdef_simulation__entry_block_simulation in Hbsim1; eauto.
  assert (Hbsim1':=Hbsim1).
  apply block_simulation_inv in Hbsim1'.
  destruct Hbsim1' as [Heq' [Hpsim1' [Hcsim1' Htsim1']]]; subst.
  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    apply fdef_simulation_inv in Hfsim1.
    destruct Hfsim1 as [Heq _]. inv Heq. uniq_result.
    auto.

    destruct Hmsim as [Hmsim1 Hmsim2].
    split; auto.
      intros.
      eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); eauto.
      clear Hmsim2.
      apply no_alias_head_tail_cons_and in Hnalias.
      destruct Hnalias as [Hnalias1 Hnalias2]; auto.

  SSCase "sExCall".

  uniq_result.

  clear - H28 H1 Hpsim.
  eapply lookupFdefViaPtr__simulation_l2r in H1; eauto.
  destruct H1 as [f2 [H1 H2]].
  apply OpsemAux.lookupExFdecViaPtr_inversion in H28.
  apply OpsemAux.lookupFdefViaPtr_inversion in H1.
  destruct H28 as [fn [J1 [J2 J3]]].
  destruct H1 as [fn' [J4 J5]].
  uniq_result.   

SCase "sExCall". 

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.

  inv Hop2.

  SSCase "SCall".

  uniq_result.

  clear - H29 H1 Hpsim.
  eapply lookupExFdecViaPtr__simulation_l2r in H1; eauto.
  apply OpsemAux.lookupExFdecViaPtr_inversion in H1.
  apply OpsemAux.lookupFdefViaPtr_inversion in H29.
  destruct H1 as [fn [J1 [J2 J3]]].
  destruct H29 as [fn' [J4 J5]].
  uniq_result.   

  SSCase "sExCall".

  uniq_result.

  assert (Hlkdec:=Hpsim).
  eapply lookupExFdecViaPtr__simulation_l2r in Hlkdec; eauto.
  uniq_result.
  eapply callExternalFunction__Mem_simulation in Hmsim; eauto.
  destruct Hmsim as [EQ Hmsim]; subst.
  uniq_result.
  repeat_solve.
    eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
      simpl. intros. admit. (* cid <> pid *)
    
Transparent inscope_of_tmn inscope_of_cmd.

Qed.
*)

Lemma s_genInitState__sas_State_simulation: forall pinfo sasinfo S1 S2 main 
  VarArgs cfg2 IS2,
  system_simulation pinfo sasinfo S1 S2 ->
  Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2) ->
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo sasinfo cfg1 IS1 cfg2 IS2.
Admitted.

Lemma s_isFinialState__sas_State_simulation: forall pinfo sasinfo cfg1 FS1 cfg2 
  FS2 r (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: s_isFinialState cfg2 FS2 = ret r),
  s_isFinialState cfg1 FS1 = ret r.
Admitted.

Lemma opsem_s_isFinialState__sas_State_simulation: forall 
  pinfo sasinfo cfg1 FS1 cfg2 FS2  
  (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2),
  Opsem.s_isFinialState FS1 = Opsem.s_isFinialState FS2.
Admitted.

Lemma undefined_state__sas_State_simulation: forall pinfo sasinfo cfg1 St1 cfg2 
  St2 (Hstsim : State_simulation pinfo sasinfo cfg1 St1 cfg2 St2),
  OpsemPP.undefined_state cfg1 St1 -> OpsemPP.undefined_state cfg2 St2.
Admitted.

Lemma sop_star__sas_State_simulation: forall pinfo sasinfo cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hstsim : State_simulation pinfo sasinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\ 
    State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent cfg1.
  generalize dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    assert (J:=Hwfpp).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]].
      apply opsem_s_isFinialState__sas_State_simulation in Hstsim.
      rewrite Hstsim in Hfinal1.
      contradict H; eauto using s_isFinialState__stuck.

      assert (OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
        apply OpsemPP.preservation in Hop1; auto.
      assert (Promotability.wf_State maxb pinfo cfg1 IS1') as Hnoalias'.
        eapply Promotability.preservation in Hop1; eauto.
      eapply sas_is_sim in Hstsim; eauto.
      destruct Hstsim as [Hstsim1 Hstsim2].
      destruct (@removable_State_dec pinfo sasinfo IS1) as [Hrm | Hnrm].
        eapply Hstsim1 in Hrm; eauto.
        destruct Hrm as [Hstsim EQ]; subst.
        admit. (* we should do induction on the measure of State_simulation *)

        eapply Hstsim2 in Hnrm; eauto.
        destruct Hnrm as [Hstsim EQ]; subst.
        eapply IHHopstar in Hstsim; eauto.
        destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
        exists FS1.
        split; eauto.

      eapply undefined_state__sas_State_simulation in Hstsim; eauto.
      contradict H; eauto using undefined_state__stuck.
Qed.

Lemma sop_div__sas_State_simulation: forall pinfo laainfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hstsim : State_simulation pinfo laainfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Admitted.

Lemma find_st_ld__sasinfo: forall l0 ps0 cs0 tmn0 i0 v cs (pinfo:PhiInfo) dones
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones) v0
  (i1 : id) (Hld : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (HBinF : blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true),
  exists sasinfo:SASInfo pinfo,
    SAS_sid1 pinfo sasinfo = i0 /\
    SAS_sid2 pinfo sasinfo = i1 /\
    SAS_value1 pinfo sasinfo = v /\
    SAS_value2 pinfo sasinfo = v0 /\
    SAS_block pinfo sasinfo = (block_intro l0 ps0 cs0 tmn0).
Admitted.

Lemma sas_sim: forall (los : layouts) (nts : namedts) (fh : fheader) 
  (dones : list id) (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) 
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
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
         (fdef_intro fh
           (List.map (remove_block i0)
             (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) :: Ps2)]
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
  eapply find_st_ld__sasinfo in HBinF; eauto.
  destruct HBinF as [sasinfo [J1 [J2 [J3 [J4 J5]]]]]; subst.
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation pinfo sasinfo
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (remove_fdef (SAS_sid1 pinfo sasinfo)
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
    eapply s_genInitState__sas_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]].    
    assert (OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    assert (exists maxb, 
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom.
      eapply Promotability.s_genInitState__wf_globals_promotable; eauto.
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]].
    eapply sop_star__sas_State_simulation in Hstsim; eauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    eapply s_isFinialState__sas_State_simulation in Hstsim'; eauto.
    econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    eapply s_genInitState__sas_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]].  
    assert (OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    assert (exists maxb, 
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom.
      eapply Promotability.s_genInitState__wf_globals_promotable; eauto.
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]].
    eapply sop_div__sas_State_simulation in Hstsim; eauto.
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.
Qed.

Lemma sas_wfS: forall (los : layouts) (nts : namedts) (fh : fheader) 
  (dones : list id) (pinfo : PhiInfo) 
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) 
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo) 
  (HwfS : 
     wf_system nil
       [module_intro los nts 
         (Ps1 ++ 
          product_fdef 
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
  wf_system nil
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
           (List.map (remove_block i0)
             (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) :: Ps2)].
Admitted.

Lemma sas_wfPI: forall (los : layouts) (nts : namedts) (fh : fheader) 
  (dones : list id) (pinfo : PhiInfo) 
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) 
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo) 
  (HwfS : 
     wf_system nil
       [module_intro los nts 
         (Ps1 ++ 
          product_fdef 
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
  WF_PhiInfo 
    (update_pinfo pinfo
      (fdef_intro fh
        (List.map (remove_block i0)
           (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))).
Admitted.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
