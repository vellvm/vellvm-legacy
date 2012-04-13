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
Require Import mem2reg.
Require Import memory_props.
Require Import sas_msim.
Require Import trans_tactic.
Require Import top_sim.

Definition fdef_simulation (pinfo: PhiInfo) f1 f2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then
    elim_dead_st_fdef (PI_id pinfo) f1 = f2
  else f1 = f2.

Definition cmds_simulation (pinfo: PhiInfo) (f1:fdef) cs1 cs2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then
    elim_dead_st_cmds cs1 (PI_id pinfo) = cs2
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) (f1:fdef) b1 b2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then
    elim_dead_st_block (PI_id pinfo) b1 = b2
  else b1 = b2.

Lemma fdef_simulation__eq_fheader: forall pinfo f1 f2
  (H: fdef_simulation pinfo f1 f2),
  fheaderOfFdef f1 = fheaderOfFdef f2.
Proof.
  unfold fdef_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) f1); inv H; auto.
    destruct (PI_f pinfo) as [fh b]; simpl; auto.
Qed.

Lemma fdef_simulation__det_right: forall pinfo f f1 f2,
  fdef_simulation pinfo f f1 ->
  fdef_simulation pinfo f f2 ->
  f1 = f2.
Proof.
  unfold fdef_simulation.
  intros.
  destruct_if; congruence.
Qed.

Definition Fsim (pinfo: PhiInfo) := mkFunSim 
(fdef_simulation pinfo)
(fdef_simulation__eq_fheader pinfo)
(fdef_simulation__det_right pinfo)
.

Definition products_simulation (pinfo: PhiInfo) Ps1 Ps2 : Prop :=
@TopSim.products_simulation (Fsim pinfo) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) S1 S2 : Prop :=
@TopSim.system_simulation (Fsim pinfo) S1 S2.

Definition EC_simulation (pinfo: PhiInfo) (EC1 EC2:@Opsem.ExecutionContext DGVs)
  : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1,
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation pinfo f1 f2 /\
       tmn1 = tmn2 /\
       als1 = als2 /\
       block_simulation pinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11,
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       lc1 = lc2 /\
       cmds_simulation pinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (pinfo: PhiInfo) (ECs1 ECs2:@Opsem.ECStack DGVs)
  : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' =>
    EC_simulation pinfo EC1 EC2 /\ ECs_simulation pinfo ECs1' ECs2'
| _, _ => False
end.

Definition no_alias_head_in_tail (pinfo:PhiInfo) omb
  (ec0:@Opsem.ExecutionContext DGVs) : Prop :=
(Opsem.CurFunction ec0 = PI_f pinfo ->
match lookupAL _ (Opsem.Locals ec0) (PI_id pinfo) with
| Some ((Vptr mb _, _)::nil) => omb = Some mb
| _ => omb = None
end) /\
(Opsem.CurFunction ec0 <> PI_f pinfo -> omb = None).

Definition no_alias_head_tail (pinfo:PhiInfo) ombs
  (ecs':list Opsem.ExecutionContext) : Prop :=
List.Forall2 (fun ec omb => 
              no_alias_head_in_tail pinfo omb ec) ecs' ombs.

Definition dse_mem_inj (pinfo:PhiInfo) (ecs1:list Opsem.ExecutionContext) 
  TD (m1 m2: mem) : Prop :=
match getTypeStoreSize TD (PI_typ pinfo) with
| Some tsz => 
    forall ombs,
      no_alias_head_tail pinfo ombs ecs1 ->
      SASmsim.mem_inj inject_id (ombs__ignores (Size.to_Z tsz) ombs) m1 m2
| None => False
end.

Definition mem_simulation (pinfo:PhiInfo) TD
  (ecs1:list Opsem.ExecutionContext) Mem1 Mem2 : Prop :=
Mem.nextblock Mem1 = Mem.nextblock Mem2 /\
(forall b, Mem.bounds Mem1 b = Mem.bounds Mem2 b) /\
dse_mem_inj pinfo ecs1 TD Mem1 Mem2.

Definition State_simulation (pinfo: PhiInfo)
  (Cfg1:OpsemAux.Config) (St1:Opsem.State)
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\
    products_simulation pinfo Ps1 Ps2 /\
    ECs_simulation pinfo ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ mem_simulation pinfo TD1 ECs1 M1 M2
end.

Definition removable_State (pinfo: PhiInfo) (St:@Opsem.State DGVs) : Prop :=
match St with
| Opsem.mkState
    (Opsem.mkEC f b
      (insn_store sid _ _ (value_id qid) _ :: cs)
      tmn lc als::_) _ =>
    if (fdef_dec (PI_f pinfo) f) then
      if (id_dec (PI_id pinfo) qid) then True else False
    else False
| _ => False
end.

Lemma removable_State_dec : forall pinfo St,
  removable_State pinfo St \/ ~ removable_State pinfo St.
Proof.
  destruct St.
  destruct ECS as [|[]]; auto.
  destruct CurCmds; auto.
  destruct_cmd c; auto.
  destruct v0 as [i1|]; auto.
  simpl.
  destruct (fdef_dec (PI_f pinfo) CurFunction); auto.
  destruct (id_dec (PI_id pinfo) i1); auto.
Qed.

Lemma cmds_simulation_elim_cons_inv: forall (pinfo : PhiInfo) (i0 : id) (t : typ)
  (v : value) (a : align) (cs1 : list cmd) (cs2 : cmds)
  (Hcssim2 : cmds_simulation pinfo (PI_f pinfo)
              (insn_store i0 t v (value_id (PI_id pinfo)) a :: cs1) cs2),
  cmds_simulation pinfo (PI_f pinfo) cs1 cs2.
Proof.
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  simpl in *.
  destruct (id_dec (PI_id pinfo) (PI_id pinfo)); congruence.
Qed.

Lemma no_alias_head_tail_irrel :
  forall pinfo omb F B1 cs1 tmn1 lc als1 ECs B2 cs2 tmn2 als2,
  no_alias_head_tail pinfo omb
              ({|
               Opsem.CurFunction := F;
               Opsem.CurBB := B1;
               Opsem.CurCmds := cs1;
               Opsem.Terminator := tmn1;
               Opsem.Locals := lc;
               Opsem.Allocas := als1 |} :: ECs) ->
  no_alias_head_tail pinfo omb
              ({|
               Opsem.CurFunction := F;
               Opsem.CurBB := B2;
               Opsem.CurCmds := cs2;
               Opsem.Terminator := tmn2;
               Opsem.Locals := lc;
               Opsem.Allocas := als2 |} :: ECs).
Proof.
  unfold no_alias_head_tail. simpl in *.
  intros. inv H. constructor; auto.
Qed.

Lemma cmds_simulation_nil_inv: forall pinfo f1 cs,
  cmds_simulation pinfo f1 nil cs -> cs = nil.
Proof.
  unfold cmds_simulation. simpl.
  intros. destruct (fdef_dec (PI_f pinfo) f1); auto.
Qed.

Lemma cmds_simulation_nelim_cons_inv: forall pinfo F c cs2 cs',
  cmds_simulation pinfo F (c :: cs2) cs' ->
  (PI_f pinfo = F -> store_in_cmd (PI_id pinfo) c = false) ->
  exists cs2',
    cs' = c :: cs2' /\ cmds_simulation pinfo F cs2 cs2'.
Proof.
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); subst; simpl; eauto.
  destruct_cmd c; simpl in H0; eauto.
  destruct v0 as [i1|]; simpl in H0; eauto.
  destruct (id_dec (PI_id pinfo) i1); subst; simpl; eauto.
  assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
  apply H0 in EQ.
  destruct (id_dec (PI_id pinfo) (PI_id pinfo)); simpl in *; congruence.
Qed.
(*
Lemma no_alias_head_tail_and_app: forall pinfo ptr ECs1 ECs2,
  no_alias_head_tail pinfo ptr ECs1 ->
  no_alias_head_tail pinfo ptr ECs2 ->
  no_alias_head_tail pinfo ptr (ECs1 ++ ECs2).
Proof.
  intros.
  unfold no_alias_head_tail in *.
  intros.
  apply in_app_or in Hin.
  destruct Hin as [Hin | Hin]; eauto.
Qed.

Lemma no_alias_head_tail_and_cons: forall pinfo ptr EC ECs,
  no_alias_head_in_tail pinfo ptr EC ->
  no_alias_head_tail pinfo ptr ECs ->
  no_alias_head_tail pinfo ptr (EC :: ECs).
Proof.
  intros.
  simpl_env.
  apply no_alias_head_tail_and_app; auto.
  unfold no_alias_head_tail.
  intros.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; subst; auto.
    inv Hin.
Qed.

Lemma no_alias_head_in_tail__return: forall pinfo F maxb TD M lc als M' EC ptr
  ty al gvs
  (Hinscope1':
   if fdef_dec (PI_f pinfo) F
   then Promotability.wf_defs maxb pinfo TD M lc als
   else True)
  (H0:free_allocas TD M als = Some M')
  (Hld1:mload TD M' ptr ty al = Some gvs)
  (EQ1:Opsem.CurFunction EC = F) (EQ2:Opsem.Locals EC = lc),
  no_alias_head_in_tail pinfo ptr EC.
Proof.
  intros.
  unfold no_alias_head_in_tail. intros.
  rewrite Heq in EQ1. subst.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  destruct (MemProps.no_alias_dec ptr gvsa) as [Hnalias' | Halias]; auto.
  apply Hinscope1' in Hlkup.
  destruct Hlkup as [[_ [[mb [EQ [Hin _]]] _]] _]; subst.
  assert (Hld1':=Hld1).
  apply mload_inv in Hld1.
  destruct Hld1 as [b [ofs [m [mc [EQ [J1 Hld1]]]]]]; subst.
  rewrite Promotability.simpl_blk2GV in Halias.
  simpl in Halias.
  destruct (Z_eq_dec b mb); subst; try (contradict Halias; auto).
  erewrite load_free_allocas_none in Hld1'; eauto.
  congruence.
Qed.
*)
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
             |} _,  Hnoalias : Promotability.wf_State _ _ _ _,
  Hsim : State_simulation _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]]; subst;
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
  apply cmds_simulation_nelim_cons_inv in Hcssim2'; auto;
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result
end.

Lemma fdef_sim__lookupAL_genLabel2Block_elim_dead_st_block : 
  forall id0 l0 bs b b',
  lookupAL _ (genLabel2Block_blocks bs) l0 = Some b ->
  lookupAL _ (genLabel2Block_blocks (List.map (elim_dead_st_block id0) bs)) l0
    = Some b' ->
  elim_dead_st_block id0 b = b'.
Proof.
  intros.
  eapply fdef_sim__lookupAL_genLabel2Block_block; eauto.
  destruct b0; simpl; auto.
Qed.

(* generalized? *)
Lemma fdef_sim__block_sim : forall pinfo f1 f2 b1 b2 l0,
  fdef_simulation pinfo f1 f2 ->
  lookupBlockViaLabelFromFdef f1 l0 = Some b1 ->
  lookupBlockViaLabelFromFdef f2 l0 = Some b2 ->
  block_simulation pinfo f1 b1 b2.
Proof.
  intros.
  unfold fdef_simulation in H.
  unfold block_simulation.
  destruct (fdef_dec (PI_f pinfo) f1); subst.
    destruct (PI_f pinfo). simpl in *.
    eapply fdef_sim__lookupAL_genLabel2Block_elim_dead_st_block; eauto.

    uniq_result. auto.
Qed.

Lemma block_simulation_inv : forall pinfo F l1 ps1 cs1 tmn1 l2 ps2 cs2
  tmn2,
  block_simulation pinfo F (block_intro l1 ps1 cs1 tmn1)
    (block_intro l2 ps2 cs2 tmn2) ->
  l1 = l2 /\ ps1 = ps2 /\
  cmds_simulation pinfo F cs1 cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold block_simulation, cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); inv H; auto.
Qed.

Lemma no_alias_head_in_tail_update :
  forall pinfo ombs EC1 EC2 
  (EQ: Opsem.CurFunction EC1 = Opsem.CurFunction EC2)
  (Hp: forall (EQ': Opsem.CurFunction EC1 = PI_f pinfo),
   lookupAL (GVsT DGVs) (Opsem.Locals EC2) (PI_id pinfo) =
     lookupAL (GVsT DGVs) (Opsem.Locals EC1) (PI_id pinfo))
  (Hnalias: no_alias_head_in_tail pinfo ombs EC1),
  no_alias_head_in_tail pinfo ombs EC2.
Proof.
  intros.
  unfold no_alias_head_in_tail in *.
  intros. 
  destruct Hnalias as [Hnalias1 Hnalias2].
  split; intros.
    rewrite Hp; try congruence.
    apply Hnalias1; try solve [auto | congruence].

    apply Hnalias2; try solve [auto | congruence].
Qed.

Lemma no_alias_head_tail_update :
  forall pinfo ombs EC1 EC2 ECs
  (EQ: Opsem.CurFunction EC1 = Opsem.CurFunction EC2)
  (Hp: forall (EQ': Opsem.CurFunction EC1 = PI_f pinfo),
   lookupAL (GVsT DGVs) (Opsem.Locals EC2) (PI_id pinfo) =
     lookupAL (GVsT DGVs) (Opsem.Locals EC1) (PI_id pinfo))
  (Hnalias: no_alias_head_tail pinfo ombs (EC1 :: ECs)),
  no_alias_head_tail pinfo ombs (EC2 :: ECs).
Proof.
  intros.
  unfold no_alias_head_tail in *.
  inv Hnalias.
  constructor; auto.
    eapply no_alias_head_in_tail_update; eauto.
Qed.

Lemma switchToNewBasicBlock_sim : forall TD l1 l2 ps cs1 cs2 tmn1 tmn2 B1 B2
  gl lc lc1 lc2 F pinfo
  (H23 : @Opsem.switchToNewBasicBlock DGVs TD
          (block_intro l1 ps cs1 tmn1) B1 gl lc =
         ret lc1)
  (Hbsim2 : block_simulation pinfo F B1 B2)
  (H2 : Opsem.switchToNewBasicBlock TD
         (block_intro l2 ps cs2 tmn2) B2 gl lc =
        ret lc2), lc1 = lc2.
Proof.
  intros.
  destruct B1, B2.
  apply block_simulation_inv in Hbsim2; auto.
  destruct Hbsim2 as [J1 [J2 [J3 J4]]]; subst.
  unfold Opsem.switchToNewBasicBlock in *. simpl in *.
  rewrite (@OpsemProps.getIncomingValuesForBlockFromPHINodes_eq 
    DGVs ps TD l0 phinodes0 cmds0 terminator0
                  phinodes0 cmds5 terminator0) in H2; auto.
  rewrite H2 in H23. congruence.
Qed.

Lemma mem_simulation_update_locals :
  forall pinfo TD EC1 EC2 ECs M1 M2
  (EQ: Opsem.CurFunction EC1 = Opsem.CurFunction EC2)
  (Hp: forall (EQ': PI_f pinfo = Opsem.CurFunction EC1),
    lookupAL (GVsT DGVs) (Opsem.Locals EC1) (PI_id pinfo) =
      lookupAL (GVsT DGVs) (Opsem.Locals EC2) (PI_id pinfo))
  (Hmsim: mem_simulation pinfo TD (EC1 :: ECs) M1 M2),
  mem_simulation pinfo TD (EC2 :: ECs) M1 M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  split; auto.
  split; auto.
    unfold dse_mem_inj in *.
    inv_mbind. clear HeqR.
    intros ombs Hin.
    apply Hmsim2. clear Hmsim2.
    eapply no_alias_head_tail_update in Hin; eauto.
      intros. apply Hp. congruence.
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
  Hnoalias : Promotability.wf_State _ _ _ _,
  Hsim : State_simulation _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]]; subst;
  destruct Hwfpp as
    [_ [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 _]]]]
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
      [Hfsim2 [Heq1 [Heq2 [Hbsim2
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct Hnoalias as
    [
      [[Hinscope' _] [HwfECs' HwfHT]]
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals;
  fold Promotability.wf_ECStack in HwfECs'
end.

Lemma no_alias_head_in_tail_inv1: forall lc2 pinfo TD mb B1 cs1 tmn2 als2 y
  (Hlkup: lookupAL (GVsT DGVs) lc2 (PI_id pinfo) =
        ret ($ blk2GV TD mb # typ_pointer (PI_typ pinfo) $)) 
  (H1 : no_alias_head_in_tail pinfo y
         {|
         Opsem.CurFunction := PI_f pinfo;
         Opsem.CurBB := B1;
         Opsem.CurCmds := cs1;
         Opsem.Terminator := tmn2;
         Opsem.Locals := lc2;
         Opsem.Allocas := als2 |}),
  y = ret mb.
Proof.
  intros.
  destruct H1 as [H1 _]. simpl in H1.
  rewrite Hlkup in H1.
  rewrite Promotability.simpl_blk2GV in H1. tauto.
Qed.

Lemma mstore_palloca_mem_simulation: forall los nts M1 mp2 gv1 a M1' pinfo lc2 
  gl2 B1 cs1 tmn2 als2 ECs1 M2 i0 v maxb Ps S
  (H23: mstore (los, nts) M1 mp2 (PI_typ pinfo) gv1 a = ret M1')
  (H20: @Opsem.getOperandValue DGVs (los, nts) (value_id (PI_id pinfo)) lc2 gl2 =
          ret mp2)
  (Hinscope' : if fdef_dec (PI_f pinfo) (PI_f pinfo)
              then Promotability.wf_defs maxb pinfo (los, nts) M1 lc2 als2
              else True)
  (H19 : Opsem.getOperandValue (los,nts) v lc2 gl2 = ret gv1)
  (Hwfg : wf_global (los, nts) S gl2)
  (Hwflc1 : OpsemPP.wf_lc (los, nts) (PI_f pinfo) lc2)
  (Hwfv : wf_value S (module_intro los nts Ps) (PI_f pinfo) v (PI_typ pinfo))
  (Hmsim: mem_simulation pinfo (los, nts)
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := 
               insn_store i0 (PI_typ pinfo) v (value_id (PI_id pinfo)) a
               :: cs1;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: ECs1) M1 M2),
  mem_simulation pinfo (los, nts)
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := cs1;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: ECs1) M1' M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  split.
    apply MemProps.nextblock_mstore in H23.
    rewrite <- H23. auto.
  split.
    intro b'.    
    eapply MemProps.bounds_mstore in H23; eauto.
    rewrite <- H23. eauto.
    
    unfold dse_mem_inj in *. inv_mbind.
    intros ombs Hin.
    inv Hin.
    assert (no_alias_head_tail pinfo (y::l')
             ({|
              Opsem.CurFunction := PI_f pinfo;
              Opsem.CurBB := B1;
              Opsem.CurCmds := 
                insn_store i0 (PI_typ pinfo) v (value_id (PI_id pinfo)) a
                :: cs1;
              Opsem.Terminator := tmn2;
              Opsem.Locals := lc2;
              Opsem.Allocas := als2 |} :: ECs1)) as Hin.
      constructor; auto.     
    apply Hmsim2 in Hin. clear Hmsim2.
    simpl in Hin.
    subst. simpl in H20.
    assert (exists mb, mp2 = 
              ($ (blk2GV (los,nts) mb) # (typ_pointer (PI_typ pinfo)) $)) as EQ.
      destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
      apply Hinscope' in H20.
      destruct H20 as [[_ [[mb [H20 _]] _]] _]. eauto.
    destruct EQ as [mb EQ]; subst.
    assert (y = Some mb) as EQ.
      eapply no_alias_head_in_tail_inv1; eauto.
    subst.
    assert (n = sizeGenericValue gv1) as EQ.
      eapply wf__getTypeStoreSize_eq_sizeGenericValue; eauto.
    subst.
    simpl.
    eapply SASmsim.mstore_inside_inj_left'; eauto.
Qed.

Ltac repeat_solve :=
  repeat (match goal with
          | |- mem_simulation _ _ _ _ _ => idtac
          | |- _ => split; eauto 2 using cmds_at_block_tail_next
          end).

Lemma getEntryBlock__simulation: forall pinfo f1 f2 b2,
  getEntryBlock f2 = Some b2 ->
  fdef_simulation pinfo f1 f2 ->
  exists b1, getEntryBlock f1 = Some b1 /\ 
    block_simulation pinfo f1 b1 b2.
Proof.
  unfold fdef_simulation.
  unfold block_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) f1); inv H0; eauto.
    remember (PI_f pinfo) as R1.
    destruct R1 as [[? ? ? a ?] b]; simpl in *.
    destruct b; simpl in *; inv H.
    exists b. 
    split; auto.
Qed.

Lemma fdef_simulation__entry_block_simulation: forall pinfo F1 F2 B1 B2,
  fdef_simulation pinfo F1 F2 ->
  getEntryBlock F1 = ret B1 ->
  getEntryBlock F2 = ret B2 ->
  block_simulation pinfo F1 B1 B2.
Proof.
  intros.
  eapply getEntryBlock__simulation in H1; eauto.
  destruct H1 as [b1 [J1 J2]].
  uniq_result. auto.
Qed.

(* generalized? *)
Lemma fdef_simulation_inv: forall pinfo fh1 fh2 bs1 bs2,
  fdef_simulation pinfo (fdef_intro fh1 bs1) (fdef_intro fh2 bs2) ->
  fh1 = fh2 /\
  List.Forall2
    (fun b1 b2 =>
      block_simulation pinfo (fdef_intro fh1 bs1) b1 b2) bs1 bs2.
Proof.
  intros.
  unfold fdef_simulation in H.
  destruct (fdef_dec (PI_f pinfo) (fdef_intro fh1 bs1)).
    simpl in H. inv H.
    split; auto.
      unfold block_simulation.
      rewrite e.
      destruct (fdef_dec (fdef_intro fh2 bs1) (fdef_intro fh2 bs1));
        try congruence.
        clear.
        induction bs1; simpl; constructor; auto.

    inv H.
    split; auto.
      unfold block_simulation.
      destruct (fdef_dec (PI_f pinfo) (fdef_intro fh2 bs2));
        try congruence.
        clear.
        induction bs2; simpl; constructor; auto.
Qed.

(*
Lemma no_alias_head_tail_cons_and: forall pinfo ptr EC ECs,
  no_alias_head_tail pinfo ptr (EC :: ECs) ->
  no_alias_head_in_tail pinfo ptr EC /\ no_alias_head_tail pinfo ptr ECs.
Proof.
  intros.
  unfold no_alias_head_tail in *.
  split.
    apply H; simpl; auto.
    intros. apply H; simpl; auto.
Qed.
*)
Axiom callExternalFunction__mem_simulation_l2r: forall pinfo TD St1 M1 M2 fid0 gvss0
  oresult1 M1' dck tr1 gl tret targs,
  mem_simulation pinfo TD St1 M1 M2 ->
  callExternalOrIntrinsics TD gl M1 fid0 tret targs dck gvss0 =
    ret (oresult1, tr1, M1') ->
  exists M2', exists oresult2, exists tr2, 
    callExternalOrIntrinsics TD gl M2 fid0 tret targs dck gvss0 =
      ret (oresult2, tr2, M2') /\
    oresult1 = oresult2 /\ mem_simulation pinfo TD St1 M1' M2' /\ tr1 = tr2.

Lemma callExternalFunction__mem_simulation: forall pinfo TD St1 M1 M2 fid0 gvss0
  oresult1 M1' oresult2 M2' dck tr1 tr2 gl tret targs,
  mem_simulation pinfo TD St1 M1 M2 ->
  callExternalOrIntrinsics TD gl M1 fid0 tret targs dck gvss0 =
    ret (oresult1, tr1, M1') ->
  callExternalOrIntrinsics TD gl M2 fid0 tret targs dck gvss0 =
    ret (oresult2, tr2, M2') ->
  oresult1 = oresult2 /\ mem_simulation pinfo TD St1 M1' M2' /\ tr1 = tr2.
Proof.
  intros.
  eapply callExternalFunction__mem_simulation_l2r in H; eauto.
  destruct H as [M2'' [oresult2' [tr2' [J1 [J2 [J3 J4]]]]]]; subst.
  uniq_result. auto.
Qed.

Ltac dse_is_sim_mem_update :=
match goal with
| Hmsim: mem_simulation _ _ _ _ _ |- _ =>
  repeat_solve;
  match goal with
  | |- mem_simulation _ _ 
         ({|Opsem.CurFunction := _;
            Opsem.CurBB := _;
            Opsem.CurCmds := _;
            Opsem.Terminator := _;
            Opsem.Locals:= ?lc';
            Opsem.Allocas:=?als'|}::_) _ _ =>
      eapply mem_simulation_update_locals in Hmsim; simpl; try solve [
          eauto |
          simpl; solve_non_pid_updateAddAL
        ]
  end
end.

Ltac dse_is_sim_common_case :=
match goal with
| Hcssim2: cmds_simulation _ _ _ _,
  Hop2: Opsem.sInsn _ _ _ _,
  Hmsim: mem_simulation _ _ _ _ _ |- _ =>
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  dse_is_sim_mem_update
end.

Lemma no_alias_head_tail__replace_head: forall EC' EC ECs1 ombs pinfo
  (Hp : forall omb,
        no_alias_head_in_tail pinfo omb EC' ->
        no_alias_head_in_tail pinfo omb EC)
  (H1: no_alias_head_tail pinfo ombs (EC' :: ECs1)),
  no_alias_head_tail pinfo ombs (EC :: ECs1).
Proof.
  intros. inv H1. constructor; auto.
Qed.

Lemma mem_simulation__replace_head: forall TD ECs1 pinfo EC EC'
  (Hp : forall omb : monad mblock,
        no_alias_head_in_tail pinfo omb EC' ->
        no_alias_head_in_tail pinfo omb EC) M1 M2
  (Hmsim : mem_simulation pinfo TD (EC :: ECs1) M1 M2),
  mem_simulation pinfo TD (EC' :: ECs1) M1 M2.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  split; auto.
  split; auto.
    unfold dse_mem_inj in *.
    inv_mbind.
    intros ombs Hin'.
    eapply no_alias_head_tail__replace_head in Hin'; eauto.
Qed.

Lemma mem_simulation__malloc: forall (pinfo : PhiInfo)
  (tmn2 : terminator) (lc2 : Opsem.GVsMap) (als2 als2': list mblock)
  (M2 : mem) (los : layouts) (nts : namedts) (F : fdef) (B : block) c align0
  (EC : list Opsem.ExecutionContext) t id0 (Hid: getCmdID c = Some id0)
  (cs : list cmd) (Mem : mem) (gn : GenericValue) (Mem' : mem) (mb : mblock)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1 (cs11 ++ c :: cs)
                 tmn2)
  (Hmalloc: match c with
            | insn_malloc _ _ _ _ | insn_alloca _ _ _ _ => True
            | _ => False
            end) (Hwfpi: WF_PhiInfo pinfo)
  (Hexeq: exists l1 : l, exists ps1 : phinodes,exists cs11 : list cmd,
              B = block_intro l1 ps1 (cs11 ++ c :: cs) tmn2)
  (HBinF: blockInFdefB B F = true) (Huniq: uniqFdef F)
  (Hpalloca : palloca_props.wf_State pinfo
                ({| Opsem.ECS := {|
                         Opsem.CurFunction := F;
                         Opsem.CurBB := B;
                         Opsem.CurCmds := c :: cs;
                         Opsem.Terminator := tmn2;
                         Opsem.Locals := lc2;
                         Opsem.Allocas := als2 |} :: EC;
                    Opsem.Mem := Mem |}))
  (Hmsim : mem_simulation pinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := B;
             Opsem.CurCmds := c :: cs;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: EC) Mem M2)
  (Hnrem : ~
          removable_State pinfo 
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := F;
                         Opsem.CurBB := B;
                         Opsem.CurCmds := c :: cs;
                         Opsem.Terminator := tmn2;
                         Opsem.Locals := lc2;
                         Opsem.Allocas := als2 |} :: EC;
            Opsem.Mem := Mem |})
  (Mem'0 : mem) (tsz0 : sz)
  (H2 : malloc (los, nts) Mem tsz0 gn align0 = ret (Mem', mb))
  (H25 : malloc (los, nts) M2 tsz0 gn align0 = ret (Mem'0, mb)),
  mem_simulation pinfo (los, nts)
     ({|
      Opsem.CurFunction := F;
      Opsem.CurBB := B;
      Opsem.CurCmds := cs;
      Opsem.Terminator := tmn2;
      Opsem.Locals := updateAddAL (GVsT DGVs) lc2 id0
                        ($ blk2GV (los, nts) mb # typ_pointer t $);
      Opsem.Allocas := als2' |} :: EC) Mem' Mem'0.
Proof.
  intros.
    destruct Hmsim as [Hmsim1 [Hmim3 Hmsim2]].
    split.
      apply MemProps.nextblock_malloc in H2.
      apply MemProps.nextblock_malloc in H25.
      rewrite <- H2. rewrite <- H25. rewrite Hmsim1. auto.
    split.  
      apply MemProps.bounds_malloc in H2.
      apply MemProps.bounds_malloc in H25.
      destruct H2 as [n [H21 H22]].
      destruct H25 as [n' [H25 H26]].
      rewrite H21 in H25. inv H25.
      intro b.
      rewrite H26. rewrite H22.
      destruct (eq_block b mb); auto.

      unfold dse_mem_inj in *.
      inv_mbind. clear HeqR.
      intros ombs Hin'. 
      apply malloc_inv in H2. destruct H2 as [n0 [J1 [J2 J3]]].
      apply malloc_inv in H25. destruct H25 as [n0' [J1' [J2' J3']]].
      rewrite J1 in J1'. inv J1'.
      eapply SASmsim.alloc_inject_id_inj with (m1:=Mem)(m2:=M2); eauto.
      assert (ret getCmdLoc c = getCmdID c) as G.
        erewrite getCmdLoc_getCmdID; eauto.
      destruct (id_dec id0 (PI_id pinfo)); subst.
      Case "id0 = pid".
        destruct c; tinv Hmalloc; simpl in *; inv Hid.
        SCase "c = malloc".
          destruct (fdef_dec (PI_f pinfo) F); subst.
          SSCase "F = PI_f".
            WF_PhiInfo_spec10_tac.
            simpl in HBinF; congruence.

          SSCase "F <> PI_f".
            inv Hin'.
            assert (no_alias_head_tail pinfo (None::l')
               ({|
                Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := insn_malloc (PI_id pinfo) typ5 value5 align5 :: cs;
                Opsem.Terminator := tmn2;
                Opsem.Locals := lc2;
                Opsem.Allocas := als2 |} :: EC)) as Hin.
              unfold no_alias_head_tail.
              constructor; auto.
                split; simpl; intros; auto.
                  congruence.
             apply_clear Hmsim2 in Hin.
             simpl in Hin. 
             simpl.
             destruct y; auto.
               simpl_env.
               apply SASmsim.mem_inj_ignores_weaken; auto.

        SCase "c = alloca".
          inv Hin'.
          assert (no_alias_head_tail pinfo (None::l')
             ({|
              Opsem.CurFunction := F;
              Opsem.CurBB := B;
              Opsem.CurCmds := insn_alloca (PI_id pinfo) typ5 value5 align5 :: cs;
              Opsem.Terminator := tmn2;
              Opsem.Locals := lc2;
              Opsem.Allocas := als2 |} :: EC)) as Hin.
            unfold no_alias_head_tail.
            constructor; auto.
              split; simpl; intros; auto.
                subst.
                assert (lookupAL (GVsT DGVs) lc2 (PI_id pinfo) = None) as Hnone.
                  clear - Hpalloca Hwfpi HBinF Huniq Hexeq.
                  eapply WF_PhiInfo_spec15 in Hpalloca; eauto.
                rewrite Hnone. auto.
           apply_clear Hmsim2 in Hin.
           simpl in Hin. 
           simpl.
           destruct y; auto.
             simpl_env.
             apply SASmsim.mem_inj_ignores_weaken; auto.

      Case "id0 <> pid".
        apply Hmsim2.
        eapply no_alias_head_tail__replace_head in Hin'; eauto.
        intros.
        eapply no_alias_head_in_tail_update in H; eauto.
          simpl. 
          rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma no_alias_head_in_tail_ex: forall pinfo EC,
  exists omb, no_alias_head_in_tail pinfo omb EC.
Proof.
  unfold no_alias_head_in_tail.
  intros. 
  destruct (fdef_dec (Opsem.CurFunction EC) (PI_f pinfo)).
    destruct (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) 
      as [[|[[]][]]|]; eauto.
      exists (Some b). tauto.

    destruct (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) 
      as [[|[[]][]]|]; eauto.
      exists None. tauto.
Qed.

Lemma no_alias_head_tail_ex: forall pinfo ECs,
  exists ombs, no_alias_head_tail pinfo ombs ECs.
Proof.
  unfold no_alias_head_tail.
  induction ECs; simpl; eauto.
    destruct IHECs as [ombs IHECs].
    destruct (@no_alias_head_in_tail_ex pinfo a) as [omb J].
    exists (omb::ombs). constructor; auto.
Qed.

Lemma mem_simulation__free_l2r' : forall TD Mem1 Mem2 Mem1' ECs pinfo ptr
  (Hmsim : mem_simulation pinfo TD ECs Mem1 Mem2)
  (Hmlc: free TD Mem1 ptr = ret Mem1'),
  exists Mem2', free TD Mem2 ptr = ret Mem2'.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  apply free_inv in Hmlc.
  destruct Hmlc as [blk [ofs [hi [lo [H1 [H2 [H3 H4]]]]]]].
  unfold dse_mem_inj in *.
  inv_mbind.
  destruct (@no_alias_head_tail_ex pinfo ECs) as [ombs J].
  apply_clear J3 in J.
  eapply SASmsim.free_inj_l2r with (delta:=0)(b1:=blk)(b2:=blk) in J; 
      eauto using SASmsim.inject_id_no_overlap, SASmsim.inject_id_zero_delta.
  destruct J as [m2' [J3 J4]].
  exists m2'.
  unfold free. fill_ctxhole. rewrite H2. rewrite <- J2. rewrite <- H3.
  replace (lo+0) with lo in J3 by omega.
  replace (hi+0) with hi in J3 by omega. 
  destruct (zeq 0 0); auto. congruence.
Qed.

Lemma mem_simulation__free : forall TD Mem1 Mem2 Mem1' Mem2'
  ECs1 pinfo EC EC' ptr
  (Hp: forall omb,
       no_alias_head_in_tail pinfo omb EC' ->
       no_alias_head_in_tail pinfo omb EC)
  (Hmsim : mem_simulation pinfo TD (EC :: ECs1) Mem1 Mem2)
  (Hmlc: free TD Mem1 ptr = ret Mem1')
  (Hmlc': free TD Mem2 ptr = ret Mem2'),
  mem_simulation pinfo TD (EC' :: ECs1) Mem1' Mem2'.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  apply free_inv in Hmlc.
  apply free_inv in Hmlc'.
  destruct Hmlc as [blk [ofs [hi [lo [H1 [H2 [H3 H4]]]]]]].
  destruct Hmlc' as [blk' [ofs' [hi' [lo' [H1' [H2' [H3' H4']]]]]]].
  unfold GV2ptr in *.
  destruct ptr as [|[[]][]]; inv H1. inv H1'.
  split.
    apply Mem.nextblock_free in H4'.
    apply Mem.nextblock_free in H4. 
    congruence.
  split.
    intros.
    apply Mem.bounds_free with (b:=b) in H4'; auto.
    apply Mem.bounds_free with (b:=b) in H4; auto.
    congruence.

    unfold dse_mem_inj in *.
    inv_mbind.
    intros ombs Hin'.
    assert (no_alias_head_tail pinfo ombs (EC :: ECs1)) as Hin.
      inv Hin'.
      constructor; auto.
    apply J3 in Hin.
    eapply SASmsim.free_inj with (delta:=0)(b1:=blk')(b2:=blk') in Hin; 
      eauto using SASmsim.inject_id_no_overlap, SASmsim.inject_id_zero_delta.
    replace (lo+0) with lo by omega.
    replace (hi+0) with hi by omega. 
    rewrite J2 in H3. rewrite <- H3' in H3. inv H3. auto.
Qed.

Lemma mem_simulation__free_l2r : forall TD Mem1 Mem2 Mem1'
  ECs1 pinfo EC EC' ptr
  (Hp: forall omb,
       no_alias_head_in_tail pinfo omb EC' ->
       no_alias_head_in_tail pinfo omb EC)
  (Hmsim : mem_simulation pinfo TD (EC :: ECs1) Mem1 Mem2)
  (Hmlc: free TD Mem1 ptr = ret Mem1'),
  exists Mem2',
    free TD Mem2 ptr = ret Mem2' /\
    mem_simulation pinfo TD (EC' :: ECs1) Mem1' Mem2'.
Proof.
  intros.
  assert (Hmsim':=Hmsim).
  eapply mem_simulation__free_l2r' in Hmsim'; eauto.
  destruct Hmsim' as [Mem2' Hfree'].
  exists Mem2'.
  split; auto.
    eapply mem_simulation__free; eauto.
Qed.

Lemma mem_simulation__free_allocas_l2r : forall TD ECs1 pinfo EC EC'
  (Hp: forall omb,
       no_alias_head_in_tail pinfo omb EC' ->
       no_alias_head_in_tail pinfo omb EC)
  als Mem1 Mem2 Mem1'
  (Hmsim : mem_simulation pinfo TD (EC :: ECs1) Mem1 Mem2)
  (Hmlc: free_allocas TD Mem1 als = ret Mem1'),
  exists Mem2',
    free_allocas TD Mem2 als = ret Mem2' /\
    mem_simulation pinfo TD (EC' :: ECs1) Mem1' Mem2'.
Proof.
  induction als; simpl; intros.
    uniq_result. exists Mem2. 
    split; auto.
      eapply mem_simulation__replace_head; eauto.

    inv_mbind.
    eapply mem_simulation__free_l2r with (Mem1':=m)(EC':=EC) in Hmsim; eauto.
    destruct Hmsim as [Mem2' [J1 J2]].
    rewrite J1.
    eapply IHals in J2; eauto.
Qed.

Lemma mem_simulation__free_allocas : forall TD ECs1 pinfo EC EC'
  (Hp: forall omb,
       no_alias_head_in_tail pinfo omb EC' ->
       no_alias_head_in_tail pinfo omb EC)
  als Mem1 Mem2 Mem1' Mem2'
  (Hmsim : mem_simulation pinfo TD (EC :: ECs1) Mem1 Mem2)
  (Hmlc: free_allocas TD Mem1 als = ret Mem1')
  (Hmlc': free_allocas TD Mem2 als = ret Mem2'),
  mem_simulation pinfo TD (EC' :: ECs1) Mem1' Mem2'.
Proof.
  induction als; simpl; intros.
    uniq_result. 
    eapply mem_simulation__replace_head; eauto.

    inv_mbind.
    eapply mem_simulation__free with (Mem1':=m0)(Mem2':=m) in Hmsim; eauto.
Qed.

Lemma mem_simulation__remove_head: forall TD ECs1 pinfo EC 
  (Hp : no_alias_head_in_tail pinfo None EC) M1 M2
  (Hmsim : mem_simulation pinfo TD (EC :: ECs1) M1 M2),
  mem_simulation pinfo TD ECs1 M1 M2.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  split; auto.
  split; auto.
    unfold dse_mem_inj in *.
    inv_mbind.
    intros ombs Hin'.
    replace (ombs__ignores (Size.to_Z n) ombs) with
            (ombs__ignores (Size.to_Z n) (None::ombs)) by auto.
    apply J3; auto.
      constructor; auto.
Qed.

Lemma no_alias_head_in_tail_inv3: forall lc2 pinfo mb B1 cs1 tmn2 als2 F
  (H1 : no_alias_head_in_tail pinfo (Some mb)
         {|
         Opsem.CurFunction := F;
         Opsem.CurBB := B1;
         Opsem.CurCmds := cs1;
         Opsem.Terminator := tmn2;
         Opsem.Locals := lc2;
         Opsem.Allocas := als2 |}),
  F = PI_f pinfo /\
  exists ofs, exists mc, 
    lookupAL (GVsT DGVs) lc2 (PI_id pinfo) = ret ((Vptr mb ofs, mc)::nil).
Proof.
  intros.
  destruct H1 as [H1 H2]. simpl in *.
  destruct (fdef_dec F (PI_f pinfo)) as [J | J].
    split; auto.
      apply H1 in J.
      destruct (lookupAL (GVsT DGVs) lc2 (PI_id pinfo)) 
        as [[|[[]][]]|]; try solve [congruence | inv J; eauto].

    apply H2 in J. congruence.
Qed.

Lemma mem_simulation__return: forall (pinfo : PhiInfo)
  (lc2 : Opsem.GVsMap) (als2 : list mblock) (tmn3 : terminator) t0 v0 
  (lc3 : Opsem.GVsMap) (als3 : list mblock) (M2 : mem) (los : layouts) 
  (nts : namedts) (F : fdef) (rid : id) tmn (F' : fdef) (B' : block) (i0 : id)
  (n : noret) (c : clattrs) (v : value) (p : params) (cs' : list cmd)
  (EC : list Opsem.ExecutionContext) (Mem : mem) (l3 : l) (ps3 : phinodes)
  (cs0 : list cmd) (Mem' : mem) (Hwfpi: WF_PhiInfo pinfo) Ps S
  (HwfF: wf_fdef S (module_intro los nts Ps) F)
  (H0 : free_allocas (los, nts) Mem als2 = ret Mem') maxb
  (Heq3' : exists l1 : l,
            exists ps1 : phinodes,
              exists cs11 : list cmd,
                B' =
                block_intro l1 ps1 (cs11 ++ insn_call i0 n c t0 v0 v p :: cs')
                  tmn3)
  (Hinscope: if fdef_dec (PI_f pinfo) F
             then Promotability.wf_defs maxb pinfo (los,nts) Mem lc2 als2
             else True)
  (Hmsim : mem_simulation pinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := block_intro l3 ps3 (cs0 ++ nil) tmn;
             Opsem.CurCmds := nil;
             Opsem.Terminator := tmn;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |}
             :: {|
                Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := insn_call i0 n c t0 v0 v p :: cs';
                Opsem.Terminator := tmn3;
                Opsem.Locals := lc3;
                Opsem.Allocas := als3 |} :: EC) Mem M2)
  (Mem'0 : mem) (lc''0 : Opsem.GVsMap)
  (EQ: PI_f pinfo = F' -> lookupAL (GVsT DGVs) lc3 (PI_id pinfo) =
         lookupAL (GVsT DGVs) lc''0 (PI_id pinfo))
  (H26 : free_allocas (los, nts) M2 als2 = ret Mem'0),
  mem_simulation pinfo (los, nts)
     ({|
      Opsem.CurFunction := F';
      Opsem.CurBB := B';
      Opsem.CurCmds := cs';
      Opsem.Terminator := tmn3;
      Opsem.Locals := lc''0;
      Opsem.Allocas := als3 |} :: EC) Mem' Mem'0.
Proof.
  intros.
  eapply mem_simulation__free_allocas in Hmsim; eauto.
  destruct Hmsim as [Hmsim1 [Hmsim2 Hmsim3]].
  split; auto.
  split; auto.
    unfold dse_mem_inj in *.
    inv_mbind.
    intros ombs Hin.
    destruct (@no_alias_head_in_tail_ex pinfo 
                {| Opsem.CurFunction := F;
                   Opsem.CurBB := block_intro l3 ps3 (cs0 ++ nil) tmn;
                   Opsem.CurCmds := nil;
                   Opsem.Terminator := tmn;
                   Opsem.Locals := lc2;
                   Opsem.Allocas := als2 |}) as [omb G].
    assert (no_alias_head_tail pinfo (omb::ombs)
             ({|
              Opsem.CurFunction := F;
              Opsem.CurBB := block_intro l3 ps3 (cs0 ++ nil) tmn;
              Opsem.CurCmds := nil;
              Opsem.Terminator := tmn;
              Opsem.Locals := lc2;
              Opsem.Allocas := als2 |}
              :: {|
                 Opsem.CurFunction := F';
                 Opsem.CurBB := B';
                 Opsem.CurCmds := insn_call i0 n c t0 v0 v p :: cs';
                 Opsem.Terminator := tmn3;
                 Opsem.Locals := lc3;
                 Opsem.Allocas := als3 |} :: EC)) as Hin'.
      unfold no_alias_head_tail. unfold no_alias_head_tail in Hin.
      constructor; auto.
        inv Hin.
        constructor; auto.
          eapply no_alias_head_in_tail_update in H2; eauto.
    apply_clear Hmsim3 in Hin'.
      destruct omb as [mb|]; auto.
      
      simpl in Hin'.
      apply SASmsim.mem_inj__remove_unperm_igns in Hin'; auto.
      apply no_alias_head_in_tail_inv3 in G.
      destruct G as [EQ1 [ofs [mc G]]]; subst.
      destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
      apply Hinscope in G.
      destruct G as [[_ [[mb0 [G1 [G2 [G3 G4]]]] _]] _]; subst.
      rewrite Promotability.simpl_blk2GV in G1. inv G1.
      intros.
      unfold Promotability.alloca_size_prop in G4.
      unfold getTypeAllocSize in G4.
      rewrite <- HeqR in G4.
      remember (getABITypeAlignment (los, nts) (PI_typ pinfo)) as R.
      destruct R; tinv G4.
      remember (Mem.bounds Mem mb0) as R.
      destruct R as [lo hi].
      destruct G4 as [G4 _].
      destruct (@G4 lo hi) as [G41 G42]; subst; auto.
      eapply MemProps.perm_mfree_alloca_2 in H0; eauto.
      assert (RoundUpAlignment n0 n1 >= n0)%nat as G.
        apply RoundUpAlignment_spec.
          eapply WF_PhiInfo_spec16 in HwfF; eauto.
          unfold getABITypeAlignment, getAlignment in HeqR0.
          destruct HwfF as [sz [al [J1 [J2 J3]]]].
          rewrite J1 in HeqR0. inv HeqR0. auto.
      unfold Size.to_Z in *.
      omega.
Qed. 

Lemma no_alias_head_in_tail__wf_ECStack_head_in_tail__no_alias_with_blk: forall
  (pinfo : PhiInfo) (lc2 : AssocList (GVsT DGVs))
  (gv2 : GVsT DGVs) S los nts Ps (Mem : Mem.mem) F t v gl
  (Hwfv: wf_value S (module_intro los nts Ps) F v t)
  (maxb : Values.block) (Hget : getOperandValue (los,nts) v lc2 gl = ret gv2)
  (EC : Opsem.ExecutionContext) (mb : mblock)
  (H : no_alias_head_in_tail pinfo (ret mb) EC)
  (Hwfg: MemProps.wf_globals maxb gl)
  (Hnals1 : 
    Promotability.wf_ECStack_head_in_tail maxb pinfo (los,nts) Mem lc2 EC),
  MemProps.no_alias_with_blk gv2 mb.
Proof.
  intros.
  unfold no_alias_head_in_tail in H.  
  destruct H as [H1 H2]. 
  destruct (fdef_dec (Opsem.CurFunction EC) (PI_f pinfo)) as [J | J].
    assert (G:=J).
    apply_clear H1 in J; auto.
    remember (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) as R.
    destruct R as [[|[[]][]]|]; tinv J.
    inv J. symmetry in HeqR.
    eapply Promotability.wf_ECStack_head_in_tail__no_alias_with_blk; eauto.
    
    apply_clear H2 in J. congruence.
Qed.

Lemma no_alias_head_tail__wf_ECStack_head_tail__no_alias_with_blk: 
  forall pinfo lc2 gv2 los nts Mem maxb size Ps F t gl
  (Hwfg: MemProps.wf_globals maxb gl) v S
  (Hwfv: wf_value S (module_intro los nts Ps) F v t)
  (Hget : getOperandValue (los,nts) v lc2 gl = ret gv2) EC ombs
  (Hdse: no_alias_head_tail pinfo ombs EC)
  (Hnals: Promotability.wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc2 EC),
  List.Forall (fun re => 
               let '(mb,_,_) := re in
               MemProps.no_alias_with_blk gv2 mb) (ombs__ignores size ombs).
Proof.
  intros.
  induction Hdse; simpl; intros; auto.
    apply Promotability.wf_ECStack_head_tail_cons__inv in Hnals.
    destruct Hnals as [Hnals1 Hals2].
    apply_clear IHHdse in Hals2.
    destruct y as [mb|]; auto.
    constructor; auto.
    eapply no_alias_head_in_tail__wf_ECStack_head_in_tail__no_alias_with_blk; 
      eauto.
Qed.

Lemma no_alias_head_tail__notin_ignores_with_size': forall maxb pinfo  
  los nts Mem lc2 EC gl
  (Hnals: Promotability.wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc2 EC)
  (Hwfg: MemProps.wf_globals maxb gl) S Ps t v F 
  (Hwfv: wf_value S (module_intro los nts Ps) F v (typ_pointer t))
  b' ofs' m'
  (Hget: getOperandValue (los,nts) v lc2 gl = Some ((Vptr b' ofs', m')::nil)) ombs size'
  (Hin: no_alias_head_tail pinfo ombs EC) size,
  SASmsim.notin_ignores_with_size (ombs__ignores size' ombs) b'
     (Int.signed 31 ofs') size.
Proof.
  intros.
  eapply no_alias_head_tail__wf_ECStack_head_tail__no_alias_with_blk 
    with (size:=size') in Hin; eauto.
  eapply SASmsim.no_alias_with_blk__notin_ignores_with_size; eauto.
Qed.   

Lemma no_alias_head_in_tail_dec: forall pinfo EC mb
  (Hnone: no_alias_head_in_tail pinfo None EC)
  (Hsome: no_alias_head_in_tail pinfo (Some mb) EC),
  False.
Proof.
  unfold no_alias_head_in_tail.
  intros.
  destruct (fdef_dec (Opsem.CurFunction EC) (PI_f pinfo)) as [J | J].
    assert (J':=J).
    apply Hnone in J. 
    apply Hsome in J'. 
    destruct (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) 
      as [[|[[]][]]|]; inv J; inv J'.

    assert (J':=J).
    apply Hnone in J. 
    apply Hsome in J'. 
    destruct (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) 
      as [[|[[]][]]|]; inv J; inv J'.
Qed.

Lemma unused_pid_no_alias_head_in_tail__wf_defs__no_alias_with_blk: 
  forall pinfo F los nts maxb Mem lc2 EC gv2 als2
  (Hinscope: if fdef_dec (PI_f pinfo) F
             then Promotability.wf_defs maxb pinfo (los,nts) Mem lc2 als2
             else True)
  gl (Hwfg: MemProps.wf_globals maxb gl) v S t Ps
  (Hwfv: wf_value S (module_intro los nts Ps) F v t)
  (Hget : getOperandValue (los,nts) v lc2 gl = ret gv2) mb
  (Hneq: used_in_value (PI_id pinfo) v = false)
  (Heq1: Opsem.CurFunction EC = F) (Heq2: Opsem.Locals EC = lc2)
  (Heq3: Opsem.Allocas EC = als2)
  (Hdse: no_alias_head_in_tail pinfo (Some mb) EC),
  MemProps.no_alias_with_blk gv2 mb.
Proof.
  intros.
  destruct Hdse as [J1 J2]. subst.
  destruct (fdef_dec (PI_f pinfo) (Opsem.CurFunction EC)) as [J | J].
    symmetry in J. assert (G:=J).
    apply_clear J1 in J.
    remember (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) as R.
    destruct R as [[|[[]][]]|]; inv J.
    clear J2. symmetry in HeqR.
    eapply Promotability.wf_defs__no_alias_with_blk; eauto.

    assert (Opsem.CurFunction EC <> PI_f pinfo) as G. intro K. auto.
    apply J2 in G. congruence.
Qed.

Lemma no_alias_head_in_tail_inv2: forall EC pinfo y
  (Heq : Opsem.CurFunction EC <> PI_f pinfo)
  (H1 : no_alias_head_in_tail pinfo y EC), y = None.
Proof.
  intros.
  destruct H1 as [_ H1]. auto.
Qed.

Lemma load_notin_fdef__unused_in_value: forall F v t id0 align0 cs B tmn2 vid0
  (Hnld: load_in_fdef vid0 F = false) (HBinF: blockInFdefB B F = true)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1
                 (cs11 ++ insn_load id0 t v align0 :: cs) tmn2),
  used_in_value vid0 v = false.
Proof.
  destruct F as [fh bs]. simpl. intros.
  remember false as R. rewrite HeqR in Hnld at 2. rewrite HeqR. clear HeqR.
  generalize dependent R. 
  induction bs; simpl in *; intros.
    inv HBinF.

    apply orb_true_iff in HBinF.
    destruct HBinF as [HBinF | HBinF]; eauto 2.
      apply blockEqB_inv in HBinF.
      subst.

      clear IHbs.
      apply fold_left_eq in Hnld.
        apply orb_false_iff in Hnld.
        destruct Hnld.
        destruct Heq3 as [l1 [ps1 [cs11 Heq3]]]; subst.
        simpl in H0.
        apply load_notin_cmds__unused_in_value in H0; auto.

        intros c b J.
        apply orb_false_iff in J.
        destruct J; auto.
Qed.

Lemma no_alias_head_tail__notin_ignores_with_size: forall maxb pinfo
  los nts Mem lc2 EC gl
  (Hnals: Promotability.wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc2 EC)
  (Hwfg: MemProps.wf_globals maxb gl) S Ps als2 tmn2 id0 t align0 v cs B F
  (Hwfv: wf_value S (module_intro los nts Ps) F v (typ_pointer t))
  (Hinscope: if fdef_dec (PI_f pinfo) F
             then Promotability.wf_defs maxb pinfo (los,nts) Mem lc2 als2
             else True) b' ofs' m'
  (Hget: getOperandValue (los,nts) v lc2 gl = Some ((Vptr b' ofs', m')::nil)) ombs size'
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (HBinF: blockInFdefB B F = true)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1
                 (cs11 ++ insn_load id0 t v align0 :: cs) tmn2)
  (Hin: no_alias_head_tail pinfo ombs 
        ({|
         Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := insn_load id0 t v align0 :: cs;
         Opsem.Terminator := tmn2;
         Opsem.Locals := lc2;
         Opsem.Allocas := als2 |} :: EC)) size,
  SASmsim.notin_ignores_with_size (ombs__ignores size' ombs) b'
     (Int.signed 31 ofs') size.
Proof.
  intros.
  inv Hin. simpl.
  eapply no_alias_head_tail__notin_ignores_with_size' with (size:=size)(size':=size') 
    in H3; eauto.
  destruct y as [mb|]; auto.
    unfold SASmsim.notin_ignores_with_size in *.
    constructor; auto.
    remember (used_in_value (PI_id pinfo) v) as R.
    destruct R.
      destruct (fdef_dec F (PI_f pinfo)); subst.
        eapply load_notin_fdef__unused_in_value in Hnld; eauto.
        congruence.

        apply no_alias_head_in_tail_inv2 in H1; simpl; auto. congruence.
      
      eapply unused_pid_no_alias_head_in_tail__wf_defs__no_alias_with_blk in H1; 
        eauto.
      simpl in H1. auto.
Qed.

Lemma mem_simulation__mload: forall (maxb : Z) (pinfo : PhiInfo) 
  (gl2 : GVMap) (fs2 : GVMap) (tmn2 : terminator)
  (lc2 : Opsem.GVsMap) (als2 : list mblock) (M2 : mem) (S : system)
  (los : layouts) (nts : namedts) (Ps : list product) (F : fdef) (B : block)
  (id0 : id) (t : typ) (align0 : align) (v : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (Mem : mem)
  (mp : GenericValue) (gv : GenericValue)
  (H1 : mload (los, nts) Mem mp t align0 = ret gv)
  (Hwfg : MemProps.wf_globals maxb gl2)
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (HBinF: blockInFdefB B F = true)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1
                 (cs11 ++ insn_load id0 t v align0 :: cs) tmn2)
  (Hmsim : mem_simulation pinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := B;
             Opsem.CurCmds := insn_load id0 t v align0 :: cs;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: EC) Mem M2)
  (Hinscope' : if fdef_dec (PI_f pinfo) F
              then Promotability.wf_defs maxb pinfo (los, nts) Mem lc2 als2
              else True)
  (HwfHT : Promotability.wf_ECStack_head_tail maxb pinfo (los, nts) Mem lc2 EC)
  (gv0 : GenericValue) (H23 : mload (los, nts) M2 mp t align0 = ret gv0)
  (H21 : Opsem.getOperandValue (los, nts) v lc2 gl2 = ret mp)
  (Hwfv : wf_value S (module_intro los nts Ps) F v (typ_pointer t)),
  gv = gv0.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  simpl in HwfHT.
  apply mload_inv in H1.
  destruct H1 as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  apply mload_inv in H23.
  destruct H23 as [b' [ofs' [m' [mc' [J1' [J2' J3']]]]]]; subst.
  rewrite J2 in J2'. inv J2'. inv J1'.
  unfold dse_mem_inj in Hmsim2.
  inv_mbind. clear HeqR.
  destruct (@no_alias_head_tail_ex pinfo 
             ({| Opsem.CurFunction := F;
                 Opsem.CurBB := B;
                 Opsem.CurCmds := insn_load id0 t v align0 :: cs;
                 Opsem.Terminator := tmn2;
                 Opsem.Locals := lc2;
                 Opsem.Allocas := als2 |} :: EC)) as [ombs Hin].
  assert (G:=Hin).
  apply_clear Hmsim2 in Hin.
  eapply SASmsim.mload_aux_inject_id_inj2; eauto.
    eapply no_alias_head_tail__notin_ignores_with_size; eauto.
Qed.

Lemma mstore_unremovable_mem_simulation: forall (maxb : Z) (pinfo : PhiInfo)
  (gl2 : GVMap) (tmn2 : terminator) 
  (lc2 : Opsem.GVsMap) (als2 : list mblock) (M2 : mem) (S : system)
  (los : layouts) (nts : namedts) (Ps : list product) (F : fdef) (B : block)
  (sid : id) (t : typ) (align0 : align) (v1 : value) (v2 : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (Mem : mem)
  (HBinF1 : blockInFdefB B F = true) (mp2 : GenericValue) (gv1 : GenericValue)
  (Mem' : mem) (H3 : mstore (los, nts) Mem mp2 t gv1 align0 = ret Mem')
  (Hwfg : wf_global (los, nts) S gl2) (Hwflc1 : OpsemPP.wf_lc (los, nts) F lc2)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1
                 (cs11 ++ insn_store sid t v1 v2 align0 :: cs) tmn2)
  (Hmsim : mem_simulation pinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := B;
             Opsem.CurCmds := insn_store sid t v1 v2 align0 :: cs;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: EC) Mem M2)
  (Hnrem : ~
          removable_State pinfo 
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := F;
                         Opsem.CurBB := B;
                         Opsem.CurCmds := insn_store sid t v1 v2 align0 :: cs;
                         Opsem.Terminator := tmn2;
                         Opsem.Locals := lc2;
                         Opsem.Allocas := als2 |} :: EC;
            Opsem.Mem := Mem |})
  (Hinscope' : if fdef_dec (PI_f pinfo) F
              then Promotability.wf_defs maxb pinfo (los, nts) Mem lc2 als2
              else True)
  (Mem'0 : mem)
  (H24 : Opsem.getOperandValue (los, nts) v1 lc2 gl2 = ret gv1)
  (H25 : Opsem.getOperandValue (los, nts) v2 lc2 gl2 = ret mp2)
  (H28 : mstore (los, nts) M2 mp2 t gv1 align0 = ret Mem'0)
  (Hwfv : wf_value S (module_intro los nts Ps) F v1 t),
  mem_simulation pinfo (los, nts)
     ({|
      Opsem.CurFunction := F;
      Opsem.CurBB := B;
      Opsem.CurCmds := cs;
      Opsem.Terminator := tmn2;
      Opsem.Locals := lc2;
      Opsem.Allocas := als2 |} :: EC) Mem' Mem'0.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  split.
    apply MemProps.nextblock_mstore in H3.
    apply MemProps.nextblock_mstore in H28.
    rewrite <- H3. rewrite <- H28. rewrite Hmsim1. auto.
  
  split.
    intro b.
    apply MemProps.bounds_mstore with (b':=b) in H3.
    apply MemProps.bounds_mstore with (b':=b) in H28.
    congruence.
  
    apply mstore_inversion in H28.
    destruct H28 as [b [ofs [cm [J1 J2]]]]; subst.
    apply mstore_inversion in H3.
    destruct H3 as [b' [ofs' [cm' [J1' J2']]]]; subst.
    inv J1'.
    unfold dse_mem_inj in *.
    inv_mbind.
    intros ombs Hin'.
    eapply no_alias_head_tail_irrel in Hin'.
    eapply_clear Hmsim2 in Hin'.
    eapply SASmsim.mstore_aux_inject_id_mapped_inj2; eauto.
Qed.

Ltac dse_is_sim_malloc :=
  destruct_ctx_other;
  match goal with 
  | Hcssim2: cmds_simulation _ _ _ _,
    Hop2: Opsem.sInsn _ _ _ _ |- _ =>
    apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
    destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
    inv Hop2; uniq_result
  end;
  match goal with
  | Hmsim: mem_simulation _ _ _ ?M1 ?M2,
    H25: malloc _ ?M1 _ _ _ = Some (_, ?mb),
    H2: malloc _ ?M2 _ _ _ = Some (_, ?mb0) |- _ =>
    assert (mb0 = mb) as EQ; try solve [
      match goal with
      | |- _ = _ =>
        destruct Hmsim as [Hmsim _];
        apply MemProps.malloc_result in H25;
        apply MemProps.malloc_result in H2; subst; auto
      end
    ]
  end;
  subst;
  repeat_solve;
    eapply mem_simulation__malloc; eauto using wf_system__uniqFdef; simpl; auto.

Lemma dse_is_sim : forall maxb pinfo Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo)
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1)
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hsim: State_simulation pinfo Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State pinfo St1) St1' tr1
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1),
     State_simulation pinfo Cfg1 St1' Cfg2 St2 /\ tr1 = E0) /\
  (forall (Hnrem: ~removable_State pinfo St1) St1' St2' tr1 tr2
     (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2)
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1),
     State_simulation pinfo Cfg1 St1' Cfg2 St2' /\ tr1 = tr2).
Proof.

Local Opaque inscope_of_tmn inscope_of_cmd.

  intros.
  split; intros.
Case "removable state".

  destruct Cfg1 as [S1 [los nts] Ps1 gl1 fs1].
  destruct St1 as [ECs1 M1].
  destruct ECs1 as [|[F1 B1 [|c1 cs1] tmn1 lc1 als1] ECs1]; tinv Hrem.
  destruct_cmd c1; tinv Hrem.
  simpl in Hrem.
  destruct v0 as [qid | vc]; tinv Hrem.
  destruct (fdef_dec (PI_f pinfo) F1); subst; tinv Hrem.
  destruct (id_dec (PI_id pinfo) qid); subst; tinv Hrem.

  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]].
  destruct Hwfpp as
    [_ [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 _]]]]
     [HwfECs Hwfcall]]
    ]; subst.
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

    assert (wf_value S1 (module_intro los nts Ps1) (PI_f pinfo) v 
              (PI_typ pinfo) /\ t = PI_typ pinfo) as Hwfv.
      get_wf_value_for_simop_ex. 
      inv H11.
      eapply WF_PhiInfo_spec20 in Hwfpi; eauto using wf_system__uniqFdef.
      uniq_result. auto.
    destruct Hwfv; subst.
    eapply mstore_palloca_mem_simulation in Hmsim; eauto.

Case "unremovable state".
  (sInsn_cases (destruct Hop1) SCase).

SCase "sReturn".
Focus.
  destruct_ctx_return.
  repeat_solve.
    assert (Huniq: uniqFdef F') by eauto using wf_system__uniqFdef.
    assert (PI_f pinfo = F' ->
            lookupAL (GVsT DGVs) lc3 (PI_id pinfo) =
              lookupAL (GVsT DGVs) lc''0 (PI_id pinfo)) as EQ.
      unfold Opsem.returnUpdateLocals in H1.
      inv_mbind; auto.
      destruct_if; auto.
      inv_mbind; auto.
      solve_non_pid_updateAddAL.
    assert (wf_fdef S (module_intro los nts Ps) F) as HwfF.
      eauto using wf_system__wf_fdef.
    clear - H26 Hmsim H0 H1 Heq3' Hinscope1' HwfF Hwfpi EQ.
    eapply mem_simulation__return; eauto.
Unfocus.

SCase "sReturnVoid".
Focus.
  destruct_ctx_return.
  repeat_solve.
    assert (wf_fdef S (module_intro los nts Ps) F) as HwfF.
      eauto using wf_system__wf_fdef.
    clear - H24 Hmsim H0 Heq3' Hinscope1' HwfF Hwfpi.
    eapply mem_simulation__return; eauto.
Unfocus.

SCase "sBranch".
Focus.
  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    clear - H22 H1 Hfsim2.
    destruct (isGVZero (los, nts) c); eauto using fdef_sim__block_sim.
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq1 [Heq2 [Hcssim' Heq5]]]; subst.

  assert (lc' = lc'0) as Heq.
    clear - H2 H23 Hbsim2.
    eapply switchToNewBasicBlock_sim in Hbsim2; eauto.
  subst.

  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    assert (uniqFdef F) as Huniq by eauto using wf_system__uniqFdef.
    assert (blockInFdefB (block_intro l'0 ps'0 cs' tmn'0) F = true) as HBinF.
      solve_blockInFdefB. 
    assert (F = PI_f pinfo ->
            lookupAL (GVsT DGVs) lc2 (PI_id pinfo) =
            lookupAL (GVsT DGVs) lc'0 (PI_id pinfo)) as EQ.
      intros. subst.
      eapply switchToNewBasicBlock_doesnt_change_pid; eauto.
    clear - H2 Hmsim EQ.
    eapply mem_simulation_update_locals in Hmsim; simpl; eauto.

Unfocus.

SCase "sBranch_uncond".
Focus.
  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    eauto using fdef_sim__block_sim.
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq1 [Heq2 [Hcssim' Heq5]]]; subst.

  assert (lc' = lc'0) as Heq.
    clear - H0 H17 Hbsim2.
    eapply switchToNewBasicBlock_sim in Hbsim2; eauto.
  subst.

  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    assert (uniqFdef F) as Huniq by eauto using wf_system__uniqFdef.
    assert (blockInFdefB (block_intro l'0 ps'0 cs' tmn'0) F = true) as HBinF.
      solve_blockInFdefB. 
    assert (F = PI_f pinfo ->
            lookupAL (GVsT DGVs) lc2 (PI_id pinfo) =
            lookupAL (GVsT DGVs) lc'0 (PI_id pinfo)) as EQ.
      intros. subst.
      eapply switchToNewBasicBlock_doesnt_change_pid; eauto.
    clear - H0 Hmsim EQ.
    eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
Unfocus.

SCase "sBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExtractValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sInsertValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sMalloc". abstract (dse_is_sim_malloc).
SCase "sFree".

  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    eapply mem_simulation__free; eauto.
    eapply mem_simulation__replace_head in Hmsim; eauto.

SCase "sAlloca". abstract (dse_is_sim_malloc).

SCase "sLoad".
  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  assert (gv = gv0) as EQ.
    assert (wf_value S (module_intro los nts Ps) F v (typ_pointer t)) as Hwfv.
      get_wf_value_for_simop_ex. auto.
    clear - H23 Hmsim H1 H21 HwfHT Hinscope' Hwfmg Hwfv Heq3 Hnld HBinF1. 
    simpl in *.
    eapply mem_simulation__mload; eauto.
  subst.
  dse_is_sim_mem_update.

SCase "sStore".

  destruct_ctx_other.

  assert (PI_f pinfo = F ->
          store_in_cmd (PI_id pinfo) (insn_store sid t v1 v2 align0) = false)
         as J.
    clear - Hnrem. simpl in Hnrem.
    destruct v2 as [i0|]; auto.
    intros. subst.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    simpl.
    destruct (id_dec i0 (PI_id pinfo)); subst; auto.
    destruct (id_dec (PI_id pinfo) (PI_id pinfo)); try congruence.
    contradict Hnrem; auto.
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    assert (wf_value S (module_intro los nts Ps) F v1 t) as Hwfv.
      get_wf_value_for_simop_ex. auto.
    clear - Hwfv H28 H24 H3 Hwflc1 Heq3 Hmsim HBinF1 Hinscope' H25 Hwfg Hnrem.
    eapply mstore_unremovable_mem_simulation; eauto.

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
    destruct (isGVZero (los,nts) c); dse_is_sim_mem_update.

SCase "sCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.

  inv Hop2.

  SSCase "SCall".

  uniq_result.
  assert (Hfsim1:=Hpsim).
  eapply TopSim.lookupFdefViaPtr__simulation in Hfsim1; eauto.
  simpl in Hfsim1.
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

    destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
    split; auto.
    split; auto.
       clear - Hmsim2 Hwfpi H4 H1 HwfSystem HmInS.
       unfold dse_mem_inj in *.
       inv_mbind. 
       intros ombs Hin'.
       inv Hin'.
       assert (y = None) as EQ.
         destruct (fdef_dec (fdef_intro (fheader_intro fa rt fid la va) lb) 
                          (PI_f pinfo)).
           apply OpsemAux.lookupFdefViaPtr_inv in H1; auto.
           eapply arguments_dont_define_pid in H4; eauto using wf_system__uniqFdef.
           destruct H2 as [H2 _]. simpl in H2.
           apply H2 in e. rewrite H4 in e. auto.

           apply no_alias_head_in_tail_inv2 in H2; simpl; auto.
        subst. simpl. apply Hmsim2; auto.

  SSCase "sExCall".

  uniq_result.
  match goal with
  | H1: OpsemAux.lookupFdefViaPtr ?Ps ?fs2 ?fptr = _,
    H29 : OpsemAux.lookupExFdecViaPtr ?Ps2 ?fs2 ?fptr = _,
    Hpsim : products_simulation _ ?Ps ?Ps2 |- _ =>
  clear - H29 H1 Hpsim;
  eapply TopSim.lookupFdefViaPtr__simulation_l2r in H1; eauto;
  simpl in H1;
  destruct H1 as [f2 [H1 H2]];
  apply OpsemAux.lookupExFdecViaPtr_inversion in H29;
  apply OpsemAux.lookupFdefViaPtr_inversion in H1;
  destruct H29 as [fn [J1 [J2 J3]]];
  destruct H1 as [fn' [J4 J5]]
  end.
  uniq_result.

SCase "sExCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.

  inv Hop2.

  SSCase "SCall".

  uniq_result.

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

  uniq_result.

  assert (Hlkdec:=Hpsim).
  eapply TopSim.lookupExFdecViaPtr__simulation_l2r in Hlkdec; eauto.
  uniq_result.

  eapply callExternalFunction__mem_simulation in Hmsim; eauto.
  destruct Hmsim as [EQ [Hmsim EQ']]; subst.
  uniq_result.
  assert (PI_f pinfo = F ->
          lookupAL (GVsT DGVs) lc2 (PI_id pinfo) =
          lookupAL (GVsT DGVs) lc' (PI_id pinfo)) as EQ.
    unfold Opsem.exCallUpdateLocals in H34.
    destruct_if; auto.
    inv_mbind; auto.
    solve_non_pid_updateAddAL.
  dse_is_sim_mem_update.

Transparent inscope_of_tmn inscope_of_cmd.

Qed.
