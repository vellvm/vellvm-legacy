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
Require Import mem2reg.
Require Import memory_props.
Require Import program_sim.
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

Lemma fdef_sim__block_sim : forall pinfo f1 f2 b1 b2 l0,
  fdef_simulation pinfo f1 f2 ->
  lookupBlockViaLabelFromFdef f1 l0 = Some b1 ->
  lookupBlockViaLabelFromFdef f2 l0 = Some b2 ->
  block_simulation pinfo f1 b1 b2.
Admitted. (* fsim *)

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
Admitted. (* switch sim *)

Lemma mem_simulation_update_locals :
  forall pinfo TD EC1 EC2 ECs M1 M2
  (EQ: Opsem.CurFunction EC1 = Opsem.CurFunction EC2)
  (Hp: forall (EQ': Opsem.CurFunction EC1 = PI_f pinfo),
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
  gl2 B1 cs1 tmn2 als2 ECs1 M2 i0 t v maxb Ps S
  (H23: mstore (los, nts) M1 mp2 t gv1 a = ret M1')
  (H20: @Opsem.getOperandValue DGVs (los, nts) (value_id (PI_id pinfo)) lc2 gl2 =
          ret mp2)
  (Hinscope' : if fdef_dec (PI_f pinfo) (PI_f pinfo)
              then Promotability.wf_defs maxb pinfo (los, nts) M1 lc2 als2
              else True)
  (H19 : Opsem.getOperandValue (los,nts) v lc2 gl2 = ret gv1)
  (Hwfg : wf_global (los, nts) S gl2)
  (Hwflc1 : OpsemPP.wf_lc (los, nts) (PI_f pinfo) lc2)
  (Hwfv : wf_value S (module_intro los nts Ps) (PI_f pinfo) v t)
  (Hmsim: mem_simulation pinfo (los, nts)
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := insn_store i0 t v (value_id (PI_id pinfo)) a
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
              Opsem.CurCmds := insn_store i0 t v (value_id (PI_id pinfo)) a
                               :: cs1;
              Opsem.Terminator := tmn2;
              Opsem.Locals := lc2;
              Opsem.Allocas := als2 |} :: ECs1)) as Hin.
      constructor; auto.     
    apply Hmsim2 in Hin. clear Hmsim2.
    simpl in Hin.
    assert (t = PI_typ pinfo) as EQ.
      admit. (* by wf *)
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

Lemma fdef_simulation_inv: forall pinfo fh1 fh2 bs1 bs2,
  fdef_simulation pinfo (fdef_intro fh1 bs1) (fdef_intro fh2 bs2) ->
  fh1 = fh2 /\
  List.Forall2
    (fun b1 b2 =>
      block_simulation pinfo (fdef_intro fh1 bs1) b1 b2) bs1 bs2.
Admitted. (* fsim *)

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
Lemma callExternalFunction__mem_simulation_l2r: forall pinfo TD St1 M1 M2 fid0 gvss0
  oresult1 M1' dck tr1 gl tret targs,
  mem_simulation pinfo TD St1 M1 M2 ->
  callExternalOrIntrinsics TD gl M1 fid0 tret targs dck gvss0 =
    ret (oresult1, tr1, M1') ->
  exists M2', exists oresult2, exists tr2, 
    callExternalOrIntrinsics TD gl M2 fid0 tret targs dck gvss0 =
      ret (oresult2, tr2, M2') /\
    oresult1 = oresult2 /\ mem_simulation pinfo TD St1 M1' M2' /\ tr1 = tr2.
Admitted. (* excall sim *)

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

Ltac dse_is_sim_common_case :=
match goal with
| Hcssim2: cmds_simulation _ _ _ _,
  Hop2: Opsem.sInsn _ _ _ _,
  Hmsim: mem_simulation _ _ _ _ _ |- _ =>
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  repeat_solve;
    eapply mem_simulation_update_locals in Hmsim; simpl; try solve [
      eauto |
      simpl; intros;
      match goal with
      | |- lookupAL _ ?lc ?id1 =
             lookupAL _ (updateAddAL _ ?lc _ _ ) ?id1 =>
        admit  (* id <> palloca *)
      end]
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
        destruct c; tinv Hmalloc; simpl in *; inv Hid.
          admit. (* malloc <> pid *)

          inv Hin'.
          assert (no_alias_head_tail pinfo (None::l')
             ({|
              Opsem.CurFunction := F;
              Opsem.CurBB := B;
              Opsem.CurCmds := insn_alloca (PI_id pinfo) t0 v a :: cs;
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
  (EQ: lookupAL (GVsT DGVs) lc3 (PI_id pinfo) =
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
    eapply wf_ECStack_head_in_tail__no_alias_with_blk; eauto.
    
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
    eapply wf_defs__no_alias_with_blk; eauto.

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

Lemma load_notin_cmds__unused_in_value: forall vid0 id0 t v align0 cs cs11,
  load_in_cmds vid0 (cs11 ++ insn_load id0 t v align0 :: cs) = false ->
  used_in_value vid0 v = false.
Proof. 
  unfold load_in_cmds. intros.
  remember false as R. rewrite HeqR in H at 2. rewrite HeqR. clear HeqR.
  generalize dependent R. 
  induction cs11; simpl; intros; eauto.
    apply fold_left_eq in H.
      apply orb_false_iff in H.
      destruct H; auto.

      intros a b J.
      apply orb_false_iff in J.
      destruct J; auto.
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
    assert (wf_value S1 (module_intro los nts Ps1) (PI_f pinfo) v t) as Hwfv.
      admit. (* wf *)
    eapply mstore_palloca_mem_simulation in Hmsim; eauto.

Case "unremovable state".
  (sInsn_cases (destruct Hop1) SCase).

SCase "sReturn".
Focus.
  destruct_ctx_return.
  repeat_solve.
    assert (wf_fdef S (module_intro los nts Ps) F) as HwfF.
      eauto using wf_system__wf_fdef.
    clear - H26 Hmsim H0 H1 Heq3' Hinscope1' HwfF Hwfpi.
    eapply mem_simulation__return; eauto.
      admit. (* pid <> i0 *)
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

    clear - H2 Hmsim.
    eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
      simpl. intros.
      admit. (* phis <> palloca *)

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

    clear - H0 Hmsim.
    eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
      simpl. intros.
      admit. (* phis <> palloca *)
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
      admit. (* wf *)
    clear - H23 Hmsim H1 H21 HwfHT Hinscope' Hwfmg Hwfv Heq3 Hnld HBinF1. 
    simpl in *.
    eapply mem_simulation__mload; eauto.
  subst.
  repeat_solve.
    eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
      admit. (* lid <> pid *)

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
      admit. (* wf *)
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
  repeat_solve.
    eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
      simpl. intros. admit. (* cid <> pid *)

Transparent inscope_of_tmn inscope_of_cmd.

Qed.

Lemma s_genInitState__dse_State_simulation: forall pinfo S1 S2 main VarArgs cfg2
  IS2 (Hssim: system_simulation pinfo S1 S2)
  (Hinit: Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2)),
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo cfg1 IS1 cfg2 IS2.
Proof.
  unfold Opsem.s_genInitState.
  intros.
  inv_mbind'.
  destruct m as [los nts ps].
  inv_mbind'.
  destruct b as [l0 ps0 cs0 tmn0].
  destruct f as [[fa rt fid la va] bs].
  inv_mbind'. symmetry_ctx.
  assert (HlkF2FromS2:=HeqR).
  eapply TopSim.system_simulation__fdef_simulation_r2l in HeqR; eauto.
  destruct HeqR as [f1 [HlkF1fromS1 Hfsim]]. simpl in Hfsim.
  fill_ctxhole.
  eapply TopSim.system_simulation__getParentOfFdefFromSystem in HeqR0; eauto.
  destruct HeqR0 as [m1 [J1 J2]].
  fill_ctxhole. destruct m1 as [los1 nts1 ps1].
  destruct J2 as [J2 [J3 J4]]; subst.
  eapply TopSim.genGlobalAndInitMem_spec in HeqR1; eauto.
  destruct HeqR1 as [gl1 [fs1 [M1 [HeqR1 [EQ1 [EQ2 EQ3]]]]]]; subst.
  fill_ctxhole.
  assert (J:=HeqR2).
  eapply getEntryBlock__simulation in J; eauto.
  destruct J as [b1 [J5 J6]].
  fill_ctxhole.
  destruct b1 as [l2 ps2 cs2 tmn2].
  destruct f1 as [[fa1 rt1 fid1 la1 va1] bs1].
  assert (J:=Hfsim).
  apply fdef_simulation__eq_fheader in J.
  inv J.
  fill_ctxhole. eauto.
  match goal with
  | |- exists _:_, exists _:_, Some (?A, ?B) = _ /\ _ => exists A; exists B
  end.
  match goal with 
  | H: getParentOfFdefFromSystem _ _ = _ |- _ =>
    apply getParentOfFdefFromSystem__moduleInProductsInSystemB in H;
    destruct H as [HMinS HinPs]
  end.
  assert (J:=J6).
  apply block_simulation_inv in J.
  destruct J as [J1 [J2 [J3 J7]]]; subst.
  assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0)
           (fdef_intro (fheader_intro fa rt fid la va) bs) = true) as HBinF.
    apply entryBlockInFdef; auto.
  split; auto.
  eapply genGlobalAndInitMem__wf_globals_Mem in HeqR1; eauto.
  destruct HeqR1 as [J7 [J8 [J9 [J10 [J11 [J12 [J13 J14]]]]]]].
  repeat (split; auto).
    exists l0. exists ps0. exists nil. auto.
    exists l0. exists ps0. exists nil. auto.

    unfold dse_mem_inj. 
    assert (exists tsz, getTypeStoreSize (OpsemAux.initTargetData los nts Mem.empty)
             (PI_typ pinfo) = Some tsz) as Htsz.
      admit. (* When dse runs PI_f must be in the system, see mem2reg_correct *)
    destruct Htsz as [tsz Htsz]. fill_ctxhole.
    intros.
    eapply SASmsim.from_MoreMem_inj; eauto.
Qed.

Ltac inTmnOp_isnt_stuck v H3 Hwfcfg1 Hwfpp1 :=
match type of Hwfpp1 with
| OpsemPP.wf_State 
              {|
              OpsemAux.CurSystem := _;
              OpsemAux.CurTargetData := ?td;
              OpsemAux.CurProducts := _;
              OpsemAux.Globals := ?gl;
              OpsemAux.FunTable := _ |}
    {| Opsem.ECS := {| Opsem.CurFunction := _;
                       Opsem.CurBB := ?b;
                       Opsem.CurCmds := nil;
                       Opsem.Terminator := ?tmn;
                       Opsem.Locals := ?lc;
                       Opsem.Allocas := _
                     |} :: _;
       Opsem.Mem := _ |}  =>
    let G := fresh "G" in
    let gvs := fresh "gvs" in
    assert (exists gvs, Opsem.getOperandValue td v lc gl = Some gvs) as G; 
      try solve [
        destruct H3 as [l5 [ps2 [cs21 H3]]]; subst;
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as 
          [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
        inv_mbind;
        eapply OpsemPP.getOperandValue_inTmnOperans_isnt_stuck; eauto 1;
          simpl; auto
      ];
    destruct G as [gvs G]
end.

Ltac s_isFinialState__dse_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal := 
  destruct cfg2 as [S2 [los2 nts2] gl2 fs2];
  destruct cfg1 as [S1 [los1 nts1] gl1 fs1];
  destruct FS1 as [[|[? ? cs1 ? ?] ES1]]; 
  destruct FS2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
    auto | congruence |
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst; inv Hstsim
  ];
  destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
  inv X; simpl;
  destruct Hstsim as [Hstsim Hstsim'];
  fold ECs_simulation in Hstsim';
  destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
  destruct cs1, cs2; try solve [
    auto |
    apply cmds_simulation_nil_inv in Hstsim; try congruence |
    inv Hfinal
  ].

Lemma s_isFinialState__dse_State_simulation_l2r: forall pinfo cfg1 FS1 cfg2
  FS2 r  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 = ret r),
  Opsem.s_isFinialState cfg2 FS2 = ret r.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__dse_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
  destruct Terminator0; auto.
    destruct ES1, ES2; try solve [auto | inv Hstsim'].
    destruct ES1, ES2; try solve [auto | inv Hstsim'].
Qed.

Lemma s_isFinialState__dse_State_simulation_l2r': forall pinfo cfg1 FS1 cfg2
  FS2 (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg1 FS1 <> None),
  Opsem.s_isFinialState cfg2 FS2 <> None.
Proof.
  intros.
  remember (Opsem.s_isFinialState cfg1 FS1) as R.
  destruct R; try congruence.
  symmetry_ctx.
  eapply s_isFinialState__dse_State_simulation_l2r in Hstsim; eauto.
  congruence.
Qed.

Lemma s_isFinialState__dse_State_simulation_None_r2l:
  forall pinfo cfg1 FS1 cfg2 FS2
  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = None),
  Opsem.s_isFinialState cfg1 FS1 = None.
Proof.
  intros.
  remember (Opsem.s_isFinialState cfg1 FS1) as R.
  destruct R; try congruence.
  contradict Hfinal.
  eapply s_isFinialState__dse_State_simulation_l2r' in Hstsim; eauto.
    congruence.
Qed.

Lemma not_removable_State_inv: forall pinfo St,
  ~ removable_State pinfo St ->
  match St with
  | {| Opsem.ECS := {| Opsem.CurFunction := F;
                       Opsem.CurBB := _;
                       Opsem.CurCmds := c :: _;
                       Opsem.Terminator := _;
                       Opsem.Locals := _;
                       Opsem.Allocas := _ |} :: _;
       Opsem.Mem := Mem |} => PI_f pinfo = F -> 
                              store_in_cmd (PI_id pinfo) c = false
  | _ => True
  end.
Proof.
  intros.
  destruct St; auto.
  destruct ECS; auto.
  destruct e; auto.
  destruct CurCmds; auto.
  simpl in H.
  destruct c; try tauto.
  destruct v0; try tauto.
  intros.
  destruct (fdef_dec (PI_f pinfo) CurFunction); try congruence.
  simpl.
  destruct (id_dec (PI_id pinfo) i1); subst; try tauto. 
  destruct (id_dec i1 (PI_id pinfo)); subst; tauto.
Qed.

Lemma s_isFinialState__dse_State_simulation_r2l':
  forall pinfo cfg1 FS1 cfg2 FS2 r
  (Hnrem: ~removable_State pinfo FS1) 
  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r),
  Opsem.s_isFinialState cfg1 FS1 = ret r.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  s_isFinialState__dse_State_simulation cfg1 cfg2 FS1 FS2 Hstsim Hfinal.
    destruct Terminator0; auto.
      destruct ES1, ES2; try solve [auto | inv Hstsim'].
      destruct ES1, ES2; try solve [auto | inv Hstsim'].

   apply not_removable_State_inv in Hnrem.
   apply cmds_simulation_nelim_cons_inv in Hstsim; auto. 
   destruct Hstsim as [cs2' [J1 Hstsim]]; congruence.
Qed.

Lemma split_cmds_by_P: forall P (cs:cmds),
  exists cs1, exists cs2, 
    cs = cs1 ++ cs2 /\
    List.Forall (fun c => P c = true) cs1 /\
    match cs2 with 
    | nil => True
    | c2::_ => P c2 = false
    end.
Proof.
  induction cs.
    exists nil. exists nil. auto.

    destruct IHcs as [cs1 [cs2 [J1 [J2 J3]]]]; subst.
    remember (P a) as R.
    destruct R.
      exists (a::cs1). exists cs2.
      simpl_env.
      split; auto.
      split; auto.
        simpl. constructor; auto.
     
      exists nil. exists (a::cs1++cs2).
      split; auto.
Qed.

Fixpoint removable_cmds pinfo f b cs1 cs2 tmn ES1 : Prop :=
match cs1 with
| nil => True
| c1::cs1' =>
    (forall lc' als' Mem',
    removable_State pinfo
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f;
                        Opsem.CurBB := b;
                        Opsem.CurCmds := c1::cs1'++cs2;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc';
                        Opsem.Allocas := als' |} :: ES1;
           Opsem.Mem := Mem' |}) /\
    removable_cmds pinfo f b cs1' cs2 tmn ES1
end.

Lemma removable_cmds_intro: forall pinfo tmn ES1 b cs2 cs1
  (J2 : Forall (fun c : cmd => store_in_cmd (PI_id pinfo) c = true) cs1),
  removable_cmds pinfo (PI_f pinfo) b cs1 cs2 tmn ES1.
Proof.
  induction 1; simpl; auto.
    split; auto.
      intros.
      destruct x; tinv H.
      destruct v0; tinv H.
      simpl in H.
      destruct_if.
      destruct_if.
      destruct (id_dec i1 (PI_id pinfo)); auto. inv H.
Qed.

Lemma removable_State__non_removable_State: forall pinfo f b tmn ES1 c cs1 lc 
  als Mem
  (Hrem : removable_State pinfo
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f;
                        Opsem.CurBB := b;
                        Opsem.CurCmds := c :: cs1;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: ES1;
           Opsem.Mem := Mem |}),
  exists cs11, exists cs12,
    c :: cs1 = cs11 ++ cs12 /\
    removable_cmds pinfo f b cs11 cs12 tmn ES1 /\
    forall lc' als' Mem',
    ~ removable_State pinfo
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f;
                        Opsem.CurBB := b;
                        Opsem.CurCmds := cs12;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc';
                        Opsem.Allocas := als' |} :: ES1;
           Opsem.Mem := Mem' |}.
Proof.
  simpl. intros.
  destruct (split_cmds_by_P (store_in_cmd (PI_id pinfo)) cs1)
    as [cs11 [cs12 [J1 [J2 J3]]]]; subst.
  exists (c::cs11). exists cs12.
  destruct c; try tauto.
  destruct v0; try tauto.
  destruct_if; try tauto.
  destruct_if; try tauto.
  split; auto.
  split.
    apply removable_cmds_intro.
    constructor; simpl; auto.
      destruct (id_dec (PI_id pinfo) (PI_id pinfo)); auto.

    intros.
    destruct cs12; auto.
    destruct c; auto.
    destruct v1; auto.
    simpl in J3.
    destruct_if; auto.
    destruct (id_dec (PI_id pinfo) (PI_id pinfo)); auto.
      inv J3.
Qed.

Lemma removable_State__isnt__final: forall pinfo cfg St
  (Hrm: removable_State pinfo St),
  Opsem.s_isFinialState cfg St = None.
Proof.
  intros.
  destruct St as [Es Mem].
  destruct cfg.
  destruct Es as [|[] Es]; tinv Hrm.
  simpl in *.
  destruct CurCmds; tauto.
Qed.

Lemma dse_removable_cmds : forall maxb pinfo Cfg1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) (Hle: 0 <= maxb)
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfcfg: OpsemPP.wf_Config Cfg1) 
  f1 b1 cs12 lc1 tmn1 als1 ES1 cs11 
  St1 (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hrm: removable_cmds pinfo f1 b1 cs11 cs12 tmn1 ES1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1)
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hsim: State_simulation pinfo Cfg1 St1 Cfg2 St2) 
  (Hok: ~ sop_goeswrong Cfg1 St1) Mem1
  (Heq1: St1 = {|Opsem.ECS := {|
                        Opsem.CurFunction := f1;
                        Opsem.CurBB := b1;
                        Opsem.CurCmds := cs11++cs12;
                        Opsem.Terminator := tmn1;
                        Opsem.Locals := lc1;
                        Opsem.Allocas := als1 |} :: ES1;
                 Opsem.Mem := Mem1 |}),
  exists Mem1', 
    Opsem.sop_star Cfg1 St1 
     {|Opsem.ECS := {|  Opsem.CurFunction := f1;
                        Opsem.CurBB := b1;
                        Opsem.CurCmds := cs12;
                        Opsem.Terminator := tmn1;
                        Opsem.Locals := lc1;
                        Opsem.Allocas := als1 |} :: ES1;
       Opsem.Mem := Mem1' |} E0 /\
   State_simulation pinfo Cfg1
     {|Opsem.ECS := {|  Opsem.CurFunction := f1;
                        Opsem.CurBB := b1;
                        Opsem.CurCmds := cs12;
                        Opsem.Terminator := tmn1;
                        Opsem.Locals := lc1;
                        Opsem.Allocas := als1 |} :: ES1;
       Opsem.Mem := Mem1' |} Cfg2 St2.
Proof.
  induction cs11; intros; subst.
    exists Mem1. split; auto.

    destruct Hrm as [Hrm1 Hrm2].
    assert (Opsem.s_isFinialState Cfg1 
      {|Opsem.ECS := {|
                    Opsem.CurFunction := f1;
                    Opsem.CurBB := b1;
                    Opsem.CurCmds := (a :: cs11) ++ cs12;
                    Opsem.Terminator := tmn1;
                    Opsem.Locals := lc1;
                    Opsem.Allocas := als1 |} :: ES1;
        Opsem.Mem := Mem1 |} = None) as Hnfinal.
    eapply removable_State__isnt__final; eauto.

    eapply dse_is_sim in Hsim; eauto.
    destruct Hsim as [Hsim _].
    assert (J:=Hwfpp).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]]; try congruence.
      SSCase "step".
      assert (Hop1':=Hop1).
      apply_clear Hsim in Hop1'; auto.
      destruct Hop1' as [J1 J2]; subst.
      assert (Hwfpp':=Hop1).
      apply OpsemPP.preservation in Hwfpp'; auto.     
      assert (Hprom':=Hop1).
      eapply Promotability.preservation in Hprom'; eauto.     
      assert (Hpalloca':=Hop1).
      eapply palloca_props.preservation in Hpalloca'; eauto.     
      assert (exists m, IS1' =
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := f1;
                        Opsem.CurBB := b1;
                        Opsem.CurCmds := cs11 ++ cs12;
                        Opsem.Terminator := tmn1;
                        Opsem.Locals := lc1;
                        Opsem.Allocas := als1 |} :: ES1;
           Opsem.Mem := m |}) as Heq.
        assert (K:=Hrm1 nil nil Mem1).
        simpl in K.
        destruct a; try tauto.
        inv Hop1. eauto.
      destruct Heq as [m Heq]; subst.
      eapply_clear IHcs11 in J1; eauto using sop_goeswrong__step.
      destruct J1 as [Mem1' [J1 J2]].
      exists Mem1'.
      split; auto.
        rewrite <- E0_left. econstructor; eauto.
     
      SSCase "stuck".
      clear - Hundef1 Hok Hnfinal.
      apply undefined_state__stuck' in Hundef1.
      contradict Hok.
      exists {|Opsem.ECS := {|
                  Opsem.CurFunction := f1;
                  Opsem.CurBB := b1;
                  Opsem.CurCmds := (a::cs11) ++ cs12;
                  Opsem.Terminator := tmn1;
                  Opsem.Locals := lc1;
                  Opsem.Allocas := als1 |} :: ES1;
               Opsem.Mem := Mem1|}.
      exists E0.
      split; auto.
Qed.

Lemma s_isFinialState__dse_State_simulation_r2l:
  forall pinfo cfg1 FS1 cfg2 FS2 r maxb
  (Hwfpi: WF_PhiInfo pinfo) (Hle: 0 <= maxb)
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) 
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 FS1)
  (Hpalloca: palloca_props.wf_State pinfo FS1)
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r)
  (Hok: ~ sop_goeswrong cfg1 FS1),
  exists FS1', 
    Opsem.sop_star cfg1 FS1 FS1' E0 /\
    State_simulation pinfo cfg1 FS1' cfg2 FS2 /\
    Opsem.s_isFinialState cfg1 FS1' = ret r.
Proof.
  intros.
  destruct (removable_State_dec pinfo FS1) as [Hrem | Hnrem].
Case "removable".
    assert (G:=Hstsim).
    destruct cfg2 as [S2 [los2 nts2] gl2 fs2];
    destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
    destruct FS1 as [[|[? ? cs1 ? ?] ES1]];
    destruct FS2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
      auto |
      destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst; inv Hstsim |
      inv Hrem
    ].
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X; simpl;
    destruct Hstsim as [Hstsim Hstsim'];
    fold ECs_simulation in Hstsim'.
    destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
    destruct cs1, cs2; try solve [
      auto |
      apply cmds_simulation_nil_inv in Hstsim; try congruence |
      inv Hfinal |
      inv Hrem
    ].
    apply removable_State__non_removable_State in Hrem.
    destruct Hrem as [cs11 [cs12 [J1 [J2 J3]]]].
    rewrite J1 in *.
    eapply dse_removable_cmds in G; eauto.
    destruct G as [Mem1' [G1 G2]].
    exists 
       {|Opsem.ECS := {|
                      Opsem.CurFunction := CurFunction;
                      Opsem.CurBB := CurBB;
                      Opsem.CurCmds := cs12;
                      Opsem.Terminator := Terminator0;
                      Opsem.Locals := Locals0;
                      Opsem.Allocas := Allocas0 |} :: ES1;
         Opsem.Mem := Mem1' |}.
    split; auto.
      split.
        unfold State_simulation in G2. auto.
        eapply s_isFinialState__dse_State_simulation_r2l' in G2; eauto.

Case "unremovable".
    assert (J:=Hstsim).
    eapply s_isFinialState__dse_State_simulation_r2l' in Hstsim; eauto.
Qed.

Lemma cmds_simulation_nil_inv' : forall (pinfo : PhiInfo) 
  (f1 : fdef) (cs1 : list cmd) b1 tmn1 lc1 als1 ECS Mem1
  (Hnrem : ~
          removable_State pinfo
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := f1;
                         Opsem.CurBB := b1;
                         Opsem.CurCmds := cs1;
                         Opsem.Terminator := tmn1;
                         Opsem.Locals := lc1;
                         Opsem.Allocas := als1 |} :: ECS;
            Opsem.Mem := Mem1 |}),
  cmds_simulation pinfo f1 cs1 nil -> cs1 = nil.
Proof.
  simpl.
  unfold cmds_simulation. intros.
  destruct_if; auto.
  destruct cs1; auto.
  simpl in *.
  destruct c; try congruence.
  destruct v0; try congruence.
  destruct_if; try tauto.
Qed.

Lemma cmds_simulation_cons_inv' : forall (pinfo : PhiInfo) 
  (f1 : fdef) b1 lc1 cs tmn1 als1 c cs2 ECS Mem1
  (Hnrem : ~
          removable_State pinfo
            {|
            Opsem.ECS := {|
                         Opsem.CurFunction := f1;
                         Opsem.CurBB := b1;
                         Opsem.CurCmds := cs;
                         Opsem.Terminator := tmn1;
                         Opsem.Locals := lc1;
                         Opsem.Allocas := als1 |} :: ECS;
            Opsem.Mem := Mem1 |}),
  cmds_simulation pinfo f1 cs (c::cs2) -> 
   exists cs1, 
     cs = c::cs1 /\
     cmds_simulation pinfo f1 cs1 cs2.
Proof.
  simpl.
  unfold cmds_simulation. intros.
  destruct_if; eauto.
  destruct cs; tinv H1.
  simpl in *.
  destruct c0; inv H1; eauto.
  destruct v0; inv H0; eauto.
  destruct_if; try tauto. eauto.
Qed.

Ltac undefined_state__State_simulation_r2l_tac1 :=
  match goal with
  | Hstsim: State_simulation _ _ ?St1 _ ?St2 |- _ =>
    destruct St2 as [[|[? ? [|CurCmds] [] ?] [|[]]] ?]; try tauto;
    destruct CurCmds; try tauto;
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X;
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [Hstsim Hstsim'];
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
    destruct Hstsim' as [Hstsim' _];
    destruct Hstsim' as [? [? [? [? [? [? [? Hstsim']]]]]]]; subst;
   simpl
  end.

Ltac undefined_state__State_simulation_r2l_tac3 :=
  match goal with
  | Hstsim: State_simulation _ _ ?St1 _ ?St2 |- _ =>
    destruct St2 as [[|[? [? ? ? tmn] CurCmds tmn' ?] ?] ?]; try tauto;
    destruct tmn; try tauto;
    destruct CurCmds; try tauto;
    destruct tmn'; try tauto;
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? H3]]]]]; subst;
    inv X;
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [Hstsim _];
    destruct Hstsim as [? [Htmn [? [? [H8 [? [? Hstsim]]]]]]]; subst;
    destruct H8 as [l5 [ps5 [cs5 EQ]]]; subst
  end.

Ltac undefined_state__State_simulation_r2l_tac41 :=
  match goal with
  | Hstsim: State_simulation _ _ ?St1 ?cfg2 ?St2 |- _ =>
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X;
    destruct ECS as [|[? ? ? ? Locals0] ECS]; try tauto;
    destruct Hstsim as [Hstsim _];
    destruct Hstsim as [? [? [? [? [H4 [H5 [? Hstsim]]]]]]]; subst
  end. 

Ltac undefined_state__d_State_simulation_r2l_tac43 := 
      match goal with
      | Hstsim: cmds_simulation _ _ _ (_::_) |- _ =>
      eapply cmds_simulation_cons_inv' in Hstsim; eauto; subst;
      destruct Hstsim as [c1' [J2 J3]]; subst
     end.

Lemma stacked_frame__unremovable: forall cfg EC1 EC2 ECS Mem0 pinfo
  (HBinF: match Opsem.CurBB EC1 with 
   | block_intro _ _ _ (insn_return _ _ _) => True
   | block_intro _ _ _ (insn_return_void _) => True
   | _ => False
   end)
  (Hwfpp1 : OpsemPP.wf_State cfg
             {| Opsem.ECS := EC1 :: EC2 :: ECS; Opsem.Mem := Mem0 |}),
  ~ removable_State pinfo
     {| Opsem.ECS := EC2 :: ECS; Opsem.Mem := Mem0 |}.
Proof.
  intros.
  destruct EC1, EC2; simpl in *. destruct cfg. destruct CurTargetData.
  destruct Hwfpp1 as 
     [_ [[_ [HbInF1 [_ [_ [_ _]]]]] [_ Hiscall]]].
  apply Hiscall in HbInF1.
  destruct CurBB as [? ? ? []]; tinv HBinF.
    destruct CurCmds0 as [|[]]; tinv HbInF1. tauto.
    destruct CurCmds0 as [|[]]; tinv HbInF1. tauto.
Qed.

Lemma mem_simulation__malloc_l2r': forall (pinfo : PhiInfo) TD ECs M1 M2
  (Hmsim : mem_simulation pinfo TD ECs M1 M2)
  (Mem'0 : mem) (tsz0 : sz) align0 gn mb M1'
  (H2 : malloc TD M1 tsz0 gn align0 = ret (M1', mb)),
  exists M2',
     malloc TD M2 tsz0 gn align0 = ret (M2', mb).
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmim3 Hmsim2]].
  unfold dse_mem_inj in *.
  inv_mbind. 
  destruct (@no_alias_head_tail_ex pinfo ECs) as [ombs J].
  apply_clear Hmsim2 in J.
  apply malloc_inv in H2. destruct H2 as [n0 [J1 [J2 J3]]].
  unfold malloc. fill_ctxhole.
  destruct_if; try congruence.
  remember (Mem.alloc M2 0 (Size.to_Z tsz0 * n0)) as R.
  destruct R as [M2' mb2].
  exists M2'.
  apply Mem.alloc_result in J3.
  symmetry in HeqR1.
  apply Mem.alloc_result in HeqR1.
  f_equal. f_equal.
  congruence.
Qed.

Lemma mem_simulation__mload_l2r: forall td gv M1 mp t align0 M2 ECs pinfo
  (H1 : mload td M1 mp t align0 = ret gv)
  (Hmsim : mem_simulation pinfo td ECs M1 M2),
  exists gv0, mload td M2 mp t align0 = ret gv0.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  apply mload_inv in H1.
  destruct H1 as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold dse_mem_inj in Hmsim2.
  inv_mbind. 
  destruct (@no_alias_head_tail_ex pinfo ECs) as [ombs J].
  apply_clear Hmsim2 in J.
  unfold mload. repeat fill_ctxhole. simpl.
  eapply SASmsim.mload_aux_inj_ex with (b2:=b)(delta:=0) in J; eauto.
  replace (Int.signed 31 ofs + 0) with (Int.signed 31 ofs)  in J by omega.
  destruct J as [gv2 J]; eauto.
Qed.

Lemma mem_simulation__mstore_l2r: forall td M1 mp2 t gv1 align0 M1' M2 ECs
  (H3 : mstore td M1 mp2 t gv1 align0 = ret M1') pinfo
  (Hmsim : mem_simulation pinfo td ECs M1 M2),
  exists M2', 
    mstore td M2 mp2 t gv1 align0 = ret M2'.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  apply mstore_inversion in H3.
  destruct H3 as [b [ofs [cm [J1 J2]]]]; subst.
  unfold dse_mem_inj in *.
  inv_mbind.
  destruct (@no_alias_head_tail_ex pinfo ECs) as [ombs J].
  apply_clear Hmsim2 in J.
  unfold mstore. simpl. 
  eapply SASmsim.mstore_aux_inject_id_mapped_inj in J; eauto.
  destruct J as [gv2 [J1 J4]]; eauto.
Qed.

Lemma undefined_state__dse_State_simulation_r2l': forall pinfo cfg1 St1 cfg2
  St2 
  (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (Hstsim : State_simulation pinfo cfg1 St1 cfg2 St2)
  (Hnrem: ~removable_State pinfo St1) 
  (Hundef: OpsemPP.undefined_state cfg2 St2),
  OpsemPP.undefined_state cfg1 St1.
Proof.
  intros.
  unfold OpsemPP.undefined_state in Hundef.
  destruct cfg2 as [S2 [los2 nts2] gl2 fs2].
  destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
  repeat match goal with
  | Hundef : _ \/ _ |- _ => destruct Hundef as [Hundef | Hundef]
  end.
  Case "1".
    undefined_state__State_simulation_r2l_tac1.
    eapply cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    assert (Hnrem' : ~
          removable_State pinfo
            {|
            Opsem.ECS := {|
                            Opsem.CurFunction := CurFunction2;
                            Opsem.CurBB := CurBB2;
                            Opsem.CurCmds := CurCmds1;
                            Opsem.Terminator := Terminator;
                            Opsem.Locals := Locals0;
                            Opsem.Allocas := Allocas0 |} :: ECS;
            Opsem.Mem := Mem0 |}).
      clear - Hwfpp1 H4.
      destruct H4 as [l5 [ps5 [cs5 H4]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto.
    eapply cmds_simulation_cons_inv' in Hnrem'; eauto.
    destruct Hnrem' as [cs1' [J1 J3]]; subst.
    left. 
    remember (free_allocas (los2, nts2) Mem0 Allocas) as R.
    destruct R; auto.
    symmetry in HeqR. simpl in H2.
    eapply mem_simulation__free_allocas_l2r in HeqR; eauto.
    destruct HeqR as [M2' [Hfree [Hmsim']]].
    congruence.

  Case "2".
    undefined_state__State_simulation_r2l_tac1.
    eapply cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    assert (Hnrem' : ~
          removable_State pinfo
            {|
            Opsem.ECS := {|
                            Opsem.CurFunction := CurFunction2;
                            Opsem.CurBB := CurBB2;
                            Opsem.CurCmds := CurCmds1;
                            Opsem.Terminator := Terminator;
                            Opsem.Locals := Locals0;
                            Opsem.Allocas := Allocas0 |} :: ECS;
            Opsem.Mem := Mem0 |}).
      clear - Hwfpp1 H4.
      destruct H4 as [l5 [ps5 [cs5 H4]]]; subst.
      eapply stacked_frame__unremovable; eauto; simpl; auto.
    eapply cmds_simulation_cons_inv' in Hnrem'; eauto.
    destruct Hnrem' as [cs1' [J1 J3]]; subst.
    right. left. 
    destruct Hundef as [Hundef | Hundef]; auto.
    left.
    remember (free_allocas (los2, nts2) Mem0 Allocas) as R.
    destruct R; auto.
    symmetry in HeqR. simpl in H2.
    eapply mem_simulation__free_allocas_l2r in HeqR; eauto.
    destruct HeqR as [M2' [Hfree [Hmsim']]].
    congruence.

  Case "3".
    undefined_state__State_simulation_r2l_tac3.
    eapply cmds_simulation_nil_inv' in Hstsim; eauto; subst.
    right. right. left. auto.

  Case "4".
    right; right; right; left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' Locals] ?] ?]; try solve [
      tauto |
      inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind;
      undefined_state__State_simulation_r2l_tac41;
      undefined_state__d_State_simulation_r2l_tac43;
      repeat fill_ctxhole; exists gn; split; auto;
      remember (malloc (los2, nts2) Mem0 s gn a) as R;
      destruct R as [[]|]; auto;
      symmetry in HeqR2;
      eapply mem_simulation__malloc_l2r' in HeqR2; eauto 2;
      destruct HeqR2 as [Mem2' J4]; congruence
    ].

  Case "5".
    right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43.
    repeat fill_ctxhole; exists gn. split; auto.
    remember (free (los2, nts2) Mem0 gn) as R.
    destruct R; auto.
    symmetry in HeqR1. simpl in H2.
    eapply mem_simulation__free_l2r' in HeqR1; eauto.
    destruct HeqR1 as [M2' Hfree].
    congruence.
   
  Case "6".
    right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gvs [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43. 
    repeat fill_ctxhole; exists gvs. split; auto.
    remember (mload (los2, nts2) Mem0 gvs t a) as R.
    destruct R; auto.
    symmetry in HeqR1. simpl in H2.
    eapply mem_simulation__mload_l2r in HeqR1; eauto.
    destruct HeqR1 as [gv2 Hload].
    congruence.

  Case "7".
    right. right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gv [mgv [EQ1 [EQ2 Hundef]]]]; 
      inv EQ1; inv EQ2; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__d_State_simulation_r2l_tac43. 
    repeat fill_ctxhole; exists gv; exists mgv.
    split; auto.
    remember (mstore (los2, nts2) Mem0 mgv t gv a) as R.
    destruct R; auto.
    symmetry in HeqR2. simpl in H2.
    eapply mem_simulation__mstore_l2r in HeqR2; eauto.
    destruct HeqR2 as [M2' Hstore].
    congruence.

  Case "8".
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    right; right; right; right. right. right. right.
    undefined_state__State_simulation_r2l_tac41.
    inv_mbind.
    destruct Hundef as [fptr [EQ Hundef]]; inv EQ.
    inv_mbind.
    eapply cmds_simulation_cons_inv' in Hstsim; subst; eauto.
    destruct Hstsim as [cs2' [J1 J2]]; subst.
    repeat fill_ctxhole.
    exists fptr. split; auto.
    remember (OpsemAux.lookupExFdecViaPtr gl2 FunTable fptr) as R.
    destruct R as [[[]]|].
      inv_mbind.
      destruct Hundef as [gvs0 [EQ' Hundef]].
      dgvs_instantiate_inv.
      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_r2l; eauto.
      simpl.
      exists l1. split; auto.
      remember (callExternalOrIntrinsics (los2, nts2) fs2 Mem0 i1 t0 
          (args2Typs a) d l1) as R.
      destruct R as [[[]]|]; auto.
      remember (Opsem.exCallUpdateLocals (los2, nts2) t n i0 o Locals) as R.
      destruct R; auto.
      eapply callExternalFunction__mem_simulation_l2r in H2; eauto.
        destruct H2 as [M2' [oresult2 [tr2 [W1 [W2 [W3 W4]]]]]]; subst.
        rewrite W1 in Hundef. rewrite <- HeqR4 in Hundef. auto.

      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_None_r2l; eauto.
Qed.

Lemma undefined_state__dse_State_simulation_r2l: forall pinfo cfg1 St1 cfg2
  St2 (Hwfpi: WF_PhiInfo pinfo) maxb (Hle: 0 <= maxb)
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) 
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 St1)
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (Hstsim : State_simulation pinfo cfg1 St1 cfg2 St2)
  (Hundef: OpsemPP.undefined_state cfg2 St2)
  (Hok: ~ sop_goeswrong cfg1 St1),
  exists St1', 
    Opsem.sop_star cfg1 St1 St1' E0 /\
    State_simulation pinfo cfg1 St1' cfg2 St2 /\
    OpsemPP.undefined_state cfg1 St1'.
Proof.
  intros.
  destruct (removable_State_dec pinfo St1) as [Hrem | Hnrem].
Case "removable".
    assert (G:=Hstsim).
    destruct cfg2 as [S2 [los2 nts2] gl2 fs2];
    destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
    destruct St1 as [[|[? ? cs1 ? ?] ES1]];
    destruct St2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
      auto |
      destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst; inv Hstsim |
      inv Hrem
    ].
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X; simpl;
    destruct Hstsim as [Hstsim Hstsim'];
    fold ECs_simulation in Hstsim'.
    destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst.
    destruct cs1; try solve [
      auto |
      apply cmds_simulation_nil_inv in Hstsim; try congruence |
      inv Hrem
    ].
    apply removable_State__non_removable_State in Hrem.
    destruct Hrem as [cs11 [cs12 [J1 [J2 J3]]]].
    rewrite J1 in *.
    eapply dse_removable_cmds in G; eauto.
    destruct G as [Mem1' [G1 G2]].
    exists 
       {|Opsem.ECS := {|
                      Opsem.CurFunction := CurFunction;
                      Opsem.CurBB := CurBB;
                      Opsem.CurCmds := cs12;
                      Opsem.Terminator := Terminator0;
                      Opsem.Locals := Locals0;
                      Opsem.Allocas := Allocas0 |} :: ES1;
         Opsem.Mem := Mem1' |}.
    split; auto.
      split.
        unfold State_simulation in G2. auto.
        eapply undefined_state__dse_State_simulation_r2l' in G2; eauto.
          eapply OpsemPP.preservation_star; eauto.

Case "unremovable".
    assert (J:=Hstsim).
    eapply undefined_state__dse_State_simulation_r2l' in Hstsim; eauto.
Qed.

Lemma sop_star__dse_State_simulation: forall pinfo  cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) (Hwfcfg: OpsemPP.wf_Config cfg1)
  (Hwfpp: OpsemPP.wf_State cfg1 IS1)
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hstsim : State_simulation pinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\
    State_simulation pinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent cfg1.
  generalize dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    assert (forall (Hfinal1: Opsem.s_isFinialState cfg1 IS1 <> merror),
            exists FS1 : Opsem.State,
              Opsem.sop_star cfg1 IS1 FS1 (tr1 ** tr2) /\
              State_simulation pinfo cfg1 FS1 cfg2 state3) as W.
      intros.
      apply s_isFinialState__dse_State_simulation_l2r' in Hstsim; auto.
      contradict H; eauto using s_isFinialState__stuck.
    assert (J:=Hwfpp).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]]; auto.
      assert (OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
        apply OpsemPP.preservation in Hop1; auto.
      assert (Promotability.wf_State maxb pinfo cfg1 IS1') as Hnoalias'.
        eapply Promotability.preservation in Hop1; eauto.
      assert (palloca_props.wf_State pinfo IS1') as Hpalloca'.
        eapply palloca_props.preservation in Hop1; eauto.
      eapply dse_is_sim in Hstsim; eauto.
      destruct Hstsim as [Hstsim1 Hstsim2].
      destruct (@removable_State_dec pinfo IS1) as [Hrm | Hnrm].
        eapply Hstsim1 in Hrm; eauto.
        destruct Hrm as [Hstsim EQ]; subst.
        admit. (* we should do induction on the measure of State_simulation *)

        eapply Hstsim2 in Hnrm; eauto.
        destruct Hnrm as [Hstsim EQ]; subst.
        eapply IHHopstar in Hstsim;
          eauto using sop_goeswrong__step, (@OpsemPP.preservation DGVs).
        destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
        exists FS1. split; eauto.

      apply undefined_state__stuck' in Hundef1.
      remember (Opsem.s_isFinialState cfg1 IS1) as R.
      destruct R.
        apply W; congruence.
        contradict Hok. exists IS1. exists E0. split; auto.
Qed.

Lemma sop_div__dse_State_simulation: forall pinfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1)
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hpalloca: palloca_props.wf_State pinfo IS1)
  (Hstsim : State_simulation pinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Admitted. (* sop div *)

Lemma dse_wfS: forall (pinfo:PhiInfo) f pid Ps1 Ps2 los nts
  (Heq1: PI_id pinfo = pid) (Heq2: PI_f pinfo = f)
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hnld: load_in_fdef pid f = false),
  wf_system
    [module_intro los nts
      (Ps1 ++  product_fdef (elim_dead_st_fdef pid f) :: Ps2)].
Proof.
Admitted. (* prev WF *)

Lemma dse_sim: forall (pinfo:PhiInfo) f pid Ps1 Ps2 los nts main
  VarArgs (Heq1: PI_id pinfo = pid) (Heq2: PI_f pinfo = f)
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hok: defined_program [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
          main VarArgs)
  (Hnld: load_in_fdef pid f = false),
  program_sim
    [module_intro los nts
      (Ps1 ++  product_fdef (elim_dead_st_fdef pid f) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Proof.
  intros. subst.
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation pinfo
    [module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2)]
    [module_intro los nts
      (Ps1 ++ product_fdef (elim_dead_st_fdef (PI_id pinfo) (PI_f pinfo))
       :: Ps2)]) as Hssim.
    constructor; auto.
    repeat split; auto.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    unfold TopSim.products_simulation. simpl. unfold system_simulation.
    apply uniq_products_simulation; auto.

Ltac dse_sim_init :=
match goal with
| H: Opsem.s_genInitState [module_intro ?los ?nts _] _ _ _ = Some (?cfg, ?IS), 
  pinfo: PhiInfo |- _ =>
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg IS) as Hwfst';
      try solve [eapply s_genInitState__opsem_wf in H; eauto using dse_wfS];
    eapply s_genInitState__dse_State_simulation in H; eauto;
    destruct H as [cfg1 [IS1 [Hinit1 Hstsim]]];
    assert (OpsemPP.wf_Config cfg1/\ OpsemPP.wf_State cfg1 IS1) as Hwfst;
      try solve [eapply s_genInitState__opsem_wf; eauto];
    assert (exists maxb,
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom;
      try solve [eapply Promotability.s_genInitState__wf_globals_promotable; eauto];
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]];
    assert (palloca_props.wf_State pinfo IS1) as Hpalloca;
      try solve [eapply palloca_props.s_genInitState__palloca; eauto]
end.

Ltac dse_sim_end :=
match goal with
| Hstsim' : State_simulation ?pinfo ?cfg1 ?FS1 ?cfg ?FS,
  Hopstar1 : Opsem.sop_star ?cfg1 _ ?FS1 _,
  Hwfg: MemProps.wf_globals ?maxb _  |- _ =>
    assert (OpsemPP.wf_State cfg FS) as Hwfst''; 
      try solve [eapply OpsemPP.preservation_star; eauto; try tauto];
    assert (OpsemPP.wf_State cfg1 FS1) as Hwfst1'';
      try solve [eapply OpsemPP.preservation_star; eauto; try tauto];
    assert (palloca_props.wf_State pinfo FS1); try solve 
      [eapply palloca_props.preservation_star in Hopstar1; eauto; try tauto];
    assert (Promotability.wf_State maxb pinfo cfg1 FS1) as Hprom'; try solve [
      eapply Promotability.preservation_star in Hopstar1; eauto; try tauto
    ]
end.

  constructor; auto.
    intros tr t Hconv.
    inv Hconv.
    dse_sim_init.
    eapply sop_star__dse_State_simulation in Hstsim;
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    dse_sim_end.
    eapply s_isFinialState__dse_State_simulation_r2l in Hstsim';
      eauto using sop_goeswrong__star, defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim' as [FS1' [Hopstar1' [Hstsim'' Hfinal]]].
    assert (Opsem.sop_star cfg1 IS1 FS1' tr) as Hopstar1''.
      rewrite <- E0_right.
      eapply OpsemProps.sop_star_trans; eauto.
    econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    dse_sim_init.
    eapply sop_div__dse_State_simulation in Hstsim; try solve [eauto | tauto].
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.

    intros tr t Hgowrong.
    inv Hgowrong.
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg t) as HwfSt.
      eapply s_genInitState__opsem_wf in H; eauto using dse_wfS.
      destruct H as [Hcfg2 HwfSt2].
      apply OpsemPP.preservation_star in H0; auto.
    assert (OpsemPP.undefined_state cfg t) as Hundef.
      apply stuck__undefined_state in H2; try solve [auto | tauto].
    dse_sim_init.
    eapply sop_star__dse_State_simulation in Hstsim; 
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    dse_sim_end.
    assert (Hundef':=Hundef).
    eapply undefined_state__dse_State_simulation_r2l in Hundef'; 
      try solve [eauto using sop_goeswrong__star, defined_program__doesnt__go_wrong | tauto].
    destruct Hundef' as [FS1' [Hopstar2 [Hsim Hundef']]].
    assert (Opsem.s_isFinialState cfg1 FS1' = merror) as Hfinal'.
      apply OpsemPP.preservation_star in Hopstar2; auto; try tauto.
      eapply s_isFinialState__dse_State_simulation_None_r2l in H2; 
        try solve [eauto | tauto].
    apply undefined_state__stuck' in Hundef'.
    exists (tr**E0). exists FS1'.
    econstructor; eauto using (@OpsemProps.sop_star_trans DGVs).   
Qed.

Lemma dse_wfPI: forall (pinfo:PhiInfo) f pid Ps1 Ps2 los nts
  (Heq1: PI_id pinfo = pid) (Heq2: PI_f pinfo = f)
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hnld: load_in_fdef pid f = false),
  WF_PhiInfo (update_pinfo pinfo (elim_dead_st_fdef pid f)).
Proof.
Admitted. (* prev WF *)

Lemma elim_dead_st_fdef_successors : forall f id',
  successors f = successors (elim_dead_st_fdef id' f).
Admitted. (* prev WF *)

Lemma elim_dead_st_fdef_reachablity_analysis : forall f id',
  dtree.reachablity_analysis f =
    dtree.reachablity_analysis (elim_dead_st_fdef id' f).
Admitted. (* prev WF *)
