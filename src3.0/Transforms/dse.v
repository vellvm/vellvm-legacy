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
Require Import trans_tactic.

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

Definition products_simulation (pinfo: PhiInfo) Ps1 Ps2 : Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation pinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) S1 S2 : Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation pinfo Ps1 Ps2
   end) S1 S2.

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

Definition no_alias_head_in_tail (pinfo:PhiInfo) ptr
  (ec0:@Opsem.ExecutionContext DGVs) : Prop :=
forall gvsa (Heq: Opsem.CurFunction ec0 = PI_f pinfo)
  (Hlkup: lookupAL _ (Opsem.Locals ec0) (PI_id pinfo) = Some gvsa),
  MemProps.no_alias ptr gvsa.

Definition no_alias_head_tail (pinfo:PhiInfo) ptr 
  (ecs':list Opsem.ExecutionContext) : Prop :=
  forall ec0 (Hin: In ec0 ecs'), no_alias_head_in_tail pinfo ptr ec0.

Definition Mem_simulation (pinfo:PhiInfo) TD (ecs1:list Opsem.ExecutionContext) 
  Mem1 Mem2 : Prop :=
Mem.nextblock Mem1 = Mem.nextblock Mem2 /\
forall ptr ty al gvs1 gvs2 
  (Hnalias: no_alias_head_tail pinfo ptr ecs1)
  (Hld1: mload TD Mem1 ptr ty al = Some gvs1)
  (Hld2: mload TD Mem2 ptr ty al = Some gvs2),
  gvs1 = gvs2.

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
    gl1 = gl2 /\ fs1 = fs2 /\ Mem_simulation pinfo TD1 ECs1 M1 M2
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
  forall pinfo ptr F B1 cs1 tmn1 lc als1 ECs B2 cs2 tmn2 als2,
  no_alias_head_tail pinfo ptr
              ({|
               Opsem.CurFunction := F;
               Opsem.CurBB := B1;
               Opsem.CurCmds := cs1;
               Opsem.Terminator := tmn1;
               Opsem.Locals := lc;
               Opsem.Allocas := als1 |} :: ECs) ->
  no_alias_head_tail pinfo ptr
              ({|
               Opsem.CurFunction := F;
               Opsem.CurBB := B2;
               Opsem.CurCmds := cs2;
               Opsem.Terminator := tmn2;
               Opsem.Locals := lc;
               Opsem.Allocas := als2 |} :: ECs).
Proof.
  unfold no_alias_head_tail. simpl in *.
  intros.
  intros.
  destruct Hin as [Hin | Hin]; subst; eauto.
  assert (no_alias_head_in_tail pinfo ptr
           {| Opsem.CurFunction := F;
              Opsem.CurBB := B1;
              Opsem.CurCmds := cs1;
              Opsem.Terminator := tmn1;
              Opsem.Locals := lc;
              Opsem.Allocas := als1 |}) as G. eauto.
  unfold no_alias_head_in_tail in *. simpl. auto.   
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

Lemma no_alias_dec: forall gvs1 gvs2,
  MemProps.no_alias gvs1 gvs2 \/ ~ MemProps.no_alias gvs1 gvs2.
Admitted.

Lemma load_free_allocas_none: forall TD M1 M2 mb als ofs m ty al
  (Hfree : free_allocas TD M1 als = ret M2)
  (Hin : In mb als),
  mload TD M2 ((Vptr mb ofs, m) :: nil) ty al = None.
Admitted.

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
  destruct (no_alias_dec ptr gvsa) as [Hnalias' | Halias]; auto.
  apply Hinscope1' in Hlkup.
  destruct Hlkup as [[[mb [EQ [Hin _]]] _] _]; subst.
  assert (Hld1':=Hld1).
  apply mload_inv in Hld1.
  destruct Hld1 as [b [ofs [m [mc [EQ [J1 Hld1]]]]]]; subst.
  rewrite Promotability.simpl_blk2GV in Halias.
  simpl in Halias.
  destruct (Z_eq_dec b mb); subst; try (contradict Halias; auto).
  erewrite load_free_allocas_none in Hld1'; eauto.
  congruence.
Qed.

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
Admitted.

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

Lemma no_alias_head_tail_update : 
  forall pinfo ptr EC1 EC2 ECs
  (EQ: Opsem.CurFunction EC1 = Opsem.CurFunction EC2)
  (Hp: forall gvsa
   (Hlkup: lookupAL (GVsT DGVs) (Opsem.Locals EC2) (PI_id pinfo) = ret gvsa),
   lookupAL (GVsT DGVs) (Opsem.Locals EC1) (PI_id pinfo) = ret gvsa)
  (Hnalias: no_alias_head_tail pinfo ptr (EC1 :: ECs)),
  no_alias_head_tail pinfo ptr (EC2 :: ECs).
Proof.
  intros.
  unfold no_alias_head_tail in *.
  intros.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; subst.
    assert (no_alias_head_in_tail pinfo ptr EC1) as J. 
      apply Hnalias; simpl; auto.
    clear Hnalias.
    unfold no_alias_head_in_tail in *. simpl in *. intros. 
    rewrite Heq in EQ.
    apply J; auto.

    apply Hnalias; simpl; auto.
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
Admitted.

Lemma mem_simulation_update_locals : 
  forall pinfo TD EC1 EC2 ECs M1 M2
  (EQ: Opsem.CurFunction EC1 = Opsem.CurFunction EC2)
  (Hp: forall gvsa
   (Hlkup: lookupAL (GVsT DGVs) (Opsem.Locals EC1) (PI_id pinfo) = ret gvsa),
   lookupAL (GVsT DGVs) (Opsem.Locals EC2) (PI_id pinfo) = ret gvsa)
  (Hmsim: Mem_simulation pinfo TD (EC1 :: ECs) M1 M2),
  Mem_simulation pinfo TD (EC2 :: ECs) M1 M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 Hmsim2].
  split; auto.
    intros.
    eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); eauto.
    eapply no_alias_head_tail_update in Hnalias; eauto; simpl; auto.
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
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
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

Lemma mstore_palloca_Mem_simulation: forall TD M1 mp2 gv1 a M1' pinfo lc2 gl2
  B1 cs1 tmn2 als2 ECs1 M2 i0 t v
  (H23: mstore TD M1 mp2 t gv1 a = ret M1')
  (H20: @Opsem.getOperandValue DGVs TD (value_id (PI_id pinfo)) lc2 gl2 =
          ret mp2)
  (Hmsim: Mem_simulation pinfo TD
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := insn_store i0 t v (value_id (PI_id pinfo)) a
                              :: cs1;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: ECs1) M1 M2),
  Mem_simulation pinfo TD
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
    eapply Hmsim2; eauto using no_alias_head_tail_irrel.
    eapply MemProps.mstore_preserves_mload_inv'; eauto.
    assert (no_alias_head_in_tail pinfo ptr 
              {| Opsem.CurFunction := PI_f pinfo;
                 Opsem.CurBB := B1;
                 Opsem.CurCmds := cs1;
                 Opsem.Terminator := tmn2;
                 Opsem.Locals := lc2;
                 Opsem.Allocas := als2 |}) as J.
      apply Hnalias; simpl; auto.
    apply MemProps.no_alias_sym.
    unfold no_alias_head_in_tail in J; eauto.
Qed.

Ltac repeat_solve :=
  repeat (match goal with
          | |- Mem_simulation _ _ _ _ _ => idtac 
          | |- _ => split; eauto 2 using cmds_at_block_tail_next
          end).


Lemma products_simulation__fdef_simulation : forall pinfo Ps1 Ps2 fid f1 f2,
  lookupFdefViaIDFromProducts Ps2 fid = Some f2 ->
  lookupFdefViaIDFromProducts Ps1 fid = Some f1 ->
  products_simulation pinfo Ps1 Ps2 ->
  fdef_simulation pinfo f1 f2.
Admitted.

Lemma lookupFdefViaPtr__simulation : forall pinfo Ps1 Ps2 fptr f1 f2 fs,
  OpsemAux.lookupFdefViaPtr Ps2 fs fptr = Some f2 ->
  products_simulation pinfo Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs fptr = Some f1 ->
  fdef_simulation pinfo f1 f2.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptr) as R2.
  destruct R2 as [fid|]; inv H1. simpl in H.
  eapply products_simulation__fdef_simulation in H0; eauto.
Qed.

Lemma fdef_simulation__entry_block_simulation: forall pinfo F1 F2 B1 B2,
  fdef_simulation pinfo F1 F2 ->
  getEntryBlock F1 = ret B1 ->
  getEntryBlock F2 = ret B2 ->
  block_simulation pinfo F1 B1 B2.
Admitted.

Lemma fdef_simulation_inv: forall pinfo fh1 fh2 bs1 bs2,
  fdef_simulation pinfo (fdef_intro fh1 bs1) (fdef_intro fh2 bs2) ->
  fh1 = fh2 /\ 
  List.Forall2 
    (fun b1 b2 => block_simulation pinfo (fdef_intro fh1 bs1) b1 b2) bs1 bs2.
Admitted.

Lemma lookupFdefViaPtr__simulation_l2r : forall pinfo Ps1 Ps2 fptr f1 fs,
  products_simulation pinfo Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs fptr = Some f1 ->
  exists f2, 
    OpsemAux.lookupFdefViaPtr Ps2 fs fptr = Some f2 /\
    fdef_simulation pinfo f1 f2.
Admitted.

Lemma lookupExFdecViaPtr__simulation_l2r : forall pinfo Ps1 Ps2 fptr f fs,
  products_simulation pinfo Ps1 Ps2 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs fptr = Some f ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs fptr = Some f.
Admitted.


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

Lemma callExternalFunction__Mem_simulation: forall pinfo TD St1 M1 M2 fid0 gvss0
  oresult1 M1' oresult2 M2' dck tr1 tr2 gl tret targs,
  Mem_simulation pinfo TD St1 M1 M2 ->
  callExternalOrIntrinsics TD gl M1 fid0 tret targs dck gvss0 = 
    ret (oresult1, tr1, M1') ->
  callExternalOrIntrinsics TD gl M2 fid0 tret targs dck gvss0 = 
    ret (oresult2, tr2, M2') ->
  oresult1 = oresult2 /\ Mem_simulation pinfo TD St1 M1' M2'.
Admitted.

Ltac dse_is_sim_common_case :=
match goal with
| Hcssim2: cmds_simulation _ _ _ _,
  Hop2: Opsem.sInsn _ _ _ _,
  Hmsim: Mem_simulation _ _ _ _ _ |- _ =>
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  repeat_solve;
    eapply mem_simulation_update_locals in Hmsim; simpl; try solve [
      eauto |
      simpl; intros;
      match goal with
      | Hlkup : lookupAL _ ?lc ?id1 = Some ?gvsa |-
        lookupAL _ (updateAddAL _ ?lc _ _ ) ?id1 = Some ?gvsa => 
        admit  (* id <> palloca *)
      end]
end.
  
Lemma dse_is_sim : forall maxb pinfo Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hsim: State_simulation pinfo Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State pinfo St1) St1' tr1 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     State_simulation pinfo Cfg1 St1' Cfg2 St2 /\ tr1 = trace_nil) /\
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
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
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
    eapply mstore_palloca_Mem_simulation in Hmsim; eauto.

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
      clear Hmsim2.
      apply no_alias_head_tail_and_cons; simpl.       
        eapply no_alias_head_in_tail__return; eauto.

        unfold Opsem.returnUpdateLocals in H1.
        inv_mbind'.
        destruct n; inv H2.
          eapply no_alias_head_tail_irrel; eauto.
          destruct t; tinv H1.
          inv_mbind'.
          eapply no_alias_head_tail_update in Hnalias; eauto; simpl; auto.
          intros.
          destruct (id_dec i0 (PI_id pinfo)); subst.
            admit. (* callid <> palloca *)
            rewrite <- lookupAL_updateAddAL_neq; auto.
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
      apply no_alias_head_tail_and_cons; simpl.       
        eapply no_alias_head_in_tail__return; eauto.
        eapply no_alias_head_tail_irrel; eauto.
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
    destruct v2 as [i0|]; auto.
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

  match goal with
  | Hpsim: products_simulation _ ?Ps ?Ps2,
    H1: OpsemAux.lookupExFdecViaPtr ?Ps _ _ = _,
    H30: OpsemAux.lookupFdefViaPtr ?Ps2 _ _ = _ |- _ =>
    clear - H30 H1 Hpsim;
    eapply lookupExFdecViaPtr__simulation_l2r in H1; eauto;
    apply OpsemAux.lookupExFdecViaPtr_inversion in H1;
    apply OpsemAux.lookupFdefViaPtr_inversion in H30;
    destruct H1 as [fn [J1 [J2 J3]]];
    destruct H30 as [fn' [J4 J5]]
  end.

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

Lemma s_genInitState__dse_State_simulation: forall pinfo S1 S2 main VarArgs cfg2 
  IS2,
  system_simulation pinfo S1 S2 ->
  Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2) ->
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo cfg1 IS1 cfg2 IS2.
Admitted.

Lemma s_isFinialState__dse_State_simulation: forall pinfo cfg1 FS1 cfg2 
  FS2 r (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: s_isFinialState cfg2 FS2 = ret r),
  s_isFinialState cfg1 FS1 = ret r.
Admitted.

Lemma opsem_s_isFinialState__dse_State_simulation: forall pinfo cfg1 FS1 cfg2 FS2
  (Hstsim : State_simulation pinfo cfg1 FS1 cfg2 FS2),
  Opsem.s_isFinialState FS1 = Opsem.s_isFinialState FS2.
Admitted.

Lemma undefined_state__dse_State_simulation: forall pinfo cfg1 St1 cfg2 
  St2 (Hstsim : State_simulation pinfo cfg1 St1 cfg2 St2),
  OpsemPP.undefined_state cfg1 St1 -> OpsemPP.undefined_state cfg2 St2.
Admitted.

Lemma sop_star__dse_State_simulation: forall pinfo  cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) (Hwfcfg: OpsemPP.wf_Config cfg1) 
  (Hwfpp: OpsemPP.wf_State cfg1 IS1)
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hstsim : State_simulation pinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\ 
    State_simulation pinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent cfg1.
  generalize dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    assert (J:=Hwfpp).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]].
      apply opsem_s_isFinialState__dse_State_simulation in Hstsim.
      rewrite Hstsim in Hfinal1.
      contradict H; eauto using s_isFinialState__stuck.

      assert (OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
        apply OpsemPP.preservation in Hop1; auto.
      assert (Promotability.wf_State maxb pinfo cfg1 IS1') as Hnoalias'.
        eapply Promotability.preservation in Hop1; eauto.
      eapply dse_is_sim in Hstsim; eauto.
      destruct Hstsim as [Hstsim1 Hstsim2].
      destruct (@removable_State_dec pinfo IS1) as [Hrm | Hnrm].
        eapply Hstsim1 in Hrm; eauto.
        destruct Hrm as [Hstsim EQ]; subst.
        admit. (* we should do induction on the measure of State_simulation *)

        eapply Hstsim2 in Hnrm; eauto.
        destruct Hnrm as [Hstsim EQ]; subst.
        eapply IHHopstar in Hstsim; eauto.
        destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
        exists FS1. split; eauto.

      eapply undefined_state__dse_State_simulation in Hstsim; eauto.
      contradict H; eauto using undefined_state__stuck.
Qed.

Lemma sop_div__dse_State_simulation: forall pinfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1)
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false) maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg1)) (Hless: 0 <= maxb)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hstsim : State_simulation pinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Admitted.
     
Lemma dse_sim: forall (pinfo:PhiInfo) f pid Ps1 Ps2 los nts main 
  VarArgs (Heq1: PI_id pinfo = pid) (Heq2: PI_f pinfo = f) 
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
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
    unfold system_simulation.
    constructor; auto.
    repeat split; auto.
    unfold products_simulation.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    apply uniq_products_simulation; auto.

  constructor.
    intros tr t Hconv.
    inv Hconv.
    eapply s_genInitState__dse_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit1 Hstsim]]]. 
    assert (OpsemPP.wf_Config cfg1/\ OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    assert (exists maxb, 
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom.
      eapply Promotability.s_genInitState__wf_globals_promotable; eauto.
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]]. 
    eapply sop_star__dse_State_simulation in Hstsim; eauto; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    eapply s_isFinialState__dse_State_simulation in Hstsim'; eauto.
    econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    eapply s_genInitState__dse_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit1 Hstsim]]]. 
    assert (OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    assert (exists maxb, 
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom.
      eapply Promotability.s_genInitState__wf_globals_promotable; eauto.
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]]. 
    eapply sop_div__dse_State_simulation in Hstsim; eauto.
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.
Qed.

Lemma dse_wfS: forall (pinfo:PhiInfo) f pid Ps1 Ps2 los nts
  (Heq1: PI_id pinfo = pid) (Heq2: PI_f pinfo = f) 
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hnld: load_in_fdef pid f = false),
  wf_system 
    [module_intro los nts 
      (Ps1 ++  product_fdef (elim_dead_st_fdef pid f) :: Ps2)].
Proof.
Admitted.

Lemma dse_wfPI: forall (pinfo:PhiInfo) f pid Ps1 Ps2 los nts
  (Heq1: PI_id pinfo = pid) (Heq2: PI_f pinfo = f) 
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hnld: load_in_fdef pid f = false),
  WF_PhiInfo (update_pinfo pinfo (elim_dead_st_fdef pid f)).
Proof.
Admitted.

Lemma elim_dead_st_fdef_successors : forall f id',
  successors f = successors (elim_dead_st_fdef id' f).
Admitted.

Lemma elim_dead_st_fdef_reachablity_analysis : forall f id',
  dtree.reachablity_analysis f = 
    dtree.reachablity_analysis (elim_dead_st_fdef id' f).
Admitted.

