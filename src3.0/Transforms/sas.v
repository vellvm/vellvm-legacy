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
Require Import sas_msim.
Require Import memory_sim.

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

Definition in_SAS_tail (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) omb 
  (TD:TargetData) (ec0:@Opsem.ExecutionContext DGVs) : Prop :=
  (EC_follow_dead_store pinfo sasinfo ec0 -> 
     match lookupAL _ (Opsem.Locals ec0) (PI_id pinfo) with
     | Some ((Vptr mb _, _)::nil) => omb = Some mb
     | _ => omb = None
     end) /\
  (~EC_follow_dead_store pinfo sasinfo ec0 -> omb = None).

Definition in_SAS_tails (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) ombs TD
  (ecs:list Opsem.ExecutionContext) : Prop :=
List.Forall2 (fun ec omb => 
              in_SAS_tail pinfo sasinfo omb TD ec) ecs ombs.

Fixpoint ombs__ignores (tsz:Z) (ombs: list (option Values.block))
  : list (Values.block*Z*Z) :=
match ombs with
| nil => nil
| Some mb::ombs' => (mb, 0, tsz)::ombs__ignores tsz ombs'
| None::ombs' => ombs__ignores tsz ombs'
end.

Definition sas_mem_inj (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) 
  (ecs1:list Opsem.ExecutionContext) (TD:TargetData) (m1 m2: mem) : Prop :=
match getTypeStoreSize TD (PI_typ pinfo) with
| Some tsz => 
    forall ombs,
      in_SAS_tails pinfo sasinfo ombs TD ecs1 ->
      SASmsim.mem_inj inject_id (ombs__ignores (Size.to_Z tsz) ombs) m1 m2
| None => False
end.

Definition mem_simulation (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) TD
  (ecs1:list Opsem.ExecutionContext) Mem1 Mem2 : Prop :=
Mem.nextblock Mem1 = Mem.nextblock Mem2 /\
(forall b, Mem.bounds Mem1 b = Mem.bounds Mem2 b) /\
sas_mem_inj pinfo sasinfo ecs1 TD Mem1 Mem2.

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
    gl1 = gl2 /\ fs1 = fs2 /\ mem_simulation pinfo sasinfo TD1 ECs1 M1 M2
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
  destruct_cmd c; auto.
  destruct (fdef_dec (PI_f pinfo) CurFunction); auto.
  destruct (id_dec i0 (SAS_sid1 pinfo sasinfo)); auto.
Qed.

Ltac repeat_solve :=
  repeat (match goal with
          | |- mem_simulation _ _ _ _ _ _ => idtac
          | |- _ => split; eauto 2 using cmds_at_block_tail_next
          end).

Lemma SAS_sid1_isnt_in_SAS_tail: forall pinfo sasinfo TD B1 t v v0 a cs1 tmn2 
  lc2 als2 (Huniq: uniqFdef (PI_f pinfo)),
  in_SAS_tail pinfo sasinfo None TD
    {| Opsem.CurFunction := PI_f pinfo;
       Opsem.CurBB := B1;
       Opsem.CurCmds := insn_store (SAS_sid1 pinfo sasinfo) t v v0 a:: cs1;
       Opsem.Terminator := tmn2;
       Opsem.Locals := lc2;
       Opsem.Allocas := als2 |}.
Proof. 
  unfold in_SAS_tail. simpl.
  intros. 
  unfold EC_follow_dead_store. simpl.
  split; intros J; auto.
    destruct J as [J1 [J2 J3]]; subst.
    unfold cs_follow_dead_store in J3.
    destruct sasinfo. simpl in *.
    destruct SAS_prop0 as [J4 [J5 J6]].
    destruct SAS_block0 as [? ? cs0 ?].
    destruct J6 as [cs2 [cs3 J6]]; subst.
    destruct (@J3 cs2 
                (insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
                  (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3)) as
      [csa [csb [J7 J8]]]; subst; auto.
    clear J3.
    simpl_env in J4. simpl_env in J7. rewrite <- J7 in J4.
    admit. (* uniqness *)
Qed.

Lemma wf__getTypeStoreSize_eq_sizeGenericValue: forall (gl2 : GVMap)
  (lc2 : Opsem.GVsMap) (S : system) (los : layouts) (nts : namedts)
  (Ps : list product) (v1 : value) (gv1 : GenericValue)
  (Hwfg : wf_global (los, nts) S gl2) (n : nat) t
  (HeqR : ret n = getTypeStoreSize (los, nts) t) F
  (H24 : @Opsem.getOperandValue DGVs (los, nts) v1 lc2 gl2 = ret gv1)
  (Hwflc1 : OpsemPP.wf_lc (los, nts) F lc2)
  (Hwfv : wf_value S (module_intro los nts Ps) F v1 t),
  n = sizeGenericValue gv1.
Proof.
  intros.
  eapply OpsemPP.getOperandValue__wf_gvs in Hwflc1; eauto.
  inv Hwflc1.
  assert (gv1 @ gv1) as Hinst. auto.
  apply H2 in Hinst.
  unfold gv_chunks_match_typ in Hinst.
  clear - Hinst HeqR Hwfv. inv_mbind.
  apply wf_value__wf_typ in Hwfv. destruct Hwfv as [J1 J2].
  symmetry in HeqR0.
  eapply flatten_typ__getTypeSizeInBits in HeqR0; eauto.
  destruct HeqR0 as [sz [al [A B]]].          
  unfold getTypeAllocSize, getTypeStoreSize, getABITypeAlignment,
         getTypeSizeInBits, getAlignment, 
         getTypeSizeInBits_and_Alignment in HeqR.
  rewrite A in HeqR.
  inv HeqR. rewrite B.
  eapply vm_matches_typ__sizeMC_eq_sizeGenericValue; eauto.
Qed.

Lemma mstore_removable_mem_simulation: forall los nts M1 mp2 gv1 a M1' pinfo lc2 
  gl2 B1 cs1 tmn2 als2 ECs1 M2 t v sasinfo v0 Ps
  (Huniq: uniqFdef (PI_f pinfo))
  (HBinF1 : blockInFdefB B1 (PI_f pinfo) = true)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B1 =
               block_intro l1 ps1
                 (cs11 ++ insn_store (SAS_sid1 pinfo sasinfo) t v v0 a :: cs1)
                 tmn2)
  (H23: mstore (los,nts) M1 mp2 t gv1 a = ret M1')
  (H20 : @Opsem.getOperandValue DGVs (los,nts) v0 lc2 gl2 = ret mp2)
  (H19 : Opsem.getOperandValue (los,nts) v lc2 gl2 = ret gv1) S
  (Hwfg : wf_global (los, nts) S gl2)
  (Hwflc1 : OpsemPP.wf_lc (los, nts) (PI_f pinfo) lc2)
  (Hwfv : wf_value S (module_intro los nts Ps) (PI_f pinfo) v t)
  (Hmsim: mem_simulation pinfo sasinfo (los,nts)
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := insn_store (SAS_sid1 pinfo sasinfo) t v v0 a
                              :: cs1;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: ECs1) M1 M2),
  mem_simulation pinfo sasinfo (los,nts)
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
    
    unfold sas_mem_inj in *. inv_mbind.
    intros ombs Hin.
    inv Hin.
    assert (in_SAS_tails pinfo sasinfo (None::l') (los,nts)
             ({|
              Opsem.CurFunction := PI_f pinfo;
              Opsem.CurBB := B1;
              Opsem.CurCmds := insn_store (SAS_sid1 pinfo sasinfo) t v v0 a
                               :: cs1;
              Opsem.Terminator := tmn2;
              Opsem.Locals := lc2;
              Opsem.Allocas := als2 |} :: ECs1)) as Hin.
      constructor; auto using SAS_sid1_isnt_in_SAS_tail.
    apply Hmsim2 in Hin. clear Hmsim2.
    simpl in Hin.
    assert (v0 = value_id (PI_id pinfo) /\ t = PI_typ pinfo) as EQ.
      admit. (* by sasinfo *)
    destruct EQ; subst. simpl in H20.
    assert (exists mb, mp2 = 
              ($ (blk2GV (los,nts) mb) # (typ_pointer (PI_typ pinfo)) $)) as EQ.
      admit. (* by promotable *)
    destruct EQ as [mb EQ]; subst.
    assert (y = Some mb) as EQ.
      admit. (* by H1 H20 *)
    subst.
    assert (n = sizeGenericValue gv1) as EQ.
      eapply wf__getTypeStoreSize_eq_sizeGenericValue; eauto.
    subst.
    simpl.
    eapply SASmsim.mstore_inside_inj_left; eauto.
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

Lemma in_SAS_tail_nil: forall pinfo sasinfo TD F B tmn lc als,
  in_SAS_tail pinfo sasinfo None TD 
    {| Opsem.CurFunction := F;
       Opsem.CurBB := B;
       Opsem.CurCmds := nil;
       Opsem.Terminator := tmn;
       Opsem.Locals := lc;
       Opsem.Allocas := als |}.
Proof.
  intros.
  unfold in_SAS_tail. simpl. intros.
  split; intros J; auto.
    destruct J as [J1 [J2 J3]]. simpl in J1, J2, J3.
    eapply cs_follow_dead_store_isnt_nil in J3; eauto.
    inv J3.      
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
    admit. (* uniqness *)
  destruct EQ as [EQ3 EQ4]; subst.
  edestruct H0 as [csa [csb [J1 J2]]]; subst; eauto.
  destruct csb.
    inv J1. contradict H; auto.

    inv J1. exists (csa++[c0]). exists csb. simpl_env. split; auto.
Qed.

Lemma cs_follow_dead_store_tail': forall pinfo sasinfo c cs
  (Hex: exists l0, exists ps0, exists tmn0, exists cs0,
          SAS_block pinfo sasinfo = block_intro l0 ps0 (cs0++c::cs) tmn0),
  getCmdLoc c <> SAS_sid1 pinfo sasinfo ->
  cs_follow_dead_store pinfo sasinfo cs ->
  cs_follow_dead_store pinfo sasinfo (c :: cs).
Proof.
  unfold cs_follow_dead_store.
  destruct sasinfo. simpl. intros.
  destruct SAS_block0.
  intros.
  destruct SAS_prop0 as [EQ1 [EQ2 [cs4 [cs2 EQ3]]]]; subst.
  assert (cs4 = cs1 /\
          cs3 = insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
                  (value_id (PI_id pinfo)) (PI_align pinfo) :: cs2) as EQ.
    admit. (* uniqness *)
  destruct EQ as [EQ3 EQ4]; subst.
  apply_clear H0 in H1.
  destruct H1 as [csa [csb [J1 J2]]]; subst.
  destruct Hex as [l1 [ps0 [tmn0 [cs0 Hex]]]].
  inv Hex.
  simpl_env in H3.
  destruct csa.
    assert (c = insn_store SAS_sid3 (PI_typ pinfo) SAS_value3
                  (value_id (PI_id pinfo)) (PI_align pinfo)) as EQ.
      admit. (* list *)
    subst. simpl in H. congruence.

    assert (exists csa', c0 :: csa = csa' ++ [c]) as EQ.
      admit. (* list *)
    destruct EQ as [csa' EQ].
    rewrite EQ.
    exists csa'. exists (c::csb).
    simpl_env.
    split; auto.
Qed.

Lemma EC_follow_dead_store_tail: forall pinfo sasinfo c cs B tmn3 lc1 als3 als3'
  lc2 F,
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
         Opsem.Allocas := als3' |}.
Proof.
  intros.
  intro J. apply H0.
  destruct J as [J1 [J2 J3]]. simpl in *.
  split; auto.
  split; auto.
    simpl.
    eapply cs_follow_dead_store_tail; eauto.
Qed.

Lemma EC_follow_dead_store_tail':forall pinfo sasinfo c cs B tmn3 lc1 als3 als3'
  lc2 F,
  getCmdLoc c <> SAS_sid2 pinfo sasinfo ->
  EC_follow_dead_store pinfo sasinfo
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := c :: cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc2;
         Opsem.Allocas := als3' |} ->
  EC_follow_dead_store pinfo sasinfo
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc1;
         Opsem.Allocas := als3 |}.
Proof.
  intros.
  destruct H0 as [J1 [J2 J3]]. simpl in *. subst.
  split; auto.
  split; auto.
    simpl.
    eapply cs_follow_dead_store_tail; eauto.
Qed.

Lemma EC_follow_dead_store_tail'':forall pinfo sasinfo c cs B tmn3 lc1 als3 als3'
  lc2 F
  (Hex: exists l0, exists ps0, exists cs0,
          B = block_intro l0 ps0 (cs0++c::cs) tmn3),
  getCmdLoc c <> SAS_sid1 pinfo sasinfo ->
  EC_follow_dead_store pinfo sasinfo
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc2;
         Opsem.Allocas := als3' |} ->
  EC_follow_dead_store pinfo sasinfo
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := c::cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc1;
         Opsem.Allocas := als3 |}.
Proof.
  intros.
  destruct H0 as [J1 [J2 J3]]. simpl in *. subst.
  split; auto.
  split; auto.
    simpl.
    eapply cs_follow_dead_store_tail'; eauto.
    destruct Hex as [l0 [ps0 [cs0 Hex]]].
    rewrite Hex. eauto.
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

Lemma EC_follow_dead_store_at_begin_false: forall pinfo sasinfo F l' ps' cs' tmn'
  tmn lc2 als2,
  ~
  EC_follow_dead_store pinfo sasinfo
    {|
     Opsem.CurFunction := F;
     Opsem.CurBB := block_intro l' ps' cs' tmn';
     Opsem.CurCmds := cs';
     Opsem.Terminator := tmn;
     Opsem.Locals := lc2;
     Opsem.Allocas := als2 |}.
Proof.
  intros. intro J.
  destruct J as [J1 [J2 J3]]. simpl in *.
  eapply cs_follow_dead_store_at_beginning_false in J3; eauto.
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

Lemma switchToNewBasicBlock_mem_simulation: forall (pinfo : PhiInfo)
  (sasinfo : SASInfo pinfo) (gl2 : GVMap) (lc2 : Opsem.GVsMap)
  (als2 : list mblock) (M2 : mem) (los : layouts) (nts : namedts) (F : fdef)
  (B : block) tmn
  (EC : list Opsem.ExecutionContext) (Mem : mem) (cs' : cmds)
  (Hmsim : mem_simulation pinfo sasinfo (los, nts)
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
  mem_simulation pinfo sasinfo (los, nts)
     ({|
      Opsem.CurFunction := F;
      Opsem.CurBB := block_intro l'0 ps'0 cs' tmn'0;
      Opsem.CurCmds := cs';
      Opsem.Terminator := tmn'0;
      Opsem.Locals := lc'0;
      Opsem.Allocas := als2 |} :: EC) Mem M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  split; auto.
  split; auto.
    intros.
    unfold sas_mem_inj in *. inv_mbind.
    intros.
    inv H.
    apply Hmsim2; auto. clear Hmsim2.
    constructor; auto. clear H5.
    unfold in_SAS_tail in *. simpl in *. 
    destruct H3 as [H31 H32].
    split.
      intros.
      apply EC_follow_dead_store_at_end_false in H.
      inv H.

      intro J.
      apply H32. apply EC_follow_dead_store_at_begin_false.
Qed.

Lemma unremovable_loc__neq__SAS_sid1: forall pinfo sasinfo F B c cs tmn2 lc2
  als2 EC Mem id0
  (Hnrem : ~ removable_State pinfo sasinfo
               {|Opsem.ECS := {| Opsem.CurFunction := F;
                                 Opsem.CurBB := B;
                                 Opsem.CurCmds := c :: cs;
                                 Opsem.Terminator := tmn2;
                                 Opsem.Locals := lc2;
                                 Opsem.Allocas := als2 |} :: EC;
                 Opsem.Mem := Mem |})
  (EQ : id0 = getCmdLoc c),
  PI_f pinfo = F -> id0 <> SAS_sid1 pinfo sasinfo.
Admitted.

Lemma unremovable_loc__neq__SAS_sid2: forall pinfo sasinfo F B c cs tmn2 lc2
  als2 EC Mem id0
  (Hnrem : ~ removable_State pinfo sasinfo
               {|Opsem.ECS := {| Opsem.CurFunction := F;
                                 Opsem.CurBB := B;
                                 Opsem.CurCmds := c :: cs;
                                 Opsem.Terminator := tmn2;
                                 Opsem.Locals := lc2;
                                 Opsem.Allocas := als2 |} :: EC;
                 Opsem.Mem := Mem |})
  (EQ : Some id0 = getCmdID c),
  PI_f pinfo = F -> id0 <> SAS_sid2 pinfo sasinfo.
Admitted.

Lemma in_SAS_tail_update :
  forall pinfo sasinfo TD F B c cs tmn3 lc1 als3 als3' lc2 omb
  (Hneq: PI_f pinfo = F -> getCmdLoc c <> SAS_sid2 pinfo sasinfo)
  (Hneq': PI_f pinfo = F -> getCmdLoc c <> SAS_sid1 pinfo sasinfo)
  (Hex: exists l0, exists ps0, exists cs0,
          B = block_intro l0 ps0 (cs0++c::cs) tmn3)
  (Hp: lookupAL (GVsT DGVs) lc2 (PI_id pinfo) =
            lookupAL (GVsT DGVs) lc1 (PI_id pinfo))
  (H1: in_SAS_tail pinfo sasinfo omb TD 
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc1;
         Opsem.Allocas := als3 |}),
  in_SAS_tail pinfo sasinfo omb TD
      {| Opsem.CurFunction := F;
         Opsem.CurBB := B;
         Opsem.CurCmds := c :: cs;
         Opsem.Terminator := tmn3;
         Opsem.Locals := lc2;
         Opsem.Allocas := als3' |}.
Proof.
  intros.
  destruct H1 as [H11 H12].
  split; simpl in *.
    intros.
    rewrite Hp.
    apply H11; auto.
    eapply EC_follow_dead_store_tail'; eauto.
      destruct H. eauto.

    intros. apply H12.
    intro G. apply H.
    eapply EC_follow_dead_store_tail''; eauto.
      destruct G. eauto.
Qed.

Lemma mem_simulation_update_locals :
  forall pinfo sasinfo TD F B c cs tmn3 lc1 lc2 als3 als3' ECs M1 M2
  (Hneq: PI_f pinfo = F -> getCmdLoc c <> SAS_sid2 pinfo sasinfo)
  (Hneq': PI_f pinfo = F -> getCmdLoc c <> SAS_sid1 pinfo sasinfo)
  (Hex: exists l0, exists ps0, exists cs0,
          B = block_intro l0 ps0 (cs0++c::cs) tmn3)
  (Hp: lookupAL (GVsT DGVs) lc1 (PI_id pinfo) =
         lookupAL (GVsT DGVs) lc2 (PI_id pinfo))
  (Hmsim: mem_simulation pinfo sasinfo TD 
            ({| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := c::cs;
                Opsem.Terminator := tmn3;
                Opsem.Locals := lc1;
                Opsem.Allocas := als3 |} :: ECs) M1 M2),
  mem_simulation pinfo sasinfo TD 
    ({| Opsem.CurFunction := F;
        Opsem.CurBB := B;
        Opsem.CurCmds := cs;
        Opsem.Terminator := tmn3;
        Opsem.Locals := lc2;
        Opsem.Allocas := als3' |} :: ECs) M1 M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  split; auto.
  split; auto.
    unfold sas_mem_inj in *.
    inv_mbind. clear HeqR.
    intros ombs Hin.
    inv Hin.
    apply Hmsim2. clear Hmsim2.
    constructor; auto. clear H3.
    eapply in_SAS_tail_update; eauto.
Qed.

Lemma products_simulation__fdef_simulation : forall pinfo sasinfo Ps1 Ps2 fid f1
  f2,
  lookupFdefViaIDFromProducts Ps2 fid = Some f2 ->
  lookupFdefViaIDFromProducts Ps1 fid = Some f1 ->
  products_simulation pinfo sasinfo Ps1 Ps2 ->
  fdef_simulation pinfo sasinfo f1 f2.
Admitted.

Lemma lookupFdefViaPtr__simulation : forall pinfo sasinfo Ps1 Ps2 fptr f1 f2 fs,
  OpsemAux.lookupFdefViaPtr Ps2 fs fptr = Some f2 ->
  products_simulation pinfo sasinfo Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs fptr = Some f1 ->
  fdef_simulation pinfo sasinfo f1 f2.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptr) as R2.
  destruct R2 as [fid|]; inv H1. simpl in H.
  eapply products_simulation__fdef_simulation in H0; eauto.
Qed.

Lemma fdef_simulation__entry_block_simulation: forall pinfo sasinfo F1 F2 B1 B2,
  fdef_simulation pinfo sasinfo F1 F2 ->
  getEntryBlock F1 = ret B1 ->
  getEntryBlock F2 = ret B2 ->
  block_simulation pinfo sasinfo F1 B1 B2.
Admitted.

Lemma fdef_simulation_inv: forall pinfo sasinfo fh1 fh2 bs1 bs2,
  fdef_simulation pinfo sasinfo (fdef_intro fh1 bs1) (fdef_intro fh2 bs2) ->
  fh1 = fh2 /\
  List.Forall2
    (fun b1 b2 =>
      block_simulation pinfo sasinfo (fdef_intro fh1 bs1) b1 b2) bs1 bs2.
Admitted.

Lemma lookupFdefViaPtr__simulation_l2r : forall pinfo sasinfo Ps1 Ps2 fptr f1 fs,
  products_simulation pinfo sasinfo Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs fptr = Some f1 ->
  exists f2,
    OpsemAux.lookupFdefViaPtr Ps2 fs fptr = Some f2 /\
    fdef_simulation pinfo sasinfo f1 f2.
Admitted.

Lemma lookupExFdecViaPtr__simulation_l2r : forall pinfo sasinfo Ps1 Ps2 fptr f fs,
  products_simulation pinfo sasinfo Ps1 Ps2 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs fptr = Some f ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs fptr = Some f.
Admitted.

(*
Lemma undead_head_tail_cons_and: forall pinfo sasinfo ptr EC ECs,
  undead_head_tail pinfo sasinfo ptr (EC :: ECs) ->
  undead_head_in_tail pinfo sasinfo ptr EC /\
    undead_head_tail pinfo sasinfo ptr ECs.
Proof.
  intros.
  unfold undead_head_tail in *.
  split.
    apply H; simpl; auto.
    intros. apply H; simpl; auto.
Qed.
*)

Lemma callExternalFunction__mem_simulation: forall pinfo sasinfo TD St1 M1 M2
  fid0 gvss0 oresult1 M1' oresult2 M2' dck tret targs gl tr1 tr2,
  mem_simulation pinfo sasinfo TD St1 M1 M2 ->
  callExternalOrIntrinsics TD gl M1 fid0 tret targs dck gvss0 = 
    ret (oresult1, tr1, M1') ->
  callExternalOrIntrinsics TD gl M2 fid0 tret targs dck gvss0 = 
    ret (oresult2, tr2, M2') ->
  oresult1 = oresult2 /\ mem_simulation pinfo sasinfo TD St1 M1' M2' /\ 
    tr1 = tr2.
Admitted.

Ltac destruct_ctx_other :=
match goal with
| Hwfcfg: OpsemPP.wf_Config _,
  Hwfpp : OpsemPP.wf_State
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
  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]];
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

Ltac destruct_ctx_return :=
match goal with
| Hwfcfg: OpsemPP.wf_Config _,
  Hwfpp : OpsemPP.wf_State
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
  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]];
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
  apply cmds_simulation_nelim_cons_inv in Hcssim2'; try solve [
    auto |
    try match goal with
        | |- _ = _ -> _ <> _ => admit
        end ];
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result
end.

Lemma mem_simulation__free : forall TD Mem1 Mem2 Mem1' Mem2'
  ECs1 pinfo sasinfo EC EC' ptr
  (Hp: forall omb,
       in_SAS_tail pinfo sasinfo omb TD EC' ->
       in_SAS_tail pinfo sasinfo omb TD EC)
  (Hmsim : mem_simulation pinfo sasinfo TD 
             (EC :: ECs1) Mem1 Mem2)
  (Hmlc: free TD Mem1 ptr = ret Mem1')
  (Hmlc': free TD Mem2 ptr = ret Mem2'),
  mem_simulation pinfo sasinfo TD (EC' :: ECs1) Mem1' Mem2'.
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

    unfold sas_mem_inj in *.
    inv_mbind.
    intros ombs Hin'.
    assert (in_SAS_tails pinfo sasinfo ombs TD (EC :: ECs1)) as Hin.
      inv Hin'.
      constructor; auto.
    apply J3 in Hin.
    eapply SASmsim.free_inj with (delta:=0)(b1:=blk')(b2:=blk') in Hin; 
      eauto using SASmsim.inject_id_no_overlap, SASmsim.inject_id_zero_delta.
    replace (lo+0) with lo by omega.
    replace (hi+0) with hi by omega. 
    rewrite J2 in H3. rewrite <- H3' in H3. inv H3. auto.
Qed.

Lemma in_SAS_tails__replace_head: forall TD EC' EC ECs1 ombs pinfo sasinfo
  (Hp : forall omb : monad mblock,
        in_SAS_tail pinfo sasinfo omb TD EC' ->
        in_SAS_tail pinfo sasinfo omb TD EC)
  (H1: in_SAS_tails pinfo sasinfo ombs TD (EC' :: ECs1)),
  in_SAS_tails pinfo sasinfo ombs TD (EC :: ECs1).
Proof.
  intros. inv H1. constructor; auto.
Qed.

Lemma mem_simulation__replace_head: forall TD ECs1 pinfo sasinfo EC EC'
  (Hp : forall omb : monad mblock,
        in_SAS_tail pinfo sasinfo omb TD EC' ->
        in_SAS_tail pinfo sasinfo omb TD EC) M1 M2
  (Hmsim : mem_simulation pinfo sasinfo TD (EC :: ECs1) M1 M2),
  mem_simulation pinfo sasinfo TD (EC' :: ECs1) M1 M2.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  split; auto.
  split; auto.
    unfold sas_mem_inj in *.
    inv_mbind.
    intros ombs Hin'.
    eapply in_SAS_tails__replace_head in Hin'; eauto.
Qed.

Lemma mem_simulation__free_allocas : forall TD ECs1 pinfo sasinfo EC EC'
  (Hp: forall omb,
       in_SAS_tail pinfo sasinfo omb TD EC' ->
       in_SAS_tail pinfo sasinfo omb TD EC)
  als Mem1 Mem2 Mem1' Mem2'
  (Hmsim : mem_simulation pinfo sasinfo TD 
             (EC :: ECs1) Mem1 Mem2)
  (Hmlc: free_allocas TD Mem1 als = ret Mem1')
  (Hmlc': free_allocas TD Mem2 als = ret Mem2'),
  mem_simulation pinfo sasinfo TD (EC' :: ECs1) Mem1' Mem2'.
Proof.
  induction als; simpl; intros.
    uniq_result. 
    eapply mem_simulation__replace_head; eauto.

    inv_mbind.
    eapply mem_simulation__free with (Mem1':=m0)(Mem2':=m) in Hmsim; eauto.
Qed.

Lemma mem_simulation__remove_head: forall TD ECs1 pinfo sasinfo EC 
  (Hp : in_SAS_tail pinfo sasinfo None TD EC) M1 M2
  (Hmsim : mem_simulation pinfo sasinfo TD (EC :: ECs1) M1 M2),
  mem_simulation pinfo sasinfo TD ECs1 M1 M2.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  split; auto.
  split; auto.
    unfold sas_mem_inj in *.
    inv_mbind.
    intros ombs Hin'.
    replace (ombs__ignores (Size.to_Z n) ombs) with
            (ombs__ignores (Size.to_Z n) (None::ombs)) by auto.
    apply J3; auto.
      constructor; auto.
Qed.

Lemma mem_simulation__return: forall (pinfo : PhiInfo) (sasinfo : SASInfo pinfo)
  (lc2 : Opsem.GVsMap) (als2 : list mblock) (tmn3 : terminator) 
  (lc3 : Opsem.GVsMap) (als3 : list mblock) (M2 : mem) (los : layouts) 
  (nts : namedts) (F : fdef) (rid : id) tmn (F' : fdef) (B' : block) (i0 : id)
  (n : noret) (c : clattrs) (t : typ) (v : value) (p : params) (cs' : list cmd)
  (EC : list Opsem.ExecutionContext) (Mem : mem) (l3 : l) (ps3 : phinodes)
  (cs0 : list cmd) (Mem' : mem)
  (H0 : free_allocas (los, nts) Mem als2 = ret Mem')
  (Heq3' : exists l1 : l,
            exists ps1 : phinodes,
              exists cs11 : list cmd,
                B' =
                block_intro l1 ps1 (cs11 ++ insn_call i0 n c t v p :: cs')
                  tmn3)
  (Hmsim : mem_simulation pinfo sasinfo (los, nts)
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
                Opsem.CurCmds := insn_call i0 n c t v p :: cs';
                Opsem.Terminator := tmn3;
                Opsem.Locals := lc3;
                Opsem.Allocas := als3 |} :: EC) Mem M2)
  (Mem'0 : mem) (lc''0 : Opsem.GVsMap)
  (EQ: lookupAL (GVsT DGVs) lc3 (PI_id pinfo) =
         lookupAL (GVsT DGVs) lc''0 (PI_id pinfo))
  (H26 : free_allocas (los, nts) M2 als2 = ret Mem'0),
  mem_simulation pinfo sasinfo (los, nts)
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
  apply mem_simulation__remove_head in Hmsim.
    eapply mem_simulation_update_locals in Hmsim; eauto.
      admit. (* id <> sid2 *)
      admit. (* id <> sid1 *)
    apply in_SAS_tail_nil.
Qed. 

Ltac dse_is_sim_common_case :=
match goal with
| Hex: exists _:_, exists _:_, exists _:_, _=block_intro _ _ (_++_::_) _,      
  Hcssim2: cmds_simulation _ _ _ _ _,
  Hop2: Opsem.sInsn _ _ _ _,
  Hmsim: mem_simulation _ _ _ _ _ _ |- _ =>
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; try solve 
    [eauto using unremovable_loc__neq__SAS_sid1];
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  repeat_solve;
  match goal with
  | |- mem_simulation _ _ _
         ({|Opsem.CurFunction := _;
            Opsem.CurBB := _;
            Opsem.CurCmds := _;
            Opsem.Terminator := _;
            Opsem.Locals:= ?lc';
            Opsem.Allocas:=?als'|}::_) _ _ =>
      apply mem_simulation_update_locals with (lc2:=lc') (als3':=als') in Hmsim; 
        simpl; try solve [
          eauto using unremovable_loc__neq__SAS_sid1,
                      unremovable_loc__neq__SAS_sid2 |
          match goal with
          | |- lookupAL _ ?lc ?id1 =
                 lookupAL _ (updateAddAL _ ?lc _ _ ) ?id1 =>
               admit  (* id <> palloca *)
          end
        ]
  end
end.

Lemma mem_simulation__malloc: forall (pinfo : PhiInfo) (sasinfo : SASInfo pinfo)
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
  (Hmsim : mem_simulation pinfo sasinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := B;
             Opsem.CurCmds := c :: cs;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: EC) Mem M2)
  (Hnrem : ~
          removable_State pinfo sasinfo
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
  mem_simulation pinfo sasinfo (los, nts)
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

      unfold sas_mem_inj in *.
      inv_mbind. clear HeqR.
      intros ombs Hin'. 
      apply malloc_inv in H2. destruct H2 as [n0 [J1 [J2 J3]]].
      apply malloc_inv in H25. destruct H25 as [n0' [J1' [J2' J3']]].
      rewrite J1 in J1'. inv J1'.
      eapply SASmsim.alloc_inject_id_inj with (m1:=Mem)(m2:=M2); eauto.
      apply Hmsim2.
      eapply in_SAS_tails__replace_head in Hin'; eauto.
      intros.
      assert (ret getCmdLoc c = getCmdID c) as G.
        erewrite getCmdLoc_getCmdID; eauto.
      apply in_SAS_tail_update with 
        (lc1:=updateAddAL (GVsT DGVs) lc2 id0
                ($ blk2GV (los, nts) mb # typ_pointer t $)) (als3:=als2); 
        eauto using unremovable_loc__neq__SAS_sid1, 
                    unremovable_loc__neq__SAS_sid2.
        admit. (* id <> pid *)
Qed.

Lemma list_suffix_dec: forall A (Hdec: forall (x y : A), {x = y}+{x <> y})
  (l1 l2: list A), (exists l3, l1 = l3 ++ l2) \/ (~ exists l3, l1 = l3 ++ l2).
Admitted.

Lemma cs_follow_dead_store_dec: forall (pinfo : PhiInfo) 
  (sasinfo : SASInfo pinfo) (EC : @Opsem.ExecutionContext DGVs)
  (Ha : Opsem.CurFunction EC = PI_f pinfo)
  (Hb : Opsem.CurBB EC = SAS_block pinfo sasinfo),
  cs_follow_dead_store pinfo sasinfo (Opsem.CurCmds EC) \/
    ~ cs_follow_dead_store pinfo sasinfo (Opsem.CurCmds EC).
Proof.
  destruct EC. simpl. destruct sasinfo.
  simpl. destruct pinfo. simpl in *.
  intros. subst.
  unfold sas in SAS_prop0. simpl in *.
  destruct SAS_prop0 as [J1 [J2 J3]].
  destruct SAS_block0.
  destruct J3 as [cs1 [cs3 J3]]; subst. 
  unfold cs_follow_dead_store. simpl.
  clear.
  destruct (@list_suffix_dec _ cmd_dec CurCmds
    (insn_store SAS_sid4 PI_typ SAS_value4 (value_id PI_id) PI_align :: cs3))
    as [J | J].
    destruct J as [l3 J]; subst.
    destruct (@list_suffix_dec _ cmd_dec SAS_tail0 l3) as [J' | J'].
      destruct J' as [l4 J']; subst.
      left.
      intros.
      assert (cs2=insn_store SAS_sid4 PI_typ SAS_value4 (value_id PI_id) PI_align
                    :: cs3 ) as EQ.
        admit.
      subst.
      exists l4. exists l3. auto.

      right.
      intro J.
      destruct (@J cs1 
                   (insn_store SAS_sid4 PI_typ SAS_value4 
                     (value_id PI_id) PI_align :: cs3))
        as [csa1 [csb1 [J1 J2]]]; subst; auto.
      clear J.
      assert (l3 = csb1) as EQ. admit.
      subst.
      apply J'. exists csa1. auto.

    right.
    intro J'.
    destruct (@J' cs1 
                  (insn_store SAS_sid4 PI_typ SAS_value4 
                    (value_id PI_id) PI_align :: cs3))
      as [csa1 [csb1 [J1 J2]]]; subst; auto.
    clear J'.
    apply J. exists csb1. auto.
Qed.

Lemma EC_follow_dead_store_dec: forall pinfo sasinfo EC, 
  EC_follow_dead_store pinfo sasinfo EC \/ 
    ~ EC_follow_dead_store pinfo sasinfo EC.
Proof.
  intros.
  unfold EC_follow_dead_store.
  destruct (fdef_dec (Opsem.CurFunction EC) (PI_f pinfo)); 
    try solve [right; tauto].
  destruct (block_dec (Opsem.CurBB EC) (SAS_block pinfo sasinfo)); 
    try solve [right; tauto].
  destruct (cs_follow_dead_store_dec pinfo sasinfo EC e e0);
    try solve [right; tauto | auto].
Qed.

Lemma in_SAS_tail_ex: forall pinfo sasinfo TD EC,
  exists omb, in_SAS_tail pinfo sasinfo omb TD EC.
Proof.
  unfold in_SAS_tail.
  intros.
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC).
    destruct (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) 
      as [[|[[]][]]|]; eauto.
    exists (Some b). tauto.

    destruct (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) 
      as [[|[[]][]]|]; eauto.
    exists None. tauto.
Qed.

Lemma in_SAS_tails_ex: forall pinfo sasinfo TD ECs,
  exists ombs, in_SAS_tails pinfo sasinfo ombs TD ECs.
Proof.
  unfold in_SAS_tails.
  induction ECs; simpl; eauto.
    destruct IHECs as [ombs IHECs].
    destruct (@in_SAS_tail_ex pinfo sasinfo TD a) as [omb J].
    exists (omb::ombs). constructor; auto.
Qed.

Lemma in_SAS_tail__wf_ECStack_head_in_tail__no_alias_with_blk: forall
  (pinfo : PhiInfo) (sasinfo : SASInfo pinfo) (lc2 : AssocList (GVsT DGVs))
  (gv2 : GVsT DGVs) S los nts Ps (Mem : Mem.mem) F t v gl
  (Hwfv: wf_value S (module_intro los nts Ps) F v t)
  (maxb : Values.block) (Hget : getOperandValue (los,nts) v lc2 gl = ret gv2)
  (EC : Opsem.ExecutionContext) (mb : mblock)
  (H : in_SAS_tail pinfo sasinfo (ret mb) (los,nts) EC)
  (Hwfg: MemProps.wf_globals maxb gl)
  (Hnals1 : 
    Promotability.wf_ECStack_head_in_tail maxb pinfo (los,nts) Mem lc2 EC),
  MemProps.no_alias_with_blk gv2 mb.
Proof.
  intros.
  destruct H as [H1 H2]. destruct EC. simpl in *.
  unfold Promotability.wf_ECStack_head_in_tail in Hnals1.
  destruct (@EC_follow_dead_store_dec pinfo sasinfo 
               {| Opsem.CurFunction := CurFunction;
                  Opsem.CurBB := CurBB;
                  Opsem.CurCmds := CurCmds;
                  Opsem.Terminator := Terminator;
                  Opsem.Locals := Locals;
                  Opsem.Allocas := Allocas |}) as [J | J].
    assert (G:=J).
    destruct G as [J1 [J2 J3]]. simpl in *. subst.
    apply_clear H1 in J.
    remember (lookupAL (GVsT DGVs) Locals (PI_id pinfo)) as R.
    destruct R as [[|[[]][]]|]; tinv J.
    inv J. symmetry in HeqR.
    destruct (@Hnals1 ((Vptr b i0, m) :: nil)) as [J5 [J2 J4]]; auto.
    destruct v as [id2 | c2]; simpl in *.
      apply J2 in Hget.
      simpl in Hget. tauto.

      inv Hwfv.
      destruct J5 as [mb [J6 [J7 _]]].
      rewrite Promotability.simpl_blk2GV in J6. inv J6.
      symmetry in Hget.
      eapply Promotability.const2GV_disjoint_with_runtime_alloca with (t:=t) 
        (mb:=mb) in Hget; eauto.
      rewrite Promotability.simpl_blk2GV in Hget. 
      simpl in Hget. tauto.
    
    apply_clear H2 in J. congruence.
Qed.

Lemma in_SAS_tails__wf_ECStack_head_tail__no_alias_with_blk: 
  forall pinfo sasinfo lc2 gv2 los nts Mem maxb size Ps F t gl
  (Hwfg: MemProps.wf_globals maxb gl) v S
  (Hwfv: wf_value S (module_intro los nts Ps) F v t)
  (Hget : getOperandValue (los,nts) v lc2 gl = ret gv2) EC ombs
  (Hsas: in_SAS_tails pinfo sasinfo ombs (los,nts) EC)
  (Hnals: Promotability.wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc2 EC),
  List.Forall (fun re => 
               let '(mb,_,_) := re in
               MemProps.no_alias_with_blk gv2 mb) (ombs__ignores size ombs).
Proof.
  intros.
  induction Hsas; simpl; intros; auto.
    apply Promotability.wf_ECStack_head_tail_cons__inv in Hnals.
    destruct Hnals as [Hnals1 Hals2].
    apply_clear IHHsas in Hals2.
    destruct y as [mb|]; auto.
    constructor; auto.
    eapply in_SAS_tail__wf_ECStack_head_in_tail__no_alias_with_blk; eauto.
Qed.

Lemma unused_pid_in_SAS_tail__wf_defs__no_alias_with_blk: forall pinfo F los nts 
  maxb Mem lc2 EC gv2 als2
  (Hinscope: if fdef_dec (PI_f pinfo) F
             then Promotability.wf_defs maxb pinfo (los,nts) Mem lc2 als2
             else True)
  gl (Hwfg: MemProps.wf_globals maxb gl) v S t Ps
  (Hwfv: wf_value S (module_intro los nts Ps) F v t)
  (Hget : getOperandValue (los,nts) v lc2 gl = ret gv2) mb
  (Hneq: used_in_value (PI_id pinfo) v = false)
  (Heq1: Opsem.CurFunction EC = F) (Heq2: Opsem.Locals EC = lc2)
  (Heq3: Opsem.Allocas EC = als2) sasinfo
  (Hsas: in_SAS_tail pinfo sasinfo (Some mb) (los,nts) EC),
  MemProps.no_alias_with_blk gv2 mb.
Proof.
  intros.
  destruct Hsas as [J1 J2].
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC) as [J | J].
    assert (G:=J).
    destruct G as [J4 [J5 J3]]. simpl in *. subst.
    destruct (fdef_dec (PI_f pinfo) (Opsem.CurFunction EC)); try congruence.
    apply_clear J1 in J.
    remember (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) as R.
    destruct R as [[|[[]][]]|]; inv J.
    clear J2. symmetry in HeqR.
    apply_clear Hinscope in HeqR.
    destruct HeqR as [J1 J2].
    destruct v as [id2 | c2].
      apply J2 in Hget.
      unfold Promotability.wf_non_alloca_GVs in Hget.
      simpl in Hneq.
      destruct (id_dec id2 (PI_id pinfo)); tinv Hneq.
      simpl in Hget. tauto.

      unfold Promotability.wf_alloca_GVs in J1.
      destruct J1 as [_ [[mb [J6 [_ [J7 _]]]] _]].
      rewrite Promotability.simpl_blk2GV in J6. inv J6.
      symmetry in Hget. inv Hwfv.
      eapply Promotability.const2GV_disjoint_with_runtime_alloca with (t:=t) 
        (mb:=mb) in Hget; eauto.
      rewrite Promotability.simpl_blk2GV in Hget. 
      simpl in Hget. tauto.
    
    apply_clear J2 in J. congruence.
Qed.

Lemma load_in_cmds_true: forall id1 id0 t align0 csb csa,
  load_in_cmds id1 (csa ++ insn_load id0 t (value_id id1) align0 :: csb) = true.
Proof.
  unfold load_in_cmds.
  intros.
  generalize false.
  induction csa; simpl; intros; eauto.
    destruct (id_dec id1 id1); try congruence. 
    simpl.
    rewrite orb_true_intro; auto.
    apply fold_left_or_spec.
    intros. subst. auto.
Qed.

Lemma load_pid_isnt_in_SAS_tail: forall pinfo sasinfo TD v t id0 align0 cs EC 
  (Hneq: used_in_value (PI_id pinfo) v = true)
  (Heq: Opsem.CurCmds EC = insn_load id0 t v align0 :: cs),
  in_SAS_tail pinfo sasinfo None TD EC.
Proof.
  unfold in_SAS_tail.
  simpl. intros.
  destruct v; inv Hneq.
  destruct (id_dec i0 (PI_id pinfo)); subst; inv H0.
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC) as [J | J].
    elimtype False.
    destruct J as [J1 [J2 J3]].
    unfold cs_follow_dead_store in J3.
    destruct sasinfo. simpl in *.
    destruct SAS_prop0 as [J4 [J5 J6]].
    destruct SAS_block0 as [? ? cs0 ?].
    destruct J6 as [cs2 [cs3 J6]]; subst. simpl in *.
    destruct (@J3 cs2 (insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
                         (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3)) as
      [csa [csb [J7 J6]]]; subst; auto. clear J3.
    rewrite Heq in J7.
    destruct csb; inv J7.
    rewrite load_in_cmds_true in J5. congruence.

    split; intro; auto.
      congruence.
Qed.
    
Lemma in_SAS_tails__notin_ignores_with_size': forall maxb pinfo sasinfo 
  los nts Mem lc2 EC gl
  (Hnals: Promotability.wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc2 EC)
  (Hwfg: MemProps.wf_globals maxb gl) S Ps t v F 
  (Hwfv: wf_value S (module_intro los nts Ps) F v (typ_pointer t))
  b' ofs' m'
  (Hget: getOperandValue (los,nts) v lc2 gl = Some ((Vptr b' ofs', m')::nil)) ombs size'
  (Hin: in_SAS_tails pinfo sasinfo ombs (los,nts) EC) size,
  SASmsim.notin_ignores_with_size (ombs__ignores size' ombs) b'
     (Int.signed 31 ofs') size.
Proof.
  intros.
  eapply in_SAS_tails__wf_ECStack_head_tail__no_alias_with_blk 
    with (size:=size') in Hin; eauto.
  eapply SASmsim.no_alias_with_blk__notin_ignores_with_size; eauto.
Qed.   

Lemma in_SAS_tail_dec: forall pinfo sasinfo TD EC mb
  (Hnone: in_SAS_tail pinfo sasinfo None TD EC)
  (Hsome: in_SAS_tail pinfo sasinfo (Some mb) TD EC),
  False.
Proof.
  unfold in_SAS_tail.
  intros.
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC) as [J | J].
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

Lemma in_SAS_tails__notin_ignores_with_size: forall maxb pinfo sasinfo 
  los nts Mem lc2 EC gl
  (Hnals: Promotability.wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc2 EC)
  (Hwfg: MemProps.wf_globals maxb gl) S Ps als2 tmn2 id0 t align0 v cs B F
  (Hwfv: wf_value S (module_intro los nts Ps) F v (typ_pointer t))
  (Hinscope: if fdef_dec (PI_f pinfo) F
             then Promotability.wf_defs maxb pinfo (los,nts) Mem lc2 als2
             else True) b' ofs' m'
  (Hget: getOperandValue (los,nts) v lc2 gl = Some ((Vptr b' ofs', m')::nil)) ombs size'
  (Hin: in_SAS_tails pinfo sasinfo ombs (los,nts)
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
  eapply in_SAS_tails__notin_ignores_with_size' with (size:=size)(size':=size') 
    in H3; eauto.
  destruct y as [mb|]; auto.
    unfold SASmsim.notin_ignores_with_size in *.
    constructor; auto.
    remember (used_in_value (PI_id pinfo) v) as R.
    destruct R.
      assert (in_SAS_tail pinfo sasinfo None (los, nts)
          {| Opsem.CurFunction := F;
             Opsem.CurBB := B;
             Opsem.CurCmds := insn_load id0 t v align0 :: cs;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |}) as Hin.
      eapply load_pid_isnt_in_SAS_tail; simpl; eauto.
      apply in_SAS_tail_dec in H1; auto.
      
      eapply unused_pid_in_SAS_tail__wf_defs__no_alias_with_blk in H1; eauto.
      simpl in H1. auto.
Qed.

Lemma mem_simulation__mload: forall (maxb : Z) (pinfo : PhiInfo) 
  (sasinfo : SASInfo pinfo) (gl2 : GVMap) (fs2 : GVMap) (tmn2 : terminator)
  (lc2 : Opsem.GVsMap) (als2 : list mblock) (M2 : mem) (S : system)
  (los : layouts) (nts : namedts) (Ps : list product) (F : fdef) (B : block)
  (id0 : id) (t : typ) (align0 : align) (v : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (Mem : mem)
  (mp : GenericValue) (gv : GenericValue)
  (H1 : mload (los, nts) Mem mp t align0 = ret gv)
  (Hwfg : MemProps.wf_globals maxb gl2)
  (Hmsim : mem_simulation pinfo sasinfo (los, nts)
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
  unfold sas_mem_inj in Hmsim2.
  inv_mbind. clear HeqR.
  destruct (@in_SAS_tails_ex pinfo sasinfo (los,nts) 
             ({| Opsem.CurFunction := F;
                 Opsem.CurBB := B;
                 Opsem.CurCmds := insn_load id0 t v align0 :: cs;
                 Opsem.Terminator := tmn2;
                 Opsem.Locals := lc2;
                 Opsem.Allocas := als2 |} :: EC)) as [ombs Hin].
  assert (G:=Hin).
  apply_clear Hmsim2 in Hin.
  eapply SASmsim.mload_aux_inject_id_inj2; eauto.
    eapply in_SAS_tails__notin_ignores_with_size; eauto.
Qed.

Lemma in_SAS_tail_at_beginning: forall pinfo sasinfo TD F tmn' lc' als' cs' ps' 
  l',
  in_SAS_tail pinfo sasinfo None TD 
    {| Opsem.CurFunction := F;
       Opsem.CurBB := block_intro l' ps' cs' tmn';
       Opsem.CurCmds := cs';
       Opsem.Terminator := tmn';
       Opsem.Locals := lc';
       Opsem.Allocas := als' |}.
Proof.
  intros.
  unfold in_SAS_tail. simpl. intros.
  split; intros J; auto.
    contradict J.
    apply EC_follow_dead_store_at_begin_false; auto.
Qed.

Lemma mem_simulation__call: forall pinfo sasinfo TD EC ECs M1 M2
  (Hmsim : mem_simulation pinfo sasinfo TD (EC :: ECs) M1 M2)
  (l'0 : l) (ps'0 : phinodes) (tmn'0 : terminator) als' lc' F cs',
  mem_simulation pinfo sasinfo TD
    ({| Opsem.CurFunction := F;
        Opsem.CurBB := block_intro l'0 ps'0 cs' tmn'0;
        Opsem.CurCmds := cs';
        Opsem.Terminator := tmn'0;
        Opsem.Locals := lc';
        Opsem.Allocas := als' |} :: EC :: ECs) M1 M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  split; auto.
  split; auto.
     clear - Hmsim2.
     unfold sas_mem_inj in *.
     inv_mbind. 
     intros ombs Hin'.
     inv Hin'.

     destruct y.
       assert (in_SAS_tail pinfo sasinfo None TD
         {| Opsem.CurFunction := F;
            Opsem.CurBB := block_intro l'0 ps'0 cs' tmn'0;
            Opsem.CurCmds := cs';
            Opsem.Terminator := tmn'0;
            Opsem.Locals := lc';
           Opsem.Allocas := als' |}) as Hin.
         apply in_SAS_tail_at_beginning; auto.
       apply in_SAS_tail_dec in H1; auto. inv H1.
       
       simpl.
       apply Hmsim2; auto.
Qed.

Lemma SAS_sid2_isnt_in_SAS_tail: forall (pinfo : PhiInfo) 
  (sasinfo : SASInfo pinfo) (tmn2 : terminator) (lc2 : Opsem.GVsMap)
  (als2 : list mblock) (los : layouts) (nts : namedts) (B : block) (t : typ)
  (align0 : align) (v1 : value) (v2 : value) (cs : list cmd)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1
                 (cs11 ++
                  insn_store (SAS_sid2 pinfo sasinfo) t v1 v2 align0 :: cs)
                 tmn2)
  (y : monad Values.block)
  (H1 : in_SAS_tail pinfo sasinfo y (los, nts)
         {|
         Opsem.CurFunction := PI_f pinfo;
         Opsem.CurBB := B;
         Opsem.CurCmds := cs;
         Opsem.Terminator := tmn2;
         Opsem.Locals := lc2;
         Opsem.Allocas := als2 |}), y = merror.
Proof.
  intros.
  destruct H1 as [_ H1]. apply H1. clear H1.
  intro J.
  clear - J Heq3.
  destruct J as [J1 [J2 J3]]. simpl in *. subst.
  unfold cs_follow_dead_store in J3.
  destruct Heq3 as [l1 [ps1 [cs11 Heq3]]].
  rewrite Heq3 in J3. clear J1.
  destruct sasinfo. simpl in *. subst.
  destruct SAS_prop0 as [J4 [J5 [cs1 [cs3 J6]]]]. 
  assert (insn_store SAS_sid4 t v1 v2 align0 :: cs = 
          insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
            (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3 /\
          cs11 = cs1 ++
            insn_store SAS_sid3 (PI_typ pinfo) SAS_value3 
              (value_id (PI_id pinfo)) (PI_align pinfo)
            :: SAS_tail0) as EQ.
    admit. (* uniqness *)
  destruct EQ as [EQ1 EQ2]; subst. clear J6.
  inv EQ1.
  destruct (@J3 cs1 (insn_store SAS_sid4 (PI_typ pinfo) SAS_value4 
                    (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3))
    as [csa [csb [J6 J7]]]; simpl_env; auto.
    admit. (* list *)
Qed.

Lemma SAS_sid2_is_in_SAS_tail: forall (pinfo : PhiInfo) (sasinfo : SASInfo pinfo)
  (tmn2 : terminator) (lc2 : Opsem.GVsMap) (als2 : list mblock) (los : layouts)
  (nts : namedts) (B : block) (align0 : align) (v1 : value) (cs : list cmd)
  (b' : Values.block) (cm' : AST.memory_chunk)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               block_intro l1 ps1
                 (cs11 ++
                  insn_store (SAS_sid2 pinfo sasinfo) 
                    (PI_typ pinfo) v1 (value_id (PI_id pinfo)) align0 :: cs)
                 tmn2)
  (H25 : lookupAL (GVsT DGVs) lc2 (PI_id pinfo) =
        ret ((Vptr b' (Int.repr 31 0), cm') :: nil)),
  in_SAS_tail pinfo sasinfo (ret b') (los, nts)
     {|
     Opsem.CurFunction := PI_f pinfo;
     Opsem.CurBB := B;
     Opsem.CurCmds := insn_store (SAS_sid2 pinfo sasinfo) 
                        (PI_typ pinfo) v1 (value_id (PI_id pinfo)) align0
                      :: cs;
     Opsem.Terminator := tmn2;
     Opsem.Locals := lc2;
     Opsem.Allocas := als2 |}.
Proof.
  intros.
  split; intros J; simpl.
    rewrite H25; auto.
  
    contradict J.                
    split; auto.
    simpl.
    destruct Heq3 as [l1 [ps1 [cs11 Heq3]]]. subst.
    assert (block_intro l1 ps1
             (cs11 ++
              insn_store (SAS_sid2 pinfo sasinfo) (PI_typ pinfo) v1
              (value_id (PI_id pinfo)) align0 :: cs) tmn2 = 
            SAS_block pinfo sasinfo) as EQ.
      admit. (* uniqness SAS *)
    split; auto.
      unfold cs_follow_dead_store.
      rewrite <- EQ.
      intros.
      clear - EQ H.
      destruct sasinfo. simpl in *.
      destruct SAS_prop0 as [J1 [J2 J3]].
      subst.
      destruct J3 as [cs5 [cs4 J3]].
      assert (cs11 = cs5 ++
                insn_store SAS_sid3 (PI_typ pinfo) SAS_value3 
                  (value_id (PI_id pinfo)) (PI_align pinfo)
                :: SAS_tail0 /\ cs = cs4) as EQ'.
        admit. (* uniqness *)
      destruct EQ'; subst. clear J3.
      assert (cs5 = cs1 /\ insn_store SAS_sid4 (PI_typ pinfo) v1
               (value_id (PI_id pinfo)) align0 :: cs4 = cs3) as EQ'.
        admit. (* uniqness *)
      destruct EQ'; subst. clear H.
      exists SAS_tail0. exists nil. simpl_env. auto.
Qed.

Lemma mstore_unremovable_mem_simulation: forall (maxb : Z) (pinfo : PhiInfo)
  (sasinfo : SASInfo pinfo) (gl2 : GVMap) (tmn2 : terminator) 
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
  (Hmsim : mem_simulation pinfo sasinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := B;
             Opsem.CurCmds := insn_store sid t v1 v2 align0 :: cs;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: EC) Mem M2)
  (Hnrem : ~
          removable_State pinfo sasinfo
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
  mem_simulation pinfo sasinfo (los, nts)
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
    unfold sas_mem_inj in *.
    inv_mbind.
    intros ombs Hin'.
    assert ((PI_f pinfo = F -> 
              getCmdLoc (insn_store sid t v1 v2 align0) = 
                SAS_sid2 pinfo sasinfo) \/
            (PI_f pinfo = F -> 
              getCmdLoc (insn_store sid t v1 v2 align0) <> 
                SAS_sid2 pinfo sasinfo)) as Hdec.
      simpl.
      destruct (id_dec sid (SAS_sid2 pinfo sasinfo)); auto.
    destruct Hdec as [Heq | Hneq].
    SSCase "sid = SAS_sid2".
      inv Hin'.
      destruct (fdef_dec (PI_f pinfo) F); subst.
        SSSCase "PI_f = F".
        simpl in Heq. rewrite Heq in *; auto. clear Heq.
        assert (y = None) as EQ. 
          clear - H1 Heq3.
          eapply SAS_sid2_isnt_in_SAS_tail; eauto.
        subst. simpl.
        assert (v2 = value_id (PI_id pinfo) /\ t = PI_typ pinfo) as EQ. 
          clear - Heq3 HBinF1.
          destruct Heq3 as [l1 [ps1 [cs11 Heq3]]].
          admit. (* uniqness SAS *)
        destruct EQ; subst.
        simpl in H25.
        assert (ofs' = Int.repr 31 0) as EQ. 
          apply Hinscope' in H25. clear - H25.
          destruct H25 as [[_ [[mb [H25 _]] _]] _].
          rewrite Promotability.simpl_blk2GV in H25. inv H25. auto.            
        subst.
        assert (in_SAS_tails pinfo sasinfo (Some b'::l') (los, nts)
                 ({|Opsem.CurFunction := PI_f pinfo;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := 
                      insn_store (SAS_sid2 pinfo sasinfo) (PI_typ pinfo) v1 
                        (value_id (PI_id pinfo)) align0::cs;
                    Opsem.Terminator := tmn2;
                    Opsem.Locals := lc2;
                    Opsem.Allocas := als2 |} :: EC)) as Hin.
          constructor; auto.
            clear - H25 Heq3.
            eapply SAS_sid2_is_in_SAS_tail; eauto.
        apply_clear Hmsim2 in Hin. simpl in Hin.
        assert (n = sizeGenericValue gv1) as EQ. 
          clear - Hwflc1 Hwfv HeqR H24 Hwfg.
          eapply wf__getTypeStoreSize_eq_sizeGenericValue; eauto.
        rewrite EQ in *. clear EQ. 
        eapply SASmsim.mstore_aux_inject_id_inside_inj2; eauto.
        rewrite Int.signed_repr; auto using Promotability.min_le_zero_le_max.
  
        SSSCase "PI_f <> F".
        assert (y = None) as EQ. 
          destruct H1 as [_ H1].
          apply H1.
          intros [J1 _]. simpl in J1. congruence.
        subst. simpl.
        assert (in_SAS_tails pinfo sasinfo (None::l') (los, nts)
                 ({|Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := 
                      insn_store sid t v1 v2 align0::cs;
                    Opsem.Terminator := tmn2;
                    Opsem.Locals := lc2;
                    Opsem.Allocas := als2 |} :: EC)) as Hin.
          constructor; auto.
            split; intro J; simpl; auto.
              destruct J as [J _]. simpl in J. congruence.
        apply_clear Hmsim2 in Hin. simpl in Hin.
        eapply SASmsim.mstore_aux_inject_id_mapped_inj2; eauto.
  
    SSCase "sid <> SAS_sid2".
      assert (in_SAS_tails pinfo sasinfo ombs (los, nts)
               ({|Opsem.CurFunction := F;
                  Opsem.CurBB := B;
                  Opsem.CurCmds := insn_store sid t v1 v2 align0 :: cs;
                  Opsem.Terminator := tmn2;
                  Opsem.Locals := lc2;
                  Opsem.Allocas := als2 |} :: EC)) as Hin.
        inv Hin'.
        constructor; auto.
        eapply in_SAS_tail_update; eauto using unremovable_loc__neq__SAS_sid1.
      apply_clear Hmsim2 in Hin.
      eapply SASmsim.mstore_aux_inject_id_mapped_inj2; eauto.
Qed.

Lemma sas_is_sim : forall maxb pinfo (sasinfo: SASInfo pinfo) Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hsim: State_simulation pinfo sasinfo Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State pinfo sasinfo St1) St1' tr1
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1),
     State_simulation pinfo sasinfo Cfg1 St1' Cfg2 St2 /\ tr1 = E0) /\
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
  destruct ECs1 as [|[F1 B1 [|c1 cs1] tmn1 lc1 als1] ECs1]; tinv Hrem.
  destruct_cmd c1; tinv Hrem.
  simpl in Hrem.
  destruct (fdef_dec (PI_f pinfo) F1); subst; tinv Hrem.
  destruct (id_dec i0 (SAS_sid1 pinfo sasinfo)); subst; tinv Hrem.
  
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
    eapply mstore_removable_mem_simulation in Hmsim;
      eauto using wf_system__uniqFdef.

Case "unremovable state".
  (sInsn_cases (destruct Hop1) SCase).

SCase "sReturn".
Focus.
  destruct_ctx_return.
  repeat_solve.
    clear - H26 Hmsim H0 H1 Heq3'.
    eapply mem_simulation__return; eauto.
      admit. (* pid <> i0 *)

Unfocus.

SCase "sReturnVoid".
Focus.
  destruct_ctx_return.
  repeat_solve.
    clear - H24 Hmsim H0 Heq3'.
    eapply mem_simulation__return; eauto.
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
    eapply switchToNewBasicBlock_mem_simulation; eauto.

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
    eapply switchToNewBasicBlock_mem_simulation; eauto.

Unfocus.

SCase "sBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExtractValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sInsertValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sMalloc".
  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  assert (mb0 = mb) as EQ.
    destruct Hmsim as [Hmsim _].
    apply MemProps.malloc_result in H25.
    apply MemProps.malloc_result in H2. subst. auto.
  subst.
  repeat_solve.
    clear - H2 H25 Heq3 Hnrem Hmsim.
    eapply mem_simulation__malloc; eauto; simpl; auto.

SCase "sFree".
  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    eapply mem_simulation__free; eauto.
    eapply mem_simulation__replace_head in Hmsim; eauto.
    intros omb Hin.
      eapply in_SAS_tail_update; eauto using unremovable_loc__neq__SAS_sid1, 
                                             unremovable_loc__neq__SAS_sid2.
        simpl. admit. (* uniqness *)

SCase "sAlloca".

  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  assert (mb0 = mb) as EQ.
    destruct Hmsim as [Hmsim _].
    apply MemProps.malloc_result in H25.
    apply MemProps.malloc_result in H2. subst. auto.
  subst.
  repeat_solve.
    clear - H2 H25 Heq3 Hnrem Hmsim.
    eapply mem_simulation__malloc; eauto; simpl; auto.

SCase "sLoad".
  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  assert (gv = gv0) as EQ.
    assert (wf_value S (module_intro los nts Ps) F v (typ_pointer t)) as Hwfv.
      admit. (* wf *)
    clear - H23 Hmsim H1 H21 HwfHT Hinscope' Hwfmg Hwfv. simpl in *.
    eapply mem_simulation__mload; eauto.
  subst.
  repeat_solve.
    eapply mem_simulation_update_locals in Hmsim; simpl; 
      eauto using unremovable_loc__neq__SAS_sid1, unremovable_loc__neq__SAS_sid2.
      admit. (* lid <> pid *)

SCase "sStore".

  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
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

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    destruct (isGVZero (los,nts) c).
      eapply mem_simulation_update_locals in Hmsim; simpl; 
        eauto using unremovable_loc__neq__SAS_sid1, unremovable_loc__neq__SAS_sid2.
        simpl. intros.
        admit. (* lid <> pid *)
      eapply mem_simulation_update_locals in Hmsim; simpl;
        eauto using unremovable_loc__neq__SAS_sid1, unremovable_loc__neq__SAS_sid2.
        simpl. intros.
        admit. (* lid <> pid *)

SCase "sCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.

  inv Hop2.

  SSCase "SCall".

  uniq_result.
  assert (Hfsim1:=Hpsim).
  eapply lookupFdefViaPtr__simulation in Hfsim1; eauto.

  assert (Hbsim1:=Hfsim1).
  eapply fdef_simulation__entry_block_simulation in Hbsim1; eauto.

  assert (InProductsB (product_fdef (fdef_intro
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    apply OpsemAux.lookupFdefViaPtr_inversion in H1.
    destruct H1 as [fn [H11 H12]].
    eapply lookupFdefViaIDFromProducts_inv; eauto.
  assert (uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
    as Huniq.
    eapply wf_system__uniqFdef; eauto.
  assert (Hbsim1':=Hbsim1).
  apply block_simulation_inv in Hbsim1'; auto using entryBlockInFdef.
  destruct Hbsim1' as [Heq' [Hpsim1' [Hcsim1' Htsim1']]]; subst.
  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    apply fdef_simulation_inv in Hfsim1.
    destruct Hfsim1 as [Heq _]. inv Heq. uniq_result.
    auto.

    clear - Hmsim.
    apply mem_simulation__call; auto.

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
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.

  inv Hop2.

  SSCase "SCall".

  uniq_result.

  match goal with
  | Hpsim: products_simulation _ _ ?Ps ?Ps2,
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
  eapply callExternalFunction__mem_simulation in Hmsim; eauto.
  destruct Hmsim as [EQ [Hmsim EQ']]; subst.
  uniq_result.
  repeat_solve.
    eapply mem_simulation_update_locals in Hmsim; simpl;
      eauto using unremovable_loc__neq__SAS_sid1.
      admit. (* rid <> pid *)  admit. (* cid <> pid *)

Transparent inscope_of_tmn inscope_of_cmd.

Qed.

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
  (Hfinal: Opsem.s_isFinialState cfg2 FS2 = ret r),
  Opsem.s_isFinialState cfg1 FS1 = ret r.
Admitted.

Lemma opsem_s_isFinialState__sas_State_simulation: forall
  pinfo sasinfo cfg1 FS1 cfg2 FS2
  (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2),
  Opsem.s_isFinialState cfg1 FS1 = Opsem.s_isFinialState cfg2 FS2.
Admitted.

Lemma undefined_state__sas_State_simulation: forall pinfo sasinfo cfg1 St1 cfg2
  St2 (Hstsim : State_simulation pinfo sasinfo cfg1 St1 cfg2 St2),
  OpsemPP.undefined_state cfg1 St1 -> OpsemPP.undefined_state cfg2 St2.
Admitted.

Lemma sop_star__sas_State_simulation: forall pinfo sasinfo cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) 
  (Hwfcfg: OpsemPP.wf_Config cfg1) maxb
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

      assert (OpsemPP.wf_State cfg1 IS1' /\ OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
        apply OpsemPP.preservation in Hop1; auto.
      assert (Promotability.wf_State maxb pinfo cfg1 IS1') as Hnoalias'.
        eapply Promotability.preservation in Hop1; eauto; try tauto.
      eapply sas_is_sim in Hstsim; eauto.
      destruct Hstsim as [Hstsim1 Hstsim2].
      destruct (@removable_State_dec pinfo sasinfo IS1) as [Hrm | Hnrm].
        eapply Hstsim1 in Hrm; eauto.
        destruct Hrm as [Hstsim EQ]; subst.
        admit. (* we should do induction on the measure of State_simulation *)

        eapply Hstsim2 in Hnrm; eauto.
        destruct Hnrm as [Hstsim EQ]; subst.
        eapply IHHopstar in Hstsim; eauto; try tauto.
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
     wf_system 
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
    assert (OpsemPP.wf_Config cfg1 /\ OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    assert (exists maxb,
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom.
      eapply Promotability.s_genInitState__wf_globals_promotable; eauto.
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]].
    eapply sop_star__sas_State_simulation in Hstsim; eauto; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    eapply s_isFinialState__sas_State_simulation in Hstsim'; eauto.
    econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    eapply s_genInitState__sas_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]].  
    assert (OpsemPP.wf_Config cfg1 /\ OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    assert (exists maxb,
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom.
      eapply Promotability.s_genInitState__wf_globals_promotable; eauto.
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]].
    eapply sop_div__sas_State_simulation in Hstsim; eauto; try tauto.
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
     wf_system 
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
  wf_system 
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
     wf_system 
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

