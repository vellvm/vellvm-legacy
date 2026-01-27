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
Require Import memory_props.
Require Import vmem2reg.
Require Import trans_tactic.
Require Import sas_msim.
Require Import memory_sim.
Require Import top_sim.
Require Import partitioning.

(***************************************************************************)
(* Define sas by partitioning 
  We allow the stores use different alignments from (PI_align pinfo). See
  the comments in alivs_store.
*)
Definition sas (sid1 sid2: id) (align1 align2: align) (v1 v2:value) (cs2:cmds) 
  (b:block) (pinfo:PhiInfo) : Prop :=
partitioning 
   (insn_store sid1 (PI_typ pinfo) v1 (value_id (PI_id pinfo)) align1)
   (insn_store sid2 (PI_typ pinfo) v2 (value_id (PI_id pinfo)) align2)
   cs2 b pinfo
   (fun cs2 pinfo => load_in_cmds (PI_id pinfo) cs2 = false).

Record SASInfo (pinfo: PhiInfo) := mkSASInfo {
  SAS_sid1 : id;
  SAS_sid2 : id;
  SAS_align1 : align;
  SAS_align2 : align;
  SAS_value1 : value;
  SAS_value2 : value;
  SAS_tail : cmds;
  SAS_block : block;
  SAS_prop: sas SAS_sid1 SAS_sid2 SAS_align1 SAS_align2 SAS_value1 SAS_value2 
    SAS_tail SAS_block pinfo
}.

Ltac destruct_sasinfo :=
match goal with
| sasinfo: SASInfo _ |- _ =>
  destruct sasinfo as [SAS_sid1 SAS_sid2 SAS_align1 SAS_align2 SAS_value1 
                       SAS_value2 SAS_tail0
                       [SAS_l0 [SAS_ps0 SAS_cs0 SAS_tmn0]] SAS_prop0];
  destruct SAS_prop0 as 
    [SAS_BInF0 [SAS_ldincmds0 [SAS_cs1 [SAS_cs3 SAS_EQ]]]]; subst; simpl
end.

Ltac destruct_sasinfo' :=
match goal with
| sasinfo: SASInfo _ |- _ =>
  destruct sasinfo as [SAS_sid1 SAS_sid2 SAS_align1 SAS_align2 SAS_value1 
                       SAS_value2 SAS_tail0
                       [SAS_l0 [SAS_ps0 SAS_cs0 SAS_tmn0]] SAS_prop0];
  simpl
end.

(***************************************************************************)
(* Simulation relations. *) 

Definition fdef_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) f1 f2
  : Prop :=
RemoveSim.fdef_simulation (PI_f pinfo) (SAS_sid1 pinfo sasinfo) f1 f2.

Definition cmds_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) (f1:fdef)
  cs1 cs2 : Prop :=
RemoveSim.cmds_simulation (PI_f pinfo) (SAS_sid1 pinfo sasinfo) f1 cs1 cs2.

Definition block_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) (f1:fdef)
  b1 b2 : Prop :=
RemoveSim.block_simulation (PI_f pinfo) (SAS_sid1 pinfo sasinfo) f1 b1 b2.

Definition Fsim (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) := mkFunSim 
(fdef_simulation pinfo sasinfo)
(RemoveSim.fdef_simulation__eq_fheader (PI_f pinfo) (SAS_sid1 pinfo sasinfo))
(RemoveSim.fdef_simulation__det_right (PI_f pinfo) (SAS_sid1 pinfo sasinfo))
.

Definition products_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  Ps1 Ps2 : Prop :=
@TopSim.products_simulation (Fsim pinfo sasinfo) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  S1 S2 : Prop :=
@TopSim.system_simulation (Fsim pinfo sasinfo) S1 S2.

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
         b1 = (l1, stmts_intro ps1 (cs11++cs1) tmn1))
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = (l2, stmts_intro ps2 (cs21++cs2) tmn2)) /\
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

(* cs follows the overwritten store *) 
Definition cs_follow_dead_store (pinfo:PhiInfo) (sasinfo: SASInfo pinfo)
  (cs:cmds) : Prop :=
let '(_, stmts_intro _ cs0 _) := SAS_block pinfo sasinfo in
forall cs1 cs3,
  cs0 =
  cs1 ++
    insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo)
      (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) 
      (SAS_align1 pinfo sasinfo) ::
    SAS_tail pinfo sasinfo ++
    cs3 ->
  (exists csa, exists csb,
    cs = csb ++ cs3 /\ SAS_tail pinfo sasinfo = csa ++ csb).

(* The current pc follows the overwritten store *)
Definition EC_follow_dead_store (pinfo:PhiInfo) (sasinfo: SASInfo pinfo)
  (ec:@Opsem.ExecutionContext DGVs) : Prop :=
Opsem.CurFunction ec = PI_f pinfo /\
Opsem.CurBB ec = SAS_block pinfo sasinfo /\
cs_follow_dead_store pinfo sasinfo (Opsem.CurCmds ec).

(* Check ignorable locations.

   If the current pc ec0 follows the overwritten store, 
     omb equals to the promotable location, 
     which is called an ignorable location;
   otherwise, omb is None.
*)
Definition in_SAS_tail (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) 
  (omb: option Values.block) (TD:TargetData) (ec0:@Opsem.ExecutionContext DGVs)
  : Prop:=
  (EC_follow_dead_store pinfo sasinfo ec0 -> 
     match lookupAL _ (Opsem.Locals ec0) (PI_id pinfo) with
     | Some ((Vptr mb _, _)::nil) => omb = Some mb
     | _ => omb = None
     end) /\
  (~EC_follow_dead_store pinfo sasinfo ec0 -> omb = None).

(* Find all ignorable locations from stack *)
Definition in_SAS_tails (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) 
  (ombs:list (option Values.block)) TD (ecs:list Opsem.ExecutionContext) 
  : Prop :=
List.Forall2 (fun ec omb => 
              in_SAS_tail pinfo sasinfo omb TD ec) ecs ombs.

(* Memory simulation:
   Data stored at ignorable locations do not need to match;
   others need to match. *)
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

(***************************************************************************)
(* States whose pc is removable. *)
Definition removable_State (pinfo: PhiInfo) (sasinfo: SASInfo pinfo)
  (St:@Opsem.State DGVs) : Prop :=
RemoveSim.removable_State (PI_f pinfo) (SAS_sid1 pinfo sasinfo) St.

(***************************************************************************)
(* Instantiate properties of partitioning to SAS *)

Lemma SAS_lid1__in_SAS_block_locs: forall pinfo sasinfo,
  In (SAS_sid1 pinfo sasinfo) (getStmtsLocs (snd (SAS_block pinfo sasinfo))).
Proof.
  intros.
  destruct_sasinfo'.
  eapply par_id1__in_block_locs in SAS_prop0; eauto.
Qed.

Lemma SAS_lid2__in_SAS_block_locs: forall pinfo sasinfo,
  In (SAS_sid2 pinfo sasinfo) (getStmtsLocs (snd (SAS_block pinfo sasinfo))).
Proof.
  intros.
  destruct_sasinfo'.
  eapply par_id2__in_block_locs in SAS_prop0; eauto.
Qed.

Lemma SAS_block_spec: forall B pinfo sasinfo (Huniq: uniqFdef (PI_f pinfo))
  (HBinF: blockInFdefB B (PI_f pinfo))
  (Hin: In (SAS_sid1 pinfo sasinfo) (getStmtsLocs (snd B)) \/
          In (SAS_sid2 pinfo sasinfo) (getStmtsLocs (snd B))),
  B = SAS_block pinfo sasinfo.
Proof.
  intros.
  destruct_sasinfo'.
  eapply par_block_eq in HBinF; eauto.
Qed.

Lemma lookup_SAS_lid1__store: forall l1 ps1 cs1 pinfo sasinfo
  (HuniqF: uniqFdef (PI_f pinfo)) tmn1
  (HBinF: blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) (PI_f pinfo)) c
  (Hin: In c cs1) (Heq: getCmdLoc c = SAS_sid1 pinfo sasinfo),
  c = insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
        (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) 
        (SAS_align1 pinfo sasinfo).
Proof.
  intros.
  destruct_sasinfo'.
  eapply par_id1__eq__c1 in Hin; eauto.
Qed.

Lemma lookup_SAS_lid2__store: forall l1 ps1 cs1 pinfo sasinfo
  (HuniqF: uniqFdef (PI_f pinfo)) tmn1
  (HBinF: blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) (PI_f pinfo)) c
  (Hin: In c cs1) (Heq: getCmdLoc c = SAS_sid2 pinfo sasinfo),
  c = insn_store (SAS_sid2 pinfo sasinfo) (PI_typ pinfo) 
        (SAS_value2 pinfo sasinfo) (value_id (PI_id pinfo))
        (SAS_align2 pinfo sasinfo).
Proof.
  intros.
  destruct_sasinfo'.
  eapply par_id2__eq__c2 in Hin; eauto.
Qed.

Lemma SAS_blockInFdefB: forall pinfo sasinfo,
  blockInFdefB (SAS_block pinfo sasinfo) (PI_f pinfo) = true.
Proof.
  intros.
  destruct_sasinfo. auto.
Qed.

Lemma SAS_block_inv1: forall l1 ps1 cs11 t1 v1 v2 cs tmn2 align0 pinfo
  sasinfo (Huniq: uniqFdef (PI_f pinfo))
  (EQ : (l1, stmts_intro ps1
         (cs11 ++
          insn_store (SAS_sid1 pinfo sasinfo) t1 v1 v2 align0 :: cs) tmn2) =
        SAS_block pinfo sasinfo),
  insn_store (SAS_sid1 pinfo sasinfo) t1 v1 v2 align0 =
    insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
      (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) 
      (SAS_align1 pinfo sasinfo) /\
  exists cs3, 
    cs = 
     SAS_tail pinfo sasinfo ++
     insn_store (SAS_sid2 pinfo sasinfo) (PI_typ pinfo) 
       (SAS_value2 pinfo sasinfo) (value_id (PI_id pinfo)) 
       (SAS_align2 pinfo sasinfo) 
     :: cs3.
Proof.
  intros.  
  destruct_sasinfo'.
  eapply par_block_inv1 in EQ; eauto.
Qed.

Lemma lookup_SAS_lid1__cmd: forall pinfo sasinfo (Huniq : uniqFdef (PI_f pinfo)),
  lookupInsnViaIDFromFdef (PI_f pinfo) (SAS_sid1 pinfo sasinfo) =
    ret insn_cmd
          (insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo)
            (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo))
            (SAS_align1 pinfo sasinfo)).
Proof.
  intros.
  destruct_sasinfo'.
  eapply par_lookup_id1__c1 in SAS_prop0; eauto.
Qed.

Lemma SAS_block_inv2: forall l1 ps1 cs11 t1 v1 v2 cs tmn2 align0 pinfo
  sasinfo (Huniq: uniqFdef (PI_f pinfo))
  (EQ : (l1, (stmts_intro ps1
         (cs ++
          insn_store (SAS_sid2 pinfo sasinfo) t1 v1 v2 align0 :: cs11) tmn2)) =
        SAS_block pinfo sasinfo),
  insn_store (SAS_sid2 pinfo sasinfo) t1 v1 v2 align0 =
    insn_store (SAS_sid2 pinfo sasinfo) (PI_typ pinfo) 
      (SAS_value2 pinfo sasinfo) (value_id (PI_id pinfo)) 
      (SAS_align2 pinfo sasinfo) /\
  exists cs3, 
    cs = 
     cs3 ++
     insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
       (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) 
       (SAS_align1 pinfo sasinfo) ::
     SAS_tail pinfo sasinfo.
Proof.
  intros.  
  destruct_sasinfo'.
  eapply par_block_inv2 in EQ; eauto.
Qed.

(***************************************************************************)
(* More properties for SAS. *)
Lemma SAS_sid1__isnt__phi: forall (pinfo : PhiInfo) sasinfo (ps1 : phinodes) 
  (l1 : l) (cs1 : cmds) (tmn1 : terminator)
  (HBinF : blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) (PI_f pinfo) = true)
  (H0 : uniqFdef (PI_f pinfo)),
  ~ In (SAS_sid1 pinfo sasinfo) (getPhiNodesIDs ps1).
Proof.
  intros.
  intro Hin.
  assert (J:=HBinF).
  apply blockInFdefB_lookupBlockViaLabelFromFdef in J; auto.
  eapply phinode_isnt_cmd with (c1:=
    insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
        (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) 
        (SAS_align1 pinfo sasinfo)) in Hin; eauto.
  eapply lookup_SAS_lid1__cmd; eauto.
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
Proof.
  intros. subst. unfold removable_State in Hnrem.
  apply RemoveSim.not_removable_State_inv in Hnrem.
  destruct Hnrem as [Hnrem | Hnrem]; try congruence.
Qed.

Lemma unstore_loc__neq__SAS_sid2: forall pinfo sasinfo F B c cs tmn2 id0
  (Hnst: match c with
         | insn_store _ _ _ _ _ => False
         | _ => True
         end) (Huniq: uniqFdef F)
  (Hex: exists l0, exists ps0, exists cs0, 
          B = (l0, stmts_intro ps0 (cs0 ++ c :: cs) tmn2)) 
  (HBinF: blockInFdefB B F = true) (EQ : id0 = getCmdLoc c),
  PI_f pinfo = F -> id0 <> SAS_sid2 pinfo sasinfo.
Proof.
  intros. subst.
  destruct Hex as [l0 [ps0 [cs0 Hex]]]; subst.
  intro J. subst.
  eapply lookup_SAS_lid2__store in HBinF; eauto using in_middle.
  subst. auto.
Qed.

Lemma unstore_loc__neq__SAS_sid1: forall pinfo sasinfo F B c cs tmn2 id0
  (Hnst: match c with
         | insn_store _ _ _ _ _ => False
         | _ => True
         end) (Huniq: uniqFdef F)
  (Hex: exists l0, exists ps0, exists cs0, 
          B = (l0, stmts_intro ps0 (cs0 ++ c :: cs) tmn2)) 
  (HBinF: blockInFdefB B F = true) (EQ : id0 = getCmdLoc c),
  PI_f pinfo = F -> id0 <> SAS_sid1 pinfo sasinfo.
Proof.
  intros. subst.
  destruct Hex as [l0 [ps0 [cs0 Hex]]]; subst.
  intro J. subst.
  eapply lookup_SAS_lid1__store in HBinF; eauto using in_middle.
  subst. auto.
Qed.

Lemma remove_phinodes_eq: forall pinfo sasinfo l0 ps0 cs0 tmn0,
  uniqFdef (PI_f pinfo) ->
  blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) (PI_f pinfo) ->
  remove_phinodes (SAS_sid1 pinfo sasinfo) ps0 = ps0.
Proof.
  intros.
  rewrite <- remove_phinodes_stable; auto.
  eapply SAS_sid1__isnt__phi; eauto.
Qed.

(***************************************************************************)
(* Properties of cs_follow_dead_store *)
Lemma cs_follow_dead_store_isnt_nil: forall pinfo sasinfo,
  cs_follow_dead_store pinfo sasinfo nil -> False.
Proof.
  intros.
  unfold cs_follow_dead_store in H.
  destruct sasinfo. simpl in *.
  destruct SAS_block0 as [? []].
  destruct SAS_prop0 as [J1 [J4 [cs1 [cs2 EQ]]]].
  apply H in EQ.
  destruct EQ as [csa [csb [EQ1 EQ2]]].
  symmetry in EQ1.
  apply app_eq_nil in EQ1. destruct EQ1 as [EQ11 EQ12]. inv EQ12.
Qed.

Lemma cs_follow_dead_store_tail: forall pinfo sasinfo c cs 
  (Huniq: uniqFdef (PI_f pinfo)),
  getCmdLoc c <> SAS_sid2 pinfo sasinfo ->
  cs_follow_dead_store pinfo sasinfo (c :: cs) ->
  cs_follow_dead_store pinfo sasinfo cs.
Proof.
  unfold cs_follow_dead_store.
  intros. 
  remember (SAS_block pinfo sasinfo) as R.
  destruct R as [? [? cs0 ?]]. intros. subst.
  eapply SAS_block_inv1 in HeqR; eauto.
  destruct HeqR as [EQa [cs4 EQb]]; subst.
  inv EQa. 
  apply app_inv_head in EQb. subst. 
  edestruct H0 as [csa [csb [J1 J2]]]; subst; eauto.
  destruct csb.
    inv J1. contradict H; auto.

    inv J1. exists (csa++[c0]). exists csb. simpl_env. split; auto.
Qed.

Lemma cs_follow_dead_store_tail': forall pinfo sasinfo c cs
  (Huniq: uniqFdef (PI_f pinfo))
  (Hex: exists l0, exists ps0, exists tmn0, exists cs0,
          SAS_block pinfo sasinfo = (l0, stmts_intro ps0 (cs0++c::cs) tmn0)),
  getCmdLoc c <> SAS_sid1 pinfo sasinfo ->
  cs_follow_dead_store pinfo sasinfo cs ->
  cs_follow_dead_store pinfo sasinfo (c :: cs).
Proof.
  unfold cs_follow_dead_store.
  intros. 
  remember (SAS_block pinfo sasinfo) as R.
  destruct R as [? [? cs0 ?]]. intros. subst.
  eapply SAS_block_inv1 in HeqR; eauto.
  destruct HeqR as [EQa [cs4 EQb]]; subst.
  inv EQa. 
  apply app_inv_head in EQb. subst.
  edestruct H0 as [csa [csb [J1 J2]]]; eauto; subst. clear H0.
  destruct Hex as [l1 [ps0 [tmn0 [cs0 Hex]]]].
  inv Hex.
  simpl_env in H3. rewrite J2 in H3.
  anti_simpl_env. 
  destruct csa.
    simpl_env in H3.
    anti_simpl_env.  
    simpl in H. congruence.

    assert (exists csa', c0 :: csa = csa' ++ [c]) as EQ.
      anti_simpl_env.
    
      match goal with
      | H: ((?A ++ [?b]) ++ [?c]) ++ ?D = _ |- _ =>
           rewrite_env ((A ++ [b]) ++ [c] ++ D) in H
      end.
      eapply list_prop1; eauto.
    destruct EQ as [csa' EQ].
    rewrite J2. rewrite EQ.
    exists csa'. exists (c::csb).
    simpl_env.
    split; auto.
Qed.

Lemma cs_follow_dead_store_at_beginning_false: forall (pinfo : PhiInfo)
  (sasinfo : SASInfo pinfo) (l' : l) (ps' : phinodes) (cs' : cmds)
  (tmn' : terminator)
  (J2 : (l', stmts_intro ps' cs' tmn') = SAS_block pinfo sasinfo)
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
         (value_id (PI_id pinfo)) SAS_align3 :: (csa ++ csb)) ++
     insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
            (value_id (PI_id pinfo)) SAS_align4 :: cs3
    ) in J'.
  apply app_inv_tail in J'.
  rewrite_env (nil ++ csb) in J'.
  rewrite_env (
    (cs1 ++
       insn_store SAS_sid3 (PI_typ pinfo) SAS_value3
         (value_id (PI_id pinfo)) SAS_align3 ::
       csa) ++ csb
    ) in J'.
  apply app_inv_tail in J'.
  assert (
    In (insn_store SAS_sid3 (PI_typ pinfo) SAS_value3
         (value_id (PI_id pinfo)) SAS_align3) nil) as Hin.
    rewrite J'. apply in_middle.
  inv Hin.
Qed.

Lemma cs_follow_dead_store_at_end_false: forall (pinfo : PhiInfo)
  (sasinfo : SASInfo pinfo) (J3 : cs_follow_dead_store pinfo sasinfo nil),
  False.
Proof.
  intros.
  unfold cs_follow_dead_store in J3.
  destruct sasinfo. simpl in *. destruct SAS_block0 as [? []].
  destruct SAS_prop0 as [_ [_ [cs1 [cs3 J]]]].
  assert (J':=J).
  apply J3 in J.
  destruct J as [csa [csb [EQ1 EQ2]]]; subst.
  assert (
    In (insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
         (value_id (PI_id pinfo)) SAS_align4) nil) as Hin.
    rewrite EQ1. apply in_middle.
  inv Hin.
Qed.

Lemma cs_follow_dead_store_dec: forall (pinfo : PhiInfo) 
  (sasinfo : SASInfo pinfo) (EC : @Opsem.ExecutionContext DGVs)
  (Ha : Opsem.CurFunction EC = PI_f pinfo) 
  (Hb : Opsem.CurBB EC = SAS_block pinfo sasinfo)
  (Huniq: uniqEC EC),
  cs_follow_dead_store pinfo sasinfo (Opsem.CurCmds EC) \/
    ~ cs_follow_dead_store pinfo sasinfo (Opsem.CurCmds EC).
Proof.
  destruct EC. simpl. destruct sasinfo.
  simpl. destruct pinfo. simpl in *.
  intros. subst.
  unfold sas in SAS_prop0. simpl in *.
  destruct SAS_prop0 as [J1 [J2 J3]].
  destruct SAS_block0 as [l5 []].
  destruct J3 as [cs1 [cs3 J3]]; subst. 
  unfold cs_follow_dead_store. simpl.
  destruct Huniq as [Huniq [_ Hex]].
  clear - Hex J1 Huniq. simpl in *.
  destruct (@list_suffix_dec _ cmd_dec CurCmds
    (insn_store SAS_sid4 PI_typ SAS_value4 (value_id PI_id) SAS_align4 :: cs3))
    as [J | J].
    destruct J as [l3 J]; subst.
    destruct (@list_suffix_dec _ cmd_dec SAS_tail0 l3) as [J' | J'].
      destruct J' as [l4 J']; subst.
      left.
      intros.
      assert (cs2=insn_store SAS_sid4 PI_typ SAS_value4 (value_id PI_id) 
                    SAS_align4 :: cs3 ) as EQ.
        apply NoDup_cmds_split_middle in H; auto.
        destruct H; subst.
        apply app_inv_head in H0. auto.

        solve_NoDup.
      subst.
      exists l4. exists l3. auto.

      right.
      intro J.
      destruct (@J cs1 
                   (insn_store SAS_sid4 PI_typ SAS_value4 
                     (value_id PI_id) SAS_align4 :: cs3))
        as [csa1 [csb1 [J1' J2]]]; subst; auto.
      clear J.
      assert (l3 = csb1) as EQ. 
        apply NoDup_cmds_split_middle in J1'; auto.
          destruct J1'; auto.
          rewrite J1'.
          destruct Hex as [l0 [ps0 [cs0 Hex]]].
          rewrite Hex in J1. rewrite <- J1'.

          apply uniqFdef__uniqBlockLocs in J1; auto.
          simpl in J1. simpl_locs_in_ctx. split_NoDup. auto.
      subst.
      apply J'. exists csa1. auto.

    right.
    intro J'.
    destruct (@J' cs1 
                  (insn_store SAS_sid4 PI_typ SAS_value4 
                    (value_id PI_id) SAS_align4 :: cs3))
      as [csa1 [csb1 [J1' J2]]]; subst; auto.
    clear J'.
    apply J. exists csb1. auto.
Qed.

(***************************************************************************)
(* Properties of EC_follow_dead_store *)

Lemma EC_follow_dead_store_dec: forall pinfo sasinfo EC
  (Huniq: uniqEC EC),
  EC_follow_dead_store pinfo sasinfo EC \/ 
    ~ EC_follow_dead_store pinfo sasinfo EC.
Proof.
  intros.
  unfold EC_follow_dead_store.
  destruct (fdef_dec (Opsem.CurFunction EC) (PI_f pinfo)); 
    try solve [right; tauto].
  destruct (block_dec (Opsem.CurBB EC) (SAS_block pinfo sasinfo)); 
    try solve [right; tauto].
  destruct (cs_follow_dead_store_dec pinfo sasinfo EC e e0 Huniq);
    try solve [right; tauto | auto].
Qed.

Lemma EC_follow_dead_store_tail: forall pinfo sasinfo c cs B tmn3 lc1 als3 als3'
  lc2 F (Heq: PI_f pinfo = F -> getCmdLoc c <> SAS_sid2 pinfo sasinfo)
  (Huniq: uniqFdef F),
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
  intro J. apply H.
  destruct J as [J1 [J2 J3]]. simpl in *.
  split; auto.
  split; auto.
    simpl. subst.
    eapply cs_follow_dead_store_tail; eauto.
Qed.

Lemma EC_follow_dead_store_tail':forall pinfo sasinfo c cs B tmn3 lc1 als3 als3'
  lc2 F (Heq: PI_f pinfo = F -> getCmdLoc c <> SAS_sid2 pinfo sasinfo)
  (Huniq: uniqFdef F),
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
  destruct H as [J1 [J2 J3]]. simpl in *. subst.
  split; auto.
  split; auto.
    simpl. subst.
    eapply cs_follow_dead_store_tail; eauto.
Qed.

Lemma EC_follow_dead_store_tail'':forall pinfo sasinfo c cs B tmn3 lc1 als3 als3'
  lc2 F
  (Hex: exists l0, exists ps0, exists cs0,
          B = (l0, stmts_intro ps0 (cs0++c::cs) tmn3))
  (Heq: PI_f pinfo = F -> getCmdLoc c <> SAS_sid1 pinfo sasinfo)
  (Huniq: uniqFdef F),
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
  destruct H as [J1 [J2 J3]]. simpl in *. subst.
  split; auto.
  split; auto.
    simpl. subst.
    eapply cs_follow_dead_store_tail'; eauto.
    destruct Hex as [l0 [ps0 [cs0 Hex]]].
    rewrite Hex. eauto.
Qed.

Lemma EC_follow_dead_store_at_begin_false: forall pinfo sasinfo F l' ps' cs' tmn'
  tmn lc2 als2,
  ~
  EC_follow_dead_store pinfo sasinfo
    {|
     Opsem.CurFunction := F;
     Opsem.CurBB := (l', stmts_intro ps' cs' tmn');
     Opsem.CurCmds := cs';
     Opsem.Terminator := tmn;
     Opsem.Locals := lc2;
     Opsem.Allocas := als2 |}.
Proof.
  intros. intro J.
  destruct J as [J1 [J2 J3]]. simpl in *.
  eapply cs_follow_dead_store_at_beginning_false in J3; eauto.
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

(***************************************************************************)
(* Properties of in_SAS_tail *)
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
    destruct SAS_block0 as [? [? cs0 ?]].
    destruct J6 as [cs2 [cs3 J6]]; subst.
    destruct (@J3 cs2 
                (insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
                  (value_id (PI_id pinfo)) SAS_align4 :: cs3)) as
      [csa [csb [J7 J8]]]; subst; auto.
    clear J3.
    simpl_env in J4. simpl_env in J7. rewrite <- J7 in J4.
    apply uniqFdef__uniqBlockLocs in J4; auto.
    simpl in J4. split_NoDup.
    simpl_locs_in_ctx.
    split_NoDup.
    inv Huniq4.
    contradict H1. repeat simpl_locs. solve_in_list.
Qed.

Lemma SAS_sid1_is_in_SAS_tail: forall (pinfo : PhiInfo) (sasinfo : SASInfo pinfo)
  (tmn2 : terminator) (lc2 : Opsem.GVsMap) (als2 : list mblock) (los : layouts)
  (nts : namedts) (B : block) (align0 : align) (v1 : value) (cs : list cmd)
  (b' : Values.block) (Huniq: uniqFdef (PI_f pinfo)) 
  (HBinF: blockInFdefB B (PI_f pinfo) = true)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               (l1, stmts_intro ps1
                 (cs11 ++
                  insn_store (SAS_sid1 pinfo sasinfo) 
                    (PI_typ pinfo) v1 (value_id (PI_id pinfo)) align0 :: cs)
                 tmn2))
  (H25 : lookupAL (GVsT DGVs) lc2 (PI_id pinfo) =
        ret ($ blk2GV (los, nts) b' # typ_pointer (PI_typ pinfo) $)) y
  (Hin: in_SAS_tail pinfo sasinfo y (los, nts)
     {|
     Opsem.CurFunction := PI_f pinfo;
     Opsem.CurBB := B;
     Opsem.CurCmds := cs;
     Opsem.Terminator := tmn2;
     Opsem.Locals := lc2;
     Opsem.Allocas := als2 |}),
  y = Some b'.
Proof.
  intros.
  destruct Hin as [J1 _]. simpl in *.
  rewrite H25 in J1. clear H25.
  apply J1. clear J1.
  destruct Heq3 as [l1 [ps1 [cs11 Heq3]]]. subst.
  split; auto. 
  assert ((l1, stmts_intro ps1
            (cs11 ++
              insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) v1
              (value_id (PI_id pinfo)) align0 :: cs) tmn2) = 
            SAS_block pinfo sasinfo) as EQ.
    apply SAS_block_spec; auto.
    simpl. repeat simpl_locs. left.
    xsolve_in_list.
  simpl.
  split; auto.
    unfold cs_follow_dead_store.
    rewrite <- EQ.
    intros.
    eapply SAS_block_inv1 in EQ; eauto.
    destruct EQ as [EQ1 EQ2]. inv EQ1.
    destruct EQ2 as [cs4 EQ2]; subst.
    exists nil. exists (SAS_tail pinfo sasinfo).
    split; auto.
      apply NoDup_cmds_split_middle in H; auto.
        destruct H; auto.
        solve_NoDup.
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

Lemma in_SAS_tail_update :
  forall pinfo sasinfo TD F B c cs tmn3 lc1 als3 als3' lc2 omb
  (Hneq: PI_f pinfo = F -> getCmdLoc c <> SAS_sid2 pinfo sasinfo)
  (Hneq': PI_f pinfo = F -> getCmdLoc c <> SAS_sid1 pinfo sasinfo)
  (Hex: exists l0, exists ps0, exists cs0,
          B = (l0, stmts_intro ps0 (cs0++c::cs) tmn3))
  (Hp: PI_f pinfo = F -> 
       lookupAL (GVsT DGVs) lc2 (PI_id pinfo) =
         lookupAL (GVsT DGVs) lc1 (PI_id pinfo))
  (Huniq: uniqFdef F)
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
  split; simpl in *; intros H.
    assert (W:=H). destruct W as [W _]. simpl in W.
    rewrite Hp; try congruence. subst.
    apply EC_follow_dead_store_tail' with (lc1:=lc1)(als3:=als3) in H; auto.
    apply H11; auto.

    apply H12.
    intro G. apply H. 
    eapply EC_follow_dead_store_tail''; eauto.
Qed.

Lemma in_SAS_tail_ex: forall pinfo sasinfo TD EC
  (Huniq: uniqEC EC),
  exists omb, in_SAS_tail pinfo sasinfo omb TD EC.
Proof.
  unfold in_SAS_tail.
  intros.
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC Huniq).
    destruct (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) 
      as [[|[[]][]]|]; eauto.
    exists (Some b). tauto.

    destruct (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) 
      as [[|[[]][]]|]; eauto.
    exists None. tauto.
Qed.

Lemma in_SAS_tails_ex: forall pinfo sasinfo TD ECs (Huniq: uniqECs ECs),
  exists ombs, in_SAS_tails pinfo sasinfo ombs TD ECs.
Proof.
  unfold in_SAS_tails.
  induction 1; simpl; eauto.
    destruct IHHuniq as [ombs IHECs].
    destruct (@in_SAS_tail_ex pinfo sasinfo TD x H) as [omb J].
    exists (omb::ombs). constructor; auto.
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

Lemma in_SAS_tail__wf_ECStack_head_in_tail__no_alias_with_blk: forall
  (pinfo : PhiInfo) (sasinfo : SASInfo pinfo) (lc2 : AssocList (GVsT DGVs))
  (gv2 : GVsT DGVs) S los nts Ps (Mem : Mem.mem) F t v gl
  (Hwfv: wf_value S (module_intro los nts Ps) F v t)
  (maxb : Values.block) (Hget : getOperandValue (los,nts) v lc2 gl = ret gv2)
  (EC : Opsem.ExecutionContext) (mb : mblock) (Huniq: uniqEC EC)
  (H : in_SAS_tail pinfo sasinfo (ret mb) (los,nts) EC)
  (Hwfg: MemProps.wf_globals maxb gl)
  (Hnals1 : 
    Promotability.wf_ECStack_head_in_tail maxb pinfo (los,nts) Mem lc2 EC),
  MemProps.no_alias_with_blk gv2 mb.
Proof.
  intros.
  destruct H as [H1 H2]. simpl in *.
  unfold Promotability.wf_ECStack_head_in_tail in Hnals1.
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC Huniq) as [J | J].
    assert (G:=J).
    destruct G as [J1 [J2 J3]]. simpl in *. subst.
    apply_clear H1 in J.
    remember (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) as R.
    destruct R as [[|[[]][]]|]; tinv J.
    inv J. symmetry in HeqR.
    eapply Promotability.wf_ECStack_head_in_tail__no_alias_with_blk; eauto.
    
    apply_clear H2 in J. congruence.
Qed.

Lemma in_SAS_tails__wf_ECStack_head_tail__no_alias_with_blk: 
  forall pinfo sasinfo lc2 gv2 los nts Mem maxb size Ps F t gl
  (Hwfg: MemProps.wf_globals maxb gl) v S
  (Hwfv: wf_value S (module_intro los nts Ps) F v t)
  (Hget : getOperandValue (los,nts) v lc2 gl = ret gv2) EC ombs
  (Hsas: in_SAS_tails pinfo sasinfo ombs (los,nts) EC) (Huniq: uniqECs EC)
  (Hnals: Promotability.wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc2 EC),
  List.Forall (fun re => 
               let '(mb,_,_) := re in
               MemProps.no_alias_with_blk gv2 mb) (ombs__ignores size ombs).
Proof.
  intros.
  induction Hsas; simpl; intros; auto.
    apply Promotability.wf_ECStack_head_tail_cons__inv in Hnals.
    destruct Hnals as [Hnals1 Hals2].
    inv Huniq.
    apply_clear IHHsas in Hals2; auto.
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
  (Heq3: Opsem.Allocas EC = als2) sasinfo (Huniq: uniqEC EC)
  (Hsas: in_SAS_tail pinfo sasinfo (Some mb) (los,nts) EC),
  MemProps.no_alias_with_blk gv2 mb.
Proof.
  intros.
  destruct Hsas as [J1 J2].
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC Huniq) as [J | J].
    assert (G:=J).
    destruct G as [J4 [J5 J3]]. simpl in *. subst.
    destruct (fdef_dec (PI_f pinfo) (Opsem.CurFunction EC)); try congruence.
    apply_clear J1 in J.
    remember (lookupAL (GVsT DGVs) (Opsem.Locals EC) (PI_id pinfo)) as R.
    destruct R as [[|[[]][]]|]; inv J.
    clear J2. symmetry in HeqR.
    eapply Promotability.wf_defs__no_alias_with_blk; eauto.
    
    apply_clear J2 in J. congruence.
Qed.

Lemma load_pid_isnt_in_SAS_tail: forall pinfo sasinfo TD v t id0 align0 cs EC 
  (Hneq: used_in_value (PI_id pinfo) v = true) (Huniq: uniqEC EC)
  (Heq: Opsem.CurCmds EC = insn_load id0 t v align0 :: cs),
  in_SAS_tail pinfo sasinfo None TD EC.
Proof.
  unfold in_SAS_tail.
  simpl. intros.
  destruct v; inv Hneq.
  destruct (id_dec id5 (PI_id pinfo)); subst; inv H0.
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC Huniq) as [J | J].
    elimtype False.
    destruct J as [J1 [J2 J3]].
    unfold cs_follow_dead_store in J3.
    destruct sasinfo. simpl in *.
    destruct SAS_prop0 as [J4 [J5 J6]].
    destruct SAS_block0 as [? [? cs0 ?]].
    destruct J6 as [cs2 [cs3 J6]]; subst. simpl in *.
    destruct (@J3 cs2 (insn_store SAS_sid4 (PI_typ pinfo) SAS_value4
                         (value_id (PI_id pinfo)) SAS_align4 :: cs3)) as
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
  b' ofs' m' (Huniq: uniqECs EC)
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

Lemma in_SAS_tail_dec: forall pinfo sasinfo TD EC mb (Huniq: uniqEC EC)
  (Hnone: in_SAS_tail pinfo sasinfo None TD EC)
  (Hsome: in_SAS_tail pinfo sasinfo (Some mb) TD EC),
  False.
Proof.
  unfold in_SAS_tail.
  intros.
  destruct (@EC_follow_dead_store_dec pinfo sasinfo EC Huniq) as [J | J].
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
       Opsem.Allocas := als2 |} :: EC)) 
  (Huniq: uniqECs ({| Opsem.CurFunction := F;
                      Opsem.CurBB := B;
                      Opsem.CurCmds := insn_load id0 t v align0 :: cs;
                      Opsem.Terminator := tmn2;
                      Opsem.Locals := lc2;
                      Opsem.Allocas := als2 |} :: EC)) size,
  SASmsim.notin_ignores_with_size (ombs__ignores size' ombs) b'
     (Int.signed 31 ofs') size.
Proof.
  intros. 
  inv Hin. simpl. inv Huniq.
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

Lemma in_SAS_tail_at_beginning: forall pinfo sasinfo TD F tmn' lc' als' cs' ps' 
  l',
  in_SAS_tail pinfo sasinfo None TD 
    {| Opsem.CurFunction := F;
       Opsem.CurBB := (l', stmts_intro ps' cs' tmn');
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

Lemma SAS_sid2_isnt_in_SAS_tail: forall (pinfo : PhiInfo) 
  (sasinfo : SASInfo pinfo) (tmn2 : terminator) (lc2 : Opsem.GVsMap)
  (als2 : list mblock) (los : layouts) (nts : namedts) (B : block) (t : typ)
  (align0 : align) (v1 : value) (v2 : value) (cs : list cmd)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               (l1, stmts_intro ps1
                 (cs11 ++
                  insn_store (SAS_sid2 pinfo sasinfo) t v1 v2 align0 :: cs)
                 tmn2))
  (y : monad Values.block) (Huniq: uniqFdef (PI_f pinfo)) 
  (HBinF: blockInFdefB B (PI_f pinfo))
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
  clear - J Heq3 Huniq.
  destruct J as [J1 [J2 J3]]. simpl in *. subst.
  unfold cs_follow_dead_store in J3.
  destruct Heq3 as [l1 [ps1 [cs11 Heq3]]].
  rewrite Heq3 in J3. clear J1.
  symmetry in Heq3.
  eapply SAS_block_inv2 in Heq3; eauto.
  destruct Heq3 as [EQ1 [cs1 EQ2]]; subst.
  inv EQ1.
  destruct (@J3 cs1 (insn_store (SAS_sid2 pinfo sasinfo) (PI_typ pinfo) 
                      (SAS_value2 pinfo sasinfo) (value_id (PI_id pinfo))
                      (SAS_align2 pinfo sasinfo) :: cs))
    as [csa [csb [J6 J7]]]; simpl_env; auto.
    anti_simpl_env. 
Qed.

Lemma SAS_sid2_is_in_SAS_tail: forall (pinfo : PhiInfo) (sasinfo : SASInfo pinfo)
  (tmn2 : terminator) (lc2 : Opsem.GVsMap) (als2 : list mblock) (los : layouts)
  (nts : namedts) (B : block) (align0 : align) (v1 : value) (cs : list cmd)
  (b' : Values.block) (cm' : AST.memory_chunk) (Huniq: uniqFdef (PI_f pinfo))
  (HBinF: blockInFdefB B (PI_f pinfo) = true)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               (l1, stmts_intro ps1
                 (cs11 ++
                  insn_store (SAS_sid2 pinfo sasinfo) 
                    (PI_typ pinfo) v1 (value_id (PI_id pinfo)) align0 :: cs)
                 tmn2))
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
    assert ((l1, stmts_intro ps1
             (cs11 ++
              insn_store (SAS_sid2 pinfo sasinfo) (PI_typ pinfo) v1
              (value_id (PI_id pinfo)) align0 :: cs) tmn2) = 
            SAS_block pinfo sasinfo) as EQ.
      apply SAS_block_spec; auto.
      simpl. repeat simpl_locs. right.
      xsolve_in_list.
    split; auto.
      unfold cs_follow_dead_store.
      rewrite <- EQ.
      intros.
      eapply SAS_block_inv2 in EQ; eauto. 
      destruct EQ as [EQ1 [cs4 EQ2]]; subst. inv EQ1.
      exists (SAS_tail pinfo sasinfo). exists nil. 
      simpl_env in H. simpl in H.
      apply NoDup_cmds_split_middle in H; auto.
        destruct H; subst. 
        apply app_inv_head in H0. simpl_env. auto.

        simpl_env in HBinF. simpl in HBinF. solve_NoDup.
Qed.

(*****************************************************)
(* Properties of simulation *)
Lemma block_simulation_inv : forall pinfo sasinfo F l1 ps1 cs1 tmn1 l2 ps2 cs2
  tmn2,
  uniqFdef F ->
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) F ->
  block_simulation pinfo sasinfo F (l1, stmts_intro ps1 cs1 tmn1)
    (l2, stmts_intro ps2 cs2 tmn2) ->
  l1 = l2 /\ ps1 = ps2 /\
  cmds_simulation pinfo sasinfo F cs1 cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold block_simulation, cmds_simulation, RemoveSim.block_simulation, 
         RemoveSim.cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); inv H1; auto.
  erewrite remove_phinodes_eq; eauto.
Qed.

Lemma switchToNewBasicBlock_sim : forall TD l1 l2 ps cs1 cs2 tmn1 tmn2 B1 B2
  gl lc lc1 lc2 F pinfo sasinfo (Huniq: uniqFdef F) 
  (HbInF: blockInFdefB B1 F = true)
  (H23 : @Opsem.switchToNewBasicBlock DGVs TD
          (l1, stmts_intro ps cs1 tmn1) B1 gl lc =
         ret lc1)
  (Hbsim2 : block_simulation pinfo sasinfo F B1 B2)
  (H2 : Opsem.switchToNewBasicBlock TD
         (l2, stmts_intro ps cs2 tmn2) B2 gl lc =
        ret lc2), lc1 = lc2.
Proof.
  intros.
  destruct B1 as [l3 []], B2 as [l4 []].
  apply block_simulation_inv in Hbsim2; auto.
  destruct Hbsim2 as [J1 [J2 [J3 J4]]]; subst.
  unfold Opsem.switchToNewBasicBlock in *. simpl in *.
  rewrite (@OpsemProps.getIncomingValuesForBlockFromPHINodes_eq 
    DGVs ps TD l4 phinodes0 cmds0 terminator0
                  phinodes0 cmds5 terminator0) in H2; auto.
  rewrite H2 in H23. congruence.
Qed.

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
         (l'0, stmts_intro ps'0 cs' tmn'0) B gl2 lc2 =
        ret lc'0),
  mem_simulation pinfo sasinfo (los, nts)
     ({|
      Opsem.CurFunction := F;
      Opsem.CurBB := (l'0, stmts_intro ps'0 cs' tmn'0);
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

Lemma mem_simulation_update_locals :
  forall pinfo sasinfo TD F B c cs tmn3 lc1 lc2 als3 als3' ECs M1 M2
  (Hneq: PI_f pinfo = F -> getCmdLoc c <> SAS_sid2 pinfo sasinfo)
  (Hneq': PI_f pinfo = F -> getCmdLoc c <> SAS_sid1 pinfo sasinfo)
  (Hex: exists l0, exists ps0, exists cs0,
          B = (l0, stmts_intro ps0 (cs0++c::cs) tmn3))
  (Hp: PI_f pinfo = F -> 
       lookupAL (GVsT DGVs) lc1 (PI_id pinfo) =
         lookupAL (GVsT DGVs) lc2 (PI_id pinfo))
  (Huniq: uniqFdef F)
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

Axiom callExternalFunction__mem_simulation_l2r: forall pinfo sasinfo 
  TD St1 M1 M2 fid0 gvss0 oresult1 M1' dck tr1 gl tret targs,
  mem_simulation pinfo sasinfo TD St1 M1 M2 ->
  callExternalOrIntrinsics TD gl M1 fid0 tret targs dck gvss0 =
    ret (oresult1, tr1, M1') ->
  exists M2', exists oresult2, exists tr2, 
    callExternalOrIntrinsics TD gl M2 fid0 tret targs dck gvss0 =
      ret (oresult2, tr2, M2') /\
    oresult1 = oresult2 /\ mem_simulation pinfo sasinfo TD St1 M1' M2' /\ 
    tr1 = tr2.

Lemma callExternalFunction__mem_simulation: forall pinfo sasinfo TD St1 M1 M2
  fid0 gvss0 oresult1 M1' oresult2 M2' dck tret targs gl tr1 tr2,
  mem_simulation pinfo sasinfo TD St1 M1 M2 ->
  callExternalOrIntrinsics TD gl M1 fid0 tret targs dck gvss0 = 
    ret (oresult1, tr1, M1') ->
  callExternalOrIntrinsics TD gl M2 fid0 tret targs dck gvss0 = 
    ret (oresult2, tr2, M2') ->
  oresult1 = oresult2 /\ mem_simulation pinfo sasinfo TD St1 M1' M2' /\ 
    tr1 = tr2.
Proof.
  intros.
  eapply callExternalFunction__mem_simulation_l2r in H; eauto.
  destruct H as [M2'' [oresult2' [tr2' [J1 [J2 [J3 J4]]]]]]; subst.
  uniq_result. auto.
Qed.

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

Lemma mem_simulation__free_l2r' : forall TD Mem1 Mem2 Mem1' ECs pinfo sasinfo ptr
  (Huniq: uniqECs ECs)
  (Hmsim : mem_simulation pinfo sasinfo TD ECs Mem1 Mem2)
  (Hmlc: free TD Mem1 ptr = ret Mem1'),
  exists Mem2', free TD Mem2 ptr = ret Mem2'.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  apply free_inv in Hmlc.
  destruct Hmlc as [blk [ofs [hi [lo [H1 [H2 [H3 H4]]]]]]].
  unfold sas_mem_inj in *.
  inv_mbind.
  destruct (@in_SAS_tails_ex pinfo sasinfo TD ECs Huniq) as [ombs J].
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

Lemma mem_simulation__free_l2r : forall TD Mem1 Mem2 Mem1'
  ECs1 pinfo sasinfo EC EC' ptr (Huniq: uniqECs (EC::ECs1))
  (Hp: forall omb,
       in_SAS_tail pinfo sasinfo omb TD EC' ->
       in_SAS_tail pinfo sasinfo omb TD EC)
  (Hmsim : mem_simulation pinfo sasinfo TD (EC :: ECs1) Mem1 Mem2)
  (Hmlc: free TD Mem1 ptr = ret Mem1'),
  exists Mem2',
    free TD Mem2 ptr = ret Mem2' /\
    mem_simulation pinfo sasinfo TD (EC' :: ECs1) Mem1' Mem2'.
Proof.
  intros.
  assert (Hmsim':=Hmsim).
  eapply mem_simulation__free_l2r' in Hmsim'; eauto.
  destruct Hmsim' as [Mem2' Hfree'].
  exists Mem2'.
  split; auto.
    eapply mem_simulation__free; eauto.
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

Ltac unstore_loc__neq__SAS_sid2_tac :=
match goal with
| Hex: exists _:_, exists _:_, exists _:_, ?B1=(_, stmts_intro _ (_++_::_) _),
  HBinF1 : blockInFdefB ?B1 ?F = true |-
  PI_f ?pinfo = ?F -> _ <> SAS_sid2 ?pinfo _ =>
    eapply unstore_loc__neq__SAS_sid2 with (B:=B1); 
            eauto using wf_system__uniqFdef; simpl; auto
end.

Lemma mem_simulation__return: forall (pinfo : PhiInfo) (sasinfo : SASInfo pinfo)
  (lc2 : Opsem.GVsMap) (als2 : list mblock) (tmn3 : terminator) t0 v0 
  (lc3 : Opsem.GVsMap) (als3 : list mblock) (M2 : mem) (los : layouts) 
  (nts : namedts) (F : fdef) (rid : id) tmn (F' : fdef) (B' : block) (i0 : id)
  (n : noret) (c : clattrs) (v : value) (p : params) (cs' : list cmd)
  (EC : list Opsem.ExecutionContext) (Mem : mem) (l3 : l) (ps3 : phinodes)
  (cs0 : list cmd) (Mem' : mem) (Huniq: uniqFdef F') 
  (HBinF: blockInFdefB B' F' = true)
  (H0 : free_allocas (los, nts) Mem als2 = ret Mem')
  (Heq3' : exists l1 : l,
            exists ps1 : phinodes,
              exists cs11 : list cmd,
                B' =
                (l1, stmts_intro ps1 (cs11 ++ insn_call i0 n c t0 v0 v p :: cs')
                  tmn3))
  (Hmsim : mem_simulation pinfo sasinfo (los, nts)
            ({|
             Opsem.CurFunction := F;
             Opsem.CurBB := (l3, stmts_intro ps3 (cs0 ++ nil) tmn);
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
      unstore_loc__neq__SAS_sid2_tac.
      eapply unstore_loc__neq__SAS_sid1; eauto; simpl; auto.
    apply in_SAS_tail_nil.
Qed. 

Lemma mem_simulation__malloc: forall (pinfo : PhiInfo) (sasinfo : SASInfo pinfo)
  (tmn2 : terminator) (lc2 : Opsem.GVsMap) (als2 als2': list mblock)
  (M2 : mem) (los : layouts) (nts : namedts) (F : fdef) (B : block) c align0
  (EC : list Opsem.ExecutionContext) t id0 (Hid: getCmdID c = Some id0)
  (cs : list cmd) (Mem : mem) (gn : GenericValue) (Mem' : mem) (mb : mblock)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               (l1, stmts_intro ps1 (cs11 ++ c :: cs) tmn2))
  (Hmalloc: match c with
            | insn_malloc _ _ _ _ | insn_alloca _ _ _ _ => True
            | _ => False
            end) (Hwfpi: WF_PhiInfo pinfo)
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
            assert (in_SAS_tails pinfo sasinfo (None::l') (los, nts)
               ({|
                Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := insn_malloc (PI_id pinfo) typ5 value5 align5 :: cs;
                Opsem.Terminator := tmn2;
                Opsem.Locals := lc2;
                Opsem.Allocas := als2 |} :: EC)) as Hin.
              unfold in_SAS_tails.
              constructor; auto.
                split; simpl; intros; auto.
                destruct H as [H _]. simpl in H. congruence.
             apply_clear Hmsim2 in Hin.
             simpl in Hin. 
             simpl.
             destruct y; auto.
               simpl_env.
               apply SASmsim.mem_inj_ignores_weaken; auto.

        SCase "c = alloca".
          inv Hin'.
          assert (in_SAS_tails pinfo sasinfo (None::l') (los, nts)
             ({|
              Opsem.CurFunction := F;
              Opsem.CurBB := B;
              Opsem.CurCmds := insn_alloca (PI_id pinfo) typ5 value5 align5 :: cs;
              Opsem.Terminator := tmn2;
              Opsem.Locals := lc2;
              Opsem.Allocas := als2 |} :: EC)) as Hin.
            unfold in_SAS_tails.
            constructor; auto.
              split; simpl; intros; auto.
                destruct H as [H _]. simpl in H. subst.
                assert (lookupAL (GVsT DGVs) lc2 (PI_id pinfo) = None) as Hnone.
                  clear - Hpalloca Hwfpi HBinF Huniq Heq3.
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
        eapply in_SAS_tails__replace_head in Hin'; eauto.
        intros.
        apply in_SAS_tail_update with 
          (lc1:=updateAddAL (GVsT DGVs) lc2 id0
                ($ blk2GV (los, nts) mb # typ_pointer t $)) (als3:=als2); 
          eauto using unremovable_loc__neq__SAS_sid1.
          eapply unstore_loc__neq__SAS_sid2; eauto.
            destruct c; tinv Hmalloc; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
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
  (Huniq: uniqECs ({| Opsem.CurFunction := F;
                      Opsem.CurBB := B;
                      Opsem.CurCmds := insn_load id0 t v align0 :: cs;
                      Opsem.Terminator := tmn2;
                      Opsem.Locals := lc2;
                      Opsem.Allocas := als2 |} :: EC))
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
                 Opsem.Allocas := als2 |} :: EC) Huniq) as [ombs Hin].
  assert (G:=Hin).
  apply_clear Hmsim2 in Hin.
  eapply SASmsim.mload_aux_inject_id_inj2; eauto.
    eapply in_SAS_tails__notin_ignores_with_size; eauto.
Qed.

Lemma mem_simulation__call: forall pinfo sasinfo TD EC ECs M1 M2
  (Hmsim : mem_simulation pinfo sasinfo TD (EC :: ECs) M1 M2)
  (l'0 : l) (ps'0 : phinodes) (tmn'0 : terminator) als' lc' F cs'
  (Huniq: uniqEC {| Opsem.CurFunction := F;
                    Opsem.CurBB := (l'0, stmts_intro ps'0 cs' tmn'0);
                    Opsem.CurCmds := cs';
                    Opsem.Terminator := tmn'0;
                    Opsem.Locals := lc';
                    Opsem.Allocas := als' |}),
  mem_simulation pinfo sasinfo TD
    ({| Opsem.CurFunction := F;
        Opsem.CurBB := (l'0, stmts_intro ps'0 cs' tmn'0);
        Opsem.CurCmds := cs';
        Opsem.Terminator := tmn'0;
        Opsem.Locals := lc';
        Opsem.Allocas := als' |} :: EC :: ECs) M1 M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim3 Hmsim2]].
  split; auto.
  split; auto.
     clear - Hmsim2 Huniq.
     unfold sas_mem_inj in *.
     inv_mbind. 
     intros ombs Hin'.
     inv Hin'.

     destruct y.
       assert (in_SAS_tail pinfo sasinfo None TD
         {| Opsem.CurFunction := F;
            Opsem.CurBB := (l'0, stmts_intro ps'0 cs' tmn'0);
            Opsem.CurCmds := cs';
            Opsem.Terminator := tmn'0;
            Opsem.Locals := lc';
           Opsem.Allocas := als' |}) as Hin.
         apply in_SAS_tail_at_beginning; auto.
       apply in_SAS_tail_dec in H1; auto. inv H1.
       
       simpl.
       apply Hmsim2; auto.
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
  (HuniqF: uniqFdef F) (HBinF: blockInFdefB B F)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               (l1, stmts_intro ps1
                 (cs11 ++ insn_store sid t v1 v2 align0 :: cs) tmn2))
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
          clear - H1 Heq3 HuniqF HBinF.
          eapply SAS_sid2_isnt_in_SAS_tail; eauto.
        subst. simpl.
        assert (v2 = value_id (PI_id pinfo) /\ t = PI_typ pinfo) as EQ.         
          clear - Heq3 HBinF1 HuniqF.
          destruct Heq3 as [l1 [ps1 [cs11 Heq3]]]. subst.
          eapply lookup_SAS_lid2__store with (sasinfo:=sasinfo) in HBinF1; 
            eauto using in_middle.
          inv HBinF1. auto.
        destruct EQ; subst.
        simpl in H25.
        assert (ofs' = Int.repr 31 0) as EQ. 
          apply Hinscope' in H25. clear - H25.
          destruct H25 as [[_ [[mb [H25 _]] _]] _].
          rewrite simpl_blk2GV in H25. inv H25. auto.            
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
            clear - H25 Heq3 HuniqF HBinF.
            eapply SAS_sid2_is_in_SAS_tail; eauto.
        apply_clear Hmsim2 in Hin. simpl in Hin.
        assert (n = sizeGenericValue gv1) as EQ. 
          clear - Hwflc1 Hwfv HeqR H24 Hwfg.
          eapply wf__getTypeStoreSize_eq_sizeGenericValue; eauto.
        rewrite EQ in *. clear EQ. 
        eapply SASmsim.mstore_aux_inject_id_inside_inj2; eauto.
        rewrite Int.signed_repr; auto using min_le_zero_le_max.
  
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

Lemma mstore_removable_mem_simulation: forall los nts M1 mp2 gv1 a M1' pinfo lc2 
  gl2 B1 cs1 tmn2 als2 ECs1 M2 t v sasinfo v0 Ps
  (Huniq: uniqFdef (PI_f pinfo))
  (HBinF1 : blockInFdefB B1 (PI_f pinfo) = true)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B1 =
               (l1, stmts_intro ps1
                 (cs11 ++ insn_store (SAS_sid1 pinfo sasinfo) t v v0 a :: cs1)
                 tmn2)) maxb
  (Hinscope' : if fdef_dec (PI_f pinfo) (PI_f pinfo)
              then Promotability.wf_defs maxb pinfo (los, nts) M1 lc2 als2
              else True)
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
      destruct Heq3 as [l1 [ps1 [cs11 Heq3]]]; subst.
      eapply lookup_SAS_lid1__store with (sasinfo:=sasinfo) in HBinF1; 
        eauto using in_middle.
      inv HBinF1. auto.
    destruct EQ; subst. simpl in H20.
    assert (exists mb, mp2 = 
              ($ (blk2GV (los,nts) mb) # (typ_pointer (PI_typ pinfo)) $)) as EQ.
      destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
      apply Hinscope' in H20.
      destruct H20 as [[_ [[mb [H20 _]] _]] _]. eauto.
    destruct EQ as [mb EQ]; subst.
    assert (y = Some mb) as EQ.
      eapply SAS_sid1_is_in_SAS_tail; eauto.
    subst.
    assert (n = sizeGenericValue gv1) as EQ.
      eapply wf__getTypeStoreSize_eq_sizeGenericValue; eauto.
    subst.
    simpl.
    eapply SASmsim.mstore_inside_inj_left; eauto.
Qed.

(*****************************************************)
(* Preservation *)
Ltac repeat_solve :=
  repeat (match goal with
          | |- mem_simulation _ _ _ _ _ _ => idtac
          | |- _ => split; eauto 2 using cmds_at_block_tail_next
          end).

Ltac dse_is_sim_mem_update :=
match goal with
| Hmsim: mem_simulation _ _ _ _ _ _ |- _ =>
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
                      wf_system__uniqFdef |
          unstore_loc__neq__SAS_sid2_tac |
          solve_non_pid_updateAddAL
        ]
  end
end.

Ltac dse_is_sim_common_case :=
match goal with
| Hex: exists _:_, exists _:_, exists _:_, ?B1=(_, stmts_intro _ (_++_::_) _),
  HBinF1 : blockInFdefB ?B1 _ = true,
  Hcssim2: cmds_simulation _ _ _ _ _,
  Hop2: Opsem.sInsn _ _ _ _,
  Hmsim: mem_simulation _ _ _ _ _ _ |- _ =>
  apply RemoveSim.cmds_simulation_nelim_cons_inv' in Hcssim2; simpl; try solve 
    [eauto 2 using unremovable_loc__neq__SAS_sid1, wf_system__uniqFdef];
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  dse_is_sim_mem_update
end.

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
  apply RemoveSim.cmds_simulation_nil_inv in Hcssim2; subst;
  wfCall_inv;
  apply RemoveSim.cmds_simulation_nelim_cons_inv' in Hcssim2'; try solve [
    auto |
    try match goal with
        | |- _ = _ -> _ <> _ => 
          eapply unstore_loc__neq__SAS_sid1; 
            eauto using wf_system__uniqFdef ; simpl; auto
        end ];
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result
end.

Ltac dse_is_sim_malloc :=
  destruct_ctx_other;
  match goal with 
  | Hcssim2: cmds_simulation _ _ _ _ _,
    Hop2: Opsem.sInsn _ _ _ _ |- _ =>
    apply RemoveSim.cmds_simulation_nelim_cons_inv' in Hcssim2; simpl;
      try solve [eauto using unremovable_loc__neq__SAS_sid1];
    destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
    inv Hop2; uniq_result
  end;
  match goal with
  | Hmsim: mem_simulation _ _ _ _ ?M1 ?M2,
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

Lemma sas_is_sim : forall maxb pinfo (sasinfo: SASInfo pinfo) Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfmg: MemProps.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hpalloca: palloca_props.wf_State pinfo St1) 
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
  simpl in Hrem.
  destruct (fdef_dec (PI_f pinfo) F1); subst; tinv Hrem.
  destruct (id_dec (SAS_sid1 pinfo sasinfo) (getCmdLoc c1)); subst; tinv Hrem.
  
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

  assert (
    c1 = insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
           (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) 
           (SAS_align1 pinfo sasinfo)) 
    as EQ.
    destruct Heq3 as [l1 [ps3 [cs11 Heq3]]]; subst.
    eapply lookup_SAS_lid1__store; eauto using wf_system__uniqFdef, in_middle.
  subst.
  inv Hop1.

  uniq_result.
  repeat_solve.
    eapply RemoveSim.cmds_simulation_elim_cons_inv; eauto.
    assert (wf_value S1 (module_intro los nts Ps1) (PI_f pinfo)
              (SAS_value1 pinfo sasinfo) (PI_typ pinfo)) as Hwfv.
      get_wf_value_for_simop_ex. auto.
    eapply mstore_removable_mem_simulation in Hmsim;
      eauto using wf_system__uniqFdef.

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
    clear - H26 Hmsim H0 H1 Heq3' Huniq EQ HBinF2.
    eapply mem_simulation__return; eauto.

SCase "sReturnVoid".
Focus.
  destruct_ctx_return.
  repeat_solve.
    assert (Huniq: uniqFdef F') by eauto using wf_system__uniqFdef.
    clear - H24 Hmsim H0 Heq3' Huniq HBinF2.
    eapply mem_simulation__return; eauto.

SCase "sBranch".
Focus.
  destruct_ctx_other.
  apply RemoveSim.cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo sasinfo F 
           (if isGVZero (los, nts) c then l2 else l1, 
            stmts_intro ps' cs' tmn')
           (if isGVZero (los, nts) c then l2 else l1, 
            stmts_intro ps'0 cs'0 tmn'0)) as Hbsim.
    clear - H22 H1 Hfsim2.
    destruct (isGVZero (los, nts) c); 
      eapply RemoveSim.fdef_sim__block_sim; eauto.
  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  assert (blockInFdefB (if isGVZero (los, nts) c then l2 else l1, 
                        stmts_intro ps' cs' tmn') F) as HBinF1'.
    solve_blockInFdefB.
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'; auto.
  destruct Hbsim' as [Heq1 [Heq2 [Hcssim' Heq5]]]; subst.

  assert (lc' = lc'0) as Heq.
    clear - H2 H23 Hbsim2 HBinF1 Huniq.
    eapply switchToNewBasicBlock_sim in Hbsim2; eauto.
  subst.

  repeat_solve.
    exists (if isGVZero (los, nts) c then l2 else l1). 
    exists ps'0. exists nil. auto.

    exists (if isGVZero (los, nts) c then l2 else l1). 
    exists ps'0. exists nil. auto.

    clear - H2 Hmsim.
    eapply switchToNewBasicBlock_mem_simulation; eauto.

SCase "sBranch_uncond".
Focus.
  destruct_ctx_other.
  apply RemoveSim.cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo sasinfo F (l0, stmts_intro ps' cs' tmn')
           (l0, stmts_intro ps'0 cs'0 tmn'0)) as Hbsim.
    eapply RemoveSim.fdef_sim__block_sim; eauto.
  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  assert (blockInFdefB (l0, stmts_intro ps' cs' tmn') F) as HBinF1'.
    solve_blockInFdefB.
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'; auto.
  destruct Hbsim' as [Heq1 [Heq2 [Hcssim' Heq5]]]; subst.

  assert (lc' = lc'0) as Heq.
    clear - H0 H17 Hbsim2 HBinF1 Huniq.
    eapply switchToNewBasicBlock_sim in Hbsim2; eauto.
  subst.

  repeat_solve.
    exists l0. exists ps'0. exists nil. auto.
    exists l0. exists ps'0. exists nil. auto.

    clear - H0 Hmsim.
    eapply switchToNewBasicBlock_mem_simulation; eauto.

SCase "sBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExtractValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sInsertValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sMalloc".  abstract (dse_is_sim_malloc).

SCase "sFree".
  destruct_ctx_other.

  apply RemoveSim.cmds_simulation_nelim_cons_inv' in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    eapply mem_simulation__free; eauto.
    eapply mem_simulation__replace_head in Hmsim; eauto.
    intros omb Hin.
      eapply in_SAS_tail_update; eauto using unremovable_loc__neq__SAS_sid1, 
                                             unstore_loc__neq__SAS_sid2,
                                             wf_system__uniqFdef.
        unstore_loc__neq__SAS_sid2_tac.

SCase "sAlloca". abstract (dse_is_sim_malloc).

SCase "sLoad".

  assert (HuniqECs:=Hwfpp). eapply wf_State__uniqECs in HuniqECs; eauto.
  destruct_ctx_other.

  apply RemoveSim.cmds_simulation_nelim_cons_inv' in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  assert (gv = gv0) as EQ.
    assert (wf_value S (module_intro los nts Ps) F v (typ_pointer t)) as Hwfv.
      get_wf_value_for_simop_ex. auto.
    clear - H23 Hmsim H1 H21 HwfHT Hinscope' Hwfmg Hwfv HuniqECs. simpl in *.
    eapply mem_simulation__mload; eauto.
  subst.
  dse_is_sim_mem_update.

SCase "sStore".

  destruct_ctx_other.

  apply RemoveSim.cmds_simulation_nelim_cons_inv' in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    assert (wf_value S (module_intro los nts Ps) F v1 t) as Hwfv.
      get_wf_value_for_simop_ex. auto.
    eapply mstore_unremovable_mem_simulation; eauto using wf_system__uniqFdef.

SCase "sGEP". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sTrunc". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExt". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sCast". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sIcmp". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFcmp". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sSelect".
  destruct_ctx_other.

  apply RemoveSim.cmds_simulation_nelim_cons_inv' in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    destruct (isGVZero (los,nts) c); dse_is_sim_mem_update.

SCase "sCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply RemoveSim.cmds_simulation_nelim_cons_inv' in Hcssim2; simpl;
    try solve [eauto using unremovable_loc__neq__SAS_sid1].
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.

  inv Hop2.

  SSCase "SCall".

  uniq_result.
  assert (Hfsim1:=Hpsim).
  eapply TopSim.lookupFdefViaPtr__simulation in Hfsim1; eauto.
  simpl in Hfsim1.
  assert (Hbsim1:=Hfsim1).
  eapply RemoveSim.fdef_simulation__entry_block_simulation in Hbsim1; eauto.

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
  assert (exists l1 : l, exists ps1 : phinodes, exists cs11 : list cmd,
           (l'0, stmts_intro ps'0 cs' tmn'0) =
           (l1, stmts_intro ps1 (cs11 ++ cs') tmn'0)) as Hex.
    exists l'0. exists ps'0. exists nil. auto.
  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.

    apply RemoveSim.fdef_simulation_inv in Hfsim1.
    destruct Hfsim1 as [Heq _]. inv Heq. uniq_result.
    auto.

    clear - Hmsim Huniq Hex H2. 
    apply mem_simulation__call; auto.
      repeat (split; simpl; try solve [auto | solve_blockInFdefB]).

  SSCase "sExCall".

  uniq_result.

  clear - H29 H1 Hpsim.
  eapply TopSim.lookupFdefViaPtr__simulation_l2r in H1; eauto.
  simpl in H1.
  destruct H1 as [f2 [H1 H2]].
  apply OpsemAux.lookupExFdecViaPtr_inversion in H29.
  apply OpsemAux.lookupFdefViaPtr_inversion in H1.
  destruct H29 as [fn [J1 [J2 J3]]].
  destruct H1 as [fn' [J4 J5]].
  uniq_result.

SCase "sExCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply RemoveSim.cmds_simulation_nelim_cons_inv' in Hcssim2; simpl;
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
