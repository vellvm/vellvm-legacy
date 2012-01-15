Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../SoftBound".
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
Require Import sb_msim.
Require Import sb_ds_trans_lib.
Require Import sb_ds_gv_inject.
Require Import sb_metadata.
Require Import program_sim.

Definition fdef_simulation (pinfo: PhiInfo) f1 f2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_fdef (PI_id pinfo) f1 = f2
  else f1 = f2.

Definition cmds_simulation (pinfo: PhiInfo) (f1:fdef) cs1 cs2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_cmds (PI_id pinfo) cs1 = cs2
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) (f1:fdef) b1 b2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_block (PI_id pinfo) b1 = b2
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

Definition is_alloca_in_EC (pinfo: PhiInfo) F1 (lc1:@Opsem.GVsMap DGVs) 
  (blk1: mblock) : bool := 
  if (fdef_dec (PI_f pinfo) F1) then 
    match lookupAL _ lc1 (PI_id pinfo) with
    | Some ((Vptr b _,_)::nil) =>
        if (Z_eq_dec b blk1) then true
        else false
    | _ => false
    end 
  else false.

Definition als_blk_simulation (pinfo: PhiInfo) (mi:MoreMem.meminj) F1 
  (lc1:@Opsem.GVsMap DGVs) (blk1 blk2: mblock) : Prop := 
  if (is_alloca_in_EC pinfo F1 lc1 blk1) then mi blk1 = None
  else mi blk1 = Some (blk2, 0).

Fixpoint als_simulation (pinfo: PhiInfo) (mi:MoreMem.meminj) F1 lc1
  (als1 als2:list mblock) : Prop :=
  match (als1, als2) with
  | (nil, nil) => True
  | (b1::als1', _) => 
      if (is_alloca_in_EC pinfo F1 lc1 b1) then 
        mi b1 = None /\ als_simulation pinfo mi F1 lc1 als1' als2
      else 
        match als2 with 
        | b2::als2' => 
           mi b1 = Some (b2, 0) /\ als_simulation pinfo mi F1 lc1 als1' als2'
        | _ => False
        end
  | _ => False
  end.

Definition reg_simulation (pinfo: PhiInfo) (mi:MoreMem.meminj) (F1:fdef) 
  (lc1 lc2:@Opsem.GVsMap DGVs) : Prop :=
  if (fdef_dec (PI_f pinfo) F1) then 
    forall i0,
      if (id_dec (PI_id pinfo) i0) then True
      else
        forall gv1 gv2,
          lookupAL _ lc1 i0 = Some gv1 -> 
          lookupAL _ lc2 i0 = Some gv2 -> 
          gv_inject mi gv1 gv2
  else
    forall i0 gv1 gv2,
      lookupAL _ lc1 i0 = Some gv1 -> 
      lookupAL _ lc2 i0 = Some gv2 -> 
      gv_inject mi gv1 gv2.

Definition EC_simulation (pinfo: PhiInfo) (mi:MoreMem.meminj) 
  (EC1 EC2:@Opsem.ExecutionContext DGVs) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation pinfo f1 f2 /\
       tmn1 = tmn2 /\
       als_simulation pinfo mi f1 lc1 als1 als2 /\
       block_simulation pinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       reg_simulation pinfo mi f1 lc1 lc2 /\
       cmds_simulation pinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (pinfo: PhiInfo) mi (ECs1 ECs2:@Opsem.ECStack DGVs) 
  : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation pinfo mi EC1 EC2 /\ ECs_simulation pinfo mi ECs1' ECs2'
| _, _ => False
end.

Definition isnt_alloca_in_ECs (pinfo:PhiInfo) (ecs:list (fdef*Opsem.GVsMap)) 
  (blk:mblock) : Prop :=
  forall f lc (Hin: In (f,lc) ecs), 
    is_alloca_in_EC pinfo f lc blk = false.

Definition strip_ECs (ecs:list (@Opsem.ExecutionContext DGVs))
  : list (fdef*Opsem.GVsMap) :=
List.map (fun ec => (Opsem.CurFunction ec, Opsem.Locals ec)) ecs.

Definition mem_simulation (pinfo:PhiInfo) mgb (mi:MoreMem.meminj)
  (ecs:list (fdef*Opsem.GVsMap)) Mem1 Mem2 : Prop :=
MoreMem.mem_inj mi Mem1 Mem2 /\
(forall blk, ~ isnt_alloca_in_ECs pinfo ecs blk -> mi blk = None) /\
wf_sb_mi mgb mi Mem1 Mem2.

(* Copied from sb_ds_sim *)
Definition ftable_simulation mi fs1 fs2 : Prop :=
  forall fv1 fv2, gv_inject mi fv1 fv2 ->
    OpsemAux.lookupFdefViaGVFromFunTable fs1 fv1 = 
    OpsemAux.lookupFdefViaGVFromFunTable fs2 fv2.

Definition State_simulation (pinfo: PhiInfo) mgb (mi:MoreMem.meminj)
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\ 
    products_simulation pinfo Ps1 Ps2 /\
    ECs_simulation pinfo mi ECs1 ECs2 /\
    gl1 = gl2 /\ ftable_simulation mi fs1 fs2 /\ 
    mem_simulation pinfo mgb mi (strip_ECs ECs1) M1 M2
end.

Definition removable_State (pinfo: PhiInfo) (St:@Opsem.State DGVs) : Prop :=
match St with
| Opsem.mkState
    (Opsem.mkEC f b (c :: cs) tmn lc als::_) _ => 
    if (fdef_dec (PI_f pinfo) f) then 
      if (id_dec (PI_id pinfo) (getCmdLoc c)) then True else False
    else False
| _ => False
end.

Lemma removable_State_dec : forall pinfo St,
  removable_State pinfo St \/ ~ removable_State pinfo St.
Proof.
  destruct St. 
  destruct ECS as [|[]]; auto.
  destruct CurCmds; auto.
  simpl.
  destruct (fdef_dec (PI_f pinfo) CurFunction); auto.
  destruct (id_dec (PI_id pinfo) (getCmdLoc c)); auto.
Qed.

Lemma cmds_simulation_elim_cons_inv: forall (pinfo : PhiInfo) c (cs1 : list cmd) 
  (cs2 : cmds) (Heq : PI_id pinfo = getCmdLoc c)
  (Hcssim2 : cmds_simulation pinfo (PI_f pinfo) (c :: cs1) cs2),
  cmds_simulation pinfo (PI_f pinfo) cs1 cs2.
Proof.
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  simpl in *. rewrite Heq in Hcssim2.
  destruct (id_dec (getCmdLoc c) (getCmdLoc c)); simpl in *; try congruence.
Qed.

(* copied from id_rhs_val.v *)
Ltac uniq_result :=
repeat dgvs_instantiate_inv;
repeat match goal with
| H1 : ?f ?a ?b ?c ?d = _,
  H2 : ?f ?a ?b ?c ?d = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a ?b ?c = _,
  H2 : ?f ?a ?b ?c = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a ?b = _,
  H2 : ?f ?a ?b = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a = _,
  H2 : ?f ?a = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : _ @ _ |- _ => inv H1
| H : ?f _ = ?f _ |- _ => inv H
| H : False |- _ => inv H
end.

Lemma cmds_simulation_nil_inv: forall pinfo f1 cs,
  cmds_simulation pinfo f1 nil cs -> cs = nil.
Proof.
  unfold cmds_simulation. simpl.
  intros. destruct (fdef_dec (PI_f pinfo) f1); auto.
Qed.

Lemma cmds_simulation_nelim_cons_inv: forall pinfo F c cs2 cs',
  cmds_simulation pinfo F (c :: cs2) cs' ->
  PI_f pinfo <> F \/ PI_id pinfo <> getCmdLoc c ->
  exists cs2', 
    cs' = c :: cs2' /\ cmds_simulation pinfo F cs2 cs2'.
Proof.  
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); subst; simpl; eauto.
  destruct (id_dec (getCmdLoc c) (PI_id pinfo)); subst; simpl; eauto.
  rewrite e in H0.
  destruct H0; congruence.
Qed.

(* copied from las.v *)
Ltac wfCall_inv :=
match goal with
| Heq3 : exists _,
           exists _,
             exists _,
               ?B = block_intro _ _ _ _,
  HBinF1 : blockInFdefB ?B ?F = true,
  HwfCall : OpsemPP.wf_call 
              {| 
              Opsem.CurFunction := ?F;
              Opsem.CurBB := ?B;
              Opsem.CurCmds := nil;
              Opsem.Terminator := _;
              Opsem.Locals := _;
              Opsem.Allocas := _ |} 
              ({|
               Opsem.CurFunction := _;
               Opsem.CurBB := _;
               Opsem.CurCmds := ?c' :: _;
               Opsem.Terminator := _;
               Opsem.Locals := _;
               Opsem.Allocas := _ |}  :: _) |- _ =>
  let cs3 := fresh "cs3" in
  destruct Heq3 as [l3 [ps3 [cs3 Heq3]]]; subst;
  assert (HBinF1':=HBinF1);
  apply HwfCall in HBinF1';
  destruct c'; tinv HBinF1'; clear HBinF1'
end.

(* This is a common property for remove *)
Lemma fdef_sim__lookupAL_genLabel2Block_block : forall id0 l0 bs b b',
  lookupAL _ (genLabel2Block_blocks bs) l0 = Some b ->
  lookupAL _ (genLabel2Block_blocks (List.map (remove_block id0) bs)) l0 
    = Some b' ->
  remove_block id0 b = b'.
Proof.
  induction bs; simpl; intros.
    congruence.   

    destruct a. simpl in *.
    destruct (l0 == l1); subst; eauto.
      inv H. inv H0. auto.
Qed.

Lemma fdef_sim__block_sim : forall pinfo f1 f2 l0 b1 b2,
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
    eapply fdef_sim__lookupAL_genLabel2Block_block; eauto.

    uniq_result. auto.
Qed.

Definition phis_simulation (pinfo: PhiInfo) (f1:fdef) ps1 ps2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then remove_phinodes (PI_id pinfo) ps1 = ps2
  else ps1 = ps2.

Lemma block_simulation_inv : forall pinfo F l1 ps1 cs1 tmn1 l2 ps2 cs2
  tmn2,
  block_simulation pinfo F (block_intro l1 ps1 cs1 tmn1)
    (block_intro l2 ps2 cs2 tmn2) ->
  l1 = l2 /\ phis_simulation pinfo F ps1 ps2 /\ 
  cmds_simulation pinfo F cs1 cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold block_simulation, cmds_simulation, phis_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); inv H; auto.
Qed.

Lemma fdef_simulation_inv: forall pinfo fh1 fh2 bs1 bs2,
  fdef_simulation pinfo (fdef_intro fh1 bs1) (fdef_intro fh2 bs2) ->
  fh1 = fh2 /\ 
  List.Forall2 
    (fun b1 b2 => block_simulation pinfo (fdef_intro fh1 bs1) b1 b2) bs1 bs2.
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

Lemma products_simulation__fdef_simulation : forall pinfo fid Ps1 Ps2
  (Hsim: products_simulation pinfo Ps1 Ps2) f1 f2,
  lookupFdefViaIDFromProducts Ps2 fid = Some f2 ->
  lookupFdefViaIDFromProducts Ps1 fid = Some f1 ->
  fdef_simulation pinfo f1 f2.
Proof.
  intros pinfo fid Ps1 Ps2 Hsim.
  induction Hsim; simpl; intros.
    inv H.

    destruct x; destruct y; inv H0; inv H1; eauto; try congruence.
    destruct (getFdefID f0 == fid); subst.
      inv H3.
      destruct (getFdefID f == getFdefID f2).
        inv H2. auto.

        destruct f2 as [[]], f1 as [[]].
        apply lookupFdefViaIDFromProducts_ideq in H2.
        simpl in H2. subst.
        destruct f.
        apply fdef_simulation_inv in H.
        destruct H as [H _]; subst.
        contradict n; auto.
    destruct (getFdefID f == fid); subst; auto.
      inv H2.
      destruct f2 as [[]], f1 as [[]].
      apply lookupFdefViaIDFromProducts_ideq in H3.
      simpl in H3. subst.
      destruct f0.
      apply fdef_simulation_inv in H.
      destruct H as [H _]; subst.
      contradict n; auto.
Qed.

Lemma fdef_simulation__entry_block_simulation: forall pinfo F1 F2 B1 B2,
  fdef_simulation pinfo F1 F2 ->
  getEntryBlock F1 = ret B1 ->
  getEntryBlock F2 = ret B2 ->
  block_simulation pinfo F1 B1 B2.
Proof.
  intros.
  unfold fdef_simulation in H.
  unfold block_simulation.
  destruct (fdef_dec (PI_f pinfo) F1); subst.
    destruct (PI_f pinfo); simpl in *.
    destruct b; inv H0.
    simpl in H1. inv H1. auto.

    uniq_result. auto.
Qed.

Ltac repeat_solve :=
  repeat (match goal with
          | |- mem_simulation _ _ _ _ _ _ => idtac 
          | |- _ => split; eauto 2 using cmds_at_block_tail_next
          end).

Ltac zeauto := eauto with zarith.

Lemma mem_simulation__palloca : forall mi TD Mem1 Mem2 tsz gn Mem1' mb 
  ECs1 pinfo maxb lc1
  (Hmsim : mem_simulation pinfo maxb mi
            ((PI_f pinfo, lc1) :: ECs1) Mem1 Mem2)
  (Hmlc: malloc TD Mem1 tsz gn (PI_align pinfo) = ret (Mem1', mb)),
  exists mi',
    mem_simulation pinfo maxb mi'
            ((PI_f pinfo, 
               updateAddAL (GVsT DGVs) lc1 (PI_id pinfo)
                 ($ blk2GV TD mb # typ_pointer (PI_typ pinfo) $))
             :: ECs1) Mem1' Mem2 /\
    Values.inject_incr mi mi' /\
    mi' mb = None /\
    (forall b, b <> mb -> mi b = mi' b).
Proof.
  intros.
  unfold malloc in *.
  inv_mbind'. symmetry_ctx.
  destruct (zle 0 (Size.to_Z tsz * z)); tinv H0.
  remember (Mem.alloc Mem1 0 (Size.to_Z tsz * z)) as R.
  inv H0.
  assert (Hresult := H1). apply Mem.alloc_result in Hresult. subst.
  assert (Hnext := H1). apply Mem.nextblock_alloc in Hnext.
  assert (Hvalid := H1). apply Mem.valid_new_block in Hvalid.
  destruct Hmsim as [Hmsim1 [Hmsim2 Hmsim3]].
  exists (fun b => if zeq b (Mem.nextblock Mem1) then None else mi b).
  assert (inject_incr mi 
           (fun b : Z => if zeq b (Mem.nextblock Mem1) then None else mi b))
    as Hinject_incr.
    unfold inject_incr.
    intros b b' d H.
    destruct (zeq b (Mem.nextblock Mem1)); subst; auto.
      destruct Hmsim3 as [_ _ Hmap1 _].
      assert (mi (Mem.nextblock Mem1) = None) as J.
        apply Hmap1; auto with zarith.
      uniq_result.

  repeat_solve.
Case "mem_sim".
    split.
  SCase "mem_inj".
    clear Hmsim2 Hmsim3.
    destruct Hmsim1.
    apply MoreMem.mk_mem_inj.
    SSCase "mi_access".
      intros b1 b2 d c ofs p J1 J2.
      destruct (zeq b1 (Mem.nextblock Mem1)); subst; tinv J1.
      eapply Mem.valid_access_alloc_inv with (b:=(Mem.nextblock Mem1))(lo:=0)
        (hi:=Size.to_Z tsz * z)(p:=p) in J2; eauto.
      destruct (eq_block); subst; try solve [eauto | contradict n; auto].

    SSCase "mi_memval".
Transparent Mem.alloc.
      intros b1 ofs b2 d J1 J2.
      injection H1. intro MEM.
      destruct Mem1. destruct Mem1'. destruct Mem2. 
      inv MEM. clear H1 Hnext Hvalid.
      simpl in *.
      unfold Mem.perm in *. simpl in *.
      clear maxaddress_pos0 conversion_props0.
      unfold update.     
      destruct (zeq b1 nextblock); subst; tinv J1.
      apply MoreMem.memval_inject_incr with (f:=mi); auto.
      apply mi_memval; auto.
        clear - J2 n.
        unfold update in J2.
        destruct (zeq b1 nextblock); subst; 
          try solve [auto | contradict n; auto].
Opaque Mem.alloc.

    split.
  SCase "isnt_alloca_in_ECs".
    clear Hmsim1 Hmsim3 Hinject_incr.
    intros.
    destruct (zeq blk (Mem.nextblock Mem1)); subst; auto.
    apply Hmsim2. clear Hmsim2.
    intro J. apply H. clear H.
    unfold isnt_alloca_in_ECs in *.
    intros.
    simpl in Hin.
    destruct Hin as [Hin | Hin]; subst.
      inv Hin. simpl. unfold is_alloca_in_EC.
      destruct (fdef_dec (PI_f pinfo) ); try congruence.
      rewrite lookupAL_updateAddAL_eq.
      rewrite Promotability.simpl_blk2GV.
      destruct (Z_eq_dec (Mem.nextblock Mem1) blk); try congruence.

      apply J. simpl; auto.

  SCase "wfmi".
    clear Hmsim1 Hmsim2 Hinject_incr.
    destruct Hmsim3 as [Hno_overlap Hnull Hmap1 Hmap2 mi_freeblocks 
      mi_mappedblocks mi_range_block mi_bounds mi_globals].
    split.
    SSCase "no_overlap".
      clear - Hno_overlap Hnext Hmap2.
      unfold MoreMem.meminj_no_overlap in *.
      intros.      
      destruct (zeq b1 (Mem.nextblock Mem1)); subst.
        destruct (zeq b2 (Mem.nextblock Mem1)); subst; try congruence.
        destruct (zeq b2 (Mem.nextblock Mem1)); subst; eauto; try congruence.
    SSCase "null".
      destruct (zeq Mem.nullptr (Mem.nextblock Mem1)); subst; auto.
        assert(J':=@Mem.nextblock_pos Mem1).
        rewrite <- e in J'.
        unfold Mem.nullptr in J'.
        contradict J'; omega.
    SSCase "map1".
      intros b H2.
      rewrite Hnext in H2.
      destruct (zeq b (Mem.nextblock Mem1)); subst; zeauto.
    SSCase "map2".
      intros b1 b delta2 J'.
      destruct (zeq b1 (Mem.nextblock Mem1)); tinv J'; eauto.
    SSCase "freeblocks".
      intros b J'.
      destruct (zeq b (Mem.nextblock Mem1)); subst.
        contradict H1; auto.

        apply mi_freeblocks.
          intro J1. apply J'.
          eapply Mem.valid_block_alloc; eauto.
    SSCase "mappedblocks".
      intros b b' delta J'.
      destruct (zeq b (Mem.nextblock Mem1)); subst; eauto; try congruence.
    SSCase "range_block".
      intros b b' delta J'.
      destruct (zeq b (Mem.nextblock Mem1)); inv J'; subst; eauto.
    SSCase "bounds".
      intros b b' delta J'.
      erewrite Mem.bounds_alloc; eauto.
      unfold eq_block.
      destruct (zeq b (Mem.nextblock Mem1)); subst; eauto; try congruence.
    SSCase "globals".
      intros b J'.
      destruct (zeq b (Mem.nextblock Mem1)); subst; eauto.
        assert (J'':=J').
        apply mi_globals in J'.
        destruct (SBspecMetadata.valid_block_dec Mem1 (Mem.nextblock Mem1)).
          apply Mem.fresh_block_alloc in H1.
          contradict H1; auto.
     
          apply mi_freeblocks in n.        
          rewrite n in J'. inversion J'.

Case "mi_prop1".
    destruct (zeq (Mem.nextblock Mem1) (Mem.nextblock Mem1)); congruence.

Case "mi_prop2".
    intros.
    destruct (zeq b (Mem.nextblock Mem1)); subst; congruence.
Qed.

Lemma reg_simulation_update_palloca: forall (pinfo : PhiInfo) 
  (mi : MoreMem.meminj) TD (lc1 lc2 : Opsem.GVsMap)
  (Hlcsim2 : reg_simulation pinfo mi (PI_f pinfo) lc1 lc2)
  (mb : mblock) (mi' : MoreMem.meminj)
  (Hinc : inject_incr mi mi'),
  reg_simulation pinfo mi' (PI_f pinfo)
    (updateAddAL (GVsT DGVs) lc1 (PI_id pinfo)
       ($ blk2GV TD mb # typ_pointer (PI_typ pinfo) $)) lc2.
Proof.
  intros.
  unfold reg_simulation in *.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  intros.
  assert (J:=@Hlcsim2 i0). clear Hlcsim2.
  destruct (id_dec (PI_id pinfo) i0); subst; auto.
  intros.
  rewrite <- lookupAL_updateAddAL_neq in H; auto.
  eapply J in H; eauto.
  eapply gv_inject_incr; eauto.
Qed.

Lemma inject_incr__preserves__als_simulation: forall pinfo mi f lc1 als1 als2 
  mi',
  als_simulation pinfo mi f lc1 als1 als2 ->
  (forall blk, 
    is_alloca_in_EC pinfo f lc1 blk = true -> 
    mi blk = None -> mi' blk = None) ->
  inject_incr mi mi' ->
  als_simulation pinfo mi' f lc1 als1 als2.
Proof.
  induction als1; destruct als2; simpl; intros; auto.
    remember (is_alloca_in_EC pinfo f lc1 a) as R.
    destruct R; auto.
    destruct H.
    split; eauto.

    remember (is_alloca_in_EC pinfo f lc1 a) as R.
    destruct R; destruct H; split; eauto.
Qed.

Lemma inject_incr__preserves__reg_simulation: forall pinfo mi f lc1 lc2 mi',
  reg_simulation pinfo mi f lc1 lc2 ->
  inject_incr mi mi' ->
  reg_simulation pinfo mi' f lc1 lc2. 
Proof.
  intros pinfo mi f lc1 lc2 mi' Hrsim Hinc.
  unfold reg_simulation in *.
  destruct (fdef_dec (PI_f pinfo) f); subst.
    intros.
    assert (J:=@Hrsim i0).
    destruct (id_dec (PI_id pinfo) i0); subst; auto.
    intros. eapply J in H; eauto using gv_inject_incr.

    intros. eapply Hrsim in H; eauto using gv_inject_incr.
Qed.

Lemma inject_incr__preserves__EC_simulation: forall pinfo mi mi' EC1 EC2,
  EC_simulation pinfo mi EC1 EC2 ->
  (forall blk, 
    is_alloca_in_EC pinfo (Opsem.CurFunction EC1) (Opsem.Locals EC1) blk 
      = true -> 
    mi blk = None -> mi' blk = None) ->
  inject_incr mi mi' ->
  EC_simulation pinfo mi' EC1 EC2.
Proof.
  intros.
  destruct EC1 as [f1 b1 cs1 tmn1 lc1 als1].
  destruct EC2 as [f2 b2 cs2 tmn2 lc2 als2].
  destruct f1. destruct f2.
  destruct b1; tinv H.
  unfold EC_simulation in H.
  destruct H as [Hfsim [Heq0 [Hasim [Hbsim [Heqb1 [Heqb2 [Hrsim Hcssim]]]]]]]; 
    subst.
  eapply inject_incr__preserves__als_simulation in Hasim; eauto.
  eapply inject_incr__preserves__reg_simulation in Hrsim; eauto.
  repeat (split; auto).
Qed.

Lemma inject_incr__preserves__ECs_simulation: forall pinfo mi mi' ECs1 ECs2,
  ECs_simulation pinfo mi ECs1 ECs2 ->
  (forall blk, ~ isnt_alloca_in_ECs pinfo (strip_ECs ECs1) blk ->
    mi blk = None -> mi' blk = None) ->
  inject_incr mi mi' ->
  ECs_simulation pinfo mi' ECs1 ECs2.
Proof.
  induction ECs1; destruct ECs2; simpl; intros; auto.
    destruct H as [J1 J2].
    split.
      eapply inject_incr__preserves__EC_simulation; eauto.
        intros.
        apply H0; auto.
        intro J.
        unfold isnt_alloca_in_ECs in J.
        assert (In (Opsem.CurFunction a, Opsem.Locals a) 
          ((Opsem.CurFunction a, Opsem.Locals a)::strip_ECs ECs1)) as G.
          simpl. auto.
        apply J in G. uniq_result.
 
        apply IHECs1; auto.
        intros. apply H0; auto.
        intro J. apply H.
        unfold isnt_alloca_in_ECs in *.
        intros. apply J. simpl; auto.
Qed.

(* copied from sb_ds_trans_axiom.v *)
Axiom inject_incr__preserves__ftable_simulation: forall mi mi' fs1 fs2,
  ftable_simulation mi fs1 fs2 ->
  inject_incr mi mi' ->
  ftable_simulation mi' fs1 fs2.

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
  Hsim : State_simulation _ _ _ _ _ ?Cfg2 ?St2 ,
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
      [Hfsim2 [Heq1 [Halsim2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct Hecsim' as 
      [Hfsim2' [Heq1' [Halsim2' [Hbsim2' 
        [Heq3' [Heq4' [Hlcsim2' Hcssim2']]]]]]]; subst;
  destruct Hnoalias as 
    [
      [[Hinscope1' _] [[[Hinscope2' _] [HwfECs' _]] _]] 
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals;
  fold Promotability.wf_ECStack in HwfECs';
  apply cmds_simulation_nil_inv in Hcssim2; subst;
  wfCall_inv
end.

(* The sb_ds_trans_lib.mem_simulation__free should use this lemma. *)
Lemma mem_inj__free : forall mi Mem0 M2 Mem' mgb hi lo
  (b2 : Values.block) (delta : Z) blk,
  wf_sb_mi mgb mi Mem0 M2 ->
  MoreMem.mem_inj mi Mem0 M2 ->
  Mem.free Mem0 blk lo hi = ret Mem' ->
  (lo, hi) = Mem.bounds Mem0 blk ->
  mi blk = ret (b2, delta) ->
  exists Mem2',
    Mem.free M2 b2 (lo+delta) (hi+delta) = ret Mem2' /\
    wf_sb_mi mgb mi Mem' Mem2' /\
    MoreMem.mem_inj mi Mem' Mem2'.
Proof.
  intros mi Mem0 M2 Mem' mgb hi lo b2 delta blk Hwfmi Hmsim1 H0 HeqR2 H4.
  assert ({ Mem2':Mem.mem | Mem.free M2 b2 (lo+delta) (hi+delta) = ret Mem2'}) 
    as J.
    apply Mem.range_perm_free.
    apply Mem.free_range_perm in H0.
    clear - H0 Hmsim1 H4.
    unfold Mem.range_perm in *.
    intros ofs J.
    assert (lo <= ofs - delta < hi) as J'.
      auto with zarith.
    apply H0 in J'.
    eapply MoreMem.perm_inj in J'; eauto.
    assert (ofs - delta + delta = ofs) as EQ. auto with zarith.
    rewrite EQ in J'. auto.
  destruct J as [Mem2' J].
  exists Mem2'. split; auto.
  split.
  SCase "wfmi".
    clear - Hwfmi H0 J H4.
    inversion_clear Hwfmi.
    split; eauto with mem.
    SSCase "Hmap3".
      intros. erewrite Mem.nextblock_free in H; eauto.
    SSCase "Hmap4".
      intros. erewrite Mem.nextblock_free; eauto.
    SSCase "bounds".
      intros. apply mi_bounds in H. 
      erewrite Mem.bounds_free; eauto.
      erewrite Mem.bounds_free with (m2:=Mem2'); eauto.

  SCase "msim".
    clear - Hmsim1 Hwfmi H0 J H4.
    inv Hwfmi.
    eapply MoreMem.free_inj; eauto.
Qed.

Lemma mem_simulation__free : forall mi TD Mem1 Mem2 Mem1' Mem2'
  ECs1 pinfo maxb lc1 F ptr1 ptr2
  (Hmsim : mem_simulation pinfo maxb mi ((F, lc1) :: ECs1) Mem1 Mem2)
  (Hsim: gv_inject mi ptr1 ptr2)
  (Hmlc: free TD Mem1 ptr1 = ret Mem1')
  (Hmlc': free TD Mem2 ptr2 = ret Mem2'),
  mem_simulation pinfo maxb mi ((F, lc1) :: ECs1) Mem1' Mem2'.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  apply free_inv in Hmlc.
  apply free_inv in Hmlc'.
  destruct Hmlc as [blk [ofs [hi [lo [H1 [H2 [H3 H4]]]]]]].
  destruct Hmlc' as [blk' [ofs' [hi' [lo' [H1' [H2' [H3' H4']]]]]]].
  unfold GV2ptr in *.
  destruct ptr1 as [|[[]][]]; inv H1.
  destruct ptr2 as [|[[]][]]; inv H1'.
  inv Hsim. inv H1.
  eapply mem_inj__free in H4; eauto.
  destruct H4 as [Mem2'' [J4 [J5 J6]]].
  assert (H6':=H6).
  apply (mi_range_block maxb mi Mem1 Mem2 J3) in H6. subst.
  apply (mi_bounds maxb mi Mem1 Mem2 J3) in H6'. 
  rewrite H6' in H3. rewrite <- H3 in H3'. inv H3'.
  assert (lo + 0 = lo) as EQ1. omega.
  assert (hi + 0 = hi) as EQ2. omega.
  rewrite EQ1 in J4. rewrite EQ2 in J4. clear EQ1 EQ2.
  rewrite J4 in H4'. inv H4'.
  split; auto.
Qed.

Lemma isnt_alloca_in_ECs_tail: forall pinfo (mi:MoreMem.meminj) EC1 EC2 ECs ,
  (forall blk, 
    ~ isnt_alloca_in_ECs pinfo (EC1 :: EC2 :: ECs) blk -> mi blk = merror) ->
  (forall blk, 
    ~ isnt_alloca_in_ECs pinfo (EC2 :: ECs) blk -> mi blk = merror).
Proof.
  intros.
  apply H; auto. 
  intro J. apply H0.
  unfold isnt_alloca_in_ECs in J. unfold isnt_alloca_in_ECs.
  intros.
  apply J; auto.
  simpl. simpl in Hin. destruct Hin; auto.
Qed.

Lemma mem_simulation_tail: forall pinfo mgb mi EC1 EC2 ECs M1 M2,
  mem_simulation pinfo mgb mi (EC1 :: EC2 :: ECs) M1 M2 ->
  mem_simulation pinfo mgb mi (EC2 :: ECs) M1 M2.
Proof.
  intros.
  destruct H as [J1 [J2 J3]].
  split; auto.
  split; auto.
    eapply isnt_alloca_in_ECs_tail; eauto.
Qed.

Ltac inv_mbind'' :=
  repeat match goal with
         | H : match ?e with
               | Some _ => _
               | None => None
               end = Some _ |- _ => remember e as R; destruct R as [|]; inv H
         | H : Some _ = match ?e with
               | Some _ => _
               | None => None
               end |- _ => remember e as R; destruct R as [|]; inv H
         | H :  ret _ = match ?p with
                        | (_, _) => _
                        end |- _ => destruct p
         | H : if ?e then _ else False |- _ => 
             remember e as R; destruct R; tinv H
         | H : if ?e then False else _ |- _ => 
             remember e as R; destruct R; tinv H
         end.

(* should move to MoreMem. *)
Lemma free_left_nonmap_inj:
  forall f m1 m2 b lo hi m1' (Hprop: f b = None),
  MoreMem.mem_inj f m1 m2 ->
  Mem.free m1 b lo hi = Some m1' ->
  MoreMem.mem_inj f m1' m2.
Proof.
  intros. exploit Mem.free_result; eauto. intro FREE. inversion H. constructor.
(* access *)
  intros. eauto with mem. 
(* mem_contents *)
  intros. rewrite FREE; simpl.
  assert (b=b1 /\ lo <= ofs < hi \/ (b<>b1 \/ ofs<lo \/ hi <= ofs)) 
    by (unfold Values.block; omega).
  destruct H3.
    destruct H3. subst b1. uniq_result.

    rewrite (Mem.clearN_out _ _ _ _ _ _ H3).
    apply mi_memval; auto.
    eapply Mem.perm_free_3; eauto.
Qed.

Lemma mem_inj__pfree : forall mi Mem0 M2 Mem' mgb hi lo
  (b2 : Values.block) (delta : Z) blk,
  wf_sb_mi mgb mi Mem0 M2 ->
  MoreMem.mem_inj mi Mem0 M2 ->
  Mem.free Mem0 blk lo hi = ret Mem' ->
  (lo, hi) = Mem.bounds Mem0 blk ->
  mi blk = None ->
  wf_sb_mi mgb mi Mem' M2 /\ MoreMem.mem_inj mi Mem' M2.
Proof.
  intros mi Mem0 M2 Mem' mgb hi lo b2 delta blk Hwfmi Hmsim1 H0 HeqR2 H4.
  split.
  SCase "wfmi".
    clear - Hwfmi H0 H4.
    inversion_clear Hwfmi.
    split; eauto with mem.
    SSCase "Hmap3".
      intros. erewrite Mem.nextblock_free in H; eauto.
    SSCase "bounds".
      intros. apply mi_bounds in H. 
      erewrite Mem.bounds_free; eauto.

  SCase "msim".
    clear - Hmsim1 Hwfmi H0 H4.
    inv Hwfmi.
    eapply free_left_nonmap_inj; eauto.
Qed.

Lemma mem_simulation__pfree : forall mi TD Mem1 Mem2 Mem1' ECs1 pinfo maxb lc1
  F (Hmsim : mem_simulation pinfo maxb mi ((F, lc1) :: ECs1) Mem1 Mem2)  
  a (Hfree: free TD Mem1 (blk2GV TD a) = Some Mem1')
  (Hinj: mi a = merror) (Hisallca: is_alloca_in_EC pinfo F lc1 a = true),
  mem_simulation pinfo maxb mi ((F, lc1) :: ECs1) Mem1' Mem2.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  apply free_inv in Hfree.
  destruct Hfree as [blk [ofs [hi [lo [H1 [H2 [H3 H4]]]]]]].
  unfold GV2ptr in *. unfold blk2GV, ptr2GV, val2GV in H1. inv H1. 
  eapply mem_inj__pfree in H4; eauto.
  destruct H4 as [H41 H42].
  split; auto.
Qed.

Lemma mem_simulation__free_allocas : forall TD mgb F lc EC pinfo mi 
  als1 M1 als2 M2 M1' 
  (Hfree1: free_allocas TD M1 als1 = Some M1')
  (Hmsim: mem_simulation pinfo mgb mi ((F,lc)::EC) M1 M2) M2'
  (Halsim: als_simulation pinfo mi F lc als1 als2)
  (Hfree2: free_allocas TD M2 als2 = Some M2'),
  mem_simulation pinfo mgb mi ((F,lc)::EC) M1' M2'.
Proof.
  induction als1; destruct als2; simpl; intros.
    uniq_result. auto.
    uniq_result.

    inv_mbind''. uniq_result.
    destruct Halsim as [J1 J2].
    eapply IHals1 with (M1:=m)(M2:=M2'); eauto.
    eapply mem_simulation__pfree in Hmsim; eauto.

    inv_mbind''. symmetry_ctx.
    remember (is_alloca_in_EC pinfo F lc a) as R.
    destruct R; destruct Halsim as [Halsim1 Halsim2].
      eapply mem_simulation__pfree in Hmsim; eauto.
      eapply IHals1 with (M1:=m1)(M2:=M2); eauto.
      simpl. rewrite HeqR. auto.

      eapply IHals1 with (M1:=m1)(M2:=m0); eauto.
      eapply mem_simulation__free with (ptr1:=blk2GV TD a) (ptr2:=blk2GV TD m) 
        in Hmsim; eauto.
      unfold blk2GV, ptr2GV, val2GV. simpl.
      constructor; auto.
        assert (Int.repr 31 0 = Int.add 31 (Int.repr 31 0) (Int.repr 31 0)) 
          as EQ.
          rewrite Int.add_zero. auto.
        rewrite EQ at 2.
        econstructor; eauto.
Qed.

Lemma free_allocas_return_void_sim : forall TD mgb F lc F' lc' EC pinfo mi 
  als1 M1 als2 M2 M1' 
  (Hfree1: free_allocas TD M1 als1 = Some M1')
  (Hmsim: mem_simulation pinfo mgb mi ((F,lc)::(F',lc')::EC) M1 M2) M2'
  (Halsim: als_simulation pinfo mi F lc als1 als2)
  (Hfree2: free_allocas TD M2 als2 = Some M2'),
  mem_simulation pinfo mgb mi ((F',lc')::EC) M1' M2'.
Proof.
  intros.
  eapply mem_simulation__free_allocas in Hmsim; eauto.
  apply mem_simulation_tail in Hmsim; auto.
Qed.

Lemma is_alloca_in_EC_update_lc: forall pinfo F lc id0 gvs0 blk,
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  is_alloca_in_EC pinfo F lc blk =
    is_alloca_in_EC pinfo F (updateAddAL (GVsT DGVs) lc id0 gvs0) blk.
Proof.
  intros.
  unfold is_alloca_in_EC in *.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  destruct H as [H | H]; try congruence.
  rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.  

Lemma isnt_alloca_in_ECs_update_non_palloca : 
  forall pinfo lc1 lc2 ECs F (mi:MoreMem.meminj) gvs3 id0,
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  updateAddAL (GVsT DGVs) lc1 id0 gvs3 = lc2 ->
  (forall blk:mblock, 
    ~ isnt_alloca_in_ECs pinfo ((F, lc1) :: ECs) blk -> 
    mi blk = merror) ->
  (forall blk:mblock, 
    ~ isnt_alloca_in_ECs pinfo ((F, lc2) :: ECs) blk -> 
    mi blk = merror).
Proof.
  intros. subst. 
  apply H1. clear H1.
  intro J. apply H2. clear H2.
  unfold isnt_alloca_in_ECs in *.
  intros.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; subst.
    inv Hin.
    rewrite <- is_alloca_in_EC_update_lc; auto.
    apply J. simpl. auto.

    apply J. clear J. simpl. auto.
Qed.

Lemma mem_simulation__update_non_palloca : forall pinfo lc1 lc2 ECs F 
  (mi:MoreMem.meminj) gvs3 id0 Mem1 Mem2 mgb,
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  updateAddAL (GVsT DGVs) lc1 id0 gvs3 = lc2 ->
  mem_simulation pinfo mgb mi ((F, lc1) :: ECs) Mem1 Mem2 ->
  mem_simulation pinfo mgb mi ((F, lc2) :: ECs) Mem1 Mem2.
Proof.
  intros.
  destruct H1 as [J1 [J2 J3]].
  repeat (split; auto);
    eapply isnt_alloca_in_ECs_update_non_palloca; eauto; simpl; eauto.
Qed.

Lemma free_allocas_return_sim : forall TD mgb F 
  Result lc F' i0 n c t v p lc' ECs lc'' gl2 pinfo
  (Hneq: PI_f pinfo <> F' \/ PI_id pinfo <> i0)
  (Hupdate: Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc lc' 
              gl2 = ret lc'') mi
  als M1 als2 M2 M1' M2'
  (Hmsim: mem_simulation pinfo mgb mi ((F, lc) :: (F', lc') :: ECs) 
    M1 M2) 
  (Hfree1: free_allocas TD M1 als = Some M1')
  (Halsim: als_simulation pinfo mi F lc als als2)
  (Hfree2: free_allocas TD M2 als2 = Some M2'),
  mem_simulation pinfo mgb mi ((F',lc'') :: ECs) M1' M2'.
Proof.
  intros.
  eapply free_allocas_return_void_sim in Hmsim; eauto.
  unfold Opsem.returnUpdateLocals in Hupdate.
  inv_mbind'.
  destruct n; inv H0; auto.
  destruct t; inv H1; auto.
  inv_mbind'.
  eapply mem_simulation__update_non_palloca; eauto.
Qed.

Lemma als_simulation_update_lc: forall pinfo F lc mi id0 gvs0 als1 als2,
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  als_simulation pinfo mi F lc als1 als2 ->
  als_simulation pinfo mi F (updateAddAL (GVsT DGVs) lc id0 gvs0) als1 als2.
Proof.
  induction als1; destruct als2; simpl; auto.
    intros.
    rewrite <- is_alloca_in_EC_update_lc; auto.
    destruct (is_alloca_in_EC pinfo F lc a); auto.
    destruct H0 as [J1 J2].
    split; auto.

    intros.
    rewrite <- is_alloca_in_EC_update_lc; auto.
    destruct (is_alloca_in_EC pinfo F lc a); destruct H0 as [J1 J2]; split; auto.
Qed.

Lemma returnUpdateLocals_als_simulation: forall pinfo mi F' lc' als' als3 TD i0 n
  c t v p Result lc gl2 lc'' (Hsim: als_simulation pinfo mi F' lc' als' als3)
  (Hprop: PI_f pinfo <> F' \/ PI_id pinfo <> i0)
  (Hupdate: Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc lc' 
              gl2 = ret lc''),
  als_simulation pinfo mi F' lc'' als' als3.
Proof.
  intros.
  unfold Opsem.returnUpdateLocals in Hupdate.
  inv_mbind'.
  destruct n; inv H0; auto.
  destruct t; inv H1; auto.
  inv_mbind'.
  apply als_simulation_update_lc; auto.
Qed.
  
Lemma reg_simulation_update_non_palloca: forall pinfo F lc1 lc2 mi id0 gvs0 gvs3,
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  reg_simulation pinfo mi F lc1 lc2 ->
  gv_inject mi gvs0 gvs3 ->
  reg_simulation pinfo mi F (updateAddAL (GVsT DGVs) lc1 id0 gvs0)
    (updateAddAL (GVsT DGVs) lc2 id0 gvs3).
Proof.
  unfold reg_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) F); subst; intros.
    assert (J:=@H0 i0). clear H0.
    destruct H as [H | H]; try congruence.
    destruct (id_dec (PI_id pinfo) i0); subst; auto.
    destruct (id_dec id0 i0); subst.
      rewrite lookupAL_updateAddAL_eq; auto.
      rewrite lookupAL_updateAddAL_eq; auto.
      intros. inv H2. inv H0. auto.

      rewrite <- lookupAL_updateAddAL_neq; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.

    assert (J:=@H0 i0). clear H0.
    destruct (id_dec id0 i0); subst.
      rewrite lookupAL_updateAddAL_eq in H2; auto.
      rewrite lookupAL_updateAddAL_eq in H3; auto.
      inv H2. inv H3. auto.

      rewrite <- lookupAL_updateAddAL_neq in H2; auto.
      rewrite <- lookupAL_updateAddAL_neq in H3; auto.
Qed.

Definition value_doesnt_use_pid pinfo F v := 
 PI_f pinfo <> F \/ used_in_value (PI_id pinfo) v = false.

Lemma simulation__getOperandValue : forall pinfo maxb mi lc lc2 TD Mem Mem2 gl F 
  v gv gv' (Hprop: value_doesnt_use_pid pinfo F v),
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  getOperandValue TD v lc gl = ret gv ->
  getOperandValue TD v lc2 gl = ret gv' ->
  gv_inject mi gv gv'.
Proof.
  intros.
  unfold getOperandValue in *.
  unfold reg_simulation in H1.  
  destruct (fdef_dec (PI_f pinfo) F); subst.
    destruct Hprop as [Hprop | Hprop]; try congruence.
    destruct v; simpl in Hprop.
      assert (J:=@H1 i0). clear H1.
      destruct (id_dec (PI_id pinfo) i0); subst; eauto.
        destruct (id_dec (PI_id pinfo) (PI_id pinfo)); 
          simpl in Hprop; try congruence.
    
      uniq_result. eapply sb_mem_inj__const2GV; eauto.

    destruct v; eauto.
      uniq_result. eapply sb_mem_inj__const2GV; eauto.
Qed.

(* from sb_ds_trans_lib, should go to sb_ds_gv_inject *)
Lemma gv_inject__same_size : forall mi gv1 gv2,
  gv_inject mi gv1 gv2 ->
  sizeGenericValue gv1 = sizeGenericValue gv2.
Proof.
  intros mi gv1 gv2 Hinj.
  induction Hinj; simpl; auto.
Qed.

Lemma simulation__lift_opt1: forall (mi : MoreMem.meminj) (TD : TargetData)
  (t : typ) (g1 g2 g2' g1': GVsT DGVs)
  (HeqR2 : lift_op1 DGVs (fit_gv TD t) g2 t = ret g2')
  (HeqR1 : lift_op1 DGVs (fit_gv TD t) g1 t = ret g1')
  (HeqR : gv_inject mi g1 g2),
  gv_inject mi g1' g2'.
Proof.
  intros.
Transparent lift_op1.
  unfold lift_op1 in *. simpl in *.
  unfold MDGVs.lift_op1 in *.
  unfold fit_gv in *.
  inv_mbind'. symmetry_ctx.
  erewrite gv_inject__same_size in H0; eauto.
  destruct (sizeGenericValue g2 =n= nat_of_Z (ZRdiv (Z_of_nat n) 8)).
    inv HeqR2. inv H0. auto.

    uniq_result.
    eapply gv_inject_gundef; eauto.
Opaque lift_op1.
Qed.

Lemma returnUpdateLocals_reg_simulation: forall pinfo mi F' lc' TD i0 n
  c t v p Result lc gl lc'' lc3 lc''0 lc2 F Mem1 Mem2 maxb
  (Hwfg: wf_globals maxb gl) (Hwfmi: wf_sb_mi maxb mi Mem1 Mem2)
  (Hprop: PI_f pinfo <> F' \/ PI_id pinfo <> i0)
  (Hprop': value_doesnt_use_pid pinfo F Result)
  (Hsim: reg_simulation pinfo mi F' lc' lc3)
  (Hsim': reg_simulation pinfo mi F lc lc2)
  (Hupdate: Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc lc' 
              gl = ret lc'')
  (Hupdate': Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc2 lc3
              gl = ret lc''0),
  reg_simulation pinfo mi F' lc'' lc''0.
Proof.
  intros.
  unfold Opsem.returnUpdateLocals in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue in HeqR; eauto.
  destruct n; uniq_result; auto.
  destruct t; tinv H0.
  inv_mbind'. symmetry_ctx.
  apply reg_simulation_update_non_palloca; auto.
  eapply simulation__lift_opt1; eauto.
Qed.

Lemma phis_simulation_inv: forall pinfo F ps1 ps2,
  WF_PhiInfo pinfo -> uniqFdef F ->
  phis_simulation pinfo F ps1 ps2 -> ps1 = ps2.
Proof.
  unfold phis_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  unfold remove_phinodes.
  admit. (*WF_PI*)
Qed.

Lemma block_simulation__getValueViaBlockFromValuels: forall pinfo F B1 B2 l0,
  block_simulation pinfo F B1 B2 ->
  getValueViaBlockFromValuels l0 B1 = getValueViaBlockFromValuels l0 B2.
Proof.
  destruct B1, B2; simpl; intros.
  unfold block_simulation in H.
  destruct (fdef_dec (PI_f pinfo) F); subst.
    simpl in H. inv H. auto.  
    inv H. auto.
Qed.

Lemma incoming_values_dont_use_pid: forall pinfo F l3 l0 v
  (Hnuse : PI_f pinfo <> F \/ used_in_list_value_l (PI_id pinfo) l0 = false)
  (HeqR3 : getValueViaLabelFromValuels l0 l3 = ret v),
  value_doesnt_use_pid pinfo F v.
Proof.
  induction l0; simpl; intros.
    congruence.

    unfold value_doesnt_use_pid.
    destruct (fdef_dec (PI_f pinfo) F); subst; auto.
      right.
      destruct Hnuse as [Hnuse | Hnuse]; try congruence.
      binvf Hnuse as J1 J2.
      destruct (l0 == l3); inv HeqR3; auto.
      apply IHl0 in H0; auto.
      unfold value_doesnt_use_pid in H0.
      destruct H0 as [H0 | H0]; try congruence.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_rsim : forall TD B1 B2 gl F mi lc1' 
  maxb Mem1 Mem2
  (Hwfg: wf_globals maxb gl) (Hwfmi: wf_sb_mi maxb mi Mem1 Mem2)
  pinfo lc2' ps 
  (Hnuse: PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps))
  (Hnuse': PI_f pinfo <> F \/ 
           fold_left
             (fun (re : bool) (p : phinode) => re || used_in_phi (PI_id pinfo) p)
           ps false = false)
  (l3 l0:list (id * GVsT DGVs))
  (HeqR0 : Opsem.getIncomingValuesForBlockFromPHINodes TD ps B1 gl lc1' =
           ret l3)
  (Hbsim2 : block_simulation pinfo F B1 B2)
  (Hrsim : reg_simulation pinfo mi F lc1' lc2')
  (HeqR : Opsem.getIncomingValuesForBlockFromPHINodes TD ps B2 gl lc2' =
          ret l0),
  reg_simulation pinfo mi F (Opsem.updateValuesForNewBlock l3 lc1')
     (Opsem.updateValuesForNewBlock l0 lc2').
Proof.
  induction ps as [|[]]; simpl; intros.
    uniq_result. simpl. auto.

    inv_mbind'. symmetry_ctx. simpl.
    assert (PI_f pinfo <> F \/ PI_id pinfo <> i0) as J1.
      clear - Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
    assert (reg_simulation pinfo mi F 
             (Opsem.updateValuesForNewBlock l1 lc1')
             (Opsem.updateValuesForNewBlock l2 lc2')) as J2.
      assert (PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps)) as J3.
        clear - Hnuse.
        destruct Hnuse as [Hnuse | Hnuse]; auto.
      assert (PI_f pinfo <> F \/
              fold_left
                (fun (re : bool) (p : phinode) => 
                  re || used_in_phi (PI_id pinfo) p)
                 ps false = false) as J4.
        clear - Hnuse'.
        destruct Hnuse' as [Hnuse' | Hnuse']; auto.
        right.
        assert (J:=Hnuse').
        apply fold_left_eq in J. 
          rewrite J in Hnuse'. auto.
          intros. apply orb_false_iff in H. destruct H; auto.
      apply IHps; auto.
    apply reg_simulation_update_non_palloca; auto.
      erewrite block_simulation__getValueViaBlockFromValuels in HeqR3; eauto.
      rewrite HeqR3 in HeqR1. inv HeqR1.
      eapply simulation__getOperandValue with (lc:=lc1')(lc2:=lc2'); eauto.
 
      destruct B2. simpl in HeqR3.
      assert (PI_f pinfo <> F \/ used_in_list_value_l (PI_id pinfo) l0 = false)
        as J3.
        clear - Hnuse'.
        destruct Hnuse' as [Hnuse' | Hnuse']; auto.
        right.
        apply fold_left_eq in Hnuse'; auto.
          intros. apply orb_false_iff in H. destruct H; auto.
      eapply incoming_values_dont_use_pid; eauto.
Qed.

Lemma switchToNewBasicBlock_rsim : forall TD l1 l2 ps cs1 cs2 tmn1 tmn2 B1 B2
  gl lc1 lc2 F pinfo mi lc1' lc2' maxb Mem1 Mem2
  (Hwfg: wf_globals maxb gl) (Hwfmi: wf_sb_mi maxb mi Mem1 Mem2)
  (Hnuse': PI_f pinfo <> F \/ 
           fold_left
             (fun (re : bool) (p : phinode) => re || used_in_phi (PI_id pinfo) p)
           ps false = false)
  (Hwfp: WF_PhiInfo pinfo) (Huniq: uniqFdef F)
  (HBinF: blockInFdefB (block_intro l1 ps cs1 tmn1) F = true)
  (H23 : @Opsem.switchToNewBasicBlock DGVs TD
          (block_intro l1 ps cs1 tmn1) B1 gl lc1' = 
         ret lc1)
  (Hbsim2 : block_simulation pinfo F B1 B2)
  (Hrsim: reg_simulation pinfo mi F lc1' lc2')
  (H2 : Opsem.switchToNewBasicBlock TD
         (block_intro l2 ps cs2 tmn2) B2 gl lc2' = 
        ret lc2), reg_simulation pinfo mi F lc1 lc2.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in *. simpl in *.
  inv_mbind'. symmetry_ctx. 
  eapply getIncomingValuesForBlockFromPHINodes_rsim; eauto.
    admit. (* wf_phi *)
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_asim: 
  forall pinfo F als1 als2 lc mi gl B TD
  (Hsim: als_simulation pinfo mi F lc als1 als2) ps l1
  (Hnuse: PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps)),
  Opsem.getIncomingValuesForBlockFromPHINodes TD ps B gl lc = ret l1 ->
  als_simulation pinfo mi F (Opsem.updateValuesForNewBlock l1 lc) als1 als2.
Proof.
  induction ps as [|[]]; simpl; intros.
    uniq_result. simpl. auto.

    inv_mbind'. symmetry_ctx. simpl.
    assert (PI_f pinfo <> F \/ PI_id pinfo <> i0) as J1.
      clear - Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
    assert (PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps)) as J2.
      clear - Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
    apply als_simulation_update_lc; auto.
Qed.

Lemma switchToNewBasicBlock_asim: forall pinfo F l0 ps0 cs0 tmn0 als1 als2 lc 
  lc' mi gl B TD,
  WF_PhiInfo pinfo -> uniqFdef F ->
  blockInFdefB (block_intro l0 ps0 cs0 tmn0) F = true ->
  als_simulation pinfo mi F lc als1 als2 ->
  Opsem.switchToNewBasicBlock TD (block_intro l0 ps0 cs0 tmn0) B gl lc = 
    ret lc' ->
  als_simulation pinfo mi F lc' als1 als2.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in *. simpl in *.
  inv_mbind'. symmetry_ctx. 
  eapply getIncomingValuesForBlockFromPHINodes_asim; eauto.
    admit. (* wf_phi *)
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_isnt_alloca_in_ECs : 
  forall pinfo TD ECs F gl B blk ps lc1 l0
  (Hnuse: PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps)),
  Opsem.getIncomingValuesForBlockFromPHINodes TD ps B gl lc1 = ret l0 ->
  isnt_alloca_in_ECs pinfo ((F,lc1) :: ECs) blk ->
  isnt_alloca_in_ECs pinfo ((F,Opsem.updateValuesForNewBlock l0 lc1) :: ECs) blk.
Proof.
  induction ps as [|[]]; simpl; intros.
    uniq_result. simpl. auto.

    inv_mbind'. symmetry_ctx. simpl.
    assert (PI_f pinfo <> F \/ ~ In (PI_id pinfo) (getPhiNodesIDs ps)) as J.
      clear - Hnuse.
      destruct Hnuse; auto.
    apply IHps in HeqR1; auto. clear IHps.
    unfold isnt_alloca_in_ECs. unfold isnt_alloca_in_ECs in H0.
    intros.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
      inv Hin.
      rewrite <- is_alloca_in_EC_update_lc.
        apply HeqR1. simpl. auto.
        clear - Hnuse. destruct Hnuse; auto.
      apply H0. simpl. auto.
Qed.

Lemma switchToNewBasicBlock_isnt_alloca_in_ECs : 
  forall pinfo TD ECs F gl B B' blk lc1 lc2,
  WF_PhiInfo pinfo -> uniqFdef F ->
  blockInFdefB B' F = true ->
  Opsem.switchToNewBasicBlock TD B' B gl lc1 = ret lc2 ->
  isnt_alloca_in_ECs pinfo ((F,lc1) :: ECs) blk ->
  isnt_alloca_in_ECs pinfo ((F,lc2) :: ECs) blk.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in *. simpl in *.
  inv_mbind'. symmetry_ctx. 
  destruct B'. simpl in *.
  eapply getIncomingValuesForBlockFromPHINodes_isnt_alloca_in_ECs; eauto.
    admit. (* wf_phi *)
Qed.

Lemma Promotability_wf_EC__isnt_alloca_in_EC: forall maxb pinfo TD M1 f lc als,
  (if fdef_dec (PI_f pinfo) f
      then Promotability.wf_defs maxb pinfo TD M1 lc als
      else True) ->
  is_alloca_in_EC pinfo f lc (Mem.nextblock M1) = false.
Proof.
  intros.
  unfold is_alloca_in_EC.
  destruct (fdef_dec (PI_f pinfo) f); subst; auto.
  remember (lookupAL (GVsT DGVs) lc (PI_id pinfo)) as R.
  destruct R as [[]|]; auto.
  destruct p as [[]]; auto.
  destruct l0; auto.
  destruct (Z_eq_dec b (Mem.nextblock M1)); subst; auto.
  symmetry in HeqR.
  apply H in HeqR.
  destruct HeqR as [HeqR _].
  destruct HeqR as [HeqR _].
  destruct HeqR as [mb [J1 [J2 J3]]].
  rewrite Promotability.simpl_blk2GV in J1.
  inv J1. 
  contradict J3; omega.
Qed.

Lemma Promotability_wf_ECs__isnt_alloca_in_ECs: forall maxb pinfo TD M1 ECs1,
  Promotability.wf_ECStack maxb pinfo TD M1 ECs1 ->
  isnt_alloca_in_ECs pinfo (strip_ECs ECs1) (Mem.nextblock M1).
Proof.
  induction ECs1; simpl; intros.
    unfold isnt_alloca_in_ECs.
    intros. inv Hin.

    destruct H as [H1 [H2 H3]].
    unfold isnt_alloca_in_ECs in *.
    intros.
    simpl in Hin.
    destruct Hin as [Hin | Hin]; subst.
      inv Hin. destruct a. destruct H1.
      eapply Promotability_wf_EC__isnt_alloca_in_EC; eauto.

      apply IHECs1; simpl; auto.
Qed.

Lemma malloc__is_alloca_in_EC: forall maxb pinfo TD Mem f lc tsz0 gn align0 Mem'
  mb (mi mi':MoreMem.meminj) als
  (H1: if fdef_dec (PI_f pinfo) f
       then Promotability.wf_defs maxb pinfo TD Mem lc als
       else True)
  (H2: malloc TD Mem tsz0 gn align0 = ret (Mem', mb))
  (Hprop2 : forall b : mblock, b <> mb -> mi b = mi' b),
  forall blk : mblock,
    is_alloca_in_EC pinfo f lc blk= true -> 
    mi blk = merror -> mi' blk = merror.
Proof.
  intros.
  destruct (zeq blk mb); subst.
    apply MemProps.malloc_result in H2. subst.
    eapply Promotability_wf_EC__isnt_alloca_in_EC in H1; eauto.
    rewrite H1 in H. inv H.

    rewrite <- Hprop2; auto.
Qed.

Lemma malloc__isnt_alloca_in_ECs: forall maxb pinfo TD Mem EC tsz0 gn align0 Mem'
  mb (mi mi':MoreMem.meminj) (H1: Promotability.wf_ECStack maxb pinfo TD Mem EC)
  (H2: malloc TD Mem tsz0 gn align0 = ret (Mem', mb))
  (Hprop2 : forall b : mblock, b <> mb -> mi b = mi' b),
  forall blk : mblock,
    ~ isnt_alloca_in_ECs pinfo (strip_ECs EC) blk -> 
    mi blk = merror -> mi' blk = merror.
Proof.
  intros.
  destruct (zeq blk mb); subst.
    apply MemProps.malloc_result in H2. subst.
    contradict H.
    eapply Promotability_wf_ECs__isnt_alloca_in_ECs; eauto.

    rewrite <- Hprop2; auto.
Qed.

(*
  lookupAL _ lc1 (PI_id pinfo) = None is important.

  if p = alloca is in a loop, then at runtime, 
    p can be assigned multiple times by p1, p2, p3...
    all of which will be erased, and should not have corresponding memory block
    in the transformed program.

  But, we can only keep track of the last one, the earlier ones will be 
   over-written...

  In practice, a promotable allocation is always at the entry block, so
  before its first assignment, its value must be none. Therefore, we are fine.
*)
Lemma als_simulation_weaken_palloca: 
  forall mi' mb mi pinfo lc1 ofs mc
  (Hlkup : lookupAL _ lc1 (PI_id pinfo) = None)
  (Hmi1 : mi' mb = merror)
  (Hmi2 : forall b : mblock, b <> mb -> mi b = mi' b)
  als1 als2 
  (Hsim : als_simulation pinfo mi (PI_f pinfo) lc1 als1 als2)
  (Hfresh : forall al, In al als1 -> al <> mb),
  als_simulation pinfo mi' (PI_f pinfo)
    (updateAddAL _ lc1 (PI_id pinfo) ((Vptr mb ofs, mc) :: nil)) 
    als1 als2.
Proof.
  induction als1; simpl; intros; auto.
    unfold is_alloca_in_EC in *.
    rewrite Hlkup in Hsim.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    destruct (id_dec (PI_id pinfo) (PI_id pinfo)); try congruence.
    rewrite lookupAL_updateAddAL_eq.
    destruct (Z_eq_dec mb a); subst.
      assert (a <> a) as Hneq.
        apply Hfresh; auto.
      congruence.

      destruct als2; auto.
      destruct Hsim as [Hsim1 Hsim2].
      split.
        rewrite <- Hmi2; auto.
        apply IHals1; auto.
Qed.    

Lemma als_simulation_update_palloca: 
  forall mi' mb mi pinfo lc1 TD M1 tsz gn M1'
  (H21: malloc TD M1 tsz gn (PI_align pinfo) = Some (M1', mb))
  (Hlkup : lookupAL _ lc1 (PI_id pinfo) = None)
  (Hmi1 : mi' mb = merror)
  (Hmi2 : forall b : mblock, b <> mb -> mi b = mi' b) maxb
  als1 als2 (Hsim : als_simulation pinfo mi (PI_f pinfo) lc1 als1 als2) ECs1
  (Halsbd : forall al : Values.block,
            In al
              (als1 ++
               flat_map
                 (fun ec : @Opsem.ExecutionContext DGVs =>
                  let '{| Opsem.Allocas := als |} := ec in als) ECs1) ->
            maxb < al < Mem.nextblock M1),
  als_simulation pinfo mi' (PI_f pinfo)
    (updateAddAL _ lc1 (PI_id pinfo) 
      ($ blk2GV TD mb # typ_pointer (PI_typ pinfo) $)) 
      (mb::als1) als2.
Proof.
  intros.
  simpl.
  unfold is_alloca_in_EC.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  destruct (id_dec (PI_id pinfo) (PI_id pinfo)); try congruence.
  rewrite lookupAL_updateAddAL_eq.
  rewrite Promotability.simpl_blk2GV.
  destruct (Z_eq_dec mb mb); try congruence.
  split; auto.    
    eapply als_simulation_weaken_palloca; eauto.
      apply MemProps.malloc_result in H21.
      intros. intro EQ. subst.
      assert (maxb < Mem.nextblock M1 < Mem.nextblock M1) as J.
        apply Halsbd. simpl. 
        apply in_or_app; auto.
      contradict J. omega.
Qed.

Lemma dae_is_sim_removable_state: forall (maxb : Values.block) (pinfo : PhiInfo)
  (mi : MoreMem.meminj) (Cfg1 : OpsemAux.Config) (St1 : Opsem.State) 
  (Cfg2 : OpsemAux.Config) (St2 : Opsem.State) (Hwfpi : WF_PhiInfo pinfo)
  (Hwfgl : wf_globals maxb (OpsemAux.Globals Cfg1)) (Hinbd : 0 <= maxb)
  (Hnuse : used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfpp : OpsemPP.wf_State Cfg1 St1)
  (Hnoalias : Promotability.wf_State maxb pinfo Cfg1 St1)
  (Hsim : State_simulation pinfo maxb mi Cfg1 St1 Cfg2 St2)
  (Hrem : removable_State pinfo St1) (St1' : Opsem.State) (tr1 : trace)
  (Hop1 : Opsem.sInsn Cfg1 St1 St1' tr1),
  exists mi' : MoreMem.meminj,
    State_simulation pinfo maxb mi' Cfg1 St1' Cfg2 St2 /\
    tr1 = trace_nil /\ inject_incr mi mi'.
Proof.
  intros.
  destruct Cfg1 as [S1 [los nts] Ps1 gl1 fs1].
  destruct St1 as [ECs1 M1].
  destruct ECs1 as [|[F1 B1 [|c1 cs1] tmn1 lc1 als1] ECs1]; tinv Hrem.
  simpl in Hrem.
  destruct (fdef_dec (PI_f pinfo) F1); subst; tinv Hrem.
  destruct (id_dec (PI_id pinfo) (getCmdLoc c1)); subst; tinv Hrem.
  assert (exists v, 
    c1 = insn_alloca (PI_id pinfo) (PI_typ pinfo) v (PI_align pinfo)) as EQ.
    admit. (* uniqness *)
  destruct EQ as [v EQ]; subst.
  
  destruct Hwfpp as 
    [Hwfg [HwfSystem [HmInS [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [HwfECs Hwfcall]]
    ]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs.

  destruct Hnoalias as 
    [
      [[Hinscope' _] [HwfECs' HwfHT]] 
      [[Hdisjals Halsbd] HwfM]
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
      [Hfsim2 [Heq1 [Halsim2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst.

  uniq_result.
  eapply mem_simulation__palloca in Hmsim; eauto.
  destruct Hmsim as [mi' [Hmsim [Hinc [Hmi1 Hmi2]]]].
  exists mi'.  
  repeat_solve.
    eapply als_simulation_update_palloca; eauto.
      admit. (*dom*)
    eapply reg_simulation_update_palloca; eauto.
    eapply cmds_simulation_elim_cons_inv; eauto.
    eapply inject_incr__preserves__ECs_simulation; eauto.
      eapply malloc__isnt_alloca_in_ECs; eauto.
    eapply inject_incr__preserves__ftable_simulation; eauto.
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
       Opsem.Mem := Mem |} => PI_f pinfo <> F \/ PI_id pinfo <> getCmdLoc c
  | _ => True
  end.
Proof.
  intros.
  destruct St; auto.
  destruct ECS; auto.
  destruct e; auto.
  destruct CurCmds; auto.
  simpl in H.
  destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
  destruct (id_dec (PI_id pinfo) (getCmdLoc c)); subst; auto.
Qed.

Lemma simulation__BOP : forall maxb mi lc lc2 TD gl F bop0 sz0 
    v1 v2 gv3 gv3' pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1)
  (Hprop2: value_doesnt_use_pid pinfo F v2),
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  BOP TD lc gl bop0 sz0 v1 v2 = ret gv3 ->
  BOP TD lc2 gl bop0 sz0 v1 v2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F bop0 sz0 v1 v2 gv3 gv3' pinfo Me Mem2 Hprop1
    Hprop2 Hwfg H0 H1 H2 H3.
  unfold BOP in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR2; eauto.
  eapply simulation__mbop in H2; eauto.
  destruct H2 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__FBOP : forall maxb mi lc lc2 TD gl F fop0 fp
    v1 v2 gv3 gv3' pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1)
    (Hprop2: value_doesnt_use_pid pinfo F v2),
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  FBOP TD lc gl fop0 fp v1 v2 = ret gv3 ->
  FBOP TD lc2 gl fop0 fp v1 v2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F fop0 fp v1 v2 gv3 gv3' pinfo Me Mem2 Hprop1
    Hprop2 Hwfg H0 H1 H2 H3.
  unfold FBOP in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR2; eauto.
  eapply simulation__mfbop in H2; eauto.
  destruct H2 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__ExtractValue : forall mi gv1 gv1' TD t1 l0 gv gv' gl2 lc
  lc2 v F pinfo Mem Mem2 maxb (Hprop: value_doesnt_use_pid pinfo F v),
  wf_globals maxb gl2 -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  getOperandValue TD v lc gl2 = Some gv1 ->
  getOperandValue TD v lc2 gl2 = Some gv1' ->
  extractGenericValue TD t1 gv1 l0 = Some gv ->
  extractGenericValue TD t1 gv1' l0 = Some gv' ->
  gv_inject mi gv gv'.
Proof.
  intros.
  eapply simulation__getOperandValue with (lc2:=lc2) in H2; eauto.
  eapply simulation__extractGenericValue in H4; eauto.
  destruct H4 as [gv'' [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__InsertValue : forall mi gv1 gv1' TD t1 l0 gv2 gv2' gl2 lc
  lc2 v1 v2 F pinfo Mem Mem2 maxb gv3 gv3' t2 
  (Hprop1: value_doesnt_use_pid pinfo F v1)
  (Hprop2: value_doesnt_use_pid pinfo F v2),
  wf_globals maxb gl2 -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  getOperandValue TD v1 lc gl2 = Some gv1 ->
  getOperandValue TD v1 lc2 gl2 = Some gv1' ->
  getOperandValue TD v2 lc gl2 = Some gv2 ->
  getOperandValue TD v2 lc2 gl2 = Some gv2' ->
  insertGenericValue TD t1 gv1 l0 t2 gv2 = ret gv3 ->
  insertGenericValue TD t1 gv1' l0 t2 gv2' = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.
  intros.
  eapply simulation__getOperandValue with (lc2:=lc2) in H2; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in H4; eauto.
  eapply simulation__insertGenericValue in H6; eauto.
  destruct H6 as [gv'' [J1 J2]].
  uniq_result. auto.
Qed.

Definition list_value_doesnt_use_pid pinfo F idxs := 
  PI_f pinfo <> F \/ used_in_list_value (PI_id pinfo) idxs = false.

Lemma simulation__values2GVs : forall maxb mi lc lc2 TD Mem Mem2 gl F idxs gvs 
  gvs' pinfo (Hprop: list_value_doesnt_use_pid pinfo F idxs),
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  values2GVs TD idxs lc gl = ret gvs ->
  values2GVs TD idxs lc2 gl = ret gvs' ->
  gvs_inject mi gvs gvs'.
Proof.
  induction idxs; simpl; intros.
    inv H2. inv H3. simpl. auto.

    inv_mbind'. symmetry_ctx.
    assert (list_value_doesnt_use_pid pinfo F idxs /\
            value_doesnt_use_pid pinfo F v) as J.
      unfold list_value_doesnt_use_pid in *.
      unfold value_doesnt_use_pid in *.
      simpl in Hprop.
      destruct Hprop as [Hprop | Hprop]; auto.
      apply orb_false_iff in Hprop.
      destruct Hprop; auto.
    destruct J as [J1 J2].
    eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
    simpl. split; eauto.
Qed.

Lemma simulation__GEP : forall maxb mi TD Mem Mem2 inbounds0 vidxs1 vidxs2 gv1 
    gv1' gv2 gv2' t gl2 lc lc2 idxs v F pinfo
  (Hprop1: value_doesnt_use_pid pinfo F v) 
  (Hprop2: list_value_doesnt_use_pid pinfo F idxs),
  wf_globals maxb gl2 -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  getOperandValue TD v lc gl2 = Some gv1 ->
  getOperandValue TD v lc2 gl2 = Some gv1' ->
  values2GVs TD idxs lc gl2 = Some vidxs1 ->
  values2GVs TD idxs lc2 gl2 = Some vidxs2 ->
  GEP TD t gv1 vidxs1 inbounds0 = ret gv2 ->
  GEP TD t gv1' vidxs2 inbounds0 = ret gv2' ->
  gv_inject mi gv2 gv2'.
Proof.
  intros.
  eapply simulation__getOperandValue with (lc2:=lc2) in H2; eauto.
  eapply simulation__values2GVs with (lc2:=lc2) in H4; eauto.
  eapply sb_ds_gv_inject.simulation__GEP in H6; eauto.
  destruct H6 as [gv'' [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__TRUNC : forall maxb mi lc lc2 TD gl F op t1 t2
    v1 gv3 gv3' pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1),
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  TRUNC TD lc gl op t1 v1 t2 = ret gv3 ->
  TRUNC TD lc2 gl op t1 v1 t2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F op t1 t2 v1 gv3 gv3' pinfo Mem Mem2 Hwfg Hprop1 
    H0 H1 H2 H3.
  unfold TRUNC in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR; eauto.
  eapply simulation__mtrunc in H3; eauto.
  destruct H3 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__EXT : forall maxb mi lc lc2 TD gl F op t1 t2
    v1 gv3 gv3' pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1),
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  EXT TD lc gl op t1 v1 t2 = ret gv3 ->
  EXT TD lc2 gl op t1 v1 t2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F op t1 t2 v1 gv3 gv3' pinfo Mem Mem2 Hprop1 Hwfg 
    H0 H1 H2 H3.
  unfold EXT in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR; eauto.
  eapply simulation__mext in H3; eauto.
  destruct H3 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__CAST : forall maxb mi lc lc2 TD gl F op t1 t2
    v1 gv3 gv3' pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1),
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  CAST TD lc gl op t1 v1 t2 = ret gv3 ->
  CAST TD lc2 gl op t1 v1 t2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F op t1 t2 v1 gv3 gv3' pinfo Mem Mem2 Hprop1 Hwfg 
    H0 H1 H2 H3.
  unfold CAST in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR; eauto.
  eapply simulation__mcast in H3; eauto.
  destruct H3 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__ICMP : forall maxb mi lc lc2 TD gl F cond0 t1 v1 v2 gv3 gv3' 
  pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1) 
  (Hprop2: value_doesnt_use_pid pinfo F v2), 
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  ICMP TD lc gl cond0 t1 v1 v2 = ret gv3 ->
  ICMP TD lc2 gl cond0 t1 v1 v2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F cond0 t1 v1 v2 gv3 gv3' pinfo Me Mem2 Hprop1 
    Hprop2 Hwfg H0 H1 H2 H3.
  unfold ICMP in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR2; eauto.
  eapply simulation__micmp in H2; eauto.
  destruct H2 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__FCMP : forall maxb mi lc lc2 TD gl F fcond0 fp v1 v2 gv3 gv3' 
  pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1) 
  (Hprop2: value_doesnt_use_pid pinfo F v2), 
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  FCMP TD lc gl fcond0 fp v1 v2 = ret gv3 ->
  FCMP TD lc2 gl fcond0 fp v1 v2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F cond0 t1 v1 v2 gv3 gv3' pinfo Me Mem2 Hprop1 
    Hprop2 Hwfg H0 H1 H2 H3.
  unfold FCMP in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR2; eauto.
  eapply simulation__mfcmp in H2; eauto.
  destruct H2 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma mem_simulation__wf_sb_sim: forall pinfo maxb mi ECs M1 M2,
  mem_simulation pinfo maxb mi ECs M1 M2 -> wf_sb_mi maxb mi M1 M2.  
Proof.
  intros. destruct H as [_ [_ H]]; auto.
Qed.

Lemma used_in_blocks_cons_inv : forall bs5 id0 b5,
  fold_left (fun (re : bool) b => re || used_in_block id0 b) 
    bs5 (used_in_block id0 b5) = false ->
  used_in_block id0 b5 = false /\
    fold_left (fun (re : bool) b => re || used_in_block id0 b) bs5 false 
      = false.
Proof.
  intros.
  destruct (used_in_block id0 b5); auto.
    apply fold_left_eq in H.
      congruence.
      intros. binvf H0 as J1 J2; auto.  
Qed.

Lemma used_in_blocks__used_in_block : forall id0 b bs,
  fold_left (fun (re : bool) (b0 : block) => re || used_in_block id0 b0) bs
    false = false ->
  InBlocksB b bs = true -> 
  used_in_block id0 b = false.
Proof.
  induction bs; simpl; intros.
    congruence.

    apply used_in_blocks_cons_inv in H. destruct H.
    binvt H0 as J1 J2; auto.
      apply blockEqB_inv in J1. subst. auto.
Qed.      

Lemma used_in_cmds_cons_inv : forall cs5 id0 c5
  (Hnouse : List.fold_left (fun re c => re || used_in_cmd id0 c) cs5 
    (used_in_cmd id0 c5) = false),
  used_in_cmd id0 c5 = false /\
    fold_left (fun (re : bool) c => re || used_in_cmd id0 c) cs5 false = false.
Proof.
  intros.
  destruct (used_in_cmd id0 c5); auto.
    apply fold_left_eq in Hnouse.
      congruence.
      intros. binvf H as J1 J2; auto.  
Qed.

Lemma used_in_cmds__used_in_cmd : forall id0 c cs,
  fold_left (fun (re : bool) c => re || used_in_cmd id0 c) cs
    false = false ->
  In c cs -> 
  used_in_cmd id0 c = false.
Proof.
  induction cs; simpl; intros.
    inv H0.

    apply used_in_cmds_cons_inv in H. destruct H.
    destruct H0 as [H0 | H0]; subst; auto.
Qed.      

Lemma used_in_list_value__used_in_value: forall id0 v vs,
  used_in_list_value id0 vs = false ->
  valueInListValue v vs ->
  used_in_value id0 v = false.
Proof.
  induction vs; simpl; intros.
    destruct v; auto.
      unfold valueInListValue in H0. simpl in H0. inv H0.

    unfold valueInListValue in H0.
    simpl in H0.
    binvf H as J3 J4; destruct H0 as [H0 | H0]; subst; auto.
Qed.

Lemma used_in_parameters_cons_inv : forall (ps:list (typ * attributes * value))
  (id0:id) (a:typ * attributes * value)
  (Hnouse : fold_left
        (fun (acc : bool) (p : typ * attributes * value) =>
         let '(_, v) := p in used_in_value id0 v || acc) ps
        (let '(_, v) := a in used_in_value id0 v || false) = false),
  (let '(_, v) := a in used_in_value id0 v = false) /\
  fold_left
        (fun (acc : bool) (p : typ * attributes * value) =>
         let '(_, v) := p in used_in_value id0 v || acc) ps false = false.
Proof.
  intros.
  destruct a.
  destruct (used_in_value id0 v); auto.
  apply fold_left_eq in Hnouse.
    binvf Hnouse as J1 J2. congruence.

    intros. destruct b.
    binvf H as J1 J2; auto.  
Qed.

Lemma valueInParams__used_in_value : forall id0 v p,
  fold_left
         (fun (acc : bool) (p : typ * attributes * value) =>
          let '(_, v) := p in used_in_value id0 v || acc) p false = false ->
  valueInParams v p -> 
  used_in_value id0 v = false.
Proof.
  induction p; simpl; intros.
    destruct v; auto.
      unfold valueInParams in H0. simpl in H0. inv H0.

    apply used_in_parameters_cons_inv in H.
    destruct H as [H1 H2].
    unfold valueInParams in H0.
    destruct a. simpl in H0.
    remember (split p) as R.
    destruct R.
    simpl in H0.
    destruct H0 as [H0 | H0]; subst; auto.
    apply IHp; auto.
    unfold valueInParams. rewrite <- HeqR. auto.
Qed.

Lemma used_in_cmd__used_in_value : forall id0 v c,
  used_in_cmd id0 c = false ->
  valueInCmdOperands v c -> 
  used_in_value id0 v = false.
Proof.
  induction c; simpl; intros;
    try solve [
      binvf H as J3 J4; destruct H0 as [H0 | H0]; subst; auto |
      subst; auto
    ].

    binvf H as J3 J4; destruct H0 as [H0 | H0]; subst; auto.
    eapply used_in_list_value__used_in_value; eauto.

    binvf H as J1 J2. binvf J1 as J1 J3.
    destruct H0 as [H0 | [H0 | H0]]; subst; auto.

    binvf H as J1 J2. 
    destruct H0 as [H0 | H0]; subst; auto.
    eapply valueInParams__used_in_value; eauto.
Qed.

Lemma used_in_fdef__used_in_cmd_value : forall id0 l3 ps1 cs c v tmn1 F1,
  used_in_fdef id0 F1 = false ->
  blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true ->
  valueInCmdOperands v c -> In c cs ->
  used_in_value id0 v = false.
Proof.
  destruct F1. simpl. intros.
  eapply used_in_blocks__used_in_block in H0; eauto.
  binvf H0 as J3 J4. binvf J3 as J1 J2.
  eapply used_in_cmds__used_in_cmd in J2; eauto.
  eapply used_in_cmd__used_in_value in H1; eauto.
Qed.

Lemma used_in_tmn__used_in_value : forall id0 v tmn,
  used_in_tmn id0 tmn = false ->
  valueInTmnOperands v tmn -> 
  used_in_value id0 v = false.
Proof.
  destruct tmn; simpl; intros; try solve [inv H0 | subst; auto].
Qed.

Lemma used_in_fdef__used_in_tmn_value : forall id0 l3 ps1 cs v tmn1 F1,
  used_in_fdef id0 F1 = false ->
  blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true ->
  valueInTmnOperands v tmn1 ->
  used_in_value id0 v = false.
Proof.
  destruct F1. simpl. intros.
  eapply used_in_blocks__used_in_block in H0; eauto.
  binvf H0 as J3 J4. binvf J3 as J1 J2.
  eapply used_in_tmn__used_in_value in H1; eauto.
Qed.

Lemma used_in_fdef__used_in_block : forall id0 b F1,
  used_in_fdef id0 F1 = false ->
  blockInFdefB b F1 = true ->
  used_in_block id0 b = false.
Proof.
  destruct F1. simpl. intros.
  eapply used_in_blocks__used_in_block in H0; eauto.
Qed.

(* The sb_ds_trans_lib.mem_simulation__malloc should use this lemma. *)
Lemma mem_inj__malloc : forall mi TD Mem Mem2 tsz gn align0 Mem' mb mgb,
  wf_sb_mi mgb mi Mem Mem2 ->
  MoreMem.mem_inj mi Mem Mem2 ->
  malloc TD Mem tsz gn align0 = ret (Mem', mb) ->
  exists mi', exists Mem2', exists mb',
    malloc TD Mem2 tsz gn align0 = ret (Mem2', mb') /\
    wf_sb_mi mgb mi' Mem' Mem2' /\
    MoreMem.mem_inj mi' Mem' Mem2' /\
    Values.inject_incr mi mi' /\
    mi' mb = Some (mb', 0) /\
    (forall b, b <> mb -> mi b = mi' b).
Proof.
  intros mi TD Mem Mem2 tsz gn align0 Mem' mb mgb Hwfmi Hmsim Halloc.
  unfold malloc in *.
  remember (GV2int TD Size.ThirtyTwo gn) as R.
  destruct R; try solve [inversion Halloc].
  remember (Mem.alloc Mem 0 (Size.to_Z tsz * z)) as R1.
  destruct R1 as [Mem1 mb1].
  destruct (zle 0 (Size.to_Z tsz * z)); inv Halloc.
  remember (Mem.alloc Mem2 0 (Size.to_Z tsz * z)) as R2.
  destruct R2 as [Mem2' mb2].
  exists (fun b => if zeq b mb then Some (mb2,0%Z) else mi b).
  exists Mem2'. exists mb2.
  split; auto.
  assert (inject_incr mi (fun b : Z => if zeq b mb then ret (mb2, 0) else mi b))
    as Hinject_incr.
    unfold inject_incr.
    intros b b' d H.
    destruct (zeq b mb); subst; auto.
      clear - Hwfmi H HeqR1.
      symmetry in HeqR1.
      apply Mem.alloc_result in HeqR1. subst.
      destruct Hwfmi as [_ _ Hmap1 _].
      assert (mi (Mem.nextblock Mem) = None) as J.
        apply Hmap1; auto with zarith.
      rewrite H in J. inversion J.

  split; auto.
  Case "wfmi".
    clear - Hwfmi HeqR2 HeqR1.
    destruct Hwfmi as [Hno_overlap Hnull Hmap1 Hmap2 mi_freeblocks 
      mi_mappedblocks mi_range_block mi_bounds mi_globals].
    symmetry in HeqR2, HeqR1. 
    assert (J:=HeqR2).
    apply Mem.nextblock_alloc in HeqR2.
    split.
    SCase "no_overlap".
      clear - Hno_overlap J Hmap2.
      unfold MoreMem.meminj_no_overlap in *.
      intros.      
      destruct (zeq b1 mb); subst.
        destruct (zeq b2 mb); subst.
          contradict H; auto.

          inv H0.
          apply Hmap2 in H1.
          apply Mem.alloc_result in J.
          subst. clear - H1. intro J. subst. contradict H1; zauto.
        destruct (zeq b2 mb); subst; eauto.
          inv H1.
          apply Hmap2 in H0.
          apply Mem.alloc_result in J.
          subst. clear - H0. intro J. subst. contradict H0; zauto.
    SCase "null".
      destruct (zeq Mem.nullptr mb); subst; auto.
        apply Mem.alloc_result in HeqR1.
        assert(J':=@Mem.nextblock_pos Mem).
        rewrite <- HeqR1 in J'.
        unfold Mem.nullptr in J'.
        contradict J'; zauto.
    SCase "map1".
      intros b H2.
      assert (J':=HeqR1).
      apply Mem.alloc_result in J'.
      apply Mem.nextblock_alloc in HeqR1.
      rewrite HeqR1 in H2.
      destruct (zeq b mb); subst; zeauto.
        contradict H2; zauto.
    SCase "map2".
      intros b1 b delta2 J'.
      rewrite HeqR2.
      destruct (zeq b1 mb); subst; zeauto.
        inv J'.
        apply Mem.alloc_result in J.
        subst.
        auto with zarith.
    SCase "freeblocks".
      intros b J'.
      destruct (zeq b mb); subst.
        apply Mem.valid_new_block in HeqR1.
        contradict HeqR1; auto.

        apply mi_freeblocks.
          intro J1. apply J'.
          eapply Mem.valid_block_alloc; eauto.
    SCase "mappedblocks".
      intros b b' delta J'.
      destruct (zeq b mb); subst.
        inv J'.            
        apply Mem.valid_new_block in J; auto.
        eapply Mem.valid_block_alloc; eauto.
    SCase "range_block".
      intros b b' delta J'.
      destruct (zeq b mb); inv J'; subst; eauto.
    SCase "bounds".
      intros b b' delta J'.
      erewrite Mem.bounds_alloc; eauto.
      erewrite Mem.bounds_alloc with (m2:=Mem2'); eauto.
      unfold eq_block.
      destruct (zeq b mb); subst.
        inv J'.
        destruct (zeq b' b'); subst; auto.
          contradict n; auto.      

        destruct (zeq b' mb2); subst; eauto.
          apply Hmap2 in J'.
          apply Mem.alloc_result in J.
          rewrite J in J'. contradict J'; zauto.
    SCase "globals".
      intros b J'.
      destruct (zeq b mb); subst; eauto.
        assert (J'':=J').
        apply mi_globals in J'.
        destruct (SBspecMetadata.valid_block_dec Mem mb).
          apply Mem.fresh_block_alloc in HeqR1.
          contradict HeqR1; auto.
     
          apply mi_freeblocks in n.        
          rewrite n in J'. inversion J'.
 
  split; auto.
  Case "msim".
      destruct Hmsim.
      apply MoreMem.mk_mem_inj.
      SSCase "mi_access".
        intros b1 b2 d c ofs p J1 J2.
        destruct (zeq b1 mb); subst; inv J1.
        SSSCase "b1=mb".
          symmetry in HeqR1.
          symmetry in HeqR2.
          destruct J2 as [J21 J22].
          assert (0 <= ofs /\ ofs + size_chunk c <= Size.to_Z tsz * z) as EQ.
            destruct (Z_le_dec 0 ofs).
              destruct (Z_le_dec (ofs + size_chunk c) (Size.to_Z tsz * z)); auto.
                apply Mem.perm_alloc_3 with (ofs:=ofs+size_chunk c-1) (p:=p) in 
                  HeqR1; auto with zarith.
                unfold Mem.range_perm in J21.
                assert (ofs <= ofs + size_chunk c - 1 < ofs + size_chunk c) as J.
                  assert (J':=@Memdata.size_chunk_pos c).
                  auto with zarith.
                apply J21 in J.           
                contradict J; auto. 
              apply Mem.perm_alloc_3 with (ofs:=ofs) (p:=p) in HeqR1; 
                auto with zarith.
              unfold Mem.range_perm in J21.
              assert (ofs <= ofs < ofs + size_chunk c) as J.
                assert (J':=@Memdata.size_chunk_pos c).
                auto with zarith.
              apply J21 in J.           
              contradict J; auto. 

          apply Mem.valid_access_alloc_same with (chunk:=c)(ofs:=ofs+0) in HeqR2;
            auto with zarith.
            eapply Mem.valid_access_implies; eauto using perm_F_any.

        SSSCase "b1<>mb".
          eapply Mem.valid_access_alloc_other; eauto.
          eapply Mem.valid_access_alloc_inv with (b:=mb)(lo:=0)
            (hi:=Size.to_Z tsz * z)(p:=p) in J2; eauto.
          destruct (eq_block); subst; try solve [eauto | contradict n; auto].

      SSCase "mi_memval".
Transparent Mem.alloc.
        intros b1 ofs b2 d J1 J2.
        injection HeqR1. intros NEXT MEM.
        injection HeqR2. intros NEXT2 MEM2.
        destruct Mem2. destruct Mem2'. destruct Mem. destruct Mem'. 
        inv MEM.
        inv MEM2. clear HeqR1 HeqR2.
        simpl in *.
        unfold Mem.perm in *. simpl in *.
        clear maxaddress_pos0 conversion_props0 maxaddress_pos2 
              conversion_props2.
        unfold update.     
        destruct (zeq b1 nextblock1); subst; inv J1.
        SSSCase "b1=nextblock1".
          destruct (zeq b2 b2) as [e | n]; 
            try solve [contradict n; auto].
          apply MoreMem.memval_inject_undef.

        SSSCase "b1<>mb".
          destruct (zeq b2 nextblock); subst.
            clear - H0 Hwfmi.
            destruct Hwfmi. simpl in *.
            apply Hmap2 in H0.
            contradict H0; auto with zarith.

            apply MoreMem.memval_inject_incr with (f:=mi); auto.
              apply mi_memval; auto.
                clear - J2 n.
                unfold update in J2.
                destruct (zeq b1 nextblock1); subst; 
                  try solve [auto | contradict n; auto].

Global Opaque Mem.alloc.

  split; auto.
  split.
    destruct (zeq mb mb); auto.
      contradict n; auto.
    intros.
    destruct (zeq b mb); subst; auto.
      contradict H; auto.
Qed.

Lemma mem_simulation__malloc : forall mi TD Mem1 Mem2 tsz gn Mem1' Mem2' mb1
  mb2 ECs1 pinfo maxb lc1 t id0 align0 F gn' ecs EC
  (Hprom: Promotability.wf_ECStack maxb pinfo TD Mem1 (EC::ECs1))
  (Hnrem : PI_f pinfo <> F \/ PI_id pinfo <> id0)
  (Heq1: F = Opsem.CurFunction EC) (Heq2: lc1 = Opsem.Locals EC)
  (Heq3: ecs = strip_ECs (EC::ECs1))
  (Hmsim : mem_simulation pinfo maxb mi ecs Mem1 Mem2)
  (Hsim: gv_inject mi gn gn')
  (Hmlc: malloc TD Mem1 tsz gn align0 = ret (Mem1', mb1))
  (Hmlc': malloc TD Mem2 tsz gn' align0 = ret (Mem2', mb2)),
  exists mi',
    mem_simulation pinfo maxb mi' 
      ((F, 
        updateAddAL (GVsT DGVs) lc1 id0
          ($ blk2GV TD mb1 # typ_pointer t $))::strip_ECs ECs1) 
      Mem1' Mem2' /\
    Values.inject_incr mi mi' /\
    mi' mb1 = Some (mb2, 0) /\
    (forall b, b <> mb1 -> mi b = mi' b).
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim2 Hmsim3]].
  eapply mem_inj__malloc in Hmsim1; eauto.
  destruct Hmsim1 as [mi' [Mem2'' [mb' [J1 [J2 [J3 [J4 [J5 J6]]]]]]]].
  assert (Hmlc0:=Hmlc).
  unfold malloc in Hmlc, Hmlc', J1.
  inv_mbind''. symmetry_ctx.
  apply simulation__eq__GV2int with (TD:=TD)(sz:=Size.ThirtyTwo) in Hsim; eauto.
  rewrite Hsim in HeqR. rewrite HeqR in HeqR0. inv HeqR0. 
  destruct (zle 0 (Size.to_Z tsz * z0)).
    rewrite H1 in H0. inv H0.
    exists mi'.
    split.
      split; auto.
      split; auto.
        eapply isnt_alloca_in_ECs_update_non_palloca; eauto.
        intros. 
        eapply malloc__isnt_alloca_in_ECs in Hprom; eauto.
    split; auto.

    congruence.
Qed.

Lemma als_simulation__malloc: forall pinfo F lc mi id0 mi' Mem1 Mem1' mb TD 
  t tsz0 gn align0 maxb als1 als2
  (Hprom: if fdef_dec (PI_f pinfo) F
          then Promotability.wf_defs maxb pinfo TD Mem1 lc als1
          else True)
  (Hml: malloc TD Mem1 tsz0 gn align0 = ret (Mem1', mb))
  (Hprop1 : inject_incr mi mi') 
  (Hprop2 : forall b : mblock, b <> mb -> mi b = mi' b),
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  als_simulation pinfo mi F lc als1 als2 ->
  als_simulation pinfo mi' F 
    (updateAddAL (GVsT DGVs) lc id0 ($ blk2GV TD mb # typ_pointer t $)) 
    als1 als2.
Proof.
  intros.
  apply als_simulation_update_lc; auto.
  eapply inject_incr__preserves__als_simulation; eauto.
  eapply malloc__is_alloca_in_EC; eauto.
Qed.

Lemma als_simulation__alloca: forall pinfo F als1 als2 lc mi id0 mi' mb1 mb2 TD 
  t tsz0 gn align0 maxb Mem1 Mem1'
  (Hprom: if fdef_dec (PI_f pinfo) F
          then Promotability.wf_defs maxb pinfo TD Mem1 lc als1
          else True)
  (Hml: malloc TD Mem1 tsz0 gn align0 = ret (Mem1', mb1))
  (Hprop1 : inject_incr mi mi') (Hprop3 : mi' mb1 = ret (mb2, 0))
  (Hprop2 : forall b : mblock, b <> mb1 -> mi b = mi' b),
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  als_simulation pinfo mi F lc als1 als2 ->
  als_simulation pinfo mi' F 
    (updateAddAL (GVsT DGVs) lc id0 ($ blk2GV TD mb1 # typ_pointer t $)) 
    (mb1::als1) (mb2::als2).
Proof.
  intros.
  apply als_simulation_update_lc; auto.
  apply inject_incr__preserves__als_simulation with (mi':=mi') in H0; auto.
    simpl.
    assert (Hml':=Hml).
    apply MemProps.malloc_result in Hml'. subst.
    erewrite Promotability_wf_EC__isnt_alloca_in_EC; eauto.

    eapply malloc__is_alloca_in_EC; eauto.
Qed.

Lemma reg_simulation__malloc: forall pinfo F lc1 lc2 mi id0 mi' mb1 mb2 TD 
  t (Hprop1 : mi' mb1 = ret (mb2, 0)) (Hprop3 : inject_incr mi mi'),
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  reg_simulation pinfo mi F lc1 lc2 ->
  reg_simulation pinfo mi' F
    (updateAddAL (GVsT DGVs) lc1 id0 ($ blk2GV TD mb1 # typ_pointer t $))
    (updateAddAL (GVsT DGVs) lc2 id0 ($ blk2GV TD mb2 # typ_pointer t $)).
Proof.
  intros.
  apply reg_simulation_update_non_palloca; auto.
    eapply inject_incr__preserves__reg_simulation; eauto.
    
    repeat rewrite Promotability.simpl_blk2GV.
    constructor; auto.
      assert (Int.repr 31 0 = Int.add 31 (Int.repr 31 0) (Int.repr 31 0)) 
        as EQ.
        rewrite Int.add_zero. auto.
      rewrite EQ at 2.
      econstructor; eauto.
Qed.

Lemma simulation__mload : forall mi TD pinfo maxb Mem1 Mem2 gvp1 align0 gv1 gv2 t
  gvp2 st,  
  wf_sb_mi maxb mi Mem1 Mem2 ->
  mem_simulation pinfo maxb mi st Mem1 Mem2 ->
  mload TD Mem1 gvp1 t align0 = ret gv1 ->
  mload TD Mem2 gvp2 t align0 = ret gv2 ->
  gv_inject mi gvp1 gvp2 ->
  gv_inject mi gv1 gv2.
Proof.
  intros mi TD pinfo max Mem1 Mem2 gvp1 align0 gv1 gv2 t gvp2 st Hwfmi Hmsim 
  Hmload1 Hmload2 Hginject. 
  apply mload_inv in Hmload1.
  destruct Hmload1 as [b1 [ofs1 [m1 [mc1 [Heq1 [Hflat1 Hmload1]]]]]]; subst.
  apply mload_inv in Hmload2.
  destruct Hmload2 as [b2 [ofs2 [m2 [mc2 [Heq2 [Hflat2 Hmload2]]]]]]; subst.
  uniq_result.
  inv Hginject. inv H1. 
  destruct Hmsim as [Hmsim _].
  eapply simulation_mload_aux in Hmload1; eauto.
  destruct Hmload1 as [gv2' [Hmload1 Hinj]].
  inv Hwfmi.
  apply mi_range_block in H3. subst.
  rewrite Int.add_zero in Hmload2.
  assert (Int.signed 31 ofs1 + 0 = Int.signed 31 ofs1) as EQ. zauto.
  rewrite EQ in Hmload1. 
  uniq_result. auto.
Qed.

(* sb_ds_trans_lib.simulation_mstore_aux should use this *)
Lemma mem_inj_mstore_aux : forall b b2 delta mi mgb 
  (H1 : mi b = ret (b2, delta)) gv ofs gv2 Mem0 Mem2 Mem0'
  (Hwfmi : wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : MoreMem.mem_inj mi Mem0 Mem2)
  (Hinj : gv_inject mi gv gv2)
  (Hmstores : mstore_aux Mem0 gv b ofs = ret Mem0'),
   exists Mem2',
     mstore_aux Mem2 gv2 b2 (ofs + delta) = ret Mem2' /\ 
     wf_sb_mi mgb mi Mem0' Mem2' /\ 
     MoreMem.mem_inj mi Mem0' Mem2'.
Proof.
  induction gv; simpl; intros.
    inv Hmstores. inv Hinj. simpl. eauto.

    destruct a. inv Hinj.
    remember (Mem.store m Mem0 b ofs v) as R1.
    destruct R1 as [M|]; tinv Hmstores.
    symmetry in HeqR1.
    inv Hwfmi.
    assert (Hmstore0 := HeqR1).
    eapply MoreMem.store_mapped_inj with (f:=mi)(m2:=Mem2) in HeqR1; 
      try solve [eauto | inversion Hwfmi; eauto].
    destruct HeqR1 as [Mem2' [Hmstore Hminj]].
    simpl. rewrite Hmstore.
    assert (ofs + delta + size_chunk m = ofs + size_chunk m + delta) as EQ. ring.
    rewrite EQ.
    apply IHgv with (Mem0:=M); auto.
    Case "wf_sb_mi".
      split; auto.
      SCase "Hnext1".
        erewrite <- Mem.nextblock_store with (m1:=Mem0) in Hmap1; eauto.
      SCase "Hnext2".
        intros b1 b0 delta2 J.
        apply Hmap2 in J.
        apply Mem.nextblock_store in Hmstore.
        rewrite Hmstore. auto.
      SCase "mi_freeblocks0".
        intros b0 J. apply mi_freeblocks. intro J'. apply J.
        eapply Mem.store_valid_block_1; eauto.
      SCase "mi_mappedblocks0".
        intros b0 b' delta0 J.
        eapply Mem.store_valid_block_1; eauto.
      SCase "mi_bounds".
        intros b0 b' delta0 J.
        apply mi_bounds in J.
        apply Mem.bounds_store with (b':=b0) in Hmstore0; auto.
        rewrite Hmstore0. rewrite J.
        erewrite Mem.bounds_store with (m2:=Mem2'); eauto.
Qed.

Lemma simulation__mstore : forall mi TD pinfo Mem1 Mem2 gvp1 gv1 gvp2 
  gv2 Mem1' Mem2' maxb F t align0 lc ECs,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  mem_simulation pinfo maxb mi ((F,lc) :: strip_ECs ECs) Mem1 Mem2 ->
  mstore TD Mem1 gvp1 t gv1 align0 = ret Mem1' ->
  mstore TD Mem2 gvp2 t gv2 align0 = ret Mem2' ->
  gv_inject mi gvp1 gvp2 ->
  gv_inject mi gv1 gv2 ->
  mem_simulation pinfo maxb mi ((F, lc) :: strip_ECs ECs) Mem1' Mem2'.
Proof.
  intros mi TD pinfo Mem1 Mem2 gvp1 gv1 gvp2 gv2 Mem1' Mem2' maxb F t align0 lc 
    ECs Hwfmi Hmsim Hmstore1 Hmstore2 Hginject1 Hginject2.
  apply mstore_inversion in Hmstore1.
  destruct Hmstore1 as [b1 [ofs1 [cm1 [Heq1 Hmstore1]]]]; subst.
  apply mstore_inversion in Hmstore2.
  destruct Hmstore2 as [b2 [ofs2 [cm2 [Heq2 Hmstore2]]]]; subst.
  inv Hginject1. inv H1.

  destruct Hmsim as [Hmsim1 [Hmsim2 Hmsim3]].
  eapply mem_inj_mstore_aux in Hmstore1; eauto.
  destruct Hmstore1 as [Mem2'' [Hmstore1 [Hwfmi' Hmsim']]].
  inv Hwfmi.
  apply mi_range_block in H3. subst.
  rewrite Int.add_zero in Hmstore2.
  assert (Int.signed 31 ofs1 + 0 = Int.signed 31 ofs1) as EQ. zauto.
  rewrite EQ in Hmstore1. uniq_result.
  split; auto.
Qed.

Lemma lookupFdefViaPtr__simulation : forall pinfo Ps1 Ps2 fptr1 fptr2 f1 f2 fs1
  fs2 mi,
  ftable_simulation mi fs1 fs2 ->
  OpsemAux.lookupFdefViaPtr Ps2 fs2 fptr2 = Some f2 ->
  products_simulation pinfo Ps1 Ps2 ->
  gv_inject mi fptr1 fptr2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs1 fptr1 = Some f1 ->
  fdef_simulation pinfo f1 f2.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs1 fptr1) as R1.
  destruct R1 as [fid1|]; inv H3. 
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs2 fptr2) as R2.
  destruct R2 as [fid2|]; inv H0. 
  eapply products_simulation__fdef_simulation; eauto.
  unfold ftable_simulation in H.
  erewrite H in HeqR1; eauto.
  rewrite <- HeqR2 in HeqR1. inv HeqR1. auto.
Qed.

Definition params_dont_use_pid pinfo F (ps:params) := 
  PI_f pinfo <> F \/
  List.fold_left 
    (fun acc p => let '(_, v):=p in used_in_value (PI_id pinfo) v || acc) 
    ps false = false.

Lemma reg_simulation__params2GVs: forall pinfo mi F lc1 lc2 gl  
  TD (Hrsim: reg_simulation pinfo mi F lc1 lc2) maxb Mem1 Mem2
  (Hwfg: wf_globals maxb gl) (Hwfmi: wf_sb_mi maxb mi Mem1 Mem2)
  lp (Hnuse: params_dont_use_pid pinfo F lp) gvs1 gvs2,
  Opsem.params2GVs TD lp lc1 gl = ret gvs1 ->
  Opsem.params2GVs TD lp lc2 gl = ret gvs2 ->
  List.Forall2 (fun gv1 => fun gv2 => gv_inject mi gv1 gv2)
    gvs1 gvs2.
Proof.
  induction lp as [|[]]; simpl; intros.
    uniq_result. constructor.

    inv_mbind'. symmetry_ctx.
    assert (params_dont_use_pid pinfo F lp /\ value_doesnt_use_pid pinfo F v) 
      as J.
      unfold params_dont_use_pid in Hnuse. unfold params_dont_use_pid.
      unfold value_doesnt_use_pid.
      destruct (fdef_dec (PI_f pinfo) F); subst; auto.
      destruct Hnuse as [Hnuse | Hnuse]; try congruence.
      simpl in Hnuse. assert (J:=Hnuse).
      apply fold_left_eq in Hnuse.
        rewrite Hnuse in J.
        binvf Hnuse as J1 J2. 
        split; right; auto.
    
        intros. destruct b.
        binvf H as J1 J2. auto.
    destruct J as [J1 J2].
    constructor; auto.
      eapply simulation__getOperandValue; eauto.
Qed.

Definition args_dont_use_pid pinfo F (la:list (typ * attributes * id)) := 
  PI_f pinfo <> F \/ (forall t a i0, In (t,a,i0) la -> PI_id pinfo <> i0).

Lemma reg_simulation__initializeFrameValues: forall pinfo mi fa0 rt0 fid0 va0
    TD lb la2 la1 (gvs1 gvs2:list (GVsT DGVs)) lc1 lc2 lc1' lc2'
  (Hnuse: args_dont_use_pid pinfo 
            (fdef_intro (fheader_intro fa0 rt0 fid0 (la1++la2) va0) lb) la2),
  List.Forall2 (fun gv1 => fun gv2 => gv_inject mi gv1 gv2) gvs1 gvs2 ->
  reg_simulation pinfo mi 
    (fdef_intro (fheader_intro fa0 rt0 fid0 (la1++la2) va0) lb) lc1 lc2 ->
  Opsem._initializeFrameValues TD la2 gvs1 lc1 = ret lc1' ->
  Opsem._initializeFrameValues TD la2 gvs2 lc2 = ret lc2' ->
  reg_simulation pinfo mi 
    (fdef_intro (fheader_intro fa0 rt0 fid0 (la1++la2) va0) lb) lc1' lc2'.
Proof.
  induction la2 as [|[[]]]; simpl; intros.
    uniq_result. auto.

    assert (args_dont_use_pid pinfo
       (fdef_intro
          (fheader_intro fa0 rt0 fid0 ((la1 ++ [(t, a, i0)]) ++ la2) va0) lb)
       la2) as J.
      unfold args_dont_use_pid. unfold args_dont_use_pid in Hnuse.
      simpl_env. simpl_env in Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
      right.
      intros.
      eapply Hnuse; simpl; eauto.

    assert (PI_f pinfo <>
      fdef_intro (fheader_intro fa0 rt0 fid0 (la1 ++ (t, a, i0) :: la2) va0) lb\/
      PI_id pinfo <> i0) as J'.
      unfold args_dont_use_pid in Hnuse.
      destruct Hnuse as [Hnuse | Hnuse]; auto.
      right. 
      eapply Hnuse; simpl; eauto.

    rewrite_env ((la1 ++ [(t, a, i0)]) ++ la2) in H0.
    inv H; inv_mbind''; symmetry_ctx.
      eapply IHla2 in H0; eauto.
        apply reg_simulation_update_non_palloca; auto.
        simpl_env in *. auto.
        eapply gv_inject_gundef; eauto.

      eapply IHla2 in H0; eauto.
        apply reg_simulation_update_non_palloca; auto.
        simpl_env in *. auto.
        eapply simulation__lift_opt1; eauto.
Qed.

Lemma reg_simulation_nil: forall pinfo mi F, reg_simulation pinfo mi F nil nil.
Proof.
  unfold reg_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
    intros.
    destruct (id_dec (PI_id pinfo) i0); subst; auto.
    intros. inv H.

    intros. intros. inv H.
Qed.

Lemma reg_simulation__initLocals: forall pinfo mi F lc1 lc2 lp gl gvs1 gvs2 lc1'
  lc2' la TD fa0 rt0 fid0 va0 lb Mem1 Mem2 maxb
  (Hwfg: wf_globals maxb gl) (Hwfmi: wf_sb_mi maxb mi Mem1 Mem2)
  (Hnuse: params_dont_use_pid pinfo F lp)
  (Hnuse': args_dont_use_pid pinfo 
            (fdef_intro (fheader_intro fa0 rt0 fid0 la va0) lb) la),
  reg_simulation pinfo mi F lc1 lc2 ->
  Opsem.params2GVs TD lp lc1 gl = ret gvs1 ->
  Opsem.params2GVs TD lp lc2 gl = ret gvs2 ->
  Opsem.initLocals TD la gvs1 = ret lc1' ->
  Opsem.initLocals TD la gvs2 = ret lc2' ->
  reg_simulation pinfo mi 
    (fdef_intro (fheader_intro fa0 rt0 fid0 la va0) lb) lc1' lc2'.
Proof.
  intros.
  eapply reg_simulation__params2GVs in H; eauto.
  unfold Opsem.initLocals in *.
  rewrite_env (nil++la).
  eapply reg_simulation__initializeFrameValues; eauto.
  apply reg_simulation_nil; auto.  
Qed.

Lemma products_simulation__fdec_simulation : forall pinfo fid Ps1 Ps2 
  (Hsim: products_simulation pinfo Ps1 Ps2) f1 f2,
  lookupFdecViaIDFromProducts Ps2 fid = Some f2 ->
  lookupFdecViaIDFromProducts Ps1 fid = Some f1 ->
  f1 = f2.
Proof.
  intros pinfo fid Ps1 Ps2 Hsim.
  induction Hsim; simpl; intros.
    inv H.

    destruct x; destruct y; inv H0; inv H1; eauto; try congruence.
    destruct (getFdecID f0 == fid); subst.
      inv H3.
      destruct (getFdecID f == getFdecID f2).
        inv H2. inv H. auto.

        destruct f2 as [[]], f1 as [[]].
        apply lookupFdecViaIDFromProducts_ideq in H2.
        simpl in H2. subst.
        destruct f.
        inv H.
        contradict n; auto.
    destruct (getFdecID f == fid); subst; auto.
      inv H2.
      destruct f2 as [[]], f1 as [[]].
      apply lookupFdecViaIDFromProducts_ideq in H3.
      simpl in H3. subst.
      destruct f0.
      inv H.
      contradict n; auto.
Qed.

Lemma products_simulation__fdef_simulation_l2r : forall pinfo fid Ps1 Ps2
  (Hsim: products_simulation pinfo Ps1 Ps2) f1,
  lookupFdefViaIDFromProducts Ps1 fid = Some f1 ->
  exists f2, 
    lookupFdefViaIDFromProducts Ps2 fid = Some f2 /\ 
    fdef_simulation pinfo f1 f2.
Proof.
  intros pinfo fid Ps1 Ps2 Hsim.
  induction Hsim; simpl; intros.
    inv H.

    destruct x; destruct y; inv H0; eauto; try congruence.
    destruct (getFdefID f == fid); subst.
      inv H2. simpl.
      destruct (getFdefID f0 == getFdefID f1); eauto.
        apply IHHsim. simpl.
        destruct f0 as [[]], f1 as [[]].
        apply fdef_simulation_inv in H.
        destruct H as [H _]. inv H.
        contradict n; auto.
    simpl.
    destruct (getFdefID f0 == fid); subst; auto.
      destruct f0 as [[]], f as [[]].
      apply fdef_simulation_inv in H.
      destruct H as [H _]. inv H.
      contradict n; auto.
Qed.

Lemma products_simulation__fdef_simulation_r2l : forall pinfo fid Ps1 Ps2 
  (Hsim: products_simulation pinfo Ps1 Ps2) f2,
  lookupFdefViaIDFromProducts Ps2 fid = Some f2 ->
  exists f1, 
    lookupFdefViaIDFromProducts Ps1 fid = Some f1 /\ 
    fdef_simulation pinfo f1 f2.
Proof.
  intros pinfo fid Ps1 Ps2 Hsim.
  induction Hsim; simpl; intros.
    inv H.

    destruct x; destruct y; inv H0; eauto; try congruence.
    destruct (getFdefID f0 == fid); subst.
      inv H2. simpl.
      destruct (getFdefID f == getFdefID f2); eauto.
        apply IHHsim. simpl.
        destruct f as [[]], f2 as [[]].
        apply fdef_simulation_inv in H.
        destruct H as [H _]. inv H.
        contradict n; auto.
    simpl.
    destruct (getFdefID f == fid); subst; auto.
      destruct f as [[]], f0 as [[]].
      apply fdef_simulation_inv in H.
      destruct H as [H _]. inv H.
      contradict n; auto.
Qed.

Lemma lookupFdefViaPtr__simulation_l2r : forall pinfo Ps1 Ps2 fptr1 fptr2 f1 
  fs1 fs2 mi f2,
  products_simulation pinfo Ps1 Ps2 ->
  ftable_simulation mi fs1 fs2 ->
  gv_inject mi fptr1 fptr2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs1 fptr1 = Some f1 ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs2 fptr2 = Some f2 ->
  False.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs1 fptr1) as R1.
  destruct R1 as [fid1|]; inv H2. 
  unfold OpsemAux.lookupExFdecViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs2 fptr2) as R2.
  destruct R2 as [fid2|]; inv H3. 
  remember (lookupFdefViaIDFromProducts Ps2 fid2) as R3.
  destruct R3; inv H4. 
  eapply products_simulation__fdef_simulation_l2r in H5; eauto.
  destruct H5 as [f2' [J1 J2]].
  unfold ftable_simulation in H0.
  erewrite H0 in HeqR1; eauto.
  rewrite <- HeqR1 in HeqR2. inv HeqR2.
  rewrite J1 in HeqR3. inv HeqR3.
Qed.

Lemma lookupExFdecViaPtr__simulation : forall pinfo Ps1 Ps2 fptr1 fptr2 f1
  f2 fs1 fs2 mi,
  products_simulation pinfo Ps1 Ps2 ->
  ftable_simulation mi fs1 fs2 ->
  gv_inject mi fptr1 fptr2 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs1 fptr1 = Some f1 ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs2 fptr2 = Some f2 ->
  f1 = f2.
Proof.
  intros.
  unfold OpsemAux.lookupExFdecViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs1 fptr1) as R1.
  destruct R1 as [fid1|]; inv H2. 
  remember (lookupFdefViaIDFromProducts Ps1 fid1) as R3.  
  destruct R3; tinv H5.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs2 fptr2) as R2.
  destruct R2 as [fid2|]; inv H3. 
  remember (lookupFdefViaIDFromProducts Ps2 fid2) as R4.  
  destruct R4; tinv H4. symmetry_ctx.
  unfold ftable_simulation in H0.
  erewrite H0 in HeqR1; eauto.
  rewrite HeqR2 in HeqR1. inv HeqR1. 
  eapply products_simulation__fdec_simulation; eauto.
Qed.

Lemma lookupFdefViaPtr__simulation_r2l : forall pinfo Ps1 Ps2 fptr1 fptr2 f1 
  fs1 fs2 mi f2,
  products_simulation pinfo Ps1 Ps2 ->
  ftable_simulation mi fs1 fs2 ->
  gv_inject mi fptr1 fptr2 ->
  OpsemAux.lookupFdefViaPtr Ps2 fs2 fptr2 = Some f2 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs1 fptr1 = Some f1 ->
  False.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs2 fptr2) as R1.
  destruct R1 as [fid2|]; inv H2. 
  unfold OpsemAux.lookupExFdecViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs1 fptr1) as R2.
  destruct R2 as [fid1|]; inv H3. 
  remember (lookupFdefViaIDFromProducts Ps1 fid1) as R3.
  destruct R3; inv H4. 
  eapply products_simulation__fdef_simulation_r2l in H5; eauto.
  destruct H5 as [f2' [J1 J2]].
  unfold ftable_simulation in H0.
  erewrite H0 in HeqR2; eauto.
  rewrite <- HeqR2 in HeqR1. inv HeqR1.
  rewrite J1 in HeqR3. inv HeqR3.
Qed.

Axiom callExternalFunction__mem_simulation: forall pinfo mi M1 M2 fid0 gvs1 
  gvs2 oresult1 M1' oresult2 M2' mgb gl lc1 lc2 TD F rid noret0 ft lp
  EC lc1' lc2' als1 als2,
  mem_simulation pinfo mgb mi ((F,lc1) :: strip_ECs EC) M1 M2 ->
  reg_simulation pinfo mi F lc1 lc2 ->
  Opsem.params2GVs TD lp lc1 gl = ret gvs1 ->
  Opsem.params2GVs TD lp lc2 gl = ret gvs2 ->
  OpsemAux.callExternalFunction M1 fid0 gvs1 = ret (oresult1, M1') ->
  OpsemAux.callExternalFunction M2 fid0 gvs2 = ret (oresult2, M2') ->
  Opsem.exCallUpdateLocals TD ft noret0 rid oresult1 lc1 = ret lc1' ->
  Opsem.exCallUpdateLocals TD ft noret0 rid oresult2 lc2 = ret lc2' ->
  als_simulation pinfo mi F lc1 als1 als2 ->
  oresult1 = oresult2 /\ 
  exists mi', 
    mem_simulation pinfo mgb mi' 
      ((F,lc1') :: strip_ECs EC) M1' M2' /\ Values.inject_incr mi mi' /\
    als_simulation pinfo mi' F lc1' als1 als2 /\
    reg_simulation pinfo mi' F lc1' lc2' /\
    (forall blk : mblock,
       ~ isnt_alloca_in_ECs pinfo (strip_ECs EC) blk -> 
       mi blk = merror -> mi' blk = merror).

Lemma used_in_fdef__tmn_value_doesnt_use_pid: forall (l3 : l) 
  (ps1 : phinodes) (cs : cmds) (v : value) (tmn1 : terminator) (F: fdef) pinfo,
  used_in_fdef (PI_id pinfo) (PI_f pinfo) = false ->
  blockInFdefB (block_intro l3 ps1 cs tmn1) F = true ->
  valueInTmnOperands v tmn1 -> 
  value_doesnt_use_pid pinfo F v.
Proof.
  intros.
  unfold value_doesnt_use_pid.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
    right. eapply used_in_fdef__used_in_tmn_value; eauto; simpl; auto.
Qed.

Lemma used_in_fdef__cmd_value_doesnt_use_pid: forall (l3 : l) c
  (ps1 : phinodes) (cs : cmds) (v : value) (tmn1 : terminator) (F: fdef) pinfo,
  used_in_fdef (PI_id pinfo) (PI_f pinfo) = false ->
  blockInFdefB (block_intro l3 ps1 cs tmn1) F = true ->
  In c cs ->
  valueInCmdOperands v c -> 
  value_doesnt_use_pid pinfo F v.
Proof.
  intros.
  unfold value_doesnt_use_pid.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
    right. eapply used_in_fdef__used_in_cmd_value; eauto; simpl; auto.
Qed.

Lemma used_in_fdef__list_value_doesnt_use_pid: forall (l3 : l)
  (ps1 : phinodes) (cs : cmds) (v : value) (tmn1 : terminator) (F: fdef) pinfo
  cs11 id0 inbounds0 t v idxs cs,
  used_in_fdef (PI_id pinfo) (PI_f pinfo) = false ->
  blockInFdefB 
    (block_intro l3 ps1 (cs11 ++ insn_gep id0 inbounds0 t v idxs :: cs) tmn1) F 
      = true ->
  list_value_doesnt_use_pid pinfo F idxs.
Proof.
  intros.
  unfold list_value_doesnt_use_pid.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
    right. 
    destruct (PI_f pinfo). simpl in *.
    eapply used_in_blocks__used_in_block in H0; eauto.
    binvf H0 as J3 J4. binvf J3 as J1 J2.
    eapply used_in_cmds__used_in_cmd in J2; eauto using in_middle.
    simpl in J2.
    binvf J2 as J3 J5. auto.
Qed.

Ltac reg_simulation_update_non_palloca_tac :=
  match goal with
  | H : Opsem.BOP _ _ _ _ _ _ _ = Some _ |- _ => eapply simulation__BOP
  | H : Opsem.FBOP _ _ _ _ _ _ _ = Some _ |- _ => eapply simulation__FBOP
  | H : Opsem.EXT _ _ _ _ _ _ _ = Some _ |- _ => eapply simulation__EXT
  | H : Opsem.TRUNC _ _ _ _ _ _ _ = Some _ |- _ => eapply simulation__TRUNC
  | H : Opsem.ICMP _ _ _ _ _ _ _ = Some _ |- _ => eapply simulation__ICMP
  | H : Opsem.FCMP _ _ _ _ _ _ _ = Some _ |- _ => eapply simulation__FCMP
  | H : Opsem.CAST _ _ _ _ _ _ _ = Some _ |- _ => eapply simulation__CAST
  | H : Opsem.extractGenericValue _ _ _ _ = Some _ |- _ =>
      eapply simulation__ExtractValue
  | H : Opsem.insertGenericValue _ _ ?gvs1 _ _ ?gvs2 = ret ?gv3,
    H' : Opsem.insertGenericValue _ _ ?gvs1' _ _ ?gvs2' = ret ?gv3' |- 
    gv_inject _ ?gv3 ?gv3' =>
      eapply simulation__InsertValue with (gv1:=gvs1) (gv2:=gvs2)
        (gv1':=gvs1') (gv2':=gvs2')
  | H : Opsem.GEP _ _ _ _ _ = Some _ |- _ => eapply simulation__GEP
  end;
  eauto using mem_simulation__wf_sb_sim;
  try solve [
    eapply used_in_fdef__cmd_value_doesnt_use_pid; eauto using in_middle;
      simpl; auto |
    eapply used_in_fdef__list_value_doesnt_use_pid; eauto using in_middle;
      simpl; auto
    ].

Ltac dse_is_sim_common_case :=
match goal with
| Hcssim2: cmds_simulation _ ?F _ _,
  HBinF1: blockInFdefB ?B ?F = true,
  Heq3: exists _, exists _, exists _, ?B = _,
  Hop2: Opsem.sInsn _ _ _ _,
  Hmsim: mem_simulation _ _ ?mi _ _ _ |- _ =>
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  exists mi;
  repeat_solve; try solve [
    apply als_simulation_update_lc; auto |
    apply reg_simulation_update_non_palloca; auto;
     reg_simulation_update_non_palloca_tac |
    eapply mem_simulation__update_non_palloca; eauto; simpl; eauto
  ]
end.

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
  Hsim : State_simulation _ _ _ _ _ ?Cfg2 ?St2 ,
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
      [Hfsim2 [Heq1 [Halsim2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  assert (Heq3':=Heq3); destruct Heq3' as [l3 [ps1 [cs11 Heq3']]]; subst;
  destruct Hnoalias as [HwfECs [[Hdisjals _] HwfM]]; simpl in Hdisjals;
  assert (HwfECs0:=HwfECs);
  destruct HwfECs0 as [[Hinscope' _] [HwfECs' HwfHT]];
  fold Promotability.wf_ECStack in HwfECs'
end.

Ltac simulation__getOperandValue_tac1 :=
    eauto using mem_simulation__wf_sb_sim;
    try solve [eapply used_in_fdef__cmd_value_doesnt_use_pid; 
               eauto using in_middle; simpl; auto].

Ltac simulation__getOperandValue_tac2 := try solve [
      eapply simulation__getOperandValue; simulation__getOperandValue_tac1
    ].

Lemma used_in_fdef__params_dont_use_pid: forall (l3 : l)
  (ps1 : phinodes) (cs : cmds) (v : value) (tmn1 : terminator) (F: fdef) pinfo
  cs11 rid noret0 ca ft fv lp cs,
  used_in_fdef (PI_id pinfo) (PI_f pinfo) = false ->
  blockInFdefB 
    (block_intro l3 ps1 (cs11 ++ insn_call rid noret0 ca ft fv lp :: cs) tmn1) F 
      = true ->
  params_dont_use_pid pinfo F lp.
Proof.
  intros.
  unfold params_dont_use_pid.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
    right. 
    destruct (PI_f pinfo). simpl in *.
    eapply used_in_blocks__used_in_block in H0; eauto.
    binvf H0 as J3 J4. binvf J3 as J1 J2.
    eapply used_in_cmds__used_in_cmd in J2; eauto using in_middle.
    simpl in J2.
    binvf J2 as J3 J5. auto.
Qed.

Lemma WF_PhiInfo__args_dont_use_pid: forall pinfo fa0 rt0 fid0 va0 lb la0,
  WF_PhiInfo pinfo ->
  args_dont_use_pid pinfo (fdef_intro (fheader_intro fa0 rt0 fid0 la0 va0) lb)
    la0.
Admitted. (* uniqness *)

Lemma dom_initializeFrameValues: forall
  (TD : TargetData) (la : args) (gvs : list (GVsT DGVs))
  (lc : Opsem.GVsMap) acc,
  Opsem._initializeFrameValues TD la gvs acc = ret lc ->
  (forall i0, i0 `in` dom lc -> i0 `in` dom acc \/ In i0 (getArgsIDs la)).
Proof.
  induction la as [|[[]]]; simpl; intros.
    inv H. auto.

    destruct gvs.
      inv_mbind'.
      rewrite updateAddAL_dom_eq in H0.
      assert (i1 `in` (dom g) \/ i1 = i0) as J.
        fsetdec.
      destruct J as [J | J]; subst; auto.
        symmetry in HeqR.
        apply IHla with (i0:=i1) in HeqR; auto.
        destruct HeqR as [HeqR | HeqR]; auto.

      inv_mbind'. 
      rewrite updateAddAL_dom_eq in H0.
      assert (i1 `in` (dom g0) \/ i1 = i0) as J.
        fsetdec.
      destruct J as [J | J]; subst; auto.
        symmetry in HeqR.
        apply IHla with (i0:=i1) in HeqR; auto.
        destruct HeqR as [HeqR | HeqR]; auto.
Qed.

Lemma NotIn_getArgsIDs__NotIn_initializeFrameValues: forall
  (TD : TargetData) (la : args) (gvs : list (GVsT DGVs)) (id1 : atom) 
  (lc : Opsem.GVsMap) acc,
  Opsem._initializeFrameValues TD la gvs acc = ret lc ->
  ~ In id1 (getArgsIDs la) /\ id1 `notin` dom acc ->
  lookupAL _ lc id1 = None.
Proof.
  induction la as [|[]]; simpl; intros.
    inv H.
    destruct H0.
    apply notin_lookupAL_None; auto.

    destruct H0 as [H1 H2].
    assert (i0 <> id1 /\ ~ In id1 (getArgsIDs la)) as J.
      split; intro; subst; contradict H1; auto.
    destruct J as [J1 J2].
    destruct p.
    destruct gvs.
      inv_mbind'.    
      rewrite <- lookupAL_updateAddAL_neq; auto.
      apply notin_lookupAL_None; auto.
      intro J. symmetry in HeqR.
      apply dom_initializeFrameValues with (i0:=id1) in HeqR; auto.
      destruct HeqR; auto.

      inv_mbind'. 
      rewrite <- lookupAL_updateAddAL_neq; auto.
      eapply IHla; eauto.
Qed.

Lemma NotIn_getArgsIDs__NotIn_initLocals : forall TD la gvs id1 lc,
  @Opsem.initLocals DGVs TD la gvs = Some lc ->
  ~ In id1 (getArgsIDs la) ->
  lookupAL _ lc id1 = None.
Proof.
  unfold Opsem.initLocals.
  intros.
  eapply NotIn_getArgsIDs__NotIn_initializeFrameValues in H; eauto.
Qed.

Lemma WF_PhiInfo__isnt_alloca_in_EC: forall pinfo fa rt fid va lb la blk lc gvs
  TD,
  WF_PhiInfo pinfo ->
  Opsem.initLocals TD la gvs = ret lc ->
  is_alloca_in_EC pinfo (fdef_intro (fheader_intro fa rt fid la va) lb) lc blk 
    = false.
Proof.
  intros.
  eapply WF_PhiInfo__args_dont_use_pid with (fa0:=fa)(rt0:=rt)(fid0:=fid)
    (va0:=va)(lb:=lb)(la0:=la) in H; eauto.
  unfold is_alloca_in_EC.
  unfold args_dont_use_pid in H.
  destruct (fdef_dec (PI_f pinfo) 
             (fdef_intro (fheader_intro fa rt fid la va) lb)); try congruence.
  rewrite e in H.
  destruct H as [H | H]; try congruence.
  erewrite NotIn_getArgsIDs__NotIn_initLocals; eauto.
  clear - H.
  induction la as [|[]]; simpl; auto.
    intro J.
    destruct J as [J | J]; subst.
      destruct p.
      assert (In (t, a, PI_id pinfo) ((t, a, PI_id pinfo) :: la)) as J.
        simpl. auto.
      apply H in J. auto.

      apply IHla in J; auto.
      intros. eapply H; simpl; eauto.
Qed.

Lemma used_in_fdef__phis_dont_use_pid: forall (l3 : l)
  (ps1 : phinodes) (cs : cmds) (tmn1 : terminator) (F: fdef) pinfo cs1,
  used_in_fdef (PI_id pinfo) (PI_f pinfo) = false ->
  blockInFdefB (block_intro l3 ps1 cs1 tmn1) F = true ->
  PI_f pinfo <> F \/
  fold_left
         (fun (re : bool) (p : phinode) => re || used_in_phi (PI_id pinfo) p)
         ps1 false = false.
Proof.
  intros.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
    right. 
    destruct (PI_f pinfo). simpl in *.
    eapply used_in_blocks__used_in_block in H0; eauto.
    binvf H0 as J3 J4. binvf J3 as J1 J2. auto.
Qed.

Lemma dae_is_sim : forall maxb pinfo mi Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfgl: sb_ds_gv_inject.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hinbd: 0 <= maxb) (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hsim: State_simulation pinfo maxb mi Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State pinfo St1) St1' tr1 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     exists mi',
       State_simulation pinfo maxb mi' Cfg1 St1' Cfg2 St2 /\ tr1 = trace_nil /\
       Values.inject_incr mi mi') /\
  (forall (Hnrem: ~removable_State pinfo St1) St1' St2' tr1 tr2
     (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2) 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     exists mi',
       State_simulation pinfo maxb mi' Cfg1 St1' Cfg2 St2' /\ tr1 = tr2 /\
       Values.inject_incr mi mi').
Proof.

Local Opaque inscope_of_tmn inscope_of_cmd.

  intros.
  split; intros.
Case "removable state". eapply dae_is_sim_removable_state; eauto.

Case "unremovable state".
  apply not_removable_State_inv in Hnrem. 
  (sInsn_cases (destruct Hop1) SCase).

SCase "sReturn".
Focus.

  destruct_ctx_return.
  assert (PI_f pinfo <> F' \/ PI_id pinfo <> getCmdLoc (insn_call i0 n c t v p))
    as Hneq.
    admit. (* wf-formedness *)
  apply cmds_simulation_nelim_cons_inv in Hcssim2'; auto.
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result.
  eapply free_allocas_return_sim in Hmsim; eauto.
  exists mi.
  repeat_solve.
    eapply returnUpdateLocals_als_simulation; eauto.

    clear - H27 H1 Hlcsim2 Hlcsim2' Hwfgl Hmsim Hneq HBinF1 Hnuse.
    eapply returnUpdateLocals_reg_simulation with (lc:=lc); 
      eauto using mem_simulation__wf_sb_sim.
      eapply used_in_fdef__tmn_value_doesnt_use_pid; eauto; simpl; auto.

Unfocus.
      
SCase "sReturnVoid".
Focus.
  destruct_ctx_return.
  assert (PI_f pinfo <> F' \/ PI_id pinfo <> getCmdLoc (insn_call i0 n c t v p))
    as Hneq.
    admit. (* wf-formedness *)
  apply cmds_simulation_nelim_cons_inv in Hcssim2'; auto.
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result.
  eapply free_allocas_return_void_sim in Hmsim; eauto.
  exists mi.
  repeat_solve.

Unfocus.

SCase "sBranch".
Focus.
  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    destruct Hmsim as [_ [_ Hwf_mi]].
    eapply simulation__getOperandValue in Hlcsim2; eauto.
      erewrite simulation__isGVZero in H1; eauto.
      clear - H22 H1 Hfsim2.
      destruct (isGVZero (los, nts) c0); eauto using fdef_sim__block_sim. 
      
      eapply used_in_fdef__tmn_value_doesnt_use_pid; eauto; simpl; auto.

  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq1 [Hpssim' [Hcssim' Heq5]]]; subst.

  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  apply phis_simulation_inv in Hpssim'; auto.
  subst.

  assert (blockInFdefB (block_intro l'0 ps'0 cs' tmn'0) F) as HBinF1'.
    admit.
  assert (reg_simulation pinfo mi F lc' lc'0) as Hlcsim2'.
    eapply switchToNewBasicBlock_rsim in Hbsim2; 
      eauto using mem_simulation__wf_sb_sim, used_in_fdef__phis_dont_use_pid.
  assert (als_simulation pinfo mi F lc' als als2) as Halsim2'.
    eapply switchToNewBasicBlock_asim; eauto.
  exists mi.
  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    destruct Hmsim as [J1 [J2 J3]].
    split; auto.
    split; auto.
      intros blk J.
      apply J2.
      intro J4. apply J.
      simpl.
      eapply switchToNewBasicBlock_isnt_alloca_in_ECs; eauto; simpl; eauto. 
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
  destruct Hbsim' as [Heq1 [Hpssim' [Hcssim' Heq5]]]; subst.

  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  apply phis_simulation_inv in Hpssim'; auto.
  subst.

  assert (blockInFdefB (block_intro l'0 ps'0 cs' tmn'0) F) as HBinF1'.
    admit.
  assert (reg_simulation pinfo mi F lc' lc'0) as Hlcsim2'.
    eapply switchToNewBasicBlock_rsim in Hbsim2; 
      eauto using mem_simulation__wf_sb_sim, used_in_fdef__phis_dont_use_pid.
  assert (als_simulation pinfo mi F lc' als als2) as Halsim2'.
    eapply switchToNewBasicBlock_asim; eauto.
  exists mi.
  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    destruct Hmsim as [J1 [J2 J3]].
    split; auto.
    split; auto.
      intros blk J.
      apply J2.
      intro J4. apply J. simpl.
      eapply switchToNewBasicBlock_isnt_alloca_in_ECs; eauto; simpl; eauto. 
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
  eapply simulation__getOperandValue with (lc2:=lc2) in H0; 
    simulation__getOperandValue_tac1.
  eapply mem_simulation__malloc in Hmsim; eauto. simpl in Hmsim.
  destruct Hmsim as [mi' [Hmsim [Hinc [Hprop1 Hprop2]]]].
  exists mi'.
  repeat_solve.
    eapply als_simulation__malloc; eauto.
    eapply reg_simulation__malloc; eauto.
    eapply inject_incr__preserves__ECs_simulation; eauto.
      eapply malloc__isnt_alloca_in_ECs; eauto.
    eapply inject_incr__preserves__ftable_simulation; eauto.

SCase "sFree". 
  destruct_ctx_other.
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.
  eapply simulation__getOperandValue with (lc2:=lc2) in H; 
    simulation__getOperandValue_tac1.
  eapply mem_simulation__free in Hmsim; eauto.
  exists mi.
  repeat_solve.

SCase "sAlloca". 
  destruct_ctx_other.
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.
  eapply simulation__getOperandValue with (lc2:=lc2) in H0; 
    simulation__getOperandValue_tac1.
  eapply mem_simulation__malloc in Hmsim; eauto. simpl in Hmsim.
  destruct Hmsim as [mi' [Hmsim [Hinc [Hprop1 Hprop2]]]].
  exists mi'.
  repeat_solve.
    eapply als_simulation__alloca; eauto. 
    eapply reg_simulation__malloc; eauto.
    eapply inject_incr__preserves__ECs_simulation; eauto.
      eapply malloc__isnt_alloca_in_ECs; eauto.
    eapply inject_incr__preserves__ftable_simulation; eauto. 

SCase "sLoad". 
  destruct_ctx_other.
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.
  exists mi.
  repeat_solve.
    apply als_simulation_update_lc; auto.
    apply reg_simulation_update_non_palloca; auto.
      eapply simulation__mload; eauto using mem_simulation__wf_sb_sim.
      simulation__getOperandValue_tac2.
    eapply mem_simulation__update_non_palloca; eauto; simpl; eauto.

SCase "sStore". 
  destruct_ctx_other.
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.
  exists mi.
  repeat_solve.
    simpl.
    eapply simulation__mstore; eauto using mem_simulation__wf_sb_sim;
    eapply simulation__getOperandValue; eauto using mem_simulation__wf_sb_sim;
      try solve [eapply used_in_fdef__cmd_value_doesnt_use_pid; 
                 eauto using in_middle; simpl; auto].

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
  exists mi.
  repeat_solve.
    destruct (isGVZero (los,nts) c);
      apply als_simulation_update_lc; auto.
    erewrite simulation__isGVZero with (c':=c0); 
      simulation__getOperandValue_tac2.
    destruct (isGVZero (los,nts) c0);
      apply reg_simulation_update_non_palloca; eauto; try solve [
        eapply simulation__getOperandValue; 
        eauto using mem_simulation__wf_sb_sim;
        try solve [eapply used_in_fdef__cmd_value_doesnt_use_pid; 
                 eauto using in_middle; simpl; auto]
      ].
    destruct (isGVZero (los,nts) c);
      eapply mem_simulation__update_non_palloca; eauto; simpl; eauto.

SCase "sCall".
  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.
  inv Hop2; uniq_result.

  SSCase "SCall".

  assert (Hfsim1:=Hpsim).
  eapply lookupFdefViaPtr__simulation in Hfsim1; eauto; 
      simulation__getOperandValue_tac2.

  assert (Hbsim1:=Hfsim1).
  eapply fdef_simulation__entry_block_simulation in Hbsim1; eauto.
  assert (Hbsim1':=Hbsim1).
  apply block_simulation_inv in Hbsim1'.
  destruct Hbsim1' as [Heq' [Hpsim1' [Hcsim1' Htsim1']]]; subst.
  exists mi.
  repeat_solve.
    exists l'0. exists ps'. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    apply fdef_simulation_inv in Hfsim1.
    destruct Hfsim1 as [Hfhsim1 Hbssim1].
    inv Hfhsim1.
    eapply reg_simulation__initLocals; eauto using mem_simulation__wf_sb_sim,
      used_in_fdef__params_dont_use_pid, WF_PhiInfo__args_dont_use_pid.

    destruct Hmsim as [Hmsim1 [Hmsim2 Hmsim3]].
    split; auto.
    split; auto.
      intros blk J.
      apply Hmsim2. 
      intro G. apply J.
      unfold isnt_alloca_in_ECs in *.
      intros. simpl in Hin.
      destruct Hin as [Hin | Hin].
        subst. simpl. 
        inv Hin. eapply WF_PhiInfo__isnt_alloca_in_EC; eauto.

        apply G. simpl. auto.

  SSCase "sExCall".

  eapply lookupFdefViaPtr__simulation_l2r in H1; eauto;
    simulation__getOperandValue_tac2.
  uniq_result.   

SCase "sExCall". 

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.
  inv Hop2; uniq_result.

  SSCase "SCall".

  eapply lookupFdefViaPtr__simulation_r2l in H1; eauto; 
    simulation__getOperandValue_tac2.
  uniq_result.   

  SSCase "sExCall".

  eapply lookupExFdecViaPtr__simulation with (fs1:=fs) (fs2:=fs2) in H1; eauto; 
    simulation__getOperandValue_tac2.
  uniq_result.

  eapply callExternalFunction__mem_simulation in Hmsim; eauto.
  destruct Hmsim as [EQ [mi' [Hmsim [Hinc [J1 [J2 J3]]]]]]; subst.
  exists mi'.
  repeat_solve.
    eapply inject_incr__preserves__ECs_simulation; eauto.
    eapply inject_incr__preserves__ftable_simulation; eauto.

Transparent inscope_of_tmn inscope_of_cmd.

Qed.

Lemma s_genInitState__dae_State_simulation: forall pinfo S1 S2 main VarArgs cfg2 
  IS2,
  system_simulation pinfo S1 S2 ->
  Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2) ->
  exists maxb, exists mi, exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo maxb mi cfg1 IS1 cfg2 IS2 /\
    sb_ds_gv_inject.wf_globals maxb (OpsemAux.Globals cfg1) /\
    0 <= maxb /\
    Promotability.wf_State maxb pinfo cfg1 IS1.
Admitted.

Lemma s_isFinialState__dae_State_simulation: forall maxb mi pinfo cfg1 FS1 cfg2 
  FS2 r (Hstsim : State_simulation pinfo maxb mi cfg1 FS1 cfg2 FS2)
  (Hfinal: s_isFinialState cfg2 FS2 = ret r),
  s_isFinialState cfg1 FS1 = ret r.
Admitted.

Lemma opsem_s_isFinialState__dae_State_simulation: forall 
  pinfo maxb mi cfg1 FS1 cfg2 FS2  
  (Hstsim : State_simulation pinfo maxb mi cfg1 FS1 cfg2 FS2),
  Opsem.s_isFinialState FS1 = Opsem.s_isFinialState FS2.
Admitted.

Lemma undefined_state__dae_State_simulation: forall pinfo maxb mi cfg1 St1 cfg2 
  St2 (Hstsim : State_simulation pinfo maxb mi cfg1 St1 cfg2 St2),
  OpsemPP.undefined_state cfg1 St1 -> OpsemPP.undefined_state cfg2 St2.
Admitted.

Lemma sop_star__dae_State_simulation: forall pinfo mi cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) maxb
  (Hwfg: sb_ds_gv_inject.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hless: 0 <= maxb) (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hstsim : State_simulation pinfo maxb mi cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr),
  exists FS1, exists mi', Opsem.sop_star cfg1 IS1 FS1 tr /\ 
    State_simulation pinfo maxb mi' cfg1 FS1 cfg2 FS2 /\
    inject_incr mi mi'.
Proof.
  intros.
  generalize dependent cfg1.
  generalize dependent IS1.
  generalize dependent mi.
  induction Hopstar; intros.
    exists IS1. exists mi. split; auto.

    assert (J:=Hwfpp).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]].
      apply opsem_s_isFinialState__dae_State_simulation in Hstsim.
      rewrite Hstsim in Hfinal1.
      contradict H; eauto using s_isFinialState__stuck.

      assert (OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
        admit. (* wf pp *)
      assert (Promotability.wf_State maxb pinfo cfg1 IS1') as Hnoalias'.
        admit. (* wf pp *)
      eapply dae_is_sim in Hstsim; eauto.
      destruct Hstsim as [Hstsim1 Hstsim2].
      destruct (@removable_State_dec pinfo IS1) as [Hrm | Hnrm].
        eapply Hstsim1 in Hrm; eauto.
        destruct Hrm as [Hstsim EQ]; subst.
        admit. (* we should do induction on the measure of State_simulation *)

        eapply Hstsim2 in Hnrm; eauto.
        destruct Hnrm as [mi' [Hstsim [EQ Hinc]]]; subst.
        eapply IHHopstar in Hstsim; eauto.
        destruct Hstsim as [FS1 [mi'' [Hopstar1 [Hstsim Hinc']]]].
        exists FS1. exists mi''.
        split; eauto.
        split; eauto.
          eapply inject_incr_trans; eauto.

      eapply undefined_state__dae_State_simulation in Hstsim; eauto.
      contradict H; eauto using undefined_state__stuck.
Qed.

Lemma sop_div__dae_State_simulation: forall pinfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) maxb mi
  (Hwfg: sb_ds_gv_inject.wf_globals maxb (OpsemAux.Globals cfg1))
  (Hless: 0 <= maxb) (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hstsim : State_simulation pinfo maxb mi cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Admitted.
     
Lemma dae_sim: forall id0 f pinfo los nts Ps1 Ps2 main VarArgs
  (Hwfpi: WF_PhiInfo pinfo)  
  (HwfS: wf_system nil [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Heq1: f = PI_f pinfo) (Heq2: id0 = PI_id pinfo),
  program_sim
    [module_intro los nts 
      (Ps1 ++  product_fdef (remove_fdef id0 f) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Proof.
  intros. subst.
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation pinfo
    [module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2)]
    [module_intro los nts
      (Ps1 ++ product_fdef (remove_fdef (PI_id pinfo) (PI_f pinfo)) :: Ps2)])
    as Hssim.
    unfold system_simulation.
    constructor; auto.
    repeat split; auto.
    unfold products_simulation.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    apply uniq_products_simulation; auto.

  constructor.
    intros tr t Hconv.
    inv Hconv.
    eapply s_genInitState__dae_State_simulation in H; eauto.
    destruct H as 
      [maxb [mi [cfg1 [IS1 [Hinit1 [Hstsim [Hwfg [Hless Hprom]]]]]]]]. 
    assert (OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    eapply sop_star__dae_State_simulation in Hstsim; eauto.
    destruct Hstsim as [FS1 [mi' [Hopstar1 [Hstsim' Hinc]]]].
    eapply s_isFinialState__dae_State_simulation in Hstsim'; eauto.
    econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    eapply s_genInitState__dae_State_simulation in H; eauto.
    destruct H as 
      [maxb [mi [cfg1 [IS1 [Hinit1 [Hstsim [Hwfg [Hless Hprom]]]]]]]]. 
    assert (OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    eapply sop_div__dae_State_simulation in Hstsim; eauto.
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
