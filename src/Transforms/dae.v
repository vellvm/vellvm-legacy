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
Require Import sb_ds_gv_inject.
Require Import sb_metadata.

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
       products_simulation pinfo Ps1 Ps1
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

Lemma fdef_sim__block_sim : forall pinfo f1 f2 b1 b2 l0,
  fdef_simulation pinfo f1 f2 ->
  lookupBlockViaLabelFromFdef f1 l0 = Some b1 ->
  lookupBlockViaLabelFromFdef f2 l0 = Some b2 ->
  block_simulation pinfo f1 b1 b2.
Admitted.

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

Lemma products_simulation__fdef_simulation : forall pinfo Ps1 Ps2 fid f1 f2,
  lookupFdefViaIDFromProducts Ps2 fid = Some f2 ->
  lookupFdefViaIDFromProducts Ps1 fid = Some f1 ->
  products_simulation pinfo Ps1 Ps2 ->
  fdef_simulation pinfo f1 f2.
Admitted.

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
    ~ isnt_alloca_in_ECs pinfo ((F, lc1) :: strip_ECs ECs) blk -> 
    mi blk = merror) ->
  (forall blk:mblock, 
    ~ isnt_alloca_in_ECs pinfo ((F, lc2) :: strip_ECs ECs) blk -> 
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
  mem_simulation pinfo mgb mi ((F, lc1) :: strip_ECs ECs) Mem1 Mem2 ->
  mem_simulation pinfo mgb mi ((F, lc2) :: strip_ECs ECs) Mem1 Mem2.
Proof.
  intros.
  destruct H1 as [J1 [J2 J3]].
  repeat (split; auto);
    eapply isnt_alloca_in_ECs_update_non_palloca; eauto; simpl; eauto.
Qed.

Lemma free_allocas_return_sim : forall TD mgb F 
  Result lc F' i0 n c t v p lc' EC lc'' gl2 pinfo
  (Hneq: PI_f pinfo <> F' \/ PI_id pinfo <> i0)
  (Hupdate: Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc lc' 
              gl2 = ret lc'') mi
  als M1 als2 M2 M1' M2'
  (Hmsim: mem_simulation pinfo mgb mi ((F, lc) :: (F', lc') :: strip_ECs EC) 
    M1 M2) 
  (Hfree1: free_allocas TD M1 als = Some M1')
  (Halsim: als_simulation pinfo mi F lc als als2)
  (Hfree2: free_allocas TD M2 als2 = Some M2'),
  mem_simulation pinfo mgb mi ((F',lc'') :: strip_ECs EC) M1' M2'.
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

Lemma simulation__getOperandValue : forall pinfo maxb mi lc lc2 TD Mem Mem2 gl F 
  v gv gv',
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
    destruct v.
(*
(Hprop: PI_f pinfo <> F' \/ PI_id pinfo <> i0)
    apply H1 in H2. auto.

    exists gv. split; auto. eapply sb_mem_inj__const2GV; eauto.
*)
Admitted.

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
  destruct Hnoalias as 
    [
      [[Hinscope' _] [HwfECs' HwfHT]] 
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals;
  fold Promotability.wf_ECStack in HwfECs'
end.

Lemma phis_simulation_inv: forall pinfo F ps1 ps2,
  WF_PhiInfo pinfo -> uniqFdef F ->
  phis_simulation pinfo F ps1 ps2 -> ps1 = ps2.
Admitted.

Lemma switchToNewBasicBlock_rsim : forall TD l1 l2 ps cs1 cs2 tmn1 tmn2 B1 B2
  gl lc1 lc2 F pinfo mi lc1' lc2'
  (H23 : @Opsem.switchToNewBasicBlock DGVs TD
          (block_intro l1 ps cs1 tmn1) B1 gl lc1' = 
         ret lc1)
  (Hbsim2 : block_simulation pinfo F B1 B2)
  (Hrsim: reg_simulation pinfo mi F lc1' lc2')
  (H2 : Opsem.switchToNewBasicBlock TD
         (block_intro l2 ps cs2 tmn2) B2 gl lc2' = 
        ret lc2), reg_simulation pinfo mi F lc1 lc2.
Admitted.

Lemma switchToNewBasicBlock_asim: forall pinfo F l0 ps0 cs0 tmn0 als1 als2 lc 
  lc' mi gl B TD,
  WF_PhiInfo pinfo -> uniqFdef F ->
  blockInFdefB (block_intro l0 ps0 cs0 tmn0) F = true ->
  als_simulation pinfo mi F lc als1 als2 ->
  Opsem.switchToNewBasicBlock TD (block_intro l0 ps0 cs0 tmn0) B gl lc = 
    ret lc' ->
  als_simulation pinfo mi F lc' als1 als2.
Admitted.

Lemma switchToNewBasicBlock_isnt_alloca_in_ECs : 
  forall pinfo TD ECs F gl B B' blk lc1 lc2,
  WF_PhiInfo pinfo -> uniqFdef F ->
  blockInFdefB B' F = true ->
  Opsem.switchToNewBasicBlock TD B' B gl lc1 = ret lc2 ->
  isnt_alloca_in_ECs pinfo ((F,lc1) :: strip_ECs ECs) blk ->
  isnt_alloca_in_ECs pinfo ((F,lc2) :: strip_ECs ECs) blk.
Admitted.

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
      inv Hin. destruct a. simpl in *.
      destruct H1 as [H1 _].
      unfold is_alloca_in_EC.
      destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
      remember (lookupAL (GVsT DGVs) Locals (PI_id pinfo)) as R.
      destruct R as [[]|]; auto.
      destruct p as [[]]; auto.
      destruct l0; auto.
      destruct (Z_eq_dec b (Mem.nextblock M1)); subst; auto.
      symmetry in HeqR.
      apply H1 in HeqR.
      destruct HeqR as [HeqR _].
      destruct HeqR as [HeqR _].
      destruct HeqR as [mb [J1 [J2 J3]]].
      rewrite Promotability.simpl_blk2GV in J1.
      inv J1. 
      contradict J3; omega.

      apply IHECs1; simpl; auto.
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
    v1 v2 gv3 gv3' pinfo Mem Mem2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  BOP TD lc gl bop0 sz0 v1 v2 = ret gv3 ->
  BOP TD lc2 gl bop0 sz0 v1 v2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F bop0 sz0 v1 v2 gv3 gv3' pinfo Me Mem2 Hwfg H0 H1 
    H2 H3.
  unfold BOP in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR2; eauto.
  eapply simulation__mbop in H2; eauto.
  destruct H2 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__FBOP : forall maxb mi lc lc2 TD gl F fop0 fp
    v1 v2 gv3 gv3' pinfo Mem Mem2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  FBOP TD lc gl fop0 fp v1 v2 = ret gv3 ->
  FBOP TD lc2 gl fop0 fp v1 v2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F fop0 fp v1 v2 gv3 gv3' pinfo Me Mem2 Hwfg H0 H1 
    H2 H3.
  unfold FBOP in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR2; eauto.
  eapply simulation__mfbop in H2; eauto.
  destruct H2 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__ExtractValue : forall mi gv1 gv1' TD t1 l0 gv gv' gl2 lc
  lc2 v F pinfo Mem Mem2 maxb,
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
  lc2 v1 v2 F pinfo Mem Mem2 maxb gv3 gv3' t2,
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

Lemma simulation__values2GVs : forall maxb mi lc lc2 TD Mem Mem2 gl F idxs gvs 
  gvs' pinfo,
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
    eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
    simpl. split; eauto.
Qed.

Lemma simulation__GEP : forall maxb mi TD Mem Mem2 inbounds0 vidxs1 vidxs2 gv1 
    gv1' gv2 gv2' t gl2 lc lc2 idxs v F pinfo,
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
    v1 gv3 gv3' pinfo Mem Mem2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  TRUNC TD lc gl op t1 v1 t2 = ret gv3 ->
  TRUNC TD lc2 gl op t1 v1 t2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F op t1 t2 v1 gv3 gv3' pinfo Mem Mem2 Hwfg H0 H1 
    H2 H3.
  unfold TRUNC in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR; eauto.
  eapply simulation__mtrunc in H3; eauto.
  destruct H3 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__EXT : forall maxb mi lc lc2 TD gl F op t1 t2
    v1 gv3 gv3' pinfo Mem Mem2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  EXT TD lc gl op t1 v1 t2 = ret gv3 ->
  EXT TD lc2 gl op t1 v1 t2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F op t1 t2 v1 gv3 gv3' pinfo Mem Mem2 Hwfg H0 H1 
    H2 H3.
  unfold EXT in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR; eauto.
  eapply simulation__mext in H3; eauto.
  destruct H3 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__CAST : forall maxb mi lc lc2 TD gl F op t1 t2
    v1 gv3 gv3' pinfo Mem Mem2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  CAST TD lc gl op t1 v1 t2 = ret gv3 ->
  CAST TD lc2 gl op t1 v1 t2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F op t1 t2 v1 gv3 gv3' pinfo Mem Mem2 Hwfg H0 H1 
    H2 H3.
  unfold CAST in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR; eauto.
  eapply simulation__mcast in H3; eauto.
  destruct H3 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__ICMP : forall maxb mi lc lc2 TD gl F cond0 t1 v1 v2 gv3 gv3' 
  pinfo Mem Mem2, 
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  ICMP TD lc gl cond0 t1 v1 v2 = ret gv3 ->
  ICMP TD lc2 gl cond0 t1 v1 v2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F cond0 t1 v1 v2 gv3 gv3' pinfo Me Mem2 Hwfg H0 H1 
    H2 H3.
  unfold ICMP in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR2; eauto.
  eapply simulation__micmp in H2; eauto.
  destruct H2 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__FCMP : forall maxb mi lc lc2 TD gl F fcond0 fp v1 v2 gv3 gv3' 
  pinfo Mem Mem2, 
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  FCMP TD lc gl fcond0 fp v1 v2 = ret gv3 ->
  FCMP TD lc2 gl fcond0 fp v1 v2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi lc lc2 TD gl F cond0 t1 v1 v2 gv3 gv3' pinfo Me Mem2 Hwfg H0 H1 
    H2 H3.
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

Ltac dse_is_sim_common_case :=
match goal with
| Hcssim2: cmds_simulation _ _ _ _,
  Hop2: Opsem.sInsn _ _ _ _,
  Hmsim: mem_simulation _ _ ?mi _ _ _ |- _ =>
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  exists mi;
  repeat_solve; try solve [
    apply als_simulation_update_lc; auto |
    apply reg_simulation_update_non_palloca; eauto using 
      simulation__BOP, simulation__FBOP, simulation__ExtractValue,
      simulation__InsertValue, simulation__GEP, simulation__TRUNC,
      simulation__EXT, simulation__ICMP, simulation__FCMP, simulation__CAST,
      mem_simulation__wf_sb_sim |
    eapply mem_simulation__update_non_palloca; eauto; simpl; eauto
  ]
end.

Lemma mem_simulation__malloc : forall mi TD Mem1 Mem2 tsz gn Mem1' Mem2' mb1
  mb2 v ECs1 pinfo maxb lc1 t id0 align0 F gn'
  (Hnrem : PI_f pinfo <> F \/
          PI_id pinfo <> getCmdLoc (insn_malloc id0 t v align0))
  (Hmsim : mem_simulation pinfo maxb mi ((F,lc1) :: ECs1) Mem1 Mem2)
  (Hsim: gv_inject mi gn gn')
  (Hmlc: malloc TD Mem1 tsz gn align0 = ret (Mem1', mb1))
  (Hmlc': malloc TD Mem2 tsz gn' align0 = ret (Mem2', mb2)),
  exists mi',
    mem_simulation pinfo maxb mi'
            ((F,updateAddAL (GVsT DGVs) lc1 id0
                 ($ blk2GV TD mb1 # typ_pointer t $)) :: ECs1) Mem1' Mem2' /\
    Values.inject_incr mi mi' /\
    mi' mb1 = Some (mb2, 0) /\
    (forall b, b <> mb1 -> mi b = mi' b).
Admitted.

Lemma als_simulation___malloc: forall pinfo F als1 als2 lc mi id0 mi' mb mb0 TD 
  t (Hprop1 : mi' mb = ret (mb0, 0))
  (Hprop2 : forall b : mblock, b <> mb -> mi b = mi' b),
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  als_simulation pinfo mi F lc als1 als2 ->
  als_simulation pinfo mi' F 
    (updateAddAL (GVsT DGVs) lc id0 ($ blk2GV TD mb # typ_pointer t $)) 
    als1 als2.
Admitted.

Lemma reg_simulation___malloc: forall pinfo F lc1 lc2 mi id0 mi' mb1 mb2 TD 
  t (Hprop1 : mi' mb1 = ret (mb2, 0))
  (Hprop2 : forall b : mblock, b <> mb1 -> mi b = mi' b),
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  reg_simulation pinfo mi F lc1 lc2 ->
  reg_simulation pinfo mi' F
    (updateAddAL (GVsT DGVs) lc1 id0 ($ blk2GV TD mb1 # typ_pointer t $))
    (updateAddAL (GVsT DGVs) lc2 id0 ($ blk2GV TD mb2 # typ_pointer t $)).
Admitted.

Lemma mem_simulation__alloca : forall mi TD Mem1 Mem2 tsz gn Mem1' Mem2' mb1
  mb2 ECs1 pinfo maxb lc1 t id0 align0 F gn'
  (Hnrem : PI_f pinfo <> F \/ PI_id pinfo <> id0)
  (Hmsim : mem_simulation pinfo maxb mi ((F,lc1) :: ECs1) Mem1 Mem2)
  (Hsim: gv_inject mi gn gn')
  (Hmlc: malloc TD Mem1 tsz gn align0 = ret (Mem1', mb1))
  (Hmlc': malloc TD Mem2 tsz gn' align0 = ret (Mem2', mb2)),
  exists mi',
    mem_simulation pinfo maxb mi'
            ((F, updateAddAL (GVsT DGVs) lc1 id0
                   ($ blk2GV TD mb1 # typ_pointer t $)) :: ECs1) Mem1' Mem2' /\
    Values.inject_incr mi mi' /\
    mi' mb1 = Some (mb2, 0) /\
    (forall b, b <> mb1 -> mi b = mi' b).
Admitted.

Lemma als_simulation___alloca: forall pinfo F als1 als2 lc mi id0 mi' mb mb0 TD 
  t (Hprop1 : mi' mb = ret (mb0, 0))
  (Hprop2 : forall b : mblock, b <> mb -> mi b = mi' b),
  PI_f pinfo <> F \/ PI_id pinfo <> id0 ->
  als_simulation pinfo mi F lc als1 als2 ->
  als_simulation pinfo mi' F 
    (updateAddAL (GVsT DGVs) lc id0 ($ blk2GV TD mb # typ_pointer t $)) 
    (mb::als1) (mb0::als2).
Admitted.

Lemma simulation__mload : forall mi TD pinfo maxb Mem1 Mem2 gvp1 align0 gv1 gv2 t
  gvp2 st,  
  mem_simulation pinfo maxb mi st Mem1 Mem2 ->
  mload TD Mem1 gvp1 t align0 = ret gv1 ->
  mload TD Mem2 gvp2 t align0 = ret gv2 ->
  gv_inject mi gvp1 gvp2 ->
  gv_inject mi gv1 gv2.
Admitted.

Lemma simulation__mstore : forall mi TD pinfo Mem1 Mem2 gvp1 gv1 gvp2 
  gv2 Mem1' Mem2' maxb F t align0 lc ECs,
  mem_simulation pinfo maxb mi ((F,lc) :: strip_ECs ECs) Mem1 Mem2 ->
  mstore TD Mem1 gvp1 t gv1 align0 = ret Mem1' ->
  mstore TD Mem2 gvp2 t gv2 align0 = ret Mem2' ->
  gv_inject mi gvp1 gvp2 ->
  gv_inject mi gv1 gv2 ->
  mem_simulation pinfo maxb mi ((F, lc) :: strip_ECs ECs) Mem1' Mem2'.
Admitted.

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
Admitted.

Lemma reg_simulation__initLocals: forall pinfo mi F lc1 lc2 lp gl gvs1 gvs2 lc1'
  lc2' la TD fa0 rt0 fid0 va0 lb,
  reg_simulation pinfo mi F lc1 lc2 ->
  Opsem.params2GVs TD lp lc1 gl = ret gvs1 ->
  Opsem.params2GVs TD lp lc2 gl = ret gvs2 ->
  Opsem.initLocals TD la gvs1 = ret lc1' ->
  Opsem.initLocals TD la gvs2 = ret lc2' ->
  reg_simulation pinfo mi 
    (fdef_intro (fheader_intro fa0 rt0 fid0 la va0) lb) lc1' lc2'.
Admitted.

Lemma lookupFdefViaPtr__simulation_l2r : forall pinfo Ps1 Ps2 fptr1 fptr2 f1 
  fs1 fs2 mi,
  products_simulation pinfo Ps1 Ps2 ->
  ftable_simulation mi fs1 fs2 ->
  gv_inject mi fptr1 fptr2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs1 fptr1 = Some f1 ->
  exists f2, 
    OpsemAux.lookupFdefViaPtr Ps2 fs2 fptr2 = Some f2 /\
    fdef_simulation pinfo f1 f2.
Admitted.

Lemma lookupExFdecViaPtr__simulation_l2r : forall pinfo Ps1 Ps2 fptr1 fptr2 f fs1
  fs2 mi,
  products_simulation pinfo Ps1 Ps2 ->
  ftable_simulation mi fs1 fs2 ->
  gv_inject mi fptr1 fptr2 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs1 fptr1 = Some f ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs2 fptr2 = Some f.
Admitted.

Lemma callExternalFunction__mem_simulation: forall pinfo mi M1 M2 fid0 gvs1 
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
Admitted.

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

    clear - H27 H1 Hlcsim2 Hlcsim2' Hwfgl Hmsim Hneq.
    eapply returnUpdateLocals_reg_simulation with (lc:=lc); 
      eauto using mem_simulation__wf_sb_sim.
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
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq1 [Hpssim' [Hcssim' Heq5]]]; subst.

  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  apply phis_simulation_inv in Hpssim'; auto.
  subst.

  assert (reg_simulation pinfo mi F lc' lc'0) as Hlcsim2'.
    eapply switchToNewBasicBlock_rsim in Hbsim2; eauto.

  assert (blockInFdefB (block_intro l'0 ps'0 cs' tmn'0) F) as HBinF1'.
    admit.
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

  assert (reg_simulation pinfo mi F lc' lc'0) as Hlcsim2'.
    eapply switchToNewBasicBlock_rsim in Hbsim2; eauto.

  assert (blockInFdefB (block_intro l'0 ps'0 cs' tmn'0) F) as HBinF1'.
    admit.
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
    eauto using mem_simulation__wf_sb_sim.
  eapply mem_simulation__malloc in Hmsim; eauto.
  destruct Hmsim as [mi' [Hmsim [Hinc [Hprop1 Hprop2]]]].
  exists mi'.
  repeat_solve.
    eapply als_simulation___malloc; eauto.
    eapply reg_simulation___malloc; eauto.
    eapply inject_incr__preserves__ECs_simulation; eauto.
      eapply malloc__isnt_alloca_in_ECs; eauto.
    eapply inject_incr__preserves__ftable_simulation; eauto.

SCase "sFree". 
  destruct_ctx_other.
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.
  eapply simulation__getOperandValue with (lc2:=lc2) in H; 
    eauto using mem_simulation__wf_sb_sim.
  eapply mem_simulation__free in Hmsim; eauto.
  exists mi.
  repeat_solve.

SCase "sAlloca". 
  destruct_ctx_other.
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.
  eapply simulation__getOperandValue with (lc2:=lc2) in H0; 
    eauto using mem_simulation__wf_sb_sim.
  eapply mem_simulation__alloca in Hmsim; eauto.
  destruct Hmsim as [mi' [Hmsim [Hinc [Hprop1 Hprop2]]]].
  exists mi'.
  repeat_solve.
    eapply als_simulation___alloca; eauto. 
    eapply reg_simulation___malloc; eauto.
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
      eapply simulation__mload; eauto.
      eapply simulation__getOperandValue; eauto using mem_simulation__wf_sb_sim.
    eapply mem_simulation__update_non_palloca; eauto; simpl; eauto.

SCase "sStore". 
  destruct_ctx_other.
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.
  exists mi.
  repeat_solve.
    simpl.
    eapply simulation__mstore; eauto 
      using simulation__getOperandValue, mem_simulation__wf_sb_sim.

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
    erewrite simulation__isGVZero; eauto
      using simulation__getOperandValue, mem_simulation__wf_sb_sim.
    destruct (isGVZero (los,nts) c0);
      apply reg_simulation_update_non_palloca; eauto
        using simulation__getOperandValue, mem_simulation__wf_sb_sim.
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
  eapply lookupFdefViaPtr__simulation in Hfsim1; eauto
    using simulation__getOperandValue, mem_simulation__wf_sb_sim.

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

    eapply reg_simulation__initLocals; eauto.

    destruct Hmsim as [Hmsim1 [Hmsim2 Hmsim3]].
    split; auto.
    split; auto.
      intros blk J.
      apply Hmsim2. 
      intro G. apply J.
      unfold isnt_alloca_in_ECs in *.
      intros. simpl in Hin.
      destruct Hin as [Hin | Hin].
        subst. simpl. admit.
        apply G. simpl. auto.

  SSCase "sExCall".

  eapply lookupFdefViaPtr__simulation_l2r in H1; eauto
    using simulation__getOperandValue, mem_simulation__wf_sb_sim.
  destruct H1 as [f2 [H1 H1']].
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
  inv Hop2; uniq_result.

  SSCase "SCall".

  eapply lookupExFdecViaPtr__simulation_l2r in H1; eauto
    using simulation__getOperandValue, mem_simulation__wf_sb_sim.
  apply OpsemAux.lookupExFdecViaPtr_inversion in H1.
  apply OpsemAux.lookupFdefViaPtr_inversion in H29.
  destruct H1 as [fn [J1 [J2 J3]]].
  destruct H29 as [fn' [J4 J5]].
  uniq_result.   

  SSCase "sExCall".

  eapply lookupExFdecViaPtr__simulation_l2r in H1; eauto
    using simulation__getOperandValue, mem_simulation__wf_sb_sim.
  uniq_result.

  eapply callExternalFunction__mem_simulation in Hmsim; eauto.
  destruct Hmsim as [EQ [mi' [Hmsim [Hinc [J1 [J2 J3]]]]]]; subst.
  exists mi'.
  repeat_solve.
    eapply inject_incr__preserves__ECs_simulation; eauto.
    eapply inject_incr__preserves__ftable_simulation; eauto.
    
Transparent inscope_of_tmn inscope_of_cmd.

Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
