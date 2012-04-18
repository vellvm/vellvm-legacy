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
Require Import memory_sim.
Require Import genericvalues_inject.
Require Import trans_tactic.
Require Import top_sim.
Require Import dae_defs.

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
  destruct (zlt 0 (Size.to_Z tsz * z)); tinv H0.
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
        destruct (Mem.valid_block_dec Mem1 (Mem.nextblock Mem1)).
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

Lemma mem_simulation__free_l2r : forall mi TD Mem1 Mem2 Mem1'
  ECs1 pinfo maxb lc1 F ptr1 ptr2
  (Hmsim : mem_simulation pinfo maxb mi ((F, lc1) :: ECs1) Mem1 Mem2)
  (Hsim: gv_inject mi ptr1 ptr2)
  (Hmlc: free TD Mem1 ptr1 = ret Mem1'),
  exists Mem2', 
    free TD Mem2 ptr2 = ret Mem2' /\
    mem_simulation pinfo maxb mi ((F, lc1) :: ECs1) Mem1' Mem2'.
Proof.
  intros.
  destruct Hmsim as [J1 [J2 J3]].
  apply free_inv in Hmlc.
  destruct Hmlc as [blk [ofs [hi [lo [H1 [H2 [H3 H4]]]]]]].
  unfold GV2ptr in *.
  destruct ptr1 as [|[[]][]]; inv H1.
  inv Hsim. inv H7. inv H6.
  eapply mem_inj__free in H4; eauto.
  destruct H4 as [Mem2'' [J4 [J5 J6]]].
  match goal with 
  | H1: mi ?blk = Some (_, _), H3: (_,_) = Mem.bounds _ ?blk |- _ =>
    assert (H6':=H1);
    apply (mi_range_block maxb mi Mem1 Mem2 J3) in H1; subst;
    apply (mi_bounds maxb mi Mem1 Mem2 J3) in H6';
    rewrite H6' in H3
  end.
  assert (lo + 0 = lo) as EQ1. omega.
  assert (hi + 0 = hi) as EQ2. omega.
  rewrite EQ1 in J4. rewrite EQ2 in J4. clear EQ1 EQ2.
  exists Mem2''. 
  unfold free, mem_simulation. simpl.
  split; auto.
    rewrite Int.add_zero. rewrite H2. rewrite <- H3.
    destruct_if; congruence.
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
  eapply mem_simulation__free_l2r in Hmsim; eauto.
  destruct Hmsim as [Mem2'' [J1 J2]].
  uniq_result. auto.
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

Lemma mem_simulation__free_allocas_l2r : forall TD mgb F lc EC pinfo mi
  als1 M1 als2 M2 M1'
  (Hfree1: free_allocas TD M1 als1 = Some M1')
  (Hmsim: mem_simulation pinfo mgb mi ((F,lc)::EC) M1 M2)
  (Halsim: als_simulation pinfo mi F lc als1 als2),
  exists M2', 
    free_allocas TD M2 als2 = Some M2' /\
    mem_simulation pinfo mgb mi ((F,lc)::EC) M1' M2'.
Proof.
  induction als1; destruct als2; simpl; intros.
    uniq_result. eauto.
    uniq_result.

    inv_mbind''. uniq_result.
    destruct Halsim as [J1 J2].
    exists M2. split; auto.
    eapply mem_simulation__pfree with (Mem1':=m) in Hmsim; eauto.
    eapply IHals1 in Hmsim; eauto.
    destruct Hmsim as [M2' [J3 J4]].
    simpl in J3. congruence.

    inv_mbind''. symmetry_ctx.
    remember (is_alloca_in_EC pinfo F lc a) as R.
    destruct R; destruct Halsim as [Halsim1 Halsim2].
      eapply mem_simulation__pfree in Hmsim; eauto.
      eapply IHals1 in Hmsim; eauto. simpl in Hmsim. eauto.

      assert (gv_inject mi (blk2GV TD a) (blk2GV TD m)) as Hinj.
        unfold blk2GV, ptr2GV, val2GV. simpl.
        constructor; auto.
          assert (Int.repr 31 0 = Int.add 31 (Int.repr 31 0) (Int.repr 31 0))
            as EQ.
            rewrite Int.add_zero. auto.
          rewrite EQ at 2.
          econstructor; eauto.
      eapply mem_simulation__free_l2r with (ptr1:=blk2GV TD a) 
        (ptr2:=blk2GV TD m) in Hmsim; eauto.
      destruct Hmsim as [Mem2' [J1 Hmsim]].
      eapply IHals1 in Hmsim; eauto.
      destruct Hmsim as [Mem2'' [J2 Hmsim]].
      exists Mem2''. fill_ctxhole. split; auto.
Qed.

Lemma mem_simulation__free_allocas : forall TD mgb F lc EC pinfo mi
  als1 M1 als2 M2 M1'
  (Hfree1: free_allocas TD M1 als1 = Some M1')
  (Hmsim: mem_simulation pinfo mgb mi ((F,lc)::EC) M1 M2) M2'
  (Halsim: als_simulation pinfo mi F lc als1 als2)
  (Hfree2: free_allocas TD M2 als2 = Some M2'),
  mem_simulation pinfo mgb mi ((F,lc)::EC) M1' M2'.
Proof.
  intros.
  eapply mem_simulation__free_allocas_l2r in Hmsim; eauto.
  destruct Hmsim as [M2'' [J1 J2]].
  uniq_result. auto.
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
  Result lc F' i0 n c t0 v0 v p lc' ECs lc'' gl2 pinfo
  (Hneq: PI_f pinfo <> F' \/ PI_id pinfo <> i0)
  (Hupdate: Opsem.returnUpdateLocals TD (insn_call i0 n c t0 v0 v p) Result lc lc'
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
  inv_mbind'.
  eapply mem_simulation__update_non_palloca; eauto.
Qed.


Lemma dae_is_sim_removable_state: forall (maxb : Values.block) (pinfo : PhiInfo)
  (mi : MoreMem.meminj) (Cfg1 : OpsemAux.Config) (St1 : Opsem.State)
  (Cfg2 : OpsemAux.Config) (St2 : Opsem.State) (Hwfpi : WF_PhiInfo pinfo)
  (Hwfgl : wf_globals maxb (OpsemAux.Globals Cfg1)) (Hinbd : 0 <= maxb)
  (Hnuse : used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfcfg : OpsemPP.wf_Config Cfg1) (Hwfpp : OpsemPP.wf_State Cfg1 St1)
  (Hnoalias : Promotability.wf_State maxb pinfo Cfg1 St1)
  (Hsim : State_simulation pinfo maxb mi Cfg1 St1 Cfg2 St2)
  (Hrem : removable_State pinfo St1) (St1' : Opsem.State) (tr1 : trace)
  (Hpalloca : palloca_props.wf_State pinfo St1)
  (Hop1 : Opsem.sInsn Cfg1 St1 St1' tr1),
  exists mi' : MoreMem.meminj,
    State_simulation pinfo maxb mi' Cfg1 St1' Cfg2 St2 /\
    tr1 = E0 /\ inject_incr mi mi'.
Proof.
  intros.
  destruct Cfg1 as [S1 [los nts] Ps1 gl1 fs1].
  destruct St1 as [ECs1 M1].
  destruct ECs1 as [|[F1 B1 [|c1 cs1] tmn1 lc1 als1] ECs1]; tinv Hrem.
  simpl in Hrem.
  destruct (fdef_dec (PI_f pinfo) F1); subst; tinv Hrem.
  destruct (id_dec (PI_id pinfo) (getCmdLoc c1)); subst; tinv Hrem.

  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]]; subst.
  destruct Hwfpp as
    [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]]
     [HwfECs Hwfcall]]
    ]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs.

  destruct Hnoalias as
    [
      [[Hinscope' _] [HwfECs' HwfHT]]
      [[Hdisjals Halsbd] HwfM]
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
      [Hfsim2 [Heq1 [Halsim2 [Hbsim2
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst.

  assert (c1 = 
    insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo) (PI_align pinfo)) 
    as EQ.
    destruct Heq3 as [? [? [? Heq3]]]; subst.
    eapply WF_PhiInfo_spec1'; eauto 2 using wf_system__uniqFdef.
  subst.

  inv Hop1.

  uniq_result.
  eapply mem_simulation__palloca in Hmsim; eauto.
  destruct Hmsim as [mi' [Hmsim [Hinc [Hmi1 Hmi2]]]].
  exists mi'.
  repeat_solve.
    eapply als_simulation_update_palloca; eauto.
      eapply WF_PhiInfo_spec15 in Hpalloca; eauto using wf_system__uniqFdef.
    eapply reg_simulation_update_palloca; eauto.
    eapply RemoveSim.cmds_simulation_elim_cons_inv; eauto.
    eapply inject_incr__preserves__ECs_simulation; eauto.
      eapply malloc__isnt_alloca_in_ECs; eauto.
    eapply OpsemAux.inject_incr__preserves__ftable_simulation; eauto.
Qed.

Lemma simulation__BOP : forall maxb mi lc lc2 los nts gl F bop0 sz0
    v1 v2 gv3 gv3' pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1)
  (Hprop2: value_doesnt_use_pid pinfo F v2) S ps
  (Hv1: wf_value S (module_intro los nts ps) F v1 (typ_int sz0))
  (Hv2: wf_value S (module_intro los nts ps) F v2 (typ_int sz0)),
  wf_globals maxb gl ->
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  BOP (los,nts) lc gl bop0 sz0 v1 v2 = ret gv3 ->
  BOP (los,nts) lc2 gl bop0 sz0 v1 v2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.
  intros maxb mi lc lc2 los nts gl F bop0 sz0 v1 v2 gv3 gv3' pinfo Me Mem2 
    Hprop1 Hprop2 S ps Hv1 Hv2 Hwfg H0 H1 H2 H3.
  unfold BOP in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR2; eauto.
  eapply simulation__mbop in H2; eauto.
  destruct H2 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__FBOP : forall maxb mi lc lc2 los nts gl F fop0 fp
    v1 v2 gv3 gv3' pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1)
    (Hprop2: value_doesnt_use_pid pinfo F v2) S ps
    (Hv1: wf_value S (module_intro los nts ps) F v1 (typ_floatpoint fp))
    (Hv2: wf_value S (module_intro los nts ps) F v2 (typ_floatpoint fp)),
  wf_globals maxb gl ->
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  FBOP (los,nts) lc gl fop0 fp v1 v2 = ret gv3 ->
  FBOP (los,nts) lc2 gl fop0 fp v1 v2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.
  intros maxb mi lc lc2 los nts gl F fop0 fp v1 v2 gv3 gv3' pinfo Me Mem2 Hprop1
    Hprop2 S ps Hv1 Hv2 Hwfg H0 H1 H2 H3.
  unfold FBOP in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR2; eauto.
  eapply simulation__mfbop in H2; eauto.
  destruct H2 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__ExtractValue : forall mi gv1 gv1' los nts t1 l0 gv gv' gl2 lc
  lc2 v F pinfo Mem Mem2 maxb (Hprop: value_doesnt_use_pid pinfo F v) S ps
  (Hv1: wf_value S (module_intro los nts ps) F v t1),
  wf_globals maxb gl2 ->
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  getOperandValue (los,nts) v lc gl2 = Some gv1 ->
  getOperandValue (los,nts) v lc2 gl2 = Some gv1' ->
  extractGenericValue (los,nts) t1 gv1 l0 = Some gv ->
  extractGenericValue (los,nts) t1 gv1' l0 = Some gv' ->
  gv_inject mi gv gv'.
Proof.
  intros.
  eapply simulation__getOperandValue with (lc2:=lc2) in H2; eauto.
  eapply simulation__extractGenericValue in H4; eauto.
  destruct H4 as [gv'' [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__InsertValue : forall mi gv1 gv1' los nts t1 l0 gv2 gv2' gl2 lc
  lc2 v1 v2 F pinfo Mem Mem2 maxb gv3 gv3' t2 ps S
  (Hprop1: value_doesnt_use_pid pinfo F v1)
  (Hprop2: value_doesnt_use_pid pinfo F v2)
  (Hv1: wf_value S (module_intro los nts ps) F v1 t1)
  (Hv2: wf_value S (module_intro los nts ps) F v2 t2),
  wf_globals maxb gl2 ->
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  getOperandValue (los,nts) v1 lc gl2 = Some gv1 ->
  getOperandValue (los,nts) v1 lc2 gl2 = Some gv1' ->
  getOperandValue (los,nts) v2 lc gl2 = Some gv2 ->
  getOperandValue (los,nts) v2 lc2 gl2 = Some gv2' ->
  insertGenericValue (los,nts) t1 gv1 l0 t2 gv2 = ret gv3 ->
  insertGenericValue (los,nts) t1 gv1' l0 t2 gv2' = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.
  intros.
  eapply simulation__getOperandValue with (lc2:=lc2) in H2; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in H4; eauto.
  eapply simulation__insertGenericValue in H6; eauto.
  destruct H6 as [gv'' [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__values2GVs : forall maxb mi lc lc2 los nts Mem Mem2 gl F idxs 
  gvs gvs' pinfo (Hprop: list_value_doesnt_use_pid pinfo F idxs) S ps
  (Ht: wf_value_list 
    (List.map
      (fun p : sz * value =>
        let '(sz_, value_) := p in
         (S,(module_intro los nts ps),F,value_,typ_int Size.ThirtyTwo)) idxs)),
  wf_globals maxb gl ->
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  values2GVs (los,nts) idxs lc gl = ret gvs ->
  values2GVs (los,nts) idxs lc2 gl = ret gvs' ->
  gvs_inject mi gvs gvs'.
Proof.
  induction idxs; simpl; intros.
    inv H2. inv H3. simpl. auto.

    simpl_prod.
    rewrite wf_value_list_cons_iff in Ht. destruct Ht.
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

Lemma simulation__GEP : forall maxb mi los nts Mem Mem2 inbounds0 vidxs1 vidxs2 
    gv1 gv1' gv2 gv2' t gl2 lc lc2 idxs v F pinfo t' S ps
  (Hprop1: value_doesnt_use_pid pinfo F v)
  (Hprop2: list_value_doesnt_use_pid pinfo F idxs)
  (Hv1: wf_value S (module_intro los nts ps) F v (typ_pointer t))
  (Ht: wf_value_list 
    (List.map
      (fun p : sz * value =>
        let '(sz_, value_) := p in
          (S,(module_intro los nts ps),F,value_,typ_int Size.ThirtyTwo)) idxs)),
  wf_globals maxb gl2 ->
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  getOperandValue (los,nts) v lc gl2 = Some gv1 ->
  getOperandValue (los,nts) v lc2 gl2 = Some gv1' ->
  values2GVs (los,nts) idxs lc gl2 = Some vidxs1 ->
  values2GVs (los,nts) idxs lc2 gl2 = Some vidxs2 ->
  GEP (los,nts) t gv1 vidxs1 inbounds0 t' = ret gv2 ->
  GEP (los,nts) t gv1' vidxs2 inbounds0 t' = ret gv2' ->
  gv_inject mi gv2 gv2'.
Proof.
  intros.
  eapply simulation__getOperandValue with (lc2:=lc2) in H2; eauto.
  eapply simulation__values2GVs with (lc2:=lc2) in H4; eauto.
  eapply genericvalues_inject.simulation__GEP in H6; eauto.
  destruct H6 as [gv'' [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__TRUNC : forall maxb mi lc lc2 los nts gl F op t1 t2
    v1 gv3 gv3' pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1)
  S ps (Hv1: wf_value S (module_intro los nts ps) F v1 t1),
  wf_globals maxb gl ->
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  TRUNC (los,nts) lc gl op t1 v1 t2 = ret gv3 ->
  TRUNC (los,nts) lc2 gl op t1 v1 t2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.
  intros maxb mi lc lc2 los nts gl F op t1 t2 v1 gv3 gv3' pinfo Mem Mem2 Hwfg 
    Hprop1 S ps Hv1 H0 H1 H2 H3.
  unfold TRUNC in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR; eauto.
  eapply simulation__mtrunc in H3; eauto.
  destruct H3 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__EXT : forall maxb mi lc lc2 los nts gl F op t1 t2
    v1 gv3 gv3' pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1)
  S ps (Hv1: wf_value S (module_intro los nts ps) F v1 t1),
  wf_globals maxb gl ->
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  EXT (los,nts) lc gl op t1 v1 t2 = ret gv3 ->
  EXT (los,nts) lc2 gl op t1 v1 t2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.
  intros maxb mi lc lc2 los nts gl F op t1 t2 v1 gv3 gv3' pinfo Mem Mem2 Hprop1 
    S ps Hv1 Hwfg H0 H1 H2 H3.
  unfold EXT in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR; eauto.
  eapply simulation__mext in H3; eauto.
  destruct H3 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__CAST : forall maxb mi lc lc2 los nts gl F op t1 t2
    v1 gv3 gv3' pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1)
  S ps (Hv1: wf_value S (module_intro los nts ps) F v1 t1),
  wf_globals maxb gl ->
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  CAST (los,nts) lc gl op t1 v1 t2 = ret gv3 ->
  CAST (los,nts) lc2 gl op t1 v1 t2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.
  intros maxb mi lc lc2 los nts gl F op t1 t2 v1 gv3 gv3' pinfo Mem Mem2 Hprop1 
    S ps Hv1 Hwfg H0 H1 H2 H3.
  unfold CAST in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR; eauto.
  eapply simulation__mcast in H3; eauto.
  destruct H3 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__ICMP : forall maxb mi lc lc2 los nts gl F cond0 t1 v1 v2 gv3 
  gv3' pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1)
  (Hprop2: value_doesnt_use_pid pinfo F v2)
  S ps (Hv1: wf_value S (module_intro los nts ps) F v1 t1)
  (Hv2: wf_value S (module_intro los nts ps) F v2 t1),
  wf_globals maxb gl ->
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  ICMP (los,nts) lc gl cond0 t1 v1 v2 = ret gv3 ->
  ICMP (los,nts) lc2 gl cond0 t1 v1 v2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.
  intros maxb mi lc lc2 los nts gl F cond0 t1 v1 v2 gv3 gv3' pinfo Me Mem2 
    Hprop1 Hprop2 S ps Hv1 Hv2 Hwfg H0 H1 H2 H3.
  unfold ICMP in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR2; eauto.
  eapply simulation__micmp in H2; eauto.
  destruct H2 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__FCMP : forall maxb mi lc lc2 los nts gl F fcond0 fp v1 v2 gv3 
  gv3' pinfo Mem Mem2 (Hprop1: value_doesnt_use_pid pinfo F v1)
  (Hprop2: value_doesnt_use_pid pinfo F v2)
  S ps (Hv1: wf_value S (module_intro los nts ps) F v1 (typ_floatpoint fp))
  (Hv2: wf_value S (module_intro los nts ps) F v2 (typ_floatpoint fp)),
  wf_globals maxb gl ->
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi F lc lc2 ->
  FCMP (los,nts) lc gl fcond0 fp v1 v2 = ret gv3 ->
  FCMP (los,nts) lc2 gl fcond0 fp v1 v2 = ret gv3' ->
  gv_inject mi gv3 gv3'.
Proof.
  intros maxb mi lc lc2 los nts gl F cond0 t1 v1 v2 gv3 gv3' pinfo Me Mem2 Hprop1
    Hprop2 S ps Hv1 Hv2 Hwfg H0 H1 H2 H3.
  unfold FCMP in *.
  inv_mbind'. symmetry_ctx.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR1; eauto.
  eapply simulation__getOperandValue with (lc2:=lc2) in HeqR2; eauto.
  eapply simulation__mfcmp in H2; eauto.
  destruct H2 as [gv4 [J1 J2]].
  uniq_result. auto.
Qed.

Lemma mem_simulation__malloc_l2r' : forall mi TD Mem1 Mem2 tsz gn Mem1' mb1
  pinfo maxb align0 gn' ecs 
  (Hmsim : mem_simulation pinfo maxb mi ecs Mem1 Mem2)
  (Hsim: gv_inject mi gn gn')
  (Hmlc: malloc TD Mem1 tsz gn align0 = ret (Mem1', mb1)),
  exists Mem2', exists mi', exists mb2,
    malloc TD Mem2 tsz gn' align0 = ret (Mem2', mb2) /\
    MoreMem.mem_inj mi' Mem1' Mem2' /\
    wf_sb_mi maxb mi' Mem1' Mem2' /\
    Values.inject_incr mi mi' /\
    mi' mb1 = Some (mb2, 0) /\
    (forall b, b <> mb1 -> mi b = mi' b).
Proof.
  intros.
  destruct Hmsim as [Hmsim1 [Hmsim2 Hmsim3]].
  eapply mem_inj__malloc in Hmsim1; eauto.
  destruct Hmsim1 as [mi' [Mem2'' [mb' [J1 [J2 [J3 [J4 [J5 J6]]]]]]]].
  exists Mem2''. exists mi'. exists mb'.
  split.
    unfold malloc in J1. unfold malloc.
    inv_mbind. symmetry_ctx.
    apply simulation__eq__GV2int with (TD:=TD)(sz:=Size.ThirtyTwo) in Hsim; 
      eauto.
    rewrite Hsim in HeqR. rewrite HeqR. auto.
  split; auto.
Qed.

Lemma mem_simulation__malloc_l2r : forall mi TD Mem1 Mem2 tsz gn Mem1' mb1
  ECs1 pinfo maxb lc1 t id0 align0 F gn' ecs EC
  (Hprom: Promotability.wf_ECStack maxb pinfo TD Mem1 (EC::ECs1))
  (Hnrem : PI_f pinfo <> F \/ PI_id pinfo <> id0)
  (Heq1: F = Opsem.CurFunction EC) (Heq2: lc1 = Opsem.Locals EC)
  (Heq3: ecs = strip_ECs (EC::ECs1))
  (Hmsim : mem_simulation pinfo maxb mi ecs Mem1 Mem2)
  (Hsim: gv_inject mi gn gn')
  (Hmlc: malloc TD Mem1 tsz gn align0 = ret (Mem1', mb1)),
  exists Mem2', exists mi', exists mb2,
    malloc TD Mem2 tsz gn' align0 = ret (Mem2', mb2) /\
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
  assert (Hmsim':=Hmsim).
  eapply mem_simulation__malloc_l2r' in Hmsim'; eauto.
  destruct Hmsim' as [Mem2' [mi' [mb2 [J1 [J2 [J3 [J4 [J5 J6]]]]]]]].
  destruct Hmsim as [_ [Hmsim2 _]].
  exists Mem2'. exists mi'. exists mb2.
  split; auto.
  split; auto.
    split; auto.
    split; auto.
      eapply isnt_alloca_in_ECs_update_non_palloca; eauto.
      intros. subst.
      eapply malloc__isnt_alloca_in_ECs in Hprom; eauto.
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
  eapply mem_simulation__malloc_l2r in Hmsim; eauto.
  destruct Hmsim as [Mem2'0 [mi' [mb3 [J1 [J2 [J3 J4]]]]]].
  uniq_result. eauto.
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

Lemma simulation__mload_l2r : forall mi TD pinfo maxb Mem1 Mem2 gvp1 align0 gv1 
  t gvp2 st,
  mem_simulation pinfo maxb mi st Mem1 Mem2 ->
  mload TD Mem1 gvp1 t align0 = ret gv1 ->
  gv_inject mi gvp1 gvp2 ->
  exists gv2, 
    mload TD Mem2 gvp2 t align0 = ret gv2 /\
    gv_inject mi gv1 gv2.
Proof.
  intros mi TD pinfo max Mem1 Mem2 gvp1 align0 gv1 t gvp2 st Hmsim
  Hmload1 Hginject.
  apply mload_inv in Hmload1.
  destruct Hmload1 as [b1 [ofs1 [m1 [mc1 [Heq1 [Hflat1 Hmload1]]]]]]; subst.
  inv Hginject. inv H3. inv H4.
  destruct Hmsim as [Hmsim [_ Hwfmi]].
  eapply simulation_mload_aux in Hmload1; eauto.
  destruct Hmload1 as [gv2' [Hmload1 Hinj]].
  exists gv2'.
  split; auto.
    unfold mload. simpl. fill_ctxhole. 
    inv Hwfmi.
    apply mi_range_block in H1. subst.
    rewrite Int.add_zero.
    assert (Int.signed 31 ofs1 + 0 = Int.signed 31 ofs1) as EQ. zauto.
    congruence.
Qed.

Lemma simulation__mload : forall mi TD pinfo maxb Mem1 Mem2 gvp1 align0 gv1 gv2 t
  gvp2 st,
  mem_simulation pinfo maxb mi st Mem1 Mem2 ->
  mload TD Mem1 gvp1 t align0 = ret gv1 ->
  mload TD Mem2 gvp2 t align0 = ret gv2 ->
  gv_inject mi gvp1 gvp2 ->
  gv_inject mi gv1 gv2.
Proof.
  intros mi TD pinfo max Mem1 Mem2 gvp1 align0 gv1 gv2 t gvp2 st Hmsim
  Hmload1 Hmload2 Hginject.
  eapply simulation__mload_l2r in Hmsim; eauto.
  destruct Hmsim as [gv2' [J1 J2]].
  uniq_result. auto.
Qed.

Lemma simulation__mstore_l2r : forall mi TD pinfo Mem1 Mem2 gvp1 gv1 gvp2
  gv2 Mem1' maxb F t align0 lc ECs,
  mem_simulation pinfo maxb mi ((F,lc) :: strip_ECs ECs) Mem1 Mem2 ->
  mstore TD Mem1 gvp1 t gv1 align0 = ret Mem1' ->
  gv_inject mi gvp1 gvp2 ->
  gv_inject mi gv1 gv2 ->
  exists Mem2', 
    mstore TD Mem2 gvp2 t gv2 align0 = ret Mem2' /\
    mem_simulation pinfo maxb mi ((F, lc) :: strip_ECs ECs) Mem1' Mem2'.
Proof.
  intros mi TD pinfo Mem1 Mem2 gvp1 gv1 gvp2 gv2 Mem1' maxb F t align0 lc
    ECs Hmsim Hmstore1 Hginject1 Hginject2.
  apply mstore_inversion in Hmstore1.
  destruct Hmstore1 as [b1 [ofs1 [cm1 [Heq1 Hmstore1]]]]; subst.
  inv Hginject1. inv H3. inv H4.
  destruct Hmsim as [Hmsim1 [Hmsim2 Hwfmi]].
  eapply mem_inj_mstore_aux in Hmstore1; eauto.
  destruct Hmstore1 as [Mem2'' [Hmstore1 [Hwfmi' Hmsim']]].
  unfold mstore. simpl.
  inv Hwfmi.
  apply mi_range_block in H1. subst.
  rewrite Int.add_zero.
  assert (Int.signed 31 ofs1 + 0 = Int.signed 31 ofs1) as EQ. zauto.
  rewrite EQ in Hmstore1.
  exists Mem2''.
  split; auto.
  split; auto.
Qed.

Lemma simulation__mstore : forall mi TD pinfo Mem1 Mem2 gvp1 gv1 gvp2
  gv2 Mem1' Mem2' maxb F t align0 lc ECs,
  mem_simulation pinfo maxb mi ((F,lc) :: strip_ECs ECs) Mem1 Mem2 ->
  mstore TD Mem1 gvp1 t gv1 align0 = ret Mem1' ->
  mstore TD Mem2 gvp2 t gv2 align0 = ret Mem2' ->
  gv_inject mi gvp1 gvp2 ->
  gv_inject mi gv1 gv2 ->
  mem_simulation pinfo maxb mi ((F, lc) :: strip_ECs ECs) Mem1' Mem2'.
Proof.
  intros mi TD pinfo Mem1 Mem2 gvp1 gv1 gvp2 gv2 Mem1' Mem2' maxb F t align0 lc
    ECs Hmsim Hmstore1 Hmstore2 Hginject1 Hginject2.
  eapply simulation__mstore_l2r in Hmsim; eauto.
  destruct Hmsim as [Mem2'' [J1 J2]].
  uniq_result. auto.
Qed.

Axiom callExternalFunction__mem_simulation_l2r: forall pinfo mi M1 M2 fid0 gvs1
  gvs2 oresult1 M1' mgb gl lc1 lc2 TD F rid noret0 ft 
  EC lc1' als1 als2 dck tret targs tr1
  (Hmsim: mem_simulation pinfo mgb mi ((F,lc1) :: strip_ECs EC) M1 M2)
  (Hmsim: reg_simulation pinfo mi F lc1 lc2)
  (Hpsim: List.Forall2 (fun gv1 => fun gv2 => gv_inject mi gv1 gv2) gvs1 gvs2)
  (Hcall: callExternalOrIntrinsics TD gl M1 fid0 tret targs dck
    gvs1 = ret (oresult1, tr1, M1'))
  (Hret: Opsem.exCallUpdateLocals TD ft noret0 rid oresult1 lc1 = ret lc1')
  (Hasim: als_simulation pinfo mi F lc1 als1 als2),
  exists tr2, exists M2', exists lc2', exists oresult2, exists mi',
    callExternalOrIntrinsics TD gl M2 fid0 tret targs dck
      gvs2 = ret (oresult2, tr2, M2') /\
    Opsem.exCallUpdateLocals TD ft noret0 rid oresult2 lc2 = ret lc2' /\
    tr1 = tr2 /\
    oresult1 = oresult2 /\
    mem_simulation pinfo mgb mi'
      ((F,lc1') :: strip_ECs EC) M1' M2' /\ Values.inject_incr mi mi' /\
    als_simulation pinfo mi' F lc1' als1 als2 /\
    reg_simulation pinfo mi' F lc1' lc2' /\
    (forall blk : mblock,
       ~ isnt_alloca_in_ECs pinfo (strip_ECs EC) blk ->
       mi blk = merror -> mi' blk = merror).

Lemma callExternalFunction__mem_simulation: forall pinfo mi M1 M2 fid0 gvs1
  gvs2 oresult1 M1' oresult2 M2' mgb gl lc1 lc2 TD F rid noret0 ft 
  EC lc1' lc2' als1 als2 dck tret targs tr1 tr2,
  mem_simulation pinfo mgb mi ((F,lc1) :: strip_ECs EC) M1 M2 ->
  reg_simulation pinfo mi F lc1 lc2 ->
  List.Forall2 (fun gv1 => fun gv2 => gv_inject mi gv1 gv2) gvs1 gvs2 ->
  callExternalOrIntrinsics TD gl M1 fid0 tret targs dck
    gvs1 = ret (oresult1, tr1, M1') ->
  callExternalOrIntrinsics TD gl M2 fid0 tret targs dck
    gvs2 = ret (oresult2, tr2, M2') ->
  Opsem.exCallUpdateLocals TD ft noret0 rid oresult1 lc1 = ret lc1' ->
  Opsem.exCallUpdateLocals TD ft noret0 rid oresult2 lc2 = ret lc2' ->
  als_simulation pinfo mi F lc1 als1 als2 ->
  tr1 = tr2 /\
  oresult1 = oresult2 /\
  exists mi',
    mem_simulation pinfo mgb mi'
      ((F,lc1') :: strip_ECs EC) M1' M2' /\ Values.inject_incr mi mi' /\
    als_simulation pinfo mi' F lc1' als1 als2 /\
    reg_simulation pinfo mi' F lc1' lc2' /\
    (forall blk : mblock,
       ~ isnt_alloca_in_ECs pinfo (strip_ECs EC) blk ->
       mi blk = merror -> mi' blk = merror).
Proof.
  intros.
  eapply callExternalFunction__mem_simulation_l2r in H; eauto.
  destruct H as 
    [tr2' [M2'' [lc2'' [or2' [mi'' [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 J9]]]]]]]]]]]]].
  uniq_result. 
  split; auto. split; auto. exists mi''. eauto.
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
  Hsim : State_simulation _ _ _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]];
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
      [Hfsim2 [Heq1 [Halsim2 [Hbsim2
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  assert (Heq3':=Heq3); destruct Heq3' as [l3 [ps1 [cs11 Heq3']]]; subst;
  destruct Hnoalias as [HwfECs [[Hdisjals _] HwfM]]; simpl in Hdisjals;
  assert (HwfECs0:=HwfECs);
  destruct HwfECs0 as [[Hinscope' _] [HwfECs' HwfHT]];
  fold Promotability.wf_ECStack in HwfECs'
end.

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
             |} _,
  Hnoalias : Promotability.wf_State _ _ _ _,
  Hsim : State_simulation _ _ _ _ _ ?Cfg2 ?St2 ,
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
  apply RemoveSim.cmds_simulation_nil_inv in Hcssim2; subst;
  wfCall_inv
end.

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
  | H : Opsem.GEP _ _ _ _ _ _ = Some _ |- _ => eapply simulation__GEP
  end;
  eauto using mem_simulation__wf_sb_sim;
  try solve [
    eapply conditional_used_in_fdef__used_in_cmd_value; eauto using in_middle;
      simpl; auto |
    eapply conditional_used_in_fdef__used_in_list_value; eauto using in_middle;
      simpl; auto |
    get_wf_value_for_simop; try find_wf_value_list; eauto |
    get_wf_value_for_simop'; try find_wf_value_list; eauto
    ].

Ltac dse_is_sim_common_case :=
match goal with
| Hcssim2: cmds_simulation _ ?F _ _,
  HBinF1: blockInFdefB ?B ?F = true,
  Heq3: exists _, exists _, exists _, ?B = _,
  Hop2: Opsem.sInsn _ _ _ _,
  Hmsim: mem_simulation _ _ ?mi _ _ _ |- _ =>
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  exists mi;
  repeat_solve; solve [
    apply als_simulation_update_lc; auto |
    apply reg_simulation_update_non_palloca; auto;
     reg_simulation_update_non_palloca_tac |
    eapply mem_simulation__update_non_palloca; eauto; simpl; eauto
  ]
end.

Ltac simulation__getOperandValue_tac1 :=
    eauto using mem_simulation__wf_sb_sim;
    try solve [eapply conditional_used_in_fdef__used_in_cmd_value;
                 eauto using in_middle; simpl; auto |
               get_wf_value_for_simop; eauto |
               get_wf_value_for_simop'; eauto].

Ltac simulation__getOperandValue_tac2 := try solve [
      eapply simulation__getOperandValue; simulation__getOperandValue_tac1
    ].

Lemma dae_is_sim : forall maxb pinfo mi Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo)
  (Hwfgl: genericvalues_inject.wf_globals maxb (OpsemAux.Globals Cfg1))
  (Hinbd: 0 <= maxb) (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1)
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1)
  (Hpalloca: palloca_props.wf_State pinfo St1)
  (Hsim: State_simulation pinfo maxb mi Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State pinfo St1) St1' tr1
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1),
     exists mi',
       State_simulation pinfo maxb mi' Cfg1 St1' Cfg2 St2 /\ tr1 = E0 /\
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
  apply RemoveSim.not_removable_State_inv in Hnrem.
  (sInsn_cases (destruct Hop1) SCase).

SCase "sReturn".
Focus.

  destruct_ctx_return.
  assert (PI_f pinfo <> F' \/ PI_id pinfo <> getCmdLoc (insn_call i0 n c t0 v0 v p))
    as Hneq.
    WF_PhiInfo_spec10_tac.
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2'; auto.
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result.
  eapply free_allocas_return_sim in Hmsim; eauto.
  exists mi.
  repeat_solve.
    eapply returnUpdateLocals_als_simulation; eauto.

    eapply returnUpdateLocals_reg_simulation with (lc:=lc);
      eauto using mem_simulation__wf_sb_sim;
      try solve [get_wf_value_for_simop'; eauto].
      eapply conditional_used_in_fdef__used_in_tmn_value; eauto; simpl; auto.

Unfocus.

SCase "sReturnVoid".
Focus.
  destruct_ctx_return.
  assert (PI_f pinfo <> F' \/ PI_id pinfo <> getCmdLoc (insn_call i0 n c t0 v0 v p))
    as Hneq.
    WF_PhiInfo_spec10_tac.
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2'; auto.
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
  apply RemoveSim.cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    destruct Hmsim as [_ [_ Hwf_mi]].
    eapply simulation__getOperandValue in Hlcsim2;
      try solve [get_wf_value_for_simop'; eauto 2].
      erewrite simulation__isGVZero in H1; eauto.
      clear - H22 H1 Hfsim2.
      destruct (isGVZero (los, nts) c0); 
        eapply RemoveSim.fdef_sim__block_sim; eauto.

      eapply conditional_used_in_fdef__used_in_tmn_value; eauto; simpl; auto.

  assert (Hbsim':=Hbsim).
  apply RemoveSim.block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq1 [Hpssim' [Hcssim' Heq5]]]; subst.

  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  assert (blockInFdefB (block_intro l'0 ps' cs' tmn'0) F) as HBinF1'.
    solve_blockInFdefB.
  eapply phis_simulation_inv in Hpssim'; eauto 2.
  subst.

  assert (reg_simulation pinfo mi F lc' lc'0) as Hlcsim2'.
    assert (HBinF1'':=HBinF1').
    eapply wf_system__blockInFdefB__wf_block in HBinF1''; eauto.     
    inv HBinF1''.
    eapply switchToNewBasicBlock_rsim in Hbsim2;
      eauto using mem_simulation__wf_sb_sim, conditional_used_in_fdef__used_in_phis.
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
  apply RemoveSim.cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    eapply RemoveSim.fdef_sim__block_sim; eauto.
  assert (Hbsim':=Hbsim).
  apply RemoveSim.block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq1 [Hpssim' [Hcssim' Heq5]]]; subst.

  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.
  assert (blockInFdefB (block_intro l'0 ps' cs' tmn'0) F) as HBinF1'.
    solve_blockInFdefB.
  eapply phis_simulation_inv in Hpssim'; eauto 2.
  subst.

  assert (reg_simulation pinfo mi F lc' lc'0) as Hlcsim2'.
    assert (HBinF1'':=HBinF1').
    eapply wf_system__blockInFdefB__wf_block in HBinF1''; eauto.     
    inv HBinF1''.
    eapply switchToNewBasicBlock_rsim in Hbsim2;
      eauto using mem_simulation__wf_sb_sim, conditional_used_in_fdef__used_in_phis.
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
  abstract (destruct_ctx_other;
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  eapply simulation__getOperandValue with (lc2:=lc2) in H0;
    try simulation__getOperandValue_tac1;
  eapply mem_simulation__malloc in Hmsim; eauto 2; simpl in Hmsim;
  destruct Hmsim as [mi' [Hmsim [Hinc [Hprop1 Hprop2]]]];
  exists mi';
  repeat_solve; try solve [
    eapply als_simulation__malloc; eauto | 
    eapply reg_simulation__malloc; eauto |
    eapply inject_incr__preserves__ECs_simulation; 
      try solve [eauto | eapply malloc__isnt_alloca_in_ECs; eauto] |
    eapply OpsemAux.inject_incr__preserves__ftable_simulation; eauto
  ]).

SCase "sFree".
  abstract (destruct_ctx_other;
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  eapply simulation__getOperandValue with (lc2:=lc2) in H;
    try simulation__getOperandValue_tac1;
  eapply mem_simulation__free in Hmsim; eauto 2;
  exists mi;
  repeat_solve).

SCase "sAlloca".
  abstract (destruct_ctx_other;
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  eapply simulation__getOperandValue with (lc2:=lc2) in H0;
    try simulation__getOperandValue_tac1;
  eapply mem_simulation__malloc in Hmsim; eauto 2; simpl in Hmsim;
  destruct Hmsim as [mi' [Hmsim [Hinc [Hprop1 Hprop2]]]];
  exists mi';
  repeat_solve; try solve [
    eapply als_simulation__alloca; eauto | 
    eapply reg_simulation__malloc; eauto |
    eapply inject_incr__preserves__ECs_simulation; 
      try solve [eauto | eapply malloc__isnt_alloca_in_ECs; eauto] |
    eapply OpsemAux.inject_incr__preserves__ftable_simulation; eauto
  ]).

SCase "sLoad".
  abstract (destruct_ctx_other;
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  exists mi;
  repeat_solve; try solve [
    apply als_simulation_update_lc; auto |
    apply reg_simulation_update_non_palloca; try solve [
      auto |
      eapply simulation__mload; try solve [
        eauto 2 using mem_simulation__wf_sb_sim |
        simulation__getOperandValue_tac2
      ]
    ] |
    eapply mem_simulation__update_non_palloca; eauto; simpl; eauto
  ]).

SCase "sStore".
  abstract (destruct_ctx_other;
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  exists mi;
  repeat_solve; try solve [
    simpl; eapply simulation__mstore; try solve [
      eauto 2 using mem_simulation__wf_sb_sim |
      eapply simulation__getOperandValue; eauto using mem_simulation__wf_sb_sim;
        try solve [eapply conditional_used_in_fdef__used_in_cmd_value;
                     eauto using in_middle; simpl; auto |
                   get_wf_value_for_simop; eauto]
    ]
  ]).

SCase "sGEP". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sTrunc". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExt". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sCast". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sIcmp". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFcmp". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sSelect".
  destruct_ctx_other.
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
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
        try solve [eapply conditional_used_in_fdef__used_in_cmd_value;
                     eauto using in_middle; simpl; auto|
                   get_wf_value_for_simop; eauto]
      ].
    destruct (isGVZero (los,nts) c);
      eapply mem_simulation__update_non_palloca; eauto; simpl; eauto.

SCase "sCall".
  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.
  inv Hop2; uniq_result.
  SSCase "SCall".

  assert (gv_inject mi fptr fptr0) as Hfptr_sim.
    assert (exists t, wf_value S (module_intro los nts Ps) F fv t) as G.
      assert (HBinF1':=HBinF1).
      eapply wf_system__wf_cmd in HBinF1'; eauto using in_middle.     
      inv HBinF1'. eauto.
    destruct G.
    simulation__getOperandValue_tac2.

  assert (Hfsim1:=Hpsim).
  eapply TopSim.lookupFdefViaPtr_inj__simulation in Hfsim1; eauto. 
  simpl in Hfsim1.
  assert (Hbsim1:=Hfsim1).
  eapply RemoveSim.fdef_simulation__entry_block_simulation in Hbsim1; eauto.
  assert (Hbsim1':=Hbsim1).
  apply RemoveSim.block_simulation_inv in Hbsim1'.
  destruct Hbsim1' as [Heq' [Hpsim1' [Hcsim1' Htsim1']]]; subst.
  exists mi.
    match goal with
    | H1: OpsemAux.lookupFdefViaPtr _ _ _ = Some ?F,
      _ : fdef_simulation _ ?F _ |- _ =>
      apply OpsemAux.lookupFdefViaPtr_inv in H1;
      eapply wf_system__uniqFdef in H1; eauto 2
    end.
  repeat_solve.
    exists l'0. exists ps'. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    apply RemoveSim.fdef_simulation_inv in Hfsim1.
    destruct Hfsim1 as [Hfhsim1 Hbssim1].
    inv Hfhsim1.
    assert (HBinF1':=HBinF1).
    eapply wf_system__wf_cmd in HBinF1'; eauto using in_middle.     
    inv HBinF1'.
    find_wf_value_list.  
    eapply reg_simulation__initLocals; try solve [
      eauto 2 using mem_simulation__wf_sb_sim, WF_PhiInfo__args_dont_use_pid |
      eapply conditional_used_in_fdef__used_in_params; eauto 1
    ].

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

  assert (gv_inject mi fptr fptr0) as Hfptr_sim.
    assert (exists t, wf_value S (module_intro los nts Ps) F fv t) as G.
      assert (HBinF1':=HBinF1).
      eapply wf_system__wf_cmd in HBinF1'; eauto using in_middle.     
      inv HBinF1'. eauto.
    destruct G.
    simulation__getOperandValue_tac2.

  eapply TopSim.lookupFdefViaPtr_inj__simulation_l2r in H1; eauto.
  uniq_result.

SCase "sExCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply RemoveSim.cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.
  inv Hop2; uniq_result.

  SSCase "SCall".

  assert (gv_inject mi fptr fptr0) as Hfptr_sim.
    assert (exists t, wf_value S (module_intro los nts Ps) F fv t) as G.
      assert (HBinF1':=HBinF1).
      eapply wf_system__wf_cmd in HBinF1'; eauto using in_middle.     
      inv HBinF1'. eauto.
    destruct G.
    simulation__getOperandValue_tac2.

  eapply TopSim.lookupFdefViaPtr_inj__simulation_r2l in H1; eauto.
  uniq_result.

  SSCase "sExCall".

  assert (gv_inject mi fptr fptr0) as Hfptr_sim.
    assert (exists t, wf_value S (module_intro los nts Ps) F fv t) as G.
      assert (HBinF1':=HBinF1).
      eapply wf_system__wf_cmd in HBinF1'; eauto using in_middle.     
      inv HBinF1'. eauto.
    destruct G.
    simulation__getOperandValue_tac2.

  eapply TopSim.lookupExFdecViaPtr_inj__simulation in Hfptr_sim; eauto.
  uniq_result.

  assert (List.Forall2 (fun gv1 => fun gv2 => gv_inject mi gv1 gv2) gvss gvss0)
    as Hparsim.
    assert (HBinF1':=HBinF1).
    eapply wf_system__wf_cmd in HBinF1'; eauto using in_middle.     
    inv HBinF1'.
    find_wf_value_list.  
    eapply reg_simulation__params2GVs; try solve [
      eauto 2 using mem_simulation__wf_sb_sim |
      eapply conditional_used_in_fdef__used_in_params; eauto 1
    ].
  eapply callExternalFunction__mem_simulation in Hmsim; eauto.
  destruct Hmsim as [EQ' [EQ [mi' [Hmsim [Hinc [J1 [J2 J3]]]]]]]; subst.
  exists mi'.
  repeat_solve.
    eapply inject_incr__preserves__ECs_simulation; eauto.
    eapply OpsemAux.inject_incr__preserves__ftable_simulation; eauto.

Transparent inscope_of_tmn inscope_of_cmd.

Qed.
