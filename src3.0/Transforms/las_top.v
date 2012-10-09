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
Require Import alive_store.
Require Import subst_inv.
Require Import vmem2reg.
Require Import program_sim.
Require Import memory_props.
Require Import trans_tactic.
Require Import top_sim.
Require Import las.
Require Import las_wfS.
Require Import subst_sim.
Require Import die_wfS.
Require Import die_top.

(* LAS's vev_State invariant is preserved. *)
Lemma vev_State_preservation : forall pinfo lasinfo cfg IS maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg))
  (Halias: Promotability.wf_State maxb pinfo cfg IS) (Hwfpi: WF_PhiInfo pinfo)
  stinfo Hp (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo)
  (Halst: alive_store.wf_State pinfo stinfo cfg IS)
  (Hwfcfg : OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg IS) 
  (Hvev: vev_State (value_id (LAS_lid pinfo lasinfo))
               (LAS_value pinfo lasinfo) (PI_f pinfo) cfg IS)
  IS' tr  (Hstep: Opsem.sInsn cfg IS IS' tr),
  vev_State (value_id (LAS_lid pinfo lasinfo))
               (LAS_value pinfo lasinfo) (PI_f pinfo) cfg IS'.
Proof.
  intros.
  eapply las__alive_store__vev; eauto.
    apply OpsemPP.preservation in Hstep; auto.
    eapply alive_store.preservation in Hstep; eauto.
Qed.

(* LAS refines programs. *)
Lemma las_sim': forall (los : layouts) (nts : namedts) (fh : fheader)
  (pinfo: PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo)
  (i1 : id) (lasinfo : LASInfo pinfo)
  (Heqi1: LAS_lid pinfo lasinfo = i1) (Heqv: LAS_value pinfo lasinfo = v)
  (Heqb: LAS_block pinfo lasinfo = (l0, stmts_intro ps0 cs0 tmn0))
  S2 (Heq2: S2=[module_intro los nts
                (Ps1 ++
                  product_fdef
                    (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
                  :: Ps2)])
  (Hok: defined_program S2 main VarArgs)
  (HwfS : wf_system S2)
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (subst_fdef i1 v
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))) :: Ps2)]
    S2 main VarArgs.
Proof.
  intros. subst.
  assert (J:=HwfS). apply wf_single_system__wf_uniq_fdef in J; auto.
  destruct J as [HwfF HuniqF]. rewrite <- Heq in HuniqF, HwfF.
  set (ctx_inv := fun cfg IS =>
    exists maxb, exists stinfo, exists Hp, 
      0 <= maxb /\
      MemProps.wf_globals maxb (OpsemAux.Globals cfg) /\
      Promotability.wf_State maxb pinfo cfg IS /\ WF_PhiInfo pinfo /\
      (exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo) /\
      (alive_store.wf_State pinfo stinfo cfg IS) /\
      (substable_values (OpsemAux.CurTargetData cfg) (OpsemAux.Globals cfg)
         (PI_f pinfo) (value_id (LAS_lid pinfo lasinfo)) 
         (LAS_value pinfo lasinfo)) /\ 
      (vev_State (value_id (LAS_lid pinfo lasinfo)) (LAS_value pinfo lasinfo) 
         (PI_f pinfo) cfg IS)).
  apply SubstSim.sim with (ctx_inv:=ctx_inv); auto.
  Case "1".
    intros. 
    rewrite <- Heq in *. 
    destruct Hp as [maxb [stinfo [Hp [G1 [G2 [G3 [G4 [G5 [G6 [G7 G8]]]]]]]]]].
    eapply subst_inv.preservation; eauto.
  Case "2".  
    intros.
    destruct H2 as [maxb [stinfo [Hp [G1 [G2 [G3 [G4 [G5 [G6 [G7 G8]]]]]]]]]].
    exists maxb. exists stinfo. exists Hp. 
    repeat (split; auto).
      eapply Promotability.preservation; eauto.
      eapply alive_store.preservation; eauto.
      eapply vev_State_preservation; eauto.
  Case "3".  
    intros.
    rewrite <- Heq in *.  
    eapply subst_inv.s_genInitState__wf_State; eauto.
      destruct cfg. simpl.
      eapply LAS_substable_values; eauto.
  Case "4".  
    intros. subst.
    eapply las_wfS'; eauto.
  Case "5".  
    intros.
    rewrite <- Heq in *.  
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg IS) as Hwfst';
      try solve [eapply s_genInitState__opsem_wf in H; eauto using las_wfS].
    assert (substable_values (OpsemAux.CurTargetData cfg) (OpsemAux.Globals cfg)
      (PI_f pinfo) (value_id (LAS_lid pinfo lasinfo)) (LAS_value pinfo lasinfo)) 
      as Hdom.
      destruct cfg. simpl.
      eapply LAS_substable_values; eauto.
    assert (exists maxb,
              MemProps.wf_globals maxb (OpsemAux.Globals cfg) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg IS) as Hprom;
      try solve [eapply Promotability.s_genInitState__wf_globals_promotable; eauto].
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]].
    remember (lasinfo__stinfo pinfo lasinfo) as R.
    destruct R as [stinfo Hp].
    assert (alive_store.wf_State pinfo stinfo cfg IS) as Halst;
      try solve [eapply s_genInitState__alive_store; eauto].
    exists maxb. exists stinfo. exists Hp.
    repeat (split; auto).
      eapply las__alive_store__vev; eauto; try tauto.
Qed.

Lemma las_sim: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo)
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  S2 (Heq2: S2=[module_intro los nts
                (Ps1 ++
                  product_fdef
                    (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
                  :: Ps2)])
  (Hok: defined_program S2 main VarArgs)
  (HwfS : wf_system S2)
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (subst_fdef i1 v
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))) :: Ps2)]
    S2 main VarArgs.
Proof.
  intros. subst.
  assert (J:=Hst). eapply las_wf_init in J; eauto 1.
  destruct J as [HwfF [HuniqF [lasinfo [J1 [J2 [J3 J4]]]]]]; subst.
  eapply las_sim'; eauto.
Qed.

(* LAS + deletion refines programs and preserves well-formedness. *)
Lemma las_die_sim_wfS': forall (los : layouts) (nts : namedts) (fh : fheader)
  (pinfo: PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) (Hreach:  In l0 (PI_rd pinfo))
  (i1 : id) (lasinfo : LASInfo pinfo)
  (Heqi1: LAS_lid pinfo lasinfo = i1) (Heqv: LAS_value pinfo lasinfo = v)
  (Heqb: LAS_block pinfo lasinfo = (l0, stmts_intro ps0 cs0 tmn0))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Hwfpi: WF_PhiInfo pinfo) S1 S2
  (Heq1: S1 = 
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
           (List.map (remove_block i1)
             (List.map (subst_block i1 v)
               (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)))) :: Ps2)])
  (Heq2: S2 = 
    [module_intro los nts
      (Ps1 ++
       product_fdef (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))::
       Ps2)])
  (HwfS: wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\ 
    defined_program S1 main VarArgs.
Proof.
  intros.
  assert ((fdef_intro fh
           (List.map (remove_block i1)
             (List.map (subst_block i1 v)
               (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)))) =
          remove_fdef i1
            (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))))
    as J.
    simpl. auto.
  subst S2 S1. rewrite J.
  assert (J':=HwfS). apply wf_single_system__wf_uniq_fdef in J'; auto.
  destruct J' as [HwfF HuniqF]. rewrite <- Heq in HuniqF, HwfF.
  assert (Hdiinfo:=HwfF).
  eapply las_diinfo' in Hdiinfo; eauto.
  destruct Hdiinfo as [diinfo [J1 J2]]. rewrite Heq in J1.
  apply program_sim_wfS_trans with (P2:=
      [module_intro los nts
          (Ps1 ++
           product_fdef
             (subst_fdef i1 v
                (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))) ::
           Ps2)]); auto; intros.
    split.
      eapply die_sim; eauto.
    split.
      eapply die_wfS; eauto.
      eapply program_sim__preserves__defined_program; eauto using die_sim.
      
    split.
      eapply las_sim'; eauto.
    split.
      eapply las_wfS'; eauto.
      eapply program_sim__preserves__defined_program; eauto using las_sim'.
Qed.

Lemma las_die_sim_wfS: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) (Hreach:  In l0 (PI_rd pinfo))
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Hwfpi: WF_PhiInfo pinfo) S1 S2
  (Heq1: S1 = 
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
           (List.map (remove_block i1)
             (List.map (subst_block i1 v)
               (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)))) :: Ps2)])
  (Heq2: S2 = 
    [module_intro los nts
      (Ps1 ++
       product_fdef (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))::
       Ps2)])
  (HwfS: wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\ 
    defined_program S1 main VarArgs.
Proof.
  intros. subst.
  eapply las_wf_init in Hst; eauto 1.
  destruct Hst as [HwfF [HuniqF [lasinfo [J1 [J2 [J3 J4]]]]]]; subst.
  eapply las_die_sim_wfS'; eauto.
Qed.
