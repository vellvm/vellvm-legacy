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
Require Import alive_alloca.
Require Import subst_inv.
Require Import vmem2reg.
Require Import program_sim.
Require Import memory_props.
Require Import trans_tactic.
Require Import top_sim.
Require Import laa.
Require Import laa_wfS.
Require Import subst_sim.
Require Import die_wfS.
Require Import die_top.

Lemma vev_State_preservation : forall pinfo laainfo cfg IS maxb
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg))
  (Halias: Promotability.wf_State maxb pinfo cfg IS) (Hwfpi: WF_PhiInfo pinfo)
  alinfo Hp (Hlas2st : exist _ alinfo Hp = laainfo__alinfo pinfo laainfo)
  (Halst: alive_alloca.wf_State pinfo alinfo cfg IS)
  (Hwfcfg : OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg IS) 
  (Hvev: vev_State (value_id (LAA_lid pinfo laainfo))
               [! pinfo !] (PI_f pinfo) cfg IS)
  IS' tr  (Hstep: Opsem.sInsn cfg IS IS' tr),
  vev_State (value_id (LAA_lid pinfo laainfo))
               [! pinfo !] (PI_f pinfo) cfg IS'.
Proof.
  intros.
  eapply laa__alive_alloca__vev; eauto.
    apply OpsemPP.preservation in Hstep; auto.
    eapply alive_alloca.preservation in Hstep; eauto.
Qed.

Lemma LAA_value__dominates__LAA_lid: forall pinfo lasinfo,
  valueDominates (PI_f pinfo) [! pinfo !] (value_id (LAA_lid pinfo lasinfo)).
Proof. simpl. auto. Qed.

Lemma LAA_substable_values : forall td gl pinfo laainfo
  (Huniq: uniqFdef (PI_f pinfo)), 
  substable_values td gl (PI_f pinfo) (value_id (LAA_lid pinfo laainfo))
    [! pinfo !].
Proof.
  intros.
  split.
    simpl. rewrite lookup_LAA_lid__load; simpl; auto.
  split. unfold substing_value. auto.
  split; auto. 
   apply LAA_value__dominates__LAA_lid.
Qed.

Lemma laa_sim': forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (v : value)
  (cs : cmds)  (i1 : id) (Heqv: v = [! pinfo !]) (laainfo:LAAInfo pinfo)
  (Heqi1: LAA_lid pinfo laainfo = i1) 
  (Heqb: LAA_block pinfo laainfo = (block_intro l0 ps0 cs0 tmn0))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  S2 (Heq2: S2=[module_intro los nts
                (Ps1 ++
                  product_fdef
                    (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
                 :: Ps2)])
  (Hok: defined_program S2 main VarArgs)
  (HwfS : wf_system S2),
  program_sim
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))
         :: Ps2)]
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
      (exist _ stinfo Hp = laainfo__alinfo pinfo laainfo) /\
      (alive_alloca.wf_State pinfo stinfo cfg IS) /\
      (substable_values (OpsemAux.CurTargetData cfg) (OpsemAux.Globals cfg)
         (PI_f pinfo) (value_id (LAA_lid pinfo laainfo)) [! pinfo !]) /\ 
      (vev_State (value_id (LAA_lid pinfo laainfo)) [! pinfo !]
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
      eapply alive_alloca.preservation; eauto.
      eapply vev_State_preservation; eauto.
  Case "3". 
    intros.
    rewrite <- Heq in *.  
    eapply subst_inv.s_genInitState__wf_State; eauto.
      destruct cfg. simpl.
      eapply LAA_substable_values; eauto.
  Case "4". 
    intros. subst.
    eapply laa_wfS'; eauto.
  Case "5". 
    intros.
    rewrite <- Heq in *.  
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg IS) as Hwfst';
      try solve [eapply s_genInitState__opsem_wf in H; eauto using laa_wfS].
    assert (substable_values (OpsemAux.CurTargetData cfg) (OpsemAux.Globals cfg)
      (PI_f pinfo) (value_id (LAA_lid pinfo laainfo)) [! pinfo !]) 
      as Hdom.
      destruct cfg. simpl.
      eapply LAA_substable_values; eauto.
    assert (exists maxb,
              MemProps.wf_globals maxb (OpsemAux.Globals cfg) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg IS) as Hprom;
      try solve [eapply Promotability.s_genInitState__wf_globals_promotable; eauto].
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]].
    remember (laainfo__alinfo pinfo laainfo) as R.
    destruct R as [stinfo Hp].
    assert (alive_alloca.wf_State pinfo stinfo cfg IS) as Halst;
      try solve [eapply s_genInitState__alive_alloca; eauto].
    exists maxb. exists stinfo. exists Hp.
    repeat (split; auto).
      eapply laa__alive_alloca__vev; eauto; try tauto.
Qed.

Lemma laa_sim: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (v : value)
  (cs : cmds)
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  S2 (Heq2: S2=[module_intro los nts
                (Ps1 ++
                  product_fdef
                    (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
                 :: Ps2)])
  (Hok: defined_program S2 main VarArgs)
  (HwfS : wf_system S2),
  program_sim
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))
         :: Ps2)]
     S2 main VarArgs.
Proof.
  intros. subst.
  assert (J:=Hst). eapply laa_wf_init in J; eauto 1.
  destruct J as [HwfF [HuniqF [EQ [laainfo [J1 J2]]]]]; subst.
  eapply laa_sim'; eauto.
Qed.

Lemma laa_die_sim_wfS': forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (v : value)
  (cs : cmds) (i1 : id) (Heqv: v = [! pinfo !]) (laainfo:LAAInfo pinfo)
  (Heqi1: LAA_lid pinfo laainfo = i1) 
  (Heqb: LAA_block pinfo laainfo = (block_intro l0 ps0 cs0 tmn0))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  S1 S2
  (Heq1: S1 = 
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
            (List.map (remove_block i1)
               (List.map (subst_block i1 v)
                  (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))) :: Ps2)])
  (Heq2: S2 =
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)])
  (HwfS: wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\ 
    defined_program S1 main VarArgs.
Proof.
  intros.
  assert ((fdef_intro fh
           (List.map (remove_block i1)
             (List.map (subst_block i1 v)
               (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))) =
          remove_fdef i1
            (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))))
    as J.
    simpl. auto.
  subst S2 S1. rewrite J.
  assert (J':=HwfS). apply wf_single_system__wf_uniq_fdef in J'; auto.
  destruct J' as [HwfF HuniqF]. rewrite <- Heq in HuniqF, HwfF.
  assert (Hdiinfo:=HuniqF).
  eapply laa_diinfo' in Hdiinfo; eauto.
  destruct Hdiinfo as [diinfo [J1 J2]]. rewrite Heq in J1.
  apply program_sim_wfS_trans with (P2:=
      [module_intro los nts
          (Ps1 ++
           product_fdef
             (subst_fdef i1 v
                (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) ::
           Ps2)]); auto; intros.
    split.
      eapply die_sim; eauto.
    split.
      eapply die_wfS; eauto.
      eapply program_sim__preserves__defined_program; eauto using die_sim.

    split.
      eapply laa_sim'; eauto.
    split.
      eapply laa_wfS'; eauto.
      eapply program_sim__preserves__defined_program; eauto using laa_sim'.
Qed.

Lemma laa_die_sim_wfS: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (v : value)
  (cs : cmds)
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  S1 S2
  (Heq1: S1 = 
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
            (List.map (remove_block i1)
               (List.map (subst_block i1 v)
                  (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))) :: Ps2)])
  (Heq2: S2 =
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)])
  (HwfS: wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\ 
    defined_program S1 main VarArgs.
Proof.
  intros. subst.
  assert (J:=Hst). eapply laa_wf_init in J; eauto 1.
  destruct J as [HwfF [HuniqF [EQ [laainfo [J1 J2]]]]]; subst.
  eapply laa_die_sim_wfS'; eauto.
Qed.
