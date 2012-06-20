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
  assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true)
    as HBinF.
    rewrite Heq. simpl. apply InBlocksB_middle.
  assert (wf_fdef [module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)]
            (module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)) 
            (PI_f pinfo) /\ uniqFdef (PI_f pinfo)) as J.
    rewrite Heq in *. subst.
    apply wf_single_system__wf_uniq_fdef; auto.
  destruct J as [HwfF HuniqF].
  eapply find_st_ld__laainfo in HBinF; eauto.
  destruct HBinF as [EQ [laainfo [J1 J2]]]; subst.
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
    eapply laa_wfS; eauto.
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
