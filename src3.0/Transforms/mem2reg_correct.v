Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import opsem_props.
Require Import program_sim.
Require Import promotable_props.
Require Import primitives.
Require Import palloca_props.
Require Import mem2reg.
Require Import memory_props.
Require Import program_sim.
Require Import subst.
Require Import las_wfS.
Require Import las_top.
Require Import laa_wfS.
Require Import laa_top.
Require Import dae_wfS.
Require Import dae_top.
Require Import dse_wfS.
Require Import dse_top.
Require Import die.
Require Import sas_top.
Require Import sas_wfS.
Require Import phiplacement_bsim_wfS.
Require Import phiplacement_bsim_top.

(* We are proving the macro-based m2r pass *)
Parameter does_macro_m2r_is_true: mem2reg.does_macro_m2r tt = true.

Parameter print_reachablity_is_true: forall rd, print_reachablity rd = true.

Parameter does_phi_elim_is_true: does_phi_elim tt = true.

Parameter does_stld_elim_is_true: does_stld_elim tt = true.

Lemma program_sim_wfS_trans: forall (P1 P2 P3 : system) (main : id)
  (VarArgs : list (GVsT DGVs)) (HwfS: wf_system P3) 
  (Hok: defined_program P3 main VarArgs),
  (wf_system P2 -> 
   defined_program P2 main VarArgs ->
   program_sim P1 P2 main VarArgs /\ wf_system P1 /\ 
   defined_program P1 main VarArgs) ->
  (wf_system P3 -> 
   defined_program P3 main VarArgs ->
   program_sim P2 P3 main VarArgs /\ wf_system P2 /\
   defined_program P2 main VarArgs) ->
  program_sim P1 P3 main VarArgs /\ wf_system P1 /\
  defined_program P1 main VarArgs.
Proof.
  intros.
  destruct H0 as [Hsim2 [Hwf2 Hok2]]; auto.
  destruct H as [Hsim1 [Hwf1 Hok1]]; auto.
  split; auto.
  eapply program_sim_trans; eauto.
Qed.

Lemma las_die_wfPI: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds)
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
  WF_PhiInfo (update_pinfo pinfo
         (fdef_intro fh
           (List.map (remove_block i1)
             (List.map (subst_block i1 v)
               (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))))).
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
  rewrite J.
  destruct (@subst_fdef__diinfo
    (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) i1 v) as
    [diinfo [J1 J2]].
  change
    (update_pinfo pinfo
      (remove_fdef i1
        (subst_fdef i1 v
          (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))))) with
    (update_pinfo
      (update_pinfo pinfo
        (subst_fdef i1 v
          (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))))
      (remove_fdef i1
        (subst_fdef i1 v
          (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))))).
  eapply die_wfPI; eauto.
    eapply las_wfPI; eauto.
    eapply las_wfS; eauto.
Qed.

Lemma las_die_sim_wfS: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds)
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo) S1 S2
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
       product_fdef (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))::
       Ps2)])
  (HwfS: wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\ 
    defined_program S1 main VarArgs.
Proof.
  intros. subst.
  assert ((fdef_intro fh
           (List.map (remove_block i1)
             (List.map (subst_block i1 v)
               (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))) =
          remove_fdef i1
            (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))))
    as J.
    simpl. auto.
  rewrite J.
  destruct (@subst_fdef__diinfo
    (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) i1 v) as
    [diinfo [J1 J2]].
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
      eapply las_sim; eauto.
    split.
      eapply las_wfS; eauto.
      eapply program_sim__preserves__defined_program; eauto using las_sim.
Qed.

Lemma laa_die_wfPI: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (v : value)
  (cs : cmds)
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
  WF_PhiInfo (update_pinfo pinfo
    (fdef_intro fh
      (List.map (remove_block i1)
        (List.map (subst_block i1 v)
          (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))))).
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
  rewrite J.
  destruct (@subst_fdef__diinfo
    (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) i1 v) as
    [diinfo [J1 J2]].
  change
    (update_pinfo pinfo
      (remove_fdef i1
        (subst_fdef i1 v
          (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))))) with
    (update_pinfo
      (update_pinfo pinfo
        (subst_fdef i1 v
          (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))))
      (remove_fdef i1
        (subst_fdef i1 v
          (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))))).
  eapply die_wfPI; eauto.
    eapply laa_wfPI; eauto.
    eapply laa_wfS; eauto.
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
  assert ((fdef_intro fh
           (List.map (remove_block i1)
             (List.map (subst_block i1 v)
               (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))) =
          remove_fdef i1
            (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))))
    as J.
    simpl. auto.
  rewrite J.
  destruct (@subst_fdef__diinfo
    (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) i1 v) as
    [diinfo [J1 J2]].
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
      eapply laa_sim; eauto.
    split.
      eapply laa_wfS; eauto.
      eapply program_sim__preserves__defined_program; eauto using laa_sim.
Qed.

Lemma remove_subst_reachablity_successors : forall i2 i1 v1 f,
  reachablity_analysis f =
    reachablity_analysis (remove_fdef i2 (subst_fdef i1 v1 f)) /\
  successors f = successors (remove_fdef i2 (subst_fdef i1 v1 f)).
Proof.
  split.
    transitivity (reachablity_analysis (subst_fdef i1 v1 f)).
      apply subst_reachablity_analysis.
      apply remove_reachablity_analysis.

    transitivity (successors (subst_fdef i1 v1 f)).
      apply subst_successors.
      apply remove_successors.
Qed.

Lemma elim_stld_cmds_reachablity_successors: forall f cs0 f0
  dones0 dones id0 (Hpass : (f0, true, dones0) = elim_stld_cmds f cs0 id0 dones),
  reachablity_analysis f = reachablity_analysis f0 /\
  successors f = successors f0.
Proof.
  intros.
  unfold elim_stld_cmds in Hpass.
  remember (find_init_stld cs0 id0 dones) as R1.
  destruct R1 as [[[[]]|[]]|]; tinv Hpass.
    remember (find_next_stld c id0) as R2.
    destruct R2 as [[|[]]|]; inv Hpass.
      apply remove_subst_reachablity_successors.
      split.
        apply remove_reachablity_analysis.
        apply remove_successors.
      split; auto.

    remember (find_next_stld c id0) as R2.
    destruct R2 as [[|[]]|]; inv Hpass.
      apply remove_subst_reachablity_successors.
      split; auto.
      split; auto.
Qed.

Lemma elim_stld_cmds_wfPI: forall los nts fh dones (pinfo:PhiInfo) f0 dones0
  bs1 l0 ps0 cs0 tmn0 bs2 Ps1 Ps2
  (Hpass : (f0, true, dones0) =
           elim_stld_cmds
             (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) cs0
             (PI_id pinfo) dones)
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
  WF_PhiInfo (update_pinfo pinfo f0).
Proof.
  intros.
  unfold elim_stld_cmds in Hpass.
  remember (find_init_stld cs0 (PI_id pinfo) dones) as R1.
  destruct R1 as [[[[]]|[]]|]; tinv Hpass.
    remember (find_next_stld c (PI_id pinfo)) as R2.
    destruct R2 as [[|[]]|]; inv Hpass.
      eapply las_die_wfPI; eauto.
      eapply sas_wfPI; eauto.
      rewrite <- Heq. rewrite update_pinfo_eq; auto.

    remember (find_next_stld c (PI_id pinfo)) as R2.
    destruct R2 as [[|[]]|]; inv Hpass.
      eapply laa_die_wfPI; eauto.
      rewrite <- Heq. rewrite update_pinfo_eq; auto.
      rewrite <- Heq. rewrite update_pinfo_eq; auto.
Qed.

Lemma elim_stld_cmds_sim_wfS: forall los nts fh dones (pinfo:PhiInfo) f0 dones0
  main VarArgs bs1 l0 ps0 cs0 tmn0 bs2 Ps1 Ps2
  (Hpass : (f0, true, dones0) =
           elim_stld_cmds
             (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) cs0
             (PI_id pinfo) dones)
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f0 :: Ps2)])
  (Heq1: S2 = 
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.
Proof.
  intros. subst.
  unfold elim_stld_cmds in Hpass.
  remember (find_init_stld cs0 (PI_id pinfo) dones) as R1.
  destruct R1 as [[[[]]|[]]|]; tinv Hpass.
    remember (find_next_stld c (PI_id pinfo)) as R2.
    destruct R2 as [[|[]]|]; inv Hpass.
      eapply las_die_sim_wfS; eauto.
      split.
        eapply sas_sim; eauto.
      split.
        eapply sas_wfS; eauto.
        eapply program_sim__preserves__defined_program; eauto using sas_sim.    
      split; auto using program_sim_refl.

    remember (find_next_stld c (PI_id pinfo)) as R2.
    destruct R2 as [[|[]]|]; inv Hpass.
      eapply laa_die_sim_wfS; eauto.
      split; auto using program_sim_refl.
      split; auto using program_sim_refl.
Qed.

Lemma elim_stld_blocks_reachablity_successors_aux: forall f0 dones0 dones id0
  flag fh bs2 bs1
  (Hpass:elim_stld_blocks (fdef_intro fh (bs1++bs2)) bs2 id0 dones =
    (f0, flag, dones0)),
  reachablity_analysis (fdef_intro fh (bs1++bs2)) =
    reachablity_analysis f0 /\
  successors (fdef_intro fh (bs1++bs2)) = successors f0.
Proof.
  induction bs2; simpl; intros.
    inv Hpass. auto.

    destruct a as [l0 ps0 cs0 tmn0].
    remember
      (elim_stld_cmds
        (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          cs0 id0 dones) as R.
    destruct R as [[f' []] dones']; inv Hpass; auto.
      eapply elim_stld_cmds_reachablity_successors; eauto.

      apply elim_stld_cmds_unchanged in HeqR. subst.
      rewrite_env ((bs1 ++ [block_intro l0 ps0 cs0 tmn0]) ++ bs2) in H0.
      apply IHbs2 in H0; simpl_env in *; auto.
Qed.

Lemma elim_stld_blocks_wfPI_aux: forall los nts fh dones (pinfo:PhiInfo) f0
  dones0 Ps1 Ps2 flag bs2 bs1
  (Hpass:elim_stld_blocks (fdef_intro fh (bs1++bs2)) bs2 (PI_id pinfo) dones =
    (f0, flag, dones0))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ bs2)) :: Ps2)]),
  WF_PhiInfo (update_pinfo pinfo f0).
Proof.
  induction bs2; simpl; intros.
    inv Hpass.
    rewrite <- Heq. rewrite update_pinfo_eq; auto.

    destruct a as [l0 ps0 cs0 tmn0].
    remember
      (elim_stld_cmds
        (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          cs0 (PI_id pinfo) dones) as R.
    destruct R as [[f' []] dones']; inv Hpass; auto.
      eapply elim_stld_cmds_wfPI; eauto.

      apply elim_stld_cmds_unchanged in HeqR. subst.
      rewrite_env ((bs1 ++ [block_intro l0 ps0 cs0 tmn0]) ++ bs2) in H0.
      apply IHbs2 in H0; simpl_env in *; auto.
Qed.

Lemma elim_stld_blocks_sim_wfS_aux: forall los nts fh dones (pinfo:PhiInfo) f0
  dones0 main VarArgs Ps1 Ps2 flag bs2 bs1
  (Hpass:elim_stld_blocks (fdef_intro fh (bs1++bs2)) bs2 (PI_id pinfo) dones =
    (f0, flag, dones0))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ bs2))
  (Hwfpi: WF_PhiInfo pinfo) S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++  product_fdef f0 :: Ps2)])
  (heq2: S2 = [module_intro los nts
      (Ps1 ++ product_fdef (fdef_intro fh (bs1++bs2)) :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.
Proof.
  induction bs2; simpl; subst; intros.
    inv Hpass; split; auto using program_sim_refl.

    destruct a as [l0 ps0 cs0 tmn0].
    remember
      (elim_stld_cmds
        (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          cs0 (PI_id pinfo) dones) as R.
    destruct R as [[f' []] dones']; inv Hpass; auto.
      eapply elim_stld_cmds_sim_wfS; eauto.

      apply elim_stld_cmds_unchanged in HeqR. subst.
      rewrite_env ((bs1 ++ [block_intro l0 ps0 cs0 tmn0]) ++ bs2) in H0.
      eapply IHbs2 in H0; simpl_env in *; eauto.
Qed.

Lemma elim_stld_blocks_reachablity_successors: forall f0 dones0 dones id0
  flag fh bs
  (Hpass:elim_stld_blocks (fdef_intro fh bs) bs id0 dones =
    (f0, flag, dones0)),
  reachablity_analysis (fdef_intro fh bs) =
    reachablity_analysis f0 /\
  successors (fdef_intro fh bs) = successors f0.
Proof.
  intros.
  rewrite_env (nil ++ bs).
  eapply elim_stld_blocks_reachablity_successors_aux; eauto.
Qed.

Lemma elim_stld_blocks_wfPI: forall los nts fh dones (pinfo:PhiInfo) f0 dones0
  Ps1 Ps2 flag bs
  (Hpass:elim_stld_blocks (fdef_intro fh bs) bs (PI_id pinfo) dones
           = (f0, flag, dones0))
  (Heq: PI_f pinfo = fdef_intro fh bs)
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system
       [module_intro los nts
         (Ps1 ++ product_fdef (fdef_intro fh bs) :: Ps2)]),
  WF_PhiInfo (update_pinfo pinfo f0).
Proof.
  intros.
  rewrite_env (nil ++ bs) in HwfS.
  eapply elim_stld_blocks_wfPI_aux; eauto; simpl; eauto.
Qed.

Lemma elim_stld_blocks_sim_wfS: forall los nts fh dones (pinfo:PhiInfo) f0 dones0
  main VarArgs Ps1 Ps2 flag bs
  (Hpass:elim_stld_blocks (fdef_intro fh bs) bs (PI_id pinfo) dones
           = (f0, flag, dones0))
  (Heq: PI_f pinfo = fdef_intro fh bs)
  (Hwfpi: WF_PhiInfo pinfo) S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++  product_fdef f0 :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef (fdef_intro fh bs) :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs), 
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\ defined_program S1 main VarArgs.
Proof.
  intros until bs.
  rewrite_env (nil ++ bs).
  intros. subst.
  eapply elim_stld_blocks_sim_wfS_aux; eauto.
Qed.

Lemma elim_stld_sim_reachablity_successors: forall f1 dones1 f2 dones2 pid
  (Hpass: SafePrimIter.iterate _ (elim_stld_step pid) (f1, dones1) =
    (f2, dones2)),
  reachablity_analysis f2 = reachablity_analysis f1 /\
  successors f2 = successors f1.
Proof.
  intros. subst.
  set (P:=fun (re:(fdef * list id)) =>
          let '(f, _) := re in
          reachablity_analysis f = reachablity_analysis f1 /\
          successors f = successors f1).
  assert (P (f1, dones1)) as HPf1.
    unfold P. split; auto.
  apply SafePrimIter.iterate_prop with (P:=P) in Hpass; auto.
    unfold elim_stld_step.
    intros a HPa.
    destruct a as [f dones].
    unfold elim_stld_fdef.
    destruct f as [fh bs].
    remember (elim_stld_blocks (fdef_intro fh bs) bs pid dones) as R.
    destruct R as [[f0 flag0] dones0]; auto.
    assert (P (f0, dones0)) as HPf0.
      unfold P.
      symmetry in HeqR.
      apply elim_stld_blocks_reachablity_successors in HeqR.
      destruct HeqR. destruct HPa.
      split.
        transitivity (reachablity_analysis (fdef_intro fh bs)); auto.
        transitivity (successors (fdef_intro fh bs)); auto.

    destruct flag0; auto.
Qed.

Lemma elim_stld_sim_wfS_wfPI: forall f1 dones1 f2 dones2 Ps1 Ps2 los nts main
  VarArgs pid (pinfo:PhiInfo)
  (Hpass: SafePrimIter.iterate _ (elim_stld_step pid)
    (f1, dones1) = (f2, dones2))
  (Heq1: PI_f pinfo = f1) (Heq2: PI_id pinfo = pid)
  (Hwfpi: WF_PhiInfo pinfo) S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  (program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs) /\
  WF_PhiInfo (update_pinfo pinfo f2).
Proof.
  intros. subst.
  set (P:=fun (re:(fdef * list id)) =>
          let '(f, _) := re in
          (program_sim [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
            [module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2)]
            main VarArgs /\
           wf_system
            [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] /\
           defined_program 
            [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
            main VarArgs) /\
          WF_PhiInfo (update_pinfo pinfo f)
       ).
  assert (P (PI_f pinfo, dones1)) as HPf1.
    unfold P.
    split; auto using program_sim_refl.
  apply SafePrimIter.iterate_prop with (P:=P) in Hpass; auto.
    unfold elim_stld_step.
    intros a HPa.
    destruct a as [f dones].
    unfold elim_stld_fdef.
    destruct f as [fh bs].
    remember (elim_stld_blocks (fdef_intro fh bs) bs (PI_id pinfo) dones) as R.
    destruct R as [[f0 flag0] dones0]; auto.
    assert (P (f0, dones0)) as HPf0.
      unfold P.
      symmetry in HeqR.
      destruct HPa as [[Hsima [HwfSa Hoka]] HwfPIa].
      change (PI_id pinfo) with (PI_id (update_pinfo pinfo (fdef_intro fh bs)))
        in HeqR.
      split.
        apply program_sim_wfS_trans with (P2:=
                [module_intro los nts
                 (Ps1 ++ product_fdef (fdef_intro fh bs) :: Ps2)]); auto.
          intros.
          eapply elim_stld_blocks_sim_wfS in HeqR; eauto.
        eapply elim_stld_blocks_wfPI in HeqR; eauto.

    destruct flag0; auto.
Qed.

Lemma macro_mem2reg_fdef_sim_wfS: forall rd f1 dones1 f2 dones2 Ps1 Ps2 los
  nts main VarArgs (Hreach: ret rd = reachablity_analysis f1)
  S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs)
  (Hiter: SafePrimIter.iterate (fdef * list id)
            (macro_mem2reg_fdef_step rd (successors f1)
              (make_predecessors (successors f1)))
            (f1, dones1) = (f2, dones2)),
  (program_sim S1 S2 main VarArgs /\
   wf_system S1 /\ defined_program S1 main VarArgs) /\
  reachablity_analysis f1 = reachablity_analysis f2 /\
  successors f1 = successors f2.
Proof.
  intros. subst.
  set (P:=fun (re:(fdef * list id)) =>
          let '(f, _) := re in
          (program_sim [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
            [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)] main VarArgs
          /\
          wf_system
            [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] /\
          defined_program 
            [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] main VarArgs) /\
          reachablity_analysis f1 = reachablity_analysis f /\
          successors f1 = successors f
      ).
  assert (P (f1, dones1)) as HPf1.
    unfold P. split; auto using program_sim_refl.
  apply SafePrimIter.iterate_prop with (P:=P) in Hiter; auto.
    unfold macro_mem2reg_fdef_step.
    intros a HPa.
    destruct a as [f dones].
    unfold macro_mem2reg_fdef_iter.
    remember (getEntryBlock f) as R.
    destruct R as [[l0 ps0 cs0 tmn0]|]; auto.
    remember (find_promotable_alloca f cs0 dones) as R.
    destruct R as [[[[pid ty] num] al]|]; auto.
    set (pinfo:=mkPhiInfo f rd pid ty num al).

    destruct HPa as [HPa [EQ2 EQ1]].
    rewrite EQ2 in Hreach.

    assert (WF_PhiInfo pinfo) as HwfPI.
      eapply find_promotable_alloca__WF_PhiInfo; eauto.

    rewrite does_stld_elim_is_true.
    remember (SafePrimIter.iterate (fdef * list id)
               (elim_stld_step pid)
               (phinodes_placement f rd pid ty al (successors f1)
               (make_predecessors (successors f1)), nil)) as R.
    destruct R as [f0 dones0].

    assert (P (f0, dones0)) as HPf0.
      symmetry in HeqR1.
      unfold P.
      split.
      Case "1".
        apply program_sim_wfS_trans with (P2:=
            [module_intro los nts (Ps1 ++
              product_fdef
                 (phinodes_placement f rd pid ty al (successors f1)
                   (make_predecessors (successors f1))) :: Ps2)]); auto; intros.
          eapply elim_stld_sim_wfS_wfPI with
            (pinfo:=mkPhiInfo (phinodes_placement f rd pid ty al
              (successors f1) (make_predecessors (successors f1)))
                rd pid ty num al); eauto.
            rewrite EQ1. destruct HPa as [Hpa1 [Hpa2 Hpa3]].
            eapply phinodes_placement_wfPI; eauto.

        apply program_sim_wfS_trans with (P2:=
          [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]); auto.
          intros. rewrite EQ1.
          split.
            eapply phinodes_placement_sim; eauto.
          split.
            eapply phinodes_placement_wfS; eauto.
            eapply program_sim__preserves__defined_program; 
              eauto using phinodes_placement_sim.          

      Case "2".
        apply elim_stld_sim_reachablity_successors in HeqR1.
        destruct HeqR1.
        split.
          transitivity (reachablity_analysis
            (phinodes_placement f rd pid ty al (successors f1)
              (make_predecessors (successors f1)))); auto.
            rewrite EQ1. rewrite EQ2.
            apply phinodes_placement_reachablity_analysis.

          transitivity (successors
            (phinodes_placement f rd pid ty al (successors f1)
              (make_predecessors (successors f1)))); auto.
            rewrite EQ1.

            apply phinodes_placement_reachablity_successors.

    assert (WF_PhiInfo (update_pinfo pinfo f0)) as HwfPIf0.
      change (update_pinfo pinfo f0) with
             (update_pinfo
               (update_pinfo pinfo
                 (phinodes_placement f rd pid ty al (successors f)
                   (make_predecessors (successors f)))) f0).
     destruct HPa as [HPa1 [HPa2 HPa3]].
     eapply elim_stld_sim_wfS_wfPI; eauto.
       rewrite EQ1. auto.
       eapply phinodes_placement_wfPI; eauto.
         rewrite EQ1. simpl.
         eapply phinodes_placement_wfS; eauto.
       eapply program_sim__preserves__defined_program; eauto.
         rewrite EQ1. simpl.
         eapply phinodes_placement_sim; eauto.

    assert (P (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef pid f0,
              nil) /\
            WF_PhiInfo (update_pinfo pinfo
              (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef pid f0)))
      as HPf.
      remember (load_in_fdef pid f0) as R.
      destruct R; auto.
      destruct HPf0 as [HPf0 HPf0'].
      split.
      Case "1".
        split.
        SCase "1.1".
          apply program_sim_wfS_trans with (P2:=
                  [module_intro los nts (Ps1 ++ product_fdef f0 :: Ps2)]); auto.
            intros.
            split.
              eapply dse_sim with (pinfo:=mkPhiInfo f0 rd pid ty num al); eauto.
            split.
              eapply dse_wfS with (pinfo:=mkPhiInfo f0 rd pid ty num al); eauto.
              eapply program_sim__preserves__defined_program; eauto.
                eapply dse_sim with (pinfo:=mkPhiInfo f0 rd pid ty num al); eauto.
        SCase "1.2".
          destruct HPf0' as [J1 J2].
          split.
            transitivity (reachablity_analysis f0); auto.
              apply elim_dead_st_fdef_reachablity_analysis.
            transitivity (successors f0); auto.
              apply elim_dead_st_fdef_successors.

      Case "2".
        destruct HPf0 as [HPf00 [HPf01 HPf02]].
        change (update_pinfo pinfo (elim_dead_st_fdef pid f0)) with
                 (update_pinfo
                   (update_pinfo
                     (update_pinfo pinfo
                       (phinodes_placement f rd pid ty al (successors f)
                         (make_predecessors (successors f))))
                   f0)
                   (elim_dead_st_fdef pid f0)
                 ).
        eapply dse_wfPI; eauto.

    destruct HPf as [HPf HwfPI0].
    remember (used_in_fdef pid
        (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef pid f0)) as R.
    destruct R; auto.
    destruct HPf as [HPf HPf'].
    split.
      apply program_sim_wfS_trans with (P2:=
                 [module_intro los nts
                   (Ps1 ++ product_fdef
                   (if load_in_fdef pid f0 then f0
                    else elim_dead_st_fdef pid f0) :: Ps2)]); auto.
        intros.
        split.
          eapply dae_sim with
            (pinfo:=mkPhiInfo
              (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef pid f0)
              rd pid ty num al); eauto.
        split.
          eapply dae_wfS with
            (pinfo:=mkPhiInfo
              (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef pid f0)
              rd pid ty num al); eauto.
          eapply program_sim__preserves__defined_program; eauto.
            eapply dae_sim with
              (pinfo:=mkPhiInfo
                (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef pid f0)
                rd pid ty num al); eauto.

      destruct HPf' as [Hreach' Hsucc'].
      split.
        transitivity
          (reachablity_analysis
            (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef pid f0));auto.
        apply remove_reachablity_analysis; auto.

        transitivity
          (successors
            (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef pid f0));auto.
        apply remove_successors; auto.
Qed.

Lemma eliminate_phis_sim_wfS: forall f Ps1 Ps2 los nts main VarArgs
  S1 S2 (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs)
  (Heq1: S1 = [module_intro los nts 
      (Ps1 ++ product_fdef (SafePrimIter.iterate fdef eliminate_step f) :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.
Admitted. (* From previous work PhiElim [2000] *)

Axiom fix_temporary_fdef_sim_wfS: forall f1 f2 Ps1 Ps2 los nts main VarArgs
  (Hpass: ret f2 = fix_temporary_fdef f1) S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.

Axiom remove_dbg_declares_sim_wfS: forall cs Ps1 Ps2 los nts main
  VarArgs f S1 S2
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq1: S1 = [module_intro los nts 
                 (Ps1 ++ product_fdef (remove_dbg_declares f cs) :: Ps2)]),
  (program_sim S2 S2 main VarArgs /\
   wf_system S2 /\
   defined_program S2 main VarArgs) ->
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.

Axiom remove_dbg_declares_sim_reachablity_successors: forall f cs,
  reachablity_analysis f 
    = reachablity_analysis (remove_dbg_declares f cs) /\
  successors f = successors (remove_dbg_declares f cs).

Lemma mem2reg_fdef_sim_wfS: forall (main : id) (VarArgs : list (GVsT DGVs))
  (los : layouts) (nts : namedts) (f : fdef) (Ps2 Ps1 : products) S1 S2
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef (mem2reg_fdef f) :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.
Proof.
  intros. subst.
  unfold mem2reg_fdef.
  remember (getEntryBlock f) as b. 
  destruct b as [[root ps cs tmn]|]; auto using program_sim_refl.
  remember (reachablity_analysis f) as R.
  destruct R as [rd|]; auto using program_sim_refl.
  rewrite print_reachablity_is_true.
  rewrite does_macro_m2r_is_true.
  remember (SafePrimIter.iterate (fdef * list id)
                   (macro_mem2reg_fdef_step rd 
                      (successors (remove_dbg_declares f cs))
                      (make_predecessors 
                        (successors (remove_dbg_declares f cs)))) 
                   ((remove_dbg_declares f cs), nil)) as R.
  destruct R as [f1 dones]; auto using program_sim_refl.
  rewrite does_phi_elim_is_true.
  remember (fix_temporary_fdef (SafePrimIter.iterate fdef eliminate_step f1))
    as R.
  destruct R as [f2|]; auto using program_sim_refl.
  apply program_sim_wfS_trans with (P2:=
    [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]); auto; intros.
    apply program_sim_wfS_trans with (P2:=
      [module_intro los nts
        (Ps1 ++ product_fdef (SafePrimIter.iterate fdef eliminate_step f1)
          :: Ps2)]); auto; intros.
      eapply fix_temporary_fdef_sim_wfS; eauto.
      eapply eliminate_phis_sim_wfS; eauto.
  apply program_sim_wfS_trans with (P2:=
    [module_intro los nts 
       (Ps1 ++ product_fdef (remove_dbg_declares f cs) :: Ps2)]); auto; intros.
    eapply macro_mem2reg_fdef_sim_wfS with (f1:=remove_dbg_declares f cs); eauto.
      rewrite HeqR.
      eapply remove_dbg_declares_sim_reachablity_successors; eauto.
    eapply remove_dbg_declares_sim_wfS; eauto using program_sim_refl.
Qed.

Lemma mem2reg_run_sim_wfS_aux: forall (main : id) (VarArgs : list (GVsT DGVs))
  (los : layouts) (nts : namedts) (Ps2 Ps1: products) S1 S2
  (HwfS : wf_system S2)
  (Hok: defined_program S2 main VarArgs)
  (Heq2: S2 = [module_intro los nts (Ps1++Ps2)])
  (Heq1: S1 = 
    [module_intro los nts
      (Ps1 ++ List.map
        (fun p : product =>
          match p with
          | product_fdef f => product_fdef (mem2reg_fdef f)
          | _ => p
          end) Ps2)]),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\ 
    defined_program S1 main VarArgs.
Proof.
  induction Ps2; simpl; intros; subst.
    split; auto using program_sim_refl.

    assert (J:=@IHPs2 (Ps1 ++ [a])). clear IHPs2.
    simpl_env in J. simpl in J.
    destruct a as [?|f|f]; auto.
    apply program_sim_wfS_trans with (P2:=
      [module_intro los nts
        (Ps1 ++ product_fdef f ::
           List.map (fun p : product =>
                     match p with
                     | product_fdef f => product_fdef (mem2reg_fdef f)
                     | _ => p
                     end) Ps2)]); auto; intros.
    eapply mem2reg_fdef_sim_wfS; eauto.
Qed.

Lemma mem2reg_run_sim_wfS: forall (m:module) (main:id) (VarArgs:list (GVsT DGVs))
  (HwfS : wf_system [m]) (Hok: defined_program [m] main VarArgs),
  program_sim [mem2reg.run m] [m] main VarArgs /\ wf_system [mem2reg.run m] /\
    defined_program [mem2reg.run m] main VarArgs.
Proof.
  destruct m as [los nts Ps].
  unfold mem2reg.run.
  intros.
  assert (J:=@mem2reg_run_sim_wfS_aux main VarArgs los nts Ps nil).
  auto.
Qed.

