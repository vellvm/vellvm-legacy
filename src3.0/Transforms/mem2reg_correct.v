Require Import vellvm.
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
Require Import die_wfS.
Require Import die_top.
Require Import sas_top.
Require Import sas_wfS.
Require Import phiplacement_bsim_wfS.
Require Import phiplacement_bsim_top.
Require Import iter_pass.
Require Import iter_pass_correct.
Require Import pass_combinators.
Require Import phielim_top.

(* We are proving the macro-based m2r pass *)
Parameter does_macro_m2r_is_true: mem2reg.does_macro_m2r tt = true.

Lemma las_die_wfPI: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) (Hreach:  In l0 (PI_rd pinfo))
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
  WF_PhiInfo (update_pinfo (subst_pinfo i1 v pinfo)
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
  assert (Hdiinfo:=HwfS).
  eapply las_diinfo in Hdiinfo; eauto.
  destruct Hdiinfo as [diinfo [J1 J2]]. rewrite Heq in J1.
  eapply die_wfPI; eauto.
    eapply las_wfPI; eauto.
    eapply las_wfS; eauto.
    rewrite <- Heq. apply subst_fdef_PI_f__PI_f_subst_pinfo.
Qed.

Lemma las_die_sim_wfS: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) (Hreach:  In l0 (PI_rd pinfo))
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
  assert (Hdiinfo:=HwfS).
  eapply las_diinfo in Hdiinfo; eauto.
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
  WF_PhiInfo (update_pinfo (subst_pinfo i1 v pinfo)
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
  assert (Hdiinfo:=HwfS).
  eapply laa_diinfo in Hdiinfo; eauto.
  destruct Hdiinfo as [diinfo [J1 J2]]. rewrite Heq in J1.
  eapply die_wfPI; eauto.
    eapply laa_wfPI; eauto.
    eapply laa_wfS; eauto.
    rewrite <- Heq. apply subst_fdef_PI_f__PI_f_subst_pinfo.
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
  assert (Hdiinfo:=HwfS).
  eapply laa_diinfo in Hdiinfo; eauto.
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
      eapply laa_sim; eauto.
    split.
      eapply laa_wfS; eauto.
      eapply program_sim__preserves__defined_program; eauto using laa_sim.
Qed.

Lemma elim_stld_cmds_unchanged: forall f' dones' f cs0 pid dones,
  (f', false, dones') = elim_stld_cmds f cs0 pid dones ->
  f' = f /\ dones = dones'.
Proof.
  intros.
  unfold elim_stld_cmds in H.
  destruct (find_init_stld cs0 pid dones) as [[[[]]|[]]|].
    destruct (find_next_stld c pid) as [[|[]]|]; inv H.
    destruct (find_next_stld c pid) as [[|[]]|]; inv H.
    inv H; auto.
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
  bs1 l0 ps0 cs0 tmn0 bs2 Ps1 Ps2 (Hreach:  In l0 (PI_rd pinfo))
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
  exists pinfo', WF_PhiInfo pinfo' /\ keep_pinfo f0 pinfo pinfo'.
Proof.
  intros.
  unfold elim_stld_cmds in Hpass.
  remember (find_init_stld cs0 (PI_id pinfo) dones) as R1.
  destruct R1 as [[[[]]|[]]|]; tinv Hpass.
    remember (find_next_stld c (PI_id pinfo)) as R2.
    destruct R2 as [[|[]]|]; inv Hpass; eauto.
      eapply las_die_wfPI in HwfS; eauto. instantiate_pinfo.
      eapply sas_wfPI in HwfS; eauto. instantiate_pinfo.
      instantiate_pinfo.

    remember (find_next_stld c (PI_id pinfo)) as R2.
    destruct R2 as [[|[]]|]; inv Hpass.
      eapply laa_die_wfPI in HwfS; eauto. instantiate_pinfo.
      instantiate_pinfo.
      instantiate_pinfo.
Qed.

Lemma elim_stld_cmds_sim_wfS: forall los nts fh dones (pinfo:PhiInfo) f0 dones0
  main VarArgs bs1 l0 ps0 cs0 tmn0 bs2 Ps1 Ps2 (Hreach:  In l0 (PI_rd pinfo))
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

Ltac elim_stld_block_tac :=
intros;
match goal with
| H:context [iter_block ElimStld _ ?b0 _ _] |- _ => destruct b0; simpl in H; 
  try solve [
    eapply elim_stld_cmds_unchanged; eauto 2 |
    eapply elim_stld_cmds_wfPI; eauto 2 |
    eapply elim_stld_cmds_sim_wfS; eauto 2 |
    eapply elim_stld_cmds_reachablity_successors; eauto 2
  ]
| _ => solve_keep_pinfo
end.

Lemma elim_stld_sim_wfS_wfPI: forall f1 f2 Ps1 Ps2 los nts main
  VarArgs pid rd (pinfo:PhiInfo) (dones1 dones2:ElimStld.(effects))
  (Hpass: SafePrimIter.iterate _ (IterationPass.iter_step ElimStld pid rd)
    (f1, dones1) = (f2, dones2))
  (Heq1: PI_f pinfo = f1) (Heq2: PI_id pinfo = pid) (Heq2: PI_rd pinfo = rd)
  (Hwfpi: WF_PhiInfo pinfo) S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  (program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs) /\
  exists pinfo', WF_PhiInfo pinfo' /\ keep_pinfo f2 pinfo pinfo'.
Proof.
  intros. 
  eapply IterationPassCorrect.iter_wfS_wfPI; eauto.
    elim_stld_block_tac. elim_stld_block_tac. 
    elim_stld_block_tac. elim_stld_block_tac. 
Qed.

Hint Unfold keep_pinfo.

Section Macro_mem2reg_fdef_sim_wfS.

Variable (Ps1 Ps2:products) (los:layouts) (nts:namedts) (main:id) 
         (VarArgs:list (GVsT DGVs)) (f1:fdef).

Definition Pmm2r' :=
  fun (f:fdef) =>
       (program_sim [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
         [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)] main VarArgs
       /\
       wf_system
         [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] /\
       defined_program 
         [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] main VarArgs) /\
       reachablity_analysis f1 = reachablity_analysis f /\
       successors f1 = successors f.

Definition Pmm2r :=
   fun (re:(fdef * list id)) => let '(f, _) := re in Pmm2r' f.

Lemma Pmm2r'_Pmm2r: forall f ds, Pmm2r' f -> Pmm2r (f, ds).
Proof. simpl. auto. Qed.

Lemma macro_mem2reg_fdef_sim_wfS: forall rd dones1 f2 dones2 
  (Hreach: ret rd = reachablity_analysis f1) S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs)
  (Hiter: SafePrimIter.iterate (fdef * list id)
            (macro_mem2reg_fdef_step rd (successors f1)
              (XATree.make_predecessors (successors f1)))
            (f1, dones1) = (f2, dones2)),
  (program_sim S1 S2 main VarArgs /\
   wf_system S1 /\ defined_program S1 main VarArgs) /\
  reachablity_analysis f1 = reachablity_analysis f2 /\
  successors f1 = successors f2.
Proof.
  intros. subst.
  assert (Pmm2r (f1, dones1)) as HPf1.
    unfold Pmm2r. split; auto using program_sim_refl.
  apply SafePrimIter.iterate_prop with (P:=Pmm2r) in Hiter; auto.
    unfold macro_mem2reg_fdef_step.
    intros a HPa.
    destruct a as [f dones].
    unfold macro_mem2reg_fdef_iter.
    remember (getEntryBlock f) as R.
    destruct R as [[l0 ps0 cs0 tmn0]|]; auto.
    remember (find_promotable_alloca f cs0 dones) as R.
    destruct R as [[[[pid ty] num] al]|]; auto.
    set (pinfo:=mkPhiInfo f rd pid ty num al).
 
    assert (HPa':=HPa).
    destruct HPa as [HPa [EQ2 EQ1]].
    rewrite EQ2 in Hreach.
    assert (WF_PhiInfo pinfo) as HwfPI.
      eapply find_promotable_alloca__WF_PhiInfo; eauto.

    case_eq (IterationPass.iter ElimStld pid rd
               (phinodes_placement rd pid ty al (successors f1)
                  (XATree.make_predecessors (successors f1)) f)).
    intros f0 dones0 HeqElimStld.
    unfold IterationPass.iter in HeqElimStld.

    apply Pmm2r'_Pmm2r.
    set (Pmm2r'' := 
           fun f => Pmm2r' f /\
           exists pinfo', WF_PhiInfo pinfo' /\ keep_pinfo f pinfo pinfo').
    repeat (rewrite seq_trans_assoc).
    apply seq_trans_pres_strengthen_P with (Pcom':=Pmm2r''); auto.
    assert (Pmm2r'' f) as HPa''. 
      split; auto.
        instantiate_pinfo.
    compass_tac.
    Case "1".
    split.
      split.
      SCase "1.1".
        apply program_sim_wfS_trans with (P2:=
                [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]); auto.
        intros.
        rewrite EQ1.
        split.
          eapply phinodes_placement_sim; eauto.
        split.
          eapply phinodes_placement_wfS; eauto.
          eapply program_sim__preserves__defined_program; 
             eauto using phinodes_placement_sim. 
    
      SCase "1.2".
        rewrite EQ1. rewrite EQ2.
        rewrite <- phinodes_placement_reachablity_analysis.
        rewrite <- phinodes_placement_successors. auto.
    
      SCase "1.3".
        destruct HPa as [HPa1 [HPa2 HPa3]].
        eapply phinodes_placement_wfPI in Hreach; eauto.
        rewrite EQ1. 
        match goal with
        | _: WF_PhiInfo 
              {| PI_f := ?f; PI_rd := ?rd; PI_id := ?pid;
                 PI_typ := ?ty; PI_num := ?num; PI_align := ?al |} |-
            exists _ : _, WF_PhiInfo _ /\ keep_pinfo ?f _ _ =>
            exists {| PI_f := f; PI_rd := rd; PI_id := pid;
                    PI_typ := ty; PI_num := num; PI_align := al |};
            repeat (split; auto)
        end.
    
    Case "2".
    unfold IterationPass.iter.
    rewrite HeqElimStld.
    destruct HPf as [[HPf21 HPf22] HPf23].
    split.
      split.
      SCase "2.1".
        apply program_sim_wfS_trans with (P2:=
                [module_intro los nts (Ps1 ++
                  product_fdef
                     (phinodes_placement rd pid ty al (successors f1)
                       (XATree.make_predecessors (successors f1)) f) :: Ps2)]); 
          auto; intros.
        SSCase "2.1.1".
          eapply elim_stld_sim_wfS_wfPI with
                (pinfo:=mkPhiInfo (phinodes_placement rd pid ty al
                  (successors f1) (XATree.make_predecessors (successors f1)) f)
                    rd pid ty num al); eauto. 
            rewrite EQ1. destruct HPa as [Hpa1 [Hpa2 Hpa3]].
            eapply phinodes_placement_wfPI; eauto.
    
      SCase "2.2".
        apply IterationPassCorrect.iter_reachablity_successors in HeqElimStld; 
              try solve [auto | elim_stld_block_tac]. 
        destruct HeqElimStld.
        destruct HPf22.
        split; etransitivity; eauto.
    
      SCase "2.3".
        apply change_keep_pinfo with (pinfo1:=
                   (update_pinfo pinfo
                     (phinodes_placement rd pid ty al (successors f)
                       (XATree.make_predecessors (successors f)) f))); auto.
        destruct HPa as [HPa1 [HPa2 HPa3]].
        eapply elim_stld_sim_wfS_wfPI; eauto.
          simpl. rewrite EQ1. auto.
          eapply phinodes_placement_wfPI; eauto.
          rewrite EQ1. simpl. eapply phinodes_placement_wfS; eauto.
          eapply program_sim__preserves__defined_program; eauto.
            rewrite EQ1. simpl.
            eapply phinodes_placement_sim; eauto.
    
    Case "3".
    match goal with
    | _: load_in_fdef _ ?f = _ |- _ => remember f as f0'
    end.
  
    destruct HPf as [[HPf10 HPf20] [pinfo' [HwfPIf0 Hkeep]]].
    
    split.
      split.   
      SCase "3.1".
        apply program_sim_wfS_trans with (P2:=
                 [module_intro los nts (Ps1 ++ product_fdef f0' :: Ps2)]); auto.
        intros.
        split. eapply dse_sim with (pinfo:=pinfo'); eauto; solve_keep_pinfo.
        split. eapply dse_wfS with (pinfo:=pinfo'); eauto; solve_keep_pinfo.
               eapply program_sim__preserves__defined_program; eauto.
                 eapply dse_sim with (pinfo:=pinfo'); eauto; solve_keep_pinfo.
      SCase "3.2".
        destruct HPf20 as [J1 J2].
        split; etransitivity; eauto.
          apply elim_dead_st_fdef_reachablity_analysis.
          apply elim_dead_st_fdef_successors.
    
      SCase "3.3".
        destruct HPf10 as [? [? ?]].
        exists (update_pinfo pinfo' (elim_dead_st_fdef pid f0')).
        split.
          eapply dse_wfPI; eauto; solve_keep_pinfo.
          solve_keep_pinfo.
    
    Case "4".
      intros [HPf2 [pinfo' [HwfPIf2 Hkeep]]].
      apply cond_trans_pres_P; try solve [compass_tac | auto].
      intros Hfalse.
      match goal with
      | _: used_in_fdef _ ?f = _ |- _ => remember f as f0'
      end.
      destruct HPf2 as [HPf12 HPf22].
      split.   
      SCase "4.1".
        apply program_sim_wfS_trans with (P2:=
                     [module_intro los nts
                       (Ps1 ++ product_fdef f0' :: Ps2)]); auto.
          intros.
          assert (f0' = PI_f pinfo') as EQ3. solve_keep_pinfo.
          assert (pid = PI_id pinfo') as EQ4. solve_keep_pinfo.
          rewrite EQ3, EQ4 in Hfalse.
          split.
            eapply dae_sim with (pinfo:=pinfo'); eauto 1.
          split.
            eapply dae_wfS with (pinfo:=pinfo'); eauto 1.
            eapply program_sim__preserves__defined_program; eauto.
              eapply dae_sim with (pinfo:=pinfo'); eauto 1.
      SCase "4.2".
        destruct HPf22 as [Hreach' Hsucc'].
        split; etransitivity; eauto.
          apply remove_reachablity_analysis; auto.
          apply remove_successors; auto.
Qed.

End Macro_mem2reg_fdef_sim_wfS.

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
  destruct (print_reachablity rd).
  Case "1".
    rewrite does_macro_m2r_is_true.
    remember (SafePrimIter.iterate (fdef * list id)
                     (macro_mem2reg_fdef_step rd 
                        (successors f)
                        (XATree.make_predecessors 
                          (successors f))) 
                     (f, nil)) as R.
    destruct R as [f1 dones]; auto using program_sim_refl.
    destruct (does_phi_elim tt).
    SCase "1.1".
      apply program_sim_wfS_trans with (P2:=
        [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]); auto; intros.
      SSCase "1.1.1".
        eapply elimphi_sim_wfS with (f:=f1); eauto.
          eapply macro_mem2reg_fdef_sim_wfS with (f1:=f) in HwfS; eauto.
          destruct HwfS as [_ [Hreach _]]. congruence.
      SSCase "1.1.2".
        eapply macro_mem2reg_fdef_sim_wfS with (f1:=f); eauto.
    SCase "1.2".
      eapply macro_mem2reg_fdef_sim_wfS with (f1:=f); eauto.      
  Case "2".
    split; auto using program_sim_refl.
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

