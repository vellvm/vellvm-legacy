Require Import vellvm.
Require Import iter_pass.
Require Import iter_pass_correct.
Require Import mem2reg.
Require Import program_sim.
Require Import primitives.
Require Import die_wfS.
Require Import die_top.
Require Import subst.
Require Import subst_sim.
Require Import phielim_spec.
Require Import phisubst_inv.

Lemma subst_phi_init: forall (los : layouts) (nts : namedts) (fh : fheader)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product)
  (v : value) p f
  (Hin: In p ps0) (Hassign: assigned_phi v p)
  (Heqf: f = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) M
  (HeqS: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HwfS : wf_system [M]),
  blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true /\
  wf_fdef [M] M f /\ uniqFdef f /\
  valueDominates f v (value_id (getPhiNodeID p)).
Proof.
  intros. 
  assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true)
    as HBinF.
    rewrite Heqf. simpl. apply InBlocksB_middle.
  assert (wf_fdef [module_intro los nts (Ps1++product_fdef f::Ps2)]
          (module_intro los nts (Ps1++product_fdef f::Ps2)) 
          f /\ uniqFdef f) as J.
    subst.
    apply wf_single_system__wf_uniq_fdef; auto.
  destruct J as [HwfF HuniqF].
  subst.
  eapply assigned_phi__domination in Hassign; eauto.
Qed.

Lemma subst_phi_wfS: forall (los : layouts) (nts : namedts) (fh : fheader)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product)
  (v : value) p f
  (Hin: In p ps0) (Hassign: assigned_phi v p) M
  (Heqf: f = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (HeqS: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HwfS : wf_system [M]),
  wf_system 
    [module_intro los nts
      (Ps1 ++ product_fdef (subst_fdef (getPhiNodeID p) v f) :: Ps2)].
Proof.
  intros. 
  assert (Hinit:=HwfS).
  eapply subst_phi_init in Hinit; eauto.
  destruct Hinit as [J1 [J2 [J3 J4]]].
  subst.
  apply subst_wfS; auto.
    apply lookupBlockViaIDFromFdef__notin_getArgsIDsOfFdef
          with (b:=(block_intro l0 ps0 cs0 tmn0)); auto.     
      apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
        simpl. xsolve_in_list. 
     eapply assigned_phi__wf_value; eauto 1.
Qed. 

Lemma subst_phi_sim: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product)
  (v : value) p f
  (Hin: In p ps0) (Hassign: assigned_phi v p) M
  (Heqf: f = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (HeqS: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HwfS : wf_system [M])  (Hok: defined_program [M] main VarArgs),
  program_sim
    [module_intro los nts 
      (Ps1 ++ product_fdef (subst_fdef (getPhiNodeID p) v f) :: Ps2)]
    [M] main VarArgs.
Proof.
  intros.
  assert (Hinit:=HwfS).
  eapply subst_phi_init in Hinit; eauto.
  destruct Hinit as [J1 [J2 [J3 J4]]].
  assert (lookupInsnViaIDFromFdef f (getPhiNodeID p) = Some (insn_phinode p))
    as Hlkup.
    eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef'; eauto.
  set (pi:=mkPEInfo f p v Hlkup Hassign).
  subst.
  set (ctx_inv := fun (cfg:OpsemAux.Config) (St:@Opsem.State DGVs) => True).
  apply SubstSim.sim with (ctx_inv:=ctx_inv); auto.
    intros ? ? ? ? ? ? ? ? Hop ?. 
    apply phisubst_inv.preservation with (pi:=pi) in Hop; auto.
    intros ? ? ? ? ? ? Hinit. 
    apply phisubst_inv.s_genInitState__inv with (pi:=pi) in Hinit; auto.
    intros. subst. eapply subst_phi_wfS; eauto.
    unfold ctx_inv. auto.
Qed.

Lemma eliminate_phis_sim_wfS: forall los nts Ps1 Ps2 rd,
 forall (fh : fheader) (efs : list id) (f1 : fdef) 
   (efs0 : list id) (main0 : id) (VarArgs0 : list (GVsT DGVs))
   (bs1 : list block) l0 ps0 cs0 tmn0 (bs2 : list block) f0
 (Heqf0: f0 = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
 (Hinrd: In l0 rd)
 (Helim: (f1, true) = eliminate_phis f0 ps0) (S0 S3 : list module)
 (Hreach: reachablity_analysis f0 = ret rd)
 (HeqS1: S0 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
 (HeqS2: S3 = [module_intro los nts (Ps1 ++ product_fdef f0 :: Ps2)])
 (HwfS2: wf_system S3) (Hok: defined_program S3 main0 VarArgs0),
 program_sim S0 S3 main0 VarArgs0 /\
 wf_system S0 /\ defined_program S0 main0 VarArgs0.
Proof.
  intros.
  assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0) f0 = true)
    as HBinF.
    rewrite Heqf0. simpl. apply InBlocksB_middle.
  assert (wf_fdef [module_intro los nts (Ps1++product_fdef f0::Ps2)]
          (module_intro los nts (Ps1++product_fdef f0::Ps2)) 
          f0 /\ uniqFdef f0) as J.
    subst.
    apply wf_single_system__wf_uniq_fdef; auto.
  destruct J as [HwfF HuniqF].
  eapply reachablity_analysis__reachable in Hreach; eauto.
  eapply eliminate_phis_true_spec in Helim; eauto 1.
  destruct Helim as [p [Hin [v [Hspec Heq]]]]; subst f1.
  assert (Hspec':=Hspec).
  eapply assigned_phi__domination in Hspec'; eauto.
  assert (Hpure: forall (instr : insn)
            (Hlkup: lookupInsnViaIDFromFdef f0 (getPhiNodeID p) = ret instr),
            die.pure_cmd instr).
    admit. (* die should support phinode *)
  assert (Hid_reach: id_in_reachable_block f0 (getPhiNodeID p)).
    intros b0 Hlkup.
    assert (b0 = block_intro l0 ps0 cs0 tmn0) as EQ.
      apply block_eq2 with (id1:=getPhiNodeID p)(f:=f0); auto.
        solve_blockInFdefB.
        solve_in_list.
        simpl. xsolve_in_list. 
      subst. auto.
  eapply subst_fdef_dom__diinfo in Hpure; eauto.
  destruct Hpure as [diinfo [EQ1 EQ2]].
  apply program_sim_wfS_trans with (P2:=
      [module_intro los nts
          (Ps1 ++ product_fdef (subst_fdef (getPhiNodeID p) v f0) :: Ps2)]); 
    auto; intros.
  Case "die".
    subst.
    split.
      eapply die_sim; eauto.
    split.
      eapply die_wfS; eauto.
      eapply program_sim__preserves__defined_program in H0; eauto using die_sim.

  Case "subst".
    subst.
    split.
      eapply subst_phi_sim; eauto.
    split.
      eapply subst_phi_wfS; eauto.
      eapply program_sim__preserves__defined_program; eauto using subst_phi_sim.
Qed.

Lemma eliminate_phis_reachablity_successors: forall (f1 f2 : fdef) ps0,
 (f2, true) = eliminate_phis f1 ps0 ->
 reachablity_analysis f1 = reachablity_analysis f2 /\
 successors f1 = successors f2.
Admitted. (* reach succ  *)

Ltac elimphi_tac :=
intros;
match goal with
| H:context [iter_block ElimPhi _ ?b0 _ _] |- _ => destruct b0; inv H; 
  try solve [
    split; 
      try solve [auto | eapply eliminate_phis_false_spec; eauto] |
    eapply eliminate_phis_sim_wfS; eauto 2 |
    eapply eliminate_phis_reachablity_successors; eauto 2
  ]
end.

Lemma elimphi_sim_wfS: forall f Ps1 Ps2 los nts main VarArgs
  S1 S2 (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs) rd
  (Hrd: reachablity_analysis f = Some rd)
  (Heq1: S1 = [module_intro los nts 
      (Ps1 ++ product_fdef (fst (IterationPass.iter ElimPhi tt rd f)) :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.
Proof.
  intros. 
  remember (IterationPass.iter ElimPhi tt rd f) as R.
  destruct R. unfold IterationPass.iter in HeqR.
  eapply IterationPassCorrect.iter_wfS with (pass:=ElimPhi); eauto.
    elimphi_tac. elimphi_tac. elimphi_tac. 
Qed.







