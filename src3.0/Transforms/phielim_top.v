Require Import vellvm.
Require Import iter_pass.
Require Import iter_pass_correct.
Require Import mem2reg.
Require Import program_sim.
Require Import primitives.
Require Import die_wfS.
Require Import die_top.
Require Import subst.

Lemma eliminate_phi_false_spec: forall f p f'
  (Helim: (f', false) = eliminate_phi f p), f = f'.
Admitted.

Lemma eliminate_phis_false_spec: forall f' f ps0
  (Helim: (f', false) = eliminate_phis f ps0 ), f' = f.
Proof.
  induction ps0 as [|p]; simpl; intros.
    congruence.

    remember (eliminate_phi f p) as R.
    destruct R as []; inv Helim.
    destruct_if; auto.
    apply eliminate_phi_false_spec in HeqR. subst. auto.
Qed.

(* vid = phi [vid vid ... vid] *)
Inductive identity_phi: phinode -> Prop :=
| identity_phi_intro: forall vid ty vls
    (Hid: forall v0 l0, In (v0, l0) vls -> v0 = value_id vid),
    identity_phi (insn_phi vid ty vls)
.

Lemma identity_phi_cannot_be_in_reachable_blocks: forall S M p f
  l0 ps0 cs0 tmn0 (Hreach: reachable f l0) 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true)
  (Hin: In p ps0) (Hid: identity_phi p),
  False. 
Admitted.

(* vid = phi [vid v ... vid v] *)
Inductive assigned_phi (v:value): phinode -> Prop :=
| assigned_phi_intro: forall vid ty vls
    (Hex: exists l0, In (v, l0) vls)
    (Hassign: forall v0 l0, In (v0, l0) vls -> v0 = value_id vid \/ v0 = v),
    assigned_phi v (insn_phi vid ty vls)
.

Lemma assigned_phi__domination: forall S M p f l0 ps0 cs0 tmn0
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true) 
  (Hin: In p ps0) v (Has: assigned_phi v p),
  valueDominates f v (value_id (getPhiNodeID p)).
Admitted.

Lemma eliminate_phi_true_spec: forall S M f b f'
  (Hreach: isReachableFromEntry f b) p 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: phinodeInFdefBlockB p f b = true)
  (Helim: (f', true) = eliminate_phi f p),
  exists v, assigned_phi v p /\ 
    f' = remove_fdef (getPhiNodeID p) (subst_fdef (getPhiNodeID p) v f).
Admitted.

Lemma eliminate_phis_true_spec': forall f b f' S M 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (Hreach: isReachableFromEntry f b) ps
  (HBinF: forall p, In p ps -> phinodeInFdefBlockB p f b = true)
  (Helim: (f', true) = eliminate_phis f ps),
  exists p, In p ps /\ exists v, assigned_phi v p /\ 
    f' = remove_fdef (getPhiNodeID p) (subst_fdef (getPhiNodeID p) v f).
Proof.
  induction ps as [|p]; simpl; intros.
    inv Helim.

    remember (eliminate_phi f p) as R.
    destruct R as []; inv Helim.
    destruct_if.
      exists p.
      split; auto. 
      eapply eliminate_phi_true_spec in HeqR; eauto.

      apply eliminate_phi_false_spec in HeqR. subst. 
      apply IHps in H1; auto. 
      destruct H1 as [p' [Hin [v [H1 H2]]]].
      eauto 6.
Qed.
    
Lemma eliminate_phis_true_spec: forall f f' l0 S M 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (Hreach: reachable f l0) ps cs0 tmn0
  (HBinF: blockInFdefB (block_intro l0 ps cs0 tmn0) f = true)
  (Helim: (f', true) = eliminate_phis f ps),
  exists p, In p ps /\ exists v, assigned_phi v p /\ 
    f' = remove_fdef (getPhiNodeID p) (subst_fdef (getPhiNodeID p) v f).
Proof.
  intros.
  eapply eliminate_phis_true_spec' with (b:=block_intro l0 ps cs0 tmn0); 
    simpl; eauto 1.
  intros.
  bsplit; auto. simpl. solve_in_list.
Qed.

(* las_wfS.v should call this one *)
Lemma subst_fdef_dom__diinfo: forall S M f id0 v0
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (Hpure: forall (instr : insn)
            (Hlkup: lookupInsnViaIDFromFdef f id0 = ret instr),
            die.pure_cmd instr)
  (Hreach: id_in_reachable_block f id0)
  (Hvdom: valueDominates f v0 (value_id id0)),
  exists diinfo:die.DIInfo, 
    die.DI_f diinfo = subst_fdef id0 v0 f /\ die.DI_id diinfo = id0.
Proof.
  intros.
  apply subst_fdef__diinfo; auto.
    intro J.
    destruct v0; simpl in *; try tauto.
    destruct J as [J | J]; try tauto. subst.
    eapply idDominates_acyclic; eauto.
Qed.

Lemma assigned_phi__wf_value: forall S M p f l0 ps0 cs0 tmn0
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true) 
  (Hin: In p ps0) v (Hassign: assigned_phi v p),
  forall ty, 
    lookupTypViaIDFromFdef f (getPhiNodeID p) = Some ty ->
    wf_value S M f v ty.
Admitted.

Lemma subst_sim: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product)
  (v : value) f i1 (Hdom: valueDominates f v (value_id i1))
  S2 (Heq2: S2=[module_intro los nts
                (Ps1 ++  product_fdef f :: Ps2)])
  (Hok: defined_program S2 main VarArgs)
  (HwfS : wf_system S2),
  program_sim
    [module_intro los nts (Ps1 ++ product_fdef (subst_fdef i1 v f) :: Ps2)]
    S2 main VarArgs.
Admitted.

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

  Case "subse".
    subst.
    split.
      eapply subst_sim; eauto.
    split.
      apply subst_wfS; auto.
        apply lookupBlockViaIDFromFdef__notin_getArgsIDsOfFdef
          with (b:=(block_intro l0 ps0 cs0 tmn0)); auto.     
          apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
            simpl. xsolve_in_list. 
        eapply assigned_phi__wf_value; eauto.
       
      eapply program_sim__preserves__defined_program; eauto using subst_sim.
Qed.

Lemma eliminate_phis_reachablity_successors: forall (f1 f2 : fdef) ps0,
 (f2, true) = eliminate_phis f1 ps0 ->
 reachablity_analysis f1 = reachablity_analysis f2 /\
 successors f1 = successors f2.
Admitted.

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







