Require Import vellvm.
Require Import Maps.
Require Import Lattice.
Require Import opsem_props.
Require Import trans_tactic.
Require Import primitives.
Require Import subst_inv.
Require Import phielim_spec.

(***************************************************************************)
(* Prove that phinode elimination implies vev_State used by subst_inv.  *)
Record PEInfo := mkPEInfo {
  PEI_f : fdef;
  PEI_b : block;
  PEI_p : phinode;
  PEI_v : value;
  PEI_in: phinodeInFdefBlockB PEI_p PEI_f PEI_b = true;
  PEI_subst: substing_value PEI_f PEI_v;
  PEI_assign: assigned_phi PEI_v PEI_p
}.

Lemma PEInfo__domination: forall (pi:PEInfo) s m (HwfF: wf_fdef s m (PEI_f pi))
  (Huniq: uniqFdef (PEI_f pi)),
  valueDominates (PEI_f pi) (PEI_v pi) (value_id (getPhiNodeID (PEI_p pi))).
Proof.
  destruct pi.
  simpl. intros.
  destruct_phinodeInFdefBlockB_tac.
  eapply assigned_phi__domination in PEI_assign0; eauto.
Qed.

Lemma PEInfo__lookupInsnViaIDFromFdef: forall (pi:PEInfo)
  (Huniq: uniqFdef (PEI_f pi)),
  lookupInsnViaIDFromFdef (PEI_f pi) (getPhiNodeID (PEI_p pi))
    = Some (insn_phinode (PEI_p pi)).
Proof.
  destruct pi. simpl. intros.
  destruct_phinodeInFdefBlockB_tac.
  solve_lookupInsnViaIDFromFdef.
Qed.

Lemma PEInfo_p__isnt__cmd: forall (pi:PEInfo) (Huniq: uniqFdef (PEI_f pi))
  l1 ps1 cs1 tmn1 c
  (HBinF: blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) (PEI_f pi) = true)
  (Hin : In c cs1),
  getCmdLoc c <> getPhiNodeID (PEI_p pi).
Proof.
  intros.
  assert (Hlk:=Huniq).
  apply PEInfo__lookupInsnViaIDFromFdef in Hlk.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HBinF; eauto.
  intro EQ. rewrite EQ in *.
  congruence.
Qed.

Lemma PEInfo__vev_ECStack: forall pi los nts M gl ps s
  (Hwfs: wf_system s)
  (HmInS: moduleInSystemB (module_intro los nts ps) s = true) 
  ECs (Hwfpp: OpsemPP.wf_ECStack (los,nts) ps ECs),
  vev_ECStack (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi)
    (PEI_f pi) (los,nts) M gl ECs.
Proof.
  induction ECs as [|[f b cs ? lc] ECs]; simpl; intros; auto.
    destruct Hwfpp as [HwfEC [HwfStk _]].
    split; eauto.
      destruct cs as [|c cs]; auto.
      destruct (inscope_of_cmd f b c); auto.
      intros EQ Hinscope; subst.
      destruct (Opsem.getOperandValue (los, nts) (PEI_v pi) lc gl); auto.
      destruct_if; auto.
      clear HeqR. 
      symmetry in e. contradict e.
      destruct HwfEC as [_ [HBinF [HFinP [_ [_ [l1 [ps1 [cs1 EQ]]]]]]]]; subst.
      eapply PEInfo_p__isnt__cmd; eauto using in_middle, wf_system__uniqFdef.
Qed.

(* The main result *)
Lemma PEInfo__vev: forall pi cfg S
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S),
  vev_State (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi)
    (PEI_f pi) cfg S.
Proof.
  intros.
  destruct cfg, S.
  destruct CurTargetData as [los nts].
  destruct Hwfcfg as [_ [Hwfg [Hwfs HmInS]]].
  destruct Hwfpp as [Hnempty Hstks].
  simpl.
  eapply PEInfo__vev_ECStack; eauto.
Qed.
 
Lemma assigned_phi__substing_value: forall S M p f l0 ps0 cs0 tmn0
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) f = true) 
  (Hin: In p ps0) v (Hassign: assigned_phi v p),
  substing_value f v.
Proof.
  intros.
  assert (Hwfp:=HBinF).
  eapply wf_fdef__wf_phinodes in Hwfp; eauto.
  eapply wf_phinodes__wf_phinode in Hwfp; eauto.
  inv Hwfp.
  inv Hassign.
  destruct Hex as [lv Hinlist].
  apply in_split_l in Hinlist.
  rewrite fst_split__map_fst in Hinlist. 
  apply H0 in Hinlist.
  unfold substing_value.
  simpl in Hinlist.
  inv Hinlist; auto.
  apply lookupTypViaIDFromFdef_elim' in H2; auto.
  destruct H2 as [H2 | [instr [J1 [J2 J3]]]]; subst; eauto.
Qed.

Lemma assigned_phi__substable_value: forall S M p f l0 ps0 cs0 tmn0
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) f = true) 
  (Hin: In p ps0) v (Hassign: assigned_phi v p),
  substable_value f (value_id (getPhiNodeID p)) v.
Proof.
  intros.
  assert (lookupInsnViaIDFromFdef f (getPhiNodeID p) = Some (insn_phinode p)) 
    as R.
    solve_lookupInsnViaIDFromFdef.
  unfold substable_value. rewrite R. auto.
Qed.


