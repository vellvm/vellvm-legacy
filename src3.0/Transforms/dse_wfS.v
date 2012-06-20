Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import opsem_props.
Require Import primitives.
Require Import palloca_props.
Require Import vmem2reg.
Require Import top_sim.
Require Import filter.

Lemma dse_wfS: forall (pinfo:PhiInfo) f pid Ps1 Ps2 los nts
  (Heq1: PI_id pinfo = pid) (Heq2: PI_f pinfo = f)
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  wf_system
    [module_intro los nts
      (Ps1 ++  product_fdef (elim_dead_st_fdef pid f) :: Ps2)].
Proof.
  intros.
  rewrite elim_dead_st_fdef_is_a_filter.
  eapply filter_wfS; eauto.
    apply wf_single_system__wf_uniq_fdef in HwfS; auto.
    destruct HwfS as [HwfF HuniqF].
    eapply fdef_doesnt_use_dead_store; eauto.
Qed.

Lemma dse_wfPI: forall (pinfo:PhiInfo) f pid Ps1 Ps2 los nts
  (Heq1: PI_id pinfo = pid) (Heq2: PI_f pinfo = f)
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  WF_PhiInfo (update_pinfo pinfo (elim_dead_st_fdef pid f)).
Proof.
  intros.
  rewrite elim_dead_st_fdef_is_a_filter.
  eapply filter_wfPI; eauto.
    intros c Hlkup Hdead.
    destruct c; tinv Hdead; simpl; auto.
Qed.

Lemma elim_dead_st_fdef_successors : forall f id',
  successors f = successors (elim_dead_st_fdef id' f).
Proof.
  intros.
  rewrite elim_dead_st_fdef_is_a_filter.
  eapply filter_successors; eauto.
Qed.

Lemma elim_dead_st_fdef_reachablity_analysis : forall f id',
  reachablity_analysis f =
    reachablity_analysis (elim_dead_st_fdef id' f).
Proof.
  intros.
  rewrite elim_dead_st_fdef_is_a_filter.
  eapply filter_reachablity_analysis; eauto.
Qed.
