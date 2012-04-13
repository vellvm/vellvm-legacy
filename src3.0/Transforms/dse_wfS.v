Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import opsem_props.
Require Import primitives.
Require Import palloca_props.
Require Import mem2reg.
Require Import top_sim.

Lemma dse_wfS: forall (pinfo:PhiInfo) f pid Ps1 Ps2 los nts
  (Heq1: PI_id pinfo = pid) (Heq2: PI_f pinfo = f)
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hnld: load_in_fdef pid f = false),
  wf_system
    [module_intro los nts
      (Ps1 ++  product_fdef (elim_dead_st_fdef pid f) :: Ps2)].
Proof.
Admitted. (* prev WF *)

Lemma dse_wfPI: forall (pinfo:PhiInfo) f pid Ps1 Ps2 los nts
  (Heq1: PI_id pinfo = pid) (Heq2: PI_f pinfo = f)
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hnld: load_in_fdef pid f = false),
  WF_PhiInfo (update_pinfo pinfo (elim_dead_st_fdef pid f)).
Proof.
Admitted. (* prev WF *)

Lemma elim_dead_st_fdef_successors : forall f id',
  successors f = successors (elim_dead_st_fdef id' f).
Admitted. (* prev WF *)

Lemma elim_dead_st_fdef_reachablity_analysis : forall f id',
  reachablity_analysis f =
    reachablity_analysis (elim_dead_st_fdef id' f).
Admitted. (* prev WF *)
