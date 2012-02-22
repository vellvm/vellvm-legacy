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
Require Import memory_props.
Require Import sb_msim.
Require Import sb_ds_trans_lib.
Require Import sb_ds_gv_inject.
Require Import sb_metadata.
Require Import program_sim.
Require Import trans_tactic.
Require Import dae.

Lemma dae_wfS: forall id0 f pinfo los nts Ps1 Ps2
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system nil [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Heq1: f = PI_f pinfo) (Heq2: id0 = PI_id pinfo),
  wf_system nil
    [module_intro los nts (Ps1 ++  product_fdef (remove_fdef id0 f) :: Ps2)].
Admitted.
