Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import primitives.
Require Import palloca_props.
Require Import die.

Lemma die_wfS: forall id0 f diinfo los nts Ps1 Ps2
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq1: f = DI_f diinfo) (Heq2: id0 = DI_id diinfo),
  wf_system 
    [module_intro los nts (Ps1 ++  product_fdef (remove_fdef id0 f) :: Ps2)].
Admitted.

Lemma subst_fdef__diinfo: forall f id0 v0,
  exists diinfo:DIInfo, DI_f diinfo = subst_fdef id0 v0 f /\ DI_id diinfo = id0.
Admitted.

Lemma die_wfPI: forall id0 f diinfo los nts Ps1 Ps2 pinfo
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq1: f = DI_f diinfo) (Heq2: id0 = DI_id diinfo) (Heq3: f = PI_f pinfo),
  WF_PhiInfo (update_pinfo pinfo (remove_fdef id0 f)).
Admitted.

Lemma remove_successors : forall f id',
  successors f = successors (remove_fdef id' f).
Admitted.

Lemma remove_reachablity_analysis : forall f id',
  reachablity_analysis f = reachablity_analysis (remove_fdef id' f).
Admitted.

