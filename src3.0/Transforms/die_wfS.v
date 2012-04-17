Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import primitives.
Require Import palloca_props.
Require Import die.
Require Import filter.

Lemma subst_fdef__diinfo: forall f id0 v0,
  exists diinfo:DIInfo, DI_f diinfo = subst_fdef id0 v0 f /\ DI_id diinfo = id0.
(* 
   To prove this, we need
   1) id0 is pure: 
      this is true, because we run die after laa/las where id0 defines a load
   2) v0 doesnt use id0, See subst_unused_in_fdef in Vminus/motion.v
      this is true, because v0 must dominate id0

   This lemma is used in las/laa_die_wfPI in mem2reg_correct.v, where we have
      (Hst : ret inl (i0, v0, cs) = find_init_stld cs0 (PI_id pinfo) dones)
      (id0 : id) (Hld : ret inl id0 = find_next_stld cs (PI_id pinfo))
   from which, we can get lasinfo and laainfo to establish the above properties. 
*)
Admitted. (* diinfo *)

Lemma die_wfS: forall id0 f diinfo los nts Ps1 Ps2
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq1: f = DI_f diinfo) (Heq2: id0 = DI_id diinfo),
  wf_system 
    [module_intro los nts (Ps1 ++  product_fdef (remove_fdef id0 f) :: Ps2)].
Proof.
  intros.
  rewrite remove_fdef_is_a_filter.
  eapply filter_wfS; eauto.
    destruct diinfo. simpl in *. subst.
    apply fdef_doesnt_use_dead_insn; auto.
Qed.

Lemma die_wfPI: forall id0 f diinfo los nts Ps1 Ps2 pinfo
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq1: f = DI_f diinfo) (Heq2: id0 = DI_id diinfo) (Heq3: f = PI_f pinfo),
  WF_PhiInfo (update_pinfo pinfo (remove_fdef id0 f)).
Proof.
  intros.
  rewrite remove_fdef_is_a_filter.
  eapply filter_wfPI; eauto.
    destruct diinfo. simpl in *. subst. 
    intros c Hlkup Hdead.
    apply undead_insn_false_inv in Hdead. subst.
    apply DI_pure in Hlkup.
    destruct c; tinv Hlkup; auto.
Qed.

Lemma remove_successors : forall f id',
  successors f = successors (remove_fdef id' f).
Proof.
  intros.
  rewrite remove_fdef_is_a_filter.
  eapply filter_successors; eauto.
Qed.

Lemma remove_reachablity_analysis : forall f id',
  reachablity_analysis f = reachablity_analysis (remove_fdef id' f).
Proof.
  intros.
  rewrite remove_fdef_is_a_filter.
  eapply filter_reachablity_analysis; eauto.
Qed.

