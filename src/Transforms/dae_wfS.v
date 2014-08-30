Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import opsem_props.
Require Import promotable_props.
Require Import primitives.
Require Import palloca_props.
Require Import memory_props.
Require Import trans_tactic.
Require Import dae.
Require Import filter.

(* This file proves that DAE preserves well-formedness. *)

(* DAE preserves well-formedness. *)
Lemma dae_wfS: forall
  (id0 : id) (f :fdef) (pinfo : PhiInfo)
  (los : layouts) (nts : namedts) (Ps1 Ps2 : list product)
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Heq1: f = PI_f pinfo) (Heq2: id0 = PI_id pinfo),
  wf_system
    [module_intro los nts (Ps1 ++ product_fdef (remove_fdef id0 f) :: Ps2)].
Proof.
  intros.
  rewrite remove_fdef_is_a_filter.
  eapply filter_wfS; eauto.
    subst. apply fdef_doesnt_use_dead_insn; auto.
Qed.

Section product_well_formedness.

(* Products are well-formed independently of each other. Therefore,
   changing just one product in a module shouldn't interfere with the
   others. *)

Lemma wf_prod_split :
  forall (sys : system)
    (m : module) (ps1 ps2 : products),
    wf_prods sys m (ps1 ++ ps2) ->
    wf_prods sys m ps1 /\ wf_prods sys m ps2.
Proof.
  induction ps1 as [|p ps1]. split. constructor. trivial.
  intros ps2 Hwf. inversion Hwf as [|? ? ? ? Hwfps Hwfp]. subst.
  clear Hwf. apply IHps1 in Hwfps. destruct Hwfps as [Hps1 Hps2].
  split; trivial.
  apply wf_prods_cons; trivial.
Qed.

Lemma in_module_wf_prods :
  forall (sys : system) (m : module) (ps : products),
    (forall p : product, InProductsB p ps -> wf_prod sys m p) ->
    wf_prods sys m ps.
Proof.
  induction ps as [|p ps]. intros. constructor.
  intros H. apply wf_prods_cons.

    apply IHps. intros p' Hin. apply H. simpl.
    apply orb_true_intro. right. trivial.

    apply H. apply orb_true_intro. left. apply productEqB_refl.
Qed.

End product_well_formedness.

