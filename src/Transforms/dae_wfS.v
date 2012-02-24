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
Require Import program_sim.
Require Import trans_tactic.
Require Import dae.
Require Import list_facts.

(* Removing an id from an fdef preserves uniqueness *)

Hint Resolve sl_nil sublist_refl.

Lemma remove_block__blockLocs__sublist :
  forall (id1 : id) (bs : blocks),
    sublist (getBlocksLocs (List.map (remove_block id1) bs))
    (getBlocksLocs bs).
Proof.
  intros id1 bs. induction bs as [|[lab phis cmds tmn] bs]. apply sl_nil.
  simpl. repeat apply sublist_app; trivial; clear IHbs.
  apply sublist_map. apply filter_sublist.
  induction cmds as [|cmd cmds]. apply sl_nil.
  simpl. destruct (id_dec (getCmdLoc cmd) id1); simpl;
  [apply sl_cons_r|apply sl_cons]; trivial.
Qed.

Lemma remove_block__uniqBlocks :
  forall (id1 : id) (bs : blocks),
    uniqBlocks bs -> uniqBlocks (List.map (remove_block id1) bs).
Proof.
  intros id1 bs H.
  split; [destruct H as [H _] | destruct H as [_ H]];
    apply (NoDup_sublist _ _ _ H); clear H;
      [|apply remove_block__blockLocs__sublist].
  induction bs as [|[lab phis cmds tmn] bs]; simpl;
    [apply sl_nil|apply sl_cons]; trivial.
Qed.

Lemma remove_fdef__uniqFdef :
  forall (id1 : id) (f : fdef),
    uniqFdef f -> uniqFdef (remove_fdef id1 f).
Proof.
  intros id1 f H.
  destruct f as [[att rtyp idf fas fvas] bs].
  destruct H as [Hbsuniq HNoDup].
  simpl. split. apply remove_block__uniqBlocks. trivial.
  apply NoDup_split' in HNoDup. destruct HNoDup as [Hfas [Hbs Hin]].
  apply NoDup_app. trivial.

  apply NoDup_sublist with (getBlocksLocs bs). trivial.
  apply remove_block__blockLocs__sublist.

  intros id' H1 H2. clear Hbsuniq. apply (Hin id' H1).
  clear H1. generalize id' H2. clear id' H2.
  apply sublist_In. apply remove_block__blockLocs__sublist.
Qed.

Lemma dae_wfS: forall
  (id0 : id) (f :fdef) (pinfo : PhiInfo)
  (los : layouts) (nts : namedts) (Ps1 Ps2 : list product)
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS: wf_system nil [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Heq1: f = PI_f pinfo) (Heq2: id0 = PI_id pinfo),
  wf_system nil
    [module_intro los nts (Ps1 ++  product_fdef (remove_fdef id0 f) :: Ps2)].
Proof.
  intros.
  apply wf_system_intro.