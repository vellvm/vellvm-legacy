Require Import List.
Require Import ListSet.
Require Import Coqlib.
Require Import Metatheory.
Require Import Maps.
Require Import cfg.
Require Import Dipaths.

Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Import LLVMsyntax.
Import LLVMinfra.

Lemma reachable_has_entry: forall f l1 (Hrd: reachable f l1),
  getEntryBlock f <> None.
Proof.
  intros.
  unfold reachable in Hrd.
  intro EQ. rewrite EQ in Hrd. inv Hrd.
Qed.

Lemma reachable_dec: forall (f:fdef) (l1:l), reachable f l1 \/ ~ reachable f l1.
Proof. 
  unfold reachable.
  intros. 
  destruct (getEntryBlock f) as [[]|]. 
    apply ACfg.reachable_dec.
    right. intro H. inv H.
Qed.

Lemma reachable_entrypoint:
  forall (f:fdef) l0 ps cs tmn,
    getEntryBlock f = Some (block_intro l0 ps cs tmn) ->
    reachable f l0.
Proof.
  intros f l0 ps cs tmn Hentry. unfold reachable.
  rewrite Hentry. exists V_nil. exists A_nil. apply DW_null.
  eapply entry_in_vertexes; eauto.
Qed.

Module DecRD.

Section RdSucc.

Variable f:fdef.

Lemma reachable_successors:
  forall l0 cs ps tmn l1 (Hinvx: vertexes_fdef f (index l1)),
  uniqFdef f -> 
  blockInFdefB (block_intro l0 cs ps tmn) f ->
  In l1 (successors_terminator tmn) ->
  reachable f l0 ->
  reachable f l1.
Proof.
  intros l0 cs ps tmn l1 Hinvx HuniqF HbInF Hin.
  unfold reachable. intro Hreach.
  remember (getEntryBlock f) as R.
  destruct R; auto.
  destruct b as [le ? ? ?].
  destruct Hreach as [vl [al Hreach]].
  exists (index l0::vl). exists (A_ends (index l1) (index l0)::al).
  apply DW_step; auto.
    eapply successor_in_arcs; eauto.
Qed.

End RdSucc.

End DecRD.

