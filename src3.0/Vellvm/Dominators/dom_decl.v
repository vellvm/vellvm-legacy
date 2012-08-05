Require Import List.
Require Import ListSet.
Require Import Coqlib.
Require Import Metatheory.
Require Import Maps.
Require Import Lattice.
Require Import Kildall.
Require Import Iteration.
Require Import cfg.
Require Import reach.
Require Import Dipaths.

Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Import LLVMsyntax.
Import LLVMinfra.

Module DecDom.

Local Open Scope dom.

Ltac unfold_cfg f :=
  unfold imm_domination, reachable, strict_domination, domination;
  intros;
  match goal with
  | Hentry: getEntryLabel f = Some ?entry |- _ =>
      apply getEntryLabel__getEntryBlock in Hentry;
      destruct Hentry as [[] [Hentry EQ]]; simpl in EQ; subst entry;
      rewrite Hentry in *
  | |- _ =>
      remember (getEntryBlock f) as R;
      destruct R as [[]|]; try congruence
  end.

Lemma sdom_isnt_refl: forall f l1 l2 (Hreach: f ~>* l2)
  (Hdom12 : strict_domination f l1 l2),
  l1 <> l2.
Proof.
  unfold_cfg f.
  eapply ACfg.sdom_isnt_refl; eauto.
Qed.

Lemma dom_tran: forall (f:fdef) (l1 l2 l3:l),
  f |= l1 >>= l2 -> f |= l2 >>= l3 -> f |= l1 >>= l3.
Proof.
  unfold_cfg f.
  eapply ACfg.dom_tran; eauto.
Qed.

Lemma everything_dominates_unreachable_blocks :
  forall f l1 l2 (Hreach: ~ f ~>* l2)
  (Hentry: getEntryBlock f <> None),
  f |= l1 >>= l2.
Proof.
  unfold_cfg f.
  eapply ACfg.everything_dominates_unreachable_blocks; eauto.
Qed.

Lemma everything_sdominates_unreachable_blocks :
  forall f l1 l2 (Hreach: ~ f ~>* l2)
  (Hentry: getEntryBlock f <> None),
  f |= l1 >> l2.
Proof.
  unfold_cfg f.
  eapply ACfg.everything_sdominates_unreachable_blocks; eauto.
Qed.

Lemma sdom_reachable : forall f l1 l2,
  f ~>* l2 -> f |= l1 >> l2 -> f ~>* l1.
Proof.
  unfold_cfg f.
  eapply ACfg.sdom_reachable; eauto.
Qed.

Lemma dom_reachable : forall f l1 l2,
  f ~>* l2 -> f |= l1 >>= l2 -> f ~>* l1.
Proof.
  unfold_cfg f.
  eapply ACfg.dom_reachable; eauto.
Qed.

Lemma sdom_dom: forall f l1 l2,
  f |= l1 >> l2 -> f |= l1 >>= l2.
Proof.
  unfold_cfg f.
  eapply ACfg.sdom_dom; eauto.
Qed.

Lemma dom_sdom: forall f l1 l2,
  f |= l1 >>= l2 -> l1 <> l2 -> f |= l1 >> l2.
Proof.
  unfold_cfg f.
  eapply ACfg.dom_sdom; eauto.
Qed.

Lemma domination_has_entry: forall f l1 l2 (Hdom: f |= l1 >>= l2),
  getEntryBlock f <> None.
Proof.
  intros.
  unfold domination in Hdom.
  intro EQ. rewrite EQ in Hdom. auto.
Qed.

Lemma strict_domination__getEntryLabel: forall f l1 l2
  (Hsdom: f |= l1 >> l2),
  exists e, getEntryLabel f = Some e.
Proof.
  unfold strict_domination.
  intros.
  inv_mbind. symmetry in HeqR.
  apply getEntryBlock__getEntryLabel in HeqR. eauto.
Qed.

Section dom_acyclic_tran.

Variable f:fdef.

Hypothesis getEntryBlock_inv : forall
  (l3 : l)
  (l' : l)
  (ps : phinodes)
  (cs : cmds)
  (tmn : terminator)
  (HBinF : blockInFdefB (l3, stmts_intro ps cs tmn) f = true)
  (Hsucc : In l' (successors_terminator tmn)) a s0
  (H : getEntryBlock f = Some (a, s0)),
  l' <> a.

Lemma entry_has_no_preds: forall (l5 : l) s5
  (HeqR : Some (l5, s5) = getEntryBlock f)
  (a0 : ATree.elt) (Hin: In l5 ((successors f) !!! a0)),
  False.
Proof.
  intros.
  eapply successors__blockInFdefB in Hin; eauto.
  destruct Hin as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
  symmetry in HeqR. destruct f.
  eapply getEntryBlock_inv in Hinsucc; eauto.
Qed.

Lemma dom_acyclic: forall (l1 l2:l)
  (H: f ~>* l2) (H0: f |= l1 >> l2),
  ~ f |= l2 >>= l1.
Proof.
  unfold_cfg f.
  eapply ACfg.dom_acyclic; eauto using entry_has_no_preds.
Qed.

Lemma sdom_tran1: forall (l1 l2 l3:l),
  f |= l1 >> l2 -> f |= l2 >>= l3 -> f |= l1 >> l3.
Proof.
  unfold_cfg f.
  eapply ACfg.sdom_tran1; eauto using entry_has_no_preds.
Qed.

Lemma sdom_tran2: forall (l1 l2 l3:l),
  f |= l1 >>= l2 -> f |= l2 >> l3 -> f |= l1 >> l3.
Proof.
  unfold_cfg f.
  eapply ACfg.sdom_tran2; eauto using entry_has_no_preds.
Qed.

Lemma sdom_tran: forall (l1 l2 l3:l),
  f |= l1 >> l2 -> f |= l2 >> l3 -> f |= l1 >> l3.
Proof.
  intros. apply sdom_dom in H0. eapply sdom_tran1; eauto.
Qed.

Lemma idom_isnt_refl: forall l1 l2 (Hreach: f ~>* l2)
  (Hdom12 : f |= l1 >>> l2),
  l1 <> l2.
Proof.
  unfold_cfg f.
  eapply ACfg.idom_isnt_refl; eauto.
Qed.

Lemma idom_sdom: forall l1 l2 (Hdom12 : f |= l1 >>> l2),
  f |= l1 >> l2.
Proof.
  intros. destruct Hdom12. auto.
Qed.

Lemma idom_injective: forall p l1 l2
  (Hidom1 : f |= p >>> l1) (Hidom2 : f |= p >>> l2)
  (Hrd1 : f ~>* l1) (Hrd2 : f ~>* l2)
  (Hneq : l1 <> l2)
  (Hdec : f |= l1 >> l2 \/ f |= l2 >> l1),
  False.
Proof.
  unfold_cfg f.
  eapply ACfg.idom_injective in Hdec; eauto using entry_has_no_preds.
Qed.

End dom_acyclic_tran.

Lemma sdom_dec : forall f l1 l2,
  f |= l1 >> l2 \/ ~ f |= l1 >> l2.
Proof. 
  unfold_cfg f; auto.
  apply ACfg.sdom_dec; auto.
Qed. 

Lemma non_sdom__inv: forall f l1 l2 be (Hentry: getEntryBlock f = Some be)
  (Hnsdom: ~ f |= l1 >> l2),
  exists vl, exists al, D_walk (vertexes_fdef f) (arcs_fdef f) 
    (index l2) (index (getBlockLabel be)) vl al /\
    ~ (In (index l1) vl /\ l1 <> l2).
Proof.
  unfold_cfg f; auto.
  inv Hentry.
  eapply ACfg.non_sdom__inv; eauto.
Qed.

Lemma sdom_ordered : forall f l1 l2 l3
  (Hneq: l1 <> l2) (Hreach: f ~>* l3)
  (Hsdom: f |= l1 >> l3)
  (Hsdom': f |= l2 >> l3),
  f |= l1 >> l2 \/ f |= l2 >> l1.
Proof.
  unfold_cfg f; auto.
  eapply ACfg.sdom_ordered; eauto.
Qed.

Lemma entry_doms_others: forall f entry l1  (Hnentry: l1 <> entry) 
  (H: getEntryLabel f = Some entry),
  f |= entry >> l1.
Proof.
  unfold_cfg f; auto.
  eapply ACfg.entry_doms_others; eauto.
Qed.

Close Scope dom.

End DecDom.
