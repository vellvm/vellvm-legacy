Require Import List.
Require Import ListSet.
Require Import Coqlib.
Require Import Metatheory.
Require Import Maps.
Require Import Lattice.
Require Import Kildall.
Require Import Iteration.
Require Import cfg.
Require Import dom_decl.
Require Import reach.
Require Import Dipaths.
Require Import dom_tree.
Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Import LLVMsyntax.
Import LLVMinfra.

(* The file defines the specification of computing dominators. *)

Notation "x {+} y" := (x :: y) (at level 0): dom.
Notation "x {<=} y" := (incl x y) (at level 0): dom.
Notation "{}" := nil (at level 0): dom.
Notation "x `in` y" := (In x y) (at level 70): dom.
Local Open Scope dom.

(* ALGDOM gives an abstract specification of algorithms that compute dominators. 
   First of all, sdom defines the signature of a dominance analysis algorithm: 
   given a function f and a label l1, (sdom f l1) returns the set of strict 
   dominators of l1 in f ; dom defines the set of dominators of l1 by adding l1 
   into l1’s strict dominators.

   To make the interface simple, ALGDOM only requires the basic properties that 
   ensure that sdom is correct: it must be both sound and complete in terms of 
   the declarative definitions (Definition 2). Given the correctness of sdom, 
   the AlgDom_Properties module can ‘lift’ properties (conversion, transitivity, 
   acyclicity, ordering, etc.) from the declarative definitions to the 
   implementations of sdom and dom. 

   ALGDOM requires completeness directly. Soundness can be proven by two more 
   basic properties: entry_sound requires that the entry has no strict 
   dominators; successors_sound requires that if l1 is a successor of l2, then 
   l2’s dominators must include l1’s strict dominators. Given an algorithm that 
   establishes the two properties, AlgDom_Properties proves that the algorithm 
   is sound by induction over any path from the entry to l2. *)
Module Type ALGDOM.

Parameter sdom : fdef -> atom -> set atom.

Axiom dom_entrypoint : forall f l0 s0
  (Hentry : getEntryBlock f = Some (l0, s0)),
  sdom f l0 = {}.

Definition branchs_in_fdef f :=
  forall (p : l) (ps0 : phinodes) (cs0 : cmds) 
         (tmn0 : terminator) (l2 : l),
  blockInFdefB (p, stmts_intro ps0 cs0 tmn0) f ->
  In l2 (successors_terminator tmn0) -> In l2 (bound_fdef f).

Axiom sdom_in_bound: forall fh bs l5, 
  (sdom (fdef_intro fh bs) l5) {<=} (bound_blocks bs).

Axiom dom_successors : forall
  (l3 : l) (l' : l) f
  (contents3 contents': ListSet.set atom)
  (Hinscs : l' `in` (successors f) !!! l3)
  (Heqdefs3 : contents3 = sdom f l3)
  (Heqdefs' : contents' = sdom f l'),
  contents' {<=} (l3 {+} contents3).

Axiom sdom_is_complete: forall (f:fdef)
  (Hbinf: branchs_in_fdef f) 
  (l3 : l) (l' : l) s3 s'
  (HuniqF : uniqFdef f)
  (HBinF' : blockInFdefB (l', s') f = true)
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hsdom: f |= l' >> l3),
  l' `in` (sdom f l3).

Axiom dom_unreachable: forall (f:fdef)
  (Hbinf: branchs_in_fdef f) 
  (Hhasentry: getEntryBlock f <> None)
  (l3 : l) s3
  (HuniqF: uniqFdef f)
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hunreach: ~ f ~>* l3),
  sdom f l3 = bound_fdef f.

Axiom pres_sdom: forall 
  (ftrans: fdef -> fdef) 
  (btrans: block -> block)
  (ftrans_spec: forall fh bs, 
    ftrans (fdef_intro fh bs) = fdef_intro fh (List.map btrans bs))
  (btrans_eq_label: forall b, getBlockLabel b = getBlockLabel (btrans b))
  (btrans_eq_tmn: forall b, 
    terminator_match (getTerminator b) (getTerminator (btrans b)))
  (f : fdef) (l5 l0 : l),
  ListSet.set_In l5 (sdom f l0) <->
  ListSet.set_In l5 (sdom (ftrans f) l0).

End ALGDOM.

Module AlgDom_Properties(adom: ALGDOM).

Lemma entry_doms_others: forall (f:fdef) 
  (Hbinf: adom.branchs_in_fdef f) (Huniq: uniqFdef f) entry
  (H: getEntryLabel f = Some entry),
  (forall b (H0: b <> entry /\ reachable f b),
     entry `in` (adom.sdom f b)).
Proof.
  intros.
  assert (Hsdom: strict_domination f entry b).
    apply DecDom.entry_doms_others; auto.
  destruct H0 as [Hneq Hreach].
  apply reachable__in_bound in Hreach; auto.
  apply In_bound_fdef__blockInFdefB in Hreach.
  destruct Hreach as [s HBinF].
  apply getEntryLabel__getEntryBlock in H.
  destruct H as [be [Hentry EQ]]; subst.
  apply entryBlockInFdef in Hentry.
  destruct be; simpl in *.
  eapply adom.sdom_is_complete; eauto.
Qed.

Lemma in_bound_dom__in_bound_fdef: forall l' f l1
  (Hin: l' `in` (adom.sdom f l1)),
  l' `in` (bound_fdef f).
Proof.
  intros. destruct f. eapply adom.sdom_in_bound; eauto.
Qed.

Section sound.

Variable f : fdef.
Hypothesis Hhasentry: getEntryBlock f <> None.

Lemma dom_is_sound : forall
  (l3 : l) (l' : l) s3
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hin : l' `in` (l3 {+} (adom.sdom f l3))),
  f |= l' >>= l3.
Proof.
  unfold domination. autounfold with cfg.
  intros. destruct f as [fh bs].
  remember (getEntryBlock (fdef_intro fh bs)) as R.
  destruct R; try congruence. clear Hhasentry.
  destruct b as [l5 s5].
  intros vl al Hreach.
  generalize dependent s3.
  remember (ACfg.vertexes (successors (fdef_intro fh bs))) as Vs.
  remember (ACfg.arcs (successors (fdef_intro fh bs))) as As.
  unfold ATree.elt, l in *.
  remember (index l3) as v0.
  remember (index l5) as v1.
  generalize dependent bs.
  generalize dependent l3.
  generalize dependent l5.
  induction Hreach; intros; subst.
    inv Heqv0. symmetry in HeqR.
    apply adom.dom_entrypoint in HeqR.
    rewrite HeqR in Hin.
    simpl in Hin. destruct Hin as [Hin | Hin]; tinv Hin; auto.

    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0,
      blockInFdefB (a0, stmts_intro ps0 cs0 tmn0) (fdef_intro fh bs) /\
      In l3 (successors_terminator tmn0)) as J.
      eapply successors__blockInFdefB; eauto.
    destruct J as [ps0 [cs0 [tmn0 [HBinF'' Hinsucc]]]].
    destruct (id_dec l' l3); subst; auto.
    left.
    assert (In l'
      (a0 :: (adom.sdom (fdef_intro fh bs) a0))) as J.
      assert (incl (adom.sdom (fdef_intro fh bs) l3)
                   (a0 :: (adom.sdom (fdef_intro fh bs) a0))) as Hinc.
        eapply adom.dom_successors; eauto.
      simpl in Hin. destruct Hin; try congruence.
      apply Hinc; auto.
    eapply IHHreach in J; eauto 1.
    simpl.
    destruct J as [J | J]; subst; eauto.
Qed.

Lemma sdom_is_sound : forall
  (l3 : l) (l' : l) s3
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hin : l' `in` (adom.sdom f l3)),
  f |= l' >> l3.
Proof. 
  intros.
  eapply dom_is_sound with (l':=l') in HBinF; simpl; eauto.
  unfold strict_domination, domination in *.
  remember (getEntryBlock f) as R.
  destruct R; try congruence.
  destruct b as [l0 ? ? ?].
  intros vl al Hreach.
  assert (Hw':=Hreach).
  apply DWalk_to_dpath in Hreach; auto.
  destruct Hreach as [vl0 [al0 Hp]].
  destruct (id_dec l' l3); subst.
  Case "l'=l3".
    destruct (id_dec l3 l0); subst.
    SCase "l3=l0".
      symmetry in HeqR.
      apply adom.dom_entrypoint in HeqR.
      rewrite HeqR in Hin. inv Hin.
    SCase "l3<>l0".   
      inv Hp; try congruence.
      destruct y as [a0].
      assert (exists ps0, exists cs0, exists tmn0,
        blockInFdefB (a0, stmts_intro ps0 cs0 tmn0) f /\
        In l3 (successors_terminator tmn0)) as J.
        eapply successors__blockInFdefB; eauto.
      destruct J as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
      assert (In l3 (a0 :: (adom.sdom f a0))) as J.
        assert (incl (adom.sdom f l3) (a0 :: (adom.sdom f a0))) as Hinc.
          destruct f. eapply adom.dom_successors; eauto.
        simpl in Hin.
        apply Hinc; auto.
      eapply dom_is_sound in J; try solve [eauto 1 | congruence].
      unfold domination in J.
      rewrite <- HeqR in J.
      assert (Hw:=H).
      apply D_path_isa_walk in Hw.
      apply J in Hw.
      destruct Hw as [Hw | Hw]; subst; auto.
        apply H4 in Hw. inv Hw; try congruence.
        elimtype False. auto.
  Case "l'<>l3".
    apply HBinF in Hw'.
    split; auto. destruct Hw'; subst; auto. congruence.
Qed. 

End sound.

Lemma sdom_isnt_refl : forall
  f (l3 : l) (l' : l) s3
  (Hreach : reachable f l3)
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hin : In l' (adom.sdom f l3)),
  l' <> l3.
Proof. 
  intros.
  eapply sdom_is_sound in Hin; eauto using reachable_has_entry.
  unfold strict_domination, reachable in *.
  autounfold with cfg in *.
  destruct (getEntryBlock f) as [[]|]; try congruence.
  destruct Hreach as [vl [al Hreach]].
  apply Hin in Hreach. tauto.
Qed. 

Definition getEntryBlock_inv f := forall
  (l3 : l)
  (l' : l)
  (ps : phinodes)
  (cs : cmds)
  (tmn : terminator)
  (HBinF : blockInFdefB (l3, stmts_intro ps cs tmn) f = true)
  (Hsucc : In l' (successors_terminator tmn)) a s0
  (H : getEntryBlock f = Some (a, s0)),
  l' <> a.

Lemma sdom_acyclic: forall f
  (HgetEntryBlock_inv : getEntryBlock_inv f)
  l1 l2 s1 s2,
  reachable f l2 ->
  blockInFdefB (l1, s1) f = true ->
  blockInFdefB (l2, s2) f = true ->
  l1 `in` (adom.sdom f l2) ->
  l2 `in` (adom.sdom f l1) ->
  l1 <> l2 ->
  False.
Proof.
  intros.
  assert (strict_domination f l1 l2) as Hdom12.
    eapply sdom_is_sound; eauto using reachable_has_entry.
  assert (strict_domination f l2 l1) as Hdom21.
    eapply sdom_is_sound; eauto using reachable_has_entry.
  eapply DecDom.dom_acyclic in Hdom12; eauto 1.
  apply Hdom12. apply DecDom.sdom_dom; auto.
Qed.

End AlgDom_Properties.

(* The analysis that create trees must ensure that generated trees are
   well-formed. *)
Module Type ALGDOM_WITH_TREE.

Include Type ALGDOM.

Parameter create_dom_tree : fdef -> option (@DTree l).

Axiom dtree_edge_iff_idom: forall (f:fdef)
  (dt: @DTree l)
  (Hcreate: create_dom_tree f = Some dt)
  (le:l) (Hentry: getEntryLabel f = Some le)
  (Hnopreds: (XATree.make_predecessors (successors f)) !!! le = nil)
  (Hwfcfg: branchs_in_fdef f)
  (Huniq: uniqFdef f),
  forall p0 ch0,
    is_dtree_edge eq_atom_dec dt p0 ch0 = true <-> 
      (imm_domination f p0 ch0 /\ reachable f ch0).

Axiom create_dom_tree__wf_dtree: forall (f:fdef)
  (dt: @DTree l)
  (Hcreate: create_dom_tree f = Some dt)
  (le:l) (Hentry: getEntryLabel f = Some le)
  (Hnopreds: (XATree.make_predecessors (successors f)) !!! le = nil)
  (Hwfcfg: branchs_in_fdef f)
  (Huniq: uniqFdef f),
  ADProps.wf_dtree (successors f) le eq_atom_dec dt.

End ALGDOM_WITH_TREE.

