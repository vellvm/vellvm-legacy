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

Module Type ALGDOM.

Parameter dom_query : fdef -> atom -> set atom.

Axiom dom_entrypoint : forall f l0 ps cs tmn
  (Hentry : getEntryBlock f = Some (block_intro l0 ps cs tmn)),
  dom_query f l0 = nil.

Definition branchs_in_fdef f :=
  forall (p : l) (ps0 : phinodes) (cs0 : cmds) 
         (tmn0 : terminator) (l2 : l),
  blockInFdefB (block_intro p ps0 cs0 tmn0) f ->
  In l2 (successors_terminator tmn0) -> In l2 (bound_fdef f).

Axiom entry_doms_others: forall (f:fdef) 
  (Hbinf: branchs_in_fdef f) (Huniq: uniqFdef f) entry
  (H: getEntryLabel f = Some entry),
  (forall b (H0: b <> entry /\ reachable f b),
     ListSet.set_In entry (dom_query f b)).

Axiom dom_query_in_bound: forall fh bs l5, 
  incl (dom_query (fdef_intro fh bs) l5) (bound_blocks bs).

Axiom dom_successors : forall
  (l3 : l) (l' : l) f
  (contents3 contents': ListSet.set atom)
  (Hinscs : In l' (successors f) !!! l3)
  (Heqdefs3 : contents3 = dom_query f l3)
  (Heqdefs' : contents' = dom_query f l'),
  incl contents' (l3 :: contents3).

Axiom sdom_is_complete: forall (f:fdef)
  (Hbinf: branchs_in_fdef f) 
  (l3 : l) (l' : l) ps cs tmn ps' cs' tmn'
  (HuniqF : uniqFdef f)
  (HBinF' : blockInFdefB (block_intro l' ps' cs' tmn') f = true)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hsdom: strict_domination f l' l3),
  In l' (dom_query f l3).

Axiom dom_unreachable: forall (f:fdef)
  (Hbinf: branchs_in_fdef f) 
  (Hhasentry: getEntryBlock f <> None)
  (l3 : l) (l' : l) ps cs tmn
  (HuniqF: uniqFdef f)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hunreach: ~ reachable f l3),
  dom_query f l3 = bound_fdef f.

Axiom pres_dom_query: forall 
  (ftrans: fdef -> fdef) 
  (btrans: block -> block)
  (ftrans_spec: forall fh bs, 
    ftrans (fdef_intro fh bs) = fdef_intro fh (List.map btrans bs))
  (btrans_eq_label: forall b, getBlockLabel b = getBlockLabel (btrans b))
  (btrans_eq_tmn: forall b, 
    terminator_match (getBlockTmn b) (getBlockTmn (btrans b)))
  (f : fdef) (l5 l0 : l),
  ListSet.set_In l5 (dom_query f l0) <->
  ListSet.set_In l5 (dom_query (ftrans f) l0).

End ALGDOM.

Module AlgDom_Properties(adom: ALGDOM).

Lemma in_bound_dom__in_bound_fdef: forall l' f l1
  (Hin: In l' (adom.dom_query f l1)),
  In l' (bound_fdef f).
Proof.
  intros. destruct f. eapply adom.dom_query_in_bound; eauto.
Qed.

Section sound.

Variable f : fdef.
Hypothesis Hhasentry: getEntryBlock f <> None.

Lemma dom_is_sound : forall
  (l3 : l) (l' : l) ps cs tmn
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : In l' (l3::(adom.dom_query f l3))),
  domination f l' l3.
Proof.
  unfold domination. autounfold with cfg.
  intros. destruct f as [fh bs].
  remember (getEntryBlock (fdef_intro fh bs)) as R.
  destruct R; try congruence. clear Hhasentry.
  destruct b as [l5 ps5 cs5 t5].
  intros vl al Hreach.
  generalize dependent ps.
  generalize dependent cs.
  generalize dependent tmn.
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
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) (fdef_intro fh bs) /\
      In l3 (successors_terminator tmn0)) as J.
      eapply successors__blockInFdefB; eauto.
    destruct J as [ps0 [cs0 [tmn0 [HBinF'' Hinsucc]]]].
    destruct (id_dec l' l3); subst; auto.
    left.
    assert (In l'
      (a0 :: (adom.dom_query (fdef_intro fh bs) a0))) as J.
      assert (incl (adom.dom_query (fdef_intro fh bs) l3)
                   (a0 :: (adom.dom_query (fdef_intro fh bs) a0))) as Hinc.
        eapply adom.dom_successors; eauto.
      simpl in Hin. destruct Hin; try congruence.
      apply Hinc; auto.
    eapply IHHreach in J; eauto.
    simpl.
    destruct J as [J | J]; subst; eauto.
Qed.

Lemma sdom_is_sound : forall
  (l3 : l) (l' : l) ps cs tmn
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : In l' (adom.dom_query f l3)),
  strict_domination f l' l3.
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
        blockInFdefB (block_intro a0 ps0 cs0 tmn0) f /\
        In l3 (successors_terminator tmn0)) as J.
        eapply successors__blockInFdefB; eauto.
      destruct J as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
      assert (In l3 (a0 :: (adom.dom_query f a0))) as J.
        assert (incl (adom.dom_query f l3) (a0 :: (adom.dom_query f a0))) as Hinc.
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
  f (l3 : l) (l' : l) ps cs tmn
  (Hreach : reachable f l3)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : In l' (adom.dom_query f l3)),
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
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hsucc : In l' (successors_terminator tmn)) a ps0 cs0 tmn0
  (H : getEntryBlock f = Some (block_intro a ps0 cs0 tmn0)),
  l' <> a.

Lemma sdom_acyclic: forall f
  (HgetEntryBlock_inv : getEntryBlock_inv f)
  l1 l2 ps1 cs1 tmn1 ps2 cs2 tmn2,
  reachable f l2 ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  blockInFdefB (block_intro l2 ps2 cs2 tmn2) f = true ->
  In l1 (adom.dom_query f l2) ->
  In l2 (adom.dom_query f l1) ->
  l1 <> l2 ->
  False.
Proof.
  intros.
  assert (strict_domination f l1 l2) as Hdom12.
    eapply sdom_is_sound; eauto using reachable_has_entry.
  assert (strict_domination f l2 l1) as Hdom21.
    eapply sdom_is_sound; eauto using reachable_has_entry.
  eapply DecDom.dom_acyclic in Hdom12; eauto.
  apply Hdom12. apply DecDom.sdom_dom; auto.
Qed.

End AlgDom_Properties.

Module Type ALGDOM_WITH_TREE.

Include Type ALGDOM.

Parameter create_dom_tree : fdef -> option (@DTree l).

Axiom dtree_edge_iff_idom: forall (f:fdef)
  (dt: @DTree l)
  (Hcreate: create_dom_tree f = Some dt)
  (le:l) (Hentry: getEntryLabel f = Some le)
  (Hnopreds: (XATree.make_predecessors (successors f)) !!! le = nil)
  (Hwfcfg: forall (p : l) (ps0 : phinodes) (cs0 : cmds) 
                  (tmn0 : terminator) (l2 : l),
           blockInFdefB (block_intro p ps0 cs0 tmn0) f ->
           In l2 (successors_terminator tmn0) -> In l2 (bound_fdef f))
  (Huniq: uniqFdef f),
  forall p0 ch0,
    is_dtree_edge eq_atom_dec dt p0 ch0 = true <-> 
      (imm_domination f p0 ch0 /\ reachable f ch0).

Axiom create_dom_tree__wf_dtree: forall (f:fdef)
  (dt: @DTree l)
  (Hcreate: create_dom_tree f = Some dt)
  (le:l) (Hentry: getEntryLabel f = Some le)
  (Hnopreds: (XATree.make_predecessors (successors f)) !!! le = nil)
  (Hwfcfg: forall (p : l) (ps0 : phinodes) (cs0 : cmds) 
                  (tmn0 : terminator) (l2 : l),
           blockInFdefB (block_intro p ps0 cs0 tmn0) f ->
           In l2 (successors_terminator tmn0) -> In l2 (bound_fdef f))
  (Huniq: uniqFdef f),
  ADProps.wf_dtree (successors f) le eq_atom_dec dt.

End ALGDOM_WITH_TREE.

