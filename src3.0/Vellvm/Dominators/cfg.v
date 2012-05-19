Require Import List.
Require Import ListSet.
Require Import Coqlib.
Require Import Metatheory.
Require Import Maps.
Require Import alist.
Require Import Dipaths.
Require Import Program.Tactics.
Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.

Module Cfg (T:TREE).

Module XTree := More_Tree_Properties(T).

Section Cfg.

Variable successors: T.t (list T.elt).

Definition vertexes : V_set :=
fun (v:Vertex) => let '(index n) := v in XTree.in_cfg successors n.

Definition arcs : A_set :=
fun (arc:Arc) =>
  let '(A_ends (index n2) (index n1)) := arc in
  In n2 (XTree.successors_list successors n1).

Variable entry:T.elt.

Definition reachable av : Prop :=
  exists vl: V_list, exists al: A_list, 
     D_walk vertexes arcs (index av) (index entry) vl al.

Lemma reachable_succ: forall
  (n : T.elt) (sc : T.elt) (H1 : reachable n)
  (Hscs : In sc (XTree.successors_list successors n)),
  reachable sc.
Proof.
  intros.
  destruct H1 as [vl [al Hwk]].
  exists (index n::vl). exists (A_ends (index sc) (index n)::al).
  apply DW_step; auto.
    apply XTree.in_succ__in_cfg with (p:=n); auto.
Qed.

Lemma reachable_entry: forall
  (Hincfg: XTree.in_cfg successors entry),
  reachable entry.
Proof.
  intros.
  exists V_nil. exists A_nil. 
  constructor; auto.
Qed.

Lemma reachable_dec: forall n, 
  reachable n \/ ~ reachable n.
Proof. intros. tauto. Qed. (* classic logic *)

Definition domination (n1 n2:T.elt) : Prop :=
  forall vl al,
    D_walk vertexes arcs (index n2) (index entry) vl al ->
    (In (index n1) vl \/ n1 = n2).

Definition strict_domination (n1 n2:T.elt) : Prop :=
domination n1 n2 /\ n1 <> n2.

Definition non_sdomination (n1 n2:T.elt) : Prop :=
  exists vl, exists al,
    D_walk vertexes arcs (index n2) (index entry) vl al /\
    ~ In (index n1) vl.

Lemma non_sdomination_refl : forall 
  (Hdec: forall x y : T.elt, {x = y} + {x <> y})
  l1 (Hneq: l1 <> entry)
  (Hreach: reachable l1),
  non_sdomination l1 l1.
Proof.
  unfold reachable, non_sdomination.
  intros.
  destruct Hreach as [vl [al Hreach]].
  apply DWalk_to_dpath in Hreach; auto.
    destruct Hreach as [vl0 [al0 Hp]].
    exists vl0. exists al0.
    split.
      apply D_path_isa_walk; auto.
      eapply DP_endx_ninV; eauto. congruence.
Qed.

End Cfg. End Cfg.

Module ACfg := Cfg(ATree).

Import LLVMsyntax.
Import LLVMinfra.

Fixpoint successors_blocks (bs: blocks) : ATree.t ls :=
match bs with
| nil => ATree.empty ls
| block_intro l0 _ _ tmn :: bs' =>
    ATree.set l0 (successors_terminator tmn) (successors_blocks bs')
end.

Definition successors (f: fdef) : ATree.t ls :=
let '(fdef_intro _ bs) := f in
successors_blocks bs.

Fixpoint bound_blocks (bs: blocks) : set atom :=
match bs with
| nil => empty_set _
| block_intro l0 _ _ tmn :: bs' => l0::(bound_blocks bs')
end.

Definition bound_fdef (f: fdef) : set atom :=
let '(fdef_intro _ bs) := f in
bound_blocks bs.

Definition vertexes_fdef (f:fdef) : V_set :=
ACfg.vertexes (successors f).

Definition arcs_fdef (f:fdef) : A_set :=
ACfg.arcs (successors f).

Definition reachable (f:fdef) (l0:l) : Prop :=
match getEntryBlock f with
| Some (block_intro entry _ _ _) =>
  ACfg.reachable (successors f) entry l0
| _ => false
end.

Definition domination (f:fdef) (l1 l2:l) : Prop :=
match getEntryBlock f with
| Some (block_intro entry _ _ _) =>
  ACfg.domination (successors f) entry l1 l2
| _ => False
end.

Hint Unfold ACfg.domination ACfg.reachable ACfg.non_sdomination: cfg.

Definition strict_domination (f:fdef) (l1 l2:l) : Prop :=
domination f l1 l2 /\ l1 <> l2.

Definition imm_domination (f:fdef) (l1 l2:l) : Prop :=
strict_domination f l1 l2 /\
forall l0, strict_domination f l0 l2 -> domination f l0 l1.

Definition predecessors (f: fdef) : ATree.t ls :=
XATree.make_predecessors (successors f).

Definition has_no_predecessors (f: fdef) (b:block) : bool :=
match (predecessors f) !!! (getBlockLabel b) with
| nil => true
| _ => false
end.

Lemma entry_in_vertexes : forall f l0 ps cs tmn
  (Hentry : getEntryBlock f = Some (block_intro l0 ps cs tmn)),
  vertexes_fdef f (index l0).
Proof.
  intros.
  unfold vertexes_fdef, ACfg.vertexes. destruct f as [f b].
  destruct b; simpl in *.
    congruence.
    inv Hentry. 
    left.
    apply ACfg.XTree.parents_of_tree__in_successors.
    rewrite ATree.gss. eauto.
Qed.

Lemma in_successors_blocks__in_bound_blocks: forall (n : ATree.elt) (s : ls) 
  (bs : blocks) (Hinscs : (successors_blocks bs) ! n = Some s),
  In n (bound_blocks bs).
Proof.
  induction bs as [|[] bs]; simpl in *; intros.
    rewrite ATree.gempty in Hinscs. congruence.

    rewrite ATree.gsspec in Hinscs.
    destruct_if; auto.
Qed.

Lemma in_bound_blocks__in_successors_blocks: forall (n : ATree.elt)
  (bs : blocks) (Hin: In n (bound_blocks bs)),
  exists s, (successors_blocks bs) ! n = Some s.
Proof.
  induction bs as [|[] bs]; simpl in *; intros.
    tauto.

    rewrite ATree.gsspec.
    destruct_if; eauto.
    destruct Hin; try solve [auto | congruence].
Qed.

Lemma in_parents__in_bound: forall bs n 
  (Hparents: In n (XATree.parents_of_tree (successors_blocks bs))), 
  In n (bound_blocks bs).
Proof.
  intros.
  apply XATree.parents_of_tree__in_successors in Hparents.
  destruct Hparents as [s Hinscs].
  eapply in_successors_blocks__in_bound_blocks; eauto.
Qed.

Lemma in_bound__in_parents: forall bs n 
  (Hin: In n (bound_blocks bs)), 
  In n (XATree.parents_of_tree (successors_blocks bs)).
Proof.
  intros.
  apply in_bound_blocks__in_successors_blocks in Hin.
  apply XATree.parents_of_tree__in_successors in Hin; auto.
Qed.

Lemma in_parents__in_bound_fdef: forall f n 
  (Hparents: In n (XATree.parents_of_tree (successors f))), 
  In n (bound_fdef f).
Proof.
  destruct f.
  intros.
  apply in_parents__in_bound; auto.
Qed.

Lemma in_bound_fdef__in_parents: forall f n 
  (Hin: In n (bound_fdef f)), 
  In n (XATree.parents_of_tree (successors f)).
Proof.
  destruct f.
  intros.
  apply in_bound__in_parents; auto.
Qed.

Lemma successors__blockInFdefB : forall l0 a f,
  In l0 (successors f) !!! a ->
  exists ps0, exists cs0, exists tmn0,
    blockInFdefB (block_intro a ps0 cs0 tmn0) f /\
    In l0 (successors_terminator tmn0).
Proof.
  destruct f as [fh bs]. simpl.
  unfold XATree.successors_list.
  induction bs as [|a0 bs]; simpl; intro.
    rewrite ATree.gempty in H. inv H.

    destruct a0 as [l1 p c t].
    destruct (id_dec l1 a); subst.
      rewrite ATree.gss in H.
      exists p. exists c. exists t.
      split; auto.
        eapply orb_true_iff. left. apply blockEqB_refl.

      rewrite ATree.gso in H; auto.
      apply IHbs in H; auto.
      destruct H as [ps0 [cs0 [tmn0 [J1 J2]]]].
      exists ps0. exists cs0. exists tmn0.
      split; auto.
        eapply orb_true_iff; eauto.
Qed.

Lemma successors_blocks__blockInFdefB : forall l0 a fh bs,
  In l0 (successors_blocks bs) !!! a ->
  exists ps0, exists cs0, exists tmn0,
    blockInFdefB (block_intro a ps0 cs0 tmn0) (fdef_intro fh bs) /\
    In l0 (successors_terminator tmn0).
Proof.
  intros.
  apply successors__blockInFdefB; auto.
Qed.

Lemma successors_terminator__successors_blocks : forall
  (bs : blocks)
  (l0 : l)
  (cs : phinodes)
  (ps : cmds)
  (tmn : terminator)
  (l1 : l)
  (HuniqF : uniqBlocks bs)
  (HbInF : InBlocksB (block_intro l0 cs ps tmn) bs)
  (Hin : In l1 (successors_terminator tmn)),
  successors_terminator tmn = (successors_blocks bs) !!! l0.
Proof.
  intros.
  induction bs.
    inversion HbInF.

    assert (J:=HuniqF).
    simpl_env in J.
    apply uniqBlocks_inv in J.
    destruct J as [J1 J2].
    simpl in *.
    apply orb_prop in HbInF.
    destruct a.
    destruct HbInF as [HbInF | HbInF].
      unfold blockEqB in HbInF.
      apply sumbool2bool_true in HbInF. inv HbInF.
      unfold XATree.successors_list.
      rewrite ATree.gss. auto.

      apply IHbs in J2; auto.
      unfold XATree.successors_list in *.
      destruct HuniqF as [J _].
      inv J.
      rewrite ATree.gso; auto.
        clear - HbInF H1.
        eapply InBlocksB__NotIn; eauto.
Qed.

Lemma successor_in_arcs : forall l0 cs ps tmn f l1
  (HuniqF : uniqFdef f)
  (HbInF : blockInFdefB (block_intro l0 cs ps tmn) f)
  (Hin : In l1 (successors_terminator tmn)),
  arcs_fdef f (A_ends (index l1) (index l0)).
Proof.
  intros.
  unfold arcs_fdef.
  destruct f as [fh bs]. apply uniqF__uniqBlocks in HuniqF.
  simpl.
  erewrite <- successors_terminator__successors_blocks; eauto.
Qed.

Lemma blockInFdefB_in_bound_fdef : forall l0 cs ps tmn f
  (HbInF : blockInFdefB (block_intro l0 cs ps tmn) f),
  In l0 (bound_fdef f).
Proof.
  intros.
  unfold bound_fdef.
  destruct f as [f b].
  generalize dependent cs.
  generalize dependent ps.
  generalize dependent tmn.
  generalize dependent l0.
  induction b; simpl in *; intros.
    congruence.

    destruct a.
    apply orb_prop in HbInF.
    destruct HbInF as [HbInF | HbInF].
      unfold blockEqB in HbInF.
      apply sumbool2bool_true in HbInF. inv HbInF.
      simpl. auto.

      apply IHb in HbInF.
      simpl. auto.
Qed.

Lemma blockInFdefB_in_vertexes : forall l0 cs ps tmn f
  (HbInF : blockInFdefB (block_intro l0 cs ps tmn) f),
  vertexes_fdef f (index l0).
Proof.
  intros.
  left.
  apply blockInFdefB_in_bound_fdef in HbInF.
  apply in_bound_fdef__in_parents; auto.
Qed.

Lemma successors_predOfBlock : forall f l1 ps1 cs1 tmn1 l0 ps0 cs0 tmn0,
  uniqFdef f ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  In l0 (successors_terminator tmn1) ->
  In l1 (predOfBlock (block_intro l0 ps0 cs0 tmn0) (genBlockUseDef_fdef f)).
Proof.
  unfold predOfBlock.
  destruct f as [f b].
  destruct f as [fnattrs5 typ5 id5 args5 varg5].
  intros.
  destruct H as [H _].
  generalize dependent l1.
  generalize dependent ps1.
  generalize dependent cs1.
  generalize dependent tmn1.
  generalize dependent l0.
  generalize dependent ps0.
  generalize dependent cs0.
  generalize dependent tmn0.
  induction b as [|a0 b]; intros; simpl in *.
    inversion H0.

    assert (G:=H). simpl_env in G.
    apply uniqBlocks_inv in G.
    destruct G as [G1 G2].
    destruct a0 as [l5 p c t0]. simpl.
    apply orb_prop in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0.
      inv H0.
      destruct t0 as [i0 t0 v0|i0|i0 v0 l2 l3|i0 l2|i0]; auto.
        apply IHb with (ps1:=p)(cs1:=c)(tmn1:=insn_return i0 t0 v0); auto.
        apply IHb with (ps1:=p)(cs1:=c)(tmn1:=insn_return_void i0); auto.

        simpl in H1.
        destruct H1 as [H1 | [H1 | H1]]; subst.
          assert (J:=@lookupAL_update_udb_eq (update_udb nil l5 l3) l5 l0).
          destruct J as [ls0 [J1 J2]].
          apply lookupAL_genBlockUseDef_blocks_spec with (bs:=b) in J1; auto.
          destruct J1 as [ls1 [J1 J3]].
          rewrite J1. apply J3; auto.

          assert (J:=@lookupAL_update_udb_eq nil l5 l0).
          destruct J as [ls0 [J J0]].
          apply lookupAL_update_udb_spec with (l1:=l5)(l2:=l2) in J; auto.
          destruct J as [ls1 [J J1]].
          apply lookupAL_genBlockUseDef_blocks_spec with (bs:=b) in J; auto.
          destruct J as [ls2 [J J2]].
          rewrite J. apply J2. apply J1. auto.

          inversion H1.
        simpl in H1.
        destruct H1 as [H1 | H1]; subst.
          assert (J:=@lookupAL_update_udb_eq nil l5 l0).
          destruct J as [ls0 [J J0]].
          apply lookupAL_genBlockUseDef_blocks_spec with (bs:=b) in J; auto.
          destruct J as [ls2 [J J2]].
          rewrite J. apply J2. auto.

          inversion H1.

        apply IHb with (ps1:=p)(cs1:=c)(tmn1:=insn_unreachable i0); auto.

      eapply IHb in H1; eauto.
        remember (lookupAL (list l) (genBlockUseDef_blocks b nil) l0) as R.
        destruct R as [l4|]; try solve [inversion H1].
        destruct H as [J1 J2].
        simpl in J1.
        inv J1.
        apply InBlocksB_In in H0.
        destruct (eq_atom_dec l1 l5); subst.
          contradict H0; auto.

          clear - HeqR H1.
          simpl.
          assert (usedef_block_inc nil
            (match t0 with
             | insn_return _ _ _ => nil
             | insn_return_void _ => nil
             | insn_br _ _ l2 l3 => update_udb (update_udb nil l5 l3) l5 l2
             | insn_br_uncond _ l2 => update_udb nil l5 l2
             | insn_unreachable _ => nil
             end)) as J.
            intros x A J. inversion J.
          apply genBlockUseDef_blocks_inc with (bs:=b) in J.
          symmetry in HeqR.
          apply J in HeqR.
          destruct HeqR as [l2 [J1 J2]].
          rewrite J1. apply J2 in H1; auto.
Qed.

Lemma blockInFdefB__successors : forall a ps0 cs0 tmn0 f (Huniq: uniqFdef f),
  blockInFdefB (block_intro a ps0 cs0 tmn0) f ->
  (successors f) ! a = Some (successors_terminator tmn0).
Proof.
  destruct f as [[] bs]. simpl.
  intros [J _].
  unfold uniqBlocks in J.
  destruct J as [J _].
  induction bs as [|a1 bs]; simpl; intros.
    congruence.

    destruct a1 as [l0 ps1 cs1 tmn1].
    apply orb_true_iff in H.
    destruct H as [H | H].
      apply blockEqB_inv in H. inv H.
      rewrite ATree.gss. auto.

      assert (J':=J). inv J'.
      simpl in J. simpl_env in J.
      apply IHbs in H3; auto.
      apply InBlocksB_In in H.
      apply infrastructure_props.NoDup_disjoint with (i0:=a) in J; auto.
      destruct (id_dec l0 a); subst.
        contradict J. simpl. auto.

        rewrite ATree.gso; auto.
Qed.

Section reachable__in_bound.

Variable f:fdef.
Hypothesis branches_in_bound_fdef: forall p ps0 cs0 tmn0 l2
  (J3 : blockInFdefB (block_intro p ps0 cs0 tmn0) f)
  (J4 : In l2 (successors_terminator tmn0)),
  In l2 (bound_fdef f).

Lemma reachable__in_bound: forall a (Hrd: reachable f a),
  In a (bound_fdef f).
Proof.
  intros.
  unfold reachable in Hrd.
  match goal with
  | H: match ?e with
       | Some _ => _
       | None => is_true false
       end |- _ => remember e as R; destruct R; tinv H
  end.
  destruct b.
  destruct Hrd as [vl [al Hrd]].
  apply Dipaths.DW_endx_inv in Hrd. 
  destruct Hrd as [Hrd | Hrd].
    apply in_parents__in_bound_fdef in Hrd; auto.

    apply XATree.children_of_tree__in_successors in Hrd.
    destruct Hrd as [p [sc [Hrd Hin]]].
    assert (In a (successors f) !!! p) as Hin'.
      unfold XATree.successors_list.
      unfold ATree.elt, l in *.
      rewrite Hrd. auto.
    apply successors__blockInFdefB in Hin'.
    destruct_conjs. eauto.
Qed.

End reachable__in_bound.

Lemma arcs_fdef_inv : forall f a1 a2,
  arcs_fdef f (A_ends (index a2) (index a1)) ->
  In a2 ((successors f)!!!a1).
Proof. auto. Qed.

Lemma In_bound_fdef__blockInFdefB: forall f l3
  (Hin: In l3 (bound_fdef f)),
  exists ps, exists cs, exists tmn,
    blockInFdefB (block_intro l3 ps cs tmn) f = true.
Proof.
  destruct f as [[] bs].
  simpl. intros.
  induction bs as [|[l0 ps0 cs0 tmn0]]; simpl in *.
    tauto.

    destruct Hin as [Hin | Hin]; subst.
      exists ps0. exists cs0. exists tmn0.
      apply orb_true_intro.
      left. solve_refl.      

      apply IHbs in Hin.
      destruct Hin as [ps [cs [tmn Hin]]].
      exists ps. exists cs. exists tmn.
      apply orb_true_intro. auto.
Qed.

Lemma successors_predOfBlock': forall (f : fdef) b (Huniq : uniqFdef f) 
  (l1 : atom)
  (Hscs : In (getBlockLabel b) ((successors f) !!! l1)),
  In l1 (predOfBlock b (genBlockUseDef_fdef f)).
Proof.
  intros.
  destruct b as [l0 ps0 cs0 tmn0].
  apply successors__blockInFdefB in Hscs.
  destruct Hscs as [ps1 [cs1 [tmn1 [HBinF Hintmn]]]].
  eapply successors_predOfBlock with (ps0:=ps0)(cs0:=cs0)(tmn0:=tmn0) 
    in Hintmn; eauto.
Qed.

Lemma successors_predecessors_of_block : forall f l1 ps1 cs1 tmn1 l0,
  uniqFdef f ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  In l0 (successors_terminator tmn1) ->
  In l1 ((predecessors f) !!! l0).
Proof.
  unfold predecessors.
  intros.
  apply XATree.make_predecessors_correct; auto.
  unfold XATree.successors_list.
  erewrite blockInFdefB__successors; eauto.
Qed.

Lemma successors_predecessors_of_block': forall (f : fdef) b (Huniq : uniqFdef f) 
  (l1 : atom)
  (Hscs : In (getBlockLabel b) ((successors f) !!! l1)),
  In l1 ((predecessors f) !!! (getBlockLabel b)).
Proof.
  intros.
  destruct b as [l0 ps0 cs0 tmn0].
  apply successors__blockInFdefB in Hscs.
  destruct Hscs as [ps1 [cs1 [tmn1 [HBinF Hintmn]]]].
  eapply successors_predecessors_of_block in Hintmn; eauto.
Qed.

Lemma has_no_predecessors_tinv: forall f b
  (Hnpred: has_no_predecessors f b = true),
  (predecessors f) !!! (getBlockLabel b) = nil.
Proof.
  unfold has_no_predecessors.
  intros.
  destruct (predecessors f) !!! (getBlockLabel b); tinv Hnpred; auto.
Qed.

Lemma successors__successors_terminator : forall scs a f
  (H: Some scs = (successors f) ! a),
  exists ps0, exists cs0, exists tmn0,
    blockInFdefB (block_intro a ps0 cs0 tmn0) f /\
    scs = successors_terminator tmn0.
Proof.
  destruct f as [fh bs]. simpl.
  induction bs as [|a0 bs]; simpl; intro.
    rewrite ATree.gempty in H. inv H.

    destruct a0 as [l1 p c t].
    destruct (id_dec l1 a); subst.
      rewrite ATree.gss in H.
      inv H.
      exists p. exists c. exists t.
      split; auto.
        eapply orb_true_iff. left. apply blockEqB_refl.

      rewrite ATree.gso in H; auto.
      apply IHbs in H; auto.
      destruct H as [ps0 [cs0 [tmn0 [J1 J2]]]].
      exists ps0. exists cs0. exists tmn0.
      split; auto.
        eapply orb_true_iff; eauto.
Qed.

Definition predecessors_dom__uniq_prop 
  (scs:ATree.t ls) (pds: ATree.t ls) : Prop :=
(forall l1 l2, In l1 pds !!! l2 -> In l2 scs !!! l1) /\
forall l0 (Huniq: forall l1, NoDup (scs !!! l1)), 
  NoDup (pds !!! l0).

Lemma predecessors_dom__uniq_aux_helper: forall m k (v:list atom)
  (Herr : m ! k = None)
  (Huniq1 : forall l1, NoDup ((ATree.set k v m) !!! l1)),
  NoDup v /\ forall l1, NoDup (m !!! l1).
Proof.
  intros.
  split.
    assert (J:=Huniq1 k).
    unfold XATree.successors_list in J.
    rewrite ATree.gsspec in J.
    destruct (ATree.elt_eq k k); try congruence.

    intros l0.
    assert (J:=Huniq1 l0).
    unfold XATree.successors_list in J.
    rewrite ATree.gsspec in J.
    unfold XATree.successors_list.
    destruct (ATree.elt_eq l0 k); subst; auto.
      rewrite Herr. auto.
Qed.

Lemma add_successors_dom__uniq: forall
  (m : ATree.t (list atom))
  (k : ATree.elt)
  (l0 : atom)
  (v2 v1 : list atom)
  (a : ATree.t (list atom))
  (H : forall l1 l2 : atom, 
          In l1 a !!! l2 -> 
          (l1 <> k -> In l2 m !!! l1) /\
          (l1 = k -> In l2 v1))
  (G1 : NoDup (v1++v2)) 
  (J : NoDup a !!! l0),
  NoDup (XATree.add_successors a k v2) !!! l0.
Proof.
  induction v2; simpl; intros; auto.
    rewrite_env ((v1++[a])++v2) in G1.
    apply IHv2 with (v1:=v1++[a]); clear IHv2; auto.
    Case "1".
      intros l1 l2 Hin.
      unfold XATree.successors_list in Hin.
      destruct (id_dec a l2); subst.
      SCase "1.1".
        rewrite ATree.gss in Hin.
        destruct_in Hin.
        SSCase "1.1.1".
          split; intro; try congruence.
            xsolve_in_list.

        SSCase "1.1.2".
          apply H in Hin.
          destruct Hin as [Hin1 Hin2].
          split; auto.
            intros EQ; subst.
            xsolve_in_list.

      SCase "1.2".
        rewrite ATree.gso in Hin; auto.
        apply H in Hin.
        destruct Hin as [Hin1 Hin2].
        split; auto.
          intros EQ; subst.
          xsolve_in_list.

    Case "2".
      unfold XATree.successors_list in J.
      unfold XATree.successors_list.
      destruct (id_dec a l0); subst.
      SCase "2.1".
        rewrite ATree.gss.
        unfold ATree.elt.
        remember (a0 ! l0) as R.
        destruct R; auto.
          constructor; auto.
            intro Hin.
            assert (In k (a0 !!! l0)) as Hin'.
              unfold XATree.successors_list.
              rewrite <- HeqR. auto.
            apply_clear H in Hin'.
            destruct Hin' as [_ Hin'].
            apply NoDup_inv in G1. destruct G1 as [G1 _].
            eapply NoDup_disjoint in G1; simpl; eauto.

      SCase "2.2".
        rewrite ATree.gso; auto.
Qed.

Lemma predecessors_dom__uniq_aux: forall scs, 
  predecessors_dom__uniq_prop scs (XATree.make_predecessors scs).
Proof.
  intros.
  unfold XATree.make_predecessors.
  apply ATree_Properties.fold_rec.
  Case "1".
    unfold predecessors_dom__uniq_prop. 
    intros m m' a Heq [IH1 IH2].
    split.
    SCase "1.1".
      intros l1 l2.
      intros.
      erewrite XATree.eq_eli__eq_successors_list; eauto.

    SCase "1.2".
      intros l0 Huniq.
      apply IH2 with (l0:=l0).
        intros l1.
        assert (J:=Huniq l1).
        erewrite XATree.eq_eli__eq_successors_list; eauto.

  Case "2".
    unfold predecessors_dom__uniq_prop.
    unfold XATree.successors_list.
    split; intros; repeat rewrite ATree.gempty.
      tauto.
      auto.

  Case "3".
    unfold predecessors_dom__uniq_prop.
    intros m a k v Herr Hkh [IH1 IH2].
    split.
    SCase "3.1".
      clear - IH1 Herr.
      intros. eapply XATree.add_successors_correct''; eauto.

    SCase "3.2".
      intros l0 Huniq.
      assert (G:=Huniq).
      apply predecessors_dom__uniq_aux_helper in G; auto.
      destruct G as [G1 G2].
      apply IH2 with (l0:=l0) in G2; auto.
        clear - G1 G2 IH1 Herr.
        eapply add_successors_dom__uniq with (v1:=nil)(m:=m); eauto.
          intros l1 l2 Hin.
          split; auto.
            intro EQ; subst.
            apply IH1 in Hin.
            unfold XATree.successors_list in Hin.
            change l with ATree.elt in Hin.
            rewrite Herr in Hin. tauto.
Qed.

Lemma make_predecessors_dom__uniq: forall scs l0
  (Huniq: forall l1, NoDup (scs !!! l1)), 
  NoDup ((XATree.make_predecessors scs) !!! l0).
Proof.
  intros.
  assert (J:=predecessors_dom__uniq_aux scs).
  unfold predecessors_dom__uniq_prop in J. destruct J; auto.
Qed.
