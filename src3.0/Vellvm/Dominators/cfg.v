Require Import List.
Require Import ListSet.
Require Import Coqlib.
Require Import Metatheory.
Require Import Maps.

Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
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

Require Import Dipaths.

Definition vertexes_fdef (f:fdef) : V_set :=
fun (v:Vertex) => let '(index a) := v in In a (bound_fdef f).

Definition arcs_fdef (f:fdef) : A_set :=
fun (arc:Arc) =>
  let '(A_ends (index a2) (index a1)) := arc in
  In a2 ((successors f)!!!a1).

Lemma entry_in_vertexes : forall f l0 ps cs tmn
  (Hentry : getEntryBlock f = Some (block_intro l0 ps cs tmn)),
  vertexes_fdef f (index l0).
Proof.
  intros.
  unfold vertexes_fdef. unfold bound_fdef. destruct f as [f b].
  destruct b; simpl in *.
    congruence.
    inv Hentry. simpl. auto.
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

Lemma in_parents__in_bound: forall bs n 
  (Hparents: In n (XATree.parents_of_tree (successors_blocks bs))), 
  In n (bound_blocks bs).
Proof.
  intros.
  apply XATree.parents_of_tree__in_successors in Hparents.
  destruct Hparents as [s Hinscs].
  eapply in_successors_blocks__in_bound_blocks; eauto.
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

Lemma blockInFdefB_in_vertexes : forall l0 cs ps tmn f
  (HbInF : blockInFdefB (block_intro l0 cs ps tmn) f),
  vertexes_fdef f (index l0).
Proof.
  intros.
  unfold vertexes_fdef, bound_fdef.
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

Definition reachable (f:fdef) (l0:l) : Prop :=
match getEntryBlock f with
| Some (block_intro entry _ _ _) =>
  let vertexes := vertexes_fdef f in
  let arcs := arcs_fdef f in
  exists vl: V_list, exists al: A_list,
    D_walk vertexes arcs (index l0) (index entry) vl al
| _ => false
end.

Definition domination (f:fdef) (l1 l2:l) : Prop :=
match getEntryBlock f with
| Some (block_intro entry _ _ _) =>
  let vertexes := vertexes_fdef f in
  let arcs := arcs_fdef f in
  forall vl al,
    D_walk vertexes arcs (index l2) (index entry) vl al ->
    (In (index l1) vl \/ l1 = l2)
| _ => False
end.

Definition strict_domination (f:fdef) (l1 l2:l) : Prop :=
domination f l1 l2 /\ l1 <> l2.

Definition imm_domination (f:fdef) (l1 l2:l) : Prop :=
strict_domination f l1 l2 /\
forall l0, strict_domination f l0 l2 -> domination f l0 l1.

