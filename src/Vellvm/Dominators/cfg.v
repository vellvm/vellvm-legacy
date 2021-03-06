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
Require Import Relations.Relation_Operators.
Require Import Relations.Operators_Properties.

(* This file defines control-flow graphs. *)

(* Properties of closure and transition of relations. *)
Lemma step_clos_refl_trans_1n__clos_trans_1n: forall A (R:A->A->Prop) y z
  (Hclos: clos_refl_trans_1n A R y z) x (Hrel: R x y),
  clos_trans_1n A R x z.
Proof.
  induction 1; simpl; intros.
    econstructor; eauto.
    apply Relation_Operators.t1n_trans with (y:=x); auto.
Qed.

Lemma step_clos_refl_trans__clos_trans: forall A (R:A->A->Prop) y z
  (Hclos: clos_refl_trans A R y z) x (Hrel: R x y),
  clos_trans A R x z.
Proof.
  intros.
  apply clos_t1n_trans.
  apply clos_rt_rt1n_iff in Hclos.
  eapply step_clos_refl_trans_1n__clos_trans_1n; eauto.
Qed.

Lemma clos_refl_trans__eq_or_clos_trans: forall A (R:A->A->Prop) x y
  (Hclos: clos_refl_trans A R x y),
  x = y \/ clos_trans A R x y.
Proof.
  induction 1; simpl; intros; auto.
    right. econstructor; eauto.
    destruct IHHclos1 as [EQ1 | IHHclos1]; subst.
      destruct IHHclos2 as [EQ2 | IHHclos2]; subst; auto.
      destruct IHHclos2 as [EQ2 | IHHclos2]; subst; auto.
        right. eapply t_trans; eauto.
Qed.

(* The Cfg module defines control-flow graphs, and is parameterized by a tree 
   data type for representing CFGs. *)
Module Cfg (T:TREE).

Module XTree := More_Tree_Properties(T).

Section Cfg.
(* A map from an id to its successors. *)
Variable successors: T.t (list T.elt).
(* Nodes in the CFG *)
Definition vertexes : V_set :=
fun (v:Vertex) => let '(index n) := v in XTree.in_cfg successors n.
(* Edges of the CFG *)
Definition arcs : A_set :=
fun (arc:Arc) =>
  let '(A_ends (index n2) (index n1)) := arc in
  In n2 (XTree.successors_list successors n1).
(* The entry point of the CFG. *)
Variable entry:T.elt.
(* The node av is reachable from entry. *)
Definition reachable av : Prop :=
  exists vl: V_list, exists al: A_list, 
     D_walk vertexes arcs (index av) (index entry) vl al.
(* n1 dominates n2. *)
Definition domination (n1 n2:T.elt) : Prop :=
  forall vl al,
    D_walk vertexes arcs (index n2) (index entry) vl al ->
    (In (index n1) vl \/ n1 = n2).
(* n1 strictly dominates n2. *)
Definition strict_domination (n1 n2:T.elt) : Prop :=
  forall vl al,
    D_walk vertexes arcs (index n2) (index entry) vl al ->
    (In (index n1) vl /\ n1 <> n2).
(* n1 does not strictly dominates n2. *)
Definition non_sdomination (n1 n2:T.elt) : Prop :=
  exists vl, exists al,
    D_walk vertexes arcs (index n2) (index entry) vl al /\
    ~ In (index n1) vl.
(* n1 immediately dominates n2. *)
Definition imm_domination (n1 n2:T.elt) : Prop :=
  strict_domination n1 n2 /\
  forall n0, strict_domination n0 n2 -> domination n0 n1.
(* We assume that the names of CFG nodes are decidable. *)
Hypothesis Hdec: forall x y : T.elt, {x = y} + {x <> y}.
(* Properties of reachability. *)
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

Lemma reachable_pred: forall n 
  (Hreach: reachable n) (Hneq: n <> entry),
  exists p, In n (XTree.successors_list successors p) /\ reachable p.
Proof.
  intros.
  destruct Hreach as [vl [al Hreach]].
  inv Hreach; try congruence.
  destruct y as [y].
  exists y. 
  unfold reachable.
  split; eauto.
Qed.

Lemma reachable_is_in_cfg: forall n (Hreach: reachable n), 
  XTree.in_cfg successors n.
Proof.
  intros.
  destruct Hreach as [vl [al Hreach]].
  apply DW_endx_inv in Hreach; auto.
Qed.

(* Properties of domination relations. *)
Lemma non_sdomination_refl : forall 
  n1 (Hneq: n1 <> entry)
  (Hreach: reachable n1),
  non_sdomination n1 n1.
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

Lemma dom_is_refl: forall n1, domination n1 n1.
Proof. unfold domination. auto. Qed.

Lemma dom_tran: forall n1 n2 n3
  (H: domination n1 n2) (H0: domination n2 n3), domination n1 n3.
Proof.
  intros.
  intros vl al Hw.
  destruct (Hdec n1 n3); auto.
  left.
  assert (Hw':=Hw).
  apply H0 in Hw'.
  destruct Hw' as [Hw' | Hw']; subst.
    apply DW_extract with (x:=index n2)(eq_a_dec:=Hdec) in Hw; 
      simpl; auto.
    destruct Hw as [al' Hw].
    assert (Hw'':=Hw).
    apply H in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; auto.
    destruct (Hdec n1 n2); subst; auto.
    apply V_extract_spec in Hw''; try congruence.
    simpl in Hw''. 
    destruct Hw'' as [Hw'' | Hw'']; auto.
      uniq_result. congruence.

    assert (Hw'':=Hw).
    apply H in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; congruence.
Qed.

Lemma everything_dominates_unreachable_blocks :
  forall n1 n2 (Hreach: ~ reachable n2),
  domination n1 n2.
Proof.
  unfold reachable. 
  intros. intros vl al Hreach'.
  contradict Hreach. eauto.
Qed.

Lemma dom_reachable : forall n1 n2
  (H: reachable n2) (H0: domination n1 n2), reachable n1.
Proof.
  intros.
  destruct H as [vl [al H]].
  assert (H':=H).
  apply H0 in H'.
  apply DW_extract with (x:=index n1)(eq_a_dec:=Hdec) in H; simpl; auto.
    destruct H as [al' H].
    exists (V_extract Hdec (index n1) (index n2 :: vl)). exists al'. auto.

    destruct H' as [H' | H']; subst; auto.
Qed.

Lemma idom_sdom: forall l1 l2 (Hdom12 : imm_domination l1 l2),
  strict_domination l1 l2.
Proof.
  intros. destruct Hdom12. auto.
Qed.

Lemma sdom_isnt_refl: forall n1 n2 (Hreach: reachable n2)
  (Hdom12 : strict_domination n1 n2),
  n1 <> n2.
Proof.
  intros.
  destruct Hreach as [vl [al Hreach]].
  apply Hdom12 in Hreach. 
  tauto.
Qed.

Lemma everything_sdominates_unreachable_blocks :
  forall n1 n2 (Hreach: ~ reachable n2),
  strict_domination n1 n2.
Proof.
  unfold reachable. 
  intros.
  intros vl al Hreach'.
  contradict Hreach. eauto.
Qed.

Lemma sdom_reachable : forall n1 n2
  (H: reachable n2) (H0: strict_domination n1 n2), reachable n1.
Proof.
  intros.
  destruct H as [vl [al H]].
  assert (H':=H).
  apply H0 in H'. destruct H' as [J1 J2].
  apply DW_extract with (x:=index n1)(eq_a_dec:=Hdec) in H; 
    simpl; auto.
  destruct H as [al' H].
  exists (V_extract Hdec (index n1) (index n2 :: vl)). exists al'.
  auto.
Qed.

Lemma sdom_dom: forall n1 n2
  (H: strict_domination n1 n2), domination n1 n2.
Proof.
  intros.
  intros vl al H0. apply H in H0. destruct H0; auto.
Qed.

Lemma dom_sdom: forall n1 n2
  (H: domination n1 n2) (H0: n1 <> n2), strict_domination n1 n2.
Proof.
  intros.
  intros vl al H1. apply H in H1.
  destruct H1 as [H1 | H1]; subst; auto.
    congruence.
Qed.

Section dom_acyclic_tran.

Hypothesis entry_has_no_preds : forall a0
  (Hin: In entry (XTree.successors_list successors a0)),
  False.

Lemma dom_acyclic: forall n1 n2
  (H: reachable n2) (H0: strict_domination n1 n2),
  ~ domination n2 n1.
Proof.
  intros. 
  destruct H as [vl [al Hw]].
  apply DWalk_to_dpath in Hw; auto.
  destruct Hw as [vl0 [al0 Hp]].
  assert (Hw:=Hp).
  apply D_path_isa_walk in Hw.
  assert (Hw':=Hw).
  apply H0 in Hw'.
  destruct Hw' as [J1 J2].
  intros J.
  apply DW_extract with (x:=index n1)(eq_a_dec:=Hdec) in Hw; simpl; auto.
  destruct Hw as [al' Hw].
  assert (Hw'':=Hw).
  apply J in Hw''.
  destruct Hw'' as [Hw'' | Hw'']; subst; auto.
  apply V_extract_spec' in Hw''; try congruence.
  inv Hp.
    inv Hw''.

    simpl in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; try congruence.
    apply H5 in Hw''. inv Hw''.
    destruct y as [a0]. eauto.
Qed.

Lemma sdom_tran1: forall n1 n2 n3
  (H: strict_domination n1 n2) (H0: domination n2 n3), strict_domination n1 n3.
Proof.
  intros.
  destruct (Hdec n1 n3); subst.
    destruct (@reachable_dec n3).
      eapply dom_acyclic in H; eauto.
        contradict H; auto.
        apply dom_reachable in H0; auto.

      apply everything_sdominates_unreachable_blocks; auto.

    apply sdom_dom in H.
    apply dom_sdom; eauto using dom_tran.
Qed.

Lemma sdom_tran2: forall n1 n2 n3
  (H: domination n1 n2) (H0: strict_domination n2 n3), strict_domination n1 n3.
Proof.
  intros.
  destruct (Hdec n1 n3); subst.
    destruct (@reachable_dec n3).
      eapply dom_acyclic in H0; eauto.
      contradict H0; auto.

      apply everything_sdominates_unreachable_blocks; auto.

    apply sdom_dom in H0.
    apply dom_sdom; eauto using dom_tran.
Qed.

Lemma sdom_tran: forall n1 n2 n3
  (H: strict_domination n1 n2) (H0: strict_domination n2 n3),
  strict_domination n1 n3.
Proof.
  intros. apply sdom_dom in H0. eapply sdom_tran1; eauto.
Qed.

Lemma idom_injective: forall p l1 l2
  (Hidom1 : imm_domination p l1) (Hidom2 : imm_domination p l2)
  (Hrd1 : reachable l1) (Hrd2 : reachable l2)
  (Hneq : l1 <> l2)
  (Hdec0 : strict_domination l1 l2 \/ strict_domination l2 l1),
  False.
Proof.
  intros.
  destruct Hidom2 as [Hsdom2 Him2].
  destruct Hidom1 as [Hsdom1 Him1].
  destruct Hdec0 as [Hsdom | Hsdom].
    eapply Him2 in Hsdom. 
    apply dom_acyclic in Hsdom1; auto.
        
    eapply Him1 in Hsdom. 
    apply dom_acyclic in Hsdom2; auto.
Qed.

Lemma clos_trans_idom__sdom: forall a b 
  (H: clos_trans T.elt imm_domination a b), 
  strict_domination a b.
Proof.
  intros.
  apply clos_trans_t1n in H.
  induction H; eauto using idom_sdom, sdom_tran.
Qed.

Lemma idom_clos_refl_trans_idom__sdom: forall a b c 
  (H': imm_domination a b)
  (H: clos_refl_trans T.elt imm_domination b c), 
  strict_domination a c.
Proof.
  intros.
  apply clos_trans_idom__sdom.
  eapply step_clos_refl_trans__clos_trans; eauto.
Qed.

End dom_acyclic_tran.

Lemma sdom_dec : forall n1 n2,
  strict_domination n1 n2 \/ ~ strict_domination n1 n2.
Proof. intros. tauto. Qed. (* classic logic *)

Import Classical_Pred_Type.

Lemma non_sdom__inv: forall n1 n2
  (Hnsdom: ~ strict_domination n1 n2),
  exists vl, exists al, D_walk vertexes arcs
    (index n2) (index entry) vl al /\
    ~ (In (index n1) vl /\ n1 <> n2).
Proof.
  intros.
  apply not_all_ex_not in Hnsdom. 
  destruct Hnsdom as [vl Hnsdom].
  apply not_all_ex_not in Hnsdom. 
  destruct Hnsdom as [al Hnsdom].
  exists vl. exists al.
  tauto.
Qed.

Lemma sdom_ordered : forall n1 n2 n3
  (Hneq: n1 <> n2) (Hreach: reachable n3)
  (Hsdom: strict_domination n1 n3)
  (Hsdom': strict_domination n2 n3),
  strict_domination n1 n2 \/ strict_domination n2 n1.
Proof.
  intros.
  destruct (sdom_dec n1 n2) as [|Hnsdom12]; auto.
  destruct (sdom_dec n2 n1) as [|Hnsdom21]; auto.
  contradict Hsdom. intro Hsdom.
  destruct Hreach as [vl [al Hreach]].
  assert (Hw:=Hreach).
  apply Hsdom in Hw.
  destruct Hw as [Hin Hneq13].
  assert (Hw:=Hreach).
  apply Hsdom' in Hw.
  destruct Hw as [Hin' Heq23].

  (* on Hw, we need to figuire the closest one to l3 in l1 and l2,
     suppose l1 is, then we split hw at l1, so l2 cannot be in the part
     from l3 to l1.
  *)
  assert (Hw:=Hreach).
  assert (vl <> V_nil) as Hnqnil.
    destruct vl; auto.
      intro J. inv J.
  apply DW_cut with (x:=index n1) (w:=index n2) in Hw; try congruence;
    simpl; auto.
  destruct Hw as [al1 [al2 [vl1 [vl2
    [[J1 [J2 [J3 [J4 J5]]]]|[J1 [J2 [J3 [J4 J5]]]]]]]]]; subst.
  Case "1".
  eapply non_sdom__inv in Hnsdom21; eauto.
  destruct Hnsdom21 as [vl1' [al1' [J1' J2']]].

  assert ((D_walk vertexes arcs (index n3) (index entry)
    (vl1++vl1') (al1++al1') * ~ In (index n2) (vl1++vl1'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5 Hneq.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hsdom' in J3.
  destruct J3 as [Hin'' Heq]; auto.

  Case "2".
  eapply non_sdom__inv in Hnsdom12; eauto.
  destruct Hnsdom12 as [vl2' [al2' [J1' J2']]].

  assert ((D_walk vertexes arcs (index n3) (index entry)
    (vl1++vl2') (al1++al2') * ~ In (index n1) (vl1++vl2'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5 Hneq.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hsdom in J3.
  destruct J3 as [Hin'' Heq]; auto.
Qed.

Lemma idom_isnt_refl: forall l1 l2 (Hreach: reachable l2)
  (Hdom12 : imm_domination l1 l2),
  l1 <> l2.
Proof.
  intros.
  destruct Hdom12.
  eapply sdom_isnt_refl; eauto.
Qed.

Section rt_idom__sdom_ordered.

Hypothesis entry_has_no_preds : forall a0
  (Hin: In entry (XTree.successors_list successors a0)),
  False.

Lemma rt_idom__sdom_ordered: forall x y z
  (Hrt1 : clos_refl_trans T.elt imm_domination y x)
  (Hrt2 : clos_refl_trans T.elt imm_domination z x)
  (Hneq : y <> z)
  (Hreachx : reachable x),
  strict_domination y z \/ strict_domination z y.
Proof.
  intros.
  apply clos_refl_trans__eq_or_clos_trans in Hrt1.
  apply clos_refl_trans__eq_or_clos_trans in Hrt2.
  destruct Hrt1 as [EQ1 | Ht1].
    destruct Hrt2 as [EQ2 | Ht2].
      congruence.
      subst. right.
      eapply clos_trans_idom__sdom; eauto.
    destruct Hrt2 as [EQ2 | Hwk2].
      subst. left.
      eapply clos_trans_idom__sdom; eauto.
  
      apply sdom_ordered with (n3:=x); 
        eauto using idom_sdom, clos_trans_idom__sdom.
Qed.

End rt_idom__sdom_ordered.

Lemma noone_sdom_entry: forall n
  (Hincfg: XTree.in_cfg successors entry)
  (Hnopred: XTree.successors_list 
              (XTree.make_predecessors successors) entry = nil)
  (Hsdom : strict_domination n entry),
  False.
Proof.
  intros.
  assert (Hreach:=reachable_entry Hincfg).
  destruct Hreach as [vl [al Hreach]].
  assert (Hw:=Hreach).
  apply Hsdom in Hw.
  inv Hreach.
    tauto.

    simpl in H1. 
    destruct y.
    apply XTree.make_predecessors_correct in H1.
    rewrite Hnopred in H1. tauto.
Qed.

Lemma sdom_of_reachable_is_in_cfg: forall n1 n2 
  (Hreach: reachable n2)
  (Hsdom: strict_domination n1 n2),
  XTree.in_cfg successors n1.
Proof.
  intros.
  apply sdom_reachable in Hsdom; auto.
  apply reachable_is_in_cfg; auto.
Qed.

Lemma entry_doms_others: forall n (Hnentry: n <> entry),
  strict_domination entry n.
Proof.
  intros.
  intros vl al Hwk.
  assert (J:=Hwk).
  inv J; try congruence.
  apply DW_iny_vl in Hwk; auto.
    intro EQ. inv EQ.  
Qed.

End Cfg. End Cfg.

(* A CFG named by atoms *)
Module ACfg := Cfg(ATree).
(* A CFG named by positives *)
Module PCfg := Cfg (PTree).

Import LLVMsyntax.
Import LLVMinfra.
(* The following defines CFGs used by Vellvm's semantics. *)

(* Compute a successor map of a list of blocks. *)
Fixpoint successors_blocks (bs: blocks) : ATree.t ls :=
match bs with
| nil => ATree.empty ls
| (l0, stmts_intro _ _ tmn) :: bs' =>
    ATree.set l0 (successors_terminator tmn) (successors_blocks bs')
end.

(* Compute a successor map of a function. *)
Definition successors (f: fdef) : ATree.t ls :=
let '(fdef_intro _ bs) := f in
successors_blocks bs.

(* The set of label names of a list of blocks *)
Fixpoint bound_blocks (bs: blocks) : set atom :=
match bs with
| nil => empty_set _
| (l0, _) :: bs' => l0::(bound_blocks bs')
end.

(* The set of label names of a function *)
Definition bound_fdef (f: fdef) : set atom :=
let '(fdef_intro _ bs) := f in
bound_blocks bs.

(* All CFG nodes of a funcion *)
Definition vertexes_fdef (f:fdef) : V_set :=
ACfg.vertexes (successors f).

(* All CFG edges of a funcion *)
Definition arcs_fdef (f:fdef) : A_set :=
ACfg.arcs (successors f).

(* l0 is reachable by f's entry. *)
Definition reachable (f:fdef) (l0:l) : Prop :=
match getEntryBlock f with
| Some (entry, _) =>
  ACfg.reachable (successors f) entry l0
| _ => false
end.

(* l1 dominates l2 in f. *)
Definition domination (f:fdef) (l1 l2:l) : Prop :=
match getEntryBlock f with
| Some (entry, _) =>
  ACfg.domination (successors f) entry l1 l2
| _ => False
end.

(* l1 strictly dominates l2 in f. *)
Definition strict_domination (f:fdef) (l1 l2:l) : Prop :=
match getEntryBlock f with
| Some (entry, _) =>
  ACfg.strict_domination (successors f) entry l1 l2
| _ => False
end.

Hint Unfold ACfg.domination ACfg.reachable ACfg.non_sdomination
            ACfg.strict_domination: cfg.

(* l1 immediately dominates l2 in f. *)
Definition imm_domination (f:fdef) (l1 l2:l) : Prop :=
strict_domination f l1 l2 /\
forall l0, strict_domination f l0 l2 -> domination f l0 l1.

Notation " f ~>* l " := (reachable f l) (at level 0): dom.
Notation " f |= l1 >> l2 " := (strict_domination f l1 l2) (at level 0): dom.
Notation " f |= l1 >>= l2 " := (domination f l1 l2) (at level 0): dom.
Notation " f |= l1 >>> l2 " := (imm_domination f l1 l2) (at level 0): dom.

(* Compute a predecessor map of a function. *)
Definition predecessors (f: fdef) : ATree.t ls :=
XATree.make_predecessors (successors f).

(* Check if b has no predecessors in f. *)
Definition has_no_predecessors (f: fdef) (b:block) : bool :=
match (predecessors f) !!! (getBlockLabel b) with
| nil => true
| _ => false
end.

(* Properties of successors *)
Lemma in_successors_blocks__in_bound_blocks: forall (n : ATree.elt) (s : ls) 
  (bs : blocks) (Hinscs : (successors_blocks bs) ! n = Some s),
  In n (bound_blocks bs).
Proof.
  induction bs as [|[? []] bs]; simpl in *; intros.
    rewrite ATree.gempty in Hinscs. congruence.

    rewrite ATree.gsspec in Hinscs.
    destruct_if; auto.
Qed.

Lemma in_bound_blocks__in_successors_blocks: forall (n : ATree.elt)
  (bs : blocks) (Hin: In n (bound_blocks bs)),
  exists s, (successors_blocks bs) ! n = Some s.
Proof.
  induction bs as [|[? []] bs]; simpl in *; intros.
    tauto.

    rewrite ATree.gsspec.
    destruct_if; eauto.
    destruct Hin; try solve [auto | congruence].
Qed.

Lemma successors_blocks__InBlocksB : forall l0 a bs,
  In l0 (successors_blocks bs) !!! a ->
  exists ps0, exists cs0, exists tmn0,
    InBlocksB (a, stmts_intro ps0 cs0 tmn0) bs /\
    In l0 (successors_terminator tmn0).
Proof.
  unfold XATree.successors_list.
  induction bs as [|a0 bs]; simpl; intro.
    rewrite ATree.gempty in H. inv H.

    destruct a0 as [l1 [p c t]].
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

Lemma successors__blockInFdefB : forall l0 a f,
  In l0 (successors f) !!! a ->
  exists ps0, exists cs0, exists tmn0,
    blockInFdefB (a, stmts_intro ps0 cs0 tmn0) f /\
    In l0 (successors_terminator tmn0).
Proof.
  destruct f as [fh bs]. simpl.
  apply successors_blocks__InBlocksB; auto.
Qed.

Lemma successors_blocks__blockInFdefB : forall l0 a fh bs,
  In l0 (successors_blocks bs) !!! a ->
  exists ps0, exists cs0, exists tmn0,
    blockInFdefB (a, stmts_intro ps0 cs0 tmn0) (fdef_intro fh bs) /\
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
  (HbInF : InBlocksB (l0, stmts_intro cs ps tmn) bs)
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
    destruct a as [? []].
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
        eapply InBlocksB__NotIn; eauto.
Qed.

Lemma successor_in_arcs : forall l0 cs ps tmn f l1
  (HuniqF : uniqFdef f)
  (HbInF : blockInFdefB (l0, stmts_intro cs ps tmn) f)
  (Hin : In l1 (successors_terminator tmn)),
  arcs_fdef f (A_ends (index l1) (index l0)).
Proof.
  intros.
  unfold arcs_fdef.
  destruct f as [fh bs]. apply uniqF__uniqBlocks in HuniqF.
  simpl.
  erewrite <- successors_terminator__successors_blocks; eauto.
Qed.

Lemma blockInFdefB__successors : forall a ps0 cs0 tmn0 f (Huniq: uniqFdef f)
  (H: blockInFdefB (a, stmts_intro ps0 cs0 tmn0) f),
  (successors f) ! a = Some (successors_terminator tmn0).
Proof.
  destruct f as [[] bs]. simpl.
  intros [J _].
  unfold uniqBlocks in J.
  destruct J as [J _].
  induction bs as [|a1 bs]; simpl; intros.
    congruence.

    destruct a1 as [l0 [ps1 cs1 tmn1]].
    apply orb_true_iff in H.
    destruct H as [H | H].
      apply blockEqB_inv in H. inv H.
      rewrite ATree.gss. auto.

      assert (J':=J). inv J'.
      simpl in J. simpl_env in J.
      assert (H':=H).
      apply IHbs in H'; auto.
      apply InBlocksB_In in H.
      apply uniq_app_3 in J.
      destruct (id_dec l0 a); subst.
        congruence.
        rewrite ATree.gso; auto.
Qed.

Lemma successors__successors_terminator : forall scs a f
  (H: Some scs = (successors f) ! a),
  exists ps0, exists cs0, exists tmn0,
    blockInFdefB (a, stmts_intro ps0 cs0 tmn0) f /\
    scs = successors_terminator tmn0.
Proof.
  destruct f as [fh bs]. simpl.
  induction bs as [|a0 bs]; simpl; intro.
    rewrite ATree.gempty in H. inv H.

    destruct a0 as [l1 [p c t]].
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

(* Properties of bound *)
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

Lemma blockInFdefB_in_bound_fdef : forall l0 s0 f
  (HbInF : blockInFdefB (l0, s0) f),
  In l0 (bound_fdef f).
Proof.
  intros.
  unfold bound_fdef.
  destruct f as [f b].
  generalize dependent s0.
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

Section reachable__in_bound.

Variable f:fdef.
Hypothesis branches_in_bound_fdef: forall p ps0 cs0 tmn0 l2
  (J3 : blockInFdefB (p, stmts_intro ps0 cs0 tmn0) f)
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

Lemma In_bound_fdef__blockInFdefB: forall f l3
  (Hin: In l3 (bound_fdef f)),
  exists s3, blockInFdefB (l3, s3) f = true.
Proof.
  destruct f as [[] bs].
  simpl. intros.
  induction bs as [|[l0 s0]]; simpl in *.
    tauto.

    destruct Hin as [Hin | Hin]; subst.
      exists s0.
      apply orb_true_intro.
      left. solve_refl.      

      apply IHbs in Hin.
      destruct Hin as [s0' Hin].
      exists s0'.
      apply orb_true_intro. auto.
Qed.

Lemma in_bound__in_cfg : forall bs l0 (Hin: In l0 (bound_blocks bs)),
  XATree.in_cfg (successors_blocks bs) l0.
Proof.
  intros. left. apply in_bound__in_parents; auto.
Qed.

Lemma in_bound_blocks__in_dom: forall bs,
  (forall a, In a (bound_blocks bs) <-> a `in` dom bs).
Proof.
  induction bs as [|[] bs]; simpl; intros.
    split; intros. tauto. fsetdec.

    split; intros. 
      destruct H as [H | H]; subst; auto.
        apply IHbs in H; auto.
      apply AtomSetFacts.add_iff in H.
      destruct H as [H | H]; subst; auto.
        apply IHbs in H; auto.
Qed.

Lemma notin_bound_blocks__notin_dom: forall bs,
  (forall a, ~ In a (bound_blocks bs) <-> a `notin` dom bs).
Proof.
  intros.
  split; intros H; intro J; apply H; apply in_bound_blocks__in_dom; auto.
Qed.

Lemma uniqFdef__NoDup_bounds_fdef: forall f (Huniq: uniqFdef f),
  NoDup (bound_fdef f).
Proof.
  destruct f as [[] bs]. simpl.
  intros. 
  destruct Huniq as [[Huniq _] _].
  induction bs as [|[? []] bs]; simpl.
    constructor.    
    
    inv Huniq.
    constructor; auto. 
      apply notin_bound_blocks__notin_dom; auto.
Qed.

Section ElementsOfCfg__eq__Bound.

Variable f:fdef.

Hypothesis branches_in_bound_fdef: forall p ps0 cs0 tmn0 l2
  (J3 : blockInFdefB (p, stmts_intro ps0 cs0 tmn0) f)
  (J4 : In l2 (successors_terminator tmn0)),
  In l2 (bound_fdef f).

Lemma in_cfg__in_bound : forall l0 
  (Hin: XATree.in_cfg (successors f) l0), In l0 (bound_fdef f).
Proof.
  destruct f as [fh bs].
  intros. 
  destruct Hin as [Hin | Hin].
    apply in_parents__in_bound; auto.

    apply XATree.children_of_tree__in_successors in Hin.
    destruct Hin as [p [sc [Hscs Hin]]].
    assert (In l0 (successors (fdef_intro fh bs)) !!! p) as Hin'.
      unfold XATree.successors_list.
      unfold ATree.elt, l in *.
      rewrite Hscs. auto.
    apply successors__blockInFdefB in Hin'.
    destruct_conjs. eauto.
Qed.

Lemma elements_of_acfg__eq__bound : 
  AtomSet.set_eq (XATree.elements_of_cfg (successors f) eq_atom_dec) 
    (bound_fdef f).
Proof.
  split.
    intros x Hinx.
    apply XATree.in_elements_of_cfg__in_cfg in Hinx.
    apply in_cfg__in_bound; auto.

    intros x Hinx.
    apply XATree.in_elements_of_cfg__in_cfg.
    destruct f.
    apply in_bound__in_cfg in Hinx; auto.
Qed.

End ElementsOfCfg__eq__Bound.

(* Properties of vertexes *)
Lemma entry_in_vertexes : forall f l0 s0
  (Hentry : getEntryBlock f = Some (l0, s0)),
  vertexes_fdef f (index l0).
Proof.
  intros.
  unfold vertexes_fdef, ACfg.vertexes. destruct f as [f b].
  destruct b; simpl in *.
    congruence.
    inv Hentry. 
    left. destruct s0.
    apply ACfg.XTree.parents_of_tree__in_successors.
    rewrite ATree.gss. eauto.
Qed.

Lemma blockInFdefB_in_vertexes : forall l0 s0 f
  (HbInF : blockInFdefB (l0, s0) f),
  vertexes_fdef f (index l0).
Proof.
  intros.
  left.
  apply blockInFdefB_in_bound_fdef in HbInF.
  apply in_bound_fdef__in_parents; auto.
Qed.

(* Properties of arcs *)
Lemma arcs_fdef_inv : forall f a1 a2,
  arcs_fdef f (A_ends (index a2) (index a1)) ->
  In a2 ((successors f)!!!a1).
Proof. auto. Qed.

(* Properties of predecessors *)
Lemma successors_predecessors_of_block : forall f l1 ps1 cs1 tmn1 l0,
  uniqFdef f ->
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true ->
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
            apply NoDup_split in G1. destruct G1 as [G1 _].
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

(* Properties of entries *)
Lemma entry_in_parents: forall (f : fdef) (a : atom) 
  (Hentry : getEntryLabel f = Some a),
  In a (XATree.parents_of_tree (successors f)).
Proof.
  intros.
  destruct f as [? [|[? []]]]; inv Hentry. 
  simpl.
  apply ACfg.XTree.parents_of_tree__in_successors.
  rewrite ATree.gss. eauto.
Qed.

Lemma entry_in_bound_fdef: forall entry f (Hentry: getEntryLabel f = Some entry),
  ListSet.set_In entry (bound_fdef f).
Proof.
  intros.
  apply getEntryLabel__getEntryBlock in Hentry.
  destruct Hentry as [[le' []] [Hentry Heq]].
  simpl in Heq. subst.
  apply entryBlockInFdef in Hentry.
  eapply blockInFdefB_in_bound_fdef; eauto.
Qed.

Lemma le_in_cfg: forall f le
  (Hentry: getEntryLabel f = Some le),
  XATree.in_cfg (successors f) le.
Proof.
  intros.
  apply getEntryLabel__getEntryBlock in Hentry.
  destruct Hentry as [[le' []] [Hentry Heq]].
  simpl in Heq. subst.
  eapply entry_in_vertexes; eauto.
Qed.

(* The following defines the maximal iteration step for Kildall's algorithms. *)
Definition Pcubeplus (p:positive) : positive := (p * (p * p) + p)%positive.

Lemma Pcubeplus_ge: forall p1 p2 (Hge: (p1 >= p2)%positive),
  (Pcubeplus p1 >= Pcubeplus p2)%positive.
Proof.
  unfold Pcubeplus.
  intros.
  assert (p1 * (p1 * p1) >= p2* (p2 * p2))%positive.
    zify. repeat (apply Zmult_ge_compat; try omega).
  zify; omega.
Qed.

Definition plength A := fun (ls1 : list A) => P_of_succ_nat (length ls1).
Implicit Arguments plength [A].

Definition pnum_of_blocks_in_fdef (f: fdef) : positive :=
match f with
| fdef_intro _ bs => List.fold_left (fun acc _ => Psucc acc) bs 3%positive
end.

Definition num_iters (f: fdef): positive :=
let pn := pnum_of_blocks_in_fdef f in
Pcubeplus pn.

Lemma plength_of_blocks__eq__P_of_plus_nat: forall bs p,
  fold_left (fun (acc : positive) (_ : block) => Psucc acc) bs p = 
    P_of_plus_nat p (length (bound_blocks bs)).
Proof.
  induction bs as [|[] bs]; simpl; intros; auto.
    rewrite IHbs.
    repeat rewrite Pplus_one_succ_l.
    rewrite P_of_plus_nat_Pplus_commut; auto.
Qed.

