Require Import Coqlib.
Require Import Iteration.
Require Import Maps.
Require Import syntax.
Require Import infrastructure_props.
Require Import infrastructure.
Require Import Metatheory.
Require Import Program.Tactics.
Require Import dom_libs.
Require Import dfs.
Require Export cfg.
Require Export reach.
Require Export dom_decl.
Require Import push_iter.
Require Import dom_tree.
Require Import dom_list_tree.

(***************************************************)
(* This file implements the list-based dominaton analysis. At the high-level, 
   our implementation works in three steps: 
   1) calculate the PO of a CFG by depth-first-search (DFS); 
   2) compute strict dominators for PO-numbered nodes in Kildall (push_iter); 
   3) finally relate the analysis results to the original nodes.
*)

Require Import Dipaths.
Require Import infrastructure.
Import LLVMsyntax.
Import LLVMinfra.

(* Define the conversion from atom-based CFGs to positive-based CFGs. *)
Definition a2p_Vertex (a2p:ATree.t positive) (av: Vertex) (pv : Vertex) :=
let '(index a) := av in
let '(index p) := pv in
a2p ! a = Some p.

Definition a2p_V_list (a2p:ATree.t positive) (avl: V_list) (pvl : V_list) :=
List.Forall2 (a2p_Vertex a2p) avl pvl.

Definition a2p_Arc (a2p:ATree.t positive) (aa: Arc) (pa : Arc) :=
let '(A_ends av1 av2) := aa in
let '(A_ends pv1 pv2) := pa in
a2p_Vertex a2p av1 pv1 /\ a2p_Vertex a2p av2 pv2.

Definition a2p_A_list (a2p:ATree.t positive) (aal: A_list) (pal : A_list) :=
List.Forall2 (a2p_Arc a2p) aal pal.

(* Properties of atolist_ptolist *)
Lemma in_init__in_atolist_ptolist: forall a a2p ps acc (Hin: In a acc),
  In a (fold_left (atolist_ptolist_fun a2p) ps acc).
Proof.
  induction ps as [|p ps]; simpl; intros; auto.
    apply IHps.
    unfold atolist_ptolist_fun. 
    destruct (a2p ! p); simpl; auto.
Qed.

Lemma in_atolist_ptolist__incl: forall a a2p ps init1 init2 
  (Hinc: incl init1 init2)
  (Hin : In a (fold_left (atolist_ptolist_fun a2p) ps init1)),
  In a (fold_left (atolist_ptolist_fun a2p) ps init2).
Proof.
  induction ps as [|p ps]; simpl; intros.
    eauto with datatypes v62.

    eapply IHps; eauto.
      unfold atolist_ptolist_fun. 
      destruct (a2p ! p); simpl; auto with datatypes v62.
Qed.

Lemma in_atolist__in_ptolist_aux: forall (a2p : ATree.t positive) a p 
  (Hget : a2p ! a = Some p) atolist (Hinscs : In a atolist) ptolist init
  (Heq: ptolist = fold_left (atolist_ptolist_fun a2p) atolist init),
  In p ptolist.
Proof.
  unfold atolist_ptolist.
  induction atolist; simpl; intros; subst.
    tauto.

    destruct Hinscs as [Hinscs | Hinscs]; subst; simpl.
      unfold atolist_ptolist_fun.
      rewrite Hget. 
      apply in_init__in_atolist_ptolist; simpl; auto.

      eapply IHatolist; eauto.
Qed.

Lemma in_atolist__in_ptolist: forall (a2p : ATree.t positive) a p 
  (Hget : a2p ! a = Some p) atolist (Hinscs : In a atolist) ptolist
  (Heq: ptolist = atolist_ptolist a2p atolist),
  In p ptolist.
Proof.
  unfold atolist_ptolist.
  intros.
  eapply in_atolist__in_ptolist_aux; eauto.
Qed.

Lemma in_ptolist__in_atolist_aux: forall (a2p : ATree.t positive) p atolist init
  (Hinscs : In p (fold_left (atolist_ptolist_fun a2p) atolist init)),
  In p init \/ exists a, a2p ! a = Some p /\ In a atolist.
Proof.
  induction atolist; simpl; intros; auto.
    apply IHatolist in Hinscs.
    destruct Hinscs as [Hinscs | Hinscs].
    Case "1".
      unfold atolist_ptolist_fun in Hinscs.
      case_eq (a2p ! a).
        intros p0 Hget0.
        rewrite Hget0 in Hinscs.
        destruct_in Hinscs.
          eauto.

        intros Hget0.
        rewrite Hget0 in Hinscs; auto.
    Case "2".
      destruct Hinscs as [a1 [J1 J2]].
      eauto.
Qed.

Lemma in_ptolist__in_atolist: forall (a2p : ATree.t positive) p atolist
  (Hinscs : In p (atolist_ptolist a2p atolist)),
  exists a, a2p ! a = Some p /\ In a atolist.
Proof.
  unfold atolist_ptolist.
  intros.
  apply in_ptolist__in_atolist_aux in Hinscs.
  destruct Hinscs as [Hinscs | Hinscs]; auto.
    tauto.
Qed.

Lemma get_a2p__ptolist_atolist': forall a2p asuccs p3 ptodo 
  (Hptodo: (asuccs_psuccs a2p asuccs) ? p3 = Some ptodo),
  exists l3, exists atodo, 
    a2p ! l3 = Some p3 /\ asuccs ! l3 = Some atodo /\ 
    atolist_ptolist a2p atodo = ptodo.
Proof.
  intros a2p asuccs.
  set (P := fun asuccs psuccs =>
            forall p3 ptodo 
              (Hptodo: psuccs ? p3 = Some ptodo),
              exists l3, exists atodo, 
                a2p ! l3 = Some p3 /\ asuccs ! l3 = Some atodo /\ 
                atolist_ptolist a2p atodo = ptodo).
  unfold asuccs_psuccs. 
  apply ATree_Properties.fold_rec with (P := P).
  Case "extensionality".
  intros m m' a H.
  unfold P; intros.
  eapply H0 in Hptodo; eauto.
  destruct Hptodo as [l3 [atodo [J1 [J2 J3]]]].
  exists l3. exists atodo. rewrite <- H. eauto.
  Case "base case".
  intros a p. rewrite PTree.gempty. intros. congruence.
  Case "inductive case".
  intros m a0 k v Hnone Hget0 IH.
  unfold P in *; intros. 
  unfold asucc_psucc in Hptodo.
  case_eq (a2p!k).
  SCase "1".
    intros p Hget. 
    rewrite Hget in Hptodo.
    rewrite PTree.gsspec in Hptodo.
    destruct_if.
    SSCase "1.1".
      exists k. exists v.
      rewrite ATree.gsspec.
      split; auto.
      destruct_if.
        congruence.
    SSCase "1.2".
      apply IH in H0.
      destruct H0 as [l3 [atodo [J1 [J2 J3]]]].
      exists l3. exists atodo.
      rewrite ATree.gsspec.
      split; auto.
      destruct_if.
        uniq_result.
  SCase "2".
    intros Hget. 
    rewrite Hget in Hptodo.
    apply IH in Hptodo.
    destruct Hptodo as [l3 [atodo [J1 [J2 J3]]]].
    exists l3. exists atodo.
    rewrite ATree.gsspec.
    split; auto.
    destruct_if.
      congruence.
Qed.

(* Properties of asuccs_psuccs. *)
Section asuccs_psuccs.

Variable a2p: ATree.t positive.
Variable asuccs: ATree.t (list l).
Hypothesis Hinj: forall a1 a2 p (Hin1: a2p ! a1 = Some p) 
                 (Hin2: a2p ! a2 = Some p), a1 = a2.

Lemma get_a2p__atolist_ptolist: forall l3 p3 
  (Hget3 : a2p ! l3 = Some p3) atodo (Hatodo: asuccs ! l3 = Some atodo),
  (asuccs_psuccs a2p asuccs) ? p3 = Some (atolist_ptolist a2p atodo).
Proof.
  set (P := fun asuccs psuccs =>
            forall (Hinj: forall a1 a2 p (Hin1: a2p ! a1 = Some p) 
                          (Hin2: a2p ! a2 = Some p), a1 = a2)
            l3 p3 
            (Hget3 : a2p ! l3 = Some p3) atodo 
            (Hatodo: asuccs ! l3 = Some atodo),
            psuccs ? p3 = Some (atolist_ptolist a2p atodo)).
  unfold asuccs_psuccs. 
  revert Hinj.
  apply ATree_Properties.fold_rec with (P := P).
  Case "extensionality".
  intros m m' a H.
  unfold P; intros.
  rewrite <- H in *.  
  eapply H0; eauto.
  Case "base case".
  intros a p. rewrite ATree.gempty. intros. congruence.
  Case "inductive case".
  intros m a0 k v Hnone Hget0 IH.
  unfold P in *; intros. 
  rewrite ATree.gsspec in Hatodo.
  unfold asucc_psucc. 
  destruct (ATree.elt_eq l3 k); subst.
    uniq_result.
    rewrite Hget3.
    rewrite PTree.gsspec.
    destruct_if; auto. 
      congruence.

    assert (G:=Hatodo).
    eapply IH in G; eauto. 
    case_eq (a2p!k); auto.
      intros p Hget. 
      rewrite PTree.gsspec.
      destruct_if; auto.
        contradict n.
        eapply Hinj; eauto.
Qed.

Lemma in_asuccs__in_psuccs: forall l' l3 p3 p'
  (Hinscs : In l' asuccs !!! l3)
  (Hget3 : a2p ! l3 = Some p3) (Hget' : a2p ! l' = Some p'),
  In p' (asuccs_psuccs a2p asuccs) ??? p3.
Proof.
  intros.
  assert (J:=Hinscs).
  apply XATree.successors_list_spec in J.
  destruct J as [scs [J1 J2]].
  eapply get_a2p__atolist_ptolist in J1; eauto.
  apply XPTree.successors_list_intro in J1. 
  eapply in_atolist__in_ptolist; eauto.
Qed.

Lemma in_aparents__in_pparents: forall (a : atom) (p : positive)
  (Hget : a2p ! a = Some p)
  (Heq : In a (XATree.parents_of_tree asuccs)),
  In p (XPTree.parents_of_tree (asuccs_psuccs a2p asuccs)).
Proof.
  intros.
  apply XATree.parents_of_tree__in_successors in Heq.
  apply XPTree.parents_of_tree__in_successors.
  destruct Heq as [scs Heq].
  eapply get_a2p__atolist_ptolist in Heq; eauto.
Qed.

Lemma in_vertexes__get_a2p: forall a2p asuccs pv
  (Hincfg: PCfg.vertexes (asuccs_psuccs a2p asuccs) pv),
  exists av, a2p_Vertex a2p av pv.
Proof.
  intros.  
  destruct pv as [p].
  destruct Hincfg as [Hincfg | Hincfg].
    apply XPTree.parents_of_tree__in_successors in Hincfg.
    destruct Hincfg as [scs Hincfg].
    apply get_a2p__ptolist_atolist' in Hincfg.
    destruct Hincfg as [a3 [? [? [? ?]]]].
    exists (index a3). auto.

    apply XPTree.children_of_tree__in_successors in Hincfg.
    destruct Hincfg as [p0 [scs0 [J1 J2]]].
    apply get_a2p__ptolist_atolist' in J1.
    destruct J1 as [l3 [atodo [J1 [J3 J4]]]]; subst scs0.
    apply in_ptolist__in_atolist in J2.
    destruct J2 as [a' [J2 J4]].
    exists (index a'). auto.
Qed.

End asuccs_psuccs.

Ltac fill_holes_in_ctx :=
let fill e H :=
  match goal with
  | H1: _ = e |- _ => rewrite <- H1 in H
  | H1: e = _ |- _ => rewrite H1 in H
  end 
in
let fill' e :=
  match goal with
  | H1: _ = e |- _ => rewrite <- H1
  | H1: e = _ |- _ => rewrite H1
  end
in
repeat match goal with
| H: context [match ?e with
     | Some _ => _
     | None => _
     end] |- _ => fill e H
| H: context [match ?e with
     | inl _ => _
     | inr _ => _
     end] |- _ => fill e H
| H: context [match ?e with
     | (_,_) => _
     end] |- _ => fill e H
| H: context [match ?e with
     | (_,_) => _
     end] |- _ => fill e H
| |- context [match ?e with
     | Some _ => _
     | None => _
     end] => fill' e
end.

(* Properties of get_reachable_nodes. *)
Definition get_reachable_nodes_fun (a2p:ATree.t positive) (acc:list positive) 
  (a:l) : list positive :=
match a2p ! a with
| Some p => p::acc
| None => acc
end.

Definition get_reachable_nodes (bd:list l) (a2p:ATree.t positive) 
  : list positive :=
fold_left (get_reachable_nodes_fun a2p) bd nil.

Lemma get_reachable_nodes_spec_aux: forall p0 a2p bd acc,
  In p0 (fold_left (get_reachable_nodes_fun a2p) bd acc) <-> 
    (In p0 acc \/ (exists l0, a2p ! l0 = Some p0 /\ In l0 bd)).
Proof.
  induction bd; simpl; intros.
    split; intro J; auto.
      destruct J as [J | [l0 [J1 J2]]]; tauto.

    split; intro.
    Case "1".
      apply IHbd in H.
      destruct H as [J | [l0 [J1 J2]]].
      SCase "1.1".
        unfold get_reachable_nodes_fun in J.
        case_eq (a2p ! a).
          intros p Hget.
          rewrite Hget in J.
          destruct_in J.
            right. exists a. split; auto.

          intros Hget.
          rewrite Hget in J. auto.
      SCase "1.2".
        right. exists l0. auto.
    Case "2".
      apply IHbd.
      unfold get_reachable_nodes_fun.
      destruct H as [J | [l0 [J1 [J2 | J2]]]]; subst.
      SCase "1.1".
        unfold get_reachable_nodes_fun.
        case_eq (a2p ! a); auto.
          intros p Hget.
          simpl. auto.
      SCase "1.2".
        rewrite J1. simpl. auto.
      SCase "1.3".
        right. exists l0. auto.
Qed.

Lemma get_reachable_nodes_spec: forall p0 a2p bd,
  In p0 (get_reachable_nodes bd a2p) <-> 
    exists l0, a2p ! l0 = Some p0 /\ In l0 bd.
Proof.
  intros.
  unfold get_reachable_nodes.
  destruct (get_reachable_nodes_spec_aux p0 a2p bd nil) as [J1 J2].
  split; intros; auto.
    apply J1 in H.
    destruct H; tauto.
Qed.

Import AtomSet.

Require Import dom_type.

(* Properties of the conversion from atom-based CFGs to positive-based CFGs. *)
Section adom_pdom.

Variable f:fdef.
Definition asuccs := cfg.successors f.
Variable PO: PostOrder.
Variable le: l.
Hypothesis Hentry: getEntryLabel f = Some le.

Hypothesis Hdfs: dfs (successors f) le 1 = PO.

Lemma entry_in_a2p_cfg: forall (p : positive) a (Hget: (PO_a2p PO) ! a = Some p) 
  (Hentry: getEntryLabel f = Some a),
  in_cfg (asuccs_psuccs (PO_a2p PO) asuccs) p.
Proof.
  intros.
  left.
  eapply in_aparents__in_pparents; eauto using Injective.dfs_inj.
  apply entry_in_parents; auto.
Qed.

Lemma get_a2p__ptolist_atolist: forall l3 p3
  (Hget3 : (PO_a2p PO) ! l3 = Some p3) ptodo 
  (Hptodo: (asuccs_psuccs (PO_a2p PO) asuccs) ? p3 = Some ptodo),
  exists atodo, asuccs ! l3 = Some atodo /\ 
                atolist_ptolist (PO_a2p PO)  atodo = ptodo.
Proof.
  intros.
  apply get_a2p__ptolist_atolist' in Hptodo.
  destruct Hptodo as [a2 [atodo [J1 [J2 J3]]]].
  assert (l3 = a2) as EQ.
    eapply Injective.dfs_inj; eauto.
  subst. eauto.
Qed.

Lemma in_pparents__in_aparents: forall (a : atom) (p : positive)
  (Hget : (PO_a2p PO) ! a = Some p)
  (Heq : In p (XPTree.parents_of_tree (asuccs_psuccs (PO_a2p PO) asuccs))),
  In a (XATree.parents_of_tree asuccs).
Proof.
  intros.
  apply XPTree.parents_of_tree__in_successors in Heq.
  apply XATree.parents_of_tree__in_successors.
  destruct Heq as [scs Heq].
  eapply get_a2p__ptolist_atolist in Heq; eauto.
  destruct_conjs. eauto.
Qed.

Lemma in_psuccs__in_asuccs: forall l3 p3 p' 
  (Hinscs : In p' (asuccs_psuccs (PO_a2p PO) asuccs) ??? p3)
  (Hget3 : (PO_a2p PO) ! l3 = Some p3),
  exists l',  (PO_a2p PO) ! l' = Some p' /\ In l' asuccs !!! l3.
Proof.
  intros.
  assert (J:=Hinscs).
  apply XPTree.successors_list_spec in J.
  destruct J as [scs [J1 J2]].
  eapply get_a2p__ptolist_atolist in J1; eauto.
  destruct J1 as [atodo [J1 J3]]; subst.
  apply in_ptolist__in_atolist in J2.
  destruct J2 as [a [J2 J3]].
  exists a.
  split; auto.
    eapply XATree.in_successors_list_intro; eauto.
Qed.

Lemma asuccs_psuccs__no_preds: forall l1 p1
  (Hnopreds : (XATree.make_predecessors asuccs) !!! l1 = nil)
  (Hget: Some p1 = (PO_a2p PO) ! l1),
  (XPTree.make_predecessors (asuccs_psuccs (PO_a2p PO) asuccs)) ??? p1 = nil.
Proof.
  intros.
  case_eq ((XPTree.make_predecessors (asuccs_psuccs (PO_a2p PO) asuccs)) ??? p1); 
    auto.
  intros hd tl Heq.
  assert (In hd (XPTree.make_predecessors 
            (asuccs_psuccs (PO_a2p PO) asuccs)) ??? p1) as Hin.
    rewrite Heq. simpl. auto.
  apply XPTree.make_predecessors_correct' in Hin.
  assert (G:=Hin).
  apply XPTree.successors_list_spec in G.
  destruct G as [scs [J1 Hin']].
  apply get_a2p__ptolist_atolist' in J1.
  destruct J1 as [l3 [atodo [J1 [J2 J3]]]]; subst scs.
  eapply in_psuccs__in_asuccs in Hin; eauto.
  destruct Hin as [l' [G1 G2]].
  apply XATree.make_predecessors_correct in G2.
  assert (l' = l1) as EQ.
    eapply Injective.dfs_inj; eauto.
  subst. 
  rewrite Hnopreds in G2. tauto.
Qed.

Lemma a2p_arcs: forall pv1 av1 pv2 av2
  (Hget1: a2p_Vertex (PO_a2p PO) av1 pv1)
  (Hget2: a2p_Vertex (PO_a2p PO) av2 pv2),
  (PCfg.arcs (asuccs_psuccs (PO_a2p PO) (successors f)) (A_ends pv1 pv2) <->
    ACfg.arcs (successors f) (A_ends av1 av2)).
Proof.
  intros.
  destruct av1 as [a1]. destruct av2 as [a2].
  destruct pv1 as [p1]. destruct pv2 as [p2].
  simpl in *.
  split; intros J.
    eapply in_psuccs__in_asuccs in J; eauto.
    destruct J as [a1' [J1 J2]].
    assert (a1 = a1') as EQ. 
      eapply Injective.dfs_inj; eauto.
    subst a1'. auto.

    eapply in_asuccs__in_psuccs in J; eauto using Injective.dfs_inj.
Qed.

Lemma get_a2p__in_pcfg: forall (a1: atom) (p1: positive) 
  (Hget1 : (PO_a2p PO) ! a1 = Some p1),
  XPTree.in_cfg (asuccs_psuccs (PO_a2p PO) (successors f)) p1.
Proof.
  intros.
  destruct (eq_atom_dec le a1); try subst a1.
    eapply entry_in_a2p_cfg; eauto.

    assert (exists p1, (PO_a2p PO) ! a1 = Some p1) as Hreach1 by eauto.
    eapply dfs_reachable_iff_get_some in Hreach1; eauto using le_in_cfg.
    apply ACfg.reachable_pred in Hreach1; auto.
    destruct Hreach1 as [a2 [Hinsc Hreach2]].
    eapply dfs_reachable_iff_get_some in Hreach2; eauto using le_in_cfg.
    destruct Hreach2 as [p2 Hget2].
    eapply in_asuccs__in_psuccs in Hinsc; eauto using Injective.dfs_inj.
    right.
    apply XPTree.children_of_tree__in_successors.
    exists p2. apply XPTree.successors_list_spec; auto.
Qed.

Lemma in_pchildren__in_acfg: forall (p : positive) (a : atom)
  (Ha2p : (PO_a2p PO) ! a = Some p)
  (Hin : In p
          (PCfg.XTree.children_of_tree
             (asuccs_psuccs (PO_a2p PO) (successors f)))),
  XATree.in_cfg (successors f) a.
Proof.
  intros.
  apply XPTree.children_of_tree__in_successors in Hin.
  destruct Hin as [p0 [scs0 [J1 J2]]].
  apply get_a2p__ptolist_atolist' in J1.
  destruct J1 as [l3 [atodo [J1 [J3 J4]]]]; subst scs0.
  apply in_ptolist__in_atolist in J2.
  destruct J2 as [a' [J2 J4]].
  simpl in Ha2p.
  assert (a = a') as EQ. 
    eapply Injective.dfs_inj; eauto.
  subst a'.
  eapply XATree.in_successors_list_intro in J3; eauto.
  eapply XATree.in_succ__in_cfg; eauto.
Qed.

Lemma a2p_vertexes: forall pv av (Ha2p: a2p_Vertex (PO_a2p PO) av pv),
  (PCfg.vertexes (asuccs_psuccs (PO_a2p PO) (successors f)) pv <-> 
   ACfg.vertexes (successors f) av).
Proof.
  intros.
  destruct pv as [p]. destruct av as [a].
  split; intro J.
    destruct J as [J | J].
      left. eapply in_pparents__in_aparents; eauto.
      eapply in_pchildren__in_acfg; eauto.

    destruct J as [J | J].
      left. eapply in_aparents__in_pparents; eauto using Injective.dfs_inj.  
      eapply get_a2p__in_pcfg; eauto.
Qed.

Definition wf_porder pentry: Prop :=
 forall n 
   (Hincfg: XPTree.in_cfg (asuccs_psuccs (PO_a2p PO) asuccs) n) 
   (Hneq: n <> pentry),
   exists p, 
     In p ((XPTree.make_predecessors (asuccs_psuccs (PO_a2p PO) asuccs)) ??? n) 
       /\ (p > n)%positive.

Lemma asuccs_psuccs_pres_order: forall pentry
  (Hwf: Order.wf_aorder le asuccs (PO_a2p PO))
  (Hentry: (PO_a2p PO) ! le = Some pentry),
  wf_porder pentry.
Proof.
  intros.
  intros p1 Hincfg Hnentry.
  assert (exists av, a2p_Vertex (PO_a2p PO) av (index p1)) as Hget.
    eapply in_vertexes__get_a2p; eauto.
  destruct Hget as [[a1] Hget].
  assert (G:=Hget).
  apply a2p_vertexes in G; auto.
  apply G in Hincfg.
  assert (a1 <> le) as Hnentry'.
    intro EQ. subst a1. simpl in Hget.
    uniq_result. auto.
  apply Hwf in Hnentry'.
  assert (J:=Hget).
  apply_clear Hnentry' in J.
  destruct J as [a2 [p2 [J1 [J2 J3]]]].
  apply XATree.make_predecessors_correct' in J1.
  exists p2.
  split; auto.
    apply XPTree.make_predecessors_correct.
    eapply in_asuccs__in_psuccs; eauto using Injective.dfs_inj.
Qed.

Lemma dfs_wf_porder: forall pentry 
  (Hentry: (PO_a2p PO) ! le = Some pentry),
  wf_porder pentry.
Proof.
  intros.
  eapply asuccs_psuccs_pres_order; eauto.
  eapply Order.dfs_wf_order; eauto.
Qed.

Lemma a2p_D_walk: forall pv1 pv2 (pvl : V_list) (pal : A_list) 
  (Hwk: D_walk (PCfg.vertexes (asuccs_psuccs (PO_a2p PO) (successors f)))
               (PCfg.arcs (asuccs_psuccs (PO_a2p PO) (successors f))) 
               pv1 pv2 pvl pal),
  exists avl, exists aal, exists av1, exists av2,
    D_walk (ACfg.vertexes (successors f)) (ACfg.arcs (successors f)) 
      av1 av2 avl aal /\
    a2p_Vertex (PO_a2p PO) av1 pv1 /\ a2p_Vertex (PO_a2p PO) av2 pv2 /\
    a2p_V_list (PO_a2p PO) avl pvl /\ a2p_A_list (PO_a2p PO) aal pal.
Proof.
  intros.
  induction Hwk.
    exists V_nil. exists A_nil.
    assert (J:=H).
    apply in_vertexes__get_a2p in J.
    destruct J as [av J].
    exists av. exists av.
    split.
      constructor. 
        eapply a2p_vertexes; eauto.
    split; auto.
    split; auto.
    split; constructor.

    destruct IHHwk as [avl [aal [av1 [av2 [J1 [J2 [J3 [J4 J5]]]]]]]].
    assert (J:=H).
    apply in_vertexes__get_a2p in J.
    destruct J as [av J].
    exists (av1::avl). exists (A_ends av av1::aal).
    exists av. exists av2.
    split.
      constructor; auto.
        eapply a2p_vertexes; eauto.
        eapply a2p_arcs; eauto.
    split; auto.
    split; auto.
    split.
      constructor; auto.
      constructor; simpl; auto.
Qed.

Lemma p2a_D_walk: forall av1 a2 avl aal
  (Hreach: forall a, ACfg.reachable asuccs a2 a <-> 
                     exists p, (PO_a2p PO) ! a = Some p)
  (Hwk: D_walk (ACfg.vertexes (successors f)) 
               (ACfg.arcs (successors f)) av1 (index a2) avl aal),
  exists pvl, exists pal, exists pv1, exists pv2,
    D_walk (PCfg.vertexes (asuccs_psuccs (PO_a2p PO) (successors f)))
           (PCfg.arcs (asuccs_psuccs (PO_a2p PO) (successors f))) 
           pv1 pv2 pvl pal /\
    a2p_Vertex (PO_a2p PO) av1 pv1 /\ a2p_Vertex (PO_a2p PO) (index a2) pv2 /\
    a2p_V_list (PO_a2p PO) avl pvl /\ a2p_A_list (PO_a2p PO) aal pal.
Proof.
  intros.
  remember (index a2) as va2.
  induction Hwk.
    subst x.
    assert (ACfg.reachable asuccs a2 a2) as Hr. 
      apply ACfg.reachable_entry; auto.
    apply Hreach in Hr.
    destruct Hr as [p Hr].
    exists V_nil. exists A_nil.
    exists (index p). exists (index p).
    split.
      constructor. 
        eapply a2p_vertexes; eauto. 
          simpl. auto.
    split; auto.
    split; auto.
    split; constructor.

    subst z.
    destruct IHHwk as [avl [aal [av1 [av2 [J1 [J2 [J3 [J4 J5]]]]]]]]; auto.
    destruct x as [x].
    assert (ACfg.reachable asuccs a2 x) as Hr. 
      destruct y as [y].
      eapply ACfg.reachable_succ with (n:=y); eauto.
      unfold ACfg.reachable. eauto.
    apply Hreach in Hr.
    destruct Hr as [p Hr].
    exists (av1::avl). exists (A_ends (index p) av1::aal).
    exists (index p). exists av2.
    split.
      constructor; auto.
        eapply a2p_vertexes; eauto.
          simpl. auto.
        eapply a2p_arcs; eauto.
          simpl. auto.
    split; auto.
    split; auto.
    split.
      constructor; auto.
      constructor; simpl; auto.
Qed.

Lemma unreachable__get_a2p: forall l2,
  ~ cfg.reachable f l2 <-> (PO_a2p PO) ! l2 = None.
Proof.
  intros.
  apply dfs_unreachable_iff_get_none with (l0:=l2) in Hdfs; 
    auto using le_in_cfg.
  apply getEntryLabel__getEntryBlock in Hentry.
  destruct Hentry as [be [Hentry' EQ]]; subst. 
  unfold cfg.reachable. rewrite Hentry'.
  unfold ACfg.reachable in Hdfs. destruct be as [le ? ? ?].
  simpl in Hdfs. auto.
Qed.

Lemma reachable__get_a2p: forall l2,
  cfg.reachable f l2 <-> exists p2, (PO_a2p PO) ! l2 = Some p2.
Proof.
  intros.
  apply dfs_reachable_iff_get_some with (l0:=l2) in Hdfs; 
    auto using le_in_cfg.
  apply getEntryLabel__getEntryBlock in Hentry.
  destruct Hentry as [be [Hentry' EQ]]; subst. 
  unfold cfg.reachable. rewrite Hentry'.
  unfold ACfg.reachable in Hdfs. destruct be as [le ? ? ?].
  simpl in Hdfs. auto.
Qed.

Lemma In__a2p_V_list: forall p pvl a avl
  (Hget: (PO_a2p PO) ! a = Some p) (J: a2p_V_list (PO_a2p PO) avl pvl), 
  In (index p) pvl <-> In (index a) avl.
Proof.
  induction 2; intros.
    split; eauto.

    destruct x as [x]. destruct y as [y].
    simpl in H.
    simpl.
    split; intro Hin.
    Case "1".
      destruct Hin as [Hin | Hin]; try tauto.
        inversion Hin; subst y.
        assert (a = x) as EQ.
          eapply Injective.dfs_inj; eauto.
        subst x.
        auto.
    Case "2".
      destruct Hin as [Hin | Hin]; try tauto.
        inversion Hin; subst x.
        uniq_result.
        auto.
Qed.

Lemma areachable__preachable: forall pe l3 p3 
  (Hpentry : (PO_a2p PO) ! le = Some pe) (Hget3 : (PO_a2p PO) ! l3 = Some p3)
  (Hreach3 : ACfg.reachable asuccs le l3),
  PCfg.reachable (asuccs_psuccs (PO_a2p PO) asuccs) pe p3.
Proof.
  unfold ACfg.reachable.
  intros.
  destruct Hreach3 as [vl [al Hreach3]].
  unfold ATree.elt, l in *.
  remember (index l3) as av3.
  remember (index le) as ave.
  generalize dependent l3.
  generalize dependent p3.
  induction Hreach3; intros.
  Case "base".
    subst x. inversion Heqav3; subst l3.
    assert (pe = p3) as EQ. uniq_result. auto.
    subst p3. apply PCfg.reachable_entry.
    eapply entry_in_a2p_cfg; eauto.
  Case "ind".
    subst x z.
    destruct y as [ay].
    assert (ACfg.reachable asuccs le ay) as Hreachy.
      unfold ACfg.reachable. eauto.
    eapply dfs_reachable_iff_get_some in Hreachy; 
      try solve [ eauto | apply le_in_cfg; auto].
      destruct Hreachy as [py Hgety].
      assert (Hreachy:=Hgety).
      apply IHHreach3 in Hreachy; auto.
      assert (PCfg.arcs (asuccs_psuccs (PO_a2p PO) asuccs)
               (A_ends (index p3) (index py))) as Harcs.
        eapply a2p_arcs with (av1:=index l3) (av2:=index ay); simpl; eauto.
      eapply PCfg.reachable_succ; eauto.
Qed.

Lemma areachable__ex_preachable: forall pe l3
  (Hpentry : (PO_a2p PO) ! le = Some pe) 
  (Hreach3 : ACfg.reachable asuccs le l3),
  exists p3,
    (PO_a2p PO) ! l3 = Some p3 /\
    PCfg.reachable (asuccs_psuccs (PO_a2p PO) asuccs) pe p3.
Proof.
  intros.
  assert (Hget3:=@reachable__get_a2p l3).
  unfold reachable in Hget3.
  assert (J:=Hentry).
  apply getEntryLabel__getEntryBlock in J.
  destruct J as [[le' []] [Hentry' Heq]]; simpl in Heq; subst le'.
  rewrite Hentry' in Hget3.
  assert (J:=Hreach3).
  apply Hget3 in J.
  destruct J as [p3 J].
  exists p3. 
  split; auto.
    eapply areachable__preachable; eauto. 
Qed.

Lemma a2p_reachable: forall pe p3 l3
  (Hreach: cfg.reachable f l3)
  (Hgete: (PO_a2p PO) ! le = Some pe)
  (Hget3: (PO_a2p PO) ! l3 = Some p3),
  PCfg.reachable (asuccs_psuccs (PO_a2p PO) asuccs) pe p3.
Proof.
  unfold cfg.reachable.
  intros.
  apply getEntryLabel__getEntryBlock in Hentry.
  destruct Hentry as [[le' []] [Hentry' Heq]]; simpl in Heq; subst le'.
  rewrite Hentry' in Hreach. 
  eapply areachable__preachable; eauto.
Qed.

Lemma reachable_isnt_bot: forall (l3 : l) (res : PMap.t LDoms.t) 
  (p3 : positive) (pe : positive)
  (Hpentry : (PO_a2p PO) ! le = Some pe) ni
  (H0 : pdom_analyze (asuccs_psuccs (PO_a2p PO) asuccs) pe ni = res)
  (Hget3 : (PO_a2p PO) ! l3 = Some p3)
  (Hreach3 : ACfg.reachable asuccs le l3)
  (Hwf_porder : wf_porder pe),
  exists dts3 : list positive, res ?? p3 = Some dts3.
Proof.
  intros.
  apply DomSound.reachable_isnt_bot with (n:=p3) (ni:=ni) in Hwf_porder; auto.
    simpl in Hwf_porder. rewrite H0 in Hwf_porder.
    unfold LDoms.bot in Hwf_porder.
    destruct (res ?? p3); eauto. congruence.

    eapply areachable__preachable; eauto.      
Qed.

Lemma preachable__areachable: forall pe l3 p3
  (Hpentry : (PO_a2p PO) ! le = Some pe) (Hget3 : (PO_a2p PO) ! l3 = Some p3)
  (Hreach3 : PCfg.reachable (asuccs_psuccs (PO_a2p PO) asuccs) pe p3),
  ACfg.reachable asuccs le l3.
Proof.
  unfold PCfg.reachable.
  intros.
  destruct Hreach3 as [vl [al Hreach3]].
  unfold PTree.elt, l in *.
  remember (index p3) as pv3.
  remember (index pe) as pve.
  generalize dependent l3.
  generalize dependent p3.
  induction Hreach3; intros.
  Case "base".
    subst x. 
    inversion Heqpv3; subst pe.
    assert (l3 = le) as EQ.
      eapply Injective.dfs_inj; eauto.
    subst.
    apply ACfg.reachable_entry.
      apply le_in_cfg; auto.
  Case "ind".
    subst x z.
    destruct y as [py].
    assert (exists avy, a2p_Vertex (PO_a2p PO) avy (index py)) as Hgety.
      apply in_vertexes__get_a2p with (asuccs:=asuccs);auto.
      simpl. simpl in H0. 
      eapply XPTree.has_succ__in_cfg; eauto.
    destruct Hgety as [[ay] Hgety]. simpl in Hgety.
    assert (Hreachy:=Hgety).
    apply IHHreach3 in Hreachy; auto.
    assert (ACfg.arcs asuccs (A_ends (index l3) (index ay))) as Harcs.
      eapply a2p_arcs with (pv1:=index p3) (pv2:=index py); simpl; eauto.
    eapply ACfg.reachable_succ; eauto.
Qed.

Lemma p2a_reachable: forall pe p3 l3
  (Hreach: PCfg.reachable (asuccs_psuccs (PO_a2p PO) asuccs) pe p3)
  (Hgete: (PO_a2p PO) ! le = Some pe)
  (Hget3: (PO_a2p PO) ! l3 = Some p3),
  cfg.reachable f l3.
Proof.
  intros.
  unfold cfg.reachable.
  apply getEntryLabel__getEntryBlock in Hentry.
  destruct Hentry as [be [Hentry' Heq]].
  rewrite Hentry'.
  destruct be as [le' ? ? ?]; simpl in Heq; subst le'.
  eapply preachable__areachable; eauto.
Qed.

Lemma reachable_isnt_bot': forall (l3: l) (pe : positive)
  (p2 : PTree.elt) (J2 : (PO_a2p PO) ! l3 = Some p2) 
  (J3 : (PO_a2p PO) ! le = Some pe) ni,
  exists dts2 : list positive,
    (pdom_analyze (asuccs_psuccs (PO_a2p PO) asuccs) pe ni) ?? p2 = Some dts2.
Proof.
  intros.
  assert (Hwf_porder:=J3).
  eapply dfs_wf_porder in Hwf_porder; eauto.
  assert (Hreach_get:=@reachable__get_a2p l3).
  assert (exists p3, (PO_a2p PO) ! l3 = Some p3) as Hget3' by eauto.
  apply Hreach_get in Hget3'.
  eapply a2p_reachable in Hget3'; eauto.
  eapply preachable__areachable in Hget3'; eauto.
  eapply reachable_isnt_bot in Hwf_porder; eauto.
Qed.

Lemma adom_pdom: forall (l1 l2 : l) p2 p1 pe
  (Hget2 : (PO_a2p PO) ! l2 = Some p2)
  (Hsdom : ACfg.domination (successors f) le l1 l2)
  (Hget1 : (PO_a2p PO) ! l1 = Some p1) (Hgetle : (PO_a2p PO) ! le = Some pe),
  PCfg.domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2.
Proof.
  intros.
  intros vl al Hwk.
  apply a2p_D_walk in Hwk.
  destruct Hwk as [avl [aal [[a1] [[a2] [Hwk [J1 [J2 [J3 J4]]]]]]]].
  simpl in *.
  eapply Injective.dfs_inj in Hget2; eauto. subst a1.
  eapply Injective.dfs_inj in Hgetle; eauto. subst a2.
  apply Hsdom in Hwk.
  destruct Hwk as [Hin | Heq]; try subst l1.
    left. eapply In__a2p_V_list in Hin; eauto.
    right. uniq_result. auto.
Qed.

Lemma asdom_psdom: forall (l1 l2 : l) p2 p1 pe
  (Hget2 : (PO_a2p PO) ! l2 = Some p2)
  (Hsdom : ACfg.strict_domination (successors f) le l1 l2)
  (Hget1 : (PO_a2p PO) ! l1 = Some p1) (Hgetle : (PO_a2p PO) ! le = Some pe),
  PCfg.strict_domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2.
Proof.
  intros.
  intros vl al Hwk.
  apply a2p_D_walk in Hwk.
  destruct Hwk as [avl [aal [[a1] [[a2] [Hwk [J1 [J2 [J3 J4]]]]]]]].
  simpl in *.
  eapply Injective.dfs_inj in Hget2; eauto. subst a1.
  eapply Injective.dfs_inj in Hgetle; eauto. subst a2.
  apply Hsdom in Hwk.
  destruct Hwk as [Hin Hneq].
  split.
    eapply In__a2p_V_list in Hin; eauto.

    intro EQ. subst. apply Hneq.
    eapply Injective.dfs_inj in Hget1; eauto.
Qed.

Lemma p2a_strict_domination: forall (l1 l2 : l)
  (Hreach2: cfg.reachable f l2)
  (Hsdom: cfg.strict_domination f l1 l2),
  exists p1, exists p2, exists pe, 
    PCfg.strict_domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2 /\
    (PO_a2p PO) ! l1 = Some p1 /\ (PO_a2p PO) ! l2 = Some p2 /\
    (PO_a2p PO) ! le = Some pe.
Proof.
  intros.
  assert (Hentry':=Hentry).
  apply getEntryLabel__getEntryBlock in Hentry'.
  destruct Hentry' as [[le0 ?] [Hentry' EQ]]; simpl in EQ; subst le0.
  assert (cfg.reachable f l1) as Hreach1.
    eapply DecDom.sdom_reachable; eauto.
  assert (cfg.reachable f le) as Hreachle.
    eapply reach.reachable_entrypoint; eauto.
  apply reachable__get_a2p in Hreach1.
  apply reachable__get_a2p in Hreach2.
  apply reachable__get_a2p in Hreachle.
  destruct Hreach1 as [p1 Hget1].
  destruct Hreach2 as [p2 Hget2].
  destruct Hreachle as [pe Hgetle].
  exists p1. exists p2. exists pe.
  split.
  Case "1".
    unfold cfg.strict_domination, cfg.domination,
           strict_domination, domination in *.
    rewrite Hentry' in Hsdom. 
    eapply asdom_psdom; eauto.
  Case "2".
    split; auto.
Qed.

Lemma preachable_ex: forall (p2 : positive) pe
  (Hrd2: PCfg.reachable (asuccs_psuccs (PO_a2p PO) asuccs) pe p2),
  exists l2, Some p2 = (PO_a2p PO) ! l2.
Proof.
  intros.
  destruct Hrd2 as [vl [al Hwk]].
  eapply DW_endx_inv in Hwk; eauto.
  apply in_vertexes__get_a2p in Hwk.
  destruct Hwk as [[l2] Hget2]. eauto.
Qed.

Lemma preachable__ex_areachable: forall pe p3
  (Hpentry : (PO_a2p PO) ! le = Some pe) 
  (Hreach3 : PCfg.reachable (asuccs_psuccs (PO_a2p PO) asuccs) pe p3),
  exists l3, (PO_a2p PO) ! l3 = Some p3 /\ ACfg.reachable asuccs le l3.
Proof.
  intros.
  assert (J:=Hreach3).
  apply preachable_ex in J.
  destruct J as [l3 Hget3].
  exists l3.
  split; eauto using preachable__areachable.
Qed.

Lemma preachable__in_get_reachable_nodes: forall pe p0
  (Hgete: Some pe = (PO_a2p PO) ! le)
  (Hwfcfg: forall (p : l) (ps0 : phinodes) (cs0 : cmds) 
                  (tmn0 : terminator) (l2 : l),
     blockInFdefB (p, stmts_intro ps0 cs0 tmn0) f ->
     In l2 (successors_terminator tmn0) -> In l2 (bound_fdef f)),
  PCfg.reachable (asuccs_psuccs (PO_a2p PO) (successors f)) pe p0 <->
  In p0 (get_reachable_nodes (bound_fdef f) (PO_a2p PO)).
Proof.
  intros.
  split; intro J.
    eapply preachable_ex in J; eauto.
    destruct J as [l3 Hget3].
    apply get_reachable_nodes_spec.
    exists l3. 
    split; auto.
      apply reachable__in_bound; auto.
      apply reachable__get_a2p; eauto.

    apply get_reachable_nodes_spec in J.
    destruct J as [l0 [Hget0 Hin0]].
    eapply areachable__preachable; eauto.
      eapply dfs_reachable_iff_get_some; eauto.
        apply le_in_cfg; auto.  
Qed.

Hypothesis Hreach: forall a, 
  ACfg.reachable asuccs le a <-> exists p : positive, (PO_a2p PO) ! a = Some p.

Lemma pdom_adom: forall (l1 l2 : l) (p1 p2 : positive)
  (Hget1: Some p1 = (PO_a2p PO) ! l1) (Hget2: Some p2 = (PO_a2p PO) ! l2) pe
  (Hget2: Some pe = (PO_a2p PO) ! le) 
  (Hdom: PCfg.domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2),
  ACfg.domination asuccs le l1 l2.
Proof.
  intros.
  unfold PCfg.domination in Hdom. 
  intros vl al Hwk.
  apply p2a_D_walk in Hwk; auto.
    destruct Hwk as [pvl [pal [[p1'] [[p2'] [Hwk [J1 [J2 [J3 J4]]]]]]]].
    simpl in J1, J2. symmetry_ctx. 
    assert (p2 = p1') as EQ1. uniq_result. auto.
    assert (pe = p2') as EQ2. uniq_result. auto.
    subst p1' p2'.
    apply Hdom in Hwk.
    destruct Hwk as [Hin | Heq]; try subst p1.
      eapply In__a2p_V_list in Hin; eauto.
      right. eapply Injective.dfs_inj; eauto.
Qed.

Lemma a2p_domination: forall (l1 l2 : l) (p1 p2 : positive)
  (Hget1: Some p1 = (PO_a2p PO) ! l1) (Hget2: Some p2 = (PO_a2p PO) ! l2) pe
  (Hget2: Some pe = (PO_a2p PO) ! le) 
  (Hdom: PCfg.domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2),
  cfg.domination f l1 l2.
Proof.
  intros.
  unfold cfg.domination. 
  assert (Hentry':=Hentry).
  apply getEntryLabel__getEntryBlock in Hentry'.
  destruct Hentry' as [[le0 ?] [Hentry' EQ]]; simpl in EQ; subst le0.
  rewrite Hentry'.
  eapply pdom_adom with (l1:=l1)(l2:=l2) in Hget0; eauto.
Qed.

Lemma psdom_asdom: forall (l1 l2 : l) (p1 p2 : positive)
  (Hget1: Some p1 = (PO_a2p PO) ! l1) (Hget2: Some p2 = (PO_a2p PO) ! l2) pe
  (Hget2: Some pe = (PO_a2p PO) ! le) 
  (Hsdom: PCfg.strict_domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2),
  ACfg.strict_domination asuccs le l1 l2.
Proof.
  intros.
  unfold PCfg.strict_domination in Hsdom. 
  intros vl al Hwk.
  apply p2a_D_walk in Hwk; auto.
    destruct Hwk as [pvl [pal [[p1'] [[p2'] [Hwk [J1 [J2 [J3 J4]]]]]]]].
    simpl in J1, J2. symmetry_ctx. 
    assert (p2 = p1') as EQ1. uniq_result. auto.
    assert (pe = p2') as EQ2. uniq_result. auto.
    subst p1' p2'.
    apply Hsdom in Hwk.
    destruct Hwk as [Hin Hneq].
    split.
      eapply In__a2p_V_list in Hin; eauto.
      intros EQ. subst l1. uniq_result. auto.
Qed.

Lemma asdom_ex_psdom: forall (l1 l2 : l) (p2 : positive)
  (Hget2: Some p2 = (PO_a2p PO) ! l2) pe
  (Hget2: Some pe = (PO_a2p PO) ! le) 
  (Hsdom: ACfg.strict_domination asuccs le l1 l2),
  exists p1, 
    Some p1 = (PO_a2p PO) ! l1 /\
    PCfg.strict_domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2.
Proof.
  intros.
  assert (XATree.in_cfg asuccs le) as Hincfg.
    apply le_in_cfg; auto.
  assert (ACfg.reachable asuccs le l2) as Hreach2.
    eapply dfs_reachable_iff_get_some; eauto.
  assert (ACfg.reachable asuccs le l1) as Hreach1.
    eapply ACfg.sdom_reachable; eauto. 
  eapply dfs_reachable_iff_get_some in Hreach1; eauto.
  destruct Hreach1 as [p1 Hget1].
  exists p1.
  split; eauto using asdom_psdom.
Qed.

Lemma pidom_aidom: forall p1 p2 l1 l2 pe (Hgete: Some pe = (PO_a2p PO) ! le)
  (Hget1: (PO_a2p PO) ! l1 = Some p1) (Hget2: (PO_a2p PO) ! l2 = Some p2),
  PCfg.imm_domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2 ->
  ACfg.imm_domination asuccs le l1 l2.
Proof.
  intros.
  destruct H as [H1 H2].
  split.
    eapply psdom_asdom; eauto.
 
    intros l0 Hsdom0.
    eapply asdom_ex_psdom in Hsdom0; eauto.
    destruct Hsdom0 as [p0 [Hget0 Hsdom0]].
    eapply pdom_adom; eauto.
Qed.

Lemma psdom_ex: forall (p1 p2 : positive) pe
  (Hrd2: PCfg.reachable (asuccs_psuccs (PO_a2p PO) asuccs) pe p2)
  (Hsdom: PCfg.strict_domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2),
  exists l1, Some p1 = (PO_a2p PO) ! l1.
Proof.
  intros.
  unfold PCfg.strict_domination in Hsdom. 
  destruct Hrd2 as [vl [al Hwk]].
  assert (J:=Hwk).
  apply Hsdom in J.
  destruct J as [Hin Hneq].
  eapply DW_invl_inv in Hin; eauto.
  apply in_vertexes__get_a2p in Hin.
  destruct Hin as [[l1] Hget1]. eauto.
Qed.

Lemma psdom_ex_asdom: forall (l2 : l) (p1 p2 : positive)
  (Hget2: Some p2 = (PO_a2p PO) ! l2) pe
  (Hget2: Some pe = (PO_a2p PO) ! le) 
  (Hrd2: PCfg.reachable (asuccs_psuccs (PO_a2p PO) asuccs) pe p2)
  (Hsdom: PCfg.strict_domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2),
  exists l1,
    Some p1 = (PO_a2p PO) ! l1 /\ ACfg.strict_domination asuccs le l1 l2.
Proof.
  intros.
  assert (J:=Hsdom).
  apply psdom_ex in J; auto.
  destruct J as [l1 Hget1].
  exists l1.
  split; eauto using psdom_asdom.
Qed.

Lemma aidom_pidom: forall l1 l2 pe
  (Hgete: Some pe = (PO_a2p PO) ! le)
  (Hrd2: ACfg.reachable asuccs le l2)
  (Hidom: ACfg.imm_domination asuccs le l1 l2),
  exists p1 : positive,
    exists p2 : positive,
      (PO_a2p PO) ! l1 = Some p1 /\
      (PO_a2p PO) ! l2 = Some p2 /\
      PCfg.imm_domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2.
Proof.
  intros.
  destruct Hidom as [Hsdom Hidom].
  assert (XATree.in_cfg asuccs le) as Hincfg.
    apply le_in_cfg; auto.
  assert (ACfg.reachable asuccs le l1) as Hreach1.
    eapply ACfg.sdom_reachable; eauto. 
  eapply dfs_reachable_iff_get_some in Hreach1; eauto.
  destruct Hreach1 as [p1 Hget1].
  assert (Hget2:=Hrd2).
  eapply dfs_reachable_iff_get_some in Hget2; eauto.
  destruct Hget2 as [p2 Hget2].
  exists p1. exists p2.
  split; auto.
  split; auto.
  split.
    eapply asdom_psdom; eauto.

    intros l0 Hsdom0.
    eapply psdom_ex_asdom in Hsdom0; eauto using areachable__preachable.
    destruct Hsdom0 as [p0 [Hget0 Hsdom0]].
    eapply adom_pdom; eauto.
Qed.

End adom_pdom.

(* The main function that computes dominators. *)
Definition dom_analyze (f: fdef) : PMap.t LDoms.t * ATree.t positive :=
  let asuccs := cfg.successors f in
  match LLVMinfra.getEntryLabel f with
  | Some le =>
      let '(mkPO _ a2p) := dfs asuccs le 1%positive in
      let psuccs := asuccs_psuccs a2p asuccs in
      match ATree.get le a2p with
      | Some pe => (pdom_analyze psuccs pe (num_iters f), a2p)
      | None => (PMap.init LDoms.top, ATree.empty _)
      end
  | None => (PMap.init LDoms.top, ATree.empty _)
  end.

(* Compute a map from positive to atom in terms of the map from atom to 
   positive. *)
Definition a2p_p2a (a2p:ATree.t positive) : PTree.t l :=
  ATree.fold (fun acc from to => PTree.set to from acc) a2p (PTree.empty l).

(*Properties of a2p_p2a *)
Lemma a2p_p2a_spec2: forall a2p a p (Hget: (a2p_p2a a2p) ? p = Some a),
  a2p ! a = Some p.
Proof.
  set (P := fun a2p p2a =>
            forall a p (Hget: p2a ? p = Some a),
            a2p ! a = Some p).
  unfold a2p_p2a.
  intros a2p.
  apply ATree_Properties.fold_rec with (P := P).
  Case "extensionality".
  intros m m' a H.
  unfold P; intros.
  rewrite <- H. 
  apply H0; auto.
  Case "base case".
  intros a p. rewrite PTree.gempty. intros. congruence.
  Case "inductive case".
  intros m a0 k v Hnone Hget0 IH.
  unfold P in *; intros. 
  rewrite PTree.gsspec in Hget.
  rewrite ATree.gsspec.
  destruct (ATree.elt_eq a k); subst.
    destruct_if; auto.
      apply IH in H0. congruence.

    destruct_if; auto.
      congruence.
Qed.

Lemma a2p_p2a_inj: forall a2p (s1 s2 : positive) (t : ATree.elt)
  (Hget1: (a2p_p2a a2p) ? s1 = Some t) (Hget2: (a2p_p2a a2p) ? s2 = Some t),
  s1 = s2.
Proof.
  intros.
  apply a2p_p2a_spec2 in Hget1.
  apply a2p_p2a_spec2 in Hget2.
  uniq_result. auto.
Qed.

Definition ps2as_fun p2a (acc: ls) (p:positive) :=
  match p2a ? p with
  | Some a => a::acc
  | None => acc
  end.

Definition ps2as (p2a: PTree.t l) (ps: list positive) : list l :=
  List.fold_left (ps2as_fun p2a) ps nil.


Lemma in_init__in_ps2as: forall a p2a ps acc (Hin: In a acc),
  In a (fold_left (ps2as_fun p2a) ps acc).
Proof.
  induction ps as [|p ps]; simpl; intros; auto.
    apply IHps.
    unfold ps2as_fun. 
    destruct (p2a ? p); simpl; auto.
Qed.

Lemma in_ps2as__incl: forall a p2a ps init1 init2 (Hinc: incl init1 init2)
  (Hin : In a (fold_left (ps2as_fun p2a) ps init1)),
  In a (fold_left (ps2as_fun p2a) ps init2).
Proof.
  induction ps as [|p ps]; simpl; intros.
    eauto with datatypes v62.

    eapply IHps; eauto.
      unfold ps2as_fun. 
      destruct (p2a ? p); simpl; auto with datatypes v62.
Qed.

Lemma in_ps2as__in_ps_aux: forall (a : atom) (a2p : ATree.t positive) 
  (ps : list positive) init
  (Hin: In a (fold_left (ps2as_fun (a2p_p2a a2p)) ps init)),
  In a init \/ exists p : positive, a2p ! a = Some p /\ In p ps.
Proof.
  induction ps as [|p ps]; simpl; intros; auto.
    apply IHps in Hin.
    destruct Hin as [Hin | Hin].
    Case "1".
      unfold ps2as_fun in Hin.
      case_eq (a2p_p2a a2p) ? p.
      SCase "1.1".
        intros l0 Hsome.
        rewrite Hsome in Hin. 
        destruct_in Hin.
        apply a2p_p2a_spec2 in Hsome. eauto.
      SCase "1.2".
        intros Hnone.
        rewrite Hnone in Hin; auto.
    Case "2".
      destruct Hin as [p' [Hin1 Hin2]]; eauto.
Qed.

Lemma in_ps2as__in_ps: forall (a : atom) a2p ps
  (Hin : In a (ps2as (a2p_p2a a2p) ps)),
  exists p, a2p ! a = Some p /\ In p ps.
Proof.
  unfold ps2as.
  intros.
  apply in_ps2as__in_ps_aux in Hin.
  destruct Hin as [Hin | Hin]; tauto.
Qed.

Section in_ps__in_ps2as.

Variable a2p: ATree.t positive.
Hypothesis Hinj: forall a1 a2 p (Hin1: a2p ! a1 = Some p) 
                 (Hin2: a2p ! a2 = Some p), a1 = a2.

Lemma a2p_p2a_spec1: forall a p 
  (Hget: a2p ! a = Some p),
  (a2p_p2a a2p) ? p = Some a.
Proof.
  set (P := fun a2p p2a =>
            forall
            (Hinj: forall a1 a2 p (Hin1: a2p ! a1 = Some p) 
                   (Hin2: a2p ! a2 = Some p), a1 = a2)
            a p (Hget: a2p ! a = Some p),
            p2a ? p = Some a).
  unfold a2p_p2a.
  revert Hinj.
  apply ATree_Properties.fold_rec with (P := P).
  Case "extensionality".
  intros m m' a H.
  unfold P; intros.
  rewrite <- H in Hget. 
  apply H0; auto.
    intros.
    rewrite H in Hin1, Hin2. eauto.
  Case "base case".
  intros a p. rewrite ATree.gempty. intros. congruence.
  Case "inductive case".
  intros m a0 k v Hnone Hget0 IH.
  unfold P in *; intros. 
  rewrite ATree.gsspec in Hget.
  rewrite PTree.gsspec.
  destruct (ATree.elt_eq a k); subst.
    uniq_result.
    destruct_if. 
      congruence.

    destruct_if. 
      contradict n.
      apply Hinj with (p:=v); rewrite ATree.gsspec; destruct_if; congruence.

      apply IH; auto.
        intros.
        apply Hinj with (p:=p0);
          rewrite ATree.gsspec; destruct_if; congruence.
Qed.

Lemma in_ps__in_ps2as: forall a p (Hget: a2p ! a = Some p) ps
  (Hin : In p ps),
  ListSet.set_In a (ps2as (a2p_p2a a2p) ps).
Proof.
  unfold ps2as.
  induction ps; simpl; intros; auto.
    destruct Hin as [Hin | Hin]; subst; simpl.
      apply in_init__in_ps2as.
      unfold ps2as_fun. 
      erewrite a2p_p2a_spec1; simpl; eauto.
      
      apply IHps in Hin.
      eapply in_ps2as__incl; eauto.
        intros x Hinx. tauto.
Qed.

End in_ps__in_ps2as.

(* The iteration bound we choose is large enough to ensure termination. *)
Section Num_iters__is__large_enough.

Variable f:fdef.
Variable PO: PostOrder.
Variable le: l.
Hypothesis Hentry: getEntryLabel f = Some le.
Hypothesis Hdfs: dfs (successors f) le 1 = PO.
Hypothesis Huniq: uniqFdef f.
Hypothesis branches_in_bound_fdef: forall p ps0 cs0 tmn0 l2
  (J3 : blockInFdefB (p, stmts_intro ps0 cs0 tmn0) f)
  (J4 : In l2 (successors_terminator tmn0)),
  In l2 (bound_fdef f).

Lemma num_iters__is__large_enough:
  (num_iters f >= 
     Termination.num_iters (asuccs_psuccs (PO_a2p PO) (successors f)))%positive.
Proof.
  intros. 
  assert (NoDup (XATree.elements_of_cfg (successors f) eq_atom_dec)) as Hpnodup.
    apply remove_redundancy_NoDup; auto.
  assert (NoDup (bound_fdef f)) as Hnodupf.
    apply uniqFdef__NoDup_bounds_fdef; auto.
  assert (J:=elements_of_acfg__eq__bound).
  eapply NoDup_set_eq_length_eq in J; eauto using eq_atom_dec.
  destruct f as [? bs]. simpl.
  unfold num_iters, Termination.num_iters, pnum_of_blocks_in_fdef,
         Termination.psize_of_cfg.
  repeat rewrite plength_of_blocks__eq__P_of_plus_nat.
  apply Pcubeplus_ge.
  assert (length 
           (XPTree.elements_of_cfg 
             (asuccs_psuccs (PO_a2p PO) (successors_blocks bs)) 
               positive_eq_dec) <=
           length (XATree.elements_of_cfg (successors_blocks bs) eq_atom_dec))%nat 
          as Hle.
    apply NoDup_incl_inj_length with (f:=fun k => (PO_a2p PO) ! k); 
      auto using eq_atom_dec.
      apply remove_redundancy_NoDup; auto.

      intros a1 Hina1.
      assert (Hincfg: PCfg.vertexes 
                (asuccs_psuccs (PO_a2p PO) (successors_blocks bs)) (index a1)).
        apply XPTree.in_elements_of_cfg__in_cfg in Hina1; auto.
      assert (J1:=Hincfg).
      apply in_vertexes__get_a2p in J1.
      destruct J1 as [[b1] J1].
      exists b1.
      split; auto.
        eapply a2p_vertexes in J1; eauto.
        apply XATree.in_elements_of_cfg__in_cfg.
        apply J1 in Hincfg; auto.
  unfold Termination.elements_of_cfg, plength.
  simpl in *. unfold ATree.elt, PTree.elt in *. rewrite <- J.
  remember (@length atom (XATree.elements_of_cfg (successors_blocks bs) eq_atom_dec)) 
    as A.
  remember (@length positive
             (XPTree.elements_of_cfg
               (asuccs_psuccs (PO_a2p PO) (successors_blocks bs))
                  positive_eq_dec)) as B.
  rewrite <- P_of_plus_one_nat__P_of_succ_nat.
  change 3%positive with (2+1)%positive.
  rewrite <- P_of_plus_nat_Pplus_commut.
  assert (A >= B)%nat as J'. omega.
  apply P_of_plus_nat__ge with (q:=1%positive) in J'.
  zify. omega.
Qed.

End Num_iters__is__large_enough.

Ltac termination_tac2 :=
let foo a2p f pe :=
  match goal with
  | Hdfs : dfs _ _ _ = _ |- _ =>
    let J := fresh "J" in
    let dms := fresh "dms" in
    let Hfix_tmn := fresh "Hfix_tmn" in
    assert (J:=Hdfs);
    apply num_iters__is__large_enough in J; auto;
    eapply Termination.fixpoint_wf with (entrypoint:=pe) in J; 
      try solve [eauto | eapply dfs_wf_porder in Hdfs; eauto];
    unfold Termination.entrypoints in J;
    destruct J as [dms Hfix_tmn]; simpl in Hfix_tmn;
    rewrite Hfix_tmn in *
  end in
match goal with
| |- context [DomDS.fixpoint (asuccs_psuccs ?a2p (successors ?f)) _ 
               ((?pe, _)::_) ?ni] => foo a2p f pe
| _: context [DomDS.fixpoint (asuccs_psuccs ?a2p (successors ?f)) _ 
             ((?pe, _)::_) ?ni] |- _ => foo a2p f pe
end.

(* Show that the algorithm meets the specification. *)
Module AlgDom : ALGDOM_WITH_TREE.

Definition p2a_dom p2a bd (res: LDoms.t) : list atom :=
match res with
| Some dts2 => ps2as p2a dts2
| None => bd
end.

Definition bound_dom (a2p:ATree.t positive) p2a bd (res: PMap.t LDoms.t) 
  (l0:atom) : list atom :=
match a2p ! l0 with
| Some p0 => p2a_dom p2a bd (res ?? p0)
| None => bd
end.

Definition sdom f : atom -> list atom :=
let '(dt, a2p) := dom_analyze f in
let b := cfg.bound_fdef f in
let p2a := a2p_p2a a2p in
bound_dom a2p p2a b dt.

Ltac simpl_sdom :=
match goal with
| Hhasentry: getEntryBlock ?f <> None |- _ =>
  let Hentry := fresh "Hentry" in
  let entry := fresh "entry" in
  case_eq (getEntryBlock f); try solve [intros; try congruence];
  intros entry Hentry
| _ => idtac
end;
match goal with
| Hentry : getEntryBlock ?f = Some _ |- _ =>
  apply getEntryBlock__getEntryLabel in Hentry; simpl in Hentry
| Hentry : getEntryBlock _ = None |- _ =>
  unfold sdom, dom_analyze, bound_dom;
  apply getEntryBlock__getEntryLabel_none in Hentry;
  rewrite Hentry
| Hsdom: strict_domination _ _ _ |- _ =>
  let Hentry := fresh "Hentry" in
  let entry := fresh "entry" in
  assert (Hentry:=Hsdom);
  apply DecDom.strict_domination__getEntryLabel in Hentry;
  destruct Hentry as [entry Hentry]
| _ => idtac
end;
match goal with
| Hentry : getEntryLabel ?f = Some ?le |- _ =>
  unfold sdom, dom_analyze, bound_dom;
  fill_holes_in_ctx;
  case_eq (dfs (cfg.successors f) le 1);
  intros PO_cnt PO_a2p Hdfs;
  assert (Hdfs_entry:=Hdfs);
  apply ReachableEntry.dfs_wf in Hdfs_entry;
  simpl in Hdfs_entry;
  case_eq (PO_a2p ! le); try solve [intros; congruence];
  intros pe Hl2p;
  fill_holes_in_ctx;
  try rewrite Hdfs in *; try rewrite Hl2p in *
| _ => idtac
end.

Lemma dom_entrypoint : forall f l0 s0
  (Hentry : getEntryBlock f = Some (l0, s0)),
  sdom f l0 = nil.
Proof.
  intros. 
  simpl_sdom.
  rewrite DomSound.adom_entrypoint.
  simpl. unfold ps2as. auto.
Qed.

Definition branchs_in_fdef f :=
  forall (p : l) (ps0 : phinodes) (cs0 : cmds) 
         (tmn0 : terminator) (l2 : l),
  blockInFdefB (p, stmts_intro ps0 cs0 tmn0) f ->
  In l2 (successors_terminator tmn0) -> In l2 (bound_fdef f).

Lemma sdom_in_bound': forall f l5, 
  incl (sdom f l5) (cfg.bound_fdef f).
Proof.
  intros.
  case_eq (getEntryBlock f).
  Case "1".
    intros [le ?] Hentry.
    simpl_sdom.
    case_eq (PO_a2p ! l5).
    SCase "1.1".
      intros p Hsome. 
      unfold pdom_analyze.
      case_eq (DomDS.fixpoint (asuccs_psuccs PO_a2p (cfg.successors f))
            LDoms.transfer ((pe, LDoms.top) :: nil) (num_iters f)).
      SSCase "1.1.1".
        intros t Heq.
        case_eq (t ??p); simpl.
        SSSCase "1.1.1.1".
          intros ps Hget. 
          intros a Hin.
          apply in_parents__in_bound_fdef.
          apply in_ps2as__in_ps in Hin.
          destruct Hin as [p' [Hget' Hin]].
          eapply DomsInParents.dom_fix_in_bound in Heq; eauto.
          eapply in_pparents__in_aparents; eauto.
        SSSCase "1.1.1.2".
          intros Hget. auto with datatypes v62.
      SSCase "1.1.2".
        intros Heq.
        unfold bound_dom.
        rewrite PMap.gi. unfold ps2as. simpl.
        intros x Hinx. tauto.
    SCase "1.2".
      intros Hnone. auto with datatypes v62.
  Case "2".
    intros Hnone.
    simpl_sdom.

    rewrite ATree.gempty. auto with datatypes v62.
Qed.

Lemma sdom_in_bound: forall fh bs l5, 
  incl (sdom (fdef_intro fh bs) l5) (cfg.bound_blocks bs).
Proof.
  intros. apply sdom_in_bound'.
Qed.

Lemma dom_successors : forall
  (l3 : l) (l' : l) f
  (contents3 contents': ListSet.set atom)
  (Hinscs : In l' (cfg.successors f) !!! l3)
  (Heqdefs3 : contents3 = sdom f l3)
  (Heqdefs' : contents' = sdom f l'),
  incl contents' (l3 :: contents3).
Proof.
  intros. 
  assert (Hinbd': incl contents' (cfg.bound_fdef f)).
    subst. apply sdom_in_bound'.
  unfold sdom in *.
  case_eq (dom_analyze f).
  intros res a2p Hdoma.
  rewrite Hdoma in *.
  unfold dom_analyze, bound_dom in *.
  remember (getEntryLabel f) as R.
  destruct f as [fh bs].
  destruct R as [le|].
  Case "entry is good".
    case_eq (dfs (cfg.successors (fdef_intro fh bs)) le 1).
    intros cnt a2p' Hdfs.
    rewrite Hdfs in *.
    assert (Hdfs_entry:=Hdfs).
    apply ReachableEntry.dfs_wf in Hdfs_entry.
    simpl in Hdfs_entry.
    case_eq (a2p' ! le); try solve [intros; congruence].
    intros pe Hpentry.
    rewrite Hpentry in *. 
    inversion Hdoma; subst a2p'.
    case_eq (a2p!l3).
    SCase "l3 is reachable".
      intros p3 Hget3.
      rewrite Hget3 in *.
      assert (ACfg.reachable (cfg.successors (fdef_intro fh bs)) le l3) 
        as Hreach3.
        apply dfs_reachable_iff_get_some with (l0:=l3) in Hdfs; 
          auto using le_in_cfg.
        apply Hdfs. eauto.
      assert (ACfg.reachable (cfg.successors (fdef_intro fh bs)) le l') 
        as Hreach'.
        eapply ACfg.reachable_succ; eauto.
      assert (exists p', a2p!l' = Some p') as Hget'.
        apply dfs_reachable_iff_get_some with (l0:=l') in Hdfs; 
          auto using le_in_cfg.
        apply Hdfs; auto.
      destruct Hget' as [p' Hget'].
      rewrite Hget' in *.
      unfold bound_dom in *.
      assert (Hwf_porder:=Hdfs).
      eapply dfs_wf_porder in Hwf_porder; eauto.
      assert (exists dts3, res ?? p3 = Some dts3) as Hget3a.
        eapply reachable_isnt_bot in Hreach3; eauto.
      assert (exists dts', res ?? p' = Some dts') as Hget'a.
        eapply reachable_isnt_bot in Hreach'; eauto.
      destruct Hget3a as [dts3 Hget3a].
      destruct Hget'a as [dts' Hget'a].
      rewrite Hget3a in *.
      rewrite Hget'a in *.
      assert (In p' 
               (asuccs_psuccs a2p (cfg.successors (fdef_intro fh bs))) ??? p3)
             as Hinscs'.
        eapply in_asuccs__in_psuccs; eauto using Injective.dfs_inj.
      subst. simpl.
      intros a1 Hin. 
      apply in_ps2as__in_ps in Hin.
      destruct Hin as [p1 [Hget1 Hin]].
      apply DomSound.sadom_adom_successors with (n1:=p1)(entrypoint:=pe) 
        (ni:=num_iters (fdef_intro fh bs)) in Hinscs'; auto.
      SSCase "1".
        unfold adomination in Hinscs'. simpl in Hinscs'.
        rewrite Hget3a in Hinscs'.
        simpl in Hinscs'.
        destruct Hinscs' as [EQ | Hin']; subst.
        SSSCase "1.1".
          assert (a1 = l3) as EQ.
            eapply Injective.dfs_inj; eauto.
          subst. simpl. auto.
        SSSCase "1.2".
          simpl. right. eapply in_ps__in_ps2as; eauto using Injective.dfs_inj.
      SSCase "2".
        left. eapply PDomProps.pdom_in_bound; eauto.
      SSCase "3".
        unfold strict_adomination. simpl.
        rewrite Hget'a. simpl. auto.

    SCase "l3 isnt reachable".
      intros Hget3.
      rewrite Hget3 in *.
      subst contents3. auto with datatypes v62.
  Case "entry is wrong".
    inversion Hdoma; subst a2p.
    rewrite ATree.gempty in *.
    subst contents3. auto with datatypes v62.
Qed.

Section sdom_is_complete.

Variable f:fdef.
Hypothesis branches_in_bound_fdef: branchs_in_fdef f.

Lemma sdom_is_complete: forall
  (l3 : l) (l' : l) s3 s'
  (HuniqF : uniqFdef f)
  (HBinF' : blockInFdefB (l', s') f = true)
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hsdom: strict_domination f l' l3),
  In l' (sdom f l3).
Proof.
  intros. 
  simpl_sdom.  
  destruct (reach.reachable_dec f l3) as [Hreach | Hunreach].
  Case "reach".
    eapply p2a_strict_domination in Hsdom; eauto.
    destruct Hsdom as [p1 [p2 [pe' [Hsdom [J1 [J2 J3]]]]]].
    simpl in J3. rewrite J3 in Hl2p. inversion Hl2p; subst pe'.
    apply PDomProps.sadom_is_complete with (ni:=(num_iters f)) in Hsdom; 
      eauto using entry_in_a2p_cfg, num_iters__is__large_enough.
    SCase "1".
      unfold strict_adomination in Hsdom.
      simpl in J1, J2, Hsdom.
      rewrite J2. 
      assert (exists dts2, 
               (pdom_analyze (asuccs_psuccs PO_a2p (asuccs f)) pe (num_iters f)) 
                 ?? p2= Some dts2) as Hdts2_some.
        eapply reachable_isnt_bot' in Hdfs; eauto.
      destruct Hdts2_some as [dts2 Hdts2_some]. unfold asuccs in *.
      rewrite Hdts2_some in *. simpl in Hsdom.
      eapply in_ps__in_ps2as; eauto using Injective.dfs_inj.
    SCase "2".
      eapply dfs_wf_porder in Hdfs; eauto.
    SCase "3". 
      apply blockInFdefB_in_vertexes in HBinF'.
      eapply get_a2p__in_pcfg; eauto.

  Case "unreach".
    eapply unreachable__get_a2p in Hunreach; eauto.
    simpl in Hunreach. rewrite Hunreach. 
    apply cfg.blockInFdefB_in_bound_fdef in HBinF'; auto.
Qed.

End sdom_is_complete.

Section dom_unreachable.

Variable f:fdef.
Hypothesis branches_in_bound_fdef: branchs_in_fdef f.

Lemma dom_unreachable: forall
  (Hhasentry: getEntryBlock f <> None)
  (l3 : l) s3
  (HuniqF: uniqFdef f)
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hunreach: ~ cfg.reachable f l3),
  sdom f l3 = cfg.bound_fdef f.
Proof.
  intros.
  simpl_sdom.
  case_eq (PO_a2p ! l3); auto.
  intros p3 Hget3.
  assert (Heq:=Hdfs).
  eapply entry_in_a2p_cfg with (p:=pe) in Heq; eauto.
  apply PDomProps.dom_unreachable with (n3:=p3)(ni:=num_iters f) in Heq; 
    eauto using num_iters__is__large_enough.
  Case "1".
    case_eq ((pdom_analyze (asuccs_psuccs PO_a2p (cfg.successors f)) pe
               (num_iters f)) ?? p3);
      try solve [intros l0 Hsome; simpl in Heq; unfold asuccs in Heq;
                 rewrite Hsome in Heq; inv Heq | auto].
  Case "2".
    eapply dfs_wf_porder in Hdfs; eauto.
  Case "3".
    intro J. apply Hunreach. eapply p2a_reachable; eauto.
Qed.

End dom_unreachable.

(* Transformation that preserve CFGs preserves analysis results. *)
Section pres_dom.

Variable ftrans: fdef -> fdef.
Variable btrans: block -> block.

Hypothesis ftrans_spec: forall fh bs, 
  ftrans (fdef_intro fh bs) = fdef_intro fh (List.map btrans bs).

Hypothesis btrans_eq_label: forall b, getBlockLabel b = getBlockLabel (btrans b).

Lemma pres_getEntryLabel : forall f,
  getEntryLabel f = getEntryLabel (ftrans f).
Proof.
  intros. destruct f as [fh bs]. rewrite ftrans_spec.
  destruct bs as [|b bs]; auto.
  assert (J:=btrans_eq_label b).
  unfold getBlockLabel in J. 
  remember (btrans b) as R.
  destruct b as [? []]; simpl.
  rewrite <- HeqR. destruct R as [? []]; simpl in J; congruence.
Qed.

Lemma pres_bound_blocks : forall bs,
  cfg.bound_blocks bs = cfg.bound_blocks (List.map btrans bs).
Proof.
  induction bs as [|a bs]; simpl; auto.
    assert (J:=btrans_eq_label a);
    remember (btrans a) as R.
    destruct R as [l1 ? ? ?]; destruct a; simpl in *; subst l1.
    congruence.
Qed.

Hypothesis btrans_eq_tmn: forall b, 
  terminator_match (getTerminator b) (getTerminator (btrans b)).

Lemma pres_successors_blocks : forall bs,
  cfg.successors_blocks bs = cfg.successors_blocks (List.map btrans bs).
Proof.
  induction bs as [|b bs]; simpl; auto.
    assert (J:=btrans_eq_tmn b).
    assert (J':=btrans_eq_label b).
    remember (btrans b) as R.
    destruct R as [l1 []]; destruct b as [? []]; simpl in *; subst l1.
    rewrite IHbs. 
    terminator_match_tac.
Qed.

Lemma pres_num_iters: forall f, num_iters f = num_iters (ftrans f).
Proof.
  destruct f as [fh bs]. 
  rewrite ftrans_spec. unfold num_iters. simpl.
  f_equal.
  generalize 3%positive.
  induction bs; simpl; intros; auto.
Qed.

Lemma pres_sdom: forall (f : fdef) (l5 l0 : l),
  ListSet.set_In l5 (sdom f l0) <->
  ListSet.set_In l5 (sdom (ftrans f) l0).
Proof.
  intros.
  unfold sdom, dom_analyze. destruct f as [fh bs]. 
  case_eq (getEntryLabel (fdef_intro fh bs)).
    intros b Hentry.
    rewrite pres_getEntryLabel in Hentry.
    rewrite <- pres_num_iters.
    rewrite Hentry. rewrite ftrans_spec. simpl.
    rewrite <- pres_successors_blocks. 
    rewrite <- pres_bound_blocks.
    split; eauto.

    intros Hentry.
    rewrite pres_getEntryLabel in Hentry.
    rewrite Hentry. rewrite ftrans_spec. simpl.
    rewrite <- pres_bound_blocks. split; auto.
Qed.

End pres_dom.

Definition create_dom_tree (f: fdef) : option DTree :=
  let '(dts, a2p) := dom_analyze f in
  match LLVMinfra.getEntryLabel f with
  | Some le =>
      match ATree.get le a2p with
      | Some pe => 
          let res := fun p:positive => PMap.get p dts in
          let p2a := a2p_p2a a2p in
          let pdt := create_dtree pe (get_reachable_nodes (bound_fdef f) a2p) res in
          DTreeConv.sdtree_tdtree p2a pdt
      | None => None
      end
  | None => None
  end.

Section create_dom_tree_correct.

Variable f:fdef.
Variable dt: @DTree l.
Hypothesis Hcreate: create_dom_tree f = Some dt.
Variable le:l.
Hypothesis Hentry: getEntryLabel f = Some le.
Hypothesis Hnopreds: (XATree.make_predecessors (successors f)) !!! le = nil.
Hypothesis Hwfcfg: branchs_in_fdef f.
Hypothesis Huniq: uniqFdef f.

Lemma dtree_edge_iff_idom: forall p0 ch0,
  is_dtree_edge eq_atom_dec dt p0 ch0 = true <-> 
    (imm_domination f p0 ch0 /\ reachable f ch0).
Proof.
  unfold reachable, create_dom_tree, imm_domination, 
         strict_domination, domination, dom_analyze in *.
  intros. rewrite Hentry in *.
  assert (J:=Hentry).
  apply getEntryLabel__getEntryBlock in J.
  destruct J as [[le' ?] [Hentry' EQ]]; simpl in EQ; subst le'.
  rewrite Hentry' in *.
  case_eq (dfs (successors f) le 1).
  intros cnt a2p Hdfs. rewrite Hdfs in *.
  assert (Hpentry:=Hdfs).
  apply ReachableEntry.dfs_wf in Hpentry. simpl in Hpentry.
  remember (a2p ! le) as R.
  destruct R; try tauto.
  rewrite <- HeqR in *. 
  assert (Hwfrd:  
    forall a : ATree.elt,
    ACfg.reachable (asuccs f) le a <->
    (exists p1 : positive,
      (PO_a2p {| PO_cnt := cnt; PO_a2p := a2p |}) ! a = Some p1)).
    intros.
    eapply dfs_reachable_iff_get_some in Hdfs; 
      eauto using le_in_cfg.
  assert (Hinj1:
     forall (a1 a2 : atom) (p1 : positive),
       (PO_a2p {| PO_cnt := cnt; PO_a2p := a2p |}) ! a1 = Some p1 ->
       (PO_a2p {| PO_cnt := cnt; PO_a2p := a2p |}) ! a2 = Some p1 -> a1 = a2).
    eauto using Injective.dfs_inj.
  eapply DTreeConv.dtree_edge_iff_idom with (s2t:=(a2p_p2a a2p))
    (sentry:=p)(Sdec:=positive_eq_dec)
    (ssuccs:=asuccs_psuccs a2p (successors f)); eauto. 
  Case "inj". apply a2p_p2a_inj; auto.
  Case "rd s2t". 
    intros. 
    eapply preachable__areachable; eauto using a2p_p2a_spec2.
  Case "imm s2t".
    intros.
    eapply pidom_aidom; eauto using a2p_p2a_spec2.
  Case "rd t2s". 
    intros.
    eapply areachable__ex_preachable in Hrd; eauto.    
    destruct Hrd as [p3 [J1 J2]].
    exists p3.
    apply a2p_p2a_spec1 in J1; eauto. 
  Case "imm t2s". 
    intros.
    eapply aidom_pidom in Hidom; eauto. 
    simpl in Hidom.
    destruct Hidom as [p1 [p2 [Hget1 [Hget2 Hidom]]]].
    exists p1. exists p2. 
    split; eauto using a2p_p2a_spec1.
  Case "wf".
    subst.
    eapply dom_list_tree.dtree_edge_iff_idom with 
      (rd:=get_reachable_nodes (bound_fdef f) a2p); eauto.
    eauto.
    SCase "rd". 
      intros.
      eapply preachable__in_get_reachable_nodes in Hdfs; eauto.
    SCase "entry in cfg". 
      eapply entry_in_a2p_cfg in Hdfs; eauto.
    SCase "rpo". 
      eapply dfs_wf_porder in Hdfs; eauto.
    SCase "large".
      eapply num_iters__is__large_enough in Hdfs; eauto.
    SCase "no pred". 
      eapply asuccs_psuccs__no_preds in Hdfs; eauto.
Qed.

Lemma create_dom_tree__wf_dtree: 
  ADProps.wf_dtree (successors f) le eq_atom_dec dt.
Proof.
  unfold create_dom_tree, dom_analyze in *.
  rewrite Hentry in *.
  case_eq (dfs (successors f) le 1).
  intros cnt a2p Hdfs. rewrite Hdfs in *.
  assert (Hpentry:=Hdfs).
  apply ReachableEntry.dfs_wf in Hpentry. simpl in Hpentry.
  remember (a2p ! le) as R.
  destruct R; try tauto.
  inv_mbind.
  rewrite <- HeqR in *. 
  inversion HeqR; subst p0; clear HeqR.
  apply DTreeConv.wf_sdtree__wf_tdtree with (tentry:=le)(Tdec:=eq_atom_dec)
    (tsuccs:=successors f) (s2t:=(a2p_p2a a2p))
    (sentry:=p)(Sdec:=positive_eq_dec)
    (ssuccs:=asuccs_psuccs a2p (successors f)) in H0; eauto. 
  Case "inj". apply a2p_p2a_inj; auto.
  Case "rd s2t". 
    intros. 
    eapply preachable__areachable; eauto using a2p_p2a_spec2.
  Case "imm s2t".
    intros.
    eapply pidom_aidom; eauto using a2p_p2a_spec2.
      intros.
      eapply dfs_reachable_iff_get_some in Hdfs; 
        eauto using le_in_cfg. 
  Case "wf".
    eapply create_dtree__wf_dtree with 
      (rd:=get_reachable_nodes (bound_fdef f) a2p); eauto.
      eauto.
    SCase "rd". 
      intros.
      eapply preachable__in_get_reachable_nodes in Hdfs; eauto.
    SCase "entry in cfg". 
      eapply entry_in_a2p_cfg in Hdfs; eauto.
    SCase "rpo". 
      eapply dfs_wf_porder in Hdfs; eauto.
    SCase "large".
      eapply num_iters__is__large_enough in Hdfs; eauto.
    SCase "no pred". 
      eapply asuccs_psuccs__no_preds in Hdfs; eauto.
Qed.

End create_dom_tree_correct.

End AlgDom.

Module AlgDomProps := AlgDom_Properties (AlgDom).

