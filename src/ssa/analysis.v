Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import List.
Require Import Arith.
Require Import monad.
Require Import Metatheory.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import ListSet.

Module AtomSet.

  Definition set_eq A (l1 l2:list A) := incl l1 l2 /\ incl l2 l1.

  Definition incl_dec_prop (n:nat) :=
    forall (l1 l2:list atom), length l1 = n -> {incl l1 l2} + {~ incl l1 l2}.

  Lemma remove_length : forall A (dec:forall x y : A, {x = y} + {x <> y}) 
      (l1:list A) (a:A),
    (length (List.remove dec a l1) <= length l1)%nat.
  Proof.
    induction l1; intros; simpl; auto.
      assert (J:=@IHl1 a0).
      destruct (dec a0 a); subst; simpl; auto. 
        omega.
  Qed.      

  Lemma remove_In_neq1 : forall A (dec:forall x y : A, {x = y} + {x <> y}) 
      (l1:list A) (a x:A),
    a <> x -> In x l1 -> In x (List.remove dec a l1).
  Proof.
    induction l1; intros; simpl in *; auto.
      destruct H0 as [H0 | H0]; subst.
        destruct (dec a0 x); subst. 
          contradict H; auto.
          simpl; auto.

        destruct (dec a0 a); subst; simpl; auto.
  Qed.          

  Lemma remove_In_neq2 : forall A (dec:forall x y : A, {x = y} + {x <> y}) 
      (l1:list A) (a x:A),
    a <> x -> In x (List.remove dec a l1) -> In x l1.
  Proof.
    induction l1; intros; simpl in *; auto.
      destruct (dec a0 a); subst; eauto.
        simpl in H0.
        destruct H0 as [H0 | H0]; subst; eauto.
  Qed.          

  Lemma incl_dec_aux : forall n, incl_dec_prop n. 
  Proof.
    intro n.  
    apply lt_wf_rec. clear n.
    intros n H.
    unfold incl_dec_prop in *.
    destruct l1; intros l2 Hlength.
      left. intros x J. inversion J.

      simpl in *.
      assert (((length (List.remove eq_atom_dec a l1)) < n)%nat) as LT.
        assert (J:=@remove_length atom eq_atom_dec l1 a).
        omega.  
      destruct (@H (length (List.remove eq_atom_dec a l1)) LT
                  (List.remove eq_atom_dec a l1) l2) as [J1 | J1]; auto.
        destruct(@in_dec _ eq_atom_dec a l2) as [J2 | J2].
          left. intros x J. simpl in J. 
          destruct J as [J | J]; subst; auto.
          destruct (eq_atom_dec x a); subst; auto.            
          apply J1.
          apply remove_In_neq1; auto.
          
          right. intros G. apply J2. apply G; simpl; auto.

        destruct(@in_dec _ eq_atom_dec a l2) as [J2 | J2].
          right. intros G. apply J1. intros x J3. apply G. simpl.
          destruct (eq_atom_dec x a); subst; auto.            
            right. eapply remove_In_neq2; eauto.

          right. intro J. apply J2. apply J. simpl; auto.
  Qed.

  Lemma incl_dec : forall (l1 l2:list atom), {incl l1 l2} + {~ incl l1 l2}.
  Proof.
    intros l1.
    assert (J:=@incl_dec_aux (length l1)).
    unfold incl_dec_prop in J. eauto.
  Qed.              

  Lemma set_eq_dec : forall (l1 l2:set atom), 
    {set_eq _ l1 l2} + {~ set_eq _ l1 l2}.
  Proof.
    intros l1 l2.
    destruct (@incl_dec l1 l2) as [J | J].
      destruct (@incl_dec l2 l1) as [J' | J'].
        left. split; auto.
        right. intro G. destruct G as [G1 G2]. auto.
      destruct (@incl_dec l2 l1) as [J' | J'].
        right. intro G. destruct G as [G1 G2]. auto.
        right. intro G. destruct G as [G1 G2]. auto.
  Qed.

  Lemma set_eq_app : forall x1 x2 y1 y2,
    set_eq atom x1 y1 -> set_eq atom x2 y2 -> set_eq atom (x1++x2) (y1++y2).
  Proof.  
    intros x1 x2 y1 y2 [Hinc11 Hinc12] [Hinc21 Hinc22].
    split.
      apply incl_app.
        apply incl_appl; auto.
        apply incl_appr; auto.
      apply incl_app.
        apply incl_appl; auto.
        apply incl_appr; auto.
  Qed.

  Lemma set_eq_swap : forall x1 x2,
    set_eq atom (x1++x2) (x2++x1).
  Proof.
    intros x1 x2.
    split.
      apply incl_app.
        apply incl_appr; auto using incl_refl.
        apply incl_appl; auto using incl_refl.
      apply incl_app.
        apply incl_appr; auto using incl_refl.
        apply incl_appl; auto using incl_refl.
  Qed.

  Lemma set_eq__rewrite_env : forall x1 x2 x3 y1 y2 y3,
    set_eq atom ((x1 ++ x2) ++ x3) ((y1 ++ y2) ++ y3) ->
    set_eq atom (x1 ++ x2 ++ x3) (y1 ++ y2 ++ y3).
  Proof.
    intros.
    simpl_env in H. auto.
  Qed.

  Lemma set_eq_refl : forall x, set_eq atom x x.  
    split; apply incl_refl.
  Qed.

  Lemma set_eq_sym: forall x y, set_eq atom x y -> set_eq atom y x.
  Proof.
    intros x y J.
    destruct J as [J1 J2]. split; auto.
  Qed.
  
  Lemma set_eq_trans: forall x y z, 
    set_eq atom x y -> set_eq atom y z -> set_eq atom x z.
  Proof.
    intros x y z J1 J2.
    destruct J1 as [J11 J12].
    destruct J2 as [J21 J22].
    split; eapply incl_tran; eauto.
  Qed.

  Lemma incl_empty_inv : forall x, 
    incl x (empty_set _) -> x = empty_set atom.
  Proof.
    destruct x; intro J; auto.
      assert (J1:=J a).
      contradict J1; simpl; auto.
  Qed.

  Lemma set_eq_empty_inv : forall x, 
    set_eq atom x (empty_set _) -> x = empty_set _.
  Proof.
    destruct x; intro J; auto.
      destruct J as [J1 J2].
      assert (J:=J1 a).
      contradict J; simpl; auto.
  Qed.

  Lemma incl_set_eq_left : forall x1 x2 y,
    set_eq atom x1 x2 -> incl x1 y -> incl x2 y.
  Proof.
    intros x1 x2 y [J1 J2] Hincl.
    eapply incl_tran; eauto.
  Qed.

  Lemma set_eq__incl : forall x1 x2, set_eq atom x1 x2 -> incl x1 x2.
  Proof.
    intros x1 x2 J.
    destruct J; auto.
  Qed.

  Lemma incl_set_eq_both : forall x1 x2 y1 y2,
    set_eq atom x1 x2 -> 
    set_eq atom y1 y2 -> 
    incl x1 y1 -> incl x2 y2.
  Proof.
    intros x1 x2 y1 y2 [J1 J2] [J3 J4] J5.
    apply incl_tran with (m:=y1); auto.
    apply incl_tran with (m:=x1); auto.
  Qed.

  Lemma set_eq_empty_inv2 : forall x, 
    set_eq atom (ListSet.empty_set _) x -> x = ListSet.empty_set _.
  Proof.
    intros.
    apply set_eq_sym in H.
    eapply set_eq_empty_inv; eauto.
  Qed.

  Lemma incl_app_invr : forall A (l1 l2 l:list A),
    incl (l1++l2) l -> incl l2 l.
  Proof.
    intros A l1 l2 l H x J.
    apply H. 
    apply (@incl_appr _ l2 l1 l2); auto using incl_refl.
  Qed.

  Lemma incl_app_invl : forall A (l1 l2 l:list A),
    incl (l1++l2) l -> incl l1 l.
  Proof.
    intros A l1 l2 l H x J.
    apply H. 
    apply (@incl_appl _ l1 l2 l1); auto using incl_refl.
  Qed.
  
  Lemma incl_set_eq_right : forall y1 y2 x,
    set_eq atom y1 y2 -> incl x y1 -> incl x y2.
  Proof.
    intros y1 y2 x [J1 J2] Hincl.
    eapply incl_tran; eauto.
  Qed.

End AtomSet.

(** * Domination analysis *)

(** The type [Dominators] of compile-time approximations of domination. *)

(** We equip this type of approximations with a semi-lattice structure.
  The ordering is inclusion between the sets of values denoted by
  the approximations. *)

Module Dominators.
 
  Export AtomSet.

  Section VarBoundSec.

  Variable bound:set atom.

  Record BoundedSet := mkBoundedSet {
    bs_contents : set atom;
    bs_bound : incl bs_contents bound
  }.

  Definition t := BoundedSet.

  Definition eq (x y: t) :=
    let '(mkBoundedSet cx _) := x in
    let '(mkBoundedSet cy _) := y in
    set_eq _ cx cy.

  Definition eq_refl: forall x, eq x x. 
  Proof.
    unfold eq. intro x. destruct x.
    apply set_eq_refl.
  Qed.

  Definition eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    unfold eq. intros x y J. destruct x. destruct y.
    apply set_eq_sym; auto.
  Qed.
 
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq. intros x y z J1 J2. destruct x. destruct y. destruct z.
    eapply set_eq_trans; eauto.
  Qed.

  Lemma eq_dec: forall (x y: t), {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. destruct x. destruct y.
    apply set_eq_dec.
  Qed.

  Definition beq (x y: t) := if eq_dec x y then true else false.

  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    unfold beq; intros.  destruct (eq_dec x y). auto. congruence.
  Qed.

  Definition sub (x y: t) :=
    let '(mkBoundedSet cx _) := x in
    let '(mkBoundedSet cy _) := y in
    incl cx cy.

  Program Definition top : t := mkBoundedSet (empty_set atom) _.
  Next Obligation.
    intros a H. inversion H.
  Qed.

  Program Definition bot : t := mkBoundedSet bound _.
  Next Obligation.
    apply incl_refl.
  Qed.

  Definition ge (x y: t) : Prop := eq x top \/ eq y bot \/ sub x y.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold ge, eq, sub. destruct x, y. simpl.
    intro J. right. right. destruct J; auto.
  Qed.

  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge, eq, sub. destruct x, y, z. simpl.
    intros J1 J2.
    destruct J1 as [J11 | [J12 | J13]]; try auto.
      destruct J2 as [J21 | [J22 | J23]]; try auto.
        assert (set_eq _ bound (empty_set atom)) as EQ.
          eapply set_eq_trans with (y:=bs_contents1); eauto using set_eq_sym.
        left. 
        apply set_eq_empty_inv in EQ; subst.
        apply incl_empty_inv in bs_bound0; subst.
        apply set_eq_refl.

        right. left. 
        eapply incl_set_eq_left in J23; eauto.
        split; auto.

      destruct J2 as [J21 | [J22 | J23]]; try auto.
        left. 
        apply set_eq_empty_inv in J21; subst.
        apply incl_empty_inv in J13; subst.
        apply set_eq_refl.

        right. right. eapply incl_tran; eauto.
  Qed.

  Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
  Proof.
    unfold ge, eq, sub. destruct x, x', y, y'. simpl in *. 
    intros J1 J2 J3.
    destruct J3 as [J31 | [J32 | J33]].
      left. eapply set_eq_trans with (y:=bs_contents0); eauto using set_eq_sym.
      right. left. 
        eapply set_eq_trans with (y:=bs_contents2); eauto using set_eq_sym.
      right. right. eapply incl_set_eq_both; eauto. 
  Qed.

  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, eq, sub. destruct x. simpl. right. left. apply set_eq_refl.
  Qed.

  Lemma ge_top: forall x, ge top x.
  Proof.
    unfold ge, eq, sub. destruct x. simpl. left. apply set_eq_refl.
  Qed.

  Program Definition lub (x y: t) : t :=
    let '(mkBoundedSet cx _) := x in
    let '(mkBoundedSet cy _) := y in
    mkBoundedSet (set_inter eq_atom_dec cx cy) _.
  Next Obligation.
    intros a J.
    apply set_inter_elim in J.
    destruct J as [J1 J2].
    eauto.
  Qed.

  Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
  Proof.
    unfold lub, eq. destruct x, y. 
    split.
      intros a J.
      apply set_inter_elim in J. destruct J.
      apply set_inter_intro; auto.

      intros a J.
      apply set_inter_elim in J. destruct J.
      apply set_inter_intro; auto.
  Qed.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold lub, ge, sub, eq. destruct x, y. simpl.
    right. right.
    intros a J.
    apply set_inter_elim in J. destruct J. auto.
  Qed.

  Program Definition add (x:t) (a:atom) : t := 
    let '(mkBoundedSet cx _) := x in
    if (In_dec eq_atom_dec a bound) then
      mkBoundedSet (a::cx) _
    else
      x.
  Next Obligation.
    intros a' J.
    simpl in J.
    destruct J; subst; eauto.
  Qed.

  End VarBoundSec. 
End Dominators.

Module Dataflow_Solver_Var_Top (NS: NODE_SET).

Module L := Dominators.

Section Kildall.

Variable bound : set atom.
Definition dt := L.t bound.
Variable successors: ATree.t (list atom).
Variable transf: atom -> dt -> dt.
Variable entrypoints: list (atom * dt).

(** The state of the iteration has two components:
- A mapping from program points to values of type [L.t] representing
  the candidate solution found so far.
- A worklist of program points that remain to be considered.
*)

Record state : Type :=
  mkstate { st_in: AMap.t dt; st_wrk: NS.t }.

(** Kildall's algorithm, in pseudo-code, is as follows:
<<
    while st_wrk is not empty, do
        extract a node n from st_wrk
        compute out = transf n st_in[n]
        for each successor s of n:
            compute in = lub st_in[s] out
            if in <> st_in[s]:
                st_in[s] := in
                st_wrk := st_wrk union {s}
            end if
        end for
    end while
    return st_in
>>

The initial state is built as follows:
- The initial mapping sets all program points to [L.bot], except
  those mentioned in the [entrypoints] list, for which we take
  the associated approximation as initial value.  Since a program
  point can be mentioned several times in [entrypoints], with different
  approximations, we actually take the l.u.b. of these approximations.
- The initial worklist contains all the program points. *)

Fixpoint start_state_in (ep: list (atom * dt)) : AMap.t dt :=
  match ep with
  | nil =>
      AMap.init (L.bot _)
  | (n, v) :: rem =>
      let m := start_state_in rem in AMap.set n (L.lub _ m!!n v) m
  end.

Definition start_state :=
  mkstate (start_state_in entrypoints) (NS.initial successors).

(** [propagate_succ] corresponds, in the pseudocode,
  to the body of the [for] loop iterating over all successors. *)

Definition propagate_succ (s: state) (out: dt) (n: atom) :=
  let oldl := s.(st_in)!!n in
  let newl := L.lub _ oldl out in
  if L.beq _ oldl newl
  then s
  else mkstate (AMap.set n newl s.(st_in)) (NS.add n s.(st_wrk)).

(** [propagate_succ_list] corresponds, in the pseudocode,
  to the [for] loop iterating over all successors. *)

Fixpoint propagate_succ_list (s: state) (out: dt) (succs: set atom)
                             {struct succs} : state :=
  match succs with
  | nil => s
  | n :: rem => propagate_succ_list (propagate_succ s out n) out rem
  end.

(** [step] corresponds to the body of the outer [while] loop in the
  pseudocode. *)

Definition step (s: state) : AMap.t dt + state :=
  match NS.pick s.(st_wrk) with
  | None => 
      inl _ s.(st_in)
  | Some(n, rem) =>
      inr _ (propagate_succ_list
              (mkstate s.(st_in) rem)
              (transf n s.(st_in)!!n)
              (successors!!!n))
  end.

(** The whole fixpoint computation is the iteration of [step] from
  the start state. *)

Definition fixpoint : option (AMap.t dt) :=
  PrimIter.iterate _ _ step start_state.

(** ** Monotonicity properties *)

(** We first show that the [st_in] part of the state evolves monotonically:
  at each step, the values of the [st_in[n]] either remain the same or
  increase with respect to the [L.ge] ordering. *)

Definition in_incr (in1 in2: AMap.t dt) : Prop :=
  forall n, L.ge _ in2!!n in1!!n.

Lemma in_incr_refl:
  forall in1, in_incr in1 in1.
Proof.
  unfold in_incr; intros. apply L.ge_refl. apply L.eq_refl.
Qed.

Lemma in_incr_trans:
  forall in1 in2 in3, in_incr in1 in2 -> in_incr in2 in3 -> in_incr in1 in3.
Proof.
  unfold in_incr; intros. apply L.ge_trans with in2!!n; auto.
Qed.

Lemma propagate_succ_incr:
  forall st out n,
  in_incr st.(st_in) (propagate_succ st out n).(st_in).
Proof.
  unfold in_incr, propagate_succ; simpl; intros.
  case (L.beq _ st.(st_in)!!n (L.lub _ st.(st_in)!!n out)).
  apply L.ge_refl. apply L.eq_refl.
  simpl. case (eq_atom_dec n n0); intro.
  subst n0. rewrite AMap.gss. apply L.ge_lub_left.
  rewrite AMap.gso; auto. apply L.ge_refl. apply L.eq_refl.
Qed.

Lemma propagate_succ_list_incr:
  forall out scs st,
  in_incr st.(st_in) (propagate_succ_list st out scs).(st_in).
Proof.
  induction scs; simpl; intros.
  apply in_incr_refl.
  apply in_incr_trans with (propagate_succ st out a).(st_in). 
  apply propagate_succ_incr. auto.
Qed. 

Lemma fixpoint_incr:
  forall res,
  fixpoint = Some res -> in_incr (start_state_in entrypoints) res.
Proof.
  unfold fixpoint; intros.
  change (start_state_in entrypoints) with start_state.(st_in).
  eapply (PrimIter.iterate_prop _ _ step
    (fun st => in_incr start_state.(st_in) st.(st_in))
    (fun res => in_incr start_state.(st_in) res)).

  intros st INCR. unfold step.
  destruct (NS.pick st.(st_wrk)) as [ [n rem] | ].
  apply in_incr_trans with st.(st_in). auto. 
  change st.(st_in) with (mkstate st.(st_in) rem).(st_in). 
  apply propagate_succ_list_incr. 
  auto. 

  eauto. apply in_incr_refl.
Qed.

(** ** Correctness invariant *)

(** The following invariant is preserved at each iteration of Kildall's
  algorithm: for all program points [n], either
  [n] is in the worklist, or the inequations associated with [n]
  ([st_in[s] >= transf n st_in[n]] for all successors [s] of [n])
  hold.  In other terms, the worklist contains all nodes that do not
  yet satisfy their inequations. *)

Definition good_state (st: state) : Prop :=
  forall n,
  NS.In n st.(st_wrk) \/
  (forall s, In s (successors!!!n) ->
             L.ge _ st.(st_in)!!s (transf n st.(st_in)!!n)).

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma start_state_good:
  good_state start_state.
Proof.
  unfold good_state, start_state; intros.
  case_eq (successors!n); intros.
  left; simpl. eapply NS.initial_spec. eauto.
  unfold successors_list. rewrite H. right; intros. contradiction.
Qed.

Lemma propagate_succ_charact:
  forall st out n,
  let st' := propagate_succ st out n in
  L.ge _ st'.(st_in)!!n out /\
  (forall s, n <> s -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  unfold propagate_succ; intros; simpl.
  predSpec (L.beq bound) (L.beq_correct bound)
           ((st_in st) !! n) (L.lub _ (st_in st) !! n out).
  split.
  eapply L.ge_trans. apply L.ge_refl. apply H; auto.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl. 
  apply L.ge_lub_left. 
  auto.

  simpl. split.
  rewrite AMap.gss.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl. 
  apply L.ge_lub_left. 
  intros. rewrite AMap.gso; auto.
Qed.

Lemma propagate_succ_list_charact:
  forall out scs st,
  let st' := propagate_succ_list st out scs in
  forall s,
  (In s scs -> L.ge _ st'.(st_in)!!s out) /\
  (~(In s scs) -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  induction scs; simpl; intros.
  tauto.
  generalize (IHscs (propagate_succ st out a) s). intros [A B].
  generalize (propagate_succ_charact st out a). intros [C D].
  split; intros.
  elim H; intro.
  subst s.
  apply L.ge_trans with (propagate_succ st out a).(st_in)!!a.
  apply propagate_succ_list_incr. assumption.
  apply A. auto.
  transitivity (propagate_succ st out a).(st_in)!!s.
  apply B. tauto.
  apply D. tauto.
Qed.

Lemma propagate_succ_incr_worklist:
  forall st out n x,
  NS.In x st.(st_wrk) -> NS.In x (propagate_succ st out n).(st_wrk).
Proof.
  intros. unfold propagate_succ. 
  case (L.beq _ (st_in st) !! n (L.lub _ (st_in st) !! n out)).
  auto.
  simpl. rewrite NS.add_spec. auto.
Qed.

Lemma propagate_succ_list_incr_worklist:
  forall out scs st x,
  NS.In x st.(st_wrk) -> NS.In x (propagate_succ_list st out scs).(st_wrk).
Proof.
  induction scs; simpl; intros.
  auto.
  apply IHscs. apply propagate_succ_incr_worklist. auto.
Qed.

Lemma propagate_succ_records_changes:
  forall st out n s,
  let st' := propagate_succ st out n in
  NS.In s st'.(st_wrk) \/ st'.(st_in)!!s = st.(st_in)!!s.
Proof.
  simpl. intros. unfold propagate_succ. 
  case (L.beq _ (st_in st) !! n (L.lub _ (st_in st) !! n out)).
  right; auto.
  case (eq_atom_dec s n); intro.
  subst s. left. simpl. rewrite NS.add_spec. auto.
  right. simpl. apply AMap.gso. auto.
Qed.

Lemma propagate_succ_list_records_changes:
  forall out scs st s,
  let st' := propagate_succ_list st out scs in
  NS.In s st'.(st_wrk) \/ st'.(st_in)!!s = st.(st_in)!!s.
Proof.
  induction scs; simpl; intros.
  right; auto.
  elim (propagate_succ_records_changes st out a s); intro.
  left. apply propagate_succ_list_incr_worklist. auto.
  rewrite <- H. auto.
Qed.

Lemma step_state_good:
  forall st n rem,
  NS.pick st.(st_wrk) = Some(n, rem) ->
  good_state st ->
  good_state (propagate_succ_list (mkstate st.(st_in) rem)
                                  (transf n st.(st_in)!!n)
                                  (successors!!!n)).
Proof.
  unfold good_state. intros st n rem WKL GOOD x.
  generalize (NS.pick_some _ _ _ WKL); intro PICK.
  set (out := transf n st.(st_in)!!n).
  elim (propagate_succ_list_records_changes 
          out (successors!!!n) (mkstate st.(st_in) rem) x).
  intro; left; auto.
  simpl; intros EQ. rewrite EQ.
  (* Case 1: x = n *)
  case (eq_atom_dec x n); intro.
  subst x.
  right; intros.
  elim (propagate_succ_list_charact out (successors!!!n)
          (mkstate st.(st_in) rem) s); intros.
  auto.
  (* Case 2: x <> n *)
  elim (GOOD x); intro.
  (* Case 2.1: x was already in worklist, still is *)
  left. apply propagate_succ_list_incr_worklist.
  simpl. rewrite PICK in H. elim H; intro. congruence. auto.
  (* Case 2.2: x was not in worklist *)
  right; intros.
  case (In_dec eq_atom_dec s (successors!!!n)); intro.
  (* Case 2.2.1: s is a successor of n, it may have increased *)
  apply L.ge_trans with st.(st_in)!!s.
  change st.(st_in)!!s with (mkstate st.(st_in) rem).(st_in)!!s.
  apply propagate_succ_list_incr. 
  auto.
  (* Case 2.2.2: s is not a successor of n, it did not change *)
  elim (propagate_succ_list_charact out (successors!!!n)
          (mkstate st.(st_in) rem) s); intros.
  rewrite H2. simpl. auto. auto.
Qed.

(** ** Correctness of the solution returned by [iterate]. *)

(** As a consequence of the [good_state] invariant, the result of
  [fixpoint], if defined, is a solution of the dataflow inequations,
  since [st_wrk] is empty when the iteration terminates. *)

Theorem fixpoint_solution:
  forall res n s,
  fixpoint = Some res ->
  In s (successors!!!n) ->
  L.ge _ res!!s (transf n res!!n).
Proof.
  assert (forall res, fixpoint = Some res ->
          forall n s,
          In s successors!!!n ->
          L.ge _ res!!s (transf n res!!n)).
  unfold fixpoint. intros res PI. pattern res. 
  eapply (PrimIter.iterate_prop _ _ step good_state).

  intros st GOOD. unfold step. 
  caseEq (NS.pick st.(st_wrk)). 
  intros [n rem] PICK. apply step_state_good; auto. 
  intros. 
  elim (GOOD n); intro. 
  elim (NS.pick_none _ n H). auto.
  auto.

  eauto. apply start_state_good. eauto.
Qed.

(** As a consequence of the monotonicity property, the result of
  [fixpoint], if defined, is pointwise greater than or equal the
  initial mapping.  Therefore, it satisfies the additional constraints
  stated in [entrypoints]. *)

Lemma start_state_in_entry:
  forall ep n v,
  In (n, v) ep ->
  L.ge _ (start_state_in ep)!!n v.
Proof.
  induction ep; simpl; intros.
  elim H.
  elim H; intros.
  subst a. rewrite AMap.gss.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl. 
  apply L.ge_lub_left.
  destruct a. rewrite AMap.gsspec. case (eq_atom_dec n a); intro.
  subst a. apply L.ge_trans with (start_state_in ep)!!n.
  apply L.ge_lub_left. auto.
  auto.
Qed.

Theorem fixpoint_entry:
  forall res n v,
  fixpoint = Some res ->
  In (n, v) entrypoints ->
  L.ge _ res!!n v.
Proof.
  intros.
  apply L.ge_trans with (start_state_in entrypoints)!!n.
  apply fixpoint_incr. auto.
  apply start_state_in_entry. auto.
Qed.

(** ** Preservation of a property over solutions *)

Variable P: dt -> Prop.
Hypothesis P_bot: P (L.bot _).
Hypothesis P_lub: forall x y, P x -> P y -> P (L.lub _ x y).
Hypothesis P_transf: forall pc x, P x -> P (transf pc x).
Hypothesis P_entrypoints: forall n v, In (n, v) entrypoints -> P v.

Theorem fixpoint_invariant:
  forall res pc,
  fixpoint = Some res ->
  P res!!pc.
Proof.
  assert (forall ep,
          (forall n v, In (n, v) ep -> P v) ->
          forall pc, P (start_state_in ep)!!pc).
    induction ep; intros; simpl.
    rewrite AMap.gi. auto.
    simpl in H.
    assert (P (start_state_in ep)!!pc). apply IHep. eauto.  
    destruct a as [n v]. rewrite AMap.gsspec. destruct (eq_atom_dec pc n).
    apply P_lub. subst. auto. eapply H. left; reflexivity. auto.
  set (inv := fun st => forall pc, P (st.(st_in)!!pc)).
  assert (forall st v n, inv st -> P v -> inv (propagate_succ st v n)).
    unfold inv, propagate_succ. intros. 
    destruct (L.beq _ (st_in st)!!n (L.lub _ (st_in st)!!n v)).
    auto. simpl. rewrite AMap.gsspec. destruct (eq_atom_dec pc n). 
    apply P_lub. subst n; auto. auto.
    auto.
  assert (forall l0 st v, inv st -> P v -> inv (propagate_succ_list st v l0)).
    induction l0; intros; simpl. auto.
    apply IHl0; auto.
  assert (forall res, fixpoint = Some res -> forall pc, P res!!pc).
    unfold fixpoint. intros res0 RES0. pattern res0.
    eapply (PrimIter.iterate_prop _ _ step inv).
    intros. unfold step. destruct (NS.pick (st_wrk a)) as [[n rem] | ].
    apply H1. auto. apply P_transf. apply H2.
    assumption.
    eauto. 
    unfold inv, start_state; simpl. auto. 
  intros. auto.
Qed.

End Kildall.

End Dataflow_Solver_Var_Top.

(**********************************)
(* Dom and Reaching analysis *)

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

Definition transfer (bound: set atom) (lbl: l) (before: Dominators.t bound) :=
  Dominators.add _ before lbl.

(** The static analysis itself is then an instantiation of Kildall's
  generic solver for forward dataflow inequations. [analyze f]
  returns a mapping from program points to mappings of pseudo-registers
  to approximations.  It can fail to reach a fixpoint in a reasonable
  number of iterations, in which case [None] is returned. *)

Module DomDS := Dataflow_Solver_Var_Top(AtomNodeSet).

Fixpoint bound_blocks (bs: blocks) : set atom :=
match bs with
| nil => empty_set _
| block_intro l0 _ _ tmn :: bs' => l0::(bound_blocks bs')
end.

Definition bound_fdef (f: fdef) : set atom :=
let '(fdef_intro _ bs) := f in
bound_blocks bs.

Lemma entry_dom : forall (bs:list block), 
  {oresult : option (l * Dominators.BoundedSet (bound_blocks bs)) &
     match oresult with
     | None => bs = nil
     | Some (le, Dominators.mkBoundedSet (l1::nil) _) => le = l1
     | _ => False
     end
  }.
Proof.
  intros.
  destruct bs; simpl in *.
    exists None. auto.

    destruct b.
    assert (incl [l0] (l0 :: bound_blocks bs)) as J.
      simpl_env.
      apply incl_appl; auto using incl_refl.
    exists (Some (l0, Dominators.mkBoundedSet _ [l0] J)).  
    simpl. auto.
Defined.

Definition dom_analyze (f: fdef) : AMap.t (Dominators.t (bound_fdef f)) :=
  let '(fdef_intro _ bs) := f in
  let bound := bound_blocks bs in
  let top := Dominators.top bound in
  match entry_dom bs with
  | (existT (Some (le, start)) _) =>
      match DomDS.fixpoint bound (successors_blocks bs) (transfer bound) 
        ((le, start) :: nil) with
      | None => (AMap.set le start (AMap.init top))
      | Some res => res
      end
  | (existT None _) => AMap.init top
  end.

(*
Program Definition dom_analyze (f: fdef): AMap.t (Dominators.t (bound_fdef f)) :=
  let bound := bound_fdef f in
  let top := Dominators.top bound in
  match getEntryBlock f with
  | Some (block_intro le _ _ _) =>
      match DomDS.fixpoint bound (successors f) (transfer bound) 
        ((le, Dominators.mkBoundedSet _ [le] _) :: nil) with
      | None => AMap.init top
      | Some res => res
      end
  | None => AMap.init top
  end.
Next Obligation.
  destruct f. 
  destruct b; simpl in *; inv Heq_anonymous. 
    simpl_env.
    apply incl_appl; auto using incl_refl.
Qed.
*)

Definition blockDominates (f: fdef) (b1 b2: block) : Prop :=
let '(block_intro l1 _ _ _) := b1 in
let '(block_intro l2 _ _ _) := b2 in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l2 dt in
set_In l1 els.

Definition blockStrictDominates (f: fdef) (b1 b2: block) : Prop :=
let '(block_intro l1 _ _ _) := b1 in
let '(block_intro l2 _ _ _) := b2 in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l2 dt in
l1 <> l2 /\ set_In l1 els.

Definition insnDominates (id1:id) (i2:insn) (b:block) : Prop :=
match b with 
| (block_intro l5 ps cs tmn) =>
  match i2 with
  | insn_terminator tmn2 =>
      ((exists cs1, exists c1, exists cs2, 
         cs = cs1++c1::cs2 /\ getCmdID c1 = Some id1) \/ 
       (exists ps1, exists p1, exists ps2, 
         ps = ps1++p1::ps2 /\ getPhiNodeID p1 = id1)
       ) /\ tmn2 = tmn
  | insn_cmd c2 =>
      (exists ps1, exists p1, exists ps2, 
         ps = ps1++p1::ps2 /\ getPhiNodeID p1 = id1) \/
      (exists cs1, exists c1, exists cs2, exists cs3,
         cs = cs1++c1::cs2 ++ c2 :: cs3 /\ getCmdID c1 = Some id1)
  | _ => False
  end
end.

Module ReachDS := Dataflow_Solver(LBoolean)(AtomNodeSet).

Definition reachable_aux (f: fdef) : option (AMap.t bool) :=
  match getEntryBlock f with
  | Some (block_intro le _ _ _) =>
     ReachDS.fixpoint (successors f) (fun pc r => r) ((le, true) :: nil)
  | None => None
  end.

Definition reachable (f: fdef) : AMap.t bool :=
  match reachable_aux f with  
  | None => AMap.init true
  | Some rs => rs
  end.

Definition isReachableFromEntry (f:fdef) (b1:block) : Prop :=
let '(block_intro l1 _ _ _) := b1 in
AMap.get l1 (reachable f).
 
(********************************************)
(** * Correctness of analysis *)

Axiom atomset_eq__proof_irr2 : forall (* proof irrelevence *)
  max
  (contents' : ListSet.set atom)
  (inbound' : incl contents' max)
  a
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = a),
  contents' = Dominators.bs_contents max a.

Lemma atomset_eq__proof_irr1 : forall
  (bs : blocks)
  (l' : l)
  (t : AMap.t (DomDS.dt (bound_blocks bs)))
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_blocks bs))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = t !! l')
  (bs_contents : ListSet.set atom)
  (bs_bound0 : incl bs_contents (bound_blocks bs))
  (HeqR2 : {|
          DomDS.L.bs_contents := bs_contents;
          DomDS.L.bs_bound := bs_bound0 |} = t !! l'),
  contents' = bs_contents.
Proof. 
  intros.  
  apply atomset_eq__proof_irr2 in Heqdefs'; subst.
  apply atomset_eq__proof_irr2 in HeqR2; subst.
  auto.
Qed.

Lemma reachable_entrypoint:
  forall (f:fdef) l0 ps cs tmn, 
    getEntryBlock f = Some (block_intro l0 ps cs tmn) ->
    (reachable f)!!l0 = true.
Proof.
  intros f l0 ps cs tmn Hentry. unfold reachable.
  caseEq (reachable_aux f).
    unfold reachable_aux; intros reach A.
    rewrite Hentry in A.
    assert (LBoolean.ge reach!!l0 true).
      eapply ReachDS.fixpoint_entry. eexact A. auto with coqlib.
    unfold LBoolean.ge in H. tauto.

    intros. apply AMap.gi.
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
      unfold successors_list.
      rewrite ATree.gss. auto.
  
      apply IHbs in J2; auto.
      unfold successors_list in *.
      destruct HuniqF as [J _].
      inv J.
      rewrite ATree.gso; auto.
        clear - HbInF H1. 
        eapply InBlocksB__NotIn; eauto.
Qed.

Lemma successors_predOfBlock : forall f l1 ps1 cs1 tmn1 l0 ps0 cs0 tmn0,
  uniqFdef f ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  In l0 (successors_terminator tmn1) ->
  In l1 (predOfBlock (block_intro l0 ps0 cs0 tmn0) (genBlockUseDef_fdef f)).
Proof.
  unfold predOfBlock.
  destruct f. destruct f. intros.
  destruct H as [H _].
  generalize dependent l1.
  generalize dependent ps1.
  generalize dependent cs1.
  generalize dependent tmn1.
  generalize dependent l0.
  generalize dependent ps0.
  generalize dependent cs0.
  generalize dependent tmn0.
  induction b; intros; simpl in *.
    inversion H0.

    assert (G:=H). simpl_env in G.
    apply uniqBlocks_inv in G.
    destruct G as [G1 G2].
    destruct a0. simpl.
    apply orb_prop in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0.
      inv H0.
      destruct t0; auto.
        apply IHb with (ps1:=p)(cs1:=c)(tmn1:=insn_return i0 t0 v0); auto.
        apply IHb with (ps1:=p)(cs1:=c)(tmn1:=insn_return_void i0); auto.

        simpl in H1.
        destruct H1 as [H1 | [H1 | H1]]; subst.
          assert (J:=@lookupAL_update_udb_eq (update_udb nil l2 l3) l2 l0).
          destruct J as [ls0 [J1 J2]].
          apply lookupAL_genBlockUseDef_blocks_spec with (bs:=b) in J1; auto.
          destruct J1 as [ls1 [J1 J3]].
          rewrite J1. apply J3; auto.

          assert (J:=@lookupAL_update_udb_eq nil l2 l0).
          destruct J as [ls0 [J J0]].
          apply lookupAL_update_udb_spec with (l1:=l2)(l2:=l1) in J; auto.
          destruct J as [ls1 [J J1]].
          apply lookupAL_genBlockUseDef_blocks_spec with (bs:=b) in J; auto.
          destruct J as [ls2 [J J2]].
          rewrite J. apply J2. apply J1. auto.

          inversion H1.
        simpl in H1.
        destruct H1 as [H1 | H1]; subst.
          assert (J:=@lookupAL_update_udb_eq nil l2 l0).
          destruct J as [ls0 [J J0]].
          apply lookupAL_genBlockUseDef_blocks_spec with (bs:=b) in J; auto.
          destruct J as [ls2 [J J2]].
          rewrite J. apply J2. auto.

          inversion H1.

        apply IHb with (ps1:=p)(cs1:=c)(tmn1:=insn_unreachable i0); auto.

      eapply IHb in H1; eauto.
        remember (lookupAL (list l) (genBlockUseDef_blocks b nil) l0) as R.
        destruct R; try solve [inversion H1].
        destruct H as [J1 J2].
        simpl in J1.
        inv J1.
        apply InBlocksB_In in H0.
        destruct (eq_atom_dec l1 l2); subst.
          contradict H0; auto.

          clear - HeqR H1.
          simpl.
          assert (usedef_block_inc nil 
            (match t0 with
             | insn_return _ _ _ => nil
             | insn_return_void _ => nil
             | insn_br _ _ l4 l5 => update_udb (update_udb nil l2 l5) l2 l4
             | insn_br_uncond _ l4 => update_udb nil l2 l4
             | insn_unreachable _ => nil
             end)) as J.
            intros x A J. inversion J.
          apply genBlockUseDef_blocks_inc with (bs:=b) in J.
          symmetry in HeqR.
          apply J in HeqR.
          destruct HeqR as [l4 [J1 J2]].
          rewrite J1. apply J2 in H1; auto.
Qed.

Lemma reachable_successors:
  forall f l0 cs ps tmn l1,
  uniqFdef f ->
  blockInFdefB (block_intro l0 cs ps tmn) f ->
  In l1 (successors_terminator tmn) ->
  (reachable f)!!l0 = true ->
  (reachable f)!!l1 = true.
Proof.
  intros f l0 cs ps tmn l1 HuniqF HbInF Hin.
  unfold reachable.
  caseEq (reachable_aux f).
    unfold reachable_aux. intro reach; intros.
    remember (getEntryBlock f) as R.
    destruct R; inv H.
    destruct b as [le ? ? ?].
    assert (LBoolean.ge reach!!l1 reach!!l0) as J.
      change (reach!!l0) with ((fun pc r => r) l0 (reach!!l0)).
      eapply ReachDS.fixpoint_solution; eauto.
        destruct f as [[?] bs]. simpl in *.
        clear - HuniqF HbInF Hin. destruct HuniqF.
        assert ((successors_terminator tmn) = (successors_blocks bs) !!! l0) 
          as EQ.
          eapply successors_terminator__successors_blocks; eauto.
        rewrite <- EQ; auto.            
    elim J; intro. congruence. auto.

  intros. apply AMap.gi.
Qed.

Ltac tinv H := try solve [inv H].
Import AtomSet.

Lemma dom_entrypoint : forall f l0 ps cs tmn
  (Hentry : getEntryBlock f = Some (block_intro l0 ps cs tmn)),
  incl (Dominators.bs_contents (bound_fdef f) ((dom_analyze f) !! l0)) [l0].
Proof.
  intros.
  unfold dom_analyze.
  destruct f.
  remember (entry_dom b) as R.
  destruct R as [R Hp].
  destruct R as [[le start] | ].
  Case "entry is good". 
    remember (DomDS.fixpoint (bound_blocks b) (successors_blocks b)
                (transfer (bound_blocks b)) ((le, start) :: nil)) as R1.
    destruct start.
    destruct bs_contents; tinv Hp.
    destruct bs_contents; tinv Hp.
    subst le. 
    destruct b; try solve [inversion HeqR].
    destruct b. simpl in HeqR. inversion HeqR. subst a.
    simpl in Hentry. inversion Hentry. subst l0 p c t.
    clear HeqR Hentry.    
    destruct R1; subst.
    SCase "analysis is done".
      symmetry in HeqR1.
      apply DomDS.fixpoint_entry with (n:=l1)(v:={|
                DomDS.L.bs_contents := l1 :: nil;
                DomDS.L.bs_bound := bs_bound |}) in HeqR1; simpl; eauto.
      unfold DomDS.L.ge in HeqR1.
      unfold DomDS.L.eq, DomDS.L.top, DomDS.L.bot, DomDS.L.sub in HeqR1.
      simpl in *.

      remember (t !! l1) as R.
      destruct R.
      erewrite <- atomset_eq__proof_irr2; eauto.
      destruct HeqR1 as [HeqR1 | [ HeqR1 | HeqR1 ]]; auto.
      SSCase "1".       
        apply set_eq_empty_inv in HeqR1. subst.
        intros x J. inversion J.
      SSCase "2".   
        eapply incl_set_eq_right; eauto using set_eq_sym.
    
    SCase "analysis fails".
      simpl.      
      rewrite AMap.gss. simpl.
      apply incl_refl.

  Case "entry is wrong". 
    subst. inversion Hentry.
Qed.

(***************************)
(* domination prop *)

Fixpoint cmds_dominates_cmd (cs:cmds) (id0:id) : list atom :=
match cs with
| nil => nil
| c1::cs' => 
    let ctx := cmds_dominates_cmd cs' id0 in
    if eq_atom_dec (getCmdLoc c1) id0 then nil
    else
      match getCmdID c1 with
      | Some id1 => id1::ctx
      | None => ctx
      end
end.

Lemma NoDup__In_cmds_dominates_cmd : forall cs1 c cs2 id1,
  NoDup (getCmdsLocs (cs1 ++ c :: cs2)) ->
  In id1 (getCmdsIDs cs1) ->
  In id1 (cmds_dominates_cmd (cs1 ++ c :: cs2) (getCmdLoc c)).
Proof.
  induction cs1; intros; simpl in *.
    inversion H0.

    inv H.
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c)).
      assert (False) as F.
        apply H3. 
        rewrite e.
        rewrite getCmdsLocs_app. simpl.
        apply in_or_app. right. simpl. auto.
      inversion F.

      destruct (getCmdID a); auto.
      simpl in *. destruct H0 as [H0 | H0]; auto.
Qed.   

Definition inscope_of_block (f:fdef) (l1:l) (opt_ctx:option (list atom)) (lbl:l)
  :=
  match opt_ctx with
  | Some ctx =>
     match lookupBlockViaLabelFromFdef f lbl with
     | None => None
     | Some b => 
         if eq_atom_dec lbl l1 then Some ctx
         else Some (getBlockIDs b ++ ctx)
     end
  | None => None
  end.

Definition inscope_of_cmd (f:fdef) (b1:block) (c:cmd) : option (list atom) :=
let id0 := getCmdLoc c in
let '(block_intro l1 ps cs _) := b1 in
let '(fdef_intro (fheader_intro _ _ _ la _) _) := f in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l1 dt in
fold_left (inscope_of_block f l1) els
  (Some (getPhiNodesIDs ps ++ cmds_dominates_cmd cs id0 ++ getArgsIDs la))
.

Definition inscope_of_tmn (f:fdef) (b1:block) (tmn:terminator) 
  : option (list atom) :=
let '(block_intro l1 ps cs _) := b1 in
let '(fdef_intro (fheader_intro _ _ _ la _) _) := f in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l1 dt in
fold_left (inscope_of_block f l1) els
  (Some (getPhiNodesIDs ps ++ getCmdsIDs cs ++ getArgsIDs la))
.

Definition defs_dominate (f:fdef) (curb incomingb:block) (i:insn) 
  : option (list atom) :=
match i with
| insn_phinode p => 
    let '(block_intro _ _ _ tmn) := incomingb in
    inscope_of_tmn f incomingb tmn
| insn_cmd c => inscope_of_cmd f curb c
| insn_terminator tmn => inscope_of_tmn f curb tmn
end.

Lemma getCmdsIDs__cmds_dominates_cmd : forall cs2' c',
  ~ In (getCmdLoc c') (getCmdsLocs cs2') ->
  set_eq _ (getCmdsIDs (cs2' ++ [c']))
  (cmds_dominates_cmd (cs2' ++ [c']) (getCmdLoc c') ++ 
    match getCmdID c' with
    | Some id1 => [id1]
    | None => nil
    end).   
Proof.
  induction cs2'; intros c' Hnotin.
    simpl in *.
    destruct (eq_atom_dec (getCmdLoc c') (getCmdLoc c')) as [_ | n];
      try solve [contradict n; auto].
      remember (getCmdID c') as R.
      destruct R; simpl_env; apply set_eq_refl.

    simpl in *.
    assert (~ In (getCmdLoc c') (getCmdsLocs cs2')) as J.
      auto.
    apply IHcs2' in J.
    remember (getCmdID a) as R1.
    remember (getCmdID c') as R2.
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c')); 
      try solve [contradict e; auto].
    destruct R1; auto.
      simpl_env.
      apply set_eq_app; auto using set_eq_refl.
Qed.      

Definition opt_set_eq (ops1 ops2:option (list atom)) : Prop :=
match (ops1, ops2) with
| (None, None) => True
| (Some s1, Some s2) => set_eq _ s1 s2
| _ => False
end.

Lemma inscope_of_block__opt_set_eq : forall f l1 l' opr1 opr2,
  opt_set_eq opr1 opr2 ->
  opt_set_eq (inscope_of_block f l1 opr1 l') (inscope_of_block f l1 opr2 l').
Proof.
  unfold inscope_of_block.
  intros.
  destruct (lookupBlockViaLabelFromFdef f l').
    destruct (eq_atom_dec l' l1); subst.
      destruct opr1.
        destruct opr2; try solve [inversion H | auto].
        destruct opr2; try solve [inversion H | auto].
      unfold opt_set_eq in *.
      destruct opr1.
        destruct opr2; try solve [inversion H ].
          apply set_eq_app; auto using set_eq_refl.
        destruct opr2; try solve [inversion H | auto ].
    unfold opt_set_eq in *.
    destruct opr1.
      destruct opr2; try solve [inversion H | auto].
      destruct opr2; try solve [inversion H | auto].
Qed.
 
Lemma fold_left__opt_set_eq_aux : forall ls0 opr1 opr2 f l1,
  opt_set_eq opr1 opr2 ->
  opt_set_eq (fold_left (inscope_of_block f l1) ls0 opr1) 
           (fold_left (inscope_of_block f l1) ls0 opr2).
Proof.
  induction ls0; intros opr1 opr2 f l1 Heq; simpl in *; auto.
    apply IHls0.
      apply inscope_of_block__opt_set_eq; auto.
Qed.

Lemma fold_left__opt_set_eq : forall (ls0:list atom) f l1 init1 init2 r1,
  set_eq _ init1 init2 ->  
  fold_left (inscope_of_block f l1) ls0 (Some init1) = Some r1 ->
  exists r2, fold_left (inscope_of_block f l1) ls0 (Some init2) = Some r2 /\ 
    set_eq _ r1 r2.
Proof.
  intros.
  assert (opt_set_eq (Some init1) (Some init2)) as EQ. unfold opt_set_eq. auto.
  apply fold_left__opt_set_eq_aux with (ls0:=ls0)(f:=f)(l1:=l1) in EQ.
  remember (fold_left (inscope_of_block f l1) ls0 (ret init2)) as R. 
  unfold opt_set_eq in EQ.    
  rewrite H0 in EQ.
  destruct R; try solve [inversion EQ].
  exists l0. auto.
Qed.
 
Lemma inscope_of_block__opt_union : forall f l1 l' init1 init2 r1,
  inscope_of_block f l1 (Some init1) l' = Some r1 ->
  exists r2, inscope_of_block f l1 (Some (init1++init2)) l' = Some r2 /\
    set_eq _ (r1++init2) r2.
Proof.
  intros.
  unfold inscope_of_block in *.
  destruct (lookupBlockViaLabelFromFdef f l').
    destruct (eq_atom_dec l' l1); subst; inv H.
      exists (r1++init2). auto using set_eq_refl.
      exists (getBlockIDs b ++ init1 ++ init2). 
        simpl_env. auto using set_eq_refl.
    inversion H.
Qed.

Lemma fold_left__none : forall (ls0:list atom) f l1,
  fold_left (inscope_of_block f l1) ls0 None = None.
Proof.
  induction ls0; intros f l1; simpl in *; auto.
Qed.

Lemma fold_left__opt_union : forall (ls0:list atom) f l1 init1 init2 r1,
  fold_left (inscope_of_block f l1) ls0 (Some init1) = Some r1 ->
  exists r2, 
    fold_left (inscope_of_block f l1) ls0 (Some (init1++init2)) = Some r2 
      /\ set_eq _ (r1++init2) r2.
Proof.
  induction ls0; intros f l1 init1 init2 r1 H; simpl in *; auto.
    inv H. exists (r1 ++ init2). split; auto using set_eq_refl.

    destruct (lookupBlockViaLabelFromFdef f a).
      destruct (eq_atom_dec a l1); subst; auto.
        apply IHls0 with (init2:=init2) in H; auto.
          simpl_env in H. auto.
      rewrite fold_left__none in H. inversion H.
Qed.

Lemma inscope_of_cmd_tmn : forall f l2 ps2 cs2' c' tmn' ids1,
~ In (getCmdLoc c') (getCmdsLocs cs2') ->
Some ids1 = inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']) tmn') c' ->
exists ids2, 
  Some ids2 = inscope_of_tmn f (block_intro l2 ps2 (cs2'++[c']) tmn') tmn' /\
  match getCmdID c' with
  | Some id1 => set_eq _ (id1::ids1) ids2
  | None => set_eq _ ids1 ids2
  end.
Proof.
  intros f l2 ps2 cs2' c' tmn' ids1 Hnotin Hinscope.
  unfold inscope_of_cmd in Hinscope.
  unfold inscope_of_tmn.
  destruct f as [[? ? ? la va] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro f t i0 la va) bs)) !! l2) as R.
  destruct R as [R_contents R_bound]. simpl in *.
  apply getCmdsIDs__cmds_dominates_cmd in Hnotin.
  symmetry in Hinscope.
  remember (getCmdID c') as R.
  destruct R.
    apply fold_left__opt_union with (init2:=[i1]) in Hinscope.
    destruct Hinscope as [r2 [Hinscope Heq]].
    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++
      ((getCmdsIDs (cs2' ++ [c'])) ++ (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
        simpl_env. 
        eapply set_eq_trans with (y:=r2); eauto.
        eapply set_eq_trans with (y:=ids1 ++ [i1]); eauto.
          apply set_eq_swap.          
      simpl_env.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_trans with (y:=(cmds_dominates_cmd (cs2' ++ [c']) 
         (getCmdLoc c') ++ [i1]) ++ getArgsIDs la).
        simpl_env.
        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_swap.          

        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_sym; auto.          

    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++ 
      ((getCmdsIDs (cs2' ++ [c'])) ++ (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_app; auto using set_eq_refl.
      simpl_env in Hnotin.
      apply set_eq_sym; auto.          
Qed.

Lemma cmds_dominates_cmd__cmds_dominates_cmd : forall cs2' c' c cs',
  NoDup (getCmdsLocs (cs2'++[c']++[c]++cs')) ->
  set_eq _ (cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c))
    (cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c') ++
     match getCmdID c' with
     | Some id1 => [id1]
     | None => nil
     end).   
Proof.
  induction cs2'; intros c' c cs' Hnodup.
    simpl in *.
    inv Hnodup. simpl in H1.
    remember (getCmdID c') as R.
    destruct (eq_atom_dec (getCmdLoc c') (getCmdLoc c)).
      contradict e; auto.

      destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_|n1];
        try solve [contradict n1; auto].
      destruct (eq_atom_dec (getCmdLoc c') (getCmdLoc c')) as [_|n2];
        try solve [contradict n2; auto].
      destruct R; auto using set_eq_refl.

    simpl in *.
    inv Hnodup.
    rewrite getCmdsLocs_app in H1.
    apply NotIn_inv in H1.    
    destruct H1 as [H11 H12].
    simpl in H12.
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c)) as [e1 | ];
      try solve [contradict e1; auto].
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c')) as [e1 | ];
      try solve [contradict e1; auto].
    destruct (getCmdID a); auto.
      apply IHcs2' in H2. clear IHcs2'.
      simpl_env.
       apply set_eq_app; auto using set_eq_refl.
Qed.      

Lemma inscope_of_cmd_cmd : forall f l2 ps2 cs2' c' c cs' tmn' ids1,
NoDup (getCmdsLocs (cs2'++[c']++[c]++cs')) ->
Some ids1 = inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn') c' 
  ->
exists ids2, 
  Some ids2 = 
    inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn') c /\
  match getCmdID c' with
  | Some id1 => set_eq _ (id1::ids1) ids2
  | None => set_eq _ ids1 ids2
  end.
Proof.
  intros f l2 ps2 cs2' c' c cs' tmn' ids1 Hnodup Hinscope.
  unfold inscope_of_cmd in Hinscope.
  unfold inscope_of_cmd.
  destruct f as [[? ? ? la va] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro f t i0 la va) bs)) !! l2) as R.
  destruct R as [R_contents R_bound].
  apply cmds_dominates_cmd__cmds_dominates_cmd in Hnodup. simpl in *.
  symmetry in Hinscope.
  remember (getCmdID c') as R.
  destruct R.
    apply fold_left__opt_union with (init2:=[i1]) in Hinscope.
    destruct Hinscope as [r2 [Hinscope Heq]].
    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++ 
      ((cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c)) ++
      (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
        simpl_env. 
        eapply set_eq_trans with (y:=r2); eauto.
        eapply set_eq_trans with (y:=ids1 ++ [i1]); eauto.
          apply set_eq_swap.          
      simpl_env.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_trans with (y:=(cmds_dominates_cmd (cs2' ++ [c']++[c]++cs') 
         (getCmdLoc c') ++ [i1]) ++ getArgsIDs la).
        simpl_env.
        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_swap.          

        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_sym; auto.          

    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++
      ((cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c)) ++
      (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_app; auto using set_eq_refl.
      simpl_env in Hnodup.
      apply set_eq_sym; auto.          
Qed.

Lemma inc__getLabel2Block_blocks : forall a bs 
  (Hinc : incl [a] (bound_blocks bs)),
  exists b : block, lookupAL block (genLabel2Block_blocks bs) a = Some b.
Proof. 
  intros.
  induction bs; simpl in *; auto.
    assert (J:=@Hinc a). simpl in J. destruct J; auto.
    destruct a0; simpl in *.
    destruct (a==l0); subst.
      exists (block_intro l0 p c t). auto.

      apply IHbs. intros x J.
      assert (x=a) as EQ.
        simpl in J. destruct J; auto. inversion H.
      subst.      
      apply Hinc in J. simpl in J.
      destruct J as [J | J]; subst; auto.
      contradict n; auto.
Qed.

Lemma fold_left__bound_blocks : forall ls0 fa t i0 la va bs l0 init,
  incl ls0 (bound_blocks bs) ->
  exists r, 
    fold_left (inscope_of_block 
      (fdef_intro (fheader_intro fa t i0 la va) bs) l0) ls0 (Some init) = 
       Some r.
Proof.
  induction ls0; intros fa t i0 la va bs l0 init Hinc; simpl in *.
    exists init. auto.

    assert (incl ls0 (bound_blocks bs)) as J.
      simpl_env in Hinc.
      eapply incl_app_invr; eauto.
    assert (exists b, lookupAL block (genLabel2Block_blocks bs) a = Some b) 
      as Hlkup.
      clear - Hinc.
      simpl_env in Hinc.
      apply incl_app_invl in Hinc.
      apply inc__getLabel2Block_blocks; auto.

    destruct Hlkup as [b Hlkup].
    rewrite Hlkup. 
    destruct (eq_atom_dec a l0); subst; auto.
Qed.

Lemma fold_left__spec : forall ls0 l0 init r f,
  fold_left (inscope_of_block f l0) ls0 (Some init) = Some r ->
    incl init r /\
    (forall l1 b1, 
      In l1 (ListSet.set_diff eq_atom_dec ls0 [l0]) -> 
      lookupBlockViaLabelFromFdef f l1 = Some b1 ->
      incl (getBlockIDs b1) r) /\
    (forall id1,
      In id1 r ->
      In id1 init \/
      exists b1, exists l1, In l1 (ListSet.set_diff eq_atom_dec ls0 [l0]) /\
        lookupBlockViaLabelFromFdef f l1 = Some b1 /\
        In id1 (getBlockIDs b1)
    ).
Proof.
  induction ls0; intros l0 init r f Hfold; simpl in *.
    inv Hfold.
    split. apply incl_refl.
    split; auto. 
      intros ? ? Hfalse. inversion Hfalse.
      
    remember (lookupBlockViaLabelFromFdef f a) as R.
    destruct R.
      destruct (eq_atom_dec a l0); subst; auto.
      apply IHls0 in Hfold.
      destruct Hfold as [J1 [J2 J3]].
      split.
        eapply incl_app_invr; eauto.
      split.
        intros l1 b1 Hin Hlkup.
        apply ListSet.set_add_elim in Hin.
        destruct Hin as [Hin | Hin]; subst; eauto.                  
          rewrite Hlkup in HeqR. inv HeqR.
          eapply incl_app_invl; eauto.
        intros id1 Hin.
        apply J3 in Hin.
        destruct Hin as [Hin | [b1 [l1 [H1 [H2 H3]]]]].
          apply in_app_or in Hin.
          destruct Hin as [Hin | Hin]; auto.
          right. 
          exists b. exists a.
          split; auto.
            apply ListSet.set_add_intro; auto.
             
          right.
          exists b1. exists l1.
          split; auto.
            apply ListSet.set_add_intro; auto.

      rewrite fold_left__none in Hfold. inversion Hfold.
Qed.

Inductive wf_phi_operands (f:fdef) (b:block) (id0:id) (t0:typ) : 
    list_value_l -> Prop :=
| wf_phi_operands_nil : wf_phi_operands f b id0 t0 Nil_list_value_l
| wf_phi_operands_cons_vid : forall vid1 l1 vls b1 vb, 
    vid1 <> id0 \/ (not (isReachableFromEntry f b)) ->
    lookupBlockViaIDFromFdef f vid1 = Some vb ->
    lookupBlockViaLabelFromFdef f l1 = Some b1 ->
    blockDominates f vb b1 \/ (not (isReachableFromEntry f b)) ->
    wf_phi_operands f b id0 t0 vls ->
    wf_phi_operands f b id0 t0 (Cons_list_value_l (value_id vid1) l1 vls)
| wf_phi_operands_cons_vc : forall c1 l1 vls, 
    wf_phi_operands f b id0 t0 vls ->
    wf_phi_operands f b id0 t0 (Cons_list_value_l (value_const c1) l1 vls).

Definition check_list_value_l (f:fdef) (b:block) (vls:list_value_l) := 
  let ud := genBlockUseDef_fdef f in
  let vls1 := unmake_list_value_l vls in
  let '(vs1,ls1) := List.split vls1 in 
  let ls2 := predOfBlock b ud in
  (length ls2 > 0)%nat /\
  AtomSet.set_eq _ ls1 ls2 /\
  NoDup ls1.

Definition wf_phinode (f:fdef) (b:block) (p:phinode) :=
let '(insn_phi id0 t0 vls0) := p in
wf_phi_operands f b id0 t0 vls0 /\ check_list_value_l f b vls0. 

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
