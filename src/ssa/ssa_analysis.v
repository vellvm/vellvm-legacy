Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import assoclist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.

Export LLVMlib.

(** * Domination analysis *)

(** The type [Dominators] of compile-time approximations of domination. *)

(** We equip this type of approximations with a semi-lattice structure.
  The ordering is inclusion between the sets of values denoted by
  the approximations. *)

Module Dominators.
  Section VarBoundSec.

  Variable bound:atoms.

  Record BoundedSet := mkBoundedSet {
    bs_contents : atoms;
    bs_bound : bs_contents [<=] bound
  }.

  Definition t := BoundedSet.

  Definition eq (x y: t) :=
    let '(mkBoundedSet cx _) := x in
    let '(mkBoundedSet cy _) := y in
    cx [=] cy.

  Definition eq_refl: forall x, eq x x. 
  Proof.
    unfold eq. intro x. destruct x.
    fsetdec.
  Qed.

  Definition eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    unfold eq. intros x y J. destruct x. destruct y.
    fsetdec.
  Qed.
  
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq. intros x y z J1 J2. destruct x. destruct y. destruct z.
    fsetdec.
  Qed.

  Lemma eq_dec: forall (x y: t), {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. destruct x. destruct y.
    apply AtomSetImpl.eq_dec.
  Qed.

  Definition beq (x y: t) := if eq_dec x y then true else false.

  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    unfold beq; intros.  destruct (eq_dec x y). auto. congruence.
  Qed.

  Definition sub (x y: t) :=
    let '(mkBoundedSet cx _) := x in
    let '(mkBoundedSet cy _) := y in
    cx [<=] cy.

  Program Definition top : t := mkBoundedSet {} _.
  Next Obligation.
    fsetdec.
  Qed.

  Program Definition bot : t := mkBoundedSet bound _.
  Next Obligation.
    fsetdec.
  Qed.

  Definition ge (x y: t) : Prop := eq x top \/ eq y bot \/ sub x y.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold ge, eq, sub. destruct x, y. simpl.
    intro J. right. right. fsetdec.
  Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge, eq, sub. destruct x, y, z. simpl.
    intros J1 J2.
    destruct J1 as [J11 | [J12 | J13]]; try auto.
      destruct J2 as [J21 | [J22 | J23]]; try auto.
        assert (bound [=] empty) as EQ by fsetdec.
        left. fsetdec.
        right. left. fsetdec.
      destruct J2 as [J21 | [J22 | J23]]; try auto.
        left. fsetdec.
        right. right. fsetdec.
  Qed.
  Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
  Proof.
    unfold ge, eq, sub. destruct x, x', y, y'. simpl in *. 
    intros J1 J2 J3.
    destruct J3 as [J31 | [J32 | J33]].
      left. fsetdec.
      right. left. fsetdec.
      right. right. fsetdec.
  Qed.
  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, eq, sub. destruct x. simpl. right. left. fsetdec.
  Qed.
  Lemma ge_top: forall x, ge top x.
  Proof.
    unfold ge, eq, sub. destruct x. simpl. left. fsetdec.
  Qed.
  Program Definition lub (x y: t) : t :=
    let '(mkBoundedSet cx _) := x in
    let '(mkBoundedSet cy _) := y in
    mkBoundedSet (AtomSetImpl.inter cx cy) _.
  Next Obligation.
    fsetdec.
  Qed.
  Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
  Proof.
    unfold lub, eq. destruct x, y. fsetdec.
  Qed.
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold lub, ge, sub, eq. destruct x, y. simpl.
    right. right. fsetdec.
  Qed.

  Program Definition add (x:t) (a:atom) : t := 
    let '(mkBoundedSet cx _) := x in
    if (AtomSetProperties.In_dec a bound) then
      mkBoundedSet (AtomSetImpl.add a cx) _
    else
      x.
  Next Obligation.
  Admitted.

  End VarBoundSec. 
End Dominators.

Module Dataflow_Solver_Var_Top (NS: NODE_SET).

Module L := Dominators.

Section Kildall.

Variable bound : atoms.
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

Fixpoint propagate_succ_list (s: state) (out: dt) (succs: list atom)
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

Definition successors_terminator (tmn: terminator) : ls :=
match tmn with
| insn_return _ _ _ => nil
| insn_return_void _ => nil
| insn_br _ _ l1 l2 => l1::l2::nil
| insn_br_uncond _ l1 => l1::nil
| insn_unreachable _ => nil
end.

Fixpoint successors_blocks (bs: blocks) : ATree.t ls :=
match bs with
| nil => ATree.empty ls
| block_intro l0 _ _ tmn :: bs' => 
    ATree.set l0 (successors_terminator tmn) (successors_blocks bs')
end.

Fixpoint successors (f: fdef) : ATree.t ls :=
let '(fdef_intro _ bs) := f in
successors_blocks bs.

Definition transfer (bound: atoms) (lbl: l) (before: Dominators.t bound) :=
  Dominators.add _ before lbl.

(** The static analysis itself is then an instantiation of Kildall's
  generic solver for forward dataflow inequations. [analyze f]
  returns a mapping from program points to mappings of pseudo-registers
  to approximations.  It can fail to reach a fixpoint in a reasonable
  number of iterations, in which case [None] is returned. *)

Module DomDS := Dataflow_Solver_Var_Top(AtomNodeSet).

Fixpoint bound_blocks (bs: blocks) :  atoms :=
match bs with
| nil => {}
| block_intro l0 _ _ tmn :: bs' => {{l0}} `union` (bound_blocks bs')
end.

Fixpoint bound_fdef (f: fdef) :  atoms :=
let '(fdef_intro _ bs) := f in
bound_blocks bs.

Program Definition dom_analyze (f: fdef): AMap.t (Dominators.t (bound_fdef f)) :=
  let bound := bound_fdef f in
  let top := Dominators.top bound in
  match getEntryBlock f with
  | Some (block_intro le _ _ _) =>
      match DomDS.fixpoint bound (successors f) (transfer bound) 
        ((le, Dominators.mkBoundedSet _ {{le}} _) :: nil) with
      | None => AMap.init top
      | Some res => res
      end
  | None => AMap.init top
  end.
Next Obligation.
  destruct f. 
  destruct b; simpl in *; inv Heq_anonymous. 
    fsetdec.
Qed.

Definition blockDominates (f: fdef) (b1 b2: block) : Prop :=
let '(block_intro l1 _ _ _) := b1 in
let '(block_intro l2 _ _ _) := b2 in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l2 dt in
AtomSetProperties.In_dec l1 els.

Definition blockDominatesB (f: fdef) (b1 b2: block) : Prop :=
let '(block_intro l1 _ _ _) := b1 in
let '(block_intro l2 _ _ _) := b2 in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l2 dt in
if AtomSetProperties.In_dec l1 els then true else false.

Definition insnDominates (i1 i2:insn) (b:block) : Prop :=
match b with 
| (block_intro l5 ps cs tmn) =>
    match (i1, i2) with
    | (insn_cmd _, insn_terminator _) => True  
    | (insn_phinode _, insn_terminator _) => True
    | (insn_phinode _, insn_cmd _) => True
    | (insn_cmd c1, insn_cmd c2) => 
      (exists cs1, exists cs2, exists cs3, cs = cs1++(c1::cs2)++(c2::cs3))
    | (insn_phinode p1, insn_phinode p2) => 
      (exists ps1, exists ps2, exists ps3, ps = ps1++(p1::ps2)++(p2::ps3))
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
 
(* blocks to CFG, which may not be useful. *)
(*
Fixpoint blocks_to_Vset (bs:blocks) : V_set :=
match bs with
| nil => V_empty
| block_intro l _ _ _ :: bs' => V_union (V_single (index l)) (blocks_to_Vset bs')
end.

Fixpoint blocks_to_Aset (bs:blocks) : A_set :=
match bs with
| nil => A_empty
| block_intro l0 _ _ (insn_br _ _ l1 l2) :: bs' => 
    A_union (A_single (A_ends (index l0) (index l1)))
      (A_union (A_single (A_ends (index l0) (index l2))) (blocks_to_Aset bs'))
| block_intro l0 _ _ (insn_br_uncond _ l1) :: bs' => 
    A_union (A_single (A_ends (index l0) (index l1))) (blocks_to_Aset bs')
| block_intro l0 _ _ _ :: bs' => blocks_to_Aset bs'
end.

Lemma blocks_to_Vset_spec : forall (blocks5 : blocks) (l0 : l) 
  (H4 : l0 `notin` dom (genLabel2Block_blocks blocks5)),
  ~ blocks_to_Vset blocks5 (index l0).
Proof.
  intros.
  induction blocks5; intro J.
    inversion J.

    destruct a. simpl in *.
    inversion J; subst.
      inversion H; subst.
      fsetdec.

      apply IHblocks5; try solve [auto | fsetdec].
Qed.

Lemma blocks_to_CFG_add_Vs : forall F bs,
  cfg_blocks F bs ->
  uniq (genLabel2Block_blocks bs) ->
  exists cfg : Digraph (blocks_to_Vset bs) A_empty, True.
Proof.
  intros F bs Hwfbs Huniq. 
  induction Hwfbs; simpl; intros.
    exists D_empty. auto.
    
    destruct block5 as [l0 ? ? tmn].
    inversion Huniq; subst.
    apply IHHwfbs in H2.
    destruct H2 as [cfg _].
    assert (~ blocks_to_Vset blocks5 (index l0)) as J.
      eapply blocks_to_Vset_spec; eauto.
    destruct tmn;
      apply D_vertex with (x:=index l0) in cfg; 
        try solve [auto | exists cfg; auto].
Qed.

Lemma Included_union_right : forall U (E F C: U_set U), 
  Included U (Union U E F) C ->
  Included U F C.
Proof.
        unfold Included in |- *; intros.
        apply H. apply In_right. trivial.
Qed.

Lemma Included_union_left : forall U (E F C: U_set U), 
  Included U (Union U E F) C ->
  Included U E C.
Proof.
        unfold Included in |- *; intros.
        apply H. apply In_left. trivial.
Qed.

Lemma blocks_to_CFG_add_As : forall F bs Vs,
  cfg_blocks F bs ->
  uniq (genLabel2Block_blocks bs) ->
  V_included (blocks_to_Vset bs) Vs ->
  Digraph Vs A_empty ->
  exists cfg : Digraph Vs (blocks_to_Aset bs), True.
Proof.
  intros F bs Vs Hwfbs Huniq Hinc Hcfg. 
  induction Hwfbs; simpl in *; intros.
    exists Hcfg. auto.
    
    destruct block5 as [l0 ? ? tmn]; simpl in *.
    inversion Huniq; subst.
    assert (J:=Hinc).
    apply Included_union_left in J.
    apply Included_union_right in Hinc.
    apply IHHwfbs in H2; auto.
    destruct H2 as [cfg _].
    destruct tmn.
      exists cfg. auto.
      exists cfg. auto.

      apply D_arc with (x:=index l0)(y:=index l2) in cfg.
        apply D_arc with (x:=index l0)(y:=index l1) in cfg.
          exists cfg. auto.
          unfold Included in J. apply J. unfold V_single. apply In_single.
         
          admit.
          admit.
          admit.
          admit.
          admit.
      admit.
      exists cfg. auto.
Qed.

Lemma blocks_to_CFG : forall F bs,
  cfg_blocks F bs ->
  uniq (genLabel2Block_blocks bs) ->
  exists cfg : Digraph (blocks_to_Vset bs) (blocks_to_Aset bs), True.
Proof.
  intros F bs Hwfbs Huniq.
  assert (J:=Hwfbs).
  apply blocks_to_CFG_add_Vs in J; auto.
  destruct J as [cfg _].
  eapply blocks_to_CFG_add_As; eauto.
    unfold V_included, Included. auto.
Qed.
*)

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
