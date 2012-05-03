Require Export Coqlib.
Require Export Iteration.
Require Export Maps.


(*
Program Fixpoint DFS (succs:ATree.t ls) (visited:ATree.t ls)
  (acc:ATree.t positive * PTree.t l) 
  (po:positive) (todo:ls) 
  {measure ((fun s' v' => f s' - length) visited succs)} :
  (ATree.t positive * PTree.t l) := 
match todo with
| nil => acc
| next::todo' =>
    match ATree.get next visited with
    | None => 
        let acc' := DFS succs visited acc po (succs!!!next) in
        acc'
    | Some _ => DFS succs visited acc po todo'
    end
end.
*)

Notation "a ! b" := (PTree.get b a) (at level 1).
Notation "a !! b" := (PMap.get b a) (at level 1).

Definition successors_list (successors: PTree.t (list positive)) (pc: positive) 
  : list positive :=
  match successors!pc with None => nil | Some l => l end.

Notation "a !!! b" := (successors_list a b) (at level 1).

Module Type PNODE_SET.

  Variable t: Type.
  Variable add: positive -> t -> t.
  Variable pick: t -> option (positive * t).
  Variable initial: PTree.t (list positive) -> t.

  Variable In: positive -> t -> Prop.
  Hypothesis add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Hypothesis pick_none:
    forall s n, pick s = None -> ~In n s.
  Hypothesis pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Hypothesis initial_spec:
    forall successors n s,
    successors!n = Some s -> In n (initial successors).

End PNODE_SET.

Require Import FSets.
Require Import FSetAVL.
Require Import Ordered.

Module PositiveSet := FSetAVL.Make(OrderedPositive).
Module PositiveSetFacts := FSetFacts.Facts(PositiveSet).
Module PTree_Properties := Tree_Properties(PTree).

Module PNodeSetForward <: PNODE_SET.
  Definition t := PositiveSet.t.
  Definition add (n: positive) (s: t) : t := PositiveSet.add n s.
  Definition pick (s: t) :=
    match PositiveSet.max_elt s with
    | Some n => Some(n, PositiveSet.remove n s)
    | None => None
    end.
  Definition initial (successors: PTree.t (list positive)) :=
    PTree.fold (fun s pc scs => PositiveSet.add pc s) successors PositiveSet.empty.
  Definition In := PositiveSet.In.

  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Proof.
    intros. exact (PositiveSetFacts.add_iff s n n').
  Qed.

  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
  Proof.
    intros until n; unfold pick. caseEq (PositiveSet.max_elt s); intros.
    congruence.
    apply PositiveSet.max_elt_3. auto.
  Qed.

  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Proof.
    intros until s'; unfold pick. caseEq (PositiveSet.max_elt s); intros.
    inversion H0; clear H0; subst.
    split; intros.
    destruct (peq n n'). auto. right. apply PositiveSet.remove_2; assumption.
    elim H0; intro. subst n'. apply PositiveSet.max_elt_1. auto.
    apply PositiveSet.remove_3 with n; assumption.
    congruence.
  Qed.

  Lemma initial_spec:
    forall successors n s,
    successors!n = Some s -> In n (initial successors).
  Proof.
    intros successors.
    apply PTree_Properties.fold_rec with
      (P := fun succ set =>
              forall n s, succ!n = Some s -> In n set).
    (* extensionality *)
    intros. rewrite <- H in H1. eauto.
    (* base case *)
    intros. rewrite PTree.gempty in H. congruence.
    (* inductive case *)
    intros. rewrite PTree.gsspec in H2. rewrite add_spec.
    destruct (peq n k). auto. eauto.
  Qed.
End PNodeSetForward.

Module Type LATTICEELT.

  Variable t: Type.
  Variable eq: t -> t -> Prop.
  Hypothesis eq_refl: forall x, eq x x.
  Hypothesis eq_sym: forall x y, eq x y -> eq y x.
  Hypothesis eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Variable beq: t -> t -> bool.
  Hypothesis beq_correct: forall x y, beq x y = true -> eq x y.
  Variable bot: t.
  Variable lub: t -> t -> t.
  Variable top: t.

End LATTICEELT.

Module LDoms <: LATTICEELT.

Definition t := option (list positive).

Definition beq_hd (l1 l2: list positive) : bool :=
match l1, l2 with
| h1::_, h2::_ => Peqb h1 h2
| nil, nil => true
| _, _ => false
end.

Definition beq (x y:t) : bool := 
match x, y with
| Some x', Some y' => beq_hd x' y'
| None, None => true
| _, _ => false
end.

Definition eq (x y: t) := beq x y = true.

Hint Unfold eq beq.

Ltac Peqb_eq_tac :=
repeat match goal with
| H: Peqb _ _ = true |- _ => eapply Peqb_eq in H; subst
| |- Peqb _ _ = true => eapply Peqb_eq
end.

Lemma eq_refl: forall x, eq x x.
Proof.
  destruct x as [[|x]|]; auto.
    autounfold. simpl. Peqb_eq_tac. auto.
Qed.

Lemma eq_sym: forall x y (Heq: eq x y), eq y x.
Proof.
  destruct x as [[|x]|]; destruct y as [[|y]|]; intros; inv Heq; auto.
    autounfold. simpl. Peqb_eq_tac. auto.
Qed.

Lemma eq_trans: forall x y z (Heq1: eq x y) (Heq2: eq y z), eq x z.
Proof.
  intros.
  destruct x as [[|x]|]; destruct y as [[|y]|]; inv Heq1; auto.
  destruct z as [[|z]|]; inv Heq2; auto.
    autounfold. simpl. Peqb_eq_tac. auto.
Qed.

Lemma beq_correct: forall x y (Heq: beq x y = true), eq x y.
Proof. auto. Qed.

Definition bot : t := None.

Program Fixpoint merge (l1 l2: list positive) 
  {measure ((fun l1 l2 => (length l1 + length l2)%nat) l1 l2)}
  : list positive :=
match l1, l2 with
| p1::l1', p2::l2' =>
    match (Pcompare p1 p2 Eq) with
    | Eq => l1
    | Lt => merge l1' l2 
    | Gt => merge l1 l2'
    end
| _, _ => nil
end.
Next Obligation.
  simpl. omega.
Qed.

Definition lub (x y:t) : t :=
match x, y with
| Some x', Some y' => Some (merge x' y')
| _, None => x
| None, _ => y
end.

Definition top : t := Some nil.

End LDoms.

Module Weak_Dataflow_Solver (NS: PNODE_SET) (L: LATTICEELT).

Section Kildall.

Variable successors: PTree.t (list positive).
Variable transf : positive -> L.t -> L.t.
Variable entrypoints: list (positive * L.t).

(** The state of the iteration has two components:
- A mapping from program points to values of type [L.t] representing
  the candidate solution found so far.
- A worklist of program points that remain to be considered.
*)

Record state : Type :=
  mkstate { st_in: PMap.t L.t; st_wrk: NS.t }.

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

Fixpoint start_state_in (ep: list (positive * L.t)) : PMap.t L.t :=
  match ep with
  | nil =>
      PMap.init L.bot
  | (n, v) :: rem =>
      let m := start_state_in rem in PMap.set n (L.lub m!!n v) m
  end.

Definition start_state :=
  mkstate (start_state_in entrypoints) (NS.initial successors).

(** [propagate_succ] corresponds, in the pseudocode,
  to the body of the [for] loop iterating over all successors. *)

Definition propagate_succ (s: state) (out: L.t) (n: positive) :=
  let oldl := s.(st_in)!!n in
  let newl := L.lub oldl out in
  if L.beq oldl newl
  then s
  else mkstate (PMap.set n newl s.(st_in)) (NS.add n s.(st_wrk)).

(** [propagate_succ_list] corresponds, in the pseudocode,
  to the [for] loop iterating over all successors. *)

Fixpoint propagate_succ_list (s: state) (out: L.t) (succs: list positive)
                             {struct succs} : state :=
  match succs with
  | nil => s
  | n :: rem => propagate_succ_list (propagate_succ s out n) out rem
  end.

(** [step] corresponds to the body of the outer [while] loop in the
  pseudocode. *)

Definition step (s: state) : PMap.t L.t + state :=
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

Definition fixpoint : option (PMap.t L.t) :=
  PrimIter.iterate _ _ step start_state.

(*
(** ** Monotonicity properties *)

(** We first show that the [st_in] part of the state evolves monotonically:
  at each step, the values of the [st_in[n]] either remain the same or
  increase with respect to the [L.ge] ordering. *)

Definition in_incr (in1 in2: AMap.t L.t) : Prop :=
  forall n, L.ge in2!!n in1!!n.

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
  case (L.beq st.(st_in)!!n (L.lub st.(st_in)!!n out)).
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
             L.ge st.(st_in)!!s (transf n st.(st_in)!!n)).

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
  L.ge st'.(st_in)!!n out /\
  (forall s, n <> s -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  unfold propagate_succ; intros; simpl.
  predSpec L.beq L.beq_correct
           ((st_in st) !! n) (L.lub (st_in st) !! n out).
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
  (In s scs -> L.ge st'.(st_in)!!s out) /\
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
  case (L.beq (st_in st) !! n (L.lub (st_in st) !! n out)).
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
  case (L.beq (st_in st) !! n (L.lub (st_in st) !! n out)).
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
  case (eq_atom_dec x n); intro.
  (* Case 1: x = n *)
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
  L.ge res!!s (transf n res!!n).
Proof.
  assert (forall res, fixpoint = Some res ->
          forall n s,
          In s successors!!!n ->
          L.ge res!!s (transf n res!!n)).
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
  L.ge (start_state_in ep)!!n v.
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
  L.ge res!!n v.
Proof.
  intros.
  apply L.ge_trans with (start_state_in entrypoints)!!n.
  apply fixpoint_incr. auto.
  apply start_state_in_entry. auto.
Qed.

(** ** Preservation of a property over solutions *)

Variable P: L.t -> Prop.
Hypothesis P_bot: P L.bot.
Hypothesis P_lub: forall x y, P x -> P y -> P (L.lub x y).
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
    destruct (LAT.beq (st_in st)!!n (LAT.lub (st_in st)!!n v)).
    auto. simpl. rewrite AMap.gsspec. destruct (eq_atom_dec pc n).
    apply P_lub. subst n; auto. auto.
    auto.
  assert (forall l st v, inv st -> P v -> inv (propagate_succ_list st v l)).
    induction l; intros; simpl. auto.
    apply IHl; auto.
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
*)

End Kildall.

End Weak_Dataflow_Solver.

Require Import syntax.
Require Import infrastructure.
Import LLVMsyntax.
Parameter dfs : ATree.t ls -> l -> positive -> ATree.t positive * PTree.t l.

Fixpoint asucc_psucc_aux (mapping: ATree.t positive)  
                         (pred: PTree.t (list positive))
                         (pfrom: positive) (tolist: list l)
                         {struct tolist} : (PTree.t (list positive)) :=
  match tolist with
  | nil => pred
  | to :: rem =>
    match ATree.get to mapping with
    | Some pto => 
        asucc_psucc_aux mapping 
          (PTree.set pfrom (pto :: pred!!!pfrom) pred) pfrom rem
    | _ => pred
    end
  end.

Definition asucc_psucc (mapping: ATree.t positive)  
                       (pred: PTree.t (list positive))
                       (from: l) (tolist: list l)
                       : PTree.t (list positive) :=
  match ATree.get from mapping with
  | Some pfrom => asucc_psucc_aux mapping pred pfrom tolist
  | _ => pred
  end.

Definition asuccs_psuccs (mapping: ATree.t positive) (succs: ATree.t ls)  
  : PTree.t (list positive) :=
  ATree.fold (asucc_psucc mapping) succs (PTree.empty (list positive)).

Fixpoint psucc_asucc_aux (mapping: PTree.t l)  
                         (pred: ATree.t (list l))
                         (afrom: l) (tolist: list positive)
                         {struct tolist} : (ATree.t (list l)) :=
  match tolist with
  | nil => pred
  | to :: rem =>
    match PTree.get to mapping with
    | Some ato => 
        psucc_asucc_aux mapping 
          (ATree.set afrom (ato :: Kildall.successors_list pred afrom) pred) 
            afrom rem
    | _ => pred
    end
  end.

Definition psucc_asucc (mapping: PTree.t l)  
                       (pred: ATree.t (list l))
                       (from: positive) (tolist: list positive)
                       : ATree.t (list l) :=
  match PTree.get from mapping with
  | Some afrom => psucc_asucc_aux mapping pred afrom tolist
  | _ => pred
  end.

Definition psuccs_asuccs (mapping: PTree.t l) (succs: PTree.t (list positive))  
  : ATree.t (list l) :=
  PTree.fold (psucc_asucc mapping) succs (ATree.empty (list l)).

Module DomDS := Weak_Dataflow_Solver (PNodeSetForward) (LDoms).

Definition transfer (n:positive) (input: LDoms.t) : LDoms.t :=
match input with
| None => Some (n::nil)
| Some ps => Some (n::ps)
end.

Require analysis.

Definition dom_analyze (f: fdef) : PMap.t LDoms.t :=
  let asuccs := analysis.successors f in
  match LLVMinfra.getEntryBlock f with
  | Some (block_intro le _ _ _) =>
      let '(a2p, p2a) := dfs asuccs le 1%positive in
      let psuccs := asuccs_psuccs a2p asuccs in
      match ATree.get le a2p with
      | Some pe => 
        match DomDS.fixpoint psuccs transfer ((pe, LDoms.top) :: nil) with
        | None => (PMap.set pe LDoms.top (PMap.init LDoms.bot))
        | Some res => res
        end
      | None => PMap.init LDoms.bot
      end
  | None => PMap.init LDoms.bot
  end.



