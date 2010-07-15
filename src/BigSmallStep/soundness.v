(** In compiler verification, we have different opinions to formalize the
    semantics of underlying languages. Small-step semantics can precisely
    define convergence and divergence with a trace of effects during 
    execution, while big-step semantics helps when proving the correctness of
    translation between high-level source languages and lower-level target 
    languages. But big-step semantics usually fail to distinguish non-terminating
    and stuck programs. 

    Using a call-by-value functional language as an example, this script 
    illustrates the use of coinductive definitions and proofs in big-step 
    operational semantics, enabling it to describe diverging evaluations in 
    addition to terminating evaluations. 

    We study the use of coinductive big-step semantics in proofs of type 
    soundness, and then summarize the connections between the coinductive 
    big-step semantics and the standard small-step semantics, proving that 
    both semantics are equivalent.

    The results and proof infrastructures can also be applied to imperative 
    languages.
*)

Add LoadPath "../../../theory/metatheory".
Require Export Coq.Program.Equality.
Require Export lang_inf.
Require Export lang_more.
Require Export Coq.Logic.Classical_Prop.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : typing_env => dom x) in
  let D1 := gather_atoms_with (fun x => fv_exp x) in
  constr:(A \u B \u C \u D1).

(* *********************************************************************** *)
(** * Notations *)
Notation " e ---> e' " := (smallstep e e') (at level 50, left associativity).
Notation " e --->* e' " := (smallstep_converging e e') (at level 50, left associativity).
Notation " e ===> e' " := (bigstep_converging e e') (at level 50, left associativity).

(* *********************************************************************** *)
(** * Conversion of forall, exists, and negation. *)

Lemma forall_neq__neq_exists : forall (A:Type) (P:A -> Prop), 
  (forall x, ~ P x) <-> (~ exists x, P x).
Proof.
  intros A P.
  split; intro J.
    intro J'. destruct J' as [x J'].
    apply (@J x); auto.

    intros x J'.
    apply J. exists x. auto.
Qed.

(** This lemma needs classical axioms. *)
Lemma neq_forall__exists_neq : forall (A:Type) (P:A -> Prop), 
  (~ forall x, P x) <-> (exists x, ~ P x).
Proof.
  intros A P.
  split; intro J.
    destruct (@classic (exists x, ~ P x)); auto.
    Case "~(exists x, ~ P x)".
      assert (forall x, P x) as nJ.
        intro x. apply NNPP.
        revert x.
        apply (@forall_neq__neq_exists A (fun x => ~ P x)); auto.
      contradict nJ; auto.
  
    intro J'. destruct J as [x J].
    apply J; auto.
Qed.

(* *********************************************************************** *)
(** * Regularity lemmas *)

Lemma typing_regular_1 : forall G e T,
  typing G e T ->
  lc_exp e.
Proof. induction 1; eauto. Qed.

Hint Resolve typing_regular_1.

Lemma typing_regular_2 : forall G e T,
  typing G e T ->
  uniq G.
Proof.
  (typing_cases (induction 1) Case); eauto.
  pick fresh z. lapply (H0 z); solve_uniq.
Qed.

Hint Resolve typing_regular_2.

Lemma smallstep_regular_1 : forall e1 e2,
  e1 ---> e2 ->
  lc_exp e1.
Proof. induction 1; eauto. Qed.

Hint Resolve smallstep_regular_1.

Lemma smallstep_regular_2 : forall e1 e2,
  e1 ---> e2 ->
  lc_exp e2.
Proof. induction 1; intuition eauto 6 with lngen. Qed.

Hint Resolve smallstep_regular_2.

Lemma smallstep_converging_regular_1 : forall e e',
  e --->* e' -> lc_exp e.
Proof.
  intros e e' e_to_e'.
  induction e_to_e'; eauto.
Qed.

Lemma smallstep_converging_regular_2 : forall e e',
  e --->* e' -> lc_exp e'.
Proof.
  intros e e' e_to_e'.
  induction e_to_e'; eauto.
Qed.

(* *********************************************************************** *)
(** * Decidable *)

Lemma is_value_of_exp_dec : forall e,
  is_value_of_exp e \/ ~ is_value_of_exp e.
Proof.
  induction e; simpl; auto.
Qed.

(** If we can prove lc_exp is decidable, we can ignore this condition. *)
Lemma smallstep_dec : forall e,
  lc_exp e ->
  (exists e', e ---> e') \/ (~ exists e', e ---> e').
Proof.
  induction 1; try solve [right; intro J; destruct J as [e' J]; inversion J].
    destruct IHlc_exp1 as [[e1' IHlc_exp1] | IHlc_exp1].
    Case "e1 steps".
      left. exists (app e1' e2). auto.
    Case "e1 is stuck".
      destruct (@is_value_of_exp_dec e1) as [e1_is_val | e1_isnt_val].
      SCase "e1 is val".
        destruct IHlc_exp2 as [[e2' IHlc_exp2] | IHlc_exp2].
        SSCase "e2 steps".
          left. exists (app e1 e2'). auto.
        SSCase "e2 is stucks".
          destruct e1; try solve [inversion e1_is_val].
          SSSCase "e1 is const".
            right. intro J. destruct J as [e' J]. 
            inversion J; subst.
              inversion H5.
              apply IHlc_exp2. exists e2'. auto.
          SSSCase "e1 is abs".
            destruct (@is_value_of_exp_dec e2) as [e2_is_val | e2_isnt_val].
            SSSSCase "e2 is val".
              left. exists (open_exp_wrt_exp e1 e2). auto.
            SSSSCase "e2 isnt val".
              right. intro J. destruct J as [e' J].
              inversion J; subst.
                inversion H5.
                apply IHlc_exp2. exists e2'. auto.
                apply e2_isnt_val; auto.
      SCase "e1 isnt val".
        right. intro J. destruct J as [e' J]. 
        inversion J; subst.
          apply IHlc_exp1. exists e1'. auto.
          apply e1_isnt_val; auto.
          apply e1_isnt_val; simpl; auto.
Qed.

(* *********************************************************************** *)
(** * typesoundness1 *)

(** A standard proof technique for showing type soundness replies on small-step
    semantics. The proof uses the properties of [smallstep_preservation]
    and [smallstep_progress].
*)

Lemma canonical_abs : forall G v T1 T2,
  typing G v (arrow T1 T2) ->
  is_value_of_exp v ->
  exists e, v = abs e.
Proof.
  intros G v T1 T2 Typing v_is_val.
  inversion Typing; subst; try solve [simpl in v_is_val; inversion v_is_val].
  exists e. auto.
Qed.

Lemma typing_weakening : forall F E G e T,
  typing (F ++ G) e T ->
  uniq (F ++ E ++ G) ->
  typing (F ++ E ++ G) e T.
Proof.
  intros until 1. (typing_cases (dependent induction H) Case); intros; eauto.
  Case "typing_abs".
   pick fresh x and apply typing_abs.
   rewrite_env ((x ~ T1 ++ F) ++ E ++ G0).
   apply_first_hyp; simpl_env; auto.
Qed.

Lemma typing_subst : forall F G e u S T x,
  typing (F ++ x ~ S ++ G) e T ->
  typing G u S ->
  typing (F ++ G) (subst_exp u x e) T.
Proof with eauto.
  intros until 1. (typing_cases (dependent induction H) Case); intros; simpl subst_exp...
  Case "typing_var".
    destruct (x == x0); try subst x0.
    SCase "x = x0".
      analyze_binds_uniq H.
      apply typing_weakening with (F := nil)...
    SCase "x <> x0".
      analyze_binds_uniq H...
  Case "typing_abs".
    pick fresh z and apply typing_abs.
    rewrite_env ((z ~ T1 ++ F) ++ G0).
    rewrite subst_exp_open_exp_wrt_exp_var...
    apply H0 with (S0 := S)...
Qed.

Lemma smallstep_preservation : forall G e1 e2 T,
  typing G e1 T ->
  e1 ---> e2 ->
  typing G e2 T.
Proof with eauto.
  intros G e1 e2 T H. revert e2.
  (typing_cases (dependent induction H) Case); try solve [intros ? J; inversion J].
  Case "typing_app".
    intros ? J; inversion J; subst...
    inversion H; subst.
    pick fresh z.
    rewrite (subst_exp_intro z)...
    eapply typing_subst with (F := nil); simpl_env...
Qed.

Lemma smallstep_progress : forall e1 T,
  typing nil e1 T ->
  (exists e2, e1 ---> e2) \/ is_value_of_exp e1.
Proof with eauto 10.
  intros e1 T H.
  (typing_cases (dependent induction H) Case); simpl...
  Case "typing_app".
    destruct IHtyping1 as [[e1' ?] | ?]...
    destruct IHtyping2 as [[e2' ?] | ?]...
    destruct e1; inversion H...
Qed.

(** Then we prove that a closed well-typed term is never ever stuck. *)
Lemma typesoundness1 : forall e T e',
  typing nil e T ->
  e --->* e' ->
  (exists e'', e' ---> e'') \/ is_value_of_exp e'.
Proof.
  intros e T e' Typing e_reduces_e'.
  (** By induction on [e --->* e'], the base case is by [smallstep_progress], 
      and the inductive case is by [smallstep_preservation] and IH. *)
  generalize dependent T.
  (smallstep_converging_cases (dependent induction e_reduces_e') Case); intros.
  Case "smallstep_c_refl".
    apply smallstep_progress with (T:=T); auto.
  Case "smallstep_c_trans".
    apply IHe_reduces_e' with (T:=T); auto.
      eapply smallstep_preservation; eauto.
Qed.

(* *********************************************************************** *)
(** * typesoundness2 (classic) *)

(** Following [typesoundness1], informally, we can conclude that 
well-typed closed terms either reduce to a value or reduce infinitely.
[typesoundness2] proves this formally.
*)

(** We first define infinite reductions via coinduction. *)

Reserved Notation " e --->o " (at level 50, left associativity).
CoInductive smallstep_diverging : exp -> Prop :=    
 | smallstep_d_intro : forall (e e':exp),
     e ---> e' ->
     e'--->o  ->
     e --->o
where " e --->o " := (smallstep_diverging e).

Hint Constructors smallstep_diverging.

Definition smallstep_stuck (e:exp) := forall e', ~ e ---> e'.

(** An alternative definition is ~ ex e', e ---> e', which
    is eqivalent to forall e', ~ e ---> e'. *)
Notation " e -\-> " := (smallstep_stuck e) (at level 50, left associativity).

(** Classically, we devided behaviors of terms into two categories:
    normalization and non-termination. First, this lemma shows that
    if a term is unstuck for any finite reductions, it diverges. *)
Lemma finitely_unstuck__diverging : forall e,
  lc_exp e ->
  (forall e', e --->* e' -> ~ e' -\-> ) ->
  e --->o.
Proof.
  cofix Hcoind.
  intros e Hlc H.
  (** if e steps to e', the conclusion follows coinduction, 
        because we know e' is not stuck finitely either;
      otherwise, it is false because we know e is never stuck finitely. 
  *)
  destruct (@smallstep_dec e Hlc) as [[e' e_steps] | e_is_stuck].
  Case "e_steps".
    apply smallstep_d_intro with (e':=e'); auto.
      apply Hcoind; eauto.
  Case "e_is_stuck".
    assert (False) as FALSE.
      destruct (@forall_neq__neq_exists exp (fun x => e ---> x)) as [_ J2].
      apply (@H e (@smallstep_c_refl e Hlc)).
      unfold smallstep_stuck.
      apply J2; auto.
    inversion FALSE.
Qed.

(** By [finitely_unstuck__diverging], we prove that a term is 
    either divergingbing or stuck after finitely steps. *)
Lemma term_is_diverging_or_finitely_stuck : forall e,
  lc_exp e ->
  e --->o \/ (exists e', e --->* e' /\ e' -\->).
Proof.
  intros e Hlc.
  (** Classically, a term is either diverging or not. *)
  destruct (@classic (e --->o)); auto.
  Case "e isnt deverging".
    right.
    (** [finitely_unstuck__diverging] shows that
        it cannnot be the case that e will not stop after finite steps:        
          if ~ e --->o then ~ (forall e', e --->* e' -> ~ e' -\-> ). 
        Classically, this concludes. 
    *)
    assert (J:=@finitely_unstuck__diverging e Hlc).
    apply imply_to_or in J.
    destruct J as [J | J]; try solve [contradict J; auto].
      destruct (@neq_forall__exists_neq exp (fun x=>e --->* x -> ~ x -\-> )) as [J1 _].
      apply J1 in J. clear J1.
      destruct J as [e' J].
      apply imply_to_and in J.
      destruct J as [e_mreduces_e' e'_is_stuck].
      exists e'. split; auto. apply NNPP; auto.
Qed.

Lemma typesoundness2 : forall e T,
  typing nil e T ->
  (exists v, e --->* v /\ is_value_of_exp v) \/ e --->o.
Proof.
  intros e T Typing.
  (** given a term, it is either diverging or stuck afer finite reductions. 
      The former case proves the conclusion. In the latter case, by 
      [typesoundness1], we have that the stuck term must be a value.
  *)
  assert (lc_exp e) as Hlc. eauto.
  destruct (@term_is_diverging_or_finitely_stuck e Hlc) as [e_is_diverging | [e' [e_reducesto_e' e'_is_stuck]]]; auto.
  Case "e_is_finitely_stuck".
    apply typesoundness1 with (e':=e') in Typing; auto.
    destruct Typing as [[e'' e'_steps] | e'_is_val].
    SCase "e'_steps".
      assert (False) as FALSE.
        unfold smallstep_stuck in e'_is_stuck.
        apply (@e'_is_stuck e''); auto.
      inversion FALSE.
    SCase "e'_is_val".      
      left. exists e'. auto.
Qed.


(* *********************************************************************** *)
(** * typesoundness3 (classic) *)

(** --->* --->o define terminating and non-terminating reductions separately. 
    We can also merge them in one judgment that captures both finite and infinite 
    reductions, to reduce the size of definitions.
*)

Reserved Notation " e -o->* e' " (at level 50, left associativity).
CoInductive smallstep_coreductions : exp -> exp -> Prop :=    
 | smallstep_co_refl : forall (e:exp),
     lc_exp e ->
     e -o->* e
 | smallstep_co_trans : forall (e e' e'':exp),
     e ---> e' ->
     e' -o->* e''->
     e -o->* e''
where " e -o->* e' " := (smallstep_coreductions e e').

Hint Constructors smallstep_coreductions.

(** [smallstep_co_refl] rule considers finite reductions, and
    [smallstep_co_trans] defines infinite reductions. So we hope that
    [-o->*] is the union of [--->*] and [--->o].

    First, we prove [-o->*] includes [--->*].
*)
Lemma smallstep_converging__implies__coreductions : forall e e',
  e --->* e' -> e -o->* e'.
Proof.
  intros e e' e_is_converging.
  (* By trivial induction. *)
  induction e_is_converging; eauto.
Qed.

(** Second, if e is diverging, then e should coreduce to any term. 
    It formalizes the intuition that non-terminating terms can prove
    any result. 

    This is stronger than stating that there exists [e'] that e coreduces to. 
    Later, we will show that [=co=>], a big-step coevaluation that 
    merges bigstep convergence and divergence, may only coevaluate to 
    a particular term at some cases. That shows that [=co=>] is smaller
    than [-o->*] by [coevaluation_implies_coreduction].
*)
Lemma smallstep_diverging__implies__coreductions : forall e e',
  e --->o -> e -o->* e'.
Proof.
  (** By coinduction and inversion on [e --->o]. *)
  cofix Hcoind.
  intros e e' e_is_diverging.
  inversion e_is_diverging; subst.
  apply smallstep_co_trans with (e':=e'0); auto.
Qed.

(** Finially, [-o->*] doesn't include more computation than [--->*] and
    [--->o]. In other words, if [e -o->* e'], and it is not the case that 
    [e --->* e'], then e must diverge.
*)
Lemma nonterminating_smallstep_coreductions__diverging : forall e e',
  e -o->* e' ->
  ~ e --->* e' ->
  e --->o.
Proof.
  (** By coinduction and case analysis on [e -o->* e']. *)
  cofix Hcoind.
  intros e e' e_coreduces_to_e' e_isnt_converging_to_e'.
  inversion e_coreduces_to_e'; subst.
  Case "e_coreduces_to_e' by refl".
    (** This is contradictory to the fact that e cannot reduce to e' finitely. *)
    assert (False) as FALSE.
      apply e_isnt_converging_to_e'; auto.
    inversion FALSE.
  Case "e_coreduces_to_e' by trans".
    (** If e steps to e'' that coreduces to e'. 
        We have that e'' cannot reduce to e' finitely either.
        Then we conclude by coinductive hypothesis. *)
    apply smallstep_d_intro with (e':=e'0); eauto.
Qed.

(** Now we proved that -o->* is the union of --->* and --->o.*)
Lemma smallstep_coreductions__iff__converging_and_diverging : forall e e',
  e -o->* e' <->
  (e --->* e' \/ e --->o ).
Proof.
  intros e e'. split.
  Case "e -o->* e' -> (e --->* e' \/ e --->o )".
    (** Classically, either e converges to e' or not. In the latter case, 
        [nonterminating_smallstep_coreductions__diverging] completes the proof.
    *)
    destruct (classic (e --->* e')) as [e_converges_to_e' | e_doesnt_converge_to_e']; auto.
    SCase "e_doesnt_converge_to_e'".
      right. apply nonterminating_smallstep_coreductions__diverging with (e':=e'); auto.
  Case "(e --->* e' \/ e --->o ) -> e -o->* e'".
    (** The conclustion follows that [-o->*] includes [--->*] and [--->o]. *)
    intro J. destruct J as [e_converges_to_e' | e_diverges].
    SCase "e_converges_to_e'".
      apply smallstep_converging__implies__coreductions; auto.  
    SCase "e_diverges".
      apply smallstep_diverging__implies__coreductions; auto.  
Qed.

(** By [typesoundness2] and the fact that [-o->*] is the union of [--->*] and
    [--->o], we show that well-typed closed terms must coreduce to values. *)
Lemma typesoundness3 : forall e T,
  typing nil e T ->
  (exists v, e -o->* v /\ is_value_of_exp v).
Proof.
  intros e T Typing.
  apply typesoundness2 in Typing.
  destruct Typing as [[v [e_converges_to_v v_is_val]] | e_diverges].
  Case "e_converges".
    exists v. split; auto.
    apply smallstep_converging__implies__coreductions; auto.
  Case "e_diverges".
    exists const. split; simpl; auto.
    apply smallstep_diverging__implies__coreductions; auto.
Qed.

(* *********************************************************************** *)
(** * typesoundness4 *)

(** However, can we prove this result without using [typesoundness2]?!

    Consider another reductions. It considers all safe reductions: either
    stopping at values, or running infinitely, but never being stuck finitely.
    It is equivalent to --->o + normalizing --->* or -o->* - stuck --->*.
*)

Reserved Notation " e --->s " (at level 50, left associativity).
CoInductive smallstep_safereductions : exp -> Prop :=    
 | smallstep_s_value : forall (v:exp),
     lc_exp v ->
     is_value_of_exp v ->
     v --->s
 | smallstep_s_trans : forall (e e' e'':exp),
     e ---> e' ->
     e' --->s ->
     e --->s
where " e --->s " := (smallstep_safereductions e).

Hint Constructors smallstep_safereductions.

(** We can prove this version of soundness from only preservation and progress. *)
Lemma typesoundness4 : forall e T,
  typing nil e T -> e --->s.
Proof.
  (** We start with coinduction. Then by [smallstep_progress], we know
      e is either a value (exacly the conclusion) or steps to e'. In the latter
      case, [smallstep_preservation] shows that e' is also well-typed. Then,
      we conclude by coinductive hyp.
  *)
  cofix Hcoind.
  intros e T Typing.
  assert (lc_exp e) as Hlc. eauto.
  assert (J:=Typing).
  apply smallstep_progress in J.
  destruct J as [[e' e_steps_to_e'] | e_is_value]; auto.
  Case "e_steps_to_e'".
    apply smallstep_preservation with (e2:=e') in Typing; eauto.
Qed.

(** I think the problem of [--->s] is that it does not consider the programs
    that "go wrong", so we still need separate rules to define stuck cases. *)

(* *********************************************************************** *)
(** * typesoundness5 *)

(** big-step evaluation [===>] defines the terminating evaluation from terms to values. *)
Lemma bigstep_converges_to_value : forall e v,
  e ===> v -> is_value_of_exp v.
Proof.
  intros e v e_evaluates_to_v.
  (bigstep_converging_cases (induction e_evaluates_to_v) Case); simpl; auto.
Qed.

(** It doesnt consider the cases where evaluation diverges or goes wrong,
    because they do not stop at values. So we cannot prove that
      if 0 |- e : T, then ex v, s.t. e ===> v.
    We can only prove a variant of preservation:
      if a well-typed term evaluates a value, the value preverses the type.    
*)
Lemma bigstep_preservation : forall G e v T,
  typing G e T ->
  e ===> v ->
  typing G v T.
Proof with eauto.
  intros G e v T Typing Bigstep.
  (** By induction on [e ===> v]. *)
  generalize dependent G.
  generalize dependent T.
  (bigstep_converging_cases (induction Bigstep) Case); intros; auto.
  Case "bigstep_c_app".
    inversion Typing; subst.
    apply IHBigstep1 in H4.
    apply IHBigstep2 in H6.
    apply IHBigstep3.
    inversion H4; subst.
    pick fresh z.
    rewrite (subst_exp_intro z)...
    eapply typing_subst with (F := nil); simpl_env...
Qed.

(** The typesoundness for bigstep should state:
      A well-typed closed term is either diverging via big-step, or
      there exists a value that this term can converge to via big-step.

    We first define infinite evaluation via coinduction. *)

Reserved Notation " e ===>o " (at level 50, left associativity).
CoInductive bigstep_diverging : exp -> Prop :=    
 | bigstep_d_app1 : forall (e1 e2:exp),
     e1 ===>o ->
     (app e1 e2) ===>o 
 | bigstep_d_app2 : forall (e1 e2 v1:exp),
     is_value_of_exp v1 ->
     e1 ===> v1  ->
     e2 ===>o ->
     (app e1 e2) ===>o 
 | bigstep_d_appf : forall (e1 e2 e1' v2:exp),
     is_value_of_exp v2 ->
     e1 ===> (abs e1') ->
     e2 ===> v2 ->
     (open_exp_wrt_exp  e1' v2 ) ===>o ->
     (app e1 e2) ===>o
where " e ===>o " := (bigstep_diverging e).

Tactic Notation "bigstep_diverging_cases" tactic(first) tactic(c) :=
  first;
  [ c "bigstep_d_app1" | c "bigstep_d_app2" | c "bigstep_d_appf" ].

Hint Constructors bigstep_diverging.

(** [===>o] defines the cases where non-termination could happen. Suppose we impose
    a left-to-right evaluation order for applications. The non-termination cases are
    1) function is looping, 2) function stops at value, but its argument is looping, 3)
    both function and its argument evaluate to values, but its body diverges.

    Obviously, values are not in non-termination cases.
*)

Lemma value_is_bigstep_converging : forall v,
  is_value_of_exp v ->
  lc_exp v ->
  v ===> v.
Proof.
  intros v v_is_val v_is_lc.
  destruct v; try solve [simpl in v_is_val; inversion v_is_val | auto].
Qed.

Hint Resolve value_is_bigstep_converging.

(** We expect that [===>o] is complete, namely it defines all the diverging cases
    well-typed closed terms can go into. In other words, if well-typed closed terms
    cannot evaluate to values, they must diverge w.r.t [===>o].

    First, we define when a term is stuck for [===>]. 
*)

Definition not_bigstep_converging (e:exp) := forall v, ~ e ===> v.

Notation " e =\=> " := (not_bigstep_converging e) (at level 50, left associativity).

(** Classically we prove that a term is either converging or stuck w.r.t. [===>]. *)
Lemma exp_evaluates_to_value_or_not : forall e,
  (exists v, e ===> v) \/ (e =\=>).
Proof.
  intros e.
  destruct (classic (@e =\=>)) as [e_isnt_converging | e_is_converging]; auto.
    destruct (@neq_forall__exists_neq exp (fun x => ~e ===> x)) as [J1 _].
    apply J1 in e_is_converging. clear J1.
    destruct e_is_converging as [v e_is_converging].
    apply NNPP in e_is_converging.
    left. exists v. auto.
Qed.

(** The new progress property shows that [===>o] is complete. *)
Lemma bigstep_progress : forall e T,
  typing nil e T ->
  e =\=> ->
  e ===>o.
Proof.
  (** The conclusion is coinductive. Case analyis over e gives different 
      constructors of ===>o. We conclude each case by cofix. *)
  cofix Hcoind.
  intros e T Typing e_diverges.
  (exp_cases (destruct e) Case).
  Case "const".
    (** const is converging. This is contradictory. *)
    assert (False) as FALSE.
      unfold not_bigstep_converging in e_diverges.
      apply forall_neq__neq_exists in e_diverges.
      apply e_diverges.
      exists const. auto.
    inversion FALSE.
  Case "var_b".
    (** var_b is not lc. *)
    inversion Typing.
  Case "var_f".
    (** var is not typable in empty context. *)
    inversion Typing; subst.
    inversion H0.
  Case "abs".
    (** abs is also converging. This is contradictory, too. *)
    assert (False) as FALSE.
      unfold not_bigstep_converging in e_diverges.
      apply forall_neq__neq_exists in e_diverges.
      apply e_diverges.
      exists (abs e). 
      apply value_is_bigstep_converging; simpl; eauto.
    inversion FALSE.
  Case "app".
    inversion Typing; subst.
    rename H2 into Typing1. rename H4 into Typing2.
    (** This is the interesting case. We consider the cases whether the function, 
        its argument or the function body evaluates or not. 

        Because we know that this application does not evaluate, at least 
        one of them does not evaluate, at that case we conclude by coinductive hyp.
    *)

    (** By PEM, e1 either evaluates to v1 or not. *)
    destruct (exp_evaluates_to_value_or_not e1) as [[v1 e1_is_converging] | e1_isnt_converging].
    SCase "e1_evaluates_to_v1".
      (** By [bigstep_preservation] and [canonical_abs], e1 must converge to an abs. *)
      apply bigstep_preservation with (v:=v1) in Typing1; auto.
      assert (is_value_of_exp v1) as v1_is_value.
        eapply bigstep_converges_to_value; eauto.
      assert (J:=Typing1).
      apply canonical_abs in J; auto.
      destruct J as [e1' EQ]; subst.
      (** By PEM, e2 either evaluates to v2 or not. *)
      destruct (exp_evaluates_to_value_or_not e2) as [[v2 e2_is_converging] | e2_isnt_converging].
      SSCase "e2_evaluates_to_v2".
        (** By [bigstep_preservation], e2 converges to well-typed value. *)
        apply bigstep_preservation with (v:=v2) in Typing2; auto.
        assert (is_value_of_exp v2) as v2_is_value.
          eapply bigstep_converges_to_value; eauto.
        (** By PEM, {v2/x}e1' either evaluates to v or not. *)
        destruct (exp_evaluates_to_value_or_not (open_exp_wrt_exp e1' v2)) as [[v e1'v2_is_converging] | e1'v2_isnt_converging].
        SSSCase "{v2/x}e1'_evaluates_to_v".
          (** If everything is converging, e1 e2 should also converge. Contradictory *)
          assert (is_value_of_exp v) as v_is_value.
            eapply bigstep_converges_to_value; eauto.
          assert False as FALSE.
            unfold not_bigstep_converging in e_diverges.
            apply forall_neq__neq_exists in e_diverges.
            apply e_diverges.
            exists v. eauto.
          inversion FALSE.
        SSSCase "{v2/x}e1'_doesnt_evaluate".
          (** By coinduction hypothesis and bigstep_d_appf. *)
          apply bigstep_d_appf with (e1':=e1')(v2:=v2); auto.
            apply Hcoind with (T:=T) in e1'v2_isnt_converging; auto.
              inversion Typing1; subst.
              pick fresh z.
              rewrite (subst_exp_intro z); auto.
              assert (z `notin` L) as z_notin_L. auto.
              apply H2 in z_notin_L. simpl_env in z_notin_L.
              eapply typing_subst with (F := nil)(S:=T1); simpl_env; eauto.
      SSCase "e2_doesnt_evaluate".
        (** By coinduction hypothesis and bigstep_d_app2. *)
        apply bigstep_d_app2 with (v1:=abs e1'); auto.
          apply Hcoind with (T:=T1); auto.
    SCase "e1_doesnt_evaluate".
      (** By coinduction hypothesis and bigstep_d_app1. *)
      apply bigstep_d_app1; eauto.
Qed.

(** Now we prove a new type soundness result. *)

Lemma typesoundness5 : forall e T,
  typing nil e T ->
  (exists v, e ===> v) \/ e ===>o. 
Proof.
  intros e T Typing.
  (* We know that e is either converging or stuck. The first cast concludes, and the
     second case is by [bigstep_progess] (that [===>o] is complete).  *)
  destruct (@exp_evaluates_to_value_or_not e) as [e_is_converging | e_isnt_converging]; auto.
  Case "e_isnt_converging".
    right. apply bigstep_progress in Typing; auto.
Qed.  

(** The standard approach for proving type soudness using bigstep semantics
    is to provide inductive inference rules to define a predicate e ===>x
    characterizing terms that go wrong because of a type error, and prove
    the statement "if 0 |- e : T, then it is not the case that e ===>x".
*)

Notation " e ===>x " := (bigstep_goingwrong e) (at level 50, left associativity).

Tactic Notation "bigstep_goingwrong_cases" tactic(first) tactic(c) :=
  first;
  [ c "bigstep_w_app1_wrong" | 
    c "bigstep_w_app1_const" | 
    c "bigstep_w_app2_wrong" |
    c "bigstep_w_appf" ].

Lemma wellformed_term_never_goes_wrong : forall e T,
  typing nil e T -> ~ e ===>x.
Proof with eauto 10.
  intros e T Typing e_goeswrong.
  generalize dependent T.
  (bigstep_goingwrong_cases (induction e_goeswrong) Case); simpl; intros...
  Case "bigstep_w_app1_wrong".
    inversion Typing; subst.
    apply IHe_goeswrong with (T:=arrow T1 T); auto.
  Case "bigstep_w_app1_const".
    inversion Typing; subst.
    apply bigstep_preservation with (v:=const) in H4; auto.
    inversion H4.
  Case "bigstep_w_app2_wrong".
    inversion Typing; subst.
    apply IHe_goeswrong with (T:=T1); auto.
  Case "bigstep_w_appf".
    inversion Typing; subst.
    apply bigstep_preservation with (v:=abs e1') in H5; auto.
    apply bigstep_preservation with (v:=v2) in H7; auto.
    apply IHe_goeswrong with (T:=T); auto.
    inversion H5; subst.
    pick fresh z.
    rewrite (subst_exp_intro z); auto.
    assert (z `notin` L) as z_notin_L. auto.
    apply H6 in z_notin_L. simpl_env in z_notin_L.
    eapply typing_subst with (F := nil)(S:=T1); simpl_env; eauto.
Qed.    

(** [wellformed_term_never_goes_wrong] shows that wellformed terms 
    wont go wrong if [===>x] includes all error cases. Therefore, 
    wellformed terms can only be normalizing or diverge.

    This approach is not fully satisfactory for two reasons: 
    1) extra rules must be provided to define ===>x, which increases the 
       size of the semanstics
    2) there is a risk that the rules for e ===>x are incomplete and miss
       some cases of 'going wrong', in which cases the typing soundness 
       statement does not guarantee that well-typed terms either evaluate to
       a value or diverge.

    [typesoundness5] is an alternative to this approach of showing 
    ~ (e ===>x) for all well-typed terms e. From a methodological standpoint,
    [typesoundness5] addresses one of the above shortcominges, namely
    the risk of not putting in enough error rules. If [===>o] forget some
    divergences rules, the proof of [bigstep_progress] will not go through.
    Therefore, this approach appears rather robust with respect to mistakes
    in the specficaion of the semantics.
   
    The other shortcoming remains. Like [===>x], [===>o] requires more
    evaluation rules than those for normal evalutions, namely the rules for
    divergence, This can easily double the size of the specification of a 
    dynamic semantics, which is a concern for realistic langauges where
    the normal evaluation rules number in dozens. For example:
       http://compcert.inria.fr/doc/html/Csem.html

    Let us consider [=o=>*], which has the same number of rules as normal
    evaluation. It attempts to describe both kinds of evaluations at the 
    same time, like [-o->*], in a more concise way, interpreting coinductively 
    the standard evaluation rules for terminating evaluations.
*)

(* *********************************************************************** *)
(** * typesoundness6 *)

Reserved Notation " e =co=> e' " (at level 50, left associativity).
CoInductive bigstep_coevaluations : exp -> exp -> Prop :=  
 | bigstep_co_const : 
     const =co=> const 
 | bigstep_co_abs : forall (e:exp),
     lc_exp (abs e) ->
     (abs e) =co=> (abs e)
 | bigstep_co_app : forall (e1 e2 v e1' v2:exp),
     is_value_of_exp v ->
     is_value_of_exp v2 ->
     e1 =co=> (abs e1') ->
     e2 =co=> v2 ->
     (open_exp_wrt_exp e1' v2) =co=> v ->
     (app e1 e2) =co=> v
where " e =co=> e' " := (bigstep_coevaluations e e').

Hint Constructors bigstep_coevaluations.

(** It is clear that [=co=>] includes [===>], trivially by induction 
    on [e ===> v]. *)
Lemma evaluations__implies__coevaluations : forall e v,
  e ===> v -> e =co=> v.
Proof.
  intros e v e_evaluates_to_v.
  (bigstep_converging_cases (induction e_evaluates_to_v) Case); auto.
  Case "bigstep_c_app".
    apply bigstep_co_app with (e1':=e1')(v:=v)(v2:=v2); auto.
Qed.

(** It is also true that [=co=>] includes some [===>o]. *)

Definition omega := (app (abs (app 0 0)) (abs (app 0 0))).

Lemma sub_omega_is_lc : lc_exp (abs (app 0 0)).
Proof.
  apply lc_abs.
    intro x. unfold open_exp_wrt_exp. simpl. auto.
Qed.

Hint Resolve sub_omega_is_lc.

Lemma omega_coevaluates_to_anyvalue : forall v,
  is_value_of_exp v ->
  omega =co=> v.
Proof.
  cofix Hcoind.
  intros v v_is_val.
  apply bigstep_co_app with (e1':=app 0 0) (v2:=abs (app 0 0)); simpl; auto.
Qed.

Lemma omega_bigstep_diverges : omega ===>o.
Proof.
  cofix Hcoind.
  apply bigstep_d_appf with (e1':=app 0 0) (v2:=abs (app 0 0)); simpl; auto.
Qed.

(** But [=co=>] is not equivalent to the union of [===>] and [===>o].

    At case [bigstep_co_app], when e1 diverges, [=co=>] still checks e2,
    in the case where e2 is stuck, [=co=>] is stuck. But [===>o] skips e2
    in this case, e1 e2 still diverges.

    Therefore, [=co=>] is not the union of [===>] and [===>o].
    But, we can prove the union of [===>] and [===>o] includes [=co=>].

    As usual, we first prove that [===>o] >= ([=co=>] - [===>]).
*)
Lemma not_converging_coevaluations_must_diverge : forall e v,
  e =co=> v ->
  ~ e ===> v ->
  e ===>o.
Proof.
  cofix Hcoind.
  intros e v e_coevaluates_to_v e_doesnt_evaluate.
  (** The proof goes by coinduction and case analysis on e.
      The cases of var, const, and abs are trivial because they
      are contradictory to that e does not evaluate. xs*)
  (exp_cases (destruct e) Case); try solve [inversion e_coevaluates_to_v].
  Case "const".
    assert False as FALSE.
      apply e_doesnt_evaluate.
      inversion e_coevaluates_to_v; subst; auto.
    inversion FALSE.
  Case "abs". 
    assert False as FALSE.
      apply e_doesnt_evaluate.
      inversion e_coevaluates_to_v; subst; auto.
    inversion FALSE.
  Case "app".
    inversion e_coevaluates_to_v; subst.
    (** By PEM one of e1, e2, or {v2/x}e1' doesn't evaluate, otherwise
        e_doesnt_evaluate is false. At the case where one of them doesn't
        evaluate, we conclude by Hcoind. *)
    destruct (@classic (e1 ===> abs e1')) as [e1_evaluates | e1_is_stuck].
    SCase "e1_evaluates".
      destruct (@classic (e2 ===> v2)) as [e2_evaluates | e2_is_stuck].
      SSCase "e2_evaluates".
        destruct (@classic ((open_exp_wrt_exp e1' v2) ===> v)) as [e1'v2_evaluates | e1'v2_is_stuck].
        SSSCase "{v2/x}e1'_evaluates".
          assert False as FALSE.
            apply e_doesnt_evaluate; eauto.
          inversion FALSE.
        SSSCase "{v2/x}e1'_is_stuck".
          eapply bigstep_d_appf; eauto.
      SSCase "e2_is_stuck".
        apply bigstep_d_app2 with (v1:=abs e1'); simpl; eauto.
    SCase "e1_is_stuck".
      eapply bigstep_d_app1; eauto.
Qed.

Lemma coevaluations__implies__converges_or_diverges : forall e v,
  e =co=> v -> (e ===> v \/ e ===>o).
Proof.
  intros e v e_coevaluates_to_v.
  destruct (@classic (e ===> v)) as [e_converges | e_isnt_converging]; auto.
    apply not_converging_coevaluations_must_diverge in e_coevaluates_to_v; auto.
Qed.

(**  However, the reverse implication from evaluation to coevaluation doesnt
     hold: there exists terms that diverge but do not coevaluate. Consider for
     instance e = omega (0 0). It is true that e [===>o], but there is no
     therm v s.t. e [=co=>] v, because the coevaluation of the argument (0 0)
     goes wrong. How about well-typed term? *)

Conjecture typesoundness6 : forall e T,
  typing nil e T -> exists v, e =co=> v.

(*
     We can prove [=co=>] equals the union of [===>] and [===>o] for STLC. But
     in the system with recursive types, let's consider:
       let rec f x = 
           let g = f x 
           in fun y -> g y
       in f 0 --->
     
       let g1 = f 0 in
       fun y -> g1 y --->

       let g2 = f 0 in
       let g1 = fun y -> g2 y in
       fun y -> g1 y --->

       ...

       let gn = f 0 in
       let gn-1 = fun y -> gn y in
       ...
       let g1 = fun y -> g2 y in
       fun y -> g1 y 

     This is an infinit term 
       \y. (\y. (\y. ... y) y) y
     that we cannot write down. So we cannot prove a version of typesoundness 
     for [=co=>].
*)

(* *********************************************************************** *)
(** * Connections between big-step and small-step semantics. *)
(** We've defined small-step semantics:
      [--->] [--->*] [--->o] [-o->*]
    and big-step semantics:
      [===>] [===>o] [=co=>].

    They have the following relations:
       [--->*] ->  [-o->*]                [smallstep_converging__implies__coreductions]
       [--->o] ->  [-o->*]                [smallstep_diverging__implies__coreductions]
       [-o->*] <-> ([--->*] \/ [--->o])   [smallstep_coreductions__iff__converging_and_diverging]
       [=co=>] ->  ([===>] \/ [===>o])    [coevaluations__implies__converges_or_diverges]
       [===>]  ->  [=co=>]                [evaluations__implies__coevaluations]
       ~ ([===>o]  ->  [=co=>])

    Now, we are proving:
       [--->*] <-> [===>]                 [smallstep_converging__iff__bigstep_converging]
       [--->o] <-> [===>o]                [smallstep_diverging__iff__bigstep_diverging]
       [=co=>] ->  [-o->*]                [coevaluation__implies__coreduction]
       ~ ([-o->*]  ->  [=co=>])
*)

(** ** Some properties for [--->] and [--->*]. *)
Lemma value_doesnt_step : forall v,
  is_value_of_exp v ->
  v -\->.
Proof.
  intros v v_is_val.
  unfold smallstep_stuck.
  eapply forall_neq__neq_exists; eauto.
  destruct v; try solve [simpl in v_is_val; inversion v_is_val].
    intro J. destruct J as [x J]. inversion J.
    intro J. destruct J as [x J]. inversion J.
Qed.

Lemma smallstep_c__trans: forall e e' e'',
  e --->* e' ->
  e' --->* e'' ->
  e --->* e''.
Proof.
  intros.
  generalize dependent e''.
  induction H; intros; eauto.
Qed.

Lemma smallstep_c_app_fun : forall e1 e2 v1,
  lc_exp e2 ->
  e1 --->* v1 ->
  (app e1 e2) --->* (app v1 e2).
Proof.
  intros e1 e2 v1 He Hbrc.
  generalize dependent e2.
  induction Hbrc; intros; eauto.
Qed.

Lemma smallstep_c_app_arg : forall v1 e2 v2,
  lc_exp v1 ->
  is_value_of_exp v1 ->
  e2 --->* v2 ->
  (app v1 e2) --->* (app v1 v2).
Proof.
  intros v1 e2 v2 Hlc Hv Hbrc.
  generalize dependent v1.
  induction Hbrc; intros; eauto.
Qed.

Lemma smallstep_deterministic : forall e e' e'',
  e ---> e' ->
  e ---> e'' ->
  e' = e''.
Proof.
  intros e e' e'' e_steps_to_e' e_steps_to_e''.
  generalize dependent e''.
  (smallstep_cases (induction e_steps_to_e') Case); intros.
  Case "smallstep_app1".
    (smallstep_cases (inversion e_steps_to_e'') SCase); subst.
    SCase "smallstep_app1".
      rewrite IHe_steps_to_e' with (e'':=e1'0); auto.
    SCase "smallstep_app2".
      apply value_doesnt_step in H2.
      unfold smallstep_stuck in H2.
      apply forall_neq__neq_exists in H2; auto.
      assert False as FALSE.
        apply H2. exists e1'. auto.
      inversion FALSE.
    SCase "smallstep_beta".
      assert (is_value_of_exp (abs e0)) as Value. simpl; auto.
      apply value_doesnt_step in Value.
      unfold smallstep_stuck in Value.
      apply forall_neq__neq_exists in Value; auto.
      assert False as FALSE.
        apply Value. exists e1'. auto.
      inversion FALSE.
  Case "smallstep_app2".
    (smallstep_cases (inversion e_steps_to_e'') SCase); subst.
    SCase "smallstep_app1".
      apply value_doesnt_step in H.
      unfold smallstep_stuck in H.
      apply forall_neq__neq_exists in H; auto.
      assert False as FALSE.
        apply H. exists e1'. auto.
      inversion FALSE.
    SCase "smallstep_app2".
      rewrite IHe_steps_to_e' with (e'':=e2'0); auto.
    SCase "smallstep_beta".
      apply value_doesnt_step in H3.
      unfold smallstep_stuck in H3.
      apply forall_neq__neq_exists in H3; auto.
      assert False as FALSE.
        apply H3. exists e2'. auto.
      inversion FALSE.
  Case "smallstep_beta".
    (smallstep_cases (inversion e_steps_to_e'') SCase); subst; auto.
    SCase "smallstep_app1".
      assert (is_value_of_exp (abs e1)) as Value. simpl; auto.
      apply value_doesnt_step in Value.
      unfold smallstep_stuck in Value.
      apply forall_neq__neq_exists in Value; auto.
      assert False as FALSE.
        apply Value. exists e1'. auto.
      inversion FALSE.
    SCase "smallstep_app2".
      apply value_doesnt_step in H.
      unfold smallstep_stuck in H.
      apply forall_neq__neq_exists in H; auto.
      assert False as FALSE.
        apply H. exists e2'. auto.
      inversion FALSE.
Qed.

(** ** [--->*] <-> [===>] *)
Lemma bigstep_converging__smallstep__congruence : forall e e' v,
  e ---> e' ->
  e' ===> v ->
  e ===> v.
Proof.
  intros e e' v e_reduces_to_e' e'_evaluates_to_v.
  generalize dependent v.
  (smallstep_cases (induction e_reduces_to_e') Case); intros; auto.
  Case "smallstep_app1".
    inversion e'_evaluates_to_v; subst.
    apply IHe_reduces_to_e' in H4.
    eapply bigstep_c_app; eauto.
  Case "smallstep_app2".
    inversion e'_evaluates_to_v; subst.
    apply IHe_reduces_to_e' in H6.
    eapply bigstep_c_app; eauto.
  Case "smallstep_beta".
    eapply bigstep_c_app; eauto.
      eapply bigstep_converges_to_value; eauto.
Qed.

Hint Resolve smallstep_converging_regular_1 smallstep_converging_regular_2.

Lemma smallstep_converging__iff__bigstep_converging : forall e v,
  e ===> v <-> (e --->* v /\ is_value_of_exp v).
Proof.
  intros e v.
  split.
  Case "[===>] -> [--->*]".
    intro J.
    (** By induction on [===>], base cases are trivial, and
        the application case is by IH. *)
    (bigstep_converging_cases (induction J) SCase); simpl; eauto.
    SCase "bigstep_c_app".
      split; auto.
        destruct IHJ1 as [IHJ11 IHJ12].
        destruct IHJ2 as [IHJ21 IHJ22].
        destruct IHJ3 as [IHJ31 IHJ32].
        apply smallstep_c__trans with (e':=app (abs e1') e2).
          apply smallstep_c_app_fun; eauto.
          apply smallstep_c__trans with (e':=app (abs e1') v2).
            apply smallstep_c_app_arg; eauto.
            apply smallstep_c_trans with (e':=open_exp_wrt_exp e1' v2); eauto.
  Case "[--->*] --> [===>]".
    intro J. destruct J as [e_to_v v_is_val].
    (** By induction on [--->*] and the facts that 
        1) v ===> v                                [value_is_bigstep_converging]
        2) if e ---> e' /\ e' ===> v then e ===> v [bigstep_converging__smallstep__congruence]
    *)
    (smallstep_converging_cases (induction e_to_v) SCase).
    SCase "smallstep_c_refl".
      apply value_is_bigstep_converging; auto.
    SCase "smallstep_c_trans".
      eapply bigstep_converging__smallstep__congruence; eauto.
Qed.

(** [--->o] <-> [===>o] *)

(** if a term e is big-step divering, then it must reduce to e' that
    is also big-step divering. *)
Lemma bigstep_diverging_inversion : forall e,
  lc_exp e ->
  e ===>o -> 
  exists e', e ---> e' /\ e' ===>o .
Proof.
  intros e e_is_lc.
  (** By induction on e and case analysis on [e ===>o].
      The value and variable cases are trivial, because they cannot diverge.
      The only interesting case is application. *)
  (lc_exp_cases (induction e_is_lc) Case); intros e_co; simpl; 
    try solve [auto | inversion e_co].
  Case "lc_app".
    (** Consider cases from [e1 e2 ===>o].
        1) if e1 diverges, by induction, e1 steps to diverging term e1'.
           We have that e1 e2 ---> e1' e2 ===>o.

        2) if e1 evaluates to v1, but e2 diverges.
           By induction, e2 steps to diverging term e2'.

           Because [--->*] <-> [===>], we have e1 reduces to v1:
           if e1 = v1, we have v1 e2 --=> v1 e2' ===>o
           else e1 ---> e' --->* v1, we have e1 e2 ---> e' e2 ====>o 
                becasue e' ===> v1 by [--->*] <-> [===>] and e2 diverges.

        3) if e1 evaluates to \x.e1', e2 evaluates to v2, but {v2/x}e1' ===>o,
           similar to 2).
    *)     
    (bigstep_diverging_cases (inversion e_co) SCase); subst.
    SCase "bigstep_d_app1".
      apply IHe_is_lc1 in H0.
      destruct H0 as [e1' [e1_to_e1' e1'_co]].
      exists (app e1' e2). split; auto.
    SCase "bigstep_d_app2".
      assert (e2_co:=H3).
      apply IHe_is_lc2 in H3.
      destruct H3 as [e2' [e2_to_e2' e2'_co]].
      apply smallstep_converging__iff__bigstep_converging in H2.
      destruct H2 as [e1_smallsteps_v1 v1_is_val].
      (smallstep_converging_cases (inversion e1_smallsteps_v1) SSCase); subst.
      SSCase "smallstep_c_refl".
        exists (app v1 e2'). split; eauto.
      SSCase "smallstep_c_trans".
        exists (app e' e2). split; eauto.
        apply bigstep_d_app2 with (v1:=v1); auto.
          eapply smallstep_converging__iff__bigstep_converging; auto.
    SCase "bigstep_d_appf".          
      apply smallstep_converging__iff__bigstep_converging in H2.
      destruct H2 as [e1_smallsteps_abs abs_is_val].
      (smallstep_converging_cases (inversion e1_smallsteps_abs) SSCase); subst.
      SSCase "smallstep_c_refl".
        apply smallstep_converging__iff__bigstep_converging in H3.
        destruct H3 as [e2_smallsteps_v2 v2_is_val].
        (smallstep_converging_cases (inversion e2_smallsteps_v2) SSSCase); subst.
        SSSCase "smallstep_c_refl".
          exists (open_exp_wrt_exp e1' v2). split; eauto.
        SSSCase "smallstep_c_trans".
          exists (app (abs e1') e'). split; eauto.
          apply bigstep_d_appf with (e1':=e1')(v2:=v2); auto.
            eapply smallstep_converging__iff__bigstep_converging; auto.
      SSCase "smallstep_c_trans".
        exists (app e' e2). split; eauto.
        apply bigstep_d_appf with (e1':=e1')(v2:=v2); auto.
          eapply smallstep_converging__iff__bigstep_converging; auto.
Qed.

(** if e is small-step diverging, then any intermediate step is also diverging.
*)
Lemma smallstep_diverging__im_step_diverging : forall e e',
  e --->o ->
  e --->* e' ->
  e' --->o.
Proof.
  intros e e' e_cor e_reds_e'.
  induction e_reds_e'; auto.
    apply IHe_reds_e'.
    inversion e_cor; subst.
    apply smallstep_deterministic with (e'':=e'0) in H; subst; auto.
Qed.

Lemma smallstep_diverging__iff__bigstep_diverging : forall e,
  lc_exp e ->
  (e ===>o <-> e--->o).
Proof.
  intros e e_is_lc.
  split.
  Case "[===>o] -> [--->o]".
    (** By CIH and [bigstep_diverging_inversion]. *)
    generalize dependent e.
    cofix Hcoind.
    intros ? ? J.
    apply bigstep_diverging_inversion in J; auto.
    destruct J as [e' [e_to_e' e'_co]].
    apply smallstep_d_intro with (e':=e'); eauto.
  Case "[--->o] --> [===>o]".
    (** By coinduction and case analysis over e. The interesting case (e1 e2) is application,
        because values and variables cannot diverge.

        We case analysis on the function, its argument, and the body by the fact that 
         a term is either diverging or stuck finitely.

        1) if e1 diverges, we conclude by hyp.
      
        2) if e1 --->* v1, but e2 diverges, then

           By [smallstep_diverging__im_step_diverging], we have v1 e2 must diverge.
           so, v1 must be a value, otherwise v1 e2 is stuck.

           this case is finished by hyp.

        3) if e1 --->* v1, e2 --->* v2, then

           by similar reasoning as 2), v1 must be \x.e1', and v2 must be value.
           Now, we know that {v2/x}e1' must diverge, otherwise e1 e2 cannot diverge.

           We conclude the case by hyp.
    *)
    generalize dependent e.
    cofix Hcoind.
    intros ? ? e_cor.
    (exp_cases (destruct e) SCase); 
      try solve [inversion e_cor; subst; inversion H].
    SCase "app".
      inversion e_is_lc; subst.
      destruct (@term_is_diverging_or_finitely_stuck e1 H1) as [e1_diverges | [v1 [e1_converges_to_v1 v1_is_stuck]]].
      SSCase "e1_diverges".
        apply bigstep_d_app1; auto.
      SSCase "e1_is_stuck".
        assert (is_value_of_exp v1) as v1_is_val.
          apply smallstep_diverging__im_step_diverging with (e':=app v1 e2) in e_cor; auto.
            inversion e_cor; subst; auto.
            inversion H; subst; simpl; auto.
              assert False as FALSE.
                unfold smallstep_stuck in v1_is_stuck.
                apply forall_neq__neq_exists in v1_is_stuck; auto.
                apply v1_is_stuck.
                exists e1'. auto.
              inversion FALSE.
            apply smallstep_c_app_fun; auto.                  
        destruct (@term_is_diverging_or_finitely_stuck e2 H2) as [e2_diverges | [v2 [e2_converges_to_v2 v2_is_stuck]]].
        SSSCase "e2_diverges".
          apply bigstep_d_app2 with (v1:=v1); auto.
            eapply smallstep_converging__iff__bigstep_converging; auto.
        SSSCase "e2_is_stuck".
          assert (is_value_of_exp v2) as v2_is_val.
            apply smallstep_diverging__im_step_diverging with (e':=app v1 v2) in e_cor; auto.
              inversion e_cor; subst; auto.
              inversion H; subst; simpl; auto.
                assert False as FALSE.
                  unfold smallstep_stuck in v1_is_stuck.
                  apply forall_neq__neq_exists in v1_is_stuck; auto.
                  apply v1_is_stuck.
                  exists e1'. auto.
                inversion FALSE.

                assert False as FALSE.
                  unfold smallstep_stuck in v2_is_stuck.
                  apply forall_neq__neq_exists in v2_is_stuck; auto.
                  apply v2_is_stuck.
                  exists e2'. auto.
                inversion FALSE.
              apply smallstep_c__trans with (e':=app v1 e2).
                apply smallstep_c_app_fun; auto.                  
                apply smallstep_c_app_arg; eauto.
          assert (exists e1', v1 = abs e1') as v1_is_abs.
            apply smallstep_diverging__im_step_diverging with (e':=app v1 v2) in e_cor; auto.
              inversion e_cor; subst; auto.
              inversion H; subst; simpl; auto.
                assert False as FALSE.
                  unfold smallstep_stuck in v1_is_stuck.
                  apply forall_neq__neq_exists in v1_is_stuck; auto.
                  apply v1_is_stuck.
                  exists e1'. auto.
                inversion FALSE.

                assert False as FALSE.
                  unfold smallstep_stuck in v2_is_stuck.
                  apply forall_neq__neq_exists in v2_is_stuck; auto.
                  apply v2_is_stuck.
                  exists e2'. auto.
                inversion FALSE.
             
                exists e0. auto.
              apply smallstep_c__trans with (e':=app v1 e2).
                apply smallstep_c_app_fun; auto.                  
                apply smallstep_c_app_arg; eauto.
          destruct v1_is_abs as [e1' EQ]; subst.
          assert (lc_exp (open_exp_wrt_exp e1' v2)) as Hlc_open.
            apply lc_body_exp_wrt_exp; eauto.
              assert (lc_exp (abs e1')) as Hlc_abs. eauto.
              inversion Hlc_abs; subst. auto. 
          destruct (@term_is_diverging_or_finitely_stuck (open_exp_wrt_exp e1' v2) Hlc_open) as [e1'v2_diverges | [v [e1'v2_converges_to_v1 e1'v2_is_stuck]]].
          SSSSCase "{v2/x}e1'_diverges".
            apply bigstep_d_appf with (e1':=e1')(v2:=v2); auto.
              eapply smallstep_converging__iff__bigstep_converging; auto.
              eapply smallstep_converging__iff__bigstep_converging; auto.
          SSSSCase "{v2/x}e1'_is_stuck".
            apply smallstep_diverging__im_step_diverging with (e':=v) in e_cor.
  
              assert False as FALSE.
                unfold smallstep_stuck in e1'v2_is_stuck.
                apply forall_neq__neq_exists in e1'v2_is_stuck; auto.
                apply e1'v2_is_stuck.
                inversion e_cor; subst.
                exists e'. auto.
              inversion FALSE.

              apply smallstep_c__trans with (e':=app (abs e1') e2).
                apply smallstep_c_app_fun; auto.                  
                apply smallstep_c__trans with (e':=app (abs e1') v2).
                  apply smallstep_c_app_arg; eauto.          
                  apply smallstep_c_trans with (e':=open_exp_wrt_exp e1' v2); eauto.
Qed.

(** ** [=co=>] -> [-o->*]

    [=co=>] is also smaller than [-o->*].

    When e1 [=co=>] (\x.e1'), {v2/x}e1' [=co=>] v converge, but e2 diverges, 
    such as (\x. 0) omega, e1 e2 =co=> v. This is not intuitive if we think 
    that diverging can prove anything. Actually we can prove (\x. 0) omega
    must [-o->*] to any value.
*)

(** Given e coevaluates to v, then either e is value, or e steps to e' that 
    also coevaluates to v. *)
Lemma coevaluation_inversion : forall e v,
  lc_exp e ->
  e =co=> v ->
  is_value_of_exp e \/ exists e', e ---> e' /\ e' =co=> v.
Proof.
  intros e v e_is_lc.
  (** By induction on e and case analysis on [e =co=> v].
      The value and variable cases are trivial. *)
  generalize dependent v.
  (lc_exp_cases (induction e_is_lc) Case); intros v e_co_v; simpl; 
    try solve [auto | inversion e_co_v].
  Case "lc_app".
    (** From [e1 e2 =co=> v], we have
          e1 =co=> \x.e1'
          e2 =co=> v1
          {v1/x}e1' =co=> v

        By induction hyp,
        if e1 --->e1' =co=> \x.e1', we have e1e2--->e1'e2=co=>v

        if e1 is a value, which must be \x.e1', and e2 ---> e2'=co=>v2
             we have e1e2--->e1e2'=co=>v

        if e1 is \x.e1', e2 is v2, and {v2/x}e1'=co=>v
             we have e1e2 -> {v2/x}e1'=co=>v
    *)     

    inversion e_co_v; subst.
    right.
    assert (e1_co_abs:=H3).
    assert (e2_co_v2:=H4).
    apply IHe_is_lc1 in H3.
    apply IHe_is_lc2 in H4. 
    rename e1' into e12.
    destruct H3 as [e1_is_val | [e1' [e1_to_e1' e1'_co_abs]]].
    SCase "e1_is_val".
      inversion e1_co_abs; subst; try solve [simpl in e1_is_val; inversion e1_is_val].
      destruct H4 as [e2_is_val | [e2' [e2_to_e2' e2'_co_v2]]].
      SSCase "e2_is_val".
        exists (open_exp_wrt_exp e12 e2).
        split; auto.
          inversion e2_co_v2; subst; try solve [simpl in e2_is_val; inversion e2_is_val | auto].
      SSCase "e2_steps".
        exists (app (abs e12) e2').
        split; eauto.
    SCase "e1_steps".
      exists (app e1' e2).
      split; eauto.
Qed.

Lemma coevaluation__implies__coreduction : forall e v,
  lc_exp e ->
  e =co=> v -> 
  e -o->* v.
Proof.
  (** By coinduction, then by [coevaluation_inversion], we know that 
      either e is value, or e--->e'=co=>v. The earlier case is trivial,
      the latter case is by coind hyp.
  *)
  cofix Hcoind.
  intros e v e_is_lc e_co_v.
  apply coevaluation_inversion with (v:=v) in e_is_lc; auto.
  destruct e_is_lc as [e_is_value | [e' [e_to_e' e'_co_v]]]; auto.
  Case "e_is_value".
    (exp_cases (destruct e) SCase); 
      try solve [simpl in e_is_value; inversion e_is_value | 
                 clear Hcoind; inversion e_co_v; auto].
  Case "e_steps".
    apply smallstep_co_trans with (e':=e'); eauto.
Qed.

(** * Notwithstanding the negative results of 
      ~ ([===>o]  ->  [=co=>]) and ~ ([-o->*]  ->  [=co=>]),
      there exists a class of terms for which [=co=>] correctly
      captures both terminating and diverging evaluations: terms that
      are in continuation-passing style (CPS). CPS terms are defined 
      by the following grammar:

        a ::= x | c | \x.b
        b ::= a | b a

      Less formally, CPS terms are built from atoms using multiple
      applications in tail-call position. A distingushing feature of 
      these terms is that function arguments are always values, such that 
      the above counter-exampled don't work. We can prove that [=co=>]
      equals to the union of [===>o] and [===>], and is also equivalent
      to [-o->*]. But I did not prove this result in Coq.     
*)
