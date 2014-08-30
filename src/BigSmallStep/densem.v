(** Denotational semantics is an alternative way to characterize divergent
    and convergent terms. This file develops a simple denotational semantics
    for CBV lambda-calculus and proves that it captures the same notations of
    convergence and divergence as the big-step operational semantics.
*)

Require Export Coq.Program.Equality.
Require Export lang_inf.
Require Export lang_more.
Require Export soundness.
Require Export Coq.Logic.Classical_Prop.
Require Import Omega.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Max.

Fixpoint exp_to_object (e:exp) : option object :=
match e with
| const => Some object_const
| abs e' => Some (object_abs e')
| _ => None
end.

Lemma value_to_some_object : forall v o,
  exp_to_object v = Some o -> is_value_of_exp v.
Proof.
  intros v o EQ.
  (exp_cases (destruct v) Case); simpl in EQ; inversion EQ; simpl; auto.
Qed.

(** Objects in the denotational domain include :
      object_const, object_abs :  normal termination with const or abs as final value;
      object_err : abrupt termination on a run-time error, such as encountering a free variable
                   or an application of a constant;
      object_bot : the computation cannot complete within n recursive steps.

    Objects Order:
      object_bot is lesseq than any object, and any object is lesseq than itself.

    First, we define the computation C n e of a term e at maximal recursion
    depth n by recursion over n, as follow:

    Notice that n is the recursive steps, but not the real computation steps.
*)

Fixpoint C (n:nat) (e:exp) : object :=
match (n, e) with
| (0, _) => object_bot            (* no computation can be done by 0 step *)
| (S n', const) => object_const   (* reach normal forms *)
| (S n', abs e') => object_abs e' (* reach normal forms *)
| (S n', app e1 e2) =>            (* application case is monadic *)
  match (C n' e1) with
  | object_const =>
     match (C n' e2) with
     | object_const => object_err                  (* const cannot apply to arguments *)
     | object_abs e2' => object_err                (* const cannot apply to arguments *)
     | object_bot => object_bot                    (* propagate uncompleted computation *)
     | object_err => object_err                    (* propagate errors *)
     end
  | object_abs e1' =>
     match (C n' e2) with
     | object_const =>
         C n' (open_exp_wrt_exp e1' const)         (* compute fuction body *)
     | object_abs e2' =>
         C n' (open_exp_wrt_exp e1' (abs e2'))     (* compute fuction body *)
     | object_bot => object_bot                    (* propagate uncompleted computation *)
     | object_err => object_err                    (* propagate errors *)
     end
  | object_bot => object_bot      (* propagate uncompleted computation *)
  | object_err => object_err      (* propagate errors *)
  end
| (S n', _) => object_err         (* stuck at variables *)
end.

(** We say that a term e executes with result o, or in other terms that o
    is the denotation of e, and we write D e o, if C n e = o for almost all n:
*)

Definition D e o := exists p, forall n, n >= p -> C n e = o.

(** Intuitively, if e is converging, then there must exists a p, s.t. C p e <> object_bot.
     If C is monotone, then with any n recursion depth that is not less than p,
     C n e should equal to the same object, namely D e (C p e);

    If e is diverging, with any n recursion depth, C n e should equal to object_bot.
    This is the case that D e object_bot holds.

    In the following, we are verifying this intuition. First, some trivial facts:
*)

(** const always computes to const with non-zero step. *)
Lemma C_const_is_const : forall n,
  n > 0 ->
  C n const = object_const.
Proof.
  induction n; simpl; auto.
    intro J. contradict J; omega.
Qed.

(** abs always computes to abs with non-zero step. *)
Lemma C_abs_is_abs : forall n e,
  n > 0 ->
  C n (abs e) = object_abs e.
Proof.
  induction n; simpl; auto.
    intros e J. contradict J; omega.
Qed.

(** var_f always computes to err with non-zero step. *)
Lemma C_varf_is_err : forall n x,
  n > 0 ->
  C n (var_f x) = object_err.
Proof.
  induction n; simpl; auto.
    intros x J. contradict J; omega.
Qed.

(** var_b always computes to err with non-zero step. *)
Lemma C_varb_is_err : forall n m,
  n > 0 ->
  C n (var_b m) = object_err.
Proof.
  induction n; simpl; auto.
    intros m J. contradict J; omega.
Qed.

(** regularity *)

Lemma lc_abs__lc_object_abs : forall e,
  lc_exp (abs e) ->
  lc_object (object_abs e).
Proof.
  intros e e_is_lc.
  apply lc_object_abs.
  inversion e_is_lc; auto.
Qed.

Lemma lc_object_abs__lc_abs : forall e,
  lc_object (object_abs e) ->
  lc_exp (abs e).
Proof.
  intros e e_is_lc.
  apply lc_abs.
  inversion e_is_lc; auto.
Qed.

Hint Resolve lc_abs__lc_object_abs lc_object_abs__lc_abs.

Lemma C_regular : forall n e,
  lc_exp e ->
  lc_object (C n e).
Proof.
  induction n; intros e e_is_lc; simpl; eauto.
  (exp_cases (destruct e) Case); auto.
  Case "app".
    inversion e_is_lc; subst.
    remember (C n e1) as C1.
    destruct C1; subst; auto.
      remember (C n e2) as C2.
      destruct C2; subst; auto.

      remember (C n e2) as C2.
      destruct C2; subst; auto.
        apply IHn; auto.
          apply lc_body_exp_wrt_exp; eauto.
          apply IHn in H1.
          rewrite <- HeqC1 in H1.
          inversion H1; subst. auto.

        apply IHn in H1.
        rewrite <- HeqC1 in H1.
        apply IHn in H2.
        rewrite <- HeqC2 in H2.
        apply IHn; auto.
          apply lc_body_exp_wrt_exp; eauto.
          inversion H1; subst. auto.
Qed.

Hint Resolve C_regular.

Lemma uniq_denotation : forall e o1 o2,
  D e o1 ->
  D e o2 ->
  o1 = o2.
Proof.
  intros e o1 o2 o1_denotes_e o2_denotes_e.
  destruct o1_denotes_e as [p1 o1_denotes_e].
  destruct o2_denotes_e as [p2 o2_denotes_e].
  rewrite <- (@o1_denotes_e (max p1 p2)); auto.
  rewrite <- (@o2_denotes_e (max p1 p2)); auto.
    assert (J:=@le_max_r p1 p2). auto.
    assert (J:=@le_max_l p1 p2). auto.
Qed.

(** We then check that C is monotone w.r.t objects order. *)

Notation " o <<= o' " := (objects_order o o') (at level 50, left associativity).

Tactic Notation "object_cases" tactic(first) tactic(c) :=
  first;
  [ c "object_bot" | c "object_err" | c "object_const" | c "object_abs" ].

(** if C returns values or errors by smaller steps, it returns the same
    resule by bigger steps. *)
Lemma C_preserves_normalforms : forall m n e,
  n <= m ->
  (C n e = object_const -> C m e = object_const) /\
  (forall e', C n e = object_abs e' -> C m e = object_abs e') /\
  (C n e = object_err -> C m e = object_err).
Proof.
  (** By induction over m.

      The base case is trivial, because n cannot be 0,
      otherwise C n e must be bottom.

      At the inductive case, the proofs go by case analysis on e. The
      interesting case is application e1 e2, where we do case analysis
      over (C n e1) and (C n e2), and conclude by induction hyp. *)
  induction m; intros n e n_lesseq_m; simpl; auto.
  Case "m=0". (* Contradictory case *)
    assert (n = 0) as n_is_0. omega.
    subst.
    split. intro Cn_const. simpl in Cn_const. inversion Cn_const.
    split. intros e' Cn_abs. simpl in Cn_abs. inversion Cn_abs.
           intro Cn_err. simpl in Cn_err. inversion Cn_err.
  Case "m=S m".
    destruct n.
    SCase "n=0".  (* Contradictory case *)
      split. intro Cn_const. simpl in Cn_const. inversion Cn_const.
      split. intros e' Cn_abs. simpl in Cn_abs. inversion Cn_abs.
             intro Cn_err. simpl in Cn_err. inversion Cn_err.
    SCase "n>0".
      rename n_lesseq_m into Sn_lesseq_Sm.
      assert (n <= m) as n_lesseq_m. omega.

      split.
      (** object_const preverses *)
      intro Cn_const. simpl in Cn_const.
      (exp_cases (destruct e) SSCase); auto.
      SSCase "app".
        remember (C n e1) as Cn1.
        (object_cases (destruct Cn1) SSSCase); try solve [inversion Cn_const].
        SSSCase "object_const".
          symmetry in HeqCn1.
          apply IHm in HeqCn1; auto.
          rewrite HeqCn1.

          remember (C n e2) as Cn2.
          (object_cases (destruct Cn2) SSSSCase); try solve [inversion Cn_const].

        SSSCase "object_abs".
          symmetry in HeqCn1.
          apply IHm in HeqCn1; auto.
          rewrite HeqCn1.

          remember (C n e2) as Cn2.
          (object_cases (destruct Cn2) SSSSCase); try solve [inversion Cn_const].
          SSSSCase "object_const".
            symmetry in HeqCn2.
            apply IHm in HeqCn2; auto.
            rewrite HeqCn2.
            apply IHm in Cn_const; auto.

          SSSSCase "object_abs".
            symmetry in HeqCn2.
            apply IHm in HeqCn2; auto.
            rewrite HeqCn2.
            apply IHm in Cn_const; auto.

      split.
      (** object_abs preverses *)
      intros e' Cn_abs. simpl in Cn_abs.
      (exp_cases (destruct e) SSCase); auto.
      SSCase "app".
        remember (C n e1) as Cn1.
        (object_cases (destruct Cn1) SSSCase); try solve [inversion Cn_abs].
        SSSCase "object_const".
          symmetry in HeqCn1.
          apply IHm in HeqCn1; auto.
          rewrite HeqCn1.

          remember (C n e2) as Cn2.
          (object_cases (destruct Cn2) SSSSCase); try solve [inversion Cn_abs].

        SSSCase "object_abs".
          symmetry in HeqCn1.
          apply IHm in HeqCn1; auto.
          rewrite HeqCn1.

          remember (C n e2) as Cn2.
          (object_cases (destruct Cn2) SSSSCase); try solve [inversion Cn_abs].
          SSSSCase "object_const".
            symmetry in HeqCn2.
            apply IHm in HeqCn2; auto.
            rewrite HeqCn2.
            apply IHm in Cn_abs; auto.

          SSSSCase "object_abs".
            symmetry in HeqCn2.
            apply IHm in HeqCn2; auto.
            rewrite HeqCn2.
            apply IHm in Cn_abs; auto.

      (** object_err preverses *)
      intros Cn_err. simpl in Cn_err.
      (exp_cases (destruct e) SSCase); auto.
      SSCase "app".
        remember (C n e1) as Cn1.
        (object_cases (destruct Cn1) SSSCase); try solve [inversion Cn_err].
        SSSCase "object_err".
          symmetry in HeqCn1.
          apply IHm in HeqCn1; auto.
          rewrite HeqCn1. auto.

        SSSCase "object_const".
          symmetry in HeqCn1.
          apply IHm in HeqCn1; auto.
          rewrite HeqCn1. auto.

          remember (C n e2) as Cn2.
          (object_cases (destruct Cn2) SSSSCase); try solve [inversion Cn_err].
          SSSSCase "object_err".
            symmetry in HeqCn2.
            apply IHm in HeqCn2; auto.
            rewrite HeqCn2. auto.

          SSSSCase "object_const".
            symmetry in HeqCn2.
            apply IHm in HeqCn2; auto.
            rewrite HeqCn2. auto.

          SSSSCase "object_abs".
            symmetry in HeqCn2.
            apply IHm in HeqCn2; auto.
            rewrite HeqCn2. auto.

        SSSCase "object_abs".
          symmetry in HeqCn1.
          apply IHm in HeqCn1; auto.
          rewrite HeqCn1.

          remember (C n e2) as Cn2.
          (object_cases (destruct Cn2) SSSSCase); try solve [inversion Cn_err].
          SSSSCase "object_err".
            symmetry in HeqCn2.
            apply IHm in HeqCn2; auto.
            rewrite HeqCn2. auto.

          SSSSCase "object_const".
            symmetry in HeqCn2.
            apply IHm in HeqCn2; auto.
            rewrite HeqCn2.
            apply IHm in Cn_err; auto.

          SSSSCase "object_abs".
            symmetry in HeqCn2.
            apply IHm in HeqCn2; auto.
            rewrite HeqCn2.
            apply IHm in Cn_err; auto.
Qed.

Lemma C_preserves_err : forall m n e,
  n <= m ->
  C n e = object_err ->
  C m e = object_err.
Proof.
  intros m n e n_lesseq_m.
  eapply C_preserves_normalforms; eauto.
Qed.

Lemma C_preserves_const : forall m n e,
  n <= m ->
  C n e = object_const ->
  C m e = object_const.
Proof.
  intros m n e n_lesseq_m.
  eapply C_preserves_normalforms; eauto.
Qed.

Lemma C_preserves_abs : forall m n e,
  n <= m ->
  forall e',
  C n e = object_abs e' ->
  C m e = object_abs e'.
Proof.
  intros m n e n_lesseq_m.
  eapply C_preserves_normalforms; eauto.
Qed.

(** Some facts when computing applications by [C_preserves_normalforms]. *)

Lemma err_applies_arguments_is_err : forall m n e1 e2,
  C n e1 = object_err ->
  n < m ->
  C m (app e1 e2) = object_err.
Proof.
  induction m; intros n e1 e2 Cne1_err n_less_m.
    contradict n_less_m; omega.

    simpl.
    apply C_preserves_err with (m:=m) in Cne1_err; try solve [omega].
    rewrite Cne1_err. auto.
Qed.

Lemma const_applies_nonbot_is_err : forall m n e1 e2,
  C n e1 = object_const ->
  C n e2 <> object_bot ->
  n < m ->
  C m (app e1 e2) = object_err.
Proof.
  induction m; intros n e1 e2 Cne1_const Cne2_nbot n_less_m.
    contradict n_less_m; omega.

    simpl.
    apply C_preserves_const with (m:=m) in Cne1_const; try solve [omega].
    rewrite Cne1_const.
    remember (C n e2) as Cn2.
    (object_cases (destruct Cn2) Case).
    Case "object_bot".
      contradict Cne2_nbot; auto.
    Case "object_err".
      symmetry in HeqCn2.
      apply C_preserves_err with (m:=m) in HeqCn2; try solve [omega].
      rewrite HeqCn2. auto.
    Case "object_const".
      symmetry in HeqCn2.
      apply C_preserves_const with (m:=m) in HeqCn2; try solve [omega].
      rewrite HeqCn2. auto.
    Case "object_abs".
      symmetry in HeqCn2.
      apply C_preserves_abs with (m:=m) in HeqCn2; try solve [omega].
      rewrite HeqCn2. auto.
Qed.

Lemma abs_applies_err_is_err : forall m n e1 e2 e1',
  C n e1 = object_abs e1' ->
  C n e2 = object_err ->
  n < m ->
  C m (app e1 e2) = object_err.
Proof.
  induction m; intros n e1 e2 e1' Cne1_abs Cne2_err n_less_m.
    contradict n_less_m; omega.

    simpl.
    apply C_preserves_abs with (m:=m) in Cne1_abs; try solve [omega].
    apply C_preserves_err with (m:=m) in Cne2_err; try solve [omega].
    rewrite Cne1_abs. rewrite Cne2_err. auto.
Qed.

Lemma abs_applies_const_is_reduction : forall m n e1 e2 e1',
  C n e1 = object_abs e1' ->
  C n e2 = object_const ->
  n < m ->
  C m (app e1 e2) = C (m-1) (open_exp_wrt_exp e1' const).
Proof.
  induction m; intros n e1 e2 e1' Cne1_abs Cne2_const n_less_m.
    contradict n_less_m; omega.

    assert (S m - 1 = m) as EQ. omega.
    rewrite EQ. simpl.
    apply C_preserves_abs with (m:=m) in Cne1_abs; try solve [omega].
    apply C_preserves_const with (m:=m) in Cne2_const; try solve [omega].
    rewrite Cne1_abs. rewrite Cne2_const. auto.
Qed.

Lemma abs_applies_abs_is_reduction : forall m n e1 e2 e1' e2',
  C n e1 = object_abs e1' ->
  C n e2 = object_abs e2' ->
  n < m ->
  C m (app e1 e2) = C (m-1) (open_exp_wrt_exp e1' (abs e2')).
Proof.
  induction m; intros n e1 e2 e1' e2' Cne1_abs Cne2_abs n_less_m.
    contradict n_less_m; omega.

    assert (S m - 1 = m) as EQ. omega.
    rewrite EQ. simpl.
    apply C_preserves_abs with (m:=m) in Cne1_abs; try solve [omega].
    apply C_preserves_abs with (m:=m) in Cne2_abs; try solve [omega].
    rewrite Cne1_abs. rewrite Cne2_abs. auto.
Qed.

Lemma C_is_monotone : forall n m e,
  lc_exp e ->
  n <= m ->
  C n e <<= C m e.
Proof.
  (** By induction over n and case analysis over e. At the interesting
      case application, we conclude by [err_applies_arguments_is_err],
      [const_applies_arguments_is_err], [abs_applies_err_is_err],
      [abs_applies_const_is_reduction], and
      [abs_applies_abs_is_reduction]. *)
  induction n; intros m e e_is_lc n_lesseq_m; simpl; auto.
  (exp_cases (destruct e) Case); simpl; auto.
  Case "const".
    rewrite C_const_is_const; try solve [auto | omega].
  Case "var_b".
    rewrite C_varb_is_err; try solve [auto | omega].
  Case "var_f".
    rewrite C_varf_is_err; try solve [auto | omega].
  Case "abs".
    rewrite C_abs_is_abs; try solve [auto | omega].
  Case "app".
    rename n_lesseq_m into Sn_lesseq_m.
    assert (n < m) as n_lt_m. omega.
    remember (C n e1) as C1.
    (object_cases (destruct C1) SCase); subst; simpl; auto.
    SCase "object_err".
      symmetry in HeqC1.
      apply err_applies_arguments_is_err with (m:=m)(e2:=e2) in HeqC1; auto.
      rewrite HeqC1. auto.
    SCase "object_const".
      symmetry in HeqC1.
      remember (C n e2) as C2.
      (object_cases (destruct C2) SSCase); subst; simpl; auto.
      SSCase "object_err".
        symmetry in HeqC2.
        apply const_applies_nonbot_is_err with (e1:=e1)(e2:=e2) in n_lt_m; auto.
          rewrite n_lt_m. auto.
          rewrite HeqC2. intro J. inversion J.
      SSCase "object_const".
        symmetry in HeqC2.
        apply const_applies_nonbot_is_err with (e1:=e1)(e2:=e2) in n_lt_m; auto.
          rewrite n_lt_m. auto.
          rewrite HeqC2. intro J. inversion J.
      SSCase "object_abs".
        symmetry in HeqC2.
        apply const_applies_nonbot_is_err with (e1:=e1)(e2:=e2) in n_lt_m; auto.
          rewrite n_lt_m. auto.
          rewrite HeqC2. intro J. inversion J.
    SCase "object_abs".
      symmetry in HeqC1.
      assert (lc_exp (abs e)) as lc_abs1.
        apply lc_object_abs__lc_abs.
        rewrite <- HeqC1.
        inversion e_is_lc; subst. auto.
      remember (C n e2) as C2.
      (object_cases (destruct C2) SSCase); subst; simpl; auto.
      SSCase "object_err".
        symmetry in HeqC2.
        apply abs_applies_err_is_err with (m:=m)(e2:=e2) in HeqC1; auto.
        rewrite HeqC1. auto.
      SSCase "object_const".
        symmetry in HeqC2.
        apply abs_applies_const_is_reduction with (m:=m)(e2:=e2) in HeqC1; auto.
        rewrite HeqC1.
        apply IHn; try solve [auto | omega].
          inversion lc_abs1; subst.
          apply lc_body_exp_wrt_exp; eauto.
      SSCase "object_abs".
        symmetry in HeqC2.
        assert (lc_exp (abs e0)) as lc_abs2.
          apply lc_object_abs__lc_abs.
          rewrite <- HeqC2.
          inversion e_is_lc; subst. auto.
        apply abs_applies_abs_is_reduction with (m:=m)(e2:=e2)(e2':=e0) in HeqC1; auto.
        rewrite HeqC1.
        apply IHn; try solve [auto | omega].
          inversion lc_abs1; subst.
          apply lc_body_exp_wrt_exp; eauto.
Qed.

(** Since C is monotone, the following properties hold: *)

Lemma o_denotes_e__implies__e_computes_to_o_or_bot : forall e o n,
  lc_exp e ->
  D e o ->
  C n e = object_bot \/ C n e = o.
Proof.
  intros e o n e_is_lc o_denotes_e.
  destruct o_denotes_e as [p o_denotes_e].
  (** By case analyis over the range of n and p
      If n >= p, by D;
      otherwise by D, we have C p e = o
        then we do case analysis over C n e
        if it is bot, we are done;
        otherwise, by [C_is_monotone],
           C n e <<= C p e
         we know C n e must be o.
  *)
  destruct (@le_lt_dec p n) as [p_le_n | p_lt_n].
  Case "p <= n".
    right. apply o_denotes_e; auto.
  Case "p > n".
    assert (n<=p) as n_le_p. omega.
    apply C_is_monotone with (e:=e) in n_le_p; auto.
    assert (p>=p) as p_ge_p. omega.
    apply o_denotes_e in p_ge_p.
    inversion n_le_p; subst; auto.
Qed.

Lemma e_computes_to_o_finitely__implies__o_denotes_e : forall e o p,
  lc_exp e ->
  o <> object_bot ->
  C p e = o ->
  D e o.
Proof.
  (** By [C_is_monotone], with steps larger than p, e must compute to
      a result o' higher than o. If o is not bot, o' must be o. This
      is exactly the definition of D.
  *)
  intros e o p e_is_lc o_isnt_bot e_computes_to_o.
  exists p.
  intros n n_ge_p.
  apply C_is_monotone with (n:=p)(m:=n) in e_is_lc; auto.
  rewrite e_computes_to_o in e_is_lc.
  inversion e_is_lc; subst; auto.
    rewrite H0 in o_isnt_bot.
    contradict o_isnt_bot; auto.
Qed.

Lemma bot_denotes_e__iff__e_diverges : forall e,
  lc_exp e ->
  (D e object_bot <-> forall n, C n e = object_bot).
Proof.
  intros e e_is_lc.
  split.
  Case "D e object_bot -> forall n, C n e = object_bot".
    intros bot_denotes_e n.
    apply o_denotes_e__implies__e_computes_to_o_or_bot with (n:=n) in bot_denotes_e; auto.
    destruct bot_denotes_e; auto.
  Case "forall n, C n e = object_bot -> D e object_bot".
    intros e_diverges.
    exists 0. intros; auto.
Qed.

(** It follows that every term has one and exactly one denotation. *)

Lemma denotation_exists : forall e, lc_exp e -> exists o, D e o.
Proof.
  intros e e_is_lc.
  (** By PEM, either forall n, C n e = bot or exists n, C n e <> bot.
      The earlier case is by [bot_denotes_e__iff__e_diverges],
      the latter case is by [e_computes_to_o_finitely__implies__o_denotes_e].
  *)
  destruct (@classic (forall n, C n e = object_bot)) as [e_diverges | e_converges].
  Case "e diverges".
    exists object_bot. eapply bot_denotes_e__iff__e_diverges; eauto.
  Case "e converges".
    destruct (@neq_forall__exists_neq nat (fun n => C n e = object_bot)) as [J _].
    apply J in e_converges. clear J.
    destruct e_converges as [n e_converges].
    exists (C n e).
    apply e_computes_to_o_finitely__implies__o_denotes_e with (p:=n); auto.
Qed.

(** We now relate this denotational semantics with the big-step operational semantics *)

Lemma bigstep_converging_regular_1 : forall e v,
  e ===> v -> lc_exp e.
Proof.
  intros e v H.
  induction H; auto.
Qed.

Lemma bigstep_converging_regular_2 : forall e v,
  e ===> v -> lc_exp v.
Proof.
  intros e v H.
  induction H; auto.
Qed.

Hint Resolve bigstep_converging_regular_1 bigstep_converging_regular_2.

(** If there exists p s.t. C p e = v, then e ===> v. *)
Lemma finite_compuations__implies__evaluations : forall p e v o,
  lc_exp e ->
  exp_to_object v = Some o ->
  C p e = o ->
  e ===> v.
Proof.
  (** By induction on p, and case analysis over e and the results of
      the recursive computations. Values and variables are trivial.

      If e = e1 e2, hypothesis leads to C (p-1) e1 = \x. e1',
      C (p-1) e2 = v2, and C (p-1) ({v2/x}e1') = v. The result
      follows these hyps and constructors.
  *)
  induction p; intros e v o e_is_lc EQ J; simpl in J; subst.
  Case "p=0".
    destruct v; simpl in EQ; inversion EQ.
  Case "S p>0".
    (exp_cases (destruct e) SCase); simpl in *.
    SCase "const".
      destruct v; simpl in EQ; inversion EQ; auto.
    SCase "var_b".
      destruct v; simpl in EQ; inversion EQ; auto.
    SCase "var_f".
      destruct v; simpl in EQ; inversion EQ; auto.
    SCase "abs".
      destruct v; simpl in EQ; inversion EQ; auto.
    SCase "app".
      inversion e_is_lc; subst.
      remember (C p e1) as Cp1.
      (object_cases (destruct Cp1) SSCase); try solve [destruct v; simpl in EQ; inversion EQ; auto].
      SSCase "object_const".
        remember (C p e2) as Cp2.
        destruct Cp2; try solve [destruct v; simpl in EQ; inversion EQ; auto].
      SSCase "object_abs".
        remember (C p e2) as Cp2.
        (object_cases (destruct Cp2) SSSCase); try solve [destruct v; simpl in EQ; inversion EQ; auto].
        SSSCase "object_const".
          assert (is_value_of_exp v) as v_is_val.
            apply value_to_some_object in EQ; auto.
          symmetry in HeqCp1.
          apply IHp with (v:=abs e) in HeqCp1; simpl; auto.

          symmetry in HeqCp2.
          apply IHp with (v:=const) in HeqCp2; simpl; auto.

          assert (lc_exp (open_exp_wrt_exp e const)) as econst_is_lc.
            apply lc_body_exp_wrt_exp; eauto.
              apply bigstep_converging_regular_2 in HeqCp1; auto.
              inversion HeqCp1; auto.

          apply bigstep_c_app with (e1':=e)(v2:=const); simpl; eauto.
        SSSCase "object_abs".
          assert (is_value_of_exp v) as v_is_val.
            apply value_to_some_object in EQ; auto.
          symmetry in HeqCp1.
          apply IHp with (v:=abs e) in HeqCp1; simpl; auto.

          symmetry in HeqCp2.
          apply IHp with (v:=abs e0) in HeqCp2; simpl; auto.

          assert (lc_exp (open_exp_wrt_exp e (abs e0))) as eabs_is_lc.
            apply bigstep_converging_regular_2 in HeqCp2; auto.
              apply lc_body_exp_wrt_exp; auto.
                apply bigstep_converging_regular_2 in HeqCp1; auto.
                inversion HeqCp1; auto.

          apply bigstep_c_app with (e1':=e)(v2:=abs e0); simpl; eauto.
Qed.

(** [===>] and D are consistent at terminating cases. *)
Lemma evaluations__iff__value_denotations : forall e v,
  lc_exp e ->
  (e ===> v <-> (exists o, exp_to_object v = Some o /\ D e o)).
Proof.
  intros e v e_is_lc.
  split.
  Case "e ===> v -> (exists o, exp_to_object v = Some o /\ D e o)".
    (**  We proceed by induction over [e===>v] and exhibit a p such that C p e = v.
         The cases where e is a value are trival, since C 1 e = v in these cases.
         For the application case e = e1 e2, the induction hyp leads to
         C p1 e1 = \x. e1',  C p2 e2 = v2 and C p3 ({v2/x}e1') = v for some p1 p2 p3.
         Taking p = 1 + max p1 (max p2 p3), we have C p e = v by definition and
         monotonicity of C, and the result follows.
    *)
    intro e_evaluates_to_v.
    (bigstep_converging_cases (induction e_evaluates_to_v) SCase); simpl in *.
    SCase "bigstep_c_const".
      exists object_const. split; auto.
      exists 1. intros n n_ge_1. apply C_const_is_const; auto.
    SCase "bigstep_c_abs".
      exists (object_abs e). split; auto.
      exists 1. intros n n_ge_1. apply C_abs_is_abs; auto.
    SCase "bigstep_c_app".
      inversion e_is_lc; subst.
      destruct (@IHe_evaluates_to_v1) as [o1 [EQ1 [p1 abs1_denotes_e1]]]; auto.
      inversion EQ1; subst. clear EQ1.
      assert (lc_exp (open_exp_wrt_exp e1' const)) as e1'const_is_lc.
        apply lc_body_exp_wrt_exp; eauto.
          apply bigstep_converging_regular_2 in e_evaluates_to_v1; auto.
          inversion e_evaluates_to_v1; auto.
      destruct v2; try solve [simpl in H0; inversion H0]; simpl in *.
      SSCase "v2 is const".
        destruct (@IHe_evaluates_to_v2) as [o2 [EQ2 [p2 const_denotes_e2]]]; auto.
        inversion EQ2; subst. clear EQ2.
        destruct v; try solve [simpl in H; inversion H]; simpl in *.
        SSSCase "v is const".
          destruct (@IHe_evaluates_to_v3) as [o3 [EQ3 [p3 const_denotes_e3]]]; auto.
          inversion EQ3; subst. clear EQ3.
          exists object_const. split; auto.
          exists (max p1 (max p2 p3) + 1).
          intros n n_ge_max.
          assert (C n (app e1 e2) = C (n-1) (open_exp_wrt_exp e1' const)) as EQ.
            apply abs_applies_const_is_reduction with (n:=max p1 (max p2 p3)); auto.
              apply abs1_denotes_e1; auto.
                assert (J:=@le_max_l p1 (max p2 p3)). auto.
              apply const_denotes_e2; auto.
                clear.
                assert (J:=@le_max_r p1 (max p2 p3)).
                assert (J':=@le_max_l p2 p3).
                omega.
              omega.
          rewrite EQ.
          apply const_denotes_e3; auto.
            clear - n_ge_max.
            assert (J:=@le_max_r p1 (max p2 p3)).
            assert (J':=@le_max_r p2 p3).
            omega.
        SSSCase "v is abs".
          destruct (@IHe_evaluates_to_v3) as [o3 [EQ3 [p3 abs_denotes_e3]]]; auto.
          inversion EQ3; subst. clear EQ3.
          exists (object_abs v). split; auto.
          exists (max p1 (max p2 p3) + 1).
          intros n n_ge_max.
          assert (C n (app e1 e2) = C (n-1) (open_exp_wrt_exp e1' const)) as EQ.
            apply abs_applies_const_is_reduction with (n:=max p1 (max p2 p3)); auto.
              apply abs1_denotes_e1; auto.
                assert (J:=@le_max_l p1 (max p2 p3)). auto.
              apply const_denotes_e2; auto.
                clear.
                assert (J:=@le_max_r p1 (max p2 p3)).
                assert (J':=@le_max_l p2 p3).
                omega.
              omega.
          rewrite EQ.
          apply abs_denotes_e3; auto.
            clear - n_ge_max.
            assert (J:=@le_max_r p1 (max p2 p3)).
            assert (J':=@le_max_r p2 p3).
            omega.
      SSCase "v2 is abs".
        destruct (@IHe_evaluates_to_v2) as [o2 [EQ2 [p2 abs2_denotes_e2]]]; auto.
        inversion EQ2; subst. clear EQ2.
        assert (lc_exp (open_exp_wrt_exp e1' (abs v2))) as e1'abs_is_lc.
          apply lc_body_exp_wrt_exp; eauto.
            apply bigstep_converging_regular_2 in e_evaluates_to_v1; auto.
            inversion e_evaluates_to_v1; auto.
        destruct v; try solve [simpl in H; inversion H]; simpl in *.
        SSSCase "v is const".
          destruct (@IHe_evaluates_to_v3) as [o3 [EQ3 [p3 const_denotes_e3]]]; auto.
          inversion EQ3; subst. clear EQ3.
          exists object_const. split; auto.
          exists (max p1 (max p2 p3) + 1).
          intros n n_ge_max.
          assert (C n (app e1 e2) = C (n-1) (open_exp_wrt_exp e1' (abs v2))) as EQ.
            apply abs_applies_abs_is_reduction with (n:=max p1 (max p2 p3)); auto.
              apply abs1_denotes_e1; auto.
                assert (J:=@le_max_l p1 (max p2 p3)). auto.
              apply abs2_denotes_e2; auto.
                clear.
                assert (J:=@le_max_r p1 (max p2 p3)).
                assert (J':=@le_max_l p2 p3).
                omega.
              omega.
          rewrite EQ.
          apply const_denotes_e3; auto.
            clear - n_ge_max.
            assert (J:=@le_max_r p1 (max p2 p3)).
            assert (J':=@le_max_r p2 p3).
            omega.
        SSSCase "v is abs".
          destruct (@IHe_evaluates_to_v3) as [o3 [EQ3 [p3 abs_denotes_e3]]]; auto.
          inversion EQ3; subst. clear EQ3.
          exists (object_abs v). split; auto.
          exists (max p1 (max p2 p3) + 1).
          intros n n_ge_max.
          assert (C n (app e1 e2) = C (n-1) (open_exp_wrt_exp e1' (abs v2))) as EQ.
            apply abs_applies_abs_is_reduction with (n:=max p1 (max p2 p3)); auto.
              apply abs1_denotes_e1; auto.
                assert (J:=@le_max_l p1 (max p2 p3)). auto.
              apply abs2_denotes_e2; auto.
                clear.
                assert (J:=@le_max_r p1 (max p2 p3)).
                assert (J':=@le_max_l p2 p3).
                omega.
              omega.
          rewrite EQ.
          apply abs_denotes_e3; auto.
            clear - n_ge_max.
            assert (J:=@le_max_r p1 (max p2 p3)).
            assert (J':=@le_max_r p2 p3).
            omega.
  Case "(exists o, exp_to_object v = Some o /\ D e o) -> e ===> v".
    intros J. destruct J as [o [EQ [p o_denotes_e]]].
    assert (p >= p) as pEQ. omega.
    assert (J:=@o_denotes_e p pEQ).
    apply finite_compuations__implies__evaluations with (v:=v) in J; auto.
Qed.

(** If e ===>o, then for any recursion depth n, C n e must be object_bot. *)
Lemma bigstep_diverging__implies__infinite_compuations : forall n e,
  lc_exp e ->
  e ===>o ->
  C n e = object_bot.
Proof.
  (** By induction on n, and case analysis over [e===>o].
      In all three cases, e = e1 e2.
      if e1 ===>o, C n e = C (n-1) e1 = bot by IH.
      if e1 ===> v1, and e2 ===>o, we have D e1 v1 by [evaluations__iff__value_denotations].
        By IH, C (n-1) e2 = bot.
        By [o_denotes_e__implies__e_computes_to_o_or_bot],
          C (n-1) e1 = bot \/ C (n-1) e1 = v1.
        In both cases, C n e = bot.
      The last case is similar.
  *)
  induction n; intros e e_is_lc e_diverges; simpl; auto.
  Case "S n=0".
  (bigstep_diverging_cases (destruct e_diverges) SCase).
    SCase "bigstep_d_app1".
      inversion e_is_lc; subst.
      apply IHn in e_diverges; auto.
      rewrite e_diverges; auto.
    SCase "bigstep_d_app2".
      inversion e_is_lc; subst.
      apply evaluations__iff__value_denotations in H0; eauto.
      destruct H0 as [o1 [EQ1 o1_denotes_e1]].
      apply IHn in e_diverges; auto.
      rewrite e_diverges; auto.
      apply o_denotes_e__implies__e_computes_to_o_or_bot with (n:=n) in o1_denotes_e1; auto.
      destruct o1_denotes_e1 as [Cne1_is_bot | Cne1_is_o].
        rewrite Cne1_is_bot. auto.

        rewrite <- Cne1_is_o in EQ1.
        destruct v1; simpl in EQ1; inversion EQ1; subst; auto.
    SCase "bigstep_d_appf".
      assert (lc_exp (open_exp_wrt_exp e1' v2)) as e1'v2_is_lc.
        apply lc_body_exp_wrt_exp; eauto.
          apply bigstep_converging_regular_2 in H0; auto.
          inversion H0; auto.
      inversion e_is_lc; subst.
      apply evaluations__iff__value_denotations in H0; eauto.
      destruct H0 as [o1 [EQ1 o1_denotes_e1]].
      apply evaluations__iff__value_denotations in H1; eauto.
      destruct H1 as [o2 [EQ2 o2_denotes_e2]].
      apply IHn in e_diverges; auto.
      apply o_denotes_e__implies__e_computes_to_o_or_bot with (n:=n) in o1_denotes_e1; auto.
      destruct o1_denotes_e1 as [Cne1_is_bot | Cne1_is_o].
        rewrite Cne1_is_bot. auto.

        rewrite <- Cne1_is_o in EQ1.
        simpl in EQ1. inversion EQ1; subst.
        apply o_denotes_e__implies__e_computes_to_o_or_bot with (n:=n) in o2_denotes_e2; auto.
        destruct o2_denotes_e2 as [Cne2_is_bot | Cne2_is_o].
          rewrite Cne2_is_bot. auto.

          rewrite <- Cne2_is_o in EQ2.
          destruct v2; simpl in EQ2; inversion EQ2; subst; auto.
Qed.

(** [===>o] and D are consistent at diverging cases. *)
Lemma bigstep_diverging__iff__bot_denotations : forall e,
  lc_exp e ->
  (e ===>o <-> D e object_bot).
Proof.
  intros e e_is_lc.
  split.
  Case "e ===>o -> D e object_bot".
    intro J.
    exists 0.
    intros n n_ge_0.
    apply bigstep_diverging__implies__infinite_compuations; auto.

  Case "D e object_bot -> e ===>o".
    (**  By coinduction and case analysis over e. The case e is value or variable
         trivially contradict the hyp that D e bot. Therefore, t must be the case
         that e = e1 e2. Let o1 and o2 denote e1 e2 by [denotation_exists].

         We then argue by case over o1 and o2 with sufficiently large n =
            max (p, p1, p2) + 1
         where p, p1 and p2 are corresponding to the donotation of e, e1 and e2.
         There are only three cases that dont contradict the hyp the D e bot:
           1) o1 = bot,
           2) o1 is value, o2 is bot,
           3) o1 and o2 are values \x.e1' and v2, and D ({v2/x}e1') bot.
         We conclude by coind for [===>o] premises, and by
         [finite_compuations__implies__evaluations] for [===>] premises.
    *)
    generalize dependent e.
    cofix Hcoind.
    intros e e_is_lc bot_denotes_e.
    (exp_cases (destruct e) SCase).
    SCase "const".
      apply bot_denotes_e__iff__e_diverges with (n:=1) in bot_denotes_e; auto.
      simpl in bot_denotes_e. inversion bot_denotes_e.
    SCase "var_b".
      rename n into i.
      apply bot_denotes_e__iff__e_diverges with (n:=1) in bot_denotes_e; auto.
      simpl in bot_denotes_e. inversion bot_denotes_e.
    SCase "var_f".
      apply bot_denotes_e__iff__e_diverges with (n:=1) in bot_denotes_e; auto.
      simpl in bot_denotes_e. inversion bot_denotes_e.
    SCase "abs".
      apply bot_denotes_e__iff__e_diverges with (n:=1) in bot_denotes_e; auto.
      simpl in bot_denotes_e. inversion bot_denotes_e.
    SCase "app".
      inversion e_is_lc; subst.
      destruct (@denotation_exists e1 H1) as [o1 [p1 o1_denotes_e1]].
      destruct (@denotation_exists e2 H2) as [o2 [p2 o2_denotes_e2]].
      destruct bot_denotes_e as [p bot_denotes_e].
      assert (p1>=p1) as p1Eq. omega.
      apply o1_denotes_e1 in p1Eq.
      assert (p2>=p2) as p2Eq. omega.
      apply o2_denotes_e2 in p2Eq.
      assert (max p (max p1 p2) + 1>=p) as pEq.
        assert (J:=@le_max_l p (max p1 p2)). omega.
      apply bot_denotes_e in pEq.
      (object_cases (destruct o1) SSCase).
      SSCase "object_bot".
        apply Hcoind in H1; auto.
          exists p1. auto.
      SSCase "object_err".
        apply err_applies_arguments_is_err with (m:=max p (max p1 p2)+1)(e2:=e2) in p1Eq; auto.
          rewrite p1Eq in pEq. inversion pEq.

          assert (J:=@le_max_r p (max p1 p2)).
          assert (J':=@le_max_l p1 p2). omega.
      SSCase "object_const".
        (object_cases (destruct o2) SSSCase).
        SSSCase "object_bot".
          apply finite_compuations__implies__evaluations with (v:=const) in p1Eq; simpl; auto.
          apply Hcoind in H2; auto.
            apply bigstep_d_app2 with (v1:=const); simpl; auto.
            exists p2. auto.
        SSSCase "object_err".
          assert (p1 <= max p1 p2) as p1_le_max. apply le_max_l.
          assert (p2 <= max p1 p2) as p2_le_max. apply le_max_r.
          apply C_preserves_const with (m:=max p1 p2) in p1Eq; auto.
          apply C_preserves_err with (m:=max p1 p2) in p2Eq; auto.
          apply const_applies_nonbot_is_err with (m:=max p (max p1 p2)+1)(e2:=e2) in p1Eq; auto.
            rewrite p1Eq in pEq. inversion pEq.
            rewrite p2Eq. intro J. inversion J.

            assert (J:=@le_max_r p (max p1 p2)). omega.
        SSSCase "object_const".
          assert (p1 <= max p1 p2) as p1_le_max. apply le_max_l.
          assert (p2 <= max p1 p2) as p2_le_max. apply le_max_r.
          apply C_preserves_const with (m:=max p1 p2) in p1Eq; auto.
          apply C_preserves_const with (m:=max p1 p2) in p2Eq; auto.
          apply const_applies_nonbot_is_err with (m:=max p (max p1 p2)+1)(e2:=e2) in p1Eq; auto.
            rewrite p1Eq in pEq. inversion pEq.
            rewrite p2Eq. intro J. inversion J.

            assert (J:=@le_max_r p (max p1 p2)). omega.
        SSSCase "object_abs".
          assert (p1 <= max p1 p2) as p1_le_max. apply le_max_l.
          assert (p2 <= max p1 p2) as p2_le_max. apply le_max_r.
          apply C_preserves_const with (m:=max p1 p2) in p1Eq; auto.
          apply C_preserves_abs with (m:=max p1 p2) in p2Eq; auto.
          apply const_applies_nonbot_is_err with (m:=max p (max p1 p2)+1)(e2:=e2) in p1Eq; auto.
            rewrite p1Eq in pEq. inversion pEq.
            rewrite p2Eq. intro J. inversion J.

            assert (J:=@le_max_r p (max p1 p2)). omega.
      SSCase "object_abs".
        (object_cases (destruct o2) SSSCase).
        SSSCase "object_bot".
          apply finite_compuations__implies__evaluations with (v:=abs e) in p1Eq; simpl; auto.
          apply Hcoind in H2; auto.
            apply bigstep_d_app2 with (v1:=abs e); simpl; auto.
            exists p2. auto.
        SSSCase "object_err".
          assert (p1 <= max p1 p2) as p1_le_max. apply le_max_l.
          assert (p2 <= max p1 p2) as p2_le_max. apply le_max_r.
          apply C_preserves_abs with (m:=max p1 p2) in p1Eq; auto.
          apply C_preserves_err with (m:=max p1 p2) in p2Eq; auto.
          apply abs_applies_err_is_err with (m:=max p (max p1 p2)+1)(e2:=e2) in p1Eq; auto.
            rewrite p1Eq in pEq. inversion pEq.

            assert (J:=@le_max_r p (max p1 p2)). omega.
        SSSCase "object_const".
          assert (J1:=p1Eq).
          assert (J2:=p2Eq).
          apply finite_compuations__implies__evaluations with (v:=abs e) in J1; simpl; auto.
          apply finite_compuations__implies__evaluations with (v:=const) in J2; simpl; auto.
          assert (lc_exp (open_exp_wrt_exp e const)) as econst_is_lc.
            apply lc_body_exp_wrt_exp; eauto.
              apply bigstep_converging_regular_2 in J1; auto.
              inversion J1; auto.
          apply bigstep_d_appf with (e1':=e)(v2:=const); simpl; auto.
            apply Hcoind; auto.
              exists (max p (max p1 p2) + 1).
              intros n n_ge_max.

              assert (p1 <= max p (max p1 p2)) as p1_le_max.
                assert (J:=@le_max_r p (max p1 p2)).
                assert (J':=@le_max_l p1 p2). omega.
              apply C_preserves_abs with (m:=max p (max p1 p2)) in p1Eq; auto.
              assert (p2 <= max p (max p1 p2)) as p2_le_max.
                assert (J:=@le_max_r p (max p1 p2)).
                assert (J':=@le_max_r p1 p2). omega.
              apply C_preserves_const with (m:=max p (max p1 p2)) in p2Eq; auto.
              apply abs_applies_const_is_reduction with (m:=n+1)(e2:=e2) in p1Eq; try solve [auto|omega].
              assert (n+1 >= p) as Sn_ge_p.
                assert (J:=@le_max_l p (max p1 p2)).
                omega.
              apply bot_denotes_e in Sn_ge_p.
              rewrite Sn_ge_p in p1Eq.
              assert (n+1-1=n) as nEq. omega.
              rewrite nEq in p1Eq. auto.

        SSSCase "object_abs".
          assert (J1:=p1Eq).
          assert (J2:=p2Eq).
          apply finite_compuations__implies__evaluations with (v:=abs e) in J1; simpl; auto.
          apply finite_compuations__implies__evaluations with (v:=abs e0) in J2; simpl; auto.
          assert (lc_exp (open_exp_wrt_exp e (abs e0))) as eabs_is_lc.
            apply lc_body_exp_wrt_exp; eauto.
              apply bigstep_converging_regular_2 in J1; auto.
              inversion J1; auto.
          apply bigstep_d_appf with (e1':=e)(v2:=abs e0); simpl; auto.
            apply Hcoind; auto.
              exists (max p (max p1 p2) + 1).
              intros n n_ge_max.
