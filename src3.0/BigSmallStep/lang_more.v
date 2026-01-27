Require Import Metatheory.
Require Import lang_def.

Coercion var_b : nat >-> exp.
Coercion var_f : expvar >-> exp.

CoInductive typ : Set :=
| int   : typ
| arrow : typ -> typ -> typ
.

Definition typing_env : Set := list (atom*typ).

(** definitions *)

(* defns Jtyping *)
Inductive typing : typing_env -> exp -> typ -> Prop :=    (* defn typing *)
 | typing_var : forall (G:typing_env) (x:expvar) (T5:typ),
     binds ( x ) ( T5 ) ( G )  ->
     uniq ( G )  ->
     typing G (var_f x) T5
 | typing_const : forall (G:typing_env),
     uniq G ->
     typing G const int 
 | typing_abs : forall (L:vars) (G:typing_env) (e:exp) (T1 T2:typ),
      ( forall x , x \notin  L  -> typing  ( x ~ T1  ++  G )   ( open_exp_wrt_exp e (var_f x) )  T2 )  ->
     typing G (abs e)  (arrow  T1   T2 ) 
 | typing_app : forall (G:typing_env) (e1 e2:exp) (T2 T1:typ),
     typing G e1  (arrow  T1   T2 )  ->
     typing G e2 T1 ->
     typing G (app e1 e2) T2.

Hint Constructors typing.

(* ********************************************************************** *)
(** * #<a name="cases"></a># Cases Tactic *)

Tactic Notation "typ_cases" tactic(first) tactic(c) :=
  first;
  [ c "int" | c "arrow" ].

Tactic Notation "exp_cases" tactic(first) tactic(c) :=
  first;
  [ c "const" | c "var_b" | c "var_f" | c "abs" | c "app" ].

Tactic Notation "lc_exp_cases" tactic(first) tactic(c) :=
  first;
  [ c "lc_const" | c "lc_var_f" | c "lc_abs" | c "lc_app" ].

Tactic Notation "smallstep_cases" tactic(first) tactic(c) :=
  first;
  [ c "smallstep_app1" | c "smallstep_app2" | c "smallstep_beta" ].

Tactic Notation "smallstep_converging_cases" tactic(first) tactic(c) :=
  first;
  [ c "smallstep_c_refl" | c "smallstep_c_trans" ].

Tactic Notation "bigstep_converging_cases" tactic(first) tactic(c) :=
  first;
  [ c "bigstep_c_const" | c "bigstep_c_abs" | c "bigstep_c_app" ].

Tactic Notation "typing_cases" tactic(first) tactic(c) :=
  first;
  [ c "typing_var" | c "typing_const" | c "typing_abs" | c "typing_app" ].
