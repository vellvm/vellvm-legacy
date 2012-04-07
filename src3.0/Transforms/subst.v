Require Import vellvm.
Require Import primitives.

Lemma subst_successors : forall f id' v',
  successors f = successors (subst_fdef id' v' f).
Admitted.

Lemma subst_reachablity_analysis : forall f id' v',
  reachablity_analysis f =
    reachablity_analysis (subst_fdef id' v' f).
Admitted.
