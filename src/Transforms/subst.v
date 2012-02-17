Require Import vellvm.
Require Import primitives.

Lemma subst_successors : forall f id' v',
  successors f = successors (subst_fdef id' v' f).
Admitted.

Lemma subst_reachablity_analysis : forall f id' v',
  dtree.reachablity_analysis f =
    dtree.reachablity_analysis (subst_fdef id' v' f).
Admitted.
