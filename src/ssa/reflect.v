Require Import ssa_lib.
Require Import Decidable.

Section Decidable.

Lemma dec_blockDominates : forall (d:dt) (b1 b2: block),
  decidable (blockDominates d b1 b2).
Proof.
  intros d b1 b2.
  unfold decidable. unfold blockDominates.
  destruct b1 as [l1 insns1].
  destruct b2 as [l2 insns2].
  remember (lset_mem l2 (d l1)) as c.
  destruct c; auto.
Qed.

End Decidable.

Inductive reflect (P:Prop) : bool -> Set :=
| ReflectT : P -> reflect P true
| ReflectF : ~P -> reflect P false
.

Section Reflect.

Lemma reflect_blockDominates : forall d b1 b2,
  reflect (blockDominates d b1 b2) (blockDominatesB d b1 b2).
Proof.
  intros d b1 b2.
  unfold blockDominates. unfold blockDominatesB.
  destruct b1 as [l1 insns1].
  destruct b2 as [l2 insns2].
  remember (lset_mem l2 (d l1)) as c.
  destruct c; auto.
    apply ReflectT; auto.
    apply ReflectF; auto.
Qed.

Require Import Monad.

Definition ifP d b1 b2 (X:Type) (t f : monad X) :=
match (reflect_blockDominates d b1 b2) with
| ReflectT _ => t
| ReflectF _ => f
end.

End Reflect.






(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./monads" "-I" "./ott") ***
*** End: ***
 *)
