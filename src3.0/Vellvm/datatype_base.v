Require Import ZArith.
Require Import Coqlib.
Require Import Floats.

Local Open Scope nat_scope.

Module Size.

Definition t := nat.
Definition dec : forall x y : t, {x=y} + {x<>y} := eq_nat_dec.
Definition Zero : t := 0.
Definition One : t := 1.
Definition Two : t := 2.
Definition Four : t := 4.
Definition Eight : t := 8.
Definition Sixteen : t := 16.
Definition ThirtyTwo : t := 32.
Definition SixtyFour : t := 64.
Definition from_nat (i:nat) : t := i.
Definition to_nat (i:t) : nat := i.
Definition to_Z (i:t) : Z := Z_of_nat i.
Definition from_Z (i:Z) : t := nat_of_Z i.
Definition add (a b:t) : t := (a + b).
Definition sub (a b:t) : t := (a - b).
Definition mul (a b:t) : t := (a * b).
Definition div (a b:t) : t := nat_of_Z ((Z_of_nat a) / (Z_of_nat b)).
Definition gt (a b:t) : Prop := (a > b).
Definition lt (a b:t) : Prop := (a < b).

End Size.

Module Align.

Definition t := nat.
Definition dec : forall x y : t, {x=y} + {x<>y} := eq_nat_dec.
Definition Zero : t := 0.
Definition One : t := 1.
Definition Two : t := 2.
Definition Four : t := 4.
Definition Eight : t := 8.
Definition Sixteen : t := 16.
Definition ThirtyTwo : t := 32.
Definition SixtyFour : t := 64.
Definition from_nat (i:nat) : t := i.
Definition to_nat (i:t) : nat := i.
Definition to_Z (i:t) : Z := Z_of_nat i.
Definition from_Z (i:Z) : t := nat_of_Z i.
Definition add (a b:t) : t := (a + b).
Definition sub (a b:t) : t := (a - b).
Definition mul (a b:t) : t := (a * b).
Definition div (a b:t) : t := nat_of_Z ((Z_of_nat a) / (Z_of_nat b)).
Definition gt (a b:t) : Prop := (a > b).
Definition lt (a b:t) : Prop := (a < b).

End Align.

Module INTEGER.

Definition t := Z.
Definition dec : forall x y : t, {x=y} + {x<>y} := zeq.
Definition to_nat (i:t) : nat := nat_of_Z i.
Definition to_Z (i:t) : Z := i.
Definition of_Z (bitwidth:Z) (v:Z) (is_signed:bool) : t := v.

End INTEGER.

Module FLOAT.

Definition t := float.
Definition dec : forall x y : t, {x=y} + {x<>y} := Float.eq_dec.
(* Definition Zero : t := Float.zero. *)

End FLOAT.
