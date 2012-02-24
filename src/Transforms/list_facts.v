(* Auxiliary properties on lists *)

Require Import Coq.Lists.List.

Section sublist.

Variables X : Type.

Inductive sublist : list X -> list X -> Prop :=
| sl_nil : forall (l : list X), sublist nil l
| sl_cons : forall (l1 l2 : list X) (x : X),
  sublist l1 l2 -> sublist (x :: l1) (x :: l2)
| sl_cons_r : forall (l1 l2 : list X) (x : X),
  sublist l1 l2 -> sublist l1 (x :: l2).

Theorem sublist_refl : forall l : list X, sublist l l.
Proof.
  intros l. induction l as [|x l]. apply sl_nil.
  apply sl_cons. trivial.
Qed.

Hint Resolve sublist_refl.

Theorem sublist_app_r : forall (l1 l2 l2' : list X),
  sublist l1 l2 -> sublist l1 (l2' ++ l2).
Proof.
  intros l1 l2 l2' H. induction l2' as [|x l2'];
  [|apply sl_cons_r]; trivial.
Qed.

Theorem sublist_cons_weaken : forall (l1 l2 : list X) (x : X),
  sublist (x :: l1) l2 -> sublist l1 l2.
Proof.
  intros l1 l2 x H.
  remember (x :: l1) as l1'.
  induction H as [|l1' l2' x' H|l1' l2' x' H]. discriminate.
  apply sl_cons_r. inversion Heql1'. subst. trivial.
  apply sl_cons_r. apply IHH. trivial.
Qed.

Theorem sublist_app : forall (l1 l1' l2 l2' : list X),
  sublist l1 l2 -> sublist l1' l2' ->
  sublist (l1 ++ l1') (l2 ++ l2').
Proof.
  intros l1 l1' l2 l2' H1 H2. induction H1 as [l2|l1 l2 x H1|l1 l2 x H1];
  [apply sublist_app_r|apply sl_cons|apply sl_cons_r]; trivial.
Qed.

Theorem sublist_In : forall (l1 l2 : list X),
  sublist l1 l2 -> forall x : X, In x l1 -> In x l2.
Proof.
  intros l1 l2 Hl1l2.
  induction Hl1l2 as [|l1 l2 x Hl1l2|l1 l2 x Hl1l2].
  intros x contra. inversion contra.
  intros y H. inversion H; [left | right; apply IHHl1l2]; trivial.
  intros y H. right. apply IHHl1l2. trivial.
Qed.

Theorem NoDup_sublist : forall (l1 l2 : list X),
  NoDup l1 -> sublist l2 l1 -> NoDup l2.
Proof.
  intros l1 l2 Hl1 Hl1l2.
  generalize dependent l2. induction Hl1 as [|x l1 Hxl1]; intros l2 Hl1l2.
  inversion Hl1l2. constructor.
  destruct l2 as [|y l2]. apply NoDup_nil.
  inversion Hl1l2 as [|l1' l2' x' Hsub|l1' l2' x' Hsub]; subst.
    apply NoDup_cons. contradict Hxl1. apply sublist_In with l2; trivial.
    apply IHHl1. trivial.
  apply IHHl1. trivial.
Qed.

Theorem filter_sublist : forall (test : X -> bool) (l : list X),
  sublist (filter test l) l.
Proof.
  intros test l. induction l as [|x l]. apply sl_nil.
  simpl. destruct (test x). apply sl_cons. trivial.
  apply sl_cons_r. trivial.
Qed.

End sublist.

Implicit Arguments sublist [[X]].

Theorem sublist_map : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  sublist l1 l2 -> sublist (map f l1) (map f l2).
Proof.
  intros X Y f l1 l2 H. induction H as [|l1 l2 x H|l1 l2 x H];
  [apply sl_nil|apply sl_cons|apply sl_cons_r]; trivial.
Qed.