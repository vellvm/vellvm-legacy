Require Import Coqlib.

Ltac uniq_result :=
repeat match goal with
| H1 : ?f ?a ?b ?c ?d = _,
  H2 : ?f ?a ?b ?c ?d = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a ?b ?c = _,
  H2 : ?f ?a ?b ?c = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a ?b = _,
  H2 : ?f ?a ?b = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a = _,
  H2 : ?f ?a = _ |- _ =>
  rewrite H1 in H2; inv H2
| H : ?f _ = ?f _ |- _ => inv H
| H : ?f _ _ = ?f _ _ |- _ => inv H
| H : ?f _ _ _ = ?f _ _ _ |- _ => inv H
| H : ?f _ _ _ _ = ?f _ _ _ _ |- _ => inv H
| H : ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ => inv H
| H : False |- _ => inv H
end.

