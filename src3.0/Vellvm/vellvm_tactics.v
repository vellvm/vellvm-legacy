Require Import Coqlib.
Require Import Metatheory.

Ltac tinv H := try solve [inv H].

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

Ltac destruct_if :=
match goal with
| H: context [(if ?lk then _ else _)] |- _ =>
   remember lk as R; destruct R; try inv H
| H: context [if ?lk then _ else _] |- _ =>
   remember lk as R; destruct R; try inv H
end.

Ltac destruct_let :=
  match goal with
  | _: context [match ?e with 
                | (_,_) => _
                end] |- _ => destruct e
  | |- context [match ?e with 
                | (_,_) => _
                end] => destruct e
  end.

Ltac destruct_exists :=
repeat match goal with
| H : exists _, _ |- _ =>
    let A := fresh "A" in
    let J := fresh "J" in
    destruct H as [A J]
end.

Ltac destruct_ands :=
repeat match goal with
| H : _ /\ _ |- _ => destruct H
end.

Ltac zeauto := eauto with zarith.

Ltac inv_mbind :=
  repeat match goal with
         | H : match ?e with
               | Some _ => _
               | None => None
               end = Some _ |- _ => remember e as R; destruct R as [|]; inv H
         | H : Some _ = match ?e with
               | Some _ => _
               | None => None
               end |- _ => remember e as R; destruct R as [|]; inv H
         | H :  Some _ = match ?p with
                        | (_, _) => _
                        end |- _ => destruct p
         | H : if ?e then _ else False |- _ =>
             remember e as R; destruct R; tinv H
         | H : if ?e then False else _ |- _ =>
             remember e as R; destruct R; tinv H
         end.

Ltac inv_mbind' := inv_mbind.
Ltac inv_mbind'' := inv_mbind.

Ltac solve_in_prefix :=
repeat match goal with
| G: In ?i (?prefix ++ _) |- In ?i (?prefix ++ _) =>
  apply in_or_app;
  apply in_app_or in G;
  destruct G as [G | G]; auto;
  right
end.

Ltac solve_in_head :=
match goal with
| H0 : In _ ([_] ++ _),
  J2 : _ \/ _ \/ _ |- _ =>
    simpl in H0;
    destruct H0 as [H0 | H0]; subst; try solve [
      destruct J2 as [J2 | [J2 | J2]]; subst;
        repeat match goal with
        | H : _ /\ _ |- _ => destruct H
        end; congruence]
| H0 : In _ (_:: _),
  J2 : _ \/ _ \/ _ |- _ =>
    simpl in H0;
    destruct H0 as [H0 | H0]; subst; try solve [
      destruct J2 as [J2 | [J2 | J2]]; subst;
        repeat match goal with
        | H : _ /\ _ |- _ => destruct H
        end; congruence]
| H0 : _ = _ \/ In _ _,
  J2 : _ \/ _ \/ _ |- _ =>
    simpl in H0;
    destruct H0 as [H0 | H0]; subst; try solve [
      destruct J2 as [J2 | [J2 | J2]]; subst;
        repeat match goal with
        | H : _ /\ _ |- _ => destruct H
        end; congruence]
end.

Ltac zauto := auto with zarith.

Ltac SSSSSCase name := Case_aux subsubsubsubsubcase name.
Ltac SSSSSSCase name := Case_aux subsubsubsubsubsubcase name.

Ltac tac0 := match goal with
  | |- exists _, _ => idtac
  | |- _ => solve [eauto]
  end.


Ltac symmetry_ctx :=
  repeat match goal with
  | H : Some _ = _ |- _ => symmetry in H
  end.

Ltac app_inv :=
  repeat match goal with
  | [ H: Some _ = Some _ |- _ ] => inv H
  end.

Ltac trans_eq :=
  repeat match goal with
  | H1 : ?a = ?b, H2 : ?c = ?b |- _ => rewrite <- H1 in H2; inv H2
  | H1 : ?a = ?b, H2 : ?b = ?c |- _ => rewrite <- H1 in H2; inv H2
  end.

Ltac inv_mfalse :=
  repeat match goal with
         | H : match ?e with
               | Some _ => _
               | None => False
               end |- _ => remember e as R; destruct R as [|]; tinv H
         end.

Tactic Notation "binvt" ident(H) "as" ident(J1) ident(J2) :=
apply orb_true_iff in H; destruct H as [J1 | J2].

Tactic Notation "binvf" ident(H) "as" ident(J1) ident(J2) :=
apply orb_false_iff in H; destruct H as [J1 J2].

Ltac destruct_match :=
match goal with
| H: match ?lk with
     | Some _ => Some _
     | None => _
     end = Some _ |- _ => 
   let r := fresh "r" in
   remember lk as R; destruct R as [r|]; inv H; symmetry_ctx
end.

Ltac fill_ctxhole :=
match goal with
| H : ?e = _ |- context [ ?e ] => rewrite H
| H : _ = ?e |- context [ ?e ] => rewrite H
end.

Tactic Notation "eapply_clear" hyp(H1) "in" hyp(H2) :=
  eapply H1 in H2; eauto; clear H1.

Tactic Notation "apply_clear" hyp(H1) "in" hyp(H2) :=
  apply H1 in H2; auto; clear H1.

