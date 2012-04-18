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
| |- context [(if ?lk then _ else _)] =>
   remember lk as R; destruct R; subst; auto
| |- context [if ?lk then _ else _] => remember lk as R; destruct R; subst; auto
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

Ltac symmetry_ctx :=
  repeat match goal with
  | H : Some _ = _ |- _ => symmetry in H
  end.

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
          | H :  match ?p with
                 | (_, _) => _
                 end = Some _ |- _ => destruct p
          | H : if ?e then _ else False |- _ =>
                remember e as R; destruct R; tinv H
          | H : if ?e then False else _ |- _ =>
                remember e as R; destruct R; tinv H
          | H : match ?e with
                | Some _ => _
                | None => False
                end |- _ => remember e as R; destruct R as [|]; tinv H
          | H : match ?e with
                | Some _ => _
                | None => false
                end = true |- _ => remember e as R; destruct R as [|]; tinv H
          | H: match ?e with
               | Some _ => _
               | None => is_true false
               end |- _ => remember e as R; destruct R; tinv H
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
| H : _ = ?e |- context [ ?e ] => rewrite <- H
| H : exists _:_, ?e = _ |- context [ ?e ] => destruct H as [? H]; rewrite H
| H : exists _:_, _ = ?e |- context [ ?e ] => destruct H as [? H]; rewrite <- H
| H: ?e = _ |- context [if ?e then _ else _] => rewrite H
| H: _ = ?e |- context [if ?e then _ else _] => rewrite H
end.

Tactic Notation "eapply_clear" hyp(H1) "in" hyp(H2) :=
  eapply H1 in H2; eauto; clear H1.

Tactic Notation "apply_clear" hyp(H1) "in" hyp(H2) :=
  apply H1 in H2; auto; clear H1.

Tactic Notation "bdestruct" ident(H) "as" ident(J1) ident(J2) :=
     apply andb_true_iff in H; destruct H as [J1 J2].

Tactic Notation "bdestruct3" ident(H) "as" ident(J1) ident(J2) ident(J3) :=
     bdestruct H as H J3;
     bdestruct H as J1 J2.

Tactic Notation "bdestruct4" ident(H) "as" ident(J1) ident(J2) ident(J3) ident(J4) :=
     bdestruct3 H as H J3 J4;
     bdestruct H as J1 J2.

Tactic Notation "bdestruct5" ident(H) "as" ident(J1) ident(J2) ident(J3) ident(J4) ident(J5) :=
     bdestruct4 H as H J3 J4 J5;
     bdestruct H as J1 J2.

Ltac bdestructn H Js :=
  match Js with
  | nil => idtac
  | ?J::nil => rename H into J
  | ?J::?Js' => apply andb_true_iff in H; destruct H as [H J]; bdestructn H Js
  end.

Ltac bsplit :=
  eapply andb_true_iff; split.

Ltac destruct_if' :=
match goal with
| H: context [(if ?lk then _ else _)] |- _ =>
  match type of lk with
  | sumbool (@eq ?t ?e ?e) (not (@eq ?t ?e ?e)) =>
      destruct lk; try congruence
  | _ => destruct_if
  end
| |- _ => destruct_if
end.

(* If a split is being destructed, name each of its components
   and destruct it *)
Tactic Notation "simpl_split" ident(l1) ident(l2) :=
  match goal with
    | H : context[let '(_, _) := ?l in _] |- _ =>
      match l with
        | split _ =>
          remember l as R; destruct R as [l1 l2]
      end
  end.

Tactic Notation "simpl_split" :=
  let l1 := fresh "l1" in
  let l2 := fresh "l2" in
    simpl_split l1 l2.

(* Break a tuple into its constituent parts *)
Ltac simpl_prod :=
  repeat match goal with
           | [ p : (_ * _)%type |- _ ] =>
             destruct p
         end.

(* Use hypothesis H, cleaning it afterwards *)
Ltac apply_and_clean H :=
  clear - H;
  intros; eapply H; eauto; try subst; trivial;
  clear H.

(* If the goal involves term t, remove everything in the context
   that is not related to t. *)
Ltac remove_irrelevant t :=
  try match goal with
        | [ |- context[t] ] =>
          repeat match goal with
                   | [ H : ?P |- _ ] => 
                     match P with
                       | context[t] => fail 1
                       | _ => clear H
                     end
                 end;
          repeat match goal with
                   | [ |- ?P -> ?Q ] => intro
                 end
      end.

(* Solve "forall-like" goals on lists by induction. Specifically,
   it was made to solve the goal whenever it looks like

   H : forall a, In a (List.map ... la) -> P a b c
   ------------------------------------------------
     forall p,
       In p (List.map (fun a => (a, b, c)) la) ->
       let '(a, b, c) := p in P a b c

   This is used to convert from the new premises in well-formedness
   judgements to backward-compatible versions like wf_value_list.
*)

Ltac solve_forall_like_ind :=
  match goal with
    | [ l : list _ |- forall p, In p ?l' -> _ ] =>
      match l' with
        | context[l] =>
          intros p Hp; simpl_prod;
          induction l; simpl_prod; simpl in *; try tauto;

          (* Either our element is the consed one, or we need to use
             the induction hypothesis *)
          repeat match goal with
                   | [ H : _ = _ \/ _ |- _ ] =>
                     destruct H as [H | H];
                     [try inversion H; clear H; subst|]
                 end;

          (* Try to solve for the newly consed element *)
          try match goal with
                | [ H : context[_ \/ _ -> _] |- _ ] =>
                  solve [apply H; left; trivial]
              end;

          (* Try to solve the for the list tail *)
          match goal with
            | [ H : context[In _ _ -> _] |- _ ] =>
              apply H;
                solve [ trivial |
                  match goal with
                    | [ H : context[_ = _ \/ _ -> _]
                        |- context[In _ _ -> _] ] =>
                      intros; apply H; right; trivial
                  end
                ]
          end
      end
  end.


(* Guess which of the hypothesis will solve this case *)
Ltac guess_hyp converter :=
  match goal with
    | [ H : _ |- _ ] =>
      apply_and_clean H; converter; solve_forall_like_ind
  end.
