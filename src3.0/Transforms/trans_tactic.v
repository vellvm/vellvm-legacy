Require Import vellvm.

(* copied from SB *)
Lemma cmds_at_block_tail_next : forall B c cs tmn2,
  (exists l1:l, exists ps1, exists cs11, B =
    (l1, stmts_intro ps1 (cs11 ++ c :: cs) tmn2)) ->
  exists l1, exists ps1, exists cs11, B = (l1, stmts_intro ps1 (cs11 ++ cs) tmn2).
Proof.
  intros.
  destruct H as [l1 [ps1 [cs11 H]]]; subst.
  exists l1. exists ps1. exists (cs11 ++ [c]). simpl_env. auto.
Qed.

Ltac repeat_solve :=
  repeat (split; eauto 2 using cmds_at_block_tail_next).


Ltac fill_holes_in_ctx :=
let fill e H :=
  match goal with
  | H1: _ = e |- _ => rewrite <- H1 in H
  | H1: e = _ |- _ => rewrite H1 in H
  end
in
repeat match goal with
| H: match ?e with
     | Some _ => _
     | None => _
     end |- _ => fill e H
| H: match ?e with
     | inl _ => _
     | inr _ => _
     end |- _ => fill e H
| H: match ?e with
     | (_,_) => _
     end = _ |- _ => fill e H
| H: _ = match ?e with
     | (_,_) => _
     end |- _ => fill e H
end.

