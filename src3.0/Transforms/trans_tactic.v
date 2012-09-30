Require Import vellvm.

Ltac unfold_blk2GV := unfold blk2GV, ptr2GV, val2GV.

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


