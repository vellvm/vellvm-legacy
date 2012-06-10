Require Import vellvm.

Definition seq_trans (trans1 trans2: fdef -> fdef): fdef -> fdef :=
fun f => trans2 (trans1 f).

Definition cond_trans (cond: fdef -> bool) (trans1 trans2: fdef -> fdef)
  : fdef -> fdef :=
fun f => if cond f then trans1 f else trans2 f.

Lemma seq_trans_assoc: forall trans1 trans2 trans3 f,
  seq_trans trans1 (seq_trans trans2 trans3) f =
    seq_trans (seq_trans trans1 trans2) trans3 f.
Proof.
  intros. unfold seq_trans. auto.
Qed.

Section CombinatorProps.

Variable Pcom: fdef -> Prop.

Definition trans_pres_P f (trans:fdef -> fdef):= forall (Hp1: Pcom f), Pcom (trans f).

Lemma seq_trans_pres_P: forall f trans1 trans2 
  (Hp1: Pcom (trans1 f)) (Hp2: trans_pres_P (trans1 f) trans2),
  trans_pres_P f (seq_trans trans1 trans2).
Proof.
  unfold trans_pres_P, seq_trans. auto.
Qed.

Definition true_trans_pres_P f cond (trans:fdef -> fdef) := 
  forall (Hc: cond f = true), Pcom (trans f).

Definition false_trans_pres_P f cond (trans:fdef -> fdef) := 
  forall (Hc: cond f = false), Pcom (trans f).

Lemma cond_trans_pres_P: forall f cond trans1 trans2 
  (Hp1: true_trans_pres_P f cond trans1) (Hp2: false_trans_pres_P f cond trans2),
  trans_pres_P f (cond_trans cond trans1 trans2).
Proof.
  unfold true_trans_pres_P, false_trans_pres_P, cond_trans, trans_pres_P.
  intros. 
  case_eq (cond0 f); auto.
Qed.

Lemma seq_trans_pres_strengthen_P: forall (Pcom':fdef -> Prop) f trans1 trans2 
  (Hp1: Pcom' (trans1 f)) (Hp2: Pcom' (trans1 f) -> Pcom (trans2 (trans1 f))),
  trans_pres_P f (seq_trans trans1 trans2).
Proof.
  unfold trans_pres_P, seq_trans. auto.
Qed.

End CombinatorProps.

Ltac compass_tac :=
repeat match goal with
| |- _ (seq_trans _ _ _) => apply seq_trans_pres_P; auto
| |- trans_pres_P _ _ _ => 
     let HPf := fresh "HPf" in intros HPf
| |- _ (cond_trans _ _ _ _) => apply cond_trans_pres_P; auto
| |- false_trans_pres_P _ _ _ Datatypes.id =>
    unfold false_trans_pres_P, Datatypes.id; auto
| |- true_trans_pres_P _ _ _ Datatypes.id =>
    unfold true_trans_pres_P, Datatypes.id; auto
| |- false_trans_pres_P _ _ _ _ =>
     let Hfalse := fresh "Hfalse" in intros Hfalse
| |- true_trans_pres_P _ _ _ _ =>
     let Htrue := fresh "Htrue" in intros Htrue
end.

