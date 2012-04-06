Require Import Coq.Lists.List.

Lemma nth_error_in {A : Type} (l : list A) (a : A) :
  In a l <-> exists n, nth_error l n = Some a.
Proof.
  split; intros H; induction l as [|a' l]; simpl in *.

    tauto. destruct H as [H | H]. subst. exists 0. trivial.
    destruct IHl as [n Hn]; trivial. exists (S n). trivial.

    destruct H as [[|n] Hn]; simpl in *; discriminate.
    destruct H as [[|n] Hn]; simpl in *; eauto.
    inversion Hn. subst. auto.
Qed.

Lemma map_id_ext {A : Type} (f : A -> A) (l : list A) :
  (forall a : A, f a = a) -> map f l = l.
Proof.
  intros H. induction l as [|a l]. trivial.
  simpl. rewrite H. rewrite IHl. trivial.
Qed.
