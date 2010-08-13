Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import Coq.Program.Equality.
Require Import CoqListFacts.
Require Import Metatheory.
Require Import assoclist.
Require Import genericvalues.

Export LLVMsyntax.
Export LLVMlib.

(* eq *)

Lemma neq_refl : forall n, n =n= n.
Proof.
  intros.
  symmetry.
  apply beq_nat_refl.
Qed.

Lemma typEqB_list_typEqB_refl : 
  (forall t, typEqB t t) /\
  (forall ts, list_typEqB ts ts).
Proof.
apply typ_mutind; intros; simpl; 
  try solve [
    auto using neq_refl |
    unfold is_true; auto |
    eapply andb_true_iff;
      split; auto using beq_nat_refl
  ].
Qed.

Lemma typEqB_refl : forall t, typEqB t t.
destruct typEqB_list_typEqB_refl ; auto.
Qed.

Lemma list_typEqB_refl : forall ts, list_typEqB ts ts.
destruct typEqB_list_typEqB_refl ; auto.
Qed.

Lemma idEqB_refl : forall i, idEqB i i.
Proof.
  intros. unfold idEqB. 
  destruct (i0==i0); auto.
    unfold is_true. auto.
    contradict n; auto.
Qed.

Lemma constEqB_list_constEqB_refl : 
  (forall c, constEqB c c) /\
  (forall cs, list_constEqB cs cs).
Proof.
apply const_mutind; intros; simpl; 
  try solve [
    auto using neq_refl, typEqB_refl |
    eapply andb_true_iff;
      split; auto using beq_nat_ref |
    unfold is_true; auto |
    eapply andb_true_iff;
      split; auto using beq_nat_refl
  ].

    eapply andb_true_iff.
    split. apply typEqB_refl. apply idEqB_refl.
Qed.

Lemma constEqB_refl : forall c, constEqB c c.
destruct constEqB_list_constEqB_refl; auto.
Qed.

Lemma list_constEqB_refl : forall cs, list_constEqB cs cs.
destruct constEqB_list_constEqB_refl; auto.
Qed.

Lemma valueEqB_refl: forall v, valueEqB v v.
Proof.
  destruct v; unfold valueEqB.
    apply idEqB_refl.
    apply constEqB_refl.
Qed.

Lemma bopEqB_refl: forall op, bopEqB op op.
destruct op; unfold bopEqB; unfold is_true; auto.
Qed.

Lemma extopEqB_refl: forall op, extopEqB op op.
destruct op; unfold extopEqB; unfold is_true; auto.
Qed.

Lemma castopEqB_refl: forall op, castopEqB op op.
destruct op; unfold castopEqB; unfold is_true; auto.
Qed.

Lemma condEqB_refl: forall c, condEqB c c.
destruct c; unfold condEqB; unfold is_true; auto.
Qed.

Lemma eqb_refl : forall i0, eqb i0 i0.
unfold eqb.
destruct i0; unfold is_true; auto.
Qed.

Lemma list_valueEqB_refl : forall vs, list_valueEqB vs vs.
induction vs; simpl; unfold is_true; auto.
  eapply andb_true_iff. split; auto.
    apply valueEqB_refl.
Qed.

Lemma paramsEqB_refl : forall p, paramsEqB p p.
induction p; intros; simpl.
  unfold is_true. auto.

  destruct a. 
  eapply andb_true_iff. split.
  eapply andb_true_iff. split.
  apply typEqB_refl. apply valueEqB_refl. auto.
Qed.
  
Lemma cmdEqB_refl : forall c, cmdEqB c c.
Proof.
  destruct c; unfold cmdEqB.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply bopEqB_refl. apply neq_refl.
    apply valueEqB_refl. apply valueEqB_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply typEqB_refl. apply valueEqB_refl. apply list_constEqB_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply typEqB_refl. apply valueEqB_refl.
    apply typEqB_refl. apply valueEqB_refl. apply list_constEqB_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply typEqB_refl. apply neq_refl.  apply neq_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply typEqB_refl. apply valueEqB_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply typEqB_refl. apply neq_refl.  apply neq_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply typEqB_refl. apply valueEqB_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply typEqB_refl. apply valueEqB_refl.  apply valueEqB_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply eqb_refl. apply typEqB_refl.
    apply valueEqB_refl.  apply list_valueEqB_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply extopEqB_refl. apply typEqB_refl.
    apply valueEqB_refl. apply typEqB_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply castopEqB_refl. apply typEqB_refl.
    apply valueEqB_refl. apply typEqB_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply condEqB_refl. apply typEqB_refl.
    apply valueEqB_refl. apply valueEqB_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply valueEqB_refl. apply typEqB_refl.
    apply valueEqB_refl. apply valueEqB_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply eqb_refl. apply eqb_refl. apply typEqB_refl.
    apply idEqB_refl. apply paramsEqB_refl.
Qed.

Lemma terminatorEqB_refl : forall tmn, terminatorEqB tmn tmn.
Proof.
  destruct tmn; unfold terminatorEqB.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply typEqB_refl.
    apply valueEqB_refl. apply idEqB_refl.

    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    eapply andb_true_iff. split.
    apply idEqB_refl. apply valueEqB_refl. apply idEqB_refl.  apply idEqB_refl.

    eapply andb_true_iff. split. apply idEqB_refl.  apply idEqB_refl.

    apply idEqB_refl.
Qed.

Lemma list_id_lEqB_refl : forall l0, list_id_lEqB l0 l0.
induction l0; simpl.
  unfold is_true. auto.

  eapply andb_true_iff. split.
  eapply andb_true_iff. split.
  apply idEqB_refl.  apply idEqB_refl. auto.
Qed.

Lemma phinodeEqB_refl : forall p, phinodeEqB p p.
Proof.
  destruct p.
  unfold phinodeEqB.
  eapply andb_true_iff. split.
  eapply andb_true_iff. split.
  apply idEqB_refl. apply typEqB_refl. apply list_id_lEqB_refl.
Qed.
  
Lemma phinodesEqB_refl : forall ps, phinodesEqB ps ps.
induction ps; intros; simpl.
  unfold is_true. auto.
  eapply andb_true_iff. split. apply phinodeEqB_refl. auto.
Qed. 

Lemma cmdsEqB_refl : forall cs, cmdsEqB cs cs.
induction cs; intros; simpl.
  unfold is_true. auto.
  eapply andb_true_iff. split. apply cmdEqB_refl. auto.
Qed. 

Lemma blockEqB_refl : forall B,
  blockEqB B B.
Proof.
  destruct B.
  unfold blockEqB.
  eapply andb_true_iff. split.
  eapply andb_true_iff. split.
  eapply andb_true_iff. split.
  apply idEqB_refl. 
  apply phinodesEqB_refl.
  apply cmdsEqB_refl.
  apply terminatorEqB_refl.   
Qed.
     
Lemma blocksEqB_refl : forall bs, blocksEqB bs bs.
induction bs; intros; simpl.
  unfold is_true. auto.
  eapply andb_true_iff. split. apply blockEqB_refl. auto.
Qed. 

Lemma argsEqB_refl : forall args0, argsEqB args0 args0.
induction args0; simpl.
  unfold is_true. auto.
  destruct a. 
  eapply andb_true_iff. split.
  eapply andb_true_iff. split.
  apply typEqB_refl. 
  apply idEqB_refl. auto.
Qed.

Lemma fheaderEqB_refl : forall f, fheaderEqB f f.
destruct f. unfold fheaderEqB.
  eapply andb_true_iff. split.
  eapply andb_true_iff. split.
  apply typEqB_refl. 
  apply idEqB_refl.
  apply argsEqB_refl.
Qed.
    
Lemma fdecEqB_refl : forall f, fdecEqB f f.
destruct f. unfold fdecEqB. apply fheaderEqB_refl.
Qed.

Lemma fdefEqB_refl : forall f, fdefEqB f f.
destruct f. unfold fdefEqB.
  eapply andb_true_iff. split.
  apply fheaderEqB_refl.
  apply blocksEqB_refl.
Qed.

Lemma gvarEqB_refl : forall g, gvarEqB g g.
destruct g. unfold gvarEqB.
  eapply andb_true_iff. split.
  eapply andb_true_iff. split.
  eapply andb_true_iff. split.
  apply idEqB_refl.
  apply typEqB_refl.
  apply constEqB_refl.
  apply neq_refl.
Qed.

Lemma productEqB_refl : forall p,
  productEqB p p.
destruct p; unfold productEqB.
  apply gvarEqB_refl.
  apply fdecEqB_refl.
  apply fdefEqB_refl.
Qed.

Lemma neq_inv : forall n m, n =n= m -> n = m.
Proof.
  intros. apply beq_nat_eq; auto.
Qed.

Lemma typEqB_list_typEqB_inv : 
  (forall t1 t2, typEqB t1 t2 -> t1=t2) /\
  (forall ts1 ts2, list_typEqB ts1 ts2 -> ts1=ts2).
Proof.
apply typ_mutind; intros; simpl.
  destruct t2; inversion H; subst.
  apply neq_inv in H1. auto.

  destruct t2; inversion H; subst; auto.
  destruct t2; inversion H; subst; auto.
  destruct t2; inversion H; subst; auto.

  destruct t2; inversion H0; subst.
  apply andb_true_iff in H2.
  destruct H2.
  apply neq_inv in H1.
  apply H in H2. subst. auto.

  destruct t2; inversion H1; subst.
  apply andb_true_iff in H3.
  destruct H3.
  apply H in H2.
  apply H0 in H3. subst. auto.

  destruct t2; inversion H0; subst.
  apply H in H2. subst. auto.

  destruct t2; inversion H0; subst.
  apply H in H2. subst. auto.

  destruct ts2; inversion H; subst. auto.

  destruct ts2; inversion H1; subst. 
  apply andb_true_iff in H3.
  destruct H3.
  apply H in H2.
  apply H0 in H3. subst. auto.
Qed.

Lemma typEqB_inv : forall t1 t2, typEqB t1 t2 -> t1= t2.
destruct typEqB_list_typEqB_inv ; auto.
Qed.

Lemma list_typEqB_inv : forall ts1 ts2, list_typEqB ts1 ts2 -> ts1=ts2.
destruct typEqB_list_typEqB_inv ; auto.
Qed.

Lemma idEqB_inv : forall i1 i2, idEqB i1 i2 -> i1 = i2.
Proof.
  intros. unfold idEqB in H.
  destruct (i1==i2); auto.
    inversion H.
Qed.

Lemma constEqB_list_constEqB_inv : 
  (forall c1 c2, constEqB c1 c2 -> c1=c2) /\
  (forall cs1 cs2, list_constEqB cs1 cs2 -> cs1=cs2).
Proof.
apply const_mutind; intros; simpl.
  destruct c2; inversion H.
  apply andb_true_iff in H1.
  destruct H1.
  apply neq_inv in H0.
  apply neq_inv in H1. subst. auto.

  destruct c2; inversion H.
  apply typEqB_inv in H1. subst. auto.

  destruct c2; inversion H.
  apply typEqB_inv in H1. subst. auto.

  destruct c2; inversion H0.
  apply H in H2. subst. auto.

  destruct c2; inversion H0.
  apply H in H2. subst. auto.

  destruct c2; inversion H.
  apply andb_true_iff in H1.
  destruct H1.
  apply typEqB_inv in H0.
  apply idEqB_inv in H1.
  subst. auto.

  destruct cs2; inversion H; auto.

  destruct cs2; inversion H1.
  apply andb_true_iff in H3.
  destruct H3.
  apply H in H2.
  apply H0 in H3. subst. auto.
Qed.

Lemma constEqB_inv : forall c1 c2, constEqB c1 c2 -> c1 = c2.
destruct constEqB_list_constEqB_inv; auto.
Qed.

Lemma list_constEqB_inv : forall cs1 cs2, list_constEqB cs1 cs2 -> cs1 = cs2.
destruct constEqB_list_constEqB_inv; auto.
Qed.

Lemma valueEqB_inv: forall v1 v2, valueEqB v1 v2 -> v1 = v2.
Proof.
  destruct v1.
    destruct v2; intros.
      unfold valueEqB in H.
      apply idEqB_inv in H. subst. auto.

      inversion H.
    destruct v2; intros.
      inversion H.

      unfold valueEqB in H.
      apply constEqB_inv in H. subst. auto.
Qed.

Lemma bopEqB_inv: forall op1 op2, bopEqB op1 op2 -> op1=op2.
destruct op1; destruct op2; intros H; inversion H; auto.
Qed.

Lemma extopEqB_inv: forall op1 op2, extopEqB op1 op2 -> op1=op2.
destruct op1; destruct op2; intros H; inversion H; auto.
Qed.

Lemma castopEqB_inv: forall op1 op2, castopEqB op1 op2 -> op1=op2.
destruct op1; destruct op2; intros H; inversion H; auto.
Qed.

Lemma condEqB_inv: forall c1 c2, condEqB c1 c2 -> c1=c2.
destruct c1; destruct c2; intros H; inversion H; auto.
Qed.

Lemma eqb_inv : forall i1 i2, eqb i1 i2 -> i1=i2.
destruct i1; destruct i2; intro H; inversion H; auto.
Qed.

Lemma list_valueEqB_inv : forall vs1 vs2, list_valueEqB vs1 vs2 -> vs1=vs2.
induction vs1; destruct vs2; intro H; inversion H; auto.
  apply andb_true_iff in H1.
  destruct H1.
  apply valueEqB_inv in H0.
  apply IHvs1 in H1. subst. auto.
Qed.

Lemma paramsEqB_inv : forall p1 p2, paramsEqB p1 p2 -> p1=p2.
induction p1; destruct p2; intro H; inversion H; auto.
  destruct a. inversion H1.

  destruct a. destruct p.
  apply andb_true_iff in H1.
  destruct H1.
  apply andb_true_iff in H0.
  destruct H0.
  apply IHp1 in H1.
  apply typEqB_inv in H0.
  apply valueEqB_inv in H2.
  subst. auto.
Qed.
  
Lemma cmdEqB_inv : forall c1 c2, cmdEqB c1 c2 -> c1 = c2.
Proof.
  destruct c1; destruct c2; intro H; unfold cmdEqB in H; try solve [inversion H; auto].
    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply andb_true_iff in H. destruct H as [H J4].
    apply idEqB_inv in H. apply bopEqB_inv in J4. apply neq_inv in J3.
    apply valueEqB_inv in J2. apply valueEqB_inv in J1. subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply idEqB_inv in H. apply typEqB_inv in J3. apply valueEqB_inv in J2. apply list_constEqB_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply andb_true_iff in H. destruct H as [H J4].
    apply andb_true_iff in H. destruct H as [H J5].
    apply idEqB_inv in H. apply typEqB_inv in J5. apply valueEqB_inv in J4.
    apply typEqB_inv in J3. apply valueEqB_inv in J2. apply list_constEqB_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply idEqB_inv in H. apply typEqB_inv in J3. apply neq_inv in J2.  apply neq_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply idEqB_inv in H. apply typEqB_inv in J2. apply valueEqB_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply idEqB_inv in H. apply typEqB_inv in J3. apply neq_inv in J2.  apply neq_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply idEqB_inv in H. apply typEqB_inv in J2. apply valueEqB_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply idEqB_inv in H. apply typEqB_inv in J3. apply valueEqB_inv in J2.  apply valueEqB_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply andb_true_iff in H. destruct H as [H J4].
    apply idEqB_inv in H. apply eqb_inv in J4. apply typEqB_inv in J3.
    apply valueEqB_inv in J2.  apply list_valueEqB_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply andb_true_iff in H. destruct H as [H J4].
    apply idEqB_inv in H. apply extopEqB_inv in J4. apply typEqB_inv in J3.
    apply valueEqB_inv in J2. apply typEqB_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply andb_true_iff in H. destruct H as [H J4].
    apply idEqB_inv in H. apply castopEqB_inv in J4. apply typEqB_inv in J3.
    apply valueEqB_inv in J2. apply typEqB_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply andb_true_iff in H. destruct H as [H J4].
    apply idEqB_inv in H. apply condEqB_inv in J4. apply typEqB_inv in J3.
    apply valueEqB_inv in J2. apply valueEqB_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply andb_true_iff in H. destruct H as [H J4].
    apply idEqB_inv in H. apply valueEqB_inv in J4. apply typEqB_inv in J3.
    apply valueEqB_inv in J2. apply valueEqB_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply andb_true_iff in H. destruct H as [H J4].
    apply andb_true_iff in H. destruct H as [H J5].
    apply idEqB_inv in H. apply eqb_inv in J5. apply eqb_inv in J4. apply typEqB_inv in J3.
    apply idEqB_inv in J2. apply paramsEqB_inv in J1.
    subst. auto.
Qed.

Lemma terminatorEqB_inv : forall tmn1 tmn2, terminatorEqB tmn1 tmn2 -> tmn1=tmn2.
Proof.
  destruct tmn1; destruct tmn2; intro H; unfold terminatorEqB in H; try solve [inversion H; auto].
    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply idEqB_inv in H. apply typEqB_inv in J2.
    apply valueEqB_inv in J1.
    subst. auto.

    apply idEqB_inv in H. subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply andb_true_iff in H. destruct H as [H J2].
    apply andb_true_iff in H. destruct H as [H J3].
    apply idEqB_inv in H. apply valueEqB_inv in J3. apply idEqB_inv in J2.  apply idEqB_inv in J1.
    subst. auto.

    apply andb_true_iff in H. destruct H as [H J1].
    apply idEqB_inv in H.  apply idEqB_inv in J1.
    subst. auto.

    apply idEqB_inv in H.
    subst. auto.
Qed.

Lemma list_id_lEqB_inv : forall l1 l2, list_id_lEqB l1 l2 -> l1=l2.
induction l1; destruct l2; intro H; inversion H; auto.
  apply andb_true_iff in H1. destruct H1 as [H1 J1].
  apply andb_true_iff in H1. destruct H1 as [H1 J2].
  apply IHl1 in J1.
  apply idEqB_inv in H1.  apply idEqB_inv in J2. subst. auto.
Qed.

Lemma phinodeEqB_inv : forall p1 p2, phinodeEqB p1 p2 -> p1=p2.
Proof.
  destruct p1; destruct p2; intro H; inversion H.
  apply andb_true_iff in H. destruct H as [H J1].
  apply andb_true_iff in H. destruct H as [H J2].
  apply idEqB_inv in H. apply typEqB_inv in J2. apply list_id_lEqB_inv in J1.
  subst. auto.
Qed.
  
Lemma phinodesEqB_inv : forall ps1 ps2, phinodesEqB ps1 ps2 -> ps1=ps2.
induction ps1; destruct ps2; intro H; inversion H; auto.
  apply andb_true_iff in H1. destruct H1 as [H1 J1].
  apply IHps1 in J1.
  apply phinodeEqB_inv in H1. subst. auto.
Qed.

Lemma cmdsEqB_inv : forall cs1 cs2, cmdsEqB cs1 cs2 -> cs1=cs2.
induction cs1; destruct cs2; intro H; inversion H; auto.
  apply andb_true_iff in H1. destruct H1 as [H1 J1].
  apply IHcs1 in J1.
  apply cmdEqB_inv in H1. subst. auto.
Qed.

Lemma blockEqB_inv : forall B1 B2,
  blockEqB B1 B2 -> B1 = B2.
Proof.
  destruct B1; destruct B2; intro H.
  apply andb_true_iff in H. destruct H as [H J1].
  apply andb_true_iff in H. destruct H as [H J2].
  apply andb_true_iff in H. destruct H as [H J3].
  apply idEqB_inv in H.
  apply phinodesEqB_inv in J3.
  apply cmdsEqB_inv in J2.
  apply terminatorEqB_inv in J1.   
  subst. auto.
Qed.
     
Lemma blocksEqB_inv : forall bs1 bs2, blocksEqB bs1 bs2 -> bs1=bs2.
induction bs1; destruct bs2; intro H; inversion H; auto.
  apply andb_true_iff in H1. destruct H1 as [H1 J1].
  apply IHbs1 in J1.
  apply blockEqB_inv in H1. subst. auto.
Qed.

Lemma argsEqB_inv : forall as1 as2, argsEqB as1 as2 -> as1=as2.
induction as1; destruct as2; intro H; try solve [inversion H; auto].
  destruct a. inversion H.

  destruct a. destruct p. simpl in H.
  apply andb_true_iff in H. destruct H as [H J1].
  apply andb_true_iff in H. destruct H as [H J2].
  apply typEqB_inv in H.
  apply idEqB_inv in J2. 
  apply IHas1 in J1. subst. auto.
Qed.

Lemma fheaderEqB_inv : forall f1 f2, fheaderEqB f1 f2 -> f1=f2.
destruct f1; destruct f2; intro H.
  apply andb_true_iff in H. destruct H as [H J1].
  apply andb_true_iff in H. destruct H as [H J2].
  apply typEqB_inv in H.
  apply idEqB_inv in J2.
  apply argsEqB_inv in J1.
  subst. auto.
Qed.
    
Lemma fdecEqB_inv : forall f1 f2, fdecEqB f1 f2 -> f1=f2.
unfold fdecEqB.
destruct f1. destruct f2. intro. 
  apply fheaderEqB_inv in H; subst; auto.
Qed.

Lemma fdefEqB_inv : forall f1 f2, fdefEqB f1 f2 -> f1=f2.
unfold fdefEqB.
destruct f1. destruct f2. intro. 
  apply andb_true_iff in H. destruct H as [H J1].
  apply fheaderEqB_inv in H.
  apply blocksEqB_inv in J1.
  subst. auto.
Qed.

Lemma gvarEqB_inv : forall g1 g2, gvarEqB g1 g2 -> g1=g2.
unfold gvarEqB.
destruct g1. destruct g2. intro. 
  apply andb_true_iff in H. destruct H as [H J1].
  apply andb_true_iff in H. destruct H as [H J2].
  apply andb_true_iff in H. destruct H as [H J3].
  apply idEqB_inv in H.
  apply typEqB_inv in J3.
  apply constEqB_inv in J2.
  apply neq_inv in J1.
  subst. auto.
Qed.

Lemma productEqB_inv : forall p1 p2,
  productEqB p1 p2 -> p1 = p2.
destruct p1; destruct p2; intro H; inversion H.
  apply gvarEqB_inv in H1; subst; auto.
  apply fdecEqB_inv in H1; subst; auto.
  apply fdefEqB_inv in H1; subst; auto.
Qed.

Lemma productsEqB_inv : forall ps1 ps2, productsEqB ps1 ps2 -> ps1=ps2.
induction ps1; destruct ps2; intro H; inversion H; auto.
  apply andb_true_iff in H1. destruct H1 as [H1 J1].
  apply IHps1 in J1.
  apply productEqB_inv in H1. subst. auto.
Qed.

Lemma layoutEqB_inv : forall a1 a2, layoutEqB a1 a2 -> a1=a2.
destruct a1; destruct a2; intro H; inversion H; auto.
  apply andb_true_iff in H1. destruct H1 as [H1 J1].
  apply andb_true_iff in H1. destruct H1 as [H1 J2].
  apply neq_inv in J1.
  apply neq_inv in J2.
  apply neq_inv in H1.
  subst. auto.
  
  apply andb_true_iff in H1. destruct H1 as [H1 J1].
  apply andb_true_iff in H1. destruct H1 as [H1 J2].
  apply neq_inv in J1.
  apply neq_inv in J2.
  apply neq_inv in H1.
  subst. auto.

  apply andb_true_iff in H1. destruct H1 as [H1 J1].
  apply andb_true_iff in H1. destruct H1 as [H1 J2].
  apply neq_inv in J1.
  apply neq_inv in J2.
  apply neq_inv in H1.
  subst. auto.

  apply andb_true_iff in H1. destruct H1 as [H1 J1].
  apply andb_true_iff in H1. destruct H1 as [H1 J2].
  apply neq_inv in J1.
  apply neq_inv in J2.
  apply neq_inv in H1.
  subst. auto.
Qed.  

Lemma layoutsEqB_inv : forall as1 as2, layoutsEqB as1 as2 -> as1=as2.
induction as1; destruct as2; intro H; inversion H; auto.
  apply andb_true_iff in H1. destruct H1 as [H1 J1].
  apply IHas1 in J1.
  apply layoutEqB_inv in H1. subst. auto.
Qed.

Lemma moduleEqB_inv : forall M M',
  moduleEqB M M' ->
  M = M'.
Proof.
  destruct M; destruct M'; intro H.
  apply andb_true_iff in H. destruct H as [H J1].
  apply productsEqB_inv in H.
  apply layoutsEqB_inv in J1.
  subst. auto.
Qed.

(* nth_err *)

Lemma nil_nth_error_Some__False : forall X n (v:X),
  nth_error (@nil X) n = Some v -> False.
Proof.
  induction n; intros; simpl in *; inversion H.
Qed.   

Lemma nth_error_cons__inv : forall X b lb n (b':X),
  nth_error (b::lb) n = Some b' ->
  b = b' \/ (exists n', S n' = n /\ nth_error lb n' = Some b').
Proof.
  destruct n; intros; simpl in *.
    inversion H; auto.

    right. exists n. split; auto.
Qed.

(* NoDup *)

Lemma NotIn_inv : forall X (a:X) (lb1 lb2:list X),
  ~ In a (lb1++lb2) ->
  ~ In a lb1 /\ ~ In a lb2.
Proof.
  intros.
  split; intro J'; apply H; auto using in_or_app.
Qed.

Lemma NoDup_inv : forall X (lb1 lb2:list X),
  NoDup (lb1++lb2) ->
  NoDup lb1 /\ NoDup lb2.
Proof.
  induction lb1; intros.
    split; auto using NoDup_nil.

    simpl in *. inversion H; subst.
    apply IHlb1 in H3. destruct H3.
    apply NotIn_inv in H2.
    destruct H2 as [J1 J2].
    split; auto using NoDup_cons.
Qed.

Lemma NoDup_split : forall A (l1 l2:list A),
  NoDup (l1++l2) ->
  NoDup l1 /\ NoDup l2.
Proof.
  induction l1; intros.
    simpl in *. 
    split; auto using NoDup_nil.
 
    inversion H; subst.
    apply IHl1 in H3.
    destruct H3 as [J1 J2].
    split; auto.
      apply NoDup_cons; auto.
        intro J. apply H2. apply in_or_app; auto.
Qed.

Lemma NoDup_last_inv : forall X (a:X) l0,
  NoDup (l0++a::nil) ->
  ~ In a l0.
Proof.
  induction l0; intros.
    intro J. inversion J.
  
    simpl in H.
    inversion H; subst.
    apply IHl0 in H3.
    intro J.
    simpl in J.
    inversion J; subst; auto.
      apply NotIn_inv in H2.
      destruct H2.
      apply H1; simpl; auto.
Qed.

(* gets *)

Lemma getCmdsIDs_app : forall cs1 cs2,
  getCmdsIDs (cs1++cs2) = getCmdsIDs cs1++getCmdsIDs cs2.
Proof.
  induction cs1; intros; auto.
    simpl. rewrite IHcs1. auto.
Qed.

Lemma getBlocksIDs_app : forall lb1 lb2,
  getBlocksIDs (lb1++lb2) = getBlocksIDs lb1++getBlocksIDs lb2.
Proof.
  induction lb1; intros; auto.
    simpl. rewrite IHlb1. simpl_env. auto.
Qed.

Lemma getBlocksLabels_app : forall lb1 lb2,
  getBlocksLabels (lb1++lb2) = getBlocksLabels lb1++getBlocksLabels lb2.
Proof.
  induction lb1; intros; auto.
    simpl. rewrite IHlb1. destruct a. simpl_env. auto.
Qed.

Lemma genLabel2Block_block_inv : forall b l0 b',
  lookupAL _ (genLabel2Block_block b) l0 = Some b' ->
  b = b'.
Proof.
  intros. unfold genLabel2Block_block in H.
  destruct b.
  simpl in H.
  destruct (l0==l1); subst; inversion H; auto.
Qed.        

Lemma NotInGetBlocksLabels__NotInGenLabel2Block_blocks : forall lb l0,
  ~ In l0 (getBlocksLabels lb) ->
  l0 `notin` dom (genLabel2Block_blocks lb).
Proof.
  induction lb; intros.
    simpl. auto.

    destruct a. simpl in *.
    destruct (l1==l0); subst.
      contradict H; auto.

      destruct (In_dec eq_atom_dec l0 (getBlocksLabels lb)) as [J | J].
        contradict H; auto.
        apply IHlb in J; auto.
Qed.

Lemma getBlockLabel_in_genLabel2Block_block : forall B,
  getBlockLabel B `in` dom (genLabel2Block_block B).
Proof.
  destruct B. simpl. auto.
Qed.


(* inclusion *)

Lemma InBlocksB_middle : forall lb1 B lb2,
  InBlocksB B (lb1++B::lb2).
Proof.
  induction lb1; intros; simpl; auto.
    apply orb_true_intro.
    left. apply blockEqB_refl.

    apply orb_true_intro.
    right. apply IHlb1.
Qed. 

Lemma uniqBlocks__uniqLabel2Block : forall lb,
  uniqBlocks lb ->
  uniq (genLabel2Block_blocks lb).
Proof.
  induction lb; intros; simpl; auto.
    destruct a.
    unfold uniqBlocks in H.
    destruct H.
    unfold genLabel2Block_block.
    simpl in *.
    inversion H; subst.
    apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H3.
    apply uniq_cons; auto.
      apply IHlb.
      rewrite ass_app in H0.
      apply NoDup_inv in H0. destruct H0.
      split; auto.
Qed.


Lemma uniqBlocks_nil : uniqBlocks nil.
unfold uniqBlocks. simpl. split; auto using NoDup_nil.
Qed.

Lemma uniqBlocks_inv : forall lb1 lb2,
  uniqBlocks (lb1++lb2) ->
  uniqBlocks lb1 /\ uniqBlocks lb2.
Proof.
  induction lb1; intros.
    split; auto using uniqBlocks_nil.

    destruct a.
    simpl in H.
    inversion H; subst. simpl in *.
    inversion H0; subst.
    clear H H0.
    rewrite getBlocksIDs_app in H1.
    rewrite getBlocksLabels_app in H4, H5.
    apply NoDup_inv in H5. destruct H5.
    simpl_env in H1.
    rewrite ass_app in H1.
    rewrite ass_app in H1.
    rewrite ass_app in H1.
    apply NoDup_inv in H1. destruct H1.
    apply NotIn_inv in H4. destruct H4.
    split.
      split; simpl. 
        auto using NoDup_cons.
        rewrite <- ass_app in H1.
        rewrite <- ass_app in H1.
        simpl_env. auto.
      split; auto.
Qed.

Lemma genLabel2Block_blocks_inv : forall lb f l0 l' ps' cs' tmn',
  uniqBlocks lb ->
  lookupAL _ (genLabel2Block_blocks lb) l0 = Some (block_intro l' ps' cs' tmn') ->
  l0 = l' /\
  blockInFdefB (block_intro l' ps' cs' tmn') (fdef_intro f lb).
Proof.
  induction lb; intros; simpl in *.
    inversion H0.

    assert (J:=H).
    apply uniqBlocks__uniqLabel2Block in H.
    apply mergeALs_inv in H0; auto.
    destruct H0 as [H0 | H0].
      unfold genLabel2Block_block in H0.
      destruct a. simpl in H0.
      destruct (l0 == l1); subst.
        inversion H0; subst. clear H0.
        split; auto.
        apply orb_true_intro.
        left. apply blockEqB_refl.

        inversion H0.

      simpl_env in J. 
      apply uniqBlocks_inv in J.
      destruct J.
      apply IHlb in H0; simpl_env; auto.
      destruct H0.
      split; auto.
      apply orb_true_intro; auto.
Qed.

Lemma lookupBlockViaLabelFromFdef_inv : forall F l0 l' ps' cs' tmn',
  uniqFdef F ->
  lookupBlockViaLabelFromFdef F l0 = Some (block_intro l' ps' cs' tmn') ->
  l0 = l' /\
  blockInFdefB (block_intro l' ps' cs' tmn') F.
Proof.
  intros.
  unfold lookupBlockViaLabelFromFdef in H.
  unfold genLabel2Block_fdef in H.
  destruct F.
  apply genLabel2Block_blocks_inv; auto.
Qed. 

Lemma lookupFdefViaIDFromProducts_inv : forall Ps fid F,
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  InProductsB (product_fdef F) Ps.
Proof.
  induction Ps; intros.
    simpl in H. inversion H.

    simpl in *.
    unfold lookupFdefViaIDFromProduct in H.
    destruct a.
      apply IHPs in H. auto.
      apply IHPs in H. auto.
      destruct (getFdefID f==fid); subst.
        inversion H; subst.
        apply orb_true_intro.
        left. apply productEqB_refl.

        apply IHPs in H. 
        apply orb_true_intro. auto.
Qed.

Lemma entryBlockInFdef : forall F B,
  getEntryBlock F = Some B ->
  blockInFdefB B F.
Proof.
  intros.
  unfold getEntryBlock in H.
  destruct F.
  destruct b; inversion H; subst.
    simpl. 
    apply orb_true_intro.
    left. apply blockEqB_refl.
Qed.

Lemma blockInSystemModuleFdef_inv : forall B F Ps TD S,
  blockInSystemModuleFdef B S (module_intro TD Ps) F ->
  blockInFdefB B F /\
  InProductsB (product_fdef F) Ps /\
  moduleInSystem (module_intro TD Ps) S /\
  productInSystemModuleB (product_fdef F) S (module_intro TD Ps).
Proof.
  intros.
  unfold blockInSystemModuleFdef in H.
  unfold blockInSystemModuleFdefB in H.
  unfold productInSystemModuleB in *.
  unfold productInModuleB in *.
  apply andb_true_iff in H. destruct H.
  split; auto.
  apply andb_true_iff in H0. destruct H0.
  split; auto.
  split; auto.
  eapply andb_true_iff.
  split; auto.
Qed.

Lemma blockInSystemModuleFdef_intro : forall B F Ps TD S,
  blockInFdefB B F ->
  InProductsB (product_fdef F) Ps ->
  moduleInSystem (module_intro TD Ps) S ->
  blockInSystemModuleFdef B S (module_intro TD Ps) F.
Proof.
  intros.
  unfold blockInSystemModuleFdef.
  unfold blockInSystemModuleFdefB.
  unfold productInSystemModuleB.
  unfold productInModuleB.
  eapply andb_true_iff.
  split; auto.
  eapply andb_true_iff.
  split; auto.
Qed.  

Lemma NotIn_NotInBlocksB : forall lb l0 ps cs tmn,
  ~ In l0 (getBlocksLabels lb) ->
  ~ InBlocksB (block_intro l0 ps cs tmn) lb.
Proof.
  induction lb; intros; simpl in *.
    intro J. inversion J.

    destruct a.
    simpl in *.
    remember (block_intro l0 ps cs tmn =b= block_intro l1 p c t) as J.
    destruct J.
      unfold blockEqB in HeqJ.
      unfold lEqB in HeqJ.
      destruct (l0==l1); subst.
        contradict H; auto.
        inversion HeqJ.

      intro J.
      apply H.
      right.
      apply orb_prop in J.
      destruct J as [J | J].
        inversion J.
     
        destruct (@In_dec _ eq_dec l0 (getBlocksLabels lb)) as [J1 | J1]; auto.
        apply IHlb with (ps:=ps)(cs:=cs)(tmn:=tmn) in J1.
        rewrite J in J1.
        contradict J1; auto.
        unfold is_true. auto.
Qed.

Lemma InBlocksB_In : forall lb l0 ps cs tmn,
  InBlocksB (block_intro l0 ps cs tmn) lb ->
  In l0 (getBlocksLabels lb).
Proof.
  intros.
  destruct (@In_dec _ eq_dec l0 (getBlocksLabels lb)) as [J1 | J1]; auto.
    apply NotIn_NotInBlocksB with (ps:=ps)(cs:=cs)(tmn:=tmn) in J1.
    contradict H; auto.
Qed.

Lemma entryBlockInSystemBlockFdef : forall TD Ps S fid F B,
  moduleInSystem (module_intro TD Ps) S ->
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  getEntryBlock F = Some B ->
  blockInSystemModuleFdef B S (module_intro TD Ps) F.
Proof.
  intros.
  apply lookupFdefViaIDFromProducts_inv in H0.
  apply entryBlockInFdef in H1.  
  apply blockInSystemModuleFdef_intro; auto.
Qed.

Lemma productInSystemModuleB_inv : forall F Ps TD S,
  productInSystemModuleB (product_fdef F) S (module_intro TD Ps) ->
  InProductsB (product_fdef F) Ps /\
  moduleInSystem (module_intro TD Ps) S.
Proof.
  intros.
  unfold productInSystemModuleB in *.
  unfold productInModuleB in *.
  apply andb_true_iff in H. destruct H.
  split; auto.
Qed.


Lemma productInSystemModuleB_intro : forall F Ps TD S,
  InProductsB (product_fdef F) Ps ->
  moduleInSystem (module_intro TD Ps) S ->
  productInSystemModuleB (product_fdef F) S (module_intro TD Ps).
Proof.
  intros.
  unfold productInSystemModuleB.
  unfold productInModuleB.
  eapply andb_true_iff.
  split; auto.
Qed.

Lemma lookupFdefViaIDFromProductsInSystem : forall TD Ps S fid F,
  moduleInSystem (module_intro TD Ps) S ->
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  productInSystemModuleB (product_fdef F) S (module_intro TD Ps).
Proof.
  intros.
  apply lookupFdefViaIDFromProducts_inv in H0.
  apply productInSystemModuleB_intro; auto.
Qed.

Lemma InBlocksB_uniq : forall lb l1 ps1 cs1 tmn1 ps2 cs2 tmn2,
  uniqBlocks lb ->
  InBlocksB (block_intro l1 ps1 cs1 tmn1) lb ->
  InBlocksB (block_intro l1 ps2 cs2 tmn2) lb ->
  ps1 = ps2 /\ cs1 = cs2 /\ tmn1 = tmn2.
Proof.
  induction lb; intros.
    unfold InBlocksB in *.
    inversion H0.

    inversion H; subst. clear H.
    simpl in *.
    destruct a.
    inversion H2; subst. clear H2.
    assert (J:=H5).
    apply NotIn_NotInBlocksB with (ps:=p)(cs:=c)(tmn:=t) in H5.
    apply orb_prop in H0.
    apply orb_prop in H1.
    destruct H0 as [H0 | H0].    
      apply blockEqB_inv in H0.
      inversion H0; subst. clear H0.
      destruct H1 as [H1 | H1].
        apply blockEqB_inv in H1.
        inversion H1; subst. clear H1.
        auto.

        apply InBlocksB_In in H1.
        contradict H1; auto.
 
      destruct H1 as [H1 | H1].
        apply blockEqB_inv in H1.
        inversion H1; subst. clear H1.
        apply InBlocksB_In in H0.
        contradict H0; auto.

        eapply IHlb; eauto.
          apply NoDup_split in H3.
          destruct H3.
          split; auto.
Qed.

Lemma blockInFdefB_uniq : forall l1 ps1 cs1 tmn1 ps2 cs2 tmn2 F,
  uniqFdef F ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F ->
  blockInFdefB (block_intro l1 ps2 cs2 tmn2) F ->
  ps1 = ps2 /\ cs1 = cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold blockInFdefB in *.
  destruct F.
  eapply InBlocksB_uniq; eauto.
Qed.

Lemma blockInSystemModuleFdef_uniq : forall l1 ps1 cs1 tmn1 ps2 cs2 tmn2 S M F,
  uniqFdef F ->
  blockInSystemModuleFdef (block_intro l1 ps1 cs1 tmn1) S M F ->
  blockInSystemModuleFdef (block_intro l1 ps2 cs2 tmn2) S M F ->
  ps1 = ps2 /\ cs1 = cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold blockInSystemModuleFdef in *.
  unfold blockInSystemModuleFdefB in *.
  apply andb_true_iff in H0.
  apply andb_true_iff in H1.
  destruct H0.
  destruct H1.
  eapply blockInFdefB_uniq; eauto.
Qed.

Lemma nth_error__InBlocksB : forall n lb B,
  nth_error lb n = Some B ->
  InBlocksB B lb.
Proof.
  induction n; intros; simpl in *.
    destruct lb; inversion H; subst; simpl.
      apply orb_true_intro.
      left. apply blockEqB_refl.

    destruct lb; inversion H; subst; simpl.
      apply orb_true_intro.
      right. apply IHn; auto.
Qed.

Lemma blockInFdefB__exists_nth_error : forall lb B fh,
  blockInFdefB B (fdef_intro fh lb) ->
  exists n, nth_error lb n = Some B.
Proof.
  induction lb; intros; simpl in *.
    inversion H.

    apply orb_prop in H.
    destruct H.
      apply blockEqB_inv in H. subst.
      exists 0. simpl; auto.

      apply IHlb in H; auto.
      destruct H as [n H].
      exists (S n). simpl. auto.
Qed.

Lemma productInSystemModuleB_nth_error__blockInSystemModuleFdef : forall fh lb S TD Ps n B,
  productInSystemModuleB (product_fdef (fdef_intro fh lb)) S (module_intro TD Ps) ->
  nth_error lb n = Some B ->
  blockInSystemModuleFdef B S (module_intro TD Ps) (fdef_intro fh lb).
Proof.
  intros.
  apply productInSystemModuleB_inv in H.
  destruct H.
  apply blockInSystemModuleFdef_intro; auto.
  unfold blockInFdefB.
  eapply nth_error__InBlocksB; eauto.
Qed.

(* uniqness *)
Lemma uniqProducts__uniqFdef : forall Ps F,
  uniqProducts Ps ->
  InProductsB (product_fdef F) Ps ->
  uniqFdef F.
Proof.
  induction Ps; intros.
    inversion H0.
    
    simpl in *.
    destruct H.
    apply orb_prop in H0.
    destruct H0; eauto.
      apply productEqB_inv in H0. subst.
      simpl in H. auto.
Qed.

Lemma uniqSystem__uniqFdef : forall S F M,
  uniqSystem S ->
  productInSystemModuleB (product_fdef F) S M ->
  uniqFdef F.
Proof.
  induction S; intros.
    unfold productInSystemModuleB in H0.
    apply andb_true_iff in H0.
    destruct H0.
    unfold moduleInSystemB in H0.
    inversion H0.

    unfold productInSystemModuleB in H0.
    apply andb_true_iff in H0.
    destruct H0.
    unfold moduleInSystemB in H0.
    inversion H0. clear H0.
    apply orb_prop in H3.
    simpl in H.
    destruct H as [J1 J2].
    destruct H3 as [H3 | H3].
      apply moduleEqB_inv in H3. subst.
      destruct a.
      simpl in H1. simpl in J1. destruct J1.
      eapply uniqProducts__uniqFdef; eauto.

      apply IHS with (M:=M); auto.
        unfold productInSystemModuleB.
        eapply andb_true_iff; auto.
Qed.

Lemma uniqSystem__uniqProducts : forall S TD Ps,
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniqProducts Ps.
Proof.
  induction S; intros.
    inversion H0.
    
    simpl in *.
    destruct H.
    destruct a.
    unfold moduleInSystem in H0.
    unfold moduleInSystemB in H0.
    inversion H0.
    apply orb_prop in H3.
    destruct H3; eauto.
      apply andb_true_iff in H2.
      destruct H2.
      apply productsEqB_inv in H2. subst.
      simpl in H. destruct H;  auto.
Qed.

Lemma lookupFdefViaIDFromProducts_uniq : forall TD Ps S fid F,
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  uniqFdef F.
Proof.
  intros.
  apply lookupFdefViaIDFromProducts_inv in H1.
  apply uniqSystem__uniqProducts in H0; auto.
  eapply uniqProducts__uniqFdef; simpl; eauto.
Qed.

Lemma nth_error__lookupAL_genLabel2Block_blocks : forall n lb1 B1,
  uniqBlocks lb1 ->
  nth_error lb1 n = Some B1 ->
  exists l0,  lookupAL _ (genLabel2Block_blocks lb1) l0 = Some B1.
Proof.
  induction n; intros.
    simpl in H0. destruct lb1; inversion H0; subst.
    exists (getBlockLabel B1).
    simpl. destruct B1. simpl.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l0 l0); subst; auto.
      contradict n; auto.

    simpl in H0.
    destruct lb1; inversion H0; subst.
    simpl_env in H.
    assert (J:=H).
    apply uniqBlocks_inv in J. destruct J.
    apply IHn in H0; auto.
    destruct H0 as [l0 H0].
    exists l0. simpl. destruct b.
    destruct H. simpl in *.
    inversion H; subst.
    destruct (l0==l1); subst; auto.
      apply lookupAL_Some_indom in H0.
      apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H7.
      contradict H0; auto.

      rewrite H2. auto.
Qed.          

Lemma nth_error_uniqBlocks__indom : forall n lb B,
  uniqBlocks lb ->
  nth_error lb n = Some B ->
  (getBlockLabel B) `in` dom (genLabel2Block_blocks lb).
Proof.
  induction n; intros.
    destruct lb; inversion H0; subst.
    simpl in *.
    assert (J:=@getBlockLabel_in_genLabel2Block_block B).
    simpl_env. fsetdec.

    destruct lb; try solve [inversion H0].
    simpl in *.
    simpl_env in H.
    apply uniqBlocks_inv in H. 
    destruct H.
    apply IHn in H0; auto.
    simpl_env. fsetdec.
Qed.

Lemma uniqBlocks__uniq_nth_error : forall n lb1 n' B1,
  uniqBlocks lb1 ->
  nth_error lb1 n = Some B1 ->
  nth_error lb1 n' = Some B1 ->
  n = n'.
Proof.
  induction n; intros.
    destruct n'; auto.
      simpl in *.
      destruct lb1; inversion H0; subst.
      assert (J:=H).
      simpl_env in J. apply uniqBlocks_inv in J. destruct J.
      apply nth_error_uniqBlocks__indom in H1; auto.
      destruct H. simpl in H. destruct B1. inversion H; subst.
      apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H7.
      simpl in H1. contradict H7; auto.

    destruct n'; auto.
      simpl in *.
      destruct lb1; inversion H1; subst.
      assert (J:=H).
      simpl_env in J. apply uniqBlocks_inv in J. destruct J.
      apply nth_error_uniqBlocks__indom in H0; auto.
      destruct H. simpl in H. destruct B1. inversion H; subst.
      apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H7.
      simpl in H0. contradict H7; auto.
     
      simpl in *.
      destruct lb1; inversion H0.
      simpl_env in H. apply uniqBlocks_inv in H. destruct H.
      apply IHn with (n':=n')(B1:=B1) in H0; auto.
Qed.      
      
Lemma uniqBlocks__uniqBlock : forall lb n l1 ps1 cs1 tmn1,
  uniqBlocks lb ->
  nth_error lb n = Some (block_intro l1 ps1 cs1 tmn1) ->
  NoDup (getCmdsIDs cs1).
Proof.
  induction lb; intros.
    apply nil_nth_error_Some__False in H0.
    inversion H0.

    apply nth_error_cons__inv in H0.
    simpl_env in H. 
    apply uniqBlocks_inv in H.
    destruct H as [J1 J2].
    destruct H0 as [EQ | [n' [EQ H0]]]; subst; eauto.
      unfold uniqBlocks in J1.
      destruct J1.
      simpl in H0.
      simpl_env in H0.
      apply NoDup_inv in H0.
      destruct H0.
      apply NoDup_inv in H1.
      destruct H1; auto.
Qed.

Lemma uniqFdef__uniqBlock : forall fh lb n l1 ps1 cs1 tmn1,
  uniqFdef (fdef_intro fh lb) ->
  nth_error lb n = Some (block_intro l1 ps1 cs1 tmn1) ->
  NoDup (getCmdsIDs cs1).
Proof.
  intros.
  unfold uniqFdef in H.
  eapply uniqBlocks__uniqBlock; eauto.
Qed.


  
