Require Import Coqlib.
Require Import Metatheory.
Require Import Maps.
Require Import infrastructure_props.
Require Import Program.Tactics.
Require Import Program.Equality.

Module Type PNODE_SET.

  Variable t: Type.
  Variable add: positive -> t -> t.
  Variable pick: t -> option (positive * t).
  Variable initial: PTree.t (list positive) -> t.

  Variable In: positive -> t -> Prop.
  Hypothesis add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Hypothesis pick_none:
    forall s n, pick s = None -> ~In n s.
  Hypothesis pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Hypothesis initial_spec:
    forall successors n s,
    successors ? n = Some s -> In n (initial successors).

End PNODE_SET.

Require Import FSets.
Require Import FSetAVL.
Require Import Ordered.
(* Require Import FSets.FSetPositive. *)
Module PositiveSet := FSetAVL.Make(OrderedPositive).
Module PositiveSetFacts := FSetFacts.Facts(PositiveSet).

Module PNodeSetMax <: PNODE_SET.
  Definition t := PositiveSet.t.
  Definition add (n: positive) (s: t) : t := PositiveSet.add n s.
  Definition pick (s: t) :=
    match PositiveSet.max_elt s with
    | Some n => Some(n, PositiveSet.remove n s)
    | None => None
    end.
  Definition initial (successors: PTree.t (list positive)) :=
    PTree.fold (fun s pc scs => PositiveSet.add pc s) successors PositiveSet.empty.
  Definition In := PositiveSet.In.

  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Proof.
    intros. exact (PositiveSetFacts.add_iff s n n').
  Qed.

  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
  Proof.
    intros until n; unfold pick. caseEq (PositiveSet.max_elt s); intros.
    congruence.
    apply PositiveSet.max_elt_3. auto.
  Qed.

  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Proof.
    intros until s'; unfold pick. caseEq (PositiveSet.max_elt s); intros.
    inversion H0; clear H0; subst.
    split; intros.
    destruct (peq n n'). auto. right. apply PositiveSet.remove_2; assumption.
    elim H0; intro. subst n'. apply PositiveSet.max_elt_1. auto.
    apply PositiveSet.remove_3 with n; assumption.
    congruence.
  Qed.

  Lemma initial_spec:
    forall successors n s,
    successors ? n = Some s -> In n (initial successors).
  Proof.
    intros successors.
    apply PTree_Properties.fold_rec with
      (P := fun succ set =>
              forall n s, succ ? n = Some s -> In n set).
    (* extensionality *)
    intros. rewrite <- H in H1. eauto.
    (* base case *)
    intros. rewrite PTree.gempty in H. congruence.
    (* inductive case *)
    intros. rewrite PTree.gsspec in H2. apply add_spec.
    destruct (peq n k). auto. eauto.
  Qed.

  Lemma pick_in:
    forall s n s', pick s = Some(n, s') -> In n s.
  Proof.
    intros until s'; unfold pick. 
    caseEq (PositiveSet.max_elt s); intros; try congruence.
    uniq_result.
    apply PositiveSet.max_elt_1. auto.
  Qed.
  
  Lemma pick_notin:
    forall s n s', pick s = Some(n, s') -> ~ In n s'.
  Proof.
    intros until s'; unfold pick. 
    caseEq (PositiveSet.max_elt s); intros; try congruence.
    uniq_result.
    apply PositiveSet.remove_1. auto.
  Qed.
  
  Lemma pick_max:
    forall s n s', pick s = Some(n, s') -> 
      PositiveSet.max_elt s = Some n.
  Proof.
    intros until s'; unfold pick. 
    caseEq (PositiveSet.max_elt s); intros; try congruence.
  Qed.
  
  Lemma pick_remove:
    forall s n s', pick s = Some(n, s') -> s' = PositiveSet.remove n s.
  Proof.
    intros until s'; unfold pick. 
    caseEq (PositiveSet.max_elt s); intros; try congruence.
  Qed.
  
  Lemma initial_spec':
    forall successors n,
    In n (initial successors) -> 
    exists s, successors ? n = Some s.
  Proof.
    intros successors.
    apply PTree_Properties.fold_rec with
      (P := fun succ set =>
              forall n, In n set -> exists s, succ ? n = Some s).
    (* extensionality *)
    intros. rewrite <- H. eauto.
    (* base case *)
    intros. apply PositiveSet.empty_1 in H. tauto.
    (* inductive case *)
    intros. rewrite PTree.gsspec. apply add_spec in H2.
    destruct (peq n k); eauto.
      destruct H2 as [H2 | H2]; subst.
        congruence.
        eauto.
  Qed.
  
End PNodeSetMax.

Module PNodeSetMin <: PNODE_SET.
  Definition t := PositiveSet.t.
  Definition add (n: positive) (s: t) : t := PositiveSet.add n s.
  Definition pick (s: t) :=
    match PositiveSet.min_elt s with
    | Some n => Some(n, PositiveSet.remove n s)
    | None => None
    end.
  Definition initial (successors: PTree.t (list positive)) :=
    PTree.fold (fun s pc scs => PositiveSet.add pc s) successors PositiveSet.empty.
  Definition In := PositiveSet.In.

  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Proof.
    intros. exact (PositiveSetFacts.add_iff s n n').
  Qed.

  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
  Proof.
    intros until n; unfold pick. caseEq (PositiveSet.min_elt s); intros.
    congruence.
    apply PositiveSet.min_elt_3. auto.
  Qed.

  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Proof.
    intros until s'; unfold pick. caseEq (PositiveSet.min_elt s); intros.
    inversion H0; clear H0; subst.
    split; intros.
    destruct (peq n n'). auto. right. apply PositiveSet.remove_2; assumption.
    elim H0; intro. subst n'. apply PositiveSet.min_elt_1. auto.
    apply PositiveSet.remove_3 with n; assumption.
    congruence.
  Qed.

  Lemma initial_spec:
    forall successors n s,
    successors ? n = Some s -> In n (initial successors).
  Proof.
    intros successors.
    apply PTree_Properties.fold_rec with
      (P := fun succ set =>
              forall n s, succ ? n = Some s -> In n set).
    (* extensionality *)
    intros. rewrite <- H in H1. eauto.
    (* base case *)
    intros. rewrite PTree.gempty in H. congruence.
    (* inductive case *)
    intros. rewrite PTree.gsspec in H2. apply add_spec.
    destruct (peq n k). auto. eauto.
  Qed.
End PNodeSetMin.

Import AtomSet.
Require Import Sorted.
Require Import ListSet.

Module Type MERGE.

  Variable Pcmp: positive -> positive -> Prop.
  Variable merge : list positive -> list positive -> list positive * bool.
  Hypothesis merge_cmp_cons: forall p ps (Hlt: Forall (Pcmp p) ps),
    merge ps (p :: ps) = (ps, false).
  Hypothesis merge_spec: forall Xsdms Ysdms rl changed 
    (Hmerge: merge Xsdms Ysdms = (rl, changed)),
    sublist rl Xsdms /\ sublist rl Ysdms /\
    (changed = false <-> rl = Xsdms).
  Hypothesis merge_commut: forall Xsdms Ysdms rl changed rl' changed'
    (Hmerge: merge Xsdms Ysdms = (rl, changed))
    (Hmerge': merge Ysdms Xsdms = (rl', changed')),
    rl = rl'.
  Hypothesis merge_refl: forall Xsdms, merge Xsdms Xsdms = (Xsdms, false).

  Hypothesis merge_inter: forall Xsdms Ysdms rl changed
    (Hmerge: merge Xsdms Ysdms = (rl, changed))
    (Hsortx: StronglySorted Plt Xsdms) (Hsorty: StronglySorted Plt Ysdms),
    set_eq (set_inter positive_eq_dec Xsdms Ysdms) (rev rl).

End MERGE.

Ltac uniq_result' :=
match goal with
| H: Eq = (_ ?= _)%positive Eq |- _ => 
    symmetry in H; apply Pcompare_Eq_eq in H; subst
| H: (_ ?= _)%positive Eq = Eq |- _ => 
    apply Pcompare_Eq_eq in H; subst
| H: nil = _ ++ _ |- _ => 
    symmetry in H; apply app_eq_nil in H; destruct H; subst
| H: _ ++ _ = _ |- _ => 
    apply app_eq_nil in H; destruct H; subst
| H: _::_ = nil |- _ => inv H
| H: nil = _::_ |- _ => inv H
| _ => uniq_result
end.

Require Import cpdt_tactics.

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

Ltac destruct_let :=
match goal with
| _:context [match ?e with
             | (_, _) => _
             end] |- _ => remember e as R; destruct R
| |- context [match ?e with
              | (_, _) => _
              end] => remember e as R; destruct R
end.

Module MergeLt <: MERGE.

  Definition Pcmp := Plt.

  Program Fixpoint merge_aux (l1 l2: list positive) (acc:list positive * bool)
    {measure (length l1 + length l2)%nat}
    : (list positive * bool) :=
  let '(rl, changed) := acc in
  match l1, l2 with
  | p1::l1', p2::l2' =>
      match (Pcompare p1 p2 Eq) with
      | Eq => merge_aux l1' l2' (p1::rl, changed)
      | Lt => merge_aux l1' l2 (rl, true)
      | Gt => merge_aux l1 l2' (rl, changed)
      end
  | nil, _ => acc
  | _::_, nil => (rl, true)
  end.
  Next Obligation.
    simpl. omega.
  Qed.
  Next Obligation.
    simpl. omega.
  Qed.
  
  Definition merge_aux_spec_prop (n:nat) := forall Xsdms Ysdms
    (Hlen: (length Xsdms + length Ysdms = n)%nat)
    rl1 changed1 rl2 changed2 
    (Hmerge: merge_aux Xsdms Ysdms (rl1, changed1) = (rl2, changed2)),
    exists rl3, rl2 = rl3 ++ rl1 /\ 
                sublist (List.rev rl3) Xsdms /\
                sublist (List.rev rl3) Ysdms /\
                (changed2 = false -> List.rev rl3 = Xsdms) /\
                (List.rev rl3 = Xsdms -> changed2 = changed1) /\
                (changed1 = true -> changed2 = true).

  Ltac fold_merge_aux :=
  match goal with
  | |- context [merge_aux_func (existT _ ?arg1 (existT _ ?arg2 ?arg3))] => 
         fold (merge_aux arg1 arg2 arg3)
  end.

  Ltac unfold_merge_aux :=
  match goal with
  | |- appcontext [merge_aux ?arg] =>
     unfold merge_aux; unfold merge_aux_func;
     Program.Wf.WfExtensionality.unfold_sub merge_aux arg; simpl;
     repeat Program.Wf.fold_sub merge_aux_func;
     repeat fold_merge_aux
  end.

  Lemma merge_aux_spec_aux: forall n, merge_aux_spec_prop n.
  Proof.
    intro n.
    elim n using (well_founded_induction lt_wf).
    intros x Hrec.
    unfold merge_aux_spec_prop; intros.
    destruct Xsdms as [|Xd Xsdms]; destruct Ysdms as [|Yd Ysdms]; 
      simpl in Hlen; try solve [contradict Hlen; simpl; omega].
      compute in Hmerge. uniq_result.
      exists nil. simpl. repeat (split; try solve [auto | constructor]).

      compute in Hmerge. uniq_result. 
      exists nil. simpl. repeat (split; try solve [auto | constructor]).

      compute in Hmerge. uniq_result. 
      exists nil. simpl. 
      repeat (split; try solve [auto | constructor | congruence]).
  
      uniq_result.
      revert Hmerge. unfold_merge_aux.
      remember ((Xd ?= Yd)%positive Eq) as Cmp.
      intro.
      destruct Cmp; subst.
        apply Hrec with (y:=(length Xsdms + length Ysdms)%nat) in Hmerge; 
          try solve [simpl; omega].
        destruct Hmerge as [rl3 [J1 [J2 [J3 [J4 [J5 J6]]]]]].
        subst.
        exists (rl3++[Xd]). simpl_env.
        rewrite rev_app_distr. simpl. 
        uniq_result'.
        repeat (split; try solve [auto | constructor; auto]).
          intro J. apply J4 in J. f_equal; auto.
          intro J. inv J. auto.
        
        apply Hrec with (y:=(length Xsdms + S (length Ysdms))%nat) in Hmerge; 
           try solve [simpl; omega].
        destruct Hmerge as [rl3 [J1 [J2 [J3 [J4 [J5 J6]]]]]].
        subst.
        exists rl3. 
        repeat (split; try solve [auto | constructor; auto]).
          intro J. assert (J':=J). apply J4 in J. apply J5 in J. congruence.
          intro J. rewrite J in J2. apply sublist_cons_false in J2. tauto.
        
        apply Hrec with (y:=(S (length Xsdms) + length Ysdms)%nat) in Hmerge; 
           try solve [simpl; omega].
        destruct Hmerge as [rl3 [J1 [J2 [J3 [J4 [J5 J6]]]]]].
        subst.
        exists rl3. 
        repeat (split; try solve [auto | constructor; auto]).
  Qed.

  Lemma merge_aux_spec: forall Xsdms Ysdms rl1 changed1 rl2 changed2 
    (Hmerge: merge_aux Xsdms Ysdms (rl1, changed1) = (rl2, changed2)),
    exists rl3, rl2 = rl3 ++ rl1 /\ 
                sublist (List.rev rl3) Xsdms /\
                sublist (List.rev rl3) Ysdms /\
                (changed2 = false -> (List.rev rl3) = Xsdms) /\
                (List.rev rl3 = Xsdms -> changed2 = changed1) /\
                (changed1 = true -> changed2 = true).
  Proof.
    intros.
    assert (J:=@merge_aux_spec_aux (length Xsdms + length Ysdms)).
    unfold merge_aux_spec_prop in J.
    auto.
  Qed.
  
  Definition merge (l1 l2: list positive) : (list positive * bool) :=
    let '(rl, changed) := merge_aux l1 l2 (nil, false) in
    (rev rl, changed).

  Lemma merge_spec: forall Xsdms Ysdms rl changed 
    (Hmerge: merge Xsdms Ysdms = (rl, changed)),
    sublist rl Xsdms /\ sublist rl Ysdms /\
    (changed = false <-> rl = Xsdms).
  Proof.
    unfold merge.
    intros.
    destruct_let.
    fill_holes_in_ctx. uniq_result.
    symmetry in HeqR.
    apply merge_aux_spec in HeqR.
    destruct_conjs.
    subst. simpl_env.
    crush.
  Qed.

  Definition merge_aux_commut_prop (n:nat) := forall Xsdms Ysdms
    (Hlen: (length Xsdms + length Ysdms = n)%nat)
    rl1 changed1 changed1' rl2 changed2 rl2' changed2' 
    (Hmerge: merge_aux Xsdms Ysdms (rl1, changed1) = (rl2, changed2))
    (Hmerge': merge_aux Ysdms Xsdms (rl1, changed1') = (rl2', changed2')),
    rl2 = rl2'.

  Lemma merge_aux_commut_aux: forall n, merge_aux_commut_prop n.
  Proof.
    intro n.
    elim n using (well_founded_induction lt_wf).
    intros x Hrec.
    unfold merge_aux_commut_prop; intros.
    destruct Xsdms as [|Xd Xsdms]; destruct Ysdms as [|Yd Ysdms]; 
      simpl in Hlen; try solve [contradict Hlen; simpl; omega].
      compute in Hmerge, Hmerge'. uniq_result. auto.
      compute in Hmerge, Hmerge'. uniq_result. auto.
      compute in Hmerge, Hmerge'. uniq_result. auto.
  
      revert Hmerge. unfold_merge_aux. intro.
      revert Hmerge'. unfold_merge_aux. intro.
      remember ((Xd ?= Yd)%positive Eq) as Cmp.
      destruct Cmp; subst.
        uniq_result'.
        rewrite Pcompare_refl in Hmerge'.
        eapply Hrec with (y:=(length Xsdms + length Ysdms)%nat); 
          try solve [eauto | simpl; omega].

        rewrite ZC2 in Hmerge'; auto.
        eapply Hrec with (y:=(length Xsdms + S (length Ysdms))%nat); 
          eauto; simpl; omega.

        rewrite ZC1 in Hmerge'; auto.
        eapply Hrec with (y:=(S (length Xsdms) + length Ysdms)%nat); 
          eauto; simpl; omega.
  Qed.

  Lemma merge_commut: forall Xsdms Ysdms rl changed rl' changed'
    (Hmerge: merge Xsdms Ysdms = (rl, changed))
    (Hmerge': merge Ysdms Xsdms = (rl', changed')),
    rl = rl'.
  Proof.
    unfold merge.
    intros. destruct_let. destruct_let. uniq_result.
    assert (J:=@merge_aux_commut_aux (length Xsdms + length Ysdms)).
    unfold merge_aux_commut_prop in J.
    f_equal. eauto.
  Qed.

  Definition merge_aux_refl_prop (n:nat) := forall Xsdms
    (Hlen: (length Xsdms + length Xsdms = n)%nat) rl changed,
    merge_aux Xsdms Xsdms (rl, changed) = (rev Xsdms++rl, changed).

  Lemma merge_aux_refl_aux: forall n, merge_aux_refl_prop n.
  Proof.
    intro n.
    elim n using (well_founded_induction lt_wf).
    intros x Hrec.
    unfold merge_aux_refl_prop; intros.
    destruct Xsdms as [|Xd Xsdms];
      simpl in Hlen; try solve [contradict Hlen; simpl; omega].
      compute. auto.
  
      unfold_merge_aux. 
      simpl_env.
      rewrite Pcompare_refl. 
      erewrite Hrec with (y:=(length Xsdms + length Xsdms)%nat); 
        try solve [eauto | simpl; omega].
  Qed.

  Lemma merge_refl: forall Xsdms, merge Xsdms Xsdms = (Xsdms, false).
  Proof.
    unfold merge. intros. destruct_let.
    assert (J:=@merge_aux_refl_aux (length Xsdms + length Xsdms)).
    unfold merge_aux_refl_prop in J.
    rewrite J in HeqR; auto.
    uniq_result. simpl_env.
    rewrite rev_involutive. auto.
  Qed.

  Lemma merge_cmp_cons: forall p ps (Hlt: Forall (Plt p) ps),
    merge ps (p :: ps) = (ps, false).
  Proof.
    destruct 1; intros.
      compute. auto.

      unfold merge. unfold_merge_aux.
      rewrite ZC2; auto.
      erewrite merge_aux_refl_aux; eauto.
      simpl_env.
      rewrite rev_involutive. auto.
  Qed.

  Definition merge_aux_inter_prop (n:nat) := forall Xsdms Ysdms
    (Hlen: (length Xsdms + length Ysdms = n)%nat)
    rl1 changed1 rl2 changed2
    (Hsortx: StronglySorted Plt Xsdms) (Hsorty: StronglySorted Plt Ysdms)
    (Hmerge: merge_aux Xsdms Ysdms (rl1, changed1) = (rl2, changed2)),
    set_eq (set_union positive_eq_dec rl1
           (set_inter positive_eq_dec Xsdms Ysdms)) rl2.

  Lemma merge_aux_inter_aux: forall n, merge_aux_inter_prop n.
  Proof.
    intro n.
    elim n using (well_founded_induction lt_wf).
    intros x Hrec.
    unfold merge_aux_inter_prop; intros.
    destruct Xsdms as [|Xd Xsdms]; destruct Ysdms as [|Yd Ysdms]; 
      simpl in Hlen; try solve [contradict Hlen; simpl; omega].
      compute in Hmerge. uniq_result. simpl. auto with atomset.
      compute in Hmerge. uniq_result. simpl. auto with atomset.
      compute in Hmerge. uniq_result. simpl.
        apply set_eq_trans with (y:=set_union positive_eq_dec rl2 nil).
          apply set_eq_union; auto with atomset.
             apply set_inter_empty_eq_empty2.
          apply set_union_empty_eq_empty2.

      inv Hsortx. inv Hsorty.
      revert Hmerge. unfold_merge_aux. intro.
      remember ((Xd ?= Yd)%positive Eq) as Cmp.
      destruct Cmp; subst; symmetry in HeqCmp.
      Case "1".
        uniq_result'.
        destruct_if.
        SCase "1.1".
          clear HeqR.      
          eapply Hrec with (y:=(length Xsdms + length Ysdms)%nat) in Hmerge; 
            try solve [eauto | simpl; omega].
          (* (a :: Z) \/ (X /\ Y) = Z \/ (a :: (X /\ Y)) *)
          split; intros x Hin.
          SSCase "1.1.1".
            apply Hmerge.
            apply set_union_elim in Hin.
            apply set_union_intro.
            simpl.
            destruct Hin as [Hin | Hin]; auto.
            simpl in Hin.
            destruct Hin as [Hin | Hin]; subst; auto.
            apply set_inter_elim in Hin.
            destruct Hin as [Hin1 Hin2].
            simpl in Hin2.
            destruct Hin2 as [Hin2| Hin2]; subst; auto.
            right. apply set_inter_intro; auto.

          SSCase "1.1.2".
            apply Hmerge in Hin.
            apply set_union_elim in Hin.
            apply set_union_intro.
            simpl.
            destruct Hin as [Hin | Hin].
            SSSCase "1.1.2.1".
              simpl in Hin.
              destruct Hin as [Hin | Hin]; subst; auto.

            SSSCase "1.1.2.2".
              apply set_inter_elim in Hin.
              destruct Hin as [Hin1 Hin2].
              right. right.
              apply set_inter_intro; simpl; auto.

        SCase "1.2".
          destruct_if; congruence.

      Case "2".
        destruct_if.
        SCase "2.1".
          (* X < Y < Ysdms => ~ In X (Y::Ysdms) *)
          destruct_if.
          SSCase "2.1.1".
            rewrite Pcompare_refl in HeqCmp. congruence.
          SSCase "2.1.2".
            apply ZC2 in HeqCmp.
            rewrite Forall_lt__notin in H0; eauto using order_lt_order.
              congruence.

        SCase "2.2".
          clear HeqR.      
          eapply Hrec with (y:=(length Xsdms + S (length Ysdms))%nat) in Hmerge; 
            try solve [eauto | simpl; omega | constructor; auto].

      Case "3".
        eapply Hrec with (y:=(S (length Xsdms) + (length Ysdms))%nat) in Hmerge; 
          try solve [eauto | simpl; omega | constructor; auto].
        destruct_if.
        SCase "3.1".
          (* X > Y, In X (Y::Ysdms) => In X Ysdms 
             In X Ysdms => (X :: Xsdms) /\ Ysdms = X ++ (Xsdms /\ Ysdms)
             X > Y, Xsdms > X => ~ In Y Xsdms
             ~ In Y Xsdms => Xsdms /\ Ysdms = Xsdms /\ (Y :: Ysdms)
             so,
             rl1 \/ ((X :: Xsdms) /\ Ysdms) = 
             rl1 \/ (X :: (Xsdms /\ Ysdms)) = 
             rl1 \/ (X :: Xsdms /\ (Y :: Ysdms)) *)
          assert (set_mem positive_eq_dec Xd Ysdms = true) as XinYsdms.
            destruct_if; auto.
            rewrite Pcompare_refl in HeqCmp. congruence.
          clear HeqR.
          eapply set_eq_trans; eauto.
          apply set_union_eq_right.
          simpl_env.
          apply set_eq_trans with 
            (y:=[Xd] ++ 
                set_inter positive_eq_dec Xsdms Ysdms).
          SSCase "1".
            apply set_eq_app; auto with atomset.
            assert (J1:=set_inter_union_distr_r positive_eq_dec [Yd] Ysdms Xsdms).
            eapply set_eq_trans; eauto.
            clear J1.
            assert (~ In Yd (Xsdms)) as Hnotin.
              apply set_mem_complete1 with (Aeq_dec:=positive_eq_dec); auto.
              apply Forall_lt__notin; eauto using order_lt_order.
            rewrite_env (Yd::nil).
            rewrite set_inter_notin_r; auto.
            apply set_union_empty_eq_empty1.

          SSCase "2".
            assert (J1:=set_inter_prefix positive_eq_dec Xsdms Ysdms [Xd]).
            eapply set_eq_trans; eauto.
            clear J1.
            apply set_inter_drop_incl; auto.
              apply set_mem_correct1 in XinYsdms. 
              apply in_incl; auto.

        SCase "3.2".
          (* ~ In X (Y::Ys) => ~ In X Ys 
             ~ In X Ys => (X :: Xs) /\ Ys = Xs /\ Ys
             X > Y, Xs > X => ~ In Y Xs
             ~ In Y Xs => Xs /\ Ys = Xs /\ (Y :: Ys)
             so, 
             rl1 \/ ((X :: Xs) /\ Ys) =
             rl1 \/ (Xs /\ Ys) =
             rl1 \/ (Xs /\ (Y :: Ys))
          *)
          eapply set_eq_trans; eauto.
          apply set_union_eq_right.
          simpl_env.
          apply set_eq_trans with 
            (y:=set_inter positive_eq_dec Xsdms Ysdms).
          SSCase "1".
            rewrite_env (Yd::nil).
            apply set_inter_drop_notin_r.
              apply set_mem_complete1 with (Aeq_dec:=positive_eq_dec); auto.
              apply Forall_lt__notin; eauto using order_lt_order.
          SSCase "2".
            apply set_eq_sym. 
            rewrite_env (Xd::nil).
            apply set_inter_drop_notin_l.
              destruct_if.              
              apply set_mem_complete1 with (Aeq_dec:=positive_eq_dec); auto.
  Qed.

  Lemma merge_inter: forall Xsdms Ysdms rl changed
    (Hmerge: merge Xsdms Ysdms = (rl, changed))
    (Hsortx: StronglySorted Plt Xsdms) (Hsorty: StronglySorted Plt Ysdms),
    set_eq (set_inter positive_eq_dec Xsdms Ysdms) (rev rl).
  Proof.
    unfold merge.
    intros. destruct_let. uniq_result.
    assert (J:=@merge_aux_inter_aux (length Xsdms + length Ysdms)).
    unfold merge_aux_inter_prop in J.
    symmetry in HeqR.
    apply_clear J in HeqR; auto.
    rewrite rev_involutive.
    simpl in HeqR.
    eapply set_eq_trans; eauto.
      apply set_eq_sym.
      apply set_union_empty_eq_empty1.
  Qed.

End MergeLt.

(*
Module MergeGt <: MERGE.

  Definition Pcmp := Pgt.

  Program Fixpoint merge (l1 l2: list positive) 
    {measure ((fun l1 l2 => (length l1 + length l2)%nat) l1 l2)}
    : list positive :=
  match l1, l2 with
  | p1::l1', p2::l2' =>
      match (Pcompare p1 p2 Eq) with
      | Eq => l1
      | Gt => merge l1' l2 
      | Lt => merge l1 l2'
      end
  | _, _ => nil
  end.
  Next Obligation.
    simpl. omega.
  Qed.
  
  Definition merge_is_tail_of_left_prop (n:nat) := forall Xsdms Ysdms
    (Hlen: (length Xsdms + length Ysdms = n)%nat),
    is_tail (merge Xsdms Ysdms) Xsdms.

  Ltac fold_merge :=
  match goal with
  | |- context [merge_func (existT _ ?arg1 ?arg2)] => 
         fold (merge arg1 arg2)
  end.

  Ltac unfold_merge :=
  match goal with
  | |- appcontext [merge ?arg] =>
     unfold merge; unfold merge_func;
     Program.Wf.WfExtensionality.unfold_sub merge arg; simpl;
     repeat Program.Wf.fold_sub merge_func;
     repeat fold_merge
  end.

  Lemma merge_is_tail_of_left_aux: forall n, merge_is_tail_of_left_prop n.
  Proof.
    induction n; unfold merge_is_tail_of_left_prop; intros.
      destruct Xsdms as [|Xsdms]; destruct Ysdms as [|Ysdms]; 
        simpl in Hlen; try solve [contradict Hlen; simpl; omega].
      compute. auto with coqlib.
  
      destruct Xsdms as [|Xsdms]; destruct Ysdms as [|Ysdms]; 
        simpl in Hlen; try solve [contradict Hlen; simpl; omega].
      
        uniq_result.
        compute. auto with coqlib.
  
        uniq_result.
        compute. apply is_tail_nil.
  
        uniq_result.
        unfold_merge.
        remember ((Xsdms ?= Ysdms)%positive Eq) as Cmp.
        destruct Cmp; auto with coqlib.
          apply IHn. simpl. omega.
  Qed.

  Lemma merge_is_tail_of_left: forall Xsdms Ysdms, 
    is_tail (merge Xsdms Ysdms) Xsdms.
  Proof.
    intros.
    assert (J:=@merge_is_tail_of_left_aux (length Xsdms + length Ysdms)).
    unfold merge_is_tail_of_left_prop in J.
    auto.
  Qed.
  
  Lemma merge_cmp_cons: forall p ps (Hlt: Forall (Pgt p) ps),
    ps = merge ps (p :: ps).
  Proof.
    destruct 1; intros.
      compute. auto.

      unfold_merge.
      rewrite ZC1; auto.
      unfold_merge.
      rewrite Pcompare_refl. auto.
  Qed.

End MergeGt.
*)

Module Type LATTICEELT.

  Variable t: Type.
  Variable eq: t -> t -> Prop.
  Hypothesis eq_refl: forall x, eq x x.
  Hypothesis eq_sym: forall x y, eq x y -> eq y x.
  Hypothesis eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
(*
  Variable beq: t -> t -> bool.
  Hypothesis beq_correct: forall x y, beq x y = true -> eq x y.
*)
  Variable bot: t.
  Variable lub: t -> t -> t * bool.
  Variable top: t.
  Variable ge: t -> t -> Prop.
  Hypothesis ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Hypothesis ge_refl: forall x, ge x x.

End LATTICEELT.

Module LATTICEELT_MAP (L: LATTICEELT).

Definition in_incr (in1 in2: PMap.t L.t) : Prop :=
  forall n, L.ge in2??n in1??n.

Lemma in_incr_refl:
  forall in1, in_incr in1 in1.
Proof.
  unfold in_incr; intros. apply L.ge_refl. 
Qed.

Lemma in_incr_trans:
  forall in1 in2 in3, in_incr in1 in2 -> in_incr in2 in3 -> in_incr in1 in3.
Proof.
  unfold in_incr; intros. apply L.ge_trans with in2??n; auto.
Qed.

Definition eq bd (in1 in2: PMap.t L.t) : Prop :=
  forall n (Hin: In n bd), L.eq in2??n in1??n.

End LATTICEELT_MAP.

Module Doms (MG:MERGE) <: LATTICEELT.

  Definition t := option (list positive).

(*  
  Definition beq_hd (l1 l2: list positive) : bool :=
  match l1, l2 with
  | h1::_, h2::_ => Peqb h1 h2
  | nil, nil => true
  | _, _ => false
  end.
  
  Definition beq (x y:t) : bool := 
  match x, y with
  | Some x', Some y' => beq_hd x' y'
  | None, None => true
  | _, _ => false
  end.
*)  

  Definition eq (x y: t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@refl_equal t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@sym_equal t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@trans_equal t).

(* 
  Lemma beq_correct: forall x y (Heq: beq x y = true), eq x y.
  Proof. auto. Qed.
*)
  
  Definition bot : t := None.
  
  Definition lub (x y:t) : t * bool :=
  match x, y with
  | Some x', Some y' => 
     let '(r, changed) := (MG.merge x' y') in (Some r, changed)
  | _, None => (x, false)
  | None, _ => (y, true)
  end.
  
  Definition top : t := Some nil.
  
  Definition ge (x y:t) : Prop :=
  match x, y with
  | _, None => True
  | Some x', Some y' => sublist x' y'
  | _, _ => False
  end.

  Lemma ge_trans: forall x y z (Hxy: ge x y) (Hyz: ge y z), ge x z.
  Proof.
    unfold ge.
    destruct x as [x|]; destruct y as [y|]; destruct z as [z|]; 
      eauto using sublist_trans.
      tauto.
  Qed.

  Lemma ge_refl: forall x, ge x x.
  Proof.
    unfold ge.
    destruct x as [x|]; auto using sublist_refl.
  Qed.
(*
  Lemma merge_is_tail_of_left: forall Xsdms Ysdms, 
    is_tail (MG.merge Xsdms Ysdms) Xsdms.
  Proof. apply MG.merge_is_tail_of_left. Qed.
*)  
  Lemma merge_cmp_cons: forall p ps (Hlt: Forall (MG.Pcmp p) ps),
    MG.merge ps (p :: ps) = (ps, false).
  Proof. apply MG.merge_cmp_cons. Qed.

  Definition transfer (n:positive) (input:t) : t :=
  match input with
  | None => None
  | Some ps => Some (n::ps)
  end.

  Lemma ge_lub_left': forall x y, ge (fst (lub x y)) x.
  Proof.
    intros.
    caseEq y.
      intros Ysdms Hgety.
      caseEq x; simpl; auto.
        intros Xsdms Hgetx.
        simpl. 
        destruct_let.
        symmetry in HeqR.
        apply MG.merge_spec in HeqR. 
        simpl. tauto.

      intros Hgety.
      caseEq x; simpl; auto with sublist.
  Qed.

  Lemma ge_lub_left: forall x y r changed (Hlub: lub x y = (r, changed)),
    ge r x.
  Proof.
    intros.
    replace r with (fst (lub x y)); try solve [rewrite Hlub; auto].
    apply ge_lub_left'.
  Qed.

  Lemma lub_commut: forall x y, fst (lub x y) = fst (lub y x).
  Proof.
    intros.
    caseEq y.
      intros Ysdms Hgety.
      caseEq x; simpl; auto.
        intros Xsdms Hgetx.
        simpl. 
        repeat destruct_let.
        symmetry in HeqR.
        eapply MG.merge_commut in HeqR; eauto.
        simpl. congruence.

      intros Hgety.
      caseEq x; simpl; auto.
  Qed.

  Lemma ge_lub_right': forall x y, ge (fst (lub x y)) y.
  Proof.
    intros.
    rewrite lub_commut.
    apply ge_lub_left'.
  Qed.

  Lemma ge_lub_right: forall x y r changed (Hlub: lub x y = (r, changed)),
    ge r y.
  Proof.
    intros.
    replace r with (fst (lub x y)); try solve [rewrite Hlub; auto].
    apply ge_lub_right'.
  Qed.

  Lemma lub_bot_inv: forall x y (Hlub: fst (lub x y) = bot),
    x = bot /\ y = bot.
  Proof.
    unfold bot.
    intros.
    destruct x; destruct y; inv Hlub; auto.
    destruct_let. simpl in *. congruence.
  Qed.
  
  Lemma lub_nonbot_spec': forall x y (Hnonbot: x <> bot \/ y <> bot),
    fst (lub x y) <> bot.
  Proof.
    intros.
    destruct x; destruct y; try tauto.
      simpl. unfold bot. destruct_let. simpl. congruence.
  Qed.
  
  Lemma Leq_nonbot_inv_r: forall x y (Hnonbot: y <> bot) (Heq: eq x y),
    x <> None.
  Proof. 
    unfold eq. intros. subst. auto.
  Qed.

  Lemma Leq_nonbot_inv_l: forall x y (Hnonbot: x <> bot) (Heq: eq x y),
    y <> None.
  Proof.
    unfold eq. intros. subst. auto.
  Qed.

  Lemma transfer_nonbot: forall p dms (Hnonbot: dms <> bot),
    transfer p dms <> bot.
  Proof.
    unfold transfer, bot.
    intros.
    destruct dms; congruence.
  Qed.

  Lemma ge_Forall: forall P ox y (Hlt : Forall P y)
    (Hge: ge ox (Some y)),
    match ox with
    | Some x => Forall P x
    | _ => True
    end.
  Proof.
    intros.
    destruct ox as [x|]; tinv Hge.
    simpl in Hge. eauto with sublist.
  Qed.

  Lemma lub_bot_invl: forall x y changed
    (Hlub: lub x y = (bot, changed)),
    x = bot.
  Proof.
    intros. assert (J:=lub_bot_inv x y).
    rewrite Hlub in J. simpl in J. eapply J; eauto.
  Qed.

  Lemma lub_bot_invr: forall x y changed
    (Hlub: lub x y = (bot, changed)),
    y = bot.
  Proof.
    intros. assert (J:=lub_bot_inv x y).
    rewrite Hlub in J. simpl in J. eapply J; eauto.
  Qed.

  Lemma lub_nonbot_spec : forall (x y r : t) changed
    (Hnbot: x <> bot \/ y <> bot)
    (Hlub: lub x y = (r, changed)),
    r <> bot.
  Proof.
    intros.
    apply lub_nonbot_spec' in Hnbot. 
    rewrite Hlub in Hnbot.
    simpl in Hnbot. auto.
  Qed.
  
  Lemma Lub_unchanged_rnonbot__lnonbot: forall x y r
    (Hnonbot : y <> None)
    (HeqR : (r, false) = lub x y),
    x <> None.
  Proof.
    intros.
    intro J. rewrite J in HeqR. simpl in HeqR.
    destruct y; congruence.
  Qed.

  Lemma lub_unchanged_eq_left: forall x y r (Hlub: lub x y = (r, false)),
    x = r.
  Proof.
    intros.
    caseEq y.
      intros Ysdms Hgety. subst.
      caseEq x; simpl.
        intros Xsdms Hgetx. subst.
        simpl in *.
        destruct_let. uniq_result.
        symmetry in HeqR.
        apply MG.merge_spec in HeqR. 
        destruct_conjs. f_equal. symmetry. apply H1; auto.

        intros. subst. simpl in Hlub. congruence.

      intros Hgety. subst.
      caseEq x; intros; subst; simpl in *; try congruence.
  Qed.

  Lemma lub_changed_neq_left: forall x y r (Hlub: lub x y = (r, true)),
    x <> r.
  Proof.
    intros.
    caseEq y.
      intros Ysdms Hgety. subst.
      caseEq x; simpl.
        intros Xsdms Hgetx. subst.
        simpl in *.
        destruct_let. uniq_result.
        symmetry in HeqR.
        apply MG.merge_spec in HeqR. 
        destruct_conjs. intro J. inv J.
        assert (l=l) as EQ. auto.
        apply H1 in EQ. congruence.

        intros. subst. simpl in Hlub. congruence.
       intros Hgety. subst.
      caseEq x; intros; subst; simpl in *; try congruence.
  Qed.

  Lemma add_mono: forall p x y,
    ge x y -> ge (transfer p x) (transfer p y).
  Proof.
    unfold transfer. intros.
    destruct x as [x|]; destruct y as [y|]; auto.
      simpl in *. auto with sublist.
  Qed.

  Definition gt (x y: t) : Prop :=
  match x, y with
  | Some _, None => True
  | Some x', Some y' => sublist x' y' /\ exists a, In a y' /\ ~ In a x'
  | _, _ => False
  end.

End Doms.

Require Import syntax.
Import LLVMsyntax.

Definition atolist_ptolist_fun (a2p:ATree.t positive) :=
  fun acc ato => 
   match ATree.get ato a2p with
   | Some pto => pto::acc 
   | _ => acc
   end.

Definition atolist_ptolist (a2p: ATree.t positive) (tolist: list l): list positive :=
  List.fold_left (atolist_ptolist_fun a2p) tolist nil.

Definition asucc_psucc (a2p: ATree.t positive)  
                       (pred: PTree.t (list positive))
                       (from: l) (tolist: list l)
                       : PTree.t (list positive) :=
  match ATree.get from a2p with
  | Some pfrom => PTree.set pfrom (atolist_ptolist a2p tolist) pred
  | _ => pred
  end.

Definition asuccs_psuccs (mapping: ATree.t positive) (succs: ATree.t ls)  
  : PTree.t (list positive) :=
  ATree.fold (asucc_psucc mapping) succs (PTree.empty (list positive)).


