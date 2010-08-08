Add LoadPath "../../../theory/metatheory".
Require Import Metatheory.

Section MoreAssocLists.

Variable X: Type.
Definition AssocList := list (atom*X).

(* update if exists, add it otherwise *)
Fixpoint updateAddAL (m:AssocList) (i:atom) (gv:X) : AssocList :=
match m with
| nil => (i, gv)::nil
| (i', gv')::m' =>
  if (eq_dec i i')
  then (i', gv)::m'
  else (i', gv')::updateAddAL m' i gv
end.

(* update only if exists, do nothing otherwise *)
Fixpoint updateAL (m:AssocList) (i:atom) (gv:X) : AssocList :=
match m with
| nil => nil
| (i', gv')::m' =>
  if (eq_dec i i')
  then (i', gv)::m'
  else (i', gv')::updateAL m' i gv
end.

Fixpoint lookupAL (m:AssocList) (i:atom) : option X :=
match m with
| nil => None
| (i', gv')::m' =>
  if (eq_dec i i')
  then Some gv'
  else lookupAL m' i
end.

Fixpoint deleteAL (m:AssocList) (i:atom) : AssocList :=
match m with
| nil => nil
| (id0, gv0)::m' => if (i == id0) then m' else (id0, gv0)::deleteAL m' i
end.

Lemma lookupAL_updateAL_in : forall m id0 gv0,
  id0 `in` dom m ->
  lookupAL (updateAL m id0 gv0) id0 = Some gv0.
Proof.
  induction m; intros; simpl.
    simpl in H. contradict H; auto.

    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); subst; simpl; auto.
        contradict n; auto.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
        contradict n; auto.

        assert (id0 = a \/ id0 `in` dom m) as J. simpl in H. fsetdec.
        destruct J as [J | J]; subst.
          contradict n; auto.
          apply IHm with (gv0:=gv0) in J; auto.
Qed.   

Lemma lookupAL_updateAddAL_eq : forall m id0 gv0,
  lookupAL (updateAddAL m id0 gv0) id0 = Some gv0.
Proof.
  induction m; intros; simpl.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 id0); subst; simpl; auto.
      contradict n; auto.  

    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); subst; simpl; auto.
        contradict n; auto.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
        contradict n; auto.
Qed.   

Lemma lookupAL_notin : forall m id0,
  id0 `notin` dom m ->
  lookupAL m id0 = None.
Proof.
  induction m; intros; simpl; auto.
    destruct a.
    simpl in H. 
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
      contradict H; auto.
Qed.

Lemma lookupAL_updateAL_neq : forall m id0 id1 gv0,
  id1 <> id0 ->
  lookupAL m id1 = lookupAL (updateAL m id0 gv0) id1.
Proof.
  induction m; intros; simpl; auto.
    destruct a.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); subst; simpl; auto.
        contradict H; auto.
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; simpl; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
            contradict H; auto.
            destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); subst; simpl; auto.
              contradict n1; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
            destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; simpl; auto.
              contradict n; auto.
            destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; simpl; auto.
              contradict n0; auto.
Qed.   

Lemma lookupAL_updateAddAL_neq : forall m id0 id1 gv0,
  id1 <> id0 ->
  lookupAL m id1 = lookupAL (updateAddAL m id0 gv0) id1.
Proof.
  induction m; intros; simpl; auto.
    destruct (id1==id0); subst; auto.
      contradict H; auto.

    destruct a.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); subst; simpl; auto.
        contradict H; auto.
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; simpl; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
            contradict H; auto.
            destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); subst; simpl; auto.
              contradict n1; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
            destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; simpl; auto.
              contradict n; auto.
            destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; simpl; auto.
              contradict n0; auto.
Qed.   


Lemma lookupAL__indom : forall m id0 gv,
  lookupAL m id0 = Some gv ->
  id0 `in` dom m.
Proof.
  induction m; intros.
    simpl in H. inversion H.

    simpl in H. destruct a. 
    destruct (id0==a); subst; simpl; auto.
      apply IHm in H; auto.
Qed.  


Lemma lookupAL_deleteAL_eq : forall m id0,
  uniq m ->
  lookupAL (deleteAL m id0) id0 = None.
Proof.
  induction m; intros id0 Uniq; simpl; auto.
  destruct a.
  inversion Uniq; subst.
  destruct (id0==a); subst.
    apply lookupAL_notin; auto.

    simpl.
    destruct (id0==a); subst; auto.
      contradict n; auto.
Qed.

Lemma lookupAL_in : forall m id0,
  id0 `in` dom m ->
  exists gv0, lookupAL m id0 = Some gv0.
Proof.
  induction m; intros.
    simpl in H.
    contradict H; auto.

    destruct a.
    simpl in H.
    assert (id0 = a \/ id0 `in` dom m) as J.
      fsetdec.
    destruct J as [EQ | J]; subst.
      simpl.
      exists x.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); auto.
        contradict n; auto.

      simpl.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; auto.
        exists x. auto.
Qed.

Lemma updateAL_dom_eq : forall m id0 gv0,
  dom m [=] dom (updateAL m id0 gv0).
Proof.
  induction m; intros; simpl.
    fsetdec.

    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst.
      simpl. fsetdec.
      simpl. rewrite <- IHm; auto. fsetdec.
Qed.

Lemma updateAL_uniq : forall m id0 gv0,
  uniq m ->
  uniq (updateAL m id0 gv0).
Proof.
  intros m id0 gv0 Uniq.
  induction Uniq; simpl; auto.
  destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 x); subst; auto.
    simpl_env.
    apply uniq_push; auto.
      rewrite <- updateAL_dom_eq; auto.
Qed.

Lemma lookupAL_deleteAL_neq : forall m id0 id1,
  id0 <> id1 ->
  lookupAL (deleteAL m id0) id1 = lookupAL m id1.
Proof.
  induction m; intros id0 id1 id0_isnt_id1; simpl; auto.
  destruct a.
  destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; auto.
      contradict id0_isnt_id1; auto.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; simpl.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); subst; auto.
        contradict n0; auto.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; auto.
        contradict n0; auto.
Qed.

Lemma deleteAL_dom_sub : forall m id0,
  dom (deleteAL m id0) [<=] dom m.
Proof.
  induction m; intros; simpl.
    fsetdec.

    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst.
      fsetdec.

      simpl. 
      assert (J:=@IHm id0).
      fsetdec.
Qed.

Lemma deleteAL_uniq : forall m id0,
  uniq m ->
  uniq (deleteAL m id0).
Proof.
  intros m id0 Uniq.
  induction Uniq; simpl; auto.
  destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 x); subst; auto.
    simpl_env.
    assert (J:=@deleteAL_dom_sub E id0).
    apply uniq_push; auto.
Qed.

Lemma updateAddAL_dom_eq : forall sm id0 st0,
  dom (updateAddAL sm id0 st0) [=] dom sm `union` {{id0}}.
Proof.
  induction sm; intros; simpl; try solve [fsetdec].
    destruct a. 
    destruct (id0==a); simpl; try solve [fsetdec].
      assert (J:=@IHsm id0 st0). fsetdec.
Qed.

Lemma updateAddAL_uniq : forall sm id0 st0,
  uniq sm ->
  uniq (updateAddAL sm id0 st0).
Proof.
  induction sm; intros; simpl; auto.
    destruct a.

    destruct_uniq.
    destruct (id0==a); subst; try solve [solve_uniq].
      apply IHsm with (id0:=id0)(st0:=st0) in H. 
      assert (J:=@updateAddAL_dom_eq sm id0 st0).
      solve_uniq.
Qed.

Lemma updateAddAL_inversion : forall sm id0 st0 id1 st1,
  uniq sm ->
  binds id1 st1 (updateAddAL sm id0 st0) ->
  (id0 <> id1 /\ binds id1 st1 sm) \/ (id0 = id1 /\ st0 = st1).
Proof.
  induction sm; intros id0 st0 id1 st1 Uniq Binds; simpl in Binds.
    analyze_binds Binds.

    destruct a.
    inversion Uniq; subst.
    destruct (id0==a); subst.
      analyze_binds Binds.
      left. split; auto.
        apply binds_In in BindsTac.
        fsetdec.

      analyze_binds Binds.
      apply IHsm in BindsTac; auto.
        destruct BindsTac; auto.
          destruct H; auto.
Qed.

            
Lemma binds_updateAddAL_eq : forall sm id0 st0,
  binds id0 st0 (updateAddAL sm id0 st0).
Proof.
  induction sm; intros id0 st0; simpl; auto.
    destruct a.
    destruct (id0 == a); subst; auto.
Qed.

Lemma binds_updateAddAL_neq : forall sm id0 st0 id1 st1,
  binds id1 st1 sm ->
  id0 <> id1 ->
  binds id1 st1 (updateAddAL sm id0 st0).
Proof.
  induction sm; intros id0 st0 id1 st1 Hbinds id0_neq_id1; simpl; auto.
    destruct a.
    simpl_env in Hbinds.
    analyze_binds Hbinds.
      destruct (id0 == a); subst; auto.
        contradict id0_neq_id1; auto.

      destruct (id0 == a); subst; auto.
Qed.

Lemma mergeALs_inv : forall l2b l2b' B l0,
  uniq (l2b++l2b') ->
  lookupAL (l2b++l2b') l0 = Some B ->
  lookupAL l2b l0 = Some B \/ 
  lookupAL l2b' l0 = Some B.
Proof.
  intros.
  induction l2b; auto.
    destruct a. simpl in *.
    inversion H; subst.
    destruct (l0==a); subst; auto.
Qed.

Lemma mergeALs_app : forall l2b l2b' B l0,
  uniq (l2b++l2b') ->
  lookupAL l2b l0 = Some B \/ lookupAL l2b' l0 = Some B ->
  lookupAL (l2b++l2b') l0 = Some B.
Proof.
  intros.
  induction l2b; auto.
    destruct H0 as [H0 | H0]; simpl_env; auto.
    inversion H0.

    destruct a. simpl in H. 
    inversion H; subst. clear H.
    destruct H0 as [H0 | H0]; simpl in *.
      destruct (l0==a); subst; auto.
        
      destruct (l0==a); subst; auto.
        apply lookupAL__indom in H0.
        contradict H0; auto.
Qed.

End MoreAssocLists.

