Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Import Arith.
Require Import ssa_mem.
Require Import monad.
Require Import trace.
Require Import Metatheory.

Definition GenericValue := mvalue.
Definition GV2nat := mvalue2nat.
Definition GV2ptr := mvalue2mptr.
Definition isGVUndef := isMvalueUndef.
Definition nat2GV := nat2mvalue.
Definition undef2GV := undef2mvalue.
Definition ptr2GV TD p := mptr2mvalue TD p (getPointerSizeInBits TD).

Definition GVMap := list (id*GenericValue).

(* update if exists, add it otherwise *)
Fixpoint updateAddGVMap (m:GVMap) (i:id) (gv:GenericValue) : GVMap :=
match m with
| nil => (i, gv)::nil
| (i', gv')::m' =>
  if (eq_dec i i')
  then (i', gv)::m'
  else (i', gv')::updateAddGVMap m' i gv
end.

(* update only if exists, do nothing otherwise *)
Fixpoint updateGVMap (m:GVMap) (i:id) (gv:GenericValue) : GVMap :=
match m with
| nil => nil
| (i', gv')::m' =>
  if (eq_dec i i')
  then (i', gv)::m'
  else (i', gv')::updateGVMap m' i gv
end.

Fixpoint lookupGVMap (m:GVMap) (i:id) : option GenericValue :=
match m with
| nil => None
| (i', gv')::m' =>
  if (eq_dec i i')
  then Some gv'
  else lookupGVMap m' i
end.

Fixpoint deleteGVMap (m:GVMap) (i:id) : GVMap :=
match m with
| nil => nil
| (id0, gv0)::m' => if (i == id0) then m' else (id0, gv0)::deleteGVMap m' i
end.

(* Globals are fixed at runtime, only changed when genGlobalAndInitMem;
   but locals can be changed. 
   Update Locals if id exists locally,
   Add it into Locals if id isnt in locals and globals,
   if the id is shadowed by locals, then update globals. *)
Definition updateEnv (locals globals:GVMap) (i:id) (gv:GenericValue) : GVMap*GVMap :=
if (@AtomSetProperties.In_dec i (dom locals))
then (* i is in locals *) 
  (updateGVMap locals i gv, globals)
else (* i isnt in locals, *)
  if (@AtomSetProperties.In_dec i (dom globals))
  then (* but i is in globals *) 
    (locals, updateGVMap globals i gv)
  else (* i is fresh. *) 
    (updateAddGVMap locals i gv, globals)
.

Definition lookupEnv (locals:GVMap) (globals:GVMap) (i:id) : option GenericValue := 
match lookupGVMap locals i with
| Some gv => Some gv
| None => lookupGVMap globals i
end.

(* replace only if exists, do nothing otherwise *)
Definition replaceEnv (locals globals : GVMap) (i:id) (gv:GenericValue) : GVMap*GVMap :=
if (@AtomSetProperties.In_dec i (dom locals))
then (* i is in locals *) 
  (updateGVMap locals i gv, globals)
else (* i isnt in locals, *)
  if (@AtomSetProperties.In_dec i (dom globals))
  then (* but i is in globals *) 
    (locals, updateGVMap globals i gv)
  else (* i is fresh. *) 
    (locals, globals)
.

Definition deleteEnv (locals globals : GVMap) (i:id) : GVMap*GVMap :=
(deleteGVMap locals i, deleteGVMap globals i).

Definition rollbackEnv (locals globals : GVMap) (i:id) (lc0 gl0 : GVMap) : GVMap*GVMap :=
match (lookupEnv lc0 gl0 i) with
| Some gv0 => replaceEnv locals globals i gv0
| None => deleteEnv locals globals i
end.

Lemma lookupGVMap_updateGVMap_in : forall m id0 gv0,
  id0 `in` dom m ->
  lookupGVMap (updateGVMap m id0 gv0) id0 = Some gv0.
Proof.
  induction m; intros; simpl.
    simpl in H. contradict H; auto.

    destruct a.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst; simpl.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) a a); subst; simpl; auto.
        contradict n; auto.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst; simpl; auto.
        contradict n; auto.

        assert (id0 = a \/ id0 `in` dom m) as J. simpl in H. fsetdec.
        destruct J as [J | J]; subst.
          contradict n; auto.
          apply IHm with (gv0:=gv0) in J; auto.
Qed.   

Lemma lookupGVMap_updateAddGVMap_eq : forall m id0 gv0,
  lookupGVMap (updateAddGVMap m id0 gv0) id0 = Some gv0.
Proof.
  induction m; intros; simpl.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 id0); subst; simpl; auto.
      contradict n; auto.  

    destruct a.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 i0); subst; simpl.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) i0 i0); subst; simpl; auto.
        contradict n; auto.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 i0); subst; simpl; auto.
        contradict n; auto.
Qed.   

Lemma lookupGVMap_notin : forall m id0,
  id0 `notin` dom m ->
  lookupGVMap m id0 = None.
Proof.
  induction m; intros; simpl; auto.
    destruct a.
    simpl in H. 
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst; simpl; auto.
      contradict H; auto.
Qed.

Lemma lookupEnv_updateEnv_eq : forall id0 lc gl gv0 lc' gl',
  updateEnv lc gl id0 gv0 = (lc', gl') ->
  lookupEnv lc' gl' id0 = Some gv0.
Proof.
  intros id0 lc gl gv0 lc' gl' HupdateEnv.
  unfold lookupEnv.
  unfold updateEnv in HupdateEnv.
  destruct (@AtomSetProperties.In_dec id0 (dom lc)) as [id0_in_lc | id0_notin_lc].
    inversion HupdateEnv; subst. clear HupdateEnv.
    rewrite lookupGVMap_updateGVMap_in; auto.

    destruct (@AtomSetProperties.In_dec id0 (dom gl)) as [id0_in_gl | id0_notin_gl].
      inversion HupdateEnv; subst. clear HupdateEnv.
      rewrite lookupGVMap_notin; auto.
      rewrite lookupGVMap_updateGVMap_in; auto. 

      inversion HupdateEnv; subst. clear HupdateEnv.
      rewrite lookupGVMap_updateAddGVMap_eq; auto.
Qed.

Lemma lookupGVMap_updateGVMap_neq : forall m id0 id1 gv0,
  id1 <> id0 ->
  lookupGVMap m id1 = lookupGVMap (updateGVMap m id0 gv0) id1.
Proof.
  induction m; intros; simpl; auto.
    destruct a.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 id0); subst; simpl; auto.
        contradict H; auto.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst; simpl; auto.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 i0); subst; simpl; auto.
            contradict H; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) i0 i0); subst; simpl; auto.
              contradict n1; auto.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 i0); subst; simpl; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst; simpl; auto.
              contradict n; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst; simpl; auto.
              contradict n0; auto.
Qed.   

Lemma lookupGVMap_updateAddGVMap_neq : forall m id0 id1 gv0,
  id1 <> id0 ->
  lookupGVMap m id1 = lookupGVMap (updateAddGVMap m id0 gv0) id1.
Proof.
  induction m; intros; simpl; auto.
    destruct (id1==id0); subst; auto.
      contradict H; auto.

    destruct a.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 id0); subst; simpl; auto.
        contradict H; auto.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst; simpl; auto.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 i0); subst; simpl; auto.
            contradict H; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) i0 i0); subst; simpl; auto.
              contradict n1; auto.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 i0); subst; simpl; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst; simpl; auto.
              contradict n; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst; simpl; auto.
              contradict n0; auto.
Qed.   

Lemma lookupEnv_updateEnv_neq : forall id0 id1 lc gl gv0 lc' gl',
  updateEnv lc gl id0 gv0 = (lc', gl') ->
  id1 <> id0 ->
  lookupEnv lc gl id1 = lookupEnv lc' gl' id1.
Proof.
  intros id0 id1 lc gl ogv0 lc' gl' HupdateEnv id1_isnt_id0.
  unfold updateEnv in HupdateEnv.
  unfold lookupEnv.
  destruct (@AtomSetProperties.In_dec id0 (dom lc)) as [id0_in_lc | id0_notin_lc].
    inversion HupdateEnv; subst. clear HupdateEnv.
    rewrite <- lookupGVMap_updateGVMap_neq; auto.

    destruct (@AtomSetProperties.In_dec id0 (dom gl)) as [id0_in_gl | id0_notin_gl].
      inversion HupdateEnv; subst. clear HupdateEnv.
      rewrite <- lookupGVMap_updateGVMap_neq; auto.
    
      inversion HupdateEnv; subst. clear HupdateEnv.
      rewrite <- lookupGVMap_updateAddGVMap_neq; auto.
Qed. 


Lemma lookupGVMap__indom : forall m id0 gv,
  lookupGVMap m id0 = Some gv ->
  id0 `in` dom m.
Proof.
  induction m; intros.
    simpl in H. inversion H.

    simpl in H. destruct a. 
    destruct (id0==i0); subst; simpl; auto.
      apply IHm in H; auto.
Qed.  

Lemma lookupEnv__indom : forall id0 lc gl gv,
  lookupEnv lc gl id0 = Some gv ->
  id0 `in` dom lc `union` dom gl.
Proof.
  intros id0 lc gl gv H.
  unfold lookupEnv in H.
  remember (lookupGVMap lc id0) as ogv.
  destruct ogv.
    symmetry in Heqogv.
    apply lookupGVMap__indom in Heqogv; auto.

    apply lookupGVMap__indom in H; auto.
Qed.

Lemma exists_updateEnv : forall lc gl i0 gv3,
  exists lc2, exists gl2, updateEnv lc gl i0 gv3 = (lc2, gl2).
Proof.
  intros lc gl i0 gv3.
  unfold updateEnv.
  destruct (AtomSetProperties.In_dec i0 (dom lc)).
    exists (updateGVMap lc i0 gv3). exists gl. auto.
    destruct (AtomSetProperties.In_dec i0 (dom gl)).
      exists lc. exists (updateGVMap gl i0 gv3). auto.
      exists (updateAddGVMap lc i0 gv3). exists gl. auto.
Qed.    

Lemma lookupGVMap_deleteGVMap_eq : forall m id0,
  uniq m ->
  lookupGVMap (deleteGVMap m id0) id0 = None.
Proof.
  induction m; intros id0 Uniq; simpl; auto.
  destruct a.
  inversion Uniq; subst.
  destruct (id0==a); subst.
    apply lookupGVMap_notin; auto.

    simpl.
    destruct (id0==a); subst; auto.
      contradict n; auto.
Qed.

Lemma exists_replaceEnv : forall lc gl i0 gv0, 
  exists lc2, exists gl2, replaceEnv lc gl i0 gv0 = (lc2, gl2).
Proof.
  intros lc gl i0 gv3.
  unfold replaceEnv.
  destruct (AtomSetProperties.In_dec i0 (dom lc)).
    exists (updateGVMap lc i0 gv3). exists gl. auto.
    destruct (AtomSetProperties.In_dec i0 (dom gl)).
      exists lc. exists (updateGVMap gl i0 gv3). auto.
      exists lc. exists gl. auto.
Qed.   

Lemma lookupEnv_replaceEnv_Some_eq : forall lc gl id0 gv0 lc' gl' gv1,
  lookupEnv lc gl id0 = Some gv0 ->
  replaceEnv lc gl id0 gv1 = (lc', gl') ->
  lookupEnv lc' gl' id0 = Some gv1.
Proof.
  intros lc gl id0 gv0 lc' gl' gv1 Hl Hr.
  unfold replaceEnv in Hr.
  unfold lookupEnv in *.
  destruct (AtomSetProperties.In_dec id0 (dom lc)).
    inversion Hr; subst.
    rewrite lookupGVMap_updateGVMap_in; auto.

    destruct (AtomSetProperties.In_dec id0 (dom gl)).
      inversion Hr; subst. clear Hr.
      rewrite lookupGVMap_notin; auto.
      rewrite lookupGVMap_updateGVMap_in; auto. 

      inversion Hr; subst. clear Hr.
      rewrite lookupGVMap_notin in Hl; auto.
      rewrite lookupGVMap_notin in Hl; auto.
      inversion Hl.
Qed.

Lemma lookupGVMap_in : forall m id0,
  id0 `in` dom m ->
  exists gv0, lookupGVMap m id0 = Some gv0.
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
      exists g.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) a a); auto.
        contradict n; auto.

      simpl.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst; auto.
        exists g. auto.
Qed.

Lemma lookupEnv_replaceEnv_None_eq : forall lc gl id0 lc' gl' gv1,
  lookupEnv lc gl id0 = None ->
  replaceEnv lc gl id0 gv1 = (lc', gl') ->
  lookupEnv lc' gl' id0 = None.
Proof.
  intros lc gl id0 lc' gl' gv1 Hl Hr.
  unfold replaceEnv in Hr.
  unfold lookupEnv in *.
  destruct (AtomSetProperties.In_dec id0 (dom lc)).
    inversion Hr; subst.
    apply lookupGVMap_in in i0.
    destruct i0 as [gv0 i0].
    rewrite i0 in Hl. 
    inversion Hl.

    rewrite lookupGVMap_notin in Hl; auto.
    destruct (AtomSetProperties.In_dec id0 (dom gl)).
      apply lookupGVMap_in in i0.
      destruct i0 as [gv0 i0].
      rewrite i0 in Hl. 
      inversion Hl.

      inversion Hr; subst. clear Hr.
      rewrite lookupGVMap_notin; auto.
Qed.

Lemma lookupEnv_replaceEnv_neq : forall id0 id1 lc gl gv0 lc' gl',
  replaceEnv lc gl id0 gv0 = (lc', gl') ->
  id1 <> id0 ->
  lookupEnv lc gl id1 = lookupEnv lc' gl' id1.
Proof.
  intros id0 id1 lc gl ogv0 lc' gl' HreplaceEnv id1_isnt_id0.
  unfold replaceEnv in HreplaceEnv.
  unfold lookupEnv.
  destruct (@AtomSetProperties.In_dec id0 (dom lc)) as [id0_in_lc | id0_notin_lc].
    inversion HreplaceEnv; subst. clear HreplaceEnv.
    rewrite <- lookupGVMap_updateGVMap_neq; auto.

    destruct (@AtomSetProperties.In_dec id0 (dom gl)) as [id0_in_gl | id0_notin_gl].
      inversion HreplaceEnv; subst. clear HreplaceEnv.
      rewrite <- lookupGVMap_updateGVMap_neq; auto.
    
      inversion HreplaceEnv; subst. auto.
Qed. 

Lemma updateGVMap_in_dom_eq : forall m id0 gv0,
  id0 `in` dom m ->
  dom m [=] dom (updateGVMap m id0 gv0).
Proof.
  induction m; intros; simpl.
    fsetdec.

    destruct a.
    assert (id0 = a \/ id0 `in` dom m) as J.
      simpl in H.
      fsetdec.
    destruct J as [EQ | J]; subst.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) a a).
        simpl. fsetdec.
        contradict n; auto.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst.
        simpl. fsetdec.

        simpl. rewrite <- IHm; auto. fsetdec.
Qed.

Lemma updateGVMap_in_uniq : forall m id0 gv0,
  uniq m ->
  id0 `in` dom m ->
  uniq (updateGVMap m id0 gv0).
Proof.
  intros m id0 gv0 Uniq InDom.
  induction Uniq; simpl; auto.
  destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 x); subst; auto.
    assert (id0 = x \/ id0 `in` dom E) as J.
      simpl in InDom.
      fsetdec.
    destruct J as [EQ | J]; subst.
      contradict n; auto.
      simpl_env.
      apply uniq_push; auto.
        rewrite <- updateGVMap_in_dom_eq; auto.
Qed.

Lemma replaceEnv_uniq : forall id0 gv0 lc gl lc' gl',
  uniq lc ->
  uniq gl ->
  replaceEnv lc gl id0 gv0 = (lc', gl') ->
  uniq lc' /\ uniq gl'.
Proof.
  intros id0 gv0 lc gl lc' gl' Uniqc Uniqg Hr.
  unfold replaceEnv in Hr.
  destruct (@AtomSetProperties.In_dec id0 (dom lc)) as [id0_in_lc | id0_notin_lc].
    inversion Hr; subst. clear Hr.
    split; auto using updateGVMap_in_uniq.

    destruct (@AtomSetProperties.In_dec id0 (dom gl)) as [id0_in_gl | id0_notin_gl].
      inversion Hr; subst. clear Hr.
      split; auto using updateGVMap_in_uniq.

      inversion Hr; subst. split; auto.
Qed.

Lemma exists_deleteEnv : forall lc gl i0, 
  exists lc2, exists gl2, deleteEnv lc gl i0 = (lc2, gl2).
Proof.
  intros lc gl i0.
  unfold deleteEnv.
  exists (deleteGVMap lc i0). 
  exists (deleteGVMap gl i0). auto.
Qed.   

Lemma lookupEnv_deleteEnv_eq : forall lc gl id0 lc' gl',
  uniq gl ->
  uniq lc ->
  deleteEnv lc gl id0 = (lc', gl') ->
  lookupEnv lc' gl' id0 = None.
Proof.
  intros lc gl id0 lc' gl' Huniqc Huniqg HdeleteEnv.
  unfold deleteEnv in HdeleteEnv.
  unfold lookupEnv.
  inversion HdeleteEnv; subst. clear HdeleteEnv.
  rewrite lookupGVMap_deleteGVMap_eq; auto.
  rewrite lookupGVMap_deleteGVMap_eq; auto.
Qed.  

Lemma lookupGVMap_deleteGVMap_neq : forall m id0 id1,
  id0 <> id1 ->
  lookupGVMap (deleteGVMap m id0) id1 = lookupGVMap m id1.
Proof.
  induction m; intros id0 id1 id0_isnt_id1; simpl; auto.
  destruct a.
  destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 i0); subst.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst; auto.
      contradict id0_isnt_id1; auto.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst; simpl.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) i0 i0); subst; auto.
        contradict n0; auto.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst; auto.
        contradict n0; auto.
Qed.

Lemma lookupEnv_deleteEnv_neq : forall lc gl id0 lc' gl' id1,
  deleteEnv lc gl id0 = (lc', gl') ->
  id0 <> id1 ->
  lookupEnv lc gl id1 = lookupEnv lc' gl' id1.
Proof.
  intros lc gl id0 lc' gl' id1 HdeleteEnv id0_isnt_id1.
  unfold deleteEnv in HdeleteEnv.
  inversion HdeleteEnv; subst. clear HdeleteEnv.
  unfold lookupEnv.
  rewrite lookupGVMap_deleteGVMap_neq; auto.
  rewrite lookupGVMap_deleteGVMap_neq; auto.
Qed.  

Lemma deleteGVMap_dom_sub : forall m id0,
  dom (deleteGVMap m id0) [<=] dom m.
Proof.
  induction m; intros; simpl.
    fsetdec.

    destruct a.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 i0); subst.
      fsetdec.

      simpl. 
      assert (J:=@IHm id0).
      fsetdec.
Qed.

Lemma deleteGVMap_uniq : forall m id0,
  uniq m ->
  uniq (deleteGVMap m id0).
Proof.
  intros m id0 Uniq.
  induction Uniq; simpl; auto.
  destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 x); subst; auto.
    simpl_env.
    assert (J:=@deleteGVMap_dom_sub E id0).
    apply uniq_push; auto.
Qed.

Lemma deleteEnv_uniq : forall lc gl id0 lc' gl',
  uniq lc ->
  uniq gl ->
  deleteEnv lc gl id0 = (lc', gl') ->
  uniq lc' /\ uniq gl'.
Proof.
  intros lc gl id0 lc' gl' Huniqc Huniqg Hd.
  unfold deleteEnv in Hd.  
  inversion Hd; subst.
  split; auto using deleteGVMap_uniq.
Qed.

Lemma exists_rollbackEnv : forall lc gl i0 lc0 gl0, 
  exists lc2, exists gl2, rollbackEnv lc gl i0 lc0 gl0 = (lc2, gl2).
Proof.
  intros lc gl i0 lc0 gl0.
  unfold rollbackEnv.
  destruct (lookupEnv lc0 gl0 i0).
    apply exists_replaceEnv.
    apply exists_deleteEnv.
Qed.   

Lemma rollbackEnv_uniq : forall id0 lc0 gl0 lc gl lc' gl',
  uniq lc ->
  uniq gl ->
  rollbackEnv lc gl id0 lc0 gl0 = (lc', gl') ->
  uniq lc' /\ uniq gl'.
Proof.
  intros id0 lc0 gl0 lc gl lc' gl' Huniqc Huniqg Hr.
  unfold rollbackEnv in Hr.
  destruct (lookupEnv lc0 gl0 id0).
    apply replaceEnv_uniq in Hr; auto.
    apply deleteEnv_uniq in Hr; auto.
Qed.     

Lemma lookupEnv_rollbackEnv_neq : forall lc gl id0 lc0 gl0 lc' gl' id1,
  rollbackEnv lc gl id0 lc0 gl0 = (lc', gl') ->
  id0 <> id1 ->
  lookupEnv lc gl id1 = lookupEnv lc' gl' id1.
Proof.
  intros lc gl id0 lc0 gl0 lc' gl' id1 Hrollback id0_isnt_id1.
  unfold rollbackEnv in Hrollback.
  remember (lookupEnv lc0 gl0 id0) as ogv0.
  destruct ogv0.
    eapply lookupEnv_replaceEnv_neq; eauto.
    eapply lookupEnv_deleteEnv_neq; eauto.
Qed.

Lemma lookupEnv_rollbackEnv_Some_eq : forall lc gl id0 lc0 gl0 lc' gl' gv0,
  uniq lc ->
  uniq gl ->
  rollbackEnv lc gl id0 lc0 gl0 = (lc', gl') ->
  lookupEnv lc gl id0 = Some gv0 ->
  lookupEnv lc' gl' id0 = lookupEnv lc0 gl0 id0.
Proof.
  intros lc gl id0 lc0 gl0 lc' gl' gv0 Huniqc Huniqg Hrollback HlookupEnv.
  unfold rollbackEnv in Hrollback.
  remember (lookupEnv lc0 gl0 id0) as ogv0.
  destruct ogv0.
    rewrite Heqogv0.
    apply lookupEnv_replaceEnv_Some_eq with (gv0:=gv0) in Hrollback; auto.
    rewrite Hrollback. auto.

    apply lookupEnv_deleteEnv_eq in Hrollback; auto.
Qed.

Lemma lookupEnv_rollbackEnv_None_eq : forall lc gl id0 lc0 gl0 lc' gl',
  uniq lc ->
  uniq gl ->
  rollbackEnv lc gl id0 lc0 gl0 = (lc', gl') ->
  lookupEnv lc gl id0 = None ->
  lookupEnv lc' gl' id0 = None.
Proof.
  intros lc gl id0 lc0 gl0 lc' gl' Huniqc Huniqg Hrollback HlookupEnv.
  unfold rollbackEnv in Hrollback.
  remember (lookupEnv lc0 gl0 id0) as ogv0.
  destruct ogv0.
    apply lookupEnv_replaceEnv_None_eq in Hrollback; auto.

    apply lookupEnv_deleteEnv_eq in Hrollback; auto.
Qed.

(**************************************)
(** Convert const to GV with storesize, and look up GV from operands. *)

Fixpoint _const2GV (TD:layouts) (c:const) : option (GenericValue*typ) := 
match c with
| const_int sz n => Some (nat2GV TD sz n, typ_int sz)
| const_undef t =>  do gv <- undef2GV TD t; Some (gv, t)
| const_null t =>   Some (ptr2GV TD null, t)
| const_arr lc => _list_const_arr2GV TD lc
| const_struct lc =>
         match (_list_const_struct2GV TD lc) with
         | None => None
         | Some ((gv, t), al) => 
           match (length gv) with
           | 0 => Some (muninits al, t)
           | _ => Some (gv++muninits (al-length gv), t)
           end
         end
end
with _list_const_arr2GV (TD:layouts) (cs:list_const) : option (GenericValue*typ) := 
match cs with
| Nil_list_const => Some (nil, typ_int 0)
| Cons_list_const c lc' =>
  match (_list_const_arr2GV TD lc', _const2GV TD c) with
  | (Some (gv, t), Some (gv0,t0)) =>
             match (getTypeAllocSize TD t0) with
             | Some sz0 => Some ((gv++gv0)++muninits (sz0 - length gv0), t0)
             | None => None 
             end
  | _ => None
  end
end
with _list_const_struct2GV (TD:layouts) (cs:list_const) : option (GenericValue*typ*align) := 
match cs with
| Nil_list_const => Some ((nil, typ_int 0), 0)
| Cons_list_const c lc' =>
  match (_list_const_struct2GV TD lc', _const2GV TD c) with
  | (Some (gv, t, struct_al), Some (gv0,t0)) =>
             match (getABITypeAlignment TD t0, getTypeAllocSize TD t0) with
             | (Some sub_al, Some sub_sz) => 
               match (le_lt_dec sub_al struct_al) with
               | left _ (* struct_al <= sub_al *) =>
                 Some (
                  (gv++
                  (muninits (sub_al - length gv0))++
                  gv0++
                  (muninits (sub_sz - length gv0)),
                  t0),
                  sub_al
                 )
               | right _ (* sub_al < struct_al *) =>
                 Some (
                  (gv++
                  (muninits (sub_al - length gv0))++
                  gv0++
                  (muninits (sub_sz - length gv0)),
                  t0),
                  struct_al
                 )
               end
             | _ => None 
             end
  | _ => None
  end
end
.

Definition const2GV (TD:layouts) (c:const) : option GenericValue :=
match (_const2GV TD c) with
| None => None
| Some (gv, t) => Some gv
end.

Definition getOperandValue (TD:layouts) (v:value) (locals:GVMap) (globals:GVMap) : option GenericValue := 
match v with
| value_id id => lookupEnv locals globals id 
| value_const c => (const2GV TD c)
end.

Definition getOperandInt (TD:layouts) (sz:nat) (v:value) (locals:GVMap) (globals:GVMap) : option nat := 
match (getOperandValue TD v locals globals) with
| Some gi => (GV2nat TD sz gi)
| None => None
end.

Definition isOperandUndef (TD:layouts) (t:typ) (v:value) (locals:GVMap) (globals:GVMap) : Prop  := 
match (getOperandValue TD v locals globals) with
| Some gi => isGVUndef TD t gi
| None => False
end.

Definition getOperandPtr (TD:layouts) (v:value) (locals:GVMap) (globals:GVMap) : option mptr := 
match (getOperandValue TD v locals globals) with
| Some gi => GV2ptr TD (getPointerSize TD) gi
| None => None
end.

Definition getOperandPtrInBits (TD:layouts) (s:sz) (v:value) (locals:GVMap) (globals:GVMap) : option mptr := 
match (getOperandValue TD v locals globals) with
| Some gi => GV2ptr TD s gi
| None => None
end.

(**************************************)
(* conversion between different lists *)

Fixpoint params2OpGVs (TD:layouts) (lp:params) (locals:GVMap) (globals:GVMap) : list (option GenericValue):=
match lp with
| nil => nil
| (_, v)::lp' => getOperandValue TD v locals globals::params2OpGVs TD lp' locals globals
end.

Fixpoint opGVs2GVs (lg:list (option GenericValue)) : list GenericValue :=
match lg with
| nil => nil
| (Some g)::lg' => g::opGVs2GVs lg'
| _::lg' => opGVs2GVs lg'
end.

Definition params2GVs (TD:layouts) (lp:params) (locals:GVMap) (globals:GVMap) := 
  opGVs2GVs (params2OpGVs TD lp locals globals).

Fixpoint values2GVs (TD:layouts) (lv:list_value) (locals:GVMap) (globals:GVMap) : option (list GenericValue):=
match lv with
| Nil_list_value => Some nil
| Cons_list_value v lv' => 
  match (getOperandValue TD v locals globals) with
  | Some GV => 
    match (values2GVs TD lv' locals globals) with
    | Some GVs => Some (GV::GVs)
    | None => None
    end
  | None => None
  end
end.

Fixpoint intValues2Nats (TD:layouts) (lv:list_value) (locals:GVMap) (globals:GVMap) : option (list nat):=
match lv with
| Nil_list_value => Some nil
| Cons_list_value v lv' => 
  match (getOperandValue TD v locals globals) with
  | Some GV => 
    match (GV2nat TD 32 GV) with
    | Some n =>
      match (intValues2Nats TD lv' locals globals) with
      | Some ns => Some (n::ns)
      | None => None
      end
    | None => None
    end
  | None => None
  end
end.

Fixpoint intConsts2Nats (TD:layouts) (lv:list_const) : option (list nat):=
match lv with
| Nil_list_const => Some nil
| Cons_list_const (const_int 32 n) lv' => 
  match (GV2nat TD 32 (nat2GV TD 32 n)) with
  | Some n =>
    match (intConsts2Nats TD lv') with
    | Some ns => Some (n::ns)
    | None => None
    end
  | None => None
  end
| _ => None
end.

Fixpoint GVs2Nats (TD:layouts) (lgv:list GenericValue) : option (list nat):=
match lgv with
| nil => Some nil
| gv::lgv' => 
    match (GV2nat TD 32 gv) with
    | Some n =>
      match (GVs2Nats TD lgv') with
      | Some ns => Some (n::ns)
      | None => None
      end
    | None => None
    end
end.

(**************************************)
(* helping functions *)

Fixpoint _initializeFrameValues (la:args) (lg:list GenericValue) (locals:GVMap) : GVMap :=
match (la, lg) with
| ((_, id)::la', g::lg') => updateAddGVMap (_initializeFrameValues la' lg' locals) id g
| _ => locals
end.

Definition initLocals (la:args) (lg:list GenericValue): GVMap := 
_initializeFrameValues la lg nil.

Definition getEntryBlock (fd:fdef) : option block :=
match fd with
| fdef_intro _ (b::_) => Some b
| _ => None
end.

Definition getEntryCmds (b:block) : cmds :=
match b with
| block_intro _ _ lc _ => lc
end.

(* FIXME : bounds check *)
Definition extractGenericValue (TD:list layout)(t:typ) (gv : GenericValue) (cidxs : list_const) : option GenericValue :=
match (intConsts2Nats TD cidxs) with
| None => None 
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some o => mget TD gv o t
  | None => None
  end
end.

Definition insertGenericValue (TD:layouts) (t:typ) (gv:GenericValue)
  (cidxs:list_const) (t0:typ) (gv0:GenericValue) : option GenericValue :=
match (intConsts2Nats TD cidxs) with
| None => None 
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some o => mset TD gv o t0 gv0
  | None => None
  end
end.

Definition GEP (TD:layouts) (locals globals:GVMap) (t:typ) (ma:mptr) (vidxs:list_value) (inbounds:bool) : option mptr :=
match (intValues2Nats TD vidxs locals globals) with
| None => None 
| Some idxs => mgep TD t ma idxs
end.

Definition mbop (TD:layouts) (op:bop) (bsz:sz) (gv1 gv2:mvalue) : option mvalue :=
match op with
| bop_add => 
  match (GV2nat TD bsz gv1, GV2nat TD bsz gv2) with
  | (Some i1, Some i2) => Some (nat2mvalue TD bsz (i1+i2))
  | _ => None
  end
| _ => None
end.

Definition BOP (TD:layouts) (lc gl:GVMap) (op:bop) (bsz:sz) (v1 v2:value) : option mvalue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => mbop TD op bsz gv1 gv2
| _ => None
end
.

Definition mcast (TD:layouts) (op:castop) (t1:typ) (gv1:mvalue) (t2:typ) : option mvalue :=
match op with
| castop_inttoptr => 
  match (t1, t2) with
  | (typ_int sz1, typ_pointer _) => 
    match (GV2ptr TD sz1 gv1) with
    | Some mp1 => Some (ptr2GV TD mp1)
    | None => None
    end
  | _ => None
  end
| castop_ptrtoint =>
  match (t1, t2) with
  | (typ_pointer _, typ_int sz2) => 
    match (GV2ptr TD (getPointerSize TD) gv1) with
    | Some mp1 => Some (mptr2mvalue TD mp1 sz2)
    | None => None
    end
  | _ => None
  end
| castop_bitcase => Some gv1
end.

Definition CAST (TD:layouts) (lc gl:GVMap) (op:castop) (t1:typ) (v1:value) (t2:typ) : option mvalue :=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mcast TD op t1 gv1 t2
| _ => None
end
.

Definition mext (TD:layouts) (op:extop) (t1:typ) (gv1:mvalue) (t2:typ) : option mvalue :=
match op with
| extop_z => 
  match (t1, t2) with
  | (typ_int sz1, typ_int sz2) => Some gv1
  | _ => None
  end
| extop_s => 
  match (t1, t2) with
  | (typ_int sz1, typ_int sz2) => Some gv1
  | _ => None
  end
end.

Definition EXT (TD:layouts) (lc gl:GVMap) (op:extop) (t1:typ) (v1:value) (t2:typ) : option mvalue :=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mext TD op t1 gv1 t2
| _ => None
end
.

Definition micmp (TD:layouts) (c:cond) (t:typ) (gv1 gv2:mvalue) : option mvalue :=
match c with
| cond_eq =>
  match t with
  | typ_int sz => None
  | typ_pointer _ => None
  | _ => None
  end
| cond_ne => None
| cond_ugt => None
| cond_uge => None
| cond_ult => None
| cond_ule => None
| cond_sgt => None
| cond_sge => None
| cond_slt => None
| cond_sle => None
end.

Definition ICMP (TD:layouts) (lc gl:GVMap) (c:cond) (t:typ) (v1 v2:value) : option mvalue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => micmp TD c t gv1 gv2
| _ => None
end.

Lemma BOP_inversion : forall TD lc gl b s v1 v2 gv,
  BOP TD lc gl b s v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    mbop TD b s gv1 gv2 = Some gv.
Proof.
  intros TD lc gl b s v1 v2 gv HBOP.
  unfold BOP in HBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HBOP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HBOP].
      remember (mbop TD b s g g0) as R.
      destruct R; inversion HBOP; subst.
        exists g. exists g0. auto.
Qed.

Lemma getOperandPtr_inversion : forall TD lc gl v mptr,
  getOperandPtr TD v lc gl = Some mptr ->
  exists gv,
    getOperandValue TD v lc gl = Some gv /\
    GV2ptr TD (getPointerSize TD) gv = Some mptr.
Proof.
  intros TD lc gl v mptr HgetOperandPtr.
  unfold getOperandPtr in HgetOperandPtr.
  remember (getOperandValue TD v lc gl) as ogv.
  destruct ogv; try solve [inversion HgetOperandPtr].
    exists g. auto.
Qed.

Lemma getOperandInt_inversion : forall TD sz lc gl v n,
  getOperandInt TD sz v lc gl = Some n ->
  exists gv,
    getOperandValue TD v lc gl = Some gv /\
    GV2nat TD sz gv = Some n.
Proof.
  intros TD sz0 lc gl v mptr HgetOperandInt.
  unfold getOperandInt in HgetOperandInt.
  remember (getOperandValue TD v lc gl) as ogv.
  destruct ogv; try solve [inversion HgetOperandInt].
    exists g. auto.
Qed.

Lemma CAST_inversion : forall TD lc gl op t1 v1 t2 gv,
  CAST TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mcast TD op t1 gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HCAST.
  unfold CAST in HCAST.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HCAST].
    remember (mcast TD op t1 g t2) as R.
    destruct R; inversion HCAST; subst.
      exists g. auto.
Qed.

Lemma EXT_inversion : forall TD lc gl op t1 v1 t2 gv,
  EXT TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mext TD op t1 gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HEXT.
  unfold EXT in HEXT.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HEXT].
    remember (mext TD op t1 g t2) as R.
    destruct R; inversion HEXT; subst.
      exists g. auto.
Qed.

Lemma ICMP_inversion : forall TD lc gl cond t v1 v2 gv,
  ICMP TD lc gl cond t v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    micmp TD cond t gv1 gv2 = Some gv.
Proof.
  intros TD lc gl cond0 t v1 v2 gv HICMP.
  unfold ICMP in HICMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HICMP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HICMP].
      remember (micmp TD cond0 t g g0) as R.
      destruct R; inversion HICMP; subst.
        exists g. exists g0. auto.
Qed.

Lemma GEP_inversion : forall (TD:layouts) (lc gl:GVMap) (t:typ) (ma:mptr) (vidxs:list_value) ib mptr0,
  GEP TD lc gl t ma vidxs ib = Some mptr0 ->
  exists idxs, intValues2Nats TD vidxs lc gl = Some idxs /\ mgep TD t ma idxs = Some mptr0.
Proof.
  intros.
  unfold GEP in H.
  remember (intValues2Nats TD vidxs lc gl) as oidxs.
  destruct oidxs; inversion H; subst.
  exists l0. auto.
Qed.

Lemma intValues2Nats_inversion : forall l0 lc gl TD ns0,
  intValues2Nats TD l0 lc gl = Some ns0 ->
  exists gvs0, 
    values2GVs TD l0 lc gl = Some gvs0 /\
    GVs2Nats TD gvs0 = Some ns0.
Proof.
  induction l0; intros; simpl in *.
    inversion H. exists nil. auto.

    remember (getOperandValue TD v lc gl) as ogv.
    destruct ogv; try solve [inversion H].
    remember (GV2nat TD 32 g) as on.
    destruct on; try solve [inversion H].
    remember (intValues2Nats TD l0 lc gl) as ons.
    destruct ons; inversion H; subst.
    symmetry in Heqons.
    apply IHl0 in Heqons.
    destruct Heqons as [gvs [J1 J2]].
    exists (g::gvs).
    rewrite J1. 
    split; auto.
      simpl. rewrite J2. rewrite <- Heqon. auto.
Qed.

Lemma values2GVs_GVs2Nats__intValues2Nats : forall l0 lc gl TD gvs0,
  values2GVs TD l0 lc gl = Some gvs0 ->
  GVs2Nats TD gvs0 = intValues2Nats TD l0 lc gl.
Proof.
  induction l0; intros lc gl TD gvs0 H; simpl in *.
    inversion H. auto.

    destruct (getOperandValue TD v lc gl); try solve [inversion H].
      remember (values2GVs TD l0 lc gl)as ogv.
      destruct ogv; inversion H; subst.
        rewrite <- IHl0 with (gvs0:=l1); auto.
Qed.

(* eq *)

Definition eqEnv lc1 gl1 lc2 gl2 := 
  forall i, lookupEnv lc1 gl1 i = lookupEnv lc2 gl2 i.

Lemma eqEnv_refl : forall lc gl,
  eqEnv lc gl lc gl.
Proof. unfold eqEnv. auto. Qed.

Lemma eqEnv_sym : forall lc1 gl1 lc2 gl2,
  eqEnv lc1 gl1 lc2 gl2 ->
  eqEnv lc2 gl2 lc1 gl1.
Proof. unfold eqEnv. auto. Qed.

Lemma eqEnv_trans : forall lc1 gl1 lc2 gl2 lc3 gl3,
  eqEnv lc1 gl1 lc2 gl2 ->
  eqEnv lc2 gl2 lc3 gl3 ->
  eqEnv lc1 gl1 lc3 gl3.
Proof. 
  unfold eqEnv. 
  intros.
  assert (J1:=@H i0).
  assert (J2:=@H0 i0).
  rewrite J1. auto.
Qed.