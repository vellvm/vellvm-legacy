(* Start CoqIDE at ./src *)
Add LoadPath "./ssa/ott".
Add LoadPath "./ssa/monads".
Add LoadPath "./ssa/compcert".
Add LoadPath "./ssa".
Add LoadPath "../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import trace.
Require Import assoclist.
Require Import ssa_props.
Require Import CoqListFacts.
Require Import symexe_def.
Require Import symexe_dec.

Export SimpleSE.

Definition subAL X lc1 lc2 := 
  forall i, i `in` dom lc1 -> lookupAL X lc1 i = lookupAL X lc2 i.

Notation "lc1 <<<= lc2" := (subAL _ lc1 lc2) (at level 70, no associativity).

Definition sub_sstate s1 s2 := 
  s1.(STerms) <<<= s2.(STerms) /\ s1.(SMem) = s2.(SMem) /\
  s1.(SFrame) = s2.(SFrame) /\ s1.(SEffects) = s2.(SEffects).

Notation "s1 <<= s2" := (sub_sstate s1 s2) (at level 70, no associativity).

Lemma lookupAL_app1 : forall X (lc1:list (atom*X)) lc2 i,
  i `in` dom lc1 ->
  lookupAL X lc1 i = lookupAL X (lc1++lc2) i.
Proof.
  induction lc1; intros lc2 i Hi_in_lc1.
    fsetdec.
    destruct a as (id, elt); simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i id); auto.
      apply IHlc1. fsetdec.
Qed.    

Lemma lookupAL_app2 : forall X lc1 (lc2:list (atom*X)) i,
  i `notin` dom lc1 ->
  lookupAL X lc2 i = lookupAL X (lc1++lc2) i.
Proof.
  induction lc1; intros lc2 i Hi_notin_lc1; auto.
    destruct a as (id, elt); simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i id); subst; eauto.
      fsetdec.
Qed.    

Lemma subAL_app : forall X (lc1:list (atom*X)) lc2 lc,
  lc1 <<<= lc ->
  lc2 <<<= lc ->
  lc1 ++ lc2 <<<= lc.
Proof.
  intros X lc1 lc2 lc Hlc1_nsub_lc Hlc2_nsub_lc.
  intros i i_in_lc12.
  simpl_env in i_in_lc12.
  apply in_dom_app_inv in i_in_lc12.
  assert (i `in`  dom lc1 \/ i `notin` dom lc1) as i_in_lc1_dec. fsetdec.
  destruct i_in_lc1_dec as [i_in_lc1 | i_notin_lc1].
    rewrite <- Hlc1_nsub_lc; auto.
    rewrite <- lookupAL_app1; auto.

    destruct i_in_lc12 as [i_in_lc1 | i_in_lc2].
      fsetdec.
      rewrite <- lookupAL_app2; auto.
Qed.

Lemma smap_sub_dec : forall (sm1 sm2:smap), 
  {sm1 <<<= sm2}+{~sm1 <<<= sm2}.
Proof.
  induction sm1.  
    intros. left. intros i i_in_nil. fsetdec. 

    intros. 
    destruct a as [id st1].
    remember (lookupAL _ sm2 id) as Lookup.
    destruct Lookup as [st2 | _].
      destruct (@sterm_dec st1 st2); subst.
        destruct (@IHsm1 sm2) as [sm1_sub_sm2 | sm1_nsub_sm2].
          left. simpl_env.
          apply subAL_app; auto.
            intros i Hi_in_dom. simpl in *.
            destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i id); subst.
              rewrite <- HeqLookup; auto.
              fsetdec.
          admit. (* uniqueness? Or, we can prove this by induction on the length
                    of sm1, and remove all elts with the key id from sm1 for the
                    inductive case. *)
        right. intro J. assert (H:=@J id). simpl in H.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id id); auto.
          rewrite <- HeqLookup in H. injection H; auto.
      right. intro J. assert (H:=@J id). simpl in H.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id id); auto.
        rewrite <- HeqLookup in H.
        assert (ret st1 = merror) as F. auto.
        inversion F.
Qed.

Lemma sstate_sub_dec : forall (sts1 sts2:sstate), {sts1<<=sts2} + {~sts1<<=sts2}.
Proof.
Ltac done_right := 
  right; intro J ; destruct J as [ J1 [J2 [J3 J4]]]; simpl in *; auto.

  destruct sts1 as [st1 sm1 sf1 se1].
  destruct sts2 as [st2 sm2 sf2 se2].
  destruct (@sterms_dec se1 se2); subst; try solve [auto | done_right].
  destruct (@sframe_dec sf1 sf2); subst; try solve [auto | done_right].
  destruct (@smem_dec sm1 sm2); subst; try solve [auto | done_right].
  destruct (@smap_sub_dec st1 st2); subst; try solve [left; split; auto | done_right].
Qed.

