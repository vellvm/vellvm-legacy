Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import ssa_static.
Require Import ssa_props.
Require Import ssa_analysis.
Require Import ssa_wf.
Require Import ssa_dynamic.
Require Import ndopsem.
Require Import sb_ds_def.
Require Import sb_ds_metadata.
Require Import sb_ns_def.
Require Import sbop_nsop.
Require Import Znumtheory.

Ltac zauto := auto with zarith.

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

Ltac repeat_bsplit :=
  repeat (bsplit; auto using eq_sumbool2bool_true).

Ltac zeauto := eauto with zarith.

Export LLVMgv.
Export SBnsop.

(*****************************************)
(* misc *)

Lemma updateValuesForNewBlock_spec4 : forall rvs lc x rm lc' rm' md,
  lookupAL _ rm x = None ->
  (lc', rm') = updateValuesForNewBlock rvs lc rm ->
  lookupAL _ rm' x = Some md ->
  exists gv, In (x, gv, Some md) rvs.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' gv Hlk Hupdate Hlk'.
    inv Hupdate. rewrite Hlk in Hlk'. inversion Hlk'.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk'; auto.
        inv Hlk'. eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk'; auto.
        eapply IHrvs in HeqR; eauto.
        destruct HeqR as [gv' HeqR]. 
        eauto.

      eapply IHrvs in HeqR; eauto.
      destruct HeqR as [gv' HeqR]. 
      eauto.
Qed.

Lemma updateValuesForNewBlock_spec6 : forall rvs lc x rm lc' rm' md,
  (lc', rm') = updateValuesForNewBlock rvs lc rm ->
  lookupAL _ rm' x = Some md ->
  lookupAL _ rm x = Some md \/
  exists id1, exists gv1, In (id1,gv1,Some md) rvs.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' md Hupdate Hlk.
    inv Hupdate. auto.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md1 ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk. 
        inv Hlk. right. exists x. exists g. auto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
        eapply IHrvs in HeqR; eauto.
        destruct HeqR as [J1 | [id1 [gv1 HeqR]]]; auto.
          right. exists id1. exists gv1. auto.

     eapply IHrvs in HeqR; eauto.
     destruct HeqR as [J1 | [id1 [gv1 HeqR]]]; auto.
       right. exists id1. exists gv1. auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec : forall ps TD b gl lc id1
    rm re gv1 opmd1,
  Some re = getIncomingValuesForBlockFromPHINodes TD ps b gl lc rm ->
  In (id1, gv1, opmd1) re ->
  In id1 (getPhiNodesIDs ps).
Proof.    
  induction ps; intros; simpl in *.
    inv H. inversion H0.

    destruct a.
    destruct (getValueViaBlockFromValuels l0 b); try solve [inversion H].   
    destruct (NDopsem.getOperandValue TD v lc gl); try solve [inversion H].   
    remember (getIncomingValuesForBlockFromPHINodes TD ps b gl lc rm) as R.
    destruct R; try solve [inv H].
    simpl.
    destruct (isPointerTypB t); inv H.
      destruct (SBopsem.get_reg_metadata TD gl rm v) as [[md mt]|]; inv H2.      
      simpl in H0.
      destruct H0 as [H0 | H0]; eauto.  
        inv H0; auto.

      simpl in H0.
      destruct H0 as [H0 | H0]; eauto.  
        inv H0; auto.
Qed.

Lemma updateValuesForNewBlock_spec1 : forall rvs lc x rm lc' rm' gv,
  lookupAL _ lc x = None ->
  (lc', rm') = updateValuesForNewBlock rvs lc rm ->
  lookupAL _ lc' x = Some gv ->
  exists omd, In (x, gv, omd) rvs.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' gv Hlk Hupdate Hlk'.
    inv Hupdate. rewrite Hlk in Hlk'. inversion Hlk'.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk'; auto.
        inv Hlk'. eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk'; auto.
        eapply IHrvs in HeqR; eauto.
        destruct HeqR as [omd HeqR]. eauto.

      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk'; auto.
        inv Hlk'. eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk'; auto.
        eapply IHrvs in HeqR; eauto.
        destruct HeqR as [omd HeqR]. eauto.
Qed.

Lemma updateValuesForNewBlock_spec5 : forall rvs lc x rm lc' rm' md,
  lookupAL _ rm x = Some md ->
  (lc', rm') = updateValuesForNewBlock rvs lc rm ->
  exists md, lookupAL _ rm' x = Some md.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' md Hlk Hupdate.
    inv Hupdate; eauto.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md1 ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq.
        eauto.

        rewrite <- lookupAL_updateAddAL_neq; auto.
        eapply IHrvs in HeqR; eauto.

      eapply IHrvs in HeqR; eauto.
Qed.

Lemma updateValuesForNewBlock_spec3 : forall rvs lc x rm lc' rm' gvx md,
  In (x, gvx, Some md) rvs ->
  (lc', rm') = updateValuesForNewBlock rvs lc rm ->
  exists md, lookupAL _ rm' x = Some md.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' gvx md Hin Hupdate.
    inversion Hin.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md1 ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq. eauto.

        rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct Hin as [Hin | Hin].
          inv Hin. contradict n; auto.
          eapply IHrvs in HeqR; eauto.

      destruct Hin as [Hin | Hin].
        inv Hin. 
        eapply IHrvs in HeqR; eauto.
Qed.

Lemma initializeFrameValues_spec1 : forall la lc1 rm1 x md lc2 rm2,
  lookupAL _ rm1 x = Some md ->
  (lc2, rm2) = _initializeFrameValues la nil lc1 rm1 ->
  exists md, lookupAL _ rm2 x = Some md.
Proof.
  induction la; simpl; intros lc1 rm1 x md lc2 rm2 Hlk Hinit.  
    inv Hinit. eauto.

    destruct a. destruct p.
    remember (_initializeFrameValues la nil lc1 rm1) as R.
    destruct R as [lc1' rm1'].
    destruct (isPointerTypB t); inv Hinit; eauto.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq; eauto.
        rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma initializeFrameValues_spec3 : forall la lc x rm lc' rm' md,
  (lc', rm') = _initializeFrameValues la nil lc rm ->
  lookupAL _ rm' x = Some md ->
  lookupAL _ rm x = Some md \/
  md = SBopsem.mkMD null null.
Proof.
  induction la; simpl; intros.
    inv H. auto.

    destruct a. destruct p.
    remember (_initializeFrameValues la nil lc rm) as R.
    destruct R as [lc1 rm1].
    destruct (isPointerTypB t); inv H.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in H0. 
        inv H0. auto.
      
        rewrite <- lookupAL_updateAddAL_neq in H0; auto.
        eapply IHla in HeqR; eauto. 
      eapply IHla in HeqR; eauto. 
Qed.

Lemma initializeFrameValues_spec2 : forall la ogvs lc x rm lc' rm' md,
  (lc', rm') = _initializeFrameValues la ogvs lc rm ->
  lookupAL _ rm' x = Some md ->
  lookupAL _ rm x = Some md \/
  md = SBopsem.mkMD null null \/
  exists gv1, In (gv1,Some md) ogvs.
Proof.
  induction la; simpl; intros ogvs lc x rm lc' rm' md Hinit Hlk.
    inv Hinit. auto.

    destruct a. destruct p.
    destruct ogvs.
      remember (_initializeFrameValues la nil lc rm) as R.
      destruct R as [lc1 rm1].
      destruct (isPointerTypB t); inv Hinit.
        destruct (eq_atom_dec i0 x); subst.
          rewrite lookupAL_updateAddAL_eq in Hlk. 
          inv Hlk. auto.

          rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
          eapply initializeFrameValues_spec3 in HeqR; eauto.
          destruct HeqR; auto.
        eapply initializeFrameValues_spec3 in HeqR; eauto.
        destruct HeqR; auto.

      destruct p.
      remember (_initializeFrameValues la ogvs lc rm) as R.
      destruct R as [lc1 rm1].
      destruct (isPointerTypB t); inv Hinit.
        destruct o as [[md1 ?]|]; inv H0.
          destruct (eq_atom_dec i0 x); subst.
            rewrite lookupAL_updateAddAL_eq in Hlk. 
            inv Hlk. right. right. exists g. simpl. auto.

            rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
            eapply IHla in HeqR; eauto.
            destruct HeqR as [HeqR | [HeqR | [gv1 HeqR]]]; auto.
              right. right. exists gv1. simpl. auto.

          destruct (eq_atom_dec i0 x); subst.
            rewrite lookupAL_updateAddAL_eq in Hlk. 
            inv Hlk. auto.

            rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
            eapply IHla in HeqR; eauto.
            destruct HeqR as [HeqR | [HeqR | [gv1 HeqR]]]; auto.
              right. right. exists gv1. simpl. auto.

        eapply IHla in HeqR; eauto.
        destruct HeqR as [HeqR | [HeqR | [gv1 HeqR]]]; auto.
          right. right. exists gv1. simpl. auto.
Qed.

(***********************************************)
(* wf_data *)

Lemma GV2ptr__cgv2gv : forall TD sz g b ofs t, 
  GV2ptr TD sz g = ret (Vptr b ofs) -> g = ? g # typ_pointer t ?.
Proof.
  intros TD sz g b ofs t J1.
  unfold GV2ptr in J1.    
  destruct g as [|[[] ?][|]]; inv J1.
  simpl. auto.
Qed.

Lemma get_const_metadata_gid__wf_data : forall S TD Mem0 gl t i0 gvb gve,
  wf_global_ptr S TD Mem0 gl ->
  wf_const S TD (const_gid t i0) (typ_pointer t) ->
  const2GV TD gl (const_castop castop_bitcast (const_gid t i0) p8) = ret gvb ->
  const2GV TD gl 
       (const_castop castop_bitcast
         (const_gep false (const_gid t i0)
            (Cons_list_const (const_int Size.ThirtyTwo 1) Nil_list_const)) p8)
       = ret gve ->
  wf_data TD Mem0 gvb gve.
Proof.
  intros S TD Mem0 gl t i0 gvb gve Hwfg Hwfc H2 H3.
  unfold const2GV in H3.
  remember (_const2GV TD gl 
    (const_castop castop_bitcast
      (const_gep false (const_gid t i0)
        (Cons_list_const (const_int Size.ThirtyTwo 1) Nil_list_const)) p8))
    as R0.
  destruct R0 as [[gv ?]|]; inv H3.
  unfold const2GV in H2.
  remember (_const2GV TD gl (const_castop castop_bitcast (const_gid t i0) p8)) 
    as R1.
  destruct R1 as [[gv' ?]|]; inv H2.
  unfold _const2GV in *.
  unfold mcast, mbitcast, p8 in *.
  remember (lookupAL GenericValue gl i0) as R'.
  destruct R'; try solve [inversion HeqR0].
  inv HeqR1.
  remember (getConstGEPTyp
              (Cons_list_const (const_int Size.ThirtyTwo 1) Nil_list_const)
              (typ_pointer t)) as R1.
  destruct R1; try solve [inversion HeqR0].
  unfold getConstGEPTyp in HeqR1.
  destruct (getSubTypFromConstIdxs Nil_list_const t); inv HeqR1.
  symmetry in HeqR'.
  assert (exists b, exists sz,
    GV2ptr TD (getPointerSize TD) g = Some (Values.Vptr b ((Int.zero 31))) /\
    getTypeAllocSize TD t = Some sz /\
    Mem.bounds Mem0 b = (0, Z_of_nat sz) /\
    b < Mem.nextblock Mem0 /\
    (blk_temporal_safe Mem0 b -> Mem.range_perm Mem0 b 0 (Z_of_nat sz) Writable))
    as J.
    eapply Hwfg; eauto.
  destruct J as [b [sz [J1 [J2 [J3 [J4 J5]]]]]].
  rewrite J1 in HeqR0.
  simpl in HeqR0.
  unfold mgetoffset in HeqR0.
  destruct TD.
  assert (exists ut2, Constant.typ2utyp l1 (typ_array 0%nat t) = 
    Some (typ_array 0%nat ut2) /\
    getTypeAllocSize (l0, l1) ut2 = getTypeAllocSize (l0, l1) t) as J.
    clear - Hwfc. inv Hwfc. 
    unfold Constant.unifiable_typ in H5.
    destruct H5 as [ut [H5 H6]].
    unfold Constant.typ2utyp in *.
    simpl. rewrite H5. simpl. rewrite <- H6. eauto.
  destruct J as [ut2 [J6 J7]].
  rewrite J6 in HeqR0. simpl in HeqR0.
  rewrite J7 in HeqR0. rewrite J2 in HeqR0. simpl in HeqR0.
  inv HeqR0.
  erewrite <- GV2ptr__cgv2gv with (g:=g); eauto.
  unfold wf_data. rewrite J1. simpl.
  destruct (zeq b b); auto.
    split; auto.  
    
    intro Htmp.
    apply J5 in Htmp.
    rewrite Int.signed_zero. 
    rewrite (Int.add_commut 31).
    rewrite (Int.add_zero 31).
    unfold INTEGER.to_Z. 
    assert (Z_of_nat sz * 1 = Z_of_nat sz) as EQ. zauto.
    rewrite EQ.
    intros z Hz.
    apply Htmp.
    assert (J:=@Int.signed_repr_ge_0 31 (Z_of_nat sz) (Z_of_nat_ge_0 sz)).
    zauto.
Qed.

Lemma eq_gv_is_wf_data : forall TD Mem gv bb bofs,
  bb < Mem.nextblock Mem ->
  GV2ptr TD (getPointerSize TD) gv = Some (Values.Vptr bb bofs) ->
  wf_data TD Mem gv gv.
Proof.
  intros TD Mem gv bb bofs H0 H.
  unfold wf_data.
  rewrite H.
  destruct (zeq bb bb); auto.
  split; auto.
    intros Hwfb ofs J.
    contradict J; zauto.
Qed.

Lemma wf_rmetadata__get_const_metadata : forall S TD gl Mem0 rm c gvb gve c0 c1
   ct',
  wf_global_ptr S TD Mem0 gl ->
  wf_const S TD c ct' ->
  wf_rmetadata TD Mem0 rm ->
  get_const_metadata c = Some (c0,c1) ->
  const2GV TD gl c0 = Some gvb ->
  const2GV TD gl c1 = Some gve ->
  wf_data TD Mem0 gvb gve.
Proof.
  induction c; intros gvb gve cc0 cc1 ct' Hwfg Hwfc Hwfr H1 H2 H3; 
    try solve [inversion H1].

  inv Hwfc.
  destruct t; inv H1; 
    try solve [ 
      eapply get_const_metadata_gid__wf_data; eauto using wf_const_gid
    ].

    unfold const2GV in H2, H3.
    remember (_const2GV TD gl (const_castop castop_bitcast (const_gid 
      (typ_function t l0 v) i0) p8)) as R.
    destruct R; try solve [inversion H2 | inversion H3].
    destruct p. inv H2. inv H3.
    unfold GV2ptr.
    unfold _const2GV in HeqR.
    remember (lookupAL GenericValue gl i0) as R1.
    destruct R1; inv HeqR.
    assert (exists b, exists sz,
      GV2ptr TD (getPointerSize TD) g0 = Some (Values.Vptr b ((Int.zero 31))) /\
      getTypeAllocSize TD (typ_function t l0 v) = Some sz /\
      Mem.bounds Mem0 b = (0, Z_of_nat sz) /\
      b < Mem.nextblock Mem0 /\
      (blk_temporal_safe Mem0 b -> Mem.range_perm Mem0 b 0 (Z_of_nat sz) Writable))
      as J.
      eapply Hwfg; eauto using wf_const_gid.
    destruct J as [b [sz [J1 [J2 [J3 [J4 J5]]]]]].
    unfold p8.
    erewrite <- GV2ptr__cgv2gv; eauto.
    eapply eq_gv_is_wf_data; eauto.

  simpl in H1.
  destruct c; try solve [inversion H1].
  destruct t; try solve [inversion H1].
  inv Hwfc.
  eapply IHc; eauto.
     
  inv Hwfc.
  simpl in H1; eauto.
Qed.

(********************************************)
(* wf_rmetadata *)

Lemma returnUpdateLocals__wf_rmetadata : forall los nts Result lc rm gl c' lc' 
    rm' Mem0 Mem' als lc'' rm'' S Ps f rt
  (Hwfg : wf_global_ptr S (los, nts) Mem0 gl)
  (Hwfv : wf_value S (module_intro los nts Ps) f Result rt)
  (H0 : free_allocas (los, nts) Mem0 als = ret Mem')
  (H1 : returnUpdateLocals (los, nts) c' rt Result lc lc' rm rm' gl =
       ret (lc'', rm''))
  (Hwfm1' : wf_rmetadata (los, nts) Mem0 rm)
  (Hwfm2' : wf_rmetadata (los, nts) Mem0 rm'),
  wf_rmetadata (los, nts) Mem' rm''.
Proof.
  intros.
  unfold returnUpdateLocals, returnResult in H1.
  assert (wf_rmetadata (los, nts) Mem' rm') as Hwfm.
    eauto using free_allocas_preserves_wf_rmetadata.
  remember (NDopsem.getOperandValue (los, nts) Result lc gl) as R1.
  destruct R1; try solve [inv H1; auto].
  destruct (isPointerTypB rt).
    remember (get_reg_metadata (los, nts) gl rm Result) as R3.
    destruct R3 as [[md ?]|]; try solve [inv H1; auto].
    destruct c'; try solve [inv H1; auto].
    destruct n; try solve [inv H1; auto].
    unfold SBopsem.isReturnPointerTypB, isPointerTypB in H1.
    destruct t; try solve [inv H1; auto].
    destruct t; inv H1; auto.
      intros x gvb gve Hlk.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk.
        inv Hlk. symmetry in HeqR3.
        eapply wf_rmetadata__get_reg_metadata with (rm:=rm); eauto.
          eapply free_allocas_preserves_wf_global_ptr in H0; eauto.
          eapply free_allocas_preserves_wf_rmetadata in H0; eauto.
 
        rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto.

    destruct c'; try solve [inv H1; auto].
    destruct n; try solve [inv H1; auto].
    unfold SBopsem.isReturnPointerTypB, isPointerTypB in H1.
    destruct t; try solve [inv H1; auto].
    destruct t; inv H1; auto.
      intros x gvb gve Hlk.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk.
        inv Hlk. apply null_is_wf_data.

        rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes__wf_rmetadata : forall los nts M f b
  ps gl lc rm S PNs re id1 gv1 bv1 ev1 b' ifs
  (Hwfg : wf_global_ptr S (los, nts) M gl)
  (Hwfps : wf_phinodes ifs S (module_intro los nts ps) f b' PNs),
  NoDup (getPhiNodesIDs PNs) ->
  wf_rmetadata (los, nts) M rm ->
  getIncomingValuesForBlockFromPHINodes (los, nts) PNs b gl lc rm = Some re ->
  In (id1,gv1,Some (mkMD bv1 ev1)) re ->
  wf_data (los, nts) M bv1 ev1.
Proof.
  induction PNs; simpl; intros re id1 gv1 bv1 ev1 b' ifs Hwfg Hwfps Huniq 
    Hwfr Hget Hin.
    inv Hget. inversion Hin.

    inv Huniq. inv Hwfps.
    destruct a.
    remember (getValueViaBlockFromValuels l0 b) as R0.
    destruct R0; try solve [inv Hget].
    destruct (NDopsem.getOperandValue (los,nts) v lc gl); try solve [inv Hget].
    remember (getIncomingValuesForBlockFromPHINodes (los,nts) PNs b gl lc rm) 
      as R.
    destruct R; try solve [inv Hget].
    destruct (isPointerTypB t); inv Hget.
      remember (get_reg_metadata (los,nts) gl rm v) as R1.
      destruct R1 as [[bv ev]|]; inv H0.
      simpl in Hin.
      destruct Hin as [Hin | Hin]; eauto.
        inv Hin. 
        symmetry in HeqR1.
        inv H8.
        destruct b. simpl in HeqR0.
        eapply wf_value_list__getValueViaLabelFromValuels__wf_value in H4; eauto.
        eapply wf_rmetadata__get_reg_metadata in HeqR1; eauto.

      simpl in Hin.
      destruct Hin as [Hin | Hin]; eauto.
        inv Hin.
Qed.

Lemma updateValuesForNewBlock__wf_rmetadata_aux : forall TD M rvs rm lc,
  (forall id1 gv1 bv1 ev1, 
    In (id1,gv1,Some (mkMD bv1 ev1)) rvs ->
    wf_data TD M bv1 ev1) ->
  forall rvs2 rvs1 lc1 rm1 lc2 rm2,
  rvs = rvs1 ++ rvs2 ->
  updateValuesForNewBlock rvs1 lc rm = (lc1, rm1) ->
  wf_rmetadata TD M rm1 ->
  updateValuesForNewBlock rvs2 lc1 rm1 = (lc2, rm2) ->
  wf_rmetadata TD M rm2.
Proof.
  intros TD M rvs rm lc Hprop.
  induction rvs2; simpl; intros rvs1 lc1 rm1 lc2 rm2 Heq Hupdate1 Hrmap1
    Hupdate2; subst.
    inv Hupdate2. auto.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs2 lc1 rm1) as R. 
    destruct R as [lc2' rm2'].
    destruct o as [[bv ev]|]; inv Hupdate2.
      intros x gvb gve Hlk.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk. inv Hlk.
        apply Hprop with (id1:=x)(gv1:=g); eauto.
          apply in_or_app. simpl. auto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
        eapply updateValuesForNewBlock_spec6 in Hlk; eauto.
        destruct Hlk as [Hlk | [id1 [gv1 Hin]]]; eauto.
          eapply Hprop; eauto.
            apply in_or_app. simpl. eauto.
                       
      intros x gvb gve Hlk.
      eapply updateValuesForNewBlock_spec6 in Hlk; eauto.
      destruct Hlk as [Hlk | [id1 [gv1 Hin]]]; eauto.
        eapply Hprop; eauto.
          apply in_or_app. simpl. eauto.
Qed.

Lemma updateValuesForNewBlock__wf_rmetadata : forall rvs TD M lc rm lc' rm',
  (forall id1 gv1 bv1 ev1, 
    In (id1,gv1,Some (mkMD bv1 ev1)) rvs ->
    wf_data TD M bv1 ev1) ->
  wf_rmetadata TD M rm ->
  updateValuesForNewBlock rvs lc rm = (lc', rm') ->
  wf_rmetadata TD M rm'.
Proof.
  intros.
  eapply updateValuesForNewBlock__wf_rmetadata_aux with (rvs1:=nil)(lc1:=lc)
    (rm1:=rm)(rvs2:=rvs); simpl; eauto.
Qed.

Lemma switchToNewBasicBlock__wf_rmetadata : forall S M b1 b2 gl lc rm lc' rm' 
    F ifs los nts Ps,
  wf_global_ptr S (los, nts) M gl ->
  wf_fdef ifs S (module_intro los nts Ps) F ->
  uniqFdef F ->
  blockInFdefB b1 F ->
  wf_rmetadata (los, nts) M rm ->
  switchToNewBasicBlock (los, nts) b1 b2 gl lc rm = Some (lc', rm') ->
  wf_rmetadata (los, nts) M rm'.
Proof.
  intros S M b1 b2 gl lc rm lc' rm' F ifs los nts m Hwfg HwfF Huniq HBinF Hwfr 
    Hswitch.
  unfold switchToNewBasicBlock in Hswitch.
  remember (getIncomingValuesForBlockFromPHINodes (los, nts)  
             (getPHINodesFromBlock b1) b2 gl lc rm) as R.
  destruct R; inv Hswitch.
  eapply updateValuesForNewBlock__wf_rmetadata; eauto.
  intros. 
  inv HwfF.
  apply wf_blocks__wf_block with (b:=b1) in H8; auto.
  destruct b1. inv H8.
  eapply getIncomingValuesForBlockFromPHINodes__wf_rmetadata; eauto.

    apply uniqFdef__uniqBlockLocs in HBinF; auto.
    apply NoDup_inv in HBinF. destruct HBinF; auto.
Qed.

Lemma prop_metadata_preserves_wf_rmetadata : forall los nts Mem0 rm md gl S Ps
    f t id0 vp
  (H : get_reg_metadata (los, nts) gl rm vp = ret md)
  (Hwfg' : wf_global_ptr S (los, nts) Mem0 gl)
  (Hwfv : wf_value S (module_intro los nts Ps) f vp t)
  (Hwfr : wf_rmetadata (los, nts) Mem0 rm),
  wf_rmetadata (los, nts) Mem0 (updateAddAL metadata rm id0 md).
Proof.
  intros.
  intros i0 gvb gve J0.
  destruct (@id_dec id0 i0); subst.
    rewrite lookupAL_updateAddAL_eq in J0.
    inversion J0; subst. clear J0.
    eapply wf_rmetadata__get_reg_metadata in H; eauto.

    rewrite <- lookupAL_updateAddAL_neq in J0; auto.
    apply Hwfr in J0; auto.
Qed.

Lemma params2GVs__wf_rmetadata : forall S los nts Ps f M rm lc gl ps ogvs
  (Hwfvs : forall t1 v1, In (t1,v1) ps -> 
    wf_value S (module_intro los nts Ps) f v1 t1)
  (Hwfg : wf_global_ptr S (los, nts) M gl),
  wf_rmetadata (los,nts) M rm ->
  params2GVs (los,nts) ps lc gl rm = Some ogvs ->
  forall gv1 bv1 ev1,
    In (gv1, Some (mkMD bv1 ev1)) ogvs ->
    wf_data (los,nts) M bv1 ev1.
Proof.
  induction ps; simpl; intros ogvs Hwfvs Hwfg Hwfr Hp2ogvs gv1 bv1 ec1 Hin.
    inv Hp2ogvs. inv Hin.

    destruct a.
    destruct (NDopsem.getOperandValue (los,nts) v lc gl); 
      try solve [inv Hp2ogvs].
    remember (params2GVs (los,nts) ps lc gl rm) as R.
    destruct R; try solve [inv Hp2ogvs].
    destruct (isPointerTypB t); inv Hp2ogvs.
      simpl in Hin. 
      destruct Hin as [Hin | Hin]; eauto. 
        inv Hin.
        eapply wf_rmetadata__get_reg_metadata in H1; eauto.
        
      simpl in Hin. 
      destruct Hin as [Hin | Hin]; eauto. 
        inv Hin.
Qed.

Lemma initializeFrameValues__wf_rmetadata : forall TD M la ogvs lc rm
  (Hprop: forall gv1 bv1 ev1, 
    In (gv1,Some (mkMD bv1 ev1)) ogvs ->
    wf_data TD M bv1 ev1),
  forall la2 la1 ogvs1 ogvs2 lc1 rm1 lc2 rm2,
  la = la1 ++ la2 ->
  ogvs = ogvs1 ++ ogvs2 ->
  _initializeFrameValues la1 ogvs1 lc rm = (lc1, rm1) ->
  wf_rmetadata TD M rm1 ->
  _initializeFrameValues la2 ogvs2 lc1 rm1 = (lc2, rm2) ->
  wf_rmetadata TD M rm2.
Proof.
  intros TD M la ogvs lc rm Hprop.
  induction la2; simpl; intros la1 ogvs1 ogvs2 lc1 rm1 lc2 rm2 Heqla heqogvs 
    Hinit1 Hwfr1 Hinit2; subst.
    inv Hinit2. auto.

    destruct a. destruct p.
    destruct ogvs2.
      remember (_initializeFrameValues la2 nil lc1 rm1) as R.
      destruct R as [lc' rm'].
      destruct (isPointerTypB t); inv Hinit2.
        apply adding_null_preserves_wf_rmetadata.
        intros x bv ev Hlk.
        eapply initializeFrameValues_spec2 in Hlk; eauto.
        destruct Hlk as [Hlk | [Hlk | [gv1 Hlk]]]; eauto.
          inv Hlk. apply null_is_wf_data.
          inv Hlk.

        intros x bv ev Hlk.
        eapply initializeFrameValues_spec2 in Hlk; eauto.
        destruct Hlk as [Hlk | [Hlk | [gv1 Hlk]]]; eauto.
          inv Hlk. apply null_is_wf_data.
          inv Hlk.

    destruct p.
    remember (_initializeFrameValues la2 ogvs2 lc1 rm1) as R.
    destruct R as [lc' rm'].
    destruct (isPointerTypB t); inv Hinit2.
      destruct o as [[md1 ?]|]; inv H0.
        intros x bv ev Hlk.
        destruct (eq_atom_dec i0 x); subst.
          rewrite lookupAL_updateAddAL_eq in Hlk. 
          inv Hlk. 
          eapply Hprop; eauto. 
            apply in_or_app. simpl. auto.

          rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
          eapply initializeFrameValues_spec2 in Hlk; eauto.
          destruct Hlk as [Hlk | [Hlk | [gv1 Hlk]]]; eauto.
            inv Hlk. apply null_is_wf_data.
            eapply Hprop; eauto. 
              apply in_or_app. simpl. eauto.

        apply adding_null_preserves_wf_rmetadata.
        intros x bv ev Hlk.
        eapply initializeFrameValues_spec2 in Hlk; eauto.
        destruct Hlk as [Hlk | [Hlk | [gv1 Hlk]]]; eauto.
          inv Hlk. apply null_is_wf_data.
          eapply Hprop; eauto. 
            apply in_or_app. simpl. eauto.
      intros x bv ev Hlk.
      eapply initializeFrameValues_spec2 in Hlk; eauto.
      destruct Hlk as [Hlk | [Hlk | [gv1 Hlk]]]; eauto.
        inv Hlk. apply null_is_wf_data.
        eapply Hprop; eauto. 
          apply in_or_app. simpl. eauto.
Qed.

Lemma initLocals__wf_rmetadata : forall ogvs (rm : rmetadata) (lc' : GVsMap) 
  M rm' los nts ps la gl lc f Ps S
  (Hwfvs : forall t1 v1, In (t1,v1) ps -> 
    wf_value S (module_intro los nts Ps) f v1 t1)
  (Hwfg : wf_global_ptr S (los, nts) M gl),
  wf_rmetadata (los,nts) M rm ->
  params2GVs (los,nts) ps lc gl rm = Some ogvs ->
  initLocals la ogvs = (lc', rm') ->
  wf_rmetadata (los,nts) M rm'.
Proof.
  intros.
  unfold initLocals in H1.
  rewrite_env (nil++la) in H1.
  rewrite_env (nil++ogvs) in H1.
  eapply initializeFrameValues__wf_rmetadata with (lc1:=nil)(rm1:=nil)(lc:=nil)
    (rm:=nil)(ogvs1:=nil)(la1:=nil) in H1; eauto.
    eapply params2GVs__wf_rmetadata; eauto.
    intros x bv gv J. inv J.
Qed.

Lemma malloc_extends_wf_rmetadata : forall
  (TD : TargetData)
  (rm : AssocList metadata)
  (lc : GVsMap)
  (id0 : atom)
  (gn : GenericValue)
  (align0 : align)
  (Mem0 : mem)
  (Mem' : mem)
  (tsz : sz)
  (mb : mblock)
  (lc' : GVsMap)
  (rm' : rmetadata)
  (n : Z) t
  (H1 : malloc TD Mem0 tsz gn align0 = ret (Mem', mb))
  (H2 : GV2int TD Size.ThirtyTwo gn = ret n)
  (H3 : prop_reg_metadata lc rm id0 ($ (blk2GV TD mb) # typ_pointer t $)
         {| md_base := base2GV TD mb; md_bound := bound2GV TD mb tsz n |} =
       (lc', rm'))
  (Hwfr : wf_rmetadata TD Mem0 rm),
  wf_rmetadata TD Mem' rm'.
Proof.
  intros.
  invert_prop_reg_metadata. clear H3.
  unfold malloc in H1.
  rewrite H2 in H1.
  destruct (zle 0 (Size.to_Z tsz * n)); try solve [inversion H1].
  remember (Mem.alloc Mem0 0 (Size.to_Z tsz * n)) as R.
  inversion H1. clear H1. subst.
  clear H2.
  intros i0 gvb gve J.
  destruct (@id_dec id0 i0); subst.
  SCase "id0=i0".
      rewrite lookupAL_updateAddAL_eq in J.
      inversion J; subst. clear J.
      unfold wf_data.
      rewrite GV2ptr_base2GV. 
      rewrite GV2ptr_bound2GV. 
      destruct (zeq mb mb) as [J | J]; try solve [contradict J; auto].
      split.
        assert (H4':=H0).
        apply Mem.alloc_result in H0.
        apply Mem.nextblock_alloc in H4'.
        rewrite H0. rewrite H4'. zauto.

        intros Hwfb ofs J1. 
        apply Mem.valid_access_alloc_same with (ofs:=ofs)(chunk:=AST.Mint 7) 
          in H0.
          destruct H0 as [J2 J3].
          unfold Mem.range_perm in J2.
          apply Mem.perm_implies with (p1:=Freeable); auto with mem.
          apply J2.
          simpl. clear.
          assert (J:=@bytesize_chunk_pos 7).
          zauto.

          rewrite Int.signed_repr in J1; zauto. clear.
          assert (J1:=@Int.min_signed_neg 31).          
          assert (J2:=@Int.max_signed_pos 31).          
          zauto.

          simpl. rewrite bytesize_chunk_7_eq_1. 
          destruct J1 as [_ J1].
          unfold Int.signed in J1.
          unfold Int.unsigned in J1.
          simpl in J1.
          clear - J1 z.
          assert (J:=@Int.modulus_pos 31).
          assert ((Size.to_Z tsz * n) mod Int.modulus 31 <= (Size.to_Z tsz * n)) 
            as LE.
            apply Zmod_le; zauto.
          destruct (zlt ((Size.to_Z tsz * n) mod Int.modulus 31) 
            (Int.half_modulus 31)); zeauto.

          simpl. rewrite bytesize_chunk_7_eq_1. zauto.

  SCase "id0<>i0".
      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      assert (J':=@Hwfr i0 gvb gve J). clear Hwfr.    
      eapply alloc_preserves_wf_data; eauto.
Qed.

(********************************************)
(* wf_mmetadata *)

Lemma malloc_extends_wf_mmetadata : forall
  (TD : TargetData)
  (lc : GVsMap)
  (id0 : atom)
  (gn : GenericValue)
  (align0 : align)
  (Mem0 : mem)
  (MM : mmetadata)
  (Mem' : mem)
  (tsz : sz)
  (mb : mblock)
  (lc' : GVsMap)
  (rm' : rmetadata)
  (n : Z) rm t
  (H1 : malloc TD Mem0 tsz gn align0 = ret (Mem', mb))
  (H2 : GV2int TD Size.ThirtyTwo gn = ret n)
  (H3 : prop_reg_metadata lc rm id0 ($ (blk2GV TD mb) # typ_pointer t $)
         {| md_base := base2GV TD mb; md_bound := bound2GV TD mb tsz n |} =
       (lc', rm'))
  (Hwfm : wf_mmetadata TD Mem0 MM),
  wf_mmetadata TD Mem' MM.
Proof.
  intros.
  invert_prop_reg_metadata. clear H3.
  unfold malloc in H1.
  rewrite H2 in H1.
  destruct (zle 0 (Size.to_Z tsz * n)); try solve [inversion H1].
  remember (Mem.alloc Mem0 0 (Size.to_Z tsz * n)) as R.
  inversion H1. clear H1. subst.
  intros b ofs gvb gve J.
  assert (J':=@Hwfm b ofs gvb gve J). clear Hwfm.
  eapply alloc_preserves_wf_data; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
