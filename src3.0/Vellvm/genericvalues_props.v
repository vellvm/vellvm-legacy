Require Import syntax.
Require Import infrastructure.
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
Require Import targetdata_props.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import typings.
Require Import infrastructure_props.
Require Import analysis.
Require Import typings_props.

Import LLVMinfra.
Import LLVMtd.
Import LLVMtypings.
Import LLVMgv.
Import AtomSet.

(********************************************)
(** * generic values *)

Lemma const2GV_typsize_mutind_array : forall const_list system5 typ5 
  (los : list layout) (nts : list namedt) gl 
  (lsdc : list (system * targetdata * const)) lt
  (HeqR0 : (lsdc, lt) =
          split
            (unmake_list_system_targetdata_const_typ
               (make_list_system_targetdata_const_typ
                  (map_list_const
                     (fun const_ : const =>
                      (system5, (los, nts), const_, typ5)) const_list))))
  (lsd : list (system * targetdata)) lc
  (HeqR' : (lsd, lc) = split lsdc)
  ls (ld : list targetdata)
  (HeqR'' : (ls, ld) = split lsd)
  (H3 : wf_global (los, nts) system5 gl),
  wf_list_targetdata_typ system5 (los, nts) gl lsd.
Proof.
  intros.
  unfold wf_list_targetdata_typ.
  generalize dependent lsdc.
  generalize dependent lt.
  generalize dependent lc.
  generalize dependent ld.
  generalize dependent ls0.
  generalize dependent lsd.
  induction const_list; intros; simpl in *.
    inv HeqR0. inv HeqR'. inv H.
    
    remember (@split (prod (prod system targetdata) const) typ
                (unmake_list_system_targetdata_const_typ
                   (make_list_system_targetdata_const_typ
                      (@map_list_const
                         (prod
                            (prod
                               (prod system
                                  (prod (list layout) (list namedt))) const)
                            typ)
                         (fun const_ : const =>
                          @pair
                            (prod
                               (prod system
                                  (prod (list layout) (list namedt))) const)
                            typ
                            (@pair
                               (prod system
                                  (prod (list layout) (list namedt))) const
                               (@pair system
                                  (prod (list layout) (list namedt)) system5
                                  (@pair (list layout) (list namedt) los nts))
                               const_) typ5) const_list)))) as R.
    destruct R.
    inv HeqR0. simpl in HeqR'.
    remember (split l0) as R1.
    destruct R1.
    inv HeqR'. simpl in HeqR''.
    remember (split l2) as R2.
    destruct R2.
    inv HeqR''. simpl in H.
    destruct H as [H | H]; subst; eauto.
      inv H. split; auto.
Qed.

Lemma const2GV_typsize_mutind_struct : forall const_typ_list system5 los nts gl
  lsdc lt
  (HeqR : (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const_typ
                    (fun (const_ : const) (typ_ : typ) =>
                     (system5, (los, nts), const_, typ_)) const_typ_list))))
  lsd lc
  (HeqR' : (lsd, lc) = split lsdc)
  (H3 : wf_global (los, nts) system5 gl),
  wf_list_targetdata_typ system5 (los, nts) gl lsd.
Proof.
  intros.
  generalize dependent lsdc.
  generalize dependent lt.
  generalize dependent lc.
  generalize dependent lsd.
  induction const_typ_list; simpl; intros.
    inv HeqR. simpl in HeqR'. inv HeqR'.
    unfold wf_list_targetdata_typ.
    intros S TD Hin. inversion Hin.
    
    remember (split
              (unmake_list_system_targetdata_const_typ
                 (make_list_system_targetdata_const_typ
                    (map_list_const_typ
                       (fun (const_ : const) (typ_ : typ) =>
                        (system5, (los, nts), const_, typ_))
                       const_typ_list)))) as R1. 
    destruct R1. inv HeqR. simpl in HeqR'.
    remember (split l0) as R2.
    destruct R2. inv HeqR'.
    unfold wf_list_targetdata_typ in *.
    intros S TD Hin. 
    simpl in Hin.
    destruct Hin as [Hin | Hin]; eauto.
      inv Hin. split; auto.
Qed.

Definition const2GV_isnt_stuck_Prop S TD c t (H:wf_const S TD c t) := 
  forall gl (Hty: uniq (snd TD)),
  LLVMtd.feasible_typ TD t ->
  wf_global TD S gl ->
  exists gv, _const2GV TD gl c = Some (gv, t).

Definition consts2GV_isnt_stuck_Prop sdct (H:wf_const_list sdct) := 
  let 'lsdct := unmake_list_system_targetdata_const_typ sdct in
  let '(lsdc, lt) := split lsdct in
  let '(lsd, lc) := split lsdc in
  let '(ls, ld) := split lsd in
  forall S TD gl (Hty: uniq (snd TD)), 
  wf_list_targetdata_typ S TD gl lsd ->
  LLVMtd.feasible_typs TD (make_list_typ lt) ->
  (forall t, (forall t0, In t0 lt -> t0 = t) ->
    exists gv, _list_const_arr2GV TD gl t (make_list_const lc) = Some gv) /\
  (exists gv, _list_const_struct2GV TD gl (make_list_const lc) = 
    Some (gv, (make_list_typ lt))).

Lemma const2GV_isnt_stuck_mutind : 
  (forall S td c t H, @const2GV_isnt_stuck_Prop S td c t H) /\
  (forall sdct H, @consts2GV_isnt_stuck_Prop sdct H).
Proof.
  (wfconst_cases (apply wf_const_mutind with
    (P  := const2GV_isnt_stuck_Prop)
    (P0 := consts2GV_isnt_stuck_Prop)) Case);
    unfold const2GV_isnt_stuck_Prop, consts2GV_isnt_stuck_Prop;
    intros; subst; simpl; eauto.
Case "wfconst_zero".
  destruct (@wf_zeroconst2GV_total targetdata5 typ5) as [gv J]; auto.
  apply feasible_typ_intro; auto.
  rewrite J. eauto.
Case "wfconst_floatingpoint". 
  inv w; eauto.
Case "wfconst_undef".
  eapply gundef__total in H; eauto.
  destruct H as [gv H].
  rewrite H. eauto.
Case "wfconst_array".
  remember (split
             (unmake_list_system_targetdata_const_typ
                (make_list_system_targetdata_const_typ
                   (map_list_const
                      (fun const_ : LLVMsyntax.const => 
                        (system5, targetdata5, const_, typ5))
                      const_list)))) as R.
  destruct R as [lsdc lt].
  remember (split lsdc) as R'.
  destruct R' as [lsd lc].
  remember (split lsd) as R''.
  destruct R'' as [ls ld].
  destruct (@H system5 targetdata5 gl) as [J1 [gv2 J2]]; 
    try solve [destruct targetdata5; eauto using const2GV_typsize_mutind_array].

    eapply make_list_const_spec1; eauto.

    assert (make_list_const lc = const_list) as EQ.
      eapply make_list_const_spec2; eauto.
    rewrite e. rewrite <- EQ. unfold Size.to_nat in *. 
    destruct (@J1 typ5) as [gv1 J3]; eauto using make_list_const_spec4.
    rewrite J3.
    destruct sz5; eauto.

Case "wfconst_struct".
  remember (split
             (unmake_list_system_targetdata_const_typ
                (make_list_system_targetdata_const_typ
                   (map_list_const_typ
                     (fun (const_ : LLVMsyntax.const) (typ_ : LLVMsyntax.typ) => 
                        (system5, (layouts5, namedts5):targetdata, const_, typ_))
                      const_typ_list)))) as R.
  destruct R as [lsdc lt].
  remember (split lsdc) as R'.
  destruct R' as [lsd lc].
  remember (split lsd) as R''.
  destruct R'' as [ls ld].
  erewrite <- map_list_const_typ_spec1 in e0; eauto.
  destruct (@H system5 (layouts5, namedts5) gl) as [_ [gv2 J2]];
    try solve [eauto using const2GV_typsize_mutind_struct |
               eapply typ_eq_list_typ_spec1; eauto].
    erewrite <- map_list_const_typ_spec2; eauto.
    rewrite J2. 
    rewrite e0.
    destruct gv2; eauto.

Case "wfconst_gid".
  apply H0 in e.  
  destruct e as [gv [sz [e [J1 J2]]]].
  rewrite e. eauto.
Case "wfconst_trunc_int".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  unfold mtrunc.
  assert (exists gv, gundef targetdata5 (typ_int sz2) = Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J.
  destruct (GV2val targetdata5 gv); eauto.
  destruct v; eauto.
Case "wfconst_trunc_fp".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  unfold mtrunc. rewrite e.
  assert (exists gv, gundef targetdata5 (typ_floatpoint floating_point2) = 
           Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J.
  destruct (GV2val targetdata5 gv); eauto.
  destruct v; eauto.
  destruct floating_point2; try solve [eauto | inversion w0].
Case "wfconst_zext".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  unfold mext.
  assert (exists gv, gundef targetdata5 (typ_int sz2) = Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J.
  destruct (GV2val targetdata5 gv); eauto.
  destruct v; eauto.
Case "wfconst_sext".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  unfold mext.
  assert (exists gv, gundef targetdata5 (typ_int sz2) = Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J.
  destruct (GV2val targetdata5 gv); eauto.
  destruct v; eauto.
Case "wfconst_fpext".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  unfold mext.
  assert (exists gv, gundef targetdata5 (typ_floatpoint floating_point2) = 
    Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J.
  rewrite e.
  destruct (GV2val targetdata5 gv); eauto.
  destruct v; eauto.
  destruct floating_point2; try solve [eauto | inversion w0].
Case "wfconst_ptrtoint".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1. 
  assert (exists gv, gundef targetdata5 (typ_int sz5) = 
    Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J. eauto.
Case "wfconst_inttoptr".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  assert (exists gv, gundef targetdata5 (typ_pointer typ5) = 
    Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J. eauto.
Case "wfconst_bitcast".
  inv f. unfold mbitcast.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1. eauto.
Case "wfconst_gep".
  clear H0.
  inv f.
  eapply H in H2; eauto.
  destruct H2 as [gv H2].
  rewrite H2. rewrite e0.
  assert (exists gv, gundef targetdata5 typ' = Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J.
  destruct (GV2ptr targetdata5 (getPointerSize targetdata5) gv); eauto.
  destruct (intConsts2Nats targetdata5 const_list); eauto.
  destruct (mgep targetdata5 typ5 v l0); eauto.
Case "wfconst_select".
  assert (J:=H2).
  eapply H0 in H2; eauto.
  destruct H2 as [gv H2].
  rewrite H2. 
  eapply H1 in J; eauto.
  destruct J as [gv' J].
  rewrite J. 
  inv f.
  eapply H in H4; eauto.
  destruct H4 as [gv'' H4].
  rewrite H4.
  destruct (isGVZero targetdata5 gv''); eauto.
Case "wfconst_icmp".
  inv f.
  assert (J:=H3).
  eapply H in H3; eauto.
  destruct H3 as [gv H3].
  rewrite H3. 
  eapply H0 in J; eauto.
  destruct J as [gv' J].
  rewrite J. 
  unfold micmp.
  unfold isPointerTyp in o. unfold is_true in o.
  unfold micmp_int.
  assert (exists gv, gundef targetdata5 (typ_int 1%nat) = 
           Some gv) as JJ.
    eapply gundef__total; eauto.
  destruct JJ as [gv0 JJ].
  rewrite JJ.
  destruct o as [o | o].
    destruct typ5; try solve [simpl in o; contradict o; auto].
    destruct (GV2val targetdata5 gv); eauto.
    destruct v; eauto.
    destruct (GV2val targetdata5 gv'); eauto.
    destruct v; eauto.
    destruct cond5; eauto.

    destruct typ5; try solve [eauto | simpl in o; contradict o; auto].
Case "wfconst_fcmp".
  inv f.
  assert (J:=H3).
  eapply H in H3; eauto.
  destruct H3 as [gv H3].
  rewrite H3. 
  eapply H0 in J; eauto.
  destruct J as [gv' J].
  rewrite J. 
  unfold mfcmp.
  assert (exists gv, gundef targetdata5 (typ_int 1%nat) = 
           Some gv) as JJ.
    eapply gundef__total; eauto.
  destruct JJ as [gv0 JJ].
  rewrite JJ.
  destruct (GV2val targetdata5 gv); eauto.
  destruct v; eauto.
  destruct (GV2val targetdata5 gv'); eauto.
  destruct v; eauto.
  destruct floating_point5; try solve [eauto | inversion w1].
    destruct fcond5; try solve [eauto | inversion e].
    destruct fcond5; try solve [eauto | inversion e].
Case "wfconst_extractvalue".
  inv f.
  eapply H in H3; eauto.
  destruct H3 as [gv H3].
  rewrite H3.
  destruct e0 as [idxs [o [J1 J2]]].
  erewrite mgetoffset__getSubTypFromConstIdxs; eauto.
  unfold LLVMgv.extractGenericValue.
  rewrite J1. rewrite J2.
  destruct (mget targetdata5 gv o typ'); eauto.
    eapply gundef__total in H1; eauto.
    destruct H1. rewrite H1. eauto.
Case "wfconst_insertvalue".
  inv f.
  assert (J:=H2).
  eapply H in H2; eauto.
  destruct H2 as [gv H2].
  rewrite H2.
  eapply H0 in H4; eauto.
  destruct H4 as [gv' H4].
  rewrite H4.
  unfold LLVMgv.insertGenericValue.
  destruct e0 as [idxs [o [J1 J2]]].
  rewrite J1. rewrite J2.
  destruct (mset targetdata5 gv o typ' gv'); eauto.
    eapply gundef__total in J; eauto.
    destruct J as [gv0 J]. rewrite J. eauto.
Case "wfconst_bop".
  assert (exists gv, gundef targetdata5 (typ_int sz5) = Some gv) as JJ.
    eapply gundef__total; eauto.
  destruct JJ as [gv0 JJ].
  assert (J:=H1).
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  eapply H0 in J; eauto.
  destruct J as [gv' J].
  rewrite J.
  unfold mbop, Size.to_nat. 
  rewrite JJ.
  destruct (GV2val targetdata5 gv); eauto.
  destruct (GV2val targetdata5 gv'); eauto.
  destruct v; eauto.
  destruct v0; eauto.
  destruct (eq_nat_dec (wz + 1) sz5); eauto.
  destruct bop5; eauto.
  destruct v; eauto.
Case "wfconst_fbop".
  assert (exists gv, gundef targetdata5 (typ_floatpoint floating_point5) 
    = Some gv) as JJ.
    eapply gundef__total; eauto.
  destruct JJ as [gv0 JJ].
  assert (J:=H1).
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  eapply H0 in J; eauto.
  destruct J as [gv' J].
  rewrite J.
  unfold mfbop. rewrite JJ.
  destruct (GV2val targetdata5 gv); eauto.
  destruct (GV2val targetdata5 gv'); eauto.
  destruct v; eauto.
  destruct v0; eauto.
  destruct floating_point5; try solve [eauto | inversion w1].
  destruct v; eauto.
Case "wfconst_cons".
  remember (split (unmake_list_system_targetdata_const_typ l')) as R1.
  destruct R1 as [lsdc lt].
  simpl.  
  remember (split lsdc) as R2.
  destruct R2 as [lsd lc].
  simpl.  
  remember (split lsd) as R3.
  destruct R3 as [ls ld].
  simpl.
  intros S TD gl Huniq Hwfl Hft.
  assert (LLVMtd.feasible_typs TD (make_list_typ lt) /\
          LLVMtd.feasible_typ TD typ5) as J.
    clear - Hft. apply feasible_cons_typs in Hft.
    destruct Hft.
    split; auto.
  destruct J as [J1 J2].
  assert (wf_list_targetdata_typ S TD gl lsd /\ system5 = S /\ targetdata5 = TD
            /\ wf_global TD S gl) 
    as Hwfl'.
    clear - Hwfl.
    unfold wf_list_targetdata_typ in *.
    assert (In (system5, targetdata5) ((system5, targetdata5) :: lsd)) as J.
      simpl. auto.
    apply Hwfl in J. 
    destruct J as [J1 [J2 J3]]; subst.
    split.
      intros S1 TD1 Hin.    
      apply Hwfl. simpl. auto.
    split; auto.

  destruct Hwfl' as [Hwfl' [Heq1 [Heq2 Hwfg]]]; subst.  
  assert (J2':=J2).
  eapply H in J2'; eauto.
  destruct J2' as [gv J2'].
  rewrite J2'.
  assert (J1':=J1).
  eapply H0 in J1'; eauto.
  destruct J1' as [J1' [g2 J12]].
  rewrite J12.
  apply feasible_typ_inv'' in J2.  
  destruct J2 as [ssz [asz [J21 J22]]].
  rewrite J22.
  split; eauto.  
    intros.
    destruct (@J1' t) as [gv0 H2]; eauto.
    rewrite H2.
    assert (typ5 = t) as EQ. apply H1; auto.
    subst.
    destruct (typ_dec t t); eauto.
      contradict n; auto.
Qed.

Lemma mbop_is_total : forall S TD bop0 sz0, 
  wf_typ S (typ_int sz0) ->
  feasible_typ TD (typ_int sz0) ->
  forall x y, exists z, mbop TD bop0 sz0 x y = Some z.
Proof.
  intros S TD bop0 sz0 Hwft Hft x y.
  unfold mbop. inv Hft.
  destruct (GV2val TD x); eauto using gundef__total.
  destruct v; eauto using gundef__total.
  destruct (GV2val TD y); eauto using gundef__total.
  destruct v; eauto using gundef__total.
  destruct (eq_nat_dec (wz + 1) (Size.to_nat sz0)); 
    eauto using gundef__total.
  destruct bop0; eauto using gundef__total.
Qed.

Lemma mfbop_is_total : forall S TD fbop0 fp, 
  wf_typ S (typ_floatpoint fp) ->
  feasible_typ TD (typ_floatpoint fp) ->
  forall x y, exists z, mfbop TD fbop0 fp x y = Some z.
Proof.
  intros.
  unfold mfbop. inv H0.
  destruct (GV2val TD x); eauto using gundef__total.
  destruct v; eauto using gundef__total.
  destruct (GV2val TD y); eauto using gundef__total.
  destruct v; eauto using gundef__total.
  destruct fp; try solve [eauto | inversion H].
Qed.

Lemma micmp_is_total : forall TD c t, 
  Typ.isIntOrIntVector t \/ isPointerTyp t ->
  forall x y, exists z, micmp TD c t x y = Some z.
Proof.
  intros TD c t Hwft x y.
  unfold micmp, micmp_int.
  unfold isPointerTyp in Hwft. unfold is_true in Hwft.
  unfold micmp_int.
  destruct Hwft as [Hwft | Hwft].
    destruct t; try solve [simpl in Hwft; contradict Hwft; auto].
    destruct (GV2val TD x); eauto using gundef_i1__total.
    destruct v; eauto using gundef_i1__total.
    destruct (GV2val TD y); eauto using gundef_i1__total.
    destruct v; eauto using gundef_i1__total.
    destruct c; eauto using gundef_i1__total.
  
    destruct t; try solve [simpl in Hwft; contradict Hwft; auto]. 
      eauto using gundef_i1__total.
Qed.

Lemma mfcmp_is_total : forall S TD c fp, 
  wf_fcond c = true  ->
  wf_typ S (typ_floatpoint fp) ->
  feasible_typ TD (typ_floatpoint fp) ->
  forall x y, exists z, mfcmp TD c fp x y = Some z.
Proof.
  intros S TD c fp Hc Ht Hft2 x y.
  unfold mfcmp.
  destruct (GV2val TD x); eauto using gundef_i1__total.
  destruct v; eauto using gundef_i1__total.
  destruct (GV2val TD y); eauto using gundef_i1__total.
  destruct v; eauto using gundef_i1__total.
  destruct fp; try solve [eauto | inversion Ht].
    destruct c; try solve [eauto | inversion Hc].
    destruct c; try solve [eauto | inversion Hc].
Qed.

Lemma GEP_is_total : forall TD t mp vidxs inbounds0,
  exists mp', LLVMgv.GEP TD t mp vidxs inbounds0 = ret mp'.
Proof.
  intros. unfold LLVMgv.GEP.
  destruct (GV2ptr TD (getPointerSize TD) mp); eauto using gundef_p1__total.
  destruct (GVs2Nats TD vidxs); eauto using gundef_p1__total.
  destruct (mgep TD t v l0); eauto using gundef_p1__total.
Qed.

Lemma gundef__total' : forall TD t
  (H0 : feasible_typ TD t),
  exists gv, gundef TD t = Some gv.
Proof.
  intros. inv H0. apply gundef__total; auto.
Qed.

Lemma fit_gv__total : forall TD t gv1
  (H0 : feasible_typ TD t),
  exists gv, fit_gv TD t gv1 = Some gv.
Proof.
  intros. 
  unfold fit_gv.
  assert (exists gv, gundef TD t = Some gv) as EQ.
    apply gundef__total'; auto.
  destruct EQ as [gv EQ].
  rewrite EQ. inv H0.
  eapply feasible_typ_inv' in H; eauto.
  destruct H as [sz [al [J1 J2]]].
  unfold getTypeSizeInBits.
  rewrite J1. 
  destruct (sizeGenericValue gv1 =n= nat_of_Z (ZRdiv (Z_of_nat sz) 8)); eauto.
Qed.

Lemma mcast_is_total : forall ifs s f b los nts ps id5 cop0 t1 t2 v,
  wf_cast ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_cast id5 cop0 t1 v t2)) ->
  forall x, exists z, mcast (los,nts) cop0 t1 t2 x = Some z.
Proof.
  intros.
  unfold mcast, mbitcast.
  inv H; eauto using gundef__total'.
Qed.

Lemma mtrunc_is_total : forall ifs s f b los nts ps id5 top0 t1 t2 v, 
  wf_trunc ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_trunc id5 top0 t1 v t2)) ->
  forall x, exists z, mtrunc (los,nts) top0 t1 t2 x = Some z.
Proof.
  intros.
  assert (J:=H).
  apply wf_trunc__wf_typ in J.
  destruct J as [J1 J2]. inv J2.
  unfold mtrunc.
  destruct (GV2val (los, nts) x); eauto using gundef__total.
  inv H; try solve [destruct v0; eauto using gundef__total].
    rewrite H16.
    destruct v0; eauto using gundef__total.
      destruct floating_point2; try solve [eauto | inversion H14].
Qed.

Lemma mext_is_total : forall ifs s f b los nts ps id5 eop0 t1 t2 v, 
  wf_ext ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_ext id5 eop0 t1 v t2)) ->
  forall x,  exists z, mext (los,nts) eop0 t1 t2 x = Some z.
Proof.
  intros.
  unfold mext.
  inv H; try solve 
    [destruct (GV2val (los, nts) x); eauto using gundef__total'; 
     destruct v0; eauto using gundef__total'].
    rewrite H15.
    destruct (GV2val (los, nts) x); eauto using gundef__total'; 
    destruct v0; eauto using gundef__total'.
    destruct floating_point2; try solve [inversion H13 | eauto].
Qed.

Definition zeroconst2GV__getTypeSizeInBits_prop (t:typ) := forall s los nts gv,
  zeroconst2GV (los,nts) t = Some gv ->
  wf_typ s t -> LLVMtd.feasible_typ (los,nts) t ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
     (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t
     = Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.

Definition zeroconsts2GV__getListTypeSizeInBits_prop (lt:list_typ) := 
  forall los nts gv lst,
  zeroconsts2GV (los,nts) lt = Some gv ->
  wf_typ_list lst -> LLVMtd.feasible_typs (los,nts) lt ->
  (exists ls, 
    split (unmake_list_system_typ lst) = (ls, unmake_list_typ lt)) ->
  exists sz, exists al,
    _getListTypeSizeInBits_and_Alignment los 
     (getTypeSizeInBits_and_Alignment_for_namedts (los, nts) true) lt = 
       Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.

Lemma zeroconst2GV_typsize_mutrec :
  (forall t, zeroconst2GV__getTypeSizeInBits_prop t) *
  (forall lt, zeroconsts2GV__getListTypeSizeInBits_prop lt).
Proof.
  (typ_cases (apply typ_mutrec; 
    unfold zeroconst2GV__getTypeSizeInBits_prop, 
           zeroconsts2GV__getListTypeSizeInBits_prop) Case);
    intros; simpl in *; try solve [eauto | inversion H | inversion H1 ].
Case "typ_int".
  inv H.
  simpl.
  exists (Size.to_nat s). exists (getIntAlignmentInfo los (Size.to_nat s) true).
  erewrite int_typsize; eauto.

Case "typ_floatingpoint".
  destruct f; inv H; 
    simpl; unfold size_chunk_nat, size_chunk, bytesize_chunk.
    exists 32%nat. exists (getFloatAlignmentInfo los 32 true).
    simpl. auto.

    exists 64%nat. exists (getFloatAlignmentInfo los 64 true).
    simpl. auto.

Case "typ_array".
  destruct s as [|s]; try solve [inv H0; exists 8%nat; exists 1%nat; auto].
  remember (zeroconst2GV (los, nts) t) as R1.
  destruct R1; try solve [inv H0].
  remember (getTypeAllocSize (los, nts) t) as R2.
  destruct R2 as [s1|]; inv H0.
  assert (
    (g ++ uninits (Size.to_nat s1 - sizeGenericValue g)) ++
          repeatGV (g ++ uninits (Size.to_nat s1 - sizeGenericValue g)) s = 
    repeatGV (g ++ uninits (Size.to_nat s1 - sizeGenericValue g)) (S s)) as G.
    simpl. auto.
  rewrite G.
  symmetry in HeqR1.
  inv H1.
  apply H with (s:=s0) in HeqR1; eauto using feasible_array_typ_inv.
  destruct HeqR1 as [sz [al [J1 J2]]].
  rewrite J1.  rewrite J2.
  exists (RoundUpAlignment (sizeGenericValue g) al * 8 * Size.to_nat (S s))%nat.
  exists al.
  split; auto.
  unfold getTypeAllocSize, getABITypeAlignment, getAlignment, getTypeStoreSize,
    getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
    getTypeSizeInBits_and_Alignment_for_namedts in HeqR2.
  rewrite J1 in HeqR2.
  inv HeqR2.
  rewrite sizeGenericValue__repeatGV.
  rewrite sizeGenericValue__app.
  rewrite sizeGenericValue__uninits. rewrite J2. unfold Size.to_nat.
  assert (RoundUpAlignment (sizeGenericValue g) al >= (sizeGenericValue g))%nat 
    as J3.
    apply RoundUpAlignment_spec.
      change (LLVMtd.feasible_typ (los, nts) t) in H2; auto.
      eapply feasible_typ_inv' in H2; eauto.
      destruct H2 as [sz0 [al0 [J3 J4]]].
      unfold getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts in J3.
      rewrite J1 in J3. inv J3. auto.

  assert ((sizeGenericValue g +
     (RoundUpAlignment (sizeGenericValue g) al - sizeGenericValue g))%nat = 
     (RoundUpAlignment (sizeGenericValue g) al)) as J4.
    rewrite <- le_plus_minus; auto.
  rewrite J4.
  rewrite ZRdiv_prop8.
  ring.

Case "typ_struct".
  remember (zeroconsts2GV (los, nts) l0) as R1.
  destruct R1; inv H0.
  symmetry in HeqR1.
  inv H1.
  eapply H in HeqR1; eauto using list_system_typ_spec, feasible_struct_typ_inv.
  destruct HeqR1 as [sz [al [J1 J2]]].
  rewrite J1.
  destruct sz.
    exists 8%nat. exists 1%nat.
    split; auto.
      simpl in J2.
      destruct g as [|[]]; inv H4; auto.
        simpl in J2.
        assert (J3 := size_chunk_nat_pos' m).
        contradict J2; omega.

    exists (S sz0). exists al.
    split; auto.
      rewrite J2.
      destruct g as [|[]]; inv H4; auto.
        assert (Coqlib.ZRdiv (Z_of_nat (S sz0)) 8 > 0) as J.
          apply Coqlib.ZRdiv_prop3; try solve [omega | apply Coqlib.Z_of_S_gt_O].
        apply Coqlib.nat_of_Z_pos in J.
        contradict J2. simpl in *. omega.

Case "typ_pointer".
  inv H0.
  exists (Size.to_nat (getPointerSizeInBits los)).
  exists (getPointerAlignmentInfo los true).
  split; auto.
     
Case "typ_nil".
  inv H. 
  exists 0%nat. exists 0%nat. auto.

Case "typ_cons".
  destruct H4 as [ls H4].
  apply unmake_list_system_typ_inv in H4.
  destruct H4 as [s [ls' [lst' [J1 [J2 J3]]]]]; subst.
  inv H2.
  remember (zeroconsts2GV (los, nts) l0) as R1.
  destruct R1; inv H1.
  remember (zeroconst2GV (los, nts) t) as R2.
  destruct R2; inv H4.
  remember (getTypeAllocSize (los, nts) t) as R3.
  destruct R3; inv H2.
  symmetry in HeqR1. symmetry in HeqR2.
  destruct H3 as [H31 H32].
  eapply H in HeqR2; eauto.
  eapply H0 in HeqR1; eauto.
  destruct HeqR1 as [sz1 [al1 [J4 J5]]].
  destruct HeqR2 as [sz2 [al2 [J6 J7]]].
  rewrite J4. rewrite J6.
  rewrite sizeGenericValue__app.
  rewrite sizeGenericValue__app.
  rewrite sizeGenericValue__uninits. 
  rewrite <- J5. rewrite <- J7. 
  erewrite getTypeAllocSize_roundup; eauto.
  eapply getTypeAllocSize_inv' in J6; eauto. subst.
  exists ((sz1 +
             RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8)) al2 * 8 )%nat).
  exists (if le_lt_dec al2 al1 then al1 else al2).
  split; auto.
    apply ZRdiv_prop9.
Qed.

Lemma zeroconst2GV__getTypeSizeInBits : forall t s los nts gv,
  zeroconst2GV (los,nts) t = Some gv ->
  wf_typ s t -> feasible_typ (los,nts) t ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof. intros. inv H1.
  destruct zeroconst2GV_typsize_mutrec. 
  unfold zeroconst2GV__getTypeSizeInBits_prop in z. eauto.
Qed.

Lemma gundef__getTypeSizeInBits : forall los nts gv s t'
  (Hwft : wf_typ s t') (Hty: ty_namedts s nts)
  (H0 : feasible_typ (los, nts) t')
  (HeqR : ret gv = gundef (los, nts) t'),
   exists sz0 : nat,
     exists al : nat,
       _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
         true t' = ret (sz0, al) /\
       Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz0) 8) = sizeGenericValue gv.
Proof.
  intros.
  unfold gundef in HeqR.
  eapply feasible_typ_inv in H0; eauto.
  destruct H0 as [sz [al [J1 [J2 J3]]]].
  unfold getTypeSizeInBits in HeqR.
  rewrite J1 in HeqR.
  inv HeqR.
  unfold getTypeSizeInBits_and_Alignment,
         getTypeSizeInBits_and_Alignment_for_namedts in J1.
  rewrite J1.
  exists sz. exists al.
  simpl. unfold size_chunk_nat, size_chunk, bytesize_chunk.
  assert (S (sz - 1) = sz) as EQ. omega.
  rewrite EQ. split; auto.
Qed.

Lemma wf_list_targetdata_typ_cons_inv : forall S TD gl S'  TD' lsd,
  wf_list_targetdata_typ S TD gl ((S', TD') :: lsd) ->
  wf_list_targetdata_typ S TD gl lsd /\ S' = S /\ TD' = TD /\ wf_global TD S gl.
Proof.
  intros. 
  unfold wf_list_targetdata_typ in *.
  assert (In (S', TD') ((S', TD') :: lsd)) as J. simpl. auto.
  apply H in J. 
  destruct J as [J1 [J2 J3]]; subst.
  split.
    intros S1 TD1 Hin.    
    apply H. simpl. auto.
  split; auto.
Qed.
 
Lemma mtrunc_typsize : forall S los nts top t1 t2 gv1 gv2 
  (Hty:ty_namedts S nts), wf_typ S t2 ->
  feasible_typ (los, nts) t2 ->
  mtrunc (los,nts) top t1 t2 gv1 = Some gv2 ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t2 = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv2.
Proof.  
  intros. unfold mtrunc, GV2val in H1.
  destruct gv1; tinv H1.
    eapply gundef__getTypeSizeInBits; eauto.
  destruct p.
  destruct gv1; 
    try solve [inversion H1; eapply gundef__getTypeSizeInBits; eauto].
  destruct v; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct_typ t1; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct_typ t2; try solve [eapply gundef__getTypeSizeInBits; eauto].
      inv H1.
      simpl. exists (Size.to_nat s1).
      exists (getIntAlignmentInfo los (Size.to_nat s1) true).
      erewrite int_typsize; eauto.
  
    destruct_typ t1; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct_typ t2; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct (floating_point_order f1 f0); tinv H1.
    destruct f1; inv H1.
      simpl. exists 32%nat. exists (getFloatAlignmentInfo los 32 true).
      auto.
  
      simpl. exists 64%nat. exists (getFloatAlignmentInfo los 64 true).
      auto.
Qed.

Lemma mext_typsize : forall S los nts eop t1 t2 gv1 gv2
  (Hty:ty_namedts S nts), wf_typ S t2 ->
  feasible_typ (los, nts) t2 ->
  mext (los,nts) eop t1 t2 gv1 = Some gv2 ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t2 = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv2.
Proof.  
  intros. unfold mext, GV2val in H1.
  destruct_typ t1; tinv H1.
    destruct_typ t2; tinv H1.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
    destruct p.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
    destruct v; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct eop; inv H1.
      simpl. exists (Size.to_nat s1).
      exists (getIntAlignmentInfo los (Size.to_nat s1) true).
      erewrite int_typsize; eauto.

      simpl. exists (Size.to_nat s1).
      exists (getIntAlignmentInfo los (Size.to_nat s1) true).
      erewrite int_typsize; eauto.

    destruct_typ t2; tinv H1.
    destruct (floating_point_order f f0); tinv H1.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
    destruct p.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
    destruct v; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct eop; inv H1.
    destruct f0; inv H3; simpl.
      exists 32%nat. exists (getFloatAlignmentInfo los 32 true). auto.
      exists 64%nat. exists (getFloatAlignmentInfo los 64 true). auto.
Qed.

Lemma extractGenericValue_typsize : forall los nts t1 gv1 const_list typ' gv
  sz al system5 (Hty:ty_namedts system5 nts) 
  (HeqR3 : ret gv = extractGenericValue (los, nts) t1 gv1 const_list)
  (e0 : getSubTypFromConstIdxs const_list t1 = ret typ')
  (J1 : _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
         true t1 = ret (sz, al))
  (J2 : Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv1)
  (H0 : feasible_typ (los, nts) typ')
  (w1 : wf_typ system5 typ'),
  exists sz0 : nat,
    exists al0 : nat,
        _getTypeSizeInBits_and_Alignment los
          (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
          true typ' = ret (sz0, al0) /\
        Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz0) 8) = sizeGenericValue gv.
Proof.
  intros.
  unfold extractGenericValue in HeqR3.
  remember (intConsts2Nats (los, nts) const_list) as R1.
  destruct R1 as [idxs|]; tinv HeqR3.
  remember (mgetoffset (los, nts) t1 idxs) as R2.
  destruct R2 as [[o t']|]; tinv HeqR3.
  remember (mget (los, nts) gv1 o t') as R4.
  eapply getSubTypFromConstIdxs__mgetoffset in e0; eauto.
  destruct R4 as [gv'|]; inv HeqR3.
    eapply mget_typsize; eauto.
    eapply gundef__getTypeSizeInBits; eauto.
Qed.    

Lemma insertGenericValue_typsize : forall los nts t1 gv1 const_list gv t2 gv2
    system5 sz al sz2 al2 (Hty:ty_namedts system5 nts) 
  (J1 : _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
         true t1 = ret (sz, al))
  (J2 : Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv1)
  (J3 : _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
         true t2 = ret (sz2, al2))
  (J4 : Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8) = sizeGenericValue gv2)
  (H0 : feasible_typ (los, nts) t1)
  (w1 : wf_typ system5 t1)
  (HeqR3 : ret gv = insertGenericValue (los, nts) t1 gv1 const_list t2 gv2),
  sizeGenericValue gv1 = sizeGenericValue gv.
Proof.
  intros.
  unfold insertGenericValue in HeqR3.
  remember (intConsts2Nats (los, nts) const_list) as R1.
  destruct R1 as [idxs|]; tinv HeqR3.
  remember (mgetoffset (los, nts) t1 idxs) as R2.
  destruct R2 as [[o t']|]; tinv HeqR3.
  remember (mset (los, nts) gv1 o t2 gv2) as R4.
  destruct R4 as [gv'|]; inv HeqR3.
    eapply mset_typsize in HeqR4; eauto. 

    eapply gundef__getTypeSizeInBits in H1; eauto.
    destruct H1 as [sz1 [al1 [J3' J4']]].
    rewrite J1 in J3'. inv J3'.
    rewrite <- J4'. rewrite <- J2. auto.
Qed.    

Lemma mbop_typsize_helper : forall TD system5 s gv 
  (Hty:ty_namedts system5 (snd TD)), 
  wf_typ system5 (typ_int s) -> 
  feasible_typ TD (typ_int s) ->
  gundef TD (typ_int s) = ret gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat s) 8) = sizeGenericValue gv.
Proof.
  intros. destruct TD.
  symmetry in H1.
  eapply gundef__getTypeSizeInBits in H1; eauto.
    simpl in H1. destruct H1 as [sz0 [al [J1 J2]]]. inv J1. auto.
Qed.

Lemma mbop_typsize : forall system5 los nts bop5 s gv1 gv2 gv
  (Hty:ty_namedts system5 nts),
  wf_typ system5 (typ_int s) -> 
  feasible_typ (los, nts) (typ_int s) ->
  mbop (los,nts) bop5 s gv1 gv2 = Some gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat s) 8) = sizeGenericValue gv.
Proof.
  intros. replace nts with (snd (los, nts)) in Hty; auto.
  unfold mbop, GV2val in H1.
  destruct gv1; 
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  destruct p.
  destruct gv1; 
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  destruct v; 
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  destruct gv2; 
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  destruct p.
  destruct gv2; 
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  destruct v; 
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  destruct (eq_nat_dec (wz + 1) (Size.to_nat s));
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  unfold Size.to_nat in e. subst.
  assert (S (Size.to_nat (wz + 1)%nat - 1) = wz + 1)%nat as EQ.
    unfold Size.to_nat. omega.
  destruct bop5; inv H1;
    try solve [simpl; unfold size_chunk_nat, size_chunk, bytesize_chunk;
               rewrite EQ; auto].
Qed.

Lemma mfbop_typsize : forall system5 los nts fbop5 f gv1 gv2 gv
  (Hty:ty_namedts system5 nts), wf_typ system5 (typ_floatpoint f) -> 
  feasible_typ (los, nts) (typ_floatpoint f) ->
  mfbop (los,nts) fbop5 f gv1 gv2 = Some gv ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true 
        (typ_floatpoint f) = Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof.
  intros. 
  unfold mfbop, GV2val in H1.
  destruct gv1; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
  destruct p.
  destruct gv1; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
  destruct v; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
  destruct gv2; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
  destruct p.
  destruct gv2; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
  destruct v; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
  destruct f; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
    destruct fbop5; inv H1; simpl; eauto.
    destruct fbop5; inv H1; simpl; eauto.
Qed.

Definition const2GV__getTypeSizeInBits_Prop S TD c t (H:wf_const S TD c t) := 
  forall los nts gl gv t' (HwfTD: wf_namedts S TD),
  TD = (los, nts) ->
  LLVMtd.feasible_typ TD t ->
  _const2GV (los,nts) gl c = Some (gv, t') ->
  wf_global TD S gl ->
  t = t' /\
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.

Definition consts2GV__getTypeSizeInBits_Prop sdct (H:wf_const_list sdct) := 
  let 'lsdct := unmake_list_system_targetdata_const_typ sdct in
  let '(lsdc, lt) := split lsdct in
  let '(lsd, lc) := split lsdc in
  let '(ls, ld) := split lsd in
  forall S TD los nts gl (HwfTD: wf_namedts S TD), 
  TD = (los, nts) ->
  wf_list_targetdata_typ S TD gl lsd ->
  (forall gv t, 
    LLVMtd.feasible_typ TD t ->
    (forall t0, In t0 lt -> t0 = t) ->
   _list_const_arr2GV TD gl t (make_list_const lc) = Some gv ->
   exists sz, 
    getTypeAllocSize TD t = Some sz /\
    (sz * length lc)%nat = sizeGenericValue gv) /\
  (forall gv lt', 
    LLVMtd.feasible_typs TD (make_list_typ lt) ->
   _list_const_struct2GV TD gl (make_list_const lc) = Some (gv, lt') ->
   lt' = make_list_typ lt /\
   exists sz, exists al,
    _getListTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) lt' = 
        Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv).

Hint Constructors feasible_typ.

Lemma const2GV_typsize_mutind : 
  (forall S td c t H, @const2GV__getTypeSizeInBits_Prop S td c t H) /\
  (forall sdct H, @consts2GV__getTypeSizeInBits_Prop sdct H).
Proof.
  (wfconst_cases (apply wf_const_mutind; 
                    unfold const2GV__getTypeSizeInBits_Prop, 
                           consts2GV__getTypeSizeInBits_Prop) Case);
    intros; subst; simpl in *;
    try (assert (HwfTD':=HwfTD); 
         inversion HwfTD' as [? ? ? Htys Hwftd]; subst).
Case "wfconst_zero".
  remember (zeroconst2GV (los, nts) typ5) as R.
  destruct R; inv H1.
  split; auto.
    eapply zeroconst2GV__getTypeSizeInBits; 
      try solve [eauto | constructor; auto].

Case "wfconst_int".
  inv H1.
  split; auto.
  exists (Size.to_nat sz5). 
  exists (getIntAlignmentInfo los (Size.to_nat sz5) true).
  erewrite int_typsize; eauto.

Case "wfconst_floatingpoint".
  destruct floating_point5; inv H1; 
    simpl; unfold size_chunk_nat, size_chunk, bytesize_chunk; split; auto.
    exists 32%nat. exists (getFloatAlignmentInfo los 32 true).
    simpl. auto.

    exists 64%nat. exists (getFloatAlignmentInfo los 64 true).
    simpl. auto.

Case "wfconst_undef".
  remember (gundef (los, nts) typ5) as R.
  destruct R; inv H1.
  split; auto.
    eapply gundef__getTypeSizeInBits; try solve [eauto | constructor; auto].

Case "wfconst_null".
  inv H1. simpl.
  split; auto.
    exists (Size.to_nat (getPointerSizeInBits los)).
    exists (getPointerAlignmentInfo los true).
    unfold getPointerSizeInBits. simpl. auto.

Case "wfconst_array". Focus.
  remember (_list_const_arr2GV (los, nts) gl typ5 const_list) as R.
  destruct R; inv H2.
  remember (split
             (unmake_list_system_targetdata_const_typ
                (make_list_system_targetdata_const_typ
                   (map_list_const
                      (fun const_ : const =>
                       (system5, (los, nts):targetdata, const_, typ5)) 
                      const_list)))) as R.
  destruct R as [lsdc lt]. 
  remember (split lsdc) as R'.
  destruct R' as [lsd lc].
  remember (split lsd) as R''.
  destruct R'' as [ls ld].
  rewrite e in H4. unfold Size.to_nat in *.
  destruct sz5; inv H4.
    split; auto.
    exists 8%nat. exists 1%nat. 
    split; auto.

    split; auto.
    destruct (@H system5 (los,nts) los nts gl) as [J1 J2]; 
      eauto using const2GV_typsize_mutind_array.
    symmetry in HeqR.
    assert (make_list_const lc = const_list) as EQ.
      eapply make_list_const_spec2; eauto.
    rewrite <- EQ in HeqR.
    apply J1 in HeqR; eauto using make_list_const_spec4.
    destruct HeqR as [sz [J3 J4]].
    apply getTypeAllocSize_inv in J3.
    destruct J3 as [sz0 [al0 [J31 [J32 J33]]]]; subst.
    unfold getTypeSizeInBits_and_Alignment in J32.
    unfold getTypeSizeInBits_and_Alignment_for_namedts in J32.
    rewrite J32.
    rewrite <- J4.        
    exists (RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz0) 8)) al0 * 8 *
             S sz5)%nat. exists al0.
    rewrite length_unmake_make_list_const in e. rewrite e.
    split; auto.
      rewrite ZRdiv_prop8. auto.

Unfocus.

Case "wfconst_struct". Focus.
  remember (split 
              (unmake_list_system_targetdata_const_typ
                 (make_list_system_targetdata_const_typ
                    (map_list_const_typ
                      (fun (const_ : const) (typ_ : typ) =>
                       (system5, (layouts5, namedts5):targetdata, const_, typ_))
                      const_typ_list)))) as R.
  destruct R as [lsdc lt]. 
  remember (split lsdc) as R'.
  destruct R' as [lsd lc].
  remember (split lsd) as R''.
  destruct R'' as [ls ld].
  remember (_list_const_struct2GV (los, nts) gl
           (make_list_const
              (map_list_const_typ (fun (const_ : const) (_ : typ) => const_)
                 const_typ_list))) as R1.
  destruct R1 as [[gv0 ts]|]; inv H2.
  inv H0.
  destruct (@H system5 (los,nts) los nts gl) as [J1 J2]; 
    eauto using const2GV_typsize_mutind_struct.

  symmetry in HeqR1.
  erewrite <- map_list_const_typ_spec2 in HeqR1; eauto.
  apply J2 in HeqR1; eauto using map_list_const_typ_spec3. clear J1 J2 H.
  destruct HeqR1 as [J5 [sz [al [J6 J7]]]]; subst.

  erewrite <- map_list_const_typ_spec1 in e0; eauto.
  rewrite e0 in H5.
  erewrite <- typ_eq_list_typ_spec2; try solve [destruct Hwftd; eauto | tauto].
  simpl. rewrite J6.
  destruct gv0; inv H5.
    split; auto.
      destruct sz.
        exists 8%nat. exists 1%nat. 
        split; auto. 

        assert (Coqlib.ZRdiv (Z_of_nat (S sz0)) 8 > 0) as J.
          apply Coqlib.ZRdiv_prop3; auto using Coqlib.Z_of_S_gt_O; omega.
        apply nat_of_Z_inj_gt in J; try omega. simpl in J, J7.
        rewrite J7 in J. contradict J. omega.

    rewrite <- J7.
    split; auto.
      destruct sz.
        clear - J7.
        assert (J := @sizeGenericValue_cons_pos p gv0).
        rewrite <- J7 in J. contradict J; simpl; omega.

        eauto.

Unfocus.

Case "wfconst_gid".
  remember (lookupAL GenericValue gl id5) as R.
  destruct R; inv H1.
  split; auto.
    apply H2 in e.
    destruct e as [gv0 [sz [J1 [J2 J3]]]].
    rewrite J1 in HeqR. inv HeqR.
    unfold getTypeSizeInBits in J2. simpl in J2.
    inv J2.
    rewrite <- J3. eauto.

Case "wfconst_trunc_int". Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  remember (mtrunc (los, nts) truncop_int t (typ_int sz2) g) as R.
  destruct R; inv H4.
  split; auto.
   symmetry in HeqR.
   eapply mtrunc_typsize in HeqR; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_trunc_fp". Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  remember (mtrunc (los, nts) truncop_int t (typ_floatpoint floating_point2) g) 
    as R.
  destruct R; inv H4.
  split; auto.
   symmetry in HeqR.
   eapply mtrunc_typsize in HeqR; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_zext". Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  remember (mext (los, nts) extop_z t (typ_int sz2) g) as R.
  destruct R; inv H4.
  split; auto.
    symmetry in HeqR.
    eapply mext_typsize in HeqR; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_sext".  Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  remember (mext (los, nts) extop_s t (typ_int sz2) g) as R.
  destruct R; inv H4.
  split; auto.
    symmetry in HeqR.
    eapply mext_typsize in HeqR; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_fpext".  Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  remember (mext (los, nts) extop_fp t (typ_floatpoint floating_point2) g) as R.
  destruct R; inv H4.
  split; auto.
    symmetry in HeqR.
    eapply mext_typsize in HeqR; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_ptrtoint". Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  simpl.
  split; auto.
    exists (Size.to_nat sz5).
    exists (getIntAlignmentInfo los (Size.to_nat sz5) true).
    erewrite int_typsize; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_inttoptr". Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  split; auto.
    exists (Size.to_nat (getPointerSizeInBits los)).
    exists (getPointerAlignmentInfo los true).
    simpl. auto.
Unfocus.

Case "wfconst_bitcast". Focus.
  remember (_const2GV (los, nts) gl const5) as R1.
  destruct R1 as [[]|]; inv H2.
  remember (mbitcast t g (typ_pointer typ2)) as R.
  destruct R; inv H4.
  unfold mbitcast in HeqR.
  destruct t; inv HeqR.
  eapply H in H1; eauto.
  destruct H1; eauto.
Unfocus.

Case "wfconst_gep". Focus.
  inv f.
  remember (_const2GV (los, nts) gl const_5) as R1.
  destruct R1 as [[]|]; tinv H3.
  destruct t; tinv H3.
  symmetry in HeqR1.
  eapply H in HeqR1; eauto.
  destruct HeqR1 as [Heq [sz [al [J1 J2]]]].
  inv J1. inv Heq.
  rewrite e0 in H3.
  assert(
    match gundef (los, nts) typ' with
       | ret gv => ret (gv, typ')
       | merror => merror
       end = ret (gv, t') ->
    typ' = t' /\
    (exists sz0 : nat,
      exists al : nat,
        _getTypeSizeInBits_and_Alignment los
          (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
          true typ' = ret (sz0, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz0) 8) = sizeGenericValue gv)) as G.
    intros W3.
    remember (gundef (los, nts) typ') as R3;
    destruct R3; inv W3;
    split; try solve 
      [auto | eapply gundef__getTypeSizeInBits with (s:=system5); 
                try solve [eauto | constructor; auto]].
  remember (GV2ptr (los, nts) (getPointerSize0 los) g) as R.
  destruct R; auto.
    remember (intConsts2Nats (los, nts) const_list) as R2.
    destruct R2; auto.
      remember (mgep (los, nts) t v l0) as R3.
      destruct R3; auto.
        inv H3.
        split; auto.  
          unfold getConstGEPTyp in e0.
          destruct const_list; tinv e0.  
          remember (getSubTypFromConstIdxs const_list t) as R4.
          destruct R4; inv e0. 
          simpl.
          exists (Size.to_nat (getPointerSizeInBits los)).
          exists (getPointerAlignmentInfo los true).
          auto.

Unfocus.

Case "wfconst_select". Focus.
  remember (_const2GV (los, nts) gl const0) as R0.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R0 as [[gv0 t0]|]; tinv H4.
  destruct R1 as [[gv1 t1]|]; tinv H4.
  destruct R2 as [[gv2 t2]|]; tinv H4.
  destruct (isGVZero (los, nts) gv0); inv H4; eauto.
Unfocus.

Case "wfconst_icmp". Focus.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H3.
  destruct R2 as [[gv2 t2]|]; tinv H3.
  remember (micmp (los, nts) cond5 t1 gv1 gv2) as R3.
  destruct R3; inv H3; eauto.
  split; auto.
    symmetry in HeqR3.
    eapply micmp_typsize in HeqR3; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_fcmp". Focus.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H3.
  destruct_typ t1; tinv H3.
  destruct R2 as [[gv2 t2]|]; tinv H3.
  remember (mfcmp (los, nts) fcond5 f1 gv1 gv2) as R3.
  destruct R3; inv H3; eauto.
  split; auto.
    symmetry in HeqR3.
    eapply mfcmp_typsize in HeqR3; try solve [eauto | constructor; auto]. 
Unfocus.

Case "wfconst_extractvalue". Focus.
  remember (_const2GV (los, nts) gl const_5) as R1.
  destruct R1 as [[gv1 t1]|]; tinv H3.
  remember (getSubTypFromConstIdxs const_list t1) as R2.
  destruct R2 as [t2|]; tinv H3.
  remember (extractGenericValue (los, nts) t1 gv1 const_list) as R3.
  destruct R3 as [gv2|]; inv H3.
  clear H0.
  symmetry in HeqR1.
  inv f.
  apply H in HeqR1; auto.
  destruct HeqR1 as [Heq [sz [al [J1 J2]]]]; subst.
  destruct e0 as [idxs [o [J3 J4]]].
  symmetry in J3.
  eapply getSubTypFromConstIdxs__mgetoffset in J3; eauto.
  subst.
  split; eauto.
    eapply extractGenericValue_typsize; try solve [eauto | constructor; auto].

Unfocus.

Case "wfconst_insertvalue". Focus.
  clear H1.
  remember (_const2GV (los, nts) gl const_5) as R1.
  destruct R1 as [[gv1 t1]|]; tinv H4.
  remember (_const2GV (los, nts) gl const') as R2.
  destruct R2 as [[gv2 t2]|]; tinv H4.
  remember (insertGenericValue (los, nts) t1 gv1 const_list t2 gv2) as R3.
  destruct R3 as [gv3|]; inv H4.
  symmetry in HeqR1.
  apply H in HeqR1; auto.
  destruct HeqR1 as [Heq [sz [al [J1 J2]]]]; subst.
  rewrite J1. 
  symmetry in HeqR2.
  inv f.
  apply H0 in HeqR2; auto.
  destruct HeqR2 as [Heq [sz2 [al2 [J3 J4]]]]; subst.
  split; auto.
    exists sz. exists al.
    split; auto.
      eapply insertGenericValue_typsize in HeqR3; 
        try solve [eauto | constructor; auto].
      rewrite <- HeqR3. auto.

Unfocus.

Case "wfconst_bop". Focus.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H3.
  destruct_typ t1; tinv H3.
  destruct R2 as [[gv2 t2]|]; tinv H3.
  remember (mbop (los, nts) bop5 s0 gv1 gv2) as R3.
  destruct R3; inv H3.
  symmetry in HeqR1.
  apply H in HeqR1; auto.
  destruct HeqR1 as [Heq _]. inv Heq.
  split; auto.
    symmetry in HeqR3.
    eapply mbop_typsize in HeqR3; eauto.

Unfocus.

Case "wfconst_fbop". Focus.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H3.
  destruct_typ t1; tinv H3.
  destruct R2 as [[gv2 t2]|]; tinv H3.
  remember (mfbop (los, nts) fbop5 f gv1 gv2) as R3.
  destruct R3; inv H3.
  symmetry in HeqR1.
  apply H in HeqR1; auto.
  destruct HeqR1 as [Heq _]. inv Heq.
  split; auto.
    symmetry in HeqR3.
    eapply mfbop_typsize in HeqR3; eauto.

Unfocus.

Case "wfconst_nil".
  intros; subst.

  split; intros; subst.
    inv H2. 
    apply feasible_typ_inv' in H.
    destruct H as [sz [al [H H']]].
    unfold getTypeAllocSize. unfold getTypeStoreSize. unfold getTypeSizeInBits.
    unfold getABITypeAlignment. unfold getAlignment.
    rewrite H. simpl. eauto.

    inv H1. simpl.
    split; eauto.    

Case "wfconst_cons".
  remember (split (unmake_list_system_targetdata_const_typ l')) as R1.
  destruct R1 as [lsdc lt].
  simpl.  
  remember (split lsdc) as R2.
  destruct R2 as [lsd lc].
  simpl.  
  remember (split lsd) as R3.
  destruct R3 as [ls ld].
  simpl.
  intros S TD los nts gl HwfTD EQ Hwfl; subst.
  split.
    intros gv t Hft Hin Hc2g.
    remember (_list_const_arr2GV (los, nts) gl t (make_list_const lc)) as R.
    destruct R; try solve [inv Hc2g].
    remember (_const2GV (los, nts) gl const_) as R'.
    destruct R' as [[gv0 t0]|]; try solve [inv Hc2g].
    destruct (typ_dec t t0); subst; try solve [inv Hc2g].
    remember (getTypeAllocSize (los, nts) t0) as R1.
    destruct R1; inv Hc2g.
    assert (typ5 = t0) as EQ. eapply Hin; eauto.
    subst.
    exists s. split; auto.
    apply wf_list_targetdata_typ_cons_inv in Hwfl.
    destruct Hwfl as [J1 [J2 [J3 J4]]]; subst.
    symmetry in HeqR'.
    apply H in HeqR'; auto.
    destruct HeqR' as [Heq [sz [al [J5 J6]]]]; subst.
    eapply H0 in J1; eauto. destruct J1 as [J1 _]. clear H H0.
    symmetry in HeqR.
    apply J1 in HeqR; auto.
    destruct HeqR as [sz0 [J7 J8]].
    simpl_env.
    rewrite sizeGenericValue__app.
    rewrite sizeGenericValue__app.
    rewrite sizeGenericValue__uninits.
    rewrite <- J8. rewrite <- J6.
    rewrite J7 in HeqR0. inv HeqR0.
    erewrite getTypeAllocSize_roundup; eauto.

    intros gv lt' [J1 J2] Hc2g.
    remember (_list_const_struct2GV (los, nts) gl (make_list_const lc)) as R.
    destruct R as [[gv1 ts1]|]; try solve [inv Hc2g].
    remember (_const2GV (los, nts) gl const_) as R'.
    destruct R' as [[gv0 t0]|]; try solve [inv Hc2g].
    remember (getTypeAllocSize (los, nts) t0) as R1.
    destruct R1; inv Hc2g.
    apply wf_list_targetdata_typ_cons_inv in Hwfl.
    destruct Hwfl as [J1' [J2' [J3 J4]]]; subst.
    symmetry in HeqR'.
    apply H in HeqR'; auto.
    destruct HeqR' as [Heq [sz [al [J5 J6]]]]; subst.
    eapply H0 in J1'; eauto. destruct J1' as [_ J1']. clear H H0.
    symmetry in HeqR.
    apply J1' in HeqR; auto.
    destruct HeqR as [Heq [sz0 [al0 [J7 J8]]]]; subst.
    split; auto.
    rewrite sizeGenericValue__app.
    rewrite sizeGenericValue__app.
    rewrite sizeGenericValue__uninits.
    rewrite <- J8. rewrite <- J6. simpl. rewrite J7. rewrite J5.
    erewrite getTypeAllocSize_roundup; eauto.
    exists (sz0 +
             RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) al * 8)%nat.
    exists (if le_lt_dec al al0 then al0 else al).
    split; auto.
      eapply getTypeAllocSize_inv' in J5; eauto. subst.
      apply ZRdiv_prop9.
Qed.

Lemma const2GV__getTypeSizeInBits_aux : forall S los nts c t gl gv t'
  (HwfTD: wf_namedts S (los, nts)),
  wf_const S (los, nts) c t ->
  feasible_typ (los, nts) t ->
  _const2GV (los, nts) gl c = Some (gv, t') ->
  wf_global (los, nts) S gl ->
  t = t' /\
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los, nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof.
  intros. inv H0.
  destruct const2GV_typsize_mutind. 
  eapply H0; eauto.
Qed.

Lemma cundef_gv__getTypeSizeInBits : forall S los nts gv t sz al,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = 
    sizeGenericValue (cundef_gv gv t).
Proof.
  intros.
  destruct_typ t; simpl in *; auto.
    inv H0.
    erewrite int_typsize; eauto.

    destruct f; tinv H; inv H0; auto.

    inv H0. auto.
Qed.

Lemma cgv2gv__getTypeSizeInBits : forall S los nts gv t sz al,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = 
    sizeGenericValue (cgv2gv gv t).
Proof.
  intros.
  destruct gv; auto.
  destruct p.
  destruct v; auto.
  destruct gv; auto.
  simpl. eapply cundef_gv__getTypeSizeInBits; eauto.
Qed.

Lemma const2GV__getTypeSizeInBits : forall S los nts c t gl gv 
  (Hwf: wf_namedts S (los, nts)) (Huniq: uniq nts),
  wf_typ S t ->
  wf_const S (los, nts) c t ->
  feasible_typ (los, nts) t ->
  const2GV (los, nts) gl c = Some gv ->
  wf_global (los, nts) S gl ->
  exists sz, 
    getTypeSizeInBits (los, nts) t = Some sz /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof.
  intros.
  unfold const2GV in H2.
  remember (_const2GV (los, nts) gl c) as R.
  destruct R as [[]|]; inv H2.
  symmetry in HeqR.
  unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment.
  eapply const2GV__getTypeSizeInBits_aux in HeqR; eauto.
  destruct HeqR as [Heq [sz [al [J1 J2]]]]; subst.
  exists sz. 
  rewrite J1.
  split; auto.
    eapply cgv2gv__getTypeSizeInBits; eauto.
Qed.

Lemma fit_gv__getTypeSizeInBits : forall TD gv s t gv'
  (Hwft : wf_typ s t) (Hty: ty_namedts s (snd TD))
  (H0 : feasible_typ TD t)
  (HeqR : ret gv' = fit_gv TD t gv),
  exists sz, 
    getTypeSizeInBits TD t = Some sz /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv'.
Proof.
  intros.
  unfold fit_gv in HeqR.
  assert (J:=H0).
  eapply feasible_typ_inv in H0; eauto.
  destruct H0 as [sz [al [J1 [J2 J3]]]].
  unfold getTypeSizeInBits in *.
  exists sz.
  rewrite J1 in HeqR. rewrite J1.
  split; auto.
    remember (sizeGenericValue gv =n= 
                Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8))
      as R.
    destruct R.
      inv HeqR.
      apply beq_nat_eq in HeqR0; auto.

      destruct TD.
      eapply gundef__getTypeSizeInBits in J; eauto.
      destruct J as [sz0 [al0 [J4 J5]]].
      unfold getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts in J1.
      rewrite J1 in J4.
      inv J4. auto.
Qed.

Definition flatten_typ__getTypeSizeInBits_prop (t:typ) := forall s los nts mc,
  flatten_typ (los,nts) t = Some mc ->
  wf_typ s t -> LLVMtd.feasible_typ (los,nts) t ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeMC mc.

Definition flatten_typs__getListTypeSizeInBits_prop (lt:list_typ) := 
  forall los nts mc lst,
  flatten_typs (los,nts) lt = Some mc ->
  wf_typ_list lst -> LLVMtd.feasible_typs (los,nts) lt ->
  (exists ls, 
    split (unmake_list_system_typ lst) = (ls, unmake_list_typ lt)) ->
  exists sz, exists al,
    _getListTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) lt = 
        Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeMC mc.

Lemma flatten_typ_typsize_mutrec :
  (forall t, flatten_typ__getTypeSizeInBits_prop t) *
  (forall lt, flatten_typs__getListTypeSizeInBits_prop lt).
Proof.
  (typ_cases (apply typ_mutrec; 
    unfold flatten_typ__getTypeSizeInBits_prop, 
           flatten_typs__getListTypeSizeInBits_prop) Case);
    intros; simpl in *; try solve [eauto | inversion H | inversion H1 ].
Case "typ_int".
  inv H.
  simpl.
  exists (Size.to_nat s). 
  exists (getIntAlignmentInfo los (Size.to_nat s) true).
  erewrite int_typsize; eauto.

Case "typ_floatingpoint".
  destruct f; 
    inv H; simpl; unfold size_chunk_nat, size_chunk, bytesize_chunk.
    exists 32%nat. exists (getFloatAlignmentInfo los 32 true).
    simpl. auto.

    exists 64%nat. exists (getFloatAlignmentInfo los 64 true).
    simpl. auto.

Case "typ_array".
  destruct s;  try solve [inv H0; exists 8%nat; exists 1%nat; auto].
  remember (flatten_typ (los, nts) t) as R1.
  destruct R1; try solve [inv H0].
  remember (getTypeAllocSize (los, nts) t) as R2.
  destruct R2 as [s1|]; inv H0.
  assert (
    (l0 ++ uninitMCs (Size.to_nat s1 - sizeMC l0)) ++
          repeatMC (l0 ++ uninitMCs (Size.to_nat s1 - sizeMC l0)) s = 
    repeatMC (l0 ++ uninitMCs (Size.to_nat s1 - sizeMC l0)) (S s)) as G.
    simpl. auto.
  rewrite G.
  symmetry in HeqR1.
  inv H1.
  apply H with (s:=s0) in HeqR1; eauto using feasible_array_typ_inv.
  destruct HeqR1 as [sz [al [J1 J2]]].
  rewrite J1.  rewrite J2.
  exists (RoundUpAlignment (sizeMC l0) al * 8 * Size.to_nat (S s))%nat.
  exists al.
  split; auto.
  unfold getTypeAllocSize, getABITypeAlignment, getAlignment, getTypeStoreSize,
    getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
    getTypeSizeInBits_and_Alignment_for_namedts in HeqR2.
  rewrite J1 in HeqR2.
  inv HeqR2.
  rewrite sizeMC__repeatMC.
  rewrite sizeMC__app.
  rewrite sizeMC__uninitMCs. rewrite J2. unfold Size.to_nat.
  assert (RoundUpAlignment (sizeMC l0) al >= (sizeMC l0))%nat as J3.
    apply RoundUpAlignment_spec.
      change (LLVMtd.feasible_typ (los, nts) t) in H2; auto.
      eapply feasible_typ_inv' in H2; eauto.
      destruct H2 as [sz0 [al0 [J3 J4]]].
      unfold getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts in J3.
      rewrite J1 in J3. inv J3. auto.

  assert ((sizeMC l0 + (RoundUpAlignment (sizeMC l0) al - sizeMC l0))%nat = 
     (RoundUpAlignment (sizeMC l0) al)) as J4.
    rewrite <- le_plus_minus; auto.
  rewrite J4.
  rewrite ZRdiv_prop8.
  ring.

Case "typ_struct".
  remember (flatten_typs (los, nts) l0) as R1.
  destruct R1; inv H0.
  symmetry in HeqR1.
  inv H1.
  eapply H in HeqR1; eauto using list_system_typ_spec, feasible_struct_typ_inv.
  destruct HeqR1 as [sz [al [J1 J2]]].
  rewrite J1.
  destruct sz.
    exists 8%nat. exists 1%nat.
    split; auto.
      simpl in J2.
      destruct l1; inv H4; auto.
        simpl in J2.
        assert (J3 := size_chunk_nat_pos' m).
        contradict J2; omega.

    exists (S sz0). exists al.
    split; auto.
      rewrite J2.
      destruct l1; inv H4; auto.
        assert (Coqlib.ZRdiv (Z_of_nat (S sz0)) 8 > 0) as J.
          apply Coqlib.ZRdiv_prop3; try solve [omega | apply Coqlib.Z_of_S_gt_O].
        apply Coqlib.nat_of_Z_pos in J.
        contradict J2. simpl in *. omega.

Case "typ_pointer".
  inv H0.
  exists (Size.to_nat (getPointerSizeInBits los)).
  exists (getPointerAlignmentInfo los true).
  split; auto.
     
Case "typ_nil".
  inv H. 
  exists 0%nat. exists 0%nat. auto.

Case "typ_cons".
  destruct H4 as [ls H4].
  apply unmake_list_system_typ_inv in H4.
  destruct H4 as [s [ls' [lst' [J1 [J2 J3]]]]]; subst.
  inv H2.
  remember (flatten_typs (los, nts) l0) as R1.
  destruct R1; inv H1.
  remember (flatten_typ (los, nts) t) as R2.
  destruct R2; inv H4.
  remember (getTypeAllocSize (los, nts) t) as R3.
  destruct R3; inv H2.
  symmetry in HeqR1. symmetry in HeqR2.
  destruct H3 as [H31 H32].
  eapply H in HeqR2; eauto.
  eapply H0 in HeqR1; eauto.
  destruct HeqR1 as [sz1 [al1 [J4 J5]]].
  destruct HeqR2 as [sz2 [al2 [J6 J7]]].
  rewrite J4. rewrite J6.
  rewrite sizeMC__app.
  rewrite sizeMC__app.
  rewrite sizeMC__uninitMCs. 
  rewrite <- J5. rewrite <- J7. 
  erewrite getTypeAllocSize_roundup; eauto.
  eapply getTypeAllocSize_inv' in J6; eauto. subst.
  exists ((sz1 +
             RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8)) al2 * 8 )%nat).
  exists (if le_lt_dec al2 al1 then al1 else al2).
  split; auto.
    apply ZRdiv_prop9.
Qed.

Lemma flatten_typ__getTypeSizeInBits : forall t s los nts mc,
  flatten_typ (los,nts) t = Some mc ->
  wf_typ s t -> feasible_typ (los,nts) t ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeMC mc.
Proof. intros. inv H1.
  destruct flatten_typ_typsize_mutrec. eapply f; eauto.
Qed.

Lemma mload__getTypeSizeInBits : forall t s TD gv a ptr M,
  mload TD M ptr t a = Some gv ->
  wf_typ s t -> feasible_typ TD t ->
  exists sz, 
    getTypeSizeInBits TD t = Some sz /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof.
  intros.
  apply mload_inv in H.
  destruct H as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment.
  erewrite <- mload_aux__sizeGenericValue; eauto.
  destruct TD.
  eapply flatten_typ__getTypeSizeInBits in J2; eauto.
  destruct J2 as [sz [al [J21 J22]]].
  rewrite J21. eauto.
Qed.
 
Lemma mset'_is_total : forall S (TD : TargetData) ofs (t1 t2 : typ) 
  (H0 : feasible_typ TD t1)
  (w1 : wf_typ S t1),
  forall x y, exists z : GenericValue, mset' TD ofs t1 t2 x y = ret z.
Proof.
  intros.
  unfold mset'. unfold mset.
  destruct (getTypeStoreSize TD t2); simpl; eauto using gundef__total'.
  destruct (n =n= length y); eauto using gundef__total'.
  destruct (splitGenericValue x ofs); eauto using gundef__total'.
  destruct p.  
  destruct (splitGenericValue g0 (Z_of_nat n)); eauto using gundef__total'.
  destruct p. eauto.
Qed.

Lemma mget'_is_total : forall S TD ofs t' 
  (H0 : feasible_typ TD t')
  (w1 : wf_typ S t'),
  forall x, exists z, mget' TD ofs t' x = Some z.
Proof.
  intros.
  unfold mget'. unfold mget.
  destruct (getTypeStoreSize TD t'); simpl; eauto using gundef__total'.
  destruct (splitGenericValue x ofs); eauto using gundef__total'.
  destruct p.  
  destruct (splitGenericValue g0 (Z_of_nat n)); eauto using gundef__total'.
  destruct p. eauto.
Qed.

Definition flatten_typ_total_prop (t:typ) := forall TD,
  Constant.wf_zeroconst_typ t -> LLVMtd.feasible_typ TD t ->
  exists gv, flatten_typ TD t = Some gv.

Definition flatten_typs_total_prop (lt:list_typ) := forall TD,
  Constant.wf_zeroconsts_typ lt -> LLVMtd.feasible_typs TD lt ->
  exists gvs, flatten_typs TD lt = Some gvs.

Lemma flatten_typ_total_mutrec :
  (forall t, flatten_typ_total_prop t) *
  (forall lt,flatten_typs_total_prop lt).
Proof.
  apply typ_mutrec; 
    unfold flatten_typ_total_prop, flatten_typs_total_prop;
    intros; simpl in *; try solve [eauto | inversion H | inversion H1 ].
Case "float".
  destruct f; try solve [eauto | inversion H].
Case "array".
  destruct H with (TD:=TD) as [gv Hz2c]; auto.
  rewrite Hz2c.
  destruct s; eauto.
  apply feasible_array_typ_inv in H1.
  apply feasible_typ_inv'' in H1. 
  destruct H1 as [ssz [asz [J1 J2]]].
  rewrite J2.
  eauto.

Case "struct".
  destruct (@H TD) as [gv Hz2c]; auto.
  rewrite Hz2c. destruct gv; eauto.

Case "cons".
  destruct H1 as [J1 J2].
  apply feasible_cons_typs_inv in H2.
  destruct H2 as [J3 J4].
  destruct (@H TD) as [gv Hz2c]; auto.
  destruct (@H0 TD) as [gvs Hz2cs]; auto.
  rewrite Hz2cs. rewrite Hz2c.
  apply feasible_typ_inv'' in J3.  
  destruct J3 as [ssz [asz [J6 J5]]].
  rewrite J5. eauto.
Qed.

Lemma flatten_typ_total : forall TD t,
  Constant.wf_zeroconst_typ t ->
  feasible_typ TD t ->
  exists gv, flatten_typ TD t = Some gv.
Proof.
  intros. inv H0.
  destruct flatten_typ_total_mutrec as [J _].
  apply J; auto.
Qed.

