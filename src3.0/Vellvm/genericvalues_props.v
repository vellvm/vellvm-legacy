Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
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
(** * total *)

Definition flatten_typ_aux_total_prop S TD t :=
  wf_styp S TD t ->
  forall los nts nts' acc
  (Hsize: exists sz, exists al, 
     getTypeSizeInBits_and_Alignment (los, nts') true t = Some (sz,al))
  (Hnc: forall id5,
          lookupAL _ nts id5 <> None ->
          exists gv5, lookupAL _ acc id5 = Some (Some gv5)),
  TD = (los, nts) ->
  exists gv, flatten_typ_aux (los, nts') acc t = Some gv.

Definition flatten_typs_aux_total_prop sdt :=
  wf_styp_list sdt ->
  let 'lsdt := unmake_list_system_targetdata_typ sdt in
  let '(lsd, lt) := split lsdt in
  forall S TD los nts nts' acc
  (Hsize: exists sz, exists al, 
     getListTypeSizeInBits_and_Alignment (los, nts') true (make_list_typ lt) = 
       Some (sz, al))
  (Hnc: forall id5,
          lookupAL _ nts id5 <> None ->
          exists gv5, lookupAL _ acc id5 = Some (Some gv5)),
  TD = (los, nts) ->
  eq_system_targetdata S TD lsd ->
  exists gvs, flatten_typs_aux (los, nts') acc (make_list_typ lt) = Some gvs.

Lemma flatten_typ_aux_total_mutrec :
  (forall S TD t, flatten_typ_aux_total_prop S TD t) /\
  (forall sdt, flatten_typs_aux_total_prop sdt).
Proof.
  (wfstyp_cases (apply wf_styp_mutind; 
                 unfold flatten_typ_aux_total_prop, 
                        flatten_typs_aux_total_prop) Case);
    intros; subst; simpl in *; uniq_result; eauto.
Case "wf_styp_structure".
  remember (split
              (unmake_list_system_targetdata_typ
                (make_list_system_targetdata_typ
                   (map_list_typ
                      (fun typ_ : typ => (system5, (los, nts):targetdata, typ_))
                      typ_list)))) as R.
  destruct R as [lsd lt].
  assert (make_list_typ lt = typ_list) as EQ1. 
    eapply make_list_typ_spec2; eauto.
  subst.
  assert (eq_system_targetdata system5 (los, nts) lsd) as EQ2.
    eapply wf_styp__feasible_typ_aux_mutrec_struct; eauto.
  subst.
  destruct Hsize as [sz [al Hsize]].
  inv_mbind. 
  eapply H1 with (nts':=nts') in Hnc; eauto.
  fill_ctxhole. destruct x; eauto.
Case "wf_styp_array".
  destruct sz5; eauto.
  destruct Hsize as [sz [al Hsize]].
  inv_mbind.
  unfold getTypeAllocSize, getTypeStoreSize, getABITypeAlignment,
         getTypeSizeInBits, getAlignment, getTypeSizeInBits_and_Alignment,
         getTypeSizeInBits_and_Alignment_for_namedts.
  eapply H0 with (nts':=nts')(acc:=acc) in Hnc; eauto.
    repeat fill_ctxhole. eauto.
Case "wf_styp_namedt".
  destruct (@Hnc id5) as [gv5 J]; try congruence.
    fill_ctxhole. eauto.  
Case "wf_styp_cons".
  remember (split (unmake_list_system_targetdata_typ l')) as R.
  destruct R as [lsd lt]. simpl.
  intros. subst.
  apply eq_system_targetdata_cons_inv in H4. 
  destruct H4 as [H4 [EQ1 EQ2]]; subst.
  destruct Hsize as [sz [al Hsize]].
  inv_mbind.
  assert (J:=Hnc).
  eapply H0 with (nts':=nts') in J; eauto. clear H0.
  eapply H2 with (nts':=nts') in Hnc; eauto. clear H2.
  unfold getTypeAllocSize, getTypeStoreSize, getABITypeAlignment,
         getTypeSizeInBits, getAlignment, getTypeSizeInBits_and_Alignment,
         getTypeSizeInBits_and_Alignment_for_namedts.
  repeat fill_ctxhole. eauto.
Qed.

Lemma flatten_typ_for_namedts_spec2: forall TD los i0 r nts2
  lt2 nts1 nts (Huniq: uniq nts),
  flatten_typ_aux TD (flatten_typ_for_namedts TD los nts2) 
    (typ_struct lt2) = r ->
  nts = nts1 ++ (i0,lt2) :: nts2 ->  
  lookupAL _ (flatten_typ_for_namedts TD los nts) i0 = Some r.
Proof.
  induction nts1 as [|[]]; intros; subst; simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i0); 
      try congruence; auto.
     
    inv Huniq.
    simpl_env in H3.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i1); subst.
      contradict H3; fsetdec.
      eapply IHnts1 in H1; eauto.
Qed.

Lemma flatten_typ_for_namedts_total: forall S los nts 
  (H: noncycled S los nts) (Huniq: uniq nts), 
  forall id5 lt nts2 nts1 nts'
  (EQ: nts = nts1 ++ (id5,lt) :: nts2)
  (Hsize: forall id5 lt5, 
     lookupAL _ nts id5 = Some lt5 ->
     exists sz0 : nat, exists al : nat,
       getTypeSizeInBits_and_Alignment (los, nts') true (typ_struct lt5) =
         Some (sz0, al)),
  exists gvs, 
    flatten_typ_aux (los, nts')
      (flatten_typ_for_namedts (los,nts') los nts2) (typ_struct lt) = Some gvs.
Proof.
Local Opaque getListTypeSizeInBits_and_Alignment getTypeSizeInBits_and_Alignment.
  induction 1; simpl; intros; subst.
    symmetry in EQ.    
    apply app_eq_nil in EQ.
    destruct EQ as [_ EQ].
    congruence.

    inv Huniq.
    destruct nts1 as [|[]]; inv EQ.
      destruct flatten_typ_aux_total_mutrec as [J _].
      eapply J in H0; eauto.
      assert (exists sz0 : nat, exists al : nat,
               getTypeSizeInBits_and_Alignment (layouts5, nts') true 
                 (typ_struct lt) = ret (sz0, al)) as Hty.
        apply Hsize with (id5:=id0).
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id0 id0); 
          try congruence.
      eapply H0 in Hty; eauto.  
      intros id5 H1.
      apply lookupAL_middle_inv' in H1.
      destruct H1 as [l0 [l1 [l2 HeqR]]].
      assert (J':=HeqR). subst.
      eapply IHnoncycled with (nts':=nts') in J'; eauto.
        destruct J' as [gv J'].
        exists gv. 
        eapply flatten_typ_for_namedts_spec2; eauto.
  
        intros.
        apply Hsize with (id6:=id1).
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); 
          subst; auto.
          apply notin_lookupAL_None in H5. congruence.
    
      assert (nts1 ++ (id0, lt) :: nts2 = nts1 ++ (id0, lt) :: nts2) as EQ. auto.
      eapply IHnoncycled in EQ; eauto.
        intros.
        apply Hsize with (id5:=id5).
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id5 i0); 
          subst; auto.
          apply notin_lookupAL_None in H5. congruence.
Transparent getListTypeSizeInBits_and_Alignment getTypeSizeInBits_and_Alignment.
Qed.

Lemma flatten_typ_total : forall S td t
  (Hty: wf_typ S td t),
  exists gv, flatten_typ td t = Some gv.
Proof.
  intros.
  assert (G:=Hty).
  apply wf_typ__getTypeSizeInBits_and_Alignment in G; auto.
  destruct G as [sz [al [G1 [G2 G3]]]].
  unfold flatten_typ.
  inv Hty.
  destruct flatten_typ_aux_total_mutrec as [J' _].
  eapply J'; eauto.
  intros id5 J.
  apply lookupAL_middle_inv' in J.
  destruct J as [l0 [l1 [l2 HeqR]]]. subst.
  eapply flatten_typ_for_namedts_total
    with (nts':=l1 ++ (id5, l0) :: l2) in H; eauto.
    destruct H as [gv H].
    exists gv.
    eapply flatten_typ_for_namedts_spec2; eauto.

    intros id0 lt5 J.
    apply lookupAL_middle_inv in J.
    destruct J as [l3 [l4 J]].
    rewrite J in *. 
    symmetry in J.
    rewrite_env ((l3 ++ [(id0, lt5)]) ++ l4).
    eapply noncycled__getTypeSizeInBits_and_Alignment_for_namedts 
      with (nts1:=l3)(nts2:=l4) in H; eauto.
    unfold getTypeSizeInBits_and_Alignment.
    destruct H as [sz0 [al0 [W1 ?]]].
    exists sz0. exists al0.
    eapply getTypeSizeInBits_and_Alignment_aux_weakening; eauto.
      simpl_env. simpl. auto.
Qed.

Lemma gundef__total : forall S TD t (H0 : wf_typ S TD t),
  exists gv, gundef TD t = Some gv.
Proof.
  intros.
  unfold gundef.
  eapply flatten_typ_total in H0; eauto.
  destruct H0 as [? H0].
  fill_ctxhole. eauto.
Qed.

(*
Lemma make_list_const_spec1' : forall
  (const_list : list_const)
  (system5 : system)
  (td5 : targetdata)
  (typ5 : typ)
  (sz5 : sz)
  (lsdc : list (system * targetdata * const))
  (lt : list typ)
  (HeqR : (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const
                    (fun const_ : const => (system5, td5, const_, typ5))
                    const_list))))
  (TD : TargetData)
  (H0 : wf_typ system5 td5 (typ_array sz5 typ5)),
  wf_typ system5 td5 (typ_struct (make_list_typ lt)).
Proof.
  intros.
  generalize dependent lsdc.
  generalize dependent lt.
  induction const_list; intros; simpl in *.
     inv HeqR. simpl. auto.
  
     remember (split
              (unmake_list_system_targetdata_const_typ
                 (make_list_system_targetdata_const_typ
                    (map_list_const
                       (fun const_ : const => (system5, td5, const_, typ5))
                       const_list)))) as R2.
     destruct R2. inv HeqR. simpl.
     split; eauto.
Qed.

Lemma typ_eq_list_typ_spec1': forall (nts:namedts) t1 lt2 (Huniq: uniq nts)
  (H: typ_eq_list_typ nts t1 lt2 = true),
  Constant.wf_zeroconst_typ t1 ->
  Constant.wf_zeroconsts_typ lt2.
Proof.
  intros.
  unfold typ_eq_list_typ in H.
  destruct t1; tinv H.
    destruct (list_typ_dec l0 lt2); inv H. auto.

    remember (lookupAL list_typ (rev nts) i0) as R.
    destruct R; tinv H.
    destruct (list_typ_dec l0 lt2); inv H.
    simpl in *. uniq_result.
Qed.
*)


Ltac elim_wrong_wf_typ:=
repeat match goal with
| H: wf_typ _ _ (typ_floatpoint fp_fp128) |- _ => inv H
| H: wf_styp _ _ (typ_floatpoint fp_fp128) |- _ => inv H
| H: wf_typ _ _ (typ_floatpoint fp_x86_fp80) |- _ => inv H
| H: wf_styp _ _ (typ_floatpoint fp_x86_fp80) |- _ => inv H
| H: wf_typ _ _ (typ_floatpoint fp_ppc_fp128) |- _ => inv H
| H: wf_styp _ _ (typ_floatpoint fp_ppc_fp128) |- _ => inv H
| e: floating_point_order ?floating_point2 fp_float = true |- _ =>
     destruct floating_point2; inv e
end.

Lemma wf_const__wf_typ: forall S TD c ty,
  wf_const S TD c ty -> wf_typ S TD ty.
Proof. intros. inv H; auto. Qed.

Definition const2GV_isnt_stuck_Prop S TD c t :=
  wf_const S TD c t ->
  forall gl (Hty: uniq (snd TD)),
  wf_global TD S gl ->
  exists gv, _const2GV TD gl c = Some (gv, t).

Definition consts2GV_isnt_stuck_Prop sdct :=
  wf_const_list sdct ->
  let 'lsdct := unmake_list_system_targetdata_const_typ sdct in
  let '(lsdc, lt) := split lsdct in
  let '(lsd, lc) := split lsdc in
  let '(ls, ld) := split lsd in
  forall S TD gl (Hty: uniq (snd TD)), 
  wf_list_targetdata_typ S TD gl lsd ->
  (forall t, (forall t0, In t0 lt -> t0 = t) ->
    exists gv, _list_const_arr2GV TD gl t (make_list_const lc) = Some gv) /\
  (exists gv, _list_const_struct2GV TD gl (make_list_const lc) = 
    Some (gv, (make_list_typ lt))).

Lemma const2GV_isnt_stuck_mutind : 
  (forall S td c t, @const2GV_isnt_stuck_Prop S td c t) /\
  (forall sdct, @consts2GV_isnt_stuck_Prop sdct).
Proof.
  (wfconst_cases (apply wf_const_mutind (*with
    (P  := const2GV_isnt_stuck_Prop)
    (P0 := consts2GV_isnt_stuck_Prop)*)) Case);
    unfold const2GV_isnt_stuck_Prop, consts2GV_isnt_stuck_Prop;
    intros; subst; simpl; eauto.
Case "wfconst_zero".
  destruct (@wf_zeroconst2GV_total system5 targetdata5 typ5) as [gv J]; auto.
  fill_ctxhole. eauto.
Case "wfconst_floatingpoint". 
  inv H. inv H2; eauto.
Case "wfconst_undef".
  match goal with
  | H: wf_typ _ _ _ |- _ =>
    eapply gundef__total in H; eauto;
    destruct H as [gv H];
    rewrite H; eauto
  end.
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
  destruct (@H0 system5 targetdata5 gl) as [J1 [gv2 J2]]; 
    try solve [destruct targetdata5; eauto using const2GV_typsize_mutind_array].
    assert (make_list_const lc = const_list) as EQ.
      eapply make_list_const_spec2; eauto.
    rewrite H1. rewrite <- EQ. unfold Size.to_nat in *. 
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
  erewrite <- map_list_const_typ_spec1 in H2; eauto.
  destruct (@H0 system5 (layouts5, namedts5) gl) as [_ [gv2 J2]];
    try solve [eauto using const2GV_typsize_mutind_struct |
               eapply typ_eq_list_typ_spec1; eauto |
               eapply typ_eq_list_typ_spec1'; eauto].
    erewrite <- map_list_const_typ_spec2; eauto.
    repeat fill_ctxhole.
    destruct gv2; eauto.

Case "wfconst_gid".
  match goal with
  | H: wf_global _ _ _ , e: lookupTypViaGIDFromSystem _ _ = _ |- _ =>
    apply H in e;  
    destruct e as [gv [sz [e [J1 J2]]]];
    rewrite e; eauto
  end.
Case "wfconst_trunc_int".
  match goal with
  | H4: wf_global _ _ _ |- _ => 
    eapply H0 in H4; eauto; destruct H4 as [gv H4]; fill_ctxhole
  end.
  unfold mtrunc.
  assert (exists gv, gundef targetdata5 (typ_int sz2) = Some gv) as J.
    eapply gundef__total; eauto.
  fill_ctxhole.
  destruct (GV2val targetdata5 gv) as [[]|]; eauto.
Case "wfconst_trunc_fp".
  match goal with
  | H4: wf_global _ _ _ |- _ => 
    eapply H0 in H4; eauto; destruct H4 as [gv H4]; fill_ctxhole
  end.
  unfold mtrunc. rewrite H1.
  assert (exists gv, gundef targetdata5 (typ_floatpoint floating_point2) = 
           Some gv) as J.
    eapply gundef__total; eauto.
  fill_ctxhole.
  destruct (GV2val targetdata5 gv) as [[]|]; eauto.
  destruct floating_point1; try solve [eauto | elim_wrong_wf_typ].
Case "wfconst_zext".
  match goal with
  | H4: wf_global _ _ _ |- _ => 
    eapply H0 in H4; eauto; destruct H4 as [gv H4]; fill_ctxhole
  end.
  unfold mext.
  assert (exists gv, gundef targetdata5 (typ_int sz2) = Some gv) as J.
    eapply gundef__total; eauto.
  fill_ctxhole.
  destruct (GV2val targetdata5 gv) as [[]|]; eauto.
Case "wfconst_sext".
  match goal with
  | H4: wf_global _ _ _ |- _ => 
    eapply H0 in H4; eauto; destruct H4 as [gv H4]; fill_ctxhole
  end.
  unfold mext.
  assert (exists gv, gundef targetdata5 (typ_int sz2) = Some gv) as J.
    eapply gundef__total; eauto.
  fill_ctxhole.
  destruct (GV2val targetdata5 gv) as [[]|]; eauto.
Case "wfconst_fpext".
  match goal with
  | H4: wf_global _ _ _ |- _ => 
    eapply H0 in H4; eauto; destruct H4 as [gv H4]; fill_ctxhole
  end.
  unfold mext.
  assert (exists gv, gundef targetdata5 (typ_floatpoint floating_point2) = 
    Some gv) as J.
    eapply gundef__total; eauto.
  fill_ctxhole.
  destruct (GV2val targetdata5 gv) as [[]|]; try fill_ctxhole; eauto.
  destruct floating_point2; try solve [eauto | elim_wrong_wf_typ].
Case "wfconst_ptrtoint".
  match goal with
  | H4: wf_global _ _ _ |- _ => 
    eapply H0 in H4; eauto; destruct H4 as [gv H4]; fill_ctxhole
  end.
  assert (exists gv, gundef targetdata5 (typ_int sz5) = Some gv) as J.
    eapply gundef__total; eauto.
  fill_ctxhole. eauto.
Case "wfconst_inttoptr".
  match goal with
  | H4: wf_global _ _ _ |- _ => 
    eapply H0 in H4; eauto; destruct H4 as [gv H4]; fill_ctxhole
  end.
  assert (exists gv, gundef targetdata5 (typ_pointer typ5) = Some gv) as J.
    eapply gundef__total; eauto.
  fill_ctxhole. eauto.
Case "wfconst_bitcast".
  unfold mbitcast.
  match goal with
  | H4: wf_global _ _ _ |- _ => 
    eapply H0 in H4; eauto; destruct H4 as [gv H4]; fill_ctxhole
  end. eauto.
Case "wfconst_gep".
  (*clear H0.*)
  eapply H0 in H7; eauto; simpl; auto.
  destruct H7 as [gv H7]. repeat fill_ctxhole.
  assert (exists gv, gundef targetdata5 typ' = Some gv) as J.
    eapply gundef__total; eauto.
  fill_ctxhole. 
  destruct (GV2ptr targetdata5 (getPointerSize targetdata5) gv); eauto.
  destruct (intConsts2Nats targetdata5 const_list); eauto.
  destruct (mgep targetdata5 typ5 v l0); eauto.

Case "wfconst_select".
  assert (J:=H8).
  eapply H0 in J; eauto; simpl; auto.
  destruct J as [gv J].
  assert (J':=H8).
  eapply H5 in J'; eauto; simpl; auto.
  destruct J' as [gv' J'].
  eapply H3 in H8; eauto; simpl; auto.
  destruct H8 as [gv'' H8].
  rewrite J. rewrite J'. rewrite H8.
  destruct (isGVZero targetdata5 gv); eauto.
Case "wfconst_icmp".
  assert (J:=H7).
  eapply H0 in H7; eauto.
  destruct H7 as [gv H7].
  rewrite H7. 
  eapply H2 in J; eauto.
  destruct J as [gv' J].
  rewrite J. 
  unfold micmp.
  unfold isPointerTyp in H4. unfold is_true in H4.
  unfold micmp_int.
  assert (exists gv, gundef targetdata5 (typ_int 1%nat) = 
           Some gv) as JJ.
    eapply gundef__total; eauto.
  destruct JJ as [gv0 JJ].
  rewrite JJ.
  destruct H4 as [o | o].
    destruct typ5; try solve [simpl in o; contradict o; auto].
    destruct (GV2val targetdata5 gv); eauto.
    destruct v; eauto.
    destruct (GV2val targetdata5 gv'); eauto.
    destruct v; eauto.
    destruct cond5; eauto.

    destruct typ5; try solve [eauto | simpl in o; contradict o; auto].
Case "wfconst_fcmp".
  assert (J:=H7).
  eapply H1 in H7; eauto.
  destruct H7 as [gv H7].
  rewrite H7. 
  eapply H3 in J; eauto.
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
  destruct floating_point5; try solve [eauto | elim_wrong_wf_typ].
    destruct fcond5; try solve [eauto | inversion H].
    destruct fcond5; try solve [eauto | inversion H].
Case "wfconst_extractvalue".
  eapply H0 in H8; eauto.
  destruct H8 as [gv H8].
  rewrite H8.
  destruct H6 as [idxs [o [J1 J2]]].
  erewrite mgetoffset__getSubTypFromConstIdxs; eauto.
  unfold LLVMgv.extractGenericValue.
  rewrite J1. rewrite J2.
  destruct (mget targetdata5 gv o typ'); eauto.
    eapply gundef__total in H7; eauto.
  fill_ctxhole. eauto.
Case "wfconst_insertvalue".
  assert (J:=H10).
  eapply H0 in H10; eauto.
  destruct H10 as [gv H10].
  rewrite H10.
  eapply H2 in J; eauto.
  destruct J as [gv' J].
  rewrite J.
  unfold LLVMgv.insertGenericValue.
  destruct H8 as [idxs [o [J1 J2]]].
  rewrite J1. rewrite J2.
  destruct (mset targetdata5 gv o typ' gv'); eauto.
    eapply gundef__total in H9; eauto.
    destruct H9 as [gv0 JJ]. rewrite JJ. eauto.
Case "wfconst_bop".
  assert (exists gv, gundef targetdata5 (typ_int sz5) = Some gv) as JJ.
    eapply gundef__total; eauto.
  destruct JJ as [gv0 JJ].
  assert (J:=H4).
  eapply H0 in H4; eauto.
  destruct H4 as [gv H4].
  rewrite H4.
  eapply H2 in J; eauto.
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
  assert (J:=H4).
  eapply H0 in H4; eauto.
  destruct H4 as [gv H4].
  rewrite H4.
  eapply H2 in J; eauto.
  destruct J as [gv' J].
  rewrite J.
  unfold mfbop. rewrite JJ.
  destruct (GV2val targetdata5 gv); eauto.
  destruct (GV2val targetdata5 gv'); eauto.
  destruct v; eauto.
  destruct v0; eauto.
  destruct floating_point5; try solve [eauto | elim_wrong_wf_typ].
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
  intros S TD gl Huniq Hwfl.
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
  assert (J2':=Hwfg).
  eapply H0 in J2'; eauto.
  destruct J2' as [gv J2'].
  rewrite J2'.
  assert (J1':=Hwfl').
  eapply H2 in J1'; eauto.
  destruct J1' as [J1' [g2 J12]].
  rewrite J12.
  apply wf_const__wf_typ in H.
  apply wf_typ__feasible_typ in H.
  apply feasible_typ_inv'' in H.  
  destruct H as [ssz [asz [J21 J22]]].
  rewrite J22.
  split; eauto.  
    intros.
    destruct (@J1' t) as [gv0 H4]; eauto.
    rewrite H4.
    assert (typ5 = t) as EQ. apply H; auto.
    subst.
    destruct (typ_dec t t); eauto.
      contradict n; auto.
Qed.

Lemma mbop_is_total : forall S TD bop0 sz0, 
  wf_typ S TD (typ_int sz0) ->
  forall x y, exists z, mbop TD bop0 sz0 x y = Some z.
Proof.
  intros S TD bop0 sz0 Hwft x y.
  unfold mbop.
  destruct (GV2val TD x); eauto using gundef__total.
  destruct v; eauto using gundef__total.
  destruct (GV2val TD y); eauto using gundef__total.
  destruct v; eauto using gundef__total.
  destruct (eq_nat_dec (wz + 1) (Size.to_nat sz0)); 
    eauto using gundef__total.
  destruct bop0; eauto using gundef__total.
Qed.

Lemma mfbop_is_total : forall S TD fbop0 fp, 
  wf_typ S TD (typ_floatpoint fp) ->
  forall x y, exists z, mfbop TD fbop0 fp x y = Some z.
Proof.
  intros.
  unfold mfbop.
  destruct (GV2val TD x); eauto using gundef__total.
  destruct v; eauto using gundef__total.
  destruct (GV2val TD y); eauto using gundef__total.
  destruct v; eauto using gundef__total.
  destruct fp; try solve [eauto | elim_wrong_wf_typ].
Qed.

Lemma micmp_is_total : forall S TD c t
  (Hztyp: wf_typ S TD t), 
  Typ.isIntOrIntVector t \/ isPointerTyp t ->
  forall x y, exists z, micmp TD c t x y = Some z.
Proof.
  intros S TD c t Hty Hwft x y.
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
  wf_typ S TD (typ_floatpoint fp) ->
  forall x y, exists z, mfcmp TD c fp x y = Some z.
Proof.
  intros S TD c fp Hc Ht x y.
  unfold mfcmp.
  destruct (GV2val TD x); eauto using gundef_i1__total.
  destruct v; eauto using gundef_i1__total.
  destruct (GV2val TD y); eauto using gundef_i1__total.
  destruct v; eauto using gundef_i1__total.
  destruct fp; try solve [eauto | elim_wrong_wf_typ].
    destruct c; try solve [eauto | inversion Hc].
    destruct c; try solve [eauto | inversion Hc].
Qed.

Lemma GEP_is_total : forall S TD t mp vidxs inbounds0 t',
  wf_typ S TD (typ_pointer t') ->
  exists mp', LLVMgv.GEP TD t mp vidxs inbounds0 t' = ret mp'.
Proof.
  intros. unfold LLVMgv.GEP.
  destruct (GV2ptr TD (getPointerSize TD) mp); eauto using gundef__total.
  destruct (GVs2Nats TD vidxs); eauto using gundef__total.
  destruct (mgep TD t v l0); eauto using gundef__total.
Qed.

Lemma fit_gv__total : forall S TD t gv1 (H0 : wf_typ S TD t),
  exists gv, fit_gv TD t gv1 = Some gv.
Proof.
  intros. 
  unfold fit_gv.
  assert (exists gv, gundef TD t = Some gv) as EQ.
    eapply gundef__total; eauto.
  destruct EQ as [gv EQ].
  rewrite EQ. apply wf_typ__feasible_typ in H0.
  eapply feasible_typ_inv' in H0; eauto.
  destruct H0 as [sz [al [J1 J2]]].
  unfold getTypeSizeInBits.
  rewrite J1. 
  match goal with
  | |- exists _:_, (if ?e then _ else _) = _ =>
       destruct e; eauto
  end.
Qed.

Lemma mcast_is_total : forall s f b los nts ps id5 cop0 t1 t2 v,
  wf_cast s (module_intro los nts ps) f b 
    (insn_cmd (insn_cast id5 cop0 t1 v t2)) ->
  forall x, exists z, mcast (los,nts) cop0 t1 t2 x = Some z.
Proof.
  intros.
  unfold mcast, mbitcast.
  inv H; eauto using gundef__total.
Qed.

Lemma mtrunc_is_total : forall s f b los nts ps id5 top0 t1 t2 v, 
  wf_trunc s (module_intro los nts ps) f b 
    (insn_cmd (insn_trunc id5 top0 t1 v t2)) ->
  forall x, exists z, mtrunc (los,nts) top0 t1 t2 x = Some z.
Proof.
  intros.
  assert (J:=H).
  apply wf_trunc__wf_typ in J.
  destruct J as [J1 J2]. 
  unfold mtrunc.
  destruct (GV2val (los, nts) x); eauto using gundef__total.
  inv H; try solve [destruct v0; eauto using gundef__total].
    match goal with
    | H15: _ = _ |- _ => rewrite H15
    end.
    destruct v0; eauto using gundef__total.
      destruct floating_point1; try solve [eauto | elim_wrong_wf_typ].
Qed.

Lemma mext_is_total : forall s f b los nts ps id5 eop0 t1 t2 v, 
  wf_ext s (module_intro los nts ps) f b 
    (insn_cmd (insn_ext id5 eop0 t1 v t2)) ->
  forall x,  exists z, mext (los,nts) eop0 t1 t2 x = Some z.
Proof.
  intros.
  unfold mext.
  inv H; try solve 
    [destruct (GV2val (los, nts) x) as [[]|]; eauto using gundef__total].
    match goal with
    | H14: _ = _ |- _ => rewrite H14
    end.
    destruct (GV2val (los, nts) x) as [[]|]; eauto using gundef__total.
    destruct floating_point2; try solve [eauto | elim_wrong_wf_typ].
Qed.

Lemma mset'_is_total : forall S (TD : TargetData) ofs (t1 t2 : typ) 
  (w1 : wf_typ S TD t1),
  forall x y, exists z : GenericValue, mset' TD ofs t1 t2 x y = ret z.
Proof.
  intros.
  unfold mset'. unfold mset.
  destruct (getTypeStoreSize TD t2); simpl; eauto using gundef__total.
  destruct (n =n= length y); eauto using gundef__total.
  destruct (splitGenericValue x ofs); eauto using gundef__total.
  destruct p.  
  destruct (splitGenericValue g0 (Z_of_nat n)); eauto using gundef__total.
  destruct p. eauto.
  destruct (gv_chunks_match_typb TD g1 t2); eauto using gundef__total.
Qed.

Lemma mget'_is_total : forall S TD ofs t' 
  (w1 : wf_typ S TD t'),
  forall x, exists z, mget' TD ofs t' x = Some z.
Proof.
  intros.
  unfold mget'. unfold mget.
  destruct (getTypeStoreSize TD t'); simpl; eauto using gundef__total.
  destruct (splitGenericValue x ofs); eauto using gundef__total.
  destruct p.  
  destruct (splitGenericValue g0 (Z_of_nat n)); eauto using gundef__total.
  destruct p. eauto.
  destruct (gv_chunks_match_typb TD g1 t'); eauto using gundef__total.
Qed.

(********************************************)
(** * type size *)

Lemma int_typsize' : forall td s
  (H0 : feasible_typ td (typ_int s)),
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat s) 8) =
    (size_chunk_nat (AST.Mint (s - 1)) + 0)%nat.
Proof.
  intros.
  unfold size_chunk_nat, size_chunk, bytesize_chunk.
  assert (s > 0)%nat as WF.
    destruct td. inv H0. auto.
  assert (S (s - 1) = s) as EQ. omega.
  rewrite EQ. auto.
Qed.

Definition zeroconst2GV_aux__getTypeSizeInBits_prop S TD t
  :=
  wf_styp S TD t ->
  forall los nts gv nts' (Hty: feasible_typ (los, nts') t) (Huniq:uniq nts')
  (Heq: TD = (los, nts)) acc (Hsub: exists nts0, nts'=nts0++nts)
  (Hnc: forall id5 gv5 lt5 sz al, 
          lookupAL _ acc id5 = Some (Some gv5) ->
          lookupAL _ nts id5 = Some lt5 ->
          _getTypeSizeInBits_and_Alignment los 
            (getTypeSizeInBits_and_Alignment_for_namedts (los,nts') true) true
            (typ_struct lt5) = Some (sz, al) ->
          Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv5)
  (Hz: zeroconst2GV_aux (los,nts') acc t = Some gv) sz al
  (Hsize: _getTypeSizeInBits_and_Alignment los 
     (getTypeSizeInBits_and_Alignment_for_namedts (los,nts') true) true t
     = Some (sz, al)),
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.

Definition zeroconsts2GV_aux__getListTypeSizeInBits_prop sdt :=
  wf_styp_list sdt ->
  let 'lsdt := unmake_list_system_targetdata_typ sdt in
  let '(lsd, lt) := split lsdt in
  forall S TD acc los nts' (Hty: feasible_typs (los, nts') (make_list_typ lt))
  nts (Heq: TD = (los, nts)) gv (Hsub: exists nts0, nts'=nts0++nts)
  (Hz: zeroconsts2GV_aux (los,nts') acc (make_list_typ lt) = Some gv)
  (Huniq:uniq nts')
  (Hnc: forall id5 gv5 lt5 sz al, 
          lookupAL _ acc id5 = Some (Some gv5) ->
          lookupAL _ nts id5 = Some lt5 ->
          _getTypeSizeInBits_and_Alignment los 
            (getTypeSizeInBits_and_Alignment_for_namedts (los, nts') true) true
            (typ_struct lt5) = Some (sz, al) ->
          Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv5)
  (Heq': eq_system_targetdata S TD lsd) sz al
  (Hsize: _getListTypeSizeInBits_and_Alignment los 
     (getTypeSizeInBits_and_Alignment_for_namedts (los, nts') true) 
       (make_list_typ lt) = Some (sz, al)),
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.

Lemma zeroconst2GV_aux_typsize_mutrec :
  (forall S T t, zeroconst2GV_aux__getTypeSizeInBits_prop S T t) /\
  (forall sdt, zeroconsts2GV_aux__getListTypeSizeInBits_prop sdt).
Proof.
Local Opaque feasible_typ feasible_typs.
  (wfstyp_cases (apply wf_styp_mutind; 
                 unfold zeroconst2GV_aux__getTypeSizeInBits_prop, 
                        zeroconsts2GV_aux__getListTypeSizeInBits_prop) Case);
    intros; subst; simpl in *; uniq_result; eauto.
Case "wf_styp_int".
  simpl. eapply int_typsize'; eauto.

Case "wf_styp_structure".
  remember (split
              (unmake_list_system_targetdata_typ
                (make_list_system_targetdata_typ
                   (map_list_typ
                      (fun typ_ : typ => (system5, (los, nts):targetdata, typ_))
                      typ_list)))) as R.
  destruct R as [lsd lt].
  assert (make_list_typ lt = typ_list) as EQ1. 
    eapply make_list_typ_spec2; eauto.
  subst.
  assert (eq_system_targetdata system5 (los, nts) lsd) as EQ2.
    eapply wf_styp__feasible_typ_aux_mutrec_struct; eauto.
  subst.
  inv_mbind. symmetry_ctx.
  eapply H1 in HeqR0; eauto using list_system_typ_spec, feasible_struct_typ_inv.
  destruct n; inv H3.
      destruct g as [|[]]; inv H4; auto.
        simpl in HeqR0.
        assert (J3 := size_chunk_nat_pos' m).
        contradict HeqR0; omega.

      destruct g as [|[]]; inv H4; auto.
        assert (Coqlib.ZRdiv (Z_of_nat (S n)) 8 > 0) as J.
          apply Coqlib.ZRdiv_prop3; try solve [omega | apply Coqlib.Z_of_S_gt_O].
        apply Coqlib.nat_of_Z_pos in J.
        contradict HeqR0. simpl in *. omega.

Case "wf_styp_array".
  destruct sz5 as [|sz5]; uniq_result; auto.
  remember (zeroconst2GV_aux (los, nts') acc typ5) as R1.
  destruct R1; try solve [inv Hz].
  remember (getTypeAllocSize (los, nts') typ5) as R2.
  destruct R2 as [s1|]; inv Hz.
  assert (
    (g ++ uninits (Size.to_nat s1 - sizeGenericValue g)) ++
          repeatGV (g ++ uninits (Size.to_nat s1 - sizeGenericValue g)) sz5 = 
    repeatGV (g ++ uninits (Size.to_nat s1 - sizeGenericValue g)) (S sz5)) as G.
    simpl. auto.
  rewrite G. clear G.
  symmetry in HeqR1.
  inv_mbind.
  unfold getTypeAllocSize, getTypeStoreSize, getTypeSizeInBits, 
    getABITypeAlignment, getAlignment, getTypeSizeInBits_and_Alignment,
    getTypeSizeInBits_and_Alignment_for_namedts in HeqR2.
  rewrite <- HeqR in HeqR2. uniq_result. 
  eapply H0 in HeqR1; eauto using feasible_array_typ_inv.
  repeat rewrite HeqR1.
  rewrite sizeGenericValue__repeatGV.
  rewrite sizeGenericValue__app.
  rewrite sizeGenericValue__uninits. unfold Size.to_nat.
  assert (RoundUpAlignment (sizeGenericValue g) al >= (sizeGenericValue g))%nat 
    as J3.
    apply RoundUpAlignment_spec.
      apply feasible_array_typ_inv in Hty.
      eapply feasible_typ_inv' in Hty; eauto.
      destruct Hty as [sz0 [al0 [J3 J4]]].
      unfold getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts in J3.
      rewrite J3 in HeqR. uniq_result. auto.
  assert ((sizeGenericValue g +
     (RoundUpAlignment (sizeGenericValue g) al - sizeGenericValue g))%nat = 
     (RoundUpAlignment (sizeGenericValue g) al)) as J4.
    rewrite <- le_plus_minus; auto.
  rewrite J4.
  rewrite ZRdiv_prop8.
  ring.

Case "wf_styp_namedt".
  inv_mbind. 
  remember (lookupAL list_typ nts id5) as R.
  destruct R as [lt|]; try congruence. symmetry_ctx.
  assert (G:=HeqR0).
  apply lookupAL_middle_inv in HeqR0.
  destruct HeqR0 as [l1 [l2 HeqR0]].
  destruct Hsub as [nts0 Hsub]; subst.
  apply feasible_typ_inv in Hty.
  destruct Hty as [sz5 [al5 [J1 ?]]].
  simpl in J1. simpl_env in Huniq.
  eapply getTypeSizeInBits_and_Alignment_for_namedts_spec1 in J1; eauto.
  rewrite_env ((nts0 ++ l1) ++ (id5, lt) :: l2) in Hsize.
  eapply getTypeSizeInBits_and_Alignment_for_namedts_spec1 
    with (nts1:=nts0++l1)(nts2:=l2) in Hsize; simpl_env; eauto.
  uniq_result.
  apply getTypeSizeInBits_and_Alignment_aux_weakening 
    with (nm2:=nts0 ++ l1 ++ [(id5, lt)]) in J1; simpl_env; auto.
  simpl_env in J1. simpl in J1.
  eapply Hnc in J1; eauto.
     
Case "wf_styp_nil".
  intros. uniq_result. simpl. auto.

Case "wf_styp_cons".
  remember (split (unmake_list_system_targetdata_typ l')) as R.
  destruct R as [lsd lt]. simpl.
  intros. subst.
  apply eq_system_targetdata_cons_inv in Heq'. 
  destruct Heq' as [H4 [EQ1 EQ2]]; subst.
  remember (zeroconsts2GV_aux (los, nts') acc (make_list_typ lt)) as R1.
  destruct R1; tinv Hz.
  remember (zeroconst2GV_aux (los, nts') acc typ_) as R2.
  destruct R2; tinv Hz.
  remember (getTypeAllocSize (los, nts') typ_) as R3.
  destruct R3; inv Hz. 
  symmetry in HeqR1. symmetry in HeqR2.
  apply feasible_cons_typs_inv in Hty.
  destruct Hty as [Hty1 Hty2]. 
  inv_mbind. uniq_result.
  eapply_clear H0 in HeqR2; eauto. 
  eapply_clear H2 in HeqR1; eauto.
  rewrite sizeGenericValue__app.
  rewrite sizeGenericValue__app.
  rewrite sizeGenericValue__uninits. 
  rewrite plus_assoc. symmetry_ctx.
  rewrite <- HeqR1. repeat rewrite <- HeqR2.
  rewrite ZRdiv_prop9.
  rewrite plus_comm with (m:=nat_of_Z (ZRdiv (Z_of_nat n) 8)).
  erewrite getTypeAllocSize_roundup; eauto.
  eapply getTypeAllocSize_inv' in HeqR3; eauto. 
Transparent feasible_typ feasible_typs.
Qed.

Lemma zeroconst2GV_for_namedts_cons : forall TD los nm1 nm2,
  exists re,
    zeroconst2GV_for_namedts TD los (nm2++nm1) =
      re ++ zeroconst2GV_for_namedts TD los nm1.
Proof.
  induction nm2 as [|[]]; simpl.
    exists nil. auto.

    destruct IHnm2 as [re IHnm2].
    rewrite IHnm2.
    match goal with 
    | |- context [
           match ?x with
           | Some _ => _
           | None => _
           end] => destruct x; simpl_env; eauto
    end.
Qed.

Definition zeroconst2GV_aux_weaken_prop (t:typ) := forall TD nm1 nm2 r,
  uniq (nm2++nm1) ->
  zeroconst2GV_aux TD nm1 t = Some r ->
  zeroconst2GV_aux TD (nm2++nm1) t = Some r.

Definition zeroconsts2GV_aux_weaken_prop (lt:list_typ) := 
  forall TD nm1 nm2 r,
  uniq (nm2++nm1) ->
  zeroconsts2GV_aux TD nm1 lt = Some r ->
  zeroconsts2GV_aux TD (nm2++nm1) lt = Some r.

Lemma zeroconst2GV_aux_weaken_mutrec :
  (forall t, zeroconst2GV_aux_weaken_prop t) *
  (forall lt, zeroconsts2GV_aux_weaken_prop lt).
Proof.
  (typ_cases (apply typ_mutrec; 
    unfold zeroconst2GV_aux_weaken_prop, 
           zeroconsts2GV_aux_weaken_prop) Case);
    intros; simpl in *; try solve [eauto | inversion H | inversion H1 ].
Case "typ_array".
  match goal with
  | H : match ?s with
    | 0%nat => _
    | S _ => _
    end = _ |- _ => destruct s as [|s]; auto
  end.
  inv_mbind. erewrite H; eauto; simpl; auto.

Case "typ_struct".
  inv_mbind. erewrite H; eauto; simpl; auto.

Case "typ_namedt".
  inv_mbind. erewrite lookupAL_weaken; auto.
Case "typ_cons".
  inv_mbind.
  erewrite H0; eauto.
  erewrite H; eauto.
Qed.

Lemma zeroconst2GV_for_namedts_dom: forall TD acc nm,
  dom (zeroconst2GV_for_namedts TD acc nm) [=] dom nm.
Proof.
  induction nm as [|[]]; simpl; fsetdec.
Qed.

Lemma zeroconst2GV_for_namedts_uniq: forall TD acc nm
  (Huniq: uniq nm),
  uniq (zeroconst2GV_for_namedts TD acc nm).
Proof.
  induction 1; simpl; auto.
    simpl_env.
    constructor; auto.
      assert (J:=@zeroconst2GV_for_namedts_dom TD acc E).
      fsetdec.
Qed.

Lemma zeroconst2GV_aux_weakening: forall TD los t r 
  (nm1 nm2:namedts) (Huniq: uniq (nm2++nm1)),
  zeroconst2GV_aux TD
    (zeroconst2GV_for_namedts TD los nm1) t = Some r ->
  zeroconst2GV_aux TD
    (zeroconst2GV_for_namedts TD los (nm2++nm1)) t = Some r.
Proof.
  intros.  
  destruct (@zeroconst2GV_for_namedts_cons TD los nm1 nm2) as [re J].
  rewrite J. 
  eapply zeroconst2GV_aux_weaken_mutrec; eauto.
  unfold id in *.
  rewrite <- J. 
  eapply zeroconst2GV_for_namedts_uniq; eauto. 
Qed.

Lemma zeroconst2GV_for_namedts_spec1: forall TD los nts2 lt2
  i0 r nts1 nts (Huniq: uniq nts),
  lookupAL _ (zeroconst2GV_for_namedts TD los nts) i0 = Some (Some r) ->
  nts = nts1 ++ (i0,lt2) :: nts2 ->  
  zeroconst2GV_aux TD (zeroconst2GV_for_namedts TD los nts2) (typ_struct lt2) 
    = Some r.
Proof.
  induction nts1 as [|[]]; intros; subst; simpl in *.
    destruct (i0 == i0); try congruence; auto.

    inv Huniq.
    simpl_env in H4.
    destruct (i0 == a); subst.
      contradict H4; fsetdec.
      apply IHnts1 in H; auto.
Qed.

Lemma noncycled__zeroconst2GV_aux_typsize: forall S los nts
  (H: noncycled S los nts) (Huniq: uniq nts)
  id5 lt nts2 nts1 (EQ: nts = nts1 ++ (id5,lt) :: nts2) nts' (Huniq': uniq nts') 
  (Hsub: exists nts0, nts'=nts0++nts)
  (Hftp: forall id5 lt5, lookupAL _ nts id5 = Some lt5 ->
                         feasible_typ (los, nts') (typ_struct lt5)) gv
  (Hz: zeroconst2GV_aux (los, nts')
         (zeroconst2GV_for_namedts (los, nts') los nts2) (typ_struct lt) = 
           Some gv) sz al
  (Hsize: _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts') true) true 
         (typ_struct lt) =  Some (sz, al)),
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof.
Local Opaque feasible_typ feasible_typs 
  getTypeSizeInBits_and_Alignment_for_namedts _getTypeSizeInBits_and_Alignment.
  induction 1; simpl; intros; subst.
    symmetry in EQ.    
    apply app_eq_nil in EQ.
    destruct EQ as [_ EQ].
    congruence.

    inv Huniq.
    destruct nts1 as [|[]]; inv EQ.
      destruct zeroconst2GV_aux_typsize_mutrec as [J _].
      eapply J in H0; eauto.
      assert (feasible_typ (layouts5, nts') (typ_struct lt)) as Hty.
        apply Hftp with (id5:=id0).
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id0 id0); 
          try congruence.
      assert (exists nts0 : list namedt, nts' = nts0 ++ nts2) as G.
        destruct Hsub as [nts0 Hsub]; subst. 
        exists (nts0 ++ [(id0, lt)]). simpl_env. auto.
      eapply H0 in Hty; eauto.  
      intros id5 gv5 lt5 sz5 al5 H1 H2 H4.
      apply lookupAL_middle_inv in H2.
      destruct H2 as [l1 [l2 HeqR]].
      assert (J':=HeqR). subst.
      eapply IHnoncycled with (nts':=nts') (al:=al5) in J'; eauto.
        intros.
        apply Hftp with (id6:=id1).
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); 
          subst; auto.
          apply notin_lookupAL_None in H5. congruence.
       
        eapply zeroconst2GV_for_namedts_spec1 in H1; eauto.
            
      assert (nts1 ++ (id0, lt) :: nts2 = nts1 ++ (id0, lt) :: nts2) as EQ. auto.
      eapply IHnoncycled with (nts':=nts') in EQ; eauto.
        destruct Hsub as [nts0 Hsub]; subst. 
        exists (nts0 ++ [(i0, l0)]). simpl_env. auto.
 
        intros.
        apply Hftp with (id5:=id5)(lt5:=lt5).
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id5 i0); 
          subst; auto.
          apply notin_lookupAL_None in H5. congruence.
Transparent feasible_typ feasible_typs
  getTypeSizeInBits_and_Alignment_for_namedts _getTypeSizeInBits_and_Alignment.
Qed.

Lemma zeroconst2GV__getTypeSizeInBits : forall t s los nts gv
  (Hz: zeroconst2GV (los,nts) t = Some gv)
  (Ht: wf_typ s (los,nts) t),
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof. 
  intros. 
  assert (G:=Ht).
  apply wf_typ__feasible_typ in G; auto.
  assert (G':=G).
  apply feasible_typ_inv in G'.
  destruct G' as [sz [al [J1 [J2 J3]]]].
  unfold getTypeSizeInBits_and_Alignment in J1.
  exists sz. exists al.
  split; auto.
  unfold zeroconst2GV in *. inv Ht.
  destruct zeroconst2GV_aux_typsize_mutrec as [J' _].
  assert (exists nts0 : list namedt, nts = nts0 ++ nts) as G'.
    exists nil. auto.
  eapply J'; eauto.
  intros id5 gv5 lt5 sz0 al0 J4 J5 J6.
  apply lookupAL_middle_inv in J5.
  destruct J5 as [l1 [l2 HeqR]]. subst.
  eapply noncycled__zeroconst2GV_aux_typsize 
    with (nts':=l1 ++ (id5, lt5) :: l2) in H1; eauto.
    intros id0 lt0 H.
    apply lookupAL_middle_inv in H.
    destruct H as [l3 [l4 H]].
    rewrite H in *. 
    symmetry in H.
    rewrite_env ((l3 ++ [(id0, lt0)]) ++ l4).
    eapply noncycled__feasible_typ_aux with (nts1:=l3)(nts2:=l4) in H1; eauto.
    unfold feasible_typ.
    eapply feasible_typ_aux_weakening; eauto.
      simpl_env. simpl. auto.

    eapply zeroconst2GV_for_namedts_spec1 in J4; eauto.
Qed.

Definition flatten_typ_aux__getTypeSizeInBits_prop S TD (t:typ) :=
  wf_styp S TD t ->
  forall los nts mc acc nts' (Hft: flatten_typ_aux (los,nts') acc t = Some mc)
  (Huniq:uniq nts') (Hty: LLVMtd.feasible_typ (los,nts') t) 
  (Heq: TD = (los, nts)) (Hsub: exists nts0, nts'=nts0++nts)
  (Hnc: forall id5 gv5 lt5 sz al, 
          lookupAL _ acc id5 = Some (Some gv5) ->
          lookupAL _ nts id5 = Some lt5 ->
          _getTypeSizeInBits_and_Alignment los 
            (getTypeSizeInBits_and_Alignment_for_namedts (los,nts') true) true
            (typ_struct lt5) = Some (sz, al) ->
          Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeMC gv5)
  sz al
  (Hsize: _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts') true) true t = 
         Some (sz, al)),
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeMC mc.

Definition flatten_typs_aux__getListTypeSizeInBits_prop sdt :=
  wf_styp_list sdt ->
  let 'lsdt := unmake_list_system_targetdata_typ sdt in
  let '(lsd, lt) := split lsdt in
  forall S TD acc los nts' mc nts
  (Hty: flatten_typs_aux (los,nts') acc (make_list_typ lt) = Some mc)
  (Hft: LLVMtd.feasible_typs (los,nts') (make_list_typ lt))
  (Heq: TD = (los, nts)) (Hsub: exists nts0, nts'=nts0++nts)
  (Huniq:uniq nts')
  (Hnc: forall id5 gv5 lt5 sz al, 
          lookupAL _ acc id5 = Some (Some gv5) ->
          lookupAL _ nts id5 = Some lt5 ->
          _getTypeSizeInBits_and_Alignment los 
            (getTypeSizeInBits_and_Alignment_for_namedts (los, nts') true) true
            (typ_struct lt5) = Some (sz, al) ->
          Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeMC gv5)
  (Heq': eq_system_targetdata S TD lsd) sz al
  (Hsize: _getListTypeSizeInBits_and_Alignment los 
     (getTypeSizeInBits_and_Alignment_for_namedts (los, nts') true) 
       (make_list_typ lt) = Some (sz, al)),
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeMC mc.

Lemma flatten_typ_aux_typsize_mutrec :
  (forall S TD t, flatten_typ_aux__getTypeSizeInBits_prop S TD t) /\
  (forall sdt, flatten_typs_aux__getListTypeSizeInBits_prop sdt).
Proof.
Local Opaque feasible_typ feasible_typs.
  (wfstyp_cases (apply wf_styp_mutind; 
                 unfold flatten_typ_aux__getTypeSizeInBits_prop, 
                        flatten_typs_aux__getListTypeSizeInBits_prop) Case);
    intros; subst; simpl in *; uniq_result; eauto.

Case "wf_styp_int".
  simpl. eapply int_typsize'; eauto.

Case "wf_styp_structure".
  remember (split
              (unmake_list_system_targetdata_typ
                (make_list_system_targetdata_typ
                   (map_list_typ
                      (fun typ_ : typ => (system5, (los, nts):targetdata, typ_))
                      typ_list)))) as R.
  destruct R as [lsd lt].
  assert (make_list_typ lt = typ_list) as EQ1. 
    eapply make_list_typ_spec2; eauto.
  subst.
  assert (eq_system_targetdata system5 (los, nts) lsd) as EQ2.
    eapply wf_styp__feasible_typ_aux_mutrec_struct; eauto.
  subst.
  inv_mbind. symmetry_ctx.
  eapply_clear H1 in HeqR0; eauto using list_system_typ_spec, feasible_struct_typ_inv.
  destruct n as [|n]; inv H3.
    destruct l0; inv H4; auto.
      simpl in HeqR0.
      assert (J3 := size_chunk_nat_pos' m).
      contradict HeqR0; omega.

    destruct l0; inv H4; auto.
      assert (Coqlib.ZRdiv (Z_of_nat (S n)) 8 > 0) as J.
        apply Coqlib.ZRdiv_prop3; try solve [omega | apply Coqlib.Z_of_S_gt_O].
      apply Coqlib.nat_of_Z_pos in J.
      contradict HeqR0. simpl in *. omega.

Case "wf_styp_array".
  destruct sz5 as [|sz5]; uniq_result; auto. 
  remember (flatten_typ_aux (los, nts') acc typ5) as R1.
  destruct R1; try solve [inv Hft].
  remember (getTypeAllocSize (los, nts') typ5) as R2.
  destruct R2 as [s1|]; inv Hft.
  assert (
    (l0 ++ uninitMCs (Size.to_nat s1 - sizeMC l0)) ++
          repeatMC (l0 ++ uninitMCs (Size.to_nat s1 - sizeMC l0)) sz5 = 
    repeatMC (l0 ++ uninitMCs (Size.to_nat s1 - sizeMC l0)) (S sz5)) as G.
    simpl. auto.
  rewrite G. clear G.
  symmetry in HeqR1.
  inv_mbind.
  unfold getTypeAllocSize, getTypeStoreSize, getTypeSizeInBits, 
    getABITypeAlignment, getAlignment, getTypeSizeInBits_and_Alignment,
    getTypeSizeInBits_and_Alignment_for_namedts in HeqR2.
  rewrite <- HeqR in HeqR2. uniq_result. 
  eapply H0 in HeqR1; eauto using feasible_array_typ_inv.
  repeat rewrite HeqR1.
  rewrite sizeMC__repeatMC.
  rewrite sizeMC__app.
  rewrite sizeMC__uninitMCs. unfold Size.to_nat.
  assert (RoundUpAlignment (sizeMC l0) al >= (sizeMC l0))%nat 
    as J3.
    apply RoundUpAlignment_spec.
      apply feasible_array_typ_inv in Hty.
      eapply feasible_typ_inv' in Hty; eauto.
      destruct Hty as [sz0 [al0 [J3 J4]]].
      unfold getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts in J3.
      rewrite J3 in HeqR. uniq_result. auto.
  assert ((sizeMC l0 +
     (RoundUpAlignment (sizeMC l0) al - sizeMC l0))%nat = 
     (RoundUpAlignment (sizeMC l0) al)) as J4.
    rewrite <- le_plus_minus; auto.
  rewrite J4.
  rewrite ZRdiv_prop8.
  ring.

Case "wf_styp_namedt".
  inv_mbind. 
  remember (lookupAL list_typ nts id5) as R.
  destruct R as [lt|]; try congruence. symmetry_ctx.
  assert (G:=HeqR0).
  apply lookupAL_middle_inv in HeqR0.
  destruct HeqR0 as [l1 [l2 HeqR0]].
  destruct Hsub as [nts0 Hsub]; subst.
  apply feasible_typ_inv in Hty.
  destruct Hty as [sz5 [al5 [J1 ?]]].
  simpl in J1. simpl_env in Huniq.
  eapply getTypeSizeInBits_and_Alignment_for_namedts_spec1 in J1; eauto.
  rewrite_env ((nts0 ++ l1) ++ (id5, lt) :: l2) in Hsize.
  eapply getTypeSizeInBits_and_Alignment_for_namedts_spec1 
    with (nts1:=nts0++l1)(nts2:=l2) in Hsize; simpl_env; eauto.
  uniq_result.
  apply getTypeSizeInBits_and_Alignment_aux_weakening 
    with (nm2:=nts0 ++ l1 ++ [(id5, lt)]) in J1; simpl_env; auto.
  simpl_env in J1. simpl in J1.
  eapply Hnc in J1; eauto.
     
Case "wf_styp_nil".
  intros. uniq_result. simpl. auto.

Case "wf_styp_cons".
  remember (split (unmake_list_system_targetdata_typ l')) as R.
  destruct R as [lsd lt]. simpl.
  intros. subst.
  apply eq_system_targetdata_cons_inv in Heq'. 
  destruct Heq' as [H4 [EQ1 EQ2]]; subst.
  remember (flatten_typs_aux (los, nts') acc (make_list_typ lt)) as R1.
  destruct R1; tinv Hty.
  remember (flatten_typ_aux (los, nts') acc typ_) as R2.
  destruct R2; tinv Hty.
  remember (getTypeAllocSize (los, nts') typ_) as R3.
  destruct R3; inv Hty. 
  symmetry in HeqR1. symmetry in HeqR2.
  apply feasible_cons_typs_inv in Hft.
  destruct Hft as [Hft1 Hft2]. 
  inv_mbind. uniq_result.
  eapply_clear H0 in HeqR2; eauto. 
  eapply_clear H2 in HeqR1; eauto.
  rewrite sizeMC__app.
  rewrite sizeMC__app.
  rewrite sizeMC__uninitMCs. 
  rewrite plus_assoc. symmetry_ctx.
  rewrite <- HeqR1. repeat rewrite <- HeqR2.
  rewrite ZRdiv_prop9.
  rewrite plus_comm with (m:=nat_of_Z (ZRdiv (Z_of_nat n) 8)).
  erewrite getTypeAllocSize_roundup; eauto.
  eapply getTypeAllocSize_inv' in HeqR3; eauto. 
Transparent feasible_typ feasible_typs.
Qed.

Lemma flatten_typ_for_namedts_cons : forall TD los nm1 nm2,
  exists re,
    flatten_typ_for_namedts TD los (nm2++nm1) =
      re ++ flatten_typ_for_namedts TD los nm1.
Proof.
  induction nm2 as [|[]]; simpl.
    exists nil. auto.

    destruct IHnm2 as [re IHnm2].
    rewrite IHnm2.
    match goal with 
    | |- context [
           match ?x with
           | Some _ => _
           | None => _
           end] => destruct x; simpl_env; eauto
    end.
Qed.

Definition flatten_typ_aux_weaken_prop (t:typ) := forall TD nm1 nm2 r,
  uniq (nm2++nm1) ->
  flatten_typ_aux TD nm1 t = Some r ->
  flatten_typ_aux TD (nm2++nm1) t = Some r.

Definition flatten_typs_aux_weaken_prop (lt:list_typ) := 
  forall TD nm1 nm2 r,
  uniq (nm2++nm1) ->
  flatten_typs_aux TD nm1 lt = Some r ->
  flatten_typs_aux TD (nm2++nm1) lt = Some r.

Lemma flatten_typ_aux_weaken_mutrec :
  (forall t, flatten_typ_aux_weaken_prop t) *
  (forall lt, flatten_typs_aux_weaken_prop lt).
Proof.
  (typ_cases (apply typ_mutrec; 
    unfold flatten_typ_aux_weaken_prop, 
           flatten_typs_aux_weaken_prop) Case);
    intros; simpl in *; try solve [eauto | inversion H | inversion H1 ].
Case "typ_array".
  match goal with
  | H : match ?s with
    | 0%nat => _
    | S _ => _
    end = _ |- _ => destruct s as [|s]; auto
  end.
  inv_mbind. erewrite H; eauto; simpl; auto.

Case "typ_struct".
  inv_mbind. erewrite H; eauto; simpl; auto.

Case "typ_namedt".
  inv_mbind. erewrite lookupAL_weaken; auto.
Case "typ_cons".
  inv_mbind.
  erewrite H0; eauto.
  erewrite H; eauto.
Qed.

Lemma flatten_typ_for_namedts_dom: forall TD acc nm,
  dom (flatten_typ_for_namedts TD acc nm) [=] dom nm.
Proof.
  induction nm as [|[]]; simpl; fsetdec.
Qed.

Lemma flatten_typ_for_namedts_uniq: forall TD acc nm
  (Huniq: uniq nm),
  uniq (flatten_typ_for_namedts TD acc nm).
Proof.
  induction 1; simpl; auto.
    simpl_env.
    constructor; auto.
      assert (J:=@flatten_typ_for_namedts_dom TD acc E).
      fsetdec.
Qed.

Lemma flatten_typ_aux_weakening: forall TD los t r 
  (nm1 nm2:namedts) (Huniq: uniq (nm2++nm1)),
  flatten_typ_aux TD
    (flatten_typ_for_namedts TD los nm1) t = Some r ->
  flatten_typ_aux TD
    (flatten_typ_for_namedts TD los (nm2++nm1)) t = Some r.
Proof.
  intros.  
  destruct (@flatten_typ_for_namedts_cons TD los nm1 nm2) as [re J].
  rewrite J. 
  eapply flatten_typ_aux_weaken_mutrec; eauto.
  unfold id in *.
  rewrite <- J. 
  eapply flatten_typ_for_namedts_uniq; eauto. 
Qed.

Lemma flatten_typ_for_namedts_spec1: forall TD los nts2 lt2
  i0 r nts1 nts (Huniq: uniq nts),
  lookupAL _ (flatten_typ_for_namedts TD los nts) i0 = Some (Some r) ->
  nts = nts1 ++ (i0,lt2) :: nts2 ->  
  flatten_typ_aux TD (flatten_typ_for_namedts TD los nts2) (typ_struct lt2) 
    = Some r.
Proof.
  induction nts1 as [|[]]; intros; subst; simpl in *.
    destruct (i0 == i0); try congruence; auto.

    inv Huniq.
    simpl_env in H4.
    destruct (i0 == a); subst.
      contradict H4; fsetdec.
      apply IHnts1 in H; auto.
Qed.

Lemma noncycled__flatten_typ_aux_typsize: forall S los nts
  (H: noncycled S los nts) (Huniq: uniq nts)
  id5 lt nts2 nts1 (EQ: nts = nts1 ++ (id5,lt) :: nts2) nts' (Huniq': uniq nts') 
  (Hsub: exists nts0, nts'=nts0++nts)
  (Hftp: forall id5 lt5, lookupAL _ nts id5 = Some lt5 ->
                         feasible_typ (los, nts') (typ_struct lt5)) mc
  (Hz: flatten_typ_aux (los, nts')
         (flatten_typ_for_namedts (los, nts') los nts2) (typ_struct lt) = 
           Some mc) sz al
  (Hsize: _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts') true) true 
         (typ_struct lt) =  Some (sz, al)),
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeMC mc.
Proof.
Local Opaque feasible_typ feasible_typs 
  getTypeSizeInBits_and_Alignment_for_namedts _getTypeSizeInBits_and_Alignment.
  induction 1; simpl; intros; subst.
    symmetry in EQ.    
    apply app_eq_nil in EQ.
    destruct EQ as [_ EQ].
    congruence.

    inv Huniq.
    destruct nts1 as [|[]]; inv EQ.
      destruct flatten_typ_aux_typsize_mutrec as [J _].
      eapply J in H0; eauto.
      assert (feasible_typ (layouts5, nts') (typ_struct lt)) as Hty.
        apply Hftp with (id5:=id0).
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id0 id0); 
          try congruence.
      assert (exists nts0 : list namedt, nts' = nts0 ++ nts2) as G.
        destruct Hsub as [nts0 Hsub]; subst. 
        exists (nts0 ++ [(id0, lt)]). simpl_env. auto.
      eapply H0 in Hty; eauto.  
      intros id5 gv5 lt5 sz5 al5 H1 H2 H4.
      apply lookupAL_middle_inv in H2.
      destruct H2 as [l1 [l2 HeqR]].
      assert (J':=HeqR). subst.
      eapply IHnoncycled with (nts':=nts') (al:=al5) in J'; eauto.
        intros.
        apply Hftp with (id6:=id1).
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); 
          subst; auto.
          apply notin_lookupAL_None in H5. congruence.
       
        eapply flatten_typ_for_namedts_spec1 in H1; eauto.
            
      assert (nts1 ++ (id0, lt) :: nts2 = nts1 ++ (id0, lt) :: nts2) as EQ. auto.
      eapply IHnoncycled with (nts':=nts') in EQ; eauto.
        destruct Hsub as [nts0 Hsub]; subst. 
        exists (nts0 ++ [(i0, l0)]). simpl_env. auto.
 
        intros.
        apply Hftp with (id5:=id5)(lt5:=lt5).
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id5 i0); 
          subst; auto.
          apply notin_lookupAL_None in H5. congruence.
Transparent feasible_typ feasible_typs
  getTypeSizeInBits_and_Alignment_for_namedts _getTypeSizeInBits_and_Alignment.
Qed.

Lemma flatten_typ__getTypeSizeInBits : forall t s los nts mc
  (Hz: flatten_typ (los,nts) t = Some mc)
  (Ht: wf_typ s (los,nts) t),
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeMC mc.
Proof. 
  intros. 
  assert (G:=Ht).
  apply wf_typ__feasible_typ in G; auto.
  assert (G':=G).
  apply feasible_typ_inv in G'.
  destruct G' as [sz [al [J1 [J2 J3]]]].
  unfold getTypeSizeInBits_and_Alignment in J1.
  exists sz. exists al.
  split; auto.
  unfold flatten_typ in *. inv Ht.
  destruct flatten_typ_aux_typsize_mutrec as [J' _].
  assert (exists nts0 : list namedt, nts = nts0 ++ nts) as G'.
    exists nil. auto.
  eapply J'; eauto.
  intros id5 gv5 lt5 sz0 al0 J4 J5 J6.
  apply lookupAL_middle_inv in J5.
  destruct J5 as [l1 [l2 HeqR]]. subst.
  eapply noncycled__flatten_typ_aux_typsize 
    with (nts':=l1 ++ (id5, lt5) :: l2) in H1; eauto.
    intros id0 lt0 H.
    apply lookupAL_middle_inv in H.
    destruct H as [l3 [l4 H]].
    rewrite H in *. 
    symmetry in H.
    rewrite_env ((l3 ++ [(id0, lt0)]) ++ l4).
    eapply noncycled__feasible_typ_aux with (nts1:=l3)(nts2:=l4) in H1; eauto.
    unfold feasible_typ.
    eapply feasible_typ_aux_weakening; eauto.
      simpl_env. simpl. auto.

    eapply flatten_typ_for_namedts_spec1 in J4; eauto.
Qed.

Lemma gundef__getTypeSizeInBits : forall s los nts gv t' 
  (H1: wf_typ s (los, nts) t') (HeqR : ret gv = gundef (los, nts) t'),
   exists sz0 : nat,
     exists al : nat,
       _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los nts true)
         true t' = ret (sz0, al) /\
       Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz0) 8) = sizeGenericValue gv.
Proof.
  intros.
  unfold gundef in HeqR.
  assert (J:=H1).
  apply flatten_typ_total in H1; auto.
  destruct H1 as [mc H1].
  rewrite H1 in HeqR.
  uniq_result.
  rewrite sizeGenericValue_mc2undefs__sizeMC.
  eapply flatten_typ__getTypeSizeInBits; eauto.
Qed.

Lemma mtrunc_typsize : forall S los nts top t1 t2 gv1 gv2
  (H0: wf_typ S (los,nts) t2) (H1: mtrunc (los,nts) top t1 t2 gv1 = Some gv2),
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t2 = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv2.
Proof.  
  intros. 
  unfold mtrunc, GV2val in H1.
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
    remember (floating_point_order f1 f0) as R.
    destruct R; tinv H1.
    destruct f0; inv H1.
    destruct f1; inv HeqR.
      simpl. exists 32%nat. exists (getFloatAlignmentInfo los 32 true).
      auto.
Qed.

Lemma mext_typsize : forall S los nts eop t1 t2 gv1 gv2
  (H0: wf_typ S (los,nts) t2)
  (H1: mext (los,nts) eop t1 t2 gv1 = Some gv2),
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
    remember (floating_point_order f f0) as R.
    destruct R; tinv H1.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
    destruct p.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
    destruct v; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct eop; inv H1.
    destruct f0; inv H2; simpl.
      exists 64%nat. exists (getFloatAlignmentInfo los 64 true). auto.
Qed.

Lemma extractGenericValue_typsize : forall los nts t1 gv1 const_list typ' gv
  sz al system5
  (HeqR3 : ret gv = extractGenericValue (los, nts) t1 gv1 const_list)
  (e0 : getSubTypFromConstIdxs const_list t1 = ret typ')
  (J1 : _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los nts true)
         true t1 = ret (sz, al))
  (J2 : Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv1)
  (w1 : wf_typ system5 (los, nts) typ'),
  exists sz0 : nat,
    exists al0 : nat,
        _getTypeSizeInBits_and_Alignment los
          (_getTypeSizeInBits_and_Alignment_for_namedts los nts true)
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
    system5 sz al sz2 al2 
  (J1 : _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los nts true)
         true t1 = ret (sz, al))
  (J2 : Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv1)
  (J3 : _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los nts true)
         true t2 = ret (sz2, al2))
  (J4 : Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8) = sizeGenericValue gv2)
  (w1 : wf_typ system5 (los, nts) t1)
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

    match goal with
    | H0: Some _ = gundef _ _ |- _ =>
      eapply gundef__getTypeSizeInBits in H0; eauto;
      destruct H0 as [sz1 [al1 [J3' J4']]];
      rewrite J1 in J3'; inv J3';
      rewrite <- J4'; rewrite <- J2; auto
    end.
Qed.    

Lemma mbop_typsize_helper : forall TD system5 s gv 
  (H0: wf_typ system5 TD (typ_int s))
  (H1: gundef TD (typ_int s) = ret gv),
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat s) 8) = sizeGenericValue gv.
Proof.
  intros. destruct TD.
  symmetry in H1.
  eapply gundef__getTypeSizeInBits in H1; eauto; simpl; auto.
    simpl in H1. destruct H1 as [sz0 [al [J1 J2]]]. inv J1. auto.
Qed.

Lemma mbop_typsize : forall system5 los nts bop5 s gv1 gv2 gv
  (H0: wf_typ system5 (los, nts) (typ_int s))
  (H1: mbop (los,nts) bop5 s gv1 gv2 = Some gv),
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat s) 8) = sizeGenericValue gv.
Proof.
  intros. 
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
  (H0: wf_typ system5 (los, nts) (typ_floatpoint f))
  (H1: mfbop (los,nts) fbop5 f gv1 gv2 = Some gv),
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

(*
Lemma map_list_const_typ_spec3' : forall nts typ_5 ts
  (HeqR : Constant.wf_zeroconst_typ typ_5)
  (HeqR' : true = typ_eq_list_typ nts typ_5 ts),
  Constant.wf_zeroconsts_typ ts.
Proof.
  unfold typ_eq_list_typ.
  intros.
  destruct typ_5; tinv HeqR'.
    destruct (list_typ_dec l0 ts); tinv HeqR'.
    subst. auto.

    remember (lookupAL list_typ (rev nts) i0) as G.
    destruct G; tinv HeqR'.
    destruct (list_typ_dec l0 ts); tinv HeqR'.
    inv HeqR.
Qed.
*)

Lemma wf_array_typ_inv : forall S TD s t,
  wf_typ S TD (typ_array s t) -> wf_typ S TD t.
Proof.
  intros.
  inv H. constructor; auto.
  inv H1. auto.
Qed.

Definition const2GV__getTypeSizeInBits_Prop S TD c t :=
  wf_const S TD c t ->
  forall los nts gl gv t'
  (Heq: TD = (los, nts)) (Hc2g: _const2GV (los,nts) gl c = Some (gv, t'))
  (Hwfg: wf_global TD S gl),
  t = t' /\
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.

Definition consts2GV__getTypeSizeInBits_Prop sdct :=
  wf_const_list sdct ->
  let 'lsdct := unmake_list_system_targetdata_const_typ sdct in
  let '(lsdc, lt) := split lsdct in
  let '(lsd, lc) := split lsdc in
  let '(ls, ld) := split lsd in
  forall S TD los nts gl (Heq: TD = (los, nts))
  (Hwf: wf_list_targetdata_typ S TD gl lsd),
  (forall gv t (Hft: feasible_typ TD t)
    (Heq: forall t0, In t0 lt -> t0 = t)
    (Hc2g: _list_const_arr2GV TD gl t (make_list_const lc) = Some gv),
   exists sz, 
    getTypeAllocSize TD t = Some sz /\
    (sz * length lc)%nat = sizeGenericValue gv) /\
  (forall gv lt'
   (Hc2g: _list_const_struct2GV TD gl (make_list_const lc) = Some (gv, lt')),
   lt' = make_list_typ lt /\
   exists sz, exists al,
    _getListTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) lt' = 
        Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv).

Lemma const2GV_typsize_mutind : 
  (forall S td c t, @const2GV__getTypeSizeInBits_Prop S td c t) /\
  (forall sdct, @consts2GV__getTypeSizeInBits_Prop sdct).
Proof.
Local Opaque zeroconst2GV.
  (wfconst_cases (apply wf_const_mutind; 
                    unfold const2GV__getTypeSizeInBits_Prop, 
                           consts2GV__getTypeSizeInBits_Prop) Case);
    intros; subst; simpl in *.

Case "wfconst_zero".
  inv_mbind.
  split; auto.
    eapply zeroconst2GV__getTypeSizeInBits; eauto.

Case "wfconst_int".
  uniq_result.
  split; auto.
  exists (Size.to_nat sz5). 
  exists (getIntAlignmentInfo los (Size.to_nat sz5) true).
  erewrite int_typsize; eauto.

Case "wfconst_floatingpoint".
  destruct floating_point5; inv Hc2g; 
    simpl; unfold size_chunk_nat, size_chunk, bytesize_chunk; split; auto.
    exists 32%nat. exists (getFloatAlignmentInfo los 32 true).
    simpl. auto.

    exists 64%nat. exists (getFloatAlignmentInfo los 64 true).
    simpl. auto.

Case "wfconst_undef".
  inv_mbind.
  split; auto.
    eapply gundef__getTypeSizeInBits; eauto.

Case "wfconst_null".
  uniq_result.
  split; auto.
    exists (Size.to_nat (getPointerSizeInBits los)).
    exists (getPointerAlignmentInfo los true).
    unfold getPointerSizeInBits. simpl. auto.

Case "wfconst_array". Focus.
  remember (_list_const_arr2GV (los, nts) gl typ5 const_list) as R.
  destruct R; inv Hc2g.
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
  rewrite H1 in H4. unfold Size.to_nat in *.
  destruct sz5; inv H4.
    split; auto.
    exists 8%nat. exists 1%nat. 
    split; auto.

    split; auto.
    destruct (@H0 system5 (los,nts) los nts gl) as [J1 J2]; 
      eauto using const2GV_typsize_mutind_array.
    symmetry in HeqR.
    assert (make_list_const lc = const_list) as EQ.
      eapply make_list_const_spec2; eauto.
    rewrite <- EQ in HeqR.
    assert (feasible_typ (los, nts) typ5) as Hft.
      apply wf_array_typ_inv in H2.
      apply wf_typ__feasible_typ in H2; auto.
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
    rewrite length_unmake_make_list_const in H1. rewrite H1.
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
  destruct R1 as [[gv0 ts]|]; inv Hc2g.
  uniq_result.
  destruct (@H0 system5 (los,nts) los nts gl) as [J1 J2]; 
    eauto using const2GV_typsize_mutind_struct.

  symmetry in HeqR1.
  erewrite <- map_list_const_typ_spec2 in HeqR1; eauto.
  erewrite <- map_list_const_typ_spec1 in H2; eauto.
  apply J2 in HeqR1; eauto.
  clear J1 J2 H.
  destruct HeqR1 as [J5 [sz [al [J6 J7]]]]; subst.
  rewrite H2 in H5.
  erewrite <- typ_eq_list_typ_spec2; try solve [eauto | tauto].
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
  inv_mbind. symmetry_ctx.
  split; auto.
    apply Hwfg in H0.
    destruct H0 as [gv0 [sz [J1 [J2 [J3 _]]]]].
    uniq_result.
    unfold getTypeSizeInBits in J2. simpl in J2.
    inv J2.
    rewrite <- J3. eauto.

Case "wfconst_trunc_int". Focus.
  inv_mbind. 
  split; auto.
    symmetry in HeqR0.
    eapply mtrunc_typsize in HeqR0; eauto.
Unfocus.

Case "wfconst_trunc_fp". Focus.
  inv_mbind. 
  split; auto.
    symmetry in HeqR0.
    eapply mtrunc_typsize in HeqR0; eauto.
Unfocus.

Case "wfconst_zext". Focus.
  inv_mbind. 
  split; auto.
    symmetry in HeqR0.
    eapply mext_typsize in HeqR0; eauto.
Unfocus.

Case "wfconst_sext".  Focus.
  inv_mbind. 
  split; auto.
    symmetry in HeqR0.
    eapply mext_typsize in HeqR0; eauto.
Unfocus.

Case "wfconst_fpext".  Focus.
  inv_mbind.  
  split; auto.
    symmetry in HeqR0.
    eapply mext_typsize in HeqR0; eauto.
Unfocus.

Case "wfconst_ptrtoint". Focus.
  inv_mbind. uniq_result.
  split; auto.
    exists (Size.to_nat sz5).
    exists (getIntAlignmentInfo los (Size.to_nat sz5) true).
    erewrite int_typsize; eauto.
Unfocus.

Case "wfconst_inttoptr". Focus.
  inv_mbind. uniq_result.
  split; auto.
    exists (Size.to_nat (getPointerSizeInBits los)).
    exists (getPointerAlignmentInfo los true).
    simpl. auto.
Unfocus.

Case "wfconst_bitcast". Focus.
  inv_mbind. 
  unfold mbitcast in HeqR0.
  destruct t; inv HeqR0.
  eapply H0 in Hwfg; eauto.
  destruct Hwfg; eauto.
Unfocus.

Case "wfconst_gep". Focus.
  remember (_const2GV (los, nts) gl const_5) as R1.
  destruct R1 as [[]|]; tinv Hc2g.
  destruct t; tinv Hc2g.
  symmetry in HeqR1.
  eapply H0 in HeqR1; eauto.
  destruct HeqR1 as [Heq [sz [al [J1 J2]]]].
  inv J1. inv Heq.
  rewrite H5 in Hc2g.
  assert(
    match gundef (los, nts) typ' with
       | ret gv => ret (gv, typ')
       | merror => merror
       end = ret (gv, t') ->
    typ' = t' /\
    (exists sz0 : nat,
      exists al : nat,
        _getTypeSizeInBits_and_Alignment los
          (_getTypeSizeInBits_and_Alignment_for_namedts los nts true)
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
      inv Hc2g.
      split; auto.
        unfold getConstGEPTyp in H5.
        destruct const_list; tinv H5.  
        remember (getSubTypFromConstIdxs const_list t) as R4.
        destruct R4; inv H5.
        simpl.
        exists (Size.to_nat (getPointerSizeInBits los)).
        exists (getPointerAlignmentInfo los true).
        auto.

Unfocus.

Case "wfconst_select". Focus.
  remember (_const2GV (los, nts) gl const0) as R0.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R0 as [[gv0 t0]|]; tinv Hc2g.
  destruct R1 as [[gv1 t1]|]; tinv Hc2g.
  destruct R2 as [[gv2 t2]|]; tinv Hc2g.
  destruct (isGVZero (los, nts) gv0); inv Hc2g; eauto.
Unfocus.

Case "wfconst_icmp". Focus.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv Hc2g.
  destruct R2 as [[gv2 t2]|]; tinv Hc2g.
  remember (micmp (los, nts) cond5 t1 gv1 gv2) as R3.
  destruct R3; inv Hc2g; eauto.
  split; auto.
    symmetry in HeqR3.
    eapply micmp_typsize in HeqR3; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_fcmp". Focus.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv Hc2g.
  destruct_typ t1; tinv Hc2g.
  destruct R2 as [[gv2 t2]|]; tinv Hc2g.
  remember (mfcmp (los, nts) fcond5 f gv1 gv2) as R3.
  destruct R3; inv Hc2g; eauto.
  split; auto.
    symmetry in HeqR3.
    eapply mfcmp_typsize in HeqR3; try solve [eauto | constructor; auto]. 
Unfocus.

Case "wfconst_extractvalue". Focus.
  remember (_const2GV (los, nts) gl const_5) as R1.
  destruct R1 as [[gv1 t1]|]; tinv Hc2g.
  remember (getSubTypFromConstIdxs const_list t1) as R2.
  destruct R2 as [t2|]; tinv Hc2g.
  remember (extractGenericValue (los, nts) t1 gv1 const_list) as R3.
  destruct R3 as [gv2|]; inv Hc2g.
  symmetry in HeqR1.
  apply H0 in HeqR1; auto.
  destruct HeqR1 as [Heq [sz [al [J1 J2]]]]; subst.
  destruct H6 as [idxs [o [J3 J4]]].
  symmetry in J3.
  eapply getSubTypFromConstIdxs__mgetoffset in J3; eauto.
  subst.
  split; eauto.
    eapply extractGenericValue_typsize; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_insertvalue". Focus.
  clear H1.
  remember (_const2GV (los, nts) gl const_5) as R1.
  destruct R1 as [[gv1 t1]|]; tinv Hc2g.
  remember (_const2GV (los, nts) gl const') as R2.
  destruct R2 as [[gv2 t2]|]; tinv Hc2g.
  remember (insertGenericValue (los, nts) t1 gv1 const_list t2 gv2) as R3.
  destruct R3 as [gv3|]; inv Hc2g.
  symmetry in HeqR1.
  apply H0 in HeqR1; auto.
  destruct HeqR1 as [Heq [sz [al [J1 J2]]]]; subst.
  rewrite J1. 
  symmetry in HeqR2.
  apply H2 in HeqR2; auto.
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
  destruct R1 as [[gv1 t1]|]; tinv Hc2g.
  destruct_typ t1; tinv Hc2g.
  destruct R2 as [[gv2 t2]|]; tinv Hc2g.
  remember (mbop (los, nts) bop5 s0 gv1 gv2) as R3.
  destruct R3; inv Hc2g.
  symmetry in HeqR1.
  apply H0 in HeqR1; auto.
  destruct HeqR1 as [Heq _]. inv Heq.
  split; auto.
    symmetry in HeqR3.
    eapply mbop_typsize in HeqR3; eauto.

Unfocus.

Case "wfconst_fbop". Focus.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv Hc2g.
  destruct_typ t1; tinv Hc2g.
  destruct R2 as [[gv2 t2]|]; tinv Hc2g.
  remember (mfbop (los, nts) fbop5 f gv1 gv2) as R3.
  destruct R3; inv Hc2g.
  symmetry in HeqR1.
  apply H0 in HeqR1; auto.
  destruct HeqR1 as [Heq _]. inv Heq.
  split; auto.
    symmetry in HeqR3.
    eapply mfbop_typsize in HeqR3; eauto.

Unfocus.

Case "wfconst_nil".
  intros; subst.
  split; intros; subst; uniq_result.
    apply feasible_typ_inv' in Hft.
    destruct Hft as [sz [al [H H']]].
    unfold getTypeAllocSize. unfold getTypeStoreSize. unfold getTypeSizeInBits.
    unfold getABITypeAlignment. unfold getAlignment.
    rewrite H. simpl. eauto.

    simpl. split; eauto.    

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
  intros S TD los nts gl EQ Hwfl; subst.
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
    apply H0 in HeqR'; auto.
    destruct HeqR' as [Heq [sz [al [J5 J6]]]]; subst.
    eapply H2 in J1; eauto. destruct J1 as [J1 _]. clear H0 H2.
    symmetry in HeqR.
    apply J1 in HeqR; auto.
    destruct HeqR as [sz0 [J7 J8]].
    simpl_env.
    rewrite sizeGenericValue__app.
    rewrite sizeGenericValue__app.
    rewrite sizeGenericValue__uninits.
    rewrite <- J8. rewrite <- J6.
    rewrite J7 in HeqR0. inv HeqR0.
    rewrite plus_assoc.
    erewrite getTypeAllocSize_roundup; eauto.
    ring.

    intros gv lt' Hc2g.
    remember (_list_const_struct2GV (los, nts) gl (make_list_const lc)) as R.
    destruct R as [[gv1 ts1]|]; try solve [inv Hc2g].
    remember (_const2GV (los, nts) gl const_) as R'.
    destruct R' as [[gv0 t0]|]; try solve [inv Hc2g].
    remember (getTypeAllocSize (los, nts) t0) as R1.
    destruct R1; inv Hc2g.
    apply wf_list_targetdata_typ_cons_inv in Hwfl.
    destruct Hwfl as [J1' [J2' [J3 J4]]]; subst.
    symmetry in HeqR'.
    apply H0 in HeqR'; auto.
    destruct HeqR' as [Heq [sz [al [J5 J6]]]]; subst.
    eapply H2 in J1'; eauto. destruct J1' as [_ J1']. clear H0 H2.
    symmetry in HeqR.
    apply J1' in HeqR; auto.
    destruct HeqR as [Heq [sz0 [al0 [J7 J8]]]]; subst.
    split; auto.
    rewrite sizeGenericValue__app.
    rewrite sizeGenericValue__app.
    rewrite sizeGenericValue__uninits.
    rewrite <- J8. rewrite <- J6. simpl. rewrite J7. rewrite J5.
    rewrite plus_assoc.
    assert (feasible_typ (los, nts) t0) as Hft.
      apply wf_const__wf_typ in H.
      apply wf_typ__feasible_typ in H; auto.
    erewrite getTypeAllocSize_roundup; eauto.
    exists (sz0 +
             RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) al * 8)%nat.
    exists (if le_lt_dec al al0 then al0 else al).
    split; auto.
      eapply getTypeAllocSize_inv' in J5; eauto. subst.
      rewrite plus_comm with (m:=nat_of_Z (ZRdiv (Z_of_nat sz0) 8)).
      apply ZRdiv_prop9.
Transparent zeroconst2GV.
Qed.

Lemma const2GV__getTypeSizeInBits_aux : forall S los nts c t gl gv t',
  wf_const S (los, nts) c t ->
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
  wf_typ S (los,nts) t ->
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
  wf_typ S (los,nts) t ->
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
  (H1: wf_const S (los, nts) c t)
  (H2: const2GV (los, nts) gl c = Some gv),
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
    apply wf_const__wf_typ in H1.
    eapply cgv2gv__getTypeSizeInBits; eauto.
Qed.

Lemma fit_gv__getTypeSizeInBits : forall TD gv s t gv'
  (Hwft : wf_typ s TD t) 
  (HeqR : ret gv' = fit_gv TD t gv),
  exists sz, 
    getTypeSizeInBits TD t = Some sz /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv'.
Proof.
  intros.
  unfold fit_gv in HeqR.
  assert (J:=Hwft).
  eapply wf_typ__getTypeSizeInBits_and_Alignment in J; eauto.
  destruct J as [sz [al [J1 [J2 J3]]]].
  unfold getTypeSizeInBits in *.
  exists sz.
  rewrite J1 in HeqR. rewrite J1.
  split; auto.
    destruct_if.
      symmetry in HeqR0.
      apply andb_true_iff in HeqR0.
      destruct HeqR0 as [HeqR0 _].
      apply neq_inv in HeqR0. auto.

      destruct TD.
      eapply gundef__getTypeSizeInBits in Hwft; eauto.
      destruct Hwft as [sz0 [al0 [J4 J5]]].
      unfold getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts in J1.
      rewrite J1 in J4.
      inv J4. auto.
Qed.

Lemma mload__getTypeSizeInBits : forall t s TD gv a ptr M,
  mload TD M ptr t a = Some gv ->
  wf_typ s TD t ->
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
 
(********************************************)
(** * matching chunks *)

Lemma mload__matches_chunks : forall t TD gv a ptr M,
  mload TD M ptr t a = Some gv ->
  gv_chunks_match_typ TD gv t.
Proof.
  intros.
  apply mload_inv in H.
  destruct H as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold gv_chunks_match_typ, vm_matches_typ, gv_has_chunk.
  fill_ctxhole.
  generalize dependent (Int.signed 31 ofs).
  generalize dependent gv.
  clear.
  induction mc; intros; inv J3; auto.
    inv_mbind. symmetry_ctx.
    apply IHmc in HeqR0.
    constructor; eauto using Mem.load_chunk.
Qed.

Lemma gundef__matches_chunks : forall td gv t (HeqR: ret gv = gundef td t),
  gv_chunks_match_typ td gv t.
Proof.
  unfold gundef. intros.
  inv_mbind. symmetry_ctx.
  unfold gv_chunks_match_typ, gv_has_chunk.
  fill_ctxhole.
  clear. unfold vm_matches_typ.
  induction l0; simpl; auto.
    constructor; simpl; auto.
Qed.

Lemma fit_gv__matches_chunks : forall TD gv t gv'
  (HeqR : ret gv' = fit_gv TD t gv),
  gv_chunks_match_typ TD gv' t.
Proof.
  intros.
  unfold fit_gv in HeqR.
  inv_mbind.
  destruct_if.
    symmetry in HeqR.
    apply andb_true_iff in HeqR.
    destruct HeqR as [_ HeqR].
    apply gv_chunks_match_typb__gv_chunks_match_typ; auto.

    apply gundef__matches_chunks; auto.
Qed.

Lemma flatten_array_typ_eq: forall TD sz t,
  match sz with
  | O => flatten_typ TD (typ_array sz t) = Some (uninitMCs 1)
  | _ =>
    match flatten_typ TD t with
    | Some mc0 =>
      match getTypeAllocSize TD t with
      | Some asz =>
         flatten_typ TD (typ_array sz t) =
           Some (repeatMC (mc0++uninitMCs (Size.to_nat asz - sizeMC mc0))
                  (Size.to_nat sz))
      | _ => flatten_typ TD (typ_array sz t) = None
      end
    | _ => flatten_typ TD (typ_array sz t) = None
    end
  end.
Proof.
  intros. destruct TD.
  destruct sz0; simpl; auto.
  destruct (flatten_typ_aux (l0, n) (flatten_typ_for_namedts (l0, n) l0 n) t);
    auto.
  destruct (getTypeAllocSize (l0, n) t); auto.
Qed.

Lemma flatten_struct_typ_eq: forall TD ts,
  match flatten_typs TD ts with
  | Some nil => flatten_typ TD (typ_struct ts) = Some (uninitMCs 1)
  | Some gv => flatten_typ TD (typ_struct ts) = Some gv
  | _ => flatten_typ TD (typ_struct ts) = None
  end.
Proof.
  intros. destruct TD. simpl.
  destruct (flatten_typs_aux (l0, n) (flatten_typ_for_namedts (l0, n) l0 n) ts)
    as [[]|]; auto.
Qed.

Lemma flatten_struct__eq__namedt: forall los nts id5 lt5 mc1 mc2 
  (Huniq: uniq nts),
  lookupAL _ nts id5 = Some lt5 ->
  flatten_typ (los,nts) (typ_struct lt5) = Some mc1 ->
  flatten_typ (los,nts) (typ_namedt id5) = Some mc2 ->
  mc1 = mc2.
Proof.
  simpl. intros.
  inv_mbind. symmetry_ctx.
  apply lookupAL_middle_inv in H.
  destruct H as [l1 [l2 H]]; subst.
  eapply flatten_typ_for_namedts_spec1 in HeqR; eauto.
  simpl_env in *.
  apply flatten_typ_aux_weakening with (nm2:=l1 ++ [(id5, lt5)]) in HeqR; 
    simpl_env; auto.
  simpl in HeqR. inv_mbind. symmetry_ctx. simpl_env in *.
  uniq_result. rewrite H0 in H2. congruence.
Qed.

Definition zeroconst2GV_aux__matches_chunks_prop S TD t :=
  wf_styp S TD t ->
  forall los nts acc gv (Heq: TD = (los, nts)) nts' 
  (Hsub:exists nts0, nts'=nts0++nts) (Huniq: uniq nts')
  (Hnc: forall id5 gv5 lt5, 
          lookupAL _ nts id5 = Some lt5 ->
          lookupAL _ acc id5 = Some (Some gv5) ->
          gv_chunks_match_typ (los,nts') gv5 (typ_struct lt5))
  (Hprop: exists mc, flatten_typ (los, nts') t = Some mc) 
  (Hz: zeroconst2GV_aux (los,nts') acc t = Some gv),
  gv_chunks_match_typ (los,nts') gv t.

Definition zeroconsts2GV_aux__matches_chunks_prop sdt :=
  wf_styp_list sdt ->
  let 'lsdt := unmake_list_system_targetdata_typ sdt in
  let '(lsd, lt) := split lsdt in
  forall S TD los nts acc gv (Heq: TD = (los, nts)) nts' 
  (Hsub:exists nts0, nts'=nts0++nts) (Huniq: uniq nts')
  (Hnc: forall id5 gv5 lt5, 
          lookupAL _ nts id5 = Some lt5 ->
          lookupAL _ acc id5 = Some (Some gv5) ->
          gv_chunks_match_typ (los,nts') gv5 (typ_struct lt5))
  (Hz: zeroconsts2GV_aux (los,nts') acc (make_list_typ lt) = Some gv)
  (Hprop: exists mc, flatten_typs (los, nts') (make_list_typ lt) = Some mc)
  (Heq': eq_system_targetdata S TD lsd),
  gv_chunks_match_list_typ (los,nts') gv (make_list_typ lt).

Lemma zeroconst2GV_aux_matches_chunks_mutrec :
  (forall S TD t, zeroconst2GV_aux__matches_chunks_prop S TD t) /\
  (forall sdt, zeroconsts2GV_aux__matches_chunks_prop sdt).
Proof.
  (wfstyp_cases (apply wf_styp_mutind; 
    unfold zeroconst2GV_aux__matches_chunks_prop, 
           zeroconsts2GV_aux__matches_chunks_prop) Case);
    intros; simpl in *; subst; uniq_result; try solve [
      congruence | eauto |
      unfold gv_chunks_match_typ, vm_matches_typ; simpl; unfold val2GV;
      constructor; try solve [
        auto |
        split; try solve [
          auto |
          apply Floats.Float.zero_singleoffloat__eq__zero |
          split; simpl; try solve [auto | apply Z_mod_lt; apply Int.modulus_pos]
        ]
      ]
    ].

Case "wf_styp_structure".
  remember (split
              (unmake_list_system_targetdata_typ
                (make_list_system_targetdata_typ
                   (map_list_typ
                      (fun typ_ : typ => (system5, (los, nts):targetdata, typ_))
                      typ_list)))) as R.
  destruct R as [lsd lt].
  assert (make_list_typ lt = typ_list) as EQ1. 
    eapply make_list_typ_spec2; eauto.
  subst.
  assert (eq_system_targetdata system5 (los, nts) lsd) as EQ2.
    eapply wf_styp__feasible_typ_aux_mutrec_struct; eauto.
  subst. 
  inv_mbind. symmetry_ctx.
  eapply_clear H1 in HeqR0; 
    try solve [eauto | destruct Hprop as [mc Hprop2]; inv_mbind; eauto].
  unfold gv_chunks_match_typ. 
  unfold gv_chunks_match_list_typ in HeqR0. 
  unfold AssocList, namedt, id, layouts in *. simpl in *.
  inv_mbind. 
  destruct l0; inv HeqR0; uniq_result; simpl in *. 
    apply uninits_match_uninitMCs.
    constructor; auto.

Case "wf_styp_array".
  assert (J:=@flatten_array_typ_eq (los,nts') sz5 typ5).
  destruct sz5 as [|s].
    uniq_result. unfold gv_chunks_match_typ. simpl. 
    apply uninits_match_uninitMCs.

    inv_mbind. symmetry_ctx.
    eapply_clear H0 in HeqR; 
      try solve [eauto | destruct Hprop as [mc Hprop2]; inv_mbind; eauto].
    unfold gv_chunks_match_typ in *.
    inv_mbind. fill_ctxhole. simpl.
    assert (Forall2 vm_matches_typ
      (g ++ uninits (Size.to_nat s0 - sizeGenericValue g))
      (l0 ++ uninitMCs (Size.to_nat s0 - sizeMC l0))) as Hsim.
      apply match_chunks_app; auto.
        erewrite match_chunks_eq_size; eauto.
        apply uninits_match_uninitMCs.
    apply match_chunks_app; auto.
    apply match_chunks_repeat; auto.

Case "wf_styp_namedt".
  inv_mbind. 
  remember (lookupAL list_typ nts id5) as R.
  destruct R as [lt|]; try congruence. symmetry_ctx.
  assert (G:=HeqR0).
  eapply Hnc in G; eauto.
  unfold gv_chunks_match_typ, null.
  unfold gv_chunks_match_typ in G.
  inv_mbind. 
  unfold flatten_typ in *. simpl. fill_ctxhole.
  inv_mbind. symmetry_ctx.
  destruct Hsub as [nts0 Hsub]; subst.
  apply lookupAL_weaken with (nm2:=nts0) in HeqR0; auto.
  eapply flatten_struct__eq__namedt with (mc1:=l0)(mc2:=x) in HeqR0; 
    subst; simpl; eauto.
    unfold namedt, id, layouts in *.
    rewrite HeqR2. auto.

Case "wf_styp_nil".
  intros. uniq_result. 
  unfold gv_chunks_match_list_typ. simpl. auto.
 
Case "wf_styp_cons".
  remember (split (unmake_list_system_targetdata_typ l')) as R.
  destruct R as [lsd lt]. simpl.
  intros. subst.
  apply eq_system_targetdata_cons_inv in Heq'. 
  destruct Heq' as [H4 [EQ1 EQ2]]; subst.
  inv_mbind. symmetry_ctx.
  eapply_clear H0 in HeqR1;
    try solve [eauto | destruct Hprop as [mc Hprop2]; inv_mbind; eauto].
  eapply_clear H2 in HeqR0;
    try solve [eauto | destruct Hprop as [mc Hprop2]; inv_mbind; eauto].
  clear Hprop. 
  unfold gv_chunks_match_list_typ in *.
  unfold gv_chunks_match_typ in *.
  inv_mbind. symmetry_ctx.
  simpl in *. unfold AssocList, namedt, id, layouts in *. 
  repeat fill_ctxhole. 
  repeat (apply match_chunks_app; auto).
    erewrite match_chunks_eq_size; eauto.
    apply uninits_match_uninitMCs.
Qed.

Lemma noncycled__matches_chunks: forall S los nts
  (H: noncycled S los nts) (Huniq: uniq nts)
  id5 lt nts2 nts1 (EQ: nts = nts1 ++ (id5,lt) :: nts2) nts' (Huniq': uniq nts') 
  (Hsub: exists nts0, nts'=nts0++nts)
  (Hnc: forall id5 lt5, 
          lookupAL _ nts id5 = Some lt5 ->
          exists mc, flatten_typ (los, nts') (typ_struct lt5) = Some mc) gv
  (Hz: zeroconst2GV_aux (los, nts')
         (zeroconst2GV_for_namedts (los, nts') los nts2) (typ_struct lt) = 
           Some gv),
  gv_chunks_match_typ (los, nts') gv (typ_struct lt).
Proof.
Local Opaque flatten_typs flatten_typ.
  induction 1; simpl; intros; subst.
    symmetry in EQ.    
    apply app_eq_nil in EQ.
    destruct EQ as [_ EQ].
    congruence.

    inv Huniq.
    destruct nts1 as [|[]]; inv EQ.
      destruct zeroconst2GV_aux_matches_chunks_mutrec as [J _].
      eapply J in H0; eauto.
      assert (exists mc, flatten_typ (layouts5, nts') (typ_struct lt) = Some mc) 
        as Hty.
        eapply Hnc with (id5:=id0); eauto.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id0 id0); 
          try congruence; eauto.
      assert (exists nts0 : list namedt, nts' = nts0 ++ nts2) as G.
        destruct Hsub as [nts0 Hsub]; subst. 
        exists (nts0 ++ [(id0, lt)]). simpl_env. auto.
      eapply H0 in Hty; eauto.  
      intros id5 gv5 lt5 H1 H2.
      apply lookupAL_middle_inv in H1.
      destruct H1 as [l1 [l2 HeqR]].
      assert (J':=HeqR). subst.
      eapply IHnoncycled with (nts':=nts') in J'; eauto.
        intros.
        eapply Hnc with (id6:=id1); eauto.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); 
          subst; auto.
          apply notin_lookupAL_None in H5. congruence.
       
        eapply zeroconst2GV_for_namedts_spec1 in H2; eauto.
            
      assert (nts1 ++ (id0, lt) :: nts2 = nts1 ++ (id0, lt) :: nts2) as EQ. auto.
      eapply IHnoncycled with (nts':=nts') in EQ; eauto.
        destruct Hsub as [nts0 Hsub]; subst. 
        exists (nts0 ++ [(i0, l0)]). simpl_env. auto.
 
        intros.
        apply Hnc with (id5:=id5)(lt5:=lt5).
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id5 i0); 
          subst; auto.
          apply notin_lookupAL_None in H5. congruence.
Transparent flatten_typs flatten_typ.
Qed.

Lemma zeroconst2GV__matches_chunks : forall t s td gv
  (Hz: zeroconst2GV td t = Some gv)
  (Ht: wf_typ s td t),
  gv_chunks_match_typ td gv t.
Proof. 
  intros. destruct td as [los nts].
  assert (G:=Ht).
  apply flatten_typ_total in G; auto.
  unfold zeroconst2GV in *. inv Ht.
  destruct zeroconst2GV_aux_matches_chunks_mutrec as [J' _].
  assert (exists nts0 : list namedt, nts = nts0 ++ nts) as G'.
    exists nil. auto.
  eapply J'; eauto.
  intros id5 gv5 lt5 J5 J6.
  apply lookupAL_middle_inv in J5.
  destruct J5 as [l1 [l2 HeqR]]. subst.
  eapply noncycled__matches_chunks
    with (nts':=l1 ++ (id5, lt5) :: l2) in H1; eauto.
    intros id0 lt0 H.
    apply lookupAL_middle_inv in H.
    destruct H as [l3 [l4 H]].
    rewrite H in *. 
    symmetry in H.
    rewrite_env ((l3 ++ [(id0, lt0)]) ++ l4).
    eapply flatten_typ_for_namedts_total with (nts1:=l3)(nts2:=l4)
      (nts':=l3 ++ (id0, lt0) :: l4) in H1; eauto.
      destruct H1 as [gvs H1]. 
      simpl_env in H5.
      apply flatten_typ_aux_weakening with (nm2:=l3 ++ [(id0, lt0)]) in H1; 
        simpl_env; auto.
        simpl. simpl in H1.
        exists gvs.
        inv_mbind. symmetry_ctx. simpl_env. simpl_env in HeqR.
        unfold AssocList, namedts, namedt, id, layouts in *. 
        rewrite HeqR. auto.
             
      intros id1 lt1 H10.
      apply lookupAL_middle_inv in H10.
      destruct H10 as [l5 [l6 H10]]. subst.
      rewrite H10 in *.
      eapply noncycled__getTypeSizeInBits_and_Alignment_for_namedts with
        (nts1:=l5)(nts2:=l6)(los:=los)(S:=s)in H1; eauto.
      destruct H1 as [sz [al [H1 ?]]].
      exists sz. exists al. 
      unfold getTypeSizeInBits_and_Alignment.
      unfold getTypeSizeInBits_and_Alignment_for_namedts in H1.
      unfold getTypeSizeInBits_and_Alignment_for_namedts.
      simpl_env in H5.
      apply getTypeSizeInBits_and_Alignment_aux_weakening with 
        (nm2:=l5 ++ [(id1, lt1)]) in H1; simpl_env; simpl_env in H1; auto.

    eapply zeroconst2GV_for_namedts_spec1 in J6; eauto.
Qed.

Lemma mtrunc_matches_chunks : forall S td t1 t2 gv1 gv2 top
  (Hzty: wf_typ S td t2) (H1: mtrunc td top t1 t2 gv1 = Some gv2),
  gv_chunks_match_typ td gv2 t2.
Proof.  
  intros. destruct td.
  unfold mtrunc, GV2val in H1.
  destruct gv1; tinv H1.
    eapply gundef__matches_chunks; eauto.
  destruct p.
  destruct gv1; 
    try solve [inversion H1; eapply gundef__matches_chunks; eauto].
  destruct v; try solve [eapply gundef__matches_chunks; eauto].
    destruct_typ t1; try solve [eapply gundef__matches_chunks; eauto].
    destruct_typ t2; try solve [eapply gundef__matches_chunks; eauto].
      inv H1. unfold gv_chunks_match_typ, vm_matches_typ. simpl.
      constructor; auto.
        split; auto.
        destruct (le_lt_dec wz (s1-1)); simpl; auto.
        split; try solve [auto | apply Z_mod_lt; apply Int.modulus_pos].       

    destruct_typ t1; try solve [eapply gundef__matches_chunks; eauto].
    destruct_typ t2; try solve [eapply gundef__matches_chunks; eauto].
    remember (floating_point_order f1 f0) as R.
    destruct R; tinv H1.
    destruct f0; inv H1.
    destruct f1; inv HeqR.
      unfold gv_chunks_match_typ, vm_matches_typ; simpl.
      constructor; auto.
        split; auto.
        simpl. rewrite Floats.Float.singleoffloat_idem. auto.
Qed.

Lemma mext_matches_chunks : forall S td eop t1 t2 gv1 gv2
  (Hzty: wf_typ S td t2) (H1: mext td eop t1 t2 gv1 = Some gv2),
  gv_chunks_match_typ td gv2 t2.
Proof.  
  intros. destruct td. unfold mext, GV2val in H1.
  destruct_typ t1; tinv H1.
    destruct_typ t2; tinv H1.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__matches_chunks; eauto].
    destruct p.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__matches_chunks; eauto].
    destruct v; try solve [eapply gundef__matches_chunks; eauto].
Local Opaque Val.zero_ext' Val.sign_ext'.
    destruct eop; inv H1;
      unfold gv_chunks_match_typ, vm_matches_typ; constructor; try solve [
        auto |
        split; try solve [auto | simpl; apply Val.zero_ext'_has_chunk
                               | simpl; apply Val.sign_ext'_has_chunk]
      ].
Transparent Val.zero_ext' Val.sign_ext'.

    destruct_typ t2; tinv H1.
    destruct (floating_point_order f f0); tinv H1.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__matches_chunks; eauto].
    destruct p.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__matches_chunks; eauto].
    destruct v; try solve [eapply gundef__matches_chunks; eauto].
    destruct eop; inv H1.
    destruct f0; inv H0; simpl;
      unfold gv_chunks_match_typ, vm_matches_typ; simpl; constructor; 
        simpl; auto.
Qed.

Lemma extractGenericValue_matches_chunks : forall S td t1 gv1 const_list typ' gv
  (e0 : getSubTypFromConstIdxs const_list t1 = ret typ')
  (Hzty: wf_typ S td typ')
  (HeqR3 : ret gv = extractGenericValue td t1 gv1 const_list)
  (J2 : gv_chunks_match_typ td gv1 t1),
  gv_chunks_match_typ td gv typ'.
Proof.
  intros.
  unfold extractGenericValue in HeqR3.
  remember (intConsts2Nats td const_list) as R1.
  destruct R1 as [idxs|]; tinv HeqR3.
  remember (mgetoffset td t1 idxs) as R2.
  destruct R2 as [[o t']|]; tinv HeqR3.
  remember (mget td gv1 o t') as R4.
  eapply getSubTypFromConstIdxs__mgetoffset in e0; eauto.
  destruct R4 as [gv'|]; inv HeqR3.
    eapply mget_matches_chunks; eauto.
    eapply gundef__matches_chunks; eauto.
Qed.

Lemma insertGenericValue_matches_chunks : forall S td t1 gv1 const_list gv t2 gv2
  (Hzty: wf_typ S td t1)
  (J1 : gv_chunks_match_typ td gv1 t1)
  (J3 : gv_chunks_match_typ td gv2 t2)
  (HeqR3 : ret gv = insertGenericValue td t1 gv1 const_list t2 gv2),
  gv_chunks_match_typ td gv t1.
Proof.
  intros.
  unfold insertGenericValue in HeqR3.
  remember (intConsts2Nats td const_list) as R1.
  destruct R1 as [idxs|]; tinv HeqR3.
  remember (mgetoffset td t1 idxs) as R2.
  destruct R2 as [[o t']|]; tinv HeqR3.
  remember (mset td gv1 o t2 gv2) as R4.
  destruct R4 as [gv'|]; inv HeqR3.
    eapply mset_matches_chunks in HeqR4; eauto. 

    eapply gundef__matches_chunks; eauto.
Qed.    

Lemma mbop_matches_chunks_helper : forall TD s gv,
  gundef TD (typ_int s) = ret gv ->
  gv_chunks_match_typ TD gv (typ_int s).
Proof.
  intros. eapply gundef__matches_chunks; eauto.
Qed.

Lemma mbop_matches_chunks : forall td bop5 s gv1 gv2 gv
  (H1: mbop td bop5 s gv1 gv2 = Some gv),
  gv_chunks_match_typ td gv (typ_int s).
Proof.
  intros.
  unfold mbop, GV2val in H1.
  destruct gv1; 
    try solve [inversion H1 | eapply mbop_matches_chunks_helper; eauto].
  destruct p.
  destruct gv1; 
    try solve [inversion H1 | eapply mbop_matches_chunks_helper; eauto].
  destruct v; 
    try solve [inversion H1 | eapply mbop_matches_chunks_helper; eauto].
  destruct gv2; 
    try solve [inversion H1 | eapply mbop_matches_chunks_helper; eauto].
  destruct p.
  destruct gv2; 
    try solve [inversion H1 | eapply mbop_matches_chunks_helper; eauto].
  destruct v; 
    try solve [inversion H1 | eapply mbop_matches_chunks_helper; eauto].
  destruct (eq_nat_dec (wz + 1) (Size.to_nat s));
    try solve [inversion H1 | eapply mbop_matches_chunks_helper; eauto].
  unfold Size.to_nat in e. subst.
  assert (S (Size.to_nat (wz + 1)%nat - 1) = wz + 1)%nat as EQ.
    unfold Size.to_nat. omega.
  destruct td.
Local Opaque Val.add Val.sub Val.mul Val.divu Val.divs Val.modu Val.mods
  Val.shl Val.shrx Val.shr Val.and Val.or Val.xor.
  assert (Size.to_nat (wz + 1)%nat - 1 = wz)%nat as EQ'. 
    rewrite <- EQ. unfold Size.to_nat. omega.
  clear EQ. 
  destruct bop5; inversion H1; subst gv;
    unfold gv_chunks_match_typ, vm_matches_typ; simpl; 
    rewrite EQ'; constructor; try solve 
      [auto | split; simpl; auto using Val.add_has_chunk1,
        Val.sub_has_chunk1, Val.mul_has_chunk1, Val.divu_has_chunk1, 
        Val.divs_has_chunk1, Val.modu_has_chunk1, Val.mods_has_chunk1,
        Val.shl_has_chunk1, Val.shrx_has_chunk1, Val.shr_has_chunk1,
        Val.and_has_chunk1, Val.or_has_chunk1, Val.xor_has_chunk1].
Transparent Val.add Val.sub Val.mul Val.divu Val.divs Val.modu Val.mods
  Val.shl Val.shrx Val.shr Val.and Val.or Val.xor.
Qed.

Lemma mfbop_matches_chunks : forall S td fbop5 f gv1 gv2 gv
  (H: wf_typ S td (typ_floatpoint f))
  (H1:mfbop td fbop5 f gv1 gv2 = Some gv),
  gv_chunks_match_typ td gv (typ_floatpoint f).
Proof.
  intros. destruct td.
  unfold mfbop, GV2val in H1.
  destruct gv1; 
    try solve [inversion H1 | eapply gundef__matches_chunks; eauto].
  destruct p.
  destruct gv1; 
    try solve [inversion H1 | eapply gundef__matches_chunks; eauto].
  destruct v; 
    try solve [inversion H1 | eapply gundef__matches_chunks; eauto].
  destruct gv2; 
    try solve [inversion H1 | eapply gundef__matches_chunks; eauto].
  destruct p.
  destruct gv2; 
    try solve [inversion H1 | eapply gundef__matches_chunks; eauto].
  destruct v; 
    try solve [inversion H1 | eapply gundef__matches_chunks; eauto].
  destruct f; 
    try solve [inversion H1 | eapply gundef__matches_chunks; eauto].
    destruct fbop5; inv H1; simpl;
      unfold gv_chunks_match_typ, vm_matches_typ; simpl; constructor;
        try solve [auto | simpl; rewrite Floats.Float.singleoffloat_idem; auto].

    destruct fbop5; inv H1; simpl;
      unfold gv_chunks_match_typ, vm_matches_typ; simpl; constructor; 
        try solve [auto | repeat split; auto].
Qed.

Lemma mgep_has_chunk: forall TD t ma idxs v,
  mgep TD t ma idxs = Some v ->
  Val.has_chunk v (AST.Mint 31).
Proof.
  unfold mgep.
  intros.
  destruct ma; tinv H.
  destruct idxs; tinv H.
  inv_mbind. uniq_result.
  simpl. auto.
Qed.

Definition const2GV__matches_chunks_Prop S TD c t :=
  wf_const S TD c t ->
  forall gl gv t',
  _const2GV TD gl c = Some (gv, t') ->
  wf_global TD S gl ->
  t = t' /\ gv_chunks_match_typ TD gv t.

Definition consts2GV__matches_chunks_Prop sdct :=
  wf_const_list sdct ->
  let 'lsdct := unmake_list_system_targetdata_const_typ sdct in
  let '(lsdc, lt) := split lsdct in
  let '(lsd, lc) := split lsdc in
  let '(ls, ld) := split lsd in
  forall S TD gl, 
  wf_list_targetdata_typ S TD gl lsd ->
  (forall gv t, 
    (forall t0, In t0 lt -> t0 = t) ->
   _list_const_arr2GV TD gl t (make_list_const lc) = Some gv ->
   match (length lc) with
   | S _ => gv_chunks_match_typ TD gv (typ_array (length lc) t)
   | _ => Forall2 vm_matches_typ gv nil
   end) /\
  (forall gv lt', 
   _list_const_struct2GV TD gl (make_list_const lc) = Some (gv, lt') ->
   lt' = make_list_typ lt /\
   gv_chunks_match_list_typ TD gv lt').

Lemma const2GV_matches_chunks_mutind : 
  (forall S td c t, @const2GV__matches_chunks_Prop S td c t) /\
  (forall sdct, @consts2GV__matches_chunks_Prop sdct).
Proof.
  (wfconst_cases (apply wf_const_mutind; 
                    unfold const2GV__matches_chunks_Prop, 
                           consts2GV__matches_chunks_Prop) Case);
    intros; subst; simpl in *.
Case "wfconst_zero".
  inv_mbind. 
  split; auto.
    eapply zeroconst2GV__matches_chunks; eauto.

Case "wfconst_int".
  uniq_result.
  split; auto.
    destruct targetdata5.
    unfold gv_chunks_match_typ, val2GV, vm_matches_typ. simpl.
    constructor; auto.
      split; auto. split; auto. 
      unfold Int.repr. simpl. apply Z_mod_lt; apply Int.modulus_pos.

Case "wfconst_floatingpoint".
  destruct targetdata5.
  destruct floating_point5; inv H0;
    split; try solve [
      auto |
      unfold gv_chunks_match_typ, val2GV, vm_matches_typ; simpl;
        constructor; try solve [
          auto| 
          split; try solve [auto |
            simpl; try solve 
             [auto | rewrite Floats.Float.singleoffloat_idem; auto]
          ]
        ]
    ].

Case "wfconst_undef".
  inv_mbind.
  split; auto.
    eapply gundef__matches_chunks; eauto.

Case "wfconst_null". 
  destruct targetdata5.
  uniq_result.
  split; auto.
    unfold gv_chunks_match_typ, val2GV, vm_matches_typ. simpl.
    constructor; auto.
      split; auto. split; auto.

Case "wfconst_array". Focus.
  inv_mbind.
  remember (split
             (unmake_list_system_targetdata_const_typ
                (make_list_system_targetdata_const_typ
                   (map_list_const
                      (fun const_ : const =>
                       (system5, targetdata5:targetdata, const_, typ5)) 
                      const_list)))) as R.
  destruct R as [lsdc lt]. 
  remember (split lsdc) as R'.
  destruct R' as [lsd lc].
  remember (split lsd) as R''.
  destruct R'' as [ls ld].
  match goal with
  | H3: match _ with
        | 0%nat => _
        | S _ => _ 
        end = _ |- _ => 
  rewrite H1 in H3; unfold Size.to_nat in *;
  destruct sz5; inv H3
  end.
    split; auto.
      unfold gv_chunks_match_typ, val2GV, vm_matches_typ. simpl.
      destruct targetdata5.
      constructor; auto. split; auto. split; auto.

    split; auto.
    destruct (@H0 system5 targetdata5 gl) as [J1 J2]; try solve 
      [destruct targetdata5; eauto using const2GV_typsize_mutind_array].
    symmetry in HeqR.
    assert (make_list_const lc = const_list) as EQ.
      eapply make_list_const_spec2; eauto.
    rewrite <- EQ in HeqR. subst.
    rewrite length_unmake_make_list_const in H1. 
    apply J1 in HeqR; eauto using make_list_const_spec4.
      unfold gv_chunks_match_typ. simpl.
      rewrite H1 in HeqR. clear - HeqR. 
      inv_mbind. simpl in HeqR. auto.
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
  remember (_list_const_struct2GV (layouts5, namedts5) gl
           (make_list_const
              (map_list_const_typ (fun (const_ : const) (_ : typ) => const_)
                 const_typ_list))) as R1.
  destruct R1 as [[gv0 ts]|]; inv H5.
  destruct (@H0 system5 (layouts5, namedts5) gl) as [J1 J2];
    eauto using const2GV_typsize_mutind_struct.

  symmetry in HeqR1.
  erewrite <- map_list_const_typ_spec2 in HeqR1; eauto.
  erewrite <- map_list_const_typ_spec1 in H2; eauto.
  apply J2 in HeqR1; eauto.
  destruct HeqR1 as [J6 J7]; subst.
  match goal with
  | H2': (if _ then _ else _) = _ |- _ => rewrite H2 in H2'
  end.
  unfold gv_chunks_match_list_typ in J7.
  unfold gv_chunks_match_typ.
  inv_mbind. symmetry_ctx.
  destruct gv0; uniq_result; split; auto.
    inv J7. 
    unfold typ_eq_list_typ in H2.
    destruct t'; tinv H2.
      destruct (list_typ_dec l0 (make_list_typ lt)); subst; tinv H2.
      simpl. simpl in HeqR0. 
      fill_ctxhole. 
      apply uninits_match_uninitMCs.

      assert (J:=H4). inv J.
      apply flatten_typ_total in H4.
      destruct H4 as [gv w1].
      inv_mbind. fill_ctxhole.
      destruct (list_typ_dec l0 (make_list_typ lt)); subst; tinv H2.
      eapply flatten_struct__eq__namedt with (mc1:=uninitMCs 1) in w1; eauto. 
        subst.
        apply uninits_match_uninitMCs.
      
        simpl. simpl in HeqR0. 
        unfold AssocList, namedts, namedt, id, layouts in *. 
        rewrite HeqR0. auto.

    inv J7. 
    unfold typ_eq_list_typ in H2.
    destruct t'; tinv H2.
      destruct (list_typ_dec l0 (make_list_typ lt)); subst; tinv H2.
      simpl. simpl in HeqR0. 
      fill_ctxhole. 
      constructor; auto.
      
      assert (J:=H4). inv J.
      apply flatten_typ_total in H4.
      destruct H4 as [gv w1].
      inv_mbind. fill_ctxhole.
      destruct (list_typ_dec l0 (make_list_typ lt)); subst; tinv H2.
      eapply flatten_struct__eq__namedt with (mc1:=y::l') in w1; eauto. 
        subst. constructor; auto.
      
        simpl. simpl in HeqR0. 
        unfold AssocList, namedts, namedt, id, layouts in *. 
        rewrite HeqR0. auto.

Unfocus.

Case "wfconst_gid".
  inv_mbind. symmetry_ctx.
  split; auto.
    apply H3 in H0.
    destruct H0 as [gv0 [sz [J1 [J2 [J3 J4]]]]]. 
    uniq_result. auto.

Case "wfconst_trunc_int". Focus.
  destruct (_const2GV targetdata5 gl const5) as [[]|]; inv H4.
  remember (mtrunc targetdata5 truncop_int t (typ_int sz2) g) as R.
  destruct R; inv H7.
  split; auto.
   symmetry in HeqR.
   eapply mtrunc_matches_chunks in HeqR; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_trunc_fp". Focus.
  destruct (_const2GV targetdata5 gl const5) as [[]|]; inv H4.
  remember (mtrunc targetdata5 truncop_int t (typ_floatpoint floating_point2) g) 
    as R.
  destruct R; inv H7.
  split; auto.
   symmetry in HeqR.
   eapply mtrunc_matches_chunks in HeqR; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_zext". Focus.
  destruct (_const2GV targetdata5 gl const5) as [[]|]; inv H4.
  remember (mext targetdata5 extop_z t (typ_int sz2) g) as R.
  destruct R; inv H7.
  split; auto.
    symmetry in HeqR.
    eapply mext_matches_chunks in HeqR; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_sext".  Focus.
  destruct (_const2GV targetdata5 gl const5) as [[]|]; inv H4.
  remember (mext targetdata5 extop_s t (typ_int sz2) g) as R.
  destruct R; inv H7.
  split; auto.
    symmetry in HeqR.
    eapply mext_matches_chunks in HeqR; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_fpext".  Focus.
  destruct (_const2GV targetdata5 gl const5) as [[]|]; inv H4.
  remember (mext targetdata5 extop_fp t (typ_floatpoint floating_point2) g) as R.
  destruct R; inv H7.
  split; auto.
    symmetry in HeqR.
    eapply mext_matches_chunks in HeqR; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_ptrtoint". Focus.
  destruct targetdata5. 
  destruct (_const2GV (l0, l1) gl const5) as [[]|]; inv H3.
  split; auto.
    unfold gv_chunks_match_typ, vm_matches_typ. simpl. 
    constructor; auto. split; auto.  split; auto.
      
Unfocus.

Case "wfconst_inttoptr". Focus.
  destruct targetdata5. 
  destruct (_const2GV (l0, l1) gl const5) as [[]|]; inv H3.
  split; auto.
    unfold gv_chunks_match_typ, vm_matches_typ. simpl. 
    constructor; auto. split; auto.  split; auto.
Unfocus.

Case "wfconst_bitcast". Focus.
  remember (_const2GV targetdata5 gl const5) as R1.
  destruct R1 as [[]|]; inv H3.
  remember (mbitcast t g (typ_pointer typ2)) as R.
  destruct R; inv H6.
  unfold mbitcast in HeqR.
  destruct t; inv HeqR.
  eapply H0 in H4; eauto.
  destruct H4; eauto.
Unfocus.

Case "wfconst_gep". Focus.
  remember (_const2GV targetdata5 gl const_5) as R1.
  destruct R1 as [[]|]; tinv H7.
  destruct t; tinv H7.
  symmetry in HeqR1.
  eapply H0 in HeqR1; eauto.
  destruct HeqR1 as [J1 J2].
  inv J1. 
  rewrite H5 in H7.
  assert(
    match gundef targetdata5 typ' with
       | ret gv => ret (gv, typ')
       | merror => merror
       end = ret (gv, t') ->
    typ' = t' /\
    gv_chunks_match_typ targetdata5 gv typ') as G.
    intros W3.
    remember (gundef targetdata5 typ') as R3;
    destruct R3; inv W3;
    split; try solve 
      [auto | eapply gundef__matches_chunks; 
                try solve [eauto | constructor; auto]].
  remember (GV2ptr targetdata5 (getPointerSize targetdata5) g) as R.
  destruct R; auto.
    remember (intConsts2Nats targetdata5 const_list) as R2.
    destruct R2; auto.
      remember (mgep targetdata5 t v l0) as R3.
      destruct R3; auto.
        inv H7.
        split; auto.  
          unfold getConstGEPTyp in H5.
          destruct const_list; tinv H5.  
          remember (getSubTypFromConstIdxs const_list t) as R4.
          destruct R4; inv H5. 
          unfold ptr2GV, val2GV.
          unfold gv_chunks_match_typ, vm_matches_typ. simpl.
          destruct targetdata5. simpl. 
          constructor; auto. split; auto.
          simpl. eapply mgep_has_chunk; eauto.
Unfocus.

Case "wfconst_select". Focus.
  remember (_const2GV targetdata5 gl const0) as R0.
  remember (_const2GV targetdata5 gl const1) as R1.
  remember (_const2GV targetdata5 gl const2) as R2.
  destruct R0 as [[gv0 t0]|]; tinv H8.
  destruct R1 as [[gv1 t1]|]; tinv H8.
  destruct R2 as [[gv2 t2]|]; tinv H8.
  destruct (isGVZero targetdata5 gv0); inv H8; eauto.
Unfocus.

Case "wfconst_icmp". Focus.
  remember (_const2GV targetdata5 gl const1) as R1.
  remember (_const2GV targetdata5 gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H7.
  destruct R2 as [[gv2 t2]|]; tinv H7.
  remember (micmp targetdata5 cond5 t1 gv1 gv2) as R3.
  destruct R3; inv H7; eauto.
  split; auto.
    symmetry in HeqR3.
    eapply micmp_matches_chunks in HeqR3; try solve [eauto | constructor; auto].
Unfocus.

Case "wfconst_fcmp". Focus.
  remember (_const2GV targetdata5 gl const1) as R1.
  remember (_const2GV targetdata5 gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H7.
  destruct_typ t1; tinv H7.
  destruct R2 as [[gv2 t2]|]; tinv H7.
  remember (mfcmp targetdata5 fcond5 f gv1 gv2) as R3.
  destruct R3; inv H7; eauto.
  split; auto.
    symmetry in HeqR3.
    eapply mfcmp_matches_chunks in HeqR3; try solve [eauto | constructor; auto]. 
Unfocus.

Case "wfconst_extractvalue". Focus.
  remember (_const2GV targetdata5 gl const_5) as R1.
  destruct R1 as [[gv1 t1]|]; tinv H8.
  remember (getSubTypFromConstIdxs const_list t1) as R2.
  destruct R2 as [t2|]; tinv H8.
  remember (extractGenericValue targetdata5 t1 gv1 const_list) as R3.
  destruct R3 as [gv2|]; inv H8.
  symmetry in HeqR1.
  apply H0 in HeqR1; auto.
  destruct HeqR1 as [J1 J2]; subst.
  destruct H6 as [idxs [o [J3 J4]]].
  symmetry in J3.
  eapply getSubTypFromConstIdxs__mgetoffset in J3; eauto.
  subst.
  split; eauto.
    eapply extractGenericValue_matches_chunks; 
      try solve [eauto | constructor; auto].

Unfocus.

Case "wfconst_insertvalue". Focus.
  remember (_const2GV targetdata5 gl const_5) as R1.
  destruct R1 as [[gv1 t1]|]; tinv H10.
  remember (_const2GV targetdata5 gl const') as R2.
  destruct R2 as [[gv2 t2]|]; tinv H10.
  remember (insertGenericValue targetdata5 t1 gv1 const_list t2 gv2) as R3.
  destruct R3 as [gv3|]; inv H10.
  symmetry in HeqR1.
  apply H0 in HeqR1; auto.
  destruct HeqR1 as [J1 J2]; subst.
  symmetry in HeqR2.
  apply H2 in HeqR2; auto.
  destruct HeqR2 as [J3 J4]; subst.
  split; auto.
    eapply insertGenericValue_matches_chunks in HeqR3; 
      try solve [eauto | constructor; auto].

Unfocus.

Case "wfconst_bop". Focus.
  remember (_const2GV targetdata5 gl const1) as R1.
  remember (_const2GV targetdata5 gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H4.
  destruct_typ t1; tinv H4.
  destruct R2 as [[gv2 t2]|]; tinv H4.
  remember (mbop targetdata5 bop5 s0 gv1 gv2) as R3.
  destruct R3; inv H4.
  symmetry in HeqR1.
  apply H0 in HeqR1; auto.
  destruct HeqR1 as [Heq _]. inv Heq.
  split; auto.
    symmetry in HeqR3.
    eapply mbop_matches_chunks in HeqR3; eauto.

Unfocus.

Case "wfconst_fbop". Focus.
  remember (_const2GV targetdata5 gl const1) as R1.
  remember (_const2GV targetdata5 gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H4.
  destruct_typ t1; tinv H4.
  destruct R2 as [[gv2 t2]|]; tinv H4.
  remember (mfbop targetdata5 fbop5 f gv1 gv2) as R3.
  destruct R3; inv H4.
  symmetry in HeqR1.
  apply H0 in HeqR1; auto.
  destruct HeqR1 as [Heq _]. inv Heq.
  split; auto.
    symmetry in HeqR3.
    eapply mfbop_matches_chunks in HeqR3; eauto.

Unfocus.

Case "wfconst_nil".
  intros; subst.
  split; intros; subst; uniq_result.
    auto.
     
    destruct TD.
    unfold gv_chunks_match_list_typ. simpl.
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
  intros S TD gl HwfTD; subst.
  split. 
    intros gv t Hin Hc2g.
    remember (_list_const_arr2GV TD gl t (make_list_const lc)) as R.
    destruct R; try solve [inv Hc2g].
    remember (_const2GV TD gl const_) as R'.
    destruct R' as [[gv0 t0]|]; try solve [inv Hc2g].
    destruct (typ_dec t t0); subst; try solve [inv Hc2g].
    remember (getTypeAllocSize TD t0) as R1.
    destruct R1; inv Hc2g.
    assert (typ5 = t0) as EQ. eapply Hin; eauto.
    subst.
    apply wf_list_targetdata_typ_cons_inv in HwfTD.
    destruct HwfTD as [J1 [J2 [J3 J4]]]; subst.
    symmetry in HeqR'.
    apply H0 in HeqR'; auto.
    destruct HeqR' as [J5 J6]; subst.
    eapply H2 in J1; eauto. destruct J1 as [J1 _]. clear H0 H2.
    symmetry in HeqR.
    apply J1 in HeqR; auto.
      destruct TD. 
      unfold gv_chunks_match_typ in HeqR, J6.
      unfold gv_chunks_match_typ. simpl. simpl in HeqR, J6.
      inv_mbind. rewrite <- HeqR0.
      simpl_env.
      repeat (apply match_chunks_app; auto).
        destruct (length lc); simpl; auto.
        rewrite <- HeqR0 in HeqR. auto. 

        erewrite match_chunks_eq_size; eauto.
        apply uninits_match_uninitMCs.

    intros gv lt' Hc2g.
    remember (_list_const_struct2GV TD gl (make_list_const lc)) as R.
    destruct R as [[gv1 ts1]|]; try solve [inv Hc2g].
    remember (_const2GV TD gl const_) as R'.
    destruct R' as [[gv0 t0]|]; try solve [inv Hc2g].
    remember (getTypeAllocSize TD t0) as R1.
    destruct R1; inv Hc2g.
    apply wf_list_targetdata_typ_cons_inv in HwfTD.
    destruct HwfTD as [J1' [J2' [J3 J4]]]; subst.
    symmetry in HeqR'.
    apply H0 in HeqR'; auto.
    destruct HeqR' as [J5 J6]; subst.
    eapply H2 in J1'; eauto. destruct J1' as [_ J1']. clear H0 H2.
    symmetry in HeqR.
    apply J1' in HeqR; auto.
    destruct HeqR as [J7 J8]; subst.
    split; auto.
      unfold gv_chunks_match_typ in J6.
      unfold gv_chunks_match_list_typ in *. 
      destruct TD. simpl in *.
      inv_mbind. simpl. symmetry_ctx. repeat fill_ctxhole.
      repeat (apply match_chunks_app; auto).
        erewrite match_chunks_eq_size; eauto.
        apply uninits_match_uninitMCs.
Qed.

Lemma const2GV__matches_chunks_aux : forall S TD c t gl gv t' 
  (Hwf: wf_const S TD c t),
  _const2GV TD gl c = Some (gv, t') ->
  wf_global TD S gl ->
  t = t' /\ gv_chunks_match_typ TD gv t.
Proof.
  intros.
  destruct const2GV_matches_chunks_mutind. 
  eapply H1; eauto.
Qed.

Lemma cundef_gv__matches_chunks : forall S TD gv t,
  wf_typ S TD t ->
  gv_chunks_match_typ TD gv t ->
  gv_chunks_match_typ TD (cundef_gv gv t) t.
Proof.
  unfold gv_chunks_match_typ, vm_matches_typ. destruct TD.
  intros. inv_mbind.
  destruct_typ t; simpl in *; auto.
    inv HeqR. constructor; auto. split; auto.
    simpl. split; auto. apply Z_mod_lt; apply Int.modulus_pos.

    destruct f; inv HeqR; uniq_result.
      constructor; auto. split; auto. simpl.
        rewrite <- Floats.Float.zero_singleoffloat__eq__zero. auto.
      constructor; auto. split; auto. simpl. auto.

    inv HeqR. unfold null. constructor; auto.
    split; auto. simpl. auto.
Qed.

Lemma cgv2gv__matches_chunks : forall S TD gv t,
  wf_typ S TD t ->
  gv_chunks_match_typ TD gv t ->
  gv_chunks_match_typ TD (cgv2gv gv t) t.
Proof.
  intros. destruct TD. 
  destruct gv as [|[]]; auto.
  destruct v; auto.
  destruct gv; auto.
  simpl. eapply cundef_gv__matches_chunks; eauto.
Qed.

Lemma const2GV__matches_chunks : forall S TD c t gl gv
  (Hwf: wf_const S TD c t) (Hc2g: const2GV TD gl c = Some gv), 
  wf_global TD S gl ->
  gv_chunks_match_typ TD gv t.
Proof.
  intros.
  unfold const2GV in Hc2g.
  remember (_const2GV TD gl c) as R.
  destruct R as [[]|]; inv Hc2g.
  symmetry in HeqR.
  unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment.
  eapply const2GV__matches_chunks_aux in HeqR; eauto.
  destruct HeqR as [J1 J2]; subst.
  apply wf_const__wf_typ in Hwf.
  eapply cgv2gv__matches_chunks; eauto.
Qed.

Lemma mset'_matches_chunks : forall (TD : TargetData) ofs (t1 t2 : typ) 
  x y z (J1: gv_chunks_match_typ TD x t1) (J2: gv_chunks_match_typ TD y t2), 
  mset' TD ofs t1 t2 x y = ret z ->
  gv_chunks_match_typ TD z t1.
Proof.
  unfold mset'. 
  intros. 
  remember (mset TD x ofs t2 y) as R.
  destruct R.
    uniq_result.
    eauto using mset_matches_chunks. 
    eauto using gundef__matches_chunks.
Qed.

Lemma mget'_matches_chunks : forall TD ofs t' x z, 
  mget' TD ofs t' x = Some z ->
  gv_chunks_match_typ TD z t'.
Proof.
  unfold mget'. intros.
  remember (mget TD x ofs t') as R.
  destruct R.
    uniq_result.
    eauto using mget_matches_chunks. 
    eauto using gundef__matches_chunks.
Qed.

Lemma GEP_matches_chunks : forall TD t mp vidxs inbounds0 t' mp',
  LLVMgv.GEP TD t mp vidxs inbounds0 t' = ret mp' ->
  gv_chunks_match_typ TD mp' (typ_pointer t').
Proof.
  unfold LLVMgv.GEP. intros.
  destruct (GV2ptr TD (getPointerSize TD) mp);eauto using gundef__matches_chunks.
  destruct (GVs2Nats TD vidxs); eauto using gundef__matches_chunks.
  remember (mgep TD t v l0) as R.
  destruct R; eauto using gundef__matches_chunks.
  uniq_result.
  unfold gv_chunks_match_typ, vm_matches_typ. destruct TD. simpl.
  unfold ptr2GV, val2GV. simpl.
  constructor; auto. split; auto. simpl. 
  eapply mgep_has_chunk; eauto.
Qed.
