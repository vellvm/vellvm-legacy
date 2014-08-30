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
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import typings.
Require Import infrastructure_props.
Require Import analysis.

Import LLVMinfra.
Import LLVMtd.
Import LLVMtypings.
Import LLVMgv.
Import AtomSet.

(* This file proves the properties of data layouts. *)

(**********************************************************)
(* Helper properties *)
Lemma make_list_const_spec1 : forall
  (const_list : list const)
  (system5 : system)
  (td5 : targetdata)
  (typ5 : typ)
  (sz5 : sz)
  (lsdc : list (system * targetdata * const))
  (lt : list typ)
  (HeqR : (lsdc, lt) =
         split
           (List.map
             (fun const_ : const => (system5, td5, const_, typ5))
             const_list))
  (TD : TargetData)
  (H0 : LLVMtd.feasible_typ TD (typ_array sz5 typ5)),
  LLVMtd.feasible_typs TD lt.
Proof.
  intros.
  generalize dependent lsdc.
  generalize dependent lt.
  induction const_list; intros; simpl in *.
     inv HeqR. simpl. apply feasible_nil_typs.
  
     remember (split
                (List.map
                  (fun const_ : const => (system5, td5, const_, typ5))
                  const_list)) as R2.
     destruct R2. inv HeqR. simpl.
     apply feasible_cons_typs.
     split; eauto.
Qed.

Lemma make_list_const_spec2 : forall
  (const_list : list const)
  (system5 : system)
  (typ5 : typ)
  (td5 : targetdata)
  (typ5 : typ)
  (sz5 : sz)
  (lsdc : list (system * targetdata * const))
  (lt : list typ)
  (HeqR : (lsdc, lt) =
         split
           (List.map
             (fun const_ : const => (system5, td5, const_, typ5))
             const_list))
  (lsd : list (system*targetdata))
  (lc : list const)
  (HeqR' : (lsd, lc) = split lsdc),
  lc = const_list.
Proof.
  induction const_list; intros; simpl in *.
    inv HeqR. simpl in HeqR'. inv HeqR'. auto.
  
    remember (split
               (List.map
                 (fun const_ : const => (system5, td5, const_, typ0))
                 const_list)) as R1.
    destruct R1. inv HeqR. simpl in HeqR'.
    remember (split l0) as R2.
    destruct R2. inv HeqR'; simpl.
    apply f_equal.
    eapply IHconst_list; eauto.
Qed.

Lemma map_list_const_typ_spec1 : 
  forall (system5 : system) (TD : targetdata)
    const_typ_list lsdc lt,
  (lsdc, lt) =
         split
           (List.map
             (fun (p : const * typ) =>
               let (const_, typ_) := p in
               (system5, TD, const_, typ_)) const_typ_list) ->
  lt = List.map snd const_typ_list.
Proof.
  induction const_typ_list; simpl; intros.
    inv H. auto.
    
    destruct a.
    remember (split
               (List.map
                 (fun (p : const * typ) =>
                   let (const_, typ_) := p in
                     (system5, TD, const_, typ_))
                       const_typ_list)) as R1. 
    destruct R1. inv H.
    erewrite <- IHconst_typ_list; eauto.
Qed.

Lemma map_list_const_typ_spec2 : forall 
  (system5 : system)
  (TD : targetdata)
  const_typ_list lsdc lt lc lsd,
  (lsdc, lt) =
         split
           (List.map
             (fun (p : const * typ) =>
               let (const_, typ_) := p in
                 (system5, TD, const_, typ_)) const_typ_list) ->
  (lsd, lc) = split lsdc ->
  lc = List.map (fun p : const * typ => let '(c, _) := p in c) const_typ_list.
Proof.
  induction const_typ_list; simpl; intros.
    inv H. inv H0. auto.
    
    destruct a.
    simpl_split. inv H.
    simpl in H0.
    simpl_split. inv H0.
    erewrite <- IHconst_typ_list; eauto.
Qed.

Lemma make_list_const_spec4 : forall
  (const_list : list const)
  (system5 : system)
  (td5 : targetdata)
  (typ5 : typ)
  (lsdc : list (system * targetdata * const))
  (lt : list typ)
  (HeqR : (lsdc, lt) =
         split
           (List.map
             (fun const_ : const => (system5, td5, const_, typ5))
             const_list))
  t (Hin : In t lt), t = typ5.
Proof.
  intros.
  generalize dependent lsdc.
  generalize dependent lt.
  induction const_list; intros; simpl in *.
     inv HeqR. inv Hin.
  
     remember (split
                 (List.map
                   (fun const_ : const => (system5, td5, const_, typ5))
                   const_list)) as R2.
     destruct R2. inv HeqR.
     simpl in Hin. 
     destruct Hin; eauto.
Qed.

Lemma make_list_typ_spec2 : forall
  (typ_list : list typ)
  (system5 : system)
  (td5 : targetdata)
  (lt : list typ)
  (lsd : list (system*targetdata))
  (HeqR : (lsd, lt) =
         split
           (List.map
             (fun typ_ : typ => (system5, td5, typ_))
             typ_list)),
  lt = typ_list.
Proof.
  induction typ_list; intros; simpl in *.
    inv HeqR. auto.
  
    remember (split
               (List.map
                 (fun typ_ : typ => (system5, td5, typ_))
                 typ_list)) as R1.
    destruct R1. inv HeqR.
    apply f_equal.
    eapply IHtyp_list; eauto.
Qed.

(**********************************************************)
(* Well-formed types are feasible. *)
Definition eq_system_targetdata (S:system) (TD:targetdata) lsd :=
  forall S1 TD1, In (S1,TD1) lsd -> S = S1 /\ TD = TD1.

Lemma eq_system_targetdata_cons_inv : forall S TD S'  TD' lsd,
  eq_system_targetdata S TD ((S', TD') :: lsd) ->
  eq_system_targetdata S TD lsd /\ S' = S /\ TD' = TD.
Proof.
  intros. 
  unfold eq_system_targetdata in *.
  assert (In (S', TD') ((S', TD') :: lsd)) as J. simpl. auto.
  apply H in J. 
  destruct J as [J1 J2]; subst.
  split; auto.
    intros S1 TD1 Hin.    
    apply H. simpl. auto.
Qed.

Lemma wf_styp__feasible_typ_aux_mutrec_struct : 
  forall lt system5 los nts lsd
  (HeqR : (lsd, lt) =
         split
           (List.map
             (fun (typ_ : typ) =>
               (system5, (los, nts), typ_)) lt)),
  eq_system_targetdata system5 (los, nts) lsd.
Proof.
  intros.
  generalize dependent lsd.
  unfold eq_system_targetdata.
  induction lt; simpl; intros.
    uniq_result. inv H.
    
    remember (split
               (List.map
                 (fun (typ_ : typ) =>
                   (system5, (los, nts), typ_))
                     lt)) as R1. 
    destruct R1. uniq_result.
    simpl in H.
    destruct H as [Hin | Hin]; eauto.
      uniq_result. eauto.
Qed.

Definition wf_styp__feasible_typ_aux_Prop S TD t :=
  forall (H : wf_styp S TD t) los nts 
  (Hnc: forall id5, lookupAL _ nts id5 <> None ->
        exists P, 
          lookupAL _ (feasible_typ_for_namedts los nts) id5 = Some P /\ P),
  TD = (los, nts) ->
  LLVMtd.feasible_typ_aux los (feasible_typ_for_namedts los nts) t.

Definition wf_styp_list__feasible_typs_aux_Prop sdt :=
  forall (H : wf_styp_list sdt),
  let 'lsdt := sdt in
  let '(lsd, lt) := split lsdt in
  forall S TD los nts
  (Hnc: forall id5, lookupAL _ nts id5 <> None ->
        exists P, 
          lookupAL _ (feasible_typ_for_namedts los nts) id5 = Some P /\ P),
  TD = (los, nts) ->
  eq_system_targetdata S TD lsd ->
  LLVMtd.feasible_typs_aux los (feasible_typ_for_namedts los nts) 
    lt.

Lemma wf_styp__feasible_typ_aux_mutrec :
  (forall S TD t, wf_styp__feasible_typ_aux_Prop S TD t) /\
  (forall sdt, wf_styp_list__feasible_typs_aux_Prop sdt).
Proof. 
  (wfstyp_cases (apply wf_styp_mutind; 
                 unfold wf_styp__feasible_typ_aux_Prop, 
                        wf_styp_list__feasible_typs_aux_Prop) Case);
    intros; subst; simpl in *; uniq_result; auto.
Case "wf_styp_structure".
  remember (split
             (List.map
               (fun typ_ : typ => (system5, (los, nts):targetdata, typ_))
               typ_list)) as R.
  destruct R as [lsd lt].
  assert (lt = typ_list) as EQ1. 
    eapply make_list_typ_spec2; eauto.
  subst.
  assert (eq_system_targetdata system5 (los, nts) lsd) as EQ2.
    eapply wf_styp__feasible_typ_aux_mutrec_struct; eauto.
  subst.
  eapply H1; eauto. 

Case "wf_styp_namedt".
  apply Hnc in H.
  destruct H as [P [n1 n2]]. fill_ctxhole. auto.

Case "wf_styp_cons".
  remember (split l') as R.
  destruct R as [lsd lt]. simpl.
  intros. subst.
  apply eq_system_targetdata_cons_inv in H4. 
  destruct H4 as [H4 [EQ1 EQ2]]; subst.
  split; eauto.
Qed.

Lemma noncycled__feasible_typ_aux: forall S los nts 
  (H: noncycled S los nts) (Huniq: uniq nts), 
  forall id5 lt nts2 nts1,
  nts = nts1 ++ (id5,lt) :: nts2 ->
  feasible_typ_aux los
    (feasible_typ_for_namedts los nts2) (typ_struct lt).
Proof.
  induction 1; simpl; intros; subst.
    symmetry in H.    
    apply app_eq_nil in H.
    destruct H as [_ H].
    congruence.

    inv Huniq.
    destruct nts1 as [|[]]; inv H1.
      destruct wf_styp__feasible_typ_aux_mutrec as [J _].
      eapply J in H0; eauto.
      eapply H0; eauto.  
      clear - IHnoncycled H4.
      intros.
      apply lookupAL_middle_inv' in H.
      destruct H as [l0 [l1 [l2 HeqR]]].
      assert (J:=HeqR).
      apply IHnoncycled in J; auto.
        subst.
        exists (feasible_typ_aux layouts5 (feasible_typ_for_namedts layouts5 l2)
                (typ_struct l0)).
        split; auto.
        eapply feasible_typ_for_namedts_spec2; eauto.
        simpl. auto.
      
      assert (nts1 ++ (id0, lt) :: nts2 = nts1 ++ (id0, lt) :: nts2) as EQ. auto.
      apply IHnoncycled in EQ; auto.
Qed.

Lemma wf_typ__feasible_typ: forall S td t
  (H: wf_typ S td t), feasible_typ td t.
Proof.
  intros. inv H.
  unfold feasible_typ.
  destruct wf_styp__feasible_typ_aux_mutrec as [J _].
  eapply J; eauto.
  intros.
  apply lookupAL_middle_inv' in H.
  destruct H as [l0 [l1 [l2 HeqR]]]. subst.
  eapply noncycled__feasible_typ_aux in H0; eauto.
  exists (feasible_typ_aux layouts5 (feasible_typ_for_namedts layouts5 l2)
          (typ_struct l0)).
  split; auto.
  eapply feasible_typ_for_namedts_spec2; eauto.
  simpl. auto.
Qed.

(**********************************************************)
(* Well-formed types must have zero constants. *)
Definition wf_zeroconst2GV_aux_total_prop S TD t :=
  wf_styp S TD t ->
  forall acc los nts' (Hty: feasible_typ (los, nts') t) nts 
  (Heq: TD = (los, nts))
  (Hnc: forall id5, lookupAL _ nts id5 <> None ->
        exists gv5, lookupAL _ acc id5 = Some (Some gv5)),
  exists gv, zeroconst2GV_aux (los, nts') acc t = Some gv.

Definition wf_zeroconsts2GV_aux_total_prop sdt :=
  wf_styp_list sdt ->
  let 'lsdt := sdt in
  let '(lsd, lt) := split lsdt in
  forall S TD acc los nts' (Hty: feasible_typs (los, nts') lt)
  nts (Heq: TD = (los, nts))
  (Hnc: forall id5, lookupAL _ nts id5 <> None ->
        exists gv5, lookupAL _ acc id5 = Some (Some gv5)),
  eq_system_targetdata S TD lsd ->
  exists gvn, zeroconsts2GV_aux (los, nts') acc lt = Some gvn.

Lemma wf_zeroconst2GV_aux_total_mutrec :
  (forall S T t, wf_zeroconst2GV_aux_total_prop S T t) /\
  (forall sdt, wf_zeroconsts2GV_aux_total_prop sdt).
Proof.
Local Opaque feasible_typ feasible_typs.
  (wfstyp_cases (apply wf_styp_mutind; 
                 unfold wf_zeroconst2GV_aux_total_prop, 
                        wf_zeroconsts2GV_aux_total_prop) Case);
    intros; subst; simpl in *; uniq_result; eauto.
Case "wf_styp_structure".
  remember (split
             (List.map
               (fun typ_ : typ => (system5, (los,nts):targetdata, typ_))
               typ_list)) as R.
  destruct R as [lsd lt].
  assert (lt = typ_list) as EQ1. 
    eapply make_list_typ_spec2; eauto.
  subst.
  assert (eq_system_targetdata system5 (los, nts) lsd) as EQ2.
    eapply wf_styp__feasible_typ_aux_mutrec_struct; eauto.
  subst.
  apply feasible_struct_typ_inv in Hty.
  eapply H1 in Hty; eauto. 
  fold zeroconsts2GV_aux. fill_ctxhole. destruct x; eauto.

Case "wf_styp_array". 
  apply feasible_array_typ_inv in Hty.
  assert (J:=Hty).
  apply feasible_typ_inv'' in J.
  destruct J as [ssz [asz [J1 J2]]].
  eapply H0 in Hty; eauto.
  repeat fill_ctxhole.
  destruct sz5; eauto.

Case "wf_styp_namedt". 
  apply Hnc in H.
  fill_ctxhole. eauto.

Case "wf_styp_cons".
  remember (split l') as R.
  destruct R as [lsd lt].
  simpl. intros. subst.
  apply feasible_cons_typs_inv in Hty.
  destruct Hty as [J3 J4].
  apply eq_system_targetdata_cons_inv in H3. 
  destruct H3 as [H3 [EQ1 EQ2]]; subst.
  assert (J:=J3).
  apply feasible_typ_inv'' in J.
  destruct J as [ssz [asz [J6 J5]]].
  eapply_clear H0 in J3; eauto.
  eapply_clear H2 in J4; eauto.
  repeat fill_ctxhole. eauto.
Transparent feasible_typ feasible_typs.
Qed.

Lemma zeroconst2GV_for_namedts_spec2: forall TD los i0 r nts2
  lt2 nts1 nts (Huniq: uniq nts),
  zeroconst2GV_aux TD (zeroconst2GV_for_namedts TD los nts2) 
    (typ_struct lt2) = r ->
  nts = nts1 ++ (i0,lt2) :: nts2 ->  
  lookupAL _ (zeroconst2GV_for_namedts TD los nts) i0 = Some r.
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

Lemma noncycled__zeroconst2GV_aux: forall S los nts
  (H: noncycled S los nts) (Huniq: uniq nts)
  id5 lt nts2 nts1 (EQ: nts = nts1 ++ (id5,lt) :: nts2) nts'
  (Hftp: forall id5 lt5, lookupAL _ nts id5 = Some lt5 ->
                         feasible_typ (los, nts') (typ_struct lt5)), 
  exists gv, 
    zeroconst2GV_aux (los, nts')
      (zeroconst2GV_for_namedts (los, nts') los nts2) (typ_struct lt) = Some gv.
Proof.
Local Opaque feasible_typ feasible_typs.
  induction 1; simpl; intros; subst.
    symmetry in EQ.    
    apply app_eq_nil in EQ.
    destruct EQ as [_ EQ].
    congruence.

    inv Huniq.
    destruct nts1 as [|[]]; inv EQ.
      destruct wf_zeroconst2GV_aux_total_mutrec as [J _].
      eapply J in H0; eauto.
      assert (feasible_typ (layouts5, nts') (typ_struct lt)) as Hty.
        apply Hftp with (id5:=id0).
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
        eapply zeroconst2GV_for_namedts_spec2; eauto.
  
        intros.
        apply Hftp with (id6:=id1).
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); 
          subst; auto.
          apply notin_lookupAL_None in H5. congruence.
    
      assert (nts1 ++ (id0, lt) :: nts2 = nts1 ++ (id0, lt) :: nts2) as EQ. auto.
      eapply IHnoncycled in EQ; eauto.
        intros.
        apply Hftp with (id5:=id5).
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id5 i0); 
          subst; auto.
          apply notin_lookupAL_None in H5. congruence.
Transparent feasible_typ feasible_typs.
Qed.

Lemma wf_zeroconst2GV_total: forall S td t
  (H: wf_typ S td t), exists gv, zeroconst2GV td t = Some gv.
Proof.
  intros. 
  assert (G:=H).
  apply wf_typ__feasible_typ in G; auto.
  unfold zeroconst2GV.
  inv H.
  destruct wf_zeroconst2GV_aux_total_mutrec as [J' _].
  eapply J'; eauto.
  intros.
  apply lookupAL_middle_inv' in H.
  destruct H as [l0 [l1 [l2 HeqR]]]. subst.
  eapply noncycled__zeroconst2GV_aux 
    with (nts':=l1 ++ (id5, l0) :: l2) in H0; eauto.
    destruct H0 as [gv H0].
    exists gv.
    eapply zeroconst2GV_for_namedts_spec2; eauto.

    intros.
    apply lookupAL_middle_inv in H.
    destruct H as [l3 [l4 H]].
    rewrite H in *. 
    symmetry in H.
    rewrite_env ((l3 ++ [(id0, lt5)]) ++ l4).
    eapply noncycled__feasible_typ_aux with (nts1:=l3)(nts2:=l4) in H0; eauto.
    unfold feasible_typ.
    eapply feasible_typ_aux_weakening; eauto.
      simpl_env. simpl. auto.
Qed.

(**********************************************************)
(* Well-formed types must have finite type size and valid alignments. *)
Lemma list_system_typ_spec : forall (s : system) td (l0 : list typ),
  exists ls0 : list (system*targetdata),
    split
      (List.map (fun typ_ : typ => (s, td, typ_)) l0) =
    (ls0, l0).
Proof.
  induction l0; simpl; eauto.
    destruct IHl0 as [ls J].
    rewrite J. eauto.
Qed.

Lemma int_typsize : forall s0 td s
  (H0 : wf_typ s0 td (typ_int s)),
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat s) 8) =
    (size_chunk_nat (AST.Mint (s - 1)) + 0)%nat.
Proof.
  intros.
  unfold size_chunk_nat, size_chunk, bytesize_chunk.
  assert (s > 0)%nat as WF.
    inv H0. inv H1. auto.
  assert (S (s - 1) = s) as EQ. omega.
  rewrite EQ. auto.
Qed.

Lemma int_pos_bitsize : forall s0 td s
  (H0 : wf_typ s0 td (typ_int s)), (s > 0)%nat.
Proof.
  intros. inv H0. inv H1. auto.
Qed.

Definition wf_styp__getTypeSizeInBits_and_Alignment_prop' 
  S TD t :=
  wf_styp S TD t ->
  forall los nts nm2
  (Hnc: forall id5, lookupAL _ nts id5 <> None ->
        exists sz0 : nat, exists al : nat,
          lookupAL (nat * nat) nm2 id5 = Some (sz0, al) /\ 
          (sz0 > 0)%nat /\ (al > 0)%nat),
  TD = (los, nts) ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los nm2 true t = Some (sz, al) /\ 
    (sz > 0)%nat /\ (al > 0)%nat.

Definition wf_list_styp__getListTypeSizeInBits_and_Alignment_prop' 
  sdt :=
  wf_styp_list sdt ->
  let 'lsdt := sdt in
  let '(lsd, lt) := split lsdt in
  forall S TD los nts nm2
  (Hnc: forall id5, lookupAL _ nts id5 <> None ->
        exists sz0 : nat, exists al : nat,
          lookupAL (nat * nat) nm2 id5 = Some (sz0, al) /\ 
          (sz0 > 0)%nat /\ (al > 0)%nat),
  TD = (los, nts) ->
  eq_system_targetdata S TD lsd ->
  exists sz, exists al,
    _getListTypeSizeInBits_and_Alignment los nm2 lt 
      = Some (sz,al) /\
    ((sz > 0)%nat -> (al > 0)%nat).

Lemma wf_styp__getTypeSizeInBits_and_Alignment_mutrec' :
  (forall S TD t, wf_styp__getTypeSizeInBits_and_Alignment_prop' S TD t) /\
  (forall sdt, wf_list_styp__getListTypeSizeInBits_and_Alignment_prop' sdt).
Proof.
  (wfstyp_cases (apply wf_styp_mutind;
    unfold wf_styp__getTypeSizeInBits_and_Alignment_prop', 
           wf_list_styp__getListTypeSizeInBits_and_Alignment_prop') Case);
    intros;
    unfold getTypeSizeInBits_and_Alignment in *;
    simpl in *; subst; uniq_result; eauto.

Case "wf_styp_float".
    exists 32%nat. exists (getFloatAlignmentInfo los 32 true).
    split; auto. omega.

Case "wf_styp_double".
    exists 64%nat. exists (getFloatAlignmentInfo los 64 true).
    split; auto. omega.

Case "wf_styp_function".
  unfold getPointerSizeInBits, Size.to_nat.
  simpl.
  exists 32%nat. exists (getPointerAlignmentInfo los true).
  split; auto. omega.

Case "wf_styp_structure".
  remember (split
             (List.map
               (fun typ_ : typ => (system5, (los, nts):targetdata, typ_))
                      typ_list)) as R.
  destruct R as [lsd lt].
  assert (lt = typ_list) as EQ1. 
    eapply make_list_typ_spec2; eauto.
  subst.
  assert (eq_system_targetdata system5 (los, nts) lsd) as EQ2.
    eapply wf_styp__feasible_typ_aux_mutrec_struct; eauto.
  subst.
  eapply H1 in Hnc; eauto.
  destruct Hnc as [sz [al [J1 J2]]].
  fold _getListTypeSizeInBits_and_Alignment. fill_ctxhole.
  destruct sz.
    exists 8%nat. exists 1%nat. split; auto. omega.
    exists (S sz0). exists al. split; auto. omega.

Case "wf_styp_array".
  eapply H0 in Hnc; eauto.
  destruct Hnc as [sz [al [J1 [J2 J3]]]].
  fill_ctxhole.
  destruct sz5 as [|s].
    exists 8%nat. exists 1%nat. split; auto. omega.

    exists (RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) al * 8 *
             Size.to_nat (S s))%nat.
    exists al. split; auto. split; auto.
    assert (RoundUpAlignment (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) al
      >= (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)))%nat as J4.
      apply RoundUpAlignment_spec; auto.
    assert (Coqlib.ZRdiv (Z_of_nat sz) 8 > 0) as J5.
      apply Coqlib.ZRdiv_prop3; try omega.
    apply nat_of_Z_inj_gt in J5; try omega.
    simpl in J5.
    assert (RoundUpAlignment (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) al
      * 8 > 0)%nat as J6. omega. clear J4 J5.
    assert (Size.to_nat (S s) > 0)%nat as J7. unfold Size.to_nat. omega.
    remember (RoundUpAlignment (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) 
      al * 8)%nat as R1. 
    remember (Size.to_nat (S s)) as R2. 
    clear - J6 J7.
    assert (0 * R2 < R1 * R2)%nat as J.
      apply mult_lt_compat_r; auto.
    simpl in J. auto.

Case "wf_styp_pointer".
  unfold getPointerSizeInBits, Size.to_nat.
  simpl.
  exists 32%nat. exists (getPointerAlignmentInfo los true).
  split; auto. omega.

Case "wf_styp_cons".
  remember (split l') as R.
  destruct R as [lsd lt]. simpl.
  intros. subst.
  apply eq_system_targetdata_cons_inv in H4. 
  destruct H4 as [H4 [EQ1 EQ2]]; subst.
  edestruct H0 as [sz1 [al1 [J11 [J12 J13]]]]; eauto.
  edestruct H2 as [sz2 [al2 [J22 J23]]]; eauto.
  repeat fill_ctxhole.
  destruct (le_lt_dec al1 al2); eauto.
    exists (sz2 +
              RoundUpAlignment
                (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz1) 8)) al1 * 8)%nat.
    exists al2.
    split; auto.
      intros. clear - J13 l0. omega.
Qed.

Lemma getTypeSizeInBits_and_Alignment_for_namedts_spec2: forall los i0 r
  nts2 lt2 nts1 nts (Huniq: uniq nts),
  _getTypeSizeInBits_and_Alignment los 
    (_getTypeSizeInBits_and_Alignment_for_namedts los nts2 true) true
      (typ_struct lt2) = Some r ->
  nts = nts1 ++ (i0,lt2) :: nts2 ->  
  lookupAL _ (_getTypeSizeInBits_and_Alignment_for_namedts los nts true) i0 = 
    Some r.
Proof.
Local Opaque _getTypeSizeInBits_and_Alignment.
  induction nts1 as [|[]]; intros; subst; simpl in *.
    rewrite H. simpl.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i0); 
      try congruence; auto.
     
    inv Huniq.
    simpl_env in H4.
    match goal with
    | |- context [match ?e with
                  | Some _ => _
                  | None => _
                  end] => destruct e; simpl; auto
    end.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i1); 
      subst; auto.
      contradict H4; fsetdec.
Transparent _getTypeSizeInBits_and_Alignment.
Qed.

Lemma noncycled__getTypeSizeInBits_and_Alignment_for_namedts: forall S los nts 
  (H: noncycled S los nts) (Huniq: uniq nts), 
  forall id5 lt nts2 nts1,
  nts = nts1 ++ (id5,lt) :: nts2 ->
  exists sz0 : nat,
    exists al : nat,
      _getTypeSizeInBits_and_Alignment los
        (getTypeSizeInBits_and_Alignment_for_namedts (los,nts2) true)
          true (typ_struct lt) = Some (sz0, al) /\ 
      (sz0 > 0)%nat /\ (al > 0)%nat.
Proof.
  induction 1; simpl; intros; subst.
    symmetry in H.    
    apply app_eq_nil in H.
    destruct H as [_ H].
    congruence.

    inv Huniq.
    destruct nts1 as [|[]]; inv H1.
      destruct wf_styp__getTypeSizeInBits_and_Alignment_mutrec' as [J _].
      unfold wf_styp__getTypeSizeInBits_and_Alignment_prop' in J.
      eapply J with (los:=layouts5)
        (nm2:=_getTypeSizeInBits_and_Alignment_for_namedts layouts5 nts2 true) 
        in H0; eauto.
      clear - IHnoncycled H4.
      intros.
      apply lookupAL_middle_inv' in H.
      destruct H as [l0 [l1 [l2 HeqR]]].
      assert (J:=HeqR).
      apply IHnoncycled in J; auto.
        subst. destruct J as [sz0 [al [J1 [J2 J3]]]].
        exists sz0. exists al.
        split; auto. 
          eapply getTypeSizeInBits_and_Alignment_for_namedts_spec2; eauto.

      assert (nts1 ++ (id0, lt) :: nts2 = nts1 ++ (id0, lt) :: nts2) as EQ. auto.
      apply IHnoncycled in EQ; auto.
Qed.

Lemma wf_typ__getTypeSizeInBits_and_Alignment: forall S TD t 
  (H: wf_typ S TD t),
  exists sz, exists al,
    getTypeSizeInBits_and_Alignment TD true t = Some (sz, al) /\ 
    (sz > 0)%nat /\ (al > 0)%nat.
Proof.
  intros.
  unfold getTypeSizeInBits_and_Alignment.
  inv H.
  destruct wf_styp__getTypeSizeInBits_and_Alignment_mutrec' as [J' _].
  eapply J'; eauto.
  intros.
  apply lookupAL_middle_inv' in H.
  destruct H as [l0 [l1 [l2 HeqR]]]. subst.
  eapply noncycled__getTypeSizeInBits_and_Alignment_for_namedts in H0; eauto.
  destruct H0 as [sz0 [al [H0 [H3 H4]]]].
  exists sz0. exists al. 
  split; auto.
  eapply getTypeSizeInBits_and_Alignment_for_namedts_spec2; eauto.
Qed.

(**********************************************************)
(* Properties of feasible_typ *)
Lemma feasible_struct_typ_inv' : forall TD ts
  (H:feasible_typs TD ts), feasible_typ TD (typ_struct ts).
Proof.
  intros. simpl. auto.
Qed.

Lemma typ_eq_list_typ_spec1: forall los (nts:namedts) t1 lt2 (Huniq: uniq nts)
  (H: typ_eq_list_typ nts t1 lt2 = true),
  feasible_typ (los, nts) t1 ->
  feasible_typs (los, nts) lt2.
Proof.
  intros.
  unfold typ_eq_list_typ in H.
  destruct t1; tinv H.
    destruct (list_typ_dec l0 lt2); inv H.
    apply feasible_struct_typ_inv; auto.

    remember (lookupAL _ nts id5) as R.
    destruct R; tinv H.
    destruct (list_typ_dec l0 lt2); inv H.
    simpl in *.
    remember (lookupAL Prop (feasible_typ_for_namedts los nts) id5) as R1.
    destruct R1; try solve [inversion H0].
    eapply feasible_typ_spec1; eauto.
Qed.

(**********************************************************)
(* Properties of getTypeSize *)
Lemma getTypeStoreSize_le_getTypeAllocSize : forall TD t sz1 sz2,
  feasible_typ TD t ->
  getTypeStoreSize TD t = Some sz1 ->
  getTypeAllocSize TD t = Some sz2 ->
  (sz2 >= sz1)%nat.
Proof.
  intros TD t sz1 sz2 J H H0.
  unfold getTypeAllocSize in H0.
  unfold getTypeStoreSize in *.
  unfold getTypeSizeInBits in *.
  unfold getABITypeAlignment in *.
  unfold getAlignment in *.
  remember (getTypeSizeInBits_and_Alignment TD true t) as R.
  destruct R as [[]|]; inv H. inv H0.
  apply feasible_typ_inv' in J; auto.
  destruct J as [sz [al [J1 J2]]].
  rewrite J1 in HeqR. inv HeqR.
  apply RoundUpAlignment_spec; auto.
Qed.  

Definition getTypeSizeInBits_weaken_prop (t:typ) := forall los nm1 nm2 flag r,
  uniq (nm2++nm1) ->
  _getTypeSizeInBits_and_Alignment los nm1 flag t = Some r ->
  _getTypeSizeInBits_and_Alignment los (nm2++nm1) flag t = Some r.

Definition getListTypeSizeInBits_weaken_prop (lt:list typ) := 
  forall los nm1 nm2 r,
  uniq (nm2++nm1) ->
  _getListTypeSizeInBits_and_Alignment los nm1 lt = Some r ->
  _getListTypeSizeInBits_and_Alignment los (nm2++nm1) lt = Some r.

Lemma getTypeSizeInBits_weaken_mutrec :
  (forall t, getTypeSizeInBits_weaken_prop t) *
  (forall lt, getListTypeSizeInBits_weaken_prop lt).
Proof.
  (typ_cases (apply typ_mutrec; 
    unfold getTypeSizeInBits_weaken_prop, 
           getListTypeSizeInBits_weaken_prop) Case);
    intros; simpl in *; try solve [eauto | inversion H | inversion H1 ].
Case "typ_array".
  match goal with
  | H : match ?s with
    | 0%nat => _
    | S _ => 
       match ?x with
       | Some _ => _
       | None => _
       end
    end = _ |- _ => destruct s as [|s]; auto;
                    remember x as R; destruct R as [[]|]; inv H
  end.
  erewrite H; eauto; simpl; auto.
Case "typ_struct".
  match goal with
  | H : match ?x with
        | Some _ => _
        | None => _
        end = _ |- _ => remember x as R; destruct R as [[]|]; inv H
  end.
  erewrite H; eauto; simpl; auto.
Case "typ_namedt".
  apply lookupAL_weaken; auto.
Case "typ_cons".
  repeat match goal with
  | H : match ?x with
        | Some _ => _
        | None => _
        end = _ |- _ => remember x as R; destruct R as [[]|]; inv H
  end.
  erewrite H0; eauto.
  erewrite H; eauto.
  simpl. auto.
Qed.

Lemma getTypeSizeInBits_weaken: forall t los nm1 nm2 flag r,
  uniq (nm2++nm1) ->
  _getTypeSizeInBits_and_Alignment los nm1 flag t = Some r ->
  _getTypeSizeInBits_and_Alignment los (nm2++nm1) flag t = Some r.
Proof.
  destruct getTypeSizeInBits_weaken_mutrec as [J _].
  unfold getTypeSizeInBits_weaken_prop in J. auto.
Qed.

Lemma getTypeSizeInBits_and_Alignment_for_namedts_dom: forall los flag nm,
  dom (_getTypeSizeInBits_and_Alignment_for_namedts los nm flag) [<=] dom nm.
Proof.
  induction nm as [|[]]; simpl.
    fsetdec.
   
    match goal with 
    | |- dom match ?x with
             | Some _ => _
             | None => _
             end [<=] _ => destruct x; simpl; fsetdec
    end.
Qed.

Lemma getTypeSizeInBits_and_Alignment_for_namedts_uniq: forall los flag nm
  (Huniq: uniq nm),
  uniq (_getTypeSizeInBits_and_Alignment_for_namedts los nm flag).
Proof.
  induction 1; simpl; auto.
    match goal with 
    | |- uniq match ?x with
             | Some _ => _
             | None => _
             end => destruct x; simpl; auto
    end.
    simpl_env.
    constructor; auto.
      assert (J:=@getTypeSizeInBits_and_Alignment_for_namedts_dom los flag E).
      fsetdec.
Qed.

Lemma getTypeSizeInBits_and_Alignment_for_namedts_cons : forall los nm1 flag 
  nm2,
  exists re,
    _getTypeSizeInBits_and_Alignment_for_namedts los (nm2++nm1) flag =
      re ++ _getTypeSizeInBits_and_Alignment_for_namedts los nm1 flag.
Proof.
  induction nm2 as [|[]]; simpl.
    exists nil. auto.

    destruct IHnm2 as [re IHnm2].
    rewrite IHnm2.
    match goal with 
    | |- exists _:_,
           match ?x with
           | Some _ => _
           | None => _
           end = _ => destruct x; simpl_env; eauto
    end.
Qed.

Lemma getTypeSizeInBits_and_Alignment_aux_weakening: forall los flag t r 
  (nm1 nm2:namedts) (Huniq: uniq (nm2++nm1)),
  _getTypeSizeInBits_and_Alignment los
    (_getTypeSizeInBits_and_Alignment_for_namedts los nm1 true) flag t 
      = Some r ->
  _getTypeSizeInBits_and_Alignment los
    (_getTypeSizeInBits_and_Alignment_for_namedts los (nm2++nm1) true) flag t 
      = Some r.
Proof.
  intros.  
  destruct (@getTypeSizeInBits_and_Alignment_for_namedts_cons los nm1 true nm2)
    as [re J].
  rewrite J.
  apply getTypeSizeInBits_weaken; auto.
    unfold id in *.
    rewrite <- J.
    eapply getTypeSizeInBits_and_Alignment_for_namedts_uniq; eauto.
Qed.

Lemma getTypeSizeInBits_and_Alignment_for_namedts_spec1: forall los nts2 lt2
  i0 r nts1 nts (Huniq: uniq nts),
  lookupAL _ 
     (_getTypeSizeInBits_and_Alignment_for_namedts los nts true) i0 = Some r ->
  nts = nts1 ++ (i0,lt2) :: nts2 ->  
  _getTypeSizeInBits_and_Alignment los
     (_getTypeSizeInBits_and_Alignment_for_namedts los nts2 true) true
     (typ_struct lt2) = Some r.
Proof.
  induction nts1 as [|[]]; intros; subst; simpl in *.
    match goal with
    | H : lookupAL _ _ _ = _ |- ?x = _ => destruct x; simpl in H
    end.
      destruct (i0 == i0); try congruence; auto.
      destruct_uniq.
      assert (i0 `notin` 
        dom (_getTypeSizeInBits_and_Alignment_for_namedts los nts2 true)) as Hnotin.
        assert (J:=@getTypeSizeInBits_and_Alignment_for_namedts_dom los true nts2).
        fsetdec.
      apply notin_lookupAL_None in Hnotin; auto.
      match goal with
      | H1: ?f ?a ?b = Some _, H2: ?f ?a ?b = None |- _ => 
          rewrite H1 in H2; inv H2
      end. 

    inv Huniq.
    match goal with
    | H : lookupAL _
            match ?x with
            | Some _ => _
            | None => _
            end _ = _ |- _ => remember x as R; destruct R; simpl in *
    end.
      simpl_env in H4.
      destruct (i0 == a); subst.
        contradict H4; fsetdec.
        apply IHnts1 in H; auto.

      apply IHnts1 in H; auto.
Qed.

Lemma getTypeSizeInBits_and_Alignment_spec1: forall (los : layouts) (i0 : id) 
  (nts : namedts) (lt2 : list typ)
  (HeqR : ret lt2 = lookupAL _ nts i0) (Huniq: uniq nts)
  (H:lookupAL _ 
     (_getTypeSizeInBits_and_Alignment_for_namedts los nts true) i0 <> None),
  _getTypeSizeInBits_and_Alignment los
     (_getTypeSizeInBits_and_Alignment_for_namedts los nts true) true
     (typ_struct lt2) =
  _getTypeSizeInBits_and_Alignment los
     (_getTypeSizeInBits_and_Alignment_for_namedts los nts true) true
     (typ_namedt i0).
Proof.
  intros. 
  assert (exists nts1, exists nts2, nts = nts1 ++ (i0,lt2) :: nts2) as J.
    apply lookupAL_middle_inv; auto.
  destruct J as [nts1 [nts2 J]]; subst.
  remember (lookupAL (nat * nat)
        (_getTypeSizeInBits_and_Alignment_for_namedts los
           (nts1 ++ (i0, lt2) :: nts2) true) i0) as R.
  destruct R; try congruence. symmetry in HeqR0.
  eapply getTypeSizeInBits_and_Alignment_for_namedts_spec1 in HeqR0; eauto.
  rewrite_env ((nts1 ++ [(i0, lt2)]) ++ nts2).
  erewrite getTypeSizeInBits_and_Alignment_aux_weakening; simpl_env; eauto.
  simpl. simpl_env.
  eapply getTypeSizeInBits_and_Alignment_for_namedts_spec2 in HeqR0; eauto.
Qed.

Lemma typ_eq_list_typ_spec2: forall S los (nts:namedts) t1 lt2
  (H: typ_eq_list_typ nts t1 lt2 = true) (Hwf: wf_typ S (los, nts) t1),
  _getTypeSizeInBits_and_Alignment los
    (_getTypeSizeInBits_and_Alignment_for_namedts los nts true)
    true (typ_struct lt2) = 
  _getTypeSizeInBits_and_Alignment los
    (_getTypeSizeInBits_and_Alignment_for_namedts los nts true)
    true t1.
Proof.
  intros.
  unfold typ_eq_list_typ in H.
  destruct t1; tinv H.
    destruct (list_typ_dec l0 lt2); inv H; auto.

    remember (lookupAL _ nts id5) as R.
    destruct R; tinv H.
    destruct (list_typ_dec l0 lt2); inv H.
    assert (Hft:=Hwf).
    apply wf_typ__getTypeSizeInBits_and_Alignment in Hft.
    inv Hwf.
    erewrite getTypeSizeInBits_and_Alignment_spec1; eauto.
    simpl in Hft.
    destruct Hft as [sz [al [J1 ?]]].
    congruence.
Qed.
