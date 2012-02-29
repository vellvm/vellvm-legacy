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

(********************************************)
(** * feasible typs *)

Lemma feasible_typ_list__in_args__feasible_typ : forall td 
  typ_attributes_id_list
  (H18: feasible_typ_list
          (make_list_targetdata_typ
             (map_list_typ_attributes_id
                (fun (typ_ : typ) (_ : attributes) (_ : id) =>
                 (td, typ_)) typ_attributes_id_list)))
  t a i0,
    In (t, a, i0)
       (map_list_typ_attributes_id
         (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) =>
          (typ_, attributes_, id_)) typ_attributes_id_list) ->
    feasible_typ td t.
Proof.
  induction typ_attributes_id_list; simpl; intros.
    inv H.
   
    inv H18. 
    destruct H as [H | H]; eauto.
      inv H; auto.
Qed.

Lemma make_list_const_spec1 : forall
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
  (H0 : LLVMtd.feasible_typ TD (typ_array sz5 typ5)),
  LLVMtd.feasible_typs TD (make_list_typ lt).
Proof.
  intros.
  generalize dependent lsdc.
  generalize dependent lt.
  induction const_list; intros; simpl in *.
     inv HeqR. simpl. apply feasible_nil_typs.
  
     remember (split
              (unmake_list_system_targetdata_const_typ
                 (make_list_system_targetdata_const_typ
                    (map_list_const
                       (fun const_ : const => (system5, td5, const_, typ5))
                       const_list)))) as R2.
     destruct R2. inv HeqR. simpl.
     apply feasible_cons_typs.
     split; eauto.
Qed.

Lemma make_list_const_spec2 : forall
  (const_list : list_const)
  (system5 : system)
  (typ5 : typ)
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
  (lsd : list (system*targetdata))
  (lc : list const)
  (HeqR' : (lsd, lc) = split lsdc),
  make_list_const lc = const_list.
Proof.
  induction const_list; intros; simpl in *.
    inv HeqR. simpl in HeqR'. inv HeqR'. auto.
  
    remember (split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const
                    (fun const_ : const => (system5, td5, const_, typ5))
                    const_list)))) as R1.
    destruct R1. inv HeqR. simpl in HeqR'.
    remember (split (unmake_list_system_targetdata_const_typ
                 (make_list_system_targetdata_const_typ
                    (map_list_const
                       (fun const_ : const => (system5, td5, const_, typ0))
                       const_list)))) as R2.
    destruct R2. inv H0; simpl.
    simpl in HeqR'.
    remember (split l2) as R3.
    destruct R3. inv HeqR'. simpl.
    erewrite IHconst_list; eauto.        
Qed.

Lemma length_unmake_make_list_const : forall lc,
  length (unmake_list_const (make_list_const lc)) = length lc.
Proof.
  induction lc; simpl; auto.
Qed.

Lemma map_list_const_typ_spec1 : forall system5 TD const_typ_list lsdc lt,
  (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const_typ
                    (fun (const_ : const) (typ_ : typ) =>
                     (system5, TD, const_, typ_)) const_typ_list))) ->
  lt = map_list_const_typ (fun (_ : const) (typ_ : typ) => typ_) const_typ_list.
Proof.
  induction const_typ_list; simpl; intros.
    inv H. auto.
    
    remember (split
              (unmake_list_system_targetdata_const_typ
                 (make_list_system_targetdata_const_typ
                    (map_list_const_typ
                       (fun (const_ : const) (typ_ : typ) =>
                        (system5, TD, const_, typ_))
                       const_typ_list)))) as R1. 
    destruct R1. inv H.
    erewrite <- IHconst_typ_list; eauto.
Qed.

Lemma map_list_const_typ_spec2 : forall system5 TD const_typ_list lsdc lt lc lsd,
  (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const_typ
                    (fun (const_ : const) (typ_ : typ) =>
                     (system5, TD, const_, typ_)) const_typ_list))) ->
  (lsd, lc) = split lsdc ->
  lc = map_list_const_typ (fun (const_ : const) (_ : typ) => const_) 
         const_typ_list.
Proof.
  induction const_typ_list; simpl; intros.
    inv H. inv H0. auto.
  
    remember (split
            (unmake_list_system_targetdata_const_typ
               (make_list_system_targetdata_const_typ
                  (map_list_const_typ
                     (fun (const_ : const) (typ_ : typ) =>
                      (system5, TD, const_, typ_))
                     const_typ_list)))) as R1. 
    destruct R1. inv H.
    simpl in H0.
    remember (split l0).
    destruct p. inv H0.
    erewrite <- IHconst_typ_list; eauto.
Qed.

Lemma map_list_const_typ_spec3 : forall system5 TD const_typ_list lsdc lt lc lsd
  (HeqR : (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const_typ
                    (fun (const_ : const) (typ_ : typ) =>
                     (system5, TD, const_, typ_)) const_typ_list))))
  (HeqR' : (lsd, lc) = split lsdc)
  (H1 : feasible_typ_list
        (make_list_targetdata_typ
           (map_list_const_typ
              (fun (_ : const) (typ_ : typ) => (TD, typ_))
              const_typ_list))),
  LLVMtd.feasible_typs TD (make_list_typ lt).
Proof.
    induction const_typ_list; simpl; intros.
      inv HeqR. simpl in HeqR'. inv HeqR'. simpl. apply feasible_nil_typs.

      remember (@split (prod (prod system targetdata) const) typ
               (unmake_list_system_targetdata_const_typ
                  (make_list_system_targetdata_const_typ
                     (@map_list_const_typ
                        (prod (prod (prod system targetdata) const) typ)
                        (fun (const_ : const) (typ_ : typ) =>
                         @pair (prod (prod system targetdata) const) typ
                           (@pair (prod system targetdata) const
                              (@pair system targetdata system5 TD) const_)
                           typ_) const_typ_list)))) as R1.
      destruct R1. inv HeqR. simpl in HeqR'.
      remember (split l0) as R2.
      destruct R2. inv HeqR'.
      simpl in *. inv H1. inv H2.
      apply feasible_cons_typs.
      split; eauto.
Qed.

Lemma make_list_const_spec4 : forall
  (const_list : list_const)
  (system5 : system)
  (td5 : targetdata)
  (typ5 : typ)
  (lsdc : list (system * targetdata * const))
  (lt : list typ)
  (HeqR : (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const
                    (fun const_ : const => (system5, td5, const_, typ5))
                    const_list))))
  t (Hin : In t lt), t = typ5.
Proof.
  intros.
  generalize dependent lsdc.
  generalize dependent lt.
  induction const_list; intros; simpl in *.
     inv HeqR. inv Hin.
  
     remember (split
              (unmake_list_system_targetdata_const_typ
                 (make_list_system_targetdata_const_typ
                    (map_list_const
                       (fun const_ : const => (system5, td5, const_, typ5))
                       const_list)))) as R2.
     destruct R2. inv HeqR.
     simpl in Hin. 
     destruct Hin; eauto.
Qed.

Lemma wf_zeroconst2GV_total : forall TD t,
  Constant.wf_zeroconst_typ t ->
  feasible_typ TD t ->
  exists gv, zeroconst2GV TD t = Some gv.
Proof.
  intros. inv H0.
  destruct wf_zeroconst2GV_total_mutrec as [J _].
  apply J; auto.
Qed.

Lemma list_system_typ_spec : forall (s : system) (l0 : list_typ),
  exists ls0 : list system,
    split
       (unmake_list_system_typ
          (make_list_system_typ
             (map_list_typ (fun typ_ : typ => (s, typ_)) l0))) =
    (ls0, unmake_list_typ l0).
Proof.
  induction l0; simpl; eauto.
    destruct IHl0 as [ls J].
    rewrite J. eauto.
Qed.

Lemma unmake_list_system_typ_inv : forall lst ls t l0,
  split (unmake_list_system_typ lst) = (ls, t :: unmake_list_typ l0) ->
  exists s, exists ls', exists lst',
    lst = Cons_list_system_typ s t lst' /\ ls = s::ls' /\ 
    split (unmake_list_system_typ lst') = (ls', unmake_list_typ l0).
Proof.
  induction lst; intros; simpl in *.
    inv H.
  
    remember (split (unmake_list_system_typ lst)) as R.
    destruct R as [g d].
    inv H.
    exists s. exists g. exists lst. auto.
Qed.

Lemma int_typsize : forall s0 s
  (H0 : wf_typ s0 (typ_int s)),
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat s) 8) =
    (size_chunk_nat (AST.Mint (s - 1)) + 0)%nat.
Proof.
  intros.
  unfold size_chunk_nat, size_chunk, bytesize_chunk.
  assert (s > 0)%nat as WF.
    inv H0. auto.
  assert (S (s - 1) = s) as EQ. omega.
  rewrite EQ. auto.
Qed.

Definition feasible_typ_aux_inv_prop (t:typ) := forall los nm1 nm2 s,
  wf_typ s t -> LLVMtd.feasible_typ_aux los nm1 t -> 
  (forall (i0 : id) (P : Prop) (HeqR : Some P = lookupAL Prop nm1 i0) (H : P),
   exists sz0 : nat,
     exists al : nat,
       lookupAL (nat * nat) nm2 i0 = Some (sz0, al) /\ 
       (sz0 > 0)%nat /\ (al > 0)%nat) ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los nm2 true t = Some (sz, al) /\ 
    (sz > 0)%nat /\ (al > 0)%nat.

Definition feasible_typs_aux_inv_prop (lt:list_typ) := forall los nm1 nm2 lst,
  wf_typ_list lst -> LLVMtd.feasible_typs_aux los nm1 lt -> 
  (forall (i0 : id) (P : Prop) (HeqR : Some P = lookupAL Prop nm1 i0) (H : P),
   exists sz0 : nat,
     exists al : nat,
       lookupAL (nat * nat) nm2 i0 = Some (sz0, al) /\ 
       (sz0 > 0)%nat /\ (al > 0)%nat) ->
   (exists ls, 
    split (unmake_list_system_typ lst) = (ls, unmake_list_typ lt)) ->
  (forall t, In t (unmake_list_typ lt) -> LLVMtd.feasible_typ_aux los nm1 t) /\
  exists sz, exists al,
    _getListTypeSizeInBits_and_Alignment los nm2 lt = Some (sz,al) /\
    ((sz > 0)%nat -> (al > 0)%nat).

Lemma feasible_typ_aux_inv_mutrec :
  (forall t, feasible_typ_aux_inv_prop t) *
  (forall lt, feasible_typs_aux_inv_prop lt).
Proof.
  (typ_cases (apply typ_mutrec; 
    unfold feasible_typ_aux_inv_prop, feasible_typs_aux_inv_prop) Case);
    intros;
    unfold getTypeSizeInBits_and_Alignment in *; 
    simpl in *; 
    try solve [eauto | inversion H0 | inversion H2].
Case "typ_int".
  inv H. eauto.
Case "typ_floatingpoint".
  destruct f; inv H; try solve [inversion H0 | eauto].
    unfold LLVMtd.feasible_typ_aux in H0; simpl in H0;
    exists 32%nat. exists (getFloatAlignmentInfo los 32 true).
    split; auto. omega.

    unfold LLVMtd.feasible_typ_aux in H0. simpl in H0.
    exists 64%nat. exists (getFloatAlignmentInfo los 64 true).
    split; auto. omega.
Case "typ_array".
  inv H0.
  eapply H in H1; eauto.
  destruct H1 as [sz [al [J1 [J2 J3]]]].
  rewrite J1. 
  destruct s.
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

Case "typ_struct".
  inv H0.
  eapply H in H1; eauto using list_system_typ_spec.
  destruct H1 as [J0 [sz [al [J1 J2]]]].
  unfold getListTypeSizeInBits_and_Alignment in J1.
  rewrite J1. 
  destruct sz.
    exists 8%nat. exists 1%nat. split; auto. omega.
    exists (S sz0). exists al. split; auto. split. omega. apply J2. omega.

Case "typ_pointer".
  unfold LLVMtd.feasible_typ_aux in H1. simpl in H1.
  unfold getPointerSizeInBits, Size.to_nat.
  simpl.
  exists 32%nat. exists (getPointerAlignmentInfo los true).
  split; auto. omega.

Case "typ_namedt".
  match goal with
  | H: match ?x with
       | Some _ => _
       | None => False
       end |- _ => remember x as R; destruct R as [|]; tinv H; eauto
  end.
  
Case "typ_nil".
  split.
    intros. tauto.
    simpl. exists 0%nat. exists 0%nat. split; auto.

Case "typ_cons".
  destruct H2 as [J1 J2]. destruct H4 as [l3 H4].
  apply unmake_list_system_typ_inv in H4.
  destruct H4 as [s [ls' [lst' [J1' [J2' J3']]]]]; subst.
  inv H1.
  eapply H0 in J2; eauto.
  destruct J2 as [J21 [sz2 [al2 [J22 J23]]]].
  split.
    intros. 
    destruct H1 as [H1 | H1]; subst; auto.
      
    simpl.
    unfold getListTypeSizeInBits_and_Alignment in J22.
    unfold getTypeSizeInBits_and_Alignment_for_namedts in J22.
    rewrite J22.
    eapply H in J1; eauto.
    destruct J1 as [sz1 [al1 [J11 [J12 J13]]]].
    unfold getTypeSizeInBits_and_Alignment_for_namedts in J11.
    rewrite J11.
    destruct (le_lt_dec al1 al2); eauto.
      exists (sz2 +
             RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz1) 8)) al1 * 8)%nat.
      exists al2.
      split; auto.
        intros. clear - J13 l1. omega.
Qed.

Lemma feasible_typ_aux_inv : forall t los nm1 nm2 s,
  wf_typ s t -> LLVMtd.feasible_typ_aux los nm1 t -> 
  (forall (i0 : id) (P : Prop) (HeqR : Some P = lookupAL Prop nm1 i0) (H : P),
   exists sz0 : nat,
     exists al : nat,
       lookupAL (nat * nat) nm2 i0 = Some (sz0, al) /\ 
       (sz0 > 0)%nat /\ (al > 0)%nat) ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los nm2 true t = Some (sz, al) /\ 
    (sz > 0)%nat /\ (al > 0)%nat.
Proof.
  destruct feasible_typ_aux_inv_mutrec. auto.
Qed.

Lemma feasible_typs_aux_inv : forall (lt:list_typ) los nm1 nm2 lst,
  wf_typ_list lst -> LLVMtd.feasible_typs_aux los nm1 lt -> 
  (forall (i0 : id) (P : Prop) (HeqR : Some P = lookupAL Prop nm1 i0) (H : P),
   exists sz0 : nat,
     exists al : nat,
       lookupAL (nat * nat) nm2 i0 = Some (sz0, al) /\ 
       (sz0 > 0)%nat /\ (al > 0)%nat) ->
   (exists ls, 
    split (unmake_list_system_typ lst) = (ls, unmake_list_typ lt)) ->
  (forall t, In t (unmake_list_typ lt) -> LLVMtd.feasible_typ_aux los nm1 t) /\
  exists sz, exists al,
    _getListTypeSizeInBits_and_Alignment los nm2 lt = Some (sz,al) /\
    ((sz > 0)%nat -> (al > 0)%nat).
Proof.
  destruct feasible_typ_aux_inv_mutrec. auto.
Qed.

Lemma feasible_typ_for_namedts_inv: 
  forall s los nts (Htyps: ty_namedts s nts) (i0 : id) (P : Prop),
  Some P = lookupAL Prop (feasible_typ_for_namedts los nts) i0 ->
  P ->
  exists sz0 : nat,
    exists al : nat,
      lookupAL (nat * nat)
        (_getTypeSizeInBits_and_Alignment_for_namedts los nts true) i0 =
      Some (sz0, al) /\ (sz0 > 0)%nat /\ (al > 0)%nat.
Proof.
  induction nts as [|[i1 lt1]]; simpl; intros.
    congruence.

    inv Htyps.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i1); subst.
      inv H.
      inv H6.
      eapply feasible_typs_aux_inv in H0; eauto using list_system_typ_spec.
      destruct H0 as [_ [sz [al [J1 J2]]]].
      rewrite J1. 
      destruct sz as [|sz].
        simpl. 
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i1 i1); 
          subst; try congruence.
        exists 8%nat. exists 1%nat.
        split; auto. split; omega.

        simpl. 
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i1 i1); 
          subst; try congruence.
        exists (S sz). exists al. 
        split; auto. split. omega. apply J2. omega.

      apply IHnts with (P:=P) in H; auto.
      destruct H as [sz [al [J1 J2]]].
      match goal with
      | |- exists _, exists _, 
             lookupAL _ (match ?x with
                        | Some _ => _
                        | None => _
                        end) _ = _ /\ _ => destruct x
      end.
        simpl.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i1); 
          try congruence. 
        rewrite J1.
        exists sz. exists al. split; auto.

        rewrite J1.
        exists sz. exists al. split; auto.
Qed.

Lemma ty_namedts_app: forall s nts2 (Htyps2: ty_namedts s nts2) nts1 
  (Htyps1: ty_namedts s nts1), ty_namedts s (nts1 ++ nts2).
Proof.
  intros. induction Htyps1; intros; auto.
    simpl_env. simpl.
    constructor; auto.
Qed.

Lemma ty_namedts_rev: forall s nts (Htyps: ty_namedts s nts), 
  ty_namedts s (rev nts).
Proof.
  induction nts; simpl; intros; auto.
    inv Htyps.
    apply ty_namedts_app; auto.
      constructor; auto. constructor.
Qed.
  
Lemma feasible_typ_inv : forall t s TD (Htyps: ty_namedts s (snd TD)),
  wf_typ s t -> feasible_typ TD t -> 
  exists sz, exists al,
    getTypeSizeInBits_and_Alignment TD true t = Some (sz, al) /\ 
    (sz > 0)%nat /\ (al > 0)%nat.
Proof.
  intros. inv H0.
  unfold LLVMtd.feasible_typ, getTypeSizeInBits_and_Alignment in *.
  destruct TD.
  eapply feasible_typ_aux_inv; eauto.
  unfold getTypeSizeInBits_and_Alignment_for_namedts.
  eapply feasible_typ_for_namedts_inv; eauto using ty_namedts_rev.
Qed.

Lemma getTypeStoreSize_le_getTypeAllocSize : forall TD t sz1 sz2,
  LLVMtypings.feasible_typ TD t ->
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
  inv J.
  apply feasible_typ_inv' in H; auto.
  destruct H as [sz [al [J1 J2]]].
  rewrite J1 in HeqR. inv HeqR.
  apply RoundUpAlignment_spec; auto.
Qed.  

Lemma feasible_struct_typ_inv' : forall TD ts
  (H:feasible_typs TD ts), LLVMtd.feasible_typ TD (typ_struct ts).
Proof.
  intros. simpl. auto.
Qed.

Lemma typ_eq_list_typ_spec1: forall los (nts:namedts) t1 lt2 (Huniq: uniq nts)
  (H: typ_eq_list_typ nts t1 lt2 = true),
  LLVMtd.feasible_typ (los, nts) t1 ->
  feasible_typs (los, nts) lt2.
Proof.
  intros.
  unfold typ_eq_list_typ in H.
  destruct t1; tinv H.
    destruct (list_typ_dec l0 lt2); inv H.
    apply feasible_struct_typ_inv; auto.

    remember (lookupAL list_typ (rev nts) i0) as R.
    destruct R; tinv H.
    destruct (list_typ_dec l0 lt2); inv H.
    simpl in *.
    remember (lookupAL Prop (feasible_typ_for_namedts los (rev nts)) i0) as R1.
    destruct R1; try solve [inversion H0].
    apply uniq_rev in Huniq.
    eapply feasible_typ_spec1; eauto.
Qed.

Definition getTypeSizeInBits_weaken_prop (t:typ) := forall los nm1 nm2 flag r,
  uniq (nm2++nm1) ->
  _getTypeSizeInBits_and_Alignment los nm1 flag t = Some r ->
  _getTypeSizeInBits_and_Alignment los (nm2++nm1) flag t = Some r.

Definition getListTypeSizeInBits_weaken_prop (lt:list_typ) := 
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

Lemma getTypeSizeInBits_and_Alignment_for_namedts_spec2: forall los i0 r nts2 
  lt2 nts1 nts (Huniq: uniq nts),
  _getTypeSizeInBits_and_Alignment los
     (_getTypeSizeInBits_and_Alignment_for_namedts los nts2 true) true
     (typ_struct lt2) = Some r ->
  nts = nts1 ++ (i0,lt2) :: nts2 ->  
  lookupAL _ 
     (_getTypeSizeInBits_and_Alignment_for_namedts los nts true) i0 = Some r.
Proof.
  induction nts1 as [|[]]; intros; subst; simpl in *.
    match goal with
    | H : ?x = _ |- _ => destruct x; inv H
    end.
      simpl.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i0); 
        try congruence; auto.
     
    inv Huniq.
    match goal with
    | |- lookupAL _
            match ?x with
            | Some _ => _
            | None => _
            end _ = _ => remember x as R; destruct R; simpl in *
    end.
      simpl_env in H4.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i1); subst.
        contradict H4; fsetdec.
        eapply IHnts1 in H; eauto.

      eapply IHnts1 in H; eauto.
Qed.

Lemma getTypeSizeInBits_and_Alignment_spec1: forall (los : layouts) (i0 : id) 
  (nts : namedts) (lt2 : list_typ)
  (HeqR : ret lt2 = lookupAL list_typ nts i0) (Huniq: uniq nts)
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

Lemma typ_eq_list_typ_spec2: forall los (nts:namedts) t1 lt2 (Huniq: uniq nts)
  (H: typ_eq_list_typ nts t1 lt2 = true) (Hwf: wf_targetdata (los, nts)),
  _getTypeSizeInBits_and_Alignment los
    (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
    true (typ_struct lt2) = 
  _getTypeSizeInBits_and_Alignment los
    (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
    true t1.
Proof.
  intros.
  unfold typ_eq_list_typ in H.
  destruct t1; tinv H.
    destruct (list_typ_dec l0 lt2); inv H; auto.

    remember (lookupAL list_typ (rev nts) i0) as R.
    destruct R; tinv H.
    destruct (list_typ_dec l0 lt2); inv H.
    unfold wf_targetdata in Hwf.
    erewrite getTypeSizeInBits_and_Alignment_spec1; 
      try solve [eauto | apply uniq_rev; auto].
      apply Hwf.
      rewrite <- HeqR. congruence.
Qed.

