Require Import syntax.
Require Import infrastructure.
Require Import Memory.
Require Import targetdata.
Require Import genericvalues.
Require Import alist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import typings.
Require Import infrastructure_props.
Require Import targetdata_props.
Require Import typings_props.
Require Import genericvalues_props.
Require Import memory_sim.

Import LLVMinfra.
Import LLVMgv.
Import LLVMtd.
Import LLVMtypings.

(* The file proves the injection between generic values in terms of memory
   injection. *)
Inductive gv_inject (mi: meminj) : GenericValue -> GenericValue -> Prop :=
| gv_inject_nil : gv_inject mi nil nil
| gv_inject_cons : forall v1 m v2 gv1 gv2, 
    MoreMem.val_inject mi v1 v2 -> gv_inject mi gv1 gv2 -> 
    gv_inject mi ((v1,m)::gv1) ((v2,m)::gv2)
.

Hint Constructors gv_inject.
Hint Unfold MoreMem.meminj_no_overlap MoreMem.meminj_zero_delta.

Definition gv_list_inject (mi: meminj) (gvss1 gvss2: list GenericValue): Prop :=
List.Forall2 (gv_inject mi) gvss1 gvss2.

Fixpoint gvs_inject mi gvs1 gvs2 : Prop :=
match (gvs1, gvs2) with
| (nil, nil) => True
| (gv1::gvs1', gv2::gvs2') => gv_inject mi gv1 gv2 /\ gvs_inject mi gvs1' gvs2'
| _ => False
end.

(* The well-formedness of memory injection. *)
Record wf_sb_mi maxb mi Mem1 Mem2 := mk_wf_sb_mi {
  Hno_overlap : MoreMem.meminj_no_overlap mi;
  Hnull : mi Mem.nullptr = Some (Mem.nullptr, 0);
  Hmap1 : forall b, b >= Mem.nextblock Mem1 -> mi b = None;
  Hmap2 : forall b1 b2 delta2, 
    mi b1 = Some (b2, delta2) -> b2 < Mem.nextblock Mem2;
  mi_freeblocks: forall b, ~(Mem.valid_block Mem1 b) -> mi b = None;
  mi_mappedblocks: forall b b' delta, 
    mi b = Some(b', delta) -> Mem.valid_block Mem2 b';
  mi_range_block: MoreMem.meminj_zero_delta mi;
  mi_bounds: forall b b' delta, 
    mi b = Some(b', delta) -> Mem.bounds Mem1 b = Mem.bounds Mem2 b';
  mi_globals : forall b, b <= maxb -> mi b = Some (b, 0)
  }.

(* Well-formed globals *)
Fixpoint wf_global (maxb:Values.block) (gv:GenericValue) 
  : Prop :=
match gv with
| nil => True
| (Vptr b _,_)::gv' => b <= maxb /\ wf_global maxb gv'
| _::gv' => wf_global maxb gv'
end.

Fixpoint wf_globals maxb (gl:GVMap) : Prop :=
match gl with
| nil => True
| (_,gv)::gl' => wf_global maxb gv /\ wf_globals maxb gl'
end.

(* Properties of gv_inject *)
Lemma gv_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  gv_inject f1 v v' ->
  gv_inject f2 v v'.
Proof.
  intros.
  induction H0; eauto using val_list_inject_incr.
Qed.

Lemma gv_inject_app : forall mi gv1 gv1' gv2 gv2',
  gv_inject mi gv1 gv2 ->
  gv_inject mi gv1' gv2' ->
  gv_inject mi (gv1++gv1') (gv2++gv2').
Proof.
  intros.
  induction H; simpl; eauto.
Qed.

Ltac tinv H := try solve [inv H].
  
Lemma gv_inject__repeatGV : forall mi gv1 gv2 n,
  gv_inject mi gv1 gv2 -> 
  gv_inject mi (repeatGV gv1 n) (repeatGV gv2 n).
Proof.
  induction n; intros; simpl; eauto using gv_inject_app.
Qed.

Lemma gv_inject_uninits : forall mi n, gv_inject mi (uninits n) (uninits n).
Proof.
  unfold uninits.
  induction n; intros; simpl; eauto using gv_inject_app.
Qed.

Lemma gv_inject__val_inject : forall mi gv1 gv2 TD,
  gv_inject mi gv1 gv2 ->
  exists v1, exists v2,
    GV2val TD gv1 = Some v1 /\ GV2val TD gv2 = Some v2 /\ 
    MoreMem.val_inject mi v1 v2.
Proof.
  intros.
  unfold GV2val in *.
  destruct gv1; inv H; subst. eauto.
    destruct gv1; inv H4; subst; eauto.
Qed.

Lemma gv_inject_mc2undefs: forall mi mcs,
  gv_inject mi (mc2undefs mcs) (mc2undefs mcs).
Proof.
  unfold mc2undefs.
  induction mcs; simpl; auto.
Qed.

Lemma gv_inject_gundef : forall mi TD t gv, gundef TD t = Some gv -> gv_inject mi gv gv.
Proof.
  intros. unfold gundef in H. 
  inv_mbind. apply gv_inject_mc2undefs.
Qed.

Lemma gv_inject_nptr_val_refl : forall TD v mi m,
  (forall b ofs, v <> Vptr b ofs) ->
  gv_inject mi (val2GV TD v m) (val2GV TD v m).
Proof.
  intros. unfold val2GV.
  destruct v; auto. 
    assert (J:=@H b i0). contradict J; auto.
Qed.

Lemma gv_inject_id__eq: forall gv1 gv2, 
  gv_inject inject_id gv1 gv2 -> gv1 = gv2.
Proof.
  induction 1; auto.
    inv H; auto.
    inv H1. rewrite Int.add_zero; auto.
Qed.

Lemma gv_inject_id__refl: forall gvs, gv_inject inject_id gvs gvs.
Proof.
  induction gvs as [|[]]; auto.
    constructor; auto.
    destruct v; try constructor.
      econstructor.
        unfold inject_id. eauto.
        rewrite Int.add_zero; auto.
Qed.

Lemma gv_inject_null_refl : forall mgb mi M1 M2,
  wf_sb_mi mgb mi M1 M2 -> gv_inject mi null null.
Proof.
  intros. inv H. unfold null. eauto.
Qed.

Lemma gv_inject__same_size : forall mi gv1 gv2,
  gv_inject mi gv1 gv2 ->
  sizeGenericValue gv1 = sizeGenericValue gv2.
Proof.
  intros mi gv1 gv2 Hinj.
  induction Hinj; simpl; auto.
Qed.

Lemma gv_inject_ptr_inv : forall mi b ofs gv' cm,
  gv_inject mi ((Vptr b ofs,cm)::nil) gv' ->
  exists b', exists ofs',
    gv' = (Vptr b' ofs', cm)::nil /\
    val_inject mi (Vptr b ofs) (Vptr b' ofs').
Proof.
  intros mi b ofs gv' cm J .
  destruct gv'; inv J.
    inv H5. inv H1.
    exists b2. exists (Int.add 31 ofs (Int.repr 31 delta)).
    split; eauto.
Qed.

Lemma gv_inject_length_eq : forall mi gv1 gv2,
  gv_inject mi gv1 gv2 -> length gv1 = length gv2.
Proof.
  induction 1; intros; simpl; auto.
Qed.

Lemma simulation__gv_chunks_match_typb : forall mi TD gv gv' t,
  gv_inject mi gv gv' ->
  gv_chunks_match_typb TD gv t = gv_chunks_match_typb TD gv' t.
Proof.
  unfold gv_chunks_match_typb.
  intros.
  destruct (flatten_typ TD t); auto.
  generalize dependent l0.
  induction H; simpl; auto.
    destruct l0; auto.
    apply MoreMem.val_inject__has_chunkb with (m:=m) in H; auto.
      congruence.
Qed.

(* Zero constants inject to themselves. *)
Definition zeroconst2GV_aux__gv_inject_refl_prop S TD t :=
  wf_styp S TD t ->
  forall los nts acc (Heq: TD = (los, nts)) nts' 
  (Hsub:exists nts0, nts'=nts0++nts) (Huniq: uniq nts')
  maxb mi Mem1 Mem2 gv (Hwfsim: wf_sb_mi maxb mi Mem1 Mem2)
  (Hnc: forall id5 gv5, 
          lookupAL _ nts id5 <> None ->
          lookupAL _ acc id5 = Some (Some gv5) ->
          gv_inject mi gv5 gv5)
  (Hz: zeroconst2GV_aux (los, nts') acc t = Some gv),
  gv_inject mi gv gv.
  
Definition zeroconsts2GV_aux__gv_inject_refl_prop sdt :=
  wf_styp_list sdt ->
  let 'lsdt := sdt in
  let '(lsd, lt) := split lsdt in
  forall S TD los nts acc (Heq: TD = (los, nts)) nts' 
  (Hsub:exists nts0, nts'=nts0++nts) (Huniq: uniq nts') maxb mi Mem1 Mem2 gv 
  (Hnc: forall id5 gv5, 
          lookupAL _ nts id5 <> None ->
          lookupAL _ acc id5 = Some (Some gv5) ->
          gv_inject mi gv5 gv5)
  (Hz: zeroconsts2GV_aux (los,nts') acc lt = Some gv)
  (Heq': eq_system_targetdata S TD lsd)
  (Hwfsim: wf_sb_mi maxb mi Mem1 Mem2),
  gv_inject mi gv gv.

Lemma zeroconst2GV_aux__gv_inject_refl_mutrec :
  (forall S TD t, zeroconst2GV_aux__gv_inject_refl_prop S TD t) /\
  (forall sdt, zeroconsts2GV_aux__gv_inject_refl_prop sdt).
Proof.
  (wfstyp_cases (apply wf_styp_mutind; 
    unfold zeroconst2GV_aux__gv_inject_refl_prop, 
           zeroconsts2GV_aux__gv_inject_refl_prop) Case);
    intros; simpl in *; subst; uniq_result; 
    try solve [constructor; auto | 
               unfold null; inv Hwfsim; eauto].

Case "wf_styp_structure".
  simpl_split lsd lt.
  assert (lt = typ_list) as EQ1. 
    eapply make_list_typ_spec2; eauto.
  subst.
  assert (eq_system_targetdata system5 (los, nts) lsd) as EQ2.
    eapply wf_styp__feasible_typ_aux_mutrec_struct; eauto.
  subst. 
  inv_mbind. symmetry_ctx.
  eapply H1 in HeqR0; eauto 2.
  destruct g as [|]; uniq_result; try solve [auto using gv_inject_uninits].
  
Case "wf_styp_array".
  destruct sz5 as [|s]; try solve [uniq_result; auto using gv_inject_uninits].
  inv_mbind. symmetry_ctx.
  eapply_clear H0 in HeqR; eauto 1.
  apply gv_inject_app; auto.
    apply gv_inject_app; auto.
      apply gv_inject_uninits.
  apply gv_inject__repeatGV.
    apply gv_inject_app; auto.
      apply gv_inject_uninits.

Case "wf_styp_namedt".
  inv_mbind. eauto.

Case "wf_styp_nil".
  intros. uniq_result. auto.
 
Case "wf_styp_cons".
  simpl_split lsd lt. simpl.
  intros. subst.
  apply eq_system_targetdata_cons_inv in Heq'. 
  destruct Heq' as [H4 [EQ1 EQ2]]; subst.
  inv_mbind. symmetry_ctx.
  eapply H0 in HeqR1; eauto 1. clear H0.
  eapply H2 in HeqR0; eauto 1. clear H2.
  apply gv_inject_app; auto.
  apply gv_inject_app; auto.
    apply gv_inject_uninits.
Qed.

Lemma noncycled__gv_inject_refl: forall S los nts maxb mi Mem1 Mem2 
  (H: noncycled S los nts) (Hwfsim: wf_sb_mi maxb mi Mem1 Mem2) (Huniq: uniq nts)
  id5 lt nts2 nts1 (EQ: nts = nts1 ++ (id5,lt) :: nts2) nts' (Huniq': uniq nts') 
  (Hsub: exists nts0, nts'=nts0++nts) gv
  (Hz: zeroconst2GV_aux (los, nts')
         (zeroconst2GV_for_namedts (los, nts') los nts2) (typ_struct lt) = 
           Some gv),
  gv_inject mi gv gv.
Proof.
  induction 1; simpl; intros; subst.
    symmetry in EQ.    
    apply app_eq_nil in EQ.
    destruct EQ as [_ EQ].
    congruence.

    inv Huniq.
    destruct nts1 as [|[]]; inv EQ.
      destruct zeroconst2GV_aux__gv_inject_refl_mutrec as [J _].
      eapply J in H0; eauto.
      assert (exists nts0 : list namedt, nts' = nts0 ++ nts2) as G.
        destruct Hsub as [nts0 Hsub]; subst. 
        exists (nts0 ++ [(id0, lt)]). simpl_env. auto.
      eapply H0 in Hwfsim; eauto 1.  
      intros id5 gv5 H1 H2.
      apply lookupAL_middle_inv' in H1.
      destruct H1 as [l0 [l1 [l2 HeqR]]].
      assert (J':=HeqR). subst.
      eapply IHnoncycled with (nts':=nts') in J'; eauto.
        eapply zeroconst2GV_for_namedts_spec1 in H2; eauto.
            
      assert (nts1 ++ (id0, lt) :: nts2 = nts1 ++ (id0, lt) :: nts2) as EQ. auto.
      eapply IHnoncycled with (nts':=nts') in EQ; eauto.
        destruct Hsub as [nts0 Hsub]; subst. 
        exists (nts0 ++ [(i0, l0)]). simpl_env. auto.
Qed.

Lemma zeroconst2GV__gv_inject_refl : forall maxb mi Mem1 Mem2 gv S td t
  (Hwft: wf_typ S td t), 
  wf_sb_mi maxb mi Mem1 Mem2 ->
  zeroconst2GV td t = Some gv ->
  gv_inject mi gv gv.
Proof. 
  intros. destruct td as [los nts].
  unfold zeroconst2GV in *. inv Hwft.
  destruct zeroconst2GV_aux__gv_inject_refl_mutrec as [J' _].
  assert (exists nts0 : list namedt, nts = nts0 ++ nts) as G'.
    exists nil. auto.
  eapply J'; eauto.
  intros id5 gv5 J5 J6.
  apply lookupAL_middle_inv' in J5.
  destruct J5 as [lt5 [l1 [l2 HeqR]]]. subst.
  eapply noncycled__gv_inject_refl
    with (nts':=l1 ++ (id5, lt5) :: l2) in H3; eauto.
    eapply zeroconst2GV_for_namedts_spec1 in J6; eauto.
Qed.

(* Globals inject to themselves. *)
Lemma global_gv_inject_refl_aux : forall maxb mi Mem1 Mem2 gv,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_global maxb gv ->
  gv_inject mi gv gv.
Proof.
  induction gv; intros; simpl; auto.
    destruct a.
    destruct v; simpl in *; try solve 
        [assert (J:=@IHgv H H0); eauto].

        destruct H0 as [H1 H2].
        assert (J:=(@IHgv H H2)).
        inversion H.
        apply mi_globals0 in H1.
        apply gv_inject_cons; auto.
          apply MoreMem.val_inject_ptr with (delta:=0); auto.
            rewrite Int.add_zero; auto.
Qed.

Lemma wf_globals__wf_global : forall mgb gl gv i0,
  wf_globals mgb gl ->
  ret gv = lookupAL GenericValue gl i0 ->
  wf_global mgb gv.
Proof.
  induction gl; intros.
    inversion H0.

    destruct a. simpl in *.
    destruct H as [J1 J2].
    destruct (i0 == i1); subst; eauto.
      inv H0; auto.
Qed.      

Lemma global_gv_inject_refl : forall maxb mi Mem1 Mem2 gl i0 gv,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_globals maxb gl ->
  lookupAL _ gl i0 = Some gv ->
  gv_inject mi gv gv.
Proof.
  intros. 
  eapply global_gv_inject_refl_aux; eauto.
    eapply wf_globals__wf_global; eauto.
Qed.

(* Generic-value operations preserve gv_inject. *)
Lemma simulation__mtrunc_aux : forall mi TD top t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mtrunc TD top t1 t2 gv1 = Some gv2 ->
  (mtrunc TD top t1 t2 gv1 = mtrunc TD top t1 t2 gv1' /\
    gv_inject mi gv2 gv2) \/
  exists gv2',
    mtrunc TD top t1 t2 gv1' = Some gv2' /\
    gv_inject mi gv2 gv2'.  
Proof.
  intros.
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v2 [J1 [J2 J3]]]].
  unfold mtrunc in *.
  rewrite J1. rewrite J2. rewrite J1 in H0.
  inv J3; auto.
    destruct_typ t1; destruct_typ t2; inv H0; try solve [
      eauto using gv_inject_gundef |
      unfold val2GV; simpl; destruct (le_lt_dec wz (s1-1)); auto
    ].

    destruct_typ t1; destruct_typ t2; inv H0; eauto using gv_inject_gundef.
      match goal with
      | H: context [floating_point_order ?f1 ?f0] |- _ => 
        destruct (floating_point_order f1 f0); inv H; 
           simpl; eauto using gv_inject_gundef;
        destruct f0; inv H0; unfold val2GV; simpl; eauto using gv_inject_gundef
      end.
 
    inv H0. eauto using gv_inject_gundef.
    inv H0. eauto using gv_inject_gundef.

    right. rewrite H0. eauto using gv_inject_gundef.
Qed.

Lemma simulation__mtrunc : forall mi TD top t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mtrunc TD top t1 t2 gv1 = Some gv2 ->
  exists gv2',
    mtrunc TD top t1 t2 gv1' = Some gv2' /\
    gv_inject mi gv2 gv2'.
Proof.
  intros.
  assert (J:=H0).
  eapply simulation__mtrunc_aux in H0; eauto.
  destruct H0 as [[H1 H2] | H0]; eauto.
    rewrite <- H1.
    exists gv2. split; auto.
Qed.

Lemma simulation__mext_aux : forall mi TD eop t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mext TD eop t1 t2 gv1 = Some gv2 ->
  (mext TD eop t1 t2 gv1 = mext TD eop t1 t2 gv1' /\
    gv_inject mi gv2 gv2) \/
  exists gv2',
    mext TD eop t1 t2 gv1' = Some gv2' /\
    gv_inject mi gv2 gv2'.  
Proof.
  intros. assert (J0:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v2 [J1 [J2 J3]]]].
  unfold mext in *.
  rewrite J1. rewrite J2. rewrite J1 in H0.
  inv J3; try solve [
    auto |
    destruct t1; destruct t2; inv H0; simpl; eauto using gv_inject_gundef;
      match goal with
      | H: context [floating_point_order ?f ?f0] |- _ => 
        destruct (floating_point_order f f0); inv H; eauto using gv_inject_gundef
      end
    ].

    destruct t1; destruct t2; inv H0; simpl; eauto using gv_inject_gundef.
      destruct eop; inv H1; 
        try solve [unfold val2GV; simpl; eauto using gv_inject_gundef].
      match goal with
      | H: context [floating_point_order ?f1 ?f0] |- _ => 
         destruct (floating_point_order f1 f0); inv H; eauto using gv_inject_gundef
      end.

    destruct t1; destruct t2; inv H0; simpl; eauto using gv_inject_gundef.
      match goal with
      | H: context [floating_point_order ?f0 ?f1] |- _ => 
        destruct (floating_point_order f0 f1); inv H1; simpl; 
          eauto using gv_inject_gundef;
        destruct eop; inv H0; simpl; eauto using gv_inject_gundef;
        destruct f1; inv H1; simpl; unfold val2GV; auto
      end.
Qed.

Lemma simulation__mext : forall mi TD eop t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mext TD eop t1 t2 gv1 = Some gv2 ->
  exists gv2',
    mext TD eop t1 t2 gv1' = Some gv2' /\
    gv_inject mi gv2 gv2'.
Proof.
  intros.
  assert (J:=H0).
  eapply simulation__mext_aux in H0; eauto.
  destruct H0 as [[H1 H2] | H0]; eauto.
    rewrite <- H1.
    exists gv2. split; auto.
Qed.

Lemma simulation__mbop_aux : forall mi TD op bsz gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mbop TD op bsz gv1 gv2 = Some gv3 ->
  (mbop TD op bsz gv1 gv2 = mbop TD op bsz gv1' gv2' /\
    gv_inject mi gv3 gv3) \/
  exists gv3',
    mbop TD op bsz gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.  
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  unfold mbop in *.
  rewrite J1. rewrite J2. rewrite J1'. rewrite J2'.  
  rewrite J1 in H1. rewrite J1' in H1. 
  inv J3; try solve [inv H1; eauto using gv_inject_gundef].
    inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef].
    destruct (eq_nat_dec (wz + 1) (Size.to_nat bsz)); 
       try solve [inv H1; eauto using gv_inject_gundef].
    destruct op; inv H1; 
       try (left; split; auto; apply gv_inject_nptr_val_refl; auto).
       apply add_isnt_ptr.
       apply sub_isnt_ptr.
       apply mul_isnt_ptr.
       apply divu_isnt_ptr.
       apply divs_isnt_ptr.
       apply modu_isnt_ptr.
       apply mods_isnt_ptr.
       apply shl_isnt_ptr.
       apply shrx_isnt_ptr.
       apply shr_isnt_ptr.
       apply and_isnt_ptr.
       apply or_isnt_ptr.
       apply xor_isnt_ptr.
Qed.

Lemma simulation__mbop : forall mi TD op bsz gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mbop TD op bsz gv1 gv2 = Some gv3 ->
  exists gv3',
    mbop TD op bsz gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Proof.
  intros.
  assert (J:=H1).
  eapply simulation__mbop_aux in H1; eauto.
  destruct H1 as [[H1 H2] | H1]; eauto.
    rewrite <- H1.
    exists gv3. split; auto.
Qed.

Lemma simulation__mfbop_aux : forall mi TD op fp gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfbop TD op fp gv1 gv2 = Some gv3 ->
  (mfbop TD op fp gv1 gv2 = mfbop TD op fp gv1' gv2' /\
    gv_inject mi gv3 gv3) \/
  exists gv3',
    mfbop TD op fp gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.  
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  unfold mfbop in *.
  rewrite J1. rewrite J2. rewrite J1'. rewrite J2'.  
  rewrite J1 in H1. rewrite J1' in H1. 
  inv J3; try solve [inv H1; eauto using gv_inject_gundef].
    inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef].
    destruct fp; inv H1; try solve [eauto using gv_inject_gundef].
       destruct op; 
          try (left; split; auto; apply gv_inject_nptr_val_refl; 
            try solve [auto | intro; simpl; congruence]).

       destruct op; 
          try (left; split; auto; apply gv_inject_nptr_val_refl; 
            try solve [auto | intro; congruence]).
Qed.

Lemma simulation__mfbop : forall mi TD op fp gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfbop TD op fp gv1 gv2 = Some gv3 ->
  exists gv3',
    mfbop TD op fp gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Proof.
  intros.
  assert (J:=H1).
  eapply simulation__mfbop_aux in H1; eauto.
  destruct H1 as [[H1 H2] | H1]; eauto.
    rewrite <- H1.
    exists gv3. split; auto.
Qed.

Lemma simulation__mcast_aux_helper : forall TD gv1' wz i0 mi gv2
  (J2 : GV2val TD gv1' = ret Vint wz i0)
  (J : gv_inject mi gv2 gv1')
  (J1 : GV2val TD gv2 = ret Vint wz i0),
   ret gv2 = ret gv1' /\ gv_inject mi gv2 gv2 \/
   (exists gv2' : GenericValue, ret gv1' = ret gv2' /\ gv_inject mi gv2 gv2').
Proof. intros.
        unfold GV2val in *.
        destruct gv1'; tinv J2.
        destruct p; tinv J2.
        destruct gv1'; tinv J2.
        destruct gv2; tinv J1.
        destruct p; tinv J1.
        destruct gv2; inv J1.
        right. exists ((v, m) :: nil). 
        simpl. auto.
Qed.

Lemma simulation__mcast_aux : forall mi TD op t1 t2 gv1 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mcast TD op t1 t2 gv1 = Some gv2 ->
  (mcast TD op t1 t2 gv1 = mcast TD op t1 t2 gv1' /\
    gv_inject mi gv2 gv2) \/
  exists gv2',
    mcast TD op t1 t2 gv1' = Some gv2' /\
    gv_inject mi gv2 gv2'.  
Proof.
  intros.  assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  unfold mcast, mbitcast in *.
  inv J3; try solve [
    destruct op; try solve [
      abstract (destruct t1; try solve [
        inv H0 |
        destruct t2; inv H0; eauto using gv_inject_gundef |
        destruct t2; inv H0; eauto using simulation__mcast_aux_helper
      ])
    ]
  ].
Qed.

Lemma simulation__mcast : forall mi TD op t1 gv1 gv1' t2 gv2,
  gv_inject mi gv1 gv1' ->
  mcast TD op t1 t2 gv1 = Some gv2 ->
  exists gv2',
    mcast TD op t1 t2 gv1' = Some gv2' /\
    gv_inject mi gv2 gv2'.
Proof.
  intros.
  assert (J:=H0).
  eapply simulation__mcast_aux in H0; eauto.
  destruct H0 as [[H1 H2] | H1]; eauto.
    rewrite <- H1.
    exists gv2. split; auto.
Qed.

Lemma simulation__micmp_aux : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  micmp TD c t gv1 gv2 = Some gv3 ->
  (micmp TD c t gv1 gv2 = micmp TD c t gv1' gv2' /\
    gv_inject mi gv3 gv3) \/
  exists gv3',
    micmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.  
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  unfold micmp, micmp_int in *.
  rewrite J1. rewrite J2. rewrite J1'. rewrite J2'.  
  rewrite J1 in H1. rewrite J1' in H1. 
  inv J3; try solve [inv H1; eauto 3 using gv_inject_gundef].
    inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef];
    destruct t; try solve [inv H1; eauto using gv_inject_gundef].
      destruct c; inv H1; 
        try (left; split; auto; 
          apply gv_inject_nptr_val_refl; try solve 
            [auto | apply cmp_isnt_ptr | apply cmpu_isnt_ptr]).
    destruct t; try solve [inv H1; eauto using gv_inject_gundef].
    destruct t; try solve [inv H1; eauto using gv_inject_gundef].
    destruct t; try solve [inv H1; eauto using gv_inject_gundef].
    destruct t; try solve [inv H1; eauto using gv_inject_gundef].
Qed.

Lemma simulation__micmp : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  micmp TD c t gv1 gv2 = Some gv3 ->
  exists gv3',
    micmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Proof.
  intros.
  assert (J:=H1).
  eapply simulation__micmp_aux in H1; eauto.
  destruct H1 as [[H1 H2] | H1]; eauto.
    rewrite <- H1.
    exists gv3. split; auto.
Qed.

Lemma simulation__mfcmp_aux : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfcmp TD c t gv1 gv2 = Some gv3 ->
  (mfcmp TD c t gv1 gv2 = mfcmp TD c t gv1' gv2' /\
    gv_inject mi gv3 gv3) \/
  exists gv3',
    mfcmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.  
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  unfold mfcmp in *.
  rewrite J1. rewrite J2. rewrite J1'. rewrite J2'.  
  rewrite J1 in H1. rewrite J1' in H1. 
  inv J3; try solve [inv H1; eauto using gv_inject_gundef].
    inv J3'; try solve [auto | inv H1; eauto using gv_inject_gundef];
    destruct t; try solve [inv H1; eauto using gv_inject_gundef].
      destruct c; inv H1; 
        try solve [
          eauto using gv_inject_gundef |
          (left; split; auto; 
          apply gv_inject_nptr_val_refl; try solve 
            [auto | apply val_of_bool_isnt_ptr | apply Vfalse_isnt_ptr | 
             apply Vtrue_isnt_ptr])
        ].
      destruct c; inv H1; 
        try solve [
          eauto using gv_inject_gundef |
          (left; split; auto; 
          apply gv_inject_nptr_val_refl; try solve 
            [auto | apply val_of_bool_isnt_ptr | apply Vfalse_isnt_ptr | 
             apply Vtrue_isnt_ptr])
        ].
Qed.

Lemma simulation__mfcmp : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfcmp TD c t gv1 gv2 = Some gv3 ->
  exists gv3',
    mfcmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Proof.
  intros.
  assert (J:=H1).
  eapply simulation__mfcmp_aux in H1; eauto.
  destruct H1 as [[H1 H2] | H1]; eauto.
    rewrite <- H1.
    exists gv3. split; auto.
Qed.

Lemma simulation__GV2ptr : forall mi TD gv1 gv1' v,
  gv_inject mi gv1 gv1' ->
  GV2ptr TD (getPointerSize TD) gv1 = Some v ->
  exists v',
    GV2ptr TD (getPointerSize TD) gv1' = Some v' /\
    MoreMem.val_inject mi v v'.
Proof.
  intros.
  unfold GV2ptr in *.
  destruct gv1; tinv H0.
  destruct p; tinv H0.
  destruct v0; tinv H0.
  destruct gv1; inv H0.
  inv H. inv H5. inv H4. eauto.
Qed.

Lemma simulation__mgep : forall mi TD v v' v0 t0 l1,
  MoreMem.val_inject mi v v' ->
  mgep TD t0 v l1 = Some v0 ->
  exists v0',
    mgep TD t0 v' l1 = Some v0' /\
    MoreMem.val_inject mi v0 v0'.
Proof.
  intros.
  unfold mgep in *.
  destruct v; tinv H0.
  destruct l1; tinv H0.
  inv H.
  destruct (mgetoffset TD (typ_array 0%nat t0) (z :: l1)) as [[i1 ?]|] ; tinv H0.
  inv H0. 
  exists (Vptr b2 (Int.add 31 (Int.add 31 i0 (Int.repr 31 delta)) (Int.repr 31 i1))).
  split; auto.
    eapply MoreMem.val_inject_ptr; eauto.
      rewrite Int.add_assoc.
      assert (Int.add 31 (Int.repr 31 delta) (Int.repr 31 i1) = 
              Int.add 31 (Int.repr 31 i1) (Int.repr 31 delta)) as EQ.
        rewrite Int.add_commut. auto.
      rewrite EQ.
      rewrite Int.add_assoc. auto.
Qed.

Lemma simulation__splitGenericValue_some : forall mi gv gv' z gvl gvr,
  gv_inject mi gv gv' ->
  splitGenericValue gv z = Some (gvl, gvr) ->
  exists gvl', exists gvr', 
    splitGenericValue gv' z = Some (gvl', gvr') /\
    gv_inject mi gvl gvl' /\ gv_inject mi gvr gvr'.
Proof.
  induction gv; simpl; intros gv' z gvl gvr H H0.
    inv H.
    simpl.
    destruct (zeq z 0); inv H0. 
      exists nil. exists nil. auto.
      destruct (zlt z 0); inv H1.

    inv H.
    simpl.
    destruct (zeq z 0); inv H0. 
      exists nil. exists ((v2, m)::gv2). 
      split; auto.
    destruct (zlt z 0); inv H1.
    remember (splitGenericValue gv (z - size_chunk m)) as R.
    destruct R as [[gvl' gvr']|]; inv H0.
    symmetry in HeqR.
    eapply IHgv in HeqR; eauto.
    destruct HeqR as [gvl'0 [gvr' [J4 [J5 J6]]]].
    rewrite J4.     
    exists ((v2, m) :: gvl'0). exists gvr'. 
    split; auto.
Qed.
   
Lemma simulation__splitGenericValue_none : forall mi gv gv' z,
  gv_inject mi gv gv' ->
  splitGenericValue gv z = None ->
  splitGenericValue gv' z = None.
Proof.
  induction gv; simpl; intros gv' z H H0.
    inv H.
    simpl.
    destruct (zeq z 0); inv H0. 
    destruct (zlt z 0); inv H1; auto.

    inv H. 
    simpl.
    destruct (zeq z 0); inv H0. 
    destruct (zlt z 0); inv H1; auto.
    remember (splitGenericValue gv (z - size_chunk m)) as R.
    destruct R as [[gvl' gvr']|]; inv H0.
    symmetry in HeqR.
    eapply IHgv in HeqR; eauto.
    rewrite HeqR; auto.
Qed.

Lemma simulation__extractGenericValue : forall mi gv1 gv1' TD t1 l0 gv,
  gv_inject mi gv1 gv1' ->
  extractGenericValue TD t1 gv1 l0 = Some gv ->
  exists gv',
    extractGenericValue TD t1 gv1' l0 = Some gv' /\
    gv_inject mi gv gv'.
Proof.
  intros mi gv1 gv1' TD t1 l0 gv H H0.
  unfold extractGenericValue in *.
  destruct (intConsts2Nats TD l0); inv H0; 
    try solve [exists (uninits 1); auto using gv_inject_uninits].
  destruct (mgetoffset TD t1 l1) as [[o t']|]; inv H2;
    try solve [exists (uninits 1); auto using gv_inject_uninits].
  unfold mget in *. 
  destruct (getTypeStoreSize TD t'); inv H1; eauto using gv_inject_gundef.
  remember (splitGenericValue gv1 o) as R.
  destruct R as [[gvl gvr]|].
    symmetry in HeqR.
    eapply simulation__splitGenericValue_some in HeqR; eauto.      
    destruct HeqR as [gvl' [gvr' [J1 [J2 J3]]]].
    simpl. rewrite J1.
    remember (splitGenericValue gvr (Z_of_nat n)) as R1.
    destruct R1 as [[gvrl gvrr]|]; inv H2.
      symmetry in HeqR1.
      eapply simulation__splitGenericValue_some in HeqR1; eauto.      
      destruct HeqR1 as [gvrl' [gvrr' [J1' [J2' J3']]]].
      simpl. rewrite J1'. 
      erewrite <- simulation__gv_chunks_match_typb; eauto.
      destruct_if; eauto using gv_inject_gundef.

      symmetry in HeqR1.
      eapply simulation__splitGenericValue_none in HeqR1; eauto.      
      rewrite HeqR1. rewrite H1. eauto using gv_inject_gundef.

    simpl.
    symmetry in HeqR.
    eapply simulation__splitGenericValue_none in HeqR; eauto.      
    rewrite HeqR. rewrite H2. eauto using gv_inject_gundef.
Qed.

Lemma simulation__insertGenericValue: forall mi gv1 gv1' TD t1 l0 gv t2 gv2 gv2',
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  insertGenericValue TD t1 gv1 l0 t2 gv2 = Some gv ->
  exists gv',
    insertGenericValue TD t1 gv1' l0 t2 gv2' = Some gv' /\
    gv_inject mi gv gv'.
Proof.
  intros mi gv1 gv1' TD t1 l0 gv t2 gv2 gv2' H H0 H1.
  unfold insertGenericValue in *.
  destruct (intConsts2Nats TD l0); inv H1; eauto using gv_inject_gundef.
  destruct (mgetoffset TD t1 l1) as [[o ?]|]; inv H3; eauto using gv_inject_gundef.
  unfold mset in *. 
  destruct (getTypeStoreSize TD t2); inv H2; eauto using gv_inject_gundef.
  assert (J:=@gv_inject_length_eq mi gv2 gv2' H0). 
  rewrite <- J. simpl.
  destruct (n =n= length gv2); subst; inv H3; eauto using gv_inject_gundef.
  remember (splitGenericValue gv1 o) as R.
  destruct R as [[gvl gvr]|].
    symmetry in HeqR.
    eapply simulation__splitGenericValue_some in HeqR; eauto.      
    destruct HeqR as [gvl' [gvr' [J1 [J2 J3]]]].
    simpl. rewrite J1.
    remember (splitGenericValue gvr (Z_of_nat n)) as R1.
    destruct R1 as [[gvrl gvrr]|]; inv H2.
      symmetry in HeqR1.
      eapply simulation__splitGenericValue_some in HeqR1; eauto.      
      destruct HeqR1 as [gvrl' [gvrr' [J1' [J2' J3']]]].
      simpl. rewrite J1'. 
      erewrite <- simulation__gv_chunks_match_typb; eauto.
      destruct_if; eauto using gv_inject_gundef.
      exists (gvl' ++ gv2' ++ gvrr').
      split; auto.
        apply gv_inject_app; auto.
        apply gv_inject_app; auto.

      symmetry in HeqR1.
      eapply simulation__splitGenericValue_none in HeqR1; eauto.      
      rewrite HeqR1. eauto using gv_inject_gundef.
    symmetry in HeqR.
    eapply simulation__splitGenericValue_none in HeqR; eauto.      
    rewrite HeqR. rewrite H2. eauto using gv_inject_gundef.
Qed.

Lemma simulation__mtrunc_refl : forall mi TD top t1 gv1 t2 gv2,
  gv_inject mi gv1 gv1 ->
  mtrunc TD top t1 t2 gv1 = Some gv2 ->
  gv_inject mi gv2 gv2.
Proof.
  intros.
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v2 [J1 [J2 J3]]]].
  unfold mtrunc in *.
  rewrite J1 in H0. 
  rewrite J1 in J2. inv J2.
  destruct v2; try (inv J3); try solve [inv H0; eauto using gv_inject_gundef].
    destruct_typ t1; try solve [
      inv H0; eauto using gv_inject_gundef |
      destruct_typ t2; try solve 
        [inv H0; eauto using gv_inject_gundef | 
         inv H0; destruct (le_lt_dec wz (s1-1)); unfold val2GV; simpl; auto]
    ].

    destruct_typ t1; try solve [
      inv H0; eauto using gv_inject_gundef |
      destruct_typ t2; try solve [
        inv H0; eauto using gv_inject_gundef |
        match goal with
        | H: context [floating_point_order ?f1 ?f0] |- _ =>
          destruct (floating_point_order f1 f0); try solve [
            destruct f0; try solve 
              [inv H0; unfold val2GV; simpl; eauto using gv_inject_gundef] |
            inv H0; eauto using gv_inject_gundef
          ]
        end
      ]
    ].
Qed.

Lemma simulation__mext_refl : forall mi TD eop t1 gv1 t2 gv2,
  gv_inject mi gv1 gv1 ->
  mext TD eop t1 t2 gv1 = Some gv2 ->
  gv_inject mi gv2 gv2.
Proof.
  intros. assert (J0:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v2 [J1 [J2 J3]]]].
  unfold mext in *.
  rewrite J1 in H0.
  rewrite J1 in J2. inv J2.
  destruct t1; destruct t2; inv H0; eauto using gv_inject_gundef.
    destruct v2; inv H1; eauto using gv_inject_gundef.
    destruct eop; inv H0; try solve [
      eauto using gv_inject_gundef | unfold val2GV; simpl; auto].
    match goal with
    | H: context [floating_point_order ?f ?f0] |- _ =>
      destruct (floating_point_order f f0); inv H1; try solve [
        eauto using gv_inject_gundef | unfold val2GV; simpl; auto]
    end.
    destruct v2; inv H0; eauto using gv_inject_gundef.
    destruct eop; inv H1; eauto using gv_inject_gundef.
    match goal with
      | f : floating_point, H : ?t = ret _ |- _ =>
        match t with
          | context[f] =>
            destruct f; inv H0; unfold val2GV; auto            
        end
    end.
Qed.

Lemma simulation__mbop_refl : forall mi TD op bsz gv1 gv2 gv3,
  gv_inject mi gv1 gv1 ->
  gv_inject mi gv2 gv2 ->
  mbop TD op bsz gv1 gv2 = Some gv3 ->
  gv_inject mi gv3 gv3.
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  rewrite J1 in J2. inv J2.
  rewrite J1' in J2'. inv J2'.
  unfold mbop in *.
  rewrite J1 in H1. rewrite J1' in H1. 
  destruct v1';
    try solve [inv H1; eauto using gv_inject_gundef].
  destruct v2';
    try solve [inv H1; eauto using gv_inject_gundef].
  destruct (eq_nat_dec (wz + 1) (Size.to_nat bsz)); 
     try solve [inv H1; eauto using gv_inject_gundef].
  destruct op; inv H1; try (apply gv_inject_nptr_val_refl; auto).
       apply add_isnt_ptr.
       apply sub_isnt_ptr.
       apply mul_isnt_ptr.
       apply divu_isnt_ptr.
       apply divs_isnt_ptr.
       apply modu_isnt_ptr.
       apply mods_isnt_ptr.
       apply shl_isnt_ptr.
       apply shrx_isnt_ptr.
       apply shr_isnt_ptr.
       apply and_isnt_ptr.
       apply or_isnt_ptr.
       apply xor_isnt_ptr.
Qed.

Lemma simulation__mfbop_refl : forall mi TD op fp gv1 gv2 gv3,
  gv_inject mi gv1 gv1 ->
  gv_inject mi gv2 gv2 ->
  mfbop TD op fp gv1 gv2 = Some gv3 ->
  gv_inject mi gv3 gv3.
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  rewrite J1 in J2. inv J2.
  rewrite J1' in J2'. inv J2'.
  unfold mfbop in *.
  rewrite J1 in H1. rewrite J1' in H1. 
  destruct v1';
    try solve [inv H1; eauto using gv_inject_gundef].
  destruct v2';
    try solve [inv H1; eauto using gv_inject_gundef].
  destruct fp; try solve [inv H1; eauto using gv_inject_gundef].
  destruct op; inv H1; 
    try (apply gv_inject_nptr_val_refl; try solve [auto | intro; congruence]).
  destruct op; inv H1; 
    try (apply gv_inject_nptr_val_refl; try solve [auto | intro; congruence]).
Qed.

Lemma simulation__mcast_refl : forall mi TD op t1 t2 gv1 gv2,
  gv_inject mi gv1 gv1 ->
  mcast TD op t1 t2 gv1 = Some gv2 ->
  gv_inject mi gv2 gv2.
Proof.
  intros.  assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  rewrite J1 in J2. inv J2.
  unfold mcast, mbitcast in *.
  destruct op; 
    try solve [
      inv H0; eauto using gv_inject_gundef |
      destruct t1; destruct t2; inv H0; eauto using gv_inject_gundef
    ].
Qed.

Lemma simulation__micmp_refl : forall mi TD c t gv1 gv2 gv3,
  gv_inject mi gv1 gv1 ->
  gv_inject mi gv2 gv2 ->
  micmp TD c t gv1 gv2 = Some gv3 ->
  gv_inject mi gv3 gv3.
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  rewrite J1 in J2. inv J2.
  rewrite J1' in J2'. inv J2'.
  unfold micmp, micmp_int in *.
  rewrite J1 in H1. rewrite J1' in H1. 
  destruct t; try solve [inv H1; eauto using gv_inject_gundef].
  destruct v1'; try solve [inv H1; eauto using gv_inject_gundef].
  destruct v2'; try solve [inv H1; eauto using gv_inject_gundef].
  destruct c; inv H1; 
        try (apply gv_inject_nptr_val_refl; try solve 
            [auto | apply cmp_isnt_ptr | apply cmpu_isnt_ptr]).
Qed.

Lemma simulation__mfcmp_refl : forall mi TD c t gv1 gv2 gv3,
  gv_inject mi gv1 gv1 ->
  gv_inject mi gv2 gv2 ->
  mfcmp TD c t gv1 gv2 = Some gv3 ->
  gv_inject mi gv3 gv3.
Proof.
  intros. assert (J0:=H0). assert (J:=H).
  apply gv_inject__val_inject with (TD:=TD) in H.
  destruct H as [v1 [v1' [J1 [J2 J3]]]].
  apply gv_inject__val_inject with (TD:=TD) in H0.
  destruct H0 as [v2 [v2' [J1' [J2' J3']]]].
  rewrite J1 in J2. inv J2.
  rewrite J1' in J2'. inv J2'.
  unfold mfcmp in *.
  rewrite J1 in H1. rewrite J1' in H1. 
  destruct v1'; try solve [inv H1; eauto using gv_inject_gundef].
  destruct v2'; try solve [inv H1; eauto using gv_inject_gundef].
  destruct t; try solve [inv H1; eauto using gv_inject_gundef].
  destruct c; inv H1; try (
    apply gv_inject_nptr_val_refl; try solve 
            [auto | apply val_of_bool_isnt_ptr | apply Vfalse_isnt_ptr | 
             apply Vtrue_isnt_ptr]
    ).
    eauto using gv_inject_gundef.
    eauto using gv_inject_gundef.
  destruct c; inv H1; try (
    apply gv_inject_nptr_val_refl; try solve 
            [auto | apply val_of_bool_isnt_ptr | apply Vfalse_isnt_ptr | 
             apply Vtrue_isnt_ptr]
    ).
Qed.

Lemma simulation__mgep_refl : forall mi TD v v0 t0 l1,
  MoreMem.val_inject mi v v ->
  mgep TD t0 v l1 = Some v0 ->
  MoreMem.val_inject mi v0 v0.
Proof.
  intros.
  unfold mgep in *.
  destruct v; tinv H0.
  destruct l1; tinv H0.
  destruct (mgetoffset TD (typ_array 0%nat t0) (z :: l1)) as [[o ?]|]; tinv H0.
  inv H0.
  inversion H. subst i0 b ofs1 b1.
  eapply MoreMem.val_inject_ptr; eauto.
    assert (Int.add 31 ofs2 (Int.repr 31 delta) = 
            Int.add 31 (Int.repr 31 delta) ofs2) as EQ.
      rewrite <- Int.add_commut. auto. 
    symmetry.
    rewrite Int.add_commut. 
    rewrite <- Int.add_assoc.
    rewrite <- EQ.   
    rewrite <- H5.
    auto.
Qed.

Lemma GV2ptr_refl : forall mi TD gv v,
  gv_inject mi gv gv ->
  GV2ptr TD (getPointerSize TD) gv = Some v ->
  MoreMem.val_inject mi v v.
Proof.
  intros.
  unfold GV2ptr in H0.
  destruct gv; tinv H0.
  destruct p; tinv H0.
  destruct v0; tinv H0.
  destruct gv; tinv H0.
  inv H0. inv H; auto.
Qed.

Lemma simulation__splitGenericValue_refl : forall mi gv z gvl gvr,
  gv_inject mi gv gv ->
  splitGenericValue gv z = Some (gvl, gvr) ->
  gv_inject mi gvl gvl /\
  gv_inject mi gvr gvr.
Proof.
  induction gv; simpl; intros; inv H; simpl.
    destruct (zeq z 0); inv H0. 
      auto.
      destruct (zlt z 0); inv H1.

    destruct (zeq z 0); inv H0. 
      split; auto.

      destruct (zlt z 0); inv H1.
      remember (splitGenericValue gv (z - size_chunk m)) as R.
      destruct R as [[gvl' gvr']|]; inv H0.
      symmetry in HeqR. 
      eapply IHgv in HeqR; eauto.
      destruct HeqR as [J5 J6].
      split; auto.
Qed.

Lemma simulation__extractGenericValue_refl : forall mi gv1 TD t1 l0 gv,
  gv_inject mi gv1 gv1 ->
  extractGenericValue TD t1 gv1 l0 = Some gv ->
  gv_inject mi gv gv.
Proof.
  intros.
  unfold extractGenericValue in *.
  destruct (intConsts2Nats TD l0); inv H0;
    try solve [auto using gv_inject_uninits].
  destruct (mgetoffset TD t1 l1) as [[o t']|]; inv H2;
    try solve [auto using gv_inject_uninits].
  unfold mget in *. 
  destruct (getTypeStoreSize TD t'); inv H1; 
    try solve [eauto using gv_inject_gundef].
  remember (splitGenericValue gv1 o) as R.
  destruct R as [[gvl gvr]|]; inv H2;
    try solve [eauto using gv_inject_gundef].
  symmetry in HeqR.
  eapply simulation__splitGenericValue_refl in HeqR; eauto.      
  destruct HeqR as [J2 J3].
  remember (splitGenericValue gvr (Z_of_nat n)) as R1.
  destruct R1 as [[gvrl gvrr]|]; inv H1;
    try solve [eauto using gv_inject_gundef].
  symmetry in HeqR1.
  eapply simulation__splitGenericValue_refl in HeqR1; eauto.      
  destruct HeqR1; auto.
  destruct_if; eauto using gv_inject_gundef.
Qed.

Lemma simulation__insertGenericValue_refl : forall mi gv1 TD t1 l0 gv t2 gv2,
  gv_inject mi gv1 gv1 ->
  gv_inject mi gv2 gv2 ->
  insertGenericValue TD t1 gv1 l0 t2 gv2 = Some gv ->
  gv_inject mi gv gv.
Proof.
  intros.
  unfold insertGenericValue in *.
  destruct (intConsts2Nats TD l0); inv H1; 
    try solve [eauto using gv_inject_gundef].
  destruct (mgetoffset TD t1 l1) as [[o ?]|]; inv H3;
    try solve [eauto using gv_inject_gundef].
  unfold mset in *. 
  destruct (getTypeStoreSize TD t2); inv H2; 
    try solve [eauto using gv_inject_gundef].
  destruct (n =n= length gv2); subst;
    try solve [inv H3; eauto using gv_inject_gundef].
  remember (splitGenericValue gv1 o) as R.
  destruct R as [[gvl gvr]|]; inv H3;
    try solve [eauto using gv_inject_gundef].
  symmetry in HeqR.
  eapply simulation__splitGenericValue_refl in HeqR; eauto.      
  destruct HeqR as [J2 J3].
  remember (splitGenericValue gvr (Z_of_nat n)) as R1.
  destruct R1 as [[gvrl gvrr]|]; inv H2;
    try solve [eauto using gv_inject_gundef].
  symmetry in HeqR1.
  eapply simulation__splitGenericValue_refl in HeqR1; eauto.      
  destruct HeqR1.
  destruct_if; eauto using gv_inject_gundef.
  apply gv_inject_app; auto.
  apply gv_inject_app; auto.
Qed.

Definition sb_mem_inj__const2GV_prop S TD c t :=
  wf_const S TD c t ->
  forall maxb mi Mem1 Mem2 gl gv t',
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_globals maxb gl -> 
  _const2GV TD gl c = Some (gv,t') ->
  t = t' /\ gv_inject mi gv gv.

Definition sb_mem_inj__list_const2GV_prop sdct :=
  wf_const_list sdct ->
  let 'lsdct := sdct in
  let '(lsdc, lt) := split lsdct in
  let '(lsd, lc) := split lsdc in
  let '(ls, ld) := split lsd in
  forall S maxb mi Mem1 Mem2 TD gl,
  wf_list_targetdata_typ' S TD lsd ->
  wf_sb_mi maxb mi Mem1 Mem2 ->
  wf_globals maxb gl -> 
  (forall gv t, 
    (forall t0, In t0 lt -> t0 = t) ->
    _list_const_arr2GV TD gl t lc = Some gv ->
    gv_inject mi gv gv
  ) /\
  (forall gv lt', 
    _list_const_struct2GV TD gl lc = Some (gv,lt') ->
    lt' = lt /\ gv_inject mi gv gv
  ).

Lemma sb_mem_inj__const2GV_mutrec :
  (forall S td c t, sb_mem_inj__const2GV_prop S td c t) /\
  (forall sdct, sb_mem_inj__list_const2GV_prop sdct).
Proof.
  (wfconst_cases (apply wf_const_mutind; 
                    unfold sb_mem_inj__const2GV_prop, 
                           sb_mem_inj__list_const2GV_prop) Case);
    intros; simpl in *; uniq_result; try solve [unfold val2GV; simpl; auto].
Case "wfconst_zero".
  inv_mbind. eauto using zeroconst2GV__gv_inject_refl.
Case "wfconst_floatingpoint".
  destruct floating_point5; inv H2; unfold val2GV; simpl; auto.
Case "wfconst_undef".
  inv_mbind.  split; eauto using gv_inject_gundef.
Case "wfconst_null".
  split; auto.
    unfold val2GV; simpl; auto.
    apply gv_inject_cons; auto.
    apply MoreMem.val_inject_ptr with (delta:=0); auto.
    destruct H0. auto.
Case "wfconst_array". Focus.
  inv_mbind.
  simpl_split lsdc lt.
  simpl_split lsd lc.
  simpl_split ls ld.
  match goal with
  | H3: match _ with
        | 0%nat => _
        | S _ => _ 
        end = _ |- _ => 
  rewrite H1 in H3; unfold Size.to_nat in *;
  destruct sz5; inv H3
  end.
    eauto using gv_inject_uninits.

    destruct (@H0 system5 maxb mi Mem1 Mem2 targetdata5 gl) as [J1 J2]; 
      try solve 
      [destruct targetdata5; eauto using const2GV_typsize_mutind_array'].
    symmetry_ctx.
    assert (lc = const_list) as EQ.
      eapply make_list_const_spec2; eauto.
    rewrite <- EQ in HeqR. subst.
    apply J1 in HeqR; eauto using make_list_const_spec4.

Case "wfconst_struct". Focus.
  simpl_split lsdc lt.
  simpl_split lsd lc.
  simpl_split ls ld.
  inv_mbind.
  destruct (@H0 system5 maxb mi Mem1 Mem2 (layouts5, namedts5) gl) as [J1 J2];
    eauto using const2GV_typsize_mutind_struct'.
  symmetry in HeqR2.
  erewrite <- map_list_const_typ_spec2 in HeqR2; eauto.
  erewrite <- map_list_const_typ_spec1 in H2; eauto.
  apply J2 in HeqR2; eauto.
  destruct HeqR2 as [J6 J7]; subst.
  match goal with
  | H2': (if _ then _ else _) = _ |- _ => rewrite H2 in H2'
  end.
  destruct g; inv H9; eauto.
    split; auto using gv_inject_uninits.

Case "wfconst_gid".
  inv_mbind. eauto using global_gv_inject_refl.

Case "wfconst_trunc_int".
  inv_mbind. symmetry_ctx.
  eapply H0 in HeqR; eauto. destruct HeqR.
  split; auto.
    eapply simulation__mtrunc_refl in HeqR0; eauto.

Case "wfconst_trunc_fp".
  inv_mbind. symmetry_ctx.
  eapply H0 in HeqR; eauto. destruct HeqR.
  split; auto.
    eapply simulation__mtrunc_refl in HeqR0; eauto.

Case "wfconst_zext".
  inv_mbind. symmetry_ctx.
  eapply H0 in HeqR; eauto. destruct HeqR.
  split; auto.
    eapply simulation__mext_refl in HeqR0; eauto.

Case "wfconst_sext".
  inv_mbind. symmetry_ctx.
  eapply H0 in HeqR; eauto. destruct HeqR.
  split; auto.
    eapply simulation__mext_refl in HeqR0; eauto.

Case "wfconst_fpext".
  inv_mbind. symmetry_ctx.
  eapply H0 in HeqR; eauto. destruct HeqR.
  split; auto.
    eapply simulation__mext_refl in HeqR0; eauto.

Case "wfconst_ptrtoint".
  inv_mbind. symmetry_ctx.
  eapply H0 in HeqR; eauto. destruct HeqR.
  split; auto.
    eauto using gv_inject_gundef.

Case "wfconst_inttoptr".
  inv_mbind. symmetry_ctx.
  eapply H0 in HeqR; eauto. destruct HeqR.
  split; auto.
    eauto using gv_inject_gundef.

Case "wfconst_bitcast".
  inv_mbind. symmetry_ctx.
  eapply H0 in HeqR; eauto. destruct HeqR.
  split; auto.
    assert (mcast targetdata5 castop_bitcast t (typ_pointer typ2) g = ret gv) 
      as J.
      simpl. auto.
    eapply simulation__mcast_refl; eauto.

Case "wfconst_gep". Focus.
  remember (_const2GV targetdata5 gl const_5) as R1.
  destruct R1 as [[gv1 t1]|]; tinv H9.
  symmetry in HeqR1.
  eapply H0 in HeqR1; eauto. destruct HeqR1. 
  destruct t1; tinv H9.
  remember (getConstGEPTyp const_list (typ_pointer t1)) as R2.
  destruct R2; tinv H9.
  remember (GV2ptr targetdata5 (getPointerSize targetdata5) gv1) as R3.
  destruct R3; tinv H9.
    remember (intConsts2Nats targetdata5 const_list) as R4.
    destruct R4; tinv H9.
      remember (mgep targetdata5 t1 v l0) as R5.
      destruct R5; inv H9.
        symmetry_ctx. uniq_result.
        eapply simulation__mgep_refl with (mi:=mi) in HeqR5; 
          eauto using GV2ptr_refl.
        unfold ptr2GV, val2GV. simpl. auto.

        inv_mbind. symmetry_ctx. uniq_result. 
        split; eauto using gv_inject_gundef.
      inv_mbind. symmetry_ctx. uniq_result. 
      split; eauto using gv_inject_gundef.
    inv_mbind. symmetry_ctx. uniq_result. 
    split; eauto using gv_inject_gundef.

Case "wfconst_select".
  inv_mbind. 
  destruct_if; eauto.

Case "wfconst_icmp".
  inv_mbind. 
  symmetry_ctx.
  eapply H0 in HeqR; eauto. clear H0.
  eapply H2 in HeqR0; eauto. clear H2.
  destruct HeqR. destruct HeqR0.
  split; eauto 2 using simulation__micmp_refl.

Case "wfconst_fcmp".
  inv_mbind. destruct t; tinv H11.
  inv_mbind. 
  symmetry_ctx.
  eapply H1 in HeqR; eauto. clear H1.
  eapply H3 in HeqR0; eauto. clear H3.
  destruct HeqR. destruct HeqR0.
  split; eauto 2 using simulation__mfcmp_refl.

Case "wfconst_extractvalue". 
  remember (_const2GV targetdata5 gl const_5) as R.
  destruct R as [[gv1 t1]|]; tinv H10.
  inv_mbind. symmetry_ctx.
  eapply H0 in HeqR; eauto. destruct HeqR. subst. 
  destruct H6 as [idxs [o [J3 J4]]].
  eapply getSubTypFromConstIdxs__mgetoffset in HeqR0; eauto.
  subst.
  split; auto.
    eapply simulation__extractGenericValue_refl; eauto.
Case "wfconst_insertvalue". 
  remember (_const2GV targetdata5 gl const_5) as R1.
  destruct R1 as [[gv1 t1]|]; tinv H12.
  remember (_const2GV targetdata5 gl const') as R2.
  destruct R2 as [[gv2 t2]|]; tinv H12.
  remember (insertGenericValue targetdata5 t1 gv1 const_list t2 gv2) as R3.
  destruct R3; inv H12. symmetry_ctx.
  eapply H0 in HeqR1; eauto.
  destruct HeqR1 as [J1 J2]; subst.
  eapply H2 in HeqR2; eauto.
  destruct HeqR2 as [J3 J4]; subst.
  split; auto.
    eapply simulation__insertGenericValue_refl in HeqR3; eauto.
Case "wfconst_bop".
  remember (_const2GV targetdata5 gl const1) as R1.
  remember (_const2GV targetdata5 gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H6.
  destruct_typ t1; tinv H6.
  destruct R2 as [[gv2 t2]|]; tinv H6.
  remember (mbop targetdata5 bop5 s0 gv1 gv2) as R3.
  destruct R3; inv H6. symmetry_ctx.
  eapply H0 in HeqR1; eauto.
  destruct HeqR1; subst.
  eapply H2 in HeqR2; eauto.
  destruct HeqR2; subst.
  split; auto.
    eapply simulation__mbop_refl in HeqR3; eauto.
Case "wfconst_fbop".
  remember (_const2GV targetdata5 gl const1) as R1.
  remember (_const2GV targetdata5 gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H6.
  destruct_typ t1; tinv H6.
  destruct R2 as [[gv2 t2]|]; tinv H6.
  remember (mfbop targetdata5 fbop5 f gv1 gv2) as R3.
  destruct R3; inv H6. symmetry_ctx.
  eapply H0 in HeqR1; eauto.
  destruct HeqR1; subst.
  eapply H2 in HeqR2; eauto.
  destruct HeqR2; subst.
  split; auto.
    eapply simulation__mfbop_refl in HeqR3; eauto.

Case "wfconst_nil".
  intros; subst.
  split; intros; subst; uniq_result.
    auto.
    split; eauto.    

Case "wfconst_cons".
  simpl_split lsdc lt. simpl.
  simpl_split lsd lc. simpl.
  simpl_split ls ld. simpl.
  intros S maxb mi Mem1 Mem2 TD gl HwfTD Hwfsim Hwgfl; subst.
  split. 
    intros gv t Hin Hc2g.
    remember (_list_const_arr2GV TD gl t lc) as R.
    destruct R; try solve [inv Hc2g].
    remember (_const2GV TD gl const_) as R'.
    destruct R' as [[gv0 t0]|]; try solve [inv Hc2g].
    destruct (typ_dec t t0); subst; try solve [inv Hc2g].
    remember (getTypeAllocSize TD t0) as R1.
    destruct R1; inv Hc2g.
    assert (typ5 = t0) as EQ. eapply Hin; eauto.
    subst.
    apply wf_list_targetdata_typ_cons_inv' in HwfTD.
    destruct HwfTD as [J1 [J2 J3]]; subst.
    symmetry in HeqR'.
    eapply H0 in HeqR'; eauto.
    destruct HeqR' as [J5 J6]; subst.
    eapply H2 in J1; eauto. destruct J1 as [J1 _]. clear H0 H2.
    symmetry in HeqR2.
    apply J1 in HeqR2; auto.
      apply gv_inject_app; eauto.
      apply gv_inject_app; eauto.
        apply gv_inject_uninits.

    intros gv lt' Hc2g.
    remember (_list_const_struct2GV TD gl lc) as R.
    destruct R as [[gv1 ts1]|]; try solve [inv Hc2g].
    remember (_const2GV TD gl const_) as R'.
    destruct R' as [[gv0 t0]|]; try solve [inv Hc2g].
    remember (getTypeAllocSize TD t0) as R1.
    destruct R1; inv Hc2g.
    apply wf_list_targetdata_typ_cons_inv' in HwfTD.
    destruct HwfTD as [J1' [J2' J3]]; subst.
    symmetry in HeqR'.
    eapply H0 in HeqR'; eauto.
    destruct HeqR' as [J5 J6]; subst.
    eapply H2 in J1'; eauto. destruct J1' as [_ J1']. clear H0 H2.
    symmetry in HeqR2.
    apply J1' in HeqR2; auto.
    destruct HeqR2 as [J7 J8]; subst.
    split; auto.
      apply gv_inject_app; eauto.
      apply gv_inject_app; eauto.
        apply gv_inject_uninits.
Qed.

Lemma sb_mem_inj__cgv2gv : forall mi g t maxb Mem Mem', 
  wf_sb_mi maxb mi Mem Mem' ->
  gv_inject mi g g -> gv_inject mi (? g # t ?) (? g # t ?).
Proof.
  intros.  
  destruct g; auto.
  destruct p; auto.
  destruct v; auto.
  destruct g; auto.
  inv H. 
  destruct_typ t; simpl; unfold null; eauto.
  destruct f; simpl; auto.
Qed.

Lemma sb_mem_inj__const2GV : forall maxb mi Mem Mem' TD gl c gv S t
  (Hwfc: wf_const S TD c t),
  wf_sb_mi maxb mi Mem Mem' ->
  wf_globals maxb gl -> 
  const2GV TD gl c = Some gv ->
  gv_inject mi gv gv.
Proof.
  destruct sb_mem_inj__const2GV_mutrec as [J _].
  unfold sb_mem_inj__const2GV_prop in J. 
  intros.
  unfold const2GV in H1.
  remember (_const2GV TD gl c) as R.
  destruct R as [[? ?]|]; inv H1; auto.
  eapply J in Hwfc; eauto. destruct Hwfc; subst.
  eapply sb_mem_inj__cgv2gv; eauto.
Qed.

Lemma simulation__eq__GV2int : forall mi gn gn' TD sz,
  gv_inject mi gn gn' ->
  GV2int TD sz gn = GV2int TD sz gn'.
Proof.
  intros mi gn gn' TD sz Hinj.
  unfold GV2int.
  destruct gn.
    inv Hinj. subst. auto.

    inv Hinj.
    inv H1; auto.
    destruct gn; inv H3; auto.
Qed.

Lemma simulation__isGVZero : forall mi c c' TD,
  gv_inject mi c c' ->
  isGVZero TD c = isGVZero TD c'.
Proof.
  intros mi c c' TD Hinj.
  unfold isGVZero.   
  erewrite simulation__eq__GV2int; eauto.
Qed.

Lemma simulation__GVs2Nats : forall mi TD vidxs vidxs',
  gvs_inject mi vidxs vidxs' ->
  GVs2Nats TD vidxs = GVs2Nats TD vidxs'.
Proof.
  induction vidxs; intros vidxs' Hinj.
    destruct vidxs'; inv Hinj; simpl; auto.
    destruct vidxs'; simpl in *; inv Hinj; auto.
      erewrite simulation__eq__GV2int; eauto.      
      erewrite IHvidxs; eauto.
Qed.

Lemma simulation__mgep' : forall mi TD v v' t0 l1,
  MoreMem.val_inject mi v v' ->
  mgep TD t0 v l1 = None -> 
  mgep TD t0 v' l1 = None.
Proof.
  intros.
  unfold mgep in *.
  inv H; auto.
  destruct l1; auto.
  destruct (mgetoffset TD (typ_array 0%nat t0) (z :: l1)) as [[i1 ?]|]; 
    try solve [inv H0 | auto].
Qed.

Lemma simulation__GV2ptr' : forall mi TD gv1 gv1',
  gv_inject mi gv1 gv1' ->
  GV2ptr TD (getPointerSize TD) gv1 = None ->
  GV2ptr TD (getPointerSize TD) gv1' = None.
Proof.
  intros.
  unfold GV2ptr in *.
  destruct gv1'; auto.
  destruct p.
  destruct v; auto.
  destruct gv1'; auto.
  destruct gv1; tinv H.
  destruct p; tinv H.
  inv H. inv H8. inv H3; tinv H0.
Qed.

Lemma simulation__GEP : forall maxb mi TD Mem Mem2 inbounds0 vidxs vidxs' gvp1 
    gvp gvp' t t',
  wf_sb_mi maxb mi Mem Mem2 ->
  gv_inject mi gvp gvp' ->
  gvs_inject mi vidxs vidxs' ->
  GEP TD t gvp vidxs inbounds0 t' = ret gvp1 ->
  exists gvp2,
    GEP TD t gvp' vidxs' inbounds0 t' = ret gvp2 /\
    gv_inject mi gvp1 gvp2.
Proof.
  intros maxb mi TD Mem Mem2 inbounds0 vidxs vidxs' gvp1 gvp gvp' t t' H H0 H1 
    H2.
  unfold GEP in *.
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; inv H2.
    symmetry in HeqR.
    eapply simulation__GV2ptr in HeqR; eauto.
    destruct HeqR as [v' [J1 J2]].
    rewrite J1. 
    assert (GVs2Nats TD vidxs = GVs2Nats TD vidxs') as EQ.
      eapply simulation__GVs2Nats; eauto.
    rewrite <- EQ.
    destruct (GVs2Nats TD vidxs).
      remember (mgep TD t v l0) as R1.
      destruct R1; inv H4.
        symmetry in HeqR1.
        eapply simulation__mgep in HeqR1; eauto.
        destruct HeqR1 as [v0' [J11 J12]].
        rewrite J11. exists (ptr2GV TD v0').
        unfold ptr2GV, val2GV.
        simpl. eauto.

        symmetry in HeqR1.
        eapply simulation__mgep' in HeqR1; eauto.
        rewrite HeqR1. simpl. 
        unfold gundef. simpl.
        eauto using gv_inject_gundef.

      rewrite H4. eauto using gv_inject_gundef.

    erewrite simulation__GV2ptr'; eauto.
    unfold gundef. simpl.
    eauto using gv_inject_gundef.
Qed.

(* The sb_ds_trans_lib.mem_simulation__free should use this lemma. *)
Lemma mem_inj__free : forall mi Mem0 M2 Mem' mgb hi lo
  (b2 : Values.block) (delta : Z) blk,
  wf_sb_mi mgb mi Mem0 M2 ->
  MoreMem.mem_inj mi Mem0 M2 ->
  Mem.free Mem0 blk lo hi = ret Mem' ->
  (lo, hi) = Mem.bounds Mem0 blk ->
  mi blk = ret (b2, delta) ->
  exists Mem2',
    Mem.free M2 b2 (lo+delta) (hi+delta) = ret Mem2' /\
    wf_sb_mi mgb mi Mem' Mem2' /\
    MoreMem.mem_inj mi Mem' Mem2'.
Proof.
  intros mi Mem0 M2 Mem' mgb hi lo b2 delta blk Hwfmi Hmsim1 H0 HeqR2 H4.
  assert ({ Mem2':Mem.mem | Mem.free M2 b2 (lo+delta) (hi+delta) = ret Mem2'})
    as J.
    apply Mem.range_perm_free.
    apply Mem.free_range_perm in H0.
    clear - H0 Hmsim1 H4.
    unfold Mem.range_perm in *.
    intros ofs J.
    assert (lo <= ofs - delta < hi) as J'.
      auto with zarith.
    apply H0 in J'.
    eapply MoreMem.perm_inj in J'; eauto.
    assert (ofs - delta + delta = ofs) as EQ. auto with zarith.
    rewrite EQ in J'. auto.
  destruct J as [Mem2' J].
  exists Mem2'. split; auto.
  split.
  SCase "wfmi".
    clear - Hwfmi H0 J H4.
    inversion_clear Hwfmi.
    split; eauto with mem.
    SSCase "Hmap3".
      intros. erewrite Mem.nextblock_free in H; eauto.
    SSCase "Hmap4".
      intros. erewrite Mem.nextblock_free; eauto.
    SSCase "bounds".
      intros. apply mi_bounds0 in H.
      erewrite Mem.bounds_free; eauto.
      erewrite Mem.bounds_free with (m2:=Mem2'); eauto.

  SCase "msim".
    clear - Hmsim1 Hwfmi H0 J H4.
    inv Hwfmi.
    eapply MoreMem.free_inj; eauto.
Qed.

Lemma mem_inj__pfree : forall mi Mem0 M2 Mem' mgb hi lo
  (b2 : Values.block) (delta : Z) blk,
  wf_sb_mi mgb mi Mem0 M2 ->
  MoreMem.mem_inj mi Mem0 M2 ->
  Mem.free Mem0 blk lo hi = ret Mem' ->
  (lo, hi) = Mem.bounds Mem0 blk ->
  mi blk = None ->
  wf_sb_mi mgb mi Mem' M2 /\ MoreMem.mem_inj mi Mem' M2.
Proof.
  intros mi Mem0 M2 Mem' mgb hi lo b2 delta blk Hwfmi Hmsim1 H0 HeqR2 H4.
  split.
  SCase "wfmi".
    clear - Hwfmi H0 H4.
    inversion_clear Hwfmi.
    split; eauto with mem.
    SSCase "Hmap3".
      intros. erewrite Mem.nextblock_free in H; eauto.
    SSCase "bounds".
      intros. apply mi_bounds0 in H.
      erewrite Mem.bounds_free; eauto.

  SCase "msim".
    clear - Hmsim1 Hwfmi H0 H4.
    inv Hwfmi.
    eapply MoreMem.free_left_nonmap_inj; eauto.
Qed.

(* The sb_ds_trans_lib.mem_simulation__malloc should use this lemma. *)
Lemma mem_inj__malloc : forall mi TD Mem Mem2 tsz gn align0 Mem' mb mgb,
  wf_sb_mi mgb mi Mem Mem2 ->
  MoreMem.mem_inj mi Mem Mem2 ->
  malloc TD Mem tsz gn align0 = ret (Mem', mb) ->
  exists mi', exists Mem2', exists mb',
    malloc TD Mem2 tsz gn align0 = ret (Mem2', mb') /\
    wf_sb_mi mgb mi' Mem' Mem2' /\
    MoreMem.mem_inj mi' Mem' Mem2' /\
    Values.inject_incr mi mi' /\
    mi' mb = Some (mb', 0) /\
    (forall b, b <> mb -> mi b = mi' b).
Proof.
  intros mi TD Mem Mem2 tsz gn align0 Mem' mb mgb Hwfmi Hmsim Halloc.
  unfold malloc in *.
  remember (GV2int TD Size.ThirtyTwo gn) as R.
  destruct R; try solve [inversion Halloc].
  remember (Mem.alloc Mem 0 (Size.to_Z tsz * z)) as R1.
  destruct R1 as [Mem1 mb1].
  destruct (zlt 0 (Size.to_Z tsz * z)); inv Halloc.
  remember (Mem.alloc Mem2 0 (Size.to_Z tsz * z)) as R2.
  destruct R2 as [Mem2' mb2].
  exists (fun b => if zeq b mb then Some (mb2,0%Z) else mi b).
  exists Mem2'. exists mb2.
  split; auto.
  assert (inject_incr mi (fun b : Z => if zeq b mb then ret (mb2, 0) else mi b))
    as Hinject_incr.
    unfold inject_incr.
    intros b b' d H.
    destruct (zeq b mb); subst; auto.
      clear - Hwfmi H HeqR1.
      symmetry in HeqR1.
      apply Mem.alloc_result in HeqR1. subst.
      destruct Hwfmi as [_ _ Hmap1 _].
      assert (mi (Mem.nextblock Mem) = None) as J.
        apply Hmap1; auto with zarith.
      rewrite H in J. inversion J.

  split; auto.
  Case "wfmi".
    clear - Hwfmi HeqR2 HeqR1.
    destruct Hwfmi as [Hno_overlap Hnull Hmap1 Hmap2 mi_freeblocks
      mi_mappedblocks mi_range_block mi_bounds mi_globals].
    symmetry in HeqR2, HeqR1.
    assert (J:=HeqR2).
    apply Mem.nextblock_alloc in HeqR2.
    split.
    SCase "no_overlap".
      clear - Hno_overlap J Hmap2.
      unfold MoreMem.meminj_no_overlap in *.
      intros.
      destruct (zeq b1 mb); subst.
        destruct (zeq b2 mb); subst.
          contradict H; auto.

          inv H0.
          apply Hmap2 in H1.
          apply Mem.alloc_result in J.
          subst. clear - H1. intro J. subst. contradict H1; zauto.
        destruct (zeq b2 mb); subst; eauto.
          inv H1.
          apply Hmap2 in H0.
          apply Mem.alloc_result in J.
          subst. clear - H0. intro J. subst. contradict H0; zauto.
    SCase "null".
      destruct (zeq Mem.nullptr mb); subst; auto.
        apply Mem.alloc_result in HeqR1.
        assert(J':=@Mem.nextblock_pos Mem).
        rewrite <- HeqR1 in J'.
        unfold Mem.nullptr in J'.
        contradict J'; zauto.
    SCase "map1".
      intros b H2.
      assert (J':=HeqR1).
      apply Mem.alloc_result in J'.
      apply Mem.nextblock_alloc in HeqR1.
      rewrite HeqR1 in H2.
      destruct (zeq b mb); subst; zeauto.
        contradict H2; zauto.
    SCase "map2".
      intros b1 b delta2 J'.
      rewrite HeqR2.
      destruct (zeq b1 mb); subst; zeauto.
        inv J'.
        apply Mem.alloc_result in J.
        subst.
        auto with zarith.
    SCase "freeblocks".
      intros b J'.
      destruct (zeq b mb); subst.
        apply Mem.valid_new_block in HeqR1.
        contradict HeqR1; auto.

        apply mi_freeblocks.
          intro J1. apply J'.
          eapply Mem.valid_block_alloc; eauto.
    SCase "mappedblocks".
      intros b b' delta J'.
      destruct (zeq b mb); subst.
        inv J'.
        apply Mem.valid_new_block in J; auto.
        eapply Mem.valid_block_alloc; eauto.
    SCase "range_block".
      intros b b' delta J'.
      destruct (zeq b mb); inv J'; subst; eauto.
    SCase "bounds".
      intros b b' delta J'.
      erewrite Mem.bounds_alloc; eauto.
      erewrite Mem.bounds_alloc with (m2:=Mem2'); eauto.
      unfold eq_block.
      destruct (zeq b mb); subst.
        inv J'.
        destruct (zeq b' b'); subst; auto.
          contradict n; auto.

        destruct (zeq b' mb2); subst; eauto.
          apply Hmap2 in J'.
          apply Mem.alloc_result in J.
          rewrite J in J'. contradict J'; zauto.
    SCase "globals".
      intros b J'.
      destruct (zeq b mb); subst; eauto.
        assert (J'':=J').
        apply mi_globals in J'.
        destruct (Mem.valid_block_dec Mem mb).
          apply Mem.fresh_block_alloc in HeqR1.
          contradict HeqR1; auto.

          apply mi_freeblocks in n.
          rewrite n in J'. inversion J'.

  split; auto.
  Case "msim".
      destruct Hmsim.
      apply MoreMem.mk_mem_inj.
      SSCase "mi_access".
        intros b1 b2 d c ofs p J1 J2.
        destruct (zeq b1 mb); subst; inv J1.
        SSSCase "b1=mb".
          symmetry in HeqR1.
          symmetry in HeqR2.
          destruct J2 as [J21 J22].
          assert (0 <= ofs /\ ofs + size_chunk c <= Size.to_Z tsz * z) as EQ.
            destruct (Z_le_dec 0 ofs).
              destruct (Z_le_dec (ofs + size_chunk c) (Size.to_Z tsz * z)); auto.
                apply Mem.perm_alloc_3 with (ofs:=ofs+size_chunk c-1) (p:=p) in
                  HeqR1; auto with zarith.
                unfold Mem.range_perm in J21.
                assert (ofs <= ofs + size_chunk c - 1 < ofs + size_chunk c) as J.
                  assert (J':=@Memdata.size_chunk_pos c).
                  auto with zarith.
                apply J21 in J.
                contradict J; auto.
              apply Mem.perm_alloc_3 with (ofs:=ofs) (p:=p) in HeqR1;
                auto with zarith.
              unfold Mem.range_perm in J21.
              assert (ofs <= ofs < ofs + size_chunk c) as J.
                assert (J':=@Memdata.size_chunk_pos c).
                auto with zarith.
              apply J21 in J.
              contradict J; auto.

          apply Mem.valid_access_alloc_same with (chunk:=c)(ofs:=ofs+0) in HeqR2;
            auto with zarith.
            eapply Mem.valid_access_implies; eauto using perm_F_any.

        SSSCase "b1<>mb".
          eapply Mem.valid_access_alloc_other; eauto.
          eapply Mem.valid_access_alloc_inv with (b:=mb)(lo:=0)
            (hi:=Size.to_Z tsz * z)(p:=p) in J2; eauto.
          destruct (eq_block); subst; try solve [eauto | contradict n; auto].

      SSCase "mi_memval".
Transparent Mem.alloc.
        intros b1 ofs b2 d J1 J2.
        injection HeqR1. intros NEXT MEM.
        injection HeqR2. intros NEXT2 MEM2.
        destruct Mem2. destruct Mem2'. destruct Mem. destruct Mem'.
        inv MEM.
        inv MEM2. clear HeqR1 HeqR2.
        simpl in *.
        unfold Mem.perm in *. simpl in *.
        clear maxaddress_pos0 conversion_props0 maxaddress_pos2
              conversion_props2.
        unfold update.
        destruct (zeq b1 nextblock1); subst; inv J1.
        SSSCase "b1=nextblock1".
          destruct (zeq b2 b2) as [e | n];
            try solve [contradict n; auto].
          apply MoreMem.memval_inject_undef.

        SSSCase "b1<>mb".
          destruct (zeq b2 nextblock); subst.
            clear - H0 Hwfmi.
            destruct Hwfmi. simpl in *.
            apply Hmap4 in H0.
            contradict H0; auto with zarith.

            apply MoreMem.memval_inject_incr with (f:=mi); auto.
              apply mi_memval; auto.
                clear - J2 n.
                unfold update in J2.
                destruct (zeq b1 nextblock1); subst;
                  try solve [auto | contradict n; auto].

Global Opaque Mem.alloc.

  split; auto.
  split.
    destruct (zeq mb mb); auto.
      contradict n; auto.
    intros.
    destruct (zeq b mb); subst; auto.
      contradict H; auto.
Qed.

(* sb_ds_trans_lib.simulation_mstore_aux should use this *)
Lemma mem_inj_mstore_aux : forall b b2 delta mi mgb
  (H1 : mi b = ret (b2, delta)) gv ofs gv2 Mem0 Mem2 Mem0'
  (Hwfmi : wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : MoreMem.mem_inj mi Mem0 Mem2)
  (Hinj : gv_inject mi gv gv2)
  (Hmstores : mstore_aux Mem0 gv b ofs = ret Mem0'),
   exists Mem2',
     mstore_aux Mem2 gv2 b2 (ofs + delta) = ret Mem2' /\
     wf_sb_mi mgb mi Mem0' Mem2' /\
     MoreMem.mem_inj mi Mem0' Mem2'.
Proof.
  induction gv; simpl; intros.
    inv Hmstores. inv Hinj. simpl. eauto.

    destruct a. inv Hinj.
    remember (Mem.store m Mem0 b ofs v) as R1.
    destruct R1 as [M|]; tinv Hmstores.
    symmetry in HeqR1.
    inv Hwfmi.
    assert (Hmstore0 := HeqR1).
    eapply MoreMem.store_mapped_inj with (f:=mi)(m2:=Mem2) in HeqR1;
      try solve [eauto | inversion Hwfmi; eauto].
    destruct HeqR1 as [Mem2' [Hmstore Hminj]].
    simpl. rewrite Hmstore.
    assert (ofs + delta + size_chunk m = ofs + size_chunk m + delta) as EQ. ring.
    rewrite EQ.
    apply IHgv with (Mem0:=M); auto.
    Case "wf_sb_mi".
      split; auto.
      SCase "Hnext1".
        erewrite <- Mem.nextblock_store with (m1:=Mem0) in Hmap3; eauto.
      SCase "Hnext2".
        intros b1 b0 delta2 J.
        apply Hmap4 in J.
        apply Mem.nextblock_store in Hmstore.
        rewrite Hmstore. auto.
      SCase "mi_freeblocks0".
        intros b0 J. apply mi_freeblocks0. intro J'. apply J.
        eapply Mem.store_valid_block_1; eauto.
      SCase "mi_mappedblocks0".
        intros b0 b' delta0 J.
        eapply Mem.store_valid_block_1; eauto.
      SCase "mi_bounds".
        intros b0 b' delta0 J.
        apply mi_bounds0 in J.
        apply Mem.bounds_store with (b':=b0) in Hmstore0; auto.
        rewrite Hmstore0. rewrite J.
        erewrite Mem.bounds_store with (m2:=Mem2'); eauto.
Qed.

Lemma simulation_mload_aux : forall Mem0 Mem2 b b2 delta mi mgb
  (Hwfmi : wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : MoreMem.mem_inj mi Mem0 Mem2)
  (H1 : mi b = ret (b2, delta)) mcs ofs gv
  (Hmloads : mload_aux Mem0 mcs b ofs = ret gv),
   exists gv2 : GenericValue,
     mload_aux Mem2 mcs b2 (ofs + delta) = ret gv2 /\ gv_inject mi gv gv2.
Proof.
  induction mcs; simpl; intros.
    inv Hmloads. eauto.

    remember (Mem.load a Mem0 b ofs) as R.
    destruct R as [v|]; tinv Hmloads.
    symmetry in HeqR.
    inv Hwfmi.
    eapply MoreMem.load_inj in HeqR; eauto.
    destruct HeqR as [v2 [Hmload Hinj]].
    rewrite Hmload.
    remember (mload_aux Mem0 mcs b (ofs + size_chunk a)) as R1.
    destruct R1; inv Hmloads.
    symmetry in HeqR1.
    apply IHmcs in HeqR1; auto.
    destruct HeqR1 as [gv2 [Hmloads Hinjs]].
    assert (ofs + delta + size_chunk a = ofs + size_chunk a + delta) as EQ. ring.
    rewrite EQ.
    rewrite Hmloads. eauto.
Qed.

Lemma simulation__fit_gv : forall maxb mi TD t Mem Mem2 gv1 gv1' gv2,
  wf_sb_mi maxb mi Mem Mem2 ->
  gv_inject mi gv1 gv2 ->
  fit_gv TD t gv1 = ret gv1' ->
  exists gv2',
    fit_gv TD t gv2 = ret gv2' /\ gv_inject mi gv1' gv2'.
Proof.
  intros maxb mi TD t Mem Mem2 gv1 gv1' gv2 Hwfmi Hinj Hfit.
  unfold fit_gv in *.
  destruct (getTypeSizeInBits TD t); tinv Hfit.
  erewrite <- gv_inject__same_size; eauto.
  erewrite <- simulation__gv_chunks_match_typb; eauto.
  destruct_if; eauto using gv_inject_gundef.
Qed.

Lemma simulation___cundef_gv : forall maxb mi t Mem Mem2 gv,
  wf_sb_mi maxb mi Mem Mem2 ->
  gv_inject mi gv gv ->
  gv_inject mi (cundef_gv gv t) (cundef_gv gv t).
Proof.
  intros.
  destruct_typ t; simpl; eauto.
    destruct f; simpl; eauto.
    inv H. unfold null. eauto.
Qed.

Lemma simulation___cgv2gv : forall maxb mi t Mem Mem2 gv1 gv2,
  wf_sb_mi maxb mi Mem Mem2 ->
  gv_inject mi gv1 gv2 ->
  gv_inject mi (? gv1 # t ?) (? gv2 # t ?).
Proof.
  intros maxb mi t Mem Mem2 gv1 gv2 Hwfmi Hinj.
  induction Hinj; auto.
    inv H; simpl; eauto.
    destruct gv1; inv Hinj; eauto.
      eapply simulation___cundef_gv; eauto.
Qed.

