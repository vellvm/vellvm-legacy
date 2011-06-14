Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa/compcert".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Export targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import genericvalues.
Require Import trace.
Require Import ssa_props.
Require Import alist.
Require Import sb_def.
Require Import Coqlib.
Require Import Memdata.
Require Import Memory.
Require Import Integers.
Require Import sb_tactic.
Require Import symexe_def.
Require Import symexe_tactic.
Require Import Znumtheory.
Require Import sb_tactic.

Import SoftBound.

Definition unsupported_cmd c : Prop :=
match c with
| insn_extractvalue _ _ _ _ | insn_insertvalue _ _ _ _ _ _ 
| insn_call _ _ _ _ _ _ => False
| _ => True
end.

Definition wf_data (TD:TargetData) (M:mem) (gvb gve:GenericValue) : Prop :=
  match (GV2ptr TD (getPointerSize TD) gvb,
         GV2ptr TD (getPointerSize TD) gve) with
  | (Some (Values.Vptr bb bofs), Some (Values.Vptr eb eofs)) =>
      if zeq bb eb then
        bb < Mem.nextblock M /\
        (blk_temporal_safe M bb ->
         Mem.range_perm M bb (Int.signed 31 bofs) (Int.signed 31 eofs) Writable)
      else False
  | _ => False
  end.

Definition wf_rmetadata (TD:TargetData) (M:mem) (rm:rmetadata) : Prop :=
  forall (i:id) (gvb gve:GenericValue),
    lookupAL _ rm i = Some (mkMD gvb gve) -> wf_data TD M gvb gve.

Definition wf_mmetadata (TD:TargetData) (M:mem) (MM:mmetadata) : Prop :=
  forall (b:Values.block) (ofs:int32) (gvb gve:GenericValue),
    MM b ofs = Some (mkMD gvb gve) -> wf_data TD M gvb gve.

Definition wf_metadata (TD:TargetData) (M:mem) (rm:rmetadata) (MM:mmetadata) 
    : Prop :=
  wf_rmetadata TD M rm /\ wf_mmetadata TD M MM.

Lemma range_perm_alloc_other:
  forall m1 lo hi m2 b, Mem.alloc m1 lo hi = (m2, b) ->
  forall b' lo' hi' p,
  Mem.range_perm m1 b' lo' hi' p ->
  Mem.range_perm m2 b' lo' hi' p.
Proof.
  intros.
  unfold Mem.range_perm in *.
  intros ofs J.
  apply H0 in J.
  eapply Mem.perm_alloc_1; eauto.
Qed.

Lemma store_range_perm_1:
  forall chunk m1 b ofs v m2, Mem.store chunk m1 b ofs v = Some m2 ->
  forall b' lo' hi' p,
  Mem.range_perm m1 b' lo' hi' p -> Mem.range_perm m2 b' lo' hi' p.
Proof.
  intros.
  unfold Mem.range_perm in *.
  intros ofs0 J.
  apply H0 in J.
  eapply Mem.perm_store_1; eauto.
Qed.

Lemma GV2ptr_base2GV : forall TD mb,
  GV2ptr TD (getPointerSize TD) (base2GV TD mb) = 
    Some (Values.Vptr mb (Int.repr 31 0)).
Proof.
  intros TD mb.
  unfold GV2ptr. unfold base2GV. unfold blk2GV. unfold ptr2GV. unfold val2GV.
  auto.
Qed.

Lemma GV2ptr_bound2GV : forall TD mb tsz n,
  GV2ptr TD (getPointerSize TD) (bound2GV TD mb tsz n) = 
    Some (Values.Vptr mb (Int.repr 31 ((Size.to_Z tsz)*n))).
Proof.
  intros TD mb tsz n.
  unfold GV2ptr. unfold bound2GV. unfold ptr2GV. unfold val2GV.
  auto.
Qed.

Lemma wf_mmetadata__wf_data : forall Mem0 TD MM b0 ofs gvb gve,
  wf_mmetadata TD Mem0 MM ->
  MM b0 ofs = Some (mkMD gvb gve) ->
  wf_data TD Mem0 gvb gve.
Proof.
  intros Mem0 TD MM b0 ofs gvb gve Hwfm J.
  apply Hwfm in J; clear Hwfm.
  unfold wf_data in *.
  destruct (GV2ptr TD (getPointerSize TD) gvb); auto.
Qed.

Lemma blk_temporal_safe_store_2 : forall m Mem0 b ofs0 v0 Mem' b0,
  Mem.store m Mem0 b ofs0 v0 = Some Mem' ->
  blk_temporal_safe Mem' b0 ->
  blk_temporal_safe Mem0 b0. 
Proof.
  intros m Mem0 b ofs0 v0 Mem' b0 Hstore H.
  unfold blk_temporal_safe in *.
  assert (J:=Hstore).
  apply Mem.bounds_store with (b':=b0) in J.
  rewrite <- J.
  destruct (Mem.bounds Mem' b0).
  eapply Mem.perm_store_2 in H; eauto.  
Qed.

Lemma wf_data__store__wf_data : forall m Mem0 b ofs0 v0 Mem' TD gvb gve,
  Mem.store m Mem0 b ofs0 v0 = Some Mem' ->
  wf_data TD Mem0 gvb gve ->
  wf_data TD Mem' gvb gve.
Proof.
  intros m Mem0 b ofs0 v0 Mem' TD gvb gve H1 J.
  unfold wf_data in *.
  destruct (GV2ptr TD (getPointerSize TD) gvb); auto.
  destruct v; auto.
  destruct (GV2ptr TD (getPointerSize TD) gve); auto.
  destruct v; auto.
  destruct (zeq b0 b1); auto.
    destruct J as [J1 J2].
    split.
      apply Mem.nextblock_store in H1.
      rewrite H1. auto.

      intro H.
      eapply blk_temporal_safe_store_2 in H; eauto.
      apply J2 in H.
      eauto using store_range_perm_1.
Qed.

Lemma wf_mmetadata__store__wf_data : forall m Mem0 b ofs0 v0 Mem' TD MM b0 ofs 
    gvb gve,
  Mem.store m Mem0 b ofs0 v0 = Some Mem' ->
  wf_mmetadata TD Mem0 MM ->
  MM b0 ofs = Some (mkMD gvb gve) ->
  wf_data TD Mem' gvb gve.
Proof.
  intros m Mem0 b ofs0 v0 Mem' TD MM b0 ofs gvb gve H1 Hwfm J.
  apply wf_mmetadata__wf_data with (Mem0:=Mem0)(TD:=TD) in J; eauto.
  eapply wf_data__store__wf_data; eauto.
Qed.

Lemma wf_rmetadata__get_const_metadata_aux : forall TD Mem0 gl t i0 gvb gve,
  const2GV TD Mem0 gl (const_gid t i0) = ret gvb ->
  const2GV TD Mem0 gl
         (const_gep false (const_gid t i0)
            (Cons_list_const (const_int Size.ThirtyTwo 1) Nil_list_const)) =
       ret gve ->
  wf_data TD Mem0 gvb gve.
Proof.
  intros TD Mem0 gl t i0 gvb gve H2 H3.
  unfold const2GV in H3.
  remember (_const2GV TD Mem0 gl
           (const_gep false (const_gid t i0)
              (Cons_list_const (const_int Size.ThirtyTwo 1) Nil_list_const))) 
    as R0.
  destruct R0; try solve [inversion H3].
  destruct p. inv H3.
  unfold const2GV in H2.
  remember (_const2GV TD Mem0 gl (const_gid t i0)) as R1.
  destruct R1; try solve [inversion H2].
  destruct p. inv H2.
  unfold _const2GV in *.
  remember (Constant.getTyp (const_gid t i0)) as R.
  destruct R; try solve [inversion HeqR0].
  destruct t2; try solve [inversion HeqR0].
  remember (lookupAL GenericValue gl i0) as R'.
  destruct R'; try solve [inversion HeqR0].
  inv HeqR1.
  remember (Constant.getTyp
    (const_gep false (const_gid t i0)
      (Cons_list_const (const_int Size.ThirtyTwo 1) Nil_list_const))) as R1.
  destruct R1; try solve [inversion HeqR0].
  remember (GV2ptr TD (getPointerSize TD) g) as R2.
  destruct R2; try solve [inversion HeqR0].
  remember (intConsts2Nats TD
    (Cons_list_const (const_int Size.ThirtyTwo 1) Nil_list_const)) as R3.
  destruct R3; try solve [inversion HeqR0].
  remember (mgep TD t2 v l0) as R4.
  destruct R4; inv HeqR0.
  simpl in *.
  inv HeqR3. inv HeqR. inv HeqR1.
  
  unfold GV2ptr in *.
  destruct g; inv HeqR2.
  destruct p.
  destruct v1; inv H0.
  destruct g; inv H1.
  unfold mgep in *.
  remember (mgetoffset TD (typ_array 0%nat t) (INTEGER.to_Z 1 :: nil)) as R.
  destruct R; inv HeqR4.
  unfold mgetoffset in HeqR.
  destruct TD.
  remember (typ2utyp n (typ_array 0%nat t)) as R1.
  destruct R1; inv HeqR.
  destruct t0; inv H0.
    remember (getTypeAllocSize (l0, n) t0) as R2.
    destruct R2; inv H1.
    unfold wf_data.
    unfold GV2ptr.
    unfold ptr2GV. unfold val2GV.
    destruct (zeq b b); auto.
      admit. (* wf of globals *)
 
    admit. (* HeqR1 is false *)
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

Lemma nullptr_lt_nextblock : forall Mem0,
  Mem.nullptr < Mem.nextblock Mem0.
Proof.
  intros.
  assert (J:=@Mem.nextblock_pos Mem0).
  unfold Mem.nullptr.
  zauto.
Qed.

Lemma null_is_wf_data : forall TD Mem,
  wf_data TD Mem null null.
Proof.
  intros TD Mem.
  eapply eq_gv_is_wf_data with (bb:=Mem.nullptr).
    apply nullptr_lt_nextblock.

    unfold GV2ptr.
    simpl. eauto.
Qed.

Lemma wf_rmetadata__get_const_metadata : forall TD gl Mem0 rm c gvb gve c0 c1 ct,
  wf_rmetadata TD Mem0 rm ->
  get_const_metadata c = Some (c0,c1,ct) ->
  const2GV TD Mem0 gl c0 = Some gvb ->
  const2GV TD Mem0 gl c1 = Some gve ->
  wf_data TD Mem0 gvb gve.
Proof.
  induction c; intros gvb gve cc0 cc1 ct Hwfr H1 H2 H3; try solve [inversion H1].
  destruct t; inv H1; 
    try solve [ eauto using wf_rmetadata__get_const_metadata_aux ].

    unfold const2GV in H2, H3.
    remember (_const2GV TD Mem0 gl (const_gid (typ_function t l0 v) i0)) as R.
    destruct R; try solve [inversion H2 | inversion H3].
    destruct p. inv H2. inv H3.
    unfold GV2ptr.
    unfold _const2GV in HeqR.
    remember (lookupAL GenericValue gl i0) as R1.
    destruct R1; inv HeqR.
    assert (exists b, exists ofs, 
      GV2ptr TD (getPointerSize TD) g = Some (Values.Vptr b ofs) /\
      b < Mem.nextblock Mem0) as J.
      admit. (* wf of globals *)
    destruct J as [b [ofs [J1 J2]]].
    eapply eq_gv_is_wf_data; eauto.

    simpl in H1; eauto.
Qed.

Lemma wf_rmetadata__get_reg_metadata : forall TD Mem0 rm gl vp gvb gve t,
  wf_rmetadata TD Mem0 rm ->
  get_reg_metadata TD Mem0 gl rm vp = Some (mkMD gvb gve, t) ->
  wf_data TD Mem0 gvb gve.
Proof.
  intros TD Mem0 rm gl vp gvb gve t Hwfr J.
  unfold get_reg_metadata in J.
  destruct vp.
    remember (lookupAL metadata rm i0) as R.
    destruct R; inv J.
    symmetry in HeqR.
    apply Hwfr in HeqR; auto.

    remember (get_const_metadata c) as R.
    destruct R as [[[bc ec] ct] |]; 
      try solve [inversion J; subst; auto using null_is_wf_data].
    remember (const2GV TD Mem0 gl bc) as R0.
    remember (const2GV TD Mem0 gl ec) as R1.
    destruct R0; try solve [inversion J]. 
    simpl in J.
    destruct R1; try solve [inversion J]. 
    simpl in J.
    inv J.
    eapply wf_rmetadata__get_const_metadata; eauto.
Qed.

Lemma wf_mmetadata__get_mem_metadata : forall TD Mem0 MM gvp gvb gve,
  wf_mmetadata TD Mem0 MM ->
  get_mem_metadata TD MM gvp = mkMD gvb gve ->
  wf_data TD Mem0 gvb gve.
Proof.
  intros TD Mem0 MM gvp gvb gve Hwfm H4.
  unfold get_mem_metadata in H4.
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion H4; subst; auto using null_is_wf_data].
  destruct v; try solve [inversion H4; subst; auto using null_is_wf_data].
  remember (MM b i0) as R'.
  destruct R'; inv H4; auto using null_is_wf_data.
  symmetry in HeqR'.     
  apply Hwfm in HeqR'; auto.
Qed.

Lemma blk_temporal_alloc_inv : forall Mem0 lo hi Mem' mb b0,
  Mem.alloc Mem0 lo hi = (Mem', mb) ->
  blk_temporal_safe Mem' b0 ->
  (if Values.eq_block b0 mb then 
    Mem.bounds Mem' b0 = (lo, hi)
  else blk_temporal_safe Mem0 b0).
Proof.
  intros.
  unfold blk_temporal_safe in *.
  assert (Halloc := H).  
  apply Mem.bounds_alloc with (b':=b0) in H.
  destruct (Values.eq_block b0 mb); subst; auto.
    rewrite <- H.
    destruct (Mem.bounds Mem' b0).
    apply Mem.perm_alloc_inv with (b':=b0)(ofs:=z)(p:=Nonempty) in Halloc; auto.
    destruct (zeq b0 mb); auto.
      subst. contradict n; auto.
Qed.

Lemma initRmetadata_aux__wf_metadata : forall TD Mem0 gl la lp rm accum rm0 MM,
  initRmetadata_aux TD Mem0 gl la lp rm accum = ret rm0 ->
  wf_metadata TD Mem0 rm MM ->
  wf_metadata TD Mem0 accum MM ->
  wf_metadata TD Mem0 rm0 MM.
Proof.
  induction la; intros lp rm accum rm0 MM H Hwf; simpl in H.
    destruct lp; inv H; auto.

    destruct a.
    destruct lp; inv H; auto.
    destruct p.
    destruct (isPointerTypB t); eauto.
    remember (get_reg_metadata TD Mem0 gl rm v) as R.
    destruct R as [[md ?]|]; try solve [inv H1].
      intro Hwf'.
      apply IHla with (MM:=MM) in H1; auto.
      destruct Hwf' as [Hwfr' Hwfm'].
      destruct Hwf as [Hwfr Hwfm].
      split; auto.
        intros i gvb gve J.
        destruct (@id_dec i0 i); subst.
          rewrite lookupAL_updateAddAL_eq in J.
          inversion J; subst. clear J.
          symmetry in HeqR.
          eapply wf_rmetadata__get_reg_metadata in HeqR; eauto. 

          rewrite <- lookupAL_updateAddAL_neq in J; auto.
          apply Hwfr' in J; auto.
Qed.

Lemma initRmetadata__wf_metadata : forall TD Mem0 gl la lp rm rm0 MM,
  initRmetadata TD Mem0 gl la lp rm = ret rm0 ->
  wf_metadata TD Mem0 rm MM ->
  wf_metadata TD Mem0 rm0 MM.
Proof.
  intros TD Mem0 gl la lp rm rm0 MM H Hwf.
  unfold initRmetadata in H.
  eapply initRmetadata_aux__wf_metadata in H; eauto.
  destruct Hwf as [Hwfr Hwfm].
  split; auto.
    intros i gvb gve J.
    inversion J.
Qed.

Lemma assert_mptr_dec : forall TD t ptr md,
  assert_mptr TD t ptr md \/ ~ assert_mptr TD t ptr md.
Proof.
  intros.
  unfold is_true. 
  destruct (assert_mptr TD t ptr md); auto.
Qed.

Lemma typ2memory_chunk__le__getTypeAllocSize : forall t c s TD,
  typ2memory_chunk t = Some c ->
  Some s = getTypeAllocSize TD t ->
  size_chunk c <= Size.to_Z s.
Proof.
  intros t c s TD H1 H2.
  unfold getTypeAllocSize, getTypeStoreSize, getTypeSizeInBits, 
         getTypeSizeInBits_and_Alignment in H2.
  destruct TD.
  destruct t; inv H1; inv H2;
    simpl; unfold bytesize_chunk, Size.to_nat, RoundUpAlignment, Size.to_Z, ndiv.
    assert (Z_of_nat (s0 + 7) / Z_of_nat 8 >= 0) as J.
      assert (J1:=@Z_of_S_gt_O (s0 + 6)).
      assert (S (s0 + 6) = (s0 + 7)%nat) as EQ. auto.
      rewrite EQ in J1.        
      assert (J2:=@O_lt_Z_of_S 7).
      assert (0 <= Z_of_nat (s0 + 7) / Z_of_nat 8) as J3.
        apply Z_div_pos; auto with zarith.
       zauto.
    assert (two_power_nat (getIntAlignmentInfo l0 s0 true) >= 0 ) as J2.
      admit. (* zarith *)
    rewrite nat_of_Z_eq.
      rewrite nat_of_Z_eq; auto.
        admit. (* zarith *)
      rewrite nat_of_Z_eq; auto.
        admit. (* zarith *)

    destruct f; inv H0; inv H1; simpl; unfold RoundUpAlignment, ndiv.
      assert (Z_of_nat 39 / Z_of_nat 8 = 4) as EQ.
        simpl. admit. (* zarith *) 
      rewrite EQ.
      rewrite nat_of_Z_eq.
        rewrite nat_of_Z_eq.
(*
Z_mod_lt
Z_div_plus_full
Z_div_mod_eq_full
*)
          admit. (* zarith *) 
          zauto. (* zarith *) 
        rewrite nat_of_Z_eq.
          admit. (* zarith *) 
          zauto. (* zarith *) 

      assert (Z_of_nat 71 / Z_of_nat 8 = 8) as EQ.
        simpl. admit. (* zarith *) 
      rewrite EQ.
      rewrite nat_of_Z_eq.
        rewrite nat_of_Z_eq.
          admit. (* zarith *) 
          zauto. (* zarith *) 
        rewrite nat_of_Z_eq.
          admit. (* zarith *) 
          zauto. (* zarith *) 

    admit. (* assume getPointerSizeInBits = 32 *)
Qed.

Lemma assert_mptr__valid_access : forall md TD Mem gl rm v MM t g b ofs c mt,
  wf_metadata TD Mem rm MM ->
  Some (md,mt) = get_reg_metadata TD Mem gl rm v ->
  assert_mptr TD t g md ->
  GV2ptr TD (getPointerSize TD) g = ret Values.Vptr b ofs ->
  typ2memory_chunk t = ret c ->
  (align_chunk c | Int.signed 31 ofs) ->
  blk_temporal_safe Mem b ->
  Mem.valid_access Mem c b (Int.signed 31 ofs) Writable.
Proof.
  intros md TD Mem gl rm v MM t g b ofs c mt Hwf Heqmd J R3 R4 R5 Htmp.
  unfold Mem.valid_access.
  split; auto.
    unfold assert_mptr in J.
    rewrite R3 in J.
    symmetry in Heqmd.  
    destruct md.
    destruct Hwf as [Hwfr Hwfm].
    apply wf_rmetadata__get_reg_metadata in Heqmd; auto.
    unfold wf_data in Heqmd.
    destruct (GV2ptr TD (getPointerSize TD) md_base0); 
      try solve [inversion Heqmd].
    destruct v0; try solve [inversion Heqmd].
    destruct (GV2ptr TD (getPointerSize TD) md_bound0); 
      try solve [inversion Heqmd].
    destruct v0; try solve [inversion Heqmd].
    destruct (zeq b0 b1); subst; try solve [inversion Heqmd].
    remember (getTypeAllocSize TD t) as R6.
    destruct R6; try solve [inversion J].
    simpl in J.
    intros z Jz.
    bdestruct4 J as J1 J4 J2 J3.
    destruct (zeq b b1); subst; try solve [inversion J1].
    apply Heqmd; auto.
    clear - J2 J3 Jz HeqR6 R4.
    assert (size_chunk c <= Size.to_Z s) as J4.
      eapply typ2memory_chunk__le__getTypeAllocSize; eauto.
    destruct (zle (Int.signed 31 i0) (Int.signed 31 ofs)); 
      simpl in J2; inversion J2.
    destruct (zle (Int.signed 31 ofs + Size.to_Z s) (Int.signed 31 i1)); 
      simpl in J3; inversion J3.
    zeauto.
Qed.

Lemma blk_temporal_safe_dec : forall M b,
  {blk_temporal_safe M b} + {~ blk_temporal_safe M b}.
Proof.
  intros M b.
  unfold blk_temporal_safe.
  destruct (Mem.bounds M b).
  apply Mem.perm_dec.
Qed.

Lemma valid_block_dec : forall M b,
  {Mem.valid_block M b} + { ~ Mem.valid_block M b}.
Proof.
  intros M b.
  unfold Mem.valid_block.
  apply Z_lt_dec; auto.
Qed.  

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
