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
Require Import assoclist.
Require Import sb_def.
Require Import Coqlib.
Require Import Memdata.
Require Import Memory.
Require Import Integers.
Require Import sb_tactic.
Require Import symexe_def.
Require Import symexe_tactic.
Require Import Znumtheory.

Import SoftBound.

Ltac zauto := auto with zarith.
Ltac zeauto := eauto with zarith.

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
  remember (mgetoffset TD (typ_array 0%nat t2) (INTEGER.to_Z 1 :: nil)) as R.
  destruct R; inv HeqR4.
  unfold mgetoffset in HeqR.
  destruct TD.
  remember (typ2utyp n (typ_array 0%nat t2)) as R1.
  destruct R1; inv HeqR.
  destruct u; inv H0.
    remember (getTypeAllocSize (l0, n) (utyp2typ u)) as R2.
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

Lemma wf_rmetadata__get_const_metadata : forall TD gl Mem0 rm c gvb gve c0 c1,
  wf_rmetadata TD Mem0 rm ->
  get_const_metadata c = Some (c0,c1) ->
  const2GV TD Mem0 gl c0 = Some gvb ->
  const2GV TD Mem0 gl c1 = Some gve ->
  wf_data TD Mem0 gvb gve.
Proof.
  induction c; intros gvb gve cc0 cc1 Hwfr H1 H2 H3; try solve [inversion H1].
  destruct t; inv H1; 
    try solve [ eauto using wf_rmetadata__get_const_metadata_aux ].

    unfold const2GV in H2, H3.
    remember (_const2GV TD Mem0 gl (const_gid (typ_function t l0) i0)) as R.
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

Lemma wf_rmetadata__get_reg_metadata : forall TD Mem0 rm gl vp gvb gve,
  wf_rmetadata TD Mem0 rm ->
  get_reg_metadata TD Mem0 gl rm vp = Some (mkMD gvb gve) ->
  wf_data TD Mem0 gvb gve.
Proof.
  intros TD Mem0 rm gl vp gvb gve Hwfr J.
  unfold get_reg_metadata in J.
  destruct vp.
    apply Hwfr in J; auto.

    remember (get_const_metadata c) as R.
    destruct R as [[bc ec] |]; 
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

Definition unsupported_cmd c : Prop :=
match c with
| insn_extractvalue _ _ _ _ | insn_insertvalue _ _ _ _ _ _ 
| insn_call _ _ _ _ _ _ => False
| _ => True
end.

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

Lemma dbCmd_preservation__dbMalloc__aux : forall TD Mem0 sz Mem' mb
  (H4 : Mem.alloc Mem0 0 sz = (Mem', mb))
  (gvb : GenericValue)
  (gve : GenericValue)
  (J' : wf_data TD Mem0 gvb gve),
  wf_data TD Mem' gvb gve.
Proof.
  intros.
  unfold wf_data in *.
  remember (GV2ptr TD (getPointerSize TD) gvb) as Rb.
  destruct Rb; auto.
  destruct v; auto.
  remember (GV2ptr TD (getPointerSize TD) gve) as Re.
  destruct Re; auto.
  destruct v; auto.
  destruct (zeq b b0); subst; auto. 
  destruct J' as [J1' J2'].
  split.
    apply Mem.nextblock_alloc in H4.
    rewrite H4. zauto.

    intro Hwfb.
    assert (Halloc := H4).
    eapply blk_temporal_alloc_inv in H4; eauto.         
    destruct (Values.eq_block b0 mb); subst.
      apply Mem.alloc_result in Halloc.    
      rewrite <- Halloc in J1'.
      contradict J1'; zauto.
      
      apply J2' in H4.
      eauto using range_perm_alloc_other.
Qed.

Lemma dbCmd_preservation__dbMalloc : forall
  (TD : TargetData)
  (rm : AssocList metadata)
  (lc : GVMap)
  (gl : GVMap)
  (id0 : atom)
  (t : typ)
  (v : value)
  (gn : GenericValue)
  (align0 : align)
  (Mem0 : mem)
  (MM : mmetadata)
  (als : list mblock)
  (Mem' : mem)
  (tsz : sz)
  (mb : mblock)
  (lc' : GVMap)
  (rm' : rmetadata)
  (n : Z)
  (H : getTypeAllocSize TD t = ret tsz)
  (H0 : getOperandValue TD Mem0 v lc gl = ret gn)
  (H1 : malloc TD Mem0 tsz gn align0 = ret (Mem', mb))
  (H2 : GV2int TD Size.ThirtyTwo gn = ret n)
  (H3 : prop_reg_metadata lc rm id0 (blk2GV TD mb)
         {| md_base := base2GV TD mb; md_bound := bound2GV TD mb tsz n |} =
       (lc', rm'))
  (Hnontemp : unsupported_cmd (insn_malloc id0 t v align0))
  (Hwf : wf_metadata TD Mem0 rm MM),
  wf_metadata TD Mem' rm' MM.
Proof.
  intros.
  invert_prop_reg_metadata. clear H3.
  unfold malloc in H1.
  rewrite H2 in H1.
  remember (Mem.alloc Mem0 0 (Size.to_Z tsz * n)) as R.
  inversion H1. clear H1. subst.
  destruct Hwf as [Hwfr Hwfm].
  split; auto.
  SCase "wf_rmd".
    clear H2 Hwfm. 
    intros i0 gvb gve J.
    destruct (@id_dec id0 i0); subst.
    SSCase "id0=i0".
      rewrite lookupAL_updateAddAL_eq in J.
      inversion J; subst. clear J.
      unfold wf_data.
      rewrite GV2ptr_base2GV. 
      rewrite GV2ptr_bound2GV. 
      destruct (zeq mb mb) as [J | J]; try solve [contradict J; auto].
      split.
        assert (H4':=H4).
        apply Mem.alloc_result in H4.
        apply Mem.nextblock_alloc in H4'.
        rewrite H4. rewrite H4'. zauto.

        intros Hwfb ofs J1. 
(*
      rewrite Int.signed_repr in J1; 
        auto using Int.min_signed_neg, Int.max_signed_pos with zarith.
*)
        apply Mem.valid_access_alloc_same with (ofs:=ofs)(chunk:=AST.Mint 7) 
          in H4.
          destruct H4 as [J2 J3].
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
          clear - J1.
          assert (J:=@Int.modulus_pos 31).
          assert ((Size.to_Z tsz * n) mod Int.modulus 31 <= (Size.to_Z tsz * n)) 
            as LE.
            apply Zmod_le.
              zauto.
              admit. (* tsz * n >= 0 *)
          destruct (zlt ((Size.to_Z tsz * n) mod Int.modulus 31) 
            (Int.half_modulus 31)); zeauto.

          simpl. rewrite bytesize_chunk_7_eq_1. zauto.

    SSCase "id0<>i0".
      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      assert (J':=@Hwfr i0 gvb gve J). clear Hwfr.    
      eapply dbCmd_preservation__dbMalloc__aux; eauto.

  SCase "wf_mmd".
    intros b ofs gvb gve J.
    assert (J':=@Hwfm b ofs gvb gve J). clear Hwfm.
    eapply dbCmd_preservation__dbMalloc__aux; eauto.
Qed.

Lemma dbCmd_preservation__dbFree__aux : forall
  TD
  (Mem0 : mem)
  (Mem' : mem)
  (b : Values.block)
  (z : Z)
  (z0 : Z)
  (HeqR : (z, z0) = Mem.bounds Mem0 b)
  (H0 : Mem.free Mem0 b z z0 = ret Mem')
  (gvb : GenericValue)
  (gve : GenericValue)
  (J : wf_data TD Mem0 gvb gve),
  wf_data TD Mem' gvb gve.
Proof.
  intros.
    unfold wf_data in *.
    remember (GV2ptr TD (getPointerSize TD) gvb) as Rb.
    destruct Rb; auto.
    destruct v; auto.
    remember (GV2ptr TD (getPointerSize TD) gve) as Re.
    destruct Re; auto.
    destruct v; auto.
    destruct (zeq b0 b1); subst; auto. 
    destruct J as [J1 J2].
    split.
      apply Mem.nextblock_free in H0.
      rewrite H0. auto.

      intro Hwfb.
      unfold blk_temporal_safe in *.
      erewrite Mem.bounds_free in Hwfb; eauto.
      assert (Hfree:=H0).
      destruct (Values.eq_block b b1); subst.
        rewrite <- HeqR in Hwfb.
        destruct (Z_lt_dec z z0).
          apply Mem.perm_free_2 with (ofs:=z)(p:=Nonempty) in H0; 
            zeauto.
          contradict Hwfb; auto.

          rewrite <- HeqR in J2.   
          eapply Mem.perm_free_3 in Hwfb; eauto.
          apply J2 in Hwfb. clear J2.
          unfold Mem.range_perm in *.
          intros ofs J. apply Hwfb in J.
          apply Mem.perm_free_1 with (b:=b1)(ofs:=ofs)(p:=Writable) in H0; auto.
            clear - n.
            destruct (Z_lt_dec ofs z); auto.
            destruct (Z_le_dec z0 ofs); auto.
            assert (False) as H. zeauto. 
            inversion H.

       destruct (Mem.bounds Mem0 b1).
       eapply Mem.perm_free_3 in Hwfb; eauto.
       apply J2 in Hwfb. clear J2.
       unfold Mem.range_perm in *.
       intros ofs J. apply Hwfb in J.
        apply Mem.perm_free_1 with (b:=b1)(ofs:=ofs)(p:=Writable) in H0;
          zeauto.
Qed.     

Lemma dbCmd_preservation : forall TD lc rm als gl Mem MM c lc' rm' als' Mem' MM' 
    tr r, 
  dbCmd TD gl lc rm als Mem MM c lc' rm' als' Mem' MM' tr r ->
  unsupported_cmd c ->
  wf_metadata TD Mem rm MM ->
  wf_metadata TD Mem' rm' MM'.
Proof.
  intros TD lc rm als gl Mem MM c lc' rm' als' Mem' MM' tr r H.
  (sb_dbCmd_cases (destruct H) Case); intros Hnontemp Hwf; 
    try solve [eauto | inversion Hnontemp].

Case "dbMalloc".
  eapply dbCmd_preservation__dbMalloc; eauto.

Case "dbFree". 
  unfold free in H0.
  destruct (GV2ptr TD (getPointerSize TD) mptr0); try solve [inversion H0].
  destruct v0; try solve [inversion H0].
  destruct (zeq (Int.signed 31 i0) 0); try solve [inversion H0].
  remember (Mem.bounds Mem0 b) as R.
  destruct R.
  unfold wf_metadata in *.
  destruct Hwf as [Hwfr Hwfm].
  split.
  SCase "wf_rmd".
    clear Hwfm. 
    intros i1 gvb gve J.
    apply Hwfr in J.   
    eapply dbCmd_preservation__dbFree__aux; eauto.
     
  SCase "wf_mmd".
    intros b1 ofs gvb gve J.
    assert (J':=@Hwfm b1 ofs gvb gve J). clear Hwfm.
    eapply dbCmd_preservation__dbFree__aux; eauto.

Case "dbAlloca".
  eapply dbCmd_preservation__dbMalloc; eauto.

Case "dbLoad_ptr".
  invert_prop_reg_metadata. clear H5.
  destruct Hwf as [Hwfr Hwfm].
  split; auto.
    intros i0 gvb gve J.
    destruct (@id_dec id0 i0); subst.
      clear Hwfr.
      rewrite lookupAL_updateAddAL_eq in J.
      inversion J; subst. clear J.
      eapply wf_mmetadata__get_mem_metadata in H5; eauto.

      clear Hwfm.
      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      apply Hwfr in J; auto.

Case "dbStore_nptr".
  unfold mstore in H3.
  destruct (GV2ptr TD (getPointerSize TD) gvp); try solve [inversion H3].
  destruct v0; try solve [inversion H3].
  destruct (typ2memory_chunk t); try solve [inversion H3].
  destruct (GV2val TD gv); try solve [inversion H3].
  destruct Hwf as [Hwfr Hwfm].
  split.
  SCase "wf_rmd".
    clear Hwfm.
    intros i1 gvb gve J.
    apply Hwfr in J. clear Hwfr.
    eapply wf_data__store__wf_data; eauto.

  SCase "wf_mmd".
    clear Hwfr.
    intros b0 ofs gvb gve J.
    apply Hwfm in J. clear Hwfm.
    eapply wf_data__store__wf_data; eauto.

Case "dbStore_ptr".
  unfold mstore in H3.
  destruct (GV2ptr TD (getPointerSize TD) gvp); try solve [inversion H3].
  destruct v0; try solve [inversion H3].
  destruct (typ2memory_chunk t); try solve [inversion H3].
  destruct (GV2val TD gv); try solve [inversion H3].
  destruct Hwf as [Hwfr Hwfm].
  split.
  SCase "wf_rmd".
    clear Hwfm.
    intros i1 gvb gve J.
    apply Hwfr in J. clear Hwfr.
    eapply wf_data__store__wf_data; eauto.

  SCase "wf_mmd".
    intros b0 ofs gvb gve J. 
    subst.
    unfold set_mem_metadata in J.
    destruct (GV2ptr TD (getPointerSize TD) gvp); 
      try solve [eauto using wf_mmetadata__store__wf_data].
    destruct v1; try solve [eauto using wf_mmetadata__store__wf_data].
    destruct (zeq b0 b1); subst; 
       simpl in J; eauto using wf_mmetadata__store__wf_data.
    destruct (Int.eq_dec 31 i1 ofs); subst; 
       simpl in J; eauto using wf_mmetadata__store__wf_data.
  
       inversion J; subst. clear J.
       apply wf_rmetadata__get_reg_metadata in H5; auto.
       eapply wf_data__store__wf_data; eauto.

Case "dbGEP".
  destruct Hwf as [Hwfr Hwfm].
  split; auto.
    clear Hwfm.
    invert_prop_reg_metadata. clear H3.
    intros i0 gvb gve J.
    destruct (@id_dec id0 i0); subst.
      rewrite lookupAL_updateAddAL_eq in J.
      inversion J; subst. clear J.
      eapply wf_rmetadata__get_reg_metadata; eauto.

      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      apply Hwfr in J; auto.

Case "dbBitcast_ptr".
  destruct Hwf as [Hwfr Hwfm].
  split; auto.
    clear Hwfm.
    invert_prop_reg_metadata. clear H2.
    intros i0 gvb gve J.
    destruct (@id_dec id0 i0); subst.
      rewrite lookupAL_updateAddAL_eq in J.
      inversion J; subst. clear J.
      eapply wf_rmetadata__get_reg_metadata; eauto.

      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      apply Hwfr in J; auto.

Case "dbInttoptr".
  destruct Hwf as [Hwfr Hwfm].
  split; auto.
    clear Hwfm.
    invert_prop_reg_metadata. clear H0.
    intros i0 gvb gve J.
    destruct (@id_dec id0 i0); subst.
      rewrite lookupAL_updateAddAL_eq in J.
      inversion J; subst. clear J.
      unfold wf_data.
      simpl.
      split.
        apply nullptr_lt_nextblock.

        intros Htmp ofs J.
        contradict J; zauto.

      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      apply Hwfr in J; auto.

Case "dbSelect_ptr".
  destruct Hwf as [Hwfr Hwfm].
  split; auto.
    clear Hwfm.
    destruct (isGVZero TD cond0). 
      invert_prop_reg_metadata. clear H4.
      intros i0 gvb gve J.
      destruct (@id_dec id0 i0); subst.
        rewrite lookupAL_updateAddAL_eq in J.
        inversion J; subst. clear J.
        eapply wf_rmetadata__get_reg_metadata; eauto.

        rewrite <- lookupAL_updateAddAL_neq in J; auto.
        apply Hwfr in J; auto.

      invert_prop_reg_metadata. clear H4.
      intros i0 gvb gve J.
      destruct (@id_dec id0 i0); subst.
        rewrite lookupAL_updateAddAL_eq in J.
        inversion J; subst. clear J.
        eapply wf_rmetadata__get_reg_metadata; eauto.

        rewrite <- lookupAL_updateAddAL_neq in J; auto.
        apply Hwfr in J; auto.
Qed.

Definition unsupported_cmds cs : Prop :=
  fold_right (fun c => fun p => p /\ unsupported_cmd c) True cs.

Lemma dbCmds_preservation : forall TD lc rm als gl Mem MM cs lc' rm' als' Mem' 
    MM' tr r,
  SoftBound.dbCmds TD gl lc rm als Mem MM cs lc' rm' als' Mem' MM' tr r ->
  unsupported_cmds cs ->
  wf_metadata TD Mem rm MM ->
  wf_metadata TD Mem' rm' MM'.
Proof.
  intros TD lc rm als gl Mem MM cs lc' rm' als' Mem' MM' tr r H Hnontemp.
  (sb_dbCmds_cases (induction H) Case); intros J; subst;
    try solve [
      invert_result | 

      simpl in Hnontemp;
      destruct Hnontemp as [Hnontemp1 Hnontemp2];
      eauto using dbCmd_preservation
    ].
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
    destruct R; try solve [inv H1].
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

Definition dbCall_preservation_prop S TD Ps fs gl lc rm Mem0 MM0 call0 lc' rm' 
  Mem' MM' tr r 
(db:SoftBound.dbCall S TD Ps fs gl lc rm Mem0 MM0 call0 lc' rm' Mem' MM' tr r) :=
  wf_metadata TD Mem0 rm MM0 ->
  wf_metadata TD Mem' rm' MM'.

Definition dbSubblock_preservation_prop S TD Ps fs gl lc rm als Mem MM cs lc' rm'
  als' Mem' MM' tr r
(db:SoftBound.dbSubblock S TD Ps fs gl lc rm als Mem MM cs lc' rm' als' Mem' MM' 
    tr r) :=
  wf_metadata TD Mem rm MM ->
  wf_metadata TD Mem' rm' MM'.

Definition dbSubblocks_preservation_prop S TD Ps fs gl lc rm als Mem MM cs lc' 
  rm' als' Mem' MM' tr r 
(db:SoftBound.dbSubblocks S TD Ps fs gl lc rm als Mem MM cs lc' rm' als' Mem' MM'
  tr r) :=
  wf_metadata TD Mem rm MM ->
  wf_metadata TD Mem' rm' MM'.

Definition dbBlock_preservation_prop S TD Ps fs gl F state state' tr r
  (db:SoftBound.dbBlock S TD Ps fs gl F state state' tr r) :=
  forall l ps cs tmn lc rm als Mem MM l' ps' cs' tmn' lc' rm' als' Mem' MM',
  state = SoftBound.mkState (SoftBound.mkEC (block_intro l ps cs tmn) lc rm als)
    Mem MM ->
  state' = SoftBound.mkState (SoftBound.mkEC (block_intro l' ps' cs' tmn') lc' 
    rm' als') Mem' MM' ->
  wf_metadata TD Mem rm MM ->
  wf_metadata TD Mem' rm' MM'.

Definition dbBlocks_preservation_prop S TD Ps fs gl F state state' tr r
  (db:SoftBound.dbBlocks S TD Ps fs gl F state state' tr r) :=
  forall l ps cs tmn lc rm als Mem MM l' ps' cs' tmn' lc' rm' als' Mem' MM',
  state = SoftBound.mkState (SoftBound.mkEC (block_intro l ps cs tmn) lc rm als)
    Mem MM ->
  state' = SoftBound.mkState (SoftBound.mkEC (block_intro l' ps' cs' tmn') lc' 
    rm' als') Mem' MM' ->
  wf_metadata TD Mem rm MM ->
  wf_metadata TD Mem' rm' MM'.

Definition dbFdef_preservation_prop fid rt lp S TD Ps lc rm gl fs Mem MM lc'
  rm' als' Mem' MM' B' Rid oResult tr r
  (db:SoftBound.dbFdef fid rt lp S TD Ps lc rm gl fs Mem MM lc' rm' als' Mem' MM'
    B' Rid oResult tr r) :=
  wf_metadata TD Mem rm MM ->
  wf_metadata TD Mem' rm' MM'.

Lemma unsupported_cmds_axiom : forall cs, unsupported_cmds cs.
Admitted. (* This is not true. We need to restrict code w/o free and calls. *)

Lemma sbop_preservation :
  (forall S TD Ps fs gl lc rm Mem0 MM0 call0 lc' rm' Mem' MM' tr r db, 
     dbCall_preservation_prop S TD Ps fs gl lc rm Mem0 MM0 call0 lc' rm' 
       Mem' MM' tr r db) 
    /\
  (forall S TD Ps fs gl lc rm als Mem MM sb lc' rm' als' Mem' MM' tr r db,
     dbSubblock_preservation_prop S TD Ps fs gl lc rm als Mem MM sb lc' 
       rm' als' Mem' MM' tr r db) /\
  (forall S TD Ps fs gl lc rm als Mem MM sbs lc' rm' als' Mem' MM' tr r db,
     dbSubblocks_preservation_prop S TD Ps fs gl lc rm als Mem MM sbs 
       lc' rm' als' Mem' MM' tr r db) /\
  (forall S TD Ps fs gl F state1 state2 tr r db,
     dbBlock_preservation_prop S TD Ps fs gl F state1 state2 tr r db) /\
  (forall S TD Ps fs gl F state1 state2 tr r db,
     dbBlocks_preservation_prop S TD Ps fs gl F state1 state2 tr r db) /\
  (forall fid rt lp S1 TD Ps1 lc rm gl fs Mem MM lc' rm' als' Mem' MM' B' Rid 
       oResult tr r db,
     dbFdef_preservation_prop fid rt lp S1 TD Ps1 lc rm gl fs Mem MM lc' rm'
       als' Mem' MM' B' Rid oResult tr r db).
Proof.
(sb_db_mutind_cases
  apply SoftBound.sb_db_mutind with
    (P  := dbCall_preservation_prop)
    (P0 := dbSubblock_preservation_prop)
    (P1 := dbSubblocks_preservation_prop)
    (P2 := dbBlock_preservation_prop)
    (P3 := dbBlocks_preservation_prop)
    (P4 := dbFdef_preservation_prop) Case);
  unfold dbCall_preservation_prop, 
         dbFdef_preservation_prop, dbSubblock_preservation_prop,
         dbSubblocks_preservation_prop, 
         dbBlock_preservation_prop,
         dbBlocks_preservation_prop; intros; subst; 
    try solve [ eauto using dbCmds_preservation, unsupported_cmds_axiom ].
Case "dbCall_internal". admit. (* goal is false *)
Case "dbCall_external". admit. (* goal is false *)
Case "dbCall_internal_error1". admit. (* goal is false *)
Case "dbCall_external_error1". admit. (* goal is false *)

Case "dbBlock_ok".
  inv H1. inv H0.
  apply dbCmds_preservation in d0; eauto using unsupported_cmds_axiom.

Case "dbBlock_error1".
  inv H1. inv H0. eauto.
  apply dbCmds_preservation in d0; eauto using unsupported_cmds_axiom.

Case "dbBlock_error2".
  inv H1. inv H0. eauto.

Case "dbBlocks_nil".
  inv H0. auto.

Case "dbBlocks_cons".
  inversion d; subst; try solve [ invert_result ].
  destruct B'. eauto.

Case "dbBlocks_cons_error".
  inv H1. eauto.
  destruct B2. eauto.

Case "dbFdef_func".
  apply dbCmds_preservation in d1; eauto using unsupported_cmds_axiom.
  apply H0; auto.
  eapply H; eauto.
  eapply initRmetadata__wf_metadata in e1; eauto.

Case "dbFdef_func_error1".
  apply H0; auto.
  eapply H; eauto.
  eapply initRmetadata__wf_metadata in e1; eauto.

Case "dbFdef_func_error2".
  eapply H; eauto.
  eapply initRmetadata__wf_metadata in e1; eauto.

Case "dbFdef_proc".
  apply dbCmds_preservation in d1; eauto using unsupported_cmds_axiom.
  apply H0; auto.
  eapply H; eauto.
  eapply initRmetadata__wf_metadata in e1; eauto.

Case "dbFdef_proc_error1".
  apply H0; auto.
  eapply H; eauto.
  eapply initRmetadata__wf_metadata in e1; eauto.

Case "dbFdef_proc_error2".
  eapply H; eauto.
  eapply initRmetadata__wf_metadata in e1; eauto.
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

Lemma assert_mptr__valid_access : forall md TD Mem gl rm v MM t g b ofs c,
  wf_metadata TD Mem rm MM ->
  Some md = get_reg_metadata TD Mem gl rm v ->
  assert_mptr TD t g md ->
  GV2ptr TD (getPointerSize TD) g = ret Values.Vptr b ofs ->
  typ2memory_chunk t = ret c ->
  (align_chunk c | Int.signed 31 ofs) ->
  blk_temporal_safe Mem b ->
  Mem.valid_access Mem c b (Int.signed 31 ofs) Writable.
Proof.
  intros md TD Mem gl rm v MM t g b ofs c Hwf Heqmd J R3 R4 R5 Htmp.
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

Lemma dbCmd_progress : forall TD lc rm als gl Mem MM c, 
  wf_metadata TD Mem rm MM ->
  unsupported_cmd c ->
  exists lc', exists rm', exists als', exists Mem', exists MM', exists tr, 
  exists r, 
    dbCmd TD gl lc rm als Mem MM c lc' rm' als' Mem' MM' tr r.
Proof.
  intros TD lc rm als gl Mem MM c Hwf Hiscall.
  cmd_cases (destruct c) Case.

Case "insn_bop".
  remember (BOP TD Mem lc gl b s v v0) as R.
  destruct R.
    exists (updateAddAL _ lc i0 g). exists rm. exists als. exists Mem.
    exists MM. exists trace_nil. exists rok.
    apply dbBop; auto.

    exists lc. exists rm. exists als. exists Mem. exists MM. exists trace_nil. 
    exists rerror.
    apply dbBop_error; auto.

Case "insn_fbop".
  remember (FBOP TD Mem lc gl f f0 v v0) as R.
  destruct R.
    exists (updateAddAL _ lc i0 g). exists rm. exists als. exists Mem.
    exists MM. exists trace_nil. exists rok.
    apply dbFBop; auto.

    exists lc. exists rm. exists als. exists Mem. exists MM. exists trace_nil. 
    exists rerror.
    apply dbFBop_error; auto.

Case "insn_extractvalue".
  inversion Hiscall.

Case "insn_insertvalue".
  inversion Hiscall.

Case "insn_malloc".
  admit.

Case "insn_free".
  admit.

Case "insn_alloca".
  admit.

Case "insn_load".

  assert (exists g, getOperandValue TD Mem v lc gl = Some g) as R2.
    admit. (* wont be stuck for well-formed SSA. *)
  destruct R2 as [g R2].
  assert (exists md, get_reg_metadata TD Mem gl rm v = Some md) as R2'.
    admit. (* wont be stuck for well-formed SSA. *)
  destruct R2' as [md R2'].
  remember (isPointerTypB t) as R1.
  destruct (assert_mptr_dec TD t g md) as [J | J].
  SCase "assert ok".
    assert (exists b, exists ofs, 
      GV2ptr TD (getPointerSize TD) g = Some (Values.Vptr b ofs)) as R3. 
      admit. (* from wf *)
    assert (exists c, typ2memory_chunk t = Some c) as R4. 
      admit. (* from wf *)
    destruct R3 as [b [ofs R3]].
    destruct R4 as [c R4].
    destruct (Zdivide_dec (align_chunk c) (Int.signed 31 ofs)) as [R5 | R5].
    SSCase "align ok".
      destruct (blk_temporal_safe_dec Mem b) as [R8 | R8].
      SSSCase "valid block".
        assert (exists gv, mload TD Mem g t a = Some gv) as R6.
          unfold mload.
          rewrite R3. rewrite R4.
          assert (Mem.valid_access Mem c b (Int.signed 31 ofs) Readable) as J'.
            apply Mem.valid_access_implies with (p1:=Writable); auto with mem.
            eapply assert_mptr__valid_access; eauto.
          apply Mem.valid_access_load in J'.
          destruct J' as [v0 J'].
          rewrite J'.
          exists (val2GV TD v0 c). auto.
        destruct R6 as [gv R6].
        destruct R1.
        SSSSCase "t is ptr".
          remember (prop_reg_metadata lc rm i0 gv (get_mem_metadata TD MM g)) 
            as R7.
          destruct R7 as (lc', rm'). 
          subst.
          exists lc'. exists rm'. exists als. exists Mem. exists MM. 
          exists trace_nil. exists rok. eapply dbLoad_ptr; eauto.
          unfold isPointerTyp. auto.
        SSSSCase "t isnt ptr".
          subst.
          exists (updateAddAL _ lc i0 gv). exists rm. exists als. exists Mem. 
          exists MM. exists trace_nil. exists rok. eapply dbLoad_nptr; eauto.
          unfold isPointerTyp. rewrite <- HeqR1. intro JJ. inversion JJ.
      SSSCase "~valid block".
        subst.
        exists lc. exists rm. exists als. exists Mem. exists MM. 
        exists trace_nil. exists rerror. eapply dbLoad_error3; eauto.
        intro JJ. apply R8. destruct JJ; auto.
    SSCase "align fails".
      subst.
      exists lc. exists rm. exists als. exists Mem. exists MM. exists trace_nil.
      exists rerror. eapply dbLoad_error3; eauto.
      intro JJ. apply R5. destruct JJ; auto.
  SCase "assert fails".
    subst.
    exists lc. exists rm. exists als. exists Mem. exists MM. exists trace_nil.
    exists rabort. eapply dbLoad_abort; eauto.

Case "insn_store".

  assert (exists gv, getOperandValue TD Mem v lc gl = Some gv) as R21.
    admit. (* wont be stuck for well-formed SSA. *)
  assert (exists gvp, getOperandValue TD Mem v0 lc gl = Some gvp) as R22.
    admit. (* wont be stuck for well-formed SSA. *)
  destruct R21 as [gv R21].
  destruct R22 as [gvp R22].
  assert (exists md, get_reg_metadata TD Mem gl rm v0 = Some md) as R21'.
    admit. (* wont be stuck for well-formed SSA. *)
  destruct R21' as [md R21'].
  remember (isPointerTypB t) as R1.
  destruct (assert_mptr_dec TD t gvp md) as [J | J].
  SCase "assert ok".
    assert (exists b, exists ofs, 
      GV2ptr TD (getPointerSize TD) gvp = Some (Values.Vptr b ofs)) as R3. 
      admit. (* from wf *)
    assert (exists c, typ2memory_chunk t = Some c) as R4. 
      admit. (* from wf *)
    destruct R3 as [b [ofs R3]].
    destruct R4 as [c R4].
    assert (exists v1, GV2val TD gv = Some v1) as R8.
      admit. (* wf *)
    assert (exists v2, GV2val TD gvp = Some v2) as R9.
      admit. (* wf *)
    destruct R8 as [v1 R8].
    destruct R9 as [v2 R9].
    destruct (Zdivide_dec (align_chunk c) (Int.signed 31 ofs)) as [R5 | R5].
    SSCase "align ok".
      destruct (blk_temporal_safe_dec Mem b) as [R10 | R10].
      SSSCase "valid block".
        assert (exists Mem', mstore TD Mem gvp t gv a = Some Mem') as R6.
          unfold mstore.
          rewrite R3. rewrite R4.
          assert (Mem.valid_access Mem c b (Int.signed 31 ofs) Writable) as J'.
            eapply assert_mptr__valid_access; eauto.
          assert (J2:=@Mem.valid_access_store Mem c b (Int.signed 31 ofs) v1 J').
          destruct J2 as [Mem' J2].
          rewrite R8.
          exists Mem'. auto.
        destruct R6 as [Mem' R6].
        destruct R1.
        SSSSCase "t is ptr".
          assert (exists md', get_reg_metadata TD Mem gl rm v = Some md') 
            as R22'.
            admit. (* wont be stuck for well-formed SSA. And we generate rm for
                      all pointer registers. *)
          destruct R22' as [md' R22'].
          subst.
          exists lc. exists rm. exists als. exists Mem'. 
          exists (set_mem_metadata TD MM gvp md'). 
          exists trace_nil. exists rok. 
          eapply dbStore_ptr; eauto.
            unfold isPointerTyp. auto.
        SSSSCase "t isnt ptr".
          subst.
          exists lc. exists rm. exists als. exists Mem'. exists MM. 
          exists trace_nil. exists rok. 
          eapply dbStore_nptr; eauto.
            unfold isPointerTyp. rewrite <- HeqR1. intro JJ. inversion JJ.
      SSSCase "~valid block".
        subst.
        exists lc. exists rm. exists als. exists Mem. exists MM. 
        exists trace_nil. exists rerror. eapply dbStore_error3; eauto.
        intro JJ. apply R10. destruct JJ; auto.
    SSCase "align fails".
      subst.
      exists lc. exists rm. exists als. exists Mem. exists MM. exists trace_nil.
      exists rerror. eapply dbStore_error3; eauto.
      intro JJ. apply R5. destruct JJ; auto.
  SCase "assert fails".
    subst.
    exists lc. exists rm. exists als. exists Mem. exists MM. exists trace_nil.
    exists rabort. eapply dbStore_abort; eauto.

Case "insn_gep".

Admitted.

Lemma dbCmds_progress : forall cs TD lc rm als gl Mem MM, 
  wf_metadata TD Mem rm MM ->
  unsupported_cmds cs ->
  exists lc', exists rm', exists als', exists Mem', exists MM', exists tr, 
  exists r, 
    dbCmds TD gl lc rm als Mem MM cs lc' rm' als' Mem' MM' tr r.
Proof.
  induction cs; intros.
    exists lc. exists rm. exists als. exists Mem0. exists MM. exists trace_nil.
    exists rok.
    apply dbCmds_nil.

    simpl in H0.
    destruct H0 as [J1 J2].
    assert (Hwfm:=H).
    apply dbCmd_progress with (lc:=lc)(gl:=gl)(c:=a)(als:=als) in H; auto.
    destruct H as [lc' [rm' [als' [Mem' [MM' [tr [r H]]]]]]].
    destruct r.
      assert (J3:=H).
      apply dbCmd_preservation in J3; auto.
      assert (J:=@IHcs TD lc' rm' als' gl Mem' MM' J3 J1).
      destruct J as [lc'' [rm'' [als'' [Mem'' [MM'' [tr' [r' J]]]]]]].
      exists lc''. exists rm''. exists als''. exists Mem''. exists MM''. 
      exists (trace_app tr tr'). exists r'. 
      eapply dbCmds_cons; simpl; eauto.

      exists lc'. exists rm'. exists als'. exists Mem'. exists MM'. exists tr. 
      exists rabort. apply dbCmds_cons_error; simpl; auto.

      exists lc'. exists rm'. exists als'. exists Mem'. exists MM'. exists tr. 
      exists rerror. apply dbCmds_cons_error; simpl; auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
