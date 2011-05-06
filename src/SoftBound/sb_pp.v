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

Import SoftBound.

Definition wf_data (TD:TargetData) (M:mem) (gvb gve:GenericValue) : Prop :=
  match (GV2ptr TD (getPointerSize TD) gvb,
         GV2ptr TD (getPointerSize TD) gve) with
  | (Some (Values.Vptr bb bofs), Some (Values.Vptr eb eofs)) =>
      if zeq bb eb then
        Mem.range_perm M bb (Int.signed 31 bofs) (Int.signed 31 eofs) Readable
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
  intros. inv H. red.
Admitted.

Lemma store_range_perm_1:
  forall chunk m1 b ofs v m2, Mem.store chunk m1 b ofs v = Some m2 ->
  forall b' lo' hi' p,
  Mem.range_perm m1 b' lo' hi' p -> Mem.range_perm m2 b' lo' hi' p.
Admitted.

Lemma GV2ptr_base2GV : forall TD mb,
  GV2ptr TD (getPointerSize TD) (base2GV TD mb) = 
    Some (Values.Vptr mb (Int.repr 31 0)).
Admitted.

Lemma GV2ptr_bound2GV : forall TD mb tsz n,
  GV2ptr TD (getPointerSize TD) (bound2GV TD mb tsz n) = 
    Some (Values.Vptr mb (Int.repr 31 ((Size.to_Z tsz)*n))).
Admitted.

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
  destruct (zeq b0 b1); eauto using store_range_perm_1.
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
    destruct R; try solve [inversion J].
    destruct p.
    remember (const2GV TD Mem0 gl c0) as R0.
    remember (const2GV TD Mem0 gl c1) as R1.
    destruct R0; try solve [inversion J]. simpl in J.
    destruct R1; try solve [inversion J]. simpl in J.
    inv J.
    unfold wf_data.
Admitted.

Lemma dbCmd_preservation : forall TD lc rm als gl Mem MM c lc' rm' als' Mem' MM' 
    tr r, 
  dbCmd TD gl lc rm als Mem MM c lc' rm' als' Mem' MM' tr r ->
  wf_metadata TD Mem rm MM ->
  wf_metadata TD Mem' rm' MM'.
Proof.
  intros TD lc rm als gl Mem MM c lc' rm' als' Mem' MM' tr r H.
  (sb_dbCmd_cases (destruct H) Case); intro Hwf; eauto.

Case "dbMalloc".
  invert_prop_reg_metadata. clear H3.
  unfold malloc in H1.
  rewrite H2 in H1.
  remember (Mem.alloc Mem0 0 (Size.to_Z tsz * n)) as R.
  inversion H1. clear H1. subst.
  destruct Hwf as [Hwfr Hwfm].
  split; auto.
    clear H2 Hwfm. 
    intros i0 gvb gve J.
    destruct (@id_dec id0 i0); subst.
      rewrite lookupAL_updateAddAL_eq in J.
      inversion J; subst. clear J.
      unfold wf_data.
      rewrite GV2ptr_base2GV. 
      rewrite GV2ptr_bound2GV. 
      destruct (zeq mb mb) as [J | J]; try solve [contradict J; auto].
      intros ofs J1. 
(*
      rewrite Int.signed_repr in J1; 
        auto using Int.min_signed_neg, Int.max_signed_pos with zarith.
*)
      apply Mem.valid_access_alloc_same with (ofs:=ofs)(chunk:=AST.Mint 7) in H4.
        destruct H4 as [J2 J3].
        unfold Mem.range_perm in J2.
        apply Mem.perm_implies with (p1:=Freeable); auto with mem.
        apply J2.
        simpl. unfold bytesize_chunk. admit.

        admit. 
        simpl. unfold bytesize_chunk. admit.
        simpl. unfold bytesize_chunk. admit.
      

       rewrite <- lookupAL_updateAddAL_neq in J; auto.
       assert (J':=@Hwfr i0 gvb gve J). clear Hwfr.    
       unfold wf_data in *.
       destruct (GV2ptr TD (getPointerSize TD) gvb); auto.
       destruct v0; auto.
       destruct (GV2ptr TD (getPointerSize TD) gve); auto.
       destruct v0; auto.
       destruct (zeq b b0); eauto using range_perm_alloc_other.

    intros b ofs gvb gve J.
    assert (J':=@Hwfm b ofs gvb gve J). clear Hwfm.
    unfold wf_data in *.
    destruct (GV2ptr TD (getPointerSize TD) gvb); auto.
    destruct v0; auto.
    destruct (GV2ptr TD (getPointerSize TD) gve); auto.
    destruct v0; auto.
    destruct (zeq b0 b1); eauto using range_perm_alloc_other.

Case "dbFree".
  admit.

Case "dbAlloca".
  invert_prop_reg_metadata. clear H3.
  unfold malloc in H1.
  rewrite H2 in H1.
  remember (Mem.alloc Mem0 0 (Size.to_Z tsz * n)) as R.
  inversion H1. clear H1. subst.
  destruct Hwf as [Hwfr Hwfm].
  split; auto.
    clear H2 Hwfm. 
    intros i0 gvb gve J.
    destruct (@id_dec id0 i0); subst.
      rewrite lookupAL_updateAddAL_eq in J.
      inversion J; subst. clear J.
      unfold wf_data in *.
      rewrite GV2ptr_base2GV. 
      rewrite GV2ptr_bound2GV. 
      destruct (zeq mb mb) as [J | J]; try solve [contradict J; auto].
      intros ofs J1. 
(*
      rewrite Int.signed_repr in J1; 
        auto using Int.min_signed_neg, Int.max_signed_pos with zarith.
*)
      apply Mem.valid_access_alloc_same with (ofs:=ofs)(chunk:=AST.Mint 7) in H4.
        destruct H4 as [J2 J3].
        unfold Mem.range_perm in J2.
        apply Mem.perm_implies with (p1:=Freeable); auto with mem.
        apply J2.
        simpl. unfold bytesize_chunk. admit.

        admit. 
        simpl. unfold bytesize_chunk. admit.
        simpl. unfold bytesize_chunk. admit.
      

       rewrite <- lookupAL_updateAddAL_neq in J; auto.
       assert (J':=@Hwfr i0 gvb gve J). clear Hwfr.    
       unfold wf_data in *.
       destruct (GV2ptr TD (getPointerSize TD) gvb); auto.
       destruct v0; auto.
       destruct (GV2ptr TD (getPointerSize TD) gve); auto.
       destruct v0; auto.
       destruct (zeq b b0); eauto using range_perm_alloc_other.

    intros b ofs gvb gve J.
    assert (J':=@Hwfm b ofs gvb gve J). clear Hwfm.
    unfold wf_data in *.
    destruct (GV2ptr TD (getPointerSize TD) gvb); auto.
    destruct v0; auto.
    destruct (GV2ptr TD (getPointerSize TD) gve); auto.
    destruct v0; auto.
    destruct (zeq b0 b1); eauto using range_perm_alloc_other.

Case "dbLoad_ptr".
  invert_prop_reg_metadata. clear H5.
  destruct Hwf as [Hwfr Hwfm].
  split; auto.
    intros i0 gvb gve J.
    destruct (@id_dec id0 i0); subst.
      clear Hwfr.
      rewrite lookupAL_updateAddAL_eq in J.
      inversion J; subst. clear J.
      unfold get_mem_metadata in H4.
      remember (GV2ptr TD (getPointerSize TD) gvp) as R.
      destruct R; try solve [inversion H4].
      destruct v; try solve [inversion H4].
      apply Hwfm in H4; auto.

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
    clear Hwfm.
    intros i1 gvb gve J.
    apply Hwfr in J. clear Hwfr.
    unfold wf_data in *.
    destruct (GV2ptr TD (getPointerSize TD) gvb); auto.
    destruct v1; auto.
    destruct (GV2ptr TD (getPointerSize TD) gve); auto.
    destruct v1; auto.
    destruct (zeq b0 b1); eauto using store_range_perm_1.

    clear Hwfr.
    intros b0 ofs gvb gve J.
    apply Hwfm in J. clear Hwfm.
    unfold wf_data in *.
    destruct (GV2ptr TD (getPointerSize TD) gvb); auto.
    destruct v1; auto.
    destruct (GV2ptr TD (getPointerSize TD) gve); auto.
    destruct v1; auto.
    destruct (zeq b1 b2); eauto using store_range_perm_1.

Case "dbStore_ptr".
  unfold mstore in H3.
  destruct (GV2ptr TD (getPointerSize TD) gvp); try solve [inversion H3].
  destruct v0; try solve [inversion H3].
  destruct (typ2memory_chunk t); try solve [inversion H3].
  destruct (GV2val TD gv); try solve [inversion H3].
  destruct Hwf as [Hwfr Hwfm].
  split.
    clear Hwfm.
    intros i1 gvb gve J.
    apply Hwfr in J. clear Hwfr.
    unfold wf_data in *.
    destruct (GV2ptr TD (getPointerSize TD) gvb); auto.
    destruct v1; auto.
    destruct (GV2ptr TD (getPointerSize TD) gve); auto.
    destruct v1; auto.
    destruct (zeq b0 b1); eauto using store_range_perm_1.

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
      intros ofs J.
      admit. (* J is false. *)

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

Case "dbLib". admit.
Case "dbLib_error". admit.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
