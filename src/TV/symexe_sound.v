Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import trace.
Require Import symexe_def.
Require Import symexe_complete.
Require Import assoclist.
Require Import ssa_props.

Export SimpleSE.

(* Symbolic execuction is sound:
   Given a concrete initial state and that its symbolic execution results
   denote some concrete states w.r.t the initial state, it is possible to
   execute the subblock to completion from this initial state. *)

Lemma value2Sterm_denotes__implies__genericvalue : forall TD lc0 Mem0 smap1 lc gl v gv,
  uniq smap1 ->
  dom lc0 [<=] dom smap1 ->
  smap_denotes_gvmap TD lc0 gl Mem0 smap1 lc ->
  sterm_denotes_genericvalue TD lc0 gl Mem0 (value2Sterm smap1 v) gv ->
  getOperandValue TD v lc gl = Some gv.
Proof.
  intros D lc0 Mem0 smap1 lc gl v gv Huniq Hsub Hdenotes J.
  unfold smap_denotes_gvmap in Hdenotes.
  destruct Hdenotes as [J1 J2].
  destruct v.
    destruct (@AtomSetProperties.In_dec i0 (dom smap1)) as [i0_in_sstate1 | i0_notin_sstate1].
      apply binds_In_inv in i0_in_sstate1.
      destruct i0_in_sstate1 as [st0 Binds].
      rewrite id2Sterm_in with (st0:=st0) in J; auto.
      apply J1 with (id':=i0) in Binds.
      destruct Binds as [gv' [J3 J4]].
      apply sterm_denotes_genericvalue_det with (gv2:=gv') in J; auto.
      subst. auto.

      rewrite id2Sterm_notin in J; auto.
      inversion J; subst.
      simpl in H4.
      apply lookupAL_Some_indom in H4.
      clear - i0_notin_sstate1 H4 Hsub.
      contradict H4; fsetdec.
    rewrite const2Sterm in J.
    inversion J. auto.
Qed.

Lemma value2Sterm_denote__imply__genericvalues : forall l0 TD lc0 Mem0 smap1 lc gl gvs0,
  uniq smap1 ->
  dom lc0 [<=] dom smap1 ->
  smap_denotes_gvmap TD lc0 gl Mem0 smap1 lc ->
  sterms_denote_genericvalues TD lc0 gl Mem0 
    (map_list_value (value2Sterm smap1) l0) gvs0 ->
  values2GVs TD l0 lc gl = Some gvs0.
Proof.
  induction l0; intros; simpl in *.
    inversion H2; subst; auto.

    inversion H2; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    rewrite H11.
    erewrite IHl0; eauto.
Qed.

Lemma aux__se_cmd__denotes__exists_op_cmd : forall TD c nc lc als gl Mem1 lc' als' Mem2 lc0 als0 Mem0 sstate1 tr1 tr2,
  uniq sstate1.(STerms) ->
  dom lc0 [<=] dom (STerms sstate1) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 sstate1 lc als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmd sstate1 (mkNB c nc)) lc' als' Mem2 tr2 ->
  exists lc',  exists als', exists Mem2, exists tr,
    dbCmd TD gl lc als Mem1 c lc' als' Mem2 tr /\
    tr2 = trace_app tr1 tr.
Proof.
  intros TD c nc lc als gl Mem1 lc' als' Mem2 lc0 als0 Mem0 sstate1 tr1 tr2 
    Huniq Hsub Hdenotes1 Hdenotes2.
  destruct Hdenotes2 as [[Hsterms_denote21 Hsterms_denote22] [Hsmem_denotes2 [Hsframe_denotes2 Hseffects_denote2]]].
  destruct Hdenotes1 as [Hsterms_denote1 [Hsmem_denotes1 [Hsframe_denotes1 Hseffects_denote1]]].
  inversion Hseffects_denote1; subst.
  inversion Hseffects_denote2; subst.
  (cmd_cases (destruct c) Case).
  Case "insn_bop".
    assert (binds i0  
             (sterm_bop b s (value2Sterm (STerms sstate1) v)
                            (value2Sterm (STerms sstate1) v0))
             (STerms (se_cmd sstate1 (mkNB (insn_bop i0 b s v v0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv3 [bop_denotes_gv3 gv3_in_env']].
    inversion bop_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    exists (updateAddAL _ lc i0 gv3). exists als. exists Mem1. exists trace_nil. 
    assert (BOP TD lc gl b s v v0 = Some gv3) as J.
      unfold BOP. rewrite H10. rewrite H11. auto.
    split; eauto.

  Case "insn_extractvalue".
    assert (binds i0  
             (sterm_extractvalue t
                            (value2Sterm (STerms sstate1) v)
                            l0)
             (STerms (se_cmd sstate1 (mkNB (insn_extractvalue i0 t v l0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [extractvalue_denotes_gv' gv_in_env']].
    inversion extractvalue_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H9; auto.
    exists (updateAddAL _ lc i0 gv'). exists als. exists Mem1. exists trace_nil.
    split; eauto.

  Case "insn_insertvalue".
    assert (binds i0  
             (sterm_insertvalue t
                            (value2Sterm (STerms sstate1) v)
                            t0
                            (value2Sterm (STerms sstate1) v0)
                            l0)
             (STerms (se_cmd sstate1 (mkNB (insn_insertvalue i0 t v t0 v0 l0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [insertvalue_denotes_gv' gv_in_env']].
    inversion insertvalue_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H12; auto.
    exists (updateAddAL _ lc i0 gv'). exists als. exists Mem1. exists trace_nil.
    split; eauto.

  Case "insn_malloc".
    assert (binds i0  
             (sterm_malloc (SMem sstate1) t s a)
             (STerms (se_cmd sstate1 (mkNB (insn_malloc i0 t s a) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [malloc_denotes_gv' gv_in_env']].
    inversion malloc_denotes_gv'; subst.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H10; auto.
    subst.
    exists (updateAddAL _ lc i0 (ptr2GV TD (mb, 0))). exists als. exists Mem5. exists trace_nil.
    split; eauto.

  Case "insn_free".
    inversion Hsmem_denotes2; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H4; auto.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H9; auto.
    subst.
    exists lc. exists als. exists Mem2. exists trace_nil.
    assert (getOperandPtr TD v lc gl = Some mptr0) as J.
      unfold getOperandPtr. rewrite H4. auto.
    split; eauto.

  Case "insn_alloca".
    assert (binds i0  
             (sterm_alloca (SMem sstate1) t s a)
             (STerms (se_cmd sstate1 (mkNB (insn_alloca i0 t s a) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [alloca_denotes_gv' gv_in_env']].
    inversion alloca_denotes_gv'; subst.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H10; auto.
    subst.
    exists (updateAddAL _ lc i0 (ptr2GV TD (mb, 0))). exists (mb::als). exists Mem5. exists trace_nil.
    split; eauto.

  Case "insn_load".
    assert (binds i0  
             (sterm_load (SMem sstate1)
                         t
                         (value2Sterm (STerms sstate1) v))
             (STerms (se_cmd sstate1 (mkNB (insn_load i0 t v) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [load_denotes_gv' gv_in_env']].
    inversion load_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H4; auto.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H9; auto.
    subst.
    exists (updateAddAL _ lc i0 gv'). exists als. exists Mem1. exists trace_nil.
    assert (getOperandPtr TD v lc gl = Some mp0) as J.
      unfold getOperandPtr. rewrite H4. auto.
    split; eauto.

  Case "insn_store".
    inversion Hsmem_denotes2; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H5; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H12; auto.
    subst.
    exists lc. exists als. exists Mem2. exists trace_nil.
    assert (getOperandPtr TD v0 lc gl = Some mptr2) as J.
      unfold getOperandPtr. rewrite H10. auto.
    split; eauto.

  Case "insn_gep".
    assert (binds i0  
             (sterm_gep i1
                        t
                        (value2Sterm (STerms sstate1) v) (map_list_value (value2Sterm (STerms sstate1)) l0))
             (STerms (se_cmd sstate1 (mkNB (insn_gep i0 i1 t v l0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [gep_denotes_gv' gv_in_env']].
    inversion gep_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H5; auto.
    apply value2Sterm_denote__imply__genericvalues with (lc:=lc)(gl:=gl) in H10; auto.
    exists (updateAddAL _ lc i0 (ptr2GV TD mp1)). exists als. exists Mem1. exists trace_nil.
    assert (getOperandPtr TD v lc gl = Some mp0) as J.
      unfold getOperandPtr. rewrite H5. auto.
    assert (GEP TD lc gl t mp0 l0 i1 = Some mp1) as J'.
      unfold GEP.
      rewrite <- values2GVs_GVs2Nats__intValues2Nats with (gvs0:=gvs0); auto.
      rewrite H13. auto.
    split; eauto.

  Case "insn_ext".
    assert (binds i0  
             (sterm_ext e t (value2Sterm (STerms sstate1) v) t0)
             (STerms (se_cmd sstate1 (mkNB (insn_ext i0 e t v t0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv3 [ext_denotes_gv3 gv3_in_env']].
    inversion ext_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    exists (updateAddAL _ lc i0 gv3). exists als. exists Mem1. exists trace_nil. 
    assert (EXT TD lc gl e t v t0 = Some gv3) as J.
      unfold EXT. rewrite H10. auto.
    split; eauto.

  Case "insn_cast".
    assert (binds i0  
             (sterm_cast c t (value2Sterm (STerms sstate1) v) t0)
             (STerms (se_cmd sstate1 (mkNB (insn_cast i0 c t v t0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv3 [cast_denotes_gv3 gv3_in_env']].
    inversion cast_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    exists (updateAddAL _ lc i0 gv3). exists als. exists Mem1. exists trace_nil. 
    assert (CAST TD lc gl c t v t0 = Some gv3) as J.
      unfold CAST. rewrite H10. auto.
    split; eauto.

  Case "insn_icmp".
    assert (binds i0  
             (sterm_icmp c t (value2Sterm (STerms sstate1) v)
                             (value2Sterm (STerms sstate1) v0))
             (STerms (se_cmd sstate1 (mkNB (insn_icmp i0 c t v v0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv3 [icmp_denotes_gv3 gv3_in_env']].
    inversion icmp_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    exists (updateAddAL _ lc i0 gv3). exists als. exists Mem1. exists trace_nil. 
    assert (ICMP TD lc gl c t v v0 = Some gv3) as J.
      unfold ICMP. rewrite H10. rewrite H11. auto.
    split; eauto.

  Case "insn_select".
    assert (binds i0  
             (sterm_select (value2Sterm (STerms sstate1) v)
                           t
                           (value2Sterm (STerms sstate1) v0)
                           (value2Sterm (STerms sstate1) v1))
             (STerms (se_cmd sstate1 (mkNB (insn_select i0 v t v0 v1) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv3 [select_denotes_gv3 gv3_in_env']].
    inversion select_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H5; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H12; auto.
    exists (if c0 then updateAddAL _ lc i0 gv1 else updateAddAL _ lc i0 gv2). exists als. exists Mem1. exists trace_nil. 
    assert (getOperandInt TD 1 v lc gl = Some c0) as J.
      unfold getOperandInt. rewrite H5. auto.
    split; eauto.

  Case "insn_call".
    inversion nc.
Qed.

Lemma aux__se_cmd__denotes__op_cmd : forall TD c nc lc als gl Mem1 lc' als' Mem2 lc0 als0 Mem0 sstate1 tr1 tr2,
  uniq sstate1.(STerms) ->
  dom lc0 [<=] dom (STerms sstate1) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 sstate1 lc als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmd sstate1 (mkNB c nc)) lc' als' Mem2 tr2 ->
  exists tr, exists slc,
    dbCmd TD gl lc als Mem1 c slc als' Mem2 tr /\
    tr2 = trace_app tr1 tr /\
    eqAL _ slc lc'.
Proof.
  intros TD c nc lc als gl Mem1 lc' als' Mem2 lc0 als0 Mem0 sstate1 tr1 tr2 
    Huniq Hsub Hdenotes1 Hdenotes2.
  assert (J:=Hdenotes2).
  apply aux__se_cmd__denotes__exists_op_cmd with
    (lc:=lc)(als:=als)(gl:=gl)(Mem1:=Mem1)(tr1:=tr1)(c:=c) in J; simpl; auto.
  destruct J as [lc'' [als'' [Mem2' [tr [HdbCmd EQ]]]]]; subst.
  assert (Hdenotes2':=HdbCmd).
  apply op_cmd__satisfies__se_cmd with (lc0:=lc0)(als0:=als0)(Mem0:=Mem0)(sstate1:=sstate1)(tr1:=tr1)(nc:=nc) in Hdenotes2'; auto.
  apply sstate_denotes_state_det with (lc2:=lc')(als2:=als')(Mem2:=Mem2)(tr2:=trace_app tr1 tr) in Hdenotes2'; auto.
  destruct Hdenotes2' as [EQ1 [EQ2 [EQ3 EQ4]]]; subst.
  exists tr. exists lc''. split; auto.
Qed.

Lemma se_cmd__denotes__op_cmd : forall TD c nc lc als gl Mem1 lc' als' Mem2 tr,
  uniq lc ->
  sstate_denotes_state TD lc gl als Mem1 (se_cmd (mkSstate (locals_to_smap lc) smem_init sframe_init nil) (mkNB c nc)) lc' als' Mem2 tr ->
  exists slc,
    dbCmd TD gl lc als Mem1 c slc als' Mem2 tr /\ eqAL _ slc lc'. 
Proof.
  intros TD c nc lc als gl Mem1 lc' als' Mem2 tr Huniqc Hdenotes.
  assert (J:=Hdenotes).
  apply aux__se_cmd__denotes__op_cmd with
    (lc:=lc)(gl:=gl)(Mem1:=Mem1)(tr1:=trace_nil)(als:=als)(c:=c) in J; simpl; auto.
    simpl in J. destruct J as [tr0 [slc [J1 [J2 J3]]]]; subst. 
    exists slc.  split; auto.

    apply locals_to_smap_uniq.
    rewrite locals_to_smap_dom_eq. fsetdec.
    apply locals_to_smap_denotes_id; auto.
Qed.

Lemma binds_se_cmd : forall c nc i0 i1 st0 smap1 smem1 sframe1 seffects1,
  binds i0 st0 smap1 ->
  getCmdID c = i1 ->
  i0 <> i1 ->
  binds i0 st0 (STerms (se_cmd (mkSstate smap1 smem1 sframe1 seffects1) (mkNB c nc) )).
Proof.
  destruct c; intros nc id0 id1 st0 smap1 smem1 sframe1 seffects1 Hbinds 
                     HgetCmdID id0_isnt_id1; simpl;
    simpl in HgetCmdID; subst; auto using binds_updateAddAL_neq.
    inversion nc.
Qed.
  
Lemma binds_se_cmds_onlyif : forall nbs i0 st0 smap1 smem1 sframe1 seffects1 c nc,
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->  
  getCmdID c = i0 ->
  binds i0 st0 smap1 ->
  binds i0 st0 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)).
Proof.
  induction nbs; intros i0 st0 smap1 smem1 sframe1 seffects1 c nc Hwf HgetCmdID Hbinds; simpl in *; auto.
    remember (se_cmd (mkSstate smap1 smem1 sframe1 seffects1) a) as R.
    destruct R as [smap0 smem0 sframe0 seffects0].
    apply IHnbs with (c:=c)(nc:=nc); auto.
      apply wf_nbranchs__inv in Hwf; auto.

      inversion Hwf; subst.
      apply cmds2nbs__nbranchs2cmds in H.
      simpl in H.
      destruct a.
      rewrite <- H in H0.
      simpl in H0.
      inversion H0; subst.
      rewrite nbranchs2cmds_app in H3.
      rewrite getCmdsIDs_app in H3.
      apply NotIn_inv in H3.
      destruct H3 as [_ H3].
      simpl in H3.
      assert (getCmdID c <> getCmdID nbranching_cmd0) as neq.
        destruct (getCmdID c == getCmdID nbranching_cmd0); auto.
      destruct nbranching_cmd0; simpl in HeqR; inversion HeqR; subst; 
        try solve [
          auto | 
          apply binds_updateAddAL_neq; auto |
          simpl in notcall0; inversion notcall0 
        ].
Qed.
         
Lemma binds_se_cmds_strengthen : forall nbs i1 st1 smap1 smem1 sframe1 seffects1,
  uniq smap1 ->
  binds i1 st1 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)) ->
  ~ In i1 (getCmdsIDs (nbranchs2cmds nbs)) ->
  binds i1 st1 smap1.
Proof.
  induction nbs; intros i1 st1 smap1 smem1 sframe1 seffects1 Uniq Binds i1_notin; simpl in *; auto.
    destruct a.
    destruct nbranching_cmd0; simpl in *; try solve [
      apply IHnbs in Binds; auto using updateAddAL_uniq;
        apply updateAddAL_inversion in Binds; auto;
        destruct Binds as [[_ J] | [EQ1 EQ2]]; subst; try solve [auto|contradict i1_notin; auto] |
      simpl in notcall0; inversion notcall0 
     ].
Qed.

Lemma binds_se_cmds_weaken : forall nbs i1 st1 smap1 smem1 sframe1 seffects1,
  uniq smap1 ->
  binds i1 st1 smap1 ->
  ~ In i1 (getCmdsIDs (nbranchs2cmds nbs)) ->
  binds i1 st1 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)).
Proof.
  induction nbs; intros i1 st1 smap1 smem1 sframe1 seffects1 Uniq Binds i1_notin; simpl in *; auto.
    destruct a.
    destruct nbranching_cmd0; simpl; try solve [
      simpl in i1_notin;
      apply IHnbs; auto using updateAddAL_uniq, binds_updateAddAL_neq |
      simpl in notcall0; inversion notcall0 
    ].
Qed.

Lemma _binds_se_cmds_if : forall nbs i1 st1 smap1 smem1 sframe1 seffects1 i0 st0,
  uniq smap1 ->
  binds i1 st1 (STerms (se_cmds (mkSstate (updateAddAL _ smap1 i0 st0) smem1 sframe1 seffects1) nbs)) ->
  ~ In i1 (getCmdsIDs (nbranchs2cmds nbs)) ->
  i1 <> i0 ->
  binds i1 st1 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)).
Proof.
  intros nbs i1 st1 smap1 smem1 sframe1 seffects1 i0 st0 Uniq Binds i1_notin i1_isnt_i0.
  apply binds_se_cmds_strengthen in Binds; auto.
    apply updateAddAL_inversion in Binds; auto.
      destruct Binds as [[_ BInds] | [EQ1 EQ2]]; subst.
        apply binds_se_cmds_weaken; auto.
        contradict i1_isnt_i0; auto.
      apply updateAddAL_uniq; auto.
Qed.

Lemma binds_se_cmds_if : forall nbs i0 st0 smap1 smem1 sframe1 seffects1 c nc,
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->  
  getCmdID c = i0 ->
  uniq smap1 ->
  binds i0 st0 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)) ->
  binds i0 st0 smap1.
Proof.
  induction nbs; intros i0 st0 smap1 smem1 sframe1 seffects1 c nc Hwf HgetCmdID Uniq Hbinds; simpl in *; auto.
    remember (se_cmd (mkSstate smap1 smem1 sframe1 seffects1) a) as R.
    destruct R as [smap0 smem0 sframe0 seffects0].
    apply IHnbs with (c:=c)(nc:=nc)(smem1:=smem0)(sframe1:=sframe0)(seffects1:=seffects0); auto.
      apply wf_nbranchs__inv in Hwf; auto.

      inversion Hwf; subst.
      apply cmds2nbs__nbranchs2cmds in H.
      simpl in H.
      destruct a.
      rewrite <- H in H0.
      simpl in H0.
      inversion H0; subst.
      rewrite nbranchs2cmds_app in H3.
      rewrite getCmdsIDs_app in H3.
      apply NotIn_inv in H3.
      destruct H3 as [_ H3].
      simpl in H3.
      assert (getCmdID c <> getCmdID nbranching_cmd0) as neq.
        destruct (getCmdID c == getCmdID nbranching_cmd0); auto.
      assert (~ In (getCmdID c) (getCmdsIDs (nbranchs2cmds nbs))) as notin.
        rewrite nbranchs2cmds_app in H4.
        rewrite getCmdsIDs_app in H4.
        simpl in H4.
        apply NoDup_last_inv; auto.
      destruct nbranching_cmd0; simpl in HeqR; inversion HeqR; subst; 
        try solve [
          auto | 
          eapply _binds_se_cmds_if; eauto |
          simpl in notcall0; inversion notcall0 
        ].
Qed.

Lemma binds_se_cmds : forall i0 st0 smap1 smem1 sframe1 seffects1 nbs c nc,
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->  
  getCmdID c = i0 ->
  binds i0 st0 smap1 ->
  binds i0 st0 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)).
Proof.
  intros i0 st0 smap1 smem1 sframe1 seffects1 nbs c nc H1 H2.
  eapply binds_se_cmds_onlyif; eauto.
Qed.

Lemma binds_se_cmds__prefix_last : forall nbs c nc id' st' smap1 smem1 sframe1 seffects1 i0,
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->  
  binds id' st' (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)) ->
  getCmdID c = i0 ->
  uniq smap1 ->
  (id'=i0 /\ binds id' st' smap1) \/ 
  (id' <> i0 /\ 
   binds id' st' 
    (STerms (se_cmd 
              (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) 
               nbs) 
             (mkNB c nc))
     )
  ).
Proof.
  intros nbs c nc id' st' smap1 smem1 sframe1 seffects1 i0 Wf Binds GetCmdID Uniq.
  destruct (i0==id'); subst.
    left. split; auto.
      eapply binds_se_cmds_if; eauto.
    right. split; auto.
      apply binds_se_cmd with (i1:=getCmdID c) ; auto.
Qed.

Lemma se_cmd_updateAddAL_inv : forall c nc st,
  STerms (se_cmd st (mkNB c nc)) = STerms st \/
  (exists st0, (STerms (se_cmd st (mkNB c nc))) = updateAddAL _ (STerms st) (getCmdID c) st0).
Proof.
  destruct c; intros; simpl; auto.
    right. 
    exists (sterm_bop b s 
                     (value2Sterm st.(STerms) v)
                     (value2Sterm st.(STerms) v0)). auto.
    right. 
    exists (sterm_extractvalue t
                     (value2Sterm st.(STerms) v)
                     l0). auto.

    right. 
    exists (sterm_insertvalue 
                     t 
                     (value2Sterm st.(STerms) v)
                     t0 
                     (value2Sterm st.(STerms) v0)
                     l0). auto.

    right. 
    exists (sterm_malloc st.(SMem) t s a). auto.

    right. 
    exists (sterm_alloca st.(SMem) t s a). auto.

    right. 
    exists (sterm_load st.(SMem) t 
                     (value2Sterm st.(STerms) v)). auto.

    right. 
    exists (sterm_gep i1 t
                     (value2Sterm st.(STerms) v)
                     (map_list_value (value2Sterm st.(STerms)) l0)). auto.

    right. 
    exists (sterm_ext e t
                     (value2Sterm st.(STerms) v)
                     t0). auto.

    right. 
    exists (sterm_cast c t
                     (value2Sterm st.(STerms) v)
                     t0). auto.

    right. 
    exists (sterm_icmp c t
                     (value2Sterm st.(STerms) v)
                     (value2Sterm st.(STerms) v0)). auto.

    right. 
    exists (sterm_select 
                     (value2Sterm st.(STerms) v)
                     t
                     (value2Sterm st.(STerms) v0)
                     (value2Sterm st.(STerms) v1)). auto.

    inversion nc.
Qed.

Lemma smap_denotes_gvmap_rollbackEnv : forall TD lc0 gl Mem0 nbs c nc lc2 gv3 i0,
  uniq lc0 ->
  uniq lc2 ->
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->
  smap_denotes_gvmap TD lc0 gl Mem0 (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB c nc))) lc2 ->
  lookupAL _ lc2 i0 = Some gv3 ->
  getCmdID c = i0 ->
  smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))
              (rollbackAL _ lc2 i0 lc0).
Proof.
  intros TD lc0 gl Mem0 nbs c nc lc2 gv3 i0
        Huniqc0 Huniqc2 Wf [Hsterms_denote1 Hsterms_denote2] gv3_in_env2 HgetCmdID.
  assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
    apply rollbackAL_uniq; auto.
  split; intros.
        apply binds_se_cmds__prefix_last with (c:=c)(i0:=i0)(nc:=nc) in H; auto using locals_to_smap_uniq.
        destruct H as [[id'_is_i0 binds_id'_st'] | [i0_isnt_id' binds_id'_st']]; subst.
          apply locals_to_smap_denotes__imples__gv with (TD:=TD)(Mem0:=Mem0)(gl:=gl) in binds_id'_st'; auto.
          destruct binds_id'_st' as [gv0 [st'_denotes_gv0 i0_gv0_in_env0]].
          exists gv0. 
          erewrite lookupAL_rollbackAL_Some_eq; eauto.

          apply Hsterms_denote1 in binds_id'_st'.
          destruct binds_id'_st' as [gv' [st'_denotes_gv' id'_gv'_in_env2]].
          erewrite <- lookupAL_rollbackAL_neq with (id1:=id'); eauto.

        destruct (i0==id'); subst.
          rewrite <- e in H.
          erewrite lookupAL_rollbackAL_eq in H; eauto.
          exists (sterm_val (value_id id')).
          rewrite <- e.
          split; auto.
            apply binds_se_cmds with (c:=c)(nc:=nc); auto.
            eapply lookupAL_locals_to_smap; eauto.

          rewrite <- lookupAL_rollbackAL_neq with (id1:=id') in H; auto.
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          exists st'. split; auto.
            destruct (@se_cmd_updateAddAL_inv c nc (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) as [J1 | [st0 J1]];
              rewrite J1 in binds_id'_st'; auto.
              apply updateAddAL_inversion in binds_id'_st'; auto. 
                destruct binds_id'_st' as [[_ binds_id'_st'] | [i0_is_id' binds_id'_st']]; auto.
                  contradict i0_is_id'; auto.
                eauto using locals_to_smap_uniq, se_cmds_uniq.
Qed.

Lemma se_cmds_denotes__decomposes__prefix_last__case1 : forall id' st' gl lc2 i0 TD Mem2 lc0,
  uniq (rollbackAL _ lc2 i0 lc0) ->
  i0 <> id' ->
  binds id' st' (locals_to_smap (rollbackAL _ lc2 i0 lc0)) ->
  exists gv', sterm_denotes_genericvalue TD (rollbackAL _ lc2 i0 lc0) gl Mem2 st' gv' /\ 
  lookupAL _ lc2 id' = Some gv'.
Proof.
  intros id' st' gl lc2 i0 TD Mem2 lc0 Uniqc1 i0_isnt_id' binds_id'_st'.
            apply locals_to_smap_denotes__imples__gv with (TD:=TD)(Mem0:=Mem2)(gl:=gl) in binds_id'_st'; auto.
            destruct binds_id'_st' as [gv' [st'_denotes_gv' gv'_in_env1]].
            exists gv'. split; auto.
            rewrite <- lookupAL_rollbackAL_neq with (id1:=id') in gv'_in_env1; auto.
Qed.

Lemma se_cmds_denotes__decomposes__prefix_last__case2 : forall id' st' Mem0 gl lc2 i0 TD Mem2 lc0 c nc gv' nbs,
  uniq (rollbackAL _ lc2 i0 lc0) ->
  i0 <> id' ->
  getCmdID c = i0 ->
  lookupAL _ lc2 id' = Some gv' ->
  binds id' st' (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) ->
  sterm_denotes_genericvalue TD lc0 gl Mem0 st' gv' ->
  exists st'0, 
    binds id' st'0 (STerms (se_cmd (mkSstate (locals_to_smap (rollbackAL _ lc2 i0 lc0)) smem_init sframe_init nil) (mkNB c nc))) /\
    sterm_denotes_genericvalue TD (rollbackAL _ lc2 i0 lc0) gl Mem2 st'0 gv'.
Proof.
  intros id' st' Mem0 gl lc2 i0 TD Mem2 lc0 c nc gv' nbs Uniqc1 i0_isnt_id' HgetCmdID id'_in_env2 binds_id'_st' st'_denotes_gv'.
  exists (sterm_val (value_id id')).
  rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.
  split; auto.
    destruct (@se_cmd_updateAddAL_inv c nc (mkSstate (locals_to_smap (rollbackAL _ lc2 i0 lc0)) smem_init sframe_init nil)) as [J1 | [st0 J1]];
      rewrite J1.
      apply lookupAL_locals_to_smap with (gv0:=gv'); auto.

      rewrite <-HgetCmdID in i0_isnt_id'.
      apply binds_updateAddAL_neq; auto.      
      apply lookupAL_locals_to_smap with (gv0:=gv'); auto.
Qed.

Lemma se_cmds_denotes__decomposes__prefix_last : forall nb TD lc0 gl als0 Mem0 nbs lc2 als2 Mem2 tr,
  uniq lc0 ->
  uniq lc2 ->
  wf_nbranchs (nbs++(nb::nil)) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) nb) lc2 als2 Mem2 tr ->
  exists lc1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) lc1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl als1 Mem1 (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) nb) lc2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ 
    uniq lc1.
Proof.
  intros [c nc] TD lc0 gl als0 Mem0 nbs lc2 als2 Mem2 tr Huniqc0 Huniqc2 Wf Hdenotes.
  assert (uniq (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))) as Uniq1.
    eauto using locals_to_smap_uniq, se_cmds_uniq.
  assert (Hsub:=@se_cmds_locals_to_smap_dom_sub lc0 nbs).
  generalize dependent TD.
  generalize dependent lc0.
  generalize dependent gl.
  generalize dependent als0.
  generalize dependent Mem0.
  generalize dependent lc2.
  generalize dependent als2.
  generalize dependent Mem2.
  generalize dependent tr.
  generalize dependent nc.
  generalize dependent nbs.
  (cmd_cases (destruct c) Case);
    intros;
    destruct Hdenotes as [[Hsterms_denote1 Hsterms_denote2] [Hsmem_denotes [Hsframe_denotes Hseffects_denote]]].
  Case "insn_bop".
    assert (binds i0  
             (sterm_bop b s (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v)
                            (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v0))
             (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB (insn_bop i0 b s v v0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [bop_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2  i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_bop i0 b s v v0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateAddAL_inversion in H; auto using locals_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion bop_denotes_gv3; subst. clear bop_denotes_gv3.
            apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateAddAL_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(i0:=i0)(lc0:=lc0)(nbs:=nbs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_bop b s (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v) (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v0)).
              split; auto using binds_updateAddAL_eq.
                inversion bop_denotes_gv3; subst.
                apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

  Case "insn_extractvalue".
    assert (binds i0  
             (sterm_extractvalue t (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v) l0)
             (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB (insn_extractvalue i0 t v l0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [extractvalue_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_extractvalue i0 t v l0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateAddAL_inversion in H; auto using locals_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

            exists gv3. split; eauto using lookupAL_rollbackAL_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion extractvalue_denotes_gv3; subst. clear extractvalue_denotes_gv3.
            apply sterm_extractvalue_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateAddAL_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(i0:=i0)(lc0:=lc0)(nbs:=nbs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_extractvalue t (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v) l0).
              split; auto using binds_updateAddAL_eq.
                inversion extractvalue_denotes_gv3; subst.
                apply sterm_extractvalue_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.        

  Case "insn_insertvalue".
    assert (binds i0  
             (sterm_insertvalue t (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v) 
                                t0 (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v0) 
                                l0)
             (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB (insn_insertvalue i0 t v t0 v0 l0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [insertvalue_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_insertvalue i0 t v t0 v0 l0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateAddAL_inversion in H; auto using locals_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

            exists gv3. split; eauto using lookupAL_rollbackAL_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion insertvalue_denotes_gv3; subst. clear insertvalue_denotes_gv3.
            apply sterm_insertvalue_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateAddAL_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(i0:=i0)(lc0:=lc0)(nbs:=nbs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_insertvalue t (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v) t0 (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v0) l0).
              split; auto using binds_updateAddAL_eq.
                inversion insertvalue_denotes_gv3; subst.
                apply sterm_insertvalue_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.        


  Case "insn_malloc".
    assert (binds i0  
             (sterm_malloc (SMem (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) t s a)
             (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB (insn_malloc i0 t s a) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [malloc_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem3. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_malloc i0 t s a)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateAddAL_inversion in H; auto using locals_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

            exists gv3. split; eauto using lookupAL_rollbackAL_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion malloc_denotes_gv3; subst. clear malloc_denotes_gv3.
            apply smem_denotes_mem_det with (Mem2:=Mem4) in H8; auto. subst.
            rewrite H12 in H9. inversion H9; subst. clear H9.
            rewrite H10 in H13. inversion H13; subst. clear H13.
            eapply sterm_malloc_denotes; eauto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateAddAL_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(i0:=i0)(lc0:=lc0)(nbs:=nbs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_malloc smem_init t s a).
              split; auto using binds_updateAddAL_eq.
                inversion malloc_denotes_gv3; subst.
                apply smem_denotes_mem_det with (Mem2:=Mem4) in H8; auto. subst.
                rewrite H12 in H9. inversion H9; subst. clear H9.
                rewrite H10 in H13. inversion H13; subst. clear H13.
                eapply sterm_malloc_denotes; eauto.
      split; simpl; eauto.
    
  Case "insn_free".
    inversion Hsmem_denotes; subst.
    exists lc2. exists als2. exists Mem3. exists tr. exists trace_nil.
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
        split; auto.
    split; auto.
      split.
        split; intros.
          simpl in H.
          apply locals_to_smap_denotes__imples__gv with (TD:=TD)(Mem0:=Mem3)(gl:=gl) in H; auto.

          exists (sterm_val (value_id id')).
          split; auto.
            simpl.
            apply lookupAL_locals_to_smap with (gv0:=gv'); auto.
      split; simpl; eauto.
        apply value2Sterm_denotes__implies__genericvalue with (lc:=lc2) in H2; try solve [auto | split; auto].
        eapply smem_free_denotes; eauto 
                  using genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.        

  Case "insn_alloca".
    assert (binds i0  
             (sterm_alloca (SMem (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) t s a)
             (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB (insn_alloca i0 t s a) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [alloca_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    inversion Hsframe_denotes; subst.
    apply smem_denotes_mem_det with (Mem2:=Mem3) in H13; auto. subst.
    rewrite H9 in H15. inversion H15; subst. clear H15.
    rewrite H10 in H16. inversion H16; subst. clear H16.
    exists (rollbackAL _ lc2 i0 lc0). exists als3. exists Mem3. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_alloca i0 t s a)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateAddAL_inversion in H; auto using locals_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

            exists gv3. split; eauto using lookupAL_rollbackAL_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion alloca_denotes_gv3; subst. clear alloca_denotes_gv3.
            apply smem_denotes_mem_det with (Mem2:=Mem2) in H8; auto. subst.
            rewrite H12 in H9. inversion H9; subst. clear H9.
            rewrite H10 in H13. inversion H13; subst. clear H13.
            eapply sterm_alloca_denotes; eauto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateAddAL_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(i0:=i0)(lc0:=lc0)(nbs:=nbs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_alloca smem_init t s a).
              split; auto using binds_updateAddAL_eq.
                inversion alloca_denotes_gv3; subst.
                apply smem_denotes_mem_det with (Mem2:=Mem2) in H8; auto. subst.
                rewrite H12 in H9. inversion H9; subst. clear H9.
                rewrite H10 in H13. inversion H13; subst. clear H13.
                eapply sterm_alloca_denotes; eauto.
      split; simpl; eauto.   

  Case "insn_load".
    assert (binds i0  
             (sterm_load (SMem (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) 
                         t 
                         (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v))
             (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB (insn_load i0 t v) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [load_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_load i0 t v)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateAddAL_inversion in H; auto using locals_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

            exists gv3. split; eauto using lookupAL_rollbackAL_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion load_denotes_gv3; subst. clear load_denotes_gv3.
            apply smem_denotes_mem_det with (Mem2:=Mem2) in H8; auto. subst.
            eapply sterm_load_denotes with (gv0:=gv0); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateAddAL_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(i0:=i0)(lc0:=lc0)(nbs:=nbs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_load smem_init t (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v)).
              split; auto using binds_updateAddAL_eq.
                inversion load_denotes_gv3; subst.
                apply smem_denotes_mem_det with (Mem2:=Mem2) in H8; auto. subst.
                eapply sterm_load_denotes with (gv0:=gv0); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.        
      split; simpl; eauto.   

  Case "insn_store".
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists lc2. exists als2. exists Mem3. exists tr. exists trace_nil.
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
        split; auto.
    split; simpl; eauto.
      split.
        split; intros.
          simpl in H.
          apply locals_to_smap_denotes__imples__gv with (TD:=TD)(Mem0:=Mem3)(gl:=gl) in H; auto.

          exists (sterm_val (value_id id')).
          split; auto.
            simpl.
            apply lookupAL_locals_to_smap with (gv0:=gv'); auto.
      split; simpl; eauto.
        apply value2Sterm_denotes__implies__genericvalue with (lc:=lc2) in H3; try solve [auto | split; auto].
        apply value2Sterm_denotes__implies__genericvalue with (lc:=lc2) in H8; try solve [auto | split; auto].
        eapply smem_store_denotes; eauto 
                  using genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.        

  Case "insn_gep".
    assert (binds i0  
             (sterm_gep i1 t (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v)
                             (map_list_value (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))) l0))
             (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB (insn_gep i0 i1 t v l0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [gep_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_gep i0 i1 t v l0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateAddAL_inversion in H; auto using locals_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

            exists gv3. split; eauto using lookupAL_rollbackAL_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion gep_denotes_gv3; subst. clear gep_denotes_gv3.
            apply value2Sterm_denote__imply__genericvalues with (lc:=(rollbackAL _ lc2 id' lc0)) in H8; try solve [auto | split; auto].
            eapply sterm_gep_denotes with (gv0:=gv0)(gvs0:=gvs0); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.
              eapply genericvalues__imply__value2Sterm_denote; eauto using locals_to_smap_uniq, locals_to_smap_denotes_gvmap.
                rewrite locals_to_smap_dom_eq. fsetdec.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateAddAL_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(i0:=i0)(lc0:=lc0)(nbs:=nbs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_gep i1 t (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v) (map_list_value (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0))) l0)).
              split; auto using binds_updateAddAL_eq.
                inversion gep_denotes_gv3; subst.
                apply value2Sterm_denote__imply__genericvalues with (lc:=(rollbackAL _ lc2 id' lc0)) in H8; try solve [auto | split; auto].
                eapply sterm_gep_denotes with (gv0:=gv0)(gvs0:=gvs0); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.
                  eapply genericvalues__imply__value2Sterm_denote; eauto using locals_to_smap_uniq, locals_to_smap_denotes_gvmap.
                    rewrite locals_to_smap_dom_eq. fsetdec.

  Case "insn_ext".
    assert (binds i0  
             (sterm_ext e t (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v) t0)
             (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB (insn_ext i0 e t v t0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [ext_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_ext i0 e t v t0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateAddAL_inversion in H; auto using locals_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

            exists gv3. split; eauto using lookupAL_rollbackAL_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion ext_denotes_gv3; subst. clear ext_denotes_gv3.
            apply sterm_ext_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateAddAL_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(i0:=i0)(lc0:=lc0)(nbs:=nbs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_ext e t (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v) t0).
              split; auto using binds_updateAddAL_eq.
                inversion ext_denotes_gv3; subst.
                apply sterm_ext_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

  Case "insn_cast".
    assert (binds i0  
             (sterm_cast c t (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v) t0)
             (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB (insn_cast i0 c t v t0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [cast_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_cast i0 c t v t0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateAddAL_inversion in H; auto using locals_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

            exists gv3. split; eauto using lookupAL_rollbackAL_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion cast_denotes_gv3; subst. clear cast_denotes_gv3.
            apply sterm_cast_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateAddAL_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(i0:=i0)(lc0:=lc0)(nbs:=nbs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_cast c t (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v) t0).
              split; auto using binds_updateAddAL_eq.
                inversion cast_denotes_gv3; subst.
                apply sterm_cast_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

  Case "insn_icmp".
    assert (binds i0  
             (sterm_icmp c t (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v)
                             (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v0))
             (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB (insn_icmp i0 c t v v0) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [icmp_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_icmp i0 c t v v0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateAddAL_inversion in H; auto using locals_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

            exists gv3. split; eauto using lookupAL_rollbackAL_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion icmp_denotes_gv3; subst. clear icmp_denotes_gv3.
            apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateAddAL_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(i0:=i0)(lc0:=lc0)(nbs:=nbs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_icmp c t (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v) (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v0)).
              split; auto using binds_updateAddAL_eq.
                inversion icmp_denotes_gv3; subst.
                apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

  Case "insn_select".
    assert (binds i0  
             (sterm_select (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v)
                           t
                           (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v0)
                           (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v1))
             (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB (insn_select i0 v t v0 v1) nc)))) as J.
      simpl. apply binds_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [select_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_select i0 v t v0 v1)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateAddAL_inversion in H; auto using locals_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

            exists gv3. split; eauto using lookupAL_rollbackAL_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion select_denotes_gv3; subst. clear select_denotes_gv3.
            eapply sterm_select_denotes with (gv0:=gv0)(gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateAddAL_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(i0:=i0)(lc0:=lc0)(nbs:=nbs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_select (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v) t (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v0) (value2Sterm (locals_to_smap (rollbackAL _ lc2 id' lc0)) v1)).
              split; auto using binds_updateAddAL_eq.
                inversion select_denotes_gv3; subst.
                eapply sterm_select_denotes with (gv0:=gv0)(gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        locals_to_smap_uniq, locals_to_smap_denotes_gvmap.

  Case "insn_call". inversion nc.
Qed. 

Lemma se_cmds_denotes__composes__prefix_last__case1 : forall TD lc0 gl Mem0 nbs lc1 lc2 Mem1 id' st' c nc i0,
  smap_denotes_gvmap TD lc0 gl Mem0 (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) lc1 ->
  smap_denotes_gvmap TD lc1 gl Mem1 (STerms (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) (mkNB c nc))) lc2 ->
  getCmdID c = i0 ->
  i0 <> id' ->
  binds id' st' (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) ->
  exists gv', sterm_denotes_genericvalue TD lc0 gl Mem0 st' gv' /\ lookupAL _ lc2 id' = ret gv'.
Proof.
  intros TD lc0 gl Mem0 nbs lc1 lc2 Mem1 id' st' c nc i0 [Hsterms_denote11 Hsterms_denote12]
     [Hsterms_denote21 Hsterms_denote22] HgetCmdID i0_isnt_id' binds_id'_st'.
            assert (J:=binds_id'_st').
            apply Hsterms_denote11 in J.
            destruct J as [gv' [st'_denotes_gv' id'_gv'_in_env1]].
            apply lookupAL_locals_to_smap in id'_gv'_in_env1.
            apply binds_se_cmd with (i1:=i0)(smem1:=smem_init)(sframe1:=sframe_init)(seffects1:=nil)(c:=c)(nc:=nc) in id'_gv'_in_env1; auto.
            apply Hsterms_denote21 in id'_gv'_in_env1.
            destruct id'_gv'_in_env1 as [gv'0 [id'_denotes_gv'0 id'_gv'0_in_env2]].
            inversion id'_denotes_gv'0; subst.
            simpl in H4.
            apply Hsterms_denote12 in H4.
            destruct H4 as [st'0 [binds_id'_st'0 st'0_denotes_gv'0]].
            apply binds_unique with (b:=st'0) in binds_id'_st'; eauto using locals_to_smap_uniq, se_cmds_uniq.
            subst.
            apply sterm_denotes_genericvalue_det with (gv2:=gv') in st'0_denotes_gv'0; auto.
            subst.
            exists gv'. split; auto.
Qed.

Lemma se_cmds_denotes__composes__prefix_last__case2 : forall TD lc1 gl Mem1 lc0 Mem0 v gv1 nbs,  
  uniq lc1 ->
  smap_denotes_gvmap TD lc0 gl Mem0 (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) lc1 ->
  sterm_denotes_genericvalue TD lc1 gl Mem1 (value2Sterm (locals_to_smap lc1) v) gv1 ->
  sterm_denotes_genericvalue TD lc0 gl Mem0 (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v) gv1.
Proof.
  intros TD lc1 gl Mem1 lc0 Mem0 v gv1 nbs U1 H1 H2.
                apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1) in H2; auto.
                  apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1); auto using locals_to_smap_uniq, se_cmds_uniq.
                  apply locals_to_smap_uniq.
                  rewrite locals_to_smap_dom_eq. fsetdec.
                  apply locals_to_smap_denotes_gvmap; auto.
Qed.

Lemma se_cmds_denotes__composes__prefix_last__case3 : forall TD lc1 gl Mem1 lc0 Mem0 nbs c nc st' gv' id' i0,  
  uniq lc1 ->
  getCmdID c = i0 ->
  i0 <> id' ->
  binds id' st' (locals_to_smap lc1) ->
  smap_denotes_gvmap TD lc0 gl Mem0 (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) lc1 ->
  sterm_denotes_genericvalue TD lc1 gl Mem1 st' gv' ->
  exists st'0,
    binds id' st'0
      (STerms (se_cmd (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) (mkNB c nc))) /\
    sterm_denotes_genericvalue TD lc0 gl Mem0 st'0 gv'.
Proof.
  intros TD lc1 gl Mem1 lc0 Mem0 nbs c nc st' gv' id' i0 
    Uc1 HgetCmdID i0_isnt_id' binds_id'_st' [Hsterms_denote11 Hsterms_denote12] st'_denotes_gv'.
  apply binds_locals_to_smap in binds_id'_st'; auto.
  destruct binds_id'_st' as [EQ [gv id'_gv_in_env1]]; subst.
  assert (J:=id'_gv_in_env1).
  unfold getOperandValue in J.
  apply Hsterms_denote12 in J.
  destruct J as [st' [binds_id'_st' st'_denotes_gv]].
  inversion st'_denotes_gv'; subst.
  unfold getOperandValue in H4.
  rewrite id'_gv_in_env1 in H4.
  inversion H4; subst. clear H4.
  exists st'.
  split; auto.
    destruct (@se_cmd_updateAddAL_inv c nc (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) as [J1 | [st0 J1]];
      rewrite J1; auto.
      apply binds_updateAddAL_neq; auto.      
Qed.

Lemma se_cmds_denotes__composes__prefix_last : forall nb TD lc1 gl als1 Mem1 
  lc2 als2 Mem2 lc0 als0 Mem0 tr1 tr2 nbs ,
  uniq lc1 ->
  wf_nbranchs (nbs++(nb::nil)) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs) lc1 als1 Mem1 tr1 ->
  sstate_denotes_state TD lc1 gl als1 Mem1 (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) nb) lc2 als2 Mem2 tr2 ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) (nbs++nb::nil)) lc2 als2 Mem2 (trace_app tr1 tr2).
Proof.
  intros [c nc] TD lc1 gl als1 Mem1 lc2 als2 Mem2 lc0 als0 Mem0 tr1 tr2 nbs 
    Huniqc1 Wf Hdenotes1 Hdenotes2.
  assert (uniq (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))) as Uniq1.
    eauto using locals_to_smap_uniq, se_cmds_uniq.
  generalize dependent TD.
  generalize dependent lc0.
  generalize dependent gl.
  generalize dependent als0.
  generalize dependent Mem0.
  generalize dependent nbs.
  generalize dependent lc2.
  generalize dependent als2.
  generalize dependent Mem2.
  generalize dependent lc1.
  generalize dependent als1.
  generalize dependent Mem1.
  generalize dependent tr1.
  generalize dependent tr2.
  generalize dependent nc.
  (cmd_cases (destruct c) Case);
    intros;
    destruct Hdenotes1 as [JJ [Hsmem_denotes1 [Hsframe_denotes1 Hseffects_denote1]]];
    assert (Hsmap_denotes1:=JJ);
    destruct JJ as [Hsterms_denote11 Hsterms_denote12];
    destruct Hdenotes2 as [[Hsterms_denote21 Hsterms_denote22] [Hsmem_denotes2 [Hsframe_denotes2 Hseffects_denote2]]];
    rewrite se_cmds_rev_cons.
  Case "insn_bop".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateAddAL_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_bop i0 b s v v0)(nc:=nc)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_bop b s (value2Sterm (locals_to_smap lc1) v) (value2Sterm (locals_to_smap lc1) v0))
                    (STerms (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) (mkNB (insn_bop id' b s v v0) nc)))
            ) as binds_id'_bop.
              simpl. apply binds_updateAddAL_eq; auto.
            apply Hsterms_denote21 in binds_id'_bop.
            destruct binds_id'_bop as [gv' [bop_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion bop_denotes_gv'; subst.

              apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateAddAL_inversion in binds_id'_st'; auto using locals_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_bop b s 
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v)
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v0)).
          split.
            simpl. apply binds_updateAddAL_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.
 
  Case "insn_extractvalue".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateAddAL_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_extractvalue i0 t v l0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_extractvalue t (value2Sterm (locals_to_smap lc1) v) l0)
                    (STerms (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) (mkNB (insn_extractvalue id' t v l0) nc)))
            ) as binds_id'_extractvalue.
              simpl. apply binds_updateAddAL_eq; auto.
            apply Hsterms_denote21 in binds_id'_extractvalue.
            destruct binds_id'_extractvalue as [gv' [extractvalue_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion extractvalue_denotes_gv'; subst.

              apply sterm_extractvalue_denotes with (gv1:=gv1); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateAddAL_inversion in binds_id'_st'; auto using locals_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_extractvalue t
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v)
                   l0).
          split.
            simpl. apply binds_updateAddAL_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_extractvalue_denotes with (gv1:=gv1);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_insertvalue".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateAddAL_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_insertvalue i0 t v t0 v0 l0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_insertvalue t (value2Sterm (locals_to_smap lc1) v) t0 (value2Sterm (locals_to_smap lc1) v0) l0)
                    (STerms (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) (mkNB (insn_insertvalue id' t v t0 v0 l0) nc)))
            ) as binds_id'_insertvalue.
              simpl. apply binds_updateAddAL_eq; auto.
            apply Hsterms_denote21 in binds_id'_insertvalue.
            destruct binds_id'_insertvalue as [gv' [insertvalue_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion insertvalue_denotes_gv'; subst.

              apply sterm_insertvalue_denotes with (gv1:=gv1) (gv2:=gv2); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateAddAL_inversion in binds_id'_st'; auto using locals_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_insertvalue t
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v)
                   t0
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v0)
                   l0).
          split.
            simpl. apply binds_updateAddAL_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_insertvalue_denotes with (gv1:=gv1) (gv2:=gv2);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_malloc".
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateAddAL_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_malloc i0 t s a)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_malloc smem_init t s a)
                    (STerms (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) (mkNB (insn_malloc id' t s a) nc)))
            ) as binds_id'_malloc.
              simpl. apply binds_updateAddAL_eq; auto.
            apply Hsterms_denote21 in binds_id'_malloc.
            destruct binds_id'_malloc as [gv' [malloc_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion malloc_denotes_gv'; subst.

              inversion H8; subst.
              apply sterm_malloc_denotes with (Mem1:=Mem4)(Mem2:=Mem5)(tsz0:=tsz0); eauto.

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateAddAL_inversion in binds_id'_st'; auto using locals_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_malloc (SMem (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) t s a).
          split.
            simpl. apply binds_updateAddAL_eq; auto.
            inversion st'_denotes_gv'; subst.
            inversion H8; subst.
            apply sterm_malloc_denotes with (Mem1:=Mem4)(Mem2:=Mem5)(tsz0:=tsz0); eauto.

    split. clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22
                 Hsframe_denotes2 Hsframe_denotes1 Hseffects_denote2 Hseffects_denote1.
           inversion Hsmem_denotes2; subst.
           inversion H8; subst.
           simpl. eapply smem_malloc_denotes; eauto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_free".
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        assert (J:=H).
        apply Hsterms_denote11 in J.
        destruct J as [gv' [st'_denotes_gv' id'_gv'_in_env1]].
        apply lookupAL_locals_to_smap in id'_gv'_in_env1.
        apply Hsterms_denote21 in id'_gv'_in_env1.
        destruct id'_gv'_in_env1 as [gv'0 [id'_denotes_gv'0 id'_gv'0_in_env2]].
        inversion id'_denotes_gv'0; subst.
        simpl in H5.
        apply Hsterms_denote12 in H5.
        destruct H5 as [st'0 [binds_id'_st'0 st'0_denotes_gv'0]].
        apply binds_unique with (b:=st'0) in H; eauto using locals_to_smap_uniq, se_cmds_uniq.
        subst.
        apply sterm_denotes_genericvalue_det with (gv2:=gv') in st'0_denotes_gv'0; auto.
        subst.
        exists gv'. split; auto.

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply binds_locals_to_smap in binds_id'_st'; auto.
        destruct binds_id'_st' as [EQ [gv id'_gv_in_env1]]; subst.
        assert (J:=id'_gv_in_env1).
        unfold getOperandValue in J.
        apply Hsterms_denote12 in J.
        destruct J as [st' [binds_id'_st' st'_denotes_gv]].
        inversion st'_denotes_gv'; subst.
        unfold getOperandValue in H4.
        rewrite id'_gv_in_env1 in H4.
        inversion H4; subst. clear H4.
        exists st'.
        split; auto.

    split. clear Hsframe_denotes2 Hsframe_denotes1 Hseffects_denote2 Hseffects_denote1.
           inversion Hsmem_denotes2; subst.
           inversion H7; subst.
           simpl. 
           assert ((dom lc1) [<=] dom (locals_to_smap lc1)) as Sub.
             rewrite locals_to_smap_dom_eq. fsetdec.
           apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1) in H2; 
            try solve [eauto using locals_to_smap_uniq, locals_to_smap_denotes_gvmap| split; auto].
           eapply smem_free_denotes; eauto using genericvalue__implies__value2Sterm_denotes.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_alloca".
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateAddAL_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_alloca i0 t s a)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_alloca smem_init t s a)
                    (STerms (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) (mkNB (insn_alloca id' t s a) nc)))
            ) as binds_id'_alloca.
              simpl. apply binds_updateAddAL_eq; auto.
            apply Hsterms_denote21 in binds_id'_alloca.
            destruct binds_id'_alloca as [gv' [alloca_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion alloca_denotes_gv'; subst.

              inversion H8; subst. clear H8.
              apply sterm_alloca_denotes with (Mem1:=Mem4)(Mem2:=Mem5)(tsz0:=tsz0); eauto.

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateAddAL_inversion in binds_id'_st'; auto using locals_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_alloca (SMem (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) t s a).
          split.
            simpl. apply binds_updateAddAL_eq; auto.
            inversion st'_denotes_gv'; subst.
            inversion H8; subst. clear H8.
            apply sterm_alloca_denotes with (Mem1:=Mem4)(Mem2:=Mem5)(tsz0:=tsz0); eauto.

    split. clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22
                 Hsframe_denotes2 Hsframe_denotes1 Hseffects_denote2 Hseffects_denote1.
           inversion Hsmem_denotes2; subst.
           inversion H8; subst.
           simpl. eapply smem_alloca_denotes; eauto.
    split. clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22
                 Hseffects_denote2 Hseffects_denote1.
           inversion Hsframe_denotes2; subst.
           inversion H11; subst. clear H11.
           inversion H10; subst. clear H10.
           simpl. eapply sframe_alloca_denotes; eauto.

           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

   Case "insn_load".
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateAddAL_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_load i0 t v)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_load smem_init t (value2Sterm (locals_to_smap lc1) v))
                    (STerms (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) (mkNB (insn_load id' t v) nc)))
            ) as binds_id'_load.
              simpl. apply binds_updateAddAL_eq; auto.
            apply Hsterms_denote21 in binds_id'_load.
            destruct binds_id'_load as [gv' [load_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion load_denotes_gv'; subst.

              inversion H7; subst. clear H7.
              eapply sterm_load_denotes with (gv0:=gv0);
                try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem4); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateAddAL_inversion in binds_id'_st'; auto using locals_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_load (SMem (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) t
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v)).
          split.
            simpl. apply binds_updateAddAL_eq; auto.
            inversion st'_denotes_gv'; subst.
            inversion H7; subst. clear H7.
            eapply sterm_load_denotes with (gv0:=gv0);
                try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem4); auto].
    split. clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22
                 Hsframe_denotes2 Hsframe_denotes1 Hseffects_denote2 Hseffects_denote1.
           inversion Hsmem_denotes2; subst.
           inversion H7; subst.
           simpl. eapply smem_load_denotes; eauto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

   Case "insn_store".
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        assert (J:=H).
        apply Hsterms_denote11 in J.
        destruct J as [gv' [st'_denotes_gv' id'_gv'_in_env1]].
        apply lookupAL_locals_to_smap in id'_gv'_in_env1.
        apply Hsterms_denote21 in id'_gv'_in_env1.
        destruct id'_gv'_in_env1 as [gv'0 [id'_denotes_gv'0 id'_gv'0_in_env2]].
        inversion id'_denotes_gv'0; subst.
        simpl in H5.
        apply Hsterms_denote12 in H5.
        destruct H5 as [st'0 [binds_id'_st'0 st'0_denotes_gv'0]].
        apply binds_unique with (b:=st'0) in H; eauto using locals_to_smap_uniq, se_cmds_uniq.
        subst.
        apply sterm_denotes_genericvalue_det with (gv2:=gv') in st'0_denotes_gv'0; auto.
        subst.
        exists gv'. split; auto.

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply binds_locals_to_smap in binds_id'_st'; auto.
        destruct binds_id'_st' as [EQ [gv id'_gv_in_env1]]; subst.
        assert (J:=id'_gv_in_env1).
        unfold getOperandValue in J.
        apply Hsterms_denote12 in J.
        destruct J as [st' [binds_id'_st' st'_denotes_gv]].
        inversion st'_denotes_gv'; subst.
        unfold getOperandValue in H4.
        rewrite id'_gv_in_env1 in H4.
        inversion H4; subst. clear H4.
        exists st'.
        split; auto.

    split. clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22
                 Hsframe_denotes2 Hsframe_denotes1 Hseffects_denote2 Hseffects_denote1.
           inversion Hsmem_denotes2; subst.
           inversion H10; subst.
           simpl. 
           assert ((dom lc1) [<=] dom (locals_to_smap lc1)) as Sub.
             rewrite locals_to_smap_dom_eq. fsetdec.
           apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1) in H3; 
            try solve [eauto using locals_to_smap_uniq, locals_to_smap_denotes_gvmap| split; auto].
           apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1) in H8; 
            try solve [eauto using locals_to_smap_uniq, locals_to_smap_denotes_gvmap| split; auto].
           eapply smem_store_denotes; eauto using genericvalue__implies__value2Sterm_denotes.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_gep".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateAddAL_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_gep i0 i1 t v l0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_gep i1 t (value2Sterm (locals_to_smap lc1) v)
                              (map_list_value (value2Sterm (locals_to_smap lc1)) l0))
                    (STerms (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) (mkNB (insn_gep id' i1 t v l0) nc)))
            ) as binds_id'_gep.
              simpl. apply binds_updateAddAL_eq; auto.
            apply Hsterms_denote21 in binds_id'_gep.
            destruct binds_id'_gep as [gv' [gep_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion gep_denotes_gv'; subst.

              eapply sterm_gep_denotes with (gv0:=gv0)(gvs0:=gvs0);
                try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].
                apply value2Sterm_denote__imply__genericvalues with (lc:=lc1) in H8; auto.
                  apply genericvalues__imply__value2Sterm_denote with (lc:=lc1); auto using locals_to_smap_uniq, se_cmds_uniq.
                  apply se_cmds_locals_to_smap_dom_sub.
                  apply locals_to_smap_uniq.
                  rewrite locals_to_smap_dom_eq. fsetdec.
                  apply locals_to_smap_denotes_gvmap; auto.

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateAddAL_inversion in binds_id'_st'; auto using locals_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_gep i1 t 
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v)
                   (map_list_value (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs))) l0)).
          split.
            simpl. apply binds_updateAddAL_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_gep_denotes with (gv0:=gv0)(gvs0:=gvs0)(mp0:=mp0)(ns0:=ns0);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].
                apply value2Sterm_denote__imply__genericvalues with (lc:=lc1) in H8; auto.
                  apply genericvalues__imply__value2Sterm_denote with (lc:=lc1); auto using locals_to_smap_uniq, se_cmds_uniq.
                  apply se_cmds_locals_to_smap_dom_sub.
                  apply locals_to_smap_uniq.
                  rewrite locals_to_smap_dom_eq. fsetdec.
                  apply locals_to_smap_denotes_gvmap; auto.

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_ext".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateAddAL_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_ext i0 e t v t0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_ext e t (value2Sterm (locals_to_smap lc1) v) t0)
                    (STerms (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) (mkNB (insn_ext id' e t v t0) nc)))
            ) as binds_id'_ext.
              simpl. apply binds_updateAddAL_eq; auto.
            apply Hsterms_denote21 in binds_id'_ext.
            destruct binds_id'_ext as [gv' [ext_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion ext_denotes_gv'; subst.

              apply sterm_ext_denotes with (gv1:=gv1); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateAddAL_inversion in binds_id'_st'; auto using locals_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_ext e t
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v) t0).
          split.
            simpl. apply binds_updateAddAL_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_ext_denotes with (gv1:=gv1);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_cast".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateAddAL_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_cast i0 c t v t0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_cast c t (value2Sterm (locals_to_smap lc1) v) t0)
                    (STerms (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) (mkNB (insn_cast id' c t v t0) nc)))
            ) as binds_id'_cast.
              simpl. apply binds_updateAddAL_eq; auto.
            apply Hsterms_denote21 in binds_id'_cast.
            destruct binds_id'_cast as [gv' [cast_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion cast_denotes_gv'; subst.

              apply sterm_cast_denotes with (gv1:=gv1); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateAddAL_inversion in binds_id'_st'; auto using locals_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_cast c t 
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v) t0).
          split.
            simpl. apply binds_updateAddAL_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_cast_denotes with (gv1:=gv1);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_icmp".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateAddAL_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_icmp i0 c t v v0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_icmp c t (value2Sterm (locals_to_smap lc1) v) (value2Sterm (locals_to_smap lc1) v0))
                    (STerms (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) (mkNB (insn_icmp id' c t v v0) nc)))
            ) as binds_id'_icmp.
              simpl. apply binds_updateAddAL_eq; auto.
            apply Hsterms_denote21 in binds_id'_icmp.
            destruct binds_id'_icmp as [gv' [icmp_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion icmp_denotes_gv'; subst.

              apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateAddAL_inversion in binds_id'_st'; auto using locals_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_icmp c t
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v)
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v0)).
          split.
            simpl. apply binds_updateAddAL_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_select".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateAddAL_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_select i0 v t v0 v1)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_select (value2Sterm (locals_to_smap lc1) v) t (value2Sterm (locals_to_smap lc1) v0) (value2Sterm (locals_to_smap lc1) v1))
                    (STerms (se_cmd (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) (mkNB (insn_select id' v t v0 v1) nc)))
            ) as binds_id'_select.
              simpl. apply binds_updateAddAL_eq; auto.
            apply Hsterms_denote21 in binds_id'_select.
            destruct binds_id'_select as [gv' [select_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion select_denotes_gv'; subst.

              apply sterm_select_denotes with (gv0:=gv0)(c0:=c0)(gv1:=gv1)(gv2:=gv2); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateAddAL_inversion in binds_id'_st'; auto using locals_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_select
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v)
                   t
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v0)
                   (value2Sterm (STerms (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs)) v1)).
          split.
            simpl. apply binds_updateAddAL_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_select_denotes with (gv0:=gv0)(c0:=c0)(gv1:=gv1)(gv2:=gv2);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_call". inversion nc.
Qed.

Definition se_cmds_denotes__decomposes__app_prop (nbs2:list nbranch) :=
forall TD lc0 gl als0 Mem0 nbs1 lc2 als2 Mem2 tr,
  uniq lc0 ->
  uniq lc2 ->
  wf_nbranchs (nbs1++nbs2) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) (nbs1++nbs2)) lc2 als2 Mem2 tr ->
  exists lc1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nbs1) lc1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl als1 Mem1 (se_cmds (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) nbs2) lc2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ uniq lc1.

Lemma se_cmds_denotes__decomposes__app : forall nbs2, 
  se_cmds_denotes__decomposes__app_prop nbs2.
Proof.
  apply (@rev_ind nbranch); unfold se_cmds_denotes__decomposes__app_prop in *; intros; simpl.
  Case "nil".
    exists lc2. exists als2. exists Mem2. exists tr. exists trace_nil.
    rewrite trace_app_nil__eq__trace.
    rewrite <- app_nil_end in H2.
    split; auto.
    split; auto.
      apply locals_to_smap_denotes_id; auto.
  Case "cons".
    rewrite <- app_ass in H3.
    rewrite se_cmds_rev_cons in H3.
    rewrite <- app_ass in H2.
    apply se_cmds_denotes__decomposes__prefix_last in H3; auto.
    destruct H3 as [lc1 [als1 [Mem1 [tr1 [tr2 [env0_denotes_env1 [env1_denotes_env2 [EQ Huniqc1]]]]]]]]; subst.
    assert (J:=H2).
    apply wf_nbranchs__decomposes__app in J. 
    destruct J as [H41 H42].
    apply H in env0_denotes_env1; auto.
    destruct env0_denotes_env1 as [lc3 [als3 [Mem3 [tr3 [tr4 [env0_denotes_env3 [env3_denotes_env1 [EQ Huniqc3]]]]]]]]; subst.
    exists lc3. exists als3. exists Mem3. exists tr3. exists (trace_app tr4 tr2).
    rewrite trace_app_commute.
    split; auto.
    split; auto.
      rewrite app_ass in H2.
      apply wf_nbranchs__decomposes__app in H2. 
      destruct H2 as [H51 H52].
      apply se_cmds_denotes__composes__prefix_last with (lc1:=lc1)(als1:=als1)(Mem1:=Mem1); eauto.
Qed.

Lemma se_cmds_denotes__decomposes__head_tail : forall nb TD lc0 gl als0 Mem0 nbs lc2 als2 Mem2 tr,
  uniq lc0 ->
  uniq lc2 ->
  wf_nbranchs (nb::nbs) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds (se_cmd (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nb) nbs) lc2 als2 Mem2 tr ->
  exists lc1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmd (mkSstate (locals_to_smap lc0) smem_init sframe_init nil) nb) lc1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl als1 Mem1 (se_cmds (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) nbs) lc2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ uniq lc1.
Proof.
  intros nb TD lc0 gl als0 Mem0 cs lc2 als2 Mem2 tr Huniqc0 Huniqc2 Wf Hdenotes.
  rewrite <- se_cmds_cons in Hdenotes.
  apply se_cmds_denotes__decomposes__app in Hdenotes; auto.
Qed.    
  
Lemma se_cmds__denote__exists_op_cmds : forall nbs TD lc1 als1 gl Mem1 lc2 als2 Mem2 tr,
  uniq lc1 ->
  uniq lc2 ->
  wf_nbranchs nbs ->
  sstate_denotes_state TD lc1 gl als1 Mem1 (se_cmds (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) nbs) lc2 als2 Mem2 tr ->
  exists lc2', exists als2, exists Mem2', exists tr', 
    dbCmds TD gl lc1 als1 Mem1 (nbranchs2cmds nbs) lc2' als2 Mem2' tr' /\
    eqAL _ lc2' lc2.
Proof.
  induction nbs; 
    intros TD lc1 als1 gl Mem1 lc2 als2 Mem2 tr Uniqc1 Uniqc2 Wf Hdenotes.

    simpl in *. 
    exists lc1. exists als1. exists Mem2. exists trace_nil. 
    assert (J:=@locals_to_smap_denotes_id TD lc1 gl als1 Mem1 Uniqc1).
    apply sstate_denotes_state_det with (lc2:=lc2)(als2:=als2)(Mem2:=Mem2)(tr2:=tr) in J; auto.
    destruct J as [EQ1 [EQ2 [EQ3 EQ4]]]; subst; auto.

    simpl in Hdenotes.
    apply se_cmds_denotes__decomposes__head_tail in Hdenotes; auto.
    destruct Hdenotes as [lc3 [als3 [Mem3 [tr3 [tr3' [J1 [J2 [EQ Huniqc3]]]]]]]]; subst.
    destruct a as [c nc].
    apply se_cmd__denotes__op_cmd with
      (als:=als1)(c:=c) in J1; simpl; auto.
    destruct J1 as [slc [HdbCmd HeqEnv]].
    apply wf_nbranchs__inv in Wf.
    apply IHnbs in J2; simpl; auto.
    destruct J2 as [lc4 [als4 [Mem4 [tr4 [HdbCmds HeqEnv']]]]].
    apply dbCmds_eqEnv with (lc1':=slc) in HdbCmds; auto using eqAL_sym.
    destruct HdbCmds as [lc4' [HdbCmds' HeqEnv'']].
    exists lc4'. exists als4. exists Mem4. exists (trace_app tr3 tr4).
    split; eauto using eqAL_trans, eqAL_sym.      
Qed.

Lemma se_cmds__denote__op_cmds : forall TD nbs lc1 gl als1 Mem1 lc2 als2 Mem2 tr,
  uniq lc1 ->
  uniq lc2 ->
  wf_nbranchs nbs ->
  sstate_denotes_state TD lc1 gl als1 Mem1 (se_cmds (mkSstate (locals_to_smap lc1) smem_init sframe_init nil) nbs) lc2 als2 Mem2 tr ->
  exists slc,
    dbCmds TD gl lc1 als1 Mem1 (nbranchs2cmds nbs) slc als2 Mem2 tr /\
    eqAL _ slc lc2.
Proof.
  intros TD nbs lc1 gl als1 Mem1 lc2 als2 Mem2 tr Huniqc1 Huniqc2 Wf Hdenotes.
  assert (J:=Hdenotes).
  apply se_cmds__denote__exists_op_cmds with
     (lc1:=lc1)(als1:=als1)(Mem1:=Mem1) in J; simpl; auto.
  destruct J as [lc2' [als2' [Mem2' [tr' [HdbCmds HeqEnv]]]]].
  assert (Hdenotes':=HdbCmds).
  apply op_cmds__satisfy__se_cmds in Hdenotes'; auto.
  apply sstate_denotes_state_det with (lc2:=lc2)(als2:=als2)(Mem2:=Mem2)(tr2:=tr) in Hdenotes'; auto.
  destruct Hdenotes' as [EQ1 [EQ2 [EQ3 EQ4]]]; subst.
  exists lc2'. split; auto.
Qed.
