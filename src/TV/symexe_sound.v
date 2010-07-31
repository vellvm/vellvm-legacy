Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Export targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import trace.
Require Import symexe_def.
Require Import symexe_complete.

Export SimpleSE.

(* Symbolic execuction is sound:
   Given a concrete initial state and that its symbolic execution results
   denote some concrete states w.r.t the initial state, it is possible to
   execute the subblock to completion from this initial state. *)

Lemma value2Sterm_denotes__implies__genericvalue : forall TD lc0 gl0 Mem0 smap1 lc gl v gv,
  uniq smap1 ->
  (dom lc0 `union` dom gl0) [<=] dom smap1 ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 smap1 lc gl ->
  sterm_denotes_genericvalue TD lc0 gl0 Mem0 (value2Sterm smap1 v) gv ->
  getOperandValue TD v lc gl = Some gv.
Proof.
  intros D lc0 gl0 Mem0 smap1 lc gl v gv Huniq Hsub Hdenotes J.
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
      apply lookupEnv__indom in H4.
      clear - i0_notin_sstate1 H4 Hsub.
      contradict H4; fsetdec.
    rewrite const2Sterm in J.
    inversion J. auto.
Qed.

Lemma value2Sterm_denote__imply__genericvalues : forall l0 TD lc0 gl0 Mem0 smap1 lc gl gvs0,
  uniq smap1 ->
  (dom lc0 `union` dom gl0) [<=] dom smap1 ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 smap1 lc gl ->
  sterms_denote_genericvalues TD lc0 gl0 Mem0 
    (List.map (value2Sterm smap1) l0) gvs0 ->
  values2GVs TD l0 lc gl = Some gvs0.
Proof.
  induction l0; intros; simpl in *.
    inversion H2; subst; auto.

    inversion H2; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    rewrite H11.
    erewrite IHl0; eauto.
Qed.

Lemma aux__se_cmd__denotes__exists_op_cmd : forall S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl Mem1 lc' gl' als' Mem2 lc0 gl0 als0 Mem0 sstate1 tr1 tr2,
  uniq sstate1.(STerms) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 sstate1 lc gl als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd sstate1 c) lc' gl' als' Mem2 tr2 ->
  exists lc', exists gl', exists als', exists Mem2, exists tr,
    dbCmd (mkState S TD Ps ((mkEC F B ((subblock_intro (c::cs) call0)::sbs) tmn lc arg0 als)::ECs) gl Mem1)
          (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc' arg0 als')::ECs) gl' Mem2) 
          tr /\
    tr2 = trace_app tr1 tr.
Proof.
  intros S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl Mem1 lc' gl' als' Mem2 lc0 gl0 als0 Mem0 sstate1 tr1 tr2 Huniq Hsub Hdenotes1 Hdenotes2.
  destruct Hdenotes2 as [[Hsterms_denote21 Hsterms_denote22] [Hsmem_denotes2 [Hsframe_denotes2 Hseffects_denote2]]].
  destruct Hdenotes1 as [Hsterms_denote1 [Hsmem_denotes1 [Hsframe_denotes1 Hseffects_denote1]]].
  inversion Hseffects_denote1; subst.
  inversion Hseffects_denote2; subst.
  (cmd_cases (destruct c) Case).
  Case "insn_bop".
    assert (binds i0  
             (sterm_bop b s (value2Sterm (STerms sstate1) v)
                            (value2Sterm (STerms sstate1) v0))
             (STerms (se_cmd sstate1 (insn_bop i0 b s v v0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv3 [bop_denotes_gv3 gv3_in_env']].
    inversion bop_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 gv3).
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    exists lc2. exists gl2. exists als. exists Mem1. exists trace_nil. 
    assert (BOP TD lc gl b s v v0 = Some gv3) as J.
      unfold BOP. rewrite H10. rewrite H11. auto.
    split; eauto.

  Case "insn_extractvalue".
    assert (binds i0  
             (sterm_extractvalue t
                            (value2Sterm (STerms sstate1) v)
                            l0)
             (STerms (se_cmd sstate1 (insn_extractvalue i0 t v l0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [extractvalue_denotes_gv' gv_in_env']].
    inversion extractvalue_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H9; auto.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 gv').
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    exists lc2. exists gl2. exists als. exists Mem1. exists trace_nil.
    split; eauto.

  Case "insn_insertvalue".
    assert (binds i0  
             (sterm_insertvalue t
                            (value2Sterm (STerms sstate1) v)
                            t0
                            (value2Sterm (STerms sstate1) v0)
                            l0)
             (STerms (se_cmd sstate1 (insn_insertvalue i0 t v t0 v0 l0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [insertvalue_denotes_gv' gv_in_env']].
    inversion insertvalue_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H12; auto.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 gv').
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    exists lc2. exists gl2. exists als. exists Mem1. exists trace_nil.
    split; eauto.

  Case "insn_malloc".
    assert (binds i0  
             (sterm_malloc (SMem sstate1) t s a)
             (STerms (se_cmd sstate1 (insn_malloc i0 t s a)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [malloc_denotes_gv' gv_in_env']].
    inversion malloc_denotes_gv'; subst.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 (ptr2GV TD (mb, 0))).
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H10; auto.
    subst.
    exists lc2. exists gl2. exists als. exists Mem5. exists trace_nil.
    split; eauto.

  Case "insn_free".
    inversion Hsmem_denotes2; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H4; auto.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H9; auto.
    subst.
    exists lc. exists gl. exists als. exists Mem2. exists trace_nil.
    assert (getOperandPtr TD v lc gl = Some mptr0) as J.
      unfold getOperandPtr. rewrite H4. auto.
    split; eauto.

  Case "insn_alloca".
    assert (binds i0  
             (sterm_alloca (SMem sstate1) t s a)
             (STerms (se_cmd sstate1 (insn_alloca i0 t s a)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [alloca_denotes_gv' gv_in_env']].
    inversion alloca_denotes_gv'; subst.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 (ptr2GV TD (mb, 0))).
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H10; auto.
    subst.
    exists lc2. exists gl2. exists (mb::als). exists Mem5. exists trace_nil.
    split; eauto.

  Case "insn_load".
    assert (binds i0  
             (sterm_load (SMem sstate1)
                         t
                         (value2Sterm (STerms sstate1) v))
             (STerms (se_cmd sstate1 (insn_load i0 t v)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [load_denotes_gv' gv_in_env']].
    inversion load_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H4; auto.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 gv').
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H9; auto.
    subst.
    exists lc2. exists gl2. exists als. exists Mem1. exists trace_nil.
    assert (getOperandPtr TD v lc gl = Some mp0) as J.
      unfold getOperandPtr. rewrite H4. auto.
    split; eauto.

  Case "insn_store".
    inversion Hsmem_denotes2; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H5; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H12; auto.
    subst.
    exists lc. exists gl. exists als. exists Mem2. exists trace_nil.
    assert (getOperandPtr TD v0 lc gl = Some mptr2) as J.
      unfold getOperandPtr. rewrite H10. auto.
    split; eauto.

  Case "insn_gep".
    assert (binds i0  
             (sterm_gep i1
                        t
                        (value2Sterm (STerms sstate1) v) (List.map (value2Sterm (STerms sstate1)) l0))
             (STerms (se_cmd sstate1 (insn_gep i0 i1 t v l0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [gep_denotes_gv' gv_in_env']].
    inversion gep_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H5; auto.
    apply value2Sterm_denote__imply__genericvalues with (lc:=lc)(gl:=gl) in H10; auto.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 (ptr2GV TD mp1)).
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    exists lc2. exists gl2. exists als. exists Mem1. exists trace_nil.
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
             (STerms (se_cmd sstate1 (insn_ext i0 e t v t0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv3 [ext_denotes_gv3 gv3_in_env']].
    inversion ext_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 gv3).
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    exists lc2. exists gl2. exists als. exists Mem1. exists trace_nil. 
    assert (EXT TD lc gl e t v t0 = Some gv3) as J.
      unfold EXT. rewrite H10. auto.
    split; eauto.

  Case "insn_cast".
    assert (binds i0  
             (sterm_cast c t (value2Sterm (STerms sstate1) v) t0)
             (STerms (se_cmd sstate1 (insn_cast i0 c t v t0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv3 [cast_denotes_gv3 gv3_in_env']].
    inversion cast_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 gv3).
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    exists lc2. exists gl2. exists als. exists Mem1. exists trace_nil. 
    assert (CAST TD lc gl c t v t0 = Some gv3) as J.
      unfold CAST. rewrite H10. auto.
    split; eauto.

  Case "insn_icmp".
    assert (binds i0  
             (sterm_icmp c t (value2Sterm (STerms sstate1) v)
                             (value2Sterm (STerms sstate1) v0))
             (STerms (se_cmd sstate1 (insn_icmp i0 c t v v0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv3 [icmp_denotes_gv3 gv3_in_env']].
    inversion icmp_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 gv3).
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    exists lc2. exists gl2. exists als. exists Mem1. exists trace_nil. 
    assert (ICMP TD lc gl c t v v0 = Some gv3) as J.
      unfold ICMP. rewrite H10. rewrite H11. auto.
    split; eauto.

  Case "insn_select".
    assert (binds i0  
             (sterm_select (value2Sterm (STerms sstate1) v)
                           t
                           (value2Sterm (STerms sstate1) v0)
                           (value2Sterm (STerms sstate1) v1))
             (STerms (se_cmd sstate1 (insn_select i0 v t v0 v1)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv3 [select_denotes_gv3 gv3_in_env']].
    inversion select_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H5; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H12; auto.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 (if c0 then gv1 else gv2)).
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    exists lc2. exists gl2. exists als. exists Mem1. exists trace_nil. 
    split; eauto.
    assert (getOperandInt TD 1 v lc gl = Some c0) as J.
      unfold getOperandInt. rewrite H5. auto.
    assert ((lc2, gl2) = if c0 then updateEnv lc gl i0 gv1 else updateEnv lc gl i0 gv2) as J'.
      destruct c0; auto.
    eapply dbSelect; eauto.
Qed.

Lemma aux__se_cmd__denotes__op_cmd : forall S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl Mem1 lc' gl' als' Mem2 lc0 gl0 als0 Mem0 sstate1 tr1 tr2,
  uniq sstate1.(STerms) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 sstate1 lc gl als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd sstate1 c) lc' gl' als' Mem2 tr2 ->
  exists tr,
    dbCmd (mkState S TD Ps ((mkEC F B ((subblock_intro (c::cs) call0)::sbs) tmn lc arg0 als)::ECs) gl Mem1)
          (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc' arg0 als')::ECs) gl' Mem2)
          tr /\
    tr2 = trace_app tr1 tr.
Proof.
  intros S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl Mem1 lc' gl' als' Mem2 lc0 gl0 als0 Mem0 sstate1 tr1 tr2 Huniq Hsub Hdenotes1 Hdenotes2.
  assert (J:=Hdenotes2).
  apply aux__se_cmd__denotes__exists_op_cmd with
    (S:=S)(Ps:=Ps)(F:=F)(B:=B)(cs:=cs)(call0:=call0)(sbs:=sbs)(tmn:=tmn)(lc:=lc)
    (arg0:=arg0)(als:=als)(ECs:=ECs)(gl:=gl)(Mem1:=Mem1)(tr1:=tr1) in J; simpl; auto.
  destruct J as [lc'' [gl'' [als'' [Mem2' [tr [HdbCmd EQ]]]]]]; subst.
  exists tr. split; auto.
  assert (Hdenotes2':=HdbCmd).
  apply op_cmd__satisfies__se_cmd with (lc0:=lc0)(gl0:=gl0)(als0:=als0)(Mem0:=Mem0)(sstate1:=sstate1)(tr1:=tr1) in Hdenotes2'; auto.
  apply sstate_denotes_state_det with (lc2:=lc')(gl2:=gl')(als2:=als')(Mem2:=Mem2)(tr2:=trace_app tr1 tr) in Hdenotes2'; auto.
  destruct Hdenotes2' as [EQ1 [EQ2 [EQ3 EQ4]]]; subst.
  eapply dbCmd_eqEnv; eauto.
Qed.

Lemma se_cmd__denotes__op_cmd : forall S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl Mem1 lc' gl' als' Mem2 tr,
  uniq gl ->
  uniq lc ->
  sstate_denotes_state TD lc gl als Mem1 (se_cmd (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) c) lc' gl' als' Mem2 tr ->
  dbCmd (mkState S TD Ps ((mkEC F B ((subblock_intro (c::cs) call0)::sbs) tmn lc arg0 als)::ECs) gl Mem1)
        (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc' arg0 als')::ECs) gl' Mem2)
        tr. 
Proof.
  intros S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl Mem1 lc' gl' als' Mem2 tr Huniqg Huniqc Hdenotes.
  assert (J:=Hdenotes).
  apply aux__se_cmd__denotes__op_cmd with
    (lc:=lc)(gl:=gl)(Mem1:=Mem1)(tr1:=trace_nil)(call0:=call0)(sbs:=sbs)(tmn:=tmn)(als:=als)
    (S:=S)(Ps:=Ps)(F:=F)(B:=B)(cs:=cs)(arg0:=arg0)(ECs:=ECs) in J; simpl; auto.
    simpl in J. destruct J as [tr0 [J1 J2]]; subst; auto.
    apply env_to_smap_uniq.
    rewrite env_to_smap_dom_eq. fsetdec.
    apply env_to_smap_denotes_id; auto.
Qed.

Lemma ssa_se_cmd : forall i0 st0 smap1 smem1 sframe1 seffects1 c,
  binds i0 st0 smap1 ->
  binds i0 st0 (STerms (se_cmd (mkSstate smap1 smem1 sframe1 seffects1) c)).
  (* SSA *)
Admitted.

Lemma ssa_se_cmds : forall i0 st0 smap1 smem1 sframe1 seffects1 cs,
  binds i0 st0 smap1 ->
  binds i0 st0 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) cs)).
  (* SSA *)
Admitted.

Lemma se_cmds_denotes__decomposes__head : forall c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (se_cmd (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) c) cs) lc2 gl2 als2 Mem2 tr ->
  exists lc1, exists gl1, exists als1, exists Mem1, exists tr1,
    sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) c) lc1 gl1 als1 Mem1 tr1.
Proof.
  intros c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr Huniqg Huniqc Hdenotes.
  assert (Uniqi:=@env_to_smap_uniq gl0 lc0).
  assert (union (dom lc0) (dom gl0) [<=] dom (env_to_smap gl0 lc0)) as Subi.
    rewrite env_to_smap_dom_eq. fsetdec.
  generalize dependent TD.
  generalize dependent lc0.
  generalize dependent gl0.
  generalize dependent als0.
  generalize dependent Mem0.
  generalize dependent cs.
  generalize dependent lc2.
  generalize dependent gl2.
  generalize dependent als2.
  generalize dependent Mem2.
  generalize dependent tr.
  (cmd_cases (destruct c) Case);
    intros;
    destruct Hdenotes as [[Hsterms_denote1 Hsterms_denote2] [Hsmem_denotes [Hsframe_denotes Hseffects_denote]]].
  Case "insn_bop".
    assert (binds i0  
             (sterm_bop b s (value2Sterm (env_to_smap gl0 lc0) v)
                            (value2Sterm (env_to_smap gl0 lc0) v0))
             (STerms (se_cmds (se_cmd (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) (insn_bop i0 b s v v0)) cs))) as J.
      apply ssa_se_cmds.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [bop_denotes_gv3 gv3_in_env2]].
    inversion bop_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc0)(gl:=gl0) in H8; eauto using env_to_smap_denotes_gvmap.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc0)(gl:=gl0) in H9; eauto using env_to_smap_denotes_gvmap.
    assert (HupdateEnv:=exists_updateEnv lc0 gl0 i0 gv3).
    destruct HupdateEnv as [lc1 [gl1 HupdateEnv]].
    exists lc1. exists gl1. exists als0. exists Mem0. exists trace_nil.
    split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply env_to_smap_denotes__imples__gv with (TD:=TD)(Mem0:=Mem0) in binds_id'_st'; auto.
            destruct binds_id'_st' as [gv' [st'_denotes_gv' gv'_in_env0]].
            exists gv'. split; auto.
            apply lookupEnv_updateEnv_neq with (id1:=id') in HupdateEnv; auto.
            rewrite <- HupdateEnv; auto.

            exists gv3. split; eauto using lookupEnv_updateEnv_eq.

          destruct (i0==id'); subst.
            apply lookupEnv_updateEnv_eq in HupdateEnv.  
            rewrite HupdateEnv in H.
            inversion H; subst.
            exists (sterm_bop b s (value2Sterm (env_to_smap gl0 lc0) v) (value2Sterm (env_to_smap gl0 lc0) v0)).
            split.
              simpl. apply binds_updateSmap_eq; auto.
              eauto using genericvalue__implies__value2Sterm_denotes, env_to_smap_denotes_gvmap.

            apply lookupEnv_updateEnv_neq with (id1:=id') in HupdateEnv; auto.
            rewrite <- HupdateEnv in H.
            assert (J:=H).
            apply lookupEnv_env_to_smap in H; auto.
            exists (sterm_val (value_id id')).
            split; auto.
              apply ssa_se_cmd; auto.
Admitted.

Lemma se_cmds_denotes__decomposes__prefix : forall c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  uniq gl2 ->
  uniq lc2 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) c) lc2 gl2 als2 Mem2 tr ->
  exists lc1, exists gl1, exists als1, exists Mem1, exists tr1,
    sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) lc1 gl1 als1 Mem1 tr1 /\
    uniq gl1 /\ uniq lc1.
Proof.
  intros c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr Huniqg0 Huniqc0 Huniqg2 Huniqc2 Hdenotes.
  assert (uniq (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))) as Uniq1.
    eauto using env_to_smap_uniq, se_cmds_uniq.
  generalize dependent TD.
  generalize dependent lc0.
  generalize dependent gl0.
  generalize dependent als0.
  generalize dependent Mem0.
  generalize dependent cs.
  generalize dependent lc2.
  generalize dependent gl2.
  generalize dependent als2.
  generalize dependent Mem2.
  generalize dependent tr.
  (cmd_cases (destruct c) Case);
    intros;
    destruct Hdenotes as [[Hsterms_denote1 Hsterms_denote2] [Hsmem_denotes [Hsframe_denotes Hseffects_denote]]].
  Case "insn_bop".
    assert (binds i0  
             (sterm_bop b s (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                            (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0))
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_bop i0 b s v v0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [bop_denotes_gv3 gv3_in_env2]].
    destruct (@exists_deleteEnv lc2 gl2 i0) as [lc1 [gl1 HdeleteEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply deleteEnv_uniq in HdeleteEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    split; auto.
      split; auto.
      clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
      split; intros.
        assert (i0 <> id') as i0_isnt_id'. 
          admit. (*SSA*)
        apply ssa_se_cmd with (c:=insn_bop i0 b s v v0)(smem1:=smem_init)(sframe1:=sframe_init)(seffects1:=nil) in H; auto.
        apply Hsterms_denote1 in H.
        destruct H as [gv' [st'_denotes_gv' id'_gv'_in_env2]].
        apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
        rewrite HdeleteEnv in id'_gv'_in_env2.
        exists gv'. split; auto.

        apply lookupEnv_deleteEnv_inv with (gv:=gv')(id1:=id') in HdeleteEnv; auto.
        destruct HdeleteEnv as [id'_in_env2 i0_isnt_id'].
        apply Hsterms_denote2 in id'_in_env2.
        destruct id'_in_env2 as [st' [binds_id'_st' st'_denotes_gv']].
        exists st'. split; auto.
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[_ binds_id'_st'] | [i0_is_id' binds_id'_st']]; auto.
              contradict i0_is_id'; auto.

  Case "insn_extractvalue".
    assert (binds i0  
             (sterm_extractvalue t (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v) l0)
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_extractvalue i0 t v l0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [extracvalue_denotes_gv3 gv3_in_env2]].
    destruct (@exists_deleteEnv lc2 gl2 i0) as [lc1 [gl1 HdeleteEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply deleteEnv_uniq in HdeleteEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    split; auto.
      split; auto.
      clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
      split; intros.
        assert (i0 <> id') as i0_isnt_id'. 
          admit. (*SSA*)
        apply ssa_se_cmd with (c:=insn_extractvalue i0 t v l0)(smem1:=smem_init)(sframe1:=sframe_init)(seffects1:=nil) in H; auto.
        apply Hsterms_denote1 in H.
        destruct H as [gv' [st'_denotes_gv' id'_gv'_in_env2]].
        apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
        rewrite HdeleteEnv in id'_gv'_in_env2.
        exists gv'. split; auto.

        apply lookupEnv_deleteEnv_inv with (gv:=gv')(id1:=id') in HdeleteEnv; auto.
        destruct HdeleteEnv as [id'_in_env2 i0_isnt_id'].
        apply Hsterms_denote2 in id'_in_env2.
        destruct id'_in_env2 as [st' [binds_id'_st' st'_denotes_gv']].
        exists st'. split; auto.
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[_ binds_id'_st'] | [i0_is_id' binds_id'_st']]; auto.
              contradict i0_is_id'; auto.
        
  Case "insn_insertvalue". admit.

  Case "insn_malloc".
    assert (binds i0  
             (sterm_malloc (SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) t s a)
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_malloc i0 t s a)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [malloc_denotes_gv3 gv3_in_env2]].
    destruct (@exists_deleteEnv lc2 gl2 i0) as [lc1 [gl1 HdeleteEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists lc1. exists gl1. exists als2. exists Mem3. exists tr.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply deleteEnv_uniq in HdeleteEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    split; auto.
      split; auto.
      clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
      split; intros.
        assert (i0 <> id') as i0_isnt_id'. 
          admit. (*SSA*)
        apply ssa_se_cmd with (c:=insn_malloc i0 t s a)(smem1:=(SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)))(sframe1:=sframe_init)(seffects1:=nil) in H; auto.
        apply Hsterms_denote1 in H.
        destruct H as [gv' [st'_denotes_gv' id'_gv'_in_env2]].
        apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
        rewrite HdeleteEnv in id'_gv'_in_env2.
        exists gv'. split; auto.

        apply lookupEnv_deleteEnv_inv with (gv:=gv')(id1:=id') in HdeleteEnv; auto.
        destruct HdeleteEnv as [id'_in_env2 i0_isnt_id'].
        apply Hsterms_denote2 in id'_in_env2.
        destruct id'_in_env2 as [st' [binds_id'_st' st'_denotes_gv']].
        exists st'. split; auto.
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[_ binds_id'_st'] | [i0_is_id' binds_id'_st']]; auto.
              contradict i0_is_id'; auto.
    
  Case "insn_free".
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists lc2. exists gl2. exists als2. exists Mem3. exists tr.
    split; auto.
      split; auto.
      clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
      split; intros.
        apply ssa_se_cmd with (c:=insn_free i0 t v)(smem1:=(SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)))(sframe1:=sframe_init)(seffects1:=nil) in H; auto.

        apply Hsterms_denote2 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        exists st'. split; auto.

  Case "insn_alloca".
    assert (binds i0  
             (sterm_alloca (SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) t s a)
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_alloca i0 t s a)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [alloca_denotes_gv3 gv3_in_env2]].
    destruct (@exists_deleteEnv lc2 gl2 i0) as [lc1 [gl1 HdeleteEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    inversion Hsframe_denotes; subst.
    exists lc1. exists gl1. exists (als3). exists Mem3. exists tr.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply deleteEnv_uniq in HdeleteEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    split; auto.
      split; auto.
      clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
      split; intros.
        assert (i0 <> id') as i0_isnt_id'. 
          admit. (*SSA*)
        apply ssa_se_cmd with (c:=insn_alloca i0 t s a)(smem1:=(SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)))(sframe1:=sframe_init)(seffects1:=nil) in H; auto.
        apply Hsterms_denote1 in H.
        destruct H as [gv' [st'_denotes_gv' id'_gv'_in_env2]].
        apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
        rewrite HdeleteEnv in id'_gv'_in_env2.
        exists gv'. split; auto.

        apply lookupEnv_deleteEnv_inv with (gv:=gv')(id1:=id') in HdeleteEnv; auto.
        destruct HdeleteEnv as [id'_in_env2 i0_isnt_id'].
        apply Hsterms_denote2 in id'_in_env2.
        destruct id'_in_env2 as [st' [binds_id'_st' st'_denotes_gv']].
        exists st'. split; auto.
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[_ binds_id'_st'] | [i0_is_id' binds_id'_st']]; auto.
              contradict i0_is_id'; auto.
Admitted.

Lemma se_cmds_denotes__decomposes__prefix_last : forall c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  uniq gl2 ->
  uniq lc2 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) c) lc2 gl2 als2 Mem2 tr ->
  exists lc1, exists gl1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) lc1 gl1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) c) lc2 gl2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ 
    uniq gl1 /\ uniq lc1.
Proof.
  intros c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr Huniqg0 Huniqc0 Huniqg2 Huniqc2 Hdenotes.
  assert (uniq (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))) as Uniq1.
    eauto using env_to_smap_uniq, se_cmds_uniq.
  assert (Hsub:=@se_cmds_env_to_smap_dom_sub lc0 gl0 cs).
  generalize dependent TD.
  generalize dependent lc0.
  generalize dependent gl0.
  generalize dependent als0.
  generalize dependent Mem0.
  generalize dependent cs.
  generalize dependent lc2.
  generalize dependent gl2.
  generalize dependent als2.
  generalize dependent Mem2.
  generalize dependent tr.
  (cmd_cases (destruct c) Case);
    intros;
    destruct Hdenotes as [[Hsterms_denote1 Hsterms_denote2] [Hsmem_denotes [Hsframe_denotes Hseffects_denote]]].
  Case "insn_bop".
    assert (binds i0  
             (sterm_bop b s (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                            (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0))
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_bop i0 b s v v0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [bop_denotes_gv3 gv3_in_env2]].
    destruct (@exists_deleteEnv lc2 gl2 i0) as [lc1 [gl1 HdeleteEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr. exists trace_nil.
    rewrite trace_app_nil__eq__trace.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply deleteEnv_uniq in HdeleteEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
      split; intros.
        assert (i0 <> id') as i0_isnt_id'. 
          admit. (*SSA*)
        apply ssa_se_cmd with (c:=insn_bop i0 b s v v0)(smem1:=smem_init)(sframe1:=sframe_init)(seffects1:=nil) in H; auto.
        apply Hsterms_denote1 in H.
        destruct H as [gv' [st'_denotes_gv' id'_gv'_in_env2]].
        apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
        rewrite HdeleteEnv in id'_gv'_in_env2.
        exists gv'. split; auto.

        apply lookupEnv_deleteEnv_inv with (gv:=gv')(id1:=id') in HdeleteEnv; auto.
        destruct HdeleteEnv as [id'_in_env2 i0_isnt_id'].
        apply Hsterms_denote2 in id'_in_env2.
        destruct id'_in_env2 as [st' [binds_id'_st' st'_denotes_gv']].
        exists st'. split; auto.
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[_ binds_id'_st'] | [i0_is_id' binds_id'_st']]; auto.
              contradict i0_is_id'; auto.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply env_to_smap_denotes__imples__gv with (TD:=TD)(Mem0:=Mem2) in binds_id'_st'; auto.
            destruct binds_id'_st' as [gv' [st'_denotes_gv' gv'_in_env1]].
            exists gv'. split; auto.
            apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
            rewrite HdeleteEnv; auto.

            exists gv3. split; eauto using lookupEnv_deleteEnv_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion bop_denotes_gv3; subst. clear bop_denotes_gv3.
            apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); auto.
              apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H8; auto.
                apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                  apply env_to_smap_denotes_gvmap; auto.
              apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H9; auto.
                apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                  apply env_to_smap_denotes_gvmap; auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
              rewrite HdeleteEnv in id'_in_env2.              
              exists (sterm_val (value_id id')).
              clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
              split; auto.
                simpl.
                apply binds_updateSmap_neq; auto.
                apply lookupEnv_env_to_smap with (gv0:=gv'); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_bop b s (value2Sterm (env_to_smap gl1 lc1) v) (value2Sterm (env_to_smap gl1 lc1) v0)).
              split; auto using binds_updateSmap_eq.
                inversion bop_denotes_gv3; subst.
                apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); auto.
                  apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H8; auto.
                    apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                      apply env_to_smap_denotes_gvmap; auto.
                  apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H9; auto.
                    apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                      apply env_to_smap_denotes_gvmap; auto.

Admitted.

Lemma se_cmds_denotes__composes__prefix_last : forall c TD lc1 gl1 als1 Mem1 
  lc2 gl2 als2 Mem2 lc0 gl0 als0 Mem0 tr1 tr2 cs,
  uniq lc1 ->
  uniq gl1 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) lc1 gl1 als1 Mem1 tr1 ->
  sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) c) lc2 gl2 als2 Mem2 tr2 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) (cs++c::nil)) lc2 gl2 als2 Mem2 (trace_app tr1 tr2).
Proof.
  intros c TD lc1 gl1 als1 Mem1 lc2 gl2 als2 Mem2 lc0 gl0 als0 Mem0 tr1 tr2 cs Huniqc1 Huniqg1 Hdenotes1 Hdenotes2.
  assert (uniq (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))) as Uniq1.
    eauto using env_to_smap_uniq, se_cmds_uniq.
  generalize dependent TD.
  generalize dependent lc0.
  generalize dependent gl0.
  generalize dependent als0.
  generalize dependent Mem0.
  generalize dependent cs.
  generalize dependent lc2.
  generalize dependent gl2.
  generalize dependent als2.
  generalize dependent Mem2.
  generalize dependent lc1.
  generalize dependent gl1.
  generalize dependent als1.
  generalize dependent Mem1.
  generalize dependent tr1.
  generalize dependent tr2.
  (cmd_cases (destruct c) Case);
    intros;
    destruct Hdenotes1 as [[Hsterms_denote11 Hsterms_denote12] [Hsmem_denotes1 [Hsframe_denotes1 Hseffects_denote1]]];
    destruct Hdenotes2 as [[Hsterms_denote21 Hsterms_denote22] [Hsmem_denotes2 [Hsframe_denotes2 Hseffects_denote2]]];
    rewrite se_cmds_rev_cons.
  Case "insn_bop".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply Hsterms_denote11 in binds_id'_st'.
            destruct binds_id'_st' as [gv' [st'_denotes_gv' id'_gv'_in_env1]].
            exists gv'. split; auto.
              admit. (*SSA*)

            assert (binds id' (sterm_bop b s (value2Sterm (env_to_smap gl1 lc1) v) (value2Sterm (env_to_smap gl1 lc1) v0))
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_bop id' b s v v0)))
            ) as binds_id'_bop.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_bop.
            destruct binds_id'_bop as [gv' [bop_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion bop_denotes_gv'; subst.
              apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); auto.
                apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H8; auto.
                  apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                    split; auto.
                  apply env_to_smap_uniq.
                  rewrite env_to_smap_dom_eq. fsetdec.
                  apply env_to_smap_denotes_gvmap; auto.
                apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H9; auto.
                  apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                    split; auto.
                  apply env_to_smap_uniq.
                  rewrite env_to_smap_dom_eq. fsetdec.
                  apply env_to_smap_denotes_gvmap; auto.

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply binds_env_to_smap with (TD:=TD) in binds_id'_st'; auto.
            destruct binds_id'_st' as [EQ [gv id'_gv_in_env1]]; subst.
            assert (J:=id'_gv_in_env1).
            unfold getOperandValue in J.
            apply Hsterms_denote12 in J.
            destruct J as [st' [binds_id'_st' st'_denotes_gv]].
            inversion st'_denotes_gv'; subst.
            rewrite id'_gv_in_env1 in H4.
            inversion H4; subst. clear H4.
            exists st'.
            split; auto.
              simpl.
              apply binds_updateSmap_neq; auto.

          exists (sterm_bop b s 
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0)).
          split.
            simpl. apply binds_updateSmap_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); auto.
              apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H8; auto.
                apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                  split; auto.
                apply env_to_smap_uniq.
                rewrite env_to_smap_dom_eq. fsetdec.
                apply env_to_smap_denotes_gvmap; auto.
              apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H9; auto.
                apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                  split; auto.
                apply env_to_smap_uniq.
                rewrite env_to_smap_dom_eq. fsetdec.
                apply env_to_smap_denotes_gvmap; auto.
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22.
      simpl in *.
      inversion Hsmem_denotes2; subst; auto.
    split.
      clear Hsmem_denotes1 Hseffects_denote1 Hsmem_denotes2 Hseffects_denote2.
      clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22.
      simpl in *.
      inversion Hsframe_denotes2; subst; auto.

      clear Hsmem_denotes1 Hsframe_denotes1 Hsmem_denotes2 Hsframe_denotes2.
      clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22.
      simpl in *.
      inversion Hseffects_denote1; subst.      
      inversion Hseffects_denote2; subst; auto.  
Admitted.

Definition se_cmds_denotes__decomposes__app_prop (cs2:list cmd) :=
forall TD lc0 gl0 als0 Mem0 cs1 lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  uniq gl2 ->
  uniq lc2 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) (cs1++cs2)) lc2 gl2 als2 Mem2 tr ->
  exists lc1, exists gl1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs1) lc1 gl1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmds (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) cs2) lc2 gl2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ uniq gl1 /\ uniq lc1.

Lemma se_cmds_denotes__decomposes__app : forall cs2, 
  se_cmds_denotes__decomposes__app_prop cs2.
Proof.
  apply (@rev_ind cmd); unfold se_cmds_denotes__decomposes__app_prop in *; intros; simpl.
  Case "nil".
    exists lc2. exists gl2. exists als2. exists Mem2. exists tr. exists trace_nil.
    rewrite trace_app_nil__eq__trace.
    rewrite <- app_nil_end in H3.
    split; auto.
    split; auto.
      apply env_to_smap_denotes_id; auto.
  Case "cons".
    rewrite <- app_ass in H4.
    rewrite se_cmds_rev_cons in H4.
    apply se_cmds_denotes__decomposes__prefix_last in H4; auto.
    destruct H4 as [lc1 [gl1 [als1 [Mem1 [tr1 [tr2 [env0_denotes_env1 [env1_denotes_env2 [EQ [Huniqg1 Huniqc1]]]]]]]]]]; subst.
    apply H in env0_denotes_env1; auto.
    destruct env0_denotes_env1 as [lc3 [gl3 [als3 [Mem3 [tr3 [tr4 [env0_denotes_env3 [env3_denotes_env1 [EQ [Huniqg3 Huniqc3]]]]]]]]]]; subst.
    exists lc3. exists gl3. exists als3. exists Mem3. exists tr3. exists (trace_app tr4 tr2).
    rewrite trace_app_commute.
    split; auto.
    split; auto.
     apply se_cmds_denotes__composes__prefix_last with (lc1:=lc1)(gl1:=gl1)(als1:=als1)(Mem1:=Mem1); eauto.
Qed.

Lemma se_cmds_denotes__decomposes__head_tail : forall c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  uniq gl2 ->
  uniq lc2 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (se_cmd (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) c) cs) lc2 gl2 als2 Mem2 tr ->
  exists lc1, exists gl1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) c) lc1 gl1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmds (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) cs) lc2 gl2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ uniq gl1 /\ uniq lc1.
Proof.
  intros c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr Huniqg0 Huniqc0 Huniqg2 Huniqc2 Hdenotes.
  rewrite <- se_cmds_cons in Hdenotes.
  apply se_cmds_denotes__decomposes__app in Hdenotes; auto.
Qed.    
  
Lemma se_cmds__denote__exists_op_cmds : forall cs S TD Ps F B call0 sbs tmn lc1 arg als1 ECs gl1 Mem1 lc2 gl2 als2 Mem2 tr,
  uniq gl1 ->
  uniq lc1 ->
  uniq gl2 ->
  uniq lc2 ->
  sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmds (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) cs) lc2 gl2 als2 Mem2 tr ->
  exists lc2', exists gl2', exists als2, exists Mem2', exists tr', 
    dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
           (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc2' arg als2)::ECs) gl2' Mem2')
           tr'.
Proof.
  induction cs; 
    intros S TD Ps F B call0 sbs tmn lc1 arg0 als1 ECs gl1 Mem1 lc2 gl2 als2 Mem2 tr Uniqg1 Uniqc1 Uniqg2 Uniqc2 Hdenotes.

    simpl in *. 
    exists lc1. exists gl1. exists als1. exists Mem2. exists trace_nil. 
    assert (J:=@env_to_smap_denotes_id TD lc1 gl1 als1 Mem1 Uniqg1 Uniqc1).
    apply sstate_denotes_state_det with (lc2:=lc2)(gl2:=gl2)(als2:=als2)(Mem2:=Mem2)(tr2:=tr) in J; auto.
    destruct J as [EQ1 [EQ2 [EQ3 EQ4]]]; subst; auto.

    simpl in Hdenotes.
    apply se_cmds_denotes__decomposes__head_tail in Hdenotes; auto.
    destruct Hdenotes as [lc3 [gl3 [als3 [Mem3 [tr3 [tr3' [J1 [J2 [EQ [Huniqg3 Huniqc3]]]]]]]]]]; subst.
    apply se_cmd__denotes__op_cmd with
      (S:=S)(Ps:=Ps)(F:=F)(B:=B)(cs:=cs)(call0:=call0)(sbs:=sbs)(tmn:=tmn)(lc:=lc1)
     (arg0:=arg0)(als:=als1)(ECs:=ECs)(gl:=gl1)(Mem1:=Mem1) in J1; simpl; auto.
    apply IHcs with
      (S:=S)(Ps:=Ps)(F:=F)(B:=B)(call0:=call0)(sbs:=sbs)(tmn:=tmn)
      (arg:=arg0)(ECs:=ECs) in J2; simpl; auto.
      destruct J2 as [lc4 [gl4 [als4 [Mem4 [tr4 HdbCmds]]]]].
      exists lc4. exists gl4. exists als4. exists Mem4. exists (trace_app tr3 tr4). 
      apply dbCmds_cons with (S2:=mkState S TD Ps ((mkEC F B (subblock_intro cs call0::sbs) tmn lc3 arg0 als3)::ECs) gl3 Mem3); eauto.
Qed.

Lemma se_cmds__denote__op_cmds : forall S TD Ps F B cs call0 sbs tmn lc1 arg ECs gl1 als1 Mem1 lc2 als2 gl2 Mem2 tr,
  uniq gl1 ->
  uniq lc1 ->
  uniq gl2 ->
  uniq lc2 ->
  sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmds (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) cs) lc2 gl2 als2 Mem2 tr ->
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
         (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc2 arg als2)::ECs) gl2 Mem2)
         tr. 
Proof.
  intros S TD Ps F B cs call0 sbs tmn lc1 arg0 ECs gl1 als1 Mem1 lc2 als2 gl2 Mem2 tr Huniqg1 Huniqc1 Huniqg2 Huniqc2 Hdenotes.
  assert (J:=Hdenotes).
  apply se_cmds__denote__exists_op_cmds with
    (S:=S)(Ps:=Ps)(F:=F)(B:=B)(cs:=cs)(call0:=call0)(sbs:=sbs)(tmn:=tmn)(lc1:=lc1)
    (arg:=arg0)(als1:=als1)(ECs:=ECs)(gl1:=gl1)(Mem1:=Mem1) in J; simpl; auto.
  destruct J as [lc2' [gl2' [als2' [Mem2' [tr' HdbCmds]]]]].
  assert (Hdenotes':=HdbCmds).
  apply op_cmds__satisfy__se_cmds in Hdenotes'; auto.
  apply sstate_denotes_state_det with (lc2:=lc2)(gl2:=gl2)(als2:=als2)(Mem2:=Mem2)(tr2:=tr) in Hdenotes'; auto.
  destruct Hdenotes' as [EQ1 [EQ2 [EQ3 EQ4]]]; subst.
  eapply dbCmds_eqEnv; eauto.
Qed.

(* Correctness of the cmds validator *)

Definition tv_cmds (cs1 cs2 : list cmd) (lc gl:GVMap) :=
se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs1 =
se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs2.

Lemma tv_cmds__is__correct : forall S TD Ps F B cs cs' call0 sbs tmn lc1 arg als1 ECs gl1 Mem1 lc2 als2 gl2 Mem2 tr,
  uniq gl1 ->
  uniq lc1 ->  
  tv_cmds cs cs' lc1 gl1 ->
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
        (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc2 arg als2)::ECs) gl2 Mem2)
        tr ->
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs' call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
        (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc2 arg als2)::ECs) gl2 Mem2)
        tr.
Proof.
  intros S TD Ps F B cs cs' call0 sbs tmn lc1 arg0 als1 ECs gl1 Mem1 lc2 als2 gl2 Mem2 tr Huniqg Huniqc Htv_cmds HdbCmds.
  unfold tv_cmds in Htv_cmds.
  assert (Uniqs:=HdbCmds).
  apply dbCmds_uniq in Uniqs; auto.
  destruct Uniqs as [Uniqg2 Uniqc2].
  apply op_cmds__satisfy__se_cmds in HdbCmds; auto.
  rewrite Htv_cmds in HdbCmds.
  apply se_cmds__denote__op_cmds; auto.
Qed.

Definition tv_subblock (b1 b2:subblock) (lc gl:GVMap) :=
match (b1, b2) with
| (subblock_intro cs1 call1, subblock_intro cs2 call2) =>
  match (call1, call2) with
  | (insn_call id1 _ _ _ _ _, insn_call id2 _ _ _ _ _) => 
    if id1==id2 
    then
      let st1 := se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs1 in
      let st2 := se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs2 in
      let cl1 := se_call st1 call1 in
      let cl2 := se_call st2 call2 in
      st1 = st2 /\ cl1 = cl2
    else
      False
  end
end.

(* Definions below have not been used yet. *)

Fixpoint subst_tt (id0:id) (s0:sterm) (s:sterm) : sterm :=
match s with
| sterm_val (value_id id1) => if id0 == id1 then s0 else s
| sterm_val (value_const c) => sterm_val (value_const c)
| sterm_bop op sz s1 s2 => 
    sterm_bop op sz (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_extractvalue t1 s1 cs => 
    sterm_extractvalue t1 (subst_tt id0 s0 s1) cs
| sterm_insertvalue t1 s1 t2 s2 cs => 
    sterm_insertvalue t1 (subst_tt id0 s0 s1) t2 (subst_tt id0 s0 s2) cs
| sterm_malloc m1 t1 sz align => 
    sterm_malloc (subst_tm id0 s0 m1) t1 sz align
| sterm_alloca m1 t1 sz align => 
    sterm_alloca (subst_tm id0 s0 m1) t1 sz align
| sterm_load m1 t1 s1 => 
    sterm_load (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1)
| sterm_gep inbounds t1 s1 ls2 =>
    sterm_gep inbounds t1 (subst_tt id0 s0 s1) (List.map (subst_tt id0 s0) ls2)
| sterm_ext extop t1 s1 t2 => 
    sterm_ext extop t1 (subst_tt id0 s0 s1) t2
| sterm_cast castop t1 s1 t2 => 
    sterm_cast castop t1 (subst_tt id0 s0 s1) t2
| sterm_icmp cond t1 s1 s2 => 
    sterm_icmp cond t1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_phi t1 lsl1 => 
    sterm_phi t1 (List.map 
                   (fun (sl1:sterm*l) => 
                    let (s1,l1):=sl1 in 
                    ((subst_tt id0 s0 s1), l1)
                   ) 
                   lsl1)
| sterm_select s1 t1 s2 s3 => 
    sterm_select (subst_tt id0 s0 s1) t1 (subst_tt id0 s0 s2) (subst_tt id0 s0 s3)
end
with subst_tm (id0:id) (s0:sterm) (m:smem) : smem :=
match m with 
| smem_init => smem_init
| smem_malloc m1 t1 sz align => smem_malloc (subst_tm id0 s0 m1) t1 sz align
| smem_free m1 t1 s1 => smem_free (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1)
| smem_alloca m1 t1 sz align => smem_alloca (subst_tm id0 s0 m1) t1 sz align
| smem_load m1 t1 s1 => smem_load (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1)
| smem_store m1 t1 s1 s2 => smem_store (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
end
.

Fixpoint subst_mt (sm:smap) (s:sterm) : sterm :=
match sm with
| nil => s
| (id0, s0)::sm' => subst_mt sm' (subst_tt id0 s0 s)
end.

Fixpoint subst_mm (sm:smap) (m:smem) : smem :=
match sm with
| nil => m
| (id0, s0)::sm' => subst_mm sm' (subst_tm id0 s0 m)
end.


