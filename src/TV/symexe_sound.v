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

Lemma binds_se_cmd : forall c i0 i1 st0 smap1 smem1 sframe1 seffects1,
  binds i0 st0 smap1 ->
  getCmdID c = i1 ->
  i0 <> i1 ->
  binds i0 st0 (STerms (se_cmd (mkSstate smap1 smem1 sframe1 seffects1) c)).
Proof.
  destruct c; intros id0 id1 st0 smap1 smem1 sframe1 seffects1 Hbinds HgetCmdID id0_isnt_id1; simpl;
    simpl in HgetCmdID; subst; auto using binds_updateSmap_neq.
Qed.
  
Lemma binds_se_cmds_iff : forall i0 st0 smap1 smem1 sframe1 seffects1 cs c,
  wf_cmds (cs++(c::nil)) ->  
  getCmdID c = i0 ->
  (binds i0 st0 smap1 <->
   binds i0 st0 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) cs))).
  (* SSA *)
Admitted.

Lemma binds_se_cmds : forall i0 st0 smap1 smem1 sframe1 seffects1 cs c,
  wf_cmds (cs++(c::nil)) ->  
  getCmdID c = i0 ->
  binds i0 st0 smap1 ->
  binds i0 st0 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) cs)).
Proof.
  intros i0 st0 smap1 smem1 sframe1 seffects1 cs c H1 H2.
  eapply binds_se_cmds_iff; eauto.
Qed.

Lemma binds_se_cmds__prefix_last : forall cs c id' st' smap1 smem1 sframe1 seffects1 i0,
  wf_cmds (cs++(c::nil)) ->  
  binds id' st' (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) cs)) ->
  getCmdID c = i0 ->
  (id'=i0 /\ binds id' st' smap1) \/ 
  (id' <> i0 /\ 
   binds id' st' 
    (STerms (se_cmd 
              (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) 
               cs) 
             c)
     )
  ).
Proof.
  intros cs c id' st' smap1 smem1 sframe1 seffects1 i0 Wf Binds GetCmdID.
  destruct (i0==id'); subst.
    left. split; auto.
      eapply binds_se_cmds_iff; eauto.
    right. split; auto.
      apply binds_se_cmd with (i1:=getCmdID c) ; auto.
Qed.

Lemma se_cmd_updateSmap_inv : forall c st,
  STerms (se_cmd st c) = STerms st \/
  (exists st0, (STerms (se_cmd st c)) = updateSmap (STerms st) (getCmdID c) st0).
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
                     (List.map (value2Sterm st.(STerms)) l0)). auto.

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
Qed.

Lemma smap_denotes_gvmap_rollbackEnv : forall TD lc0 gl0 Mem0 cs c lc2 gl2 lc1 gl1 gv3 i0,
  uniq gl0 ->
  uniq lc0 ->
  uniq gl2 ->
  uniq lc2 ->
  wf_cmds (cs++(c::nil)) ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) c)) lc2 gl2 ->
  lookupEnv lc2 gl2 i0 = Some gv3 ->
  rollbackEnv lc2 gl2 i0 lc0 gl0 = (lc1, gl1) ->
  getCmdID c = i0 ->
  smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1.
Proof.
  intros TD lc0 gl0 Mem0 cs c lc2 gl2 lc1 gl1 gv3 i0
         Huniqg0 Huniqc0 Huniqg2 Huniqc2 Wf [Hsterms_denote1 Hsterms_denote2] gv3_in_env2 HrollbackEnv HgetCmdID.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply rollbackEnv_uniq in HrollbackEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
  split; intros.
        apply binds_se_cmds__prefix_last with (c:=c)(i0:=i0) in H; auto.
        destruct H as [[id'_is_i0 binds_id'_st'] | [i0_isnt_id' binds_id'_st']]; subst.
          apply env_to_smap_denotes__imples__gv with (TD:=TD)(Mem0:=Mem0) in binds_id'_st'; auto.
          destruct binds_id'_st' as [gv0 [st'_denotes_gv0 i0_gv0_in_env0]].
          exists gv0. 
          apply lookupEnv_rollbackEnv_Some_eq with (gv0:=gv3) in HrollbackEnv; auto.
          rewrite <- HrollbackEnv in i0_gv0_in_env0.
          split; auto.

          apply Hsterms_denote1 in binds_id'_st'.
          destruct binds_id'_st' as [gv' [st'_denotes_gv' id'_gv'_in_env2]].
          apply lookupEnv_rollbackEnv_neq with (id1:=id') in HrollbackEnv; auto.
          rewrite HrollbackEnv in id'_gv'_in_env2.
          exists gv'. split; auto.

        destruct (i0==id'); subst.
          apply lookupEnv_rollbackEnv_Some_eq with (gv0:=gv3) in HrollbackEnv; auto.
          exists (sterm_val (value_id id')).
          rewrite e in HrollbackEnv.
          rewrite HrollbackEnv in H.
          split; auto.
            apply binds_se_cmds with (c:=c); auto.
            apply lookupEnv_env_to_smap with (gv0:=gv'); auto.

          apply lookupEnv_rollbackEnv_neq with (id1:=id') in HrollbackEnv; auto.
          rewrite <- HrollbackEnv in H.
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          exists st'. split; auto.
            simpl in binds_id'_st'.

            destruct (@se_cmd_updateSmap_inv c (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) as [J1 | [st0 J1]];
              rewrite J1 in binds_id'_st'; auto.
              apply updateSmap_inversion in binds_id'_st'; auto. 
                destruct binds_id'_st' as [[_ binds_id'_st'] | [i0_is_id' binds_id'_st']]; auto.
                  contradict i0_is_id'; auto.
                eauto using env_to_smap_uniq, se_cmds_uniq.
Qed.

Lemma se_cmds_denotes__decomposes__prefix_last__case1 : forall id' st' gl1 lc1 lc2 gl2 i0 TD Mem2 lc0 gl0,
  uniq gl1 ->
  uniq lc1 ->
  i0 <> id' ->
  binds id' st' (env_to_smap gl1 lc1) ->
  rollbackEnv lc2 gl2 i0 lc0 gl0 = (lc1, gl1) ->
  exists gv', sterm_denotes_genericvalue TD lc1 gl1 Mem2 st' gv' /\ 
  lookupEnv lc2 gl2 id' = Some gv'.
Proof.
  intros id' st' gl1 lc1 lc2 gl2 i0 TD Mem2 lc0 gl0 Uniqg1 Uniqc1 i0_isnt_id' binds_id'_st' HrollbackEnv.
            apply env_to_smap_denotes__imples__gv with (TD:=TD)(Mem0:=Mem2) in binds_id'_st'; auto.
            destruct binds_id'_st' as [gv' [st'_denotes_gv' gv'_in_env1]].
            exists gv'. split; auto.
            apply lookupEnv_rollbackEnv_neq with (id1:=id') in HrollbackEnv; auto.
            rewrite HrollbackEnv; auto.
Qed.


  
Lemma se_cmds_denotes__decomposes__prefix_last__case2 : forall id' st' Mem0 gl1 lc1 lc2 gl2 i0 TD Mem2 lc0 gl0 c gv' cs,
  uniq gl1 ->
  uniq lc1 ->
  i0 <> id' ->
  getCmdID c = i0 ->
  lookupEnv lc2 gl2 id' = Some gv' ->
  binds id' st' (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) ->
  rollbackEnv lc2 gl2 i0 lc0 gl0 = (lc1, gl1) ->
  sterm_denotes_genericvalue TD lc0 gl0 Mem0 st' gv' ->
  exists st'0, 
    binds id' st'0 (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) c)) /\
    sterm_denotes_genericvalue TD lc1 gl1 Mem2 st'0 gv'.
Proof.
  intros id' st' Mem0 gl1 lc1 lc2 gl2 i0 TD Mem2 lc0 gl0 c gv' cs Uniqg1 Uniqc1 i0_isnt_id' HgetCmdID id'_in_env2 binds_id'_st' HrollbackEnv st'_denotes_gv'.
  apply lookupEnv_rollbackEnv_neq with (id1:=id') in HrollbackEnv; auto.
  rewrite HrollbackEnv in id'_in_env2.              
  exists (sterm_val (value_id id')).
  split; auto.
    destruct (@se_cmd_updateSmap_inv c (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil)) as [J1 | [st0 J1]];
      rewrite J1.
      apply lookupEnv_env_to_smap with (gv0:=gv'); auto.

      rewrite <-HgetCmdID in i0_isnt_id'.
      apply binds_updateSmap_neq; auto.      
      apply lookupEnv_env_to_smap with (gv0:=gv'); auto.
Qed.

Lemma se_cmds_denotes__decomposes__prefix_last : forall c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  uniq gl2 ->
  uniq lc2 ->
  wf_cmds (cs++(c::nil)) ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) c) lc2 gl2 als2 Mem2 tr ->
  exists lc1, exists gl1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) lc1 gl1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) c) lc2 gl2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ 
    uniq gl1 /\ uniq lc1.
Proof.
  intros c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr Huniqg0 Huniqc0 Huniqg2 Huniqc2 Wf Hdenotes.
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
    destruct (@exists_rollbackEnv lc2 gl2 i0 lc0 gl0) as [lc1 [gl1 HrollbackEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply rollbackEnv_uniq in HrollbackEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_bop i0 b s v v0)(i0:=i0)(lc2:=lc2)(gl2:=gl2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0)(gl0:=gl0); auto.

            exists gv3. split; eauto using lookupEnv_rollbackEnv_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion bop_denotes_gv3; subst. clear bop_denotes_gv3.
            apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(gl2:=gl2)(i0:=i0)(lc0:=lc0)(gl0:=gl0)(cs:=cs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_bop b s (value2Sterm (env_to_smap gl1 lc1) v) (value2Sterm (env_to_smap gl1 lc1) v0)).
              split; auto using binds_updateSmap_eq.
                inversion bop_denotes_gv3; subst.
                apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.

  Case "insn_extractvalue".
    assert (binds i0  
             (sterm_extractvalue t (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v) l0)
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_extractvalue i0 t v l0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [extractvalue_denotes_gv3 gv3_in_env2]].
    destruct (@exists_rollbackEnv lc2 gl2 i0 lc0 gl0) as [lc1 [gl1 HrollbackEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply rollbackEnv_uniq in HrollbackEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_extractvalue i0 t v l0)(i0:=i0)(lc2:=lc2)(gl2:=gl2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0)(gl0:=gl0); auto.

            exists gv3. split; eauto using lookupEnv_rollbackEnv_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion extractvalue_denotes_gv3; subst. clear extractvalue_denotes_gv3.
            apply sterm_extractvalue_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(gl2:=gl2)(i0:=i0)(lc0:=lc0)(gl0:=gl0)(cs:=cs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_extractvalue t (value2Sterm (env_to_smap gl1 lc1) v) l0).
              split; auto using binds_updateSmap_eq.
                inversion extractvalue_denotes_gv3; subst.
                apply sterm_extractvalue_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.        

  Case "insn_insertvalue".
    assert (binds i0  
             (sterm_insertvalue t (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v) 
                                t0 (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0) 
                                l0)
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_insertvalue i0 t v t0 v0 l0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [insertvalue_denotes_gv3 gv3_in_env2]].
    destruct (@exists_rollbackEnv lc2 gl2 i0 lc0 gl0) as [lc1 [gl1 HrollbackEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply rollbackEnv_uniq in HrollbackEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_insertvalue i0 t v t0 v0 l0)(i0:=i0)(lc2:=lc2)(gl2:=gl2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0)(gl0:=gl0); auto.

            exists gv3. split; eauto using lookupEnv_rollbackEnv_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion insertvalue_denotes_gv3; subst. clear insertvalue_denotes_gv3.
            apply sterm_insertvalue_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(gl2:=gl2)(i0:=i0)(lc0:=lc0)(gl0:=gl0)(cs:=cs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_insertvalue t (value2Sterm (env_to_smap gl1 lc1) v) t0 (value2Sterm (env_to_smap gl1 lc1) v0) l0).
              split; auto using binds_updateSmap_eq.
                inversion insertvalue_denotes_gv3; subst.
                apply sterm_insertvalue_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.        


  Case "insn_malloc".
    assert (binds i0  
             (sterm_malloc (SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) t s a)
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_malloc i0 t s a)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [malloc_denotes_gv3 gv3_in_env2]].
    destruct (@exists_rollbackEnv lc2 gl2 i0 lc0 gl0) as [lc1 [gl1 HrollbackEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists lc1. exists gl1. exists als2. exists Mem3. exists tr. exists trace_nil.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply rollbackEnv_uniq in HrollbackEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_malloc i0 t s a)(i0:=i0)(lc2:=lc2)(gl2:=gl2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0)(gl0:=gl0); auto.

            exists gv3. split; eauto using lookupEnv_rollbackEnv_Some_eq.
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
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(gl2:=gl2)(i0:=i0)(lc0:=lc0)(gl0:=gl0)(cs:=cs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_malloc smem_init t s a).
              split; auto using binds_updateSmap_eq.
                inversion malloc_denotes_gv3; subst.
                apply smem_denotes_mem_det with (Mem2:=Mem4) in H8; auto. subst.
                rewrite H12 in H9. inversion H9; subst. clear H9.
                rewrite H10 in H13. inversion H13; subst. clear H13.
                eapply sterm_malloc_denotes; eauto.
      split; simpl; eauto.
    
  Case "insn_free".
    inversion Hsmem_denotes; subst.
    exists lc2. exists gl2. exists als2. exists Mem3. exists tr. exists trace_nil.
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
        split; auto.
    split; auto.
      split.
        split; intros.
          simpl in H.
          apply env_to_smap_denotes__imples__gv with (TD:=TD)(Mem0:=Mem3) in H; auto.

          exists (sterm_val (value_id id')).
          split; auto.
            simpl.
            apply lookupEnv_env_to_smap with (gv0:=gv'); auto.
      split; simpl; eauto.
        apply value2Sterm_denotes__implies__genericvalue with (lc:=lc2)(gl:=gl2) in H2; try solve [auto | split; auto].
        eapply smem_free_denotes; eauto 
                  using genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.        

  Case "insn_alloca".
    assert (binds i0  
             (sterm_alloca (SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) t s a)
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_alloca i0 t s a)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [alloca_denotes_gv3 gv3_in_env2]].
    destruct (@exists_rollbackEnv lc2 gl2 i0 lc0 gl0) as [lc1 [gl1 HrollbackEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    inversion Hsframe_denotes; subst.
    apply smem_denotes_mem_det with (Mem2:=Mem3) in H13; auto. subst.
    rewrite H9 in H15. inversion H15; subst. clear H15.
    rewrite H10 in H16. inversion H16; subst. clear H16.
    exists lc1. exists gl1. exists als3. exists Mem3. exists tr. exists trace_nil.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply rollbackEnv_uniq in HrollbackEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_alloca i0 t s a)(i0:=i0)(lc2:=lc2)(gl2:=gl2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0)(gl0:=gl0); auto.

            exists gv3. split; eauto using lookupEnv_rollbackEnv_Some_eq.
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
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(gl2:=gl2)(i0:=i0)(lc0:=lc0)(gl0:=gl0)(cs:=cs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_alloca smem_init t s a).
              split; auto using binds_updateSmap_eq.
                inversion alloca_denotes_gv3; subst.
                apply smem_denotes_mem_det with (Mem2:=Mem2) in H8; auto. subst.
                rewrite H12 in H9. inversion H9; subst. clear H9.
                rewrite H10 in H13. inversion H13; subst. clear H13.
                eapply sterm_alloca_denotes; eauto.
      split; simpl; eauto.   

  Case "insn_load".
    assert (binds i0  
             (sterm_load (SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) 
                         t 
                         (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v))
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_load i0 t v)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [load_denotes_gv3 gv3_in_env2]].
    destruct (@exists_rollbackEnv lc2 gl2 i0 lc0 gl0) as [lc1 [gl1 HrollbackEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply rollbackEnv_uniq in HrollbackEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_load i0 t v)(i0:=i0)(lc2:=lc2)(gl2:=gl2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0)(gl0:=gl0); auto.

            exists gv3. split; eauto using lookupEnv_rollbackEnv_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion load_denotes_gv3; subst. clear load_denotes_gv3.
            apply smem_denotes_mem_det with (Mem2:=Mem2) in H8; auto. subst.
            eapply sterm_load_denotes with (gv0:=gv0); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(gl2:=gl2)(i0:=i0)(lc0:=lc0)(gl0:=gl0)(cs:=cs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_load smem_init t (value2Sterm (env_to_smap gl1 lc1) v)).
              split; auto using binds_updateSmap_eq.
                inversion load_denotes_gv3; subst.
                apply smem_denotes_mem_det with (Mem2:=Mem2) in H8; auto. subst.
                eapply sterm_load_denotes with (gv0:=gv0); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.        
      split; simpl; eauto.   

  Case "insn_store".
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists lc2. exists gl2. exists als2. exists Mem3. exists tr. exists trace_nil.
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
        split; auto.
    split; simpl; eauto.
      split.
        split; intros.
          simpl in H.
          apply env_to_smap_denotes__imples__gv with (TD:=TD)(Mem0:=Mem3) in H; auto.

          exists (sterm_val (value_id id')).
          split; auto.
            simpl.
            apply lookupEnv_env_to_smap with (gv0:=gv'); auto.
      split; simpl; eauto.
        apply value2Sterm_denotes__implies__genericvalue with (lc:=lc2)(gl:=gl2) in H3; try solve [auto | split; auto].
        apply value2Sterm_denotes__implies__genericvalue with (lc:=lc2)(gl:=gl2) in H8; try solve [auto | split; auto].
        eapply smem_store_denotes; eauto 
                  using genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.        

  Case "insn_gep".
    assert (binds i0  
             (sterm_gep i1 t (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                             (List.map (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))) l0))
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_gep i0 i1 t v l0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [gep_denotes_gv3 gv3_in_env2]].
    destruct (@exists_rollbackEnv lc2 gl2 i0 lc0 gl0) as [lc1 [gl1 HrollbackEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply rollbackEnv_uniq in HrollbackEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_gep i0 i1 t v l0)(i0:=i0)(lc2:=lc2)(gl2:=gl2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0)(gl0:=gl0); auto.

            exists gv3. split; eauto using lookupEnv_rollbackEnv_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion gep_denotes_gv3; subst. clear gep_denotes_gv3.
            apply value2Sterm_denote__imply__genericvalues with (lc:=lc1)(gl:=gl1) in H8; try solve [auto | split; auto].
            eapply sterm_gep_denotes with (gv0:=gv0)(gvs0:=gvs0); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.
              eapply genericvalues__imply__value2Sterm_denote; eauto using env_to_smap_uniq, env_to_smap_denotes_gvmap.
                rewrite env_to_smap_dom_eq. fsetdec.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(gl2:=gl2)(i0:=i0)(lc0:=lc0)(gl0:=gl0)(cs:=cs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_gep i1 t (value2Sterm (env_to_smap gl1 lc1) v) (List.map (value2Sterm (env_to_smap gl1 lc1)) l0)).
              split; auto using binds_updateSmap_eq.
                inversion gep_denotes_gv3; subst.
                apply value2Sterm_denote__imply__genericvalues with (lc:=lc1)(gl:=gl1) in H8; try solve [auto | split; auto].
                eapply sterm_gep_denotes with (gv0:=gv0)(gvs0:=gvs0); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.
                  eapply genericvalues__imply__value2Sterm_denote; eauto using env_to_smap_uniq, env_to_smap_denotes_gvmap.
                    rewrite env_to_smap_dom_eq. fsetdec.

  Case "insn_ext".
    assert (binds i0  
             (sterm_ext e t (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v) t0)
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_ext i0 e t v t0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [ext_denotes_gv3 gv3_in_env2]].
    destruct (@exists_rollbackEnv lc2 gl2 i0 lc0 gl0) as [lc1 [gl1 HrollbackEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply rollbackEnv_uniq in HrollbackEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_ext i0 e t v t0)(i0:=i0)(lc2:=lc2)(gl2:=gl2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0)(gl0:=gl0); auto.

            exists gv3. split; eauto using lookupEnv_rollbackEnv_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion ext_denotes_gv3; subst. clear ext_denotes_gv3.
            apply sterm_ext_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(gl2:=gl2)(i0:=i0)(lc0:=lc0)(gl0:=gl0)(cs:=cs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_ext e t (value2Sterm (env_to_smap gl1 lc1) v) t0).
              split; auto using binds_updateSmap_eq.
                inversion ext_denotes_gv3; subst.
                apply sterm_ext_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.

  Case "insn_cast".
    assert (binds i0  
             (sterm_cast c t (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v) t0)
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_cast i0 c t v t0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [cast_denotes_gv3 gv3_in_env2]].
    destruct (@exists_rollbackEnv lc2 gl2 i0 lc0 gl0) as [lc1 [gl1 HrollbackEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply rollbackEnv_uniq in HrollbackEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_cast i0 c t v t0)(i0:=i0)(lc2:=lc2)(gl2:=gl2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0)(gl0:=gl0); auto.

            exists gv3. split; eauto using lookupEnv_rollbackEnv_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion cast_denotes_gv3; subst. clear cast_denotes_gv3.
            apply sterm_cast_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(gl2:=gl2)(i0:=i0)(lc0:=lc0)(gl0:=gl0)(cs:=cs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_cast c t (value2Sterm (env_to_smap gl1 lc1) v) t0).
              split; auto using binds_updateSmap_eq.
                inversion cast_denotes_gv3; subst.
                apply sterm_cast_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.

  Case "insn_icmp".
    assert (binds i0  
             (sterm_icmp c t (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                             (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0))
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_icmp i0 c t v v0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [icmp_denotes_gv3 gv3_in_env2]].
    destruct (@exists_rollbackEnv lc2 gl2 i0 lc0 gl0) as [lc1 [gl1 HrollbackEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply rollbackEnv_uniq in HrollbackEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_icmp i0 c t v v0)(i0:=i0)(lc2:=lc2)(gl2:=gl2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0)(gl0:=gl0); auto.

            exists gv3. split; eauto using lookupEnv_rollbackEnv_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion icmp_denotes_gv3; subst. clear icmp_denotes_gv3.
            apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(gl2:=gl2)(i0:=i0)(lc0:=lc0)(gl0:=gl0)(cs:=cs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_icmp c t (value2Sterm (env_to_smap gl1 lc1) v) (value2Sterm (env_to_smap gl1 lc1) v0)).
              split; auto using binds_updateSmap_eq.
                inversion icmp_denotes_gv3; subst.
                apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.

  Case "insn_select".
    assert (binds i0  
             (sterm_select (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                           t
                           (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0)
                           (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v1))
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_select i0 v t v0 v1)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [select_denotes_gv3 gv3_in_env2]].
    destruct (@exists_rollbackEnv lc2 gl2 i0 lc0 gl0) as [lc1 [gl1 HrollbackEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply rollbackEnv_uniq in HrollbackEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_select i0 v t v0 v1)(i0:=i0)(lc2:=lc2)(gl2:=gl2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0)(gl0:=gl0); auto.

            exists gv3. split; eauto using lookupEnv_rollbackEnv_Some_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion select_denotes_gv3; subst. clear select_denotes_gv3.
            eapply sterm_select_denotes with (gv0:=gv0)(gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply se_cmds_denotes__decomposes__prefix_last__case2 with (st':=st')(Mem0:=Mem0)(lc2:=lc2)(gl2:=gl2)(i0:=i0)(lc0:=lc0)(gl0:=gl0)(cs:=cs); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_select (value2Sterm (env_to_smap gl1 lc1) v) t (value2Sterm (env_to_smap gl1 lc1) v0) (value2Sterm (env_to_smap gl1 lc1) v1)).
              split; auto using binds_updateSmap_eq.
                inversion select_denotes_gv3; subst.
                eapply sterm_select_denotes with (gv0:=gv0)(gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        env_to_smap_uniq, env_to_smap_denotes_gvmap.
Qed.

 

Lemma se_cmds_denotes__composes__prefix_last__case1 : forall TD lc0 gl0 Mem0 cs lc1 gl1 lc2 gl2 Mem1 id' st' c i0,
  smap_denotes_gvmap TD lc0 gl0 Mem0 (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) lc1 gl1 ->
  smap_denotes_gvmap TD lc1 gl1 Mem1 (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) c)) lc2 gl2 ->
  getCmdID c = i0 ->
  i0 <> id' ->
  binds id' st' (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) ->
  exists gv', sterm_denotes_genericvalue TD lc0 gl0 Mem0 st' gv' /\ lookupEnv lc2 gl2 id' = ret gv'.
Proof.
  intros TD lc0 gl0 Mem0 cs lc1 gl1 lc2 gl2 Mem1 id' st' c i0 [Hsterms_denote11 Hsterms_denote12]
     [Hsterms_denote21 Hsterms_denote22] HgetCmdID i0_isnt_id' binds_id'_st'.
            assert (J:=binds_id'_st').
            apply Hsterms_denote11 in J.
            destruct J as [gv' [st'_denotes_gv' id'_gv'_in_env1]].
            apply lookupEnv_env_to_smap in id'_gv'_in_env1.
            apply binds_se_cmd with (i1:=i0)(smem1:=smem_init)(sframe1:=sframe_init)(seffects1:=nil)(c:=c) in id'_gv'_in_env1; auto.
            apply Hsterms_denote21 in id'_gv'_in_env1.
            destruct id'_gv'_in_env1 as [gv'0 [id'_denotes_gv'0 id'_gv'0_in_env2]].
            inversion id'_denotes_gv'0; subst.
            simpl in H4.
            apply Hsterms_denote12 in H4.
            destruct H4 as [st'0 [binds_id'_st'0 st'0_denotes_gv'0]].
            apply binds_unique with (b:=st'0) in binds_id'_st'; eauto using env_to_smap_uniq, se_cmds_uniq.
            subst.
            apply sterm_denotes_genericvalue_det with (gv2:=gv') in st'0_denotes_gv'0; auto.
            subst.
            exists gv'. split; auto.
Qed.

Lemma se_cmds_denotes__composes__prefix_last__case2 : forall TD lc1 gl1 Mem1 lc0 gl0 Mem0 v gv1 cs,  
  uniq lc1 ->
  uniq gl1 ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) lc1 gl1 ->
  sterm_denotes_genericvalue TD lc1 gl1 Mem1 (value2Sterm (env_to_smap gl1 lc1) v) gv1 ->
  sterm_denotes_genericvalue TD lc0 gl0 Mem0 (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v) gv1.
Proof.
  intros TD lc1 gl1 Mem1 lc0 gl0 Mem0 v gv1 cs U1 U2 H1 H2.
                apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H2; auto.
                  apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq, se_cmds_uniq.
                  apply env_to_smap_uniq.
                  rewrite env_to_smap_dom_eq. fsetdec.
                  apply env_to_smap_denotes_gvmap; auto.
Qed.

Lemma se_cmds_denotes__composes__prefix_last__case3 : forall TD lc1 gl1 Mem1 lc0 gl0 Mem0 cs c st' gv' id' i0,  
  uniq lc1 ->
  uniq gl1 ->
  getCmdID c = i0 ->
  i0 <> id' ->
  binds id' st' (env_to_smap gl1 lc1) ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) lc1 gl1 ->
  sterm_denotes_genericvalue TD lc1 gl1 Mem1 st' gv' ->
  exists st'0,
    binds id' st'0
      (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) c)) /\
    sterm_denotes_genericvalue TD lc0 gl0 Mem0 st'0 gv'.
Proof.
  intros TD lc1 gl1 Mem1 lc0 gl0 Mem0 cs c st' gv' id' i0 
    Uc1 Uq1 HgetCmdID i0_isnt_id' binds_id'_st' [Hsterms_denote11 Hsterms_denote12] st'_denotes_gv'.
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
    destruct (@se_cmd_updateSmap_inv c (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) as [J1 | [st0 J1]];
      rewrite J1; auto.
      apply binds_updateSmap_neq; auto.      
Qed.

Lemma se_cmds_denotes__composes__prefix_last : forall c TD lc1 gl1 als1 Mem1 
  lc2 gl2 als2 Mem2 lc0 gl0 als0 Mem0 tr1 tr2 cs,
  uniq lc1 ->
  uniq gl1 ->
  wf_cmds (cs++(c::nil)) ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) lc1 gl1 als1 Mem1 tr1 ->
  sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) c) lc2 gl2 als2 Mem2 tr2 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) (cs++c::nil)) lc2 gl2 als2 Mem2 (trace_app tr1 tr2).
Proof.
  intros c TD lc1 gl1 als1 Mem1 lc2 gl2 als2 Mem2 lc0 gl0 als0 Mem0 tr1 tr2 cs Huniqc1 Huniqg1 Wf Hdenotes1 Hdenotes2.
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
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (cs:=cs)(lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(c:=insn_bop i0 b s v v0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_bop b s (value2Sterm (env_to_smap gl1 lc1) v) (value2Sterm (env_to_smap gl1 lc1) v0))
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_bop id' b s v v0)))
            ) as binds_id'_bop.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_bop.
            destruct binds_id'_bop as [gv' [bop_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion bop_denotes_gv'; subst.

              apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_bop b s 
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0)).
          split.
            simpl. apply binds_updateSmap_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.
 
  Case "insn_extractvalue".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (cs:=cs)(lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(c:=insn_extractvalue i0 t v l0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_extractvalue t (value2Sterm (env_to_smap gl1 lc1) v) l0)
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_extractvalue id' t v l0)))
            ) as binds_id'_extractvalue.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_extractvalue.
            destruct binds_id'_extractvalue as [gv' [extractvalue_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion extractvalue_denotes_gv'; subst.

              apply sterm_extractvalue_denotes with (gv1:=gv1); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_extractvalue t
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                   l0).
          split.
            simpl. apply binds_updateSmap_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_extractvalue_denotes with (gv1:=gv1);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_insertvalue".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (cs:=cs)(lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(c:=insn_insertvalue i0 t v t0 v0 l0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_insertvalue t (value2Sterm (env_to_smap gl1 lc1) v) t0 (value2Sterm (env_to_smap gl1 lc1) v0) l0)
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_insertvalue id' t v t0 v0 l0)))
            ) as binds_id'_insertvalue.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_insertvalue.
            destruct binds_id'_insertvalue as [gv' [insertvalue_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion insertvalue_denotes_gv'; subst.

              apply sterm_insertvalue_denotes with (gv1:=gv1) (gv2:=gv2); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_insertvalue t
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                   t0
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0)
                   l0).
          split.
            simpl. apply binds_updateSmap_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_insertvalue_denotes with (gv1:=gv1) (gv2:=gv2);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_malloc".
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (cs:=cs)(lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(c:=insn_malloc i0 t s a)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_malloc smem_init t s a)
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_malloc id' t s a)))
            ) as binds_id'_malloc.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_malloc.
            destruct binds_id'_malloc as [gv' [malloc_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion malloc_denotes_gv'; subst.

              inversion H8; subst.
              apply sterm_malloc_denotes with (Mem1:=Mem4)(Mem2:=Mem5)(tsz0:=tsz0); eauto.

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_malloc (SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) t s a).
          split.
            simpl. apply binds_updateSmap_eq; auto.
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
        apply lookupEnv_env_to_smap in id'_gv'_in_env1.
        apply Hsterms_denote21 in id'_gv'_in_env1.
        destruct id'_gv'_in_env1 as [gv'0 [id'_denotes_gv'0 id'_gv'0_in_env2]].
        inversion id'_denotes_gv'0; subst.
        simpl in H5.
        apply Hsterms_denote12 in H5.
        destruct H5 as [st'0 [binds_id'_st'0 st'0_denotes_gv'0]].
        apply binds_unique with (b:=st'0) in H; eauto using env_to_smap_uniq, se_cmds_uniq.
        subst.
        apply sterm_denotes_genericvalue_det with (gv2:=gv') in st'0_denotes_gv'0; auto.
        subst.
        exists gv'. split; auto.

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
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

    split. clear Hsframe_denotes2 Hsframe_denotes1 Hseffects_denote2 Hseffects_denote1.
           inversion Hsmem_denotes2; subst.
           inversion H7; subst.
           simpl. 
           assert (union (dom lc1) (dom gl1) [<=] dom (env_to_smap gl1 lc1)) as Sub.
             rewrite env_to_smap_dom_eq. fsetdec.
           apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H2; 
            try solve [eauto using env_to_smap_uniq, env_to_smap_denotes_gvmap| split; auto].
           eapply smem_free_denotes; eauto using genericvalue__implies__value2Sterm_denotes.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_alloca".
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (cs:=cs)(lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(c:=insn_alloca i0 t s a)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_alloca smem_init t s a)
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_alloca id' t s a)))
            ) as binds_id'_alloca.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_alloca.
            destruct binds_id'_alloca as [gv' [alloca_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion alloca_denotes_gv'; subst.

              inversion H8; subst. clear H8.
              apply sterm_alloca_denotes with (Mem1:=Mem4)(Mem2:=Mem5)(tsz0:=tsz0); eauto.

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_alloca (SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) t s a).
          split.
            simpl. apply binds_updateSmap_eq; auto.
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
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (cs:=cs)(lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(c:=insn_load i0 t v)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_load smem_init t (value2Sterm (env_to_smap gl1 lc1) v))
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_load id' t v)))
            ) as binds_id'_load.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_load.
            destruct binds_id'_load as [gv' [load_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion load_denotes_gv'; subst.

              inversion H7; subst. clear H7.
              eapply sterm_load_denotes with (gv0:=gv0);
                try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem4); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_load (SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) t
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)).
          split.
            simpl. apply binds_updateSmap_eq; auto.
            inversion st'_denotes_gv'; subst.
            inversion H7; subst. clear H7.
            eapply sterm_load_denotes with (gv0:=gv0);
                try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem4); auto].
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
        apply lookupEnv_env_to_smap in id'_gv'_in_env1.
        apply Hsterms_denote21 in id'_gv'_in_env1.
        destruct id'_gv'_in_env1 as [gv'0 [id'_denotes_gv'0 id'_gv'0_in_env2]].
        inversion id'_denotes_gv'0; subst.
        simpl in H5.
        apply Hsterms_denote12 in H5.
        destruct H5 as [st'0 [binds_id'_st'0 st'0_denotes_gv'0]].
        apply binds_unique with (b:=st'0) in H; eauto using env_to_smap_uniq, se_cmds_uniq.
        subst.
        apply sterm_denotes_genericvalue_det with (gv2:=gv') in st'0_denotes_gv'0; auto.
        subst.
        exists gv'. split; auto.

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
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

    split. clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22
                 Hsframe_denotes2 Hsframe_denotes1 Hseffects_denote2 Hseffects_denote1.
           inversion Hsmem_denotes2; subst.
           inversion H10; subst.
           simpl. 
           assert (union (dom lc1) (dom gl1) [<=] dom (env_to_smap gl1 lc1)) as Sub.
             rewrite env_to_smap_dom_eq. fsetdec.
           apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H3; 
            try solve [eauto using env_to_smap_uniq, env_to_smap_denotes_gvmap| split; auto].
           apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H8; 
            try solve [eauto using env_to_smap_uniq, env_to_smap_denotes_gvmap| split; auto].
           eapply smem_store_denotes; eauto using genericvalue__implies__value2Sterm_denotes.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_gep".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (cs:=cs)(lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(c:=insn_gep i0 i1 t v l0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_gep i1 t (value2Sterm (env_to_smap gl1 lc1) v)
                              (List.map (value2Sterm (env_to_smap gl1 lc1)) l0))
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_gep id' i1 t v l0)))
            ) as binds_id'_gep.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_gep.
            destruct binds_id'_gep as [gv' [gep_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion gep_denotes_gv'; subst.

              eapply sterm_gep_denotes with (gv0:=gv0)(gvs0:=gvs0);
                try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].
                apply value2Sterm_denote__imply__genericvalues with (lc:=lc1)(gl:=gl1) in H8; auto.
                  apply genericvalues__imply__value2Sterm_denote with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq, se_cmds_uniq.
                  apply se_cmds_env_to_smap_dom_sub.
                  apply env_to_smap_uniq.
                  rewrite env_to_smap_dom_eq. fsetdec.
                  apply env_to_smap_denotes_gvmap; auto.

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_gep i1 t 
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                   (List.map (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))) l0)).
          split.
            simpl. apply binds_updateSmap_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_gep_denotes with (gv0:=gv0)(gvs0:=gvs0)(mp0:=mp0)(ns0:=ns0);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].
                apply value2Sterm_denote__imply__genericvalues with (lc:=lc1)(gl:=gl1) in H8; auto.
                  apply genericvalues__imply__value2Sterm_denote with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq, se_cmds_uniq.
                  apply se_cmds_env_to_smap_dom_sub.
                  apply env_to_smap_uniq.
                  rewrite env_to_smap_dom_eq. fsetdec.
                  apply env_to_smap_denotes_gvmap; auto.

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_ext".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (cs:=cs)(lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(c:=insn_ext i0 e t v t0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_ext e t (value2Sterm (env_to_smap gl1 lc1) v) t0)
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_ext id' e t v t0)))
            ) as binds_id'_ext.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_ext.
            destruct binds_id'_ext as [gv' [ext_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion ext_denotes_gv'; subst.

              apply sterm_ext_denotes with (gv1:=gv1); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_ext e t
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v) t0).
          split.
            simpl. apply binds_updateSmap_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_ext_denotes with (gv1:=gv1);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_cast".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (cs:=cs)(lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(c:=insn_cast i0 c t v t0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_cast c t (value2Sterm (env_to_smap gl1 lc1) v) t0)
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_cast id' c t v t0)))
            ) as binds_id'_cast.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_cast.
            destruct binds_id'_cast as [gv' [cast_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion cast_denotes_gv'; subst.

              apply sterm_cast_denotes with (gv1:=gv1); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_cast c t 
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v) t0).
          split.
            simpl. apply binds_updateSmap_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_cast_denotes with (gv1:=gv1);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_icmp".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (cs:=cs)(lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(c:=insn_icmp i0 c t v v0)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_icmp c t (value2Sterm (env_to_smap gl1 lc1) v) (value2Sterm (env_to_smap gl1 lc1) v0))
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_icmp id' c t v v0)))
            ) as binds_id'_icmp.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_icmp.
            destruct binds_id'_icmp as [gv' [icmp_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion icmp_denotes_gv'; subst.

              apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_icmp c t
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0)).
          split.
            simpl. apply binds_updateSmap_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_select".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (cs:=cs)(lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(c:=insn_select i0 v t v0 v1)(i0:=i0); try solve [auto | split; auto].

            assert (binds id' (sterm_select (value2Sterm (env_to_smap gl1 lc1) v) t (value2Sterm (env_to_smap gl1 lc1) v0) (value2Sterm (env_to_smap gl1 lc1) v1))
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_select id' v t v0 v1)))
            ) as binds_id'_select.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_select.
            destruct binds_id'_select as [gv' [select_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion select_denotes_gv'; subst.

              apply sterm_select_denotes with (gv0:=gv0)(c0:=c0)(gv1:=gv1)(gv2:=gv2); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(st':=st')(i0:=i0); try solve [auto | split; auto].

          exists (sterm_select
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                   t
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0)
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v1)).
          split.
            simpl. apply binds_updateSmap_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_select_denotes with (gv0:=gv0)(c0:=c0)(gv1:=gv1)(gv2:=gv2);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1); auto].
    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.
Qed.

Definition se_cmds_denotes__decomposes__app_prop (cs2:list cmd) :=
forall TD lc0 gl0 als0 Mem0 cs1 lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  uniq gl2 ->
  uniq lc2 ->
  wf_cmds (cs1++cs2) ->
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
    rewrite <- app_nil_end in H4.
    split; auto.
    split; auto.
      apply env_to_smap_denotes_id; auto.
  Case "cons".
    rewrite <- app_ass in H5.
    rewrite se_cmds_rev_cons in H5.
    rewrite <- app_ass in H4.
    apply se_cmds_denotes__decomposes__prefix_last in H5; auto.
    destruct H5 as [lc1 [gl1 [als1 [Mem1 [tr1 [tr2 [env0_denotes_env1 [env1_denotes_env2 [EQ [Huniqg1 Huniqc1]]]]]]]]]]; subst.
    assert (J:=H4).
    apply wf_cmds__decomposes__app in J. 
    destruct J as [H41 H42].
    apply H in env0_denotes_env1; auto.
    destruct env0_denotes_env1 as [lc3 [gl3 [als3 [Mem3 [tr3 [tr4 [env0_denotes_env3 [env3_denotes_env1 [EQ [Huniqg3 Huniqc3]]]]]]]]]]; subst.
    exists lc3. exists gl3. exists als3. exists Mem3. exists tr3. exists (trace_app tr4 tr2).
    rewrite trace_app_commute.
    split; auto.
    split; auto.
      rewrite app_ass in H4.
      apply wf_cmds__decomposes__app in H4. 
      destruct H4 as [H51 H52].
      apply se_cmds_denotes__composes__prefix_last with (lc1:=lc1)(gl1:=gl1)(als1:=als1)(Mem1:=Mem1); eauto.
Qed.

Lemma se_cmds_denotes__decomposes__head_tail : forall c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  uniq gl2 ->
  uniq lc2 ->
  wf_cmds (c::cs) ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (se_cmd (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) c) cs) lc2 gl2 als2 Mem2 tr ->
  exists lc1, exists gl1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) c) lc1 gl1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmds (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) cs) lc2 gl2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ uniq gl1 /\ uniq lc1.
Proof.
  intros c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr Huniqg0 Huniqc0 Huniqg2 Huniqc2 Wf Hdenotes.
  rewrite <- se_cmds_cons in Hdenotes.
  apply se_cmds_denotes__decomposes__app in Hdenotes; auto.
Qed.    
  
Lemma se_cmds__denote__exists_op_cmds : forall cs S TD Ps F B call0 sbs tmn lc1 arg als1 ECs gl1 Mem1 lc2 gl2 als2 Mem2 tr,
  uniq gl1 ->
  uniq lc1 ->
  uniq gl2 ->
  uniq lc2 ->
  wf_cmds cs ->
  sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmds (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) cs) lc2 gl2 als2 Mem2 tr ->
  exists lc2', exists gl2', exists als2, exists Mem2', exists tr', 
    dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
           (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc2' arg als2)::ECs) gl2' Mem2')
           tr'.
Proof.
  induction cs; 
    intros S TD Ps F B call0 sbs tmn lc1 arg0 als1 ECs gl1 Mem1 lc2 gl2 als2 Mem2 tr Uniqg1 Uniqc1 Uniqg2 Uniqc2 Wf Hdenotes.

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
    apply wf_cmds__inv in Wf.
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
  wf_cmds cs ->
  sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmds (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) cs) lc2 gl2 als2 Mem2 tr ->
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
         (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc2 arg als2)::ECs) gl2 Mem2)
         tr. 
Proof.
  intros S TD Ps F B cs call0 sbs tmn lc1 arg0 ECs gl1 als1 Mem1 lc2 als2 gl2 Mem2 tr Huniqg1 Huniqc1 Huniqg2 Huniqc2 Wf Hdenotes.
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
  wf_cmds cs' ->
  tv_cmds cs cs' lc1 gl1 ->
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
        (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc2 arg als2)::ECs) gl2 Mem2)
        tr ->
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs' call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
        (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc2 arg als2)::ECs) gl2 Mem2)
        tr.
Proof.
  intros S TD Ps F B cs cs' call0 sbs tmn lc1 arg0 als1 ECs gl1 Mem1 lc2 als2 gl2 Mem2 tr Huniqg Huniqc Wf Htv_cmds HdbCmds.
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
