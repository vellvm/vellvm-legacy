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

Export SimpleSE.

(* Symbolic execuction is complete:
   Any concrete execution of a subblock satisfies its symbolic execution. *)

Lemma genericvalue__implies__value2Sterm_denotes : forall TD lc0 gl0 Mem0 smap1 lc gl v gv,
  uniq smap1 ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 smap1 lc gl ->
  getOperandValue TD v lc gl = Some gv ->
  sterm_denotes_genericvalue TD lc0 gl0 Mem0 (value2Sterm smap1 v) gv.
Proof.
  intros D lc0 gl0 Mem0 smap1 lc gl v gv Huniq Hdenotes J.
  unfold getOperandValue in J.
  unfold smap_denotes_gvmap in Hdenotes.
  destruct Hdenotes as [J1 J2].
  destruct v.
    apply J2 in J.
    destruct J as [st0 [J3 J4]].
    rewrite id2Sterm_in with (st0:=st0); auto.

    rewrite const2Sterm; auto.
Qed.

Lemma genericvalues__imply__value2Sterm_denote : forall l0 TD lc0 gl0 Mem0 smap1 lc gl gvs0,
  uniq smap1 ->
  (dom lc0 `union` dom gl0) [<=] dom smap1 ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 smap1 lc gl ->
  values2GVs TD l0 lc gl = Some gvs0 ->
  sterms_denote_genericvalues TD lc0 gl0 Mem0 
    (map_list_value (value2Sterm smap1) l0) gvs0.
Proof.
  induction l0; intros; simpl in *.
    inversion H2; subst; auto.

    remember (getOperandValue TD v lc gl) as ogv.
    destruct ogv; try solve [inversion H2].
    remember (values2GVs TD l0 lc gl) as ogvs.
    destruct ogvs; try solve [inversion H2].
    inversion H2; subst.
    apply sterms_cons_denote; eauto using genericvalue__implies__value2Sterm_denotes.
Qed.

Lemma se_cmd__denotes__op_cmd__case1 : forall lc gl i0 gv3 lc' gl' id' st' smap1 TD lc0 gl0 Mem0,
  updateEnv lc gl i0 gv3 = (lc', gl') ->
  i0 <> id' ->
  binds id' st' smap1 ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 smap1 lc gl ->
  exists gv',
    sterm_denotes_genericvalue TD lc0 gl0 Mem0 st' gv' /\
    lookupEnv lc' gl' id' = Some gv'.
Proof.
  intros lc gl i0 gv3 lc' gl' id' st' smap1 TD lc0 gl0 Mem0 H25 nEQ Hbinds Hsterm_denotes.
  apply lookupEnv_updateEnv_neq with (id1:=id') in H25; auto.
  rewrite <- H25. 
  unfold smap_denotes_gvmap in Hsterm_denotes.
  destruct Hsterm_denotes as [J1 J2].
  apply J1 in Hbinds.
  destruct Hbinds as [gv' [J3 J4]].
  exists gv'. split; auto.
Qed.

Lemma se_cmd__denotes__op_cmd__case2 : forall lc gl i0 gv3 lc' gl' id' smap1 TD lc0 gl0 Mem0 gv' st0,
  updateEnv lc gl i0 gv3 = (lc', gl') ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 smap1 lc gl ->
  lookupEnv lc' gl' id' = Some gv' ->
  id' <> i0 ->
  exists st', binds id' st' (updateSmap smap1 i0 st0) /\ 
              sterm_denotes_genericvalue TD lc0 gl0 Mem0 st' gv'.
Proof.
  intros lc gl i0 gv3 lc' gl' id' smap1 TD lc0 gl0 Mem0 gv' st0 H25 Hsterm_denotes HlookupEnv n.
  apply lookupEnv_updateEnv_neq with (id1:=id') in H25; auto.
  rewrite <- H25 in HlookupEnv.
  destruct Hsterm_denotes as [J1 J2].
  apply J2 in HlookupEnv; auto.
  destruct HlookupEnv as [st' [J3 J4]].
  exists st'. split; auto.
    apply binds_updateSmap_neq; auto.
Qed.

Lemma op_cmd__satisfies__se_cmd : forall TD c nc lc als gl lc0 gl0 als0 Mem0 lc' als' gl' Mem1 Mem2 sstate1 tr tr1,
  dbCmd TD lc als gl Mem1 c lc' als' gl' Mem2 tr -> 
  uniq sstate1.(STerms) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 sstate1 lc gl als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd sstate1 (mkNB c nc)) lc' gl' als' Mem2 (trace_app tr1 tr).
Proof.
  intros TD c nc lc als gl lc0 gl0 als0 Mem0 lc' als' gl' Mem1 Mem2 sstate1 tr tr1
         HdsInsn Huniq Hsub Hdenotes.
  (cmd_cases (destruct c) Case);
              inversion HdsInsn; subst;
              destruct Hdenotes as [Hsterm_denotes [Hsmem_denotes [Hsframe_denotes Hseffects_denote]]];
              rewrite trace_app_nil__eq__trace.
  Case "insn_bop".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H15; auto.
          rewrite H15.
          apply BOP_inversion in H14.
          destruct H14 as [gv1 [gv2 [J1 [J2 J3]]]].
          exists gv3. split; auto.
          apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_bop b s (value2Sterm (STerms sstate1) v) (value2Sterm (STerms sstate1) v0)).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H15; auto.
            rewrite H15 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply BOP_inversion in H14.
            destruct H14 as [gv1 [gv2 [J1 [J2 J3]]]].
            apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_extractvalue".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H15; auto.
          rewrite H15.
          exists gv'. split; auto.
          apply sterm_extractvalue_denotes with (gv1:=gv); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv'0 HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_extractvalue t (value2Sterm (STerms sstate1) v) l0).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H15; auto.
            rewrite H15 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply sterm_extractvalue_denotes with (gv1:=gv); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_insertvalue".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H18; auto.
          rewrite H18.
          exists gv''. split; auto.
          eapply sterm_insertvalue_denotes; eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv'0 HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_insertvalue t (value2Sterm(STerms sstate1) v) t0 (value2Sterm (STerms sstate1) v0) l0).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H18; auto.
            rewrite H18 in HlookupEnv.
            inversion HlookupEnv; subst.
            eapply sterm_insertvalue_denotes; eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_malloc".
    split; simpl; eauto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H15; auto.
          rewrite H15.
          exists (ptr2GV TD (mb, 0)).
          split; auto.
            eapply sterm_malloc_denotes; eauto.

        intros id' gv'0 HlookupEnv.
        simpl.
        destruct (id'==i0); subst.
          exists (sterm_malloc (SMem sstate1) t s a).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H15; auto.
            rewrite H15 in HlookupEnv.
            inversion HlookupEnv; subst.
            eapply sterm_malloc_denotes; eauto.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_free".
    split; simpl.
      destruct Hsterm_denotes as [J1 J2].
      split; auto.
    split; auto.     
      apply getOperandPtr_inversion in H12.
      destruct H12 as [gv [J1 J2]].
      apply smem_free_denotes with (Mem1:=Mem1)(gv0:=gv)(mptr0:=mptr); auto.
        eapply genericvalue__implies__value2Sterm_denotes; eauto.
    
  Case "insn_alloca".
    split; simpl; eauto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H15; auto.
          rewrite H15.
          exists (ptr2GV TD (mb, 0)).
          split; auto.
          eapply sterm_alloca_denotes; eauto.

        intros id' gv'0 HlookupEnv.
        simpl.
        destruct (id'==i0); subst.
          exists (sterm_alloca (SMem sstate1) t s a).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H15; auto.
            rewrite H15 in HlookupEnv.
            inversion HlookupEnv; subst.
            eapply sterm_alloca_denotes; eauto.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_load".
    split; simpl; eauto.
      apply getOperandPtr_inversion in H7.
      destruct H7 as [gv2 [J1 J2]].
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H14; auto.
          rewrite H14.
          exists gv.
          split; auto.
          apply sterm_load_denotes with (Mem1:=Mem2)(gv0:=gv2)(mp0:=mp); eauto.
            eapply genericvalue__implies__value2Sterm_denotes; eauto.
     
        intros id' gv'0 HlookupEnv.
        simpl.
        destruct (id'==i0); subst.
          exists (sterm_load (SMem sstate1) t (value2Sterm (STerms sstate1) v)).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H14; auto.
            rewrite H14 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply sterm_load_denotes with (Mem1:=Mem2)(gv0:=gv2)(mp0:=mp); eauto.
              eapply genericvalue__implies__value2Sterm_denotes; eauto.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_store".
    split; simpl.
      destruct Hsterm_denotes as [J1 J2].
      split; auto.
    split; auto.
      apply getOperandPtr_inversion in H14.
      destruct H14 as [gv2 [J1 J2]].
      eapply smem_store_denotes; 
        eauto using genericvalue__implies__value2Sterm_denotes.

  Case "insn_gep". 
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        apply getOperandPtr_inversion in H14.
        destruct H14 as [gv0 [J1 J2]].
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H16; auto.
          rewrite H16.
          apply GEP_inversion in H15.
          destruct H15 as [idxs [J3 J4]].
          apply intValues2Nats_inversion in J3.
          destruct J3 as [gvs0 [J31 J32]].
          exists (ptr2GV TD mp').
          split; auto.
            eapply sterm_gep_denotes; eauto using genericvalue__implies__value2Sterm_denotes, genericvalues__imply__value2Sterm_denote.

        intros id' gv' HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_gep i1 t (value2Sterm (STerms sstate1) v) (map_list_value (value2Sterm (STerms sstate1)) l0)).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H16; auto.
            rewrite H16 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply getOperandPtr_inversion in H14.
            destruct H14 as [gv0 [J1 J2]].
            apply GEP_inversion in H15.
            destruct H15 as [idxs [J3 J4]].
            apply intValues2Nats_inversion in J3.
            destruct J3 as [gvs0 [J31 J32]].
            eapply sterm_gep_denotes; eauto using genericvalue__implies__value2Sterm_denotes, genericvalues__imply__value2Sterm_denote.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_ext".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H15; auto.
          rewrite H15.
          apply EXT_inversion in H14.
          destruct H14 as [gv1 [J1 J2]].
          exists gv2. split; auto.
            apply sterm_ext_denotes with (gv1:=gv1); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_ext e t (value2Sterm (STerms sstate1) v) t0).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H15; auto.
            rewrite H15 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply EXT_inversion in H14.
            destruct H14 as [gv1 [J1 J2]].
            apply sterm_ext_denotes with (gv1:=gv1); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_cast".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H15; auto.
          rewrite H15.
          apply CAST_inversion in H14.
          destruct H14 as [gv1 [J1 J2]].
          exists gv2. split; auto.
            apply sterm_cast_denotes with (gv1:=gv1); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_cast c t (value2Sterm (STerms sstate1) v) t0).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H15; auto.
            rewrite H15 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply CAST_inversion in H14.
            destruct H14 as [gv1 [J1 J2]].
            apply sterm_cast_denotes with (gv1:=gv1); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_icmp".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H15; auto.
          rewrite H15.
          apply ICMP_inversion in H14.
          destruct H14 as [gv1 [gv2 [J1 [J2 J3]]]].
          exists gv3. split; auto.
            apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_icmp c t (value2Sterm (STerms sstate1) v) (value2Sterm (STerms sstate1) v0)).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H15; auto.
            rewrite H15 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply ICMP_inversion in H14.
            destruct H14 as [gv1 [gv2 [J1 [J2 J3]]]].
            apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_select".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          destruct cond0; eapply se_cmd__denotes__op_cmd__case1; eauto.

          symmetry in H17.
          apply getOperandInt_inversion in H14. destruct H14 as [gv5 [J1 J2]].
          destruct cond0; apply lookupEnv_updateEnv_eq in H17; auto.
            exists gv1.
            split; auto.
              apply sterm_select_denotes with (c0:=0)(gv0:=gv5)(gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

            exists gv2.
            split; auto.
              apply sterm_select_denotes with (c0:=Datatypes.S cond0)(gv0:=gv5)(gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_select (value2Sterm (STerms sstate1) v) t (value2Sterm (STerms sstate1) v0) (value2Sterm (STerms sstate1) v1)).
          split. 
            apply binds_updateSmap_eq; auto.

            apply getOperandInt_inversion in H14. destruct H14 as [gv5 [J1 J2]].
            apply sterm_select_denotes with (c0:=cond0)(gv0:=gv5)(gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.
            symmetry in H17.
            destruct cond0;
              apply lookupEnv_updateEnv_eq in H17; auto;
              rewrite H17 in HlookupEnv;
              inversion HlookupEnv; subst; auto.

          destruct cond0; eapply se_cmd__denotes__op_cmd__case2; eauto.
Qed.

Lemma aux__op_cmds__satisfy__se_cmds : forall nbs TD lc0 als gl0 als0 Mem0 lc als' gl Mem1 sstate1 lc' gl' Mem2 tr tr1,
  dbCmds TD lc als gl Mem1 (nbranchs2cmds nbs) lc' als' gl' Mem2 tr ->
  uniq sstate1.(STerms) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 sstate1 lc gl als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds sstate1 nbs) lc' gl' als' Mem2 (trace_app tr1 tr).
Proof.
  induction nbs; 
    intros TD lc0 als gl0 als0 Mem0 lc als' gl Mem1 sstate1 lc' gl' Mem2 tr tr1 
    HdbCmds Huniq Hsub Hdenotes.

    simpl in HdbCmds.
    inversion HdbCmds; subst; try solve [rewrite trace_app_nil__eq__trace; auto].

    destruct a as [c nc].
    simpl in HdbCmds.
    inversion HdbCmds; subst.
    apply op_cmd__satisfies__se_cmd with (lc0:=lc0)(gl0:=gl0)(sstate1:=sstate1)(als0:=als0)(Mem0:=Mem0)(tr1:=tr1)(nc:=nc) in H6; auto.
    rewrite trace_app_commute.
    apply IHnbs with (lc0:=lc0)(gl0:=gl0)(sstate1:=se_cmd sstate1 (mkNB c nc))(als0:=als0)(Mem0:=Mem0)(tr1:=trace_app tr1 t1) in H12; auto.
      apply _se_cmd_uniq; auto.

      assert (J:=@se_cmd_dom_mono' sstate1 (mkNB c nc)).
      clear - J Hsub. fsetdec.
Qed.

Lemma op_cmds__satisfy__se_cmds : forall TD nbs lc als gl Mem lc' als' gl' Mem' tr,
  uniq gl ->
  uniq lc ->
  dbCmds TD lc als gl Mem (nbranchs2cmds nbs) lc' als' gl' Mem' tr ->
  sstate_denotes_state TD lc gl als Mem (se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) nbs) lc' gl' als' Mem' tr.
Proof.
  intros TD nbs lc als gl Mem0 lc' als' gl' Mem' tr Uniqg Uniqc HdbCmds.
  apply aux__op_cmds__satisfy__se_cmds with (lc0:=lc)(gl0:=gl)(als0:=als)(Mem0:=Mem0)(sstate1:=mkSstate (env_to_smap gl lc) smem_init sframe_init nil) (tr1:=trace_nil)(nbs:=nbs) in HdbCmds; simpl; auto.
    apply env_to_smap_uniq.
    rewrite env_to_smap_dom_eq. fsetdec.
    apply env_to_smap_denotes_id; auto.
Qed.           


