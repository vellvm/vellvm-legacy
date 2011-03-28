Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa/compcert".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import opsem_pp.
Require Import trace.
Require Import assoclist.
Require Import ssa_props.
Require Import CoqListFacts.
Require Import Coqlib.
Require Import symexe_def.

Export SimpleSE.

(* cmd2sbs *)

Lemma cmds2sbs_nil_inv : forall cs,
  cmds2sbs cs = (nil, nil) ->
  cs = nil.
Proof.
  destruct cs; intros; auto.
    simpl in H.
    destruct (isCall_dec c).
      destruct (cmds2sbs cs).
      destruct l0.
        inversion H.
        destruct s. inversion H.
      destruct (cmds2sbs cs).
      inversion H.
Qed.

Lemma cmds2sb_inv : forall cs sb,
  cmds2sbs cs = (sb::nil, nil) ->
  exists cs', exists call0,
    cs = cs'++call0::nil /\
    cmds2sbs cs' = (nil, NBs sb) /\
    call_cmd sb = call0.
Proof.
  induction cs; intros; simpl in *.
    inversion H.

    remember (cmds2sbs cs) as R.
    remember (isCall_dec a) as R'.
    destruct R'.
      destruct R.
      destruct l0.
        inversion H.

        destruct s. inversion H; subst. clear H.
        destruct (@IHcs (mkSB NBs0 call_cmd0 call_cmd_isCall0)) as [cs' [call0 [J1 [J2 J3]]]]; subst; auto.
        clear IHcs.
        simpl in *.
        exists (a::cs').
        exists (call_cmd0).
        split; auto.
        split; auto.
          simpl.
          rewrite J2.
          rewrite <- HeqR'. auto.

      destruct R.
      inversion H; subst. clear H.
      symmetry in HeqR.
      apply cmds2sbs_nil_inv in HeqR. subst.
      exists nil. exists a.
      split; auto.
Qed.

Definition dbCmds__cmds2nbs : forall TD lc als gl Mem1 cs lc' als' Mem2 tr, 
  dbCmds TD gl lc als Mem1 cs lc' als' Mem2 tr ->
  exists nbs, cmds2sbs cs = (nil, nbs).
Proof.
  intros.
  induction H; simpl.
    exists nil. auto.

    destruct IHdbCmds as [nbs J].
    destruct (isCall_dec c).
      rewrite J. exists (mkNB c e::nbs). auto.

      apply dbCmd_isNotCallInst in H.
      rewrite e in H. inversion H.
Qed.

Lemma dbCall_isCall : forall S TD Ps lc gl fs Mem1 c lc' Mem2 tr,
  dbCall S TD Ps fs gl lc Mem1 c lc' Mem2 tr ->
  isCall c = true.
Proof.
  intros S TD Ps lc gl fs Mem1 c lc' Mem2 tr HdbCall.
  induction HdbCall; auto.
Qed.

Lemma cmdscall2sbs : forall cs call0 nbs
  (isCall0:isCall call0=true),
  cmds2sbs cs = (nil, nbs) ->
  isCall_dec call0 = right isCall0 ->
  cmds2sbs (cs++call0::nil) = (mkSB nbs call0 isCall0::nil, nil).
Proof.
  induction cs; intros; simpl in *.
    inversion H; subst.
    rewrite H0. auto.

    destruct (isCall_dec a).
      remember (cmds2sbs cs) as R.
      destruct R.
      destruct l0.
        inversion H; subst. clear H.
        apply IHcs with (nbs:=l1) in H0; auto.
        rewrite H0; auto.
     
        destruct s. inversion H.

      destruct (cmds2sbs cs).
      inversion H.
Qed.

Lemma dbSubblock__cmds2sb : forall S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr,
  dbSubblock S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr ->
  exists sb, cmds2sbs cs = (sb::nil, nil).
Proof.
  intros.
  inversion H; subst.
  apply dbCmds__cmds2nbs in H0.
  destruct H0 as [nbs H0].
  remember (isCall_dec call0) as R.
  destruct R.
    apply dbCall_isCall in H1.
    rewrite e in H1. inversion H1.

    exists (mkSB nbs call0 e).
    apply cmdscall2sbs; auto.
Qed.

Lemma cmds_cons2sbs : forall cs cs' sb sbs',
  cmds2sbs cs = (sb::nil, nil) ->
  cmds2sbs cs' = (sbs', nil) ->
  cmds2sbs (cs++cs') = (sb::sbs', nil).
Proof.
  induction cs; intros; simpl.
    simpl in H. inversion H.

    simpl in H.
    destruct (isCall_dec a).
      remember (cmds2sbs cs) as R.
      destruct R.
        destruct l0.
          inversion H.

          destruct s. inversion H; subst. clear H.
          apply IHcs with (sb:=mkSB NBs0 call_cmd0 call_cmd_isCall0) in H0; auto.
          clear IHcs.
          rewrite H0. auto.
 
      remember (cmds2sbs cs) as R.
      destruct R.
      inversion H; subst. clear H.
      symmetry in HeqR.
      apply cmds2sbs_nil_inv in HeqR. subst.
      simpl.
      rewrite H0. auto.
Qed.

Lemma dbSubblocks__cmds2sbs : forall S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr,
  dbSubblocks S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr ->
  exists sbs, cmds2sbs cs = (sbs, nil).
Proof.
  intros.
  induction H; simpl.
    exists nil. auto.

    apply dbSubblock__cmds2sb in H.
    destruct H as [sb H].
    destruct IHdbSubblocks as [sbs H1].
    exists (sb::sbs).
    apply cmds_cons2sbs; auto.
Qed.

Lemma cmds_cons2sbs_inv : forall cs cs' sbs0 sb sbs',
  cmds2sbs (cs++cs') = (sbs0, nil) ->
  cmds2sbs cs = (sb::nil, nil) ->
  cmds2sbs cs' = (sbs', nil) ->
  sbs0 = sb::sbs'.
Proof.
  intros.
  apply cmds_cons2sbs with (cs':=cs')(sbs':=sbs') in H0; auto.
  rewrite H in H0.
  inversion H0; auto.
Qed.

Lemma cmds2sbs_cons_inv : forall cs0 sb sbs',
  cmds2sbs cs0 = (sb::sbs', nil) ->
  exists cs, exists cs',
    cmds2sbs cs = (sb::nil, nil) /\
    cmds2sbs cs' = (sbs', nil) /\
    cs0 = cs++cs'.
Proof.
  induction cs0; intros.
    simpl in H. inversion H.

    simpl in H.
    remember (isCall_dec a) as R.
    remember (cmds2sbs cs0) as R'.
    destruct R.
      destruct R'.
        destruct l0.
          inversion H.

          destruct s. inversion H; subst. clear H.
          destruct (@IHcs0 (mkSB NBs0 call_cmd0 call_cmd_isCall0) sbs') as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
          exists (a::cs). exists cs'.
          split; auto.
            simpl.
            rewrite <- HeqR.
            rewrite J1. auto.

      destruct R'.
      inversion H; subst. clear H.
      destruct sbs'.
        symmetry in HeqR'.
        apply cmds2sbs_nil_inv in HeqR'. subst.
        exists (a::nil). exists nil.
        simpl. rewrite <- HeqR. auto.

        destruct (@IHcs0 s sbs') as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
        exists (a::nil). exists (cs++cs').
        simpl. rewrite <- HeqR. auto.
Qed.

Lemma cmds_rcons2sbs : forall cs cs' sbs nbs,
  cmds2sbs cs = (sbs, nil) ->
  cmds2sbs cs' = (nil, nbs) ->
  cmds2sbs (cs++cs') = (sbs, nbs).
Proof.
  induction cs; intros.
    simpl in H. inversion H; subst. auto.

    simpl in *.
    remember (cmds2sbs cs) as R.
    destruct (isCall_dec a).
      destruct R.
        destruct l0.
          inversion H.

          destruct s. inversion H; subst. clear H.
          apply IHcs with (sbs:=mkSB NBs0 call_cmd0 call_cmd_isCall0::l0) in H0; auto.
          rewrite H0. auto.

      destruct R.
      inversion H; subst. clear H.
      apply IHcs with (sbs:=l0) in H0; auto.
      rewrite H0. auto.
Qed.

Lemma cmds_rcons2sbs_inv : forall cs cs' sbs0 nbs0 sbs nbs,
  cmds2sbs (cs++cs') = (sbs0, nbs0) ->
  cmds2sbs cs = (sbs, nil) ->
  cmds2sbs cs' = (nil, nbs) ->
  sbs0 = sbs /\ nbs0 = nbs.
Proof.
  intros.
  apply cmds_rcons2sbs with (cs':=cs')(nbs:=nbs) in H0; auto.
  rewrite H in H0. inversion H0; auto.
Qed.
 
Lemma cmds2nbranchs__cmds2nbs : forall cs nbs,
  cmds2nbranchs cs = Some nbs ->
  cmds2sbs cs = (nil, nbs).
Proof.
  induction cs; intros.
    simpl in H. inversion H; auto.

    simpl in *.
    unfold cmd2nbranch in H.
    destruct (isCall_dec a).
      destruct (cmds2sbs cs).
        remember (cmds2nbranchs cs) as R.
        destruct R.
          inversion H; subst. clear H.
          assert (ret l2 = ret l2) as EQ. auto.
          apply IHcs in EQ.
          inversion EQ; subst. auto.

          inversion H.
      inversion H.
Qed.

Lemma cmds2nbs__nbranchs2cmds : forall nbs cs,
  cmds2sbs cs = (nil, nbs) ->
  nbranchs2cmds nbs = cs.
Proof.
  induction nbs; intros.
    apply cmds2sbs_nil_inv in H. subst. auto.

    simpl.
    destruct a.
    destruct cs.
      simpl in H. inversion H.

      simpl in H.
      destruct (isCall_dec c).
        remember (cmds2sbs cs) as R.
        destruct R.
        destruct l0.
          inversion H; subst.
          rewrite IHnbs with (cs:=cs); auto.

          destruct s.
          inversion H; subst.

        destruct (cmds2sbs cs).
        inversion H.
Qed.


Lemma cmds2nbranchs__nbranchs2cmds : forall cs nbs,
  cmds2nbranchs cs = Some nbs ->
  nbranchs2cmds nbs = cs.
Proof.
  intros.
  apply cmds2nbs__nbranchs2cmds.
  apply cmds2nbranchs__cmds2nbs; auto.
Qed.

Lemma cmds2sbs_inv : forall cs sbs nbs,
  cmds2sbs cs = (sbs, nbs) ->
  exists cs1, exists cs2, 
    cs = cs1++cs2 /\
    cmds2sbs cs1 = (sbs, nil) /\
    cmds2sbs cs2 = (nil, nbs).
Proof.
  induction cs; intros.
    simpl in H. inversion H; subst.
    exists nil. exists nil. auto.

    simpl in H.
    remember (isCall_dec a) as R.
    remember (cmds2sbs cs) as R'.
    destruct R.
      destruct R'.
        destruct l0.
          inversion H; subst. clear H.
          
          destruct (@IHcs nil l1) as [cs1 [cs2 [J1 [J2 J3]]]]; subst; auto.
          apply cmds2sbs_nil_inv in J2. subst.
          exists nil. exists (a::cs2).
          simpl. rewrite <- HeqR. 
          simpl in HeqR'. rewrite <- HeqR'.
          split; auto.

       destruct s.
       inversion H; subst. clear H.
       destruct (@IHcs (mkSB NBs0 call_cmd0 call_cmd_isCall0::l0) nbs) as [cs1 [cs2 [J1 [J2 J3]]]]; subst; auto.
       clear IHcs.
       exists (a::cs1). exists cs2.
       simpl. rewrite <- HeqR. rewrite J2. auto.
    
     destruct R'.
     inversion H; subst. clear H.
     destruct (@IHcs l0 nbs) as [cs1 [cs2 [J1 [J2 J3]]]]; subst; auto.
     clear IHcs.
     exists (a::cs1). exists cs2.
     simpl. rewrite <- HeqR. rewrite J2. auto.
Qed.

Lemma cmds2sbs_cons_inv' : forall cs0 sb sbs' nbs,
  cmds2sbs cs0 = (sb::sbs', nbs) ->
  exists cs, exists cs',
    cmds2sbs cs = (sb::nil, nil) /\
    cmds2sbs cs' = (sbs', nbs) /\
    cs0 = cs++cs'.
Proof.
  induction cs0; intros.
    simpl in H. inversion H.

    simpl in H.
    remember (isCall_dec a) as R.
    remember (cmds2sbs cs0) as R'.
    destruct R.
      destruct R'.
        destruct l0.
          inversion H.

          destruct s. inversion H; subst. clear H.
          destruct (@IHcs0 (mkSB NBs0 call_cmd0 call_cmd_isCall0) sbs' nbs) as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
          exists (a::cs). exists cs'.
          split; auto.
            simpl.
            rewrite <- HeqR.
            rewrite J1. auto.

      destruct R'.
      inversion H; subst. clear H.
      destruct sbs'.
        symmetry in HeqR'.
        exists (a::nil). exists cs0.
        simpl. rewrite <- HeqR. auto.

        destruct (@IHcs0 s sbs' nbs) as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
        exists (a::nil). exists (cs++cs').
        simpl. rewrite <- HeqR. auto.
Qed.

  
Lemma cmds2nbs_app_inv : forall cs0 nbs1 nbs2,
  cmds2sbs cs0 = (nil, nbs1++nbs2) ->
  exists cs, exists cs',
    cmds2sbs cs = (nil, nbs1) /\
    cmds2sbs cs' = (nil, nbs2) /\
    cs0 = cs++cs'.
Proof.
  induction cs0; intros.
    simpl in H. inversion H.
    symmetry in H1.
    apply app_eq_nil in H1.
    destruct H1; subst.
    exists nil. exists nil. auto.

    simpl in H.
    remember (isCall_dec a) as R.
    remember (cmds2sbs cs0) as R'.
    destruct R.
      destruct R'.
        destruct l0.
          inversion H.
          apply cons_eq_app in H1.
          destruct H1 as [[qs [J1 J2]] | [J1 J2]]; subst.
            destruct (@IHcs0 qs nbs2) as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
            clear IHcs0.
            exists (a::cs). exists cs'.
            simpl. rewrite <- HeqR. rewrite J1. split; auto.

            exists nil. exists (a::cs0). 
            simpl. rewrite <- HeqR. rewrite <- HeqR'. split; auto.

          destruct s. inversion H; subst.

      destruct R'.
      inversion H; subst. 
Qed.

Lemma nbranchs2cmds_app : forall nbs1 nbs2,
  nbranchs2cmds (nbs1++nbs2) = nbranchs2cmds nbs1 ++ nbranchs2cmds nbs2.
Proof.
  induction nbs1; intros; auto.
    simpl. destruct a. rewrite IHnbs1. auto.
Qed.

Lemma cmds_cons2nbranchs_inv : forall c cs' nbs,
  cmds2nbranchs (c::cs') = Some nbs ->
  exists nb, exists nbs',
    cmd2nbranch c = Some nb /\
    cmds2nbranchs cs' = Some nbs' /\
    nbs = nb::nbs'.
Proof.
  intros.
  simpl in H.
  destruct (cmd2nbranch c); try solve [inversion H].
  destruct (cmds2nbranchs cs'); inversion H; subst.
  exists n. exists l0. auto.
Qed.

Lemma cmd2nbranch_Some_isCallInst : forall c nb,
  cmd2nbranch c = Some nb ->
  exists H, nb = mkNB c H.
Proof.
  intros.
  unfold cmd2nbranch in H.
  destruct nb.
  destruct (isCall_dec c); inversion H; subst.
    exists notcall0. auto. 
Qed.

(* wf *)
Lemma wf_nbranchs__decomposes__app : forall nbs1 nbs2,
  wf_nbranchs (nbs1++nbs2) ->
  wf_nbranchs nbs1 /\ wf_nbranchs nbs2.
Proof.
  intros.
  inversion H; subst.
  apply cmds2nbs_app_inv in H0.
  destruct H0 as [cs1 [cs2 [J1 [J2 J3]]]]; subst.
  rewrite getCmdsIDs_app in H1.
  apply NoDup_inv in H1.
  destruct H1.
  split; eapply wf_nbranchs_intro; eauto.
Qed.

Lemma wf_nbranchs__inv : forall nb nbs,
  wf_nbranchs (nb::nbs) ->
  wf_nbranchs nbs.
Proof.
  intros.
  simpl_env in H.
  apply wf_nbranchs__decomposes__app in H.
  destruct H; auto.
Qed.

Lemma wf_nbranchs_nil : wf_nbranchs nil.
Proof.
  apply wf_nbranchs_intro with (cs:=nil); simpl; auto using NoDup_nil.
Qed.

Hint Resolve wf_nbranchs_nil.

Lemma uniqCmds___wf_subblocks_wf_nbranchs : forall cs sbs nbs,
  NoDup (getCmdsIDs cs) ->
  cmds2sbs cs = (sbs, nbs) ->
  wf_subblocks sbs /\ wf_nbranchs nbs.
Proof.
  induction cs; intros.
    simpl in H0. inversion H0; subst.
    split; auto using wf_nbranchs_nil.

    simpl in *.
    remember (cmds2sbs cs) as R.
    destruct R as [sbs' nbs'].
    remember (isCall_dec a) as R'.
    destruct R'.
      destruct sbs'.
        inversion H0; subst. clear H0.
        split; auto.
          apply wf_nbranchs_intro with (cs:=a::cs); auto.
            simpl.
            rewrite <- HeqR'.
            rewrite <- HeqR. auto.

        destruct s. 
        inversion H0; subst. clear H0.
        inversion H; subst.
        apply IHcs with (nbs0:=nbs)(sbs:=mkSB NBs0 call_cmd0 call_cmd_isCall0::sbs') in H3; auto.
        destruct H3 as [H3 H4].
        split; auto.
          inversion H3; subst.
          apply wf_subblocks_cons; auto.
            apply wf_subblock_intro.

            symmetry in HeqR.
            apply cmds2sbs_cons_inv' in HeqR.
            destruct HeqR as [cs1 [cs2 [Hcs1NBs0call0 [Hcs2sbs EQ]]]]; subst.
            apply cmds2sb_inv in Hcs1NBs0call0.
            destruct Hcs1NBs0call0 as [cs1' [call0 [EQ [Hcs1'nbs EQ']]]]; subst.
            simpl in *.
            simpl_env in H.
            rewrite getCmdsIDs_app in H.
            rewrite ass_app in H.
            apply NoDup_inv in H. destruct H as [H _].
            apply wf_nbranchs_intro with (cs:=a::cs1'); auto.
              simpl.
              rewrite <- HeqR'.
              rewrite Hcs1'nbs. auto.

      inversion H0; subst. clear H0.
      simpl_env in H.
      apply NoDup_inv in H. destruct H as [H1 H2].
      apply IHcs with (sbs:=sbs')(nbs0:=nbs) in H2; auto.
      destruct H2.
      split; auto.
        apply wf_subblocks_cons; auto.
          apply wf_subblock_intro; auto.
Qed.

Lemma uniqBlock__wf_block : forall B,
  uniqBlocks [B] -> wf_block B.
Proof.
  intros B HuniqBlocks.
  unfold uniqBlocks in HuniqBlocks.
  simpl in HuniqBlocks. destruct B.
  destruct HuniqBlocks as [J1 J2].
  remember (cmds2sbs c) as R.
  destruct R as [sbs nbs].
  simpl in J2. simpl_env in J2.
  apply NoDup_inv in J2. destruct J2.
  apply NoDup_inv in H0. destruct H0.
  apply uniqCmds___wf_subblocks_wf_nbranchs with (sbs:=sbs)(nbs:=nbs) in H0; auto.
  destruct H0.
  apply wf_block_intro with (sbs:=sbs)(nbs:=nbs); auto.
Qed.

Lemma uniqBlocks__wf_block : forall lb n B,
  uniqBlocks lb ->
  nth_error lb n = Some B ->
  wf_block B.
Proof.
  induction lb; intros.
    apply nil_nth_error_Some__False in H0.
    inversion H0.

    apply nth_error_cons__inv in H0.
    simpl_env in H. 
    apply uniqBlocks_inv in H.
    destruct H as [J1 J2].
    destruct H0 as [EQ | [n' [EQ H0]]]; subst; eauto.
      apply uniqBlock__wf_block; auto.
Qed.

Lemma uniqFdef__wf_block : forall fh lb n B,
  uniqFdef (fdef_intro fh lb) ->
  nth_error lb n = Some B ->
  wf_block B.
Proof.
  intros.
  unfold uniqFdef in H.
  eapply uniqBlocks__wf_block; eauto.
Qed.

(* Properties of se *)

Lemma se_lib_uniq: forall id0 noret0 tailc0 rt fv lp st
  (nocall : isCall (insn_call id0 noret0 tailc0 rt fv lp) = false),
  uniq (STerms st) ->
  uniq (STerms (se_lib (insn_call id0 noret0 tailc0 rt fv lp) 
    id0 noret0 tailc0 rt fv lp st eq_refl nocall)).
Proof.
  intros.
  destruct fv; simpl.
    apply updateAddAL_uniq; auto.
    simpl in nocall. inversion nocall.
Qed.

Lemma se_cmd_uniq : forall smap0 sm0 sf0 se0 c,
  uniq smap0 ->
  uniq (STerms (se_cmd (mkSstate smap0 sm0 sf0 se0) c)).
Proof.
  intros smap0 sm0 sf0 se0 [c nocall] Huniq.
  destruct c; simpl; 
    try solve [
      apply updateAddAL_uniq; auto | 
      auto | 
      apply se_lib_uniq; auto].
Qed.

Lemma se_cmd_dom_mono : forall smap0 sm0 sf0 se0 c,
  dom smap0 [<=] dom (STerms (se_cmd (mkSstate smap0 sm0 sf0 se0) c)).
Proof.
  intros smap0 sm0 sf0 se0 [c nocall].
  assert (forall sm id0 st0, dom sm [<=] dom (updateAddAL sterm sm id0 st0)) as J.
    intros. assert (J:=@updateAddAL_dom_eq _ sm id0 st0). fsetdec. 
  destruct c; simpl; try solve [eauto using J| fsetdec].
    destruct v; simpl.
      eauto using J.
      simpl in nocall. inversion nocall.
Qed.

Lemma _se_cmd_uniq : forall c sstate0,
  uniq (STerms sstate0) ->
  uniq (STerms (se_cmd sstate0 c)).
Proof.
  intros [c nocall] sstate0 Huniq.
  destruct c; simpl; try solve [apply updateAddAL_uniq; auto | auto].
    destruct v; simpl.
      apply updateAddAL_uniq; auto.
      simpl in nocall. inversion nocall.
Qed.

Lemma _se_cmds_uniq : forall cs sstate0,
  uniq (STerms sstate0) ->
  uniq (STerms (se_cmds sstate0 cs)).
Proof.
  induction cs; intros; simpl; auto using _se_cmd_uniq.
Qed.

Lemma se_cmds_uniq : forall cs smap0 sm0 sf0 se0,
  uniq smap0 ->
  uniq (STerms (se_cmds (mkSstate smap0 sm0 sf0 se0) cs)).
Proof.
  intros.
  apply _se_cmds_uniq; auto. 
Qed.

Lemma se_cmds_init_uniq : forall cs,
  uniq (STerms (se_cmds sstate_init cs)).
Proof.
  unfold sstate_init. intro. auto using se_cmds_uniq.
Qed.

Lemma se_cmds_rev_cons : forall cs c sstate0,
  se_cmds sstate0 (cs++c::nil) = se_cmd (se_cmds sstate0 cs) c.
Proof.
  induction cs; intros; simpl; auto.
Qed.

Lemma se_cmds_app : forall cs cs' sstate0,
  se_cmds sstate0 (cs++cs') = se_cmds (se_cmds sstate0 cs) cs'.
Proof.
  induction cs; intros; simpl; auto.
Qed.

Lemma se_cmds_cons : forall cs c sstate0,
  se_cmds sstate0 ((c::nil)++cs) = se_cmds (se_cmd sstate0 c) cs.
Proof.
  induction cs; intros; simpl; auto.
Qed.

Lemma se_cmd_dom_upper : forall sstate0 c nc,
  dom (STerms (se_cmd sstate0 (mkNB c nc))) [<=] dom (STerms sstate0) `union` {{getCmdID c}}.
Proof.
  intros [smap0 sm0 sf0 se0] c nc.
  destruct c; simpl; try solve [rewrite updateAddAL_dom_eq; fsetdec | fsetdec].
    destruct v; simpl.
      rewrite updateAddAL_dom_eq; fsetdec. 
      inversion nc.
Qed.

Lemma se_cmd_dom_mono' : forall sstate0 c,
  dom (STerms sstate0) [<=] dom (STerms (se_cmd sstate0 c)).
Proof.
  intros [smap0 sm0 sf0 se0] c. 
  simpl.
  apply se_cmd_dom_mono; auto.
Qed.

Definition se_cmds_dom_mono_prop (cs:list nbranch) :=
  forall smap0 sm0 sf0 se0,
  dom smap0 [<=]
    dom (STerms (se_cmds (mkSstate smap0 sm0 sf0 se0) cs)).

Lemma se_cmds_dom_mono: forall cs, se_cmds_dom_mono_prop cs.
Proof.
  apply (@rev_ind nbranch); unfold se_cmds_dom_mono_prop; intros; simpl.
    fsetdec.

    rewrite se_cmds_rev_cons.
    assert (J:=@se_cmd_dom_mono' (se_cmds (mkSstate smap0 sm0 sf0 se0) l0) x).
    assert (J':=@H smap0 sm0 sf0 se0).
    fsetdec.
Qed.

Lemma se_cmds_dom_mono' : forall sstate0 cs,
  dom (STerms sstate0) [<=] dom (STerms (se_cmds sstate0 cs)).
Proof.
  intros [smap0 sm0 sf0 se0] cs. 
  simpl.
  apply se_cmds_dom_mono; auto.
Qed.

(* props of lookupSmap *)

Lemma lookupSmap_in : forall sm id0 st0,
  uniq sm ->
  binds id0 st0 sm ->
  lookupSmap sm id0 = st0.
Proof.
  induction sm; intros.
    inversion H0.

    destruct a.
    simpl in *.
    inversion H; subst.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst; simpl;
      analyze_binds_uniq H0; auto.
Qed.

Lemma id2Sterm_in : forall sm id0 st0,
  uniq sm ->
  binds id0 st0 sm ->
  value2Sterm sm (value_id id0) = st0.
Proof.
  intros. simpl. apply lookupSmap_in; auto.
Qed.

Lemma lookupSmap_notin : forall sm id0,
  uniq sm ->
  id0 `notin` dom sm ->
  lookupSmap sm id0 = sterm_val (value_id id0).
Proof.
  induction sm; intros; simpl; auto.
    destruct a.
    simpl in *.
    inversion H; subst.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst; simpl;
      analyze_binds_uniq H0; auto.
Qed.

Lemma id2Sterm_notin : forall sm id0,
  uniq sm ->
  id0 `notin` dom sm ->
  value2Sterm sm (value_id id0) = sterm_val (value_id id0).
Proof.
  intros. simpl. apply lookupSmap_notin; auto.
Qed.

Lemma const2Sterm : forall sm c,
  value2Sterm sm (value_const c) = sterm_val (value_const c).
Proof.
  intros. auto.
Qed.
       
Lemma lookupSmap_in_lookupAL : forall m id0,
  id0 `in` dom m ->
  lookupAL _ m id0 = Some (lookupSmap m id0).
Proof.
  induction m; intros id0 id0inm; simpl.
    contradict id0inm; auto.

    destruct a.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); subst; simpl; auto.
        contradict n; auto.
      assert (id0 = a \/ id0 `in` dom m) as id0in. simpl in id0inm. fsetdec.
      destruct id0in as [EQ | id0in]; subst.
        contradict n; auto.
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; auto.
          contradict n; auto.
Qed.

Lemma lookupSmap_updateAddAL_neq : forall m id0 id1 gv0,
  id1 <> id0 ->
  lookupSmap m id1 = lookupSmap (updateAddAL _ m id0 gv0) id1.
Proof.
  induction m; intros; simpl; auto.
    destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) id1 id0); subst; auto.
      contradict H; auto.

    destruct a.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); subst; simpl; auto.
        contradict H; auto.
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; simpl; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
            contradict H; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) a a); subst; simpl; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 a); subst; simpl; auto.
              contradict n; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 a); subst; simpl; auto.
Qed.   

Lemma lookupSmap_updateAddAL_eq : forall m id0 gv0,
  lookupSmap (updateAddAL _ m id0 gv0) id0 = gv0.
Proof.
  induction m; intros; simpl.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 id0); subst; simpl; auto.
      contradict n; auto.  

    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) a a); subst; simpl; auto.
        contradict n; auto.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst; simpl; auto.
        contradict n; auto.
Qed.

Lemma lookupSmap_se_cmd_neq : forall c id' smap1 smem1 sframe1 seffects1 nc,
  getCmdID c <> id' ->
  lookupSmap (STerms (se_cmd (mkSstate smap1 smem1 sframe1 seffects1) (mkNB c nc))) id' =
  lookupSmap smap1 id'.
Proof.
  destruct c; intros id' smap1 smem1 sframe1 seffects1 nc HnEQ; simpl;
    try solve [rewrite <- lookupSmap_updateAddAL_neq; auto | auto].
    destruct v; simpl.
      rewrite <- lookupSmap_updateAddAL_neq; auto.
      inversion nc.
Qed.

Lemma init_denotes_id : forall TD lc gl als Mem0,
  sstate_denotes_state TD lc gl als Mem0 sstate_init lc als Mem0 trace_nil.
Proof.
  intros TD lc gl als Mem0.
  split; auto.
    split; intros; simpl in *; auto.
      assert (id' `in` dom lc) as id'_in_lc. fsetdec.
      apply indom_lookupAL_Some in id'_in_lc.
      destruct id'_in_lc as [gv' id'_gv'_in_lc].
      exists gv'. split; auto.
Qed.

(* props of denotes *)

Lemma id_denotes_gv : forall id0 TD Mem0 gl lc,
  id0 `in` dom lc ->
  exists gv0,
    sterm_denotes_genericvalue TD lc gl Mem0 (sterm_val (value_id id0)) gv0 /\
    lookupAL _ lc id0 = Some gv0.
Proof.
  intros id0 TD Mem0 gl lc Hin.
  apply indom_lookupAL_Some in Hin.
  destruct Hin as [gv0 Hin].
  exists gv0. split; auto.
Qed.

Lemma init_denotes_gvmap :forall TD lc gl Mem0,
  uniq lc ->
  smap_denotes_gvmap TD lc gl Mem0 nil lc.
Proof.
  intros TD lc gl Mem0 Uniqc.
  unfold smap_denotes_gvmap.
  split; intros; simpl; auto.
    apply id_denotes_gv; auto. 
      fsetdec.
Qed.

(* The denotational rules are determinastic. *)

Definition sterm_denotes_genericvalue_det_prop TD lc gl Mem0 st0 gv1 
  (sd:sterm_denotes_genericvalue TD lc gl Mem0 st0 gv1) :=
  forall gv2,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv2 ->
  gv1 = gv2.

Definition sterms_denote_genericvalues_det_prop TD lc gl Mem0 sts0 gvs1
  (ds:sterms_denote_genericvalues TD lc gl Mem0 sts0 gvs1) :=
  forall gvs2,
  sterms_denote_genericvalues TD lc gl Mem0 sts0 gvs2 ->
  gvs1 = gvs2.

Definition smem_denotes_mem_det_prop TD lc gl Mem0 st0 Mem1
  (sd:smem_denotes_mem TD lc gl Mem0 st0 Mem1) :=
  forall Mem2,
  smem_denotes_mem TD lc gl Mem0 st0 Mem2 ->
  Mem1 = Mem2.

Lemma sdenotes_det : 
  (forall TD lc gl Mem0 st0 gv1 sd, @sterm_denotes_genericvalue_det_prop TD lc gl Mem0 st0 gv1 sd) /\
  (forall TD lc gl Mem0 sts0 gvs1 sd, @sterms_denote_genericvalues_det_prop TD lc gl Mem0 sts0 gvs1 sd) /\
  (forall TD lc gl Mem0 st0 Mem1 sd, @smem_denotes_mem_det_prop TD lc gl Mem0 st0 Mem1 sd).
Proof.
(sd_mutind_cases
  apply sd_mutind with
    (P  := sterm_denotes_genericvalue_det_prop)
    (P0 := sterms_denote_genericvalues_det_prop)
    (P1 := smem_denotes_mem_det_prop) Case);
  unfold sterm_denotes_genericvalue_det_prop, 
         sterms_denote_genericvalues_det_prop, 
         smem_denotes_mem_det_prop; intros.
Case "sterm_val_denotes".
  inversion H; subst.
  rewrite e in H5. inversion H5; auto.
Case "sterm_bop_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e.
  inversion e; auto.
Case "sterm_fbop_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e.
  inversion e; auto.
Case "sterm_extractvalue_denotes".
  inversion H0; subst.
  apply H in H9; subst.
  rewrite H10 in e.
  inversion e; auto.
Case "sterm_insertvalue_denotes".
  inversion H1; subst.
  apply H in H12; subst.
  apply H0 in H13; subst.
  rewrite H14 in e.
  inversion e; auto.
Case "sterm_malloc_denotes".
  inversion H1; subst.
  rewrite e in H12. inversion H12; subst.
  apply H in H10; subst.
  apply H0 in H13; subst.
  rewrite H14 in e0. inversion e0; auto.
Case "sterm_alloca_denotes".
  inversion H1; subst.
  rewrite e in H12. inversion H12; subst.
  apply H in H10; subst.
  apply H0 in H13; subst.
  rewrite H14 in e0. inversion e0; auto.
Case "sterm_load_denotes".
  inversion H1; subst.
  apply H0 in H12; subst.
  apply H in H11; subst.
  rewrite e in H13. inversion H13; auto.
Case "sterm_gep_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e. inversion e; auto.
Case "sterm_trunc_denotes".
  inversion H0; subst.
  apply H in H10; subst.
  rewrite H11 in e.
  inversion e; auto.
Case "sterm_ext_denotes".
  inversion H0; subst.
  apply H in H10; subst.
  rewrite H11 in e.
  inversion e; auto.
Case "sterm_cast_denotes".
  inversion H0; subst.
  apply H in H10; subst.
  rewrite H11 in e.
  inversion e; auto.
Case "sterm_icmp_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e. inversion e; auto.
Case "sterm_fcmp_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e. inversion e; auto.
Case "sterm_select_denotes".
  inversion H2; subst.
  apply H in H11; subst.
  apply H0 in H13; subst.
  apply H1 in H14; subst; auto.
Case "sterm_lib_denotes".
  inversion H1; subst.
  apply H in H9; subst.  
  apply H0 in H11; subst.
  rewrite H12 in e.
  injection e; auto.
Case "sterms_nil_denote".
  inversion H; auto.
Case "sterms_cons_denote".
  inversion H1; subst.
  apply H in H8; subst.
  apply H0 in H10; subst; auto.
Case "smem_init_denotes".
  inversion H; auto.
Case "smem_malloc_denotes".
  inversion H1; subst.
  apply H in H10; subst. 
  apply H0 in H13; subst. 
  rewrite H12 in e. inversion e; subst.
  rewrite H14 in e0. inversion e0; auto.
Case "smem_free_denotes".
  inversion H1; subst.
  apply H in H9; subst. 
  apply H0 in H11; subst. 
  rewrite H12 in e. inversion e; auto.
Case "smem_alloca_denotes".
  inversion H1; subst.
  apply H in H10; subst. 
  apply H0 in H13; subst. 
  rewrite H12 in e. inversion e; subst.
  rewrite H14 in e0. inversion e0; auto.
Case "smem_load_denotes".
  inversion H0; subst.
  apply H in H10; auto. 
Case "smem_store_denotes".
  inversion H2; subst.
  apply H in H13; subst. 
  apply H0 in H14; subst. 
  apply H1 in H15; subst. 
  rewrite H16 in e. inversion e; auto.
Case "smem_lib_denotes".
  inversion H1; subst.
  apply H in H9; subst.  
  apply H0 in H11; subst.
  rewrite H12 in e.
  injection e; auto.  
Qed.

Lemma sterm_denotes_genericvalue_det : forall TD lc gl Mem0 st0 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv2 ->
  gv1 = gv2.
Proof.
  destruct sdenotes_det as [J _].
  unfold sterm_denotes_genericvalue_det_prop in J.
  eauto.
Qed.

Lemma sterms_denote_genericvalues_det : forall TD lc gl Mem0 sts0 gvs1 gvs2,
  sterms_denote_genericvalues TD lc gl Mem0 sts0 gvs1 ->
  sterms_denote_genericvalues TD lc gl Mem0 sts0 gvs2 ->
  gvs1 = gvs2.
Proof.
  destruct sdenotes_det as [_ [J _]].
  unfold sterms_denote_genericvalues_det_prop in J.
  eauto.
Qed.

Lemma smem_denotes_mem_det : forall TD lc gl Mem0 st0 Mem1 Mem2,
  smem_denotes_mem TD lc gl Mem0 st0 Mem1 ->
  smem_denotes_mem TD lc gl Mem0 st0 Mem2 ->
  Mem1 = Mem2.
Proof.
  destruct sdenotes_det as [_ [_ J]].
  unfold smem_denotes_mem_det_prop in J.
  eauto.
Qed.

Lemma sframe_denotes_frame_det : forall TD lc gl als Mem0 st0 als1 als2,
  sframe_denotes_frame TD lc gl als Mem0 st0 als1 ->
  sframe_denotes_frame TD lc gl als Mem0 st0 als2 ->
  als1 = als2.
Proof.
  intros.
  generalize dependent als2.
  induction H; intros.
    inversion H0; auto.

    inversion H4; subst.
    apply smem_denotes_mem_det with (Mem1:=Mem4) in H; auto; subst.
    apply sterm_denotes_genericvalue_det with (gv1:=gv1) in H2; auto; subst.
    rewrite H1 in H18. inversion H18; subst.
    rewrite H20 in H3. inversion H3; subst.
    apply IHsframe_denotes_frame in H17; subst; auto.
Qed.

Lemma seffects_denote_trace_det : forall ses tr1 tr2,
  seffects_denote_trace ses tr1 ->
  seffects_denote_trace ses tr2 ->
  tr1 = tr2.
Proof.
  intros. 
  inversion H; subst.
  inversion H0; subst; auto.
Qed.

Lemma lookupSmap_inv : forall m id0 st0,
  lookupSmap m id0 = st0 ->
  (id0 `in` dom m /\ binds id0 st0 m) \/ 
  (id0 `notin` dom m /\ st0 = sterm_val (value_id id0)).
Proof.
  induction m; intros id0 st0 HlkSmap; simpl in *.
    right. auto.

    destruct a.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst.
      left. auto.

      remember (lookupSmap m id0) as st0.
      symmetry in Heqst0.
      apply IHm in Heqst0.
      destruct Heqst0 as [[id0in binds_id0_st0] | [id0notin EQ]]; subst; auto.
Qed.


Lemma sterm_val_denotes_in : forall TD lc gl Mem0 id0 gv,
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_val (value_id id0)) gv ->
  id0 `in` dom lc.
Proof.
  intros TD lc gl Mem0 id0 gv Hdenotes.
  inversion Hdenotes; subst.
  simpl in H4.
  apply lookupAL_Some_indom in H4; auto.
Qed.

Lemma smap_denotes_gvmap_det : forall TD lc gl Mem0 smap0 lc1 lc2,
  uniq smap0 ->
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc1 ->
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc2 ->
  eqAL _ lc1 lc2.
Proof.
  intros TD lc gl Mem0 smap0 lc1 lc2 Uniq J1 J2.
  destruct J1 as [J11 J12].
  destruct J2 as [J21 J22].
  intros id0.
  remember (lookupAL _ lc1 id0) as ogv1.
  remember (lookupAL _ lc2 id0) as ogv2.
  destruct ogv1 as [gv1 | ].
    symmetry in Heqogv1.
    apply J12 in Heqogv1.
    destruct (@AtomSetProperties.In_dec id0 (dom smap0)) as [id0_in_smap0 | id0_notin_smap0].
      assert (id0 `in` dom smap0 `union` dom lc) as id0_in_smap0_lc. auto.
      apply J21 in id0_in_smap0_lc.
      destruct id0_in_smap0_lc as [gv' [id0_denotes_gv' id0_in_lc2]].
      rewrite id0_in_lc2 in Heqogv2. inversion Heqogv2; subst.
      apply sterm_denotes_genericvalue_det with (gv2:=gv1) in id0_denotes_gv'; auto.
      subst. auto.
      
      apply lookupSmap_notin in id0_notin_smap0; auto.
      rewrite id0_notin_smap0 in Heqogv1.
      assert (id0_in_lc:=@sterm_val_denotes_in TD lc gl Mem0 id0 gv1 Heqogv1).
      assert (id0 `in` dom smap0 `union` dom lc) as id0_in_smap0_lc. auto.
      apply J21 in id0_in_smap0_lc.
      destruct id0_in_smap0_lc as [gv' [id0_denotes_gv' id0_in_lc2]].
      rewrite id0_in_lc2 in Heqogv2. inversion Heqogv2; subst.
      rewrite id0_notin_smap0 in id0_denotes_gv'.
      apply sterm_denotes_genericvalue_det with (gv2:=gv1) in id0_denotes_gv'; auto.
      subst. auto.
    
  destruct ogv2 as [gv2 | ]; auto.
    symmetry in Heqogv2.
    apply J22 in Heqogv2.
    destruct (@AtomSetProperties.In_dec id0 (dom smap0)) as [id0_in_smap0 | id0_notin_smap0].
      assert (id0 `in` dom smap0 `union` dom lc) as id0_in_smap0_lc. auto.   
      apply J11 in id0_in_smap0_lc.
      destruct id0_in_smap0_lc as [gv' [id0_denotes_gv' id0_in_lc1]].
      rewrite id0_in_lc1 in Heqogv1.
      inversion Heqogv1.

      apply lookupSmap_notin in id0_notin_smap0; auto.
      rewrite id0_notin_smap0 in Heqogv2.
      assert (id0_in_lc:=@sterm_val_denotes_in TD lc gl Mem0 id0 gv2 Heqogv2).
      assert (id0 `in` dom smap0 `union` dom lc) as id0_in_smap0_lc. auto.
      apply J11 in id0_in_smap0_lc.
      destruct id0_in_smap0_lc as [gv' [id0_denotes_gv' id0_in_lc1]].
      rewrite id0_in_lc1 in Heqogv1. inversion Heqogv1; subst.
Qed.

Lemma sstate_denotes_state_det : forall TD lc gl als Mem0 sstate0 lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2,
  uniq (STerms sstate0) ->
  sstate_denotes_state TD lc gl als Mem0 sstate0 lc1 als1 Mem1 tr1 ->
  sstate_denotes_state TD lc gl als Mem0 sstate0 lc2 als2 Mem2 tr2 ->
  eqAL _ lc1 lc2 /\ als1 = als2 /\ Mem1 = Mem2 /\ tr1 = tr2.
Proof.
  intros TD lc gl als Mem0 sstate0 lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 Uniq J1 J2.
  destruct J1 as [J11 [J12 [J13 J14]]].
  destruct J2 as [J21 [J22 [J23 J24]]].
  apply smem_denotes_mem_det with (Mem2:=Mem2) in J12; auto; subst.
  apply sframe_denotes_frame_det with (als2:=als2) in J13; auto; subst.
  apply seffects_denote_trace_det with (tr2:=tr2) in J14; auto; subst.
  apply smap_denotes_gvmap_det with (lc2:=lc2) in J11; auto.
Qed.

Lemma smap_denotes_gvmap_eqEnv : forall TD lc gl Mem0 smap0 lc1 lc2,
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc1 ->
  eqAL _ lc1 lc2 ->
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc2.
Proof.
  intros TD lc gl Mem0 smap0 lc1 lc2 [H1 H2] H3.
  split; intros.
    apply H1 in H.
    destruct H as [gv' [st'_denotes_gv' id'_gv'_is_env1]].
    exists gv'. rewrite <- H3.
    split; auto.

    rewrite <- H3 in H.
    apply H2 in H; auto.
Qed.

(* p&p *)
Lemma exCallUpdateLocals_uniq : forall noret0 rid rt oresult lc,
  uniq lc ->
  uniq (exCallUpdateLocals noret0 rid rt oresult lc).
Proof.
  intros.
  unfold exCallUpdateLocals.
  destruct noret0; auto.
  destruct (rt=t=typ_void); auto.
  destruct oresult; auto.
  apply updateAddAL_uniq; auto.
Qed.

Lemma se_dbCmd_preservation : forall TD lc als gl Mem0 c lc' als' Mem' tr,
  dbCmd TD gl lc als Mem0 c lc' als' Mem' tr ->
  uniq lc ->
  uniq lc'.
Proof.
  intros TD lc als gl Mem0 c lc' als' Mem' tr HdbCmd Uniqlc.
  (dbCmd_cases (inversion HdbCmd) Case); subst; auto using updateAddAL_uniq.
  Case "dbSelect".
    destruct (isGVZero TD cond0); eauto using updateAddAL_uniq.
  Case "dbLib".
    apply exCallUpdateLocals_uniq; auto.      
Qed.

Lemma se_dbCmds_preservation : forall TD lc als gl Mem0 cs lc' als' Mem' tr,
  dbCmds TD gl lc als Mem0 cs lc' als' Mem' tr ->
  uniq lc ->
  uniq lc'.
Proof.
  intros TD lc als gl Mem0 cs lc' als' Mem' tr HdbCmd Uniqlc.
  induction HdbCmd; auto. 
    apply se_dbCmd_preservation in H; auto.
Qed.

Lemma se_dbTerminator_preservation : forall TD F B gl lc c B' lc' tr,
  dbTerminator TD F gl B lc c B' lc' tr ->
  uniq lc ->
  uniqFdef F ->
  blockInFdefB B F ->
  uniq lc' /\ blockInFdefB B' F.
Proof.
  intros TD F gl B lc c B' lc' tr HdbTerminator Uniqlc UniqF Hblockin.
  inversion HdbTerminator; subst.
    destruct (isGVZero TD c0).
      split; auto using switchToNewBasicBlock_uniq.
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; auto.
        destruct H0; auto.

      split; auto using switchToNewBasicBlock_uniq.
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; auto.
        destruct H0; auto.

    symmetry in H.
    apply lookupBlockViaLabelFromFdef_inv in H; auto.
    destruct H.
    split; auto using switchToNewBasicBlock_uniq.
Qed.

Definition se_dbCall_preservation_prop S TD Ps fs gl lc Mem0 call0 lc' Mem' tr
  (db:dbCall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr) :=
  forall los nts,
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  TD = (los, nts) ->
  uniq lc' .
Definition se_dbSubblock_preservation_prop S TD Ps fs gl lc als Mem cs lc' als' Mem' tr
  (db:dbSubblock S TD Ps fs gl lc als Mem cs lc' als' Mem' tr) :=
  forall los nts,
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  TD = (los, nts) ->
  uniq lc'.
Definition se_dbSubblocks_preservation_prop S TD Ps fs gl lc als Mem cs lc' als' Mem' tr
  (db:dbSubblocks S TD Ps fs gl lc als Mem cs lc' als' Mem' tr) :=
  forall los nts,
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  TD = (los, nts) ->
  uniq lc'.
Definition se_dbBlock_preservation_prop S TD Ps fs gl F arg state1 state2 tr
  (db:dbBlock S TD Ps fs gl F arg state1 state2 tr) :=
  forall B1 lc als Mem B1' lc' als' Mem' los nts,
  state1 = mkState (mkEC B1 lc als) Mem ->
  state2 = mkState (mkEC B1' lc' als') Mem' ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro los nts Ps) F ->
  TD = (los, nts) ->
  uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro los nts Ps) F.
Definition se_dbBlocks_preservation_prop S TD Ps fs gl F lp state1 state2 tr
  (db:dbBlocks S TD Ps fs gl F lp state1 state2 tr) :=
  forall B1 lc als Mem B1' lc' als' Mem' los nts,
  state1 = (mkState (mkEC B1 lc als) Mem) ->
  state2 = (mkState (mkEC B1' lc' als') Mem') ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro los nts Ps) F ->
  TD = (los, nts) ->
  uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro los nts Ps) F.
Definition se_dbFdef_preservation_prop fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr
  (db:dbFdef fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr) :=
  forall fid la lb los nts,
  lookupFdefViaGV TD Ps gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  TD = (los, nts) ->
  uniq lc' /\ 
  blockInSystemModuleFdef B' S (module_intro los nts Ps) (fdef_intro (fheader_intro rt fid la) lb).

Lemma se_db_preservation :
  (forall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db, 
     se_dbCall_preservation_prop S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db,
     se_dbSubblock_preservation_prop S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db,
     se_dbSubblocks_preservation_prop S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl F arg state1 state2 tr db,
     se_dbBlock_preservation_prop S TD Ps fs gl F arg state1 state2 tr db) /\
  (forall S TD Ps fs gl F lp state1 state2 tr db,
     se_dbBlocks_preservation_prop S TD Ps fs gl F lp state1 state2 tr db) /\
  (forall fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db,
     se_dbFdef_preservation_prop fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db).
Proof.
(db_mutind_cases
  apply db_mutind with
    (P  := se_dbCall_preservation_prop)
    (P0 := se_dbSubblock_preservation_prop)
    (P1 := se_dbSubblocks_preservation_prop)
    (P2 := se_dbBlock_preservation_prop)
    (P3 := se_dbBlocks_preservation_prop)
    (P4 := se_dbFdef_preservation_prop) Case);
  unfold se_dbCall_preservation_prop, 
         se_dbSubblock_preservation_prop, se_dbSubblocks_preservation_prop,
         se_dbBlock_preservation_prop, se_dbBlocks_preservation_prop,
         se_dbFdef_preservation_prop; intros; subst; eauto.
Case "dbCall_internal".
  inversion d; subst.
    eapply H in H3; eauto. clear H.
    destruct H3 as [Huniqlc' Hblockin].
    unfold callUpdateLocals.
    destruct noret0; auto.
      destruct (rt=t=typ_void); auto.
        destruct (getOperandValue (los, nts) Result lc' gl); auto.
          apply updateAddAL_uniq; auto.

    eapply H in H3; eauto. clear H.
    destruct H3 as [Huniqlc' Hblockin].
    unfold callUpdateLocals.
    destruct noret0; auto.
      destruct (rt=t=typ_void); auto.

Case "dbCall_external".
  apply exCallUpdateLocals_uniq; auto.      

Case "dbSubblock_intro".
  apply se_dbCmds_preservation in d; eauto.
 
Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  apply blockInSystemModuleFdef_inv in H4.
  destruct H4 as [Hblockin [Hinproducts [Hmodulein Hproductin]]].
  eapply H in H2; eauto.
  apply se_dbCmds_preservation in d0; auto.
  assert (uniqFdef F) as uniqF.
    apply uniqSystem__uniqFdef in Hproductin; auto.
  apply se_dbTerminator_preservation in d1; auto.
  destruct d1 as [uniqc' B1inF].
  split; auto using blockInSystemModuleFdef_intro.

Case "dbBlocks_nil".
  inversion H0; subst. clear H0.
  split; auto.
 
Case "dbBlocks_cons".
  inversion d; subst.
  assert (J:=H4).
  eapply H with (B1:=block_intro l0 ps (cs++cs') tmn)(lc0:=lc)(als0:=als)(Mem:=Mem0) 
               (B1':=B')(lc':=lc4)(als':=als3)(Mem':=Mem3) in J; eauto.
  clear H.
  destruct J as [uniqc4 B'in].
  eapply H0; eauto.

Case "dbFdef_func".
  rewrite e in H1. inversion H1; subst. clear H1.
  apply entryBlockInSystemBlockFdef' with (los:=los)(nts:=nts)(Ps:=Ps)(S:=S)(fv:=fv)(gl:=gl)(lc:=lc)(fs:=fs) in e0; auto.
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(lc0:=initLocals la0 (params2GVs (los, nts) lp lc gl))(als:=nil)(Mem:=Mem0)
               (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result))(lc':=lc1)(als':=als1)(Mem':=Mem1) in e0; auto using initLocals_uniq.
  clear H. destruct e0 as [uniqc1 Bin].
  eapply H0 in uniqc1; eauto. clear H0.
  apply se_dbCmds_preservation in d1; auto.

Case "dbFdef_proc".
  rewrite e in H1. inversion H1; subst. clear H1.
  apply entryBlockInSystemBlockFdef' with (los:=los)(nts:=nts)(Ps:=Ps)(S:=S)(fv:=fv)(gl:=gl)(lc:=lc)(fs:=fs) in e0; auto.
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(lc0:=initLocals la0 (params2GVs (los, nts) lp lc gl))(als:=nil)(Mem:=Mem0)
               (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return_void rid))(lc':=lc1)(als':=als1)(Mem':=Mem1) in e0; auto using initLocals_uniq.
  clear H. destruct e0 as [uniqc1 Bin].
  eapply H0 in uniqc1; eauto. clear H0.
  apply se_dbCmds_preservation in d1; auto.
Qed.

Lemma se_dbCall_preservation : forall S los nts Ps fs lc gl Mem0 call0 lc' Mem' tr,
  dbCall S (los, nts) Ps fs gl lc Mem0 call0 lc' Mem' tr ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  uniq lc' .
Proof.
  intros.
  destruct se_db_preservation as [J _].
  unfold se_dbCall_preservation_prop in J. eauto.
Qed.

Lemma se_dbSubblock_preservation : forall S los nts Ps fs gl lc als Mem cs lc' als' Mem' tr,
  dbSubblock S (los, nts) Ps fs gl lc als Mem cs lc' als' Mem' tr ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  uniq lc'.
Proof.
  intros.
  destruct se_db_preservation as [_ [J _]].
  unfold se_dbSubblock_preservation_prop in J. eauto.
Qed.

Lemma se_dbSubblocks_preservation : forall S los nts Ps fs gl lc als Mem cs lc' als' Mem' tr,
  dbSubblocks S (los, nts) Ps fs gl lc als Mem cs lc' als' Mem' tr ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  uniq lc'.
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [J _]]].
  unfold se_dbSubblocks_preservation_prop in J. eauto.
Qed.

Lemma se_dbBlock_preservation : forall S los nts Ps fs gl F arg tr B1 lc als Mem B1' lc' als' Mem',
  dbBlock S (los, nts)  Ps fs gl F arg 
    (mkState (mkEC B1 lc als) Mem) 
    (mkState (mkEC B1' lc' als') Mem') tr ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro los nts Ps) F ->
  uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro los nts Ps) F.
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [_ [J _]]]].
  unfold se_dbBlock_preservation_prop in J. eauto.
Qed.

Lemma se_dbBlocks_preservation : forall S los nts Ps fs gl F lp tr B1 lc als Mem B1' lc' als' Mem',
  dbBlocks S (los, nts) Ps fs gl F lp 
    (mkState (mkEC B1 lc als) Mem)
    (mkState (mkEC B1' lc' als') Mem') tr ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro los nts Ps) F ->
  uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro los nts Ps) F.
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [_ [_ [J _]]]]].
  unfold se_dbBlocks_preservation_prop in J. eauto.
Qed.

Lemma se_dbFdef_preservation : forall fv rt lp S los nts Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr fid la lb,
  dbFdef fv rt lp S (los, nts) Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ->
  lookupFdefViaGV (los, nts) Ps gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  uniq lc' /\ 
  blockInSystemModuleFdef B' S (module_intro los nts Ps) (fdef_intro (fheader_intro rt fid la) lb).
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [_ [_ [_ J]]]]].
  unfold se_dbFdef_preservation_prop in J. eauto.
Qed.

(* eqEnv *)
Lemma dbCmd_eqEnv : forall TD c lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1',
  dbCmd TD gl lc1 als1 Mem1 c lc2 als2 Mem2 tr ->
  eqAL _ lc1 lc1' ->
  exists lc2', 
    dbCmd TD gl lc1' als1 Mem1 c lc2' als2 Mem2 tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros TD c lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1' HdbCmd HeqEnv.
  (dbCmd_cases (inversion HdbCmd) Case); subst.
Case "dbBop".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  rewrite BOP_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbFBop".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  rewrite FBOP_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbExtractValue".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv').
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  split; eauto using eqAL_updateAddAL.
  
Case "dbInsertValue".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv'').
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H0; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbMalloc".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 (blk2GV TD mb)).
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H0; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbFree".
  exists lc1'.
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  split; eauto.

Case "dbAlloca".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 (blk2GV TD mb)).
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H0; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbLoad".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv).
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbStore".
  exists lc1'.
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H0; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbGEP".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 mp').
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  rewrite values2GVs_eqAL with (lc2:=lc1') in H0; auto. 
(* rewrite GEP_eqAL with (lc2:=lc1') in H0; auto. *)
  split; eauto using eqAL_updateAddAL.

Case "dbTrunc".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  rewrite TRUNC_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbExt".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  rewrite EXT_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbCast".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  rewrite CAST_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbIcmp".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  rewrite ICMP_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbFcmp".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  rewrite FCMP_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbSelect".
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H0; auto. 
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H1; auto. 
  assert (HupdateEnv:=HeqEnv).
  exists (if isGVZero TD cond0 then updateAddAL _ lc1' id0 gv2 else updateAddAL _ lc1' id0 gv1).
  split; auto.
    destruct (isGVZero TD cond0); auto using eqAL_updateAddAL.

Case "dbLib".
  admit.
Qed.

Lemma dbCmds_eqEnv : forall TD cs lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1',
  dbCmds TD gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr ->
  eqAL _ lc1 lc1' ->
  exists lc2', 
    dbCmds TD gl lc1' als1 Mem1 cs lc2' als2 Mem2 tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros TD cs lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1' HdbCmds HeqEnv.
  generalize dependent lc1'.
  induction HdbCmds; intros.
    exists lc1'. split; auto.

    apply dbCmd_eqEnv with (lc1':=lc1') in H; auto.
    destruct H as [lc2' [HdbCmd HeqEnv']].
    apply IHHdbCmds in HeqEnv'; auto.
    destruct HeqEnv' as [lc3' [HdbCmds' HeqEnv'']].
    exists lc3'.
    split; eauto.
Qed.

Lemma dbTerminator_eqEnv : forall TD F gl lc1 tmn lc2 tr lc1' B B',
  dbTerminator TD F gl B lc1 tmn B' lc2 tr ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbTerminator TD F gl B lc1' tmn B' lc2' tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros TD F gl lc1 tmn lc2 tr lc1' B B' HdbTerminator HeqAL.
  inversion HdbTerminator; subst.
    exists (switchToNewBasicBlock TD (block_intro l' ps' sbs' tmn') B gl lc1').
    split.
      apply dbBranch with (c:=c); auto.
        erewrite <- getOperandValue_eqAL; eauto.
      apply eqAL_switchToNewBasicBlock; auto.     
  
    exists (switchToNewBasicBlock TD (block_intro l' ps' sbs' tmn') B gl lc1').
    split.
      apply dbBranch_uncond; auto.
      apply eqAL_switchToNewBasicBlock; auto.
Qed.     

Definition dbCall_eqEnv_prop S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr
  (db:dbCall S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr) := 
  forall lc1',
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbCall S TD Ps fs gl lc1' Mem0 call0 lc2' Mem' tr /\
    eqAL _ lc2 lc2'.
Definition dbSubblock_eqEnv_prop S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr
  (db:dbSubblock S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr) :=
  forall lc1',
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbSubblock S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    eqAL _ lc2 lc2'.
Definition dbSubblocks_eqEnv_prop S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr
  (db:dbSubblocks S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr) :=
  forall lc1',
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbSubblocks S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    eqAL _ lc2 lc2'.
Definition dbBlock_eqEnv_prop S TD Ps fs gl F arg state1 state2 tr
  (db:dbBlock S TD Ps fs gl F arg state1 state2 tr) :=
  forall B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  state1 = mkState (mkEC B1 lc1 als) Mem ->
  state2 = mkState (mkEC B1' lc2 als') Mem' ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbBlock S TD Ps fs gl F arg 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    eqAL _ lc2 lc2'.
Definition dbBlocks_eqEnv_prop S TD Ps fs gl F lp state1 state2 tr
  (db:dbBlocks S TD Ps fs gl F lp state1 state2 tr) :=
  forall B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  state1 = mkState (mkEC B1 lc1 als) Mem ->
  state2 = mkState (mkEC B1' lc2 als') Mem' ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbBlocks S TD Ps fs gl F lp 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    eqAL _ lc2 lc2'.
Definition dbFdef_eqEnv_prop fv rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr
  (db:dbFdef fv rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr) :=
  forall fid la lb lc1',
  lookupFdefViaGV TD Ps gl lc1 fs fv = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbFdef fv rt lp S TD Ps lc1' gl fs Mem lc2' als' Mem' B' Rid oResult tr /\
    eqAL _ lc2 lc2'.

Lemma db_eqEnv :
  (forall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db, 
     dbCall_eqEnv_prop S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db,
     dbSubblock_eqEnv_prop S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db,
     dbSubblocks_eqEnv_prop S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl F arg state1 state2 tr db,
     dbBlock_eqEnv_prop S TD Ps fs gl F arg state1 state2 tr db) /\
  (forall S TD Ps fs gl F lp state1 state2 tr db,
     dbBlocks_eqEnv_prop S TD Ps fs gl F lp state1 state2 tr db) /\
  (forall fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db,
     dbFdef_eqEnv_prop fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db).
Proof.
(db_mutind_cases
  apply db_mutind with
    (P  := dbCall_eqEnv_prop)
    (P0 := dbSubblock_eqEnv_prop)
    (P1 := dbSubblocks_eqEnv_prop)
    (P2 := dbBlock_eqEnv_prop)
    (P3 := dbBlocks_eqEnv_prop)
    (P4 := dbFdef_eqEnv_prop) Case);
  unfold dbCall_eqEnv_prop, 
         dbSubblock_eqEnv_prop, dbSubblocks_eqEnv_prop,
         dbBlock_eqEnv_prop, dbBlocks_eqEnv_prop,
         dbFdef_eqEnv_prop; intros; subst; auto.
Case "dbCall_internal".
  inversion d; subst.
    apply H with (lc1':=lc1') in H1; auto. clear H.
    destruct H1 as [lc2' [HdbBlocks HeqEnv]].
    exists (callUpdateLocals TD noret0 rid rt (Some Result) lc1' lc2' gl).
    split; eauto using dbCall_internal, eqAL_callUpdateLocals.

    apply H with (lc1':=lc1') in H1; auto. clear H.
    destruct H1 as [lc2' [HdbBlocks HeqEnv]].
    exists (callUpdateLocals TD noret0 rid rt None lc1' lc2' gl).
    split; eauto using dbCall_internal, eqAL_callUpdateLocals.

Case "dbCall_external".
  exists (exCallUpdateLocals noret0 rid rt oresult lc1').
  split; eauto using eqAL_exCallUpdateLocals.
    eapply dbCall_external; eauto.
      erewrite eqAL_lookupExFdecViaGV; eauto using eqAL_sym.

    rewrite <- eqAL_params2GVs with (lc:=lc); auto.

Case "dbSubblock_intro".
  apply dbCmds_eqEnv with (lc1':=lc1') in d; auto.
  destruct d as [lc2' [HdbCmds HeqEnv2]].
  apply H in HeqEnv2. clear H.
  destruct HeqEnv2 as [lc3' [HdbCall HeqEnv3]].
  exists lc3'.
  split; eauto.

Case "dbSubblocks_nil".
  exists lc1'. split; auto.
 
Case "dbSubblocks_cons".
  apply H in H1. clear H.
  destruct H1 as [lc2' [HdbSubblock Heq2]].
  apply H0 in Heq2. clear H0.
  destruct Heq2 as [lc3' [HdbSubblocks Heq3]].
  exists lc3'. split; eauto.

Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  apply H in H2. clear H.
  destruct H2 as [lc2' [HdbSubblocks Heq2]].
  apply dbCmds_eqEnv with (lc1':=lc2') in d0; auto.
  destruct d0 as [lc3' [HdbCmds Heq3]].
  apply dbTerminator_eqEnv with (lc1':=lc3') in d1; auto.
  destruct d1 as [lc5' [HdbTerminator Heq5]].
  exists lc5'. split; eauto.

Case "dbBlocks_nil".
  inversion H0; subst. clear H0.
  exists lc1'. split; auto.
 
Case "dbBlocks_cons".
  inversion d; subst.
  apply H with (B1:=block_intro l0 ps (cs++cs') tmn)(als0:=als)(Mem:=Mem0) 
               (B1':=B')(als':=als3)(Mem':=Mem3)(lc3:=lc5) in H3; auto.
  clear H.
  destruct H3 as [lc5' [HdbBlock Heq5]].
  apply H0 with (als'0:=als')(als:=als3)(Mem:=Mem3)(Mem'0:=Mem')(lc3:=lc2)(B1:=B')(B1'0:=B1') in Heq5; auto.
  clear H0.
  destruct Heq5 as [lc2' [HdbBlocks Heq2]].
  exists lc2'. split; eauto.

Case "dbFdef_func".
  rewrite e in H1. inversion H1; subst. clear H1.
  assert (J:=@eqAL_initLocals la0 lp TD lc gl lc1' H2).
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(als:=nil)(Mem:=Mem0)(lc3:=lc1)
               (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result))(als':=als1)(Mem':=Mem1) in J; auto.
  clear H. destruct J as [lc2' [HdbBlocks Heq2]].
  rewrite eqAL_params2GVs with (lc':=lc1') in HdbBlocks; eauto.
  apply H0 in Heq2. clear H0.
  destruct Heq2 as [lc3' [Hsubblocks Heq3]].
  apply dbCmds_eqEnv with (lc1':=lc3') in d1; auto.
  destruct d1 as [lc4' [HdbCmds Heq4]].
  exists lc4'. split; eauto.
    eapply dbFdef_func; eauto.
      erewrite eqAL_lookupExFdefViaGV; eauto using eqAL_sym.

Case "dbFdef_proc".
  rewrite e in H1. inversion H1; subst. clear H1.
  assert (J:=@eqAL_initLocals la0 lp TD lc gl lc1' H2).
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(als:=nil)(Mem:=Mem0)(lc3:=lc1)
               (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return_void rid))(als':=als1)(Mem':=Mem1) in J; auto.
  clear H. destruct J as [lc2' [HdbBlocks Heq2]].
  rewrite eqAL_params2GVs with (lc':=lc1') in HdbBlocks; eauto.
  apply H0 in Heq2. clear H0.
  destruct Heq2 as [lc3' [Hsubblocks Heq3]].
  apply dbCmds_eqEnv with (lc1':=lc3') in d1; auto.
  destruct d1 as [lc4' [HdbCmds Heq4]].
  exists lc4'. split; eauto.
    eapply dbFdef_proc; eauto.
      erewrite eqAL_lookupExFdefViaGV; eauto using eqAL_sym.
Qed.

Lemma dbCall_eqEnv : forall S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr lc1',
  dbCall S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbCall S TD Ps fs gl lc1' Mem0 call0 lc2' Mem' tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_eqEnv as [J _].
  unfold dbCall_eqEnv_prop in J. eauto.
Qed.

Lemma dbSubblock_eqEnv : forall S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr lc1',
  dbSubblock S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbSubblock S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_eqEnv as [_ [J _]].
  unfold dbSubblock_eqEnv_prop in J. eauto.
Qed.

Lemma dbSubblocks_eqEnv : forall S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr lc1',
  dbSubblocks S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbSubblocks S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_eqEnv as [_ [_ [J _]]].
  unfold dbSubblocks_eqEnv_prop in J. eauto.
Qed.

Lemma dbBlock_eqEnv : forall S TD Ps fs gl F arg tr B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  dbBlock S TD Ps fs gl F arg 
    (mkState (mkEC B1 lc1 als) Mem) 
    (mkState (mkEC B1' lc2 als') Mem') 
    tr ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbBlock S TD Ps fs gl F arg 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_eqEnv as [_ [_ [_ [J _]]]].
  unfold dbBlock_eqEnv_prop in J. eauto.
Qed.

Lemma dbBlocks_eqEnv : forall S TD Ps fs gl F lp tr B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  dbBlocks S TD Ps fs gl F lp
    (mkState (mkEC B1 lc1 als) Mem)
    (mkState (mkEC B1' lc2 als') Mem')
    tr ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbBlocks S TD Ps fs gl F lp 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_eqEnv as [_ [_ [_ [_ [J _]]]]].
  unfold dbBlocks_eqEnv_prop in J. eauto.
Qed.

Lemma dbFdef_eqEnv : forall fv fid rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr la lb lc1',
  dbFdef fv rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr ->
  lookupFdefViaGV TD Ps gl lc1 fs fv = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbFdef fv rt lp S TD Ps lc1' gl fs Mem lc2' als' Mem' B' Rid oResult tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_eqEnv as [_ [_ [_ [_ [_ J]]]]].
  unfold dbFdef_eqEnv_prop in J. eauto.
Qed.

(* subAL *)

Definition subAL X lc1 lc2 := 
  forall i, i `in` dom lc1 -> lookupAL X lc1 i = lookupAL X lc2 i.

Notation "lc1 <<<= lc2" := (subAL _ lc1 lc2) (at level 70, no associativity).

Lemma lookupAL_app1 : forall X (lc1:list (atom*X)) lc2 i,
  i `in` dom lc1 ->
  lookupAL X lc1 i = lookupAL X (lc1++lc2) i.
Proof.
  induction lc1; intros lc2 i Hi_in_lc1.
    fsetdec.
    destruct a as (id, elt); simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i id); auto.
      apply IHlc1. fsetdec.
Qed.    

Lemma lookupAL_app2 : forall X lc1 (lc2:list (atom*X)) i,
  i `notin` dom lc1 ->
  lookupAL X lc2 i = lookupAL X (lc1++lc2) i.
Proof.
  induction lc1; intros lc2 i Hi_notin_lc1; auto.
    destruct a as (id, elt); simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i id); subst; eauto.
      fsetdec.
Qed.    

Lemma subAL_app1 : forall X (lc1:list (atom*X)) lc2 lc,
  lc1 <<<= lc ->
  lc2 <<<= lc ->
  lc1 ++ lc2 <<<= lc.
Proof.
  intros X lc1 lc2 lc Hlc1_sub_lc Hlc2_sub_lc.
  intros i i_in_lc12.
  simpl_env in i_in_lc12.
  apply in_dom_app_inv in i_in_lc12.
  assert (i `in`  dom lc1 \/ i `notin` dom lc1) as i_in_lc1_dec. fsetdec.
  destruct i_in_lc1_dec as [i_in_lc1 | i_notin_lc1].
    rewrite <- Hlc1_sub_lc; auto.
    rewrite <- lookupAL_app1; auto.

    destruct i_in_lc12 as [i_in_lc1 | i_in_lc2].
      fsetdec.
      rewrite <- lookupAL_app2; auto.
Qed.

Lemma lookupALs_tail : forall X l2b l2b' l0,
  l0 `notin` dom l2b ->
  lookupAL X (l2b++l2b') l0 = lookupAL _ l2b' l0.
Proof.
  intros.
  induction l2b; auto.
    destruct a. simpl in *.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l0 a); subst; auto.
      fsetdec.
Qed.

Lemma subAL_app2 : forall X (lc1:list (atom*X)) lc2 lc,
  lc1 <<<= lc ->
  disjoint lc1 lc2 ->
  ~ lc2 <<<= lc ->
  ~ lc1 ++ lc2 <<<= lc.
Proof.
  intros X lc1 lc2 lc Hlc1_sub_lc Hdisj Hlc2_nsub_lc Hlc12_sub_lc.
  apply Hlc2_nsub_lc.
  intros i i_in_lc2.
    assert (i `notin` dom lc1) as i_notin_lc1. solve_uniq.
    assert (i `in` dom (lc1++lc2)) as i_in_lc12. simpl_env. fsetdec.
    apply Hlc12_sub_lc in i_in_lc12.
    erewrite lookupALs_tail in i_in_lc12; eauto.
Qed.
    
(* subAL *)

Lemma getOperandValue_subAL : forall lc1 gl lc2 v TD gv,
  subAL _ lc1 lc2 ->
  getOperandValue TD v lc1 gl = Some gv ->
  getOperandValue TD v lc1 gl = getOperandValue TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD gv Hnon_none HeqAL.
  unfold getOperandValue in *.
  destruct v; auto.
    apply lookupAL_Some_indom in HeqAL. eauto.
Qed.

Lemma subAL_updateAddAL : forall X lc1 lc2 id0 gv0,
  subAL X lc1 lc2 ->
  subAL _ (updateAddAL _ lc1 id0 gv0) (updateAddAL _ lc2 id0 gv0).
Proof.
  unfold subAL. 
  intros.
  rewrite updateAddAL_dom_eq in H0.
  destruct (id0==i0); subst.
    rewrite lookupAL_updateAddAL_eq; auto.
    rewrite lookupAL_updateAddAL_eq; auto.

    assert (i0 `in` dom lc1) as Hi0_in_lc1. fsetdec.
    assert (J:=H i0 Hi0_in_lc1).
    erewrite <- lookupAL_updateAddAL_neq; eauto.
    erewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma subAL_callUpdateLocals : forall TD noret0 rid rt oResult lc1 lc2 gl lc1' lc2',
  subAL _ lc1 lc1' ->
  subAL _ lc2 lc2' ->
  subAL _ (callUpdateLocals TD noret0 rid rt oResult lc1 lc2 gl)
         (callUpdateLocals TD noret0 rid rt oResult lc1' lc2' gl).
Proof.
  intros TD noret0 rid rt oResult lc1 lc2 gl lc1' lc2' H1 H2.
    unfold callUpdateLocals.
    destruct noret0; auto.
      destruct (rt=t=typ_void); auto.
        destruct oResult; simpl; auto.
          destruct v; simpl.
            remember (lookupAL _ lc2 i0) as Lookup.
            destruct Lookup as [gr | _].
              rewrite H2 in HeqLookup; eauto using lookupAL_Some_indom.
              rewrite <- HeqLookup. apply subAL_updateAddAL; auto.

              (* We should prove that if oResult is Some, i0 in lc2. *)
              admit.

          destruct (const2GV TD gl c); auto using subAL_updateAddAL.
Qed.

Lemma subAL_refl : forall X lc,
  subAL X lc lc.
Proof. unfold subAL. auto. Qed.

Lemma subAL_getIncomingValuesForBlockFromPHINodes : forall TD ps B gl lc lc',
  subAL _ lc lc' ->
  getIncomingValuesForBlockFromPHINodes TD ps B gl lc =
  getIncomingValuesForBlockFromPHINodes TD ps B gl lc'.
Proof.
  induction ps; intros; simpl; auto.
    destruct a; auto.
    destruct (getValueViaBlockFromValuels l0 B); auto.
    destruct v; erewrite IHps; eauto.
      (* We should redefine getIncomingValuesForBlockFromPHINodes to be partial. 
         If we cannot find any incoming value, we should return None. *)
      assert (i1 `in` dom lc) as J. admit. 
      rewrite H; auto.
Qed.

Lemma subAL_updateValuesForNewBlock : forall vs lc lc',
  subAL _ lc lc' ->
  subAL _ (updateValuesForNewBlock vs lc) (updateValuesForNewBlock vs lc').
Proof.
  induction vs; intros; simpl; auto.
    destruct a.
    destruct o; auto using subAL_updateAddAL.
Qed.

Lemma subAL_switchToNewBasicBlock : forall TD B1 B2 gl lc lc',
  subAL _ lc lc' ->
  subAL _ (switchToNewBasicBlock TD B1 B2 gl lc) (switchToNewBasicBlock TD B1 B2 gl lc').
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite subAL_getIncomingValuesForBlockFromPHINodes; eauto.
  apply subAL_updateValuesForNewBlock; auto.
Qed.

Lemma subAL_exCallUpdateLocals : forall noret0 rid rt oResult lc lc',
  subAL _ lc lc' ->
  subAL _ (exCallUpdateLocals noret0 rid rt oResult lc)
         (exCallUpdateLocals noret0 rid rt oResult lc').
Proof.
  intros noret0 rid rt oResult lc lc' H1.
    unfold exCallUpdateLocals.
    destruct noret0; auto.
      destruct (rt=t=typ_void); auto.
        destruct oResult; simpl; auto using subAL_updateAddAL.
Qed.

Lemma subAL_lookupExFdecViaGV : forall gl TD Ps lc lc' fs fv gv,
  subAL _ lc lc' ->
  lookupExFdecViaGV TD Ps gl lc fs fv = Some gv ->
  lookupExFdecViaGV TD Ps gl lc fs fv = lookupExFdecViaGV TD Ps gl lc' fs fv.
Proof.
  intros.
  unfold lookupExFdecViaGV in *.
  assert (exists gv, getOperandValue TD fv lc gl = Some gv) as J.
    destruct (getOperandValue TD fv lc gl); eauto.
      inversion H0.
  destruct J as [gv' J].
  erewrite getOperandValue_subAL; eauto.
Qed.

Lemma subAL_lookupExFdefViaGV : forall gl TD Ps lc lc' fs fv gv,
  subAL _ lc lc' ->
  lookupFdefViaGV TD Ps gl lc fs fv = Some gv ->
  lookupFdefViaGV TD Ps gl lc fs fv = lookupFdefViaGV TD Ps gl lc' fs fv.
Proof.
  intros.
  unfold lookupFdefViaGV in *.
  assert (exists gv, getOperandValue TD fv lc gl = Some gv) as J.
    destruct (getOperandValue TD fv lc gl); eauto.
      inversion H0.
  destruct J as [gv' J].
  erewrite getOperandValue_subAL; eauto.
Qed.

Lemma subAL_params2OpGVs : forall lp TD lc gl lc',
  subAL _ lc lc' ->
  params2OpGVs TD lp lc gl = params2OpGVs TD lp lc' gl.
Proof.
  induction lp; intros; simpl; auto.
    destruct a.
    destruct v; simpl.
      (* We should redefine params2OpGVs to be partial. 
         If we cannot find any param value, we should return None. *)
      assert (i0 `in` dom lc) as J. admit. 
      rewrite H; auto. erewrite IHlp; eauto.
      erewrite IHlp; eauto.
Qed.

Lemma subAL_params2GVs : forall lp TD lc gl lc',
  subAL _ lc lc' ->
  params2GVs TD lp lc gl = params2GVs TD lp lc' gl.
Proof.
  induction lp; intros; simpl; auto.
    destruct a.
    unfold params2GVs.
    erewrite subAL_params2OpGVs; eauto.
Qed.

Lemma subAL_initLocals : forall la lp TD lc gl lc',
  subAL _ lc lc' ->
  subAL _ (initLocals la (params2GVs TD lp lc gl)) (initLocals la (params2GVs TD lp lc' gl)).
Proof.
  intros. erewrite subAL_params2GVs; eauto using subAL_refl.
  (* This lemma will be broken if we fix subAL_params2GVs 
     The problem is that the Fdef rule should check that params2GVs lp = Some ... *)
Qed.

Lemma BOP_subAL : forall lc1 gl lc2 bop0 sz0 v1 v2 TD gv,
  subAL _ lc1 lc2 ->
  BOP TD lc1 gl bop0 sz0 v1 v2 = Some gv ->
  BOP TD lc1 gl bop0 sz0 v1 v2 = BOP TD lc2 gl bop0 sz0 v1 v2.
Proof.
  intros lc1 gl lc2 bop0 sz0 v1 v2 TD gv HsubEnv Hsome.
  apply BOP_inversion in Hsome.
  destruct Hsome as [gv1 [gv2 [Hsome1 [Hsome2 _]]]].
  unfold BOP in *.
  erewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1); eauto.
  erewrite getOperandValue_subAL with (lc2:=lc2)(v:=v2); eauto.
Qed.

Lemma FBOP_subAL : forall lc1 gl lc2 fbop0 fp0 v1 v2 TD gv,
  subAL _ lc1 lc2 ->
  FBOP TD lc1 gl fbop0 fp0 v1 v2 = Some gv ->
  FBOP TD lc1 gl fbop0 fp0 v1 v2 = FBOP TD lc2 gl fbop0 fp0 v1 v2.
Proof.
  intros lc1 gl lc2 fbop0 fp0 v1 v2 TD gv HsubEnv Hsome.
  apply FBOP_inversion in Hsome.
  destruct Hsome as [gv1 [gv2 [Hsome1 [Hsome2 _]]]].
  unfold FBOP in *.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1)(gv:=gv1); auto.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v2)(gv:=gv2); auto.
Qed.

Lemma getOperandPtr_subAL : forall lc1 gl lc2 v TD gv,
  subAL _ lc1 lc2 ->
  getOperandPtr TD v lc1 gl = Some gv ->
  getOperandPtr TD v lc1 gl = getOperandPtr TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD gv HsubEnv Hsome.
  apply getOperandPtr_inversion in Hsome.
  destruct Hsome as [gv0 [Hsome _]].
  unfold getOperandPtr in *.
  erewrite getOperandValue_subAL; eauto.
Qed.

Lemma getOperandInt_subAL : forall lc1 gl lc2 sz v TD gv,
  subAL _ lc1 lc2 ->
  getOperandInt TD sz v lc1 gl = Some gv ->
  getOperandInt TD sz v lc1 gl = getOperandInt TD sz v lc2 gl.
Proof.
  intros lc1 gl lc2 sz0 v TD gv HsubAL Hsome.
  apply getOperandInt_inversion in Hsome.
  destruct Hsome as [gv0 [Hsome _]].
  unfold getOperandInt in *.
  erewrite getOperandValue_subAL; eauto.
Qed.

Lemma getOperandPtrInBits_subAL : forall lc1 gl lc2 sz v TD gv,
  subAL _ lc1 lc2 ->
  getOperandValue TD v lc1 gl = Some gv ->
  getOperandPtrInBits TD sz v lc1 gl = getOperandPtrInBits TD sz v lc2 gl.
Proof.
  intros lc1 gl lc2 sz0 v TD gv HsubAL Hsome.
  unfold getOperandPtrInBits in *.
  erewrite getOperandValue_subAL; eauto.
Qed.

Lemma CAST_subAL : forall lc1 gl lc2 op t1 v1 t2 TD gv,
  subAL _ lc1 lc2 ->
  CAST TD lc1 gl op t1 v1 t2 = Some gv ->
  CAST TD lc1 gl op t1 v1 t2 = CAST TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD gv HsubAL Hsome.
  apply CAST_inversion in Hsome.
  destruct Hsome as [gv1 [Hsome _]].
  unfold CAST in *.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1)(gv:=gv1); auto.
Qed.

Lemma TRUNC_subAL : forall lc1 gl lc2 op t1 v1 t2 TD gv,
  subAL _ lc1 lc2 ->
  TRUNC TD lc1 gl op t1 v1 t2 = Some gv ->
  TRUNC TD lc1 gl op t1 v1 t2 = TRUNC TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD gv HsubAL Hsome.
  apply TRUNC_inversion in Hsome.
  destruct Hsome as [gv1 [Hsome _]].
  unfold TRUNC in *.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1)(gv:=gv1); auto.
Qed.

Lemma EXT_subAL : forall lc1 gl lc2 op t1 v1 t2 TD gv,
  subAL _ lc1 lc2 ->
  EXT TD lc1 gl op t1 v1 t2 = Some gv ->
  EXT TD lc1 gl op t1 v1 t2 = EXT TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD gv HsubAL Hsome.
  apply EXT_inversion in Hsome.
  destruct Hsome as [gv1 [Hsome _]].
  unfold EXT in *.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1)(gv:=gv1); auto.
Qed.

Lemma ICMP_subAL : forall lc1 gl lc2 cond t v1 v2 TD gv,
  subAL _ lc1 lc2 ->
  ICMP TD lc1 gl cond t v1 v2 = Some gv ->
  ICMP TD lc1 gl cond t v1 v2 = ICMP TD lc2 gl cond t v1 v2.
Proof.
  intros lc1 gl lc2 cond0 t v1 v2 TD gv HsubAL Hsome.
  apply ICMP_inversion in Hsome.
  destruct Hsome as [gv1 [gv2 [Hsome1 [Hsome2 _]]]].
  unfold ICMP in *.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1)(gv:=gv1); auto.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v2)(gv:=gv2); auto.
Qed.

Lemma FCMP_subAL : forall lc1 gl lc2 cond fp v1 v2 TD gv,
  subAL _ lc1 lc2 ->
  FCMP TD lc1 gl cond fp v1 v2 = Some gv ->
  FCMP TD lc1 gl cond fp v1 v2 = FCMP TD lc2 gl cond fp v1 v2.
Proof.
  intros lc1 gl lc2 cond0 fp v1 v2 TD gv HsubAL Hsome.
  apply FCMP_inversion in Hsome.
  destruct Hsome as [gv1 [gv2 [Hsome1 [Hsome2 _]]]].
  unfold FCMP in *.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v1)(gv:=gv1); auto.
  rewrite getOperandValue_subAL with (lc2:=lc2)(v:=v2)(gv:=gv2); auto.
Qed.

Lemma intValues2Nats_subAL : forall l0 lc1 gl lc2 TD zs,
  subAL _ lc1 lc2 ->
  intValues2Nats TD l0 lc1 gl = Some zs ->
  intValues2Nats TD l0 lc1 gl = intValues2Nats TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD zs HsubAL Hsome; simpl in *; auto.
    assert (exists gv, getOperandValue TD v lc1 gl = Some gv) as J.
      destruct (getOperandValue TD v lc1 gl); eauto.
        inversion Hsome.
    destruct J as [gv J].
    erewrite getOperandValue_subAL with (lc2:=lc2)(v:=v); eauto.
      rewrite J in Hsome.
      destruct (GV2int TD Size.ThirtyTwo gv); try solve [inversion Hsome].
      assert (exists zs', intValues2Nats TD l0 lc1 gl = Some zs') as J'.
        destruct (intValues2Nats TD l0 lc1 gl); eauto.
      destruct J' as [gv' J'].
      erewrite IHl0; eauto.
Qed.

Lemma values2GVs_subAL : forall l0 lc1 gl lc2 TD gvs,
  subAL _ lc1 lc2 ->
  values2GVs TD l0 lc1 gl = Some gvs ->
  values2GVs TD l0 lc1 gl = values2GVs TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD gvs HsubAL Hsome; simpl in *; auto.
    assert (exists gv, getOperandValue TD v lc1 gl = Some gv) as J.
      destruct (getOperandValue TD v lc1 gl); eauto.
        inversion Hsome.
    destruct J as [gv J].
    erewrite getOperandValue_subAL with (lc2:=lc2)(v:=v); eauto.
      rewrite J in Hsome.
      assert (exists gvs', values2GVs TD l0 lc1 gl = Some gvs') as J'.
        destruct (values2GVs TD l0 lc1 gl); eauto.
      destruct J' as [gvs' J'].
      erewrite IHl0; eauto.
Qed.

(* subEnv *)

Lemma dbCmd_subEnv : forall TD c lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1',
  dbCmd TD gl lc1 als1 Mem1 c lc2 als2 Mem2 tr ->
  subAL _ lc1 lc1' ->
  exists lc2', 
    dbCmd TD gl lc1' als1 Mem1 c lc2' als2 Mem2 tr /\
    subAL _ lc2 lc2'.
Proof.
  intros TD c lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1' HdbCmd HsubEnv.
  (dbCmd_cases (inversion HdbCmd) Case); subst.
Case "dbBop".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  erewrite BOP_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbFBop".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  erewrite FBOP_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbExtractValue".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv').
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 
  split; eauto using subAL_updateAddAL.
  
Case "dbInsertValue".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv'').
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 
  erewrite getOperandValue_subAL with (lc2:=lc1') in H0; eauto. 
  split; eauto using subAL_updateAddAL.

Case "dbMalloc".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 (blk2GV TD mb)).
  erewrite getOperandValue_subAL with (lc2:=lc1') in H0; eauto. 
  split; eauto using subAL_updateAddAL.

Case "dbFree".
  exists lc1'.
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 

Case "dbAlloca".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 (blk2GV TD mb)).
  erewrite getOperandValue_subAL with (lc2:=lc1') in H0; eauto. 
  split; eauto using subAL_updateAddAL.

Case "dbLoad".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv).
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 
  split; eauto using subAL_updateAddAL.

Case "dbStore".
  exists lc1'.
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 
  erewrite getOperandValue_subAL with (lc2:=lc1') in H0; eauto. 

Case "dbGEP".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 mp').
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 
  erewrite values2GVs_subAL with (lc2:=lc1') in H0; eauto. 
(* rewrite GEP_eqAL with (lc2:=lc1') in H0; auto. *)
  split; eauto using subAL_updateAddAL.

Case "dbTrunc".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  erewrite TRUNC_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbExt".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  erewrite EXT_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbCast".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  erewrite CAST_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbIcmp".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  erewrite ICMP_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbFcmp".
  assert (HupdateEnv:=HsubEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  erewrite FCMP_subAL with (lc2:=lc1') in H; eauto.
  split; eauto using subAL_updateAddAL.

Case "dbSelect".
  erewrite getOperandValue_subAL with (lc2:=lc1') in H; eauto. 
  erewrite getOperandValue_subAL with (lc2:=lc1') in H0; eauto. 
  erewrite getOperandValue_subAL with (lc2:=lc1') in H1; eauto. 
  assert (HupdateEnv:=HsubEnv).
  exists (if isGVZero TD cond0 then updateAddAL _ lc1' id0 gv2 else updateAddAL _ lc1' id0 gv1).
  split; auto.
    destruct (isGVZero TD cond0); auto using subAL_updateAddAL.

Case "dbLib".
  admit.
Qed.

Lemma dbCmds_subEnv : forall TD cs lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1',
  dbCmds TD gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr ->
  subAL _ lc1 lc1' ->
  exists lc2', 
    dbCmds TD gl lc1' als1 Mem1 cs lc2' als2 Mem2 tr /\
    subAL _ lc2 lc2'.
Proof.
  intros TD cs lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1' HdbCmds HsubEnv.
  generalize dependent lc1'.
  induction HdbCmds; intros.
    exists lc1'. split; auto.

    apply dbCmd_subEnv with (lc1':=lc1') in H; auto.
    destruct H as [lc2' [HdbCmd HsubEnv']].
    apply IHHdbCmds in HsubEnv'; auto.
    destruct HsubEnv' as [lc3' [HdbCmds' HsubEnv'']].
    exists lc3'.
    split; eauto.
Qed.

Lemma dbTerminator_subEnv : forall TD F gl lc1 tmn lc2 tr lc1' B B',
  dbTerminator TD F gl B lc1 tmn B' lc2 tr ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbTerminator TD F gl B lc1' tmn B' lc2' tr /\
    subAL _ lc2 lc2'.
Proof.
  intros TD F gl lc1 tmn lc2 tr lc1' B B' HdbTerminator HsubAL.
  inversion HdbTerminator; subst.
    exists (switchToNewBasicBlock TD (block_intro l' ps' sbs' tmn') B gl lc1').
    split.
      apply dbBranch with (c:=c); auto.
        erewrite <- getOperandValue_subAL; eauto.
      apply subAL_switchToNewBasicBlock; auto.     
  
    exists (switchToNewBasicBlock TD (block_intro l' ps' sbs' tmn') B gl lc1').
    split.
      apply dbBranch_uncond; auto.
      apply subAL_switchToNewBasicBlock; auto.
Qed.     

Definition dbCall_subEnv_prop S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr
  (db:dbCall S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr) := 
  forall lc1',
  subAL _ lc1 lc1' ->
  exists lc2',
    dbCall S TD Ps fs gl lc1' Mem0 call0 lc2' Mem' tr /\
    subAL _ lc2 lc2'.
Definition dbSubblock_subEnv_prop S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr
  (db:dbSubblock S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr) :=
  forall lc1',
  subAL _ lc1 lc1' ->
  exists lc2',
    dbSubblock S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    subAL _ lc2 lc2'.
Definition dbSubblocks_subEnv_prop S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr
  (db:dbSubblocks S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr) :=
  forall lc1',
  subAL _ lc1 lc1' ->
  exists lc2',
    dbSubblocks S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    subAL _ lc2 lc2'.
Definition dbBlock_subEnv_prop S TD Ps fs gl F arg state1 state2 tr
  (db:dbBlock S TD Ps fs gl F arg state1 state2 tr) :=
  forall B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  state1 = mkState (mkEC B1 lc1 als) Mem ->
  state2 = mkState (mkEC B1' lc2 als') Mem' ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbBlock S TD Ps fs gl F arg 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    subAL _ lc2 lc2'.
Definition dbBlocks_subEnv_prop S TD Ps fs gl F lp state1 state2 tr
  (db:dbBlocks S TD Ps fs gl F lp state1 state2 tr) :=
  forall B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  state1 = mkState (mkEC B1 lc1 als) Mem ->
  state2 = mkState (mkEC B1' lc2 als') Mem' ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbBlocks S TD Ps fs gl F lp 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    subAL _ lc2 lc2'.
Definition dbFdef_subEnv_prop fv rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr
  (db:dbFdef fv rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr) :=
  forall fid la lb lc1',
  lookupFdefViaGV TD Ps gl lc1 fs fv = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbFdef fv rt lp S TD Ps lc1' gl fs Mem lc2' als' Mem' B' Rid oResult tr /\
    subAL _ lc2 lc2'.

Lemma db_subEnv :
  (forall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db, 
     dbCall_subEnv_prop S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db,
     dbSubblock_subEnv_prop S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db,
     dbSubblocks_subEnv_prop S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl F arg state1 state2 tr db,
     dbBlock_subEnv_prop S TD Ps fs gl F arg state1 state2 tr db) /\
  (forall S TD Ps fs gl F lp state1 state2 tr db,
     dbBlocks_subEnv_prop S TD Ps fs gl F lp state1 state2 tr db) /\
  (forall fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db,
     dbFdef_subEnv_prop fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db).
Proof.
(db_mutind_cases
  apply db_mutind with
    (P  := dbCall_subEnv_prop)
    (P0 := dbSubblock_subEnv_prop)
    (P1 := dbSubblocks_subEnv_prop)
    (P2 := dbBlock_subEnv_prop)
    (P3 := dbBlocks_subEnv_prop)
    (P4 := dbFdef_subEnv_prop) Case);
  unfold dbCall_subEnv_prop, 
         dbSubblock_subEnv_prop, dbSubblocks_subEnv_prop,
         dbBlock_subEnv_prop, dbBlocks_subEnv_prop,
         dbFdef_subEnv_prop; intros; subst; auto.
Case "dbCall_internal".
  inversion d; subst.
    apply H with (lc1':=lc1') in H1; auto. clear H.
    destruct H1 as [lc2' [HdbBlocks HeqEnv]].
    exists (callUpdateLocals TD noret0 rid rt (Some Result) lc1' lc2' gl).
    split; eauto using dbCall_internal, subAL_callUpdateLocals.

    apply H with (lc1':=lc1') in H1; auto. clear H.
    destruct H1 as [lc2' [HdbBlocks HeqEnv]].
    exists (callUpdateLocals TD noret0 rid rt None lc1' lc2' gl).
    split; eauto using dbCall_internal, subAL_callUpdateLocals.

Case "dbCall_external".
  exists (exCallUpdateLocals noret0 rid rt oresult lc1').
  split; eauto using subAL_exCallUpdateLocals.
    eapply dbCall_external; eauto.
      erewrite <- subAL_lookupExFdecViaGV; eauto.
    rewrite <- subAL_params2GVs with (lc:=lc); auto.

Case "dbSubblock_intro".
  apply dbCmds_subEnv with (lc1':=lc1') in d; auto.
  destruct d as [lc2' [HdbCmds HsubEnv2]].
  apply H in HsubEnv2. clear H.
  destruct HsubEnv2 as [lc3' [HdbCall HsubEnv3]].
  exists lc3'.
  split; eauto.

Case "dbSubblocks_nil".
  exists lc1'. split; auto.
 
Case "dbSubblocks_cons".
  apply H in H1. clear H.
  destruct H1 as [lc2' [HdbSubblock Heq2]].
  apply H0 in Heq2. clear H0.
  destruct Heq2 as [lc3' [HdbSubblocks Heq3]].
  exists lc3'. split; eauto.

Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  apply H in H2. clear H.
  destruct H2 as [lc2' [HdbSubblocks Heq2]].
  apply dbCmds_subEnv with (lc1':=lc2') in d0; auto.
  destruct d0 as [lc3' [HdbCmds Heq3]].
  apply dbTerminator_subEnv with (lc1':=lc3') in d1; auto.
  destruct d1 as [lc5' [HdbTerminator Heq5]].
  exists lc5'. split; eauto.

Case "dbBlocks_nil".
  inversion H0; subst. clear H0.
  exists lc1'. split; auto.
 
Case "dbBlocks_cons".
  inversion d; subst.
  apply H with (B1:=block_intro l0 ps (cs++cs') tmn)(als0:=als)(Mem:=Mem0) 
               (B1':=B')(als':=als3)(Mem':=Mem3)(lc3:=lc5) in H3; auto.
  clear H.
  destruct H3 as [lc5' [HdbBlock Heq5]].
  apply H0 with (als'0:=als')(als:=als3)(Mem:=Mem3)(Mem'0:=Mem')(lc3:=lc2)(B1:=B')(B1'0:=B1') in Heq5; auto.
  clear H0.
  destruct Heq5 as [lc2' [HdbBlocks Heq2]].
  exists lc2'. split; eauto.

Case "dbFdef_func".
  rewrite e in H1. inversion H1; subst. clear H1.
  assert (J:=@subAL_initLocals la0 lp TD lc gl lc1' H2).
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(als:=nil)(Mem:=Mem0)(lc3:=lc1)
               (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result))(als':=als1)(Mem':=Mem1) in J; auto.
  clear H. destruct J as [lc2' [HdbBlocks Hsub2]].
  rewrite subAL_params2GVs with (lc':=lc1') in HdbBlocks; eauto.
  apply H0 in Hsub2. clear H0.
  destruct Hsub2 as [lc3' [Hsubblocks Hsub3]].
  apply dbCmds_subEnv with (lc1':=lc3') in d1; auto.
  destruct d1 as [lc4' [HdbCmds Hsub4]].
  exists lc4'. split; eauto.
    eapply dbFdef_func; eauto.
      erewrite <- subAL_lookupExFdefViaGV; eauto.

Case "dbFdef_proc".
  rewrite e in H1. inversion H1; subst. clear H1.
  assert (J:=@subAL_initLocals la0 lp TD lc gl lc1' H2).
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(als:=nil)(Mem:=Mem0)(lc3:=lc1)
               (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return_void rid))(als':=als1)(Mem':=Mem1) in J; auto.
  clear H. destruct J as [lc2' [HdbBlocks Hsub2]].
  rewrite subAL_params2GVs with (lc':=lc1') in HdbBlocks; eauto.
  apply H0 in Hsub2. clear H0.
  destruct Hsub2 as [lc3' [Hsubblocks Hsub3]].
  apply dbCmds_subEnv with (lc1':=lc3') in d1; auto.
  destruct d1 as [lc4' [HdbCmds Hsub4]].
  exists lc4'. split; eauto.
    eapply dbFdef_proc; eauto.
      erewrite <- subAL_lookupExFdefViaGV; eauto.
Qed.

Lemma dbCall_subEnv : forall S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr lc1',
  dbCall S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbCall S TD Ps fs gl lc1' Mem0 call0 lc2' Mem' tr /\
    subAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_subEnv as [J _].
  unfold dbCall_subEnv_prop in J. eauto.
Qed.

Lemma dbSubblock_subEnv : forall S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr lc1',
  dbSubblock S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbSubblock S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    subAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_subEnv as [_ [J _]].
  unfold dbSubblock_subEnv_prop in J. eauto.
Qed.

Lemma dbSubblocks_subEnv : forall S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr lc1',
  dbSubblocks S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbSubblocks S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    subAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_subEnv as [_ [_ [J _]]].
  unfold dbSubblocks_subEnv_prop in J. eauto.
Qed.

Lemma dbBlock_subEnv : forall S TD Ps fs gl F arg tr B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  dbBlock S TD Ps fs gl F arg 
    (mkState (mkEC B1 lc1 als) Mem) 
    (mkState (mkEC B1' lc2 als') Mem') 
    tr ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbBlock S TD Ps fs gl F arg 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    subAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_subEnv as [_ [_ [_ [J _]]]].
  unfold dbBlock_subEnv_prop in J. eauto.
Qed.

Lemma dbBlocks_subEnv : forall S TD Ps fs gl F lp tr B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  dbBlocks S TD Ps fs gl F lp
    (mkState (mkEC B1 lc1 als) Mem)
    (mkState (mkEC B1' lc2 als') Mem')
    tr ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbBlocks S TD Ps fs gl F lp 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    subAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_subEnv as [_ [_ [_ [_ [J _]]]]].
  unfold dbBlocks_subEnv_prop in J. eauto.
Qed.

Lemma dbFdef_subEnv : forall fv fid rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr la lb lc1',
  dbFdef fv rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr ->
  lookupFdefViaGV TD Ps gl lc1 fs fv = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  subAL _ lc1 lc1' ->
  exists lc2',
    dbFdef fv rt lp S TD Ps lc1' gl fs Mem lc2' als' Mem' B' Rid oResult tr /\
    subAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_subEnv as [_ [_ [_ [_ [_ J]]]]].
  unfold dbFdef_subEnv_prop in J. eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)


