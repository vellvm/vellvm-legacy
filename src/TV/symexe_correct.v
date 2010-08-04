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
Require Import symexe_sound.
Require Import seop_llvmop.

Export SimpleSE.

(* cmd2sbs *)

Record subblock := mkSB
{
  NBs : list nbranch;
  call_cmd : cmd;
  call_cmd_isCall : Instruction.isCallInst call_cmd = true
}.


Fixpoint cmds2sbs (cs:list cmd) : (list subblock*list nbranch) :=
match cs with
| nil => (nil,nil)
| c::cs' =>
  match (isCallInst_dec c) with
  | left isnotcall => 
    match (cmds2sbs cs') with
    | (nil, nbs0) => (nil, mkNB c isnotcall::nbs0) 
    | (mkSB nbs call0 iscall0::sbs', nbs0) => 
      (mkSB (mkNB c isnotcall::nbs) call0 iscall0::sbs', nbs0) 
    end
  | right iscall => 
    match (cmds2sbs cs') with
    | (sbs, nbs0) => (mkSB nil c iscall::sbs, nbs0) 
    end
  end
end.


Lemma cmds2sbs_nil_inv : forall cs,
  cmds2sbs cs = (nil, nil) ->
  cs = nil.
Proof.
  destruct cs; intros; auto.
    simpl in H.
    destruct (isCallInst_dec c).
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
    remember (isCallInst_dec a) as R'.
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

Definition dbCmds__cmds2nbs : forall TD lc als gl Mem1 cs lc' als' gl' Mem2 tr, 
  dbCmds TD lc als gl Mem1 cs lc' als' gl' Mem2 tr ->
  exists nbs, cmds2sbs cs = (nil, nbs).
Proof.
  intros.
  induction H; simpl.
    exists nil. auto.

    destruct IHdbCmds as [nbs J].
    destruct (isCallInst_dec c).
      rewrite J. exists (mkNB c e::nbs). auto.

      apply dbCmd_isNotCallInst in H.
      rewrite e in H. inversion H.
Qed.

Lemma dbCall_isCallInst : forall S TD Ps lc gl Mem1 c lc' gl' Mem2 tr,
  dbCall S TD Ps lc gl Mem1 c lc' gl' Mem2 tr ->
  Instruction.isCallInst c = true.
Proof.
  intros S TD Ps lc gl Mem1 c lc' gl' Mem2 tr HdbCall.
  induction HdbCall; auto.
Qed.

Lemma cmdscall2sbs : forall cs call0 nbs
  (isCall0:Instruction.isCallInst call0=true),
  cmds2sbs cs = (nil, nbs) ->
  isCallInst_dec call0 = right isCall0 ->
  cmds2sbs (cs++call0::nil) = (mkSB nbs call0 isCall0::nil, nil).
Proof.
  induction cs; intros; simpl in *.
    inversion H; subst.
    rewrite H0. auto.

    destruct (isCallInst_dec a).
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

Lemma dbSubblock__cmds2sb : forall S TD Ps lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr,
  dbSubblock S TD Ps lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr ->
  exists sb, cmds2sbs cs = (sb::nil, nil).
Proof.
  intros.
  inversion H; subst.
  apply dbCmds__cmds2nbs in H0.
  destruct H0 as [nbs H0].
  remember (isCallInst_dec call0) as R.
  destruct R.
    apply dbCall_isCallInst in H1.
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
    destruct (isCallInst_dec a).
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

Lemma dbSubblocks__cmds2sbs : forall S TD Ps lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr,
  dbSubblocks S TD Ps lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr ->
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
    remember (isCallInst_dec a) as R.
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
    destruct (isCallInst_dec a).
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
    destruct (isCallInst_dec a).
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
      destruct (isCallInst_dec c).
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
    remember (isCallInst_dec a) as R.
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

(* Correctness of the cmds validator *)

Definition tv_cmds (nbs1 nbs2 : list nbranch) (lc gl:GVMap) :=
se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) nbs1 =
se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) nbs2.

Lemma tv_cmds__is__correct : forall TD nbs nbs' lc1 als1 gl1 Mem1 lc2 als2 gl2 Mem2 tr,
  uniq gl1 ->
  uniq lc1 ->  
  wf_nbranchs nbs' ->
  tv_cmds nbs nbs' lc1 gl1 ->
  dbCmds TD lc1 als1 gl1 Mem1 (nbranchs2cmds nbs) lc2 als2 gl2 Mem2 tr ->
  dbCmds TD lc1 als1 gl1 Mem1 (nbranchs2cmds nbs') lc2 als2 gl2 Mem2 tr.
Proof.
  intros TD nbs nbs' lc1 als1 gl1 Mem1 lc2 als2 gl2 Mem2 tr Huniqg Huniqc Wf Htv_cmds HdbCmds.
  unfold tv_cmds in Htv_cmds.
  assert (Uniqs:=HdbCmds).
  apply dbCmds_uniq in Uniqs; auto.
  destruct Uniqs as [Uniqg2 Uniqc2].
  apply op_cmds__satisfy__se_cmds in HdbCmds; auto.
  rewrite Htv_cmds in HdbCmds.
  apply se_cmds__denote__op_cmds; auto.
Qed.

Definition tv_subblock (sb1 sb2:subblock) (lc gl:GVMap) :=
match (sb1, sb2) with
| (mkSB nbs1 call1 iscall1, mkSB nbs2 call2 iscall2) =>
  let st1 := se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) nbs1 in
  let st2 := se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) nbs2 in
  let cl1 := se_call st1 call1 iscall1 in
  let cl2 := se_call st2 call2 iscall2 in
  st1 = st2 /\ call1 = call2
end.

Fixpoint tv_subblocks (sbs1 sbs2:list subblock) (lc gl:GVMap) :=
match (sbs1, sbs2) with
| (nil, nil) => True
| (sb1::sbs1', sb2::sbs2') => tv_subblock sb1 sb2 lc gl /\ tv_subblocks sbs1' sbs2' lc gl 
| _ => False
end.

Fixpoint tv_phinodes (ps1 ps2:list phinode) :=
match (ps1, ps2) with
| (nil, nil) => True
| (p1::ps1', p2::ps2') => p1=p2 /\ tv_phinodes ps1' ps2'
| _ => False
end.

Definition tv_block (b1 b2:block) (lc gl:GVMap) :=
match (b1, b2) with
| (block_intro l1 ps1 cs1 tmn1, block_intro l2 ps2 cs2 tmn2) =>
  match (cmds2sbs cs1, cmds2sbs cs2) with
  | ((sbs1, nbs1), (sbs2, nbs2)) =>
    l1 = l2 /\ 
    tv_phinodes ps1 ps2 /\ 
    tv_subblocks sbs1 sbs2 lc gl /\ 
    tv_cmds nbs1 nbs2 lc gl /\ 
    tmn1 = tmn2
  end
end.

Fixpoint tv_blocks (bs1 bs2:list block) (lc gl:GVMap) :=
match (bs1, bs2) with
| (nil, nil) => True
| (b1::bs1', b2::bs2') => tv_block b1 b2 lc gl /\ tv_blocks bs1' bs2' lc gl 
| _ => False
end.

Variable lc0 gl0 : GVMap.

Definition tv_fdef (f1 f2:fdef) (gl:GVMap) :=
match (f1, f2) with
| (fdef_intro fh1 lb1, fdef_intro fh2 lb2) =>
  fh1 = fh2 /\ tv_blocks lb1 lb2 lc0 gl
end.

Fixpoint tv_products (Ps1 Ps2:list product):=
match (Ps1, Ps2) with
| (nil, nil) => True
| (product_fdec f1::Ps1', product_fdec f2::Ps2') => 
  f1 = f2 /\ tv_products Ps1' Ps2'
| (product_fdef f1::Ps1', product_fdef f2::Ps2') => 
  tv_fdef f1 f2 gl0 /\ tv_products Ps1' Ps2'
| (product_gvar gvar1::Ps1', product_gvar gvar2::Ps2') => 
  gvar1 = gvar2 /\ tv_products Ps1' Ps2'
| _ => False
end.

Definition tv_module (m1 m2:module) :=
match (m1, m2) with
| (module_intro TD1 Ps1, module_intro TD2 Ps2) =>
  TD1 = TD2 /\ tv_products Ps1 Ps2
end.

Fixpoint tv_system (S1 S2:system) :=
match (S1, S2) with
| (nil, nil) => True
| (m1::S1', m2::S2') => tv_module m1 m2 /\ tv_system S1' S2'
| _ => False
end.

Inductive wf_subblock : subblock -> Prop :=
| wf_subblock_intro : forall nbs call0 iscall0, 
  wf_nbranchs nbs ->
  wf_subblock (mkSB nbs call0 iscall0).

Inductive wf_subblocks : list subblock -> Prop :=
| wf_subblocks_nil : wf_subblocks nil
| wf_subblocks_cons : forall sb sbs,
  wf_subblock sb ->
  wf_subblocks sbs ->
  wf_subblocks (sb::sbs).

Inductive wf_block : block -> Prop :=
| wf_block_intro : forall l ps cs sbs nbs tmn, 
  cmds2sbs cs = (sbs,nbs) ->
  wf_subblocks sbs ->
  wf_nbranchs nbs ->
  wf_block (block_intro l ps cs tmn).

Lemma tv_terminator__is__correct : forall TD fh1 lb1 fh2 lb2 B1 B2 lc gl tmn B1' lc' tr,
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) gl0 ->
  tv_block B1 B2 lc gl ->
  dbTerminator TD (fdef_intro fh1 lb1) B1 lc gl tmn B1' lc' tr ->
  exists B2', exists n,
    tv_block B1' B2' lc gl /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    dbTerminator TD (fdef_intro fh2 lb2) B2 lc gl tmn B2' lc' tr.
Proof.
  intros TD fh1 lb1 fh2 lb2 B1 B2 lc gl tmn B1' lc' tr Htv_fdef Htv_block HdbTerminator.
  inversion HdbTerminator; subst.
    assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' lc gl /\ 
                                  nth_error lb1 n = Some (block_intro l' ps' sbs' tmn') /\
                                  nth_error lb2 n = Some B2') as J.
      admit. (*lookup*)
    destruct J as [B2' [n [J1 [J2 J3]]]].
    exists B2'. exists n. split; auto. split; auto. split; auto.
    destruct B2' as [l2' ps2' sbs2' tmn2'].
    apply dbBranch with (c:=c); auto.
      admit. (*lookup*)
      admit. (*switch*)
    
    assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' lc gl /\ 
                                  nth_error lb1 n = Some (block_intro l' ps' sbs' tmn') /\
                                  nth_error lb2 n = Some B2') as J.
      admit. (*lookup*)
    destruct J as [B2' [n [J1 [J2 J3]]]].
    exists B2'. exists n. split; auto. split; auto. split; auto.
    destruct B2' as [l2' ps2' sbs2' tmn2'].
    apply dbBranch_uncond; auto.
      admit. (*lookup*)
      admit. (*switch*)
Qed.

Lemma tv_blocks_nth_Some_inv : forall lb1 lb2 lc gl n B1,
  tv_blocks lb1 lb2 lc gl ->
  nth_error lb1 n = Some B1 ->
  exists B2, 
    nth_error lb2 n = Some B2 /\ tv_block B1 B2 lc gl.
Admitted. (*nth*)


Definition tv_dbCall__is__correct_prop S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr
  (db:dbCall S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr) :=
  forall S2 Ps2,
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  dbCall S2 TD Ps2 lc gl Mem0 call0 lc' gl' Mem' tr.
Definition tv_subblock__is__correct_prop S1 TD Ps1 lc als gl Mem cs1 lc' als' gl' Mem' tr
  (db:dbSubblock S1 TD Ps1 lc als gl Mem cs1 lc' als' gl' Mem' tr) :=
  forall S2 Ps2 cs2 sb1 sb2,
  uniq gl ->
  uniq lc ->
  cmds2sbs cs1 = (sb1::nil, nil) ->
  cmds2sbs cs2 = (sb2::nil, nil) ->
  wf_subblock sb2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_subblock sb1 sb2 lc gl ->
  dbSubblock S2 TD Ps2 lc als gl Mem cs2 lc' als' gl' Mem' tr.
Definition tv_subblocks__is__correct_prop S1 TD Ps1 lc als gl Mem cs1 lc' als' gl' Mem' tr
  (db:dbSubblocks S1 TD Ps1 lc als gl Mem cs1 lc' als' gl' Mem' tr) :=
  forall S2 Ps2 sbs1 sbs2 cs2,
  uniq gl ->
  uniq lc ->
  cmds2sbs cs1 = (sbs1, nil) ->
  cmds2sbs cs2 = (sbs2, nil) ->
  wf_subblocks sbs2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_subblocks sbs1 sbs2 lc gl ->
  dbSubblocks S2 TD Ps2 lc als gl Mem cs2 lc' als' gl' Mem' tr.
Definition tv_block__is__correct_prop S1 TD Ps1 F1 arg state1 state2 tr
  (db:dbBlock S1 TD Ps1 F1 arg state1 state2 tr) :=
  forall S2 Ps2 fh1 lb1 fh2 lb2 B1 lc als gl Mem B1' lc' als' gl' Mem' B2,
  state1 = mkState (mkEC B1 lc als) gl Mem ->
  state2 = mkState (mkEC B1' lc' als') gl' Mem' ->
  F1 = fdef_intro fh1 lb1 ->
  uniq gl ->
  uniq lc ->
  wf_block B2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) gl0 ->
  tv_block B1 B2 lc gl ->
  exists B2', exists n,
    dbBlock S2 TD Ps2 (fdef_intro fh2 lb2) arg 
      (mkState (mkEC B2 lc als) gl Mem) 
      (mkState (mkEC B2' lc' als') gl' Mem')
      tr /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' lc gl.
Definition tv_blocks__is__correct_prop S1 TD Ps1 F1 lp state1 state2 tr
  (db:dbBlocks S1 TD Ps1 F1 lp state1 state2 tr) :=
  forall S2 Ps2 fh1 lb1 fh2 lb2 gl lc n tmn1
                            l1 ps1 cs1 ps1' l1' als
                            lc' gl' Mem Mem' als' tmn1' cs1',
  state1 = (mkState (mkEC (block_intro l1 ps1 cs1 tmn1) lc als) gl Mem) ->
  state2 = (mkState (mkEC (block_intro l1' ps1' cs1' tmn1') lc' als') gl' Mem') ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  F1 = fdef_intro fh1 lb1 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) gl0 ->
  tv_blocks lb1 lb2 lc gl ->
  nth_error lb1 n = Some (block_intro l1 ps1 cs1 tmn1) ->
  exists l2, exists ps2, exists cs2, exists tmn2, 
  exists l2', exists ps2', exists cs2', exists tmn2', exists n',
    nth_error lb2 n = Some (block_intro l2 ps2 cs2 tmn2) /\
    nth_error lb1 n' = Some (block_intro l1' ps1' cs1' tmn1') /\
    nth_error lb2 n' = Some (block_intro l2' ps2' cs2' tmn2') /\
    tv_block (block_intro l1 ps1 cs1 tmn1) (block_intro l2 ps2 cs2 tmn2) lc gl /\
    tv_block (block_intro l1' ps1' cs1' tmn1') (block_intro l2' ps2' cs2' tmn2') lc gl /\
    dbBlocks S2 TD Ps2 (fdef_intro fh2 lb2) lp
      (mkState (mkEC (block_intro l2 ps2 cs2 tmn2) lc als) gl Mem)
      (mkState (mkEC (block_intro l2' ps2' cs2' tmn2') lc' als') gl' Mem')
      tr.
Definition tv_fdef__is__correct_prop fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' B1' Rid oResult tr
  (db:dbFdef fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' B1' Rid oResult tr) :=
  forall Ps2 S2 la lb1,
  lookupFdefViaIDFromProducts Ps1 fid = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists lb2, exists B2', exists n,
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' lc gl /\
    lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2 lc gl /\
    dbFdef fid rt lp S2 TD Ps2 lc gl Mem lc' gl' als' Mem' B2' Rid oResult tr.


Lemma tv__is__correct :
  (forall S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr db, 
     tv_dbCall__is__correct_prop S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr db) /\
  (forall S1 TD Ps1 lc als gl Mem sb1 lc' als' gl' Mem' tr db,
     tv_subblock__is__correct_prop S1 TD Ps1 lc als gl Mem sb1 lc' als' gl' Mem' tr db) /\
  (forall S1 TD Ps1 lc als gl Mem sbs1 lc' als' gl' Mem' tr db,
     tv_subblocks__is__correct_prop S1 TD Ps1 lc als gl Mem sbs1 lc' als' gl' Mem' tr db) /\
  (forall S1 TD Ps1 F1 arg state1 state2 tr db,
     tv_block__is__correct_prop S1 TD Ps1 F1 arg state1 state2 tr db) /\
  (forall S1 TD Ps1 F1 lp state1 state2 tr db,
     tv_blocks__is__correct_prop S1 TD Ps1 F1 lp state1 state2 tr db) /\
  (forall fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' B' Rid oResult tr db,
     tv_fdef__is__correct_prop fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' B' Rid oResult tr db).
Proof.
(db_mutind_cases
  apply db_mutind with
    (P  := tv_dbCall__is__correct_prop)
    (P0 := tv_subblock__is__correct_prop)
    (P1 := tv_subblocks__is__correct_prop)
    (P2 := tv_block__is__correct_prop)
    (P3 := tv_blocks__is__correct_prop)
    (P4 := tv_fdef__is__correct_prop) Case);
  unfold tv_dbCall__is__correct_prop, 
         tv_subblock__is__correct_prop, tv_subblocks__is__correct_prop,
         tv_block__is__correct_prop, tv_blocks__is__correct_prop,
         tv_fdef__is__correct_prop; intros; subst.
Case "dbCall_intro".
  inversion d; subst.
    apply H with (S2:=S2)(Ps2:=Ps2) in H2; auto.
    clear H.
    destruct H2 as [lb2 [B2' [n [J1 [J2 [J3 [J4 [J5 J6]]]]]]]].
    eauto.

    apply H with (S2:=S2)(Ps2:=Ps2) in H2; auto.
    clear H.
    destruct H2 as [lb2 [B2' [n [J1 [J2 [J3 [J4 [J5 J6]]]]]]]].
    eauto.

Case "dbSubblock_intro".
  unfold tv_subblock in H7.
  destruct sb1.
  destruct sb2.
  apply cmds2sb_inv in H2.
  destruct H2 as [cs' [call1 [J1 [J2 J3]]]].
  apply cmds2nbs__nbranchs2cmds in J2.
  apply app_inj_tail in J1.
  destruct J1; subst.
  apply cmds2sb_inv in H3.
  destruct H3 as [cs2' [call0 [J1 [J2 J3]]]]; subst.
  apply cmds2nbs__nbranchs2cmds in J2.
  destruct H7 as [EQ1 EQ2]; subst.
  inversion H4; subst.
  apply tv_cmds__is__correct with (nbs':=NBs1) in d; eauto.

Case "dbSubblocks_nil".
  simpl in H1. inversion H1; subst.
  destruct sbs2;try solve [auto | simpl in H6; inversion H6].
    apply cmds2sbs_nil_inv in H2; subst; auto.

Case "dbSubblocks_cons".
  assert (Hcs2sb := d).
  apply dbSubblock__cmds2sb in Hcs2sb.
  destruct Hcs2sb as [sb Hcs2sb].
  assert (Hcs'2sbs := d0).
  apply dbSubblocks__cmds2sbs in Hcs'2sbs.
  destruct Hcs'2sbs as [sbs Hcs'2sbs].
  apply cmds_cons2sbs_inv with (sb:=sb)(sbs':=sbs) in H3; auto.
  subst.
  simpl in H8.
  destruct sbs2 ; simpl in H8; inversion H8.
  clear H8.
  apply cmds2sbs_cons_inv in H4.
  destruct H4 as [cs21 [cs22 [cs212s [cs222sbs2 EQ]]]]; subst.
  inversion H5; subst. clear H5.  
  apply H with (S2:=S2)(Ps2:=Ps2)(cs2:=cs21) in H3; auto.
  assert (tv_subblocks sbs sbs2 lc2 gl2) as J. 
    admit. (*tv inclusion*)
  assert (uniq lc2) as Uniqc2. admit. (*uniq*)
  assert (uniq gl2) as Uniqg2. admit. (*uniq*)
  apply H0 with (S2:=S2)(Ps2:=Ps2)(cs2:=cs22) in J; eauto.

Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  destruct B2 as [l2 ps2 cs2 tmn2].
  unfold tv_block in H9.
  remember (cmds2sbs (cs++cs')) as R1.
  remember (cmds2sbs cs2) as R2.
  destruct R1 as [sbs1 nbs1].
  destruct R2 as [sbs2 nbs2].
  destruct H9 as [EQ1 [Htv_phinodes [Htv_subblocks [Htv_cmds EQ2]]]]; subst.

  assert (Hcs2sbs1 := d).
  apply dbSubblocks__cmds2sbs in Hcs2sbs1.
  destruct Hcs2sbs1 as [sbs Hcs2sbs1].
  assert (Hcs2nbs1 := d0).
  apply dbCmds__cmds2nbs in Hcs2nbs1.
  destruct Hcs2nbs1 as [nbs Hcs2nbs1].
 
  assert (J:=HeqR1).
  symmetry in J.
  apply cmds_rcons2sbs_inv with (sbs:=sbs)(nbs:=nbs) in J; auto using cmds2nbranchs__cmds2nbs.
  destruct J; subst.

  assert (J:=HeqR2).
  symmetry in J.
  apply cmds2sbs_inv in J.
  destruct J as [cs1 [cs3 [EQ [Hcs12sbs2 Hcs32nbs2]]]]; subst.
  inversion H5; subst. clear H5.

  apply cmds_rcons2sbs_inv with (sbs:=sbs2)(nbs:=nbs2) in H9; auto.
  destruct H9; subst.
  assert (J:=Htv_subblocks).
  apply H with (S2:=S2)(Ps2:=Ps2)(cs2:=cs1) in J; auto.
  clear H.

  apply cmds2nbs__nbranchs2cmds in Hcs2nbs1. subst.
  apply cmds2nbs__nbranchs2cmds in Hcs32nbs2. subst.
  assert (tv_cmds nbs nbs2 lc2 gl2) as Htv_cmds'.
    admit. (*tv inclusion*)
  assert (uniq lc2) as Uniqc2. admit.
  assert (uniq gl2) as Uniqg2. admit.
  apply tv_cmds__is__correct with (nbs':=nbs2) in d0; auto.
  apply tv_terminator__is__correct with (B2:=block_intro l2 ps2 (cs1++nbranchs2cmds nbs2) tmn2)(fh2:=fh2)(lb2:=lb2) in d1; auto.
    destruct d1 as [B2' [n [Htv_block1'2' [J2 [J3 Hdb]]]]].
    exists B2'. exists n. 
    split; eauto.
    split; auto.
    split; auto.
      clear - Htv_block1'2'.
      admit. (*tv inclusion*)

    unfold tv_block.
    rewrite <- HeqR1.
    rewrite <- HeqR2.
    split; auto.
    split; auto.
    split.
      clear - Htv_subblocks.
      admit. (*tv inclusion*)      
    split; auto.
      clear - Htv_cmds.
      admit. (*tv inclusion*)      

Case "dbBlocks_nil".
  inversion H0; subst. clear H0.
  apply tv_blocks_nth_Some_inv with (n:=n)(B1:=block_intro l1' ps1' cs1' tmn1') in H5; auto.
  destruct H5 as [[l2 ps2 cs2 tmn2] [Hnth_error2 Htv_block]].
  exists l2. exists ps2. exists cs2. exists tmn2.
  exists l2. exists ps2. exists cs2. exists tmn2. 
  exists n.
  split; auto.

Case "dbBlocks_cons".
  inversion d; subst.
  assert (J:=H7).  
  apply tv_blocks_nth_Some_inv with (n:=n)(B1:=block_intro l1 ps1 (cs++cs') tmn1) in J; auto.
  destruct J as [[l2 ps2 cs2 tmn2] [Hnth_error2 Htv_block12]].
  assert (J:=Htv_block12).
  apply H with (S2:=S0)(Ps2:=Ps2)(fh3:=fh2)(lb3:=lb2)(fh2:=fh1)(lb2:=lb1)(Mem:=Mem0)(B1':=B')(lc':=lc4)(als':=als3)(gl':=gl3)(Mem':=Mem3)(als0:=als) in J; auto.
    destruct J as [B2' [n' [Hdb [J1 [J2 Htv_block12']]]]].
    clear H.
    destruct B' as [l3 ps3 cs3 tmn3].
    assert (tv_blocks lb1 lb2 lc4 gl3) as H.
      admit. (*tv inclusion*)      
    apply H0 with (S2:=S0)(Ps2:=Ps2)(fh2:=fh1)(fh3:=fh2)(n:=n')(tmn1:=tmn3)
      (l1:=l3)(ps1:=ps3)(cs1:=cs3)(ps1'0:=ps1')(l1'0:=l1')(als:=als3)(lc'0:=lc')(gl'0:=gl')
      (Mem:=Mem3)(Mem'0:=Mem')(als'0:=als')(tmn1'0:=tmn1')(cs1'0:=cs1') in H; auto.
    destruct H as [l4 [ps4 [cs4 [tmn4 [l4' [ps4' [cs4' [tmn4' [n'' [J3 [J4 [J5 [J6 [J7 J8]]]]]]]]]]]]]].
    clear H0.
    exists l2. exists ps2. exists cs2. exists tmn2.
    exists l4'. exists ps4'. exists cs4'. exists tmn4'.
    exists n''.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.
      clear - J7.
      admit. (*tv inclusion*)      
      
      rewrite J2 in J3.
      inversion J3; subst. clear J3.
      eauto.

    admit. (*uniq*)
    admit. (*uniq*)
    admit. (*Wf*)

Case "dbFdef_func".
    rewrite H1 in e. inversion e; subst. clear e.
    assert (exists lb2, lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
                        tv_blocks lb lb2 lc gl) as J.
      clear - H1 H3.
      admit. (*lookup*)
    destruct J as [lb2 [H4 H5]].
    assert (tv_blocks lb lb2 (initLocals la (params2GVs TD lp lc gl)) gl) as Htv_blocks.
      clear - H5.
      admit. (*tv inclusion*)      
    apply H with (S2:=S2)(Ps2:=Ps2)(fh1:=fheader_intro rt fid la)(fh2:=fheader_intro rt fid la)(n:=0)
      (ps1':=ps2)(l1':=l2)(als:=nil)(lc':=lc1)(gl':=gl1)
      (Mem:=Mem0)(Mem':=Mem1)(als':=als1)(tmn1':=insn_return rid rt Result)(cs1':=cs21++cs22) 
      (ps3:=ps1)(cs2:=cs1)(tmn2:=tmn1)(l3:=l1)in Htv_blocks; auto.
      clear H.
      destruct Htv_blocks as [l3 [ps3 [cs3 [tmn2 [l2' [ps2' [cs2' [tmn2' [n' [J1 [J2 [J3 [J4 [J5 J6]]]]]]]]]]]]]].

      exists lb2. exists (block_intro l2' ps2' cs2' tmn2'). exists n'.
      split; auto. split; auto.
      split.
        clear - J5.
        admit. (*tv inclusion*)      
      split; auto. split; auto.

      unfold tv_block in J5.
      remember (cmds2sbs (cs21++cs22)) as R1.
      remember (cmds2sbs cs2') as R2.
      destruct R1 as [sbs1 nbs1].
      destruct R2 as [sbs2 nbs2].
      destruct J5 as [EQ1 [Htv_phinodes [Htv_subblocks [Htv_cmds EQ2]]]]; subst.

      assert (Hcs21sbs1 := d0).
      apply dbSubblocks__cmds2sbs in Hcs21sbs1.
      destruct Hcs21sbs1 as [sbs Hcs21sbs1].
      assert (Hcs22nbs1 := d1).
      apply dbCmds2nbranchs in Hcs22nbs1.
      destruct Hcs22nbs1 as [nbs Hcs22nbs1].

      assert (J:=HeqR1).
      symmetry in J.
      apply cmds_rcons2sbs_inv with (sbs:=sbs)(nbs:=nbs) in J; auto using cmds2nbranchs__cmds2nbs.
      destruct J; subst.

      assert (J:=HeqR2).
      symmetry in J.
      apply cmds2sbs_inv in J.
      destruct J as [cs41 [cs42 [EQ [Hcs41sbs2 Hcs42nbs2]]]]; subst.

      assert (J:=HeqR2).
      symmetry in J.
      apply cmds_rcons2sbs_inv with (sbs:=sbs2)(nbs:=nbs2) in J; auto.
      destruct J; subst. clear H H6.

      assert (tv_subblocks sbs sbs2 lc1 gl1) as Htv_subblocks'.
        clear - Htv_subblocks.
        admit.
      assert (uniq lc1) as Uniqc1. admit.
      assert (uniq gl1) as Uniqg1. admit.
      apply H0 with (S2:=S2)(Ps2:=Ps2)(cs2:=cs41) in Htv_subblocks'; auto.
        clear H0.

        apply cmds2nbranchs__nbranchs2cmds in Hcs22nbs1. subst.
        apply cmds2nbs__nbranchs2cmds in Hcs42nbs2. subst.
        assert (tv_cmds nbs nbs2 lc2 gl2) as Htv_cmds'.
          admit. (*tv inclusion*)
        assert (uniq lc2) as Uniqc2. admit.
        assert (uniq gl2) as Uniqg2. admit.
        apply tv_cmds__is__correct with (nbs':=nbs2) in d1; auto.
          apply dbFdef_func with (l1:=l3)(ps1:=ps3)(cs1:=cs3)(tmn1:=tmn2)(la:=la)(lb:=lb2)
            (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(als1:=als1)(l2:=l2')(ps2:=ps2')(cs21:=cs41)(cs22:=nbranchs2cmds nbs2)
            (lc3:=lc3)(als3:=als3)(gl3:=gl3)(Mem3:=Mem3)(lc2:=lc2)(als2:=als2)(gl2:=gl2)(Mem2:=Mem2); eauto.
          admit. (*Wf*) 
        admit. (*Wf*) 

      unfold tv_fdef.
      split; auto.
        clear - H5.
        admit. (*tv inclusion*)      

Case "dbFdef_proc".
    rewrite H1 in e. inversion e; subst. clear e.
    assert (exists lb2, lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
                        tv_blocks lb lb2 lc gl) as J.
      clear - H1 H3.
      admit.  (*lookup*)
    destruct J as [lb2 [H4 H5]].
    assert (tv_blocks lb lb2 (initLocals la (params2GVs TD lp lc gl)) gl) as Htv_blocks.
      clear - H5.
      admit. (*tv inclusion*)      
    apply H with (S2:=S2)(Ps2:=Ps2)(fh1:=fheader_intro rt fid la)(fh2:=fheader_intro rt fid la)(n:=0)
      (ps1':=ps2)(l1':=l2)(als:=nil)(lc':=lc1)(gl':=gl1)
      (Mem:=Mem0)(Mem':=Mem1)(als':=als1)(tmn1':=insn_return_void rid)(cs1':=cs21++cs22) 
      (ps3:=ps1)(cs2:=cs1)(tmn2:=tmn1)(l3:=l1)in Htv_blocks; auto.
      clear H.
      destruct Htv_blocks as [l3 [ps3 [cs3 [tmn2 [l2' [ps2' [cs2' [tmn2' [n' [J1 [J2 [J3 [J4 [J5 J6]]]]]]]]]]]]]].

      exists lb2. exists (block_intro l2' ps2' cs2' tmn2'). exists n'.
      split; auto. split; auto.
      split.
        clear - J5.
        admit. (*tv inclusion*)      
      split; auto. split; auto.

      unfold tv_block in J5.
      remember (cmds2sbs (cs21++cs22)) as R1.
      remember (cmds2sbs cs2') as R2.
      destruct R1 as [sbs1 nbs1].
      destruct R2 as [sbs2 nbs2].
      destruct J5 as [EQ1 [Htv_phinodes [Htv_subblocks [Htv_cmds EQ2]]]]; subst.

      assert (Hcs21sbs1 := d0).
      apply dbSubblocks__cmds2sbs in Hcs21sbs1.
      destruct Hcs21sbs1 as [sbs Hcs21sbs1].
      assert (Hcs22nbs1 := d1).
      apply dbCmds2nbranchs in Hcs22nbs1.
      destruct Hcs22nbs1 as [nbs Hcs22nbs1].

      assert (J:=HeqR1).
      symmetry in J.
      apply cmds_rcons2sbs_inv with (sbs:=sbs)(nbs:=nbs) in J; auto using cmds2nbranchs__cmds2nbs.
      destruct J; subst.

      assert (J:=HeqR2).
      symmetry in J.
      apply cmds2sbs_inv in J.
      destruct J as [cs41 [cs42 [EQ [Hcs41sbs2 Hcs42nbs2]]]]; subst.

      assert (J:=HeqR2).
      symmetry in J.
      apply cmds_rcons2sbs_inv with (sbs:=sbs2)(nbs:=nbs2) in J; auto.
      destruct J; subst. clear H H6.

      assert (tv_subblocks sbs sbs2 lc1 gl1) as Htv_subblocks'.
        clear - Htv_subblocks.
        admit.
      assert (uniq lc1) as Uniqc1. admit.
      assert (uniq gl1) as Uniqg1. admit.
      apply H0 with (S2:=S2)(Ps2:=Ps2)(cs2:=cs41) in Htv_subblocks'; auto.
        clear H0.

        apply cmds2nbranchs__nbranchs2cmds in Hcs22nbs1. subst.
        apply cmds2nbs__nbranchs2cmds in Hcs42nbs2. subst.
        assert (tv_cmds nbs nbs2 lc2 gl2) as Htv_cmds'.
          admit. (*tv inclusion*)
        assert (uniq lc2) as Uniqc2. admit.
        assert (uniq gl2) as Uniqg2. admit.
        apply tv_cmds__is__correct with (nbs':=nbs2) in d1; auto.
          apply dbFdef_proc with (l1:=l3)(ps1:=ps3)(cs1:=cs3)(tmn1:=tmn2)(la:=la)(lb:=lb2)
            (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(als1:=als1)(l2:=l2')(ps2:=ps2')(cs21:=cs41)(cs22:=nbranchs2cmds nbs2)
            (lc3:=lc3)(als3:=als3)(gl3:=gl3)(Mem3:=Mem3)(lc2:=lc2)(als2:=als2)(gl2:=gl2)(Mem2:=Mem2); eauto.
          admit. (*Wf*) 
        admit. (*Wf*) 

      unfold tv_fdef.
      split; auto.
        clear - H5.
        admit. (*tv inclusion*)      
Qed.   

Lemma tv_dbCall__is__correct : forall S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr S2 Ps2,
  dbCall S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  dbCall S2 TD Ps2 lc gl Mem0 call0 lc' gl' Mem' tr.
Proof.
  intros.
  destruct tv__is__correct as [J _].
  unfold tv_dbCall__is__correct_prop in J.
  eapply J; eauto.
Qed.

Definition tv_subblock__is__correct : forall S1 TD Ps1 lc als gl Mem cs1 lc' als' gl' Mem' tr S2 Ps2 cs2 sb1 sb2,
  dbSubblock S1 TD Ps1 lc als gl Mem cs1 lc' als' gl' Mem' tr ->
  uniq gl ->
  uniq lc ->
  cmds2sbs cs1 = (sb1::nil, nil) ->
  cmds2sbs cs2 = (sb2::nil, nil) ->
  wf_subblock sb2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_subblock sb1 sb2 lc gl ->
  dbSubblock S2 TD Ps2 lc als gl Mem cs2 lc' als' gl' Mem' tr.
Proof.
  intros.
  destruct tv__is__correct as [_ [J _]].
  unfold tv_subblock__is__correct_prop in J.
  eapply J; eauto.
Qed.

Lemma tv_subblocks__is__correct : forall S1 TD Ps1 lc als gl Mem cs1 lc' als' gl' Mem' tr S2 Ps2 sbs1 sbs2 cs2,
  dbSubblocks S1 TD Ps1 lc als gl Mem cs1 lc' als' gl' Mem' tr ->
  uniq gl ->
  uniq lc ->
  cmds2sbs cs1 = (sbs1, nil) ->
  cmds2sbs cs2 = (sbs2, nil) ->
  wf_subblocks sbs2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_subblocks sbs1 sbs2 lc gl ->
  dbSubblocks S2 TD Ps2 lc als gl Mem cs2 lc' als' gl' Mem' tr.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [J _]]].
  unfold tv_subblocks__is__correct_prop in J.
  eapply J; eauto.
Qed.

Lemma tv_block__is__correct : forall S1 TD Ps1 arg tr
  S2 Ps2 fh1 lb1 fh2 lb2 B1 lc als gl Mem B1' lc' als' gl' Mem' B2,
  dbBlock S1 TD Ps1 (fdef_intro fh1 lb1) arg (mkState (mkEC B1 lc als) gl Mem) (mkState (mkEC B1' lc' als') gl' Mem') tr ->
  uniq gl ->
  uniq lc ->
  wf_block B2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) gl0 ->
  tv_block B1 B2 lc gl ->
  exists B2', exists n,
    dbBlock S2 TD Ps2 (fdef_intro fh2 lb2) arg 
      (mkState (mkEC B2 lc als) gl Mem) 
      (mkState (mkEC B2' lc' als') gl' Mem')
      tr /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' lc gl.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [_ [J _]]]].
  unfold tv_block__is__correct_prop in J.
  eapply J with (state1:=(mkState (mkEC B1 lc als) gl Mem0))(state2:=(mkState (mkEC B1' lc' als') gl' Mem'))(F1:=(fdef_intro fh1 lb1)); eauto.
Qed.

Lemma tv_blocks__is__correct : forall S1 TD Ps1 lp tr
  S2 Ps2 fh1 lb1 fh2 lb2 gl lc n tmn1
                            l1 ps1 sbs1 ps1' l1' als
                            lc' gl' Mem Mem' als' tmn1' sbs1',
  dbBlocks S1 TD Ps1 (fdef_intro fh1 lb1) lp (mkState (mkEC (block_intro l1 ps1 sbs1 tmn1) lc als) gl Mem) (mkState (mkEC (block_intro l1' ps1' sbs1' tmn1') lc' als') gl' Mem') tr ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) gl0 ->
  tv_blocks lb1 lb2 lc gl ->
  nth_error lb1 n = Some (block_intro l1 ps1 sbs1 tmn1) ->
  exists l2, exists ps2, exists sbs2, exists tmn2, 
  exists l2', exists ps2', exists sbs2', exists tmn2', exists n',
    nth_error lb2 n = Some (block_intro l2 ps2 sbs2 tmn2) /\
    nth_error lb1 n' = Some (block_intro l1' ps1' sbs1' tmn1') /\
    nth_error lb2 n' = Some (block_intro l2' ps2' sbs2' tmn2') /\
    tv_block (block_intro l1 ps1 sbs1 tmn1) (block_intro l2 ps2 sbs2 tmn2) lc gl /\
    tv_block (block_intro l1' ps1' sbs1' tmn1') (block_intro l2' ps2' sbs2' tmn2') lc gl /\
    dbBlocks S2 TD Ps2 (fdef_intro fh2 lb2) lp
      (mkState (mkEC (block_intro l2 ps2 sbs2 tmn2) lc als) gl Mem)
      (mkState (mkEC (block_intro l2' ps2' sbs2' tmn2') lc' als') gl' Mem')
      tr.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [_ [_ [J _]]]]].
  unfold tv_blocks__is__correct_prop in J.
  eapply J with (state1:=(mkState (mkEC (block_intro l1 ps1 sbs1 tmn1) lc als) gl Mem0))(state2:=(mkState (mkEC (block_intro l1' ps1' sbs1' tmn1') lc' als') gl' Mem'))(F1:=(fdef_intro fh1 lb1)); eauto.
Qed.

Lemma _tv_fdef__is__correct : forall fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' B1' Rid oResult tr
  Ps2 S2 la lb1,
  dbFdef fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' B1' Rid oResult tr ->
  lookupFdefViaIDFromProducts Ps1 fid = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists lb2, exists B2', exists n,
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' lc gl /\
    lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2 lc gl /\
    dbFdef fid rt lp S2 TD Ps2 lc gl Mem lc' gl' als' Mem' B2' Rid oResult tr.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [_ [_ [_ J]]]]].
  unfold tv_fdef__is__correct_prop in J.
  eapply J; eauto.
Qed.

Lemma tv_fdef__is__correct : forall ECs fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' B1' Rid oResult tr
  Ps2 S2 la lb1,
  LLVMopsem.dbFdef fid rt lp S1 TD Ps1 ECs lc gl Mem lc' gl' als' Mem' B1' Rid oResult tr ->
  lookupFdefViaIDFromProducts Ps1 fid = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists lb2, exists B2', exists n,
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' lc gl /\
    lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2 lc gl /\
    LLVMopsem.dbFdef fid rt lp S2 TD Ps2 ECs lc gl Mem lc' gl' als' Mem' B2' Rid oResult tr.
Proof.
  intros.
  apply llvmop_dbFdef__seop_dbFdef in H.
  apply _tv_fdef__is__correct with (Ps2:=Ps2)(S2:=S2)(la:=la)(lb1:=lb1) in H; auto.
  destruct H as [lb2 [B2' [n [J1 [J2 [J3 [J4 [J5 J6]]]]]]]].
  exists lb2. exists B2'. exists n.
  repeat (split; auto).
    apply seop_dbFdef__llvmop_dbFdef; auto.
Qed.

Extraction "symexe" tv_blocks.

