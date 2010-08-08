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
Require Import opsem_pp.
Require Import trace.
Require Import symexe_def.
Require Import symexe_complete.
Require Import symexe_sound.
Require Import seop_llvmop.
Require Import assoclist.
Require Import ssa_props.

Export SimpleSE.

(* p&p *)
Lemma se_dbCmd_preservation : forall TD lc als gl Mem0 c lc' als' gl' Mem' tr,
  dbCmd TD lc als gl Mem0 c lc' als' gl' Mem' tr ->
  uniq gl ->
  uniq lc ->
  uniq gl' /\ uniq lc'.
Proof.
  intros TD lc als gl Mem0 c lc' als' gl' Mem' tr HdbCmd Uniqgl Uniqlc.
  (dbCmd_cases (inversion HdbCmd) Case); subst;
    try solve [eapply updateEnv_uniq with (lc:=lc)(gl:=gl); eauto | split; auto].
  Case "dbSelect".
    destruct cond0; eapply updateEnv_uniq with (lc:=lc)(gl:=gl); eauto. 
Qed.

Lemma se_dbCmds_preservation : forall TD lc als gl Mem0 cs lc' als' gl' Mem' tr,
  dbCmds TD lc als gl Mem0 cs lc' als' gl' Mem' tr ->
  uniq gl ->
  uniq lc ->
  uniq gl' /\ uniq lc'.
Proof.
  intros TD lc als gl Mem0 cs lc' als' gl' Mem' tr HdbCmd Uniqgl Uniqlc.
  induction HdbCmd; auto. 
    apply se_dbCmd_preservation in H; auto.
    destruct H; auto.
Qed.

Lemma se_dbTerminator_preservation : forall TD F B lc gl c B' lc' tr,
  dbTerminator TD F B lc gl c B' lc' tr ->
  uniq gl ->
  uniq lc ->
  uniqFdef F ->
  blockInFdefB B F ->
  uniq lc' /\ blockInFdefB B' F.
Proof.
  intros TD F B lc gl c B' lc' tr HdbTerminator Uniqgl Uniqlc UniqF Hblockin.
  inversion HdbTerminator; subst.
    destruct c0.
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

Definition se_dbCall_preservation_prop S TD Ps lc gl Mem0 call0 lc' gl' Mem' tr
  (db:dbCall S TD Ps lc gl Mem0 call0 lc' gl' Mem' tr) :=
  uniq gl ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq gl' /\ uniq lc' .
Definition se_dbSubblock_preservation_prop S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr
  (db:dbSubblock S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr) :=
  uniq gl ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq gl' /\ uniq lc'.
Definition se_dbSubblocks_preservation_prop S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr
  (db:dbSubblocks S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr) :=
  uniq gl ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq gl' /\ uniq lc'.
Definition se_dbBlock_preservation_prop S TD Ps F arg state1 state2 tr
  (db:dbBlock S TD Ps F arg state1 state2 tr) :=
  forall B1 lc als gl Mem B1' lc' als' gl' Mem',
  state1 = mkState (mkEC B1 lc als) gl Mem ->
  state2 = mkState (mkEC B1' lc' als') gl' Mem' ->
  uniq gl ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro TD Ps) F ->
  uniq gl' /\ uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro TD Ps) F.
Definition se_dbBlocks_preservation_prop S TD Ps F lp state1 state2 tr
  (db:dbBlocks S TD Ps F lp state1 state2 tr) :=
  forall B1 lc als gl Mem B1' lc' als' gl' Mem',
  state1 = (mkState (mkEC B1 lc als) gl Mem) ->
  state2 = (mkState (mkEC B1' lc' als') gl' Mem') ->
  uniq gl ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro TD Ps) F ->
  uniq gl' /\ uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro TD Ps) F.
Definition se_dbFdef_preservation_prop fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr
  (db:dbFdef fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr) :=
  forall la lb,
  lookupFdefViaIDFromProducts Ps fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  uniq gl ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq gl' /\ uniq lc' /\ 
  blockInSystemModuleFdef B' S (module_intro TD Ps) (fdef_intro (fheader_intro rt fid la) lb).


Lemma se_db_preservation :
  (forall S TD Ps lc gl Mem0 call0 lc' gl' Mem' tr db, 
     se_dbCall_preservation_prop S TD Ps lc gl Mem0 call0 lc' gl' Mem' tr db) /\
  (forall S TD Ps lc als gl Mem sb lc' als' gl' Mem' tr db,
     se_dbSubblock_preservation_prop S TD Ps lc als gl Mem sb lc' als' gl' Mem' tr db) /\
  (forall S TD Ps lc als gl Mem sbs lc' als' gl' Mem' tr db,
     se_dbSubblocks_preservation_prop S TD Ps lc als gl Mem sbs lc' als' gl' Mem' tr db) /\
  (forall S TD Ps F arg state1 state2 tr db,
     se_dbBlock_preservation_prop S TD Ps F arg state1 state2 tr db) /\
  (forall S TD Ps F lp state1 state2 tr db,
     se_dbBlocks_preservation_prop S TD Ps F lp state1 state2 tr db) /\
  (forall fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr db,
     se_dbFdef_preservation_prop fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr db).
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
         se_dbFdef_preservation_prop; intros; subst.
Case "dbCall_intro".
  inversion d; subst.
    apply H in H4; auto. clear H.
    destruct H4 as [Huniqgl' [Huniqlc' Hblockin]].
    destruct noret0.
      inversion e; subst. split; auto.
      destruct (rt=t=typ_void).
        inversion e; subst. split; auto.
        destruct (getOperandValue TD Result lc' gl').
          symmetry in e.
          apply updateEnv_uniq in e; auto.

          inversion e; subst. split; auto.

    apply H in H4; auto. clear H.
    destruct H4 as [Huniqgl' [Huniqlc' Hblockin]].
    destruct noret0.
      inversion e; subst. split; auto.
      destruct (rt=t=typ_void).
        inversion e; subst. split; auto.
        inversion e; subst. split; auto.

Case "dbSubblock_intro".
  apply se_dbCmds_preservation in d; auto.
  destruct d as [uniqg2 uniqc2]; auto.
 
Case "dbSubblocks_nil".
  split; auto.
 
Case "dbSubblocks_cons".
  assert (J:=H4).
  apply H in J; auto.
  destruct J as [uniqc2 uniqg2].
  apply H0; auto.

Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  apply blockInSystemModuleFdef_inv in H5.
  destruct H5 as [Hblockin [Hinproducts [Hmodulein Hproductin]]].
  apply H in H3; auto.
  destruct H3 as [uniqg2 uniqc2].
  apply se_dbCmds_preservation in d0; auto.
  destruct d0 as [uniqg' uniqc3].
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
  assert (J:=H5).
  apply H with (B1:=block_intro l0 ps (cs++cs') tmn)(lc0:=lc)(als0:=als)(gl0:=gl)(Mem:=Mem0) 
               (B1':=B')(lc':=lc4)(als':=als3)(gl':=gl3)(Mem':=Mem3) in J; auto.
  clear H.
  destruct J as [uniqg3 [uniqc4 B'in]].
  eapply H0; eauto.

Case "dbFdef_func".
  rewrite e in H1. inversion H1; subst. clear H1.
  apply entryBlockInSystemBlockFdef with (TD:=TD)(Ps:=Ps)(S:=S)(fid:=fid) in e0; auto.
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(lc0:=initLocals la0 (params2GVs TD lp lc gl))(als:=nil)(gl0:=gl)(Mem:=Mem0)
               (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result))(lc':=lc1)(als':=als1)(gl':=gl1)(Mem':=Mem1) in e0; auto using initLocals_uniq.
  clear H. destruct e0 as [uniqg1 [uniqc1 Bin]].
  apply H0 in uniqg1; auto. clear H0.
  destruct uniqg1 as [uniqg2 uniqc2].
  apply se_dbCmds_preservation in d1; auto.
  destruct d1 as [uniqg3 uniqc3].
  split; auto.

Case "dbFdef_proc".
  rewrite e in H1. inversion H1; subst. clear H1.
  apply entryBlockInSystemBlockFdef with (TD:=TD)(Ps:=Ps)(S:=S)(fid:=fid) in e0; auto.
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(lc0:=initLocals la0 (params2GVs TD lp lc gl))(als:=nil)(gl0:=gl)(Mem:=Mem0)
               (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return_void rid))(lc':=lc1)(als':=als1)(gl':=gl1)(Mem':=Mem1) in e0; auto using initLocals_uniq.
  clear H. destruct e0 as [uniqg1 [uniqc1 Bin]].
  apply H0 in uniqg1; auto. clear H0.
  destruct uniqg1 as [uniqg2 uniqc2].
  apply se_dbCmds_preservation in d1; auto.
  destruct d1 as [uniqg3 uniqc3].
  split; auto.

Qed.

Lemma se_dbCall_preservation : forall S TD Ps lc gl Mem0 call0 lc' gl' Mem' tr,
  dbCall S TD Ps lc gl Mem0 call0 lc' gl' Mem' tr ->
  uniq gl ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq gl' /\ uniq lc' .
Proof.
  intros.
  destruct se_db_preservation as [J _].
  unfold se_dbCall_preservation_prop in J. eauto.
Qed.

Lemma se_dbSubblock_preservation : forall S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr,
  dbSubblock S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr ->
  uniq gl ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq gl' /\ uniq lc'.
Proof.
  intros.
  destruct se_db_preservation as [_ [J _]].
  unfold se_dbSubblock_preservation_prop in J. eauto.
Qed.

Lemma se_dbSubblocks_preservation : forall S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr,
  dbSubblocks S TD Ps lc als gl Mem cs lc' als' gl' Mem' tr ->
  uniq gl ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq gl' /\ uniq lc'.
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [J _]]].
  unfold se_dbSubblocks_preservation_prop in J. eauto.
Qed.

Lemma se_dbBlock_preservation : forall S TD Ps F arg tr B1 lc als gl Mem B1' lc' als' gl' Mem',
  dbBlock S TD Ps F arg 
    (mkState (mkEC B1 lc als) gl Mem) 
    (mkState (mkEC B1' lc' als') gl' Mem') tr ->
  uniq gl ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro TD Ps) F ->
  uniq gl' /\ uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro TD Ps) F.
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [_ [J _]]]].
  unfold se_dbBlock_preservation_prop in J. eauto.
Qed.

Lemma se_dbBlocks_preservation : forall S TD Ps F lp tr B1 lc als gl Mem B1' lc' als' gl' Mem',
  dbBlocks S TD Ps F lp 
    (mkState (mkEC B1 lc als) gl Mem)
    (mkState (mkEC B1' lc' als') gl' Mem') tr ->
  uniq gl ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro TD Ps) F ->
  uniq gl' /\ uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro TD Ps) F.
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [_ [_ [J _]]]]].
  unfold se_dbBlocks_preservation_prop in J. eauto.
Qed.

Lemma se_dbFdef_preservation : forall fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr la lb,
  dbFdef fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr ->
  lookupFdefViaIDFromProducts Ps fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  uniq gl ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq gl' /\ uniq lc' /\ 
  blockInSystemModuleFdef B' S (module_intro TD Ps) (fdef_intro (fheader_intro rt fid la) lb).
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [_ [_ [_ J]]]]].
  unfold se_dbFdef_preservation_prop in J. eauto.
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
  apply se_dbCmds_preservation in Uniqs; auto.
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

Fixpoint tv_phinodes (ps1 ps2:phinodes) :=
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

Fixpoint tv_blocks (bs1 bs2:blocks) (lc gl:GVMap) :=
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

Fixpoint tv_products (Ps1 Ps2:products):=
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

Lemma lookup_tv_blocks__tv_block : forall lb1 lb2 lc gl l0 B1,
  uniqBlocks lb1 ->
  uniqBlocks lb2 ->
  tv_blocks lb1 lb2 lc gl ->
  lookupAL _ (genLabel2Block_blocks lb1) l0 = Some B1 ->
  exists B2, exists n,
    tv_block B1 B2 lc gl /\
    nth_error lb1 n = Some B1 /\
    nth_error lb2 n = Some B2 /\
    lookupAL _ (genLabel2Block_blocks lb2) l0 = Some B2.
Proof.
  induction lb1; intros; simpl in *.
    inversion H2.

    destruct lb2.
      inversion H1.

      destruct H1 as [J1 J2].
      assert (K:=H).
      apply uniqBlocks__uniqLabel2Block in H.
      apply mergeALs_inv in H2; auto.
      destruct H2 as [H2 | H2].
        exists b. exists 0.
        assert (J:=H2).
        apply genLabel2Block_block_inv in J. subst.
        simpl. repeat (split; auto).
          apply uniqBlocks__uniqLabel2Block in H0.
          apply mergeALs_app; auto.
            left.
            unfold genLabel2Block_block in *.
            destruct B1.
            destruct b. simpl in *.
            unfold tv_block in J1.
            destruct (cmds2sbs c).
            destruct (cmds2sbs c0).
            destruct J1 as [EQ _]; subst.
            destruct (l0==l2); inversion H2; subst; auto.

        simpl_env in K. apply uniqBlocks_inv in K. destruct K.
        assert (K':=H0). apply uniqBlocks__uniqLabel2Block in K'.
        simpl_env in H0. apply uniqBlocks_inv in H0. destruct H0.
        apply IHlb1 with (lb2:=lb2)(lc:=lc)(gl:=gl) in H2; auto.
        destruct H2 as [B2 [n [H8 [H6 [H5 H7]]]]].
        exists B2. exists (S n). simpl. repeat (split; auto).
          apply mergeALs_app; auto.
Qed.        

Lemma tv_blocks_nth_Some_inv : forall lb1 lb2 lc gl n B1,
  uniqBlocks lb1 ->
  uniqBlocks lb2 ->
  tv_blocks lb1 lb2 lc gl ->
  nth_error lb1 n = Some B1 ->
  exists B2, 
    nth_error lb2 n = Some B2 /\ tv_block B1 B2 lc gl.
Proof.
  intros.
  assert (J:=H2).
  apply nth_error__lookupAL_genLabel2Block_blocks in H2; auto.
  destruct H2 as [l0 H2].
  apply lookup_tv_blocks__tv_block with (l0:=l0)(B1:=B1) in H1; auto.
  destruct H1 as [B2 [n' [J1 [J2 [J3 J4]]]]].
  apply uniqBlocks__uniq_nth_error with (n':=n) in J2; auto.
  subst.
  exists B2. split; auto.
Qed.

Lemma lookup_tv_fdef__tv_block : forall fh1 fh2 lb1 lb2 gl0 lc gl l0 B1,
  uniqBlocks lb1 ->
  uniqBlocks lb2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) gl0 ->
  lookupBlockViaLabelFromFdef (fdef_intro fh1 lb1) l0 = Some B1 ->
  exists B2, exists n,
    tv_block B1 B2 lc gl /\
    nth_error lb1 n = Some B1 /\
    nth_error lb2 n = Some B2 /\
    lookupBlockViaLabelFromFdef (fdef_intro fh2 lb2) l0 = Some B2.
Proof.
  intros.
  destruct H1 as [EQ Htv_blocks].
  unfold lookupBlockViaLabelFromFdef in H2.
  unfold genLabel2Block_fdef in H2.
  eapply lookup_tv_blocks__tv_block; eauto.
    admit. (*inclusion*)
Qed.

Lemma tv_block__inv : forall B1 B2 lc gl,
  tv_block B1 B2 lc gl ->
  getBlockLabel B1 = getBlockLabel B2 /\
  tv_phinodes (getPhiNodesFromBlock B1) (getPhiNodesFromBlock B2) /\
  getTerminatorFromBlock B1 = getTerminatorFromBlock B2.
Proof.
  intros.
  destruct B1.
  destruct B2. simpl in *.
  unfold tv_block in H.
  destruct (cmds2sbs c).
  destruct (cmds2sbs c0).
  decompose [and] H. split; auto.
Qed.
 
Lemma tv_getIncomingValuesForBlockFromPHINodes : forall ps1 B1 ps2 B2 lc gl,
  tv_block B1 B2 lc gl ->
  tv_phinodes ps1 ps2 ->
  getIncomingValuesForBlockFromPHINodes ps1 B1 lc =
  getIncomingValuesForBlockFromPHINodes ps2 B2 lc.
Proof.
  induction ps1; intros.
    destruct ps2; simpl in *; auto.
      inversion H0.

    destruct ps2; simpl in *.
      inversion H0.

      destruct H0; subst.
      apply IHps1 with (B1:=B1)(B2:=B2)(lc:=lc)(gl:=gl) in H1; auto.
      rewrite H1.
      apply tv_block__inv in H.
      destruct H as [H _].
      destruct B1.
      destruct B2.
      simpl in *. subst.
      destruct p. simpl. auto.
Qed.     

Lemma tv_switchToNewBasicBlock : forall l1 ps1 sbs1 tmn1 B1 l2 ps2 sbs2 tmn2 B2 lc gl,
  tv_block B1 B2 lc gl ->
  tv_block (block_intro l1 ps1 sbs1 tmn1) (block_intro l2 ps2 sbs2 tmn2) lc gl ->
  switchToNewBasicBlock (block_intro l1 ps1 sbs1 tmn1) B1 lc =
  switchToNewBasicBlock (block_intro l2 ps2 sbs2 tmn2) B2 lc.
Proof.
  unfold switchToNewBasicBlock.
  intros.
  apply tv_block__inv in H0.
  destruct H0 as [_ [H0 _]].
  erewrite tv_getIncomingValuesForBlockFromPHINodes; simpl; eauto.
Qed.

Lemma tv_terminator__is__correct : forall TD fh1 lb1 fh2 lb2 B1 B2 lc gl tmn B1' lc' tr,
  uniqFdef (fdef_intro fh1 lb1) ->
  uniqFdef (fdef_intro fh2 lb2) ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) gl0 ->
  tv_block B1 B2 lc gl ->
  dbTerminator TD (fdef_intro fh1 lb1) B1 lc gl tmn B1' lc' tr ->
  exists B2', exists n,
    tv_block B1' B2' lc gl /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    dbTerminator TD (fdef_intro fh2 lb2) B2 lc gl tmn B2' lc' tr.
Proof.
  intros TD fh1 lb1 fh2 lb2 B1 B2 lc gl tmn B1' lc' tr HuniqF1 HuniqF2 Htv_fdef Htv_block HdbTerminator.
  inversion HdbTerminator; subst.
    destruct c.
      assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' lc gl /\ 
                                  nth_error lb1 n = Some (block_intro l' ps' sbs' tmn') /\
                                  nth_error lb2 n = Some B2' /\
                                  lookupBlockViaLabelFromFdef (fdef_intro fh2 lb2) l1 = Some B2') as J.
        eapply lookup_tv_fdef__tv_block; eauto.
      destruct J as [B2' [n [J1 [J2 [J3 J4]]]]].
      exists B2'. exists n. split; auto. split; auto. split; auto.
      destruct B2' as [l2' ps2' sbs2' tmn2'].
      apply dbBranch with (c:=0); auto.
        eapply tv_switchToNewBasicBlock; eauto.
    
      assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' lc gl /\ 
                                  nth_error lb1 n = Some (block_intro l' ps' sbs' tmn') /\
                                  nth_error lb2 n = Some B2' /\
                                  lookupBlockViaLabelFromFdef (fdef_intro fh2 lb2) l2 = Some B2') as J.
        eapply lookup_tv_fdef__tv_block; eauto.
      destruct J as [B2' [n [J1 [J2 [J3 J4]]]]].
      exists B2'. exists n. split; auto. split; auto. split; auto.
      destruct B2' as [l2' ps2' sbs2' tmn2'].
      apply dbBranch with (c:=S c); auto.
        eapply tv_switchToNewBasicBlock; eauto.

    assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' lc gl /\ 
                                  nth_error lb1 n = Some (block_intro l' ps' sbs' tmn') /\
                                  nth_error lb2 n = Some B2' /\
                                  lookupBlockViaLabelFromFdef (fdef_intro fh2 lb2) l0 = Some B2') as J.
      eapply lookup_tv_fdef__tv_block; eauto.
    destruct J as [B2' [n [J1 [J2 [J3 J4]]]]].
    exists B2'. exists n. split; auto. split; auto. split; auto.
    destruct B2' as [l2' ps2' sbs2' tmn2'].
    apply dbBranch_uncond; auto.
      eapply tv_switchToNewBasicBlock; eauto.
Qed.

Lemma tv_products__lookupFdefViaIDFromProducts : forall Ps1 Ps2 fid rt la lb1 lc gl,
  tv_products Ps1 Ps2 ->
  lookupFdefViaIDFromProducts Ps1 fid = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  exists lb2,
    lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2 lc gl.
Proof.
  induction Ps1; intros.
    destruct Ps2; inversion H.
      inversion H0.

    destruct a; simpl in H.
      destruct Ps2; try solve [inversion H].
      simpl in H0.
      destruct p; inversion H; subst.
      apply IHPs1 with (fid:=fid)(rt:=rt)(la:=la)(lb1:=lb1)(lc:=lc)(gl:=gl) in H2; auto.
 
      destruct Ps2; try solve [inversion H].
      simpl in H0.
      destruct p; inversion H; subst.
      apply IHPs1 with (fid:=fid)(rt:=rt)(la:=la)(lb1:=lb1)(lc:=lc)(gl:=gl) in H2; auto.

      destruct Ps2; try solve [inversion H].
      simpl in *.
      destruct p; inversion H; subst. 
      simpl in *.
      destruct f.
      destruct f0.
      unfold tv_fdef in H1.
      destruct H1 as [EQ H1]; subst.
      simpl in *.
      remember (getFheaderID f0) as R.
      destruct (R==fid); subst.
        inversion H0. subst b. 
        exists b0. split; auto.
          admit. (*tv inclusion*)      

        destruct H.
        apply IHPs1 with (Ps2:=Ps2)(lc:=lc)(gl:=gl) in H0; auto.
Qed.

Definition tv_dbCall__is__correct_prop S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr
  (db:dbCall S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr) :=
  forall S2 Ps2,
  uniq gl ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
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
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
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
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
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
  uniqSystem S1 ->
  uniqSystem S2 ->
  productInSystemModuleB (product_fdef (fdef_intro fh1 lb1)) S1 (module_intro TD Ps1) ->
  productInSystemModuleB (product_fdef (fdef_intro fh2 lb2)) S2 (module_intro TD Ps2) ->
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
  uniq gl ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  productInSystemModuleB (product_fdef (fdef_intro fh1 lb1)) S1 (module_intro TD Ps1) ->
  productInSystemModuleB (product_fdef (fdef_intro fh2 lb2)) S2 (module_intro TD Ps2) ->
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
  uniq gl ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
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
    apply H with (S2:=S2)(Ps2:=Ps2) in H8; auto.
    clear H.
    destruct H8 as [lb2 [B2' [n [J1 [J2 [J3 [J4 [J5 J6]]]]]]]].
    eauto.

    apply H with (S2:=S2)(Ps2:=Ps2) in H8; auto.
    clear H.
    destruct H8 as [lb2 [B2' [n [J1 [J2 [J3 [J4 [J5 J6]]]]]]]].
    eauto.

Case "dbSubblock_intro".
  unfold tv_subblock in H11.
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
  destruct H11 as [EQ1 EQ2]; subst.
  inversion H8; subst.
  assert (uniq gl2 /\ uniq lc2) as J.
    apply se_dbCmds_preservation in d; auto.
  destruct J as [Uniqg2 Uniqc2].
  apply tv_cmds__is__correct with (nbs':=NBs1) in d; eauto.

Case "dbSubblocks_nil".
  simpl in H1. inversion H1; subst.
  destruct sbs2;try solve [auto | simpl in H10; inversion H10].
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
  simpl in H12.
  destruct sbs2 ; simpl in H12; inversion H12.
  clear H12.
  apply cmds2sbs_cons_inv in H4.
  destruct H4 as [cs21 [cs22 [cs212s [cs222sbs2 EQ]]]]; subst.
  inversion H9; subst. clear H9.  
  apply H with (S2:=S2)(Ps2:=Ps2)(cs2:=cs21) in H3; auto.
  assert (tv_subblocks sbs sbs2 lc2 gl2) as J. 
    admit. (*tv inclusion*)
  assert (uniq gl2 /\ uniq lc2) as J'.
    apply se_dbSubblock_preservation in d; auto.
  destruct J' as [Uniqg2 Uniqc2].
  apply H0 with (S2:=S2)(Ps2:=Ps2)(cs2:=cs22) in J; eauto.

Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  destruct B2 as [l2 ps2 cs2 tmn2].
  unfold tv_block in H13.
  remember (cmds2sbs (cs++cs')) as R1.
  remember (cmds2sbs cs2) as R2.
  destruct R1 as [sbs1 nbs1].
  destruct R2 as [sbs2 nbs2].
  destruct H13 as [EQ1 [Htv_phinodes [Htv_subblocks [Htv_cmds EQ2]]]]; subst.

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
  inversion H9; subst. clear H9.

  apply cmds_rcons2sbs_inv with (sbs:=sbs2)(nbs:=nbs2) in H13; auto.
  destruct H13; subst.
  assert (J:=Htv_subblocks).
  assert (moduleInSystem (module_intro TD Ps) S) as MinS.
    apply productInSystemModuleB_inv in H7.    
    destruct H7; auto.
  assert (moduleInSystem (module_intro TD Ps2) S2) as M2inS2.
    apply productInSystemModuleB_inv in H8.    
    destruct H8; auto.
  apply H with (S2:=S2)(Ps2:=Ps2)(cs2:=cs1) in J; auto.
  clear H.

  apply cmds2nbs__nbranchs2cmds in Hcs2nbs1. subst.
  apply cmds2nbs__nbranchs2cmds in Hcs32nbs2. subst.
  assert (tv_cmds nbs nbs2 lc2 gl2) as Htv_cmds'.
    admit. (*tv inclusion*)
  assert (uniq gl2 /\ uniq lc2) as J'.
    apply se_dbSubblocks_preservation in d; auto.
  destruct J' as [Uniqg2 Uniqc2].
  apply tv_cmds__is__correct with (nbs':=nbs2) in d0; auto.
  apply tv_terminator__is__correct with (B2:=block_intro l2 ps2 (cs1++nbranchs2cmds nbs2) tmn2)(fh2:=fh2)(lb2:=lb2) in d1; auto.
    destruct d1 as [B2' [n [Htv_block1'2' [J2 [J3 Hdb]]]]].
    exists B2'. exists n. 
    split; eauto.
    split; auto.
    split; auto.
      clear - Htv_block1'2'.
      admit. (*tv inclusion*)

    apply uniqSystem__uniqFdef with (S:=S)(M:=module_intro TD Ps); auto.
    apply uniqSystem__uniqFdef with (S:=S2)(M:=module_intro TD Ps2); auto.

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
  apply uniqSystem__uniqFdef in H5; auto.
  apply uniqSystem__uniqFdef in H6; auto.
  apply tv_blocks_nth_Some_inv with (n:=n)(B1:=block_intro l1' ps1' cs1' tmn1') in H11; auto.
  destruct H11 as [[l2 ps2 cs2 tmn2] [Hnth_error2 Htv_block]].
  exists l2. exists ps2. exists cs2. exists tmn2.
  exists l2. exists ps2. exists cs2. exists tmn2. 
  exists n.
  split; auto.

Case "dbBlocks_cons".
  inversion d; subst.
  assert (J:=H13).  
  assert (uniqF1:=H7).
  assert (uniqF2:=H8).
  apply uniqSystem__uniqFdef in uniqF1; auto.
  apply uniqSystem__uniqFdef in uniqF2; auto.
  apply tv_blocks_nth_Some_inv with (n:=n)(B1:=block_intro l1 ps1 (cs++cs') tmn1) in J; auto.
  destruct J as [[l2 ps2 cs2 tmn2] [Hnth_error2 Htv_block12]].
  assert (J:=Htv_block12).
  apply H with (S2:=S0)(Ps2:=Ps2)(fh3:=fh2)(lb3:=lb2)(fh2:=fh1)(lb2:=lb1)(Mem:=Mem0)(B1':=B')(lc':=lc4)(als':=als3)(gl':=gl3)(Mem':=Mem3)(als0:=als) in J; auto.
    destruct J as [B2' [n' [Hdb [J1 [J2 Htv_block12']]]]].
    clear H.
    destruct B' as [l3 ps3 cs3 tmn3].
    assert (tv_blocks lb1 lb2 lc4 gl3) as H.
      admit. (*tv inclusion*)    
    assert (uniq gl3 /\ uniq lc4) as J'.
      apply se_dbBlock_preservation in d; 
        eauto using productInSystemModuleB_nth_error__blockInSystemModuleFdef.
      destruct d as [L [M _]]; auto.
    destruct J' as [Uniqg3 Uniqc4].
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

    apply uniqFdef__wf_block with (fh:=fh2)(lb:=lb2)(n:=n); eauto using uniqSystem__uniqFdef.

Case "dbFdef_func".
    rewrite H1 in e. inversion e; subst. clear e.
    assert (exists lb2, lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
                        tv_blocks lb lb2 lc gl) as J.
      apply tv_products__lookupFdefViaIDFromProducts with (Ps1:=Ps); auto.
    destruct J as [lb2 [H10 H11]].
    assert (tv_blocks lb lb2 (initLocals la (params2GVs TD lp lc gl)) gl) as Htv_blocks.
      clear - H11.
      admit. (*tv inclusion*)      
    assert (uniq (initLocals la (params2GVs TD lp lc gl))) as uniqInitLocals.
      apply initLocals_uniq.
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
      destruct J; subst. clear H H12.

      assert (tv_subblocks sbs sbs2 lc1 gl1) as Htv_subblocks'.
        clear - Htv_subblocks.
        admit. (* inclusion *)
      assert (uniq gl1 /\ uniq lc1) as J'.
        apply se_dbBlocks_preservation in d; auto.
          destruct d as [U1 [U2 _]]; auto.
          apply productInSystemModuleB_nth_error__blockInSystemModuleFdef with (n:=0); 
            eauto using lookupFdefViaIDFromProductsInSystem.
      destruct J' as [Uniqg1 Uniqc1].
      assert (wf_subblocks sbs2 /\ wf_nbranchs nbs2) as J.
        apply uniqCmds___wf_subblocks_wf_nbranchs with (cs:=cs41++cs42); auto.
          clear - J6 J1 H10 H7 H3 H2 H5.
          apply se_dbBlocks_preservation in J6; auto using initLocals_uniq.
          destruct J6 as [uniqg1 [uinqc1 Bin]].
          apply blockInSystemModuleFdef_inv in Bin.
          destruct Bin as [J2 [J3 [J4 J5]]].
          apply uniqSystem__uniqFdef in J5; auto.

          apply blockInFdefB__exists_nth_error in J2.       
          destruct J2 as [n J2].
          apply uniqFdef__uniqBlock with (n:=n)(l1:=l2')(ps1:=ps2')(cs1:=cs41++cs42)(tmn1:=insn_return rid rt Result) in J5; auto.

          eapply productInSystemModuleB_nth_error__blockInSystemModuleFdef; 
            eauto using lookupFdefViaIDFromProductsInSystem.
      destruct J as [wf_sbs2 wf_nbs2].
      apply H0 with (S2:=S2)(Ps2:=Ps2)(cs2:=cs41) in Htv_subblocks'; auto.
        clear H0.

        apply cmds2nbranchs__nbranchs2cmds in Hcs22nbs1. subst.
        apply cmds2nbs__nbranchs2cmds in Hcs42nbs2. subst.
        assert (tv_cmds nbs nbs2 lc2 gl2) as Htv_cmds'.
          admit. (*tv inclusion*)
        assert (uniq gl2 /\ uniq lc2) as J'.
          apply se_dbSubblocks_preservation in Htv_subblocks'; auto.
        destruct J' as [Uniqg2 Uniqc2].
        apply tv_cmds__is__correct with (nbs':=nbs2) in d1; auto.
          apply dbFdef_func with (l1:=l3)(ps1:=ps3)(cs1:=cs3)(tmn1:=tmn2)(la:=la)(lb:=lb2)
            (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(als1:=als1)(l2:=l2')(ps2:=ps2')(cs21:=cs41)(cs22:=nbranchs2cmds nbs2)
            (lc3:=lc3)(als3:=als3)(gl3:=gl3)(Mem3:=Mem3)(lc2:=lc2)(als2:=als2)(gl2:=gl2)(Mem2:=Mem2); eauto.

      eapply lookupFdefViaIDFromProductsInSystem; eauto.
      eapply lookupFdefViaIDFromProductsInSystem; eauto.

      unfold tv_fdef.
      split; auto.
        clear - H11.
        admit. (*tv inclusion*)      

Case "dbFdef_proc".
    rewrite H1 in e. inversion e; subst. clear e.
    assert (exists lb2, lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
                        tv_blocks lb lb2 lc gl) as J.
      apply tv_products__lookupFdefViaIDFromProducts with (Ps1:=Ps); auto.
    destruct J as [lb2 [H10 H11]].
    assert (tv_blocks lb lb2 (initLocals la (params2GVs TD lp lc gl)) gl) as Htv_blocks.
      clear - H11.
      admit. (*tv inclusion*)      
    assert (uniq (initLocals la (params2GVs TD lp lc gl))) as uniqInitLocals.
      apply initLocals_uniq.
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
      destruct J; subst. clear H H12.

      assert (tv_subblocks sbs sbs2 lc1 gl1) as Htv_subblocks'.
        clear - Htv_subblocks.
        admit. (* inclusion *)
      assert (uniq gl1 /\ uniq lc1) as J'.
        apply se_dbBlocks_preservation in d; auto.
          destruct d as [U1 [U2 _]]; auto.
          apply productInSystemModuleB_nth_error__blockInSystemModuleFdef with (n:=0); 
            eauto using lookupFdefViaIDFromProductsInSystem.
      destruct J' as [Uniqg1 Uniqc1].
      assert (wf_subblocks sbs2 /\ wf_nbranchs nbs2) as J.
        apply uniqCmds___wf_subblocks_wf_nbranchs with (cs:=cs41++cs42); auto.
          clear - J6 J1 H10 H7 H3 H2 H5.
          apply se_dbBlocks_preservation in J6; auto using initLocals_uniq.
          destruct J6 as [uniqg1 [uinqc1 Bin]].
          apply blockInSystemModuleFdef_inv in Bin.
          destruct Bin as [J2 [J3 [J4 J5]]].
          apply uniqSystem__uniqFdef in J5; auto.

          apply blockInFdefB__exists_nth_error in J2.       
          destruct J2 as [n J2].
          apply uniqFdef__uniqBlock with (n:=n)(l1:=l2')(ps1:=ps2')(cs1:=cs41++cs42)(tmn1:=insn_return_void rid) in J5; auto.

          eapply productInSystemModuleB_nth_error__blockInSystemModuleFdef; 
            eauto using lookupFdefViaIDFromProductsInSystem.
      destruct J as [wf_sbs2 wf_nbs2].
      apply H0 with (S2:=S2)(Ps2:=Ps2)(cs2:=cs41) in Htv_subblocks'; auto.
        clear H0.

        apply cmds2nbranchs__nbranchs2cmds in Hcs22nbs1. subst.
        apply cmds2nbs__nbranchs2cmds in Hcs42nbs2. subst.
        assert (tv_cmds nbs nbs2 lc2 gl2) as Htv_cmds'.
          admit. (*tv inclusion*)
        assert (uniq gl2 /\ uniq lc2) as J'.
          apply se_dbSubblocks_preservation in Htv_subblocks'; auto.
        destruct J' as [Uniqg2 Uniqc2].
        apply tv_cmds__is__correct with (nbs':=nbs2) in d1; auto.
          apply dbFdef_proc with (l1:=l3)(ps1:=ps3)(cs1:=cs3)(tmn1:=tmn2)(la:=la)(lb:=lb2)
            (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(als1:=als1)(l2:=l2')(ps2:=ps2')(cs21:=cs41)(cs22:=nbranchs2cmds nbs2)
            (lc3:=lc3)(als3:=als3)(gl3:=gl3)(Mem3:=Mem3)(lc2:=lc2)(als2:=als2)(gl2:=gl2)(Mem2:=Mem2); eauto.

      eapply lookupFdefViaIDFromProductsInSystem; eauto.
      eapply lookupFdefViaIDFromProductsInSystem; eauto.

      unfold tv_fdef.
      split; auto.
        clear - H11.
        admit. (*tv inclusion*)      
Qed.   

Lemma tv_dbCall__is__correct : forall S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr S2 Ps2,
  dbCall S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr ->
  uniq gl ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
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
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
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
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
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
  uniqSystem S1 ->
  uniqSystem S2 ->
  productInSystemModuleB (product_fdef (fdef_intro fh1 lb1)) S1 (module_intro TD Ps1) ->
  productInSystemModuleB (product_fdef (fdef_intro fh2 lb2)) S2 (module_intro TD Ps2) ->
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
  uniq gl ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  productInSystemModuleB (product_fdef (fdef_intro fh1 lb1)) S1 (module_intro TD Ps1) ->
  productInSystemModuleB (product_fdef (fdef_intro fh2 lb2)) S2 (module_intro TD Ps2) ->
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
  uniq gl ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
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
  uniq gl ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
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
  apply llvmop_dbFdef__seop_dbFdef in H; auto.
  apply _tv_fdef__is__correct with (Ps2:=Ps2)(S2:=S2)(la:=la)(lb1:=lb1) in H; auto.
  destruct H as [lb2 [B2' [n [J1 [J2 [J3 [J4 [J5 J6]]]]]]]].
  exists lb2. exists B2'. exists n.
  repeat (split; auto).
    apply seop_dbFdef__llvmop_dbFdef; auto.
Qed.

Extraction "symexe" tv_blocks.

