Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
(*Add LoadPath "../../../theory/metatheory".*)
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
Require Import symexe_def.
Require Import symexe_complete.
Require Import symexe_sound.
Require Import seop_llvmop.
Require Import assoclist.
Require Import ssa_props.
Require Import symexe_dec.
Require Import Coq.Bool.Sumbool.

Export SimpleSE.

(* p&p *)
Lemma se_dbCmd_preservation : forall TD lc als gl Mem0 c lc' als' Mem' tr,
  dbCmd TD gl lc als Mem0 c lc' als' Mem' tr ->
  uniq lc ->
  uniq lc'.
Proof.
  intros TD lc als gl Mem0 c lc' als' Mem' tr HdbCmd Uniqlc.
  (dbCmd_cases (inversion HdbCmd) Case); subst; auto using updateAddAL_uniq.
  Case "dbSelect".
    destruct (isGVZero TD cond0); eauto using updateAddAL_uniq.
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
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq lc' .
Definition se_dbSubblock_preservation_prop S TD Ps fs gl lc als Mem cs lc' als' Mem' tr
  (db:dbSubblock S TD Ps fs gl lc als Mem cs lc' als' Mem' tr) :=
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq lc'.
Definition se_dbSubblocks_preservation_prop S TD Ps fs gl lc als Mem cs lc' als' Mem' tr
  (db:dbSubblocks S TD Ps fs gl lc als Mem cs lc' als' Mem' tr) :=
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq lc'.
Definition se_dbBlock_preservation_prop S TD Ps fs gl F arg state1 state2 tr
  (db:dbBlock S TD Ps fs gl F arg state1 state2 tr) :=
  forall B1 lc als Mem B1' lc' als' Mem',
  state1 = mkState (mkEC B1 lc als) Mem ->
  state2 = mkState (mkEC B1' lc' als') Mem' ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro TD Ps) F ->
  uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro TD Ps) F.
Definition se_dbBlocks_preservation_prop S TD Ps fs gl F lp state1 state2 tr
  (db:dbBlocks S TD Ps fs gl F lp state1 state2 tr) :=
  forall B1 lc als Mem B1' lc' als' Mem',
  state1 = (mkState (mkEC B1 lc als) Mem) ->
  state2 = (mkState (mkEC B1' lc' als') Mem') ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro TD Ps) F ->
  uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro TD Ps) F.
Definition se_dbFdef_preservation_prop fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr
  (db:dbFdef fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr) :=
  forall fid la lb,
  lookupFdefViaGV TD Ps gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq lc' /\ 
  blockInSystemModuleFdef B' S (module_intro TD Ps) (fdef_intro (fheader_intro rt fid la) lb).

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
         se_dbFdef_preservation_prop; intros; subst; auto.
Case "dbCall_internal".
  inversion d; subst.
    apply H in H3; auto. clear H.
    destruct H3 as [Huniqlc' Hblockin].
    unfold callUpdateLocals.
    destruct noret0; auto.
      destruct (rt=t=typ_void); auto.
        destruct (getOperandValue TD Result lc' gl); auto.
          apply updateAddAL_uniq; auto.

    apply H in H3; auto. clear H.
    destruct H3 as [Huniqlc' Hblockin].
    unfold callUpdateLocals.
    destruct noret0; auto.
      destruct (rt=t=typ_void); auto.

Case "dbCall_external".
  unfold exCallUpdateLocals.
  destruct noret0; auto.
  destruct (rt=t=typ_void); auto.
  destruct oresult; auto.
  apply updateAddAL_uniq; auto.

Case "dbSubblock_intro".
  apply se_dbCmds_preservation in d; auto.
 
Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  apply blockInSystemModuleFdef_inv in H4.
  destruct H4 as [Hblockin [Hinproducts [Hmodulein Hproductin]]].
  apply H in H2; auto.
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
  apply H with (B1:=block_intro l0 ps (cs++cs') tmn)(lc0:=lc)(als0:=als)(Mem:=Mem0) 
               (B1':=B')(lc':=lc4)(als':=als3)(Mem':=Mem3) in J; auto.
  clear H.
  destruct J as [uniqc4 B'in].
  eapply H0; eauto.

Case "dbFdef_func".
  rewrite e in H1. inversion H1; subst. clear H1.
  apply entryBlockInSystemBlockFdef' with (TD:=TD)(Ps:=Ps)(S:=S)(fv:=fv)(gl:=gl)(lc:=lc)(fs:=fs) in e0; auto.
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(lc0:=initLocals la0 (params2GVs TD lp lc gl))(als:=nil)(Mem:=Mem0)
               (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result))(lc':=lc1)(als':=als1)(Mem':=Mem1) in e0; auto using initLocals_uniq.
  clear H. destruct e0 as [uniqc1 Bin].
  apply H0 in uniqc1; auto. clear H0.
  apply se_dbCmds_preservation in d1; auto.

Case "dbFdef_proc".
  rewrite e in H1. inversion H1; subst. clear H1.
  apply entryBlockInSystemBlockFdef' with (TD:=TD)(Ps:=Ps)(S:=S)(fv:=fv)(gl:=gl)(lc:=lc)(fs:=fs) in e0; auto.
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(lc0:=initLocals la0 (params2GVs TD lp lc gl))(als:=nil)(Mem:=Mem0)
               (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return_void rid))(lc':=lc1)(als':=als1)(Mem':=Mem1) in e0; auto using initLocals_uniq.
  clear H. destruct e0 as [uniqc1 Bin].
  apply H0 in uniqc1; auto. clear H0.
  apply se_dbCmds_preservation in d1; auto.
Qed.

Lemma se_dbCall_preservation : forall S TD Ps fs lc gl Mem0 call0 lc' Mem' tr,
  dbCall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq lc' .
Proof.
  intros.
  destruct se_db_preservation as [J _].
  unfold se_dbCall_preservation_prop in J. eauto.
Qed.

Lemma se_dbSubblock_preservation : forall S TD Ps fs gl lc als Mem cs lc' als' Mem' tr,
  dbSubblock S TD Ps fs gl lc als Mem cs lc' als' Mem' tr ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq lc'.
Proof.
  intros.
  destruct se_db_preservation as [_ [J _]].
  unfold se_dbSubblock_preservation_prop in J. eauto.
Qed.

Lemma se_dbSubblocks_preservation : forall S TD Ps fs gl lc als Mem cs lc' als' Mem' tr,
  dbSubblocks S TD Ps fs gl lc als Mem cs lc' als' Mem' tr ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq lc'.
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [J _]]].
  unfold se_dbSubblocks_preservation_prop in J. eauto.
Qed.

Lemma se_dbBlock_preservation : forall S TD Ps fs gl F arg tr B1 lc als Mem B1' lc' als' Mem',
  dbBlock S TD Ps fs gl F arg 
    (mkState (mkEC B1 lc als) Mem) 
    (mkState (mkEC B1' lc' als') Mem') tr ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro TD Ps) F ->
  uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro TD Ps) F.
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [_ [J _]]]].
  unfold se_dbBlock_preservation_prop in J. eauto.
Qed.

Lemma se_dbBlocks_preservation : forall S TD Ps fs gl F lp tr B1 lc als Mem B1' lc' als' Mem',
  dbBlocks S TD Ps fs gl F lp 
    (mkState (mkEC B1 lc als) Mem)
    (mkState (mkEC B1' lc' als') Mem') tr ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro TD Ps) F ->
  uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro TD Ps) F.
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [_ [_ [J _]]]]].
  unfold se_dbBlocks_preservation_prop in J. eauto.
Qed.

Lemma se_dbFdef_preservation : forall fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr fid la lb,
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ->
  lookupFdefViaGV TD Ps gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  uniq lc' /\ 
  blockInSystemModuleFdef B' S (module_intro TD Ps) (fdef_intro (fheader_intro rt fid la) lb).
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [_ [_ [_ J]]]]].
  unfold se_dbFdef_preservation_prop in J. eauto.
Qed.

(* eqEnv *)

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

(* Correctness of the cmds validator *)


Tactic Notation "bdestruct" ident(H) "as" ident(J1) ident(J2) :=
     apply andb_true_iff in H; destruct H as [J1 J2].

Tactic Notation "bdestruct3" ident(H) "as" ident(J1) ident(J2) ident(J3) :=
     bdestruct H as H J3;
     bdestruct H as J1 J2.

Tactic Notation "bdestruct4" ident(H) "as" ident(J1) ident(J2) ident(J3) ident(J4) :=
     bdestruct3 H as H J3 J4;
     bdestruct H as J1 J2.

Tactic Notation "bdestruct5" ident(H) "as" ident(J1) ident(J2) ident(J3) ident(J4) ident(J5) :=
     bdestruct4 H as H J3 J4 J5;
     bdestruct H as J1 J2.

Ltac bdestructn H Js :=
  match Js with
  | nil => idtac
  | ?J::nil => rename H into J
  | ?J::?Js' => apply andb_true_iff in H; destruct H as [H J]; bdestructn H Js
  end.

Definition tv_cmds (nbs1 nbs2 : list nbranch) :=
sumbool2bool _ _ (sstate_dec (se_cmds sstate_init nbs1) (se_cmds sstate_init nbs2)).

Ltac sumbool_simpl :=
  repeat
  match goal with
  | [ H:sumbool2bool _ _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:is_true(sumbool2bool _ _ _) |- _ ] => apply sumbool2bool_true in H
  | [ H:tv_cmds _ _ = true |- _ ] => unfold is_true in H; apply sumbool2bool_true in H
  | [ H:is_true(tv_cmds _ _) |- _ ] => unfold is_true in H; apply sumbool2bool_true in H
  end.

Ltac sumbool_subst :=
  repeat
  match goal with
  | [ H:sumbool2bool _ _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:is_true(sumbool2bool _ _ _) |- _ ] => apply sumbool2bool_true in H; subst
  end.

Tactic Notation "sumbool_subst" "in" hyp(H) :=
  apply sumbool2bool_true in H.

Ltac bsplit :=
  eapply andb_true_iff; split.

Ltac repeat_bsplit :=
  repeat (bsplit; auto using eq_sumbool2bool_true).

Lemma tv_cmds__is__correct : forall TD nbs nbs' lc1 als1 gl Mem1 lc2 als2 Mem2 tr,
  uniq lc1 ->  
  wf_nbranchs nbs' ->
  tv_cmds nbs nbs' ->
  dbCmds TD gl lc1 als1 Mem1 (nbranchs2cmds nbs) lc2 als2 Mem2 tr ->
  exists slc,
    dbCmds TD gl lc1 als1 Mem1 (nbranchs2cmds nbs') slc als2 Mem2 tr /\
    eqAL _ slc lc2.
Proof.
  intros TD nbs nbs' lc1 als1 gl Mem1 lc2 als2 Mem2 tr Huniqc Wf Htv_cmds HdbCmds.
  assert (Uniqs:=HdbCmds).
  apply se_dbCmds_preservation in Uniqs; auto.
  apply op_cmds__satisfy__se_cmds in HdbCmds; auto.
  sumbool_simpl.
  rewrite Htv_cmds in HdbCmds.
  apply se_cmds__denote__op_cmds; auto.
Qed.

Definition tv_subblock (sb1 sb2:subblock) :=
match (sb1, sb2) with
| (mkSB nbs1 call1 iscall1, mkSB nbs2 call2 iscall2) =>
  let st1 := se_cmds sstate_init nbs1 in
  let st2 := se_cmds sstate_init nbs2 in
  let cl1 := se_call st1 call1 iscall1 in
  let cl2 := se_call st2 call2 iscall2 in
   (sumbool2bool _ _ (sstate_dec st1 st2)) &&
   (sumbool2bool _ _ (cmd_dec call1 call2))
end.

Fixpoint tv_subblocks (sbs1 sbs2:list subblock) :=
match (sbs1, sbs2) with
| (nil, nil) => true
| (sb1::sbs1', sb2::sbs2') => 
   (tv_subblock sb1 sb2) && (tv_subblocks sbs1' sbs2')
| _ => false
end.

Fixpoint tv_phinodes (ps1 ps2:phinodes) :=
match (ps1, ps2) with
| (nil, nil) => true
| (p1::ps1', p2::ps2') => 
    sumbool2bool _ _ (phinode_dec p1 p2) && tv_phinodes ps1' ps2'
| _ => false
end.

Definition tv_block (b1 b2:block) :=
match (b1, b2) with
| (block_intro l1 ps1 cs1 tmn1, block_intro l2 ps2 cs2 tmn2) =>
  match (cmds2sbs cs1, cmds2sbs cs2) with
  | ((sbs1, nbs1), (sbs2, nbs2)) =>
    sumbool2bool _ _ (eq_atom_dec l1 l2) &&
    tv_phinodes ps1 ps2 &&
    tv_subblocks sbs1 sbs2 &&
    tv_cmds nbs1 nbs2 &&
    sumbool2bool _ _ (terminator_dec tmn1 tmn2)
  end
end.

Fixpoint tv_blocks (bs1 bs2:blocks):=
match (bs1, bs2) with
| (nil, nil) => true
| (b1::bs1', b2::bs2') => tv_block b1 b2 && tv_blocks bs1' bs2'
| _ => false
end.

Definition tv_fdef (f1 f2:fdef) :=
match (f1, f2) with
| (fdef_intro fh1 lb1, fdef_intro fh2 lb2) =>
  sumbool2bool _ _ (fheader_dec fh1 fh2) &&
  tv_blocks lb1 lb2
end.

Fixpoint tv_products (Ps1 Ps2:products):=
match (Ps1, Ps2) with
| (nil, nil) => true
| (product_fdec f1::Ps1', product_fdec f2::Ps2') => 
  sumbool2bool _ _ (fdec_dec f1 f2) &&
  tv_products Ps1' Ps2'
| (product_fdef f1::Ps1', product_fdef f2::Ps2') => 
  tv_fdef f1 f2 && tv_products Ps1' Ps2'
| (product_gvar gvar1::Ps1', product_gvar gvar2::Ps2') => 
  sumbool2bool _ _ (gvar_dec gvar1 gvar2) &&
  tv_products Ps1' Ps2'
| _ => false
end.

Definition tv_module (m1 m2:module) :=
match (m1, m2) with
| (module_intro TD1 Ps1, module_intro TD2 Ps2) =>
  sumbool2bool _ _ (layouts_dec TD1 TD2) &&
  tv_products Ps1 Ps2
end.

Fixpoint tv_system (S1 S2:system) :=
match (S1, S2) with
| (nil, nil) => true
| (m1::S1', m2::S2') => tv_module m1 m2 && tv_system S1' S2'
| _ => false
end.

Lemma lookup_tv_blocks__tv_block : forall lb1 lb2 l0 B1,
  uniqBlocks lb1 ->
  uniqBlocks lb2 ->
  tv_blocks lb1 lb2 ->
  lookupAL _ (genLabel2Block_blocks lb1) l0 = Some B1 ->
  exists B2, exists n,
    tv_block B1 B2 /\
    nth_error lb1 n = Some B1 /\
    nth_error lb2 n = Some B2 /\
    lookupAL _ (genLabel2Block_blocks lb2) l0 = Some B2.
Proof.
  induction lb1; intros; simpl in *.
    inversion H2.

    destruct lb2.
      inversion H1.

      bdestruct H1 as J1 J2.
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
            bdestruct5 J1 as J11 J12 J13 J14 J15.
            sumbool_subst.
            destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l2); inversion H2; subst; auto.

        simpl_env in K. apply uniqBlocks_inv in K. destruct K.
        assert (K':=H0). apply uniqBlocks__uniqLabel2Block in K'.
        simpl_env in H0. apply uniqBlocks_inv in H0. destruct H0.
        apply IHlb1 with (lb2:=lb2) in H2; auto.
        destruct H2 as [B2 [n [H8 [H6 [H5 H7]]]]].
        exists B2. exists (S n). simpl. repeat (split; auto).
          apply mergeALs_app; auto.
Qed.        

Lemma tv_blocks_nth_Some_inv : forall lb1 lb2 n B1,
  uniqBlocks lb1 ->
  uniqBlocks lb2 ->
  tv_blocks lb1 lb2 ->
  nth_error lb1 n = Some B1 ->
  exists B2, 
    nth_error lb2 n = Some B2 /\ tv_block B1 B2.
Proof.
  intros lb1 lb2 n B1 H H0 H1 H2.
  assert (J:=H2).
  apply nth_error__lookupAL_genLabel2Block_blocks in H2; auto.
  destruct H2 as [l0 H2].
  apply lookup_tv_blocks__tv_block with (l0:=l0)(B1:=B1) in H1; auto.
  destruct H1 as [B2 [n' [J1 [J2 [J3 J4]]]]].
  apply uniqBlocks__uniq_nth_error with (n':=n) in J2; auto.
  subst.
  exists B2. split; auto.
Qed.

Lemma lookup_tv_fdef__tv_block : forall fh1 fh2 lb1 lb2 l0 B1,
  uniqBlocks lb1 ->
  uniqBlocks lb2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) ->
  lookupBlockViaLabelFromFdef (fdef_intro fh1 lb1) l0 = Some B1 ->
  exists B2, exists n,
    tv_block B1 B2 /\
    nth_error lb1 n = Some B1 /\
    nth_error lb2 n = Some B2 /\
    lookupBlockViaLabelFromFdef (fdef_intro fh2 lb2) l0 = Some B2.
Proof.
  intros fh1 fh2 lb1 lb2 l0 B1 H H0 H1 H2.
  bdestruct H1 as EQ Htv_blocks.
  sumbool_subst.
  unfold lookupBlockViaLabelFromFdef in H2.
  unfold genLabel2Block_fdef in H2.
  eapply lookup_tv_blocks__tv_block; eauto.
Qed.

Lemma tv_block__inv : forall B1 B2,
  tv_block B1 B2 ->
  getBlockLabel B1 = getBlockLabel B2 /\
  tv_phinodes (getPhiNodesFromBlock B1) (getPhiNodesFromBlock B2) /\
  getTerminatorFromBlock B1 = getTerminatorFromBlock B2.
Proof.
  intros B1 B2 H.
  destruct B1.
  destruct B2. simpl in *.
  unfold tv_block in H.
  destruct (cmds2sbs c).
  destruct (cmds2sbs c0).
  bdestruct5 H as J1 J2 J3 J4 J5.
  sumbool_subst.
  split; auto.
Qed.
 
Lemma tv_getIncomingValuesForBlockFromPHINodes : forall ps1 TD B1 ps2 B2,
  tv_block B1 B2 ->
  tv_phinodes ps1 ps2 ->
  getIncomingValuesForBlockFromPHINodes TD ps1 B1 =
  getIncomingValuesForBlockFromPHINodes TD ps2 B2 .
Proof.
  induction ps1; intros TD B1 ps2 B2 H H0.
    destruct ps2; simpl in *; auto.
      inversion H0.

    destruct ps2; simpl in *.
      inversion H0.

      bdestruct H0 as J1 H1.
      sumbool_subst.
      apply IHps1 with (B1:=B1)(B2:=B2) (TD:=TD) in H1; auto.
      rewrite H1.
      apply tv_block__inv in H.
      destruct H as [H _].
      destruct B1.
      destruct B2.
      simpl in *. subst.
      destruct p. simpl. auto.
Qed.     

Lemma tv_switchToNewBasicBlock : forall TD l1 ps1 sbs1 tmn1 B1 l2 ps2 sbs2 tmn2 B2 lc gl,
  tv_block B1 B2 ->
  tv_block (block_intro l1 ps1 sbs1 tmn1) (block_intro l2 ps2 sbs2 tmn2) ->
  switchToNewBasicBlock TD (block_intro l1 ps1 sbs1 tmn1) B1 gl lc =
  switchToNewBasicBlock TD (block_intro l2 ps2 sbs2 tmn2) B2 gl lc.
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
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) ->
  tv_block B1 B2 ->
  dbTerminator TD (fdef_intro fh1 lb1) gl B1 lc tmn B1' lc' tr ->
  exists B2', exists n,
    tv_block B1' B2' /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    dbTerminator TD (fdef_intro fh2 lb2) gl B2 lc tmn B2' lc' tr.
Proof.
  intros TD fh1 lb1 fh2 lb2 B1 B2 lc gl tmn B1' lc' tr HuniqF1 HuniqF2 Htv_fdef Htv_block HdbTerminator.
  inversion HdbTerminator; subst.
    remember (isGVZero TD c) as R.
    destruct R; subst.
      assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' /\ 
                                  nth_error lb1 n = Some (block_intro l' ps' sbs' tmn') /\
                                  nth_error lb2 n = Some B2' /\
                                  lookupBlockViaLabelFromFdef (fdef_intro fh2 lb2) l2 = Some B2') as J.
        eapply lookup_tv_fdef__tv_block; eauto.
      destruct J as [B2' [n [J1 [J2 [J3 J4]]]]].
      exists B2'. exists n. split; auto. split; auto. split; auto.
      destruct B2' as [l2' ps2' sbs2' tmn2'].
      eapply dbBranch; eauto.
        rewrite <- HeqR. auto.
        eapply tv_switchToNewBasicBlock; eauto.
    
      assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' /\ 
                                  nth_error lb1 n = Some (block_intro l' ps' sbs' tmn') /\
                                  nth_error lb2 n = Some B2' /\
                                  lookupBlockViaLabelFromFdef (fdef_intro fh2 lb2) l1 = Some B2') as J.
        eapply lookup_tv_fdef__tv_block; eauto.
      destruct J as [B2' [n' [J1 [J2 [J3 J4]]]]].
      exists B2'. exists n'. split; auto. split; auto. split; auto.
      destruct B2' as [l2' ps2' sbs2' tmn2'].
      apply dbBranch with (c:=c); auto.
        rewrite <- HeqR. auto.
        eapply tv_switchToNewBasicBlock; eauto.

    assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' /\ 
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

Lemma tv_products__lookupFdefViaIDFromProducts : forall Ps1 Ps2 fid rt la lb1,
  tv_products Ps1 Ps2 ->
  lookupFdefViaIDFromProducts Ps1 fid = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  exists lb2,
    lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2.
Proof.
  induction Ps1; intros.
    destruct Ps2; inversion H.
      inversion H0.

    (product_cases (destruct a) Case); simpl in H.
    Case "product_gvar".
      destruct Ps2; try solve [inversion H].
      simpl in H0.
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.
      apply IHPs1 with (fid:=fid)(rt:=rt)(la:=la)(lb1:=lb1) in H2; auto.
 
    Case "product_fdec".
      destruct Ps2; try solve [inversion H].
      simpl in H0.
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.
      apply IHPs1 with (fid:=fid)(rt:=rt)(la:=la)(lb1:=lb1) in H2; auto.

    Case "product_fdef".
      destruct Ps2; try solve [inversion H].
      simpl in *.
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.    
      simpl in *.
      destruct f.
      destruct f0.
      unfold tv_fdef in H1.
      bdestruct H1 as EQ H1.
      sumbool_subst.
      simpl in *.
      remember (getFheaderID f0) as R.
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) R fid); subst.
        inversion H0. subst b. 
        exists b0. split; auto.

        apply IHPs1 with (Ps2:=Ps2) in H0; auto.

    Case "product_namedt".
      inversion H.
Qed.

Lemma tv_products__lookupFdefViaGV : forall Ps1 Ps2 fv fid rt la lb1 TD gl lc fs,
  tv_products Ps1 Ps2 ->
  lookupFdefViaGV TD Ps1 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  exists lb2,
    lookupFdefViaGV TD Ps2 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2.
Proof.
  intros.
  unfold lookupFdefViaGV in *.
  destruct (getOperandValue TD fv lc gl); try solve [inversion H0].
  destruct (lookupFdefViaGVFromFunTable fs g); try solve [inversion H0].
  assert (J:=H0). 
  apply lookupFdefViaIDFromProducts_ideq in J; subst.
  eapply tv_products__lookupFdefViaIDFromProducts; eauto.
Qed.

Lemma tv_products__lookupFdecViaIDFromProducts : forall Ps1 Ps2 fid,
  tv_products Ps1 Ps2 ->
  lookupFdecViaIDFromProducts Ps1 fid = lookupFdecViaIDFromProducts Ps2 fid.
Proof.
  induction Ps1; intros.
    destruct Ps2; inversion H; auto.

    (product_cases (destruct a) Case); simpl in H.
    Case "product_gvar".
      destruct Ps2; try solve [inversion H].
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.
      apply IHPs1 with (fid:=fid) in H2; auto.
 
    Case "product_fdec".
      destruct Ps2; try solve [inversion H].
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.
      sumbool_subst.
      simpl.
      rewrite IHPs1 with (Ps2:=Ps2); auto.

    Case "product_fdef".
      destruct Ps2; try solve [inversion H].
      simpl in *.
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.    
      simpl in *.
      rewrite IHPs1 with (Ps2:=Ps2); auto.

    Case "product_namedt".
      inversion H.
Qed.

Lemma tv_products__lookupFdefViaIDFromProducts_None : forall Ps1 Ps2 fid,
  tv_products Ps1 Ps2 ->
  lookupFdefViaIDFromProducts Ps1 fid = None ->
  lookupFdefViaIDFromProducts Ps2 fid = None.
Proof.
  induction Ps1; intros.
    destruct Ps2; inversion H; auto.

    (product_cases (destruct a) Case); simpl in H.
    Case "product_gvar".
      destruct Ps2; try solve [inversion H].
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.
      apply IHPs1 with (fid:=fid) in H2; auto.
 
    Case "product_fdec".
      destruct Ps2; try solve [inversion H].
      simpl in *.
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.    
      simpl in *.
      rewrite IHPs1 with (Ps2:=Ps2); auto.

    Case "product_fdef".
      destruct Ps2; try solve [inversion H].
      destruct p; try solve [inversion H].
      bdestruct H as H1 H2.
      destruct f. destruct f0.
      destruct f. destruct f0.
      unfold tv_fdef in H1.
      bdestruct H1 as H1 H3.
      sumbool_subst.
      inversion H1; subst.
      simpl in *.
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) i1 fid); subst; auto.
        inversion H0.      

    Case "product_namedt".
      inversion H.
Qed.

Lemma tv_products__lookupFdefViaGV_None : forall Ps1 Ps2 fv TD gl lc fs,
  tv_products Ps1 Ps2 ->
  lookupFdefViaGV TD Ps1 gl lc fs fv = None ->
  lookupFdefViaGV TD Ps2 gl lc fs fv = None.
Proof.
  intros.
  unfold lookupFdefViaGV in *.
  destruct (getOperandValue TD fv lc gl); auto.
  destruct (lookupFdefViaGVFromFunTable fs g); auto.
  eapply tv_products__lookupFdefViaIDFromProducts_None; eauto.
Qed.

Lemma tv_products__lookupExFdecViaGV : forall Ps1 Ps2 TD gl lc fs fv,
  tv_products Ps1 Ps2 ->
  lookupExFdecViaGV TD Ps1 gl lc fs fv = lookupExFdecViaGV TD Ps2 gl lc fs fv.
Proof.
  intros.
  unfold lookupExFdecViaGV.
  destruct (getOperandValue TD fv lc gl); auto.
  destruct (lookupFdefViaGVFromFunTable fs g); auto.
  remember (lookupFdefViaIDFromProducts Ps1 i0) as R.
  symmetry in HeqR.
  destruct R.  
    destruct f. destruct f.
    assert (H1:=HeqR).
    apply lookupFdefViaIDFromProducts_ideq in H1; subst.
    apply tv_products__lookupFdefViaIDFromProducts with (Ps2:=Ps2) in HeqR; auto.
    destruct HeqR as [lb2 [J1 J2]].
    rewrite J1. auto.

    apply tv_products__lookupFdefViaIDFromProducts_None with (Ps2:=Ps2) in HeqR; auto.
    rewrite HeqR.
    apply tv_products__lookupFdecViaIDFromProducts; auto.
Qed.

Definition tv_dbCall__is__correct_prop S1 TD Ps1 fs gl lc Mem0 call0 lc' Mem' tr
  (db:dbCall S1 TD Ps1 fs gl lc Mem0 call0 lc' Mem' tr) :=
  forall S2 Ps2,
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists slc, 
    dbCall S2 TD Ps2 fs gl lc Mem0 call0 slc Mem' tr /\
    eqAL _ slc lc'.
Definition tv_subblock__is__correct_prop S1 TD Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr
  (db:dbSubblock S1 TD Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr) :=
  forall S2 Ps2 cs2 sb1 sb2,
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
  tv_subblock sb1 sb2 ->
  exists slc,
    dbSubblock S2 TD Ps2 fs gl lc als Mem cs2 slc als' Mem' tr /\
    eqAL _ slc lc'.
Definition tv_subblocks__is__correct_prop S1 TD Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr
  (db:dbSubblocks S1 TD Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr) :=
  forall S2 Ps2 sbs1 sbs2 cs2,
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
  tv_subblocks sbs1 sbs2 ->
  exists slc,
    dbSubblocks S2 TD Ps2 fs gl lc als Mem cs2 slc als' Mem' tr /\
    eqAL _ slc lc'.
Definition tv_block__is__correct_prop S1 TD Ps1 fs gl F1 arg state1 state2 tr
  (db:dbBlock S1 TD Ps1 fs gl F1 arg state1 state2 tr) :=
  forall S2 Ps2 fh1 lb1 fh2 lb2 B1 lc als Mem B1' lc' als' Mem' B2,
  state1 = mkState (mkEC B1 lc als) Mem ->
  state2 = mkState (mkEC B1' lc' als') Mem' ->
  F1 = fdef_intro fh1 lb1 ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  productInSystemModuleB (product_fdef (fdef_intro fh1 lb1)) S1 (module_intro TD Ps1) ->
  productInSystemModuleB (product_fdef (fdef_intro fh2 lb2)) S2 (module_intro TD Ps2) ->
  wf_block B2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) ->
  tv_block B1 B2 ->
  exists B2', exists n,
  exists slc, 
    dbBlock S2 TD Ps2 fs gl (fdef_intro fh2 lb2) arg 
      (mkState (mkEC B2 lc als) Mem) 
      (mkState (mkEC B2' slc als') Mem')
      tr /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' /\
    eqAL _ slc lc'.
Definition tv_blocks__is__correct_prop S1 TD Ps1 fs gl F1 lp state1 state2 tr
  (db:dbBlocks S1 TD Ps1 fs gl F1 lp state1 state2 tr) :=
  forall S2 Ps2 fh1 lb1 fh2 lb2 lc n tmn1
                            l1 ps1 cs1 ps1' l1' als
                            lc' Mem Mem' als' tmn1' cs1',
  state1 = (mkState (mkEC (block_intro l1 ps1 cs1 tmn1) lc als) Mem) ->
  state2 = (mkState (mkEC (block_intro l1' ps1' cs1' tmn1') lc' als') Mem') ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  productInSystemModuleB (product_fdef (fdef_intro fh1 lb1)) S1 (module_intro TD Ps1) ->
  productInSystemModuleB (product_fdef (fdef_intro fh2 lb2)) S2 (module_intro TD Ps2) ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  F1 = fdef_intro fh1 lb1 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) ->
  tv_blocks lb1 lb2 ->
  nth_error lb1 n = Some (block_intro l1 ps1 cs1 tmn1) ->
  exists l2, exists ps2, exists cs2, exists tmn2, 
  exists l2', exists ps2', exists cs2', exists tmn2', exists n',
  exists slc, 
    nth_error lb2 n = Some (block_intro l2 ps2 cs2 tmn2) /\
    nth_error lb1 n' = Some (block_intro l1' ps1' cs1' tmn1') /\
    nth_error lb2 n' = Some (block_intro l2' ps2' cs2' tmn2') /\
    tv_block (block_intro l1 ps1 cs1 tmn1) (block_intro l2 ps2 cs2 tmn2) /\
    tv_block (block_intro l1' ps1' cs1' tmn1') (block_intro l2' ps2' cs2' tmn2') /\
    dbBlocks S2 TD Ps2 fs gl (fdef_intro fh2 lb2) lp
      (mkState (mkEC (block_intro l2 ps2 cs2 tmn2) lc als) Mem)
      (mkState (mkEC (block_intro l2' ps2' cs2' tmn2') slc als') Mem')
      tr /\
    eqAL _ slc lc'.
Definition tv_fdef__is__correct_prop fv rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B1' Rid oResult tr
  (db:dbFdef fv rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B1' Rid oResult tr) :=
  forall fid Ps2 S2 la lb1,
  lookupFdefViaGV TD Ps1 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists lb2, exists B2', exists n,
  exists slc, 
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' /\
    lookupFdefViaGV TD Ps2 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2 /\
    dbFdef fv rt lp S2 TD Ps2 lc gl fs Mem slc als' Mem' B2' Rid oResult tr /\
    eqAL _ slc lc'.

Lemma tv__is__correct :
  (forall S1 TD Ps1 fs gl lc Mem0 call0 lc' Mem' tr db, 
     tv_dbCall__is__correct_prop S1 TD Ps1 fs gl lc Mem0 call0 lc' Mem' tr db) /\
  (forall S1 TD Ps1 fs gl lc als Mem sb1 lc' als' Mem' tr db,
     tv_subblock__is__correct_prop S1 TD Ps1 fs gl lc als Mem sb1 lc' als' Mem' tr db) /\
  (forall S1 TD Ps1 fs gl lc als Mem sbs1 lc' als' Mem' tr db,
     tv_subblocks__is__correct_prop S1 TD Ps1 fs gl lc als Mem sbs1 lc' als' Mem' tr db) /\
  (forall S1 TD Ps1 fs gl F1 arg state1 state2 tr db,
     tv_block__is__correct_prop S1 TD Ps1 fs gl F1 arg state1 state2 tr db) /\
  (forall S1 TD Ps1 fs gl F1 lp state1 state2 tr db,
     tv_blocks__is__correct_prop S1 TD Ps1 fs gl F1 lp state1 state2 tr db) /\
  (forall fv rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B' Rid oResult tr db,
     tv_fdef__is__correct_prop fv rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B' Rid oResult tr db).
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
         tv_fdef__is__correct_prop.
Case "dbCall_internal".
  intros S TD Ps lc gl fs rid noret0 tailc0 rt fid lp Rid oResult tr lc' Mem0 Mem' 
         als' Mem'' B' d H e S2 Ps2 H0 H1 H2 H3 H4 H5 H6.
  inversion d; subst.
    apply H with (S2:=S2)(Ps2:=Ps2) in H7; auto.
    clear H.
    destruct H7 as [lb2 [B2' [n [slc [J1 [J2 [J3 [J4 [J5 [J6 HeqEnv]]]]]]]]]].
    exists (callUpdateLocals TD noret0 rid rt (Some Result) lc slc gl).
    split; eauto using eqAL_callUpdateLocals, eqAL_refl.

    apply H with (S2:=S2)(Ps2:=Ps2) in H7; auto.
    clear H.
    destruct H7 as [lb2 [B2' [n [slc [J1 [J2 [J3 [J4 [J5 [J6 HeqEnv]]]]]]]]]].
    exists (callUpdateLocals TD noret0 rid rt None lc slc gl).
    split; eauto using eqAL_callUpdateLocals, eqAL_refl.

Case "dbCall_external".
  intros S TD Ps lc gl fs rid noret0 tailc0 fv fid lp rt la Mem0 oresult Mem'
         H S2 Ps2 H0 H1 H2 H3 H4 H5 H6.
  exists (exCallUpdateLocals noret0 rid rt oresult lc).
  split; auto using eqAL_exCallUpdateLocals, eqAL_refl.
    apply dbCall_external with (fid:=fid)(la:=la); auto.
      rewrite <- tv_products__lookupExFdecViaGV with (Ps1:=Ps); auto.

Case "dbSubblock_intro".
  intros S TD Ps lc1 als1 gl fs Mem1 cs call0 lc2 als2 Mem2 tr1 lc3 Mem3 tr2 d d0 H S2 
         Ps2 cs2 sb1 sb2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  unfold tv_subblock in H10.
  destruct sb1.
  destruct sb2.
  apply cmds2sb_inv in H1.
  destruct H1 as [cs' [call1 [J1 [J2 J3]]]].
  apply cmds2nbs__nbranchs2cmds in J2.
  apply app_inj_tail in J1.
  destruct J1; subst.
  apply cmds2sb_inv in H2.
  destruct H2 as [cs2' [call0 [J1 [J2 J3]]]]; subst.
  apply cmds2nbs__nbranchs2cmds in J2.
  bdestruct H10 as EQ1 EQ2.
  sumbool_subst.
  inversion H7; subst.
  assert (uniq lc2) as J.
    apply se_dbCmds_preservation in d; auto.
  apply tv_cmds__is__correct with (nbs':=NBs1) in d; 
    try solve [eauto using eq_sumbool2bool_true | apply eq_sumbool2bool_true; auto].
  destruct d as [lc2' [Hcmds Heq2]].
  apply H in H6; auto. clear H.
  destruct H6 as [lc3' [HdbCall Heq3]].  
  apply dbCall_eqEnv with (lc1':=lc2') in HdbCall; auto using eqAL_sym.
  destruct HdbCall as [lc3'' [HdbCall Heq3']].
  exists lc3''. split; eauto using eqAL_trans, eqAL_sym.

Case "dbSubblocks_nil".
  intros S TD Ps lc als gl fs Mem0 S2 Ps2 sbs1 sbs2 cs2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
  simpl in H0. inversion H0; subst.
  destruct sbs2;try solve [auto | simpl in H9; inversion H9].
    apply cmds2sbs_nil_inv in H1; subst.
    exists lc. split; auto using eqAL_refl.

Case "dbSubblocks_cons".
  intros S TD Ps lc1 als1 gl fs Mem1 lc2 als2 Mem2 lc3 als3 Mem3 cs cs' t1 t2 d H d0 H0 S2
         Ps2 sbs1 sbs2 cs2 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
  assert (Hcs2sb := d).
  apply dbSubblock__cmds2sb in Hcs2sb.
  destruct Hcs2sb as [sb Hcs2sb].
  assert (Hcs'2sbs := d0).
  apply dbSubblocks__cmds2sbs in Hcs'2sbs.
  destruct Hcs'2sbs as [sbs Hcs'2sbs].
  apply cmds_cons2sbs_inv with (sb:=sb)(sbs':=sbs) in H2; auto.
  subst.
  simpl in H11.
  destruct sbs2 ; try solve [inversion H11].
  bdestruct H11 as H2 H12.
  apply cmds2sbs_cons_inv in H3.
  destruct H3 as [cs21 [cs22 [cs212s [cs222sbs2 EQ]]]]; subst.
  inversion_clear H8; subst.
  apply H with (S2:=S2)(Ps2:=Ps2)(cs2:=cs21) in H2; auto.
  clear H. destruct H2 as [lc2' [HdbSubblock Heq2]].
  assert (uniq lc2) as Uniqc2.
    apply se_dbSubblock_preservation in d; auto.
  apply H0 with (S2:=S2)(Ps2:=Ps2)(cs2:=cs22) in H12; auto.
  clear H0. destruct H12 as [lc3' [HdbSubblocks Heq3]].
  apply dbSubblocks_eqEnv with (lc1':=lc2') in HdbSubblocks; auto using eqAL_sym.
  destruct HdbSubblocks as [lc3'' [HdbSubblocks Heq3']].
  exists lc3''. split; eauto using eqAL_trans, eqAL_sym.

Case "dbBlock_intro".
  intros S TD Ps F tr1 tr2 l0 ps cs cs' tmn gl fs lc1 als1 Mem1 lc2 als2 Mem2 lc3 als3 Mem3 lc4 B' arg0 tr3 d H d0 d1
         S2 Ps2 fh1 lb1 fh2 lb2 B1 lc als Mem0 B1' lc' als' Mem' B2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12; subst.
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  destruct B2 as [l2 ps2 cs2 tmn2].
  unfold tv_block in H12.
  remember (cmds2sbs (cs++cs')) as R1.
  remember (cmds2sbs cs2) as R2.
  destruct R1 as [sbs1 nbs1].
  destruct R2 as [sbs2 nbs2].
  bdestruct5 H12 as EQ1 Htv_phinodes Htv_subblocks Htv_cmds EQ2.
  sumbool_subst.

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
  inversion H8; subst. clear H8.

  apply cmds_rcons2sbs_inv with (sbs:=sbs2)(nbs:=nbs2) in H12; auto.
  destruct H12; subst.
  assert (J:=Htv_subblocks).
  assert (moduleInSystem (module_intro TD Ps) S) as MinS.
    apply productInSystemModuleB_inv in H6.    
    destruct H6; auto.
  assert (moduleInSystem (module_intro TD Ps2) S2) as M2inS2.
    apply productInSystemModuleB_inv in H7.    
    destruct H7; auto.
  apply H with (S2:=S2)(Ps2:=Ps2)(cs2:=cs1) in J; auto.
  clear H.
  destruct J as [lc2' [Hsubblocks Heq2]].

  apply cmds2nbs__nbranchs2cmds in Hcs2nbs1. subst.
  apply cmds2nbs__nbranchs2cmds in Hcs32nbs2. subst.
  assert (uniq lc2) as Uniqc2.
    apply se_dbSubblocks_preservation in d; auto.
  apply tv_cmds__is__correct with (nbs':=nbs2) in d0; auto.
  destruct d0 as [lc3' [HdbCmds Heq3]].
  apply tv_terminator__is__correct with (B2:=block_intro l2 ps2 (cs1++nbranchs2cmds nbs2) tmn2)(fh2:=fh2)(lb2:=lb2) in d1; auto.
    destruct d1 as [B2' [n [Htv_block1'2' [J2 [J3 Hdb]]]]].
    exists B2'. exists n. 
    
    apply dbCmds_eqEnv with (lc1':=lc2') in HdbCmds; auto using eqAL_sym.
    destruct HdbCmds as [lc2'' [HdbCmds Heq2']].

    apply dbTerminator_eqEnv with (lc1':=lc2'') in Hdb; eauto using eqAL_sym, eqAL_trans.
    destruct Hdb as [lc3'' [HdbTerminator Heq3']].

    exists lc3''. 
    split; eauto using eqAL_trans, eqAL_sym.

    apply uniqSystem__uniqFdef with (S:=S)(M:=module_intro TD Ps); auto.
    apply uniqSystem__uniqFdef with (S:=S2)(M:=module_intro TD Ps2); auto.

    unfold tv_block.
    rewrite <- HeqR1.
    rewrite <- HeqR2.
    repeat_bsplit.

Case "dbBlocks_nil".
  intros S TD Ps fs gl F arg0 state S2 Ps2 fh1 lb1 fh2 lb2 lc n tmn1 l1 ps1 cs1
         ps1' l1' als lc' Mem0 Mem' als' tmn1' cs1' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11; subst.
  inversion H0; subst. clear H0.
  apply uniqSystem__uniqFdef in H4; auto.
  apply uniqSystem__uniqFdef in H5; auto.
  apply tv_blocks_nth_Some_inv with (n:=n)(B1:=block_intro l1' ps1' cs1' tmn1') in H10; auto.
  destruct H10 as [[l2 ps2 cs2 tmn2] [Hnth_error2 Htv_block]].
  exists l2. exists ps2. exists cs2. exists tmn2.
  exists l2. exists ps2. exists cs2. exists tmn2. 
  exists n. exists lc'.
  repeat (split; auto).

Case "dbBlocks_cons".
  intros S TD Ps fs gl F arg0 S1 S2 S3 t1 t2 d H d0 H0 S0 Ps2 fh1 lb1 fh2 lb2 lc n tmn1 l1
         ps1 cs1 ps1' l1' als lc' Mem0 Mem' als' tmn1' cs1' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13; subst.
  inversion d; subst.
  assert (J:=H12).  
  assert (uniqF1:=H6).
  assert (uniqF2:=H7).
  apply uniqSystem__uniqFdef in uniqF1; auto.
  apply uniqSystem__uniqFdef in uniqF2; auto.
  apply tv_blocks_nth_Some_inv with (n:=n)(B1:=block_intro l1 ps1 (cs++cs') tmn1) in J; auto.
  destruct J as [[l2 ps2 cs2 tmn2] [Hnth_error2 Htv_block12]].
  assert (J:=Htv_block12).
  apply H with (S2:=S0)(Ps2:=Ps2)(fh3:=fh2)(lb3:=lb2)(fh2:=fh1)(lb2:=lb1)(Mem:=Mem0)(B1':=B')(lc':=lc4)(als':=als3)(Mem':=Mem3)(als0:=als)(lc0:=lc) in J; auto.
    destruct J as [B2' [n' [lc4' [Hdb [J1 [J2 [Htv_block12' Heq4]]]]]]].
    clear H.
    destruct B' as [l3 ps3 cs3 tmn3].
    assert (uniq lc4) as Uniqc4.
      apply se_dbBlock_preservation in d; 
        eauto using productInSystemModuleB_nth_error__blockInSystemModuleFdef.
      destruct d as [L _]; auto.
    apply H0 with (S2:=S0)(Ps2:=Ps2)(fh2:=fh1)(fh3:=fh2)(n:=n')(tmn1:=tmn3) (lc:=lc4)
      (l1:=l3)(ps1:=ps3)(cs1:=cs3)(ps1'0:=ps1')(l1'0:=l1')(als:=als3)(lc'0:=lc')
      (Mem:=Mem3)(Mem'0:=Mem')(als'0:=als')(tmn1'0:=tmn1')(cs1'0:=cs1') in H12; auto.
    destruct H12 as [l4 [ps4 [cs4 [tmn4 [l4' [ps4' [cs4' [tmn4' [n'' [lc2' [J3 [J4 [J5 [J6 [J7 [J8 Heq2]]]]]]]]]]]]]]]].
    clear H0.

    apply dbBlocks_eqEnv with (lc1':=lc4') in J8; auto using eqAL_sym.
    destruct J8 as [lc2'' [HdbBlocks Heq2']].

    exists l2. exists ps2. exists cs2. exists tmn2.
    exists l4'. exists ps4'. exists cs4'. exists tmn4'.
    exists n''. exists lc2''.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.

    rewrite J2 in J3.
    inversion J3; subst. clear J3.
    split; eauto using eqAL_sym, eqAL_trans.

    apply uniqFdef__wf_block with (fh:=fh2)(lb:=lb2)(n:=n); eauto using uniqSystem__uniqFdef.

Case "dbFdef_func".
    intros S TD Ps gl fs fv fid lp lc rid l1 ps1 cs1 tmn1 rt la lb Result lc1 tr1 Mem0 Mem1 als1
           l2 ps2 cs21 cs22 lc2 als2 Mem2 tr2 lc3 als3 Mem3 tr3 e e0 d H d0 H0 d1
           fid0 Ps2 S2 la0 lb1 H1 H2 H3 H4 H5 H6 H7 H8.
    rewrite H1 in e. inversion e; subst. clear e.
    assert (exists lb2, lookupFdefViaGV TD Ps2 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
                        tv_blocks lb lb2) as J.
      apply tv_products__lookupFdefViaGV with (Ps1:=Ps); auto.
    destruct J as [lb2 [H10 H11]].
    assert (uniq (initLocals la (params2GVs TD lp lc gl))) as uniqInitLocals.
      apply initLocals_uniq.
    assert (Htv_blocks:=H11).
    apply H with (S2:=S2)(Ps2:=Ps2)(fh1:=fheader_intro rt fid la)(fh2:=fheader_intro rt fid la)(n:=0)
      (ps1':=ps2)(l1':=l2)(als:=nil)(lc':=lc1) (lc0:=initLocals la (params2GVs TD lp lc gl))
      (Mem:=Mem0)(Mem':=Mem1)(als':=als1)(tmn1':=insn_return rid rt Result)(cs1':=cs21++cs22) 
      (ps3:=ps1)(cs2:=cs1)(tmn2:=tmn1)(l3:=l1)in H11; auto.
      clear H.
      destruct H11 as [l3 [ps3 [cs3 [tmn2 [l2' [ps2' [cs2' [tmn2' [n' [lc1' [J1 [J2 [J3 [J4 [J5 [J6 Heq1]]]]]]]]]]]]]]]].

      exists lb2. exists (block_intro l2' ps2' cs2' tmn2'). exists n'.

      assert (J5':=J5).
      unfold tv_block in J5.
      remember (cmds2sbs (cs21++cs22)) as R1.
      remember (cmds2sbs cs2') as R2.
      destruct R1 as [sbs1 nbs1].
      destruct R2 as [sbs2 nbs2].
      bdestruct5 J5 as EQ1 Htv_phinodes Htv_subblocks Htv_cmds EQ2.
      sumbool_subst.

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
      destruct J; subst. clear H H9.

      assert (uniq lc1) as Uniqc1.
        apply se_dbBlocks_preservation in d; auto.
          destruct d as [U1 _]; auto.
          apply productInSystemModuleB_nth_error__blockInSystemModuleFdef with (n:=0); 
            eauto using lookupFdefViaGVInSystem.
      assert (wf_subblocks sbs2 /\ wf_nbranchs nbs2) as J.
        apply uniqCmds___wf_subblocks_wf_nbranchs with (cs:=cs41++cs42); auto.
          clear - J6 J1 H10 H6 H2 H1 H4.
          apply se_dbBlocks_preservation in J6; auto using initLocals_uniq.
          destruct J6 as [uinqc1 Bin].
          apply blockInSystemModuleFdef_inv in Bin.
          destruct Bin as [J2 [J3 [J4 J5]]].
          apply uniqSystem__uniqFdef in J5; auto.

          apply blockInFdefB__exists_nth_error in J2.       
          destruct J2 as [n J2].
          apply uniqFdef__uniqBlock with (n:=n)(l1:=l2')(ps1:=ps2')(cs1:=cs41++cs42)(tmn1:=insn_return rid rt Result) in J5; auto.

          eapply productInSystemModuleB_nth_error__blockInSystemModuleFdef; 
            eauto using lookupFdefViaGVInSystem.
      destruct J as [wf_sbs2 wf_nbs2].
      apply H0 with (S2:=S2)(Ps2:=Ps2)(cs2:=cs41) in Htv_subblocks; auto.
        clear H0.
        destruct Htv_subblocks as [lc2' [HdbSubblocks Heq2]].

        apply cmds2nbranchs__nbranchs2cmds in Hcs22nbs1. subst.
        apply cmds2nbs__nbranchs2cmds in Hcs42nbs2. subst.
        assert (uniq lc2) as Uniqc2.
          apply se_dbSubblocks_preservation in d0; auto.
        apply tv_cmds__is__correct with (nbs':=nbs2) in d1; auto.
        destruct d1 as [lc3' [HdbCmds Heq3]].

        apply dbSubblocks_eqEnv with (lc1':=lc1') in HdbSubblocks; auto using eqAL_sym.
        destruct HdbSubblocks as [lc2'' [HdbSubblocks Heq2']].

        apply dbCmds_eqEnv with (lc1':=lc2'') in HdbCmds; eauto using eqAL_sym, eqAL_trans.
        destruct HdbCmds as [lc3'' [HdbCmds Heq3']].

        exists lc3''.
        split; auto. split; auto.
        split; auto.
        split; auto.
        split; auto.
        split; eauto using eqAL_trans, eqAL_sym.

      eapply lookupFdefViaGVInSystem; eauto.
      eapply lookupFdefViaGVInSystem; eauto.

      unfold tv_fdef.
      repeat_bsplit.

Case "dbFdef_proc".
    intros S TD Ps gl fs fv fid lp lc rid l1 ps1 cs1 tmn1 rt la lb lc1 tr1 Mem0 Mem1 als1
           l2 ps2 cs21 cs22 lc2 als2 Mem2 tr2 lc3 als3 Mem3 tr3 e e0 d H d0 H0 d1
           fid0 Ps2 S2 la0 lb1 H1 H2 H3 H4 H5 H6 H7 H8.
    rewrite H1 in e. inversion e; subst. clear e.
    assert (exists lb2, lookupFdefViaGV TD Ps2 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
                        tv_blocks lb lb2) as J.
      apply tv_products__lookupFdefViaGV with (Ps1:=Ps); auto.
    destruct J as [lb2 [H10 H11]].
    assert (uniq (initLocals la (params2GVs TD lp lc gl))) as uniqInitLocals.
      apply initLocals_uniq.
    assert (Htv_blocks:=H11).
    apply H with (S2:=S2)(Ps2:=Ps2)(fh1:=fheader_intro rt fid la)(fh2:=fheader_intro rt fid la)(n:=0)
      (ps1':=ps2)(l1':=l2)(als:=nil)(lc':=lc1)(lc0:=(initLocals la (params2GVs TD lp lc gl)))
      (Mem:=Mem0)(Mem':=Mem1)(als':=als1)(tmn1':=insn_return_void rid)(cs1':=cs21++cs22) 
      (ps3:=ps1)(cs2:=cs1)(tmn2:=tmn1)(l3:=l1)in H11; auto.
      clear H.
      destruct H11 as [l3 [ps3 [cs3 [tmn2 [l2' [ps2' [cs2' [tmn2' [n' [lc1' [J1 [J2 [J3 [J4 [J5 [J6 Heq1]]]]]]]]]]]]]]]].

      exists lb2. exists (block_intro l2' ps2' cs2' tmn2'). exists n'.

      assert (J5':=J5).
      unfold tv_block in J5.
      remember (cmds2sbs (cs21++cs22)) as R1.
      remember (cmds2sbs cs2') as R2.
      destruct R1 as [sbs1 nbs1].
      destruct R2 as [sbs2 nbs2].
      bdestruct5 J5 as EQ1 Htv_phinodes Htv_subblocks Htv_cmds EQ2.
      sumbool_subst.

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
      destruct J; subst. clear H H9.

      assert (uniq lc1) as Uniqc1.
        apply se_dbBlocks_preservation in d; auto.
          destruct d as [U1 _]; auto.
          apply productInSystemModuleB_nth_error__blockInSystemModuleFdef with (n:=0); 
            eauto using lookupFdefViaGVInSystem.
      assert (wf_subblocks sbs2 /\ wf_nbranchs nbs2) as J.
        apply uniqCmds___wf_subblocks_wf_nbranchs with (cs:=cs41++cs42); auto.
          clear - J6 J1 H10 H6 H2 H1 H4.
          apply se_dbBlocks_preservation in J6; auto using initLocals_uniq.
          destruct J6 as [uinqc1 Bin].
          apply blockInSystemModuleFdef_inv in Bin.
          destruct Bin as [J2 [J3 [J4 J5]]].
          apply uniqSystem__uniqFdef in J5; auto.

          apply blockInFdefB__exists_nth_error in J2.       
          destruct J2 as [n J2].
          apply uniqFdef__uniqBlock with (n:=n)(l1:=l2')(ps1:=ps2')(cs1:=cs41++cs42)(tmn1:=insn_return_void rid) in J5; auto.

          eapply productInSystemModuleB_nth_error__blockInSystemModuleFdef; 
            eauto using lookupFdefViaGVInSystem.
      destruct J as [wf_sbs2 wf_nbs2].
      apply H0 with (S2:=S2)(Ps2:=Ps2)(cs2:=cs41) in Htv_subblocks; auto.
        clear H0.
        destruct Htv_subblocks as [lc2' [HdbSubblocks Heq2]].

        apply cmds2nbranchs__nbranchs2cmds in Hcs22nbs1. subst.
        apply cmds2nbs__nbranchs2cmds in Hcs42nbs2. subst.
        assert (uniq lc2) as Uniqc2.
          apply se_dbSubblocks_preservation in d0; auto.
        apply tv_cmds__is__correct with (nbs':=nbs2) in d1; auto.
        destruct d1 as [lc3' [HdbCmds Heq3]].

        apply dbSubblocks_eqEnv with (lc1':=lc1') in HdbSubblocks; auto using eqAL_sym.
        destruct HdbSubblocks as [lc2'' [HdbSubblocks Heq2']].

        apply dbCmds_eqEnv with (lc1':=lc2'') in HdbCmds; eauto using eqAL_sym, eqAL_trans.
        destruct HdbCmds as [lc3'' [HdbCmds Heq3']].

        exists lc3''.
        split; auto. split; auto.
        split; auto.
        split; auto. split; auto.
        split; eauto using eqAL_trans, eqAL_sym.

      eapply lookupFdefViaGVInSystem; eauto.
      eapply lookupFdefViaGVInSystem; eauto.

      unfold tv_fdef.
      repeat_bsplit.
Qed.   

Lemma tv_dbCall__is__correct : forall S1 TD Ps1 fs gl lc Mem0 call0 lc' Mem' tr S2 Ps2,
  dbCall S1 TD Ps1 fs gl lc Mem0 call0 lc' Mem' tr ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists slc,
    dbCall S2 TD Ps2 fs gl lc Mem0 call0 slc Mem' tr /\
    eqAL _ slc lc'.
Proof.
  intros.
  destruct tv__is__correct as [J _].
  unfold tv_dbCall__is__correct_prop in J.
  eapply J; eauto.
Qed.

Definition tv_subblock__is__correct : forall S1 TD Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr S2 Ps2 cs2 sb1 sb2,
  dbSubblock S1 TD Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr ->
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
  tv_subblock sb1 sb2 ->
  exists slc,
    dbSubblock S2 TD Ps2 fs gl lc als Mem cs2 slc als' Mem' tr /\
    eqAL _ slc lc'.
Proof.
  intros.
  destruct tv__is__correct as [_ [J _]].
  unfold tv_subblock__is__correct_prop in J.
  eapply J; eauto.
Qed.

Lemma tv_subblocks__is__correct : forall S1 TD Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr S2 Ps2 sbs1 sbs2 cs2,
  dbSubblocks S1 TD Ps1 fs gl lc als Mem cs1 lc' als' Mem' tr ->
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
  tv_subblocks sbs1 sbs2 ->
  exists slc, 
    dbSubblocks S2 TD Ps2 fs gl lc als Mem cs2 slc als' Mem' tr /\
    eqAL _ slc lc'.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [J _]]].
  unfold tv_subblocks__is__correct_prop in J.
  eapply J; eauto.
Qed.

Lemma tv_block__is__correct : forall S1 TD Ps1 arg tr
  S2 Ps2 fh1 lb1 fh2 lb2 B1 lc als gl fs Mem B1' lc' als' Mem' B2,
  dbBlock S1 TD Ps1 fs gl (fdef_intro fh1 lb1) arg (mkState (mkEC B1 lc als) Mem) (mkState (mkEC B1' lc' als') Mem') tr ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  productInSystemModuleB (product_fdef (fdef_intro fh1 lb1)) S1 (module_intro TD Ps1) ->
  productInSystemModuleB (product_fdef (fdef_intro fh2 lb2)) S2 (module_intro TD Ps2) ->
  wf_block B2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) ->
  tv_block B1 B2 ->
  exists B2', exists n, exists slc,
    dbBlock S2 TD Ps2 fs gl (fdef_intro fh2 lb2) arg 
      (mkState (mkEC B2 lc als) Mem) 
      (mkState (mkEC B2' slc als') Mem')
      tr /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' /\ 
    eqAL _ slc lc'.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [_ [J _]]]].
  unfold tv_block__is__correct_prop in J.
  eapply J with (state1:=(mkState (mkEC B1 lc als) Mem0))(state2:=(mkState (mkEC B1' lc' als') Mem'))(F1:=(fdef_intro fh1 lb1)); eauto.
Qed.

Lemma tv_blocks__is__correct : forall S1 TD Ps1 lp tr
  S2 Ps2 fh1 lb1 fh2 lb2 fs gl lc n tmn1
                            l1 ps1 sbs1 ps1' l1' als
                            lc' Mem Mem' als' tmn1' sbs1',
  dbBlocks S1 TD Ps1 fs gl (fdef_intro fh1 lb1) lp (mkState (mkEC (block_intro l1 ps1 sbs1 tmn1) lc als) Mem) (mkState (mkEC (block_intro l1' ps1' sbs1' tmn1') lc' als') Mem') tr ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  productInSystemModuleB (product_fdef (fdef_intro fh1 lb1)) S1 (module_intro TD Ps1) ->
  productInSystemModuleB (product_fdef (fdef_intro fh2 lb2)) S2 (module_intro TD Ps2) ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) ->
  tv_blocks lb1 lb2 ->
  nth_error lb1 n = Some (block_intro l1 ps1 sbs1 tmn1) ->
  exists l2, exists ps2, exists sbs2, exists tmn2, 
  exists l2', exists ps2', exists sbs2', exists tmn2', exists n',
  exists slc,
    nth_error lb2 n = Some (block_intro l2 ps2 sbs2 tmn2) /\
    nth_error lb1 n' = Some (block_intro l1' ps1' sbs1' tmn1') /\
    nth_error lb2 n' = Some (block_intro l2' ps2' sbs2' tmn2') /\
    tv_block (block_intro l1 ps1 sbs1 tmn1) (block_intro l2 ps2 sbs2 tmn2) /\
    tv_block (block_intro l1' ps1' sbs1' tmn1') (block_intro l2' ps2' sbs2' tmn2') /\
    dbBlocks S2 TD Ps2 fs gl (fdef_intro fh2 lb2) lp
      (mkState (mkEC (block_intro l2 ps2 sbs2 tmn2) lc als) Mem)
      (mkState (mkEC (block_intro l2' ps2' sbs2' tmn2') slc als') Mem')
      tr /\
    eqAL _ slc lc'.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [_ [_ [J _]]]]].
  unfold tv_blocks__is__correct_prop in J.
  eapply J with (state1:=(mkState (mkEC (block_intro l1 ps1 sbs1 tmn1) lc als) Mem0))(state2:=(mkState (mkEC (block_intro l1' ps1' sbs1' tmn1') lc' als') Mem'))(F1:=(fdef_intro fh1 lb1)); eauto.
Qed.

Lemma _tv_fdef__is__correct : forall fv rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B1' Rid oResult tr
  fid Ps2 S2 la lb1,
  dbFdef fv rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B1' Rid oResult tr ->
  lookupFdefViaGV TD Ps1 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists lb2, exists B2', exists n, exists slc,
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' /\
    lookupFdefViaGV TD Ps2 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2 /\
    dbFdef fv rt lp S2 TD Ps2 lc gl fs Mem slc als' Mem' B2' Rid oResult tr /\
    eqAL _ slc lc'.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [_ [_ [_ J]]]]].
  unfold tv_fdef__is__correct_prop in J.
  eapply J; eauto.
Qed.

Lemma tv_fdef__is__correct : forall ECs fv rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B1' Rid oResult tr
  fid Ps2 S2 la lb1,
  LLVMopsem.dbFdef fv rt lp S1 TD Ps1 ECs lc gl fs Mem lc' als' Mem' B1' Rid oResult tr ->
  uniq gl ->
  uniq lc ->
  uniqSystem S1 ->
  uniqSystem S2 ->
  moduleInSystem (module_intro TD Ps1) S1 ->
  moduleInSystem (module_intro TD Ps2) S2 ->
  lookupFdefViaGV TD Ps1 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists lb2, exists B2', exists n, exists slc,
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' /\
    lookupFdefViaGV TD Ps2 gl lc fs fv = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2 /\
    LLVMopsem.dbFdef fv rt lp S2 TD Ps2 ECs lc gl fs Mem slc als' Mem' B2' Rid oResult tr /\
    eqAL _ slc lc'.
Proof.
  intros.
  apply llvmop_dbFdef__seop_dbFdef in H; auto.
  apply _tv_fdef__is__correct with (fid:=fid)(Ps2:=Ps2)(S2:=S2)(la:=la)(lb1:=lb1) in H; auto.
  destruct H as [lb2 [B2' [n [slc [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]]]]]].
  exists lb2. exists B2'. exists n. exists slc.
  repeat (split; auto).
    apply seop_dbFdef__llvmop_dbFdef; auto.
Qed.


