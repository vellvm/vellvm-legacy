Add LoadPath "./ott".
Add LoadPath "./monads".
(* Add LoadPath "../../../theory/metatheory". *)
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import ssa_def.
Require Import ssa_lib.
Require Import trace.
Require Import List.
Require Import tactics.
Require Import Coq.Program.Equality.
Require Import CoqListFacts.
Require Import Bool.
Require Import Metatheory.
Require Import assoclist.
Require Import ssa_props.

Export LLVMsyntax.
Export LLVMlib.
Export LLVMopsem.

(* prop *)


Lemma eqAL_callUpdateLocals : forall TD noret0 rid rt oResult lc1 lc2 gl lc1' lc2',
  eqAL _ lc1 lc1' ->
  eqAL _ lc2 lc2' ->
  eqAL _ (callUpdateLocals TD noret0 rid rt oResult lc1 lc2 gl)
         (callUpdateLocals TD noret0 rid rt oResult lc1' lc2' gl).
Proof.
  intros TD noret0 rid rt oResult lc1 lc2 gl lc1' lc2' H1 H2.
    unfold callUpdateLocals.
    destruct noret0; auto.
      destruct (rt=t=typ_void); auto.
        destruct oResult; simpl; auto.
          destruct v; simpl.
            rewrite H2.
            destruct (lookupAL _ lc2' i0); auto using eqAL_updateAddAL.

            destruct (const2GV TD gl c); auto using eqAL_updateAddAL.
Qed.


Lemma eqAL_getIncomingValuesForBlockFromPHINodes : forall ps B lc lc',
  eqAL _ lc lc' ->
  getIncomingValuesForBlockFromPHINodes ps B lc = getIncomingValuesForBlockFromPHINodes ps B lc'.
Proof.
  induction ps; intros; simpl; auto.
    destruct (getIdViaBlockFromPHINode a B); auto.
    rewrite H.
    erewrite IHps; eauto.
Qed.
  
Lemma eqAL_updateValuesForNewBlock : forall vs lc lc',
  eqAL _ lc lc' ->
  eqAL _ (updateValuesForNewBlock vs lc) (updateValuesForNewBlock vs lc').
Proof.
  induction vs; intros; simpl; auto.
    destruct a.
    destruct o; auto using eqAL_updateAddAL.
Qed.

Lemma eqAL_switchToNewBasicBlock : forall B1 B2 lc lc',
  eqAL _ lc lc' ->
  eqAL _ (switchToNewBasicBlock B1 B2 lc) (switchToNewBasicBlock B1 B2 lc').
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite eqAL_getIncomingValuesForBlockFromPHINodes; eauto.
  apply eqAL_updateValuesForNewBlock; auto.
Qed.

Lemma eqAL_params2OpGVs : forall lp TD lc gl lc',
  eqAL _ lc lc' ->
  params2OpGVs TD lp lc gl = params2OpGVs TD lp lc' gl.
Proof.
  induction lp; intros; simpl; auto.
    destruct a. 
    destruct v; simpl.
      rewrite H. erewrite IHlp; eauto.
      erewrite IHlp; eauto.
Qed.

Lemma eqAL_params2GVs : forall lp TD lc gl lc',
  eqAL _ lc lc' ->
  params2GVs TD lp lc gl = params2GVs TD lp lc' gl.
Proof.
  induction lp; intros; simpl; auto.
    destruct a.
    unfold params2GVs.
    erewrite eqAL_params2OpGVs; eauto.
Qed.

Lemma eqAL_initLocals : forall la lp TD lc gl lc',
  eqAL _ lc lc' ->
  eqAL _ (initLocals la (params2GVs TD lp lc gl)) (initLocals la (params2GVs TD lp lc' gl)).
Proof.
  intros. erewrite eqAL_params2GVs; eauto using eqAL_refl. 
Qed.

Lemma updateValuesForNewBlock_uniq : forall l0 lc,
  uniq lc ->
  uniq (updateValuesForNewBlock l0 lc).
Proof.
  induction l0; intros lc Uniqc; simpl; auto.
    destruct a.
    destruct o; auto.
      apply updateAddAL_uniq; auto.
Qed.

Lemma switchToNewBasicBlock_uniq : forall B1 B2 lc,
  uniq lc ->
  uniq (switchToNewBasicBlock B1 B2 lc).
Proof.
  intros B1 B2 lc Uniqc.
  unfold switchToNewBasicBlock.
  apply updateValuesForNewBlock_uniq; auto.
Qed.      

Lemma _initializeFrameValues_init : forall la l0,
  uniq (_initializeFrameValues la l0 nil).
Proof.
  induction la; intros; simpl; auto.
    destruct a.
    destruct l0; auto using updateAddAL_uniq.
Qed.

Lemma initLocals_uniq : forall la ps,
  uniq (initLocals la ps).
Proof.
  intros la ps.
  unfold initLocals.
  apply _initializeFrameValues_init; auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_eq : forall ps l1 ps1 cs1 tmn1 ps2 cs2 tmn2,
  getIncomingValuesForBlockFromPHINodes ps (block_intro l1 ps1 cs1 tmn1) =
  getIncomingValuesForBlockFromPHINodes ps (block_intro l1 ps2 cs2 tmn2).
Proof.
  induction ps; intros; auto.
    simpl.
    erewrite IHps; eauto.
Qed.

Lemma switchToNewBasicBlock_eq : forall B l1 ps1 cs1 tmn1 ps2 cs2 tmn2 lc,
  switchToNewBasicBlock B (block_intro l1 ps1 cs1 tmn1) lc =
  switchToNewBasicBlock B (block_intro l1 ps2 cs2 tmn2) lc.
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite getIncomingValuesForBlockFromPHINodes_eq; eauto.
Qed.

Lemma dbop_trans : forall state1 state2 state3 tr1 tr2,
  dbop state1 state2 tr1 ->
  dbop state2 state3 tr2 ->
  dbop state1 state3 (trace_app tr1 tr2).
Proof.
  intros state1 state2 state3 tr1 tr2 H.
  generalize dependent state3.
  generalize dependent tr2.
  induction H; intros; auto.
    rewrite <- trace_app_commute. eauto.
Qed.

Lemma dbInsn__dbop : forall state1 state2 tr,
  dbInsn state1 state2 tr ->
  dbop state1 state2 tr.
Proof.
  intros.
  rewrite <- trace_app_nil__eq__trace.
  eapply dbop_cons; eauto.
Qed.

Lemma dbInsn__inv : forall S1 TD1 Ps1 F1 l1 ps1 cs1 tmn1 c cs tmn3 lc1 arg1 als1 ECs1 gl1 Mem1
                         S2 TD2 Ps2 F2 l2 ps2 cs2 tmn2 tmn4 lc2 arg2 als2 ECs2 gl2 Mem2 tr,
  dbInsn 
    (mkState S1 TD1 Ps1 (mkEC F1 (block_intro l1 ps1 cs1 tmn1) (c::cs) tmn3 lc1 arg1 als1::ECs1) gl1 Mem1) 
    (mkState S2 TD2 Ps2 (mkEC F2 (block_intro l2 ps2 cs2 tmn2) cs tmn4 lc2 arg2 als2::ECs2) gl2 Mem2)
    tr ->
  S1 = S2 /\ TD1 = TD2 /\ Ps1 = Ps2 /\ F1 = F2 /\ l1 = l2 /\ ps1 = ps2 /\
  cs1 = cs2 /\ tmn1 = tmn2 /\ tmn3 = tmn4 /\ gl1 = gl2.
Proof.
  intros.
  inversion H; subst; repeat (split; auto).
Qed.

Lemma dbInsn_Call__inv : forall S1 TD1 Ps1 F1 l1 ps1 cs1 tmn1 c cs tmn3 lc1 arg1 als1 ECs1 gl1 Mem1
                         S2 TD2 Ps2 F2 l2 ps2 cs2 tmn2 tmn4 lc2 arg2 als2 ECs2 gl2 Mem2 tr,
  
  dbInsn 
    (mkState S1 TD1 Ps1 (mkEC F1 (block_intro l1 ps1 cs1 tmn1) (c::cs) tmn3 lc1 arg1 als1::ECs1) gl1 Mem1) 
    (mkState S2 TD2 Ps2 (mkEC F2 (block_intro l2 ps2 cs2 tmn2) cs tmn4 lc2 arg2 als2::ECs2) gl2 Mem2)
    tr ->
  Instruction.isCallInst c = true ->
  S1 = S2 /\ TD1 = TD2 /\ Ps1 = Ps2 /\ F1 = F2 /\ l1 = l2 /\ ps1 = ps2 /\
  cs1 = cs2 /\ tmn1 = tmn2 /\ tmn3 = tmn4 /\ gl1 = gl2 /\ als1 = als2.
Proof.
  intros.
  inversion H; subst; try solve [inversion H0].
    repeat (split; auto).
Qed.

(* preservation *)

Definition dbInsn_preservation_prop state1 state2 tr
  (db:dbInsn state1 state2 tr) :=
  forall S TD Ps F l ps cs tmn lc arg als ECs gl Mem cs0,
  state1 = (mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem) ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro TD Ps) F ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists Mem', exists cs0',
  state2 = (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl Mem') /\
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S (module_intro TD Ps) F.
Definition dbop_preservation_prop state1 state2 tr
  (db:dbop state1 state2 tr) :=
  forall S TD Ps F l ps cs tmn lc arg als ECs gl Mem l' ps' cs' tmn' lc' als' gl' Mem' cs0 cs0',
  state1 = (mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem) ->
  state2 = (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem') ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro TD Ps) F ->
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S (module_intro TD Ps) F.
Definition dbFdef_preservation_prop fid rt lp S TD Ps ECs lc gl Mem lc' als' Mem' B' Rid oResult tr
  (db:dbFdef fid rt lp S TD Ps ECs lc gl Mem lc' als' Mem' B' Rid oResult tr) :=
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  exists F, 
    lookupFdefViaIDFromProducts Ps fid = Some F /\
    uniqFdef F /\
    blockInSystemModuleFdef B' S (module_intro TD Ps) F.

Lemma db_preservation : 
  (forall state1 state2 tr db, @dbInsn_preservation_prop state1 state2 tr db) /\
  (forall state1 state2 tr db, @dbop_preservation_prop state1 state2 tr  db) /\
  (forall fid rt lp S TD Ps lc gl Mem lc' als' Mem' B' Rid oResult tr ECs db, 
    @dbFdef_preservation_prop fid rt lp S TD Ps lc gl Mem lc' als' Mem' B' Rid oResult tr ECs db).
Proof.
(db_mutind_cases
  apply LLVMopsem.db_mutind with
    (P  := dbInsn_preservation_prop)
    (P0 := dbop_preservation_prop)
    (P1 := dbFdef_preservation_prop) Case);
  unfold dbInsn_preservation_prop, 
         dbop_preservation_prop, 
         dbFdef_preservation_prop; intros; subst.
Case "dbBranch".
  inversion H; subst. clear H.
  exists l'. exists ps'. exists cs'. exists tmn'.
  exists (switchToNewBasicBlock (block_intro l' ps' cs' tmn') (block_intro l0 ps cs0 (insn_br bid Cond l1 l2)) lc0). exists als0. exists Mem1.
  exists cs'. split; auto.
  apply andb_true_iff in H1.
  destruct H1.
  eapply andb_true_iff.
  split; auto.
    assert (uniqFdef F0) as UniqF0.
      eapply uniqSystem__uniqFdef with (S:=S0); eauto.
    symmetry in e0.
    destruct (Coqlib.zeq c 0);
      apply lookupBlockViaLabelFromFdef_inv in e0;
      destruct e0; auto.

Case "dbBranch_uncond".
  inversion H; subst. clear H.
  exists l'. exists ps'. exists cs'. exists tmn'.
  exists (switchToNewBasicBlock (block_intro l' ps' cs' tmn') (block_intro l1 ps cs0 (insn_br_uncond bid l0)) lc0). exists als0. exists Mem1.
  exists cs'. split; auto.
  apply andb_true_iff in H1.
  destruct H1.
  eapply andb_true_iff.
  split; auto.
    assert (uniqFdef F0) as UniqF0.
      eapply uniqSystem__uniqFdef with (S:=S0); eauto.
    symmetry in e.
    apply lookupBlockViaLabelFromFdef_inv in e; auto.
    destruct e; auto.

Case "dbBop".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "dbExtractValue".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv'). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "dbInsertValue".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv''). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "dbMalloc".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 (blk2GV TD0 mb)). exists als0. exists Mem'.
  exists cs1. split; auto.

Case "dbFree".
  inversion H; subst. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists Mem'.
  exists cs1. split; auto.

Case "dbAlloca".
  inversion H; subst. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 (blk2GV TD0 mb)). exists (mb::als0). exists Mem'.
  exists cs1. split; auto.

Case "dbLoad".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "dbStore".
  inversion H; subst. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists Mem'.
  exists cs1. split; auto.

Case "dbGEP".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 (ptr2GV TD0 mp')). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "dbExt".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv2). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "dbCast".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv2). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "dbIcmp".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "dbSelect".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (if Coqlib.zeq c 0 then updateAddAL _ lc0 id0 gv2 else updateAddAL _ lc0 id0 gv1). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "dbCall".
  inversion H0; subst. clear H0.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (callUpdateLocals TD0 noret0 rid rt oResult lc0 lc' gl0). exists als0. exists Mem''.
  exists cs1. split; auto.
 
Case "dbop_nil".
  inversion H0; subst. auto.
  
Case "dbop_cons".
  apply H with (cs1:=cs)(lc0:=lc)(arg:=arg0)(als0:=als)(ECs0:=ECs)(gl0:=gl)(Mem:=Mem0) in H4; auto.
  clear H.
  destruct H4 as [l1 [ps1 [cs1 [tmn1 [lc1 [als1 [Mem1 [cs1' [EQ H4]]]]]]]]]; subst.
  eapply H0; eauto.

Case "dbFdef_func".
  exists (fdef_intro (fheader_intro rt fid la) lb).
  split; auto.
  split; auto.
    eapply lookupFdefViaIDFromProducts_uniq; eauto.
    eapply H; eauto using entryBlockInSystemBlockFdef.

Case "dbFdef_proc".
  exists (fdef_intro (fheader_intro rt fid la) lb).
  split; auto.
  split; auto.
    eapply lookupFdefViaIDFromProducts_uniq; eauto.
    eapply H; eauto using entryBlockInSystemBlockFdef.
Qed.

Lemma _dbInsn_preservation : forall state2 tr S TD Ps F l ps cs tmn lc arg als ECs gl Mem cs0,
  dbInsn ((mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem)) state2 tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro TD Ps) F ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists Mem', exists cs0',
  state2 = (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl Mem') /\
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S (module_intro TD Ps) F.
Proof.
  intros.
  destruct db_preservation as [J _].
  unfold dbInsn_preservation_prop in J.
  eapply J; eauto.
Qed.

Lemma dbInsn_preservation : forall tr S TD Ps F l ps cs tmn lc arg als ECs gl Mem cs0
  l' ps'  cs' tmn' lc' als' gl' Mem' cs0',
  dbInsn 
    ((mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem)) 
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem')
    tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro TD Ps) F ->
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S (module_intro TD Ps) F.
Proof.
  intros.
  apply _dbInsn_preservation in H; auto.
  destruct H as [l1 [ps1 [cs1 [tmn1 [lc1 [als1 [Mem1 [cs2 [J1 J2]]]]]]]]].
  inversion J1; subst. clear J1. auto.  
Qed.

Lemma dbop_preservation : forall tr S TD Ps F l ps cs tmn lc arg als ECs gl Mem l' ps' cs' tmn' lc' als' gl' Mem' cs0 cs0',
  dbop 
    (mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem')
    tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro TD Ps) F ->
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S (module_intro TD Ps) F.
Proof.
  intros.
  destruct db_preservation as [_ [J _]].
  unfold dbop_preservation_prop in J.
  eapply J; eauto.
Qed.

Lemma dbFdef_preservation : forall fid rt lp S TD Ps ECs lc gl Mem lc' als' Mem' B' Rid oResult tr,
  dbFdef fid rt lp S TD Ps ECs lc gl Mem lc' als' Mem' B' Rid oResult tr ->
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  exists F, 
    lookupFdefViaIDFromProducts Ps fid = Some F /\
    uniqFdef F /\
    blockInSystemModuleFdef B' S (module_intro TD Ps) F.
Proof.
  intros.
  destruct db_preservation as [_ [_ J]].
  unfold dbFdef_preservation_prop in J.
  eapply J; eauto.
Qed.

