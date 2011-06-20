Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
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
Require Import alist.
Require Import ssa_props.

Export LLVMsyntax.
Export LLVMlib.
Export LLVMopsem.

(* prop *)

Lemma eqAL_callUpdateLocals : forall TD M noret0 rid oResult lc1 lc2 gl lc1' 
  lc2',
  eqAL _ lc1 lc1' ->
  eqAL _ lc2 lc2' ->
  match (callUpdateLocals TD M noret0 rid oResult lc1 lc2 gl,
         callUpdateLocals TD M noret0 rid oResult lc1' lc2' gl) with
  | (Some lc, Some lc') => eqAL _ lc lc'
  | (None, None) => True
  | _ => False
  end.
Proof.
  intros TD M noret0 rid oResult lc1 lc2 gl lc1' lc2' H1 H2.
    unfold callUpdateLocals.
    destruct noret0; auto.
      destruct oResult; simpl; auto.
        destruct v; simpl.
          rewrite H2.
          destruct (lookupAL _ lc2' i0); auto using eqAL_updateAddAL.

          destruct (const2GV TD M gl c); auto using eqAL_updateAddAL.
Qed.

Lemma eqAL_getIncomingValuesForBlockFromPHINodes : forall TD M ps B gl lc lc',
  eqAL _ lc lc' ->
  getIncomingValuesForBlockFromPHINodes TD M ps B gl lc = 
  getIncomingValuesForBlockFromPHINodes TD M ps B gl lc'.
Proof.
  induction ps; intros; simpl; auto.
    destruct a; auto.
    destruct (getValueViaBlockFromValuels l0 B); auto.
    destruct v; erewrite IHps; eauto.
      rewrite H. auto.
Qed.
  
Lemma eqAL_updateValuesForNewBlock : forall vs lc lc',
  eqAL _ lc lc' ->
  eqAL _ (updateValuesForNewBlock vs lc) (updateValuesForNewBlock vs lc').
Proof.
  induction vs; intros; simpl; auto.
    destruct a; auto using eqAL_updateAddAL.
Qed.

Lemma eqAL_switchToNewBasicBlock : forall TD M B1 B2 gl lc lc',
  eqAL _ lc lc' ->
  match (switchToNewBasicBlock TD M B1 B2 gl lc,
         switchToNewBasicBlock TD M B1 B2 gl lc') with
  | (Some lc1, Some lc1') => eqAL _ lc1 lc1'
  | (None, None) => True
  | _ => False
  end.
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite eqAL_getIncomingValuesForBlockFromPHINodes; eauto.
  destruct 
    (getIncomingValuesForBlockFromPHINodes TD M (getPHINodesFromBlock B1) B2 gl 
    lc'); auto using eqAL_updateValuesForNewBlock.
Qed.

Lemma eqAL_params2GVs : forall lp TD M lc gl lc',
  eqAL _ lc lc' ->
  params2GVs TD M lp lc gl = params2GVs TD M lp lc' gl.
Proof.
  induction lp; intros; simpl; auto.
    destruct a. 
    destruct v; simpl.
      rewrite H. erewrite IHlp; eauto.
      erewrite IHlp; eauto.
Qed.

Lemma eqAL_exCallUpdateLocals : forall noret0 rid oResult lc lc',
  eqAL _ lc lc' ->
  match (exCallUpdateLocals noret0 rid oResult lc,
         exCallUpdateLocals noret0 rid oResult lc') with
  | (Some lc1, Some lc1') => eqAL _ lc1 lc1'
  | (None, None) => True
  | _ => False
  end.
Proof.
  intros noret0 rid oResult lc lc' H1.
    unfold exCallUpdateLocals.
    destruct noret0; auto.
    destruct oResult; simpl; auto using eqAL_updateAddAL.
Qed.

Lemma updateValuesForNewBlock_uniq : forall l0 lc,
  uniq lc ->
  uniq (updateValuesForNewBlock l0 lc).
Proof.
  induction l0; intros lc Uniqc; simpl; auto.
    destruct a; apply updateAddAL_uniq; auto.
Qed.

Lemma switchToNewBasicBlock_uniq : forall TD M B1 B2 gl lc lc',
  uniq lc ->
  switchToNewBasicBlock TD M B1 B2 gl lc = Some lc' ->
  uniq lc'.
Proof.
  intros TD M B1 B2 gl lc lc' Uniqc H.
  unfold switchToNewBasicBlock in H.
  destruct (getIncomingValuesForBlockFromPHINodes TD M (getPHINodesFromBlock B1)
    B2 gl lc); inversion H; subst.
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

Lemma getIncomingValuesForBlockFromPHINodes_eq : 
  forall ps TD M l1 ps1 cs1 tmn1 ps2 cs2 tmn2,
  getIncomingValuesForBlockFromPHINodes TD M ps (block_intro l1 ps1 cs1 tmn1) =
  getIncomingValuesForBlockFromPHINodes TD M ps (block_intro l1 ps2 cs2 tmn2).
Proof.
  induction ps; intros; auto.
    simpl.
    erewrite IHps; eauto.
Qed.

Lemma switchToNewBasicBlock_eq : 
  forall TD M B l1 ps1 cs1 tmn1 ps2 cs2 tmn2 gl lc,
  switchToNewBasicBlock TD M B (block_intro l1 ps1 cs1 tmn1) gl lc =
  switchToNewBasicBlock TD M B (block_intro l1 ps2 cs2 tmn2) gl lc.
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

Lemma dbInsn__inv : forall S1 TD1 Ps1 F1 l1 ps1 cs1 tmn1 c cs tmn3 lc1 als1 
    ECs1 gl1 fs1 Mem1 S2 TD2 Ps2 F2 l2 ps2 cs2 tmn2 tmn4 lc2 als2 ECs2 gl2 
    fs2 Mem2 tr,
  dbInsn 
    (mkState S1 TD1 Ps1 (mkEC F1 (block_intro l1 ps1 cs1 tmn1) (c::cs) tmn3 lc1 
      als1::ECs1) gl1 fs1 Mem1) 
    (mkState S2 TD2 Ps2 (mkEC F2 (block_intro l2 ps2 cs2 tmn2) cs tmn4 lc2
      als2::ECs2) gl2 fs2 Mem2)
    tr ->
  S1 = S2 /\ TD1 = TD2 /\ Ps1 = Ps2 /\ F1 = F2 /\ l1 = l2 /\ ps1 = ps2 /\
  cs1 = cs2 /\ tmn1 = tmn2 /\ tmn3 = tmn4 /\ gl1 = gl2 /\ fs1 = fs2.
Proof.
  intros.
  inversion H; subst; repeat (split; auto).
Qed.

Lemma dbInsn_Call__inv : forall S1 TD1 Ps1 F1 l1 ps1 cs1 tmn1 c cs tmn3 lc1 
    als1 ECs1 gl1 fs1 Mem1 S2 TD2 Ps2 F2 l2 ps2 cs2 tmn2 tmn4 lc2 als2 ECs2
     gl2 fs2 Mem2 tr,
  dbInsn 
    (mkState S1 TD1 Ps1 (mkEC F1 (block_intro l1 ps1 cs1 tmn1) (c::cs) tmn3 lc1 
      als1::ECs1) gl1 fs1 Mem1) 
    (mkState S2 TD2 Ps2 (mkEC F2 (block_intro l2 ps2 cs2 tmn2) cs tmn4 lc2 
      als2::ECs2) gl2 fs2 Mem2)
    tr ->
  Instruction.isCallInst c = true ->
  S1 = S2 /\ TD1 = TD2 /\ Ps1 = Ps2 /\ F1 = F2 /\ l1 = l2 /\ ps1 = ps2 /\
  cs1 = cs2 /\ tmn1 = tmn2 /\ tmn3 = tmn4 /\ gl1 = gl2  /\ fs1 = fs2 /\ als1 = als2.
Proof.
  intros.
  inversion H; subst; try solve [inversion H0 | repeat (split; auto)].
Qed.

(* preservation *)

Definition dbInsn_preservation_prop state1 state2 tr
  (db:dbInsn state1 state2 tr) :=
  forall S los nts Ps F l ps cs tmn lc als ECs gl fs Mem cs0,
  state1 = (mkState S (los, nts) Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn 
    lc als)::ECs) gl fs Mem) ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S 
    (module_intro los nts Ps) F ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists Mem', exists cs0',
  state2 = (mkState S (los, nts) Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' 
    tmn' lc' als')::ECs) gl fs Mem') /\
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S 
    (module_intro los nts Ps) F.
Definition dbop_preservation_prop state1 state2 tr
  (db:dbop state1 state2 tr) :=
  forall S los nts Ps F l ps cs tmn lc als ECs gl fs Mem l' ps' cs' tmn' lc'
    als' gl' fs' Mem' cs0 cs0',
  state1 = (mkState S (los, nts) Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn 
    lc als)::ECs) gl fs Mem) ->
  state2 = (mkState S (los, nts) Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' 
    tmn' lc' als')::ECs) gl' fs' Mem') ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S 
    (module_intro los nts Ps) F ->
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S 
    (module_intro los nts Ps) F.
Definition dbFdef_preservation_prop fv rt lp S TD Ps ECs lc gl fs Mem lc' als' 
  Mem' B' Rid oResult tr
  (db:dbFdef fv rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' B' Rid oResult tr) 
  :=
  forall los nts,
  TD = (los, nts) ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  exists F, 
    lookupFdefViaGV TD Mem Ps gl lc fs fv = Some F /\
    uniqFdef F /\
    blockInSystemModuleFdef B' S (module_intro los nts Ps) F.

Lemma db_preservation : 
  (forall state1 state2 tr db, @dbInsn_preservation_prop state1 state2 tr db) /\
  (forall state1 state2 tr db, @dbop_preservation_prop state1 state2 tr  db) /\
  (forall fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ECs db, 
    @dbFdef_preservation_prop fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ECs db).
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
  exists lc'. exists als0. exists Mem1.
  exists cs'. split; auto.
  apply andb_true_iff in H1.
  destruct H1.
  eapply andb_true_iff.
  split; auto.
    assert (uniqFdef F0) as UniqF0.
      eapply uniqSystem__uniqFdef with (S:=S0); eauto.
    symmetry in e0.
    destruct (isGVZero (los, nts) c);
      apply lookupBlockViaLabelFromFdef_inv in e0;
      destruct e0; auto.

Case "dbBranch_uncond".
  inversion H; subst. clear H.
  exists l'. exists ps'. exists cs'. exists tmn'.
  exists lc'. exists als0. exists Mem1.
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

Case "dbFBop".
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
  exists (updateAddAL _ lc0 id0 (blk2GV (los, nts) mb)). exists als0. exists Mem'.
  exists cs1. split; auto.

Case "dbFree".
  inversion H; subst. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists Mem'.
  exists cs1. split; auto.

Case "dbAlloca".
  inversion H; subst. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 (blk2GV (los, nts) mb)). exists (mb::als0). exists Mem'.
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
  exists (updateAddAL _ lc0 id0 mp'). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "dbTrunc".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv2). exists als0. exists Mem1.
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

Case "dbFcmp".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "dbSelect".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (if isGVZero (los, nts) c then updateAddAL _ lc0 id0 gv2 else updateAddAL _ lc0 id0 gv1). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "dbCall".
  inversion H0; subst. clear H0.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc''. exists als0. exists Mem''.
  exists cs1. split; auto.
 
Case "dbExCall".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists Mem'.
  exists cs1. split; auto.

Case "dbop_nil".
  inversion H0; subst. auto.
  
Case "dbop_cons".
  apply H with (cs1:=cs)(lc0:=lc)(als0:=als)(ECs0:=ECs)(gl0:=gl)
    (fs0:=fs)(Mem:=Mem0) in H4; auto.
  clear H.
  destruct H4 as [l1 [ps1 [cs1 [tmn1 [lc1 [als1 [Mem1 [cs1' [EQ H4]]]]]]]]]; 
    subst.
  eapply H0; eauto.

Case "dbFdef_func".
  exists (fdef_intro (fheader_intro fa rt fid la va) lb).
  split; auto.
  split; auto.
    eapply lookupFdefViaGV_uniq; eauto.
    eapply H with (lc'0:=lc')(cs'0:=nil)(als'0:=als')(gl':=gl)(fs':=fs)
      (Mem'0:=Mem'); 
      eauto using entryBlockInSystemBlockFdef'.
      

Case "dbFdef_proc".
  exists (fdef_intro (fheader_intro fa rt fid la va) lb).
  split; auto.
  split; auto.
    eapply lookupFdefViaGV_uniq; eauto.
    eapply H; eauto using entryBlockInSystemBlockFdef'.
Qed.

Lemma _dbInsn_preservation : forall state2 tr S los nts Ps F l ps cs tmn lc als ECs gl fs Mem cs0,
  dbInsn ((mkState S (los, nts) Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc als)::ECs) gl fs Mem)) state2 tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps) F ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists Mem', exists cs0',
  state2 = (mkState S (los, nts) Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' als')::ECs) gl fs Mem') /\
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S (module_intro los nts Ps) F.
Proof.
  intros.
  destruct db_preservation as [J _].
  unfold dbInsn_preservation_prop in J.
  eapply J; eauto.
Qed.

Lemma dbInsn_preservation : forall tr S los nts Ps F l ps cs tmn lc als ECs gl 
    fs Mem cs0 l' ps'  cs' tmn' lc' als' gl' fs' Mem' cs0',
  dbInsn 
    ((mkState S (los, nts) Ps 
      ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc als)::ECs) gl fs Mem)) 
    (mkState S (los, nts) Ps 
      ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' als')::ECs) gl' fs' 
        Mem')
    tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps)
    F ->
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S 
    (module_intro los nts Ps) F.
Proof.
  intros.
  apply _dbInsn_preservation in H; auto.
  destruct H as [l1 [ps1 [cs1 [tmn1 [lc1 [als1 [Mem1 [cs2 [J1 J2]]]]]]]]].
  inversion J1; subst. clear J1. auto.  
Qed.

Lemma dbop_preservation : forall tr S los nts Ps F l ps cs tmn lc als ECs gl
    fs Mem l' ps' cs' tmn' lc' als' gl' fs' Mem' cs0 cs0',
  dbop 
    (mkState S (los, nts) Ps 
      ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc als)::ECs) gl fs Mem)
    (mkState S (los, nts) Ps 
      ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' als')::ECs) gl' fs' 
        Mem')
    tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps)
    F ->
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S 
    (module_intro los nts Ps) F.
Proof.
  intros.
  destruct db_preservation as [_ [J _]].
  unfold dbop_preservation_prop in J.
  eapply J; eauto.
Qed.

Lemma dbFdef_preservation : forall fv rt lp S los nts Ps ECs lc gl fs Mem lc' 
    als' Mem' B' Rid oResult tr,
  dbFdef fv rt lp S (los, nts) Ps ECs lc gl fs Mem lc' als' Mem' B' Rid oResult tr ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  exists F, 
    lookupFdefViaGV (los, nts) Mem Ps gl lc fs fv = Some F /\
    uniqFdef F /\
    blockInSystemModuleFdef B' S (module_intro los nts Ps) F.
Proof.
  intros.
  destruct db_preservation as [_ [_ J]].
  unfold dbFdef_preservation_prop in J.
  eapply J; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
