Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "../../../theory/metatheory".
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import ssa.
Require Import trace.
Require Import List.
Require Import tactics.
Require Import Coq.Program.Equality.
Require Import CoqListFacts.
Require Import Bool.
Require Import Metatheory.

Export LLVMsyntax.
Export LLVMlib.
Export LLVMopsem.

(* eq *)

Lemma blockEqB_refl : forall B,
  blockEqB B B.
Admitted.
     
Lemma productEqB_refl : forall p,
  productEqB p p.
Admitted.

Lemma blockEqB_inv : forall B1 B2,
  blockEqB B1 B2 -> B1 = B2.
Admitted.

Lemma moduleEqB_inv : forall M M',
  moduleEqB M M' ->
  M = M'.
Admitted.

Lemma productEqB_inv : forall P P',
  productEqB P P' ->
  P = P'.
Admitted.


(* prop *)

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
  cs1 = cs2 /\ tmn1 = tmn2 /\ tmn3 = tmn4.
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
  cs1 = cs2 /\ tmn1 = tmn2 /\ tmn3 = tmn4 /\ als1 = als2.
Proof.
  intros.
  inversion H; subst; try solve [inversion H0].
    repeat (split; auto).
Qed.

Lemma InBlocksB_middle : forall lb1 B lb2,
  InBlocksB B (lb1++B::lb2).
Proof.
  induction lb1; intros; simpl; auto.
    apply orb_true_intro.
    left. apply blockEqB_refl.

    apply orb_true_intro.
    right. apply IHlb1.
Qed. 

Lemma _genLabel2Block_blocks_inv : forall lb2 lb1 lb f l0 l' ps' cs' tmn',
  genLabel2Block_blocks lb2 (fdef_intro f lb) l0 = Some (block_intro l' ps' cs' tmn') ->
  lb1++lb2 = lb ->
  l0 = l' /\
  blockInFdefB (block_intro l' ps' cs' tmn') (fdef_intro f lb).
Proof.
  induction lb2; intros; simpl in *.
    inversion H.

    unfold mergel2block in H.
    remember (genLabel2Block_blocks lb2 (fdef_intro f lb) l0) as ob.
    destruct ob.
      inversion H; subst. clear H.
      symmetry in Heqob.
      apply IHlb2 with (lb1:=lb1++a::nil) in Heqob; simpl_env; auto.
       
      unfold genLabel2Block_block in H.
      destruct a.
      destruct (l0 == l1); subst.
        inversion H; subst. clear H.
        split; auto using InBlocksB_middle.

        inversion H.
Qed.

Lemma genLabel2Block_blocks_inv : forall lb f l0 l' ps' cs' tmn',
  genLabel2Block_blocks lb (fdef_intro f lb) l0 = Some (block_intro l' ps' cs' tmn') ->
  l0 = l' /\
  blockInFdefB (block_intro l' ps' cs' tmn') (fdef_intro f lb).
Proof.
  intros.
  apply _genLabel2Block_blocks_inv with (lb1:=nil)(lb2:=lb); auto.
Qed.


Lemma lookupBlockViaLabelFromFdef_inv : forall F l0 l' ps' cs' tmn',
  lookupBlockViaLabelFromFdef F l0 = Some (block_intro l' ps' cs' tmn') ->
  l0 = l' /\
  blockInFdefB (block_intro l' ps' cs' tmn') F.
Proof.
  intros.
  unfold lookupBlockViaLabelFromFdef in H.
  unfold genLabel2Block_fdef in H.
  destruct F.
  apply genLabel2Block_blocks_inv; auto.
Qed. 

Lemma lookupFdefViaIDFromProducts_inv : forall Ps fid F,
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  InProductsB (product_fdef F) Ps.
Proof.
  induction Ps; intros.
    simpl in H. inversion H.

    simpl in *.
    unfold lookupFdefViaIDFromProduct in H.
    destruct a.
      apply IHPs in H. auto.
      apply IHPs in H. auto.
      destruct (getFdefID f==fid); subst.
        inversion H; subst.
        apply orb_true_intro.
        left. apply productEqB_refl.

        apply IHPs in H. 
        apply orb_true_intro. auto.
Qed.

Lemma entryBlockInFdef : forall F B,
  getEntryBlock F = Some B ->
  blockInFdefB B F.
Proof.
  intros.
  unfold getEntryBlock in H.
  destruct F.
  destruct b; inversion H; subst.
    simpl. 
    apply orb_true_intro.
    left. apply blockEqB_refl.
Qed.

Lemma blockInSystemModuleFdef_inv : forall B F Ps TD S,
  blockInSystemModuleFdef B S (module_intro TD Ps) F ->
  blockInFdefB B F /\
  InProductsB (product_fdef F) Ps /\
  moduleInSystem (module_intro TD Ps) S /\
  productInSystemModuleB (product_fdef F) S (module_intro TD Ps).
Proof.
  intros.
  unfold blockInSystemModuleFdef in H.
  unfold blockInSystemModuleFdefB in H.
  unfold productInSystemModuleB in *.
  unfold productInModuleB in *.
  apply andb_true_iff in H. destruct H.
  split; auto.
  apply andb_true_iff in H0. destruct H0.
  split; auto.
  split; auto.
  eapply andb_true_iff.
  split; auto.
Qed.

Lemma blockInSystemModuleFdef_intro : forall B F Ps TD S,
  blockInFdefB B F ->
  InProductsB (product_fdef F) Ps ->
  moduleInSystem (module_intro TD Ps) S ->
  blockInSystemModuleFdef B S (module_intro TD Ps) F.
Proof.
  intros.
  unfold blockInSystemModuleFdef.
  unfold blockInSystemModuleFdefB.
  unfold productInSystemModuleB.
  unfold productInModuleB.
  eapply andb_true_iff.
  split; auto.
  eapply andb_true_iff.
  split; auto.
Qed.  

Lemma entryBlockInSystemBlockFdef : forall TD Ps S fid F B,
  moduleInSystem (module_intro TD Ps) S ->
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  getEntryBlock F = Some B ->
  blockInSystemModuleFdef B S (module_intro TD Ps) F.
Proof.
  intros.
  apply lookupFdefViaIDFromProducts_inv in H0.
  apply entryBlockInFdef in H1.
  apply blockInSystemModuleFdef_intro; auto.
Qed.

Lemma NotIn_NotInBlocksB : forall lb l0 ps cs tmn,
  ~ In l0 (getBlocksLabels lb) ->
  ~ InBlocksB (block_intro l0 ps cs tmn) lb.
Proof.
  induction lb; intros; simpl in *.
    intro J. inversion J.

    destruct a.
    simpl in *.
    remember (block_intro l0 ps cs tmn =b= block_intro l1 p c t) as J.
    destruct J.
      unfold blockEqB in HeqJ.
      unfold lEqB in HeqJ.
      destruct (l0==l1); subst.
        contradict H; auto.
        inversion HeqJ.

      intro J.
      apply H.
      right.
      apply orb_prop in J.
      destruct J as [J | J].
        inversion J.
     
        destruct (@In_dec _ eq_dec l0 (getBlocksLabels lb)) as [J1 | J1]; auto.
        apply IHlb with (ps:=ps)(cs:=cs)(tmn:=tmn) in J1.
        rewrite J in J1.
        contradict J1; auto.
        unfold is_true. auto.
Qed.

Lemma InBlocksB_In : forall lb l0 ps cs tmn,
  InBlocksB (block_intro l0 ps cs tmn) lb ->
  In l0 (getBlocksLabels lb).
Proof.
  intros.
  destruct (@In_dec _ eq_dec l0 (getBlocksLabels lb)) as [J1 | J1]; auto.
    apply NotIn_NotInBlocksB with (ps:=ps)(cs:=cs)(tmn:=tmn) in J1.
    contradict H; auto.
Qed.

Lemma NoDup_split : forall A (l1 l2:list A),
  NoDup (l1++l2) ->
  NoDup l1 /\ NoDup l2.
Proof.
  induction l1; intros.
    simpl in *. 
    split; auto using NoDup_nil.
 
    inversion H; subst.
    apply IHl1 in H3.
    destruct H3 as [J1 J2].
    split; auto.
      apply NoDup_cons; auto.
        intro J. apply H2. apply in_or_app; auto.
Qed.

Lemma InBlocksB_uniq : forall lb l1 ps1 cs1 tmn1 ps2 cs2 tmn2,
  uniqBlocks lb ->
  InBlocksB (block_intro l1 ps1 cs1 tmn1) lb ->
  InBlocksB (block_intro l1 ps2 cs2 tmn2) lb ->
  ps1 = ps2 /\ cs1 = cs2 /\ tmn1 = tmn2.
Proof.
  induction lb; intros.
    unfold InBlocksB in *.
    inversion H0.

    inversion H; subst. clear H.
    simpl in *.
    destruct a.
    inversion H2; subst. clear H2.
    assert (J:=H5).
    apply NotIn_NotInBlocksB with (ps:=p)(cs:=c)(tmn:=t) in H5.
    apply orb_prop in H0.
    apply orb_prop in H1.
    destruct H0 as [H0 | H0].    
      apply blockEqB_inv in H0.
      inversion H0; subst. clear H0.
      destruct H1 as [H1 | H1].
        apply blockEqB_inv in H1.
        inversion H1; subst. clear H1.
        auto.

        apply InBlocksB_In in H1.
        contradict H1; auto.
 
      destruct H1 as [H1 | H1].
        apply blockEqB_inv in H1.
        inversion H1; subst. clear H1.
        apply InBlocksB_In in H0.
        contradict H0; auto.

        eapply IHlb; eauto.
          apply NoDup_split in H3.
          destruct H3.
          split; auto.
Qed.

Lemma blockInFdefB_uniq : forall l1 ps1 cs1 tmn1 ps2 cs2 tmn2 F,
  uniqFdef F ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F ->
  blockInFdefB (block_intro l1 ps2 cs2 tmn2) F ->
  ps1 = ps2 /\ cs1 = cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold blockInFdefB in *.
  destruct F.
  eapply InBlocksB_uniq; eauto.
Qed.

Lemma blockInSystemModuleFdef_uniq : forall l1 ps1 cs1 tmn1 ps2 cs2 tmn2 S M F,
  uniqFdef F ->
  blockInSystemModuleFdef (block_intro l1 ps1 cs1 tmn1) S M F ->
  blockInSystemModuleFdef (block_intro l1 ps2 cs2 tmn2) S M F ->
  ps1 = ps2 /\ cs1 = cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold blockInSystemModuleFdef in *.
  unfold blockInSystemModuleFdefB in *.
  apply andb_true_iff in H0.
  apply andb_true_iff in H1.
  destruct H0.
  destruct H1.
  eapply blockInFdefB_uniq; eauto.
Qed.

Lemma uniqProducts__uniqFdef : forall Ps F,
  uniqProducts Ps ->
  InProductsB (product_fdef F) Ps ->
  uniqFdef F.
Proof.
  induction Ps; intros.
    inversion H0.
    
    simpl in *.
    destruct H.
    apply orb_prop in H0.
    destruct H0; eauto.
      apply productEqB_inv in H0. subst.
      simpl in H. auto.
Qed.

Lemma uniqSystem__uniqFdef : forall S F M,
  uniqSystem S ->
  productInSystemModuleB (product_fdef F) S M ->
  uniqFdef F.
Proof.
  induction S; intros.
    unfold productInSystemModuleB in H0.
    apply andb_true_iff in H0.
    destruct H0.
    unfold moduleInSystemB in H0.
    inversion H0.

    unfold productInSystemModuleB in H0.
    apply andb_true_iff in H0.
    destruct H0.
    unfold moduleInSystemB in H0.
    inversion H0. clear H0.
    apply orb_prop in H3.
    simpl in H.
    destruct H as [J1 J2].
    destruct H3 as [H3 | H3].
      apply moduleEqB_inv in H3. subst.
      destruct a.
      simpl in H1. simpl in J1. destruct J1.
      eapply uniqProducts__uniqFdef; eauto.

      apply IHS with (M:=M); auto.
        unfold productInSystemModuleB.
        eapply andb_true_iff; auto.
Qed.

(* preservation *)

Definition dbInsn_preservation_prop state1 state2 tr
  (db:dbInsn state1 state2 tr) :=
  forall S TD Ps F l ps cs tmn lc arg als ECs gl Mem cs0,
  state1 = (mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem) ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro TD Ps) F ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists gl', exists Mem', exists cs0',
  state2 = (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem') /\
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S (module_intro TD Ps) F.
Definition dbop_preservation_prop state1 state2 tr
  (db:dbop state1 state2 tr) :=
  forall S TD Ps F l ps cs tmn lc arg als ECs gl Mem l' ps' cs' tmn' lc' als' gl' Mem' cs0 cs0',
  state1 = (mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem) ->
  state2 = (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem') ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro TD Ps) F ->
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S (module_intro TD Ps) F.
Definition dbFdef_preservation_prop fid rt lp S TD Ps ECs lc gl Mem lc' gl' als' Mem' B' Rid oResult tr
  (db:dbFdef fid rt lp S TD Ps ECs lc gl Mem lc' gl' als' Mem' B' Rid oResult tr) :=
  moduleInSystem (module_intro TD Ps) S ->
  exists F, 
    lookupFdefViaIDFromProducts Ps fid = Some F /\
    blockInSystemModuleFdef B' S (module_intro TD Ps) F.

Lemma db_preservation : 
  (forall state1 state2 tr db, @dbInsn_preservation_prop state1 state2 tr db) /\
  (forall state1 state2 tr db, @dbop_preservation_prop state1 state2 tr  db) /\
  (forall fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr ECs db, 
    @dbFdef_preservation_prop fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr ECs db).
Proof.
(db_mutind_cases
  apply LLVMopsem.db_mutind with
    (P  := dbInsn_preservation_prop)
    (P0 := dbop_preservation_prop)
    (P1 := dbFdef_preservation_prop) Case);
  unfold dbInsn_preservation_prop, 
         dbop_preservation_prop, 
         dbFdef_preservation_prop; intros; subst;
  try solve [
  inversion H; subst;
  exists l0; exists ps; exists cs; exists tmn0;
  exists lc'; exists als0; exists gl'; exists Mem1;
  exists cs1; split; auto
    ].
Case "dbBranch".
  inversion H; subst. clear H.
  exists l'. exists ps'. exists cs'. exists tmn'.
  exists (switchToNewBasicBlock (block_intro l' ps' cs' tmn') (block_intro l0 ps cs0 (insn_br bid Cond l1 l2)) lc0). exists als0. exists gl0. exists Mem1.
  exists cs'. split; auto.
  apply andb_true_iff in H0.
  destruct H0.
  eapply andb_true_iff.
  split; auto.
    symmetry in e0.
    destruct c;
      apply lookupBlockViaLabelFromFdef_inv in e0;
      destruct e0; auto.

Case "dbBranch_uncond".
  inversion H; subst. clear H.
  exists l'. exists ps'. exists cs'. exists tmn'.
  exists (switchToNewBasicBlock (block_intro l' ps' cs' tmn') (block_intro l1 ps cs0 (insn_br_uncond bid l0)) lc0). exists als0. exists gl0. exists Mem1.
  exists cs'. split; auto.
  apply andb_true_iff in H0.
  destruct H0.
  eapply andb_true_iff.
  split; auto.
    symmetry in e.
    apply lookupBlockViaLabelFromFdef_inv in e.
    destruct e; auto.

Case "dbMalloc".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists gl'. exists Mem'.
  exists cs1. split; auto.

Case "dbFree".
  inversion H; subst. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists gl0. exists Mem'.
  exists cs1. split; auto.

Case "dbAlloca".
  inversion H; subst. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists (mb::als0). exists gl'. exists Mem'.
  exists cs1. split; auto.

Case "dbStore".
  inversion H; subst. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists gl0. exists Mem'.
  exists cs1. split; auto.

Case "dbCall".
  inversion H0; subst. clear H0.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc''. exists als0. exists gl''. exists Mem''.
  exists cs1. split; auto.
 
Case "dbop_nil".
  inversion H0; subst. auto.
  
Case "dbop_cons".
  apply H with (cs1:=cs)(lc0:=lc)(arg:=arg0)(als0:=als)(ECs0:=ECs)(gl0:=gl)(Mem:=Mem0) in H3; auto.
  clear H.
  destruct H3 as [l1 [ps1 [cs1 [tmn1 [lc1 [als1 [gl1 [Mem1 [cs1' [EQ H3]]]]]]]]]]; subst.
  eapply H0; eauto.

Case "dbFdef_func".
  exists (fdef_intro (fheader_intro rt fid la) lb).
  split; auto.
    eapply H; eauto using entryBlockInSystemBlockFdef.

Case "dbFdef_proc".
  exists (fdef_intro (fheader_intro rt fid la) lb).
  split; auto.
    eapply H; eauto using entryBlockInSystemBlockFdef.
Qed.

Lemma _dbInsn_preservation : forall state2 tr S TD Ps F l ps cs tmn lc arg als ECs gl Mem cs0,
  dbInsn ((mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem)) state2 tr ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro TD Ps) F ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists gl', exists Mem', exists cs0',
  state2 = (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem') /\
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
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro TD Ps) F ->
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S (module_intro TD Ps) F.
Proof.
  intros.
  apply _dbInsn_preservation in H; auto.
  destruct H as [l1 [ps1 [cs1 [tmn1 [lc1 [als1 [gl1 [Mem1 [cs2 [J1 J2]]]]]]]]]].
  inversion J1; subst. clear J1. auto.  
Qed.

Lemma dbop_preservation : forall tr S TD Ps F l ps cs tmn lc arg als ECs gl Mem l' ps' cs' tmn' lc' als' gl' Mem' cs0 cs0',
  dbop 
    (mkState S TD Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' Mem')
    tr ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro TD Ps) F ->
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S (module_intro TD Ps) F.
Proof.
  intros.
  destruct db_preservation as [_ [J _]].
  unfold dbop_preservation_prop in J.
  eapply J; eauto.
Qed.

Lemma dbFdef_preservation : forall fid rt lp S TD Ps ECs lc gl Mem lc' gl' als' Mem' B' Rid oResult tr,
  dbFdef fid rt lp S TD Ps ECs lc gl Mem lc' gl' als' Mem' B' Rid oResult tr ->
  moduleInSystem (module_intro TD Ps) S ->
  exists F, 
    lookupFdefViaIDFromProducts Ps fid = Some F /\
    blockInSystemModuleFdef B' S (module_intro TD Ps) F.
Proof.
  intros.
  destruct db_preservation as [_ [_ J]].
  unfold dbFdef_preservation_prop in J.
  eapply J; eauto.
Qed.

