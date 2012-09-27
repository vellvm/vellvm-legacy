Require Import vellvm.
Require Import palloca_props.

Definition partitioning (c1 c2:cmd) (cs2:cmds) (b:block) (pinfo:PhiInfo) 
  (p: cmds -> PhiInfo -> Prop) : Prop :=
blockInFdefB b (PI_f pinfo) = true /\
p cs2 pinfo /\
let '(_, stmts_intro _ cs _) := b in
exists cs1, exists cs3,
  cs = cs1 ++ c1 :: cs2 ++ c2 :: cs3.

Ltac destruct_par :=
match goal with
| par: partitioning _ _ _ ?b _ _ |- _ =>
  destruct b as [P_l0 [P_ps0 P_cs0 P_tmn0]];
  destruct par as [P_BInF0 [P_p [P_cs1 [P_cs3 P_EQ]]]]; subst; simpl
end.

Lemma par_lookup_id2__c2: forall c1 c2 cs2 b pinfo p 
  (H:partitioning c1 c2 cs2 b pinfo p)
  (Huniq: uniqFdef (PI_f pinfo)),
  lookupInsnViaIDFromFdef (PI_f pinfo) (getCmdLoc c2) = ret insn_cmd c2.
Proof.
  intros.
  destruct_par.
  match goal with 
  | H: context [?A1++?a2::?A3++?a4::?A5] |- _ =>
       rewrite_env ((A1++a2::A3)++a4::A5) in H;
       eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H; 
         eauto using in_middle
  end.
Qed.  

Lemma par_id2__in_block_Locs: forall c1 c2 cs2 b (pinfo : PhiInfo) p
  (H:partitioning c1 c2 cs2 b pinfo p),
  In (getCmdLoc c2) (getStmtsLocs (snd b)).
Proof.
  intros.
  destruct_par.
  simpl; xsolve_in_list.
Qed.

Lemma par_id1__in_block_locs: forall c1 c2 cs2 b pinfo p
  (H:partitioning c1 c2 cs2 b pinfo p),
  In (getCmdLoc c1) (getStmtsLocs (snd b)).
Proof.
  intros.
  destruct_par.
  repeat simpl_locs.
  xsolve_in_list.
Qed.

Lemma par_id2__in_block_locs: forall c1 c2 cs2 b pinfo p
  (H:partitioning c1 c2 cs2 b pinfo p),
  In (getCmdLoc c2) (getStmtsLocs (snd b)).
Proof.
  intros.
  destruct_par.
  repeat simpl_locs.
  xsolve_in_list.
Qed.

Lemma par_block_eq: forall c1 c2 cs2 b pinfo p
  (H:partitioning c1 c2 cs2 b pinfo p) B (Huniq: uniqFdef (PI_f pinfo))
  (HBinF: blockInFdefB B (PI_f pinfo))
  (Hin: In (getCmdLoc c1) (getStmtsLocs (snd B)) \/
          In (getCmdLoc c2) (getStmtsLocs (snd B))),
  B = b.
Proof.
  intros.
  assert (J1:=@par_id1__in_block_locs c1 c2 cs2 b pinfo p H).
  assert (J2:=@par_id2__in_block_locs c1 c2 cs2 b pinfo p H).
  destruct_par.
  destruct Hin;
    eapply block_eq2; eauto 2.
Qed.

Lemma par_block_eq2: forall c1 c2 cs2 b (pinfo : PhiInfo) p
  (H:partitioning c1 c2 cs2 b pinfo p)
  (CurCmds : list cmd) (Terminator : terminator) (l' : l) (ps' : phinodes)
  (cs' : list cmd) (Huniq: uniqFdef (PI_f pinfo))
  (HbInF : blockInFdefB
            (l', stmts_intro ps'
               (cs' ++ c2 :: CurCmds) Terminator) (PI_f pinfo) = true),
  (l', stmts_intro ps' (cs' ++ c2 :: CurCmds) Terminator) = b.
Proof.
  intros.
  eapply par_block_eq; eauto.
    right. simpl.
    rewrite getCmdsLocs_app. simpl.
    rewrite_env ((getPhiNodesIDs ps' ++ getCmdsLocs cs') ++
                    getCmdLoc c2 :: getCmdsLocs CurCmds ++ 
                    getTerminatorID Terminator :: nil).
    apply in_middle.
Qed.

Lemma par_id2__in_block_IDs: forall c1 c2 cs2 b (pinfo : PhiInfo) p id2
  (H:partitioning c1 c2 cs2 b pinfo p) (Hget: getCmdID c2 = Some id2),
  In id2 (getStmtsIDs (snd b)).
Proof.
  intros.
  destruct_par. 
  simpl_env.
  repeat (rewrite getCmdsIDs_app; apply in_or_app; right).
  simpl. rewrite Hget. xsolve_in_list.
Qed.

Lemma par_lookup_id2__block: forall c1 c2 cs2 b (pinfo : PhiInfo) p id2
  (H:partitioning c1 c2 cs2 b pinfo p) (Hget: getCmdID c2 = Some id2)
  (Huniq: uniqFdef (PI_f pinfo)),
  lookupBlockViaIDFromFdef (PI_f pinfo) id2 = Some b.
Proof.
  intros.
  apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
    eapply par_id2__in_block_IDs; eauto.
    destruct_par. auto.
Qed.

Lemma par_block__reachable: forall c1 c2 cs2 b (pinfo : PhiInfo) p id2
  (H:partitioning c1 c2 cs2 b pinfo p) (Huniq : uniqFdef (PI_f pinfo))
  (Hreach : isReachableFromEntry (PI_f pinfo) b) (Hget: getCmdID c2 = Some id2),
  forall (b2 : block)
    (H0: lookupBlockViaIDFromFdef (PI_f pinfo) id2 = ret b2),
    isReachableFromEntry (PI_f pinfo) b2.
Proof.
  intros.
  erewrite par_lookup_id2__block in H0; eauto.
  inv H0. auto.
Qed.

Lemma par_lookup_id1__c1: forall c1 c2 cs2 b pinfo p 
  (H:partitioning c1 c2 cs2 b pinfo p)
  (Huniq: uniqFdef (PI_f pinfo)),
  lookupInsnViaIDFromFdef (PI_f pinfo) (getCmdLoc c1) = ret insn_cmd c1.
Proof.
  intros.
  destruct_par.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in P_BInF0;eauto using in_middle.
Qed.

Lemma par_block__reachable': forall c1 c2 cs2 b pinfo p id2
  (H:partitioning c1 c2 cs2 b pinfo p)
  (Huniq : uniqFdef (PI_f pinfo)) (Hget: getCmdID c2 = Some id2)
  (Hreach: id_in_reachable_block (PI_f pinfo) id2),
  isReachableFromEntry (PI_f pinfo) b.
Proof.
  intros. apply Hreach. eapply par_lookup_id2__block; eauto.
Qed.

Lemma par_id1__eq__c1: forall l1 ps1 cs1 c1 c2 cs2 b pinfo p
  (H:partitioning c1 c2 cs2 b pinfo p)
  (HuniqF: uniqFdef (PI_f pinfo)) tmn1
  (HBinF: blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) (PI_f pinfo)) c
  (Hin: In c cs1) (Heq: getCmdLoc c = getCmdLoc c1),
  c = c1.
Proof.
  intros.
  assert ((l1, stmts_intro ps1 cs1 tmn1) = b) as EQ.
    eapply par_block_eq; eauto.
      rewrite <- Heq.
      simpl. left. xsolve_in_list.
  destruct_par. simpl in *. inv EQ.
  eapply NoDup_getCmdsLocs_prop; eauto.
    solve_NoDup.
    solve_in_list.
Qed.

Lemma par_id2__eq__c2: forall l1 ps1 cs1 c1 c2 cs2 b pinfo p
  (H:partitioning c1 c2 cs2 b pinfo p)
  (HuniqF: uniqFdef (PI_f pinfo)) tmn1
  (HBinF: blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) (PI_f pinfo)) c
  (Hin: In c cs1) (Heq: getCmdLoc c = getCmdLoc c2),
  c = c2.
Proof.
  intros.
  assert ((l1, stmts_intro ps1 cs1 tmn1) = b) as EQ.
    eapply par_block_eq; eauto.
      rewrite <- Heq.
      simpl. right. xsolve_in_list.
  destruct_par. simpl in *. inv EQ.
  eapply NoDup_getCmdsLocs_prop; eauto.
    solve_NoDup.
    solve_in_list.
Qed.

Lemma par_blockInFdefB: forall c1 c2 cs2 b pinfo p
  (H:partitioning c1 c2 cs2 b pinfo p),
  blockInFdefB b (PI_f pinfo) = true.
Proof.
  intros.
  destruct_par. auto.
Qed.

Lemma par_block_inv1: forall l1 ps1 cs11 cs tmn2 c1 c2 cs2 b pinfo p
  (H:partitioning c1 c2 cs2 b pinfo p) (Huniq: uniqFdef (PI_f pinfo)) c0
  (EQ : (l1, stmts_intro ps1
         (cs11 ++
          c0 :: cs) tmn2) = b) (Heq: getCmdLoc c0 = getCmdLoc c1),
  c0 = c1 /\
  exists cs3, 
    cs = cs2 ++ c2 :: cs3.
Proof.
  intros.  
  assert (blockInFdefB b (PI_f pinfo)) as HBinF.
    eapply par_blockInFdefB; eauto.
  assert (EQ':=HBinF). rewrite <- EQ in EQ'.
  eapply par_id1__eq__c1 in EQ'; simpl; eauto using in_middle.
  split; auto.
  destruct_par. simpl in *. clear HBinF.
  inv EQ.
  apply NoDup_cmds_split_middle in H2; auto.
    destruct H2; subst. eauto.
    
    rewrite H2.
    solve_NoDup.
Qed.

Lemma par_block_inv2: forall l1 ps1 cs11 cs tmn2 c1 c2 cs2 b pinfo p
  (H:partitioning c1 c2 cs2 b pinfo p) (Huniq: uniqFdef (PI_f pinfo)) c0
  (EQ : (l1, (stmts_intro ps1
         (cs ++ c0 :: cs11) tmn2)) = b) (Heq: getCmdLoc c0 = getCmdLoc c2),
  c0 = c2 /\
  exists cs3, 
    cs = cs3 ++ c1 :: cs2.
Proof.
  intros.  
  assert (blockInFdefB b (PI_f pinfo)) as HBinF.
    eapply par_blockInFdefB; eauto.
  assert (EQ':=HBinF). rewrite <- EQ in EQ'.
  eapply par_id2__eq__c2 in EQ'; simpl; eauto using in_middle.
  split; auto.
  destruct_par. simpl in *. clear HBinF.
  inv EQ.
  match goal with
  | H: _ = ?A ++ ?b :: ?C ++ ?d :: ?E |- _ =>
     rewrite_env ((A ++ b :: C) ++ d :: E) in H
  end.
  apply NoDup_cmds_split_middle in H2; auto.
    destruct H2; subst. eauto.
    rewrite H2. simpl_env. simpl. solve_NoDup.
Qed.

