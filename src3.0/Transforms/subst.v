Require Import vellvm.
Require Import primitives.
Require Import top_wfS.

Lemma subst_block__getBlockLabel: forall i0 v0 b,
  getBlockLabel b = getBlockLabel (subst_block i0 v0 b).
Proof.
  destruct b as [l0 ? ? ?]; simpl; auto.
Qed.

Lemma subst_tmn__tmn_match: forall i0 v0 t, 
  terminator_match t (subst_tmn i0 v0 t).
Proof. destruct t; simpl; auto. Qed.

Lemma subst_block__tmn_match: forall i0 v0 b, 
  terminator_match (getBlockTmn b) (getBlockTmn (subst_block i0 v0 b)).
Proof. 
  destruct b as [l0 ? ? t0]; simpl.
  apply subst_tmn__tmn_match.
Qed.

Lemma subst_fdef_spec2: forall i0 v0 fh bs, 
  subst_fdef i0 v0 (fdef_intro fh bs) = 
    fdef_intro fh (List.map (subst_block i0 v0) bs).
Proof. simpl. auto. Qed.

Definition Subst i0 v0 := mkPass 
(subst_block i0 v0)
(subst_fdef i0 v0)
(subst_fdef_spec2 i0 v0)
(subst_block__getBlockLabel i0 v0)
(subst_block__tmn_match i0 v0)
.

Ltac fold_subst_tac :=
repeat match goal with
| |- context [subst_fdef ?id0 ?v0 ?f] =>
  replace (subst_fdef id0 v0 f) with (ftrans (Subst id0 v0) f); auto
| |- context [subst_block ?id0 ?v0 ?b] =>
  replace (subst_block id0 v0 b) with (btrans (Subst id0 v0) b); auto
| |- context [subst_fdef ?id0 ?v0] =>
  replace (subst_fdef id0 v0) with (ftrans (Subst id0 v0)); auto
| |- context [subst_block ?id0 ?v0] =>
  replace (subst_block id0 v0) with (btrans (Subst id0 v0)); auto
end.

Ltac unfold_subst_tac :=
repeat match goal with
| |- context [ftrans (Subst ?id0 ?v0) ?f] =>
  replace (ftrans (Subst id0 v0) f) with (subst_fdef id0 v0 f); auto
| |- context [btrans (Subst ?id0 ?v0) ?b] =>
  replace (btrans (Subst id0 v0) b) with (subst_block id0 v0 b); auto
| |- context [ftrans (Subst ?id0 ?v0)] =>
  replace (ftrans (Subst id0 v0)) with (subst_fdef id0 v0); auto
| |- context [btrans (Subst ?id0 ?v0)] =>
  replace (btrans (Subst id0 v0)) with (subst_block id0 v0); auto
end.

Lemma subst_reachablity_analysis : forall f id' v',
  reachablity_analysis f =
    reachablity_analysis (subst_fdef id' v' f).
Proof.
  intros.
  fold_subst_tac.
  apply TransCFG.pres_reachablity_analysis.
Qed.

Lemma subst_successors : forall f id' v',
  successors f = successors (subst_fdef id' v' f).
Proof.
  intros.
  fold_subst_tac.
  apply TransCFG.pres_successors.
Qed.

Section Uniqness.

Variable (f f':fdef) (id0:id) (v0:value).
Hypothesis (HeqF': f' = subst_fdef id0 v0 f) (HuniqF: uniqFdef f).

Lemma subst_getPhiNodesIDs : forall ps,
  getPhiNodesIDs (List.map (subst_phi id0 v0) ps) = getPhiNodesIDs ps.
Proof.
  induction ps; simpl; intros; auto.
    destruct a. simpl in *. rewrite IHps; auto.
Qed.

Lemma subst_getCmdsLocs : forall cs,
  getCmdsLocs (List.map (subst_cmd id0 v0) cs) = getCmdsLocs cs.
Proof.
  induction cs; simpl; intros; auto.
    destruct a; simpl in *; rewrite IHcs; auto.
Qed.

Lemma subst_blocksLocs : forall (bs : blocks),
  getBlocksLocs (List.map (subst_block id0 v0) bs) = getBlocksLocs bs.
Proof.
  induction bs as [|[l0 ps0 cs0 tmn0] bs]; simpl; auto.
    rewrite subst_getPhiNodesIDs.
    rewrite subst_getCmdsLocs.
    rewrite IHbs.
    destruct tmn0; auto.
Qed.

Lemma subst_uniqBlocksLocs : forall (bs : blocks)
  (HuniqBs : NoDup (getBlocksLocs bs)),
  NoDup (getBlocksLocs (List.map (subst_block id0 v0) bs)).
Proof.
  intros. rewrite subst_blocksLocs. auto.
Qed.

Hint Resolve subst_uniqBlocksLocs : ssa_subst.

Lemma subst_uniqBlocks : forall (bs : blocks)
  (HuniqBs : uniqBlocks bs),
  uniqBlocks (List.map (subst_block id0 v0) bs).
Proof.
  intros.
  destruct HuniqBs as [J1 J2].
  split; auto with ssa_subst.
    fold_subst_tac.
    apply TransCFG.pres_uniqBlocksLabels; auto.
Qed.

Lemma subst_uniqFdef : uniqFdef f'.
Proof.
  intros. subst f'.
  destruct f as [[] bs]. simpl in *. 
  destruct HuniqF as [J1 J2].
  split.
    apply subst_uniqBlocks; auto.
    rewrite subst_blocksLocs. auto.
Qed.

End Uniqness.

Hint Resolve subst_uniqFdef : ssa_subst.

Section SubstBasic.

Variable (id0:id) (v0:value).

Lemma subst_InPhiNodesB : forall p ps,
  InPhiNodesB p ps = true ->
  InPhiNodesB (subst_phi id0 v0 p) (List.map (subst_phi id0 v0) ps) = true.
Proof.
  induction ps; simpl; intros.
    congruence.
    apply orb_true_iff in H.
    apply orb_true_iff.
    destruct H as [H | H]; auto.
    apply phinodeEqB_inv in H; subst.
    left. apply phinodeEqB_refl.
Qed.

Hint Resolve subst_InPhiNodesB: ssa_subst.

Lemma subst_phinodeInBlockB : forall p b
  (Hin : phinodeInBlockB p b = true),
  phinodeInBlockB (subst_phi id0 v0 p) (subst_block id0 v0 b) = true.
Proof.
  destruct b. simpl. intro. auto with ssa_subst.
Qed.

Hint Resolve subst_phinodeInBlockB: ssa_subst.

Lemma subst_InCmdsB : forall c cs,
  InCmdsB c cs = true ->
  InCmdsB (subst_cmd id0 v0 c) (List.map (subst_cmd id0 v0) cs) = true.
Proof.
  induction cs; simpl; intros.
    congruence.
    apply orb_true_iff in H.
    apply orb_true_iff.
    destruct H as [H | H]; auto.
    apply cmdEqB_inv in H; subst.
    left. apply cmdEqB_refl.
Qed.

Hint Resolve subst_InCmdsB: ssa_subst.

Lemma subst_cmdInBlockB : forall c b
  (Hin : cmdInBlockB c b = true),
  cmdInBlockB (subst_cmd id0 v0 c) (subst_block id0 v0 b) = true.
Proof.
  destruct b. simpl. intro. auto with ssa_subst.
Qed.

Hint Resolve subst_cmdInBlockB: ssa_subst.

Lemma subst_terminatorInBlockB : forall t b
  (Hin : terminatorInBlockB t b = true),
  terminatorInBlockB (subst_tmn id0 v0 t) (subst_block id0 v0 b) = true.
Proof.
  destruct b. simpl. intro.
  apply terminatorEqB_inv in Hin. subst.
  apply terminatorEqB_refl.
Qed.

Hint Resolve subst_terminatorInBlockB: ssa_subst.

Lemma subst_insnInFdefBlockB: forall f b instr
  (Hin: insnInFdefBlockB instr f b = true),
  insnInFdefBlockB (subst_insn id0 v0 instr)
    (subst_fdef id0 v0 f) (subst_block id0 v0 b) = true.
Proof.
  intros.
  apply destruct_insnInFdefBlockB in Hin.
  destruct Hin as [Hin1 Hin2].
  apply insnInFdefBlockB_intro.
    destruct instr; simpl; auto with ssa_subst.

    fold_subst_tac. 
    apply TransCFG.pres_blockInFdefB; auto.
Qed.

Hint Resolve subst_insnInFdefBlockB: ssa_subst.

Lemma subst_getCmdsIDs : forall cs,
  getCmdsIDs (List.map (subst_cmd id0 v0) cs) = getCmdsIDs cs.
Proof.
  induction cs; simpl; intros; auto.
    destruct a; simpl in *; rewrite IHcs; auto.
Qed.

Lemma subst_lookupBlockViaIDFromBlocks : forall id5 bs b,
  lookupBlockViaIDFromBlocks bs id5 = ret b ->
  lookupBlockViaIDFromBlocks (List.map (subst_block id0 v0) bs) id5 =
    ret (subst_block id0 v0 b).
Proof.
  induction bs as [|[l1 ps1 cs1 tmn1]]; simpl; intros.
    congruence.

    simpl in *.
    rewrite subst_getPhiNodesIDs.
    rewrite subst_getCmdsIDs.
    destruct_if; auto.
Qed.

Hint Resolve subst_lookupBlockViaIDFromBlocks : ssa_subst.

Lemma subst_lookupBlockViaIDFromFdef : forall f id5 b,
  lookupBlockViaIDFromFdef f id5 = ret b ->
  lookupBlockViaIDFromFdef (subst_fdef id0 v0 f) id5 =
    ret (subst_block id0 v0 b).
Proof.
  destruct f. simpl; intros. auto with ssa_subst.
Qed.

Hint Resolve subst_lookupBlockViaIDFromFdef: ssa_subst.

Lemma subst_isPhiNode : forall instr,
  isPhiNode instr = isPhiNode (subst_insn id0 v0 instr).
Proof.
  destruct instr; auto.
Qed.

Lemma subst_insnDominates : forall i0 instr b,
  NoDup (getBlockLocs b) ->
  insnInBlockB instr b = true ->
  (insnDominates i0 instr b <->
  insnDominates i0 (subst_insn id0 v0 instr) (subst_block id0 v0 b)).
Proof.
 intros i0 instr b Hnodup HiInB. destruct b. simpl.
 destruct instr; simpl; split; intro J; auto.
   destruct J as [[ps1 [p1 [ps2 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]];
     subst.
     left.
     exists (List.map (subst_phi id0 v0) ps1).
     exists (subst_phi id0 v0 p1).
     exists (List.map (subst_phi id0 v0) ps2).
     repeat rewrite List.map_app.
     destruct p1. simpl. auto.

     right.
     exists (List.map (subst_cmd id0 v0) cs1).
     exists (subst_cmd id0 v0 c1).
     exists (List.map (subst_cmd id0 v0) cs2).
     exists (List.map (subst_cmd id0 v0) cs3).
     simpl_env.
     repeat rewrite List.map_app.
     destruct c1; simpl in *; inv J2; auto.

   destruct J as [[ps1 [p1 [ps2 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]];
     subst.
     left.
     apply map_app_inv in J1. destruct J1 as [ps1' [ps2' [J1 [J2 J3]]]]; subst.
     destruct ps2'; inv J3.
     exists ps1'. exists p. exists ps2'.
     destruct p. simpl. auto.

     right.
     apply map_app_inv in J1. destruct J1 as [cs1' [cs2' [J1 [J3 J4]]]]. subst.
     destruct cs2'; inv J4.
     apply map_app_inv in H1. destruct H1 as [cs3' [cs4' [J1 [J3 J4]]]]; subst.
     destruct cs4'; inv J4.
     assert (c0 = cmd5) as EQ.
       simpl in *.
       assert (getCmdLoc cmd5 = getCmdLoc c0) as EQ'.
         destruct cmd5; destruct c0; inv H0; auto.
       apply NoDup_inv in Hnodup. inv Hnodup.
       apply NoDup_inv in H1. inv H1.
       rewrite_env ((cs1'++c::cs3')++c0::cs4') in HiInB.
       rewrite_env ((cs1'++c::cs3')++c0::cs4') in H2.
       eapply NoDup_getCmdsLocs_prop; eauto using In_middle, InCmdsB_in.
     subst.
     exists cs1'. exists c. exists cs3'. exists cs4'.
     destruct c; simpl in *; inv J2; auto.

   destruct J as [[[cs1 [c1 [cs2 [J1 J2]]]] | [ps1 [p1 [ps2 [J1 J2]]]]] Heq];
     subst; split; auto.
     left.
     exists (List.map (subst_cmd id0 v0) cs1).
     exists (subst_cmd id0 v0 c1).
     exists (List.map (subst_cmd id0 v0) cs2).
     simpl_env.
     repeat rewrite List.map_app.
     destruct c1; simpl in *; inv J2; auto.

     right.
     exists (List.map (subst_phi id0 v0) ps1).
     exists (subst_phi id0 v0 p1).
     exists (List.map (subst_phi id0 v0) ps2).
     repeat rewrite List.map_app.
     destruct p1. simpl. auto.

   simpl in *. apply terminatorEqB_inv in HiInB. subst.
   destruct J as [[[cs1 [c1 [cs2 [J1 J2]]]] | [ps1 [p1 [ps2 [J1 J2]]]]] Heq];
     subst; split; auto.
     left.
     apply map_app_inv in J1. destruct J1 as [cs1' [cs2' [J1 [J3 J4]]]]. subst.
     destruct cs2'; inv J4.
     exists cs1'. exists c. exists cs2'.
     destruct c; simpl in *; inv J2; auto.

     right.
     apply map_app_inv in J1. destruct J1 as [ps1' [ps2' [J1 [J2 J3]]]]; subst.
     destruct ps2'; inv J3.
     exists ps1'. exists p. exists ps2'.
     destruct p. simpl. auto.
Qed.

Lemma subst_lookupTypViaIDFromPhiNodes : forall id5 ps,
  lookupTypViaIDFromPhiNodes ps id5 =
    lookupTypViaIDFromPhiNodes (List.map (subst_phi id0 v0) ps) id5.
Proof.
  induction ps as [|[]]; simpl; intros; auto.
    unfold lookupTypViaIDFromPhiNode in *.
    simpl in *.
    destruct_if; auto.
Qed.

Lemma subst_lookupTypViaIDFromCmds : forall id5 cs,
  lookupTypViaIDFromCmds cs id5 =
    lookupTypViaIDFromCmds (List.map (subst_cmd id0 v0) cs) id5.
Proof.
  induction cs as [|c]; simpl; intros; auto.
    unfold lookupTypViaIDFromCmd in *.
    destruct c; simpl in *; try solve 
      [destruct_if; auto | destruct_if; destruct_if; auto].
Qed.

Lemma subst_lookupTypViaIDFromTerminator : forall id5 t,
  lookupTypViaIDFromTerminator t id5 =
    lookupTypViaIDFromTerminator (subst_tmn id0 v0 t) id5.
Proof.
  destruct t; auto.
Qed.

Lemma subst_lookupTypViaIDFromBlocks : forall id5 bs,
  lookupTypViaIDFromBlocks bs id5 =
    lookupTypViaIDFromBlocks (List.map (subst_block id0 v0) bs) id5.
Proof.
  induction bs as [|[? p c t]]; simpl; intros.
    congruence.

    simpl in *.
    rewrite IHbs.
    remember (lookupTypViaIDFromPhiNodes p id5) as R1.
    erewrite subst_lookupTypViaIDFromPhiNodes in HeqR1; eauto.
    rewrite HeqR1.
    remember (lookupTypViaIDFromCmds c id5) as R2.
    erewrite subst_lookupTypViaIDFromCmds in HeqR2; eauto.
    rewrite HeqR2.
    remember (lookupTypViaIDFromTerminator t id5) as R3.
    erewrite subst_lookupTypViaIDFromTerminator in HeqR3; eauto.
    rewrite HeqR3; auto.
Qed.

Lemma subst_lookupTypViaIDFromFdef : forall f id5,
  lookupTypViaIDFromFdef f id5 = 
    lookupTypViaIDFromFdef (subst_fdef id0 v0 f) id5.
Proof.
  destruct f. simpl. intros. rewrite <- subst_lookupTypViaIDFromBlocks; auto.
Qed.

Lemma subst_list_value_l__labels : forall vls,
  let '(_, ls1):=split vls in
  let '(_, ls2):=split (subst_list_value_l id0 v0 vls) in
  ls1 = ls2.
Proof.
  induction vls as [|[]]; simpl; auto.
    destruct (split vls).
    destruct (split (subst_list_value_l id0 v0 vls)).
    subst. auto.
Qed.

Lemma subst_check_list_value_l : forall f b vls
  (Hcl: check_list_value_l f b vls),
  check_list_value_l (subst_fdef id0 v0 f) (subst_block id0 v0 b)
    (subst_list_value_l id0 v0 vls).
Proof.
  unfold check_list_value_l. destruct f as [fh bs]. simpl. intros until vls.
  fold_subst_tac.
  repeat rewrite <- TransCFG.pres_genBlockUseDef_blocks.
  erewrite TransCFG.pres_predOfBlock.
  assert (J:=@subst_list_value_l__labels vls).
  destruct (split vls).
  destruct (split (subst_list_value_l id0 v0 vls)).
  subst. eauto.
Qed.

Lemma subst_getSubTypFromValueIdxs: forall svls typ5 t0 
  (Hget: getSubTypFromValueIdxs svls typ5 = Some t0),
  getSubTypFromValueIdxs (subst_list_value id0 v0 svls) typ5 = Some t0.
Proof.
  induction svls as [|[]]; simpl; intros; auto.
    destruct typ5; tinv Hget; auto.
    destruct v as [|[]]; tinv Hget.
    simpl. 
    remember (nth_error l0 (INTEGER.to_nat Int5)) as R.
    destruct R; tinv Hget. auto.
Qed.    

Lemma subst_getGEPTyp: forall t0 typ5 svls
  (Hget: getGEPTyp svls typ5 = Some t0),
  getGEPTyp (subst_list_value id0 v0 svls) typ5 = Some t0.
Proof.
  unfold getGEPTyp.
  destruct svls as [|[]]; simpl; auto.
    intros.
    inv_mbind.
    symmetry_ctx.
    apply subst_getSubTypFromValueIdxs in HeqR.
    fill_ctxhole. auto.
Qed.

Lemma subst_fheader: forall f,
  fheaderOfFdef f = fheaderOfFdef (subst_fdef id0 v0 f).
Proof.
  destruct f; auto.
Qed.

End SubstBasic.

Hint Resolve subst_insnInFdefBlockB subst_lookupBlockViaIDFromFdef
             subst_check_list_value_l subst_lookupTypViaIDFromFdef
             subst_getGEPTyp : ssa_subst.

Section SubstBasicSys.

Variable (los:layouts) (nts:namedts) (Ps1 Ps2:products)
         (M M':module) (f f':fdef) (id0:id) (v0:value).
Hypothesis (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
           (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
           (HeqF': f' = subst_fdef id0 v0 f).

Lemma subst_wf_typ: forall t,
  wf_typ [M] (los,nts) t -> wf_typ [M'] (los,nts) t.
Proof.
  subst.
  eapply TopWFS.subst_fdef_preserves_single_wf_typ; 
    eauto using subst_fheader.
Qed.

Lemma subst_wf_const: forall c t,
  wf_const [M] (los,nts) c t -> wf_const [M'] (los,nts) c t.
Proof.
  subst.
  eapply TopWFS.subst_fdef_preserves_single_wf_const;
    eauto using subst_fheader.
Qed.

Lemma subst_blockInSystemModuleFdefB: forall b b'
  (Heqb': b' = subst_block id0 v0 b) 
  (Hin: blockInSystemModuleFdefB b [M] M f),
  blockInSystemModuleFdefB b' [M'] M' f'.
Proof.
  intros.
  subst.
  apply blockInSystemModuleFdef_inv in Hin.
  destruct Hin as [J1 [J2 [J3 J4]]].
  apply blockInSystemModuleFdef_intro.
    fold_subst_tac.
    apply TransCFG.pres_blockInFdefB; auto.

    apply InProductsB_middle.

    unfold moduleInSystem. simpl.
    apply orb_true_intro.
    left. solve_refl.
Qed.

Lemma subst_preserves_wf_fheader: forall fh,
  wf_fheader [M] (los,nts) fh -> wf_fheader [M'] (los,nts) fh.
Proof.
  subst.
  eapply TopWFS.subst_fdef_preserves_single_wf_fheader; 
    eauto using subst_fheader.
Qed.

Lemma subst_wf_original_value : forall v t (Hwfv: wf_value [M] M f v t),
  wf_value [M'] M' f' v t.
Proof.
  intros.
  assert (J1:=subst_wf_const).
  assert (J3:=subst_wf_typ).
  subst. 
  inv Hwfv; uniq_result; try constructor; eauto.
    rewrite <- subst_lookupTypViaIDFromFdef; auto.
Qed.

End SubstBasicSys.

Hint Resolve subst_fheader subst_wf_typ subst_wf_const: ssa_subst.

Section CSubst.

Variable (id0:id) (c0:const).

Hint Unfold csubst_fdef csubst_block csubst_insn.

Fixpoint remove_from_list_id (id':id) (l0:list id) : list id :=
match l0 with
| nil => nil
| id0 :: tl =>
    if id_dec id0 id'
    then remove_from_list_id id' tl
    else id0 :: (remove_from_list_id id' tl)
end.

Lemma csubst_values2ids : forall l0 id_list0,
  values2ids (list_prj1 value l l0) = id_list0 ->
  values2ids
     (list_prj1 value l
       (subst_list_value_l id0 (value_const c0) l0)) =
    remove_from_list_id id0 id_list0.
Proof.
  induction l0 as [|[]]; simpl; intros; subst; auto.
    destruct v as [id5|]; simpl in *; auto.
      destruct (id_dec id5 id0); subst; simpl; auto.
        rewrite <- IHl0; auto.
Qed.

Hint Resolve csubst_values2ids : ssa_subst.

Lemma csubst_getPhiNodeOperands : forall p id_list0,
  getPhiNodeOperands p = id_list0 ->
  getPhiNodeOperands (subst_phi id0 (value_const c0) p) =
    (remove_from_list_id id0 id_list0).
Proof.
  destruct p; simpl; intros; auto with ssa_subst.
Qed.

Lemma remove_from_list_id_app: forall id' ids2 ids1,
  remove_from_list_id id' ids1 ++ remove_from_list_id id' ids2 =
    remove_from_list_id id' (ids1 ++ ids2).
Proof.
  induction ids1; simpl; auto.
    destruct_if.
    simpl_env. congruence.
Qed.

Lemma csubst_getValueIDs : forall v id_list0
  (H : getValueIDs v = id_list0),
  getValueIDs (v {[value_const c0 // id0]}) =
   (remove_from_list_id id0 id_list0).
Proof.
  intros.
  destruct v as [vid|]; subst. simpl.
    destruct_if; subst; simpl; auto.
    auto.
Qed.

Lemma csubst_getValueIDs2 : forall v v0 id_list0
  (H : getValueIDs v ++ getValueIDs v0 = id_list0),
  getValueIDs (v {[value_const c0 // id0]}) ++
  getValueIDs (v0 {[value_const c0 // id0]}) =
   (remove_from_list_id id0 id_list0).
Proof.
  intros.
  subst.
  rewrite <- remove_from_list_id_app.
  repeat erewrite csubst_getValueIDs; eauto.
Qed.

Hint Resolve csubst_getValueIDs2
             csubst_getValueIDs: ssa_subst.

Lemma csubst_values2ids' : forall l0,
  values2ids (List.map snd (subst_list_value id0 (value_const c0) l0)) =
    remove_from_list_id id0 (values2ids (List.map snd l0)).
Proof.
  induction l0 as [|[]]; simpl; auto.
    destruct v as [vid|]; subst; simpl; auto.
    destruct_if. rewrite IHl0. auto.
Qed.

Lemma csubst_getParamsOperand: forall params5,
  getParamsOperand
     (List.map
        (fun p : typ * attributes * value =>
         let '(t, v) := p in (t, v {[value_const c0 // id0]})) params5) =
    remove_from_list_id id0 (getParamsOperand params5).
Proof.
  unfold getParamsOperand. 
  induction params5 as [|[[]]]; simpl; auto.
  match goal with
  | _:context [split ?e] |- _ => 
      remember (split e) as R; destruct R
  end.
  match goal with
  | |- context [split ?e] => 
      remember (split e) as R; destruct R
  end.
  simpl. 
  destruct v; simpl; auto.
    destruct_if.
      congruence.
Qed.

Lemma csubst_getCmdOperands : forall c id_list0,
 getCmdOperands c = id_list0 ->
 getCmdOperands (subst_cmd id0 (value_const c0) c) =
   (remove_from_list_id id0 id_list0).
Proof.
  destruct c; simpl; intros; auto with ssa_subst.
    subst.
    rewrite <- remove_from_list_id_app.
    erewrite csubst_getValueIDs; eauto.
    rewrite csubst_values2ids'; auto.

    subst.
    repeat rewrite <- remove_from_list_id_app.
    repeat erewrite csubst_getValueIDs; eauto.

    subst.
    repeat rewrite <- remove_from_list_id_app.
    erewrite csubst_getValueIDs; eauto.
    rewrite csubst_getParamsOperand; auto.
Qed.

Lemma csubst_getTerminatorOperands : forall t id_list0,
 getTerminatorOperands t = id_list0 ->
 getTerminatorOperands (subst_tmn id0 (value_const c0) t) =
   (remove_from_list_id id0 id_list0).
Proof.
  destruct t; simpl; intros; 
    try solve [simpl; auto with ssa_subst | subst; auto].
Qed.

Hint Resolve csubst_getCmdOperands csubst_getPhiNodeOperands
  csubst_getTerminatorOperands: ssa_subst.

Lemma csubst_getInsnOperands : forall instr id_list0,
  getInsnOperands instr = id_list0 ->
  getInsnOperands (csubst_insn id0 c0 instr) = 
    (remove_from_list_id id0 id_list0).
Proof.
  destruct instr; simpl; intros; auto with ssa_subst.
Qed.

Lemma csubst_In_values2ids : forall i0 l0
  (n : i0 <> id0)
  (H2 : ListSet.set_In i0
    (values2ids (list_prj1 value l l0))),
  ListSet.set_In i0
    (values2ids
      (list_prj1 value l
        (subst_list_value_l id0 (value_const c0) l0))).
Proof.
  induction l0 as [|[v]]; simpl; intros; auto.
    destruct v as [vid|]; simpl in *; auto.
    destruct H2 as [H2 | H2]; subst.
      destruct_if; try congruence; simpl; auto.
      destruct_if; subst; simpl; auto.
Qed.

Hint Resolve csubst_In_values2ids : ssa_subst.

Lemma csubst_In_getPhiNodeOperands : forall i0 p
  (n : i0 <> id0)
  (H2 : ListSet.set_In i0 (getPhiNodeOperands p)),
  ListSet.set_In i0 (getPhiNodeOperands (subst_phi id0 (value_const c0) p)).
Proof.
  destruct p; simpl; intros; auto with ssa_subst.
Qed.

Lemma csubst_In_getValueIDs : forall v i3
  (n : i3 <> id0)
  (H2 : ListSet.set_In i3 (getValueIDs v)),
  ListSet.set_In i3 (getValueIDs (v {[value_const c0 // id0]})).
Proof.
  intros.
  destruct v as [vid|]; simpl in *; auto.
    destruct H2 as [H2 | H2]; subst.
      destruct_if.
        congruence.
        simpl; auto.
      tauto.
Qed.

Lemma csubst_In_getValueIDs2 : forall v v0 i3
  (n : i3 <> id0)
  (H2 : ListSet.set_In i3 (getValueIDs v ++ getValueIDs v0)),
  ListSet.set_In i3 (getValueIDs (v {[value_const c0 // id0]}) ++
                     getValueIDs (v0 {[value_const c0 // id0]})).
Proof.
  intros.
  unfold ListSet.set_In in *.
  destruct_in H2;
    apply csubst_In_getValueIDs in H2; auto; xsolve_in_list.
Qed.

Hint Resolve csubst_In_getValueIDs csubst_In_getValueIDs2: ssa_subst.

Lemma csubst_In_values2ids' : forall i0 l0
  (n : i0 <> id0)
  (H2 : ListSet.set_In i0
    (values2ids (List.map snd l0))),
  ListSet.set_In i0
    (values2ids
      (List.map snd (subst_list_value id0 (value_const c0) l0))).
Proof.
  induction l0 as [|[]]; simpl; intros; auto.
    destruct v as [vid|]; subst; simpl; auto.
    unfold ListSet.set_In in *.
    destruct_in H2.
      destruct_if; simpl; auto.
      congruence.

      destruct_if; simpl; auto.
Qed.

Lemma csubst_In_getParamsOperand: forall i0 params5
  (n : i0 <> id0)
  (H2 : ListSet.set_In i0 (getParamsOperand params5)),
  ListSet.set_In i0
    (getParamsOperand
      (List.map
        (fun p : typ * attributes * value =>
         let '(t, v) := p in (t, v {[value_const c0 // id0]})) params5)).
Proof.
  unfold getParamsOperand. 
  induction params5 as [|[[]]]; simpl; intros; auto.
  match goal with
  | _:context [split ?e] |- _ => 
      remember (split e) as R; destruct R
  end.
  match goal with
  | |- context [split ?e] => 
      remember (split e) as R; destruct R
  end.
  simpl. 
  destruct v; simpl; auto.
    simpl in H2.
    destruct H2 as [H2 | H2]; subst.
      destruct_if; simpl; auto.
      congruence.

      destruct_if; simpl; auto.
Qed.

Lemma csubst_In_getCmdOperands : forall c i3
  (n : i3 <> id0)
  (H2 : ListSet.set_In i3 (getCmdOperands c)),
  ListSet.set_In i3 (getCmdOperands (subst_cmd id0 (value_const c0) c)).
Proof.
  destruct c; simpl; intros; auto with ssa_subst.
    unfold ListSet.set_In in *.
    destruct_in H2.
      apply csubst_In_getValueIDs in H2; auto. xsolve_in_list.
      apply csubst_In_values2ids' in H2; auto. xsolve_in_list.

    unfold ListSet.set_In in *.
    destruct_in H2.
      apply csubst_In_getValueIDs in H2; auto; xsolve_in_list.
    destruct_in H2;
      apply csubst_In_getValueIDs in H2; auto; xsolve_in_list.

    unfold ListSet.set_In in *.
    destruct_in H2.
      apply csubst_In_getValueIDs in H2; auto. xsolve_in_list.
      apply csubst_In_getParamsOperand in H2; auto. xsolve_in_list.
Qed.

Lemma csubst_In_getTerminatorOperands : forall t i3
  (n : i3 <> id0)
  (H2 : ListSet.set_In i3 (getTerminatorOperands t)),
  ListSet.set_In i3 (getTerminatorOperands(subst_tmn id0 (value_const c0) t)).
Proof.
  destruct t; simpl; intros; auto with ssa_subst.
Qed.

Hint Resolve csubst_In_getCmdOperands csubst_In_getPhiNodeOperands
  csubst_In_getTerminatorOperands: ssa_subst.

Lemma csubst_In_getInsnOperands : forall i0 instr
  (n : i0 <> id0)
  (H2 : ListSet.set_In i0 (getInsnOperands instr)),
  ListSet.set_In i0
     (getInsnOperands (csubst_insn id0 c0 instr)).
Proof.
  destruct instr; simpl; auto with ssa_subst.
Qed.

Hint Resolve csubst_In_getInsnOperands: ssa_subst.

Lemma csubst_wf_operand : forall instr f b i0
  (Huniq : NoDup (getBlockLocs b))
  (H1 : wf_operand f b instr i0)
  (n : i0 <> id0),
   wf_operand (csubst_fdef id0 c0 f) (csubst_block id0 c0 b)
     (csubst_insn id0 c0 instr) i0.
Proof.
  intros.
  inv H1.
  eapply wf_operand_intro; try solve
    [eauto with ssa_subst | autounfold; eauto with ssa_subst].

    autounfold.
    rewrite <- subst_isPhiNode; auto.

    autounfold.
    fold_subst_tac.
    rewrite <- TransCFG.pres_getArgsIDsOfFdef; auto.
    rewrite <- TransCFG.pres_isReachableFromEntry; auto.
    destruct H4 as [[[b' [J1 J2]] | H4] | H4]; auto.
    left. left.
    exists (subst_block id0 (value_const c0) b').
    simpl.
    split.
      apply subst_lookupBlockViaIDFromFdef; auto.

      rewrite <- subst_insnDominates; eauto using insnInFdefBlockB__insnInBlockB.
      fold_subst_tac.
      rewrite <- TransCFG.pres_blockStrictDominates. auto.
Qed.

Hint Resolve csubst_wf_operand: ssa_subst.

Lemma csubst_wf_operand_list : forall instr f b 
  (Huniq : NoDup (getBlockLocs b)) id_list0
  (H2 : forall id_ : id,
          In id_ (List.map (fun id_0 : id => id_0) id_list0) ->
          wf_operand f b instr id_),
  forall id_ : id,
    In id_ (List.map (fun id_0 : id => id_0) 
              (remove_from_list_id id0 id_list0)) ->
    wf_operand (csubst_fdef id0 c0 f) (csubst_block id0 c0 b)
      (csubst_insn id0 c0 instr) id_.
Proof.
  induction id_list0 as [|a]; simpl; intros; auto.
    tauto.
  
    destruct (id_dec a id0); subst; auto.
      simpl in H.
      destruct H as [H | H]; subst.
        auto with ssa_subst.
        apply IHid_list0; auto.
Qed.

Hint Resolve csubst_getInsnOperands csubst_wf_operand_list: ssa_subst.

Lemma csubst_wf_insn_base : forall f b instr
  (Huniq : NoDup (getBlockLocs b))
  (HwfI: wf_insn_base f b instr),
  wf_insn_base (csubst_fdef id0 c0 f) (csubst_block id0 c0 b)
    (csubst_insn id0 c0 instr).
Proof.
  intros.
  inv HwfI.
  eapply subst_insnInFdefBlockB in H; eauto.
  eapply csubst_getInsnOperands in H1; eauto.
  eapply wf_insn_base_intro; eauto with ssa_subst.
Qed.

Hint Constructors wf_phi_operands.

Lemma csubst_wf_phi_operands : forall f b ty id' vls
  (Hwf_pnops: wf_phi_operands f b id' ty vls),
  wf_phi_operands (csubst_fdef id0 c0 f) (csubst_block id0 c0 b) id' ty
    (subst_list_value_l id0 (value_const c0) vls).
Proof.
  intros.
  induction Hwf_pnops; simpl; auto.
    destruct (id_dec vid1 id0); auto.
    eapply wf_phi_operands_cons_vid; eauto.
      autounfold. fold_subst_tac.
      eapply TransCFG.pres_lookupBlockViaLabelFromFdef in H; eauto.

      autounfold.
      fold_subst_tac.
      rewrite <- TransCFG.pres_getArgsIDsOfFdef; auto.
      rewrite <- TransCFG.pres_isReachableFromEntry; auto.
      destruct H0 as [[[vb [J1 J2]] | H0] | H0]; auto.
      left. left.
      exists (csubst_block id0 c0 vb).
      autounfold.
      fold_subst_tac.
      rewrite <- TransCFG.pres_blockDominates; auto.
      simpl.
      eapply subst_lookupBlockViaIDFromFdef in J1; eauto.
Qed.

End CSubst.

Section ISubst.

Variable (id1:id) (id2:id) (f:fdef).

Definition subst_id (id1 id2 : id) (id0:id) : id :=
if id_dec id0 id1 then id2 else id0.

Fixpoint subst_list_id (id1 id2 : id) (l0:list id) : list id :=
match l0 with
| nil => nil
| id0 :: tl =>
    (subst_id id1 id2 id0) :: (subst_list_id id1 id2 tl)
end.

Lemma isubst_values2ids : forall l0 id_list0,
  values2ids (list_prj1 value l l0) = id_list0 ->
  values2ids
    (list_prj1 value l
       (subst_list_value_l id2 (value_id id1) l0)) =
    subst_list_id id2 id1 id_list0.
Proof.
  induction l0 as [|[]]; simpl; intros; subst; auto.
    destruct v as [vid|c]; simpl in *; unfold subst_id; auto.
      rewrite <- IHl0; auto.
      destruct_if.
Qed.

Hint Resolve isubst_values2ids : ssa_subst.

Lemma isubst_getPhiNodeOperands : forall p id_list0,
  getPhiNodeOperands p = id_list0 ->
  getPhiNodeOperands (subst_phi id2 (value_id id1) p) =
    subst_list_id id2 id1 id_list0.
Proof.
  destruct p; simpl; intros; auto with ssa_subst.
Qed.

Lemma subst_list_id_app: forall id' id'' ids2 ids1,
  subst_list_id id' id'' ids1 ++ subst_list_id id' id'' ids2 =
    subst_list_id id' id'' (ids1 ++ ids2).
Proof.
  induction ids1; simpl; auto.
    rewrite IHids1; auto.
Qed.

Lemma isubst_getValueIDs : forall v id_list0
  (H : getValueIDs v = id_list0),
  getValueIDs (v {[value_id id1 // id2]}) = subst_list_id id2 id1 id_list0.
Proof.
  intros.
  destruct v as [|vod]; subst; simpl in *; unfold subst_id; auto.
    destruct_if; subst; simpl; auto.
Qed.

Lemma isubst_getValueIDs2 : forall v v0 id_list0
  (H : getValueIDs v ++ getValueIDs v0 = id_list0),
  getValueIDs (v {[value_id id1 // id2]}) ++
  getValueIDs (v0 {[value_id id1 // id2]}) = subst_list_id id2 id1 id_list0.
Proof.
  intros.
  subst.
  rewrite <- subst_list_id_app.
  repeat erewrite isubst_getValueIDs; eauto.
Qed.

Hint Resolve isubst_getValueIDs2
             isubst_getValueIDs: ssa_subst.

Lemma isubst_values2ids' : forall l0,
  values2ids (List.map snd (subst_list_value id2 (value_id id1) l0)) =
    subst_list_id id2 id1 (values2ids (List.map snd l0)).
Proof.
  induction l0 as [|[]]; simpl; auto.
    destruct v as [vid|]; subst; simpl; auto.
    unfold subst_id. rewrite IHl0. 
    destruct_if. 
Qed.

Lemma isubst_getParamsOperand: forall params5,
  getParamsOperand
     (List.map
        (fun p : typ * attributes * value =>
         let '(t, v) := p in (t, v {[value_id id1 // id2]})) params5) =
    subst_list_id id2 id1 (getParamsOperand params5).
Proof.
  unfold getParamsOperand. 
  induction params5 as [|[[]]]; simpl; auto.
  match goal with
  | _:context [split ?e] |- _ => 
      remember (split e) as R; destruct R
  end.
  match goal with
  | |- context [split ?e] => 
      remember (split e) as R; destruct R
  end.
  simpl. 
  destruct v; simpl; auto.
    unfold subst_id.
    destruct_if; congruence.
Qed.

Lemma isubst_getCmdOperands : forall c id_list0,
 getCmdOperands c = id_list0 ->
 getCmdOperands (subst_cmd id2 (value_id id1) c) = 
   subst_list_id id2 id1 id_list0.
Proof.
  destruct c; simpl; intros; auto with ssa_subst.
    subst.
    rewrite <- subst_list_id_app.
    erewrite isubst_getValueIDs; eauto.
    rewrite isubst_values2ids'; auto.

    subst.
    repeat rewrite <- subst_list_id_app.
    repeat erewrite isubst_getValueIDs; eauto.

    subst.
    repeat rewrite <- subst_list_id_app.
    erewrite isubst_getValueIDs; eauto.
    rewrite isubst_getParamsOperand; auto.
Qed.

Lemma isubst_getTerminatorOperands : forall t id_list0,
  getTerminatorOperands t = id_list0 ->
  getTerminatorOperands (subst_tmn id2 (value_id id1) t) =
    subst_list_id id2 id1 id_list0.
Proof.
  destruct t; simpl; intros; 
    try solve [simpl; auto with ssa_subst | subst; auto].
Qed.

Hint Resolve isubst_getCmdOperands isubst_getPhiNodeOperands
  isubst_getTerminatorOperands: ssa_subst.

Lemma isubst_getInsnOperands : forall instr id_list0,
  getInsnOperands instr = id_list0 ->
  getInsnOperands (isubst_insn id2 id1 instr) = subst_list_id id2 id1 id_list0.
Proof.
  destruct instr; simpl; intros; auto with ssa_subst.
Qed.

Hint Resolve isubst_getInsnOperands: ssa_subst.

Lemma isubst_In_values2ids : forall i0 l0
  (H2 : ListSet.set_In i0
    (values2ids (list_prj1 value l l0))),
  ListSet.set_In (subst_id id2 id1 i0)
    (values2ids
      (list_prj1 value l
        (subst_list_value_l id2 (value_id id1) l0))).
Proof.
  induction l0 as [|[v]]; simpl; intros; auto.
    destruct v as [vid|]; simpl in *; auto.
    unfold subst_id in *.
    destruct H2 as [H2 | H2]; subst.
      destruct_if; try congruence; simpl; auto.
      destruct_if; destruct_if; subst; simpl; auto.
Qed.

Hint Resolve isubst_In_values2ids : ssa_subst.

Lemma isubst_In_getPhiNodeOperands : forall i0 p
  (H2 : ListSet.set_In i0 (getPhiNodeOperands p)),
  ListSet.set_In (subst_id id2 id1 i0)
    (getPhiNodeOperands (subst_phi id2 (value_id id1) p)).
Proof.
  destruct p; simpl; intros; auto with ssa_subst.
Qed.

Lemma isubst_In_getValueIDs : forall v i3
  (H2 : ListSet.set_In i3 (getValueIDs v)),
  ListSet.set_In (subst_id id2 id1 i3) (getValueIDs (v {[value_id id1 // id2]})).
Proof.
  intros.
  destruct v as [vid|]; simpl in *; unfold subst_id; auto.
    destruct H2 as [H2 | H2]; subst.
      destruct_if; simpl; auto.
      tauto.
Qed.

Lemma isubst_In_getValueIDs2 : forall v v0 i3
  (H2 : ListSet.set_In i3 (getValueIDs v ++ getValueIDs v0)),
  ListSet.set_In (subst_id id2 id1 i3)
    (getValueIDs (v {[value_id id1 // id2]}) ++
     getValueIDs (v0 {[value_id id1 // id2]})).
Proof.
  intros.
  unfold ListSet.set_In in *.
  destruct_in H2;
    apply isubst_In_getValueIDs in H2; auto; xsolve_in_list.
Qed.

Hint Resolve isubst_In_getValueIDs isubst_In_getValueIDs2: ssa_subst.

Lemma isubst_In_values2ids' : forall i0 l0
  (H2 : ListSet.set_In i0
    (values2ids (List.map snd l0))),
  ListSet.set_In (subst_id id2 id1 i0)
    (values2ids
      (List.map snd (subst_list_value id2 (value_id id1) l0))).
Proof.
  induction l0 as [|[]]; simpl; intros; auto.
    destruct v as [vid|]; subst; simpl; auto.
    unfold ListSet.set_In in *. unfold subst_id in *.
    destruct_in H2.
      destruct_if; simpl; auto.
      destruct_if; destruct_if; simpl; auto.
Qed.

Lemma isubst_In_getParamsOperand: forall i0 params5
  (H2 : ListSet.set_In i0 (getParamsOperand params5)),
  ListSet.set_In (subst_id id2 id1 i0)
    (getParamsOperand
      (List.map
        (fun p : typ * attributes * value =>
         let '(t, v) := p in (t, v {[value_id id1 // id2]})) params5)).
Proof.
  unfold getParamsOperand. 
  induction params5 as [|[[]]]; simpl; intros; auto.
  match goal with
  | _:context [split ?e] |- _ => 
      remember (split e) as R; destruct R
  end.
  match goal with
  | |- context [split ?e] => 
      remember (split e) as R; destruct R
  end.
  simpl. 
  destruct v; simpl; auto.
    simpl in H2. unfold subst_id in *.
    destruct H2 as [H2 | H2]; subst.
      destruct_if; simpl; auto.
      destruct_if; destruct_if; simpl; auto.
Qed.

Lemma isubst_In_getCmdOperands : forall c i3
  (H2 : ListSet.set_In i3 (getCmdOperands c)),
  ListSet.set_In (subst_id id2 id1 i3)
    (getCmdOperands (subst_cmd id2 (value_id id1) c)).
Proof.
  destruct c; simpl; intros; auto with ssa_subst.
    unfold ListSet.set_In in *.
    destruct_in H2.
      apply isubst_In_getValueIDs in H2; auto. xsolve_in_list.
      apply isubst_In_values2ids' in H2; auto. xsolve_in_list.

    unfold ListSet.set_In in *.
    destruct_in H2.
      apply isubst_In_getValueIDs in H2; auto; xsolve_in_list.
    destruct_in H2;
      apply isubst_In_getValueIDs in H2; auto; xsolve_in_list.

    unfold ListSet.set_In in *.
    destruct_in H2.
      apply isubst_In_getValueIDs in H2; auto. xsolve_in_list.
      apply isubst_In_getParamsOperand in H2; auto. xsolve_in_list.
Qed.

Lemma isubst_In_getTerminatorOperands : forall t i3
  (H2 : ListSet.set_In i3 (getTerminatorOperands t)),
  ListSet.set_In (subst_id id2 id1 i3)
    (getTerminatorOperands(subst_tmn id2 (value_id id1) t)).
Proof.
  destruct t; simpl; intros; auto with ssa_subst.
Qed.

Hint Resolve isubst_In_getCmdOperands isubst_In_getPhiNodeOperands
  isubst_In_getTerminatorOperands: ssa_subst.

Lemma isubst_In_getInsnOperands : forall i0 instr
  (H2 : ListSet.set_In i0 (getInsnOperands instr)),
  ListSet.set_In (subst_id id2 id1 i0)
     (getInsnOperands (isubst_insn id2 id1 instr)).
Proof.
  destruct instr; simpl; auto with ssa_subst.
Qed.

End ISubst.

Section ISubstOps.

Variable (los:layouts) (nts:namedts) (Ps1 Ps2:products)
         (M:module) (f:fdef) (id1 id2:id).
Hypothesis (Hdom: id_in_reachable_block f id2 -> idDominates f id1 id2)
           (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
           (HwfF: wf_fdef [M] M f) 
           (HuniqF: uniqFdef f)
           (Hnotin2: ~ In id2 (getArgsIDsOfFdef f)).

Lemma isubst_wf_operand : forall instr b i0
  (Huniq : NoDup (getBlockLocs b))
  (H1 : wf_operand f b instr i0),
   wf_operand (isubst_fdef id2 id1 f) (isubst_block id2 id1 b)
     (isubst_insn id2 id1 instr) (subst_id id2 id1 i0).
Proof.
  intros.
  inv H1.
  match goal with
  | H2: ListSet.set_In _ _, H3: notT (isPhiNode _) |- _ =>
    apply isubst_In_getInsnOperands with (id1:=id1)(id2:=id2) in H2;
    rewrite subst_isPhiNode with (id0:=id2)(v0:=value_id id1) in H3
  end.
  unfold subst_id in *.
  destruct (id_dec i0 id2); subst.
    eapply wf_operand_intro; try solve
      [eauto with ssa_subst | autounfold; eauto with ssa_subst].
    autounfold.
    fold_subst_tac.
    rewrite <- TransCFG.pres_isReachableFromEntry.
    rewrite <- TransCFG.pres_getArgsIDsOfFdef.
    destruct (In_dec id_dec id1 (getArgsIDsOfFdef f)) as [Hin1 | Hnotin1]; auto.
    destruct (isReachableFromEntry_dec f b) as [Hreach | Hnreach]; auto.
    left. left.
    match goal with
    | H4: (_ \/ _) \/ _ |- _ => 
      destruct H4 as [[[b' [Hlkup H4]] | H4] | H4]; try congruence
    end.
    assert (blockInFdefB b f = true) as HBinF.
      apply destruct_insnInFdefBlockB in H. tauto.
    assert (id_in_reachable_block f id2) as Hireach.
      intros b2 Hlkup'.
      uniq_result.
      destruct H4 as [H4 | H4].
        eapply insnDominates_spec3 in H4; eauto 1.
        uniq_result. auto.

        eapply blockStrictDominates_isReachableFromEntry; eauto.
    apply Hdom in Hireach. 
    assert (J:=Hireach).
    apply idDominates__lookupBlockViaIDFromFdef in J; auto.
    destruct J as [b1 J].
    exists (btrans (Subst id2 (value_id id1)) b1).
    split.
      simpl. apply subst_lookupBlockViaIDFromFdef; auto.
     
      rewrite <- TransCFG.pres_blockStrictDominates.
      simpl.
      rewrite <- subst_insnDominates; eauto
         using insnInFdefBlockB__insnInBlockB.
      match goal with
      | H4 : _ \/ _ |- _ => 
         destruct H4 as [H4 | H4]; 
           eauto using idDominates_insnDominates__insnOrBlockStrictDominates,
                       idDominates_blockStrictDominates__blockStrictDominates
      end.

    eapply wf_operand_intro; try solve
      [eauto with ssa_subst | autounfold; eauto with ssa_subst].
      autounfold.
      fold_subst_tac.
      rewrite <- TransCFG.pres_isReachableFromEntry.
      rewrite <- TransCFG.pres_getArgsIDsOfFdef.
      match goal with
      | H4: (_ \/ _) \/ _ |- _ => 
        destruct H4 as [[[b' [Hlkup H4]] | H4] | H4]; auto
      end.
      left. left.
      exists (btrans (Subst id2 (value_id id1)) b').
      rewrite <- TransCFG.pres_blockStrictDominates.
      simpl.
      rewrite <- subst_insnDominates; eauto using insnInFdefBlockB__insnInBlockB.
      split; auto.
        apply subst_lookupBlockViaIDFromFdef; auto.
Qed.

Hint Resolve isubst_wf_operand: ssa_subst.

Lemma isubst_wf_operand_list : forall instr b 
  (Huniq : NoDup (getBlockLocs b)) id_list0
  (H2 : forall id_ : id,
          In id_ (List.map (fun id_0 : id => id_0) id_list0) ->
          wf_operand f b instr id_),
  forall id_ : id,
    In id_ (List.map (fun id_0 : id => id_0) 
              (subst_list_id id2 id1 id_list0)) ->
    wf_operand (isubst_fdef id2 id1 f) (isubst_block id2 id1 b)
      (isubst_insn id2 id1 instr) id_.
Proof.
  induction id_list0 as [|a]; simpl; intros; auto.
    tauto.
    destruct H as [H | H]; subst; auto with ssa_subst.
Qed.

Hint Resolve isubst_getInsnOperands isubst_wf_operand_list: ssa_subst.

Lemma isubst_wf_insn_base : forall b instr
  (Huniq : NoDup (getBlockLocs b))
  (HwfI: wf_insn_base f b instr),
  wf_insn_base (isubst_fdef id2 id1 f) (isubst_block id2 id1 b)
    (isubst_insn id2 id1 instr).
Proof.
  intros.
  inv HwfI.
  eapply subst_insnInFdefBlockB in H; eauto.
  eapply isubst_getInsnOperands in H1; eauto.
  eapply wf_insn_base_intro; eauto with ssa_subst.
Qed.

Hint Constructors wf_phi_operands.

Lemma isubst_wf_phi_operands : forall b ty id' vls
  (Hwf_pnops: wf_phi_operands f b id' ty vls),
  wf_phi_operands (isubst_fdef id2 id1 f) (isubst_block id2 id1 b) id' ty
    (subst_list_value_l id2 (value_id id1) vls).
Proof.
  intros.
  induction Hwf_pnops; simpl; auto.
    assert (H':=H).
    eapply (@TransCFG.pres_lookupBlockViaLabelFromFdef 
             (Subst id2 (value_id id1))) in H; eauto.
    destruct (id_dec vid1 id2); subst.
      eapply wf_phi_operands_cons_vid; eauto.
      autounfold.
      fold_subst_tac.
      rewrite <- TransCFG.pres_isReachableFromEntry.
      rewrite <- TransCFG.pres_getArgsIDsOfFdef.
      destruct (In_dec id_dec id1 (getArgsIDsOfFdef f)) as [Hin1 | Hnotin1]; auto.
      left.
      destruct (isReachableFromEntry_dec f b1) as [Hreach | Hnreach]; auto.
      left.
      match goal with
      | H0: (_ \/ _) \/ _ |- _ => 
        destruct H0 as [[[vb [Hlkup H0]] | H0] | H0]; try congruence
      end.
      assert (blockInFdefB b1 f = true) as HBinF.
        solve_blockInFdefB.
      assert (id_in_reachable_block f id2) as Hireach.
        intros b2 Hlkup'.
        uniq_result.
        eapply blockDominates_isReachableFromEntry; eauto 1.
      apply Hdom in Hireach.  
      assert (J:=Hireach).
      apply idDominates__lookupBlockViaIDFromFdef in J; auto.
      destruct J as [vb1 J].
      exists (btrans (Subst id2 (value_id id1)) vb1).
      split.
        simpl. apply subst_lookupBlockViaIDFromFdef; auto.

        rewrite <- TransCFG.pres_blockDominates; auto.
        eapply blockDominates_trans with (b2:=vb);
              eauto using lookupBlockViaIDFromFdef__blockInFdefB,
                          lookupBlockViaLabelFromFdef__blockInFdefB.
          eapply idDominates__blockDominates; eauto.

      eapply wf_phi_operands_cons_vid; eauto.
      autounfold.
      fold_subst_tac.
      rewrite <- TransCFG.pres_isReachableFromEntry.
      rewrite <- TransCFG.pres_getArgsIDsOfFdef.
      match goal with
      | H4: (_ \/ _) \/ _ |- _ => 
        destruct H4 as [[[b' [Hlkup H4]] | H4] | H4]; auto
      end.
      left. left.
      exists (btrans (Subst id2 (value_id id1)) b').
      rewrite <- TransCFG.pres_blockDominates.
      simpl.
      split; auto.
        apply subst_lookupBlockViaIDFromFdef; auto.
Qed.

End ISubstOps.

Section Subst.

Variable (los:layouts) (nts:namedts) (Ps1 Ps2:products)
         (M M':module) (f f':fdef) (id0:id) (v0:value).
Hypothesis (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
           (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
           (HeqF': f' = subst_fdef id0 v0 f)
           (HwfF: wf_fdef [M] M f) 
           (Hwfcst0: forall t0, lookupTypViaIDFromFdef f id0 = Some t0 ->
                                wf_value [M] M f v0 t0)
           (HuniqF: uniqFdef f).

Hypothesis subst_wf_insn_base : forall b instr
  (Huniq : NoDup (getBlockLocs b))
  (HwfI: wf_insn_base f b instr),
  wf_insn_base f' (subst_block id0 v0 b) (subst_insn id0 v0 instr).

Hypothesis subst_wf_phi_operands: forall b ty id' vls
  (Hwf_pnops: wf_phi_operands f b id' ty vls),
  wf_phi_operands (subst_fdef id0 v0 f) (subst_block id0 v0 b) id' ty
    (subst_list_value_l id0 v0 vls).

Lemma subst_wf_value : forall v t (Hwfv: wf_value [M] M f v t),
  wf_value [M'] M' f' (subst_value id0 v0 v) t.
Proof.
  intros.
  assert (J1:=subst_wf_const).
  assert (J2:=subst_wf_original_value).
  assert (J3:=subst_wf_typ).
  subst. 
  inv Hwfv; uniq_result; try constructor; eauto.
    simpl. 
    destruct_if; eauto 3.
      constructor; eauto 2.
        rewrite <- subst_lookupTypViaIDFromFdef; auto.
Qed.

Lemma subst_wf_phinode : forall b PN (HwfPN: wf_phinode f b PN),
  wf_phinode (subst_fdef id0 v0 f) (subst_block id0 v0 b)
    (subst_phi id0 v0 PN).
Proof.
  intros. destruct PN as [id' vls].
  unfold wf_phinode in *. simpl.
  destruct HwfPN as [Hwf_pnops Hcl].
  split; auto with ssa_subst.
Qed.

Lemma subst_wf_sz_value_list : forall
  sz_value_list t
  (H :forall value_ : value,
       In value_
         (List.map
            (fun pat_ : sz * value => let (_, value_0) := pat_ in value_0)
            sz_value_list) ->
       wf_value [M] M f value_ t),
  forall (value_ : value)
    (Hin: In value_
      (List.map
         (fun pat_ : sz * value => let (_, value_0) := pat_ in value_0)
      (subst_list_value id0 v0 sz_value_list))),
  wf_value [M'] M' f' value_ t.
Proof.
  assert (J:=subst_wf_value).
  induction sz_value_list as [|[]]; simpl; intros.
    tauto.
    destruct Hin as [Hin | Hin]; subst; auto.
Qed.

Lemma subst_wf_list_value_l : forall
  value_l_list t
  (H :forall value_ : value,
       In value_
         (List.map 
            (fun pat_ : value * l => let (value_0, _) := pat_ in value_0)
         value_l_list) ->
       wf_value [M] M f value_ t),
  forall (value_ : value)
    (Hin: In value_
      (List.map 
        (fun pat_ : value * l => let (value_0, _) := pat_ in value_0)
        (subst_list_value_l id0 v0 value_l_list))),
  wf_value [M'] M' f' value_ t.
Proof.
  assert (J:=subst_wf_value).
  induction value_l_list as [|[]]; simpl; intros.
    tauto.
    destruct Hin as [Hin | Hin]; subst; auto.
Qed.
 
Lemma subst_wf_params : forall
  (typ'_attributes'_value''_list : list (typ * attributes * value))
  (H4 : forall (value_'' : value) (typ_' : typ),
       In (value_'', typ_')
         (List.map
            (fun pat_ : typ * attributes * value =>
             let (p, value_''0) := pat_ in
             let (typ_'0, _) := p in (value_''0, typ_'0))
            typ'_attributes'_value''_list) ->
       wf_value [M] M f value_'' typ_'),
   forall (value_'' : value) (typ_' : typ)
   (Hin: In (value_'', typ_')
     (List.map
        (fun x : typ * attributes * value =>
         let (p, value_''0) :=
             let (p, value_''0) := x in
             let (typ_'0, attributes_') := p in
             (typ_'0, attributes_', value_''0 {[v0 // id0]}) in
         let (typ_'0, _) := p in (value_''0, typ_'0))
        typ'_attributes'_value''_list)),
   wf_value [M'] M' f' value_'' typ_'.
Proof.
  assert (J:=subst_wf_value).
  induction typ'_attributes'_value''_list as [|[[]]]; simpl; intros.
    tauto.
    destruct Hin as [Hin | Hin]; subst; auto.
      uniq_result. auto.
Qed.

Ltac subst_wf_cmd_tac :=
match goal with
| H2: wf_insn_base _ _ _ |- wf_insn_base _ _ _ =>
   eapply subst_wf_insn_base in H2; eauto
| H2: wf_typ _ _ _ |- wf_typ _ _ _ => 
   eapply subst_wf_typ; eauto
| _ => auto
end.

Lemma subst_wf_trunc : forall b b' 
  (Huniq: NoDup (getBlockLocs b))
  (Heqb': b' = subst_block id0 v0 b) instr
  (HwfI : wf_trunc [M] M f b instr),
  wf_trunc [M'] M' f' b' (subst_insn id0 v0 instr).
Proof.
  intros.
  assert (J2:=subst_wf_value).
  inv HwfI; uniq_result; try solve [
    econstructor; try solve [subst_wf_cmd_tac]
  ].
Qed.

Lemma subst_wf_ext : forall b b' 
  (Huniq: NoDup (getBlockLocs b))
  (Heqb': b' = subst_block id0 v0 b) instr
  (HwfI : wf_ext [M] M f b instr),
  wf_ext [M'] M' f' b' (subst_insn id0 v0 instr).
Proof.
  intros.
  assert (J2:=subst_wf_value).
  inv HwfI; uniq_result; try solve [
    econstructor; try solve [subst_wf_cmd_tac]
  ].
Qed.

Lemma subst_wf_cast : forall b b' 
  (Huniq: NoDup (getBlockLocs b))
  (Heqb': b' = subst_block id0 v0 b) instr
  (HwfI : wf_cast [M] M f b instr),
  wf_cast [M'] M' f' b' (subst_insn id0 v0 instr).
Proof.
  intros.
  assert (J2:=subst_wf_value).
  inv HwfI; uniq_result; try solve [
    econstructor; try solve [subst_wf_cmd_tac]
  ].
Qed.

Lemma subst_wf_insn : forall b instr (HwfI: wf_insn [M] M f b instr)
  (Huniq : NoDup (getBlockLocs b)) b' (Heqb': b' = subst_block id0 v0 b),
  wf_insn [M'] M' (subst_fdef id0 v0 f) b'
    (subst_insn id0 v0 instr).
Proof.
  intros.
  assert (J:=subst_wf_params).
  assert (J0:=subst_wf_list_value_l).
  assert (J1:=subst_wf_sz_value_list).
  assert (J2:=subst_wf_value).
  assert (J5:=@subst_wf_trunc b b' Huniq Heqb' instr).
  assert (J6:=@subst_wf_ext b b' Huniq Heqb' instr).
  assert (J7:=@subst_wf_cast b b' Huniq Heqb' instr).
  assert (J8:=subst_wf_const los nts Ps1 Ps2 M M' f f' id0 
                v0 HeqM HeqM' HeqF').

Ltac subst_wf_insn_pre_tac :=
repeat match goal with
| H1 : context [Function.getDefReturnType f] |- _ =>
  rewrite <- 
    (@TransCFG.pres_getDefReturnType (Subst id0 v0)) in H1
| |- context [Function.getDefReturnType f] =>
  rewrite <- 
    (@TransCFG.pres_getDefReturnType (Subst id0 v0)); auto
| H1 : lookupBlockViaLabelFromFdef f _ = ret _ |- _ =>
  apply (@TransCFG.pres_lookupBlockViaLabelFromFdef 
           (Subst id0 v0)) in H1
end.

Ltac subst_wf_insn_post_tac :=
match goal with
| H1 : insnInFdefBlockB _ _ _ = true |- insnInFdefBlockB _ _ _ = true =>
  eapply subst_insnInFdefBlockB in H1; eauto
| H2: wf_insn_base _ _ _ |- wf_insn_base _ _ _ => 
  eapply subst_wf_insn_base in H2; eauto
| H2: wf_typ _ _ _ |- wf_typ _ _ _ => 
  eapply subst_wf_typ in H2; eauto
| H2: wf_phinode _ _ _ |- wf_phinode _ _ _ => 
   eapply subst_wf_phinode in H2; eauto
| _ => eauto with ssa_subst
end.

  inv HwfI; uniq_result; try solve [
    subst_wf_insn_pre_tac;
    econstructor; 
    subst_wf_insn_post_tac
  ].

    subst_wf_insn_pre_tac.
    econstructor; subst_wf_insn_post_tac.
      match goal with
      | H1: FunctionType.getNumParams _ = _ |- _ =>
        rewrite H1; clear; f_equal;
        repeat rewrite map_length; auto
      end.

      instantiate 
        (1 := List.map
          (fun pat_ : typ * attributes * value =>
           let (p, value_'') := pat_ in
           let (typ_', attributes_') := p in 
           (typ_', attributes_', value_''{[v0 // id0]}))
          typ'_attributes'_value''_list).
      clear.
      repeat rewrite map_map.
      apply map_ext.
      destruct a as [[]]. auto.

      rewrite map_map.
      intros. eauto.
Qed.

Hint Resolve subst_wf_insn : ssa_subst.

Hint Constructors wf_phinodes.

Ltac subst_wf_insn_tac :=
match goal with
| H2: wf_insn _ _ _ _ _ |- wf_insn _ _ _ _ _ => 
   eapply subst_wf_insn in H2; subst; eauto
| _ => auto
end.

Lemma subst_wf_phinodes : forall b PNs (HwfPNs: wf_phinodes [M] M f b PNs)
  (Huniq : NoDup (getBlockLocs b)) b' (Heqb': b' = subst_block id0 v0 b),
  wf_phinodes [M'] M' f' (subst_block id0 v0 b)
    (List.map (subst_phi id0 v0) PNs).
Proof.
  intros.
  induction PNs; simpl; auto.
    inversion HwfPNs.
    econstructor; eauto 2.
      subst_wf_insn_tac.
Qed.

Hint Constructors wf_cmds.

Lemma subst_wf_cmds : forall b Cs (HwfCs: wf_cmds [M] M f b Cs)
  (Huniq : NoDup (getBlockLocs b)) b' (Heqb': b' = subst_block id0 v0 b),
  wf_cmds [M'] M' f' b' (List.map (subst_cmd id0 v0) Cs).
Proof.
  intros.
  induction Cs; simpl; auto.
    inversion HwfCs.
    econstructor; eauto 2.
      subst_wf_insn_tac.
Qed.

Lemma subst_wf_block : forall b (HwfB : wf_block [M] M f b)
  (Huniq : NoDup (getBlockLocs b)) b' (Heqb': b' = subst_block id0 v0 b),
  wf_block [M'] M' f' b'.
Proof.
  intros.
  inv_wf_block HwfB. subst b.
  eapply subst_blockInSystemModuleFdefB in HBinSMF; eauto.
  eapply subst_wf_cmds in Hwfcs; eauto.
  eapply subst_wf_phinodes in Hwfps; eauto.
  eapply subst_wf_insn in Hwfi; eauto.
  subst.
  apply wf_block_intro; eauto.
Qed.

Hint Resolve subst_wf_block : ssa_subst.

Hint Constructors wf_blocks.

Lemma subst_wf_blocks : forall bs 
  (Hin: forall b, In b bs -> blockInFdefB b f = true)
  (HwfBs : wf_blocks [M] M f bs) (Huniq : NoDup (getBlocksLocs bs)),
  wf_blocks [M'] M' f' (List.map (subst_block id0 v0) bs).
Proof.
  intros. 
  induction bs; simpl.
    constructor.

    simpl in Huniq.
    split_NoDup. inversion HwfBs.
    constructor; auto.
      eapply subst_wf_block; eauto 1.
      apply IHbs; auto.
        intros b Hin'. apply Hin. simpl; auto.
Qed.

Hint Resolve subst_wf_blocks : ssa_subst.

Lemma subst_wf_fdef: 
  wf_fdef [M'] M' f'.
Proof.
  intros. assert (HwfF':=HwfF).
  assert (G:=subst_preserves_wf_fheader).
  inv_wf_fdef HwfF'.
  match goal with
  | Hentry : getEntryBlock _ = _,
    HuniqF : uniqFdef _,
    Hnpred : hasNonePredecessor _ _ = _,
    HwfBs : wf_blocks _ _ _ _ |- _ =>
     eapply (@TransCFG.pres_getEntryBlock (Subst id0 v0)) 
       in Hentry; eauto;
     eapply (@TransCFG.pres_hasNonePredecessor (Subst id0 v0)) 
       in Hnpred; eauto
  end.
  rewrite EQ2 in Hwfb.
  match goal with
  | H2: fdef_intro _ _ = _,
    H9: wf_blocks _ _ _ _ |- _ =>
    rewrite H2 in H9;
    eapply subst_wf_blocks in H9; try solve [
      eauto |
      rewrite <- H2 in HuniqF; eapply uniqF__uniqBlocksLocs; eauto |
      rewrite <- H2; simpl; intros; apply In_InBlocksB; auto
    ]
  end.

  subst. uniq_result.
  eapply wf_fdef_intro; eauto 2.
    clear. 
    apply productInSystemModuleB_intro.
      simpl. unfold is_true. apply InProductsB_middle.

      unfold moduleInSystem. simpl. apply orb_true_intro. 
      left. apply moduleEqB_refl.
Qed.

End Subst.

Lemma subst_wfS: forall (los : layouts) (nts : namedts) (f:fdef)
  (Ps1 : list product) (Ps2 : list product) (id0 : id) (v0 : value) 
  (Hdom: valueDominates f v0 (value_id id0))
  (Hnotin2: ~ In id0 (getArgsIDsOfFdef f))
  (Hwfv: forall t0, lookupTypViaIDFromFdef f id0 = Some t0 ->
         wf_value [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
                  (module_intro los nts (Ps1 ++ product_fdef f :: Ps2)) 
                  f v0 t0)
  (HwfS :
     wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  wf_system 
    [module_intro los nts
      (Ps1 ++ product_fdef (subst_fdef id0 v0 f) :: Ps2)].
Proof.
  intros.
  assert (HuniqF: uniqFdef f).
    apply wf_single_system__wf_uniq_fdef in HwfS.
    destruct HwfS; auto.
  eapply TopWFS.trans_wfS with (f:=f) in HwfS; intros;
    eauto using subst_fheader.
    eapply subst_wf_fdef in HwfF; eauto.
      destruct v0 as [vid0|c0].
        eapply isubst_wf_insn_base; eauto.
        apply csubst_wf_insn_base; auto.
      destruct v0 as [vid0|c0].
        eapply isubst_wf_phi_operands; eauto.
        apply csubst_wf_phi_operands; auto.
    eapply subst_uniqFdef; eauto.
Qed.

Require Import palloca_props.
Require Import mem2reg.

Section SubstUsed.

Variable (id0:id) (v0:value) (pid:id).
Hypothesis (Hnused : used_in_value pid v0 = false).

Lemma subst_used_in_value: forall v5,
  used_in_value pid v5 = false ->
  used_in_value pid (v5 {[v0 // id0]}) = false.
Proof.
  destruct v5; simpl; auto.
  destruct_if.
Qed.

Hint Resolve subst_used_in_value: substused.

Lemma subst_used_in_tmn: forall tmn,
  used_in_tmn pid tmn = false ->
  used_in_tmn pid (subst_tmn id0 v0 tmn) = false.
Proof.
  destruct tmn; simpl; auto with substused.
Qed.

Lemma subst_used_in_list_value_l: forall l0
  (H: used_in_list_value_l pid l0 = false),
  used_in_list_value_l pid (subst_list_value_l id0 v0 l0) = false.
Proof.
  induction l0 as [|[]]; simpl; intros; auto.
    apply orb_false_iff in H.
    apply orb_false_iff.
    destruct H as [H1 H2].
    auto using subst_used_in_value.
Qed.

Lemma subst_used_in_phi: forall p 
  (H: used_in_phi pid p = false),
  used_in_phi pid (subst_phi id0 v0 p) = false.
Proof.
  destruct p. simpl. apply subst_used_in_list_value_l.
Qed.

Lemma subst_used_in_phis: forall ps init
  (H: fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
        ps init = false),
  fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
     (List.map (subst_phi id0 v0) ps) init = false.
Proof.
  induction ps; simpl; intros; auto.
    apply fold_left_or_false in H.
      destruct H as [H1 H2].
      apply orb_false_iff in H2.
      destruct H2; subst. 
      rewrite subst_used_in_phi; auto.
      
      apply used_in_phi_fun_spec.
Qed.

Lemma subst_used_in_list_value: forall l0
  (H: used_in_list_value pid l0 = false),
  used_in_list_value pid (subst_list_value id0 v0 l0) = false.
Proof.
  induction l0 as [|[]]; simpl; intros; auto.
    apply orb_false_iff in H.
    apply orb_false_iff.
    destruct H as [H1 H2].
    auto using subst_used_in_value.
Qed.

Lemma subst_used_in_params: forall ps init
  (H : fold_left
    (fun (acc : bool) (p : typ * attributes * value) =>
     let '(_, v) := p in used_in_value pid v || acc) ps init = false),
  fold_left
    (fun (acc : bool) (p : typ * attributes * value) =>
     let '(_, v) := p in used_in_value pid v || acc)
    (List.map
       (fun p : typ * attributes * value =>
        let '(t, v) := p in (t, v {[v0 // id0]})) ps) init = false.
Proof.
  induction ps as [|[[]]]; simpl; intros; auto.
    apply fold_left_or_false in H.
      destruct H as [H1 H2].
      apply orb_false_iff in H2.
      destruct H2; subst. 
      rewrite subst_used_in_value; auto.
      
      intros a0 [[b1 b2] b3] H4.
      apply orb_false_iff in H4. tauto.
Qed.

Lemma subst_used_in_cmd: forall c,
  used_in_cmd pid c = false ->
  used_in_cmd pid (subst_cmd id0 v0 c) = false.
Proof.
  destruct c; simpl; intros; try solve [
    auto with substused |
    match goal with
    | H: _ || _ || _ = false |- _ =>
       apply orb_false_iff in H; destruct H as [H1 H2];
       apply orb_false_iff in H1; destruct H1;
       repeat (apply orb_false_iff; split; auto with substused)
    | H: _ || _ = false |- _ =>
       apply orb_false_iff in H; destruct H;
       apply orb_false_iff; 
         auto using subst_used_in_list_value, subst_used_in_params with substused
    end
   ].
Qed.

Lemma subst_is_promotable_cmd: forall c acc
  (H: is_promotable_cmd pid acc c = true),
  is_promotable_cmd pid acc (subst_cmd id0 v0 c) = true.
Proof.
  unfold is_promotable_cmd.
  intros.
  destruct_if.
    destruct c; try congruence; subst; simpl.
      destruct_if.
   
      apply andb_true_iff in H1.
      destruct H1 as [EQ1 EQ2]; subst.
      rewrite EQ1. simpl.
      unfold negb in *.
      destruct_if. 
      rewrite valueEqB__used_in_value in HeqR0.
      rewrite valueEqB__used_in_value.
      rewrite subst_used_in_value; auto.
      destruct_if.
    
   rewrite subst_used_in_cmd; auto.
Qed.

Lemma subst_is_promotable_cmds: forall cs acc
  (H: fold_left (is_promotable_cmd pid) cs acc = true),
  fold_left (is_promotable_cmd pid) (List.map (subst_cmd id0 v0) cs) acc =
    true.
Proof.
  induction cs; simpl; intros; auto.
    apply fold_left_and_true in H.
      destruct H as [H1 H2].
      rewrite subst_is_promotable_cmd; auto.
      
      apply is_promotable_cmd_spec.
Qed.

Lemma subst_is_promotable_fun: forall b acc,
  is_promotable_fun pid acc b = true ->
  is_promotable_fun pid acc (subst_block id0 v0 b) = true.
Proof.
  destruct b; simpl.
  intros.
  match goal with
  | H: context [if ?lk then _ else _] |- _ =>
    remember lk as R; destruct R; tinv H
  end.
  symmetry in HeqR.
  assert (forall (a : bool) c, a || c = false -> a = false) as G.
    intros a c Hin. apply orb_false_iff in Hin. tauto.
  apply fold_left_or_false in HeqR; eauto 2.
  destruct HeqR as [J1 J2].
  apply subst_used_in_tmn in J2.
  apply subst_used_in_phis in J1.
  rewrite J2. rewrite J1.
  apply subst_is_promotable_cmds; auto.
Qed.

Lemma subst_is_promotable_funs: forall bs init
  (H : fold_left (is_promotable_fun pid) bs init = true),
  fold_left (is_promotable_fun pid) (List.map (subst_block id0 v0) bs) init =
    true.
Proof.
  induction bs; simpl; intros; auto.
    apply fold_left_and_true in H.
      destruct H as [H1 H2].
      rewrite subst_is_promotable_fun; auto.
      
      apply is_promotable_fun_spec.
Qed.

Lemma subst_is_promotable: forall f
  (Hnused : used_in_value pid v0 = false)
  (H: is_promotable f pid = true),
  is_promotable (subst_fdef id0 v0 f) pid = true.
Proof.
  unfold is_promotable.
  destruct f as [fh bs]. simpl. intros.
  apply subst_is_promotable_funs; auto.
Qed.

End SubstUsed.

Definition subst_pinfo (id0:id) (v0:value) (pinfo:PhiInfo) :=
  {| PI_f := subst_fdef id0 v0 (PI_f pinfo);
     PI_rd := PI_rd pinfo;
     PI_id := PI_id pinfo;
     PI_typ := PI_typ pinfo;
     PI_num := subst_value id0 v0 (PI_num pinfo);
     PI_align := PI_align pinfo |}.

Lemma subst_fdef_PI_f__PI_f_subst_pinfo: forall i1 v pinfo,
  subst_fdef i1 v (PI_f pinfo) = PI_f (subst_pinfo i1 v pinfo).
Proof. destruct pinfo; auto. Qed.

Lemma subst_alloca_in_entry: forall pid pty pnum pal id0 v0 cs
  (H : In (insn_alloca pid pty pnum pal) cs),
  In (insn_alloca pid pty (subst_value id0 v0 pnum) pal) 
     (List.map (subst_cmd id0 v0) cs).
Proof.
  induction cs; simpl; intros; auto.
    destruct H; subst; auto.
Qed.

Lemma subst_wfPI: forall (los : layouts) (nts : namedts)
  (dones : list id) (pinfo: PhiInfo)
  (Ps1 : list product) (Ps2 : list product)
  id0 (v0 : value) (Hwfpi: WF_PhiInfo pinfo) f
  (HwfS:  wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)])
  (Heq: PI_f pinfo = f) 
  (Hnused: used_in_value (PI_id pinfo) v0 = false),
  WF_PhiInfo (subst_pinfo id0 v0 pinfo).
Proof.
  intros. subst.
  destruct Hwfpi.
  destruct pinfo. 
  split; simpl in *.
    unfold promotable_alloca in *.
    inv_mbind. 
    fold_subst_tac.
    erewrite TransCFG.pres_getEntryBlock; eauto.
    destruct b as [l0 ps0 cs0 tmn0]. 
    destruct H.
    simpl.
    split.
      apply subst_alloca_in_entry; auto.

      unfold is_true.
      apply subst_is_promotable; auto.

    rewrite <- subst_reachablity_analysis; auto.
Qed.

Section SubstOther.

Variable (id0:id) (v0:value).

Lemma subst_lookupBlockViaIDFromBlocks_rev : forall id5 bs b2
  (Hlkup: lookupBlockViaIDFromBlocks (List.map (subst_block id0 v0) bs) id5 =
            ret b2),
  exists b1, 
    lookupBlockViaIDFromBlocks bs id5 = ret b1 /\ subst_block id0 v0 b1 = b2.
Proof.
  induction bs as [|[l1 ps1 cs1 tmn1]]; simpl; intros.
    congruence.

    rewrite subst_getPhiNodesIDs in Hlkup.
    rewrite subst_getCmdsIDs in Hlkup.
    destruct_if; eauto.
Qed.

Lemma subst_lookupBlockViaIDFromFdef_rev : forall f id5 b2,
  lookupBlockViaIDFromFdef (subst_fdef id0 v0 f) id5 = ret b2 ->
  exists b1,
    lookupBlockViaIDFromFdef f id5 = ret b1 /\ subst_block id0 v0 b1 = b2.
Proof.
  destruct f. simpl; intros. 
  apply subst_lookupBlockViaIDFromBlocks_rev; auto.
Qed.

Lemma subst_id_in_reachable_block: forall f id1
  (Hin : id_in_reachable_block (subst_fdef id0 v0 f) id1 \/
        In id1 (getArgsIDsOfFdef (subst_fdef id0 v0 f))),
  id_in_reachable_block f id1 \/ In id1 (getArgsIDsOfFdef f).
Proof.
  intros.
  rewrite (@TransCFG.pres_getArgsIDsOfFdef (Subst id0 v0)); auto.
  destruct Hin as [Hin | Hin]; auto.
    left.
    intros b Hlkup.
    eapply subst_lookupBlockViaIDFromFdef in Hlkup; eauto.
    apply Hin in Hlkup.
    rewrite (@TransCFG.pres_isReachableFromEntry (Subst id0 v0)); auto.
Qed.

Lemma subst_cmd__getCmdLoc: forall c, 
  getCmdLoc c = getCmdLoc (subst_cmd id0 v0 c).
Proof. destruct c; simpl; auto. Qed.

Lemma subst_lookupCmdViaIDFromCmds_none_rev: forall cs id1
  (Hlk: lookupCmdViaIDFromCmds (List.map (subst_cmd id0 v0) cs) id1 = None),
  lookupCmdViaIDFromCmds cs id1 = None.
Proof.
  induction cs; simpl; intros; auto.
    rewrite <- subst_cmd__getCmdLoc in Hlk.
    destruct_if. rewrite H0. auto.
Qed.

Lemma subst_lookupPhiNodeViaIDFromPhiNodes_none_rev: forall ps id1
  (Hlk: lookupPhiNodeViaIDFromPhiNodes 
           (List.map (subst_phi id0 v0) ps) id1 = None),
  lookupPhiNodeViaIDFromPhiNodes  ps id1 = None.
Proof.
  induction ps as [|[]]; simpl; intros; auto.
    destruct_if. rewrite H0. auto.
Qed.

Lemma subst_tmn__getTerminatorID: forall t, 
  getTerminatorID t = getTerminatorID (subst_tmn id0 v0 t).
Proof. destruct t; simpl; auto. Qed.

Lemma subst_lookupInsnViaIDFromBlock_none_rev: forall b id1
  (Hlk: lookupInsnViaIDFromBlock (subst_block id0 v0 b) id1 = None),
  lookupInsnViaIDFromBlock b id1 = None.
Proof.
  destruct b. simpl. intros.
  inv_mbind_app; try congruence.
  inv_mbind_app; try congruence.
  rewrite subst_lookupPhiNodeViaIDFromPhiNodes_none_rev; auto.
  rewrite subst_lookupCmdViaIDFromCmds_none_rev; auto.
  rewrite subst_tmn__getTerminatorID.
  destruct_if; auto.
Qed.

Lemma subst_lookupCmdViaIDFromCmds_some_rev: forall cs id1 c2
  (Hlk: lookupCmdViaIDFromCmds (List.map (subst_cmd id0 v0) cs) id1 = Some c2),
  exists c1,
    lookupCmdViaIDFromCmds cs id1 = Some c1 /\ subst_cmd id0 v0 c1 = c2.
Proof.
  induction cs; simpl; intros.
    congruence.

    rewrite <- subst_cmd__getCmdLoc in Hlk.
    destruct_if; eauto.
Qed.

Lemma subst_lookupPhiNodeViaIDFromPhiNodes_some_rev: forall ps id1 p2
  (Hlk: lookupPhiNodeViaIDFromPhiNodes 
           (List.map (subst_phi id0 v0) ps) id1 = Some p2),
  exists p1, 
    lookupPhiNodeViaIDFromPhiNodes ps id1 = Some p1 /\ subst_phi id0 v0 p1 = p2.
Proof.
  induction ps as [|[]]; simpl; intros.
    congruence.
    destruct_if; eauto.
Qed.

Lemma subst_lookupInsnViaIDFromBlock_some_rev: forall b id1 instr2
  (Hlk: lookupInsnViaIDFromBlock (subst_block id0 v0 b) id1 = ret instr2),
  exists instr1, 
    lookupInsnViaIDFromBlock b id1 = ret instr1 /\ 
    subst_insn id0 v0 instr1 = instr2.
Proof.
  destruct b. simpl. intros.
  inv_mbind_app.
    uniq_result. symmetry_ctx.
    apply subst_lookupPhiNodeViaIDFromPhiNodes_some_rev in HeqR.
    destruct HeqR as [p1 [Hlk EQ]]; subst.
    fill_ctxhole. eauto.

    rewrite subst_lookupPhiNodeViaIDFromPhiNodes_none_rev; auto.
    inv_mbind_app.
      uniq_result. symmetry_ctx.
      apply subst_lookupCmdViaIDFromCmds_some_rev in HeqR0.
      destruct HeqR0 as [c1 [Hlk' EQ]]; subst.
      fill_ctxhole. eauto.

      rewrite subst_lookupCmdViaIDFromCmds_none_rev; auto.
      rewrite subst_tmn__getTerminatorID.
      destruct_if; eauto.
Qed.

Lemma subst_lookupInsnViaIDFromFdef_rev: forall f id1 instr2
  (Hlk: lookupInsnViaIDFromFdef (subst_fdef id0 v0 f) id1 = ret instr2),
  exists instr1, 
    lookupInsnViaIDFromFdef f id1 = ret instr1 /\ 
    subst_insn id0 v0 instr1 = instr2.
Proof.
  destruct f as [? bs].
  induction bs; simpl; intros.
    congruence.

    inv_mbind_app.
      inv Hlk.
      symmetry_ctx.
      apply subst_lookupInsnViaIDFromBlock_some_rev in HeqR.
      destruct HeqR as [instr1 [J1 J2]]. fill_ctxhole. eauto.

      rewrite subst_lookupInsnViaIDFromBlock_none_rev; auto.
      apply IHbs; simpl; auto.
Qed.

End SubstOther.


