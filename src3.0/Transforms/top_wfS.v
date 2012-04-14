Require Import vellvm.

Ltac destruct_in H :=
match type of H with
| In _ [_] => simpl in H; destruct H as [H | H]; subst; try tauto
| In _ (_::_) => simpl in H; destruct H as [H | H]; subst; try tauto
| In _ (_++_) => apply in_app_or in H; destruct H as [H | H]
end.

Lemma wf_prods_elim: forall (prod:product) S md prods 
  (Hwfps: wf_prods S md prods) (Hin: In prod prods), 
  wf_prod S md prod.
Proof.
  induction 1; intros; try tauto.
    destruct_in Hin; auto.
Qed.    

Ltac xsolve_in_list :=
match goal with
| |- In ?a (_++_) =>
  apply in_or_app;
  first [left; solve [xsolve_in_list] | right; solve [xsolve_in_list]]
| |- In ?a (_::_) =>
  simpl;
  first [left; solve [auto] | right; solve [xsolve_in_list]]
| |- In ?a _ => solve_in_list || auto
end.

Lemma wf_prods_intro: forall S md prods 
  (H: forall (prod:product) (Hin: In prod prods), wf_prod S md prod),
  wf_prods S md prods.
Proof.
  induction prods; intros.
    constructor.
    constructor.
      apply IHprods. intros.
      apply H. xsolve_in_list.

      apply H. xsolve_in_list.
Qed.    

Lemma wf_modules_elim: forall (md:module) S mds 
  (Hwfms: wf_modules S mds) (Hin: In md mds), 
  wf_module S md.
Proof.
  induction 1; intros; try tauto.
    destruct_in Hin; auto.
Qed.

Lemma wf_modules_intro: forall S mds 
  (H: forall (md:module) (Hin: In md mds), wf_module S md),
  wf_modules S mds.
Proof.
  induction mds; intros.
    constructor.
    constructor.
      apply H. xsolve_in_list.

      apply IHmds. intros.
      apply H. xsolve_in_list.
Qed.    

Lemma subst_module_preserves_uniqModules: forall Ms2 M M'
  (HuniqM': uniqModule M') Ms1 
  (HuniqMs: uniqModules (Ms1 ++ M :: Ms2)),
  uniqModules (Ms1 ++ M' :: Ms2).
Proof.
  induction Ms1; simpl; intros; inv HuniqMs; constructor; auto.
Qed.

Lemma uniqModules_elim: forall M Ms (Hin: In M Ms) (Huniq: uniqModules Ms),
  uniqModule M.
Proof.
  induction Ms; simpl; intros.
    tauto.
    destruct Hin as [Hin | Hin]; subst; tauto.
Qed.

(* The following independency lemmas do not mean the rules are over-stated
   When we extend the rules to support multiple modules, we need to find 
   type names from other modules in systems. Then, we should strengthen the
   lemmas to check if the signatures in the two systems match.
*)
Lemma wf_styp_independent: forall (sys1 sys2 : system) (td: targetdata)
  (t: typ) (Hwft: wf_styp sys1 td t), wf_styp sys2 td t.
Proof.
  induction 1; try solve [constructor; auto].
Qed.

Lemma noncycled_independent : forall (sys1 sys2 : system) los nts
  (Hnclc: noncycled sys1 los nts), noncycled sys2 los nts.
Proof.
  induction 1; constructor; auto.
    eapply wf_styp_independent. eauto.
Qed.

Lemma wf_namedts_independent :
  forall (sys1 sys2 : system) (p : layouts * namedts),
    wf_namedts sys1 p -> wf_namedts sys2 p.
Proof.
  intros sys1 sys2 p Hwf. destruct p as [los nts].
  inversion Hwf as [? ? ? Hnts Htarget]. subst.
  constructor; trivial. clear Hwf Htarget.

  eapply noncycled_independent. eauto.
Qed.

Module TopWFS.

Section Uniqness.

Variable (f f':fdef).
Hypothesis (Heq_fheader: fheaderOfFdef f = fheaderOfFdef f').

Lemma subst_fdef_preserves_uniqProducts: forall Ps2 (Huniqf': uniqFdef f') Ps1 
  (HuniqPs: uniqProducts (Ps1 ++ product_fdef f :: Ps2)),
  uniqProducts (Ps1 ++ product_fdef f' :: Ps2).
Proof.
  unfold uniqProducts.
  induction Ps1; simpl; intros; inv HuniqPs; constructor; auto.
Qed.

Lemma subst_fdef_preserves_uniqProductsIDs: forall Ps2 Ps1,
  getProductsIDs (Ps1 ++ product_fdef f :: Ps2) = 
    getProductsIDs (Ps1 ++ product_fdef f' :: Ps2).
Proof.
  induction Ps1; simpl; intros.
    destruct f as [[]].
    destruct f' as [[]]. 
    inv Heq_fheader. auto.
    
    congruence.
Qed.

Lemma subst_fdef_preserves_uniqModule: forall Ps2 los nts
  (Huniqf': uniqFdef f') Ps1 
  (HuniqM: uniqModule (module_intro los nts (Ps1 ++ product_fdef f :: Ps2))),
  uniqModule (module_intro los nts (Ps1 ++ product_fdef f' :: Ps2)).
Proof.
  intros.
  destruct HuniqM as [J1 [J2 J3]].
  unfold uniqModule. 
  erewrite <- subst_fdef_preserves_uniqProductsIDs; eauto.
  split; eauto using subst_fdef_preserves_uniqProducts.
Qed.

Lemma subst_fdef_preserves_uniqSystem: forall los nts Ps2 
  Ms1 Ms2 Ps1 S S' M M'
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqS: S = Ms1 ++ M :: Ms2) (HeqS': S' = Ms1 ++ M' :: Ms2) 
  (Huniqf': uniqFdef f') (HuniqS : uniqSystem S),
  uniqSystem S'.
Proof.
  unfold uniqSystem.
  intros. subst.
  eapply subst_module_preserves_uniqModules; eauto.
  eapply subst_fdef_preserves_uniqModule; eauto.
  eapply uniqModules_elim in HuniqS; eauto using in_middle. 
Qed.  

End Uniqness.

Section SubstFdefWF.

Variable (f f':fdef).
Hypothesis (Heq_fheader: fheaderOfFdef f = fheaderOfFdef f').

(* This lemma is provable. But it shows a bug in the typing. 
   The wf_const_gid rule does not look up types of functions!!

   The second issue is that in all the rules, module is completely 
   independent. When looking-up gid, wf_const_gid rule searches it from 
   the entire system directly. We should search from the current module,
   and then, for external definitions, we should go find other modules
   in the system. In the case, the system contains only one module (which
   is the assumption of the current design), this is not an issue. But,
   we may want to fix it.

   The third point is that we should simplify typing rules to carry a ctx
   that only takes the signatures of products, rather than the entire 
   definitions, then the following lemma is trivial!
*)
Lemma subst_fdef_preserves_wf_the_prod: forall M M' los nts Ps1 Ps2 Ms1 
  Ms2 prod (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HwfPs: wf_prod (Ms1 ++ M :: Ms2) M prod) 
  (Hin: In prod Ps1 \/ In prod Ps2),
  wf_prod (Ms1 ++ M' :: Ms2) M' prod.
Admitted. (* need to fix typing *)

Lemma subst_fdef_preserves_wf_other_prod: forall M M' los nts Ps1 Ps2 Ms1 
  Ms2 prod (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  md (HwfPs: wf_prod (Ms1 ++ M :: Ms2) md prod) 
  (Hin: In md Ms1 \/ In md Ms2),
  wf_prod (Ms1 ++ M' :: Ms2) md prod.
Admitted. (* need to fix typing, See subst_fdef_preserves_wf_the_prod *)

Lemma subst_fdef_preserves_wf_other_module: forall los nts Ps2 
  Ms1 Ms2 Ps1 S S' M M'
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqS: S = Ms1 ++ M :: Ms2) (HeqS': S' = Ms1 ++ M' :: Ms2) md
  (Hin: In md Ms1 \/ In md Ms2) (HwfS : wf_module S md), 
  wf_module S' md.
Proof.
  intros. subst.
  inv HwfS.
  constructor.
    eapply wf_namedts_independent; eauto.

    destruct Hin as [Hin | Hin]; xsolve_in_list.

    apply wf_prods_intro.
      intros.
      eapply wf_prods_elim with (prod:=prod) in H1; eauto.
        eapply subst_fdef_preserves_wf_other_prod; eauto. 
Qed.

Lemma subst_fdef_preserves_wf_the_module: forall los nts Ps2 
  Ms1 Ms2 Ps1 S S' M M'
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqS: S = Ms1 ++ M :: Ms2) (HeqS': S' = Ms1 ++ M' :: Ms2) 
  (HwfF': wf_fdef (Ms1 ++ M' :: Ms2) M' f') (HwfS : wf_module S M),
  wf_module S' M'.
Proof.
  intros. subst.
  inv HwfS.
  constructor.
    eapply wf_namedts_independent; eauto.

    solve_in_list.

    apply wf_prods_intro.
      intros.

      destruct_in Hin.
        eapply wf_prods_elim with (prod:=prod) in H5; eauto.
          eapply subst_fdef_preserves_wf_the_prod; eauto. 
          xsolve_in_list.
      destruct_in Hin.
        constructor; auto.
          constructor.

        eapply wf_prods_elim with (prod:=prod) in H5; eauto.
          eapply subst_fdef_preserves_wf_the_prod; eauto.
          xsolve_in_list.
Qed.

Lemma subst_fdef_preserves_wf_system: forall los nts Ps2 
  Ms1 Ms2 Ps1 S S' M M'
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqS: S = Ms1 ++ M :: Ms2) (HeqS': S' = Ms1 ++ M' :: Ms2) 
  (HwfF': wf_fdef (Ms1 ++ M' :: Ms2) M' f') (Huniqf': uniqFdef f') 
  (HwfS : wf_system S),
  wf_system S'.
Proof.
  intros.
  inv HwfS.
  constructor.
    apply wf_modules_intro.
      intros.
      destruct_in Hin.
        eapply wf_modules_elim with (md:=md) in H; eauto.
          eapply subst_fdef_preserves_wf_other_module in H; eauto. 
          xsolve_in_list.
      destruct_in Hin.
        eapply wf_modules_elim 
          with (md:=module_intro los nts (Ps1 ++ product_fdef f :: Ps2)) 
          in H; eauto.
          eapply subst_fdef_preserves_wf_the_module in H; eauto. 
        solve_in_list.

        eapply wf_modules_elim with (md:=md) in H; eauto.
          eapply subst_fdef_preserves_wf_other_module in H; eauto. 
          xsolve_in_list.
    eapply subst_fdef_preserves_uniqSystem in H0; eauto.
Qed.

Lemma subst_fdef_preserves_wf_single_module: forall los nts M M' Ps1 Ps2
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HwfF': wf_fdef [M'] M' f') (Huniqf': uniqFdef f') 
  (HwfS : wf_system [M]), wf_system [M'].
Proof.
  intros. subst.
  repeat match goal with
  | |- context [ [?A ] ] => rewrite_env (nil ++ A :: nil)
  | H:context [ [?A ] ] |- _ => rewrite_env (nil ++ A :: nil) in H
  end.
  eapply subst_fdef_preserves_wf_system; eauto.
Qed.

End SubstFdefWF.

Section TopWFS.

Variable (f f':fdef).

Hypothesis trans_wf_fdef: forall los nts Ps1 Ps2
  (HwfF: wf_fdef [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
           (module_intro los nts (Ps1 ++ product_fdef f :: Ps2)) f),
  wf_fdef [module_intro los nts (Ps1 ++ product_fdef f' :: Ps2)]
    (module_intro los nts (Ps1 ++ product_fdef f' :: Ps2)) f'.

Hypothesis trans_uniqFdef: forall (Huniq: uniqFdef f), uniqFdef f'.

Hypothesis trans_fheaderOfFdef: fheaderOfFdef f = fheaderOfFdef f'.

Lemma trans_wfS: forall Ps1 Ps2 los nts  
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  wf_system [module_intro los nts (Ps1 ++ product_fdef f' :: Ps2)].
Proof.
  intros.
  assert (Hwf:=HwfS).
  apply wf_single_system__wf_uniq_fdef in Hwf.
  destruct Hwf as [HwfF HuniqF].
  eapply subst_fdef_preserves_wf_single_module with (f:=f) in HwfS; eauto.
Qed.

End TopWFS.

End TopWFS.

Definition getBlockTmn (b:block) : terminator :=
match b with
| block_intro _ _ _ tmn => tmn
end.

Definition terminator_match (tmn1 tmn2: terminator) : Prop :=
match tmn1, tmn2 with
| insn_return id1 _ _, insn_return id2 _ _ => id1 = id2
| insn_return_void id1, insn_return_void id2 => id1 = id2
| insn_br id1 _ l11 l12, insn_br id2 _ l21 l22 => 
    id1 = id2 /\ l11 = l21 /\ l12 = l22
| insn_br_uncond id1 l1, insn_br_uncond id2 l2 => id1 = id2 /\ l1 = l2
| insn_unreachable i1, insn_unreachable i2 => i1 = i2
| _, _ => False
end.

Structure Pass := mkPass {
btrans: block -> block;
ftrans: fdef -> fdef;
ftrans_spec: forall fh bs, 
  ftrans (fdef_intro fh bs) = fdef_intro fh (List.map btrans bs);
btrans_eq_label: forall b, getBlockLabel b = getBlockLabel (btrans b);
btrans_eq_tmn: forall b, 
  terminator_match (getBlockTmn b) (getBlockTmn (btrans b))
}.

Ltac ftrans_spec_tac :=
repeat match goal with
| H: context [?pass.(ftrans) (fdef_intro _ _)] |- _ => 
  rewrite pass.(ftrans_spec) in H
| |- context [?pass.(ftrans) (fdef_intro _ _)] => rewrite pass.(ftrans_spec)
end.

Ltac btrans_eq_label_tac b :=
let J:=fresh "J" in
let l1:=fresh "l1" in
let R:=fresh "R" in
match goal with
| pass: Pass |- _ =>
  assert (J:=pass.(btrans_eq_label) b);
  remember (btrans pass b) as R;
  destruct R as [l1 ? ? ?]; destruct b; simpl in *; subst l1
end.

Ltac terminator_match_tac :=
match goal with
| J : terminator_match ?t1 ?t2 |- _ =>
  destruct t1; destruct t2; simpl in J; tinv J; auto;
    match goal with
    | J': ?id1 = _ /\ ?id2 = _ /\ ?id3 = _ |- _ =>
      destruct J' as [? [? ?]]; subst id1 id2 id3; auto
    | J': ?id1 = _ /\ ?id2 = _ |- _ =>
      destruct J' as [? ?]; subst id1 id2; auto
    | J' : ?id0 = _ |- _ => subst id0; auto
    end
end.

Module TransCFG.

Section TransCFG.

Context `{pass: Pass}.

(************** Preserving wellformedness **************************************)

Lemma pres_getEntryBlock : forall f b
  (Hentry : getEntryBlock f = Some b),
  getEntryBlock (pass.(ftrans) f) = Some (pass.(btrans) b).
Proof.
  intros. destruct f as [fh bs]. ftrans_spec_tac.
  destruct bs; inv Hentry; auto.
Qed.

Lemma pres_getEntryBlock_None : forall f
  (Hentry : getEntryBlock f = None),
  getEntryBlock (pass.(ftrans) f) = None.
Proof.
  intros. destruct f as [fh bs]. ftrans_spec_tac.
  destruct bs; inv Hentry; auto.
Qed.

Lemma pres_genBlockUseDef_block : forall b ud,
  genBlockUseDef_block b ud =
  genBlockUseDef_block (pass.(btrans) b) ud.
Proof.
  intros.
  assert (J:=pass.(btrans_eq_tmn) b).
  btrans_eq_label_tac b.
  terminator_match_tac.
Qed.

Lemma pres_genBlockUseDef_blocks : forall bs ud,
  genBlockUseDef_blocks bs ud =
  genBlockUseDef_blocks (List.map pass.(btrans) bs) ud.
Proof.
  induction bs; simpl; intros; auto.
    rewrite <- IHbs.
    rewrite <- pres_genBlockUseDef_block; auto.
Qed.

Lemma pres_genBlockUseDef_fdef : forall f,
  genBlockUseDef_fdef f =
  genBlockUseDef_fdef (pass.(ftrans) f).
Proof.
  destruct f as [fh bs]. ftrans_spec_tac. simpl.
  rewrite <- pres_genBlockUseDef_blocks. auto.
Qed.

Lemma pres_hasNonePredecessor : forall f b
  (Hnpred : hasNonePredecessor b (genBlockUseDef_fdef f) = true),
  hasNonePredecessor (pass.(btrans) b)
    (genBlockUseDef_fdef (pass.(ftrans) f)) = true.
Proof.
  unfold hasNonePredecessor. unfold predOfBlock.
  intros. 
  rewrite <- pres_genBlockUseDef_fdef.
  rewrite <- pass.(btrans_eq_label). auto.
Qed.

Lemma pres_InBlocksLabels : forall l0 (bs : blocks)
  (Hin : In l0 (getBlocksLabels (List.map pass.(btrans) bs))),
  In l0 (getBlocksLabels bs).
Proof.
  induction bs as [|b bs]; simpl; auto.
    btrans_eq_label_tac b.
    intro Hin.
    destruct Hin as [Hin | Hin]; auto.
Qed.

Lemma pres_uniqBlocksLabels : forall (bs : blocks)
  (HuniqBs : NoDup (getBlocksLabels bs)),
  NoDup (getBlocksLabels (List.map pass.(btrans) bs)).
Proof.
  induction bs as [|b bs]; simpl; intros; auto.
    btrans_eq_label_tac b.
    inv HuniqBs.
    apply NoDup_cons; eauto using pres_InBlocksLabels.
Qed.

Lemma pres_blockInFdefB : forall f b
  (Hin : blockInFdefB b f = true),
  blockInFdefB (pass.(btrans) b) (pass.(ftrans) f) = true.
Proof.
  intros. destruct f as [fh bs]. ftrans_spec_tac. simpl.
  apply InBlocksB_map; auto.
Qed.

Hint Resolve pres_blockInFdefB: ssa_trans.

Lemma pres_successors_blocks : forall bs,
  successors_blocks bs = successors_blocks (List.map pass.(btrans) bs).
Proof.
  induction bs as [|b bs]; simpl; auto.
    assert (J:=pass.(btrans_eq_tmn) b).
    btrans_eq_label_tac b. 
    rewrite IHbs.
    terminator_match_tac.
Qed.

Hint Resolve pres_successors_blocks: ssa_trans.

Lemma pres_successors : forall f,
  successors f = successors (pass.(ftrans) f).
Proof.
  intros. destruct f. ftrans_spec_tac. simpl. auto with ssa_trans.
Qed.

Lemma pres_bound_blocks : forall bs,
  bound_blocks bs = bound_blocks (List.map pass.(btrans) bs).
Proof.
  induction bs as [|a bs]; simpl; auto.
    btrans_eq_label_tac a. congruence.
Qed.

Lemma pres_bound_fdef : forall f,
  bound_fdef f = bound_fdef (pass.(ftrans) f).
Proof.
  destruct f as [fh bs]. ftrans_spec_tac. simpl.
  apply pres_bound_blocks.
Qed.

Lemma pres_vertexes_fdef: forall f,
  vertexes_fdef f = vertexes_fdef (pass.(ftrans) f).
Proof.
  unfold vertexes_fdef.
  destruct f.  ftrans_spec_tac. simpl. intros.
  rewrite <- pres_bound_blocks. auto.
Qed.

Lemma pres_arcs_fdef: forall f,
  arcs_fdef f = arcs_fdef (pass.(ftrans) f).
Proof.
  unfold arcs_fdef.
  destruct f.  ftrans_spec_tac. simpl. intros.
  rewrite <- pres_successors_blocks. auto.
Qed.

Lemma pres_reachable : forall f,
  reachable f = reachable (pass.(ftrans) f).
Proof.
  intros.
  unfold reachable.
  case_eq (getEntryBlock f).
    intros b Hentry.
    apply pres_getEntryBlock in Hentry; eauto.
    rewrite Hentry.
    btrans_eq_label_tac b.
    rewrite <- pres_vertexes_fdef.
    rewrite <- pres_arcs_fdef. auto.

    intro Hentry.
    apply pres_getEntryBlock_None in Hentry; eauto.
    rewrite Hentry. auto.
Qed.

Lemma pres_isReachableFromEntry : forall f b,
  isReachableFromEntry f b =
    isReachableFromEntry (pass.(ftrans) f) (pass.(btrans) b).
Proof.
  unfold isReachableFromEntry. intros.
  btrans_eq_label_tac b. 
  rewrite <- pres_reachable; auto.
Qed.

Lemma pres_areachable_aux : forall f,
  areachable_aux f = areachable_aux (pass.(ftrans) f).
Proof.
  intros.
  unfold areachable_aux.
  case_eq (getEntryBlock f).
    intros b Hentry.
    apply pres_getEntryBlock in Hentry; eauto.
    rewrite Hentry.
    btrans_eq_label_tac b.
    rewrite <- pres_successors. auto.

    intro Hentry.
    apply pres_getEntryBlock_None in Hentry; eauto.
    rewrite Hentry. auto.
Qed.

Lemma pres_reachablity_analysis : forall f,
  reachablity_analysis f = reachablity_analysis (pass.(ftrans) f).
Proof.
  intros.
  unfold reachablity_analysis.
  case_eq (getEntryBlock f).
    intros b Hentry.
    apply pres_getEntryBlock in Hentry; eauto.
    rewrite Hentry.
    btrans_eq_label_tac b.
    rewrite <- pres_bound_fdef.
    rewrite <- pres_areachable_aux. auto.

    intro Hentry.
    apply pres_getEntryBlock_None in Hentry; eauto.
    rewrite Hentry. auto.
Qed.

Lemma pres_blockStrictDominates : forall f b1 b2,
  blockStrictDominates f b1 b2 <->
    blockStrictDominates (pass.(ftrans) f) (pass.(btrans) b1) (pass.(btrans) b2).
Proof.
  intros.
  unfold blockStrictDominates. 
  btrans_eq_label_tac b1. 
  btrans_eq_label_tac b2. 
  unfold dom_analyze. destruct f as [fh bs]. ftrans_spec_tac.
  rewrite <- pres_successors_blocks.
  remember (entry_dom bs) as R1.
  remember (entry_dom (List.map pass.(btrans) bs)) as R2.
  destruct R1 as [x1 Hx1].
  destruct R2 as [x2 Hx2].
  destruct x1 as [x1|].
  Case "1".
    destruct x1 as [le1 start1].
    destruct start1.
    destruct bs_contents as [|l2' bs_contents]; tinv Hx1.
    destruct x2 as [x2|].
    SCase "1.1".
      destruct x2 as [le2 start2].
      destruct start2.
      destruct bs_contents as [|l3 bs_contents]; tinv Hx2.
      destruct bs as [|b bs]; tinv HeqR1.
      assert (J:=pass.(btrans_eq_label) b).
      simpl in *.
      destruct (btrans pass b). 
      destruct b. 
      inv HeqR1. inv HeqR2. simpl in J. subst.
      eapply blockStrictDominates_iff; eauto.
      rewrite pres_bound_blocks; auto.
    SCase "1.2".
      destruct bs; simpl in *; tinv HeqR1.
        inv Hx2.
  Case "2".
    subst. simpl in *. inv HeqR2. split; intro; auto.
Qed.

Lemma pres_blockDominates : forall f b1 b2,
  blockDominates f b1 b2 <->
    blockDominates (pass.(ftrans) f) (pass.(btrans) b1) (pass.(btrans) b2).
Proof.
  intros.
  unfold blockDominates.
  btrans_eq_label_tac b1. 
  btrans_eq_label_tac b2. 
  unfold dom_analyze. destruct f as [fh bs]. ftrans_spec_tac.
  rewrite <- pres_successors_blocks.
  remember (entry_dom bs) as R1.
  remember (entry_dom (List.map pass.(btrans) bs)) as R2.
  destruct R1 as [x1 Hx1].
  destruct R2 as [x2 Hx2].
  destruct x1 as [x1|].
  Case "1".
    destruct x1 as [le1 start1].
    destruct start1.
    destruct bs_contents as [|l2' bs_contents]; tinv Hx1.
    destruct x2 as [x2|].
    SCase "1.1".
      destruct x2 as [le2 start2].
      destruct start2.
      destruct bs_contents as [|l3 bs_contents]; tinv Hx2.
      destruct bs as [|b bs]; tinv HeqR1.
      assert (J:=pass.(btrans_eq_label) b).
      simpl in *.
      destruct (btrans pass b). 
      destruct b. 
      inv HeqR1. inv HeqR2. simpl in J. subst.
      eapply blockDominates_iff; eauto.
      rewrite pres_bound_blocks; auto.
    SCase "1.2".
      destruct bs; simpl in *; tinv HeqR1.
        inv Hx2.
  Case "2".
    subst. simpl in *. inv HeqR2. split; intro; auto.
Qed.

Lemma pres_lookupBlockViaLabelFromBlocks : forall l5 bs b,
  lookupBlockViaLabelFromBlocks bs l5 = ret b ->
  lookupBlockViaLabelFromBlocks (List.map pass.(btrans) bs) l5 =
    ret (pass.(btrans) b).
Proof.
  unfold lookupBlockViaLabelFromBlocks.
  induction bs as [|a]; simpl; intros.
    congruence.

    btrans_eq_label_tac a. 
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l5 l0);
      subst; inv H; auto.
      congruence.
Qed.

Hint Resolve pres_lookupBlockViaLabelFromBlocks : ssa_trans.

Lemma pres_lookupBlockViaLabelFromFdef : forall f l5 b,
  lookupBlockViaLabelFromFdef f l5 = ret b ->
  lookupBlockViaLabelFromFdef (pass.(ftrans) f) l5 =
    ret (pass.(btrans) b).
Proof.
  destruct f. ftrans_spec_tac. 
  intros. apply pres_lookupBlockViaLabelFromBlocks; auto.
Qed.

Lemma pres_predOfBlock : forall b,
  predOfBlock b = predOfBlock (pass.(btrans) b).
Proof.
  intros.
  btrans_eq_label_tac b. auto.
Qed.

End TransCFG.

End TransCFG.
