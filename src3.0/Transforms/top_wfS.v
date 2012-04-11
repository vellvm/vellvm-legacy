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

Section SubstFdef.

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
Lemma subst_fdef_preserves_wf_the_prod: forall M M' los nts Ps1 Ps2 Ms1 Ms2
  prod (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HwfPs: wf_prod (Ms1 ++ M :: Ms2) M prod),
  wf_prod (Ms1 ++ M' :: Ms2) M' prod.
Admitted. (* need to fix typing *)

Lemma subst_fdef_preserves_wf_other_prod: forall M M' los nts Ps1 Ps2 Ms1 
  Ms2 prod (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  md (HwfPs: wf_prod (Ms1 ++ M :: Ms2) md prod) (Hin: In md Ms1 \/ In md Ms2),
  wf_prod (Ms1 ++ M' :: Ms2) md prod.
Admitted. (* need to fix typing *)

Lemma subst_fdef_in_ctx_preserves_wf_the_fdef: forall M M' los nts Ps2 Ms1 
  Ms2 Ps1
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2)) f0
  (HwfF: wf_fdef (Ms1 ++ M :: Ms2) M f0),
  wf_fdef (Ms1 ++ M' :: Ms2) M' f0.
Proof.
  intros.
  apply wf_prod_function_def in HwfF; try constructor.
  eapply subst_fdef_preserves_wf_the_prod in HwfF; eauto using in_middle.
  inv HwfF; auto.
Qed.

Lemma subst_fdef_preserves_wf_the_module: forall los nts Ps2 
  Ms1 Ms2 Ps1 S S' M M'
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqS: S = Ms1 ++ M :: Ms2) (HeqS': S' = Ms1 ++ M' :: Ms2) 
  (Hwff': wf_fdef S' M' f') (HwfS : wf_module S M),
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
        constructor; auto. constructor.

        eapply wf_prods_elim with (prod:=prod) in H5; eauto.
          eapply subst_fdef_preserves_wf_the_prod; eauto.
          xsolve_in_list.
Qed.

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

Lemma subst_fdef_preserves_wf_system: forall los nts Ps2 
  Ms1 Ms2 Ps1 S S' M M'
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqS: S = Ms1 ++ M :: Ms2) (HeqS': S' = Ms1 ++ M' :: Ms2) 
  (Hwff': wf_fdef S' M' f') (Huniqf': uniqFdef f') (HwfS : wf_system S),
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

Lemma subst_fdef_preserves_wf_single_module: forall los nts M Ps1 Ps2
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
  (HwfF_pres: wf_fdef [M] M f -> wf_fdef [M] M f') 
  (Huniq_pres: uniqFdef f -> uniqFdef f') (HwfS : wf_system [M]),
  wf_system [module_intro los nts (Ps1 ++ product_fdef f' :: Ps2)].
Proof.
  intros. subst.
  assert (Hwf:=HwfS).
  apply wf_single_system__wf_uniq_fdef in Hwf.
  destruct Hwf as [HwfF HuniqF].
  repeat match goal with
  | |- context [ [?A ] ] => rewrite_env (nil ++ A :: nil)
  | H:context [ [?A ] ] |- _ => rewrite_env (nil ++ A :: nil) in H
  end.
  eapply subst_fdef_preserves_wf_system; eauto.
    apply HwfF_pres in HwfF.
    eapply subst_fdef_in_ctx_preserves_wf_the_fdef in HwfF; eauto.
Qed.

End SubstFdef.

Section TopWFS.

Variable (f f':fdef).

Hypothesis trans_wf_fdef: forall los nts Ps1 Ps2
  (HwfF: wf_fdef [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
           (module_intro los nts (Ps1 ++ product_fdef f :: Ps2)) f),
  wf_fdef [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    (module_intro los nts (Ps1 ++ product_fdef f :: Ps2)) f'.

Hypothesis trans_uniqFdef: forall (Huniq: uniqFdef f), uniqFdef f'.

Hypothesis trans_fheaderOfFdef: fheaderOfFdef f = fheaderOfFdef f'.

Lemma trans_wfS: forall Ps1 Ps2 los nts  
  (HwfS: wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  wf_system [module_intro los nts (Ps1 ++ product_fdef f' :: Ps2)].
Proof.
  intros.
  eapply subst_fdef_preserves_wf_single_module with (f:=f) in HwfS; eauto.
Qed.

End TopWFS.

End TopWFS.

