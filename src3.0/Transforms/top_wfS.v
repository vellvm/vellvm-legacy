Require Import vellvm.

Lemma subst_module_preserves_uniqModules: forall Ms2 M M'
  (HuniqM': uniqModule M') Ms1 
  (HuniqMs: uniqModules (Ms1 ++ M :: Ms2)),
  uniqModules (Ms1 ++ M' :: Ms2).
Proof.
  induction Ms1; simpl; intros; inv HuniqMs; constructor; auto.
Qed.

Ltac inv_module_intro :=
match goal with
| H1 : module_intro ?layouts5 ?namedts5 ?products5 =
       module_intro ?los ?nts ?ps |- _ => inv H1
| _ => idtac
end.

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

Section EqSig.

Definition eq_product_sig (prod1 prod2: product) : Prop :=
match prod1, prod2 with
| product_gvar g1, product_gvar g2 => g1 = g2
| product_fdec f1, product_fdec f2 => f1 = f2
| product_fdef f1, product_fdef f2 => fheaderOfFdef f1 = fheaderOfFdef f2
| _, _ => False
end.

Definition eq_module_sig (m1 m2: module) : Prop :=
let '(module_intro los1 nts1 ps1) := m1 in 
let '(module_intro los2 nts2 ps2) := m2 in
los1 = los2 /\ nts1 = nts2 /\ List.Forall2 eq_product_sig ps1 ps2.

Definition eq_system_sig (s1 s2: system) : Prop :=
List.Forall2 eq_module_sig s1 s2.

Lemma eq_product_sig_refl: forall P, eq_product_sig P P.
Proof.
  unfold eq_product_sig.
  destruct P; auto.
Qed.

Lemma eq_products_sig_refl: forall Ps, Forall2 eq_product_sig Ps Ps.
Proof.
  induction Ps; auto.
    constructor; auto.
      apply eq_product_sig_refl.
Qed.

Lemma eq_module_sig_refl: forall M, eq_module_sig M M.
Proof.
  destruct M as [? ? Ps].
  split; auto.
  split; auto.
    induction Ps; auto.
      apply eq_products_sig_refl.
Qed. 

Lemma eq_system_sig_refl: forall S, eq_system_sig S S.
Proof.
  induction S.
    constructor.

    constructor; auto.
      apply eq_module_sig_refl.
Qed.

Lemma eqsig_lookupTypViaGIDFromProduct: forall id5 P1 P2
  (Heq: eq_product_sig P1 P2),
  lookupTypViaGIDFromProduct P1 id5 = lookupTypViaGIDFromProduct P2 id5.
Proof.
  intros.
  destruct P1, P2; inv Heq; auto.
Qed.

Lemma eqsig_lookupTypViaGIDFromProducts: forall id5 Ps1 Ps2
  (Heq: List.Forall2 eq_product_sig Ps1 Ps2),
  lookupTypViaGIDFromProducts Ps1 id5 = lookupTypViaGIDFromProducts Ps2 id5.
Proof.
  induction 1; simpl in *; auto.
    rewrite IHHeq.
    erewrite eqsig_lookupTypViaGIDFromProduct; eauto.
Qed.

Lemma eqsig_lookupTypViaGIDFromModule: forall id5 M1 M2
  (Heq: eq_module_sig M1 M2),
  lookupTypViaGIDFromModule M1 id5 = lookupTypViaGIDFromModule M2 id5.
Proof.
  destruct M1, M2. simpl.
  intros.
  erewrite eqsig_lookupTypViaGIDFromProducts; eauto.
    tauto.
Qed.

Lemma eqsig_lookupTypViaGIDFromSystem: forall S1 S2
  (Heq: eq_system_sig S1 S2) id5,
  lookupTypViaGIDFromSystem S1 id5 = lookupTypViaGIDFromSystem S2 id5.
Proof.
  induction 1; simpl in *; intros; auto.
    rewrite IHHeq.
    erewrite eqsig_lookupTypViaGIDFromModule; eauto.
Qed.

Variable (M M':module) (S S':system).
Hypothesis (HeqM: eq_module_sig M M') (HeqS: eq_system_sig S S').

(* These lemmas are provable. But it shows a bug in the typing. 
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
(* The following independency lemmas do not mean the rules are over-stated
   When we extend the rules to support multiple modules, we need to find 
   type names from other modules in systems. Then, we should strengthen the
   lemmas to check if the signatures in the two systems match.
*)
Lemma eqsig_wf_styp: forall (td: targetdata)
  (t: typ) (Hwft: wf_styp S td t), wf_styp S' td t.
Proof.
  induction 1; try solve [constructor; auto].
Qed.

Lemma eqsig_noncycled : forall los nts
  (Hnclc: noncycled S los nts), noncycled S' los nts.
Proof.
  intros.
  assert (J:=eqsig_wf_styp).
  induction Hnclc; constructor; auto.
Qed.

Lemma eqsig_wf_namedts :
  forall (p : layouts * namedts), wf_namedts S p -> wf_namedts S' p.
Proof.
  intros p Hwf. destruct p as [los nts].
  inversion Hwf as [? ? ? Hnts Htarget]. subst.
  constructor; trivial. clear Hwf Htarget.

  eapply eqsig_noncycled. eauto.
Qed.

Lemma eqsig_wf_typ: forall (td: targetdata)
  (t: typ) (Hwft: wf_typ S td t), wf_typ S' td t.
Proof.
  intros.
  inv Hwft.
  constructor; eauto using eqsig_wf_styp, eqsig_noncycled.
Qed.

Lemma eqsig_wf_const : forall td c t
  (Hwfc: wf_const S td c t),
  wf_const S' td c t.
Proof.
  intros.
  assert (J3:=@eqsig_wf_typ).
  assert (J4:=@eqsig_lookupTypViaGIDFromSystem S S' HeqS).
  induction Hwfc; subst; try solve 
    [econstructor; try solve [eauto 3 | rewrite <- J4; auto]].
Qed.

Ltac inv_eq_module_sig :=
destruct M, M'; destruct HeqM as [EQ1 [EQ2 HeqM']]; subst.

Lemma eqsig_wf_value : forall f v t
  (Hwfv: wf_value S M f v t),
  wf_value S' M' f v t.
Proof.
  intros.
  assert (J1:=eqsig_wf_const).
  inv_eq_module_sig.
  inv Hwfv; uniq_result;
    constructor; eauto using eqsig_wf_typ.
Qed.

Ltac solve_eqsig_wf_cmd HwfI :=
  intros;
  assert (J2:=eqsig_wf_value);
  assert (J3:=@eqsig_wf_typ);
  inv_eq_module_sig;
  inv HwfI; uniq_result; try solve [
    econstructor; eauto 3
  ].

Lemma eqsig_wf_trunc : forall f b instr
  (HwfI : wf_trunc S M f b instr),
  wf_trunc S' M' f b instr.
Proof. solve_eqsig_wf_cmd HwfI. Qed.

Lemma eqsig_wf_ext : forall f b instr
  (HwfI : wf_ext S M f b instr),
  wf_ext S' M' f b instr.
Proof. solve_eqsig_wf_cmd HwfI. Qed.

Lemma eqsig_wf_cast : forall f b instr
  (HwfI : wf_cast S M f b instr),
  wf_cast S' M' f b instr.
Proof. solve_eqsig_wf_cmd HwfI. Qed.

Lemma eqsig_wf_insn: forall f b instr
  (Hwf : wf_insn S M f b instr), wf_insn S' M' f b instr.
Proof.
  intros.
  assert (J2:=eqsig_wf_value).
  assert (J3:=@eqsig_wf_typ);
  assert (J4:=eqsig_wf_const).
  assert (J5:=@eqsig_wf_trunc f b instr).
  assert (J6:=@eqsig_wf_ext f b instr).
  assert (J7:=@eqsig_wf_cast f b instr).
  inv_eq_module_sig.
  inv Hwf; uniq_result; try solve [
    econstructor; eauto 3
  ].
Qed.

Lemma eqsig_wf_cmds: forall f b cs
  (Hwf : wf_cmds S M f b cs), wf_cmds S' M' f b cs.
Proof.
  intros.
  induction cs; intros.
    constructor.

    inversion Hwf.
    econstructor; eauto using eqsig_wf_insn.
Qed.

Lemma eqsig_wf_phinodes: forall f b ps
  (Hwf : wf_phinodes S M f b ps), wf_phinodes S' M' f b ps.
Proof.
  intros.
  induction ps; intros.
    constructor.

    inversion Hwf.
    econstructor; eauto using eqsig_wf_insn.
Qed.

Lemma eqsig_wf_block: forall f b
  (HfInSM: productInSystemModuleB (product_fdef f) S' M' = true)
  (Hwf : wf_block S M f b), wf_block S' M' f b.
Proof.
  intros.
  assert (J1:=eqsig_wf_phinodes).
  assert (J2:=eqsig_wf_cmds).
  assert (J3:=eqsig_wf_insn).
  inv Hwf.
  constructor; auto.
    destruct M. destruct M'.
    apply blockInSystemModuleFdef_inv in H.
    apply productInSystemModuleB_inv in HfInSM.
    apply blockInSystemModuleFdef_intro; tauto.
Qed.

Lemma eqsig_wf_blocks: forall f bs
  (HfInSM: productInSystemModuleB (product_fdef f) S' M' = true)
  (Hwf : wf_blocks S M f bs), wf_blocks S' M' f bs.
Proof.
  intros.
  assert (J1:=eqsig_wf_block).
  induction Hwf.
    constructor.
    econstructor; eauto 2.
Qed.

Lemma eqsig_wf_gvar: forall gvar5
  (Hwf : wf_gvar S M gvar5), wf_gvar S' M' gvar5.
Proof.
  intros.
  inv_eq_module_sig.
  inv Hwf. 
  constructor; auto.
    eapply eqsig_wf_const; eauto.
Qed.

Lemma eqsig_wf_fheader: forall fheader5 td
  (Hwfh: wf_fheader S td fheader5),
  wf_fheader S' td fheader5.
Proof.
  intros.
  inv Hwfh.
  econstructor; eauto.
    intros t0 Hint0.
    apply H0 in Hint0.
    eapply eqsig_wf_typ; eauto.
Qed.

Lemma eqsig_wf_fdec: forall fdec5
  (Hin': productInSystemModuleB (product_fdec fdec5) S' M' = true)
  (Hwf : wf_fdec S M fdec5), wf_fdec S' M' fdec5.
Proof.
  intros.
  assert (J2:=eqsig_wf_fheader).
  inv_eq_module_sig.
  inv Hwf. 
  constructor; eauto 2.
Qed.

Lemma eqsig_wf_fdef: forall fdef5
  (Hin': productInSystemModuleB (product_fdef fdef5) S' M' = true)
  (Hwf : wf_fdef S M fdef5), wf_fdef S' M' fdef5.
Proof.
  intros.
  assert (J2:=eqsig_wf_fheader).
  assert (J3:=eqsig_wf_blocks).
  inv_eq_module_sig.
  inv Hwf. 
  econstructor; eauto 2.
Qed.

Lemma eqsig_wf_prod: forall prod 
  (HwfP: wf_prod S M prod)
  (Hin': productInSystemModuleB prod S' M' = true),
  wf_prod S' M' prod.
Proof.
  intros.
  assert (J1:=eqsig_wf_gvar).
  assert (J2:=eqsig_wf_fdec).
  assert (J3:=eqsig_wf_fdef).
  inv HwfP; try solve [constructor; try solve [eauto | constructor]].
Qed.

End EqSig.

Section SubstFdefWF.

Variable (f f':fdef) (M M':module) (los:layouts) (nts:namedts) (Ps1 Ps2:products)
         (Ms1 Ms2:modules) (S S':system).
Hypothesis (Heq_fheader: fheaderOfFdef f = fheaderOfFdef f')
           (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
           (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
           (HeqS: S = Ms1 ++ M :: Ms2) (HeqS': S' = Ms1 ++ M' :: Ms2) 
           .

Lemma subst_fdef_eq_module_sig: eq_module_sig M M'.
Proof.
  subst.
  split; auto.
  split; auto.
    induction Ps1.
      constructor; auto.
        apply eq_products_sig_refl.
      constructor; auto.
        apply eq_product_sig_refl.
Qed.

Lemma subst_fdef_eq_system_sig: eq_system_sig S S'.
Proof.
  assert (J1:=subst_fdef_eq_module_sig).
  subst.
  induction Ms1.
    constructor; auto.
      apply eq_system_sig_refl.
    constructor; auto.
      apply eq_module_sig_refl.
Qed.

Lemma subst_fdef_InSystemModuleB:
  productInSystemModuleB (product_fdef f') S' M'.
Proof.
  intros.
  subst.
  apply productInSystemModuleB_intro.
    apply InProductsB_middle.
    apply moduleInSystem_middle.
Qed.  

Lemma subst_fdef_preserves_wf_typ: forall (td: targetdata)
  (t: typ) (Hwft: wf_typ S td t), wf_typ S' td t.
Proof.
  intros.
  eapply eqsig_wf_typ; eauto using subst_fdef_eq_system_sig.
Qed.

Lemma subst_fdef_preserves_wf_const : forall td c t
  (Hwfc: wf_const S td c t),
  wf_const S' td c t.
Proof.
  intros.
  eapply eqsig_wf_const; eauto using subst_fdef_eq_system_sig.
Qed.

Lemma subst_fdef_preserves_wf_value : forall f v t
  (Hwfv: wf_value S M f v t),
  wf_value S' M' f v t.
Proof.
  intros.
  eapply eqsig_wf_value; 
    eauto using subst_fdef_eq_system_sig, subst_fdef_eq_module_sig.
Qed.

Lemma subst_fdef_preserves_wf_other_module: forall md
  (Hin': moduleInSystemB md S' = true)
  (HwfS : wf_module S md), 
  wf_module S' md.
Proof.
  intros. 
  assert (Ja:=subst_fdef_eq_system_sig).
  assert (J:=eqsig_wf_prod).
  assert (J4:=eq_module_sig_refl md).
  subst.
  inv HwfS.
  constructor.
    eapply eqsig_wf_namedts; eauto.

    apply InModulesB_In. auto.

    apply wf_prods_intro.
      intros.
      eapply wf_prods_elim with (prod:=prod) in H1; eauto.
      eapply J; eauto 1.
      apply productInSystemModuleB_intro; auto.
        apply In_InProductsB. auto.
Qed.

Lemma subst_fdef_preserves_wf_the_module: forall 
  (Hin': moduleInSystemB M' S' = true)
  (HwfF': wf_fdef S' M' f') (HwfS : wf_module S M),
  wf_module S' M'.
Proof.
  intros. 
  assert (Ja:=subst_fdef_eq_system_sig).
  assert (Jb:=subst_fdef_eq_module_sig).
  assert (J:=eqsig_wf_prod).
  subst.
  inv HwfS.
  constructor.
    eapply eqsig_wf_namedts; eauto.

    solve_in_list.

    apply wf_prods_intro.
      intros.
      assert (Hin0: 
        productInSystemModuleB prod 
          (Ms1 ++
            module_intro los nts (Ps1 ++ product_fdef f' :: Ps2) :: Ms2)
          (module_intro los nts (Ps1 ++ product_fdef f' :: Ps2)) = true).
        apply productInSystemModuleB_intro.
          apply In_InProductsB. auto.
          apply moduleInSystem_middle.
      destruct_in Hin.
        eapply wf_prods_elim with (prod:=prod) in H5; eauto.
          xsolve_in_list.
      destruct_in Hin.
        constructor; auto.
          constructor.
        eapply wf_prods_elim with (prod:=prod) in H5; eauto.
          xsolve_in_list.
Qed.

Lemma subst_fdef_preserves_wf_system: forall 
  (HwfF': wf_fdef S' M' f') (Huniqf': uniqFdef f') 
  (HwfS : wf_system S),
  wf_system S'.
Proof.
  intros.
  assert (Ja:=subst_fdef_eq_system_sig).
  assert (Jb:=subst_fdef_eq_module_sig).
  assert (J:=subst_fdef_preserves_wf_other_module).
  assert (J':=subst_fdef_preserves_wf_the_module).
  inv HwfS.
  constructor.
    apply wf_modules_intro.
      intros.
      assert (Hin': moduleInSystemB md
        (Ms1 ++ module_intro los nts (Ps1 ++ product_fdef f' :: Ps2) :: Ms2) 
        = true).
        unfold moduleInSystemB.
        apply In_InModulesB; auto.        
      destruct_in Hin.
        eapply wf_modules_elim with (md:=md) in H; eauto.
          xsolve_in_list.
      destruct_in Hin.
        eapply wf_modules_elim 
          with (md:=module_intro los nts (Ps1 ++ product_fdef f :: Ps2)) 
          in H; eauto.
        solve_in_list.

        eapply wf_modules_elim with (md:=md) in H; eauto.
          xsolve_in_list.
    eapply subst_fdef_preserves_uniqSystem in H0; eauto.
Qed.

End SubstFdefWF.

Section SubstFdefSingleWF.

Variable (f f':fdef) (M M':module) (los:layouts) (nts:namedts)(Ps1 Ps2:products).
Hypothesis (Heq_fheader: fheaderOfFdef f = fheaderOfFdef f')
           (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
           (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2)).

Ltac spa_ctx :=
  repeat match goal with
  | |- context [ [?A ] ] => rewrite_env (nil ++ A :: nil)
  | H:context [ [?A ] ] |- _ => rewrite_env (nil ++ A :: nil) in H
  end. 

Lemma subst_fdef_preserves_single_wf_typ: forall 
  (t: typ) (Hwft: wf_typ [M] (los,nts) t), wf_typ [M'] (los,nts) t.
Proof.
  intros. spa_ctx.
  eapply subst_fdef_preserves_wf_typ; eauto.
Qed.

Lemma subst_fdef_preserves_single_wf_const : forall c t
  (Hwfc: wf_const [M] (los,nts) c t), wf_const [M'] (los,nts) c t.
Proof.
  intros. spa_ctx.
  eapply subst_fdef_preserves_wf_const; eauto.
Qed.

Lemma subst_fdef_preserves_single_wf_fheader : forall fh
  (Hwfc: wf_fheader [M] (los,nts) fh), wf_fheader [M'] (los,nts) fh.
Proof.
  intros. spa_ctx.
  eapply eqsig_wf_fheader; eauto.
    eapply subst_fdef_eq_system_sig; eauto.
Qed.

Lemma subst_fdef_preserves_wf_single_module: forall 
  (HwfF': wf_fdef [M'] M' f') (Huniqf': uniqFdef f') 
  (HwfS : wf_system [M]), wf_system [M'].
Proof.
  intros. spa_ctx.
  eapply subst_fdef_preserves_wf_system; eauto.
Qed.

End SubstFdefSingleWF.

Section TopWFS.

Variable (f f':fdef) (los:layouts) (nts:namedts)(Ps1 Ps2:products).

Hypothesis trans_wf_fdef: forall 
  (HwfF: wf_fdef [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
           (module_intro los nts (Ps1 ++ product_fdef f :: Ps2)) f),
  wf_fdef [module_intro los nts (Ps1 ++ product_fdef f' :: Ps2)]
    (module_intro los nts (Ps1 ++ product_fdef f' :: Ps2)) f'.

Hypothesis trans_uniqFdef: forall (Huniq: uniqFdef f), uniqFdef f'.

Hypothesis trans_fheaderOfFdef: fheaderOfFdef f = fheaderOfFdef f'.

Lemma trans_wfS: forall
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

Section SingleModule.

Variable (los:layouts) (nts:namedts) (Ps1 Ps2:products) (M M':module) 
         (f f':fdef).
Hypothesis (HeqM: M = module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
           (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
           (Heq_fheader: fheaderOfFdef f = fheaderOfFdef f').

Lemma pres_lookupTypViaGIDFromSystem: forall id5 t5
  (Hlkup: lookupTypViaGIDFromSystem [M] id5 = Some t5),
  lookupTypViaGIDFromSystem [M'] id5 = Some t5.
Proof.
  subst. simpl. intros.
  clear - Hlkup.
  inv_mbind. 
  induction Ps1; simpl in *.
    rewrite <- HeqR. auto.

    symmetry_ctx.
    inv_mbind_app; auto.
Qed.

Lemma pres_productInSystemModuleB:
  productInSystemModuleB (product_fdef f') [M'] M'.
Proof.
  intros.
  subst.
  apply productInSystemModuleB_intro.
    apply InProductsB_middle.

    unfold moduleInSystem. simpl.
    apply orb_true_intro.
    left. solve_refl.
Qed.

End SingleModule.

End TopWFS.

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

Lemma pres_getArgsIDsOfFdef: forall f,
  getArgsIDsOfFdef f = getArgsIDsOfFdef (pass.(ftrans) f).
Proof.
  intros. destruct f as [fh bs].
  rewrite ftrans_spec. simpl. auto.
Qed.

Lemma pres_getArgsOfFdef: forall f,
  getArgsOfFdef f = getArgsOfFdef (pass.(ftrans) f).
Proof.
  intros. destruct f as [fh bs].
  rewrite ftrans_spec. simpl. auto.
Qed.

Lemma pres_getDefReturnType: forall f,
  Function.getDefReturnType (pass.(ftrans) f) = Function.getDefReturnType f.
Proof.
  intros. destruct f as [fh bs].
  rewrite ftrans_spec. simpl. auto.
Qed.

End TransCFG.

End TransCFG.
