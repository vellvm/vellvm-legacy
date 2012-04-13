Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import targetdata_props.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import typings.
Require Import infrastructure_props.
Require Import analysis.
Require Import util.

Import LLVMinfra.
Import LLVMtd.
Import LLVMtypings.
Import LLVMgv.
Import AtomSet.

(* Basic inversion lemmas *)

Lemma wf_value_list_cons_iff p l :
  wf_value_list (p :: l) <->
  wf_value_list l /\
  let '(s, m, f, v, t) := p in wf_value s m f v t.
Proof.
  unfold wf_value_list; repeat rewrite <- Forall_forall; split; intros H.
  inversion H; subst. eauto.
  inversion H; constructor; eauto.
Qed.

(********************************************)
(** * Inversion of well-formedness *)

Lemma getEntryBlock_inv : forall
  (bs : blocks)
  (l3 : l)
  (l' : l)
  (ps : phinodes)
  (cs : cmds)
  (tmn : terminator)
  (fh : fheader)
  (s : system)
  (m : module)
  (HwfF : wf_fdef s m (fdef_intro fh bs))
  (HBinF : InBlocksB (block_intro l3 ps cs tmn) bs = true)
  (a : atom)
  (Hsucc : In l' (successors_terminator tmn))
  ps1 cs1 tmn1
  (H : getEntryBlock (fdef_intro fh bs) = ret block_intro a ps1 cs1 tmn1),
  l' <> a.
Proof.
  intros.
   destruct (eq_atom_dec l' a); subst; auto.
   inv HwfF.
   match goal with
   | H11: hasNonePredecessor ?b _ = _,
     H7: getEntryBlock _ = Some ?b,
     H: getEntryBlock _ = _ |- _ =>
       rename H11 into J1; rename H7 into J2; rename H into J3;
       simpl in J1; rewrite J3 in J2; inv J2;
       clear - J1 Hsucc HBinF
   end.
   induction bs; simpl in *.
     inversion HBinF.

     apply orb_prop in HBinF.
     destruct HBinF as [HBinF | HBinF].
       apply blockEqB_inv in HBinF; subst.
       simpl in J1.
       destruct tmn as [| |? ? l1 l2| l1 |]; try solve [inversion Hsucc].
         unfold hasNonePredecessor in J1.
         unfold predOfBlock in J1. simpl in J1.
         simpl in Hsucc.
         destruct Hsucc as [Hsucc | [Hsucc | Hsucc]]; subst;
           try inversion Hsucc.

           destruct (@lookupAL_update_udb_eq (update_udb nil l3 l2) l3 a)
             as [re [Hlk Hin]].
           apply lookupAL_genBlockUseDef_blocks_spec with (bs:=bs) in Hlk.
           destruct Hlk as [re' [Hlk Hinc]].
           rewrite Hlk in J1.
           destruct re'; inversion J1.
           apply Hinc in Hin. inversion Hin.

           destruct (@lookupAL_update_udb_eq nil l3 a) as [re [Hlk Hin]].
           apply lookupAL_update_udb_spec with (l1:=l3)(l2:=l1) in Hlk.
           destruct Hlk as [re1 [Hlk Hinc1]].
           apply lookupAL_genBlockUseDef_blocks_spec with (bs:=bs) in Hlk.
           destruct Hlk as [re2 [Hlk Hinc2]].
           rewrite Hlk in J1.
           destruct re2; inversion J1.
           apply Hinc1 in Hin.
           apply Hinc2 in Hin.
           inversion Hin.

         unfold hasNonePredecessor in J1.
         unfold predOfBlock in J1. simpl in J1.
         simpl in Hsucc.
         destruct Hsucc as [Hsucc | Hsucc]; subst; try inversion Hsucc.
           destruct (@lookupAL_update_udb_eq nil l3 a) as [re [Hlk Hin]].
           apply lookupAL_genBlockUseDef_blocks_spec with (bs:=bs) in Hlk.
           destruct Hlk as [re' [Hlk Hinc]].
           rewrite Hlk in J1.
           destruct re'; inversion J1.
           apply Hinc in Hin. inversion Hin.
     apply hasNonPredecessor__mono in J1; eauto.
Qed.

Lemma entryBlock_has_no_pred: forall s m F B l0 l3 ps cs tmn
  (HwfF: wf_fdef s m F) (Hentry:  getEntryBlock F = Some B) (Huniq:uniqFdef F)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) F = true)
  (Hsucc : In l0 (successors_terminator tmn))
  (Hlkup: lookupBlockViaLabelFromFdef F l0 = Some B),
  False.
Proof.
  intros.
  destruct B as [l1 ps1 cs1 tmn1].
  apply lookupBlockViaLabelFromFdef_inv in Hlkup; auto.
  destruct Hlkup as [EQ HBinF']; subst.
  destruct F as [fh bs].
  simpl in HBinF. clear HBinF'.
  eapply getEntryBlock_inv in Hentry; eauto.
Qed.

Lemma wf_modules__wf_module : forall S ms m,
  wf_modules S ms ->
  moduleInSystemB m ms ->
  wf_module S m.
Proof.
  induction ms; intros m HwfS HMinS; simpl in *.
    inv HMinS.

    inv HwfS.
    apply orb_prop in HMinS.
    inv HMinS; auto.
      apply moduleEqB_inv in H.
      subst. auto.
Qed.

Lemma wf_prods__wf_prod : forall S M Ps P,
  wf_prods S M Ps ->
  InProductsB P Ps = true ->
  wf_prod S M P.
Proof.
  induction Ps; intros P HwfPs HPinPs.
    inv HPinPs.

    inv HwfPs.
    simpl in HPinPs.
    apply orb_prop in HPinPs.
    inv HPinPs; eauto.
      apply productEqB_inv in H.
      subst. auto.
Qed.

Lemma wf_system__wf_fdef : forall S los nts Ps f,
  wf_system S ->
  moduleInSystemB (module_intro los nts Ps) S = true ->
  InProductsB (product_fdef f) Ps = true ->
  wf_fdef S (module_intro los nts Ps) f.
Proof.
  intros S los nts Ps f HwfS HMinS HPinM.
  inv HwfS.
  eapply wf_modules__wf_module in HMinS; eauto.
  inv HMinS.
  match goal with
  | H7: wf_prods _ _ _ |- _ =>
    eapply wf_prods__wf_prod in H7; eauto; inv H7; auto
  end.
Qed.

Lemma wf_system__wf_fdec : forall S los nts Ps f,
  wf_system S ->
  moduleInSystemB (module_intro los nts Ps) S = true ->
  InProductsB (product_fdec f) Ps = true ->
  wf_fdec S (module_intro los nts Ps) f.
Proof.
  intros S los nts Ps f HwfS HMinS HPinM.
  inv HwfS.
  eapply wf_modules__wf_module in HMinS; eauto.
  inv HMinS.
  match goal with
  | H7: wf_prods _ _ _ |- _ =>
    eapply wf_prods__wf_prod in H7; eauto; inv H7; auto
  end.
Qed.

Lemma wf_system__uniqFdef : forall S los nts Ps f,
  wf_system S ->
  moduleInSystemB (module_intro los nts Ps) S = true ->
  InProductsB (product_fdef f) Ps = true ->
  uniqFdef f.
Proof.
  intros.
  inv H.
  apply uniqSystem__uniqFdef with (S:=S)(M:=module_intro los nts Ps); auto.
  unfold productInSystemModuleB, productInModuleB, is_true.
  apply andb_true_iff; auto.
Qed.

Lemma wf_system__uniqFdec : forall S los nts Ps f,
  wf_system S ->
  moduleInSystemB (module_intro los nts Ps) S = true ->
  InProductsB (product_fdec f) Ps = true ->
  uniqFdec f.
Proof.
  intros.
  inv H.
  apply uniqSystem__uniqFdec with (S:=S)(M:=module_intro los nts Ps); auto.
  unfold productInSystemModuleB, productInModuleB, is_true.
  apply andb_true_iff; auto.
Qed.

Lemma wf_blocks__wf_block : forall s m f bs b,
  wf_blocks s m f bs ->
  InBlocksB b bs = true ->
  wf_block s m f b.
Proof.
  induction bs; intros b Hwfbs Hbinbs.
    inv Hbinbs.

    inv Hwfbs.
    simpl in Hbinbs.
    apply orb_prop in Hbinbs.
    inv Hbinbs; eauto.
      apply blockEqB_inv in H.
      subst. auto.
Qed.

Lemma wf_fdef__blockInFdefB__wf_block : forall b S M f,
  blockInFdefB b f = true ->
  wf_fdef S M f ->
  wf_block S M f b.
Proof.
  intros.
  inv H0.
  eapply wf_blocks__wf_block; eauto.
Qed.

Lemma wf_system__blockInFdefB__wf_block : forall b f ps los nts s,
  blockInFdefB b f = true ->
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system s ->
  wf_block s (module_intro los nts ps) f b.
Proof.
  intros.
  eapply wf_system__wf_fdef in H1; eauto.
  inv H1.
  eapply wf_blocks__wf_block; eauto.
Qed.

Lemma wf_system__lookup__wf_block : forall b f l0 ps los nts s,
  Some b = lookupBlockViaLabelFromFdef f l0 ->
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system s ->
  wf_block s (module_intro los nts ps) f b.
Proof.
  intros.
  eapply wf_system__blockInFdefB__wf_block; eauto.
    symmetry in H. destruct b.
    assert (uniqFdef f) as J. eapply wf_system__uniqFdef; eauto.
    eapply lookupBlockViaLabelFromFdef_inv in H; eauto.
    destruct H; auto.
Qed.

Lemma wf_system__uniq_block : forall b f ps los nts s,
  blockInFdefB b f = true ->
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system s ->
  NoDup (getBlockLocs b).
Proof.
  intros.
  eapply wf_system__uniqFdef in H1; eauto.
  destruct f as [f bs]. destruct f. simpl in *.
  inv H1. inv H3.
  eapply uniqBlocksLocs__uniqBlockLocs; eauto.
Qed.

Lemma wf_cmds__wf_cmd : forall s m f b cs c,
  wf_cmds s m f b cs ->
  In c cs ->
  wf_insn s m f b (insn_cmd c).
Proof.
  induction cs; intros.
    inversion H0.

    simpl in H0.
    inv H.
    destruct H0 as [H0 | H0]; subst; eauto.
Qed.

Lemma wf_system__wf_cmd : forall l1 ps1 cs1 tmn1 f ps los nts s c,
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system s ->
  In c cs1 ->
  wf_insn s (module_intro los nts ps) f (block_intro l1 ps1 cs1 tmn1)
    (insn_cmd c).
Proof.
  intros.
  eapply wf_system__blockInFdefB__wf_block in H1; eauto.
  inv H1.
  eapply wf_cmds__wf_cmd; eauto.
Qed.

Lemma wf_system__wf_tmn : forall l1 ps1 cs1 tmn1 f ps los nts s,
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system s ->
  wf_insn s (module_intro los nts ps) f (block_intro l1 ps1 cs1 tmn1)
    (insn_terminator tmn1).
Proof.
  intros.
  eapply wf_system__blockInFdefB__wf_block in H1; eauto.
  inv H1. auto.
Qed.

Lemma wf_fdef__wf_cmd : forall l1 ps1 cs1 tmn1 s m f c,
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  wf_fdef s m f ->
  In c cs1 ->
  wf_insn s m f (block_intro l1 ps1 cs1 tmn1) (insn_cmd c).
Proof.
  intros.
  eapply wf_fdef__blockInFdefB__wf_block in H; eauto.
  inv H. eapply wf_cmds__wf_cmd; eauto.
Qed.

Lemma wf_fdef__wf_tmn : forall l1 ps1 cs1 tmn1 s m f,
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  wf_fdef s m f ->
  wf_insn s m f (block_intro l1 ps1 cs1 tmn1) (insn_terminator tmn1).
Proof.
  intros.
  eapply wf_fdef__blockInFdefB__wf_block in H; eauto.
  inv H. auto.
Qed.

Lemma wf_fdef__non_entry: forall s m f,
  wf_fdef s m f -> getEntryBlock f <> None.
Proof.
  intros. inv H.
  match goal with
  | H2: getEntryBlock ?f = Some _ |- getEntryBlock ?f <> None =>
      rewrite H2; congruence
  end.
Qed.

Lemma wf_tmn__wf_value : forall s m f b tmn v,
  wf_insn s m f b (insn_terminator tmn) ->
  valueInTmnOperands v tmn ->
  exists t, wf_value s m f v t.
Proof.
  intros s m f b tmn v Hwfinsn HvInOps.
  inv Hwfinsn; simpl in HvInOps; subst; try solve [
    eauto | inversion HvInOps
  ].
Qed.

Lemma wf_value__wf_typ : forall s los nts ps f v t,
  wf_value s (module_intro los nts ps) f v t ->
  wf_typ s (los, nts) t /\ feasible_typ (los, nts) t.
Proof.
  intros.
  inv H; eauto using wf_typ__feasible_typ.
Qed.

Lemma entryBlock_has_no_phinodes : forall s f l1 ps1 cs1 tmn1 los nts ps,
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system s ->
  getEntryBlock f = Some (block_intro l1 ps1 cs1 tmn1) ->
  ps1 = nil.
Proof.
  intros s f l1 ps1 cs1 tmn1 los nts ps HFinP HMinS Hwfs Hentry.
  assert (wf_fdef s (module_intro los nts ps) f) as Hwff.
    eapply wf_system__wf_fdef; eauto.
  assert (wf_block s (module_intro los nts ps) f
    (block_intro l1 ps1 cs1 tmn1)) as Hwfb.
    apply entryBlockInFdef in Hentry.
    eapply wf_system__blockInFdefB__wf_block; eauto.
  inv Hwfb.
  match goal with
  | H8: wf_cmds _ _ _ _ _, H9: wf_insn _ _ _ _ _ |- _ => clear H8 H9
  end.
  destruct ps1; auto.
  match goal with
  | H7: wf_phinodes _ _ _ _ _ |- _ => inv H7
  end.
  match goal with
  | H8: wf_phinodes _ _ _ _ _ |- _ => clear H8
  end.
  match goal with
  | H5: wf_insn _ _ _ _ _ |- _ => inv H5
  end.
  match goal with
  | H11: wf_phinode _ _ _ |- _ => inv H11
  end.
  match goal with
  | H5: check_list_value_l _ _ _ |- _ =>
    unfold check_list_value_l in H5;
    remember (split value_l_list) as R;
    destruct R;
    destruct H5 as [J1 [J2 J3]]
  end.
  inv Hwff.
  match goal with
  | Hentry: getEntryBlock _ = Some (block_intro _ _ _ _),
    H14: getEntryBlock _ = Some _ |- _ =>
    rewrite H14 in Hentry; inv Hentry
  end.
  match goal with
  | H18: hasNonePredecessor _ _ = _ |- _ =>
    unfold hasNonePredecessor in H18;
    simpl in *;
    destruct (predOfBlock
            (block_intro l1 (insn_phi id5 typ5 value_l_list :: ps1) cs1 tmn1)
            (genBlockUseDef_blocks blocks5 nil)); inversion H18
  end.
  simpl in J1. contradict J1. omega.
Qed.

Lemma wf_operand_list__wf_operand : forall id_list fdef5 block5 insn5 id_ n,
  wf_operand_list
  (List.map
    (fun id_ : id => (fdef5, block5, insn5, id_)) id_list) ->
  nth_error id_list n = Some id_ ->
  wf_operand fdef5 block5 insn5 id_.
Proof.
  induction id_list; intros fdef5 block5 insn5 id_ n Hwfops Hnth.
    destruct n; inversion Hnth.

    unfold wf_operand_list in *. simpl in Hwfops.
    destruct n; inv Hnth; eauto.
      apply (Hwfops (_, _, _, _)). eauto.
      eapply IHid_list; eauto. intros p Hp. apply Hwfops. eauto.
Qed.

Lemma wf_phi_operands__elim : forall f b i0 t0 vls0 vid1 l1 n,
  wf_phi_operands f b i0 t0 vls0 ->
  nth_error vls0 n = Some (value_id vid1, l1) ->
  exists b1,
    lookupBlockViaLabelFromFdef f l1 = Some b1 /\
    ((exists vb,
       lookupBlockViaIDFromFdef f vid1 = Some vb /\
       (blockDominates f vb b1 \/ not (isReachableFromEntry f b))) \/
    In vid1 (getArgsIDsOfFdef f)).
Proof.
  induction vls0; intros.
    destruct n; inversion H0.
    destruct t0; inv H; destruct n; inv H0; eauto.
Qed.

Lemma wf_value_list__getValueViaLabelFromValuels__wf_value : forall
  (s : system) (m : module) (f : fdef) (l1 : l) (t0 : typ) v l2
  (H2 : wf_value_list
    (List.map
      (fun (p : value * l) => 
        let '(v, _) := p in (s, m, f, v, t0)) l2))
  (J : getValueViaLabelFromValuels l2 l1 = ret v),
  wf_value s m f v t0.
Proof.
  intros.
  induction l2; simpl in *.
    inversion J. destruct a.

    unfold wf_value_list in *. simpl in H2.
    destruct (l0==l1); subst; eauto.
      inv J. eapply (H2 (_, _, _, _, _)). auto.
      apply IHl2; auto.
      intros p Hp. apply H2. right. auto.
Qed.

Lemma wf_value_list__valueInListValue__wf_value : forall s m f v value_list
  (J : valueInListValue v value_list)
  (H1 : wf_value_list
          (List.map
            (fun (p : sz * value) =>
              (s, m, f, snd p, typ_int Size.ThirtyTwo)) value_list)),
  exists t : typ, wf_value s m f v t.
Proof.
  intros.
  unfold valueInListValue in J.
  induction value_list; simpl in *.
    inversion J.

    unfold wf_value_list in *. simpl in *.
    destruct J as [J | J]; subst; eauto.
      exists (typ_int Size.ThirtyTwo).
        apply (H1 (_, _, _, _, _)).
        left. trivial.
      apply IHvalue_list. trivial.
      intros p Hp. apply H1. right. trivial.
Qed.

Lemma wf_value_list__valueInParams__wf_value : forall s m f v tv_list
  (H4 : wf_value_list
          (List.map
            (fun (p : typ * _ * value) =>
              let '(typ_', attr, value_'') := p in
                (s, m, f, value_'', typ_')) tv_list))
  (HvInOps : valueInParams v
              (List.map
                 (fun p : typ * _ * value =>
                   let '(typ_', attr, value_'') := p in
                     (typ_', attr, value_''))
                 tv_list)),
  exists t : typ, wf_value s m f v t.
Proof.
  intros.
  unfold valueInParams in *.
  induction tv_list; simpl in *.
    inversion HvInOps. destruct a as [[? ?] ?].

    unfold wf_value_list in *. simpl in H4.
    remember (split
                (List.map
                  (fun p : typ * _ * value =>
                   let '(typ_', attr, value_'') := p in
                     (typ_', attr, value_'')) tv_list)) as R.
    destruct R.
    simpl in HvInOps. destruct HvInOps.
      subst. exists t. apply (H4 (_, _, _, _, _)). left. trivial.
      apply IHtv_list; trivial. intros p Hp. apply H4. right. trivial.
Qed.

Lemma wf_value_list__in_params__wf_value : forall S m F tvs
  (H18: wf_value_list
          (List.map
                (fun p : (typ * attributes * value) =>
                  let '(typ_', attr, value_'') := p in
                    (S, m, F, value_'', typ_'))
                tvs))
  (t1 : typ) a1 (v1 : value),
    In (t1, a1, v1)
     (List.map
        (fun p : typ * attributes * value =>
          let '(typ_', attr, value_'') := p in (typ_', attr, value_''))
        tvs) ->
    wf_value S m F v1 t1.
Proof.
  induction tvs; simpl; intros.
    inv H. destruct a as [[? ?] ?].

    destruct H as [H | H]; eauto.
      inv H. apply (H18 (_, _, _, _, _)). left. trivial.
      eapply IHtvs; eauto. intros p Hp. apply H18. right. trivial.
Qed.

Lemma wf_cmd__wf_value : forall s m f b c v,
  wf_insn s m f b (insn_cmd c) ->
  valueInCmdOperands v c ->
  exists t, wf_value s m f v t.
Proof.
  intros s m f b c v Hwfinsn HvInOps.
  inv Hwfinsn; simpl in HvInOps; subst; try solve [
    eauto |
    destruct HvInOps as [HvInOps | HvInOps]; subst; eauto |
    match goal with
    | H4: ?f _ _ _ _ _ |- _ => inv H4; eauto
    end
  ].

    destruct HvInOps as [HvInOps | [HvInOps | HvInOps]]; subst; eauto.

    destruct HvInOps as [HvInOps | HvInOps]; subst; eauto.
      eapply wf_value_list__valueInParams__wf_value; eauto.
      unfold wf_value_list in *.
      remove_irrelevant wf_value.
      solve_forall_like_ind.
Qed.

Lemma wf_operand_list__elim : forall ops f1 b1 insn1 id1,
  wf_operand_list ops ->
  In (f1, b1, insn1, id1) ops ->
  wf_operand f1 b1 insn1 id1.
Proof.
  induction ops; intros f1 b1 insn1 id1 Hwfops Hin; simpl in *.
    inversion Hin.

    destruct Hin as [Hin | Hin]; subst; apply (Hwfops (_, _, _, _)).
      left. trivial.
      right. trivial.
Qed.

Lemma wf_insn__wf_insn_base : forall s m f b insn,
  ~ isPhiNode insn -> wf_insn s m f b insn -> wf_insn_base f b insn.
Proof.
  intros s m f b insn Hnonphi Hwf.
  inv Hwf; auto.
    inv H; auto.
    inv H; auto.
    inv H; auto.
    unfold isPhiNode in Hnonphi. simpl in Hnonphi. contradict Hnonphi; auto.
Qed.

Lemma wf_value_list__getValueViaBlockFromValuels__wf_value : forall
  (s : system)  (m : module)  (f : fdef) b (t0 : typ) v l2
  (H2 : wf_value_list
          (List.map
            (fun (p : value * l) =>
              let '(v, _) := p in (s, m, f, v, t0)) l2))
  (J : getValueViaBlockFromValuels l2 b = ret v),
  wf_value s m f v t0.
Proof.
  intros. destruct b. simpl in J.
  eapply wf_value_list__getValueViaLabelFromValuels__wf_value in H2; eauto.
Qed.

Lemma wf_fdef__wf_phinodes : forall s m f l3 cs tmn ps,
  wf_fdef s m f ->
  blockInFdefB (block_intro l3 ps cs tmn) f ->
  wf_phinodes s m f (block_intro l3 ps cs tmn) ps.
Proof.
  intros.
  inv H.
  match goal with
  | H6: wf_blocks _ _ _ _ |- _ =>
    eapply wf_blocks__wf_block in H6; eauto;
    inv H6; auto
  end.
Qed.

Lemma wf_typ_list__in_args__wf_typ : forall s td typ_attributes_id_list
  (H18: wf_typ_list
          (List.map
            (fun (p : typ * attributes * id) =>
              let '(t, _, _) := p in (s, td, t)) typ_attributes_id_list))
  t a i0,
    In (t, a, i0)
       (List.map
         (fun p : typ * attributes * id =>
           let '(typ_, attributes_, id_) := p in
             (typ_, attributes_, id_)) typ_attributes_id_list) ->
    wf_typ s td t.
Proof.
  induction typ_attributes_id_list; simpl; intros.
    inv H.

    destruct a as [[? ?] ?].
    destruct H as [H | H]; eauto.
      inv H. apply (H18 (_, _, _)). left. trivial.
      eapply IHtyp_attributes_id_list; eauto.
      intros p Hp. apply H18. right. trivial.
Qed.

Lemma wf_trunc__wf_typ : forall s los nts ps f b i0 t t0 v t1
  (H: wf_trunc s (module_intro los nts ps) f b
    (insn_cmd (insn_trunc i0 t t0 v t1))),
  wf_typ s (los, nts) t1 /\ feasible_typ (los, nts) t1.
Proof.
  intros.
  inv H; eauto using wf_typ__feasible_typ.
Qed.

Lemma wf_trunc__wf_value : forall s los nts ps f b i0 t t0 v t1
  (H: wf_trunc s (module_intro los nts ps) f b
    (insn_cmd (insn_trunc i0 t t0 v t1))),
  wf_value s (module_intro los nts ps) f v t0.
Proof.
  intros.
  inv H; auto.
Qed.

Lemma wf_ext__wf_typ : forall s los nts ps f b i0 e t0 v t1
  (H: wf_ext s (module_intro los nts ps) f b
    (insn_cmd (insn_ext i0 e t0 v t1))),
  wf_typ s (los, nts) t1 /\ feasible_typ (los, nts) t1.
Proof.
  intros.
  inv H; eauto using wf_typ__feasible_typ.
Qed.

Lemma wf_ext__wf_value : forall s los nts ps f b i0 e t0 v t1
  (H: wf_ext s (module_intro los nts ps) f b
    (insn_cmd (insn_ext i0 e t0 v t1))),
  wf_value s (module_intro los nts ps) f v t0.
Proof.
  intros.
  inv H; auto.
Qed.

(********************************************)
(** * Correctness of analysis *)

Lemma dom_successors : forall
  (bs : blocks)
  (l3 : l)
  (l' : l)
  ps cs tmn fh s m
  (HwfF : wf_fdef s m (fdef_intro fh bs))
  (Huniq : uniqBlocks bs)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) (fdef_intro fh bs) = true)
  (Doms : AMap.t
           (Dominators.t (bound_fdef (fdef_intro fh bs))))
  (HeqDoms : Doms = dom_analyze (fdef_intro fh bs))
  (contents3 : ListSet.set atom)
  (inbound3 : incl contents3 (bound_fdef (fdef_intro fh bs)))
  (Heqdefs3 : {|
             DomDS.L.bs_contents := contents3;
             DomDS.L.bs_bound := inbound3 |} = Doms !! l3)
  (Hsucc : In l' (successors_terminator tmn))
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_fdef (fdef_intro fh bs)))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = Doms !! l'),
  incl contents' (l3 :: contents3).
Proof.
  intros. simpl in *.
  unfold dom_analyze in *.
  remember (entry_dom bs) as R.
  destruct R as [R Hp].
  destruct R as [[le start] | ].
  Case "entry is good".
    remember (DomDS.fixpoint (bound_blocks bs) (successors_blocks bs)
                (transfer (bound_blocks bs)) ((le, start) :: nil)) as R1.
    destruct start.
    destruct bs_contents; tinv Hp.
    destruct R1; subst.
    SCase "analysis is done".
      symmetry in HeqR1.
      assert (In l' (successors_blocks bs) !!! l3) as J1.
        clear - HBinF Hsucc Huniq.
        assert (successors_terminator tmn = (successors_blocks bs) !!! l3) as EQ.
          eapply successors_terminator__successors_blocks; eauto.
        rewrite <- EQ. auto.

      apply DomDS.fixpoint_solution with (s:=l')(n:=l3) in HeqR1; eauto.
      unfold transfer, DomDS.L.ge, DomDS.L.top, DomDS.L.bot, DomDS.L.sub,
        DomDS.L.eq, Dominators.add in HeqR1.
      remember (t !! l') as R2.
      destruct R2.
      assert (contents' = bs_contents) as EQ.
        clear - Heqdefs' HeqR2.
        eapply atomset_eq__proof_irr1; eauto.
      subst.
      remember (t !! l3) as R3.
      destruct R3.
      assert (contents3 = bs_contents0) as EQ.
        clear - Heqdefs3 HeqR3.
        eapply atomset_eq__proof_irr1; eauto.
      subst.
      clear - Heqdefs3 Heqdefs' HeqR2 HeqR3 HeqR1.
      destruct HeqR1 as [HeqR1 | [HeqR1 | HeqR1]].
        destruct HeqR1 as [G1 G2].
        intros x G.
        apply G1 in G. inversion G.
        destruct (in_dec eq_atom_dec l3 (bound_blocks bs)).
          eapply incl_set_eq_right; eauto using set_eq_sym.
          apply incl_tran with (m:=bs_contents0).
            eapply incl_set_eq_right; eauto using set_eq_sym.
            apply incl_tl; auto using incl_refl.

        destruct (in_dec eq_atom_dec l3 (bound_blocks bs)); auto.
          apply incl_tl; auto.

    SCase "analysis fails".
      subst.
      unfold Dominators.top in Heqdefs3, Heqdefs'.
      simpl in Heqdefs3, Heqdefs'.
      destruct bs; tinv HeqR.
      destruct b as [l0 p c t]; inv HeqR.
      assert (exists ps, exists cs, exists tmn,
        getEntryBlock (fdef_intro fh ((block_intro l0 p c t) :: bs)) =
          Some (block_intro l0 ps cs tmn)) as H.
        unfold entry_dom in HeqR1.
        exists p. exists c. exists t. auto.
      assert (l' <> l0) as Neq.
        clear - H Hsucc HwfF HBinF.
        destruct H as [ps1 [cs1 [tmn1 H]]].
        eapply getEntryBlock_inv; eauto.
      rewrite AMap.gso in Heqdefs'; auto.
      rewrite AMap.gi in Heqdefs'.
      inv Heqdefs'.
      clear.
      intros x J. inversion J.

  Case "entry is wrong".
    subst. inversion HBinF.
Qed.

Lemma wf_tmn__in_successors: forall s m f l0 cs ps tmn l1
  (HuniqF : uniqFdef f)
  (Hwftmn : wf_insn s m f (block_intro l0 cs ps tmn) (insn_terminator tmn))
  (Hin : In l1 (successors_terminator tmn)),
  exists cs1, exists ps1, exists tmn1,
    blockInFdefB (block_intro l1 cs1 ps1 tmn1) f.
Proof.
  intros.
  inv Hwftmn; simpl in Hin; tinv Hin.
    destruct Hin as [Hin | [Hin | Hin]]; tinv Hin; subst.
      destruct block1.
      apply lookupBlockViaLabelFromFdef_inv in H2; auto.
      destruct H2 as [J1 J2]; subst; eauto.

      destruct block2.
      apply lookupBlockViaLabelFromFdef_inv in H3; auto.
      destruct H3 as [J1 J2]; subst; eauto.

    destruct Hin as [Hin | Hin]; tinv Hin; subst.
      apply lookupBlockViaLabelFromFdef_inv in H0; auto.
      destruct H0 as [J1 J2]; subst; eauto.
Qed.

Require Import Dipaths.

Module DomComplete. Section DomComplete.

Variable S : system.
Variable M : module.
Variable fh : fheader.
Variable bs : blocks.
Definition bound := bound_blocks bs.
Definition predecessors := make_predecessors (successors_blocks bs).
Definition transf := transfer bound.
Definition top := Dominators.top bound.
Definition bot := Dominators.bot bound.
Definition dt := DomDS.dt bound.
Variable entry: l.
Variable entrypoints: list (atom * dt).

Hypothesis wf_entrypoints:
  predecessors!!!entry = nil /\
  match bs with
  | block_intro l0 _ _ _ :: _ => l0 = entry
  | _ => False
  end /\
  exists v, [(entry, v)] = entrypoints /\ Dominators.eq _ v top.

Hypothesis HwfF: wf_fdef S M (fdef_intro fh bs).
Hypothesis HuniqF: uniqFdef (fdef_intro fh bs).

Definition non_sdomination (l1 l2:l) : Prop :=
  let vertexes := vertexes_fdef (fdef_intro fh bs) in
  let arcs := arcs_fdef (fdef_intro fh bs) in
  exists vl, exists al,
    D_walk vertexes arcs (index l2) (index entry) vl al /\
    ~ In (index l1) vl.

Definition non_sdomination_prop (res: AMap.t dt) : Prop :=
  forall l1 l2,
    vertexes_fdef (fdef_intro fh bs) (index l1) ->
    ~ Dominators.member _ l1 res!!l2 ->
    non_sdomination l1 l2.

Lemma start_non_sdomination:
  non_sdomination_prop
    (DomDS.st_in _ (DomDS.start_state _ (successors_blocks bs) entrypoints)).
Proof.
  intros l1 l2 Hin Hnotin.
  destruct (eq_atom_dec l2 entry); try subst l2.
    unfold non_sdomination.
    exists V_nil. exists A_nil.
    split.
      constructor.
      destruct wf_entrypoints as [_ [J _]].
      destruct bs; tinv J.
      destruct b; subst.
      eapply entry_in_vertexes; simpl; eauto.

      intro J. inv J.

    eapply EntryDomsOthers.dom_nonentry_start_state_in in n; eauto.
    contradict Hnotin.
    unfold DomDS.start_state. simpl.
    apply Dominators.member_eq with (x2:=bot); auto.
Qed.

Lemma non_sdomination_refl : forall l1,
  l1 <> entry ->
  reachable (fdef_intro fh bs) l1 ->
  non_sdomination l1 l1.
Proof.
  unfold reachable, non_sdomination.
  intros.
  destruct bs; simpl in *.
    inv H0.
    destruct b; simpl in *.
    destruct H0 as [vl [al H0]].
    apply DWalk_to_dpath in H0.
    destruct H0 as [vl0 [al0 Hp]].
    exists vl0. exists al0.
    destruct wf_entrypoints as [_ [Heq _]]; subst.
    split.
      apply D_path_isa_walk; auto.
      eapply DP_endx_ninV; eauto. congruence.
Qed.

Lemma propagate_succ_non_sdomination: forall st p n out
  (Hinpds: In p predecessors!!!n)
  (Hout: Dominators.ge _ (transf p st.(DomDS.st_in _)!!p) out)
  (Hdom: non_sdomination_prop st.(DomDS.st_in _)),
  non_sdomination_prop (DomDS.propagate_succ _ st out n).(DomDS.st_in _).
Proof.
  unfold non_sdomination_prop. intros.
  destruct (@DomDS.propagate_succ_spec _ st out n) as [J1 J2].
  destruct (eq_atom_dec n l2) as [Heq | Hneq]; subst.
  Case "n=l2".
    destruct (Dominators.member_dec _ l1 (DomDS.st_in _ st) !! l2)
      as [Hin12 | Hnotin12]; auto.
    assert (~ Dominators.member bound l1
      (DomDS.L.lub bound (DomDS.st_in bound st) !! l2 out)) as Hnotlub12.
      intro J. apply H0.
      eapply Dominators.member_eq; eauto.
    clear J1 J2.
    destruct (Dominators.member_dec _ l1 out) as [Hinout | Hnotout]; auto.
    SCase "l1 in out".
      contradict Hnotlub12. apply Dominators.lub_intro; auto.
    SCase "l1 notin out".
      assert (~ Dominators.member _ l1 (transf p (DomDS.st_in bound st) !! p))
        as Hnotintransf.
        intro J. apply Hnotout.
        eapply Dominators.ge_elim in Hout; eauto.
      unfold transf, transfer in Hnotintransf.
      assert (l1 <> p /\ ~ Dominators.member _ l1 (DomDS.st_in bound st)!!p)
        as J.
        split; intro J; subst; apply Hnotintransf.
          apply Dominators.add_member1; auto.
          apply Dominators.add_member2; auto.
      clear Hnotintransf.
      destruct J as [Hneq J].
      apply Hdom in J; auto.
      destruct J as [vl [al [J1 J2]]].
      exists (index p::vl). exists (A_ends (index l2) (index p)::al).
      split.
        apply make_predecessors_correct' in Hinpds.
        change (successors_blocks bs) with (successors (fdef_intro fh bs))
          in Hinpds.
        apply successors__blockInFdefB in Hinpds.
        destruct Hinpds as [ps0 [cs0 [tmn0 [J3 J4]]]].
        constructor; auto.
          eapply wf_fdef__blockInFdefB__wf_block in J3; eauto.
          inv J3. inv HwfF.
          match goal with
          | H12: wf_insn _ _ _ _ _ |- _ =>
            eapply wf_tmn__in_successors in H12; eauto;
            destruct H12 as [cs1 [ps1 [tmn1 H12]]]
          end.
          eapply blockInFdefB_in_vertexes; eauto.

          inv HwfF.
          eapply successor_in_arcs; eauto.

          intro J. simpl in J.
          destruct J as [J | J]; auto.
            inv J. auto.
  Case "n<>l2".
    rewrite J2 in H0; auto.
Qed.

Lemma propagate_succ_list_non_sdomination_aux:
  forall p scs st out,
  (forall s, In s scs -> In p predecessors!!!s) ->
  non_sdomination_prop st.(DomDS.st_in _) ->
  Dominators.ge _ (transf p st.(DomDS.st_in _)!!p) out ->
  non_sdomination_prop (DomDS.propagate_succ_list _ st out scs).(DomDS.st_in _).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs; auto.
      eapply propagate_succ_non_sdomination; eauto.
      apply Dominators.ge_trans with (y:=transf p (DomDS.st_in _ st) !! p);
        auto.
        eapply EntryDomsOthers.transf_mono; eauto.
        destruct (@DomDS.propagate_succ_spec _ st out a) as [J1 J2].
        destruct (eq_atom_dec a p); subst.
          apply Dominators.ge_trans with
            (y:=Dominators.lub _ (DomDS.st_in _ st) !! p out).
            apply Dominators.ge_refl; auto.
            apply Dominators.ge_lub_left.
          rewrite J2; auto.
            apply Dominators.ge_refl'.
Qed.

Lemma propagate_succ_list_non_sdomination:
  forall p scs st,
  (forall s, In s scs -> In p predecessors!!!s) ->
  non_sdomination_prop st.(DomDS.st_in _) ->
  non_sdomination_prop (DomDS.propagate_succ_list _ st
    (transf p st.(DomDS.st_in _)!!p) scs).(DomDS.st_in _).
Proof.
  intros.
  eapply propagate_succ_list_non_sdomination_aux; eauto.
    apply Dominators.ge_refl'.
Qed.

Lemma step_non_sdomination:
  forall st n rem,
  AtomNodeSet.pick st.(DomDS.st_wrk _) = Some(n, rem) ->
  non_sdomination_prop st.(DomDS.st_in _) ->
  non_sdomination_prop (DomDS.propagate_succ_list _
                                 (DomDS.mkstate _ st.(DomDS.st_in _) rem)
                                 (transf n st.(DomDS.st_in _)!!n)
                                 ((successors_blocks bs)!!!n)).(DomDS.st_in _).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_non_sdomination; auto.
    apply make_predecessors_correct.
Qed.

Theorem dom_non_sdomination: forall res,
  DomDS.fixpoint _ (successors_blocks bs) transf entrypoints = Some res ->
  non_sdomination_prop res.
Proof.
  unfold DomDS.fixpoint. intros res PI. pattern res.
  eapply (PrimIter.iterate_prop _ _ (DomDS.step _ _ _)
    (fun st => non_sdomination_prop st.(DomDS.st_in _))); eauto.
    intros st GOOD. unfold DomDS.step.
    caseEq (AtomNodeSet.pick st.(DomDS.st_wrk _)); auto.
    intros [n rem] PICK. apply step_non_sdomination; auto.

    apply start_non_sdomination.
Qed.

End DomComplete. End DomComplete.

Lemma reachable_successors:
  forall S M f l0 cs ps tmn l1,
  uniqFdef f -> wf_fdef S M f ->
  blockInFdefB (block_intro l0 cs ps tmn) f ->
  In l1 (successors_terminator tmn) ->
  reachable f l0 ->
  reachable f l1.
Proof.
  intros S M f l0 cs ps tmn l1 HuniqF HwfF HbInF Hin.
  unfold reachable. intro Hreach.
  remember (getEntryBlock f) as R.
  destruct R; auto.
  destruct b as [le ? ? ?].
  destruct Hreach as [vl [al Hreach]].
  exists (index l0::vl). exists (A_ends (index l1) (index l0)::al).
  apply DW_step; auto.
    eapply wf_fdef__wf_tmn in HbInF; eauto.
    eapply wf_tmn__in_successors in HbInF; eauto.
    destruct HbInF as [cs1 [ps1 [tmn1 HbInF]]].
    eapply blockInFdefB_in_vertexes; eauto.

    eapply successor_in_arcs; eauto.
Qed.

Module UnreachableDoms. Section UnreachableDoms.

Variable S : system.
Variable M : module.
Variable fh : fheader.
Variable bs : blocks.
Definition bound := bound_blocks bs.
Definition predecessors := make_predecessors (successors_blocks bs).
Definition transf := transfer bound.
Definition top := Dominators.top bound.
Definition bot := Dominators.bot bound.
Definition dt := DomDS.dt bound.
Variable entry: l.
Variable entrypoints: list (atom * dt).

Hypothesis wf_entrypoints:
  predecessors!!!entry = nil /\
  match bs with
  | block_intro l0 _ _ _ :: _ => l0 = entry
  | _ => False
  end /\
  exists v, [(entry, v)] = entrypoints /\ Dominators.eq _ v top.

Hypothesis HwfF: wf_fdef S M (fdef_intro fh bs).
Hypothesis HuniqF: uniqFdef (fdef_intro fh bs).

Definition unrechable_doms (res: AMap.t dt) : Prop :=
  forall l0, ~ reachable (fdef_intro fh bs) l0 -> l0 <> entry ->
  Dominators.eq _ res!!l0 bot.

Lemma start_unrechable_doms:
  unrechable_doms
    (DomDS.st_in _ (DomDS.start_state _ (successors_blocks bs) entrypoints)).
Proof.
  intros l0 Hunreach Heq.
  unfold DomDS.start_state. simpl.
  eapply EntryDomsOthers.dom_nonentry_start_state_in in Heq; eauto.
Qed.

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma propagate_succ_unrechable_doms: forall st n out,
  (~ reachable (fdef_intro fh bs) n -> n <> entry -> Dominators.eq _ out bot) ->
  unrechable_doms st.(DomDS.st_in _) ->
  unrechable_doms (DomDS.propagate_succ _ st out n).(DomDS.st_in _).
Proof.
  unfold unrechable_doms.
  intros.
  destruct (@DomDS.propagate_succ_spec _ st out n) as [J1 J2].
  assert (H':=H1).
  apply H0 in H1; auto.
  destruct (eq_atom_dec n l0); subst.
    apply H in H'; auto.
    apply Dominators.eq_trans with
      (y:=DomDS.L.lub bound (DomDS.st_in bound st) !! l0 out); auto.
    apply Dominators.eq_trans with (y:=DomDS.L.lub _ bot bot); auto.
       apply Dominators.lub_compat_eq; auto.
       apply Dominators.eq_sym. apply Dominators.lub_refl.

    rewrite J2; auto.
Qed.

Lemma propagate_succ_list_unrechable_doms:
  forall scs st out,
  (forall s, In s scs ->
             ~ reachable (fdef_intro fh bs) s -> s <> entry ->
             Dominators.eq _ out bot) ->
  unrechable_doms st.(DomDS.st_in _) ->
  unrechable_doms (DomDS.propagate_succ_list _ st out scs).(DomDS.st_in _).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs.
      intros. apply H with (s:=s); auto.
      apply propagate_succ_unrechable_doms; auto.
        intros J1 J2. eapply H; eauto.
Qed.

Lemma step_unrechable_doms:
  forall st n rem,
  AtomNodeSet.pick st.(DomDS.st_wrk _) = Some(n, rem) ->
  unrechable_doms st.(DomDS.st_in _) ->
  unrechable_doms (DomDS.propagate_succ_list _
                                  (DomDS.mkstate _ st.(DomDS.st_in _) rem)
                                  (transf n st.(DomDS.st_in _)!!n)
                                  ((successors_blocks bs)!!!n)).(DomDS.st_in _).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_unrechable_doms; auto.
  intros s Hin Hunreach.
    destruct (reachable_dec (fdef_intro fh bs) n).
      assert(exists ps0, exists cs0, exists tmn0,
        blockInFdefB (block_intro n ps0 cs0 tmn0) (fdef_intro fh bs) /\
        In s (successors_terminator tmn0)) as J.
        apply successors__blockInFdefB; auto.
      destruct J as [ps0 [cs0 [tmn0 [J1 J2]]]].
      eapply reachable_successors with (l1:=s) in H; eauto.
      congruence.

      apply GOOD in H. simpl in H.
      unfold transf, transfer.
      intros.
      destruct (eq_atom_dec n entry); subst.
        assert (exists ps0, exists cs0, exists tmn0,
          blockInFdefB (block_intro entry ps0 cs0 tmn0) (fdef_intro fh bs) /\
          In s (successors_terminator tmn0)) as J.
          apply successors__blockInFdefB; auto.
        destruct J as [ps0 [cs0 [tmn0 [J1 J2]]]].
        contradict Hunreach.
        unfold reachable. inv HwfF.
        match goal with | H5: getEntryBlock _ = _ |- _ => rewrite H5 end.
        destruct block5 as [l0 ? ? ?].
        destruct wf_entrypoints as [_ [J _]].
        destruct bs as [|b ?]; tinv J.
        destruct b as [l5 ? ? ?]. subst entry.
        unfold successors_list in Hin. simpl in Hin. rewrite ATree.gss in Hin.
        clear J.
        exists (index l0::nil). exists (A_ends (index s) (index l0)::nil).
        constructor.
          constructor.
            eapply entry_in_vertexes; simpl; eauto.
          match goal with
          | H14: wf_blocks _ _ _ _ |- _ => inv H14
          end.
          match goal with
          | H11: wf_block _ _ _ _ |- _ => inv H11
          end.
          eapply wf_tmn__in_successors in Hin; eauto.
          destruct Hin as [cs1 [ps1 [tmn1 Hin]]].
          eapply blockInFdefB_in_vertexes; eauto.

          match goal with | H5: getEntryBlock _ = _ |- _ => inv H5 end.
          eapply successor_in_arcs; eauto.
      apply Dominators.eq_trans with (y:=Dominators.add _ (Dominators.bot _) n).
        apply Dominators.add_eq; auto.
        apply Dominators.add_bot.
Qed.

Theorem dom_unrechable_doms: forall res,
  DomDS.fixpoint _ (successors_blocks bs) transf entrypoints = Some res ->
  unrechable_doms res.
Proof.
  unfold DomDS.fixpoint. intros res PI. pattern res.
  eapply (PrimIter.iterate_prop _ _ (DomDS.step _ _ _)
    (fun st => unrechable_doms st.(DomDS.st_in _))); eauto.
  intros st GOOD. unfold DomDS.step.
  caseEq (AtomNodeSet.pick st.(DomDS.st_wrk _)); auto.
  intros [n rem] PICK.
  apply step_unrechable_doms; auto.
    apply start_unrechable_doms.
Qed.

End UnreachableDoms.

End UnreachableDoms.

Lemma dom_unreachable: forall
  S M (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef S M f) (HuniqF: uniqFdef f)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hunreach: ~ reachable f l3)
  (Hnempty: DomDS.L.bs_contents _ ((dom_analyze f) !! l3) <> nil),
  DomDS.L.eq _ ((dom_analyze f) !! l3) (DomDS.L.bot _).
Proof.
  intros.
  assert (HwfF':=HwfF). inv HwfF'.
  destruct block5 as [l0 p c t].
  rename blocks5 into bs.
  match goal with | H1: getEntryBlock _ = _ |- _ => assert (J:=H1) end.
  destruct bs; inv J.
  match goal with | H1: getEntryBlock _ = _ |- _ =>
    apply dom_entrypoint in H1 end.
  destruct (id_dec l3 l0); subst.
    match goal with
    | H1: Dominators.bs_contents _ _ = _ |- _ =>
      rewrite H1 in Hnempty; congruence
    end.

    clear H.
    unfold dom_analyze in *.
    remember (entry_dom (block_intro l0 p c t :: bs)) as R.
    destruct R as [R Hp].
    destruct R as [[le start] | ]; tinv Hp.
    destruct start; tinv Hp.
    destruct bs_contents; tinv Hp. inv HeqR.
    remember (DomDS.fixpoint (bound_blocks (block_intro l0 p c t :: bs))
                  (successors_blocks (block_intro l0 p c t :: bs))
                  (transfer (bound_blocks (block_intro l0 p c t :: bs)))
                  ((l0,
                   {|
                   DomDS.L.bs_contents := nil;
                   DomDS.L.bs_bound := bs_bound |}) :: nil)) as R.
    destruct R.
      symmetry in HeqR.
      eapply UnreachableDoms.dom_unrechable_doms with (entry:=l0) in HeqR;
        eauto.
        split.
           remember ((DomComplete.predecessors (block_intro l0 p c t :: bs))
             !!! l0) as R.
           destruct R; auto.
           assert (In a (DomComplete.predecessors (block_intro l0 p c t :: bs))
             !!! l0) as Hin. rewrite <- HeqR0. simpl; auto.
           unfold DomComplete.predecessors in Hin.
           apply make_predecessors_correct' in Hin.
           apply successors_blocks__blockInFdefB with (fh:=fheader5) in Hin.
           destruct Hin as [ps0 [cs0 [tmn0 [J1 J2]]]].
           eapply getEntryBlock_inv with (l3:=a)(a:=l0) in J2; simpl; eauto.
           congruence.

        split; auto.
               exists {| DomDS.L.bs_contents := nil;
                         DomDS.L.bs_bound := bs_bound |}.
               split; auto. simpl. apply set_eq_refl.

      simpl in Hnempty.
      destruct (id_dec l0 l3); subst.
        rewrite AMap.gss in *. simpl in *. congruence.
        rewrite AMap.gso; auto. rewrite AMap.gso in Hnempty; auto.
        rewrite AMap.gi in *; auto. simpl in *. unfold ListSet.empty_set in *.
        congruence.
Qed.

Definition domination (f:fdef) (l1 l2:l) : Prop :=
match getEntryBlock f with
| Some (block_intro entry _ _ _) =>
  let vertexes := vertexes_fdef f in
  let arcs := arcs_fdef f in
  forall vl al,
    D_walk vertexes arcs (index l2) (index entry) vl al ->
    (In (index l1) vl \/ l1 = l2)
| _ => False
end.

Definition strict_domination (f:fdef) (l1 l2:l) : Prop :=
domination f l1 l2 /\ l1 <> l2.

Lemma sdom_is_complete: forall
  S M (f : fdef) (l3 : l) (l' : l) ps cs tmn ps' cs' tmn'
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f)
  (HBinF' : blockInFdefB (block_intro l' ps' cs' tmn') f = true)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hsdom: strict_domination f l' l3)
  (Hnempty: DomDS.L.bs_contents _ ((dom_analyze f) !! l3) <> nil),
  In l' (DomDS.L.bs_contents _ ((dom_analyze f) !! l3)).
Proof.
  intros. unfold dom_analyze in *. destruct f as [fh bs].
  remember (entry_dom bs) as R.
  destruct R as [R Hp].
  destruct R as [[le start] | ].
    destruct start; tinv Hp.
    destruct bs_contents; tinv Hp.
    destruct bs as [|b ?]; tinv HeqR.
    destruct b as [l0 p c t]; inv HeqR.
    remember (DomDS.fixpoint (bound_blocks (block_intro l0 p c t :: bs))
                  (successors_blocks (block_intro l0 p c t :: bs))
                  (transfer (bound_blocks (block_intro l0 p c t :: bs)))
                  ((l0,
                   {|
                   DomDS.L.bs_contents := nil;
                   DomDS.L.bs_bound := bs_bound |}) :: nil)) as R.
    destruct R.
      symmetry in HeqR.
      eapply DomComplete.dom_non_sdomination with (entry:=l0) in HeqR; eauto.
        Focus.
        unfold DomComplete.non_sdomination_prop in HeqR.
        destruct (in_dec eq_atom_dec l'
          (DomDS.L.bs_contents
            (bound_fdef (fdef_intro fh (block_intro l0 p c t :: bs)))
            t0 !! l3)); auto.
        assert (vertexes_fdef (fdef_intro fh (block_intro l0 p c t :: bs))
           (index l')) as J.
          apply blockInFdefB_in_vertexes in HBinF'; auto.
        apply HeqR with (l2:=l3) in J.
          unfold DomComplete.non_sdomination in J.
          destruct J as [vl [al [J1 J2]]].
          unfold strict_domination in Hsdom.
          destruct Hsdom as [Hdom Hneq].
          unfold domination in Hdom.
          simpl in Hdom.
          apply Hdom in J1.
          destruct J1; subst; congruence.

          unfold Dominators.member.
          unfold DomComplete.dt. unfold DomComplete.bound.
          destruct (t0!!l3). simpl in *; auto.
        Unfocus.

        assert (HwfF':=HwfF). inv HwfF'.
        split.
           remember ((DomComplete.predecessors (block_intro l0 p c t :: bs))
             !!! l0) as R.
           destruct R; auto.
           assert (In a (DomComplete.predecessors (block_intro l0 p c t :: bs))
             !!! l0) as Hin. rewrite <- HeqR0. simpl; auto.
           unfold DomComplete.predecessors in Hin.
           apply make_predecessors_correct' in Hin.
           apply successors_blocks__blockInFdefB with (fh:=fh) in Hin.
           destruct Hin as [ps0 [cs0 [tmn0 [J1 J2]]]].
           eapply getEntryBlock_inv with (l3:=a)(a:=l0) in J2; simpl; eauto.
           congruence.

        split; auto.
               exists {| DomDS.L.bs_contents := nil; DomDS.L.bs_bound := bs_bound |}.
               split; auto. simpl. apply set_eq_refl.

      simpl in Hnempty.
      destruct (id_dec l0 l3); subst.
        rewrite AMap.gss in *. simpl in *. auto.
        rewrite AMap.gso in *; auto. rewrite AMap.gi in *; auto.
        simpl in *. auto.

    subst. inv HBinF.
Qed.

Lemma dom_is_sound : forall
  S M (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin :
    In l' (l3::(DomDS.L.bs_contents _ ((dom_analyze f) !! l3)))),
  domination f l' l3.
Proof.
  unfold domination, strict_domination.
  intros. destruct f as [fh bs].
  apply uniqF__uniqBlocks in HuniqF.
  assert (HwfF':=HwfF).
  apply wf_fdef__non_entry in HwfF'.
  remember (getEntryBlock (fdef_intro fh bs)) as R.
  destruct R; auto. clear HwfF'.
  destruct b as [l5 ps5 cs5 t5].
  intros vl al Hreach.
  generalize dependent ps.
  generalize dependent cs.
  generalize dependent tmn.
  remember (vertexes_fdef (fdef_intro fh bs)) as Vs.
  remember (arcs_fdef (fdef_intro fh bs)) as As.
  remember (index l3) as v0.
  remember (index l5) as v1.
  generalize dependent bs.
  generalize dependent l3.
  generalize dependent l5.
  induction Hreach; intros; subst.
    inv Heqv0. symmetry in HeqR.
    apply dom_entrypoint in HeqR.
    rewrite HeqR in Hin.
    simpl in Hin. destruct Hin as [Hin | Hin]; tinv Hin; auto.

    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0,
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) (fdef_intro fh bs) /\
      In l3 (successors_terminator tmn0)) as J.
      eapply successors__blockInFdefB; eauto.
    destruct J as [ps0 [cs0 [tmn0 [HBinF'' Hinsucc]]]].
    remember ((dom_analyze (fdef_intro fh bs)) !! a0) as R.
    destruct R as [bs_contents bs_bounds].
    destruct (id_dec l' l3); subst; auto.
    left.
    assert (In l'
      (a0 :: DomDS.L.bs_contents (bound_fdef (fdef_intro fh bs))
                (dom_analyze (fdef_intro fh bs)) !! a0)) as J.
      remember ((dom_analyze (fdef_intro fh bs)) !! l3) as R.
      destruct R.
      assert (incl bs_contents0 (a0 :: bs_contents)) as Hinc.
        eapply dom_successors; eauto.
      rewrite <- HeqR0. simpl.
      simpl in Hin. destruct Hin; try congruence.
      apply Hinc; auto.
    eapply IHHreach in J; eauto.
    simpl.
    destruct J as [J | J]; subst; eauto.
Qed.

Lemma sdom_is_sound : forall
  S M (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f) (Hreach : reachable f l3)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin :
    In l' (DomDS.L.bs_contents _ ((dom_analyze f) !! l3))),
  strict_domination f l' l3.
Proof.
  intros.
  eapply dom_is_sound with (l':=l') in HBinF; simpl; eauto.
  split; auto.
  destruct (id_dec l' l3); subst; auto.
  unfold reachable, domination in *.
  remember (getEntryBlock f) as R.
  destruct R; try congruence.
  destruct b as [l0 ? ? ?].
  destruct Hreach as [vl [al Hreach]].
  apply DWalk_to_dpath in Hreach.
  destruct Hreach as [vl0 [al0 Hp]].
  destruct (id_dec l3 l0); subst.
    symmetry in HeqR.
    apply dom_entrypoint in HeqR.
    rewrite HeqR in Hin. inv Hin.

    inv Hp; try congruence.
    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0,
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) f /\
      In l3 (successors_terminator tmn0)) as J.
      eapply successors__blockInFdefB; eauto.
    destruct J as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
    remember ((dom_analyze f) !! a0) as R.
    destruct R as [bs_contents bs_bounds].
    assert (In l3
      (a0 :: DomDS.L.bs_contents (bound_fdef f)
                (dom_analyze f) !! a0)) as J.
      remember ((dom_analyze f) !! l3) as R.
      destruct R.
      assert (incl bs_contents0 (a0 :: bs_contents)) as Hinc.
        destruct f. apply uniqF__uniqBlocks in HuniqF.
        eapply dom_successors; eauto.
      rewrite <- HeqR0. simpl.
      simpl in Hin.
      apply Hinc; auto.
    eapply dom_is_sound in J; eauto.
    unfold domination in J.
    rewrite <- HeqR in J.
    assert (Hw:=H).
    apply D_path_isa_walk in Hw.
    apply J in Hw.
    destruct Hw as [Hw | Hw]; subst; try congruence.
    apply H4 in Hw. inv Hw; try congruence.
Qed.

Lemma sdom_isnt_refl : forall
  S M (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f) (Hreach : reachable f l3)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : In l' (DomDS.L.bs_contents _ ((dom_analyze f) !! l3))),
  l' <> l3.
Proof.
  intros.
  eapply sdom_is_sound in Hin; eauto.
  destruct Hin; auto.
Qed.

Lemma blockStrictDominates_isnt_refl : forall S M F1 block'
  (Hin : blockInFdefB block' F1) (HwfF : wf_fdef S M F1)
  (HuniqF : uniqFdef F1) (Hreach : isReachableFromEntry F1 block'),
  ~ blockStrictDominates F1 block' block'.
Proof.
  intros. destruct block' as [l0 ? ? ?].
  unfold blockStrictDominates. intro J.
  remember ((dom_analyze F1) !! l0) as R.
  destruct R.
  simpl in Hreach.
  eapply sdom_isnt_refl in Hreach; eauto.
  rewrite <- HeqR. simpl. auto.
Qed.

Lemma dom_tran: forall (f:fdef) (l1 l2 l3:l),
  domination f l1 l2 -> domination f l2 l3 -> domination f l1 l3.
Proof.
  unfold domination.
  intros.
  destruct (getEntryBlock f); tinv H.
  destruct b.
  intros vl al Hw.
  destruct (id_dec l1 l3); auto.
  left.
  assert (Hw':=Hw).
  apply H0 in Hw'.
  destruct Hw' as [Hw' | Hw']; subst.
    apply DW_extract with (x:=index l2) in Hw; simpl; auto.
    destruct Hw as [al' Hw].
    assert (Hw'':=Hw).
    apply H in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; auto.
    destruct (id_dec l1 l2); subst; auto.
    apply V_extract_spec in Hw''; try congruence.
    simpl in Hw''. destruct Hw'' as [Hw'' | Hw'']; congruence.

    assert (Hw'':=Hw).
    apply H in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; congruence.
Qed.

Lemma dom_acyclic: forall S M (f:fdef) (l1 l2:l)
  (HwfF:wf_fdef S M f) (HuniqF : uniqFdef f),
  reachable f l2 ->
  strict_domination f l1 l2 -> ~ domination f l2 l1.
Proof.
  unfold reachable, strict_domination, domination.
  intros. assert (HwfF':=HwfF).
  apply wf_fdef__non_entry in HwfF'.
  remember (getEntryBlock f) as R.
  destruct R; auto. clear HwfF'.
  destruct b as [l0 ? ? ?].
  destruct H as [vl [al Hw]].
  apply DWalk_to_dpath in Hw.
  destruct Hw as [vl0 [al0 Hp]].
  assert (Hw:=Hp).
  apply D_path_isa_walk in Hw.
  destruct H0 as [J1 J2].
  assert (Hw':=Hw).
  apply J1 in Hw'.
  destruct Hw' as [Hw' | Hw']; subst; try congruence.
  intros J.
  apply DW_extract with (x:=index l1) in Hw; simpl; auto.
  destruct Hw as [al' Hw].
  assert (Hw'':=Hw).
  apply J in Hw''.
  destruct Hw'' as [Hw'' | Hw'']; subst; auto.
  apply V_extract_spec' in Hw''; try congruence.
  inv Hp.
    inv Hw'.

    simpl in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; try congruence.
    apply H4 in Hw''. inv Hw''.
    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0,
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) f /\
      In l0 (successors_terminator tmn0)) as J'.
      eapply successors__blockInFdefB; eauto.
    destruct J' as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
    symmetry in HeqR. destruct f.
    eapply getEntryBlock_inv in HeqR; eauto.
Qed.

Lemma sdom_reachable : forall f l1 l2,
  reachable f l2 -> strict_domination f l1 l2 -> reachable f l1.
Proof.
  unfold reachable, strict_domination, domination.
  intros.
  destruct H0 as [J1 J2].
  destruct (getEntryBlock f); try congruence.
  destruct b.
  destruct H as [vl [al H]].
  assert (H':=H).
  apply J1 in H'.
  assert (In (index l1) vl) as Hin.
    destruct H' as [H' | H']; subst; try congruence.
  apply DW_extract with (x:=index l1) in H; simpl; auto.
  destruct H as [al' H].
  exists (V_extract (index l1) (index l2 :: vl)). exists al'.
  auto.
Qed.

Lemma dom_reachable : forall f l1 l2,
  reachable f l2 -> domination f l1 l2 -> reachable f l1.
Proof.
  intros.
  destruct (id_dec l1 l2); subst; auto.
  eapply sdom_reachable; eauto. split; auto.
Qed.

Lemma sdom_dec : forall f l1 l2,
  strict_domination f l1 l2 \/ ~ strict_domination f l1 l2.
Proof. intros. tauto. Qed. (* classic logic *)

Lemma everything_dominates_unreachable_blocks :
  forall f l1 l2 (Hreach: ~ reachable f l2)
  (Hentry: getEntryBlock f <> None),
  domination f l1 l2.
Proof.
  unfold reachable, domination.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b.
  intros.
  contradict Hreach. eauto.
Qed.

Lemma sdom_tran1: forall S M (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef S M f)
  (HuniqF: uniqFdef f) (Hreach: reachable f l2),
  strict_domination f l1 l2 -> domination f l2 l3 -> strict_domination f l1 l3.
Proof.
  intros.
  destruct (id_dec l1 l3); subst.
    eapply dom_acyclic in H; eauto.
    contradict H; auto.

    destruct H.
    split; eauto using dom_tran.
Qed.

Lemma sdom_tran2: forall S M (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef S M f)
  (HuniqF: uniqFdef f) (Hreach: reachable f l3),
  domination f l1 l2 -> strict_domination f l2 l3 -> strict_domination f l1 l3.
Proof.
  intros.
  destruct (id_dec l1 l3); subst.
    eapply dom_acyclic in H0; eauto.
    contradict H0; auto.

    destruct H0.
    split; eauto using dom_tran.
Qed.

Lemma sdom_tran: forall S M (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef S M f)
  (HuniqF: uniqFdef f) (Hreach: reachable f l2),
  strict_domination f l1 l2 -> strict_domination f l2 l3 ->
  strict_domination f l1 l3.
Proof.
  intros. destruct H0. eapply sdom_tran1; eauto.
Qed.

Lemma tauto_helper : forall A B:Prop,
  A -> ~ (B /\ A) -> ~ B.
Proof. tauto. Qed.

Import Classical_Pred_Type.

Lemma sdom_ordered : forall f l1 l2 l3
  (Hneq: l1 <> l2) (Hreach: reachable f l3)
  (Hsdom: strict_domination f l1 l3)
  (Hsdom': strict_domination f l2 l3),
  strict_domination f l1 l2 \/ strict_domination f l2 l1.
Proof.
  intros.
  destruct (sdom_dec f l1 l2); auto.
  destruct (sdom_dec f l2 l1); auto.
  contradict Hsdom'. intro Hsdom'.
  unfold strict_domination in *.
  destruct Hsdom as [Hdom Hneq1].
  destruct Hsdom' as [Hdom' Hneq2].
  unfold domination, reachable in *.
  destruct (getEntryBlock f); auto.
  destruct b as [l0 ? ? ?].
  destruct Hreach as [vl [al Hreach]].
  assert (Hw:=Hreach).
  apply Hdom in Hw.
  destruct Hw as [Hin | Heq]; try congruence.
  assert (Hw:=Hreach).
  apply Hdom' in Hw.
  destruct Hw as [Hin' | Heq]; try congruence.

  (* on Hw, we need to figuire the closest one to l3 in l1 and l2,
     suppose l1 is, then we split hw at l1, so l2 cannot be in the part
     from l3 to l1.
  *)
  assert (Hw:=Hreach).
  assert (vl <> V_nil) as Hnqnil.
    destruct vl; auto.
      intro J. inv J.
  apply DW_cut with (x:=index l1) (w:=index l2) in Hw; try congruence;
    simpl; auto.
  destruct Hw as [al1 [al2 [vl1 [vl2
    [[J1 [J2 [J3 [J4 J5]]]]|[J1 [J2 [J3 [J4 J5]]]]]]]]]; subst.
  Case "1".
  assert (exists vl:V_list, exists al:A_list,
    D_walk (vertexes_fdef f) (arcs_fdef f) (index l1) (index l0) vl al /\
    ~ In (index l2) vl) as J.
    clear - Hneq H0.
    apply tauto_helper in H0; auto.
    apply not_all_ex_not in H0. (* can we remove the classic lemma? *)
    destruct H0 as [vl H0].
    apply not_all_ex_not in H0.
    destruct H0 as [al H0].
    exists vl. exists al.
    tauto.
  destruct J as [vl1' [al1' [J1' J2']]].

  assert ((D_walk (vertexes_fdef f) (arcs_fdef f) (index l3) (index l0)
    (vl1++vl1') (al1++al1') * ~ In (index l2) (vl1++vl1'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hdom' in J3.
  destruct J3 as [Hin'' | Heq]; try congruence.

  Case "2".
  assert (exists vl:V_list, exists al:A_list,
    D_walk (vertexes_fdef f) (arcs_fdef f) (index l2) (index l0) vl al /\
    ~ In (index l1) vl) as J.
    clear - Hneq H.
    apply tauto_helper in H; auto.
    apply not_all_ex_not in H.
    destruct H as [vl H].
    apply not_all_ex_not in H.
    destruct H as [al H].
    exists vl. exists al.
    tauto.
  destruct J as [vl2' [al2' [J1' J2']]].

  assert ((D_walk (vertexes_fdef f) (arcs_fdef f) (index l3) (index l0)
    (vl1++vl2') (al1++al2') * ~ In (index l1) (vl1++vl2'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hdom in J3.
  destruct J3 as [Hin'' | Heq]; try congruence.
Qed.

Lemma adom_acyclic: forall l1 l2 ps1 cs1 tmn1 ps2 cs2 tmn2 S M F,
  wf_fdef S M F -> uniqFdef F ->
  reachable F l2 ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F = true ->
  blockInFdefB (block_intro l2 ps2 cs2 tmn2) F = true ->
  In l1 (DomDS.L.bs_contents (bound_fdef F) ((dom_analyze F) !! l2)) ->
  In l2 (DomDS.L.bs_contents (bound_fdef F) ((dom_analyze F) !! l1)) ->
  l1 <> l2 ->
  False.
Proof.
  intros.
  assert (strict_domination F l1 l2) as Hdom12.
    eapply sdom_is_sound; eauto.
  assert (strict_domination F l2 l1) as Hdom21.
    eapply sdom_is_sound; eauto.
      apply sdom_reachable in Hdom12; auto.
  eapply dom_acyclic in Hdom12; eauto.
  apply Hdom12. destruct Hdom21; auto.
Qed.

Lemma blockStrictDominates_trans : forall S M f b1 b2 b3
  (HwfF: wf_fdef S M f) (HuniqF: uniqFdef f)
  (HBinF1: blockInFdefB b1 f)
  (HBinF2: blockInFdefB b2 f)
  (HBinF3: blockInFdefB b3 f)
  (H1 : blockStrictDominates f b1 b2)
  (H2 : blockStrictDominates f b2 b3),
  blockStrictDominates f b1 b3.
Proof.
  unfold blockStrictDominates.
  intros. destruct b1 as [l0 ? ? ?], b2 as [l1 ? ? ?], b3 as [l2 ? ? ?].
  remember (Maps.AMap.get l1 (dom_analyze f)) as R1.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R2.
  destruct R1. destruct R2.
  destruct (reachable_dec f l2).
    assert (strict_domination f l1 l2) as Hsdom23.
      eapply sdom_is_sound; eauto.
        rewrite <- HeqR2. simpl. auto.
    assert (reachable f l1) as Hreach1.
      apply sdom_reachable in Hsdom23; auto.
    assert (strict_domination f l0 l1) as Hsdom12.
      eapply sdom_is_sound; eauto.
        rewrite <- HeqR1. simpl. auto.
    assert (strict_domination f l0 l2) as Hsdom13.
      eapply sdom_tran with (l2:=l1); eauto.
    eapply sdom_is_complete in Hsdom13; eauto.
      rewrite <- HeqR2 in Hsdom13. simpl in *. auto.

      rewrite <- HeqR2. simpl.
      destruct bs_contents0; auto.
        intro J. inv J.

    eapply dom_unreachable in H; eauto.
      rewrite <- HeqR2 in H. simpl in H.
      destruct H. apply H0.
      apply blockInFdefB_in_vertexes in HBinF1.
      unfold vertexes_fdef in HBinF1. auto.

      rewrite <- HeqR2. simpl. intro J. subst. inv H2.
Qed.

Lemma blockDominates_trans : forall S M f b1 b2 b3
  (HwfF: wf_fdef S M f) (HuniqF: uniqFdef f)
  (HBinF1: blockInFdefB b1 f)
  (HBinF2: blockInFdefB b2 f)
  (HBinF3: blockInFdefB b3 f)
  (H1 : blockDominates f b1 b2)
  (H2 : blockDominates f b2 b3),
  blockDominates f b1 b3.
Proof.
  unfold blockDominates.
  intros. destruct b1 as [l0 ? ? ?], b2 as [l1 ? ? ?], b3 as [l2 ? ? ?].
  remember (Maps.AMap.get l1 (dom_analyze f)) as R1.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R2.
  destruct R1. destruct R2.
  destruct (l_dec l0 l2); auto.
  destruct H2 as [H2 | H2]; subst; auto.
  Case "l1 in sdom(l2)".
    left.
    assert (domination f l1 l2) as Hdom23.
      eapply dom_is_sound; eauto.
        rewrite <- HeqR2. simpl. auto.
    destruct H1 as [H1 | H1]; subst.
    SCase "l0 in sdom(l1)".
      assert (domination f l0 l1) as Hdom12.
        eapply dom_is_sound; eauto.
          rewrite <- HeqR1. simpl. auto.
      assert (strict_domination f l0 l2) as Hsdom13.
        split; auto.
          eapply dom_tran; eauto.
      eapply sdom_is_complete in Hsdom13; eauto.
        rewrite <- HeqR2 in Hsdom13. simpl in *. auto.

        rewrite <- HeqR2. simpl.
        destruct bs_contents0; auto.
          intro J. inv J.

    SCase "l0=l1".
      assert (strict_domination f l1 l2) as Hsdom12.
        split; auto.
      eapply sdom_is_complete in Hsdom12; eauto.
        rewrite <- HeqR2. simpl.
        destruct bs_contents0; auto.
          intro J. inv J.

  Case "l1=l2".
    rewrite <- HeqR2 in HeqR1. inv HeqR1; auto.
Qed.

Module AnotherDominators.

Definition domination (f:fdef) (l1 l2:l) : Prop :=
match getEntryBlock f with
| Some (block_intro entry _ _ _) =>
  let vertexes := vertexes_fdef f in
  let arcs := arcs_fdef f in
  forall vl al,
    D_walk vertexes arcs (index l2) (index entry) vl al ->
    (In (index l1) vl \/ l1 = l2)
| _ => False
end.

Definition strict_domination (f:fdef) (l1 l2:l) : Prop :=
match getEntryBlock f with
| Some (block_intro entry _ _ _) =>
  let vertexes := vertexes_fdef f in
  let arcs := arcs_fdef f in
  forall vl al,
    D_walk vertexes arcs (index l2) (index entry) vl al ->
    (In (index l1) vl /\ l1 <> l2)
| _ => False
end.

Lemma sdom_is_complete: forall
  S M (f : fdef) (l3 : l) (l' : l) ps cs tmn ps' cs' tmn'
  (HwfF : wf_fdef S M f) (HuniqF: uniqFdef f)
  (HBinF' : blockInFdefB (block_intro l' ps' cs' tmn') f = true)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hsdom: strict_domination f l' l3)
  (Hnempty: DomDS.L.bs_contents _ ((dom_analyze f) !! l3) <> nil),
  In l' (DomDS.L.bs_contents _ ((dom_analyze f) !! l3)).
Proof.
  intros. unfold dom_analyze in *. destruct f as [fh bs].
  remember (entry_dom bs) as R.
  destruct R as [R Hp].
  destruct R as [[le start] | ].
    destruct start; tinv Hp.
    destruct bs_contents; tinv Hp.
    destruct bs as [|b ?]; tinv HeqR.
    destruct b as [l0 p c t]; inv HeqR.
    remember (DomDS.fixpoint (bound_blocks (block_intro l0 p c t :: bs))
                  (successors_blocks (block_intro l0 p c t :: bs))
                  (transfer (bound_blocks (block_intro l0 p c t :: bs)))
                  ((l0,
                   {|
                   DomDS.L.bs_contents := nil;
                   DomDS.L.bs_bound := bs_bound |}) :: nil)) as R.
    destruct R.
      symmetry in HeqR.
      eapply DomComplete.dom_non_sdomination with (entry:=l0) in HeqR; eauto.
        Focus.
        unfold DomComplete.non_sdomination_prop in HeqR.
        destruct (in_dec eq_atom_dec l'
          (DomDS.L.bs_contents
            (bound_fdef (fdef_intro fh (block_intro l0 p c t :: bs)))
            t0 !! l3)); auto.
        assert (vertexes_fdef (fdef_intro fh (block_intro l0 p c t :: bs))
           (index l')) as J.
          apply blockInFdefB_in_vertexes in HBinF'; auto.
        apply HeqR with (l2:=l3) in J.
          unfold DomComplete.non_sdomination in J.
          destruct J as [vl [al [J1 J2]]].
          unfold strict_domination in Hsdom.
          simpl in Hsdom.
          apply Hsdom in J1.
          destruct J1; subst; congruence.

          unfold Dominators.member.
          unfold DomComplete.dt. unfold DomComplete.bound.
          destruct (t0!!l3). simpl in *; auto.
        Unfocus.

        assert (HwfF':=HwfF). inv HwfF'.
        split.
           remember ((DomComplete.predecessors (block_intro l0 p c t :: bs))
             !!! l0) as R.
           destruct R; auto.
           assert (In a (DomComplete.predecessors (block_intro l0 p c t :: bs))
             !!! l0) as Hin. rewrite <- HeqR0. simpl; auto.
           unfold DomComplete.predecessors in Hin.
           apply make_predecessors_correct' in Hin.
           apply successors_blocks__blockInFdefB with (fh:=fh) in Hin.
           destruct Hin as [ps0 [cs0 [tmn0 [J1 J2]]]].
           eapply getEntryBlock_inv with (l3:=a)(a:=l0) in J2; simpl; eauto.
           congruence.

        split; auto.
               exists {| DomDS.L.bs_contents := nil;
                         DomDS.L.bs_bound := bs_bound |}.
               split; auto. simpl. apply set_eq_refl.

      simpl in Hnempty.
      destruct (id_dec l0 l3); subst.
        rewrite AMap.gss in *. simpl in *. auto.
        rewrite AMap.gso in *; auto. rewrite AMap.gi in *; auto.
        simpl in *. auto.

    subst. inv HBinF.
Qed.

Lemma dom_is_sound : forall
  S M (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin :
    In l' (l3::(DomDS.L.bs_contents _ ((dom_analyze f) !! l3)))),
  domination f l' l3.
Proof.
  unfold domination, strict_domination.
  intros. destruct f as [fh bs].
  apply uniqF__uniqBlocks in HuniqF.
  assert (HwfF':=HwfF).
  apply wf_fdef__non_entry in HwfF'.
  remember (getEntryBlock (fdef_intro fh bs)) as R.
  destruct R; auto. clear HwfF'.
  destruct b as [l5 ps5 cs5 t5].
  intros vl al Hreach.
  generalize dependent ps.
  generalize dependent cs.
  generalize dependent tmn.
  remember (vertexes_fdef (fdef_intro fh bs)) as Vs.
  remember (arcs_fdef (fdef_intro fh bs)) as As.
  remember (index l3) as v0.
  remember (index l5) as v1.
  generalize dependent bs.
  generalize dependent l3.
  generalize dependent l5.
  induction Hreach; intros; subst.
    inv Heqv0. symmetry in HeqR.
    apply dom_entrypoint in HeqR.
    rewrite HeqR in Hin.
    simpl in Hin. destruct Hin as [Hin | Hin]; tinv Hin; auto.

    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0,
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) (fdef_intro fh bs) /\
      In l3 (successors_terminator tmn0)) as J.
      eapply successors__blockInFdefB; eauto.
    destruct J as [ps0 [cs0 [tmn0 [HBinF'' Hinsucc]]]].
    remember ((dom_analyze (fdef_intro fh bs)) !! a0) as R.
    destruct R as [bs_contents bs_bounds].
    destruct (id_dec l' l3); subst; auto.
    left.
    assert (In l'
      (a0 :: DomDS.L.bs_contents (bound_fdef (fdef_intro fh bs))
                (dom_analyze (fdef_intro fh bs)) !! a0)) as J.
      remember ((dom_analyze (fdef_intro fh bs)) !! l3) as R.
      destruct R.
      assert (incl bs_contents0 (a0 :: bs_contents)) as Hinc.
        eapply dom_successors; eauto.
      rewrite <- HeqR0. simpl.
      simpl in Hin. destruct Hin; try congruence.
      apply Hinc; auto.
    eapply IHHreach in J; eauto.
    simpl.
    destruct J as [J | J]; subst; eauto.
Qed.

Lemma sdom_is_sound : forall
  S M (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin :
    In l' (DomDS.L.bs_contents _ ((dom_analyze f) !! l3))),
  strict_domination f l' l3.
Proof.
  intros.
  eapply dom_is_sound with (l':=l') in HBinF; simpl; eauto.
  unfold strict_domination, domination in *.
  remember (getEntryBlock f) as R.
  destruct R; try congruence.
  destruct b as [l0 ? ? ?].
  intros vl al Hreach.
  assert (Hw':=Hreach).
  apply DWalk_to_dpath in Hreach.
  destruct Hreach as [vl0 [al0 Hp]].
  destruct (id_dec l' l3); subst; auto.
  Case "l'=l3".
    destruct (id_dec l3 l0); subst.
    SCase "l3=l0".
      symmetry in HeqR.
      apply dom_entrypoint in HeqR.
      rewrite HeqR in Hin. inv Hin.

    SCase "l3<>l0".
      inv Hp; try congruence.
      destruct y as [a0].
      assert (exists ps0, exists cs0, exists tmn0,
        blockInFdefB (block_intro a0 ps0 cs0 tmn0) f /\
        In l3 (successors_terminator tmn0)) as J.
        eapply successors__blockInFdefB; eauto.
      destruct J as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
      remember ((dom_analyze f) !! a0) as R.
      destruct R as [bs_contents bs_bounds].
      assert (In l3
        (a0 :: DomDS.L.bs_contents (bound_fdef f)
                  (dom_analyze f) !! a0)) as J.
        remember ((dom_analyze f) !! l3) as R.
        destruct R.
        assert (incl bs_contents0 (a0 :: bs_contents)) as Hinc.
          destruct f. apply uniqF__uniqBlocks in HuniqF.
          eapply dom_successors; eauto.
        rewrite <- HeqR0. simpl.
        simpl in Hin.
        apply Hinc; auto.
      eapply dom_is_sound in J; eauto.
      unfold domination in J.
      rewrite <- HeqR in J.
      assert (Hw:=H).
      apply D_path_isa_walk in Hw.
      apply J in Hw.
      destruct Hw as [Hw | Hw]; subst; try congruence.
      apply H4 in Hw. inv Hw; try congruence.
  Case "l'<>l3".
    apply HBinF in Hw'.
    split; auto. destruct Hw'; subst; auto. congruence.
Qed.

Lemma dom_tran: forall (f:fdef) (l1 l2 l3:l),
  domination f l1 l2 -> domination f l2 l3 -> domination f l1 l3.
Proof.
  unfold domination.
  intros.
  destruct (getEntryBlock f); tinv H.
  destruct b.
  intros vl al Hw.
  destruct (id_dec l1 l3); auto.
  left.
  assert (Hw':=Hw).
  apply H0 in Hw'.
  destruct Hw' as [Hw' | Hw']; subst.
    apply DW_extract with (x:=index l2) in Hw; simpl; auto.
    destruct Hw as [al' Hw].
    assert (Hw'':=Hw).
    apply H in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; auto.
    destruct (id_dec l1 l2); subst; auto.
    apply V_extract_spec in Hw''; try congruence.
    simpl in Hw''. destruct Hw'' as [Hw'' | Hw'']; congruence.

    assert (Hw'':=Hw).
    apply H in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; congruence.
Qed.

Lemma dom_acyclic: forall S M (f:fdef) (l1 l2:l) (HwfF:wf_fdef S M f)
  (HuniqF: uniqFdef f),
  reachable f l2 ->
  strict_domination f l1 l2 -> ~ domination f l2 l1.
Proof.
  unfold reachable, strict_domination, domination.
  intros. assert (HwfF':=HwfF).
  apply wf_fdef__non_entry in HwfF'.
  remember (getEntryBlock f) as R.
  destruct R; auto. clear HwfF'.
  destruct b as [l0 ? ? ?].
  destruct H as [vl [al Hw]].
  apply DWalk_to_dpath in Hw.
  destruct Hw as [vl0 [al0 Hp]].
  assert (Hw:=Hp).
  apply D_path_isa_walk in Hw.
  assert (Hw':=Hw).
  apply H0 in Hw'.
  destruct Hw' as [J1 J2].
  intros J.
  apply DW_extract with (x:=index l1) in Hw; simpl; auto.
  destruct Hw as [al' Hw].
  assert (Hw'':=Hw).
  apply J in Hw''.
  destruct Hw'' as [Hw'' | Hw'']; subst; auto.
  apply V_extract_spec' in Hw''; try congruence.
  inv Hp.
    inv Hw''.

    simpl in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; try congruence.
    apply H5 in Hw''. inv Hw''.
    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0,
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) f /\
      In l0 (successors_terminator tmn0)) as J'.
      eapply successors__blockInFdefB; eauto.
    destruct J' as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
    symmetry in HeqR. destruct f.
    eapply getEntryBlock_inv in HeqR; eauto.
Qed.

Lemma sdom_reachable : forall f l1 l2,
  reachable f l2 -> strict_domination f l1 l2 -> reachable f l1.
Proof.
  unfold reachable, strict_domination.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b.
  destruct H as [vl [al H]].
  assert (H':=H).
  apply H0 in H'. destruct H' as [J1 J2].
  apply DW_extract with (x:=index l1) in H; simpl; auto.
  destruct H as [al' H].
  exists (V_extract (index l1) (index l2 :: vl)). exists al'.
  auto.
Qed.

Lemma dom_reachable : forall f l1 l2,
  reachable f l2 -> domination f l1 l2 -> reachable f l1.
Proof.
  unfold reachable, domination.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b.
  destruct H as [vl [al H]].
  assert (H':=H).
  apply H0 in H'.
  apply DW_extract with (x:=index l1) in H; simpl; auto.
    destruct H as [al' H].
    exists (V_extract (index l1) (index l2 :: vl)). exists al'. auto.

    destruct H' as [H' | H']; subst; auto.
Qed.

Lemma everything_dominates_unreachable_blocks :
  forall f l1 l2 (Hreach: ~ reachable f l2)
  (Hentry: getEntryBlock f <> None),
  domination f l1 l2.
Proof.
  unfold reachable, domination.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b.
  intros.
  contradict Hreach. eauto.
Qed.

Lemma everything_sdominates_unreachable_blocks :
  forall f l1 l2 (Hreach: ~ reachable f l2)
  (Hentry: getEntryBlock f <> None),
  strict_domination f l1 l2.
Proof.
  unfold reachable, strict_domination.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b.
  intros.
  contradict Hreach. eauto.
Qed.

Lemma sdom_dom: forall f l1 l2,
  strict_domination f l1 l2 -> domination f l1 l2.
Proof.
  unfold strict_domination, domination.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b. intros. apply H in H0. destruct H0; auto.
Qed.

Lemma dom_sdom: forall f l1 l2,
  domination f l1 l2 -> l1 <> l2 -> strict_domination f l1 l2.
Proof.
  unfold strict_domination, domination.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b. intros. apply H in H1.
  destruct H1 as [H1 | H1]; subst; auto.
    congruence.
Qed.

Lemma sdom_tran1: forall S M (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef S M f)
  (HuniqF: uniqFdef f),
  strict_domination f l1 l2 -> domination f l2 l3 -> strict_domination f l1 l3.
Proof.
  intros.
  destruct (id_dec l1 l3); subst.
    destruct (@reachable_dec f l3).
      eapply dom_acyclic in H; eauto.
        contradict H; auto.
        apply dom_reachable in H0; auto.

      apply everything_sdominates_unreachable_blocks; auto.
        eapply wf_fdef__non_entry; eauto.

    apply sdom_dom in H.
    apply dom_sdom; eauto using dom_tran.
Qed.

Lemma sdom_tran2: forall S M (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef S M f)
  (HuniqF : uniqFdef f),
  domination f l1 l2 -> strict_domination f l2 l3 -> strict_domination f l1 l3.
Proof.
  intros.
  destruct (id_dec l1 l3); subst.
    destruct (@reachable_dec f l3).
      eapply dom_acyclic in H0; eauto.
      contradict H0; auto.

      apply everything_sdominates_unreachable_blocks; auto.
        eapply wf_fdef__non_entry; eauto.

    apply sdom_dom in H0.
    apply dom_sdom; eauto using dom_tran.
Qed.

Lemma sdom_tran: forall S M (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef S M f)
  (HuniqF: uniqFdef f),
  strict_domination f l1 l2 -> strict_domination f l2 l3 ->
  strict_domination f l1 l3.
Proof.
  intros. apply sdom_dom in H0. eapply sdom_tran1; eauto.
Qed.

Import Classical_Pred_Type.

Definition strict_domination' f l1 l2 := domination f l1 l2 /\ l1 <> l2.

Lemma sdom_sdom': forall f l1 l2,
  strict_domination f l1 l2 -> reachable f l2 -> strict_domination' f l1 l2.
Proof.
  intros.
  split. apply sdom_dom; auto.
    unfold reachable, strict_domination in *. intros.
    destruct (getEntryBlock f); tinv H.
    destruct b.
    destruct H0 as [vl [al H0]].
    apply H in H0; auto.
Qed.

Lemma sdom_dec' : forall f l1 l2,
  strict_domination' f l1 l2 \/ ~ strict_domination' f l1 l2.
Proof. intros. tauto. Qed. (* classic logic *)

Lemma sdom_ordered' : forall f l1 l2 l3
  (Hneq: l1 <> l2) (Hreach: reachable f l3)
  (Hsdom: strict_domination' f l1 l3)
  (Hsdom': strict_domination' f l2 l3),
  strict_domination' f l1 l2 \/ strict_domination' f l2 l1.
Proof.
  intros.
  destruct (sdom_dec' f l1 l2); auto.
  destruct (sdom_dec' f l2 l1); auto.
  contradict Hsdom'. intro Hsdom'.
  unfold strict_domination' in *.
  destruct Hsdom as [Hdom Hneq1].
  destruct Hsdom' as [Hdom' Hneq2].
  unfold domination, reachable in *.
  destruct (getEntryBlock f); auto.
  destruct b as [l0 ? ? ?].
  destruct Hreach as [vl [al Hreach]].
  assert (Hw:=Hreach).
  apply Hdom in Hw.
  destruct Hw as [Hin | Heq]; try congruence.
  assert (Hw:=Hreach).
  apply Hdom' in Hw.
  destruct Hw as [Hin' | Heq]; try congruence.

  (* on Hw, we need to figuire the closest one to l3 in l1 and l2,
     suppose l1 is, then we split hw at l1, so l2 cannot be in the part
     from l3 to l1.
  *)
  assert (Hw:=Hreach).
  assert (vl <> V_nil) as Hnqnil.
    destruct vl; auto.
      intro J. inv J.
  apply DW_cut with (x:=index l1) (w:=index l2) in Hw; try congruence;
    simpl; auto.
  destruct Hw as [al1 [al2 [vl1 [vl2
    [[J1 [J2 [J3 [J4 J5]]]]|[J1 [J2 [J3 [J4 J5]]]]]]]]]; subst.
  Case "1".
  assert (exists vl:V_list, exists al:A_list,
    D_walk (vertexes_fdef f) (arcs_fdef f) (index l1) (index l0) vl al /\
    ~ In (index l2) vl) as J.
    clear - Hneq H0.
    apply tauto_helper in H0; auto.
    apply not_all_ex_not in H0. (* can we remove the classic lemma? *)
    destruct H0 as [vl H0].
    apply not_all_ex_not in H0.
    destruct H0 as [al H0].
    exists vl. exists al.
    tauto.
  destruct J as [vl1' [al1' [J1' J2']]].

  assert ((D_walk (vertexes_fdef f) (arcs_fdef f) (index l3) (index l0)
    (vl1++vl1') (al1++al1') * ~ In (index l2) (vl1++vl1'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hdom' in J3.
  destruct J3 as [Hin'' | Heq]; try congruence.

  Case "2".
  assert (exists vl:V_list, exists al:A_list,
    D_walk (vertexes_fdef f) (arcs_fdef f) (index l2) (index l0) vl al /\
    ~ In (index l1) vl) as J.
    clear - Hneq H.
    apply tauto_helper in H; auto.
    apply not_all_ex_not in H.
    destruct H as [vl H].
    apply not_all_ex_not in H.
    destruct H as [al H].
    exists vl. exists al.
    tauto.
  destruct J as [vl2' [al2' [J1' J2']]].

  assert ((D_walk (vertexes_fdef f) (arcs_fdef f) (index l3) (index l0)
    (vl1++vl2') (al1++al2') * ~ In (index l1) (vl1++vl2'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hdom in J3.
  destruct J3 as [Hin'' | Heq]; try congruence.
Qed.

Lemma sdom_ordered : forall f l1 l2 l3
  (Hneq: l1 <> l2) (Hreach: reachable f l3)
  (Hsdom: strict_domination f l1 l3)
  (Hsdom': strict_domination f l2 l3),
  strict_domination f l1 l2 \/ strict_domination f l2 l1.
Proof.
  intros.
  apply sdom_sdom' in Hsdom; auto.
  apply sdom_sdom' in Hsdom'; auto.
  assert (J:=Hsdom').
  eapply sdom_ordered' in J; eauto.
  destruct J as [[J1 J2] | [J1 J2]].
    left. apply dom_sdom; auto.
    right. apply dom_sdom; auto.
Qed.

Lemma adom_acyclic: forall l1 l2 ps1 cs1 tmn1 ps2 cs2 tmn2 S M F,
  wf_fdef S M F -> uniqFdef F ->
  reachable F l2 ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F = true ->
  blockInFdefB (block_intro l2 ps2 cs2 tmn2) F = true ->
  In l1 (DomDS.L.bs_contents (bound_fdef F) ((dom_analyze F) !! l2)) ->
  In l2 (DomDS.L.bs_contents (bound_fdef F) ((dom_analyze F) !! l1)) ->
  l1 <> l2 ->
  False.
Proof.
  intros.
  assert (strict_domination F l1 l2) as Hdom12.
    eapply sdom_is_sound; eauto.
  assert (strict_domination F l2 l1) as Hdom21.
    eapply sdom_is_sound; eauto.
  eapply dom_acyclic in Hdom12; eauto.
  apply Hdom12. apply sdom_dom; auto.
Qed.

Lemma blockStrictDominates_trans : forall S M f b1 b2 b3
  (HwfF: wf_fdef S M f) (HuniqF:uniqFdef f)
  (HBinF1: blockInFdefB b1 f)
  (HBinF2: blockInFdefB b2 f)
  (HBinF3: blockInFdefB b3 f)
  (H1 : blockStrictDominates f b1 b2)
  (H2 : blockStrictDominates f b2 b3),
  blockStrictDominates f b1 b3.
Proof.
  unfold blockStrictDominates.
  intros. destruct b1 as [l0 ? ? ?], b2 as [l1 ? ? ?], b3 as [l2 ? ? ?].
  remember (Maps.AMap.get l1 (dom_analyze f)) as R1.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R2.
  destruct R1. destruct R2.
  destruct (reachable_dec f l2).
    assert (strict_domination f l1 l2) as Hsdom23.
      eapply sdom_is_sound; eauto.
        rewrite <- HeqR2. simpl. auto.
    assert (reachable f l1) as Hreach1.
      apply sdom_reachable in Hsdom23; auto.
    assert (strict_domination f l0 l1) as Hsdom12.
      eapply sdom_is_sound; eauto.
        rewrite <- HeqR1. simpl. auto.
    assert (strict_domination f l0 l2) as Hsdom13.
      eapply sdom_tran with (l2:=l1); eauto.
    eapply sdom_is_complete in Hsdom13; eauto.
      rewrite <- HeqR2 in Hsdom13. simpl in *. auto.

      rewrite <- HeqR2. simpl.
      destruct bs_contents0; auto.
        intro J. inv J.

    eapply dom_unreachable in H; eauto.
      rewrite <- HeqR2 in H. simpl in H.
      destruct H. apply H0.
      apply blockInFdefB_in_vertexes in HBinF1.
      unfold vertexes_fdef in HBinF1. auto.

      rewrite <- HeqR2. simpl. intro J. subst. inv H2.
Qed.

Lemma blockDominates_trans : forall S M f b1 b2 b3
  (HwfF: wf_fdef S M f) (HuniqF:uniqFdef f)
  (HBinF1: blockInFdefB b1 f)
  (HBinF2: blockInFdefB b2 f)
  (HBinF3: blockInFdefB b3 f)
  (H1 : blockDominates f b1 b2)
  (H2 : blockDominates f b2 b3),
  blockDominates f b1 b3.
Proof.
  unfold blockDominates.
  intros. destruct b1 as [l0 ? ? ?], b2 as [l1 ? ? ?], b3 as [l2 ? ? ?].
  remember (Maps.AMap.get l1 (dom_analyze f)) as R1.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R2.
  destruct R1. destruct R2.
  destruct (l_dec l0 l2); auto.
  destruct H2 as [H2 | H2]; subst; auto.
  Case "l1 in sdom(l2)".
    left.
    assert (domination f l1 l2) as Hdom23.
      eapply dom_is_sound; eauto.
        rewrite <- HeqR2. simpl. auto.
    destruct H1 as [H1 | H1]; subst.
    SCase "l0 in sdom(l1)".
      assert (domination f l0 l1) as Hdom12.
        eapply dom_is_sound; eauto.
          rewrite <- HeqR1. simpl. auto.
      assert (strict_domination f l0 l2) as Hsdom13.
        apply dom_sdom; auto.
        eapply dom_tran; eauto.
      eapply sdom_is_complete in Hsdom13; eauto.
        rewrite <- HeqR2 in Hsdom13. simpl in *. auto.

        rewrite <- HeqR2. simpl.
        destruct bs_contents0; auto.
          intro J. inv J.

    SCase "l0=l1".
      assert (strict_domination f l1 l2) as Hsdom12.
        apply dom_sdom; auto.
      eapply sdom_is_complete in Hsdom12; eauto.
        rewrite <- HeqR2. simpl.
        destruct bs_contents0; auto.
          intro J. inv J.

  Case "l1=l2".
    rewrite <- HeqR2 in HeqR1. inv HeqR1; auto.
Qed.
End AnotherDominators.

Lemma wf_insn__wf_value: forall S m F B instr v
  (Hwfi: wf_insn S m F B instr)
  (HvInOps : valueInInsnOperands v instr),
  exists t, wf_value S m F v t.
Proof.
  intros.
  destruct instr.
    inv Hwfi. simpl in *.
    apply In_list_prj1__getValueViaLabelFromValuels in HvInOps.
      destruct HvInOps as [l1 HvInOps].

      find_wf_value_list.
      eapply wf_value_list__getValueViaLabelFromValuels__wf_value in H0; eauto.

      match goal with
      | H9: _ /\ check_list_value_l _ _ _ |- _ =>
        destruct H9 as [_ H5];
        unfold check_list_value_l in H5;
        remember (split value_l_list) as R;
        destruct R;
        destruct H5 as [_ [_ H5]]; auto
      end.

    eapply wf_cmd__wf_value; eauto.

    eapply wf_tmn__wf_value; eauto.
Qed.

Lemma wf_phinodes__wf_phinode : forall s m f b ps p,
  wf_phinodes s m f b ps ->
  In p ps ->
  wf_insn s m f b (insn_phinode p).
Proof.
  induction ps; intros.
    inversion H0.

    simpl in H0.
    inv H.
    destruct H0 as [H0 | H0]; subst; eauto.
Qed.

Lemma wf_fdef__wf_insn: forall S m instr F B
  (HwfF: wf_fdef S m F)
  (HBinF : insnInFdefBlockB instr F B = true),
  wf_insn S m F B instr.
Proof.
  intros.
  destruct B.
  destruct instr; apply andb_true_iff in HBinF; destruct HBinF as [J1 J2].
    eapply wf_fdef__blockInFdefB__wf_block in J2; eauto.
    simpl in J1.
    apply InPhiNodesB_In in J1.
    inv J2.
    eapply wf_phinodes__wf_phinode; eauto.

    simpl in J1.
    apply InCmdsB_in in J1.
    apply wf_fdef__wf_cmd; auto.

    simpl in J1.
    apply terminatorEqB_inv in J1.
    subst.
    apply wf_fdef__wf_tmn; auto.
Qed.

Definition wf_list_targetdata_typ (S:system) (TD:targetdata) gl lsd :=
  forall S1 TD1, In (S1,TD1) lsd -> wf_global TD S1 gl /\ S = S1 /\ TD = TD1.

Lemma const2GV_typsize_mutind_array : forall const_list system5
  (typ5 : typ)
  (los : list layout) (nts : list namedt) gl
  (lsdc : list (system * targetdata * const)) lt
  (HeqR0 : (lsdc, lt) =
          split
            (List.map
              (fun const_ : const =>
                (system5, (los, nts), const_, typ5)) const_list))
  (lsd : list (system * targetdata)) lc
  (HeqR' : (lsd, lc) = split lsdc)
  ls (ld : list targetdata)
  (HeqR'' : (ls, ld) = split lsd)
  (H3 : wf_global (los, nts) system5 gl),
  wf_list_targetdata_typ system5 (los, nts) gl lsd.
Proof.
  intros.
  unfold wf_list_targetdata_typ.
  generalize dependent lsdc.
  generalize dependent lt.
  generalize dependent lc.
  generalize dependent ld.
  generalize dependent ls0.
  generalize dependent lsd.
  induction const_list; intros; simpl in *.
    inv HeqR0. inv HeqR'. inv H.

    remember (split
                 (List.map
                    (fun const_ : const =>
                     (system5, (los, nts), const_, typ5)) const_list)) as R.
    destruct R.
    inv HeqR0. simpl in HeqR'.
    remember (@split (system * targetdata) _ l0) as R1.
    destruct R1.
    inv HeqR'. simpl in HeqR''.
    remember (split l2) as R2.
    destruct R2.
    inv HeqR''. simpl in H.
    destruct H as [H | H]; subst; eauto.
      inv H. split; auto.
Qed.

Lemma const2GV_typsize_mutind_struct : forall const_typ_list system5 los nts gl
  lsdc lt
  (HeqR : (lsdc, lt) =
         split
           (List.map
             (fun (p : const * typ) =>
               let '(c, t) := p in
               (system5, (los, nts), c, t)) const_typ_list))
  lsd lc
  (HeqR' : (lsd, lc) = split lsdc)
  (H3 : wf_global (los, nts) system5 gl),
  wf_list_targetdata_typ system5 (los, nts) gl lsd.
Proof.
  intros.
  generalize dependent lsdc.
  generalize dependent lt.
  generalize dependent lc.
  generalize dependent lsd.
  induction const_typ_list; simpl; intros.
    inv HeqR. simpl in HeqR'. inv HeqR'.
    unfold wf_list_targetdata_typ.
    intros S TD Hin. inversion Hin.

    destruct a. simpl_split lsdc' lt'.
    inv HeqR. simpl in HeqR'. 
    simpl_split lsd' lc'. inv HeqR'.
    unfold wf_list_targetdata_typ in *.
    intros S TD Hin.
    simpl in Hin.
    destruct Hin as [Hin | Hin]; eauto.
      inv Hin. split; auto.
Qed.

Lemma wf_list_targetdata_typ_cons_inv : forall S TD gl S'  TD' lsd,
  wf_list_targetdata_typ S TD gl ((S', TD') :: lsd) ->
  wf_list_targetdata_typ S TD gl lsd /\ S' = S /\ TD' = TD /\ wf_global TD S gl.
Proof.
  intros.
  unfold wf_list_targetdata_typ in *.
  assert (In (S', TD') ((S', TD') :: lsd)) as J. simpl. auto.
  apply H in J.
  destruct J as [J1 [J2 J3]]; subst.
  split.
    intros S1 TD1 Hin.
    apply H. simpl. auto.
  split; auto.
Qed.

Definition wf_list_targetdata_typ' (S:system) (TD:targetdata) lsd :=
  forall S1 TD1, In (S1,TD1) lsd -> S = S1 /\ TD = TD1.

Lemma const2GV_typsize_mutind_array' : forall const_list system5
  (typ5 : typ)
  (los : list layout) (nts : list namedt)
  (lsdc : list (system * targetdata * const)) lt
  (HeqR0 : (lsdc, lt) =
          split
            (List.map
              (fun const_ : const =>
                (system5, (los, nts), const_, typ5)) const_list))
  (lsd : list (system * targetdata)) lc
  (HeqR' : (lsd, lc) = split lsdc)
  ls (ld : list targetdata)
  (HeqR'' : (ls, ld) = split lsd),
  wf_list_targetdata_typ' system5 (los, nts) lsd.
Proof.
  intros.
  unfold wf_list_targetdata_typ'.
  generalize dependent lsdc.
  generalize dependent lt.
  generalize dependent lc.
  generalize dependent ld.
  generalize dependent ls0.
  generalize dependent lsd.
  induction const_list; intros; simpl in *.
    inv HeqR0. inv HeqR'. inv H.

    remember (split
                 (List.map
                    (fun const_ : const =>
                     (system5, (los, nts), const_, typ5)) const_list)) as R.
    destruct R.
    inv HeqR0. simpl in HeqR'.
    remember (@split (system * targetdata) _ l0) as R1.
    destruct R1.
    inv HeqR'. simpl in HeqR''.
    remember (split l2) as R2.
    destruct R2.
    inv HeqR''. simpl in H.
    destruct H as [H | H]; subst; eauto.
      inv H. split; auto.
Qed.

Lemma const2GV_typsize_mutind_struct' : forall const_typ_list system5 los nts
  lsdc lt
  (HeqR : (lsdc, lt) =
         split
           (List.map
             (fun (p : const * typ) =>
               let '(c, t) := p in
                 (system5, (los, nts), c, t)) const_typ_list))
  lsd lc
  (HeqR' : (lsd, lc) = split lsdc),
  wf_list_targetdata_typ' system5 (los, nts) lsd.
Proof.
  intros.
  generalize dependent lsdc.
  generalize dependent lt.
  generalize dependent lc.
  generalize dependent lsd.
  induction const_typ_list as [|[? ?] l]; simpl; intros.
    inv HeqR. simpl in HeqR'. inv HeqR'.
    unfold wf_list_targetdata_typ.
    intros S TD Hin. inversion Hin.

    simpl_split. inv HeqR. simpl in *. 
    simpl_split. inv HeqR'.
    unfold wf_list_targetdata_typ' in *.
    intros S TD Hin.
    simpl in Hin.
    destruct Hin as [Hin | Hin]; eauto.
      inv Hin. split; auto.
Qed.

Lemma wf_list_targetdata_typ_cons_inv' : forall S TD S'  TD' lsd,
  wf_list_targetdata_typ' S TD ((S', TD') :: lsd) ->
  wf_list_targetdata_typ' S TD lsd /\ S' = S /\ TD' = TD.
Proof.
  intros.
  unfold wf_list_targetdata_typ' in *.
  assert (In (S', TD') ((S', TD') :: lsd)) as J. simpl. auto.
  apply H in J.
  destruct J as [J1 J2]; subst.
  split.
    intros S1 TD1 Hin.
    apply H. simpl. auto.
  split; auto.
Qed.

Lemma wf_phinodes__nth_list_value_l__wf_value: forall s m f b ps id1 t1 vls1
  n v lv (Hwfps: wf_phinodes s m f b ps) (Hin: In (insn_phi id1 t1 vls1) ps)
  (Hnth: nth_error vls1 n = Some (v, lv)),
  wf_value s m f v t1.
Proof.
  intros.
  eapply wf_phinodes__wf_phinode in Hwfps; eauto. inv Hwfps.
  match goal with
  | Hnth: nth_error _ _ = _,
    H6: forall _:_, In _ _ -> _ |- _ => clear - Hnth H6
  end.
  generalize dependent vls1.
  induction n as [|n]; simpl; intros; auto.
    destruct vls1 as [|[val l0] vls1]; inv Hnth.
      apply H6. left. trivial.
    destruct vls1 as [|[vla l0] vls1]; inv Hnth.
      apply IHn with vls1; auto.
      intros v' Hv'. apply H6. right. trivial.
Qed.

Lemma block_in_scope__strict: forall (l' : l) (ps' : phinodes) (cs' : cmds)
  (F : fdef) (tmn' : terminator)
  (Hreach' : isReachableFromEntry F (block_intro l' ps' cs' tmn')) s m
  (HwfF : wf_fdef s m F) (HuniqF : uniqFdef F)
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_fdef F))
  (Heqdefs' : {| DomDS.L.bs_contents := contents';
                 DomDS.L.bs_bound := inbound' |} = (dom_analyze F) !! l')
  (l0 : l) (Hindom' : In l0 contents')
  (HbInF' : blockInFdefB (block_intro l' ps' cs' tmn') F = true),
  l0 <> l'.
Proof.
  intros.
  assert (strict_domination F l0 l') as Hdom12.
    eapply sdom_is_sound; eauto.
      rewrite <- Heqdefs'. simpl. auto.
  destruct Hdom12; auto.
Qed.

Lemma wf_fdef__wf_insn_base' : forall S M F id1 instr
  (HwfF: wf_fdef S M F) (HnPhi:~ isPhiNode instr)
  (Hlkup: lookupInsnViaIDFromFdef F id1 = ret instr),
  exists b1, wf_insn_base F b1 instr.
Proof.
  intros.
  apply lookupInsnViaIDFromFdef__insnInFdefBlockB' in Hlkup.
  destruct Hlkup as [b Hlkup]. exists b.
  apply destruct_insnInFdefBlockB in Hlkup.
  destruct Hlkup as [J1 J2].
  destruct b.
  destruct instr.
    contradict HnPhi. constructor.

    apply InCmdsB_in in J1.
    eapply wf_fdef__wf_cmd in J2; eauto.
    apply wf_insn__wf_insn_base in J2; auto.

    simpl in J1. apply terminatorEqB_inv in J1. subst.
    eapply wf_fdef__wf_tmn in J2; eauto.
    apply wf_insn__wf_insn_base in J2; auto.
Qed.

Lemma wf_fdef__wf_insn_base : forall S M F id1 c1,
  wf_fdef S M F ->
  lookupInsnViaIDFromFdef F id1 = ret insn_cmd c1 ->
  exists b1, wf_insn_base F b1 (insn_cmd c1).
Proof.
  intros.
  eapply wf_fdef__wf_insn_base'; eauto.
    intro. inv H1.
Qed.

Lemma in_unmake_list_id__nth_list_id: forall i0 tl hd
  (id_list : list id)
  (H1 : hd ++ i0 :: tl  = id_list),
  exists n : nat, nth_error id_list n = ret i0.
Proof.
  induction hd; simpl; intros.
    exists 0%nat. destruct id_list; inv H1. simpl. auto.

    destruct id_list; inversion H1.
    edestruct IHhd as [n H]; eauto.
    exists (S n). simpl. subst. auto.
Qed.

Lemma values2ids__nth_list_id: forall (i0 : id) (id_list : list id) l0 hd
  (i3 : In i0 (values2ids l0))
  (H1 : hd ++ values2ids l0 = id_list),
  exists n : nat, nth_error id_list n = ret i0.
Proof.
  induction l0; simpl; intros.
    tauto.

    destruct a.
      simpl in i3.
      destruct i3 as [EQ | Hin]; subst.
        eapply in_unmake_list_id__nth_list_id; eauto.

        apply IHl0 with (hd0:=hd++[id5]); auto.
        simpl_env. simpl. auto.

      apply IHl0 with (hd:=hd); auto.
Qed.

Lemma getParamsOperand__nth_list_id: forall (i0 : id)
  (id_list : list id) p hd
  (i3 : In i0 (getParamsOperand p))
  (H1 : hd ++ getParamsOperand p = id_list),
  exists n : nat, nth_error id_list n = ret i0.
Proof.
  unfold getParamsOperand.
  intros. destruct (split p).
  eapply values2ids__nth_list_id; eauto.
Qed.

Lemma getCmdOperands__nth_list_id : forall i0 c1 id_list
  (i1 : In i0 (getCmdOperands c1))
  (H1 : getInsnOperands (insn_cmd c1) = id_list),
  exists n : nat, nth_error id_list n = ret i0.
Proof.

intros i c id_list Hin Heq. subst id_list.

destruct c; simpl; intros; unfold getValueIDs in *;
repeat match goal with
         | v:value |- _ => destruct v
       end;
simpl in *;
repeat match goal with
         | H : _ \/ _ |- _ => destruct H
         | H : False |- _ => contradict H
       end;
subst;
try solve [
  exists 0%nat; trivial |
  exists 1%nat; trivial |
  exists 2%nat; trivial ];
try match goal with
      | H : In _ _ |- _ =>
        rewrite nth_error_in in H;
        destruct H as [n Hn];
        solve [ exists n; trivial | exists (S n); trivial ]
    end.
Qed.

Lemma in_getArgsIDsOfFdef__inscope_of_tmn: forall defs f b tmn id1
  (Hinscope: inscope_of_tmn f b tmn = Some defs)
  (Hin: In id1 (getArgsIDsOfFdef f)), In id1 defs.
Proof.
  intros. destruct b as [l1 ? ? ?].
  unfold inscope_of_tmn in Hinscope.
  remember ((dom_analyze f) !! l1) as R.
  destruct R.
  apply fold_left__spec in Hinscope.
  destruct Hinscope as [Hinscope _].
  apply Hinscope. solve_in_list.
Qed.

Lemma in_getArgsIDsOfFdef__init_scope: forall f ps cs id0 id1
  (Hin:In id1 (getArgsIDsOfFdef f)), In id1 (init_scope f ps cs id0).
Proof.
  intros.
  unfold init_scope.
  destruct_if; auto.
    solve_in_list.
Qed.

Lemma in_getArgsIDsOfFdef__inscope_of_id: forall defs f b id0 id1
  (Hinscope: inscope_of_id f b id0 = Some defs)
  (Hin: In id1 (getArgsIDsOfFdef f)), In id1 defs.
Proof.
  intros. destruct b as [l1 ? ? ?].
  unfold inscope_of_id in Hinscope.
  remember ((dom_analyze f) !! l1) as R.
  destruct R.
  apply fold_left__spec in Hinscope.
  destruct Hinscope as [Hinscope _].
  apply Hinscope. apply in_getArgsIDsOfFdef__init_scope; auto.
Qed.

Lemma in_getArgsIDsOfFdef__inscope_of_cmd: forall defs f b c id1
  (Hinscope: inscope_of_cmd f b c = Some defs)
  (Hin: In id1 (getArgsIDsOfFdef f)), In id1 defs.
Proof.
  intros. destruct b as [l1 ? ? ?].
  unfold inscope_of_cmd, inscope_of_id in Hinscope.
  remember ((dom_analyze f) !! l1) as R.
  destruct R.
  apply fold_left__spec in Hinscope.
  destruct Hinscope as [Hinscope _].
  apply Hinscope. apply in_getArgsIDsOfFdef__init_scope; auto.
Qed.

Lemma operands_of_cmd__cannot_be__phis_that_cmd_doms: forall (l' : l)
  (ps' : phinodes) (cs' : cmds) (F : fdef) (tmn' : terminator) (b : block)
  (Hreach' : isReachableFromEntry F (block_intro l' ps' cs' tmn')) s m
  (Hlkup : ret block_intro l' ps' cs' tmn' = lookupBlockViaLabelFromFdef F l')
  (ids0' : list atom) (HwfF : wf_fdef s m F) (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_fdef F)) (Huniq: uniqFdef F)
  (Heqdefs' : {| DomDS.L.bs_contents := contents';
                 DomDS.L.bs_bound := inbound' |} = (dom_analyze F) !! l')
  (Hinscope : fold_left (inscope_of_block F l') contents'
               (ret (getPhiNodesIDs ps' ++ getArgsIDsOfFdef F)) = ret ids0')
  (id1 : atom) (Hid1 : In id1 ids0')
  (Hnotin' : ~ In id1 (getPhiNodesIDs ps' ++ getArgsIDsOfFdef F))
  (i0 : atom) (HeqR1' : In i0 (getPhiNodesIDs ps')) (c1 : cmd)
  (Hlkc1 : lookupInsnViaIDFromFdef F id1 = ret insn_cmd c1)
  (Hreach'' : forall b1 : block,
              cmdInFdefBlockB c1 F b1 = true -> isReachableFromEntry F b1)
  (i1 : In i0 (getCmdOperands c1)),
  False.
Proof.
  intros.
  assert (exists b1, wf_insn_base F b1 (insn_cmd c1)) as HwfI.
    eapply wf_fdef__wf_insn_base; eauto.
  destruct HwfI as [b1 HwfI].
  inv HwfI.
  assert (exists n, nth_error id_list n = Some i0) as Hnth.
    eapply getCmdOperands__nth_list_id; eauto.
  destruct Hnth as [n Hnth].
  apply (wf_operand_list__wf_operand _ F b1 (insn_cmd c1)) in Hnth.
  inv Hnth.
  match goal with
  | H10: (exists _:_, _) \/ In _ (getArgsIDsOfFdef _) |- _ =>
     destruct H10 as [[block' [Hlk H10]] | H10]
  end.
  Case "i0 isnt args".
  assert (isReachableFromEntry F b1) as Hreachb1.
    apply Hreach'' in H. auto.
  assert (block_intro l' ps' cs' tmn' = block') as EQ.
    eapply lookupBlockViaIDFromFdef__lookupBlockViaLabelFromFdef__eq;
      eauto.
      solve_in_list.
  subst.
  destruct b1 as [l0 p c t0].
  assert (In l0 contents') as Hindom'.
    eapply cmd_in_scope__block_in_scope; eauto.
  assert (blockInFdefB (block_intro l' ps' cs' tmn') F = true)as HbInF'.
    symmetry in Hlkup.
    apply lookupBlockViaLabelFromFdef_inv in Hlkup; auto.
    destruct Hlkup; auto.
  assert (l0 <> l') as Hneq.
    eapply block_in_scope__strict; eauto.
  assert (blockInFdefB (block_intro l0 p c t0) F = true)as HbInF0.
    eauto using insnInFdefBlockB__blockInFdefB.
  assert (In l' (DomDS.L.bs_contents (bound_fdef F)
    ((dom_analyze F) !! l0))) as Hindom.
    eapply domination__block_in_scope; eauto.
  eapply adom_acyclic in Hindom; eauto.
  rewrite <- Heqdefs'. simpl. auto.
  Case "i0 is args".
    assert (blockInFdefB (block_intro l' ps' cs' tmn') F = true) as HBinF.
      solve_blockInFdefB.
    eapply getBlocksLocs__notin__getArgsIDs in HBinF; eauto.
    solve_in_list.
  Case "wf_operand".
    unfold wf_operand_list.
    remove_irrelevant wf_operand.
    solve_forall_like_ind.
Qed.

Lemma isReachableFromEntry_successors : forall f l3 ps cs tmn l' b'
  (Hreach : isReachableFromEntry f (block_intro l3 ps cs tmn))
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Huniq : uniqFdef f) s m (HwfF : wf_fdef s m f)
  (Hsucc : In l' (successors_terminator tmn))
  (Hlkup : lookupBlockViaLabelFromFdef f l' = Some b'),
  isReachableFromEntry f b'.
Proof.
  intros.
  unfold isReachableFromEntry in *. destruct b'.
  apply lookupBlockViaLabelFromFdef_inv in Hlkup; auto.
  destruct Hlkup as [Hlkup _]. subst.
  eapply reachable_successors; eauto.
Qed.

Lemma strict_operands__in_scope: forall f (l1 : l) (ps1 : phinodes)
  (cs1 : cmds) (tmn1 : terminator) (defs : list atom) (id1 : id)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1))
  (bs_contents : ListSet.set atom)
  (bs_bound : incl bs_contents (bound_fdef f))
  (HeqR : {|
         DomDS.L.bs_contents := bs_contents;
         DomDS.L.bs_bound := bs_bound |} = (dom_analyze f) !! l1)
  (Hinscope : forall (l2 : atom) (b1 : block),
             In l2 (ListSet.set_diff eq_atom_dec bs_contents [l1]) ->
             lookupBlockViaLabelFromFdef f l2 = ret b1 ->
             incl (getBlockIDs b1) defs) s m
  (HwfF : wf_fdef s m f) (Huniq: uniqFdef f) instr
  (HinOps : In id1 (getInsnOperands instr))
  (H:insnInFdefBlockB instr f (block_intro l1 ps1 cs1 tmn1) = true)
  (block' : block)
  (H4 : lookupBlockViaIDFromFdef f id1 = ret block')
  (J': blockStrictDominates f block' (block_intro l1 ps1 cs1 tmn1)),
  In id1 defs.
Proof.
  intros.
  unfold blockStrictDominates in J'.
  rewrite <- HeqR in J'.
  destruct block'.
  assert (In l5 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as J.
    simpl in Hreach.
    apply insnInFdefBlockB__blockInFdefB in H.
    eapply sdom_isnt_refl with (l':=l5) in Hreach; eauto.
      apply ListSet.set_diff_intro; auto.
      simpl. intro J. destruct J as [J | J]; auto.
      rewrite <- HeqR. simpl. auto.
  assert (lookupBlockViaLabelFromFdef f l5 = 
    ret block_intro l5 phinodes5 cmds5 terminator5) as J1.
     apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
     eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto.
  apply Hinscope with
    (b1:=block_intro l5 phinodes5 cmds5 terminator5) in J; auto.
    apply J.
    eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma terminator_operands__in_scope: forall (f : fdef) (l1 : l) (ps1 : phinodes)
  (cs1 : cmds) (tmn1 : terminator) (defs : list atom) (id1 : id)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1))
  (Hinscope : ret defs = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  s m (HwfF : wf_fdef s m f) (Huniq: uniqFdef f)
  (HinOps : In id1 (getInsnOperands (insn_terminator tmn1)))
  (H : insnInFdefBlockB (insn_terminator tmn1) f (block_intro l1 ps1 cs1 tmn1) =
       true)
  (H2 : wf_operand f (block_intro l1 ps1 cs1 tmn1) (insn_terminator tmn1) id1),
  In id1 defs.
Proof.
  intros.
  inv H2.
  match goal with
  | H10: (exists _:_, _) \/ In _ (getArgsIDsOfFdef _) |- _ =>
     destruct H10 as [[block' [Hlk H10]] | H10]
  end.
  Case "id1 isnt args".
  unfold inscope_of_tmn in Hinscope.
  destruct f as [[fa ty fid la va] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro fa ty fid la va) bs)) !! l1)
    as R.
  destruct R.
  symmetry in Hinscope.
  apply fold_left__spec in Hinscope.
  match goal with
  | H6: _ \/ _ \/ _ |- _ =>
    destruct H6 as [J' | [J' | J']]; try solve [contradict J'; auto]
  end.
    SCase "insnDom".
    destruct Hinscope as [Hinscope _].
    apply Hinscope.
    eapply insnDominates_spec6; eauto.

    SCase "blkDom".
    destruct Hinscope as [_ [Hinscope _]].
    eapply strict_operands__in_scope; eauto.
  Case "id1 is args".
    eapply in_getArgsIDsOfFdef__inscope_of_tmn; eauto.
Qed.

Lemma cmd_operands__in_scope: forall (f : fdef) (b : block) (c : cmd)
  (defs : list atom) (id1 : id) (Hnodup : NoDup (getBlockLocs b))
  (Hreach : isReachableFromEntry f b)
  (Hinscope : ret defs = inscope_of_cmd f b c)
  s m (HwfF : wf_fdef s m f) (HuniqF : uniqFdef f)
  (HinOps : In id1 (getInsnOperands (insn_cmd c)))
  (H : insnInFdefBlockB (insn_cmd c) f b = true)
  (H2 : wf_operand f b (insn_cmd c) id1),
  In id1 defs.
Proof.
  intros.
  inv H2.
  match goal with
  | H10: (exists _:_, _) \/ In _ (getArgsIDsOfFdef _) |- _ =>
     destruct H10 as [[block' [Hlk H10]] | H10]
  end.
  Case "id1 isnt args".
  unfold inscope_of_cmd, inscope_of_id in Hinscope.
  destruct b. destruct f as [[f t0 i0 a v] b].
  remember ((dom_analyze (fdef_intro (fheader_intro f t0 i0 a v) b)) !! l5) as R.
  destruct R.
  symmetry in Hinscope.
  assert (~ In (getCmdLoc c) (getPhiNodesIDs phinodes5)) as Hnotin.
    simpl in Hnodup.
    eapply NoDup_disjoint; eauto.
    apply destruct_insnInFdefBlockB in H.
    destruct H. simpl in H.
    solve_in_list.
  apply fold_left__spec in Hinscope.
  match goal with
  | H6: _ \/ _ \/ _ |- _ =>
    destruct H6 as [J' | [J' | J']]; try solve [contradict J'; auto]
  end.
    SCase "insnDom".
    destruct Hinscope as [Hinscope _].
    apply Hinscope.
    unfold init_scope.
    destruct_if; try solve [tauto].
    simpl in J'.
    destruct J' as [[ps2 [p1 [ps3 [J1 J2]]]] | [cs1 [c1' [cs2 [cs3 [J1 J2]]]]]]
      ; subst.
      SSCase "p >> ".
        solve_in_list.

      SSCase "c >> ".
      clear - J2 Hnodup.
      apply in_or_app. right.
      apply in_or_app. left.
        simpl in Hnodup. apply NoDup_inv in Hnodup.
        destruct Hnodup as [_ Hnodup].
        apply NoDup_inv in Hnodup.
        destruct Hnodup as [Hnodup _].
        rewrite_env ((cs1 ++ c1' :: cs2) ++ c :: cs3).
        rewrite_env ((cs1 ++ c1' :: cs2) ++ c :: cs3) in Hnodup.
        apply NoDup__In_cmds_dominates_cmd; auto.
          solve_in_list.

    SCase "blkDom".
    destruct Hinscope as [_ [Hinscope _]].
    eapply strict_operands__in_scope; eauto.
  Case "id1 is args".
    eapply in_getArgsIDsOfFdef__inscope_of_cmd; eauto.
Qed.

Lemma cmd_doesnt_use_self: forall (F1 : fdef) (l3 : l) (ps1 : phinodes)
  (cs : list cmd) (tmn1 : terminator)
  (Hreach : isReachableFromEntry F1 (block_intro l3 ps1 cs tmn1))
  (HBinF1 : blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true) s m
  (HwfF1 : wf_fdef s m F1) (Huniq: uniqFdef F1) (c1 : cmd) (b1 : block)
  (id_list : list id)
  (H : insnInFdefBlockB (insn_cmd c1) F1 b1 = true)
  (H2 : wf_operand_list
          (List.map (fun id_ : id => (F1, b1, insn_cmd c1, id_)) id_list))
  (H1 : getInsnOperands (insn_cmd c1) = id_list)
  (Hreach': isReachableFromEntry F1 b1),
  ~ In (getCmdLoc c1) (getCmdOperands c1).
Proof.
  intros.
  destruct (in_dec id_dec (getCmdLoc c1) (getCmdOperands c1)); auto.
  assert (exists n, nth_error id_list n = Some (getCmdLoc c1)) as Hnth.
    eapply getCmdOperands__nth_list_id; eauto.
  destruct Hnth as [n Hnth].
  eapply wf_operand_list__wf_operand in Hnth; eauto.
  inv Hnth.
  match goal with
  | H10: (exists _:_, _) \/ In _ (getArgsIDsOfFdef _) |- _ =>
     destruct H10 as [[block' [Hlk H10]] | H10]
  end.
  Case "id1 isnt args".
  assert (b1 = block') as EQ.
    eapply insnInFdefBlockB__lookupBlockViaIDFromFdef__eq; eauto.
  subst.
  match goal with
  | H7: _ \/ _ \/ _ |- _ =>
    destruct H7 as [H7 | [H7 | H7]]; auto; contradict H7
  end.
    SCase "insnDom".
       assert (H':=H).
       apply insnInFdefBlockB__blockInFdefB in H'.
       apply uniqFdef__uniqBlockLocs in H'; auto.
       apply insnInFdefBlockB__insnInBlockB in H.
       apply insnDominates_spec1; auto.
    SCase "blkDom".
      apply insnInFdefBlockB__blockInFdefB in H.
      eapply blockStrictDominates_isnt_refl; eauto.
  Case "id1 is args".
    contradict H6.
    apply getInsnLoc__notin__getArgsIDs'' in H; auto.
Qed.

Lemma wf_insn_base__non_selfref: forall f b c0 id' s m
  (Hreach: isReachableFromEntry f b) (HwfF:wf_fdef s m f) (HuniqF: uniqFdef f),
  wf_insn_base f b (insn_cmd c0) ->
  In id' (getCmdOperands c0) ->
  id' <> getCmdLoc c0.
Proof.
  intros. inv H.
  intro EQ. subst.
  revert H0. destruct b.
  eapply cmd_doesnt_use_self; eauto.
    solve_blockInFdefB.
  unfold wf_operand_list.
  remove_irrelevant wf_operand.
  generalize H8.
  generalize (getInsnOperands (insn_cmd c0)).
  clear H8. intros is H. unfold ids in *.
  solve_forall_like_ind.
Qed.

Lemma c1_in_scope_of_c2__c1_insnDominates_c2: forall (ids1 : list atom)
  (F1 : fdef) (c : cmd) s m (HwfF1 : wf_fdef s m F1) (Huniq: uniqFdef F1)
  (bs_contents : ListSet.set atom)
  (c1 : cmd) (Hin : In (getCmdLoc c1) ids1) (l0 : l) (p : phinodes) (c0 : cmds)
  (t : terminator)
  (H : insnInFdefBlockB (insn_cmd c1) F1 (block_intro l0 p c0 t) = true)
  init (Heq: init = getArgsIDsOfFdef F1)
  (HInscope : ret ids1 =
       fold_left (inscope_of_block F1 l0) bs_contents
         (ret (getPhiNodesIDs p ++ cmds_dominates_cmd c0 (getCmdLoc c) ++ init)))
  (HcInB : cmdInBlockB c (block_intro l0 p c0 t) = true),
  insnDominates (getCmdLoc c1) (insn_cmd c) (block_intro l0 p c0 t).
Proof.
  intros. subst.
  assert (~ In (getCmdLoc c1) (getArgsIDsOfFdef F1)) as Hnotin.
    eapply getInsnLoc__notin__getArgsIDs'' in H; eauto.
  symmetry in HInscope.
  apply fold_left__spec in HInscope.
  destruct HInscope as [_ [_ HInscope]].
  apply HInscope in Hin. clear HInscope.
  destruct Hin as [Hin | [b1 [l1 [J1 [J2 J3]]]]].
  SSCase "1".
    simpl in HcInB. apply InCmdsB_in in HcInB.
    assert (Hin' : In (getCmdLoc c1)
          (getPhiNodesIDs p ++ cmds_dominates_cmd c0 (getCmdLoc c))).
      solve_in_list.
    clear Hin.
    assert (getCmdID c1 <> None) as foo.
      eapply In_cmds_dominates_cmd_fdef__getCmdID_eq_getCmdLoc
        with (id0:=getCmdLoc c) in H; eauto.
        congruence.
    eapply cmds_dominates_cmd__insnDominates; eauto.

  SSCase "2".
    destruct b1.
    assert (l1 = l5) as EQ.
      apply lookupBlockViaLabelFromFdef_inv in J2; auto.
      destruct J2; auto.
    subst.
    eapply lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef in J2;
      eauto.
    assert (getCmdID c1 <> None) as foo.
      eapply lookupInsnViaIDFromFdef_lookupBlockViaIDFromFdef__getInsnID
        with (insn1:=insn_cmd c1) in J3; eauto.
        simpl in J3. congruence.

        simpl in H. bdestruct H as H1 H2.
        eapply IngetCmdsIDs__lookupCmdViaIDFromFdef; eauto.
          solve_in_list.
    eapply insnInFdefBlockB__lookupBlockViaIDFromFdef in H; eauto.
    simpl in H. rewrite H in J2. inv J2.
    apply ListSet.set_diff_elim2 in J1. contradict J1; simpl; auto.
Qed.

Lemma l1_strict_in_scope_of_l2__l1_blockDominates_l2: forall (ids1 : list atom)
  (F1 : fdef) (l3 : l) (ps1 : phinodes) (cs : list cmd) (tmn1 : terminator)
  (c : cmd) (HBinF1 : blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true) s m
  (HwfF1 : wf_fdef s m F1) (Huniq: uniqFdef F1) (bs_contents : ListSet.set atom)
  (bs_bound : incl bs_contents (bound_fdef F1)) (c1 : cmd)
  (Hin : In (getCmdLoc c1) ids1) (l0 : l) (p : phinodes) (c0 : cmds)
  (t : terminator)
  (H0 : insnInFdefBlockB (insn_cmd c1) F1 (block_intro l0 p c0 t) = true)
  (HeqR : {| DomDS.L.bs_contents := bs_contents;
             DomDS.L.bs_bound := bs_bound |} = (dom_analyze F1) !! l3)
  init (Heq: init = getArgsIDsOfFdef F1)
  (HInscope : ret ids1 =
              fold_left (inscope_of_block F1 l3) bs_contents
                 (ret (getPhiNodesIDs ps1 ++
                    cmds_dominates_cmd cs (getCmdLoc c) ++ init)))
  (Hneq : l0 <> l3),
  In l0 bs_contents.
Proof.
  intros. subst.
  assert (~ In (getCmdLoc c1) (getArgsIDsOfFdef F1)) as Hnotin.
    eapply getInsnLoc__notin__getArgsIDs'' in H0; eauto.
  symmetry in HInscope.
  apply fold_left__spec in HInscope.
  destruct HInscope as [_ [_ HInscope]].
  apply HInscope in Hin.
  destruct Hin as [Hid1 | [b1 [l1 [J1 [J2 J3]]]]].
    assert (Hin' : In (getCmdLoc c1)
        (getPhiNodesIDs ps1 ++ cmds_dominates_cmd cs (getCmdLoc c))).
      solve_in_list.
    clear - HBinF1 H0 Hneq Huniq Hin'.
    apply InGetBlockIDs__lookupBlockViaIDFromFdef with (i0:=getCmdLoc c1)
      in HBinF1; auto.
      assert (getCmdID c1 <> None) as foo.
        assert (block_intro l0 p c0 t = block_intro l3 ps1 cs tmn1) as EQ.
          eapply insnInFdefBlockB__lookupBlockViaIDFromFdef__eq; eauto.
        inv EQ.
        eapply In_cmds_dominates_cmd_fdef__getCmdID_eq_getCmdLoc
          with (id0:=getCmdLoc c) in H0; eauto.
      apply insnInFdefBlockB__lookupBlockViaIDFromFdef in H0; auto.
      simpl in H0. rewrite H0 in HBinF1. inv HBinF1. congruence.
      simpl.
      eapply cmds_dominates_cmd_spec' with (id0:=getCmdLoc c); eauto.

    destruct b1.
    assert (l1 = l5) as EQ.
      apply lookupBlockViaLabelFromFdef_inv in J2; auto.
      destruct J2; auto.
    subst.
    eapply lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef in J2;
      eauto.
    assert (getCmdID c1 <> None) as foo.
      eapply lookupInsnViaIDFromFdef_lookupBlockViaIDFromFdef__getInsnID
        with (insn1:=insn_cmd c1) in J2; eauto.
        simpl in J2. congruence.

        simpl in H0. bdestruct H0 as H1 H2.
        eapply IngetCmdsIDs__lookupCmdViaIDFromFdef; eauto.
          solve_in_list.
    eapply insnInFdefBlockB__lookupBlockViaIDFromFdef in H0; eauto.
    simpl in H0. rewrite H0 in J2. inv J2.
    apply ListSet.set_diff_elim1 in J1; auto.
Qed.

Lemma cmd_doesnt_use_nondom_operands: forall (ids1 : list atom)
  (F1 : fdef) (B1 : block) (l3 : l) (ps1 : phinodes) (cs : list cmd)
  (tmn1 : terminator) (c : cmd) (HinCs : In c cs)
  (Hreach : isReachableFromEntry F1 (block_intro l3 ps1 cs tmn1))
  (HBinF1 : blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true)
  (HBinF2 : blockInFdefB B1 F1 = true)
  s m (HwfF1 : wf_fdef s m F1) (Huniq: uniqFdef F1)
  (HcInB : cmdInBlockB c B1 = true)
  (HInscope : ret ids1 = inscope_of_id F1 B1 (getCmdLoc c))
  (c1 : cmd) (Hin : In (getCmdLoc c1) ids1)
  (b1 : block) (id_list : list id)
  (H : insnInFdefBlockB (insn_cmd c1) F1 b1 = true)
  (H2 : wf_operand_list
          (List.map (fun id_ : id => (F1, b1, insn_cmd c1, id_)) id_list))
  (H1 : getInsnOperands (insn_cmd c1) = id_list)
  (Hreach' : isReachableFromEntry F1 b1),
  ~ In (getCmdLoc c) (getCmdOperands c1).
Proof.
  intros.
  destruct (in_dec id_dec (getCmdLoc c) (getCmdOperands c1)); auto.
  assert (exists n, nth_error id_list n = Some (getCmdLoc c)) as Hnth.
    eapply getCmdOperands__nth_list_id; eauto.
  destruct Hnth as [n' Hnth].
  eapply wf_operand_list__wf_operand in Hnth; eauto.
  inv Hnth.
  match goal with
  | H10: (exists _:_, _) \/ In _ (getArgsIDsOfFdef _) |- _ =>
     destruct H10 as [[block' [Hlk H10]] | H10]
  end.
  Case "id1 isnt args".
  destruct b1 as [l0 p c0 t].
  destruct B1 as [l1 p0 c2 t0]. simpl in HInscope.
  assert (~ In (getCmdLoc c) (getPhiNodesIDs p0)) as Hnotin.
    apply uniqFdef__uniqBlockLocs in HBinF2; auto.
    simpl in HBinF2.
    eapply NoDup_disjoint in HBinF2; eauto.
    simpl in HcInB. solve_in_list.
  rewrite init_scope_spec1 in HInscope; auto.
  remember ((dom_analyze F1) !! l1) as R.
  destruct R.
  assert (block' = block_intro l3 ps1 cs tmn1) as RQ.
    symmetry.
    eapply lookupBlockViaIDFromFdef__lookupBlockViaLabelFromFdef__eq; eauto.
      symmetry.
      apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
      simpl. apply in_or_app. right.  apply in_or_app.
      left. apply getCmdLoc_in_getCmdsLocs; eauto.
  subst.
  match goal with
  | H7: _ \/ _ \/ _ |- _ =>
    destruct H7 as [H7 | [H7 | H7]]; auto
  end.
  SCase "1".
    assert (block_intro l1 p0 c2 t0 = block_intro l0 p c0 t) as EQ.
      apply insnInFdefBlockB__blockInFdefB in H0.
      eapply cmdInBlockB_eqBlock with (c:=c); eauto.
      match goal with
      | H7: insnDominates _ _ _ |- _ =>
        eapply insnDominates_spec5 in H7; eauto
      end.
      uniq_result. simpl; apply In_InCmdsB; auto.
    inv EQ.
    assert (insnDominates (getCmdLoc c1) (insn_cmd c) (block_intro l0 p c0 t))
      as Hdom.
      clear - Hin HInscope HcInB H HwfF1 Huniq. destruct F1 as [[]].
      eapply c1_in_scope_of_c2__c1_insnDominates_c2 in HInscope; eauto.
    apply insnDominates_spec2 in Hdom; try solve [simpl; auto].
      eapply uniqFdef__uniqBlockLocs; eauto.
      eapply insnDominates_spec5 in Hdom; eauto.
      apply insnInFdefBlockB__insnInBlockB in H; auto.

  SCase "2".
    assert (block_intro l1 p0 c2 t0 = block_intro l3 ps1 cs tmn1) as EQ.
      apply In_InCmdsB in HinCs.
      eapply cmdInBlockB_eqBlock; eauto.
    inv EQ.
    assert (l0 <> l3) as Hneq.
      match goal with
      | H6: blockStrictDominates _ _ _ |- _ => simpl in H6 end.
      remember ((dom_analyze F1) !! l0) as R.
      destruct R.
      simpl in Hreach'. apply insnInFdefBlockB__blockInFdefB in H.
      eapply sdom_isnt_refl with (l':=l3) in Hreach'; eauto.
        rewrite <- HeqR0. simpl. auto.

    assert (In l0 bs_contents) as Hindom'.
      clear - H0 HeqR HInscope Hin Hneq HBinF1 HwfF1 Huniq. destruct F1 as [[]].
      eapply l1_strict_in_scope_of_l2__l1_blockDominates_l2 in HInscope; eauto.

    assert (In l3 (DomDS.L.bs_contents (bound_fdef F1)
           ((dom_analyze F1) !! l0))) as Hindom.
      match goal with
      | H6: blockStrictDominates _ _ _ |- _ =>
        clear - H6; unfold blockStrictDominates in H6
      end.
      destruct ((dom_analyze F1) !! l0). simpl. auto.
    apply insnInFdefBlockB__blockInFdefB in H0.
    eapply adom_acyclic in Hindom; eauto.
    rewrite <- HeqR. simpl. auto.
  Case "id1 is args".
    contradict H6.
    replace (getCmdLoc c) with (getInsnLoc (insn_cmd c)); auto.
    eapply getInsnLoc__notin__getArgsIDs'' with (b:=B1); eauto 1.
      solve_insnInFdefBlockB.
Qed.

Lemma incoming_value__in_scope: forall (f : fdef) (l0 : l)
  (t : list atom) (l1 : l) (ps1 : phinodes) (cs1 : cmds) (tmn1 : terminator)
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (HuniqF : uniqFdef f) (ps' : phinodes) (cs' : cmds) (tmn' : terminator)
  (i0 : id) (l2 : list (value * l))
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true) t0
  (H7 : wf_phinode f (block_intro l0 ps' cs' tmn') (insn_phi i0 t0 l2))
  (vid : id)
  (J : getValueViaLabelFromValuels l2 l1 = ret value_id vid),
  In vid t.
Proof.
  intros.
  destruct H7 as [Hwfops Hwfvls].
  assert (Hnth:=J).
  eapply getValueViaLabelFromValuels__nth_list_value_l in Hnth; eauto.
  destruct Hnth as [n Hnth].
  eapply wf_phi_operands__elim in Hwfops; eauto.
  destruct Hwfops as [b1 [Hlkb1 [[vb [Hlkvb Hdom]] | HinArgs]]].
  Case "isnt args".
  assert (b1 = block_intro l1 ps1 cs1 tmn1)
    as EQ.
    clear - Hlkb1 HbInF HuniqF.
    apply blockInFdefB_lookupBlockViaLabelFromFdef in HbInF; auto.
    rewrite HbInF in Hlkb1. inv Hlkb1; auto.

  subst.
  clear - Hdom HeqR J Hreach HbInF Hlkvb Hlkb1 HuniqF.
  destruct Hdom as [J3 | J3]; try solve [contradict Hreach; auto].
  clear Hreach.
  unfold blockDominates in J3.
  destruct vb.
  unfold inscope_of_tmn in HeqR.
  destruct f as [[fa ty fid la va] bs].
  remember ((dom_analyze
    (fdef_intro (fheader_intro fa ty fid la va) bs)) !! l1) as R1.
  destruct R1.
  symmetry in HeqR.
  apply fold_left__spec in HeqR.
  destruct (eq_atom_dec l5 l1); subst.
  SCase "l5=l1".
    destruct HeqR as [HeqR _].
    clear - J HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
    assert (J':=Hlkvb).
    apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
    apply lookupBlockViaLabelFromFdef_inv in Hlkb1; auto.
    destruct Hlkb1 as [J1 J2].
    eapply blockInFdefB_uniq in J2; eauto.
    destruct J2 as [J2 [J4 J5]]; subst.
    apply lookupBlockViaIDFromFdef__InGetBlockIDs in J'.
    simpl in J'.
    apply HeqR; auto. solve_in_list.

  SCase "l5<>l1".
    destruct J3 as [J3 | Heq]; subst; try congruence.
    assert (In l5 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as G.
      apply ListSet.set_diff_intro; auto.
        simpl. intro JJ. destruct JJ as [JJ | JJ]; auto.
    assert (
      lookupBlockViaLabelFromFdef (fdef_intro (fheader_intro fa ty fid la va) bs)
        l5 = ret block_intro l5 phinodes5 cmds5 terminator5) as J1.
      clear - Hlkvb HuniqF.
      apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
      apply blockInFdefB_lookupBlockViaLabelFromFdef in Hlkvb; auto.
    destruct HeqR as [_ [HeqR _]].
    apply HeqR in J1; auto.
      clear - J1 HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
      apply J1.
      apply lookupBlockViaIDFromFdef__InGetBlockIDs in Hlkvb; auto.
  Case "is args".
    eapply in_getArgsIDsOfFdef__inscope_of_tmn; eauto.
Qed.

Lemma inscope_of_block_inscope_of_block__inscope_of_block: forall (f : fdef)
  (t : list atom) (l1 : l) (ps1 : phinodes) (cs1 : cmds) s m
  (tmn1 : terminator) id1 (id2 : id) (HwfF : wf_fdef s m f)
  (bs_contents : ListSet.set atom) (Huniq: uniqFdef f)
  (bs_bound : incl bs_contents (bound_fdef f))
  (HeqR3 : {| DomDS.L.bs_contents := bs_contents;
              DomDS.L.bs_bound := bs_bound |} = (dom_analyze f) !! l1)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (l2 : l) (p : phinodes) (c2 : cmds) (t0 : terminator)
  (HeqR1 : ret block_intro l2 p c2 t0 = lookupBlockViaIDFromFdef f id2)
  (bs_contents0 : ListSet.set atom)
  (bs_bound0 : incl bs_contents0 (bound_fdef f))
  (HeqR4 : {| DomDS.L.bs_contents := bs_contents0;
              DomDS.L.bs_bound := bs_bound0 |} = (dom_analyze f) !! l2)
  (b1 : block) (l1' : atom)
  (J10 : In l1' (ListSet.set_diff eq_atom_dec bs_contents0 [l2]))
  (J11 : lookupBlockViaLabelFromFdef f l1' = ret b1)
  (J11' : In id1 (getBlockIDs b1)) (b2 : block) (l2' : atom)
  (J13 : In l2' (ListSet.set_diff eq_atom_dec bs_contents [l1]))
  (J14 : lookupBlockViaLabelFromFdef f l2' = ret b2)
  (J15 : In id2 (getBlockIDs b2)) init
  (HeqR' : fold_left (inscope_of_block f l1) bs_contents (ret init) = ret t),
  In id1 t.
Proof.
  intros.
  assert (block_intro l2 p c2 t0 = b2) as EQ.
    clear - Huniq HeqR1 J14 J15.
    apply lookupBlockViaLabelFromFdef__blockInFdefB in J14; auto.
    eapply block_eq1 with (id0:=id2); eauto.
  subst.
  apply lookupBlockViaLabelFromFdef_inv in J14; auto.
  destruct J14 as [Heq J14]; subst.
  destruct b1 as [l3 p0 c3 t1].
  apply lookupBlockViaLabelFromFdef_inv in J11; auto.
  destruct J11 as [Heq J11]; subst.
  assert (blockStrictDominates f (block_intro l3 p0 c3 t1)
                                 (block_intro l2 p c2 t0)) as Hdom.
    clear - J10 HeqR4 HwfF. simpl. rewrite <- HeqR4.
    apply ListSet.set_diff_elim1 in J10; auto.
  assert (blockStrictDominates f (block_intro l2 p c2 t0)
                (block_intro l1 ps1 cs1 tmn1)) as Hdom'.
    clear - J13 HeqR3 HwfF. simpl. rewrite <- HeqR3.
    apply ListSet.set_diff_elim1 in J13; auto.
  assert (blockStrictDominates f (block_intro l3 p0 c3 t1)
                (block_intro l1 ps1 cs1 tmn1)) as Hdom''.
    eapply blockStrictDominates_trans; eauto.
  destruct (l_dec l3 l1); subst.
    assert (block_intro l1 p0 c3 t1 =
            block_intro l1 ps1 cs1 tmn1) as EQ.
      clear - HbInF J11 Huniq.
      eapply blockInFdefB_uniq in HbInF; eauto.
      destruct HbInF as [Heq1 [Heq2 Heq3]]; subst. auto.
    inv EQ.
    eapply blockStrictDominates_isnt_refl in Hreach;
      try solve [eauto | contradict Hdom''; auto].

    simpl in Hdom''. rewrite <- HeqR3 in Hdom''.
    apply fold_left__intro with (l2:=l3)(B:=block_intro l3 p0 c3 t1)
      in HeqR'; auto.
      apply ListSet.set_diff_intro; auto.
         intro J. simpl in J. destruct J; auto.
      clear - J11 Huniq.
      eapply blockInFdefB_lookupBlockViaLabelFromFdef; eauto.
Qed.

Lemma idDominates_inscope_of_cmd__inscope_of_cmd: forall (f : fdef)
  (t : list atom) (l1 : l) (ps1 : phinodes) (cs1 : cmds) (cs : cmds) s m
  (tmn1 : terminator) id1 (instr1 : insn)
  (c : cmd) (id2 : id) (HwfF : wf_fdef s m f)
  (HeqR : inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn1) c =
          ret t) (Huniq: uniqFdef f)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn1))
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs) tmn1) f = true)
  (J1 : idDominates f id1 id2)
  (J2 : lookupInsnViaIDFromFdef f id1 = ret instr1)
  instr0
  (HeqR0 : ret instr0 = lookupInsnViaIDFromFdef f id2)
  (Hid2InScope : In id2 t),
  In id1 t.
Proof.
  intros.
  unfold inscope_of_cmd, inscope_of_id in HeqR.
  unfold idDominates in J1.
  remember (lookupBlockViaIDFromFdef f id2) as R.
  destruct R; tinv J1.
  remember (inscope_of_id f b id2) as R.
  destruct R; tinv J1.
  unfold inscope_of_id in HeqR2.
  destruct b. destruct f as [[fa ty fid la va] bs].
  remember ((dom_analyze
    (fdef_intro (fheader_intro fa ty fid la va) bs)) !! l1) as R1.
  remember ((dom_analyze
    (fdef_intro (fheader_intro fa ty fid la va) bs)) !! l5) as R2.
  destruct R1, R2.

  assert (~ In (getCmdLoc c) (getPhiNodesIDs ps1)) as Hnotin.
    apply uniqFdef__uniqBlockLocs in HbInF; auto.
    simpl in HbInF.
    eapply NoDup_disjoint in HbInF; eauto.
    solve_in_list.
  rewrite init_scope_spec1 in HeqR; auto.

  assert (HeqR':=HeqR).
  apply fold_left__spec in HeqR.
  symmetry in HeqR2.
  assert (HeqR2':=HeqR2).
  apply fold_left__spec in HeqR2.
  destruct HeqR as [J4 [J5 J6]].
  destruct HeqR2 as [J7 [J8 J9]].
  apply J6 in Hid2InScope.
  apply J9 in J1.

  assert (~ In id2 (getArgsIDs la)) as Hnotin1.
    clear - HeqR0 Huniq.
    eapply getInsnLoc__notin__getArgsIDs' in Huniq; eauto.
  assert (~ In id1 (getArgsIDs la)) as Hnotin2.
    clear - J2 Huniq.
    eapply getInsnLoc__notin__getArgsIDs' in Huniq; eauto.
  destruct J1 as [J1 | [b1 [l1' [J10 [J11 J11']]]]].
  Case "1".
    destruct Hid2InScope as [J12 | [b2 [l2' [J13 [J14 J15]]]]].
    SCase "1.1".
      eapply cmds_dominates_cmd_inscope_of_cmd__inscope_of_cmd in HeqR'; eauto.
        solve_in_list.
    SCase "1.2".
      clear - Huniq HeqR1 J14 J15 J1 HeqR' J13 Hnotin2.
      apply init_scope_spec2 in J1; auto.
      eapply cmds_dominates_cmd_inscope_of_block__inscope_of_block; eauto.
        solve_in_list.
  Case "2".
    destruct Hid2InScope as [J12 | [b2 [l2' [J13 [J14 J15]]]]].
    SCase "2.1".
      clear - HeqR1 HbInF Huniq HeqR' J12 J10 J11 J11' HeqR3 HeqR4 Hnotin1.
      eapply inscope_of_block_cmds_dominates_cmd__inscope_of_cmd
        with (bs_bound:=bs_bound); eauto.
        solve_in_list.
   SCase "2.2".
      clear - HwfF HeqR1 J14 J15 J11 J13 HeqR4 HeqR3 J10 Hreach HbInF HeqR' J11' Huniq.
      eapply inscope_of_block_inscope_of_block__inscope_of_block
        with (bs_bound:=bs_bound); eauto.
Qed.

Lemma idDominates_inscope_of_tmn__inscope_of_tmn: forall (f : fdef)
  (t : list atom) (l1 : l) (ps1 : phinodes) (cs1 : cmds) s m
  (tmn1 : terminator) id1 insn1 (id2 : id) (HwfF : wf_fdef s m f)
  (HeqR : inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1 =
          ret t) (Huniq: uniqFdef f)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (J1 : idDominates f id1 id2)
  (J2 : lookupInsnViaIDFromFdef f id1 = ret insn1)
  instr0
  (HeqR0 : ret instr0 = lookupInsnViaIDFromFdef f id2)
  (Hid2InScope : In id2 t),
  In id1 t.
Proof.
  intros.
  unfold inscope_of_tmn in HeqR.
  unfold idDominates in J1.
  remember (lookupBlockViaIDFromFdef f id2) as R.
  destruct R; tinv J1.
  remember (inscope_of_id f b id2) as R.
  destruct R; tinv J1.
  unfold inscope_of_id in HeqR2.
  destruct b. destruct f as [[fa ty fid la va] bs].
  remember ((dom_analyze
    (fdef_intro (fheader_intro fa ty fid la va) bs)) !! l1) as R1.
  remember ((dom_analyze
    (fdef_intro (fheader_intro fa ty fid la va) bs)) !! l5) as R2.
  destruct R1, R2.
  assert (HeqR':=HeqR).
  apply fold_left__spec in HeqR.
  symmetry in HeqR2.
  assert (HeqR2':=HeqR2).
  apply fold_left__spec in HeqR2.
  destruct HeqR as [J4 [J5 J6]].
  destruct HeqR2 as [J7 [J8 J9]].
  apply J6 in Hid2InScope.
  apply J9 in J1.
  assert (~ In id2 (getArgsIDs la)) as Hnotin1.
    clear - HeqR0 Huniq.
    eapply getInsnLoc__notin__getArgsIDs' in Huniq; eauto.
  assert (~ In id1 (getArgsIDs la)) as Hnotin2.
    clear - J2 Huniq.
    eapply getInsnLoc__notin__getArgsIDs' in Huniq; eauto.
  destruct J1 as [J1 | [b1 [l1' [J10 [J11 J11']]]]].
  Case "1".
    apply init_scope_spec2 in J1; auto.
    destruct Hid2InScope as [J12 | [b2 [l2' [J13 [J14 J15]]]]].
    SCase "1.1".
      eapply cmds_dominates_cmd_inscope_of_tmn__inscope_of_tmn; eauto.
        solve_in_list. solve_in_list.
    SCase "1.2".
      eapply cmds_dominates_cmd_inscope_of_block__inscope_of_block; eauto.
        solve_in_list.
  Case "2".
    destruct Hid2InScope as [J12 | [b2 [l2' [J13 [J14 J15]]]]].
    SCase "2.1".
      eapply inscope_of_block_cmds_dominates_cmd__inscope_of_tmn
        with (bs_contents:=bs_contents); eauto.
        solve_in_list.
    SCase "2.2".
      eapply inscope_of_block_inscope_of_block__inscope_of_block
        with (bs_contents:=bs_contents); eauto.
Qed.

Lemma make_list_fdef_block_insn_id_spec:
  forall id1 (f : fdef) (b : block) (instr : insn) id_list,
  In id1 (id_list) ->
  In (f, b, instr, id1)
     (List.map
       (fun id_ : id =>
         (f, b, instr, id_))
       id_list).
Proof.
  induction id_list; simpl; intros; auto.
    destruct H as [H | H]; subst; auto.
Qed.

Lemma cmd_operands__in_scope': forall (S : system) (m : module) c b f
  (HwfF : wf_fdef S m f) (Huniq : uniqFdef f) (Hreach : isReachableFromEntry f b)
  (HBinF: blockInFdefB b f = true) (HCinB: cmdInBlockB c b = true) id0
  (Heq: getCmdLoc c = id0) (l0 : list atom)
  (HeqR : ret l0 = inscope_of_id f b id0) id1 (Hin: In id1 (getCmdOperands c)),
  In id1 l0.
Proof.
  intros.
  destruct b.
  assert (HBinF':=HBinF).
  apply IngetCmdsIDs__lookupCmdViaIDFromFdef with
    (c1:=c) in HBinF; try solve [auto | solve_in_list].
  eapply wf_fdef__wf_insn_base in HBinF; eauto.
  destruct HBinF as [b1 Hwfi].
  inv Hwfi.
  match goal with
  | _: _ = inscope_of_id _ ?b _ |- _ =>
    assert (b1 = b) as HeqB
  end.
    eapply block_eq2 with (id1:=getCmdLoc c); try solve [
      eauto 1 | solve_blockInFdefB
      ].
    apply insnInFdefBlockB__insnInBlockB in H.
    simpl in H.
    apply cmdInBlockB__inGetBlockLocs in H; auto.

    simpl. apply in_or_app. right. apply in_or_app. left.
    solve_in_list.

  subst.
  match goal with
  | [ _ : _ = inscope_of_id _ ?b _,
      f : fdef,
      c : cmd |- _ ] =>
      assert (wf_operand_list 
        (List.map (fun i => (f, b, (insn_cmd c), i))
          (getInsnOperands (insn_cmd c)))) as H6';
      try solve [solve_wf_operand]
  end.

  match goal with
  | _ : _ = inscope_of_id _ ?b _ |- _ =>
  apply wf_operand_list__elim with (f1:=f)(b1:=b)
    (insn1:=insn_cmd c) (id1:=id1)
    in H6'; try solve [
      auto |
      apply make_list_fdef_block_insn_id_spec; try solve
        [match goal with
         | EQ: ?A = ?B |- In _ ?B => rewrite <- EQ; simpl; auto
         end]
      ]
  end.

  eapply cmd_operands__in_scope; eauto; simpl; auto.
    solve_NoDup.
  apply make_list_fdef_block_insn_id_spec.
  simpl. auto.
Qed.

Lemma terminator_operands__in_scope': forall (S : system) (m : module) l0 ps0 cs0
  t0 f (HwfF : wf_fdef S m f) (Huniq : uniqFdef f)
  (Hreach : isReachableFromEntry f (block_intro l0 ps0 cs0 t0))
  (HBinF: blockInFdefB (block_intro l0 ps0 cs0 t0) f = true)
  (l1 : list atom)
  (HeqR : ret l1 = inscope_of_tmn f (block_intro l0 ps0 cs0 t0) t0) id1
  (Hin: In id1 (getTerminatorOperands t0)),
  In id1 l1.
Proof.
  intros.
  assert (HBinF':=HBinF).
  apply IngetTmnID__lookupTmnViaIDFromFdef in HBinF;
    try solve [auto | solve_in_list].
  eapply wf_fdef__wf_insn_base' in HBinF; try solve [eauto | intro J; inv J].
  destruct HBinF as [b1 Hwfi].
  inv Hwfi.
  match goal with
  | _: _ = inscope_of_tmn _ ?b _ |- _ =>
    assert (b1 = b) as HeqB
  end.
    eapply block_eq2 with (id1:=getTerminatorID t0); try solve [
      eauto 1 | solve_blockInFdefB
      ].
    apply insnInFdefBlockB__insnInBlockB in H.
    simpl in H.
    destruct b1. simpl in H.
    apply terminatorEqB_inv in H. subst.
    simpl. solve_in_list.

    simpl. solve_in_list.

  subst.
  match goal with
  | [ _ : _ = inscope_of_tmn _ ?b _,
      f : fdef,
      t : terminator |- _ ] =>
      assert (wf_operand_list 
        (List.map (fun i => (f, b, (insn_terminator t), i))
          (getInsnOperands (insn_terminator t)))) as H6';
      try solve [solve_wf_operand]
  end.

  match goal with
  | _: _ = inscope_of_tmn _ ?b _ |- _ =>
  apply wf_operand_list__elim with (f1:=f)(b1:=b)
    (insn1:=insn_terminator t0) (id1:=id1)
    in H6'; try solve [
      auto |
      apply make_list_fdef_block_insn_id_spec; try solve
        [match goal with
         | EQ: ?A = ?B |- In _ ?B => rewrite <- EQ; simpl; auto
         end]
      ]
  end.
  eapply terminator_operands__in_scope; eauto; simpl; auto.
  apply make_list_fdef_block_insn_id_spec. simpl. auto.
Qed.

Lemma idDominates_acyclic: forall s m f (HwfF:wf_fdef s m f)
  (HuniqF: uniqFdef f) id1 id2
  (Hdom1: idDominates f id1 id2) (Hdom2: idDominates f id2 id1)
  (Hreach: (forall b, lookupBlockViaIDFromFdef f id1 = Some b ->
                      isReachableFromEntry f b)),
  False.
Proof.
  unfold idDominates, inscope_of_id.
  intros.
  inv_mbind.
  symmetry_ctx.
  assert (isReachableFromEntry f b) as Hreachable by auto.
  clear Hreach.
  assert (blockInFdefB b0 f = true) as HBinF0.
    solve_blockInFdefB.
  assert (blockInFdefB b f = true) as HBinF1.
    solve_blockInFdefB.
  destruct b0 as [l2 ps2 cs2 tmn2].
  destruct b as [l3 ps3 cs3 tmn3].
  remember ((dom_analyze f) !! l2) as R2.
  remember ((dom_analyze f) !! l3) as R3.
  destruct R2, R3.
  apply fold_left__spec in HeqR2.
  apply fold_left__spec in HeqR0.
  destruct HeqR2 as [_ [_ HeqR2]].
  destruct HeqR0 as [_ [_ HeqR0]].
  apply_clear HeqR2 in Hdom1.
  apply_clear HeqR0 in Hdom2.
  assert (~ In id1 (getArgsIDsOfFdef f)) as Hnotin1.
    solve_notin_getArgsIDs.
  assert (~ In id2 (getArgsIDsOfFdef f)) as Hnotin2.
    solve_notin_getArgsIDs.
  assert (In id2 (getBlockLocs (block_intro l2 ps2 cs2 tmn2))) as Hin9.
    solve_in_list.
  assert (In id1 (getBlockLocs (block_intro l3 ps3 cs3 tmn3))) as Hin10.
    solve_in_list.
  destruct Hdom1 as [Hdom1 | [b1 [a1 [J1 [J2 J3]]]]].
  Case "local".
      unfold init_scope in Hdom1.
      destruct_if; try tauto.
      assert (block_intro l2 ps2 cs2 tmn2 =
                block_intro l3 ps3 cs3 tmn3) as EQ.
        eapply block_eq2 with (id1:=id1); eauto.
         simpl.
         solve_in_list.
         apply cmds_dominates_cmd_spec in Hdom1.
         solve_in_list.
      inv EQ.
      destruct Hdom2 as [Hdom2 | [b2 [a2 [J4 [J5 J6]]]]].
      SCase "local".
        unfold init_scope in Hdom2.
        destruct_if; try tauto.
        assert (NoDup (getCmdsLocs cs3)) as Hnodup.
          solve_NoDup.
        assert (In id2 (cmds_dominates_cmd cs3 id1)) as Hin2.
          apply in_app_or in Hdom2.
          destruct Hdom2 as [Hdom2 | Hdom2]; try solve [contradict Hdom2; auto].
          apply in_app_or in Hdom2.
          destruct Hdom2 as [Hdom2 | Hdom2]; try solve [contradict Hdom2; auto].
          auto.
        assert (In id1 (cmds_dominates_cmd cs3 id2)) as Hin1.
          apply in_app_or in Hdom1.
          destruct Hdom1 as [Hdom1 | Hdom1]; try solve [contradict Hdom1; auto].
          apply in_app_or in Hdom1.
          destruct Hdom1 as [Hdom1 | Hdom1]; try solve [contradict Hdom1; auto].
          auto.
        assert (In id1 (getCmdsLocs cs3) /\ In id2 (getCmdsLocs cs3)) as Hin.
          apply cmds_dominates_cmd_spec in Hin2.
          apply cmds_dominates_cmd_spec in Hin1.
          split; solve_in_list.
        destruct Hin as [Hin3 Hin4].
        eapply cmds_dominates_cmd_acyclic; eauto.
      SCase "remote".
        assert (b2 = block_intro l3 ps3 cs3 tmn3) as EQ.
          eapply block_eq2 with (id1:=id2); eauto 1.
            solve_blockInFdefB.
            solve_in_list.
        subst.
        apply lookupBlockViaLabelFromFdef_inv in J5; auto.
        destruct J5; subst.
        apply ListSet.set_diff_elim2 in J4; auto.
        simpl in J4. auto.
  Case "remote".
      assert (b1 = block_intro l3 ps3 cs3 tmn3) as EQ.
        eapply block_eq2 with (id1:=id1); eauto 1.
          solve_blockInFdefB.
          solve_in_list.
      subst.
      apply lookupBlockViaLabelFromFdef_inv in J2; auto.
      destruct J2; subst.
      destruct Hdom2 as [Hdom2 | [b2 [a2 [J4 [J5 J6]]]]].
      SCase "local".
        unfold init_scope in Hdom2.
        destruct_if; try tauto.
        assert (block_intro l2 ps2 cs2 tmn2 =
                  block_intro l3 ps3 cs3 tmn3) as EQ.
          eapply block_eq2 with (id1:=id2); eauto 1.
            simpl.
            solve_in_list.
            apply cmds_dominates_cmd_spec in Hdom2.
            solve_in_list.
        inv EQ.
        apply ListSet.set_diff_elim2 in J1; auto.
        simpl in J1. auto.
      SCase "remote".
        assert (b2 = block_intro l2 ps2 cs2 tmn2) as EQ.
          eapply block_eq2 with (id1:=id2); eauto 1.
            solve_blockInFdefB.
            solve_in_list.
        subst.
        apply lookupBlockViaLabelFromFdef_inv in J5; auto.
        destruct J5; subst.
        assert (l2 <> l3) as Hneq.
          intro J. subst.
          apply ListSet.set_diff_elim2 in J4; auto.
          simpl in J4. auto.
        eapply adom_acyclic in Hneq; eauto 1.
          rewrite <- HeqR4. simpl.
          apply ListSet.set_diff_elim1 in J4; auto.

          rewrite <- HeqR3. simpl.
          apply ListSet.set_diff_elim1 in J1; auto.
Qed.

Lemma any_cmd_doesnt_use_following_operands: forall
  (F1 : fdef) (l3 : l) (ps1 : phinodes) (cs : list cmd)
  (tmn1 : terminator) (c : cmd)
  (Hreach : isReachableFromEntry F1 (block_intro l3 ps1 cs tmn1))
  (HBinF1 : blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true)
  s m (HwfF1 : wf_fdef s m F1) (Huniq: uniqFdef F1)
  (c1 : cmd) cs1 cs2 cs3
  (Hfollow: cs = cs1 ++ c1 :: cs2 ++ c :: cs3)
  (id_list : list id)
  (H2 : wf_operand_list
          (List.map (fun id_ : id =>
            (F1, (block_intro l3 ps1 cs tmn1), insn_cmd c1, id_)) id_list))
  (H1 : getInsnOperands (insn_cmd c1) = id_list),
  ~ In (getCmdLoc c) (getCmdOperands c1).
Proof.
  intros. subst cs.
  destruct (in_dec id_dec (getCmdLoc c) (getCmdOperands c1)); auto.
  assert (exists n, nth_error id_list n = Some (getCmdLoc c)) as Hnth.
    eapply getCmdOperands__nth_list_id; eauto.
  destruct Hnth as [n' Hnth].
  eapply wf_operand_list__wf_operand in Hnth; eauto.
  inv Hnth.
  match goal with
  | H10: (exists _:_, _) \/ In _ (getArgsIDsOfFdef _) |- _ =>
     destruct H10 as [[block' [Hlk H10]] | H10]
  end.
  Case "id1 isnt args".
  assert (In (getCmdLoc c)
     (getCmdsLocs (cs1 ++ c1 :: cs2 ++ c :: cs3) ++
      getTerminatorID tmn1 :: nil)) as Hin.
    apply in_or_app. left.
    apply getCmdLoc_in_getCmdsLocs. solve_in_list.
  assert (~ In (getCmdLoc c) (getPhiNodesIDs ps1)) as Hnotin.
    apply uniqFdef__uniqBlockLocs in HBinF1; auto.
    simpl in HBinF1.
    eapply NoDup_disjoint in HBinF1; eauto.
  match goal with
  | H7: _ \/ _ \/ _ |- _ =>
    destruct H7 as [H7 | [H7 | H7]]; auto
  end.
  SCase "1".
    assert (NoDup (getBlockLocs
      (block_intro l3 ps1 (cs1 ++ c1 :: cs2 ++ c :: cs3) tmn1))) as Hnodup.
      solve_NoDup.
    elimtype False.
    eapply insnDominates_spec7; eauto.

  SCase "2".
    assert (block' = block_intro l3 ps1 (cs1 ++ c1 :: cs2 ++ c :: cs3) tmn1)
      as EQ.
      eapply block_eq2 with (id1:=getCmdLoc c); eauto 1.
        solve_blockInFdefB.
        solve_in_list.
        simpl. solve_in_list.
    subst.
    contradict H5.
    eapply blockStrictDominates_isnt_refl; eauto.
  Case "id1 is args".
    contradict H5.
    replace (getCmdLoc c) with (getInsnLoc (insn_cmd c)); auto.
    match goal with
    | H: blockInFdefB ?b1 _ = true |- _ =>
      eapply getInsnLoc__notin__getArgsIDs'' with (b:=b1); eauto 1
    end.
      apply insnInFdefBlockB_intro; auto.
      simpl. solve_in_list.
Qed.

Lemma wf_single_system__wf_uniq_fdef: forall los nts Ps1 f Ps2,
  wf_system [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] ->
  wf_fdef [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    (module_intro los nts (Ps1 ++ product_fdef f :: Ps2)) f /\
  uniqFdef f.
Proof.
  intros.
  assert (
    moduleInSystemB (module_intro los nts (Ps1 ++ product_fdef f :: Ps2))
      [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] = true) as HmInS.
    simpl. rewrite moduleEqB_refl. auto.
  assert (
    InProductsB (product_fdef f) (Ps1 ++ product_fdef f :: Ps2) = true)
    as HpInM.
    apply InProductsB_middle; auto.
  split.
    eapply wf_system__wf_fdef; eauto 1.
    eapply wf_system__uniqFdef; eauto 1.
Qed.

Lemma wf_system__uniqSystem: forall S, wf_system S -> uniqSystem S.
Proof.
  intros.
  destruct H; auto.
Qed.

Lemma wf_fdef__wf_phinodes': forall s m F l' ps' cs' tmn' l2,
  wf_fdef s m F ->
  ret block_intro l' ps' cs' tmn' = lookupBlockViaLabelFromFdef F l2 ->
  uniqFdef F ->
  wf_phinodes s m F (block_intro l' ps' cs' tmn') ps'.
Proof.
  intros.
  symmetry in H0.
  apply lookupBlockViaLabelFromFdef_inv in H0; auto.
  destruct H0 as [_ Hlkup].
  eapply wf_fdef__wf_phinodes in Hlkup; eauto.
 Qed.

Ltac get_wf_value_for_simop :=
  match goal with
  | HBinF: blockInFdefB (block_intro _ _ (_++_::_) _) _ = _ |- _ =>
    let HBinF':=fresh "HBinF'" in
    assert (HBinF':=HBinF);
    eapply wf_system__wf_cmd in HBinF'; eauto using in_middle;
    inv HBinF'; 
    match goal with
    | H: wf_trunc _ _ _ _ _ |- _ => inv H
    | H: wf_cast _ _ _ _ _ |- _ => inv H 
    | H: wf_ext _ _ _ _ _ |- _ => inv H 
    | _ => idtac
    end
  end.

Ltac get_wf_value_for_simop' :=
  match goal with
  | HBinF: blockInFdefB (block_intro _ _ (_++nil) _) _ = _ |- _ =>
    let HBinF':=fresh "HBinF'" in
    assert (HBinF':=HBinF);
    eapply wf_system__wf_tmn in HBinF'; eauto using in_middle;
    inv HBinF'
  end.

Ltac get_wf_value_for_simop_ex :=
  match goal with
  | HBinF: blockInFdefB ?B _ = _,
    Hex: exists _:_, exists _:_, exists _:_,
          ?B = (block_intro _ _ (_++_::_) _) |- _ =>
    let l1:=fresh "l1" in
    let ps1:=fresh "ps1" in
    let cs1:=fresh "cs1" in
      destruct Hex as [l1 [ps1 [cs1 Hex]]]; subst
  | _ => idtac
  end;
  match goal with
  | HBinF: blockInFdefB (block_intro _ _ (_++_::_) _) _ = _ |- _ =>
    let HBinF':=fresh "HBinF'" in
    assert (HBinF':=HBinF);
    eapply wf_system__wf_cmd in HBinF'; eauto using in_middle;
    inv HBinF'; 
    match goal with
    | H: wf_trunc _ _ _ _ _ |- _ => inv H
    | H: wf_cast _ _ _ _ _ |- _ => inv H 
    | H: wf_ext _ _ _ _ _ |- _ => inv H 
    | _ => idtac
    end
  end.
