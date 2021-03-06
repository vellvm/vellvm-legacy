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
Require Import dom_list.
Require Import analysis.
Require Import util.
Require Import datatype_base.

Import LLVMinfra.
Import LLVMtd.
Import LLVMtypings.
Import LLVMgv.
Import AtomSet.

(* This file proves the properties of typing rules. *)

(** * Inversion of well-formedness *)

Ltac inv_wf_fdef H :=
let S5 := fresh "S5" in
let los5 := fresh "los5" in
let nts5 := fresh "nts5" in
let prods5 := fresh "prods5" in
let fh5 := fresh "fh5" in
let bs5 := fresh "bs5" in
let b5 := fresh "b5" in
let HpInS := fresh "HpInS" in
let Hwffh := fresh "Hwffh" in
let Hentry := fresh "Hentry" in
let Hnpred := fresh "Hnpred" in
let Hwfb := fresh "Hwfb" in
let EQ1 := fresh "EQ1" in
let EQ2 := fresh "EQ2" in
let EQ3 := fresh "EQ3" in
inversion H as 
  [S5 los5 nts5 prods5 fh5 bs5 b5 HpInS Hwffh Hentry Hnpred
   Hwfb EQ1 EQ2 EQ3]; subst S5.

(* Properties of wf_typ *)
Lemma wf_styp__isValidElementTyp: forall S td t (Hty: wf_styp S td t),
  isValidElementTyp t.
Proof.
  intros.
  unfold isValidElementTyp, isValidElementTypB, isNotValidElementTypB.
  inv Hty; simpl; auto.
Qed.

Lemma getPointerAlignmentInfo_pos: forall los (Hwfl: wf_layouts los),
 (getPointerAlignmentInfo los true > 0)%nat.
Proof.
  intros.
  destruct (@Hwfl true); auto.
Qed.

Lemma wf_typ_pointer: forall S los nts t (Hwft: wf_typ S (los,nts) t)
  (Hwfl: wf_layouts los),
  wf_typ S (los,nts) (typ_pointer t).
Proof.
  intros. 
  inv Hwft.
  constructor; auto.
    constructor; auto.
      eapply wf_styp__isValidElementTyp; eauto.
      apply getPointerAlignmentInfo_pos; auto.
Qed.

(* Properties of wf_tmn *)
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

Lemma wf_tmn__in_successors: forall s m f l0 cs ps tmn l1
  (HuniqF : uniqFdef f)
  (Hwftmn : wf_insn s m f (l0, stmts_intro cs ps tmn) (insn_terminator tmn))
  (Hin : In l1 (successors_terminator tmn)),
  exists s1, blockInFdefB (l1, s1) f.
Proof.
  intros.
  inv Hwftmn; simpl in Hin; tinv Hin.
    destruct Hin as [Hin | [Hin | Hin]]; tinv Hin; subst.
      apply lookupBlockViaLabelFromFdef_inv in H2; eauto.
      apply lookupBlockViaLabelFromFdef_inv in H3; eauto.

    destruct Hin as [Hin | Hin]; tinv Hin; subst.
      apply lookupBlockViaLabelFromFdef_inv in H0; eauto.
Qed.

(* Properties of wf_blocks *)
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

(* Properties of wf_cmds *)
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

Lemma wf_cmds_intro: forall s m f b cs,
  (forall c, In c cs -> wf_insn s m f b (insn_cmd c)) ->
  wf_cmds s m f b cs.
Proof.
  induction cs; intros.
    constructor.
    constructor.
      apply H; simpl; auto.
      apply IHcs. intros. apply H; simpl; auto.
Qed.

Lemma wf_cmds_elim: forall s m f b cs,
  wf_cmds s m f b cs -> forall c, In c cs -> wf_insn s m f b (insn_cmd c).
Proof.
  intros s m f b cs J.
  induction J; intros.
    inv H.

    simpl in H0.
    destruct H0 as [H0 | H0]; subst; auto.
Qed.

Lemma wf_cmds_app: forall s m f b cs2 (Hwfcs2: wf_cmds s m f b cs2) cs1
  (Hwfcs1: wf_cmds s m f b cs1), wf_cmds s m f b (cs1++cs2).
Proof.
  induction cs1; simpl; intros; auto.
    inv Hwfcs1. constructor; auto.
Qed.

(* Properties of wf_modules *)
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

(* Properties of wf_prods *)
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

Lemma wf_prods_elim: forall (prod:product) S md prods 
  (Hwfps: wf_prods S md prods) (Hin: In prod prods), 
  wf_prod S md prod.
Proof.
  induction 1; intros; try tauto.
    destruct_in Hin; auto.
Qed.    

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

(* Properties of wf_system *)
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

Lemma wf_system__lookup__wf_block : forall sts0 f l0 ps los nts s,
  Some sts0 = lookupBlockViaLabelFromFdef f l0 ->
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system s ->
  wf_block s (module_intro los nts ps) f (l0, sts0).
Proof.
  intros.
  eapply wf_system__blockInFdefB__wf_block; eauto 1.
    symmetry in H. 
    assert (uniqFdef f) as J. eapply wf_system__uniqFdef; eauto.
    eapply lookupBlockViaLabelFromFdef_inv in H; eauto.
Qed.

Lemma wf_system__uniq_block : forall l0 sts0 f ps los nts s,
  blockInFdefB (l0, sts0) f = true ->
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system s ->
  NoDup (getStmtsLocs sts0).
Proof.
  intros.
  eapply wf_system__uniqFdef in H1; eauto.
  destruct f as [f bs]. destruct f. simpl in *.
  inv H1. inv H3.
  eapply uniqBlocksLocs__uniqBlockLocs in H; eauto.
Qed.

Lemma wf_system__wf_cmd : forall l1 ps1 cs1 tmn1 f ps los nts s c,
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true ->
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system s ->
  In c cs1 ->
  wf_insn s (module_intro los nts ps) f (l1, stmts_intro ps1 cs1 tmn1)
    (insn_cmd c).
Proof.
  intros.
  eapply wf_system__blockInFdefB__wf_block in H1; eauto.
  inv H1.
  eapply wf_cmds__wf_cmd; eauto.
Qed.

Lemma wf_system__wf_tmn : forall l1 ps1 cs1 tmn1 f ps los nts s,
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true ->
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system s ->
  wf_insn s (module_intro los nts ps) f (l1, stmts_intro ps1 cs1 tmn1)
    (insn_terminator tmn1).
Proof.
  intros.
  eapply wf_system__blockInFdefB__wf_block in H1; eauto.
  inv H1. auto.
Qed.

Lemma wf_system__wf_layouts: forall los nts Ps1 f Ps2 S 
  (HwfS : wf_system S) 
  (Hin: In (module_intro los nts (Ps1 ++ product_fdef f :: Ps2)) S),
  wf_layouts los.
Proof.
  intros.
  inv HwfS.
  apply In_InModulesB in Hin.
  eapply wf_modules__wf_module in H; eauto.
  inv H. inv H5; auto.
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

(* Properties of wf_phinodes *)
Lemma wf_phinodes_app: forall s m f b ps2 (Hwfps2: wf_phinodes s m f b ps2) ps1
  (Hwfps1: wf_phinodes s m f b ps1), wf_phinodes s m f b (ps1++ps2).
Proof.
  induction ps1; simpl; intros; auto.
    inv Hwfps1. constructor; auto.
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

(* Properties of wf_value *)
Lemma wf_value__wf_typ : forall s los nts ps f v t,
  wf_value s (module_intro los nts ps) f v t ->
  wf_typ s (los, nts) t /\ feasible_typ (los, nts) t.
Proof.
  intros.
  inv H; eauto using wf_typ__feasible_typ.
Qed.

Lemma wf_value_list_cons_iff p l :
  wf_value_list (p :: l) <->
  wf_value_list l /\
  let '(s, m, f, v, t) := p in wf_value s m f v t.
Proof.
  unfold wf_value_list; repeat rewrite <- Forall_forall; split; intros H.
  inversion H; subst. eauto.
  inversion H; constructor; eauto.
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

Lemma wf_value_id__in_getFdefLocs : forall S m f v t,
  wf_value S m f v t -> getValueID' v[<=]ids2atoms (getFdefLocs f).
Proof.
  intros.
  inv H; simpl.
    clear. fsetdec.

    destruct f as [f b]. destruct f as [? ? ? a ?]. simpl in *.
    apply ids2atoms__in.
    destruct_match.
      destruct (In_dec eq_atom_dec id5 (getArgsIDs a)) as [Hin | Hnotin].
        apply in_or_app. auto.

        apply NotInArgsIDs_lookupTypViaIDFromArgs in Hnotin.
        congruence.
      destruct (In_dec eq_atom_dec id5 (getBlocksLocs b)) as [Hin | Hnotin].
        apply in_or_app. auto.

        apply notInBlocks__lookupTypViaIDFromBlocks in Hnotin.
        congruence.
Qed.

Lemma wf_value_id__in_getFdefLocs' : forall S m f v t,
  wf_value S m f v t ->
  match v with
  | value_id vid => In vid (getFdefLocs f)
  | _ => True
  end.
Proof.
  intros.
  destruct v; auto.
  apply wf_value_id__in_getFdefLocs in H.
  simpl in H.
  apply ids2atoms__in in H; auto.
Qed.

(* Properties of wf_cmd *)
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

(* Properties of wf_insn *)
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

(* Properties of wf_fdef *)
Lemma wf_fdef__blockInFdefB__wf_block : forall b S M f,
  blockInFdefB b f = true ->
  wf_fdef S M f ->
  wf_block S M f b.
Proof.
  intros.
  inv H0.
  eapply wf_blocks__wf_block; eauto.
Qed.

Lemma wf_fdef__wf_cmd : forall l1 ps1 cs1 tmn1 s m f c,
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true ->
  wf_fdef s m f ->
  In c cs1 ->
  wf_insn s m f (l1, stmts_intro ps1 cs1 tmn1) (insn_cmd c).
Proof.
  intros.
  eapply wf_fdef__blockInFdefB__wf_block in H; eauto.
  inv H. eapply wf_cmds__wf_cmd; eauto.
Qed.

Lemma wf_fdef__wf_tmn : forall l1 ps1 cs1 tmn1 s m f,
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true ->
  wf_fdef s m f ->
  wf_insn s m f (l1, stmts_intro ps1 cs1 tmn1) (insn_terminator tmn1).
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

Lemma wf_fdef_entryBlock_has_no_phinodes : forall s m f l1 ps1 cs1 tmn1
  (Hwff: wf_fdef s m f)
  (Hentry: getEntryBlock f = Some (l1, stmts_intro ps1 cs1 tmn1)),
  ps1 = nil.
Proof.
  intros s m f l1 ps1 cs1 tmn1 Hwff Hentry.
  assert (wf_block s m f (l1, stmts_intro ps1 cs1 tmn1)) as Hwfb.
    apply entryBlockInFdef in Hentry.
    eapply wf_fdef__blockInFdefB__wf_block; eauto.
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
  inv Hwff. uniq_result.
  match goal with
  | H5: has_no_predecessors _ _ = _,
    J1: (length _ > 0)%nat |- _ => 
    apply has_no_predecessors_tinv in H5;
    rewrite H5 in J1;
    contradict J1; simpl; omega
  end.
Qed.

Lemma wf_fdef__wf_phinodes : forall s m f l3 cs tmn ps,
  wf_fdef s m f ->
  blockInFdefB (l3, stmts_intro ps cs tmn) f ->
  wf_phinodes s m f (l3, stmts_intro ps cs tmn) ps.
Proof.
  intros.
  inv H.
  match goal with
  | H6: wf_blocks _ _ _ _ |- _ =>
    eapply wf_blocks__wf_block in H6; eauto;
    inv H6; auto
  end.
Qed.

Lemma wf_fdef__wf_phinodes': forall s m F ps' cs' tmn' l2,
  wf_fdef s m F ->
  ret (stmts_intro ps' cs' tmn') = lookupBlockViaLabelFromFdef F l2 ->
  uniqFdef F ->
  wf_phinodes s m F (l2, stmts_intro ps' cs' tmn') ps'.
Proof.
  intros.
  symmetry in H0.
  apply lookupBlockViaLabelFromFdef_inv in H0; auto.
  eapply wf_fdef__wf_phinodes in H0; eauto.
 Qed.

Lemma getEntryBlock_inv : forall fh bs
  (l3 : l)
  (l' : l)
  (ps : phinodes)
  (cs : cmds)
  (tmn : terminator)
  (s : system)
  (m : module)
  (HwfF : wf_fdef s m (fdef_intro fh bs)) (Huniq:uniqFdef (fdef_intro fh bs))
  (HBinF : InBlocksB (l3, stmts_intro ps cs tmn) bs = true)
  (Hsucc : In l' (successors_terminator tmn)) a s0
  (H : getEntryBlock (fdef_intro fh bs) = ret (a, s0)),
  l' <> a.
Proof.
  intros.
  destruct (eq_atom_dec l' a); subst; auto.
  inv_wf_fdef HwfF. subst.
  uniq_result.
  eapply successors_predecessors_of_block in Hsucc; eauto 1.
  apply has_no_predecessors_tinv in Hnpred.
  simpl in Hnpred. rewrite Hnpred in Hsucc. tauto.
Qed.

Lemma entryBlock_has_no_pred: forall s m F B l0 l3 ps cs tmn
  (HwfF: wf_fdef s m F) (Hentry:  getEntryBlock F = Some B) (Huniq:uniqFdef F)
  (HBinF : blockInFdefB (l3, stmts_intro ps cs tmn) F = true)
  (Hsucc : In l0 (successors_terminator tmn)) (Heq: l0 = fst B)
  (Hlkup: lookupBlockViaLabelFromFdef F l0 = Some (snd B)),
  False.
Proof.
  intros. subst.
  destruct F as [fh bs]. destruct B.
  eapply getEntryBlock_inv in HBinF; eauto.
Qed.

Lemma entryBlock_has_no_phinodes : forall s f l1 ps1 cs1 tmn1 los nts ps,
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system s ->
  getEntryBlock f = Some (l1, stmts_intro ps1 cs1 tmn1) ->
  ps1 = nil.
Proof.
  intros s f l1 ps1 cs1 tmn1 los nts ps HFinP HMinS Hwfs Hentry.
  assert (wf_fdef s (module_intro los nts ps) f) as Hwff.
    eapply wf_system__wf_fdef; eauto.
  eapply wf_fdef_entryBlock_has_no_phinodes; eauto.
Qed.

Lemma wf_fdef__wf_entry: forall (S : system) (M : module) (f : fdef)
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f),
  match getEntryBlock f with
  | ret (l0, _) =>
      (XATree.make_predecessors (successors f)) !!! l0 = nil
  | merror => False
  end.
Proof.
  intros.
  assert (HwfF':=HwfF).
  inv_wf_fdef HwfF'. subst.
  rewrite Hentry.
  destruct b5 as [l0 ?]. simpl.
  remember ((XATree.make_predecessors (successors_blocks bs5)) !!! l0) as R.
  destruct R as [|a]; auto.
  assert (In a (XATree.make_predecessors (successors_blocks bs5)) !!! l0) as Hin. 
    rewrite <- HeqR. simpl; auto.
  apply XATree.make_predecessors_correct' in Hin.
  apply successors_blocks__blockInFdefB with (fh:=fh5) in Hin.
  destruct Hin as [ps0 [cs0 [tmn0 [J1 J2]]]].
  eapply getEntryBlock_inv with (l3:=a)(a:=l0) in J2; simpl; eauto.
    congruence.
Qed.

Lemma entry_no_preds: forall (S : system) (M : module) (f : fdef)
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f) le 
  (Hentry: getEntryLabel f = Some le),
  (XATree.make_predecessors (successors f)) !!! le = nil.
Proof.
  intros.
  apply wf_fdef__wf_entry in HwfF; auto.
  apply getEntryLabel__getEntryBlock in Hentry.
  destruct Hentry as [[le' ?] [Hentry' EQ]]; 
    simpl in EQ; subst le'; rewrite Hentry' in HwfF; auto.
Qed.

Lemma getEntryBlock_inv': forall (S : system) (M : module) (f : fdef)
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f),
  forall (l3 l' : l) (ps : phinodes) (cs : cmds) (tmn : terminator),
  blockInFdefB (l3, stmts_intro ps cs tmn) f = true ->
  In l' (successors_terminator tmn) ->
  forall (a : l) s0,
  getEntryBlock f = ret (a, s0) -> 
  l' <> a.
Proof.
  intros. destruct f. eapply getEntryBlock_inv; eauto.
Qed.

Lemma wf_fdef__wf_insn: forall S m instr F B
  (HwfF: wf_fdef S m F)
  (HBinF : insnInFdefBlockB instr F B = true),
  wf_insn S m F B instr.
Proof.
  intros.
  destruct B as [? []].
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

Lemma wf_fdef__wf_phinode: forall (s : system) (m : module) (f : fdef) 
  (l3 : l) (cs : cmds) (tmn : terminator) (ps : phinodes) p
  (HwfF: wf_fdef s m f) (HBinF: blockInFdefB (l3, stmts_intro ps cs tmn) f)
  (HinPs: In p ps), wf_phinode f (l3, stmts_intro ps cs tmn) p.
Proof.
  intros.
  eapply wf_fdef__wf_phinodes in HBinF; eauto.
  eapply wf_phinodes__wf_phinode in HBinF; eauto.
  inv HBinF; auto.
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
  destruct b as [? []].
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

(** Properties of dominations *)

Lemma dom_successors : forall
  (bs : blocks) (l3 : l) (l' : l) ps3 cs3 tmn fh
  (Huniq' : uniqFdef (fdef_intro fh bs))
  (HBinF : blockInFdefB (l3, stmts_intro ps3 cs3 tmn) (fdef_intro fh bs) = true)
  (contents3 : ListSet.set atom)
  (Heqdefs3 : contents3 = AlgDom.sdom (fdef_intro fh bs) l3)
  (Hsucc : In l' (successors_terminator tmn))
  (contents' : ListSet.set atom)
  (Heqdefs' : contents' = AlgDom.sdom (fdef_intro fh bs) l'),
  incl contents' (l3 :: contents3).
Proof.
  intros. 
  eapply AlgDom.dom_successors; eauto.
    assert (uniqBlocks bs) as Huniq by eauto using uniqF__uniqBlocks.
    clear - HBinF Hsucc Huniq.
    assert (successors_terminator tmn = (successors_blocks bs) !!! l3) as EQ.
      eapply successors_terminator__successors_blocks; eauto.
    simpl. rewrite <- EQ. auto.
Qed.

Require Import Dipaths.

Lemma branches_in_vertexes: forall (S : system) (M : module) (f : fdef)
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f) (p : l) (ps0 : phinodes)
  (cs0 : cmds) (tmn0 : terminator) (l2 : l)
  (HbInF : blockInFdefB (p, stmts_intro ps0 cs0 tmn0) f)
  (Hinscs : In l2 (successors_terminator tmn0)),
  vertexes_fdef f (index l2).
Proof.
  intros.
  eapply wf_fdef__wf_tmn in HbInF; eauto.
  eapply wf_tmn__in_successors in HbInF; eauto.
  destruct HbInF as [s1 HbInF].
  eapply blockInFdefB_in_vertexes; eauto.
Qed.

Lemma branches_in_bound_fdef: forall (S : system) (M : module) (f : fdef)
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f) (p : l) (ps0 : phinodes)
  (cs0 : cmds) (tmn0 : terminator) (l2 : l)
  (HbInF : blockInFdefB (p, stmts_intro ps0 cs0 tmn0) f)
  (Hinscs : In l2 (successors_terminator tmn0)),
  In l2 (bound_fdef f).
Proof.
  intros.
  eapply wf_fdef__wf_tmn in HbInF; eauto.
  eapply wf_tmn__in_successors in HbInF; eauto.
  destruct HbInF as [s1 HbInF].
  eapply blockInFdefB_in_bound_fdef; eauto.
Qed.

Lemma reachable_successors:
  forall S M f l0 cs ps tmn l1,
  uniqFdef f -> wf_fdef S M f ->
  blockInFdefB (l0, stmts_intro cs ps tmn) f ->
  In l1 (successors_terminator tmn) ->
  reachable f l0 ->
  reachable f l1.
Proof.
  intros S M f l0 cs ps tmn l1 HuniqF HwfF HbInF Hin.
  eapply DecRD.reachable_successors; eauto.
    eapply branches_in_vertexes; eauto.
Qed.

Lemma reachable__reachablity_analysis: forall S M f rd a
  (HwfF: wf_fdef S M f) (Huniq: uniqFdef f) (Hdec: reachable f a)
  (Halg: reachablity_analysis f = Some rd),
  In a rd.
Proof.
  intros.
  assert (Hinbnd:=Hdec).
  apply reachable__in_bound in Hinbnd; eauto using branches_in_bound_fdef.
  apply areachable_is_correct in Hdec; auto.
  unfold reachablity_analysis in Halg.
  inv_mbind. 
  unfold areachable in Hdec. rewrite <- HeqR0 in Hdec.
  apply get_reachable_labels__spec; auto.
Qed.

Lemma reachablity_analysis__reachable: forall S M f rd a
  (Huniq: uniqFdef f) (HwfF: wf_fdef S M f)
  (Hrd: reachablity_analysis f = Some rd) (Hin: In a rd), reachable f a.
Proof.
  unfold reachablity_analysis, areachable_aux in *.
  intros.
  inv_mbind. 
  symmetry in HeqR0.
  set (P:=fun (pc:atom)(r:ReachDS.L.t) => 
          if r then reachable f pc else True).
  assert (forall res : AMap.t ReachDS.L.t,
       ReachDS.fixpoint (successors f) 
         (fun (_ : atom) (r : ReachDS.L.t) => r) 
         ((l0, true) :: nil) = ret res ->
       forall pc : atom, P pc res !! pc) as J.
    apply ReachDS.fixpoint_inv; simpl; auto.
      destruct x; auto.

      unfold P. intros pc sc x y Hin' H1 H2.
      destruct y; auto.
      destruct x; simpl; auto.
      apply successors__blockInFdefB in Hin'.
      destruct Hin' as [ps0 [cs0 [tmn0 [HBinF Hin']]]].
      eapply reachable_successors; eauto.

      intros n v H.
      destruct H as [H | H]; try tauto.
      inv H. unfold P.
      eapply reachable_entrypoint; eauto.

      apply LBoolean.ge_lub.

      unfold P.
      intros n x y H1 H2.
      destruct y; auto.
      destruct H1; subst; try tauto.
  apply J with (pc:=a) in HeqR0.
  unfold P in HeqR0.
  apply get_reachable_labels__spec'' in Hin.
  unfold ReachDS.L.t in *.
  rewrite Hin in HeqR0. auto.
Qed.

Ltac solve_dom :=
try solve [
  eauto 1 |
  unfold AlgDomProps.getEntryBlock_inv; eapply getEntryBlock_inv'; eauto | 
  eapply wf_fdef__non_entry; eauto |
  eapply branches_in_vertexes; eauto |
  eapply wf_fdef__wf_entry; eauto |
  unfold AlgDom.branchs_in_fdef; eapply branches_in_bound_fdef; eauto
].

Lemma dom_unreachable: forall
  S M (f : fdef) (l3 : l) (l' : l) s3
  (HwfF : wf_fdef S M f) (HuniqF: uniqFdef f)
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hunreach: ~ reachable f l3)
  (Hnempty: AlgDom.sdom f l3 <> nil),
  AlgDom.sdom f l3 = bound_fdef f.
Proof. 
  intros. eapply AlgDom.dom_unreachable; solve_dom.
Qed.

Lemma sdom_is_complete: forall
  S M (f : fdef) (l3 : l) (l' : l) s3 s'
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f)
  (HBinF' : blockInFdefB (l', s') f = true)
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hsdom: strict_domination f l' l3)
  (Hnempty: AlgDom.sdom f l3 <> nil),
  In l' (AlgDom.sdom f l3).
Proof.
  intros. eapply AlgDom.sdom_is_complete; solve_dom.
Qed.

Lemma dom_is_sound : forall
  S M (f : fdef) (l3 : l) (l' : l) s3
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f)
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hin : In l' (l3::(AlgDom.sdom f l3))),
  domination f l' l3.
Proof. 
  intros. eapply AlgDomProps.dom_is_sound; solve_dom.
Qed.

Lemma sdom_is_sound : forall
  S M (f : fdef) (l3 : l) (l' : l) s3
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f) (Hreach : reachable f l3)
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hin : In l' (AlgDom.sdom f l3)),
  strict_domination f l' l3.
Proof. 
  intros. eapply AlgDomProps.sdom_is_sound; solve_dom.
Qed.

Lemma sdom_isnt_refl : forall
  S M (f : fdef) (l3 : l) (l' : l) s3
  (HwfF : wf_fdef S M f) (HuniqF : uniqFdef f) (Hreach : reachable f l3)
  (HBinF : blockInFdefB (l3, s3) f = true)
  (Hin : In l' (AlgDom.sdom f l3)),
  l' <> l3.
Proof. 
  intros. eapply AlgDomProps.sdom_isnt_refl; solve_dom.
Qed.

Lemma blockStrictDominates_isnt_refl : forall S M F1 block'
  (Hin : blockInFdefB block' F1) (HwfF : wf_fdef S M F1)
  (HuniqF : uniqFdef F1) (Hreach : isReachableFromEntry F1 block'),
  ~ blockStrictDominates F1 block' block'.
Proof.
  intros. destruct block' as [l0 ? ? ?].
  unfold blockStrictDominates. intro J.
  simpl in Hreach.
  eapply sdom_isnt_refl in Hreach; eauto.
Qed.

Lemma dom_acyclic: forall S M (f:fdef) (l1 l2:l)
  (HwfF:wf_fdef S M f) (HuniqF : uniqFdef f),
  reachable f l2 ->
  strict_domination f l1 l2 -> ~ domination f l2 l1.
Proof. 
  intros. eapply DecDom.dom_acyclic; eauto using getEntryBlock_inv'.
Qed.

Lemma sdom_tran1: forall S M (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef S M f)
  (HuniqF: uniqFdef f) (Hreach: reachable f l2),
  strict_domination f l1 l2 -> domination f l2 l3 -> 
  strict_domination f l1 l3.
Proof.
  intros. eapply DecDom.sdom_tran1; eauto using getEntryBlock_inv'.
Qed.

Lemma sdom_tran2: forall S M (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef S M f)
  (HuniqF: uniqFdef f) (Hreach: reachable f l3),
  domination f l1 l2 -> strict_domination f l2 l3 -> 
  strict_domination f l1 l3.
Proof.
  intros. eapply DecDom.sdom_tran2; eauto using getEntryBlock_inv'.
Qed.

Lemma sdom_tran: forall S M (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef S M f)
  (HuniqF: uniqFdef f) (Hreach: reachable f l2),
  strict_domination f l1 l2 -> strict_domination f l2 l3 ->
  strict_domination f l1 l3.
Proof.
  intros. eapply DecDom.sdom_tran; eauto using getEntryBlock_inv'.
Qed.

Lemma sdom_acyclic: forall l1 l2 s1 s2 S M F
  (Hwf: wf_fdef S M F) (Huniq: uniqFdef F) (Hrd: reachable F l2)
  (HbInF1: blockInFdefB (l1, s1) F = true)
  (HbInF2: blockInFdefB (l2, s2) F = true)
  (Hin1: In l1 (AlgDom.sdom F l2))
  (Hin2: In l2 (AlgDom.sdom F l1))
  (Hneq: l1 <> l2),
  False.
Proof. 
  intros. eapply AlgDomProps.sdom_acyclic in Hneq; solve_dom.
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
  destruct (reachable_dec f l2).
  Case "1".
    assert (strict_domination f l1 l2) as Hsdom23.
      eapply sdom_is_sound; eauto.
    assert (reachable f l1) as Hreach1.
      apply DecDom.sdom_reachable in Hsdom23; auto.
    assert (strict_domination f l0 l1) as Hsdom12.
      eapply sdom_is_sound; eauto.
    assert (strict_domination f l0 l2) as Hsdom13.
      eapply sdom_tran with (l2:=l1); eauto.
    eapply sdom_is_complete in Hsdom13; eauto.
      intro J. rewrite J in H2. inv H2.

  Case "2".
    eapply dom_unreachable in H; eauto.
      rewrite H. 
      apply blockInFdefB_in_bound_fdef in HBinF1; auto.

      intro J. rewrite J in H2. inv H2.
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
  destruct (l_dec l0 l2); auto.
  destruct H2 as [H2 | H2]; subst; auto.
  Case "l1 in sdom(l2)".
    left.
    assert (domination f l1 l2) as Hdom23.
      eapply dom_is_sound; eauto.
        simpl. auto.
    destruct H1 as [H1 | H1]; subst.
    SCase "l0 in sdom(l1)".
      assert (domination f l0 l1) as Hdom12.
        eapply dom_is_sound; eauto.
          simpl. auto.
      assert (strict_domination f l0 l2) as Hsdom13.
        apply DecDom.dom_sdom; auto.
        eapply DecDom.dom_tran; eauto.
      eapply sdom_is_complete in Hsdom13; eauto.
        intro J. rewrite J in H2. inv H2.

    SCase "l0=l1".
      assert (strict_domination f l1 l2) as Hsdom12.
        apply DecDom.dom_sdom; auto.
      eapply sdom_is_complete in Hsdom12; eauto.
        intro J. rewrite J in H2. inv H2.
Qed.

Lemma blockDominates__domination: forall (S : system) (M : module) (f : fdef)
  (Hwf : wf_fdef S M f) (Huniq : uniqFdef f) (b1 b2:block)
  (HBinF : blockInFdefB b2 f) (Hdom : blockDominates f b1 b2),
  domination f (getBlockLabel b1) (getBlockLabel b2).
Proof.
  intros.
  destruct b1 as [l5 ?], b2.
  unfold blockDominates in Hdom.
  eapply dom_is_sound with (l':=l5) in HBinF; simpl; eauto 1.
    destruct Hdom; auto.
Qed.

(* Properties of wf_operand *)
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

(* Properties of wf_phi_operands *)

(* wf_phi_operands doesnt depend on i0 and t0, which should be removed. *)
Lemma wf_phi_operands__intro : forall f b i0 t0 vls0,
  (forall vid1 l1 (Hin: In (value_id vid1, l1) vls0), 
     exists sts1,
      lookupBlockViaLabelFromFdef f l1 = Some sts1 /\
      (((exists vb,
         lookupBlockViaIDFromFdef f vid1 = Some vb /\
         blockDominates f vb (l1, sts1)) \/ 
        not (isReachableFromEntry f (l1, sts1))) \/
      In vid1 (getArgsIDsOfFdef f))) ->
  wf_phi_operands f b i0 t0 vls0.
Proof.
  induction vls0 as [|[[vid5|] l0]]; intros.
    constructor.

    assert (In (value_id vid5, l0) ((value_id vid5, l0) :: vls0)) as Hin.
      xsolve_in_list.
    apply H in Hin.
    destruct Hin as [b1 [J1 J2]].
    econstructor; eauto.
      apply IHvls0.
      intros.
      apply H. simpl. auto.

    constructor.
      apply IHvls0.
      intros.
      apply H. simpl. auto.
Qed.

Lemma wf_phi_operands__elim' : forall f b i0 t0 vls0 vid1 l1
  (Hwfop: wf_phi_operands f b i0 t0 vls0)
  (Hin: In (value_id vid1, l1) vls0),
  exists sts1,
    lookupBlockViaLabelFromFdef f l1 = Some sts1 /\
    (((exists vb,
        lookupBlockViaIDFromFdef f vid1 = Some vb /\
        blockDominates f vb (l1, sts1)) \/ 
      not (isReachableFromEntry f (l1, sts1))) \/
     In vid1 (getArgsIDsOfFdef f)).
Proof.
  induction 1; intros.
    tauto.

    destruct_in Hin.
      inv Hin. eauto.

    destruct_in Hin.
      congruence.
Qed.

Lemma wf_phi_operands__elim : forall f b i0 t0 vls0 vid1 l1 n,
  wf_phi_operands f b i0 t0 vls0 ->
  nth_error vls0 n = Some (value_id vid1, l1) ->
  exists sts1,
    lookupBlockViaLabelFromFdef f l1 = Some sts1 /\
    (((exists vb,
       lookupBlockViaIDFromFdef f vid1 = Some vb /\
       blockDominates f vb (l1, sts1)) \/ 
      not (isReachableFromEntry f (l1, sts1))) \/
     In vid1 (getArgsIDsOfFdef f)).
Proof.
  induction vls0; intros.
    destruct n; inversion H0.
    inv H; destruct n; inv H0; eauto.
Qed.

Lemma wf_phi_operands__elim'': forall (S : system) (M : module) (f : fdef)
  (l0 : l) sts0
  (Hwf : wf_fdef S M f) (Huniq : uniqFdef f) (value_l_list : list (value * l))
  (id5 : id) (typ5 : typ)
  (Hwfops : wf_phi_operands f (l0, sts0) id5 typ5
              value_l_list) vid
  (Hnotinfh : ~ In vid (getArgsIDsOfFdef f)) (l1 : l)
  (Hinlist: In (value_id vid, l1) value_l_list) (Hreach: reachable f l1),
  exists bv, exists bvl,
    lookupBlockViaLabelFromFdef f l1 = ret bvl /\
    lookupBlockViaIDFromFdef f vid = ret bv /\
    domination f (getBlockLabel bv) l1.
Proof.
  intros.
  eapply wf_phi_operands__elim' in Hinlist; eauto.
  destruct Hinlist 
    as [blv' [Hlkupblv [[[bv' [Hlkbv Hdom]]|Hnreachblv]|?]]]; 
    try solve [contradict Hnotinfh; auto].
  Case "bv' doms blk'".
    exists bv'. exists blv'.
    split; auto.
    split; auto.
      lookupBlockViaLabelFromFdef_inv_tac.
      eapply blockDominates__domination in Hdom; eauto 1.

  Case "blk' is unreachable".
    lookupBlockViaLabelFromFdef_inv_tac.
    simpl in *. congruence.
Qed.

Lemma wf_phi_operands__successors: forall (S : system) (M : module) (f : fdef) b
  (Huniq : uniqFdef f) (vls : list (value * l))
  (id5 : id) (typ5 : typ) 
  (Hwfops : check_list_value_l f b vls) l1
  (Hscs: arcs_fdef f (A_ends (index (getBlockLabel b)) (index l1))),
  exists v1, In (v1, l1) vls.
Proof. 
  simpl.
  intros.
  unfold check_list_value_l in Hwfops.
  remember (split vls) as R.
  destruct R as [? ls1].
  destruct Hwfops as [_ [Hwfops _]].
  apply successors_predecessors_of_block' in Hscs; auto.
  apply Hwfops in Hscs.
  apply split_r_in; auto.
    unfold l in *.
    rewrite <- HeqR. auto.
Qed.

(* Properties of wf_typ_list *)
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

(* const2GV has invariant system and targetdata. *)
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

(* Properties of operands *)
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

(* Properties of reachability *)
Lemma isReachableFromEntry_successors : forall f l3 ps cs tmn l' sts'
  (Hreach : isReachableFromEntry f (l3, stmts_intro ps cs tmn))
  (HBinF : blockInFdefB (l3, stmts_intro ps cs tmn) f = true)
  (Huniq : uniqFdef f) s m (HwfF : wf_fdef s m f)
  (Hsucc : In l' (successors_terminator tmn))
  (Hlkup : lookupBlockViaLabelFromFdef f l' = Some sts'),
  isReachableFromEntry f (l', sts').
Proof.
  intros.
  unfold isReachableFromEntry in *. 
  apply lookupBlockViaLabelFromFdef_inv in Hlkup; auto.
  eapply reachable_successors; eauto.
Qed.

Ltac unfold_reachable_tac :=
match goal with
| Hentry: getEntryBlock ?f = ret ?be, Hreach: reachable ?f _ |- _ =>
  let vl := fresh "vl" in
  let al := fresh "al" in
  let Hwalk := fresh "Hwalk" in
    unfold reachable in Hreach;
    rewrite Hentry in Hreach;
    match goal with 
    | _: getEntryBlock ?f = ret (_, _) |- _ => idtac
    | _ =>
        let le := fresh "le" in
        destruct be as [le []]
    end;
    destruct Hreach as [vl [al Hwalk]]
end.

Lemma reachable_phinode__ex_reachable_incoming: forall (S : system) (M : module)
  (f : fdef) (Hwf : wf_fdef S M f) (Huniq : uniqFdef f) b
  (Hreach : isReachableFromEntry f b) (pid : id) (ty : typ) 
  (vls : list (value * l))
  (Hwfops : check_list_value_l f b vls)
  (be : block) (Hentry : getEntryBlock f = ret be)
  (Hneq : getBlockLabel be <> getBlockLabel b),
  exists v0 : value, exists l1 : l, In (v0, l1) vls /\ reachable f l1.
Proof.
  intros.
  destruct b.
  simpl in *.
  unfold_reachable_tac.
  simpl in Hneq.
  inv Hwalk; try congruence.
  destruct y as [ly].
  eapply wf_phi_operands__successors in Hwfops; eauto.
  destruct Hwfops as [v1 Hwfops].
  exists v1. exists ly.
  split; auto.
    unfold reachable. autounfold with cfg.
    rewrite Hentry.
    eauto.
Qed.

(* Properties of scoping *)
Lemma block_in_scope__strict: forall (l' : l) sts' F
  (Hreach' : isReachableFromEntry F (l', sts')) s m
  (HwfF : wf_fdef s m F) (HuniqF : uniqFdef F)
  (contents' : ListSet.set atom)
  (Heqdefs' : contents' = AlgDom.sdom F l')
  (l0 : l) (Hindom' : In l0 contents')
  (HbInF' : blockInFdefB (l', sts') F = true),
  l0 <> l'.
Proof.
  intros.
  assert (strict_domination F l0 l') as Hdom12.
    eapply sdom_is_sound; eauto.
      rewrite <- Heqdefs'. simpl. auto.
  eapply DecDom.sdom_isnt_refl; eauto.
Qed.

Lemma in_getArgsIDsOfFdef__inscope_of_tmn: forall defs f b tmn id1
  (Hinscope: inscope_of_tmn f b tmn = Some defs)
  (Hin: In id1 (getArgsIDsOfFdef f)), In id1 defs.
Proof.
  intros. destruct b as [l1 []].
  unfold inscope_of_tmn in Hinscope.
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
  intros. destruct b as [l1 []].
  unfold inscope_of_id in Hinscope.
  apply fold_left__spec in Hinscope.
  destruct Hinscope as [Hinscope _].
  apply Hinscope. apply in_getArgsIDsOfFdef__init_scope; auto.
Qed.

Lemma in_getArgsIDsOfFdef__inscope_of_cmd: forall defs f b c id1
  (Hinscope: inscope_of_cmd f b c = Some defs)
  (Hin: In id1 (getArgsIDsOfFdef f)), In id1 defs.
Proof.
  intros. destruct b as [l1 []].
  unfold inscope_of_cmd, inscope_of_id in Hinscope.
  apply fold_left__spec in Hinscope.
  destruct Hinscope as [Hinscope _].
  apply Hinscope. apply in_getArgsIDsOfFdef__init_scope; auto.
Qed.

Lemma operands_of_cmd__cannot_be__phis_that_cmd_doms: forall (l' : l)
  (ps' : phinodes) (cs' : cmds) (F : fdef) (tmn' : terminator) (b : block)
  (Hreach' : isReachableFromEntry F (l', stmts_intro ps' cs' tmn')) s m
  (Hlkup : ret stmts_intro ps' cs' tmn' = lookupBlockViaLabelFromFdef F l')
  (ids0' : list atom) (HwfF : wf_fdef s m F) (contents' : ListSet.set atom)
  (Huniq: uniqFdef F)
  (Heqdefs' : contents' = AlgDom.sdom F l')
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
  assert (isReachableFromEntry F b1) as Hreachb1.
    apply Hreach'' in H. auto.
  match goal with
  | H10: (_ \/ _ ) \/ In _ (getArgsIDsOfFdef _) |- _ =>
     destruct H10 as [[[block' [Hlk H10]] | H10] | H10]; try congruence
  end.
  Case "i0 isnt args".
  assert ((l', stmts_intro ps' cs' tmn') = block') as EQ.
    eapply lookupBlockViaIDFromFdef__lookupBlockViaLabelFromFdef__eq;
      eauto.
      solve_in_list.
  subst.
  destruct b1 as [l0 [p c t0]].
  assert (In l0 (AlgDom.sdom F l')) as Hindom'.
    eapply cmd_in_scope__block_in_scope; eauto.
  assert (blockInFdefB (l', stmts_intro ps' cs' tmn') F = true)as HbInF'.
    symmetry in Hlkup.
    apply lookupBlockViaLabelFromFdef_inv in Hlkup; auto.
    destruct Hlkup; auto.
  assert (l0 <> l') as Hneq.
    eapply block_in_scope__strict; eauto. apply in_app. left; auto.
  assert (blockInFdefB (l0, stmts_intro p c t0) F = true)as HbInF0.
    eauto using insnInFdefBlockB__blockInFdefB.
  assert (In l' (AlgDom.sdom F l0)) as Hindom.
    eapply domination__block_in_scope; eauto.
  eapply sdom_acyclic in Hindom'; eauto.
  Case "i0 is args".
    assert (blockInFdefB (l', stmts_intro ps' cs' tmn') F = true) as HBinF.
      solve_blockInFdefB.
    eapply getBlocksLocs__notin__getArgsIDs in HBinF; eauto. 
    solve_in_list.
  Case "wf_operand".
    unfold wf_operand_list.
    remove_irrelevant wf_operand.
    solve_forall_like_ind.
Qed.

Lemma strict_operands__in_scope: forall f (l1 : l) sts1 
  (defs : list atom) (id1 : id)
  (Hreach : isReachableFromEntry f (l1, sts1))
  (bs_contents : ListSet.set atom)
  (HeqR : bs_contents = AlgDom.sdom f l1)
  (Hinscope : forall (l2 : atom) sts2,
             In l2 (ListSet.set_diff eq_atom_dec bs_contents [l1]) ->
             lookupBlockViaLabelFromFdef f l2 = ret sts2 ->
             incl (getStmtsIDs sts2) defs) s m
  (HwfF : wf_fdef s m f) (Huniq: uniqFdef f) instr
  (HinOps : In id1 (getInsnOperands instr))
  (H:insnInFdefBlockB instr f (l1, sts1) = true)
  (block' : block)
  (H4 : lookupBlockViaIDFromFdef f id1 = ret block')
  (J': blockStrictDominates f block' (l1, sts1)),
  In id1 defs.
Proof.
  intros.
  unfold blockStrictDominates in J'.
  rewrite <- HeqR in J'.
  destruct block' as [l5 sts5].
  assert (In l5 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as J.
    simpl in Hreach.
    apply insnInFdefBlockB__blockInFdefB in H.
    eapply sdom_isnt_refl with (l':=l5) in Hreach; eauto.
      apply ListSet.set_diff_intro; auto.
      simpl. intro J. destruct J as [J | J]; auto.
      rewrite <- HeqR. simpl. auto.
  assert (lookupBlockViaLabelFromFdef f l5 = ret sts5) as J1.
     apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
     eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto.
  apply Hinscope with (sts2:=sts5) in J; auto.
    apply J.
    eapply lookupBlockViaIDFromFdef__InGetBlockIDs in H4; eauto.
Qed.

Lemma terminator_operands__in_scope: forall (f : fdef) (l1 : l) (ps1 : phinodes)
  (cs1 : cmds) (tmn1 : terminator) (defs : list atom) (id1 : id)
  (Hreach : isReachableFromEntry f (l1, stmts_intro ps1 cs1 tmn1))
  (Hinscope : ret defs = inscope_of_tmn f (l1, stmts_intro ps1 cs1 tmn1) tmn1)
  s m (HwfF : wf_fdef s m f) (Huniq: uniqFdef f)
  (HinOps : In id1 (getInsnOperands (insn_terminator tmn1)))
  (H : insnInFdefBlockB (insn_terminator tmn1) f (l1, stmts_intro ps1 cs1 tmn1) =
       true)
  (H2 : wf_operand f (l1, stmts_intro ps1 cs1 tmn1) (insn_terminator tmn1) id1),
  In id1 defs.
Proof.
  intros.
  inv H2.
  match goal with
  | H10: (_ \/ _ ) \/ In _ (getArgsIDsOfFdef _) |- _ =>
     destruct H10 as [[[block' [Hlk H10]] | H10] | H10]; try congruence
  end.
  Case "id1 isnt args".
  unfold inscope_of_tmn in Hinscope.
  destruct f as [[fa ty fid la va] bs].
  symmetry in Hinscope.
  apply fold_left__spec in Hinscope.
  match goal with
  | H6: _ \/ _ |- _ =>
    destruct H6 as [J' | J']
  end.
    SCase "insnDom".
    destruct Hinscope as [Hinscope _].
    apply Hinscope.
    eapply insnDominates_spec6; eauto.

    SCase "blkDom".
    destruct Hinscope as [_ [Hinscope _]].
    eapply strict_operands__in_scope; eauto.
    rewrite app_nil_r.
    intros. eapply Hinscope; eauto.
    
  Case "id1 is args".
    eapply in_getArgsIDsOfFdef__inscope_of_tmn; eauto.
Qed.

Lemma cmd_operands__in_scope: forall (f : fdef) (b : block) (c : cmd)
  (defs : list atom) (id1 : id) (Hnodup : NoDup (getStmtsLocs (snd b)))
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
  | H10: (_ \/ _ ) \/ In _ (getArgsIDsOfFdef _) |- _ =>
     destruct H10 as [[[block' [Hlk H10]] | H10] | H10]; try congruence
  end.
  Case "id1 isnt args".
  unfold inscope_of_cmd, inscope_of_id in Hinscope.
  destruct b as [? [ps5 ? ? ]]. destruct f as [[f t0 i0 a v] b].
  symmetry in Hinscope.
  assert (~ In (getCmdLoc c) (getPhiNodesIDs ps5)) as Hnotin.
    simpl in Hnodup.
    eapply NoDup_disjoint; eauto.
    apply destruct_insnInFdefBlockB in H.
    destruct H. simpl in H.
    solve_in_list.
  apply fold_left__spec in Hinscope.
  match goal with
  | H6: _ \/ _ |- _ =>
    destruct H6 as [J' | J']
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
        simpl in Hnodup. apply NoDup_split in Hnodup.
        destruct Hnodup as [_ Hnodup].
        apply NoDup_split in Hnodup.
        destruct Hnodup as [Hnodup _].
        rewrite_env ((cs1 ++ c1' :: cs2) ++ c :: cs3).
        rewrite_env ((cs1 ++ c1' :: cs2) ++ c :: cs3) in Hnodup.
        apply NoDup__In_cmds_dominates_cmd; auto.
          solve_in_list.

    SCase "blkDom".
    destruct Hinscope as [_ [Hinscope _]].
    eapply strict_operands__in_scope; eauto.
    rewrite app_nil_r. intros; eauto.
    
  Case "id1 is args".
    eapply in_getArgsIDsOfFdef__inscope_of_cmd; eauto.
Qed.

Lemma cmd_doesnt_use_self: forall (F1 : fdef) (l3 : l) sts3
  (Hreach : isReachableFromEntry F1 (l3, sts3))
  (HBinF1 : blockInFdefB (l3, sts3) F1 = true) s m
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
  | H10: (_ \/ _) \/ In _ (getArgsIDsOfFdef _) |- _ =>
     destruct H10 as [[[block' [Hlk H10]] | ? ]| H10]; try congruence
  end.
  Case "id1 isnt args".
  assert (b1 = block') as EQ.
    eapply insnInFdefBlockB__lookupBlockViaIDFromFdef__eq; eauto.
  subst.
  match goal with
  | H7: _ \/ _ |- _ =>
    destruct H7 as [H7 | H7]; contradict H7
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
  match goal with
  | H8: forall _:_, _ -> _ |- _ =>
    generalize H8;
    generalize (getInsnOperands (insn_cmd c0));
    clear H8; intros is H; unfold ids in *;
    solve_forall_like_ind
  end.
Qed.

Lemma c1_in_scope_of_c2__c1_insnDominates_c2: forall (ids1 : list atom)
  (F1 : fdef) (c : cmd) s m (HwfF1 : wf_fdef s m F1) (Huniq: uniqFdef F1)
  (bs_contents : ListSet.set atom)
  (c1 : cmd) (Hin : In (getCmdLoc c1) ids1) (l0 : l) (p : phinodes) (c0 : cmds)
  (t : terminator)
  (H : insnInFdefBlockB (insn_cmd c1) F1 (l0, stmts_intro p c0 t) = true)
  init (Heq: init = getArgsIDsOfFdef F1)
  (HInscope : ret ids1 =
       fold_left (inscope_of_block F1 l0) bs_contents
         (ret (getPhiNodesIDs p ++ cmds_dominates_cmd c0 (getCmdLoc c) ++ init)))
  (HcInB : cmdInBlockB c (l0, stmts_intro p c0 t) = true),
  insnDominates (getCmdLoc c1) (insn_cmd c) (l0, stmts_intro p c0 t).
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
    eapply lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef in J2;
      eauto.
    assert (getCmdID c1 <> None) as foo.
      eapply lookupInsnViaIDFromFdef_lookupBlockViaIDFromFdef__getInsnID
        with (insn1:=insn_cmd c1) in J2; eauto 1.
        simpl in J2. congruence.

        simpl in H. bdestruct H as H1 H2.
        eapply IngetCmdsIDs__lookupCmdViaIDFromFdef; eauto.
          solve_in_list.
    eapply insnInFdefBlockB__lookupBlockViaIDFromFdef in H; eauto.
    simpl in H. rewrite H in J2. inv J2.
    apply ListSet.set_diff_elim2 in J1. contradict J1; simpl; auto.
Qed.

Lemma l1_strict_in_scope_of_l2__l1_blockDominates_l2: forall (ids1 : list atom)
  (F1 : fdef) (l3 : l) (ps1 : phinodes) (cs : list cmd) (tmn1 : terminator)
  (c : cmd) (HBinF1 : blockInFdefB (l3, stmts_intro ps1 cs tmn1) F1 = true) s m
  (HwfF1 : wf_fdef s m F1) (Huniq: uniqFdef F1) (bs_contents : ListSet.set atom)
  (c1 : cmd)
  (Hin : In (getCmdLoc c1) ids1) (l0 : l) sts0
  (H0 : insnInFdefBlockB (insn_cmd c1) F1 (l0, sts0) = true)
  (HeqR : bs_contents = AlgDom.sdom F1 l3)
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
        assert ((l0, sts0) = (l3, stmts_intro ps1 cs tmn1)) as EQ.
          eapply insnInFdefBlockB__lookupBlockViaIDFromFdef__eq; eauto.
        inv EQ.
        eapply In_cmds_dominates_cmd_fdef__getCmdID_eq_getCmdLoc
          with (id0:=getCmdLoc c) in H0; eauto.
      apply insnInFdefBlockB__lookupBlockViaIDFromFdef in H0; auto.
      simpl in H0. rewrite H0 in HBinF1. inv HBinF1. congruence.
      simpl.
      eapply cmds_dominates_cmd_spec' with (id0:=getCmdLoc c); eauto.

    eapply lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef in J2;
      eauto.
    assert (getCmdID c1 <> None) as foo.
      eapply lookupInsnViaIDFromFdef_lookupBlockViaIDFromFdef__getInsnID
        with (insn1:=insn_cmd c1) in J2; eauto 1.
        simpl in J2. congruence.

        simpl in H0. bdestruct H0 as H1 H2. destruct sts0.
        eapply IngetCmdsIDs__lookupCmdViaIDFromFdef; eauto.
          solve_in_list.
    eapply insnInFdefBlockB__lookupBlockViaIDFromFdef in H0; eauto.
    simpl in H0. rewrite H0 in J2. inv J2.
    apply ListSet.set_diff_elim1 in J1; auto.
Qed.

Lemma cmd_doesnt_use_nondom_operands: forall (ids1 : list atom)
  (F1 : fdef) (B1 : block) (l3 : l) (ps1 : phinodes) (cs : list cmd)
  (tmn1 : terminator) (c : cmd) (HinCs : In c cs)
  (Hreach : isReachableFromEntry F1 (l3, stmts_intro ps1 cs tmn1))
  (HBinF1 : blockInFdefB (l3, stmts_intro ps1 cs tmn1) F1 = true)
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
  | H10: (_ \/ _ ) \/ In _ (getArgsIDsOfFdef _) |- _ =>
     destruct H10 as [[[block' [Hlk H10]] | ?] | H10]; try congruence
  end.
  Case "id1 isnt args".
  destruct b1 as [l0 [p c0 t]].
  destruct B1 as [l1 [p0 c2 t0]]. simpl in HInscope.
  assert (~ In (getCmdLoc c) (getPhiNodesIDs p0)) as Hnotin.
    apply uniqFdef__uniqBlockLocs in HBinF2; auto.
    simpl in HBinF2.
    eapply NoDup_disjoint in HBinF2; eauto.
    simpl in HcInB. solve_in_list.
  rewrite init_scope_spec1 in HInscope; auto.
  assert (block' = (l3, stmts_intro ps1 cs tmn1)) as RQ.
    symmetry.
    eapply lookupBlockViaIDFromFdef__lookupBlockViaLabelFromFdef__eq; eauto.
      symmetry.
      apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
      simpl. apply in_or_app. right.  apply in_or_app.
      left. apply getCmdLoc_in_getCmdsLocs; eauto.
  subst.
  match goal with
  | H7: _ \/ _ |- _ =>
    destruct H7 as [H7 | H7]; auto
  end.
  SCase "1".
    assert ((l1, stmts_intro p0 c2 t0) = (l0, stmts_intro p c0 t)) as EQ.
      apply insnInFdefBlockB__blockInFdefB in H0.
      eapply cmdInBlockB_eqBlock with (c:=c); eauto.
      match goal with
      | H7: insnDominates _ _ _ |- _ =>
        eapply insnDominates_spec5 in H7; eauto
      end.
      uniq_result. simpl; apply In_InCmdsB; auto.
    inv EQ.
    assert (insnDominates (getCmdLoc c1) (insn_cmd c) (l0, stmts_intro p c0 t))
      as Hdom.
      clear - Hin HInscope HcInB H HwfF1 Huniq. destruct F1 as [[]].
      eapply c1_in_scope_of_c2__c1_insnDominates_c2 in HInscope; eauto.
    apply insnDominates_spec2 in Hdom; try solve [simpl; auto].
      eapply uniqFdef__uniqBlockLocs; eauto.
      eapply insnDominates_spec5 in Hdom; eauto.
      apply insnInFdefBlockB__insnInBlockB in H; auto.

  SCase "2".
    assert ((l1, stmts_intro p0 c2 t0) = (l3, stmts_intro ps1 cs tmn1)) as EQ.
      apply In_InCmdsB in HinCs.
      eapply cmdInBlockB_eqBlock; eauto.
    inv EQ.
    assert (l0 <> l3) as Hneq.
      match goal with
      | H6: blockStrictDominates _ _ _ |- _ => simpl in H6 end.
      simpl in Hreach'. apply insnInFdefBlockB__blockInFdefB in H.
      eapply sdom_isnt_refl with (l':=l3) in Hreach'; eauto.

    assert (In l0 (AlgDom.sdom F1 l3)) as Hindom'.
      clear - H0 HInscope Hin Hneq HBinF1 HwfF1 Huniq. destruct F1 as [[]].
      eapply l1_strict_in_scope_of_l2__l1_blockDominates_l2 in HInscope; eauto.

    assert (In l3 (AlgDom.sdom F1 l0)) as Hindom.
      match goal with
      | H6: blockStrictDominates _ _ _ |- _ =>
        clear - H6; unfold blockStrictDominates in H6
      end.
      auto.
    apply insnInFdefBlockB__blockInFdefB in H0.
    eapply sdom_acyclic in Hindom; eauto.
  Case "id1 is args".
    contradict H6.
    replace (getCmdLoc c) with (getInsnLoc (insn_cmd c)); auto.
    eapply getInsnLoc__notin__getArgsIDs'' with (b:=B1); eauto 1.
      solve_insnInFdefBlockB.
Qed.

Lemma incoming_value__in_scope: forall (f : fdef) (l0 : l)
  (t : list atom) (l1 : l) ps1 cs1 tmn1
  (HeqR : ret t = inscope_of_tmn f (l1, stmts_intro ps1 cs1 tmn1) tmn1)
  (HuniqF : uniqFdef f) sts0 (i0 : id) (l2 : list (value * l))
  (Hreach : isReachableFromEntry f (l1, stmts_intro ps1 cs1 tmn1))
  (HbInF : blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true) t0
  (H7 : wf_phinode f (l0, sts0) (insn_phi i0 t0 l2))
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
  destruct Hwfops as [sts1 [Hlkb1 Hwfops]].
  assert (sts1 = stmts_intro ps1 cs1 tmn1) as EQ.
    clear - Hlkb1 HbInF HuniqF.
    apply blockInFdefB_lookupBlockViaLabelFromFdef in HbInF; auto.
    rewrite HbInF in Hlkb1. inv Hlkb1; auto.
  subst.
  destruct Hwfops as [[ [vb [Hlkvb Hdom]] | ? ] | HinArgs]; try congruence.
  Case "isnt args".
  clear - Hdom HeqR J HbInF Hlkvb Hlkb1 HuniqF.
  rename Hdom into J3.
  unfold blockDominates in J3.
  destruct vb as [l5 sts5].
  unfold inscope_of_tmn in HeqR.
  destruct f as [[fa ty fid la va] bs].
  symmetry in HeqR.
  apply fold_left__spec in HeqR.
  destruct (eq_atom_dec l5 l1); subst.
  SCase "l5=l1".
    destruct HeqR as [HeqR _].
    clear - J HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
    assert (J':=Hlkvb).
    apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
    apply lookupBlockViaLabelFromFdef_inv in Hlkb1; auto.
    eapply blockInFdefB_uniq in Hlkb1; eauto.
    subst.
    apply lookupBlockViaIDFromFdef__InGetBlockIDs in J'.
    simpl in J'.
    apply HeqR; auto. solve_in_list.

  SCase "l5<>l1".
    destruct J3 as [J3 | Heq]; subst; try congruence.
    assert (In l5 (ListSet.set_diff eq_atom_dec 
       (AlgDom.sdom (fdef_intro (fheader_intro fa ty fid la va) bs) l1) [l1])) as G.
      apply ListSet.set_diff_intro; auto.
        simpl. intro JJ. destruct JJ as [JJ | JJ]; auto.
    assert (
      lookupBlockViaLabelFromFdef (fdef_intro (fheader_intro fa ty fid la va) bs)
        l5 = ret sts5) as J1.
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
  (t : list atom) (l1 : l) sts1 s m id1 (id2 : id) (HwfF : wf_fdef s m f)
  (bs_contents : ListSet.set atom) (Huniq: uniqFdef f)
  (HeqR3 : bs_contents = AlgDom.sdom f l1)
  (Hreach : isReachableFromEntry f (l1, sts1))
  (HbInF : blockInFdefB (l1, sts1) f = true)
  (l2 : l) sts2
  (HeqR1 : ret (l2, sts2) = lookupBlockViaIDFromFdef f id2)
  (bs_contents0 : ListSet.set atom)
  (HeqR4 : bs_contents0 = AlgDom.sdom f l2)
  sts1' (l1' : atom)
  (J10 : In l1' (ListSet.set_diff eq_atom_dec bs_contents0 [l2]))
  (J11 : lookupBlockViaLabelFromFdef f l1' = ret sts1')
  (J11' : In id1 (getStmtsIDs sts1')) sts2' (l2' : atom)
  (J13 : In l2' (ListSet.set_diff eq_atom_dec bs_contents [l1]))
  (J14 : lookupBlockViaLabelFromFdef f l2' = ret sts2')
  (J15 : In id2 (getStmtsIDs sts2')) init
  (HeqR' : fold_left (inscope_of_block f l1) bs_contents (ret init) = ret t),
  In id1 t.
Proof.
  intros.
  assert ((l2, sts2) = (l2', sts2')) as EQ.
    clear - Huniq HeqR1 J14 J15.
    apply lookupBlockViaLabelFromFdef__blockInFdefB in J14; auto.
    eapply block_eq1 with (id0:=id2); eauto 1.
  inv EQ.
  apply lookupBlockViaLabelFromFdef_inv in J14; auto.
  apply lookupBlockViaLabelFromFdef_inv in J11; auto.
  assert (blockStrictDominates f (l1', sts1')
                                 (l2', sts2')) as Hdom.
    clear - J10 HwfF. simpl. 
    apply ListSet.set_diff_elim1 in J10; auto.
  assert (blockStrictDominates f (l2', sts2')
                                 (l1, sts1)) as Hdom'.
    clear - J13 HwfF. simpl. 
    apply ListSet.set_diff_elim1 in J13; auto.
  assert (blockStrictDominates f (l1', sts1') (l1, sts1)) as Hdom''.
    eapply blockStrictDominates_trans; eauto.
  destruct (l_dec l1' l1); subst.
    assert ((l1, sts1') = (l1, sts1)) as EQ.
      clear - HbInF J11 Huniq.
      eapply blockInFdefB_uniq in HbInF; eauto.
      destruct HbInF as [Heq1 [Heq2 Heq3]]; subst. auto.
    inv EQ.
    eapply blockStrictDominates_isnt_refl in Hreach;
      try solve [eauto | contradict Hdom''; auto].

    simpl in Hdom''. 
    apply fold_left__intro with (l2:=l1')(sts2:= sts1')
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
  (HeqR : inscope_of_cmd f (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn1) c =
          ret t) (Huniq: uniqFdef f)
  (Hreach : isReachableFromEntry f (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn1))
  (HbInF : blockInFdefB (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn1) f = true)
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
  destruct b as [? []]. destruct f as [[fa ty fid la va] bs].
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
      clear - case subcase HeqR1 HbInF Huniq HeqR' J12 J10 J11 J11' Hnotin1.
      eapply inscope_of_block_cmds_dominates_cmd__inscope_of_cmd; eauto.
        rewrite app_nil_r. auto.
        solve_in_list. 
        rewrite app_nil_r. simpl in *. eauto.
   SCase "2.2".
   eapply inscope_of_block_inscope_of_block__inscope_of_block.
   eauto. eauto. reflexivity. eauto. eauto. eauto. reflexivity.
   apply J10. eauto. eauto. eauto. eauto. eauto. eauto.
Qed.

Lemma idDominates_inscope_of_tmn__inscope_of_tmn: forall (f : fdef)
  (t : list atom) (l1 : l) (ps1 : phinodes) (cs1 : cmds) s m
  (tmn1 : terminator) id1 insn1 (id2 : id) (HwfF : wf_fdef s m f)
  (HeqR : inscope_of_tmn f (l1, stmts_intro ps1 cs1 tmn1) tmn1 =
          ret t) (Huniq: uniqFdef f)
  (Hreach : isReachableFromEntry f (l1, stmts_intro ps1 cs1 tmn1))
  (HbInF : blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true)
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
  destruct b as [? []]. destruct f as [[fa ty fid la va] bs].
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
      eapply inscope_of_block_cmds_dominates_cmd__inscope_of_tmn; eauto.
        solve_in_list.
      rewrite app_nil_r. eauto. solve_in_list. rewrite app_nil_r; eauto. 
    SCase "2.2".
      eapply inscope_of_block_inscope_of_block__inscope_of_block.
      eauto. eauto. reflexivity. eauto. eauto. eauto. reflexivity.
      apply J10. eauto. eauto. apply J13. eauto. eauto. eauto.
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
  destruct b as [? []].
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
  (Hreach : isReachableFromEntry f (l0, stmts_intro ps0 cs0 t0))
  (HBinF: blockInFdefB (l0, stmts_intro ps0 cs0 t0) f = true)
  (l1 : list atom)
  (HeqR : ret l1 = inscope_of_tmn f (l0, stmts_intro ps0 cs0 t0) t0) id1
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
    destruct b1 as [? []]. simpl in H.
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
  assert (isReachableFromEntry f (l1,s0)) as Hreachable by auto.
  clear Hreach.
  assert (blockInFdefB (l3,s1) f = true) as HBinF0.
    solve_blockInFdefB.
  assert (blockInFdefB (l1,s0) f = true) as HBinF1.
    solve_blockInFdefB.
  destruct s1 as [ps2 cs2 tmn2].
  destruct s0 as [ps3 cs3 tmn3].
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
  assert (In id2 (getStmtsLocs (stmts_intro ps2 cs2 tmn2))) as Hin9.
    solve_in_list.
  assert (In id1 (getStmtsLocs (stmts_intro ps3 cs3 tmn3))) as Hin10.
    solve_in_list.
  destruct Hdom1 as [Hdom1 | [sts1 [a1 [J1 [J2 J3]]]]].
  Case "local".
      unfold init_scope in Hdom1.
      destruct_if; try tauto.
      assert ((l3, stmts_intro ps2 cs2 tmn2) =
              (l1, stmts_intro ps3 cs3 tmn3)) as EQ.
        eapply block_eq2 with (id1:=id1); eauto 1.
         simpl.
         solve_in_list.
         apply cmds_dominates_cmd_spec in Hdom1.
         solve_in_list.
      inv EQ.
      destruct Hdom2 as [Hdom2 | [sts2 [a2 [J4 [J5 J6]]]]].
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
        assert ((a2, sts2) = (l1, stmts_intro ps3 cs3 tmn3)) as EQ.
          eapply block_eq2 with (id1:=id2); eauto 1.
            solve_blockInFdefB.
            solve_in_list.
        inv EQ.
        apply lookupBlockViaLabelFromFdef_inv in J5; auto.
        destruct J5; subst.
        apply ListSet.set_diff_elim2 in J4; auto.
        simpl in J4. auto.
  Case "remote".
      assert ((a1, sts1) = (l1, stmts_intro ps3 cs3 tmn3)) as EQ.
        eapply block_eq2 with (id1:=id1); eauto 1.
          solve_blockInFdefB.
          solve_in_list.
      inv EQ.
      apply lookupBlockViaLabelFromFdef_inv in J2; auto.
      destruct J2; subst.
      destruct Hdom2 as [Hdom2 | [sts2 [a2 [J4 [J5 J6]]]]].
      SCase "local".
        unfold init_scope in Hdom2.
        destruct_if; try tauto.
        assert ((l3, stmts_intro ps2 cs2 tmn2) =
                (l1, stmts_intro ps3 cs3 tmn3)) as EQ.
          eapply block_eq2 with (id1:=id2); eauto 1.
            simpl.
            solve_in_list.
            apply cmds_dominates_cmd_spec in Hdom2.
            solve_in_list.
        inv EQ.
        apply ListSet.set_diff_elim2 in J1; auto.
        simpl in J1. auto.
      SCase "remote".
        assert ((a2, sts2) = (l3, stmts_intro ps2 cs2 tmn2)) as EQ.
          eapply block_eq2 with (id1:=id2); eauto 1.
            solve_blockInFdefB.
            solve_in_list.
        inv EQ.
        apply lookupBlockViaLabelFromFdef_inv in J5; auto.
        assert (l3 <> l1) as Hneq.
          intro J. subst.
          apply ListSet.set_diff_elim2 in J4; auto.
          simpl in J4. auto.
        eapply sdom_acyclic in Hneq; eauto 1.
          apply ListSet.set_diff_elim1 in J4; auto.
          apply ListSet.set_diff_elim1 in J1; auto.
Qed.

Lemma idDominates_trans: forall s m f (HwfF:wf_fdef s m f)
  (HuniqF: uniqFdef f) id1 id2 id3
  (Hdom1: idDominates f id1 id2) (Hdom2: idDominates f id2 id3)
  (Hreach: (forall b, lookupBlockViaIDFromFdef f id3 = Some b ->
                      isReachableFromEntry f b)),
  idDominates f id1 id3.
Proof.
  unfold idDominates, inscope_of_id.
  intros.
  inv_mbind.
  symmetry_ctx.
  assert (blockInFdefB (l3,s1) f = true) as HBinF0.
    solve_blockInFdefB.
  assert (blockInFdefB (l1,s0) f = true) as HBinF1.
    solve_blockInFdefB.
  destruct s1 as [ps2 cs2 tmn2].
  destruct s0 as [ps3 cs3 tmn3].
  apply fold_left__spec in HeqR2.
  apply fold_left__spec in HeqR0.
  destruct HeqR2 as [_ [_ HeqR2]].
  destruct HeqR0 as [Hinit0 [HeqR3 HeqR0]].
  apply_clear HeqR2 in Hdom1.
  apply_clear HeqR0 in Hdom2.
  assert (~ In id3 (getArgsIDsOfFdef f)) as Hnotin3.
    solve_notin_getArgsIDs.
  assert (~ In id2 (getArgsIDsOfFdef f)) as Hnotin2.
    solve_notin_getArgsIDs.
  assert (In id2 (getStmtsLocs (stmts_intro ps2 cs2 tmn2))) as Hin9.
    solve_in_list.
  assert (In id3 (getStmtsLocs (stmts_intro ps3 cs3 tmn3))) as Hin10.
    solve_in_list.
  destruct (In_dec id_dec id1 (getArgsIDsOfFdef f)) as [Hin1 | Hnotin1].
  Case "id1 is in args".
    apply Hinit0. 
    apply in_getArgsIDsOfFdef__init_scope; auto.
  Case "id1 isnt in args".
    destruct Hdom1 as [Hdom1 | [sts1 [a1 [J1 [J2 J3]]]]].
    SCase "id1 local".
      unfold init_scope in Hdom1.
      destruct_if; try tauto.
      destruct Hdom2 as [Hdom2 | [sts2 [a2 [J4 [J5 J6]]]]].
      SSCase "id2 local".
        unfold init_scope in Hdom2.
        destruct_if; try tauto.
        assert ((l3, stmts_intro ps2 cs2 tmn2) =
                (l1, stmts_intro ps3 cs3 tmn3)) as EQ.
          eapply block_eq2 with (id1:=id2); eauto 1.
            simpl.
            solve_in_list.
            apply cmds_dominates_cmd_spec in Hdom2.
            solve_in_list.
        inv EQ. 
        assert (NoDup (getCmdsLocs cs3)) as Hnodup.
          solve_NoDup.
        assert (In id2 (cmds_dominates_cmd cs3 id3)) as Hin2.
          apply in_app_or in Hdom2.
          destruct Hdom2 as [Hdom2 | Hdom2]; try solve [contradict Hdom2; auto].
          apply in_app_or in Hdom2.
          destruct Hdom2 as [Hdom2 | Hdom2]; try solve [contradict Hdom2; auto].
          auto.
        apply Hinit0. 
        unfold init_scope. 
        destruct_if; try congruence.
        assert (In id2 (getCmdsLocs cs3)) as Hin.
          apply cmds_dominates_cmd_spec in Hin2.
          solve_in_list.
        eapply cmds_dominates_cmd_trans; eauto.
          apply uniqFdef__uniqBlockLocs in HBinF0; auto.
          simpl in HBinF0.
          rewrite_env ((getPhiNodesIDs ps3 ++
            getCmdsLocs cs3) ++ getTerminatorID tmn3 :: nil) in HBinF0.
          apply NoDup_split in HBinF0. tauto.
      
          solve_in_list.        
      SSCase "id2 remote".
        assert ((a2, sts2) = (l3, stmts_intro ps2 cs2 tmn2)) as EQ.
          eapply block_eq2 with (id1:=id2); eauto 1.
            solve_blockInFdefB.
            solve_in_list.
        inv EQ.
        apply HeqR3 in J5; auto.
        apply J5.
        simpl.
        apply cmds_dominates_cmd_spec' with (id0:=id2); auto.
        solve_in_list.
    SCase "id1 remote".
      destruct Hdom2 as [Hdom2 | [sts2 [a2 [J4 [J5 J6]]]]].
      SSCase "id2 local".
        unfold init_scope in Hdom2.
        destruct_if; try tauto.
        assert ((l3, stmts_intro ps2 cs2 tmn2) =
                (l1, stmts_intro ps3 cs3 tmn3)) as EQ.
          eapply block_eq2 with (id1:=id2); eauto 1.
            simpl.
            solve_in_list.
            apply cmds_dominates_cmd_spec in Hdom2.
            solve_in_list.
        inv EQ.
        apply HeqR3 in J2; auto.
      SSCase "id2 remote".
        assert ((a2, sts2) = (l3, stmts_intro ps2 cs2 tmn2)) as EQ.
          eapply block_eq2 with (id1:=id2); eauto 1.
            solve_blockInFdefB.
            solve_in_list.
        inv EQ.
        apply lookupBlockViaLabelFromFdef_inv in J5; auto.
        assert (HBinF:=J2).
        apply lookupBlockViaLabelFromFdef_inv in HBinF; auto.        
        assert (blockStrictDominates f (a1, sts1)
                                       (l3, stmts_intro ps2 cs2 tmn2)) as Hdom.
          simpl. apply ListSet.set_diff_elim1 in J1; auto.
        assert (blockStrictDominates f (l3, stmts_intro ps2 cs2 tmn2)
                                       (l1, stmts_intro ps3 cs3 tmn3)) as Hdom'.
          simpl. apply ListSet.set_diff_elim1 in J4; auto.
        assert (blockStrictDominates f (a1, sts1) 
                                       (l1, stmts_intro ps3 cs3 tmn3)) as Hdom''.
          eapply blockStrictDominates_trans 
            with (b2:=(l3, stmts_intro ps2 cs2 tmn2)); eauto.
        destruct (l_dec a1 l1); subst.
        SSSCase "a1 = l1".
          assert ((l1, sts1) = (l1, stmts_intro ps3 cs3 tmn3)) as EQ.
            eapply blockInFdefB_uniq in HBinF1; eauto.
            destruct HBinF1 as [Heq1 [Heq2 Heq3]]; subst. auto.
          inv EQ.
          assert (isReachableFromEntry f (l1, stmts_intro ps3 cs3 tmn3)) 
            as Hreach' by auto.
          eapply blockStrictDominates_isnt_refl in Hreach';
            try solve [eauto | contradict Hdom''; auto].
        SSSCase "a1 <> l1".        
          simpl in Hdom''. 
          apply HeqR3 in J2; auto.
          apply ListSet.set_diff_intro; auto.
            intro J. simpl in J. destruct J; auto.
Qed.

Lemma any_cmd_doesnt_use_following_operands: forall
  (F1 : fdef) (l3 : l) (ps1 : phinodes) (cs : list cmd)
  (tmn1 : terminator) (c : cmd)
  (Hreach : isReachableFromEntry F1 (l3, stmts_intro ps1 cs tmn1))
  (HBinF1 : blockInFdefB (l3, stmts_intro ps1 cs tmn1) F1 = true)
  s m (HwfF1 : wf_fdef s m F1) (Huniq: uniqFdef F1)
  (c1 : cmd) cs1 cs2 cs3
  (Hfollow: cs = cs1 ++ c1 :: cs2 ++ c :: cs3)
  (id_list : list id)
  (H2 : wf_operand_list
          (List.map (fun id_ : id =>
            (F1, (l3, stmts_intro ps1 cs tmn1), insn_cmd c1, id_)) id_list))
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
  | H10: (_ \/ _) \/ In _ (getArgsIDsOfFdef _) |- _ =>
     destruct H10 as [[[block' [Hlk H10]] | ?] | H10]; try congruence
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
  | H7: _ \/ _ |- _ =>
    destruct H7 as [H7 | H7]; auto
  end.
  SCase "1".
    assert (NoDup (getStmtsLocs
      (stmts_intro ps1 (cs1 ++ c1 :: cs2 ++ c :: cs3) tmn1))) as Hnodup.
      solve_NoDup.
    elimtype False.
    eapply insnDominates_spec7; eauto.

  SCase "2".
    assert (block' = (l3, stmts_intro ps1 (cs1 ++ c1 :: cs2 ++ c :: cs3) tmn1))
      as EQ.
      eapply block_eq2 with (id1:=getCmdLoc c); eauto 1.
        solve_blockInFdefB.
        solve_in_list.
        simpl. solve_in_list.
    inv EQ.
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

Ltac get_wf_value_for_simop :=
  match goal with
  | HBinF: blockInFdefB (_, stmts_intro _ (_++_::_) _) _ = _ |- _ =>
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
  | HBinF: blockInFdefB (_, stmts_intro _ (_++nil) _) _ = _ |- _ =>
    let HBinF':=fresh "HBinF'" in
    assert (HBinF':=HBinF);
    eapply wf_system__wf_tmn in HBinF'; eauto using in_middle;
    inv HBinF'
  end.

Ltac get_wf_value_for_simop_ex :=
  match goal with
  | HBinF: blockInFdefB ?B _ = _,
    Hex: exists _:_, exists _:_, exists _:_,
          ?B = (_, stmts_intro _ (_++_::_) _) |- _ =>
    let l1:=fresh "l1" in
    let ps1:=fresh "ps1" in
    let cs1:=fresh "cs1" in
      destruct Hex as [l1 [ps1 [cs1 Hex]]]; subst
  | _ => idtac
  end;
  match goal with
  | HBinF: blockInFdefB (_, stmts_intro _ (_++_::_) _) _ = _ |- _ =>
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

Lemma dom_analysis__entry_doms_others: forall S M f 
  (HwfF: wf_fdef S M f) (Huniq: uniqFdef f) entry
  (H: getEntryLabel f = Some entry),
  (forall b, b <> entry /\ reachable f b ->
     ListSet.set_In entry (AlgDom.sdom f b)).
Proof.
  intros. eapply AlgDomProps.entry_doms_others; solve_dom.
Qed.

Lemma entry_blockStrictDominates_others: forall s m f (HwfF : wf_fdef s m f)
  (Huniq: uniqFdef f) (b be : block) (Hentry : getEntryBlock f = ret be)
  (n : getBlockLabel be <> getBlockLabel b)
  (Hreach : isReachableFromEntry f b),
  blockStrictDominates f be b.
Proof.
  unfold blockStrictDominates.
  intros.
  destruct be as [l1 ? ? ?].
  destruct b as [l2 ? ? ?].
  simpl in n.
  assert (getEntryLabel f = Some l1) as Gentry.
    destruct f as [? blocks5].
    destruct blocks5; inv Hentry. auto.
  eapply dom_analysis__entry_doms_others with (b:=l2) in Gentry; eauto.
Qed.

Ltac inv_wf_block H :=
let S5 := fresh "S5" in
let M5 := fresh "M5" in
let F5 := fresh "F5" in
let l5 := fresh "l5" in 
let ps5 := fresh "ps5" in 
let cs5 := fresh "cs5" in 
let tmn5 := fresh "tmn5" in 
let HBinSMF := fresh "HBinSMF" in 
let Hwfps := fresh "Hwfps" in 
let Hwfcs := fresh "Hwfcs" in 
let Hwfi := fresh "Hwfi" in 
let EQ1 := fresh "EQ1" in
let EQ2 := fresh "EQ2" in
let EQ3 := fresh "EQ3" in 
let EQ4 := fresh "EQ4" in
inversion H as 
  [S5 M5 F5 l5 ps5 cs5 tmn5 HBinSMF Hwfps Hwfcs Hwfi EQ1 EQ2 EQ3 EQ4];
subst S5 M5 F5.

Lemma blockStrictDominates_isReachableFromEntry: forall f b1 b2 S M
  (HuniqF: uniqFdef f) (HwfF: wf_fdef S M f) 
  (Hreach: isReachableFromEntry f b1) (Hin: blockInFdefB b1 f = true)
  (Hsdom: blockStrictDominates f b2 b1),
  isReachableFromEntry f b2.
Proof.
  intros.
  unfold isReachableFromEntry in *. destruct b1, b2.
  eapply DecDom.sdom_reachable; eauto.
  simpl in Hsdom.
  eapply sdom_is_sound; eauto 1.
Qed.

Lemma blockDominates_isReachableFromEntry: forall f b1 b2 S M
  (HuniqF: uniqFdef f) (HwfF: wf_fdef S M f) 
  (Hreach: isReachableFromEntry f b1) (Hin: blockInFdefB b1 f = true)
  (Hdom: blockDominates f b2 b1),
  isReachableFromEntry f b2.
Proof.
  intros.
  unfold isReachableFromEntry in *. destruct b1, b2.
  eapply DecDom.dom_reachable; eauto.
  simpl in Hdom.
  eapply dom_is_sound; eauto 1.
    simpl. destruct Hdom; auto.
Qed.

Lemma idDominates_blockStrictDominates__blockStrictDominates :
forall S M f id1 id2 b1 b2 b (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB b f = true),
  idDominates f id1 id2 ->
  lookupBlockViaIDFromFdef f id1 = ret b1 ->
  lookupBlockViaIDFromFdef f id2 = ret b2 ->
  blockStrictDominates f b2 b ->
  blockStrictDominates f b1 b.
Proof.
  unfold idDominates, blockStrictDominates in *. intros.
  remember (lookupBlockViaIDFromFdef f id2) as R1.
  destruct R1; tinv H.
  remember (inscope_of_id f b0 id2) as R2.
  destruct R2; tinv H.
  unfold inscope_of_id in *.
  destruct b1 as [l1 [p c t]]. 
  destruct b as [l2 [p0 c0 t0]]. destruct b0 as [l3 ?]. 
  destruct b2 as [l4 [p2 c2 t2]].
  inv H1.
  symmetry in HeqR2.
  apply fold_left__spec in HeqR2.
  destruct HeqR2 as [J1 [J2 J3]].
  apply J3 in H. clear J3.
  destruct H as [H | [sts1 [l1' [J1' [J2' J3']]]]].
    assert ((l1, stmts_intro p c t) = (l4, stmts_intro p2 c2 t2)) as J'.
      clear - H H0 HeqR1 Huniq.
      symmetry in HeqR1.
      apply lookupBlockViaIDFromFdef__blockInFdefB in HeqR1.
      eapply block_eq1 in H0; eauto.
      simpl. 
      assert (~ In id1 (getArgsIDsOfFdef f)) as Hnotin.
        solve_notin_getArgsIDs.
      apply init_scope_spec2 in H; auto.
      apply cmds_dominates_cmd_spec'' in H; auto.
    inv J'. auto.
    assert ((l1, stmts_intro p c t) = (l1', sts1)) as EQ.
      apply lookupBlockViaLabelFromFdef__blockInFdefB in J2'; auto.
      eapply block_eq1 in H0; eauto.
    inv EQ.
    apply lookupBlockViaLabelFromFdef_inv in J2'; auto.
    assert (blockStrictDominates f (l1', stmts_intro p c t)
                                   (l4, stmts_intro p2 c2 t2)) as Hdom.
      apply ListSet.set_diff_elim1 in J1'; auto.
    assert (blockStrictDominates f (l4, stmts_intro p2 c2 t2)
                  (l2, stmts_intro p0 c0 t0)) as Hdom'.
      auto.
    assert (blockStrictDominates f (l1', stmts_intro p c t)
                  (l2, stmts_intro p0 c0 t0)) as Hdom''.
      eapply blockStrictDominates_trans with (b2:=(l4, stmts_intro p2 c2 t2));
        eauto.
        eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto.
    auto.
Qed.

Lemma inscope_of_blocks_with_init__id_in_reachable_block: forall s m F 
  (HwfF: wf_fdef s m F) (Huniq: uniqFdef F) b
  (Hreach : isReachableFromEntry F b)
  (HBinF : blockInFdefB b F = true)
  (contents' : ListSet.set atom)
  (Heqdefs' : contents' = AlgDom.sdom F (getBlockLabel b)) ids2 init
  (Hinscope : (fold_left (inscope_of_block F (getBlockLabel b)) contents'
    (ret init) = ret ids2))
  (Hinc: incl init (getStmtsIDs (snd b) ++ getArgsIDsOfFdef F)) vid
  (HIn: In vid ids2),
  id_in_reachable_block F vid.
Proof.
  intros.
  intros b' Hlkup'.
  assert (Hinscope':=Hinscope).
  apply fold_left__spec in Hinscope; auto.
  destruct Hinscope as [_ [_ Hinscope]].
  apply Hinscope in HIn.
  destruct HIn as [Hin | [sts1 [l1 [Hin [Hlk Hin']]]]].
    apply Hinc in Hin.
    destruct_in Hin.
      assert (b = b') as EQ.
        solve_block_eq.
      subst. auto.

      contradict Hin.
      solve_notin_getArgsIDs.
  
    assert ((l1, sts1) = b') as EQ.
      solve_block_eq.
    subst.
    destruct b.
    eapply sdom_is_sound with (l':=l1) in HBinF; eauto.
      apply lookupBlockViaLabelFromFdef_inv in Hlk; auto.
      eapply DecDom.sdom_reachable; eauto.

      apply ListSet.set_diff_elim1 in Hin. auto.
Qed.

Lemma inscope_of_id__id_in_reachable_block: forall s m F (HwfF: wf_fdef s m F) 
  (Huniq: uniqFdef F) l1 ps1 cs1 tmn1
  (Hreach : isReachableFromEntry F (l1, stmts_intro ps1 cs1 tmn1))
  (HBinF : blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) F = true) c
  (HcInCs : In c cs1) ids1
  (Hinscope: 
    ret ids1 = inscope_of_id F (l1, stmts_intro ps1 cs1 tmn1) (getCmdLoc c)) vid
  (HIn: In vid ids1),
  id_in_reachable_block F vid.
Proof.
  unfold inscope_of_id.
  intros. 
  eapply inscope_of_blocks_with_init__id_in_reachable_block in HBinF; eauto. 
    simpl. rewrite app_nil_r. eauto. apply init_scope_incl with (tmn1:=tmn1); auto.
Qed.

Lemma inscope_of_cmd__id_in_reachable_block: forall s m F (HwfF: wf_fdef s m F) 
  (Huniq: uniqFdef F) l1 ps1 cs1 tmn1
  (Hreach : isReachableFromEntry F (l1, stmts_intro ps1 cs1 tmn1))
  (HBinF : blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) F = true) c
  (HcInCs : In c cs1) ids1
  (Hinscope: ret ids1 = inscope_of_cmd F (l1, stmts_intro ps1 cs1 tmn1) c) vid
  (HIn: In vid ids1),
  id_in_reachable_block F vid.
Proof.
  unfold inscope_of_cmd.
  intros. 
  eapply inscope_of_id__id_in_reachable_block; eauto.
Qed.

Lemma idDominates_inscope_of_cmd_at_beginning__inscope_of_cmd_at_beginning: 
  forall (f : fdef) (t : list atom) (l1 : l) (ps1 : phinodes)
  (cs1 cs : cmds) (s : system) (m : module) (tmn1 : terminator) (id1 : id) 
  (instr1 : insn) (id2 : id)
  (HBinF: blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true) contents'
  (Heqdefs' : contents' = AlgDom.sdom f l1)
  (Hinscope : fold_left (inscope_of_block f l1) contents'
               (ret (getPhiNodesIDs ps1 ++ getArgsIDsOfFdef f)) = 
             ret t)
  (HwfF: wf_fdef s m f) (HuniqF: uniqFdef f)
  (Hreach: isReachableFromEntry f (l1, stmts_intro ps1 cs1 tmn1))
  (Hdom: idDominates f id1 id2)
  (Hlkup: lookupInsnViaIDFromFdef f id1 = ret instr1) (instr0 : insn),
  ret instr0 = lookupInsnViaIDFromFdef f id2 -> In id2 t -> In id1 t.
Proof.
  intros.
  destruct cs1 as [|c cs1].
    eapply idDominates_inscope_of_tmn__inscope_of_tmn; eauto.
    simpl. rewrite <- Heqdefs'. auto.

    rewrite_env (nil ++ c :: cs1) in HBinF.
    eapply idDominates_inscope_of_cmd__inscope_of_cmd; eauto 1.
    simpl. rewrite <- Heqdefs'. 
    rewrite init_scope_spec1.
      simpl. destruct_if; try congruence.

      apply uniqFdef__uniqBlockLocs in HBinF; auto.
      simpl in HBinF.
      eapply NoDup_disjoint in HBinF; simpl; eauto.
Qed.

Ltac unfold_domination_tac :=
match goal with
| Hentry: getEntryBlock ?f = ret ?be, Hdom: domination ?f _ _ |- _ =>
    unfold domination in Hdom;
    rewrite Hentry in Hdom;
    match goal with 
    | _: getEntryBlock ?f = ret (_, _) |- _ => idtac
    | _ =>
        let le := fresh "le" in
        destruct be as [le []]
    end
end.

Lemma phinodes_from_the_same_block__dont__valueDominate: forall 
  l0 ps0 cs0 tmn0 f vid1 vid2 s m (HwfF: wf_fdef s m f)
  (Huniq: uniqFdef f) (Hreach: reachable f l0)
  (HBinF: blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) f = true)
  (Hdom : valueDominates f (value_id vid1) (value_id vid2))
  (Hpin1 : In vid1 (getPhiNodesIDs ps0))
  (Hpin2 : In vid2 (getPhiNodesIDs ps0)),
  False.
Proof.
  intros.
  assert (id_in_reachable_block f vid2) as Hreach'.
    intros b2 Hlkup2.
    assert ((l0, stmts_intro ps0 cs0 tmn0) = b2) as EQ.
      solve_block_eq.
    subst. auto.
  simpl in Hdom.
  apply_clear Hdom in Hreach'.
  unfold idDominates, inscope_of_id in *.
  inv_mbind. symmetry_ctx.
  assert ((l0, stmts_intro ps0 cs0 tmn0) = (l2, s0)) as EQ.
    solve_block_eq.
  inv EQ.
  unfold init_scope in HeqR0.
  destruct_if; try congruence.
  apply fold_left__spec in H0.
  destruct H0 as [_ [_ H0]].
  apply_clear H0 in Hreach'.
  destruct Hreach' as [Hreach' | [b1 [l1' [J1 [J2 J3]]]]].
    contradict Hreach'.
    apply inGetBlockIDs__lookupBlockViaIDFromFdef with (id1:=vid1) 
      in HBinF; auto.
      solve_notin_getArgsIDs.
      simpl. solve_in_list.
    lookupBlockViaLabelFromFdef_inv_tac.
    assert ((l1', stmts_intro phinodes5 cmds5 terminator5) = 
            (l2, stmts_intro ps0 cs0 tmn0)) as EQ.
      eapply block_eq2 with (id1:=vid1); eauto.
        solve_in_list.
        simpl. solve_in_list.
    inv EQ.
    eapply sdom_is_sound with (l':=l2) in HBinF; eauto.
      apply DecDom.sdom_isnt_refl in HBinF; auto.
      apply ListSet.set_diff_elim1 in J1; auto.
Qed.

Lemma idDominates_id_in_reachable_block: forall (s : system) (m : module)
  (f : fdef) (HwfF : wf_fdef s m f) (HuniqF : uniqFdef f) (id2 : id) (id3 : id)
  (Hreach : id_in_reachable_block f id3) (Hdom : idDominates f id2 id3),
  id_in_reachable_block f id2.
Proof.
  intros.
  unfold id_in_reachable_block in *.
  intros.
  unfold idDominates in *.
  inv_mbind.
  
  unfold inscope_of_id in HeqR0.
  destruct b as [l1 [ps1 cs1 tmn1]].
  symmetry in HeqR0.
  apply fold_left__spec in HeqR0.
  destruct HeqR0 as [J1 [J2 J3]].
  apply_clear J3 in Hdom.
  assert (blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true) as HBinF1.
    symmetry in HeqR. solve_blockInFdefB. 
  assert (blockInFdefB b2 f = true) as HBinF2 by solve_blockInFdefB.
  assert (In id2 (getStmtsLocs (snd b2))) as Hin by solve_in_list.
  destruct Hdom as [Hdom | [sts2 [l2 [J4 [J5 J3]]]]].
    assert (~ In id2 (getArgsIDsOfFdef f)) as Hnotin2.
      solve_notin_getArgsIDs.
    unfold init_scope in Hdom.
    destruct_if; try tauto.
    apply Hreach.
      f_equal.
      apply block_eq2 with (id1:=id2)(f:=f); auto.
        simpl. xsolve_in_list.
        apply cmds_dominates_cmd_spec in Hdom; auto.
        xsolve_in_list.
  
    assert (b2 = (l2, sts2)) as EQ.
      apply block_eq2 with (id1:=id2)(f:=f); auto.
        solve_blockInFdefB.
        simpl. xsolve_in_list.
    subst.
    assert (Some (l1, stmts_intro ps1 cs1 tmn1) = 
            Some (l1, stmts_intro ps1 cs1 tmn1)) as EQ by auto.
    apply Hreach in EQ.
    assert (strict_domination f l2 l1) as J.
      eapply sdom_is_sound with (s3:=stmts_intro ps1 cs1 tmn1); eauto 1.
        apply ListSet.set_diff_elim1 in J4; auto.
    apply DecDom.sdom_reachable in J; auto.
Qed.

Lemma valueDominates_trans: forall s m f (HwfF:wf_fdef s m f)
  (HuniqF: uniqFdef f) v1 v2 v3
  (Hdom1: valueDominates f v1 v2) (Hdom2: valueDominates f v2 v3),
  valueDominates f v1 v3.
Proof.
  intros.
  destruct v1 as [id1|]; auto.
  destruct v2 as [id2|]; tinv Hdom1.
  destruct v3 as [id3|]; tinv Hdom2.
  simpl in *.
  intro Hreach.
  eapply idDominates_trans; eauto.
    apply Hdom1.
    assert (Hdom:=Hreach). apply Hdom2 in Hdom. 
    eapply idDominates_id_in_reachable_block; eauto.
Qed.

(* Properties of CFGs. *)
Lemma successors_codom__uniq: forall s m f 
  (HwfF : wf_fdef s m f) l0, 
  NoDup ((successors f) !!! l0).
Proof.
  intros.
  unfold XATree.successors_list.
  remember (@ATree.get (list l) l0 (successors f)) as R.
  destruct R as [scs|]; auto.
  apply successors__successors_terminator in HeqR.
  destruct HeqR as [ps0 [cs0 [tmn0 [HBinF Heq]]]]; subst.
  eapply wf_fdef__wf_tmn in HBinF; eauto.
  inv HBinF; simpl; auto.
    constructor; auto.
      simpl. intro J.
      destruct J as [J | J]; try solve [auto | congruence].
Qed.

Lemma predecessors_dom__uniq: forall s m f l0 pds
  (HeqR3 : ret pds = (XATree.make_predecessors (successors f)) ! l0)
  (HwfF0 : wf_fdef s m f),
  NoDup pds.
Proof.
  intros.
  assert (J: forall l1, NoDup ((successors f) !!! l1)).
    eapply successors_codom__uniq; eauto.
  apply make_predecessors_dom__uniq with (l0:=l0) in J; auto.
  unfold XATree.successors_list in J.
  rewrite <- HeqR3 in J. auto.
Qed.
