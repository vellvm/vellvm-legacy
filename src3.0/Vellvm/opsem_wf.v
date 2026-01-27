Require Import Ensembles.
Require Import infrastructure.
Require Import infrastructure_props.
Require Import dom_list.
Require Import analysis.
Require Import typings.
Require Import static.
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
Require Import Lattice.
Require Import Floats.
Require Import AST.
Require Import Maps.
Require Import opsem.
Require Import opsem_props.
Require Import syntax.
Require Import util.

(****************************************************************)
(* This file proves the safety result of Vellvm's semantics.    *)

Module OpsemPP. Section OpsemPP.

Context `{GVsSig : GenericValues}.

Export Opsem.
Export OpsemProps.
Import AtomSet.

(* Notations *)
Notation GVs := GVsSig.(GVsT).
Notation "gv @ gvs" :=
  (GVsSig.(instantiate_gvs) gv gvs) (at level 43, right associativity).
Notation "$ gv # t $" := (GVsSig.(gv2gvs) gv t) (at level 41).
Notation "vidxs @@ vidxss" := (in_list_gvs vidxs vidxss)
  (at level 43, right associativity).

(* A set of runtime values with type t is well-formed if 
   1) all values in the set are of size t;
   2) the set is not empty;
   3) all values match type t. *)
Inductive wf_GVs : TargetData -> GVs -> typ -> Prop :=
| wf_GVs_intro : forall TD gvs t sz,
    getTypeSizeInBits TD t = Some sz ->
    (forall gv, gv @ gvs ->
      sizeGenericValue gv = Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) ->
    GVsSig.(inhabited) gvs ->
    (forall gv, gv @ gvs -> gv_chunks_match_typ TD gv t) ->
    wf_GVs TD gvs t.

Hint Constructors wf_GVs.

(* A set of definitions that strictly dominates the program counter is
   well-formed if:
   1) the definition is defined in a reachable block;
   2) the definition has a runtime value;
   3) the definition's runtime value is well-formed. *)
Inductive wf_defs TD (f:fdef) (lc:GVsMap) : list atom -> Prop :=
| wf_defs_nil : wf_defs TD f lc nil
| wf_defs_cons : forall id1 t1 gvs1 defs',
    lookupTypViaIDFromFdef f id1 = Some t1 ->
    lookupAL _ lc id1 = Some gvs1 ->
    id_in_reachable_block f id1 ->
    wf_GVs TD gvs1 t1 ->
    wf_defs TD f lc defs' ->
    wf_defs TD f lc (id1::defs').

(* All values in locals are well-formed. *)
Definition wf_lc TD (f:fdef) (lc:GVsMap) : Prop := forall i0 gvs0 t0,
  lookupTypViaIDFromFdef f i0 = Some t0 ->
  lookupAL _ lc i0 = Some gvs0 ->
  wf_GVs TD gvs0 t0.

(* A frame ec is well-formed if
   1) the current block is reachable
   2) the block is in the current function
   3) the function is in the current module
   4) locals are well-formed
   5) the set of strictly-dominating definitions is well-formed
   6) the commands to execute are at the tail of the block
*)
Definition wf_ExecutionContext TD (ps:list product) (ec:ExecutionContext) : Prop
  :=
let '(mkEC f b cs tmn lc als) := ec in
isReachableFromEntry f b /\
blockInFdefB b f = true /\
InProductsB (product_fdef f) ps = true /\
wf_lc TD f lc /\
match cs with
| nil =>
    match inscope_of_tmn f b tmn with
    | Some ids => wf_defs TD f lc ids
    | None => False
    end
| c::_ =>
    match inscope_of_cmd f b c with
    | Some ids => wf_defs TD f lc ids
    | None => False
    end
end /\
exists l1, exists ps, exists cs',
b = (l1, stmts_intro ps (cs'++cs) tmn).

(* If the current ec's current block ends with return, the next ec's
   current command must be a call. *)
Definition wf_call (ec:@ExecutionContext GVsSig) (ecs:@ECStack GVsSig) : Prop :=
let '(mkEC f _ _ _ _ _) := ec in
forall b, blockInFdefB b f ->
let '(_, stmts_intro _ _ tmn) := b in
match tmn with
| insn_return _ _ _ | insn_return_void _ =>
    match ecs with
    | nil => True
    | mkEC f' b' (insn_call _ _ _ _ _ _ _ ::_) tmn' lc' als'::ecs'
        => True
    | _ => False
    end
| _ => True
end.

Fixpoint wf_ECStack TD (ps:list product) (ecs:ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' =>
    wf_ExecutionContext TD ps ec /\ wf_ECStack TD ps ecs' /\ wf_call ec ecs'
end.

(* Stack is never empty, and must be well-formed. *)
Definition wf_State (cfg:Config) (S:State) : Prop :=
let '(mkCfg _ (los, nts) ps _ _ ) := cfg in
let '(mkState ecs _) := S in
ecs <> nil /\
wf_ECStack (los,nts) ps ecs.

(* A configuration is well-formed if
   1) named types are well-formed
   2) globals are well-formed
   3) the system is well-formed
   4) the current module is in the system
*)
Definition wf_Config (cfg:Config) : Prop :=
let '(mkCfg s (los, nts) ps gl _ ) := cfg in
wf_namedts s (los,nts) /\
wf_global (los,nts) s gl /\
wf_system s /\
moduleInSystemB (module_intro los nts ps) s = true.

(* Properties of inhabited *)
Lemma const2GV__inhabited : forall TD gl c gvs,
  const2GV TD gl c = Some gvs -> GVsSig.(inhabited) gvs.
Proof.
  intros TD gl c gvs H.
  unfold const2GV in H.
  destruct (_const2GV TD gl c) as [[gv ?]|]; inv H.
    eauto using GVsSig.(cgv2gvs__inhabited).
Qed.

Lemma getOperandValue__inhabited : forall los nts s ps f v t lc gl gvs,
  wf_lc (los, nts) f lc ->
  wf_value s (module_intro los nts ps) f v t ->
  getOperandValue (los, nts) v lc gl = Some gvs ->
  GVsSig.(inhabited) gvs.
Proof.
  intros los nts s ps f v t lc gl gvs Hwflc Hwfv Hget.
  inv Hwfv; simpl in Hget; eauto using const2GV__inhabited.
    unfold wf_lc in Hwflc.
    match goal with
    | H7: lookupTypViaIDFromFdef _ _ = _ |- _ =>
      eapply Hwflc in H7; eauto;
      inv H7; auto
    end.
Qed.

Lemma values2GVs__inhabited : forall S los nts f lc (Hwflc: wf_lc (los,nts) f lc)
  gl Ps idxs vidxs,
  wf_value_list
    (List.map
      (fun (p : sz * value) =>
        let '(sz_, value_) := p in
          (S, module_intro los nts Ps, f, value_,
            typ_int Size.ThirtyTwo)) idxs) ->
  values2GVs (los,nts) idxs lc gl = Some vidxs ->
  exists vidxs0, vidxs0 @@ vidxs.
Proof.
  induction idxs as [|[s v] idxs]; simpl; intros vidxs Hwfvs Hv2gvs.
    inv Hv2gvs. exists nil. simpl. auto.

    remember (getOperandValue (los,nts) v lc gl) as R.
    destruct R; tinv Hv2gvs.
    remember (values2GVs (los,nts) idxs lc gl) as R1.
    destruct R1; inv Hv2gvs.
    symmetry in HeqR1. symmetry in HeqR.
    rewrite wf_value_list_cons_iff in Hwfvs. destruct Hwfvs.
    destruct (@IHidxs l0) as [vidxs0 J]; auto.
    eapply getOperandValue__inhabited in HeqR; eauto.
    apply GVsSig.(inhabited_inv) in HeqR.
    destruct HeqR as [gv HeqR].
    exists (gv::vidxs0). simpl. simpl; auto.
Qed.

(* Properties of type size *)
Lemma const2GV__getTypeSizeInBits : forall S TD c t gl gvs gv
  (hwfc: wf_const S TD c t)
  (Hc2g: const2GV TD gl c = Some gvs),
  gv @ gvs ->
  wf_global TD S gl ->
  exists sz,
    getTypeSizeInBits TD t = Some sz /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof.
  intros.
  unfold const2GV in Hc2g.
  remember (_const2GV TD gl c) as R.
  destruct R as [[]|]; inv Hc2g.
  symmetry in HeqR.
  destruct TD.
  unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment.
  eapply const2GV__getTypeSizeInBits_aux in HeqR; eauto.
  destruct HeqR as [Heq [sz [al [J1 J2]]]]; subst.
  exists sz.
  rewrite J1.
  split; auto.
    eapply GVsSig.(cgv2gvs__getTypeSizeInBits); eauto using wf_const__wf_typ.
Qed.

(* Properties of matching chunks *)
Lemma const2GV__matches_chunks : forall S TD c t gl gvs gv
  (hwfc: wf_const S TD c t)
  (Hc2g: const2GV TD gl c = Some gvs),
  gv @ gvs ->
  wf_global TD S gl ->
  gv_chunks_match_typ TD gv t.
Proof.
  intros.
  unfold const2GV in Hc2g.
  remember (_const2GV TD gl c) as R.
  destruct R as [[]|]; inv Hc2g.
  symmetry in HeqR.
  destruct TD.
  eapply const2GV__matches_chunks_aux in HeqR; eauto.
  destruct HeqR as [J1 J2]; subst.
  eapply GVsSig.(cgv2gvs__matches_chunks); eauto using wf_const__wf_typ.
Qed.

(* Properties of wf_gvs *)
Lemma getOperandValue__wf_gvs : forall (los:layouts) (nts:namedts) s ps f v t lc
  gl gvs,
  wf_global (los,nts) s gl ->
  wf_lc (los,nts) f lc ->
  wf_value s (module_intro los nts ps) f v t ->
  getOperandValue (los,nts) v lc gl = Some gvs ->
  wf_GVs (los,nts) gvs t.
Proof.
  intros los nts s ps f v t lc gl gvs Hwfg Hwflc Hwfv Hget.
  assert (J:=Hget).
  eapply getOperandValue__inhabited in J; eauto.
  inv Hwfv;  simpl in Hget.
    assert (H7':=H7).
    eapply wf_typ__getTypeSizeInBits_and_Alignment in H7; eauto.
    destruct H7 as [sz [al [J1 J2]]].
    eapply wf_GVs_intro with (sz:=sz);
      eauto using GVsSig.(cgv2gvs__getTypeSizeInBits).
      unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts in *.
      rewrite J1. auto.

      intros.
      eapply const2GV__getTypeSizeInBits in Hget; eauto.
      destruct Hget as [sz0 [J3 J4]].
      unfold getTypeSizeInBits in J3.
      rewrite J1 in J3. inv J3. auto.

      intros.
      eapply const2GV__matches_chunks; eauto.

    unfold wf_lc in Hwflc.
    match goal with
    | H7: lookupTypViaIDFromFdef _ _ = _ |- _ =>
      eapply Hwflc in H7; eauto
    end.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec1_aux : forall s Ps los nts f
    b gl lc id1 t l3 cs tmn ps2 ps1 lc'
  (Hreach: isReachableFromEntry f (l3, stmts_intro (ps1++ps2) cs tmn)),
  wf_lc (los,nts) f lc ->
  Some lc' = getIncomingValuesForBlockFromPHINodes (los,nts) ps2 b gl lc ->
  List.In id1 (getPhiNodesIDs ps2) ->
  uniqFdef f ->
  blockInFdefB (l3, stmts_intro (ps1++ps2) cs tmn) f ->
  wf_global (los, nts) s gl ->
  wf_phinodes s (module_intro los nts Ps) f
    (l3, stmts_intro (ps1++ps2) cs tmn) ps2 ->
  lookupTypViaIDFromFdef f id1 = ret t ->
  id_in_reachable_block f id1 /\
  exists gvs, lookupAL _ lc' id1 = Some gvs /\ wf_GVs (los,nts) gvs t.
Proof.
  intros s Ps los nts f b gl lc id1 t l3 cs tmn ps2 ps1 lc' Hreach Hwflc H H0
    Huniq Hbinf Hwfg Hwfps Hlk.
  assert (Huniq':=Hbinf).
  apply uniqFdef__uniqBlockLocs in Huniq'; auto.
  simpl in Huniq'.
  apply NoDup_split in Huniq'.
  destruct Huniq' as [Huniq' _].
  assert (In id1 (getPhiNodesIDs (ps1++ps2))) as Hin.
    rewrite getPhiNodesIDs_app.
    apply in_app_iff; auto.
  generalize dependent lc'.
  generalize dependent ps1.
  induction ps2; simpl in *; intros.
    inversion H0.

    assert (J:=Hbinf).
    eapply lookupTypViaIDFromFdef__lookupTypViaIDFromPhiNodes in J; eauto.
    destruct a as [i0 t0 l0].
    simpl in H0. simpl in J.
    inv Hwfps.
    match goal with
    | H7: wf_insn _ _ _ _ _ |- _ => inv H7
    end.
    destruct H0 as [H0 | H0]; subst.
      split.
        eapply block_id_in_reachable_block; eauto 1; simpl; auto.
          solve_in_list.

        rewrite NoDup_lookupTypViaIDFromPhiNodes in J; auto.
        inv J. inv_mbind.
        exists g. simpl.
        destruct (id1 == id1) as [e' | n]; try solve [contradict n; auto].
          split; auto.
        eapply getOperandValue__wf_gvs; eauto.
        find_wf_value_list.
        eapply wf_value_list__getValueViaBlockFromValuels__wf_value; eauto.


      remember (getValueViaBlockFromValuels l0 b) as R0.
      destruct R0; try solve [inversion H].
        remember (getOperandValue (los,nts) v lc gl) as R.
        destruct R; tinv H.
        remember (getIncomingValuesForBlockFromPHINodes (los,nts) ps2 b gl lc)
          as R.
        destruct R; inversion H; subst.
        simpl.
        destruct (id1==i0); subst.
          clear - Huniq' H0.
          rewrite getPhiNodesIDs_app in Huniq'.
          apply NoDup_split in Huniq'.
          destruct Huniq' as [_ Huniq'].
          inv Huniq'. congruence.

          eapply IHps2 with (ps1:=ps1 ++ [insn_phi i0 t0 l0]); simpl_env; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec1 : forall s Ps los nts f b
    gl lc id1 t l3 cs tmn ps lc'
  (Hreach: isReachableFromEntry f (l3, stmts_intro ps cs tmn)),
  wf_lc (los,nts) f lc ->
  Some lc' = getIncomingValuesForBlockFromPHINodes (los,nts) ps b gl lc ->
  In id1 (getPhiNodesIDs ps) ->
  uniqFdef f ->
  Some (stmts_intro ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_global (los, nts) s gl ->
  wf_fdef s (module_intro los nts Ps) f ->
  lookupTypViaIDFromFdef f id1 = ret t ->
  id_in_reachable_block f id1 /\
  exists gvs, lookupAL _ lc' id1 = Some gvs /\ wf_GVs (los,nts) gvs t.
Proof.
  intros.
  assert (blockInFdefB (l3, stmts_intro ps cs tmn) f) as Hbinf.
    symmetry in H3.
    apply lookupBlockViaLabelFromFdef_inv in H3; auto.
    destruct H3; eauto.
  eapply getIncomingValuesForBlockFromPHINodes_spec1_aux with (ps1:=nil);
    eauto using wf_fdef__wf_phinodes.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec2_aux : forall s los nts Ps f
  b gl lc l3 cs tmn (Hwflc: wf_lc (los, nts) f lc)
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f) ps2 ps1 rs,
  blockInFdefB (l3, stmts_intro (ps1++ps2) cs tmn) f ->
  wf_phinodes s (module_intro los nts Ps) f
    (l3, stmts_intro (ps1++ps2) cs tmn) ps2 ->
  Some rs = getIncomingValuesForBlockFromPHINodes (los, nts) ps2 b gl lc ->
  (forall id0 gvs t0, In (id0,gvs) rs ->
     lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_GVs (los, nts) gvs t0).
Proof.
  intros s los nts Ps f b gl lc l3 cs tmn Hwflc Hwfg Huniq ps2 ps1 rs Hbinf.
  assert (Huniq':=Hbinf).
  apply uniqFdef__uniqBlockLocs in Huniq'; auto.
  simpl in Huniq'.
  apply NoDup_split in Huniq'.
  destruct Huniq' as [Huniq' _].
  generalize dependent rs.
  generalize dependent ps1.
  induction ps2; intros ps1 Hbinf Hnup rs Hwfps H id0 gv t0 Hin Hlkup;
    simpl in *.
    inv H. inv Hin.

    destruct a as [i0 t l0].
    remember (getValueViaBlockFromValuels l0 b) as R1.
    inv_mbind.
    inv Hwfps. simpl in Hin. destruct Hin as [Hin | Hin].
      inv Hin.
      match goal with
        | H5: wf_insn _ _ _ _ _ |- _ => inv H5
      end.
      assert (J:=Hbinf).
      eapply lookupTypViaIDFromFdef__lookupTypViaIDFromPhiNodes in J; eauto.
        simpl in J.
        rewrite NoDup_lookupTypViaIDFromPhiNodes in J; auto.
        inv J.
        symmetry in HeqR. eapply getOperandValue__wf_gvs in HeqR; eauto.
        find_wf_value_list.
        eapply wf_value_list__getValueViaBlockFromValuels__wf_value with
          (l2 := l0); eauto.

        simpl. rewrite getPhiNodesIDs_app.
        apply in_app_iff; simpl; auto.

     match goal with
       | H6: wf_phinodes _ _ _ _ _ |-_ =>
         rewrite_env ((ps1 ++ [insn_phi i0 t l0]) ++ ps2) in H6;
         eapply IHps2 in H6; simpl_env; eauto
     end.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec2 : forall s los nts Ps f b
  gl lc l3 cs tmn (Hwflc: wf_lc (los, nts) f lc)
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f) ps rs,
  Some (stmts_intro ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_global (los, nts) s gl ->
  wf_fdef s (module_intro los nts Ps) f ->
  Some rs = getIncomingValuesForBlockFromPHINodes (los, nts) ps b gl lc ->
  (forall id0 gvs t0, In (id0,gvs) rs ->
     lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_GVs (los, nts) gvs t0).
Proof.
  intros.
  assert (blockInFdefB (l3, stmts_intro ps cs tmn) f) as Hbinf.
    symmetry in H.
    apply lookupBlockViaLabelFromFdef_inv in H; auto.
    destruct H; eauto.
  eapply getIncomingValuesForBlockFromPHINodes_spec2_aux with (ps1:=nil);
    eauto using wf_fdef__wf_phinodes.
Qed.

Lemma updateValuesForNewBlock_spec2 : forall TD f lc id1 gv t,
  lookupAL _ lc id1 = Some gv ->
  lookupTypViaIDFromFdef f id1 = Some t ->
  wf_lc TD f lc ->
  forall rs,
  (forall id0 gv t0,
     In (id0,gv) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_GVs TD gv t0) ->
  exists t', exists gv',
    lookupTypViaIDFromFdef f id1 = Some t' /\
    lookupAL _ (updateValuesForNewBlock rs lc) id1 = Some gv' /\
    wf_GVs TD gv' t'.
Proof.
  induction rs; intros; simpl in *.
    exists t. exists gv. eauto.

    destruct a.
    destruct (id1==i0); subst.
      exists t. exists g. rewrite lookupAL_updateAddAL_eq; eauto.
      rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Fixpoint wf_params TD (gvs:list GVs) (lp:params) : Prop :=
match (gvs, lp) with
| (nil, nil) => True
| (gv::gvs', ((t, _), _)::lp') => wf_GVs TD gv t /\ wf_params TD gvs' lp'
| _ => False
end.

Lemma params2GVs_wf_gvs : forall los nts S
  Ps F gl lc (Hwfc : wf_lc (los,nts) F lc)
  (Hwfg : wf_global (los, nts) S gl) tvs lp gvs,
  wf_value_list
    (List.map
      (fun p : typ * attributes * value =>
        let '(typ_', attr, value_'') := p in
          (S, (module_intro los nts Ps), F, value_'', typ_'))
                tvs) ->
  lp = List.map
        (fun p : typ * attributes * value =>
          let '(typ_', attr, value_'') := p in (typ_', attr, value_''))
        tvs ->
  params2GVs (los,nts) lp lc gl = Some gvs -> wf_params (los,nts) gvs lp.
Proof.
  induction tvs as [|[[t a] v] tvs]; intros lp gvs Hwfvs Heq Hp2gv;
  subst; simpl in *.

    inv Hp2gv. simpl. auto.

    remember (getOperandValue (los,nts) v lc gl) as R0.
    destruct R0; try solve [inv Hp2gv].
    match goal with
      | [ H : context[?t] |- _ ] =>
        match t with
          | params2GVs _ _ _ _ =>
            remember t as R
        end
    end.
    destruct R; inv Hp2gv.
    simpl. split.
      eapply getOperandValue__wf_gvs; eauto.
      eapply (Hwfvs (_, _, _, _, _)). left. eauto.

      eapply IHtvs; eauto.
      intros p Hp. apply Hwfvs. right. trivial.
Qed.

Lemma wf_params_spec : forall TD gvs lp,
  wf_params TD gvs lp -> forall gv, In gv gvs -> GVsSig.(inhabited) gv.
Proof.
  induction gvs; simpl; intros.
    inv H0.

    destruct lp as [|[[]]]; tinv H.
    destruct H as [J1 J2].
    destruct H0 as [H0 | H0]; subst; eauto.
      inv J1; auto.
Qed.

(* Properties of wf_defs *)
Lemma wf_defs_elim : forall TD ids1 F lc,
  wf_defs TD F lc ids1 ->
  forall id1, List.In id1 ids1 ->
  id_in_reachable_block F id1 /\
  exists t1, exists gvs1,
    lookupTypViaIDFromFdef F id1 = Some t1 /\
    lookupAL _ lc id1 = Some gvs1 /\
    wf_GVs TD gvs1 t1.
Proof.
  induction ids1; intros; simpl in H0; inv H0.
    inv H. split; auto. eauto.
    inv H. eauto.
Qed.

Lemma wf_defs_intro : forall TD ids1 F lc,
  (forall id1, List.In id1 ids1 ->
   id_in_reachable_block F id1 /\
   exists t1, exists gvs1,
     lookupTypViaIDFromFdef F id1 = Some t1 /\
     lookupAL _ lc id1 = Some gvs1 /\
     wf_GVs TD gvs1 t1) ->
  wf_defs TD F lc ids1.
Proof.
  induction ids1; intros.
    apply wf_defs_nil.

    destruct (@H a) as [J4 [t1 [gvs1 [J1 [J2 J3]]]]]; simpl; auto.
    eapply wf_defs_cons; eauto.
      apply IHids1.
      intros id1 J.
      apply H. simpl. auto.
Qed.

Lemma wf_defs_eq : forall TD ids2 ids1 F' lc',
  set_eq ids1 ids2 ->
  wf_defs TD F' lc' ids1 ->
  wf_defs TD F' lc' ids2.
Proof.
  intros.
  apply wf_defs_intro.
  intros id1 Hin.
  destruct H as [J1 J2].
  eapply wf_defs_elim in H0; eauto.
Qed.

Lemma wf_defs_updateAddAL : forall TD g F' lc' ids1 ids2 i1 t1
  (Hreach: id_in_reachable_block F' i1),
  wf_defs TD F' lc' ids1 ->
  set_eq (i1::ids1) ids2 ->
  lookupTypViaIDFromFdef F' i1 = ret t1 ->
  wf_GVs TD g t1 ->
  wf_defs TD F' (updateAddAL _ lc' i1 g) ids2.
Proof.
  intros TD g F' lc' ids1 ids2 i1 t1 Hreach HwfDefs Heq Hlkup Hwfgvs.
  apply wf_defs_intro.
  intros id1 Hin.
  destruct Heq as [Hinc1 Hinc2].
  apply Hinc2 in Hin.
  simpl in Hin.
  destruct (eq_dec i1 id1); subst.
    split; auto.
    exists t1. exists g.
    split; auto.
    split; auto.
      apply lookupAL_updateAddAL_eq; auto.

    destruct Hin as [Eq | Hin]; subst; try solve [contradict n; auto].
    eapply wf_defs_elim in HwfDefs; eauto.
    destruct HwfDefs as [J4 [t2 [gv2 [J1 [J2 J3]]]]].
    split; auto.
    exists t2. exists gv2.
    split; auto.
    split; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma wf_defs_br_aux : forall lc l' ps' cs' lc' F tmn' gl los nts Ps s
  (l3 : l)
  (ps : phinodes)
  (cs : list cmd) tmn
  (Hreach: isReachableFromEntry F (l', stmts_intro ps' cs' tmn'))
  (Hlkup : Some (stmts_intro ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hswitch : switchToNewBasicBlock (los,nts) (l', stmts_intro ps' cs' tmn')
         (l3, stmts_intro ps cs tmn) gl lc = ret lc')
  (t : list atom)
  (Hwfdfs : wf_defs (los,nts) F lc t)
  (ids0' : list atom)
  (Hwflc : wf_lc (los,nts) F lc)
  (Hwfg : wf_global (los, nts) s gl)
  (HwfF : wf_fdef s (module_intro los nts Ps) F)
  (Huniq : uniqFdef F)
  (Hinc : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) t),
  wf_defs (los,nts) F lc' ids0'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  apply wf_defs_intro.
  intros id1 Hid1.
  remember (getIncomingValuesForBlockFromPHINodes (los,nts) ps'
                (l3, stmts_intro ps cs tmn) gl lc) as R1.
  destruct R1; inv Hswitch.
  destruct (In_dec eq_atom_dec id1 (getPhiNodesIDs ps')) as [Hin | Hnotin].
    assert (J:=Hlkup).
    eapply InPhiNodes_lookupTypViaIDFromFdef in Hlkup; eauto.
    destruct Hlkup as [t1 Hlkup].
    eapply getIncomingValuesForBlockFromPHINodes_spec1 in HeqR1; eauto.
    destruct HeqR1 as [Hinrch [gv [HeqR1 Hwfgv]]].
    split; auto.
    eapply updateValuesForNewBlock_spec4 in HeqR1; eauto.

    apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) in Hnotin;
      auto.
    apply Hinc in Hnotin.
    apply wf_defs_elim with (id1:=id1) in Hwfdfs; auto.
    destruct Hwfdfs as [J4 [t1 [gv1 [J1 [J2 J3]]]]].
    eapply updateValuesForNewBlock_spec2 with (rs:=l0) in J2; eauto.
      eapply getIncomingValuesForBlockFromPHINodes_spec2; eauto.
Qed.

Lemma inscope_of_tmn_br_aux : forall F l3 ps cs tmn ids0 ps' cs' tmn' l0
  s los nts Ps lc lc' gl
(Hreach: isReachableFromEntry F (l0, stmts_intro ps' cs' tmn')),
wf_global (los, nts) s gl ->
wf_lc (los,nts) F lc ->
wf_fdef s (module_intro los nts Ps) F ->
uniqFdef F ->
blockInFdefB (l3, stmts_intro ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (l3, stmts_intro ps cs tmn) tmn ->
Some (stmts_intro ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (los,nts) (l0, stmts_intro ps' cs' tmn')
  (l3, stmts_intro ps cs tmn) gl lc = Some lc' ->
wf_defs (los,nts) F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (l0, stmts_intro ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (l0, stmts_intro ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs (los,nts) F lc' ids0'.
Proof.
  intros F l3 ps cs tmn ids0 ps' cs' tmn' l0 s los nts Ps lc lc' gl
    Hreach Hwfg Hwflc HwfF Huniq HBinF Hsucc Hinscope Hlkup Hswitch Hwfdfs.
  symmetry in Hlkup.
  assert (J:=Hlkup).
  apply lookupBlockViaLabelFromFdef_inv in J; auto.
  unfold inscope_of_tmn in Hinscope.
  unfold inscope_of_tmn. unfold inscope_of_cmd, inscope_of_id.
  destruct F as [fh bs].

  assert (incl (AlgDom.sdom (fdef_intro fh bs) l0)
     (l3::(AlgDom.sdom (fdef_intro fh bs) l3))) as Hsub.
    clear - HBinF Hsucc Huniq HwfF.
    eapply dom_successors; eauto.

  assert (J1:=AlgDom.sdom_in_bound fh bs l0).
  destruct fh as [f t i0 la va].
  apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++
    getArgsIDs la)(fh:=fheader_intro f t i0 la va)(bs:=bs) (l0:=l0) in J1.
  destruct J1 as [r J1].
  exists r.

  assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
    as Jinc.
    clear - Hinscope J1 Hsub HBinF Huniq.
    eapply inscope_of_tmn__inscope_of_cmd_at_beginning in J1; eauto.

  destruct cs'.
  Case "cs'=nil".
    simpl.
    split; auto.
    split; auto.
      eapply wf_defs_br_aux; eauto.

  Case "cs'<>nil".
    assert (~ In (getCmdLoc c) (getPhiNodesIDs ps')) as Hnotin.
      apply uniqFdef__uniqBlockLocs in J; auto.
      simpl in J.
      eapply NoDup_disjoint in J; simpl; eauto.
    rewrite init_scope_spec1; auto.
    unfold cmds_dominates_cmd. simpl.
    destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_ | n];
      try solve [contradict n; auto].
    simpl_env.
    split; auto.
    split; auto.
      eapply wf_defs_br_aux; eauto.
Qed.

Lemma inscope_of_tmn_br_uncond : forall F l3 ps cs ids0 ps' cs' tmn' l0
  s los nts Ps lc lc' gl bid
(Hreach: isReachableFromEntry F (l0, stmts_intro ps' cs' tmn')),
wf_global (los, nts) s gl ->
wf_lc (los,nts) F lc ->
wf_fdef s (module_intro los nts Ps) F ->
uniqFdef F ->
blockInFdefB (l3, stmts_intro ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (l3, stmts_intro ps cs (insn_br_uncond bid l0))
  (insn_br_uncond bid l0) ->
Some (stmts_intro ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (los,nts) (l0, stmts_intro ps' cs' tmn')
  (l3, stmts_intro ps cs (insn_br_uncond bid l0)) gl lc = Some lc' ->
wf_defs (los,nts) F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (l0, stmts_intro ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (l0, stmts_intro ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs (los,nts) F lc' ids0'.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

Lemma inscope_of_tmn_br : forall F l0 ps cs bid l1 l2 ids0 ps' cs' tmn' Cond
  c los nts Ps gl lc s lc'
(Hreach: isReachableFromEntry F 
         ((if isGVZero (los,nts) c then l2 else l1), stmts_intro ps' cs' tmn')),
wf_global (los, nts) s gl ->
wf_lc (los,nts) F lc ->
wf_fdef s (module_intro los nts Ps) F ->
uniqFdef F ->
blockInFdefB (l0, stmts_intro ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (l0, stmts_intro ps cs (insn_br bid Cond l1 l2))
  (insn_br bid Cond l1 l2) ->
Some (stmts_intro ps' cs' tmn') =
       (if isGVZero (los,nts) c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
switchToNewBasicBlock (los,nts) 
  ((if isGVZero (los,nts) c then l2 else l1), stmts_intro ps' cs' tmn')
  (l0, stmts_intro ps cs (insn_br bid Cond l1 l2)) gl lc = Some lc' ->
wf_defs (los,nts) F lc ids0 ->
exists ids0',
  match cs' with
  | nil => 
      Some ids0' = 
        inscope_of_tmn F 
          ((if isGVZero (los,nts) c then l2 else l1), stmts_intro ps' cs' tmn') tmn'
  | c'::_ => 
      Some ids0' = 
        inscope_of_cmd F 
          ((if isGVZero (los,nts) c then l2 else l1), stmts_intro ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs (los,nts) F lc' ids0'.
Proof.
  intros.
  remember (isGVZero (los,nts) c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

(* Properties of wf_lc *)
Lemma updateValuesForNewBlock_spec3 : forall TD f lc,
  wf_lc TD f lc ->
  forall rs,
  (forall id0 gv t0,
     In (id0,gv) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_GVs TD gv t0) ->
  wf_lc TD f (updateValuesForNewBlock rs lc).
Proof.
  induction rs; intros; simpl in *; auto.
    destruct a.
    intros x gvx tx Htyp Hlk.
    destruct (i0==x); subst.
      rewrite lookupAL_updateAddAL_eq in Hlk. inv Hlk. eauto.

      rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
      eapply IHrs in Hlk; eauto.
Qed.

Lemma wf_lc_br_aux : forall s los nts Ps f sts3 b2 gl lc lc' l3
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f)
  (Hswitch : switchToNewBasicBlock (los, nts) (l3, sts3) b2 gl lc = ret lc')
  (Hlkup : Some sts3 = lookupBlockViaLabelFromFdef f l3)
  (Hwfg : wf_global (los, nts) s gl)
  (HwfF : wf_fdef s (module_intro los nts Ps) f)
  (Hwflc : wf_lc (los, nts) f lc),
  wf_lc (los, nts) f lc'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. 
  remember (getIncomingValuesForBlockFromPHINodes (los, nts)
              (getPHINodesFromBlock (l3, sts3)) b2 gl lc) as R1.
  destruct R1; inv Hswitch.
  apply updateValuesForNewBlock_spec3; auto.
    destruct sts3.
    eapply getIncomingValuesForBlockFromPHINodes_spec2; simpl; eauto.
Qed.

Lemma wf_lc_updateAddAL : forall TD f lc gv i0 t,
  wf_lc TD f lc ->
  lookupTypViaIDFromFdef f i0 = ret t ->
  wf_GVs TD gv t ->
  wf_lc TD f (updateAddAL _ lc i0 gv).
Proof.
  intros.
  intros x gvx tx Htyp Hlk.
  destruct (eq_atom_dec i0 x); subst.
    rewrite lookupAL_updateAddAL_eq in Hlk.
    inv Hlk. rewrite H0 in Htyp. inv Htyp. auto.

    rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto.
Qed.

Lemma gundef_cgv2gvs__wf_gvs : forall los nts gv s t
  (Hwft : wf_typ s (los, nts) t)
  (HeqR : ret gv = gundef (los, nts) t),
  wf_GVs (los, nts) ($ gv # t $) t.
Proof.
  intros.
  assert (J:=HeqR).
  eapply gundef__getTypeSizeInBits in HeqR; eauto.
  destruct HeqR as [sz1 [al1 [J1 J2]]].
  apply wf_GVs_intro with (sz:=sz1); auto.
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
           getTypeSizeInBits_and_Alignment_for_namedts.
    rewrite J1. auto.
    eapply GVsSig.(gv2gvs__getTypeSizeInBits); eauto.
    eapply GVsSig.(gv2gvs__inhabited); eauto.
    eapply GVsSig.(gv2gvs__matches_chunks); eauto.
      eapply gundef__matches_chunks in J; eauto.
Qed.

Lemma fit_gv_gv2gvs__wf_gvs_aux : forall los nts gv s t gv0
  (Hwft : wf_typ s (los,nts) t)
  (HeqR : ret gv = fit_gv (los, nts) t gv0),
  wf_GVs (los, nts) ($ gv # t $) t.
Proof.
  intros.
  assert (J:=HeqR).
  eapply fit_gv__getTypeSizeInBits in HeqR; eauto.
  destruct HeqR as [sz [J1 J2]].
  apply wf_GVs_intro with (sz:=sz); auto.
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
           getTypeSizeInBits_and_Alignment_for_namedts in J1.
    remember (_getTypeSizeInBits_and_Alignment los
           (_getTypeSizeInBits_and_Alignment_for_namedts los nts true)
           true t) as R.
    destruct R as [[]|]; inv J1.
    eapply GVsSig.(gv2gvs__getTypeSizeInBits); eauto.

    eapply GVsSig.(gv2gvs__inhabited); eauto.

    eapply GVsSig.(gv2gvs__matches_chunks); eauto.
      eapply fit_gv__matches_chunks in J; eauto.
Qed.

Lemma lift_fit_gv__wf_gvs : forall los nts g s t t0 gv
  (Hwft : wf_typ s (los, nts) t) (Hwfg : wf_GVs (los, nts) g t0)
  (HeqR : GVsSig.(lift_op1) (fit_gv (los, nts) t) g t = Some gv),
  wf_GVs (los, nts) gv t.
Proof.
  intros.
  assert (J:=Hwft).
  eapply wf_typ__getTypeSizeInBits_and_Alignment in J; eauto.
  destruct J as [sz [al [J1 [J2 J3]]]].
  apply wf_GVs_intro with (sz:=sz); auto.
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
           getTypeSizeInBits_and_Alignment_for_namedts in *.
    rewrite J1. auto.

    eapply GVsSig.(lift_op1__getTypeSizeInBits); eauto.
    intros. symmetry in H0.
    eapply fit_gv__getTypeSizeInBits in H0; eauto.
    destruct H0 as [sz0 [H1 H2]].
    unfold getTypeSizeInBits in H1.
    rewrite J1 in H1. inv H1. auto.

    inv Hwfg.
    eapply GVsSig.(lift_op1__inhabited) in HeqR; eauto.
    intro x. eapply fit_gv__total; eauto.

    inv Hwfg.
    eapply GVsSig.(lift_op1__matches_chunks); eauto.
    intros.
    eapply fit_gv__matches_chunks; eauto.
Qed.

Ltac find_middle_element :=
  match goal with
    | H: _ ++ ?e :: _ = ?l |- _ =>
      assert (In e l) as J by
        (rewrite <- H; apply in_or_app; simpl; auto)
  end.

Lemma initializeFrameValues__wf_lc_aux : forall los nts s fattr ft fid va
  bs2 la2 la1 lc1
  (Huniq: NoDup (getArgsIDs (la1 ++ la2)))
  (HwfF: wf_fheader s (los, nts) (fheader_intro fattr ft fid (la1 ++ la2) va))
  (Hwflc: wf_lc (los,nts)
     (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2) lc1)
  lc2 gvs2 lp2,
  _initializeFrameValues (los,nts) la2 gvs2 lc1 = Some lc2 ->
  wf_params (los,nts) gvs2 lp2 ->
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2)
    lc2.
Proof.
  induction la2; simpl; intros la1 lc1 Huniq HwfF Hwflc lc2 gvs2 lp2 Hin Hpar.
    inv Hin. auto.

    simpl_prod.
    destruct gvs2; simpl in *; subst.
      remember (_initializeFrameValues (los,nts) la2 nil lc1) as R1.
      destruct R1 as [lc'|]; tinv Hin.
      remember (gundef (los,nts) t) as R2.
      destruct R2; inv Hin.
        apply wf_lc_updateAddAL with (t:=t); eauto.
          rewrite_env ((la1++[(t,a,i0)])++la2).
          eapply IHla2; simpl_env; eauto.

          simpl.
          rewrite NoDup_lookupTypViaIDFromArgs; auto.

          inv HwfF. find_middle_element.
          eapply gundef_cgv2gvs__wf_gvs; eauto.
          solve_wf_typ.

      remember (_initializeFrameValues (los,nts) la2 gvs2 lc1) as R1.
      destruct R1 as [lc'|]; tinv Hin.
      remember (GVsSig.(lift_op1) (fit_gv (los, nts) t) g t) as R2.
      destruct R2 as [gv|]; inv Hin.
      destruct lp2 as [|[[]]]; tinv Hpar.
      destruct Hpar as [Hwfg Hpar].
      apply wf_lc_updateAddAL with (t:=t); eauto.
        rewrite_env ((la1++[(t,a,i0)])++la2).
        eapply IHla2; simpl_env; eauto.

        simpl.
        rewrite NoDup_lookupTypViaIDFromArgs; auto.

        inv HwfF. find_middle_element.
        eapply lift_fit_gv__wf_gvs; eauto.
        solve_wf_typ.
Qed.

Lemma initializeFrameValues__wf_lc : forall s los nts fattr ft fid la2 va
  bs2 lc1
  (Huniq: NoDup (getArgsIDs la2))
  (HwfF: wf_fheader s (los, nts)
           (fheader_intro fattr ft fid la2 va))
  (Hwflc:wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2)
    lc1)
  lc2 gvs2 lp2,
  _initializeFrameValues (los,nts) la2 gvs2 lc1 = Some lc2 ->
  wf_params (los,nts) gvs2 lp2 ->
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2) lc2.
Proof.
  intros.
  rewrite_env (nil++la2) in HwfF.
  rewrite_env (nil++la2) in Hwflc.
  rewrite_env (nil++la2).
  eapply initializeFrameValues__wf_lc_aux; eauto.
Qed.

Lemma initLocals__wf_lc : forall s los nts Ps fattr ft fid la2 va bs2
  (Huniq: uniqFdef (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  (HwfF: wf_fdef s (module_intro los nts Ps)
    (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  lc gvs2 lp2,
  initLocals (los,nts) la2 gvs2 = Some lc ->
  wf_params (los,nts) gvs2 lp2 ->
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2) lc.
Proof.
  intros. unfold initLocals in H.
  inv HwfF.
  destruct Huniq as [Huniq1 Huniq2].
  apply NoDup_split in Huniq2.
  destruct Huniq2 as [Huniq2 _].
  eapply initializeFrameValues__wf_lc; eauto.
    intros x gvx tx J1 J2. inv J2.
Qed.

Lemma initLocals_spec' : forall fid fa rt la va lb gvs los nts s lc Ps id1 t
  lp (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (HwfF: wf_fdef s (module_intro los nts Ps)
    (fdef_intro (fheader_intro fa rt fid la va) lb))
  (lk: lookupTypViaIDFromFdef (fdef_intro (fheader_intro fa rt fid la va) lb)
         id1 = ret t)
  (Hinit: initLocals (los,nts) la gvs = Some lc)
  (Hwfp : wf_params (los,nts) gvs lp)
  (Hin: In id1 (getArgsIDs la)),
  exists gv, lookupAL _ lc id1 = Some gv /\ wf_GVs (los, nts) gv t.
Proof.
  intros.
  assert (J:=Hinit).
  eapply initLocals_spec in J; eauto.
  destruct J as [gv J].
  eapply initLocals__wf_lc in Hinit; eauto.
Qed.

Lemma returnUpdateLocals__wf_lc : forall los nts S F F' c Result lc lc' gl
  lc'' Ps l1 ps1 cs1 tmn1 t B'
  (Hwfg: wf_global (los,nts) S gl)
  (Hwfv: wf_value S (module_intro los nts Ps) F Result t),
  wf_lc (los,nts) F lc -> wf_lc (los,nts) F' lc' ->
  returnUpdateLocals (los,nts) c Result lc lc' gl =
    ret lc'' ->
  uniqFdef F' ->
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) F' = true ->
  In c cs1 ->
  wf_insn S (module_intro los nts Ps) F' B' (insn_cmd c) ->
  wf_lc (los,nts) F' lc''.
Proof.
  intros.
  unfold returnUpdateLocals in H1.
  remember (getOperandValue (los,nts) Result lc gl) as R.
  destruct R; tinv H1.
  destruct_cmd c; inv H1; auto.
  destruct n; inv H7; auto.
  remember (GVsSig.(lift_op1) (fit_gv (los, nts) t1) g t1) as R.
  destruct R; inv H6.
    eapply wf_lc_updateAddAL with (t:=t1); eauto.
      eapply uniqF__lookupTypViaIDFromFdef; eauto.
      symmetry in HeqR.
      eapply getOperandValue__wf_gvs in HeqR; eauto.
      match goal with
      | H5: wf_insn _ _ _ _ _ |- _ => inv H5 end.
      match goal with
      | H11: module_intro _ _ _ = module_intro _ _ _ |- _ => inv H11 end.
      eapply lift_fit_gv__wf_gvs; eauto.
Qed.

Lemma BOP__wf_gvs : forall S F los nts ps lc gl bop0 sz0 v1 v2 gvs3,
  wf_lc (los,nts) F lc ->
  wf_value S (module_intro los nts ps) F v1 (typ_int sz0) ->
  wf_value S (module_intro los nts ps) F v2 (typ_int sz0) ->
  BOP (los,nts) lc gl bop0 sz0 v1 v2 = ret gvs3 ->
  wf_GVs (los,nts) gvs3 (typ_int sz0).
Proof.
  intros S F los nts ps lc gl bop0 sz0 v1 v2 gvs3 Hwflc Hwfv1 Hwfv2
    Hbop.
  assert (J:=Hwfv1). apply wf_value__wf_typ in J. destruct J as [Hwft Hft].
  unfold BOP in Hbop.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; tinv Hbop.
  remember(getOperandValue (los,nts) v2 lc gl) as R2.
  destruct R2; inv Hbop.
  eapply wf_GVs_intro; eauto.
    unfold getTypeSizeInBits. simpl. eauto.

    intros gv Hin.
    eapply GVsSig.(lift_op2__getTypeSizeInBits) with (los:=los)(nts:=nts); eauto.
      simpl. eauto.
      intros. erewrite mbop_typsize; eauto.

    eapply GVsSig.(lift_op2__inhabited) in H0;
      eauto using getOperandValue__inhabited.
    eapply mbop_is_total; eauto.

    intros gv Hin.
    eapply GVsSig.(lift_op2__matches_chunks) with (los:=los)(nts:=nts); eauto.
      simpl. eauto.
      intros. eapply mbop_matches_chunks; eauto.
Qed.

Lemma FBOP__wf_gvs : forall S F (los:layouts) (nts:namedts) ps lc gl fbop0 fp v1
  v2 gvs3, wf_lc (los,nts) F lc ->
  wf_value S (module_intro los nts ps) F v1 (typ_floatpoint fp) ->
  wf_value S (module_intro los nts ps) F v2 (typ_floatpoint fp) ->
  FBOP (los,nts) lc gl fbop0 fp v1 v2 = ret gvs3 ->
  wf_GVs (los,nts) gvs3 (typ_floatpoint fp).
Proof.
  intros S F los nts ps lc gl fbop0 fp v1 v2 gvs3 Hwflc Hwfv1 Hwfv2 Hfbop.
  unfold FBOP in Hfbop.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; tinv Hfbop.
  remember(getOperandValue (los,nts) v2 lc gl) as R2.
  destruct R2; inv Hfbop.
  assert (J:=Hwfv1). apply wf_value__wf_typ in J. destruct J as [Hwft Hft].
  assert (Hft':=Hft).
  eapply feasible_typ_inv in Hft; eauto.
  destruct Hft as [sz [al [H1 H2]]].
  eapply wf_GVs_intro with (sz:=sz); eauto.
    unfold getTypeSizeInBits. rewrite H1. auto.

    intros gv Hin.
    eapply GVsSig.(lift_op2__getTypeSizeInBits) with (los:=los)(nts:=nts); eauto.
      simpl. eauto.

      intros x y z ? ? J3.
      eapply mfbop_typsize in J3; eauto.
      destruct J3 as [sz1 [al1 [J5 J6]]].
      unfold getTypeSizeInBits_and_Alignment in H1.
      unfold getTypeSizeInBits_and_Alignment_for_namedts in *.
      rewrite H1 in J5. inv J5. auto.

    eapply GVsSig.(lift_op2__inhabited) in H0;
      eauto using getOperandValue__inhabited.
    eapply mfbop_is_total; eauto.

    intros gv Hin.
    eapply GVsSig.(lift_op2__matches_chunks) with (los:=los)(nts:=nts); eauto.
      intros. eapply mfbop_matches_chunks; eauto.
Qed.

Lemma ICMP__wf_gvs : forall S los nts ps F lc gl c t v1 v2 gvs3
  (Hwft1: wf_typ S (los, nts) (typ_int Size.One)),
  wf_lc (los,nts) F lc ->
  Typ.isIntOrIntVector t \/ isPointerTyp t ->
  wf_value S (module_intro los nts ps) F v1 t ->
  wf_value S (module_intro los nts ps) F v2 t ->
  ICMP (los,nts) lc gl c t v1 v2 = ret gvs3 ->
  wf_GVs (los,nts) gvs3 (typ_int Size.One).
Proof.
  intros S los nts ps F lc gl c t v1 v2 gvs3 Hwft1 Hwflc Hwft Hwfv1 Hwfv2 Hiop.
  unfold ICMP in Hiop.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; tinv Hiop.
  remember(getOperandValue (los,nts) v2 lc gl) as R2.
  destruct R2; inv Hiop.
  eapply wf_GVs_intro with (sz:=Size.to_nat Size.One); eauto.
    intros gv Hin.
    eapply GVsSig.(lift_op2__getTypeSizeInBits) with (los:=los)(nts:=nts)(S:=S);
      eauto.
      simpl. eauto.
      intros. unfold Size.to_nat. erewrite micmp_typsize; eauto.

    apply GVsSig.(lift_op2__inhabited) in H0;
      eauto using getOperandValue__inhabited.
    apply wf_value__wf_typ in Hwfv1. destruct Hwfv1.
    eapply micmp_is_total; eauto.

    intros gv Hin.
    eapply GVsSig.(lift_op2__matches_chunks) with (los:=los)(nts:=nts); eauto.
      intros. eapply micmp_matches_chunks; eauto.
Qed.

Lemma FCMP__wf_gvs : forall S los nts ps F lc gl c fp v1 v2 gvs3
  (Hwft1: wf_typ S (los, nts) (typ_int Size.One)),
  wf_lc (los,nts) F lc ->
  wf_fcond c = true  ->
  wf_value S (module_intro los nts ps) F v1 (typ_floatpoint fp) ->
  wf_value S (module_intro los nts ps) F v2 (typ_floatpoint fp) ->
  FCMP (los,nts) lc gl c fp v1 v2 = ret gvs3 ->
  wf_GVs (los,nts) gvs3 (typ_int Size.One).
Proof.
  intros S los nts ps F lc gl c fp v1 v2 gvs3 Hwft1 Hwflc Hc Hwfv1 Hwfv2 Hiop.
  unfold FCMP in Hiop.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; tinv Hiop.
  remember(getOperandValue (los,nts) v2 lc gl) as R2.
  destruct R2; inv Hiop.
  eapply wf_GVs_intro with (sz:=Size.to_nat Size.One); eauto.
    intros gv Hin.
    eapply GVsSig.(lift_op2__getTypeSizeInBits) with (los:=los)(nts:=nts)(S:=S);
      eauto.
      simpl. eauto.
      intros. unfold Size.to_nat. erewrite mfcmp_typsize; eauto.

    apply GVsSig.(lift_op2__inhabited) in H0;
      eauto using getOperandValue__inhabited.
    apply wf_value__wf_typ in Hwfv1. destruct Hwfv1.
    eapply mfcmp_is_total; eauto.

    intros gv Hin.
    eapply GVsSig.(lift_op2__matches_chunks) with (los:=los)(nts:=nts); eauto.
      intros. eapply mfcmp_matches_chunks; eauto.
Qed.

Lemma GEP__wf_gvs : forall S TD t mp vidxs inbounds0 mp' vidxs0 t' gl lc idxs,
  @values2GVs GVsSig TD idxs lc gl = Some vidxs ->
  wf_GVs TD mp (typ_pointer t) -> vidxs0 @@ vidxs ->
  wf_typ S TD (typ_pointer t') ->
  getGEPTyp idxs t = ret (typ_pointer t') ->
  GEP TD t mp vidxs0 inbounds0 t' = ret mp' ->
  wf_GVs TD mp' (typ_pointer t').
Proof.
  intros S TD t mp vidxs inbounds0 mp' vidxs0 t' gl lc idxs Hvg2 Hwfgv Hin
    Hwft Hgt' Hget.
  unfold GEP in Hget. inv Hget.
  unfold getGEPTyp in Hgt'.
  destruct idxs; tinv Hgt'. simpl_prod.
  remember (getSubTypFromValueIdxs idxs t) as R4.
  destruct R4; inv Hgt'.
  destruct TD as [los nts].
  apply wf_GVs_intro with (sz:=32%nat); auto.
    intros gv Hin'.
    eapply GVsSig.(lift_op1__getTypeSizeInBits) with (los:=los)(nts:=nts)
      (f:=gep (los, nts) t vidxs0 inbounds0 t') (g:=mp)
      (S:=S)(t:=typ_pointer t'); eauto.
      simpl. auto.

      intros x y ? J3.
      unfold gep, LLVMgv.GEP in J3.
      assert(gundef (los, nts) (typ_pointer t') = ret y ->
             sizeGenericValue y = nat_of_Z (ZRdiv (Z_of_nat 32) 8)) as G.
        intro W. unfold gundef in W. simpl in W. inv W. simpl. auto.
      destruct (GV2ptr (los, nts) (getPointerSize (los, nts)) x); eauto.
      destruct (GVs2Nats (los, nts) vidxs0); eauto.
      destruct (mgep (los, nts) t v0 l0); eauto.
        inv J3. unfold ptr2GV, val2GV. simpl. auto.

    inv Hwfgv.
    eapply GVsSig.(lift_op1__inhabited) in H0; eauto.
    unfold gep. intro. eapply GEP_is_total; eauto.

    intros gv Hin'.
    eapply GVsSig.(lift_op1__matches_chunks) with (los:=los)(nts:=nts)
      (f:=gep (los, nts) t vidxs0 inbounds0 t')(S:=S)
      (t:=typ_pointer t'); eauto.
      unfold gep. intros. eapply GEP_matches_chunks; eauto.
Qed.

Lemma CAST__wf_gvs : forall s f b los nts ps lc gl cop0 t1 v1 t2 gvs2 id5
  (Hwfg : wf_global (los, nts) s gl),
  wf_lc (los,nts) f lc ->
  wf_cast s (module_intro los nts ps) f b
    (insn_cmd (insn_cast id5 cop0 t1 v1 t2)) ->
  CAST (los,nts) lc gl cop0 t1 v1 t2 = ret gvs2 ->
  wf_GVs (los,nts) gvs2 t2.
Proof.
  intros s f b los nts ps lc gl cop0 t1 v1 t2 gvs2 id5 Hwfg Hwflc Hwfc
    Hcast.
  unfold CAST in Hcast.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; inv Hcast.
  symmetry in HeqR1.
  inv Hwfc.
    eapply getOperandValue__wf_gvs in HeqR1; eauto.
    eapply wf_GVs_intro with (sz:=sz5); eauto.
      intros gv Hin.
      eapply GVsSig.(lift_op1__getTypeSizeInBits)with (los:=los)(nts:=nts);eauto.
        simpl. eauto.

        intros x y ? J2.
        symmetry in J2.
        eapply gundef__getTypeSizeInBits in J2; eauto.
        destruct J2 as [sz1 [al1 [J4 J5]]].
        simpl in J4. inv J4. auto.

      inv HeqR1.
      eapply GVsSig.(lift_op1__inhabited) in H0; eauto.
        intro. eapply gundef__total; eauto.

      intros.
      eapply GVsSig.(lift_op1__matches_chunks)with (los:=los)(nts:=nts); eauto.
        intros. eapply gundef__matches_chunks; eauto.

    eapply getOperandValue__wf_gvs in HeqR1; eauto.
    eapply wf_GVs_intro with (sz:=32%nat); eauto.
      intros gv Hin.
      eapply GVsSig.(lift_op1__getTypeSizeInBits)with (los:=los)(nts:=nts);eauto.
        simpl. eauto.

        intros x y ? J2.
        symmetry in J2.
        eapply gundef__getTypeSizeInBits in J2; eauto.
        destruct J2 as [sz1 [al1 [J4 J5]]].
        simpl in J4. inv J4. auto.

      inv HeqR1.
      eapply GVsSig.(lift_op1__inhabited) in H0; eauto.
        intro. eapply gundef__total; eauto.

      intros.
      eapply GVsSig.(lift_op1__matches_chunks)with (los:=los)(nts:=nts); eauto.
        intros. eapply gundef__matches_chunks; eauto.

    eapply getOperandValue__wf_gvs in HeqR1; eauto.
    eapply wf_GVs_intro with (sz:=32%nat); eauto.
      intros gv Hin.
      eapply GVsSig.(lift_op1__getTypeSizeInBits)with(los:=los)(nts:=nts) in Hin;
        eauto.
        simpl. eauto.
        intros x y Hin' Heq. inv Heq.
        inv HeqR1.
        unfold getTypeSizeInBits in H. inv H. simpl in *. eauto.

      inv HeqR1.
      eapply GVsSig.(lift_op1__inhabited) in H0; eauto.
        unfold mcast, mbitcast. eauto.

      intros.
      eapply GVsSig.(lift_op1__matches_chunks)with (los:=los)(nts:=nts); eauto.
        unfold mcast, mbitcast. intros.
        inv HeqR1.
        apply H6 in H1. uniq_result.
        unfold gv_chunks_match_typ. unfold gv_chunks_match_typ in H1.
        simpl  in *. auto.
Qed.

Lemma TRUNC__wf_gvs : forall s f b (los:layouts) (nts:namedts) ps lc gl
  top0 t1 v1 t2 gvs2 id5 (Hwfg : wf_global (los, nts) s gl),
  wf_lc (los,nts) f lc ->
  wf_trunc s (module_intro los nts ps) f b
    (insn_cmd (insn_trunc id5 top0 t1 v1 t2)) ->
  TRUNC (los,nts) lc gl top0 t1 v1 t2 = ret gvs2 ->
  wf_GVs (los,nts) gvs2 t2.
Proof.
  intros s f b los nts ps lc gl top0 t1 v1 t2 gvs2 id5 Hwfg Hwflc Hwfc
    Htrunc.
  unfold TRUNC in Htrunc.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; inv Htrunc.
  assert (J:=Hwfc).
  apply wf_trunc__wf_typ in J.
  destruct J as [J1 J2].
  assert (H':=J2).
  apply feasible_typ_inv' in H'.
  destruct H' as [sz [al [J3 J4]]].
  eapply wf_GVs_intro with (sz:=sz); eauto.
    unfold getTypeSizeInBits.
    rewrite J3. auto.

    intros gv Hin.
    eapply GVsSig.(lift_op1__getTypeSizeInBits) with (los:=los)(nts:=nts); eauto.
      intros x y Hin' J2'.
      eapply mtrunc_typsize in J2'; eauto.
      destruct J2' as [sz' [al' [J2' J4']]].
      unfold getTypeSizeInBits_and_Alignment in J3.
      unfold layouts, namedts in *.
      rewrite J3 in J2'. inv J2'. auto.

    eapply GVsSig.(lift_op1__inhabited) in H0; eauto.
      eapply mtrunc_is_total; eauto.

      symmetry in HeqR1.
      eapply getOperandValue__wf_gvs in HeqR1; eauto using wf_trunc__wf_value.
      inv HeqR1; auto.

    intros gv Hin.
    eapply GVsSig.(lift_op1__matches_chunks) with (los:=los)(nts:=nts); eauto.
      intros x y Hin' J2'.
      eapply mtrunc_matches_chunks in J2'; eauto.
Qed.

Lemma EXT__wf_gvs : forall s f b (los:layouts) (nts:namedts) ps lc gl eop0
  t1 v1 t2 gvs2 id5 (Hwfg : wf_global (los, nts) s gl),
  wf_lc (los,nts) f lc ->
  wf_ext s (module_intro los nts ps) f b
    (insn_cmd (insn_ext id5 eop0 t1 v1 t2)) ->
  EXT (los,nts) lc gl eop0 t1 v1 t2 = ret gvs2 ->
  wf_GVs (los,nts) gvs2 t2.
Proof.
  intros s f b los nts ps lc gl eop0 t1 v1 t2 gvs2 id5 Hwfg Hwflc Hwfc Hext.
  unfold EXT in Hext.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; inv Hext.
  assert (J:=Hwfc).
  apply wf_ext__wf_typ in J.
  destruct J as [J1 J2].
  assert (H':=J2).
  apply feasible_typ_inv' in H'.
  destruct H' as [sz [al [J4 J3]]].
  eapply wf_GVs_intro with (sz:=sz); eauto.
    unfold getTypeSizeInBits.
    rewrite J4. auto.

    intros gv Hin.
    eapply GVsSig.(lift_op1__getTypeSizeInBits) with (los:=los)(nts:=nts); eauto.
      intros x y Hin' J2'.
      eapply mext_typsize in J2'; eauto.
      destruct J2' as [sz' [al' [J2' J4']]].
      unfold getTypeSizeInBits_and_Alignment in J4.
      unfold layouts, namedts in *.
      rewrite J4 in J2'. inv J2'. auto.

    eapply GVsSig.(lift_op1__inhabited) in H0; eauto.
      eapply mext_is_total; eauto.

      symmetry in HeqR1.
      eapply getOperandValue__wf_gvs in HeqR1; eauto using wf_ext__wf_value.
      inv HeqR1; auto.

    intros gv Hin.
    eapply GVsSig.(lift_op1__matches_chunks) with (los:=los)(nts:=nts); eauto.
      intros x y Hin' J2'.
      eapply mext_matches_chunks in J2'; eauto.
Qed.

Lemma insertGenericValue__wf_gvs : forall S los nts t1 t2 gvs1 gvs2 cidxs gvs',
  wf_GVs (los, nts) gvs1 t1 ->
  wf_GVs (los, nts) gvs2 t2 ->
  insertGenericValue (los, nts) t1 gvs1 cidxs t2 gvs2 = ret gvs' ->
  getSubTypFromConstIdxs cidxs t1 = ret t2 ->
  wf_typ S (los, nts) t1 ->
  wf_typ S (los, nts) t2 ->
  wf_GVs (los, nts) gvs' t1.
Proof.
  intros S los nts t1 t2 gvs1 gvs2 cidxs gvs' Hwfgv1 Hwfgv2 Hinsert e0 Hwft
    Hwft2.
  match goal with
  | H5: wf_typ _ _ _, H6: wf_typ _ _ _ |- _ =>
    assert (H5':=H5);
    apply wf_typ__getTypeSizeInBits_and_Alignment in H5;
    destruct H5 as [sz [al [J2 J3]]];
    assert (H6':=H6);
    apply wf_typ__getTypeSizeInBits_and_Alignment in H6;
    destruct H6 as [sz' [al' [J2' J3']]]
  end.
  unfold insertGenericValue in Hinsert.
  remember (intConsts2Nats (los, nts) cidxs) as R1.
  destruct R1; tinv Hinsert.
  remember (mgetoffset (los, nts) t1 l0) as R2.
  destruct R2 as [[]|]; inv Hinsert.
  eapply getSubTypFromConstIdxs__mgetoffset in e0; eauto.
  subst.
  inv Hwfgv1. inv Hwfgv2.
  eapply wf_GVs_intro with (sz:=sz); eauto.
    unfold getTypeSizeInBits.
    rewrite J2. auto.

    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
           getTypeSizeInBits_and_Alignment_for_namedts in *.
    inv_mbind.
    uniq_result. symmetry_ctx. uniq_result.
    intros gv0 Hin.
    eapply GVsSig.(lift_op2__getTypeSizeInBits)with (los:=los)(nts:=nts)(t:=t1);
      eauto.
      intros x y z0 J4 J5 J6.
      apply H1 in J4. apply H5 in J5.
      unfold mset' in J6.
      remember (mset (los, nts) x z t2 y) as R4.
      destruct R4 as [gv'|]; inv J6.
        eapply mset_typsize in HeqR4; eauto.
        rewrite <- HeqR4. auto.

        match goal with
        | H8: gundef _ _ = _ |- _ =>
          symmetry in H8;
          eapply gundef__getTypeSizeInBits in H8; eauto;
          destruct H8 as [sz2 [al2 [J7' J8']]];
          symmetry_ctx; uniq_result; auto
        end.

    match goal with
    | H6: lift_op2 _ _ _ _ _ = _ |- _ =>
      eapply GVsSig.(lift_op2__inhabited) in H6; try solve [
        eauto | eapply mset'_is_total; eauto]
    end.

    intros gv0 Hin.
    eapply GVsSig.(lift_op2__matches_chunks)with (los:=los)(nts:=nts)(t:=t1);
      eauto.
      intros. apply H3 in H8. apply H7 in H9.  eapply mset'_matches_chunks; eauto.
Qed.

Lemma extractGenericValue__wf_gvs : forall S los nts t1 gv1 const_list gv typ'
  (Hwfg : wf_GVs (los, nts) gv1 t1)
  (HeqR3 : extractGenericValue (los, nts) t1 gv1 const_list = ret gv)
  (e0 : getSubTypFromConstIdxs const_list t1 = ret typ')
  (w1 : wf_typ S (los, nts) typ'),
  wf_GVs (los, nts) gv typ'.
Proof.
  intros.
  match goal with
  | H3: wf_typ _ _ _ |- _ =>
    assert (H3':=H3);
    apply wf_typ__getTypeSizeInBits_and_Alignment in H3;
    destruct H3 as [sz [al [J2 J3]]]
  end.
  unfold extractGenericValue in HeqR3.
  remember (intConsts2Nats (los, nts) const_list) as R1.
  destruct R1; tinv HeqR3.
  remember (mgetoffset (los, nts) t1 l0) as R2.
  destruct R2 as [[]|]; inv HeqR3.
  eapply getSubTypFromConstIdxs__mgetoffset in e0; eauto.
  subst.
  eapply wf_GVs_intro with (sz:=sz); eauto.
    unfold getTypeSizeInBits.
    rewrite J2. auto.

    intros gv0 Hin.
    eapply GVsSig.(lift_op1__getTypeSizeInBits) with (los:=los)(nts:=nts); eauto.
      intros x y J4 J5.
      unfold mget' in J5.
      unfold getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts in J2.
      remember (mget (los, nts) x z typ') as R4.
      destruct R4 as [gv'|]; inv J5.
        eapply mget_typsize in HeqR4; eauto.
          destruct HeqR4 as [sz1 [al1 [J7 J8]]].
          unfold layouts, namedts in J2.
          rewrite J2 in J7. inv J7. auto.

        match goal with
        | H4: gundef _ _ = _ |- _ =>
          symmetry in H4;
          eapply gundef__getTypeSizeInBits in H4; eauto;
          destruct H4 as [sz1 [al1 [J7 J8]]]
        end.
        rewrite J2 in J7. inv J7. auto.

    match goal with
    | H3: lift_op1 _ _ _ _ = _ |- _ =>
      inv Hwfg;
      eapply GVsSig.(lift_op1__inhabited) in H3;
        try solve [eauto | eapply mget'_is_total; eauto]
    end.

    intros gv0 Hin.
    eapply GVsSig.(lift_op1__matches_chunks)with (los:=los)(nts:=nts);
      eauto.
      intros. inv Hwfg. apply H3 in H. eapply mget'_matches_chunks; eauto.
Qed.

(* Properties of wf_State *)
Lemma wf_State__inv : forall S los nts Ps F B c cs tmn lc als EC gl fs Mem0
  (HwfCfg: wf_Config (mkCfg S (los,nts) Ps gl fs)),
  wf_State (mkCfg S (los,nts) Ps gl fs)
    (mkState ((mkEC F B (c::cs) tmn lc als)::EC) Mem0) ->
  wf_namedts S (los, nts) /\
  wf_global (los, nts) S gl /\
  wf_lc (los,nts) F lc /\
  wf_insn S (module_intro los nts Ps) F B (insn_cmd c).
Proof.
  intros.
  destruct HwfCfg as [Hwftd [Hwfg [HwfSystem HmInS]]]; subst.
  destruct H as
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]; subst.
  split; auto.
  split; auto.
  split; auto.
    eapply wf_system__wf_cmd; eauto using in_middle.
Qed.

(*********************************************)
(** * Preservation *)

Lemma preservation_dbCall_case : forall fid l' fa rt la va lb gvs los
  nts s lc Ps lp
  (Hinhs : forall gv, In gv gvs -> GVsSig.(inhabited) gv)
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (HwfF: wf_fdef s (module_intro los nts Ps)
    (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hwfp : wf_params (los, nts) gvs lp)
  (Hinit : initLocals (los,nts) la gvs = Some lc),
   match
     fold_left
       (inscope_of_block (fdef_intro (fheader_intro fa rt fid la va) lb) l')
       nil (ret getArgsIDs la)
   with
   | ret ids0 =>
       wf_defs (los,nts) (fdef_intro (fheader_intro fa rt fid la va) lb) lc ids0
   | merror => False
   end.
Proof.
  intros.
  assert (incl nil (bound_blocks lb)) as J.
    intros x J. inv J.
  apply fold_left__bound_blocks with (fh:=fheader_intro fa rt fid la va)(l0:=l')
    (init:=getArgsIDs la) in J.
  destruct J as [r J]. unfold l in *.
  rewrite J.
  apply fold_left__spec in J.
  destruct J as [_ [_ J]].
  apply wf_defs_intro.
  intros id1 Hin.
  apply J in Hin.
  destruct Hin as [Hin | Hin].
    assert (J1:=Hin).
    apply InArgsIDs_lookupTypViaIDFromFdef with (t0:=rt)(id0:=fid)(la0:=la)
      (va0:=va)(bs:=lb)(fa:=fa) in J1.
    destruct J1 as [t J1].
    split; eauto using arg_id_in_reachable_block.
    exists t. rewrite J1.
    eapply initLocals_spec' with (gvs:=gvs) in Hin; eauto.
    destruct Hin as [gv [Hin Hinh]].
    exists gv. split; auto.

    destruct Hin as [b1 [l1 [Hin _]]].
    apply ListSet.set_diff_elim1 in Hin. inv Hin.
Qed.

Lemma preservation_cmd_updated_case : forall
  (S : system)
  (los : layouts)
  (nts : namedts)
  (Ps : list product)
  (F : fdef)
  (B : block)
  (lc : GVsMap)
  (gl : GVMap)
  (fs : GVMap)
  (gv3 : GVs)
  (EC : list ExecutionContext)
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 : mem)
  (als : list mblock)
  id0 c0
  (Hid : Some id0 = getCmdID c0)
  t0
  (Htyp : Some t0 = getCmdTyp c0)
  (Hwfgv : wf_GVs (los,nts) gv3 t0)
  (HwfCfg : wf_Config {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            Globals := gl;
            FunTable := fs |})
  (HwfS1 : wf_State {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            Globals := gl;
            FunTable := fs |}
            {|
            ECS := {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := c0 :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Allocas := als |} :: EC;
            Mem := Mem0 |}),
   wf_State {|
     CurSystem := S;
     CurTargetData := (los, nts);
     CurProducts := Ps;
     Globals := gl;
     FunTable := fs |}
     {|
     ECS := {|
            CurFunction := F;
            CurBB := B;
            CurCmds := cs;
            Terminator := tmn;
            Locals := updateAddAL GVs lc id0 gv3;
            Allocas := als |} :: EC;
     Mem := Mem0 |}.
Proof.

Ltac preservation_cmd_updated_case_tac :=
match goal with
| Hnotin: NoDup (getStmtsLocs _) |- id_in_reachable_block _ _ =>
  eapply block_id_in_reachable_block; eauto 1; try solve [
    simpl; apply in_or_app; right;
    apply getCmdLoc__in__getCmdsIDs; try solve
      [auto | congruence | simpl in Hnotin; split_NoDup; auto |
       solve_in_list]
  ]
end.

  intros.
  destruct HwfCfg as [Hwftd [Hwfg [HwfSystem HmInS]]]; subst.
  destruct HwfS1 as [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]; subst.
  remember (inscope_of_cmd F (l3, stmts_intro ps3 (cs3' ++ c0 :: cs) tmn) c0)
    as R1.
  assert (uniqFdef F) as HuniqF.
    eapply wf_system__uniqFdef; eauto.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      intros; congruence.
      Case "wflc".
      eapply wf_lc_updateAddAL; eauto.
        eapply uniqF__lookupTypViaIDFromFdef; eauto using in_middle.

      assert (Hid':=Hid).
      symmetry in Hid.
      apply getCmdLoc_getCmdID in Hid.
       subst.
      assert (NoDup (getStmtsLocs (stmts_intro ps3 (cs3' ++ c0 :: cs) tmn)))
        as Hnotin.
        eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.
      destruct cs; simpl_env in *.
      Case "1.1.1".
        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL with (t1:=t0) ; eauto.
          preservation_cmd_updated_case_tac.
          eapply uniqF__lookupTypViaIDFromFdef; eauto.

      Case "1.1.2".
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL with (t1:=t0) ; eauto.
          preservation_cmd_updated_case_tac.
          eapply uniqF__lookupTypViaIDFromFdef; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
Qed.

Lemma preservation_cmd_non_updated_case : forall
  (S : system)
  (los : layouts)
  (nts : namedts)
  (Ps : list product)
  (F : fdef)
  (B : block)
  (lc : GVsMap)
  (gl : GVMap)
  (fs : GVMap)
  (EC : list ExecutionContext)
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 : mem)
  (als : list mblock)
  c0
  (Hid : getCmdID c0 = None)
  (HwfCfg : wf_Config {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            Globals := gl;
            FunTable := fs |})
  (HwfS1 : wf_State {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            Globals := gl;
            FunTable := fs |}
            {|
            ECS := {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := c0 :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Allocas := als |} :: EC;
            Mem := Mem0 |}),
   wf_State {|
     CurSystem := S;
     CurTargetData := (los, nts);
     CurProducts := Ps;
     Globals := gl;
     FunTable := fs |}
     {|
     ECS := {|
            CurFunction := F;
            CurBB := B;
            CurCmds := cs;
            Terminator := tmn;
            Locals := lc;
            Allocas := als |} :: EC;
     Mem := Mem0 |}.
Proof.
  intros.
  destruct HwfCfg as [Hwftd [Hwfg [HwfSystem HmInS]]]; subst.
  destruct HwfS1 as [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]; subst.
  remember (inscope_of_cmd F (l3, stmts_intro ps3 (cs3' ++ c0 :: cs) tmn) c0)
    as R1.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      Case "0".
      intros. congruence.
      assert (NoDup (getStmtsLocs (stmts_intro ps3 (cs3' ++ c0 :: cs) tmn)))
        as Hnotin.
        eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.
      Case "1".
      destruct cs; simpl_env in *.
      SCase "1.1.1".
        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq; eauto.

      SCase "1.1.2".
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq ; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
Qed.

Tactic Notation "sInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "sReturn" | c "sReturnVoid" | c "sBranch" | c "sBranch_uncond" |
    c "sBop" | c "sFBop" | c "sExtractValue" | c "sInsertValue" |
    c "sMalloc" | c "sFree" |
    c "sAlloca" | c "sLoad" | c "sStore" | c "sGEP" |
    c "sTrunc" | c "sExt" |
    c "sCast" |
    c "sIcmp" | c "sFcmp" | c "sSelect" |
    c "sCall" | c "sExCall" ].

Ltac solve_wf_gvs :=
match goal with
| HwfS1 : wf_State _ _, H: _ = Some ?gv3 |- wf_GVs _ ?gv3 _ =>
  apply wf_State__inv in HwfS1; auto;
  destruct HwfS1 as [Hwftd [Hwfg [Hwflc Hwfc]]];
  inv Hwfc;
  try solve [
    eapply BOP__wf_gvs in H; eauto |
    eapply FBOP__wf_gvs in H; eauto |
    eapply TRUNC__wf_gvs in H; eauto |
    eapply EXT__wf_gvs in H; eauto |
    eapply CAST__wf_gvs in H; eauto |
    eapply ICMP__wf_gvs in H; eauto |
    eapply FCMP__wf_gvs in H; eauto
  ]
end.

Ltac destruct_wfCfgState HwfCfg HwfS1 :=
  let Hwftd := fresh "Hwftd" in
  let Hwfg := fresh "Hwfg" in
  let HwfSystem := fresh "HwfSystem" in
  let HmInS := fresh "HmInS" in
  let Hnonempty := fresh "Hnonempty" in
  let Hreach1 := fresh "Hreach1" in
  let HBinF1 := fresh "HBinF1" in
  let HFinPs1 := fresh "HFinPs1" in
  let Hwflc1 := fresh "Hwflc1" in
  let Hinscope1 := fresh "Hinscope1" in
  let l3 := fresh "l3" in
  let ps3 := fresh "ps3" in
  let cs3' := fresh "cs3'" in
  let Heq1 := fresh "Heq1" in
  let HwfEC := fresh "HwfEC" in
  let HwfCall := fresh "HwfCall" in
  destruct HwfCfg as [Hwftd [Hwfg [HwfSystem HmInS]]];
  destruct HwfS1 as
       [Hnonempty [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
         [HwfEC HwfCall]]]; subst.

Lemma wf_ExecutionContext__at_beginning_of_function: forall
  (S : system) (los : layouts) (nts : namedts)
  (Ps : products) (HwfSystem : wf_system S)
  (HmInS : moduleInSystemB (module_intro los nts Ps) S = true)
  (fid : id) (lp : params) (lc' : GVsMap) (l' : l) (ps' : phinodes)
  (cs' : cmds) (tmn' : terminator) f (gvs : list GVs)
  (H2 : getEntryBlock f = ret (l', stmts_intro ps' cs' tmn'))
  (H4 : initLocals (los, nts) (getArgsOfFdef f) gvs = ret lc')
  (HFinPs' : InProductsB (product_fdef f) Ps = true)
  (JJ : wf_params (los, nts) gvs lp),
  wf_ExecutionContext (los, nts) Ps
     {|
     CurFunction := f;
     CurBB := (l', stmts_intro ps' cs' tmn');
     CurCmds := cs';
     Terminator := tmn';
     Locals := lc';
     Allocas := nil |}.
Proof.
  intros.
    assert (uniqFdef f) as Huniq.
      eapply wf_system__uniqFdef; eauto.
    assert (wf_fdef S (module_intro los nts Ps) f) as HwfF.
      eapply wf_system__wf_fdef; eauto.
    split.
      simpl. eapply reachable_entrypoint; eauto.
    split.
      apply entryBlockInFdef in H2; auto.
    split; auto.
    split.
      destruct f as [[]]. eapply initLocals__wf_lc; eauto.
    split.
    Case "1".
     assert (ps'=nil) as EQ.
       eapply entryBlock_has_no_phinodes with (s:=S); eauto.
     subst.
     apply AlgDom.dom_entrypoint in H2.
     destruct cs'.
     SCase "1.1".
       unfold inscope_of_tmn. rewrite H2. simpl.
       destruct f as [[]].
       eapply preservation_dbCall_case; eauto using wf_params_spec.

     SCase "1.2".
       unfold inscope_of_cmd, inscope_of_id.
       rewrite init_scope_spec1; auto.
       rewrite H2. simpl.
       destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n];
         try solve [contradict n; auto].
       destruct f as [[]].
       eapply preservation_dbCall_case; eauto using wf_params_spec.
    Case "2".
    exists l'. exists ps'. exists nil. simpl_env. auto.
    Grab Existential Variables.
    assumption. assumption.
Qed.

Lemma preservation : forall cfg S1 S2 tr (HwfCfg: wf_Config cfg),
  sInsn cfg S1 S2 tr -> wf_State cfg S1 -> wf_State cfg S2.
Proof.
  intros cfg S1 S2 tr HwfCfg HsInsn HwfS1.
  (sInsn_cases (induction HsInsn) Case); destruct TD as [los nts].

Focus.
Case "sReturn".
  destruct HwfCfg as [Hwftd [Hwfg [HwfSystem HmInS]]].
  destruct HwfS1 as
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]]
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]; subst.
  remember (inscope_of_cmd F' (l2, stmts_intro ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (l1, stmts_intro ps1 (cs1' ++ nil)(insn_return rid RetTy Result))
             (insn_return rid RetTy Result)) as R1.
  destruct R1; try solve [inversion Hinscope1].
  split. intros; congruence.
  SCase "1".
    remember (getCmdID c') as R.
    destruct c' as [ | | | | | | | | | | | | | | | | i0 n c rt va v p];
      try solve [inversion H].
    assert (In (insn_call i0 n c rt va v p)
      (cs2'++[insn_call i0 n c rt va v p] ++ cs')) as HinCs.
      apply in_or_app. right. simpl. auto.
    assert (Hwfc := HBinF2).
    eapply wf_system__wf_cmd with (c:=insn_call i0 n c rt va v p) in Hwfc;
      eauto.
    assert (uniqFdef F') as HuniqF.
      eapply wf_system__uniqFdef; eauto.
      eapply wf_system__wf_tmn in HBinF1; eauto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    eapply returnUpdateLocals__wf_lc with (Result:=Result)(lc:=lc); eauto.
    inv HBinF1. eauto.

    split.
    SSCase "1.1".
      assert (NoDup (getStmtsLocs
                       (stmts_intro ps2
                          (cs2' ++ insn_call i0 n c rt va v p :: cs') tmn')))
        as Hnotin.
        eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.
      assert (n = false -> id_in_reachable_block F' i0) as Hidreach.
        intro; subst.
        eapply block_id_in_reachable_block; eauto 1.
          simpl. apply in_or_app. right.
          clear - Hnotin. simpl in Hnotin.
          split_NoDup.
          match goal with
          | |- In _ (getCmdsIDs (_++?c1::_)) =>
             apply getCmdLoc__in__getCmdsIDs with (c:=c1) in Huniq1; auto
          end.
            simpl. congruence.
            simpl. solve_in_list.
      assert (n = false -> lookupTypViaIDFromFdef F' i0 = ret rt) as Hlktyp.
        intro; subst.
        eapply uniqF__lookupTypViaIDFromFdef; eauto.
      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        unfold returnUpdateLocals in H1. simpl in H1.
        remember (getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR.
          remember (GVsSig.(lift_op1) (fit_gv (los, nts) rt) g rt) as R2.
          destruct R2; inv H1.
          inv Hwfc.

          match goal with
          | H7: module_intro _ _ _ = module_intro _ _ _,
            H18: wf_insn_base _ _ _ |- _ => inv H7; inv H18
          end.
          eapply wf_defs_updateAddAL with (t1:=rt);
            eauto using getOperandValue__inhabited.

            eapply lift_fit_gv__wf_gvs; eauto.
              inv HBinF1.
              eapply getOperandValue__wf_gvs with (f:=F)(v:=Result); eauto.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto.

      SSSCase "1.1.2".
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        unfold returnUpdateLocals in H1. simpl in H1.
        remember (getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR.
          remember (GVsSig.(lift_op1) (fit_gv (los, nts) rt) g rt) as R2.
          destruct R2; inv H1.
          inv Hwfc.
          match goal with
          | H7: module_intro _ _ _ = module_intro _ _ _,
            H18: wf_insn_base _ _ _ |- _ => inv H7; inv H18
          end.
          eapply wf_defs_updateAddAL with (t1:=rt);
            eauto using getOperandValue__inhabited.

            eapply lift_fit_gv__wf_gvs; eauto.
              inv HBinF1.
              eapply getOperandValue__wf_gvs with (f:=F)(v:=Result); eauto.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto.
    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[insn_call i0 n c rt va v p]).
      simpl_env. auto.

Focus.
Case "sReturnVoid".
  destruct HwfCfg as [Hwftd [Hwfg [HwfSystem HmInS]]].
  destruct HwfS1 as
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]]
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]; subst.
  remember (inscope_of_cmd F' (l2, stmts_intro ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (l1, stmts_intro ps1 (cs1' ++ nil)(insn_return_void rid))
             (insn_return_void rid)) as R1.
  destruct R1; try solve [inversion Hinscope1].
  split. intros; congruence.
  SCase "1".
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.
    SSCase "1.1".
      apply HwfCall' in HBinF1. simpl in HBinF1.
      assert (NoDup (getStmtsLocs
                       (stmts_intro ps2 (cs2' ++ c' :: cs') tmn')))
        as Hnotin.
        eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.
      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnotin H1.
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct_cmd c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto.

      SSSCase "1.1.2".
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 H1 Hnotin.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct_cmd c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto.

    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[c']).
      simpl_env. auto.

Focus.
Case "sBranch".
  destruct_wfCfgState HwfCfg HwfS1.
  remember (inscope_of_tmn F
             (l3, stmts_intro ps3 (cs3' ++ nil)(insn_br bid Cond l1 l2))
             (insn_br bid Cond l1 l2)) as R1.
  destruct R1; try solve [inversion Hinscope1].
  split. intros; congruence.
  split; auto.
  SCase "1".
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
    assert (isReachableFromEntry F 
             (if isGVZero (los, nts) c then l2 else l1,
              stmts_intro ps' cs' tmn')) as Hreach'.
      clear - Hreach1 H1 HBinF1 HFinPs1 HmInS HwfSystem HuniqF HwfF.
      unfold isReachableFromEntry in *.
      destruct (isGVZero (los, nts) c);
        symmetry in H1;
        apply lookupBlockViaLabelFromFdef_inv in H1; eauto;
        eapply reachable_successors; eauto; simpl; auto.
    split; auto.
    split.
      clear - H1 HBinF1 HFinPs1 HmInS HwfSystem HuniqF.
      destruct (isGVZero (los, nts) c);
        symmetry in H1; apply lookupBlockViaLabelFromFdef_inv in H1; auto.
    split; auto.
    split.
      destruct (isGVZero (los, nts) c);
        eapply wf_lc_br_aux in H1; eauto.
    split.
      clear - H0 HeqR1 H1 Hinscope1 H2 HwfSystem HBinF1 HwfF HuniqF Hwflc1 Hwfg
              Hwftd Hreach'.
      eapply inscope_of_tmn_br in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists (if isGVZero (los, nts) c then l2 else l1). 
      exists ps'. exists nil. simpl_env. auto.

Focus.
Case "sBranch_uncond".
  destruct_wfCfgState HwfCfg HwfS1.
  remember (inscope_of_tmn F
             (l3, stmts_intro ps3 (cs3' ++ nil)(insn_br_uncond bid l0))
             (insn_br_uncond bid l0)) as R1.
  destruct R1; try solve [inversion Hinscope1].
  split. intros; congruence.
  SCase "1".
    split; auto.
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
    assert (isReachableFromEntry F (l0, stmts_intro ps' cs' tmn')) as Hreach'.
      clear - Hreach1 H HBinF1 HFinPs1 HmInS HwfSystem HuniqF HwfF.
      unfold isReachableFromEntry in *.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
      eapply reachable_successors; eauto.
        simpl. auto.
    split; auto.
    split.
      clear - H HBinF1 HFinPs1 HmInS HwfSystem HuniqF.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
    split; auto.
    split. eapply wf_lc_br_aux in H0; eauto.
    split.
      clear - H0 HeqR1 Hinscope1 H HwfSystem HBinF1 HwfF HuniqF Hwfg Hwflc1
        Hwftd Hreach'.
      assert (Hwds := HeqR1).
      eapply inscope_of_tmn_br_uncond with (cs':=cs')(ps':=ps')
        (tmn':=tmn') in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l0. exists ps'. exists nil. simpl_env. auto.

Case "sBop".
  abstract (eapply preservation_cmd_updated_case in HwfS1; simpl;
    try solve [eauto | solve_wf_gvs]).

Case "sFBop".
  abstract (eapply preservation_cmd_updated_case in HwfS1; simpl;
    try solve [eauto | solve_wf_gvs]).

Case "sExtractValue".
Focus.
  assert (J':=HwfS1).
  destruct_wfCfgState HwfCfg J'.
  eapply wf_system__wf_cmd with (c:=insn_extractvalue id0 t v idxs t') in HBinF1;
    eauto using in_middle.
  inv HBinF1.
  match goal with
  | H14: exists _:_, exists _:_, _ |- _ => destruct H14 as [idxs0 [o [J1 J2]]]
  end.
  assert (exists t0, getSubTypFromConstIdxs idxs t = Some t0) as J.
    symmetry in J2.
    eapply mgetoffset__getSubTypFromConstIdxs in J2; eauto.
  destruct J as [t0 J].
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    symmetry in J2.
    eapply mgetoffset__getSubTypFromConstIdxs in J2; eauto.
    rewrite J in J2. inv J2.
    eapply getOperandValue__wf_gvs in H; eauto.
    eapply extractGenericValue__wf_gvs; eauto.

Case "sInsertValue".
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1; auto.
    destruct HwfS1 as [Hwftd [Hwfg [Hwflc Hwfc]]].
    inv Hwfc.
    match goal with
    | H18: exists _:_, exists _:_, _ |- _ => destruct H18 as [idxs0 [o [J3 J4]]]
    end.
    symmetry in J4.
    eapply mgetoffset__getSubTypFromConstIdxs in J4; eauto.
    eapply getOperandValue__wf_gvs in H; eauto.
    eapply getOperandValue__wf_gvs in H0; eauto.
    match goal with
    | H12: wf_value _ _ _ _ _, H15: wf_value _ _ _ _ _ |- _ =>
      assert (J1:=H12); apply wf_value__wf_typ in H12; destruct H12;
      assert (J2:=H15); apply wf_value__wf_typ in H15; destruct H15
    end.
    eapply insertGenericValue__wf_gvs in H1; eauto.

Case "sMalloc". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  unfold blk2GV, ptr2GV, val2GV. simpl.
  eapply wf_GVs_intro; eauto.
    unfold getTypeSizeInBits. simpl. eauto.
    intros gv Hin.
    apply GVsSig.(none_undef2gvs_inv) in Hin; subst; auto.
      intros mc. congruence.
    apply GVsSig.(gv2gvs__inhabited).

    intros gv Hin. unfold gv_chunks_match_typ, vm_matches_typ.
    apply GVsSig.(none_undef2gvs_inv) in Hin; subst; simpl.
    constructor; auto. simpl. split; auto.
      intros mc. congruence.

Case "sFree". eapply preservation_cmd_non_updated_case in HwfS1; eauto.
Case "sAlloca". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfCfg as [Hwftd [Hwfg [HwfSystem HmInS]]].
  destruct HwfS1 as
      [Hnonempty [
        [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
        [HwfEC HwfCall]]]; subst.
  repeat (split; try solve [intros; congruence | eauto]).

  unfold blk2GV, ptr2GV, val2GV. simpl.
  eapply wf_GVs_intro; eauto.
    unfold getTypeSizeInBits. simpl. eauto.
    intros gv Hin.
    apply GVsSig.(none_undef2gvs_inv) in Hin; subst; auto.
      intros mc. congruence.
    apply GVsSig.(gv2gvs__inhabited).

    intros gv Hin. unfold gv_chunks_match_typ, vm_matches_typ.
    apply GVsSig.(none_undef2gvs_inv) in Hin; subst; simpl.
    constructor; auto. simpl. split; auto.
      intros mc. congruence.

Case "sLoad".  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1; auto.
  destruct HwfS1 as [Hwftd [Hwfg [Hwflc Hwfc]]].
  inv Hwfc.
  match goal with
  | H10: wf_value _ _ _ _ _ |- _ => apply wf_value__wf_typ in H10; destruct H10
  end.
  match goal with
  | H2: wf_typ _ _ _, H15: wf_insn_base _ _ _ |- _ => inv H15
  end.
  assert (H1':=H1).
  eapply mload__getTypeSizeInBits in H1; eauto.
  destruct H1 as [sz [J1 J2]].
  eapply wf_GVs_intro; eauto.
    unfold getTypeSizeInBits in J1.
    remember (getTypeSizeInBits_and_Alignment (los, nts) true t) as R.
    destruct R as [[]|]; inv J1.
    unfold getTypeSizeInBits_and_Alignment in HeqR.
    eapply GVsSig.(gv2gvs__getTypeSizeInBits); eauto.

    apply GVsSig.(gv2gvs__inhabited).

    intros gv0 Hin.
    eapply mload__matches_chunks in H1'; eauto.
    eapply GVsSig.(gv2gvs__matches_chunks); eauto.

Case "sStore". eapply preservation_cmd_non_updated_case in HwfS1; eauto.
Case "sGEP".
  destruct HwfCfg as [Hwftd [Hwfg [HwfSystem HmInS]]].
  assert (J:=HwfS1).
  destruct J as
    [Hnonempty [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
         [HwfEC HwfCall]]]; subst.
  eapply wf_system__wf_cmd with (c:=insn_gep id0 inbounds0 t v idxs t') in HBinF1;
    eauto using in_middle.
  inv HBinF1; eauto. uniq_result.
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    eapply getOperandValue__wf_gvs in H; eauto.
    assert (H0':=H0).
    eapply values2GVs__inhabited in H0; eauto.
    destruct H0 as [vidxs0 H0].
    eapply GEP__wf_gvs in H1; eauto.
    solve_wf_value_list.

Case "sTrunc".
  abstract (eapply preservation_cmd_updated_case in HwfS1; simpl;
    try solve [eauto | solve_wf_gvs]).

Case "sExt".
  abstract (eapply preservation_cmd_updated_case in HwfS1; simpl;
    try solve [eauto | solve_wf_gvs]).

Case "sCast".
  abstract (eapply preservation_cmd_updated_case in HwfS1; simpl;
    try solve [eauto | solve_wf_gvs]).

Case "sIcmp".
  abstract (eapply preservation_cmd_updated_case in HwfS1; simpl;
    try solve [eauto | solve_wf_gvs]).

Case "sFcmp".
  abstract (eapply preservation_cmd_updated_case in HwfS1; simpl;
    try solve [eauto | solve_wf_gvs]).

Case "sSelect".
  assert (J:=HwfS1).
  apply wf_State__inv in J; auto.
  destruct J as [Hwftd [Hwfg [Hwflc Hwfc]]].
  inv Hwfc.
  eapply getOperandValue__wf_gvs in H0; eauto.
  eapply getOperandValue__wf_gvs in H1; eauto.
  destruct (isGVZero (los, nts) c);
    eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.

Focus.
Case "sCall".
  destruct_wfCfgState HwfCfg HwfS1.
  assert (InProductsB (product_fdef (fdef_intro
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    apply lookupFdefViaPtr_inversion in H1.
    destruct H1 as [fn [H11 H12]].
    eapply lookupFdefViaIDFromProducts_inv; eauto.
  split. intros; congruence.
  split; auto.
  SCase "1".
    assert (wf_params (los,nts) gvs lp) as JJ.
      eapply wf_system__wf_cmd in HBinF1; eauto using in_middle.
      inv HBinF1.
      eapply params2GVs_wf_gvs; eauto. solve_wf_value_list.
    clear - JJ HwfSystem HmInS HFinPs' H2 H4.
    eapply wf_ExecutionContext__at_beginning_of_function; eauto.
  split.
  SCase "2".
    repeat (split; auto). eauto.
  SCase "3".
    simpl. intros b HbInBs. destruct b as [? [? ? t]].
    destruct t; auto.

Case "sExCall".
  match goal with
  | H6:exCallUpdateLocals _ _ _ _ _ _ = _ |- _ =>unfold exCallUpdateLocals in H6
  end.
  destruct noret0.
    match goal with | H6: munit _ = munit _ |- _ => inv H6 end.
    eapply preservation_cmd_non_updated_case in HwfS1; eauto.

    assert (exists t0,
      getCmdTyp (insn_call rid false ca rt1 va1 fv lp) = Some t0) as J.
      destruct_wfCfgState HwfCfg HwfS1.
      eapply wf_system__wf_cmd
        with (c:=insn_call rid false ca rt1 va1 fv lp) in HBinF1; eauto.
      simpl.
      inv HBinF1; eauto.
      apply in_or_app; simpl; auto.
    destruct J as [t0 J].
    match goal with
    | H6: match ?oresult with
          | Some _ => _
          | None => _
          end = Some _ |- _ =>
      destruct oresult; tinv H6;
      remember (fit_gv (los, nts) rt1 g) as R;
      destruct R; inv H6
    end.
    eapply preservation_cmd_updated_case with (t0:=rt1) in HwfS1; simpl; eauto.
      inv J.
      apply wf_State__inv in HwfS1; auto.
      destruct HwfS1 as [Hwftd [Hwfg [Hwflc Hwfc]]].
      inv Hwfc.
      match goal with
      | H11: module_intro _ _ _ = module_intro _ _ _,
        H24: wf_insn_base _ _ _ |- _ => inv H11; inv H24
      end.
      eapply fit_gv_gv2gvs__wf_gvs_aux; eauto.
Qed.

Lemma preservation_star: forall cfg IS IS' tr (Hwfcfg: wf_Config cfg),
  wf_State cfg IS ->
  sop_star cfg IS IS' tr ->
  wf_State cfg IS'.
Proof.
  intros.
  induction H0; auto.
    apply preservation in H0; auto.
Qed.

Lemma preservation_plus: forall cfg IS IS' tr (Hwfcfg: wf_Config cfg),
  wf_State cfg IS ->
  sop_plus cfg IS IS' tr ->
  wf_State cfg IS'.
Proof.
  intros.
  apply sop_plus__implies__sop_star in H0.
  eapply preservation_star; eauto.
Qed.

(*********************************************)
(** * Progress *)

Lemma state_tmn_typing : forall TD s m f l1 ps1 cs1 tmn1 defs id1 lc,
  isReachableFromEntry f (l1, stmts_intro ps1 cs1 tmn1) ->
  wf_insn s m f (l1, stmts_intro ps1 cs1 tmn1) (insn_terminator tmn1) ->
  Some defs = inscope_of_tmn f (l1, stmts_intro ps1 cs1 tmn1) tmn1 ->
  wf_defs TD f lc defs ->
  wf_fdef s m f -> uniqFdef f ->
  In id1 (getInsnOperands (insn_terminator tmn1)) ->
  exists t, exists gv,
    lookupTypViaIDFromFdef f id1 = munit t /\
    lookupAL _ lc id1 = Some gv /\ wf_GVs TD gv t.
Proof.
  intros TD s m f l1 ps1 cs1 tmn1 defs id1 lc Hreach HwfInstr Hinscope
    HwfDefs HwfF HuniqF HinOps.
  apply wf_insn__wf_insn_base in HwfInstr;
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr. find_wf_operand_list. subst. find_wf_operand_by_id.

  eapply wf_defs_elim; eauto.
    eapply terminator_operands__in_scope; eauto.
Qed.

Lemma state_cmd_typing : forall TD s m f b c defs id1 lc,
  NoDup (getStmtsLocs (snd b)) ->
  isReachableFromEntry f b ->
  wf_insn s m f b (insn_cmd c) ->
  Some defs = inscope_of_cmd f b c ->
  wf_defs TD f lc defs ->
  wf_fdef s m f -> uniqFdef f ->
  In id1 (getInsnOperands (insn_cmd c)) ->
  exists t, exists gv,
    lookupTypViaIDFromFdef f id1 = munit t /\
    lookupAL _ lc id1 = Some gv /\ wf_GVs TD gv t.
Proof.
  intros TD s m f b c defs id1 lc Hnodup Hreach HwfInstr Hinscope HwfDefs
    HwfF HuniqF HinOps.
  apply wf_insn__wf_insn_base in HwfInstr;
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.

  find_wf_operand_list. subst. find_wf_operand_by_id.
  eapply wf_defs_elim; eauto.
    eapply cmd_operands__in_scope; eauto.
Qed.

Lemma const2GV_isnt_stuck : forall TD S gl c t,
  wf_const S TD c t ->
  wf_global TD S gl ->
  exists gv, @const2GV GVsSig TD gl c = Some gv.
Proof.
  intros.
  destruct const2GV_isnt_stuck_mutind as [J _].
  unfold const2GV_isnt_stuck_Prop in J.
  unfold const2GV.
  assert (G:=H). apply wf_const__wf_typ in G. inv G.
  eapply J in H; eauto.
  destruct H as [gv H].
  rewrite H. eauto.
Qed.

Lemma getOperandValue_inCmdOps_isnt_stuck : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVsMap)
  (gl : GVMap)
  (Hwfg : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (c : cmd)
  (Hreach : isReachableFromEntry f (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_cmd f (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn) c)
  (Hinscope : wf_defs (los,nts) f lc l0)
  (v : value)
  (Hvincs : valueInCmdOperands v c),
  exists gv : GVs,
    getOperandValue (los, nts) v lc gl = ret gv.
Proof.
  intros.
  destruct v as [vid | vc]; simpl.
    assert (exists t, exists gv,
                lookupTypViaIDFromFdef f vid = munit t /\
                lookupAL _ lc vid = Some gv /\
                wf_GVs (los,nts) gv t) as Hlkup.
      eapply state_cmd_typing; eauto.
      eapply wf_system__uniq_block; eauto.
      eapply wf_system__wf_cmd; eauto using In_middle.
      eapply wf_system__wf_fdef; eauto.
      eapply wf_system__uniqFdef; eauto.
      apply valueInCmdOperands__InOps; auto.
    destruct Hlkup as [gt [gv [Hlktyp [Hlkup Hwfgv]]]].
    simpl. rewrite Hlkup. eauto.

    assert (In c (cs1++c::cs)) as H.
      apply in_or_app. simpl. auto.
    eapply wf_system__wf_cmd with (c:=c) in HbInF; eauto.
    eapply wf_cmd__wf_value with (v:=value_const vc) in HbInF; eauto.
    destruct HbInF as [t Hwfc].
    inv Hwfc.
    eapply const2GV_isnt_stuck with (S:=s)(t:=t); eauto.
Qed.

Lemma getOperandValue_inTmnOperans_isnt_stuck : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  (tmn : terminator)
  (lc : GVsMap)
  (gl : GVMap)
  (Hwfg : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f (l1, stmts_intro ps1 cs1 tmn))
  (HbInF : blockInFdefB (l1, stmts_intro ps1 cs1 tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_tmn f (l1, stmts_intro ps1 cs1 tmn) tmn)
  (Hinscope : wf_defs (los,nts) f lc l0)
  (v : value)
  (Hvincs : valueInTmnOperands v tmn),
  exists gv : GVs, getOperandValue (los, nts) v lc gl = ret gv.
Proof.
  intros.
  destruct v as [vid | vc].
    assert (HwfInstr:=HbInF).
    eapply wf_system__wf_tmn in HwfInstr; eauto.
    assert (exists t, exists gv,
      lookupTypViaIDFromFdef f vid = munit t /\
      lookupAL _ lc vid = Some gv /\
      wf_GVs (los,nts) gv t) as Hlkup.
      eapply state_tmn_typing; eauto.
      eapply wf_system__wf_fdef; eauto.
      eapply wf_system__uniqFdef; eauto.
      apply valueInTmnOperands__InOps; auto.
    destruct Hlkup as [gt [gv [Hlktyp [Hlkup Hwfgv]]]].
    simpl.
    rewrite Hlkup. eauto.

    eapply wf_system__wf_tmn in HbInF; eauto.
    eapply wf_tmn__wf_value with (v:=value_const vc) in HbInF; eauto.
    destruct HbInF as [ct Hwfc].
    inv Hwfc.
    eapply const2GV_isnt_stuck with (S:=s)(t:=ct); eauto.
Qed.

Lemma values2GVs_isnt_stuck : forall
  l22
  (s : system)
  los nts
  (ps : list product)
  (f : fdef)
  (i0 : id)
  (i1 : inbounds)
  (t : typ)
  (v : value)
  (l2 : list (sz * value))
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVsMap)
  (gl : GVMap)
  (Hwfg1 : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd) t'
  (Hreach : isReachableFromEntry f
             (l1, stmts_intro ps1 (cs1 ++ insn_gep i0 i1 t v l2 t':: cs) tmn))
  (HbInF : blockInFdefB
            (l1, stmts_intro ps1 (cs1 ++ insn_gep i0 i1 t v l2 t':: cs) tmn) f =
          true)
  (l0 : list atom)
  (HeqR : ret l0 =
         inscope_of_cmd f
           (l1, stmts_intro ps1 (cs1 ++ insn_gep i0 i1 t v l2 t':: cs) tmn)
           (insn_gep i0 i1 t v l2 t'))
  (Hinscope : wf_defs (los,nts) f lc l0)
  (Hex : exists l21, l2 = l21 ++ l22),
  exists vidxs, values2GVs (los, nts) l22 lc gl = Some vidxs.
Proof.
  induction l22 as [|[s v] l22]; intros; simpl; eauto.
    destruct Hex as [l21 Hex]; subst.
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv)
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl. unfold valueInListValue. right.
        change v with (snd (s, v)) at 1.
        apply In_map. apply in_or_app. right. left. trivial.

    destruct J as [gv J].
    rewrite J.
    eapply IHl22 in HbInF; eauto.
      destruct HbInF as [vidxs HbInF].
      rewrite HbInF. eauto.

      exists (l21 ++ [(s, v)]).
      rewrite app_assoc. simpl. trivial.
Qed.

Lemma wf_phinodes__getIncomingValuesForBlockFromPHINodes : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  l0
  (lc : GVsMap)
  (gl : GVMap)
  (t : list atom)
  l1 ps1 cs1 tmn1
  (Hwfg : wf_global (los,nts) s gl)
  (HeqR : ret t = inscope_of_tmn f (l1, stmts_intro ps1 cs1 tmn1) tmn1)
  (Hinscope : wf_defs (los,nts) f lc t)
  (HuniqF : uniqFdef f)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  ps2
  (Hreach : isReachableFromEntry f (l1, stmts_intro ps1 cs1 tmn1))
  (HbInF : blockInFdefB
            (l1, stmts_intro ps1 cs1 tmn1) f = true)
  (HwfB : wf_block s (module_intro los nts ps) f
             (l1, stmts_intro ps1 cs1 tmn1))
  (H8 : wf_phinodes s (module_intro los nts ps) f
         (l0, stmts_intro ps' cs' tmn') ps2)
  (Hsucc : In l0 (successors_terminator tmn1))
  (Hin: exists ps1, ps' = ps1 ++ ps2),
   exists RVs : list (id * GVs),
     getIncomingValuesForBlockFromPHINodes (los, nts) ps2
       (l1, stmts_intro ps1 cs1 tmn1) gl lc =
       ret RVs.
Proof.
  intros.
  induction ps2; simpl.
    exists nil. auto.

    destruct a as [i0 t0 l2].
    match goal with | H8: wf_phinodes _ _ _ _ _ |- _ => inv H8 end.
    match goal with | H5: wf_insn _ _ _ _ _ |- _ => inv H5 end.
    assert (exists v, getValueViaLabelFromValuels l2 l1 = Some v) as J.
      match goal with
      | H13: wf_phinode _ _ _ |- _ =>
         clear - H13 HbInF HuniqF Hsucc; inv H13
      end.
      unfold check_list_value_l in H0.
      simpl_split.
      destruct H0 as [J1 [J2 J3]].
      eapply In__getValueViaLabelFromValuels; eauto.
      destruct J2 as [_ J2].
      apply J2.
      eapply successors_predecessors_of_block; eauto.

    destruct J as [v J]. unfold getValueViaBlockFromValuels. simpl.
    rewrite J.
    destruct v as [vid | vc].
    Case "vid".
      assert (exists gv1, lookupAL _ lc vid = Some gv1) as J1.
        Focus.
        assert (In vid t) as K.
          eapply incoming_value__in_scope; eauto.
        apply wf_defs_elim with (id1:=vid) in Hinscope; auto.
        destruct Hinscope as [? [? [gv1 [? [Hinscope ?]]]]].
        exists gv1. auto.

      destruct J1 as [gv1 J1].
      simpl. rewrite J1.
      apply IHps2 in H6.
        destruct H6 as [RVs H6]; rewrite H6.
        exists ((i0, gv1) :: RVs). auto.

        destruct Hin as [ps3 Hin]. subst.
        exists (ps3++[insn_phi i0 t0 l2]).
        simpl_env. auto.

    Case "vc".
      find_wf_value_list.
      match goal with
      | H2: wf_value_list _ |- _ =>
        eapply wf_value_list__getValueViaLabelFromValuels__wf_value in H2; eauto;
        inv H2
      end.
      destruct (@const2GV_isnt_stuck (los,nts) s gl vc t0); auto.
      simpl. rewrite H.
      match goal with
      | H6: wf_phinodes _ _ _ _ _ |- _ =>
      apply IHps2 in H6; try solve [
        destruct H6 as [RVs H6];
        rewrite H6; simpl;
        exists ((i0, x) :: RVs); auto |

        destruct Hin as [ps3 Hin]; subst;
        exists (ps3++[insn_phi i0 t0 l2]);
        simpl_env; auto
      ]
      end.
Qed.

Lemma params2GVs_isnt_stuck : forall
  p22
  (s : system)
  los nts
  (ps : list product)
  (f : fdef)
  (i0 : id)
  n c rt va v p2
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVsMap)
  (gl : GVMap)
  (Hwfg1 : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f
             (l1, stmts_intro ps1
               (cs1 ++ insn_call i0 n c rt va  v p2 :: cs) tmn))
  (HbInF : blockInFdefB
            (l1, stmts_intro ps1
              (cs1 ++ insn_call i0 n c rt va v p2 :: cs) tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 =
         inscope_of_cmd f
           (l1, stmts_intro ps1
             (cs1 ++ insn_call i0 n c rt va v p2 :: cs) tmn)
           (insn_call i0 n c rt va v p2))
  (Hinscope : wf_defs (los,nts) f lc l0)
  (Hex : exists p21, p2 = p21 ++ p22),
  exists gvs, params2GVs (los, nts) p22 lc gl = Some gvs.
Proof.
  induction p22; intros; simpl; eauto.

    destruct a as [[t0 attr0] v0].
    destruct Hex as [p21 Hex]; subst.
    assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv)
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl. unfold valueInParams. right.
        assert (J:=@in_split_r _ _ (p21 ++ (t0, attr0, v0) :: p22)
          (t0, attr0, v0)).
        remember (split (p21 ++ (t0, attr0, v0) :: p22)) as R.
        destruct R.
        simpl in J. apply J.
        apply In_middle.
    destruct J as [gv J].
    rewrite J.
    eapply IHp22 in HbInF; eauto.
      destruct HbInF as [vidxs HbInF].
      rewrite HbInF. eauto.

      exists (p21 ++ [(t0, attr0,v0)]). simpl_env. auto.
Qed.

Lemma initializeFrameValues__total_aux : forall los nts s fattr ft fid va
  la2 la1 lc1
  (HwfF: wf_fheader s (los, nts) (fheader_intro fattr ft fid (la1 ++ la2) va))
  gvs2,
  exists lc2, @_initializeFrameValues GVsSig (los,nts) la2 gvs2 lc1 = Some lc2.
Proof.
  induction la2; simpl in *; intros.
    eauto.

    destruct a. destruct p.
    assert (HwfF':=HwfF).
    simpl_env in HwfF'.
    rewrite_env ((la1 ++ [(t, a, i0)]) ++ la2) in HwfF'.
    inv HwfF. find_middle_element.
    find_wf_typ_list.
    match goal with | H7: wf_typ_list _ |- _ =>
      apply wf_typ_list__in_args__wf_typ with (t:=t)(a:=a)(i0:=i0) in H7; auto
    end.

    destruct gvs2.
      apply IHla2 with (gvs2:=nil)(lc1:=lc1) in HwfF'.
      destruct HwfF' as [lc2 J'].
      rewrite J'.
      match goal with | H8: wf_typ _ _ _ |- _ =>
        apply gundef__total in H8;
        destruct H8 as [gv H8]; rewrite H8; eauto
      end.

      apply IHla2 with (gvs2:=gvs2)(lc1:=lc1) in HwfF'.
      destruct HwfF' as [lc2 J'].
      rewrite J'.
      assert (exists gvs2, GVsSig.(lift_op1) (fit_gv (los, nts) t) g t
        = Some gvs2) as W.
        apply GVsSig.(lift_op1__isnt_stuck); eauto using fit_gv__total.
      destruct W as [gvs2' W].
      rewrite W. eauto.
Qed.

Lemma initLocal__total : forall los nts Ps s fattr ft fid va bs2 la2
  (HwfF: wf_fdef s (module_intro los nts Ps)
    (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  gvs2,
  exists lc2, @initLocals GVsSig (los,nts) la2 gvs2 = Some lc2.
Proof.
  intros.
  unfold initLocals. inv HwfF.
  eapply initializeFrameValues__total_aux with (la1:=nil); eauto.
Qed.

Ltac gvs_inhabited_inv H := apply GVsSig.(inhabited_inv) in H; inv H.

Lemma wf_params_spec' : forall TD gvss lp,
  wf_params TD gvss lp ->
  exists gvs, gvs @@ gvss.
Proof.
  induction gvss; simpl; intros.
    exists nil. simpl. auto.

    destruct lp as [|[[]]]; tinv H.
    destruct H as [J1 J2].
    inv J1. gvs_inhabited_inv H1.
    apply IHgvss in J2. destruct J2 as [gvs J2].
    exists (x::gvs). simpl. auto.
Qed.

Lemma params2GVs_inhabited : forall los nts Ps F gl lc
  (Hwfc : wf_lc (los,nts) F lc) S
  (Hwfg : wf_global (los, nts) S gl)
  tvs lp gvss,
  wf_value_list
    (List.map
      (fun (p : typ * attributes * value) =>
        let '(typ_', attr, value_'') := p in
          (S, (module_intro los nts Ps), F, value_'', typ_'))
      tvs) ->
  lp = List.map
        (fun (p : typ * attributes * value) =>
          let '(typ_', attr, value_'') := p in (typ_', attr, value_''))
        tvs ->
  params2GVs (los,nts) lp lc gl = Some gvss -> exists gvs, gvs @@ gvss.
Proof.
  intros.
  eapply params2GVs_wf_gvs in H; eauto.
  apply wf_params_spec' in H; auto.
Qed.

Definition undefined_state (cfg: Config) (S : State): Prop :=
match cfg with
| {| CurTargetData := td; CurProducts := ps; Globals := gl; FunTable := fs |} =>
  match S with
  | {| ECS := {|
                CurCmds := nil;
                Terminator := insn_return _ _ _;
                Allocas := als |} ::
              {| CurCmds := c::_ |} :: _;
       Mem := M |} => free_allocas td M als = None
  | _ => False
  end \/
  match S with
  | {| ECS := {|
                CurBB := _;
                CurCmds := nil;
                Terminator := insn_return_void _;
                Allocas := als |} ::
              {| CurCmds := c::_ |} :: _;
       Mem := M |} => free_allocas td M als = None \/
                      match getCallerReturnID c with
                      | Some _ => True
                      | _ => False
                      end
  | _ => False
  end \/
  match S with
  | {| ECS := {|
                CurBB := (_, stmts_intro _ _ (insn_unreachable _));
                CurCmds := nil;
                Terminator := (insn_unreachable _)
               |} :: _
     |} => True
  | _ => False
  end \/
  match S with
  | {| ECS :=
         {| CurCmds := insn_malloc _ t v a::_ ;
            Locals := lc|} :: _;
       Mem := M |}
  | {| ECS :=
         {| CurCmds := insn_alloca _ t v a::_ ;
            Locals := lc|} :: _;
       Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some gvs =>
           match getTypeAllocSize td t with
           | Some asz => exists gn, gn @ gvs /\
               match malloc td M asz gn a with
               | None => True
               | _ => False
               end
           | _ => False
           end
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| ECS := {| CurCmds := insn_free _ _ v::_ ;
                             Locals := lc|} :: _;
       Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some gvs => exists gv, gv @ gvs /\
           match free td M gv with
           | None => True
           | _ => False
           end
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| ECS := {| CurCmds := insn_load _ t v a::_ ;
                             Locals := lc|} :: _;
       Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some gvs => exists gv, gv @ gvs /\
           match mload td M gv t a with
           | None => True
           | _ => False
           end
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| ECS := {| CurCmds := insn_store _ t v v0 a::_ ;
                             Locals := lc|} :: _;
       Mem := M |} =>
       match getOperandValue td v lc gl,
             getOperandValue td v0 lc gl with
       | Some gvs, Some mgvs => exists gv, exists mgv, gv @ gvs /\ mgv @ mgvs /\
           match mstore td M mgv t gv a with
           | None => True
           | _ => False
           end
       | _, _ => False
       end
  | _ => False
  end \/
  match S with
  | {|
       ECS := {| CurCmds := insn_call i0 n _ rt1 _ v p::_ ;
                             Locals := lc|} :: _;
       Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some fptrs =>
            exists fptr, fptr @ fptrs /\
            match lookupFdefViaPtr ps fs fptr,
                  lookupExFdecViaPtr ps fs fptr with
            | None, Some (fdec_intro (fheader_intro fa rt fid la va) dck) =>
                match params2GVs td p lc gl with
                | Some gvss =>
                    exists gvs, gvs @@ gvss /\
                    match external_intrinsics.callExternalOrIntrinsics
                            td gl M fid rt (args2Typs la) dck gvs with
                    | Some (oresult, _, _) =>
                       match exCallUpdateLocals td rt1 n i0 oresult lc with
                       | None => True
                       | _ => False
                       end
                    | None => True
                    end
                | _ => False
                end
            | None, None => True
            | _, _ => False
            end
       | _ => False
       end
  | _ => False
  end
end.

Ltac undefbehave := unfold undefined_state; simpl;
  try solve [
    auto |
    right; auto |
    right; right; auto |
    right; right; right; right; auto |
    right; right; right; right; right; auto |
    right; right; right; right; right; right; auto |
    right; right; right; right; right; right; right; auto |
    right; right; right; right; right; right; right; right; auto
  ].

Lemma progress : forall cfg S1 (HwfCfg: wf_Config cfg),
  wf_State cfg S1 ->
  s_isFinialState cfg S1 <> None \/
  (exists S2, exists tr, sInsn cfg S1 S2 tr) \/
  undefined_state cfg S1.
Proof.
  intros cfg S1 HwfCfg HwfS1.
  destruct cfg as [s [los nts] ps gl fs].
  destruct S1 as [ecs M].
  destruct HwfCfg as [Hwftd1 [Hwfg1 [HwfSys1 HmInS1]]].
  destruct HwfS1 as [Hnonempty HwfECs].
  destruct ecs; try congruence.
  destruct e as [f b cs tmn lc als].
  destruct HwfECs as [[Hreach
                        [HbInF [HfInPs [Hwflc [Hinscope [l1 [ps1 [cs1 Heq]]]]]]]]
                      [HwfECs HwfCall]].
  subst b.
  destruct cs.
  Case "cs=nil".
    remember (inscope_of_tmn f (l1, stmts_intro ps1 (cs1 ++ nil) tmn) tmn) as R.
    destruct R; try solve [inversion Hinscope].
    destruct_tmn tmn.
    SCase "tmn=ret".
      simpl in HwfCall.
      assert (exists gv : GVs,
        getOperandValue (los, nts) value5 lc gl = ret gv) as H.
        eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
         simpl. auto.
      destruct H as [gv H].
      destruct ecs.
        simpl. rewrite H. left. congruence.

        right.
        destruct e as [f' b' cs' tmn' lc' als'].
        assert (J:=HbInF).
        apply HwfCall in J. clear HwfCall.
        destruct cs'; try solve [inversion J].
        destruct c as [ | | | | | | | | | | | | | | | |i1 n c rt0 va0 v0 p];
          try solve [inversion J].
        clear J.
        remember (free_allocas (los,nts) M als) as Rm.
        destruct Rm as [M' |]; try solve [undefbehave].
        left. symmetry in HeqRm.
        rename HeqRm into J.
        assert (exists lc'',
          returnUpdateLocals (los,nts) (insn_call i1 n c rt0 va0 v0 p) value5
            lc lc' gl = Some lc'') as Hretup.
          unfold returnUpdateLocals. simpl.
          rewrite H.
          destruct n.
            exists lc'. auto.

            destruct HwfECs as [[Hreach'
              [HbInF' [HfInPs' [Hwflc' [Hinscope' [l1' [ps1' [cs1' Heq']]]]]]]]
              [HwfECs HwfCall]]; subst.
            eapply wf_system__wf_cmd
              with (c:=insn_call i1 false c rt0 va0 v0 p)
              in HbInF'; eauto using in_middle.
            inv HbInF'.
            match goal with
            | H6: module_intro _ _ _ = module_intro _ _ _ |- _ => inv H6
            end.
            assert (exists gvs2,
              GVsSig.(lift_op1) (fit_gv (layouts5, namedts5) rt0) gv rt0
                = Some gvs2) as W.
              match goal with | H19: wf_insn_base _ _ _ |- _ => inv H19 end.
              apply GVsSig.(lift_op1__isnt_stuck); eauto using fit_gv__total.
            destruct W as [gvs2' W]. rewrite W.
            eauto.

        destruct Hretup as [lc'' Hretup].
        exists (mkState ((mkEC f' b' cs' tmn' lc'' als')::ecs) M').
        exists events.E0.
        eauto.

    SCase "tmn=ret void".
      simpl in HwfCall.
      destruct ecs.
        simpl. unfold const2GV. simpl. left. congruence.

        right.
        destruct e as [f' b' cs' tmn' lc' als'].
        assert (J:=HbInF).
        apply HwfCall in J. clear HwfCall.
        destruct cs'; try solve [inversion J].
        destruct_cmd c; try solve [inversion J]. clear J.
        remember (free_allocas (los,nts) M als) as Rm.
        destruct Rm as [M' |]; try solve [undefbehave].
        symmetry in HeqRm.
        rename HeqRm into J.
        destruct n; try solve [undefbehave].
        left.
        exists (mkState ((mkEC f' b' cs' tmn' lc' als')::ecs) M').
        exists events.E0.
        eauto.

    SCase "tmn=br".
      right. left.
      assert (wf_fdef s (module_intro los nts ps) f) as HwfF.
        eapply wf_system__wf_fdef; eauto.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists cond, getOperandValue (los,nts) value5 lc gl =
        Some cond) as Hget.
        eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
          simpl. auto.
      destruct Hget as [cond Hget].
      assert (Hwfc := HbInF).
      eapply wf_system__wf_tmn in Hwfc; eauto.
      assert (exists c, c @ cond) as Hinh.
        inv Hwfc.
        eapply getOperandValue__inhabited in Hget; eauto.
        gvs_inhabited_inv Hget. eauto.
      destruct Hinh as [c Hinh].
      assert (exists sts',
              Some sts' =
              (if isGVZero (los,nts) c
                 then lookupBlockViaLabelFromFdef f l3
                 else lookupBlockViaLabelFromFdef f l2)) as HlkB.
        inv Hwfc.
        destruct (isGVZero (los, nts) c); eauto.

      destruct HlkB as [[ps' cs' tmn'] HlkB].
      assert (exists lc', switchToNewBasicBlock (los, nts)
        (if isGVZero (los, nts) c then l3 else l2, stmts_intro ps' cs' tmn')
        (l1, stmts_intro ps1 (cs1++nil) (insn_br id5 value5 l2 l3)) gl lc =
          Some lc') as Hswitch.
         assert (exists RVs,
           getIncomingValuesForBlockFromPHINodes (los, nts) ps'
             (l1, stmts_intro ps1 (cs1++nil) (insn_br id5 value5 l2 l3)) gl lc =
           Some RVs) as J.
           assert (HwfB := HbInF).
           eapply wf_system__blockInFdefB__wf_block in HwfB; eauto.
           simpl_env in *.
           destruct (isGVZero (los, nts) c).
             assert (J:=HlkB).
             symmetry in J.
             apply lookupBlockViaLabelFromFdef_inv in J; auto.
             destruct J as [Heq J]; subst.
             eapply wf_system__lookup__wf_block in HlkB; eauto.
             inv HlkB. clear H9 H8.
             eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes
               with (ps':=ps')(cs':=cs')(tmn':=tmn')(l0:=l3); eauto.
               simpl. auto.
               exists nil. auto.

             assert (J:=HlkB).
             symmetry in J.
             apply lookupBlockViaLabelFromFdef_inv in J; auto.
             destruct J as [Heq J]; subst.
             eapply wf_system__lookup__wf_block in HlkB; eauto.
             inv HlkB. clear H9 H8.
             eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes
               with (ps':=ps')(cs':=cs')(tmn':=tmn')(l0:=l2); eauto.
               simpl. auto.
               exists nil. auto.

         destruct J as [RVs J].
         unfold switchToNewBasicBlock. simpl.
         rewrite J.
         exists (updateValuesForNewBlock RVs lc). auto.

      destruct Hswitch as [lc' Hswitch].
      exists (mkState ((mkEC f (if isGVZero (los, nts) c then l3 else l2, 
                                stmts_intro ps' cs' tmn') cs' tmn' lc'
              als)::ecs) M).
      exists events.E0. eauto.

    SCase "tmn=br_uncond".
      right. left.
      assert (wf_fdef s (module_intro los nts ps) f) as HwfF.
        eapply wf_system__wf_fdef; eauto.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists sts2, Some sts2 = lookupBlockViaLabelFromFdef f l2)
          as HlkB.
        eapply wf_system__wf_tmn in HbInF; eauto.
        inv HbInF. eauto.

      destruct HlkB as [[ps' cs' tmn'] HlkB].

      assert (exists lc', switchToNewBasicBlock (los, nts)
        (l2, stmts_intro ps' cs' tmn')
        (l1, stmts_intro ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc =
          Some lc') as Hswitch.
         assert (exists RVs,
           getIncomingValuesForBlockFromPHINodes (los, nts) ps'
             (l1, stmts_intro ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc =
           Some RVs) as J.
           assert (HwfB := HbInF).
           eapply wf_system__blockInFdefB__wf_block in HwfB; eauto.
           eapply wf_system__lookup__wf_block in HlkB; eauto.
           inv HlkB. clear H9 H8.
           eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes
             with (l0:=l2); eauto.
             simpl. auto.
             exists nil. auto.

         destruct J as [RVs J].
         unfold switchToNewBasicBlock. simpl.
         rewrite J.
         exists (updateValuesForNewBlock RVs lc). auto.

      destruct Hswitch as [lc' Hswitch].
      exists (mkState ((mkEC f (l2, stmts_intro ps' cs' tmn') cs' tmn' lc'
              als)::ecs) M).
      exists events.E0. eauto.

    SCase "tmn=unreachable".
      undefbehave.

  Case "cs<>nil".
    assert (wf_insn s (module_intro los nts ps) f
      (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn) (insn_cmd c)) as Hwfc.
      assert (In c (cs1++c::cs)) as H.
        apply in_or_app. simpl. auto.
      eapply wf_system__wf_cmd with (c:=c) in HbInF; eauto.
    remember (inscope_of_cmd f (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn) c) as R.
    destruct R; try solve [inversion Hinscope].
    right.
    destruct c as [i0 b s0 v v0|i0 f0 f1 v v0|i0 t v l2|i0 t v t0 v0 l2 t0'|
                   i0 t v a|i0 t v|i0 t v a|i0 t v a|i0 t v v0 a|i0 i1 t v l2|
                   i0 t t0 v t1|i0 e t v t0|i0 c t v t0|i0 c t v v0|
                   i0 f0 f1 v v0|i0 v t v0 v1|i0 n c rt1 va1 v p].
  SCase "c=bop".
    left.
    assert (exists gv3, BOP (los,nts) lc gl b s0 v v0 = Some gv3)
      as Hinsn_bop.
      unfold BOP.
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv)
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv)
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0.
      inv Hwfc. apply wf_value__wf_typ in H6. destruct H6.
      apply GVsSig.(lift_op2__isnt_stuck); eauto using mbop_is_total.
      eauto.
    destruct Hinsn_bop as [gv3 Hinsn_bop].
    exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_bop i0 b s0 v v0 :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv3);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists events.E0. eauto.

  SCase "c=fbop".
    left.
    assert (exists gv3, FBOP (los,nts) lc gl f0 f1 v v0 = Some gv3)
      as Hinsn_fbop.
      unfold FBOP.
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv)
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv)
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0.
      inv Hwfc. apply wf_value__wf_typ in H6. destruct H6.
      apply GVsSig.(lift_op2__isnt_stuck); eauto using mfbop_is_total.
      eauto.

    destruct Hinsn_fbop as [gv3 Hinsn_fbop].
    exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_fbop i0 f0 f1 v v0 :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv3);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists events.E0. eauto.

  SCase "c=extractvalue".
    left.
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv)
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', extractGenericValue (los, nts) t gv l2 = Some gv')
      as J'.
      unfold extractGenericValue.
      inv Hwfc.
      match goal with
      | H12: exists _:_, _ |- _ => destruct H12 as [idxs [o [J1 J2]]]
      end.
      rewrite J1. rewrite J2.
      apply GVsSig.(lift_op1__isnt_stuck); eauto using mget'_is_total.
      eauto.
    destruct J' as [gv' J'].
    exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_extractvalue i0 t v l2 typ':: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv');
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists events.E0. eauto.

  SCase "c=insertvalue".
    left.
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv)
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', getOperandValue (los, nts) v0 lc gl = Some gv')
      as J'.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J' as [gv' J'].
    assert (exists gv'', insertGenericValue (los, nts) t gv l2 t0 gv' =
      Some gv'') as J''.
      unfold insertGenericValue.
      inv Hwfc.
      match goal with
      | H15: exists _:_, exists _:_, _ |- _ =>
         destruct H15 as [idxs [o [J1 J2]]]; rewrite J1; rewrite J2
      end.
      match goal with
      | H9: wf_value _ _ _ _ ?t0 |- context [mset' _ _ ?t0 _] =>
        apply wf_value__wf_typ in H9; destruct H9
      end.
      apply GVsSig.(lift_op2__isnt_stuck); eauto using mset'_is_total.
    destruct J'' as [gv'' J''].
    exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_insertvalue i0 t v t0 v0 l2 :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv'');
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists events.E0. eauto.

  SCase "c=malloc".
    inv Hwfc.
    match goal with
    | H11: wf_typ _ _ _ |- _ =>
      apply wf_typ__feasible_typ in H11;
      eapply feasible_typ_inv'' in H11; eauto;
      destruct H11 as [ssz [asz [J1 J2]]]
    end.
    assert (exists gvs, getOperandValue (los, nts) v lc gl = Some gvs)
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gn, gn @ gvs) as Hinh.
      eapply getOperandValue__inhabited in J; eauto.
      gvs_inhabited_inv J. eauto.
    destruct Hinh as [gn Hinh].
    remember (malloc (los, nts) M asz gn a) as R.
    destruct R as [[M' mb] |].
      left.
      exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_malloc i0 t v a :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals :=
               (updateAddAL _ lc i0 ($ (blk2GV (los, nts) mb) # typ_pointer t$));
                Allocas := als |} :: ecs;
         Mem := M' |}.
      exists events.E0.
      eauto.

      unfold undefined_state.
      right. rewrite J. rewrite J2. right. right. right. left.
      exists gn. rewrite <- HeqR0. undefbehave.

  SCase "free".
    assert (exists gvs, getOperandValue (los, nts) v lc gl = Some gvs)
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gv, gv @ gvs) as Hinh.
      inv Hwfc.
      eapply getOperandValue__inhabited in J; eauto.
      gvs_inhabited_inv J. eauto.
    destruct Hinh as [gv Hinh].
    remember (free (los, nts) M gv) as R.
    destruct R as [M'|].
      left.
      exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_free i0 t v :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc;
                Allocas := als |} :: ecs;
         Mem := M' |}.
      exists events.E0.
      eauto.

      unfold undefined_state.
      right. rewrite J. right. right. right. right. left.
      exists gv. rewrite <- HeqR0. undefbehave.

  SCase "alloca".
    inv Hwfc.
    match goal with
    | H11: wf_typ _ _ _ |- _ =>
      apply wf_typ__feasible_typ in H11;
      eapply feasible_typ_inv'' in H11; eauto;
      destruct H11 as [ssz [asz [J1 J2]]]
    end.
    assert (exists gvs, getOperandValue (los, nts) v lc gl = Some gvs)
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gn, gn @ gvs) as Hinh.
      eapply getOperandValue__inhabited in J; eauto.
      gvs_inhabited_inv J. eauto.
    destruct Hinh as [gn Hinh].
    remember (malloc (los, nts) M asz gn a) as R.
    destruct R as [[M' mb] |].
      left.
      exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_alloca i0 t v a :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals :=
               (updateAddAL _ lc i0 ($ (blk2GV (los, nts) mb) # typ_pointer t$));
                Allocas := (mb::als) |} :: ecs;
         Mem := M' |}.
      exists events.E0.
      eauto.

      right.
      unfold undefined_state.
      right. rewrite J. rewrite J2. right. right. left. exists gn.
      rewrite <- HeqR0. undefbehave.

  SCase "load".
    assert (exists gvs, getOperandValue (los, nts) v lc gl = Some gvs)
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gv, gv @ gvs) as Hinh.
      inv Hwfc.
      eapply getOperandValue__inhabited in J; eauto.
      gvs_inhabited_inv J. eauto.
    destruct Hinh as [gv Hinh].
    remember (mload (los,nts) M gv t a) as R.
    destruct R as [gv' |].
      left.
      exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_load i0 t v a :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := updateAddAL _ lc i0 ($ gv' # t$);
                Allocas := als |} :: ecs;
         Mem := M |}.
      exists events.E0.
      eauto.

      right.
      unfold undefined_state.
      right. rewrite J. right. right. right. right. left. exists gv.
      rewrite <- HeqR0. undefbehave.

  SCase "store".
    assert (exists gvs, getOperandValue (los, nts) v lc gl = Some gvs)
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gvs, getOperandValue (los, nts) v0 lc gl = Some gvs)
      as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [mgvs J0].
    inv Hwfc.
    assert (exists gv, gv @ gvs) as Hinh1.
      eapply getOperandValue__inhabited in J; eauto.
      gvs_inhabited_inv J. eauto.
    destruct Hinh1 as [gv Hinh1].
    assert (exists mgv, mgv @ mgvs) as Hinh2.
      eapply getOperandValue__inhabited in J0; eauto.
      gvs_inhabited_inv J0. eauto.
    destruct Hinh2 as [mgv Hinh2].
    remember (mstore (los,nts) M mgv t gv a) as R.
    destruct R as [M' |].
      left.
      exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_store i0 t v v0 a :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc;
                Allocas := als |} :: ecs;
         Mem := M' |}.
      exists events.E0.
      eauto.

      right.
      unfold undefined_state.
      right. rewrite J. rewrite J0. right. right. right. right. right. left.
      exists gv. exists mgv.  rewrite <- HeqR0. undefbehave.

  SCase "gep".
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv)
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [mp J].
    assert (exists vidxs, values2GVs (los, nts) l2 lc gl = Some vidxs)
      as J2.
      eapply values2GVs_isnt_stuck; eauto.
        exists nil. auto.
    destruct J2 as [vidxss J2].
    inv Hwfc. find_wf_value_list.
    match goal with
    | H12: wf_value_list _ |- _ =>
      assert (Hins:=H12);
      eapply values2GVs__inhabited in Hins; eauto;
      destruct Hins as [vidxs Hins]
    end.
    assert (exists mp', GEP (los, nts) t mp vidxs i1 typ' = Some mp') as J3.      unfold GEP, gep.
      apply GVsSig.(lift_op1__isnt_stuck); eauto using GEP_is_total.
    destruct J3 as [mp' J3].
    left.
    exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_gep i0 i1 t v l2 typ' :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 mp');
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists events.E0. eauto.

  SCase "trunc".
    left.
    assert (exists gv2, TRUNC (los,nts) lc gl t t0 v t1 = Some gv2)
      as Hinsn_trunc.
      unfold TRUNC.
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv)
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J. inv Hwfc.
      apply GVsSig.(lift_op1__isnt_stuck); eauto using mtrunc_is_total.

    destruct Hinsn_trunc as [gv2 Hinsn_trunc].
    exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_trunc i0 t t0 v t1 :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists events.E0. eauto.

  SCase "ext".
    left.
    assert (exists gv2, EXT (los,nts) lc gl e t v t0 = Some gv2)
      as Hinsn_ext.
      unfold EXT.
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv)
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J. inv Hwfc.
      apply GVsSig.(lift_op1__isnt_stuck); eauto using mext_is_total.

    destruct Hinsn_ext as [gv2 Hinsn_ext].
    exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_ext i0 e t v t0 :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists events.E0. eauto.

  SCase "cast".
    left.
    assert (exists gvs2, CAST (los,nts) lc gl c t v t0 = Some gvs2)
      as Hinsn_cast.
      unfold CAST.
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv)
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J. inv Hwfc.
      apply GVsSig.(lift_op1__isnt_stuck); eauto using mcast_is_total.

    destruct Hinsn_cast as [gv2 Hinsn_cast].
    exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_cast i0 c t v t0 :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists events.E0. eauto.

  SCase "icmp".
    left.
    assert (exists gv2, ICMP (los,nts) lc gl c t v v0 = Some gv2)
      as Hinsn_icmp.
      unfold ICMP.
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv)
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv)
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0. inv Hwfc.
      match goal with
      | H11: wf_value _ _ _ _ _ |- _ =>
        apply wf_value__wf_typ in H11; destruct H11
      end.
      apply GVsSig.(lift_op2__isnt_stuck); eauto using micmp_is_total.

    destruct Hinsn_icmp as [gv2 Hinsn_icmp].
    exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_icmp i0 c t v v0 :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists events.E0. eauto.

  SCase "fcmp".
    left.
    assert (exists gv2, FCMP (los,nts) lc gl f0 f1 v v0 = Some gv2)
      as Hinsn_fcmp.
      unfold FCMP.
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv)
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv)
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0. inv Hwfc.
      match goal with
      | H11: wf_value _ _ _ _ _ |- _ =>
        apply wf_value__wf_typ in H11; destruct H11
      end.
      apply GVsSig.(lift_op2__isnt_stuck); eauto using mfcmp_is_total.

    destruct Hinsn_fcmp as [gv2 Hinsn_fcmp].
    exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_fcmp i0 f0 f1 v v0 :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists events.E0. eauto.

  SCase "select".
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv)
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [cond J].
    assert (exists c, c @ cond) as Hinh.
      inv Hwfc.
      eapply getOperandValue__inhabited in J; eauto.
      gvs_inhabited_inv J. eauto.
    destruct Hinh as [c Hinh].
    assert (exists gv0, getOperandValue (los, nts) v0 lc gl = Some gv0)
      as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [gv0 J0].
    assert (exists gv1, getOperandValue (los, nts) v1 lc gl = Some gv1)
      as J1.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J1 as [gv1 J1].
    left.
    exists
         {|
         ECS := {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_select i0 v t v0 v1 :: cs) tmn);
                CurCmds := cs;
                Terminator := tmn;
                Locals := (if isGVZero (los, nts) c
                           then updateAddAL _ lc i0 gv1
                           else updateAddAL _ lc i0 gv0);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists events.E0. eauto.

  SCase "call".
    assert (exists gvs, params2GVs (los, nts) p lc gl = Some gvs) as G.
      eapply params2GVs_isnt_stuck; eauto.
        exists nil. auto.
    destruct G as [gvss G].
    assert (exists fptrs, getOperandValue (los, nts) v lc gl =
      Some fptrs) as J'.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J' as [fptrs J'].
    assert (exists fptr, fptr @ fptrs) as Hinh.
      inv Hwfc.
      eapply getOperandValue__inhabited in J'; eauto.
      gvs_inhabited_inv J'. eauto.
    destruct Hinh as [fptr Hinh].
    remember (lookupFdefViaPtr ps fs fptr) as Hlk.
    destruct Hlk as [f' |].
    SSCase "internal call".
    destruct f' as [[fa rt fid la va] lb].
    assert (J:=HeqHlk).
    symmetry in J.
    apply lookupFdefViaPtr_inversion in J; auto.
    destruct J as [fn [Hlkft J]].
    apply lookupFdefViaIDFromProducts_inv in J; auto.
    eapply wf_system__wf_fdef in J; eauto.
    assert (Hinit := J).
    apply initLocal__total with (gvs2:=gvss) in Hinit; auto.
    destruct Hinit as [lc2 Hinit].
    inv J. destruct block5 as [l5 [ps5 cs5 tmn5]].
    left.
    exists
         {|
         ECS :=(mkEC (fdef_intro (fheader_intro fa rt fid la va) lb)
                     (l5, stmts_intro ps5 cs5 tmn5) cs5 tmn5 lc2
                     nil)::
               {|
                CurFunction := f;
                CurBB := (l1, stmts_intro ps1
                           (cs1 ++ insn_call i0 n c rt1 va1 v p :: cs) tmn);
                CurCmds := insn_call i0 n c rt1 va1 v p :: cs;
                Terminator := tmn;
                Locals := lc;
                Allocas := als |} :: ecs;
         Mem := M |}.
    exists events.E0.
    eauto.

    remember (lookupExFdecViaPtr ps fs fptr) as Helk.
    destruct Helk as [f' |].
    SSCase "external call".
    assert (exists gvs, gvs @@ gvss) as G'. simpl in HwfECs.
      inv Hwfc. find_wf_value_list.
      eapply params2GVs_inhabited in G; eauto.
    destruct G' as [gvs G'].
    destruct f' as [[fa rt fid la va]].
    remember (external_intrinsics.callExternalOrIntrinsics
               (los, nts) gl M fid rt (args2Typs la) deckind5 gvs) as R.
    destruct R as [[[oresult tr] Mem']|].
      remember (exCallUpdateLocals (los, nts) rt1 n i0 oresult lc) as R'.
      destruct R' as [lc' |]; tinv J.
        left.
        exists
          {|
          ECS :={|
                 CurFunction := f;
                 CurBB := (l1, stmts_intro ps1
                            (cs1 ++ insn_call i0 n c rt1 va1 v p :: cs) tmn);
                 CurCmds := cs;
                 Terminator := tmn;
                 Locals := lc';
                 Allocas := als |} :: ecs;
          Mem := Mem' |}.
        exists tr.
        eauto.

        right.
        unfold undefined_state.
        right. right. right. right. right. right. right.
        rewrite J'. rewrite G. exists fptr. rewrite <- HeqHlk. rewrite <- HeqHelk.
        split; auto. exists gvs. rewrite <- HeqR0. rewrite <- HeqR'. undefbehave.

      right.
      unfold undefined_state.
      right. rewrite J'. rewrite G. right. right. right. right. right. right.
      exists fptr. rewrite <- HeqHlk. rewrite <- HeqHelk.
      split; auto. exists gvs.  rewrite <- HeqR0. undefbehave.

   SSCase "stuck".
     right.
     unfold undefined_state.
     right. rewrite J'. rewrite G. right. right. right. right. right. right.
     exists fptr. rewrite <- HeqHlk. rewrite <- HeqHelk. split; auto.
Qed.

End OpsemPP. End OpsemPP.

