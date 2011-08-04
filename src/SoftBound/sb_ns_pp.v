Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import ssa_static.
Require Import ssa_props.
Require Import ssa_analysis.
Require Import ssa_wf.
Require Import ssa_dynamic.
Require Import ndopsem.
Require Import ndopsem_pp.
Require Import sb_ds_def.
Require Import sb_ds_metadata.
Require Import sb_ds_pp.
Require Import sb_ns_def.
Require Import sbop_nsop.
Require Import Znumtheory.
Require Import sb_ns_metadata.

Export LLVMwf.
Export AtomSet.
Export LLVMgv.
Export SBnsop.

(*****************************************)
(* Definitions *)

Definition wf_rmap (f:fdef) (lc:GVsMap) (rm:SBopsem.rmetadata) : Prop :=
forall id1 gv1 t1,
  lookupAL _ lc id1 = Some gv1 ->
  lookupTypViaIDFromFdef f id1 = Some (typ_pointer t1) ->
  exists md, lookupAL _ rm id1 = Some md.

Definition wf_ExecutionContext TD M (ps:list product) (ec:ExecutionContext) 
  : Prop :=
let '(SBnsop.mkEC f b cs tmn lc rm als) := ec in
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
wf_rmap f lc rm /\
wf_rmetadata TD M rm /\
exists l1, exists ps, exists cs',
b = block_intro l1 ps (cs'++cs) tmn.

Definition wf_call (ec:SBnsop.ExecutionContext) (ecs:SBnsop.ECStack) 
  : Prop :=
let '(SBnsop.mkEC f _ _ _ _ _ _) := ec in
forall b, blockInFdefB b f ->
let '(block_intro _ _ _ tmn) := b in
match tmn with
| insn_return _ _ _ | insn_return_void _ =>
    match ecs with
    | nil => True
    | SBnsop.mkEC f' b' (insn_call _ _ _ _ _ _ ::_) tmn' lc' rm' als'::ecs' =>
        True
    | _ => False
    end
| _ => True
end.

Fixpoint wf_ECStack TD M (ps:list product) (ecs:SBnsop.ECStack) : Prop :=
match ecs with
| nil => False
| ec::ecs' => 
    wf_ExecutionContext TD M ps ec /\ wf_ECStack TD M ps ecs' /\ wf_call ec ecs'
end.

Definition wf_State (S:SBnsop.State) : Prop :=
let '(SBnsop.mkState s (los, nts) ps ecs gl _ M MM) := S in
wf_mmetadata (los, nts) M MM /\
wf_global (los, nts) s gl /\
wf_global_ptr s (los, nts) M gl /\
wf_system nil s /\
moduleInSystemB (module_intro los nts ps) s = true /\
wf_ECStack (los, nts) M ps ecs.

(*********************************************)
(** * wf_state *)

Lemma wf_State__cmd__lookupTypViaIDFromFdef : forall S,
  wf_State S ->
  match S with 
  | {| ECS := {|CurFunction := F; CurCmds := c :: cs |} :: EC |} =>
      forall id0, getCmdID c = Some id0 ->
      lookupTypViaIDFromFdef F id0 = getCmdTyp c
  | _ => True
  end.
Proof.
  intros S HwfS.
  destruct S.
  destruct CurTargetData0.
  destruct ECS0; auto.
  destruct e; auto.
  destruct CurCmds0; auto.
  destruct HwfS as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  intros id0 HgetID.
  eapply uniqF__lookupTypViaIDFromFdef'; eauto.
    eapply wf_system__uniqFdef; eauto.
    apply in_or_app; simpl; auto.
Qed.

Lemma wf_State__wf_cmd : forall St,
  wf_State St ->
  match St with 
  | {| CurSystem := sys;
       CurTargetData := (los, nts);
       CurProducts := Ps;
       ECS := {|CurFunction := F; CurBB := B; CurCmds := c :: cs |} :: EC 
     |} => wf_insn nil sys (module_intro los nts Ps) F B (insn_cmd c)
  | _ => True
  end.
Proof.
  intros S HwfS.
  destruct S.
  destruct CurTargetData0.
  destruct ECS0; auto.
  destruct e; auto.
  destruct CurCmds0; auto.
  destruct HwfS as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  eapply wf_system__wf_cmd with(c:=c) in HBinF1; 
    try solve [eauto | apply in_or_app; simpl; auto].
Qed.

Lemma free_allocas_preserves_wf_EC : forall EC TD M M' als Ps,
  free_allocas TD M als = Some M' ->
  wf_ExecutionContext TD M Ps EC ->
  wf_ExecutionContext TD M' Ps EC.
Proof.
  destruct EC; simpl; intros TD M M' als Ps Hfrees HwfEC.
  destruct HwfEC as [J1 [J2 [J3 [J4 [J5 [J6 [J7 J8]]]]]]].
  repeat (split; eauto using free_allocas_preserves_wf_rmetadata).
Qed.  

Lemma free_allocas_preserves_wf_ECStack : forall EC TD M M' als Ps,
  free_allocas TD M als = Some M' ->
  wf_ECStack TD M Ps EC ->
  wf_ECStack TD M' Ps EC.
Proof.
  induction EC; simpl; intros TD M M' als Ps Hfrees HwfECs; auto.
  destruct HwfECs as [J1 [J2 J3]].
  repeat (split; eauto using free_allocas_preserves_wf_EC).
Qed.

Lemma free_preserves_wf_EC : forall EC TD M M' gv Ps,
  free TD M gv = Some M' ->
  wf_ExecutionContext TD M Ps EC ->
  wf_ExecutionContext TD M' Ps EC.
Proof.
  destruct EC; simpl; intros TD M M' als Ps Hfrees HwfEC.
  destruct HwfEC as [J1 [J2 [J3 [J4 [J5 [J6 [J7 J8]]]]]]].
  repeat (split; eauto using free_preserves_wf_rmetadata).
Qed.  

Lemma free_preserves_wf_ECStack : forall ECs TD M M' gv Ps,
  free TD M gv = Some M' ->
  wf_ECStack TD M Ps ECs ->
  wf_ECStack TD M' Ps ECs.
Proof.
  induction ECs; simpl; intros TD M M' als Ps Hfrees HwfECs; auto.
  destruct HwfECs as [J1 [J2 J3]].
  repeat (split; eauto using free_preserves_wf_EC).
Qed.

Lemma malloc_preserves_wf_EC : forall EC TD M tsz gn align0 M' mb Ps,
  malloc TD M tsz gn align0 = ret (M', mb) ->
  wf_ExecutionContext TD M Ps EC ->
  wf_ExecutionContext TD M' Ps EC.
Proof.
  destruct EC; simpl; intros TD M tsz gn align0 M' mb Ps Hmalloc HwfEC.
  destruct HwfEC as [J1 [J2 [J3 [J4 [J5 [J6 [J7 J8]]]]]]].
  repeat (split; eauto using malloc_preserves_wf_rmetadata).
Qed.

Lemma malloc_preserves_wf_ECStack : forall ECs TD M tsz gn align0 M' mb Ps,
  malloc TD M tsz gn align0 = ret (M', mb) ->
  wf_ECStack TD M Ps ECs ->
  wf_ECStack TD M' Ps ECs.
Proof.
  induction ECs; simpl; intros TD M tsz gn align0 M' mb Ps Halloc HwfECs; auto.
  destruct HwfECs as [J1 [J2 J3]].
  repeat (split; eauto using malloc_preserves_wf_EC).
Qed.

Lemma store_preserves_wf_EC : forall EC TD M gvp t gv align M' Ps,
  mstore TD M gvp t gv align = Some M' ->
  wf_ExecutionContext TD M Ps EC ->
  wf_ExecutionContext TD M' Ps EC.
Proof.
  destruct EC; simpl; intros TD M gvp t gv align M' Ps Hstore HwfEC.
  destruct HwfEC as [J1 [J2 [J3 [J4 [J5 [J6 [J7 J8]]]]]]].
  repeat (split; eauto using store_preserves_wf_rmetadata).
Qed.

Lemma store_preserves_wf_ECStack : forall ECs TD M gvp t gv align M' Ps,
  mstore TD M gvp t gv align = Some M' ->
  wf_ECStack TD M Ps ECs ->
  wf_ECStack TD M' Ps ECs.
Proof.
  induction ECs; simpl; intros TD M gvp t gv align M' Ps Hstore HwfECs; auto.
  destruct HwfECs as [J1 [J2 J3]].
  repeat (split; eauto using store_preserves_wf_EC).
Qed.

Lemma callExternalFunction_preserves_wf_EC : forall EC M fid gvs oresult M' TD 
    Ps,
  callExternalFunction M fid gvs = Some (oresult, M') ->
  wf_ExecutionContext TD M Ps EC ->
  wf_ExecutionContext TD M' Ps EC.
Proof.
  destruct EC; simpl; intros M fid gvs oresult M' TD Ps Hcall HwfEC.
  destruct HwfEC as [J1 [J2 [J3 [J4 [J5 [J6 [J7 J8]]]]]]].
  repeat (split; eauto using callExternalFunction_preserves_wf_rmetadata).
Qed.

Lemma callExternalFunction_preserves_wf_ECStack : forall ECs Mem0 fid gvs oresult
    Mem' TD Ps,
  callExternalFunction Mem0 fid gvs = Some (oresult, Mem') ->
  wf_ECStack TD Mem0 Ps ECs ->
  wf_ECStack TD Mem' Ps ECs.
Proof.
  induction ECs; simpl; intros Mem0 fid gvs oresult Mem' TD Ps Hcall HwfECs; 
    auto.
  destruct HwfECs as [J1 [J2 J3]].
  repeat (split; eauto using callExternalFunction_preserves_wf_EC).
Qed.

(*********************************************)
(** * wf_rmap *)

Lemma returnUpdateLocals__wf_rmap : 
  forall los nts c' rt Result lc lc' rm rm' gl lc'' rm'' F' tmn' cs' Ps S
  (H1 : returnUpdateLocals (los, nts) c' rt Result lc lc' rm rm' gl =
       ret (lc'', rm''))
  (HwfSystem : wf_system nil S)
  (HmInS : moduleInSystemB (module_intro los nts Ps) S = true)
  (HFinPs2 : InProductsB (product_fdef F') Ps = true)
  (Hwfm2 : wf_rmap F' lc' rm')
  (l2 : l)
  (ps2 : phinodes)
  (cs2' : list cmd) 
  (HBinF2 : blockInFdefB (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') F' =
           true)
  (Hwfc : wf_insn nil S (module_intro los nts Ps) F'
           (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') 
           (insn_cmd c')),
  wf_rmap F' lc'' rm''.
Proof.
  intros.
  eapply wf_system__uniqFdef with (f:=F') in HwfSystem; eauto.
  unfold returnUpdateLocals, returnResult in H1.
  remember (NDopsem.getOperandValue (los, nts) Result lc gl) as R1.
  destruct R1; inv H1.
  destruct (isPointerTypB rt).
    remember (get_reg_metadata (los, nts) gl rm Result) as R3.
    destruct R3 as [[md ?]|]; inv H0.
    destruct c'; inv H1; auto.
    destruct n; inv H0; auto.
    destruct t; tinv H1.
    inv Hwfc. inv H6. inv H15.
    clear H19 H17 H8 H18 H16 H20 H7.
    assert (lookupTypViaIDFromFdef F' i0 = Some typ1) as J.
      eapply uniqF__lookupTypViaIDFromFdef with 
        (c:=insn_call i0 false c
                 (typ_function typ1
                    (make_list_typ
                       (map_list_typ_value
                          (fun (typ_' : typ) (_ : value) => typ_')
                          typ'_value''_list)) varg5) v
                 (map_list_typ_value
                    (fun (typ_' : typ) (value_'' : value) =>
                     (typ_', value_'')) typ'_value''_list))(i0:=i0)(t0:=typ1)
        in HBinF2; eauto.
        apply in_or_app. right. simpl. auto.
    clear HBinF2.
    simpl in H1.
    remember (isPointerTypB typ1) as R.
    destruct R; inv H1.
      intros x gvx tx Hin Htyp.
      destruct (eq_atom_dec x i0); subst.        
        rewrite J in Htyp. inv Htyp.
        rewrite lookupAL_updateAddAL_eq. eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hin; auto.
        rewrite <- lookupAL_updateAddAL_neq; eauto.

      intros x gvx tx Hin Htyp.
      destruct (eq_atom_dec x i0); subst.        
        rewrite J in Htyp. inv Htyp. inv HeqR.

        rewrite <- lookupAL_updateAddAL_neq in Hin; eauto.

    destruct c'; try solve [inv H0; auto].
    destruct n; inv H0; auto.
    destruct t; tinv H1.
    inv Hwfc. inv H6. inv H15.
    clear H19 H17 H8 H18 H16 H20 H7.
    assert (lookupTypViaIDFromFdef F' i0 = Some typ1) as J.
      eapply uniqF__lookupTypViaIDFromFdef with 
        (c:=insn_call i0 false c
                 (typ_function typ1
                    (make_list_typ
                       (map_list_typ_value
                          (fun (typ_' : typ) (_ : value) => typ_')
                          typ'_value''_list)) varg5) v
                 (map_list_typ_value
                    (fun (typ_' : typ) (value_'' : value) =>
                     (typ_', value_'')) typ'_value''_list))(i0:=i0)(t0:=typ1)
        in HBinF2; eauto.
        apply in_or_app. right. simpl. auto.
    clear HBinF2.
    simpl in H1.
    remember (isPointerTypB typ1) as R.
    destruct R; inv H1.
      intros x gvx tx Hin Htyp.
      destruct (eq_atom_dec x i0); subst.        
        rewrite J in Htyp. inv Htyp.
        rewrite lookupAL_updateAddAL_eq. eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hin; auto.
        rewrite <- lookupAL_updateAddAL_neq; eauto.

      intros x gvx tx Hin Htyp.
      destruct (eq_atom_dec x i0); subst.        
        rewrite J in Htyp. inv Htyp. inv HeqR.

        rewrite <- lookupAL_updateAddAL_neq in Hin; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes__wf_rmap : forall PNs TD b gl lc rm
   re id1 gv1 opmd1 t1,
  NoDup (getPhiNodesIDs PNs) ->
  getIncomingValuesForBlockFromPHINodes TD PNs b gl lc rm = Some re ->
  In (id1,gv1,opmd1) re ->
  lookupTypViaIDFromPhiNodes PNs id1 = Some (typ_pointer t1) ->
  opmd1 <> None.
Proof.
  induction PNs; simpl; intros TD b gl lc rm re id1 gv1 opmd1 t1 Huniq Hget Hin
    Hlk.
    inv Hget. inversion Hin.

    inv Huniq.
    destruct a.
    destruct (getValueViaBlockFromValuels l0 b); try solve [inv Hget].
    destruct (NDopsem.getOperandValue TD v lc gl); try solve [inv Hget].    
    remember (getIncomingValuesForBlockFromPHINodes TD PNs b gl lc rm) as R.
    destruct R; try solve [inv Hget].
    unfold lookupTypViaIDFromPhiNode in Hlk. simpl in Hlk.
    destruct (id1==i0); subst.
      inv Hlk.
      simpl in Hget.
      remember (get_reg_metadata TD gl rm v) as R.
      destruct R as [md|]; inv Hget.
      simpl in Hin.
      destruct Hin as [Hin | Hin]; try (inv Hin; congruence).
        simpl in H1.         
        eapply getIncomingValuesForBlockFromPHINodes_spec in HeqR; eauto.

      destruct (isPointerTypB t); inv Hget.
        destruct (get_reg_metadata TD gl rm v) as [md|]; inv H0.
        simpl in Hin.
        destruct Hin as [Hin | Hin].
          inv Hin. congruence.
          eauto.
        simpl in Hin.
        destruct Hin as [Hin | Hin].
          inv Hin. congruence.
          eauto.
Qed.

Lemma updateValuesForNewBlock__wf_rmap_aux : forall rvs F rm lc,
  (forall id1 gv1 opmd1 t1, 
    In (id1,gv1,opmd1) rvs ->
    lookupTypViaIDFromFdef F id1 = Some (typ_pointer t1) ->
    opmd1 <> None) ->
  forall rvs2 rvs1 lc1 rm1 lc2 rm2,
  rvs = rvs1 ++ rvs2 ->
  updateValuesForNewBlock rvs1 lc rm = (lc1, rm1) ->
  wf_rmap F lc1 rm1 ->
  updateValuesForNewBlock rvs2 lc1 rm1 = (lc2, rm2) ->
  wf_rmap F lc2 rm2.
Proof.
  intros rvs F rm lc Hprop.
  induction rvs2; simpl; intros rvs1 lc1 rm1 lc2 rm2 Heq Hupdate1 Hrmap1
    Hupdate2; subst.
    inv Hupdate2. auto.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs2 lc1 rm1) as R. 
    destruct R as [lc2' rm2'].
    destruct o as [[md ?]|]; inv Hupdate2.
      intros x gvx tx Hlk Htyp.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq. eauto.

        rewrite <- lookupAL_updateAddAL_neq; auto.
        rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
        remember (lookupAL _ lc1 x) as R.
        destruct R as [gv|].
          symmetry in HeqR0.
          assert (exists md0, lookupAL metadata rm1 x = ret md0) as J.
            eapply Hrmap1; eauto.
          destruct J as [md0 J].
          eapply updateValuesForNewBlock_spec5 in J; eauto.

          symmetry in HeqR0.
          eapply updateValuesForNewBlock_spec1 in HeqR0; eauto.
          destruct HeqR0 as [omd HeqR0].
          apply Hprop with (gv1:=gvx)(opmd1:=omd) in Htyp; eauto.
            destruct omd as [md1|]; try solve [contradict Htyp; auto].
            eapply updateValuesForNewBlock_spec3 in HeqR; eauto.

            apply in_or_app. simpl. auto.

      intros x gvx tx Hlk Htyp.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk. inv Hlk.
        apply Hprop with (gv1:=gvx)(opmd1:=merror) in Htyp; auto.
          contradict Htyp; auto.
          apply in_or_app. simpl. auto.
         
        rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
        remember (lookupAL _ lc1 x) as R.
        destruct R as [gv|].
          symmetry in HeqR0.
          assert (exists md0, lookupAL metadata rm1 x = ret md0) as J.
            eapply Hrmap1; eauto.
          destruct J as [md0 J].
          eapply updateValuesForNewBlock_spec5 in J; eauto.

          symmetry in HeqR0.
          eapply updateValuesForNewBlock_spec1 in HeqR0; eauto.
          destruct HeqR0 as [omd HeqR0].
          eapply Hprop with (gv1:=gvx)(opmd1:=omd) in Htyp; eauto.
            destruct omd as [md1|]; try solve [contradict Htyp; auto].
            eapply updateValuesForNewBlock_spec3 in HeqR; eauto.

            apply in_or_app. simpl. auto.
Qed.

Lemma updateValuesForNewBlock__wf_rmap : forall rvs F lc rm lc' rm',
  wf_rmap F lc rm ->
  (forall id1 gv1 opmd1 t1, 
    In (id1,gv1,opmd1) rvs ->
    lookupTypViaIDFromFdef F id1 = Some (typ_pointer t1) ->
    opmd1 <> None) ->
  updateValuesForNewBlock rvs lc rm = (lc', rm') ->
  wf_rmap F lc' rm'.
Proof.
  intros.
  eapply updateValuesForNewBlock__wf_rmap_aux with (rvs1:=nil)(lc1:=lc)(rm1:=rm)
    (rvs2:=rvs); simpl; eauto.
Qed.

Lemma switchToNewBasicBlock__wf_rmap : forall F TD b1 b2 gl lc rm lc' rm',
  uniqFdef F ->
  blockInFdefB b1 F ->
  wf_rmap F lc rm ->
  switchToNewBasicBlock TD b1 b2 gl lc rm = Some (lc', rm') ->
  wf_rmap F lc' rm'.
Proof.
  intros F TD b1 b2 gl lc rm lc' rm' Huniq HBinF Hwfm Hswitch.
  unfold switchToNewBasicBlock in Hswitch.
  remember (getIncomingValuesForBlockFromPHINodes TD
             (getPHINodesFromBlock b1) b2 gl lc rm) as R.
  destruct R; inv Hswitch.
  eapply updateValuesForNewBlock__wf_rmap; eauto.
  intros.
  eapply getIncomingValuesForBlockFromPHINodes__wf_rmap with (t1:=t1); eauto.
    apply uniqFdef__uniqBlockLocs in HBinF; auto.
    destruct b1. simpl in HBinF. simpl.
    apply NoDup_inv in HBinF. destruct HBinF; auto.

    eapply lookupTypViaIDFromFdef__lookupTypViaIDFromPhiNodes; eauto.
      eapply getIncomingValuesForBlockFromPHINodes_spec; eauto.
Qed.

Lemma updateAddAL_nptr__wf_rmap : forall F lc rm id0 gv3,
  wf_rmap F lc rm -> 
  (forall t0, lookupTypViaIDFromFdef F id0 <> Some (typ_pointer t0)) ->
  wf_rmap F (updateAddAL _ lc id0 gv3) rm.
Proof.
  intros.
  intros x gv t J1 J2.
  destruct (eq_atom_dec id0 x); subst.
    contradict J2; auto.

    rewrite <- lookupAL_updateAddAL_neq in J1; eauto.
Qed.

Lemma updateAddAL_ptr__wf_rmap: forall F lc rm id0 gv3 md,
  wf_rmap F lc rm -> 
  wf_rmap F (updateAddAL _ lc id0 gv3) (updateAddAL _ rm id0 md).
Proof.
  intros.
  intros x gv t J1 J2.
  destruct (eq_atom_dec id0 x); subst.
    rewrite lookupAL_updateAddAL_eq in J1.
    rewrite lookupAL_updateAddAL_eq.
    inv J1. eauto.

    rewrite <- lookupAL_updateAddAL_neq in J1; auto.
    rewrite <- lookupAL_updateAddAL_neq; eauto. 
Qed.

Lemma initializeFrameValues__wf_rmap : forall TD fa rt fid va lb lc1 rm1 la2 la1 
    ogvs2 lc' rm',
  uniqFdef (fdef_intro (fheader_intro fa rt fid (la1++la2) va) lb) ->
  wf_rmap (fdef_intro (fheader_intro fa rt fid (la1++la2) va) lb) lc1 rm1 ->
  _initializeFrameValues TD la2 ogvs2 lc1 rm1 = Some (lc', rm') ->
  wf_rmap (fdef_intro (fheader_intro fa rt fid (la1++la2) va) lb) lc' rm'.
Proof.
  induction la2; intros la1 ogvs2 llc' rm' HuniqF Hwfm Hinit2.
    inv Hinit2. auto.

    simpl in Hinit2.
    destruct a. destruct p.
    assert (lookupTypViaIDFromArgs (la1 ++ (t, a, i0) :: la2) i0 = Some t) 
      as Hlk'.
      clear - HuniqF. simpl in HuniqF. destruct HuniqF as [_ HuniqF].
      apply NoDup_inv in HuniqF.
      destruct HuniqF as [J1 J2].
      apply NoDup_lookupTypViaIDFromArgs; auto.

    destruct ogvs2 as [|[gv opmd] ogvs2'].
      remember (_initializeFrameValues TD la2 nil lc1 rm1) as R.      
      destruct R as [[lc2 rm2]|]; tinv Hinit2.
      destruct (gundef TD t); tinv Hinit2. 
      remember (isPointerTypB t) as R1.
      destruct R1; inv Hinit2; simpl.
        apply updateAddAL_ptr__wf_rmap; auto.
          rewrite_env ((la1 ++ [(t,a,i0)]) ++ la2). 
          eapply IHla2; simpl_env; simpl; eauto.
        
        intros x gvx tx Hlk Htyp.
        destruct (eq_atom_dec x i0); subst.
          simpl in Htyp.
          rewrite Hlk' in Htyp.
          inv Htyp.
          inv HeqR1.

          rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
          rewrite_env ((la1 ++ [(t,a,i0)]) ++ la2) in Hwfm.
          rewrite_env ((la1 ++ [(t,a,i0)]) ++ la2) in HuniqF.
          rewrite_env ((la1 ++ [(t,a,i0)]) ++ la2) in Htyp.
          eapply IHla2 with (la1:=la1 ++ [(t,a,i0)]); eauto.

      remember (_initializeFrameValues TD la2 ogvs2' lc1 rm1) as R.      
      destruct R as [[lc2 rm2]|]; tinv Hinit2.
      remember (isPointerTypB t) as R1.
      destruct R1; inv Hinit2; simpl.
        destruct opmd as [[md ?]|]; inv H0.
          apply updateAddAL_ptr__wf_rmap; auto.
            rewrite_env ((la1 ++ [(t,a,i0)]) ++ la2). 
            eapply IHla2; simpl_env; simpl; eauto.
          apply updateAddAL_ptr__wf_rmap; auto.
            rewrite_env ((la1 ++ [(t,a,i0)]) ++ la2). 
            eapply IHla2; simpl_env; simpl; eauto.

        rewrite_env ((la1 ++ [(t,a,i0)]) ++ la2) in Hwfm.
        rewrite_env ((la1 ++ [(t,a,i0)]) ++ la2) in HuniqF.
        eapply IHla2 with (ogvs2:=ogvs2') in Hwfm; eauto.
          rewrite_env (la1 ++ [(t,a,i0)] ++ la2) in Hwfm.
          apply updateAddAL_nptr__wf_rmap; auto.
            simpl. intros t0 Hlk.
            rewrite Hlk' in Hlk.
            inv Hlk. inversion HeqR1.
Qed.

Lemma initLocals__wf_rmap : forall TD ogvs lc' rm' fa rt fid la va lb,
  uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  initLocals TD la ogvs = Some (lc', rm') ->
  wf_rmap (fdef_intro (fheader_intro fa rt fid la va) lb) lc' rm'.
Proof.
  unfold initLocals.
  intros TD ogvs lc' rm' fa rt fid la va lb Huniq Hinit.
  rewrite_env (nil ++ la).
  eapply initializeFrameValues__wf_rmap; eauto.
    intros x gvx tx Hlk. inv Hlk.
Qed.

(*********************************************)
(** * Preservation *)

(* extract/insert values are not supported. *)
Axiom extractValue_preserves_wf_rmap : forall los nts Mem0 v lc gl 
  t gv idxs gv' rm fs EC B S Ps F MM id0 als tmn cs
  (H : NDopsem.getOperandValue (los, nts) v lc gl = ret gv)
  (H0 : NDopsem.extractGenericValue (los, nts) t gv idxs = ret gv')
  (HwfS1 : wf_State
            {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            ECS := {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := insn_extractvalue id0 t v idxs :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Rmap := rm;
                   Allocas := als |} :: EC;
            Globals := gl;
            FunTable := fs;
            Mem := Mem0;
            Mmap := MM |}),
   wf_rmap F lc rm -> 
   wf_rmap F (updateAddAL _ lc id0 gv') rm.

Axiom insertValue_preserves_wf_rmap : forall los nts Mem0 v lc gl 
  t gv idxs gv' rm fs EC B S Ps F MM id0 als tmn cs t' v' gv''
  (H : NDopsem.getOperandValue (los, nts) v lc gl = ret gv)
  (H0 : NDopsem.getOperandValue (los, nts) v' lc gl = ret gv')
  (H1 : NDopsem.insertGenericValue (los, nts) t gv idxs t' gv' = ret gv'')
  (HwfS1 : wf_State
            {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            ECS := {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := insn_insertvalue id0 t v t' v' idxs :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Rmap := rm;
                   Allocas := als |} :: EC;
            Globals := gl;
            FunTable := fs;
            Mem := Mem0;
            Mmap := MM |}),
   wf_rmap F lc rm -> 
   wf_rmap F (updateAddAL _ lc id0 gv'') rm.

Lemma wf_State__inv : forall S los nts Ps F B c cs tmn lc rm als EC gl fs Mem0 
    MM0,
  wf_State (SBnsop.mkState S (los,nts) Ps
              ((SBnsop.mkEC F B (c::cs) tmn lc rm als)::EC) gl fs Mem0 MM0) ->
  wf_global (los, nts) S gl /\
  wf_lc (los,nts) F lc /\ 
  wf_insn nil S (module_intro los nts Ps) F B (insn_cmd c).
Proof.
  intros.
  destruct H as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  split; auto. 
  split; auto. 
    eapply wf_system__wf_cmd; eauto using in_middle.
Qed.  
(*
Ltac preservation_tac HwfS1 :=
  eapply preservation_cmd_updated_case in HwfS1; simpl; try solve [
      eauto | 
      intro J;
      apply updateAddAL_nptr__wf_rmap; try solve [auto |
        apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1;
        rewrite HwfS1; simpl; try solve [auto | congruence]]
    ].
*)

Lemma wf_sbExecutionContext__wf_ExecutionContext : forall TD M ps sbEC, 
  wf_ExecutionContext TD M ps sbEC -> 
  ndopsem_pp.wf_ExecutionContext TD ps (SBnsop.sbEC__EC sbEC).
Proof.
  intros.
  destruct sbEC.
  destruct H as [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
    [l3 [ps3 [cs3' Heq1]]]]]]]]]].
  repeat (split; eauto). 
Qed.  

Lemma wf_sbcall__wf_call : forall sbEC sbECs,
  wf_call sbEC sbECs -> 
  ndopsem_pp.wf_call (SBnsop.sbEC__EC sbEC) (SBnsop.sbECs__ECs sbECs).
Proof.
  intros.
  destruct sbEC.  
  simpl in *. 
  intros.
  apply H in H0. clear H.
  destruct b; auto.
  destruct t; auto.
    destruct sbECs; auto.
    destruct e; auto.

    destruct sbECs; auto.
    destruct e; auto.
Qed.

Lemma wf_sbECs__wf_ECs : forall TD M ps sbECs, 
  wf_ECStack TD M ps sbECs -> 
  ndopsem_pp.wf_ECStack TD ps (SBnsop.sbECs__ECs sbECs).
Proof.
  induction sbECs; simpl; intros; auto.
    destruct H as [J1 [J2 J3]].
    repeat (split; eauto using wf_sbExecutionContext__wf_ExecutionContext,
                               wf_sbcall__wf_call).
Qed.  

Lemma wf_sbState__wf_State : forall sbSt, 
  wf_State sbSt -> ndopsem_pp.wf_State (SBnsop.sbState__State sbSt).
Proof.
  intros.
  destruct sbSt. destruct CurTargetData0.
  destruct H as [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS HwfEC]]]]].
  repeat (split; eauto using wf_sbECs__wf_ECs). 
Qed.

Ltac preservation_simpl :=
  match goal with
  | [HwfS1 : wf_State
           {|
           CurSystem := _;
           CurTargetData := _;
           CurProducts := _;
           ECS := {| CurFunction := _;
                     CurBB := _;
                     CurCmds := _;
                     Terminator := _;
                     Locals := _;
                     Rmap := _;
                     Allocas := _ 
                   |} :: _;
           Globals := _;
           FunTable := _;
           Mem := _;
           Mmap := _ |} ,
      HwfLLVM2 : ndopsem_pp.wf_State
               (sbState__State
                  {|
                  CurSystem := _;
                  CurTargetData := _;
                  CurProducts := _;
                  ECS := {|
                         CurFunction := _;
                         CurBB := _;
                         CurCmds := _;
                         Terminator := _;
                         Locals := _;
                         Rmap := ?rm;
                         Allocas := _ |} :: _;
                  Globals := _;
                  FunTable := _;
                  Mem := _;
                  Mmap := _ |})
     |- _ ] => 
    assert (J:=HwfS1);
    destruct J as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
       [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm' 
         [l3 [ps3 [cs3' Heq1]]]]]]]]]]
       [HwfEC HwfCall]]]]
      ]]]; subst;
    destruct HwfLLVM2 as 
      [Hwfg0 [HwfSystem0 [HmInS0 [
       [Hreach0 [HBinF0 [HFinPs0 [Hwflc0 [Hinscope0 [l0' [ps0 [cs0 Heq0]]]]]]]]
       [HwfECs0 HwfCall0]
      ]]]]; subst
  end.

Ltac preservation_tac :=
  match goal with
  | [HwfS1 : wf_State
           {|
           CurSystem := ?S;
           CurTargetData := (?los, ?nts);
           CurProducts := ?Ps;
           ECS := {| CurFunction := ?F;
                     CurBB := ?B;
                     CurCmds := _ :: ?cs;
                     Terminator := ?tmn;
                     Locals := ?lc;
                     Rmap := ?rm;
                     Allocas := ?als 
                   |} :: ?EC;
           Globals := ?gl;
           FunTable := ?fs;
           Mem := ?Mem0;
           Mmap := ?MM |} ,
      HwfLLVM2 : ndopsem_pp.wf_State
               (sbState__State
                  {|
                  CurSystem := ?S;
                  CurTargetData := (?los, ?nts);
                  CurProducts := ?Ps;
                  ECS := {|
                         CurFunction := ?F;
                         CurBB := ?B;
                         CurCmds := ?cs;
                         Terminator := ?tmn;
                         Locals := updateAddAL _ ?lc _ _;
                         Rmap := ?rm;
                         Allocas := ?als |} :: ?EC;
                  Globals := ?gl;
                  FunTable := ?fs;
                  Mem := ?Mem0;
                  Mmap := ?MM |})
     |- wf_State
           {|
           CurSystem := ?S;
           CurTargetData := (?los, ?nts);
           CurProducts := ?Ps;
           ECS := {| CurFunction := ?F;
                     CurBB := ?B;
                     CurCmds := ?cs;
                     Terminator := ?tmn;
                     Locals := updateAddAL _ ?lc _ _;
                     Rmap := ?rm;
                     Allocas := ?als 
                   |} :: ?EC;
           Globals := ?gl;
           FunTable := ?fs;
           Mem := ?Mem0;
           Mmap := ?MM |} ] => 
    preservation_simpl;
    repeat (split; auto); try solve [
      apply updateAddAL_nptr__wf_rmap; try solve [auto |
          apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1;
          rewrite HwfS1; simpl; try solve [auto | congruence]] |
      eauto]
  end.

Ltac ctx_simpl' :=
  match goal with
  | [H1 : NDopsem.getOperandValue (?los, ?nts) ?vp ?lc ?gl = _,
     H2 : NDopsem.getOperandValue (?los, ?nts) ?vp ?lc ?gl = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H1 : getOperandValue (?los, ?nts) ?vp ?lc ?gl = _,
     H2 : getOperandValue (?los, ?nts) ?vp ?lc ?gl = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H1 : getTypeAllocSize (?los, ?nts) ?t = _,
     H2 : getTypeAllocSize (?los, ?nts) ?t = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H1 : malloc (?los, ?nts) ?Mem0 ?tsz0 ?gn ?align0 = _,
     H2 : malloc (?los, ?nts) ?Mem0 ?tsz0 ?gn ?align0 = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H1 : lookupExFdecViaGV (?los, ?nts) ?Ps ?gl ?lc ?fs ?fv = _,
     H2 : lookupExFdecViaGV (?los, ?nts) ?Ps ?gl ?lc ?fs ?fv = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H1 : LLVMgv.params2GVs (?los, ?nts) ?lp ?lc ?gl = _,
     H2 : LLVMgv.params2GVs (?los, ?nts) ?lp ?lc ?gl = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H1 : callExternalFunction ?Mem0 ?fid ?gvs = _,
     H2 : callExternalFunction ?Mem0 ?fid ?gvs = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H : updateAddAL _ ?lc ?id0 _ = updateAddAL _ ?lc ?id0 _ |- _ ] =>
    rewrite H in *
  end.

Lemma preservation : forall S1 S2 tr,
  SBnsop.nsInsn S1 S2 tr -> wf_State S1 -> wf_State S2.
Proof.
Opaque wf_mmetadata wf_rmetadata.

  intros S1 S2 tr HnsInsn HwfS1.
  inv HnsInsn.
  rename H into HnsInsn_delta.
  rename H0 into HnsInsn_llvm.
  assert (HwfLLVM2 := HnsInsn_llvm).
  apply ndopsem_pp.preservation in HwfLLVM2; auto using wf_sbState__wf_State.
  (sb_nsInsn_cases (induction HnsInsn_delta) Case); destruct TD as [los nts];
    subst; simpl in HnsInsn_llvm; inv HnsInsn_llvm; try invert_prop_reg_metadata.

Focus.
Case "nsReturn".
  destruct HwfS1 as 
    [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
       [l1 [ps1 [cs1' Heq1]]]]]]]]]]
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [Hwfm2 [Hwfm2' 
           [l2 [ps2 [cs2' Heq2]]]]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]]]]; subst.

  destruct HwfLLVM2 as 
    [Hwfg0 [HwfSystem0 [HmInS0 [
     [Hreach0 [HBinF0 [HFinPs0 [Hwflc0 [Hinscope0 [l0 [ps0 [cs0 Heq0]]]]]]]]
     [HwfECs0 HwfCall0]
    ]]]]; subst.
  assert (Hwfc := HBinF2).
  eapply wf_system__wf_cmd with (c:=c') in Hwfc; eauto using in_middle.
  repeat (split; auto).
    eapply free_allocas_preserves_wf_mmetadata; eauto.
    eapply free_allocas_preserves_wf_global_ptr; eauto.
    eapply returnUpdateLocals__wf_rmap; eauto.

    assert (Hwfc' := HBinF1).
    eapply wf_system__wf_tmn in Hwfc'; eauto.
    inv Hwfc'.
    eapply returnUpdateLocals__wf_rmetadata; eauto.

    exists l2. exists ps2. exists (cs2'++[c']). simpl_env. auto.

    eapply free_allocas_preserves_wf_ECStack; eauto.
Unfocus.

Focus.
Case "nsReturnVoid".
  destruct HwfS1 as 
    [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
       [l1 [ps1 [cs1' Heq1]]]]]]]]]]
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [Hwfm2 [Hwfm2' 
           [l2 [ps2 [cs2' Heq2]]]]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]]]]; subst.

  destruct HwfLLVM2 as 
    [Hwfg0 [HwfSystem0 [HmInS0 [
     [Hreach0 [HBinF0 [HFinPs0 [Hwflc0 [Hinscope0 [l0 [ps0 [cs0 Heq0]]]]]]]]
     [HwfECs0 HwfCall0]
    ]]]]; subst.
  assert (Hwfc := HBinF2).
  eapply wf_system__wf_cmd with (c:=c') in Hwfc; eauto using in_middle.
  repeat (split; auto).
    eapply free_allocas_preserves_wf_mmetadata; eauto.
    eapply free_allocas_preserves_wf_global_ptr; eauto.
    eapply free_allocas_preserves_wf_rmetadata; eauto.
    exists l2. exists ps2. exists (cs2'++[c']). simpl_env. auto.
    eapply free_allocas_preserves_wf_ECStack; eauto.
Unfocus.

Focus.
Case "nsBranch".
  preservation_simpl.
  assert (uniqFdef F) as HuniqF.
    eapply wf_system__uniqFdef in HwfSystem; eauto.   
  assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
  repeat (split; auto).
    eapply switchToNewBasicBlock__wf_rmap with 
      (b1:=block_intro l' ps' cs' tmn')
      (b2:=block_intro l3 ps3 (cs3' ++ nil) (insn_br bid Cond l1 l2)); eauto.
    eapply switchToNewBasicBlock__wf_rmetadata in H; eauto.
    exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Focus.
Case "nsBranch_uncond".
  preservation_simpl.
  assert (uniqFdef F) as HuniqF.
    eapply wf_system__uniqFdef in HwfSystem; eauto.   
  assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
  repeat (split; auto).
    eapply switchToNewBasicBlock__wf_rmap in H; eauto.
    eapply switchToNewBasicBlock__wf_rmetadata in H; eauto.
    exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Case "nsBop". preservation_tac.
Case "nsFBop". preservation_tac.
Case "nsExtractValue". 
  preservation_tac.
  eapply extractValue_preserves_wf_rmap; eauto.
Case "nsInsertValue". 
  preservation_tac.
  eapply insertValue_preserves_wf_rmap with (gv:=gvs); eauto.
Case "nsMalloc". 
  repeat ctx_simpl'.
  preservation_simpl.
  repeat (split; auto). 
    eapply malloc_extends_wf_mmetadata; eauto.
    eapply malloc_preserves_wf_global_ptr; eauto.
    apply updateAddAL_ptr__wf_rmap; auto. 
    eapply malloc_extends_wf_rmetadata; eauto.
    eauto.
    eapply malloc_preserves_wf_ECStack; eauto.

Case "nsFree". 
  preservation_simpl.
  repeat (split; auto). 
    eapply free_preserves_wf_mmetadata; eauto.
    eapply free_preserves_wf_global_ptr; eauto.
    eapply free_preserves_wf_rmetadata; eauto.
    eauto.
    eapply free_preserves_wf_ECStack; eauto.

Case "nsAlloca".
  repeat ctx_simpl'.
  preservation_simpl.
  repeat (split; auto). 
    eapply malloc_extends_wf_mmetadata; eauto.
    eapply malloc_preserves_wf_global_ptr; eauto.
    apply updateAddAL_ptr__wf_rmap; auto. 
    eapply malloc_extends_wf_rmetadata; eauto.
    eauto.
    eapply malloc_preserves_wf_ECStack; eauto.

Case "nsLoad_nptr". 
  repeat ctx_simpl'.
  preservation_simpl.
  repeat (split; auto). 
    apply updateAddAL_nptr__wf_rmap; auto.
      apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1.
      rewrite HwfS1; simpl; auto. 
        intros t0 EQ. inv EQ. inv H4.
    eauto.

Case "nsLoad_ptr".
  repeat ctx_simpl'.
  preservation_simpl.
  repeat (split; auto). 
    apply updateAddAL_ptr__wf_rmap; auto. 
    apply get_mem_metadata__wf_rmetadata; auto.
    eauto.

Case "nsStore_nptr". 
  repeat ctx_simpl'.
  preservation_simpl.
  repeat (split; auto). 
    eapply store_nptr_preserves_wf_mmetadata; eauto.
    eapply store_preserves_wf_global_ptr; eauto.
    eapply store_preserves_wf_rmetadata; eauto.
    eauto.
    eapply store_preserves_wf_ECStack; eauto.

Case "nsStore_ptr". 
  repeat ctx_simpl'.
  preservation_simpl.
  repeat (split; auto). 
    eapply store_ptr_preserves_wf_mmetadata; eauto.
      eapply wf_system__wf_cmd with (c:=insn_store sid t v vp align0) in HBinF1; 
        eauto.
        inv HBinF1; eauto.
        apply in_or_app; simpl; auto.
    eapply store_preserves_wf_global_ptr; eauto.
    eapply store_preserves_wf_rmetadata; eauto.
    eauto.
    eapply store_preserves_wf_ECStack; eauto.

Case "nsGEP". 
  preservation_simpl.
  repeat (split; auto). 
    apply updateAddAL_ptr__wf_rmap; auto.

    assert (Hwfc:=HwfS1). apply wf_State__wf_cmd in Hwfc.
    inv Hwfc.
    eapply prop_metadata_preserves_wf_rmetadata; eauto.

    eauto.

Case "nsTrunc". 
  preservation_tac.
  apply updateAddAL_nptr__wf_rmap; auto.
    assert (Htyp:=HwfS1).
    apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
    rewrite Htyp; simpl; auto. 
      apply wf_State__wf_cmd in HwfS1.
      inv HwfS1. inv H5; congruence.

Case "nsExt". 
  preservation_tac.
  apply updateAddAL_nptr__wf_rmap; auto.
    assert (Htyp:=HwfS1).
    apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
    rewrite Htyp; simpl; auto. 
      apply wf_State__wf_cmd in HwfS1.
      inv HwfS1. inv H5; congruence.

Case "nsBitcast_nptr". 
  preservation_tac.
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. inv H6; try congruence.
          inv H.

Case "nsBitcast_ptr". 
  preservation_simpl.
  repeat (split; auto). 
    apply updateAddAL_ptr__wf_rmap; auto.

    assert (Hwfc:=HwfS1). apply wf_State__wf_cmd in Hwfc.
    inv Hwfc.
    eapply prop_metadata_preserves_wf_rmetadata with (t:=t1); eauto.
      inv H7; eauto.

    eauto.

Case "nsInttoptr". 
  preservation_simpl.
  repeat (split; auto). 
    apply updateAddAL_ptr__wf_rmap; auto.
    apply adding_null_preserves_wf_rmetadata; auto.
    eauto.

Case "nsOthercast". 
  preservation_tac.
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. 
        destruct H as [J1 J2]. 
        inv H6; try (congruence).

Case "nsIcmp". preservation_tac.
Case "nsFcmp". preservation_tac.
Case "nsSelect_nptr".
  preservation_simpl.
  repeat (split; auto). 
    destruct (isGVZero (los, nts) c); 
    apply updateAddAL_nptr__wf_rmap; try solve [
        auto |
        apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1;
          rewrite HwfS1; simpl; try solve [auto | intros t0 EQ; inv EQ; inv H]
      ].
    eauto.

Case "nsSelect_ptr".
  repeat ctx_simpl'.
  preservation_simpl.
  assert (Hwfc:=HwfS1). apply wf_State__wf_cmd in Hwfc.
  inv Hwfc.
  rewrite <- H25 in *.
  repeat (split; auto). 
    rewrite H25.
    destruct (isGVZero (los, nts) c); 
      try solve [apply updateAddAL_ptr__wf_rmap; auto].
    destruct (isGVZero (los, nts) c);
      try solve [eapply prop_metadata_preserves_wf_rmetadata; eauto].
    eauto.

Focus.
Case "nsCall".
  preservation_simpl.
  assert (Hwfc:=HwfS1).
  apply wf_State__wf_cmd in Hwfc.
  assert (uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb)) as Huniq.
    eapply wf_system__uniqFdef; eauto.
  assert (wf_fdef nil S (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fa rt fid la va) lb)) as HwfF.
    eapply wf_system__wf_fdef; eauto.
  repeat (split; auto). 
    eapply initLocals__wf_rmap; eauto.

    inv Hwfc. inv H7.
    eapply initLocals__wf_rmetadata in H0; eauto.
      eapply wf_value_list__in_params__wf_value; eauto.

    exists l'. exists ps'. exists nil. simpl_env. auto.
    eauto.

  apply mismatch_cons_false in H27. inv H27.
Unfocus.

Case "nsExCall". 
  symmetry in H32.
  apply mismatch_cons_false in H32. inv H32.

  preservation_simpl.
  repeat ctx_simpl'.
  repeat (split; auto). 
    eapply callExternalFunction_preserves_wf_mmetadata; eauto.
    eapply callExternalFunction_preserves_wf_global_ptr; eauto.
   
    unfold exCallUpdateLocals in H5.
    destruct noret0.
      inv H5; auto.

      destruct oresult; tinv H5.
      destruct ft; tinv H5.
      remember (fit_gv (los, nts) ft g) as R.
      destruct R; tinv H5.
      assert (HwfS1':=HwfS1).
      apply wf_State__inv in HwfS1'.
      destruct HwfS1' as [_ [_ Hwfc]].
      inv Hwfc. inv H21. inv H12. inv H23.
      remember (isPointerTypB typ1) as R.
      destruct R; inv H5; auto.
        apply updateAddAL_ptr__wf_rmap; auto.
        apply updateAddAL_nptr__wf_rmap; try solve [auto |
          apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1;
          rewrite HwfS1; simpl; 
          try solve [auto | intros t0 EQ; subst; inv EQ; inv HeqR0]].

    unfold exCallUpdateLocals in H5.
    destruct noret0.
      inv H5.
      eapply callExternalFunction_preserves_wf_rmetadata; eauto.

      destruct oresult; tinv H5.
      destruct ft; tinv H5.
      remember (fit_gv (los, nts) ft g) as R.
      destruct R; tinv H5.
      assert (HwfS1':=HwfS1).
      apply wf_State__inv in HwfS1'.
      destruct HwfS1' as [_ [_ Hwfc]].
      inv Hwfc. inv H21. inv H12. inv H23.
      remember (isPointerTypB typ1) as R.
      destruct R; inv H5.
        apply adding_null_preserves_wf_rmetadata; auto.
          eapply callExternalFunction_preserves_wf_rmetadata; eauto.
        eapply callExternalFunction_preserves_wf_rmetadata; eauto.

    eauto.

    eapply callExternalFunction_preserves_wf_ECStack; eauto.

Transparent wf_mmetadata wf_rmetadata.
Qed.

(*********************************************)
(** * not stuck *)

Lemma get_const_metadata_isnt_stuck : forall S TD Mem gl vc gv ct bc ec,
  wf_global_ptr S TD Mem gl ->
  wf_const S TD vc ct ->
  NDopsem.const2GV TD gl vc = Some gv ->
  get_const_metadata vc = Some (bc, ec) ->
  exists blk, exists bofs, exists eofs,
    const2GV TD gl bc = Some ((Vptr blk bofs, AST.Mint 31)::nil) /\ 
    const2GV TD gl ec = Some ((Vptr blk eofs, AST.Mint 31)::nil).
Proof.
  unfold NDopsem.const2GV, const2GV.
  intros S TD Mem gl vc gv ct bc ec Hwfg Hwfc J1 J2.  
  remember (_const2GV TD gl vc) as J3.
  destruct J3 as [[gv3 t3]|]; inv J1.
  generalize dependent gv3.
  generalize dependent t3.
  generalize dependent ec.
  generalize dependent bc.
  generalize dependent ct.
  induction vc; intros; try solve [inversion J2].
    simpl in HeqJ3.
    remember (lookupAL GenericValue gl i0) as R.
    destruct R; inv HeqJ3.
    symmetry in HeqR.
    assert (Hwfc':=Hwfc).
    inv Hwfc'.
    unfold wf_global_ptr in Hwfg.
    assert (Hlk:=HeqR).
    apply Hwfg with (typ0:=t) in HeqR; simpl; auto.
    destruct HeqR as [b [sz [J1 [J5 [J3 J4]]]]]; subst.
    destruct t; inv J2; 
      try solve [eapply get_const_metadata_isnt_stuck_helper; eauto].
 
      simpl. rewrite Hlk. simpl.
      unfold mgetoffset. simpl.
      exists b. exists (Int.zero 31). exists (Int.zero 31). 
      split; auto.

    destruct c; tinv J2.
    destruct t; tinv J2.
    simpl in *. inv Hwfc.
    remember (_const2GV TD gl vc) as R.
    destruct R as [[]|]; tinv HeqJ3.
    destruct t0; inv HeqJ3.
    destruct TD. inv H4.
    eapply IHvc with (ct:=typ_pointer typ1); auto.

    simpl in *.
    remember (_const2GV TD gl vc) as R1.
    destruct R1 as [[]|]; tinv HeqJ3.
    destruct t; tinv HeqJ3.
    remember (getConstGEPTyp l0 (typ_pointer t)) as R2.
    destruct R2; tinv HeqJ3.
    inv Hwfc.
    eapply IHvc in J2; eauto.
Qed.

Lemma get_reg_metadata_isnt_stuck : forall Mem s los nts Ps t f rm gl lc gv v
  (Hwfgptr : wf_global_ptr s (los,nts) Mem gl)
  (Hwfv : wf_value s (module_intro los nts Ps) f v t)
  (Hptr : true = isPointerTypB t)
  (Hget : NDopsem.getOperandValue (los, nts) v lc gl = ret gv)
  (Hwfm : wf_rmap f lc rm),
  exists omd : metadata, get_reg_metadata (los, nts) gl rm v = ret omd.
Proof.
  intros.
  destruct v; simpl in *.
    assert (exists md, lookupAL metadata rm i0 = Some md) as J0.
      destruct t; try solve [inversion Hptr].
      eapply Hwfm with (t1:=t); eauto.
        inv Hwfv; auto.
    destruct J0 as [md J0].
    rewrite J0; eauto.
  
    remember (get_const_metadata c) as R.
    destruct R as [[bc ec]|]; eauto.
      remember (NDopsem.const2GV (los, nts) gl c) as R.
      destruct R; try solve [inv Hget].
      inv Hwfv.
      symmetry in HeqR0.
      eapply get_const_metadata_isnt_stuck in HeqR0; eauto.
      destruct HeqR0 as [blk [bofs [eofs [Hc1 Hc2]]]].
      rewrite Hc1. rewrite Hc2.
      destruct (zeq blk blk); try solve [contradict n; auto].
      destruct (eq_nat_dec 31 31); try solve [contradict n; auto | simpl; eauto].
Qed.

Definition matched_incoming_values (re1:list (id * GVs))
  (re2:list (id * GVs * option metadata)) : Prop :=
List.Forall2 
  (fun e1 e2 =>
     let '(id1, gv1) := e1 in
     let '(id2, gv2, _) := e2 in
     id1 = id2 /\ gv1 = gv2
  ) 
  re1 re2.

Lemma wf_phinodes__getIncomingValuesForBlockFromPHINodes : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  l0
  (lc : GVsMap)
  (gl : GVMap)
  b Mem
  (Hwfgptr : wf_global_ptr s (los,nts) Mem gl)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  ps2
  (H8 : wf_phinodes nil s (module_intro los nts ps) f
         (block_intro l0 ps' cs' tmn') ps2)
  rm (Hwfm: wf_rmap f lc rm) re
  (HgetIn : NDopsem.getIncomingValuesForBlockFromPHINodes (los, nts) ps2 
       b gl lc = ret re)
  (Hin: exists ps1, ps' = ps1 ++ ps2),
   exists RVs : list (id * GVs * option metadata),
     getIncomingValuesForBlockFromPHINodes (los, nts) ps2 
       b gl lc rm = ret RVs /\
     matched_incoming_values re RVs.
Proof.
  unfold matched_incoming_values.
  induction ps2; simpl in *; intros.
    inv HgetIn.
    exists nil. auto.
  
    destruct a. 
    remember (getValueViaBlockFromValuels l1 b) as R0.
    destruct R0 as [v|]; tinv HgetIn.
    remember (NDopsem.getOperandValue (los, nts) v lc gl) as R1.
    destruct R1 as [gv1|]; tinv HgetIn.
    remember (NDopsem.getIncomingValuesForBlockFromPHINodes 
      (los, nts) ps2 b gl lc) as R2.
    destruct R2; inv HgetIn.
    inv H8. 
    destruct Hin as [ps1 Hin]; subst.
    assert (exists ps0, ps1 ++ insn_phi i0 t l1 :: ps2 = ps0 ++ ps2) as Heq.
      exists (ps1 ++ [insn_phi i0 t l1]). simpl_env. auto.
    eapply IHps2 in H7; eauto.
    destruct H7 as [RVs [J1 J2]].
    rewrite J1.
    assert (HwfV:=HeqR0).
    symmetry in HwfV. destruct b.
    inv H6.
    eapply wf_value_list__getValueViaLabelFromValuels__wf_value in HwfV; eauto.
    remember (isPointerTypB t) as R.
    destruct R; eauto.
      assert (exists omd, get_reg_metadata (los, nts) gl rm v = ret omd) as J.
        eapply get_reg_metadata_isnt_stuck; eauto.       
      destruct J as [md J].
      rewrite J.
      eauto.
Qed.

Lemma llvm_sb_updateValuesForNewBlock : forall lc rm re RVs,
  matched_incoming_values re RVs ->
  exists rm' : rmetadata,
    ret updateValuesForNewBlock RVs lc rm =
    ret (NDopsem.updateValuesForNewBlock re lc, rm').
Proof.
  induction 1; simpl; eauto.
    destruct x. destruct y. destruct p.
    destruct H; subst.
    destruct IHForall2 as [rm' IHForall2].
    inv IHForall2.
    rewrite H1.
    unfold prop_reg_metadata.
    destruct o; eauto.
Qed.

Definition matched_params (re1:list GVs) 
  (re2:list (GVs * option metadata)) : Prop :=
List.Forall2 (fun gv1 e2 => let '(gv2, _) := e2 in gv1 = gv2) re1 re2.

Hint Unfold matched_params.

Lemma params2GVs_isnt_stuck : forall TD lc gl rm p re
  (J : NDopsem.params2GVs TD p lc gl = ret re),
  exists gvs, params2GVs TD p lc gl rm = Some gvs /\ 
    matched_params re gvs.
Proof.
  induction p; simpl; intros.
    inv J. eauto.

    destruct a.
    destruct (NDopsem.getOperandValue TD v lc gl) as [gv|]; tinv J.
    remember (NDopsem.params2GVs TD p lc gl) as R.
    destruct R as [gvs|]; inv J.
    destruct (@IHp gvs) as [gvs' [J1 J2]]; auto.
    rewrite J1.
    destruct (isPointerTypB t); eauto.     
Qed.

Lemma initializeFrameValues__total_aux : forall TD la2 gvs1 gvs2 lc1 rm1 lc,
  matched_params gvs1 gvs2 ->
  NDopsem._initializeFrameValues TD la2 gvs1 lc1 = Some lc ->
  exists rm, _initializeFrameValues TD la2 gvs2 lc1 rm1 = Some (lc, rm).
Proof.
  induction la2; simpl in *; intros.
    inv H0. eauto.

    destruct a. destruct p.
    unfold prop_reg_metadata.
    inv H.
      remember (NDopsem._initializeFrameValues TD la2 nil lc1) as R.
      destruct R; tinv H0.
      edestruct IHla2 with (rm1:=rm1); eauto. 
      rewrite H.
      destruct (gundef TD t); inv H0.
      destruct (isPointerTypB t); eauto.

      destruct y. subst.
      remember (NDopsem._initializeFrameValues TD la2 l0 lc1) as R.
      destruct R; inv H0.
      edestruct IHla2 with (rm1:=rm1); eauto. 
      rewrite H.
      destruct (isPointerTypB t); eauto.
      destruct o; eauto.
Qed.

Lemma initLocal__total : forall gvs1 gvs2 TD lc la, 
  matched_params gvs1 gvs2 ->
  NDopsem.initLocals TD la gvs1 = ret lc ->
  exists rm, initLocals TD la gvs2 = Some (lc, rm).
Proof.
  intros.
  unfold initLocals.
  unfold NDopsem.initLocals in H0.
  eapply initializeFrameValues__total_aux; eauto.
Qed.

Lemma exCallUpdateLocals_isnt_stuck : forall TD t n i0 o lc rm lc',
  NDopsem.exCallUpdateLocals TD t n i0 o lc = Some lc' ->
  exists rm', exCallUpdateLocals TD t n i0 o lc rm = Some (lc', rm').
Proof.
  intros.
  unfold NDopsem.exCallUpdateLocals in H.
  unfold exCallUpdateLocals.
  destruct n; inv H; eauto.
  destruct o; tinv H1.
  destruct t; tinv H1.
  destruct (fit_gv TD t g); inv H1; eauto.
  destruct (isPointerTypB t); eauto.
Qed.

Lemma wf_GVs__wf_genericvalue : forall TD gvs gv t,
  wf_GVs TD gvs t -> gv @ gvs -> wf_genericvalue TD gv t.
Proof.
  intros.
  inv H. eauto.
Qed.

(*********************************************)
(** * Progress *)

Definition spatial_memory_violation S : Prop :=
  match S with
  | {| SBnsop.CurTargetData := TD;
       SBnsop.ECS := {| SBnsop.CurCmds := insn_load _ t vp _ :: cs;
                           SBnsop.Locals := lc;
                           SBnsop.Rmap := rm
                         |} :: _;
        SBnsop.Globals := gl;
        SBnsop.Mem := Mem0 |} => 
      match SBopsem.get_reg_metadata TD gl rm vp, 
            NDopsem.getOperandValue TD vp lc gl with
      | ret md, ret gvps => 
          exists gvp, gvp @ gvps /\ ~ SBopsem.assert_mptr TD t gvp md
      | _, _ => False
      end
  | {| SBnsop.CurTargetData := TD;
       SBnsop.ECS := {| SBnsop.CurCmds := insn_store _ t v vp _ :: cs;
                           SBnsop.Locals := lc;
                           SBnsop.Rmap := rm
                         |} :: _;
        SBnsop.Globals := gl;
        SBnsop.Mem := Mem0 |} => 
      match SBopsem.get_reg_metadata TD gl rm vp, 
            NDopsem.getOperandValue TD vp lc gl with
      | ret md, ret gvps => 
          exists gvp, gvp @ gvps /\ ~ SBopsem.assert_mptr TD t gvp md
      | _, _ => False
      end
  | _ => False
  end.

Definition undefined_state S : Prop :=
  match S with
  | {| SBnsop.CurTargetData := td;
       SBnsop.ECS := {|
                SBnsop.CurCmds := nil;
                SBnsop.Terminator := insn_return _ _ _;
                SBnsop.Allocas := als |} :: 
              {| SBnsop.CurCmds := c::_ |} :: _;
       SBnsop.Mem := M |} => free_allocas td M als = None
  | _ => False
  end \/
  match S with
  | {| SBnsop.CurTargetData := td;
       SBnsop.ECS := {|
                SBnsop.CurBB := _;
                SBnsop.CurCmds := nil;
                SBnsop.Terminator := insn_return_void _;
                SBnsop.Allocas := als |} :: 
              {| SBnsop.CurCmds := c::_ |} :: _;
       SBnsop.Mem := M |} => 
                      free_allocas td M als = None \/ 
                      match getCallerReturnID c with
                      | Some _ => True
                      | _ => False
                      end
  | _ => False
  end \/
  match S with
  | {| SBnsop.ECS := {|
                SBnsop.CurBB := block_intro _ _ _ (insn_unreachable _);
                SBnsop.CurCmds := nil;
                SBnsop.Terminator := (insn_unreachable _)
               |} :: _
     |} => True
  | _ => False
  end \/
  match S with
  | {| SBnsop.CurTargetData := td;
       SBnsop.ECS := 
         {| SBnsop.CurCmds := insn_malloc _ t v a::_ ; 
            SBnsop.Locals := lc|} :: _;
       SBnsop.Globals := gl;
      SBnsop.Mem := M |}
  | {| SBnsop.CurTargetData := td;
       SBnsop.ECS := 
         {| SBnsop.CurCmds := insn_alloca _ t v a::_ ; 
            SBnsop.Locals := lc|} :: _;
       SBnsop.Globals := gl;
       SBnsop.Mem := M |} =>
       match NDopsem.getOperandValue td v lc gl with
       | Some gns =>
           match getTypeAllocSize td t with
           | Some asz => exists gn, gn @ gns /\ 
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
  | {| SBnsop.CurTargetData := td;
       SBnsop.ECS := 
         {| SBnsop.CurCmds := insn_free _ _ v::_ ; SBnsop.Locals := lc|} 
         :: _;
       SBnsop.Globals := gl;
       SBnsop.Mem := M |} =>
       match NDopsem.getOperandValue td v lc gl with
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
  | {| SBnsop.CurTargetData := td;
       SBnsop.ECS := 
         {| SBnsop.CurCmds := insn_load _ t v a::_ ; 
            SBnsop.Locals := lc|} :: _;
       SBnsop.Globals := gl;
       SBnsop.Mem := M |} =>
       match NDopsem.getOperandValue td v lc gl with
       | Some gvs => exists gv, gv @ gvs /\ other_load_violation td M gv t
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| SBnsop.CurTargetData := td;
       SBnsop.ECS := 
         {| SBnsop.CurCmds := insn_store _ t v v0 a::_ ; 
            SBnsop.Locals := lc|} :: _;
       SBnsop.Globals := gl;
       SBnsop.Mem := M |} =>
       match NDopsem.getOperandValue td v lc gl, 
             NDopsem.getOperandValue td v0 lc gl with
       | Some gvs, Some mgvs => 
           exists gv, exists mgv, 
             gv @ gvs /\ mgv @ mgvs /\ other_store_violation td M mgv gv
       | _, _ => False
       end
  | _ => False
  end \/
  match S with
  | {| SBnsop.CurTargetData := td;
       SBnsop.CurProducts := ps;
       SBnsop.ECS := 
         {| SBnsop.CurCmds := insn_call i0 n _ ft v p::_ ; 
            SBnsop.Locals := lc; SBnsop.Rmap := rm |} :: _;
       SBnsop.Globals := gl;
       SBnsop.FunTable := fs;
       SBnsop.Mem := M |} =>
       match NDopsem.getOperandValue td v lc gl with
       | Some fptrs =>
            exists fptr, fptr @ fptrs /\
            match lookupFdefViaPtr ps fs fptr, 
                  lookupExFdecViaPtr ps fs fptr with
            | None, Some (fdec_intro (fheader_intro fa rt fid la va)) =>
                match NDopsem.params2GVs td p lc gl with
                | Some gvss =>
                  exists gvs, gvs @@ gvss /\
                  match LLVMopsem.callExternalFunction M fid gvs with
                  | Some (oresult, _) =>
                     match exCallUpdateLocals td ft n i0 oresult lc rm with
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
  end \/
  spatial_memory_violation S.

Hint Unfold undefined_state spatial_memory_violation other_load_violation
            other_store_violation.

Hint Constructors SBnsop.nsInsn_delta SBnsop.nsInsn.

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

Ltac SSSSSCase name := Case_aux subsubsubsubsubcase name.
Ltac SSSSSSCase name := Case_aux subsubsubsubsubsubcase name.
Ltac SSSSSSSCase name := Case_aux subsubsubsubsubsubsubcase name.

Lemma llvm_isFinialState__sb_isFinialState : forall S,
  NDopsem.ns_isFinialState (sbState__State S) = true -> 
  ns_isFinialState S = true.
Proof.
  intros S Hfinal.
  destruct S. 
  destruct ECS0; simpl in *; auto.
  destruct e; simpl in *; auto.
  destruct CurCmds0; simpl in *; auto.
  destruct Terminator0; simpl in *; auto.
    destruct ECS0; simpl in *; auto.
    destruct ECS0; simpl in *; auto.
Qed.

Lemma llvm_exCallUpdateLocals__sb_exCallUpdateLocals : forall TD t n i0 o lc rm,
  NDopsem.exCallUpdateLocals TD t n i0 o lc = None ->
  exCallUpdateLocals TD t n i0 o lc rm = None.
Proof.
  intros.
  unfold NDopsem.exCallUpdateLocals in H.
  unfold exCallUpdateLocals.
  destruct n; tinv H.
  destruct o; tinv H; auto.
  destruct t; tinv H; auto.
  destruct (fit_gv TD t g); tinv H; auto.
Qed.
       
Lemma load_progress : forall s los nts ps f b i0 t v a cs tmn lc rm als ecs gl
  fs M Mmap0 gvs gv
  (HwfS1 : wf_State
            {|
            CurSystem := s;
            CurTargetData := (los, nts);
            CurProducts := ps;
            ECS := {|
                   CurFunction := f;
                   CurBB := b;
                   CurCmds := insn_load i0 t v a :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Rmap := rm;
                   Allocas := als |} :: ecs;
            Globals := gl;
            FunTable := fs;
            Mem := M;
            Mmap := Mmap0 |})
  (HeqR : NDopsem.getOperandValue (los, nts) v lc gl = Some gvs) 
  (Hin : gv @ gvs),
  (exists S2 : State,
      exists tr : trace,
        nsInsn
          {|
          CurSystem := s;
          CurTargetData := (los, nts);
          CurProducts := ps;
          ECS := {|
                 CurFunction := f;
                 CurBB := b;
                 CurCmds := insn_load i0 t v a :: cs;
                 Terminator := tmn;
                 Locals := lc;
                 Rmap := rm;
                 Allocas := als |} :: ecs;
          Globals := gl;
          FunTable := fs;
          Mem := M;
          Mmap := Mmap0 |} S2 tr) \/
   undefined_state
     {|
     CurSystem := s;
     CurTargetData := (los, nts);
     CurProducts := ps;
     ECS := {|
            CurFunction := f;
            CurBB := b;
            CurCmds := insn_load i0 t v a :: cs;
            Terminator := tmn;
            Locals := lc;
            Rmap := rm;
            Allocas := als |} :: ecs;
     Globals := gl;
     FunTable := fs;
     Mem := M;
     Mmap := Mmap0 |}.
Proof.
  intros.
  destruct HwfS1 as [HwfMM1 [Hwfg1 [Hwfg1' [HwfSys1 [HmInS1 HwfECs]]]]].
  destruct HwfECs as [[Hreach [HbInF [HfInPs [Hwflc [Hinscope [Hwfm [Hwfm'
                        [l1 [ps1 [cs1 Heq]]]]]]]]]]
                      [HwfECs HwfCall]].
  subst b.
  assert (wf_insn nil s (module_intro los nts ps) f 
           (block_intro l1 ps1 (cs1 ++ (insn_load i0 t v a) :: cs) tmn) 
           (insn_cmd (insn_load i0 t v a))) as Hwfc.
    eapply wf_system__wf_cmd in HbInF; eauto using in_middle.
  assert (exists omd, SBopsem.get_reg_metadata (los, nts) gl rm v = 
    Some omd) as J2.
    eapply get_reg_metadata_isnt_stuck; try solve [eauto | inv Hwfc; eauto].
  destruct J2 as [md J2].
  destruct (assert_mptr_dec (los, nts) t gv md) as [J3 | J3].
  SSCase "assert ok".
    assert (exists b, exists ofs, 
      GV2ptr (los,nts) (getPointerSize (los,nts)) gv = Some (Values.Vptr b ofs)
      ) as R3. 
      unfold assert_mptr in J3.
      destruct md.
      destruct (GV2ptr (los, nts) (getPointerSize (los, nts)) gv); 
        try solve [inv J3].
      destruct v0; inv J3; eauto.
    destruct R3 as [b [ofs R3]].
    inv Hwfc. 
    assert (exists mcs, flatten_typ (los,nts) t = Some mcs) as Hflat.
      inv H11. eapply flatten_typ_total; eauto.
    destruct Hflat as [mcs Hflat].
    destruct (proper_aligned_dec mcs (Int.signed 31 ofs)) as [R5 | R5].
    SSSCase "align ok".
      destruct (blk_temporal_safe_dec M b) as [R8 | R8].
      SSSSCase "valid block".
        assert (exists gv', mload (los,nts) M gv t a = Some gv') as R6.
          unfold mload.
          rewrite R3. rewrite Hflat.
          destruct md as [gvb gve].
          eapply wf_rmetadata__get_reg_metadata in J2; eauto.
          apply wf_value__wf_typ in H8. destruct H8. inv H.
          eapply mload_aux_isnt_stuck; eauto.
  
        destruct R6 as [gv' R6].
        remember (isPointerTypB t) as R1.
        destruct R1.      
        SSSSSCase "load_ptr".
          left.
          exists 
           {|
             SBnsop.CurSystem := s;
             SBnsop.CurTargetData := (los, nts);
             SBnsop.CurProducts := ps;
             SBnsop.ECS := {|
                SBnsop.CurFunction := f;
                SBnsop.CurBB := block_intro l1 ps1
                         (cs1 ++ insn_load i0 t v a :: cs) tmn;
                SBnsop.CurCmds := cs;
                SBnsop.Terminator := tmn;
                SBnsop.Locals := updateAddAL _ lc i0 ($ gv' # t $);
                SBnsop.Rmap := updateAddAL _ rm i0 
                  (SBopsem.get_mem_metadata (los, nts) Mmap0 gv);
                SBnsop.Allocas := als |} :: ecs;
             SBnsop.Globals := gl;
             SBnsop.FunTable := fs;
             SBnsop.Mem := M;
             SBnsop.Mmap := Mmap0 |}.
          exists trace_nil. 
          apply nsInsn_intro; try solve [eauto | simpl; eauto].
  
        SSSSSCase "load_nptr".
          left.
          exists 
           {|
             SBnsop.CurSystem := s;
             SBnsop.CurTargetData := (los, nts);
             SBnsop.CurProducts := ps;
             SBnsop.ECS := {|
                SBnsop.CurFunction := f;
                SBnsop.CurBB := block_intro l1 ps1
                         (cs1 ++ insn_load i0 t v a :: cs) tmn;
                SBnsop.CurCmds := cs;
                SBnsop.Terminator := tmn;
                SBnsop.Locals := updateAddAL _ lc i0 ($ gv' # t $);
                SBnsop.Rmap := rm;
                SBnsop.Allocas := als |} :: ecs;
             SBnsop.Globals := gl;
             SBnsop.FunTable := fs;
             SBnsop.Mem := M;
             SBnsop.Mmap := Mmap0 |}.
          exists trace_nil.
          apply nsInsn_intro; try solve [eauto | simpl; eauto].
  
      SSSSCase "~valid block".
        right.
        unfold undefined_state. unfold other_load_violation.
        right. rewrite HeqR. right. right. right. right. left.
        exists gv. rewrite R3. rewrite Hflat. undefbehave.
  
    SSSCase "align fails".
      right.
      unfold undefined_state. unfold other_load_violation.
      right. rewrite HeqR. right. right. right. right. left.
      exists gv. rewrite R3. rewrite Hflat. undefbehave.
  
  SSCase "assert fails".
    right.
    unfold undefined_state. unfold spatial_memory_violation.
    right. rewrite HeqR. rewrite J2. right. right. right. right. right. right. 
    right. exists gv. undefbehave.
Qed.

Lemma store_progress : forall s los nts ps f b i0 t v v0 a cs tmn lc rm als ecs
  gl fs M Mmap0 gvs1 gvs2 gv mgv
  (HwfS1 : wf_State
            {|
            CurSystem := s;
            CurTargetData := (los, nts);
            CurProducts := ps;
            ECS := {|
                   CurFunction := f;
                   CurBB := b;
                   CurCmds := insn_store i0 t v v0 a :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Rmap := rm;
                   Allocas := als |} :: ecs;
            Globals := gl;
            FunTable := fs;
            Mem := M;
            Mmap := Mmap0 |})
  (J : NDopsem.getOperandValue (los, nts) v lc gl = Some gvs1)
  (Hin : gv @ gvs1)
  (J0 : NDopsem.getOperandValue (los, nts) v0 lc gl = Some gvs2)
  (Hin0 : mgv @ gvs2),
  (exists S2 : State,
      exists tr : trace,
        nsInsn
          {|
          CurSystem := s;
          CurTargetData := (los, nts);
          CurProducts := ps;
          ECS := {|
                 CurFunction := f;
                 CurBB := b;
                 CurCmds := insn_store i0 t v v0 a :: cs;
                 Terminator := tmn;
                 Locals := lc;
                 Rmap := rm;
                 Allocas := als |} :: ecs;
          Globals := gl;
          FunTable := fs;
          Mem := M;
          Mmap := Mmap0 |} S2 tr) \/
   undefined_state
     {|
     CurSystem := s;
     CurTargetData := (los, nts);
     CurProducts := ps;
     ECS := {|
            CurFunction := f;
            CurBB := b;
            CurCmds := insn_store i0 t v v0 a :: cs;
            Terminator := tmn;
            Locals := lc;
            Rmap := rm;
            Allocas := als |} :: ecs;
     Globals := gl;
     FunTable := fs;
     Mem := M;
     Mmap := Mmap0 |}.
Proof.
  intros.
  destruct HwfS1 as [HwfMM1 [Hwfg1 [Hwfg1' [HwfSys1 [HmInS1 HwfECs]]]]].
  destruct HwfECs as [[Hreach [HbInF [HfInPs [Hwflc [Hinscope [Hwfm [Hwfm'
                        [l1 [ps1 [cs1 Heq]]]]]]]]]]
                      [HwfECs HwfCall]].
  subst b.
  assert (wf_insn nil s (module_intro los nts ps) f 
           (block_intro l1 ps1 (cs1 ++ (insn_store i0 t v v0 a) :: cs) tmn) 
           (insn_cmd (insn_store i0 t v v0 a))) as Hwfc.
    eapply wf_system__wf_cmd in HbInF; eauto using in_middle.

    inv Hwfc.
    assert (exists omd, SBopsem.get_reg_metadata (los, nts) gl rm v0 = 
      Some omd) as J2.
      eapply get_reg_metadata_isnt_stuck; try solve [eauto | inv Hwfc; eauto].
    destruct J2 as [md J2].
    destruct (assert_mptr_dec (los, nts) t mgv md) as [J3 | J3].
    SSCase "assert ok".
      assert (exists b, exists ofs, 
       GV2ptr (los,nts) (getPointerSize (los,nts)) mgv = Some (Values.Vptr b ofs)
       ) as R3.
        unfold assert_mptr in J3.
        destruct md.
        destruct (GV2ptr (los, nts) (getPointerSize (los, nts)) mgv); 
          try solve [inv J3].
        destruct v1; inv J3; eauto.
      destruct R3 as [b [ofs R3]].
      destruct (aligned_gv_dec gv (Int.signed 31 ofs)) as [R5 | R5].
      SSSCase "align ok".
        destruct (blk_temporal_safe_dec M b) as [R9 | R9].
        SSSSCase "valid block".
          assert (exists M', mstore (los,nts) M mgv t gv a = Some M') 
            as R6.
            unfold mstore.
            rewrite R3. 
            destruct md as [gvb gve].
            eapply wf_rmetadata__get_reg_metadata in J2; eauto.
            eapply mstore_aux_isnt_stuck; eauto.
              eapply getOperandValue__wf_gvs in J; 
                eauto using wf_GVs__wf_genericvalue.

          destruct R6 as [M' R6].
          remember (isPointerTypB t) as R1.
          destruct R1.      
          SSSSSCase "store_ptr".
            assert (exists omd, SBopsem.get_reg_metadata (los, nts) gl rm v = 
              Some omd) as J4.
              eapply get_reg_metadata_isnt_stuck; 
                try solve [eauto | inv Hwfc; eauto].
            destruct J4 as [md' J4].
            left.
            remember (set_mem_metadata (los, nts) Mmap0 mgv md') as Mmap0'.
            exists 
               {|
               CurSystem := s;
               CurTargetData := (los, nts);
               CurProducts := ps;
               ECS := {|
                    CurFunction := f;
                    CurBB := block_intro l1 ps1
                               (cs1 ++ insn_store i0 t v v0 a :: cs) tmn;
                    CurCmds := cs;
                    Terminator := tmn;
                    Locals := lc;
                    Rmap := rm;
                    Allocas := als |} :: ecs;
               Globals := gl;
               FunTable := fs;
               Mem := M';
               Mmap := Mmap0'|}.
            exists trace_nil.
            apply nsInsn_intro; try solve [eauto | simpl; eauto].

          SSSSSCase "store_nptr".
            left.
            exists 
               {|
               CurSystem := s;
               CurTargetData := (los, nts);
               CurProducts := ps;
               ECS := {|
                    CurFunction := f;
                    CurBB := block_intro l1 ps1
                               (cs1 ++ insn_store i0 t v v0 a :: cs) tmn;
                    CurCmds := cs;
                    Terminator := tmn;
                    Locals := lc;
                    Rmap := rm;
                    Allocas := als |} :: ecs;
               Globals := gl;
               FunTable := fs;
               Mem := M';
               Mmap := Mmap0|}.
            exists trace_nil.
            apply nsInsn_intro; try solve [eauto | simpl; eauto].

        SSSSCase "~valid block".
          right.
          unfold undefined_state. unfold other_store_violation.
          right. rewrite J. rewrite J0. right. right. right. right. right. left.
          exists gv. exists mgv. rewrite R3. undefbehave.

      SSSCase "align fails".
        right.
        unfold undefined_state. unfold other_store_violation.
        right. rewrite J. rewrite J0. right. right. right. right. right. left.
        exists gv. exists mgv. rewrite R3. undefbehave.

    SSCase "assert fails".
      right.
      unfold undefined_state. unfold spatial_memory_violation.
      right. rewrite J. rewrite J0. rewrite J2. right. right. right. right. 
      right. right. right. exists mgv. undefbehave.
Qed.

Lemma llvm_undef__sb_progress : forall (S1 : State)
  (HwfS1 : wf_State S1)
  (Hundef : ndopsem_pp.undefined_state (sbState__State S1)),
  (exists S2 : State, exists tr : trace, nsInsn S1 S2 tr) \/
  undefined_state S1.
Proof.
  intros.
  unfold ndopsem_pp.undefined_state in Hundef.
  destruct S1 as [s [los nts] ps ecs gl fs M]; simpl in Hundef.
  destruct ecs; simpl in Hundef.
    elim_undef_false Hundef.
  destruct e as  [f b cs tmn lc rm als]; simpl in Hundef.
  destruct cs; simpl in Hundef.
    destruct tmn; simpl in Hundef.
      destruct ecs; simpl in Hundef.
        elim_undef_false Hundef.
        destruct b.
        destruct t0; inversion Hundef.

        destruct e; simpl in Hundef.
        elim_undef_false Hundef.
          destruct CurCmds0; tinv Hundef.
            undefbehave.
          destruct b.
          destruct t0; inversion Hundef.
      elim_undef_false Hundef.
      destruct ecs; tinv Hundef.
      destruct e; tinv Hundef.
        simpl in Hundef.
        destruct CurCmds0; tinv Hundef.
          undefbehave.
        destruct b.
        destruct t; inversion Hundef.

      elim_undef_false Hundef.
      destruct b.
      destruct t; inversion Hundef.

      elim_undef_false Hundef.
      destruct b.
      destruct t; inversion Hundef.

      elim_undef_false Hundef.
      destruct b.
      destruct t; inversion Hundef.
        undefbehave.

    elim_undef_false Hundef.
      destruct b.
      destruct t; inversion Hundef.

      destruct c; try solve [inversion Hundef | undefbehave].
      destruct c; try solve [inversion Hundef | undefbehave].   
      destruct c; try solve [inversion Hundef | undefbehave].
        remember (NDopsem.getOperandValue (los, nts) v lc gl) as R.
        destruct R as [gvs|]; tinv Hundef.
        destruct Hundef as [gv [Hin Hundef]].
        eapply load_progress; eauto.

      destruct c; try solve [inversion Hundef | undefbehave].
        remember (NDopsem.getOperandValue (los, nts) v lc gl) as R1.
        remember (NDopsem.getOperandValue (los, nts) v0 lc gl) as R2.
        destruct R1 as [gvs1|]; tinv Hundef.
        destruct R2 as [gvss|]; tinv Hundef.
        destruct Hundef as [gv [mgv [Hin1 [Hin2 Hundef]]]].
        eapply store_progress; eauto.

      destruct c; try solve [inversion Hundef | undefbehave].
        unfold undefined_state.
        destruct (NDopsem.getOperandValue (los, nts) v lc gl); tinv Hundef.
        destruct Hundef as [fptr [Hin Hundef]].
        right. right. right. right. right. right. right. right. left.
        exists fptr. split; auto. 
        destruct (lookupFdefViaPtr ps fs fptr); tinv Hundef.
        destruct (lookupExFdecViaPtr ps fs fptr); 
          try solve [inversion Hundef | undefbehave].
        destruct f0.
        destruct f0.     
        destruct (NDopsem.params2GVs (los, nts) p lc gl); tinv Hundef.
        destruct Hundef as [gvs [Hin2 Hundef]].
        exists gvs. split; auto.
        destruct (callExternalFunction M i1 gvs) as [[]|];
          try solve [inversion Hundef | undefbehave].
        remember (NDopsem.exCallUpdateLocals (los, nts) t n i0 o lc) as R.
        destruct R; try solve [inversion Hundef | undefbehave].
        rewrite llvm_exCallUpdateLocals__sb_exCallUpdateLocals; auto.
Qed.

Lemma sbECs__ECs_cons_inv : forall ec11 ecs12 ecs2, 
  ec11 :: ecs12 = sbECs__ECs ecs2 ->
  exists ec21, exists ecs22, ecs2 = ec21 :: ecs22 /\
    ec11 = sbEC__EC ec21 /\ ecs12 = sbECs__ECs ecs22.
Proof.
  intros.
  destruct ecs2; inv H; eauto.
Qed.

Lemma sbECs__ECs_cons_inv0 : forall F' B' cs' tmn' lc' als' ecs12 ecs2, 
 (NDopsem.mkEC F' B' cs' tmn' lc' als') :: ecs12 = sbECs__ECs ecs2 ->
  exists rm', exists ecs22, 
    ecs2 = (SBnsop.mkEC F' B' cs' tmn' lc' rm' als') :: ecs22 /\
    ecs12 = sbECs__ECs ecs22.
Proof.
  intros.
  destruct ecs2; tinv H.
  destruct e; inv H; eauto.
Qed.

Ltac progress_tac_aux rm' :=
  match goal with
  | [ Hstep' : NDopsem.nsInsn
             (sbState__State
                {|
                CurSystem := ?s;
                CurTargetData := (?los, ?nts);
                CurProducts := ?ps;
                ECS := {|
                       CurFunction := ?f;
                       CurBB := ?b;
                       CurCmds := _ :: ?cs;
                       Terminator := ?tmn;
                       Locals := _ ;
                       Rmap := ?rm;
                       Allocas := _ |} :: ?ecs;
                Globals := ?gl;
                FunTable := ?fs;
                Mem := _;
                Mmap := ?Mmap0 |})
             {|
             NDopsem.CurSystem := ?s;
             NDopsem.CurTargetData := (?los, ?nts);
             NDopsem.CurProducts := ?ps;
             NDopsem.ECS := {|
                              NDopsem.CurFunction := ?f;
                              NDopsem.CurBB := ?b;
                              NDopsem.CurCmds := ?cs;
                              NDopsem.Terminator := ?tmn;
                              NDopsem.Locals := ?lc';
                              NDopsem.Allocas := ?als |} :: 
                              sbECs__ECs ?ecs;
             NDopsem.Globals := ?gl;
             NDopsem.FunTable := ?fs;
             NDopsem.Mem := ?M |} ?tr |- _ ] =>
    try solve [exists 
         {|
         SBnsop.CurSystem := s;
         SBnsop.CurTargetData := (los, nts);
         SBnsop.CurProducts := ps;
         SBnsop.ECS := {|
                SBnsop.CurFunction := f;
                SBnsop.CurBB := b;
                SBnsop.CurCmds := cs;
                SBnsop.Terminator := tmn;
                SBnsop.Locals := lc';
                SBnsop.Rmap := rm';
                SBnsop.Allocas := als |} :: ecs;
         SBnsop.Globals := gl;
         SBnsop.FunTable := fs;
         SBnsop.Mem := M;
         SBnsop.Mmap := Mmap0 |};
    exists tr; eauto];
    exists 
         {|
         SBnsop.CurSystem := s;
         SBnsop.CurTargetData := (los, nts);
         SBnsop.CurProducts := ps;
         SBnsop.ECS := {|
                SBnsop.CurFunction := f;
                SBnsop.CurBB := b;
                SBnsop.CurCmds := cs;
                SBnsop.Terminator := tmn;
                SBnsop.Locals := lc';
                SBnsop.Rmap := rm;
                SBnsop.Allocas := als |} :: ecs;
         SBnsop.Globals := gl;
         SBnsop.FunTable := fs;
         SBnsop.Mem := M;
         SBnsop.Mmap := Mmap0 |};
    exists tr; eauto
  end.

Ltac progress_tac := progress_tac_aux nil.

Lemma progress : forall S1,
  wf_State S1 -> 
  SBnsop.ns_isFinialState S1 = true \/ 
  (exists S2, exists tr, SBnsop.nsInsn S1 S2 tr) \/
  undefined_state S1.
Proof.
  intros S1 HwfS1.
  assert (Hllvm_progress := HwfS1).
  apply wf_sbState__wf_State in Hllvm_progress.
  apply ndopsem_pp.progress in Hllvm_progress.
  destruct Hllvm_progress as [His_final | [[S2 [tr Hstep]] | Hundef]];
    try solve [auto using llvm_isFinialState__sb_isFinialState |
               right; apply llvm_undef__sb_progress; auto].

  destruct S1 as [s [los nts] ps ecs gl fs M].
  destruct HwfS1 as [HwfMM1 [Hwfg1 [Hwfg1' [HwfSys1 [HmInS1 HwfECs]]]]].
  destruct ecs; try solve [inversion HwfECs].
  destruct e as [f b cs tmn lc rm als].
  destruct HwfECs as [[Hreach [HbInF [HfInPs [Hwflc [Hinscope [Hwfm [Hwfm'
                        [l1 [ps1 [cs1 Heq]]]]]]]]]]
                      [HwfECs HwfCall]].
  subst b. assert (Hstep':=Hstep).
  destruct cs.
  Case "cs=nil".
    destruct tmn; inv Hstep.
    SCase "tmn=ret".
      apply sbECs__ECs_cons_inv0 in H10.
      destruct H10 as [rm' [ecs0 [Heq1 Heq2]]]; subst.
      assert (exists rm'', SBnsop.returnUpdateLocals (los,nts) 
        c' t v lc lc' rm rm' gl = Some (lc'', rm'')) as Hretup.
        unfold SBnsop.returnUpdateLocals, returnResult.
        unfold NDopsem.returnUpdateLocals in H17.
        remember (NDopsem.getOperandValue (los, nts) v lc gl) as R. 
        destruct R; tinv H17.
        destruct c'; tinv H17.
        unfold prop_reg_metadata.
        remember (isPointerTypB t) as Hptr.
        destruct Hptr.
          destruct HwfECs as [[Hreach' 
              [HbInF' [HfInPs' [Hwflc' [Hinscope' [Hwfm1 [Hwfm1'
                [l1' [ps1' [cs1' Heq']]]]]]]]]] 
              [HwfECs HwfCall']]; subst.
          eapply wf_system__wf_cmd in HbInF'; eauto using in_middle.
          inv HbInF'. inv H5.
          destruct t; inv HeqHptr.
          assert (wf_insn nil s (module_intro layouts5 namedts5 products5) f 
            (block_intro l1 ps1 (cs1 ++ nil) 
               (insn_return i0 (typ_pointer t) v)) 
            (insn_terminator (insn_return i0 (typ_pointer t) v))) as Hwfc.
            eapply wf_system__wf_tmn in HbInF; eauto.
          assert (exists omd, 
            SBopsem.get_reg_metadata (layouts5, namedts5) gl rm v = 
            Some omd) as J2.
            eapply get_reg_metadata_isnt_stuck; 
              try solve [eauto | inv Hwfc; eauto].
          destruct J2 as [md J2]. rewrite J2. 
          destruct n; inv H17; eauto.
          destruct (isPointerTypB typ1); eauto.
          
          destruct n; inv H17; eauto.
          destruct t0; inv H0; eauto.
          destruct (isPointerTypB t0); eauto.
         
      destruct Hretup as [rm'' Hretup].
      right. left.
      exists (SBnsop.mkState s (los, nts) ps 
        ((SBnsop.mkEC F' B' cs' tmn' lc'' rm'' als')::ecs0) gl fs Mem' Mmap0).
      exists trace_nil.
      eauto.

    SCase "tmn=ret void".
      apply sbECs__ECs_cons_inv0 in H8.
      destruct H8 as [rm' [ecs0 [Heq1 Heq2]]]; subst.
      right. left.
      exists (SBnsop.mkState s (los, nts) ps 
        ((SBnsop.mkEC F' B' cs' tmn' lc' rm' als')::ecs0) gl fs Mem' Mmap0).
      exists trace_nil.
      eauto.  

    SCase "tmn=br".
      right. left.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists rm', SBnsop.switchToNewBasicBlock (los, nts) 
        (block_intro l' ps' cs' tmn') 
        (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l0 l2)) gl lc rm = 
          Some (lc', rm')) as Hswitch.
        unfold NDopsem.switchToNewBasicBlock in H19.
        remember (NDopsem.getIncomingValuesForBlockFromPHINodes 
          (los, nts) (getPHINodesFromBlock (block_intro l' ps' cs' tmn'))
          (block_intro l1 ps1 (cs1 ++ nil) (insn_br i0 v l0 l2)) gl lc) as R.
        destruct R; tinv H19.
        assert (exists RVs, 
           SBnsop.getIncomingValuesForBlockFromPHINodes (los, nts) ps'
             (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l0 l2)) gl lc rm =
           Some RVs /\
           matched_incoming_values l3 RVs) as J.
           assert (HwfB := HbInF).
           eapply wf_system__blockInFdefB__wf_block in HwfB; eauto.
           simpl_env in *.
           destruct (isGVZero (los, nts) c).
             assert (J:=H18).
             symmetry in J.
             apply lookupBlockViaLabelFromFdef_inv in J; auto.
             destruct J as [Heq J]; subst.
             eapply wf_system__lookup__wf_block in H18; eauto.
             inv H18. clear H9 H10.
             eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
               with (ps':=ps')(cs':=cs')(tmn':=tmn')(l0:=l'); eauto.
               exists nil. auto.

             assert (J:=H18).
             symmetry in J.
             apply lookupBlockViaLabelFromFdef_inv in J; auto.
             destruct J as [Heq J]; subst.
             eapply wf_system__lookup__wf_block in H18; eauto.
             inv H18. clear H9 H10.
             eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
               with (ps':=ps')(cs':=cs')(tmn':=tmn')(l0:=l'); eauto.
               exists nil. auto.
         
         destruct J as [RVs [J J']].
         unfold switchToNewBasicBlock. simpl.
         rewrite J. inv H19. apply llvm_sb_updateValuesForNewBlock; auto.

      destruct Hswitch as [rm' Hswitch].
      exists (mkState s (los, nts) ps 
              ((mkEC f (block_intro l' ps' cs' tmn') cs' tmn' lc' rm' als)
              ::ecs) gl fs M Mmap0).
      exists trace_nil. eauto.

    SCase "tmn=br_uncond".
      right. left.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists rm', switchToNewBasicBlock (los, nts) 
        (block_intro l' ps' cs' tmn') 
        (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l0)) gl lc rm = 
          Some (lc', rm')) as Hswitch.
        unfold NDopsem.switchToNewBasicBlock in H15.
        remember (NDopsem.getIncomingValuesForBlockFromPHINodes 
          (los, nts) (getPHINodesFromBlock (block_intro l' ps' cs' tmn'))
          (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l0)) gl lc) as R.
        destruct R; tinv H15.
        assert (exists RVs, 
           getIncomingValuesForBlockFromPHINodes (los, nts) ps'
             (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l0)) gl lc rm =
           Some RVs /\
           matched_incoming_values l2 RVs) as J.
           assert (HwfB := HbInF).
           eapply wf_system__blockInFdefB__wf_block in HwfB; eauto.
           eapply wf_system__lookup__wf_block in H14; eauto.
           inv H14. clear H9 H10.
           eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
             with (l0:=l'); eauto.      
             exists nil. auto.
         
         destruct J as [RVs [J J']].
         unfold switchToNewBasicBlock. simpl.
         rewrite J. inv H15. apply llvm_sb_updateValuesForNewBlock; auto.

      destruct Hswitch as [rm' Hswitch].
      exists (mkState s (los, nts) ps 
              ((mkEC f (block_intro l' ps' cs' tmn') cs' tmn' lc' rm' als)
              ::ecs) gl fs M Mmap0).
      exists trace_nil. eauto.

  Case "cs<>nil".
    assert (wf_insn nil s (module_intro los nts ps) f 
      (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) (insn_cmd c)) as Hwfc.
      assert (In c (cs1++c::cs)) as H. 
        apply in_or_app. simpl. auto.
      eapply wf_system__wf_cmd with (c:=c) in HbInF; eauto.
    right.
    destruct c; inv Hstep.

  SCase "c=bop". left. progress_tac.
  SCase "c=fbop". left. progress_tac.
  SCase "c=extractvalue". left. progress_tac.
  SCase "c=insertvalue". left. progress_tac.

  SCase "c=malloc". 
    left.
    assert (exists n, GV2int (los, nts) Size.ThirtyTwo gn = Some n) as H.
      clear - H21. unfold malloc in H21.
      destruct (GV2int (los, nts) Size.ThirtyTwo gn); inv H21; eauto.
    destruct H as [n H].
    progress_tac_aux (updateAddAL _ rm i0 (bound2MD mb tsz n)).

  SCase "free".  left. progress_tac.
      
  SCase "alloca".
    left.
    assert (exists n, GV2int (los, nts) Size.ThirtyTwo gn = Some n) as H.
      clear - H21. unfold malloc in H21.
      destruct (GV2int (los, nts) Size.ThirtyTwo gn); inv H21; eauto.
    destruct H as [n H].
    progress_tac_aux (updateAddAL _ rm i0 (bound2MD mb tsz n)).
      
  SCase "load".
    eapply load_progress; eauto.
    repeat (split; auto). eauto.

  SCase "store".
    eapply store_progress; eauto.
    repeat (split; auto). eauto.

  SCase "gep".
    left.
    assert (exists omd, SBopsem.get_reg_metadata (los, nts) gl rm v = 
      Some omd) as J4.
      eapply get_reg_metadata_isnt_stuck; try solve [eauto | inv Hwfc; eauto].
    destruct J4 as [md J4].
    progress_tac_aux (updateAddAL _ rm i0 md).

  SCase "trunc". left. progress_tac.
  SCase "ext". left. progress_tac.

  SCase "cast". 
    left.
    remember c as c'.
    destruct c; try solve [
      progress_tac; subst;
      eapply nsInsn_intro; try solve [
        eauto |
        eapply nsOtherCast; try solve [eauto | split; congruence]]].

    SSCase "case_inttoptr".
      subst. progress_tac_aux (updateAddAL _ rm i0 null_md).

    SSCase "case_bitcast".
      remember (isPointerTypB t) as R.
      destruct R.
      SSSCase "case_ptr".

        assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) as J.
          unfold NDopsem.CAST in H19. 
          destruct (NDopsem.getOperandValue (los, nts) v lc gl); eauto.
        destruct J as [gv J].
        assert (exists omd, SBopsem.get_reg_metadata (los, nts) gl rm v = 
          Some omd) as J4.
          eapply get_reg_metadata_isnt_stuck; eauto.
             inv Hwfc. inv H5; eauto.
        destruct J4 as [md J4].
        subst. progress_tac_aux (updateAddAL _ rm i0 md).

      SSSCase "case_nptr". subst. progress_tac.

  SCase "icmp". left. progress_tac.
  SCase "fcmp". left. progress_tac.

  SCase "select".
    left.
    remember (isPointerTypB t) as R.
    destruct R.
    SSCase "select_ptr".
      assert (exists omd, SBopsem.get_reg_metadata (los, nts) gl rm v0 = 
          Some omd) as J2.
        eapply get_reg_metadata_isnt_stuck; try solve [eauto | inv Hwfc; eauto].
      destruct J2 as [md0 J2].
      assert (exists omd, SBopsem.get_reg_metadata (los, nts) gl rm v1 = 
          Some omd) as J3.
        eapply get_reg_metadata_isnt_stuck; try solve [eauto | inv Hwfc; eauto].
      destruct J3 as [md1 J3].
      progress_tac_aux (if isGVZero (los, nts) c
                        then updateAddAL _ rm i0 md1
                        else updateAddAL _ rm i0 md0).

    SSCase "select_ptr". progress_tac.

  SCase "internal call".
    assert (exists gvss, params2GVs (los, nts) p lc gl rm = Some gvss /\
      matched_params gvs gvss) as G.
      eapply params2GVs_isnt_stuck; eauto. 
    destruct G as [gvss [G G']].
    eapply initLocal__total in H25; eauto.
    destruct H25 as [rm' H25].
    left.
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS :=(mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                       (block_intro l' ps' cs' tmn') cs' tmn' lc' rm'
                       nil)::
               {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_call i0 n c t v p :: cs) tmn;
                CurCmds := insn_call i0 n c t v p :: cs;
                Terminator := tmn;
                Locals := lc;
                Rmap := rm;
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M;
         Mmap := Mmap0 |}.
    exists trace_nil.
    eauto.    

  SCase "external call".
    eapply exCallUpdateLocals_isnt_stuck in H26; eauto.
    destruct H26 as [rm' H26].
    left. progress_tac_aux rm'.
Qed.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
