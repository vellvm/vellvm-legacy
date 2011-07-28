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
(*
Lemma params2GVs_inhabited : forall TD gl lc rm (Hwfc : wf_lc lc) lp gvs,
  SBnsop.params2GVs TD lp lc gl rm = Some gvs ->
  (forall gv omd, In (gv,omd) gvs -> Ensembles.Inhabited _ gv).
Proof.
  induction lp; simpl; intros gvs Hp2gv gv omd Hin.
    inv Hp2gv. inv Hin.

    destruct a. 
    remember (NDopsem.getOperandValue TD v lc gl) as R0.
    destruct R0; try solve [inv Hp2gv].
    remember (params2GVs TD lp lc gl rm) as R.
    destruct R; inv Hp2gv.
    destruct (isPointerTypB t); inv H0.
      simpl in Hin.
      destruct Hin as [Hin | Hin]; eauto.
        inv Hin.
        eapply getOperandValue__inhabited; eauto.

      simpl in Hin.
      destruct Hin as [Hin | Hin]; eauto.
        inv Hin.
        eapply getOperandValue__inhabited; eauto.
Qed.
*)

Fixpoint wf_params TD (gvs:list (GVs * option metadata)) (lp:params) : Prop :=
match (gvs, lp) with
| (nil, nil) => True
| ((gv,_)::gvs', (t, _)::lp') => wf_GVs TD gv t /\ wf_params TD gvs' lp'
| _ => False
end.

Lemma params2GVs_wf_gvs : forall los nts Ps F gl lc rm 
  (Hwfc : wf_lc (los,nts) F lc) S (Hwfg : wf_global (los, nts) S gl) tvs lp gvs,
  wf_value_list
          (make_list_system_module_fdef_value_typ
             (map_list_typ_value
                (fun (typ_' : typ) (value_'' : value) =>
                 (S, (module_intro los nts Ps), F, value_'', typ_'))
                tvs)) ->
  lp = map_list_typ_value
        (fun (typ_' : typ) (value_'' : value) => (typ_', value_''))
        tvs ->
  SBnsop.params2GVs (los,nts) lp lc gl rm = Some gvs -> 
  wf_params (los,nts) gvs lp.
Proof.
  induction tvs; intros lp gvs Hwfvs Heq Hp2gv; subst; simpl in *.
    inv Hp2gv. simpl. auto.

    remember (NDopsem.getOperandValue (los,nts) v lc gl) as R0.
    destruct R0; try solve [inv Hp2gv].
    remember (params2GVs (los,nts) (map_list_typ_value
                (fun (typ_' : typ) (value_'' : value) => (typ_', value_''))
                tvs) lc gl rm) as R.
    destruct R; inv Hp2gv.
    inv Hwfvs.
    destruct (isPointerTypB t); inv H0;
      split; eauto using getOperandValue__wf_gvs.
Qed.

Lemma initializeFrameValues__wf_lc_aux : forall los nts Ps s ifs fattr ft fid va 
  bs2 la2 la1 lc1 rm1
  (Huniq: uniqFdef (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2))
  (Hwflc: wf_lc (los,nts) 
     (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2) lc1) 
  lc2 gvs2 lp2 rm2,
  _initializeFrameValues (los,nts) la2 gvs2 lc1 rm1 = Some (lc2, rm2) -> 
  wf_params (los,nts) gvs2 lp2 ->
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2) 
    lc2.
Proof.
  induction la2; simpl; intros la1 lc1 rm1 Huniq HwfF Hwflc lc2 gvs2 lp2 rm2 Hin 
    Hpar.
    inv Hin. auto.

    destruct a. destruct p.
    destruct gvs2; simpl in *; subst.
      remember (_initializeFrameValues (los,nts) la2 nil lc1 rm1) as R1.
      destruct R1 as [[lc' rm']|]; tinv Hin.
      remember (gundef (los,nts) t) as R2.
      destruct R2; tinv Hin.
        assert (lc2=updateAddAL _ lc' i0 ($ g # t $)) as EQ.
          destruct (isPointerTypB t); inv Hin; auto.
        subst.
        apply wf_lc_updateAddAL with (t:=t); eauto.
          rewrite_env ((la1++[(t,a,i0)])++la2).
          eapply IHla2; simpl_env; eauto.

          inv HwfF.
          simpl. 
          destruct Huniq as [Huniq1 Huniq2].
          apply NoDup_split in Huniq2.
          destruct Huniq2 as [Huniq2 _].
          rewrite NoDup_lookupTypViaIDFromArgs; auto.

          inv HwfF.
          assert (In (t, a, i0)
            (map_list_typ_attributes_id
              (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) =>
              (typ_, attributes_, id_)) typ_attributes_id_list)) as J.
            rewrite <- H11.
            apply in_or_app; simpl; auto.
          apply wf_typ_list__in_args__wf_typ with (t:=t)(a:=a)(i0:=i0) in H12; 
            auto.
          apply feasible_typ_list__in_args__feasible_typ 
            with (t:=t)(a:=a)(i0:=i0) in H13; auto.
          inv H13.
          eapply gundef_cgv2gvs__wf_gvs; eauto.

      destruct p.
      remember (_initializeFrameValues (los,nts) la2 gvs2 lc1 rm1) as R1.
      destruct R1 as [[lc' rm']|]; tinv Hin.
      destruct lp2 as [|[]]; tinv Hpar.
      destruct Hpar as [Hwfg Hpar].
      assert (lc2=updateAddAL _ lc' i0 (lift_op1 (fit_gv (los, nts) t) g t)) 
        as EQ.
        destruct (isPointerTypB t); inv Hin; auto.
        destruct o; inv H0; auto.
      subst.
      apply wf_lc_updateAddAL with (t:=t); eauto.
        rewrite_env ((la1++[(t,a,i0)])++la2).
        eapply IHla2; simpl_env; eauto.
        
        inv HwfF.
        simpl. 
        destruct Huniq as [Huniq1 Huniq2].
        apply NoDup_split in Huniq2.
        destruct Huniq2 as [Huniq2 _].
        rewrite NoDup_lookupTypViaIDFromArgs; auto.
        
        inv HwfF.
        assert (In (t, a, i0)
          (map_list_typ_attributes_id
            (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) =>
            (typ_, attributes_, id_)) typ_attributes_id_list)) as J.
          rewrite <- H11.
          apply in_or_app; simpl; auto.
        apply wf_typ_list__in_args__wf_typ with (t:=t)(a:=a)(i0:=i0) in H12; 
          auto.
        apply feasible_typ_list__in_args__feasible_typ 
          with (t:=t)(a:=a)(i0:=i0) in H13; auto.
        inv H13.
        eapply lift_fit_gv__wf_gvs; eauto.
Qed.

Lemma initializeFrameValues__wf_lc : forall ifs s los nts Ps fattr ft fid la2 va 
  bs2 lc1 rm1
  (Huniq: uniqFdef (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  (Hwflc:wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2) 
    lc1) 
  lc2 gvs2 lp2 rm2,
  _initializeFrameValues (los,nts) la2 gvs2 lc1 rm1 = Some (lc2, rm2) -> 
  wf_params (los,nts) gvs2 lp2 ->
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2) lc2.
Proof.
  intros.  
  rewrite_env (nil++la2) in HwfF.
  rewrite_env (nil++la2) in Hwflc.
  rewrite_env (nil++la2).
  eapply initializeFrameValues__wf_lc_aux; eauto.
Qed.

Lemma initLocals__wf_lc : forall ifs s los nts Ps fattr ft fid la2 va 
  bs2
  (Huniq: uniqFdef (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  lc rm gvs2 lp2,
  initLocals (los,nts) la2 gvs2 = Some (lc, rm) -> 
  wf_params (los,nts) gvs2 lp2 ->
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2) lc.
Proof.
  intros. unfold initLocals in H. 
  eapply initializeFrameValues__wf_lc; eauto.
    intros x gvx tx J1 J2. inv J2.
Qed.

Lemma initLocals_spec : forall TD la gvs id1 lc rm,
  In id1 (getArgsIDs la) ->
  initLocals TD la gvs = Some (lc, rm) ->
  exists gv, lookupAL _ lc id1 = Some gv.
Proof.
  unfold initLocals.
  induction la; intros; simpl in *.
    inversion H.

    destruct a as [[t c] id0].  
    simpl in H.
    destruct H as [H | H]; subst; simpl.
      destruct gvs. 
        remember (_initializeFrameValues TD la nil nil nil) as R1.
        destruct R1 as [[lc' rm']|]; tinv H0.
        remember (gundef TD t) as R2.
        destruct R2; inv H0.
        destruct (isPointerTypB t); inv H1;
          exists ($ g # t $); apply lookupAL_updateAddAL_eq; auto.      

        destruct p.
        remember (_initializeFrameValues TD la gvs nil nil) as R1.
        destruct R1 as [[lc' rm']|]; tinv H0.
        assert (lc = updateAddAL _ lc' id1 (lift_op1 (fit_gv TD t) g t)) as EQ.
          destruct (isPointerTypB t); inv H0; auto.
          destruct o; inv H1; auto.
        subst.
        exists (lift_op1 (fit_gv TD t) g t). apply lookupAL_updateAddAL_eq; auto.

      destruct (eq_atom_dec id0 id1); subst.
        destruct gvs.
          remember (_initializeFrameValues TD la nil nil nil) as R1.
          destruct R1 as [[lc' rm']|]; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          destruct (isPointerTypB t); inv H2;
            exists ($ g # t $); apply lookupAL_updateAddAL_eq; auto.
              
          destruct p.
          remember (_initializeFrameValues TD la gvs nil nil) as R1.
          destruct R1 as [[lc' rm']|]; tinv H0.
          assert (lc = updateAddAL _ lc' id1 (lift_op1 (fit_gv TD t) g t)) as EQ.
            destruct (isPointerTypB t); inv H0; auto.
            destruct o; inv H2; auto.
          subst.
          exists (lift_op1 (fit_gv TD t) g t). 
          apply lookupAL_updateAddAL_eq; auto.      

        destruct gvs.
          remember (_initializeFrameValues TD la nil nil nil) as R1.
          destruct R1 as [[lc' rm']|]; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1]. 
          destruct (isPointerTypB t); inv H2;
            exists gv; rewrite <- lookupAL_updateAddAL_neq; auto.

          destruct p.
          remember (_initializeFrameValues TD la gvs nil nil) as R1.
          destruct R1 as [[lc' rm']|]; tinv H0.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1]. 
          assert (lc = updateAddAL _ lc' id0 (lift_op1 (fit_gv TD t) g t)) as EQ.
            destruct (isPointerTypB t); inv H0; auto.
            destruct o; inv H2; auto.
          subst.
          exists gv. rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma initLocals_spec' : forall fid fa rt la va lb gvs los nts ifs s lc Ps id1 t 
  lp rm
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hlk: lookupTypViaIDFromFdef (fdef_intro (fheader_intro fa rt fid la va) lb)
         id1 = ret t)
  (Hinit: initLocals (los,nts) la gvs = Some (lc, rm))
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

Lemma returnUpdateLocals__wf_lc : forall ifs los nts S F F' c Result lc lc' gl 
  lc'' Ps l1 ps1 cs1 tmn1 t B' rt rm rm' rm''
  (Hwfg: wf_global (los,nts) S gl) 
  (Hwfv: wf_value S (module_intro los nts Ps) F Result t),
  wf_lc (los,nts) F lc -> wf_lc (los,nts) F' lc' ->
  returnUpdateLocals (los,nts) c rt Result lc lc' rm rm' gl = 
    ret (lc'', rm'') ->
  uniqFdef F' ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F' = true -> 
  In c cs1 ->
  wf_insn ifs S (module_intro los nts Ps) F' B' (insn_cmd c) ->
  wf_lc (los,nts) F' lc''.
Proof.
  intros.
  unfold returnUpdateLocals, returnResult in H1.
  remember (NDopsem.getOperandValue (los,nts) Result lc gl) as R.
  destruct R; tinv H1.
  destruct (isPointerTypB rt).
    destruct (get_reg_metadata (los, nts) gl rm Result); tinv H1.
    destruct c; inv H1; auto.
    destruct n; inv H7; auto.
    destruct t0; tinv H6.
      assert (lc''=updateAddAL _ lc' i0 (lift_op1 (fit_gv (los, nts) t0) g t0)) 
        as EQ.
        destruct (isPointerTypB t0); inv H6; auto.
      subst.
      eapply wf_lc_updateAddAL with (t:=t0); eauto.
        eapply uniqF__lookupTypViaIDFromFdef; eauto.

        symmetry in HeqR.
        eapply getOperandValue__wf_gvs in HeqR; eauto.
        inv H5. inv H21. inv H12. inv H23.
        eapply lift_fit_gv__wf_gvs; eauto.

    destruct c; inv H1; auto.
    destruct n; inv H7; auto.
    destruct t0; tinv H6.
      assert (lc''=updateAddAL _ lc' i0 (lift_op1 (fit_gv (los, nts) t0) g t0)) 
        as EQ.
        destruct (isPointerTypB t0); inv H6; auto.
      subst.
      eapply wf_lc_updateAddAL with (t:=t0); eauto.
        eapply uniqF__lookupTypViaIDFromFdef; eauto.

        symmetry in HeqR.
        eapply getOperandValue__wf_gvs in HeqR; eauto.
        inv H5. inv H21. inv H12. inv H23.
        eapply lift_fit_gv__wf_gvs; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec2_aux : forall ifs s los nts Ps f
  b gl lc rm l3 cs tmn (Hwflc: wf_lc (los, nts) f lc) 
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f) ps2 ps1 rs,
  blockInFdefB (block_intro l3 (ps1++ps2) cs tmn) f ->
  wf_phinodes ifs s (module_intro los nts Ps) f 
    (block_intro l3 (ps1++ps2) cs tmn) ps2 ->
  Some rs = getIncomingValuesForBlockFromPHINodes (los, nts) ps2 b gl lc rm ->
  (forall id0 gvs omd0 t0, In (id0,gvs,omd0) rs -> 
     lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_GVs (los, nts) gvs t0).
Proof.    
  intros ifs s los nts Ps f b gl lc rm l3 cs tmn Hwflc Hwfg Huniq ps2 ps1 rs 
    Hbinf.
  assert (Huniq':=Hbinf).
  apply uniqFdef__uniqBlockLocs in Huniq'; auto.
  simpl in Huniq'. 
  apply NoDup_split in Huniq'.
  destruct Huniq' as [Huniq' _].
  generalize dependent rs.
  generalize dependent ps1.
  induction ps2; intros ps1 Hbinf Hnup rs Hwfps H id0 gv opmd0 t0 Hin Hlkup; 
    simpl in *.
    inv H. inv Hin.

    destruct a.
    remember (getValueViaBlockFromValuels l0 b) as R1.
    destruct R1; try solve [inversion H].   
      remember (NDopsem.getOperandValue (los,nts) v lc gl) as R.
      destruct R; tinv H.
      destruct (getIncomingValuesForBlockFromPHINodes (los,nts) ps2 b gl lc); 
        tinv H.
      assert (exists om, rs = (i0, g, om) :: l1) as EQ.
        destruct (isPointerTypB t); inv H; eauto.
        destruct (get_reg_metadata (los, nts) gl rm v); inv H1; eauto.
      destruct EQ as [om EQ]; subst.  
      inv Hwfps.
      simpl in Hin. 
      destruct Hin as [Hin | Hin]; eauto.
        inv Hin.
        inv H7.
        assert (J:=Hbinf).
        eapply lookupTypViaIDFromFdef__lookupTypViaIDFromPhiNodes in J; eauto.
          eapply wf_value_list__getValueViaBlockFromValuels__wf_value in H3; 
            eauto.
          simpl in J.
          rewrite NoDup_lookupTypViaIDFromPhiNodes in J; auto.
          inv J.
          symmetry in HeqR. eapply getOperandValue__wf_gvs in HeqR; eauto.

          simpl. rewrite getPhiNodesIDs_app.
          apply in_app_iff; simpl; auto.

        rewrite_env ((ps1 ++ [insn_phi i0 t l0]) ++ ps2) in H8.
        eapply IHps2 in H8; simpl_env; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec2 : forall ifs s los nts Ps f b 
  gl lc rm l3 cs tmn (Hwflc: wf_lc (los, nts) f lc) 
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f) ps rs,
  Some (block_intro l3 ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_global (los, nts) s gl ->
  wf_fdef ifs s (module_intro los nts Ps) f ->
  Some rs = getIncomingValuesForBlockFromPHINodes (los, nts) ps b gl lc rm ->
  (forall id0 gvs omd0 t0, In (id0,gvs,omd0) rs -> 
     lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_GVs (los, nts) gvs t0).
Proof.
  intros.
  assert (blockInFdefB (block_intro l3 ps cs tmn) f) as Hbinf.
    symmetry in H.
    apply lookupBlockViaLabelFromFdef_inv in H; auto.
    destruct H; eauto.
  eapply getIncomingValuesForBlockFromPHINodes_spec2_aux with (ps1:=nil); 
    eauto using wf_fdef__wf_phinodes.
Qed.

Lemma updateValuesForNewBlock_spec2 : forall TD f lc rm id1 gv t,
  lookupAL _ lc id1 = Some gv ->
  lookupTypViaIDFromFdef f id1 = Some t ->
  wf_lc TD f lc ->
  forall rs lc' rm', 
  (forall id0 gv omd t0, 
     In (id0,gv,omd) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_GVs TD gv t0) ->
  SBnsop.updateValuesForNewBlock rs lc rm = (lc', rm') ->
  exists t', exists gv', 
    lookupTypViaIDFromFdef f id1 = Some t' /\
    lookupAL _ lc' id1 = Some gv' /\
    wf_GVs TD gv' t'.
Proof.
  induction rs; intros; simpl in *.   
    inv H3.
    exists t. exists gv. eauto.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rs lc rm) as R.
    destruct R.
    destruct o; inv H3.
      destruct (id1==i0); subst.
        exists t. exists g. rewrite lookupAL_updateAddAL_eq; eauto.
        rewrite <- lookupAL_updateAddAL_neq; eauto.
      destruct (id1==i0); subst.
        exists t. exists g. rewrite lookupAL_updateAddAL_eq; eauto.
        rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma updateValuesForNewBlock_spec3 : forall TD f lc rm,
  wf_lc TD f lc ->
  forall rs lc' rm', 
  (forall id0 gv omd t0, 
     In (id0,gv,omd) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_GVs TD gv t0) ->
  updateValuesForNewBlock rs lc rm = (lc', rm') ->
  wf_lc TD f lc'.
Proof.  
  induction rs; intros; simpl in *; auto.
    inv H1. auto.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rs lc rm) as R.
    destruct R.
    intros x gvx tx Htyp Hlk.
    destruct o; inv H1.
      destruct (i0==x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk. inv Hlk. eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
        eapply IHrs in Hlk; eauto.
      destruct (i0==x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk. inv Hlk. eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
        eapply IHrs in Hlk; eauto.
Qed.

Lemma wf_lc_br_aux : forall ifs s los nts Ps f b1 b2 gl lc rm lc' rm' l3 
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f)
  (Hswitch : switchToNewBasicBlock (los, nts) b1 b2 gl lc rm = ret (lc', rm'))
  (Hlkup : Some b1 = lookupBlockViaLabelFromFdef f l3)
  (Hwfg : wf_global (los, nts) s gl)
  (HwfF : wf_fdef ifs s (module_intro los nts Ps) f)
  (Hwflc : wf_lc (los, nts) f lc),
  wf_lc (los, nts) f lc'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  remember (getIncomingValuesForBlockFromPHINodes (los, nts)
              (getPHINodesFromBlock b1) b2 gl lc rm) as R1.
  destruct R1; inv Hswitch.
  eapply updateValuesForNewBlock_spec3; eauto.
    destruct b1.
    eapply getIncomingValuesForBlockFromPHINodes_spec2; 
      eauto using lookupBlockViaLabelFromFdef_prop.
Qed.

(*********************************************)
(** * Preservation *)

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
  (EC : list SBnsop.ExecutionContext)
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 Mem': mem)
  (als : list mblock)
  id0 c0
  (Hid : Some id0 = getCmdID c0)
  t0
  (Htyp : Some t0 = getCmdTyp c0)
  (Hwfgv : wf_GVs (los,nts) gv3 t0)
  MM rm rm'
  (Hp1: wf_rmap F lc rm -> wf_rmap F (updateAddAL _ lc id0 gv3) rm')
  (Hp2 : wf_rmetadata (los, nts) Mem0 rm -> wf_rmetadata (los, nts) Mem' rm')
  (Hp3 : wf_mmetadata (los, nts) Mem0 MM -> wf_mmetadata (los, nts) Mem' MM)
  (Hp4 : wf_global_ptr S (los, nts) Mem0 gl -> 
         wf_global_ptr S (los, nts) Mem' gl)
  (Hp5 : wf_ECStack (los, nts) Mem0 Ps EC -> wf_ECStack (los, nts) Mem' Ps EC)
  (HwfS1 : wf_State
            {|
            SBnsop.CurSystem := S;
            SBnsop.CurTargetData := (los, nts);
            SBnsop.CurProducts := Ps;
            SBnsop.ECS := {|
                   SBnsop.CurFunction := F;
                   SBnsop.CurBB := B;
                   SBnsop.CurCmds := c0 :: cs;
                   SBnsop.Terminator := tmn;
                   SBnsop.Locals := lc;
                   SBnsop.Rmap := rm;
                   SBnsop.Allocas := als |} :: EC;
            SBnsop.Globals := gl;
            SBnsop.FunTable := fs;
            SBnsop.Mem := Mem0;
            SBnsop.Mmap := MM |}),
   wf_State
     {|
     SBnsop.CurSystem := S;
     SBnsop.CurTargetData := (los, nts);
     SBnsop.CurProducts := Ps;
     SBnsop.ECS := {|
            SBnsop.CurFunction := F;
            SBnsop.CurBB := B;
            SBnsop.CurCmds := cs;
            SBnsop.Terminator := tmn;
            SBnsop.Locals := updateAddAL _ lc id0 gv3;
            SBnsop.Rmap := rm';
            SBnsop.Allocas := als |} :: EC;
     SBnsop.Globals := gl;
     SBnsop.FunTable := fs;
     SBnsop.Mem := Mem';
     SBnsop.Mmap := MM |}.
Proof.
  intros.
  assert (Hwfc := HwfS1). apply wf_State__wf_cmd in Hwfc.
  destruct HwfS1 as 
    [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm [Hwfm' 
       [l3 [ps3 [cs3' Heq1]]]]]]]]]]
     [HwfEC HwfCall]]]]
    ]]]; subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0) 
    as R1. 
  assert (uniqFdef F) as HuniqF.
    eapply wf_system__uniqFdef; eauto.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      eapply wf_lc_updateAddAL; eauto.
        eapply uniqF__lookupTypViaIDFromFdef; eauto using in_middle.

      assert (Hid':=Hid).
      symmetry in Hid.
      apply getCmdLoc_getCmdID in Hid.
       subst.
      destruct cs; simpl_env in *.
      Case "1.1.1".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs3')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL with (t1:=t0) ; eauto.
          eapply uniqF__lookupTypViaIDFromFdef; eauto.
        
      Case "1.1.2".
        assert (NoDup (getCmdsLocs (cs3' ++ [c0] ++ [c] ++ cs))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL with (t1:=t0) ; eauto.
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
  (EC : list SBnsop.ExecutionContext)
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 Mem': mem)
  (als : list mblock)
  c0
  (Hid : getCmdID c0 = None)
  rm MM MM'
  (Hp1 : wf_rmetadata (los, nts) Mem0 rm -> wf_rmetadata (los, nts) Mem' rm)
  (Hp2 : wf_mmetadata (los, nts) Mem0 MM -> wf_mmetadata (los, nts) Mem' MM')
  (Hp3 : wf_global_ptr S (los, nts) Mem0 gl -> 
         wf_global_ptr S (los, nts) Mem' gl)
  (Hp4 : wf_ECStack (los, nts) Mem0 Ps EC -> wf_ECStack (los, nts) Mem' Ps EC)
  (HwfS1 : wf_State
            {|
            SBnsop.CurSystem := S;
            SBnsop.CurTargetData := (los, nts);
            SBnsop.CurProducts := Ps;
            SBnsop.ECS := {|
                   SBnsop.CurFunction := F;
                   SBnsop.CurBB := B;
                   SBnsop.CurCmds := c0 :: cs;
                   SBnsop.Terminator := tmn;
                   SBnsop.Locals := lc;
                   SBnsop.Rmap := rm;
                   SBnsop.Allocas := als |} :: EC;
            SBnsop.Globals := gl;
            SBnsop.FunTable := fs;
            SBnsop.Mem := Mem0;
            SBnsop.Mmap := MM |}),
   wf_State
     {|
     SBnsop.CurSystem := S;
     SBnsop.CurTargetData := (los, nts);
     SBnsop.CurProducts := Ps;
     SBnsop.ECS := {|
            SBnsop.CurFunction := F;
            SBnsop.CurBB := B;
            SBnsop.CurCmds := cs;
            SBnsop.Terminator := tmn;
            SBnsop.Locals := lc;
            SBnsop.Rmap := rm;
            SBnsop.Allocas := als |} :: EC;
     SBnsop.Globals := gl;
     SBnsop.FunTable := fs;
     SBnsop.Mem := Mem';
     SBnsop.Mmap := MM' |}.
Proof.
  intros.
  assert (Hwfc := HwfS1). apply wf_State__wf_cmd in Hwfc.
  destruct HwfS1 as 
    [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm [Hwfm'
       [l3 [ps3 [cs3' Heq1]]]]]]]]]]
     [HwfEC HwfCall]]]]
    ]]]; subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0) 
    as R1. 
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      destruct cs; simpl_env in *.
      Case "1.1.1".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs3')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        rewrite Hid in J2.
        eapply wf_defs_eq; eauto.
        
      Case "1.1.2".
        assert (NoDup (getCmdsLocs (cs3' ++ [c0] ++ [c] ++ cs))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        rewrite Hid in J2.
        eapply wf_defs_eq ; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
Qed.

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

Ltac preservation_tac HwfS1 :=
  eapply preservation_cmd_updated_case in HwfS1; simpl; try solve [
      eauto | 
      intro J;
      apply updateAddAL_nptr__wf_rmap; try solve [auto |
        apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1;
        rewrite HwfS1; simpl; try solve [auto | congruence]]
    ].

Lemma preservation : forall S1 S2 tr,
  SBnsop.nsInsn S1 S2 tr -> wf_State S1 -> wf_State S2.
Proof.
  intros S1 S2 tr HnsInsn HwfS1.
  (sb_nsInsn_cases (induction HnsInsn) Case); destruct TD as [los nts];
    try invert_prop_reg_metadata.
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
  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return rid RetTy Result))
             (insn_return rid RetTy Result)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split. eapply free_allocas_preserves_wf_mmetadata in H0; eauto.
  split; auto.
  split. eapply free_allocas_preserves_wf_global_ptr in H0; eauto.
  split; auto. 
  split; auto. 
  SCase "1".
    split; auto.
    split; auto.
    split; auto.
    split; auto.

    remember (getCmdID c') as R.
    destruct c'; try solve [inversion H].
    assert (In (insn_call i0 n c t v p) 
      (cs2'++[insn_call i0 n c t v p] ++ cs')) as HinCs.
      apply in_or_app. right. simpl. auto.
    assert (Hwfc := HBinF2).
    eapply wf_system__wf_cmd with (c:=insn_call i0 n c t v p) in Hwfc; eauto.
    assert (uniqFdef F') as HuniqF.
      eapply wf_system__uniqFdef; eauto.

    split.
      eapply wf_system__wf_tmn in HBinF1; eauto.
      inv HBinF1.
      eapply returnUpdateLocals__wf_lc with (Result:=Result)(lc:=lc); eauto.
    split.
    SSCase "1.1".
      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        assert (~ In (getCmdLoc (insn_call i0 n c t v p)) (getCmdsLocs cs2')) 
          as Hnotin.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          apply NoDupBlockLocs__notInCmds in HwfSystem; auto.       
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        unfold SBnsop.returnUpdateLocals, returnResult in H1.
        remember (NDopsem.getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].          
        destruct (isPointerTypB RetTy).        
          destruct (get_reg_metadata (los, nts) gl rm Result) as 
            [[md ?]|]; try solve [inv H1; auto].
          destruct R.
            destruct n; inv HeqR.
            destruct t; tinv H1.
            inv Hwfc.  inv H8. inv H17. inv H19.
            unfold SBopsem.prop_reg_metadata in H1.
            assert (wf_defs (layouts5, namedts5) F'
              (updateAddAL _ lc' i0 (lift_op1 (fit_gv (layouts5, namedts5) typ1)                 g typ1)) ids2) as J.
              eapply wf_defs_updateAddAL with (t1:=typ1);
                eauto using getOperandValue__inhabited.
                eapply uniqF__lookupTypViaIDFromFdef; eauto.
                eapply lift_fit_gv__wf_gvs; eauto.
                  eapply wf_system__wf_tmn in HBinF1; eauto.
                  inv HBinF1.
                  eapply getOperandValue__wf_gvs with (f:=F)(v:=Result); eauto.
            destruct typ1; inv H1; auto.

            destruct n; inv HeqR. inv H1.
            simpl in J2.
            eapply wf_defs_eq; eauto. 

          destruct R.
            destruct n; inv HeqR.
            destruct t; tinv H1.
            inv Hwfc.  inv H8. inv H17. inv H19.
            unfold SBopsem.prop_reg_metadata in H1.
            assert (wf_defs (layouts5, namedts5) F'
              (updateAddAL _ lc' i0 (lift_op1 (fit_gv (layouts5, namedts5) typ1)                 g typ1)) ids2) as J.
              eapply wf_defs_updateAddAL with (t1:=typ1);
                eauto using getOperandValue__inhabited.
                eapply uniqF__lookupTypViaIDFromFdef; eauto.
                eapply lift_fit_gv__wf_gvs; eauto.
                  eapply wf_system__wf_tmn in HBinF1; eauto.
                  inv HBinF1.
                  eapply getOperandValue__wf_gvs with (f:=F)(v:=Result); eauto.
            destruct typ1; inv H1; auto.

            destruct n; inv HeqR. inv H1.
            simpl in J2.
            eapply wf_defs_eq; eauto. 

      SSSCase "1.1.2".
        assert (NoDup (getCmdsLocs (cs2' ++ [insn_call i0 n c t v p] ++ [c0] ++ 
          cs'))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          apply NoDupBlockLocs__NoDupCmds in HwfSystem; auto.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        unfold SBnsop.returnUpdateLocals, returnResult in H1.
        remember (NDopsem.getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].          
        destruct (isPointerTypB RetTy).        
          destruct (get_reg_metadata (los, nts) gl rm Result) as 
            [[md ?]|]; try solve [inv H1; auto].
          destruct R.
            destruct n; inv HeqR.
            destruct t; tinv H1.
            inv Hwfc. inv H17. inv H8. inv H19.
            unfold SBnsop.prop_reg_metadata in H1.
            assert (wf_defs (layouts5, namedts5) F'
              (updateAddAL _ lc' i0 (lift_op1 (fit_gv (layouts5, namedts5) typ1)                 g typ1)) ids2) as J.
              eapply wf_defs_updateAddAL with (t1:=typ1);
                eauto using getOperandValue__inhabited.
                eapply uniqF__lookupTypViaIDFromFdef; eauto.
                eapply lift_fit_gv__wf_gvs; eauto.
                  eapply wf_system__wf_tmn in HBinF1; eauto.
                  inv HBinF1.
                  eapply getOperandValue__wf_gvs with (f:=F)(v:=Result); eauto.
            destruct typ1; inv H1; auto.

            destruct n; inv HeqR. inv H1.
            simpl in J2.
            eapply wf_defs_eq; eauto. 

          destruct R.
            destruct n; inv HeqR.
            destruct t; tinv H1.
            inv Hwfc. inv H17. inv H8. inv H19.
            unfold SBnsop.prop_reg_metadata in H1.
            assert (wf_defs (layouts5, namedts5) F'
              (updateAddAL _ lc' i0 (lift_op1 (fit_gv (layouts5, namedts5) typ1)                 g typ1)) ids2) as J.
              eapply wf_defs_updateAddAL with (t1:=typ1);
                eauto using getOperandValue__inhabited.
                eapply uniqF__lookupTypViaIDFromFdef; eauto.
                eapply lift_fit_gv__wf_gvs; eauto.
                  eapply wf_system__wf_tmn in HBinF1; eauto.
                  inv HBinF1.
                  eapply getOperandValue__wf_gvs with (f:=F)(v:=Result); eauto.
            destruct typ1; inv H1; auto.

            destruct n; inv HeqR. inv H1.
            simpl in J2.
            eapply wf_defs_eq; eauto. 

    split.
    SSCase "1.2".
      clear HeqR2 HwfCall HwfCall' HinCs Hreach2 HwfEC H0 Hwfg H Hreach1 HBinF1.
      clear HeqR1 Hinscope1 Hinscope2 HFinPs1 Hwfm1.
      eapply returnUpdateLocals__wf_rmap; eauto.

    split.
      assert (Hwfc' := HBinF1).
      eapply wf_system__wf_tmn in Hwfc'; eauto.
      clear - H0 Hwfm1' Hwfm2' H1 Hwfg' Hwfc'.
      inv Hwfc'.
      eapply returnUpdateLocals__wf_rmetadata; eauto.

    SSCase "1.3".
      exists l2. exists ps2. exists (cs2'++[insn_call i0 n c t v p]).   
      simpl_env. auto.
    split; auto.
      eapply free_allocas_preserves_wf_ECStack in H0; eauto.
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
  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return_void rid))
             (insn_return_void rid)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split. eapply free_allocas_preserves_wf_mmetadata in H0; eauto.
  split; auto.
  split. eapply free_allocas_preserves_wf_global_ptr in H0; eauto.
  split; auto.
  split; auto.
  SCase "1".
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.
    SSCase "1.1".
      apply HwfCall' in HBinF1. simpl in HBinF1.
      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        assert (~ In (getCmdLoc c') (getCmdsLocs cs2')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnotin H1.
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsLocs (cs2' ++ [c'] ++ [c] ++ cs'))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnodup H1.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto. 

    split; auto.
    split. eapply free_allocas_preserves_wf_rmetadata in H0; eauto.
    SSCase "1.3".
      exists l2. exists ps2. exists (cs2'++[c']).   
      simpl_env. auto.
    split; auto.
      eapply free_allocas_preserves_wf_ECStack in H0; eauto.
Unfocus.

Focus.
Case "nsBranch".
  destruct HwfS1 as 
    [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
       [l3 [ps3 [cs3' Heq1]]]]]]]]]]
     [HwfEC HwfCall]]]]
    ]]]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br bid Cond l1 l2))
             (insn_br bid Cond l1 l2)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
    assert (uniqFdef F) as HuniqF.
      eapply wf_system__uniqFdef in HwfSystem; eauto.   
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
    assert (blockInFdefB (block_intro l' ps' cs' tmn') F = true) as HBinF.
      clear - H0 HBinF1 HFinPs1 HmInS HwfSystem HuniqF H1.
      destruct (isGVZero (los, nts) c).
        symmetry in H1.
        apply lookupBlockViaLabelFromFdef_inv in H1; auto.
          destruct H1; auto.
        symmetry in H1.
        apply lookupBlockViaLabelFromFdef_inv in H1; auto.
          destruct H1; auto.
    split.
      clear - Hreach1 H0 HBinF1 HFinPs1 HmInS HwfSystem HuniqF H1.
      unfold isReachableFromEntry in *.
      destruct (isGVZero (los, nts) c).
        symmetry in H1.
        apply lookupBlockViaLabelFromFdef_inv in H1; eauto.
        destruct H1 as [H1 _].
        eapply reachable_successors; eauto.
          simpl. auto.
      
        symmetry in H1.
        apply lookupBlockViaLabelFromFdef_inv in H1; eauto.
        destruct H1 as [H1 _].
        eapply reachable_successors; eauto.
          simpl. auto.
    split; auto.
    split; auto.
    split.
      destruct (isGVZero (los, nts) c);
        eapply wf_lc_br_aux in H1; eauto.
    split.
      clear - H0 HeqR1 H1 H2 Hinscope1 H HwfSystem HBinF1 HwfF HuniqF Hwflc1 
        Hwfg.
      eapply inscope_of_tmn_br in HeqR1; eauto.
        destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
        destruct cs'; rewrite <- HeqR1; eauto.

        eapply switchToNewBasicBlock_sim; eauto.

    split.
      clear HwfEC Hreach1 HwfCall Hwfg HeqR1 Hinscope1 H Hwflc1.
      eapply switchToNewBasicBlock__wf_rmap with 
        (b1:=block_intro l' ps' cs' tmn')
        (b2:=block_intro l3 ps3 (cs3' ++ nil) (insn_br bid Cond l1 l2)); eauto.
    split; auto.
      eapply switchToNewBasicBlock__wf_rmetadata in H2; eauto.
      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Focus.
Case "nsBranch_uncond".
  destruct HwfS1 as 
    [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm' 
       [l3 [ps3 [cs3' Heq1]]]]]]]]]]
     [HwfEC HwfCall]]]]
    ]]]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br_uncond bid l0))
             (insn_br_uncond bid l0)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  SCase "1".
    assert (uniqFdef F) as HuniqF.
      eapply wf_system__uniqFdef in HwfSystem; eauto.   
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
    assert (H':=H).
    symmetry in H'.
    apply lookupBlockViaLabelFromFdef_inv in H'; auto.
    destruct H' as [EQ HBinF]; subst.
    split; auto.
    split.
      clear - Hreach1 HBinF1 HFinPs1 HmInS HwfSystem HuniqF HBinF.
      unfold isReachableFromEntry in *.
      eapply reachable_successors; eauto.
        simpl. auto.
    split; auto.
    split; auto.
    split. eapply wf_lc_br_aux in H0; eauto. 
    split.
      clear - H0 HeqR1 Hinscope1 HwfSystem HBinF1 HwfF HuniqF HBinF H Hwflc1 
        Hwfg.
      assert (Hwds := HeqR1).
      eapply inscope_of_tmn_br_uncond with (cs':=cs')(l':=l')(ps':=ps')
        (tmn':=tmn') in HeqR1; eauto.
        destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
        destruct cs'; rewrite <- HeqR1; eauto.

        eapply switchToNewBasicBlock_sim; eauto.

    split.
      clear HwfEC Hreach1 HwfCall Hwfg HeqR1 Hinscope1.
      eapply switchToNewBasicBlock__wf_rmap 
        with (b1:=block_intro l' ps' cs' tmn'); eauto.
    split.
      eapply switchToNewBasicBlock__wf_rmetadata in H0; eauto.
      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Case "nsBop". preservation_tac HwfS1.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  eapply BOP__wf_gvs with (v1:=v1); eauto.

Case "nsFBop". preservation_tac HwfS1. 
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  eapply FBOP__wf_gvs with (v1:=v1); eauto.

Case "nsExtractValue".
  assert (J':=HwfS1).
  destruct J' as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  eapply wf_system__wf_cmd with (c:=insn_extractvalue id0 t v idxs) in HBinF1; 
    eauto using in_middle.
  inv HBinF1.
  assert (exists t0, getSubTypFromConstIdxs idxs t = Some t0) as J.
    destruct H15 as [idxs0 [o [J1 J2]]].
    symmetry in J2.
    eapply mgetoffset__getSubTypFromConstIdxs in J2; eauto.
  destruct J as [t0 J].
  preservation_tac HwfS1. 
    destruct H15 as [idxs0 [o [J3 J4]]].
    symmetry in J4.
    eapply mgetoffset__getSubTypFromConstIdxs in J4; eauto.
    rewrite J in J4. inv J4.
    eapply getOperandValue__wf_gvs in H; eauto.
    eapply extractGenericValue__wf_gvs in H0; eauto. 
    eapply extractValue_preserves_wf_rmap; eauto.

Case "nsInsertValue". 
  preservation_tac HwfS1. 
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc.
    destruct H19 as [idxs0 [o [J3 J4]]].
    symmetry in J4.
    eapply mgetoffset__getSubTypFromConstIdxs in J4; eauto.
    eapply getOperandValue__wf_gvs in H; eauto.
    eapply getOperandValue__wf_gvs in H0; eauto.
    assert (J1:=H13). apply wf_value__wf_typ in H13. destruct H13.
    assert (J2:=H16). apply wf_value__wf_typ in H16. destruct H16.
    eapply insertGenericValue__wf_gvs in H1; eauto.
    eapply insertValue_preserves_wf_rmap with (gv:=gv); eauto.

Case "nsMalloc". 
  eapply preservation_cmd_updated_case with (rm':=
          updateAddAL _ rm id0 (bound2MD mb tsz n))
   in HwfS1; simpl; eauto.
    unfold blk2GV, ptr2GV, val2GV. simpl.
    eapply wf_GVs_intro; eauto.  
    unfold getTypeSizeInBits. simpl. eauto.
    intros gv Hin. inv Hin. auto.
    apply singleton_inhabited.

    apply updateAddAL_ptr__wf_rmap; auto. 
    eapply malloc_extends_wf_rmetadata; eauto.
    eapply malloc_extends_wf_mmetadata; eauto.
    eapply malloc_preserves_wf_global_ptr; eauto.
    eapply malloc_preserves_wf_ECStack; eauto.
Case "nsFree". 
  eapply preservation_cmd_non_updated_case with (MM':=MM) in HwfS1; eauto.
    eapply free_preserves_wf_rmetadata; eauto.
    eapply free_preserves_wf_mmetadata; eauto.
    eapply free_preserves_wf_global_ptr; eauto.
    eapply free_preserves_wf_ECStack; eauto.
Case "nsAlloca".
  eapply preservation_cmd_updated_case with (rm':=
          updateAddAL _ rm id0 (bound2MD mb tsz n))
   in HwfS1; simpl; eauto.
    unfold blk2GV, ptr2GV, val2GV. simpl.
    eapply wf_GVs_intro; eauto.  
    unfold getTypeSizeInBits. simpl. eauto.
    intros gv Hin. inv Hin. auto.
    apply singleton_inhabited.

    apply updateAddAL_ptr__wf_rmap; auto. 
    eapply malloc_extends_wf_rmetadata; eauto.
    eapply malloc_extends_wf_mmetadata; eauto.
    eapply malloc_preserves_wf_global_ptr; eauto.
    eapply malloc_preserves_wf_ECStack; eauto.
Case "nsLoad_nptr". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc.
    apply wf_value__wf_typ in H14. destruct H14.
    inv H5. inv H6. inv H17.
    eapply mload__getTypeSizeInBits in H3; eauto.
      destruct H3 as [sz [J1 J2]]. 
      eapply wf_GVs_intro; eauto.  
        unfold getTypeSizeInBits in J1.
        remember (getTypeSizeInBits_and_Alignment (los, nts) true t) as R.
        destruct R as [[]|]; inv J1.
        unfold getTypeSizeInBits_and_Alignment in HeqR.
        eapply gv2gvs__getTypeSizeInBits; eauto.

        apply gv2gvs__inhabited.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1.
      rewrite HwfS1; simpl; auto. 
        intros t0 EQ. inv EQ. inv H4.

Case "nsLoad_ptr".
  assert (J:=HwfS1).
  destruct J as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwfc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  eapply preservation_cmd_updated_case with (rm':=updateAddAL metadata rm id0
    (get_mem_metadata (los, nts) MM gvp)) in HwfS1; simpl; eauto.
    eapply wf_system__wf_cmd in HBinF1; eauto using in_middle.
    inv HBinF1.
    apply wf_value__wf_typ in H15. destruct H15.
    inv H5. inv H6. inv H18.
    eapply mload__getTypeSizeInBits in H5; eauto.
      destruct H5 as [sz [J1 J2]]. 
      eapply wf_GVs_intro; eauto.  
        unfold getTypeSizeInBits in J1.
        remember (getTypeSizeInBits_and_Alignment (los, nts) true t) as R.
        destruct R as [[]|]; inv J1.
        unfold getTypeSizeInBits_and_Alignment in HeqR.
        eapply gv2gvs__getTypeSizeInBits; eauto.

        apply gv2gvs__inhabited.

    apply updateAddAL_ptr__wf_rmap; auto. 
    apply get_mem_metadata__wf_rmetadata; auto.

Case "nsStore_nptr". 
  eapply preservation_cmd_non_updated_case with (MM':=MM) in HwfS1; eauto.
    eapply store_preserves_wf_rmetadata; eauto.
    eapply store_nptr_preserves_wf_mmetadata; eauto.
    eapply store_preserves_wf_global_ptr; eauto.
    eapply store_preserves_wf_ECStack; eauto.
Case "nsStore_ptr". 
  assert (J:=HwfS1).
  destruct J as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  eapply preservation_cmd_non_updated_case with 
    (MM':=set_mem_metadata (los, nts) MM gvp md') in HwfS1; eauto.
    eapply store_preserves_wf_rmetadata; eauto.
    eapply store_ptr_preserves_wf_mmetadata; eauto.
      eapply wf_system__wf_cmd with (c:=insn_store sid t v vp align0) in HBinF1; 
        eauto.
        inv HBinF1; eauto.
        apply in_or_app; simpl; auto.
    eapply store_preserves_wf_global_ptr; eauto.
    eapply store_preserves_wf_ECStack; eauto.
Case "nsGEP". 
  assert (J:=HwfS1).
  destruct J as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  eapply wf_system__wf_cmd with (c:=insn_gep id0 inbounds0 t vp idxs) in HBinF1;
    eauto using in_middle.
  inv HBinF1; eauto.
  eapply preservation_cmd_updated_case with 
    (rm':=updateAddAL _ rm id0 md) in HwfS1; simpl; eauto.
    eapply getOperandValue__wf_gvs in H0; eauto.
    assert (H1':=H1).
    eapply values2GVs__inhabited in H1; eauto.
    destruct H1 as [vidxs0 H1].
    eapply GEP__wf_gvs in H2; eauto. 

    apply updateAddAL_ptr__wf_rmap; auto.
    eapply prop_metadata_preserves_wf_rmetadata; eauto.

Case "nsTrunc".
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc.
    eapply TRUNC__wf_gvs; eauto.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. inv H6; congruence.
Case "nsExt". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc.
    eapply EXT__wf_gvs; eauto.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. inv H6; congruence.

Case "nsBitcast_nptr". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc.
    eapply CAST__wf_gvs; eauto.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. inv H7; try congruence.
          inv H0.
Case "nsBitcast_ptr". 
  assert (J:=HwfS1).
  destruct J as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  assert (Hwfc:=HwfS1). apply wf_State__wf_cmd in Hwfc.
  inv Hwfc.
  eapply preservation_cmd_updated_case with (rm':=updateAddAL metadata rm id0 md)
    in HwfS1; simpl; eauto.
    eapply CAST__wf_gvs; eauto.

    apply updateAddAL_ptr__wf_rmap; auto.
    eapply prop_metadata_preserves_wf_rmetadata with (t:=t1); eauto.
      inv H9; eauto.

Case "nsInttoptr". 
  eapply preservation_cmd_updated_case with (rm':=
    updateAddAL SBopsem.metadata rm id0 null_md) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc.
    eapply CAST__wf_gvs; eauto.

    apply updateAddAL_ptr__wf_rmap; auto.
    apply adding_null_preserves_wf_rmetadata; auto.
Case "nsOthercast". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc.
    eapply CAST__wf_gvs; eauto.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. 
        destruct H0 as [J1 J2]. 
        inv H7; try (congruence).
Case "nsIcmp". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].  
    inv Hwfc.
    eapply ICMP__wf_gvs with (v1:=v1); eauto.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. congruence.
Case "nsFcmp". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].  
    inv Hwfc.
    eapply FCMP__wf_gvs with (v1:=v1); eauto.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. congruence.
Case "nsSelect_nptr".
  assert (J:=HwfS1).
  apply wf_State__inv in J.
  destruct J as [Hwfg [Hwflc Hwfc]].
  inv Hwfc. 
  eapply getOperandValue__wf_gvs in H0; eauto.
  eapply getOperandValue__wf_gvs in H1; eauto.
  destruct (isGVZero (los, nts) c); 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; 
    try solve [
      eauto |
      intro J0;
      apply updateAddAL_nptr__wf_rmap; try solve [
        auto |
        apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1;
          rewrite HwfS1; simpl; try solve [auto | intros t0 EQ; inv EQ; inv H3]
      ]
    ].

Case "nsSelect_ptr".
  assert (J:=HwfS1).
  destruct J as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  assert (Hwfc:=HwfS1). apply wf_State__wf_cmd in Hwfc.
  inv Hwfc.
  eapply getOperandValue__wf_gvs in H0; eauto.
  eapply getOperandValue__wf_gvs in H1; eauto.
  destruct (isGVZero (los, nts) c); try invert_prop_reg_metadata.
    eapply preservation_cmd_updated_case with 
      (rm':=updateAddAL metadata rm id0 md2) in HwfS1; simpl; 
      try solve [eauto | apply updateAddAL_ptr__wf_rmap; auto |
        eapply prop_metadata_preserves_wf_rmetadata; eauto ].
    eapply preservation_cmd_updated_case with 
      (rm':=updateAddAL metadata rm id0 md1) in HwfS1; simpl; 
      try solve [eauto | apply updateAddAL_ptr__wf_rmap; auto |
        eapply prop_metadata_preserves_wf_rmetadata; eauto].

Focus.
Case "nsCall".
  assert (Hwfc:=HwfS1).
  apply wf_State__wf_cmd in Hwfc.
  destruct HwfS1 as 
    [HwfMM [Hwfg [Hwfg' [HwfSys [HmInS [
      [Hreach [HBinF [HFinPs [Hwflc [Hinscope [Hwfm1 [Hwfm2 
        [l1 [ps [cs'' Heq]]]]]]]]]]
      [HwfECs HwfCall]]]]]]]; subst.
  assert (InProductsB (product_fdef (fdef_intro 
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    apply ndopsem_dsop.lookupFdefViaPtr_inversion in H1.
    destruct H1 as [fn [H11 H12]].
    eapply lookupFdefViaIDFromProducts_inv; eauto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  SCase "1".     
    assert (uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb)) as Huniq.
      eapply wf_system__uniqFdef; eauto.
    assert (wf_fdef nil S (module_intro los nts Ps) 
      (fdef_intro (fheader_intro fa rt fid la va) lb)) as HwfF.
      eapply wf_system__wf_fdef; eauto.
    assert (wf_params (los,nts) ogvs lp) as JJ.
      eapply wf_system__wf_cmd in HBinF; eauto using in_middle.
      inv HBinF.
      eapply params2GVs_wf_gvs; eauto.

    split.
      simpl. eapply reachable_entrypoint; eauto.
    split.
      apply entryBlockInFdef in H2; auto.
    split; auto.
    split.
      eapply initLocals__wf_lc; eauto.
    split.
     assert (ps'=nil) as EQ.
       eapply entryBlock_has_no_phinodes with (ifs:=nil)(s:=S); eauto.        
     subst.
     apply dom_entrypoint in H2.
     eapply initLocals_params2GVs_sim in H4; eauto.
     destruct H4 as [gvs [J1 J2]]; subst.
     assert (ndopsem_pp.wf_params (los,nts) gvs lp) as JJ'.
       eapply wf_system__wf_cmd in HBinF; eauto using in_middle.
       inv HBinF.
       eapply ndopsem_pp.params2GVs_wf_gvs; eauto.
     destruct cs'.
       unfold inscope_of_tmn.
       remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
         !! l') as R.
       destruct R.
       eapply preservation_dbCall_case; eauto using ndopsem_pp.wf_params_spec.

       unfold inscope_of_cmd.
       remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
         !! l') as R.
       destruct R. simpl.
       destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n]; 
         try solve [contradict n; auto]. 
       eapply preservation_dbCall_case; eauto using ndopsem_pp.wf_params_spec.
    split.
      eapply initLocals__wf_rmap; eauto.
    split. 
      eapply initLocals__wf_rmetadata; eauto.
        inv Hwfc. clear - H23.
        apply wf_value_list__in_params__wf_value; eauto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
  split.
  SCase "2".
    repeat (split; auto). eauto.
  SCase "3".
    simpl. intros b HbInBs. destruct b.
    destruct t; auto.

Unfocus.

Case "nsExCall". 
  unfold exCallUpdateLocals in H2.
  destruct noret0.
    inv H5.

    eapply preservation_cmd_non_updated_case with (MM':=MM) in HwfS1; eauto.
      eapply callExternalFunction_preserves_wf_rmetadata; eauto.
      eapply callExternalFunction_preserves_wf_mmetadata; eauto.
      eapply callExternalFunction_preserves_wf_global_ptr; eauto.
      eapply callExternalFunction_preserves_wf_ECStack; eauto.

    destruct oresult; tinv H5.
    destruct ft; tinv H5.
    simpl in H5.
    remember (fit_gv (los, nts) ft g) as R.
    destruct R; tinv H5.
    assert (HwfS1':=HwfS1).
    apply wf_State__inv in HwfS1'.
    destruct HwfS1' as [_ [_ Hwfc]].
    inv Hwfc. inv H21. inv H12. inv H23.
    destruct typ1; inv H5; try solve [
      eapply preservation_cmd_updated_case with (rm':=rm') in HwfS1; 
        try solve [simpl; eauto |
          eapply fit_gv_gv2gvs__wf_gvs_aux; eauto |
          intro J0;
          apply updateAddAL_nptr__wf_rmap; try solve [auto |
            apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1;
            rewrite HwfS1; simpl; try solve [auto | congruence]] |
          eapply callExternalFunction_preserves_wf_rmetadata; eauto |
          eapply callExternalFunction_preserves_wf_mmetadata; eauto |
          eapply callExternalFunction_preserves_wf_global_ptr; eauto |
          eapply callExternalFunction_preserves_wf_ECStack; eauto
        ] |
      eapply preservation_cmd_updated_case with (Mem':=Mem')
        (rm':=updateAddAL metadata rm rid null_md) in HwfS1; 
        try solve [simpl; eauto | 
          eapply fit_gv_gv2gvs__wf_gvs_aux; eauto |
          intro J0; apply updateAddAL_ptr__wf_rmap; auto |
          intro G; apply adding_null_preserves_wf_rmetadata;
            eapply callExternalFunction_preserves_wf_rmetadata; eauto |
          eapply callExternalFunction_preserves_wf_mmetadata; eauto |
          eapply callExternalFunction_preserves_wf_global_ptr; eauto |
          eapply callExternalFunction_preserves_wf_ECStack; eauto
        ]
    ].
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
  l1 ps1 cs1 tmn1 Mem
  (Hwfgptr : wf_global_ptr s (los,nts) Mem gl)
  (Hwfg : wf_global (los,nts) s gl)
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : wf_defs (los,nts) f lc t)
  (HuniqF : uniqFdef f)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  ps2
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 cs1 tmn1) f = true)
  (HwfB : wf_block nil s (module_intro los nts ps) f 
             (block_intro l1 ps1 cs1 tmn1))
  (H8 : wf_phinodes nil s (module_intro los nts ps) f
         (block_intro l0 ps' cs' tmn') ps2)
  (Hsucc : In l0 (successors_terminator tmn1))
  rm (Hwfm: wf_rmap f lc rm)
  (Hin: exists ps1, ps' = ps1 ++ ps2),
   exists RVs : list (id * GVs * option metadata),
     getIncomingValuesForBlockFromPHINodes (los, nts) ps2 
       (block_intro l1 ps1 cs1 tmn1) gl lc rm =
       ret RVs.
Proof.
  intros.
  induction ps2; simpl.
    exists nil. auto.
  
    destruct a. inv H8. inv H6.
    assert (exists v, getValueViaLabelFromValuels l2 l1 = Some v) as J.      
      clear - H14 HbInF HuniqF Hsucc.
      inv H14.
      unfold check_list_value_l in H0.
      remember (split (unmake_list_value_l l2)) as R.
      destruct R.
      destruct H0 as [J1 [J2 J3]].
      eapply In__getValueViaLabelFromValuels; eauto.
      destruct J2 as [_ J2].
      apply J2.
      eapply successors_predOfBlock; eauto.

    destruct J as [v J].
    rewrite J.
    assert (HwfV:=J).
    eapply wf_value_list__getValueViaLabelFromValuels__wf_value in HwfV; eauto.
    destruct v as [vid | vc].
    Case "vid".
      assert (exists gv1, lookupAL _ lc vid = Some gv1) as J1.
        Focus.
        destruct H14 as [Hwfops Hwfvls].             
        assert (Hnth:=J).
        eapply getValueViaLabelFromValuels__nth_list_value_l in Hnth; eauto.
        destruct Hnth as [n Hnth].
        eapply wf_phi_operands__elim in Hwfops; eauto.
        destruct Hwfops as [Hneqid [vb [b1 [Hlkvb [Hlkb1 Hdom]]]]].
        assert (b1 = block_intro l1 ps1 cs1 tmn1) 
          as EQ.
          clear - Hlkb1 HbInF HuniqF.
          apply blockInFdefB_lookupBlockViaLabelFromFdef in HbInF; auto.
          rewrite HbInF in Hlkb1. inv Hlkb1; auto.

        subst.
        clear - Hdom Hinscope HeqR J Hreach H2 HbInF Hlkvb Hlkb1 HuniqF.
        destruct Hdom as [J3 | J3]; try solve [contradict Hreach; auto].
        clear Hreach.        
        unfold blockDominates in J3.         
        destruct vb.
        unfold inscope_of_tmn in HeqR.
        destruct f. destruct f.
        remember ((dom_analyze (fdef_intro (fheader_intro f t2 i0 a v) b)) !! l1)
          as R1.
        destruct R1.
        symmetry in HeqR.    
        apply fold_left__spec in HeqR.
        destruct (eq_atom_dec l3 l1); subst.
        SCase "l3=l1".
          destruct HeqR as [HeqR _].
          assert (In vid t) as G.
            clear - J HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
            assert (J':=Hlkvb).
            apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
            apply lookupBlockViaLabelFromFdef_inv in Hlkb1; auto.
            destruct Hlkb1 as [J1 J2].
            eapply blockInFdefB_uniq in J2; eauto.
            destruct J2 as [J2 [J4 J5]]; subst.
            apply lookupBlockViaIDFromFdef__InGetBlockIDs in J'.
            simpl in J'.
            apply HeqR.
            rewrite_env ((getPhiNodesIDs ps1 ++ getCmdsIDs cs1)++getArgsIDs a).
            apply in_or_app; auto.       
          apply wf_defs_elim with (id1:=vid) in Hinscope; auto.
          destruct Hinscope as [? [gv1 [? [Hinscope ?]]]].
          exists gv1. auto.

        SCase "l3<>l1".
          assert (In l3 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as G.
            apply ListSet.set_diff_intro; auto.
              simpl. intro JJ. destruct JJ as [JJ | JJ]; auto.
          assert (
            lookupBlockViaLabelFromFdef 
              (fdef_intro (fheader_intro f t2 i0 a v) b) l3 = 
              ret block_intro l3 p c t1) as J1.
            clear - Hlkvb HuniqF.
            apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
            apply blockInFdefB_lookupBlockViaLabelFromFdef in Hlkvb; auto.
          destruct HeqR as [_ [HeqR _]].
          apply HeqR in J1; auto.
          assert (In vid t) as InVid.
            clear - J1 HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
            apply J1.
            apply lookupBlockViaIDFromFdef__InGetBlockIDs in Hlkvb; auto.
          apply wf_defs_elim with (id1:=vid) in Hinscope; auto.
          destruct Hinscope as [? [gv1 [? [Hinscope ?]]]].
          exists gv1. auto.
        Unfocus.
  
      destruct J1 as [gv1 J1].
      simpl. rewrite J1.
      apply IHps2 in H7.
        destruct H7 as [RVs H7].
        rewrite H7. 
        remember (isPointerTypB t0) as R.
        destruct R; eauto.
          inv HwfV. 
          destruct t0; try solve [inversion HeqR0].
          assert(exists md, lookupAL metadata rm vid = Some md) as J2.
            eapply Hwfm; eauto.
          destruct J2 as [md J2].
          rewrite J2. eauto.
  
        destruct Hin as [ps3 Hin]. subst.
        exists (ps3++[insn_phi i0 t0 l2]).
        simpl_env. auto.
  
    Case "vc".
      simpl. inv HwfV.
      destruct (@const2GV_isnt_stuck (los,nts) s gl vc t0); auto.
      rewrite H.
      apply IHps2 in H7; eauto.
        destruct H7 as [RVs H7].
        rewrite H7. 
        remember (get_const_metadata vc) as R.
        destruct R as [[bc ec]|].
          eapply get_const_metadata_isnt_stuck in H; eauto.
          destruct H as [blk [bofs [eofs [Hc1 Hc2]]]].
          rewrite Hc1. rewrite Hc2.
          destruct (isPointerTypB t0); eauto.
            destruct (zeq blk blk); try solve [contradict n; auto].
            destruct (eq_nat_dec 31 31); 
              try solve [contradict n; auto | simpl; eauto].

          destruct (isPointerTypB t0); eauto.

        destruct Hin as [ps3 Hin]. subst.
        exists (ps3++[insn_phi i0 t0 l2]).
        simpl_env. auto.
Qed.

Lemma params2GVs_isnt_stuck : forall
  p22
  (s : system)
  los nts
  (ps : list product)
  (f : fdef)
  (i0 : id)
  n c t v p2
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVsMap)
  (gl : GVMap)
  (Hwfg1 : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system nil s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f
             (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn) f =
          true)
  (l0 : list atom)
  (HeqR : ret l0 =
         inscope_of_cmd f
           (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn)
           (insn_call i0 n c t v p2))
  (Hinscope : wf_defs (los,nts) f lc l0)
  rm (Hwfm : wf_rmap f lc rm)
  (Hex : exists p21, p2 = p21 ++ p22),
  exists gvs, params2GVs (los, nts) p22 lc gl rm = Some gvs.
Proof.
  induction p22; intros; simpl; eauto.

    destruct a.
    destruct Hex as [p21 Hex]; subst.
    assert (exists gv, NDopsem.getOperandValue (los, nts) v0 lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl. unfold valueInParams. right. 
        assert (J:=@in_split_r _ _ (p21 ++ (t0, v0) :: p22) (t0, v0)).
        remember (split (p21 ++ (t0, v0) :: p22)) as R.
        destruct R.
        simpl in J. apply J.
        apply In_middle.
    destruct J as [gv J]. 
    rewrite J.         
    eapply IHp22 in HbInF; eauto.  
      destruct HbInF as [vidxs HbInF].
      rewrite HbInF.
      remember (isPointerTypB t0) as R.
      destruct R; eauto.

      exists (p21 ++ [(t0,v0)]). simpl_env. auto.
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

Lemma initializeFrameValues__total_aux : forall los nts Ps s ifs fattr ft fid va 
  bs2 la2 la1 lc1 rm1
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2))
  gvs2,
  exists re, _initializeFrameValues (los,nts) la2 gvs2 lc1 rm1 = Some re.
Proof.
  induction la2; simpl in *; intros.
    eauto.

    destruct a. destruct p.
    assert (HwfF':=HwfF).
    simpl_env in HwfF'.
    rewrite_env ((la1 ++ [(t, a, i0)]) ++ la2) in HwfF'.
    inv HwfF.
    assert (In (t, a, i0)
            (map_list_typ_attributes_id
              (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) =>
              (typ_, attributes_, id_)) typ_attributes_id_list)) as JJ.
    rewrite <- H11.
    apply in_or_app; simpl; auto.
    apply wf_typ_list__in_args__wf_typ with (t:=t)(a:=a)(i0:=i0) in H12; 
      auto.
    apply feasible_typ_list__in_args__feasible_typ with (t:=t)(a:=a)(i0:=i0) 
      in H13; auto.   
    destruct gvs2.
      apply IHla2 with (gvs2:=nil)(lc1:=lc1)(rm1:=rm1) in HwfF'.
      destruct HwfF' as [[lc2 rm2] J].
      rewrite J. 
      apply gundef__total' in H13. 
      destruct H13 as [gv H13]. rewrite H13.
      destruct (isPointerTypB t); eauto.

      destruct p.
      apply IHla2 with (gvs2:=gvs2)(lc1:=lc1)(rm1:=rm1) in HwfF'.
      destruct HwfF' as [[lc2 rm2] J].
      rewrite J. inv H13.
      destruct (isPointerTypB t); eauto.
      destruct o; eauto.
Qed.

Lemma initLocal__total : forall los nts Ps s ifs fattr ft fid va bs2 la2  
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  gvs2,
  exists re, initLocals (los,nts) la2 gvs2 = Some re.
Proof.
  intros.
  unfold initLocals.
  eapply initializeFrameValues__total_aux with (la1:=nil); eauto.
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

Hint Constructors SBnsop.nsInsn.

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

Lemma progress : forall S1,
  wf_State S1 -> 
  SBnsop.ns_isFinialState S1 = true \/ 
  (exists S2, exists tr, SBnsop.nsInsn S1 S2 tr) \/
  undefined_state S1.
Proof.
  intros S1 HwfS1.
  destruct S1 as [s [los nts] ps ecs gl fs M].
  destruct HwfS1 as [HwfMM1 [Hwfg1 [Hwfg1' [HwfSys1 [HmInS1 HwfECs]]]]].
  destruct ecs; try solve [inversion HwfECs].
  destruct e as [f b cs tmn lc rm als].
  destruct HwfECs as [[Hreach [HbInF [HfInPs [Hwflc [Hinscope [Hwfm [Hwfm'
                        [l1 [ps1 [cs1 Heq]]]]]]]]]]
                      [HwfECs HwfCall]].
  subst b.
  destruct cs.
  Case "cs=nil".
    remember (inscope_of_tmn f (block_intro l1 ps1 (cs1 ++ nil) tmn) tmn) as R.
    destruct R; try solve [inversion Hinscope].
    destruct tmn.
    SCase "tmn=ret".
      simpl in HwfCall.
      destruct ecs.
        simpl; auto.      

        right.
        destruct e as [f' b' cs' tmn' lc' rm' als'].
        assert (J:=HbInF).
        apply HwfCall in J. clear HwfCall.
        destruct cs'; try solve [inversion J].
        destruct c; try solve [inversion J]. clear J.
        remember (free_allocas (los,nts) M als) as Rm.
        destruct Rm as [M' |]; try solve [undefbehave].
        left. symmetry in HeqRm.
        rename HeqRm into J.
        assert (exists lc'', exists rm'', SBnsop.returnUpdateLocals (los,nts) 
            (insn_call i1 n c t0 v0 p) t v lc lc' rm rm' gl = 
            Some (lc'',rm'')) as Hretup.
          unfold SBnsop.returnUpdateLocals, returnResult.
          assert (exists gv : GVs, 
            NDopsem.getOperandValue (los, nts) v lc gl = ret gv) as H.
            eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
              simpl. auto.
          destruct H as [gv H]. rewrite H.
          unfold SBnsop.prop_reg_metadata.   
          destruct HwfECs as [[Hreach' 
              [HbInF' [HfInPs' [Hwflc' [Hinscope' [Hwfm1 [Hwfm1'
                [l1' [ps1' [cs1' Heq']]]]]]]]]] 
              [HwfECs HwfCall]]; subst.
          eapply wf_system__wf_cmd in HbInF'; eauto using in_middle.
          inv HbInF'. inv H6.       
          remember (isPointerTypB t) as Hptr.
          destruct Hptr.
            destruct t; inv HeqHptr.
            assert (wf_insn nil s (module_intro layouts5 namedts5 products5) f 
              (block_intro l1 ps1 (cs1 ++ nil) 
                 (insn_return i0 (typ_pointer t) v)) 
              (insn_terminator (insn_return i0 (typ_pointer t) v))) as Hwfc.
              eapply wf_system__wf_tmn in HbInF; eauto.
            assert (exists omd, 
              SBopsem.get_reg_metadata (layouts5, namedts5) gl rm v = Some omd) 
              as J2.
              eapply get_reg_metadata_isnt_stuck; 
                try solve [eauto | inv Hwfc; eauto].
            destruct J2 as [md J2]. rewrite J2. 
            destruct n; eauto.
            destruct (isPointerTypB typ1); eauto.

            destruct n; eauto. 
            destruct (isPointerTypB typ1); eauto.
         
        destruct Hretup as [lc'' [rm'' Hretup]].
        exists (SBnsop.mkState s (los, nts) ps 
           ((SBnsop.mkEC f' b' cs' tmn' lc'' rm'' als')::ecs) gl fs M' Mmap0).
        exists trace_nil.
        eauto. 

    SCase "tmn=ret void".
      simpl in HwfCall.
      destruct ecs.
        simpl; auto.      

        right.
        destruct e as [f' b' cs' tmn' lc' rm' als'].
        assert (J:=HbInF).
        apply HwfCall in J. clear HwfCall.
        destruct cs'; try solve [inversion J].
        destruct c; try solve [inversion J]. clear J.
        remember (free_allocas (los,nts) M als) as Rm.
        destruct Rm as [M' |]; try solve [undefbehave].
        symmetry in HeqRm.
        rename HeqRm into J.
        destruct n; try solve [undefbehave].
        left.
        exists (SBnsop.mkState s (los, nts) ps 
          ((SBnsop.mkEC f' b' cs' tmn' lc' rm' als')::ecs) gl fs M' Mmap0).
        exists trace_nil.
        eauto.  

    SCase "tmn=br".
      right. left.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists cond, NDopsem.getOperandValue (los,nts) v lc gl = Some cond)
        as Hget.
        eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
          simpl. auto.
      destruct Hget as [cond Hget].
      assert (Hwfc := HbInF).
      eapply wf_system__wf_tmn in Hwfc; eauto.
      assert (exists c, c @ cond) as Hinh.
        inv Hwfc. 
        eapply getOperandValue__inhabited in Hget; eauto.
        inv Hget. eauto.
      destruct Hinh as [c Hinh].
      assert (exists l', exists ps', exists cs', exists tmn',
              Some (block_intro l' ps' cs' tmn') = 
              (if isGVZero (los,nts) c
                 then lookupBlockViaLabelFromFdef f l3
                 else lookupBlockViaLabelFromFdef f l2)) as HlkB.
        eapply wf_system__wf_tmn in HbInF; eauto.
        inv HbInF. 
        destruct block1 as [l2' ps2 cs2 tmn2].
        destruct block2 as [l3' ps3 cs3 tmn3].
        destruct (isGVZero (los, nts) c).
          exists l3'. exists ps3. exists cs3. exists tmn3.
          rewrite H11. auto.

          exists l2'. exists ps2. exists cs2. exists tmn2.
          rewrite H10. auto.

      destruct HlkB as [l' [ps' [cs' [tmn' HlkB]]]].
      assert (exists lc', exists rm', SBnsop.switchToNewBasicBlock (los, nts) 
        (block_intro l' ps' cs' tmn') 
        (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l2 l3)) gl lc rm = 
          Some (lc', rm')) as Hswitch.
         assert (exists RVs, 
           SBnsop.getIncomingValuesForBlockFromPHINodes (los, nts) ps'
             (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l2 l3)) gl lc rm =
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
             inv HlkB. clear H9 H10.
             eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
               with (ps':=ps')(cs':=cs')(tmn':=tmn')(l0:=l'); eauto.
               apply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1)
                 (tmn:=insn_br i0 v l2 l'); simpl; auto.
               simpl. auto.    
               exists nil. auto.

             assert (J:=HlkB).
             symmetry in J.
             apply lookupBlockViaLabelFromFdef_inv in J; auto.
             destruct J as [Heq J]; subst.
             eapply wf_system__lookup__wf_block in HlkB; eauto.
             inv HlkB. clear H9 H10.
             eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
               with (ps':=ps')(cs':=cs')(tmn':=tmn')(l0:=l'); eauto.
               apply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1)
                 (tmn:=insn_br i0 v l' l3); simpl; auto.
               simpl. auto.    
               exists nil. auto.
         
         destruct J as [RVs J].
         unfold switchToNewBasicBlock. simpl.
         rewrite J. destruct (updateValuesForNewBlock RVs lc rm); eauto.

      destruct Hswitch as [lc' [rm' Hswitch]].
      exists (mkState s (los, nts) ps 
              ((mkEC f (block_intro l' ps' cs' tmn') cs' tmn' lc' rm' als)
              ::ecs) gl fs M Mmap0).
      exists trace_nil. eauto.

    SCase "tmn=br_uncond".
      right. left.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists ps', exists cs', exists tmn',
        Some (block_intro l2 ps' cs' tmn') = lookupBlockViaLabelFromFdef f l2) 
          as HlkB.
        eapply wf_system__wf_tmn in HbInF; eauto.
        inv HbInF.        
        exists ps1. exists (cs1++nil). exists (insn_br_uncond i0 l2).
        rewrite H6. 
        apply lookupBlockViaLabelFromFdef_inv in H6; auto.
        destruct H6 as [H6 _]; subst. auto.

      destruct HlkB as [ps' [cs' [tmn' HlkB]]].

      assert (exists lc', exists rm', switchToNewBasicBlock (los, nts) 
        (block_intro l2 ps' cs' tmn') 
        (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc rm = 
          Some (lc', rm')) as Hswitch.
         assert (exists RVs, 
           getIncomingValuesForBlockFromPHINodes (los, nts) ps'
             (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc rm =
           Some RVs) as J.
           assert (HwfB := HbInF).
           eapply wf_system__blockInFdefB__wf_block in HwfB; eauto.
           eapply wf_system__lookup__wf_block in HlkB; eauto.
           inv HlkB. clear H9 H10.
           eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
             with (l0:=l2); eauto.      
             apply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1++nil)
               (tmn:=insn_br_uncond i0 l2); simpl; auto.
             simpl. auto.
             exists nil. auto.
         
         destruct J as [RVs J].
         unfold switchToNewBasicBlock. simpl.
         rewrite J. 
         destruct (updateValuesForNewBlock RVs lc rm). eauto.

      destruct Hswitch as [lc' [rm' Hswitch]].
      exists (mkState s (los, nts) ps 
              ((mkEC f (block_intro l2 ps' cs' tmn') cs' tmn' lc' rm' als)
              ::ecs) gl fs M Mmap0).
      exists trace_nil. eauto.

    SCase "tmn=unreachable".
      undefbehave.

  Case "cs<>nil".
    assert (wf_insn nil s (module_intro los nts ps) f 
      (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) (insn_cmd c)) as Hwfc.
      assert (In c (cs1++c::cs)) as H. 
        apply in_or_app. simpl. auto.
      eapply wf_system__wf_cmd with (c:=c) in HbInF; eauto.
    remember (inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c) as R.
    destruct R; try solve [inversion Hinscope].
    right.
    destruct c.
  SCase "c=bop". 
    left.
    assert (exists gv3, NDopsem.BOP (los,nts) lc gl b s0 v v0 = Some gv3) 
      as Hinsn_bop.
      unfold NDopsem.BOP.      
      assert (exists gv, NDopsem.getOperandValue (los, nts)v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, NDopsem.getOperandValue (los, nts) v0 lc gl = Some gv) 
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
          destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0. eauto.
    destruct Hinsn_bop as [gv3 Hinsn_bop].
    exists 
         {|
         SBnsop.CurSystem := s;
         SBnsop.CurTargetData := (los, nts);
         SBnsop.CurProducts := ps;
         SBnsop.ECS := {|
                SBnsop.CurFunction := f;
                SBnsop.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_bop i0 b s0 v v0 :: cs) tmn;
                SBnsop.CurCmds := cs;
                SBnsop.Terminator := tmn;
                SBnsop.Locals := (updateAddAL _ lc i0 gv3);
                SBnsop.Rmap := rm;
                SBnsop.Allocas := als |} :: ecs;
         SBnsop.Globals := gl;
         SBnsop.FunTable := fs;
         SBnsop.Mem := M;
         SBnsop.Mmap := Mmap0 |}.
     exists trace_nil. eauto.

  SCase "c=fbop". 
    left.
    assert (exists gv3, NDopsem.FBOP (los,nts) lc gl f0 f1 v v0 = Some gv3) 
      as Hinsn_fbop.
      unfold NDopsem.FBOP.      
      assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, NDopsem.getOperandValue (los, nts) v0 lc gl = Some gv) 
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0. 
      eauto.

    destruct Hinsn_fbop as [gv3 Hinsn_fbop].
    exists 
         {|
         SBnsop.CurSystem := s;
         SBnsop.CurTargetData := (los, nts);
         SBnsop.CurProducts := ps;
         SBnsop.ECS := {|
                SBnsop.CurFunction := f;
                SBnsop.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_fbop i0 f0 f1 v v0 :: cs) tmn;
                SBnsop.CurCmds := cs;
                SBnsop.Terminator := tmn;
                SBnsop.Locals := (updateAddAL _ lc i0 gv3);
                SBnsop.Rmap := rm;
                SBnsop.Allocas := als |} :: ecs;
         SBnsop.Globals := gl;
         SBnsop.FunTable := fs;
         SBnsop.Mem := M;
         SBnsop.Mmap := Mmap0 |}.
     exists trace_nil. eauto.

  SCase "c=extractvalue".
    left.
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', NDopsem.extractGenericValue (los, nts) t gv l2 
      = Some gv') as J'.
      unfold NDopsem.extractGenericValue.
      inv Hwfc. destruct H13 as [idxs [o [J1 J2]]].
      rewrite J1. rewrite J2. eauto.
    destruct J' as [gv' J'].
    exists {|
         SBnsop.CurSystem := s;
         SBnsop.CurTargetData := (los, nts);
         SBnsop.CurProducts := ps;
         SBnsop.ECS := {|
                SBnsop.CurFunction := f;
                SBnsop.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_extractvalue i0 t v l2 :: cs) tmn;
                SBnsop.CurCmds := cs;
                SBnsop.Terminator := tmn;
                SBnsop.Locals := (updateAddAL _ lc i0 gv');
                SBnsop.Rmap := rm;
                SBnsop.Allocas := als |} :: ecs;
         SBnsop.Globals := gl;
         SBnsop.FunTable := fs;
         SBnsop.Mem := M;
         SBnsop.Mmap := Mmap0|}.
     exists trace_nil. eauto.

  SCase "c=insertvalue".
    left.
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', NDopsem.getOperandValue (los, nts) v0 lc gl = Some gv') 
      as J'.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J' as [gv' J'].
    assert (exists gv'', NDopsem.insertGenericValue (los, nts) t gv l2 t0 gv' = 
      Some gv'') as J''.
      unfold NDopsem.insertGenericValue.
      inv Hwfc. destruct H16 as [idxs [o [J1 J2]]].
      rewrite J1. rewrite J2. eauto.
    destruct J'' as [gv'' J''].
    exists 
         {|
         SBnsop.CurSystem := s;
         SBnsop.CurTargetData := (los, nts);
         SBnsop.CurProducts := ps;
         SBnsop.ECS := {|
                SBnsop.CurFunction := f;
                SBnsop.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_insertvalue i0 t v t0 v0 l2 :: cs) tmn;
                SBnsop.CurCmds := cs;
                SBnsop.Terminator := tmn;
                SBnsop.Locals := (updateAddAL _ lc i0 gv'');
                SBnsop.Rmap := rm;
                SBnsop.Allocas := als |} :: ecs;
         SBnsop.Globals := gl;
         SBnsop.FunTable := fs;
         SBnsop.Mem := M;
         SBnsop.Mmap := Mmap0 |}.
     exists trace_nil. eauto.

  SCase "c=malloc". 
    inv Hwfc. inv H12.
    apply feasible_typ_inv'' in H.
    destruct H as [ssz [asz [J1 J2]]].
    assert (exists gns, NDopsem.getOperandValue (los, nts) v lc gl = Some gns) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gns J].
    assert (exists gn, gn @ gns) as Hinh.
      eapply getOperandValue__inhabited in J; eauto.
      inv J. eauto.
    destruct Hinh as [gn Hinh].
    remember (malloc (los, nts) M asz gn a) as R.
    destruct R as [[M' mb] |].
      left.
      assert (exists n, GV2int (los, nts) Size.ThirtyTwo gn = Some n) as H.
        clear - HeqR0. unfold malloc in HeqR0.
        destruct (GV2int (los, nts) Size.ThirtyTwo gn); inv HeqR0; eauto.
      destruct H as [n H].
      remember (prop_reg_metadata lc rm i0 
        ($(blk2GV (los, nts) mb) # typ_pointer t$) (bound2MD mb asz n)) as R.
      destruct R as [lc' rm'].
      exists 
         {|
         SBnsop.CurSystem := s;
         SBnsop.CurTargetData := (los, nts);
         SBnsop.CurProducts := ps;
         SBnsop.ECS := {|
                SBnsop.CurFunction := f;
                SBnsop.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_malloc i0 t v a :: cs) tmn;
                SBnsop.CurCmds := cs;
                SBnsop.Terminator := tmn;
                SBnsop.Locals := lc';
                SBnsop.Rmap := rm';
                SBnsop.Allocas := als |} :: ecs;
         SBnsop.Globals := gl;
         SBnsop.FunTable := fs;
         SBnsop.Mem := M';
         SBnsop.Mmap := Mmap0 |}.
      exists trace_nil.
      eauto.
      
      unfold undefined_state.
      right. rewrite J. rewrite J2. right. right. right. left.
      exists gn. rewrite <- HeqR0. undefbehave.

  SCase "free". 
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) as 
      J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gv, gv @ gvs) as Hinh.
      inv Hwfc.
      eapply getOperandValue__inhabited in J; eauto.
      inv J. eauto.
    destruct Hinh as [gv Hinh].
    remember (free (los, nts) M gv) as R.
    destruct R as [M'|].
      left.
      exists 
         {|
         SBnsop.CurSystem := s;
         SBnsop.CurTargetData := (los, nts);
         SBnsop.CurProducts := ps;
         SBnsop.ECS := {|
                SBnsop.CurFunction := f;
                SBnsop.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_free i0 t v :: cs) tmn;
                SBnsop.CurCmds := cs;
                SBnsop.Terminator := tmn;
                SBnsop.Locals := lc;
                SBnsop.Rmap := rm;
                SBnsop.Allocas := als |} :: ecs;
         SBnsop.Globals := gl;
         SBnsop.FunTable := fs;
         SBnsop.Mem := M';
         SBnsop.Mmap := Mmap0 |}.
      exists trace_nil.
      eauto.      
      
      unfold undefined_state.
      right. rewrite J. right. right. right. right. left. 
      exists gv. rewrite <- HeqR0. undefbehave.

  SCase "alloca".
    inv Hwfc. inv H12.
    apply feasible_typ_inv'' in H.
    destruct H as [ssz [asz [J1 J2]]].
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gns J].
    assert (exists gn, gn @ gns) as Hinh.
      eapply getOperandValue__inhabited with (t:=typ_int Size.ThirtyTwo) 
        (f:=f) in J; eauto.
      inv J. eauto.
    destruct Hinh as [gn Hinh].
    remember (malloc (los, nts) M asz gn a) as R.
    destruct R as [[M' mb] |].
      assert (exists n, GV2int (los, nts) Size.ThirtyTwo gn = Some n) as H.
        clear - HeqR0. unfold malloc in HeqR0.
        destruct (GV2int (los, nts) Size.ThirtyTwo gn); inv HeqR0; eauto.
      destruct H as [n H].
      remember (prop_reg_metadata lc rm i0 
        ($(blk2GV (los, nts) mb) # typ_pointer t$) (bound2MD mb asz n)) as R.
      destruct R as [lc' rm'].
      left.
      exists 
         {|
         SBnsop.CurSystem := s;
         SBnsop.CurTargetData := (los, nts);
         SBnsop.CurProducts := ps;
         SBnsop.ECS := {|
                SBnsop.CurFunction := f;
                SBnsop.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_alloca i0 t v a :: cs) tmn;
                SBnsop.CurCmds := cs;
                SBnsop.Terminator := tmn;
                SBnsop.Locals := lc';
                SBnsop.Rmap := rm';
                SBnsop.Allocas := (mb::als) |} :: ecs;
         SBnsop.Globals := gl;
         SBnsop.FunTable := fs;
         SBnsop.Mem := M';
         SBnsop.Mmap := Mmap0 |}.
      exists trace_nil.
      eauto.
      
      right.
      unfold undefined_state.
      right. rewrite J. rewrite J2. right. right. left. exists gn.
      rewrite <- HeqR0. undefbehave.

  SCase "load".
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists omd, SBopsem.get_reg_metadata (los, nts) gl rm v = 
      Some omd) as J2.
      eapply get_reg_metadata_isnt_stuck; try solve [eauto | inv Hwfc; eauto].
    destruct J2 as [md J2].
    assert (exists gv, gv @ gvs) as Hinh.
      inv Hwfc.
      eapply getOperandValue__inhabited in J; eauto.
      inv J. eauto.
    destruct Hinh as [gv Hinh].
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
            remember (SBnsop.prop_reg_metadata lc rm i0 ($ gv' # t $) 
              (SBopsem.get_mem_metadata (los, nts) Mmap0 gv)) as R.
            destruct R as [lc' rm'].
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
                  SBnsop.Locals := lc';
                  SBnsop.Rmap := rm';
                  SBnsop.Allocas := als |} :: ecs;
               SBnsop.Globals := gl;
               SBnsop.FunTable := fs;
               SBnsop.Mem := M;
               SBnsop.Mmap := Mmap0 |}.
            exists trace_nil. eauto.

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
            exists trace_nil. eauto.

        SSSSCase "~valid block".
          right.
          unfold undefined_state. unfold other_load_violation.
          right. rewrite J. right. right. right. right. left.
          exists gv. rewrite R3. rewrite Hflat. undefbehave.

      SSSCase "align fails".
        right.
        unfold undefined_state. unfold other_load_violation.
        right. rewrite J. right. right. right. right. left.
        exists gv. rewrite R3. rewrite Hflat. undefbehave.

    SSCase "assert fails".
      right.
      unfold undefined_state. unfold spatial_memory_violation.
      right. rewrite J. rewrite J2. right. right. right. right. right. right. 
      right. exists gv. undefbehave.

  SCase "store".
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gv, NDopsem.getOperandValue (los, nts) v0 lc gl = Some gv) 
      as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [mgvs J0].
    inv Hwfc.
    assert (exists omd, SBopsem.get_reg_metadata (los, nts) gl rm v0 = 
      Some omd) as J2.
      eapply get_reg_metadata_isnt_stuck; try solve [eauto | inv Hwfc; eauto].
    destruct J2 as [md J2].
    assert (exists gv, gv @ gvs) as Hinh1.
      eapply getOperandValue__inhabited in J; eauto.
      inv J. eauto.
    destruct Hinh1 as [gv Hinh1].
    assert (exists mgv, mgv @ mgvs) as Hinh2.
      eapply getOperandValue__inhabited in J0; eauto.
      inv J0. eauto.
    destruct Hinh2 as [mgv Hinh2].
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
            eauto.

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
            eauto.

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

  SCase "gep".
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [mp J].
    assert (exists vidxs, NDopsem.values2GVs (los, nts) l2 lc gl = Some vidxs) 
      as J2.
      eapply values2GVs_isnt_stuck; eauto.
        exists Nil_list_value. auto.
    destruct J2 as [vidxs J2].
    assert (exists mp', NDopsem.GEP (los, nts) t mp vidxs i1 = Some mp') as J3.
      unfold NDopsem.GEP. eauto.
    destruct J3 as [mp' J3].
    left.
    assert (exists omd, SBopsem.get_reg_metadata (los, nts) gl rm v = 
      Some omd) as J4.
      eapply get_reg_metadata_isnt_stuck; try solve [eauto | inv Hwfc; eauto].
    destruct J4 as [md J4].
    remember (prop_reg_metadata lc rm i0 mp' md) as R.
    destruct R as [lc' rm'].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M;
         Mmap := Mmap0 |}.
    exists trace_nil. eauto.

  SCase "trunc".
    left.
    assert (exists gv2, NDopsem.TRUNC (los,nts) lc gl t t0 v t1 = Some gv2) 
      as Hinsn_trunc.
      unfold NDopsem.TRUNC.      
      assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J. eauto.

    destruct Hinsn_trunc as [gv2 Hinsn_trunc].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_trunc i0 t t0 v t1 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Rmap := rm;
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M;
         Mmap := Mmap0 |}.
     exists trace_nil. eauto.

  SCase "ext".
    left.
    assert (exists gv2, NDopsem.EXT (los,nts) lc gl e t v t0 = Some gv2) 
      as Hinsn_ext.
      unfold NDopsem.EXT.      
      assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J. eauto.

    destruct Hinsn_ext as [gv2 Hinsn_ext].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_ext i0 e t v t0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Rmap := rm;
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M;
         Mmap := Mmap0 |}.
     exists trace_nil. eauto.

  SCase "cast". 
    left.
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv2, NDopsem.CAST (los,nts) lc gl c t v t0 = Some gv2) 
      as Hinsn_cast.
      unfold NDopsem.CAST.      
      rewrite J. eauto.
        
    destruct Hinsn_cast as [gv2 Hinsn_cast].
    remember c as c'.
    destruct c; try solve [
      exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_cast i0 c' t v t0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Rmap := rm;
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M;
         Mmap := Mmap0 |};
       exists trace_nil; subst; eapply nsOtherCast; 
         try solve [eauto | split; congruence]].

    SSCase "case_inttoptr".
      remember (prop_reg_metadata lc rm i0 gv2 null_md) as R.
      destruct R as [lc' rm'].
      exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_cast i0 c' t v t0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M;
         Mmap := Mmap0 |}.
       exists trace_nil. subst. eauto.

    SSCase "case_bitcast".
      remember (isPointerTypB t) as R.
      destruct R.
      SSSCase "case_ptr".

        assert (exists omd, SBopsem.get_reg_metadata (los, nts) gl rm v = 
          Some omd) as J4.
          eapply get_reg_metadata_isnt_stuck; eauto.
             inv Hwfc. inv H5; eauto.
        destruct J4 as [md J4].
        remember (prop_reg_metadata lc rm i0 gv2 md) as R.
        destruct R as [lc' rm'].
        exists 
           {|
           CurSystem := s;
           CurTargetData := (los, nts);
           CurProducts := ps;
           ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_cast i0 c' t v t0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: ecs;
           Globals := gl;
           FunTable := fs;
           Mem := M;
           Mmap := Mmap0 |}.
         exists trace_nil. subst. eauto.

      SSSCase "case_nptr".
        exists 
           {|
           CurSystem := s;
           CurTargetData := (los, nts);
           CurProducts := ps;
           ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_cast i0 c' t v t0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Rmap := rm;
                Allocas := als |} :: ecs;
           Globals := gl;
           FunTable := fs;
           Mem := M;
           Mmap := Mmap0 |}.
         exists trace_nil. subst. eauto.

  SCase "icmp".
    left.
    assert (exists gv2, NDopsem.ICMP (los,nts) lc gl c t v v0 = Some gv2) 
      as Hinsn_icmp.
      unfold NDopsem.ICMP.      
      assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, NDopsem.getOperandValue (los, nts) v0 lc gl = Some gv) 
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0. eauto.

    destruct Hinsn_icmp as [gv2 Hinsn_icmp].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_icmp i0 c t v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Rmap := rm;
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M;
         Mmap := Mmap0 |}.
     exists trace_nil. eauto.

  SCase "fcmp".
    left.
    assert (exists gv2, NDopsem.FCMP (los,nts) lc gl f0 f1 v v0 = Some gv2) 
      as Hinsn_fcmp.
      unfold NDopsem.FCMP.      
      assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, NDopsem.getOperandValue (los, nts) v0 lc gl = Some gv) 
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0. eauto.

    destruct Hinsn_fcmp as [gv2 Hinsn_fcmp].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_fcmp i0 f0 f1 v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Rmap := rm;
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M;
         Mmap := Mmap0 |}.
     exists trace_nil. eauto.

  SCase "select".
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [cond J].
    assert (exists c, c @ cond) as Hinh.
      inv Hwfc.
      eapply getOperandValue__inhabited in J; eauto.
      inv J. eauto.
    destruct Hinh as [c Hinh].
    assert (exists gv0, NDopsem.getOperandValue (los, nts) v0 lc gl = Some gv0) 
      as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [gv0 J0].
    assert (exists gv1, NDopsem.getOperandValue (los, nts) v1 lc gl = Some gv1) 
      as J1.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J1 as [gv1 J1].
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
      remember (if isGVZero (los, nts) c then 
                  prop_reg_metadata lc rm i0 gv1 md1
                else
                  prop_reg_metadata lc rm i0 gv0 md0) as R.
      destruct R as [lc' rm'].
      exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_select i0 v t v0 v1 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M;
         Mmap := Mmap0 |}.
       exists trace_nil. eauto.

    SSCase "select_ptr".
      exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_select i0 v t v0 v1 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (if isGVZero (los, nts) c
                           then updateAddAL _ lc i0 gv1 
                           else updateAddAL _ lc i0 gv0);
                Rmap := rm;
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M;
         Mmap := Mmap0 |}.
       exists trace_nil. eauto.

  SCase "call". 
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [fptrs J].
    assert (exists fptr, fptr @ fptrs) as Hinh.
      inv Hwfc.
      eapply getOperandValue__inhabited in J; eauto.
      inv J. eauto.
    destruct Hinh as [fptr Hinh].
    remember (lookupFdefViaPtr ps fs fptr) as Hlk. 
    destruct Hlk as [f' |].
    SSCase "internal call".
    assert (exists gvs, params2GVs (los, nts) p lc gl rm = Some gvs) as G.
      eapply params2GVs_isnt_stuck; eauto. 
        exists nil. auto.
    destruct G as [gvs G].
    destruct f' as [[fa rt fid la va] lb].
    assert (J1:=HeqHlk).
    symmetry in J1.
    apply ndopsem_dsop.lookupFdefViaPtr_inversion in J1; auto.
    destruct J1 as [fn [Hlkft J1]].
    apply lookupFdefViaIDFromProducts_inv in J1; auto.
    eapply wf_system__wf_fdef in J1; eauto.
    assert (Hinit := J1).
    apply initLocal__total with (gvs2:=gvs) in Hinit; auto.
    destruct Hinit as [[lc' rm'] Hinit].
    inv J1. destruct block5 as [l5 ps5 cs5 tmn5].
    left.
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS :=(mkEC (fdef_intro (fheader_intro fa rt fid
                        (map_list_typ_attributes_id
                         (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) 
                         => (typ_, attributes_, id_)) typ_attributes_id_list)
                        va) lb) 
                       (block_intro l5 ps5 cs5 tmn5) cs5 tmn5 
                       lc' rm'
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

    remember (lookupExFdecViaPtr ps fs fptr) as Helk. 
    destruct Helk as [f' |].
    SSCase "external call".
    assert (exists gvs, NDopsem.params2GVs (los, nts) p lc gl = Some gvs) 
      as G.
      eapply ndopsem_pp.params2GVs_isnt_stuck; eauto. 
        exists nil. auto.
    destruct G as [gvss G].
    assert (exists gvs, gvs @@ gvss) as G'.
      inv Hwfc.
      eapply params2GVs_inhabited in G; eauto.
    destruct G' as [gvs G']. 
    destruct f' as [[fa rt fid la va]].
    remember (callExternalFunction M fid gvs) as R.
    destruct R as [[oresult Mem']|].
      remember (exCallUpdateLocals (los, nts) t n i0 oresult lc rm) as R'.
      destruct R' as [[lc' rm']|].
        left.
        exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS :={|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_call i0 n c t v p :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := Mem';
         Mmap := Mmap0 |}.
        exists trace_nil.
        eauto.

        right.
        unfold undefined_state.
        right. right. right. right. right. right. right. 
        rewrite J. left. exists fptr. rewrite <- HeqHlk. rewrite <- HeqHelk. 
        rewrite G. split; auto. exists gvs. 
        rewrite <- HeqR0. rewrite <- HeqR'. undefbehave.

      right.
      unfold undefined_state.
      right. rewrite J. right. right. right. right. right. right. left.
      exists fptr. rewrite <- HeqHlk. rewrite <- HeqHelk. rewrite G. 
      split; auto. exists gvs.  rewrite <- HeqR0. undefbehave.

   SSCase "stuck".
     right.
     unfold undefined_state.
     right. rewrite J. right. right. right. right. right. right. left.
     exists fptr. rewrite <- HeqHlk. rewrite <- HeqHelk. split; auto. 
Qed.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
