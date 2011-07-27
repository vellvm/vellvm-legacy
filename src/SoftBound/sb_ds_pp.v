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
Require Import sb_ds_def.
Require Import sbop_dsop.
Require Import Znumtheory.
Require Import sb_ds_metadata.

Export LLVMwf.
Export AtomSet.
Export LLVMgv.
Export SBopsem.

(*****************************************)
(* Definitions *)

Definition wf_rmap (f:fdef) (lc:GVMap) (rm:rmetadata) : Prop :=
forall id1 gv1 t1, 
  lookupAL _ lc id1 = Some gv1 -> 
  lookupTypViaIDFromFdef f id1 = Some (typ_pointer t1) ->
  exists md, lookupAL _ rm id1 = Some md.

Definition wf_ExecutionContext TD M (ps:list product) (ec:ExecutionContext) 
  : Prop :=
let '(SBopsem.mkEC f b cs tmn lc rm als) := ec in
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

Definition wf_call (ec:SBopsem.ExecutionContext) (ecs:SBopsem.ECStack) 
  : Prop :=
let '(SBopsem.mkEC f _ _ _ _ _ _) := ec in
forall b, blockInFdefB b f ->
let '(block_intro _ _ _ tmn) := b in
match tmn with
| insn_return _ _ _ | insn_return_void _ =>
    match ecs with
    | nil => True
    | SBopsem.mkEC f' b' (insn_call _ _ _ _ _ _ ::_) tmn' lc' rm' als'::ecs' =>
        True
    | _ => False
    end
| _ => True
end.

Fixpoint wf_ECStack TD M (ps:list product) (ecs:SBopsem.ECStack) : Prop :=
match ecs with
| nil => False
| ec::ecs' => 
    wf_ExecutionContext TD M ps ec /\ wf_ECStack TD M ps ecs' /\ wf_call ec ecs'
end.

Definition wf_State (S:SBopsem.State) : Prop :=
let '(SBopsem.mkState s (los, nts) ps ecs gl _ M MM) := S in
wf_mmetadata (los, nts) M MM /\
wf_global (los, nts) s gl /\
wf_global_ptr s (los, nts) M gl /\
wf_system nil s /\
moduleInSystemB (module_intro los nts ps) s = true /\
wf_ECStack (los, nts) M ps ecs.

Lemma wf_State__inv : forall S los nts Ps F B c cs tmn lc rm als EC gl fs Mem0 
    MM0,
  wf_State (mkState S (los,nts) Ps
              ((mkEC F B (c::cs) tmn lc rm als)::EC) gl fs Mem0 MM0) ->
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
  remember (getOperandValue (los, nts) Result lc gl) as R1.
  destruct R1; inv H1.
  destruct (isPointerTypB rt).
    remember (get_reg_metadata (los, nts) gl rm Result) as R3.
    destruct R3 as [[md ?]|]; inv H0.
    destruct c'; inv H1; auto.
    destruct n; inv H0; auto.
    destruct t; tinv H1.
    destruct (fit_gv (los,nts) t g); tinv H1.
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
    destruct (fit_gv (los,nts) t g); tinv H1.
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
    destruct (getOperandValue TD v lc gl); try solve [inv Hget].    
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
  wf_rmap F (updateAddAL GenericValue lc id0 gv3) rm.
Proof.
  intros.
  intros x gv t J1 J2.
  destruct (eq_atom_dec id0 x); subst.
    contradict J2; auto.

    rewrite <- lookupAL_updateAddAL_neq in J1; eauto.
Qed.

Lemma updateAddAL_ptr__wf_rmap: forall F lc rm id0 gv3 md,
  wf_rmap F lc rm -> 
  wf_rmap F (updateAddAL GenericValue lc id0 gv3) (updateAddAL _ rm id0 md).
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

Lemma initializeFrameValues__wf_rmap : forall TD  fa rt fid va lb lc1 rm1 la2 la1
  ogvs2 lc' rm' ,
  uniqFdef (fdef_intro (fheader_intro fa rt fid (la1++la2) va) lb) ->
  wf_rmap (fdef_intro (fheader_intro fa rt fid (la1++la2) va) lb) lc1 rm1 ->
  _initializeFrameValues TD la2 ogvs2 lc1 rm1 = Some (lc', rm') ->
  wf_rmap (fdef_intro (fheader_intro fa rt fid (la1++la2) va) lb) lc' rm'.
Proof.
  induction la2; intros la1 ogvs2 lc' rm' HuniqF Hwfm Hinit2.
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
      destruct (fit_gv TD t gv); tinv Hinit2. 
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

Lemma returnUpdateLocals__wf_lc : forall ifs los nts S F F' c Result lc lc' gl 
  lc'' Ps l1 ps1 cs1 tmn1 t B' rt rm rm' rm''
  (Hwfg: wf_global (los,nts) S gl) 
  (Hwfv: wf_value S (module_intro los nts Ps) F Result t),
  wf_lc (los,nts) F lc -> wf_lc (los,nts) F' lc' ->
  returnUpdateLocals (los, nts) c rt Result lc lc' rm rm' gl = 
    ret (lc'', rm'') ->
  uniqFdef F' ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F' = true -> 
  In c cs1 ->
  wf_insn ifs S (module_intro los nts Ps) F' B' (insn_cmd c) ->
  wf_lc (los,nts) F' lc''.
Proof.
  intros.
  unfold returnUpdateLocals, returnResult in H1.
  remember (getOperandValue (los,nts) Result lc gl) as R.
  destruct R; tinv H1.
  destruct (isPointerTypB rt).
    destruct (get_reg_metadata (los, nts) gl rm Result); tinv H1.
    destruct c; inv H1; auto.
    destruct n; inv H7; auto.
    destruct t0; tinv H6.
      remember (fit_gv (los, nts) t0 g) as R.
      destruct R; inv H6.
      assert (lc''=updateAddAL GenericValue lc' i0 (? g0 # t0 ?)) as EQ.
        destruct (isPointerTypB t0); inv H7; auto.
      subst.
      eapply wf_lc_updateAddAL with (t:=t0); eauto.
        eapply uniqF__lookupTypViaIDFromFdef; eauto.

        symmetry in HeqR.
        eapply getOperandValue__wf_gv in HeqR; eauto.
        inv H5. inv H21. inv H12. inv H23.
        eapply fit_gv_cgv2gv__wf_gv; eauto.

    destruct c; inv H1; auto.
    destruct n; inv H7; auto.
    destruct t0; tinv H6.
      remember (fit_gv (los, nts) t0 g) as R.
      destruct R; inv H6.
      assert (lc''=updateAddAL GenericValue lc' i0 (? g0 # t0 ?)) as EQ.
        destruct (isPointerTypB t0); inv H7; auto.
      subst.
      eapply wf_lc_updateAddAL with (t:=t0); eauto.
        eapply uniqF__lookupTypViaIDFromFdef; eauto.

        symmetry in HeqR.
        eapply getOperandValue__wf_gv in HeqR; eauto.
        inv H5. inv H21. inv H12. inv H23.
        eapply fit_gv_cgv2gv__wf_gv; eauto.
Qed.

Lemma initializeFrameValues__wf_lc_aux : forall los nts Ps s ifs fattr ft fid va 
  bs2 la2 la1 lc1 rm1
  (Huniq: uniqFdef (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2))
  (Hwflc: wf_lc (los,nts) 
     (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2) lc1) 
  lc2 rm2 gvs2,
  _initializeFrameValues (los,nts) la2 gvs2 lc1 rm1 = Some (lc2, rm2) -> 
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2) 
    lc2.
Proof.
  induction la2; simpl; intros la1 lc1 rm1 Huniq HwfF Hwflc lc2 rm2 gvs2 Hin.
    inv Hin. auto.

    destruct a. destruct p.
    destruct gvs2; simpl in *; subst.
      remember (_initializeFrameValues (los,nts) la2 nil lc1 rm1) as R1.
      destruct R1 as [[lc' rm']|]; tinv Hin.
      remember (gundef (los,nts) t) as R2.
      destruct R2; tinv Hin.
        assert (lc2=updateAddAL GenericValue lc' i0 (? g # t ?)) as EQ.
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
          eapply gundef_cgv2gv__wf_gv; eauto.

      destruct p.
      remember (_initializeFrameValues (los,nts) la2 gvs2 lc1 rm1) as R1.
      destruct R1 as [[lc' rm']|]; tinv Hin.
      remember (fit_gv (los,nts) t g) as R2.
      destruct R2; inv Hin.
        assert (lc2=updateAddAL GenericValue lc' i0 (? g0 # t ?)) as EQ.
          destruct (isPointerTypB t); inv H0; auto.
          destruct o; inv H1; auto.
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
            rewrite <- H12.
            apply in_or_app; simpl; auto.
          apply wf_typ_list__in_args__wf_typ with (t:=t)(a:=a)(i0:=i0) in H13; 
            auto.
          apply feasible_typ_list__in_args__feasible_typ 
            with (t:=t)(a:=a)(i0:=i0) in H14; auto.
          inv H14.
          eapply fit_gv_cgv2gv__wf_gv; eauto.
Qed.

Lemma initializeFrameValues__wf_lc : forall ifs s los nts Ps fattr ft fid la2 va 
  bs2 lc1 rm1
  (Huniq: uniqFdef (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  (Hwflc:wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2) 
    lc1) 
  lc2 rm2 gvs2,
  _initializeFrameValues (los,nts) la2 gvs2 lc1 rm1 = Some (lc2, rm2) -> 
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
  lc rm gvs2,
  initLocals (los,nts) la2 gvs2 = Some (lc, rm) -> 
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
          exists (? g # t ?); apply lookupAL_updateAddAL_eq; auto.      

        destruct p.
        remember (_initializeFrameValues TD la gvs nil nil) as R1.
        destruct R1 as [[lc' rm']|]; tinv H0.
        remember (fit_gv TD t g) as R2.
        destruct R2; inv H0.
        assert (lc = updateAddAL GenericValue lc' id1 (? g0 # t ?)) as EQ.
          destruct (isPointerTypB t); inv H1; auto.
          destruct o; inv H0; auto.
        subst. exists (? g0 # t ?). apply lookupAL_updateAddAL_eq; auto. 

      destruct (eq_atom_dec id0 id1); subst.
        destruct gvs.
          remember (_initializeFrameValues TD la nil nil nil) as R1.
          destruct R1 as [[lc' rm']|]; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          destruct (isPointerTypB t); inv H2;
            exists (? g # t ?); apply lookupAL_updateAddAL_eq; auto.      

          destruct p.
          remember (_initializeFrameValues TD la gvs nil nil) as R1.
          destruct R1 as [[lc' rm']|]; tinv H0.
          remember (fit_gv TD t g) as R2.
          destruct R2; inv H0.
          assert (lc = updateAddAL GenericValue lc' id1 (? g0 # t ?)) as EQ.
            destruct (isPointerTypB t); inv H2; auto.
            destruct o; inv H1; auto.
          subst. exists (? g0 # t ?). apply lookupAL_updateAddAL_eq; auto. 

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
          remember (fit_gv TD t g) as R2.
          destruct R2; inv H0.
          assert (lc = updateAddAL GenericValue lc' id0 (? g0 # t ?)) as EQ.
            destruct (isPointerTypB t); inv H2; auto.
            destruct o; inv H1; auto.
          subst.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1]. 
          exists gv. rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma initLocals_spec' : forall fid fa rt la va lb gvs los nts ifs s lc Ps id1 t
    rm
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hlk: lookupTypViaIDFromFdef (fdef_intro (fheader_intro fa rt fid la va) lb)
         id1 = ret t)
  (Hinit: initLocals (los,nts) la gvs = Some (lc, rm))
  (Hin: In id1 (getArgsIDs la)),
  exists gv, lookupAL _ lc id1 = Some gv /\ wf_genericvalue (los, nts) gv t.
Proof.
  intros.
  assert (J:=Hinit).
  eapply initLocals_spec in J; eauto.
  destruct J as [gv J].
  eapply initLocals__wf_lc in Hinit; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec2_aux : forall ifs s los nts Ps f
  b gl lc rm l3 cs tmn (Hwflc: wf_lc (los, nts) f lc) 
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f) ps2 ps1 rs,
  blockInFdefB (block_intro l3 (ps1++ps2) cs tmn) f ->
  wf_phinodes ifs s (module_intro los nts Ps) f 
    (block_intro l3 (ps1++ps2) cs tmn) ps2 ->
  Some rs = getIncomingValuesForBlockFromPHINodes (los, nts) ps2 b gl lc rm ->
  (forall id0 gv opmd0 t0, 
     In (id0,gv,opmd0) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_genericvalue (los, nts) gv t0).
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
      remember (getOperandValue (los,nts) v lc gl) as R.
      destruct R; tinv H.
      destruct (getIncomingValuesForBlockFromPHINodes (los,nts) ps2 b gl lc rm); 
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
          symmetry in HeqR. eapply getOperandValue__wf_gv in HeqR; eauto.

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
  (forall id0 gv opmd0 t0, 
     In (id0,gv,opmd0) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_genericvalue (los, nts) gv t0).
Proof.
  intros.
  assert (blockInFdefB (block_intro l3 ps cs tmn) f) as Hbinf.
    symmetry in H.
    apply lookupBlockViaLabelFromFdef_inv in H; auto.
    destruct H; eauto.
  eapply getIncomingValuesForBlockFromPHINodes_spec2_aux with (ps1:=nil); 
    eauto using wf_fdef__wf_phinodes.
Qed.

Lemma updateValuesForNewBlock_spec3 : forall TD f lc rm,
  wf_lc TD f lc ->
  forall rs lc' rm', 
  (forall id0 gv opmd0 t0, 
     In (id0,gv,opmd0) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_genericvalue TD gv t0) ->
  updateValuesForNewBlock rs lc rm = (lc', rm') ->
  wf_lc TD f lc'.
Proof.  
  induction rs; intros; simpl in *.
    inv H1. auto.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rs lc rm) as R.
    destruct R as [lc1 rm1].
    assert (lc' = updateAddAL GenericValue lc1 i0 g) as EQ.
      destruct o; inv H1; auto.
    subst.
    intros x gvx tx Htyp Hlk.
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
  (lc : GVMap)
  (gl : GVMap)
  (fs : GVMap)
  (gv3 : GenericValue)
  (EC : list SBopsem.ExecutionContext)
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 Mem': mem)
  (als : list mblock)
  id0 c0
  (Hid : Some id0 = getCmdID c0)
  t0
  (Htyp : Some t0 = getCmdTyp c0)
  (Hwfgv : wf_genericvalue (los,nts) gv3 t0)
  MM rm rm'
  (Hp1: wf_rmap F lc rm -> wf_rmap F (updateAddAL GenericValue lc id0 gv3) rm')
  (Hp2 : wf_rmetadata (los, nts) Mem0 rm -> wf_rmetadata (los, nts) Mem' rm')
  (Hp3 : wf_mmetadata (los, nts) Mem0 MM -> wf_mmetadata (los, nts) Mem' MM)
  (Hp4 : wf_global_ptr S (los, nts) Mem0 gl -> 
         wf_global_ptr S (los, nts) Mem' gl)
  (Hp5 : wf_ECStack (los, nts) Mem0 Ps EC -> wf_ECStack (los, nts) Mem' Ps EC)
  (HwfS1 : wf_State
            {|
            SBopsem.CurSystem := S;
            SBopsem.CurTargetData := (los, nts);
            SBopsem.CurProducts := Ps;
            SBopsem.ECS := {|
                   SBopsem.CurFunction := F;
                   SBopsem.CurBB := B;
                   SBopsem.CurCmds := c0 :: cs;
                   SBopsem.Terminator := tmn;
                   SBopsem.Locals := lc;
                   SBopsem.Rmap := rm;
                   SBopsem.Allocas := als |} :: EC;
            SBopsem.Globals := gl;
            SBopsem.FunTable := fs;
            SBopsem.Mem := Mem0;
            SBopsem.Mmap := MM |}),
   wf_State
     {|
     SBopsem.CurSystem := S;
     SBopsem.CurTargetData := (los, nts);
     SBopsem.CurProducts := Ps;
     SBopsem.ECS := {|
            SBopsem.CurFunction := F;
            SBopsem.CurBB := B;
            SBopsem.CurCmds := cs;
            SBopsem.Terminator := tmn;
            SBopsem.Locals := updateAddAL GenericValue lc id0 gv3;
            SBopsem.Rmap := rm';
            SBopsem.Allocas := als |} :: EC;
     SBopsem.Globals := gl;
     SBopsem.FunTable := fs;
     SBopsem.Mem := Mem';
     SBopsem.Mmap := MM |}.
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
      Case "wflc".
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
  (lc : GVMap)
  (gl : GVMap)
  (fs : GVMap)
  (EC : list SBopsem.ExecutionContext)
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
            SBopsem.CurSystem := S;
            SBopsem.CurTargetData := (los, nts);
            SBopsem.CurProducts := Ps;
            SBopsem.ECS := {|
                   SBopsem.CurFunction := F;
                   SBopsem.CurBB := B;
                   SBopsem.CurCmds := c0 :: cs;
                   SBopsem.Terminator := tmn;
                   SBopsem.Locals := lc;
                   SBopsem.Rmap := rm;
                   SBopsem.Allocas := als |} :: EC;
            SBopsem.Globals := gl;
            SBopsem.FunTable := fs;
            SBopsem.Mem := Mem0;
            SBopsem.Mmap := MM |}),
   wf_State
     {|
     SBopsem.CurSystem := S;
     SBopsem.CurTargetData := (los, nts);
     SBopsem.CurProducts := Ps;
     SBopsem.ECS := {|
            SBopsem.CurFunction := F;
            SBopsem.CurBB := B;
            SBopsem.CurCmds := cs;
            SBopsem.Terminator := tmn;
            SBopsem.Locals := lc;
            SBopsem.Rmap := rm;
            SBopsem.Allocas := als |} :: EC;
     SBopsem.Globals := gl;
     SBopsem.FunTable := fs;
     SBopsem.Mem := Mem';
     SBopsem.Mmap := MM' |}.
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
  (H : getOperandValue (los, nts) v lc gl = ret gv)
  (H0 : extractGenericValue (los, nts) t gv idxs = ret gv')
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
   wf_rmap F (updateAddAL GenericValue lc id0 gv') rm.

Axiom insertValue_preserves_wf_rmap : forall los nts Mem0 v lc gl 
  t gv idxs gv' rm fs EC B S Ps F MM id0 als tmn cs t' v' gv''
  (H : getOperandValue (los, nts) v lc gl = ret gv)
  (H0 : getOperandValue (los, nts) v' lc gl = ret gv')
  (H1 : insertGenericValue (los, nts) t gv idxs t' gv' = ret gv'')
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
   wf_rmap F (updateAddAL GenericValue lc id0 gv'') rm.

Ltac preservation_tac HwfS1 :=
  eapply preservation_cmd_updated_case in HwfS1; simpl; try solve [
      eauto | 
      intro J;
      apply updateAddAL_nptr__wf_rmap; try solve [auto |
        apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1;
        rewrite HwfS1; simpl; try solve [auto | congruence]]
    ].

Lemma preservation : forall S1 S2 tr,
  SBopsem.dsInsn S1 S2 tr -> wf_State S1 -> wf_State S2.
Proof.
  intros S1 S2 tr HdsInsn HwfS1.
  (sb_dsInsn_cases (induction HdsInsn) Case); destruct TD as [los nts];
    try invert_prop_reg_metadata.
Focus.
Case "dsReturn".
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
        unfold SBopsem.returnUpdateLocals, returnResult in H1.
        remember (getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].          
        destruct (isPointerTypB RetTy).        
          destruct (get_reg_metadata (los, nts) gl rm Result) as 
            [[md ?]|]; try solve [inv H1; auto].
          destruct R.
            destruct n; inv HeqR.
            destruct t; tinv H1.
            remember (fit_gv (los, nts) t g) as R1.
            destruct R1; tinv H1.
            inv Hwfc. inv H17. inv H8. inv H19.
            unfold SBopsem.prop_reg_metadata in H1.
            assert (wf_defs (layouts5,namedts5) F' 
              (updateAddAL GenericValue lc' i0 (? g0 # typ1 ?)) ids2) as J.
              eapply wf_defs_updateAddAL with (t1:=typ1) ; eauto.
                eapply uniqF__lookupTypViaIDFromFdef; eauto.
                eapply fit_gv_cgv2gv__wf_gv; eauto.
            destruct typ1; inv H1; auto.

            destruct n; inv HeqR. inv H1.
            simpl in J2.
            eapply wf_defs_eq; eauto. 

          destruct R.
            destruct n; inv HeqR.
            destruct t; tinv H1.
            remember (fit_gv (los, nts) t g) as R1.
            destruct R1; tinv H1.
            inv Hwfc. inv H17. inv H8. inv H19.
            unfold SBopsem.prop_reg_metadata in H1.
            assert (wf_defs (layouts5,namedts5) F' 
              (updateAddAL GenericValue lc' i0 (? g0 # typ1 ?)) ids2) as J.
              eapply wf_defs_updateAddAL with (t1:=typ1) ; eauto.
                eapply uniqF__lookupTypViaIDFromFdef; eauto.
                eapply fit_gv_cgv2gv__wf_gv; eauto.
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
        unfold SBopsem.returnUpdateLocals, returnResult in H1.
        remember (getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].          
        destruct (isPointerTypB RetTy).        
          destruct (get_reg_metadata (los, nts) gl rm Result) as 
            [[md ?]|]; try solve [inv H1; auto].
          destruct R.
            destruct n; inv HeqR.
            destruct t; tinv H1.
            remember (fit_gv (los, nts) t g) as R1.
            destruct R1; tinv H1.
            inv Hwfc. inv H17. inv H8. inv H19.
            unfold SBopsem.prop_reg_metadata in H1.
            assert (wf_defs (layouts5,namedts5) F' 
              (updateAddAL GenericValue lc' i0 (? g0 # typ1 ?)) ids2) as J.
              eapply wf_defs_updateAddAL with (t1:=typ1) ; eauto.
                eapply uniqF__lookupTypViaIDFromFdef; eauto.
                eapply fit_gv_cgv2gv__wf_gv; eauto.
            destruct typ1; inv H1; auto.

            destruct n; inv HeqR. inv H1.
            simpl in J2.
            eapply wf_defs_eq; eauto. 

          destruct R.
            destruct n; inv HeqR.
            destruct t; tinv H1.
            remember (fit_gv (los, nts) t g) as R1.
            destruct R1; tinv H1.
            inv Hwfc. inv H17. inv H8. inv H19.
            unfold SBopsem.prop_reg_metadata in H1.
            assert (wf_defs (layouts5,namedts5) F' 
              (updateAddAL GenericValue lc' i0 (? g0 # typ1 ?)) ids2) as J.
              eapply wf_defs_updateAddAL with (t1:=typ1) ; eauto.
                eapply uniqF__lookupTypViaIDFromFdef; eauto.
                eapply fit_gv_cgv2gv__wf_gv; eauto.
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
Case "dsReturnVoid".
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
Case "dsBranch".
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
      clear - H0 HBinF1 HFinPs1 HmInS HwfSystem HuniqF.
      destruct (isGVZero (los, nts) c).
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; auto.
          destruct H0; auto.
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; auto.
          destruct H0; auto.
    split.
      clear - Hreach1 H0 HBinF1 HFinPs1 HmInS HwfSystem HuniqF.
      unfold isReachableFromEntry in *.
      destruct (isGVZero (los, nts) c).
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; eauto.
        destruct H0 as [H0 _].
        eapply reachable_successors; eauto.
          simpl. auto.
      
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; eauto.
        destruct H0 as [H0 _].
        eapply reachable_successors; eauto.
          simpl. auto.
    split; auto.
    split; auto.
    split.
      destruct (isGVZero (los, nts) c);
        eapply wf_lc_br_aux in H0; eauto.
    split.
      clear - H0 HeqR1 H1 Hinscope1 H HwfSystem HBinF1 HwfF HuniqF Hwflc1 Hwfg.
      eapply inscope_of_tmn_br in HeqR1; eauto.
        destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
        destruct cs'; rewrite <- HeqR1; eauto.

        eapply switchToNewBasicBlock_sim; eauto.

    split.
      clear HwfEC Hreach1 HwfCall Hwfg HeqR1 Hinscope1 H.
      eapply switchToNewBasicBlock__wf_rmap with 
        (b1:=block_intro l' ps' cs' tmn')
        (b2:=block_intro l3 ps3 (cs3' ++ nil) (insn_br bid Cond l1 l2)); eauto.
    split; auto.
      eapply switchToNewBasicBlock__wf_rmetadata in H1; eauto.
      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Focus.
Case "dsBranch_uncond".
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
      clear - H0 HeqR1 Hinscope1 HwfSystem HBinF1 HwfF HuniqF HBinF H Hwfg 
        Hwflc1.
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

Case "dsBop". preservation_tac HwfS1.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  apply wf_value__wf_typ in H8.
  destruct H8 as [J1 J2].
  eapply BOP__wf_gv; eauto.

Case "dsFBop". preservation_tac HwfS1. 
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  apply wf_value__wf_typ in H8.
  destruct H8 as [J1 J2].
  eapply FBOP__wf_gv; eauto.

Case "dsExtractValue".
  assert (J':=HwfS1).
  destruct J' as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  assert (exists t0, getSubTypFromConstIdxs idxs t = Some t0) as J.
    eapply wf_system__wf_cmd with (c:=insn_extractvalue id0 t v idxs) in HBinF1; 
      eauto using in_middle.
      inv HBinF1; eauto.
      destruct H15 as [idxs0 [o [J1 J2]]].
      symmetry in J2.
      eapply mgetoffset__getSubTypFromConstIdxs in J2; eauto.
  destruct J as [t0 J].
  preservation_tac HwfS1. 
    eapply wf_system__wf_cmd in HBinF1; eauto using in_middle.
    inv HBinF1. 
    destruct H15 as [idxs0 [o [J1 J2]]].
    symmetry in J2.
    eapply getSubTypFromConstIdxs__mgetoffset in J2; eauto.
    subst.
    eapply getOperandValue__wf_gv in H; eauto.
    eapply extractGenericValue__wf_gv with (t1:=t); eauto.

    eapply extractValue_preserves_wf_rmap; eauto.

Case "dsInsertValue". 
  preservation_tac HwfS1. 
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc.
    eapply getOperandValue__wf_gv in H; eauto.
    eapply getOperandValue__wf_gv in H0; eauto.
    apply wf_value__wf_typ in H13. destruct H13.
    eapply insertGenericValue__wf_gv; eauto.

    eapply insertValue_preserves_wf_rmap with (gv:=gv); eauto.

Case "dsMalloc". 
  eapply preservation_cmd_updated_case with (rm':=
          updateAddAL SBopsem.metadata rm id0
            {| SBopsem.md_base := SBopsem.base2GV (los, nts) mb;
               SBopsem.md_bound := SBopsem.bound2GV (los, nts) mb tsz n |})
   in HwfS1; simpl; eauto.
    unfold blk2GV, ptr2GV, val2GV. simpl.
    eapply wf_genericvalue_intro; eauto.  
    unfold getTypeSizeInBits. simpl. eauto.
    simpl. auto.

    apply updateAddAL_ptr__wf_rmap; auto. 
    eapply malloc_extends_wf_rmetadata; eauto.
    eapply malloc_extends_wf_mmetadata; eauto.
    eapply malloc_preserves_wf_global_ptr; eauto.
    eapply malloc_preserves_wf_ECStack; eauto.
Case "dsFree". 
  eapply preservation_cmd_non_updated_case with (MM':=MM) in HwfS1; eauto.
    eapply free_preserves_wf_rmetadata; eauto.
    eapply free_preserves_wf_mmetadata; eauto.
    eapply free_preserves_wf_global_ptr; eauto.
    eapply free_preserves_wf_ECStack; eauto.
Case "dsAlloca".
  eapply preservation_cmd_updated_case with (rm':=
          updateAddAL SBopsem.metadata rm id0
            {| SBopsem.md_base := SBopsem.base2GV (los, nts) mb;
               SBopsem.md_bound := SBopsem.bound2GV (los, nts) mb tsz n |})
   in HwfS1; simpl; eauto.
    unfold blk2GV, ptr2GV, val2GV. simpl.
    eapply wf_genericvalue_intro; eauto.  
    unfold getTypeSizeInBits. simpl. eauto.
    simpl. auto.

    apply updateAddAL_ptr__wf_rmap; auto. 
    eapply malloc_extends_wf_rmetadata; eauto.
    eapply malloc_extends_wf_mmetadata; eauto.
    eapply malloc_preserves_wf_global_ptr; eauto.
    eapply malloc_preserves_wf_ECStack; eauto.
Case "dsLoad_nptr". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc.
    apply wf_value__wf_typ in H13. destruct H13.
    inv H5. inv H4. inv H16.
    eapply mload__getTypeSizeInBits in H2; eauto.
      destruct H2 as [sz [J1 J2]]. 
      eapply wf_genericvalue_intro; eauto.  

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1.
      rewrite HwfS1; simpl; auto. 
        intros t0 EQ. inv EQ. inv H3.
Case "dsLoad_ptr".
  assert (J:=HwfS1).
  destruct J as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  eapply preservation_cmd_updated_case with (rm':=updateAddAL metadata rm id0
    (get_mem_metadata (los, nts) MM gvp)) in HwfS1; simpl; eauto.
    eapply wf_system__wf_cmd in HBinF1; eauto using in_middle.
    inv HBinF1.
    apply wf_value__wf_typ in H14. destruct H14.
    inv H6. inv H4. inv H17.
    eapply mload__getTypeSizeInBits in H2; eauto.
      destruct H2 as [sz [J1 J2]]. 
      eapply wf_genericvalue_intro; eauto.      

    apply updateAddAL_ptr__wf_rmap; auto. 
    apply get_mem_metadata__wf_rmetadata; auto.
Case "dsStore_nptr". 
  eapply preservation_cmd_non_updated_case with (MM':=MM) in HwfS1; eauto.
    eapply store_preserves_wf_rmetadata; eauto.
    eapply store_nptr_preserves_wf_mmetadata; eauto.
    eapply store_preserves_wf_global_ptr; eauto.
    eapply store_preserves_wf_ECStack; eauto.
Case "dsStore_ptr". 
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
Case "dsGEP". 
  assert (J:=HwfS1).
  destruct J as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  assert (Hwfc:=HwfS1). apply wf_State__wf_cmd in Hwfc.
  inv Hwfc.
  eapply preservation_cmd_updated_case with 
    (rm':=updateAddAL SBopsem.metadata rm id0 md) in HwfS1; simpl; eauto.
    eapply GEP__wf_gv; eauto.
    apply updateAddAL_ptr__wf_rmap; auto.
    eapply prop_metadata_preserves_wf_rmetadata; eauto.

Case "dsTrunc".
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.  
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc. 
    inv H6; eapply TRUNC__wf_gv with (S:=S); eauto.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. inv H6; congruence.
Case "dsExt". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc. 
    inv H6; eapply EXT__wf_gv with (S:=S); eauto.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. inv H6; congruence.
Case "dsBitcast_nptr". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc. 
    eapply CAST__wf_gv in H; eauto.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. inv H7; try congruence.
          inv H0.
Case "dsBitcast_ptr". 
  assert (J:=HwfS1).
  destruct J as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  assert (Hwfc:=HwfS1). apply wf_State__wf_cmd in Hwfc.
  inv Hwfc.
  eapply preservation_cmd_updated_case with (rm':=updateAddAL metadata rm id0 md)
    in HwfS1; simpl; eauto.
    eapply CAST__wf_gv in H; eauto.
    apply updateAddAL_ptr__wf_rmap; auto.
    eapply prop_metadata_preserves_wf_rmetadata with (t:=t1); eauto.
      inv H9; eauto.

Case "dsInttoptr". 
  eapply preservation_cmd_updated_case with (rm':=
    updateAddAL SBopsem.metadata rm id0 
      {| SBopsem.md_base := null;
         SBopsem.md_bound := null |}) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc. 
    eapply CAST__wf_gv in H; eauto.

    apply updateAddAL_ptr__wf_rmap; auto.
    apply adding_null_preserves_wf_rmetadata; auto.
Case "dsOthercast". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc. 
    eapply CAST__wf_gv in H; eauto.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. 
        destruct H0 as [J1 J2]. 
        inv H7; try (congruence).
Case "dsIcmp". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc. 
    eapply ICMP__wf_gv in H; eauto.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. congruence.
Case "dsFcmp". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc. 
    eapply FCMP__wf_gv in H; eauto.

    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. congruence.
Case "dsSelect_nptr".
  assert (J:=HwfS1).
  apply wf_State__inv in J.
  destruct J as [Hwfg [Hwflc Hwfc]].
  inv Hwfc. 
  eapply getOperandValue__wf_gv in H0; eauto.
  eapply getOperandValue__wf_gv in H1; eauto.
  destruct (isGVZero (los, nts) c); 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; 
    try solve [
      eauto |
      intro J0;
      apply updateAddAL_nptr__wf_rmap; try solve [
        auto |
        apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1;
          rewrite HwfS1; simpl; try solve [auto | intros t0 EQ; inv EQ; inv H2]
      ]
    ].

Case "dsSelect_ptr".
  assert (J:=HwfS1).
  destruct J as 
      [HwfMM [Hwfg [Hwfg' [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwlc1 [Hinscope1 [Hwfm1 [Hwfm1' 
           [l3 [ps3 [cs3' Heq1]]]]]]]]]]
         [HwfEC HwfCall]]]]
      ]]]; subst.
  assert (Hwfc:=HwfS1). apply wf_State__wf_cmd in Hwfc.
  inv Hwfc.
  eapply getOperandValue__wf_gv in H0; eauto.
  eapply getOperandValue__wf_gv in H1; eauto.
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
Case "dsCall".
  assert (Hwfc:=HwfS1).
  apply wf_State__wf_cmd in Hwfc.
  destruct HwfS1 as [HwfMM [Hwfg [Hwfg' [HwfSys [HmInS [
    [Hreach [HBinF [HFinPs [Hwflc [Hinscope [l1 [ps [cs'' Heq]]]]]]]]
    [HwfECs HwfCall]]]]]]].
  assert (InProductsB (product_fdef (fdef_intro 
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    eapply lookupFdefViaGV_inv; eauto.
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

    split.
      simpl. eapply reachable_entrypoint; eauto.
    split.
     apply entryBlockInFdef in H0; auto.
    split; auto.
    split.
     eapply initLocals__wf_lc; eauto.
    split.
     assert (ps'=nil) as EQ.
       eapply entryBlock_has_no_phinodes with (ifs:=nil)(s:=S); eauto.        
     subst.
     apply dom_entrypoint in H0.
     eapply initLocals_params2GVs_sim in H1; eauto.
      destruct H1 as [gvs [J1 J2]]; subst.
     destruct cs'.
       unfold inscope_of_tmn.
       remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
         !! l') as R.
       destruct R.
       eapply preservation_dbCall_case; eauto.

       unfold inscope_of_cmd.
       remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
         !! l') as R.
       destruct R. simpl.
       destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n]; 
         try solve [contradict n; auto]. 
       eapply preservation_dbCall_case; eauto.
    split.
      eapply initLocals__wf_rmap; eauto.
    split. 
      eapply initLocals__wf_rmetadata; eauto.
        inv Hwfc. inv H9. clear - H21.
        apply wf_value_list__in_params__wf_value; eauto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
  split.
  SCase "2".
    repeat (split; auto). eauto.
  SCase "3".
    simpl. intros b HbInBs. destruct b.
    destruct t; auto.

Unfocus.

Case "dsExCall". 
  unfold exCallUpdateLocals in H2.
  destruct noret0.
    inv H2.
    eapply preservation_cmd_non_updated_case with (MM':=MM) in HwfS1; eauto.
      eapply callExternalFunction_preserves_wf_rmetadata; eauto.
      eapply callExternalFunction_preserves_wf_mmetadata; eauto.
      eapply callExternalFunction_preserves_wf_global_ptr; eauto.
      eapply callExternalFunction_preserves_wf_ECStack; eauto.

    destruct oresult; tinv H2.
    destruct ft; tinv H2.
    remember (fit_gv (los, nts) ft g) as R.
    destruct R; tinv H2.
    assert (HwfS1':=HwfS1).
    apply wf_State__inv in HwfS1'.
    destruct HwfS1' as [_ [_ Hwfc]].
    inv Hwfc. inv H18. inv H9. inv H20.
    destruct typ1; inv H2; try solve [
      eapply preservation_cmd_updated_case with (rm':=rm') in HwfS1; 
        try solve [simpl; eauto |
          eapply fit_gv_cgv2gv__wf_gv; eauto |
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
        (rm':=updateAddAL metadata rm rid
          {| md_base := null; md_bound := null |}) in HwfS1; 
        try solve [simpl; eauto | 
          eapply fit_gv_cgv2gv__wf_gv; eauto |
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
Lemma get_const_metadata_isnt_stuck : forall TD gl vc gv bc ec,
  const2GV TD gl vc = Some gv ->
  get_const_metadata vc = Some (bc, ec) ->
  exists gvb, exists gve, 
    const2GV TD gl bc = Some gvb /\ const2GV TD gl ec = Some gve.
Proof.
  unfold const2GV.
  intros TD gl vc gv bc ec J1 J2.  
  remember (_const2GV TD gl vc) as J3.
  destruct J3 as [[gv3 t3]|]; inv J1.
  generalize dependent gv3.
  generalize dependent t3.
  generalize dependent ec.
  generalize dependent bc.
  induction vc; intros; try solve [inversion J2].
    exists (? gv3 # t3 ?). 
    remember t as T.
    destruct TD as [los nts].
    destruct T; inversion J2; clear J2; subst bc ec; simpl in *; 
    unfold mbitcast, p8; try solve [
      destruct (lookupAL GenericValue gl i0); inversion HeqJ3; subst gv3 t3;
      simpl;
      destruct (GV2ptr (los,nts) (getPointerSize0 los) g); eauto;
      remember (mgep (los,nts) t v 
        (INTEGER.to_Z (INTEGER.of_Z 32 1 false) :: nil)) as optr;
      subst t; rewrite <- Heqoptr;
      destruct optr; eauto
    ].

    simpl in *.
    destruct c; try solve [inversion J2].
    destruct t; inv J2.
    remember (_const2GV TD gl vc) as R.
    destruct R as [[gv2 t2]|]; try solve [inv HeqJ3].
    destruct (mcast TD castop_bitcast t2 (typ_pointer t) gv2); 
      try solve [inv HeqJ3].
    apply IHvc with (gv3:=gv2)(t3:=t2) in H0; auto.
    
    simpl in *.
    remember (_const2GV TD gl vc) as R.
    destruct R as [[gv2 t2]|]; try solve [inv HeqJ3].
    apply IHvc with (gv3:=gv2)(t3:=t2) in J2; auto.
Qed.

Lemma wf_phinodes__getIncomingValuesForBlockFromPHINodes : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  l0
  (lc : GVMap)
  (gl : GVMap)
  (t : list atom)
  l1 ps1 cs1 tmn1
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
   exists RVs : list (id * GenericValue * option metadata),
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
      assert (exists gv1, lookupAL GenericValue lc vid = Some gv1) as J1.
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
          destruct H as [gvb [gve [Hc1 Hc2]]].
          rewrite Hc1. rewrite Hc2. simpl.
          destruct (isPointerTypB t0); eauto.

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
  (lc : GVMap)
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
    assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) as J.
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

Lemma get_reg_metadata_isnt_stuck : forall s los nts Ps t f rm gl lc gv v
  (Hwfv : wf_value s (module_intro los nts Ps) f v t)
  (Hptr : true = isPointerTypB t)
  (Hget : getOperandValue (los, nts) v lc gl = ret gv)
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
      eapply get_const_metadata_isnt_stuck in Hget; eauto.
      destruct Hget as [gvb [gve [Hc1 Hc2]]].
      rewrite Hc1. rewrite Hc2. simpl.
      eauto.
Qed.

Definition flatten_typ_total_prop (t:typ) := forall TD,
  Constant.wf_zeroconst_typ t -> Constant.feasible_typ TD t ->
  exists gv, flatten_typ TD t = Some gv.

Definition flatten_typs_total_prop (lt:list_typ) := forall TD,
  Constant.wf_zeroconsts_typ lt -> Constant.feasible_typs TD lt ->
  exists gvs, flatten_typs TD lt = Some gvs.

Lemma flatten_typ_total_mutrec :
  (forall t, flatten_typ_total_prop t) *
  (forall lt,flatten_typs_total_prop lt).
Proof.
  apply typ_mutrec; 
    unfold flatten_typ_total_prop, flatten_typs_total_prop;
    intros; simpl in *; try solve [eauto | inversion H | inversion H1 ].
Case "float".
  destruct f; try solve [eauto | inversion H].
Case "array".
  destruct H with (TD:=TD) as [gv Hz2c]; auto.
  rewrite Hz2c.
  destruct s; eauto.
  apply feasible_typ_inv'' in H1. 
  destruct H1 as [ssz [asz [J1 J2]]].
  rewrite J2.
  eauto.

Case "struct".
  destruct (@H TD) as [gv Hz2c]; auto.
  rewrite Hz2c. destruct gv; eauto.

Case "cons".
  destruct H1 as [J1 J2].
  destruct H2 as [J3 J4].
  destruct (@H TD) as [gv Hz2c]; auto.
  destruct (@H0 TD) as [gvs Hz2cs]; auto.
  rewrite Hz2cs. rewrite Hz2c.
  apply feasible_typ_inv'' in J3.  
  destruct J3 as [ssz [asz [J6 J5]]].
  rewrite J5. eauto.
Qed.

Lemma flatten_typ_total : forall TD t,
  Constant.wf_zeroconst_typ t ->
  Constant.feasible_typ TD t ->
  exists gv, flatten_typ TD t = Some gv.
Proof.
  intros.
  destruct flatten_typ_total_mutrec as [J _].
  apply J; auto.
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
      apply fit_gv__total with (gv1:=g) in H; auto.
      destruct H as [gv H]. rewrite H.
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

Fixpoint proper_aligned (mcs:list AST.memory_chunk) (ofs:Z) : Prop :=
match mcs with
| nil => True
| c::mcs' => (align_chunk c | ofs) /\ proper_aligned mcs' (ofs+size_chunk c)
end.

Lemma proper_aligned_dec : forall (mcs:list AST.memory_chunk) (ofs:Z), 
  proper_aligned mcs ofs \/ ~ proper_aligned mcs ofs.
Proof.
  induction mcs; intros; simpl; auto.
    destruct (Zdivide_dec (align_chunk a) ofs) as [J1 | J1].
      destruct (@IHmcs (ofs + size_chunk a)) as [J2 | J2]; auto.
      right. intro J. apply J2. destruct J; auto.
    right. intro J. apply J1. destruct J; auto.
Qed.

Lemma mload_aux_isnt_stuck_helper : forall TD M gvb gve gv t b ofs mcs2 mcs1
  (Hft : feasible_typ TD t)
  (Hwfd : wf_data TD M gvb gve)
  (Hassert : assert_mptr TD t gv (mkMD gvb gve))
  (Hptr : GV2ptr TD (getPointerSize TD) gv = ret Vptr b ofs)
  (Hflat : getTypeStoreSize TD t = ret (sizeMC (mcs1 ++ mcs2)))
  (Halign : proper_aligned mcs2 ((Int.signed 31 ofs) + Z_of_nat (sizeMC mcs1))) 
  (Htemp : blk_temporal_safe M b),
  exists gv, 
    mload_aux M mcs2 b ((Int.signed 31 ofs) + Z_of_nat (sizeMC mcs1)) = Some gv.
Proof.
  induction mcs2; intros.
    simpl. eauto.
   
    simpl.
    simpl in Halign. destruct Halign as [Halign1 Halign2].
    rewrite_env ((mcs1 ++ [a]) ++ mcs2) in Hflat.

    assert (Z_of_nat (sizeMC mcs1) + size_chunk a =
            Z_of_nat (sizeMC (mcs1 ++ [a]))) as EQ'.
      rewrite sizeMC__app. simpl.
      unfold size_chunk_nat.
      rewrite inj_plus.
      assert (J':=@size_chunk_pos a).
      assert (nat_of_Z (size_chunk a) + 0 = nat_of_Z (size_chunk a))%nat as EQ.
        omega.
        rewrite EQ.
      rewrite nat_of_Z_eq; zauto.

    assert (exists v, Mem.load a M b (Int.signed 31 ofs + Z_of_nat (sizeMC mcs1))
      = Some v) as Hld.
      apply Mem.valid_access_load.
      apply Mem.valid_access_implies with (p1:=Writable); auto with mem.
      assert (J:=Hassert).
      apply assert_mptr_inv in J.
      destruct J as [pb [pofs [bb [bofs [eb [eofs [tsz [J1 [J2 [J3 
        [J4 J5]]]]]]]]]]].
      rewrite Hptr in J1. inv J1.
      eapply assert_mptr__valid_access; eauto. 
        apply Z_of_nat_ge_0.
        eapply getTypeStoreSize_le_getTypeAllocSize in Hft; eauto.
        rewrite EQ'. clear - Hft.
        rewrite sizeMC__app in Hft.        
        unfold Size.to_Z.
        apply inj_le.
        omega.

    assert (Int.signed 31 ofs + Z_of_nat (sizeMC mcs1) + size_chunk a =
            Int.signed 31 ofs + Z_of_nat (sizeMC (mcs1 ++ [a]))) as EQ.
      rewrite <- EQ'. omega.

    destruct Hld as [v Hld].
    rewrite Hld.
    rewrite EQ in Halign2. rewrite EQ.
    destruct (@IHmcs2 (mcs1 ++ [a])) as [gv' Hlds]; auto.
    rewrite Hlds. eauto.
Qed.

Lemma mload_aux_isnt_stuck : forall S TD M gvb gve gv t b ofs mcs
  (Hwft : wf_typ S t)
  (Hft : feasible_typ TD t)
  (Hwfd : wf_data TD M gvb gve)
  (Hassert : assert_mptr TD t gv (mkMD gvb gve))
  (Hptr : GV2ptr TD (getPointerSize TD) gv = ret Vptr b ofs)
  (Hflat : flatten_typ TD t = ret mcs)
  (Halign : proper_aligned mcs (Int.signed 31 ofs)) 
  (Htemp : blk_temporal_safe M b),
  exists gv, mload_aux M mcs b (Int.signed 31 ofs) = Some gv.
Proof.
  intros.
  assert (Int.signed 31 ofs + Z_of_nat (sizeMC nil) = Int.signed 31 ofs) as EQ.
    simpl. ring.
  rewrite <- EQ. rewrite <- EQ in Halign. 
  rewrite_env (mcs ++ nil). 
  eapply mload_aux_isnt_stuck_helper; simpl_env; eauto.
    inv Hft. destruct TD. 
    eapply flatten_typ__getTypeSizeInBits in Hflat; eauto.
    unfold getTypeStoreSize, getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
           getTypeSizeInBits_and_Alignment_for_namedts in *.
    destruct Hflat as [sz [al [J1 J2]]].
    rewrite J1. auto.
Qed.

Definition aligned_gv (gv : GenericValue) ofs : Prop :=
let '(_,mcs) := split gv in proper_aligned mcs ofs.

Lemma aligned_gv_dec : forall gv ofs, aligned_gv gv ofs \/ ~ aligned_gv gv ofs.
Proof.
  unfold aligned_gv. intro gv.
  destruct (split gv).
  apply proper_aligned_dec; auto.
Qed.

Lemma mstore_aux_isnt_stuck_helper : forall TD gvb gve gvp t b ofs gv2 gv1 M
  (Hft : feasible_typ TD t)
  (Hwfd : wf_data TD M gvb gve)
  (Hassert : assert_mptr TD t gvp (mkMD gvb gve))
  (Hptr : GV2ptr TD (getPointerSize TD) gvp = ret Vptr b ofs)
  (Hflat : getTypeStoreSize TD t = ret (sizeGenericValue (gv1 ++ gv2)))
  (Halign : aligned_gv gv2 ((Int.signed 31 ofs) + Z_of_nat (sizeGenericValue gv1))) 
  (Htemp : blk_temporal_safe M b),
  exists M', 
    mstore_aux M gv2 b ((Int.signed 31 ofs) + Z_of_nat (sizeGenericValue gv1)) 
      = Some M'.
Proof.
  induction gv2; intros.
    simpl. eauto.
   
    destruct a. simpl. unfold aligned_gv in Halign.
    remember (split ((v,m)::gv2)) as R.
    destruct R. simpl in HeqR.
    remember (split gv2) as R1.
    destruct R1. inv HeqR. simpl in Halign.
    destruct Halign as [Halign1 Halign2].
    rewrite_env ((gv1 ++ [(v,m)]) ++ gv2) in Hflat.

    assert (Z_of_nat (sizeGenericValue gv1) + size_chunk m =
            Z_of_nat (sizeGenericValue (gv1 ++ [(v,m)]))) as EQ'.
      rewrite sizeGenericValue__app. simpl.
      unfold size_chunk_nat.
      rewrite inj_plus.
      assert (J':=@size_chunk_pos m).
      assert (nat_of_Z (size_chunk m) + 0 = nat_of_Z (size_chunk m))%nat as EQ.
        omega.
        rewrite EQ.
      rewrite nat_of_Z_eq; zauto.

    assert ({ M0 | Mem.store m M b 
             (Int.signed 31 ofs + Z_of_nat (sizeGenericValue gv1)) v
               = Some M0 }) as Hst.
      apply Mem.valid_access_store.
      apply Mem.valid_access_implies with (p1:=Writable); auto with mem.
      assert (J:=Hassert).
      apply assert_mptr_inv in J.
      destruct J as [pb [pofs [bb [bofs [eb [eofs [tsz [J1 [J2 [J3 
        [J4 J5]]]]]]]]]]].
      rewrite Hptr in J1. inv J1.
      eapply assert_mptr__valid_access; eauto. 
        apply Z_of_nat_ge_0.
        eapply getTypeStoreSize_le_getTypeAllocSize in Hft; eauto.
        rewrite EQ'. clear - Hft.
        rewrite sizeGenericValue__app in Hft.        
        unfold Size.to_Z.
        apply inj_le.
        omega.

    assert (Int.signed 31 ofs + Z_of_nat (sizeGenericValue gv1) + size_chunk m =
            Int.signed 31 ofs + Z_of_nat (sizeGenericValue (gv1 ++ [(v,m)]))) 
      as EQ.
      rewrite <- EQ'. omega.

    destruct Hst as [M0 Hst].
    rewrite Hst.
    rewrite EQ in Halign2. rewrite EQ.
    destruct (@IHgv2 (gv1 ++ [(v,m)]) M0) as [M' Hsts]; auto.
      eapply wf_data__store__wf_data in Hst; eauto.
      unfold aligned_gv. rewrite <- HeqR1. auto.
      apply blk_temporal_safe_store_1 with (b0:=b) in Hst; eauto.

    rewrite Hsts. eauto.
Qed.

Lemma mstore_aux_isnt_stuck : forall TD M gvb gve gvp t b ofs gv
  (Hft : feasible_typ TD t)
  (Hwfg : wf_genericvalue TD gv t)
  (Hwfd : wf_data TD M gvb gve)
  (Hassert : assert_mptr TD t gvp (mkMD gvb gve))
  (Hptr : GV2ptr TD (getPointerSize TD) gvp = ret Vptr b ofs)
  (Halign : aligned_gv gv (Int.signed 31 ofs)) 
  (Htemp : blk_temporal_safe M b),
  exists M', mstore_aux M gv b (Int.signed 31 ofs) = Some M'.
Proof.
  intros.
  assert (Int.signed 31 ofs + Z_of_nat (sizeGenericValue nil) = Int.signed 31 ofs) 
    as EQ.
    simpl. ring.
  rewrite <- EQ. rewrite <- EQ in Halign. 
  rewrite_env (gv ++ nil). 
  eapply mstore_aux_isnt_stuck_helper; simpl_env; eauto.
    inv Hwfg. unfold getTypeStoreSize. rewrite H. auto.
Qed.

(*********************************************)
(** * Progress *)

Definition spatial_memory_violation S : Prop :=
  match S with
  | {| SBopsem.CurTargetData := TD;
       SBopsem.ECS := {| SBopsem.CurCmds := insn_load _ t vp _ :: cs;
                           SBopsem.Locals := lc;
                           SBopsem.Rmap := rm
                         |} :: _;
        SBopsem.Globals := gl;
        SBopsem.Mem := Mem0 |} => 
      match SBopsem.get_reg_metadata TD gl rm vp, 
            getOperandValue TD vp lc gl with
      | ret md, ret gvp => ~ SBopsem.assert_mptr TD t gvp md
      | _, _ => False
      end
  | {| SBopsem.CurTargetData := TD;
       SBopsem.ECS := {| SBopsem.CurCmds := insn_store _ t v vp _ :: cs;
                           SBopsem.Locals := lc;
                           SBopsem.Rmap := rm
                         |} :: _;
        SBopsem.Globals := gl;
        SBopsem.Mem := Mem0 |} => 
      match SBopsem.get_reg_metadata TD gl rm vp, 
            getOperandValue TD vp lc gl with
      | ret md, ret gvp => ~ SBopsem.assert_mptr TD t gvp md
      | _, _ => False
      end
  | _ => False
  end.

Definition other_store_violation TD M gvp gv : Prop :=
  match (GV2ptr TD (getPointerSize TD) gvp) with
  | Some (Values.Vptr b ofs) =>
    ~ (aligned_gv gv (Int.signed 31 ofs)) \/ ~ blk_temporal_safe M b
  | _ => False
  end.

Definition other_load_violation TD M gvp t : Prop :=
  match (GV2ptr TD (getPointerSize TD) gvp, flatten_typ TD t) with
  | (Some (Values.Vptr b ofs), Some mcs) =>
    ~ (proper_aligned mcs (Int.signed 31 ofs)) \/ ~ blk_temporal_safe M b
  | _ => False
  end.

Definition undefined_state S : Prop :=
  match S with
  | {| SBopsem.CurTargetData := td;
       SBopsem.ECS := {|
                SBopsem.CurCmds := nil;
                SBopsem.Terminator := insn_return _ _ _;
                SBopsem.Allocas := als |} :: 
              {| SBopsem.CurCmds := c::_ |} :: _;
       SBopsem.Mem := M |} => free_allocas td M als = None
  | _ => False
  end \/
  match S with
  | {| SBopsem.CurTargetData := td;
       SBopsem.ECS := {|
                SBopsem.CurBB := _;
                SBopsem.CurCmds := nil;
                SBopsem.Terminator := insn_return_void _;
                SBopsem.Allocas := als |} :: 
              {| SBopsem.CurCmds := c::_ |} :: _;
       SBopsem.Mem := M |} => 
                      free_allocas td M als = None \/ 
                      match getCallerReturnID c with
                      | Some _ => True
                      | _ => False
                      end
  | _ => False
  end \/
  match S with
  | {| SBopsem.ECS := {|
                SBopsem.CurBB := block_intro _ _ _ (insn_unreachable _);
                SBopsem.CurCmds := nil;
                SBopsem.Terminator := (insn_unreachable _)
               |} :: _
     |} => True
  | _ => False
  end \/
  match S with
  | {| SBopsem.CurTargetData := td;
       SBopsem.ECS := 
         {| SBopsem.CurCmds := insn_malloc _ t v a::_ ; 
            SBopsem.Locals := lc|} :: _;
       SBopsem.Globals := gl;
      SBopsem.Mem := M |}
  | {| SBopsem.CurTargetData := td;
       SBopsem.ECS := 
         {| SBopsem.CurCmds := insn_alloca _ t v a::_ ; 
            SBopsem.Locals := lc|} :: _;
       SBopsem.Globals := gl;
       SBopsem.Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some gv =>
           match getTypeAllocSize td t with
           | Some asz =>
               match malloc td M asz gv a with
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
  | {| SBopsem.CurTargetData := td;
       SBopsem.ECS := 
         {| SBopsem.CurCmds := insn_free _ _ v::_ ; SBopsem.Locals := lc|} 
         :: _;
       SBopsem.Globals := gl;
       SBopsem.Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some gv =>
           match free td M gv with
           | None => True
           | _ => False
           end
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| SBopsem.CurTargetData := td;
       SBopsem.ECS := 
         {| SBopsem.CurCmds := insn_load _ t v a::_ ; 
            SBopsem.Locals := lc|} :: _;
       SBopsem.Globals := gl;
       SBopsem.Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some gv => other_load_violation td M gv t
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| SBopsem.CurTargetData := td;
       SBopsem.ECS := 
         {| SBopsem.CurCmds := insn_store _ t v v0 a::_ ; 
            SBopsem.Locals := lc|} :: _;
       SBopsem.Globals := gl;
       SBopsem.Mem := M |} =>
       match getOperandValue td v lc gl, getOperandValue td v0 lc gl with
       | Some gv, Some mgv => other_store_violation td M mgv gv
       | _, _ => False
       end
  | _ => False
  end \/
  match S with
  | {| SBopsem.CurTargetData := td;
       SBopsem.CurProducts := ps;
       SBopsem.ECS := 
         {| SBopsem.CurCmds := insn_call i0 n _ ft v p::_ ; 
            SBopsem.Locals := lc; SBopsem.Rmap := rm |} :: _;
       SBopsem.Globals := gl;
       SBopsem.FunTable := fs;
       SBopsem.Mem := M |} =>
       match lookupFdefViaGV td ps gl lc fs v, 
             lookupExFdecViaGV td ps gl lc fs v with
       | None, Some (fdec_intro (fheader_intro fa rt fid la va)) =>
           match LLVMgv.params2GVs td p lc gl with
           | Some gvs =>
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
  end \/
  spatial_memory_violation S.

Hint Unfold undefined_state spatial_memory_violation other_load_violation
            other_store_violation.

Hint Constructors SBopsem.dsInsn.

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
  SBopsem.ds_isFinialState S1 = true \/ 
  (exists S2, exists tr, SBopsem.dsInsn S1 S2 tr) \/
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
        assert (exists lc'', exists rm'', SBopsem.returnUpdateLocals (los,nts) 
            (insn_call i1 n c t0 v0 p) t v lc lc' rm rm' gl = 
            Some (lc'',rm'')) as Hretup.
          unfold SBopsem.returnUpdateLocals, returnResult.
          assert (exists gv : GenericValue, 
            getOperandValue (los, nts) v lc gl = ret gv) as H.
            eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
              simpl. auto.
          destruct H as [gv H]. rewrite H.
          unfold SBopsem.prop_reg_metadata.            
          destruct HwfECs as [[Hreach' 
              [HbInF' [HfInPs' [Hwflc' [Hinscope' [Hwfm1 [Hwfm1'
                [l1' [ps1' [cs1' Heq']]]]]]]]]] 
              [HwfECs HwfCall]]; subst.
          eapply wf_system__wf_cmd in HbInF'; eauto using in_middle.
          inv HbInF'. inv H6.
          assert (exists gv0, fit_gv (layouts5, namedts5) typ1 gv = Some gv0)
            as G.
            inv H17.
            apply fit_gv__total; auto.
          destruct G as [gv0 G].
          remember (isPointerTypB t) as Hptr.
          destruct Hptr.
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
            destruct n; eauto.
            rewrite G. 
            destruct (isPointerTypB typ1); eauto.

            destruct n; eauto.
            rewrite G. 
            destruct (isPointerTypB typ1); eauto.
         
        destruct Hretup as [lc'' [rm'' Hretup]].
        exists (SBopsem.mkState s (los, nts) ps 
           ((SBopsem.mkEC f' b' cs' tmn' lc'' rm'' als')::ecs) gl fs M' Mmap0).
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
        exists (SBopsem.mkState s (los, nts) ps 
          ((SBopsem.mkEC f' b' cs' tmn' lc' rm' als')::ecs) gl fs M' Mmap0).
        exists trace_nil.
        eauto.  

    SCase "tmn=br".
      right. left.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists c, getOperandValue (los,nts) v lc gl = Some c) as Hget.
        eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
          simpl. auto.
      destruct Hget as [c Hget].
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
      assert (exists lc', exists rm', SBopsem.switchToNewBasicBlock (los, nts) 
        (block_intro l' ps' cs' tmn') 
        (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l2 l3)) gl lc rm = 
          Some (lc', rm')) as Hswitch.
         assert (exists RVs, 
           SBopsem.getIncomingValuesForBlockFromPHINodes (los, nts) ps'
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
    assert (exists gv3, BOP (los,nts) lc gl b s0 v v0 = Some gv3) as Hinsn_bop.
      unfold BOP.      
      assert (exists gv, getOperandValue (los, nts)v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
          destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0. 
      unfold mbop. inv Hwfc.
      apply wf_value__wf_typ in H7. destruct H7 as [J1 J2]. inv J2.
      destruct (GV2val (los, nts) gv); eauto using gundef__total.
      destruct v1; eauto using gundef__total.
      destruct (GV2val (los, nts) gv0); eauto using gundef__total.
      destruct v1; eauto using gundef__total.
      destruct (eq_nat_dec (wz + 1) (Size.to_nat s0)); 
        eauto using gundef__total.
      destruct b; eauto using gundef__total.

    destruct Hinsn_bop as [gv3 Hinsn_bop].
    exists 
         {|
         SBopsem.CurSystem := s;
         SBopsem.CurTargetData := (los, nts);
         SBopsem.CurProducts := ps;
         SBopsem.ECS := {|
                SBopsem.CurFunction := f;
                SBopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_bop i0 b s0 v v0 :: cs) tmn;
                SBopsem.CurCmds := cs;
                SBopsem.Terminator := tmn;
                SBopsem.Locals := (updateAddAL _ lc i0 gv3);
                SBopsem.Rmap := rm;
                SBopsem.Allocas := als |} :: ecs;
         SBopsem.Globals := gl;
         SBopsem.FunTable := fs;
         SBopsem.Mem := M;
         SBopsem.Mmap := Mmap0 |}.
     exists trace_nil. eauto.

  SCase "c=fbop". 
    left.
    assert (exists gv3, FBOP (los,nts) lc gl f0 f1 v v0 = Some gv3) 
      as Hinsn_fbop.
      unfold FBOP.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0. 
      unfold mfbop. inv Hwfc.
      apply wf_value__wf_typ in H7. destruct H7 as [J1 J2]. inv J2.
      destruct (GV2val (los, nts) gv); eauto using gundef__total.
      destruct v1; eauto using gundef__total.
      destruct (GV2val (los, nts) gv0); eauto using gundef__total.
      destruct v1; eauto using gundef__total.
      destruct f1; try solve [eauto | inversion J1].

    destruct Hinsn_fbop as [gv3 Hinsn_fbop].
    exists 
         {|
         SBopsem.CurSystem := s;
         SBopsem.CurTargetData := (los, nts);
         SBopsem.CurProducts := ps;
         SBopsem.ECS := {|
                SBopsem.CurFunction := f;
                SBopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_fbop i0 f0 f1 v v0 :: cs) tmn;
                SBopsem.CurCmds := cs;
                SBopsem.Terminator := tmn;
                SBopsem.Locals := (updateAddAL _ lc i0 gv3);
                SBopsem.Rmap := rm;
                SBopsem.Allocas := als |} :: ecs;
         SBopsem.Globals := gl;
         SBopsem.FunTable := fs;
         SBopsem.Mem := M;
         SBopsem.Mmap := Mmap0 |}.
     exists trace_nil. eauto.

  SCase "c=extractvalue".
    left.
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', extractGenericValue (los, nts) t gv l2 = Some gv') as J'.
      unfold extractGenericValue.
      inv Hwfc. destruct H13 as [idxs [o [J1 J2]]].
      rewrite J1. rewrite J2. inv H15.
      destruct (mget (los, nts) gv o typ'); eauto using gundef__total.

    destruct J' as [gv' J'].
    exists {|
         SBopsem.CurSystem := s;
         SBopsem.CurTargetData := (los, nts);
         SBopsem.CurProducts := ps;
         SBopsem.ECS := {|
                SBopsem.CurFunction := f;
                SBopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_extractvalue i0 t v l2 :: cs) tmn;
                SBopsem.CurCmds := cs;
                SBopsem.Terminator := tmn;
                SBopsem.Locals := (updateAddAL _ lc i0 gv');
                SBopsem.Rmap := rm;
                SBopsem.Allocas := als |} :: ecs;
         SBopsem.Globals := gl;
         SBopsem.FunTable := fs;
         SBopsem.Mem := M;
         SBopsem.Mmap := Mmap0|}.
     exists trace_nil. eauto.

  SCase "c=insertvalue".
    left.
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', getOperandValue (los, nts) v0 lc gl = Some gv') as J'.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J' as [gv' J'].
    assert (exists gv'', insertGenericValue (los, nts) t gv l2 t0 gv' = 
      Some gv'') as J''.
      unfold insertGenericValue.
      inv Hwfc. destruct H16 as [idxs [o [J1 J2]]].
      rewrite J1. rewrite J2.
      apply wf_value__wf_typ in H10. destruct H10 as [J3 J4]. inv J4.
      destruct (mset (los, nts) gv o t0 gv'); eauto using gundef__total.

    destruct J'' as [gv'' J''].
    exists 
         {|
         SBopsem.CurSystem := s;
         SBopsem.CurTargetData := (los, nts);
         SBopsem.CurProducts := ps;
         SBopsem.ECS := {|
                SBopsem.CurFunction := f;
                SBopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_insertvalue i0 t v t0 v0 l2 :: cs) tmn;
                SBopsem.CurCmds := cs;
                SBopsem.Terminator := tmn;
                SBopsem.Locals := (updateAddAL _ lc i0 gv'');
                SBopsem.Rmap := rm;
                SBopsem.Allocas := als |} :: ecs;
         SBopsem.Globals := gl;
         SBopsem.FunTable := fs;
         SBopsem.Mem := M;
         SBopsem.Mmap := Mmap0 |}.
     exists trace_nil. eauto.

  SCase "c=malloc". 
    inv Hwfc. inv H12.
    apply feasible_typ_inv'' in H.
    destruct H as [ssz [asz [J1 J2]]].
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    remember (malloc (los, nts) M asz gv a) as R.
    destruct R as [[M' mb] |].
      left.
      assert (exists n, GV2int (los, nts) Size.ThirtyTwo gv = Some n) as H.
        clear - HeqR0. unfold malloc in HeqR0.
        destruct (GV2int (los, nts) Size.ThirtyTwo gv); inv HeqR0; eauto.
      destruct H as [n H].
      remember (prop_reg_metadata lc rm i0 (blk2GV (los, nts) mb) 
        (mkMD (base2GV (los, nts) mb) (bound2GV (los, nts) mb asz n))) as R.
      destruct R as [lc' rm'].
      exists 
         {|
         SBopsem.CurSystem := s;
         SBopsem.CurTargetData := (los, nts);
         SBopsem.CurProducts := ps;
         SBopsem.ECS := {|
                SBopsem.CurFunction := f;
                SBopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_malloc i0 t v a :: cs) tmn;
                SBopsem.CurCmds := cs;
                SBopsem.Terminator := tmn;
                SBopsem.Locals := lc';
                SBopsem.Rmap := rm';
                SBopsem.Allocas := als |} :: ecs;
         SBopsem.Globals := gl;
         SBopsem.FunTable := fs;
         SBopsem.Mem := M';
         SBopsem.Mmap := Mmap0 |}.
      exists trace_nil.
      eauto.
      
      unfold undefined_state.
      right. rewrite J. rewrite J2. rewrite <- HeqR0. undefbehave.

  SCase "free". 
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    remember (free (los, nts) M gv) as R.
    destruct R as [M'|].
      left.
      exists 
         {|
         SBopsem.CurSystem := s;
         SBopsem.CurTargetData := (los, nts);
         SBopsem.CurProducts := ps;
         SBopsem.ECS := {|
                SBopsem.CurFunction := f;
                SBopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_free i0 t v :: cs) tmn;
                SBopsem.CurCmds := cs;
                SBopsem.Terminator := tmn;
                SBopsem.Locals := lc;
                SBopsem.Rmap := rm;
                SBopsem.Allocas := als |} :: ecs;
         SBopsem.Globals := gl;
         SBopsem.FunTable := fs;
         SBopsem.Mem := M';
         SBopsem.Mmap := Mmap0 |}.
      exists trace_nil.
      eauto.      
      
      unfold undefined_state.
      right. rewrite J. rewrite <- HeqR0. undefbehave.

  SCase "alloca".
    inv Hwfc. inv H12.
    apply feasible_typ_inv'' in H.
    destruct H as [ssz [asz [J1 J2]]].
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    remember (malloc (los, nts) M asz gv a) as R.
    destruct R as [[M' mb] |].
      assert (exists n, GV2int (los, nts) Size.ThirtyTwo gv = Some n) as H.
        clear - HeqR0. unfold malloc in HeqR0.
        destruct (GV2int (los, nts) Size.ThirtyTwo gv); inv HeqR0; eauto.
      destruct H as [n H].
      remember (prop_reg_metadata lc rm i0 (blk2GV (los, nts) mb) 
        (mkMD (base2GV (los, nts) mb) (bound2GV (los, nts) mb asz n))) as R.
      destruct R as [lc' rm'].
      left.
      exists 
         {|
         SBopsem.CurSystem := s;
         SBopsem.CurTargetData := (los, nts);
         SBopsem.CurProducts := ps;
         SBopsem.ECS := {|
                SBopsem.CurFunction := f;
                SBopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_alloca i0 t v a :: cs) tmn;
                SBopsem.CurCmds := cs;
                SBopsem.Terminator := tmn;
                SBopsem.Locals := lc';
                SBopsem.Rmap := rm';
                SBopsem.Allocas := (mb::als) |} :: ecs;
         SBopsem.Globals := gl;
         SBopsem.FunTable := fs;
         SBopsem.Mem := M';
         SBopsem.Mmap := Mmap0 |}.
      exists trace_nil.
      eauto.
      
      right.
      unfold undefined_state.
      right. rewrite J. rewrite J2. rewrite <- HeqR0. undefbehave.

  SCase "load".
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
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
            remember (SBopsem.prop_reg_metadata lc rm i0 gv' 
              (SBopsem.get_mem_metadata (los, nts) Mmap0 gv)) as R.
            destruct R as [lc' rm'].
            left.
            exists 
             {|
               SBopsem.CurSystem := s;
               SBopsem.CurTargetData := (los, nts);
               SBopsem.CurProducts := ps;
               SBopsem.ECS := {|
                  SBopsem.CurFunction := f;
                  SBopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_load i0 t v a :: cs) tmn;
                  SBopsem.CurCmds := cs;
                  SBopsem.Terminator := tmn;
                  SBopsem.Locals := lc';
                  SBopsem.Rmap := rm';
                  SBopsem.Allocas := als |} :: ecs;
               SBopsem.Globals := gl;
               SBopsem.FunTable := fs;
               SBopsem.Mem := M;
               SBopsem.Mmap := Mmap0 |}.
            exists trace_nil. eauto.

          SSSSSCase "load_nptr".
            left.
            exists 
             {|
               SBopsem.CurSystem := s;
               SBopsem.CurTargetData := (los, nts);
               SBopsem.CurProducts := ps;
               SBopsem.ECS := {|
                  SBopsem.CurFunction := f;
                  SBopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_load i0 t v a :: cs) tmn;
                  SBopsem.CurCmds := cs;
                  SBopsem.Terminator := tmn;
                  SBopsem.Locals := updateAddAL _ lc i0 gv';
                  SBopsem.Rmap := rm;
                  SBopsem.Allocas := als |} :: ecs;
               SBopsem.Globals := gl;
               SBopsem.FunTable := fs;
               SBopsem.Mem := M;
               SBopsem.Mmap := Mmap0 |}.
            exists trace_nil. eauto.

        SSSSCase "~valid block".
          right.
          unfold undefined_state. unfold other_load_violation.
          right. rewrite J. rewrite R3. rewrite Hflat. undefbehave.

      SSSCase "align fails".
        right.
        unfold undefined_state. unfold other_load_violation.
        right. rewrite J. rewrite R3. rewrite Hflat. undefbehave.

    SSCase "assert fails".
      right.
      unfold undefined_state. unfold spatial_memory_violation.
      right. rewrite J. rewrite J2. undefbehave.

  SCase "store".
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [mgv J0].
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
      inv Hwfc. 
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
              eapply getOperandValue__wf_gv in J; eauto.

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
          right. rewrite J. rewrite J0. rewrite R3. undefbehave.

      SSSCase "align fails".
        right.
        unfold undefined_state. unfold other_store_violation.
        right. rewrite J. rewrite J0. rewrite R3. undefbehave.

    SSCase "assert fails".
      right.
      unfold undefined_state. unfold spatial_memory_violation.
      right. rewrite J. rewrite J0. rewrite J2. undefbehave.

  SCase "gep".
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [mp J].
    assert (exists vidxs, values2GVs (los, nts) l2 lc gl = Some vidxs) as J2.
      eapply values2GVs_isnt_stuck; eauto.
        exists Nil_list_value. auto.
    destruct J2 as [vidxs J2].
    inv Hwfc.
    assert (exists mp', GEP (los, nts) t mp vidxs i1 = Some mp') as J3.
      unfold GEP. inv H17.
      destruct (GV2ptr (los, nts) (getPointerSize (los, nts)) mp); 
        eauto using gundef_p1__total.
      destruct (GVs2Nats (los, nts) vidxs); eauto using gundef_p1__total.
      destruct (mgep (los, nts) t v0 l3); eauto using gundef_p1__total.
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
    assert (exists gv2, TRUNC (los,nts) lc gl t t0 v t1 = Some gv2) 
      as Hinsn_trunc.
      unfold TRUNC.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      unfold mtrunc. inv Hwfc.
      assert (H5':=H5).
      apply wf_trunc__wf_typ in H5'. destruct H5' as [J1 J2]. inv J2.
      destruct (GV2val (los, nts) gv); eauto using gundef__total.
      inv H5; try solve [destruct v0; eauto using gundef__total].
        rewrite H16.
        destruct v0; eauto using gundef__total.
          destruct floating_point2; try solve [eauto | inversion H14].

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
    assert (exists gv2, EXT (los,nts) lc gl e t v t0 = Some gv2) 
      as Hinsn_ext.
      unfold EXT.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      unfold mext. 
      inv Hwfc. 
      inv H5; try solve 
        [destruct (GV2val (los, nts) gv); eauto using gundef__total'; 
         destruct v0; eauto using gundef__total'].
        rewrite H15.
        destruct (GV2val (los, nts) gv); eauto using gundef__total'; 
        destruct v0; eauto using gundef__total'.
        destruct floating_point2; try solve [inversion H13 | eauto].

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
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv2, CAST (los,nts) lc gl c t v t0 = Some gv2) 
      as Hinsn_cast.
      unfold CAST.      
      rewrite J.
      unfold mcast, mptrtoint, mbitcast.
      inv Hwfc. 
      inv H5; eauto using gundef__total'.

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
       exists trace_nil; subst; eapply dsOtherCast; 
         try solve [eauto | split; congruence]].
    SSCase "case_inttoptr".
      remember (prop_reg_metadata lc rm i0 gv2 (mkMD null null)) as R.
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
    assert (exists gv2, ICMP (los,nts) lc gl c t v v0 = Some gv2) 
      as Hinsn_icmp.
      unfold ICMP.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0.
      unfold micmp.
      inv Hwfc. 
      unfold isPointerTyp in H13. unfold is_true in H13.
      unfold micmp_int.
      destruct H13 as [H13 | H13].
        destruct t; try solve [simpl in H13; contradict H13; auto].
        destruct (GV2val (los,nts) gv); eauto using gundef_i1__total.
        destruct v1; eauto using gundef_i1__total.
        destruct (GV2val (los,nts) gv0); eauto using gundef_i1__total.
        destruct v1; eauto using gundef_i1__total.
        destruct c; eauto using gundef_i1__total.

        destruct t; try solve [simpl in H13; contradict H13; auto]. 
          eauto using gundef_i1__total.
        (*destruct (mptrtoint (los, nts) M gv Size.ThirtyTwo); eauto.
        destruct (mptrtoint (los, nts) M gv0 Size.ThirtyTwo); eauto.
        destruct (GV2val (los, nts) g); eauto.
        destruct v1; eauto.
        destruct (GV2val (los, nts) g0); eauto.
        destruct v1; eauto.
        destruct c; eauto.*)
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
    assert (exists gv2, FCMP (los,nts) lc gl f0 f1 v v0 = Some gv2) 
      as Hinsn_fcmp.
      unfold FCMP.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0.
      unfold mfcmp.
      inv Hwfc. 
      destruct (GV2val (los, nts) gv); eauto using gundef_i1__total.
      destruct v1; eauto using gundef_i1__total.
      destruct (GV2val (los, nts) gv0); eauto using gundef_i1__total.
      destruct v1; eauto using gundef_i1__total.
      apply wf_value__wf_typ in H12.
      destruct H12 as [J1 J2].
      destruct f1; try solve [eauto | inversion J1].
        destruct f0; try solve [eauto | inversion H8].
        destruct f0; try solve [eauto | inversion H8].

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
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv0, getOperandValue (los, nts) v0 lc gl = Some gv0) as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [gv0 J0].
    assert (exists gv1, getOperandValue (los, nts) v1 lc gl = Some gv1) as J1.
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
      remember (if isGVZero (los, nts) gv then 
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
                Locals := (if isGVZero (los, nts) gv 
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
    remember (lookupFdefViaGV (los, nts) ps gl lc fs v) as Hlk. 
    destruct Hlk as [f' |].
    SSCase "internal call".
    assert (exists gvs, params2GVs (los, nts) p lc gl rm = Some gvs) as G.
      eapply params2GVs_isnt_stuck; eauto. 
        exists nil. auto.
    destruct G as [gvs G].
    destruct f' as [[fa rt fid la va] lb].
    assert (J:=HeqHlk).
    symmetry in HeqHlk.
    apply lookupFdefViaGV_inv in HeqHlk; auto.
    eapply wf_system__wf_fdef in HeqHlk; eauto.
    assert (Hinit := HeqHlk).
    apply initLocal__total with (gvs2:=gvs) in Hinit; auto.
    destruct Hinit as [[lc' rm'] Hinit].
    inv HeqHlk. destruct block5 as [l5 ps5 cs5 tmn5].
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

    remember (lookupExFdecViaGV (los, nts) ps gl lc fs v) as Helk. 
    destruct Helk as [f' |].
    SSCase "external call".
    assert (exists gvs, LLVMgv.params2GVs (los, nts) p lc gl = Some gvs) 
      as G.
      eapply ssa_wf.params2GVs_isnt_stuck; eauto. 
        exists nil. auto.
    destruct G as [gvs G].
    destruct f' as [[fa rt fid la va]].
    remember (callExternalFunction M fid gvs) as R.
    destruct R as [[oresult Mem']|].
      remember (exCallUpdateLocals (los,nts) t n i0 oresult lc rm) as R'.
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
        right. rewrite <- HeqHlk. rewrite <- HeqHelk. rewrite G. 
        rewrite <- HeqR0. rewrite <- HeqR'. undefbehave.

      right.
      unfold undefined_state.
      right. rewrite <- HeqHlk. rewrite <- HeqHelk. rewrite G. 
      rewrite <- HeqR0. undefbehave.

   SSCase "stuck".
     right.
     unfold undefined_state.
     right. rewrite <- HeqHlk. rewrite <- HeqHelk. undefbehave.
Qed.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
