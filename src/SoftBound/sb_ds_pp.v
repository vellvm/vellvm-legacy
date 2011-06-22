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

Export LLVMwf.
Export AtomSet.
Export LLVMgv.
Export SBopsem.

Definition wf_rmap (f:fdef) (lc:GVMap) (rm:rmetadata) : Prop :=
forall id1 gv1 t1, 
  lookupAL _ lc id1 = Some gv1 -> 
  lookupTypViaIDFromFdef f id1 = Some (typ_pointer t1) ->
  exists md, lookupAL _ rm id1 = Some md.

Definition wf_ExecutionContext (ps:list product) (ec:SBopsem.ExecutionContext) 
  : Prop :=
let '(SBopsem.mkEC f b cs tmn lc rm als) := ec in
isReachableFromEntry f b /\
blockInFdefB b f = true /\
InProductsB (product_fdef f) ps = true /\
match cs with
| nil => 
    match inscope_of_tmn f b tmn with
    | Some ids => wf_defs f lc ids
    | None => False
    end
| c::_ =>
    match inscope_of_cmd f b c with
    | Some ids => wf_defs f lc ids
    | None => False
    end
end /\
wf_rmap f lc rm /\
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

Fixpoint wf_ECStack (ps:list product) (ecs:SBopsem.ECStack) : Prop :=
match ecs with
| nil => False
| ec::ecs' => wf_ExecutionContext ps ec /\ wf_ECStack ps ecs' /\ wf_call ec ecs'
end.

Definition wf_State (S:SBopsem.State) : Prop :=
let '(SBopsem.mkState s (los, nts) ps ecs gl _ _ _) := S in
wf_global s gl /\
wf_system nil s /\
moduleInSystemB (module_intro los nts ps) s = true /\
wf_ECStack ps ecs.

(*********************************************)
(** * Preservation *)

Definition preserved_MM (MM MM':SBopsem.mmetadata) := True.

Hint Unfold preserved_MM.

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
  (Mem0 : mem)
  (als : list mblock)
  id0 c0
  (Hid : Some id0 = getCmdID c0)
  t0
  (Htyp : Some t0 = getCmdTyp c0)
  MM rm rm'
  (Hprm : wf_rmap F lc rm -> wf_rmap F (updateAddAL GenericValue lc id0 gv3) rm')
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
     SBopsem.Mem := Mem0;
     SBopsem.Mmap := MM |}.
Proof.
  intros.
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [Hwfm [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]]
    ]; subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0) 
    as R1. 
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
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
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL with (t1:=t0) ; eauto.
          eapply uniqF__lookupTypViaIDFromFdef; eauto.
            eapply wf_system__uniqFdef; eauto.
        
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
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL with (t1:=t0) ; eauto.
          eapply uniqF__lookupTypViaIDFromFdef; eauto.
            eapply wf_system__uniqFdef; eauto.

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
  (Mem0 : mem)
  (als : list mblock)
  c0
  (Hid : getCmdID c0 = None)
  rm MM MM'
  (HpMM : preserved_MM MM MM')
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
     SBopsem.Mem := Mem0;
     SBopsem.Mmap := MM' |}.
Proof.
  intros.
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [Hwfm [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]]
    ]; subst.
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
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
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
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq ; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
Qed.

Lemma returnUpdateLocals__wf_rmap : 
  forall los nts Mem' c' Result lc lc' rm rm' gl lc'' rm'' F' tmn' cs' Ps S
  (H1 : returnUpdateLocals (los, nts) Mem' c' Result lc lc' rm rm' gl =
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
      unfold returnUpdateLocals in H1.
      destruct c'; inv H1; auto.
      destruct n; inv H0; auto.
      remember (getOperandValue (los, nts) Mem' Result lc gl) as R1.
      destruct R1; inv H1.
      inv Hwfc. 
      clear H12 H17 H6 H15 H16.
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
      intros x gvx tx Hin Htyp.
      destruct (eq_atom_dec x i0); subst.        
        rewrite J in Htyp. inv Htyp.
        remember (get_reg_metadata (los, nts) Mem' gl rm Result) as R3.
        destruct R3 as [[md ?]|]; inv H0.
          rewrite lookupAL_updateAddAL_eq. eauto.
          rewrite lookupAL_updateAddAL_eq. eauto.
       
        destruct typ1; inv H0; try solve [
          rewrite <- lookupAL_updateAddAL_neq in Hin; auto;
          eapply Hwfm2 in Hin; eauto
        ].
          destruct (get_reg_metadata (los, nts) Mem' gl rm Result)
            as [[md ?]|]; inv H1; try solve [
            rewrite <- lookupAL_updateAddAL_neq in Hin; auto;
            rewrite <- lookupAL_updateAddAL_neq; eauto
          ].
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec : forall ps TD Mem0 b gl lc id1
    rm re gv1 opmd1,
  Some re = getIncomingValuesForBlockFromPHINodes TD Mem0 ps b gl lc rm ->
  In (id1, gv1, opmd1) re ->
  In id1 (getPhiNodesIDs ps).
Proof.    
  induction ps; intros; simpl in *.
    inv H. inversion H0.

    destruct a.
    destruct (getValueViaBlockFromValuels l0 b); try solve [inversion H].   
    destruct (getOperandValue TD Mem0 v lc gl); try solve [inversion H].   
    remember (getIncomingValuesForBlockFromPHINodes TD Mem0 ps b gl lc rm) as R.
    destruct R; try solve [inv H].
    simpl.
    destruct (isPointerTypB t); inv H.
      destruct (get_reg_metadata TD Mem0 gl rm v) as [[md mt]|]; inv H2.      
      simpl in H0.
      destruct H0 as [H0 | H0]; eauto.  
        inv H0; auto.

      simpl in H0.
      destruct H0 as [H0 | H0]; eauto.  
        inv H0; auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes__wf_rmap : forall PNs TD M b gl lc rm
   re id1 gv1 opmd1 t1,
  NoDup (getPhiNodesIDs PNs) ->
  getIncomingValuesForBlockFromPHINodes TD M PNs b gl lc rm = Some re ->
  In (id1,gv1,opmd1) re ->
  lookupTypViaIDFromPhiNodes PNs id1 = Some (typ_pointer t1) ->
  opmd1 <> None.
Proof.
  induction PNs; simpl; intros TD M b gl lc rm re id1 gv1 opmd1 t1 Huniq Hget Hin
    Hlk.
    inv Hget. inversion Hin.

    inv Huniq.
    destruct a.
    destruct (getValueViaBlockFromValuels l0 b); try solve [inv Hget].
    destruct (getOperandValue TD M v lc gl); try solve [inv Hget].    
    remember (getIncomingValuesForBlockFromPHINodes TD M PNs b gl lc rm) as R.
    destruct R; try solve [inv Hget].
    unfold lookupTypViaIDFromPhiNode in Hlk. simpl in Hlk.
    destruct (id1==i0); subst.
      inv Hlk.
      simpl in Hget.
      remember (get_reg_metadata TD M gl rm v) as R.
      destruct R as [[md mt]|]; inv Hget.
      simpl in Hin.
      destruct Hin as [Hin | Hin]; try (inv Hin; congruence).
        simpl in H1.         
        eapply getIncomingValuesForBlockFromPHINodes_spec in HeqR; eauto.

      destruct (isPointerTypB t); inv Hget.
        destruct (get_reg_metadata TD M gl rm v) as [[md mt]|]; inv H0.
        simpl in Hin.
        destruct Hin as [Hin | Hin].
          inv Hin. congruence.
          eauto.
        simpl in Hin.
        destruct Hin as [Hin | Hin].
          inv Hin. congruence.
          eauto.
Qed.

Lemma updateValuesForNewBlock_spec1 : forall rvs lc x rm lc' rm' gv,
  lookupAL _ lc x = None ->
  (lc', rm') = updateValuesForNewBlock rvs lc rm ->
  lookupAL _ lc' x = Some gv ->
  exists omd, In (x, gv, omd) rvs.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' gv Hlk Hupdate Hlk'.
    inv Hupdate. rewrite Hlk in Hlk'. inversion Hlk'.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk'; auto.
        inv Hlk'. eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk'; auto.
        eapply IHrvs in HeqR; eauto.
        destruct HeqR as [omd HeqR]. eauto.

      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk'; auto.
        inv Hlk'. eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk'; auto.
        eapply IHrvs in HeqR; eauto.
        destruct HeqR as [omd HeqR]. eauto.
Qed.

Lemma updateValuesForNewBlock_spec2 : forall rvs lc x rm lc' rm' md,
  lookupAL _ rm x = Some md ->
  (lc', rm') = updateValuesForNewBlock rvs lc rm ->
  exists md, lookupAL _ rm' x = Some md.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' md Hlk Hupdate.
    inv Hupdate; eauto.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md1 ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq.
        eauto.

        rewrite <- lookupAL_updateAddAL_neq; auto.
        eapply IHrvs in HeqR; eauto.

      eapply IHrvs in HeqR; eauto.
Qed.

Lemma updateValuesForNewBlock_spec3 : forall rvs lc x rm lc' rm' gvx md mt,
  In (x, gvx, Some (md,mt)) rvs ->
  (lc', rm') = updateValuesForNewBlock rvs lc rm ->
  exists md, lookupAL _ rm' x = Some md.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' gvx md mt Hin Hupdate.
    inversion Hin.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md1 ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq. eauto.

        rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct Hin as [Hin | Hin].
          inv Hin. contradict n; auto.
          eapply IHrvs in HeqR; eauto.

      destruct Hin as [Hin | Hin].
        inv Hin. 
        eapply IHrvs in HeqR; eauto.
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
          eapply updateValuesForNewBlock_spec2 in J; eauto.

          symmetry in HeqR0.
          eapply updateValuesForNewBlock_spec1 in HeqR0; eauto.
          destruct HeqR0 as [omd HeqR0].
          apply Hprop with (gv1:=gvx)(opmd1:=omd) in Htyp; eauto.
            destruct omd as [[md1 mt1]|]; try solve [contradict Htyp; auto].
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
          eapply updateValuesForNewBlock_spec2 in J; eauto.

          symmetry in HeqR0.
          eapply updateValuesForNewBlock_spec1 in HeqR0; eauto.
          destruct HeqR0 as [omd HeqR0].
          eapply Hprop with (gv1:=gvx)(opmd1:=omd) in Htyp; eauto.
            destruct omd as [[md1 mt1]|]; try solve [contradict Htyp; auto].
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

Lemma lookupTypViaIDFromFdef__lookupTypViaIDFromPhiNodes : forall F id1 t b1,
  uniqFdef F ->
  lookupTypViaIDFromFdef F id1 = Some t ->
  blockInFdefB b1 F ->
  In id1 (getPhiNodesIDs (getPHINodesFromBlock b1)) ->
  lookupTypViaIDFromPhiNodes (getPHINodesFromBlock b1) id1 = Some t. 
Admitted.

Lemma uniqFdef__uniqBlock : forall F b1,
  uniqFdef F -> blockInFdefB b1 F -> NoDup (getBlockLocs b1).
Proof.
  intros.
  destruct F. destruct f.
  destruct H as [H _]. simpl in H0. destruct H.
  apply NoDup__InBlocksB in H0; auto.
Qed.

Lemma switchToNewBasicBlock__wf_rmap : forall F TD M b1 b2 gl lc rm lc' rm',
  uniqFdef F ->
  blockInFdefB b1 F ->
  wf_rmap F lc rm ->
  switchToNewBasicBlock TD M b1 b2 gl lc rm = Some (lc', rm') ->
  wf_rmap F lc' rm'.
Proof.
  intros F TD M b1 b2 gl lc rm lc' rm' Huniq HBinF Hwfm Hswitch.
  unfold switchToNewBasicBlock in Hswitch.
  remember (getIncomingValuesForBlockFromPHINodes TD M 
             (getPHINodesFromBlock b1) b2 gl lc rm) as R.
  destruct R; inv Hswitch.
  eapply updateValuesForNewBlock__wf_rmap; eauto.
  intros.
  eapply getIncomingValuesForBlockFromPHINodes__wf_rmap with (t1:=t1); eauto.
    apply uniqFdef__uniqBlock in HBinF; auto.
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

Lemma initLocals__wf_rmap : forall ogvs rm lc' rm' fa rt fid la va lb lp TD
    Mem0 gl lc,
  params2GVs TD Mem0 lp lc gl rm = ret ogvs ->
  initLocals la ogvs rm = (lc', rm') ->
  wf_rmap (fdef_intro (fheader_intro fa rt fid la va) lb) lc' rm'.
Admitted.

Lemma wf_State__cmd__lookupTypViaIDFromFdef : forall S,
  wf_State S ->
  match S with 
  | {| ECS := {|CurFunction := F; CurCmds := c :: cs |} :: EC |} =>
      forall id0, getCmdID c = Some id0 ->
      lookupTypViaIDFromFdef F id0 = getCmdTyp c
  | _ => True
  end.
Admitted.

Ltac preservation_tac HwfS1 :=
  eapply preservation_cmd_updated_case in HwfS1; simpl; try solve [
      eauto | 
      intro J;
      apply updateAddAL_nptr__wf_rmap; try solve [auto |
        apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1;
        rewrite HwfS1; simpl; try solve [auto | congruence]]
    ].

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
Admitted.

Lemma preservation : forall S1 S2 tr,
  SBopsem.dsInsn S1 S2 tr -> wf_State S1 -> wf_State S2.
Proof.
  intros S1 S2 tr HdsInsn HwfS1.
  (sb_dsInsn_cases (induction HdsInsn) Case); destruct TD as [los nts];
    try invert_prop_reg_metadata.
Focus.
Case "dsReturn".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [Hwfm1 [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hinscope2 [Hwfm2 [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]]; subst.
  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return rid RetTy Result))
             (insn_return rid RetTy Result)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  SCase "1".
    split; auto.
    split; auto.  
    split; auto. 
    split; auto.
    split; auto.
    assert (Hwfc := HBinF2).
    assert (In c' (cs2'++[c']++cs')) as HinCs.
      apply in_or_app. right. simpl. auto.
    eapply wf_system__wf_cmd with (c:=c') in Hwfc; eauto.
    split.
    SSCase "1.1".
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
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        unfold SBopsem.returnUpdateLocals in H1. simpl in H1.
        destruct R.
          destruct n; inv HeqR.
          remember (getOperandValue (los,nts) Mem' Result lc gl) as R1.
          destruct R1; inv H1.          
          inv Hwfc. 
          remember (SBopsem.get_reg_metadata (los, nts) Mem' gl rm Result) 
            as R2.
          unfold SBopsem.prop_reg_metadata in H3.
          assert (wf_defs F' (updateAddAL GenericValue lc' i0 g) ids2) as J.
            eapply wf_defs_updateAddAL with (t1:=typ1) ; eauto.
              eapply uniqF__lookupTypViaIDFromFdef; eauto.
                eapply wf_system__uniqFdef; eauto.
          destruct typ1; inv H3; auto.
            destruct (get_reg_metadata (los, nts) Mem' gl rm Result) as 
              [[md ?]|]; inv H2; auto.

          destruct n; inv HeqR. inv H1.
          eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsLocs (cs2' ++ [c'] ++ [c] ++ cs'))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        unfold SBopsem.returnUpdateLocals in H1. simpl in H1.
        destruct R.
          destruct n; inv HeqR.
          remember (getOperandValue (los,nts) Mem' Result lc gl) as R1.
          destruct R1; inv H1.
          inv Hwfc.
          remember (SBopsem.get_reg_metadata (los, nts) Mem' gl rm Result) 
            as R2.
          unfold SBopsem.prop_reg_metadata in H3.
          assert (wf_defs F' (updateAddAL GenericValue lc' i0 g) ids2) as J.
            eapply wf_defs_updateAddAL with (t1:=typ1) ; eauto.
              eapply uniqF__lookupTypViaIDFromFdef; eauto.
                eapply wf_system__uniqFdef; eauto.
          destruct typ1; inv H3; auto.
            destruct (get_reg_metadata (los, nts) Mem' gl rm Result) as 
              [[md ?]|]; inv H2; auto.

          destruct n; inv HeqR. inv H1.
          eapply wf_defs_eq; eauto. 

    split.
    SSCase "1.2".
      clear HeqR2 HwfCall HwfCall' HinCs Hreach2 HwfEC H0 Hwfg H Hreach1 HBinF1.
      clear HeqR1 Hinscope1 Hinscope2 HFinPs1 Hwfm1.
      eapply returnUpdateLocals__wf_rmap; eauto.

    SSCase "1.3".
      exists l2. exists ps2. exists (cs2'++[c']).   
      simpl_env. auto.
Unfocus.

Focus.
Case "dsReturnVoid".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [Hwfm1 [l1 [ps1 [cs1' Heq1]]]]]]]]
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hinscope2 [Hwfm2 [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]]; subst.
  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return_void rid))
             (insn_return_void rid)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
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
    SSCase "1.3".
      exists l2. exists ps2. exists (cs2'++[c']).   
      simpl_env. auto.
Unfocus.

Focus.
Case "dsBranch".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [Hwfm1 [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]]
    ]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br bid Cond l1 l2))
             (insn_br bid Cond l1 l2)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split; auto.
  split; auto.
    assert (uniqFdef F) as HuniqF.
      eapply wf_system__uniqFdef in HwfSystem; eauto.   
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
      assert (HwfF := HwfSystem).
      eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
      clear - H0 HeqR1 H1 Hinscope1 H HwfSystem HBinF1 HwfF HuniqF.
      eapply inscope_of_tmn_br in HeqR1; eauto.
        destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
        destruct cs'; rewrite <- HeqR1; eauto.

        eapply switchToNewBasicBlock_sim; eauto.

    split.
      clear HwfEC Hreach1 HwfCall Hwfg HeqR1 Hinscope1 H.
      eapply switchToNewBasicBlock__wf_rmap with 
        (b1:=block_intro l' ps' cs' tmn')
        (b2:=block_intro l3 ps3 (cs3' ++ nil) (insn_br bid Cond l1 l2)); eauto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Focus.
Case "dsBranch_uncond".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [Hwfm1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
     [HwfEC HwfCall]]]]
    ]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br_uncond bid l0))
             (insn_br_uncond bid l0)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split; auto.
  SCase "1".
    assert (uniqFdef F) as HuniqF.
      eapply wf_system__uniqFdef in HwfSystem; eauto.   
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
    split.
      assert (HwfF := HwfSystem).
      eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
      clear - H0 HeqR1 Hinscope1 HwfSystem HBinF1 HwfF HuniqF HBinF H.
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

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Case "dsBop". preservation_tac HwfS1.
Case "dsFBop". preservation_tac HwfS1. 
Case "dsExtractValue".
  assert (exists t0, getSubTypFromConstIdxs idxs t = Some t0) as J.
    destruct HwfS1 as 
      [Hwfg [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [Hwfm1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
         [HwfEC HwfCall]]]]
      ]; subst.
    eapply wf_system__wf_cmd with (c:=insn_extractvalue id0 t v idxs) in HBinF1; 
      eauto.
      inv HBinF1; eauto.
      apply in_or_app; simpl; auto.

  destruct J as [t0 J].
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1.
      rewrite HwfS1; simpl; auto. 
        rewrite J. 
          admit. (* unsupported *)
Case "dsInsertValue". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    intro J. 
    apply updateAddAL_nptr__wf_rmap; auto.
      apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1.
      rewrite HwfS1; simpl; auto. 
        admit. (* unsupported *)
Case "dsMalloc". 
  eapply preservation_cmd_updated_case with (rm':=
          updateAddAL SBopsem.metadata rm id0
            {| SBopsem.md_base := SBopsem.base2GV (los, nts) mb;
               SBopsem.md_bound := SBopsem.bound2GV (los, nts) mb tsz n |})
   in HwfS1; simpl; eauto.
    apply updateAddAL_ptr__wf_rmap; auto. 
Case "dsFree". 
  eapply preservation_cmd_non_updated_case with (MM':=MM) in HwfS1; eauto.
Case "dsAlloca".
  eapply preservation_cmd_updated_case with (rm':=
          updateAddAL SBopsem.metadata rm id0
            {| SBopsem.md_base := SBopsem.base2GV (los, nts) mb;
               SBopsem.md_bound := SBopsem.bound2GV (los, nts) mb tsz n |})
   in HwfS1; simpl; eauto.
    apply updateAddAL_ptr__wf_rmap; auto. 
Case "dsLoad_nptr". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1.
      rewrite HwfS1; simpl; auto. 
        intros t0 EQ. inv EQ. inv H3.
Case "dsLoad_ptr".
  eapply preservation_cmd_updated_case with (rm':=updateAddAL metadata rm id0
    (get_mem_metadata (los, nts) MM gvp)) in HwfS1; simpl; eauto.
    apply updateAddAL_ptr__wf_rmap; auto. 
Case "dsStore_nptr". 
  eapply preservation_cmd_non_updated_case with (MM':=MM) in HwfS1; eauto.
Case "dsStore_ptr". 
  eapply preservation_cmd_non_updated_case with (MM':=MM') in HwfS1; eauto.
Case "dsGEP". 
  assert (exists t0, getGEPTyp idxs t = Some t0) as J.
    destruct HwfS1 as 
      [Hwfg [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [Hwfm1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
         [HwfEC HwfCall]]]]
      ]; subst.
    eapply wf_system__wf_cmd with(c:=insn_gep id0 inbounds0 t vp idxs) in HBinF1;
      eauto.
      inv HBinF1; eauto.
      apply in_or_app; simpl; auto.
  destruct J as [t0 J].
  eapply preservation_cmd_updated_case with 
    (rm':=updateAddAL SBopsem.metadata rm id0 md) in HwfS1; simpl; eauto.
    apply updateAddAL_ptr__wf_rmap; auto.
Case "dsTrunc".
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. inv H6; congruence.
Case "dsExt". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. inv H6; congruence.
Case "dsBitcast_nptr". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. inv H7; try congruence.
          inv H0.
Case "dsBitcast_ptr". 
  eapply preservation_cmd_updated_case with (rm':=updateAddAL metadata rm id0 md)
    in HwfS1; simpl; eauto.
    apply updateAddAL_ptr__wf_rmap; auto.
Case "dsInttoptr". 
  eapply preservation_cmd_updated_case with (rm':=
    updateAddAL SBopsem.metadata rm id0 
      {| SBopsem.md_base := null;
         SBopsem.md_bound := null |}) in HwfS1; simpl; eauto.
    apply updateAddAL_ptr__wf_rmap; auto.
Case "dsOthercast". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
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
    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. congruence.
Case "dsFcmp". 
  eapply preservation_cmd_updated_case with (rm':=rm) in HwfS1; simpl; eauto.
    intro J0. 
    apply updateAddAL_nptr__wf_rmap; auto.
      assert (Htyp:=HwfS1).
      apply wf_State__cmd__lookupTypViaIDFromFdef in Htyp.
      rewrite Htyp; simpl; auto. 
        apply wf_State__wf_cmd in HwfS1.
        inv HwfS1. congruence.
Case "dsSelect_nptr".
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
  destruct (isGVZero (los, nts) c); try invert_prop_reg_metadata.
    eapply preservation_cmd_updated_case with 
      (rm':=updateAddAL metadata rm id0 md2) in HwfS1; simpl; 
      try solve [eauto | apply updateAddAL_ptr__wf_rmap; auto].
    eapply preservation_cmd_updated_case with 
      (rm':=updateAddAL metadata rm id0 md1) in HwfS1; simpl; 
      try solve [eauto | apply updateAddAL_ptr__wf_rmap; auto].

Focus.
Case "dsCall".
  destruct HwfS1 as [Hwfg [HwfSys [HmInS [HwfEC [HwfECs HwfCall]]]]].
  assert (InProductsB (product_fdef (fdef_intro 
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    eapply lookupFdefViaGV_inv; eauto.
  split; auto.
  split; auto.
  split; auto.
  split.
  SCase "1".     
    split.
      simpl. eapply reachable_entrypoint; eauto.
    split.
     apply entryBlockInFdef in H0; auto.
    split; auto.
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
       destruct HwfEC as [Hreach [HBinF [HFinPs [Hinscope [l1 [ps [cs' Heq]]]]]]]
         ; subst.       
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

      exists l'. exists ps'. exists nil. simpl_env. auto.
  split.
  SCase "2".
    split; auto.
  SCase "3".
    simpl. intros b HbInBs. destruct b.
    destruct t; auto.

Unfocus.

Case "dsExCall". 
  unfold exCallUpdateLocals in H2.
  destruct noret0.
    inv H2.
    eapply preservation_cmd_non_updated_case with (MM':=MM) in HwfS1; eauto.

    destruct oresult; inv H2.
    assert (exists t0, getCmdTyp (insn_call rid false ca ft fv lp) = Some t0)
      as J.
      destruct HwfS1 as 
        [Hwfg [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [Hwfm1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
         [HwfEC HwfCall]]]]
        ]; subst.
      eapply wf_system__wf_cmd with (c:=insn_call rid false ca ft fv lp) 
        in HBinF1; eauto.
      simpl.
      inv HBinF1; eauto. 
      apply in_or_app; simpl; auto.

    destruct J as [t0 J].
    destruct ft; inv H4; try solve [
      eapply preservation_cmd_updated_case with (t0:=t0)(rm':=rm') in HwfS1; 
        try solve [eauto |
          intro J0;
          apply updateAddAL_nptr__wf_rmap; try solve [auto |
            apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1;
            rewrite HwfS1; simpl; try solve [auto | congruence]]
        ]
    ].    
    destruct ft; inv H3; try solve [
      eapply preservation_cmd_updated_case with (t0:=t0)
        (rm':=updateAddAL metadata rm rid
          {| md_base := gundef; md_bound := gundef |}) in HwfS1; 
        try solve [eauto | intro J0; apply updateAddAL_ptr__wf_rmap; auto] |
      eapply preservation_cmd_updated_case with (t0:=t0)(rm':=rm') in HwfS1; 
        try solve [eauto |
          intro J0;
          apply updateAddAL_nptr__wf_rmap; try solve [auto |
            apply wf_State__cmd__lookupTypViaIDFromFdef in HwfS1;
            rewrite HwfS1; simpl; try solve [auto | congruence]]
        ]
    ].
Qed.

(*********************************************)
(** * Progress *)

Definition memory_violation S : Prop :=
  match S with
  | {| SBopsem.CurTargetData := TD;
       SBopsem.ECS := {| SBopsem.CurCmds := insn_load _ t vp _ :: cs;
                           SBopsem.Locals := lc;
                           SBopsem.Rmap := rm
                         |} :: _;
        SBopsem.Globals := gl;
        SBopsem.Mem := Mem0 |} => 
      match SBopsem.get_reg_metadata TD Mem0 gl rm vp, 
            getOperandValue TD Mem0 vp lc gl with
      | ret (md, mt), ret gvp => ~ SBopsem.assert_mptr TD t gvp md
      | _, _ => False
      end
  | {| SBopsem.CurTargetData := TD;
       SBopsem.ECS := {| SBopsem.CurCmds := insn_store _ t v vp _ :: cs;
                           SBopsem.Locals := lc;
                           SBopsem.Rmap := rm
                         |} :: _;
        SBopsem.Globals := gl;
        SBopsem.Mem := Mem0 |} => 
      match SBopsem.get_reg_metadata TD Mem0 gl rm vp, 
            getOperandValue TD Mem0 vp lc gl with
      | ret (md, mt), ret gvp => ~ SBopsem.assert_mptr TD t gvp md
      | _, _ => False
      end
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
       match getOperandValue td M v lc gl with
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
       match getOperandValue td M v lc gl with
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
       match getOperandValue td M v lc gl with
       | Some gv =>
           match mload td M gv t a with
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
         {| SBopsem.CurCmds := insn_store _ t v v0 a::_ ; 
            SBopsem.Locals := lc|} :: _;
       SBopsem.Globals := gl;
       SBopsem.Mem := M |} =>
       match getOperandValue td M v lc gl, getOperandValue td M v0 lc gl with
       | Some gv, Some mgv =>
           match mstore td M mgv t gv a with
           | None => True
           | _ => False
           end
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
       match lookupFdefViaGV td M ps gl lc fs v, 
             lookupExFdecViaGV td M ps gl lc fs v with
       | None, Some (fdec_intro (fheader_intro fa rt fid la va)) =>
           match LLVMgv.params2GVs td M p lc gl with
           | Some gvs =>
             match LLVMopsem.callExternalFunction M fid gvs with
             | (oresult, _) =>
                match exCallUpdateLocals ft n i0 oresult lc rm with
                | None => True
                | _ => False
                end
             end
           | _ => False
           end
       | None, None => True
       | _, _ => False
       end
  | _ => False
  end \/
  memory_violation S.

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

Hint Constructors SBopsem.dsInsn.

Lemma assert_mptr_dec : forall TD t ptr md,
  SBopsem.assert_mptr TD t ptr md \/ ~ SBopsem.assert_mptr TD t ptr md.
Proof.
  intros.
  unfold is_true. 
  destruct (SBopsem.assert_mptr TD t ptr md); auto.
Qed.

Lemma get_const_metadata_isnt_stuck : forall TD M gl vc gv bc ec t1,
  const2GV TD M gl vc = Some gv ->
  get_const_metadata vc = Some (bc, ec, t1) ->
  exists gvb, exists gve, 
    const2GV TD M gl bc = Some gvb /\ const2GV TD M gl ec = Some gve.
Proof.
  unfold const2GV.
  intros TD M gl vc gv bc ec t1 J1 J2.  
  remember (_const2GV TD M gl vc) as J3.
  destruct J3 as [[gv3 t3]|]; inv J1.
  generalize dependent gv.
  generalize dependent t3.
  generalize dependent ec.
  generalize dependent bc.
  generalize dependent t1.
  induction vc; intros; try solve [inversion J2].
    exists gv.
    remember t as T.
    destruct T; inversion J2; clear J2; subst bc ec t1; simpl in *; try solve [
      destruct (lookupAL GenericValue gl i0); inversion HeqJ3; subst gv t3;
      destruct (GV2ptr TD (getPointerSize TD) g); eauto;
      remember (mgep TD t v 
        (INTEGER.to_Z (INTEGER.of_Z 32 1 false) :: nil)) as optr;
      subst t; rewrite <- Heqoptr;
      destruct optr; eauto
    ].

    simpl in *.
    destruct c; try solve [inversion J2].
    destruct t; inv J2.
    remember (_const2GV TD M gl vc) as R.
    destruct R as [[gv2 t2]|]; try solve [inv HeqJ3].
    destruct (mcast TD M castop_bitcast t2 gv2 (typ_pointer t)); 
      try solve [inv HeqJ3].
    apply IHvc with (gv:=gv2)(t3:=t2) in H0; auto.
    
    simpl in *.
    remember (_const2GV TD M gl vc) as R.
    destruct R as [[gv2 t2]|]; try solve [inv HeqJ3].
    apply IHvc with (gv:=gv2)(t3:=t2) in J2; auto.
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
  (M : mem)
  (t : list atom)
  l1 ps1 cs1 tmn1
  (Hwfg : wf_global s gl)
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : wf_defs f lc t)
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
   exists RVs : list (id * GenericValue * option (metadata * typ)),
     getIncomingValuesForBlockFromPHINodes (los, nts) M ps2 
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
      destruct (@const2GV_isnt_stuck (los,nts) s M gl vc t0); auto.
      rewrite H.
      apply IHps2 in H7; eauto.
        destruct H7 as [RVs H7].
        rewrite H7. 
        remember (get_const_metadata vc) as R.
        destruct R as [[[bc ec] tc]|].
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
  (M : mem)
  (Hwfg1 : wf_global s gl)
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
  (Hinscope : wf_defs f lc l0)
  rm (Hwfm : wf_rmap f lc rm)
  (Hex : exists p21, p2 = p21 ++ p22),
  exists gvs, params2GVs (los, nts) M p22 lc gl rm = Some gvs.
Proof.
  induction p22; intros; simpl; eauto.

    destruct a.
    destruct Hex as [p21 Hex]; subst.
    assert (exists gv, getOperandValue (los, nts) M v0 lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl. unfold valueInParams. right. 
        assert (J:=@in_split_r _ _ (p21 ++ (t0, v0) :: p22) (t0, v0)).
        remember (split (p21 ++ (t0, v0) :: p22)) as R.
        destruct R.
        simpl in J. apply J.
        apply In_middle.
    destruct J as [gv J]. 
    rewrite J.         
    eapply IHp22 with (M:=M) in HbInF; eauto.  
      destruct HbInF as [vidxs HbInF].
      rewrite HbInF.
      remember (isPointerTypB t0) as R.
      destruct R; eauto.

      exists (p21 ++ [(t0,v0)]). simpl_env. auto.
Qed.

Lemma progress : forall S1,
  wf_State S1 -> 
  SBopsem.ds_isFinialState S1 = true \/ 
  (exists S2, exists tr, SBopsem.dsInsn S1 S2 tr) \/
  undefined_state S1.
Proof.
  intros S1 HwfS1.
  destruct S1 as [s [los nts] ps ecs gl fs M].
  destruct HwfS1 as [Hwfg1 [HwfSys1 [HmInS1 HwfECs]]].
  destruct ecs; try solve [inversion HwfECs].
  destruct e as [f b cs tmn lc rm als].
  destruct HwfECs as [[Hreach [HbInF [HfInPs [Hinscope [Hwfm 
                        [l1 [ps1 [cs1 Heq]]]]]]]]
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
            M' (insn_call i1 n c t0 v0 p) v lc lc' rm rm' gl = Some (lc'',rm'')) 
            as Hretup.
          unfold SBopsem.returnUpdateLocals.
          destruct n; eauto.
          assert (exists gv : GenericValue, 
            getOperandValue (los, nts) M' v lc gl = ret gv) as H.
            eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
              simpl. auto.
          destruct H as [gv H]. rewrite H.
          destruct t0; eauto.
          destruct t0; eauto.
          unfold SBopsem.prop_reg_metadata.            
          destruct (SBopsem.get_reg_metadata (los, nts) M' gl rm v) as 
            [[md ?]|]; eauto.
         
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
      assert (exists c, getOperandValue (los,nts) M v lc gl = Some c) as Hget.
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
      assert (exists lc', exists rm', SBopsem.switchToNewBasicBlock (los, nts) M
        (block_intro l' ps' cs' tmn') 
        (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l2 l3)) gl lc rm = 
          Some (lc', rm')) as Hswitch.
         assert (exists RVs, 
           SBopsem.getIncomingValuesForBlockFromPHINodes (los, nts) M ps'
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

      assert (exists lc', exists rm', switchToNewBasicBlock (los, nts) M
        (block_intro l2 ps' cs' tmn') 
        (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc rm = 
          Some (lc', rm')) as Hswitch.
         assert (exists RVs, 
           getIncomingValuesForBlockFromPHINodes (los, nts) M ps'
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
    assert (exists gv3, BOP (los,nts) M lc gl b s0 v v0 = Some gv3) as Hinsn_bop.
      unfold BOP.      
      assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, getOperandValue (los, nts) M v0 lc gl = Some gv) as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
          destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0. 
      unfold mbop. 
      destruct (GV2val (los, nts) gv); eauto.
      destruct v1; eauto.
      destruct (GV2val (los, nts) gv0); eauto.
      destruct v1; eauto.
      destruct (eq_nat_dec (wz + 1) (Size.to_nat s0)); eauto.
      destruct b; eauto.
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
    assert (exists gv3, FBOP (los,nts) M lc gl f0 f1 v v0 = Some gv3) 
      as Hinsn_fbop.
      unfold FBOP.      
      assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, getOperandValue (los, nts) M v0 lc gl = Some gv) as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0. 
      unfold mfbop. 
      destruct (GV2val (los, nts) gv); eauto.
      destruct v1; eauto.
      destruct (GV2val (los, nts) gv0); eauto.
      destruct v1; eauto.
      inv Hwfc.
      apply wf_value__wf_typ in H7.
      destruct H7 as [J1 J2].
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
    assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', extractGenericValue (los, nts) t gv l2 = Some gv') as J'.
      unfold extractGenericValue.
      destruct (intConsts2Nats (los, nts) l2); eauto.
      destruct (mgetoffset (los, nts) t l3); eauto.
      destruct (mget (los, nts) gv i1 t); eauto.
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
    assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', getOperandValue (los, nts) M v0 lc gl = Some gv') as J'.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J' as [gv' J'].
    assert (exists gv'', insertGenericValue (los, nts) t gv l2 t0 gv' = 
      Some gv'') as J''.
      unfold insertGenericValue.
      destruct (intConsts2Nats (los, nts) l2); eauto.
      destruct (mgetoffset (los, nts) t l3); eauto.
      destruct (mset (los, nts) gv i1 t0 gv'); eauto.
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
    apply feasible_typ_inv in H.
    destruct H as [ssz [asz [J1 J2]]].
    assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
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
    assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
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
    apply feasible_typ_inv in H.
    destruct H as [ssz [asz [J1 J2]]].
    assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
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
    assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    remember (mload (los, nts) M gv t a) as R.
    destruct R as [gv'|].
    SSCase "load ok".
      assert (exists omd, SBopsem.get_reg_metadata (los, nts) M gl rm v = 
        Some omd) as J2.
        clear - Hwfm J HbInF Hwfc.
        destruct v; simpl in *.
          assert (exists md, lookupAL metadata rm i1 = Some md) as J0.
            eapply Hwfm with (t1:=t); eauto.
              inv Hwfc. inv H6; auto.
          destruct J0 as [md J0].
          rewrite J0; eauto.

          remember (get_const_metadata c) as R.
          destruct R as [[[bc ec] tc]|]; eauto.
            eapply get_const_metadata_isnt_stuck in J; eauto.
            destruct J as [gvb [gve [Hc1 Hc2]]].
            rewrite Hc1. rewrite Hc2. simpl.
            eauto.
      destruct J2 as [[md mt] J2].
      destruct (assert_mptr_dec (los, nts) t gv md) as [J3 | J3].
      SSSCase "assert ok".
        remember (isPointerTypB t) as R1.
        destruct R1.      
          SSSSCase "load_ptr".
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

          SSSSCase "load_nptr".
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

      SSSCase "assert fails".
        right.
        unfold undefined_state. unfold memory_violation.
        right. rewrite J. rewrite J2. undefbehave.

    SSCase "load fails".
      right.
      unfold undefined_state.
      right. rewrite J. rewrite <- HeqR0. undefbehave.

  SCase "store".
    assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv, getOperandValue (los, nts) M v0 lc gl = Some gv) as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [mgv J0].
    remember (mstore (los, nts) M mgv t gv a) as R.
    destruct R as [M'|].
    SSCase "store ok".
      assert (exists omd, SBopsem.get_reg_metadata (los, nts) M gl rm v0 = 
        Some omd) as J2.
        clear - Hwfm J0 HbInF Hwfc.
        destruct v0; simpl in *.
          assert (exists md, lookupAL metadata rm i1 = Some md) as J1.
            eapply Hwfm with (t1:=t); eauto.
              inv Hwfc. inv H10; eauto.
          destruct J1 as [md J1].
          rewrite J1; eauto.

          remember (get_const_metadata c) as R.
          destruct R as [[[bc ec] tc]|]; eauto.
            eapply get_const_metadata_isnt_stuck in J0; eauto.
            destruct J0 as [gvb [gve [Hc1 Hc2]]].
            rewrite Hc1. rewrite Hc2. simpl.
            eauto.
      destruct J2 as [[md mt] J2].
      destruct (assert_mptr_dec (los, nts) t mgv md) as [J3 | J3].
      SSSCase "assert ok".
        remember (isPointerTypB t) as R1.
        destruct R1.      
        SSSSCase "store_ptr".
          assert (exists omd, SBopsem.get_reg_metadata (los, nts) M gl rm v = 
            Some omd) as J4.
            clear - Hwfm J HbInF Hwfc HeqR1.
            destruct v; simpl in *.
              assert (exists md, lookupAL metadata rm i1 = Some md) as J1.
                destruct t; try solve [inversion HeqR1].
                eapply Hwfm with (t1:=t); eauto.
                  inv Hwfc. inv H7; eauto.
              destruct J1 as [md J1].
              rewrite J1; eauto.

              remember (get_const_metadata c) as R.
              destruct R as [[[bc ec] tc]|]; eauto.
                eapply get_const_metadata_isnt_stuck in J; eauto.
                destruct J as [gvb [gve [Hc1 Hc2]]].
                rewrite Hc1. rewrite Hc2. simpl.
                eauto.
          destruct J4 as [[md' mt'] J4].
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

        SSSSCase "store_nptr".
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

      SSSCase "assert fails".
        right.
        unfold undefined_state. unfold memory_violation.
        right. rewrite J0. rewrite J2. undefbehave.

    SSCase "store fails".
      right.
      unfold undefined_state.
      right. rewrite J. rewrite J0. rewrite <- HeqR0. undefbehave.

  SCase "gep".
    assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [mp J].
    assert (exists vidxs, values2GVs (los, nts) M l2 lc gl = Some vidxs) as J2.
      eapply values2GVs_isnt_stuck; eauto.
        exists Nil_list_value. auto.
    destruct J2 as [vidxs J2].
    assert (exists mp', GEP (los, nts) t mp vidxs i1 = Some mp') as J3.
      unfold GEP.
      destruct (GV2ptr (los, nts) (getPointerSize (los, nts)) mp); eauto.
      destruct (GVs2Nats (los, nts) vidxs); eauto.
      destruct (mgep (los, nts) t v0 l3); eauto.
    destruct J3 as [mp' J3].
    left.
    assert (exists omd, SBopsem.get_reg_metadata (los, nts) M gl rm v = 
      Some omd) as J4.
      clear - Hwfm J HbInF Hwfc.
      destruct v; simpl in *.
        assert (exists md, lookupAL metadata rm i2 = Some md) as J0.
          eapply Hwfm with (t1:=t); eauto.
            inv Hwfc. inv H9; auto.
        destruct J0 as [md J0].
        rewrite J0; eauto.

        remember (get_const_metadata c) as R.
        destruct R as [[[bc ec] tc]|]; eauto.
          eapply get_const_metadata_isnt_stuck in J; eauto.
          destruct J as [gvb [gve [Hc1 Hc2]]].
          rewrite Hc1. rewrite Hc2. simpl.
          eauto.
    destruct J4 as [[md mt] J4].
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
    assert (exists gv2, TRUNC (los,nts) M lc gl t t0 v t1 = Some gv2) 
      as Hinsn_trunc.
      unfold TRUNC.      
      assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      unfold mtrunc. 
      destruct (GV2val (los, nts) gv); eauto.
      inv Hwfc. 
      inv H5; try solve [destruct v0; eauto].
        rewrite H11.
        destruct v0; eauto.
          destruct floating_point2; try solve [eauto | inversion H13].
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
    assert (exists gv2, EXT (los,nts) M lc gl e t v t0 = Some gv2) 
      as Hinsn_ext.
      unfold EXT.      
      assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      unfold mext. 
      inv Hwfc. 
      inv H5; try solve 
        [destruct (GV2val (los, nts) gv); eauto; destruct v0; eauto].
        rewrite H11.
        destruct (GV2val (los, nts) gv); eauto; destruct v0; eauto.
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
    assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv2, CAST (los,nts) M lc gl c t v t0 = Some gv2) 
      as Hinsn_cast.
      unfold CAST.      
      rewrite J.
      unfold mcast, mptrtoint.
      inv Hwfc. 
      inv H5; eauto.
        destruct (GV2val (los, nts) gv); eauto.
        destruct v0; eauto.
        destruct (Mem.ptr2int M b 0); eauto.

        destruct (GV2val (los, nts) gv); eauto.
        destruct v0; eauto.
        destruct (Mem.int2ptr M (Int.signed wz i1)); eauto.
        destruct p; eauto.

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

        assert (exists omd, SBopsem.get_reg_metadata (los, nts) M gl rm v = 
          Some omd) as J4.
          clear - Hwfm J HbInF Hwfc HeqR0. 
          destruct v; simpl in *.
            assert (exists md, lookupAL metadata rm i1 = Some md) as J0.
              destruct t; try solve [inversion HeqR0].
              eapply Hwfm with (t1:=t); eauto.
                inv Hwfc. 
                inv H5.
                  inv H7; auto.
                  inv H8; auto.
            destruct J0 as [md J0].
            rewrite J0; eauto.

            remember (get_const_metadata c) as R.
            destruct R as [[[bc ec] tc]|]; eauto.
              eapply get_const_metadata_isnt_stuck in J; eauto.
              destruct J as [gvb [gve [Hc1 Hc2]]].
              rewrite Hc1. rewrite Hc2. simpl.
              eauto.
        destruct J4 as [[md mt] J4].
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
    assert (exists gv2, ICMP (los,nts) M lc gl c t v v0 = Some gv2) 
      as Hinsn_icmp.
      unfold ICMP.      
      assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, getOperandValue (los, nts) M v0 lc gl = Some gv) as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0.
      unfold micmp.
      inv Hwfc. 
      unfold isPointerTyp in H11. unfold is_true in H11.
      unfold micmp_int.
      destruct H11 as [H11 | H11].
        destruct t; try solve [simpl in H11; contradict H11; auto].
        destruct (GV2val (los,nts) gv); eauto.
        destruct v1; eauto.
        destruct (GV2val (los,nts) gv0); eauto.
        destruct v1; eauto.
        destruct c; eauto.

        destruct t; try solve [simpl in H11; contradict H11; auto].
        destruct (mptrtoint (los, nts) M gv Size.ThirtyTwo); eauto.
        destruct (mptrtoint (los, nts) M gv0 Size.ThirtyTwo); eauto.
        destruct (GV2val (los, nts) g); eauto.
        destruct v1; eauto.
        destruct (GV2val (los, nts) g0); eauto.
        destruct v1; eauto.
        destruct c; eauto.
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
    assert (exists gv2, FCMP (los,nts) M lc gl f0 f1 v v0 = Some gv2) 
      as Hinsn_fcmp.
      unfold FCMP.      
      assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, getOperandValue (los, nts) M v0 lc gl = Some gv) as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0.
      unfold mfcmp.
      inv Hwfc. 
      destruct (GV2val (los, nts) gv); eauto.
      destruct v1; eauto.
      destruct (GV2val (los, nts) gv0); eauto.
      destruct v1; eauto.
      apply wf_value__wf_typ in H10.
      destruct H10 as [J1 J2].
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
    assert (exists gv, getOperandValue (los, nts) M v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv0, getOperandValue (los, nts) M v0 lc gl = Some gv0) as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [gv0 J0].
    assert (exists gv1, getOperandValue (los, nts) M v1 lc gl = Some gv1) as J1.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J1 as [gv1 J1].
    left.
    remember (isPointerTypB t) as R.
    destruct R.
    SSCase "select_ptr".
      assert (exists omd, SBopsem.get_reg_metadata (los, nts) M gl rm v0 = 
          Some omd) as J2.
        clear - Hwfm J0 HbInF Hwfc HeqR0. 
        destruct v0; simpl in *.
          assert (exists md, lookupAL metadata rm i1 = Some md) as J0'.
            destruct t; try solve [inversion HeqR0].
            eapply Hwfm with (t1:=t); eauto.
              inv Hwfc. inv H11; auto.
          destruct J0' as [md J0'].
          rewrite J0'; eauto.

          remember (get_const_metadata c) as R.
          destruct R as [[[bc ec] tc]|]; eauto.
            eapply get_const_metadata_isnt_stuck in J0; eauto.
            destruct J0 as [gvb [gve [Hc1 Hc2]]].
            rewrite Hc1. rewrite Hc2. simpl.
            eauto.
      destruct J2 as [[md0 mt0] J2].
      assert (exists omd, SBopsem.get_reg_metadata (los, nts) M gl rm v1 = 
          Some omd) as J3.
        clear - Hwfm J1 HbInF Hwfc HeqR0. 
        destruct v1; simpl in *.
          assert (exists md, lookupAL metadata rm i1 = Some md) as J0'.
            destruct t; try solve [inversion HeqR0].
            eapply Hwfm with (t1:=t); eauto.
              inv Hwfc. inv H12; auto.
          destruct J0' as [md J0'].
          rewrite J0'; eauto.

          remember (get_const_metadata c) as R.
          destruct R as [[[bc ec] tc]|]; eauto.
            eapply get_const_metadata_isnt_stuck in J1; eauto.
            destruct J1 as [gvb [gve [Hc1 Hc2]]].
            rewrite Hc1. rewrite Hc2. simpl.
            eauto.
      destruct J3 as [[md1 mt1] J3].
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
    remember (lookupFdefViaGV (los, nts) M ps gl lc fs v) as Hlk. 
    destruct Hlk as [f' |].
    SSCase "internal call".
    assert (exists gvs, params2GVs (los, nts) M p lc gl rm = Some gvs) as G.
      eapply params2GVs_isnt_stuck; eauto. 
        exists nil. auto.
    destruct G as [gvs G].
    destruct f' as [[fa rt fid la va] lb].
    assert (J:=HeqHlk).
    symmetry in HeqHlk.
    apply lookupFdefViaGV_inv in HeqHlk; auto.
    eapply wf_system__wf_fdef in HeqHlk; eauto.
    inv HeqHlk. destruct block5 as [l5 ps5 cs5 tmn5].
    left.
    remember (initLocals la gvs rm) as R.
    destruct R as [lc' rm'].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS :=(mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
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

    remember (lookupExFdecViaGV (los, nts) M ps gl lc fs v) as Helk. 
    destruct Helk as [f' |].
    SSCase "external call".
    assert (exists gvs, LLVMgv.params2GVs (los, nts) M p lc gl = Some gvs) 
      as G.
      eapply ssa_wf.params2GVs_isnt_stuck; eauto. 
        exists nil. auto.
    destruct G as [gvs G].
    destruct f' as [[fa rt fid la va]].
    remember (callExternalFunction M fid gvs) as R.
    destruct R as [oresult Mem'].
    remember (exCallUpdateLocals t n i0 oresult lc rm) as R'.
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
      right. rewrite <- HeqHlk. rewrite <- HeqHelk. rewrite G. rewrite <- HeqR0.
      rewrite <- HeqR'. undefbehave.

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
