Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
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
Require Import ssa_dynamic.
Require Import ssa_props.
Require Import ssa_analysis.
Require Import ssa_wf.
Require Import ndopsem.
Require Import ndopsem_dsop.

Export LLVMwf.
Export AtomSet.

(***************************)
(* domination prop *)

Export LLVMgv.
Export NDopsem.

Inductive wf_GVs : GVs -> typ -> Prop :=
| wf_GVs_intro : forall gvs t, Ensembles.Inhabited _ gvs -> wf_GVs gvs t.

Hint Constructors wf_GVs.

Inductive wf_defs (f:fdef) (lc:GVsMap) : list atom -> Prop :=
| wf_defs_nil : wf_defs f lc nil
| wf_defs_cons : forall id1 t1 gvs1 defs',
    lookupTypViaIDFromFdef f id1 = Some t1 ->
    lookupAL _ lc id1 = Some gvs1 -> 
    wf_GVs gvs1 t1 ->
    wf_defs f lc defs' ->
    wf_defs f lc (id1::defs').

Lemma wf_defs_elim : forall ids1 F lc,
  wf_defs F lc ids1 ->
  forall id1, In id1 ids1 ->
  exists t1, exists gvs1,
    lookupTypViaIDFromFdef F id1 = Some t1 /\
    lookupAL _ lc id1 = Some gvs1 /\
    wf_GVs gvs1 t1.
Proof.
  induction ids1; intros; simpl in H0; inv H0.  
    inv H.
    exists t1. exists gvs1. split; auto.

    inv H.
    eapply IHids1 in H6; eauto.
Qed.    

Lemma wf_defs_intro : forall ids1 F lc,
  (forall id1, In id1 ids1 ->
   exists t1, exists gvs1,
     lookupTypViaIDFromFdef F id1 = Some t1 /\
     lookupAL _ lc id1 = Some gvs1 /\
     wf_GVs gvs1 t1) ->
  wf_defs F lc ids1.
Proof.
  induction ids1; intros.
    apply wf_defs_nil.  

    destruct (@H a) as [t1 [gvs1 [J1 [J2 J3]]]]; simpl; auto.
    eapply wf_defs_cons; eauto.
      apply IHids1.
      intros id1 J.
      apply H. simpl. auto.
Qed.

Lemma wf_defs_eq : forall ids2 ids1 F' lc',
  set_eq _ ids1 ids2 ->
  wf_defs F' lc' ids1 ->
  wf_defs F' lc' ids2.
Proof.
  intros.
  apply wf_defs_intro.
  intros id1 Hin.
  destruct H as [J1 J2].
  eapply wf_defs_elim in H0; eauto.
Qed.

Lemma wf_defs_updateAddAL : forall g F' lc' ids1 ids2 i1 t1,
  wf_defs F' lc' ids1 ->
  set_eq _ (i1::ids1) ids2 ->
  lookupTypViaIDFromFdef F' i1 = ret t1 ->
  wf_GVs g t1 ->
  wf_defs F' (updateAddAL _ lc' i1 g) ids2.
Proof.
  intros g F' lc' ids1 ids2 i1 t1 HwfDefs Heq Hlkup Hwfgvs.  
  apply wf_defs_intro.  
  intros id1 Hin.
  destruct Heq as [Hinc1 Hinc2].
  apply Hinc2 in Hin.
  simpl in Hin.
  destruct (eq_dec i1 id1); subst.
    exists t1. exists g. 
    split; auto.
    split; auto. 
      apply lookupAL_updateAddAL_eq; auto.      

    destruct Hin as [Eq | Hin]; subst; try solve [contradict n; auto].
    eapply wf_defs_elim in HwfDefs; eauto.
    destruct HwfDefs as [t2 [gv2 [J1 [J2 J3]]]].
    exists t2. exists gv2.
    split; auto.
    split; auto. 
      rewrite <- lookupAL_updateAddAL_neq; auto.      
Qed.

Definition wf_lc (lc:GVsMap) : Prop :=
forall i0 gvs0, lookupAL _ lc i0 = Some gvs0 -> Ensembles.Inhabited _ gvs0. 

Lemma const2GV__inhabited : forall TD gl c gvs,
  const2GV TD gl c = Some gvs -> 
  Ensembles.Inhabited _ gvs.
Proof.
  intros TD gl c gvs H.
  unfold const2GV in H.
  destruct (_const2GV TD gl c) as [[gv ?]|]; inv H.
    eauto using cgv2gvs__inhabited.
Qed.

Lemma getOperandValue__inhabited : forall TD v lc gl gvs,
  wf_lc lc ->
  NDopsem.getOperandValue TD v lc gl = Some gvs ->
  Ensembles.Inhabited _ gvs.
Proof.
  intros TD v lc gl gvs Hwflc Hget.
  destruct v; simpl in Hget; eauto using const2GV__inhabited.
Qed.
    
Lemma getIncomingValuesForBlockFromPHINodes_spec1 : forall ps TD b gl lc lc'
    id1,
  wf_lc lc ->
  Some lc' = NDopsem.getIncomingValuesForBlockFromPHINodes TD ps b gl lc ->
  In id1 (getPhiNodesIDs ps) ->
  exists gvs, lookupAL _ lc' id1 = Some gvs /\ Ensembles.Inhabited _ gvs.  
Proof.    
  induction ps; intros TD b gl lc lc' id1 Hwflc H H0; simpl in *.
    inversion H0.

    destruct a.
    simpl in H0.
    destruct H0 as [H0 | H0]; subst.
      destruct (getValueViaBlockFromValuels l0 b); try solve [inversion H].   
        remember (NDopsem.getOperandValue TD v lc gl) as R.
        destruct R; inversion H; subst. 
        symmetry in HeqR. apply getOperandValue__inhabited in HeqR; auto.
        destruct (NDopsem.getIncomingValuesForBlockFromPHINodes TD ps b gl 
          lc); inversion H1; subst.         
        exists g. simpl. 
        destruct (id1==id1); auto.
          contradict n; auto.

      destruct (getValueViaBlockFromValuels l0 b); 
        try solve [inversion H].   
        remember (NDopsem.getOperandValue TD v lc gl) as R.
        destruct R; inversion H; subst. 
        symmetry in HeqR. apply getOperandValue__inhabited in HeqR; auto.
        remember (NDopsem.getIncomingValuesForBlockFromPHINodes TD ps b gl 
          lc) as R.
        destruct R; inversion H2; subst.         
        simpl.
        destruct (id1==i0); subst; eauto.
Qed.
    
Lemma updateValuesForNewBlock_spec1 : forall rs lc id1 gv,
  lookupAL _ rs id1 = Some gv ->
  lookupAL _ (NDopsem.updateValuesForNewBlock rs lc) id1 = Some gv.
Proof.  
  induction rs; intros; simpl in *.   
    inversion H.

    destruct a.
    destruct (id1==a); subst.
      inversion H; subst. apply lookupAL_updateAddAL_eq; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec2 : forall TD b gl lc 
  (Hwflc: wf_lc lc) ps rs,
  Some rs = NDopsem.getIncomingValuesForBlockFromPHINodes TD ps b gl lc ->
  (forall id0 gvs, In (id0,gvs) rs -> Ensembles.Inhabited _ gvs).
Proof.    
  induction ps; intros rs H id0 gvs Hin; simpl in *.
    inv H. inv Hin.

    destruct a.
    destruct (getValueViaBlockFromValuels l0 b); try solve [inversion H].   
      remember (NDopsem.getOperandValue TD v lc gl) as R.
      destruct R; tinv H.
      symmetry in HeqR. apply getOperandValue__inhabited in HeqR; auto.
      destruct (NDopsem.getIncomingValuesForBlockFromPHINodes TD ps b gl 
        lc); inv H.
      simpl in Hin. 
      destruct Hin as [Hin | Hin]; eauto.
        inv Hin; auto.
Qed.

Lemma updateValuesForNewBlock_spec2 : forall lc id1 gv,
  lookupAL _ lc id1 = Some gv ->
  wf_lc lc ->
  forall rs, 
  (forall id0 gvs, In (id0,gvs) rs -> Ensembles.Inhabited _ gvs) ->
  exists gv', 
    lookupAL _ (NDopsem.updateValuesForNewBlock rs lc) id1 = Some gv' /\
    Ensembles.Inhabited _ gv'. 
Proof.  
  induction rs; intros; simpl in *.   
    exists gv. eauto.

    destruct a. 
    destruct (id1==i0); subst.
      exists e. rewrite lookupAL_updateAddAL_eq; eauto.
      rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma updateValuesForNewBlock_spec3 : forall lc,
  wf_lc lc ->
  forall rs, 
  (forall id0 gvs, In (id0,gvs) rs -> Ensembles.Inhabited _ gvs) ->
  wf_lc (NDopsem.updateValuesForNewBlock rs lc).
Proof.  
  induction rs; intros; simpl in *; auto.

    destruct a.
    intros x gvx Hlk.
    destruct (i0==x); subst.
      rewrite lookupAL_updateAddAL_eq in Hlk. inv Hlk. eauto.

      rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
      apply IHrs in Hlk; auto.
        intros. eauto.
Qed.

Lemma wf_lc_br_aux : forall TD b1 b2 gl lc lc' 
  (Hswitch : NDopsem.switchToNewBasicBlock TD b1 b2 gl lc = ret lc')
  (Hwflc : wf_lc lc),
  wf_lc lc'.
Proof.
  intros.
  unfold NDopsem.switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  remember (NDopsem.getIncomingValuesForBlockFromPHINodes TD
              (getPHINodesFromBlock b1) b2 gl lc) as R1.
  destruct R1; inv Hswitch.
  apply updateValuesForNewBlock_spec3; auto.
    eapply getIncomingValuesForBlockFromPHINodes_spec2; eauto.
Qed.

Lemma wf_defs_br_aux : forall lc l' ps' cs' lc' F tmn' gl TD
  (l3 : l)
  (ps : phinodes)
  (cs : list cmd) tmn
  (Hlkup : Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hswitch : NDopsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
         (block_intro l3 ps cs tmn) gl lc = ret lc')
  (t : list atom)
  (Hwflc : wf_lc lc)
  (Hwfdfs : wf_defs F lc t)
  (ids0' : list atom)
  (Hinc : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) t),
  wf_defs F lc' ids0'.
Proof.
  intros.
  unfold NDopsem.switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  remember (NDopsem.getIncomingValuesForBlockFromPHINodes TD ps'
                (block_intro l3 ps cs tmn) gl lc) as R1.
  destruct R1; inv Hswitch.
  apply wf_defs_intro.
  intros id1 Hid1.
  destruct (In_dec eq_atom_dec id1 (getPhiNodesIDs ps')) as [Hin | Hnotin].
    eapply getIncomingValuesForBlockFromPHINodes_spec1 in HeqR1; eauto.
    destruct HeqR1 as [gv [HeqR1 Hinh]].
    apply updateValuesForNewBlock_spec1 with (lc:=lc) in HeqR1.
    eapply InPhiNodes_lookupTypViaIDFromFdef in Hlkup; eauto.
    destruct Hlkup as [t1 Hlkup].
    exists t1. exists gv.
    split; auto.

    apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) in Hnotin;
      auto.
    apply Hinc in Hnotin.
    apply wf_defs_elim with (id1:=id1) in Hwfdfs; auto.
    destruct Hwfdfs as [t1 [gv1 [J1 [J2 J3]]]].
    apply updateValuesForNewBlock_spec2 with (rs:=l0) in J2; auto.
      destruct J2 as [gv' [J2 J2']].
      exists t1. exists gv'. 
      split; auto.

      eapply getIncomingValuesForBlockFromPHINodes_spec2; eauto.
Qed.

Lemma inscope_of_tmn_br_aux : forall F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 ifs
  s m lc lc' TD gl,
wf_lc lc ->
wf_fdef ifs s m F ->
uniqFdef F ->
blockInFdefB (block_intro l3 ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs tmn) tmn ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
NDopsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs tmn) gl lc = Some lc' ->
wf_defs F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs F lc' ids0'.
Proof.
  intros F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 ifs s m lc lc' TD gl Hwflc HwfF 
    Huniq HBinF Hsucc Hinscope Hlkup Hswitch Hwfdfs.
  symmetry in Hlkup.
  assert (J:=Hlkup).
  apply lookupBlockViaLabelFromFdef_inv in J; auto.
  destruct J as [Heq J]; subst.
  unfold inscope_of_tmn in Hinscope.
  unfold inscope_of_tmn. unfold inscope_of_cmd.
  destruct F as [[? ? ? la va] bs].
  remember (dom_analyze (fdef_intro (fheader_intro f t i0 la va) bs)) as Doms.
  remember (Doms !! l3)as defs3.
  remember (Doms !! l')as defs'.
  destruct defs3 as [contents3 inbound3]. 
  destruct defs' as [contents' inbound']. 

  assert (incl contents' (l3::contents3)) as Hsub.
    clear - HBinF Hsucc Heqdefs3 Heqdefs' HeqDoms Huniq HwfF.
    simpl in Huniq. destruct Huniq.
    eapply dom_successors; eauto.

  destruct cs'.
  Case "cs'=nil".
    assert (J1:=inbound').
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getCmdsIDs nil ++ getArgsIDs la)(t:=t)(i0:=i0)(la:=la)(va:=va)(bs:=bs)
      (fa:=f)(l0:=l') in J1.
    destruct J1 as [r J1].
    exists r. split; auto.

    assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
      as Jinc.
      clear - Hinscope J1 Hsub HBinF Huniq.
      apply fold_left__spec in J1.
      symmetry in Hinscope.
      apply fold_left__spec in Hinscope.
      destruct J1 as [J1 [J2 J3]].
      destruct Hinscope as [J4 [J5 J6]].
      intros id1 J.
      assert (J':=J).
      apply ListSet.set_diff_elim1 in J.
      apply ListSet.set_diff_elim2 in J'.
      apply J3 in J.
      destruct J as [J | J].
      SCase "id1 in init and the current block".
        simpl in J.
        apply in_app_or in J.
        destruct J as [J | J]; try solve [contradict J; auto].
        apply J4.
        apply in_or_app. right.
        apply in_or_app; auto.
      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq. destruct Huniq.
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4.
            rewrite_env 
              ((getPhiNodesIDs ps ++ getCmdsIDs cs) ++ getArgsIDs la).
            apply in_or_app; auto.
      
            apply J5 in J9; auto.
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.

    split; auto.
      eauto using wf_defs_br_aux.
        
  Case "cs'<>nil".
    assert (J1:=inbound').
    unfold cmds_dominates_cmd. simpl.
    destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_ | n]; 
      try solve [contradict n; auto].
    simpl_env.
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getArgsIDs la)(t:=t)(i0:=i0)(la:=la)(va:=va)(bs:=bs)(l0:=l')(fa:=f) in J1.
    destruct J1 as [r J1].
    exists r.  split; auto.

    assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
      as Jinc.
      clear - Hinscope J1 Hsub HBinF Huniq.
      apply fold_left__spec in J1.
      symmetry in Hinscope.
      apply fold_left__spec in Hinscope.
      destruct J1 as [J1 [J2 J3]].
      destruct Hinscope as [J4 [J5 J6]].
      intros id1 J.
      assert (J':=J).
      apply ListSet.set_diff_elim1 in J.
      apply ListSet.set_diff_elim2 in J'.
      apply J3 in J.
      destruct J as [J | J].
      SCase "id1 in init and the current block".
        simpl in J.
        apply in_app_or in J.
        destruct J as [J | J]; try solve [contradict J; auto].
        apply J4.
        apply in_or_app. right.
        apply in_or_app; auto.
      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq. destruct Huniq.
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4.
            rewrite_env 
              ((getPhiNodesIDs ps ++ getCmdsIDs cs) ++ getArgsIDs la).
            apply in_or_app; auto.
      
            apply J5 in J9; auto. 
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.

    split; auto.
      eauto using wf_defs_br_aux.
Qed.

Lemma inscope_of_tmn_br_uncond : forall F l3 ps cs bid ids0 l' ps' cs' tmn' l0 
 ifs s m gl lc lc' TD,
wf_lc lc ->
wf_fdef ifs s m F ->
uniqFdef F ->
blockInFdefB (block_intro l3 ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0)) 
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
NDopsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs (insn_br_uncond bid l0)) gl lc = Some lc' ->
wf_defs F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs F lc' ids0'.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

Lemma inscope_of_tmn_br : forall F l0 ps cs bid l1 l2 ids0 l' ps' cs' tmn' Cond 
  c TD gl lc ifs s m lc',
wf_lc lc ->
wf_fdef ifs s m F ->
uniqFdef F ->
blockInFdefB (block_intro l0 ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) 
  (insn_br bid Cond l1 l2) ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
NDopsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
  (block_intro l0 ps cs (insn_br bid Cond l1 l2)) gl lc = Some lc' ->
wf_defs F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs F lc' ids0'.
Proof.
  intros.
  remember (isGVZero TD c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

Lemma params2GVs_inhabited : forall TD gl lc (Hwfc : wf_lc lc) lp gvs,
  NDopsem.params2GVs TD lp lc gl = Some gvs ->
  (forall gv, In gv gvs -> Ensembles.Inhabited _ gv).
Proof.
  induction lp; simpl; intros gvs Hp2gv gv Hin.
    inv Hp2gv. inv Hin.

    destruct a. 
    remember (NDopsem.getOperandValue TD v lc gl) as R0.
    destruct R0; try solve [inv Hp2gv].
    remember (NDopsem.params2GVs TD lp lc gl) as R.
    destruct R; inv Hp2gv.
    simpl in Hin.
    destruct Hin as [Hin | Hin]; subst; eauto.
      eapply getOperandValue__inhabited; eauto.
Qed.

Lemma params2GVs_inhabited' : forall TD gl lc (Hwfc : wf_lc lc) lp gvss,
  NDopsem.params2GVs TD lp lc gl = Some gvss ->
  exists gvs, gvs @@ gvss.
Proof.
  induction lp; simpl; intros gvss Hp2gv.
    inv Hp2gv. exists nil. simpl. auto.

    destruct a. 
    remember (NDopsem.getOperandValue TD v lc gl) as R0.
    destruct R0; try solve [inv Hp2gv].
    remember (NDopsem.params2GVs TD lp lc gl) as R.
    destruct R; inv Hp2gv.
    symmetry in HeqR0.
    apply getOperandValue__inhabited in HeqR0; auto.
    inv HeqR0.
    destruct (@IHlp l0) as [gvs' J]; auto.
    exists (x::gvs'). simpl. auto.
Qed.

Lemma initLocals_spec' : forall la gvs id1,
  In id1 (getArgsIDs la) ->
  exists gv, lookupAL _ (NDopsem.initLocals la gvs) id1 = Some gv.
Proof.
  unfold NDopsem.initLocals.
  induction la; intros; simpl in *.
    inversion H.

    destruct a. destruct p.
    simpl in H.
    destruct H as [H | H]; subst; simpl.
      destruct gvs. 
        exists ($ gundef t $). apply lookupAL_updateAddAL_eq; auto.      
        exists g. apply lookupAL_updateAddAL_eq; auto.      

      destruct (eq_atom_dec i0 id1); subst.
        destruct gvs.
          exists ($ gundef t $). apply lookupAL_updateAddAL_eq; auto.
          exists g. apply lookupAL_updateAddAL_eq; auto.
        destruct gvs; rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma wf_lc_updateAddAL : forall lc gv i0,
  wf_lc lc -> Ensembles.Inhabited _ gv -> wf_lc (updateAddAL _ lc i0 gv).
Proof.
  intros.
  intros x gvx Hlk.
  destruct (eq_atom_dec i0 x); subst.
    rewrite lookupAL_updateAddAL_eq in Hlk.
    inv Hlk. auto.

    rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto.
Qed.

Lemma initializeFrameValues__wf_lc : forall lc1 (Hwflc:wf_lc lc1) la2 gvs2,
  (forall gv, In gv gvs2 -> Ensembles.Inhabited _ gv) ->
  wf_lc (NDopsem._initializeFrameValues la2 gvs2 lc1).
Proof.
  induction la2; simpl; intros gvs2 Hin; auto.
    destruct a. destruct p.
    destruct gvs2; simpl in *; subst.
      apply wf_lc_updateAddAL; eauto.
        apply gv2gvs__inhabited.
      apply wf_lc_updateAddAL; eauto.
Qed.

Lemma initLocals__wf_lc : forall la gvs,
  (forall gv, In gv gvs -> Ensembles.Inhabited _ gv) ->  
  wf_lc (NDopsem.initLocals la gvs).
Proof.
  intros. unfold NDopsem.initLocals. 
  apply initializeFrameValues__wf_lc; auto.
    intros x gvx J. inv J.
Qed.

Lemma initLocals_spec : forall la gvs id1,
  (forall gv, In gv gvs -> Ensembles.Inhabited _ gv) ->  
  In id1 (getArgsIDs la) ->
  exists gv, lookupAL _ (NDopsem.initLocals la gvs) id1 = Some gv /\
    Ensembles.Inhabited _ gv.
Proof.
  intros.
  apply initLocals_spec' with (gvs:=gvs) in H0; auto.
  destruct H0 as [gv H0].
  exists gv. split; auto.
  apply initLocals__wf_lc with (la:=la) in H; eauto.
Qed.

Lemma returnUpdateLocals__wf_lc : forall TD c Result lc lc' gl lc'',
  wf_lc lc -> wf_lc lc' ->
  NDopsem.returnUpdateLocals TD c Result lc lc' gl = ret lc'' ->
  wf_lc lc''.
Proof.
  intros.
  unfold NDopsem.returnUpdateLocals in H1.
  remember (NDopsem.getOperandValue TD Result lc gl) as R.
  destruct R; tinv H1.
  destruct (getCallerReturnID c); inv H1; auto.
    apply wf_lc_updateAddAL; eauto using getOperandValue__inhabited.
Qed.

Lemma lift_op2__inhabited : forall f gvs1 gvs2 
  (H:forall x y, exists z, f x y = Some z),
  Ensembles.Inhabited _ gvs1 -> Ensembles.Inhabited _ gvs2 ->
  Ensembles.Inhabited _ (lift_op2 f gvs1 gvs2).
Proof.
  intros.
  unfold lift_op2. 
  inv H0. inv H1.
  destruct (@H x x0) as [z J].
  destruct (@gv2gvs__inhabited z).
  exists x1. unfold Ensembles.In. exists x. exists x0. exists z.
  rewrite J.
  repeat (split; auto).
Qed.

Lemma BOP__inhabited : forall TD lc gl bop0 sz0 v1 v2 gvs3,
  wf_lc lc ->
  NDopsem.BOP TD lc gl bop0 sz0 v1 v2 = ret gvs3 ->
  Ensembles.Inhabited GenericValue gvs3.
Proof.
  intros TD lc gl bop0 sz0 v1 v2 gvs3 Hwflc Hbop.
  unfold NDopsem.BOP in Hbop.
  remember(NDopsem.getOperandValue TD v1 lc gl) as R1.
  destruct R1; tinv Hbop.
  remember(NDopsem.getOperandValue TD v2 lc gl) as R2.
  destruct R2; inv Hbop.
  apply lift_op2__inhabited; eauto using getOperandValue__inhabited.
  apply mbop_is_total; auto.
Qed.

Lemma FBOP__inhabited : forall TD lc gl fbop0 fp v1 v2 gvs3,
  wf_lc lc ->
  NDopsem.FBOP TD lc gl fbop0 fp v1 v2 = ret gvs3 ->
  Ensembles.Inhabited GenericValue gvs3.
Proof.
  intros TD lc gl fbop0 fp v1 v2 gvs3 Hwflc Hfbop.
  unfold NDopsem.FBOP in Hfbop.
  remember(NDopsem.getOperandValue TD v1 lc gl) as R1.
  destruct R1; tinv Hfbop.
  remember(NDopsem.getOperandValue TD v2 lc gl) as R2.
  destruct R2; inv Hfbop.
  apply lift_op2__inhabited; eauto using getOperandValue__inhabited.
  apply mfbop_is_total; auto.
Qed.

Lemma ICMP__inhabited : forall TD lc gl c t v1 v2 gvs3,
  wf_lc lc ->
  NDopsem.ICMP TD lc gl c t v1 v2 = ret gvs3 ->
  Ensembles.Inhabited GenericValue gvs3.
Proof.
  intros TD lc gl c t v1 v2 gvs3 Hwflc Hiop.
  unfold NDopsem.ICMP in Hiop.
  remember(NDopsem.getOperandValue TD v1 lc gl) as R1.
  destruct R1; tinv Hiop.
  remember(NDopsem.getOperandValue TD v2 lc gl) as R2.
  destruct R2; inv Hiop.
  apply lift_op2__inhabited; eauto using getOperandValue__inhabited.
  apply micmp_is_total; auto.
Qed.

Lemma FCMP__inhabited : forall TD lc gl c t v1 v2 gvs3,
  wf_lc lc ->
  NDopsem.FCMP TD lc gl c t v1 v2 = ret gvs3 ->
  Ensembles.Inhabited GenericValue gvs3.
Proof.
  intros TD lc gl c t v1 v2 gvs3 Hwflc Hiop.
  unfold NDopsem.FCMP in Hiop.
  remember(NDopsem.getOperandValue TD v1 lc gl) as R1.
  destruct R1; tinv Hiop.
  remember(NDopsem.getOperandValue TD v2 lc gl) as R2.
  destruct R2; inv Hiop.
  apply lift_op2__inhabited; eauto using getOperandValue__inhabited.
  apply mfcmp_is_total; auto.
Qed.

Lemma values2GVs__inhabited' : forall TD lc (Hwflc: wf_lc lc) gl idxs vidxs,
  NDopsem.values2GVs TD idxs lc gl = Some vidxs ->
  (forall gvs, In gvs vidxs -> Ensembles.Inhabited GenericValue gvs).
Proof.
  induction idxs; simpl; intros vidxs Hv2gvs gvs Hin.
    inv Hv2gvs. inv Hin.

    remember (NDopsem.getOperandValue TD v lc gl) as R.
    destruct R; tinv Hv2gvs.
    remember (NDopsem.values2GVs TD idxs lc gl) as R1.
    destruct R1; inv Hv2gvs.
    simpl in Hin.
    destruct Hin as [Hin | Hin]; subst; eauto.
      eauto using getOperandValue__inhabited.
Qed.

Lemma values2GVs__inhabited : forall TD lc (Hwflc: wf_lc lc) gl idxs vidxs,
  NDopsem.values2GVs TD idxs lc gl = Some vidxs ->
  exists vidxs0, vidxs0 @@ vidxs.
Proof.
  induction idxs; simpl; intros vidxs Hv2gvs.
    inv Hv2gvs. exists nil. simpl. auto.

    remember (NDopsem.getOperandValue TD v lc gl) as R.
    destruct R; tinv Hv2gvs.
    remember (NDopsem.values2GVs TD idxs lc gl) as R1.
    destruct R1; inv Hv2gvs.
    symmetry in HeqR1. symmetry in HeqR.
    destruct (@IHidxs l0) as [vidxs0 J]; auto.
    apply getOperandValue__inhabited in HeqR; auto.
    inv HeqR.
    exists (x::vidxs0). simpl. simpl; auto.
Qed.

Lemma GEP__inhabited : forall TD t mp vidxs inbounds0 mp' vidxs0,
  Ensembles.Inhabited GenericValue mp ->
  vidxs0 @@ vidxs ->
  NDopsem.GEP TD t mp vidxs inbounds0 = ret mp' ->
  Ensembles.Inhabited GenericValue mp'.
Proof.
  intros.
  unfold NDopsem.GEP in H1. inv H.
  inv H1.
  destruct (@GEP_is_total TD t x vidxs0 inbounds0) as [mp' J].
  assert (J1:=@gv2gvs__inhabited mp'). inv J1.
  apply Ensembles.Inhabited_intro with (x:=x0).
  unfold Ensembles.In.
  exists x. exists vidxs0. exists mp'. rewrite J. split; auto.
Qed.

Lemma lift_op1__inhabited : forall f gvs1
  (H:forall x, exists z, f x = Some z),
  Ensembles.Inhabited _ gvs1 ->
  Ensembles.Inhabited _ (lift_op1 f gvs1).
Proof.
  intros.
  unfold lift_op1. 
  inv H0.
  destruct (@H x) as [z J].
  destruct (@gv2gvs__inhabited z).
  exists x0. unfold Ensembles.In. exists x. exists z.
  rewrite J.
  repeat (split; auto).
Qed.

Lemma CAST__inhabited : forall TD lc gl cop0 t1 v1 t2 gvs2,
  wf_lc lc ->
  NDopsem.CAST TD lc gl cop0 t1 v1 t2 = ret gvs2 ->
  Ensembles.Inhabited GenericValue gvs2.
Proof.
  intros TD lc gl cop0 t1 v1 t2 gvs2 Hwflc Hcast.
  unfold NDopsem.CAST in Hcast.
  remember(NDopsem.getOperandValue TD v1 lc gl) as R1.
  destruct R1; inv Hcast.
  apply lift_op1__inhabited; eauto using getOperandValue__inhabited.
  apply mcast_is_total; auto.
Qed.

Lemma TRUNC__inhabited : forall TD lc gl top0 t1 v1 t2 gvs2,
  wf_lc lc ->
  NDopsem.TRUNC TD lc gl top0 t1 v1 t2 = ret gvs2 ->
  Ensembles.Inhabited GenericValue gvs2.
Proof.
  intros TD lc gl top0 t1 v1 t2 gvs2 Hwflc Htrunc.
  unfold NDopsem.TRUNC in Htrunc.
  remember(NDopsem.getOperandValue TD v1 lc gl) as R1.
  destruct R1; inv Htrunc.
  apply lift_op1__inhabited; eauto using getOperandValue__inhabited.
  apply mtrunc_is_total; auto.
Qed.

Lemma EXT__inhabited : forall TD lc gl eop0 t1 v1 t2 gvs2,
  wf_lc lc ->
  NDopsem.EXT TD lc gl eop0 t1 v1 t2 = ret gvs2 ->
  Ensembles.Inhabited GenericValue gvs2.
Proof.
  intros TD lc gl eop0 t1 v1 t2 gvs2 Hwflc Hext.
  unfold NDopsem.EXT in Hext.
  remember(NDopsem.getOperandValue TD v1 lc gl) as R1.
  destruct R1; inv Hext.
  apply lift_op1__inhabited; eauto using getOperandValue__inhabited.
  apply mext_is_total; auto.
Qed.

Lemma extractGenericValue__inhabited : forall TD t gvs cidxs gvs',
  Ensembles.Inhabited GenericValue gvs ->
  NDopsem.extractGenericValue TD t gvs cidxs = ret gvs' ->
  Ensembles.Inhabited GenericValue gvs'.
Proof.  
  intros TD t gvs cidxs gvs' J1 J2.
  unfold extractGenericValue in J2.
  assert (J:=@gv2gvs__inhabited (uninits 1)).
  destruct (intConsts2Nats TD cidxs); try solve [inv J2; auto].
  destruct (mgetoffset TD t l0); try solve [inv J2; auto].
  destruct p. inv J2.
  apply lift_op1__inhabited; auto.
    apply mget'_is_total; auto.
Qed.

Lemma insertGenericValue__inhabited : forall TD t1 t2 gvs1 gvs2 cidxs gvs',
  Ensembles.Inhabited GenericValue gvs1 ->
  Ensembles.Inhabited GenericValue gvs2 ->
  NDopsem.insertGenericValue TD t1 gvs1 cidxs t2 gvs2 = ret gvs' ->
  Ensembles.Inhabited GenericValue gvs'.
Proof.  
  intros TD t1 t2 gvs1 gvs2 cidxs gvs' J1 J2 J3.
  unfold insertGenericValue in J3.
  assert (J:=@gv2gvs__inhabited (gundef t1)).
  destruct (intConsts2Nats TD cidxs); try solve [inv J3; auto].
  destruct (mgetoffset TD t1 l0); try solve [inv J3; auto].
  destruct p. inv J3.
  apply lift_op2__inhabited; auto.
    apply mset'_is_total; auto.
Qed.

(*********************************************)
(** * Preservation *)

Lemma preservation_dbCall_case : forall fid l' fa rt la va lb bs_contents gvs
  (Hinhs : forall gv, In gv gvs -> Ensembles.Inhabited _ gv)
  (bs_bound : incl bs_contents (bound_blocks lb))
  (H0 : incl bs_contents [l']),
   match
     fold_left
       (inscope_of_block (fdef_intro (fheader_intro fa rt fid la va) lb) l')
       bs_contents (ret getArgsIDs la)
   with
   | ret ids0 =>
       wf_defs (fdef_intro (fheader_intro fa rt fid la va) lb)
         (NDopsem.initLocals la gvs) ids0
   | merror => False
   end.
Proof.
  intros.
  assert (J:=bs_bound).
  apply fold_left__bound_blocks with (t:=rt)(i0:=fid)(la:=la)(va:=va)(fa:=fa)
    (l0:=l')(init:=getArgsIDs la) in J.
  destruct J as [r J].
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
    exists t. rewrite J1.
    apply initLocals_spec with (gvs:=gvs) in Hin; auto.
    destruct Hin as [gv [Hin Hinh]].
    exists gv. split; auto.
  
    destruct Hin as [b1 [l1 [Hin _]]].
    simpl in H0. clear - H0 Hin.
    assert (J:=Hin).
    apply ListSet.set_diff_elim1 in Hin.
    apply ListSet.set_diff_elim2 in J.
    apply H0 in Hin.
    simpl in Hin. 
    destruct Hin as [Hin | Hin]; subst; try inversion Hin.
    simpl in J. contradict J; auto.
Qed.

Definition wf_ExecutionContext (ps:list product) 
  (ec:NDopsem.ExecutionContext) : Prop :=
let '(NDopsem.mkEC f b cs tmn lc als) := ec in
isReachableFromEntry f b /\
blockInFdefB b f = true /\
InProductsB (product_fdef f) ps = true /\
wf_lc lc /\
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
exists l1, exists ps, exists cs',
b = block_intro l1 ps (cs'++cs) tmn.

Definition wf_call (ec:NDopsem.ExecutionContext) (ecs:NDopsem.ECStack) 
  : Prop :=
let '(NDopsem.mkEC f _ _ _ _ _) := ec in
forall b, blockInFdefB b f ->
let '(block_intro _ _ _ tmn) := b in
match tmn with
| insn_return _ _ _ | insn_return_void _ =>
    match ecs with
    | nil => True
    | NDopsem.mkEC f' b' (insn_call _ _ _ _ _ _ ::_) tmn' lc' als'::ecs' 
        => True
    | _ => False
    end
| _ => True
end.

Fixpoint wf_ECStack (ps:list product) (ecs:NDopsem.ECStack) : Prop :=
match ecs with
| nil => False
| ec::ecs' => wf_ExecutionContext ps ec /\ wf_ECStack ps ecs' /\ wf_call ec ecs'
end.

Definition wf_global system5 gl := forall id5 typ5, 
  lookupTypViaGIDFromSystem system5 id5 = ret typ5 ->
  exists gv : GenericValue, lookupAL GenericValue gl id5 = Some gv.

Definition wf_State (S:NDopsem.State) : Prop :=
let '(NDopsem.mkState s (los, nts) ps ecs gl _ _) := S in
wf_global s gl /\
wf_system nil s /\
moduleInSystemB (module_intro los nts ps) s = true /\
wf_ECStack ps ecs.

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
  (Hinhabited : Ensembles.Inhabited GenericValue gv3)
  (EC : list NDopsem.ExecutionContext)
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 : mem)
  (als : list mblock)
  id0 c0
  (Hid : Some id0 = getCmdID c0)
  t0
  (Htyp : Some t0 = getCmdTyp c0)
  (HwfS1 : wf_State
            {|
            NDopsem.CurSystem := S;
            NDopsem.CurTargetData := (los, nts);
            NDopsem.CurProducts := Ps;
            NDopsem.ECS := {|
                   NDopsem.CurFunction := F;
                   NDopsem.CurBB := B;
                   NDopsem.CurCmds := c0 :: cs;
                   NDopsem.Terminator := tmn;
                   NDopsem.Locals := lc;
                   NDopsem.Allocas := als |} :: EC;
            NDopsem.Globals := gl;
            NDopsem.FunTable := fs;
            NDopsem.Mem := Mem0 |}),
   wf_State
     {|
     NDopsem.CurSystem := S;
     NDopsem.CurTargetData := (los, nts);
     NDopsem.CurProducts := Ps;
     NDopsem.ECS := {|
            NDopsem.CurFunction := F;
            NDopsem.CurBB := B;
            NDopsem.CurCmds := cs;
            NDopsem.Terminator := tmn;
            NDopsem.Locals := updateAddAL GVs lc id0 gv3;
            NDopsem.Allocas := als |} :: EC;
     NDopsem.Globals := gl;
     NDopsem.FunTable := fs;
     NDopsem.Mem := Mem0 |}.
Proof.
  intros.
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]]
    ]; subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0) 
    as R1. 
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      apply wf_lc_updateAddAL; auto.
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
  (lc : GVsMap)
  (gl : GVMap)
  (fs : GVMap)
  (EC : list NDopsem.ExecutionContext)
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 : mem)
  (als : list mblock)
  c0
  (Hid : getCmdID c0 = None)
  (HwfS1 : wf_State
            {|
            NDopsem.CurSystem := S;
            NDopsem.CurTargetData := (los, nts);
            NDopsem.CurProducts := Ps;
            NDopsem.ECS := {|
                   NDopsem.CurFunction := F;
                   NDopsem.CurBB := B;
                   NDopsem.CurCmds := c0 :: cs;
                   NDopsem.Terminator := tmn;
                   NDopsem.Locals := lc;
                   NDopsem.Allocas := als |} :: EC;
            NDopsem.Globals := gl;
            NDopsem.FunTable := fs;
            NDopsem.Mem := Mem0 |}),
   wf_State
     {|
     NDopsem.CurSystem := S;
     NDopsem.CurTargetData := (los, nts);
     NDopsem.CurProducts := Ps;
     NDopsem.ECS := {|
            NDopsem.CurFunction := F;
            NDopsem.CurBB := B;
            NDopsem.CurCmds := cs;
            NDopsem.Terminator := tmn;
            NDopsem.Locals := lc;
            NDopsem.Allocas := als |} :: EC;
     NDopsem.Globals := gl;
     NDopsem.FunTable := fs;
     NDopsem.Mem := Mem0 |}.
Proof.
  intros.
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
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

Lemma wf_State__wf_lc : forall S TD Ps F B c cs tmn lc als EC gl fs Mem0,
  wf_State (NDopsem.mkState S TD Ps
              ((NDopsem.mkEC F B (c::cs) tmn lc als)::EC) gl fs Mem0) ->
  wf_lc lc.
Proof.
  intros. destruct TD.
  destruct H as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
     [HwfEC HwfCall]]]]
    ]; auto.
Qed.  

Tactic Notation "nsInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "nsReturn" | c "nsReturnVoid" | c "nsBranch" | c "nsBranch_uncond" |
    c "nsBop" | c "nsFBop" | c "nsExtractValue" | c "nsInsertValue" |
    c "nsMalloc" | c "nsFree" |
    c "nsAlloca" | c "nsLoad" | c "nsStore" | c "nsGEP" |
    c "nsTrunc" | c "nsExt" | 
    c "nsCast" | 
    c "nsIcmp" | c "nsFcmp" | c "nsSelect" |  
    c "nsCall" | c "nsExCall" ].

Lemma preservation : forall S1 S2 tr,
  nsInsn S1 S2 tr -> wf_State S1 -> wf_State S2.
Proof.
  intros S1 S2 tr HdsInsn HwfS1.
  (nsInsn_cases (induction HdsInsn) Case); destruct TD as [los nts].
Focus.
Case "nsReturn".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]]
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
    split. eapply returnUpdateLocals__wf_lc in H1; eauto.
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
        unfold NDopsem.returnUpdateLocals in H1. simpl in H1.
        remember (NDopsem.getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR. inv H1.
          assert (Hwfc := HBinF2).
          assert (In (insn_call i0 false c t v p) 
            (cs2'++[insn_call i0 false c t v p])) as HinCs.
            apply in_or_app. right. simpl. auto.
          eapply wf_system__wf_cmd with (c:=insn_call i0 false c t v p) 
            in Hwfc; eauto.
          inv Hwfc.
          eapply wf_defs_updateAddAL with (t1:=typ1);
            eauto using getOperandValue__inhabited.
            eapply uniqF__lookupTypViaIDFromFdef; eauto.
              eapply wf_system__uniqFdef; eauto.

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
        unfold NDopsem.returnUpdateLocals in H1. simpl in H1.
        remember (NDopsem.getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR. inv H1.
          assert (In (insn_call i0 false c0 t v p) 
            (cs2'++[insn_call i0 false c0 t v p] ++ [c] ++ cs')) as HinCs.
            apply in_or_app. right. simpl. auto.
          assert (Hwfc := HBinF2).
          eapply wf_system__wf_cmd with (c:=insn_call i0 false c0 t v p) 
            in Hwfc; eauto.
          inv Hwfc.
          eapply wf_defs_updateAddAL with (t1:=typ1); 
            eauto using getOperandValue__inhabited.
            eapply uniqF__lookupTypViaIDFromFdef; eauto.
              eapply wf_system__uniqFdef; eauto.

          destruct n; inv HeqR. inv H1.
          eapply wf_defs_eq; eauto. 
    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[c']).   
      simpl_env. auto.
Unfocus.

Focus.
Case "nsReturnVoid".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]]
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

    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[c']).   
      simpl_env. auto.
Unfocus.

Focus.
Case "nsBranch".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
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
  SCase "1".
    split.
      clear - Hreach1 H1 HBinF1 HFinPs1 HmInS HwfSystem.
      eapply wf_system__uniqFdef in HwfSystem; eauto.
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
    split. 
      clear - H1 HBinF1 HFinPs1 HmInS HwfSystem.
      eapply wf_system__uniqFdef with (f:=F) in HwfSystem; eauto.
      destruct (isGVZero (los, nts) c).
        symmetry in H1.
        apply lookupBlockViaLabelFromFdef_inv in H1; auto.
          destruct H1; auto.
        symmetry in H1.
        apply lookupBlockViaLabelFromFdef_inv in H1; auto.
          destruct H1; auto.
    split; auto.
    split. apply wf_lc_br_aux in H2; auto.
    split.
      assert (HwfF := HwfSystem).
      eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
      eapply wf_system__uniqFdef with (f:=F) in HwfSystem; eauto.
      clear - H0 HeqR1 H1 Hinscope1 H2 HwfSystem HBinF1 HwfF Hwflc1.
      eapply inscope_of_tmn_br in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Focus.
Case "nsBranch_uncond".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
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
    split; auto.
    split.
      clear - Hreach1 H HBinF1 HFinPs1 HmInS HwfSystem.
      eapply wf_system__uniqFdef with (f:=F) in HwfSystem; eauto.
      unfold isReachableFromEntry in *.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
      destruct H as [H _].
      eapply reachable_successors; eauto.
        simpl. auto.
    split.
      clear - H HBinF1 HFinPs1 HmInS HwfSystem.
      eapply wf_system__uniqFdef with (f:=F) in HwfSystem; eauto.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
        destruct H; auto.
    split; auto.
    split. apply wf_lc_br_aux in H0; auto.
    split.
      assert (HwfF := HwfSystem).
      eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
      eapply wf_system__uniqFdef with (f:=F) in HwfSystem; eauto.
      clear - H0 HeqR1 Hinscope1 H HwfSystem HBinF1 HwfF Hwflc1.
      assert (Hwds := HeqR1).
      eapply inscope_of_tmn_br_uncond with (cs':=cs')(l':=l')(ps':=ps')
        (tmn':=tmn') in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Case "nsBop". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  eapply BOP__inhabited; eauto using wf_State__wf_lc.
Case "nsFBop". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  eapply FBOP__inhabited; eauto using wf_State__wf_lc.
Case "nsExtractValue".
  assert (J':=HwfS1).
  destruct J' as 
      [Hwfg [HwfSystem [HmInS [
        [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
        [HwfEC HwfCall]]]]
      ]; subst.
  assert (exists t0, getSubTypFromConstIdxs idxs t = Some t0) as J.
    eapply wf_system__wf_cmd with (c:=insn_extractvalue id0 t v idxs) in HBinF1; 
      eauto.
      inv HBinF1; eauto.
      apply in_or_app; simpl; auto.
  destruct J as [t0 J].
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    apply getOperandValue__inhabited in H; auto.
    eapply extractGenericValue__inhabited in H0; eauto. 

Case "nsInsertValue". 
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    apply getOperandValue__inhabited in H; eauto using wf_State__wf_lc. 
    apply getOperandValue__inhabited in H0; eauto using wf_State__wf_lc. 
    eapply insertGenericValue__inhabited in H1; eauto using wf_State__wf_lc. 

Case "nsMalloc". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply singleton_inhabited.
Case "nsFree". eapply preservation_cmd_non_updated_case in HwfS1; eauto.
Case "nsAlloca". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply singleton_inhabited.
Case "nsLoad".  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply gv2gvs__inhabited.
Case "nsStore". eapply preservation_cmd_non_updated_case in HwfS1; eauto.
Case "nsGEP". 
  assert (J:=HwfS1).
  destruct J as 
    [Hwfg [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
         [HwfEC HwfCall]]]]
    ]; subst.
  assert (exists t0, getGEPTyp idxs t = Some t0) as J.
    eapply wf_system__wf_cmd with (c:=insn_gep id0 inbounds0 t v idxs) in HBinF1;
      eauto.
      inv HBinF1; eauto.
      apply in_or_app; simpl; auto.
  destruct J as [t0 J].
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    apply getOperandValue__inhabited in H; auto.
    apply values2GVs__inhabited in H0; auto.
    destruct H0 as [vidxs0 H0].
    eapply GEP__inhabited in H1; eauto. 

Case "nsTrunc". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  eapply TRUNC__inhabited; eauto using wf_State__wf_lc.
Case "nsExt". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  eapply EXT__inhabited; eauto using wf_State__wf_lc.
Case "nsCast". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  eapply CAST__inhabited; eauto using wf_State__wf_lc.
Case "nsIcmp". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  eapply ICMP__inhabited; eauto using wf_State__wf_lc.
Case "nsFcmp". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  eapply FCMP__inhabited; eauto using wf_State__wf_lc.
Case "nsSelect".
  destruct (isGVZero (los, nts) c); 
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    apply getOperandValue__inhabited in H1; eauto using wf_State__wf_lc.
    apply getOperandValue__inhabited in H0; eauto using wf_State__wf_lc.
Focus.
Case "nsCall".
  destruct HwfS1 as [Hwfg [HwfSys [HmInS [
    [Hreach [HBinF [HFinPs [Hwflc [Hinscope [l1 [ps [cs'' Heq]]]]]]]]
    [HwfECs HwfCall]]]]]; subst.
  assert (InProductsB (product_fdef (fdef_intro 
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    apply lookupFdefViaPtr_inversion in H1.
    destruct H1 as [fn [H11 H12]].
    eapply lookupFdefViaIDFromProducts_inv; eauto.
  split; auto.
  split; auto.
  split; auto.
  split.
  SCase "1".     
    assert (forall gv : GVs, In gv gvs -> Ensembles.Inhabited GenericValue gv)
      as JJ.
      eapply params2GVs_inhabited; eauto.
    split.
      simpl. eapply reachable_entrypoint; eauto.
    split.
     apply entryBlockInFdef in H2; auto.
    split; auto.
    split.
     apply initLocals__wf_lc; eauto.
    split.
     assert (ps'=nil) as EQ.
       eapply entryBlock_has_no_phinodes with (ifs:=nil)(s:=S); eauto.        
     subst.
     apply dom_entrypoint in H2.
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
    eapply preservation_cmd_non_updated_case in HwfS1; eauto.

    destruct oresult; inv H5.
    assert (exists t0, getCmdTyp (insn_call rid false ca ft fv lp) = Some t0)
      as J.
      destruct HwfS1 as 
       [Hwfg [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
         [HwfEC HwfCall]]]]
       ]; subst.
      eapply wf_system__wf_cmd with (c:=insn_call rid false ca ft fv lp) 
        in HBinF1; eauto.
      simpl.
      inv HBinF1; eauto. 
      apply in_or_app; simpl; auto.
    destruct J as [t0 J].
    eapply preservation_cmd_updated_case with (t0:=t0) in HwfS1; simpl; eauto.
      apply gv2gvs__inhabited.
Qed.

(*********************************************)
(** * Progress *)

Lemma state_tmn_typing : forall ifs s m f l1 ps1 cs1 tmn1 defs id1 lc,
  isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1) ->
  wf_insn ifs s m f (block_intro l1 ps1 cs1 tmn1) (insn_terminator tmn1) ->
  Some defs = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1 ->
  wf_defs f lc defs ->
  uniqFdef f ->
  In id1 (getInsnOperands (insn_terminator tmn1)) ->
  exists t, exists gv, 
    lookupTypViaIDFromFdef f id1 = munit t /\
    lookupAL _ lc id1 = Some gv /\ wf_GVs gv t.
Proof.
  intros ifs s m f l1 ps1 cs1 tmn1 defs id1 lc Hreach HwfInstr Hinscope HwfDefs 
    HuniqF HinOps.
  apply wf_insn__wf_insn_base in HwfInstr; 
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.  
 
  assert (
     In (f, block_intro l1 ps1 cs1 tmn1, insn_terminator tmn1, id1)
     (unmake_list_fdef_block_insn_id
        (make_list_fdef_block_insn_id
           (map_list_id
              (fun id_ : id =>
               (f, block_intro l1 ps1 cs1 tmn1, insn_terminator tmn1, id_))
              id_list)))
    ) as G.
    rewrite H5 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=block_intro l1 ps1 cs1 tmn1)
    (insn1:=insn_terminator tmn1)(id1:=id1) in H6; auto.

  inv H6.
  clear - H11 HwfDefs Hinscope H0 Hreach H9 HuniqF.
  eapply wf_defs_elim; eauto.
    unfold inscope_of_tmn in Hinscope.
    destruct f. destruct f.
    remember ((dom_analyze (fdef_intro (fheader_intro f t i0 a v) b)) !! l1) 
      as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H11 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      destruct J' as [J' _].
      destruct J' as [[cs2 [c1 [cs3 [J1 J2]]]] | [ps2 [p1 [ps3 [J1 J2]]]]]; 
        subst.
        rewrite getCmdsIDs_app. simpl. rewrite J2.
        apply in_or_app. right.
        apply in_or_app. left.
        apply in_or_app. right. simpl. auto.
    
        rewrite getPhiNodesIDs_app. simpl.
        apply in_or_app. left. 
        apply in_or_app. right. simpl. auto.
          
     unfold blockStrictDominates in J'.
     rewrite <- HeqR in J'.
     destruct block'.
     assert (In l0 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as J.       
       destruct J' as [J1 J2].
       apply ListSet.set_diff_intro; auto.
         simpl. intro J. destruct J as [J | J]; auto.
     destruct Hinscope as [_ [Hinscope _]].
     assert (
       lookupBlockViaLabelFromFdef (fdef_intro (fheader_intro f t i0 a v) b) l0 =
       ret block_intro l0 p c t0) as J1.
       apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
         eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
     apply Hinscope with (b1:=block_intro l0 p c t0) in J; auto.
       apply J.
       eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma state_cmd_typing : forall ifs s m f b c defs id1 lc,
  NoDup (getBlockLocs b) ->
  isReachableFromEntry f b ->
  wf_insn ifs s m f b (insn_cmd c) ->
  Some defs = inscope_of_cmd f b c ->
  wf_defs f lc defs ->
  uniqFdef f ->
  In id1 (getInsnOperands (insn_cmd c)) ->
  exists t, exists gv, 
    lookupTypViaIDFromFdef f id1 = munit t /\
    lookupAL _ lc id1 = Some gv /\ wf_GVs gv t.
Proof.
  intros ifs s m f b c defs id1 lc Hnodup Hreach HwfInstr Hinscope HwfDefs 
    HuniqF HinOps.
  apply wf_insn__wf_insn_base in HwfInstr;
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.  

  assert (
     In (f, b, insn_cmd c, id1)
     (unmake_list_fdef_block_insn_id
        (make_list_fdef_block_insn_id
           (map_list_id
              (fun id_ : id =>
               (f, b, insn_cmd c, id_))
              id_list)))
    ) as G.
    rewrite H5 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=b)(insn1:=insn_cmd c)(id1:=id1) 
    in H6; auto.

  inv H6. 
  eapply wf_defs_elim; eauto.
    unfold inscope_of_cmd in Hinscope.
    destruct b. destruct f. destruct f.
    remember ((dom_analyze (fdef_intro (fheader_intro f t0 i0 a v) b)) !! l0) 
      as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H11 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      simpl in J'.
      destruct J' as [[ps2 [p1 [ps3 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]];
        subst.

        rewrite getPhiNodesIDs_app. simpl.
        apply in_or_app. left. 
        apply in_or_app. right. simpl. auto.
          
        clear - J2 Hnodup.
        apply in_or_app. right.
        apply in_or_app. left. 
          simpl in Hnodup. apply NoDup_inv in Hnodup.
          destruct Hnodup as [_ Hnodup].
          apply NoDup_inv in Hnodup.
          destruct Hnodup as [Hnodup _].
          rewrite_env ((cs1 ++ c1 :: cs2) ++ c :: cs3).
          rewrite_env ((cs1 ++ c1 :: cs2) ++ c :: cs3) in Hnodup.
          apply NoDup__In_cmds_dominates_cmd; auto.
            rewrite getCmdsIDs_app.
            apply in_or_app. right. simpl. rewrite J2. simpl. auto.
    
     clear Hreach H0 HwfDefs.
     unfold blockStrictDominates in J'.
     rewrite <- HeqR in J'.
     destruct block'.
     assert (In l1 (ListSet.set_diff eq_atom_dec bs_contents [l0])) as J.       
       destruct J' as [J1 J2].
       apply ListSet.set_diff_intro; auto.
         simpl. intro J. destruct J as [J | J]; auto.
     destruct Hinscope as [_ [Hinscope _]].
     assert (
       lookupBlockViaLabelFromFdef (fdef_intro (fheader_intro f t0 i0 a v) b) l1
         = ret block_intro l1 p0 c1 t1) as J1.
       apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
         eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
     apply Hinscope with (b1:=block_intro l1 p0 c1 t1) in J; auto.
       apply J.
       eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma const2GV_isnt_stuck : forall TD S gl c t,
  wf_const S TD c t ->
  feasible_typ TD t ->
  wf_global S gl ->
  exists gv, NDopsem.const2GV TD gl c = Some gv.
Proof.
  intros.
  destruct const2GV_isnt_stuck_mutind as [J _].
  unfold const2GV_isnt_stuck_Prop in J.
  unfold NDopsem.const2GV.
  inv H0.
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
  (Hwfg : wf_global s gl)
  (HwfSys1 : wf_system nil s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (c : cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c)
  (Hinscope : wf_defs f lc l0)
  (v : value)
  (Hvincs : valueInCmdOperands v c),
  exists gv : GVs, 
    NDopsem.getOperandValue (los, nts) v lc gl = ret gv.
Proof.
  intros.
  destruct v as [vid | vc]; simpl.
    assert (exists t, exists gv, 
                lookupTypViaIDFromFdef f vid = munit t /\
                lookupAL _ lc vid = Some gv /\ 
                wf_GVs gv t) as Hlkup.
      eapply state_cmd_typing; eauto. 
      eapply wf_system__uniq_block; eauto.
      eapply wf_system__wf_cmd; eauto using In_middle.
      eapply wf_system__uniqFdef; eauto.
      apply valueInCmdOperands__InOps; auto.
    destruct Hlkup as [gt [gv [Hlktyp [Hlkup Hwfgv]]]].
    simpl.
    rewrite Hlkup. eauto.

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
  (Hwfg : wf_global s gl)
  (HwfSys1 : wf_system nil s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn) tmn)
  (Hinscope : wf_defs f lc l0)
  (v : value)
  (Hvincs : valueInTmnOperands v tmn),
  exists gv : GVs, NDopsem.getOperandValue (los, nts) v lc gl = ret gv.
Proof.
  intros.
  destruct v as [vid | vc].
    assert (HwfInstr:=HbInF).
    eapply wf_system__wf_tmn in HwfInstr; eauto.
    assert (exists t, exists gv, 
      lookupTypViaIDFromFdef f vid = munit t /\
      lookupAL _ lc vid = Some gv /\ 
      wf_GVs gv t) as Hlkup.
      eapply state_tmn_typing; eauto. 
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
  (l2 : list_value)
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVsMap)
  (gl : GVMap)
  (Hwfg1 : wf_global s gl)
  (HwfSys1 : wf_system nil s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f
             (block_intro l1 ps1 (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn) f =
          true)
  (l0 : list atom)
  (HeqR : ret l0 =
         inscope_of_cmd f
           (block_intro l1 ps1 (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn)
           (insn_gep i0 i1 t v l2))
  (Hinscope : wf_defs f lc l0)
  (Hex : exists l21, l2 = app_list_value l21 l22),
  exists vidxs, NDopsem.values2GVs (los, nts) l22 lc gl = Some vidxs.
Proof.
  induction l22; intros; simpl; eauto.
    destruct Hex as [l21 Hex]; subst.
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl. unfold valueInListValue. right. 
        apply in_app_list_value_right; simpl; auto.

    destruct J as [gv J].
    rewrite J.         
    eapply IHl22 in HbInF; eauto.  
      destruct HbInF as [vidxs HbInF].
      rewrite HbInF. eauto.

      exists (app_list_value l21 (Cons_list_value v Nil_list_value)).
        rewrite cons_eq_app_list_value.
        rewrite cons_eq_app_list_value.
        apply app_list_value_assoc.
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
  (Hin: exists ps1, ps' = ps1 ++ ps2),
   exists RVs : list (id * GVs),
     NDopsem.getIncomingValuesForBlockFromPHINodes (los, nts) ps2 
       (block_intro l1 ps1 cs1 tmn1) gl lc =
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
    destruct v as [vid | vc].
    Case "vid".
      assert (exists gv1, lookupAL _ lc vid = Some gv1) as J1.
        Focus.
        destruct H14 as [Hwfops Hwfvls].             
        assert (Hnth:=J).
        eapply getValueViaLabelFromValuels__nth_list_value_l in Hnth; eauto.
        destruct Hnth as [n Hnth].
        assert (HwfV:=J).
        eapply wf_value_list__getValueViaLabelFromValuels__wf_value in HwfV; eauto.
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
        exists ((i0, gv1) :: RVs). auto.
  
        destruct Hin as [ps3 Hin]. subst.
        exists (ps3++[insn_phi i0 t0 l2]).
        simpl_env. auto.
  
    Case "vc".
      eapply wf_value_list__getValueViaLabelFromValuels__wf_value in H2; eauto.
      inv H2.
      destruct (@const2GV_isnt_stuck (los,nts) s gl vc t0); auto.
      simpl. rewrite H.
      apply IHps2 in H7.
        destruct H7 as [RVs H7].
        rewrite H7. simpl.
        exists ((i0, x) :: RVs). auto.
  
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
  (Hex : exists p21, p2 = p21 ++ p22),
  exists gvs, NDopsem.params2GVs (los, nts) p22 lc gl = Some gvs.
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
      rewrite HbInF. eauto.

      exists (p21 ++ [(t0,v0)]). simpl_env. auto.
Qed.

Definition undefined_state (S : NDopsem.State): Prop :=
  match S with
  | {| NDopsem.CurTargetData := td;
       NDopsem.ECS := {|
                NDopsem.CurCmds := nil;
                NDopsem.Terminator := insn_return _ _ _;
                NDopsem.Allocas := als |} :: 
              {| NDopsem.CurCmds := c::_ |} :: _;
       NDopsem.Mem := M |} => free_allocas td M als = None
  | _ => False
  end \/
  match S with
  | {| NDopsem.CurTargetData := td;
       NDopsem.ECS := {|
                NDopsem.CurBB := _;
                NDopsem.CurCmds := nil;
                NDopsem.Terminator := insn_return_void _;
                NDopsem.Allocas := als |} :: 
              {| NDopsem.CurCmds := c::_ |} :: _;
       NDopsem.Mem := M |} => free_allocas td M als = None \/ 
                      match getCallerReturnID c with
                      | Some _ => True
                      | _ => False
                      end
  | _ => False
  end \/
  match S with
  | {| NDopsem.ECS := {|
                NDopsem.CurBB := block_intro _ _ _ (insn_unreachable _);
                NDopsem.CurCmds := nil;
                NDopsem.Terminator := (insn_unreachable _)
               |} :: _
     |} => True
  | _ => False
  end \/
  match S with
  | {| NDopsem.CurTargetData := td;
       NDopsem.ECS := 
         {| NDopsem.CurCmds := insn_malloc _ t v a::_ ; 
            NDopsem.Locals := lc|} :: _;
       NDopsem.Globals := gl;
       NDopsem.Mem := M |}
  | {| NDopsem.CurTargetData := td;
       NDopsem.ECS := 
         {| NDopsem.CurCmds := insn_alloca _ t v a::_ ; 
            NDopsem.Locals := lc|} :: _;
       NDopsem.Globals := gl;
       NDopsem.Mem := M |} =>
       match NDopsem.getOperandValue td v lc gl with
       | Some gvs =>
           match getTypeAllocSize td t with
           | Some asz => ~ exists gv, exists M', exists mb, 
               gv @ gvs /\ malloc td M asz gv a = Some (M', mb)
           | _ => False
           end
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| NDopsem.CurTargetData := td;
       NDopsem.ECS := {| NDopsem.CurCmds := insn_free _ _ v::_ ; 
                             NDopsem.Locals := lc|} :: _;
       NDopsem.Globals := gl;
       NDopsem.Mem := M |} =>
       match NDopsem.getOperandValue td v lc gl with
       | Some gvs => ~ exists gv, exists M', gv @ gvs /\ free td M gv = Some M'
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| NDopsem.CurTargetData := td;
       NDopsem.ECS := {| NDopsem.CurCmds := insn_load _ t v a::_ ; 
                             NDopsem.Locals := lc|} :: _;
       NDopsem.Globals := gl;
       NDopsem.Mem := M |} =>
       match NDopsem.getOperandValue td v lc gl with
       | Some gvs => 
           ~ exists gv, exists gv', gv @ gvs /\ mload td M gv t a = Some gv'
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| NDopsem.CurTargetData := td;
       NDopsem.ECS := {| NDopsem.CurCmds := insn_store _ t v v0 a::_ ; 
                             NDopsem.Locals := lc|} :: _;
       NDopsem.Globals := gl;
       NDopsem.Mem := M |} =>
       match NDopsem.getOperandValue td v lc gl, 
             NDopsem.getOperandValue td v0 lc gl with
       | Some gvs, Some mgvs => 
           ~ (exists gv, exists mgv, exists M', gv @ gvs /\ mgv @ mgvs /\ 
                mstore td M mgv t gv a = Some M')
       | _, _ => False
       end
  | _ => False
  end \/
  match S with
  | {| NDopsem.CurTargetData := td;
       NDopsem.CurProducts := ps;
       NDopsem.ECS := {| NDopsem.CurCmds := insn_call i0 n _ _ v p::_ ; 
                             NDopsem.Locals := lc|} :: _;
       NDopsem.Globals := gl;
       NDopsem.FunTable := fs;
       NDopsem.Mem := M |} => 
       match NDopsem.getOperandValue td v lc gl, params2GVs td p lc gl with
       | Some fptrs, Some gvss =>
           (~ exists fptr, exists f, fptr @ fptrs /\ 
                lookupFdefViaPtr ps fs fptr = Some f) /\
           (~ exists fptr, exists gvs, 
                fptr @ fptrs /\ 
                gvs @@ gvss /\ 
                match lookupExFdecViaPtr ps fs fptr with
                | Some (fdec_intro (fheader_intro _ _ fid _ _)) =>
                   match callExternalFunction M fid gvs with
                   | Some (oresult, _) =>
                      match exCallUpdateLocals n i0 oresult lc with
                      | None => False
                      | _ => True
                      end
                   | None => False
                   end
                | _ => False
                end
            )
       | _, _ => False
       end
  | _ => False
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
   
Require Import Classical_Prop.

Lemma progress : forall S1,
  wf_State S1 -> 
  ns_isFinialState S1 = true \/ 
  (exists S2, exists tr, nsInsn S1 S2 tr) \/
  undefined_state S1.
Proof.
  intros S1 HwfS1.
  destruct S1 as [s [los nts] ps ecs gl fs M].
  destruct HwfS1 as [Hwfg1 [HwfSys1 [HmInS1 HwfECs]]].
  destruct ecs; try solve [inversion HwfECs].
  destruct e as [f b cs tmn lc als].
  destruct HwfECs as [[Hreach 
                        [HbInF [HfInPs [Hwflc [Hinscope [l1 [ps1 [cs1 Heq]]]]]]]]
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
        destruct e as [f' b' cs' tmn' lc' als'].
        assert (J:=HbInF).
        apply HwfCall in J. clear HwfCall.
        destruct cs'; try solve [inversion J].
        destruct c; try solve [inversion J]. clear J.
        remember (free_allocas (los,nts) M als) as Rm.
        destruct Rm as [M' |]; try solve [undefbehave].
        left. symmetry in HeqRm.
        rename HeqRm into J.
        assert (exists lc'', 
          NDopsem.returnUpdateLocals (los,nts) (insn_call i1 n c t0 v0 p) v 
            lc lc' gl = Some lc'') as Hretup.
          unfold NDopsem.returnUpdateLocals. simpl.
          assert (exists gv : GVs, 
            NDopsem.getOperandValue (los, nts) v lc gl = ret gv) as H.
            eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
              simpl. auto.
          destruct H as [gv H]. rewrite H.
          destruct n.
            exists lc'. auto.
            exists (updateAddAL _ lc' i1 gv). auto.
          
        destruct Hretup as [lc'' Hretup].
        exists (NDopsem.mkState s (los, nts) ps 
                 ((NDopsem.mkEC f' b' cs' tmn' lc'' als')::ecs) gl fs M').
        exists trace_nil.
        eauto.  

    SCase "tmn=ret void".
      simpl in HwfCall.
      destruct ecs.
        simpl; auto.      

        right.
        destruct e as [f' b' cs' tmn' lc' als'].
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
        exists (NDopsem.mkState s (los, nts) ps 
                 ((NDopsem.mkEC f' b' cs' tmn' lc' als')::ecs) gl fs M').
        exists trace_nil.
        eauto.  

    SCase "tmn=br". 
      right. left.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists cond, NDopsem.getOperandValue (los,nts) v lc gl = 
        Some cond) as Hget.
        eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
          simpl. auto.
      destruct Hget as [cond Hget].
      assert (exists c, c @ cond) as Hinh.
        apply getOperandValue__inhabited in Hget; auto.
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
      assert (exists lc', NDopsem.switchToNewBasicBlock (los, nts) 
        (block_intro l' ps' cs' tmn') 
        (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l2 l3)) gl lc = 
          Some lc') as Hswitch.
         assert (exists RVs, 
           NDopsem.getIncomingValuesForBlockFromPHINodes (los, nts) ps'
             (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l2 l3)) gl lc =
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
         unfold NDopsem.switchToNewBasicBlock. simpl.
         rewrite J. 
         exists (NDopsem.updateValuesForNewBlock RVs lc). auto.

      destruct Hswitch as [lc' Hswitch].
      exists (NDopsem.mkState s (los, nts) ps 
              ((NDopsem.mkEC f (block_intro l' ps' cs' tmn') cs' tmn' lc' 
              als)::ecs) gl fs M).
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

      assert (exists lc', NDopsem.switchToNewBasicBlock (los, nts) 
        (block_intro l2 ps' cs' tmn') 
        (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc = 
          Some lc') as Hswitch.
         assert (exists RVs, 
           NDopsem.getIncomingValuesForBlockFromPHINodes (los, nts) ps'
             (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc =
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
         unfold NDopsem.switchToNewBasicBlock. simpl.
         rewrite J. 
         exists (NDopsem.updateValuesForNewBlock RVs lc). auto.

      destruct Hswitch as [lc' Hswitch].
      exists (NDopsem.mkState s (los, nts) ps 
              ((NDopsem.mkEC f (block_intro l2 ps' cs' tmn') cs' tmn' lc' 
              als)::ecs) gl fs M).
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
    destruct Hinsn_bop as [gv3 Hinsn_bop].
    exists 
         {|
         NDopsem.CurSystem := s;
         NDopsem.CurTargetData := (los, nts);
         NDopsem.CurProducts := ps;
         NDopsem.ECS := {|
                NDopsem.CurFunction := f;
                NDopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_bop i0 b s0 v v0 :: cs) tmn;
                NDopsem.CurCmds := cs;
                NDopsem.Terminator := tmn;
                NDopsem.Locals := (updateAddAL _ lc i0 gv3);
                NDopsem.Allocas := als |} :: ecs;
         NDopsem.Globals := gl;
         NDopsem.FunTable := fs;
         NDopsem.Mem := M |}.
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
      rewrite J. rewrite J0. eauto.

    destruct Hinsn_fbop as [gv3 Hinsn_fbop].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_fbop i0 f0 f1 v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv3);
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "c=extractvalue".
    left.
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', extractGenericValue (los, nts) t gv l2 = Some gv') as J'.
      unfold extractGenericValue.
      destruct (intConsts2Nats (los, nts) l2); eauto.
      destruct (mgetoffset (los, nts) t l3) as [[]|]; eauto.
    destruct J' as [gv' J'].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_extractvalue i0 t v l2 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv');
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
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
    assert (exists gv'', insertGenericValue (los, nts) t gv l2 t0 gv' = 
      Some gv'') as J''.
      unfold insertGenericValue.
      destruct (intConsts2Nats (los, nts) l2); eauto.
      destruct (mgetoffset (los, nts) t l3) as [[]|]; eauto.
    destruct J'' as [gv'' J''].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_insertvalue i0 t v t0 v0 l2 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv'');
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "c=malloc". 
    inv Hwfc. inv H12.
    apply feasible_typ_inv in H.
    destruct H as [ssz [asz [J1 J2]]].
    assert (exists gvs, NDopsem.getOperandValue (los, nts) v lc gl = Some gvs) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    destruct (classic 
      (exists gv, exists M', exists mb, 
         gv @ gvs /\ malloc (los, nts) M asz gv a = Some (M', mb))) as 
      [[gv [M' [mb [Hgvin Hex]]]] | Hnex].
      left.
      exists 
         {|
         NDopsem.CurSystem := s;
         NDopsem.CurTargetData := (los, nts);
         NDopsem.CurProducts := ps;
         NDopsem.ECS := {|
                NDopsem.CurFunction := f;
                NDopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_malloc i0 t v a :: cs) tmn;
                NDopsem.CurCmds := cs;
                NDopsem.Terminator := tmn;
                NDopsem.Locals := 
                  (updateAddAL _ lc i0 ($ (blk2GV (los, nts) mb) $));
                NDopsem.Allocas := als |} :: ecs;
         NDopsem.Globals := gl;
         NDopsem.FunTable := fs;
         NDopsem.Mem := M' |}.
      exists trace_nil.
      eauto.      
      
      unfold undefined_state.
      right. rewrite J. rewrite J2. undefbehave.

  SCase "free". 
    assert (exists gvs, NDopsem.getOperandValue (los, nts) v lc gl = Some gvs) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    destruct (classic 
      (exists gv, exists M', gv @ gvs /\ free (los, nts) M gv = Some M')) as 
      [[gv [M' [Hgvin Hex]]] | Hnex].
      left.
      exists 
         {|
         NDopsem.CurSystem := s;
         NDopsem.CurTargetData := (los, nts);
         NDopsem.CurProducts := ps;
         NDopsem.ECS := {|
                NDopsem.CurFunction := f;
                NDopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_free i0 t v :: cs) tmn;
                NDopsem.CurCmds := cs;
                NDopsem.Terminator := tmn;
                NDopsem.Locals := lc;
                NDopsem.Allocas := als |} :: ecs;
         NDopsem.Globals := gl;
         NDopsem.FunTable := fs;
         NDopsem.Mem := M' |}.
      exists trace_nil.
      eauto.      
      
      unfold undefined_state.
      right. rewrite J. undefbehave.

  SCase "alloca".
    inv Hwfc. inv H12.
    apply feasible_typ_inv in H.
    destruct H as [ssz [asz [J1 J2]]].
    assert (exists gvs, NDopsem.getOperandValue (los, nts) v lc gl = Some gvs) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    destruct (classic 
      (exists gv, exists M', exists mb, 
         gv @ gvs /\ malloc (los, nts) M asz gv a = Some (M', mb))) as 
      [[gv [M' [mb [Hgvin Hex]]]] | Hnex].
      left.
      exists 
         {|
         NDopsem.CurSystem := s;
         NDopsem.CurTargetData := (los, nts);
         NDopsem.CurProducts := ps;
         NDopsem.ECS := {|
                NDopsem.CurFunction := f;
                NDopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_alloca i0 t v a :: cs) tmn;
                NDopsem.CurCmds := cs;
                NDopsem.Terminator := tmn;
                NDopsem.Locals := 
                  (updateAddAL _ lc i0 ($ (blk2GV (los, nts) mb) $));
                NDopsem.Allocas := (mb::als) |} :: ecs;
         NDopsem.Globals := gl;
         NDopsem.FunTable := fs;
         NDopsem.Mem := M' |}.
      exists trace_nil.
      eauto.      
      
      right.
      unfold undefined_state.
      right. rewrite J. rewrite J2. undefbehave.

  SCase "load".
    assert (exists gvs, NDopsem.getOperandValue (los, nts) v lc gl = Some gvs) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    destruct (classic 
      (exists gv, exists gv', 
      gv @ gvs /\ mload (los, nts) M gv t a = Some gv')) as 
      [[gv [gv' [Hgvin Hex]]] | Hnex].
      left.
      exists 
         {|
         NDopsem.CurSystem := s;
         NDopsem.CurTargetData := (los, nts);
         NDopsem.CurProducts := ps;
         NDopsem.ECS := {|
                NDopsem.CurFunction := f;
                NDopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_load i0 t v a :: cs) tmn;
                NDopsem.CurCmds := cs;
                NDopsem.Terminator := tmn;
                NDopsem.Locals := updateAddAL _ lc i0 ($ gv' $);
                NDopsem.Allocas := als |} :: ecs;
         NDopsem.Globals := gl;
         NDopsem.FunTable := fs;
         NDopsem.Mem := M |}.
      exists trace_nil.
      eauto.      

      right.
      unfold undefined_state.
      right. rewrite J. undefbehave.
      
  SCase "store".
    assert (exists gvs, NDopsem.getOperandValue (los, nts) v lc gl = Some gvs) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gvs, NDopsem.getOperandValue (los, nts) v0 lc gl = Some gvs) 
      as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [mgvs J0].
    destruct (classic (exists gv, exists mgv, exists M', 
       gv @ gvs /\ mgv @ mgvs /\ mstore (los, nts) M mgv t gv a = Some M')) as
      [[gv [mgv [M' [Hgvin [Hmgvin Hex]]]]] | Hnex].
      left.
      exists 
         {|
         NDopsem.CurSystem := s;
         NDopsem.CurTargetData := (los, nts);
         NDopsem.CurProducts := ps;
         NDopsem.ECS := {|
                NDopsem.CurFunction := f;
                NDopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_store i0 t v v0 a :: cs) tmn;
                NDopsem.CurCmds := cs;
                NDopsem.Terminator := tmn;
                NDopsem.Locals := lc;
                NDopsem.Allocas := als |} :: ecs;
         NDopsem.Globals := gl;
         NDopsem.FunTable := fs;
         NDopsem.Mem := M' |}.
      exists trace_nil.
      eauto.      

      right.
      unfold undefined_state.
      right. rewrite J. rewrite J0. undefbehave.

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
    exists 
         {|
         NDopsem.CurSystem := s;
         NDopsem.CurTargetData := (los, nts);
         NDopsem.CurProducts := ps;
         NDopsem.ECS := {|
                NDopsem.CurFunction := f;
                NDopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn;
                NDopsem.CurCmds := cs;
                NDopsem.Terminator := tmn;
                NDopsem.Locals := (updateAddAL _ lc i0 mp');
                NDopsem.Allocas := als |} :: ecs;
         NDopsem.Globals := gl;
         NDopsem.FunTable := fs;
         NDopsem.Mem := M |}.
     exists trace_nil. eauto.

  SCase "trunc". 
    left.
    assert (exists gv2, NDopsem.TRUNC (los,nts) lc gl t t0 v t1 = Some gv2) 
      as Hinsn_trunc.
      unfold TRUNC.      
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
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "ext".
    left.
    assert (exists gv2, NDopsem.EXT (los,nts) lc gl e t v t0 = Some gv2) 
      as Hinsn_ext.
      unfold EXT.      
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
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "cast". 
    left.
    assert (exists gvs2, NDopsem.CAST (los,nts) lc gl c t v t0 = Some gvs2) 
      as Hinsn_cast.
      unfold NDopsem.CAST.      
      assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J. eauto.
      
    destruct Hinsn_cast as [gv2 Hinsn_cast].
    exists 
         {|
         NDopsem.CurSystem := s;
         NDopsem.CurTargetData := (los, nts);
         NDopsem.CurProducts := ps;
         NDopsem.ECS := {|
                NDopsem.CurFunction := f;
                NDopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_cast i0 c t v t0 :: cs) tmn;
                NDopsem.CurCmds := cs;
                NDopsem.Terminator := tmn;
                NDopsem.Locals := (updateAddAL _ lc i0 gv2);
                NDopsem.Allocas := als |} :: ecs;
         NDopsem.Globals := gl;
         NDopsem.FunTable := fs;
         NDopsem.Mem := M |}.
     exists trace_nil. eauto.

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
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "fcmp". 
    left.
    assert (exists gv2, NDopsem.FCMP (los,nts) lc gl f0 f1 v v0 = Some gv2) 
      as Hinsn_fcmp.
      unfold FCMP.      
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
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "select". 
    assert (exists gv, NDopsem.getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [cond J].
    assert (exists c, c @ cond) as Hinh.
      apply getOperandValue__inhabited in J; auto.
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
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "call". 
    assert (exists gvs, NDopsem.params2GVs (los, nts) p lc gl = Some gvs) as G.
      eapply params2GVs_isnt_stuck; eauto. 
        exists nil. auto.
    destruct G as [gvss G].
    assert (exists fptrs, NDopsem.getOperandValue (los, nts) v lc gl = 
      Some fptrs) as J'.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J' as [fptrs J'].
    destruct (classic (exists fptr, exists f', fptr @ fptrs /\ 
                      lookupFdefViaPtr ps fs fptr = Some f')) as 
      [[fptr [f' [Hgvin HeqHlk]]] | Hnex].
    SSCase "internal call".
    destruct f' as [[fa rt fid la va] lb].
    assert (J:=HeqHlk).
    apply lookupFdefViaPtr_inversion in J; auto.
    destruct J as [fn [Hlkft J]].
    apply lookupFdefViaIDFromProducts_inv in J; auto.
    eapply wf_system__wf_fdef in J; eauto.
    inv J. destruct block5 as [l5 ps5 cs5 tmn5].
    left.
    exists 
         {|
         NDopsem.CurSystem := s;
         NDopsem.CurTargetData := (los, nts);
         NDopsem.CurProducts := ps;
         NDopsem.ECS :=(NDopsem.mkEC 
                       (fdef_intro (fheader_intro fa rt fid la va) lb) 
                       (block_intro l5 ps5 cs5 tmn5) cs5 tmn5 
                       (NDopsem.initLocals la gvss) 
                       nil)::
               {|
                NDopsem.CurFunction := f;
                NDopsem.CurBB := block_intro l1 ps1
                           (cs1 ++ insn_call i0 n c t v p :: cs) tmn;
                NDopsem.CurCmds := insn_call i0 n c t v p :: cs;
                NDopsem.Terminator := tmn;
                NDopsem.Locals := lc;
                NDopsem.Allocas := als |} :: ecs;
         NDopsem.Globals := gl;
         NDopsem.FunTable := fs;
         NDopsem.Mem := M |}.
    exists trace_nil.
    eauto.     

    destruct (classic 
          (exists fptr, exists gvs, 
                fptr @ fptrs /\ 
                gvs @@ gvss /\ 
                match lookupExFdecViaPtr ps fs fptr with
                | Some (fdec_intro (fheader_intro _ _ fid _ _)) =>
                   match callExternalFunction M fid gvs with
                   | Some (oresult, _) =>
                      match exCallUpdateLocals n i0 oresult lc with
                      | None => False
                      | _ => True  
                      end
                   | None => False
                   end
                | _ => False
                end
            )) as 
      [[fptr [gvs [Hgvin [Hgvin' J]]]] | Hnex'].

    SSCase "external call".
    remember (lookupExFdecViaPtr ps fs fptr) as R. 
    destruct R as [f' |]; tinv J.
    destruct f' as [[fa rt fid la va]].
    remember (callExternalFunction M fid gvs) as R.
    destruct R as [[oresult Mem']|]; tinv J.
    remember (exCallUpdateLocals n i0 oresult lc) as R'.
    destruct R' as [lc' |]; tinv J.
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
              Allocas := als |} :: ecs;
       Globals := gl;
       FunTable := fs;
       Mem := Mem' |}.
      exists trace_nil.
      eauto.     

    SSCase "stuck".
      right.
      unfold undefined_state.
      right. rewrite J'. rewrite G. undefbehave.
Qed.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
