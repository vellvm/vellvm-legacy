Require Import vellvm.
Require Import Maps.
Require Import Lattice.
Require Import opsem_props.
Require Import trans_tactic.
Require Import primitives.
Require Import subst_inv.
Require Import phielim_spec.

Record PEInfo := mkPEInfo {
  PEI_f : fdef;
  PEI_b : block;
  PEI_p : phinode;
  PEI_v : value;
  PEI_in: phinodeInFdefBlockB PEI_p PEI_f PEI_b = true;
  PEI_subst: substing_value PEI_f PEI_v;
  PEI_assign: assigned_phi PEI_v PEI_p
}.

Lemma PEInfo__domination: forall (pi:PEInfo) s m (HwfF: wf_fdef s m (PEI_f pi))
  (Huniq: uniqFdef (PEI_f pi)),
  valueDominates (PEI_f pi) (PEI_v pi) (value_id (getPhiNodeID (PEI_p pi))).
Proof.
  destruct pi.
  simpl. intros.
  destruct_phinodeInFdefBlockB_tac.
  eapply assigned_phi__domination in PEI_assign0; eauto.
Qed.

Lemma PEInfo__lookupInsnViaIDFromFdef: forall (pi:PEInfo)
  (Huniq: uniqFdef (PEI_f pi)),
  lookupInsnViaIDFromFdef (PEI_f pi) (getPhiNodeID (PEI_p pi))
    = Some (insn_phinode (PEI_p pi)).
Proof.
  destruct pi. simpl. intros.
  destruct_phinodeInFdefBlockB_tac.
  solve_lookupInsnViaIDFromFdef.
Qed.

Lemma PEInfo_p__isnt__cmd: forall (pi:PEInfo) (Huniq: uniqFdef (PEI_f pi))
  l1 ps1 cs1 tmn1 c
  (HBinF: blockInFdefB (block_intro l1 ps1 cs1 tmn1) (PEI_f pi) = true)
  (Hin : In c cs1),
  getCmdLoc c <> getPhiNodeID (PEI_p pi).
Proof.
  intros.
  assert (Hlk:=Huniq).
  apply PEInfo__lookupInsnViaIDFromFdef in Hlk.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HBinF; eauto.
  intro EQ. rewrite EQ in *.
  congruence.
Qed.

(* similar to id_rhs_val.v *)
Lemma valueDominates_value_in_scope__value_in_scope__cmd: forall 
  pi S M (c : cmd) (ids1 : list atom) (Huniq : uniqFdef (PEI_f pi))
  (HwfF: wf_fdef S M (PEI_f pi)) 
  (l1 : l) (ps1 : phinodes) (cs1 : cmds) (tmn1 : terminator)
  (H : blockInFdefB (block_intro l1 ps1 cs1 tmn1) (PEI_f pi) = true)
  (H0 : In c cs1)
  (Hreach : isReachableFromEntry (PEI_f pi) (block_intro l1 ps1 cs1 tmn1))
  (Hinscope : 
    ret ids1 = inscope_of_cmd (PEI_f pi) (block_intro l1 ps1 cs1 tmn1) c)
  ids2
  (Heq : AtomSet.set_eq _ (getCmdLoc c::ids1) ids2)
  (Hina : value_in_scope (value_id (getPhiNodeID (PEI_p pi))) ids2),
  value_in_scope (PEI_v pi) ids2.
Proof.
Local Opaque inscope_of_cmd.
  intros.
  assert (Hdom:=HwfF). apply PEInfo__domination in Hdom; auto.
  assert (Hval2:=PEI_subst pi).
  destruct Heq as [Hinc1 Hinc2].
  remember (PEI_v pi) as v2. 
  destruct v2 as [vid2|]; auto.
  apply Hinc1.
  simpl. right.
  assert (getCmdLoc c <> getPhiNodeID (PEI_p pi)) as Hneq.
    eapply PEInfo_p__isnt__cmd; eauto.
  assert (In (getPhiNodeID (PEI_p pi)) ids1) as Hinscope'.
    apply Hinc2 in Hina. 
    destruct_in Hina; try congruence.
  assert (Hlkid:=Huniq). apply PEInfo__lookupInsnViaIDFromFdef in Hlkid.
  assert (Hidreach:=Hinscope').
  eapply inscope_of_cmd__id_in_reachable_block 
    with (vid:=getPhiNodeID (PEI_p pi)) in Hidreach; eauto 1.
  simpl.
  apply Hdom in Hidreach; auto.
  apply in_split in H0. destruct H0 as [cs3 [cs2 H0]]; subst.
  destruct Hval2 as [Hval2 | [instr Hval2]].
    eapply in_getArgsIDsOfFdef__inscope_of_cmd; eauto 1.
    eapply idDominates_inscope_of_cmd__inscope_of_cmd; eauto 2.
Transparent inscope_of_cmd.
Qed.

(* similar to id_rhs_val.v *)
Lemma wf_defs_updateAddAL: forall (pi:PEInfo) td gl F' lc' c ids1 ids2 g0
  s m (HwfF: wf_fdef s m F') (Huniq: uniqFdef F') l1 ps1 cs1 tmn1 
  (H : blockInFdefB (block_intro l1 ps1 cs1 tmn1) F' = true)
  (H0 : In c cs1) (Hreach: isReachableFromEntry F' (block_intro l1 ps1 cs1 tmn1))
  (Hinscope: ret ids1 = inscope_of_cmd F' (block_intro l1 ps1 cs1 tmn1) c)
  (Hinscope2' : wf_defs (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi) 
                  td gl F' lc' ids1)
  (Hinscope2'' : OpsemPP.wf_defs td F' lc' ids1)
  (Heq : AtomSet.set_eq _ (getCmdLoc c::ids1) ids2)
  (Hsome: getCmdID c <> None),
  wf_defs (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi) 
    td gl F' (updateAddAL _ lc' (getCmdLoc c) g0) ids2.
Proof.
Local Opaque inscope_of_cmd.
  intros.
  intros EQ gvsa gvsb Hina Hgeta Hgetb; subst.
  assert (Hinb: value_in_scope (PEI_v pi) ids2).
    eapply valueDominates_value_in_scope__value_in_scope__cmd; eauto.
  destruct Heq as [Hinc1 Hinc2].
  assert (Hdom:=HwfF). apply PEInfo__domination in Hdom; auto.
  assert (getCmdLoc c <> getPhiNodeID (PEI_p pi)) as Hneq.
    eapply PEInfo_p__isnt__cmd; eauto.
  assert (In (getPhiNodeID (PEI_p pi)) ids1) as Hin.
    apply Hinc2 in Hina. simpl in Hina.
    destruct Hina; subst; try congruence; auto.
  unfold wf_defs in Hinscope2'.
  simpl in *.
  remember (PEI_v pi) as v2.
  destruct v2 as [vid2 | vc2]; simpl in *.
    SCase "v2 = vid2".
      rewrite <- lookupAL_updateAddAL_neq in Hgeta; auto.
      destruct (vid2 == getCmdLoc c); subst.
      SSSCase "vid2 == c".
        (* vid1 in ids1 ==> vid1 >> c
           vid2 == c ==> vid1 >> vid2. Cycle!! *)
        elimtype False.
        apply inscope_of_cmd__idDominates with 
          (i0:=(getPhiNodeID (PEI_p pi))) in Hinscope; 
          auto using in__cmdInBlockB.
        assert (id_in_reachable_block (PEI_f pi) (getPhiNodeID (PEI_p pi))) 
          as Hinv.
          (* vid1 in scope, so it is reachable. *)
          eapply OpsemPP.wf_defs_elim in Hinscope2''; eauto. tauto.
        eapply idDominates_acyclic in Hinv; eauto.

      SSSCase "vid2 <> c".
        rewrite <- lookupAL_updateAddAL_neq in Hgetb; auto.

    SCase "v2 = vc2".
      rewrite <- lookupAL_updateAddAL_neq in Hgeta; auto.
Transparent inscope_of_cmd.
Qed.

Ltac destruct_ctx_return :=
match goal with
| Hwfcfg : OpsemPP.wf_Config ?cfg,
  Hwfpp : OpsemPP.wf_State ?cfg _,
  HwfS1 : wf_State _ _ _ _ _ |- _ =>
  destruct Hwfcfg as [_ [_ [HwfSystem HmInS]]];
  destruct Hwfpp as 
    [Hnempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]]
     [
      [
        [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]]
        [HwfECs HwfCall]
      ]
      HwfCall'
     ]]
    ]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs;
  destruct HwfS1 as [Hinscope1' [Hinscope2' HwfECs']];
  fold wf_ECStack in HwfECs';
  unfold wf_ExecutionContext in Hinscope1', Hinscope2';
  simpl in Hinscope1', Hinscope2'
end.

(* similar to id_rhs_val.v *)
Lemma valueDominates_value_in_scope__value_in_scope__at_beginning: forall 
  pi S M (ids1 : list atom) (Huniq : uniqFdef (PEI_f pi))
  (HwfF: wf_fdef S M (PEI_f pi)) 
  (l1 : l) (ps1 : phinodes) (cs1 : cmds) (tmn1 : terminator)
  (H : blockInFdefB (block_intro l1 ps1 cs1 tmn1) (PEI_f pi) = true)
  (Hreach : isReachableFromEntry (PEI_f pi) (block_intro l1 ps1 cs1 tmn1)) ids2
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_fdef (PEI_f pi)))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = (dom_analyze (PEI_f pi)) !! l1)
  (Hinscope : (fold_left (inscope_of_block (PEI_f pi) l1) contents'
    (ret (getPhiNodesIDs ps1 ++ getArgsIDsOfFdef (PEI_f pi))) = ret ids2))
  (Hina : value_in_scope (value_id (getPhiNodeID (PEI_p pi))) ids2),
  value_in_scope (PEI_v pi) ids2.
Proof.
  intros.
  assert (Hdom:=HwfF). apply PEInfo__domination in Hdom; auto.
  assert (Hval2:=PEI_subst pi).
  remember (PEI_v pi) as v2. 
  destruct v2 as [vid2|]; auto.
  simpl in Hval2. 
  assert (Hlkid:=Huniq). apply PEInfo__lookupInsnViaIDFromFdef in Hlkid.
  assert (Hidreach:=Hreach). 
  eapply inscope_of_blocks_with_init__id_in_reachable_block 
    with (vid:=getPhiNodeID (PEI_p pi)) in Hidreach; eauto 1.
    simpl.
    apply Hdom in Hidreach; auto.
    destruct Hval2 as [Hval2 | [instr Hval2]].
      eapply in_getArgsIDsOfFdef__inscope_of_blocks_with_init; eauto.
      intros x Hin. xsolve_in_list.

      eapply idDominates_inscope_of_cmd_at_beginning__inscope_of_cmd_at_beginning;
        eauto 2.

    intros id0 Hin0. simpl.
    destruct_in Hin0; xsolve_in_list.
Qed.

(* similar to id_rhs_val.v *)
Lemma wf_defs_br_aux : forall pi TD gl S M lc l' ps' cs' lc' F tmn' l1 ps1 cs1 
  tmn1 (HBinF: blockInFdefB (block_intro l1 ps1 cs1 tmn1) F = true)
  (Hreach : isReachableFromEntry F (block_intro l1 ps1 cs1 tmn1))
  (Hreach': isReachableFromEntry F (block_intro l' ps' cs' tmn'))
  (Hlkup : Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hswitch : Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') 
               (block_intro l1 ps1 cs1 tmn1) gl lc = ret lc')
  (t : list atom)
  (Hinscope': ret t = inscope_of_tmn F (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hwfdfs : wf_defs (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi) 
             TD gl F lc t)
  (Hwfdfs' : OpsemPP.wf_defs TD F lc t)
  (ids0' : list atom)
  (HwfF : wf_fdef S M F) (HuniqF: uniqFdef F)
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_fdef F))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = (dom_analyze F) !! l')
  (Hinscope : (fold_left (inscope_of_block F l') contents'
    (ret (getPhiNodesIDs ps' ++ getArgsIDsOfFdef F)) = ret ids0'))
  (Hinc : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) t),
  wf_defs (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi)  
    TD gl F lc' ids0'.
Proof.
Local Opaque inscope_of_tmn.
  intros. 
  assert (HBinF':=Hlkup).
  symmetry in HBinF'.
  apply lookupBlockViaLabelFromFdef_inv in HBinF'; auto.
  destruct HBinF' as [_ HBinF'].

  intros EQ gvs1 gvs2 Hin1 Hget1 Hget2; subst.
  assert (Hin2: value_in_scope (PEI_v pi) ids0').
    eapply valueDominates_value_in_scope__value_in_scope__at_beginning 
      in Hinscope; eauto 1.
      solve_blockInFdefB.
  assert (Hdom:=HwfF). apply PEInfo__domination in Hdom; auto.
(* destruct Hvals as [Hval1 [Hval2 [Hdom _]]]. *)
  unfold Opsem.switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  remember (Opsem.getIncomingValuesForBlockFromPHINodes TD ps' 
              (block_intro l1 ps1 cs1 tmn1) gl lc) as R1.
  destruct R1 as [rs|]; inv Hswitch.
  simpl in *.
  destruct (In_dec id_dec (getPhiNodeID (PEI_p pi)) (getPhiNodesIDs ps'))
    as [Hpin1 | Hnotin1].
  Case "p in ps".
    assert (getPhiNodeID (PEI_p pi) `in` dom rs) as Hinrs.
      eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec6; eauto.
    assert (match (PEI_v pi) with
            | value_id vid0 => vid0 `notin` dom rs
            | _ => True
            end) as Hnotinrs.
       destruct (PEI_v pi) as [vid0 | vc0]; auto.
         eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec8; eauto.
         intro J.
         eapply phinodes_from_the_same_block__dont__valueDominate in Hdom;
           eauto 1.
    apply OpsemProps.updateValuesForNewBlock_spec6 in Hget1; auto.
    eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec9' in HeqR1; 
      eauto 1.
    destruct HeqR1 as [t1 [vls1 [v [HinPs [Hnth Hget]]]]].
    assert (insn_phi (getPhiNodeID (PEI_p pi)) t1 vls1 = PEI_p pi) as EQ.
      assert (Hlkup':=HuniqF).
      apply PEInfo__lookupInsnViaIDFromFdef in Hlkup'.
      eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef' in HinPs; eauto 1.
      simpl in *. uniq_result. auto.
    assert (J:=PEI_assign pi).
    rewrite <- EQ in J.
    inv J.
    assert (In (v, getBlockLabel (block_intro l1 ps1 cs1 tmn1)) vls1) as Hinlist.
      apply getValueViaLabelFromValuels__InValueList; auto.
    apply Hassign in Hinlist.
    destruct Hinlist as [Hinlist | Hinlist]; subst.
    SCase "reading PEI_p".
      assert (In (getPhiNodeID (PEI_p pi)) t) as Hint.
        assert (wf_phinode (PEI_f pi) (block_intro l' ps' cs' tmn')
                 (insn_phi (getPhiNodeID (PEI_p pi)) t1 vls1)) as Hwfp.
          eapply wf_fdef__wf_phinode; eauto.
            solve_blockInFdefB.
        eapply incoming_value__in_scope in Hinscope'; eauto 1.
      assert (Opsem.getOperandValue TD (PEI_v pi) lc gl = ret gvs2) as Hget2'.
        destruct (PEI_v pi) as [vid0 | vc0]; auto.
          simpl in Hget2.
          eapply OpsemProps.updateValuesForNewBlock_spec7 in Hget2; eauto.
      eapply Hwfdfs in Hint; eauto.

    SCase "reading PEI_v".
      destruct (PEI_v pi) as [vid0 | vc0]; simpl in Hget2, Hget.
        eapply OpsemProps.updateValuesForNewBlock_spec7 in Hget2; eauto.
        congruence.

        congruence.

  Case "p notin ps".
    assert (Hnotin1' := Hnotin1).
    apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec)
      in Hnotin1; auto.
    apply Hinc in Hnotin1. assert (HeqR1':=HeqR1).
    eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec8 in HeqR1;
      eauto.
    eapply OpsemProps.updateValuesForNewBlock_spec7 in Hget1; eauto.

    remember (PEI_v pi) as v2.
    destruct v2 as [vid2 | vc2]; simpl in *; eauto.
    SCase "v2 = vid2".
      assert (~ In vid2 (getPhiNodesIDs ps')) as Hnotin2.
        (* vid1 in ids0' /\ vid1 notin ps' /\ vid2 in ps' ==>  
           v1d1 >> vid2 !! *)
        intro Hin.
        eapply inscope_of_cmd_at_beginning__idDominates__phinode
          with (i0:=getPhiNodeID (PEI_p pi)) in Hinscope; eauto.
        assert (id_in_reachable_block (PEI_f pi) (getPhiNodeID (PEI_p pi))) 
          as Hinv.
          (* vid1 in scope, so it is reachable. *)
          eapply OpsemPP.wf_defs_elim in Hwfdfs'; eauto. tauto.
        eapply idDominates_acyclic in Hinv; eauto. 

      assert (Hnotin2' := Hnotin2).
      apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec)
        in Hnotin2; auto.
      apply Hinc in Hnotin2. assert (HeqR1'':=HeqR1').
      eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec8 in HeqR1';
        eauto.
      eapply OpsemProps.updateValuesForNewBlock_spec7 in Hget2; eauto.
Transparent inscope_of_tmn.
Qed.

(* similar to id_rhs_val.v *)
Lemma inscope_of_tmn_br_aux : forall pi S M F l3 ps cs tmn ids0 l' ps' cs' tmn'
  l0 lc lc' gl TD (Hreach : isReachableFromEntry F (block_intro l3 ps cs tmn))
  (Hwfdfs': OpsemPP.wf_defs TD F lc ids0),
wf_fdef S M F -> 
uniqFdef F ->
blockInFdefB (block_intro l3 ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs tmn) tmn ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs tmn) gl lc = Some lc' ->
wf_defs (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi)  
  TD gl F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi)  
    TD gl F lc' ids0'.
Proof.
  intros pi S M F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 lc lc' gl TD Hreach Hwfdfs'
    HwfF HuniqF HBinF Hsucc Hinscope Hlkup Hswitch Hwfdfs.
  symmetry in Hlkup.
  assert (J:=Hlkup).
  apply lookupBlockViaLabelFromFdef_inv in J; auto.
  destruct J as [Heq J]; subst.
  assert (Hinscope':=Hinscope).
  unfold inscope_of_tmn in Hinscope.
  unfold inscope_of_tmn. unfold inscope_of_cmd, inscope_of_id.
  destruct F as [fh bs].
  remember (dom_analyze (fdef_intro fh bs)) as Doms.
  remember (Doms !! l3)as defs3.
  remember (Doms !! l')as defs'.
  destruct defs3 as [contents3 inbound3].
  destruct defs' as [contents' inbound'].

  assert (incl contents' (l3::contents3)) as Hsub.
    clear - HBinF Hsucc Heqdefs3 Heqdefs' HeqDoms HuniqF HwfF.
    apply uniqF__uniqBlocks in HuniqF.
    simpl in HuniqF.
    eapply dom_successors; eauto.

  assert (isReachableFromEntry (fdef_intro fh bs) (block_intro l' ps' nil tmn'))
    as Hreach'.
    eapply isReachableFromEntry_successors in Hlkup; eauto.

  assert (J1:=inbound'). destruct fh as [f t i0 a v].
  apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++
    getArgsIDs a)(bs:=bs)(l0:=l') (fh:=fheader_intro f t i0 a v) in J1; auto.
  destruct J1 as [r J1].
  exists r. 

  assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
    as Jinc.
    clear - Hinscope J1 Hsub HBinF HuniqF.
    eapply inscope_of_tmn__inscope_of_cmd_at_beginning in J1; eauto. 

  destruct cs'.
  Case "cs'=nil".
    simpl.
    split; auto.
    split; auto.
      subst. simpl in J1. simpl_env in J1.
      eapply wf_defs_br_aux in Hswitch; eauto.
  Case "cs'<>nil".
    assert (~ In (getCmdLoc c) (getPhiNodesIDs ps')) as Hnotin.
      apply uniqFdef__uniqBlockLocs in J; auto.
      simpl in J. 
      eapply NoDup_disjoint in J; simpl; eauto.
    rewrite init_scope_spec1; auto.
    unfold cmds_dominates_cmd. simpl.
    destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_ | n];
      try solve [contradict n; auto].
    split; auto.
    split; auto.
      subst. eapply wf_defs_br_aux in Hswitch; eauto.
Qed.

(* same to id_rhs_val.v *)
Lemma inscope_of_tmn_br_uncond : forall pi S M F l3 ps cs ids0 l' ps' 
  cs' tmn' l0 lc lc' bid TD gl
  (Hwfdfs': OpsemPP.wf_defs TD F lc ids0),
isReachableFromEntry F (block_intro l3 ps cs (insn_br_uncond bid l0)) ->
wf_fdef S M F -> uniqFdef F ->
blockInFdefB (block_intro l3 ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0))
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs (insn_br_uncond bid l0)) gl lc = Some lc' ->
wf_defs (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi)  
  TD gl F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi) 
    TD gl F lc' ids0'.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

(* same to id_rhs_val.v *)
Lemma inscope_of_tmn_br : forall pi S M F l0 ps cs bid l1 l2 ids0 l' 
  ps' cs' tmn' Cond c lc lc' gl TD
  (Hwfdfs': OpsemPP.wf_defs TD F lc ids0),
isReachableFromEntry F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) ->
wf_fdef S M F -> uniqFdef F ->
blockInFdefB (block_intro l0 ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2))
  (insn_br bid Cond l1 l2) ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
  (block_intro l0 ps cs (insn_br bid Cond l1 l2)) gl lc = Some lc' ->
wf_defs (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi) 
  TD gl F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi)
    TD gl F lc' ids0'.
Proof.
  intros.
  remember (isGVZero TD c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

Ltac destruct_ctx_other :=
match goal with
| Hwfcfg : OpsemPP.wf_Config ?cfg,
  Hwfpp : OpsemPP.wf_State ?cfg _,
  HwfS1 : wf_State _ _ _ _ _ |- _ =>
  destruct Hwfcfg as [_ [_ [HwfSystem HmInS]]];
  destruct Hwfpp as 
    [Hnempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1' [ps1' [cs1' Heq1]]]]]]]]
     [HwfECs HwfCall]]
    ]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs;
  destruct HwfS1 as [Hinscope1' HwfECs'];
  fold wf_ECStack in HwfECs';
  unfold wf_ExecutionContext in Hinscope1';
  simpl in Hinscope1'
end.

(* same to id_rhs_val.v *)
Lemma preservation_cmd_updated_case : forall pi
  (B : block)
  lc gv3
  (cs : list cmd)
  (tmn : terminator)
  id0 c0 los nts gl Mem0 Mem1 als EC fs Ps S
  (Hid : Some id0 = getCmdID c0) Cfg St
  (Hwfcfg : OpsemPP.wf_Config Cfg) (Hwfpp : OpsemPP.wf_State Cfg St)
  (EQ1 : Cfg = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := (los, nts);
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |}) F0
  (EQ2 : St = {| Opsem.ECS := {|
                           Opsem.CurFunction := F0;
                           Opsem.CurBB := B;
                           Opsem.CurCmds := c0 :: cs;
                           Opsem.Terminator := tmn;
                           Opsem.Locals := lc;
                           Opsem.Allocas := als |} :: EC;
                 Opsem.Mem := Mem0 |})
  (HwfS1 : wf_State (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) 
            (PEI_f pi) Cfg St) als',
  wf_State (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi) Cfg
     {|
     Opsem.ECS := {|
            Opsem.CurFunction := F0;
            Opsem.CurBB := B;
            Opsem.CurCmds := cs;
            Opsem.Terminator := tmn;
            Opsem.Locals := updateAddAL _ lc id0 gv3;
            Opsem.Allocas := als' |} :: EC;
     Opsem.Mem := Mem1 |}.
Proof.
Local Opaque inscope_of_cmd inscope_of_tmn.
  intros. subst.
  destruct_ctx_other.
  split; auto.
    unfold wf_ExecutionContext. simpl.
    remember (inscope_of_cmd F0 (block_intro l1' ps1' (cs1' ++ c0 :: cs) tmn) c0)
      as R1.
    assert (HeqR1':=HeqR1).
    assert (uniqFdef F0) as HuniqF.
      eapply wf_system__uniqFdef; eauto.
    destruct R1; try solve [inversion Hinscope1].
      assert (Hid':=Hid).
      symmetry in Hid.
      apply getCmdLoc_getCmdID in Hid.
      subst.
      assert (cmdInBlockB c0 (block_intro l1' ps1' (cs1' ++ c0 :: cs) tmn)
               = true) as Hin.
        simpl. apply In_InCmdsB. apply in_middle.
      assert (NoDup (getBlockLocs (block_intro l1' ps1' (cs1' ++ c0 :: cs) tmn))) 
        as Hnotin.
        eapply wf_system__uniq_block with (f:=F0) in HwfSystem; eauto.
      destruct cs; simpl_env in *.
      Case "1.1.1".
        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs1' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite <- Hid' in J2.
        assert (HwfF:=HFinPs1). eapply wf_system__wf_fdef in HwfF; eauto.
        eapply wf_defs_updateAddAL; try solve [eauto | congruence].

      Case "1.1.2".
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs1' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite <- Hid' in J2.
        assert (HwfF:=HFinPs1). eapply wf_system__wf_fdef in HwfF; eauto.
        eapply wf_defs_updateAddAL; try solve [eauto | congruence].
Transparent inscope_of_cmd inscope_of_tmn.
Qed.

(* same to id_rhs_val *)
Lemma preservation_cmd_non_updated_case : forall pi
  (S : system)
  (los : layouts)
  (nts : namedts)
  (Ps : list product)
  (B : block)
  lc (gl : GVMap)
  (fs : GVMap) EC
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 Mem1: mem)
  (als : list mblock)
  c0
  (Hid : getCmdID c0 = None) Cfg St
  (Hwfcfg : OpsemPP.wf_Config Cfg) (Hwfpp : OpsemPP.wf_State Cfg St)
  (EQ1 : Cfg = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := (los, nts);
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |}) F0
  (EQ2 : St = {| Opsem.ECS := {|
                           Opsem.CurFunction := F0;
                           Opsem.CurBB := B;
                           Opsem.CurCmds := c0 :: cs;
                           Opsem.Terminator := tmn;
                           Opsem.Locals := lc;
                           Opsem.Allocas := als |} :: EC;
                 Opsem.Mem := Mem0 |})
  (HwfS1 : wf_State (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) 
             (PEI_f pi) Cfg St),
  wf_State (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi) Cfg
     {|
     Opsem.ECS := {|
            Opsem.CurFunction := F0;
            Opsem.CurBB := B;
            Opsem.CurCmds := cs;
            Opsem.Terminator := tmn;
            Opsem.Locals := lc;
            Opsem.Allocas := als |} :: EC;
     Opsem.Mem := Mem1 |}.
Proof.
Local Opaque inscope_of_cmd inscope_of_tmn.
  intros. subst.
  destruct_ctx_other.
  split; auto.
    remember (inscope_of_cmd F0 (block_intro l1' ps1' (cs1' ++ c0 :: cs) tmn) c0)
      as R1.
    destruct R1; try solve [inversion Hinscope1].
    unfold wf_ExecutionContext. simpl.
    assert (NoDup (getBlockLocs (block_intro l1' ps1' (cs1' ++ c0 :: cs) tmn))) 
      as Hnotin.
      eapply wf_system__uniq_block with (f:=F0) in HwfSystem; eauto.
    destruct cs; simpl_env in *.
    Case "1.1.1".
        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs1' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq; eauto.

    Case "1.1.2".
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs1' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq ; eauto.
Transparent inscope_of_cmd inscope_of_tmn.
Qed.

Lemma PEInfo_p__isnt__arg: forall (pi:PEInfo) (Huniq: uniqFdef (PEI_f pi)),
  ~ In (getPhiNodeID (PEI_p pi)) (getArgsIDsOfFdef (PEI_f pi)).
Proof.
  intros.
  assert (Hlk:=Huniq).
  apply PEInfo__lookupInsnViaIDFromFdef in Hlk.
  solve_notin_getArgsIDs.
Qed.

(* similar to id_rhs_val *)
Lemma preservation_dbCall_case : forall fid fa rt la va lb td lc gl
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb)) pi,
  wf_defs (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi) td gl
    (fdef_intro (fheader_intro fa rt fid la va) lb) lc (getArgsIDs la).
Proof.
  intros.
  assert (incl nil (bound_blocks lb)) as J.
    intros x J. inv J.
  intros EQ gvs1 gvs2 Hin1 Hget1 Hget2; subst.
  simpl in Hin1.
  contradict Hin1.
  rewrite <- EQ in Huniq.
  apply PEInfo_p__isnt__arg in Huniq.
  rewrite EQ in Huniq. auto.
Qed.

(* same to id_rhs_val *)
Lemma preservation: forall (cfg1 : OpsemAux.Config)
  (S1 S1' : Opsem.State) (tr : trace) (pi: PEInfo)
  (Hcfg: OpsemPP.wf_Config cfg1) (Hpp: OpsemPP.wf_State cfg1 S1)
  (HsInsn: Opsem.sInsn cfg1 S1 S1' tr)
  (HwfS1 : subst_inv.wf_State (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) 
          (PEI_f pi) cfg1 S1),
  subst_inv.wf_State (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi) 
    cfg1 S1'.
Proof.

Local Opaque inscope_of_tmn inscope_of_cmd.

  intros.
  (sInsn_cases (induction HsInsn) Case); destruct TD as [los nts]; simpl HwfS1.

Case "sReturn".
Focus.

  destruct_ctx_return.

  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return rid RetTy Result))
             (insn_return rid RetTy Result)) as R1.
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
    unfold wf_ExecutionContext. simpl.
    remember (getCmdID c') as R.
    destruct_cmd c'; try solve [inversion H].
    assert (uniqFdef F') as HuniqF.
      eapply wf_system__uniqFdef; eauto.
    assert (wf_fdef S (module_intro los nts Ps) F') as HwfF.
      eapply wf_system__wf_fdef; eauto.

    assert (NoDup (getBlockLocs 
                     (block_intro l2 ps2
                        (cs2' ++ insn_call i0 n c t0 v0 v p :: cs') tmn'))) 
      as Hnotin.
      eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.
    destruct cs'; simpl_env in *.
    SSSCase "1.1.1".
        assert (HeqR2':=HeqR2).
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        unfold Opsem.returnUpdateLocals in H1. simpl in H1.
        remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR.
          remember (lift_op1 DGVs (fit_gv (los, nts) t0) g t0) as R2.
          destruct R2; inv H1.
          change i0 with
            (getCmdLoc (insn_call i0 false c t0 v0 v p)); auto.
          eapply wf_defs_updateAddAL; try solve [eauto | simpl; congruence].
            simpl. apply in_middle.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto.

    SSSCase "1.1.2".
        assert (HeqR2':=HeqR2).
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        unfold Opsem.returnUpdateLocals in H1. simpl in H1.
        remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR.
          remember (lift_op1 DGVs (fit_gv (los, nts) t0) g t0) as R2.
          destruct R2; inv H1.
          change i0 with
            (getCmdLoc (insn_call i0 false c t0 v0 v p)); auto.
          eapply wf_defs_updateAddAL; try solve [eauto | simpl; congruence].
            simpl. apply in_middle.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto.

Unfocus.

Case "sReturnVoid".
Focus.

  destruct_ctx_return.

  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return_void rid))
             (insn_return_void rid)) as R1.
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
    unfold wf_ExecutionContext. simpl.
    apply HwfCall' in HBinF1. simpl in HBinF1.
    assert (NoDup (getBlockLocs 
                     (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn'))) 
      as Hnotin.
      eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.
    destruct cs'; simpl_env in *.
    SSSCase "1.1.1".
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnotin H1 Hinscope2'.
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct_cmd c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto.

    SSSCase "1.1.2".
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnotin H1 Hinscope2'.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct_cmd c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto.

Unfocus.

Case "sBranch".
Focus.

  destruct_ctx_other.
  remember (inscope_of_tmn F
             (block_intro l1' ps1' (cs1' ++ nil)(insn_br bid Cond l1 l2))
             (insn_br bid Cond l1 l2)) as R1.
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
    unfold wf_ExecutionContext. simpl.
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
    eapply inscope_of_tmn_br in HeqR1; eauto.
    destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
    destruct cs'; rewrite <- HeqR1; auto.
Unfocus.

Case "sBranch_uncond".
Focus.

  destruct_ctx_other.
  remember (inscope_of_tmn F
             (block_intro l1' ps1' (cs1' ++ nil)(insn_br_uncond bid l0))
             (insn_br_uncond bid l0)) as R1.
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
    unfold wf_ExecutionContext. simpl.
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
    eapply inscope_of_tmn_br_uncond with (cs':=cs')(l':=l')(ps':=ps')
      (tmn':=tmn') in HeqR1; eauto.
    destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
    destruct cs'; rewrite <- HeqR1; auto.
Unfocus.

Case "sBop". abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sFBop".
  abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sExtractValue".
  abstract (eapply preservation_cmd_updated_case; eauto; simpl; eauto).
Case "sInsertValue".
  abstract (eapply preservation_cmd_updated_case; eauto; simpl; eauto).
Case "sMalloc".
  abstract (eapply preservation_cmd_updated_case; eauto; simpl; eauto 10).
Case "sFree".
  abstract (eapply preservation_cmd_non_updated_case; eauto; simpl; auto).
Case "sAlloca".
  abstract (eapply preservation_cmd_updated_case; eauto; simpl; eauto 10).
Case "sLoad".
  abstract (eapply preservation_cmd_updated_case; eauto; simpl; eauto 7).
Case "sStore".
  abstract (eapply preservation_cmd_non_updated_case; eauto; simpl; auto).
Case "sGEP".
  abstract (eapply preservation_cmd_updated_case; eauto; simpl; eauto 9).
Case "sTrunc". abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sExt". abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sCast". abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sIcmp". abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sFcmp". abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sSelect".
  abstract (
    destruct (isGVZero (los, nts) c);
      eapply preservation_cmd_updated_case; eauto; auto
  ).

Case "sCall".
Focus.
  destruct_ctx_other.

  assert (InProductsB (product_fdef (fdef_intro
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    apply OpsemAux.lookupFdefViaPtr_inversion in H1.
    destruct H1 as [fn [H11 H12]].
    eapply lookupFdefViaIDFromProducts_inv; eauto.

  repeat (split; auto).
    assert (uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb)) as Huniq.
      eapply wf_system__uniqFdef; eauto.
    assert (wf_fdef S (module_intro los nts Ps) 
      (fdef_intro (fheader_intro fa rt fid la va) lb)) as HwfF.
      eapply wf_system__wf_fdef; eauto.
    unfold wf_ExecutionContext. simpl.
    assert (ps'=nil) as EQ.
      eapply entryBlock_has_no_phinodes with (s:=S); eauto.
    subst.
    apply dom_entrypoint in H2.

Transparent inscope_of_tmn inscope_of_cmd.

    destruct cs'.
      unfold inscope_of_tmn.
      remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb))
        !! l') as R.
      destruct R. simpl in H2. subst. simpl.
      eapply preservation_dbCall_case; eauto.

      unfold inscope_of_cmd, inscope_of_id.
      rewrite init_scope_spec1; auto.
      remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb))
        !! l') as R.
      destruct R. simpl. simpl in H2. subst. simpl.
      destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n];
        try solve [contradict n; auto].
      eapply preservation_dbCall_case; eauto.
Unfocus.

Case "sExCall".
  abstract (
  match goal with
  | H5: Opsem.exCallUpdateLocals _ _ _ _ _ _ = _ |- _ =>
    unfold Opsem.exCallUpdateLocals in H5;
    destruct noret0; try solve [
      inv H5; eapply preservation_cmd_non_updated_case in HwfS1; eauto; auto |
      destruct oresult; tinv H5;
      remember (fit_gv (los, nts) rt1 g) as R;
      destruct R; inv H5;
      eapply preservation_cmd_updated_case with (Mem1:=Mem') in HwfS1; 
        simpl; eauto; simpl; auto]
  end).
Qed.

(* similar to id_rhs_val *)
Lemma initLocals__wf_defs : forall pi fid l' fa rt la va
  lb gvs lc CurLayouts CurNamedts initGlobal 
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hinit : Opsem.initLocals
     (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty)
     la gvs = Some lc),
   match
     fold_left
       (inscope_of_block (fdef_intro (fheader_intro fa rt fid la va) lb) l')
       nil (ret getArgsIDs la)
   with
   | ret ids0 =>
       wf_defs (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi)
         (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty) initGlobal
         (fdef_intro (fheader_intro fa rt fid la va) lb) lc ids0
   | merror => False
   end.
Proof.
  intros.
  assert (incl nil (bound_blocks lb)) as J.
    intros x J. inv J.
  apply fold_left__bound_blocks with (fh:=fheader_intro fa rt fid la va)(l0:=l')
    (init:=getArgsIDs la) in J.
  destruct J as [r J]. unfold l in *.
  intros EQ gvs1 gvs2 Hinscope1 Hget1 Hget2.
  assert (uniqFdef (PEI_f pi)) as Huniq'. 
    rewrite EQ. auto.
  simpl in *. uniq_result.
  contradict Hinscope1.
  apply PEInfo_p__isnt__arg in Huniq'.
  rewrite EQ in Huniq'. auto.
Qed.

(* similar to id_rhs_val *)
Lemma s_genInitState__inv: forall (S : system) (main : id) (pi: PEInfo) 
  (VarArgs : list (GVsT DGVs)) (cfg : OpsemAux.Config) (IS : Opsem.State)
  (HwfS: wf_system S)
  (Hinit: Opsem.s_genInitState S main VarArgs Mem.empty = ret (cfg, IS)),
  wf_State (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi) cfg IS.
Proof.
  intros.
  simpl_s_genInitState.
Local Opaque inscope_of_tmn inscope_of_cmd.
  simpl.
  split; auto.
    apply getParentOfFdefFromSystem__moduleInProductsInSystemB in HeqR0.
    destruct HeqR0 as [HMinS HinPs].
    assert (uniqFdef (fdef_intro (fheader_intro f t i0 a v) b)) as Huniq.
      eapply wf_system__uniqFdef; eauto.
    unfold wf_ExecutionContext. simpl.
    assert (ps0=nil) as EQ.
      eapply entryBlock_has_no_phinodes with (s:=S); eauto.        
    subst.
Transparent inscope_of_tmn inscope_of_cmd.
    apply dom_entrypoint in HeqR2.
    destruct cs0.
      unfold inscope_of_tmn.
      remember ((dom_analyze (fdef_intro (fheader_intro f t i0 a v) b))
        !! l0) as R.
      destruct R. simpl in HeqR2. subst.
      eapply initLocals__wf_defs; eauto.

      unfold inscope_of_cmd, inscope_of_id.
      rewrite init_scope_spec1; auto.
      remember ((dom_analyze (fdef_intro (fheader_intro f t i0 a v) b))
        !! l0) as R.
      destruct R. simpl. simpl in HeqR2. subst.
      destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n];
        try solve [contradict n; auto].
      eapply initLocals__wf_defs; eauto.
Qed.

