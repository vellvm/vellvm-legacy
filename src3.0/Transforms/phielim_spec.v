Require Import vellvm.
Require Import primitives.
Require Import vmem2reg.
Require Import trans_tactic.
Require Import Dipaths.

Lemma all_non_reachable__or__ex_reachable: forall f v (vls:list (value*l)),
  (forall l0, In (v,l0) vls -> ~ reachable f l0) \/
  exists l0, In (v,l0) vls /\ reachable f l0.
Proof.
  induction vls as [|[v1 l1]]. 
    auto.
          
    destruct (value_dec v v1); subst.
      destruct (reachable_dec f l1).
        right.
        exists l1. simpl. auto.

        destruct IHvls.
          left. simpl.
          intros l0 Hin.
          destruct Hin as [Hin | Hin]; auto.
            inv Hin. auto.
          
          right. destruct H0 as [l0 [Hin Hreach]].
          exists l0. simpl. auto.

      destruct IHvls.
        left. simpl.
        intros l0 Hin.
        destruct Hin as [Hin | Hin]; auto.
          inv Hin. auto.
        
        right. destruct H as [l0 [Hin Hreach]].
        exists l0. simpl. auto.
Qed.

Lemma eliminate_phi_false_spec: forall f p f'
  (Helim: (f', false) = eliminate_phi f p), f = f'.
Proof.
  destruct p as [pid pty pvls].
  unfold eliminate_phi.
  intros. 
  remember (remove_redundancy nil (value_id pid :: List.map fst pvls)) 
    as R.
  destruct R as [|[] l0]; inv Helim; auto.
    repeat destruct_if; auto.

    destruct l0 as [|[] l0]; inv H0; try solve [
      auto |
      destruct l0 as [|]; inv H1; 
        try solve [auto | repeat destruct_if; auto]
    ].

    destruct l0 as [|? [|]]; inv H0; 
      try solve [auto | repeat destruct_if; auto].
Qed.

Lemma eliminate_phis_false_spec: forall f' f ps0
  (Helim: (f', false) = eliminate_phis f ps0 ), f' = f.
Proof.
  induction ps0 as [|p]; simpl; intros.
    congruence.

    remember (eliminate_phi f p) as R.
    destruct R as []; inv Helim.
    destruct_if; auto.
    apply eliminate_phi_false_spec in HeqR. subst. auto.
Qed.

(* b0 defines a phinode whose reachable incoming values are all defined in b0 *)
Inductive selfrefl_phi (f:fdef) (b0:block): phinode -> Prop :=
| selfrefl_phi_intro: forall pid ty vls
    (Hinc: insnInFdefBlockB (insn_phinode (insn_phi pid ty vls)) f b0 = true)
    (Hid: forall v1 l1, In (v1, l1) vls -> 
            (~ reachable f l1) \/
            exists vid1, 
              v1 = value_id vid1 /\ 
              lookupBlockViaIDFromFdef f vid1 = Some b0),
    selfrefl_phi f b0 (insn_phi pid ty vls)
.

Lemma selfrelf_phi_cannot_be_in_reachable_blocks: forall (S : system)
  (M : module) (f : fdef)(Hwf : wf_fdef S M f) (Huniq : uniqFdef f)
  b (Hreach: isReachableFromEntry f b) p
  (Hsefl: selfrefl_phi f b p), False.
Proof.
  intros.
  inv Hsefl.
  apply destruct_insnInFdefBlockB in Hinc.
  destruct Hinc as [HPinB HBinF].
  assert (Hwfp:=HBinF). 
  destruct b as [l0 [ps0 cs0 tmn0]].
  simpl in HPinB. apply InPhiNodesB_In in HPinB.
  eapply wf_fdef__wf_phinodes in Hwfp; eauto.
  eapply wf_phinodes__wf_phinode in Hwfp; eauto.
  inv Hwfp.
  assert (lookupBlockViaIDFromFdef f 
           (getPhiNodeID (insn_phi pid ty vls)) = 
           Some (l0, stmts_intro ps0 cs0 tmn0)) as Hlkup.
    solve_lookupBlockViaIDFromFdef.
  match goal with
  | H6: wf_phinode _  _ _ |- _ => destruct H6 as [Hwfops Hwflist]
  end.
  caseEq (getEntryBlock f); 
    try solve [intros Hentry; apply wf_fdef__non_entry in Hwf; auto; congruence].
  intros be Hentry.
  destruct (l_dec (getBlockLabel be) 
                  (getBlockLabel (l0, stmts_intro ps0 cs0 tmn0))) as [Heq | Hneq].
  Case "the current block is entry? no!".
    destruct be; simpl in *; subst.
    assert (HBinF':=Hentry).
    apply entryBlockInFdef in HBinF'.
    eapply blockInFdefB_uniq in HBinF; eauto.
    inv HBinF.
    eapply wf_fdef_entryBlock_has_no_phinodes in Hentry; eauto.
    subst; tauto.

  Case "the current block isnt enty. good".
    assert (Hentry_sdom:=Hentry).
    eapply entry_blockStrictDominates_others in Hentry_sdom; eauto 1.
    assert (~ In pid (getArgsIDsOfFdef f)) as Hid5notinfh.
      solve_notin_getArgsIDs.
    assert (forall vid vl, 
                ~ In vid (getArgsIDsOfFdef f) ->
                In (value_id vid,vl) vls -> 
                reachable f vl ->
                exists bv, exists bvl, 
                  lookupBlockViaLabelFromFdef f vl = Some bvl /\
                  lookupBlockViaIDFromFdef f vid = Some bv /\
                  domination f (getBlockLabel bv) vl) as Hvid_spec.
       intros. eapply wf_phi_operands__elim''; eauto.

   (* l0 is reachable, so one of its pred must be reachable, say l1 *)
    assert (exists v0, exists l0, In (v0, l0) vls /\ reachable f l0)
      as Hex_reach_pred.
      eapply reachable_phinode__ex_reachable_incoming; eauto.

    destruct Hex_reach_pred as [v1 [l1 [Hinlist1 Hreach1]]].
    assert (Hinlist1':=Hinlist1).
    apply Hid in Hinlist1'.
    destruct Hinlist1' as [? | [vid1 [Heq Hlkup1]]]; subst; try congruence.
    assert (Hinlist1':=Hinlist1).
    apply Hvid_spec in Hinlist1'; try solve [auto | solve_notin_getArgsIDs].
    destruct Hinlist1' as [bv1 [bvl1 [Hlkupbvl1 [Hlkupbv1 Hdom]]]].
    uniq_result.

    (* Get the path from entry to l1, l0 must be on the path. *)
    unfold_reachable_tac.
    unfold_domination_tac.
    apply DWalk_to_dpath in Hwalk; auto.
    destruct Hwalk as [vl0 [al0 Hpath]].
    assert (Hwalk:=Hpath).
    apply D_path_isa_walk in Hwalk.
    apply_clear Hdom in Hwalk.

    (* split path by l0 *)
    assert (Hpath':=Hpath).
    apply DP_split with (x:=index l0) in Hpath'; try solve
      [simpl in *; destruct Hwalk; subst; auto | auto]. 
    destruct Hpath' as [al1 [al2 [vl1 [vl2 [Hpath1 [Hpath2 [EQ1 EQ2]]]]]]]; subst.

    (* in the path from entry to l0, the neigher of l0 must be the pred of l0,
       say ly, which cannot be entry *)
    simpl in Hneq.
    assert (Hpath2':=Hpath2).
    inv Hpath2; try congruence.

    match goal with
    | H4: ACfg.arcs _ (A_ends _ ?y),
      H: D_path _ _ ?y _ _ _ |- _ => 
       rename H4 into Harc; destruct y as [ly];
       assert (Hwalk2:=H); apply D_path_isa_walk in Hwalk2
    end.
    eapply wf_phi_operands__successors in Hwflist; eauto 1.
    destruct Hwflist as [v2 Hinlist2].

    assert (reachable f ly) as Hreachy.
      unfold reachable, ACfg.reachable. fill_ctxhole. eauto.

    assert (Hinlist2':=Hinlist2).
    apply Hid in Hinlist2'; auto.
    destruct Hinlist2' as [Hinlist2' | [vid2' [EQ1 Hlkup2']]]; try congruence.
    inv EQ1.
    
    assert (~ In vid2' (getArgsIDsOfFdef f)) as Hnotargs2.
      solve_notin_getArgsIDs.

    apply Hvid_spec in Hinlist2; auto.
    destruct Hinlist2 as [bv2 [bvl2 [Hlkupbvl2 [Hlkupbv2 Hdom2]]]].
    uniq_result.

    (* In the path from entry to ly, l0 must be there, since l0 doms ly.
       But, a simple path cannot contain two l0. *)
    unfold_domination_tac.
    apply Hdom2 in Hwalk2.
    clear - Hwalk2 Hpath2' Hneq. simpl in *.
    apply DP_endx_ninV in Hpath2'; try congruence.
      apply Hpath2'.
      simpl.
      destruct Hwalk2; subst; auto.
Qed.

(* 
  all incoming variables equal to the variable defined by the phinode:
    vid = phi [vid vid ... vid] 
*)
Inductive identity_phi: phinode -> Prop :=
| identity_phi_intro: forall vid ty vls
    (Hid: forall v0 l0, In (v0, l0) vls -> v0 = value_id vid),
    identity_phi (insn_phi vid ty vls)
.

Lemma identity_phi__selfrefl_phi: forall l0 ps0 cs0 tmn0 f p
  (HBinF: blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) f = true)
  (Hin: In p ps0) (Hid: identity_phi p) (Huniq: uniqFdef f),
  selfrefl_phi f (l0, stmts_intro ps0 cs0 tmn0) p.
Proof.
  intros.
  inv Hid.
  apply selfrefl_phi_intro.
    simpl.
    bsplit; auto. solve_in_list.

    intros.
    apply Hid0 in H. subst.
    right.
    exists vid. 
    split; auto.
      apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
      simpl. apply getPhiNodeID_in_getPhiNodesIDs in Hin.
      xsolve_in_list.
Qed.

Lemma identity_phi_cannot_be_in_reachable_blocks: forall S M p f
  l0 ps0 cs0 tmn0 (Hreach: reachable f l0) 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) f = true)
  (Hin: In p ps0) (Hid: identity_phi p),
  False. 
Proof.
  intros.
  eapply selfrelf_phi_cannot_be_in_reachable_blocks 
    with (b:=(l0, stmts_intro ps0 cs0 tmn0))(p:=p) in Hwf; 
    eauto using identity_phi__selfrefl_phi.
Qed.

(* 
  all incoming values equal to either v or the variable defined by the phinode:
    vid = phi [vid v ... vid v] 
*)
Inductive assigned_phi (v:value): phinode -> Prop :=
| assigned_phi_intro: forall vid ty vls
    (Hex: exists l0, In (v, l0) vls)
    (Hassign: forall v0 l0, In (v0, l0) vls -> v0 = value_id vid \/ v0 = v),
    assigned_phi v (insn_phi vid ty vls)
.

Lemma assigned_phi_unreachable_vid__selfrefl_phi: forall l0 ps0 cs0 tmn0 f ty 
  vls vid (HBinF: blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) f = true) id0
  (Hin: In (insn_phi id0 ty vls) ps0) (Hreach: reachable f l0)
  (Has: assigned_phi (value_id vid) (insn_phi id0 ty vls)) (Huniq: uniqFdef f)
  (Hnoreachvid : forall l0 : l,
                 In (value_id vid, l0) vls -> ~ reachable f l0),
  selfrefl_phi f (l0, stmts_intro ps0 cs0 tmn0) (insn_phi id0 ty vls).
Proof.
  intros.
  inv Has.
  apply selfrefl_phi_intro.
    simpl.
    bsplit; auto. solve_in_list.

    intros v1 l1 Hin'.
    assert (J:=Hin').
    apply Hassign in J.
    destruct J; subst. 
      right.
      exists id0.
      split; auto.
        apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
        simpl. apply getPhiNodeID_in_getPhiNodesIDs in Hin.
        xsolve_in_list.

      left. auto.
Qed.

Lemma assigned_phi__domination: forall S M p f l0 ps0 cs0 tmn0
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) f = true) 
  (Hin: In p ps0) v (Has: assigned_phi v p),
  valueDominates f v (value_id (getPhiNodeID p)).
Proof.
  intros.
  destruct v as [vid|]; simpl; auto.
  intros Hidreach.
  assert (Hwfp:=HBinF).
  eapply wf_fdef__wf_phinodes in Hwfp; eauto.
  eapply wf_phinodes__wf_phinode in Hwfp; eauto.
  inv Hwfp.
  assert (lookupBlockViaIDFromFdef f 
           (getPhiNodeID (insn_phi id5 typ5 value_l_list)) = 
           Some (l0, stmts_intro ps0 cs0 tmn0)) as Hlkup.
    solve_lookupBlockViaIDFromFdef.
  assert (isReachableFromEntry f (l0, stmts_intro ps0 cs0 tmn0)) as Hreach.
    apply Hidreach; auto.
  match goal with
  | H6: wf_phinode _  _ _ |- _ => destruct H6 as [Hwfops Hwflist]
  end.
  caseEq (getEntryBlock f); 
    try solve [intros Hentry; apply wf_fdef__non_entry in Hwf; auto; congruence].
  intros be Hentry.
  destruct (l_dec (getBlockLabel be) 
                  (getBlockLabel (l0, stmts_intro ps0 cs0 tmn0))) as [Heq | Hneq].
  Case "the current block is entry? no!".
    destruct be; simpl in *; subst.
    assert (HBinF':=Hentry).
    apply entryBlockInFdef in HBinF'.
    eapply blockInFdefB_uniq in HBinF; eauto.
    inv HBinF.
    eapply wf_fdef_entryBlock_has_no_phinodes in Hentry; eauto.
    subst; tauto.

  Case "the current block isnt enty. good".
    assert (Hentry_sdom:=Hentry).
    eapply entry_blockStrictDominates_others in Hentry_sdom; eauto 1.
    unfold idDominates.
    fill_ctxhole. 
    caseEq (inscope_of_id f (l0, stmts_intro ps0 cs0 tmn0)
       (getPhiNodeID (insn_phi id5 typ5 value_l_list))); 
      try solve [intros Hinscope; contradict Hinscope;
                 apply inscope_of_id__total].
    unfold inscope_of_id, init_scope.
    intros ids1 Hinscope.
    destruct_if.
    SCase "id5 in ps. nice".
      destruct (in_dec id_dec vid (getArgsIDsOfFdef f)) as [Hinfh | Hnotinfh].
      SSCase "vid in args".
        apply fold_left__init in H2. auto.
 
      SSCase "vid notin args".
        assert (~ In id5 (getArgsIDsOfFdef f)) as Hid5notinfh.
          solve_notin_getArgsIDs.
        assert (forall vid vl, 
                ~ In vid (getArgsIDsOfFdef f) ->
                In (value_id vid,vl) value_l_list -> 
                reachable f vl ->
                exists bv, exists bvl, 
                  lookupBlockViaLabelFromFdef f vl = Some bvl /\
                  lookupBlockViaIDFromFdef f vid = Some bv /\
                  domination f (getBlockLabel bv) vl) as Hvid_spec.
          intros. eapply wf_phi_operands__elim''; eauto.
        assert ((forall l0, In (value_id vid,l0) value_l_list -> ~ reachable f l0) \/
                 exists l0, In (value_id vid,l0) value_l_list /\ reachable f l0) as Hdec.
          apply all_non_reachable__or__ex_reachable; auto.

        destruct Hdec as [Hnoreachvid | [vl [Hinlist Hreachvid]]].
        SSSCase "no vid is reachable".
          eapply assigned_phi_unreachable_vid__selfrefl_phi in Has; eauto. 
          elimtype False.
          eapply selfrelf_phi_cannot_be_in_reachable_blocks in Has; eauto.

        SSSCase "vid is reach".
          eapply wf_phi_operands__elim' in Hinlist; eauto.
          destruct Hinlist 
            as [blv [Hlkupblv [[[bv [Hlkbv Hdom]]|Hnreachblv]|?]]]; 
            try congruence.
          SSSSCase "bv doms blv". 
            destruct (DecDom.sdom_dec f (getBlockLabel bv) l0) as [Hsdom | Hnsdom].
            SSSSSCase "bv sdoms blv".
              apply fold_left__spec in H2.
              destruct H2 as [_ [H2 _]].
              eapply H2 with (b1:=snd bv)(l1:=getBlockLabel bv); eauto 1.
                assert (getBlockLabel bv <> l0) as Hneq'.
                  apply DecDom.sdom_isnt_refl in Hsdom; auto.
                apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkbv; auto.
                destruct bv.
                eapply sdom_is_complete in Hsdom; eauto 1.
                  apply ListSet.set_diff_intro; auto.
                    simpl in *. intro J. destruct J as [J|J]; auto.

                  eapply blockStrictDominates__non_empty_contents in Hentry_sdom; 
                    eauto.
                destruct bv. solve_lookupBlockViaLabelFromFdef.
                solve_in_list. auto.
            SSSSSCase "bv doesnt sdom blv".
              eapply DecDom.non_sdom__inv in Hnsdom; eauto 1.
              destruct Hnsdom as [vl1 [al1 [Hwalk Hnsdom]]].
              assert (getBlockLabel bv = l0 \/ ~ In (index (getBlockLabel bv)) vl1) as K.
                clear - Hnsdom. tauto.
              destruct K as [EQ | Hnotonwalk]; subst.
              SSSSSSCase "all incomings are self".
                elimtype False.
                eapply selfrelf_phi_cannot_be_in_reachable_blocks 
                  with (p:=insn_phi id5 typ5 value_l_list); eauto.
                  apply selfrefl_phi_intro.
                    simpl. bsplit; auto. solve_in_list.

                    intros v1 l1 Hinlist.
                    inv Has.
                    apply Hassign in Hinlist.
                    right.
                    destruct Hinlist; subst.
                      exists id5.
                      split; auto.
                        
                      exists vid.
                      split; auto.
                        assert (J:=Hlkbv).
                        apply lookupBlockViaIDFromFdef__blockInFdefB in J.
                        destruct bv.
                        eapply blockInFdefB_uniq in HBinF; eauto.
                        destruct HBinF as [EQ1 [EQ2 EQ3]]; subst. auto.

              SSSSSSCase "ex a non-sdom walk".
                apply DWalk_to_dpath' in Hwalk; auto.
                (* consider a simple path from entry to l0, which doesnt
                   contain vid's block *)
                destruct Hwalk as [vl0 [al0 [Hpath Hinc]]].
                simpl in Hneq.
                inv Hpath; try congruence.
                match goal with
                | H: D_path _ _ _ _ _ _ |- _ => 
                  assert (Hwalk:=H); apply D_path_isa_walk in Hwalk
                end.
                destruct y as [ly].
                assert (reachable f ly) as Hreachy.
                  unfold reachable, ACfg.reachable. fill_ctxhole. 
                  destruct be. eauto.
                match goal with
                | H4: arcs_fdef _ _ |- _ => rename H4 into Harc
                end.
                eapply wf_phi_operands__successors in Hwflist; eauto 1.
                destruct Hwflist as [v1 Hinlist].
                assert (Hvid_eq:=Hinlist).
                inv Has.
                apply Hassign in Hvid_eq.

                (* the path must be from pid or vid's incoming blocks *)
                destruct Hvid_eq as [Hvid_eq | Hvid_eq]; inv Hvid_eq.
                SSSSSSSCase "from pid".
                  (* pid must appear between entry to pred, then this is
                     not a simple path *)
                  eapply Hvid_spec in Hinlist; eauto 1.
                  destruct Hinlist 
                    as [by0 [bly0 [Hlkbly0 [Hlkby0 Hby0_dom_bly0]]]].
                  simpl in *. uniq_result.
                  lookupBlockViaLabelFromFdef_inv_tac.
                  unfold domination, ACfg.domination in Hby0_dom_bly0.
                  rewrite Hentry in Hby0_dom_bly0.
                  destruct be as [le ? ? ?].
                  apply Hby0_dom_bly0 in Hwalk.
                  destruct Hwalk as [Hinpath | EQ]; subst; simpl in *.
                    apply H7 in Hinpath. inv Hinpath. congruence.
                    elimtype False. auto.

                SSSSSSSCase "from vid".
                  (* then vid's block must appear in the path, contradict. *)
                  eapply Hvid_spec in Hinlist; eauto 1.
                  destruct Hinlist 
                    as [by0 [bly0 [Hlkbly0 [Hlkby0 Hby0_dom_bly0]]]].
                  simpl in *. uniq_result.
                  lookupBlockViaLabelFromFdef_inv_tac.
                  unfold domination, ACfg.domination in Hby0_dom_bly0.
                  rewrite Hentry in Hby0_dom_bly0.
                  destruct be as [le ? ? ?].
                  apply Hby0_dom_bly0 in Hwalk.
                  contradict Hnotonwalk.
                  destruct Hwalk as [Hinpath | EQ]; 
                    subst; simpl in *; apply Hinc; auto.
              
          SSSSCase "blv is unreach".
            lookupBlockViaLabelFromFdef_inv_tac.
            simpl in *. congruence.

    SCase "id5 notin ps? no".
      clear HeqR.
      contradict n. solve_in_list.
Qed.

Lemma valueInListValueB_spec: forall (v:value) (vs:list value),
  valueInListValueB v vs = true <-> In v vs.
Proof.
  unfold valueInListValueB.
  induction vs; simpl.
    split; try solve [tauto | congruence].
  
    destruct IHvs as [J1 J2].
    remember (valueEqB v a) as R.
    split; intro J.
      destruct R; auto.
        symmetry in HeqR.
        apply valueEqB_inv in HeqR. subst. auto.

      destruct J.
        subst v R.
        rewrite valueEqB_refl.
        apply fold_left_or_spec.
          intros; subst; auto.

        destruct R; auto.
          apply fold_left_or_spec.
            intros; subst; auto.
Qed.

Lemma remove_redundancy_aux: forall vs acc re
  (Hred: re = remove_redundancy acc vs) 
  (Hnodup: NoDup (values2ids acc)),
  (forall v0, (In v0 vs \/ In v0 acc) <-> In v0 re) /\
  NoDup (values2ids re).
Proof.
  intros.
  generalize dependent acc.
  generalize dependent re.
  induction vs as [|v vs]; simpl; intros; subst.
    tauto.

    destruct_if.
      assert (J:=Hnodup).
      eapply IHvs in J; eauto.
      simpl_env in J.
      destruct J as [J1 J2].
      symmetry in HeqR.
      apply valueInListValueB_spec in HeqR.
      split; auto.
        intro v0.
        split; intro J.
          apply J1. 
          destruct J as [J | J]; auto.
          destruct J as [J | J]; subst; auto.

          apply J1 in J. tauto.

      assert (NoDup (values2ids (v::acc))) as Hnodup'.
        simpl. 
        destruct v as [vid|vc]; auto.
        constructor; auto.
          destruct (In_dec id_dec vid (values2ids acc)) as [Hin | Hnotin]; auto.
            apply valueInValues__iff__InOps in Hin.
            apply valueInListValueB_spec in Hin. congruence.

      assert (J:=Hnodup').
      eapply IHvs with (acc:=v::acc) in J; eauto.
      simpl_env in J.
      destruct J as [J1 J2].
      simpl_env.
      split; auto.
        intro v0.
        split; intro J.
          apply J1. simpl. tauto.

          apply J1 in J. simpl in J. tauto.
Qed.

Lemma remove_redundancy: forall vs vs'
  (Hred: vs' = remove_redundancy nil vs),
  (forall v0, In v0 vs <-> In v0 vs') /\
  NoDup (values2ids vs').
Proof.
  intros.
  apply remove_redundancy_aux in Hred; simpl; auto.
  destruct Hred as [J1 J2].
  split; auto.
    intros v0.  
    destruct (J1 v0) as [J3 J4].
    split; auto.
      intro J.
      apply J4 in J. tauto.
Qed.

Lemma eliminate_phi_true_spec: forall S M f b f'
  (Hreach: isReachableFromEntry f b) p 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HPinF: phinodeInFdefBlockB p f b = true)
  (Helim: (f', true) = eliminate_phi f p),
  (used_in_fdef (getPhiNodeID p) f = false /\
     f' = remove_fdef (getPhiNodeID p) f) \/
  exists v, assigned_phi v p /\ 
    f' = remove_fdef (getPhiNodeID p) (subst_fdef (getPhiNodeID p) v f).
Proof.
  destruct p as [pid pty pvls].
  unfold eliminate_phi.
  intros. 
  bdestruct HPinF as HPinB HBinF.
  destruct b as [l0 [ps0 cs0 tmn0]].
  simpl in HPinB. apply InPhiNodesB_In in HPinB.
  remember (vmem2reg.remove_redundancy nil 
             (value_id pid :: List.map fst pvls)) as vs.
  apply remove_redundancy in Heqvs.
  destruct Heqvs as [Hinc Hnodup].
  rewrite <- fst_split__map_fst in Hinc.
  destruct vs as [|v1 vs']; try solve [repeat destruct_if; auto].
  destruct v1 as [vid1 | vc1].
  Case "1".
    destruct vs' as [|v2].
    SCase "1.1: pid = phi pid ... pid".
      elimtype False.
      eapply identity_phi_cannot_be_in_reachable_blocks; eauto 1.
      constructor.
        intros v1 l1 Hin.
        apply in_split_l in Hin. simpl in Hin.
        assert (pid = vid1) as EQ.
          assert (In (value_id pid) (value_id vid1 :: nil)) as Hin1.
            apply Hinc; simpl; auto.
            destruct_in Hin1; try tauto. 
          congruence.
        subst.
        assert (In v1 (value_id vid1 :: fst (split pvls))) as Hin'.
          simpl. auto.
        apply Hinc in Hin'.
        destruct_in Hin'; try tauto. 
       
    SCase "1.2".
      destruct vs' as [|]; try solve [repeat destruct_if; auto].
      SSCase "1.2.1: pid = phi v2 .. v2 . pid".
        right.
        destruct_dec; inv Helim.
          SSSCase "pid=vid1".
          exists v2.
          split; auto.
            constructor.
              apply split_l_in; auto.
              assert (In v2 (value_id vid1 :: v2 :: nil)) as Hin.
                simpl; auto.
              apply Hinc in Hin.
              destruct_in Hin.
                simpl in Hnodup. inv Hnodup. simpl in H1. tauto.

              intros v1 l1 Hin.  
              apply in_split_l in Hin. simpl in Hin.
              assert (In v1 (value_id vid1 :: fst (split pvls))) as Hin'.
                simpl. auto.
              apply Hinc in Hin'.
              destruct_in Hin'; auto.
              destruct Hin'; subst; tauto.

          SSSCase "pid<>vid1".
          exists (value_id vid1). 
          split; auto.
            constructor.
              apply split_l_in; auto.
              assert (In (value_id vid1) (value_id vid1 :: v2 :: nil)) as Hin.
                simpl; auto.
              apply Hinc in Hin.
              destruct_in Hin. 
                congruence.

              assert (v2 = value_id pid) as EQ.         
                assert (In (value_id pid) (value_id pid :: fst (split pvls))) 
                  as Hin0.
                  simpl; auto.
                apply Hinc in Hin0.
                destruct_in Hin0.
                  congruence.
              subst.
              intros v1 l1 Hin.  
              apply in_split_l in Hin. simpl in Hin.
              assert (In v1 (value_id pid :: fst (split pvls))) as Hin'.
                simpl. auto.
              apply Hinc in Hin'.
              destruct_in Hin'; auto.
              destruct Hin'; subst; tauto.

  Case "2".
    destruct vs' as [|? vs']; try solve [repeat destruct_if; auto].
    SCase "2.1: pid = vc".
      right.
      assert (In (value_id pid) (value_id pid :: fst (split pvls))) as Hin.
        simpl; auto.
      apply Hinc in Hin.
      destruct_in Hin.
        congruence.

    SCase "2.2".
      destruct vs' as [|? vs']; try solve [repeat destruct_if; auto].
        SSCase "2.2.2: pid = phi pid c .. c . pid".
        inv Helim. right.
        assert (v = value_id pid) as EQ.         
          assert (In (value_id pid) (value_id pid :: fst (split pvls))) 
            as Hin0.
            simpl; auto.
          apply Hinc in Hin0.
          destruct_in Hin0.
            congruence.
        subst.
        exists (value_const vc1).
        split; auto.
        constructor.
          apply split_l_in; auto.
          assert (In (value_const vc1) (value_const vc1 :: value_id pid :: nil))  
            as Hin.
            simpl; auto.
          apply Hinc in Hin.
          destruct_in Hin. 
            congruence.

          intros v1 l1 Hin.  
          apply in_split_l in Hin. simpl in Hin.
          assert (In v1 (value_id pid :: fst (split pvls))) as Hin'.
            simpl. auto.
          apply Hinc in Hin'.
          destruct_in Hin'; auto.
          destruct Hin'; subst; tauto.
Qed.

Lemma eliminate_phis_true_spec': forall f b f' S M 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (Hreach: isReachableFromEntry f b) ps
  (HBinF: forall p, In p ps -> phinodeInFdefBlockB p f b = true)
  (Helim: (f', true) = eliminate_phis f ps),
  exists p, In p ps /\ 
    ((used_in_fdef (getPhiNodeID p) f = false /\
      f' = remove_fdef (getPhiNodeID p) f) \/
    exists v, assigned_phi v p /\ 
      f' = remove_fdef (getPhiNodeID p) (subst_fdef (getPhiNodeID p) v f)).
Proof.
  induction ps as [|p]; simpl; intros.
    inv Helim.

    remember (eliminate_phi f p) as R.
    destruct R as []; inv Helim.
    destruct_if.
      exists p.
      split; auto. 
      eapply eliminate_phi_true_spec in HeqR; eauto.

      apply eliminate_phi_false_spec in HeqR. subst. 
      apply IHps in H1; auto. 
      destruct H1 as [p' [Hin [H1 | [v [H1 H2]]]]]; eauto 7.
Qed.
    
Lemma eliminate_phis_true_spec: forall f f' l0 S M 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (Hreach: reachable f l0) ps cs0 tmn0
  (HBinF: blockInFdefB (l0, stmts_intro ps cs0 tmn0) f = true)
  (Helim: (f', true) = eliminate_phis f ps),
  exists p, In p ps /\ 
    ((used_in_fdef (getPhiNodeID p) f = false /\
      f' = remove_fdef (getPhiNodeID p) f) \/
    exists v, assigned_phi v p /\ 
      f' = remove_fdef (getPhiNodeID p) (subst_fdef (getPhiNodeID p) v f)).
Proof.
  intros.
  eapply eliminate_phis_true_spec' with (b:=(l0, stmts_intro ps cs0 tmn0)); 
    simpl; eauto 1.
  intros.
  bsplit; auto. simpl. solve_in_list.
Qed.

Lemma assigned_phi__wf_value: forall S M p f l0 ps0 cs0 tmn0
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) f = true) 
  (Hin: In p ps0) v (Hassign: assigned_phi v p),
  forall ty, 
    lookupTypViaIDFromFdef f (getPhiNodeID p) = Some ty ->
    wf_value S M f v ty.
Proof.
  intros.
  erewrite uniqF__lookupPhiNodeTypViaIDFromFdef in H; eauto.
  inv H.
  assert (Hwfp:=HBinF).
  eapply wf_fdef__wf_phinodes in Hwfp; eauto.
  eapply wf_phinodes__wf_phinode in Hwfp; eauto.
  inv Hwfp.
  inv Hassign.
  destruct Hex as [lv Hinlist].
  apply H0.
  rewrite <- fst_split__map_fst. 
  apply in_split_l in Hinlist; auto.
Qed.
