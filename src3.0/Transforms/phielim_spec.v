Require Import vellvm.
Require Import primitives.
Require Import mem2reg.
Require Import trans_tactic.

Lemma eliminate_phi_false_spec: forall f p f'
  (Helim: (f', false) = eliminate_phi f p), f = f'.
Admitted. (* spec *)

Lemma lookupBlockViaLabelFromFdef_self: forall f bv (Huniq: uniqFdef f),
  lookupBlockViaLabelFromFdef f (getBlockLabel bv) = ret bv.
Admitted.

Ltac solve_lookupBlockViaLabelFromFdef' :=
match goal with
| Huniq: uniqFdef ?f |- 
  lookupBlockViaLabelFromFdef ?f (getBlockLabel ?b) = ret ?b =>
    eapply lookupBlockViaLabelFromFdef_self; eauto
| _ => solve_lookupBlockViaLabelFromFdef
end.

Require Import Dipaths.

Lemma non_sdom__inv: forall f l1 l2 be (Hentry: getEntryBlock f = Some be)
  (Hnsdom: ~ strict_domination f l1 l2),
  l1 = l2 \/ 
  exists vl, exists al, D_walk (vertexes_fdef f) (arcs_fdef f) 
    (index l2) (index (getBlockLabel be)) vl al /\
    ~ In (index l1) vl.
Admitted.

Lemma wf_phi_operands__successors: forall (S : system) (M : module) (f : fdef)
  (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator) 
  (Hwf : wf_fdef S M f) (Huniq : uniqFdef f) (value_l_list : list (value * l))
  (id5 : id) (typ5 : typ)
  (Hwfops : wf_phi_operands f (block_intro l0 ps0 cs0 tmn0) id5 typ5
              value_l_list) l1
  (Hscs: arcs_fdef f (A_ends (index l0) (index l1))),
  exists vid1, In (value_id vid1, l1) value_l_list.
Admitted.

Require Import Kildall.

Lemma blockInFdef__bound_fdef: forall f b,
  blockInFdefB b f = true ->
  In (getBlockLabel b) (bound_fdef f).
Admitted.

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
  destruct b as [l0 ps0 cs0 tmn0].
  simpl in HPinB. apply InPhiNodesB_In in HPinB.
  eapply wf_fdef__wf_phinodes in Hwfp; eauto.
  eapply wf_phinodes__wf_phinode in Hwfp; eauto.
  inv Hwfp.
  assert (lookupBlockViaIDFromFdef f 
           (getPhiNodeID (insn_phi pid ty vls)) = 
           Some (block_intro l0 ps0 cs0 tmn0)) as Hlkup.
    solve_lookupBlockViaIDFromFdef.
  match goal with
  | H6: wf_phinode _  _ _ |- _ => destruct H6 as [Hwfops Hwflist]
  end.
  caseEq (getEntryBlock f); 
    try solve [intros Hentry; apply wf_fdef__non_entry in Hwf; auto; congruence].
  intros be Hentry.
  destruct (l_dec (getBlockLabel be) 
                  (getBlockLabel (block_intro l0 ps0 cs0 tmn0))) as [Heq | Hneq].
  Case "the current block is entry? no!".
    destruct be; simpl in *; subst.
    assert (HBinF':=Hentry).
    apply entryBlockInFdef in HBinF'.
    eapply blockInFdefB_uniq in HBinF; eauto.
    destruct HBinF as [EQ1 [EQ2 EQ3]]; subst.
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

    (* entry cannot be l0's incoming block, 
       otherwise l0 must sdom entry, or be entry. *)
    assert (forall v vl, In (v,vl) vls -> vl <> getBlockLabel be)
      as Hincoming_neq_entry.
      admit.

    (* l0 is reachable, so one of its pred must be reachable, say l1 *)
    assert (exists v0, exists l0, In (v0, l0) vls /\ reachable f l0)
      as Hex_reach_pred.
      admit.
    destruct Hex_reach_pred as [v1 [l1 [Hinlist1 Hreach1]]].
    assert (Hinlist1':=Hinlist1).
    apply Hid in Hinlist1'.
    destruct Hinlist1' as [? | [vid1 [Heq Hlkup1]]]; subst; try congruence.
    assert (Hinlist1':=Hinlist1).
    apply Hvid_spec in Hinlist1'; try solve [auto | solve_notin_getArgsIDs].
    destruct Hinlist1' as [bv1 [bvl1 [Hlkupbvl1 [Hlkupbv1 Hdom]]]].
    uniq_result.

    (* Get the path from entry to l1, l0 must be on the path. *)
    unfold domination in Hdom.
    unfold reachable in Hreach1.
    rewrite Hentry in Hdom. 
    rewrite Hentry in Hreach1. 
    destruct be as [le ? ? ?].
    destruct Hreach1 as [vl [al Hwalk]].
    apply DWalk_to_dpath in Hwalk.
    destruct Hwalk as [vl0 [al0 Hpath]].
    assert (Hwalk:=Hpath).
    apply D_path_isa_walk in Hwalk.
    apply_clear Hdom in Hwalk.

    (* split path by l0 *)
    assert (Hpath':=Hpath).
    apply DP_split with (x:=index l0) in Hpath'; try solve
      [simpl in *; destruct Hwalk; subst; auto]. 
    destruct Hpath' as [al1 [al2 [vl1 [vl2 [Hpath1 [Hpath2 [EQ1 EQ2]]]]]]]; subst.

    (* in the path from entry to l0, the neigher of l0 must be the pred of l0,
       say ly, which cannot be entry *)
    simpl in Hneq.
    assert (Hpath2':=Hpath2).
    inv Hpath2; try congruence.

    match goal with
    | H4: arcs_fdef _ (A_ends _ ?y),
      H: D_path _ _ ?y _ _ _ |- _ => 
       rename H4 into Harc; destruct y as [ly];
       assert (Hwalk2:=H); apply D_path_isa_walk in Hwalk2
    end.
    eapply wf_phi_operands__successors in Harc; eauto 1.
    destruct Harc as [vid2 Hinlist2].

    assert (reachable f ly) as Hreachy.
      unfold reachable. fill_ctxhole. eauto.

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
    unfold domination in Hdom2.
    rewrite Hentry in Hdom2.
    apply Hdom2 in Hwalk2.
    clear - Hwalk2 Hpath2' Hneq. simpl in *.
    apply DP_endx_ninV in Hpath2'; try congruence.
      apply Hpath2'.
      simpl.
      destruct Hwalk2; subst; auto.
Qed.

(* vid = phi [vid vid ... vid] *)
Inductive identity_phi: phinode -> Prop :=
| identity_phi_intro: forall vid ty vls
    (Hid: forall v0 l0, In (v0, l0) vls -> v0 = value_id vid),
    identity_phi (insn_phi vid ty vls)
.

Lemma identity_phi__selfrefl_phi: forall l0 ps0 cs0 tmn0 f p
  (HBinF: blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true)
  (Hin: In p ps0) (Hid: identity_phi p) (Huniq: uniqFdef f),
  selfrefl_phi f (block_intro l0 ps0 cs0 tmn0) p.
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
  (HBinF: blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true)
  (Hin: In p ps0) (Hid: identity_phi p),
  False. 
Proof.
  intros.
  eapply selfrelf_phi_cannot_be_in_reachable_blocks 
    with (b:=block_intro l0 ps0 cs0 tmn0)(p:=p) in Hwf; 
    eauto using identity_phi__selfrefl_phi.
Qed.

(* vid = phi [vid v ... vid v] *)
Inductive assigned_phi (v:value): phinode -> Prop :=
| assigned_phi_intro: forall vid ty vls
    (Hex: exists l0, In (v, l0) vls)
    (Hassign: forall v0 l0, In (v0, l0) vls -> v0 = value_id vid \/ v0 = v),
    assigned_phi v (insn_phi vid ty vls)
.

Lemma assigned_phi_unreachable_vid__selfrefl_phi: forall l0 ps0 cs0 tmn0 f ty 
  vls vid (HBinF: blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true) id0
  (Hin: In (insn_phi id0 ty vls) ps0) (Hreach: reachable f l0)
  (Has: assigned_phi (value_id vid) (insn_phi id0 ty vls)) (Huniq: uniqFdef f)
  (Hnoreachvid : forall l0 : l,
                 In (value_id vid, l0) vls -> ~ reachable f l0),
  selfrefl_phi f (block_intro l0 ps0 cs0 tmn0) (insn_phi id0 ty vls).
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
  (HBinF: blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true) 
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
           Some (block_intro l0 ps0 cs0 tmn0)) as Hlkup.
    solve_lookupBlockViaIDFromFdef.
  assert (isReachableFromEntry f (block_intro l0 ps0 cs0 tmn0)) as Hreach.
    apply Hidreach; auto.
  match goal with
  | H6: wf_phinode _  _ _ |- _ => destruct H6 as [Hwfops Hwflist]
  end.
  caseEq (getEntryBlock f); 
    try solve [intros Hentry; apply wf_fdef__non_entry in Hwf; auto; congruence].
  intros be Hentry.
  destruct (l_dec (getBlockLabel be) 
                  (getBlockLabel (block_intro l0 ps0 cs0 tmn0))) as [Heq | Hneq].
  Case "the current block is entry? no!".
    destruct be; simpl in *; subst.
    assert (HBinF':=Hentry).
    apply entryBlockInFdef in HBinF'.
    eapply blockInFdefB_uniq in HBinF; eauto.
    destruct HBinF as [EQ1 [EQ2 EQ3]]; subst.
    eapply wf_fdef_entryBlock_has_no_phinodes in Hentry; eauto.
    subst; tauto.

  Case "the current block isnt enty. good".
    assert (Hentry_sdom:=Hentry).
    eapply entry_blockStrictDominates_others in Hentry_sdom; eauto 1.
    unfold idDominates.
    fill_ctxhole. 
    caseEq (inscope_of_id f (block_intro l0 ps0 cs0 tmn0)
       (getPhiNodeID (insn_phi id5 typ5 value_l_list))); 
      try solve [intros Hinscope; contradict Hinscope;
                 apply inscope_of_id__total].
    unfold inscope_of_id, init_scope.
    intros ids1 Hinscope.
    destruct_if.
    SCase "id5 in ps. nice".
      remember (Maps.AMap.get l0 (dom_analyze f)) as R.
      destruct R.
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
            destruct (sdom_dec f (getBlockLabel bv) l0) as [Hsdom | Hnsdom].
            SSSSSCase "bv sdoms blv".
              apply fold_left__spec in H2.
              destruct H2 as [_ [H2 _]].
              eapply H2 with (b1:=bv)(l1:=getBlockLabel bv); eauto 1.
                assert (getBlockLabel bv <> l0) as Hneq'.
                  destruct Hsdom; auto.
                apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkbv; auto.
                destruct bv.
                eapply sdom_is_complete in Hsdom; eauto 1.
                  rewrite <- HeqR0 in Hsdom.
                  apply ListSet.set_diff_intro; auto.
                    simpl in *. intro J. destruct J as [J|J]; auto.

                  eapply blockStrictDominates__non_empty_contents in Hentry_sdom; 
                    eauto.
                solve_lookupBlockViaLabelFromFdef'.
                solve_in_list. auto.
            SSSSSCase "bv doesnt sdom blv".
              eapply non_sdom__inv in Hnsdom; eauto 1.
              destruct Hnsdom as [EQ | Hnsdom]; subst.
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
                destruct Hnsdom as [vl1 [al1 [Hwalk Hnotonwalk]]].
                apply DWalk_to_dpath' in Hwalk.
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
                  unfold reachable. fill_ctxhole. destruct be. eauto.
                match goal with
                | H4: arcs_fdef _ _ |- _ => rename H4 into Harc
                end.
                eapply wf_phi_operands__successors in Harc; eauto 1.
                destruct Harc as [vid1 Hinlist].
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
                  unfold domination in Hby0_dom_bly0.
                  rewrite Hentry in Hby0_dom_bly0.
                  destruct be as [le ? ? ?].
                  apply Hby0_dom_bly0 in Hwalk.
                  destruct Hwalk as [Hinpath | EQ]; subst; simpl in *; try congruence.
                  apply H7 in Hinpath. inv Hinpath. congruence.

                SSSSSSSCase "from vid".
                  (* then vid's block must appear in the path, contradict. *)
                  eapply Hvid_spec in Hinlist; eauto 1.
                  destruct Hinlist 
                    as [by0 [bly0 [Hlkbly0 [Hlkby0 Hby0_dom_bly0]]]].
                  simpl in *. uniq_result.
                  lookupBlockViaLabelFromFdef_inv_tac.
                  unfold domination in Hby0_dom_bly0.
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

Lemma eliminate_phi_true_spec: forall S M f b f'
  (Hreach: isReachableFromEntry f b) p 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: phinodeInFdefBlockB p f b = true)
  (Helim: (f', true) = eliminate_phi f p),
  exists v, assigned_phi v p /\ 
    f' = remove_fdef (getPhiNodeID p) (subst_fdef (getPhiNodeID p) v f).
Admitted. (* spec *)

Lemma eliminate_phis_true_spec': forall f b f' S M 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (Hreach: isReachableFromEntry f b) ps
  (HBinF: forall p, In p ps -> phinodeInFdefBlockB p f b = true)
  (Helim: (f', true) = eliminate_phis f ps),
  exists p, In p ps /\ exists v, assigned_phi v p /\ 
    f' = remove_fdef (getPhiNodeID p) (subst_fdef (getPhiNodeID p) v f).
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
      destruct H1 as [p' [Hin [v [H1 H2]]]].
      eauto 6.
Qed.
    
Lemma eliminate_phis_true_spec: forall f f' l0 S M 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (Hreach: reachable f l0) ps cs0 tmn0
  (HBinF: blockInFdefB (block_intro l0 ps cs0 tmn0) f = true)
  (Helim: (f', true) = eliminate_phis f ps),
  exists p, In p ps /\ exists v, assigned_phi v p /\ 
    f' = remove_fdef (getPhiNodeID p) (subst_fdef (getPhiNodeID p) v f).
Proof.
  intros.
  eapply eliminate_phis_true_spec' with (b:=block_intro l0 ps cs0 tmn0); 
    simpl; eauto 1.
  intros.
  bsplit; auto. simpl. solve_in_list.
Qed.

Lemma assigned_phi__wf_value: forall S M p f l0 ps0 cs0 tmn0
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true) 
  (Hin: In p ps0) v (Hassign: assigned_phi v p),
  forall ty, 
    lookupTypViaIDFromFdef f (getPhiNodeID p) = Some ty ->
    wf_value S M f v ty.
Admitted. (* spec *)
