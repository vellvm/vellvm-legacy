Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import primitives.
Require Import palloca_props.
Require Import vmem2reg.
Require Import subst.
Require Import laa.
Require Import die_wfS.

Lemma find_st_ld__laainfo: forall l0 ps0 cs0 tmn0 v cs (pinfo:PhiInfo) dones
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Hwfpi: WF_PhiInfo pinfo)
  s m (HwfF: wf_fdef s m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo))
  (HBinF : blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) (PI_f pinfo) = true),
  v = [! pinfo !] /\
  exists laainfo:LAAInfo pinfo,
    LAA_lid pinfo laainfo = i1 /\
    LAA_block pinfo laainfo = (l0, stmts_intro ps0 cs0 tmn0).
Proof.
  intros.
  assert (v = [! pinfo !] /\
          exists tail, exists lal, 
            laa i1 lal tail (l0, stmts_intro ps0 cs0 tmn0) pinfo) as Hlaa. 
    unfold laa.
    apply find_init_stld_inr_spec in Hst.
    destruct Hst as [cs1 [ty [num [al [EQ Hst]]]]]; subst.
    apply find_next_stld_inl_spec in Hld.
    destruct Hld as [cs2 [cs3 [ty' [al' [Hld J]]]]]; subst.
    assert (J':=HBinF).
    eapply WF_PhiInfo_spec1' in J'; eauto. inv J'.
    assert (J':=HBinF).
    match goal with
    | H1 : context [?A ++ ?b :: ?C ++ ?d :: ?E] |- _ =>
      rewrite_env ((A ++ b :: C) ++ d :: E) in H1;
      eapply WF_PhiInfo_spec23 in H1; eauto
    end.
    subst. 
    split; auto.
      exists cs2. exists al'.
      split; auto.
      split; auto.
      exists cs1. exists cs3. auto.
  destruct Hlaa as [EQ [tail [lal Hlaa]]]; subst.
  split; auto.
    exists (mkLAAInfo pinfo i1 lal tail (l0, stmts_intro ps0 cs0 tmn0) Hlaa).
    auto.
Qed.

Lemma laa_wf_init: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product)
  (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo)
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (HwfS :
     wf_system 
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
          :: Ps2)])
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)),
  wf_fdef  [module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2)]
           (module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
           (PI_f pinfo) /\
  uniqFdef (PI_f pinfo) /\
  v = [! pinfo !] /\
  exists laainfo:LAAInfo pinfo,
    LAA_lid pinfo laainfo = i1 /\
    LAA_block pinfo laainfo = (l0, stmts_intro ps0 cs0 tmn0).
Proof.
  intros.
  assert (blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) (PI_f pinfo) = true)
    as HBinF.
    rewrite Heq. simpl. apply InBlocksB_middle.
  assert (wf_fdef [module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)]
            (module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)) 
            (PI_f pinfo) /\ uniqFdef (PI_f pinfo)) as J.
    rewrite Heq in *. subst.
    apply wf_single_system__wf_uniq_fdef; auto.
  destruct J as [HwfF HuniqF].
  eapply find_st_ld__laainfo in HBinF; eauto.
Qed.

Lemma laa_diinfo': forall (fh : fheader) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (v : value) (cs : cmds) (i1 : id) 
  (HuniqF: uniqFdef (PI_f pinfo)) (Heqv: v = [! pinfo !]) (laainfo:LAAInfo pinfo)
  (Heqi1: LAA_lid pinfo laainfo = i1) 
  (Heqb: LAA_block pinfo laainfo = (l0, stmts_intro ps0 cs0 tmn0))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Hwfpi: WF_PhiInfo pinfo),
  exists diinfo:die.DIInfo, 
    die.DI_f diinfo = subst_fdef i1 v (PI_f pinfo) /\ die.DI_id diinfo = i1.
Proof.    
  intros. subst.
  assert (J:=HuniqF).
  apply lookup_LAA_lid__load with (laainfo:=laainfo) in J; auto.
  apply subst_fdef__diinfo.
    intros.
    uniq_result. simpl. auto.

    intros. simpl. tauto.
Qed.

Lemma laa_diinfo: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product)
  (v : value) (cs : cmds)
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
          :: Ps2)]),
  exists diinfo:die.DIInfo, 
    die.DI_f diinfo = subst_fdef i1 v (PI_f pinfo) /\ die.DI_id diinfo = i1.
Proof.    
  intros.
  eapply laa_wf_init in HwfS; eauto 1.
  destruct HwfS as [HwfF [HuniqF [EQ [laainfo [J1 J2]]]]]; subst.
  eapply laa_diinfo'; eauto.
Qed.

Lemma laa_wfPI': forall (fh : fheader) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo)
  (HuniqF: uniqFdef (PI_f pinfo)) (Heqv: v = [! pinfo !]) (i1 : id) 
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)),
  WF_PhiInfo (subst_pinfo i1 v pinfo).
Proof.
  intros. subst.
  eapply subst_wfPI; eauto 2.
Qed.

Lemma laa_wfPI: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product)
  (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo)
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (HwfS :
     wf_system 
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
          :: Ps2)])
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)),
  WF_PhiInfo (subst_pinfo i1 v pinfo).
Proof.
  intros.
  eapply laa_wf_init in Hst; eauto 1.
  destruct Hst as [HwfF [HuniqF [EQ [laainfo [J1 J2]]]]]; subst.
  eapply laa_wfPI'; eauto.
Qed.

Lemma laa_wfS': forall (los : layouts) (nts : namedts) (fh : fheader) 
  (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product)
  (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo)
  (i1 : id) (Heqv: v = [! pinfo !]) (laainfo:LAAInfo pinfo)
  (Heqi1: LAA_lid pinfo laainfo = i1) 
  (Heqb: LAA_block pinfo laainfo = (l0, stmts_intro ps0 cs0 tmn0))
  (HwfS :
     wf_system 
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
          :: Ps2)])
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)),
  wf_system 
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (subst_fdef i1 v
           (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))) :: Ps2)].
Proof.
  intros. subst.
  assert (J:=HwfS). apply wf_single_system__wf_uniq_fdef in J; auto.
  destruct J as [HwfF HuniqF]. rewrite <- Heq in HuniqF, HwfF.
  apply subst_wfS; auto.
    simpl. auto.

    assert (J:=HuniqF).
    apply lookup_LAA_lid__load with (laainfo:=laainfo) in J; auto.
    rewrite <- Heq.
    solve_notin_getArgsIDs.

    rewrite <- Heq. clear - laainfo HuniqF HwfF Hwfpi.
    intros t0 Htyp.
    assert (lookupTypViaIDFromFdef (PI_f pinfo)
             (LAA_lid pinfo laainfo) = ret (PI_typ pinfo)) as Htyp'.
      apply lookupTypViaIDFromFdef_intro; auto.
      right.
      exists (LAA_block pinfo laainfo).
      exists (insn_cmd
               (insn_load (LAA_lid pinfo laainfo) (PI_typ pinfo)
                 (value_id (PI_id pinfo)) (LAA_lalign pinfo laainfo))).
      simpl. 
      split; auto.
        clear - laainfo.
        destruct_laainfo. 
        apply andb_true_iff.
        split; auto.
          solve_in_list.
    uniq_result.
    eapply WF_PhiInfo_spec21 in Hwfpi; eauto.
    constructor; auto.
      constructor; auto.
Qed.

Lemma laa_wfS: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product)
  (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo)
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (HwfS :
     wf_system 
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
          :: Ps2)])
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)),
  wf_system 
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (subst_fdef i1 v
           (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))) :: Ps2)].
Proof.
  intros.
  eapply laa_wf_init in Hst; eauto 1.
  destruct Hst as [HwfF [HuniqF [EQ [laainfo [J1 J2]]]]]; subst.
  eapply laa_wfS'; eauto.
Qed.

Lemma laa_die_wfPI': forall (los : layouts) (nts : namedts) (fh : fheader)
  (pinfo : PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (v : value)
  (cs : cmds) (i1 : id) (Heqv: v = [! pinfo !]) (laainfo:LAAInfo pinfo)
  (Heqi1: LAA_lid pinfo laainfo = i1) 
  (Heqb: LAA_block pinfo laainfo = (l0, stmts_intro ps0 cs0 tmn0))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
          :: Ps2)]),
  WF_PhiInfo (update_pinfo (subst_pinfo i1 v pinfo)
    (fdef_intro fh
      (List.map (remove_block i1)
        (List.map (subst_block i1 v)
          (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))))).
Proof.
  intros.
  assert ((fdef_intro fh
           (List.map (remove_block i1)
             (List.map (subst_block i1 v)
               (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)))) =
          remove_fdef i1
            (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))))
    as J.
    simpl. auto.
  rewrite J.
  assert (J':=HwfS). apply wf_single_system__wf_uniq_fdef in J'; auto.
  destruct J' as [HwfF HuniqF]. rewrite <- Heq in HuniqF, HwfF.
  assert (Hdiinfo:=HuniqF).
  eapply laa_diinfo' in Hdiinfo; eauto.
  destruct Hdiinfo as [diinfo [J1 J2]]. rewrite Heq in J1.
  eapply die_wfPI; eauto.
    eapply laa_wfPI'; eauto.
    eapply laa_wfS'; eauto.
    rewrite <- Heq. apply subst_fdef_PI_f__PI_f_subst_pinfo.
Qed.

Lemma laa_die_wfPI: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (v : value)
  (cs : cmds)
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
          :: Ps2)]),
  WF_PhiInfo (update_pinfo (subst_pinfo i1 v pinfo)
    (fdef_intro fh
      (List.map (remove_block i1)
        (List.map (subst_block i1 v)
          (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))))).
Proof.
  intros.
  eapply laa_wf_init in Hst; eauto 1.
  destruct Hst as [HwfF [HuniqF [EQ [laainfo [J1 J2]]]]]; subst.
  eapply laa_die_wfPI'; eauto.
Qed.
