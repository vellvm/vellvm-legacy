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
Require Import las.
Require Import die_wfS.

(* This file proves that LAS preserves well-formedness. *)

(* First, vmem2reg pass indeed finds a LAS pair. *)
Lemma find_st_ld__lasinfo: forall l0 ps0 cs0 tmn0 i0 v cs (pinfo:PhiInfo) dones
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo)) 
  (Hwfpi: WF_PhiInfo pinfo)
  s m (HwfF: wf_fdef s m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo))
  (HBinF : blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) (PI_f pinfo) = true),
  exists lasinfo:LASInfo pinfo,
    LAS_lid pinfo lasinfo = i1 /\
    LAS_sid pinfo lasinfo = i0 /\
    LAS_value pinfo lasinfo = v /\
    LAS_block pinfo lasinfo = (l0, stmts_intro ps0 cs0 tmn0).
Proof.
  intros.
  assert (exists tail, exists lalign, exists salign, 
            las i1 i0 lalign salign v tail (l0, stmts_intro ps0 cs0 tmn0) pinfo)
    as Hlas. 
    unfold las.
    apply find_init_stld_inl_spec in Hst.
    destruct Hst as [cs1 [ty1 [al1 Hst]]]; subst.
    apply find_next_stld_inl_spec in Hld.
    destruct Hld as [cs2 [cs3 [tl2 [al2 [Hld J]]]]]; subst.
    exists cs2. exists al2. exists al1.
    split; auto.
    split; auto.
    exists cs1. exists cs3.
      assert (J':=HBinF).
      eapply WF_PhiInfo_spec24 in J'; eauto.
      match goal with
      | H1 : context [?A ++ ?b :: ?C ++ ?d :: ?E] |- _ =>
        rewrite_env ((A ++ b :: C) ++ d :: E) in H1;
        eapply WF_PhiInfo_spec23 in H1; eauto
      end.
      subst. auto.
  destruct Hlas as [tail [lal [sal Hlas]]].
  exists 
    (mkLASInfo pinfo i1 i0 lal sal v tail (l0, stmts_intro ps0 cs0 tmn0) Hlas).
  auto.
Qed.

Lemma las_wf_init: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo)
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
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
  exists lasinfo : LASInfo pinfo,
            LAS_lid pinfo lasinfo = i1 /\
            LAS_sid pinfo lasinfo = i0 /\
            LAS_value pinfo lasinfo = v /\
            LAS_block pinfo lasinfo = (l0, stmts_intro ps0 cs0 tmn0).
Proof.
  intros.
  assert (blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) (PI_f pinfo) = true)
    as HBinF.
    rewrite Heq. simpl. apply InBlocksB_middle.
  assert (wf_fdef [module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)]
          (module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)) 
          (PI_f pinfo) /\ uniqFdef (PI_f pinfo)) as J.
  rewrite Heq in *.
  apply wf_single_system__wf_uniq_fdef; auto.
  destruct J as [HwfF HuniqF].
  eapply find_st_ld__lasinfo in HBinF; eauto 2.
  destruct HBinF as [lasinfo [J1 [J2 [J3 J4]]]]; subst.
  eauto 7.
Qed.

(* After LAS, the substituted definition is removable. *)
Lemma las_diinfo': forall (los : layouts) (nts : namedts) (fh : fheader)
  (pinfo: PhiInfo) (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) 
  (tmn0 : terminator) (bs2 : list block) (Ps1 : list product) (Ps2 : list product)
  (v : value) (cs : cmds) (Hreach: In l0 (PI_rd pinfo)) (i1 : id) 
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfF: wf_fdef  
           [module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2)]
           (module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
           (PI_f pinfo)) 
  (HuniqF: uniqFdef (PI_f pinfo)) (lasinfo : LASInfo pinfo)
  (Heqi1: LAS_lid pinfo lasinfo = i1) (Heqv: LAS_value pinfo lasinfo = v)
  (Heqb: LAS_block pinfo lasinfo = (l0, stmts_intro ps0 cs0 tmn0)),
  exists diinfo:die.DIInfo, 
    die.DI_f diinfo = subst_fdef i1 v (PI_f pinfo) /\ die.DI_id diinfo = i1.
Proof.    
(* 
   To prove this, we need
   1) id0 is pure: 
      this is true, because we run die after laa/las where id0 defines a load
   2) v0 doesnt use id0, See subst_unused_in_fdef in Vminus/motion.v
      this is true, because v0 must dominate id0
*)
  intros. subst.
  assert (J:=HuniqF).
  apply lookup_LAS_lid__load with (lasinfo:=lasinfo) in J; auto.
  apply subst_fdef__diinfo.
    intros.
    uniq_result. simpl. auto.

    intros.
    assert (id_in_reachable_block (PI_f pinfo) (LAS_lid pinfo lasinfo)) 
      as Hreach'.
      intros b0 Hlkup.
      rewrite lookup_LAS_lid__LAS_block in Hlkup; auto.
      inv Hlkup.
      rewrite Heqb. simpl.
      destruct Hwfpi.
      eapply reachablity_analysis__reachable; eauto.
      intro Hin. 
      assert (Hvdom:=HwfF).
      apply LAS_value__dominates__LAS_lid with (lasinfo:=lasinfo) in Hvdom; auto.
      destruct (LAS_value pinfo lasinfo) as [vid|]; simpl in Hin; try tauto.
      destruct Hin as [Hin | Hin]; subst; try tauto.
    assert (Hidom:=Hreach').
    apply Hvdom in Hidom.
    eapply idDominates_acyclic; eauto.
Qed.

Lemma las_diinfo: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) (Hreach: In l0 (PI_rd pinfo))
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
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
  eapply las_wf_init in HwfS; eauto 1.
  destruct HwfS as [HwfF [HuniqF [lasinfo [J1 [J2 [J3 J4]]]]]]; subst.
  eapply las_diinfo'; eauto.
Qed.

(* LAS preserves promotability (WF_PhiInfo). *)
Lemma las_wfPI': forall (fh : fheader) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block)
  (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo) (i1 : id) 
  (HuniqF: uniqFdef (PI_f pinfo)) (lasinfo : LASInfo pinfo)
  (Heqi1: LAS_lid pinfo lasinfo = i1) (Heqv: LAS_value pinfo lasinfo = v)
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)),
  WF_PhiInfo (subst_pinfo i1 v pinfo).
Proof.
  intros. subst.
  eapply subst_wfPI; eauto 2.
    assert (J:=HuniqF).
    apply lookup_LAS_sid__store with (lasinfo:=lasinfo) in J; auto.
    eapply WF_PhiInfo_spec4; eauto; simpl; auto.
Qed.

Lemma las_wfPI: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo)
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
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
  assert (J:=HwfS).
  eapply las_wf_init in J; eauto 1.
  destruct J as [HwfF [HuniqF [lasinfo [J1 [J2 [J3 J4]]]]]]; subst.
  eapply las_wfPI'; eauto.
Qed.

(* LAS preserves well-formedness. *)
Lemma las_wfS': forall (los : layouts) (nts : namedts) (fh : fheader)
  (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) 
  (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo) (i1 : id) 
  (HwfS :
     wf_system 
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
          :: Ps2)]) (lasinfo : LASInfo pinfo)
  (Heqi1: LAS_lid pinfo lasinfo = i1) (Heqv: LAS_value pinfo lasinfo = v)
  (Heqb: LAS_block pinfo lasinfo = (l0, stmts_intro ps0 cs0 tmn0))
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
    rewrite <- Heq.
    eapply LAS_value__dominates__LAS_lid; eauto.

    assert (J:=HuniqF).
    apply lookup_LAS_lid__load with (lasinfo:=lasinfo) in J; auto.
    rewrite <- Heq.
    solve_notin_getArgsIDs.

    rewrite <- Heq. clear - lasinfo HuniqF HwfF.
    intros t0 Htyp.
    assert (lookupTypViaIDFromFdef (PI_f pinfo)
             (LAS_lid pinfo lasinfo) = ret (PI_typ pinfo)) as Htyp'.
      apply lookupTypViaIDFromFdef_intro; auto.
      right.
      exists (LAS_block pinfo lasinfo).
      exists (insn_cmd
               (insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
                 (value_id (PI_id pinfo)) (LAS_lalign pinfo lasinfo))).
      simpl. 
      split; auto.
        clear - lasinfo.
        destruct_lasinfo. 
        apply andb_true_iff.
        split; auto.
          solve_in_list.
    uniq_result.
    clear - lasinfo HwfF.
    destruct_lasinfo. 
    eapply wf_fdef__wf_cmd in LAS_BInF0; eauto using in_middle.
    inv LAS_BInF0. auto.
Qed.

Lemma las_wfS: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) (Hwfpi: WF_PhiInfo pinfo)
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
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
  eapply las_wf_init in Hst; eauto 1.
  destruct Hst as [HwfF [HuniqF [lasinfo [J1 [J2 [J3 J4]]]]]]; subst.
  eapply las_wfS'; eauto.
Qed.

(* LAS + deletion preserves promotability. *)
Lemma las_die_wfPI': forall (los : layouts) (nts : namedts) (fh : fheader)
  (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product)
  (v : value) (cs : cmds) (Hreach:  In l0 (PI_rd pinfo))
  (i1 : id) (lasinfo : LASInfo pinfo)
  (Heqi1: LAS_lid pinfo lasinfo = i1) (Heqv: LAS_value pinfo lasinfo = v)
  (Heqb: LAS_block pinfo lasinfo = (l0, stmts_intro ps0 cs0 tmn0))
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
  assert (Hdiinfo:=HwfF).
  eapply las_diinfo' in Hdiinfo; eauto.
  destruct Hdiinfo as [diinfo [J1 J2]]. rewrite Heq in J1.
  eapply die_wfPI; eauto.
    eapply las_wfPI'; eauto.
    eapply las_wfS'; eauto.
    rewrite <- Heq. apply subst_fdef_PI_f__PI_f_subst_pinfo.
Qed.

Lemma las_die_wfPI: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo: PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) (Hreach:  In l0 (PI_rd pinfo))
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
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
  eapply las_wf_init in Hst; eauto 1.
  destruct Hst as [HwfF [HuniqF [lasinfo [J1 [J2 [J3 J4]]]]]]; subst.
  eapply las_die_wfPI'; eauto.
Qed.

