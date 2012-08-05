Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import primitives.
Require Import palloca_props.
Require Import vmem2reg.
Require Import sas.
Require Import filter.

Lemma find_st_ld__sasinfo: forall l0 ps0 cs0 tmn0 i0 v cs (pinfo:PhiInfo) dones
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones) v0
  (i1 : id) (Hld : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (Hwfpi: WF_PhiInfo pinfo)
  s m (HwfF: wf_fdef s m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo))
  (HBinF : blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) (PI_f pinfo) = true),
  exists sasinfo:SASInfo pinfo,
    SAS_sid1 pinfo sasinfo = i0 /\
    SAS_sid2 pinfo sasinfo = i1 /\
    SAS_value1 pinfo sasinfo = v /\
    SAS_value2 pinfo sasinfo = v0 /\
    SAS_block pinfo sasinfo = (l0, stmts_intro ps0 cs0 tmn0).
Proof.
  intros.
  assert (exists tail, exists sal1, exists sal2, 
            sas i0 i1 sal1 sal2 v v0 tail (l0, stmts_intro ps0 cs0 tmn0) pinfo)
    as Hsas. 
    unfold sas.
    apply find_init_stld_inl_spec in Hst.
    destruct Hst as [cs1 [ty1 [al1 Hst]]]; subst.
    apply find_next_stld_inr_spec in Hld.
    destruct Hld as [cs2 [cs3 [ty2 [al2 [Hld J]]]]]; subst.
    exists cs2. exists al1. exists al2.
    split; auto.
    split; auto.
    exists cs1. exists cs3. 
      assert (J':=HBinF).
      eapply WF_PhiInfo_spec24 in J'; eauto.
      match goal with
      | H1 : context [?A ++ ?b :: ?C ++ ?d :: ?E] |- _ =>
        rewrite_env ((A ++ b :: C) ++ d :: E) in H1;
        eapply WF_PhiInfo_spec24 in H1; eauto
      end.
      subst. auto.
  destruct Hsas as [tail [sal1 [sal2 Hsas]]].
  exists (mkSASInfo pinfo i0 i1 sal1 sal2 v v0 tail 
           (l0, stmts_intro ps0 cs0 tmn0) Hsas).
  auto.
Qed.

Lemma sas_wf_init: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds)
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system 
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
          :: Ps2)]),
  wf_fdef  [module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2)]
           (module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
           (PI_f pinfo) /\
  uniqFdef (PI_f pinfo) /\
  exists sasinfo : SASInfo pinfo,
            SAS_sid1 pinfo sasinfo = i0 /\
            SAS_sid2 pinfo sasinfo = i1 /\
            SAS_value1 pinfo sasinfo = v /\
            SAS_value2 pinfo sasinfo = v0 /\
            SAS_block pinfo sasinfo = (l0, stmts_intro ps0 cs0 tmn0).
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
  eapply find_st_ld__sasinfo in HBinF; eauto.
Qed.

Lemma PI_f_doesnt_use_SAS_sid1: forall S M pinfo sasinfo
  (HwfF: wf_fdef S M (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo)),
  used_in_fdef (SAS_sid1 pinfo sasinfo) (PI_f pinfo) = false.
Proof.
  intros.
  apply fdef_doesnt_use_store in HwfF; auto.
  unfold fdef_doesnt_use_removed in HwfF.
  apply lookup_SAS_lid1__cmd with (sasinfo:=sasinfo) in Huniq.
  apply lookupInsnViaIDFromFdef__insnInFdefBlockB in Huniq.
  apply HwfF in Huniq; auto.
Qed.

Lemma sas_wfS: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds)
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system 
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
          :: Ps2)]),
  wf_system 
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
           (List.map (remove_block i0)
             (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))) :: Ps2)].
Proof.
  intros.
  assert (J:=HwfS).
  eapply filter_wfS with (check:=undead_insn i0) in HwfS; eauto 1.
    rewrite <- remove_fdef_is_a_filter in HwfS; auto.

    eapply sas_wf_init in J; eauto.
    destruct J as [HwfF [Huniq [sasinfo [J1 [J2 [J3 [J4 J5]]]]]]]; subst.
    eapply fdef_doesnt_use_dead_insn; eauto 1.
    rewrite <- Heq.
    eapply PI_f_doesnt_use_SAS_sid1; eauto.
Qed.

Lemma sas_wfPI: forall (los : layouts) (nts : namedts) (fh : fheader)
  (dones : list id) (pinfo : PhiInfo)
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds)
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
  (Hwfpi: WF_PhiInfo pinfo)
  (HwfS :
     wf_system 
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2))
          :: Ps2)]),
  WF_PhiInfo
    (update_pinfo pinfo
      (fdef_intro fh
        (List.map (remove_block i0)
           (bs1 ++ (l0, stmts_intro ps0 cs0 tmn0) :: bs2)))).
Proof.
  intros.
  assert (J:=HwfS).
  eapply filter_wfPI with (check:=undead_insn i0) in HwfS; eauto.
    rewrite <- remove_fdef_is_a_filter in HwfS; auto.

    eapply sas_wf_init in J; eauto.
    destruct J as [HwfF [Huniq [sasinfo [J1 [J2 [J3 [J4 J5]]]]]]]; subst.
    intros c Hlkup Hdead.
    apply undead_insn_false_inv in Hdead.
    simpl in Hdead.
    rewrite <- Hdead in Hlkup.
    rewrite <- Heq in Hlkup.
    apply lookup_SAS_lid1__cmd with (sasinfo:=sasinfo) in Huniq; auto.
    uniq_result. simpl. auto.
Qed.
