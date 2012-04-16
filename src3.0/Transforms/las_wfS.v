Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import primitives.
Require Import palloca_props.
Require Import mem2reg.
Require Import subst.
Require Import las.

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
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)])
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)),
  WF_PhiInfo
    (update_pinfo pinfo
      (subst_fdef i1 v
        (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))).
Proof.
Admitted.  (* WF prev *)

Lemma find_st_ld__lasinfo: forall l0 ps0 cs0 tmn0 i0 v cs (pinfo:PhiInfo) dones
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo)) 
  (Hwfpi: WF_PhiInfo pinfo)
  s m (HwfF: wf_fdef s m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo))
  (HBinF : blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true),
  exists lasinfo:LASInfo pinfo,
    LAS_lid pinfo lasinfo = i1 /\
    LAS_sid pinfo lasinfo = i0 /\
    LAS_value pinfo lasinfo = v /\
    LAS_block pinfo lasinfo = (block_intro l0 ps0 cs0 tmn0).
Proof.
  intros.
  assert (exists tail, exists lalign, exists salign, 
            las i1 i0 lalign salign v tail (block_intro l0 ps0 cs0 tmn0) pinfo)
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
    (mkLASInfo pinfo i1 i0 lal sal v tail (block_intro l0 ps0 cs0 tmn0) Hlas).
  auto.
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
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)])
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)),
  wf_system 
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (subst_fdef i1 v
           (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) :: Ps2)].
Proof.
  intros.
  apply subst_wfS; auto.
    assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true)
      as HBinF.
      rewrite Heq. simpl. apply InBlocksB_middle.
    assert (wf_fdef [module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)]
              (module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)) 
              (PI_f pinfo) /\ uniqFdef (PI_f pinfo)) as J.
      rewrite Heq in *.
      apply wf_single_system__wf_uniq_fdef; auto.
    destruct J as [HwfF HuniqF].
    eapply find_st_ld__lasinfo in HBinF; eauto.
    destruct HBinF as [lasinfo [J1 [J2 [J3 J4]]]]; subst.
    rewrite <- Heq.
    eapply LAS_value__dominates__LAS_lid; eauto.
Qed.

