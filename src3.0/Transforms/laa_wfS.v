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
Require Import laa.

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
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)])
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)),
  WF_PhiInfo
    (update_pinfo pinfo
      (subst_fdef i1 v
        (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))).
Admitted. (* pres wfPI*)

Lemma find_st_ld__laainfo: forall l0 ps0 cs0 tmn0 v cs (pinfo:PhiInfo) dones
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Hwfpi: WF_PhiInfo pinfo)
  s m (HwfF: wf_fdef s m (PI_f pinfo)) (Huniq: uniqFdef (PI_f pinfo))
  (HBinF : blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true),
  v = [! pinfo !] /\
  exists laainfo:LAAInfo pinfo,
    LAA_lid pinfo laainfo = i1 /\
    LAA_block pinfo laainfo = (block_intro l0 ps0 cs0 tmn0).
Proof.
  intros.
  assert (v = [! pinfo !] /\
          exists tail, exists lal, 
            laa i1 lal tail (block_intro l0 ps0 cs0 tmn0) pinfo) as Hlaa. 
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
    exists (mkLAAInfo pinfo i1 lal tail (block_intro l0 ps0 cs0 tmn0) Hlaa).
    auto.
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
  assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true)
    as HBinF.
    rewrite Heq. simpl. apply InBlocksB_middle.
  assert (wf_fdef [module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)]
            (module_intro los nts (Ps1++product_fdef (PI_f pinfo)::Ps2)) 
            (PI_f pinfo) /\ uniqFdef (PI_f pinfo)) as J.
    rewrite Heq in *. subst.
    apply wf_single_system__wf_uniq_fdef; auto.
  destruct J as [HwfF HuniqF].
  eapply find_st_ld__laainfo in HBinF; eauto.
  destruct HBinF as [EQ [laainfo [J1 J2]]]; subst.
  apply subst_wfS; auto.
    simpl. auto.

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

