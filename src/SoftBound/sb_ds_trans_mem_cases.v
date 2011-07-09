Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import ssa_def.
Require Import ssa_lib.
Require Import ssa_dynamic.
Require Import trace.
Require Import Memory.
Require Import genericvalues.
Require Import alist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import sb_ds_def.
Require Import sb_ds_trans.
Require Import sb_msim.
Require Import sb_ds_gv_inject.
Require Import sb_ds_sim.
Require Import sb_ds_trans_axioms.
Require Import sb_ds_trans_lib.
Require Import ssa_wf.
Require Import ssa_props.

Import SB_ds_pass.

Lemma SBpass_is_correct__dsMalloc : forall (mi : meminj) (mgb : Values.block)
  (St : LLVMopsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : GVMap) (rm : AssocList SBopsem.metadata)
  (gl : GVMap) (fs : GVMap) (id0 : atom) (t : typ) (v : value) (align0 : align)
  (EC : list SBopsem.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (MM : SBopsem.mmetadata) (als : list mblock) 
  (Hsim : sbState_simulates_State mi mgb
           {|
           SBopsem.CurSystem := S;
           SBopsem.CurTargetData := TD;
           SBopsem.CurProducts := Ps;
           SBopsem.ECS := {|
                          SBopsem.CurFunction := F;
                          SBopsem.CurBB := B;
                          SBopsem.CurCmds := insn_malloc id0 t v align0 :: cs;
                          SBopsem.Terminator := tmn;
                          SBopsem.Locals := lc;
                          SBopsem.Rmap := rm;
                          SBopsem.Allocas := als |} :: EC;
           SBopsem.Globals := gl;
           SBopsem.FunTable := fs;
           SBopsem.Mem := Mem;
           SBopsem.Mmap := MM |} St)
  (gn : GenericValue) (Mem' : mem) (tsz : sz) (mb : mblock) (lc' : GVMap)
  (rm' : SBopsem.rmetadata) (n : Z) (H : getTypeAllocSize TD t = ret tsz)
  (H0 : getOperandValue TD v lc gl = ret gn) 
  (H1 : malloc TD Mem tsz gn align0 = ret (Mem', mb))
  (H2 : GV2int TD Size.ThirtyTwo gn = ret n)
  (H3 : SBopsem.prop_reg_metadata lc rm id0 (blk2GV TD mb)
         {|
         SBopsem.md_base := SBopsem.base2GV TD mb;
         SBopsem.md_bound := SBopsem.bound2GV TD mb tsz n |} = 
       (lc', rm')),
  exists St' : LLVMopsem.State,
     exists mi' : MoreMem.meminj,
       LLVMopsem.dsop_star St St' trace_nil /\
       sbState_simulates_State mi' mgb
         {|
         SBopsem.CurSystem := S;
         SBopsem.CurTargetData := TD;
         SBopsem.CurProducts := Ps;
         SBopsem.ECS := {|
                        SBopsem.CurFunction := F;
                        SBopsem.CurBB := B;
                        SBopsem.CurCmds := cs;
                        SBopsem.Terminator := tmn;
                        SBopsem.Locals := lc';
                        SBopsem.Rmap := rm';
                        SBopsem.Allocas := als |} :: EC;
         SBopsem.Globals := gl;
         SBopsem.FunTable := fs;
         SBopsem.Mem := Mem';
         SBopsem.Mmap := MM |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd.
  remember (lookupAL (id * id) rm2 id0) as R1.
  destruct R1 as [[bid eid]|]; try solve [inversion Htcmd].
  remember (mk_tmp ex_ids3) as R9.
  destruct R9 as [ntmp ex_ids6'].
  remember (mk_tmp ex_ids6') as R2.
  destruct R2 as [tmp ex_ids6].
  inv Htcmd.
  invert_prop_reg_metadata.
  assert (Hmalloc:=H1).
  apply mem_simulation__malloc with (MM:=MM)(mgb:=mgb)(Mem2:=M2)(mi:=mi) in H1;
    auto.
  destruct H1 as [mi' [Mem2' [mb' [H11 [H16 [H12 [H13 [H14 H15]]]]]]]].

  eapply simulation__getOperandValue with (mi:=mi)(Mem2:=M2) in H0; eauto.
  destruct H0 as [gn' [H00 H01]].
  assert (GV2int (los, nts) Size.ThirtyTwo gn = 
    GV2int (los, nts) Size.ThirtyTwo gn') as Heqgn.
    eapply simulation__eq__GV2int; eauto.

  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
                (updateAddAL _ 
                  (updateAddAL _ 
                    (updateAddAL _ 
                      (updateAddAL _ 
                        (updateAddAL _ lc2 ntmp gn') 
                        id0 (blk2GV (los, nts) mb'))
                      tmp (SBopsem.bound2GV (los, nts) mb' tsz n))
                    bid (SBopsem.base2GV (los, nts) mb'))
                  eid (SBopsem.bound2GV (los, nts) mb' tsz n))
             als2):: 
            ECs2) gl2 fs2 Mem2').
  exists mi'.

  assert (In id0 (getFdefLocs (fdef_intro fh1 bs1))) as Hin. 
    eauto using getCmdID_in_getFdefLocs.
  assert (Hspec := Hgenmeta).
  apply gen_metadata_fdef_spec in Hspec; auto.
  destruct Hspec as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].

  assert (id_fresh_in_value v ntmp) as Hfresh_ctmp.
    assert (Hwfc := HBinF).
    destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
    eapply wf_system__wf_cmd with (c:=insn_malloc id0 t v align0) in Hwfc; eauto.
      inv Hwfc. 
      eapply wf_value_id__in_getFdefLocs in H18; auto.
        eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.
      apply in_or_app. right. simpl. auto. 

  assert (ntmp <> id0) as Hntmp_neq_id0.
    apply tmp_is_fresh2 with (i0:=id0)(d:=getFdefLocs (fdef_intro fh1 bs1)) 
      (ex_ids1:=ex_ids) in HeqR9; auto.
  assert (bid <> ntmp /\ eid <> ntmp) as Hntmp'.
    eapply tmp_is_fresh3 with (bid:=bid)(eid:=eid)(ex_ids1:=ex_ids) in HeqR9; 
      eauto.
  destruct Hntmp' as [Hntmpb Hntmpe].
  assert (tmp <> ntmp) as Hneq''.
    clear - HeqR2 HeqR9.
    unfold mk_tmp in *.
    destruct (atom_fresh_for_list ex_ids3).
    destruct (atom_fresh_for_list ex_ids6').
    inv HeqR9. inv HeqR2. 
    simpl in n0. intro J. subst. auto.
 
  assert (incl ex_ids ex_ids6') as Hinc'.
    eapply mk_tmp_inc in HeqR9; eauto.
  assert (incl ex_ids ex_ids5) as Hinc''.
    eapply mk_tmp_inc in HeqR9; eauto.
    eapply mk_tmp_inc in HeqR2; eauto.
 
  simpl.
  split.
  SCase "opsem".
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
        LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
             (insn_malloc id0 t v align0 ::
              insn_gep tmp false t (value_id id0) 
                (Cons_list_value (value_id ntmp) Nil_list_value):: 
              insn_cast bid castop_bitcast (typ_pointer t)(value_id id0) p8 :: 
              insn_cast eid castop_bitcast (typ_pointer t)(value_id tmp) p8 :: 
              cs2' ++ cs23)
             tmn2 
             (updateAddAL GenericValue lc2 ntmp gn')
             als2):: 
            ECs2) gl2 fs2 M2); auto.
      eapply dsCast; eauto.        
        unfold CAST. simpl. rewrite H00. unfold i32, mbitcast. auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
        LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
             (insn_gep tmp false t (value_id id0) 
                (Cons_list_value (value_id ntmp) Nil_list_value):: 
              insn_cast bid castop_bitcast (typ_pointer t)(value_id id0) p8 :: 
              insn_cast eid castop_bitcast (typ_pointer t)(value_id tmp) p8 :: 
              cs2' ++ cs23)
             tmn2 
             (updateAddAL _
                (updateAddAL _ lc2 ntmp gn') 
                id0 (blk2GV (los, nts) mb'))
             als2):: 
            ECs2) gl2 fs2 Mem2'); auto.
      unfold malloc in H11.
      rewrite Heqgn in H11; eauto.
      eapply LLVMopsem.dsMalloc; eauto.
        rewrite <- getOperandValue_eq_fresh_id; auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
        LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
             (insn_cast bid castop_bitcast (typ_pointer t)(value_id id0) p8 :: 
              insn_cast eid castop_bitcast (typ_pointer t)(value_id tmp) p8 :: 
              cs2' ++ cs23)
             tmn2 
             (updateAddAL _
               (updateAddAL _ 
                 (updateAddAL _ lc2 ntmp gn') id0 (blk2GV (los,nts) mb'))
               tmp (SBopsem.bound2GV (los,nts) mb' tsz n))
             als2):: 
            ECs2) gl2 fs2 Mem2'); auto.
      apply LLVMopsem.dsGEP with (mp:=blk2GV (los,nts) mb')(vidxs:=[gn']); auto.
        simpl.
        rewrite lookupAL_updateAddAL_eq; auto.

        assert(getOperandValue (los,nts) (value_id ntmp)
          (updateAddAL _ (updateAddAL _ lc2 ntmp gn') 
             id0 (blk2GV (los,nts) mb')) gl2 = Some gn') as EQ'.
          rewrite <- getOperandValue_eq_fresh_id; auto.
          simpl. apply lookupAL_updateAddAL_eq; auto.
        
        simpl. simpl in EQ'.
        rewrite EQ'. clear EQ'.
        auto.

        unfold SBopsem.bound2GV, GEP, blk2GV, GV2ptr, ptr2GV, val2GV.
        simpl.
        rewrite <- Heqgn. rewrite H2.
        unfold Constant.typ2utyp.
        assert (exists ut, 
          Constant.typ2utyp_aux (Constant.subst_nts_by_nts nts nts) 
            (typ_array 0%nat t) = Some (typ_array 0%nat ut) /\
          getTypeAllocSize (los, nts) ut = getTypeAllocSize (los, nts) t) as EQ1.
          destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
          eapply wf_system__wf_cmd with (c:=insn_malloc id0 t v align0) in HBinF;
            eauto.
            inv HBinF. inv H22.
            simpl. destruct H0 as [J3 J4].
            unfold Constant.typ2utyp in J3.
            rewrite J3. simpl. eauto.

            apply in_or_app. simpl. auto.
        destruct EQ1 as [ut [EQ1 EQ2]].
        rewrite EQ1. simpl.
        rewrite EQ2. rewrite H. simpl.
        rewrite Int.add_commut.
        rewrite Int.add_zero. auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
        LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
             (insn_cast eid castop_bitcast (typ_pointer t)(value_id tmp) p8 :: 
              cs2' ++ cs23)
             tmn2 
             (updateAddAL _
               (updateAddAL _
                 (updateAddAL _ 
                   (updateAddAL _ lc2 ntmp gn') id0 (blk2GV (los,nts) mb'))
                 tmp (SBopsem.bound2GV (los,nts) mb' tsz n))
               bid (SBopsem.base2GV (los,nts) mb'))               
             als2):: 
            ECs2) gl2 fs2 Mem2'); auto.
      apply LLVMopsem.dsCast; auto.
        unfold CAST. simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.

          clear - HeqR2 Hinc1 Hinc' Hin.
          eapply tmp_is_fresh2 with (d:=getFdefLocs (fdef_intro fh1 bs1)); eauto.
 
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
       (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
                (updateAddAL _ 
                  (updateAddAL _ 
                    (updateAddAL _ 
                      (updateAddAL _
                        (updateAddAL _ lc2 ntmp gn') id0 (blk2GV (los, nts) mb'))
                      tmp (SBopsem.bound2GV (los, nts) mb' tsz n))
                    bid (SBopsem.base2GV (los, nts) mb'))                    
                  eid (SBopsem.bound2GV (los, nts) mb' tsz n))
             als2):: 
            ECs2) gl2 fs2 Mem2')); auto.
      apply LLVMopsem.dsCast; auto.
        unfold CAST. simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.

          clear - HeqR2 Hinc3 Hinc' HeqR1.
          eapply tmp_is_fresh3 with (tmp:=tmp) in HeqR1; eauto.
          destruct HeqR1; auto.

  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split.
  split.
  split; auto.          
  split; auto.          
  split; auto.          
  split; auto.          
  split; auto.          
  split; auto.          
  split; auto.          
  split; auto.          
  split; eauto using inject_incr__preserves__als_simulation.
  split; auto.
  split.
    eapply cmds_at_block_tail_next; eauto.
  split.
    destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
    exists l2. exists ps2. exists (cs21 ++
                  (insn_cast ntmp castop_bitcast i32 v i32 ::
                    insn_malloc id0 t v align0
                    :: insn_gep tmp false t (value_id id0)
                         (Cons_list_value (value_id ntmp) Nil_list_value)
                       :: insn_cast bid castop_bitcast 
                            (typ_pointer t) (value_id id0) p8
                          :: insn_cast eid castop_bitcast 
                               (typ_pointer t) (value_id tmp) p8 :: nil)).
    simpl_env. auto.
  exists ex_ids. exists rm2.
  exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
  split.
  SCase "rsim".
    eapply reg_simulation__updateAddAL_md; eauto.
      eapply reg_simulation__updateAddAL_tmp with (ex_ids5:=ex_ids5)
        (ex_ids3':=ex_ids6'); eauto.
      eapply reg_simulation__updateAddAL_lc; eauto.
      eapply reg_simulation__updateAddAL_tmp with (ex_ids5:=ex_ids6')
        (ex_ids3':=ex_ids3); eauto.
        eapply inject_incr__preserves__reg_simulation; eauto.

      unfold blk2GV, ptr2GV, val2GV.
      simpl. eauto.

      unfold SBopsem.base2GV, blk2GV, ptr2GV, val2GV.
      simpl. clear - H14. eauto.

      unfold SBopsem.bound2GV, blk2GV, ptr2GV, val2GV.
      simpl. clear - H14.
        apply gv_inject_cons; eauto.
          eapply MoreMem.val_inject_ptr; eauto.
            rewrite Int.add_zero. auto.

    split; auto.
      clear - HsimECs H13. 
      eapply inject_incr__preserves__sbECs_simulate_ECs_tail; eauto.
    repeat(split; eauto using inject_incr__preserves__fable_simulation).
Qed.

Lemma SBpass_is_correct__dsAlloca : forall 
  (mi : MoreMem.meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : GVMap)
  (rm : AssocList metadata) (gl : GVMap) (fs : GVMap) (id0 : atom) (t : typ)  
  (v : value) (align0 : align) (EC : list ExecutionContext) (cs : list cmd)
  (tmn : terminator) (Mem0 : mem) (MM : mmetadata) (als : list mblock)
  (Hsim : sbState_simulates_State mi mgb
           {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_alloca id0 t v align0 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Globals := gl;
           FunTable := fs;
           Mem := Mem0;
           Mmap := MM |} St)
  (gn : GenericValue) (Mem' : mem) (tsz : sz) (mb : mblock) (lc' : GVMap)
  (rm' : rmetadata) (n : Z) (H : getTypeAllocSize TD t = ret tsz)
  (H0 : getOperandValue TD v lc gl = ret gn) 
  (H1 : malloc TD Mem0 tsz gn align0 = ret (Mem', mb))
  (H2 : GV2int TD Size.ThirtyTwo gn = ret n)
  (H3 : prop_reg_metadata lc rm id0 (blk2GV TD mb)
         {| md_base := base2GV TD mb; md_bound := bound2GV TD mb tsz n |} =
       (lc', rm')),
  exists St' : LLVMopsem.State,
     exists mi' : MoreMem.meminj,
       LLVMopsem.dsop_star St St' trace_nil /\
       sbState_simulates_State mi' mgb
         {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := mb :: als |} :: EC;
         Globals := gl;
         FunTable := fs;
         Mem := Mem';
         Mmap := MM |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd.
  remember (lookupAL (id * id) rm2 id0) as R1.
  destruct R1 as [[bid eid]|]; try solve [inversion Htcmd].
  remember (mk_tmp ex_ids3) as R9.
  destruct R9 as [ntmp ex_ids6'].
  remember (mk_tmp ex_ids6') as R2.
  destruct R2 as [tmp ex_ids6].
  inv Htcmd.
  invert_prop_reg_metadata.
  assert (Hmalloc:=H1).
  apply mem_simulation__malloc with (MM:=MM)(mgb:=mgb)(Mem2:=M2)(mi:=mi) in H1;
    auto.
  destruct H1 as [mi' [Mem2' [mb' [H11 [H16 [H12 [H13 [H14 H15]]]]]]]].

  eapply simulation__getOperandValue with (mi:=mi)(Mem2:=M2) in H0; eauto.
  destruct H0 as [gn' [H00 H01]].
  assert (GV2int (los, nts) Size.ThirtyTwo gn = 
    GV2int (los, nts) Size.ThirtyTwo gn') as Heqgn.
    eapply simulation__eq__GV2int; eauto.

  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
                (updateAddAL _ 
                  (updateAddAL _ 
                    (updateAddAL _ 
                      (updateAddAL _ 
                        (updateAddAL _ lc2 ntmp gn') 
                        id0 (blk2GV (los, nts) mb'))
                      tmp (SBopsem.bound2GV (los, nts) mb' tsz n))
                    bid (SBopsem.base2GV (los, nts) mb'))
                  eid (SBopsem.bound2GV (los, nts) mb' tsz n))
             (mb'::als2)):: 
            ECs2) gl2 fs2 Mem2').
  exists mi'.

  assert (In id0 (getFdefLocs (fdef_intro fh1 bs1))) as Hin. 
    eauto using getCmdID_in_getFdefLocs.
  assert (Hspec := Hgenmeta).
  apply gen_metadata_fdef_spec in Hspec; auto.
  destruct Hspec as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].

  assert (id_fresh_in_value v ntmp) as Hfresh_ctmp.
    assert (Hwfc := HBinF).
    destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
    eapply wf_system__wf_cmd with (c:=insn_alloca id0 t v align0) in Hwfc; eauto.
      inv Hwfc. 
      eapply wf_value_id__in_getFdefLocs in H18; auto.
        eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.
      apply in_or_app. right. simpl. auto. 

  assert (ntmp <> id0) as Hntmp_neq_id0.
    apply tmp_is_fresh2 with (i0:=id0)(d:=getFdefLocs (fdef_intro fh1 bs1)) 
      (ex_ids1:=ex_ids) in HeqR9; auto.
  assert (bid <> ntmp /\ eid <> ntmp) as Hntmp'.
    eapply tmp_is_fresh3 with (bid:=bid)(eid:=eid)(ex_ids1:=ex_ids) in HeqR9; 
      eauto.
  destruct Hntmp' as [Hntmpb Hntmpe].
  assert (tmp <> ntmp) as Hneq''.
    clear - HeqR2 HeqR9.
    unfold mk_tmp in *.
    destruct (atom_fresh_for_list ex_ids3).
    destruct (atom_fresh_for_list ex_ids6').
    inv HeqR9. inv HeqR2. 
    simpl in n0. intro J. subst. auto.
 
  assert (incl ex_ids ex_ids6') as Hinc'.
    eapply mk_tmp_inc in HeqR9; eauto.
  assert (incl ex_ids ex_ids5) as Hinc''.
    eapply mk_tmp_inc in HeqR9; eauto.
    eapply mk_tmp_inc in HeqR2; eauto.

  split.
  SCase "opsem".
    simpl.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
        LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
             (insn_alloca id0 t v align0 ::
              insn_gep tmp false t (value_id id0) 
                (Cons_list_value (value_id ntmp) Nil_list_value):: 
              insn_cast bid castop_bitcast (typ_pointer t)(value_id id0) p8 :: 
              insn_cast eid castop_bitcast (typ_pointer t)(value_id tmp) p8 :: 
              cs2' ++ cs23)
             tmn2 
             (updateAddAL GenericValue lc2 ntmp gn')
             als2):: 
            ECs2) gl2 fs2 M2); auto.
      eapply dsCast; eauto.        
        unfold CAST. simpl. rewrite H00. unfold i32, mbitcast. auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
        LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
             (insn_gep tmp false t (value_id id0) 
                (Cons_list_value (value_id ntmp) Nil_list_value):: 
              insn_cast bid castop_bitcast (typ_pointer t)(value_id id0) p8 :: 
              insn_cast eid castop_bitcast (typ_pointer t)(value_id tmp) p8 :: 
              cs2' ++ cs23)
             tmn2 
             (updateAddAL _
                (updateAddAL _ lc2 ntmp gn') 
                id0 (blk2GV (los, nts) mb'))
             (mb'::als2)):: 
            ECs2) gl2 fs2 Mem2'); auto.
      unfold malloc in H11.
      rewrite Heqgn in H11; eauto.
      eapply LLVMopsem.dsAlloca; eauto.
        rewrite <- getOperandValue_eq_fresh_id; auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
        LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
             (insn_cast bid castop_bitcast (typ_pointer t)(value_id id0) p8 :: 
              insn_cast eid castop_bitcast (typ_pointer t)(value_id tmp) p8 :: 
              cs2' ++ cs23)
             tmn2 
             (updateAddAL _
               (updateAddAL _ 
                 (updateAddAL _ lc2 ntmp gn') id0 (blk2GV (los,nts) mb'))
               tmp (SBopsem.bound2GV (los,nts) mb' tsz n))
             (mb'::als2)):: 
            ECs2) gl2 fs2 Mem2'); auto.
      apply LLVMopsem.dsGEP with (mp:=blk2GV (los,nts) mb')(vidxs:=[gn']); auto.
        simpl.
        rewrite lookupAL_updateAddAL_eq; auto.

        assert(getOperandValue (los,nts) (value_id ntmp)
          (updateAddAL _ (updateAddAL _ lc2 ntmp gn') 
             id0 (blk2GV (los,nts) mb')) gl2 = Some gn') as EQ'.
          rewrite <- getOperandValue_eq_fresh_id; auto.
          simpl. apply lookupAL_updateAddAL_eq; auto.
        
        simpl. simpl in EQ'.
        rewrite EQ'. clear EQ'.
        auto.

        unfold SBopsem.bound2GV, GEP, blk2GV, GV2ptr, ptr2GV, val2GV.
        simpl.
        rewrite <- Heqgn. rewrite H2.
        unfold Constant.typ2utyp.
        assert (exists ut, 
          Constant.typ2utyp_aux (Constant.subst_nts_by_nts nts nts) 
            (typ_array 0%nat t) = Some (typ_array 0%nat ut) /\
          getTypeAllocSize (los, nts) ut = getTypeAllocSize (los, nts) t) as EQ1.
          destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
          eapply wf_system__wf_cmd with (c:=insn_alloca id0 t v align0) in HBinF;
            eauto.
            inv HBinF. inv H22.
            simpl. destruct H0 as [J3 J4].
            unfold Constant.typ2utyp in J3.
            rewrite J3. simpl. eauto.

            apply in_or_app. simpl. auto.
        destruct EQ1 as [ut [EQ1 EQ2]].
        rewrite EQ1. simpl.
        rewrite EQ2. rewrite H. simpl.
        rewrite Int.add_commut.
        rewrite Int.add_zero. auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
        LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
             (insn_cast eid castop_bitcast (typ_pointer t)(value_id tmp) p8 :: 
              cs2' ++ cs23)
             tmn2 
             (updateAddAL _
               (updateAddAL _
                 (updateAddAL _ 
                   (updateAddAL _ lc2 ntmp gn') id0 (blk2GV (los,nts) mb'))
                 tmp (SBopsem.bound2GV (los,nts) mb' tsz n))
               bid (SBopsem.base2GV (los,nts) mb'))               
             (mb'::als2)):: 
            ECs2) gl2 fs2 Mem2'); auto.
      apply LLVMopsem.dsCast; auto.
        unfold CAST. simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.

          clear - HeqR2 Hinc1 Hinc' Hin.
          eapply tmp_is_fresh2 with (d:=getFdefLocs (fdef_intro fh1 bs1)); eauto.
 
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
       (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
                (updateAddAL _ 
                  (updateAddAL _ 
                    (updateAddAL _ 
                      (updateAddAL _
                        (updateAddAL _ lc2 ntmp gn') id0 (blk2GV (los, nts) mb'))
                      tmp (SBopsem.bound2GV (los, nts) mb' tsz n))
                    bid (SBopsem.base2GV (los, nts) mb'))                    
                  eid (SBopsem.bound2GV (los, nts) mb' tsz n))
             (mb'::als2)):: 
            ECs2) gl2 fs2 Mem2')); auto.
      apply LLVMopsem.dsCast; auto.
        unfold CAST. simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.

          clear - HeqR2 Hinc3 Hinc' HeqR1.
          eapply tmp_is_fresh3 with (tmp:=tmp) in HeqR1; eauto.
          destruct HeqR1; auto.

  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split.
  split.
  split; auto.          
  split; auto.          
  split; auto.          
  split; auto.          
  split; auto.          
  split; auto.          
  split; auto.          
  split; auto.
  split. 
    split; eauto using inject_incr__preserves__als_simulation; eauto.
  split; auto.
  split.
    eapply cmds_at_block_tail_next; eauto.
  split.
    destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
    exists l2. exists ps2. exists (cs21 ++
                  (insn_cast ntmp castop_bitcast i32 v i32 ::
                    insn_alloca id0 t v align0
                    :: insn_gep tmp false t (value_id id0)
                         (Cons_list_value (value_id ntmp) Nil_list_value)
                       :: insn_cast bid castop_bitcast 
                            (typ_pointer t) (value_id id0) p8
                          :: insn_cast eid castop_bitcast 
                               (typ_pointer t) (value_id tmp) p8 :: nil)).
    simpl_env. auto.
  exists ex_ids. exists rm2.
  exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
  split.
  SCase "rsim".
    eapply reg_simulation__updateAddAL_md; eauto.
      eapply reg_simulation__updateAddAL_tmp with (ex_ids5:=ex_ids5)
        (ex_ids3':=ex_ids6'); eauto.
      eapply reg_simulation__updateAddAL_lc; eauto.
      eapply reg_simulation__updateAddAL_tmp with (ex_ids5:=ex_ids6')
        (ex_ids3':=ex_ids3); eauto.
        eapply inject_incr__preserves__reg_simulation; eauto.

      unfold blk2GV, ptr2GV, val2GV.
      simpl. eauto.

      unfold SBopsem.base2GV, blk2GV, ptr2GV, val2GV.
      simpl. clear - H14. eauto.

      unfold SBopsem.bound2GV, blk2GV, ptr2GV, val2GV.
      simpl. clear - H14.
        apply gv_inject_cons; eauto.
          eapply MoreMem.val_inject_ptr; eauto.
            rewrite Int.add_zero. auto.

    split; auto.
      clear - HsimECs H13. 
      eapply inject_incr__preserves__sbECs_simulate_ECs_tail; eauto.
    repeat(split; eauto using inject_incr__preserves__fable_simulation).
Qed.

Lemma SBpass_is_correct__dsFree : forall (mi : MoreMem.meminj) (mgb : Values.block)
  (St : LLVMopsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : GVMap) (rm : rmetadata) (gl : GVMap)
  (fs : GVMap) (fid : id) (t : typ) (v : value) (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (als : list mblock)
  (MM : mmetadata)
  (Hsim : sbState_simulates_State mi mgb
           {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_free fid t v :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Globals := gl;
           FunTable := fs;
           Mem := Mem0;
           Mmap := MM |} St)
  (Mem' : mem)
  (mptr0 : GenericValue)
  (H : getOperandValue TD v lc gl = ret mptr0)
  (H0 : free TD Mem0 mptr0 = ret Mem'),
   exists St' : LLVMopsem.State,
     exists mi' : MoreMem.meminj,
       LLVMopsem.dsop_star St St' trace_nil /\
       sbState_simulates_State mi' mgb
         {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc;
                Rmap := rm;
                Allocas := als |} :: EC;
         Globals := gl;
         FunTable := fs;
         Mem := Mem';
         Mmap := MM |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd. 
  inv Htcmd.
  apply free_inv in H0.
  destruct H0 as [blk [i0 [hi [lo [HeqR0 [J12 [HeqR2 H0]]]]]]].
  eapply simulation__getOperandValue in H; eauto.
  destruct H as [mptr0' [H1 H2]].
  eapply simulation__GV2ptr in HeqR0; eauto.
  destruct HeqR0 as [v' [J1 J2]].
  inv J2.
  eapply mem_simulation__free in H0; eauto.
  destruct H0 as [Mem2' [Hfree2 [Hwfmi2  Hmsim2]]].
  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 lc2
             als2):: 
            ECs2) gl2 fs2 Mem2').
  exists mi.
  split.
  SCase "opsem".
    simpl.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    eapply LLVMopsem.dsop_star_cons; eauto.
      apply LLVMopsem.dsFree with (mptr:=mptr0'); auto.
        unfold free.     
        rewrite J1.
        inversion_clear Hwfmi.
        assert (H4':=H4).
        apply mi_range_block in H4'. subst.
        rewrite Int.add_zero.
        destruct (zeq (Int.signed 31 i0) 0).
          apply mi_bounds in H4.
          rewrite <- H4. rewrite <- HeqR2.
          assert (lo + 0 = lo) as EQ''. auto with zarith. 
          rewrite EQ'' in Hfree2. clear EQ''.
          assert (hi + 0 = hi) as EQ''. auto with zarith.
          rewrite EQ'' in Hfree2. clear EQ''.
          auto.

          clear - J12 n. contradict J12; auto.          

  repeat (split; auto).
    eapply cmds_at_block_tail_next; eauto.

    simpl_env in Heqb2. simpl in Heqb2.
    eapply cmds_at_block_tail_next; eauto.

  exists ex_ids. exists rm2.
  exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
Qed.

Lemma SBpass_is_correct__dsLoad_nptr : forall 
  (mi : MoreMem.meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : GVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : id) (t : typ)
  (align0 : align) (vp : value) (EC : list ExecutionContext) (cs : list cmd)
  (tmn : terminator) (Mem0 : mem) (als : list mblock) (MM : mmetadata)
  (Hsim : sbState_simulates_State mi mgb
           {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_load id0 t vp align0 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Globals := gl;
           FunTable := fs;
           Mem := Mem0;
           Mmap := MM |} St)
  (gvp : GenericValue) (gv : GenericValue) (md : metadata)
  (H : SBopsem.get_reg_metadata TD gl rm vp = ret md)
  (H0 : getOperandValue TD vp lc gl = ret gvp)
  (H1 : assert_mptr TD t gvp md)
  (H2 : mload TD Mem0 gvp t align0 = ret gv)
  (H3 : isPointerTypB t = false),
   exists St' : LLVMopsem.State,
     exists mi' : MoreMem.meminj,
       LLVMopsem.dsop_star St St' trace_nil /\
       sbState_simulates_State mi' mgb
         {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := updateAddAL GenericValue lc id0 gv;
                Rmap := rm;
                Allocas := als |} :: EC;
         Globals := gl;
         FunTable := fs;
         Mem := Mem0;
         Mmap := MM |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd. 
  remember (get_reg_metadata rm2 vp) as R.
  destruct R as [[bv ev]|]; try solve [inversion Htcmd].
  remember (mk_tmp ex_ids3) as R1. 
  destruct R1 as [ptmp ex_ids3'].
  remember (isPointerTypB t) as R4.
  destruct R4.
  SCase "t is ptr".
    unfold isPointerTyp in H3.
    inv H3.

  SCase "t isnt ptr".
  inv Htcmd.
  assert (J:=H1).
  unfold SBopsem.assert_mptr in J.
  destruct md as [md_base md_bound].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (getTypeAllocSize (los,nts) t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gvp2 [H00 H01]].            
  eapply simulation__mload in H2; eauto.
  destruct H2 as [gv2 [H21 H22]].
  assert (J':=Hrsim).
  destruct J' as [Hrsim1 Hrsim2].
  assert (HeqR8':=H).
  apply Hrsim2 in HeqR8'.      
  destruct HeqR8' as [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
  rewrite J1 in HeqR. inv HeqR.
  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
                  (updateAddAL _ 
                    (updateAddAL GenericValue lc2 ptmp gvp2)
                   id0 gv2)
             als2):: 
            ECs2) gl2 fs2 M2).
  exists mi.
  split.
  SSCase "opsem".
    simpl.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
       (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (insn_call fake_id true attrs assert_typ assert_fn
              ((p8, bv2)::(p8, ev2)::(p8, value_id ptmp)::(i32, type_size t):: 
                 (i32, vint1) :: nil):: 
             insn_load id0 t vp align0 :: cs2' ++ cs23) tmn2 
            (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 M2)).
      apply LLVMopsem.dsCast; auto.
        unfold CAST. simpl. simpl in H00.
        rewrite H00. auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
       (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (insn_load id0 t vp align0 :: cs2' ++ cs23) tmn2 
            (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 M2)).
       clear - H00 J2 J3 J4 J5 J H00 H01 HeqR0 HeqR2 HeqR3 HeqR5.
       eapply assert_mptr_fn__ok with (b:=b)(b0:=b0)(b1:=b1); eauto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
       (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
            (updateAddAL _ (updateAddAL GenericValue lc2 ptmp gvp2) id0 gv2)
             als2):: 
            ECs2) gl2 fs2 M2)); auto.
      apply LLVMopsem.dsLoad with (mp:=gvp2); auto.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          assert (sb_ds_sim.getValueID vp[<=]ids2atoms (getFdefLocs (fdef_intro fh1 bs1))) as Hindom.
            assert (Hwfc := HBinF).
            destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
            eapply wf_system__wf_cmd with (c:=insn_load id0 t vp align0)  
              in Hwfc; eauto.
              inv Hwfc. 
              eapply wf_value_id__in_getFdefLocs in H11; auto.
              apply in_or_app. right. simpl. auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

  repeat (split; auto).
    eapply cmds_at_block_tail_next; eauto.

    destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
    exists l2. exists ps2. exists (cs21 ++
                  (insn_cast ptmp castop_bitcast (typ_pointer t) vp p8
                    :: insn_call fake_id true attrs assert_typ assert_fn
                         ((p8, bv2)
                          :: (p8, ev2)
                             :: (p8, value_id ptmp)
                                :: (i32, type_size t) :: (i32, vint1) :: nil)
                       :: insn_load id0 t vp align0 :: nil)).
    simpl_env. auto.

  exists ex_ids. exists rm2.
  exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
  split.
    eapply reg_simulation__updateAddAL_lc; eauto.
      eapply reg_simulation__updateAddAL_tmp; eauto.
        eauto using getCmdID_in_getFdefLocs.

    split; auto.
      clear - Hinc HeqR1. eapply mk_tmp_inc; eauto.
Qed.

Lemma SBpass_is_correct__dsLoad_ptr : forall 
  (mi : MoreMem.meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : GVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : id) (t : typ)
  (align0 : align) (vp : value) (EC : list ExecutionContext) (cs : list cmd)
  (tmn : terminator) (Mem0 : mem) (als : list mblock) (MM : mmetadata)
  (Hsim : sbState_simulates_State mi mgb
           {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_load id0 t vp align0 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Globals := gl;
           FunTable := fs;
           Mem := Mem0;
           Mmap := MM |} St)
  md' lc' rm'
  (gvp : GenericValue) (gv : GenericValue) (md : metadata)
  (H : SBopsem.get_reg_metadata TD gl rm vp = ret md)
  (H0 : getOperandValue TD vp lc gl = ret gvp)
  (H1 : assert_mptr TD t gvp md)
  (H2 : mload TD Mem0 gvp t align0 = ret gv)
  (H3 : isPointerTypB t = true)
  (H4 : get_mem_metadata TD MM gvp = md')
  (H5 : prop_reg_metadata lc rm id0 gv md' = (lc', rm')),
   exists St' : LLVMopsem.State,
     exists mi' : MoreMem.meminj,
       LLVMopsem.dsop_star St St' trace_nil /\
       sbState_simulates_State mi' mgb
         {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: EC;
         Globals := gl;
         FunTable := fs;
         Mem := Mem0;
         Mmap := MM |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd. 
  remember (get_reg_metadata rm2 vp) as R.
  destruct R as [[bv ev]|]; try solve [inversion Htcmd].
  remember (mk_tmp ex_ids3) as R1. 
  destruct R1 as [ptmp ex_ids3'].
  remember (isPointerTypB t) as R4.
  destruct R4; try solve [inv H3].
  remember (lookupAL (id * id) rm2 id0) as R5.
  destruct R5 as [[bid0 eid0]|]; inv Htcmd.
  assert (J:=H1).
  unfold SBopsem.assert_mptr in J.
  destruct md as [md_base md_bound].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (getTypeAllocSize (los,nts) t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gvp2 [H00 H01]].            
  unfold SBopsem.get_reg_metadata in H.
  assert (H2':=H2).
  eapply simulation__mload in H2'; eauto.
  destruct H2' as [gv2 [H21 H22]].
  assert (J':=Hrsim).
  destruct J' as [Hrsim1 Hrsim2].
  case_eq (SBopsem.get_mem_metadata (los,nts) MM gvp).
  intros mb_base0 md_bound0 JJ.
  assert (Hmsim':=HsimM).
  destruct Hmsim' as [Hmsim1 [Hmgb [Hzeroout Hmsim2]]].
  assert (JJ':=JJ).
  assert (exists b, exists ofs, exists cm, gvp = (Vptr b ofs, cm)::nil) as EQ.
    clear - H2.
    eapply mload_inversion; eauto.
  destruct EQ as [pb [pofs [cm EQ]]]. subst.

  assert (In id0 (getFdefLocs (fdef_intro fh1 bs1))) as Hin. 
    eauto using getCmdID_in_getFdefLocs.
  assert (Hspec := Hgenmeta).
  apply gen_metadata_fdef_spec in Hspec; auto.
  destruct Hspec as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].

  assert (getOperandValue (los, nts) (value_id ptmp) 
      (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) id0 gv2) gl2 = ret gvp2) as K.
    simpl.
    rewrite <- lookupAL_updateAddAL_neq; auto.
      rewrite lookupAL_updateAddAL_eq; auto.
      apply tmp_is_fresh2 with (i0:=id0)(d:=getFdefLocs (fdef_intro fh1 bs1)) 
        (ex_ids1:=ex_ids) in HeqR1; auto.

  eapply Hmsim2 with (bid0:=bid0)(eid0:=eid0)(lc2:=
    (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) id0 gv2)) in JJ'; eauto.
  destruct JJ' as [bgv' [egv' [JJ1 [JJ2 JJ4]]]].
  assert (HeqR9':=H).
  apply Hrsim2 in HeqR9'.      
  destruct HeqR9' as [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
  rewrite J1 in HeqR. inv HeqR.
  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
               (updateAddAL _ 
                 (updateAddAL _ 
                   (updateAddAL _ 
                    (updateAddAL GenericValue lc2 ptmp gvp2)
                   id0 gv2)
                  bid0 bgv')
                 eid0 egv')
             als2):: 
            ECs2) gl2 fs2 M2).
  exists mi.
  split.
  SSCase "opsem".
    simpl.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
       (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (insn_call fake_id true attrs assert_typ assert_fn
              ((p8, bv2)::(p8, ev2)::(p8, value_id ptmp)::(i32, type_size t):: 
                 (i32, vint1) :: nil):: 
             insn_load id0 t vp align0 :: 
             insn_call bid0 false attrs gmb_typ gmb_fn
               ((p8, value_id ptmp)::(p8, vnullp8)::(i32, vint1):: 
                  (p32, vnullp32) :: nil) :: 
             insn_call eid0 false attrs gme_typ gme_fn
               ((p8, value_id ptmp)::(p8, vnullp8)::(i32, vint1):: 
                  (p32, vnullp32) :: nil) :: 
             cs2' ++ cs23) tmn2 
            (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 M2)).
      apply LLVMopsem.dsCast; auto.
        unfold CAST. simpl. simpl in H00.
        rewrite H00. auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
       (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (insn_load id0 t vp align0 :: 
             insn_call bid0 false attrs gmb_typ gmb_fn
               ((p8, value_id ptmp)::(p8, vnullp8)::(i32, vint1):: 
                  (p32, vnullp32) :: nil) :: 
             insn_call eid0 false attrs gme_typ gme_fn
               ((p8, value_id ptmp)::(p8, vnullp8)::(i32, vint1):: 
                  (p32, vnullp32) :: nil) :: 
             cs2' ++ cs23) tmn2 
            (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 M2)).
       clear - H00 J2 J3 J4 J5 J H00 H01 HeqR0 HeqR2 HeqR3 HeqR5 HeqR6.
       eapply assert_mptr_fn__ok with (b:=b)(b0:=b0)(b1:=b1); eauto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
       (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (insn_call bid0 false attrs gmb_typ gmb_fn
               ((p8, value_id ptmp)::(p8, vnullp8)::(i32, vint1):: 
                  (p32, vnullp32) :: nil) :: 
             insn_call eid0 false attrs gme_typ gme_fn
               ((p8, value_id ptmp)::(p8, vnullp8)::(i32, vint1):: 
                  (p32, vnullp32) :: nil) :: 
             cs2' ++ cs23) tmn2 
                 (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) id0 gv2)
             als2):: 
            ECs2) gl2 fs2 M2)); eauto.
      apply LLVMopsem.dsLoad with (mp:=gvp2); auto.
        rewrite <- getOperandValue_eq_fresh_id; auto.
        assert (sb_ds_sim.getValueID vp[<=]ids2atoms (getFdefLocs (fdef_intro fh1 bs1))) as Hindom.
            assert (Hwfc := HBinF).
            destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
            eapply wf_system__wf_cmd with (c:=insn_load id0 t vp align0)  
              in Hwfc; eauto.
              inv Hwfc. 
              eapply wf_value_id__in_getFdefLocs in H13; auto.
              apply in_or_app. right. simpl. auto.
        eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split.
    eapply cmds_at_block_tail_next; eauto.
  split.
    destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
    exists l2. exists ps2. exists (cs21 ++
           (insn_cast ptmp castop_bitcast (typ_pointer t) vp p8 ::
            insn_call fake_id true attrs assert_typ assert_fn
              ((p8, bv2)::(p8, ev2)::(p8, value_id ptmp)::(i32, type_size t):: 
                 (i32, vint1) :: nil):: 
            insn_load id0 t vp align0 :: 
            insn_call bid0 false attrs gmb_typ gmb_fn
               ((p8, value_id ptmp)::(p8, vnullp8)::(i32, vint1):: 
                  (p32, vnullp32) :: nil) :: 
            insn_call eid0 false attrs gme_typ gme_fn
               ((p8, value_id ptmp)::(p8, vnullp8)::(i32, vint1):: 
                  (p32, vnullp32)::nil) :: nil)).
    simpl_env. auto.
  exists ex_ids. exists rm2.
  exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
  split.
    inv H5. rewrite JJ.
    eapply reg_simulation__updateAddAL_prop; eauto.
      eapply reg_simulation__updateAddAL_tmp; eauto.
    split; auto.
      clear - Hinc HeqR1. eapply mk_tmp_inc; eauto.
Qed.

Lemma SBpass_is_correct__dsStore_nptr : forall 
  (mi : MoreMem.meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : GVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (sid : id) (t : typ) 
  (align0 : align) (v : value) (vp : value) (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (MM : mmetadata) 
  (als : list mblock)
  (Hsim : sbState_simulates_State mi mgb
           {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_store sid t v vp align0 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Globals := gl;
           FunTable := fs;
           Mem := Mem0;
           Mmap := MM |} St)
  (gv : GenericValue) (gvp : GenericValue) (md : metadata) (Mem' : mem)
  (H : SBopsem.get_reg_metadata TD gl rm vp = ret md)
  (H0 : getOperandValue TD v lc gl = ret gv)
  (H1 : getOperandValue TD vp lc gl = ret gvp)
  (H2 : assert_mptr TD t gvp md)
  (H3 : mstore TD Mem0 gvp t gv align0 = ret Mem')
  (H4 : isPointerTypB t = false),
   exists St' : LLVMopsem.State,
     exists mi' : MoreMem.meminj,
       LLVMopsem.dsop_star St St' trace_nil /\
       sbState_simulates_State mi' mgb
         {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc;
                Rmap := rm;
                Allocas := als |} :: EC;
         Globals := gl;
         FunTable := fs;
         Mem := Mem';
         Mmap := MM |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd. 
  remember (get_reg_metadata rm2 vp) as R.
  destruct R as [[bv ev]|]; try solve [inversion Htcmd].
  remember (mk_tmp ex_ids3) as R1. 
  destruct R1 as [ptmp ex_ids3'].
  remember (isPointerTypB t) as R4.
  destruct R4; try solve [inv H4].
  inv Htcmd.
  assert (J:=H2).
  unfold SBopsem.assert_mptr in J.
  destruct md as [md_base md_bound].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (getTypeAllocSize (los,nts) t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gv2 [H00 H01]].            
  eapply simulation__getOperandValue in H1; eauto.
  destruct H1 as [gvp2 [H10 H11]].            
  unfold SBopsem.get_reg_metadata in H.
  assert (Hmstore:=H3).
  eapply simulation__mstore in H3; eauto.
  destruct H3 as [Mem2' [H31 [H33 H32]]].
  assert (J':=Hrsim).
  destruct J' as [Hrsim1 Hrsim2].
  assert (HeqR8':=H).
  apply Hrsim2 in HeqR8'.      
  destruct HeqR8' as [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
  rewrite <- HeqR in J1. inv J1.
  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
              (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 Mem2').
  exists mi.
  split.
  SSCase "opsem".
    simpl.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
      (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              (insn_call fake_id true attrs assert_typ assert_fn
                ((p8, bv2)::(p8, ev2)::(p8, value_id ptmp)::(i32, type_size t):: 
                   (i32, vint1) :: nil):: 
               insn_store sid t v vp align0 :: 
               cs2' ++ cs23) tmn2 
              (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 M2)).
      apply LLVMopsem.dsCast; auto.
        unfold CAST. simpl. simpl in H10.
        rewrite H10. auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
      (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              (insn_store sid t v vp align0 :: 
               cs2' ++ cs23) tmn2 
              (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 M2)).
       clear - H00 J2 J3 J4 J5 J H10 H11 HeqR0 HeqR2 HeqR3 HeqR5.
       eapply assert_mptr_fn__ok with (b:=b)(b0:=b0)(b1:=b1); eauto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
      (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              (cs2' ++ cs23) tmn2 
              (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 Mem2')); auto.
      assert (Hwfc := HBinF).
      destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
      assert (In (insn_store sid t v vp align0)
        (cs11 ++ insn_store sid t v vp align0 :: cs)) as HinCs.
        apply in_or_app. right. simpl. auto.
      eapply wf_system__wf_cmd with (c:=insn_store sid t v vp align0) in Hwfc; 
        eauto.
      inv Hwfc. 
      apply LLVMopsem.dsStore with (mp2:=gvp2)(gv1:=gv2); auto.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          assert (sb_ds_sim.getValueID v[<=]ids2atoms (getFdefLocs (fdef_intro fh1 bs1))) as Hindom.
            eapply wf_value_id__in_getFdefLocs in H14; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

        rewrite <- getOperandValue_eq_fresh_id; auto.
          assert (sb_ds_sim.getValueID vp[<=]ids2atoms (getFdefLocs (fdef_intro fh1 bs1))) as Hindom.
            eapply wf_value_id__in_getFdefLocs in H17; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split.
    eapply cmds_at_block_tail_next; eauto.
  split.
    destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
    exists l2. exists ps2. exists (cs21 ++
                  (insn_cast ptmp castop_bitcast (typ_pointer t) vp p8
                    :: insn_call fake_id true attrs assert_typ assert_fn
                         ((p8, bv2)
                          :: (p8, ev2)
                             :: (p8, value_id ptmp)
                                :: (i32, type_size t) :: (i32, vint1) :: nil)
                       :: insn_store sid t v vp align0 :: nil)).
    simpl_env. auto.
  exists ex_ids. exists rm2.
  exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
  split.
    eapply reg_simulation__updateAddAL_tmp; eauto.
    split; auto.
      clear - Hinc HeqR1. eapply mk_tmp_inc; eauto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  SSCase "wfmi".
    clear - H33 H31 Hmstore Hwfmi.
    inversion H33.
    unfold mstore in Hmstore.
    destruct (GV2ptr (los,nts) (getPointerSize (los,nts)) gvp); 
      try solve [inversion Hmstore].
    destruct v; try solve [inversion Hmstore].
    destruct (typ2memory_chunk t); try solve [inversion Hmstore].
    destruct (GV2val (los,nts) gv); try solve [inversion Hmstore].
    erewrite <- Mem.nextblock_store with (m1:=Mem0) in Hmap1; eauto.
    split; auto.
    SSSCase "mi_bounds".
      intros b1 b2 delta J.
      erewrite Mem.bounds_store with (m1:=Mem0); eauto.
Qed.

Lemma SBpass_is_correct__dsStore_ptr : forall (mi : MoreMem.meminj) (mgb : Values.block)
  (St : LLVMopsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : GVMap) (rm : rmetadata) (gl : GVMap) (fs : GVMap)
  (sid : id) (t : typ) (align0 : align) (v : value) (vp : value) 
  (EC : list ExecutionContext) (cs : list cmd) (tmn : terminator) (Mem0 : mem)
  (MM : mmetadata) (als : list mblock) 
  (Hsim : sbState_simulates_State mi mgb
           {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_store sid t v vp align0 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Globals := gl;
           FunTable := fs;
           Mem := Mem0;
           Mmap := MM |} St)
  (gv : GenericValue) (gvp : GenericValue) (md : metadata)
  (md' : metadata) (Mem' : mem) (MM' : mmetadata)
  (H : SBopsem.get_reg_metadata TD gl rm vp = ret md)
  (H0 : getOperandValue TD v lc gl = ret gv)
  (H1 : getOperandValue TD vp lc gl = ret gvp)
  (H2 : assert_mptr TD t gvp md)
  (H3 : mstore TD Mem0 gvp t gv align0 = ret Mem')
  (H4 : isPointerTypB t = true)
  (H5 : SBopsem.get_reg_metadata TD gl rm v = ret md')
  (H6 : set_mem_metadata TD MM gvp md' = MM'),
   exists St' : LLVMopsem.State,
     exists mi' : MoreMem.meminj,
       LLVMopsem.dsop_star St St' trace_nil /\
       sbState_simulates_State mi' mgb
         {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc;
                Rmap := rm;
                Allocas := als |} :: EC;
         Globals := gl;
         FunTable := fs;
         Mem := Mem';
         Mmap := MM' |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd. 
  remember (get_reg_metadata rm2 vp) as R.
  destruct R as [[bv ev]|]; try solve [inversion Htcmd].
  remember (mk_tmp ex_ids3) as R1. 
  destruct R1 as [ptmp ex_ids3'].
  remember (isPointerTypB t) as R4.
  destruct R4; try solve [inv H4].
  remember (get_reg_metadata rm2 v) as R5.
  destruct R5 as [[bv0 ev0]|]; inv Htcmd.
  assert (J:=H2).
  unfold SBopsem.assert_mptr in J.
  destruct md as [md_base md_bound].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (getTypeAllocSize (los,nts) t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gv2 [H00 H01]].            
  eapply simulation__getOperandValue in H1; eauto.
  destruct H1 as [gvp2 [H10 H11]].            
  unfold SBopsem.get_reg_metadata in H.
  assert (H3':=H3).
  eapply simulation__mstore in H3'; eauto.
  destruct H3' as [Mem2' [H31 [H33 H32]]].
  assert (J':=Hrsim).
  destruct J' as [Hrsim1 Hrsim2].

  destruct md' as [md_base' md_bound'].
  assert (HeqR9':=H).
  apply Hrsim2 in HeqR9'.      
  destruct HeqR9' as [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
  assert (H5':=H5).      
  apply Hrsim2 in H5'.
  destruct H5' as [bv2' [ev2' [bgv2' [egv2' [J1' [J2' [J3' [J4' J5']]]]]]]].
  simpl in HeqR5.
  rewrite J1' in HeqR5.
  inv HeqR5.
  rewrite <- HeqR in J1. inv J1.

  assert (exists Mem2'',
    LLVMopsem.dsInsn
      (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              (insn_call fake_id true attrs smmd_typ smmd_fn
                ((p8, value_id ptmp) :: (p8, bv2') :: (p8, ev2') :: (p8, vnullp8)
                    :: (i32, vint1) :: (i32, vint1) :: nil):: 
               cs2' ++ cs23) tmn2 
              (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 Mem2')
      (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              (cs2' ++ cs23) tmn2 
              (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 Mem2'') trace_nil /\
      mem_simulation mi (los,nts) mgb
        (SBopsem.set_mem_metadata (los,nts) MM gvp 
          (SBopsem.mkMD md_base' md_bound')) 
        Mem' Mem2'') as W.
    assert (exists b : Values.block, exists ofs : int32, exists cm,
      gvp = (Vptr b ofs,cm)::nil) as EQ.
      clear - H11 H31 H3.
      eapply mstore_inversion; eauto.
    destruct EQ as [b2 [ofs2 [cm EQ]]]. subst.

    eapply simulation__set_mmetadata_fn with (pgv':=gvp2)(bgv':=bgv2')
      (egv':=egv2')(rm:=rm)(v:=v); simpl; eauto.
      clear - HeqR1 HeqR2 HeqR3.
      rewrite lookupAL_updateAddAL_eq; auto.

      clear - J2' H31 J1' HeqR1 HeqR2 HeqR3 Hgenmeta Hinc.
      rewrite <- getOperandValue_eq_fresh_id; eauto.
        eapply get_reg_metadata__fresh with (rm2:=rm2) in J1'; 
          eauto; try fsetdec. destruct J1'; auto.

      clear - J3' H31 J1' HeqR1 HeqR2 HeqR3 Hgenmeta Hinc.
      rewrite <- getOperandValue_eq_fresh_id; eauto.
        eapply get_reg_metadata__fresh with (rm2:=rm2) in J1'; 
          eauto; try fsetdec. destruct J1'; auto.

  destruct W as [Mem2'' [W1 W2]].

  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
              (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 Mem2'').
  exists mi.
  split.
  SSCase "opsem".
    simpl.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
      (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              (insn_call fake_id true attrs assert_typ assert_fn
                ((p8, bv2)::(p8, ev2)::(p8, value_id ptmp)::(i32, type_size t):: 
                   (i32, vint1) :: nil):: 
               insn_store sid t v vp align0 :: 
               insn_call fake_id true attrs smmd_typ smmd_fn
                ((p8, value_id ptmp) :: (p8, bv2') :: (p8, ev2') :: (p8, vnullp8)
                    :: (i32, vint1) :: (i32, vint1) :: nil):: 
              cs2' ++ cs23) tmn2 
              (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 M2)).
      apply LLVMopsem.dsCast; auto.
        unfold CAST. simpl. simpl in H10.
        rewrite H10. auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
      (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              (insn_store sid t v vp align0 :: 
               insn_call fake_id true attrs smmd_typ smmd_fn
                ((p8, value_id ptmp) :: (p8, bv2') :: (p8, ev2') :: (p8, vnullp8)
                    :: (i32, vint1) :: (i32, vint1) :: nil):: 
               cs2' ++ cs23) tmn2 
              (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 M2)).
       clear - H00 J2 J3 J4 J5 J H10 H11 HeqR0 HeqR2 HeqR3 HeqR6.
       eapply assert_mptr_fn__ok with (b:=b)(b0:=b0)(b1:=b1); eauto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
      (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              (insn_call fake_id true attrs smmd_typ smmd_fn
                ((p8, value_id ptmp) :: (p8, bv2') :: (p8, ev2') :: (p8, vnullp8)
                    :: (i32, vint1) :: (i32, vint1) :: nil):: 
               cs2' ++ cs23) tmn2 
              (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl2 fs2 Mem2')); auto.
      assert (Hwfc := HBinF).
      destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
      assert (In (insn_store sid t v vp align0)
        (cs11 ++ insn_store sid t v vp align0 :: cs)) as HinCs.
        apply in_or_app. right. simpl. auto.
      eapply wf_system__wf_cmd with (c:=insn_store sid t v vp align0) in Hwfc; 
        eauto.
      inv Hwfc. 
      apply LLVMopsem.dsStore with (mp2:=gvp2)(gv1:=gv2); auto.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          assert (sb_ds_sim.getValueID v[<=]ids2atoms (getFdefLocs (fdef_intro fh1 bs1))) as Hindom.
            eapply wf_value_id__in_getFdefLocs in H16; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

        rewrite <- getOperandValue_eq_fresh_id; auto.
          assert (sb_ds_sim.getValueID vp[<=]ids2atoms (getFdefLocs (fdef_intro fh1 bs1))) as Hindom.
            eapply wf_value_id__in_getFdefLocs in H19; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    eapply LLVMopsem.dsop_star_cons; eauto.

  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split.
    eapply cmds_at_block_tail_next; eauto.
  split.
    destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
    exists l2. exists ps2. exists (cs21 ++
                  (insn_cast ptmp castop_bitcast (typ_pointer t) vp p8
                    :: insn_call fake_id true attrs assert_typ assert_fn
                         ((p8, bv2)
                          :: (p8, ev2)
                             :: (p8, value_id ptmp)
                                :: (i32, type_size t) :: (i32, vint1) :: nil)
                       :: insn_store sid t v vp align0 :: 
                   insn_call fake_id true attrs smmd_typ smmd_fn
                      ((p8, value_id ptmp) :: (p8, bv2') :: (p8, ev2') :: 
                      (p8, vnullp8) :: (i32, vint1) :: (i32, vint1) :: nil)::   
                   nil)).
    simpl_env. auto.
  exists ex_ids. exists rm2.
  exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
  split.
    eapply reg_simulation__updateAddAL_tmp; eauto.
    split; auto.
      clear - Hinc HeqR1. eapply mk_tmp_inc; eauto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  SSCase "wfmi".
    clear - H33 H31 H3 Hwfmi W1.
    inversion H33.
    unfold mstore in H3.
    destruct (GV2ptr (los,nts) (getPointerSize (los,nts)) gvp); 
      try solve [inversion H3].
    destruct v; try solve [inversion H3].
    destruct (typ2memory_chunk t); try solve [inversion H3].
    destruct (GV2val (los,nts) gv); try solve [inversion H3].
    erewrite <- Mem.nextblock_store with (m1:=Mem0) in Hmap1; eauto.
    apply set_mmetadata_fn__prop in W1.
    destruct W1 as [W1 [W2 W3]].
    split; auto.
    SSSCase "Hmap4".
      intros b1 b2 delta2 J.
      apply Hmap2 in J.
      eauto with zarith.
    SSSCase "mappedblocks0".
      intros b1 b2 delta J.
      apply mi_mappedblocks in J.
      eauto.
    SSSCase "bounds0".
      intros b1 b2 delta J.
      apply mi_bounds in J.
      rewrite <- W3.
      erewrite Mem.bounds_store with (m1:=Mem0); eauto.
Qed.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
