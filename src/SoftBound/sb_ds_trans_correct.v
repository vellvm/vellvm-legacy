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
Require Import sb_ds_sim.
Require Import ssa_wf.
Require Import ssa_props.
Require Import sb_ds_trans_cmd_cases.
Require Import sb_ds_trans_mem_cases.

Import SB_ds_pass.

Ltac destruct_ctx_return :=
match goal with
| [Hsim : sbState_simulates_State _ _
           {|
           SBopsem.CurSystem := _;
           SBopsem.CurTargetData := ?TD;
           SBopsem.CurProducts := _;
           SBopsem.ECS := {|
                          SBopsem.CurFunction := ?F;
                          SBopsem.CurBB := _;
                          SBopsem.CurCmds := nil;
                          SBopsem.Terminator := _;
                          SBopsem.Locals := _;
                          SBopsem.Rmap := _;
                          SBopsem.Allocas := _ |}
                          :: {|
                             SBopsem.CurFunction := ?F';
                             SBopsem.CurBB := _;
                             SBopsem.CurCmds := ?c' :: _;
                             SBopsem.Terminator := _;
                             SBopsem.Locals := _;
                             SBopsem.Rmap := _;
                             SBopsem.Allocas := _ |} :: _;
           SBopsem.Globals := _;
           SBopsem.FunTable := _;
           SBopsem.Mem := _;
           SBopsem.Mmap := _ |} ?St |- _] =>
  destruct St as [S2 TD2 Ps2 ECs2 gl2 fs2 M2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Heq2 [Heq3 [Hwfg 
    [Hwfmi HsimM]]]]]]]]]];
    subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct ECs2 as [|[F2' B2' cs2' tmn2' lc2' als2'] ECs2];
    try solve [inversion HsimECs];
  destruct HsimECs as [HsimEC' HsimECs];
  destruct F as [fh1 bs1];
  destruct F2 as [fh2 bs2];
  destruct HsimEC as [HBinF [HFinPs [Htfdef [Heq0 [Hasim [Hnth [Heqb1 [Heqb2 
    [ex_ids [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [Hgenmeta [Hrsim [Hinc [Hfresh 
    [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]; subst;
  destruct F' as [fh1' bs1'];
  destruct F2' as [fh2' bs2'];
  destruct c'; try solve [inversion HsimEC'];
  destruct HsimEC' as [HBinF' [HFinPs' [Htfdef' [Heq0' [Hasim' [Hnth' [Heqb1' 
    [Heqb2' [ex_ids' [rm2' [ex_ids3' [ex_ids4' [cs22' [cs23' [cs24' 
    [Hgenmeta' [Hrsim' [Hinc' [Hcall' [Hfresh' [Htcmds' [Httmn' Heq2']]]]]]]]]]]]
    ]]]]]]]]]]; 
    subst
end.

Lemma SBpass_is_correct__dsReturn : forall 
  (mi : meminj)
  (mgb : Values.block)
  (St : LLVMopsem.State)
  (S : system)
  (TD : TargetData)
  (Ps : list product)
  (F : fdef)
  (B : block)
  (rid : id)
  (RetTy : typ)
  (Result : value)
  (lc : GVMap)
  (rm : SBopsem.rmetadata)
  (gl : GVMap)
  (fs : GVMap)
  (F' : fdef)
  (B' : block)
  (c' : cmd)
  (cs' : list cmd)
  (tmn' : terminator)
  (lc' : GVMap)
  (rm' : SBopsem.rmetadata)
  (EC : list SBopsem.ExecutionContext)
  (Mem : mem)
  (MM : SBopsem.mmetadata)
  (als : list mblock)
  (als' : list mblock)
  (Hsim : sbState_simulates_State mi mgb
           {|
           SBopsem.CurSystem := S;
           SBopsem.CurTargetData := TD;
           SBopsem.CurProducts := Ps;
           SBopsem.ECS := {|
                          SBopsem.CurFunction := F;
                          SBopsem.CurBB := B;
                          SBopsem.CurCmds := nil;
                          SBopsem.Terminator := insn_return rid RetTy Result;
                          SBopsem.Locals := lc;
                          SBopsem.Rmap := rm;
                          SBopsem.Allocas := als |}
                          :: {|
                             SBopsem.CurFunction := F';
                             SBopsem.CurBB := B';
                             SBopsem.CurCmds := c' :: cs';
                             SBopsem.Terminator := tmn';
                             SBopsem.Locals := lc';
                             SBopsem.Rmap := rm';
                             SBopsem.Allocas := als' |} :: EC;
           SBopsem.Globals := gl;
           SBopsem.FunTable := fs;
           SBopsem.Mem := Mem;
           SBopsem.Mmap := MM |} St)
  (Mem' : mem)
  (lc'' : GVMap)
  (rm'' : SBopsem.rmetadata)
  (H : Instruction.isCallInst c' = true)
  (H0 : free_allocas TD Mem als = ret Mem')
  (H1 : SBopsem.returnUpdateLocals TD c' RetTy Result lc lc' rm rm' gl =
       ret (lc'', rm'')),
  exists St' : LLVMopsem.State,
     exists mi' : meminj,
       LLVMopsem.dsop_star St St' trace_nil /\
       sbState_simulates_State mi' mgb
         {|
         SBopsem.CurSystem := S;
         SBopsem.CurTargetData := TD;
         SBopsem.CurProducts := Ps;
         SBopsem.ECS := {|
                        SBopsem.CurFunction := F';
                        SBopsem.CurBB := B';
                        SBopsem.CurCmds := cs';
                        SBopsem.Terminator := tmn';
                        SBopsem.Locals := lc'';
                        SBopsem.Rmap := rm'';
                        SBopsem.Allocas := als' |} :: EC;
         SBopsem.Globals := gl;
         SBopsem.FunTable := fs;
         SBopsem.Mem := Mem';
         SBopsem.Mmap := MM |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_return.
  inv Htcmds.
  simpl in H1.
  unfold call_suffix in Hcall'.
  unfold SBopsem.returnUpdateLocals in H1.
  remember (SBopsem.returnResult (los, nts) RetTy Result lc rm gl2) as Ret.
  destruct Ret as [[gr md]|]; try solve [inv H1].
  unfold SBopsem.returnResult in HeqRet.
  remember (getOperandValue (los, nts) Result lc gl2) as ogr.
  destruct ogr as [ogr|]; try solve [inv HeqRet].
  destruct n.
  SCase "nret = true".
    inv Hcall'.
    inv H1.
    simpl in Httmn.
    destruct (isPointerTypB RetTy).
    SSCase "rt is ptr". 
      remember (SBopsem.get_reg_metadata (los, nts) gl2 rm Result) as oRmd.
      destruct oRmd as [[bgv1 egv1]|]; inv HeqRet.
      assert (exists bv2, exists ev2, exists bgv2, exists egv2,
        get_reg_metadata rm2 Result = Some (bv2, ev2) /\
        getOperandValue (los,nts) bv2 lc2 gl2 = Some bgv2 /\
        getOperandValue (los,nts) ev2 lc2 gl2 = Some egv2 /\
        gv_inject mi bgv1 bgv2 /\
        gv_inject mi egv1 egv2) as J.
        clear - HeqoRmd Hrsim. 
        destruct Hrsim as [_ Hrsim].
        apply Hrsim; auto.
      destruct J as [bv2 [ev2 [bgv2 [egv2 [Hgetrmd [Hgetbgv2 [Hgetegv2 [Hinj1 
        Hinj2]]]]]]]]. rewrite Hgetrmd in Httmn. inv Httmn.
      destruct (@stk_ret_sim (los,nts) Mem0 M2 mi mgb MM bgv2 egv2) as 
        [M2' [M2'' [Hsbase [Hsbound [Hmsim3 [Hwfmi3 [Hgbase Hgbound]]]]]]]; 
        auto.
      eapply free_allocas_sim in Hmsim3; eauto.
      destruct Hmsim3 as [M2''' [Hfree2' [Hmsim2' Hwfmi2']]].
      exists (LLVMopsem.mkState S2 (los, nts) Ps2
        ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' lc2' als2'):: ECs2)
        gl2 fs2 M2''').
      exists mi.
      split.
      SSSCase "dsop_star".
        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              ((insn_call fake_id true attrs sse_typ sse_fn 
                  ((p8, ev2)::(i32, vint0) :: nil))::nil)
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 true c t (wrap_call v) p)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2')).
          eapply LLVMopsem.dsExCall with (fid:=ssb_fid)
            (gvs:=(bgv2 :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply ssb_is_found; eauto.
            simpl. rewrite Hgetbgv2. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2 nil
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 true c t (wrap_call v) p)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2'')).
          eapply LLVMopsem.dsExCall with (fid:=sse_fid)
            (gvs:=(egv2 :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply sse_is_found; eauto.
            simpl. rewrite Hgetegv2. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
            unfold LLVMopsem.returnUpdateLocals. simpl.
            clear - Hrsim Heqogr Hwfg Hwfmi.
            symmetry in Heqogr.
            eapply simulation__getOperandValue in Heqogr; eauto.
            destruct Heqogr as [gv' [J1 J2]]. rewrite J1. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (cs23' ++ cs24')
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2''')); auto.
          eapply LLVMopsem.dsExCall; simpl; eauto.
            eapply dstk_is_found; eauto.
            eapply dstk_spec; eauto.

      split; auto using inject_incr_refl.
      SSSCase "sim".
      repeat (split; auto).
          eapply cmds_at_block_tail_next; eauto.

          destruct Heqb2' as [l2' [ps2' [cs21' Heqb2']]]; subst.
          exists l2'. exists ps2'. exists (cs21' ++
              [insn_call i0 true c t (wrap_call v) p] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          repeat (split; auto).

    SSCase "rt isnt ptr".
      inv Httmn.
      destruct (@stk_ret_sim (los,nts) Mem0 M2 mi mgb MM null null) as 
        [M2' [M2'' [Hsbase [Hsbound [Hmsim3 [Hwfmi3 [Hgbase Hgbound]]]]]]]; 
        auto.
      eapply free_allocas_sim in Hmsim3; eauto.
      destruct Hmsim3 as [M2''' [Hfree2' [Hmsim2' Hwfmi2']]].
      exists (LLVMopsem.mkState S2 (los, nts) Ps2
        ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' lc2' als2'):: ECs2)
        gl2 fs2 M2''').
      exists mi.
      split.
      SSSCase "dsop_star".
        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              ((insn_call fake_id true attrs sse_typ sse_fn 
                  ((p8, vnullp8)::(i32, vint0) :: nil))::nil)
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 true c t (wrap_call v) p)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2')).
          eapply LLVMopsem.dsExCall with (fid:=ssb_fid)
            (gvs:=(null :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply ssb_is_found; eauto.
        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2 nil
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 true c t (wrap_call v) p)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2'')).
          eapply LLVMopsem.dsExCall with (fid:=sse_fid)
            (gvs:=(null :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply sse_is_found; eauto.
        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
            unfold LLVMopsem.returnUpdateLocals. simpl.
            clear - Hrsim Heqogr Hwfg Hwfmi.
            symmetry in Heqogr.
            eapply simulation__getOperandValue in Heqogr; eauto.
            destruct Heqogr as [gv' [J1 J2]]. rewrite J1. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (cs23' ++ cs24')
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2''')); auto.
          eapply LLVMopsem.dsExCall; simpl; eauto.
            eapply dstk_is_found; eauto.
            eapply dstk_spec; eauto.

      split; auto using inject_incr_refl.
      SSSCase "sim".
      repeat (split; auto).
          eapply cmds_at_block_tail_next; eauto.

          destruct Heqb2' as [l2' [ps2' [cs21' Heqb2']]]; subst.
          exists l2'. exists ps2'. exists (cs21' ++
              [insn_call i0 true c t (wrap_call v) p] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          repeat (split; auto).

  SCase "nret = false".
    destruct (SBopsem.isReturnPointerTypB t).
    SSCase "ct is ptr".
      simpl in Hcall'.
      remember (lookupAL (id * id) rm2' i0) as R.
      destruct R as [[bid0 eid0]|]; inv Hcall'.
      simpl in Httmn.
      destruct (isPointerTypB RetTy).
    SSSCase "rt is ptr". 
      inv H1.
      remember (SBopsem.get_reg_metadata (los, nts) gl2 rm Result) as oRmd.
      destruct oRmd as [[bgv1 egv1]|]; inv HeqRet.
      assert (exists bv2, exists ev2, exists bgv2, exists egv2,
        get_reg_metadata rm2 Result = Some (bv2, ev2) /\
        getOperandValue (los,nts) bv2 lc2 gl2 = Some bgv2 /\
        getOperandValue (los,nts) ev2 lc2 gl2 = Some egv2 /\
        gv_inject mi bgv1 bgv2 /\
        gv_inject mi egv1 egv2) as J.
        clear - HeqoRmd Hrsim. 
        destruct Hrsim as [_ Hrsim].
        apply Hrsim; auto.
      destruct J as [bv2 [ev2 [bgv2 [egv2 [Hgetrmd [Hgetbgv2 [Hgetegv2 [Hinj1 
        Hinj2]]]]]]]]. rewrite Hgetrmd in Httmn. inv Httmn.
      destruct (@stk_ret_sim (los,nts) Mem0 M2 mi mgb MM bgv2 egv2) as 
        [M2' [M2'' [Hsbase [Hsbound [Hmsim3 [Hwfmi3 [Hgbase Hgbound]]]]]]]; 
        auto.
      eapply free_allocas_sim in Hmsim3; eauto.
      destruct Hmsim3 as [M2''' [Hfree2' [Hmsim2' Hwfmi2']]].
      symmetry in Heqogr.
      eapply simulation__getOperandValue in Heqogr; eauto.
      destruct Heqogr as [gr2 [J1 J2]]. 
      exists (LLVMopsem.mkState S2 (los, nts) Ps2
        ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' 
            (updateAddAL _ (updateAddAL _ (updateAddAL _ lc2' i0 gr2) bid0 bgv2) 
              eid0 egv2)
            als2'):: ECs2)
        gl2 fs2 M2''').
      exists mi.
      split.
      SSSSCase "dsop_star".
        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              ((insn_call fake_id true attrs sse_typ sse_fn 
                  ((p8, ev2)::(i32, vint0) :: nil))::nil)
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 false c t (wrap_call v) p)::
               insn_call bid0 false attrs gsb_typ gsb_fn((i32, vint0) :: nil):: 
               insn_call eid0 false attrs gse_typ gse_fn((i32, vint0) :: nil)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
               cs23' ++ cs24')
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2')). 
          eapply LLVMopsem.dsExCall with (fid:=ssb_fid)
            (gvs:=(bgv2 :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply ssb_is_found; eauto.
            simpl. rewrite Hgetbgv2. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2 nil
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 false c t (wrap_call v) p)::
               insn_call bid0 false attrs gsb_typ gsb_fn((i32, vint0) :: nil):: 
               insn_call eid0 false attrs gse_typ gse_fn((i32, vint0) :: nil)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2'')).
          eapply LLVMopsem.dsExCall with (fid:=sse_fid)
            (gvs:=(egv2 :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply sse_is_found; eauto.
            simpl. rewrite Hgetegv2. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (insn_call bid0 false attrs gsb_typ gsb_fn((i32, vint0) :: nil):: 
               insn_call eid0 false attrs gse_typ gse_fn((i32, vint0) :: nil)::
               insn_call fake_id true attrs dstk_typ dstk_fn nil::
               (cs23' ++ cs24'))
              tmn2' (updateAddAL _ lc2' i0 gr2) als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
            unfold LLVMopsem.returnUpdateLocals. simpl.
            rewrite J1. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (insn_call eid0 false attrs gse_typ gse_fn((i32, vint0) :: nil)::
               insn_call fake_id true attrs dstk_typ dstk_fn nil::
               (cs23' ++ cs24'))
              tmn2' (updateAddAL _ (updateAddAL _ lc2' i0 gr2) bid0 bgv2) 
              als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsExCall with (fid:=gsb_fid)
            (gvs:=(int2GV 0 :: nil))(oresult:=Some bgv2); eauto.
            eapply gsb_is_found; eauto.
              clear - Hfree2' Hgbase.
              eapply free_doesnt_change_gsb; eauto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (insn_call fake_id true attrs dstk_typ dstk_fn nil:: 
               cs23' ++ cs24')
              tmn2' (updateAddAL _ (updateAddAL _ (updateAddAL _ lc2' i0 gr2) 
                bid0 bgv2) eid0 egv2) als2'):: ECs2)
            gl2 fs2 M2''')); auto.
          eapply LLVMopsem.dsExCall with (fid:=gse_fid)
            (gvs:=(int2GV 0 :: nil))(oresult:=Some egv2); eauto.
            eapply gse_is_found; eauto.
              clear - Hfree2' Hgbound.
              eapply free_doesnt_change_gse; eauto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (cs23' ++ cs24')
              tmn2' (updateAddAL _ (updateAddAL _ (updateAddAL _ lc2' i0 gr2) 
                bid0 bgv2) eid0 egv2) als2'):: ECs2)
            gl2 fs2 M2''')); auto.
          eapply LLVMopsem.dsExCall; simpl; eauto.
            eapply dstk_is_found; eauto.
            eapply dstk_spec; eauto.

      split; auto using inject_incr_refl.
      SSSSCase "sim".
      repeat (split; auto).
          eapply cmds_at_block_tail_next; eauto.

          destruct Heqb2' as [l2' [ps2' [cs21' Heqb2']]]; subst.
          exists l2'. exists ps2'. exists (cs21' ++
              [insn_call i0 false c t (wrap_call v) p] ++
              [insn_call bid0 false attrs gsb_typ gsb_fn [(i32, vint0)]] ++
              [insn_call eid0 false attrs gse_typ gse_fn [(i32, vint0)]] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          repeat (split; auto).              
            clear - J2 Hrsim' HeqR. admit.
            clear - J2 Hrsim' HeqR Hinj1 Hinj2. admit.

    SSSCase "rt isnt ptr". 
      inv H1. inv HeqRet. inv Httmn.
      destruct (@stk_ret_sim (los,nts) Mem0 M2 mi mgb MM null null) as 
        [M2' [M2'' [Hsbase [Hsbound [Hmsim3 [Hwfmi3 [Hgbase Hgbound]]]]]]]; 
        auto.
      eapply free_allocas_sim in Hmsim3; eauto.
      destruct Hmsim3 as [M2''' [Hfree2' [Hmsim2' Hwfmi2']]].
      symmetry in Heqogr.
      eapply simulation__getOperandValue in Heqogr; eauto.
      destruct Heqogr as [gr2 [J1 J2]]. 
      exists (LLVMopsem.mkState S2 (los, nts) Ps2
        ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' 
            (updateAddAL _ (updateAddAL _ (updateAddAL _ lc2' i0 gr2) bid0 null) 
              eid0 null)
            als2'):: ECs2)
        gl2 fs2 M2''').
      exists mi.
      split.
      SSSSCase "dsop_star".
        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              ((insn_call fake_id true attrs sse_typ sse_fn 
                  ((p8, vnullp8)::(i32, vint0) :: nil))::nil)
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 false c t (wrap_call v) p)::
               insn_call bid0 false attrs gsb_typ gsb_fn((i32, vint0) :: nil):: 
               insn_call eid0 false attrs gse_typ gse_fn((i32, vint0) :: nil)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
               cs23' ++ cs24')
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2')). 
          eapply LLVMopsem.dsExCall with (fid:=ssb_fid)
            (gvs:=(null :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply ssb_is_found; eauto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2 nil
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 false c t (wrap_call v) p)::
               insn_call bid0 false attrs gsb_typ gsb_fn((i32, vint0) :: nil):: 
               insn_call eid0 false attrs gse_typ gse_fn((i32, vint0) :: nil)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2'')).
          eapply LLVMopsem.dsExCall with (fid:=sse_fid)
            (gvs:=(null :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply sse_is_found; eauto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (insn_call bid0 false attrs gsb_typ gsb_fn((i32, vint0) :: nil):: 
               insn_call eid0 false attrs gse_typ gse_fn((i32, vint0) :: nil)::
               insn_call fake_id true attrs dstk_typ dstk_fn nil::
               (cs23' ++ cs24'))
              tmn2' (updateAddAL _ lc2' i0 gr2) als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
            unfold LLVMopsem.returnUpdateLocals. simpl.
            rewrite J1. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (insn_call eid0 false attrs gse_typ gse_fn((i32, vint0) :: nil)::
               insn_call fake_id true attrs dstk_typ dstk_fn nil::
               (cs23' ++ cs24'))
              tmn2' (updateAddAL _ (updateAddAL _ lc2' i0 gr2) bid0 null) 
              als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsExCall with (fid:=gsb_fid)
            (gvs:=(int2GV 0 :: nil))(oresult:=Some null); eauto.
            eapply gsb_is_found; eauto. admit.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (insn_call fake_id true attrs dstk_typ dstk_fn nil:: 
               cs23' ++ cs24')
              tmn2' (updateAddAL _ (updateAddAL _ (updateAddAL _ lc2' i0 gr2) 
                bid0 null) eid0 null) als2'):: ECs2)
            gl2 fs2 M2''')); auto.
          eapply LLVMopsem.dsExCall with (fid:=gse_fid)
            (gvs:=(int2GV 0 :: nil))(oresult:=Some null); eauto.
            eapply gse_is_found; eauto. admit.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (cs23' ++ cs24')
              tmn2' (updateAddAL _ (updateAddAL _ (updateAddAL _ lc2' i0 gr2) 
                bid0 null) eid0 null) als2'):: ECs2)
            gl2 fs2 M2''')); auto.
          eapply LLVMopsem.dsExCall; simpl; eauto.
            eapply dstk_is_found; eauto.
            eapply dstk_spec; eauto.

      split; auto using inject_incr_refl.
      SSSSCase "sim".
      repeat (split; auto).
          eapply cmds_at_block_tail_next; eauto.

          destruct Heqb2' as [l2' [ps2' [cs21' Heqb2']]]; subst.
          exists l2'. exists ps2'. exists (cs21' ++
              [insn_call i0 false c t (wrap_call v) p] ++
              [insn_call bid0 false attrs gsb_typ gsb_fn [(i32, vint0)]] ++
              [insn_call eid0 false attrs gse_typ gse_fn [(i32, vint0)]] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          repeat (split; auto).    
            clear - J2 Hrsim' HeqR. admit.
            clear - J2 Hrsim' HeqR. admit.

    SSCase "ct isnt ptr".
      inv Hcall'.
      simpl in Httmn.
      destruct (isPointerTypB RetTy).
    SSSCase "rt is ptr". 
      inv H1.
      remember (SBopsem.get_reg_metadata (los, nts) gl2 rm Result) as oRmd.
      destruct oRmd as [[bgv1 egv1]|]; inv HeqRet.
      assert (exists bv2, exists ev2, exists bgv2, exists egv2,
        get_reg_metadata rm2 Result = Some (bv2, ev2) /\
        getOperandValue (los,nts) bv2 lc2 gl2 = Some bgv2 /\
        getOperandValue (los,nts) ev2 lc2 gl2 = Some egv2 /\
        gv_inject mi bgv1 bgv2 /\
        gv_inject mi egv1 egv2) as J.
        clear - HeqoRmd Hrsim. 
        destruct Hrsim as [_ Hrsim].
        apply Hrsim; auto.
      destruct J as [bv2 [ev2 [bgv2 [egv2 [Hgetrmd [Hgetbgv2 [Hgetegv2 [Hinj1 
        Hinj2]]]]]]]]. rewrite Hgetrmd in Httmn. inv Httmn.
      destruct (@stk_ret_sim (los,nts) Mem0 M2 mi mgb MM bgv2 egv2) as 
        [M2' [M2'' [Hsbase [Hsbound [Hmsim3 [Hwfmi3 [Hgbase Hgbound]]]]]]]; 
        auto.
      eapply free_allocas_sim in Hmsim3; eauto.
      destruct Hmsim3 as [M2''' [Hfree2' [Hmsim2' Hwfmi2']]].
      symmetry in Heqogr.
      eapply simulation__getOperandValue in Heqogr; eauto.
      destruct Heqogr as [gr2 [J1 J2]]. 
      exists (LLVMopsem.mkState S2 (los, nts) Ps2
        ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' (updateAddAL _ lc2' i0 gr2)
            als2'):: ECs2)
        gl2 fs2 M2''').
      exists mi.
      split.
      SSSSCase "dsop_star".
        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              ((insn_call fake_id true attrs sse_typ sse_fn 
                  ((p8, ev2)::(i32, vint0) :: nil))::nil)
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 false c t (wrap_call v) p)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
               cs23' ++ cs24')
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2')). 
          eapply LLVMopsem.dsExCall with (fid:=ssb_fid)
            (gvs:=(bgv2 :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply ssb_is_found; eauto.
            simpl. rewrite Hgetbgv2. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2 nil
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 false c t (wrap_call v) p)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2'')).
          eapply LLVMopsem.dsExCall with (fid:=sse_fid)
            (gvs:=(egv2 :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply sse_is_found; eauto.
            simpl. rewrite Hgetegv2. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
               (insn_call fake_id true attrs dstk_typ dstk_fn nil::
                (cs23' ++ cs24'))
              tmn2' (updateAddAL _ lc2' i0 gr2) als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
            unfold LLVMopsem.returnUpdateLocals. simpl.
            rewrite J1. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (cs23' ++ cs24')
              tmn2' (updateAddAL _ lc2' i0 gr2) als2'):: ECs2)
            gl2 fs2 M2''')); auto.
          eapply LLVMopsem.dsExCall; simpl; eauto.
            eapply dstk_is_found; eauto.
            eapply dstk_spec; eauto.

      split; auto using inject_incr_refl.
      SSSSCase "sim".
      repeat (split; auto).
          eapply cmds_at_block_tail_next; eauto.

          destruct Heqb2' as [l2' [ps2' [cs21' Heqb2']]]; subst.
          exists l2'. exists ps2'. exists (cs21' ++
              [insn_call i0 false c t (wrap_call v) p] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          apply reg_simulation__updateAddAL_lc with (i0:=i0)(gv:=ogr)(gv':=gr2) 
            in Hrsim'; auto.
            repeat (split; auto).    
            admit. admit.

    SSSCase "rt isnt ptr". 
      inv H1. inv HeqRet. inv Httmn.
      destruct (@stk_ret_sim (los,nts) Mem0 M2 mi mgb MM null null) as 
        [M2' [M2'' [Hsbase [Hsbound [Hmsim3 [Hwfmi3 [Hgbase Hgbound]]]]]]]; 
        auto.
      eapply free_allocas_sim in Hmsim3; eauto.
      destruct Hmsim3 as [M2''' [Hfree2' [Hmsim2' Hwfmi2']]].
      symmetry in Heqogr.
      eapply simulation__getOperandValue in Heqogr; eauto.
      destruct Heqogr as [gr2 [J1 J2]]. 
      exists (LLVMopsem.mkState S2 (los, nts) Ps2
        ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' (updateAddAL _ lc2' i0 gr2)
            als2'):: ECs2)
        gl2 fs2 M2''').
      exists mi.
      split.
      SSSSCase "dsop_star".
        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
              ((insn_call fake_id true attrs sse_typ sse_fn 
                  ((p8, vnullp8)::(i32, vint0) :: nil))::nil)
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 false c t (wrap_call v) p)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
               cs23' ++ cs24')
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2')). 
          eapply LLVMopsem.dsExCall with (fid:=ssb_fid)
            (gvs:=(null :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply ssb_is_found; eauto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2 nil
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 false c t (wrap_call v) p)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2'')).
          eapply LLVMopsem.dsExCall with (fid:=sse_fid)
            (gvs:=(null :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply sse_is_found; eauto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (insn_call fake_id true attrs dstk_typ dstk_fn nil::
               (cs23' ++ cs24'))
              tmn2' (updateAddAL _ lc2' i0 gr2) als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
            unfold LLVMopsem.returnUpdateLocals. simpl.
            rewrite J1. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (cs23' ++ cs24')
              tmn2' (updateAddAL _ lc2' i0 gr2) als2'):: ECs2)
            gl2 fs2 M2''')); auto.
          eapply LLVMopsem.dsExCall; simpl; eauto.
            eapply dstk_is_found; eauto.
            eapply dstk_spec; eauto.

      split; auto using inject_incr_refl.
      SSSSCase "sim".
      repeat (split; auto).
          eapply cmds_at_block_tail_next; eauto.

          destruct Heqb2' as [l2' [ps2' [cs21' Heqb2']]]; subst.
          exists l2'. exists ps2'. exists (cs21' ++
              [insn_call i0 false c t (wrap_call v) p] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          apply reg_simulation__updateAddAL_lc with (i0:=i0)(gv:=ogr)(gv':=gr2) 
            in Hrsim'; auto.
            repeat (split; auto).    
            admit. admit.
Qed.

Lemma SBpass_is_correct__dsReturnVoid : forall
  (mi : meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block)
  (rid : id) (lc : GVMap) (rm : SBopsem.rmetadata) (gl : GVMap)
  (fs : GVMap) (F' : fdef) (B' : block) (c' : cmd) (tmn' : terminator)
  (lc' : GVMap) (rm' : SBopsem.rmetadata) (EC : list SBopsem.ExecutionContext)
  (cs' : list cmd) (Mem : mem) (MM : SBopsem.mmetadata) (als : list mblock)
  (als' : list mblock)
  (Hsim : sbState_simulates_State mi mgb
           {|
           SBopsem.CurSystem := S;
           SBopsem.CurTargetData := TD;
           SBopsem.CurProducts := Ps;
           SBopsem.ECS := {|
                          SBopsem.CurFunction := F;
                          SBopsem.CurBB := B;
                          SBopsem.CurCmds := nil;
                          SBopsem.Terminator := insn_return_void rid;
                          SBopsem.Locals := lc;
                          SBopsem.Rmap := rm;
                          SBopsem.Allocas := als |}
                          :: {|
                             SBopsem.CurFunction := F';
                             SBopsem.CurBB := B';
                             SBopsem.CurCmds := c' :: cs';
                             SBopsem.Terminator := tmn';
                             SBopsem.Locals := lc';
                             SBopsem.Rmap := rm';
                             SBopsem.Allocas := als' |} :: EC;
           SBopsem.Globals := gl;
           SBopsem.FunTable := fs;
           SBopsem.Mem := Mem;
           SBopsem.Mmap := MM |} St)
  (Mem' : mem)
  (H : Instruction.isCallInst c' = true)
  (H0 : free_allocas TD Mem als = ret Mem')
  (H1 : getCallerReturnID c' = merror),
  exists St' : LLVMopsem.State,
     exists mi' : meminj,
       LLVMopsem.dsop_star St St' trace_nil /\
       sbState_simulates_State mi' mgb
         {|
         SBopsem.CurSystem := S;
         SBopsem.CurTargetData := TD;
         SBopsem.CurProducts := Ps;
         SBopsem.ECS := {|
                        SBopsem.CurFunction := F';
                        SBopsem.CurBB := B';
                        SBopsem.CurCmds := cs';
                        SBopsem.Terminator := tmn';
                        SBopsem.Locals := lc';
                        SBopsem.Rmap := rm';
                        SBopsem.Allocas := als' |} :: EC;
         SBopsem.Globals := gl;
         SBopsem.FunTable := fs;
         SBopsem.Mem := Mem';
         SBopsem.Mmap := MM |} St' /\ inject_incr mi mi'.
Proof. 
  intros.
  destruct_ctx_return.
  inv Htcmds.
  simpl in H1.
  destruct n; inv H1.
  unfold call_suffix in Hcall'. inv Hcall'.
  inv Httmn.
  eapply free_allocas_sim in HsimM; eauto.
  destruct HsimM as [M2' [Hfree2' [Hmsim2' Hwfmi2']]].
  exists (LLVMopsem.mkState S2 (los, nts) Ps2
        ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' lc2' als2'):: ECs2)
        gl2 fs2 M2').
  exists mi.
  split.
    SCase "dsop_star".
      rewrite <- (@trace_app_nil__eq__trace trace_nil).
      apply LLVMopsem.dsop_star_cons with (state2:=
        (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            ((insn_call fake_id true attrs dstk_typ dstk_fn nil)::
            (cs23' ++ cs24'))
            tmn2' lc2' als2'):: ECs2)
          gl2 fs2 M2')).
        eapply LLVMopsem.dsReturnVoid; eauto.
    
      rewrite <- (@trace_app_nil__eq__trace trace_nil).
      apply LLVMopsem.dsop_star_cons with (state2:=
        (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24')
            tmn2' lc2' als2'):: ECs2)
          gl2 fs2 M2')); auto.
        eapply LLVMopsem.dsExCall; simpl; eauto.
          eapply dstk_is_found; eauto.
          eapply dstk_spec; eauto.
    
    split; auto using inject_incr_refl.
    SSSCase "sim".
    repeat (split; auto).
        eapply cmds_at_block_tail_next; eauto.
     
        destruct Heqb2' as [l2' [ps2' [cs21' Heqb2']]]; subst.
        exists l2'. exists ps2'. exists (cs21' ++
            [insn_call i0 true c t (wrap_call v) p] ++
            [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
        simpl_env. auto.
    
        exists ex_ids'. exists rm2'.
        exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
        repeat (split; auto).
Qed.

Ltac destruct_ctx_other :=
match goal with
| [Hsim : sbState_simulates_State _ _
           {|
           SBopsem.CurSystem := _;
           SBopsem.CurTargetData := ?TD;
           SBopsem.CurProducts := _;
           SBopsem.ECS := {|
                          SBopsem.CurFunction := ?F;
                          SBopsem.CurBB := _;
                          SBopsem.CurCmds := ?c::_;
                          SBopsem.Terminator := _;
                          SBopsem.Locals := _;
                          SBopsem.Rmap := _;
                          SBopsem.Allocas := _ |} :: _;
           SBopsem.Globals := _;
           SBopsem.FunTable := _;
           SBopsem.Mem := _;
           SBopsem.Mmap := _ |} ?St |- _] =>
  destruct St as [S2 TD2 Ps2 ECs2 gl2 fs2 M2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Heq2 [Heq3 
    [Hwfg [Hwfmi HsimM]]]]]]]]]];
    subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct F as [fh1 bs1];
  destruct F2 as [fh2 bs2];
  destruct HsimEC as [HBinF [HFinPS [Htfdef [Heq0 [Hasim [Hnth [Heqb1 [Heqb2 
    [ex_ids [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [Hgenmeta [Hrsim [Hinc [Hfresh 
    [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]; subst
end.

Lemma lookup_trans_blocks__trans_block : forall ex_ids0 l0 rm b1 bs1 bs2 ex_ids 
    ex_ids',
  uniqBlocks bs1 ->
  incl ex_ids0 ex_ids ->
  trans_blocks ex_ids rm bs1 = Some (ex_ids', bs2) ->
  lookupBlockViaLabelFromBlocks bs1 l0 = Some b1 ->
  exists ex_ids1, exists ex_ids2, exists b2, exists n,
    lookupBlockViaLabelFromBlocks bs2 l0 = Some b2 /\
    trans_block ex_ids1 rm b1 = Some (ex_ids2, b2) /\
    incl ex_ids0 ex_ids1 /\
    nth_error bs1 n = Some b1 /\
    nth_error bs2 n = Some b2.
Proof.
  induction bs1; simpl; intros bs2 ex_ids ex_ids' Huniq Hinc Htrans Hlk.
    inv Hlk.
Admitted.


Ltac destruct_ctx_br :=
match goal with
| [Hsim : sbState_simulates_State _ _
           {|
           SBopsem.CurSystem := _;
           SBopsem.CurTargetData := ?TD;
           SBopsem.CurProducts := _;
           SBopsem.ECS := {|
                          SBopsem.CurFunction := ?F;
                          SBopsem.CurBB := _;
                          SBopsem.CurCmds := nil;
                          SBopsem.Terminator := _;
                          SBopsem.Locals := _;
                          SBopsem.Rmap := _;
                          SBopsem.Allocas := _ |} :: _;
           SBopsem.Globals := _;
           SBopsem.FunTable := _;
           SBopsem.Mem := _;
           SBopsem.Mmap := _ |} ?St |- _] =>
  destruct St as [S2 TD2 Ps2 ECs2 gl2 fs2 M2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Heq2 [Heq3 [Hwfg 
    [Hwfmi HsimM]]]]]]]]]];
    subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct F as [fh1 bs1];
  destruct F2 as [fh2 bs2];
  destruct HsimEC as [HBinF [HFinPs [Htfdef [Heq0 [Hasim [Hnth [Heqb1 [Heqb2 
    [ex_ids [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [Hgenmeta [Hrsim [Hinc [Hfresh 
    [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]; subst
end.

Lemma SBpass_is_correct__dsBranch_uncond : forall
  (mi : meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : GVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (bid : id) (l0 : l)
  (EC : list ExecutionContext) (Mem0 : mem) (MM : mmetadata) (als : list mblock)
  (Hsim : sbState_simulates_State mi mgb
           {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := nil;
                  Terminator := insn_br_uncond bid l0;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Globals := gl;
           FunTable := fs;
           Mem := Mem0;
           Mmap := MM |} St)
  (l' : l) (ps' : phinodes) (cs' : cmds) (tmn' : terminator) (lc' : GVMap)
  (rm' : rmetadata) 
  (H : ret block_intro l' ps' cs' tmn' = lookupBlockViaLabelFromFdef F l0)
  (H0 : switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc rm =
       ret (lc', rm')),
   exists St' : LLVMopsem.State,
     exists mi' : meminj,
       LLVMopsem.dsop_star St St' trace_nil /\
       sbState_simulates_State mi' mgb
         {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         ECS := {|
                CurFunction := F;
                CurBB := block_intro l' ps' cs' tmn';
                CurCmds := cs';
                Terminator := tmn';
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: EC;
         Globals := gl;
         FunTable := fs;
         Mem := Mem0;
         Mmap := MM |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_br.
  simpl in Hfresh. destruct Hfresh as [Hnotin Hfresh].
  inv Htcmds. inv Httmn.

  assert (HuniqF:=HFinPs).
  eapply wf_system__uniqFdef in HuniqF; eauto.
  destruct fh1. destruct HuniqF as [HuniqBlocks HuniqArgs].
  destruct Hnth as [n [Hnth1 Hth2]].
  simpl in H. symmetry in H.
  assert (Htfdef':=Htfdef). simpl in Htfdef.  
  destruct (isCallLib i0). admit. (* we should rule out the case *)
  simpl in Hgenmeta.
  rewrite Hgenmeta in Htfdef.

  remember (trans_args rm2 a 1 nil) as R1. 
  destruct R1; try solve [inversion Htfdef].
  remember (trans_blocks ex_ids rm2 bs1) as R2.
  destruct R2 as [[ex_ids' bs']|]; try solve [inversion Htfdef].
  destruct bs'; try solve [inversion Htfdef]. 
  destruct b; inv Htfdef.

  symmetry in HeqR2.
  eapply lookup_trans_blocks__trans_block with (ex_ids0:=ex_ids) in HeqR2; 
    eauto using incl_refl.
  destruct HeqR2 as [ex_ids1 [ex_ids2 [b2' [n' [Hlk' [Htblock [Hinc' [Hnth1' 
    Hnth2']]]]]]]].
  simpl in Htblock.

  remember (trans_phinodes rm2 ps') as R1.
  destruct R1 as [ps2|]; try solve [inversion Htblock].
  remember (trans_cmds ex_ids1 rm2 cs') as R2.
  destruct R2 as [[ex_ids2' cs2]|]; try solve [inversion Htblock].
  remember (trans_terminator rm2 tmn') as R3.
  destruct R3 as [cs|]; inv Htblock.

  assert (exists lc2', LLVMopsem.switchToNewBasicBlock (los,nts) 
    (block_intro l' ps2 (cs2 ++ cs) tmn') B2 gl2 lc2 = Some lc2' /\
    reg_simulation mi (los, nts) gl2
            (fdef_intro (fheader_intro f t i0 a v) bs1) rm' rm2 lc' lc2') 
    as Hswitch2.
    admit.
  destruct Hswitch2 as [lc2' [Hswitch2 Hrsim']].
  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC 
            (fdef_intro (fheader_intro f t (wrapper_fid i0) a v)
               (block_intro l1 p (c ++ c0) t0 :: bs'))
            (block_intro l' ps2 (cs2 ++ cs) tmn')
            (cs2 ++ cs) tmn' lc2' als2):: 
            ECs2) gl2 fs2 M2).
  exists mi.
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    eapply LLVMopsem.dsop_star_cons; eauto.
      eapply LLVMopsem.dsBranch_uncond; eauto.
        simpl. unfold lookupBlockViaLabelFromBlocks in Hlk'.
        simpl in Hlk'. auto.
        admit. (* cannot jmp to entry blk *)

  repeat (split; auto).
    simpl. eapply nth_error__InBlocksB; eauto.
    exists n'. split; auto.
    admit. (* cannot jmp to entry blk *)
    exists l'. exists ps'. exists nil. auto.
    exists l'. exists ps2. exists nil. auto.
    exists ex_ids. exists rm2. exists ex_ids1. exists ex_ids2. exists cs2.
    exists cs. 
    repeat (split; auto).
      admit. (* we do not need this fresh. *)
Qed.

Lemma SBpass_is_correct__dsExCall : forall (mi : meminj) 
  (mgb : Values.block)
  (St : LLVMopsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : GVMap) (rm : SBopsem.rmetadata) (gl : GVMap)
  (fs : GVMap) rid noret0 ca ft fv lp
  (EC : list SBopsem.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem0 : mem) (MM : SBopsem.mmetadata) (als : list mblock)
  (Hsim : sbState_simulates_State mi mgb
           {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_call rid noret0 ca ft fv lp :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Globals := gl;
           FunTable := fs;
           Mem := Mem0;
           Mmap := MM |} St)
  (fid : id) (rt : typ) (fa : fnattrs) (la : args) (va : varg)
  (oresult : monad GenericValue) (Mem' : mem) (lc' : GVMap)
  (rm' : rmetadata) (gvs : list GenericValue) 
  (H : lookupExFdecViaGV TD Ps gl lc fs fv =
      ret fdec_intro (fheader_intro fa rt fid la va))
  (H0 : LLVMgv.params2GVs TD lp lc gl = ret gvs)
  (H1 : callExternalFunction Mem0 fid gvs = ret (oresult, Mem'))
  (H2 : exCallUpdateLocals ft noret0 rid oresult lc rm = ret (lc', rm')),
   exists St' : LLVMopsem.State,
     exists mi' : meminj,
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
         Mem := Mem';
         Mmap := MM |} St' /\ inject_incr mi mi'.
Admitted.

Lemma SBpass_is_correct__dsBranch : forall
  (mi : meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : GVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (bid : id) (Cond : value)
  (l1 : l) (l2 : l) (EC : list ExecutionContext) (Mem0 : mem) (MM : mmetadata)
  (als : list mblock)
  (Hsim : sbState_simulates_State mi mgb
           {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := nil;
                  Terminator := insn_br bid Cond l1 l2;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Globals := gl;
           FunTable := fs;
           Mem := Mem0;
           Mmap := MM |} St)
  (c : GenericValue)
  (l' : l)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  (lc' : GVMap)
  (rm' : rmetadata)
  (H : getOperandValue TD Cond lc gl = ret c)
  (H0 : ret block_intro l' ps' cs' tmn' =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1))
  (H1 : switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc rm =
       ret (lc', rm')),
   exists St' : LLVMopsem.State,
     exists mi' : meminj,
       LLVMopsem.dsop_star St St' trace_nil /\
       sbState_simulates_State mi' mgb
         {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         ECS := {|
                CurFunction := F;
                CurBB := block_intro l' ps' cs' tmn';
                CurCmds := cs';
                Terminator := tmn';
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: EC;
         Globals := gl;
         FunTable := fs;
         Mem := Mem0;
         Mmap := MM |} St' /\ inject_incr mi mi'.
Admitted.

Lemma SBpass_is_correct__dsCall : forall (mi : meminj) 
  (mgb : Values.block)
  (St : LLVMopsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : GVMap) (rm : SBopsem.rmetadata) (gl : GVMap)
  (fs : GVMap) rid noret0 ca ft fv lp
  (EC : list SBopsem.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem0 : mem) (MM : SBopsem.mmetadata) (als : list mblock)
  (Hsim : sbState_simulates_State mi mgb
           {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_call rid noret0 ca ft fv lp :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Globals := gl;
           FunTable := fs;
           Mem := Mem0;
           Mmap := MM |} St)
  (fid : id) (ogvs : list (GenericValue * monad metadata)) 
  (l' : l) (ps' : phinodes) (cs' : cmds) (tmn' : terminator) (fa : fnattrs)
  (rt : typ) (la : args) (va : varg) (lb : blocks) (rm' : rmetadata)
  (lc' : GVMap)
  (H : lookupFdefViaGV TD Ps gl lc fs fv =
      ret fdef_intro (fheader_intro fa rt fid la va) lb)
  (H0 : getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) =
       ret block_intro l' ps' cs' tmn')
  (H1 : params2GVs TD lp lc gl rm = ret ogvs)
  (H2 : initLocals la ogvs rm = (lc', rm')),
   exists St' : LLVMopsem.State,
     exists mi' : meminj,
       LLVMopsem.dsop_star St St' trace_nil /\
       sbState_simulates_State mi' mgb
         {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         ECS := {|
                CurFunction := fdef_intro (fheader_intro fa rt fid la va) lb;
                CurBB := block_intro l' ps' cs' tmn';
                CurCmds := cs';
                Terminator := tmn';
                Locals := lc';
                Rmap := rm';
                Allocas := nil |}
                :: {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := insn_call rid noret0 ca ft fv lp :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Rmap := rm;
                   Allocas := als |} :: EC;
         Globals := gl;
         FunTable := fs;
         Mem := Mem0;
         Mmap := MM |} St' /\ inject_incr mi mi'.
Admitted.

Lemma SBpass_is_correct : forall mi mgb sbSt St sbSt' tr,
  sbState_simulates_State mi mgb sbSt St ->
  SBopsem.dsInsn sbSt sbSt' tr -> 
  exists St', exists mi',
    LLVMopsem.dsop_star St St' tr /\    
    sbState_simulates_State mi' mgb sbSt' St' /\
    Values.inject_incr mi mi'.
Proof.
  intros mi mgb sbSt St sbSt' tr Hsim Hsbop.
  (sb_dsInsn_cases (induction Hsbop) Case).
Case "dsReturn". eapply SBpass_is_correct__dsReturn; eauto.
Case "dsReturnVoid". eapply SBpass_is_correct__dsReturnVoid; eauto.
Case "dsBranch".  eapply SBpass_is_correct__dsBranch; eauto.
Case "dsBranch_uncond". eapply SBpass_is_correct__dsBranch_uncond; eauto.
Case "dsBop". eapply SBpass_is_correct__dsBop; eauto.
Case "dsFBop". eapply SBpass_is_correct__dsFBop; eauto.
Case "dsExtractValue". eapply SBpass_is_correct__dsExtractValue; eauto.
Case "dsInsertValue". eapply SBpass_is_correct__dsInsertValue; eauto.
Case "dsMalloc". eapply SBpass_is_correct__dsMalloc; eauto.
Case "dsFree". eapply SBpass_is_correct__dsFree; eauto.
Case "dsAlloca". eapply SBpass_is_correct__dsAlloca; eauto.
Case "dsLoad_nptr". eapply SBpass_is_correct__dsLoad_nptr; eauto.
Case "dsLoad_ptr". eapply SBpass_is_correct__dsLoad_ptr; eauto.
Case "dsStore_nptr". eapply SBpass_is_correct__dsStore_nptr; eauto.
Case "dsStore_ptr". eapply SBpass_is_correct__dsStore_ptr; eauto.
Case "dsGEP". eapply SBpass_is_correct__dsGEP; eauto.
Case "dsTrunc". eapply SBpass_is_correct__dsTrunc; eauto.
Case "dsExt". eapply SBpass_is_correct__dsExt; eauto.
Case "dsBitcast_nptr". eapply SBpass_is_correct__dsBitcase_nptr; eauto.
Case "dsBitcast_ptr". eapply SBpass_is_correct__dsBitcase_ptr; eauto.
Case "dsInttoptr". eapply SBpass_is_correct__dsInttoptr; eauto.
Case "dsOthercast". eapply SBpass_is_correct__dsOthercast; eauto.
Case "dsIcmp". eapply SBpass_is_correct__dsIcmp; eauto.
Case "dsFcmp". eapply SBpass_is_correct__dsFcmp; eauto.
Case "dsSelect_nptr". eapply SBpass_is_correct__dsSelect_nptr; eauto.
Case "dsSelect_ptr". eapply SBpass_is_correct__dsSelect_ptr; eauto.
Case "dsCall".  eapply SBpass_is_correct__dsCall; eauto.
Case "dsExCall". eapply SBpass_is_correct__dsExCall; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)


