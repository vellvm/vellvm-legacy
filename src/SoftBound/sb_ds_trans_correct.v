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

Lemma SBpass_is_correct__dsBop : forall (mi : meminj) (mgb : Values.block)
  (St : LLVMopsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : GVMap) (rm : SBopsem.rmetadata) (gl : GVMap)
  (fs : GVMap) (id0 : id) (bop0 : bop) (sz0 : sz) (v1 : value) (v2 : value)
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
                          SBopsem.CurCmds := insn_bop id0 bop0 sz0 v1 v2
                                             :: cs;
                          SBopsem.Terminator := tmn;
                          SBopsem.Locals := lc;
                          SBopsem.Rmap := rm;
                          SBopsem.Allocas := als |} :: EC;
           SBopsem.Globals := gl;
           SBopsem.FunTable := fs;
           SBopsem.Mem := Mem;
           SBopsem.Mmap := MM |} St)
  (gv3 : GenericValue)
  (H : BOP TD lc gl bop0 sz0 v1 v2 = ret gv3),
  exists St' : LLVMopsem.State,
     exists mi' : meminj,
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
                        SBopsem.Locals := updateAddAL GenericValue lc id0 gv3;
                        SBopsem.Rmap := rm;
                        SBopsem.Allocas := als |} :: EC;
         SBopsem.Globals := gl;
         SBopsem.FunTable := fs;
         SBopsem.Mem := Mem;
         SBopsem.Mmap := MM |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  simpl in Htcmds.
  remember (trans_cmds ex_ids3 rm2 cs) as R.
  destruct R as [[ex_ids2 cs2]|]; inv Htcmds.
  eapply simulation__BOP in H; eauto.
  destruct H as [gv3' [Hbop Hinj]].
  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2 ++ cs23) tmn2 (updateAddAL GenericValue lc2 id0 gv3') als2):: 
            ECs2) gl2 fs2 M2).
  exists mi.
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    eapply LLVMopsem.dsop_star_cons; eauto.
      apply LLVMopsem.dsBop; auto.

    split; auto using inject_incr_refl.
    repeat (split; auto).
      eapply cmds_at_block_tail_next; eauto.
      eapply cmds_at_block_tail_next; eauto.

      exists ex_ids. exists rm2.
      exists ex_ids3. exists ex_ids4. exists cs2. exists cs23.
      simpl in Hfresh. destruct Hfresh as [Hfresh1 Hfresh2].
      split; auto.
      split.
        clear - Hfresh1 Hrsim Hinj.
        destruct Hfresh1 as [Hnotin _]. 
        unfold getCmdIDs in Hnotin. simpl in Hnotin.
        apply reg_simulation__updateAddAL_lc; try solve [auto | fsetdec].
          admit.
      repeat (split; auto).
Qed.

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
     exists mi' : meminj,
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
  simpl in Hfresh. destruct Hfresh as [Hnotin Hfresh].
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd.
  remember (lookupAL (id * id) rm2 id0) as R1.
  destruct R1 as [[bid eid]|]; try solve [inversion Htcmd].
  remember (mk_tmp ex_ids3) as R2.
  destruct R2 as [tmp ex_ids6].
  inv Htcmd.
  invert_prop_reg_metadata.
  assert (Hmalloc:=H1).
  apply mem_simulation__malloc with (MM:=MM)(mgb:=mgb)(Mem2:=M2)(mi:=mi) in H1;
    auto.
  destruct H1 as [mi' [Mem2' [mb' [H11 [H16 [H12 [H13 [H14 H15]]]]]]]].
  simpl.
  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
                (updateAddAL _ 
                  (updateAddAL _ 
                    (updateAddAL _ 
                      (updateAddAL GenericValue lc2 id0 (blk2GV (los, nts) mb'))
                      tmp (SBopsem.bound2GV (los, nts) mb' tsz n))
                    bid (SBopsem.base2GV (los, nts) mb'))
                  eid (SBopsem.bound2GV (los, nts) mb' tsz n))
             als2):: 
            ECs2) gl2 fs2 Mem2').
  exists mi'.
  split.
  SCase "opsem".
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
        LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
             (insn_gep tmp false t (value_id id0) 
                (Cons_list_value v Nil_list_value):: 
              insn_cast bid castop_bitcast (typ_pointer t)(value_id id0) p8 :: 
              insn_cast eid castop_bitcast (typ_pointer t)(value_id tmp) p8 :: 
              cs2' ++ cs23)
             tmn2 
             (updateAddAL GenericValue lc2 id0 (blk2GV (los, nts) mb'))
             als2):: 
            ECs2) gl2 fs2 Mem2'); auto.
      eapply simulation__getOperandValue with (mi:=mi)(Mem2:=M2) in H0; eauto.
      destruct H0 as [gn' [H00 H01]].
      unfold malloc in H11.
      erewrite simulation__eq__GV2int in H11; eauto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
        LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
             (insn_cast bid castop_bitcast (typ_pointer t)(value_id id0) p8 :: 
              insn_cast eid castop_bitcast (typ_pointer t)(value_id tmp) p8 :: 
              cs2' ++ cs23)
             tmn2 
             (updateAddAL _
               (updateAddAL GenericValue lc2 id0 (blk2GV (los,nts) mb'))
               tmp (SBopsem.bound2GV (los,nts) mb' tsz n))
             als2):: 
            ECs2) gl2 fs2 Mem2'); auto.
      assert (exists gn', getOperandValue (los,nts) v lc2 gl2 = ret gn' /\
          GV2int (los,nts) Size.ThirtyTwo gn = 
          GV2int (los,nts) Size.ThirtyTwo gn') as H4.
        eapply simulation__getOperandValue with (Mem2:=M2) in H0; eauto.
        destruct H0 as [gv' [H00 H01]].
        exists gv'. split; auto.
          rewrite simulation__eq__GV2int with (mi:=mi)(gn':=gv'); eauto.
      destruct H4 as [gn' [H41 H42]].
      apply LLVMopsem.dsGEP with (mp:=blk2GV (los,nts) mb')(vidxs:=[gn']); auto.
        simpl.
        rewrite lookupAL_updateAddAL_eq; auto.

        simpl.
        assert(getOperandValue (los,nts) v
          (updateAddAL _ lc2 id0 (blk2GV (los,nts) mb')) gl2 = 
          getOperandValue (los,nts) v lc2 gl2) as EQ'.
          clear - Hnotin HeqR1. 
          destruct Hnotin as [Hnotin1 [Hnotin2 _ ]]. simpl in Hnotin2.

          rewrite <- getOperandValue_eq_fresh_id; auto.
            unfold getCmdIDs in Hnotin1. simpl in Hnotin1.
            eapply notin_codom__neq' in HeqR1; eauto.
              destruct v; simpl in *; fsetdec.

        rewrite EQ'. clear EQ'.
        rewrite H41. auto.

        unfold SBopsem.bound2GV, GEP, blk2GV, GV2ptr, ptr2GV, val2GV.
        simpl.
        rewrite <- H42. rewrite H2.
        unfold Constant.typ2utyp.
        assert (exists ut, 
          Constant.typ2utyp_aux (Constant.subst_nts_by_nts nts nts) 
            (typ_array 0%nat t) = Some (typ_array 0%nat ut) /\
          getTypeAllocSize (los, nts) ut = getTypeAllocSize (los, nts) t) as EQ1.
          destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
          eapply wf_system__wf_cmd with (c:=insn_malloc id0 t v align0) in HBinF;
            eauto.
            inv HBinF. inv H21. 
            (* ssa_static should check this typ is Constant.unifiable_typ
               like wf_const_gid *)
            admit.

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
                 (updateAddAL GenericValue lc2 id0 (blk2GV (los,nts) mb'))
                 tmp (SBopsem.bound2GV (los,nts) mb' tsz n))
               bid (SBopsem.base2GV (los,nts) mb'))               
             als2):: 
            ECs2) gl2 fs2 Mem2'); auto.
      apply LLVMopsem.dsCast; auto.
        unfold CAST. simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq.
          auto.

          clear - Hnotin HeqR1 HeqR2.
          destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]]. 
          unfold getCmdIDs in *. simpl in *.
          eapply tmp_is_fresh; eauto. fsetdec.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
       (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
                (updateAddAL _ 
                  (updateAddAL _ 
                    (updateAddAL _ 
                      (updateAddAL GenericValue lc2 id0 (blk2GV (los, nts) mb'))
                      tmp (SBopsem.bound2GV (los, nts) mb' tsz n))
                    bid (SBopsem.base2GV (los, nts) mb'))                    
                  eid (SBopsem.bound2GV (los, nts) mb' tsz n))
             als2):: 
            ECs2) gl2 fs2 Mem2')); auto.
      apply LLVMopsem.dsCast; auto.
        unfold CAST. simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.

          destruct Hnotin as [Hnotin1 [Hnotin2 [Hnotin3 Hnotin4]]]. 
          unfold getCmdIDs in *.
          eapply tmp_is_fresh' with (tmp:=tmp) in HeqR1; eauto. 
            destruct HeqR1; auto.
            clear - Hnotin3. fsetdec.

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
  split; eauto using inject_incr__preserves__als_simulation.
  split; auto.
  split.
    eapply cmds_at_block_tail_next; eauto.
  split.
    destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
    exists l2. exists ps2. exists (cs21 ++
                  (insn_malloc id0 t v align0
                    :: insn_gep tmp false t (value_id id0)
                         (Cons_list_value v Nil_list_value)
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
      eapply reg_simulation__updateAddAL_tmp; eauto.
      eapply reg_simulation__updateAddAL_lc; eauto.
        eapply inject_incr__preserves__reg_simulation; eauto.
        admit.
        admit.

      unfold gv_inject, blk2GV, ptr2GV, val2GV.
      simpl. apply val_cons_inject; eauto.

      unfold gv_inject, SBopsem.base2GV, blk2GV, ptr2GV, val2GV.
      simpl. clear - H14.
      apply val_cons_inject; eauto.

      unfold gv_inject, SBopsem.base2GV, blk2GV, ptr2GV, val2GV.
      simpl. clear - H14.
        apply val_cons_inject; eauto.
          eapply val_inject_ptr; eauto.
            rewrite Int.add_zero. auto.

    split; auto.
      clear - Hinc HeqR2. eapply mk_tmp_inc; eauto.
    split; auto.
      clear - Hinc HeqR2 Hfresh. eapply wf_freshs__mk_tmp; eauto.
      
      clear - HsimECs H13. 
      eapply inject_incr__preserves__sbECs_simulate_ECs_tail; eauto.
Qed.

Lemma SBpass_is_correct__dsFree : forall (mi : meminj) (mgb : Values.block)
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
  simpl in Hfresh. destruct Hfresh as [Hnotin Hfresh].
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
  split; auto.
Qed.

Lemma SBpass_is_correct__dsLoad_nptr : forall 
  (mi : meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
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
  simpl in Hfresh. destruct Hfresh as [Hnotin Hfresh].
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
        clear - J1 Hnotin HeqR1 HeqR2 HeqR3 H00.
        destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]].
        unfold getCmdIDs in *. simpl in *.
        rewrite <- getOperandValue_eq_fresh_id; auto.
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
      admit.
      admit.

    split; auto.
      clear - Hinc HeqR1. eapply mk_tmp_inc; eauto.
    split; auto.
      clear - Hinc HeqR1 Hfresh. eapply wf_freshs__mk_tmp; eauto.
Qed.

Lemma SBpass_is_correct__dsLoad_ptr : forall 
  (mi : meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
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
         Mem := Mem0;
         Mmap := MM |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  simpl in Hfresh. destruct Hfresh as [Hnotin Hfresh].
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
  assert (getOperandValue (los, nts) (value_id ptmp) 
      (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) id0 gv2) gl2 = ret gvp2) as K.
    destruct Hnotin as [Hnotin1 [Hnotin2 [Hnotin3 Hnotin4]]]. 
    simpl.
    rewrite <- lookupAL_updateAddAL_neq; auto.
      rewrite lookupAL_updateAddAL_eq; auto.
      unfold getCmdIDs in Hnotin3. simpl in Hnotin3.
      eapply tmp_is_fresh with (i0:=id0) in HeqR1; eauto. clear. fsetdec.

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
        clear - J1 Hnotin HeqR1 HeqR2 HeqR3 H00.
        destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]].
        unfold getCmdIDs in *. simpl in *.
        rewrite <- getOperandValue_eq_fresh_id; auto.
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
      admit.
      admit.
    split; auto.
      clear - Hinc HeqR1. eapply mk_tmp_inc; eauto.
    split; auto.
      clear - Hinc HeqR1 Hfresh. eapply wf_freshs__mk_tmp; eauto.
Qed.

Lemma SBpass_is_correct__dsStore_nptr : forall 
  (mi : meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
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
  simpl in Hfresh. destruct Hfresh as [Hnotin Hfresh].
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
      apply LLVMopsem.dsStore with (mp2:=gvp2)(gv1:=gv2); auto.
        clear - Hnotin HeqR1 HeqR2 HeqR3 H00.
        destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]].
        unfold getCmdIDs in *. simpl in *.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

        clear - Hnotin HeqR1 HeqR2 HeqR3 H10.
        destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]].
        unfold getCmdIDs in *. simpl in *.
        rewrite <- getOperandValue_eq_fresh_id; auto.
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
      clear - Hinc HeqR1 Hfresh. eapply wf_freshs__mk_tmp; eauto.
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

Lemma SBpass_is_correct__dsStore_ptr : forall (mi : meminj) (mgb : Values.block)
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
  simpl in Hfresh. destruct Hfresh as [Hnotin Hfresh].
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

      clear - J2' H31 J1' Hnotin HeqR1 HeqR2 HeqR3.
      rewrite <- getOperandValue_eq_fresh_id; eauto.
        eapply get_reg_metadata__fresh with (rm2:=rm2)
          (c:=insn_store sid t v vp align0) in J1'; 
          eauto; try fsetdec. destruct J1'; auto.

      clear - J3' H31 J1' Hnotin HeqR1 HeqR2 HeqR3.
      rewrite <- getOperandValue_eq_fresh_id; eauto.
        eapply get_reg_metadata__fresh with (rm2:=rm2)
          (c:=insn_store sid t v vp align0) in J1'; 
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
      apply LLVMopsem.dsStore with (mp2:=gvp2)(gv1:=gv2); auto.
        clear - Hnotin HeqR1 HeqR2 HeqR3 H00.
        destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]].
        unfold getCmdIDs in *. simpl in *.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

        clear - Hnotin HeqR1 HeqR2 HeqR3 H10.
        destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]].
        unfold getCmdIDs in *. simpl in *.
        rewrite <- getOperandValue_eq_fresh_id; auto.
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
      clear - Hinc HeqR1 Hfresh. eapply wf_freshs__mk_tmp; eauto.
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


Lemma SBpass_is_correct__dsAlloca : forall 
  (mi : meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
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
                Allocas := mb :: als |} :: EC;
         Globals := gl;
         FunTable := fs;
         Mem := Mem';
         Mmap := MM |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  simpl in Hfresh. destruct Hfresh as [Hnotin Hfresh].
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd.
  remember (lookupAL (id * id) rm2 id0) as R1.
  destruct R1 as [[bid eid]|]; try solve [inversion Htcmd].
  remember (mk_tmp ex_ids3) as R2.
  destruct R2 as [tmp ex_ids6].
  inv Htcmd.
  invert_prop_reg_metadata.
  assert (Hmalloc:=H1).
  apply mem_simulation__malloc with (MM:=MM)(mgb:=mgb)(Mem2:=M2)(mi:=mi) in H1;
    auto.
  destruct H1 as [mi' [Mem2' [mb' [H11 [H16 [H12 [H13 [H14 H15]]]]]]]].
  simpl.
  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
                (updateAddAL _ 
                  (updateAddAL _ 
                    (updateAddAL _ 
                      (updateAddAL GenericValue lc2 id0 (blk2GV (los, nts) mb'))
                      tmp (SBopsem.bound2GV (los, nts) mb' tsz n))
                    bid (SBopsem.base2GV (los, nts) mb'))
                  eid (SBopsem.bound2GV (los, nts) mb' tsz n))
             (mb'::als2)):: 
            ECs2) gl2 fs2 Mem2').
  exists mi'.
  split.
  SCase "opsem".
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
        LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
             (insn_gep tmp false t (value_id id0) 
                (Cons_list_value v Nil_list_value):: 
              insn_cast bid castop_bitcast (typ_pointer t)(value_id id0) p8 :: 
              insn_cast eid castop_bitcast (typ_pointer t)(value_id tmp) p8 :: 
              cs2' ++ cs23)
             tmn2 
             (updateAddAL GenericValue lc2 id0 (blk2GV (los, nts) mb'))
             (mb'::als2)):: 
            ECs2) gl2 fs2 Mem2'); auto.
      eapply simulation__getOperandValue with (mi:=mi)(Mem2:=M2) in H0; eauto.
      destruct H0 as [gn' [H00 H01]].
      unfold malloc in H11.
      erewrite simulation__eq__GV2int in H11; eauto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
        LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
             (insn_cast bid castop_bitcast (typ_pointer t)(value_id id0) p8 :: 
              insn_cast eid castop_bitcast (typ_pointer t)(value_id tmp) p8 :: 
              cs2' ++ cs23)
             tmn2 
             (updateAddAL _
               (updateAddAL GenericValue lc2 id0 (blk2GV (los,nts) mb'))
               tmp (SBopsem.bound2GV (los,nts) mb' tsz n))
             (mb'::als2)):: 
            ECs2) gl2 fs2 Mem2'); auto.
      assert (exists gn', getOperandValue (los,nts) v lc2 gl2 = ret gn' /\
          GV2int (los,nts) Size.ThirtyTwo gn = 
          GV2int (los,nts) Size.ThirtyTwo gn') as H4.
        eapply simulation__getOperandValue with (Mem2:=M2) in H0; eauto.
        destruct H0 as [gv' [H00 H01]].
        exists gv'. split; auto.
          rewrite simulation__eq__GV2int with (mi:=mi)(gn':=gv'); eauto.
      destruct H4 as [gn' [H41 H42]].
      apply LLVMopsem.dsGEP with (mp:=blk2GV (los,nts) mb')(vidxs:=[gn']); auto.
        simpl.
        rewrite lookupAL_updateAddAL_eq; auto.

        simpl.
        assert(getOperandValue (los,nts) v
          (updateAddAL _ lc2 id0 (blk2GV (los,nts) mb')) gl2 = 
          getOperandValue (los,nts) v lc2 gl2) as EQ'.
          clear - Hnotin HeqR1. 
          destruct Hnotin as [Hnotin1 [Hnotin2 _ ]]. simpl in Hnotin2.

          rewrite <- getOperandValue_eq_fresh_id; auto.
            unfold getCmdIDs in Hnotin1. simpl in Hnotin1.
            eapply notin_codom__neq' in HeqR1; eauto.
              destruct v; simpl in *; fsetdec.

        rewrite EQ'. clear EQ'.
        rewrite H41. auto.

        unfold SBopsem.bound2GV, GEP, blk2GV, GV2ptr, ptr2GV, val2GV.
        simpl.
        rewrite <- H42. rewrite H2.
        unfold Constant.typ2utyp.
        assert (exists ut, 
          Constant.typ2utyp_aux (Constant.subst_nts_by_nts nts nts) 
            (typ_array 0%nat t) = Some (typ_array 0%nat ut) /\
          getTypeAllocSize (los, nts) ut = getTypeAllocSize (los, nts) t) as EQ1.
          destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
          eapply wf_system__wf_cmd with (c:=insn_alloca id0 t v align0) in HBinF;
            eauto.
            inv HBinF. inv H21. 
            (* ssa_static should check this typ is Constant.unifiable_typ
               like wf_const_gid *)
            admit.
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
                 (updateAddAL GenericValue lc2 id0 (blk2GV (los,nts) mb'))
                 tmp (SBopsem.bound2GV (los,nts) mb' tsz n))
               bid (SBopsem.base2GV (los,nts) mb'))               
             (mb'::als2)):: 
            ECs2) gl2 fs2 Mem2'); auto.
      apply LLVMopsem.dsCast; auto.
        unfold CAST. simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq.
          auto.

          clear - Hnotin HeqR1 HeqR2.
          destruct Hnotin as [Hnotin1 [_ [Hnotin2 _]]]. 
          unfold getCmdIDs in *. simpl in *.
          eapply tmp_is_fresh; eauto. fsetdec.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply LLVMopsem.dsop_star_cons with (state2:=
       (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
                (updateAddAL _ 
                  (updateAddAL _ 
                    (updateAddAL _ 
                      (updateAddAL GenericValue lc2 id0 (blk2GV (los, nts) mb'))
                      tmp (SBopsem.bound2GV (los, nts) mb' tsz n))
                    bid (SBopsem.base2GV (los, nts) mb'))                    
                  eid (SBopsem.bound2GV (los, nts) mb' tsz n))
             (mb'::als2)):: 
            ECs2) gl2 fs2 Mem2')); auto.
      apply LLVMopsem.dsCast; auto.
        unfold CAST. simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.

          destruct Hnotin as [Hnotin1 [Hnotin2 [Hnotin3 Hnotin4]]]. 
          unfold getCmdIDs in *.
          eapply tmp_is_fresh' with (tmp:=tmp) in HeqR1; eauto. 
            destruct HeqR1; auto.
            clear - Hnotin3. fsetdec.

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
  split; auto.          
    eapply cmds_at_block_tail_next; eauto.
  split.
    destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
    exists l2. exists ps2. exists (cs21 ++
                  (insn_alloca id0 t v align0
                    :: insn_gep tmp false t (value_id id0)
                         (Cons_list_value v Nil_list_value)
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
      eapply reg_simulation__updateAddAL_tmp; eauto.
      eapply reg_simulation__updateAddAL_lc; eauto.
        eapply inject_incr__preserves__reg_simulation; eauto.
        admit.
        admit.

      unfold gv_inject, blk2GV, ptr2GV, val2GV.
      simpl. apply val_cons_inject; eauto.

      unfold gv_inject, SBopsem.base2GV, blk2GV, ptr2GV, val2GV.
      simpl. clear - H14.
      apply val_cons_inject; eauto.

      unfold gv_inject, SBopsem.base2GV, blk2GV, ptr2GV, val2GV.
      simpl. clear - H14.
        apply val_cons_inject; eauto.
          eapply val_inject_ptr; eauto.
            rewrite Int.add_zero. auto.

    split; auto.
      clear - Hinc HeqR2. eapply mk_tmp_inc; eauto.
    split; auto.
      clear - Hinc HeqR2 Hfresh. eapply wf_freshs__mk_tmp; eauto.
      
      clear - HsimECs H13. 
      eapply inject_incr__preserves__sbECs_simulate_ECs_tail; eauto.
Qed.

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
Case "dsBranch". admit.
Case "dsBranch_uncond". Focus.

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

  destruct_ctx_br.
  simpl in Hfresh. destruct Hfresh as [Hnotin Hfresh].
  inv Htcmds. inv Httmn.

Lemma lookup_trans_blocks__trans_block : forall bs1 bs2 ex_ids0 ex_ids ex_ids'
    l0 b1 rm,
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
Admitted.

     
admit.

Case "dsBop". eapply SBpass_is_correct__dsBop; eauto.
admit. admit. admit.

Case "dsMalloc". eapply SBpass_is_correct__dsMalloc; eauto.
Case "dsFree". eapply SBpass_is_correct__dsFree; eauto.
Case "dsAlloca". eapply SBpass_is_correct__dsAlloca; eauto.

Case "dsLoad_nptr". eapply SBpass_is_correct__dsLoad_nptr; eauto.
Case "dsLoad_ptr". eapply SBpass_is_correct__dsLoad_ptr; eauto.
Case "dsStore_nptr". eapply SBpass_is_correct__dsStore_nptr; eauto.
Case "dsStore_ptr". eapply SBpass_is_correct__dsStore_ptr; eauto.

Admitted.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)


