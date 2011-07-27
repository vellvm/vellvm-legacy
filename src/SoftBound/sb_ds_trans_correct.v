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
Require Import ssa_wf.
Require Import ssa_props.
Require Import sb_ds_trans_axioms.
Require Import sb_ds_trans_lib.

Import SB_ds_pass.


Lemma SBpass_is_correct__dsCall : forall (mi : MoreMem.meminj) 
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
  (H2 : initLocals TD la ogvs = Some (lc', rm')),
   exists St' : LLVMopsem.State,
     exists mi' : MoreMem.meminj,
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
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd.
  remember (trans_params rm2 lp 1) as R.
  destruct R as [cs1|]; try solve [inversion Htcmd].
  remember (call_suffix rid noret0 ca ft fv lp rm2) as R1.
  destruct R1 as [cs2|]; try solve [inversion Htcmd].
  inv Htcmd.
  unfold call_suffix in HeqR1.
  remember (if negb noret0 && isReturnPointerTypB ft
             then
              match lookupAL (id * id) rm2 rid with
              | ret (bid0, eid0) =>
                  ret (insn_call bid0 false attrs gsb_typ gsb_fn
                         ((i32, vint0) :: nil)
                       :: insn_call eid0 false attrs gse_typ gse_fn
                            ((i32, vint0) :: nil)
                          :: insn_call fake_id true attrs dstk_typ dstk_fn
                               nil :: nil)
              | merror => merror
              end
             else ret [insn_call fake_id true attrs dstk_typ dstk_fn nil]) as R2.
  destruct R2 as [cs22|]; inv HeqR1.

  assert (Hlkf:=H).
  eapply lookupFdefViaGV__simulation in H; eauto.
  destruct H as [f2 [Hlkf' Htfdef2]].
  assert (Htfdef2':=Htfdef2).
  apply trans_fdef_inv in Htfdef2.
  assert (JJ:=Hlkf).
  apply lookupFdefViaGV_isnt_callLib in JJ.
  rewrite JJ in Htfdef2.
  destruct Htfdef2 as [ex_ids3 [rm3 [cs3 [ex_ids3' [bs3 [l1 [ps1 [cs4 [tmn1 [J1
    [J2 [J3 J4]]]]]]]]]]]]; subst.

  assert (Hpsim := H1).
  eapply trans_params_simulation in Hpsim; eauto.
     simpl_env. simpl.
     assert (Hop:=Hlkf').
     apply shadow_stack_init with (S2:=S2)(B2:=B2)(ft:=ft)(cs2':=cs2')(lc':=lc')
       (rm':=rm')(gl:=gl2)(mi:=mi)(lp:=lp)(cs1:=cs1)(rm2:=rm2)(Mem0:=Mem0)
       (MM:=MM)(noret0:=noret0)(M2:=M2)(ex_ids3:=ex_ids3)(ogvs:=ogvs)
       (mgb:=mgb)(lb:=lb)(als2:=als2)(tmn2:=tmn2)(ca:=ca)(rid:=rid)(cs22:=cs22)
       (cs23:=cs23)(bs2:=bs2)(fh2:=fh2)(ECs2:=ECs2)(rm3:=rm3) in Hop; auto.
     destruct Hop as [M2' [lc2' [Hop [Hwfmi2 [Hrsim2 Hmsim2]]]]].
     exists (LLVMopsem.mkState S2 (los, nts) Ps2
      ((LLVMopsem.mkEC 
        (fdef_intro (fheader_intro fa rt (wrapper_fid fid) la va)
                (block_intro l1 ps1 (cs3 ++ cs4) tmn1 :: bs3))
        (block_intro l1 ps1 (cs3 ++ cs4) tmn1)
        cs4
      tmn1 lc2' nil):: 
      (LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
        (insn_call rid noret0 ca ft (wrap_call fv) lp :: cs22 ++ cs2' ++ cs23)
      tmn2 lc2 als2):: ECs2) gl2 fs2 M2').
     exists mi. 
     split; auto.
     clear Hop.
     assert (Hentry:=H0).
     apply trans_blocks_inv in J3.
     destruct J3 as [b1 [bs1' [ex_ids4' [J31 [J32 J33]]]]]; subst.
     simpl in H0. inv H0.
     apply trans_block_inv in J31.
     destruct J31 as [p' [c' [cs5 [J31 [J35 [J36 J37]]]]]].
     inv J37.
     repeat (split; auto).
       eapply entryBlockInFdef; eauto.
       eapply lookupFdefViaGV_inv; eauto.        
       exists l'. exists ps'. exists nil. auto.
       exists l'. exists p'. exists cs3. auto.
       exists ex_ids3. exists rm3. exists ex_ids3. exists ex_ids4'.
       exists c'. exists cs5.
       split; auto. split; auto. split; auto using incl_refl.
       clear - Heqb2. destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
       exists l2. exists ps2. 
       exists 
           (cs21 ++
            ((insn_call fake_id true attrs astk_typ astk_fn
                (val32 (Z_of_nat (length lp + 1)) :: nil)
              :: cs1))).
       simpl_env. auto.
       exists ex_ids. exists rm2. exists ex_ids5. exists ex_ids4.
       exists (insn_call rid noret0 ca ft (wrap_call fv) lp :: cs22).
       exists cs2'. exists cs23.
       repeat (split; auto).
         unfold call_suffix.
         rewrite <- HeqR2. auto.
Qed.
       

Lemma SBpass_is_correct__dsExCall : forall (mi : MoreMem.meminj) 
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
  (H2 : exCallUpdateLocals TD ft noret0 rid oresult lc rm = ret (lc', rm')),
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
         Mem := Mem';
         Mmap := MM |} St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd.
  remember (trans_params rm2 lp 1) as R.
  destruct R as [cs1|]; try solve [inversion Htcmd].
  remember (call_suffix rid noret0 ca ft fv lp rm2) as R1.
  destruct R1 as [cs2|]; try solve [inversion Htcmd].
  inv Htcmd.
  unfold call_suffix in HeqR1.
  remember (if negb noret0 && isReturnPointerTypB ft
             then
              match lookupAL (id * id) rm2 rid with
              | ret (bid0, eid0) =>
                  ret (insn_call bid0 false attrs gsb_typ gsb_fn
                         ((i32, vint0) :: nil)
                       :: insn_call eid0 false attrs gse_typ gse_fn
                            ((i32, vint0) :: nil)
                          :: insn_call fake_id true attrs dstk_typ dstk_fn
                               nil :: nil)
              | merror => merror
              end
             else ret [insn_call fake_id true attrs dstk_typ dstk_fn nil]) as R2.
  destruct R2 as [cs22|]; inv HeqR1.

  assert (Hlkf:=H).
  eapply lookupExFdecViaGV__simulation in H; eauto.
  destruct H as [f2 [Hlkf' Htfdec2]].
  inv Htfdec2. 

     simpl_env. simpl.
     assert (Hop:=Hlkf').
     apply shadow_stack_exfdec with (S2:=S2)(B2:=B2)(ft:=ft)(cs2':=cs2')
       (lc':=lc')(oresult:=oresult)(bs1:=bs1)(fh1:=fh1)(lc:=lc)
       (rm':=rm')(mi:=mi)(lp:=lp)(cs1:=cs1)(rm2:=rm2)(Mem0:=Mem0)
       (MM:=MM)(noret0:=noret0)(M2:=M2)(gvs:=gvs)(Mem':=Mem')
       (mgb:=mgb)(als2:=als2)(tmn2:=tmn2)(ca:=ca)(rid:=rid)(cs22:=cs22)
       (cs23:=cs23)(bs2:=bs2)(fh2:=fh2)(ECs2:=ECs2)(rm:=rm) in Hop; auto.
     destruct Hop as [M2' [lc2' [Hop [Hwfmi2 [Hrsim2 Hmsim2]]]]].
     exists (LLVMopsem.mkState S2 (los, nts) Ps2
              ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2 (cs2' ++ cs23)
                tmn2 lc2' als2):: ECs2) gl2 fs2 M2').
     exists mi. 
     split; auto.
     clear Hop.
     repeat (split; auto).
       clear - Heqb1. destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
       exists l1. exists ps1. exists (cs11++[insn_call rid noret0 ca ft fv lp]).
       simpl_env. auto.
       
       clear - Heqb2. destruct Heqb2 as [l2 [ps2 [cs2 Heqb2]]]; subst.
       exists l2. exists ps2. 
       exists (cs2 ++
           ((insn_call fake_id true attrs astk_typ astk_fn
            (val32 (Z_of_nat (length lp + 1)) :: nil)
           :: cs1 ++ insn_call rid noret0 ca ft (wrap_call fv) lp :: cs22))).
       simpl_env. auto.
       exists ex_ids. exists rm2. exists ex_ids5. exists ex_ids4.
       exists cs2'. exists cs23.
       repeat (split; auto).
Qed.

Lemma SBpass_is_correct__dsBranch_uncond : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
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
     exists mi' : MoreMem.meminj,
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
  inv Htcmds. inv Httmn.

  assert (HuniqF:=HFinPs).
  eapply wf_system__uniqFdef in HuniqF; eauto.
  destruct fh1. destruct HuniqF as [HuniqBlocks HuniqArgs].
  simpl in H. symmetry in H.
  assert (Htfdef':=Htfdef). 
  apply trans_fdef_inv in Htfdef'.
  rewrite Hclib in Htfdef'.
  destruct Htfdef' as [ex_ids1 [rm2' [cs1' [ex_ids' [bs' [l1 [ps1 [cs1 [tmn1 [J1
    [J2 [J3 J4]]]]]]]]]]]].
  inv J4.
  rewrite Hgenmeta in J1. inv J1.

  assert (Htblocks := J3).
  eapply lookup_trans_blocks__trans_block with (ex_ids0:=ex_ids1) in J3; 
    eauto using incl_refl.
  destruct J3 as [ex_ids1' [ex_ids2 [b2' [Hlk' [Htblock Hinc']]]]].
  simpl in Htblock.

  apply trans_block_inv in Htblock.
  destruct Htblock as [ps2 [cs2 [cs [JJ1 [JJ2 [JJ3 eq]]]]]]; subst.

  assert (HBinF':=H).
  apply genLabel2Block_blocks_inv with (f:=(fheader_intro f t i0 a v)) in HBinF';
    auto. 
  destruct HBinF' as [EQ HBinF']; subst.

  assert (exists lc2', LLVMopsem.switchToNewBasicBlock (los,nts) 
    (block_intro l' ps2 (cs2 ++ cs) tmn') B2 gl2 lc2 = Some lc2' /\
    reg_simulation mi (los, nts) gl2
            (fdef_intro (fheader_intro f t i0 a v) bs1) rm' rm2' lc' lc2') 
    as Hswitch2.
    eapply switchToNewBasicBlock__reg_simulation; eauto.

  destruct Hswitch2 as [lc2' [Hswitch2 Hrsim']].
  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC 
            (fdef_intro (fheader_intro f t (wrapper_fid i0) a v)
               (block_intro l1 ps1 (cs1'++ cs1) tmn1 :: bs'))
            (block_intro l' ps2 (cs2 ++ cs) tmn')
            (cs2 ++ cs) tmn' lc2' als2):: 
            ECs2) gl2 fs2 M2).
  exists mi.
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    eapply LLVMopsem.dsop_star_cons; eauto.
      eapply LLVMopsem.dsBranch_uncond; eauto.
        simpl. unfold lookupBlockViaLabelFromBlocks in Hlk'.
        rewrite <- Hlk'. simpl.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l' l1); 
          subst; auto.

          simpl in Hlk'.
          destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l1 l1).
            inv Hlk'.
           apply trans_blocks_inv in Htblocks.
           destruct Htblocks as [b1 [bs1' [ex_ids3 [J1 [J7 J8]]]]]; subst.
           destruct b1.
           apply trans_block_inv in J1.
           destruct J1 as [p' [cs'' [cs0' [J9 [J10 [J11 J12]]]]]].
           inv J12. 
           eapply wf_system__wf_fdef in HFinPs; eauto.
           clear - HBinF H Heqb1 HFinPs.
           destruct Heqb1 as [l1 [ps1 [cs1'' Heq1]]]; subst.
           eapply getEntryBlock_inv with (l':=l0)(a:=l0) in HBinF; simpl; eauto.
           contradict HBinF; auto.

           contradict n; auto.

  repeat (split; auto).
    exists l'. exists ps'. exists nil. auto.
    exists l'. exists ps2. exists nil. auto.
    exists ex_ids1. exists rm2'. exists ex_ids1'. exists ex_ids2. exists cs2.
    exists cs. 
    repeat (split; auto).
Qed.

Lemma SBpass_is_correct__dsBranch : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
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
     exists mi' : MoreMem.meminj,
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
  inv Htcmds. inv Httmn.

  assert (HuniqF:=HFinPs).
  eapply wf_system__uniqFdef in HuniqF; eauto.
  destruct fh1. destruct HuniqF as [HuniqBlocks HuniqArgs].
  simpl in H. symmetry in H.
  assert (Htfdef':=Htfdef). 
  apply trans_fdef_inv in Htfdef'.
  rewrite Hclib in Htfdef'.
  destruct Htfdef' as [ex_ids1 [rm2' [cs1' [ex_ids' [bs' [l1' [ps1 [cs1 [tmn1 [J1
    [J2 [J3 J4]]]]]]]]]]]].
  inv J4.
  rewrite Hgenmeta in J1. inv J1.

  symmetry in H.
  eapply simulation__getOperandValue in H; eauto.
  destruct H as [c' [H Hinj]].

  erewrite simulation__isGVZero in H0; eauto.
  assert (exists ex_ids1' : ids, exists ex_ids2 : ids, exists b2 : block,
    (if isGVZero (los,nts) c' 
     then lookupBlockViaLabelFromBlocks (block_intro l1' ps1 cs1 tmn1 :: bs') l2
     else lookupBlockViaLabelFromBlocks (block_intro l1' ps1 cs1 tmn1 :: bs') l1)
      = ret b2 /\
    trans_block ex_ids1' rm2' (block_intro l' ps' cs' tmn') = ret (ex_ids2, b2) 
      /\
    incl ex_ids1 ex_ids1') as Hfind.
   destruct (isGVZero (los,nts) c');
      eapply lookup_trans_blocks__trans_block with (ex_ids:=ex_ids1);
        eauto using incl_refl.
  destruct Hfind as [ex_ids1' [ex_ids2 [b2' [Hlk' [Htblock Hinc']]]]].
  simpl in Htblock.

  apply trans_block_inv in Htblock.
  destruct Htblock as [ps2 [cs2 [cs [JJ1 [JJ2 [JJ3 eq]]]]]]; subst.

  assert (blockInFdefB (block_intro l' ps' cs' tmn') 
    (fdef_intro (fheader_intro f t i0 a v) bs1)) as HBinF'.
    symmetry in H0.
    destruct (isGVZero (los,nts) c').
      apply genLabel2Block_blocks_inv with (f:=(fheader_intro f t i0 a v)) in H0
        ; auto. destruct H0; eauto.
      apply genLabel2Block_blocks_inv with (f:=(fheader_intro f t i0 a v)) in H0
        ; auto. destruct H0; eauto.

  assert (exists lc2', LLVMopsem.switchToNewBasicBlock (los,nts) 
    (block_intro l' ps2 (cs2 ++ cs) tmn') B2 gl2 lc2 = Some lc2' /\
    reg_simulation mi (los, nts) gl2
            (fdef_intro (fheader_intro f t i0 a v) bs1) rm' rm2' lc' lc2') 
    as Hswitch2.
    eapply switchToNewBasicBlock__reg_simulation; eauto.

  destruct Hswitch2 as [lc2' [Hswitch2 Hrsim']].
  exists (LLVMopsem.mkState S2 (los, nts) Ps2
          ((LLVMopsem.mkEC 
            (fdef_intro (fheader_intro f t (wrapper_fid i0) a v)
               (block_intro l1' ps1 (cs1'++ cs1) tmn1 :: bs'))
            (block_intro l' ps2 (cs2 ++ cs) tmn')
            (cs2 ++ cs) tmn' lc2' als2):: 
            ECs2) gl2 fs2 M2).
  exists mi.
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    eapply LLVMopsem.dsop_star_cons; eauto.
      eapply LLVMopsem.dsBranch; eauto.
        apply trans_blocks_inv in J3.
        destruct J3 as [b1 [bs1' [ex_ids3 [J1 [J7 J8]]]]]; subst.
        destruct b1.
        apply trans_block_inv in J1.
        destruct J1 as [p' [cs'' [cs0' [J9 [J10 [J11 J12]]]]]].
        inv J12. 
        eapply wf_system__wf_fdef in HFinPs; eauto.
        destruct Heqb1 as [l3 [ps1 [cs1'' Heq1]]]; subst.
        assert (l1 <> l0 /\ l2 <> l0) as HA.
          clear - HBinF H HFinPs.
          split.
            eapply getEntryBlock_inv with (l':=l1)(a:=l0) in HBinF; 
              simpl; eauto.
            eapply getEntryBlock_inv with (l':=l2)(a:=l0) in HBinF; 
              simpl; eauto.

        rewrite <- Hlk'. unfold lookupBlockViaLabelFromBlocks. simpl.
        destruct HA as [HA1 HA2].
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l2 l0); 
          subst; try solve [auto | contradict HA2; auto].
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l1 l0); 
          subst; try solve [auto | contradict HA1; auto].

  repeat (split; auto).
    exists l'. exists ps'. exists nil. auto.
    exists l'. exists ps2. exists nil. auto.
    exists ex_ids1. exists rm2'. exists ex_ids1'. exists ex_ids2. exists cs2.
    exists cs. 
    repeat (split; auto).
Qed.

Lemma SBpass_is_correct__dsReturn : forall 
  (mi : MoreMem.meminj)
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
     exists mi' : MoreMem.meminj,
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
    assert (In i0 (getFdefLocs (fdef_intro fh1' bs1'))) as Hin.
      eauto using getCmdID_in_getFdefLocs.
    destruct t; tinv H1.
    remember (fit_gv (los, nts) t gr) as Fit.
    destruct Fit; tinv H1. simpl in Hcall'.
    destruct (isPointerTypB t).
    SSCase "ct is ptr".
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
      symmetry in HeqFit.
      eapply simulation__fit_gv in HeqFit; eauto.
      destruct HeqFit as [gr2' [HeqFit HinjFit]].
      exists (LLVMopsem.mkState S2 (los, nts) Ps2
        ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' 
            (updateAddAL _ 
              (updateAddAL _ (updateAddAL _ lc2' i0 (? gr2' # t ?)) bid0 bgv2) 
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
              ((insn_call i0 false c (typ_function t l0 v0) (wrap_call v) p)::
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
              ((insn_call i0 false c (typ_function t l0 v0) (wrap_call v) p)::
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
              tmn2' (updateAddAL _ lc2' i0 (? gr2' # t ?)) als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
            unfold LLVMopsem.returnUpdateLocals.
            rewrite J1. rewrite HeqFit. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (insn_call eid0 false attrs gse_typ gse_fn((i32, vint0) :: nil)::
               insn_call fake_id true attrs dstk_typ dstk_fn nil::
               (cs23' ++ cs24'))
              tmn2' 
              (updateAddAL _ (updateAddAL _ lc2' i0  (? gr2' # t ?)) bid0 bgv2) 
              als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsExCall with (fid:=gsb_fid)
            (gvs:=(int2GV 0 :: nil))(oresult:=Some bgv2); eauto.
            eapply gsb_is_found; eauto.
              clear - Hfree2' Hgbase.
              eapply free_doesnt_change_gsb; eauto.
              unfold gsb_typ, p8. simpl. unfold fit_gv. simpl. 
              admit. (*md is canonical *)

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (insn_call fake_id true attrs dstk_typ dstk_fn nil:: 
               cs23' ++ cs24')
              tmn2' (updateAddAL _ (updateAddAL _ 
                (updateAddAL _ lc2' i0  (? gr2' # t ?)) 
                bid0 bgv2) eid0 egv2) als2'):: ECs2)
            gl2 fs2 M2''')); auto.
          eapply LLVMopsem.dsExCall with (fid:=gse_fid)
            (gvs:=(int2GV 0 :: nil))(oresult:=Some egv2); eauto.
            eapply gse_is_found; eauto.
              clear - Hfree2' Hgbound.
              eapply free_doesnt_change_gse; eauto.
              unfold gsb_typ, p8. simpl. unfold fit_gv. simpl.
              admit. (*md is canonical *)

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (cs23' ++ cs24')
              tmn2' (updateAddAL _ (updateAddAL _ 
                (updateAddAL _ lc2' i0  (? gr2' # t ?)) 
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
              [insn_call i0 false c (typ_function t l0 v0) (wrap_call v) p] ++
              [insn_call bid0 false attrs gsb_typ gsb_fn [(i32, vint0)]] ++
              [insn_call eid0 false attrs gse_typ gse_fn [(i32, vint0)]] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          split; auto.              
          split.
            eapply reg_simulation__updateAddAL_prop with (ex_ids3:=ex_ids'); 
              eauto using simulation___cgv2gv.
            repeat (split; auto).

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
      symmetry in HeqFit.
      eapply simulation__fit_gv in HeqFit; eauto.
      destruct HeqFit as [gr2' [HeqFit HinjFit]].
      exists (LLVMopsem.mkState S2 (los, nts) Ps2
        ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' 
            (updateAddAL _ (updateAddAL _ 
              (updateAddAL _ lc2' i0 (? gr2' # t ?)) bid0 null) 
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
              ((insn_call i0 false c (typ_function t l0 v0) (wrap_call v) p)::
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
              ((insn_call i0 false c (typ_function t l0 v0) (wrap_call v) p)::
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
              tmn2' (updateAddAL _ lc2' i0 (? gr2' # t ?)) als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
            unfold LLVMopsem.returnUpdateLocals. simpl.
            rewrite J1. rewrite HeqFit. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (insn_call eid0 false attrs gse_typ gse_fn((i32, vint0) :: nil)::
               insn_call fake_id true attrs dstk_typ dstk_fn nil::
               (cs23' ++ cs24'))
              tmn2' 
              (updateAddAL _ (updateAddAL _ lc2' i0 (? gr2' # t ?)) bid0 null) 
              als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsExCall with (fid:=gsb_fid)
            (gvs:=(int2GV 0 :: nil))(oresult:=Some null); eauto.
            eapply gsb_is_found; eauto. 
              eapply free_allocas_preserves_gsb; eauto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (insn_call fake_id true attrs dstk_typ dstk_fn nil:: 
               cs23' ++ cs24')
              tmn2' (updateAddAL _ (updateAddAL _ 
                (updateAddAL _ lc2' i0 (? gr2' # t ?)) 
                bid0 null) eid0 null) als2'):: ECs2)
            gl2 fs2 M2''')); auto.
          eapply LLVMopsem.dsExCall with (fid:=gse_fid)
            (gvs:=(int2GV 0 :: nil))(oresult:=Some null); eauto.
            eapply gse_is_found; eauto.
              eapply free_allocas_preserves_gse; eauto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (cs23' ++ cs24')
              tmn2' (updateAddAL _ (updateAddAL _ 
                (updateAddAL _ lc2' i0 (? gr2' # t ?)) 
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
              [insn_call i0 false c (typ_function t l0 v0) (wrap_call v) p] ++
              [insn_call bid0 false attrs gsb_typ gsb_fn [(i32, vint0)]] ++
              [insn_call eid0 false attrs gse_typ gse_fn [(i32, vint0)]] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          split; auto.              
          split.
            eapply reg_simulation__updateAddAL_prop with (ex_ids3:=ex_ids'); 
              eauto using simulation___cgv2gv, gv_inject_null_refl.
            repeat (split; auto).

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
      symmetry in HeqFit.
      eapply simulation__fit_gv in HeqFit; eauto.
      destruct HeqFit as [gr2' [HeqFit HinjFit]].
      exists (LLVMopsem.mkState S2 (los, nts) Ps2
        ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' (updateAddAL _ lc2' i0 (? gr2' # t ?))
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
              ((insn_call i0 false c (typ_function t l0 v0) (wrap_call v) p)::
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
              ((insn_call i0 false c (typ_function t l0 v0) (wrap_call v) p)::
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
              tmn2' (updateAddAL _ lc2' i0 (? gr2' # t ?)) als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
            unfold LLVMopsem.returnUpdateLocals. simpl.
            rewrite J1. rewrite HeqFit. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (cs23' ++ cs24')
              tmn2' (updateAddAL _ lc2' i0 (? gr2' # t ?)) als2'):: ECs2)
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
              [insn_call i0 false c (typ_function t l0 v0) (wrap_call v) p] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          apply reg_simulation__updateAddAL_lc with (i0:=i0)(gv:= (? g # t ?))
            (gv':= (? gr2' # t ?)) (ex_ids3:=ex_ids') in Hrsim'; 
            eauto using simulation___cgv2gv.
          repeat (split; auto).

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
      symmetry in HeqFit.
      eapply simulation__fit_gv in HeqFit; eauto.
      destruct HeqFit as [gr2' [HeqFit HinjFit]].
      exists (LLVMopsem.mkState S2 (los, nts) Ps2
        ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' (updateAddAL _ lc2' i0 (? gr2' # t ?))
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
              ((insn_call i0 false c (typ_function t l0 v0) (wrap_call v) p)::
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
              ((insn_call i0 false c (typ_function t l0 v0) (wrap_call v) p)::
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
              tmn2' (updateAddAL _ lc2' i0 (? gr2' # t ?)) als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
            unfold LLVMopsem.returnUpdateLocals. simpl.
            rewrite J1. rewrite HeqFit. auto.

        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              (cs23' ++ cs24')
              tmn2' (updateAddAL _ lc2' i0 (? gr2' # t ?)) als2'):: ECs2)
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
              [insn_call i0 false c (typ_function t l0 v0) (wrap_call v) p] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          apply reg_simulation__updateAddAL_lc with (i0:=i0)(gv:= (? g # t ?))
            (gv':= (? gr2' # t ?)) (ex_ids3:=ex_ids') in Hrsim'; 
            eauto using simulation___cgv2gv.
          repeat (split; auto).
Qed.

Lemma SBpass_is_correct__dsReturnVoid : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : LLVMopsem.State) (S : system)
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
     exists mi' : MoreMem.meminj,
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

Require Import sb_ds_trans_cmd_cases.
Require Import sb_ds_trans_mem_cases.

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
Case "dsCall". eapply SBpass_is_correct__dsCall; eauto.
Case "dsExCall". eapply SBpass_is_correct__dsExCall; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)


