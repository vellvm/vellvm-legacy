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
Require Import sb_ds_trans_axioms.
Require Import sb_ds_trans_lib.

Import SB_ds_pass.


Lemma incl_cons : forall A l1 (x:A), incl l1 (x::l1).
Proof.
  intros. intros y J. simpl; auto.
Qed.


Lemma prop_metadata_mono : forall ex_ids1 rm c v i0 ex_ids2 cs2,
  prop_metadata ex_ids1 rm c v i0 =  ret (ex_ids2, cs2) ->
  incl ex_ids1 ex_ids2.
Proof.
  intros.
  unfold prop_metadata in *.
  destruct (get_reg_metadata rm v) as [[? ?]|]; try solve [inv H].
  remember (mk_tmp ex_ids1) as R.
  destruct R; inv H.
  unfold mk_tmp in HeqR.
  destruct (atom_fresh_for_list ex_ids1); inv HeqR.
  destruct (lookupAL (id * id) rm i0) as [[? ?]|]; inv H1.
  auto using incl_refl.
Qed.

Lemma trans_cmd_fresh_mono : forall rm c ex_ids1 ex_ids2 cs2,
  trans_cmd ex_ids1 rm c = Some (ex_ids2, cs2) ->
  incl ex_ids1 ex_ids2.
Proof.
  intros.
  destruct c; simpl in H; try solve [inv H; auto using incl_refl].
  
    destruct (lookupAL (id * id) rm i0) as [[bid eid]|]; inv H.
    remember (mk_tmp ex_ids1) as R.
    destruct R; inv H1.
    unfold mk_tmp in HeqR.
    destruct (atom_fresh_for_list ex_ids1); inv HeqR; auto using incl_cons.

    destruct (lookupAL (id * id) rm i0) as [[bid eid]|]; inv H.
    remember (mk_tmp ex_ids1) as R.
    destruct R; inv H1.
    unfold mk_tmp in HeqR.
    destruct (atom_fresh_for_list ex_ids1); inv HeqR; auto using incl_cons.
    
    destruct (get_reg_metadata rm v) as [[? ?]|]; try solve [inv H].
    remember (mk_tmp ex_ids1) as R.
    destruct R; inv H.
    unfold mk_tmp in HeqR.
    destruct (atom_fresh_for_list ex_ids1); inv HeqR.
    destruct (isPointerTypB t).
      destruct (lookupAL (id * id) rm i0) as [[? ?]|]; inv H1.
      auto using incl_cons.
      inv H1. auto using incl_cons. 

    destruct (get_reg_metadata rm v0) as [[? ?]|]; try solve [inv H].
    remember (mk_tmp ex_ids1) as R.
    destruct R; inv H.
    unfold mk_tmp in HeqR.
    destruct (atom_fresh_for_list ex_ids1); inv HeqR.
    destruct (isPointerTypB t).
      destruct (get_reg_metadata rm v) as [[? ?]|]; inv H1.
      auto using incl_cons.
      inv H1. auto using incl_cons. 

    eapply prop_metadata_mono; eauto.
    
    destruct c; inv H; auto using incl_refl.
      destruct (lookupAL (id * id) rm i0) as [[? ?]|]; inv H1.
      auto using incl_refl.

      destruct (isPointerTypB t).
        eapply prop_metadata_mono; eauto.
        inv H1. auto using incl_refl.

    destruct (isPointerTypB t).
      destruct (get_reg_metadata rm v0) as [[? ?]|]; inv H.
      destruct (get_reg_metadata rm v1) as [[? ?]|]; inv H1.
      destruct (lookupAL (id * id) rm i0) as [[? ?]|]; inv H0.
        auto using incl_refl.
      inv H. auto using incl_refl.

    destruct (trans_params rm p 1) as [?|]; inv H.
    destruct (call_suffix i0 n c t v p rm); inv H1.
    auto using incl_refl.
Qed.
    
Lemma trans_cmds_cons_inv : forall ex_ids1 rm c cs ex_ids2 cs2,
  trans_cmds ex_ids1 rm (c :: cs) = ret (ex_ids2, cs2) ->
  exists ex_ids3, exists cs21, exists cs22,
    trans_cmd ex_ids1 rm c = ret (ex_ids3, cs21) /\
    trans_cmds ex_ids3 rm cs = ret (ex_ids2, cs22) /\
    cs21 ++ cs22 = cs2.
Proof.
  intros. 
  simpl in H.
  remember (trans_cmd ex_ids1 rm c) as R.
  destruct R as [[ex_ids1' cs21]|]; inv H.
  remember (trans_cmds ex_ids1' rm cs) as R1.
  destruct R1 as [[ex_ids2' cs22]|]; inv H1.
  exists ex_ids1'. exists cs21. exists cs22.
  split; eauto.
Qed.    

Lemma trans_cmds_fresh_mono : forall rm cs ex_ids1 ex_ids2 cs2,
  trans_cmds ex_ids1 rm cs = Some (ex_ids2, cs2) ->
  incl ex_ids1 ex_ids2.
Proof.
  induction cs; intros.
    inv H; auto using incl_refl.

    apply trans_cmds_cons_inv in H.
    destruct H as [ex_ids3 [cs21 [cs22 [J1 [J2 eq]]]]]; subst.
    apply trans_cmd_fresh_mono in J1.
    apply IHcs in J2.
    eapply incl_tran; eauto. 
Qed.


Lemma trans_blocks_cons_inv : forall ex_ids1 rm b bs ex_ids2 bs2,
  trans_blocks ex_ids1 rm (b :: bs) = ret (ex_ids2, bs2) ->
  exists ex_ids3, exists b2, exists bs2',
    trans_block ex_ids1 rm b = ret (ex_ids3, b2) /\
    trans_blocks ex_ids3 rm bs = ret (ex_ids2, bs2') /\
    b2::bs2' = bs2.
Proof.
  intros. 
  simpl in H.
  remember (trans_block ex_ids1 rm b) as R.
  destruct R as [[ex_ids1' b1]|]; inv H.
  remember (trans_blocks ex_ids1' rm bs) as R1.
  destruct R1 as [[ex_ids2' bs']|]; inv H1.
  exists ex_ids1'. exists b1. exists bs'.
  split; eauto.
Qed.    

Lemma trans_block_inv : forall ex_ids rm l1 p c t ex_ids3 b2,
  trans_block ex_ids rm (block_intro l1 p c t) = ret (ex_ids3, b2) ->
  exists p', exists c', exists cs,
    trans_phinodes rm p = Some p' /\
    trans_cmds ex_ids rm c = Some (ex_ids3, c') /\
    trans_terminator rm t = Some cs /\
    b2 = block_intro l1 p' (c'++cs) t.
Proof.
  intros. simpl in *.
    remember (trans_phinodes rm p) as R2.
    destruct R2 as [ps2|]; try solve [inv H].
    remember (trans_cmds ex_ids rm c) as R3.
    destruct R3 as [[ex_ids2 cs2]|]; try solve [inv H].
    remember (trans_terminator rm t) as R4.
    destruct R4 as [cs2'|]; inv H.
    exists ps2. exists cs2. exists cs2'. split; auto.
Qed.

Lemma trans_fdef_inv : forall nts fa t fid la va bs f',
  trans_fdef nts (fdef_intro (fheader_intro fa t fid la va) bs) = Some f' ->
  if isCallLib fid then 
    f' = (fdef_intro (fheader_intro fa t fid la va) bs)
  else
    exists ex_ids, exists rm, exists cs', exists ex_ids',
    exists bs', exists l1, exists ps1, exists cs1, exists tmn1,
      gen_metadata_fdef nts 
        (getFdefLocs (fdef_intro (fheader_intro fa t fid la va) bs)) nil 
        (fdef_intro (fheader_intro fa t fid la va) bs) = Some (ex_ids,rm) /\
      trans_args rm la 1%Z = Some cs' /\
      trans_blocks ex_ids rm bs = 
        Some (ex_ids', (block_intro l1 ps1 cs1 tmn1)::bs') /\
      f' = (fdef_intro 
                     (fheader_intro fa t (wrapper_fid fid) la va) 
                     ((block_intro l1 ps1 (cs'++cs1) tmn1)::bs')). 
Proof.
  intros. simpl in *.
  destruct (isCallLib fid).
    inv H; auto.

    destruct (gen_metadata_args (let '(_, ids0) := split la in
               ids0 ++ getBlocksLocs bs) nil la).
    destruct (gen_metadata_blocks nts i0 r bs) as [[ex_ids rm]|]; inv H.
    exists ex_ids. exists rm.
    destruct (trans_args rm la 1) as [cs'|]; inv H1.
    exists cs'.
    destruct (trans_blocks ex_ids rm bs); inv H0.
    destruct p.
    destruct b; inv H1.
    destruct b; inv H0. 
    exists i1. exists b0. exists l0. exists p. exists c. exists t0.
    eauto.
Qed.

Lemma trans_blocks_inv : forall ex_ids1 rm2 bs1 ex_ids2 b2 bs2',
  trans_blocks ex_ids1 rm2 bs1 = Some (ex_ids2, b2::bs2') ->
  exists b1, exists bs1', exists ex_ids3, 
    trans_block ex_ids1 rm2 b1 = Some (ex_ids3, b2) /\
    trans_blocks ex_ids3 rm2 bs1' = Some (ex_ids2, bs2') /\
    bs1 = b1::bs1'.
Proof.
  intros.
  destruct bs1.
    inv H.
    apply trans_blocks_cons_inv in H; auto.
    destruct H as [e1 [b1 [bs3' [J1 [J2 J3]]]]].
    inv J3.
    exists b. exists bs1. exists e1. split; auto.
Qed.

Lemma lookup_trans_blocks__trans_block : forall ex_ids0 l0 rm b1 bs1 bs2 ex_ids 
    ex_ids',
  incl ex_ids0 ex_ids ->
  trans_blocks ex_ids rm bs1 = Some (ex_ids', bs2) ->
  lookupBlockViaLabelFromBlocks bs1 l0 = Some b1 ->
  exists ex_ids1, exists ex_ids2, exists b2,
    lookupBlockViaLabelFromBlocks bs2 l0 = Some b2 /\
    trans_block ex_ids1 rm b1 = Some (ex_ids2, b2) /\
    incl ex_ids0 ex_ids1.
Proof.
  induction bs1; intros bs2 ex_ids ex_ids' Hinc Htrans Hlk.
    inv Hlk.

    apply trans_blocks_cons_inv in Htrans.
    destruct Htrans as [ex_ids3 [b2 [bs2' [J1 [J2 eq]]]]]; subst.
    
    destruct a.
    apply trans_block_inv in J1.
    destruct J1 as [ps2 [cs2 [cs2' [J1 [J3 [J4 eq]]]]]]; subst.
    unfold lookupBlockViaLabelFromBlocks in *. simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l1); subst.
    exists ex_ids. exists ex_ids3. exists (block_intro l1 ps2 (cs2 ++ cs2') t). 
    inv Hlk. simpl. rewrite J1. rewrite J3. rewrite J4.
    split; auto.

    eapply IHbs1 with (ex_ids':=ex_ids')(ex_ids:=ex_ids3) ; eauto.
      apply trans_cmds_fresh_mono in J3.
      eapply incl_tran; eauto.
Qed.


Lemma wrapper_is_identical : forall fv, wrap_call fv = fv.
Proof. 
  unfold wrap_call. 
  destruct fv; auto.
  destruct c; auto. 
    rewrite wrapper_fid_is_identical. auto.
Qed.


Lemma trans_products__trans_fdef : forall nts Ps1 Ps2 fid f1,
  trans_products nts Ps1 = Some Ps2 ->
  lookupFdefViaIDFromProducts Ps1 fid = ret f1 ->
  exists f2, 
    lookupFdefViaIDFromProducts Ps2 fid = ret f2 /\
    trans_fdef nts f1 = ret f2.
Proof.
  induction Ps1; simpl; intros Ps2 fid f1 J1 J2.
    inv J2.

    remember (trans_product nts a) as R.     
    destruct R; try solve [inv J1].
    remember (trans_products nts Ps1) as R1.
    destruct R1; inv J1.
    destruct a; simpl in *.
      inv HeqR. simpl. eauto.
      inv HeqR. simpl. eauto.

      remember (trans_fdef nts f) as R1.
      destruct R1; inv HeqR. 
      simpl.
      destruct f. destruct f.
      symmetry in HeqR0. assert (Hf:=HeqR0).
      apply trans_fdef_inv in HeqR0.
      remember (isCallLib i0) as R.
      destruct R; subst.      
        simpl. simpl in J2.
        destruct (i0==fid); subst.
          destruct (fid==fid); subst.
            inv J2.
            exists (fdef_intro (fheader_intro f t fid a v) b).
            split; auto.
            contradict n; auto.
          eauto.

        destruct HeqR0 as [e1 [rm [cs [e2 [bs [l1 [ps1 [cs1 [tmn1 [J1 [J5 [J3 J4]
          ]]]]]]]]]]]; subst.
        simpl. simpl in J2.
        rewrite wrapper_fid_is_identical.
        rewrite wrapper_fid_is_identical in Hf.
        destruct (i0==fid); subst.
          destruct (fid==fid); subst.
            inv J2. 
            exists (fdef_intro (fheader_intro f t fid a v)
              (block_intro l1 ps1 (cs ++ cs1) tmn1 :: bs)).
            split; auto.

            contradict n; auto.
          eauto.
Qed.

Lemma lookupFdefViaGV__simulation : forall mi los nts gl2 F rm rm2 lc lc2 f1
    fv Ps1 Ps2 fs1 fs2 M1 M2 mgb,
  wf_globals mgb  gl2 ->
  wf_sb_mi mgb mi M1 M2 ->
  reg_simulation mi (los,nts) gl2 F rm rm2 lc lc2 ->
  ftable_simulation mi fs1 fs2 ->
  lookupFdefViaGV (los,nts) Ps1 gl2 lc fs1 fv = Some f1 ->
  trans_products nts Ps1 = Some Ps2 ->
  exists f2,
    lookupFdefViaGV (los,nts) Ps2 gl2 lc2 fs2 (wrap_call fv) = Some f2 /\
    trans_fdef nts f1 = Some f2.
Proof.
  intros.
  unfold lookupFdefViaGV in *.
  remember (getOperandValue (los, nts) fv lc gl2) as R1.
  destruct R1 as [fv1|]; inv H3.
  remember (lookupFdefViaGVFromFunTable fs1 fv1) as R2.
  destruct R2 as [fid|]; inv H6.
  symmetry in HeqR1.
  eapply simulation__getOperandValue in HeqR1; eauto.
  destruct HeqR1 as [fv2 [J1 J2]].
  rewrite wrapper_is_identical.
  rewrite J1. simpl.
  erewrite <- H2; eauto.
  rewrite <- HeqR2. simpl.
  eapply trans_products__trans_fdef; eauto.
Qed.
  
Lemma trans_params_simulation : forall mi TD gl F rm2 lp n rm1 lc1 lc2 ogvs cs,
  reg_simulation mi TD gl F rm1 rm2 lc1 lc2 ->
  params2GVs TD lp lc1 gl rm1 = Some ogvs ->
  trans_params rm2 lp n = Some cs ->
  params_simulation TD gl mi lc2 ogvs n cs.
Proof.
  induction lp; simpl; intros n rm1 lc1 lc2 ogvs cs Hrsim Hp2gv Htpa.
    inv Hp2gv. inv Htpa. simpl. auto.

    destruct a.
    remember (getOperandValue TD v lc1 gl) as R0.
    destruct R0; try solve [inv Hp2gv].
    remember (params2GVs TD lp lc1 gl rm1) as R.
    destruct R; try solve [inv Hp2gv].
    remember (trans_params rm2 lp (n + 1)) as R1.
    destruct R1; try solve [inv Htpa].
    destruct (isPointerTypB t); inv Hp2gv.
      remember (get_reg_metadata rm2 v) as R2.
      destruct R2 as [[bv2 ev2]|]; inv Htpa.
      unfold call_set_shadowstack.
      simpl.
      remember (SBopsem.get_reg_metadata TD gl rm1 v) as R3.
      destruct R3 as [[bgv1 egv1]|].
        symmetry in HeqR3.
        assert (J:=Hrsim).
        destruct J as [_ Hrsim2].        
        apply Hrsim2 in HeqR3.
        destruct HeqR3 as [bv2' [ev2' [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
        rewrite <- HeqR2 in J1. inv J1.
        exists bv2'. exists ev2'. exists bgv2. exists egv2.
        repeat (split; eauto).

        eauto.
     inv Htpa. 
     simpl. eauto.
Qed.


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
  (H2 : initLocals la ogvs = (lc', rm')),
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
Proof.
  intros.
  destruct_ctx_other.
  simpl in Hfresh. destruct Hfresh as [Hnotin Hfresh].
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
       split. admit. (*fresh*)
       split; auto. 
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
       

Lemma trans_products__trans_fdec : forall nts Ps1 Ps2 fid f1,
  trans_products nts Ps1 = Some Ps2 ->
  lookupFdecViaIDFromProducts Ps1 fid = ret f1 ->
  exists f2, 
    lookupFdecViaIDFromProducts Ps2 fid = ret f2 /\
    trans_fdec f1 = f2.
Proof.
  induction Ps1; simpl; intros Ps2 fid f1 J1 J2.
    inv J2.

    remember (trans_product nts a) as R.     
    destruct R; try solve [inv J1].
    remember (trans_products nts Ps1) as R1.
    destruct R1; inv J1.
    destruct a; simpl in *.
      inv HeqR. simpl. eauto.

      destruct f. destruct f. simpl in HeqR.
      inv HeqR. simpl. 
      simpl in J2.
      rewrite wrapper_fid_is_identical.
      destruct (i0==fid); subst; eauto.
        inv J2. simpl. 
        rewrite wrapper_fid_is_identical.
        eauto.

      remember (trans_fdef nts f) as R.
      destruct R; inv HeqR.
      simpl. eauto.
Qed.


Lemma trans_products__none : forall nts Ps1 Ps2 fid,
  trans_products nts Ps1 = Some Ps2 ->
  lookupFdefViaIDFromProducts Ps1 fid = None ->
  lookupFdefViaIDFromProducts Ps2 fid = None.
Proof.
  induction Ps1; simpl; intros Ps2 fid J1 J2.
    inv J1. simpl. auto.

    remember (trans_product nts a) as R.     
    destruct R; try solve [inv J1].
    remember (trans_products nts Ps1) as R1.
    destruct R1; inv J1.
    destruct a; simpl in *.
      inv HeqR. simpl. eauto.
      inv HeqR. simpl. eauto.

      remember (trans_fdef nts f) as R1.
      destruct R1; inv HeqR. 
      simpl.
      destruct f. destruct f.
      symmetry in HeqR0. assert (Hf:=HeqR0).
      apply trans_fdef_inv in HeqR0.
      remember (isCallLib i0) as R.
      destruct R; subst.      
        simpl. simpl in J2.
        destruct (i0==fid); subst.
          inv J2. eauto.

        destruct HeqR0 as [e1 [rm [cs [e2 [bs [l1 [ps1 [cs1 [tmn1 [J1 [J5 [J3 J4]
          ]]]]]]]]]]]; subst.
        simpl. simpl in J2.
        rewrite wrapper_fid_is_identical.
        rewrite wrapper_fid_is_identical in Hf.
        destruct (i0==fid); subst.
          inv J2. eauto.
Qed.

Lemma lookupExFdecViaGV__simulation : forall mi los nts gl2 F rm rm2 lc lc2 f1
    fv Ps1 Ps2 fs1 fs2 M1 M2 mgb,
  wf_globals mgb gl2 ->
  wf_sb_mi mgb mi M1 M2 ->
  reg_simulation mi (los,nts) gl2 F rm rm2 lc lc2 ->
  ftable_simulation mi fs1 fs2 ->
  lookupExFdecViaGV (los,nts) Ps1 gl2 lc fs1 fv = Some f1 ->
  trans_products nts Ps1 = Some Ps2 ->
  exists f2,
    lookupExFdecViaGV (los,nts) Ps2 gl2 lc2 fs2 (wrap_call fv) = Some f2 /\
    trans_fdec f1 = f2.
Proof.
  intros.
  unfold lookupExFdecViaGV in *.
  remember (getOperandValue (los, nts) fv lc gl2) as R1.
  destruct R1 as [fv1|]; inv H3.
  remember (lookupFdefViaGVFromFunTable fs1 fv1) as R2.
  destruct R2 as [fid|]; inv H6.
  symmetry in HeqR1.
  eapply simulation__getOperandValue in HeqR1; eauto.
  destruct HeqR1 as [fv2 [J1 J2]].
  rewrite wrapper_is_identical.
  rewrite J1. simpl.
  erewrite <- H2; eauto.
  rewrite <- HeqR2. simpl.
  remember (lookupFdefViaIDFromProducts Ps1 fid) as R.
  destruct R; inv H5.
  erewrite trans_products__none; eauto.
  eapply trans_products__trans_fdec; eauto.
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
Proof.
  intros.
  destruct_ctx_other.
  simpl in Hfresh. destruct Hfresh as [Hnotin Hfresh].
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
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Htprds [Hfsim [Hwfg 
    [Hwfmi HsimM]]]]]]]]]];
    subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct F as [fh1 bs1];
  destruct F2 as [fh2 bs2];
  destruct HsimEC as [Hclib [HBinF [HFinPs [Htfdef [Heq0 [Hasim [Hnth [Heqb1 
    [Heqb2 [ex_ids [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [Hgenmeta [Hrsim [Hinc 
    [Hfresh [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]]; subst
end.

Fixpoint incomingValues_simulation (mi:Values.meminj)
  (re1:list (id * GenericValue * monad metadata))(rm2:rmap)
  (re2:list (id * GenericValue)) : Prop :=
match (re1, re2) with
| (nil, nil) => True
| ((i1,gv1,None)::re1', (i2,gv2)::re2') =>
    i1 = i2 /\ gv_inject mi gv1 gv2 /\ incomingValues_simulation mi re1' rm2 re2'
| ((i1,gv1,Some (SBopsem.mkMD bgv1 egv1))::re1', 
   (eid2,egv2)::(bid2,bgv2)::(i2,gv2)::re2') =>
    i1 = i2 /\ gv_inject mi gv1 gv2 /\ 
    lookupAL _ rm2 i2 = Some (bid2,eid2) /\
    gv_inject mi bgv1 bgv2 /\ gv_inject mi egv1 egv2 /\
    incomingValues_simulation mi re1' rm2 re2'
| _ => False
end.

Lemma getValueViaBlockFromValuels__eql : forall B1 B2 vls,
  label_of_block B1 = label_of_block B2 ->
  getValueViaBlockFromValuels vls B1 = getValueViaBlockFromValuels vls B2.
Proof.
  intros.  
  destruct B1. destruct B2. simpl in H. subst. simpl. auto.
Qed.

Lemma get_metadata_from_list_value_l_spec : forall mi TD gl F rm1 rm2 lc1 lc2 B1 
  B2 bgv1 egv1
  (Hrsim : reg_simulation mi TD gl F rm1 rm2 lc1 lc2)
  (Heq : label_of_block B1 = label_of_block B2)
  vls v
  (HeqR1 : ret v = getValueViaBlockFromValuels vls B1)
  (HeqR4 : ret {| md_base := bgv1; md_bound := egv1 |} =
          SBopsem.get_reg_metadata TD gl rm1 v)
  (bvls0 : list_value_l) (evls0 : list_value_l)
  (HeqR5 : ret (bvls0, evls0) =
          get_metadata_from_list_value_l rm2 vls),
  exists bv2, exists ev2, exists bgv2, exists egv2,
    getValueViaBlockFromValuels bvls0 B2 = Some bv2 /\
    getValueViaBlockFromValuels evls0 B2 = Some ev2 /\
    getOperandValue TD bv2 lc2 gl = Some bgv2 /\
    getOperandValue TD ev2 lc2 gl = Some egv2 /\
    gv_inject mi bgv1 bgv2 /\
    gv_inject mi egv1 egv2.
Proof.
  intros mi TD gl F rm1 rm2 lc1 lc2.
  destruct B1. destruct B2. simpl.
  induction vls; simpl; intros; subst.
    inv HeqR1.

    remember (get_reg_metadata rm2 v) as R.
    destruct R as [[bv ev]|]; try solve [inv HeqR5].
    remember (get_metadata_from_list_value_l rm2 vls) as R'.
    destruct R' as [[baccum eaccum]|]; inv HeqR5.
    simpl.
    destruct (l2==l1); subst.
      inv HeqR1.
      exists bv. exists ev.
      destruct Hrsim as [Hrsim1 Hrsim2].
      symmetry in HeqR4.
      apply Hrsim2 in HeqR4.
      destruct HeqR4 as [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
      rewrite <- HeqR in J1. inv J1.
      exists bgv2. exists egv2. split; auto.

      eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes__reg_simulation : forall M1 M2 TD gl   mi F B1 B2 rm2 mgb
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl)
  ps1 lc1 rm1 re1 lc2 ps2,
  reg_simulation mi TD gl F rm1 rm2 lc1 lc2 ->
  getIncomingValuesForBlockFromPHINodes TD ps1 B1 gl lc1 rm1 = Some re1 ->
  label_of_block B1 = label_of_block B2 ->
  trans_phinodes rm2 ps1 = Some ps2 ->
  exists re2, 
    LLVMopsem.getIncomingValuesForBlockFromPHINodes TD ps2 B2 gl lc2 = Some re2 
      /\ incomingValues_simulation mi re1 rm2 re2.
Proof.
  induction ps1; simpl; intros lc1 rm1 re1 lc2 ps2 Hrsim Hget Heq Htrans; auto.
    inv Hget. inv Htrans. simpl. exists nil. auto.

    destruct a as [id0 t vls].
    remember (trans_phinodes rm2 ps1) as R.
    destruct R as [ps2'|]; try solve [inv Htrans].
    remember (getValueViaBlockFromValuels vls B1) as R1.
    destruct R1 as [v|]; try solve [inv Hget].
    remember (getOperandValue TD v lc1 gl) as R2.
    destruct R2 as [gv1|]; try solve [inv Hget].
    remember (getIncomingValuesForBlockFromPHINodes TD ps1 B1 gl lc1 rm1) as R3.
    destruct R3 as [idgvs|]; try solve [inv Hget].
    destruct (isPointerTypB t).
      remember (SBopsem.get_reg_metadata TD gl rm1 v) as R4.
      destruct R4 as [[bgv1 egv1]|]; inv Hget.
      remember (get_metadata_from_list_value_l rm2 vls) as R5.
      destruct R5 as [[bvls0 evls0]|]; try solve [inv Htrans].
      remember (lookupAL (id * id) rm2 id0) as R6.
      destruct R6 as [[bid0 eid0]|]; inv Htrans.
      simpl.
      eapply get_metadata_from_list_value_l_spec in HeqR5; eauto.
      destruct HeqR5 as [bv2 [ev2 [bgv2 [egv2 [Hvb [Hve [Hgetb [Hgete
        [Hinjb Hinje]]]]]]]]].
      rewrite Hvb. rewrite Hgetb. rewrite Hve. rewrite Hgete.
      erewrite <- getValueViaBlockFromValuels__eql; eauto.
      rewrite <- HeqR1.
      symmetry in HeqR2.
      eapply simulation__getOperandValue in HeqR2; eauto.
      destruct HeqR2 as [gv2 [HeqR2 Hinj2]].
      rewrite HeqR2.
      symmetry in HeqR3.
      eapply IHps1 in HeqR3; eauto.
      destruct HeqR3 as [re2 [Hgeti Hisim]].
      rewrite Hgeti.  
      exists ((eid0, egv2) :: (bid0, bgv2) :: (id0,gv2) :: re2).
      repeat (split; auto). 
      
      inv Hget. inv Htrans.
      simpl. 
      erewrite <- getValueViaBlockFromValuels__eql; eauto.
      rewrite <- HeqR1.
      symmetry in HeqR2.
      eapply simulation__getOperandValue in HeqR2; eauto.
      destruct HeqR2 as [gv2 [HeqR2 Hinj2]].
      rewrite HeqR2.
      symmetry in HeqR3.
      eapply IHps1 in HeqR3; eauto.
      destruct HeqR3 as [re2 [Hgeti Hisim]].
      rewrite Hgeti.  
      exists ((id0, gv2) :: re2).
      repeat (split; auto). 
Qed.

Lemma reg_simulation__updateAddAL_prop' : forall mi TD gl f1 rm1 rm2 lc1 lc2  
    bgv1 bgv2 egv1 egv2 bid eid mgb M1 M2 id0 gv1 gv2
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl),
  reg_simulation mi TD gl f1 rm1 rm2 lc1 lc2 ->
  ret (bid, eid) = lookupAL (id * id) rm2 id0 ->
  gv_inject mi gv1 gv2 ->
  gv_inject mi bgv1 bgv2 ->
  gv_inject mi egv1 egv2 ->
  reg_simulation mi TD gl f1 
    (updateAddAL _ rm1 id0 (mkMD bgv1 egv1)) rm2 
    (updateAddAL GenericValue lc1 id0 gv1)
    (updateAddAL _ (updateAddAL _ 
      (updateAddAL GenericValue lc2 id0 gv2) bid bgv2) eid egv2).
Admitted.

Lemma updateValuesForNewBlock__reg_simulation : forall mi TD gl F rm2 re1 rm1 lc1
    lc2 re2 lc1' rm1' lc2' M1 M2 mgb 
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl),
  reg_simulation mi TD gl F rm1 rm2 lc1 lc2 ->
  incomingValues_simulation mi re1 rm2 re2 ->
  updateValuesForNewBlock re1 lc1 rm1 = (lc1', rm1') ->
  LLVMopsem.updateValuesForNewBlock re2 lc2 = lc2' ->
  reg_simulation mi TD gl F rm1' rm2 lc1' lc2'.
Proof.
  induction re1; simpl; intros rm1 lc1 lc2 re2 lc1' rm1' lc2' M1 M2 mgb Hwfmi
    Hwfg Hrsim Hisim Hupdate Hupdate'.
    inv Hupdate. 
    destruct re2; inv Hisim; eauto.

    destruct a as [[i1 gv1] [[bgv1 bgv2]|]].
      destruct re2; try solve [inv Hisim].
      destruct p as [i2 gv2].
      destruct re2; try solve [inv Hisim].
      destruct p as [bid2 bgv2'].
      destruct re2; try solve [inv Hisim].
      destruct p as [eid2 egv2'].
      destruct Hisim as [Heq [Hginj [Hlk [Hbinj [Heinj Hisim]]]]]; subst.
      remember (updateValuesForNewBlock re1 lc1 rm1) as R.      
      destruct R as [lc' rm']. inv Hupdate.
      simpl.
      eapply reg_simulation__updateAddAL_prop'; eauto.

      destruct re2; try solve [inv Hisim].
      destruct p as [i2 gv2].
      destruct Hisim as [Heq [Hginj Hisim]]; subst.
      remember (updateValuesForNewBlock re1 lc1 rm1) as R.      
      destruct R as [lc' rm']. inv Hupdate.
      simpl.
      eapply reg_simulation__updateAddAL_lc; eauto.
        admit. admit. (*fresh*)
Qed.

Lemma switchToNewBasicBlock__reg_simulation : forall mi TD gl F rm1 rm2 lc1 lc2 
  B1 B2 l0 ps1 cs1 tmn ps2 cs2 lc1' rm1' M1 M2 mgb
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl),  
  reg_simulation mi TD gl F rm1 rm2 lc1 lc2 ->
  switchToNewBasicBlock TD (block_intro l0 ps1 cs1 tmn) B1 gl lc1 rm1 = 
    ret (lc1', rm1') ->
  label_of_block B1 = label_of_block B2 ->
  trans_phinodes rm2 ps1 = Some ps2 ->
  exists lc2', LLVMopsem.switchToNewBasicBlock TD
    (block_intro l0 ps2 cs2 tmn) B2 gl lc2 = Some lc2' /\
    reg_simulation mi TD gl F rm1' rm2 lc1' lc2'.
Proof.
  intros mi TD gl F rm1 rm2 lc1 lc2 B1 B2 l0 ps1 cs1 tmn ps2 cs2 lc1' rm1' M1 M2
    mgb Hwfmi Hwfg Hrsim Hswitch Hleq Htphis.
  unfold switchToNewBasicBlock in Hswitch.
  unfold LLVMopsem.switchToNewBasicBlock. simpl in *.
  remember (getIncomingValuesForBlockFromPHINodes TD ps1 B1 gl lc1 rm1) as R.
  destruct R; try solve [inv Hswitch].  
    symmetry in HeqR.
    eapply getIncomingValuesForBlockFromPHINodes__reg_simulation in HeqR; eauto.
    destruct HeqR as [re2 [Hget Hisim]].
    rewrite Hget. inv Hswitch.
    eapply updateValuesForNewBlock__reg_simulation in H0; eauto.
Qed.

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
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l1); 
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
    apply genLabel2Block_blocks_inv with (f:=(fheader_intro f t i0 a v)) in H; 
      auto. destruct H; eauto.
    exists l'. exists ps'. exists nil. auto.
    exists l'. exists ps2. exists nil. auto.
    exists ex_ids1. exists rm2'. exists ex_ids1'. exists ex_ids2. exists cs2.
    exists cs. 
    repeat (split; auto).
      admit. (* we do not need this fresh. *)
Qed.


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
Proof.
  intros.
  destruct_ctx_br.
  simpl in Hfresh. destruct Hfresh as [Hnotin Hfresh].
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
    symmetry in H0.
    destruct (isGVZero (los,nts) c').
      apply genLabel2Block_blocks_inv with (f:=(fheader_intro f t i0 a v)) in H0
        ; auto. destruct H0; eauto.
      apply genLabel2Block_blocks_inv with (f:=(fheader_intro f t i0 a v)) in H0
        ; auto. destruct H0; eauto.
    exists l'. exists ps'. exists nil. auto.
    exists l'. exists ps2. exists nil. auto.
    exists ex_ids1. exists rm2'. exists ex_ids1'. exists ex_ids2. exists cs2.
    exists cs. 
    repeat (split; auto).
      admit. (* we do not need this fresh. *)
Qed.

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
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Htprds [Hfsim [Hwfg 
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
  destruct HsimEC as [Hclib [HBinF [HFinPs [Htfdef [Heq0 [Hasim [Hnth [Heqb1 
    [Heqb2 [ex_ids [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [Hgenmeta [Hrsim [Hinc 
    [Hfresh [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]]; subst;
  destruct F' as [fh1' bs1'];
  destruct F2' as [fh2' bs2'];
  destruct c'; try solve [inversion HsimEC'];
  destruct HsimEC' as [Hclib' [HBinF' [HFinPs' [Htfdef' [Heq0' [Hasim' [Hnth' 
    [Heqb1' [Heqb2' [ex_ids' [rm2' [ex_ids3' [ex_ids4' [cs22' [cs23' [cs24' 
    [Hgenmeta' [Hrsim' [Hinc' [Hcall' [Hfresh' [Htcmds' [Httmn' Heq2']]]]]]]]]]]]
    ]]]]]]]]]]]; 
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
            eapply gsb_is_found; eauto. 
              eapply free_allocas_preserves_gsb; eauto.

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
            eapply gse_is_found; eauto.
              eapply free_allocas_preserves_gse; eauto.

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


