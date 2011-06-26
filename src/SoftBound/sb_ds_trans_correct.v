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

Import SB_ds_pass.

(* Simulation *)

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2'.

Lemma meminj_no_overlap__implies : forall f m,
  meminj_no_overlap f m -> Mem.meminj_no_overlap f m.
Proof.
  intros f m J.
  unfold meminj_no_overlap in J.
  unfold Mem.meminj_no_overlap.
  eauto.
Qed.

Record wf_sb_mi maxb mi Mem1 Mem2 := mk_wf_sb_mi {
  Hno_overlap : meminj_no_overlap mi Mem1;
  Hnull : mi Mem.nullptr = Some (Mem.nullptr, 0);
  Hmap1 : forall b, b >= Mem.nextblock Mem1 -> mi b = None;
  Hmap2 : forall b1 b2 delta2, 
    mi b1 = Some (b2, delta2) -> b2 < Mem.nextblock Mem2;
  mi_freeblocks: forall b, ~(Mem.valid_block Mem1 b) -> mi b = None;
  mi_mappedblocks: forall b b' delta, 
    mi b = Some(b', delta) -> Mem.valid_block Mem2 b';
  mi_range_block: forall b b' delta, 
    mi b = Some(b', delta) -> delta = 0;
  mi_bounds: forall b b' delta, 
    mi b = Some(b', delta) -> Mem.bounds Mem1 b = Mem.bounds Mem2 b';
  mi_globals : forall b, b <= maxb -> mi b = Some (b, 0)
  }.

Definition gv_inject (mi: Values.meminj) (gv gv':GenericValue) : Prop :=
let '(vals,mks) := List.split gv in 
let '(vals',mks') := List.split gv' in 
val_list_inject mi vals vals' /\ mks = mks'.

Definition reg_simulation (mi:Values.meminj) TD gl (rm1:SBopsem.rmetadata) 
  (rm2:rmap) Mem1 Mem2 (lc1 lc2:GVMap) : Prop :=
(forall i0 gv1, 
  lookupAL _ lc1 i0 = Some gv1 -> 
  exists gv2, 
    lookupAL _ lc2 i0 = Some gv2 /\ gv_inject mi gv1 gv2
) /\
(forall vp bgv1 egv1, 
  SBopsem.get_reg_metadata TD Mem1 gl rm1 vp = 
    Some (SBopsem.mkMD bgv1 egv1) -> 
  exists bv2, exists ev2, exists bgv2, exists egv2,
    get_reg_metadata rm2 vp = Some (bv2, ev2) /\
    getOperandValue TD Mem2 bv2 lc2 gl = Some bgv2 /\
    getOperandValue TD Mem2 ev2 lc2 gl = Some egv2 /\
    gv_inject mi bgv1 bgv2 /\
    gv_inject mi egv1 egv2
).

Fixpoint wf_global (maxb:Values.block) (gv:GenericValue) 
  : Prop :=
match gv with
| nil => True
| (Vptr b _,_)::gv' => b <= maxb /\ wf_global maxb gv'
| _::gv' => wf_global maxb gv'
end.

Fixpoint wf_globals maxb (gl:GVMap) : Prop :=
match gl with
| nil => True
| (_,gv)::gl' => wf_global maxb gv /\ wf_globals maxb gl'
end.

Definition mem_simulation (mi:Values.meminj) TD (max_gblock:Values.block) 
  (MM1:SBopsem.mmetadata) (Mem1 Mem2:mem) : Prop :=
Mem.mem_inj mi Mem1 Mem2 /\
0 <= max_gblock < Mem.nextblock Mem2 /\
(forall lc2 gl b ofs bgv egv als addrb addre bid0 eid0 pgv' fs F B cs tmn S Ps 
    EC v,  
  wf_globals max_gblock gl -> 
  SBopsem.get_mem_metadata TD MM1 (ptr2GV TD (Vptr b ofs)) = 
    SBopsem.mkMD bgv egv -> 
  gv_inject mi (ptr2GV TD (Vptr b ofs)) pgv' ->
  getOperandValue TD Mem2 v lc2 gl = Some pgv' ->
  exists bgv', exists egv',
  LLVMopsem.dsInsn 
    (LLVMopsem.mkState S TD Ps 
      ((LLVMopsem.mkEC F B 
        (insn_call fake_id true attrs gmd_typ gmd_fn
           ((p8,v)::
            (p8,(value_id addrb))::
            (p8,(value_id addre))::nil)::
         insn_load bid0 p8 (value_id addrb) Align.Zero::
         insn_load eid0 p8 (value_id addre) Align.Zero::   
         cs) 
        tmn lc2 als)
        ::EC) gl fs Mem2)
    (LLVMopsem.mkState S TD Ps 
       ((LLVMopsem.mkEC F B cs tmn 
         (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als)::EC) 
        gl fs Mem2)
    trace_nil /\
    gv_inject mi bgv bgv' /\
    gv_inject mi egv egv'
).

Definition alloca_simulation (mi:Values.meminj) (b1 b2:Values.block) : Prop := 
  mi b1 = Some(b2, 0).

Fixpoint allocas_simulation_suffix (mi:Values.meminj) 
  (als1 als2:list Values.block) : Prop := 
match als1, als2 with
| nil, nil => True
| b1::als1', b2::als2' => alloca_simulation mi b1 b2 /\
    allocas_simulation_suffix mi als1' als2'
| _, _ => False
end.

Definition allocas_simulation TD (mi:Values.meminj) lc2 addrb addre 
  (als1 als2:list mblock) : Prop := 
let als1' := rev als1 in
let als2' := rev als2 in
match als2' with
| baddrb::baddre::als2'' => allocas_simulation_suffix mi als1 als2 /\
    lookupAL _ lc2 addrb = Some (ptr2GV TD (Vptr baddrb (Int.zero 31))) /\
    lookupAL _ lc2 addre = Some (ptr2GV TD (Vptr baddre (Int.zero 31))) /\
    forall b1 b2 d, mi b1 = Some (b2, d) -> b2 <> baddrb /\ b2 <> baddre
| _ => False
end.

Definition sbEC_simulates_EC_tail (TD:TargetData) M1 M2 gl (mi:Values.meminj) 
  (sbEC:SBopsem.ExecutionContext) (EC:LLVMopsem.ExecutionContext) : Prop :=
  match (sbEC, EC) with
  | (SBopsem.mkEC f1 b1 ((insn_call i0 nr ca t0 v p)::cs13) tmn1 lc1 rm1 als1, 
     LLVMopsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       let '(fdef_intro fh1 bs1) := f1 in
       let '(fdef_intro fh2 bs2) := f2 in
       let '(los, nts) := TD in
       trans_fdef nts f1 = Some f2 /\
       tmn1 = tmn2 /\
       (exists n, nth_error bs1 n = Some b1 /\ nth_error bs2 n = Some b2) /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++(insn_call i0 nr ca t0 v p)::cs13) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       exists ex_ids, exists rm2, 
       exists addrb, exists ex_ids1, exists addre, exists ex_ids2, 
       exists ex_ids3, exists ex_ids4, exists cs22, exists cs23, exists cs24,
         gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids, rm2) /\
         reg_simulation mi TD gl rm1 rm2 M1 M2 lc1 lc2 /\
         (addrb,ex_ids1) = mk_tmp ex_ids /\
         (addre,ex_ids2) = mk_tmp ex_ids1 /\
         allocas_simulation TD mi lc2 addrb addre als1 als2 /\
         incl ex_ids2 ex_ids3 /\ 
         call_suffix i0 nr ca t0 v p rm2 = Some cs22 /\
         trans_cmds ex_ids1 addrb addre rm2 cs13 = Some (ex_ids4,cs23) /\
         trans_terminator rm2 tmn1 = Some cs24 /\
         cs2 = cs22 ++ cs23 ++ cs24
  | _ => False
  end.

Definition sbEC_simulates_EC_head (TD:TargetData) M1 M2 gl (mi:Values.meminj) 
  (sbEC:SBopsem.ExecutionContext) (EC:LLVMopsem.ExecutionContext) : Prop :=
  match (sbEC, EC) with
  | (SBopsem.mkEC f1 b1 cs12 tmn1 lc1 rm1 als1, 
     LLVMopsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       let '(fdef_intro fh1 bs1) := f1 in
       let '(fdef_intro fh2 bs2) := f2 in
       let '(los, nts) := TD in
       trans_fdef nts f1 = Some f2 /\
       tmn1 = tmn2 /\
       (exists n, nth_error bs1 n = Some b1 /\ nth_error bs2 n = Some b2) /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs12) tmn1) /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       exists ex_ids, exists rm2, 
       exists addrb, exists ex_ids1, exists addre, exists ex_ids2, 
       exists ex_ids3, exists ex_ids4, exists cs22, exists cs23,
         gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids, rm2) /\
         reg_simulation mi TD gl rm1 rm2 M1 M2 lc1 lc2 /\
         (addrb,ex_ids1) = mk_tmp ex_ids /\
         (addre,ex_ids2) = mk_tmp ex_ids1 /\
         allocas_simulation TD mi lc2 addrb addre als1 als2 /\
         incl ex_ids2 ex_ids3 /\ 
         trans_cmds ex_ids1 addrb addre rm2 cs12 = Some (ex_ids4,cs22) /\
         trans_terminator rm2 tmn1 = Some cs23 /\
         cs2 = cs22 ++ cs23
  end.

Fixpoint sbECs_simulate_ECs_tail (TD:TargetData) M1 M2 gl (mi:Values.meminj) 
  (sbECs:SBopsem.ECStack) (ECs:LLVMopsem.ECStack) : Prop :=
  match sbECs, ECs with
  | nil, nil => True
  | sbEC::sbECs', EC::ECs' => 
      sbEC_simulates_EC_tail TD M1 M2 gl mi sbEC EC /\ 
      sbECs_simulate_ECs_tail TD M1 M2 gl mi sbECs' ECs'
  | _, _ => False
  end.

Definition sbECs_simulate_ECs (TD:TargetData) M1 M2 gl (mi:Values.meminj) 
  (sbECs:SBopsem.ECStack) (ECs:LLVMopsem.ECStack) : Prop :=
  match sbECs, ECs with
  | sbEC::sbECs', EC::ECs' => 
      sbEC_simulates_EC_head TD M1 M2 gl mi sbEC EC /\ 
      sbECs_simulate_ECs_tail TD M1 M2 gl mi sbECs' ECs'
  | _, _ => False
  end.

Definition sbState_simulates_State (mi:Values.meminj) (mgb:Values.block) 
  (sbSt:SBopsem.State) (St:LLVMopsem.State) : Prop :=
  match (sbSt, St) with
  | (SBopsem.mkState S1 TD1 Ps1 ECs1 gl1 fs1 M1 MM1,
     LLVMopsem.mkState S2 TD2 Ps2 ECs2 gl2 fs2 M2) =>
      let '(los, nts) := TD1 in
      trans_system S1 = Some S2 /\ 
      TD1 = TD2 /\ 
      trans_products nts Ps1 = trans_products nts Ps2 /\ 
      sbECs_simulate_ECs TD1 M1 M2 gl1 mi ECs1 ECs2 /\
      gl1 = gl2 /\ 
      fs1 = fs2 /\ 
      wf_sb_mi mgb mi M1 M2 /\
      mem_simulation mi TD1 mgb MM1 M1 M2 
  end.

Lemma free_allocas_sim : forall TD M1 als1 M2 mi als2 M1' MM mgb lc1 lc2 rm1 rm2 
    gl ECsc1 ECs2 addrb addre lc,
  free_allocas TD M1 als1 = Some M1' ->
  allocas_simulation TD mi lc addrb addre als1 als2 ->
  mem_simulation mi TD mgb MM M1 M2 ->
  reg_simulation mi TD gl rm1 rm2 M1 M2 lc1 lc2 ->
  sbECs_simulate_ECs_tail TD M1 M2 gl mi ECsc1 ECs2 ->
  wf_sb_mi mgb mi M1 M2 ->
  exists M2', free_allocas TD M2 als2 = Some M2' /\ 
    mem_simulation mi TD mgb MM M1' M2' /\
    reg_simulation mi TD gl rm1 rm2 M1' M2' lc1 lc2 /\
    sbECs_simulate_ECs_tail TD M1' M2' gl mi ECsc1 ECs2 /\
    wf_sb_mi mgb mi M1' M2'.
Admitted.

Definition sb_fnattrs := fnattrs_intro linkage_external visibility_default 
  callconv_ccc nil nil.

Axiom dstk_spec : forall M, 
  LLVMopsem.callExternalFunction M dstk_fid nil = Some (None, M).

Axiom dstk_is_found : forall TD M Ps gl lc fs, 
  LLVMopsem.lookupExFdecViaGV TD M Ps gl lc fs dstk_fn = Some
    (fdec_intro (fheader_intro sb_fnattrs dstk_typ dstk_fid nil false)).

Definition int2GV n :=
  (Vint 31 (Int.repr 31 (INTEGER.to_Z n)), AST.Mint 31)::nil.

Axiom stk_ret_sim : forall TD M1 M2 mi MM mgb lc1 lc2 rm1 rm2 gl ECsc1 ECs2 bgv
    egv,
  mem_simulation mi TD mgb MM M1 M2 ->
  reg_simulation mi TD gl rm1 rm2 M1 M2 lc1 lc2 ->
  sbECs_simulate_ECs_tail TD M1 M2 gl mi ECsc1 ECs2 ->
  wf_sb_mi mgb mi M1 M2 ->
  exists M2',  exists M2'',
    LLVMopsem.callExternalFunction M2 sbase_fid (bgv::int2GV 0%Z::nil) = 
      Some (None, M2') /\
    LLVMopsem.callExternalFunction M2' sbound_fid (egv::int2GV 0%Z::nil) = 
      Some (None, M2'') /\
    mem_simulation mi TD mgb MM M1 M2'' /\
    reg_simulation mi TD gl rm1 rm2 M1 M2'' lc1 lc2 /\
    sbECs_simulate_ECs_tail TD M1 M2'' gl mi ECsc1 ECs2 /\
    wf_sb_mi mgb mi M1 M2'' /\
    LLVMopsem.callExternalFunction M2'' gbase_fid [int2GV 0%Z] = 
      Some (Some bgv, M2'') /\
    LLVMopsem.callExternalFunction M2'' gbound_fid [int2GV 0%Z] = 
      Some (Some egv, M2'').

Axiom sbase_is_found : forall TD M Ps gl lc fs, 
  LLVMopsem.lookupExFdecViaGV TD M Ps gl lc fs sbase_fn = Some
    (fdec_intro (fheader_intro sb_fnattrs dstk_typ sbase_fid nil false)).

Axiom sbound_is_found : forall TD M Ps gl lc fs, 
  LLVMopsem.lookupExFdecViaGV TD M Ps gl lc fs sbound_fn = Some
    (fdec_intro (fheader_intro sb_fnattrs dstk_typ sbound_fid nil false)).

Axiom gbase_is_found : forall TD M Ps gl lc fs, 
  LLVMopsem.lookupExFdecViaGV TD M Ps gl lc fs gbase_fn = Some
    (fdec_intro (fheader_intro sb_fnattrs dstk_typ gbase_fid nil false)).

Axiom gbound_is_found : forall TD M Ps gl lc fs, 
  LLVMopsem.lookupExFdecViaGV TD M Ps gl lc fs gbound_fn = Some
    (fdec_intro (fheader_intro sb_fnattrs dstk_typ gbound_fid nil false)).

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
Case "dsReturn". Focus.
  destruct St as [S2 TD2 Ps2 ECs2 gl2 fs2 M2].
  destruct TD as [los nts].
  destruct Hsim as [Htsym [Heq1 [Htps [HsimECs [Heq2 [Heq3 [Hwfmi HsimM]]]]]]];
    subst.
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs].
  simpl in HsimECs.
  destruct HsimECs as [HsimEC HsimECs].
  destruct ECs2 as [|[F2' B2' cs2' tmn2' lc2' als2'] ECs2];
    try solve [inversion HsimECs].
  destruct HsimECs as [HsimEC' HsimECs].
  destruct F as [fh1 bs1].
  destruct F2 as [fh2 bs2].
  destruct HsimEC as [Htfdef [Heq0 [Hnth [Heqb1 [Heqb2 [ex_ids [rm2 
    [addrb [ex_ids1 [addre [ex_ids2 [ex_ids3 [ex_ids4 [cs22 [cs23 
    [Hgenmeta [Hrsim [Hmk1 [Hmk2 [Hals 
    [Hinc [Htcmds [Httmn Heq1]]]]]]]]]]]]]]]]]]]]]]]; subst.
  destruct F' as [fh1' bs1'].
  destruct F2' as [fh2' bs2'].
  destruct c'; try solve [inversion HsimEC'].  
  destruct HsimEC' as [Htfdef' [Heq0' [Hnth' [Heqb1' [Heqb2'
    [ex_ids' [rm2' [addrb' [ex_ids1' [addre' [ex_ids2' 
    [ex_ids3' [ex_ids4' [cs22' [cs23' [cs24' 
    [Hgenmeta' [Hrsim' [Hmk1' [Hmk2' [Hals' 
    [Hinc' [Hcall' [Htcmds' [Httmn' Heq1']]]]]]]]]]]]]]]]]]]]]]]]]; subst.
  inv Htcmds.
  simpl in H1.
  unfold call_suffix in Hcall'.
  unfold SBopsem.returnUpdateLocals in H1.
  remember (SBopsem.returnResult (los, nts) Mem' RetTy Result lc rm gl2) as Ret.
  destruct Ret as [[gr md]|]; try solve [inv H1].
  unfold SBopsem.returnResult in HeqRet.
  remember (getOperandValue (los, nts) Mem' Result lc gl2) as ogr.
  destruct ogr as [ogr|]; try solve [inv HeqRet].
  destruct n.
  SCase "nret = true".
    inv Hcall'.
    inv H1.
    simpl in Httmn.
    destruct (isPointerTypB RetTy).
    SSCase "rt is ptr". Focus.
      remember (SBopsem.get_reg_metadata (los, nts) Mem' gl2 rm Result) as oRmd.
      destruct oRmd as [[bgv1 egv1]|]; inv HeqRet.
      assert (exists bv2, exists ev2, exists bgv2, exists egv2,
        get_reg_metadata rm2 Result = Some (bv2, ev2) /\
        getOperandValue (los,nts) M2 bv2 lc2 gl2 = Some bgv2 /\
        getOperandValue (los,nts) M2 ev2 lc2 gl2 = Some egv2 /\
        gv_inject mi bgv1 bgv2 /\
        gv_inject mi egv1 egv2) as J.
        clear - HeqoRmd Hrsim. 
        destruct Hrsim as [_ Hrsim].
        apply Hrsim; auto.
          admit. (* const2GV *)
      destruct J as [bv2 [ev2 [bgv2 [egv2 [Hgetrmd [Hgetbgv2 [Hgetegv2 [Hinj1 
        Hinj2]]]]]]]]. rewrite Hgetrmd in Httmn. inv Httmn.
Admitted.
(*
      destruct (@stk_ret_sim (los,nts) Mem M2 mi MM mgb lc'' lc2' rm'' rm2'
        gl2 EC ECs2 bv null) as [M2' [M2'' [Hsbase [Hsbound [Hmsim3 [Hrsim3
        [HsimECs3 [Hwfmi3 [Hgbase Hgbound]]]]]]]]]; auto.
      eapply free_allocas_sim with (rm1:=rm'')(rm2:=rm2')(lc1:=lc'')(lc2:=lc2') 
        in HsimECs3; eauto.
      destruct HsimECs3 as [M2''' [Hfree2' [Hmsim2' [Hrsim2' [HsimECs2' Hwfmi2']]
        ]]].
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
              ((insn_call fake_id true attrs sbound_typ sbound_fn 
                  ((p8, vnullp8)::(i32, vint0) :: nil))::nil)
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 true c t (wrap_call v) p)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2')).
          eapply LLVMopsem.dsExCall with (fid:=sbase_fid)
            (gvs:=(null :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply sbase_is_found; eauto.
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
          eapply LLVMopsem.dsExCall with (fid:=sbound_fid)
            (gvs:=(null :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply sbound_is_found; eauto.
        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
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
          destruct Heqb1' as [l1' [ps1' [cs11' Heqb1']]]; subst.
          exists l1'. exists ps1'. 
          exists (cs11' ++ [insn_call i0 true c t v p]). 
          simpl_env. auto.

          destruct Heqb2' as [l2' [ps2' [cs21' Heqb2']]]; subst.
          exists l2'. exists ps2'. exists (cs21' ++
              [insn_call i0 true c t (wrap_call v) p] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists addrb'. exists ex_ids1'. exists addre'. exists ex_ids2'. 
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          repeat (split; auto).


    SSCase "rt isnt ptr".
      inv Httmn.
      destruct (@stk_ret_sim (los,nts) Mem M2 mi MM mgb lc'' lc2' rm'' rm2'
        gl2 EC ECs2 null null) as [M2' [M2'' [Hsbase [Hsbound [Hmsim3 [Hrsim3
        [HsimECs3 [Hwfmi3 [Hgbase Hgbound]]]]]]]]]; auto.
      eapply free_allocas_sim with (rm1:=rm'')(rm2:=rm2')(lc1:=lc'')(lc2:=lc2') 
        in HsimECs3; eauto.
      destruct HsimECs3 as [M2''' [Hfree2' [Hmsim2' [Hrsim2' [HsimECs2' Hwfmi2']]
        ]]].
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
              ((insn_call fake_id true attrs sbound_typ sbound_fn 
                  ((p8, vnullp8)::(i32, vint0) :: nil))::nil)
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 true c t (wrap_call v) p)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2')).
          eapply LLVMopsem.dsExCall with (fid:=sbase_fid)
            (gvs:=(null :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply sbase_is_found; eauto.
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
          eapply LLVMopsem.dsExCall with (fid:=sbound_fid)
            (gvs:=(null :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply sbound_is_found; eauto.
        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
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
          destruct Heqb1' as [l1' [ps1' [cs11' Heqb1']]]; subst.
          exists l1'. exists ps1'. 
          exists (cs11' ++ [insn_call i0 true c t v p]). 
          simpl_env. auto.

          destruct Heqb2' as [l2' [ps2' [cs21' Heqb2']]]; subst.
          exists l2'. exists ps2'. exists (cs21' ++
              [insn_call i0 true c t (wrap_call v) p] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists addrb'. exists ex_ids1'. exists addre'. exists ex_ids2'. 
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          repeat (split; auto).

  SCase "nret = false".
    remember (getOperandValue (los, nts) Mem' Result lc gl2) as R.
    destruct R; try solve [inv H1].
    destruct (SBopsem.isReturnPointerTypB t); simpl in Hcall'.
    SSCase "ct is ptr".
      simpl in Httmn.
      destruct (isPointerTypB RetTy).
    SSSCase "rt is ptr".
      destruct (get_reg_metadata rm2 Result) as [[bv ev]|]; inv Httmn.



    inv H1.
    inv Hcall'.

    SSCase "rt isnt ptr".
      inv Httmn.
      destruct (@stk_ret_sim (los,nts) Mem M2 mi MM mgb lc'' lc2' rm'' rm2'
        gl2 EC ECs2 null null) as [M2' [M2'' [Hsbase [Hsbound [Hmsim3 [Hrsim3
        [HsimECs3 [Hwfmi3 [Hgbase Hgbound]]]]]]]]]; auto.
      eapply free_allocas_sim with (rm1:=rm'')(rm2:=rm2')(lc1:=lc'')(lc2:=lc2') 
        in HsimECs3; eauto.
      destruct HsimECs3 as [M2''' [Hfree2' [Hmsim2' [Hrsim2' [HsimECs2' Hwfmi2']]
        ]]].
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
              ((insn_call fake_id true attrs sbound_typ sbound_fn 
                  ((p8, vnullp8)::(i32, vint0) :: nil))::nil)
              (insn_return rid RetTy Result) lc2 als2)::
             (LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call i0 true c t (wrap_call v) p)::
               (insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2')).
          eapply LLVMopsem.dsExCall with (fid:=sbase_fid)
            (gvs:=(null :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply sbase_is_found; eauto.
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
          eapply LLVMopsem.dsExCall with (fid:=sbound_fid)
            (gvs:=(null :: int2GV 0 :: nil))(oresult:=None); eauto.
            eapply sbound_is_found; eauto.
        rewrite <- (@trace_app_nil__eq__trace trace_nil).
        apply LLVMopsem.dsop_star_cons with (state2:=
          (LLVMopsem.mkState S2 (los, nts) Ps2
            ((LLVMopsem.mkEC (fdef_intro fh2' bs2') B2'
              ((insn_call fake_id true attrs dstk_typ dstk_fn nil)::
              (cs23' ++ cs24'))
              tmn2' lc2' als2'):: ECs2)
            gl2 fs2 M2''')).
          eapply LLVMopsem.dsReturn; eauto.
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
          destruct Heqb1' as [l1' [ps1' [cs11' Heqb1']]]; subst.
          exists l1'. exists ps1'. 
          exists (cs11' ++ [insn_call i0 true c t v p]). 
          simpl_env. auto.

          destruct Heqb2' as [l2' [ps2' [cs21' Heqb2']]]; subst.
          exists l2'. exists ps2'. exists (cs21' ++
              [insn_call i0 true c t (wrap_call v) p] ++
              [insn_call fake_id true attrs dstk_typ dstk_fn nil]). 
          simpl_env. auto.
 
          exists ex_ids'. exists rm2'.
          exists addrb'. exists ex_ids1'. exists addre'. exists ex_ids2'. 
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          repeat (split; auto).
*)

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
