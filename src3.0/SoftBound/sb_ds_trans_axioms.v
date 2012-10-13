Require Import Values.
Require Import vellvm.
Require Import events.
Require Import Memory.
Require Import alist.
Require Import Integers.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import opsem.
Require Import dopsem.
Require Import sb_def.
Require Import memory_sim.
Require Import genericvalues_inject.
Require Import sb_ds_sim.
Require Import sb_ds_trans.

Import SB_ds_pass.

(* This file defines the specification of external functions used by SoftBound. 
 *)
Definition sb_fnattrs := fnattrs_intro linkage_external visibility_default
  callconv_ccc nil nil.

Definition gmmd_args v :=
  ((p8,nil,v)::(p8,nil,vnullp8):: (i32,nil,vint1)::(p32,nil,vnullp32)
   :: @nil param).
Hint Unfold gmmd_args.

Axiom free_doesnt_change_gmmd : forall M2 b2 lo hi Mem2' lc2 gl als
   bid0 eid0 bgv' egv' fs F B cs tmn S Ps EC TD v,
  Mem.free M2 b2 lo hi = ret Mem2' ->
  @Opsem.sop_star DGVs (OpsemAux.mkCfg S TD Ps gl fs)
    (Opsem.mkState
      ((Opsem.mkEC F B
        (insn_call bid0 false attrs gmb_typ None gmb_fn (gmmd_args v)::
         insn_call eid0 false attrs gme_typ None gme_fn (gmmd_args v)::
         cs)
        tmn lc2 als)
        ::EC) M2)
    (Opsem.mkState
       ((Opsem.mkEC F B cs tmn
         (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als)::EC)
        M2)
    E0 ->
  Opsem.sop_star (OpsemAux.mkCfg S TD Ps gl fs)
    (Opsem.mkState
      ((Opsem.mkEC F B
        (insn_call bid0 false attrs gmb_typ None gmb_fn (gmmd_args v)::
         insn_call eid0 false attrs gme_typ None gme_fn (gmmd_args v)::
         cs)
        tmn lc2 als)
        ::EC) Mem2')
    (Opsem.mkState
       ((Opsem.mkEC F B cs tmn
         (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als)::EC)
        Mem2')
    E0.

Axiom get_mmetadata_fn__alloc__preserve : forall Mem2 lo hi Mem2' mb2
  (HeqR2 : (Mem2', mb2) = Mem.alloc Mem2 lo hi)
  (lc2 : DGVMap) (gl : GVMap) (als : list mblock) (fs : GVMap) (F : fdef)
  (B : block) (cs : list cmd) (tmn : terminator) (S : system) (Ps : list product)
  (EC : list Opsem.ExecutionContext) (bgv' : GenericValue)
  (egv' : GenericValue) bid0 eid0 TD v als,
  Opsem.sop_star (OpsemAux.mkCfg S TD Ps gl fs)
     (Opsem.mkState ((Opsem.mkEC F B
        (insn_call bid0 false attrs gmb_typ None gmb_fn (gmmd_args v) ::
         insn_call eid0 false attrs gme_typ None gme_fn (gmmd_args v) ::
         cs) tmn lc2 als) :: EC) Mem2)
     (Opsem.mkState ((Opsem.mkEC F B cs tmn
        (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als) :: EC)
        Mem2)
     E0 ->
  Opsem.sop_star (OpsemAux.mkCfg S TD Ps gl fs)
     (Opsem.mkState ((Opsem.mkEC F B
        (insn_call bid0 false attrs gmb_typ None gmb_fn (gmmd_args v) ::
         insn_call eid0 false attrs gme_typ None gme_fn (gmmd_args v) ::
         cs) tmn lc2 als) :: EC) Mem2')
     (Opsem.mkState ((Opsem.mkEC F B cs tmn
        (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als) :: EC)
        Mem2')
     E0.

Axiom get_mmetadata_fn__alloc__zeroout : forall Mem2 lo hi Mem2' mb2 cm
  (HeqR2 : (Mem2', mb2) = Mem.alloc Mem2 lo hi)
  (lc2 : DGVMap) (gl : GVMap) (als : list mblock) (fs : GVMap) (F : fdef)
  (B : block) (cs : list cmd) (tmn : terminator) (S : system) (Ps : list product)
  (EC : list Opsem.ExecutionContext) bid0 eid0 TD v als ofs,
  getOperandValue TD v lc2 gl =
    Some ((Vptr mb2 (Int.add 31 ofs (Int.repr 31 0)), cm)::nil) ->
  Opsem.sop_star (OpsemAux.mkCfg S TD Ps gl fs)
     (Opsem.mkState ((Opsem.mkEC F B
        (insn_call bid0 false attrs gmb_typ None gmb_fn (gmmd_args v) ::
         insn_call eid0 false attrs gme_typ None gme_fn (gmmd_args v) ::
         cs) tmn lc2 als) :: EC) Mem2')
     (Opsem.mkState ((Opsem.mkEC F B cs tmn
        (updateAddAL _ (updateAddAL _ lc2 bid0 null) eid0 null) als) :: EC)
        Mem2')
     E0.

Axiom assert_mptr_fn__ok : forall
  (lc2 : DGVMap)
  (Mem2 : mem)
  (mi : MoreMem.meminj)
  (t : typ)
  (vp : value)
  (ptmp : id)
  (btmp : id)
  (etmp : id)
  (TD : TargetData)
  (gl : GVMap)
  (als : list mblock)
  (gvp : GenericValue) blk bofs eofs
  (b : Values.block)
  (i0 : int32)
  (HeqR0 : ret Vptr b i0 = GV2ptr TD (getPointerSize TD) gvp)
  (s : sz)
  (HeqR7 : ret s = getTypeAllocSize TD t)
  (J : zeq b blk && zle (Int.signed 31 bofs) (Int.signed 31 i0) &&
      zle (Int.signed 31 i0 + Size.to_Z s) (Int.signed 31 eofs))
  (gvp2 : GenericValue)
  (H00 : getOperandValue TD vp lc2 gl = ret gvp2)
  (H01 : gv_inject mi gvp gvp2)
  (bv2 : value)
  (ev2 : value)
  (bgv2 : GenericValue)
  (egv2 : GenericValue)
  (J2 : getOperandValue TD bv2 lc2 gl = ret bgv2)
  (J3 : getOperandValue TD ev2 lc2 gl = ret egv2)
  (J4 : gv_inject mi ((Vptr blk bofs, AST.Mint 31) :: nil) bgv2)
  (J5 : gv_inject mi ((Vptr blk eofs, AST.Mint 31) :: nil) egv2)
  S2 Ps2 F2 B2 cs2' als2 fs2 M2 tmn2 ECs2,
  Opsem.sInsn (OpsemAux.mkCfg S2 TD Ps2 gl fs2)
       (Opsem.mkState
          ((Opsem.mkEC F2 B2
            (insn_call fake_id true attrs assert_typ None assert_fn
              ((p8,nil,bv2)::(p8,nil,ev2)::(p8,nil,value_id ptmp)::
                 (i32,nil,type_size t)::(i32,nil,vint1) :: nil)::
             cs2') tmn2
            (updateAddAL _ lc2 ptmp gvp2)
             als2)::
            ECs2) M2)
       (Opsem.mkState
          ((Opsem.mkEC F2 B2
            cs2' tmn2
            (updateAddAL _ lc2 ptmp gvp2)
             als2)::
            ECs2) M2) E0.

Axiom simulation__set_mmetadata_fn : forall lc2 gl b ofs blk bofs eofs als2 tmn2 ECs2
  pgv' bgv' egv' mi ptmp bv0 ev0 MM1 Mem1 Mem2 rm v gmb fs2 gl2 cs F2 B2 TD
  Ps2 S2 cm,
  mem_simulation mi TD gmb MM1 Mem1 Mem2 ->
  SBspecAux.get_reg_metadata TD gl rm v = Some (SBspecAux.mkMD blk bofs eofs) ->
  lookupAL _ lc2 ptmp = Some pgv' ->
  @Opsem.getOperandValue DGVs TD bv0 lc2 gl = Some bgv' ->
  getOperandValue TD ev0 lc2 gl = Some egv' ->
  gv_inject mi ((Vptr b ofs,cm)::nil) pgv' ->
  gv_inject mi ((Vptr blk bofs, AST.Mint 31)::nil) bgv' ->
  gv_inject mi ((Vptr blk eofs, AST.Mint 31)::nil) egv' ->
  exists Mem2',
    Opsem.sInsn (OpsemAux.mkCfg S2 TD Ps2 gl2 fs2)
      (Opsem.mkState
          ((Opsem.mkEC F2 B2
              (insn_call fake_id true attrs smmd_typ None smmd_fn
                ((p8,nil,value_id ptmp) :: (p8,nil,bv0) :: (p8,nil,ev0)
                  :: (p8,nil,vnullp8) :: (i32,nil,vint1) :: (i32,nil,vint1)
                  :: nil)::
               cs) tmn2 lc2
             als2)::
            ECs2) Mem2)
      (Opsem.mkState
          ((Opsem.mkEC F2 B2
              cs tmn2 lc2 als2)::
            ECs2) Mem2') E0 /\
      mem_simulation mi TD gmb
        (SBspecAux.set_mem_metadata TD MM1 ((Vptr b ofs,cm)::nil)
        (SBspecAux.mkMD blk bofs eofs)) Mem1 Mem2'.

Axiom set_mmetadata_fn__prop : forall TD Mem1 lc2 als2 Mem2 S2 Ps2 F2
   B2 tmn2 cs fs2 gl2 ECs2 lp,
  @Opsem.sInsn DGVs (OpsemAux.mkCfg S2 TD Ps2 gl2 fs2)
      (Opsem.mkState
          ((Opsem.mkEC F2 B2
              (insn_call fake_id true attrs smmd_typ None smmd_fn lp ::
               cs) tmn2 lc2
             als2)::
            ECs2) Mem1)
      (Opsem.mkState
          ((Opsem.mkEC F2 B2 cs tmn2 lc2 als2)::
            ECs2) Mem2) E0 ->
  Mem.nextblock Mem1 <= Mem.nextblock Mem2 /\
  (forall b2, Mem.valid_block Mem1 b2 -> Mem.valid_block Mem2 b2) /\
  (forall b0, Mem.bounds Mem1 b0 = Mem.bounds Mem2 b0).

Axiom dstk_spec : forall TD gl M, 
  callExternalOrIntrinsics TD gl M dstk_fid dstk_typ nil
    (deckind_external eid_other) nil = Some (None, events.E0, M).

Axiom dstk_is_found : forall TD Ps gl lc fs,
  exists fv,
  @Opsem.getOperandValue DGVs TD dstk_fn gl lc = Some fv /\
  OpsemAux.lookupExFdecViaPtr Ps fs fv = Some
    (fdec_intro (fheader_intro sb_fnattrs dstk_typ dstk_fid nil None) 
       (deckind_external eid_other)).

Definition int2GV n :=
  (Vint 31 (Int.repr 31 (INTEGER.to_Z n)), AST.Mint 31)::nil.

Axiom stk_ret_sim : forall TD gl M1 M2 mi mgb MM bgv egv,
  mem_simulation mi TD mgb MM M1 M2 ->
  wf_sb_mi mgb mi M1 M2 ->
  exists M2',  exists M2'',
    callExternalOrIntrinsics TD gl M2 ssb_fid ssb_typ nil
      (deckind_external eid_other) (bgv::int2GV 0%Z::nil) 
        = Some (None, events.E0, M2') /\
    callExternalOrIntrinsics TD gl M2' sse_fid sse_typ nil
      (deckind_external eid_other) (egv::int2GV 0%Z::nil) 
        = Some (None, events.E0, M2'') /\
    mem_simulation mi TD mgb MM M1 M2'' /\
    wf_sb_mi mgb mi M1 M2'' /\
    callExternalOrIntrinsics TD gl M2'' gsb_fid gsb_typ nil
      (deckind_external eid_other) [int2GV 0%Z] 
        = Some (Some bgv, events.E0, M2'') /\
    callExternalOrIntrinsics TD gl M2'' gse_fid gse_typ nil
      (deckind_external eid_other) [int2GV 0%Z] 
        = Some (Some egv, events.E0, M2'').

Axiom ssb_is_found : forall TD Ps gl lc fs,
  exists fv,
  @Opsem.getOperandValue DGVs TD ssb_fn gl lc = Some fv /\
  OpsemAux.lookupExFdecViaPtr Ps fs fv = Some
    (fdec_intro (fheader_intro sb_fnattrs ssb_typ ssb_fid nil None)
      (deckind_external eid_other)).

Axiom sse_is_found : forall TD Ps gl lc fs,
  exists fv,
  @Opsem.getOperandValue DGVs TD sse_fn gl lc = Some fv /\
  OpsemAux.lookupExFdecViaPtr Ps fs fv = Some
    (fdec_intro (fheader_intro sb_fnattrs sse_typ sse_fid nil None)
      (deckind_external eid_other)).

Axiom gsb_is_found : forall TD Ps gl lc fs,
  exists fv,
  @Opsem.getOperandValue DGVs TD gsb_fn gl lc = Some fv /\
  OpsemAux.lookupExFdecViaPtr Ps fs fv = Some
    (fdec_intro (fheader_intro sb_fnattrs gsb_typ gsb_fid nil None)
       (deckind_external eid_other)).

Axiom gse_is_found : forall TD Ps gl lc fs,
  exists fv,
  @Opsem.getOperandValue DGVs TD gse_fn gl lc = Some fv /\
  OpsemAux.lookupExFdecViaPtr Ps fs fv = Some
    (fdec_intro (fheader_intro sb_fnattrs gse_typ gse_fid nil None)
      (deckind_external eid_other)).

Axiom free_doesnt_change_gsb : forall TD M1 z gv M2 als gl,
  callExternalOrIntrinsics TD gl M1 gsb_fid gsb_typ nil
    (deckind_external eid_other) [int2GV z] = ret (ret gv, events.E0, M1) ->
  free_allocas TD M1 als = ret M2 ->
  callExternalOrIntrinsics TD gl M2 gsb_fid gsb_typ nil
    (deckind_external eid_other) [int2GV z] = ret (ret gv, events.E0, M2).

Axiom free_doesnt_change_gse : forall TD M1 z gv M2 als gl,
  callExternalOrIntrinsics TD gl M1 gse_fid gse_typ nil
    (deckind_external eid_other) [int2GV z] = ret (ret gv, events.E0, M1) ->
  free_allocas TD M1 als = ret M2 ->
  callExternalOrIntrinsics TD gl M2 gse_fid gse_typ nil
    (deckind_external eid_other) [int2GV z] = ret (ret gv, events.E0, M2).

Axiom wrapper_fid_is_identical : forall fid, wrapper_fid fid = fid.

Axiom lookupFdefViaPtr_isnt_callLib : forall Ps1 fs1 fv fa rt fid la va
    lb,
  OpsemAux.lookupFdefViaPtr Ps1 fs1 fv =
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  isCallLib fid = false.

Axiom shadow_stack_init : forall la ogvs lc' rm' gl mi lc2 lp cs1 rm2 nts los
    Mem0 MM mgb fa rt fid va lb fs2 gl2 als2 tmn2 cs3 cs4 bs3 S2 Ps2 B2 cs2' tmn1
    ps1 l1 fv rt1 va1 noret0 ca rid cs22 cs23 bs2 fh2 ECs2 M2 rm3 ex_ids3 fptr,
  wf_sb_mi mgb mi Mem0 M2 ->
  mem_simulation mi (los, nts) mgb MM Mem0 M2 ->
  @SBspec.initLocals DGVs (los, nts) la ogvs = Some (lc', rm') ->
  params_simulation (los,nts) gl mi lc2 ogvs 1 cs1 ->
  ret cs1 = trans_params rm2 lp 1 ->
  gen_metadata_fdef nts
         (getFdefLocs (fdef_intro (fheader_intro fa rt fid la va) lb)) nil
         (fdef_intro (fheader_intro fa rt fid la va) lb) =
       ret (ex_ids3, rm3) ->
  trans_args rm3 la 1 = ret cs3 ->
  Opsem.getOperandValue (los, nts) (wrap_call fv) lc2 gl2 = Some fptr ->
  OpsemAux.lookupFdefViaPtr Ps2 fs2 fptr =
          ret fdef_intro (fheader_intro fa rt (wrapper_fid fid) la va)
                ((l1, stmts_intro ps1 (cs3 ++ cs4) tmn1) :: bs3) ->
  exists M2', exists lc2',
  Opsem.sop_star (OpsemAux.mkCfg S2 (los, nts) Ps2 gl2 fs2)
    (Opsem.mkState
      ((Opsem.mkEC (fdef_intro fh2 bs2) B2
        (insn_call fake_id true attrs astk_typ None astk_fn
           [val32 (Z_of_nat (length lp + 1))]::
        cs1 ++ insn_call rid noret0 ca rt1 va1 (wrap_call fv) lp :: cs22 ++
        cs2' ++ cs23)
      tmn2 lc2 als2):: ECs2) M2)
    (Opsem.mkState
      ((Opsem.mkEC
        (fdef_intro (fheader_intro fa rt (wrapper_fid fid) la va)
                ((l1, stmts_intro ps1 (cs3 ++ cs4) tmn1) :: bs3))
        (l1, stmts_intro ps1 (cs3 ++ cs4) tmn1)
        cs4
      tmn1 lc2' nil)::
      (Opsem.mkEC (fdef_intro fh2 bs2) B2
        (insn_call rid noret0 ca rt1 va1 (wrap_call fv) lp :: cs22 ++ cs2' ++ cs23)
      tmn2 lc2 als2):: ECs2) M2') E0 /\
  wf_sb_mi mgb mi Mem0 M2' /\
  mem_simulation mi (los, nts) mgb MM Mem0 M2' /\
  reg_simulation mi (los, nts) gl2
    (fdef_intro (fheader_intro fa rt fid la va) lb) rm' rm3 lc' lc2'.

Axiom lookupExFdecViaPtr_isnt_callLib : forall Ps1 fs1 fv fa rt fid la va dck,
  OpsemAux.lookupExFdecViaPtr Ps1 fs1 fv =
    Some (fdec_intro (fheader_intro fa rt fid la va) dck) ->
  isCallLib fid = false.

Axiom shadow_stack_exfdec : forall la lc' mi lc2 lp cs1 nts los fptr
    Mem0 MM mgb fa rt fid va fs2 gl2 als2 tmn2 S2 Ps2 B2 cs2' dck
    fv rt1 va1 noret0 ca rid cs22 cs23 bs2 fh2 ECs2 M2 Mem' rm rm2
    bs1 fh1 lc oresult rm' gvs tr,
  wf_sb_mi mgb mi Mem0 M2 /\
  mem_simulation mi (los, nts) mgb MM Mem0 M2 /\
  reg_simulation mi (los, nts) gl2 (fdef_intro fh1 bs1) rm rm2 lc lc2 ->
  callExternalOrIntrinsics (los,nts) gl2 Mem0 fid rt (args2Typs la)
    dck gvs = ret (oresult, tr, Mem') ->
  SBspec.exCallUpdateLocals (los, nts) rt1 noret0 rid oresult lc rm =
    ret (lc', rm') ->
  ret cs1 = trans_params rm2 lp 1 ->
  Opsem.getOperandValue (los, nts) (wrap_call fv) lc2 gl2 = Some fptr ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs2 fptr =
          ret fdec_intro (fheader_intro fa rt (wrapper_fid fid) la va) dck ->
  exists M2', exists lc2',
  Opsem.sop_star (OpsemAux.mkCfg S2 (los, nts) Ps2 gl2 fs2)
    (Opsem.mkState
      ((Opsem.mkEC (fdef_intro fh2 bs2) B2
        (insn_call fake_id true attrs astk_typ None astk_fn
           [val32 (Z_of_nat (length lp + 1))]::
        cs1 ++ insn_call rid noret0 ca rt1 va1 (wrap_call fv) lp :: cs22 ++
        cs2' ++ cs23)
      tmn2 lc2 als2):: ECs2) M2)
    (Opsem.mkState
      ((Opsem.mkEC (fdef_intro fh2 bs2) B2
        (cs2' ++ cs23)
      tmn2 lc2' als2):: ECs2) M2') tr /\
  wf_sb_mi mgb mi Mem' M2' /\
  mem_simulation mi (los, nts) mgb MM Mem' M2' /\
  reg_simulation mi (los, nts) gl2 (fdef_intro fh1 bs1) rm' rm2 lc' lc2'.

Axiom free_allocas_preserves_gsb : forall M2 TD als2 M2' lp re gl,
  free_allocas TD M2 als2 = ret M2' ->
  callExternalOrIntrinsics TD gl M2 gsb_fid gsb_typ nil
    (deckind_external eid_other) lp = Some (re, events.E0, M2) ->
  callExternalOrIntrinsics TD gl M2' gsb_fid gsb_typ nil
    (deckind_external eid_other) lp = Some (re, events.E0, M2').

Axiom free_allocas_preserves_gse : forall M2 TD als2 M2' lp re gl,
  free_allocas TD M2 als2 = ret M2' ->
  callExternalOrIntrinsics TD gl M2 gse_fid gse_typ nil
    (deckind_external eid_other) lp = Some (re, events.E0, M2) ->
  callExternalOrIntrinsics TD gl M2' gse_fid gse_typ nil
    (deckind_external eid_other) lp = Some (re, events.E0, M2').

Axiom store_doesnt_change_gmmd : forall M2 b2 ofs v0 Mem2' lc2 gl als
   bid0 eid0 bgv' egv' fs F B cs tmn S Ps EC TD v ck,
  Mem.store ck M2 b2 ofs v0 = ret Mem2' ->
  @Opsem.sop_star DGVs (OpsemAux.mkCfg S TD Ps gl fs)
    (Opsem.mkState
      ((Opsem.mkEC F B
        (insn_call bid0 false attrs gmb_typ None gmb_fn (gmmd_args v) ::
         insn_call eid0 false attrs gme_typ None gme_fn (gmmd_args v) ::
         cs)
        tmn lc2 als)
        ::EC) M2)
    (Opsem.mkState
       ((Opsem.mkEC F B cs tmn
         (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als)::EC)
        M2)
    E0 ->
  Opsem.sop_star (OpsemAux.mkCfg S TD Ps gl fs)
    (Opsem.mkState
      ((Opsem.mkEC F B
        (insn_call bid0 false attrs gmb_typ None gmb_fn (gmmd_args v) ::
         insn_call eid0 false attrs gme_typ None gme_fn (gmmd_args v) ::
         cs)
        tmn lc2 als)
        ::EC) Mem2')
    (Opsem.mkState
       ((Opsem.mkEC F B cs tmn
         (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als)::EC)
        Mem2')
    E0.
