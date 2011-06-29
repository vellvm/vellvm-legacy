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
Require Import sb_ds_sim.
Require Import sb_ds_trans.

Import SB_ds_pass.

Axiom inject_incr__preserves__fable_simulation : forall mi fs1 fs2 mi',
  inject_incr mi mi' ->
  ftable_simulation mi fs1 fs2 ->
  ftable_simulation mi' fs1 fs2.

Axiom free_doesnt_change_gmmd : forall M2 b2 lo hi Mem2' lc2 gl als
   bid0 eid0 bgv' egv' fs F B cs tmn S Ps EC TD v,
  Mem.free M2 b2 lo hi = ret Mem2' ->
  LLVMopsem.dsop_star 
    (LLVMopsem.mkState S TD Ps 
      ((LLVMopsem.mkEC F B 
        (insn_call bid0 false attrs gmb_typ gmb_fn 
          ((p8,v)::(p8,vnullp8):: (i32,vint1)::(p32,vnullp32):: nil)::
         insn_call eid0 false attrs gme_typ gme_fn 
          ((p8,v)::(p8,vnullp8)::(i32,vint1)::(p32,vnullp32)::nil)::
         cs) 
        tmn lc2 als)
        ::EC) gl fs M2)
    (LLVMopsem.mkState S TD Ps 
       ((LLVMopsem.mkEC F B cs tmn 
         (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als)::EC) 
        gl fs M2)
    trace_nil ->
  LLVMopsem.dsop_star 
    (LLVMopsem.mkState S TD Ps 
      ((LLVMopsem.mkEC F B 
        (insn_call bid0 false attrs gmb_typ gmb_fn 
          ((p8,v)::(p8,vnullp8):: (i32,vint1)::(p32,vnullp32):: nil)::
         insn_call eid0 false attrs gme_typ gme_fn 
          ((p8,v)::(p8,vnullp8):: (i32,vint1)::(p32,vnullp32):: nil)::
         cs) 
        tmn lc2 als)
        ::EC) gl fs Mem2')
    (LLVMopsem.mkState S TD Ps 
       ((LLVMopsem.mkEC F B cs tmn 
         (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als)::EC) 
        gl fs Mem2')
    trace_nil.

Axiom get_mmetadata_fn__alloc__preserve : forall Mem2 lo hi Mem2' mb2
  (HeqR2 : (Mem2', mb2) = Mem.alloc Mem2 lo hi)
  (lc2 : GVMap) (gl : GVMap) (als : list mblock) (fs : GVMap) (F : fdef)
  (B : block) (cs : list cmd) (tmn : terminator) (S : system) (Ps : list product)
  (EC : list LLVMopsem.ExecutionContext) (bgv' : GenericValue) 
  (egv' : GenericValue) bid0 eid0 TD v als,
  LLVMopsem.dsop_star
     (LLVMopsem.mkState S TD Ps ((LLVMopsem.mkEC F B
        (insn_call bid0 false attrs gmb_typ gmb_fn 
           ((p8, v) :: (p8,vnullp8)::(i32,vint1):: (p32,vnullp32)::nil) :: 
         insn_call eid0 false attrs gme_typ gme_fn 
           ((p8, v) :: (p8,vnullp8)::(i32,vint1):: (p32,vnullp32)::nil) :: 
         cs) tmn lc2 als) :: EC) gl fs Mem2)
     (LLVMopsem.mkState S TD Ps ((LLVMopsem.mkEC F B cs tmn
        (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als) :: EC) 
        gl fs Mem2)
     trace_nil ->
  LLVMopsem.dsop_star
     (LLVMopsem.mkState S TD Ps ((LLVMopsem.mkEC F B
        (insn_call bid0 false attrs gmb_typ gmb_fn 
           ((p8, v) :: (p8,vnullp8)::(i32,vint1):: (p32,vnullp32)::nil) :: 
         insn_call eid0 false attrs gme_typ gme_fn 
           ((p8, v) :: (p8,vnullp8)::(i32,vint1):: (p32,vnullp32)::nil) :: 
         cs) tmn lc2 als) :: EC) gl fs Mem2')
     (LLVMopsem.mkState S TD Ps ((LLVMopsem.mkEC F B cs tmn 
        (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als) :: EC) 
        gl fs Mem2')
     trace_nil.

Axiom get_mmetadata_fn__alloc__zeroout : forall Mem2 lo hi Mem2' mb2 cm
  (HeqR2 : (Mem2', mb2) = Mem.alloc Mem2 lo hi)
  (lc2 : GVMap) (gl : GVMap) (als : list mblock) (fs : GVMap) (F : fdef)
  (B : block) (cs : list cmd) (tmn : terminator) (S : system) (Ps : list product)
  (EC : list LLVMopsem.ExecutionContext) bid0 eid0 TD v als ofs,
  getOperandValue TD v lc2 gl = 
    Some ((Vptr mb2 (Int.add 31 ofs (Int.repr 31 0)), cm)::nil) ->
  LLVMopsem.dsop_star
     (LLVMopsem.mkState S TD Ps ((LLVMopsem.mkEC F B
        (insn_call bid0 false attrs gmb_typ gmb_fn 
           ((p8, v) :: (p8,vnullp8)::(i32,vint1):: (p32,vnullp32)::nil) :: 
         insn_call eid0 false attrs gme_typ gme_fn 
           ((p8, v) :: (p8,vnullp8)::(i32,vint1):: (p32,vnullp32)::nil) :: 
         cs) tmn lc2 als) :: EC) gl fs Mem2')
     (LLVMopsem.mkState S TD Ps ((LLVMopsem.mkEC F B cs tmn 
        (updateAddAL _ (updateAddAL _ lc2 bid0 null) eid0 null) als) :: EC) 
        gl fs Mem2')
     trace_nil.

Axiom assert_mptr_fn__ok : forall 
  (lc2 : GVMap)
  (Mem2 : mem)
  (mi : meminj)
  (t : typ)
  (vp : value)
  (ptmp : id)
  (btmp : id)
  (etmp : id)
  (TD : TargetData)
  (gl : GVMap)
  (als : list mblock)
  (gvp : GenericValue)
  (md_base : GenericValue)
  (md_bound : GenericValue)
  (b : Values.block)
  (i0 : int32)
  (HeqR0 : ret Vptr b i0 = GV2ptr TD (getPointerSize TD) gvp)
  (b0 : Values.block)
  (i1 : int32)
  (HeqR5 : ret Vptr b0 i1 = GV2ptr TD (getPointerSize TD) md_base)
  (b1 : Values.block)
  (i2 : int32)
  (HeqR6 : ret Vptr b1 i2 = GV2ptr TD (getPointerSize TD) md_bound)
  (s : sz)
  (HeqR7 : ret s = getTypeAllocSize TD t)
  (J : zeq b b0 && zeq b0 b1 && zle (Int.signed 31 i1) (Int.signed 31 i0) &&
      zle (Int.signed 31 i0 + Size.to_Z s) (Int.signed 31 i2))
  (gvp2 : GenericValue)
  (H00 : getOperandValue TD vp lc2 gl = ret gvp2)
  (H01 : gv_inject mi gvp gvp2)
  (bv2 : value)
  (ev2 : value)
  (bgv2 : GenericValue)
  (egv2 : GenericValue)
  (J2 : getOperandValue TD bv2 lc2 gl = ret bgv2)
  (J3 : getOperandValue TD ev2 lc2 gl = ret egv2)
  (J4 : gv_inject mi md_base bgv2)
  (J5 : gv_inject mi md_bound egv2)
  S2 Ps2 F2 B2 cs2' als2 fs2 M2 tmn2 ECs2,
  LLVMopsem.dsInsn
       (LLVMopsem.mkState S2 TD Ps2
          ((LLVMopsem.mkEC F2 B2
            (insn_call fake_id true attrs assert_typ assert_fn
              ((p8, bv2)::(p8, ev2)::(p8, value_id ptmp)::(i32, type_size t):: 
                 (i32, vint1) :: nil):: 
             cs2') tmn2 
            (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl fs2 M2)
       (LLVMopsem.mkState S2 TD Ps2
          ((LLVMopsem.mkEC F2 B2
            cs2' tmn2 
            (updateAddAL GenericValue lc2 ptmp gvp2)
             als2):: 
            ECs2) gl fs2 M2) trace_nil.

Axiom simulation__set_mmetadata_fn : forall lc2 gl b ofs bgv egv als2 tmn2 ECs2 
  pgv' bgv' egv' mi ptmp bv0 ev0 MM1 Mem1 Mem2 rm v gmb fs2 gl2 cs F2 B2 TD
  Ps2 S2 cm,
  mem_simulation mi TD gmb MM1 Mem1 Mem2 ->
  SBopsem.get_reg_metadata TD gl rm v = Some (SBopsem.mkMD bgv egv) -> 
  lookupAL _ lc2 ptmp = Some pgv' ->
  getOperandValue TD bv0 lc2 gl = Some bgv' ->
  getOperandValue TD ev0 lc2 gl = Some egv' ->
  gv_inject mi ((Vptr b ofs,cm)::nil) pgv' ->
  gv_inject mi bgv bgv' ->
  gv_inject mi egv egv' ->
  exists Mem2',
    LLVMopsem.dsInsn
      (LLVMopsem.mkState S2 TD Ps2
          ((LLVMopsem.mkEC F2 B2
              (insn_call fake_id true attrs smmd_typ smmd_fn
                ((p8, value_id ptmp) :: (p8, bv0) :: (p8, ev0) :: (p8, vnullp8)
                    :: (i32, vint1) :: (i32, vint1) :: nil):: 
               cs) tmn2 lc2
             als2):: 
            ECs2) gl2 fs2 Mem2)
      (LLVMopsem.mkState S2 TD Ps2
          ((LLVMopsem.mkEC F2 B2
              cs tmn2 lc2 als2):: 
            ECs2) gl2 fs2 Mem2') trace_nil /\
      mem_simulation mi TD gmb
        (SBopsem.set_mem_metadata TD MM1 ((Vptr b ofs,cm)::nil) 
        (SBopsem.mkMD bgv egv)) Mem1 Mem2'.

Axiom set_mmetadata_fn__prop : forall TD Mem1 lc2 als2 Mem2 S2 Ps2 F2
   B2 tmn2 cs fs2 gl2 ECs2 lp,
  LLVMopsem.dsInsn
      (LLVMopsem.mkState S2 TD Ps2
          ((LLVMopsem.mkEC F2 B2
              (insn_call fake_id true attrs smmd_typ smmd_fn lp ::
               cs) tmn2 lc2
             als2):: 
            ECs2) gl2 fs2 Mem1)
      (LLVMopsem.mkState S2 TD Ps2
          ((LLVMopsem.mkEC F2 B2 cs tmn2 lc2 als2):: 
            ECs2) gl2 fs2 Mem2) trace_nil ->
  Mem.nextblock Mem1 <= Mem.nextblock Mem2 /\
  (forall b2, Mem.valid_block Mem1 b2 -> Mem.valid_block Mem2 b2) /\
  (forall b0, Mem.bounds Mem1 b0 = Mem.bounds Mem2 b0).

Axiom dstk_spec : forall M, 
  LLVMopsem.callExternalFunction M dstk_fid nil = Some (None, M).

Axiom dstk_is_found : forall TD Ps gl lc fs, 
  LLVMopsem.lookupExFdecViaGV TD Ps gl lc fs dstk_fn = Some
    (fdec_intro (fheader_intro sb_fnattrs dstk_typ dstk_fid nil false)).

Definition int2GV n :=
  (Vint 31 (Int.repr 31 (INTEGER.to_Z n)), AST.Mint 31)::nil.

Axiom stk_ret_sim : forall TD M1 M2 mi mgb MM bgv egv,
  mem_simulation mi TD mgb MM M1 M2 ->
  wf_sb_mi mgb mi M1 M2 ->
  exists M2',  exists M2'',
    LLVMopsem.callExternalFunction M2 ssb_fid (bgv::int2GV 0%Z::nil) = 
      Some (None, M2') /\
    LLVMopsem.callExternalFunction M2' sse_fid (egv::int2GV 0%Z::nil) = 
      Some (None, M2'') /\
    mem_simulation mi TD mgb MM M1 M2'' /\
    wf_sb_mi mgb mi M1 M2'' /\
    LLVMopsem.callExternalFunction M2'' gsb_fid [int2GV 0%Z] = 
      Some (Some bgv, M2'') /\
    LLVMopsem.callExternalFunction M2'' gse_fid [int2GV 0%Z] = 
      Some (Some egv, M2'').

Axiom ssb_is_found : forall TD Ps gl lc fs, 
  LLVMopsem.lookupExFdecViaGV TD Ps gl lc fs ssb_fn = Some
    (fdec_intro (fheader_intro sb_fnattrs ssb_typ ssb_fid nil false)).

Axiom sse_is_found : forall TD Ps gl lc fs, 
  LLVMopsem.lookupExFdecViaGV TD Ps gl lc fs sse_fn = Some
    (fdec_intro (fheader_intro sb_fnattrs sse_typ sse_fid nil false)).

Axiom gsb_is_found : forall TD Ps gl lc fs, 
  LLVMopsem.lookupExFdecViaGV TD Ps gl lc fs gsb_fn = Some
    (fdec_intro (fheader_intro sb_fnattrs gsb_typ gsb_fid nil false)).

Axiom gse_is_found : forall TD Ps gl lc fs, 
  LLVMopsem.lookupExFdecViaGV TD Ps gl lc fs gse_fn = Some
    (fdec_intro (fheader_intro sb_fnattrs gse_typ gse_fid nil false)).

Axiom free_doesnt_change_gsb : forall TD M1 z gv M2 als,
  LLVMopsem.callExternalFunction M1 gsb_fid [int2GV z] = ret (ret gv, M1) ->
  free_allocas TD M1 als = ret M2 ->
  LLVMopsem.callExternalFunction M2 gsb_fid [int2GV z] = ret (ret gv, M2).

Axiom free_doesnt_change_gse : forall TD M1 z gv M2 als,
  LLVMopsem.callExternalFunction M1 gse_fid [int2GV z] = ret (ret gv, M1) ->
  free_allocas TD M1 als = ret M2 ->
  LLVMopsem.callExternalFunction M2 gse_fid [int2GV z] = ret (ret gv, M2).

Axiom wrapper_fid_is_identical : forall fid, wrapper_fid fid = fid.

Axiom lookupFdefViaGV_isnt_callLib : forall TD Ps1 gl2 lc fs1 fv fa rt fid la va 
    lb,
  LLVMopsem.lookupFdefViaGV TD Ps1 gl2 lc fs1 fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  isCallLib fid = false.

Axiom shadow_stack_init : forall la ogvs lc' rm' gl mi lc2 lp cs1 rm2 nts los 
    Mem0 MM mgb fa rt fid va lb fs2 gl2 als2 tmn2 cs3 cs4 bs3 S2 Ps2 B2 cs2' tmn1
    ps1 l1 fv ft noret0 ca rid cs22 cs23 bs2 fh2 ECs2 M2 rm3 ex_ids3,
  wf_sb_mi mgb mi Mem0 M2 ->
  mem_simulation mi (los, nts) mgb MM Mem0 M2 -> 
  initLocals la ogvs = (lc', rm') ->
  params_simulation (los,nts) gl mi lc2 ogvs 1 cs1 -> 
  ret cs1 = trans_params rm2 lp 1 ->
  gen_metadata_fdef nts
         (getFdefLocs (fdef_intro (fheader_intro fa rt fid la va) lb)) nil
         (fdef_intro (fheader_intro fa rt fid la va) lb) = 
       ret (ex_ids3, rm3) ->
  trans_args rm3 la 1 = ret cs3 -> 
  LLVMopsem.lookupFdefViaGV (los, nts) Ps2 gl2 lc2 fs2 (wrap_call fv) =
          ret fdef_intro (fheader_intro fa rt (wrapper_fid fid) la va)
                (block_intro l1 ps1 (cs3 ++ cs4) tmn1 :: bs3) ->
  exists M2', exists lc2',
  LLVMopsem.dsop_star
    (LLVMopsem.mkState S2 (los, nts) Ps2
      ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
        (insn_call fake_id true attrs astk_typ astk_fn 
           [val32 (Z_of_nat (length lp + 1))]:: 
        cs1 ++ insn_call rid noret0 ca ft (wrap_call fv) lp :: cs22 ++
        cs2' ++ cs23)
      tmn2 lc2 als2):: ECs2) gl2 fs2 M2)
    (LLVMopsem.mkState S2 (los, nts) Ps2
      ((LLVMopsem.mkEC 
        (fdef_intro (fheader_intro fa rt (wrapper_fid fid) la va)
                (block_intro l1 ps1 (cs3 ++ cs4) tmn1 :: bs3))
        (block_intro l1 ps1 (cs3 ++ cs4) tmn1)
        cs4
      tmn1 lc2' nil):: 
      (LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
        (insn_call rid noret0 ca ft (wrap_call fv) lp :: cs22 ++ cs2' ++ cs23)
      tmn2 lc2 als2):: ECs2) gl2 fs2 M2') trace_nil /\
  wf_sb_mi mgb mi Mem0 M2' /\
  mem_simulation mi (los, nts) mgb MM Mem0 M2' /\
  reg_simulation mi (los, nts) gl2 
    (fdef_intro (fheader_intro fa rt fid la va) lb) rm' rm3 lc' lc2'.

Axiom lookupExFdecViaGV_isnt_callLib : forall TD Ps1 gl2 lc fs1 fv fa rt fid la 
    va,
  LLVMopsem.lookupExFdecViaGV TD Ps1 gl2 lc fs1 fv = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  isCallLib fid = false.

Axiom shadow_stack_exfdec : forall la lc' mi lc2 lp cs1 nts los 
    Mem0 MM mgb fa rt fid va fs2 gl2 als2 tmn2 S2 Ps2 B2 cs2' 
    fv ft noret0 ca rid cs22 cs23 bs2 fh2 ECs2 M2 Mem' rm rm2
    bs1 fh1 lc oresult rm' gvs,
  wf_sb_mi mgb mi Mem0 M2 /\
  mem_simulation mi (los, nts) mgb MM Mem0 M2 /\
  reg_simulation mi (los, nts) gl2 (fdef_intro fh1 bs1) rm rm2 lc lc2 ->
  LLVMopsem.callExternalFunction Mem0 fid gvs = ret (oresult, Mem') ->
  exCallUpdateLocals ft noret0 rid oresult lc rm = ret (lc', rm') ->
  ret cs1 = trans_params rm2 lp 1 ->
  LLVMopsem.lookupExFdecViaGV (los, nts) Ps2 gl2 lc2 fs2 (wrap_call fv) =
          ret fdec_intro (fheader_intro fa rt (wrapper_fid fid) la va) ->
  exists M2', exists lc2',
  LLVMopsem.dsop_star
    (LLVMopsem.mkState S2 (los, nts) Ps2
      ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
        (insn_call fake_id true attrs astk_typ astk_fn 
           [val32 (Z_of_nat (length lp + 1))]:: 
        cs1 ++ insn_call rid noret0 ca ft (wrap_call fv) lp :: cs22 ++
        cs2' ++ cs23)
      tmn2 lc2 als2):: ECs2) gl2 fs2 M2)
    (LLVMopsem.mkState S2 (los, nts) Ps2
      ((LLVMopsem.mkEC (fdef_intro fh2 bs2) B2
        (cs2' ++ cs23)
      tmn2 lc2' als2):: ECs2) gl2 fs2 M2') trace_nil /\
  wf_sb_mi mgb mi Mem' M2' /\
  mem_simulation mi (los, nts) mgb MM Mem' M2' /\
  reg_simulation mi (los, nts) gl2 (fdef_intro fh1 bs1) rm' rm2 lc' lc2'.

Axiom free_allocas_preserves_gsb : forall M2 TD als2 M2' lp re,
  free_allocas TD M2 als2 = ret M2' ->
  LLVMopsem.callExternalFunction M2 gsb_fid lp = Some (re, M2) ->
  LLVMopsem.callExternalFunction M2' gsb_fid lp = Some (re, M2').

Axiom free_allocas_preserves_gse : forall M2 TD als2 M2' lp re,
  free_allocas TD M2 als2 = ret M2' ->
  LLVMopsem.callExternalFunction M2 gse_fid lp = Some (re, M2) ->
  LLVMopsem.callExternalFunction M2' gse_fid lp = Some (re, M2').

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)





