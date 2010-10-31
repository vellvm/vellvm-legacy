Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa/compcert".
Add LoadPath "../ssa".
(*Add LoadPath "../../../theory/metatheory".*)
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import trace.
Require Import assoclist.
Require Import ssa_props.
Require Import CoqListFacts.
Require Import Coqlib.

Export LLVMsyntax.
Export LLVMlib.
Export LLVMgv.
Export LLVMmem.

(***************************************************************)
(* Syntax easy to be proved with symbolic execution. *)

Module SimpleSE.

(***************************************************************)
(* deterministic big-step for this new syntax with subblocks. *)

Record ExecutionContext : Type := mkEC {
CurBB       : block;
Locals      : GVMap;                 (* LLVM values used in this invocation *)
Allocas     : list mblock            (* Track memory allocated by alloca *)
}.

Record State : Type := mkState {
Frame          : ExecutionContext;
Mem            : mem
}.

Inductive dbCmd : layouts ->  GVMap ->
                  GVMap -> list mblock -> mem -> 
                  cmd -> 
                  GVMap -> list mblock -> mem -> 
                  trace -> Prop :=
| dbBop: forall TD lc gl id bop sz v1 v2 gv3 Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gv3 ->
  dbCmd TD gl
    lc als Mem
    (insn_bop id bop sz v1 v2)
    (updateAddAL _ lc id gv3) als Mem
    trace_nil 
| dbFBop: forall TD lc gl id fbop fp v1 v2 gv3 Mem als,
  FBOP TD lc gl fbop fp v1 v2 = Some gv3 ->
  dbCmd TD gl
    lc als Mem
    (insn_fbop id fbop fp v1 v2)
    (updateAddAL _ lc id gv3) als Mem
    trace_nil 
| dbExtractValue : forall TD lc gl id t v gv gv' Mem als idxs,
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  dbCmd TD gl
    lc als Mem
    (insn_extractvalue id t v idxs)
    (updateAddAL _ lc id gv') als Mem
    trace_nil 
| dbInsertValue : forall TD lc gl id t v t' v' gv gv' gv'' idxs Mem als,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  dbCmd TD gl
    lc als Mem
    (insn_insertvalue id t v t' v' idxs)
    (updateAddAL _ lc id gv'') als Mem
    trace_nil 
| dbMalloc : forall TD lc gl id t sz align Mem als Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  malloc TD Mem (tsz * sz)%nat align = Some (Mem', mb) ->
  dbCmd TD gl
    lc als Mem
    (insn_malloc id t sz align)
    (updateAddAL _ lc id (blk2GV TD mb)) als Mem'
    trace_nil
| dbFree : forall TD lc gl fid t v Mem als Mem' mptr,
  getOperandValue TD v lc gl = Some mptr ->
  free TD Mem mptr = Some Mem'->
  dbCmd TD gl
    lc als Mem
    (insn_free fid t v)
    lc als Mem'
    trace_nil
| dbAlloca : forall TD lc gl id t sz align Mem als Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  malloc TD Mem (tsz * sz)%nat align = Some (Mem', mb) ->
  dbCmd TD gl
    lc als Mem
    (insn_alloca id t sz align)
    (updateAddAL _ lc id (blk2GV TD mb)) (mb::als) Mem'
    trace_nil
| dbLoad : forall TD lc gl id t v align Mem als mp gv,
  getOperandValue TD v lc gl = Some mp ->
  mload TD Mem mp t align = Some gv ->
  dbCmd TD gl
    lc als Mem
    (insn_load id t v align)
    (updateAddAL _ lc id gv) als Mem
    trace_nil
| dbStore : forall TD lc gl sid t v1 v2 align Mem als mp2 gv1 Mem',
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some mp2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  dbCmd TD gl 
    lc als Mem
    (insn_store sid t v1 v2 align)
    lc als Mem'
    trace_nil
| dbGEP : forall TD lc gl id inbounds t v idxs vidxs mp mp' Mem als,
  getOperandValue TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxs ->
  GEP TD t mp vidxs inbounds = Some mp' ->
  dbCmd TD gl
    lc als Mem
    (insn_gep id inbounds t v idxs)
    (updateAddAL _ lc id mp') als Mem
    trace_nil 
| dbTrunc : forall TD lc gl id truncop t1 v1 t2 gv2 Mem als,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gv2 ->
  dbCmd TD gl
    lc als Mem
    (insn_trunc id truncop t1 v1 t2)
    (updateAddAL _ lc id gv2) als Mem
    trace_nil
| dbExt : forall TD lc gl id extop t1 v1 t2 gv2 Mem als,
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  dbCmd TD gl
    lc als Mem
    (insn_ext id extop t1 v1 t2)
    (updateAddAL _ lc id gv2) als Mem
    trace_nil
| dbCast : forall TD lc gl id castop t1 v1 t2 gv2 Mem als,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  dbCmd TD gl
    lc als Mem
    (insn_cast id castop t1 v1 t2)
    (updateAddAL _ lc id gv2) als Mem
    trace_nil
| dbIcmp : forall TD lc gl id cond t v1 v2 gv3 Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  dbCmd TD gl
    lc als Mem
    (insn_icmp id cond t v1 v2)
    (updateAddAL _ lc id gv3) als Mem
    trace_nil
| dbFcmp : forall TD lc gl id fcond fp v1 v2 gv3 Mem als,
  FCMP TD lc gl fcond fp v1 v2 = Some gv3 ->
  dbCmd TD gl
    lc als Mem
    (insn_fcmp id fcond fp v1 v2)
    (updateAddAL _ lc id gv3) als Mem
    trace_nil
| dbSelect : forall TD lc gl id v0 t v1 v2 cond Mem als gv1 gv2,
  getOperandValue TD v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  dbCmd TD gl
    lc als Mem
    (insn_select id v0 t v1 v2)
    (if isGVZero TD cond then updateAddAL _ lc id gv2 else updateAddAL _ lc id gv1) als Mem
    trace_nil
.

Inductive dbTerminator : 
  layouts -> fdef -> GVMap -> 
  block -> GVMap -> 
  terminator -> 
  block -> GVMap -> 
  trace -> Prop :=
| dbBranch : forall TD F B lc gl bid Cond l1 l2 c
                              l' ps' sbs' tmn' lc',   
  getOperandValue TD Cond lc gl = Some c ->
  Some (block_intro l' ps' sbs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  lc' = LLVMopsem.switchToNewBasicBlock TD (block_intro l' ps' sbs' tmn') B gl lc ->
  dbTerminator TD F gl
    B lc
    (insn_br bid Cond l1 l2)
    (block_intro l' ps' sbs' tmn') lc' 
    trace_nil 
| dbBranch_uncond : forall TD F B lc gl l bid
                              l' ps' sbs' tmn' lc',   
  Some (block_intro l' ps' sbs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  lc' = LLVMopsem.switchToNewBasicBlock TD (block_intro l' ps' sbs' tmn') B gl lc ->
  dbTerminator TD F gl
    B lc
    (insn_br_uncond bid l) 
    (block_intro l' ps' sbs' tmn') lc'
    trace_nil 
.

Inductive dbCmds : layouts -> GVMap -> 
                   GVMap -> list mblock -> mem -> 
                   cmds -> 
                   GVMap -> list mblock -> mem -> 
                   trace -> Prop :=
| dbCmds_nil : forall TD lc als gl Mem, dbCmds TD gl lc als Mem nil lc als Mem trace_nil
| dbCmds_cons : forall TD c cs gl lc1 als1 Mem1 t1 t2 lc2 als2 Mem2
                       lc3 als3 Mem3,
    dbCmd TD gl lc1 als1 Mem1 c lc2 als2 Mem2 t1 ->
    dbCmds TD gl lc2 als2 Mem2 cs lc3 als3 Mem3 t2 ->
    dbCmds TD gl lc1 als1 Mem1 (c::cs) lc3 als3 Mem3 (trace_app t1 t2).

Inductive dbCall : system -> layouts -> list product -> GVMap -> 
                   GVMap -> mem -> 
                   cmd -> 
                   GVMap -> mem -> 
                   trace -> Prop :=
| dbCall_internal : forall S TD Ps lc gl rid noret tailc rt fid lp
                       Rid oResult tr lc' Mem Mem' als' Mem'' B',
  dbFdef fid rt lp S TD Ps lc gl Mem lc' als' Mem' B' Rid oResult tr ->
  free_allocas TD Mem' als' = Some Mem'' ->
  dbCall S TD Ps gl
    lc Mem
    (insn_call rid noret tailc rt fid lp)
    (LLVMopsem.callUpdateLocals TD noret rid rt oResult lc lc' gl) 
    Mem'' tr
| dbCall_external : forall S TD Ps lc gl rid noret tailc fid 
                          lp rt la Mem oresult Mem',
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  LLVMopsem.lookupExFdefViaIDFromProducts Ps fid = Some (fdec_intro (fheader_intro rt fid la)) ->
  LLVMopsem.callExternalFunction Mem fid (params2GVs TD lp lc gl) = (oresult, Mem') ->
  dbCall S TD Ps gl
    lc Mem
    (insn_call rid noret tailc rt fid lp)
    (LLVMopsem.exCallUpdateLocals noret rid rt oresult lc) 
    Mem' trace_nil
with dbSubblock : system -> layouts -> list product -> GVMap -> 
                  GVMap -> list mblock -> mem -> 
                  cmds -> 
                  GVMap -> list mblock -> mem -> 
                  trace -> Prop :=
| dbSubblock_intro : forall S TD Ps lc1 als1 gl Mem1 cs call0 lc2 als2 Mem2 tr1 
                     lc3 Mem3 tr2,
  dbCmds TD gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr1 ->
  dbCall S TD Ps gl lc2 Mem2 call0 lc3 Mem3 tr2 ->
  dbSubblock S TD Ps gl
             lc1 als1 Mem1
             (cs++call0::nil) 
             lc3 als2 Mem3
             (trace_app tr1 tr2)
with dbSubblocks : system -> layouts -> list product -> GVMap -> 
                   GVMap -> list mblock -> mem -> 
                   cmds -> 
                   GVMap -> list mblock -> mem -> 
                   trace -> Prop :=
| dbSubblocks_nil : forall S TD Ps lc als gl Mem, 
    dbSubblocks S TD Ps gl lc als Mem nil lc als Mem trace_nil
| dbSubblocks_cons : forall S TD Ps lc1 als1 gl Mem1 lc2 als2 Mem2 lc3 als3 Mem3 cs cs' t1 t2,
    dbSubblock S TD Ps gl lc1 als1 Mem1 cs lc2 als2 Mem2 t1 ->
    dbSubblocks S TD Ps gl lc2 als2 Mem2 cs' lc3 als3 Mem3 t2 ->
    dbSubblocks S TD Ps gl lc1 als1 Mem1 (cs++cs') lc3 als3 Mem3 (trace_app t1 t2)
with dbBlock : system -> layouts -> list product -> GVMap -> fdef -> list GenericValue -> State -> State -> trace -> Prop :=
| dbBlock_intro : forall S TD Ps F tr1 tr2 l ps cs cs' tmn gl lc1 als1 Mem1
                         lc2 als2 Mem2 lc3 als3 Mem3 lc4 B' arg tr3,
  dbSubblocks S TD Ps gl
    lc1 als1 Mem1
    cs
    lc2 als2 Mem2
    tr1 ->
  dbCmds TD gl lc2 als2 Mem2 cs' lc3 als3 Mem3 tr2 ->
  dbTerminator TD F gl
    (block_intro l ps (cs++cs') tmn) lc3
    tmn
    B' lc4
    tr3 ->
  dbBlock S TD Ps gl F arg
    (mkState (mkEC (block_intro l ps (cs++cs') tmn) lc1 als1) Mem1)
    (mkState (mkEC B' lc4 als3) Mem3)
    (trace_app (trace_app tr1 tr2) tr3)
with dbBlocks : system -> layouts -> list product -> GVMap -> fdef -> list GenericValue -> State -> State -> trace -> Prop :=
| dbBlocks_nil : forall S TD Ps gl F arg state, dbBlocks S TD Ps gl F arg state state trace_nil
| dbBlocks_cons : forall S TD Ps gl F arg S1 S2 S3 t1 t2,
    dbBlock S TD Ps gl F arg S1 S2 t1 ->
    dbBlocks S TD Ps gl F arg S2 S3 t2 ->
    dbBlocks S TD Ps gl F arg S1 S3 (trace_app t1 t2)
with dbFdef : id -> typ -> params -> system -> layouts -> list product -> GVMap -> GVMap -> mem -> GVMap -> list mblock -> mem -> block -> id -> option value -> trace -> Prop :=
| dbFdef_func : forall S TD Ps gl fid lp lc rid
                       l1 ps1 cs1 tmn1 rt la lb Result lc1 tr1 Mem Mem1 als1
                       l2 ps2 cs21 cs22 lc2 als2 Mem2 tr2 lc3 als3 Mem3 tr3,
  lookupFdefViaIDFromProducts Ps fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some (block_intro l1 ps1 cs1 tmn1) ->
  dbBlocks S TD Ps gl (fdef_intro (fheader_intro rt fid la) lb) (params2GVs TD lp lc gl)
    (mkState (mkEC (block_intro l1 ps1 cs1 tmn1) (initLocals la (params2GVs TD lp lc gl)) nil) Mem)
    (mkState (mkEC (block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result)) lc1 als1) Mem1)
    tr1 ->
  dbSubblocks S TD Ps gl
    lc1 als1 Mem1
    cs21
    lc2 als2 Mem2
    tr2 ->
  dbCmds TD gl
    lc2 als2 Mem2
    cs22
    lc3 als3 Mem3
    tr3 ->
  dbFdef fid rt lp S TD Ps lc gl Mem lc3 als3 Mem3 (block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result)) rid (Some Result) (trace_app (trace_app tr1 tr2) tr3)
| dbFdef_proc : forall S TD Ps gl fid lp lc rid
                       l1 ps1 cs1 tmn1 rt la lb lc1 tr1 Mem Mem1 als1
                       l2 ps2 cs21 cs22 lc2 als2 Mem2 tr2 lc3 als3 Mem3 tr3,
  lookupFdefViaIDFromProducts Ps fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some (block_intro l1 ps1 cs1 tmn1) ->
  dbBlocks S TD Ps gl (fdef_intro (fheader_intro rt fid la) lb) (params2GVs TD lp lc gl) 
    (mkState (mkEC (block_intro l1 ps1 cs1 tmn1) (initLocals la (params2GVs TD lp lc gl)) nil) Mem)
    (mkState (mkEC (block_intro l2 ps2 (cs21++cs22) (insn_return_void rid)) lc1 als1) Mem1)
    tr1 ->
  dbSubblocks S TD Ps gl
    lc1 als1 Mem1
    cs21
    lc2 als2 Mem2
    tr2 ->
  dbCmds TD gl
    lc2 als2 Mem2
    cs22
    lc3 als3 Mem3
    tr3 ->
  dbFdef fid rt lp S TD Ps lc gl Mem lc3 als3 Mem3 (block_intro l2 ps2 (cs21++cs22) (insn_return_void rid)) rid None (trace_app (trace_app tr1 tr2) tr3)
.

Scheme dbCall_ind2 := Induction for dbCall Sort Prop
  with dbSubblock_ind2 := Induction for dbSubblock Sort Prop
  with dbSubblocks_ind2 := Induction for dbSubblocks Sort Prop
  with dbBlock_ind2 := Induction for dbBlock Sort Prop
  with dbBlocks_ind2 := Induction for dbBlocks Sort Prop
  with dbFdef_ind2 := Induction for dbFdef Sort Prop.

Combined Scheme db_mutind from dbCall_ind2, dbSubblock_ind2, dbSubblocks_ind2,
                               dbBlock_ind2, dbBlocks_ind2, dbFdef_ind2.

Tactic Notation "db_mutind_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCall_internal" | c "dbCall_external" | 
    c "dbSubblock_intro" | c "dbSubblocks_nil" | c "dbSubblocks_cons" | 
    c "dbBlock_intro" | c "dbBlocks_nil" | c "dbBlocks_cons" | 
    c "dbFdef_func" | c "dbFdef_proc" ].

Tactic Notation "dbCmd_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBop" | c "dbFBop" | c "dbExtractValue" | c "dbInsertValue" |
    c "dbMalloc" | c "dbFree" |
    c "dbAlloca" | c "dbLoad" | c "dbStore" | c "dbGEP" |
    c "dbTrunc" | c "dbExt" | c "dbCast" | 
    c "dbIcmp" | c "dbFcmp" | c "dbSelect" ].

Tactic Notation "dbTerminator_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBranch" | c "dbBranch_uncond" ].

Tactic Notation "dbCmds_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCmds_nil" | c "dbCmds_cons" ].

Hint Constructors dbCmd dbCmds dbTerminator dbCall 
                  dbSubblock dbSubblocks dbBlock dbBlocks dbFdef.

(* eqEnv *)
Lemma dbCmd_eqEnv : forall TD c lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1',
  dbCmd TD gl lc1 als1 Mem1 c lc2 als2 Mem2 tr ->
  eqAL _ lc1 lc1' ->
  exists lc2', 
    dbCmd TD gl lc1' als1 Mem1 c lc2' als2 Mem2 tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros TD c lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1' HdbCmd HeqEnv.
  (dbCmd_cases (inversion HdbCmd) Case); subst.
Case "dbBop".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  rewrite BOP_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbFBop".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  rewrite FBOP_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbExtractValue".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv').
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  split; eauto using eqAL_updateAddAL.
  
Case "dbInsertValue".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv'').
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H0; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbMalloc".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 (blk2GV TD mb)).
  split; eauto using eqAL_updateAddAL.

Case "dbFree".
  exists lc1'.
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  split; eauto.

Case "dbAlloca".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 (blk2GV TD mb)).
  split; eauto using eqAL_updateAddAL.

Case "dbLoad".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv).
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbStore".
  exists lc1'.
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H0; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbGEP".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 mp').
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  rewrite values2GVs_eqAL with (lc2:=lc1') in H0; auto. 
(* rewrite GEP_eqAL with (lc2:=lc1') in H0; auto. *)
  split; eauto using eqAL_updateAddAL.

Case "dbTrunc".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  rewrite TRUNC_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbExt".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  rewrite EXT_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbCast".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  rewrite CAST_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbIcmp".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  rewrite ICMP_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbFcmp".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  rewrite FCMP_eqAL with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbSelect".
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H; auto. 
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H0; auto. 
  rewrite getOperandValue_eqAL with (lc2:=lc1') in H1; auto. 
  assert (HupdateEnv:=HeqEnv).
  exists (if isGVZero TD cond0 then updateAddAL _ lc1' id0 gv2 else updateAddAL _ lc1' id0 gv1).
  split; auto.
    destruct (isGVZero TD cond0); auto using eqAL_updateAddAL.
Qed.

Lemma dbCmds_eqEnv : forall TD cs lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1',
  dbCmds TD gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr ->
  eqAL _ lc1 lc1' ->
  exists lc2', 
    dbCmds TD gl lc1' als1 Mem1 cs lc2' als2 Mem2 tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros TD cs lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1' HdbCmds HeqEnv.
  generalize dependent lc1'.
  induction HdbCmds; intros.
    exists lc1'. split; auto.

    apply dbCmd_eqEnv with (lc1':=lc1') in H; auto.
    destruct H as [lc2' [HdbCmd HeqEnv']].
    apply IHHdbCmds in HeqEnv'; auto.
    destruct HeqEnv' as [lc3' [HdbCmds' HeqEnv'']].
    exists lc3'.
    split; eauto.
Qed.

(* nonbranching cmd *)
Record nbranch := mkNB
{ nbranching_cmd:cmd;
  notcall:Instruction.isCallInst nbranching_cmd = false
}.

Lemma isCallInst_dec : forall c, 
  {Instruction.isCallInst c = false} + {Instruction.isCallInst c = true}.
Proof.
  destruct c; simpl; auto.
Qed.

Definition cmd2nbranch (c:cmd) : option nbranch :=
match (isCallInst_dec c) with 
| left H => Some (mkNB c H)
| right _ => None
end.

Lemma dbCmd_isNotCallInst : forall TD lc als gl Mem1 c lc' als' Mem2 tr,
  dbCmd TD gl lc als Mem1 c lc' als' Mem2 tr ->
  Instruction.isCallInst c = false.
Proof.
  intros TD lc als gl Mem1 c lc' als' Mem2 tr HdbCmd.
  induction HdbCmd; auto.
Qed.

Definition dbCmd2nbranch : forall TD lc als gl Mem1 c lc' als' Mem2 tr, 
  dbCmd TD gl lc als Mem1 c lc' als' Mem2 tr ->
  exists nb, cmd2nbranch c = Some nb.
Proof.
  intros.
  apply dbCmd_isNotCallInst in H.
  unfold cmd2nbranch.
  destruct (isCallInst_dec).
    exists (mkNB c e). auto.
    rewrite H in e. inversion e.
Qed.

(* This may not work sometimes. This function creates a proof
   that a cmd is not a call, which can only be proved to eual to
   the same proof in the context by proof-irrevelance axiom. *)
Fixpoint cmds2nbranchs (cs:list cmd) : option (list nbranch) :=
match cs with
| nil => Some nil
| c::cs' =>
  match (cmd2nbranch c, cmds2nbranchs cs') with
  | (Some nb, Some nbs') => Some (nb::nbs')
  | _ => None
  end
end.

Fixpoint nbranchs2cmds (nbs:list nbranch) : list cmd :=
match nbs with
| nil => nil
| (mkNB c nc)::nbs' =>c::nbranchs2cmds nbs'
end.

Lemma nbranchs2cmds_app : forall nbs1 nbs2,
  nbranchs2cmds (nbs1++nbs2) = nbranchs2cmds nbs1 ++ nbranchs2cmds nbs2.
Proof.
  induction nbs1; intros; auto.
    simpl. destruct a. rewrite IHnbs1. auto.
Qed.

Definition dbCmds2nbranchs : forall cs TD lc als gl Mem1 lc' als' Mem2 tr, 
  dbCmds TD gl lc als Mem1 cs lc' als' Mem2 tr ->
  exists nbs, cmds2nbranchs cs = Some nbs.
Proof.
  induction cs; intros.
    exists nil. simpl. auto.

    inversion H; subst.
    apply dbCmd2nbranch in H7.
    apply IHcs in H12.
    destruct H7 as [nb J1].
    destruct H12 as [nbs J2].
    exists (nb::nbs).
    simpl. 
    rewrite J1.
    rewrite J2.
    auto.
Qed.

Lemma cmds_cons2nbranchs_inv : forall c cs' nbs,
  cmds2nbranchs (c::cs') = Some nbs ->
  exists nb, exists nbs',
    cmd2nbranch c = Some nb /\
    cmds2nbranchs cs' = Some nbs' /\
    nbs = nb::nbs'.
Proof.
  intros.
  simpl in H.
  destruct (cmd2nbranch c); try solve [inversion H].
  destruct (cmds2nbranchs cs'); inversion H; subst.
  exists n. exists l0. auto.
Qed.

Lemma cmd2nbranch_Some_isCallInst : forall c nb,
  cmd2nbranch c = Some nb ->
  exists H, nb = mkNB c H.
Proof.
  intros.
  unfold cmd2nbranch in H.
  destruct nb.
  destruct (isCallInst_dec c); inversion H; subst.
    exists notcall0. auto. 
Qed.

(* cmd2sbs *)

Record subblock := mkSB
{
  NBs : list nbranch;
  call_cmd : cmd;
  call_cmd_isCall : Instruction.isCallInst call_cmd = true
}.


Fixpoint cmds2sbs (cs:cmds) : (list subblock*list nbranch) :=
match cs with
| nil => (nil,nil)
| c::cs' =>
  match (isCallInst_dec c) with
  | left isnotcall => 
    match (cmds2sbs cs') with
    | (nil, nbs0) => (nil, mkNB c isnotcall::nbs0) 
    | (mkSB nbs call0 iscall0::sbs', nbs0) => 
      (mkSB (mkNB c isnotcall::nbs) call0 iscall0::sbs', nbs0) 
    end
  | right iscall => 
    match (cmds2sbs cs') with
    | (sbs, nbs0) => (mkSB nil c iscall::sbs, nbs0) 
    end
  end
end.


Lemma cmds2sbs_nil_inv : forall cs,
  cmds2sbs cs = (nil, nil) ->
  cs = nil.
Proof.
  destruct cs; intros; auto.
    simpl in H.
    destruct (isCallInst_dec c).
      destruct (cmds2sbs cs).
      destruct l0.
        inversion H.
        destruct s. inversion H.
      destruct (cmds2sbs cs).
      inversion H.
Qed.

Lemma cmds2sb_inv : forall cs sb,
  cmds2sbs cs = (sb::nil, nil) ->
  exists cs', exists call0,
    cs = cs'++call0::nil /\
    cmds2sbs cs' = (nil, NBs sb) /\
    call_cmd sb = call0.
Proof.
  induction cs; intros; simpl in *.
    inversion H.

    remember (cmds2sbs cs) as R.
    remember (isCallInst_dec a) as R'.
    destruct R'.
      destruct R.
      destruct l0.
        inversion H.

        destruct s. inversion H; subst. clear H.
        destruct (@IHcs (mkSB NBs0 call_cmd0 call_cmd_isCall0)) as [cs' [call0 [J1 [J2 J3]]]]; subst; auto.
        clear IHcs.
        simpl in *.
        exists (a::cs').
        exists (call_cmd0).
        split; auto.
        split; auto.
          simpl.
          rewrite J2.
          rewrite <- HeqR'. auto.

      destruct R.
      inversion H; subst. clear H.
      symmetry in HeqR.
      apply cmds2sbs_nil_inv in HeqR. subst.
      exists nil. exists a.
      split; auto.
Qed.

Definition dbCmds__cmds2nbs : forall TD lc als gl Mem1 cs lc' als' Mem2 tr, 
  dbCmds TD gl lc als Mem1 cs lc' als' Mem2 tr ->
  exists nbs, cmds2sbs cs = (nil, nbs).
Proof.
  intros.
  induction H; simpl.
    exists nil. auto.

    destruct IHdbCmds as [nbs J].
    destruct (isCallInst_dec c).
      rewrite J. exists (mkNB c e::nbs). auto.

      apply dbCmd_isNotCallInst in H.
      rewrite e in H. inversion H.
Qed.

Lemma dbCall_isCallInst : forall S TD Ps lc gl Mem1 c lc' Mem2 tr,
  dbCall S TD Ps gl lc Mem1 c lc' Mem2 tr ->
  Instruction.isCallInst c = true.
Proof.
  intros S TD Ps lc gl Mem1 c lc' Mem2 tr HdbCall.
  induction HdbCall; auto.
Qed.

Lemma cmdscall2sbs : forall cs call0 nbs
  (isCall0:Instruction.isCallInst call0=true),
  cmds2sbs cs = (nil, nbs) ->
  isCallInst_dec call0 = right isCall0 ->
  cmds2sbs (cs++call0::nil) = (mkSB nbs call0 isCall0::nil, nil).
Proof.
  induction cs; intros; simpl in *.
    inversion H; subst.
    rewrite H0. auto.

    destruct (isCallInst_dec a).
      remember (cmds2sbs cs) as R.
      destruct R.
      destruct l0.
        inversion H; subst. clear H.
        apply IHcs with (nbs:=l1) in H0; auto.
        rewrite H0; auto.
     
        destruct s. inversion H.

      destruct (cmds2sbs cs).
      inversion H.
Qed.

Lemma dbSubblock__cmds2sb : forall S TD Ps gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr,
  dbSubblock S TD Ps gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr ->
  exists sb, cmds2sbs cs = (sb::nil, nil).
Proof.
  intros.
  inversion H; subst.
  apply dbCmds__cmds2nbs in H0.
  destruct H0 as [nbs H0].
  remember (isCallInst_dec call0) as R.
  destruct R.
    apply dbCall_isCallInst in H1.
    rewrite e in H1. inversion H1.

    exists (mkSB nbs call0 e).
    apply cmdscall2sbs; auto.
Qed.

Lemma cmds_cons2sbs : forall cs cs' sb sbs',
  cmds2sbs cs = (sb::nil, nil) ->
  cmds2sbs cs' = (sbs', nil) ->
  cmds2sbs (cs++cs') = (sb::sbs', nil).
Proof.
  induction cs; intros; simpl.
    simpl in H. inversion H.

    simpl in H.
    destruct (isCallInst_dec a).
      remember (cmds2sbs cs) as R.
      destruct R.
        destruct l0.
          inversion H.

          destruct s. inversion H; subst. clear H.
          apply IHcs with (sb:=mkSB NBs0 call_cmd0 call_cmd_isCall0) in H0; auto.
          clear IHcs.
          rewrite H0. auto.
 
      remember (cmds2sbs cs) as R.
      destruct R.
      inversion H; subst. clear H.
      symmetry in HeqR.
      apply cmds2sbs_nil_inv in HeqR. subst.
      simpl.
      rewrite H0. auto.
Qed.

Lemma dbSubblocks__cmds2sbs : forall S TD Ps gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr,
  dbSubblocks S TD Ps gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr ->
  exists sbs, cmds2sbs cs = (sbs, nil).
Proof.
  intros.
  induction H; simpl.
    exists nil. auto.

    apply dbSubblock__cmds2sb in H.
    destruct H as [sb H].
    destruct IHdbSubblocks as [sbs H1].
    exists (sb::sbs).
    apply cmds_cons2sbs; auto.
Qed.

Lemma cmds_cons2sbs_inv : forall cs cs' sbs0 sb sbs',
  cmds2sbs (cs++cs') = (sbs0, nil) ->
  cmds2sbs cs = (sb::nil, nil) ->
  cmds2sbs cs' = (sbs', nil) ->
  sbs0 = sb::sbs'.
Proof.
  intros.
  apply cmds_cons2sbs with (cs':=cs')(sbs':=sbs') in H0; auto.
  rewrite H in H0.
  inversion H0; auto.
Qed.

Lemma cmds2sbs_cons_inv : forall cs0 sb sbs',
  cmds2sbs cs0 = (sb::sbs', nil) ->
  exists cs, exists cs',
    cmds2sbs cs = (sb::nil, nil) /\
    cmds2sbs cs' = (sbs', nil) /\
    cs0 = cs++cs'.
Proof.
  induction cs0; intros.
    simpl in H. inversion H.

    simpl in H.
    remember (isCallInst_dec a) as R.
    remember (cmds2sbs cs0) as R'.
    destruct R.
      destruct R'.
        destruct l0.
          inversion H.

          destruct s. inversion H; subst. clear H.
          destruct (@IHcs0 (mkSB NBs0 call_cmd0 call_cmd_isCall0) sbs') as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
          exists (a::cs). exists cs'.
          split; auto.
            simpl.
            rewrite <- HeqR.
            rewrite J1. auto.

      destruct R'.
      inversion H; subst. clear H.
      destruct sbs'.
        symmetry in HeqR'.
        apply cmds2sbs_nil_inv in HeqR'. subst.
        exists (a::nil). exists nil.
        simpl. rewrite <- HeqR. auto.

        destruct (@IHcs0 s sbs') as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
        exists (a::nil). exists (cs++cs').
        simpl. rewrite <- HeqR. auto.
Qed.

Lemma cmds_rcons2sbs : forall cs cs' sbs nbs,
  cmds2sbs cs = (sbs, nil) ->
  cmds2sbs cs' = (nil, nbs) ->
  cmds2sbs (cs++cs') = (sbs, nbs).
Proof.
  induction cs; intros.
    simpl in H. inversion H; subst. auto.

    simpl in *.
    remember (cmds2sbs cs) as R.
    destruct (isCallInst_dec a).
      destruct R.
        destruct l0.
          inversion H.

          destruct s. inversion H; subst. clear H.
          apply IHcs with (sbs:=mkSB NBs0 call_cmd0 call_cmd_isCall0::l0) in H0; auto.
          rewrite H0. auto.

      destruct R.
      inversion H; subst. clear H.
      apply IHcs with (sbs:=l0) in H0; auto.
      rewrite H0. auto.
Qed.

Lemma cmds_rcons2sbs_inv : forall cs cs' sbs0 nbs0 sbs nbs,
  cmds2sbs (cs++cs') = (sbs0, nbs0) ->
  cmds2sbs cs = (sbs, nil) ->
  cmds2sbs cs' = (nil, nbs) ->
  sbs0 = sbs /\ nbs0 = nbs.
Proof.
  intros.
  apply cmds_rcons2sbs with (cs':=cs')(nbs:=nbs) in H0; auto.
  rewrite H in H0. inversion H0; auto.
Qed.
 
Lemma cmds2nbranchs__cmds2nbs : forall cs nbs,
  cmds2nbranchs cs = Some nbs ->
  cmds2sbs cs = (nil, nbs).
Proof.
  induction cs; intros.
    simpl in H. inversion H; auto.

    simpl in *.
    unfold cmd2nbranch in H.
    destruct (isCallInst_dec a).
      destruct (cmds2sbs cs).
        remember (cmds2nbranchs cs) as R.
        destruct R.
          inversion H; subst. clear H.
          assert (ret l2 = ret l2) as EQ. auto.
          apply IHcs in EQ.
          inversion EQ; subst. auto.

          inversion H.
      inversion H.
Qed.

Lemma cmds2nbs__nbranchs2cmds : forall nbs cs,
  cmds2sbs cs = (nil, nbs) ->
  nbranchs2cmds nbs = cs.
Proof.
  induction nbs; intros.
    apply cmds2sbs_nil_inv in H. subst. auto.

    simpl.
    destruct a.
    destruct cs.
      simpl in H. inversion H.

      simpl in H.
      destruct (isCallInst_dec c).
        remember (cmds2sbs cs) as R.
        destruct R.
        destruct l0.
          inversion H; subst.
          rewrite IHnbs with (cs:=cs); auto.

          destruct s.
          inversion H; subst.

        destruct (cmds2sbs cs).
        inversion H.
Qed.


Lemma cmds2nbranchs__nbranchs2cmds : forall cs nbs,
  cmds2nbranchs cs = Some nbs ->
  nbranchs2cmds nbs = cs.
Proof.
  intros.
  apply cmds2nbs__nbranchs2cmds.
  apply cmds2nbranchs__cmds2nbs; auto.
Qed.

Lemma cmds2sbs_inv : forall cs sbs nbs,
  cmds2sbs cs = (sbs, nbs) ->
  exists cs1, exists cs2, 
    cs = cs1++cs2 /\
    cmds2sbs cs1 = (sbs, nil) /\
    cmds2sbs cs2 = (nil, nbs).
Proof.
  induction cs; intros.
    simpl in H. inversion H; subst.
    exists nil. exists nil. auto.

    simpl in H.
    remember (isCallInst_dec a) as R.
    remember (cmds2sbs cs) as R'.
    destruct R.
      destruct R'.
        destruct l0.
          inversion H; subst. clear H.
          
          destruct (@IHcs nil l1) as [cs1 [cs2 [J1 [J2 J3]]]]; subst; auto.
          apply cmds2sbs_nil_inv in J2. subst.
          exists nil. exists (a::cs2).
          simpl. rewrite <- HeqR. 
          simpl in HeqR'. rewrite <- HeqR'.
          split; auto.

       destruct s.
       inversion H; subst. clear H.
       destruct (@IHcs (mkSB NBs0 call_cmd0 call_cmd_isCall0::l0) nbs) as [cs1 [cs2 [J1 [J2 J3]]]]; subst; auto.
       clear IHcs.
       exists (a::cs1). exists cs2.
       simpl. rewrite <- HeqR. rewrite J2. auto.
    
     destruct R'.
     inversion H; subst. clear H.
     destruct (@IHcs l0 nbs) as [cs1 [cs2 [J1 [J2 J3]]]]; subst; auto.
     clear IHcs.
     exists (a::cs1). exists cs2.
     simpl. rewrite <- HeqR. rewrite J2. auto.
Qed.

Lemma cmds2sbs_cons_inv' : forall cs0 sb sbs' nbs,
  cmds2sbs cs0 = (sb::sbs', nbs) ->
  exists cs, exists cs',
    cmds2sbs cs = (sb::nil, nil) /\
    cmds2sbs cs' = (sbs', nbs) /\
    cs0 = cs++cs'.
Proof.
  induction cs0; intros.
    simpl in H. inversion H.

    simpl in H.
    remember (isCallInst_dec a) as R.
    remember (cmds2sbs cs0) as R'.
    destruct R.
      destruct R'.
        destruct l0.
          inversion H.

          destruct s. inversion H; subst. clear H.
          destruct (@IHcs0 (mkSB NBs0 call_cmd0 call_cmd_isCall0) sbs' nbs) as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
          exists (a::cs). exists cs'.
          split; auto.
            simpl.
            rewrite <- HeqR.
            rewrite J1. auto.

      destruct R'.
      inversion H; subst. clear H.
      destruct sbs'.
        symmetry in HeqR'.
        exists (a::nil). exists cs0.
        simpl. rewrite <- HeqR. auto.

        destruct (@IHcs0 s sbs' nbs) as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
        exists (a::nil). exists (cs++cs').
        simpl. rewrite <- HeqR. auto.
Qed.

  
Lemma cmds2nbs_app_inv : forall cs0 nbs1 nbs2,
  cmds2sbs cs0 = (nil, nbs1++nbs2) ->
  exists cs, exists cs',
    cmds2sbs cs = (nil, nbs1) /\
    cmds2sbs cs' = (nil, nbs2) /\
    cs0 = cs++cs'.
Proof.
  induction cs0; intros.
    simpl in H. inversion H.
    symmetry in H1.
    apply app_eq_nil in H1.
    destruct H1; subst.
    exists nil. exists nil. auto.

    simpl in H.
    remember (isCallInst_dec a) as R.
    remember (cmds2sbs cs0) as R'.
    destruct R.
      destruct R'.
        destruct l0.
          inversion H.
          apply cons_eq_app in H1.
          destruct H1 as [[qs [J1 J2]] | [J1 J2]]; subst.
            destruct (@IHcs0 qs nbs2) as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
            clear IHcs0.
            exists (a::cs). exists cs'.
            simpl. rewrite <- HeqR. rewrite J1. split; auto.

            exists nil. exists (a::cs0). 
            simpl. rewrite <- HeqR. rewrite <- HeqR'. split; auto.

          destruct s. inversion H; subst.

      destruct R'.
      inversion H; subst. 
Qed.

(* wf *)

Inductive wf_nbranchs : list nbranch -> Prop :=
| wf_nbranchs_intro : forall cs nbs, 
  cmds2sbs cs = (nil, nbs) ->
  NoDup (getCmdsIDs cs) ->
  wf_nbranchs nbs.

Lemma wf_nbranchs__decomposes__app : forall nbs1 nbs2,
  wf_nbranchs (nbs1++nbs2) ->
  wf_nbranchs nbs1 /\ wf_nbranchs nbs2.
Proof.
  intros.
  inversion H; subst.
  apply cmds2nbs_app_inv in H0.
  destruct H0 as [cs1 [cs2 [J1 [J2 J3]]]]; subst.
  rewrite getCmdsIDs_app in H1.
  apply NoDup_inv in H1.
  destruct H1.
  split; eapply wf_nbranchs_intro; eauto.
Qed.

Lemma wf_nbranchs__inv : forall nb nbs,
  wf_nbranchs (nb::nbs) ->
  wf_nbranchs nbs.
Proof.
  intros.
  simpl_env in H.
  apply wf_nbranchs__decomposes__app in H.
  destruct H; auto.
Qed.

Inductive wf_subblock : subblock -> Prop :=
| wf_subblock_intro : forall nbs call0 iscall0, 
  wf_nbranchs nbs ->
  wf_subblock (mkSB nbs call0 iscall0).

Inductive wf_subblocks : list subblock -> Prop :=
| wf_subblocks_nil : wf_subblocks nil
| wf_subblocks_cons : forall sb sbs,
  wf_subblock sb ->
  wf_subblocks sbs ->
  wf_subblocks (sb::sbs).

Inductive wf_block : block -> Prop :=
| wf_block_intro : forall l ps cs sbs nbs tmn, 
  cmds2sbs cs = (sbs,nbs) ->
  wf_subblocks sbs ->
  wf_nbranchs nbs ->
  wf_block (block_intro l ps cs tmn).

Hint Constructors wf_subblocks.

Lemma wf_nbranchs_nil : wf_nbranchs nil.
Proof.
  apply wf_nbranchs_intro with (cs:=nil); simpl; auto using NoDup_nil.
Qed.

Hint Resolve wf_nbranchs_nil.

Lemma uniqCmds___wf_subblocks_wf_nbranchs : forall cs sbs nbs,
  NoDup (getCmdsIDs cs) ->
  cmds2sbs cs = (sbs, nbs) ->
  wf_subblocks sbs /\ wf_nbranchs nbs.
Proof.
  induction cs; intros.
    simpl in H0. inversion H0; subst.
    split; auto using wf_nbranchs_nil.

    simpl in *.
    remember (cmds2sbs cs) as R.
    destruct R as [sbs' nbs'].
    remember (isCallInst_dec a) as R'.
    destruct R'.
      destruct sbs'.
        inversion H0; subst. clear H0.
        split; auto.
          apply wf_nbranchs_intro with (cs:=a::cs); auto.
            simpl.
            rewrite <- HeqR'.
            rewrite <- HeqR. auto.

        destruct s. 
        inversion H0; subst. clear H0.
        inversion H; subst.
        apply IHcs with (nbs0:=nbs)(sbs:=mkSB NBs0 call_cmd0 call_cmd_isCall0::sbs') in H3; auto.
        destruct H3 as [H3 H4].
        split; auto.
          inversion H3; subst.
          apply wf_subblocks_cons; auto.
            apply wf_subblock_intro.

            symmetry in HeqR.
            apply cmds2sbs_cons_inv' in HeqR.
            destruct HeqR as [cs1 [cs2 [Hcs1NBs0call0 [Hcs2sbs EQ]]]]; subst.
            apply cmds2sb_inv in Hcs1NBs0call0.
            destruct Hcs1NBs0call0 as [cs1' [call0 [EQ [Hcs1'nbs EQ']]]]; subst.
            simpl in *.
            simpl_env in H.
            rewrite getCmdsIDs_app in H.
            rewrite ass_app in H.
            apply NoDup_inv in H. destruct H as [H _].
            apply wf_nbranchs_intro with (cs:=a::cs1'); auto.
              simpl.
              rewrite <- HeqR'.
              rewrite Hcs1'nbs. auto.

      inversion H0; subst. clear H0.
      simpl_env in H.
      apply NoDup_inv in H. destruct H as [H1 H2].
      apply IHcs with (sbs:=sbs')(nbs0:=nbs) in H2; auto.
      destruct H2.
      split; auto.
        apply wf_subblocks_cons; auto.
          apply wf_subblock_intro; auto.
Qed.

Lemma uniqBlock__wf_block : forall B,
  uniqBlocks [B] -> wf_block B.
Proof.
  intros B HuniqBlocks.
  unfold uniqBlocks in HuniqBlocks.
  simpl in HuniqBlocks. destruct B.
  destruct HuniqBlocks as [J1 J2].
  remember (cmds2sbs c) as R.
  destruct R as [sbs nbs].
  simpl in J2. simpl_env in J2.
  apply NoDup_inv in J2. destruct J2.
  apply NoDup_inv in H0. destruct H0.
  apply uniqCmds___wf_subblocks_wf_nbranchs with (sbs:=sbs)(nbs:=nbs) in H0; auto.
  destruct H0.
  apply wf_block_intro with (sbs:=sbs)(nbs:=nbs); auto.
Qed.

Lemma uniqBlocks__wf_block : forall lb n B,
  uniqBlocks lb ->
  nth_error lb n = Some B ->
  wf_block B.
Proof.
  induction lb; intros.
    apply nil_nth_error_Some__False in H0.
    inversion H0.

    apply nth_error_cons__inv in H0.
    simpl_env in H. 
    apply uniqBlocks_inv in H.
    destruct H as [J1 J2].
    destruct H0 as [EQ | [n' [EQ H0]]]; subst; eauto.
      apply uniqBlock__wf_block; auto.
Qed.

Lemma uniqFdef__wf_block : forall fh lb n B,
  uniqFdef (fdef_intro fh lb) ->
  nth_error lb n = Some B ->
  wf_block B.
Proof.
  intros.
  unfold uniqFdef in H.
  eapply uniqBlocks__wf_block; eauto.
Qed.

(***************************************************************)
(** symbolic terms and memories. *)
Inductive sterm : Set := 
| sterm_val : value -> sterm
| sterm_bop : bop -> sz -> sterm -> sterm -> sterm
| sterm_fbop : fbop -> floating_point -> sterm -> sterm -> sterm
| sterm_extractvalue : typ -> sterm -> list_const -> sterm
| sterm_insertvalue : typ -> sterm -> typ -> sterm -> list_const -> sterm
| sterm_malloc : smem -> typ -> sz -> align -> sterm
| sterm_alloca : smem -> typ -> sz -> align -> sterm
| sterm_load : smem -> typ -> sterm -> align -> sterm
| sterm_gep : inbounds -> typ -> sterm -> list_sterm -> sterm
| sterm_trunc : truncop -> typ -> sterm -> typ -> sterm
| sterm_ext : extop -> typ -> sterm -> typ -> sterm
| sterm_cast : castop -> typ -> sterm -> typ -> sterm
| sterm_icmp : cond -> typ -> sterm -> sterm -> sterm
| sterm_fcmp : fcond -> floating_point -> sterm -> sterm -> sterm
| sterm_phi : typ -> list_sterm_l -> sterm
| sterm_select : sterm -> typ -> sterm -> sterm -> sterm
with list_sterm : Set :=
| Nil_list_sterm : list_sterm
| Cons_list_sterm : sterm -> list_sterm -> list_sterm
with list_sterm_l : Set :=
| Nil_list_sterm_l : list_sterm_l
| Cons_list_sterm_l : sterm -> l -> list_sterm_l -> list_sterm_l
with smem : Set :=
| smem_init : smem
| smem_malloc : smem -> typ -> sz -> align -> smem
| smem_free : smem -> typ -> sterm -> smem
| smem_alloca : smem -> typ -> sz -> align -> smem
| smem_load : smem -> typ -> sterm -> align -> smem
| smem_store : smem -> typ -> sterm -> sterm -> align -> smem
with sframe : Set :=
| sframe_init : sframe
| sframe_alloca : smem -> sframe -> typ -> sz -> align -> sframe
.

Scheme sterm_rec2 := Induction for sterm Sort Set
  with list_sterm_rec2 := Induction for list_sterm Sort Set
  with list_sterm_l_rec2 := Induction for list_sterm_l Sort Set
  with smem_rec2 := Induction for smem Sort Set
  with sframe_rec2 := Induction for sframe Sort Set.

Definition se_mutrec P1 P2 P3 P4 P5:=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 =>
   (pair
      (pair 
           (pair 
                 (pair (@sterm_rec2 P1 P2 P3 P4 P5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28)
                       (@list_sterm_rec2 P1 P2 P3 P4 P5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28))
                 (@list_sterm_l_rec2 P1 P2 P3 P4 P5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28))
            (@smem_rec2 P1 P2 P3 P4 P5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28))
      (@sframe_rec2 P1 P2 P3 P4 P5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28)).

Tactic Notation "se_mut_cases" tactic(first) tactic(c) :=
  first;
  [ c "sterm_val" | 
    c "sterm_bop" |
    c "sterm_fbop" |
    c "sterm_extractvalue" |
    c "sterm_insertvalue" |
    c "sterm_malloc" |
    c "sterm_alloca" |
    c "sterm_load" |
    c "sterm_gep" |
    c "sterm_trunc" |
    c "sterm_ext" |
    c "sterm_cast" |
    c "sterm_icmp" |
    c "sterm_fcmp" |
    c "sterm_phi" |
    c "sterm_select" |
    c "list_sterm_nil" |
    c "list_sterm_cons" |
    c "list_sterm_l_nil" |
    c "list_sterm_l_cons" |
    c "smem_init" |
    c "smem_malloc" |
    c "smem_free" |
    c "smem_alloca" |
    c "smem_load" |
    c "smem_store" |
    c "sframe_init" |
    c "sframe_alloca" ].

Fixpoint map_list_sterm (A:Set) (f:sterm->A) (l0:list_sterm) {struct l0} : list A :=
  match l0 with
  | Nil_list_sterm => nil
  | Cons_list_sterm h tl_ => cons (f h) (map_list_sterm A f tl_)
  end.
Implicit Arguments map_list_sterm.

Fixpoint make_list_sterm (l0:list sterm) : list_sterm :=
  match l0 with
  | nil  => Nil_list_sterm
  | cons h tl_ => Cons_list_sterm h (make_list_sterm tl_)
  end.

Fixpoint unmake_list_sterm (l0:list_sterm) :  list sterm :=
  match l0 with
  | Nil_list_sterm => nil
  | Cons_list_sterm h tl_ =>  cons h (unmake_list_sterm tl_)
  end.

Fixpoint nth_list_sterm (n:nat) (l0:list_sterm) {struct n} : option sterm :=
  match n,l0 with
  | O, Cons_list_sterm h tl_ => Some h
  | O, other => None
  | S m, Nil_list_sterm => None
  | S m, Cons_list_sterm h tl_ => nth_list_sterm m tl_
  end.
Implicit Arguments nth_list_sterm.

Fixpoint app_list_sterm (l0 m:list_sterm) {struct l0} : list_sterm :=
  match l0 with
  | Nil_list_sterm => m
  | Cons_list_sterm h tl_ => Cons_list_sterm h (app_list_sterm tl_ m)
  end.

Fixpoint map_list_sterm_l (A:Set) (f:sterm->l->A) (l0:list_sterm_l) {struct l0} : list A :=
  match l0 with
  | Nil_list_sterm_l => nil
  | Cons_list_sterm_l h0 h1 tl_ => cons (f h0 h1) (map_list_sterm_l A f tl_)
  end.
Implicit Arguments map_list_sterm_l.

Fixpoint make_list_sterm_l (l0:list (sterm*l)) : list_sterm_l :=
  match l0 with
  | nil  => Nil_list_sterm_l
  | cons (h0,h1) tl_ => Cons_list_sterm_l h0 h1 (make_list_sterm_l tl_)
  end.

Fixpoint unmake_list_sterm_l (l0:list_sterm_l) :  list (sterm*l) :=
  match l0 with
  | Nil_list_sterm_l => nil
  | Cons_list_sterm_l h0 h1 tl_ =>  cons (h0,h1) (unmake_list_sterm_l tl_)
  end.

Fixpoint nth_list_sterm_l (n:nat) (l0:list_sterm_l) {struct n} : option (sterm*l) :=
  match n,l0 with
  | O, Cons_list_sterm_l h0 h1 tl_ => Some (h0,h1)
  | O, other => None
  | S m, Nil_list_sterm_l => None
  | S m, Cons_list_sterm_l h0 h1 tl_ => nth_list_sterm_l m tl_
  end.
Implicit Arguments nth_list_sterm_l.

Fixpoint app_list_sterm_l (l0 m:list_sterm_l) {struct l0} : list_sterm_l :=
  match l0 with
  | Nil_list_sterm_l => m
  | Cons_list_sterm_l h0 h1 tl_ => Cons_list_sterm_l h0 h1 (app_list_sterm_l tl_ m)
  end.

Inductive sterminator : Set :=
| stmn_return : id -> typ -> sterm -> sterminator
| stmn_return_void : id -> sterminator
| stmn_br : id -> sterm -> l -> l -> sterminator
| stmn_br_uncond : id -> l -> sterminator
| stmn_unreachable : id -> sterminator
.

Inductive scall : Set :=
| stmn_call : id -> noret -> tailc -> typ -> id -> list (typ*sterm) -> scall
.

Definition smap := list (atom*sterm).

Record sstate : Set := mkSstate 
{
  STerms : smap;
  SMem : smem;
  SFrame : sframe;
  SEffects : list sterm
}.

Definition sstate_init := mkSstate nil smem_init sframe_init nil.

Fixpoint lookupSmap (sm:smap) (i0:id) : sterm :=
match sm with
| nil => (sterm_val (value_id i0))
| (id0, s0)::sm' => 
  if i0 == id0 then s0 else lookupSmap sm' i0
end.

Definition value2Sterm (sm:smap) (v:value) : sterm :=
match v with
| value_const _ => sterm_val v
| value_id i0 => lookupSmap sm i0
end.

Fixpoint list_param__list_typ_subst_sterm (list_param1:params) (sm:smap) : list (typ*sterm) :=
match list_param1 with
| nil => nil
| (t, v)::list_param1' => (t, (value2Sterm sm v))::(list_param__list_typ_subst_sterm list_param1' sm)
end.

Lemma se_cmd_false_elim : forall i id0 noret0 tailc0 rt fid lp,
  i=insn_call id0 noret0 tailc0 rt fid lp ->
  Instruction.isCallInst i = false ->
  False.
Proof.
  intros; subst. simpl in H0. inversion H0.
Qed.

Definition se_cmd (st : sstate) (c:nbranch) : sstate :=
match c with 
| mkNB i notcall =>
  (match i as r return (i = r -> _) with 
  | insn_bop id0 op0 sz0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_bop op0 sz0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_fbop id0 op0 fp0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_fbop op0 fp0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
 | insn_extractvalue id0 t1 v1 cs3 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_extractvalue t1 
                     (value2Sterm st.(STerms) v1)
                     cs3))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_insertvalue id0 t1 v1 t2 v2 cs3 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_insertvalue 
                     t1 
                     (value2Sterm st.(STerms) v1)
                     t2 
                     (value2Sterm st.(STerms) v2)
                     cs3))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_malloc id0 t1 sz1 al1 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_malloc st.(SMem) t1 sz1 al1))
                 (smem_malloc st.(SMem) t1 sz1 al1)
                 st.(SFrame)
                 st.(SEffects))
  | insn_free id0 t0 v0 => fun _ =>  
       (mkSstate st.(STerms)
                 (smem_free st.(SMem) t0 
                   (value2Sterm st.(STerms) v0))
                 st.(SFrame)
                 st.(SEffects))
  | insn_alloca id0 t1 sz1 al1 => fun _ =>   
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_alloca st.(SMem) t1 sz1 al1))
                 (smem_alloca st.(SMem) t1 sz1 al1)
                 (sframe_alloca st.(SMem) st.(SFrame) t1 sz1 al1)
                 st.(SEffects))
  | insn_load id0 t2 v2 align => fun _ =>   
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_load st.(SMem) t2 
                     (value2Sterm st.(STerms) v2) align))
                 (smem_load st.(SMem)t2 
                   (value2Sterm st.(STerms) v2) align)
                 st.(SFrame)
                 st.(SEffects))
  | insn_store id0 t0 v1 v2 align => fun _ =>  
       (mkSstate st.(STerms)
                 (smem_store st.(SMem) t0 
                   (value2Sterm st.(STerms) v1)
                   (value2Sterm st.(STerms) v2)
                   align)
                 st.(SFrame)
                 st.(SEffects))
  | insn_gep id0 inbounds0 t1 v1 lv2 => fun _ =>  
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_gep inbounds0 t1 
                     (value2Sterm st.(STerms) v1)
                     (make_list_sterm (map_list_value (value2Sterm st.(STerms)) lv2))))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_trunc id0 op0 t1 v1 t2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_trunc op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_ext id0 op0 t1 v1 t2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_ext op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_cast id0 op0 t1 v1 t2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_cast op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_icmp id0 c0 t0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_icmp c0 t0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_fcmp id0 c0 fp0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_fcmp c0 fp0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_select id0 v0 t0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_select 
                     (value2Sterm st.(STerms) v0)
                     t0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_call id0 noret0 tailc0 rt fid lp => 
    fun (EQ:i=insn_call id0 noret0 tailc0 rt fid lp ) =>
    False_rec sstate (@se_cmd_false_elim i id0 noret0 tailc0 rt fid lp EQ notcall)
  end) (@refl_equal _ i)
end.

Fixpoint _se_phinodes (st st0: sstate) (ps:list phinode) : sstate :=
match ps with
| nil => st
| insn_phi id0 t0 idls0::ps' =>  
    _se_phinodes 
     (mkSstate (updateAL _ st.(STerms) id0 
                 (sterm_phi 
                   t0 
                   (make_list_sterm_l
                     (map_list_value_l
                       (fun v5 l5 =>
                        ((value2Sterm st.(STerms) v5), l5)
                       )
                       idls0
                     )
                   )
                 )
               )
               st.(SMem)
               st.(SFrame)
               st.(SEffects))
     st0
     ps'
end.

Fixpoint se_phinodes (st: sstate) (ps:list phinode) := _se_phinodes st st ps.

Fixpoint se_cmds (st : sstate) (cs:list nbranch) : sstate :=
match cs with
| nil => st
| c::cs' => se_cmds (se_cmd st c) cs'
end.

Definition se_terminator (st : sstate) (i:terminator) : sterminator :=
match i with 
| insn_return id0 t0 v0 => stmn_return id0 t0 (value2Sterm st.(STerms) v0)
| insn_return_void id0 => stmn_return_void id0 
| insn_br id0 v0 l1 l2 => stmn_br id0 (value2Sterm st.(STerms) v0) l1 l2
| insn_br_uncond id0 l0 => stmn_br_uncond id0 l0
| insn_unreachable id0 => stmn_unreachable id0 
end.

Definition se_call : forall (st : sstate) (i:cmd) (iscall:Instruction.isCallInst i = true), scall.
Proof.
  intros. unfold Instruction.isCallInst in iscall. unfold _isCallInsnB in iscall.
  destruct i0; try solve [inversion iscall].
  apply (@stmn_call i0 n t t0 i1 
                      (list_param__list_typ_subst_sterm p st.(STerms))).
Defined.

(* Properties of se *)

Lemma se_cmd_uniq : forall smap0 sm0 sf0 se0 c,
  uniq smap0 ->
  uniq (STerms (se_cmd (mkSstate smap0 sm0 sf0 se0) c)).
Proof.
  intros smap0 sm0 sf0 se0 [c nocall] Huniq.
  destruct c; simpl; 
    try solve [
      apply updateAddAL_uniq; auto | 
      auto | 
      inversion nocall].
Qed.

Lemma se_cmd_dom_mono : forall smap0 sm0 sf0 se0 c,
  dom smap0 [<=] dom (STerms (se_cmd (mkSstate smap0 sm0 sf0 se0) c)).
Proof.
  intros smap0 sm0 sf0 se0 [c nocall].
  assert (forall sm id0 st0, dom sm [<=] dom (updateAddAL sterm sm id0 st0)) as J.
    intros. assert (J:=@updateAddAL_dom_eq _ sm id0 st0). fsetdec. 
  destruct c; simpl; try solve [eauto using J| fsetdec|inversion nocall].
Qed.

Lemma _se_cmd_uniq : forall c sstate0,
  uniq (STerms sstate0) ->
  uniq (STerms (se_cmd sstate0 c)).
Proof.
  intros [c nocall] sstate0 Huniq.
  destruct c; simpl; try solve [apply updateAddAL_uniq; auto | auto | inversion nocall].
Qed.

Lemma _se_cmds_uniq : forall cs sstate0,
  uniq (STerms sstate0) ->
  uniq (STerms (se_cmds sstate0 cs)).
Proof.
  induction cs; intros; simpl; auto using _se_cmd_uniq.
Qed.

Lemma se_cmds_uniq : forall cs smap0 sm0 sf0 se0,
  uniq smap0 ->
  uniq (STerms (se_cmds (mkSstate smap0 sm0 sf0 se0) cs)).
Proof.
  intros.
  apply _se_cmds_uniq; auto. 
Qed.

Lemma se_cmds_init_uniq : forall cs,
  uniq (STerms (se_cmds sstate_init cs)).
Proof.
  unfold sstate_init. intro. auto using se_cmds_uniq.
Qed.

Lemma se_cmds_rev_cons : forall cs c sstate0,
  se_cmds sstate0 (cs++c::nil) = se_cmd (se_cmds sstate0 cs) c.
Proof.
  induction cs; intros; simpl; auto.
Qed.

Lemma se_cmds_app : forall cs cs' sstate0,
  se_cmds sstate0 (cs++cs') = se_cmds (se_cmds sstate0 cs) cs'.
Proof.
  induction cs; intros; simpl; auto.
Qed.

Lemma se_cmds_cons : forall cs c sstate0,
  se_cmds sstate0 ((c::nil)++cs) = se_cmds (se_cmd sstate0 c) cs.
Proof.
  induction cs; intros; simpl; auto.
Qed.

Lemma se_cmd_dom_upper : forall sstate0 c nc,
  dom (STerms (se_cmd sstate0 (mkNB c nc))) [<=] dom (STerms sstate0) `union` {{getCmdID c}}.
Proof.
  intros [smap0 sm0 sf0 se0] c nc.
  destruct c; simpl; try solve [rewrite updateAddAL_dom_eq; fsetdec | fsetdec | inversion nc].
Qed.

Lemma se_cmd_dom_mono' : forall sstate0 c,
  dom (STerms sstate0) [<=] dom (STerms (se_cmd sstate0 c)).
Proof.
  intros [smap0 sm0 sf0 se0] c. 
  simpl.
  apply se_cmd_dom_mono; auto.
Qed.

Definition se_cmds_dom_mono_prop (cs:list nbranch) :=
  forall smap0 sm0 sf0 se0,
  dom smap0 [<=]
    dom (STerms (se_cmds (mkSstate smap0 sm0 sf0 se0) cs)).

Lemma se_cmds_dom_mono: forall cs, se_cmds_dom_mono_prop cs.
Proof.
  apply (@rev_ind nbranch); unfold se_cmds_dom_mono_prop; intros; simpl.
    fsetdec.

    rewrite se_cmds_rev_cons.
    assert (J:=@se_cmd_dom_mono' (se_cmds (mkSstate smap0 sm0 sf0 se0) l0) x).
    assert (J':=@H smap0 sm0 sf0 se0).
    fsetdec.
Qed.

Lemma se_cmds_dom_mono' : forall sstate0 cs,
  dom (STerms sstate0) [<=] dom (STerms (se_cmds sstate0 cs)).
Proof.
  intros [smap0 sm0 sf0 se0] cs. 
  simpl.
  apply se_cmds_dom_mono; auto.
Qed.

(* props of lookupSmap *)

Lemma lookupSmap_in : forall sm id0 st0,
  uniq sm ->
  binds id0 st0 sm ->
  lookupSmap sm id0 = st0.
Proof.
  induction sm; intros.
    inversion H0.

    destruct a.
    simpl in *.
    inversion H; subst.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst; simpl;
      analyze_binds_uniq H0; auto.
Qed.

Lemma id2Sterm_in : forall sm id0 st0,
  uniq sm ->
  binds id0 st0 sm ->
  value2Sterm sm (value_id id0) = st0.
Proof.
  intros. simpl. apply lookupSmap_in; auto.
Qed.

Lemma lookupSmap_notin : forall sm id0,
  uniq sm ->
  id0 `notin` dom sm ->
  lookupSmap sm id0 = sterm_val (value_id id0).
Proof.
  induction sm; intros; simpl; auto.
    destruct a.
    simpl in *.
    inversion H; subst.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst; simpl;
      analyze_binds_uniq H0; auto.
Qed.

Lemma id2Sterm_notin : forall sm id0,
  uniq sm ->
  id0 `notin` dom sm ->
  value2Sterm sm (value_id id0) = sterm_val (value_id id0).
Proof.
  intros. simpl. apply lookupSmap_notin; auto.
Qed.

Lemma const2Sterm : forall sm c,
  value2Sterm sm (value_const c) = sterm_val (value_const c).
Proof.
  intros. auto.
Qed.
       
Lemma lookupSmap_in_lookupAL : forall m id0,
  id0 `in` dom m ->
  lookupAL _ m id0 = Some (lookupSmap m id0).
Proof.
  induction m; intros id0 id0inm; simpl.
    contradict id0inm; auto.

    destruct a.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); subst; simpl; auto.
        contradict n; auto.
      assert (id0 = a \/ id0 `in` dom m) as id0in. simpl in id0inm. fsetdec.
      destruct id0in as [EQ | id0in]; subst.
        contradict n; auto.
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; auto.
          contradict n; auto.
Qed.

Lemma lookupSmap_updateAddAL_neq : forall m id0 id1 gv0,
  id1 <> id0 ->
  lookupSmap m id1 = lookupSmap (updateAddAL _ m id0 gv0) id1.
Proof.
  induction m; intros; simpl; auto.
    destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) id1 id0); subst; auto.
      contradict H; auto.

    destruct a.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); subst; simpl; auto.
        contradict H; auto.
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; simpl; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
            contradict H; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) a a); subst; simpl; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 a); subst; simpl; auto.
              contradict n; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 a); subst; simpl; auto.
Qed.   

Lemma lookupSmap_updateAddAL_eq : forall m id0 gv0,
  lookupSmap (updateAddAL _ m id0 gv0) id0 = gv0.
Proof.
  induction m; intros; simpl.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 id0); subst; simpl; auto.
      contradict n; auto.  

    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) a a); subst; simpl; auto.
        contradict n; auto.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst; simpl; auto.
        contradict n; auto.
Qed.

Lemma lookupSmap_se_cmd_neq : forall c id' smap1 smem1 sframe1 seffects1 nc,
  getCmdID c <> id' ->
  lookupSmap (STerms (se_cmd (mkSstate smap1 smem1 sframe1 seffects1) (mkNB c nc))) id' =
  lookupSmap smap1 id'.
Proof.
  destruct c; intros id' smap1 smem1 sframe1 seffects1 nc HnEQ; simpl;
    try solve [rewrite <- lookupSmap_updateAddAL_neq; auto | inversion nc | auto].
Qed.

(***************************************************************)
(* Denotational semantics of symbolic exe *)

Inductive sterm_denotes_genericvalue : 
   layouts ->               (* CurTatgetData *)
   GVMap ->                 (* local registers *)
   GVMap ->                 (* global variables *)
   mem ->                   (* Memory *)
   sterm ->                 (* symbolic term *)
   GenericValue ->          (* value that denotes sterm *)
   Prop :=
| sterm_val_denotes : forall TD lc gl Mem v gv,
  getOperandValue TD v lc gl = Some gv ->  
  sterm_denotes_genericvalue TD lc gl Mem (sterm_val v) gv
| sterm_bop_denotes : forall TD lc gl Mem op0 sz0 st1 st2 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  mbop TD op0 sz0 gv1 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_bop op0 sz0 st1 st2) gv3
| sterm_fbop_denotes : forall TD lc gl Mem op0 fp0 st1 st2 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  mfbop TD op0 fp0 gv1 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_fbop op0 fp0 st1 st2) gv3
| sterm_extractvalue_denotes : forall TD lc gl Mem t1 st1 idxs0 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  extractGenericValue TD t1 gv1 idxs0 = Some gv2 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_extractvalue t1 st1 idxs0) gv2
| sterm_insertvalue_denotes : forall TD lc gl Mem t1 st1 t2 st2 idxs0 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  insertGenericValue TD t1 gv1 idxs0 t2 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_insertvalue t1 st1 t2 st2 idxs0) gv3
| sterm_malloc_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 sz0 align0 tsz0 Mem2 mb,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  getTypeAllocSize TD t0 = Some tsz0 ->
  malloc TD Mem1 (tsz0 * sz0)%nat align0 = Some (Mem2, mb) ->
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_malloc sm0 t0 sz0 align0) (blk2GV TD mb)
| sterm_alloca_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 sz0 align0 tsz0 Mem2 mb,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  getTypeAllocSize TD t0 = Some tsz0 ->
  malloc TD Mem1 (tsz0 * sz0)%nat align0 = Some (Mem2, mb) ->
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_alloca sm0 t0 sz0 align0) (blk2GV TD mb)
| sterm_load_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 align0 st0 gv0 gv1,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 ->
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  mload TD Mem1 gv0 t0 align0 = Some gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_load sm0 t0 st0 align0) gv1
| sterm_gep_denotes : forall TD lc gl Mem ib0 t0 st0 sts0 gv0 gvs0 gv1,
  sterm_denotes_genericvalue TD lc gl Mem st0 gv0 ->
  sterms_denote_genericvalues TD lc gl Mem sts0 gvs0 ->
  GEP TD t0 gv0 gvs0 ib0 = Some gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_gep ib0 t0 st0 sts0) gv1
| sterm_trunc_denotes : forall TD lc gl Mem op0 t1 st1 t2 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  mtrunc TD op0 t1 gv1 t2 = Some gv2 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_trunc op0 t1 st1 t2) gv2
| sterm_ext_denotes : forall TD lc gl Mem op0 t1 st1 t2 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  mext TD op0 t1 gv1 t2 = Some gv2 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_ext op0 t1 st1 t2) gv2
| sterm_cast_denotes : forall TD lc gl Mem op0 t1 st1 t2 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  mcast TD op0 t1 gv1 t2 = Some gv2 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_cast op0 t1 st1 t2) gv2
| sterm_icmp_denotes : forall TD lc gl Mem cond0 t0 st1 st2 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  micmp TD cond0 t0 gv1 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_icmp cond0 t0 st1 st2) gv3
| sterm_fcmp_denotes : forall TD lc gl Mem cond0 fp0 st1 st2 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  mfcmp TD cond0 fp0 gv1 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_fcmp cond0 fp0 st1 st2) gv3
| sterm_select_denotes : forall TD lc gl Mem st0 t0 st1 st2 gv0 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st0 gv0 ->
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  (if isGVZero TD gv0 then gv2 else gv1) = gv3 -> 
  sterm_denotes_genericvalue TD lc gl Mem (sterm_select st0 t0 st1 st2) gv3
with sterms_denote_genericvalues : 
   layouts ->               (* CurTatgetData *)
   GVMap ->                 (* local registers *)
   GVMap ->                 (* global variables *)
   mem ->                   (* Memory *)
   list_sterm ->            (* symbolic terms *)
   list GenericValue ->     (* values that denote sterms *)
   Prop :=
| sterms_nil_denote : forall TD lc gl Mem,
  sterms_denote_genericvalues TD lc gl Mem Nil_list_sterm nil
| sterms_cons_denote : forall TD lc gl Mem sts st gvs gv,
  sterms_denote_genericvalues TD lc gl Mem sts gvs ->
  sterm_denotes_genericvalue TD lc gl Mem st gv ->
  sterms_denote_genericvalues TD lc gl Mem (Cons_list_sterm st sts) (gv::gvs)
with smem_denotes_mem : 
   layouts ->               (* CurTatgetData *)
   GVMap ->                 (* local registers *)
   GVMap ->                 (* global variables *)
   mem ->                   (* Memory *)
   smem ->                  (* symbolic mem *)
   mem ->                   (* value that denotes smem *)
   Prop :=
| smem_init_denotes : forall TD lc gl Mem,
  smem_denotes_mem TD lc gl Mem smem_init Mem
| smem_malloc_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 sz0 align0 tsz0 Mem2 mb,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  getTypeAllocSize TD t0 = Some tsz0 ->
  malloc TD Mem1 (tsz0 * sz0)%nat align0 = Some (Mem2, mb) ->
  smem_denotes_mem TD lc gl Mem0 (smem_malloc sm0 t0 sz0 align0) Mem2
| smem_free_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 st0 gv0 Mem2,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 ->
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  free TD Mem1 gv0 = Some Mem2->
  smem_denotes_mem TD lc gl Mem0 (smem_free sm0 t0 st0) Mem2
| smem_alloca_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 sz0 align0 tsz0 Mem2 mb,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  getTypeAllocSize TD t0 = Some tsz0 ->
  malloc TD Mem1 (tsz0 * sz0)%nat align0 = Some (Mem2, mb) ->
  smem_denotes_mem TD lc gl Mem0 (smem_alloca sm0 t0 sz0 align0) Mem2
| smem_load_denotes : forall TD lc gl Mem0 sm0 t0 st0 align0 Mem1,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  smem_denotes_mem TD lc gl Mem0 (smem_load sm0 t0 st0 align0) Mem1
| smem_store_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 st1 st2 align0 gv1 gv2  Mem2,
  sterm_denotes_genericvalue TD lc gl Mem0 st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st2 gv2 ->
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  mstore TD Mem1 gv2 t0 gv1 align0 = Some Mem2 ->
  smem_denotes_mem TD lc gl Mem0 (smem_store sm0 t0 st1 st2 align0) Mem2
.

Inductive sframe_denotes_frame : 
   layouts ->               (* CurTatgetData *)
   GVMap ->                 (* local registers *)
   GVMap ->                 (* global variables *)
   list mblock ->           (* Track memory allocated by alloca *)
   mem ->                  (* mem *)
   sframe ->                (* symbolic frame *)
   list mblock ->           (* allocas that denotes sframe *)
   Prop :=
| sframe_init_denotes : forall TD lc gl Mem als,
  sframe_denotes_frame TD lc gl als Mem sframe_init als
| sframe_alloca_denotes : forall TD lc gl Mem0 Mem1 als0 als1 t0 sz0 align0 tsz0 Mem2 mb sm0 sf0,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  sframe_denotes_frame TD lc gl als0 Mem0 sf0 als1 ->
  getTypeAllocSize TD t0 = Some tsz0 ->
  malloc TD Mem1 (tsz0 * sz0)%nat align0 = Some (Mem2, mb) ->
  sframe_denotes_frame TD lc gl als0 Mem0 (sframe_alloca sm0 sf0 t0 sz0 align0) (mb::als1)
.

Inductive seffects_denote_trace : 
   list sterm ->            (* symbolic effects *)
   trace ->                 (* trace that denotes seffects *)
   Prop :=
| seffects_nil_denote : 
  seffects_denote_trace nil trace_nil
.

Hint Constructors sterm_denotes_genericvalue sterms_denote_genericvalues 
                  smem_denotes_mem sframe_denotes_frame seffects_denote_trace.

Scheme sterm_denotes_genericvalue_ind2 := Induction for sterm_denotes_genericvalue Sort Prop
  with sterms_denote_genericvalues_ind2 := Induction for sterms_denote_genericvalues Sort Prop
  with smem_denotes_mem_ind2 := Induction for smem_denotes_mem Sort Prop.

Combined Scheme sd_mutind from sterm_denotes_genericvalue_ind2, 
                               sterms_denote_genericvalues_ind2, 
                               smem_denotes_mem_ind2.

Tactic Notation "sd_mutind_cases" tactic(first) tactic(c) :=
  first;
[ c "sterm_val_denotes"
| c "sterm_bop_denotes"
| c "sterm_fbop_denotes"
| c "sterm_extractvalue_denotes"
| c "sterm_insertvalue_denotes"
| c "sterm_malloc_denotes"
| c "sterm_alloca_denotes"
| c "sterm_load_denotes"
| c "sterm_gep_denotes"
| c "sterm_trunc_denotes"
| c "sterm_ext_denotes"
| c "sterm_cast_denotes"
| c "sterm_icmp_denotes" 
| c "sterm_fcmp_denotes" 
| c "sterm_select_denotes"
| c "sterms_nil_denote"
| c "sterms_cons_denote"
| c "smem_init_denotes"
| c "smem_malloc_denotes"
| c "smem_free_denotes"
| c "smem_alloca_denotes"
| c "smem_load_denotes"
| c "smem_store_denotes" ].

Definition smap_denotes_gvmap TD lc gl Mem smap' lc' :=
(forall id',  
  id' `in` dom smap' `union` dom lc ->
  exists gv',
    sterm_denotes_genericvalue TD lc gl Mem (lookupSmap smap' id') gv' /\
    lookupAL _ lc' id' = Some gv') /\
(forall id' gv',  
  lookupAL _ lc' id' = Some gv' ->
  sterm_denotes_genericvalue TD lc gl Mem (lookupSmap smap' id') gv'
).

Definition sstate_denotes_state TD lc gl als Mem sstate' lc' als' mem' tr :=
smap_denotes_gvmap TD lc gl Mem sstate'.(STerms) lc' /\
smem_denotes_mem TD lc gl Mem sstate'.(SMem) mem' /\
sframe_denotes_frame TD lc gl als Mem sstate'.(SFrame) als' /\
seffects_denote_trace sstate'.(SEffects) tr.

Lemma init_denotes_id : forall TD lc gl als Mem0,
  sstate_denotes_state TD lc gl als Mem0 sstate_init lc als Mem0 trace_nil.
Proof.
  intros TD lc gl als Mem0.
  split; auto.
    split; intros; simpl in *; auto.
      assert (id' `in` dom lc) as id'_in_lc. fsetdec.
      apply indom_lookupAL_Some in id'_in_lc.
      destruct id'_in_lc as [gv' id'_gv'_in_lc].
      exists gv'. split; auto.
Qed.

Lemma id_denotes_gv : forall id0 TD Mem0 gl lc,
  id0 `in` dom lc ->
  exists gv0,
    sterm_denotes_genericvalue TD lc gl Mem0 (sterm_val (value_id id0)) gv0 /\
    lookupAL _ lc id0 = Some gv0.
Proof.
  intros id0 TD Mem0 gl lc Hin.
  apply indom_lookupAL_Some in Hin.
  destruct Hin as [gv0 Hin].
  exists gv0. split; auto.
Qed.

Lemma init_denotes_gvmap :forall TD lc gl Mem0,
  uniq lc ->
  smap_denotes_gvmap TD lc gl Mem0 nil lc.
Proof.
  intros TD lc gl Mem0 Uniqc.
  unfold smap_denotes_gvmap.
  split; intros; simpl; auto.
    apply id_denotes_gv; auto. 
      fsetdec.
Qed.

(* The denotational rules are determinastic. *)

Definition sterm_denotes_genericvalue_det_prop TD lc gl Mem0 st0 gv1 
  (sd:sterm_denotes_genericvalue TD lc gl Mem0 st0 gv1) :=
  forall gv2,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv2 ->
  gv1 = gv2.

Definition sterms_denote_genericvalues_det_prop TD lc gl Mem0 sts0 gvs1
  (ds:sterms_denote_genericvalues TD lc gl Mem0 sts0 gvs1) :=
  forall gvs2,
  sterms_denote_genericvalues TD lc gl Mem0 sts0 gvs2 ->
  gvs1 = gvs2.

Definition smem_denotes_mem_det_prop TD lc gl Mem0 st0 Mem1
  (sd:smem_denotes_mem TD lc gl Mem0 st0 Mem1) :=
  forall Mem2,
  smem_denotes_mem TD lc gl Mem0 st0 Mem2 ->
  Mem1 = Mem2.

Lemma sdenotes_det : 
  (forall TD lc gl Mem0 st0 gv1 sd, @sterm_denotes_genericvalue_det_prop TD lc gl Mem0 st0 gv1 sd) /\
  (forall TD lc gl Mem0 sts0 gvs1 sd, @sterms_denote_genericvalues_det_prop TD lc gl Mem0 sts0 gvs1 sd) /\
  (forall TD lc gl Mem0 st0 Mem1 sd, @smem_denotes_mem_det_prop TD lc gl Mem0 st0 Mem1 sd).
Proof.
(sd_mutind_cases
  apply sd_mutind with
    (P  := sterm_denotes_genericvalue_det_prop)
    (P0 := sterms_denote_genericvalues_det_prop)
    (P1 := smem_denotes_mem_det_prop) Case);
  unfold sterm_denotes_genericvalue_det_prop, 
         sterms_denote_genericvalues_det_prop, 
         smem_denotes_mem_det_prop; intros.
Case "sterm_val_denotes".
  inversion H; subst.
  rewrite e in H5. inversion H5; auto.
Case "sterm_bop_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e.
  inversion e; auto.
Case "sterm_fbop_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e.
  inversion e; auto.
Case "sterm_extractvalue_denotes".
  inversion H0; subst.
  apply H in H9; subst.
  rewrite H10 in e.
  inversion e; auto.
Case "sterm_insertvalue_denotes".
  inversion H1; subst.
  apply H in H12; subst.
  apply H0 in H13; subst.
  rewrite H14 in e.
  inversion e; auto.
Case "sterm_malloc_denotes".
  inversion H0; subst.
  rewrite e in H11. inversion H11; subst.
  apply H in H10; subst.
  rewrite H12 in e0. inversion e0; auto.
Case "sterm_alloca_denotes".
  inversion H0; subst.
  rewrite e in H11. inversion H11; subst.
  apply H in H10; subst.
  rewrite H12 in e0. inversion e0; auto.
Case "sterm_load_denotes".
  inversion H1; subst.
  apply H0 in H12; subst.
  apply H in H11; subst.
  rewrite e in H13. inversion H13; auto.
Case "sterm_gep_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e. inversion e; auto.
Case "sterm_trunc_denotes".
  inversion H0; subst.
  apply H in H10; subst.
  rewrite H11 in e.
  inversion e; auto.
Case "sterm_ext_denotes".
  inversion H0; subst.
  apply H in H10; subst.
  rewrite H11 in e.
  inversion e; auto.
Case "sterm_cast_denotes".
  inversion H0; subst.
  apply H in H10; subst.
  rewrite H11 in e.
  inversion e; auto.
Case "sterm_icmp_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e. inversion e; auto.
Case "sterm_fcmp_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e. inversion e; auto.
Case "sterm_select_denotes".
  inversion H2; subst.
  apply H in H11; subst.
  apply H0 in H13; subst.
  apply H1 in H14; subst; auto.
Case "sterms_nil_denote".
  inversion H; auto.
Case "sterms_cons_denote".
  inversion H1; subst.
  apply H in H8; subst.
  apply H0 in H10; subst; auto.
Case "smem_init_denotes".
  inversion H; auto.
Case "smem_malloc_denotes".
  inversion H0; subst.
  apply H in H10; subst. 
  rewrite H11 in e. inversion e; subst.
  rewrite H12 in e0. inversion e0; auto.
Case "smem_free_denotes".
  inversion H1; subst.
  apply H in H9; subst. 
  apply H0 in H11; subst. 
  rewrite H12 in e. inversion e; auto.
Case "smem_alloca_denotes".
  inversion H0; subst.
  apply H in H10; subst. 
  rewrite H11 in e. inversion e; subst.
  rewrite H12 in e0. inversion e0; auto.
Case "smem_load_denotes".
  inversion H0; subst.
  apply H in H10; auto. 
Case "smem_store_denotes".
  inversion H2; subst.
  apply H in H13; subst. 
  apply H0 in H14; subst. 
  apply H1 in H15; subst. 
  rewrite H16 in e. inversion e; auto.
Qed.

Lemma sterm_denotes_genericvalue_det : forall TD lc gl Mem0 st0 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv2 ->
  gv1 = gv2.
Proof.
  destruct sdenotes_det as [J _].
  unfold sterm_denotes_genericvalue_det_prop in J.
  eauto.
Qed.

Lemma sterms_denote_genericvalues_det : forall TD lc gl Mem0 sts0 gvs1 gvs2,
  sterms_denote_genericvalues TD lc gl Mem0 sts0 gvs1 ->
  sterms_denote_genericvalues TD lc gl Mem0 sts0 gvs2 ->
  gvs1 = gvs2.
Proof.
  destruct sdenotes_det as [_ [J _]].
  unfold sterms_denote_genericvalues_det_prop in J.
  eauto.
Qed.

Lemma smem_denotes_mem_det : forall TD lc gl Mem0 st0 Mem1 Mem2,
  smem_denotes_mem TD lc gl Mem0 st0 Mem1 ->
  smem_denotes_mem TD lc gl Mem0 st0 Mem2 ->
  Mem1 = Mem2.
Proof.
  destruct sdenotes_det as [_ [_ J]].
  unfold smem_denotes_mem_det_prop in J.
  eauto.
Qed.

Lemma sframe_denotes_frame_det : forall TD lc gl als Mem0 st0 als1 als2,
  sframe_denotes_frame TD lc gl als Mem0 st0 als1 ->
  sframe_denotes_frame TD lc gl als Mem0 st0 als2 ->
  als1 = als2.
Proof.
  intros.
  generalize dependent als2.
  induction H; intros.
    inversion H0; auto.

    inversion H3; subst.
    apply smem_denotes_mem_det with (Mem1:=Mem4) in H; auto; subst.
    rewrite H1 in H17. inversion H17; subst.
    rewrite H18 in H2. inversion H2; subst.
    apply IHsframe_denotes_frame in H16; subst; auto.
Qed.

Lemma seffects_denote_trace_det : forall ses tr1 tr2,
  seffects_denote_trace ses tr1 ->
  seffects_denote_trace ses tr2 ->
  tr1 = tr2.
Proof.
  intros. 
  inversion H; subst.
  inversion H0; subst; auto.
Qed.

Lemma lookupSmap_inv : forall m id0 st0,
  lookupSmap m id0 = st0 ->
  (id0 `in` dom m /\ binds id0 st0 m) \/ 
  (id0 `notin` dom m /\ st0 = sterm_val (value_id id0)).
Proof.
  induction m; intros id0 st0 HlkSmap; simpl in *.
    right. auto.

    destruct a.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst.
      left. auto.

      remember (lookupSmap m id0) as st0.
      symmetry in Heqst0.
      apply IHm in Heqst0.
      destruct Heqst0 as [[id0in binds_id0_st0] | [id0notin EQ]]; subst; auto.
Qed.


Lemma sterm_val_denotes_in : forall TD lc gl Mem0 id0 gv,
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_val (value_id id0)) gv ->
  id0 `in` dom lc.
Proof.
  intros TD lc gl Mem0 id0 gv Hdenotes.
  inversion Hdenotes; subst.
  simpl in H4.
  apply lookupAL_Some_indom in H4; auto.
Qed.

Lemma smap_denotes_gvmap_det : forall TD lc gl Mem0 smap0 lc1 lc2,
  uniq smap0 ->
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc1 ->
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc2 ->
  eqAL _ lc1 lc2.
Proof.
  intros TD lc gl Mem0 smap0 lc1 lc2 Uniq J1 J2.
  destruct J1 as [J11 J12].
  destruct J2 as [J21 J22].
  intros id0.
  remember (lookupAL _ lc1 id0) as ogv1.
  remember (lookupAL _ lc2 id0) as ogv2.
  destruct ogv1 as [gv1 | ].
    symmetry in Heqogv1.
    apply J12 in Heqogv1.
    destruct (@AtomSetProperties.In_dec id0 (dom smap0)) as [id0_in_smap0 | id0_notin_smap0].
      assert (id0 `in` dom smap0 `union` dom lc) as id0_in_smap0_lc. auto.
      apply J21 in id0_in_smap0_lc.
      destruct id0_in_smap0_lc as [gv' [id0_denotes_gv' id0_in_lc2]].
      rewrite id0_in_lc2 in Heqogv2. inversion Heqogv2; subst.
      apply sterm_denotes_genericvalue_det with (gv2:=gv1) in id0_denotes_gv'; auto.
      subst. auto.
      
      apply lookupSmap_notin in id0_notin_smap0; auto.
      rewrite id0_notin_smap0 in Heqogv1.
      assert (id0_in_lc:=@sterm_val_denotes_in TD lc gl Mem0 id0 gv1 Heqogv1).
      assert (id0 `in` dom smap0 `union` dom lc) as id0_in_smap0_lc. auto.
      apply J21 in id0_in_smap0_lc.
      destruct id0_in_smap0_lc as [gv' [id0_denotes_gv' id0_in_lc2]].
      rewrite id0_in_lc2 in Heqogv2. inversion Heqogv2; subst.
      rewrite id0_notin_smap0 in id0_denotes_gv'.
      apply sterm_denotes_genericvalue_det with (gv2:=gv1) in id0_denotes_gv'; auto.
      subst. auto.
    
  destruct ogv2 as [gv2 | ]; auto.
    symmetry in Heqogv2.
    apply J22 in Heqogv2.
    destruct (@AtomSetProperties.In_dec id0 (dom smap0)) as [id0_in_smap0 | id0_notin_smap0].
      assert (id0 `in` dom smap0 `union` dom lc) as id0_in_smap0_lc. auto.   
      apply J11 in id0_in_smap0_lc.
      destruct id0_in_smap0_lc as [gv' [id0_denotes_gv' id0_in_lc1]].
      rewrite id0_in_lc1 in Heqogv1.
      inversion Heqogv1.

      apply lookupSmap_notin in id0_notin_smap0; auto.
      rewrite id0_notin_smap0 in Heqogv2.
      assert (id0_in_lc:=@sterm_val_denotes_in TD lc gl Mem0 id0 gv2 Heqogv2).
      assert (id0 `in` dom smap0 `union` dom lc) as id0_in_smap0_lc. auto.
      apply J11 in id0_in_smap0_lc.
      destruct id0_in_smap0_lc as [gv' [id0_denotes_gv' id0_in_lc1]].
      rewrite id0_in_lc1 in Heqogv1. inversion Heqogv1; subst.
Qed.

Lemma sstate_denotes_state_det : forall TD lc gl als Mem0 sstate0 lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2,
  uniq (STerms sstate0) ->
  sstate_denotes_state TD lc gl als Mem0 sstate0 lc1 als1 Mem1 tr1 ->
  sstate_denotes_state TD lc gl als Mem0 sstate0 lc2 als2 Mem2 tr2 ->
  eqAL _ lc1 lc2 /\ als1 = als2 /\ Mem1 = Mem2 /\ tr1 = tr2.
Proof.
  intros TD lc gl als Mem0 sstate0 lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 Uniq J1 J2.
  destruct J1 as [J11 [J12 [J13 J14]]].
  destruct J2 as [J21 [J22 [J23 J24]]].
  apply smem_denotes_mem_det with (Mem2:=Mem2) in J12; auto; subst.
  apply sframe_denotes_frame_det with (als2:=als2) in J13; auto; subst.
  apply seffects_denote_trace_det with (tr2:=tr2) in J14; auto; subst.
  apply smap_denotes_gvmap_det with (lc2:=lc2) in J11; auto.
Qed.

Lemma smap_denotes_gvmap_eqEnv : forall TD lc gl Mem0 smap0 lc1 lc2,
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc1 ->
  eqAL _ lc1 lc2 ->
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc2.
Proof.
  intros TD lc gl Mem0 smap0 lc1 lc2 [H1 H2] H3.
  split; intros.
    apply H1 in H.
    destruct H as [gv' [st'_denotes_gv' id'_gv'_is_env1]].
    exists gv'. rewrite <- H3.
    split; auto.

    rewrite <- H3 in H.
    apply H2 in H; auto.
Qed.


(* Definions below have not been used yet. *)

Fixpoint subst_tt (id0:id) (s0:sterm) (s:sterm) : sterm :=
match s with
| sterm_val (value_id id1) => if id0 == id1 then s0 else s
| sterm_val (value_const c) => sterm_val (value_const c)
| sterm_bop op sz s1 s2 => 
    sterm_bop op sz (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_fbop op fp s1 s2 => 
    sterm_fbop op fp (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_extractvalue t1 s1 cs => 
    sterm_extractvalue t1 (subst_tt id0 s0 s1) cs
| sterm_insertvalue t1 s1 t2 s2 cs => 
    sterm_insertvalue t1 (subst_tt id0 s0 s1) t2 (subst_tt id0 s0 s2) cs
| sterm_malloc m1 t1 sz align => 
    sterm_malloc (subst_tm id0 s0 m1) t1 sz align
| sterm_alloca m1 t1 sz align => 
    sterm_alloca (subst_tm id0 s0 m1) t1 sz align
| sterm_load m1 t1 s1 align => 
    sterm_load (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) align
| sterm_gep inbounds t1 s1 ls2 =>
    sterm_gep inbounds t1 (subst_tt id0 s0 s1) (subst_tlt id0 s0 ls2)
| sterm_trunc truncop t1 s1 t2 => 
    sterm_trunc truncop t1 (subst_tt id0 s0 s1) t2
| sterm_ext extop t1 s1 t2 => 
    sterm_ext extop t1 (subst_tt id0 s0 s1) t2
| sterm_cast castop t1 s1 t2 => 
    sterm_cast castop t1 (subst_tt id0 s0 s1) t2
| sterm_icmp cond t1 s1 s2 => 
    sterm_icmp cond t1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_fcmp cond fp1 s1 s2 => 
    sterm_fcmp cond fp1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_phi t1 lsl1 => 
    sterm_phi t1 (subst_tltl id0 s0 lsl1)
| sterm_select s1 t1 s2 s3 => 
    sterm_select (subst_tt id0 s0 s1) t1 (subst_tt id0 s0 s2) (subst_tt id0 s0 s3)
end
with subst_tlt (id0:id) (s0:sterm) (ls:list_sterm) : list_sterm :=
match ls with
| Nil_list_sterm => Nil_list_sterm
| Cons_list_sterm s ls' => Cons_list_sterm (subst_tt id0 s0 s) (subst_tlt id0 s0 ls')
end
with subst_tltl (id0:id) (s0:sterm) (ls:list_sterm_l) : list_sterm_l :=
match ls with
| Nil_list_sterm_l => Nil_list_sterm_l
| Cons_list_sterm_l s l0 ls' => Cons_list_sterm_l (subst_tt id0 s0 s) l0 (subst_tltl id0 s0 ls')
end
with subst_tm (id0:id) (s0:sterm) (m:smem) : smem :=
match m with 
| smem_init => smem_init
| smem_malloc m1 t1 sz align => smem_malloc (subst_tm id0 s0 m1) t1 sz align
| smem_free m1 t1 s1 => smem_free (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1)
| smem_alloca m1 t1 sz align => smem_alloca (subst_tm id0 s0 m1) t1 sz align
| smem_load m1 t1 s1 align => smem_load (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) align 
| smem_store m1 t1 s1 s2 align => smem_store (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2) align
end
.

Fixpoint subst_mt (sm:smap) (s:sterm) : sterm :=
match sm with
| nil => s
| (id0, s0)::sm' => subst_mt sm' (subst_tt id0 s0 s)
end.

Fixpoint subst_mm (sm:smap) (m:smem) : smem :=
match sm with
| nil => m
| (id0, s0)::sm' => subst_mm sm' (subst_tm id0 s0 m)
end.

End SimpleSE.
