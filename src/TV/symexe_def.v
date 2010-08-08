Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
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

Export LLVMsyntax.
Export LLVMlib.

(***************************************************************)
(* Syntax easy to be proved with symbolic execution. *)

Module SimpleSE.

(***************************************************************)
(* deterministic big-step for this new syntax with subblocks. *)

Record ExecutionContext : Set := mkEC {
CurBB       : block;
Locals      : GVMap;                 (* LLVM values used in this invocation *)
Allocas     : list mblock            (* Track memory allocated by alloca *)
}.

Record State : Set := mkState {
Frame          : ExecutionContext;
Globals        : GVMap;
Mem            : mem
}.

Inductive dbCmd : layouts -> 
                  GVMap -> list mblock -> GVMap -> mem -> 
                  cmd -> 
                  GVMap -> list mblock -> GVMap -> mem -> 
                  trace -> Prop :=
| dbBop: forall TD lc gl lc' gl' id bop sz v1 v2 gv3 Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gv3 ->
  updateEnv lc gl id gv3 = (lc', gl') -> 
  dbCmd TD
    lc als gl Mem
    (insn_bop id bop sz v1 v2)
    lc' als gl' Mem
    trace_nil 
| dbExtractValue : forall TD lc gl lc' gl' id t v gv gv' Mem als idxs,
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  updateEnv lc gl id gv' = (lc', gl') -> 
  dbCmd TD 
    lc als gl Mem
    (insn_extractvalue id t v idxs)
    lc' als gl' Mem
    trace_nil 
| dbInsertValue : forall TD lc gl lc' gl' id t v t' v' gv gv' gv'' idxs Mem als,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  updateEnv lc gl id gv'' = (lc', gl') -> 
  dbCmd TD 
    lc als gl Mem
    (insn_insertvalue id t v t' v' idxs)
    lc' als gl' Mem
    trace_nil 
| dbMalloc : forall TD lc gl lc' gl' id t sz align Mem als Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  malloc TD Mem (tsz * sz) align = Some (Mem', mb) ->
  updateEnv lc gl id (ptr2GV TD (mb, 0)) = (lc', gl') -> 
  dbCmd TD 
    lc als gl Mem
    (insn_malloc id t sz align)
    lc' als gl' Mem'
    trace_nil
| dbFree : forall TD lc gl fid t v Mem als Mem' mptr,
  getOperandPtr TD v lc gl = Some mptr ->
  free Mem mptr = Some Mem'->
  dbCmd TD 
    lc als gl Mem
    (insn_free fid t v)
    lc als gl Mem'
    trace_nil
| dbAlloca : forall TD lc gl lc' gl' id t sz align Mem als Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  malloc TD Mem (tsz * sz) align = Some (Mem', mb) ->
  updateEnv lc gl id (ptr2GV TD (mb, 0)) = (lc', gl') -> 
  dbCmd TD 
    lc als gl Mem
    (insn_alloca id t sz align)
    lc' (mb::als) gl' Mem'
    trace_nil
| dbLoad : forall TD lc gl lc' gl' id t v Mem als mp gv,
  getOperandPtr TD v lc gl = Some mp ->
  mload TD Mem mp t = Some gv ->
  updateEnv lc gl id gv = (lc', gl') -> 
  dbCmd TD 
    lc als gl Mem
    (insn_load id t v)
    lc' als gl' Mem
    trace_nil
| dbStore : forall TD lc gl sid t v1 v2 Mem als mp2 gv1 Mem',
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandPtr TD v2 lc gl = Some mp2 ->
  mstore TD Mem mp2 t gv1 = Some Mem' ->
  dbCmd TD 
    lc als gl Mem
    (insn_store sid t v1 v2)
    lc als gl Mem'
    trace_nil
| dbGEP : forall TD lc gl lc' gl' id inbounds t v idxs mp mp' Mem als,
  getOperandPtr TD v lc gl = Some mp ->
  GEP TD lc gl t mp idxs inbounds = Some mp' ->
  updateEnv lc gl id (ptr2GV TD mp') = (lc', gl') -> 
  dbCmd TD 
    lc als gl Mem
    (insn_gep id inbounds t v idxs)
    lc' als gl' Mem
    trace_nil 
| dbExt : forall TD lc gl id extop t1 v1 t2 gv2 lc' gl' Mem als,
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  updateEnv lc gl id gv2 = (lc', gl') -> 
  dbCmd TD 
    lc als gl Mem
    (insn_ext id extop t1 v1 t2)
    lc' als gl' Mem
    trace_nil
| dbCast : forall TD lc gl id castop t1 v1 t2 gv2 lc' gl' Mem als,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  updateEnv lc gl id gv2 = (lc', gl') -> 
  dbCmd TD 
    lc als gl Mem
    (insn_cast id castop t1 v1 t2)
    lc' als gl' Mem
    trace_nil
| dbIcmp : forall TD lc gl id cond t v1 v2 gv3 lc' gl' Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  updateEnv lc gl id gv3 = (lc', gl') -> 
  dbCmd TD 
    lc als gl Mem
    (insn_icmp id cond t v1 v2)
    lc' als gl' Mem
    trace_nil
| dbSelect : forall TD lc gl id v0 t v1 v2 cond lc' gl' Mem als gv1 gv2,
  getOperandInt TD 1 v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  (lc', gl') = (if cond
               then updateEnv lc gl id gv1
               else updateEnv lc gl id gv2) ->
  dbCmd TD 
    lc als gl Mem
    (insn_select id v0 t v1 v2)
    lc' als gl' Mem
    trace_nil
.

Inductive dbTerminator : 
  layouts -> fdef ->
  block -> GVMap -> GVMap -> 
  terminator -> 
  block -> GVMap -> 
  trace -> Prop :=
| dbBranch : forall TD F B lc gl bid Cond l1 l2 c
                              l' ps' sbs' tmn' lc',   
  getOperandInt TD 1 Cond lc gl = Some c ->
  Some (block_intro l' ps' sbs' tmn') = (if c 
               then lookupBlockViaLabelFromFdef F l1
               else lookupBlockViaLabelFromFdef F l2) ->
  lc' = LLVMopsem.switchToNewBasicBlock (block_intro l' ps' sbs' tmn') B lc ->
  dbTerminator TD F
    B lc gl
    (insn_br bid Cond l1 l2)
    (block_intro l' ps' sbs' tmn') lc' 
    trace_nil 
| dbBranch_uncond : forall TD F B lc gl l bid
                              l' ps' sbs' tmn' lc',   
  Some (block_intro l' ps' sbs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  lc' = LLVMopsem.switchToNewBasicBlock (block_intro l' ps' sbs' tmn') B lc ->
  dbTerminator TD F
    B lc gl
    (insn_br_uncond bid l) 
    (block_intro l' ps' sbs' tmn') lc'
    trace_nil 
.

Inductive dbCmds : layouts -> 
                   GVMap -> list mblock -> GVMap -> mem -> 
                   cmds -> 
                   GVMap -> list mblock -> GVMap -> mem -> 
                   trace -> Prop :=
| dbCmds_nil : forall TD lc als gl Mem, dbCmds TD lc als gl Mem nil lc als gl Mem trace_nil
| dbCmds_cons : forall TD c cs lc1 als1 gl1 Mem1 t1 t2 lc2 als2 gl2 Mem2
                       lc3 als3 gl3 Mem3,
    dbCmd TD lc1 als1 gl1 Mem1 c lc2 als2 gl2 Mem2 t1 ->
    dbCmds TD lc2 als2 gl2 Mem2 cs lc3 als3 gl3 Mem3 t2 ->
    dbCmds TD lc1 als1 gl1 Mem1 (c::cs) lc3 als3 gl3 Mem3 (trace_app t1 t2).

Inductive dbCall : system -> layouts -> list product ->
                   GVMap -> GVMap -> mem -> 
                   cmd -> 
                   GVMap -> GVMap -> mem -> 
                   trace -> Prop :=
| dbCall_intro : forall S TD Ps lc gl rid noret tailc rt fid lp gl' gl''
                       Rid oResult tr lc'' lc' Mem Mem' als' Mem'' B',
  dbFdef fid rt lp S TD Ps lc gl Mem lc' gl' als' Mem' B' Rid oResult tr ->
  (lc'', gl'') = 
    match noret with
    | false =>
      if (LLVMlib.typEqB rt typ_void) 
      then (lc, gl') 
      else 
        match oResult with
        | None => (lc, gl')
        | Some Result => 
          match (getOperandValue TD Result lc' gl') with
          | Some gr => updateEnv lc gl' rid gr
          | None => (lc, gl')
          end
        end
    | true => (lc, gl')
    end ->
  free_allocas Mem' als' = Some Mem'' ->
  dbCall S TD Ps
    lc gl Mem
    (insn_call rid noret tailc rt fid lp)
    lc'' gl'' Mem'' 
    tr
with dbSubblock : system -> layouts -> list product ->
                  GVMap -> list mblock -> GVMap -> mem -> 
                  cmds -> 
                  GVMap -> list mblock -> GVMap -> mem -> 
                  trace -> Prop :=
| dbSubblock_intro : forall S TD Ps lc1 als1 gl1 Mem1 cs call0 lc2 als2 gl2 Mem2 tr1 
                     lc3 gl3 Mem3 tr2,
  dbCmds TD lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr1 ->
  dbCall S TD Ps lc2 gl2 Mem2 call0 lc3 gl3 Mem3 tr2 ->
  dbSubblock S TD Ps
             lc1 als1 gl1 Mem1
             (cs++call0::nil) 
             lc3 als2 gl3 Mem3
             (trace_app tr1 tr2)
with dbSubblocks : system -> layouts -> list product ->
                   GVMap -> list mblock -> GVMap -> mem -> 
                   cmds -> 
                   GVMap -> list mblock -> GVMap -> mem -> 
                   trace -> Prop :=
| dbSubblocks_nil : forall S TD Ps lc als gl Mem, 
    dbSubblocks S TD Ps lc als gl Mem nil lc als gl Mem trace_nil
| dbSubblocks_cons : forall S TD Ps lc1 als1 gl1 Mem1 lc2 als2 gl2 Mem2 lc3 als3 gl3 Mem3 cs cs' t1 t2,
    dbSubblock S TD Ps lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 t1 ->
    dbSubblocks S TD Ps lc2 als2 gl2 Mem2 cs' lc3 als3 gl3 Mem3 t2 ->
    dbSubblocks S TD Ps lc1 als1 gl1 Mem1 (cs++cs') lc3 als3 gl3 Mem3 (trace_app t1 t2)
with dbBlock : system -> layouts -> list product -> fdef -> list GenericValue -> State -> State -> trace -> Prop :=
| dbBlock_intro : forall S TD Ps F tr1 tr2 l ps cs cs' tmn lc1 als1 gl1 Mem1
                         lc2 als2 gl2 Mem2 lc3 als3 gl3 Mem3 lc4 B' arg tr3,
  dbSubblocks S TD Ps
    lc1 als1 gl1 Mem1
    cs
    lc2 als2 gl2 Mem2
    tr1 ->
  dbCmds TD lc2 als2 gl2 Mem2 cs' lc3 als3 gl3 Mem3 tr2 ->
  dbTerminator TD F
    (block_intro l ps (cs++cs') tmn) lc3 gl3
    tmn
    B' lc4
    tr3 ->
  dbBlock S TD Ps F arg
    (mkState (mkEC (block_intro l ps (cs++cs') tmn) lc1 als1) gl1 Mem1)
    (mkState (mkEC B' lc4 als3) gl3 Mem3)
    (trace_app (trace_app tr1 tr2) tr3)
with dbBlocks : system -> layouts -> list product -> fdef -> list GenericValue -> State -> State -> trace -> Prop :=
| dbBlocks_nil : forall S TD Ps F arg state, dbBlocks S TD Ps F arg state state trace_nil
| dbBlocks_cons : forall S TD Ps F arg S1 S2 S3 t1 t2,
    dbBlock S TD Ps F arg S1 S2 t1 ->
    dbBlocks S TD Ps F arg S2 S3 t2 ->
    dbBlocks S TD Ps F arg S1 S3 (trace_app t1 t2)
with dbFdef : id -> typ -> params -> system -> layouts -> list product -> GVMap -> GVMap -> mem -> GVMap -> GVMap -> list mblock -> mem -> block -> id -> option value -> trace -> Prop :=
| dbFdef_func : forall S TD Ps gl fid lp lc rid
                       l1 ps1 cs1 tmn1 rt la lb Result lc1 gl1 tr1 Mem Mem1 als1
                       l2 ps2 cs21 cs22 lc2 als2 gl2 Mem2 tr2 lc3 als3 gl3 Mem3 tr3,
  lookupFdefViaIDFromProducts Ps fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some (block_intro l1 ps1 cs1 tmn1) ->
  dbBlocks S TD Ps (fdef_intro (fheader_intro rt fid la) lb) (params2GVs TD lp lc gl)
    (mkState (mkEC (block_intro l1 ps1 cs1 tmn1) (initLocals la (params2GVs TD lp lc gl)) nil) gl Mem)
    (mkState (mkEC (block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result)) lc1 als1) gl1 Mem1)
    tr1 ->
  dbSubblocks S TD Ps
    lc1 als1 gl1 Mem1
    cs21
    lc2 als2 gl2 Mem2
    tr2 ->
  dbCmds TD
    lc2 als2 gl2 Mem2
    cs22
    lc3 als3 gl3 Mem3
    tr3 ->
  dbFdef fid rt lp S TD Ps lc gl Mem lc3 gl3 als3 Mem3 (block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result)) rid (Some Result) (trace_app (trace_app tr1 tr2) tr3)
| dbFdef_proc : forall S TD Ps gl fid lp lc rid
                       l1 ps1 cs1 tmn1 rt la lb lc1 gl1 tr1 Mem Mem1 als1
                       l2 ps2 cs21 cs22 lc2 als2 gl2 Mem2 tr2 lc3 als3 gl3 Mem3 tr3,
  lookupFdefViaIDFromProducts Ps fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some (block_intro l1 ps1 cs1 tmn1) ->
  dbBlocks S TD Ps (fdef_intro (fheader_intro rt fid la) lb) (params2GVs TD lp lc gl) 
    (mkState (mkEC (block_intro l1 ps1 cs1 tmn1) (initLocals la (params2GVs TD lp lc gl)) nil) gl Mem)
    (mkState (mkEC (block_intro l2 ps2 (cs21++cs22) (insn_return_void rid)) lc1 als1) gl1 Mem1)
    tr1 ->
  dbSubblocks S TD Ps
    lc1 als1 gl1 Mem1
    cs21
    lc2 als2 gl2 Mem2
    tr2 ->
  dbCmds TD
    lc2 als2 gl2 Mem2
    cs22
    lc3 als3 gl3 Mem3
    tr3 ->
  dbFdef fid  rt lp S TD Ps lc gl Mem lc3 gl3 als3 Mem3 (block_intro l2 ps2 (cs21++cs22) (insn_return_void rid)) rid None (trace_app (trace_app tr1 tr2) tr3)
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
  [ c "dbCall_intro" | 
    c "dbSubblock_intro" | c "dbSubblocks_nil" | c "dbSubblocks_cons" | 
    c "dbBlock_intro" | c "dbBlocks_nil" | c "dbBlocks_cons" | 
    c "dbFdef_func" | c "dbFdef_proc" ].

Tactic Notation "dbCmd_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBop" | c "dbExtractValue" | c "dbInsertValue" |
    c "dbMalloc" | c "dbFree" |
    c "dbAlloca" | c "dbLoad" | c "dbStore" | c "dbGEP" |
    c "dbExt" | c "dbCast" | c "dbIcmp" |  c "dbSelect" ].

Tactic Notation "dbTerminator_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBranch" | c "dbBranch_uncond" ].

Tactic Notation "dbCmds_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCmds_nil" | c "dbCmds_cons" ].

Hint Constructors dbCmd dbCmds dbTerminator dbCall 
                  dbSubblock dbSubblocks dbBlock dbBlocks dbFdef.

(* properties of opsem *)
Lemma dbCmd_eqEnv : forall TD c lc1  als1 gl1 Mem1 lc2 als2 gl2 Mem2 tr lc2' gl2',
  dbCmd TD lc1 als1 gl1 Mem1 c lc2 als2 gl2 Mem2 tr ->
  eqEnv lc2 gl2 lc2' gl2' ->
  dbCmd TD lc1 als1 gl1 Mem1 c lc2' als2 gl2' Mem2 tr.
Proof.
  intros TD c lc1  als1 gl1 Mem1 lc2 als2 gl2 Mem2 tr lc2' gl2' HdbCmd EqEnv.
  (dbCmd_cases (inversion HdbCmd) Case); subst.
    eapply dbBop; eauto.

Lemma updateEnv_eqEnv : forall lc gl lc1 gl1 lc2 gl2 id0 gv0,
  updateEnv lc gl id0 gv0 = (lc1, gl1) ->
  eqEnv lc1 gl1 lc2 gl2 ->
  updateEnv lc gl id0 gv0 = (lc2, gl2).
Proof.
Admitted.

Admitted.

Lemma dbCmds_eqEnv : forall TD cs lc1 als1 gl1 Mem1 lc2 als2 gl2 Mem2 tr lc2' gl2',
  dbCmds TD lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr ->
  eqEnv lc2 gl2 lc2' gl2' ->
  dbCmds TD lc1 als1 gl1 Mem1 cs lc2' als2 gl2' Mem2 tr.
Admitted.

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

Lemma dbCmd_isNotCallInst : forall TD lc als gl Mem1 c lc' als' gl' Mem2 tr,
  dbCmd TD lc als gl Mem1 c lc' als' gl' Mem2 tr ->
  Instruction.isCallInst c = false.
Proof.
  intros TD lc als gl Mem1 c lc' als' gl' Mem2 tr HdbCmd.
  induction HdbCmd; auto.
Qed.

Definition dbCmd2nbranch : forall TD lc als gl Mem1 c lc' als' gl' Mem2 tr, 
  dbCmd TD lc als gl Mem1 c lc' als' gl' Mem2 tr ->
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

Definition dbCmds2nbranchs : forall cs TD lc als gl Mem1 lc' als' gl' Mem2 tr, 
  dbCmds TD lc als gl Mem1 cs lc' als' gl' Mem2 tr ->
  exists nbs, cmds2nbranchs cs = Some nbs.
Proof.
  induction cs; intros.
    exists nil. simpl. auto.

    inversion H; subst.
    apply dbCmd2nbranch in H7.
    apply IHcs in H13.
    destruct H7 as [nb J1].
    destruct H13 as [nbs J2].
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

Definition dbCmds__cmds2nbs : forall TD lc als gl Mem1 cs lc' als' gl' Mem2 tr, 
  dbCmds TD lc als gl Mem1 cs lc' als' gl' Mem2 tr ->
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

Lemma dbCall_isCallInst : forall S TD Ps lc gl Mem1 c lc' gl' Mem2 tr,
  dbCall S TD Ps lc gl Mem1 c lc' gl' Mem2 tr ->
  Instruction.isCallInst c = true.
Proof.
  intros S TD Ps lc gl Mem1 c lc' gl' Mem2 tr HdbCall.
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

Lemma dbSubblock__cmds2sb : forall S TD Ps lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr,
  dbSubblock S TD Ps lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr ->
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

Lemma dbSubblocks__cmds2sbs : forall S TD Ps lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr,
  dbSubblocks S TD Ps lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr ->
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
| sterm_extractvalue : typ -> sterm -> list_const -> sterm
| sterm_insertvalue : typ -> sterm -> typ -> sterm -> list_const -> sterm
| sterm_malloc : smem -> typ -> sz -> align -> sterm
| sterm_alloca : smem -> typ -> sz -> align -> sterm
| sterm_load : smem -> typ -> sterm -> sterm
| sterm_gep : inbounds -> typ -> sterm -> list sterm -> sterm
| sterm_ext : extop -> typ -> sterm -> typ -> sterm
| sterm_cast : castop -> typ -> sterm -> typ -> sterm
| sterm_icmp : cond -> typ -> sterm -> sterm -> sterm
| sterm_phi : typ -> list (sterm*l) -> sterm
| sterm_select : sterm -> typ -> sterm -> sterm -> sterm
with smem : Set :=
| smem_init : smem
| smem_malloc : smem -> typ -> sz -> align -> smem
| smem_free : smem -> typ -> sterm -> smem
| smem_alloca : smem -> typ -> sz -> align -> smem
| smem_load : smem -> typ -> sterm -> smem
| smem_store : smem -> typ -> sterm -> sterm -> smem
with sframe : Set :=
| sframe_init : sframe
| sframe_alloca : smem -> sframe -> typ -> sz -> align -> sframe
.

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

Fixpoint lookupSmap (sm:smap) (i0:id) : sterm :=
match sm with
| nil => (sterm_val (value_id i0))
| (id0, s0)::sm' => 
  if id0 == i0 then s0 else lookupSmap sm' i0
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
  | insn_load id0 t2 v2 => fun _ =>   
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_load st.(SMem) t2 
                     (value2Sterm st.(STerms) v2)))
                 (smem_load st.(SMem)t2 
                   (value2Sterm st.(STerms) v2))
                 st.(SFrame)
                 st.(SEffects))
  | insn_store id0 t0 v1 v2 => fun _ =>  
       (mkSstate st.(STerms)
                 (smem_store st.(SMem) t0 
                   (value2Sterm st.(STerms) v1)
                   (value2Sterm st.(STerms) v2))
                 st.(SFrame)
                 st.(SEffects))
  | insn_gep id0 inbounds0 t1 v1 lv2 => fun _ =>  
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_gep inbounds0 t1 
                     (value2Sterm st.(STerms) v1)
                     (map_list_value (value2Sterm st.(STerms)) lv2)))
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
  end) (refl_equal i)
end.

Fixpoint _se_phinodes (st st0: sstate) (ps:list phinode) : sstate :=
match ps with
| nil => st
| insn_phi id0 t0 idls0::ps' =>  
    _se_phinodes 
     (mkSstate (updateAL _ st.(STerms) id0 
                 (sterm_phi 
                   t0 
                   (map_list_id_l
                     (fun id5 l5 =>
                      ((value2Sterm st.(STerms) (value_id id5)), l5)
                     )
                     idls0
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

(* Properties *)

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
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a id0); subst; simpl;
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
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a id0); subst; simpl;
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
  malloc TD Mem1 (tsz0 * sz0) align0 = Some (Mem2, mb) ->
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_malloc sm0 t0 sz0 align0) (ptr2GV TD (mb, 0))
| sterm_alloca_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 sz0 align0 tsz0 Mem2 mb,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  getTypeAllocSize TD t0 = Some tsz0 ->
  malloc TD Mem1 (tsz0 * sz0) align0 = Some (Mem2, mb) ->
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_alloca sm0 t0 sz0 align0) (ptr2GV TD (mb, 0))
| sterm_load_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 st0 gv0 mp0 gv1,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 ->
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  GV2ptr TD (getPointerSize TD) gv0 = Some mp0 ->
  mload TD Mem1 mp0 t0 = Some gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_load sm0 t0 st0) gv1
| sterm_gep_denotes : forall TD lc gl Mem ib0 t0 st0 sts0 gv0 gvs0 ns0 mp0 mp1,
  sterm_denotes_genericvalue TD lc gl Mem st0 gv0 ->
  sterms_denote_genericvalues TD lc gl Mem sts0 gvs0 ->
  GV2ptr TD (getPointerSize TD) gv0 = Some mp0 ->
  GVs2Nats TD gvs0 = Some ns0 ->
  mgep TD t0 mp0 ns0 = Some mp1 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_gep ib0 t0 st0 sts0) (ptr2GV TD mp1)
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
| sterm_select_denotes : forall TD lc gl Mem st0 t0 st1 st2 gv0 gv1 gv2 c0 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st0 gv0 ->
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  GV2nat TD 1 gv0 = Some c0 ->
  (if c0 then gv1 else gv2) = gv3 -> 
  sterm_denotes_genericvalue TD lc gl Mem (sterm_select st0 t0 st1 st2) gv3
with sterms_denote_genericvalues : 
   layouts ->               (* CurTatgetData *)
   GVMap ->                 (* local registers *)
   GVMap ->                 (* global variables *)
   mem ->                   (* Memory *)
   list sterm ->            (* symbolic terms *)
   list GenericValue ->     (* values that denote sterms *)
   Prop :=
| sterms_nil_denote : forall TD lc gl Mem,
  sterms_denote_genericvalues TD lc gl Mem nil nil
| sterms_cons_denote : forall TD lc gl Mem sts st gvs gv,
  sterms_denote_genericvalues TD lc gl Mem sts gvs ->
  sterm_denotes_genericvalue TD lc gl Mem st gv ->
  sterms_denote_genericvalues TD lc gl Mem (st::sts) (gv::gvs)
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
  malloc TD Mem1 (tsz0 * sz0) align0 = Some (Mem2, mb) ->
  smem_denotes_mem TD lc gl Mem0 (smem_malloc sm0 t0 sz0 align0) Mem2
| smem_free_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 st0 gv0 mptr0 Mem2,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 ->
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  GV2ptr TD (getPointerSize TD) gv0 = Some mptr0 ->
  free Mem1 mptr0 = Some Mem2->
  smem_denotes_mem TD lc gl Mem0 (smem_free sm0 t0 st0) Mem2
| smem_alloca_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 sz0 align0 tsz0 Mem2 mb,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  getTypeAllocSize TD t0 = Some tsz0 ->
  malloc TD Mem1 (tsz0 * sz0) align0 = Some (Mem2, mb) ->
  smem_denotes_mem TD lc gl Mem0 (smem_alloca sm0 t0 sz0 align0) Mem2
| smem_load_denotes : forall TD lc gl Mem0 sm0 t0 st0 Mem1,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  smem_denotes_mem TD lc gl Mem0 (smem_load sm0 t0 st0) Mem1
| smem_store_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 st1 st2 gv1 gv2 mptr2 Mem2,
  sterm_denotes_genericvalue TD lc gl Mem0 st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st2 gv2 ->
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  GV2ptr TD (getPointerSize TD) gv2 = Some mptr2 ->
  mstore TD Mem1 mptr2 t0 gv1 = Some Mem2 ->
  smem_denotes_mem TD lc gl Mem0 (smem_store sm0 t0 st1 st2) Mem2
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
  malloc TD Mem1 (tsz0 * sz0) align0 = Some (Mem2, mb) ->
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
| c "sterm_extractvalue_denotes"
| c "sterm_insertvalue_denotes"
| c "sterm_malloc_denotes"
| c "sterm_alloca_denotes"
| c "sterm_load_denotes"
| c "sterm_gep_denotes"
| c "sterm_ext_denotes"
| c "sterm_cast_denotes"
| c "sterm_icmp_denotes" 
| c "sterm_select_denotes"
| c "sterms_nil_denote"
| c "sterms_cons_denote"
| c "smem_init_denotes"
| c "smem_malloc_denotes"
| c "smem_free_denotes"
| c "smem_alloca_denotes"
| c "smem_load_denotes"
| c "smem_store_denotes" ].

Definition smap_denotes_gvmap TD lc gl Mem smap' lc' gl' :=
(forall id' st',  
  binds id' st' smap' ->
  exists gv',
    sterm_denotes_genericvalue TD lc gl Mem st' gv' /\
    lookupEnv lc' gl' id' = Some gv') /\
(forall id' gv',  
  lookupEnv lc' gl' id' = Some gv' ->
  exists st',
    binds id' st' smap' /\
    sterm_denotes_genericvalue TD lc gl Mem st' gv'
).

Definition sstate_denotes_state TD lc gl als Mem sstate' lc' gl' als' mem' tr :=
smap_denotes_gvmap TD lc gl Mem sstate'.(STerms) lc' gl' /\
smem_denotes_mem TD lc gl Mem sstate'.(SMem) mem' /\
sframe_denotes_frame TD lc gl als Mem sstate'.(SFrame) als' /\
seffects_denote_trace sstate'.(SEffects) tr.

(* Initial smap of a symbolic exe w.r.t a concrete a state. *)

Fixpoint globals_to_smap (gl:GVMap) : smap :=
match gl with
| nil => nil
| (id0, _)::gl' => updateAddAL _ (globals_to_smap gl') id0 (sterm_val (value_id id0)) 
end.

Fixpoint locals_to_smap (lc:GVMap) (m0:smap) : smap :=
match lc with
| nil => m0
| (id0, _)::lc' => updateAddAL _ (locals_to_smap lc' m0) id0 (sterm_val (value_id id0)) 
end.

Definition env_to_smap (gl lc:GVMap) : smap :=
locals_to_smap lc (globals_to_smap gl).

Lemma globals_to_smap_dom_eq : forall gl,
  dom (globals_to_smap gl) [=] dom gl.
Proof.
  induction gl; simpl.
    fsetdec.

    destruct a.
    rewrite <- IHgl. clear IHgl.
    rewrite updateAddAL_dom_eq. fsetdec.
Qed.

Lemma locals_to_smap_dom_eq : forall lc m0,
  dom (locals_to_smap lc m0) [=] dom lc `union` dom m0.
Proof.
  induction lc; intros m0; simpl.
    fsetdec.

    destruct a.
    rewrite updateAddAL_dom_eq. 
    rewrite IHlc.
    fsetdec.
Qed.

Lemma env_to_smap_dom_eq : forall gl lc,
  dom (env_to_smap gl lc) [=] dom gl `union` dom lc.
Proof.
  intros gl lc.
  unfold env_to_smap.
  rewrite locals_to_smap_dom_eq.
  rewrite globals_to_smap_dom_eq.
  fsetdec.
Qed.

Lemma globals_to_smap_uniq : forall gl,
  uniq (globals_to_smap gl).
Proof.
  induction gl; simpl; auto.
    destruct a.
    apply updateAddAL_uniq; auto.
Qed.

Lemma locals_to_smap_uniq : forall lc m0,
  uniq m0 ->
  uniq (locals_to_smap lc m0).
Proof.
  induction lc; simpl; intros; auto.
    destruct a.
    apply updateAddAL_uniq; auto.
Qed.

Lemma env_to_smap_uniq : forall gl lc,
  uniq (env_to_smap gl lc).
Proof.
  intros gl lc.
  unfold env_to_smap.
  apply locals_to_smap_uniq.
  apply globals_to_smap_uniq.
Qed.

Lemma binds_globals_to_smap : forall gl id0 st0,
  uniq gl ->
  binds id0 st0 (globals_to_smap gl) ->
  st0 = sterm_val (value_id id0) /\ 
  exists gv, lookupAL _ gl id0 = Some gv.
Proof.
  induction gl; intros; simpl in *.
    inversion H0.

    inversion H; subst.
    apply updateAddAL_inversion in H0; auto using globals_to_smap_uniq.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 x); subst; simpl; auto.
      destruct H0 as [[J1 J2] | [J1 J2]].
        contradict J1; auto.
        split; auto. exists a0. auto.
     
      destruct H0 as [[J1 J2] | [J1 J2]].
        apply IHgl in J2; auto.

        contradict n; auto.
Qed.

Lemma binds_locals_to_smap : forall id0 st0 lc m0,
  uniq m0 ->
  uniq lc ->
  binds id0 st0 (locals_to_smap lc m0) ->
  (st0 = sterm_val (value_id id0) /\ exists gv, lookupAL _ lc id0 = Some gv) \/
  binds id0 st0 m0.  
Proof.
  induction lc; intros; simpl in *; auto.
    inversion H0; subst.
    apply updateAddAL_inversion in H1; auto using locals_to_smap_uniq.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 x); subst; simpl; auto.
      destruct H1 as [[J1 J2] | [J1 J2]].
        contradict J1; auto.
        left. split; auto. exists a0. auto.
     
      destruct H1 as [[J1 J2] | [J1 J2]].
        apply IHlc in J2; auto.

        contradict n; auto.
Qed.

Lemma binds_env_to_smap : forall TD id0 st0 gl lc,
  uniq gl ->
  uniq lc -> 
  binds id0 st0 (env_to_smap gl lc) ->
  st0 = sterm_val (value_id id0) /\ 
  exists gv, getOperandValue TD (value_id id0) lc gl = Some gv.
Proof.
  intros.
  apply binds_locals_to_smap in H1; auto using globals_to_smap_uniq.
  destruct H1 as [[J1 [gv J2]] | H1]; subst.
    split; auto. simpl. unfold lookupEnv. rewrite J2. exists gv. auto.
    apply binds_globals_to_smap in H1; auto using globals_to_smap_uniq.
    destruct H1 as [J1 [gv J2]]; auto.
      split; auto. simpl. unfold lookupEnv. rewrite J2. 
      destruct (lookupAL _ lc id0).
        exists g. auto.
        exists gv. auto.
Qed.

Lemma env_to_smap_denotes__imples__gv : forall id0 st0 TD Mem0 gl lc,
  uniq gl ->
  uniq lc -> 
  binds id0 st0 (env_to_smap gl lc) ->
  exists gv0,
    sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 /\
    lookupEnv lc gl id0 = Some gv0.
Proof.
  intros id0 st0 TD Mem0 gl lc Uniqg Uniqc Binds.
  apply binds_env_to_smap with (TD:=TD) in Binds; auto.
  destruct Binds as [J1 [gv0 J2]]; subst.
  exists gv0. split; auto.
Qed.

Lemma lookupEnv_globals_to_smap : forall gl id0 gv0,
  lookupAL _ gl id0 = Some gv0 ->
  binds id0 (sterm_val (value_id id0)) (globals_to_smap gl).
Proof.
  induction gl; intros; simpl in *.
    inversion H.
    destruct a.
    destruct (id0==a); subst.
      inversion H; subst. 
      apply binds_updateAddAL_eq; auto.

      apply binds_updateAddAL_neq; eauto.
Qed.

Lemma lookupEnv_locals_to_smap : forall lc m1 id0 gv0,
  lookupAL _ lc id0 = Some gv0 ->
  binds id0 (sterm_val (value_id id0)) (locals_to_smap lc m1).
Proof.
  induction lc; intros; simpl in *.
    inversion H.
    destruct a.
    destruct (id0==a); subst.
      inversion H; subst. 
      apply binds_updateAddAL_eq; auto.

      apply binds_updateAddAL_neq; eauto.
Qed.

Lemma lookupEnv_locals_to_smap' : forall lc m1 st0 id0,
  lookupAL _ lc id0 = None ->
  binds id0 st0 m1 ->
  binds id0 st0 (locals_to_smap lc m1).
Proof.
  induction lc; intros; simpl in *; auto.
    destruct a.
    destruct (id0==a); subst.
      inversion H.    
      apply binds_updateAddAL_neq; eauto.
Qed.

Lemma lookupEnv_env_to_smap : forall id0 gv0 gl lc,
  lookupEnv lc gl id0 = Some gv0 ->
  binds id0 (sterm_val (value_id id0)) (env_to_smap gl lc).
Proof.
  intros.
  unfold lookupEnv in H.
  unfold env_to_smap.
  remember (lookupAL _ lc id0) as ogv.
  destruct ogv.
    inversion H; subst.
    eapply lookupEnv_locals_to_smap; eauto.

    apply lookupEnv_locals_to_smap'; auto.
    apply lookupEnv_globals_to_smap in H; auto.
Qed.

Lemma gv__imples__env_to_smap_denotes : forall id0 TD Mem0 gl lc gv0,
  lookupEnv lc gl id0 = Some gv0 ->
  binds id0 (sterm_val (value_id id0)) (env_to_smap gl lc) /\
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_val (value_id id0)) gv0.
Proof.
  intros id0 TD Mem0 gl lc gv0 Binds.
  split.
    eapply lookupEnv_env_to_smap; eauto.

    apply sterm_val_denotes; auto.
Qed.

Lemma env_to_smap_denotes_gvmap :forall TD lc gl Mem0,
  uniq gl ->
  uniq lc ->
  smap_denotes_gvmap TD lc gl Mem0 (env_to_smap gl lc) lc gl.
Proof.
  intros TD lc gl Mem0 Uniqg Uniqc.
  unfold smap_denotes_gvmap.
  split; intros.
    apply env_to_smap_denotes__imples__gv; auto.

    exists (sterm_val (value_id id')).
    apply gv__imples__env_to_smap_denotes; auto.
Qed.

Lemma env_to_smap_denotes_id :forall TD lc gl als Mem0,
  uniq gl ->
  uniq lc ->
  sstate_denotes_state TD lc gl als Mem0 (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) lc gl als Mem0 trace_nil.
Proof.
  intros TD lc gl als Mem0 Uniqg Uniqc.
  split; simpl; auto using env_to_smap_denotes_gvmap.
Qed.

Lemma se_cmds_env_to_smap_dom_sub: forall lc0 gl0 cs,
  union (dom lc0) (dom gl0) [<=]
    dom (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)).
Proof.
  intros.
  assert (J:=@se_cmds_dom_mono cs (env_to_smap gl0 lc0) smem_init sframe_init nil).
  rewrite env_to_smap_dom_eq in J. fsetdec.
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
  apply H0 in H10; subst.
  apply H in H5; subst.
  rewrite e in H12. inversion H12; subst.
  rewrite H13 in e0. inversion e0; auto.
Case "sterm_gep_denotes".
  inversion H1; subst.
  apply H in H6; subst.
  apply H0 in H11; subst.
  rewrite H13 in e. inversion e; subst.
  rewrite H14 in e0. inversion e0; subst.
  rewrite H15 in e1. inversion e1; auto.
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
Case "sterm_select_denotes".
  inversion H2; subst.
  apply H in H7; subst.
  apply H0 in H12; subst.
  apply H1 in H14; subst.
  rewrite H15 in e. inversion e; auto.
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
  apply H in H5; subst. 
  apply H0 in H10; subst. 
  rewrite H12 in e. inversion e; subst.
  rewrite H13 in e0. inversion e0; auto.
Case "smem_alloca_denotes".
  inversion H0; subst.
  apply H in H10; subst. 
  rewrite H11 in e. inversion e; subst.
  rewrite H12 in e0. inversion e0; auto.
Case "smem_load_denotes".
  inversion H0; subst.
  apply H in H9; auto. 
Case "smem_store_denotes".
  inversion H2; subst.
  apply H in H7; subst. 
  apply H0 in H12; subst. 
  apply H1 in H14; subst. 
  rewrite H15 in e. inversion e; subst.
  rewrite H16 in e0. inversion e0; auto.
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

Lemma smap_denotes_gvmap_det : forall TD lc gl Mem0 smap0 lc1 gl1 lc2 gl2,
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc1 gl1 ->
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc2 gl2 ->
  eqEnv lc1 gl1 lc2 gl2.
Proof.
  intros TD lc gl Mem0 smap0 lc1 gl1 lc2 gl2 J1 J2.
  destruct J1 as [J11 J12].
  destruct J2 as [J21 J22].
  intros id0.
  remember (lookupEnv lc1 gl1 id0) as ogv1.
  remember (lookupEnv lc2 gl2 id0) as ogv2.
  destruct ogv1 as [gv1 | ].
    symmetry in Heqogv1.
    apply J12 in Heqogv1.
    destruct Heqogv1 as [st0 [binds_id0_st0 st0_denotes_gv1]].
    apply J21 in binds_id0_st0.
    destruct binds_id0_st0 as [gv' [st0_denotes_gv' id0_gv'_in_env2]].
    rewrite id0_gv'_in_env2 in Heqogv2.
    apply sterm_denotes_genericvalue_det with (gv2:=gv1) in st0_denotes_gv'; auto.
    subst. auto.
    
  destruct ogv2 as [gv2 | ]; auto.
    symmetry in Heqogv2.
    apply J22 in Heqogv2.
    destruct Heqogv2 as [st0 [binds_id0_st0 st0_denotes_gv2]].
    apply J11 in binds_id0_st0.
    destruct binds_id0_st0 as [gv' [st0_denotes_gv' id0_gv'_in_env1]].
    rewrite id0_gv'_in_env1 in Heqogv1.
    inversion Heqogv1.
Qed.

Lemma sstate_denotes_state_det : forall TD lc gl als Mem0 sstate0 lc1 gl1 als1 Mem1 tr1 lc2 gl2 als2 Mem2 tr2,
  sstate_denotes_state TD lc gl als Mem0 sstate0 lc1 gl1 als1 Mem1 tr1 ->
  sstate_denotes_state TD lc gl als Mem0 sstate0 lc2 gl2 als2 Mem2 tr2 ->
  eqEnv lc1 gl1 lc2 gl2 /\ als1 = als2 /\ Mem1 = Mem2 /\ tr1 = tr2.
Proof.
  intros TD lc gl als Mem0 sstate0 lc1 gl1 als1 Mem1 tr1 lc2 gl2 als2 Mem2 tr2 J1 J2.
  destruct J1 as [J11 [J12 [J13 J14]]].
  destruct J2 as [J21 [J22 [J23 J24]]].
  apply smem_denotes_mem_det with (Mem2:=Mem2) in J12; auto; subst.
  apply sframe_denotes_frame_det with (als2:=als2) in J13; auto; subst.
  apply seffects_denote_trace_det with (tr2:=tr2) in J14; auto; subst.
  apply smap_denotes_gvmap_det with (lc2:=lc2)(gl2:=gl2) in J11; auto.
Qed.

Lemma smap_denotes_gvmap_eqEnv : forall TD lc gl Mem0 smap0 lc1 gl1 lc2 gl2,
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc1 gl1 ->
  eqEnv lc1 gl1 lc2 gl2 ->
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc2 gl2.
Proof.
  intros TD lc gl Mem0 smap0 lc1 gl1 lc2 gl2 [H1 H2] H3.
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
| sterm_extractvalue t1 s1 cs => 
    sterm_extractvalue t1 (subst_tt id0 s0 s1) cs
| sterm_insertvalue t1 s1 t2 s2 cs => 
    sterm_insertvalue t1 (subst_tt id0 s0 s1) t2 (subst_tt id0 s0 s2) cs
| sterm_malloc m1 t1 sz align => 
    sterm_malloc (subst_tm id0 s0 m1) t1 sz align
| sterm_alloca m1 t1 sz align => 
    sterm_alloca (subst_tm id0 s0 m1) t1 sz align
| sterm_load m1 t1 s1 => 
    sterm_load (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1)
| sterm_gep inbounds t1 s1 ls2 =>
    sterm_gep inbounds t1 (subst_tt id0 s0 s1) (List.map (subst_tt id0 s0) ls2)
| sterm_ext extop t1 s1 t2 => 
    sterm_ext extop t1 (subst_tt id0 s0 s1) t2
| sterm_cast castop t1 s1 t2 => 
    sterm_cast castop t1 (subst_tt id0 s0 s1) t2
| sterm_icmp cond t1 s1 s2 => 
    sterm_icmp cond t1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_phi t1 lsl1 => 
    sterm_phi t1 (List.map 
                   (fun (sl1:sterm*l) => 
                    let (s1,l1):=sl1 in 
                    ((subst_tt id0 s0 s1), l1)
                   ) 
                   lsl1)
| sterm_select s1 t1 s2 s3 => 
    sterm_select (subst_tt id0 s0 s1) t1 (subst_tt id0 s0 s2) (subst_tt id0 s0 s3)
end
with subst_tm (id0:id) (s0:sterm) (m:smem) : smem :=
match m with 
| smem_init => smem_init
| smem_malloc m1 t1 sz align => smem_malloc (subst_tm id0 s0 m1) t1 sz align
| smem_free m1 t1 s1 => smem_free (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1)
| smem_alloca m1 t1 sz align => smem_alloca (subst_tm id0 s0 m1) t1 sz align
| smem_load m1 t1 s1 => smem_load (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1)
| smem_store m1 t1 s1 s2 => smem_store (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
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
