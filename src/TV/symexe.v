Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Export targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import trace.

(***************************************************************)
(* Syntax easy to be proved with symbolic execution. *)

Module SimpleSE.

Inductive cmd : Set := 
 | insn_bop : id -> bop -> sz -> value -> value -> cmd
 | insn_extractvalue : id -> typ -> value -> list const -> cmd
 | insn_insertvalue : id -> typ -> value -> typ -> value -> list const -> cmd
 | insn_malloc : id -> typ -> sz -> align -> cmd
 | insn_free : id -> typ -> value -> cmd
 | insn_alloca : id -> typ -> sz -> align -> cmd
 | insn_load : id -> typ -> value -> cmd
 | insn_store : id -> typ -> value -> value -> cmd
 | insn_gep : id -> inbounds -> typ -> value -> list value -> cmd
 | insn_ext : id -> extop -> typ -> value -> typ -> cmd
 | insn_cast : id -> castop -> typ -> value -> typ -> cmd
 | insn_icmp : id -> cond -> typ -> value -> value -> cmd
 | insn_select : id -> value -> typ -> value -> value -> cmd
.

Tactic Notation "cmd_cases" tactic(first) tactic(c) :=
  first;
  [ c "insn_bop" | c "insn_extractvalue" | c "insn_insertvalue" |
    c "insn_malloc" | c "insn_free" |
    c "insn_alloca" | c "insn_load" | c "insn_store" | c "insn_gep" |
    c "insn_ext" | c "insn_cast" | c "insn_icmp" |  c "insn_select" ].

Inductive call : Set := 
 | insn_call : id -> noret -> tailc -> typ -> id -> list_param -> call.

Inductive subblock : Set :=
 | subblock_intro : list cmd -> call -> subblock.

Inductive block : Set :=
 | block_intro : l -> list phinode -> list subblock -> terminator -> block.

Inductive fdef : Set := 
 | fdef_intro : fheader -> list block -> fdef.

Inductive product : Set := 
 | product_gvar : gvar -> product
 | product_fdec : fdec -> product
 | product_fdef : fdef -> product.

Inductive module : Set := 
 | module_intro : list_layout -> list product -> module.

Definition system : Set := list module.

(***************************************************************)
(* deterministic big-step for this new syntax with subblocks. *)

Record ExecutionContext : Set := mkEC {
CurFunction : fdef;
CurBB       : block;
CurCmds     : list subblock;         (* subblock to run within CurBB *)
Terminator  : terminator;
Locals      : GVMap;                 (* LLVM values used in this invocation *)
Args        : list GenericValue;      
Allocas     : list mblock            (* Track memory allocated by alloca *)
}.

Definition ECStack := list ExecutionContext.

Record State : Set := mkState {
CurSystem      : system;
CurTatgetData  : layouts;
CurProducts    : list product;
ECS            : ECStack;
Globals        : GVMap;
Mem            : mem
}.

Variable lookupBlockViaLabelFromSystem : system -> l -> option block.
Variable switchToNewBasicBlock : block -> block -> GVMap -> GVMap.
Variable lookupFdefViaIDFromSystem : system -> id -> option fdef.
Variable getEntryBlock : fdef -> option block.

Inductive dbCmd : State -> State -> trace -> Prop :=
| dbBop: forall S TD Ps F B lc gl lc' gl' arg id bop sz v1 v2 gv3 EC cs c sbs tmn Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gv3 ->
  updateEnv lc gl id gv3 = (lc', gl') -> 
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_bop id bop sz v1 v2)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc' arg als)::EC) gl' Mem)
    trace_nil 
| dbExtractValue : forall S TD Ps F B lc gl lc' gl' arg id t v gv gv' idxs EC cs c sbs tmn Mem als,
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  updateEnv lc gl id gv' = (lc', gl') -> 
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_extractvalue id t v idxs)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc' arg als)::EC) gl' Mem)
    trace_nil 
| dbInsertValue : forall S TD Ps F B lc gl lc' gl' arg id t v t' v' gv gv' gv'' idxs EC cs c sbs tmn Mem als,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  updateEnv lc gl id gv'' = (lc', gl') -> 
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_insertvalue id t v t' v' idxs)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc' arg als)::EC) gl' Mem)
    trace_nil 
| dbMalloc : forall S TD Ps F B lc gl lc' gl' arg id t sz align EC cs c sbs tmn Mem als Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  malloc TD Mem (tsz * sz) align = Some (Mem', mb) ->
  updateEnv lc gl id (ptr2GV TD (mb, 0)) = (lc', gl') -> 
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_malloc id t sz align)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc' arg als)::EC) gl' Mem')
    trace_nil
| dbFree : forall S TD Ps F B lc gl arg fid t v EC cs c sbs tmn Mem als Mem' mptr,
  getOperandPtr TD v lc gl = Some mptr ->
  free Mem mptr = Some Mem'->
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_free fid t v)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc arg als)::EC) gl Mem')
    trace_nil
| dbAlloca : forall S TD Ps F B lc gl lc' gl' arg id t sz align EC cs c sbs tmn Mem als Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  malloc TD Mem (tsz * sz) align = Some (Mem', mb) ->
  updateEnv lc gl id (ptr2GV TD (mb, 0)) = (lc', gl') -> 
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_alloca id t sz align)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc' arg (mb::als))::EC) gl' Mem')
    trace_nil
| dbLoad : forall S TD Ps F B lc gl lc' gl' arg id t v EC cs c sbs tmn Mem als mp gv,
  getOperandPtr TD v lc gl = Some mp ->
  mload TD Mem mp t = Some gv ->
  updateEnv lc gl id gv = (lc', gl') -> 
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_load id t v)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc' arg als)::EC) gl' Mem)
    trace_nil
| dbStore : forall S TD Ps F B lc gl arg sid t v1 v2 EC cs c sbs tmn Mem als mp2 gv1 Mem',
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandPtr TD v2 lc gl = Some mp2 ->
  mstore TD Mem mp2 t gv1 = Some Mem' ->
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_store sid t v1 v2)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc arg als)::EC) gl Mem')
    trace_nil
| dbGEP : forall S TD Ps F B lc gl lc' gl' arg id inbounds t v idxs EC mp mp' cs c sbs tmn Mem als,
  getOperandPtr TD v lc gl = Some mp ->
  GEP TD lc gl t mp idxs inbounds = Some mp' ->
  updateEnv lc gl id (ptr2GV TD mp') = (lc', gl') -> 
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_gep id inbounds t v idxs)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc' arg als)::EC) gl' Mem)
    trace_nil 
| dbExt : forall S TD Ps F B lc gl arg id extop t1 v1 t2 gv2 EC cs c sbs tmn lc' gl' Mem als,
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  updateEnv lc gl id gv2 = (lc', gl') -> 
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_ext id extop t1 v1 t2)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc' arg als)::EC) gl' Mem)
    trace_nil
| dbCast : forall S TD Ps F B lc gl arg id castop t1 v1 t2 gv2 EC cs c sbs tmn lc' gl' Mem als,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  updateEnv lc gl id gv2 = (lc', gl') -> 
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_cast id castop t1 v1 t2)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc' arg als)::EC) gl' Mem)
    trace_nil
| dbIcmp : forall S TD Ps F B lc gl arg id cond t v1 v2 gv3 EC cs c sbs tmn lc' gl' Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  updateEnv lc gl id gv3 = (lc', gl') -> 
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_icmp id cond t v1 v2)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc' arg als)::EC) gl' Mem)
    trace_nil
| dbSelect : forall S TD Ps F B lc gl arg id v0 t v1 v2 cond EC cs c sbs tmn lc' gl' Mem als gv1 gv2,
  getOperandInt TD 1 v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  (lc', gl') = (if cond
               then updateEnv lc gl id gv1
               else updateEnv lc gl id gv2) ->
  dbCmd 
    (mkState S TD Ps ((mkEC F B ((subblock_intro ((insn_select id v0 t v1 v2)::cs) c)::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B ((subblock_intro cs c)::sbs) tmn lc' arg als)::EC) gl' Mem)
    trace_nil
.

Inductive dbTerminator : State -> State -> trace -> Prop :=
| dbBranch : forall S TD Ps F B lc gl arg bid Cond l1 l2 c
                              l' ps' sbs' tmn' lc' EC Mem als,   
  getOperandInt TD 1 Cond lc gl = Some c ->
  Some (block_intro l' ps' sbs' tmn') = (if c 
               then lookupBlockViaLabelFromSystem S l1
               else lookupBlockViaLabelFromSystem S l2) ->
  lc' = switchToNewBasicBlock (block_intro l' ps' sbs' tmn') B lc ->
  dbTerminator 
    (mkState S TD Ps ((mkEC F B nil (insn_br bid Cond l1 l2) lc arg als)::EC) gl Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' sbs' tmn') sbs' tmn' lc' arg als)::EC) gl Mem)
    trace_nil 
| dbBranch_uncond : forall S TD Ps F B lc gl arg l bid
                              l' ps' sbs' tmn' lc' EC Mem als,   
  Some (block_intro l' ps' sbs' tmn') = (lookupBlockViaLabelFromSystem S l) ->
  lc' = switchToNewBasicBlock (block_intro l' ps' sbs' tmn') B lc ->
  dbTerminator 
    (mkState S TD Ps ((mkEC F B nil (insn_br_uncond bid l) lc arg als)::EC) gl Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' sbs' tmn') sbs' tmn' lc' arg als)::EC) gl Mem)
    trace_nil 
.

Inductive dbCmds : State -> State -> trace -> Prop :=
| dbCmds_nil : forall S, dbCmds S S trace_nil
| dbCmds_cons : forall S1 S2 S3 t1 t2,
    dbCmd S1 S2 t1 ->
    dbCmds S2 S3 t2 ->
    dbCmds S1 S3 (trace_app t1 t2).

Inductive dbCall : State -> State -> trace -> Prop :=
| dbCall_intro : forall S TD Ps F B lc gl arg rid noret tailc rt fid lp gl' gl'' sbs tmn
                       EC Rid oResult tr lc'' B' lc' Mem Mem' als' als Mem'',
  dbFdef fid rt lp S TD Ps ((mkEC F B ((subblock_intro nil (insn_call rid noret tailc rt fid lp))::sbs) tmn lc arg als)::EC) lc gl Mem lc' gl' als' Mem' B' Rid oResult tr ->
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
  dbCall 
    (mkState S TD Ps ((mkEC F B ((subblock_intro nil (insn_call rid noret tailc rt fid lp))::sbs) tmn lc arg als)::EC) gl Mem) 
    (mkState S TD Ps ((mkEC F B sbs tmn lc'' arg als)::EC) gl'' Mem'') 
    tr
with dbSubblock : State -> State -> trace -> Prop :=
| dbSubblock_intro : forall state1 state2 tr1 state3 tr2,
  dbCmds state1 state2 tr1 ->
  dbCall state2 state3 tr2 ->
  dbSubblock state1 state3 (trace_app tr1 tr2)
with dbSubblocks : State -> State -> trace -> Prop :=
| dbSubblocks_nil : forall S, dbSubblocks S S trace_nil
| dbSubblocks_cond : forall S1 S2 S3 t1 t2,
    dbSubblock S1 S2 t1 ->
    dbSubblocks S2 S3 t2 ->
    dbSubblocks S1 S3 (trace_app t1 t2)
with dbBlock : State -> State -> trace -> Prop :=
| dbBlock_intro : forall state1 state2 tr1 state3 tr2,
  dbSubblocks state1 state2 tr1 ->
  dbTerminator state2 state3 tr2 ->
  dbBlock state1 state3 (trace_app tr1 tr2)
with dbBlocks : State -> State -> trace -> Prop :=
| dbBlocks_nil : forall S, dbBlocks S S trace_nil
| dbBlocks_cons : forall S1 S2 S3 t1 t2,
    dbBlock S1 S2 t1 ->
    dbBlocks S2 S3 t2 ->
    dbBlocks S1 S3 (trace_app t1 t2)
with dbFdef : id -> typ -> list_param -> system -> layouts -> list product -> list ExecutionContext -> GVMap -> GVMap -> mem -> GVMap -> GVMap -> list mblock -> mem -> block -> id -> option value -> trace -> Prop :=
| dbFdef_func : forall S TD Ps gl fid lp lc rid
                            l' ps' cs' tmn' rt la lb B'' Result lc' gl' tr ECs Mem Mem' als',
  lookupFdefViaIDFromSystem S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some (block_intro l' ps' cs' tmn') ->
  dbBlocks 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             (block_intro l' ps' cs' tmn') cs' tmn' (initLocals la (params2GVs TD lp lc gl))
                            (params2GVs TD lp lc gl) nil)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             B'' nil (insn_return rid rt Result) lc'
                            (params2GVs TD lp lc gl) als')::ECs) gl' Mem')
    tr ->
  dbFdef fid rt lp S TD Ps ECs lc gl Mem lc' gl' als' Mem' B'' rid (Some Result) tr
| dbFdef_proc : forall S TD Ps gl fid lp lc rid
                            l' ps' cs' tmn' rt la lb B'' lc' gl' tr ECs Mem Mem' als',
  lookupFdefViaIDFromSystem S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some (block_intro l' ps' cs' tmn') ->
  dbBlocks 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             (block_intro l' ps' cs' tmn') cs' tmn' (initLocals la (params2GVs TD lp lc gl))
                            (params2GVs TD lp lc gl) nil)::ECs) gl Mem)
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             B'' nil (insn_return_void rid) lc'
                            (params2GVs TD lp lc gl) als')::ECs) gl' Mem')
    tr ->
  dbFdef fid  rt lp S TD Ps ECs lc gl Mem lc' gl' als' Mem' B'' rid None tr
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
Lemma dbCmd_inversion : forall a cs S TD Ps F B call0 sbs tmn arg als ECs lc gl Mem1 state2 tr,
  dbCmd (mkState S TD Ps ((mkEC F B ((subblock_intro (a::cs) call0)::sbs) tmn lc arg als)::ECs) gl Mem1)
        state2
        tr ->
  exists lc', exists gl', exists als', exists Mem2,
    state2 = (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc' arg als')::ECs) gl' Mem2).
Proof.
  intros a cs S TD Ps F B call0 sbs tmn arg0 als ECs lc gl Mem1 state2 tr HdbCmd.
  inversion HdbCmd; subst; 
  try solve [
    exists lc'; exists gl'; exists als; exists Mem1; auto |
    exists lc'; exists gl'; exists als; exists Mem'; auto |
    exists lc; exists gl; exists als; exists Mem'; auto |
    exists lc'; exists gl'; exists (mb::als); exists Mem'; auto
  ].
Qed.


(***************************************************************)
(** symbolic terms and memories. *)
Inductive sterm : Set := 
| sterm_val : value -> sterm
| sterm_bop : bop -> sz -> sterm -> sterm -> sterm
| sterm_extractvalue : typ -> sterm -> list const -> sterm
| sterm_insertvalue : typ -> sterm -> typ -> sterm -> list const -> sterm
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

Fixpoint updateSmap (sm:smap) (id0:id) (s0:sterm) : smap :=
match sm with
| nil => (id0, s0)::nil
| (id1, s1)::sm' =>
  if id1==id0
  then (id1, s0)::sm'
  else (id1, s1)::updateSmap sm' id0 s0
end.

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

Fixpoint list_param__list_typ_subst_sterm (list_param1:list_param) (sm:smap) : list (typ*sterm) :=
match list_param1 with
| nil => nil
| (t, v)::list_param1' => (t, (value2Sterm sm v))::(list_param__list_typ_subst_sterm list_param1' sm)
end.

Definition se_cmd (st : sstate) (i:cmd) : sstate :=
match i with 
| insn_bop id0 op0 sz0 v1 v2 => 
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_bop op0 sz0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
| insn_extractvalue id0 t1 v1 cs3 =>
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_extractvalue t1 
                     (value2Sterm st.(STerms) v1)
                     cs3))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
| insn_insertvalue id0 t1 v1 t2 v2 cs3 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_insertvalue 
                     t1 
                     (value2Sterm st.(STerms) v1)
                     t2 
                     (value2Sterm st.(STerms) v2)
                     cs3))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
| insn_malloc id0 t1 sz1 al1 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_malloc st.(SMem) t1 sz1 al1))
                 (smem_malloc st.(SMem) t1 sz1 al1)
                 st.(SFrame)
                 st.(SEffects))
| insn_free id0 t0 v0 =>  
       (mkSstate st.(STerms)
                 (smem_free st.(SMem) t0 
                   (value2Sterm st.(STerms) v0))
                 st.(SFrame)
                 st.(SEffects))
| insn_alloca id0 t1 sz1 al1 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_alloca st.(SMem) t1 sz1 al1))
                 (smem_alloca st.(SMem) t1 sz1 al1)
                 (sframe_alloca st.(SMem) st.(SFrame) t1 sz1 al1)
                 st.(SEffects))
| insn_load id0 t2 v2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_load st.(SMem) t2 
                     (value2Sterm st.(STerms) v2)))
                 (smem_load st.(SMem)t2 
                   (value2Sterm st.(STerms) v2))
                 st.(SFrame)
                 st.(SEffects))
| insn_store id0 t0 v1 v2 =>  
       (mkSstate st.(STerms)
                 (smem_store st.(SMem) t0 
                   (value2Sterm st.(STerms) v1)
                   (value2Sterm st.(STerms) v2))
                 st.(SFrame)
                 st.(SEffects))
| insn_gep id0 inbounds0 t1 v1 lv2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_gep inbounds0 t1 
                     (value2Sterm st.(STerms) v1)
                     (List.map (value2Sterm st.(STerms)) lv2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
| insn_ext id0 op0 t1 v1 t2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_ext op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
| insn_cast id0 op0 t1 v1 t2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_cast op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
| insn_icmp id0 c0 t0 v1 v2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_icmp c0 t0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
| insn_select id0 v0 t0 v1 v2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_select 
                     (value2Sterm st.(STerms) v0)
                     t0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
end.

Fixpoint _se_phinodes (st st0: sstate) (ps:list phinode) : sstate :=
match ps with
| nil => st
| insn_phi id0 t0 idls0::ps' =>  
    _se_phinodes 
     (mkSstate (updateSmap st.(STerms) id0 
                 (sterm_phi 
                   t0 
                   (List.map
                     (fun (idl:id*l) =>
                      let (id5, l5) := idl in
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

Fixpoint se_cmds (st : sstate) (cs:list cmd) : sstate :=
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

Definition se_call (st : sstate) (i:call) : scall :=
match i with
| insn_call id0 noret tailc0 t1 id1 list_param1 =>  
                   (stmn_call id0 noret tailc0 t1 id1 
                      (list_param__list_typ_subst_sterm list_param1 st.(STerms)))
end.

(* Properties *)

Lemma updateSmap_dom_eq : forall sm id0 st0,
  dom (updateSmap sm id0 st0) [=] dom sm `union` {{id0}}.
Proof.
  induction sm; intros; simpl; try solve [fsetdec].
    destruct a. 
    destruct (a==id0); simpl; try solve [fsetdec].
      assert (J:=@IHsm id0 st0). fsetdec.
Qed.

Lemma updateSmap_uniq : forall sm id0 st0,
  uniq sm ->
  uniq (updateSmap sm id0 st0).
Proof.
  induction sm; intros; simpl; auto.
    destruct a.

    destruct_uniq.
    destruct (a==id0); subst; try solve [solve_uniq].
      apply IHsm with (id0:=id0)(st0:=st0) in H. 
      assert (J:=@updateSmap_dom_eq sm id0 st0).
      solve_uniq.
Qed.

Lemma se_cmd_uniq : forall smap0 sm0 sf0 se0 c,
  uniq smap0 ->
  uniq (STerms (se_cmd (mkSstate smap0 sm0 sf0 se0) c)).
Proof.
  intros smap0 sm0 sf0 se0 c Huniq.
  destruct c; simpl; try solve [apply updateSmap_uniq; auto | auto].
Qed.

Lemma se_cmd_dom_mono : forall smap0 sm0 sf0 se0 c,
  dom smap0 [<=] dom (STerms (se_cmd (mkSstate smap0 sm0 sf0 se0) c)).
Proof.
  intros smap0 sm0 sf0 se0 c.
  assert (forall sm id0 st0, dom sm [<=] dom (updateSmap sm id0 st0)) as J.
    intros. assert (J:=@updateSmap_dom_eq sm id0 st0). fsetdec. 
  destruct c; simpl; try solve [eauto using J| fsetdec].
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
       
Lemma updateSmap_inversion : forall sm id0 st0 id1 st1,
  uniq sm ->
  binds id1 st1 (updateSmap sm id0 st0) ->
  (id0 <> id1 /\ binds id1 st1 sm) \/ (id0 = id1 /\ st0 = st1).
Proof.
  induction sm; intros id0 st0 id1 st1 Uniq Binds; simpl in Binds.
    analyze_binds Binds.

    destruct a.
    inversion Uniq; subst.
    destruct (a==id0); subst.
      analyze_binds Binds.
      left. split; auto.
        apply binds_In in BindsTac.
        fsetdec.

      analyze_binds Binds.
      apply IHsm in BindsTac; auto.
        destruct BindsTac; auto.
          destruct H; auto.
Qed.

            
Lemma binds_updateSmap_eq : forall sm id0 st0,
  binds id0 st0 (updateSmap sm id0 st0).
Proof.
  induction sm; intros id0 st0; simpl; auto.
    destruct a.
    destruct (a == id0); subst; auto.
Qed.

Lemma binds_updateSmap_neq : forall sm id0 st0 id1 st1,
  binds id1 st1 sm ->
  id0 <> id1 ->
  binds id1 st1 (updateSmap sm id0 st0).
Proof.
  induction sm; intros id0 st0 id1 st1 Hbinds id0_neq_id1; simpl; auto.
    destruct a.
    simpl_env in Hbinds.
    analyze_binds Hbinds.
      destruct (a == id0); subst; auto.
        contradict id0_neq_id1; auto.

      destruct (a == id0); subst; auto.
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
| sterms_nil_denote_genericvalues : forall TD lc gl Mem,
  sterms_denote_genericvalues TD lc gl Mem nil nil
| sterms_cons_denote_genericvalues : forall TD lc gl Mem sts st gvs gv,
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
| c "sterms_nil_denote_genericvalues"
| c "sterms_cons_denote_genericvalues"
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
    lookupEnv id' lc' gl' = Some gv') /\
(forall id' gv',  
  lookupEnv id' lc' gl' = Some gv' ->
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
| (id0, _)::gl' => updateSmap (globals_to_smap gl') id0 (sterm_val (value_id id0)) 
end.

Fixpoint locals_to_smap (lc:GVMap) (m0:smap) : smap :=
match lc with
| nil => m0
| (id0, _)::lc' => updateSmap (locals_to_smap lc' m0) id0 (sterm_val (value_id id0)) 
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
    rewrite updateSmap_dom_eq. fsetdec.
Qed.

Lemma locals_to_smap_dom_eq : forall lc m0,
  dom (locals_to_smap lc m0) [=] dom lc `union` dom m0.
Proof.
  induction lc; intros m0; simpl.
    fsetdec.

    destruct a.
    rewrite updateSmap_dom_eq. 
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
    apply updateSmap_uniq; auto.
Qed.

Lemma locals_to_smap_uniq : forall lc m0,
  uniq m0 ->
  uniq (locals_to_smap lc m0).
Proof.
  induction lc; simpl; intros; auto.
    destruct a.
    apply updateSmap_uniq; auto.
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
  exists gv, lookupGVMap gl id0 = Some gv.
Proof.
  induction gl; intros; simpl in *.
    inversion H0.

    inversion H; subst.
    apply updateSmap_inversion in H0; auto using globals_to_smap_uniq.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 x); subst; simpl; auto.
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
  (st0 = sterm_val (value_id id0) /\ exists gv, lookupGVMap lc id0 = Some gv) \/
  binds id0 st0 m0.  
Proof.
  induction lc; intros; simpl in *; auto.
    inversion H0; subst.
    apply updateSmap_inversion in H1; auto using locals_to_smap_uniq.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 x); subst; simpl; auto.
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
      destruct (lookupGVMap lc id0).
        exists g. auto.
        exists gv. auto.
Qed.

Lemma env_to_smap_denotes__imples__gv : forall id0 st0 TD Mem0 gl lc,
  uniq gl ->
  uniq lc -> 
  binds id0 st0 (env_to_smap gl lc) ->
  exists gv0,
    sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 /\
    lookupEnv id0 lc gl = Some gv0.
Proof.
  intros id0 st0 TD Mem0 gl lc Uniqg Uniqc Binds.
  apply binds_env_to_smap with (TD:=TD) in Binds; auto.
  destruct Binds as [J1 [gv0 J2]]; subst.
  exists gv0. split; auto.
Qed.

Lemma lookupEnv_globals_to_smap : forall gl id0 gv0,
  lookupGVMap gl id0 = Some gv0 ->
  binds id0 (sterm_val (value_id id0)) (globals_to_smap gl).
Proof.
  induction gl; intros; simpl in *.
    inversion H.
    destruct a.
    destruct (id0==i0); subst.
      inversion H; subst. 
      apply binds_updateSmap_eq; auto.

      apply binds_updateSmap_neq; eauto.
Qed.

Lemma lookupEnv_locals_to_smap : forall lc m1 id0 gv0,
  lookupGVMap lc id0 = Some gv0 ->
  binds id0 (sterm_val (value_id id0)) (locals_to_smap lc m1).
Proof.
  induction lc; intros; simpl in *.
    inversion H.
    destruct a.
    destruct (id0==i0); subst.
      inversion H; subst. 
      apply binds_updateSmap_eq; auto.

      apply binds_updateSmap_neq; eauto.
Qed.

Lemma lookupEnv_locals_to_smap' : forall lc m1 st0 id0,
  lookupGVMap lc id0 = None ->
  binds id0 st0 m1 ->
  binds id0 st0 (locals_to_smap lc m1).
Proof.
  induction lc; intros; simpl in *; auto.
    destruct a.
    destruct (id0==i0); subst.
      inversion H.    
      apply binds_updateSmap_neq; eauto.
Qed.

Lemma lookupEnv_env_to_smap : forall id0 gv0 gl lc,
  lookupEnv id0 lc gl = Some gv0 ->
  binds id0 (sterm_val (value_id id0)) (env_to_smap gl lc).
Proof.
  intros.
  unfold lookupEnv in H.
  unfold env_to_smap.
  remember (lookupGVMap lc id0) as ogv.
  destruct ogv.
    inversion H; subst.
    eapply lookupEnv_locals_to_smap; eauto.

    apply lookupEnv_locals_to_smap'; auto.
    apply lookupEnv_globals_to_smap in H; auto.
Qed.

Lemma gv__imples__env_to_smap_denotes : forall id0 TD Mem0 gl lc gv0,
  lookupEnv id0 lc gl = Some gv0 ->
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

(* Symbolic execuction is complete:
   Any concrete execution of a subblock satisfies its symbolic execution. *)

Lemma genericvalue__implies__value2Sterm_denotes : forall TD lc0 gl0 Mem0 smap1 lc gl v gv,
  uniq smap1 ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 smap1 lc gl ->
  getOperandValue TD v lc gl = Some gv ->
  sterm_denotes_genericvalue TD lc0 gl0 Mem0 (value2Sterm smap1 v) gv.
Proof.
  intros D lc0 gl0 Mem0 smap1 lc gl v gv Huniq Hdenotes J.
  unfold getOperandValue in J.
  unfold smap_denotes_gvmap in Hdenotes.
  destruct Hdenotes as [J1 J2].
  destruct v.
    apply J2 in J.
    destruct J as [st0 [J3 J4]].
    rewrite id2Sterm_in with (st0:=st0); auto.

    rewrite const2Sterm; auto.
Qed.

Lemma genericvalues__imply__value2Sterm_denote : forall l0 TD lc0 gl0 Mem0 smap1 lc gl gvs0,
  uniq smap1 ->
  (dom lc0 `union` dom gl0) [<=] dom smap1 ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 smap1 lc gl ->
  values2GVs TD l0 lc gl = Some gvs0 ->
  sterms_denote_genericvalues TD lc0 gl0 Mem0 
    (List.map (value2Sterm smap1) l0) gvs0.
Proof.
  induction l0; intros; simpl in *.
    inversion H2; subst; auto.

    remember (getOperandValue TD a lc gl) as ogv.
    destruct ogv; try solve [inversion H2].
    remember (values2GVs TD l0 lc gl) as ogvs.
    destruct ogvs; try solve [inversion H2].
    inversion H2; subst.
    apply sterms_cons_denote_genericvalues; eauto using genericvalue__implies__value2Sterm_denotes.
Qed.

Lemma se_cmd__denotes__op_cmd__case1 : forall lc gl i0 gv3 lc' gl' id' st' smap1 TD lc0 gl0 Mem0,
  updateEnv lc gl i0 gv3 = (lc', gl') ->
  i0 <> id' ->
  binds id' st' smap1 ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 smap1 lc gl ->
  exists gv',
    sterm_denotes_genericvalue TD lc0 gl0 Mem0 st' gv' /\
    lookupEnv id' lc' gl' = Some gv'.
Proof.
  intros lc gl i0 gv3 lc' gl' id' st' smap1 TD lc0 gl0 Mem0 H25 nEQ Hbinds Hsterm_denotes.
  apply lookupEnv_updateEnv_neq with (id1:=id') in H25; auto.
  rewrite <- H25. 
  unfold smap_denotes_gvmap in Hsterm_denotes.
  destruct Hsterm_denotes as [J1 J2].
  apply J1 in Hbinds.
  destruct Hbinds as [gv' [J3 J4]].
  exists gv'. split; auto.
Qed.

Lemma se_cmd__denotes__op_cmd__case2 : forall lc gl i0 gv3 lc' gl' id' smap1 TD lc0 gl0 Mem0 gv' st0,
  updateEnv lc gl i0 gv3 = (lc', gl') ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 smap1 lc gl ->
  lookupEnv id' lc' gl' = Some gv' ->
  id' <> i0 ->
  exists st', binds id' st' (updateSmap smap1 i0 st0) /\ 
              sterm_denotes_genericvalue TD lc0 gl0 Mem0 st' gv'.
Proof.
  intros lc gl i0 gv3 lc' gl' id' smap1 TD lc0 gl0 Mem0 gv' st0 H25 Hsterm_denotes HlookupEnv n.
  apply lookupEnv_updateEnv_neq with (id1:=id') in H25; auto.
  rewrite <- H25 in HlookupEnv.
  destruct Hsterm_denotes as [J1 J2].
  apply J2 in HlookupEnv; auto.
  destruct HlookupEnv as [st' [J3 J4]].
  exists st'. split; auto.
    apply binds_updateSmap_neq; auto.
Qed.

Lemma op_cmd__satisfies__se_cmd : forall S TD Ps F B c cs call0 sbs tmn lc arg als ECs gl lc0 gl0 als0 Mem0 lc' als' gl' Mem1 Mem2 sstate1 tr tr1,
  dbCmd (mkState S TD Ps ((mkEC F B ((subblock_intro (c::cs) call0)::sbs) tmn lc arg als)::ECs) gl Mem1)
         (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc' arg als')::ECs) gl' Mem2)
         tr -> 
  uniq sstate1.(STerms) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 sstate1 lc gl als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd sstate1 c) lc' gl' als' Mem2 (trace_app tr1 tr).
Proof.
  intros S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl lc0 gl0 als0 Mem0 lc' als' gl' Mem1 Mem2 sstate1 tr tr1 HdsInsn Huniq Hsub Hdenotes.
  (cmd_cases (destruct c;
              inversion HdsInsn; subst;
              destruct Hdenotes as [Hsterm_denotes [Hsmem_denotes [Hsframe_denotes Hseffects_denote]]];
              rewrite trace_app_nil__eq__trace) Case).
  Case "insn_bop".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H25; auto.
          rewrite H25.
          apply BOP_inversion in H24.
          destruct H24 as [gv1 [gv2 [J1 [J2 J3]]]].
          exists gv3. split; auto.
          apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_bop b s (value2Sterm (STerms sstate1) v) (value2Sterm (STerms sstate1) v0)).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H25; auto.
            rewrite H25 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply BOP_inversion in H24.
            destruct H24 as [gv1 [gv2 [J1 [J2 J3]]]].
            apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_extractvalue".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H25; auto.
          rewrite H25.
          exists gv'. split; auto.
          apply sterm_extractvalue_denotes with (gv1:=gv); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv'0 HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_extractvalue t (value2Sterm (STerms sstate1) v) l0).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H25; auto.
            rewrite H25 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply sterm_extractvalue_denotes with (gv1:=gv); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_insertvalue".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H28; auto.
          rewrite H28.
          exists gv''. split; auto.
          eapply sterm_insertvalue_denotes; eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv'0 HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_insertvalue t (value2Sterm(STerms sstate1) v) t0 (value2Sterm (STerms sstate1) v0) l0).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H28; auto.
            rewrite H28 in HlookupEnv.
            inversion HlookupEnv; subst.
            eapply sterm_insertvalue_denotes; eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_malloc".
    split; simpl; eauto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H25; auto.
          rewrite H25.
          exists (ptr2GV TD (mb, 0)).
          split; auto.
            eapply sterm_malloc_denotes; eauto.

        intros id' gv'0 HlookupEnv.
        simpl.
        destruct (id'==i0); subst.
          exists (sterm_malloc (SMem sstate1) t s a).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H25; auto.
            rewrite H25 in HlookupEnv.
            inversion HlookupEnv; subst.
            eapply sterm_malloc_denotes; eauto.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_free".
    split; simpl.
      destruct Hsterm_denotes as [J1 J2].
      split; auto.
    split; auto.     
      apply getOperandPtr_inversion in H22.
      destruct H22 as [gv [J1 J2]].
      apply smem_free_denotes with (Mem1:=Mem1)(gv0:=gv)(mptr0:=mptr); auto.
        eapply genericvalue__implies__value2Sterm_denotes; eauto.
    
  Case "insn_alloca".
    split; simpl; eauto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H25; auto.
          rewrite H25.
          exists (ptr2GV TD (mb, 0)).
          split; auto.
          eapply sterm_alloca_denotes; eauto.

        intros id' gv'0 HlookupEnv.
        simpl.
        destruct (id'==i0); subst.
          exists (sterm_alloca (SMem sstate1) t s a).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H25; auto.
            rewrite H25 in HlookupEnv.
            inversion HlookupEnv; subst.
            eapply sterm_alloca_denotes; eauto.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_load".
    split; simpl; eauto.
      apply getOperandPtr_inversion in H22.
      destruct H22 as [gv2 [J1 J2]].
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H24; auto.
          rewrite H24.
          exists gv.
          split; auto.
          apply sterm_load_denotes with (Mem1:=Mem2)(gv0:=gv2)(mp0:=mp); eauto.
            eapply genericvalue__implies__value2Sterm_denotes; eauto.
     
        intros id' gv'0 HlookupEnv.
        simpl.
        destruct (id'==i0); subst.
          exists (sterm_load (SMem sstate1) t (value2Sterm (STerms sstate1) v)).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H24; auto.
            rewrite H24 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply sterm_load_denotes with (Mem1:=Mem2)(gv0:=gv2)(mp0:=mp); eauto.
              eapply genericvalue__implies__value2Sterm_denotes; eauto.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_store".
    split; simpl.
      destruct Hsterm_denotes as [J1 J2].
      split; auto.
    split; auto.
      apply getOperandPtr_inversion in H24.
      destruct H24 as [gv2 [J1 J2]].
      eapply smem_store_denotes; 
        eauto using genericvalue__implies__value2Sterm_denotes.

  Case "insn_gep". 
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        apply getOperandPtr_inversion in H24.
        destruct H24 as [gv0 [J1 J2]].
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H26; auto.
          rewrite H26.
          apply GEP_inversion in H25.
          destruct H25 as [idxs [J3 J4]].
          apply intValues2Nats_inversion in J3.
          destruct J3 as [gvs0 [J31 J32]].
          exists (ptr2GV TD mp').
          split; auto.
            eapply sterm_gep_denotes; eauto using genericvalue__implies__value2Sterm_denotes, genericvalues__imply__value2Sterm_denote.

        intros id' gv' HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_gep i1 t (value2Sterm (STerms sstate1) v) (List.map (value2Sterm (STerms sstate1)) l0)).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H26; auto.
            rewrite H26 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply getOperandPtr_inversion in H24.
            destruct H24 as [gv0 [J1 J2]].
            apply GEP_inversion in H25.
            destruct H25 as [idxs [J3 J4]].
            apply intValues2Nats_inversion in J3.
            destruct J3 as [gvs0 [J31 J32]].
            eapply sterm_gep_denotes; eauto using genericvalue__implies__value2Sterm_denotes, genericvalues__imply__value2Sterm_denote.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_ext".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H25; auto.
          rewrite H25.
          apply EXT_inversion in H24.
          destruct H24 as [gv1 [J1 J2]].
          exists gv2. split; auto.
            apply sterm_ext_denotes with (gv1:=gv1); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_ext e t (value2Sterm (STerms sstate1) v) t0).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H25; auto.
            rewrite H25 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply EXT_inversion in H24.
            destruct H24 as [gv1 [J1 J2]].
            apply sterm_ext_denotes with (gv1:=gv1); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_cast".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H25; auto.
          rewrite H25.
          apply CAST_inversion in H24.
          destruct H24 as [gv1 [J1 J2]].
          exists gv2. split; auto.
            apply sterm_cast_denotes with (gv1:=gv1); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_cast c t (value2Sterm (STerms sstate1) v) t0).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H25; auto.
            rewrite H25 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply CAST_inversion in H24.
            destruct H24 as [gv1 [J1 J2]].
            apply sterm_cast_denotes with (gv1:=gv1); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_icmp".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          apply lookupEnv_updateEnv_eq in H25; auto.
          rewrite H25.
          apply ICMP_inversion in H24.
          destruct H24 as [gv1 [gv2 [J1 [J2 J3]]]].
          exists gv3. split; auto.
            apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_icmp c t (value2Sterm (STerms sstate1) v) (value2Sterm (STerms sstate1) v0)).
          split. 
            apply binds_updateSmap_eq; auto.

            apply lookupEnv_updateEnv_eq in H25; auto.
            rewrite H25 in HlookupEnv.
            inversion HlookupEnv; subst.
            apply ICMP_inversion in H24.
            destruct H24 as [gv1 [gv2 [J1 [J2 J3]]]].
            apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_select".
    split; auto.
      split.
        intros id' st' Hbinds.
        simpl in Hbinds. simpl_env in Hbinds.
        analyze_binds Hbinds.
        apply updateSmap_inversion in Hbinds; auto.
        destruct Hbinds as [[nEQ Hbinds] | [EQ1 EQ2]]; subst.
          destruct cond0; eapply se_cmd__denotes__op_cmd__case1; eauto.

          symmetry in H27.
          apply getOperandInt_inversion in H24. destruct H24 as [gv5 [J1 J2]].
          destruct cond0; apply lookupEnv_updateEnv_eq in H27; auto.
            exists gv1.
            split; auto.
              apply sterm_select_denotes with (c0:=0)(gv0:=gv5)(gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

            exists gv2.
            split; auto.
              apply sterm_select_denotes with (c0:=Datatypes.S cond0)(gv0:=gv5)(gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupEnv.
        simpl. 
        destruct (id'==i0); subst.
          exists (sterm_select (value2Sterm (STerms sstate1) v) t (value2Sterm (STerms sstate1) v0) (value2Sterm (STerms sstate1) v1)).
          split. 
            apply binds_updateSmap_eq; auto.

            apply getOperandInt_inversion in H24. destruct H24 as [gv5 [J1 J2]].
            apply sterm_select_denotes with (c0:=cond0)(gv0:=gv5)(gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.
            symmetry in H27.
            destruct cond0;
              apply lookupEnv_updateEnv_eq in H27; auto;
              rewrite H27 in HlookupEnv;
              inversion HlookupEnv; subst; auto.

          destruct cond0; eapply se_cmd__denotes__op_cmd__case2; eauto.
Qed.

Lemma aux__op_cmds__satisfy__se_cmds : forall cs S TD Ps F B call0 sbs tmn lc0 arg als ECs gl0 als0 Mem0 lc als' gl Mem1 sstate1 lc' gl' Mem2 tr tr1,
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc arg als)::ECs) gl Mem1)
         (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc' arg als')::ECs) gl' Mem2)
         tr ->
  uniq sstate1.(STerms) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 sstate1 lc gl als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds sstate1 cs) lc' gl' als' Mem2 (trace_app tr1 tr).
Proof.
  induction cs; 
    intros S TD Ps F B call0 sbs tmn lc0 arg0 als ECs gl0 als0 Mem0 lc als' gl Mem1 sstate1 lc' gl' Mem2 tr tr1 HdbCmds Huniq Hsub Hdenotes.

    inversion HdbCmds; subst; try solve [rewrite trace_app_nil__eq__trace; auto].
      inversion H.

    inversion HdbCmds; subst.
    assert (Hcmd:=H).
    apply dbCmd_inversion in H.
    destruct H as [lc3 [gl3 [als3 [Mem3 H]]]]; subst.
    simpl.
    apply op_cmd__satisfies__se_cmd with (lc0:=lc0)(gl0:=gl0)(sstate1:=sstate1)(als0:=als0)(Mem0:=Mem0)(tr1:=tr1) in Hcmd; auto.
    rewrite trace_app_commute.
    apply IHcs with (lc0:=lc0)(gl0:=gl0)(sstate1:=se_cmd sstate1 a)(als0:=als0)(Mem0:=Mem0)(tr1:=trace_app tr1 t1) in H0; auto.
      apply se_cmd_uniq; auto.

      destruct sstate1 as [smap1 sm1 sf1 se1].
      assert (J:=@se_cmd_dom_mono smap1 sm1 sf1 se1 a).
      clear - J Hsub. fsetdec.
Qed.

Lemma op_cmds__satisfy__se_cmds : forall S TD Ps F B cs call0 sbs tmn lc arg als ECs gl Mem lc' als' gl' Mem' tr,
  uniq gl ->
  uniq lc ->
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc arg als)::ECs) gl Mem)
         (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc' arg als')::ECs) gl' Mem')
         tr ->
  sstate_denotes_state TD lc gl als Mem (se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs) lc' gl' als' Mem' tr.
Proof.
  intros S TD Ps F B cs call0 sbs tmn lc arg0 als ECs gl Mem0 lc' als' gl' Mem' tr Uniqg Uniqc HdbCmds.
  apply aux__op_cmds__satisfy__se_cmds with (lc0:=lc)(gl0:=gl)(als0:=als)(Mem0:=Mem0)(sstate1:=mkSstate (env_to_smap gl lc) smem_init sframe_init nil) (tr1:=trace_nil) in HdbCmds; simpl; auto.
    apply env_to_smap_uniq.
    rewrite env_to_smap_dom_eq. fsetdec.
    apply env_to_smap_denotes_id; auto.
Qed.           

(* Symbolic execuction is sound:
   Given a concrete initial state and that its symbolic execution results
   denote some concrete states w.r.t the initial state, it is possible to
   execute the subblock to completion from this initial state. *)

Lemma sterm_denotes_genericvalue_det : forall TD lc gl Mem0 st0 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv2 ->
  gv1 = gv2.
Admitted.

Lemma smem_denotes_mem_det : forall TD lc gl Mem0 st0 Mem1 Mem2,
  smem_denotes_mem TD lc gl Mem0 st0 Mem1 ->
  smem_denotes_mem TD lc gl Mem0 st0 Mem2 ->
  Mem1 = Mem2.
Admitted.

Lemma sframe_denotes_frame_det : forall TD lc gl als Mem0 st0 als1 als2,
  sframe_denotes_frame TD lc gl als Mem0 st0 als1 ->
  sframe_denotes_frame TD lc gl als Mem0 st0 als2 ->
  als1 = als2.
Admitted.

Lemma seffects_denote_trace_det : forall ses tr1 tr2,
  seffects_denote_trace ses tr1 ->
  seffects_denote_trace ses tr2 ->
  tr1 = tr2.
Admitted.

Lemma sstate_denotes_state_det : forall TD lc gl als Mem0 sstate0 lc1 gl1 als1 Mem1 tr1 lc2 gl2 als2 Mem2 tr2,
  sstate_denotes_state TD lc gl als Mem0 sstate0 lc1 gl1 als1 Mem1 tr1 ->
  sstate_denotes_state TD lc gl als Mem0 sstate0 lc2 gl2 als2 Mem2 tr2 ->
  lc1 = lc2 /\ gl1 = gl2 /\ als1 = als2 /\ Mem1 = Mem2 /\ tr1 = tr2.
Admitted.

Lemma value2Sterm_denotes__implies__genericvalue : forall TD lc0 gl0 Mem0 smap1 lc gl v gv,
  uniq smap1 ->
  (dom lc0 `union` dom gl0) [<=] dom smap1 ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 smap1 lc gl ->
  sterm_denotes_genericvalue TD lc0 gl0 Mem0 (value2Sterm smap1 v) gv ->
  getOperandValue TD v lc gl = Some gv.
Proof.
  intros D lc0 gl0 Mem0 smap1 lc gl v gv Huniq Hsub Hdenotes J.
  unfold smap_denotes_gvmap in Hdenotes.
  destruct Hdenotes as [J1 J2].
  destruct v.
    destruct (@AtomSetProperties.In_dec i0 (dom smap1)) as [i0_in_sstate1 | i0_notin_sstate1].
      apply binds_In_inv in i0_in_sstate1.
      destruct i0_in_sstate1 as [st0 Binds].
      rewrite id2Sterm_in with (st0:=st0) in J; auto.
      apply J1 with (id':=i0) in Binds.
      destruct Binds as [gv' [J3 J4]].
      apply sterm_denotes_genericvalue_det with (gv2:=gv') in J; auto.
      subst. auto.

      rewrite id2Sterm_notin in J; auto.
      inversion J; subst.
      simpl in H4.
      apply lookupEnv__indom in H4.
      clear - i0_notin_sstate1 H4 Hsub.
      contradict H4; fsetdec.
    rewrite const2Sterm in J.
    inversion J. auto.
Qed.

Lemma value2Sterm_denote__imply__genericvalues : forall l0 TD lc0 gl0 Mem0 smap1 lc gl gvs0,
  uniq smap1 ->
  (dom lc0 `union` dom gl0) [<=] dom smap1 ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 smap1 lc gl ->
  sterms_denote_genericvalues TD lc0 gl0 Mem0 
    (List.map (value2Sterm smap1) l0) gvs0 ->
  values2GVs TD l0 lc gl = Some gvs0.
Proof.
  induction l0; intros; simpl in *.
    inversion H2; subst; auto.

    inversion H2; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    rewrite H11.
    erewrite IHl0; eauto.
Qed.

Lemma exists_updateEnv : forall lc gl i0 gv3,
  exists lc2, exists gl2, updateEnv lc gl i0 gv3 = (lc2, gl2).
Proof.
  intros lc gl i0 gv3.
  unfold updateEnv.
  destruct (AtomSetProperties.In_dec i0 (dom lc)).
    exists (updateGVMap lc i0 gv3). exists gl. auto.
    destruct (AtomSetProperties.In_dec i0 (dom gl)).
      exists lc. exists (updateGVMap gl i0 gv3). auto.
      exists (updateAddGVMap lc i0 gv3). exists gl. auto.
Qed.    

Lemma aux__se_cmd__denotes__exists_op_cmd : forall S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl Mem1 lc' gl' als' Mem2 lc0 gl0 als0 Mem0 sstate1 tr1 tr2,
  uniq sstate1.(STerms) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 sstate1 lc gl als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd sstate1 c) lc' gl' als' Mem2 tr2 ->
  exists lc', exists gl', exists als', exists Mem2, exists tr,
    dbCmd (mkState S TD Ps ((mkEC F B ((subblock_intro (c::cs) call0)::sbs) tmn lc arg0 als)::ECs) gl Mem1)
          (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc' arg0 als')::ECs) gl' Mem2) 
          tr /\
    tr2 = trace_app tr1 tr.
Proof.
  intros S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl Mem1 lc' gl' als' Mem2 lc0 gl0 als0 Mem0 sstate1 tr1 tr2 Huniq Hsub Hdenotes1 Hdenotes2.
  destruct Hdenotes2 as [[Hsterms_denote21 Hsterms_denote22] [Hsmem_denotes2 [Hsframe_denotes2 Hseffects_denote2]]].
  destruct Hdenotes1 as [Hsterms_denote1 [Hsmem_denotes1 [Hsframe_denotes1 Hseffects_denote1]]].
  inversion Hseffects_denote1; subst.
  inversion Hseffects_denote2; subst.
  (cmd_cases (destruct c) Case).
  Case "insn_bop".
    assert (binds i0  
             (sterm_bop b s (value2Sterm (STerms sstate1) v)
                            (value2Sterm (STerms sstate1) v0))
             (STerms (se_cmd sstate1 (insn_bop i0 b s v v0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv3 [bop_denotes_gv3 gv3_in_env']].
    inversion bop_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 gv3).
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    exists lc2. exists gl2. exists als. exists Mem1. exists trace_nil. 
    assert (BOP TD lc gl b s v v0 = Some gv3) as J.
      unfold BOP. rewrite H10. rewrite H11. auto.
    split; eauto.

  Case "insn_extractvalue".
    assert (binds i0  
             (sterm_extractvalue t
                            (value2Sterm (STerms sstate1) v)
                            l0)
             (STerms (se_cmd sstate1 (insn_extractvalue i0 t v l0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [extractvalue_denotes_gv' gv_in_env']].
    inversion extractvalue_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H9; auto.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 gv').
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    exists lc2. exists gl2. exists als. exists Mem1. exists trace_nil.
    split; eauto.

  Case "insn_insertvalue". admit.

  Case "insn_malloc".
    assert (binds i0  
             (sterm_malloc (SMem sstate1) t s a)
             (STerms (se_cmd sstate1 (insn_malloc i0 t s a)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [malloc_denotes_gv' gv_in_env']].
    inversion malloc_denotes_gv'; subst.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 (ptr2GV TD (mb, 0))).
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H10; auto.
    subst.
    exists lc2. exists gl2. exists als. exists Mem5. exists trace_nil.
    split; eauto.

  Case "insn_free".
    inversion Hsmem_denotes2; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H4; auto.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H9; auto.
    subst.
    exists lc. exists gl. exists als. exists Mem2. exists trace_nil.
    assert (getOperandPtr TD v lc gl = Some mptr0) as J.
      unfold getOperandPtr. rewrite H4. auto.
    split; eauto.

  Case "insn_alloca".
    assert (binds i0  
             (sterm_alloca (SMem sstate1) t s a)
             (STerms (se_cmd sstate1 (insn_alloca i0 t s a)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote21 in J.
    destruct J as [gv' [alloca_denotes_gv' gv_in_env']].
    inversion alloca_denotes_gv'; subst.
    assert (HupdateEnv:=exists_updateEnv lc gl i0 (ptr2GV TD (mb, 0))).
    destruct HupdateEnv as [lc2 [gl2 HupdateEnv]].
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H10; auto.
    subst.
    exists lc2. exists gl2. exists (mb::als). exists Mem5. exists trace_nil.
    split; eauto.

Admitted.

Lemma aux__se_cmd__denotes__op_cmd : forall S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl Mem1 lc' gl' als' Mem2 lc0 gl0 als0 Mem0 sstate1 tr1 tr2,
  uniq sstate1.(STerms) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 sstate1 lc gl als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd sstate1 c) lc' gl' als' Mem2 tr2 ->
  exists tr,
    dbCmd (mkState S TD Ps ((mkEC F B ((subblock_intro (c::cs) call0)::sbs) tmn lc arg0 als)::ECs) gl Mem1)
          (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc' arg0 als')::ECs) gl' Mem2)
          tr /\
    tr2 = trace_app tr1 tr.
Proof.
  intros S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl Mem1 lc' gl' als' Mem2 lc0 gl0 als0 Mem0 sstate1 tr1 tr2 Huniq Hsub Hdenotes1 Hdenotes2.
  assert (J:=Hdenotes2).
  apply aux__se_cmd__denotes__exists_op_cmd with
    (S:=S)(Ps:=Ps)(F:=F)(B:=B)(cs:=cs)(call0:=call0)(sbs:=sbs)(tmn:=tmn)(lc:=lc)
    (arg0:=arg0)(als:=als)(ECs:=ECs)(gl:=gl)(Mem1:=Mem1)(tr1:=tr1) in J; simpl; auto.
  destruct J as [lc'' [gl'' [als'' [Mem2' [tr [HdbCmd EQ]]]]]]; subst.
  exists tr. split; auto.
  assert (Hdenotes2':=HdbCmd).
  apply op_cmd__satisfies__se_cmd with (lc0:=lc0)(gl0:=gl0)(als0:=als0)(Mem0:=Mem0)(sstate1:=sstate1)(tr1:=tr1) in Hdenotes2'; auto.
  apply sstate_denotes_state_det with (lc2:=lc')(gl2:=gl')(als2:=als')(Mem2:=Mem2)(tr2:=trace_app tr1 tr) in Hdenotes2'; auto.
  destruct Hdenotes2' as [EQ1 [EQ2 [EQ3 [EQ4 EQ5]]]]; subst; auto.
Qed.

Lemma se_cmd__denotes__op_cmd : forall S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl Mem1 lc' gl' als' Mem2 tr,
  uniq gl ->
  uniq lc ->
  sstate_denotes_state TD lc gl als Mem1 (se_cmd (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) c) lc' gl' als' Mem2 tr ->
  dbCmd (mkState S TD Ps ((mkEC F B ((subblock_intro (c::cs) call0)::sbs) tmn lc arg0 als)::ECs) gl Mem1)
        (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc' arg0 als')::ECs) gl' Mem2)
        tr. 
Proof.
  intros S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl Mem1 lc' gl' als' Mem2 tr Huniqg Huniqc Hdenotes.
  assert (J:=Hdenotes).
  apply aux__se_cmd__denotes__op_cmd with
    (lc:=lc)(gl:=gl)(Mem1:=Mem1)(tr1:=trace_nil)(call0:=call0)(sbs:=sbs)(tmn:=tmn)(als:=als)
    (S:=S)(Ps:=Ps)(F:=F)(B:=B)(cs:=cs)(arg0:=arg0)(ECs:=ECs) in J; simpl; auto.
    simpl in J. destruct J as [tr0 [J1 J2]]; subst; auto.
    apply env_to_smap_uniq.
    rewrite env_to_smap_dom_eq. fsetdec.
    apply env_to_smap_denotes_id; auto.
Qed.

Lemma ssa_se_cmd : forall i0 st0 smap1 smem1 sframe1 seffects1 c,
  binds i0 st0 smap1 ->
  binds i0 st0 (STerms (se_cmd (mkSstate smap1 smem1 sframe1 seffects1) c)).
  (* SSA *)
Admitted.

Lemma ssa_se_cmds : forall i0 st0 smap1 smem1 sframe1 seffects1 cs,
  binds i0 st0 smap1 ->
  binds i0 st0 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) cs)).
  (* SSA *)
Admitted.

Lemma se_cmds_denotes__decomposes__head : forall c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (se_cmd (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) c) cs) lc2 gl2 als2 Mem2 tr ->
  exists lc1, exists gl1, exists als1, exists Mem1, exists tr1,
    sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) c) lc1 gl1 als1 Mem1 tr1.
Proof.
  intros c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr Huniqg Huniqc Hdenotes.
  assert (Uniqi:=@env_to_smap_uniq gl0 lc0).
  assert (union (dom lc0) (dom gl0) [<=] dom (env_to_smap gl0 lc0)) as Subi.
    rewrite env_to_smap_dom_eq. fsetdec.
  generalize dependent TD.
  generalize dependent lc0.
  generalize dependent gl0.
  generalize dependent als0.
  generalize dependent Mem0.
  generalize dependent cs.
  generalize dependent lc2.
  generalize dependent gl2.
  generalize dependent als2.
  generalize dependent Mem2.
  generalize dependent tr.
  (cmd_cases (destruct c) Case);
    intros;
    destruct Hdenotes as [[Hsterms_denote1 Hsterms_denote2] [Hsmem_denotes [Hsframe_denotes Hseffects_denote]]].
  Case "insn_bop".
    assert (binds i0  
             (sterm_bop b s (value2Sterm (env_to_smap gl0 lc0) v)
                            (value2Sterm (env_to_smap gl0 lc0) v0))
             (STerms (se_cmds (se_cmd (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) (insn_bop i0 b s v v0)) cs))) as J.
      apply ssa_se_cmds.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [bop_denotes_gv3 gv3_in_env2]].
    inversion bop_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc0)(gl:=gl0) in H8; eauto using env_to_smap_denotes_gvmap.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc0)(gl:=gl0) in H9; eauto using env_to_smap_denotes_gvmap.
    assert (HupdateEnv:=exists_updateEnv lc0 gl0 i0 gv3).
    destruct HupdateEnv as [lc1 [gl1 HupdateEnv]].
    exists lc1. exists gl1. exists als0. exists Mem0. exists trace_nil.
    split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply env_to_smap_denotes__imples__gv with (TD:=TD)(Mem0:=Mem0) in binds_id'_st'; auto.
            destruct binds_id'_st' as [gv' [st'_denotes_gv' gv'_in_env0]].
            exists gv'. split; auto.
            apply lookupEnv_updateEnv_neq with (id1:=id') in HupdateEnv; auto.
            rewrite <- HupdateEnv; auto.

            exists gv3. split; eauto using lookupEnv_updateEnv_eq.

          destruct (i0==id'); subst.
            apply lookupEnv_updateEnv_eq in HupdateEnv.  
            rewrite HupdateEnv in H.
            inversion H; subst.
            exists (sterm_bop b s (value2Sterm (env_to_smap gl0 lc0) v) (value2Sterm (env_to_smap gl0 lc0) v0)).
            split.
              simpl. apply binds_updateSmap_eq; auto.
              eauto using genericvalue__implies__value2Sterm_denotes, env_to_smap_denotes_gvmap.

            apply lookupEnv_updateEnv_neq with (id1:=id') in HupdateEnv; auto.
            rewrite <- HupdateEnv in H.
            assert (J:=H).
            apply lookupEnv_env_to_smap in H; auto.
            exists (sterm_val (value_id id')).
            split; auto.
              apply ssa_se_cmd; auto.
Admitted.

Variable deleteEnv : id -> GVMap -> GVMap -> GVMap*GVMap.

Lemma exists_deleteEnv : forall lc gl i0,
  exists lc2, exists gl2, deleteEnv i0 lc gl = (lc2, gl2).
Admitted.

Lemma updateEnv_deleteEnv_eq : forall lc gl id0 gv0 lc' gl',
  updateEnv lc gl id0 gv0 = (lc', gl') ->
  deleteEnv id0 lc' gl' = (lc, gl).
Admitted.

Lemma lookupEnv_deleteEnv_neq : forall lc gl id0 id1 lc' gl',
  deleteEnv id1 lc gl = (lc', gl') ->
  id0 <> id1 ->
  lookupEnv id0 lc gl = lookupEnv id0 lc' gl'.
Admitted.

Lemma lookupEnv_deleteEnv_eq : forall lc gl id0 lc' gl',
  deleteEnv id0 lc gl = (lc', gl') ->
  lookupEnv id0 lc' gl' = None.
Admitted.

Lemma lookupEnv_deleteEnv_inv : forall lc gl id0 id1 lc' gl' gv,
  deleteEnv id0 lc gl = (lc', gl') ->
  lookupEnv id1 lc' gl' = Some gv ->
  lookupEnv id1 lc gl = Some gv /\ id0 <> id1.
Admitted.


Lemma _se_cmd_uniq : forall c sstate0,
  uniq (STerms sstate0) ->
  uniq (STerms (se_cmd sstate0 c)).
Proof.
  intros c sstate0 Huniq.
  destruct c; simpl; try solve [apply updateSmap_uniq; auto | auto].
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

Lemma deleteEnv_uniq : forall id0 lc gl lc' gl',
  uniq lc ->
  uniq gl ->
  deleteEnv id0 lc gl = (lc', gl') ->
  uniq lc' /\ uniq gl'.
Admitted.

Lemma se_cmds_denotes__decomposes__prefix : forall c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  uniq gl2 ->
  uniq lc2 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) c) lc2 gl2 als2 Mem2 tr ->
  exists lc1, exists gl1, exists als1, exists Mem1, exists tr1,
    sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) lc1 gl1 als1 Mem1 tr1 /\
    uniq gl1 /\ uniq lc1.
Proof.
  intros c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr Huniqg0 Huniqc0 Huniqg2 Huniqc2 Hdenotes.
  assert (uniq (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))) as Uniq1.
    eauto using env_to_smap_uniq, se_cmds_uniq.
  generalize dependent TD.
  generalize dependent lc0.
  generalize dependent gl0.
  generalize dependent als0.
  generalize dependent Mem0.
  generalize dependent cs.
  generalize dependent lc2.
  generalize dependent gl2.
  generalize dependent als2.
  generalize dependent Mem2.
  generalize dependent tr.
  (cmd_cases (destruct c) Case);
    intros;
    destruct Hdenotes as [[Hsterms_denote1 Hsterms_denote2] [Hsmem_denotes [Hsframe_denotes Hseffects_denote]]].
  Case "insn_bop".
    assert (binds i0  
             (sterm_bop b s (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                            (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0))
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_bop i0 b s v v0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [bop_denotes_gv3 gv3_in_env2]].
    destruct (@exists_deleteEnv lc2 gl2 i0) as [lc1 [gl1 HdeleteEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply deleteEnv_uniq in HdeleteEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    split; auto.
      split; auto.
      clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
      split; intros.
        assert (i0 <> id') as i0_isnt_id'. 
          admit. (*SSA*)
        apply ssa_se_cmd with (c:=insn_bop i0 b s v v0)(smem1:=smem_init)(sframe1:=sframe_init)(seffects1:=nil) in H; auto.
        apply Hsterms_denote1 in H.
        destruct H as [gv' [st'_denotes_gv' id'_gv'_in_env2]].
        apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
        rewrite HdeleteEnv in id'_gv'_in_env2.
        exists gv'. split; auto.

        apply lookupEnv_deleteEnv_inv with (gv:=gv')(id1:=id') in HdeleteEnv; auto.
        destruct HdeleteEnv as [id'_in_env2 i0_isnt_id'].
        apply Hsterms_denote2 in id'_in_env2.
        destruct id'_in_env2 as [st' [binds_id'_st' st'_denotes_gv']].
        exists st'. split; auto.
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[_ binds_id'_st'] | [i0_is_id' binds_id'_st']]; auto.
              contradict i0_is_id'; auto.

  Case "insn_extractvalue".
    assert (binds i0  
             (sterm_extractvalue t (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v) l0)
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_extractvalue i0 t v l0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [extracvalue_denotes_gv3 gv3_in_env2]].
    destruct (@exists_deleteEnv lc2 gl2 i0) as [lc1 [gl1 HdeleteEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply deleteEnv_uniq in HdeleteEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    split; auto.
      split; auto.
      clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
      split; intros.
        assert (i0 <> id') as i0_isnt_id'. 
          admit. (*SSA*)
        apply ssa_se_cmd with (c:=insn_extractvalue i0 t v l0)(smem1:=smem_init)(sframe1:=sframe_init)(seffects1:=nil) in H; auto.
        apply Hsterms_denote1 in H.
        destruct H as [gv' [st'_denotes_gv' id'_gv'_in_env2]].
        apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
        rewrite HdeleteEnv in id'_gv'_in_env2.
        exists gv'. split; auto.

        apply lookupEnv_deleteEnv_inv with (gv:=gv')(id1:=id') in HdeleteEnv; auto.
        destruct HdeleteEnv as [id'_in_env2 i0_isnt_id'].
        apply Hsterms_denote2 in id'_in_env2.
        destruct id'_in_env2 as [st' [binds_id'_st' st'_denotes_gv']].
        exists st'. split; auto.
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[_ binds_id'_st'] | [i0_is_id' binds_id'_st']]; auto.
              contradict i0_is_id'; auto.
        
  Case "insn_insertvalue". admit.

  Case "insn_malloc".
    assert (binds i0  
             (sterm_malloc (SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) t s a)
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_malloc i0 t s a)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [malloc_denotes_gv3 gv3_in_env2]].
    destruct (@exists_deleteEnv lc2 gl2 i0) as [lc1 [gl1 HdeleteEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists lc1. exists gl1. exists als2. exists Mem3. exists tr.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply deleteEnv_uniq in HdeleteEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    split; auto.
      split; auto.
      clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
      split; intros.
        assert (i0 <> id') as i0_isnt_id'. 
          admit. (*SSA*)
        apply ssa_se_cmd with (c:=insn_malloc i0 t s a)(smem1:=(SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)))(sframe1:=sframe_init)(seffects1:=nil) in H; auto.
        apply Hsterms_denote1 in H.
        destruct H as [gv' [st'_denotes_gv' id'_gv'_in_env2]].
        apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
        rewrite HdeleteEnv in id'_gv'_in_env2.
        exists gv'. split; auto.

        apply lookupEnv_deleteEnv_inv with (gv:=gv')(id1:=id') in HdeleteEnv; auto.
        destruct HdeleteEnv as [id'_in_env2 i0_isnt_id'].
        apply Hsterms_denote2 in id'_in_env2.
        destruct id'_in_env2 as [st' [binds_id'_st' st'_denotes_gv']].
        exists st'. split; auto.
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[_ binds_id'_st'] | [i0_is_id' binds_id'_st']]; auto.
              contradict i0_is_id'; auto.
    
  Case "insn_free".
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists lc2. exists gl2. exists als2. exists Mem3. exists tr.
    split; auto.
      split; auto.
      clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
      split; intros.
        apply ssa_se_cmd with (c:=insn_free i0 t v)(smem1:=(SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)))(sframe1:=sframe_init)(seffects1:=nil) in H; auto.

        apply Hsterms_denote2 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        exists st'. split; auto.

  Case "insn_alloca".
    assert (binds i0  
             (sterm_alloca (SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) t s a)
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_alloca i0 t s a)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [alloca_denotes_gv3 gv3_in_env2]].
    destruct (@exists_deleteEnv lc2 gl2 i0) as [lc1 [gl1 HdeleteEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    inversion Hsframe_denotes; subst.
    exists lc1. exists gl1. exists (als3). exists Mem3. exists tr.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply deleteEnv_uniq in HdeleteEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    split; auto.
      split; auto.
      clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
      split; intros.
        assert (i0 <> id') as i0_isnt_id'. 
          admit. (*SSA*)
        apply ssa_se_cmd with (c:=insn_alloca i0 t s a)(smem1:=(SMem (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)))(sframe1:=sframe_init)(seffects1:=nil) in H; auto.
        apply Hsterms_denote1 in H.
        destruct H as [gv' [st'_denotes_gv' id'_gv'_in_env2]].
        apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
        rewrite HdeleteEnv in id'_gv'_in_env2.
        exists gv'. split; auto.

        apply lookupEnv_deleteEnv_inv with (gv:=gv')(id1:=id') in HdeleteEnv; auto.
        destruct HdeleteEnv as [id'_in_env2 i0_isnt_id'].
        apply Hsterms_denote2 in id'_in_env2.
        destruct id'_in_env2 as [st' [binds_id'_st' st'_denotes_gv']].
        exists st'. split; auto.
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[_ binds_id'_st'] | [i0_is_id' binds_id'_st']]; auto.
              contradict i0_is_id'; auto.
Admitted.

Lemma se_cmds_dom_sub: forall smap0 sm0 sf0 se0 cs,
  dom smap0 [<=]
    dom (STerms (se_cmds (mkSstate smap0 sm0 sf0 se0) cs)).
Admitted.

Lemma se_cmds_env_to_smap_dom_sub: forall lc0 gl0 cs,
  union (dom lc0) (dom gl0) [<=]
    dom (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)).
Admitted.

Lemma se_cmds_denotes__decomposes__prefix_last : forall c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  uniq gl2 ->
  uniq lc2 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) c) lc2 gl2 als2 Mem2 tr ->
  exists lc1, exists gl1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) lc1 gl1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) c) lc2 gl2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ 
    uniq gl1 /\ uniq lc1.
Proof.
  intros c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr Huniqg0 Huniqc0 Huniqg2 Huniqc2 Hdenotes.
  assert (uniq (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))) as Uniq1.
    eauto using env_to_smap_uniq, se_cmds_uniq.
  assert (Hsub:=@se_cmds_env_to_smap_dom_sub lc0 gl0 cs).
  generalize dependent TD.
  generalize dependent lc0.
  generalize dependent gl0.
  generalize dependent als0.
  generalize dependent Mem0.
  generalize dependent cs.
  generalize dependent lc2.
  generalize dependent gl2.
  generalize dependent als2.
  generalize dependent Mem2.
  generalize dependent tr.
  (cmd_cases (destruct c) Case);
    intros;
    destruct Hdenotes as [[Hsterms_denote1 Hsterms_denote2] [Hsmem_denotes [Hsframe_denotes Hseffects_denote]]].
  Case "insn_bop".
    assert (binds i0  
             (sterm_bop b s (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                            (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0))
             (STerms (se_cmd (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) (insn_bop i0 b s v v0)))) as J.
      simpl. apply binds_updateSmap_eq; auto.
    apply Hsterms_denote1 in J.
    destruct J as [gv3 [bop_denotes_gv3 gv3_in_env2]].
    destruct (@exists_deleteEnv lc2 gl2 i0) as [lc1 [gl1 HdeleteEnv]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists lc1. exists gl1. exists als2. exists Mem2. exists tr. exists trace_nil.
    rewrite trace_app_nil__eq__trace.
    assert (uniq lc1 /\ uniq gl1) as Uniq.
      apply deleteEnv_uniq in HdeleteEnv; auto.
    destruct Uniq as [Huniqc1 Huniqg1].
    assert (smap_denotes_gvmap TD lc0 gl0 Mem0
              (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))
              lc1 gl1) as env0_denote_env1.
      clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
      split; intros.
        assert (i0 <> id') as i0_isnt_id'. 
          admit. (*SSA*)
        apply ssa_se_cmd with (c:=insn_bop i0 b s v v0)(smem1:=smem_init)(sframe1:=sframe_init)(seffects1:=nil) in H; auto.
        apply Hsterms_denote1 in H.
        destruct H as [gv' [st'_denotes_gv' id'_gv'_in_env2]].
        apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
        rewrite HdeleteEnv in id'_gv'_in_env2.
        exists gv'. split; auto.

        apply lookupEnv_deleteEnv_inv with (gv:=gv')(id1:=id') in HdeleteEnv; auto.
        destruct HdeleteEnv as [id'_in_env2 i0_isnt_id'].
        apply Hsterms_denote2 in id'_in_env2.
        destruct id'_in_env2 as [st' [binds_id'_st' st'_denotes_gv']].
        exists st'. split; auto.
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[_ binds_id'_st'] | [i0_is_id' binds_id'_st']]; auto.
              contradict i0_is_id'; auto.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H.
          apply updateSmap_inversion in H; auto using env_to_smap_uniq.
          destruct H as [[i0_isnt_id' binds_id'_st'] | [EQ1 EQ2]]; subst.
            apply env_to_smap_denotes__imples__gv with (TD:=TD)(Mem0:=Mem2) in binds_id'_st'; auto.
            destruct binds_id'_st' as [gv' [st'_denotes_gv' gv'_in_env1]].
            exists gv'. split; auto.
            apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
            rewrite HdeleteEnv; auto.

            exists gv3. split; eauto using lookupEnv_deleteEnv_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion bop_denotes_gv3; subst. clear bop_denotes_gv3.
            apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); auto.
              apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H8; auto.
                apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                  apply env_to_smap_denotes_gvmap; auto.
              apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H9; auto.
                apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                  apply env_to_smap_denotes_gvmap; auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          destruct H as [st' [binds_id'_st' st'_denotes_gv']].
          simpl in binds_id'_st'.
          apply updateSmap_inversion in binds_id'_st'; auto. 
            destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
              apply lookupEnv_deleteEnv_neq with (id0:=id') in HdeleteEnv; auto.
              rewrite HdeleteEnv in id'_in_env2.              
              exists (sterm_val (value_id id')).
              clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
              split; auto.
                simpl.
                apply binds_updateSmap_neq; auto.
                apply lookupEnv_env_to_smap with (gv0:=gv'); auto.

              rewrite id'_in_env2 in gv3_in_env2.
              inversion gv3_in_env2; subst. clear gv3_in_env2.
              simpl.
              exists (sterm_bop b s (value2Sterm (env_to_smap gl1 lc1) v) (value2Sterm (env_to_smap gl1 lc1) v0)).
              split; auto using binds_updateSmap_eq.
                inversion bop_denotes_gv3; subst.
                apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); auto.
                  apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H8; auto.
                    apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                      apply env_to_smap_denotes_gvmap; auto.
                  apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H9; auto.
                    apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                      apply env_to_smap_denotes_gvmap; auto.

Admitted.

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

Lemma se_cmds_denotes__composes__prefix_last : forall c TD lc1 gl1 als1 Mem1 
  lc2 gl2 als2 Mem2 lc0 gl0 als0 Mem0 tr1 tr2 cs,
  uniq lc1 ->
  uniq gl1 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs) lc1 gl1 als1 Mem1 tr1 ->
  sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) c) lc2 gl2 als2 Mem2 tr2 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) (cs++c::nil)) lc2 gl2 als2 Mem2 (trace_app tr1 tr2).
Proof.
  intros c TD lc1 gl1 als1 Mem1 lc2 gl2 als2 Mem2 lc0 gl0 als0 Mem0 tr1 tr2 cs Huniqc1 Huniqg1 Hdenotes1 Hdenotes2.
  assert (uniq (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs))) as Uniq1.
    eauto using env_to_smap_uniq, se_cmds_uniq.
  generalize dependent TD.
  generalize dependent lc0.
  generalize dependent gl0.
  generalize dependent als0.
  generalize dependent Mem0.
  generalize dependent cs.
  generalize dependent lc2.
  generalize dependent gl2.
  generalize dependent als2.
  generalize dependent Mem2.
  generalize dependent lc1.
  generalize dependent gl1.
  generalize dependent als1.
  generalize dependent Mem1.
  generalize dependent tr1.
  generalize dependent tr2.
  (cmd_cases (destruct c) Case);
    intros;
    destruct Hdenotes1 as [[Hsterms_denote11 Hsterms_denote12] [Hsmem_denotes1 [Hsframe_denotes1 Hseffects_denote1]]];
    destruct Hdenotes2 as [[Hsterms_denote21 Hsterms_denote22] [Hsmem_denotes2 [Hsframe_denotes2 Hseffects_denote2]]];
    rewrite se_cmds_rev_cons.
  Case "insn_bop".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H.
        apply updateSmap_inversion in H; auto. 
          destruct H as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
            apply Hsterms_denote11 in binds_id'_st'.
            destruct binds_id'_st' as [gv' [st'_denotes_gv' id'_gv'_in_env1]].
            exists gv'. split; auto.
              admit. (*SSA*)

            assert (binds id' (sterm_bop b s (value2Sterm (env_to_smap gl1 lc1) v) (value2Sterm (env_to_smap gl1 lc1) v0))
                    (STerms (se_cmd (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) (insn_bop id' b s v v0)))
            ) as binds_id'_bop.
              simpl. apply binds_updateSmap_eq; auto.
            apply Hsterms_denote21 in binds_id'_bop.
            destruct binds_id'_bop as [gv' [bop_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion bop_denotes_gv'; subst.
              apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); auto.
                apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H8; auto.
                  apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                    split; auto.
                  apply env_to_smap_uniq.
                  rewrite env_to_smap_dom_eq. fsetdec.
                  apply env_to_smap_denotes_gvmap; auto.
                apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H9; auto.
                  apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                    split; auto.
                  apply env_to_smap_uniq.
                  rewrite env_to_smap_dom_eq. fsetdec.
                  apply env_to_smap_denotes_gvmap; auto.

        apply Hsterms_denote22 in H.
        destruct H as [st' [binds_id'_st' st'_denotes_gv']].
        simpl in binds_id'_st'.
        apply updateSmap_inversion in binds_id'_st'; auto using env_to_smap_uniq.
        destruct binds_id'_st' as [[i0_isnt_id' binds_id'_st'] | [i0_is_id' binds_id'_st']]; subst.
          apply binds_env_to_smap with (TD:=TD) in binds_id'_st'; auto.
            destruct binds_id'_st' as [EQ [gv id'_gv_in_env1]]; subst.
            assert (J:=id'_gv_in_env1).
            unfold getOperandValue in J.
            apply Hsterms_denote12 in J.
            destruct J as [st' [binds_id'_st' st'_denotes_gv]].
            inversion st'_denotes_gv'; subst.
            rewrite id'_gv_in_env1 in H4.
            inversion H4; subst. clear H4.
            exists st'.
            split; auto.
              simpl.
              apply binds_updateSmap_neq; auto.

          exists (sterm_bop b s 
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v)
                   (value2Sterm (STerms (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs)) v0)).
          split.
            simpl. apply binds_updateSmap_eq; auto.
            inversion st'_denotes_gv'; subst.
            apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); auto.
              apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H8; auto.
                apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                  split; auto.
                apply env_to_smap_uniq.
                rewrite env_to_smap_dom_eq. fsetdec.
                apply env_to_smap_denotes_gvmap; auto.
              apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1)(gl:=gl1) in H9; auto.
                apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1)(gl:=gl1); auto using env_to_smap_uniq.
                  split; auto.
                apply env_to_smap_uniq.
                rewrite env_to_smap_dom_eq. fsetdec.
                apply env_to_smap_denotes_gvmap; auto.
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22.
      simpl in *.
      inversion Hsmem_denotes2; subst; auto.
    split.
      clear Hsmem_denotes1 Hseffects_denote1 Hsmem_denotes2 Hseffects_denote2.
      clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22.
      simpl in *.
      inversion Hsframe_denotes2; subst; auto.

      clear Hsmem_denotes1 Hsframe_denotes1 Hsmem_denotes2 Hsframe_denotes2.
      clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22.
      simpl in *.
      inversion Hseffects_denote1; subst.      
      inversion Hseffects_denote2; subst; auto.  
Admitted.

Definition se_cmds_denotes__decomposes__app_prop (cs2:list cmd) :=
forall TD lc0 gl0 als0 Mem0 cs1 lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  uniq gl2 ->
  uniq lc2 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) (cs1++cs2)) lc2 gl2 als2 Mem2 tr ->
  exists lc1, exists gl1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) cs1) lc1 gl1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmds (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) cs2) lc2 gl2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ uniq gl1 /\ uniq lc1.

Lemma se_cmds_denotes__decomposes__app : forall cs2, 
  se_cmds_denotes__decomposes__app_prop cs2.
Proof.
  apply (@rev_ind cmd); unfold se_cmds_denotes__decomposes__app_prop in *; intros; simpl.
  Case "nil".
    exists lc2. exists gl2. exists als2. exists Mem2. exists tr. exists trace_nil.
    rewrite trace_app_nil__eq__trace.
    rewrite <- app_nil_end in H3.
    split; auto.
    split; auto.
      apply env_to_smap_denotes_id; auto.
  Case "cons".
    rewrite <- app_ass in H4.
    rewrite se_cmds_rev_cons in H4.
    apply se_cmds_denotes__decomposes__prefix_last in H4; auto.
    destruct H4 as [lc1 [gl1 [als1 [Mem1 [tr1 [tr2 [env0_denotes_env1 [env1_denotes_env2 [EQ [Huniqg1 Huniqc1]]]]]]]]]]; subst.
    apply H in env0_denotes_env1; auto.
    destruct env0_denotes_env1 as [lc3 [gl3 [als3 [Mem3 [tr3 [tr4 [env0_denotes_env3 [env3_denotes_env1 [EQ [Huniqg3 Huniqc3]]]]]]]]]]; subst.
    exists lc3. exists gl3. exists als3. exists Mem3. exists tr3. exists (trace_app tr4 tr2).
    rewrite trace_app_commute.
    split; auto.
    split; auto.
     apply se_cmds_denotes__composes__prefix_last with (lc1:=lc1)(gl1:=gl1)(als1:=als1)(Mem1:=Mem1); eauto.
Qed.

Lemma se_cmds_cons : forall cs c sstate0,
  se_cmds sstate0 ((c::nil)++cs) = se_cmds (se_cmd sstate0 c) cs.
Proof.
  induction cs; intros; simpl; auto.
Qed.

Lemma se_cmds_denotes__decomposes__head_tail : forall c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr,
  uniq gl0 ->
  uniq lc0 ->
  uniq gl2 ->
  uniq lc2 ->
  sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmds (se_cmd (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) c) cs) lc2 gl2 als2 Mem2 tr ->
  exists lc1, exists gl1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl0 als0 Mem0 (se_cmd (mkSstate (env_to_smap gl0 lc0) smem_init sframe_init nil) c) lc1 gl1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmds (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) cs) lc2 gl2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ uniq gl1 /\ uniq lc1.
Proof.
  intros c TD lc0 gl0 als0 Mem0 cs lc2 gl2 als2 Mem2 tr Huniqg0 Huniqc0 Huniqg2 Huniqc2 Hdenotes.
  rewrite <- se_cmds_cons in Hdenotes.
  apply se_cmds_denotes__decomposes__app in Hdenotes; auto.
Qed.    
  
Lemma se_cmds__denote__exists_op_cmds : forall cs S TD Ps F B call0 sbs tmn lc1 arg als1 ECs gl1 Mem1 lc2 gl2 als2 Mem2 tr,
  uniq gl1 ->
  uniq lc1 ->
  uniq gl2 ->
  uniq lc2 ->
  sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmds (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) cs) lc2 gl2 als2 Mem2 tr ->
  exists lc2', exists gl2', exists als2, exists Mem2', exists tr', 
    dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
           (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc2' arg als2)::ECs) gl2' Mem2')
           tr'.
Proof.
  induction cs; 
    intros S TD Ps F B call0 sbs tmn lc1 arg0 als1 ECs gl1 Mem1 lc2 gl2 als2 Mem2 tr Uniqg1 Uniqc1 Uniqg2 Uniqc2 Hdenotes.

    simpl in *. 
    exists lc1. exists gl1. exists als1. exists Mem2. exists trace_nil. 
    assert (J:=@env_to_smap_denotes_id TD lc1 gl1 als1 Mem1 Uniqg1 Uniqc1).
    apply sstate_denotes_state_det with (lc2:=lc2)(gl2:=gl2)(als2:=als2)(Mem2:=Mem2)(tr2:=tr) in J; auto.
    destruct J as [EQ1 [EQ2 [EQ3 [EQ4 EQ5]]]]; subst; auto.

    simpl in Hdenotes.
    apply se_cmds_denotes__decomposes__head_tail in Hdenotes; auto.
    destruct Hdenotes as [lc3 [gl3 [als3 [Mem3 [tr3 [tr3' [J1 [J2 [EQ [Huniqg3 Huniqc3]]]]]]]]]]; subst.
    apply se_cmd__denotes__op_cmd with
      (S:=S)(Ps:=Ps)(F:=F)(B:=B)(cs:=cs)(call0:=call0)(sbs:=sbs)(tmn:=tmn)(lc:=lc1)
     (arg0:=arg0)(als:=als1)(ECs:=ECs)(gl:=gl1)(Mem1:=Mem1) in J1; simpl; auto.
    apply IHcs with
      (S:=S)(Ps:=Ps)(F:=F)(B:=B)(call0:=call0)(sbs:=sbs)(tmn:=tmn)
      (arg:=arg0)(ECs:=ECs) in J2; simpl; auto.
      destruct J2 as [lc4 [gl4 [als4 [Mem4 [tr4 HdbCmds]]]]].
      exists lc4. exists gl4. exists als4. exists Mem4. exists (trace_app tr3 tr4). 
      apply dbCmds_cons with (S2:=mkState S TD Ps ((mkEC F B (subblock_intro cs call0::sbs) tmn lc3 arg0 als3)::ECs) gl3 Mem3); eauto.
Qed.

Lemma se_cmds__denote__op_cmds : forall S TD Ps F B cs call0 sbs tmn lc1 arg ECs gl1 als1 Mem1 lc2 als2 gl2 Mem2 tr,
  uniq gl1 ->
  uniq lc1 ->
  uniq gl2 ->
  uniq lc2 ->
  sstate_denotes_state TD lc1 gl1 als1 Mem1 (se_cmds (mkSstate (env_to_smap gl1 lc1) smem_init sframe_init nil) cs) lc2 gl2 als2 Mem2 tr ->
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
         (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc2 arg als2)::ECs) gl2 Mem2)
         tr. 
Proof.
  intros S TD Ps F B cs call0 sbs tmn lc1 arg0 ECs gl1 als1 Mem1 lc2 als2 gl2 Mem2 tr Huniqg1 Huniqc1 Huniqg2 Huniqc2 Hdenotes.
  assert (J:=Hdenotes).
  apply se_cmds__denote__exists_op_cmds with
    (S:=S)(Ps:=Ps)(F:=F)(B:=B)(cs:=cs)(call0:=call0)(sbs:=sbs)(tmn:=tmn)(lc1:=lc1)
    (arg:=arg0)(als1:=als1)(ECs:=ECs)(gl1:=gl1)(Mem1:=Mem1) in J; simpl; auto.
  destruct J as [lc2' [gl2' [als2' [Mem2' [tr' HdbCmds]]]]].
  assert (Hdenotes':=HdbCmds).
  apply op_cmds__satisfy__se_cmds in Hdenotes'; auto.
  apply sstate_denotes_state_det with (lc2:=lc2)(gl2:=gl2)(als2:=als2)(Mem2:=Mem2)(tr2:=tr) in Hdenotes'; auto.
  destruct Hdenotes' as [EQ1 [EQ2 [EQ3 [EQ4 EQ5]]]]; subst; auto.
Qed.

(* Correctness of the cmds validator *)

Definition tv_cmds (cs1 cs2 : list cmd) (lc gl:GVMap) :=
se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs1 =
se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs2.

Lemma dbCmds_uniq : forall S TD Ps F B cs cs' call0 sbs tmn lc1 arg als1 ECs gl1 Mem1 lc2 als2 gl2 Mem2 tr,
  uniq gl1 ->
  uniq lc1 ->
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
        (mkState S TD Ps ((mkEC F B ((subblock_intro cs' call0)::sbs) tmn lc2 arg als2)::ECs) gl2 Mem2)
        tr ->
  uniq gl2 /\ uniq lc2.
Admitted.

Lemma tv_cmds__is__correct : forall S TD Ps F B cs cs' call0 sbs tmn lc1 arg als1 ECs gl1 Mem1 lc2 als2 gl2 Mem2 tr,
  uniq gl1 ->
  uniq lc1 ->  
  tv_cmds cs cs' lc1 gl1 ->
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
        (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc2 arg als2)::ECs) gl2 Mem2)
        tr ->
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs' call0)::sbs) tmn lc1 arg als1)::ECs) gl1 Mem1)
        (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc2 arg als2)::ECs) gl2 Mem2)
        tr.
Proof.
  intros S TD Ps F B cs cs' call0 sbs tmn lc1 arg0 als1 ECs gl1 Mem1 lc2 als2 gl2 Mem2 tr Huniqg Huniqc Htv_cmds HdbCmds.
  unfold tv_cmds in Htv_cmds.
  assert (Uniqs:=HdbCmds).
  apply dbCmds_uniq in Uniqs; auto.
  destruct Uniqs as [Uniqg2 Uniqc2].
  apply op_cmds__satisfy__se_cmds in HdbCmds; auto.
  rewrite Htv_cmds in HdbCmds.
  apply se_cmds__denote__op_cmds; auto.
Qed.

Definition tv_subblock (b1 b2:subblock) (lc gl:GVMap) :=
match (b1, b2) with
| (subblock_intro cs1 call1, subblock_intro cs2 call2) =>
  match (call1, call2) with
  | (insn_call id1 _ _ _ _ _, insn_call id2 _ _ _ _ _) => 
    if id1==id2 
    then
      let st1 := se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs1 in
      let st2 := se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs2 in
      let cl1 := se_call st1 call1 in
      let cl2 := se_call st2 call2 in
      st1 = st2 /\ cl1 = cl2
    else
      False
  end
end.

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

