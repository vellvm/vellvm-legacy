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

(* deterministic big-step for this new syntax with subblocks. *)

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
  SMem : smem
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
                 st.(SMem))
| insn_extractvalue id0 t1 v1 cs3 =>
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_extractvalue t1 
                     (value2Sterm st.(STerms) v1)
                     cs3))
                 st.(SMem))
| insn_insertvalue id0 t1 v1 t2 v2 cs3 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_insertvalue 
                     t1 
                     (value2Sterm st.(STerms) v1)
                     t2 
                     (value2Sterm st.(STerms) v2)
                     cs3))
                 st.(SMem))
| insn_malloc id0 t1 sz1 al1 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_malloc st.(SMem) t1 sz1 al1))
                 (smem_malloc st.(SMem) t1 sz1 al1))
| insn_free id0 t0 v0 =>  
       (mkSstate st.(STerms)
                (smem_free st.(SMem) t0 
                  (value2Sterm st.(STerms) v0)))
| insn_alloca id0 t1 sz1 al1 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_alloca st.(SMem) t1 sz1 al1))
                 (smem_alloca st.(SMem) t1 sz1 al1))
| insn_load id0 t2 v2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_load st.(SMem) t2 
                     (value2Sterm st.(STerms) v2)))
                 (smem_load st.(SMem)t2 
                   (value2Sterm st.(STerms) v2)))
| insn_store id0 t0 v1 v2 =>  
       (mkSstate st.(STerms)
                 (smem_store st.(SMem) t0 
                   (value2Sterm st.(STerms) v1)
                   (value2Sterm st.(STerms) v2)))
| insn_gep id0 inbounds0 t1 v1 lv2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_gep inbounds0 t1 
                     (value2Sterm st.(STerms) v1)
                     (List.map (value2Sterm st.(STerms)) lv2)))
                 st.(SMem))
| insn_ext id0 op0 t1 v1 t2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_ext op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem))
| insn_cast id0 op0 t1 v1 t2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_cast op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem))
| insn_icmp id0 c0 t0 v1 v2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_icmp c0 t0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem))
| insn_select id0 v0 t0 v1 v2 =>  
       (mkSstate (updateSmap st.(STerms) id0 
                   (sterm_select 
                     (value2Sterm st.(STerms) v0)
                     t0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem))
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
               st.(SMem))
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

Hint Constructors sterm_denotes_genericvalue sterms_denote_genericvalues smem_denotes_mem.

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

Definition smap_denotes_gvmap TD lc gl Mem sstate' lc' gl' :=
(forall id' st',  
  binds id' st' sstate'.(STerms) ->
  exists gv',
    sterm_denotes_genericvalue TD lc gl Mem st' gv' /\
    lookupEnv id' lc' gl' = Some gv') /\
(forall id' gv',  
  lookupEnv id' lc' gl' = Some gv' ->
  exists st',
    binds id' st' sstate'.(STerms) /\
    sterm_denotes_genericvalue TD lc gl Mem st' gv'
).

Definition sstate_denotes_state TD lc gl Mem sstate' lc' gl' mem' :=
smap_denotes_gvmap TD lc gl Mem sstate' lc' gl' /\
smem_denotes_mem TD lc gl Mem sstate'.(SMem) mem'.

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

Lemma genericvalue__implies__value2Sterm_denotes : forall TD lc0 gl0 Mem0 sstate1 lc gl v gv,
  uniq (STerms sstate1) ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 sstate1 lc gl ->
  getOperandValue TD v lc gl = Some gv ->
  sterm_denotes_genericvalue TD lc0 gl0 Mem0 (value2Sterm (STerms sstate1) v) gv.
Proof.
  intros D lc0 gl0 Mem0 sstate1 lc gl v gv Huniq Hdenotes J.
  unfold getOperandValue in J.
  unfold smap_denotes_gvmap in Hdenotes.
  destruct Hdenotes as [J1 J2].
  destruct v.
    apply J2 in J.
    destruct J as [st0 [J3 J4]].
    rewrite id2Sterm_in with (st0:=st0); auto.

    rewrite const2Sterm; auto.
Qed.

Lemma se_cmd__denotes__op_cmd__case1 : forall lc gl i0 gv3 lc' gl' id' st' sstate1 TD lc0 gl0 Mem0,
  updateEnv lc gl i0 gv3 = (lc', gl') ->
  i0 <> id' ->
  binds id' st' (STerms sstate1) ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 sstate1 lc gl ->
  exists gv',
    sterm_denotes_genericvalue TD lc0 gl0 Mem0 st' gv' /\
    lookupEnv id' lc' gl' = Some gv'.
Proof.
  intros lc gl i0 gv3 lc' gl' id' st' sstate1 TD lc0 gl0 Mem0 H25 nEQ Hbinds Hsterm_denotes.
  apply lookupEnv_updateEnv_neq with (id1:=id') in H25; auto.
  rewrite <- H25. 
  unfold smap_denotes_gvmap in Hsterm_denotes.
  destruct Hsterm_denotes as [J1 J2].
  apply J1 in Hbinds.
  destruct Hbinds as [gv' [J3 J4]].
  exists gv'. split; auto.
Qed.

Lemma se_cmd__denotes__op_cmd__case2 : forall lc gl i0 gv3 lc' gl' id' sstate1 TD lc0 gl0 Mem0 gv' st0,
  updateEnv lc gl i0 gv3 = (lc', gl') ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 sstate1 lc gl ->
  lookupEnv id' lc' gl' = Some gv' ->
  id' <> i0 ->
  exists st', binds id' st' (updateSmap (STerms sstate1) i0 st0) /\ 
              sterm_denotes_genericvalue TD lc0 gl0 Mem0 st' gv'.
Proof.
  intros lc gl i0 gv3 lc' gl' id' sstate1 TD lc0 gl0 Mem0 gv' st0 H25 Hsterm_denotes HlookupEnv n.
  apply lookupEnv_updateEnv_neq with (id1:=id') in H25; auto.
  rewrite <- H25 in HlookupEnv.
  destruct Hsterm_denotes as [J1 J2].
  apply J2 in HlookupEnv; auto.
  destruct HlookupEnv as [st' [J3 J4]].
  exists st'. split; auto.
    apply binds_updateSmap_neq; auto.
Qed.

Lemma genericvalues__imply__value2Sterm_denote : forall l0 TD lc0 gl0 Mem0 sstate1 lc gl gvs0,
  uniq (STerms sstate1) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 sstate1 lc gl ->
  values2GVs TD l0 lc gl = Some gvs0 ->
  sterms_denote_genericvalues TD lc0 gl0 Mem0 
    (List.map (value2Sterm (STerms sstate1)) l0) gvs0.
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

Lemma se_cmd__denotes__op_cmd : forall S TD Ps F B c cs call0 sbs tmn lc arg als ECs gl lc0 gl0 Mem0 lc' als' gl' Mem1 Mem2 sstate1 tr,
  dbCmd (mkState S TD Ps ((mkEC F B ((subblock_intro (c::cs) call0)::sbs) tmn lc arg als)::ECs) gl Mem1)
         (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc' arg als')::ECs) gl' Mem2)
         tr -> 
  uniq sstate1.(STerms) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  sstate_denotes_state TD lc0 gl0 Mem0 sstate1 lc gl Mem1 ->
  sstate_denotes_state TD lc0 gl0 Mem0 (se_cmd sstate1 c) lc' gl' Mem2.
Proof.
  intros S TD Ps F B c cs call0 sbs tmn lc arg0 als ECs gl lc0 gl0 Mem0 lc' als' gl' Mem1 Mem2 sstate1 tr HdsInsn Huniq Hsub Hdenotes.
  (cmd_cases (destruct c;
              inversion HdsInsn; subst;
              destruct Hdenotes as [Hsterm_denotes Hsmem_denotes]) Case).
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

Lemma se_cmd_uniq : forall sstate0 c,
  uniq (STerms sstate0) ->
  uniq (STerms (se_cmd sstate0 c)).
Proof.
  intros sstate0 c Huniq.
  destruct c; simpl; try solve [apply updateSmap_uniq; auto | auto].
Qed.

Lemma se_cmd_dom_mono : forall sstate0 c,
  dom (STerms sstate0) [<=] dom (STerms (se_cmd sstate0 c)).
Proof.
  intros sstate0 c.
  assert (forall sm id0 st0, dom sm [<=] dom (updateSmap sm id0 st0)) as J.
    intros. assert (J:=@updateSmap_dom_eq sm id0 st0). fsetdec. 
  destruct c; simpl; try solve [eauto using J| fsetdec].
Qed.

Lemma aux__se_cmds__denotes__op_cmds : forall cs S TD Ps F B call0 sbs tmn lc0 arg als ECs gl0 Mem0 lc als' gl Mem1 sstate1 lc' gl' Mem2 tr,
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc arg als)::ECs) gl Mem1)
         (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc' arg als')::ECs) gl' Mem2)
         tr ->
  uniq sstate1.(STerms) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  sstate_denotes_state TD lc0 gl0 Mem0 sstate1 lc gl Mem1 ->
  sstate_denotes_state TD lc0 gl0 Mem0 (se_cmds sstate1 cs) lc' gl' Mem2.
Proof.
  induction cs; 
    intros S TD Ps F B call0 sbs tmn lc0 arg0 als ECs gl0 Mem0 lc als' gl Mem1 sstate1 lc' gl' Mem2 tr HdbCmds Huniq Hsub Hdenotes.

    inversion HdbCmds; subst; auto.
      inversion H.

    inversion HdbCmds; subst.
    assert (Hcmd:=H).
    apply dbCmd_inversion in H.
    destruct H as [lc3 [gl3 [als3 [Mem3 H]]]]; subst.
    simpl.
    apply se_cmd__denotes__op_cmd with (lc0:=lc0)(gl0:=gl0)(sstate1:=sstate1)(Mem0:=Mem0) in Hcmd; auto.
    apply IHcs with (lc0:=lc0)(gl0:=gl0)(sstate1:=se_cmd sstate1 a)(Mem0:=Mem0) in H0; auto.
      apply se_cmd_uniq; auto.

      assert (J:=@se_cmd_dom_mono sstate1 a).
      clear - J Hsub. fsetdec.
Qed.

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

Lemma se_cmds__denotes__op_cmds : forall S TD Ps F B cs call0 sbs tmn lc arg als ECs gl Mem lc' als' gl' Mem' tr,
  uniq gl ->
  uniq lc ->
  dbCmds (mkState S TD Ps ((mkEC F B ((subblock_intro cs call0)::sbs) tmn lc arg als)::ECs) gl Mem)
         (mkState S TD Ps ((mkEC F B ((subblock_intro nil call0)::sbs) tmn lc' arg als')::ECs) gl' Mem')
         tr ->
  sstate_denotes_state TD lc gl Mem (se_cmds (mkSstate (env_to_smap gl lc) smem_init) cs) lc' gl' Mem'.
Proof.
  intros S TD Ps F B cs call0 sbs tmn lc arg0 als ECs gl Mem0 lc' als' gl' Mem' tr Uniqg Uniqc HdbCmds.
  apply aux__se_cmds__denotes__op_cmds with (lc0:=lc)(gl0:=gl)(Mem0:=Mem0)(sstate1:=mkSstate (env_to_smap gl lc) smem_init) in HdbCmds; simpl; auto.
    apply env_to_smap_uniq.

    rewrite env_to_smap_dom_eq. fsetdec.

    split; simpl; auto.
      unfold smap_denotes_gvmap.
      split; intros.
        apply env_to_smap_denotes__imples__gv; auto.

        exists (sterm_val (value_id id')).
        apply gv__imples__env_to_smap_denotes; auto.
Qed.           

Definition se_subblock (st : sstate) (b:subblock) : sstate*scall :=
match b with
| subblock_intro cs call0 =>
  let st0 := se_cmds st cs in
  (st0, se_call st0 call0)
end.

Definition tv_subblock (b1 b2:subblock) :=
match (b1, b2) with
| (subblock_intro cs1 call1, subblock_intro cs2 call2) =>
  match (call1, call2) with
  | (insn_call id1 _ _ _ _ _, insn_call id2 _ _ _ _ _) => 
    if id1==id2 
    then
      let st1 := se_cmds (mkSstate nil smem_init) cs1 in
      let st2 := se_cmds (mkSstate nil smem_init) cs2 in
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

Lemma sterm_denotes_genericvalue_det : forall TD lc gl Mem0 st0 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv2 ->
  gv1 = gv2.
Admitted.

Lemma value2Sterm_denotes__implies__genericvalue : forall TD lc0 gl0 Mem0 sstate1 lc gl v gv,
  uniq (STerms sstate1) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 sstate1 lc gl ->
  sterm_denotes_genericvalue TD lc0 gl0 Mem0 (value2Sterm (STerms sstate1) v) gv ->
  getOperandValue TD v lc gl = Some gv.
Proof.
  intros D lc0 gl0 Mem0 sstate1 lc gl v gv Huniq Hsub Hdenotes J.
  unfold smap_denotes_gvmap in Hdenotes.
  destruct Hdenotes as [J1 J2].
  destruct v.
    destruct (@AtomSetProperties.In_dec i0 (dom sstate1.(STerms))) as [i0_in_sstate1 | i0_notin_sstate1].
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

Lemma value2Sterm_denote__imply__genericvalues : forall l0 TD lc0 gl0 Mem0 sstate1 lc gl gvs0,
  uniq (STerms sstate1) ->
  (dom lc0 `union` dom gl0) [<=] dom (STerms sstate1) ->
  smap_denotes_gvmap TD lc0 gl0 Mem0 sstate1 lc gl ->
  sterms_denote_genericvalues TD lc0 gl0 Mem0 
    (List.map (value2Sterm (STerms sstate1)) l0) gvs0 ->
  values2GVs TD l0 lc gl = Some gvs0.
Proof.
  induction l0; intros; simpl in *.
    inversion H2; subst; auto.

    inversion H2; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    rewrite H11.
    erewrite IHl0; eauto.
Qed.


End SimpleSE.

