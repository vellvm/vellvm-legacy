Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.

Module LLVMopsem.

Export LLVMsyntax.
Export LLVMlib.
Export LLVMgv.
Export LLVMtd.

(**************************************)
(** Execution contexts *)

Record ExecutionContext : Type := mkEC {
CurFunction : fdef;
CurBB       : block;
CurCmds     : cmds;              (* cmds to run within CurBB *)
Terminator  : terminator;
Locals      : GVMap;                 (* LLVM values used in this invocation *)
Allocas     : list mblock            (* Track memory allocated by alloca *)
}.

Definition ECStack := list ExecutionContext.

(* FunTable maps function names to their addresses that are taken as function 
   pointers. When we are calling a function via an id, we first search in Globals
   via the value id to get its address, and then search in FunTable to get its
   name, via the name, we search in CurProducts to get its definition.

   We assume that there is an 'initFunTable' that returns function addresses to
   initialize FunTable
*)
Record State : Type := mkState {
CurSystem          : system;
CurTargetData      : TargetData;
CurProducts        : list product;
ECS                : ECStack;
Globals            : GVMap;
FunTable           : GVMap;
Mem                : mem
}.

Inductive wfState : State -> Prop :=
| wfState_intro : forall state los nts ,
  state.(CurTargetData) = (los, nts) ->
  In (module_intro los nts state.(CurProducts)) state.(CurSystem) ->
  wfState state
.

Inductive wfExecutionContext : ExecutionContext -> Prop :=
| wfExecutionContext_intro : forall EC fh lb l lp lc tmn,
  EC.(CurFunction) = fdef_intro fh lb ->
  In EC.(CurBB) lb ->
  EC.(CurBB) = block_intro l lp lc tmn ->
  (exists done, done++EC.(CurCmds)=lc) ->
  wfExecutionContext EC
.

Inductive wfECStack : ECStack -> Prop :=
| wfECStack_nil : wfECStack nil
| wfECStack_cons : forall EC ECS,
  wfExecutionContext EC ->
  wfECStack ECS ->
  wfECStack (EC::ECS)
.

Inductive wfContexts : State -> Prop :=
| wfContexts_intro : forall ECS s td ps g fs mem,
  wfECStack ECS ->
  wfContexts (mkState s td ps ECS g fs mem)
.

(**************************************)
(** switchToNewBasicBlock *)

(* This function is used by switchToNewBasicBlock, which only checks local 
   variables (from PHI) *)
Fixpoint getIncomingValuesForBlockFromPHINodes (TD:TargetData)
  (PNs:list phinode) (b:block) (globals locals:GVMap) : 
  option (list (id*GenericValue)) :=
match PNs with
| nil => Some nil
| (insn_phi id0 t vls)::PNs => 
  match (getValueViaBlockFromPHINode (insn_phi id0 t vls) b) with
  | None => None
  | Some v => 
      match (getOperandValue TD v locals globals, 
             getIncomingValuesForBlockFromPHINodes TD PNs b globals locals)
      with
      | (Some gv1, Some idgvs) => Some ((id0,gv1)::idgvs)
      | _ => None
      end               
  end
end.

(* This function is used by switchToNewBasicBlock, which only updates local 
   variables (from PHI) *)
Fixpoint updateValuesForNewBlock (ResultValues:list (id*GenericValue)) 
  (locals:GVMap) : GVMap :=
match ResultValues with
| nil => locals
| (id, v)::ResultValues' => 
    updateAddAL _ (updateValuesForNewBlock ResultValues' locals) id v
end.

(*
  SwitchToNewBasicBlock - This method is used to jump to a new basic block.
  This function handles the actual updating of block and instruction iterators
  as well as execution of all of the PHI nodes in the destination block.
 
  This method does this because all of the PHI nodes must be executed
  atomically, reading their inputs before any of the results are updated.  Not
  doing this can cause problems if the PHI nodes depend on other PHI nodes for
  their inputs.  If the input PHI node is updated before it is read, incorrect
  results can happen.  Thus we use a two phase approach.

  It only checks and update local variables. I don't think PHInode can refer to
  a global. !!!
*)
Definition switchToNewBasicBlock (TD:TargetData) (Dest:block) 
  (PrevBB:block) (globals locals:GVMap): option GVMap :=
  let PNs := getPHINodesFromBlock Dest in
  match getIncomingValuesForBlockFromPHINodes TD PNs PrevBB globals locals with
  | Some ResultValues => Some (updateValuesForNewBlock ResultValues locals)
  | None => None
  end.

(**************************************)
(* To realize it in LLVM, we can try to dynamically cast fptr to Function*, 
   if failed, return None
   if successeful, we can return this function's name *)
Fixpoint lookupFdefViaGVFromFunTable (fs:GVMap) (fptr:GenericValue) : option id 
  :=
match fs with
| nil => None
| (id0,gv0)::fs' => 
  if eq_gv gv0 fptr
  then Some id0 
  else lookupFdefViaGVFromFunTable fs' fptr
end.

(* For each function id, the runtime emits an address as a function pointer. 
   It can be realized by taking Function* in LLVM as the address. *)
Axiom initFunTable : mem -> id -> option GenericValue.

Definition lookupFdefViaGV (TD:TargetData) (Ps:products) (gl lc:GVMap) 
  (fs:GVMap) (fv:value) : option fdef :=
do fptr <- getOperandValue TD fv lc gl;
do fn <- lookupFdefViaGVFromFunTable fs fptr;
   lookupFdefViaIDFromProducts Ps fn
.

(**************************************)
(* Realized by libffi in LLVM *)
Axiom callExternalFunction : mem -> id -> list GenericValue -> 
  option ((option GenericValue)*mem).

Definition lookupExFdecViaGV (TD:TargetData) (Ps:products) (gl lc:GVMap)
  (fs:GVMap) (fv:value) : option fdec :=
do fptr <- getOperandValue TD fv lc gl;
do fn <- lookupFdefViaGVFromFunTable fs fptr;
    match lookupFdefViaIDFromProducts Ps fn with 
    | Some _ => None
    | None => lookupFdecViaIDFromProducts Ps fn
    end
.

Definition exCallUpdateLocals TD ft (noret:bool) (rid:id) 
  (oResult:option GenericValue) (lc :GVMap) : option GVMap :=
  match noret with
  | false =>
      match oResult with
      | None => None
      | Some Result => 
          match ft with
          | typ_function t _ _ => 
            match fit_gv TD Result t with
            | Some gr => Some (updateAddAL _ lc rid (? gr # t ?))
            | _ => None
            end
          | _ => None
          end
      end
  | true => Some lc
  end.

(***************************************************************)
(* deterministic small-step *)

Definition returnUpdateLocals (TD:TargetData) (c':cmd) (Result:value) 
  (lc lc' gl:GVMap) : option GVMap :=
  match (getOperandValue TD Result lc gl) with
  | Some gr =>    
      match c' with
      | insn_call id0 false _ t _ _ => 
        match t with
        | typ_function ct _ _ =>
          match fit_gv TD gr ct with
          | Some gr' => Some (updateAddAL _ lc' id0 (? gr' # ct ?))
          | _ => None
          end
        | _ => None
        end
      | insn_call _ _ _ _ _ _ => Some lc'
      | _=> None
      end
  | None => None
  end.

Inductive dsInsn : State -> State -> trace -> Prop :=
| dsReturn : forall S TD Ps F B rid RetTy Result lc gl fs
                            F' B' c' cs' tmn' lc' EC
                            Mem Mem' als als' lc'',   
  Instruction.isCallInst c' = true ->
  (* FIXME: we should get Result before free?! *)
  free_allocas TD Mem als = Some Mem' ->
  returnUpdateLocals TD c' Result lc lc' gl = Some lc'' ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_return rid RetTy Result) lc als)::
                      (mkEC F' B' (c'::cs') tmn' lc' als')::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC F' B' cs' tmn' lc'' als')::EC) gl fs Mem')
    trace_nil 

| dsReturnVoid : forall S TD Ps F B rid lc gl fs
                            F' B' c' tmn' lc' EC
                            cs' Mem Mem' als als',   
  Instruction.isCallInst c' = true ->
  free_allocas TD Mem als = Some Mem' ->
  getCallerReturnID c' = None ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_return_void rid) lc als)::
                      (mkEC F' B' (c'::cs') tmn' lc' als')::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC F' B' cs' tmn' lc' als')::EC) gl fs Mem')
    trace_nil 

| dsBranch : forall S TD Ps F B lc gl fs bid Cond l1 l2 c
                              l' ps' cs' tmn' lc' EC Mem als,   
  getOperandValue TD Cond lc gl = Some c ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  dsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br bid Cond l1 l2) lc als)::EC) 
                       gl fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' als)
                       ::EC) gl fs Mem)
    trace_nil 

| dsBranch_uncond : forall S TD Ps F B lc gl fs bid l 
                           l' ps' cs' tmn' lc' EC Mem als,   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  dsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br_uncond bid l) lc als)::EC) 
                       gl fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' als)
                       ::EC) gl fs Mem)
    trace_nil 

| dsBop: forall S TD Ps F B lc gl fs id bop sz v1 v2 gv3 EC cs tmn Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gv3 ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                      gl fs Mem)
    trace_nil 

| dsFBop: forall S TD Ps F B lc gl fs id fbop fp v1 v2 gv3 EC cs tmn Mem als,
  FBOP TD lc gl fbop fp v1 v2 = Some gv3 ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                      gl fs Mem)
    trace_nil 

| dsExtractValue : forall S TD Ps F B lc gl fs id t v gv gv' idxs EC cs tmn 
                          Mem als,
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_extractvalue id t v idxs)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv') als)::EC) 
                       gl fs Mem)
    trace_nil 

| dsInsertValue : forall S TD Ps F B lc gl fs id t v t' v' gv gv' gv'' idxs 
                         EC cs tmn Mem als,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_insertvalue id t v t' v' idxs)::cs) tmn 
                       lc als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv'') als)::EC) 
                       gl fs Mem)
    trace_nil 

| dsMalloc : forall S TD Ps F B lc gl fs id t v gn align EC cs tmn Mem als 
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_malloc id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id (blk2GV TD mb)) 
                      als)::EC) gl fs Mem')
    trace_nil

| dsFree : forall S TD Ps F B lc gl fs fid t v EC cs tmn Mem als Mem' mptr,
  getOperandValue TD v lc gl = Some mptr ->
  free TD Mem mptr = Some Mem'->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_free fid t v)::cs) tmn lc als)::EC) 
                       gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) gl fs Mem')
    trace_nil

| dsAlloca : forall S TD Ps F B lc gl fs id t v gn align EC cs tmn Mem als 
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_alloca id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id (blk2GV TD mb)) 
                      (mb::als))::EC) gl fs Mem')
    trace_nil

| dsLoad : forall S TD Ps F B lc gl fs id t align v EC cs tmn Mem als mp gv,
  getOperandValue TD v lc gl = Some mp ->
  mload TD Mem mp t align = Some gv ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_load id t v align)::cs) tmn lc als)::
                       EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv) als)::EC) gl 
                       fs Mem)
    trace_nil

| dsStore : forall S TD Ps F B lc gl fs sid t align v1 v2 EC cs tmn Mem als 
                   mp2 gv1 Mem',
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some mp2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_store sid t v1 v2 align)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) gl fs Mem')
    trace_nil

| dsGEP : forall S TD Ps F B lc gl fs id inbounds t v idxs vidxs EC mp mp' 
                 cs tmn Mem als t',
  getOperandValue TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxs ->
  getGEPTyp idxs t = ret t' ->
  GEP TD t mp vidxs inbounds t' = Some mp' ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_gep id inbounds t v idxs)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id mp') als)::EC) 
                       gl fs Mem)
    trace_nil 

| dsTrunc : forall S TD Ps F B lc gl fs id truncop t1 v1 t2 gv2 EC cs tmn 
                   Mem als,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gv2 ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                       gl fs Mem)
    trace_nil

| dsExt : forall S TD Ps F B lc gl fs id extop t1 v1 t2 gv2 EC cs tmn Mem 
                 als,
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                       gl fs Mem)
    trace_nil

| dsCast : forall S TD Ps F B lc gl fs id castop t1 v1 t2 gv2 EC cs tmn Mem 
                  als,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_cast id castop t1 v1 t2)::cs) tmn lc 
                      als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                      gl fs Mem)
    trace_nil

| dsIcmp : forall S TD Ps F B lc gl fs id cond t v1 v2 gv3 EC cs tmn Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem)
    trace_nil

| dsFcmp : forall S TD Ps F B lc gl fs id fcond fp v1 v2 gv3 EC cs tmn Mem 
                  als,
  FCMP TD lc gl fcond fp v1 v2 = Some gv3 ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem)
    trace_nil

| dsSelect : forall S TD Ps F B lc gl fs id v0 t v1 v2 c EC cs tmn Mem als 
                    gv1 gv2,
  getOperandValue TD v0 lc gl = Some c ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (if isGVZero TD c 
                                        then updateAddAL _ lc id gv2 
                                        else updateAddAL _ lc id gv1) als)
                      ::EC) gl fs Mem)
    trace_nil

| dsCall : forall S TD Ps F B lc gl fs rid noret ca fid fv lp cs tmn
                          lc' l' ps' cs' tmn' EC rt la va lb Mem als ft fa gvs,
  (* only look up the current module for the time being, 
     do not support linkage. *)
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc' ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                       (block_intro l' ps' cs' tmn') cs' tmn' 
                       lc'
                       nil)::
                      (mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem)
    trace_nil 

| dsExCall : forall S TD Ps F B lc gl fs rid noret ca fid fv lp cs tmn EC 
                    rt la Mem als oresult Mem' lc' va ft fa gvs,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  lookupExFdecViaGV TD Ps gl lc fs fv = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  params2GVs TD lp lc gl = Some gvs ->
  callExternalFunction Mem fid gvs = Some (oresult, Mem') ->
  exCallUpdateLocals TD ft noret rid oresult lc = Some lc' ->
  dsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC F B cs tmn lc' als)::EC) gl fs Mem')
    trace_nil 
.

Definition initGlobal (TD:TargetData)(gl:GVMap)(Mem:mem)(id0:id)(t:typ)(c:const)
  (align0:align) : option (GenericValue*mem) :=
  do tsz <- getTypeAllocSize TD t;
  do gv <- const2GV TD gl c;
     match (malloc_one TD Mem (Size.from_nat tsz) align0) with
     | Some (Mem', mb) =>
       do Mem'' <- mstore TD Mem' (blk2GV TD mb) t gv align0;
       ret (blk2GV TD mb,  Mem'')
     | None => None
     end.

Definition initTargetData (los:layouts)(nts:namedts)(Mem:mem) : TargetData := 
  (los, nts).

Axiom getExternalGlobal : mem -> id -> option GenericValue.

Fixpoint genGlobalAndInitMem (TD:TargetData)(Ps:list product)(gl:GVMap)(fs:GVMap)
  (Mem:mem) : option (GVMap*GVMap*mem) :=
match Ps with
| nil => Some (gl, fs, Mem)
| (product_gvar (gvar_intro id0 _ spec t c align))::Ps' => 
  match (initGlobal TD gl Mem id0 t c align) with
  | Some (gv, Mem') => 
      genGlobalAndInitMem TD Ps' (updateAddAL _ gl id0 gv) fs Mem'
  | None => None
  end
| (product_gvar (gvar_external id0 spec t))::Ps' => 
  match (getExternalGlobal Mem id0) with
  | Some gv => genGlobalAndInitMem TD Ps' (updateAddAL _ gl id0 gv) fs Mem
  | None => None
  end
| (product_fdef (fdef_intro (fheader_intro _ _ id0 _ _) _))::Ps' =>
  match initFunTable Mem id0 with
  | Some gv => genGlobalAndInitMem TD Ps' (updateAddAL _ gl id0 gv) 
      (updateAddAL _ fs id0 gv) Mem
  | None => None
  end
| (product_fdec (fdec_intro (fheader_intro _ _ id0 _ _)))::Ps' =>
  match initFunTable Mem id0 with
  | Some gv => genGlobalAndInitMem TD Ps' (updateAddAL _ gl id0 gv) 
      (updateAddAL _ fs id0 gv) Mem
  | None => None
  end
end.

Definition ds_genInitState (S:system) (main:id) (Args:list GenericValue) (initmem:mem) : option State :=
match (lookupFdefViaIDFromSystem S main) with
| None => None
| Some CurFunction =>
  match (getParentOfFdefFromSystem CurFunction S) with
  | None => None
  | Some (module_intro CurLayouts CurNamedts CurProducts) =>
    let initargetdata := initTargetData CurLayouts CurNamedts initmem in 
    match (genGlobalAndInitMem initargetdata CurProducts nil nil initmem) with
    | None => None
    | Some (initGlobal, initFunTable, initMem) =>
      match (getEntryBlock CurFunction) with
      | None => None
      | Some (block_intro l ps cs tmn) => 
          match CurFunction with 
          | fdef_intro (fheader_intro _ rt _ la _) _ =>
            match initLocals initargetdata la Args with
            | Some Values =>
              Some
              (mkState
                S
                initargetdata
                CurProducts
                ((mkEC
                  CurFunction 
                  (block_intro l ps cs tmn) 
                  cs
                  tmn
                  Values 
                  nil
                )::nil)
                initGlobal
                initFunTable
                initMem
              )
            | None => None
            end
        end
      end
    end
  end
end.

Definition ds_isFinialState (state:State) : bool :=
match state with
| (mkState _ _ _ ((mkEC _ _ nil (insn_return_void _) _ _)::nil) _ _ _) => true
| (mkState _ _ _ ((mkEC _ _ nil (insn_return _ _ _) _ _)::nil) _ _ _) => true 
| _ => false
end.

Inductive dsop_star : State -> State -> trace -> Prop :=
| dsop_star_nil : forall state, dsop_star state state trace_nil
| dsop_star_cons : forall state1 state2 state3 tr1 tr2,
    dsInsn state1 state2 tr1 ->
    dsop_star state2 state3 tr2 ->
    dsop_star state1 state3 (trace_app tr1 tr2)
.

Inductive dsop_plus : State -> State -> trace -> Prop :=
| dsop_plus_cons : forall state1 state2 state3 tr1 tr2,
    dsInsn state1 state2 tr1 ->
    dsop_star state2 state3 tr2 ->
    dsop_plus state1 state3 (trace_app tr1 tr2)
.

CoInductive dsop_diverges : State -> Trace -> Prop :=
| dsop_diverges_intro : forall state1 state2 tr1 tr2,
    dsop_plus state1 state2 tr1 ->
    dsop_diverges state2 tr2 ->
    dsop_diverges state1 (Trace_app tr1 tr2)
.

Inductive ds_converges : system -> id -> list GenericValue -> State -> Prop :=
| ds_converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) 
                              (IS FS:State) tr,
  ds_genInitState s main VarArgs Mem.empty = Some IS ->
  dsop_star IS FS tr ->
  ds_isFinialState FS ->
  ds_converges s main VarArgs FS
.

Inductive ds_diverges : system -> id -> list GenericValue -> Trace -> Prop :=
| ds_diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) 
                             (IS:State) tr,
  ds_genInitState s main VarArgs Mem.empty = Some IS ->
  dsop_diverges IS tr ->
  ds_diverges s main VarArgs tr
.

Inductive ds_goeswrong : system -> id -> list GenericValue -> State -> Prop :=
| ds_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) 
                              (IS FS:State) tr,
  ds_genInitState s main VarArgs Mem.empty = Some IS ->
  dsop_star IS FS tr ->
  ~ ds_isFinialState FS ->
  ds_goeswrong s main VarArgs FS
.

(***************************************************************)
(* non-deterministic small-step *)

(* List may contain duplicated states, set is better, because we need
   an equalivance relation between State*trace.
*)
Definition States := list (State*trace).

Inductive wfStates : States -> Prop :=
| wfStates_nil : wfStates nil
| wfStates_cons : forall state te states,
  wfState state ->
  wfStates states ->
  wfStates ((state, te)::states)
.

Inductive nsInsn : State*trace -> States -> Prop :=
| nsReturn : forall S TD Ps F B rid RetTy Result lc gl fs
                            F' B' c' cs' tmn' lc' EC
                            tr Mem Mem' als als' lc'',   
  Instruction.isCallInst c' = true ->  
  free_allocas TD Mem als = Some Mem' ->
  returnUpdateLocals TD c' Result lc lc' gl = Some lc'' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_return rid RetTy Result) lc als)::
                      (mkEC F' B' (c'::cs') tmn' lc' als')::EC) gl fs Mem, 
                       tr)
    ((mkState S TD Ps ((mkEC F' B' cs' tmn' lc'' als')::EC) gl fs Mem', tr)
                       ::nil)

| nsReturnVoid : forall S TD Ps F B lc gl fs rid
                            F' B' c' lc' EC
                            cs' tmn' Mem Mem' als als' tr,   
  Instruction.isCallInst c' = true ->
  free_allocas TD Mem als = Some Mem' ->
  getCallerReturnID c' = None ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_return_void rid) lc als)::
                      (mkEC F' B' (c'::cs') tmn' lc' als')::EC) gl fs Mem, 
                       tr)
    ((mkState S TD Ps ((mkEC F' B' cs' tmn' lc' als')::EC) gl fs Mem', tr)::
                        nil)

| nsBranch_def : forall S TD Ps F B lc gl fs bid Cond l1 l2 c
                              l' ps' cs' tmn' EC tr Mem als lc',   
  getOperandValue TD Cond lc gl = Some c ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  nsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br bid Cond l1 l2) lc als)::EC) gl
                      fs Mem, tr)
    ((mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' 
                        als)::EC) gl fs Mem, tr)::nil)

| nsBranch_undef : forall S TD Ps F B lc bid Cond l1 l2
                              l1' ps1' cs1' tmn1' 
                              l2' ps2' cs2' tmn2' EC gl fs tr Mem als lc1' lc2', 
  isOperandUndef TD (typ_int Size.One) Cond lc gl ->
  Some (block_intro l1' ps1' cs1' tmn1') = lookupBlockViaLabelFromFdef F l1 ->
  Some (block_intro l2' ps2' cs2' tmn2') = lookupBlockViaLabelFromFdef F l2 ->
  switchToNewBasicBlock TD (block_intro l1' ps1' cs1' tmn1') B gl lc = 
    Some lc1' ->
  switchToNewBasicBlock TD (block_intro l2' ps2' cs2' tmn2') B gl lc =
    Some lc2' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br bid Cond l1 l2) lc als)::EC) gl 
                       fs Mem, tr)
    ((mkState S TD Ps ((mkEC F (block_intro l1' ps1' cs1' tmn1') cs1' tmn1' 
                         lc1' als)::EC) gl fs Mem, tr)::
     (mkState S TD Ps ((mkEC F (block_intro l2' ps2' cs2' tmn2') cs2' tmn2' 
                         lc2' als)::EC) gl fs Mem, tr)::nil)

| nsBranch_uncond : forall S TD Ps F B lc gl fs bid l
                              l' ps' cs' tmn' EC tr Mem als lc',   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc=Some lc'->
  nsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br_uncond bid l) lc als)::EC) gl fs
                       Mem, tr)
    ((mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc'
                         als)::EC) gl fs Mem, tr)::nil)

| nsBop : forall S TD Ps F B lc gl fs id bop sz v1 v2 gv3 EC cs tmn tr Mem 
                 als,
  BOP TD lc gl bop sz v1 v2 = Some gv3 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc als)
      ::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
      gl fs Mem, tr)::nil)

| nsFBop : forall S TD Ps F B lc gl fs id fbop fp v1 v2 gv3 EC cs tmn tr Mem 
                  als,
  FBOP TD lc gl fbop fp v1 v2 = Some gv3 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc 
                       als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                        gl fs Mem, tr)::nil)

| nsExtractValue : forall S TD Ps F B lc gl fs id t v gv gv' idxs EC cs tmn 
                          Mem als tr,
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_extractvalue id t v idxs)::cs) tmn lc
                       als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv') als)::EC) 
                        gl fs Mem, tr)::nil)

| nsInsertValue : forall S TD Ps F B lc gl fs id t v t' v' gv gv' gv'' idxs 
                         EC cs tmn Mem als tr,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_insertvalue id t v t' v' idxs)::cs) tmn 
                       lc als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv'') als)::EC)
                        gl fs Mem, tr)::nil)

| nsMalloc : forall S TD Ps F B lc gl fs id t v gn align EC cs tmn Mem als 
                    Mem' tsz mb tr,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_malloc id t v align)::cs) tmn lc als)
                       ::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id (blk2GV TD mb))
                        als)::EC) gl fs Mem', tr)::nil)

| nsFree : forall S TD Ps F B lc gl fs fid t v EC cs tmn Mem als Mem' mptr 
                  tr,
  getOperandValue TD v lc gl = Some mptr ->
  free TD Mem mptr = Some Mem'->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_free fid t v)::cs) tmn lc als)::EC) 
                       gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) gl fs Mem', tr)::nil)

| nsAlloca : forall S TD Ps F B lc gl fs id t v gn align EC cs tmn Mem als 
                    Mem' tsz mb tr,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_alloca id t v align)::cs) tmn lc als)
                       ::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id (blk2GV TD mb))
                       (mb::als))::EC) gl fs Mem', tr)::nil)

| nsLoad : forall S TD Ps F B lc gl fs id t v align EC cs tmn Mem als mp gv 
                  tr,
  getOperandValue TD v lc gl = Some mp ->
  mload TD Mem mp t align = Some gv ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_load id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv) als)::EC) 
                       gl fs Mem, tr)::nil)

| nsStore : forall S TD Ps F B lc gl fs sid t v1 v2 align EC cs tmn Mem als 
                   mp2 gv1 Mem' tr,
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some mp2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_store sid t v1 v2 align)::cs) tmn lc 
                      als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) gl fs Mem', tr)::nil)

| nsGEP : forall S TD Ps F B lc gl fs id inbounds t v idxs vidxs EC mp mp' 
                 cs tmn Mem als tr t',
  getOperandValue TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxs ->
  getGEPTyp idxs t = ret t' ->
  GEP TD t mp vidxs inbounds t' = Some mp' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_gep id inbounds t v idxs)::cs) tmn lc
                       als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id mp') als)::EC) 
                       gl fs Mem, tr)::nil)

| nsTrunc : forall S TD Ps F B lc gl fs id truncop t1 v1 t2 gv2 EC cs tmn 
                   Mem als tr,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gv2 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc 
                       als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                       gl fs Mem, tr)::nil)
| nsExt : forall S TD Ps F B lc gl fs id extop t1 v1 t2 gv2 EC cs tmn Mem 
                 als tr,
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc
                       als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                       gl fs Mem, tr)::nil)

| nsCast : forall S TD Ps F B lc gl fs id castop t1 v1 t2 gv2 EC cs tmn Mem 
                  als tr,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_cast id castop t1 v1 t2)::cs) tmn lc 
                       als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                        gl fs Mem, tr)::nil)

| nsIcmp : forall S TD Ps F B lc gl fs id cond t v1 v2 gv3 EC cs tmn Mem als
                  tr,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem, tr)::nil)

| nsFcmp : forall S TD Ps F B lc gl fs id fcond fp v1 v2 gv3 EC cs tmn Mem 
                  als tr,
  FCMP TD lc gl fcond fp v1 v2 = Some gv3 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc 
                      als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem, tr)::nil)

| nsSelect : forall S TD Ps F B lc gl fs id v0 t v1 v2 c EC cs tmn Mem als 
                    tr gv1 gv2,
  getOperandValue TD v0 lc gl = Some c ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc als)
                       ::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn 
                         (if isGVZero TD c 
                          then updateAddAL _ lc id gv2 
                          else updateAddAL _ lc id gv1) als)::EC) 
                         gl fs Mem, tr)::nil)

| nsCall : forall S TD Ps F B lc gl fs rid noret fv fid lp cs tmn lc'
                fa ca l' ps' cs' tmn' EC rt id la va lb tr Mem als ft gvs,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                      lc als)::EC) gl fs Mem, tr)
    ((mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt id la va) lb) 
                       (block_intro l' ps' cs' tmn') cs' tmn' 
                         lc'
                         nil)::
                       (mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem, tr)::nil)

| nsExCall : forall S TD Ps F B lc gl fs rid noret ca fv fid lp cs tmn EC
                    rt la va Mem als tr oresult Mem' lc' ft fa gvs,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  lookupExFdecViaGV TD Ps gl lc fs fv = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  params2GVs TD lp lc gl = Some gvs ->
  callExternalFunction Mem fid gvs = Some (oresult, Mem') ->
  exCallUpdateLocals TD ft noret rid oresult lc = Some lc' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                      lc als)::EC) gl fs Mem, tr)
    ((mkState S TD Ps ((mkEC F B cs tmn lc' als)::EC) gl fs Mem', tr)::nil)
.

Definition ns_genInitState (S:system) (main:id) (Args:list GenericValue) 
  (initmem:mem) : option States :=
match (lookupFdefViaIDFromSystem S main) with
| None => None
| Some CurFunction =>
  match (getParentOfFdefFromSystem CurFunction S) with
  | None => None
  | Some (module_intro CurTD CurNamedts CurPs) =>
    let initargetdata := initTargetData CurTD CurNamedts initmem in 
    match (genGlobalAndInitMem initargetdata CurPs nil nil initmem) with
    | None => None
    | Some (initGlobal, initFunTable, initMem) =>
      match (getEntryBlock CurFunction) with
      | None => None
      | Some (block_intro l ps cs tmn) => 
          match CurFunction with 
          | fdef_intro (fheader_intro _ rt _ la _) _ =>
            match initLocals initargetdata la Args with
            | Some Values =>
              Some
               ((mkState
                 S
                 initargetdata
                 CurPs
                 ((mkEC
                   CurFunction 
                   (block_intro l ps cs tmn) 
                   cs
                   tmn
                   Values 
                   nil
                 )::nil)
                 initGlobal
                 initFunTable
                 initMem,
                 trace_nil
               )::nil)
            | None => None
            end
          end
      end
    end
  end
end.

Fixpoint ns_isFinialState (states:States) : bool :=
match states with
| (mkState _ _ _ ((mkEC _ _ nil (insn_return_void _) _ _)::nil) _ _ _, _)
    ::states' => true
| (mkState _ _ _ ((mkEC _ _ nil (insn_return _ _ _) _ _)::nil) _ _ _, _)
    ::states' => true
| (mkState _ _ _ _ _ _ _, _)::states' => ns_isFinialState states'
| _ => false
end.

Inductive nsop_star : States -> States -> Prop :=
| nsop_star_nil : forall states, nsop_star states states
| nsop_star_refl : forall state tr states states',
  nsop_star states states' ->
  nsop_star ((state, tr)::states) ((state, tr)::states')
| nsop_star_cons : forall state tr states states1 states2,
  nsInsn (state, tr) states1 ->
  nsop_star states states2 ->
  nsop_star ((state, tr)::states) (states1++states2)
| nsop_star_trans : forall states1 states2 states3,
  nsop_star states1 states2 ->
  nsop_star states2 states3 ->
  nsop_star states1 states3
.

Inductive nsop_plus : States -> States -> Prop :=
| nsop_plus_cons : forall state tr states states1 states2,
  nsInsn (state, tr) states1 ->
  nsop_star states states2 ->
  nsop_plus ((state, tr)::states) (states1++states2)
| nsop_plus_trans : forall states1 states2 states3,
  nsop_plus states1 states2 ->
  nsop_star states2 states3 ->
  nsop_plus states1 states3
.

CoInductive nsop_diverges : States -> list Trace -> Prop :=
| nsop_diverges_cons : forall state_tr states trs1 trs2,
  nsop_diverges (state_tr::nil) trs1 ->
  nsop_diverges states trs2 ->
  nsop_diverges (state_tr::states) (trs1++trs2)
| nsop_diverges_trans : forall states states' trs,
    nsop_plus states states' ->
    nsop_diverges states' trs ->
    nsop_diverges states trs
.

Inductive ns_converges : system -> id -> list GenericValue -> States -> Prop :=
| ns_converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) 
                              (IS FS:States),
  ns_genInitState s main VarArgs Mem.empty = Some IS ->
  nsop_star IS FS ->
  ns_isFinialState FS ->
  ns_converges s main VarArgs FS
.

Inductive ns_diverges : system -> id -> list GenericValue -> list Trace -> Prop 
  :=
| ns_diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) 
                             (IS:States) trs,
  ns_genInitState s main VarArgs Mem.empty = Some IS ->
  nsop_diverges IS trs ->
  ns_diverges s main VarArgs trs
.

Inductive ns_goeswrong : system -> id -> list GenericValue -> States -> Prop :=
| ns_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) 
                              (IS FS:States),
  ns_genInitState s main VarArgs Mem.empty = Some IS ->
  nsop_star IS FS ->
  ~ ns_isFinialState FS ->
  ns_goeswrong s main VarArgs FS
.

(***************************************************************)
(* deterministic big-step *)

Definition callUpdateLocals (TD:TargetData) ft (noret:bool) (rid:id) 
  (oResult:option value) (lc lc' gl:GVMap) : option GVMap :=
    match noret with
    | false =>
        match oResult with
        | None => None
        | Some Result => 
          match getOperandValue TD Result lc' gl with 
          | Some gr =>  
            match ft with
            | typ_function t _ _ => 
              match fit_gv TD gr t with
              | Some gr' => Some (updateAddAL _ lc rid (? gr' # t ?))
              | None => None
              end
            | _ => None
            end
          | None => None
          end
        end
    | true => 
        match oResult with
        | None => Some lc
        | Some Result => 
          match (getOperandValue TD Result lc' gl) with 
          | Some gr => Some lc
          | None => None
          end
        end
    end.

Inductive dbInsn : State -> State -> trace -> Prop :=
| dbBranch : forall S TD Ps F B lc gl fs bid Cond l1 l2 c
                              l' ps' cs' tmn' EC Mem als lc',   
  getOperandValue TD Cond lc gl = Some c ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  dbInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br bid Cond l1 l2) lc als)::EC) gl 
                       fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' als)
                       ::EC) gl fs Mem)
    trace_nil 

| dbBranch_uncond : forall S TD Ps F B lc gl fs l bid
                              l' ps' cs' tmn' EC Mem als lc',   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  dbInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br_uncond bid l) lc als)::EC) gl 
                      fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' als)
                       ::EC) gl fs Mem)
    trace_nil 

| dbBop : forall S TD Ps F B lc gl fs id bop sz v1 v2 gv3 EC cs tmn Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gv3 ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc als)
                       ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem)
    trace_nil 

| dbFBop : forall S TD Ps F B lc gl fs id fbop fp v1 v2 gv3 EC cs tmn Mem 
                  als,
  FBOP TD lc gl fbop fp v1 v2 = Some gv3 ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem)
    trace_nil 

| dbExtractValue : forall S TD Ps F B lc gl fs id t v gv gv' idxs EC cs tmn 
                          Mem als,
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_extractvalue id t v idxs)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv') als)::EC) 
                      gl fs Mem)
    trace_nil 

| dbInsertValue : forall S TD Ps F B lc gl fs id t v t' v' gv gv' gv'' idxs
                         EC cs tmn Mem als,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  dbInsn
    (mkState S TD Ps ((mkEC F B ((insn_insertvalue id t v t' v' idxs)::cs) tmn 
                      lc als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv'') als)::EC) 
                      gl fs Mem)
    trace_nil 

| dbMalloc : forall S TD Ps F B lc gl fs id t v gn align EC cs tmn Mem als 
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_malloc id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id (blk2GV TD mb))
                      als)::EC) gl fs Mem')
    trace_nil

| dbFree : forall S TD Ps F B lc gl fs fid t v EC cs tmn Mem als Mem' mptr,
  getOperandValue TD v lc gl = Some mptr ->
  free TD Mem mptr = Some Mem'->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_free fid t v)::cs) tmn lc als)::EC) 
                      gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) gl fs Mem')
    trace_nil

| dbAlloca : forall S TD Ps F B lc gl fs id t v gn align EC cs tmn Mem als 
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_alloca id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id (blk2GV TD mb))
                      (mb::als))::EC) gl fs Mem')
    trace_nil

| dbLoad : forall S TD Ps F B lc gl fs id t v align EC cs tmn Mem als mp gv,
  getOperandValue TD v lc gl = Some mp ->
  mload TD Mem mp t align = Some gv ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_load id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv) als)::EC) gl
                      fs Mem)
    trace_nil

| dbStore : forall S TD Ps F B lc gl fs sid t v1 v2 align EC cs tmn Mem als 
                   mp2 gv1 Mem',
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some mp2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_store sid t v1 v2 align)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) gl fs Mem')
    trace_nil

| dbGEP : forall S TD Ps F B lc gl fs id inbounds t v idxs vidxs EC mp mp' 
                 cs tmn Mem als t',
  getOperandValue TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxs ->
  getGEPTyp idxs t = ret t' ->
  GEP TD t mp vidxs inbounds t' = Some mp' ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_gep id inbounds t v idxs)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id mp') als)::EC) 
                      gl fs Mem)
    trace_nil 

| dbTrunc : forall S TD Ps F B lc gl fs id truncop t1 v1 t2 gv2 EC cs tmn Mem
                   als,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gv2 ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) gl
                       fs Mem)
    trace_nil

| dbExt : forall S TD Ps F B lc gl fs id extop t1 v1 t2 gv2 EC cs tmn Mem als,
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc 
                      als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                      gl fs Mem)
    trace_nil

| dbCast : forall S TD Ps F B lc gl fs id castop t1 v1 t2 gv2 EC cs tmn Mem als,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_cast id castop t1 v1 t2)::cs) tmn lc 
                      als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                     gl fs Mem)
    trace_nil

| dbIcmp : forall S TD Ps F B lc gl fs id cond t v1 v2 gv3 EC cs tmn Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                      gl fs Mem)
    trace_nil

| dbFcmp : forall S TD Ps F B lc gl fs id fcond fp v1 v2 gv3 EC cs tmn Mem als,
  FCMP TD lc gl fcond fp v1 v2 = Some gv3 ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem)
    trace_nil

| dbSelect : forall S TD Ps F B lc gl fs id v0 t v1 v2 c EC cs tmn Mem als 
                    gv1 gv2,
  getOperandValue TD v0 lc gl = Some c ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn 
                       (if isGVZero TD c 
                        then updateAddAL _ lc id gv2 
                        else updateAddAL _ lc id gv1) als)::EC) 
                       gl fs Mem)
    trace_nil

| dbCall : forall S TD Ps F B lc gl fs rid noret ca rt fv lp cs tmn
                       EC Rid oResult tr B' lc' Mem Mem' als' als Mem'' lc'' ft,
  dbFdef fv rt lp S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs)
    tmn lc als)::EC) lc gl fs Mem lc' als' Mem' B' Rid oResult tr ->
  free_allocas TD Mem' als' = Some Mem'' ->
  callUpdateLocals TD ft noret rid oResult lc lc' gl = Some lc'' ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn lc'' als)::EC) gl fs Mem'') 
    tr

| dbExCall : forall S TD Ps F B lc gl fs rid noret fv fid lp cs tmn EC
                    rt la va Mem als oresult Mem' lc' ft fa ca gvs,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  lookupExFdecViaGV TD Ps gl lc fs fv = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  params2GVs TD lp lc gl = Some gvs ->
  callExternalFunction Mem fid gvs = Some (oresult, Mem') ->
  exCallUpdateLocals TD ft noret rid oresult lc = Some lc' ->
  dbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC F B cs tmn lc' als)::EC) gl fs Mem')
    trace_nil

with dbop : State -> State -> trace -> Prop :=
| dbop_nil : forall S, dbop S S trace_nil
| dbop_cons : forall S1 S2 S3 t1 t2,
    dbInsn S1 S2 t1 ->
    dbop S2 S3 t2 ->
    dbop S1 S3 (trace_app t1 t2)

with dbFdef : value -> typ -> params -> system -> TargetData -> products -> 
            list ExecutionContext -> GVMap -> GVMap -> GVMap -> mem -> GVMap ->
            list mblock -> mem -> block -> id -> option value -> trace -> Prop :=
| dbFdef_func : forall S TD Ps gl fs fv fid lp lc rid fa lc0
   l' ps' cs' tmn' rt la lb l'' ps'' cs'' Result lc' tr ECs Mem Mem' als' va gvs,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbop 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             (block_intro l' ps' cs' tmn') cs' tmn' 
                             lc'
                            nil)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             (block_intro l'' ps'' cs'' 
                             (insn_return rid rt Result)) nil 
                             (insn_return rid rt Result) lc'
                            als')::ECs) gl fs Mem')
    tr ->
  dbFdef fv rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' 
    (block_intro l'' ps'' cs'' (insn_return rid rt Result)) rid (Some Result) tr

| dbFdef_proc : forall S TD Ps gl fs fv fid lp lc rid fa lc0
       l' ps' cs' tmn' rt la lb l'' ps'' cs'' lc' tr ECs Mem Mem' als' va gvs,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbop 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             (block_intro l' ps' cs' tmn') cs' tmn' 
                             lc0             
                            nil)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             (block_intro l'' ps'' cs'' (insn_return_void rid)) 
                             nil (insn_return_void rid) lc'
                            als')::ECs) gl fs Mem')
    tr ->
  dbFdef fv rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' 
    (block_intro l'' ps'' cs'' (insn_return_void rid)) rid None tr
.

CoInductive dbInsnInf : State -> Trace -> Prop :=
| dbCallInsnInf : forall S TD Ps F B lc gl fs rid noret ca rt fv lp cs tmn
                       EC tr Mem als ft,
  dbFdefInf fv rt lp S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)
    ::cs) tmn lc als)::EC) lc gl fs Mem tr ->
  dbInsnInf 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
      lc als)::EC) gl fs Mem) tr

with dbopInf : State -> Trace -> Prop :=
| dbopInf_insn : forall state1 t1,
    dbInsnInf state1 t1 ->
    dbopInf state1 t1
| dbopInf_cons : forall state1 state2 t1 t2,
    dbInsn state1 state2 t1 ->
    dbopInf state2 t2 ->
    dbopInf state1 (Trace_app t1 t2)

with dbFdefInf : value -> typ -> params -> system -> TargetData -> products -> 
  list ExecutionContext -> GVMap -> GVMap  -> GVMap -> mem -> Trace -> Prop :=
| dbFdefInf_intro : forall S TD Ps lc gl fs fv fid lp fa lc0
                           l' ps' cs' tmn' rt la va lb tr ECs Mem gvs,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbopInf 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                        (block_intro l' ps' cs' tmn') cs' tmn'
                        lc0
                        nil)::ECs) gl fs Mem)
    tr ->
  dbFdefInf fv rt lp S TD Ps ECs lc gl fs Mem tr
.

Definition db_genInitState := ds_genInitState.
Definition db_isFinialState := ds_isFinialState.

Inductive db_converges : system -> id -> list GenericValue -> State -> Prop :=
| db_converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) 
                       (IS FS:State) tr,
  db_genInitState s main VarArgs Mem.empty = Some IS ->
  dbop IS FS tr ->
  db_isFinialState FS ->
  db_converges s main VarArgs FS
.

Inductive db_diverges : system -> id -> list GenericValue -> Trace -> Prop :=
| db_diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) 
                             (IS S:State) tr,
  db_genInitState s main VarArgs Mem.empty = Some IS ->
  dbopInf IS tr ->
  db_diverges s main VarArgs tr
.

Inductive db_goeswrong : system -> id -> list GenericValue -> State -> Prop :=
| db_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) 
                              (IS FS:State) tr,
  db_genInitState s main VarArgs Mem.empty = Some IS ->
  dbop IS FS tr ->
  ~ db_isFinialState FS ->
  db_goeswrong s main VarArgs FS
.

(***************************************************************)
(* non-deterministic big-step *)

Fixpoint returnStatesFromOp S TD Ps ECs gl fs fa rt fid la va lb 
  (lc_als_Mem_block_ore_trs : 
  list (GVMap*list mblock*mem*block*id*option value*trace)) : States :=
match lc_als_Mem_block_ore_trs with
| nil => nil
| (lc', als', Mem', B'', rid, Some re, tr')::lc_als_Mem_block_ore_trs' => 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             B'' nil (insn_return rid rt re) lc'
                            als')::ECs) gl fs Mem',
                       tr')::
    (returnStatesFromOp S TD Ps ECs gl fs fa rt fid la va lb 
       lc_als_Mem_block_ore_trs')
| (lc', als', Mem', B'', rid, None, tr')::lc_als_Mem_block_ore_trs' => 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             B'' nil (insn_return_void rid) lc'
                            als')::ECs) gl fs Mem',
                       tr')::
    (returnStatesFromOp S TD Ps ECs gl fs fa rt fid la va lb 
      lc_als_Mem_block_ore_trs')
end.

Fixpoint updateStatesFromReturns S TD Ps F B cs tmn lc gl fs rid als EC 
  ft noret (lc_als_Mem_block_rid_re_trs : 
  list (GVMap*list mblock*mem*block*id*option value*trace)): option States :=
match lc_als_Mem_block_rid_re_trs with 
| nil => Some nil
| (lc', als', Mem', B', _, Some re, tr)::lc_als_Mem_block_rid_ore_trs' => 
  do Mem'' <- free_allocas TD Mem' als';
  do lc'' <- 
    match noret with
    | false =>
        match (getOperandValue TD re lc' gl) with
        | Some gr => 
          match ft with
          | typ_function t _ _ =>
            match fit_gv TD gr t with
            | Some gr' => Some (updateAddAL _ lc rid (? gr # t ?))
            | None => None
            end
          | _ => None
          end
        | None => None
        end
    | true =>
        match (getOperandValue TD re lc' gl) with
        | Some gr => Some lc
        | None => None
        end
    end;
  do states <- updateStatesFromReturns S TD Ps F B cs tmn lc gl fs rid als 
                 EC ft noret lc_als_Mem_block_rid_ore_trs';
     ret ((mkState S TD Ps ((mkEC F B cs tmn lc'' als)::EC) 
                           gl fs Mem'', tr)::states)
| (lc', als', Mem', B', _, None, tr)::lc_als_Mem_block_rid_ore_trs' => 
  do Mem'' <- free_allocas TD Mem' als';
  do lc'' <- 
    match noret with
    | false => None
    | true => Some lc
    end;
  do states <- updateStatesFromReturns S TD Ps F B cs tmn lc gl fs rid als
                 EC ft noret lc_als_Mem_block_rid_ore_trs';
     ret ((mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) 
                            gl fs Mem'', tr)::states)
end.

Inductive nbInsn : State*trace -> States -> Prop :=
| nbBranch_def : forall S TD Ps F B lc gl fs bid Cond l1 l2 c
                              l' ps' cs' tmn' EC tr Mem als lc',   
  getOperandValue TD Cond lc gl = Some c ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  nbInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br bid Cond l1 l2) lc als)::EC) gl
                       fs Mem, tr)
    ((mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc'
                          als)::EC) gl fs Mem, tr)::nil)

| nbBranch_undef : forall S TD Ps F B lc bid Cond l1 l2 l1' ps1' cs1' tmn1' 
      l2' ps2' cs2' tmn2' EC tr gl fs Mem als lc1' lc2',   
  isOperandUndef TD (typ_int Size.One) Cond lc gl ->
  Some (block_intro l1' ps1' cs1' tmn1') = lookupBlockViaLabelFromFdef F l1 ->
  Some (block_intro l2' ps2' cs2' tmn2') = lookupBlockViaLabelFromFdef F l2 ->
  switchToNewBasicBlock TD (block_intro l1' ps1' cs1' tmn1') B gl lc =
    Some lc1' ->
  switchToNewBasicBlock TD (block_intro l2' ps2' cs2' tmn2') B gl lc =
    Some lc2' ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br bid Cond l1 l2) lc als)::EC) 
                       gl fs Mem, tr)
    ((mkState S TD Ps ((mkEC F (block_intro l1' ps1' cs1' tmn1') cs1' tmn1'
                         lc1' als)::EC) gl fs Mem, tr)::
     (mkState S TD Ps ((mkEC F (block_intro l2' ps2' cs2' tmn2') cs2' tmn2' 
                         lc2' als)::EC) gl fs Mem, tr)::nil)

| nbBranch_uncond : forall S TD Ps F B lc gl fs l bid
                              l' ps' cs' tmn' EC tr Mem als lc',   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  nbInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br_uncond bid l) lc als)::EC) gl fs
                       Mem, tr)
    ((mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn'
                         lc' als)::EC) gl fs Mem, tr)::nil)

| nbBop : forall S TD Ps F B lc gl fs id bop sz v1 v2 gv3 EC cs tmn tr Mem 
                 als,
  BOP TD lc gl bop sz v1 v2 = Some gv3 ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem, tr)::nil)

| nbFBop : forall S TD Ps F B lc gl fs id fbop fp v1 v2 gv3 EC cs tmn tr Mem
                  als,
  FBOP TD lc gl fbop fp v1 v2 = Some gv3 ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc 
                       als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem, tr)::nil)

| nbExtractValue : forall S TD Ps F B lc gl fs id t v gv gv' idxs EC cs tmn 
                          Mem als tr,
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_extractvalue id t v idxs)::cs) tmn lc
                       als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv') als)::EC) 
                       gl fs Mem, tr)::nil)

| nbInsertValue : forall S TD Ps F B lc gl fs id t v t' v' gv gv' gv'' idxs 
                         EC cs tmn Mem als tr,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_insertvalue id t v t' v' idxs)::cs) tmn 
                       lc als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv'') als)::EC)
                        gl fs Mem, tr)::nil)

| nbMalloc : forall S TD Ps F B lc gl fs id t v gn align EC cs tmn Mem als 
                    Mem' tsz mb tr,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_malloc id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id (blk2GV TD mb))
                        als)::EC) gl fs Mem', tr)::nil)

| nbFree : forall S TD Ps F B lc gl fs fid t v EC cs tmn Mem als Mem' mptr 
                  tr,
  getOperandValue TD v lc gl = Some mptr ->
  free TD Mem mptr = Some Mem'->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_free fid t v)::cs) tmn lc als)::EC) 
                      gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) gl fs Mem', tr)::nil)

| nbAlloca : forall S TD Ps F B lc gl fs id t v gn align EC cs tmn Mem als 
                    Mem' tsz mb tr,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_alloca id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id (blk2GV TD mb))
                       (mb::als))::EC) gl fs Mem', tr)::nil)

| nbLoad : forall S TD Ps F B lc gl fs id t v align EC cs tmn Mem als mp gv 
                  tr,
  getOperandValue TD v lc gl = Some mp ->
  mload TD Mem mp t align = Some gv ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_load id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv) als)::EC) 
                       gl fs Mem, tr)::nil)

| nbStore : forall S TD Ps F B lc gl fs sid t v1 v2 align EC cs tmn Mem als
                   mp2 gv1 Mem' tr,
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some mp2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_store sid t v1 v2 align)::cs) tmn lc 
                      als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) gl fs Mem', tr)::nil)

| nbGEP : forall S TD Ps F B lc gl fs id inbounds t v idxs vidxs EC mp mp' 
                 cs tmn Mem als tr t',
  getOperandValue TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxs ->
  getGEPTyp idxs t = ret t' ->
  GEP TD t mp vidxs false t' = Some mp' ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_gep id inbounds t v idxs)::cs) tmn lc
                       als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn(updateAddAL _ lc id mp') als)::EC) 
                        gl fs Mem, tr)::nil)

| nbTrunc : forall S TD Ps F B lc gl fs id truncop t1 v1 t2 gv2 EC cs tmn 
                   Mem als tr, 
  TRUNC TD lc gl truncop t1 v1 t2 = Some gv2 ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc 
                       als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                        gl fs Mem, tr)::nil)

| nbExt : forall S TD Ps F B lc gl fs id extop t1 v1 t2 gv2 EC cs tmn Mem 
                 als tr, 
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc
                      als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                        gl fs Mem, tr)::nil)

| nbCast : forall S TD Ps F B lc gl fs id castop t1 v1 t2 gv2 EC cs tmn Mem 
                  als tr,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_cast id castop t1 v1 t2)::cs) tmn lc
                       als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                        gl fs Mem, tr)::nil)

| nbIcmp : forall S TD Ps F B lc gl fs id cond t v1 v2 gv3 EC cs tmn Mem als tr,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem, tr)::nil)

| nbFcmp : forall S TD Ps F B lc gl fs id fcond fp v1 v2 gv3 EC cs tmn Mem 
                  als tr,
  FCMP TD lc gl fcond fp v1 v2 = Some gv3 ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc
                       als)::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem, tr)::nil)

| nbSelect : forall S TD Ps F B lc gl fs id v0 t v1 v2 c EC cs tmn Mem als 
                    tr gv1 gv2,
  getOperandValue TD v0 lc gl = Some c ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem, tr) 
    ((mkState S TD Ps ((mkEC F B cs tmn 
                         (if isGVZero TD c 
                          then updateAddAL _ lc id gv2 
                          else updateAddAL _ lc id gv1) als)::EC) gl fs Mem, 
                       tr)::nil)

| nbCall : forall S TD Ps F B lc gl fs rid noret ca rt fv lp cs tmn
                         EC tr lc_als_Mem_block_rid_ore_trs Mem als states ft, 
  nbFdef fv rt lp S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) 
     tmn lc als)::EC) lc gl fs Mem tr lc_als_Mem_block_rid_ore_trs ->
  updateStatesFromReturns S TD Ps F B cs tmn lc gl fs rid als EC ft noret 
    lc_als_Mem_block_rid_ore_trs = Some states ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem, tr) states    

| nbExCall : forall S TD Ps F B lc gl fs rid noret ca fv fid lp cs tmn EC
                     rt la va Mem als tr oresult Mem' lc' ft fa gvs,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  lookupExFdecViaGV TD Ps gl lc fs fv = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  params2GVs TD lp lc gl = Some gvs ->
  callExternalFunction Mem fid gvs = Some (oresult, Mem') ->
  exCallUpdateLocals TD ft noret rid oresult lc = Some lc' ->
  nbInsn 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem, tr)
    ((mkState S TD Ps ((mkEC F B cs tmn lc' als)::EC) gl fs Mem', tr)::nil)

with nbop_star : States -> States -> Prop :=
| nbop_star_nil : nbop_star nil nil
| nbop_star_refl : forall state_tr states states',
  nbop_star states states' ->
  nbop_star (state_tr::states) (state_tr::states')
| nbop_star_cons : forall state tr states states1 states2,
  nbInsn (state, tr) states1 ->
  nbop_star states states2 ->
  nbop_star ((state, tr)::states) (states1++states2)
| nbop_star_trans : forall states1 states2 states3,
  nbop_star states1 states2 ->
  nbop_star states2 states3 ->
  nbop_star states1 states3 

with nbFdef : value -> typ -> params -> system -> TargetData -> products -> 
  list ExecutionContext -> GVMap -> GVMap -> GVMap -> mem -> trace -> 
  list (GVMap*list mblock*mem*block*id*option value*trace) -> Prop :=
| nbFdef_intro : forall S TD Ps lc gl fs fv fid lp fa lc0
       l' ps' cs' tmn' rt la va lb tr lc_als_Mem_block_rid_ore_trs ECs Mem gvs,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  nbop_star 
    ((mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                         (block_intro l' ps' cs' tmn') cs' tmn' 
                         lc0
                         nil)::ECs) gl fs Mem, tr)
                         ::nil)
    (returnStatesFromOp S TD Ps ECs gl fs fa rt fid la va lb 
      lc_als_Mem_block_rid_ore_trs) ->
  nbFdef fv rt lp S TD Ps ECs lc gl fs Mem tr lc_als_Mem_block_rid_ore_trs
.

Definition StatesInf := list (State*Trace).

Inductive wfStatesInf : StatesInf -> Prop :=
| wfStatesInf_nil : wfStatesInf nil
| wfStatesInf_cons : forall state t states,
  wfState state ->
  wfStatesInf states ->
  wfStatesInf ((state, t)::states)
.

Inductive nbop_plus : States -> States -> Prop :=
| nbop_plus_cons : forall state_tr states states1 states2,
  nbInsn state_tr states1 ->
  nbop_star states states2 ->
  nbop_plus (state_tr::states) (states1++states2)
| nbop_plus_trans : forall states1 states2 states3,
  nbop_plus states1 states2 ->
  nbop_star states2 states3 ->
  nbop_plus states1 states3 
.

CoInductive nbInsnInf : State*trace -> list Trace -> Prop :=
| nbCallInsnInf : forall S TD Ps F B lc gl fs rid noret ca rt fv lp
                            EC tr trs Mem als cs tmn ft, 
  nbFdefInf fv rt lp S TD Ps 
    ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn lc als)::EC)  
    lc gl fs Mem tr trs ->
  nbInsnInf 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
    lc als)::EC) gl fs Mem, tr) trs

with nbopInf : States -> list Trace -> Prop :=
| nbopInf_cons : forall state_tr states tr1 tr2,
  nbInsnInf state_tr tr1 ->
  nbopInf states tr2 ->
  nbopInf (state_tr::states) (tr1++tr2)
| nbopInf_trans : forall states1 states2 trs,
  nbop_plus states1 states2 ->
  nbopInf states2 trs ->
  nbopInf states1 trs 

with nbFdefInf : value -> typ -> params -> system -> TargetData -> products -> 
                 list ExecutionContext -> GVMap -> GVMap -> GVMap -> mem -> 
                 trace -> list Trace -> Prop :=
| nbFdefInf_intro : forall S TD Ps lc gl fs fv fid lp fa lc0
                            l' ps' cs' tmn' ECs rt la va lb tr trs' Mem gvs,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  nbopInf 
    ((mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                          (block_intro l' ps' cs' tmn') cs' tmn' 
                          lc0
                          nil)::ECs) gl fs Mem, tr)
                          ::nil) 
    trs' ->
  nbFdefInf fv rt lp S TD Ps ECs lc gl fs Mem tr trs'
.

Definition nb_genInitState := ns_genInitState.
Definition nb_isFinialState := ns_isFinialState.

Inductive nb_converges : system -> id -> list GenericValue -> States -> Prop :=
| nb_converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) 
                              (IS FS:States),
  nb_genInitState s main VarArgs Mem.empty = Some IS ->
  nbop_star IS FS ->
  nb_isFinialState FS ->
  nb_converges s main VarArgs FS
.

Inductive nb_diverges : system -> id -> list GenericValue -> list Trace -> Prop 
  :=
| nb_diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) 
                             (IS:States) trs,
  nb_genInitState s main VarArgs Mem.empty = Some IS ->
  nbopInf IS trs ->
  nb_diverges s main VarArgs trs
.

Inductive nb_goeswrong : system -> id -> list GenericValue -> States -> Prop :=
| nb_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) 
                              (IS FS:States),
  nb_genInitState s main VarArgs Mem.empty = Some IS ->
  nbop_star IS FS ->
  ~ nb_isFinialState FS ->
  nb_goeswrong s main VarArgs FS
.

Scheme dbInsn_ind2 := Induction for dbInsn Sort Prop
  with dbop_ind2 := Induction for dbop Sort Prop
  with dbFdef_ind2 := Induction for dbFdef Sort Prop.

Combined Scheme db_mutind from dbInsn_ind2, dbop_ind2, dbFdef_ind2.

Scheme nbInsn_ind2 := Induction for nbInsn Sort Prop
  with nbop_star_ind2 := Induction for nbop_star Sort Prop
  with nbFdef_ind2 := Induction for nbFdef Sort Prop.

Combined Scheme nb_mutind from nbInsn_ind2, nbop_star_ind2, nbFdef_ind2.

Tactic Notation "db_mutind_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBranch" | c "dbBranch_uncond" |
    c "dbBop" | c "dbFBop" | c "dbExtractValue" | c "dbInsertValue" |
    c "dbMalloc" | c "dbFree" |
    c "dbAlloca" | c "dbLoad" | c "dbStore" | c "dbGEP" |
    c "dbTrunc" | c "dbExt" | c "dbCast" | c "dbIcmp" | c "dbFcmp" |  c "dbSelect" | 
    c "dbCall" | c "dbExCall" |
    c "dbop_nil" | c "dbop_cons" | c "dbFdef_func" | c "dbFdef_proc" ].

Tactic Notation "dsInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "dsReturn" | c "dsReturnVoid" | c "dsBranch" | c "dsBranch_uncond" |
    c "dsBop" | c "dsFBop" | c "dsExtractValue" | c "dsInsertValue" |
    c "dsMalloc" | c "dsFree" |
    c "dsAlloca" | c "dsLoad" | c "dsStore" | c "dsGEP" |
    c "dsTrunc" | c "dsExt" | c "dsCast" | c "dsIcmp" | c "dsFcmp" | c "dsSelect" |  
    c "dsCall" | c "dsExCall" ].

Tactic Notation "dsop_star_cases" tactic(first) tactic(c) :=
  first;
  [ c "dsop_star_nil" | c "dsop_star_cons" ].

Tactic Notation "nb_mutind_cases" tactic(first) tactic(c) :=
  first;
  [ c "nbBranch_def" | c "nbBranch_undef" | c "nbBranch_uncond" |
    c "nbBop" | c "nbFBop" | c "nbExtractValue" | c "nbInsertValue" |
    c "nbMalloc" | c "nbFree" |
    c "nbAlloca" | c "nbLoad" | c "nbStore" | c "nbGEP" | 
    c "nbTrunc" | c "nbExt" | c "nbCast" | c "nbIcmp" | c "nbFcmp" | c "nbSelect" | 
    c "nbCall" | c "nbExCall" |
    c "nbop_star_nil" | c "nbop_star_refl" | c "nbop_star_cons" | 
    c "nbop_star_trans" | c "nbFdef_intro" ].

Tactic Notation "nsInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "nsReturn" | c "nsReturnVoid" | c "nsBranch_def" | c "nsBranch_undef" | 
    c "nsBranch_uncond" | c "nsBop" | c "nsFBop" | c "nsExtractValue" | c "nsInsertValue" |
    c "nsMalloc" | c "bsFree" |
    c "nsAlloca" | c "nsLoad" | c "nsStore" | c "nsGEP" |
    c "nsTrunc" | c "nsExt" | c "nsCast" | c "nsIcmp" | c "nsFcmp" | c "nsSelect" | 
    c "nsCall" | c "nsExCall" ].

Tactic Notation "nsop_star_cases" tactic(first) tactic(c) :=
  first;
  [ c "nsop_star_nil" | c "nsop_star_refl" | 
    c "nsop_star_cons" | c "nsop_star_trans" ].

Tactic Notation "nsop_plus_cases" tactic(first) tactic(c) :=
  first;
  [ c "nsop_plus_cons" | c "nsop_plus_trans" ].


Hint Constructors dbInsn dbop dbFdef dsInsn dsop_star dsop_diverges dsop_plus
                  nbInsn nbop_star nbop_plus nbFdef nsInsn nsop_star
                  nsop_diverges nsop_plus.

End LLVMopsem.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
