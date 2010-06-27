Require Import ssa.
Require Import List.
Require Import Arith.

Inductive GenericValue : Set := 
| GV_int : forall (n:nat), GenericValue
| GV_ptr : forall (n:nat), GenericValue
| GV_undef : GenericValue
.

Definition GVMap := id -> option GenericValue.

Definition updateGVMap (m:GVMap) (i:id) (v:option GenericValue) : GVMap :=
fun i' =>
  if (beq_nat i i')
  then v
  else m i'
.

Record ExecutionContext : Set := mkEC {
CurFunction : fdef;
CurBB       : block;
CurInst     : insn;
Locals      : GVMap;
VarArgs     : list GenericValue
}.

Definition ECStack := list ExecutionContext.

Record State : Set := mkState {
CurSystem   : system;
CurModule   : module;
ExistValue  : option GenericValue;
ECS         : ECStack;
Globals     : GVMap
}.

Definition updateLocals := updateGVMap.
Definition updateGlobals := updateGVMap.

Definition updateMem (locals globals:GVMap) (i:id) (v:option GenericValue) : GVMap*GVMap :=
(updateLocals locals i v,
 fun i' =>
  if (beq_nat i i')
  then 
    match (locals i) with
    | Some _ => None
    | None => v
    end
  else globals i')
.

Inductive wfState : State -> Prop :=
| wfState_intro : forall state,
  In state.(CurModule) state.(CurSystem) ->
  wfState state
.

Inductive wfExecutionContext : ExecutionContext -> Prop :=
| wfExecutionContext_intro : forall EC fh lb l li,
  EC.(CurFunction) = fdef_intro fh lb ->
  In EC.(CurBB) lb ->
  EC.(CurBB) = block_intro l li ->
  In EC.(CurInst) li ->
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
| wfContexts_intro : forall ECS ExistValue s m g,
  wfECStack ECS ->
  wfContexts (mkState s m ExistValue ECS g)
.

Definition getCallerReturnID (Caller:insn) : option id :=
match Caller with
(* | insn_invoke i _ _ _ _ _ => Some i *)
| insn_call i _ _ _ => Some i
| _ => None
end.

Fixpoint getIdViaLabelFromIdls (idls:list (id*l)) (l0:l) : option id :=
match idls with
| nil => None
| (id1, l1)::idls'=>
  if (beq_nat l1 l0)
  then Some id1
  else None
end.

Definition getIdViaBlockFromIdls (idls:list (id*l)) (b:block) : option id :=
match b with
| block_intro l _ => getIdViaLabelFromIdls idls l
end.

Definition getIdViaBlockFromPHINode (i:insn) (b:block) : option id :=
match i with
| insn_phi _ _ idls => getIdViaBlockFromIdls idls b
| _ => None
end.

Fixpoint getPHINodesFromListInsn (li:list_insn): list_insn :=
match li with
| nil => nil
| (insn_phi a b c)::li' => (insn_phi a b c)::getPHINodesFromListInsn li'
| _::li' => getPHINodesFromListInsn li'
end.

Definition getPHINodesFromBlock (b:block) : list_insn :=
match b with
| (block_intro _ li) => getPHINodesFromListInsn li
end.

(* This function is used by switchToNewBasicBlock, which only checks local variables (from PHI) *)
Fixpoint getIncomingValuesForBlockFromPHINodes (PNs:list_insn) (b:block) (locals:GVMap) : list (id*(option GenericValue)) :=
match PNs with
| nil => nil
| PN::PNs => 
  match (getIdViaBlockFromPHINode PN b) with
  | None => getIncomingValuesForBlockFromPHINodes PNs b locals
  | Some id => (id, locals id)::getIncomingValuesForBlockFromPHINodes PNs b locals
  end
end.

(* This function is used by switchToNewBasicBlock, which only updates local variables (from PHI) *)
Fixpoint updateValusForNewBlock (ResultValues:list (id*(option GenericValue))) (locals:GVMap) : GVMap :=
match ResultValues with
| nil => locals
| (id, Some v)::ResultValues' => updateLocals (updateValusForNewBlock ResultValues' locals) id (Some v)
| _::ResultValues' => updateValusForNewBlock ResultValues' locals
end.

Fixpoint getEntryInsnFromInsns (li:list_insn) : option insn :=
match li with
| nil => None
| (insn_phi _ _ _)::li' => getEntryInsnFromInsns li'
| i'::li' => Some i'
end.

Definition getEntryBlock (fd:fdef) : option block :=
match fd with
| fdef_intro _ (b::_) => Some b
| _ => None
end.

Definition getEntryInsn (b:block) : option insn :=
match b with
| block_intro _ li => getEntryInsnFromInsns li
end.

Function getNextInsnFromInsns (input:list_insn*insn) 
         {measure (fun input'=>length (fst input'))} : option insn :=
let (li, ci) := input in
match li with
| nil => None
| i::(i'::li') => if (ci =i= i) then Some i' else (getNextInsnFromInsns (i'::li', ci))
| _ => None
end.
intros.
  simpl. auto.
Qed.

Definition getNextInsnFrom (ci:insn) (b:block) : option insn :=
match b with
| block_intro _ li => getNextInsnFromInsns (li,ci)
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
Definition switchToNewBasicBlock (Dest:block) (PrevBB:block) (locals:GVMap): (block*GVMap) :=
  let PNs := getPHINodesFromBlock Dest in
  let ResultValues := getIncomingValuesForBlockFromPHINodes PNs PrevBB locals in
  (Dest, updateValusForNewBlock ResultValues locals).

(* FIXME: Interpreter::getOperandValue is more complicated than this definition...
*)
Definition getOperandValue (v:value) (locals:GVMap) (globals:GVMap) : option GenericValue := 
match v with
| value_id id => 
  match locals id with
  | Some gv => Some gv
  | None => globals id
  end
| value_constant (const_val n) => Some (GV_int n)
| value_constant const_undef => Some GV_undef
end.

Fixpoint params2OpGenericValues (lp:list_param) (locals:GVMap) (globals:GVMap) : list (option GenericValue):=
match lp with
| nil => nil
| (_, v)::lp' => getOperandValue v locals globals::params2OpGenericValues lp' locals globals
end.

Fixpoint _initializeFrameValues (la:list_arg) (lg:list GenericValue) (locals:GVMap) : GVMap :=
match (la, lg) with
| ((_, id)::la', g::lg') => updateLocals (_initializeFrameValues la' lg' locals) id (Some g)
| _ => locals
end.

Definition initializeFrameValues (la:list_arg) (lg:list GenericValue): GVMap := 
_initializeFrameValues la lg (fun _ => None).

Fixpoint opGenericValues2GenericValues (lg:list (option GenericValue)) : list GenericValue :=
match lg with
| nil => nil
| (Some g)::lg' => g::opGenericValues2GenericValues lg'
| _::lg' => opGenericValues2GenericValues lg'
end.

Record Event : Set := mkEvent {}.

Inductive trace : Set :=
| trace_nil : trace
| trace_cons : Event -> trace -> trace
.

CoInductive Trace : Set :=
| Trace_cons : Event -> Trace -> Trace
.

Fixpoint trace_app (t1 t2:trace) : trace :=
match t1 with
| trace_nil => t2
| trace_cons t t1' => trace_cons t (trace_app t1' t2)
end.

Fixpoint Trace_app (t1:trace) (t2:Trace) : Trace :=
match t1 with
| trace_nil => t2
| trace_cons t t1' => Trace_cons t (Trace_app t1' t2)
end.

(***************************************************************)
(* deterministic small-step *)

Inductive dsInst : State -> State -> trace -> Prop :=
| dsReturn_finished : forall S M F B RetTy Result lc gl arg ExitValue,
  (* Finished main.  Put result into exit code... *)
  ExitValue =  (if (Typ.isInteger RetTy)  (* Nonvoid return type? *)
               then getOperandValue Result lc gl (* Capture the exit value of the program *)
               else Some GV_undef) ->
  dsInst 
    (mkState S M None ((mkEC F B (insn_return RetTy Result) lc arg)::nil) gl)
    (mkState S M ExitValue nil gl)
    trace_nil 
| dsReturn_call : forall S M F B RetTy Result lc gl arg id
                            F' B' I' lc' arg' EC gv
                            I'' lc'' gl'',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  Instruction.isCallInst I' ->
  getCallerReturnID I' = Some id ->
  getOperandValue Result lc gl = Some gv -> 
  (lc'', gl'') = (if (RetTy =t= typ_void) 
                  then (lc', gl) 
                  else (updateMem lc' gl id (Some gv))) ->
  getNextInsnFrom I' B' = Some I'' ->
  dsInst 
    (mkState S M None ((mkEC F B (insn_return RetTy Result) lc arg)::(mkEC F' B' I' lc' arg')::EC) gl)
    (mkState S M None ((mkEC F' B' I'' lc'' arg')::EC) gl'')
    trace_nil 
| dsReturnVoid_finished : forall S M F B lc gl arg ExitValue,
  (* Finished main.  Put result into exit code... *)
  ExitValue = Some GV_undef ->
  dsInst 
    (mkState S M None ((mkEC F B (insn_return_void) lc arg)::nil) gl)
    (mkState S M ExitValue nil gl)
    trace_nil
| dsReturnVoid_call : forall S M F B lc gl arg ExitValue id
                            F' B' I' lc' arg' EC
                            I'',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  Instruction.isCallInst I' ->
  getCallerReturnID I' = Some id ->
  getNextInsnFrom I' B' = Some I'' ->
  dsInst 
    (mkState S M ExitValue ((mkEC F B insn_return_void lc arg)::(mkEC F' B' I' lc' arg')::EC) gl)
    (mkState S M ExitValue ((mkEC F' B' I'' lc' arg')::EC) gl)
    trace_nil 
| dsBranch : forall S M F B lc gl arg ExitValue t Cond l1 l2 c
                              B' I' lc' Dest EC,   
  getOperandValue Cond lc gl = Some (GV_int c) ->
  Some Dest = (if c 
               then lookupBlockViaLabelFromSystem S l1
               else lookupBlockViaLabelFromSystem S l2) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B' = Some I' ->
  dsInst 
    (mkState S M ExitValue ((mkEC F B (insn_br t Cond l1 l2) lc arg)::EC) gl)
    (mkState S M ExitValue ((mkEC F B' I' lc' arg)::EC) gl)
    trace_nil 
| dsBranch_uncond : forall S M F B lc gl arg ExitValue l
                              B' I' lc' Dest EC,   
  Some Dest = (lookupBlockViaLabelFromSystem S l) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B = Some I' ->
  dsInst 
    (mkState S M ExitValue ((mkEC F B (insn_br_uncond l) lc arg)::EC) gl)
    (mkState S M ExitValue ((mkEC F B' I' lc' arg)::EC) gl)
    trace_nil 
| dsCallInsnt : forall S M F B lc gl arg ExitValue rid t fid lp
                            Oparg' arg' F' B' I' EC rt id la lb lc',
  params2OpGenericValues lp lc gl = Oparg' ->   
  opGenericValues2GenericValues Oparg' = arg' ->   
  lookupFdefViaIDFromSystemC S fid = Some F' ->
  getEntryBlock F' = Some B' ->
  getEntryInsn B' = Some I' ->
  F' = fdef_intro (fheader_intro rt id la) lb ->
  initializeFrameValues la arg' = lc' ->
  dsInst 
    (mkState S M ExitValue ((mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl)
    (mkState S M ExitValue ((mkEC F' B' I' lc' arg')::(mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl)
    trace_nil 
| dsAddInsnt : forall S M F B lc gl lc' gl' arg ExitValue id t v1 v2 EC i1 i2 I',
  getOperandValue v1 lc gl = Some (GV_int i1) ->
  getOperandValue v2 lc gl = Some (GV_int i2) ->
  getNextInsnFrom (insn_add id t v1 v2) B = Some I' ->
  updateMem lc gl id (Some (GV_int (i1+i2))) = (lc', gl') -> 
  dsInst 
    (mkState S M ExitValue ((mkEC F B (insn_add id t v1 v2) lc arg)::EC) gl) 
    (mkState S M ExitValue ((mkEC F B I' lc' arg)::EC) gl')
    trace_nil 
.

(* A fake generation of global, we have not support globals yet. *)
Definition genGlobal (s:system) (main:id) : GVMap := fun _ => None.

Definition ds_genInitState (S:system) (main:id) (VarArgs:list GenericValue) :=
match (lookupFdefViaIDFromSystemC S main) with
| None => None
| Some CurFunction =>
  match (getParentOfFdefFromSystemC CurFunction S) with
  | None => None
  | Some CurModule =>
    match (getEntryBlock CurFunction) with
    | None => None
    | Some CurBB => 
      match (getEntryInsn CurBB) with
      | None => None
      | Some CurInst =>
        match CurFunction with 
        | fdef_intro (fheader_intro rt _ la) _ =>
          let Values := initializeFrameValues la VarArgs in
          Some
            (mkState
              S
              CurModule
              None
              ((mkEC
                CurFunction 
                CurBB 
                CurInst
                Values 
                VarArgs 
              )::nil)
              (genGlobal S main)
            )          
        end
      end
    end
  end
end.

Definition ds_isFinialState (S:State) : bool :=
match S with
| (mkState _ _ _ nil _) => true
| _ => false
end.

Inductive dsop : State -> State -> trace -> Prop :=
| dsop_nil : forall S, dsop S S trace_nil
| dsop_cons : forall S1 S2 S3 t1 t2,
    dsInst S1 S2 t1 ->
    dsop S2 S3 t2 ->
    dsop S1 S3 (trace_app t1 t2)
.

CoInductive dsop_diverges : State -> State -> Trace -> Prop :=
| dsop_diverges_intro : forall S1 S2 S3 t1 t2,
    dsInst S1 S2 t1 ->
    dsop_diverges S2 S3 t2 ->
    dsop_diverges S1 S3 (Trace_app t1 t2)
.

Inductive ds_converges : system -> id -> list GenericValue -> State -> Prop :=
| ds_converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:State) tr,
  ds_genInitState s main VarArgs = Some IS ->
  dsop IS FS tr ->
  ds_isFinialState FS ->
  ds_converges s main VarArgs FS
.

Inductive ds_diverges : system -> id -> list GenericValue -> Prop :=
| ds_diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS S:State) tr,
  ds_genInitState s main VarArgs = Some IS ->
  dsop_diverges IS S tr ->
  ds_diverges s main VarArgs
.


Inductive ds_goeswrong : system -> id -> list GenericValue -> State -> Prop :=
| ds_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:State) tr,
  ds_genInitState s main VarArgs = Some IS ->
  dsop IS FS tr ->
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
| wfStates_cons : forall state t states,
  wfState state ->
  wfStates states ->
  wfStates ((state, t)::states)
.

Inductive nsInst : State*trace -> States -> Prop :=
| nsReturn_finished : forall S M F B RetTy Result lc gl arg ExitValue tr,
  (* Finished main.  Put result into exit code... *)
  ExitValue =  (if (Typ.isInteger RetTy)  (* Nonvoid return type? *)
               then getOperandValue Result lc gl (* Capture the exit value of the program *)
               else Some GV_undef) ->
  nsInst 
    (mkState S M None ((mkEC F B (insn_return RetTy Result) lc arg)::nil) gl, tr)
    ((mkState S M ExitValue nil gl, tr)::nil)
| nsReturn_call : forall S M F B RetTy Result lc gl arg id
                            F' B' I' lc' arg' EC gv
                            I'' lc'' gl'' tr,   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  Instruction.isCallInst I' ->
  getCallerReturnID I' = Some id ->
  getOperandValue Result lc gl = Some gv -> 
  (lc'', gl'') = (if (RetTy =t= typ_void) 
                  then (lc', gl) 
                  else (updateMem lc' gl id (Some gv))) ->
  getNextInsnFrom I' B' = Some I'' ->
  nsInst 
    (mkState S M None ((mkEC F B (insn_return RetTy Result) lc arg)::(mkEC F' B' I' lc' arg')::EC) gl, tr)
    ((mkState S M None ((mkEC F' B' I'' lc'' arg')::EC) gl'', tr)::nil)
| nsReturnVoid_finished : forall S M F B lc gl arg ExitValue tr,
  (* Finished main.  Put result into exit code... *)
  ExitValue = Some GV_undef ->
  nsInst 
    (mkState S M None ((mkEC F B (insn_return_void) lc arg)::nil) gl, tr)
    ((mkState S M ExitValue nil gl, tr)::nil)
| nsReturnVoid_call : forall S M F B lc gl arg ExitValue id
                            F' B' I' lc' arg' EC
                            I'' tr,   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  Instruction.isCallInst I' ->
  getCallerReturnID I' = Some id ->
  getNextInsnFrom I' B' = Some I'' ->
  nsInst 
    (mkState S M ExitValue ((mkEC F B insn_return_void lc arg)::(mkEC F' B' I' lc' arg')::EC) gl, tr)
    ((mkState S M ExitValue ((mkEC F' B' I'' lc' arg')::EC) gl, tr)::nil)
| nsBranch_def : forall S M F B lc gl arg ExitValue t Cond l1 l2 c
                              B' I' lc' Dest EC tr,   
  getOperandValue Cond lc gl = Some (GV_int c) ->
  Some Dest = (if c 
               then lookupBlockViaLabelFromSystem S l1
               else lookupBlockViaLabelFromSystem S l2) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B' = Some I' ->
  nsInst 
    (mkState S M ExitValue ((mkEC F B (insn_br t Cond l1 l2) lc arg)::EC) gl, tr)
    ((mkState S M ExitValue ((mkEC F B' I' lc' arg)::EC) gl, tr)::nil)
| nsBranch_undef : forall S M F B lc arg ExitValue t Cond l1 l2
                              B1' I1' lc1' B2' I2' lc2' Dest1 Dest2 EC gl tr,   
  getOperandValue Cond lc gl = Some GV_undef ->
  Some Dest1 = lookupBlockViaLabelFromSystem S l1 ->
  Some Dest2 = lookupBlockViaLabelFromSystem S l2 ->
  (B1', lc1') = (switchToNewBasicBlock Dest1 B lc) ->
  (B2', lc2') = (switchToNewBasicBlock Dest2 B lc) ->
  getEntryInsn B1' = Some I1' ->
  getEntryInsn B2' = Some I2' ->
  nsInst 
    (mkState S M ExitValue ((mkEC F B (insn_br t Cond l1 l2) lc arg)::EC) gl, tr)
    ((mkState S M ExitValue ((mkEC F B1' I1' lc1' arg)::EC) gl, tr)::
     (mkState S M ExitValue ((mkEC F B2' I2' lc2' arg)::EC) gl, tr)::nil)
| nsBranch_uncond : forall S M F B lc gl arg ExitValue l
                              B' I' lc' Dest EC tr,   
  Some Dest = (lookupBlockViaLabelFromSystem S l) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B = Some I' ->
  nsInst 
    (mkState S M ExitValue ((mkEC F B (insn_br_uncond l) lc arg)::EC) gl, tr)
    ((mkState S M ExitValue ((mkEC F B' I' lc' arg)::EC) gl, tr)::nil)
| nsCallInsnt : forall S M F B lc gl arg ExitValue rid t fid lp
                            Oparg' arg' F' B' I' EC rt id la lb lc' tr,
  params2OpGenericValues lp lc gl = Oparg' ->   
  opGenericValues2GenericValues Oparg' = arg' ->   
  lookupFdefViaIDFromSystemC S fid = Some F' ->
  getEntryBlock F' = Some B' ->
  getEntryInsn B' = Some I' ->
  F' = fdef_intro (fheader_intro rt id la) lb ->
  initializeFrameValues la arg' = lc' ->
  nsInst 
    (mkState S M ExitValue ((mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl, tr)
    ((mkState S M ExitValue ((mkEC F' B' I' lc' arg')::(mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl, tr)::nil)
| nsAddInsnt : forall S M F B lc gl lc' gl' arg ExitValue id t v1 v2 EC i1 i2 I' tr,
  getOperandValue v1 lc gl = Some (GV_int i1) ->
  getOperandValue v2 lc gl = Some (GV_int i2) ->
  getNextInsnFrom (insn_add id t v1 v2) B = Some I' ->
  updateMem lc gl id (Some (GV_int (i1+i2))) = (lc', gl') -> 
  nsInst 
    (mkState S M ExitValue ((mkEC F B (insn_add id t v1 v2) lc arg)::EC) gl, tr) 
    ((mkState S M ExitValue ((mkEC F B I' lc' arg)::EC) gl', tr)::nil)
.

Definition ns_genInitState (S:system) (main:id) (VarArgs:list GenericValue) : option States :=
match (lookupFdefViaIDFromSystemC S main) with
| None => None
| Some CurFunction =>
  match (getParentOfFdefFromSystemC CurFunction S) with
  | None => None
  | Some CurModule =>
    match (getEntryBlock CurFunction) with
    | None => None
    | Some CurBB => 
      match (getEntryInsn CurBB) with
      | None => None
      | Some CurInst =>
        match CurFunction with 
        | fdef_intro (fheader_intro rt _ la) _ =>
          let Values := initializeFrameValues la VarArgs in
          Some
            ((mkState
              S
              CurModule
              None
              ((mkEC
                CurFunction 
                CurBB 
                CurInst
                Values 
                VarArgs 
              )::nil)
              (genGlobal S main),
              trace_nil
            )::nil)
        end
      end
    end
  end
end.

Fixpoint ns_isFinialState (states:States) : bool :=
match states with
| (mkState _ _ _ nil _, _)::states' => true
| (mkState _ _ _ _ _, _)::states' => ns_isFinialState states'
| _ => false
end.

Inductive nsInstMerge : States -> States -> Prop :=
| nsInstMerge_nil : nsInstMerge nil nil
| nsInstMerge_cons : forall state tr states states1 states2,
  nsInst (state, tr) states1 ->
  nsInstMerge states states2 ->
  nsInstMerge ((state, tr)::states) (states1++states2)
.

Inductive nsop : States -> States -> Prop :=
| nsop_nil : nsop nil nil
| nsop_cons : forall states1 states2 states3,
  nsInstMerge states1 states2 ->
  nsop states2 states3 ->
  nsop states1 states3
.

CoInductive nsop_diverges : States -> States -> Prop :=
| nsop_diverges_intro : forall state tr states states1 states2,
    nsInst (state,tr) states1 ->
    nsop_diverges states states2 ->
    nsop_diverges ((state, tr)::states) (states1++states2)
.

Inductive ns_converges : system -> id -> list GenericValue -> States -> Prop :=
| ns_converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:States),
  ns_genInitState s main VarArgs = Some IS ->
  nsop IS FS ->
  ns_isFinialState FS ->
  ns_converges s main VarArgs FS
.

Inductive ns_diverges : system -> id -> list GenericValue -> Prop :=
| ns_diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS S:States),
  ns_genInitState s main VarArgs = Some IS ->
  nsop_diverges IS S ->
  ns_diverges s main VarArgs
.

Inductive ns_goeswrong : system -> id -> list GenericValue -> States -> Prop :=
| ns_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:States),
  ns_genInitState s main VarArgs = Some IS ->
  nsop IS FS ->
  ~ ns_isFinialState FS ->
  ns_goeswrong s main VarArgs FS
.

(***************************************************************)
(* deterministic big-step *)

Inductive dbInst : State -> State -> trace -> Prop :=
| dbReturn_finished : forall S M F B RetTy Result lc gl arg ExitValue,
  (* Finished main.  Put result into exit code... *)
  ExitValue =  (if (Typ.isInteger RetTy)  (* Nonvoid return type? *)
               then getOperandValue Result lc gl (* Capture the exit value of the program *)
               else Some GV_undef) ->
  dbInst 
    (mkState S M None ((mkEC F B (insn_return RetTy Result) lc arg)::nil) gl)
    (mkState S M ExitValue nil gl)
    trace_nil 
| dbReturn_call : forall S M F B RetTy Result lc gl arg id
                            F' B' I' lc' arg' EC gv
                            I'' lc'' gl'',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  Instruction.isCallInst I' ->
  getCallerReturnID I' = Some id ->
  getOperandValue Result lc gl = Some gv -> 
  (lc'', gl'') = (if (RetTy =t= typ_void) 
                  then (lc', gl) 
                  else (updateMem lc' gl id (Some gv))) ->
  getNextInsnFrom I' B' = Some I'' ->
  dbInst 
    (mkState S M None ((mkEC F B (insn_return RetTy Result) lc arg)::(mkEC F' B' I' lc' arg')::EC) gl)
    (mkState S M None ((mkEC F' B' I'' lc'' arg')::EC) gl'')
    trace_nil 
| dbReturnVoid_finished : forall S M F B lc gl arg ExitValue,
  (* Finished main.  Put result into exit code... *)
  ExitValue = Some GV_undef ->
  dbInst 
    (mkState S M None ((mkEC F B (insn_return_void) lc arg)::nil) gl)
    (mkState S M ExitValue nil gl)
    trace_nil
| dbReturnVoid_call : forall S M F B lc gl arg ExitValue id
                            F' B' I' lc' arg' EC
                            I'',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  Instruction.isCallInst I' ->
  getCallerReturnID I' = Some id ->
  getNextInsnFrom I' B' = Some I'' ->
  dbInst 
    (mkState S M ExitValue ((mkEC F B insn_return_void lc arg)::(mkEC F' B' I' lc' arg')::EC) gl)
    (mkState S M ExitValue ((mkEC F' B' I'' lc' arg')::EC) gl)
    trace_nil 
| dbBranch : forall S M F B lc gl arg ExitValue t Cond l1 l2 c
                              B' I' lc' Dest EC,   
  getOperandValue Cond lc gl = Some (GV_int c) ->
  Some Dest = (if c 
               then lookupBlockViaLabelFromSystem S l1
               else lookupBlockViaLabelFromSystem S l2) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B' = Some I' ->
  dbInst 
    (mkState S M ExitValue ((mkEC F B (insn_br t Cond l1 l2) lc arg)::EC) gl)
    (mkState S M ExitValue ((mkEC F B' I' lc' arg)::EC) gl)
    trace_nil 
| dbBranch_uncond : forall S M F B lc gl arg ExitValue l
                              B' I' lc' Dest EC,   
  Some Dest = (lookupBlockViaLabelFromSystem S l) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B = Some I' ->
  dbInst 
    (mkState S M ExitValue ((mkEC F B (insn_br_uncond l) lc arg)::EC) gl)
    (mkState S M ExitValue ((mkEC F B' I' lc' arg)::EC) gl)
    trace_nil 
| dbCallInsnt : forall S M F B lc gl arg rid t fid lp gl' gl''
                       EC ExitValue ReturnValue tr I',
  dbFdef fid lp
    (mkState S M None ((mkEC F B (insn_call rid t fid lp) lc arg)::nil) gl) 
    (mkState S M ReturnValue nil gl') 
    tr ->
  updateGlobals gl' rid ReturnValue = gl'' -> 
  getNextInsnFrom (insn_call rid t fid lp) B = Some I' ->
  dbInst 
    (mkState S M ExitValue ((mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl) 
    (mkState S M ExitValue ((mkEC F B I' lc arg)::EC) gl'') 
    tr
| dbAddInsnt : forall S M F B lc gl lc' gl' arg ExitValue id t v1 v2 EC i1 i2 I',
  getOperandValue v1 lc gl = Some (GV_int i1) ->
  getOperandValue v2 lc gl = Some (GV_int i2) ->
  getNextInsnFrom (insn_add id t v1 v2) B = Some I' ->
  updateMem lc gl id (Some (GV_int (i1+i2))) = (lc', gl') -> 
  dbInst 
    (mkState S M ExitValue ((mkEC F B (insn_add id t v1 v2) lc arg)::EC) gl) 
    (mkState S M ExitValue ((mkEC F B I' lc' arg)::EC) gl')
    trace_nil 
with dbop : State -> State -> trace -> Prop :=
| dbop_nil : forall S, dbop S S trace_nil
| dbop_cons : forall S1 S2 S3 t1 t2,
    dbInst S1 S2 t1 ->
    dbop S2 S3 t2 ->
    dbop S1 S3 (trace_app t1 t2)
with dbFdef : id -> list_param -> State -> State -> trace -> Prop :=
| dbFdef_intro : forall S M F B lc gl arg ExitValue rid t fid lp
                            Oparg' arg' F' B' I' EC rt id la lb lc' state' tr,
  params2OpGenericValues lp lc gl = Oparg' ->   
  opGenericValues2GenericValues Oparg' = arg' ->   
  lookupFdefViaIDFromSystemC S fid = Some F' ->
  getEntryBlock F' = Some B' ->
  getEntryInsn B' = Some I' ->
  F' = fdef_intro (fheader_intro rt id la) lb ->
  initializeFrameValues la arg' = lc' ->
  dbop 
    (mkState S M ExitValue ((mkEC F' B' I' lc' arg')::(mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl)
    state'
    tr ->
  dbFdef fid lp 
    (mkState S M ExitValue ((mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl) state' tr
.

CoInductive dbInstInf : State -> Trace -> Prop :=
| dbCallInsntInf : forall S M F B lc gl arg rid t fid lp gl' gl''
                       EC ExitValue ReturnValue tr I',
  dbFdefInf fid lp
    (mkState S M None ((mkEC F B (insn_call rid t fid lp) lc arg)::nil) gl) 
    tr ->
  updateGlobals gl' rid ReturnValue = gl'' -> 
  getNextInsnFrom (insn_call rid t fid lp) B = Some I' ->
  dbInstInf 
    (mkState S M ExitValue ((mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl) 
    tr
with dbopInf : State -> Trace -> Prop :=
| dbopInf_cons1 : forall S1 t1,
    dbInstInf S1 t1 ->
    dbopInf S1 t1
| dbopInf_cons2 : forall S1 S2 t1 t2,
    dbInst S1 S2 t1 ->
    dbopInf S2 t2 ->
    dbopInf S1 (Trace_app t1 t2)
with dbFdefInf : id -> list_param -> State -> Trace -> Prop :=
| dbFdefInf_intro : forall S M F B lc gl arg ExitValue rid t fid lp
                            Oparg' arg' F' B' I' EC rt id la lb lc' tr,
  params2OpGenericValues lp lc gl = Oparg' ->   
  opGenericValues2GenericValues Oparg' = arg' ->   
  lookupFdefViaIDFromSystemC S fid = Some F' ->
  getEntryBlock F' = Some B' ->
  getEntryInsn B' = Some I' ->
  F' = fdef_intro (fheader_intro rt id la) lb ->
  initializeFrameValues la arg' = lc' ->
  dbopInf 
    (mkState S M ExitValue ((mkEC F' B' I' lc' arg')::(mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl)
    tr ->
  dbFdefInf fid lp 
    (mkState S M ExitValue ((mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl) 
    tr
.

Definition db_genInitState := ds_genInitState.
Definition db_isFinialState := ds_isFinialState.

Inductive db_converges : system -> id -> list GenericValue -> State -> Prop :=
| db_converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:State) tr,
  db_genInitState s main VarArgs = Some IS ->
  dbop IS FS tr ->
  db_isFinialState FS ->
  db_converges s main VarArgs FS
.

Inductive db_diverges : system -> id -> list GenericValue -> Prop :=
| db_diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS S:State) tr,
  db_genInitState s main VarArgs = Some IS ->
  dbopInf IS tr ->
  db_diverges s main VarArgs
.

Inductive db_goeswrong : system -> id -> list GenericValue -> State -> Prop :=
| db_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:State) tr,
  db_genInitState s main VarArgs = Some IS ->
  dbop IS FS tr ->
  ~ db_isFinialState FS ->
  db_goeswrong s main VarArgs FS
.

(***************************************************************)
(* non-deterministic big-step *)

Fixpoint returnStatesFromFdef S M (gls_ev_tr : list (GVMap*(option GenericValue)*trace)) : States :=
match gls_ev_tr with
| nil => nil
| (gl, ev, tr)::gls_ev_tr' => (mkState S M ev nil gl, tr)::(returnStatesFromFdef S M gls_ev_tr')
end.

Fixpoint updateStatesFromReturns S M F B I' ExitValue lc arg EC rid gls_ev_tr : States :=
match gls_ev_tr with 
| nil => nil
| (gl, ev, tr)::gls_ev_tr' => 
  (mkState S M ExitValue ((mkEC F B I' lc arg)::EC) (updateGlobals gl rid ev), tr)::
  (updateStatesFromReturns S M F B I' ExitValue lc arg EC rid gls_ev_tr')
end.

Inductive nbInst : State*trace -> States -> Prop :=
| nbReturn_finished : forall S M F B RetTy Result lc gl arg ExitValue tr,
  (* Finished main.  Put result into exit code... *)
  ExitValue =  (if (Typ.isInteger RetTy)  (* Nonvoid return type? *)
               then getOperandValue Result lc gl (* Capture the exit value of the program *)
               else Some GV_undef) ->
  nbInst 
    (mkState S M None ((mkEC F B (insn_return RetTy Result) lc arg)::nil) gl, tr)
    ((mkState S M ExitValue nil gl, tr)::nil)
| nbReturn_call : forall S M F B RetTy Result lc gl arg id
                            F' B' I' lc' arg' EC gv
                            I'' lc'' gl'' tr,   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  Instruction.isCallInst I' ->
  getCallerReturnID I' = Some id ->
  getOperandValue Result lc gl = Some gv -> 
  (lc'', gl'') = (if (RetTy =t= typ_void) 
                  then (lc', gl) 
                  else (updateMem lc' gl id (Some gv))) ->
  getNextInsnFrom I' B' = Some I'' ->
  nbInst 
    (mkState S M None ((mkEC F B (insn_return RetTy Result) lc arg)::(mkEC F' B' I' lc' arg')::EC) gl, tr)
    ((mkState S M None ((mkEC F' B' I'' lc'' arg')::EC) gl'', tr)::nil)
| nbReturnVoid_finished : forall S M F B lc gl arg ExitValue tr,
  (* Finished main.  Put result into exit code... *)
  ExitValue = Some GV_undef ->
  nbInst 
    (mkState S M None ((mkEC F B (insn_return_void) lc arg)::nil) gl, tr)
    ((mkState S M ExitValue nil gl, tr)::nil)
| nbReturnVoid_call : forall S M F B lc gl arg ExitValue id
                            F' B' I' lc' arg' EC
                            I'' tr,   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  Instruction.isCallInst I' ->
  getCallerReturnID I' = Some id ->
  getNextInsnFrom I' B' = Some I'' ->
  nbInst 
    (mkState S M ExitValue ((mkEC F B insn_return_void lc arg)::(mkEC F' B' I' lc' arg')::EC) gl, tr)
    ((mkState S M ExitValue ((mkEC F' B' I'' lc' arg')::EC) gl, tr)::nil)
| nbBranch_def : forall S M F B lc gl arg ExitValue t Cond l1 l2 c
                              B' I' lc' Dest EC tr,   
  getOperandValue Cond lc gl = Some (GV_int c) ->
  Some Dest = (if c 
               then lookupBlockViaLabelFromSystem S l1
               else lookupBlockViaLabelFromSystem S l2) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B' = Some I' ->
  nbInst 
    (mkState S M ExitValue ((mkEC F B (insn_br t Cond l1 l2) lc arg)::EC) gl, tr)
    ((mkState S M ExitValue ((mkEC F B' I' lc' arg)::EC) gl, tr)::nil)
| nbBranch_undef : forall S M F B lc arg ExitValue t Cond l1 l2
                              B1' I1' lc1' B2' I2' lc2' Dest1 Dest2 EC tr gl,   
  getOperandValue Cond lc gl = Some GV_undef ->
  Some Dest1 = lookupBlockViaLabelFromSystem S l1 ->
  Some Dest2 = lookupBlockViaLabelFromSystem S l2 ->
  (B1', lc1') = (switchToNewBasicBlock Dest1 B lc) ->
  (B2', lc2') = (switchToNewBasicBlock Dest2 B lc) ->
  getEntryInsn B1' = Some I1' ->
  getEntryInsn B2' = Some I2' ->
  nbInst 
    (mkState S M ExitValue ((mkEC F B (insn_br t Cond l1 l2) lc arg)::EC) gl, tr)
    ((mkState S M ExitValue ((mkEC F B1' I1' lc1' arg)::EC) gl, tr)::
     (mkState S M ExitValue ((mkEC F B2' I2' lc2' arg)::EC) gl, tr)::nil)
| nbBranch_uncond : forall S M F B lc gl arg ExitValue l
                              B' I' lc' Dest EC tr,   
  Some Dest = (lookupBlockViaLabelFromSystem S l) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B = Some I' ->
  nbInst 
    (mkState S M ExitValue ((mkEC F B (insn_br_uncond l) lc arg)::EC) gl, tr)
    ((mkState S M ExitValue ((mkEC F B' I' lc' arg)::EC) gl, tr)::nil)
| nbCallInsnt : forall S M F B lc gl arg ExitValue rid t fid lp
                            EC tr gls_ev_tr I', 
  nbFdef fid lp
    (mkState S M None ((mkEC F B (insn_call rid t fid lp) lc arg)::nil) gl, tr) 
    (returnStatesFromFdef S M gls_ev_tr) ->
  getNextInsnFrom (insn_call rid t fid lp) B = Some I' ->
  nbInst 
    (mkState S M ExitValue ((mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl, tr) 
    (updateStatesFromReturns S M F B I' ExitValue lc arg EC rid gls_ev_tr)
| nbAddInsnt : forall S M F B lc gl lc' gl' arg ExitValue id t v1 v2 EC i1 i2 I' tr,
  getOperandValue v1 lc gl = Some (GV_int i1) ->
  getOperandValue v2 lc gl = Some (GV_int i2) ->
  getNextInsnFrom (insn_add id t v1 v2) B = Some I' ->
  updateMem lc gl id (Some (GV_int (i1+i2))) = (lc', gl') -> 
  nbInst 
    (mkState S M ExitValue ((mkEC F B (insn_add id t v1 v2) lc arg)::EC) gl, tr) 
    ((mkState S M ExitValue ((mkEC F B I' lc' arg)::EC) gl', tr)::nil)
with nbInstMerge : States -> States -> Prop :=
| nbInstMerge_nil : nbInstMerge nil nil
| nbInstMerge_cons : forall state tr states states1 states2,
  nbInst (state, tr) states1 ->
  nbInstMerge states states2 ->
  nbInstMerge ((state, tr)::states) (states1++states2)
with nbop : States -> States -> Prop :=
| nbop_nil : nbop nil nil
| nbop_cons : forall states1 states2 states3,
  nbInstMerge states1 states2 ->
  nbop states2 states3 ->
  nbop states1 states3 
with nbFdef : id -> list_param -> State*trace -> States -> Prop :=
| nbFdef_intro : forall S M F B lc gl arg ExitValue rid t fid lp
                            Oparg' arg' F' B' I' EC rt id la lb lc' states' tr,
  params2OpGenericValues lp lc gl = Oparg' ->   
  opGenericValues2GenericValues Oparg' = arg' ->   
  lookupFdefViaIDFromSystemC S fid = Some F' ->
  getEntryBlock F' = Some B' ->
  getEntryInsn B' = Some I' ->
  F' = fdef_intro (fheader_intro rt id la) lb ->
  initializeFrameValues la arg' = lc' ->
  nbop 
    ((mkState S M ExitValue ((mkEC F' B' I' lc' arg')::(mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl, tr)::nil)
    states' ->
  nbFdef fid lp 
    (mkState S M ExitValue ((mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl, tr) states'
.

Definition StatesInf := list (State*Trace).

Inductive wfStatesInf : StatesInf -> Prop :=
| wfStatesInf_nil : wfStatesInf nil
| wfStatesInf_cons : forall state t states,
  wfState state ->
  wfStatesInf states ->
  wfStatesInf ((state, t)::states)
.

CoInductive nbInstInf : State*trace -> list Trace -> Prop :=
| nbCallInsntInf : forall S M F B lc gl arg ExitValue rid t fid lp
                            EC tr trs, 
  nbFdefInf fid lp
    (mkState S M None ((mkEC F B (insn_call rid t fid lp) lc arg)::nil) gl, tr) 
    trs ->
  nbInstInf 
    (mkState S M ExitValue ((mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl, tr)
    trs
with nbInstInfMerge : States -> list Trace -> Prop :=
| nbInstInfMerge_nil : nbInstInfMerge nil nil
| nbInstInfMerge_cons : forall state states tr1 tr2,
  nbInstInf state tr1 ->
  nbInstInfMerge states tr2 ->
  nbInstInfMerge (state::states) (tr1++tr2)
with nbopInf : States -> list Trace -> Prop :=
| nbopInf_cons1 : forall states trs,
  nbInstInfMerge states trs ->
  nbopInf states trs
| nbopInf_cons2 : forall states1 states2 states3,
  nbInstMerge states1 states2 ->
  nbopInf states2 states3 ->
  nbopInf states1 states3 
with nbFdefInf : id -> list_param -> State*trace -> list Trace -> Prop :=
| nbFdefInf_intro : forall S M F B lc gl arg ExitValue rid t fid lp
                            Oparg' arg' F' B' I' EC rt id la lb lc' tr tr',
  params2OpGenericValues lp lc gl = Oparg' ->   
  opGenericValues2GenericValues Oparg' = arg' ->   
  lookupFdefViaIDFromSystemC S fid = Some F' ->
  getEntryBlock F' = Some B' ->
  getEntryInsn B' = Some I' ->
  F' = fdef_intro (fheader_intro rt id la) lb ->
  initializeFrameValues la arg' = lc' ->
  nbopInf 
    ((mkState S M ExitValue ((mkEC F' B' I' lc' arg')::(mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl, tr)::nil) 
    tr' ->
  nbFdefInf fid lp 
    (mkState S M ExitValue ((mkEC F B (insn_call rid t fid lp) lc arg)::EC) gl, tr)
    tr'
.

Definition nb_genInitState := ns_genInitState.
Definition nb_isFinialState := ns_isFinialState.

Inductive nb_converges : system -> id -> list GenericValue -> States -> Prop :=
| nb_converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:States),
  nb_genInitState s main VarArgs = Some IS ->
  nbop IS FS ->
  nb_isFinialState FS ->
  nb_converges s main VarArgs FS
.

Inductive nb_diverges : system -> id -> list GenericValue -> list Trace -> Prop :=
| nb_diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS:States) trs,
  nb_genInitState s main VarArgs = Some IS ->
  nbopInf IS trs ->
  nb_diverges s main VarArgs trs
.

Inductive nb_goeswrong : system -> id -> list GenericValue -> States -> Prop :=
| nb_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:States),
  nb_genInitState s main VarArgs = Some IS ->
  nbop IS FS ->
  ~ nb_isFinialState FS ->
  nb_goeswrong s main VarArgs FS
.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../monads" "-I" "../ott" "-I" "../") ***
*** End: ***
 *)
