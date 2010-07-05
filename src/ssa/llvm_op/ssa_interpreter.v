Require Import ssa_lib.
Require Import List.
Require Import Arith.

Inductive GenericValue : Set := 
| GenericValue_int : forall (n:nat), GenericValue
| GenericValue_untyped : forall (n:nat), GenericValue
.

Definition Mem := id -> option GenericValue.

Definition updateMem (m:Mem) (i:id) (v:GenericValue) : Mem :=
fun i' =>
  if (beq_nat i i')
  then Some v
  else m i'
.

Record ExecutionContext : Set := mkExecutionContext {
CurFunction : fdef;
CurBB       : block;
CurInst     : insn;
Values      : Mem;
VarArgs     : list GenericValue;
Caller      : insn
}.

Definition ECStack := list ExecutionContext.

Record State : Set := mkState {
CurSystem   : system;
CurModule   : module;
ExistValue  : option GenericValue;
ECS         : ECStack
}.

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
| wfContexts_intro : forall ECS ExistValue s m,
  wfECStack ECS ->
  wfContexts (mkState s m ExistValue ECS)
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

Fixpoint getIncomingValuesForBlockFromPHINodes (PNs:list_insn) (b:block) (Values:Mem) : list (id*(option GenericValue)) :=
match PNs with
| nil => nil
| PN::PNs => 
  match (getIdViaBlockFromPHINode PN b) with
  | None => getIncomingValuesForBlockFromPHINodes PNs b Values
  | Some id => (id, Values id)::getIncomingValuesForBlockFromPHINodes PNs b Values
  end
end.

Fixpoint updateValusForNewBlock (ResultValues:list (id*(option GenericValue))) (Values:Mem) : Mem :=
match ResultValues with
| nil => Values
| (id, Some v)::ResultValues' => updateMem (updateValusForNewBlock ResultValues' Values) id v
| _::ResultValues' => updateValusForNewBlock ResultValues' Values
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
*)
Definition switchToNewBasicBlock (Dest:block) (PrevBB:block) (Values:Mem): (block*Mem) :=
  let PNs := getPHINodesFromBlock Dest in
  let ResultValues := getIncomingValuesForBlockFromPHINodes PNs Dest Values in
  (Dest, updateValusForNewBlock ResultValues Values).

(* FIXME: Interpreter::getOperandValue is more complicated than this definition...
*)
Definition getOperandValue (v:value) (Values:Mem) : option GenericValue := 
match v with
| value_id id => Values id
| value_constant (const_val n) => Some (GenericValue_int n)
| value_constant const_undef => Some (GenericValue_int 0)
end.

Fixpoint params2OpGenericValues (lp:list_param) (Values:Mem) : list (option GenericValue):=
match lp with
| nil => nil
| (_, v)::lp' => getOperandValue v Values::params2OpGenericValues lp' Values
end.

Fixpoint _initializeFrameValues (la:list_arg) (lg:list GenericValue) (Values:Mem) : Mem :=
match (la, lg) with
| ((_, id)::la', g::lg') => updateMem (_initializeFrameValues la' lg' Values) id g
| _ => Values
end.

Definition initializeFrameValues (la:list_arg) (lg:list GenericValue): Mem := 
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

Inductive visitInst : State -> State -> trace -> Prop :=
(* 
  Save away the return value... (if we are not 'ret void')
  Pop the last stack frame off of ECStack and then copy the result
  back into the result variable if we are not returning void. The
  result variable may be the ExitValue, or the Value of the calling
  CallInst if there was a previous stack frame. This method may
  invalidate any ECStack iterators you have. This method also takes
  care of switching to the normal destination BB, if we are returning
  from an invoke.  
*)
| visitReturn_finished : forall CurSystem CurModule CurFunction CurBB RetTy Result Values VarArgs Caller ExitValue,
  (* Finished main.  Put result into exit code... *)
  ExitValue = 
        (if (Typ.isInteger RetTy)  (* Nonvoid return type? *)
        then getOperandValue Result Values (* Capture the exit value of the program *)
        else (Some (GenericValue_untyped 0))) ->
  visitInst 
    (mkState 
      CurSystem
      CurModule
      None
      ((mkExecutionContext 
          CurFunction 
          CurBB 
          (insn_return RetTy Result) 
          Values 
          VarArgs 
          Caller
       )
       ::nil) 
     )
    (mkState CurSystem CurModule ExitValue nil)
    trace_nil 
| visitReturn_call : forall CurSystem CurModule CurFunction CurBB RetTy Result Values VarArgs Caller id
                            CurFunction' CurBB' CurInst' Values' VarArgs' Caller' ECS' gvalue
                            CurInst'' Values'',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  getCallerReturnID CurInst' = Some id ->
  getOperandValue Result Values = Some gvalue -> 
  Values'' = (if (RetTy =t= typ_void) 
             then Values' 
             else (updateMem Values' id gvalue)) ->
  Instruction.isCallInst CurInst' ->
  getNextInsnFrom CurInst' CurBB' = Some CurInst'' ->
  visitInst 
    (mkState 
      CurSystem
      CurModule
      None
      ((mkExecutionContext 
          CurFunction 
          CurBB 
          (insn_return RetTy Result) 
          Values 
          VarArgs 
          Caller
      )::
      (mkExecutionContext 
          CurFunction' 
          CurBB' 
          CurInst' 
          Values' 
          VarArgs' 
          Caller'
      )::ECS')
    )
    (mkState
      CurSystem
      CurModule
      None
      ((mkExecutionContext 
          CurFunction' 
          CurBB'
          CurInst''
          Values''
          VarArgs' 
          Caller'
      )::ECS')
    )
    trace_nil 
(*
| visitReturn_invoke : forall CurSystem CurModule CurFunction CurBB RetTy Result Values VarArgs Caller id
                              CurFunction' CurBB' CurInst' Values' VarArgs' Caller' ECS' 
                              Dest CurBB'' CurInst'' Values'' Values0'' gvalue,   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  getCallerReturnID CurInst' = Some id ->
  getOperandValue Result Values = Some gvalue -> 
  Values0'' = (if (RetTy =t= typ_void) 
             then Values' 
             else (updateMem Values' id gvalue)) ->
  Instruction.isInvokeInst CurInst' ->
  InvokeInst.getNormalDest CurSystem CurInst' = Some Dest -> 
  (CurBB'', Values'') = 
             (if (Instruction.isInvokeInst CurInst')
              then (switchToNewBasicBlock Dest CurBB' Values0'')
              else (CurBB', Values0'')) ->
  getEntryInsn CurBB' = Some CurInst'' ->
  visitInst 
    (mkState
      CurSystem
      CurModule
      None
      ((mkExecutionContext 
          CurFunction 
          CurBB 
          (insn_return RetTy Result) 
          Values 
          VarArgs 
          Caller
      )::
      (mkExecutionContext 
          CurFunction' 
          CurBB' 
          CurInst' 
          Values' 
          VarArgs' 
          Caller'
      )::ECS')
    )
    (mkState 
      CurSystem
      CurModule
      None
      ((mkExecutionContext 
          CurFunction' 
          CurBB''
          CurInst''
          Values''
          VarArgs' 
          Caller'
      )::ECS')
    )
    trace_nil 
| visitReturnVoid_finished : forall CurSystem CurModule CurFunction CurBB Values VarArgs Caller ExitValue,
  (* Finished main.  Put result into exit code... *)
  ExitValue = (Some (GenericValue_untyped 0)) ->
  visitInst 
    (mkState 
      CurSystem
      CurModule
      None
      ((mkExecutionContext 
          CurFunction 
          CurBB 
          (insn_return_void) 
          Values 
          VarArgs 
          Caller
       )
       ::nil) 
     )
    (mkState
      CurSystem
      CurModule
      ExitValue
      nil
    )
    trace_nil
| visitReturnVoid_call : forall CurSystem CurModule CurFunction CurBB Values VarArgs Caller ExitValue id
                            CurFunction' CurBB' CurInst' Values' VarArgs' Caller' ECS' 
                            CurInst'',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  getCallerReturnID CurInst' = Some id ->
  Instruction.isCallInst CurInst' ->
  getNextInsnFrom CurInst' CurBB' = Some CurInst'' ->
  visitInst 
    (mkState
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction 
          CurBB 
          insn_return_void
          Values
          VarArgs 
          Caller
      )::
      (mkExecutionContext 
          CurFunction' 
          CurBB' 
          CurInst' 
          Values' 
          VarArgs' 
          Caller'
      )::ECS')
    )
    (mkState 
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction' 
          CurBB'
          CurInst''
          Values'
          VarArgs' 
          Caller'
      )::ECS')
    )
    trace_nil 
| visitReturnVoid_invoke : forall CurSystem CurModule CurFunction CurBB Values VarArgs Caller ExitValue
                              CurFunction' CurBB' CurInst' Values' VarArgs' Caller' ECS' 
                              Dest CurBB'' CurInst'' Values'',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  Instruction.isInvokeInst CurInst' ->
  InvokeInst.getNormalDest CurSystem CurInst' = Some Dest -> 
  (CurBB'', Values'') = 
             (if (Instruction.isInvokeInst CurInst')
              then (switchToNewBasicBlock Dest CurBB' Values')
              else (CurBB', Values')) ->
  getEntryInsn CurBB' = Some CurInst'' ->
  visitInst 
    (mkState
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction 
          CurBB 
          (insn_return_void) 
          Values 
          VarArgs 
          Caller
      )::
      (mkExecutionContext 
          CurFunction' 
          CurBB' 
          CurInst' 
          Values' 
          VarArgs' 
          Caller'
      )::ECS')
    )
    (mkState
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction' 
          CurBB''
          CurInst''
          Values''
          VarArgs' 
          Caller'
      )::ECS')
    )
    trace_nil 
*)
| visitBranch : forall CurSystem CurModule CurFunction CurBB Values VarArgs Caller ExitValue t Cond l1 l2 c
                              CurBB' CurInst' Values' Dest ECS,   
  getOperandValue Cond Values = Some (GenericValue_int c) ->
  Some Dest = (if c 
               then lookupBlockViaLabelFromSystem CurSystem l1
               else lookupBlockViaLabelFromSystem CurSystem l2) ->
  (CurBB', Values') = (switchToNewBasicBlock Dest CurBB Values) ->
  getEntryInsn CurBB = Some CurInst' ->
  visitInst 
    (mkState 
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction 
          CurBB 
          (insn_br t Cond l1 l2) 
          Values 
          VarArgs 
          Caller
      )::ECS)
    )
    (mkState
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction
          CurBB'
          CurInst'
          Values'
          VarArgs 
          Caller
      )::ECS)
    )
    trace_nil 
| visitBranch_uncond : forall CurSystem CurModule CurFunction CurBB Values VarArgs Caller ExitValue l
                              CurBB' CurInst' Values' Dest ECS,   
  Some Dest = (lookupBlockViaLabelFromSystem CurSystem l) ->
  (CurBB', Values') = (switchToNewBasicBlock Dest CurBB Values) ->
  getEntryInsn CurBB = Some CurInst' ->
  visitInst 
    (mkState
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction 
          CurBB 
          (insn_br_uncond l) 
          Values 
          VarArgs 
          Caller
      )::ECS)
    )
    (mkState
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction
          CurBB'
          CurInst'
          Values'
          VarArgs 
          Caller
      )::ECS)
    )
    trace_nil 
(*
| visitInvokeInsnt : forall CurSystem CurModule CurFunction CurBB Values VarArgs Caller ExitValue rid t fid lp l1 l2
                            OpVarArgs' VarArgs' CurFunction' CurBB' CurInst' ECS rt id la lb Values',
  params2OpGenericValues lp Values = OpVarArgs' ->   
  opGenericValues2GenericValues OpVarArgs' = VarArgs' ->   
  lookupFdefViaIDFromSystemC CurSystem fid = Some CurFunction' ->
  getEntryBlock CurFunction' = Some CurBB' ->
  getEntryInsn CurBB' = Some CurInst' ->
  CurFunction' = fdef_intro (fheader_intro rt id la) lb ->
  initializeFrameValues la VarArgs' = Values' ->
  visitInst 
    (mkState 
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction 
          CurBB 
          (insn_invoke rid t fid lp l1 l2) 
          Values 
          VarArgs 
          Caller
      )::ECS)
    )
    (mkState
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction'
          CurBB' 
          CurInst'
          Values' 
          VarArgs' 
          (insn_invoke rid t fid lp l1 l2) 
      )::(mkExecutionContext 
          CurFunction 
          CurBB 
          (insn_invoke rid t fid lp l1 l2) 
          Values 
          VarArgs 
          Caller
      )::ECS)
    )
    trace_nil 
*)
| visitCallInsnt : forall CurSystem CurModule CurFunction CurBB Values VarArgs Caller ExitValue rid t fid lp
                            OpVarArgs' VarArgs' CurFunction' CurBB' CurInst' ECS rt id la lb Values',
  params2OpGenericValues lp Values = OpVarArgs' ->   
  opGenericValues2GenericValues OpVarArgs' = VarArgs' ->   
  lookupFdefViaIDFromSystemC CurSystem fid = Some CurFunction' ->
  getEntryBlock CurFunction' = Some CurBB' ->
  getEntryInsn CurBB' = Some CurInst' ->
  CurFunction' = fdef_intro (fheader_intro rt id la) lb ->
  initializeFrameValues la VarArgs' = Values' ->
  visitInst 
    (mkState
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction 
          CurBB 
          (insn_call rid t fid lp) 
          Values 
          VarArgs 
          Caller
      )::ECS)
    )
    (mkState
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction'
          CurBB' 
          CurInst'
          Values' 
          VarArgs' 
          (insn_call rid t fid lp) 
      )::(mkExecutionContext 
          CurFunction 
          CurBB 
          (insn_call rid t fid lp) 
          Values 
          VarArgs 
          Caller
      )::ECS)
    )
    trace_nil 
| visitAddInsnt : forall CurSystem CurModule CurFunction CurBB Values VarArgs Caller ExitValue id t v1 v2 ECS i1 i2 CurInst',
  getOperandValue v1 Values = Some (GenericValue_int i1) ->
  getOperandValue v2 Values = Some (GenericValue_int i2) ->
  getNextInsnFrom (insn_add id t v1 v2) CurBB = Some CurInst' ->
  visitInst 
    (mkState
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction 
          CurBB 
          (insn_add id t v1 v2) 
          Values 
          VarArgs 
          Caller
      )::ECS)
    ) 
    (mkState
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction 
          CurBB 
          CurInst'
          (updateMem Values id (GenericValue_int (i1+i2)))
          VarArgs 
          Caller
      )::ECS)
    )
    trace_nil 
.

Inductive op_converges : State -> State -> trace -> Prop :=
| op_converges_nil : forall S, op_converges S S trace_nil
| op_converges_cons : forall S1 S2 S3 t1 t2,
    visitInst S1 S2 t1 ->
    op_converges S2 S3 t2 ->
    op_converges S1 S3 (trace_app t1 t2)
.

CoInductive op_diverges : State -> State -> Trace -> Prop :=
| op_diverges_intro : forall S1 S2 S3 t1 t2,
    visitInst S1 S2 t1 ->
    op_diverges S2 S3 t2 ->
    op_diverges S1 S3 (Trace_app t1 t2)
.

Definition genInitState (s:system) (main:id) (VarArgs:list GenericValue) :=
match (lookupFdefViaIDFromSystemC s main) with
| None => None
| Some CurFunction =>
  match (getParentOfFdefFromSystemC CurFunction s) with
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
              s
              CurModule
              None
              ((mkExecutionContext 
                CurFunction 
                CurBB 
                CurInst
                Values 
                VarArgs 
                (insn_call 0 rt main nil) 
              )::nil)
           )          
        end
      end
    end
  end
end.

Definition isFinialState (S:State) : bool :=
match S with
| (mkState _ _ _ nil) => true
| _ => false
end.

Inductive converges : system -> id -> list GenericValue -> State -> Prop :=
| converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:State) t,
  genInitState s main VarArgs = Some IS ->
  op_converges IS FS t ->
  isFinialState FS ->
  converges s main VarArgs FS
.

Inductive diverges : system -> id -> list GenericValue -> Prop :=
| diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS S:State) t,
  genInitState s main VarArgs = Some IS ->
  op_diverges IS S t ->
  diverges s main VarArgs
.

Inductive goeswrong : system -> id -> list GenericValue -> State -> Prop :=
| goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:State) t,
  genInitState s main VarArgs = Some IS ->
  op_converges IS FS t ->
  ~ isFinialState FS ->
  goeswrong s main VarArgs FS
.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../monads" "-I" "../ott" "-I" "../") ***
*** End: ***
 *)
