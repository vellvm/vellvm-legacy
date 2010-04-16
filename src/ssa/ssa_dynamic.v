Require Import ssa_lib.
Require Import List.
Require Import Arith.
Require Import vmcore.
Require Import reflect.

Inductive CallSite : Set := .

Inductive GenericValue : Set := 
| GenericValue_value : forall (v:value), GenericValue
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

Record Contexts : Set := mkContexts {
CurSystem   : system;
CurModule   : module;
ExitValue   : GenericValue;
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

Inductive wfContexts : Contexts -> Prop :=
| wfContexts_intro : forall ECS s m ExitValue,
  wfECStack ECS ->
  wfContexts (mkContexts s m ExitValue ECS)
.

Definition getCallerReturnID (Caller:insn) : option id :=
match Caller with
| insn_invoke i _ _ _ _ _ => Some i
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

Inductive visitInst : Contexts -> Contexts -> Prop :=
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
| visitReturn_finished : forall CurSystem CurModule CurFunction CurBB RetTy Result Values VarArgs Caller ExitValue ExitValue',
  (* Finished main.  Put result into exit code... *)
  ExitValue' = 
        (if (Typ.isInteger RetTy)  (* Nonvoid return type? *)
        then GenericValue_value Result (* Capture the exit value of the program *)
        else GenericValue_untyped 0) ->
  visitInst 
    (mkContexts 
      CurSystem
      CurModule
      ExitValue
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
    (mkContexts 
      CurSystem
      CurModule
      ExitValue'
      nil
    )
| visitReturn_call : forall CurSystem CurModule CurFunction CurBB RetTy Result Values VarArgs Caller ExitValue id
                            CurFunction' CurBB' CurInst' Values' VarArgs' Caller' ECS' 
                            CurInst'' Values'',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  getCallerReturnID CurInst' = Some id ->
  Values'' = (if (RetTy =t= typ_void) 
             then Values' 
             else (updateMem Values' id (GenericValue_value Result))) ->
  Instruction.isCallInst CurInst' ->
  getNextInsnFrom CurInst' CurBB' = Some CurInst'' ->
  visitInst 
    (mkContexts 
      CurSystem
      CurModule
      ExitValue
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
    (mkContexts 
      CurSystem
      CurModule
      ExitValue
      ((mkExecutionContext 
          CurFunction' 
          CurBB'
          CurInst''
          Values''
          VarArgs' 
          Caller'
      )::ECS')
    )
| visitReturn_invoke : forall CurSystem CurModule CurFunction CurBB RetTy Result Values VarArgs Caller ExitValue id
                              CurFunction' CurBB' CurInst' Values' VarArgs' Caller' ECS' 
                              Dest CurBB'' CurInst'' Values'' Values0'',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  getCallerReturnID CurInst' = Some id ->
  Values0'' = (if (RetTy =t= typ_void) 
             then Values' 
             else (updateMem Values' id (GenericValue_value Result))) ->
  Instruction.isInvokeInst CurInst' ->
  InvokeInst.getNormalDest CurSystem CurInst' = Some Dest -> 
  (CurBB'', Values'') = 
             (if (Instruction.isInvokeInst CurInst')
              then (switchToNewBasicBlock Dest CurBB' Values0'')
              else (CurBB', Values0'')) ->
  getEntryInsn CurBB' = Some CurInst'' ->
  visitInst 
    (mkContexts 
      CurSystem
      CurModule
      ExitValue
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
    (mkContexts 
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
| visitReturnVoid_finished : forall CurSystem CurModule CurFunction CurBB Values VarArgs Caller ExitValue ExitValue',
  (* Finished main.  Put result into exit code... *)
  ExitValue' = GenericValue_untyped 0 ->
  visitInst 
    (mkContexts 
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
       )
       ::nil) 
     )
    (mkContexts 
      CurSystem
      CurModule
      ExitValue'
      nil
    )
| visitReturnVoid_call : forall CurSystem CurModule CurFunction CurBB Values VarArgs Caller ExitValue id
                            CurFunction' CurBB' CurInst' Values' VarArgs' Caller' ECS' 
                            CurInst'',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  getCallerReturnID CurInst' = Some id ->
  Instruction.isCallInst CurInst' ->
  getNextInsnFrom CurInst' CurBB' = Some CurInst'' ->
  visitInst 
    (mkContexts 
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
    (mkContexts 
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
| visitReturnVoid_invoke : forall CurSystem CurModule CurFunction CurBB Values VarArgs Caller ExitValue id
                              CurFunction' CurBB' CurInst' Values' VarArgs' Caller' ECS' 
                              Dest CurBB'' CurInst'' Values'',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  getCallerReturnID CurInst' = Some id ->
  Instruction.isInvokeInst CurInst' ->
  InvokeInst.getNormalDest CurSystem CurInst' = Some Dest -> 
  (CurBB'', Values'') = 
             (if (Instruction.isInvokeInst CurInst')
              then (switchToNewBasicBlock Dest CurBB' Values')
              else (CurBB', Values')) ->
  getEntryInsn CurBB' = Some CurInst'' ->
  visitInst 
    (mkContexts 
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
    (mkContexts 
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
.


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./monads" "-I" "./ott") ***
*** End: ***
 *)
