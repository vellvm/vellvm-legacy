Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import ssa_mem.

Inductive GenericValue : Set := 
| GV_int : forall (n:nat), GenericValue
| GV_ptr : forall (addr:maddr), GenericValue
| GV_arr : list GenericValue -> GenericValue
| GV_struct : list GenericValue -> GenericValue
| GV_undef : GenericValue
.

Variable load : list layout -> mem -> maddr -> typ -> option GenericValue.

Variable store : list layout -> mem -> maddr -> typ -> GenericValue -> option mem.

Definition GVMap := id -> option GenericValue.

(** Compute ptr w.r.t data layout, locals/globals, bounds or not *)
Variable gep : list layout -> GVMap -> GVMap -> typ -> maddr -> list value -> bool -> option maddr.

Definition updateGVMap (m:GVMap) (i:id) (v:option GenericValue) : GVMap :=
fun i' =>
  if (beq_nat i i')
  then v
  else m i'
.

Record ExecutionContext : Set := mkEC {
CurFunction : fdef;
CurBB       : block;
CurInsn     : insn;
Locals      : GVMap;                 (* LLVM values used in this invocation *)
Args        : list GenericValue;      
Allocas     : list mblock            (* Track memory allocated by alloca *)
}.

Definition ECStack := list ExecutionContext.

Record State : Set := mkState {
CurSystem   : system;
CurModule   : module;
ECS         : ECStack;
Globals     : GVMap;
Mem         : mem
}.

Definition updateLocals := updateGVMap.
Definition updateGlobals := updateGVMap.

Definition updateEnv (locals globals:GVMap) (i:id) (v:option GenericValue) : GVMap*GVMap :=
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
  In EC.(CurInsn) li ->
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
| wfContexts_intro : forall ECS s m g mem,
  wfECStack ECS ->
  wfContexts (mkState s m ECS g mem)
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
Fixpoint const2GV (c:const) : GenericValue :=
match c with
| (const_int n) => (GV_int n)
| const_undef => GV_undef
| const_null => (GV_ptr null)
| (const_arr lc) => GV_arr (map const2GV lc)
| (const_struct lc) => GV_struct (map const2GV lc)
end.

Definition getOperandValue (v:value) (locals:GVMap) (globals:GVMap) : option GenericValue := 
match v with
| value_id id => 
  match locals id with
  | Some gv => Some gv
  | None => globals id
  end
| value_const c => Some (const2GV c)
end.

Fixpoint params2OpGVs (lp:list_param) (locals:GVMap) (globals:GVMap) : list (option GenericValue):=
match lp with
| nil => nil
| (_, v)::lp' => getOperandValue v locals globals::params2OpGVs lp' locals globals
end.

Fixpoint _initializeFrameValues (la:list_arg) (lg:list GenericValue) (locals:GVMap) : GVMap :=
match (la, lg) with
| ((_, id)::la', g::lg') => updateLocals (_initializeFrameValues la' lg' locals) id (Some g)
| _ => locals
end.

Definition initLocals (la:list_arg) (lg:list GenericValue): GVMap := 
_initializeFrameValues la lg (fun _ => None).

Fixpoint opGVs2GVs (lg:list (option GenericValue)) : list GenericValue :=
match lg with
| nil => nil
| (Some g)::lg' => g::opGVs2GVs lg'
| _::lg' => opGVs2GVs lg'
end.

Definition params2GVs (lp:list_param) (locals:GVMap) (globals:GVMap) := opGVs2GVs (params2OpGVs lp locals globals).

Record Event : Set := mkEvent { }.

Inductive trace : Set :=
| trace_nil : trace
| trace_cons : Event -> trace -> trace
.

CoInductive Trace : Set :=
| Trace_cons : Event -> Trace -> Trace
.

Fixpoint trace_app (tr1 tr2:trace) : trace :=
match tr1 with
| trace_nil => tr2
| trace_cons e tr1' => trace_cons e (trace_app tr1' tr2)
end.

Fixpoint Trace_app (tr1:trace) (tr2:Trace) : Trace :=
match tr1 with
| trace_nil => tr2
| trace_cons e tr1' => Trace_cons e (Trace_app tr1' tr2)
end.

Fixpoint extractGenericValue (locals globals:GVMap) (gv : GenericValue) (idxs : list value) : option GenericValue :=
match idxs with
| nil => Some gv
| idx::idxs' => 
    match (getOperandValue idx locals globals) with
    | Some (GV_int i) =>
      match gv with
      | GV_arr lgv => match (nth_error lgv i) with
                      | Some gv' => extractGenericValue locals globals gv' idxs'
                      | None => None
                      end
      | GV_struct lgv => match (nth_error lgv i) with
                         | Some gv' => extractGenericValue locals globals gv' idxs'
                         | None => None
                         end
      | _ => None
      end
    | _ => None
    end
end.

Fixpoint GV_size (GV:GenericValue) : nat :=
match GV with
| GV_int _ => 1
| GV_ptr _ => 1
| GV_arr GVs => 1 + fold_left plus (map GV_size GVs) 0
| GV_struct GVs => 1 + fold_left plus (map GV_size GVs) 0
| GV_undef => 1
end.

Lemma fold_left_mono1 : forall lgv a b, 
  a <= b ->
  a < S (fold_left plus (map GV_size lgv) b).
Proof.
  induction lgv; intros; simpl; try solve [omega].
    apply IHlgv. omega.
Qed.

Lemma fold_left_mono2 : forall lgv a b, 
  a <= b ->
  (fold_left plus (map GV_size lgv) a) <= (fold_left plus (map GV_size lgv) b).
Proof.
  induction lgv; intros; simpl; try solve [omega].
    apply IHlgv. omega.
Qed.

Lemma nth_error_fold_left_GV_size : forall (lgv:list GenericValue) i gv,
  nth_error lgv i = Some gv ->
  GV_size gv < S (fold_left plus (map GV_size lgv) 0).
Proof.
  induction lgv; intros i gv H.
    destruct i; simpl in *; inversion H.

    destruct i; simpl in *.
      inversion H; subst.
      apply fold_left_mono1; auto.

      apply IHlgv in H.
      assert (J:=@fold_left_mono2 lgv 0 (GV_size a)).
      omega.      
Qed.     

Function _insertGenericValue  
  (input:GenericValue*GVMap*GVMap*list (option GenericValue)*GenericValue) 
  {measure 
    (fun a => 
       match a with ((((gv, locals), globals), gvidxs), gv0) => GV_size gv end
     )
  }: option GenericValue :=
match input with 
((((gv, locals), globals), gvidxs), gv0) =>
  match gvidxs with
  | nil => Some gv0
  | (Some (GV_int i))::gvidxs' => 
    match gv with
    | GV_arr lgv => 
      match (nth_error lgv i) with
      | Some gv' =>
        match (_insertGenericValue (gv', locals, globals, gvidxs' ,gv0)) with
        | Some gv'' =>
          Some (GV_arr (firstn (i-1) lgv ++ ( gv'':: skipn i lgv)))
        | None => None
        end
      | None => None
      end
    | GV_struct lgv => 
      match (nth_error lgv i) with
      | Some gv' =>
        match (_insertGenericValue (gv', locals, globals, gvidxs' ,gv0)) with
        | Some gv'' =>
          Some (GV_struct (firstn (i-1) lgv ++ ( gv'':: skipn i lgv)))
        | None => None
        end
      | None => None
      end
    | _ => None
    end
  | _ => None
  end 
end.
Proof.
  intros. simpl. eapply nth_error_fold_left_GV_size; eauto.
  intros. simpl. eapply nth_error_fold_left_GV_size; eauto.
Qed.

Definition insertGenericValue gv locals globals gvidxs gv0 :=
  _insertGenericValue ((((gv, locals), globals), gvidxs), gv0).

Fixpoint values2OpGVs (lv:list value) (locals:GVMap) (globals:GVMap) : list (option GenericValue):=
match lv with
| nil => nil
| v::lv' => getOperandValue v locals globals::values2OpGVs lv' locals globals
end.

(***************************************************************)
(* deterministic small-step *)

Inductive dsInsn : State -> State -> trace -> Prop :=
| dsReturn : forall S M F B RetTy Result lc gl arg id
                            F' B' I' lc' arg' EC
                            I'' lc'' gl'' Mem Mem' als als',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  Instruction.isCallInst I' = true ->
  getCallerReturnID I' = Some id ->
  (lc'', gl'') = (if (RetTy =t= typ_void) 
                  then (lc', gl) 
                  else (updateEnv lc' gl id (getOperandValue Result lc gl))) ->
  getNextInsnFrom I' B' = Some I'' ->
  free_allocas Mem als = Some Mem' ->
  dsInsn 
    (mkState S M ((mkEC F B (insn_return RetTy Result) lc arg als)::(mkEC F' B' I' lc' arg' als')::EC) gl Mem)
    (mkState S M ((mkEC F' B' I'' lc'' arg' als')::EC) gl'' Mem')
    trace_nil 
(*
| dsReturnVoid : forall S M F B lc gl arg id
                            F' B' I' lc' arg' EC
                            I'',   
  Instruction.isCallInst I' = true ->
  getCallerReturnID I' = Some id ->
  getNextInsnFrom I' B' = Some I'' ->
  dsInsn 
    (mkState S M ((mkEC F B insn_return_void lc arg)::(mkEC F' B' I' lc' arg')::EC) gl)
    (mkState S M ((mkEC F' B' I'' lc' arg')::EC) gl)
    trace_nil 
*)
| dsBranch : forall S M F B lc gl arg Cond l1 l2 c
                              B' I' lc' Dest EC Mem als,   
  getOperandValue Cond lc gl = Some (GV_int c) ->
  Some Dest = (if c 
               then lookupBlockViaLabelFromSystem S l1
               else lookupBlockViaLabelFromSystem S l2) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B' = Some I' ->
  dsInsn 
    (mkState S M ((mkEC F B (insn_br Cond l1 l2) lc arg als)::EC) gl Mem)
    (mkState S M ((mkEC F B' I' lc' arg als)::EC) gl Mem)
    trace_nil 
| dsBranch_uncond : forall S M F B lc gl arg l
                              B' I' lc' Dest EC Mem als,   
  Some Dest = (lookupBlockViaLabelFromSystem S l) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B = Some I' ->
  dsInsn 
    (mkState S M ((mkEC F B (insn_br_uncond l) lc arg als)::EC) gl Mem)
    (mkState S M ((mkEC F B' I' lc' arg als)::EC) gl Mem)
    trace_nil 
| dsCall : forall S M F B lc gl arg rid fid lp
                            B' I' EC rt la lb Mem als,
  lookupFdefViaIDFromSystemC S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some B' ->
  getEntryInsn B' = Some I' ->
  dsInsn 
    (mkState S M ((mkEC F B (insn_call rid rt fid lp) lc arg als)::EC) gl Mem)
    (mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             B' I' (initLocals la (params2GVs lp lc gl)) 
                             (params2GVs lp lc gl) nil)::
                       (mkEC F B (insn_call rid rt fid lp) lc arg als)::EC) gl Mem)
    trace_nil 
| dsAdd : forall S M F B lc gl lc' gl' arg id t v1 v2 EC i1 i2 I' Mem als,
  getOperandValue v1 lc gl = Some (GV_int i1) ->
  getOperandValue v2 lc gl = Some (GV_int i2) ->
  getNextInsnFrom (insn_add id t v1 v2) B = Some I' ->
  updateEnv lc gl id (Some (GV_int (i1+i2))) = (lc', gl') -> 
  dsInsn 
    (mkState S M ((mkEC F B (insn_add id t v1 v2) lc arg als)::EC) gl Mem) 
    (mkState S M ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil 
| dsExtractValue : forall S M F B lc gl lc' gl' arg id t v gv gv' idxs EC I' Mem als,
  getOperandValue v lc gl = Some gv ->
  extractGenericValue lc gl gv idxs = Some gv' ->
  getNextInsnFrom (insn_extractvalue id t v idxs) B = Some I' ->
  updateEnv lc gl id (Some gv') = (lc', gl') -> 
  dsInsn 
    (mkState S M ((mkEC F B (insn_extractvalue id t v idxs) lc arg als)::EC) gl Mem) 
    (mkState S M ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil 
| dsInsertValue : forall S M F B lc gl lc' gl' arg id t v t' v' gv gv' gv'' idxs gvidxs EC I' Mem als,
  getOperandValue v lc gl = Some gv ->
  getOperandValue v' lc gl = Some gv' ->
  values2OpGVs idxs lc gl = gvidxs -> 
  insertGenericValue gv lc gl gvidxs gv' = Some gv'' ->
  getNextInsnFrom (insn_insertvalue id t v t' v' idxs) B = Some I' ->
  updateEnv lc gl id (Some gv'') = (lc', gl') -> 
  dsInsn 
    (mkState S M ((mkEC F B (insn_insertvalue id t v t' v' idxs) lc arg als)::EC) gl Mem) 
    (mkState S M ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil 
| dsAlloca : forall S TD Ps F B lc gl lc' gl' arg id t sz align EC I' Mem als Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  malloc TD Mem (tsz * sz) align = Some (Mem', mb) ->
  getNextInsnFrom (insn_alloca id t sz align) B = Some I' ->
  updateEnv lc gl id (Some (GV_ptr (mb, 0))) = (lc', gl') -> 
  dsInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_alloca id t sz align) lc arg als)::EC) gl Mem) 
    (mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg (mb::als))::EC) gl' Mem')
    trace_nil
| dsLoad : forall S TD Ps F B lc gl lc' gl' arg id t v EC I' Mem als ma gv,
  getOperandValue v lc gl = Some (GV_ptr ma) ->
  load TD Mem ma t = Some gv ->
  updateEnv lc gl id (Some gv) = (lc', gl') -> 
  getNextInsnFrom (insn_load id t v) B = Some I' ->
  dsInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_load id t v) lc arg als)::EC) gl Mem) 
    (mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil
| dsStore : forall S TD Ps F B lc gl lc' gl' arg t v1 v2 EC I' Mem als ma2 gv1 Mem',
  getOperandValue v1 lc gl = Some gv1 ->
  getOperandValue v2 lc gl = Some (GV_ptr ma2) ->
  store TD Mem ma2 t gv1 = Some Mem' ->
  getNextInsnFrom (insn_store t v1 v2) B = Some I' ->
  dsInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_store t v1 v2) lc arg als)::EC) gl Mem) 
    (mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil
| dsGEP : forall S TD Ps F B lc gl lc' gl' arg id t v idxs EC ma ma' I' Mem als,
  getOperandValue v lc gl = Some (GV_ptr ma) ->
  gep TD lc gl t ma idxs false = Some ma' ->
  getNextInsnFrom (insn_gep id t v idxs) B = Some I' ->
  updateEnv lc gl id (Some (GV_ptr ma')) = (lc', gl') -> 
  dsInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_gep id t v idxs) lc arg als)::EC) gl Mem) 
    (mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil 
| dsBGEP : forall S TD Ps F B lc gl lc' gl' arg id t v idxs EC ma ma' I' Mem als,
  getOperandValue v lc gl = Some (GV_ptr ma) ->
  gep TD lc gl t ma idxs true = Some ma' ->
  getNextInsnFrom (insn_bgep id t v idxs) B = Some I' ->
  updateEnv lc gl id (Some (GV_ptr ma')) = (lc', gl') -> 
  dsInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_bgep id t v idxs) lc arg als)::EC) gl Mem) 
    (mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil 
.

(* A fake generation of global, we have not support globals yet. *)
Definition genGlobal (s:system) (main:id) : GVMap := fun _ => None.
Variable initmem : mem.
Definition genMem (s:system) (main:id) : mem := initmem.

Definition ds_genInitState (S:system) (main:id) (Args:list GenericValue) :=
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
          let Values := initLocals la Args in
          Some
            (mkState
              S
              CurModule
              ((mkEC
                CurFunction 
                CurBB 
                CurInst
                Values 
                Args 
                nil
              )::nil)
              (genGlobal S main)
              (genMem S main)
            )          
        end
      end
    end
  end
end.

Definition ds_isFinialState (state:State) : bool :=
match state with
| (mkState _ _ ((mkEC _ _ insn_return_void _ _ _)::nil) _ _) => true
(* | (mkState _ _ ((mkEC _ _ (insn_return _ _) _ _ _)::nil) _ _) => true *)
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
| ds_converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:State) tr,
  ds_genInitState s main VarArgs = Some IS ->
  dsop_star IS FS tr ->
  ds_isFinialState FS ->
  ds_converges s main VarArgs FS
.

Inductive ds_diverges : system -> id -> list GenericValue -> Trace -> Prop :=
| ds_diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS:State) tr,
  ds_genInitState s main VarArgs = Some IS ->
  dsop_diverges IS tr ->
  ds_diverges s main VarArgs tr
.

Inductive ds_goeswrong : system -> id -> list GenericValue -> State -> Prop :=
| ds_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:State) tr,
  ds_genInitState s main VarArgs = Some IS ->
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
| nsReturn : forall S M F B RetTy Result lc gl arg id
                            F' B' I' lc' arg' EC
                            I'' lc'' gl'' tr Mem Mem' als als',   
  (* If we have a previous stack frame, and we have a previous call,
          fill in the return value... *)
  Instruction.isCallInst I' = true ->
  getCallerReturnID I' = Some id ->
  (lc'', gl'') = (if (RetTy =t= typ_void) 
                  then (lc', gl) 
                  else (updateEnv lc' gl id (getOperandValue Result lc gl))) ->
  getNextInsnFrom I' B' = Some I'' ->
  free_allocas Mem als = Some Mem' ->
  nsInsn 
    (mkState S M ((mkEC F B (insn_return RetTy Result) lc arg als)::(mkEC F' B' I' lc' arg' als')::EC) gl Mem, tr)
    ((mkState S M ((mkEC F' B' I'' lc'' arg' als')::EC) gl'' Mem', tr)::nil)
(* 
| nsReturnVoid : forall S M F B lc gl arg id
                            F' B' I' lc' arg' EC
                            I'' tr,   
  Instruction.isCallInst I' = true ->
  getCallerReturnID I' = Some id ->
  getNextInsnFrom I' B' = Some I'' ->
  nsInsn 
    (mkState S M ((mkEC F B insn_return_void lc arg)::(mkEC F' B' I' lc' arg')::EC) gl, tr)
    ((mkState S M ((mkEC F' B' I'' lc' arg')::EC) gl, tr)::nil)
*)
| nsBranch_def : forall S M F B lc gl arg Cond l1 l2 c
                              B' I' lc' Dest EC tr Mem als,   
  getOperandValue Cond lc gl = Some (GV_int c) ->
  Some Dest = (if c 
               then lookupBlockViaLabelFromSystem S l1
               else lookupBlockViaLabelFromSystem S l2) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B' = Some I' ->
  nsInsn 
    (mkState S M ((mkEC F B (insn_br Cond l1 l2) lc arg als)::EC) gl Mem, tr)
    ((mkState S M ((mkEC F B' I' lc' arg als)::EC) gl Mem, tr)::nil)
| nsBranch_undef : forall S M F B lc arg Cond l1 l2
                              B1' I1' lc1' B2' I2' lc2' Dest1 Dest2 EC gl tr Mem als,   
  getOperandValue Cond lc gl = Some GV_undef ->
  Some Dest1 = lookupBlockViaLabelFromSystem S l1 ->
  Some Dest2 = lookupBlockViaLabelFromSystem S l2 ->
  (B1', lc1') = (switchToNewBasicBlock Dest1 B lc) ->
  (B2', lc2') = (switchToNewBasicBlock Dest2 B lc) ->
  getEntryInsn B1' = Some I1' ->
  getEntryInsn B2' = Some I2' ->
  nsInsn 
    (mkState S M ((mkEC F B (insn_br Cond l1 l2) lc arg als)::EC) gl Mem, tr)
    ((mkState S M ((mkEC F B1' I1' lc1' arg als)::EC) gl Mem, tr)::
     (mkState S M ((mkEC F B2' I2' lc2' arg als)::EC) gl Mem, tr)::nil)
| nsBranch_uncond : forall S M F B lc gl arg l
                              B' I' lc' Dest EC tr Mem als,   
  Some Dest = (lookupBlockViaLabelFromSystem S l) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B = Some I' ->
  nsInsn 
    (mkState S M ((mkEC F B (insn_br_uncond l) lc arg als)::EC) gl Mem, tr)
    ((mkState S M ((mkEC F B' I' lc' arg als)::EC) gl Mem, tr)::nil)
| nsCall : forall S M F B lc gl arg rid fid lp
                            Oparg' arg' F' B' I' EC rt id la lb lc' tr Mem als,
  params2OpGVs lp lc gl = Oparg' ->   
  opGVs2GVs Oparg' = arg' ->   
  lookupFdefViaIDFromSystemC S fid = Some F' ->
  getEntryBlock F' = Some B' ->
  getEntryInsn B' = Some I' ->
  F' = fdef_intro (fheader_intro rt id la) lb ->
  initLocals la arg' = lc' ->
  nsInsn 
    (mkState S M ((mkEC F B (insn_call rid rt fid lp) lc arg als)::EC) gl Mem, tr)
    ((mkState S M ((mkEC F' B' I' lc' arg' nil)::(mkEC F B (insn_call rid rt fid lp) lc arg als)::EC) gl Mem, tr)::nil)
| nsAdd : forall S M F B lc gl lc' gl' arg id t v1 v2 EC i1 i2 I' tr Mem als,
  getOperandValue v1 lc gl = Some (GV_int i1) ->
  getOperandValue v2 lc gl = Some (GV_int i2) ->
  getNextInsnFrom (insn_add id t v1 v2) B = Some I' ->
  updateEnv lc gl id (Some (GV_int (i1+i2))) = (lc', gl') -> 
  nsInsn 
    (mkState S M ((mkEC F B (insn_add id t v1 v2) lc arg als)::EC) gl Mem, tr) 
    ((mkState S M ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
| nsExtractValue : forall S M F B lc gl lc' gl' arg id t v gv gv' idxs EC I' Mem als tr,
  getOperandValue v lc gl = Some gv ->
  extractGenericValue lc gl gv idxs = Some gv' ->
  getNextInsnFrom (insn_extractvalue id t v idxs) B = Some I' ->
  updateEnv lc gl id (Some gv') = (lc', gl') -> 
  nsInsn 
    (mkState S M ((mkEC F B (insn_extractvalue id t v idxs) lc arg als)::EC) gl Mem, tr) 
    ((mkState S M ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
| nsInsertValue : forall S M F B lc gl lc' gl' arg id t v t' v' gv gv' gv'' idxs gvidxs EC I' Mem als tr,
  getOperandValue v lc gl = Some gv ->
  getOperandValue v' lc gl = Some gv' ->
  values2OpGVs idxs lc gl = gvidxs -> 
  insertGenericValue gv lc gl gvidxs gv' = Some gv'' ->
  getNextInsnFrom (insn_insertvalue id t v t' v' idxs) B = Some I' ->
  updateEnv lc gl id (Some gv'') = (lc', gl') -> 
  nsInsn 
    (mkState S M ((mkEC F B (insn_insertvalue id t v t' v' idxs) lc arg als)::EC) gl Mem, tr) 
    ((mkState S M ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
| nsAlloca : forall S TD Ps F B lc gl lc' gl' arg id t sz align EC I' Mem als Mem' tsz mb tr,
  getTypeAllocSize TD t = Some tsz ->
  malloc TD Mem (tsz * sz) align = Some (Mem', mb) ->
  getNextInsnFrom (insn_alloca id t sz align) B = Some I' ->
  updateEnv lc gl id (Some (GV_ptr (mb, 0))) = (lc', gl') -> 
  nsInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_alloca id t sz align) lc arg als)::EC) gl Mem, tr) 
    ((mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg (mb::als))::EC) gl' Mem', tr)::nil)
| nsLoad : forall S TD Ps F B lc gl lc' gl' arg id t v EC I' Mem als ma gv tr,
  getOperandValue v lc gl = Some (GV_ptr ma) ->
  load TD Mem ma t = Some gv ->
  updateEnv lc gl id (Some gv) = (lc', gl') -> 
  getNextInsnFrom (insn_load id t v) B = Some I' ->
  nsInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_load id t v) lc arg als)::EC) gl Mem, tr) 
    ((mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
| nsStore : forall S TD Ps F B lc gl lc' gl' arg t v1 v2 EC I' Mem als ma2 gv1 Mem' tr,
  getOperandValue v1 lc gl = Some gv1 ->
  getOperandValue v2 lc gl = Some (GV_ptr ma2) ->
  store TD Mem ma2 t gv1 = Some Mem' ->
  getNextInsnFrom (insn_store t v1 v2) B = Some I' ->
  nsInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_store t v1 v2) lc arg als)::EC) gl Mem, tr) 
    ((mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
| nsGEP : forall S TD Ps F B lc gl lc' gl' arg id t v idxs EC ma ma' I' Mem als tr,
  getOperandValue v lc gl = Some (GV_ptr ma) ->
  gep TD lc gl t ma idxs false = Some ma' ->
  getNextInsnFrom (insn_gep id t v idxs) B = Some I' ->
  updateEnv lc gl id (Some (GV_ptr ma')) = (lc', gl') -> 
  nsInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_gep id t v idxs) lc arg als)::EC) gl Mem, tr) 
    ((mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
| nsBGEP : forall S TD Ps F B lc gl lc' gl' arg id t v idxs EC ma ma' I' Mem als tr,
  getOperandValue v lc gl = Some (GV_ptr ma) ->
  gep TD lc gl t ma idxs true = Some ma' ->
  getNextInsnFrom (insn_bgep id t v idxs) B = Some I' ->
  updateEnv lc gl id (Some (GV_ptr ma')) = (lc', gl') -> 
  nsInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_bgep id t v idxs) lc arg als)::EC) gl Mem, tr) 
    ((mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
.

Definition ns_genInitState (S:system) (main:id) (Args:list GenericValue) : option States :=
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
          let Values := initLocals la Args in
          Some
            ((mkState
              S
              CurModule
              ((mkEC
                CurFunction 
                CurBB 
                CurInst
                Values 
                Args 
                nil
              )::nil)
              (genGlobal S main)
              (genMem S main),
              trace_nil
            )::nil)
        end
      end
    end
  end
end.

Fixpoint ns_isFinialState (states:States) : bool :=
match states with
| (mkState _ _ ((mkEC _ _ insn_return_void _ _ _)::nil) _ _, _)::states' => true
(* | (mkState _ _ ((mkEC _ _ (insn_return _ _) _ _ _)::nil) _ _, _)::states' => true *)
| (mkState _ _ _ _ _, _)::states' => ns_isFinialState states'
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
| ns_converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:States),
  ns_genInitState s main VarArgs = Some IS ->
  nsop_star IS FS ->
  ns_isFinialState FS ->
  ns_converges s main VarArgs FS
.

Inductive ns_diverges : system -> id -> list GenericValue -> list Trace -> Prop :=
| ns_diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS:States) trs,
  ns_genInitState s main VarArgs = Some IS ->
  nsop_diverges IS trs ->
  ns_diverges s main VarArgs trs
.

Inductive ns_goeswrong : system -> id -> list GenericValue -> States -> Prop :=
| ns_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:States),
  ns_genInitState s main VarArgs = Some IS ->
  nsop_star IS FS ->
  ~ ns_isFinialState FS ->
  ns_goeswrong s main VarArgs FS
.

(***************************************************************)
(* deterministic big-step *)

Inductive dbInsn : State -> State -> trace -> Prop :=
| dbBranch : forall S M F B lc gl arg Cond l1 l2 c
                              B' I' lc' Dest EC Mem als,   
  getOperandValue Cond lc gl = Some (GV_int c) ->
  Some Dest = (if c 
               then lookupBlockViaLabelFromSystem S l1
               else lookupBlockViaLabelFromSystem S l2) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B' = Some I' ->
  dbInsn 
    (mkState S M ((mkEC F B (insn_br Cond l1 l2) lc arg als)::EC) gl Mem)
    (mkState S M ((mkEC F B' I' lc' arg als)::EC) gl Mem)
    trace_nil 
| dbBranch_uncond : forall S M F B lc gl arg l
                              B' I' lc' Dest EC Mem als,   
  Some Dest = (lookupBlockViaLabelFromSystem S l) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B = Some I' ->
  dbInsn 
    (mkState S M ((mkEC F B (insn_br_uncond l) lc arg als)::EC) gl Mem)
    (mkState S M ((mkEC F B' I' lc' arg als)::EC) gl Mem)
    trace_nil 
| dbCall : forall S M F B lc gl arg rid rt fid lp gl' gl''
                       EC Result tr I' lc'' B' lc' oGV Mem Mem' als' als Mem'',
  dbFdef fid rt lp S M ((mkEC F B (insn_call rid rt fid lp) lc arg als)::EC) lc gl Mem lc' gl' als' Mem' B' Result tr ->
  getOperandValue Result lc' gl' = oGV -> 
  (lc'', gl'') = (if (rt =t= typ_void) 
                  then (lc, gl') 
                  else (updateEnv lc gl' rid oGV)) ->
  free_allocas Mem' als' = Some Mem'' ->
  getNextInsnFrom (insn_call rid rt fid lp) B = Some I' ->
  dbInsn 
    (mkState S M ((mkEC F B (insn_call rid rt fid lp) lc arg als)::EC) gl Mem) 
    (mkState S M ((mkEC F B I' lc'' arg als)::EC) gl'' Mem'') 
    tr
| dbAdd : forall S M F B lc gl lc' gl' arg id t v1 v2 EC i1 i2 I' Mem als,
  getOperandValue v1 lc gl = Some (GV_int i1) ->
  getOperandValue v2 lc gl = Some (GV_int i2) ->
  getNextInsnFrom (insn_add id t v1 v2) B = Some I' ->
  updateEnv lc gl id (Some (GV_int (i1+i2))) = (lc', gl') -> 
  dbInsn 
    (mkState S M ((mkEC F B (insn_add id t v1 v2) lc arg als)::EC) gl Mem) 
    (mkState S M ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil 
| dbExtractValue : forall S M F B lc gl lc' gl' arg id t v gv gv' idxs EC I' Mem als,
  getOperandValue v lc gl = Some gv ->
  extractGenericValue lc gl gv idxs = Some gv' ->
  getNextInsnFrom (insn_extractvalue id t v idxs) B = Some I' ->
  updateEnv lc gl id (Some gv') = (lc', gl') -> 
  dbInsn 
    (mkState S M ((mkEC F B (insn_extractvalue id t v idxs) lc arg als)::EC) gl Mem) 
    (mkState S M ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil 
| dbInsertValue : forall S M F B lc gl lc' gl' arg id t v t' v' gv gv' gv'' idxs gvidxs EC I' Mem als,
  getOperandValue v lc gl = Some gv ->
  getOperandValue v' lc gl = Some gv' ->
  values2OpGVs idxs lc gl = gvidxs -> 
  insertGenericValue gv lc gl gvidxs gv' = Some gv'' ->
  getNextInsnFrom (insn_insertvalue id t v t' v' idxs) B = Some I' ->
  updateEnv lc gl id (Some gv'') = (lc', gl') -> 
  dbInsn 
    (mkState S M ((mkEC F B (insn_insertvalue id t v t' v' idxs) lc arg als)::EC) gl Mem) 
    (mkState S M ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil 
| dbAlloca : forall S TD Ps F B lc gl lc' gl' arg id t sz align EC I' Mem als Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  malloc TD Mem (tsz * sz) align = Some (Mem', mb) ->
  getNextInsnFrom (insn_alloca id t sz align) B = Some I' ->
  updateEnv lc gl id (Some (GV_ptr (mb, 0))) = (lc', gl') -> 
  dbInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_alloca id t sz align) lc arg als)::EC) gl Mem) 
    (mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg (mb::als))::EC) gl' Mem')
    trace_nil
| dbLoad : forall S TD Ps F B lc gl lc' gl' arg id t v EC I' Mem als ma gv,
  getOperandValue v lc gl = Some (GV_ptr ma) ->
  load TD Mem ma t = Some gv ->
  updateEnv lc gl id (Some gv) = (lc', gl') -> 
  getNextInsnFrom (insn_load id t v) B = Some I' ->
  dbInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_load id t v) lc arg als)::EC) gl Mem) 
    (mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil
| dbStore : forall S TD Ps F B lc gl lc' gl' arg t v1 v2 EC I' Mem als ma2 gv1 Mem',
  getOperandValue v1 lc gl = Some gv1 ->
  getOperandValue v2 lc gl = Some (GV_ptr ma2) ->
  store TD Mem ma2 t gv1 = Some Mem' ->
  getNextInsnFrom (insn_store t v1 v2) B = Some I' ->
  dbInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_store t v1 v2) lc arg als)::EC) gl Mem) 
    (mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil
| dbGEP : forall S TD Ps F B lc gl lc' gl' arg id t v idxs EC ma ma' I' Mem als,
  getOperandValue v lc gl = Some (GV_ptr ma) ->
  gep TD lc gl t ma idxs false = Some ma' ->
  getNextInsnFrom (insn_gep id t v idxs) B = Some I' ->
  updateEnv lc gl id (Some (GV_ptr ma')) = (lc', gl') -> 
  dbInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_gep id t v idxs) lc arg als)::EC) gl Mem) 
    (mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil 
| dbBGEP : forall S TD Ps F B lc gl lc' gl' arg id t v idxs EC ma ma' I' Mem als,
  getOperandValue v lc gl = Some (GV_ptr ma) ->
  gep TD lc gl t ma idxs true = Some ma' ->
  getNextInsnFrom (insn_bgep id t v idxs) B = Some I' ->
  updateEnv lc gl id (Some (GV_ptr ma')) = (lc', gl') -> 
  dbInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_bgep id t v idxs) lc arg als)::EC) gl Mem) 
    (mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem)
    trace_nil 
with dbop : State -> State -> trace -> Prop :=
| dbop_nil : forall S, dbop S S trace_nil
| dbop_cons : forall S1 S2 S3 t1 t2,
    dbInsn S1 S2 t1 ->
    dbop S2 S3 t2 ->
    dbop S1 S3 (trace_app t1 t2)
with dbFdef : id -> typ -> list_param -> system -> module -> list ExecutionContext -> GVMap -> GVMap -> mem -> GVMap -> GVMap -> list mblock -> mem -> block -> value -> trace -> Prop :=
| dbFdef_intro : forall S M gl fid lp lc
                            B' I' rt la lb B'' Result lc' gl' tr ECs Mem Mem' als',
  lookupFdefViaIDFromSystemC S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some B' ->
  getEntryInsn B' = Some I' ->
  dbop 
    (mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             B' I' (initLocals la (params2GVs lp lc gl))
                            (params2GVs lp lc gl) nil)::ECs) gl Mem)
    (mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             B'' (insn_return rt Result) lc'
                            (params2GVs lp lc gl) als')::ECs) gl' Mem')
    tr ->
  dbFdef fid rt lp S M ECs lc gl Mem lc' gl' als' Mem' B'' Result tr
.

CoInductive dbInsnInf : State -> Trace -> Prop :=
| dbCallInsnInf : forall S M F B lc gl arg rid rt fid lp
                       EC tr Mem als,
  dbFdefInf fid rt lp S M ((mkEC F B (insn_call rid rt fid lp) lc arg als)::EC) lc gl Mem tr ->
  dbInsnInf 
    (mkState S M ((mkEC F B (insn_call rid rt fid lp) lc arg als)::EC) gl Mem) 
    tr
with dbopInf : State -> Trace -> Prop :=
| dbopInf_insn : forall state1 t1,
    dbInsnInf state1 t1 ->
    dbopInf state1 t1
| dbopInf_cons : forall state1 state2 t1 t2,
    dbInsn state1 state2 t1 ->
    dbopInf state2 t2 ->
    dbopInf state1 (Trace_app t1 t2)
with dbFdefInf : id -> typ -> list_param -> system -> module -> list ExecutionContext -> GVMap -> GVMap -> mem -> Trace -> Prop :=
| dbFdefInf_intro : forall S M lc gl fid lp
                           B' I' rt la lb tr ECs Mem,
  lookupFdefViaIDFromSystemC S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some B' ->
  getEntryInsn B' = Some I' ->
  dbopInf 
    (mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) B' I' 
                        (initLocals la (params2GVs lp lc gl)) 
                        (params2GVs lp lc gl) nil)::ECs) gl Mem)
    tr ->
  dbFdefInf fid rt lp S M ECs lc gl Mem tr
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

Inductive db_diverges : system -> id -> list GenericValue -> Trace -> Prop :=
| db_diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS S:State) tr,
  db_genInitState s main VarArgs = Some IS ->
  dbopInf IS tr ->
  db_diverges s main VarArgs tr
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

Fixpoint returnStatesFromOp S M ECs lp lc gl rt fid la lb 
  (lc_gl_als_Mem_block_re_trs : list (GVMap*GVMap*list mblock*mem*block*value*trace)) : States :=
match lc_gl_als_Mem_block_re_trs with
| nil => nil
| (lc', gl', als', Mem', B'', re, tr')::lc_gl_als_Mem_block_re_trs' => 
    (mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             B'' (insn_return rt re) lc'
                            (params2GVs lp lc gl) als')::ECs) gl' Mem', tr')::
    (returnStatesFromOp S M ECs lp lc gl rt fid la lb lc_gl_als_Mem_block_re_trs')
end.

Fixpoint updateStatesFromReturns S M F B I' lc t arg als EC rid 
  (lc_gl_als_Mem_block_re_trs : list (GVMap*GVMap*list mblock*mem*block*value*trace)): option States :=
match lc_gl_als_Mem_block_re_trs with 
| nil => Some nil
| (lc', gl', als', Mem', B', re, tr)::lc_gl_als_Mem_block_re_trs' => 
  let ogv := getOperandValue re lc' gl' in 
  let (lc'', gl'') := (if (t =t= typ_void) 
                      then (lc, gl') 
                      else (updateEnv lc gl' rid ogv)) in
  match (free_allocas Mem' als') with
  | Some Mem'' =>
    match (updateStatesFromReturns S M F B I' lc t arg als EC rid lc_gl_als_Mem_block_re_trs') with
    | Some states => Some ((mkState S M ((mkEC F B I' lc'' arg als)::EC) gl'' Mem'', tr)::states)
    | None => None
    end
  | None => None
  end
end.

Inductive nbInsn : State*trace -> States -> Prop :=
| nbBranch_def : forall S M F B lc gl arg  Cond l1 l2 c
                              B' I' lc' Dest EC tr Mem als,   
  getOperandValue Cond lc gl = Some (GV_int c) ->
  Some Dest = (if c 
               then lookupBlockViaLabelFromSystem S l1
               else lookupBlockViaLabelFromSystem S l2) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B' = Some I' ->
  nbInsn 
    (mkState S M ((mkEC F B (insn_br Cond l1 l2) lc arg als)::EC) gl Mem, tr)
    ((mkState S M ((mkEC F B' I' lc' arg als)::EC) gl Mem, tr)::nil)
| nbBranch_undef : forall S M F B lc arg Cond l1 l2
                              B1' I1' lc1' B2' I2' lc2' Dest1 Dest2 EC tr gl Mem als,   
  getOperandValue Cond lc gl = Some GV_undef ->
  Some Dest1 = lookupBlockViaLabelFromSystem S l1 ->
  Some Dest2 = lookupBlockViaLabelFromSystem S l2 ->
  (B1', lc1') = (switchToNewBasicBlock Dest1 B lc) ->
  (B2', lc2') = (switchToNewBasicBlock Dest2 B lc) ->
  getEntryInsn B1' = Some I1' ->
  getEntryInsn B2' = Some I2' ->
  nbInsn 
    (mkState S M ((mkEC F B (insn_br Cond l1 l2) lc arg als)::EC) gl Mem, tr)
    ((mkState S M ((mkEC F B1' I1' lc1' arg als)::EC) gl Mem, tr)::
     (mkState S M ((mkEC F B2' I2' lc2' arg als)::EC) gl Mem, tr)::nil)
| nbBranch_uncond : forall S M F B lc gl arg l
                              B' I' lc' Dest EC tr Mem als,   
  Some Dest = (lookupBlockViaLabelFromSystem S l) ->
  (B', lc') = (switchToNewBasicBlock Dest B lc) ->
  getEntryInsn B = Some I' ->
  nbInsn 
    (mkState S M ((mkEC F B (insn_br_uncond l) lc arg als)::EC) gl Mem, tr)
    ((mkState S M ((mkEC F B' I' lc' arg als)::EC) gl Mem, tr)::nil)
| nbCall : forall S M F B lc gl arg rid rt fid lp
                            EC tr lc_gl_als_Mem_block_re_trs I' Mem als states, 
  nbFdef fid rt lp S M ((mkEC F B (insn_call rid rt fid lp) lc arg als)::EC) lc gl Mem tr lc_gl_als_Mem_block_re_trs ->
  getNextInsnFrom (insn_call rid rt fid lp) B = Some I' ->
  updateStatesFromReturns S M F B I' lc rt arg als EC rid lc_gl_als_Mem_block_re_trs = Some states ->
  nbInsn 
    (mkState S M ((mkEC F B (insn_call rid rt fid lp) lc arg als)::EC) gl Mem, tr) states    
| nbAdd : forall S M F B lc gl lc' gl' arg id t v1 v2 EC i1 i2 I' tr Mem als,
  getOperandValue v1 lc gl = Some (GV_int i1) ->
  getOperandValue v2 lc gl = Some (GV_int i2) ->
  getNextInsnFrom (insn_add id t v1 v2) B = Some I' ->
  updateEnv lc gl id (Some (GV_int (i1+i2))) = (lc', gl') -> 
  nbInsn 
    (mkState S M ((mkEC F B (insn_add id t v1 v2) lc arg als)::EC) gl Mem, tr) 
    ((mkState S M ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
| nbExtractValue : forall S M F B lc gl lc' gl' arg id t v gv gv' idxs EC I' Mem als tr,
  getOperandValue v lc gl = Some gv ->
  extractGenericValue lc gl gv idxs = Some gv' ->
  getNextInsnFrom (insn_extractvalue id t v idxs) B = Some I' ->
  updateEnv lc gl id (Some gv') = (lc', gl') -> 
  nbInsn 
    (mkState S M ((mkEC F B (insn_extractvalue id t v idxs) lc arg als)::EC) gl Mem, tr) 
    ((mkState S M ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
| nbInsertValue : forall S M F B lc gl lc' gl' arg id t v t' v' gv gv' gv'' idxs gvidxs EC I' Mem als tr,
  getOperandValue v lc gl = Some gv ->
  getOperandValue v' lc gl = Some gv' ->
  values2OpGVs idxs lc gl = gvidxs -> 
  insertGenericValue gv lc gl gvidxs gv' = Some gv'' ->
  getNextInsnFrom (insn_insertvalue id t v t' v' idxs) B = Some I' ->
  updateEnv lc gl id (Some gv'') = (lc', gl') -> 
  nbInsn 
    (mkState S M ((mkEC F B (insn_insertvalue id t v t' v' idxs) lc arg als)::EC) gl Mem, tr) 
    ((mkState S M ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
| nbAlloca : forall S TD Ps F B lc gl lc' gl' arg id t sz align EC I' Mem als Mem' tsz mb tr,
  getTypeAllocSize TD t = Some tsz ->
  malloc TD Mem (tsz * sz) align = Some (Mem', mb) ->
  getNextInsnFrom (insn_alloca id t sz align) B = Some I' ->
  updateEnv lc gl id (Some (GV_ptr (mb, 0))) = (lc', gl') -> 
  nbInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_alloca id t sz align) lc arg als)::EC) gl Mem, tr) 
    ((mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg (mb::als))::EC) gl' Mem', tr)::nil)
| nbLoad : forall S TD Ps F B lc gl lc' gl' arg id t v EC I' Mem als ma gv tr,
  getOperandValue v lc gl = Some (GV_ptr ma) ->
  load TD Mem ma t = Some gv ->
  updateEnv lc gl id (Some gv) = (lc', gl') -> 
  getNextInsnFrom (insn_load id t v) B = Some I' ->
  nbInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_load id t v) lc arg als)::EC) gl Mem, tr) 
    ((mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
| nbStore : forall S TD Ps F B lc gl lc' gl' arg t v1 v2 EC I' Mem als ma2 gv1 Mem' tr,
  getOperandValue v1 lc gl = Some gv1 ->
  getOperandValue v2 lc gl = Some (GV_ptr ma2) ->
  store TD Mem ma2 t gv1 = Some Mem' ->
  getNextInsnFrom (insn_store t v1 v2) B = Some I' ->
  nbInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_store t v1 v2) lc arg als)::EC) gl Mem, tr) 
    ((mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
| nbGEP : forall S TD Ps F B lc gl lc' gl' arg id t v idxs EC ma ma' I' Mem als tr,
  getOperandValue v lc gl = Some (GV_ptr ma) ->
  gep TD lc gl t ma idxs false = Some ma' ->
  getNextInsnFrom (insn_gep id t v idxs) B = Some I' ->
  updateEnv lc gl id (Some (GV_ptr ma')) = (lc', gl') -> 
  nbInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_gep id t v idxs) lc arg als)::EC) gl Mem, tr) 
    ((mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
| nbBGEP : forall S TD Ps F B lc gl lc' gl' arg id t v idxs EC ma ma' I' Mem als tr,
  getOperandValue v lc gl = Some (GV_ptr ma) ->
  gep TD lc gl t ma idxs true = Some ma' ->
  getNextInsnFrom (insn_bgep id t v idxs) B = Some I' ->
  updateEnv lc gl id (Some (GV_ptr ma')) = (lc', gl') -> 
  nbInsn 
    (mkState S (module_intro TD Ps) ((mkEC F B (insn_bgep id t v idxs) lc arg als)::EC) gl Mem, tr) 
    ((mkState S (module_intro TD Ps) ((mkEC F B I' lc' arg als)::EC) gl' Mem, tr)::nil)
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
with nbFdef : id -> typ -> list_param -> system -> module -> list ExecutionContext -> GVMap -> GVMap -> mem -> trace -> list (GVMap*GVMap*list mblock*mem*block*value*trace) -> Prop :=
| nbFdef_intro : forall S M lc gl fid lp
                            B' I' rt la lb tr lc_gl_als_Mem_block_re_trs ECs Mem,
  lookupFdefViaIDFromSystemC S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some B' ->
  getEntryInsn B' = Some I' ->
  nbop_star 
    ((mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                         B' I' (initLocals la (params2GVs lp lc gl)) 
                         (params2GVs lp lc gl) nil)::ECs) gl Mem, tr)::nil)
    (returnStatesFromOp S M ECs lp lc gl rt fid la lb lc_gl_als_Mem_block_re_trs) ->
  nbFdef fid rt lp S M ECs lc gl Mem tr lc_gl_als_Mem_block_re_trs
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
| nbCallInsnInf : forall S M F B lc gl arg rid rt fid lp
                            EC tr trs Mem als, 
  nbFdefInf fid rt lp S M 
    ((mkEC F B (insn_call rid rt fid lp) lc arg als)::EC)      
    lc gl Mem tr trs ->
  nbInsnInf 
    (mkState S M ((mkEC F B (insn_call rid rt fid lp) lc arg als)::EC) gl Mem, tr)
    trs
with nbopInf : States -> list Trace -> Prop :=
| nbopInf_cons : forall state_tr states tr1 tr2,
  nbInsnInf state_tr tr1 ->
  nbopInf states tr2 ->
  nbopInf (state_tr::states) (tr1++tr2)
| nbopInf_trans : forall states1 states2 trs,
  nbop_plus states1 states2 ->
  nbopInf states2 trs ->
  nbopInf states1 trs 
with nbFdefInf : id -> typ -> list_param -> system -> module -> list ExecutionContext -> GVMap -> GVMap -> mem -> trace -> list Trace -> Prop :=
| nbFdefInf_intro : forall S M lc gl fid lp
                            B' I' ECs rt la lb tr trs' Mem,
  lookupFdefViaIDFromSystemC S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some B' ->
  getEntryInsn B' = Some I' ->
  nbopInf 
    ((mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                          B' I' (initLocals la (params2GVs lp lc gl)) 
                          (params2GVs lp lc gl) nil)::ECs) gl Mem, tr)::nil) 
    trs' ->
  nbFdefInf fid rt lp S M ECs lc gl Mem tr trs'
.

Definition nb_genInitState := ns_genInitState.
Definition nb_isFinialState := ns_isFinialState.

Inductive nb_converges : system -> id -> list GenericValue -> States -> Prop :=
| nb_converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:States),
  nb_genInitState s main VarArgs = Some IS ->
  nbop_star IS FS ->
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
  [ c "dbBranch" | c "dbBranch_uncond" | c "dbCallInsn" |
    c "dbAdd" | c "dbExtractValue" | c "dbInsertValue" |
    c "dbAlloca" | c "dbLoad" | c "dbStore" | c "dbGEP" | c "dbBGEP" |
    c "dbop_nil" | c "dbop_cons" | c "dbFdef_intro" ].

Tactic Notation "dsInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "dsReturn" | c "dsBranch" | c "dsBranch_uncond" | c "dsCall" |
    c "dsAdd" | c "dsExtractValue" | c "dsInsertValue" |
    c "dsAlloca" | c "dsLoad" | c "dsStore" | c "dsGEP" | c "dsBGEP" ].

Tactic Notation "dsop_star_cases" tactic(first) tactic(c) :=
  first;
  [ c "dsop_star_nil" | c "dsop_star_cons" ].

Tactic Notation "nb_mutind_cases" tactic(first) tactic(c) :=
  first;
  [ c "nbBranch_def" | c "nbBranch_undef" | c "nbBranch_uncond" | c "nbCall" |
    c "nbAdd" | c "nbExtractValue" | c "nbInsertValue" |
    c "nbAlloca" | c "nbLoad" | c "nbStore" | c "nbGEP" | c "nbBGEP" |
    c "nbop_star_nil" | c "nbop_star_refl" | c "nbop_star_cons" | 
    c "nbop_star_trans" | c "nbFdef_intro" ].

Tactic Notation "nsInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "nsReturn" | c "nsBranch_def" | c "nsBranch_undef" | 
    c "nsBranch_uncond" | c "nsCall" | c "nsAdd" | c "nsExtractValue" | c "nsInsertValue" |
    c "nsAlloca" | c "nsLoad" | c "nsStore" | c "nsGEP" | c "nsBGEP" ].

Tactic Notation "nsop_star_cases" tactic(first) tactic(c) :=
  first;
  [ c "nsop_star_nil" | c "nsop_star_refl" | 
    c "nsop_star_cons" | c "nsop_star_trans" ].

Tactic Notation "nsop_plus_cases" tactic(first) tactic(c) :=
  first;
  [ c "nsop_plus_cons" | c "nsop_plus_trans" ].


Hint Constructors dbInsn dbop dbFdef dsInsn dsop_star dsop_diverges dsop_plus
                  nbInsn nbop_star nbop_plus nbFdef nsInsn nsop_star nsop_diverges nsop_plus.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../monads" "-I" "../ott" "-I" "../") ***
*** End: ***
 *)
