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
Require Import Ensembles.
Require Import ssa_dynamic.

Module NDopsem.

Export LLVMsyntax.
Export LLVMlib.
Export LLVMgv.
Export LLVMtd.

Definition GVs := Ensemble GenericValue.
Definition GVsMap := list (id * GVs).

(**************************************)
(** Execution contexts *)

Record ExecutionContext : Type := mkEC {
CurFunction : fdef;
CurBB       : block;
CurCmds     : cmds;                  (* cmds to run within CurBB *)
Terminator  : terminator;
Locals      : GVsMap;                (* LLVM values used in this invocation *)
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

Lemma singleton_inhabited : forall U (x:U), Inhabited U (Singleton U x).
Proof.
  intros. apply Inhabited_intro with (x:=x); auto using In_singleton.
Qed.

Lemma full_set_inhabited : Inhabited GenericValue (Full_set GenericValue).
Proof.
  intros. apply Inhabited_intro with (x:=nil); auto using Full_intro.
Qed.

Definition gv2gvs (gv:GenericValue) : GVs :=
match gv with
| (Vundef, _)::_ => Full_set _
| _ => Singleton GenericValue gv
end.

Notation "$ gv $" := (gv2gvs gv) (at level 41).
Notation "% ogv %" := (mmap GenericValue GVs gv2gvs ogv) (at level 41).
Notation "gv @ gvs" := (Ensembles.In GenericValue gvs gv) 
                         (at level 43, right associativity).

Definition getOperandValue (TD:TargetData) (v:value) (locals:GVsMap) 
  (globals:GVMap) : option GVs := 
match v with
| value_id id => lookupAL _ locals id 
| value_const c => % (const2GV TD globals c) %
end.

Definition returnUpdateLocals (TD:TargetData) (c':cmd) (Result:value) 
  (lc lc':GVsMap) (gl:GVMap) : option GVsMap :=
  match (getOperandValue TD Result lc gl) with
  | Some gr =>    
      match (getCallerReturnID c') with
      | Some id0 => Some (updateAddAL _ lc' id0 gr)
      | None => Some lc'
      end
  | None => None
  end.

Fixpoint getIncomingValuesForBlockFromPHINodes (TD:TargetData)
  (PNs:list phinode) (b:block) (globals:GVMap) (locals:GVsMap) : 
  option (list (id*GVs)) :=
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

Fixpoint updateValuesForNewBlock (ResultValues:list (id*GVs)) (locals:GVsMap) 
  : GVsMap :=
match ResultValues with
| nil => locals
| (id, v)::ResultValues' => 
    updateAddAL _ (updateValuesForNewBlock ResultValues' locals) id v
end.

Definition switchToNewBasicBlock (TD:TargetData) (Dest:block) 
  (PrevBB:block) (globals: GVMap) (locals:GVsMap): option GVsMap :=
  let PNs := getPHINodesFromBlock Dest in
  match getIncomingValuesForBlockFromPHINodes TD PNs PrevBB globals locals with
  | Some ResultValues => Some (updateValuesForNewBlock ResultValues locals)
  | None => None
  end.

Lemma gv_in_gv2gvs : forall gv, gv @ $ gv $.
Proof.
  intros.
  destruct gv; simpl.
    apply In_singleton; auto.
    destruct p; simpl.
    destruct v; simpl; auto using In_singleton.
      apply Full_intro.
Qed.

Definition lift_op2 (f: GenericValue -> GenericValue -> option GenericValue)
  gvs1 gvs2 : GVs :=
  fun gv3 => exists gv1, exists gv2, exists gv3',
    gv1 @ gvs1 /\ gv2 @ gvs2 /\ f gv1 gv2 = Some gv3' /\ (gv3 @ $ gv3' $).

Definition BOP (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:bop) (bsz:sz) 
  (v1 v2:value) : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) => Some (lift_op2 (mbop TD op bsz) gvs1 gvs2)
| _ => None
end
.

Definition lift_op1 (f: GenericValue -> option GenericValue) gvs1 : GVs :=
  fun gv2 => exists gv1, exists gv2', 
    gv1 @ gvs1 /\ f gv1 = Some gv2' /\ (gv2 @ $ gv2' $).

Definition CAST (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:castop) 
  (t1:typ) (v1:value) (t2:typ) : option GVs:=
match (getOperandValue TD v1 lc gl) with
| (Some gvs1) => Some (lift_op1 (mcast TD op t1 t2) gvs1)
| _ => None
end
.

Fixpoint values2GVs (TD:TargetData) (lv:list_value) (locals:GVsMap) 
  (globals:GVMap) : option (list GVs):=
match lv with
| Nil_list_value => Some nil
| Cons_list_value v lv' => 
  match (getOperandValue TD v locals globals) with
  | Some GV => 
    match (values2GVs TD lv' locals globals) with
    | Some GVs => Some (GV::GVs)
    | None => None
    end
  | None => None
  end
end.

Fixpoint in_list_gvs (l1 : list GenericValue) (l2 : list GVs) :=
match l1, l2 with
| nil, nil => True
| gv1::l1', gvs2::l2' => gv1 @ gvs2 /\ in_list_gvs l1' l2'
| _, _ => False
end.

Notation "vidxs @@ vidxss" := (in_list_gvs vidxs vidxss) 
  (at level 43, right associativity).

Definition GEP (TD:TargetData) (t:typ) (mas:GVs) (vidxss:list GVs) 
  (inbounds:bool) : option GVs :=
  Some (fun gv => exists ma, exists vidxs, ma @ mas /\ vidxs @@ vidxss /\
        LLVMgv.GEP TD t ma vidxs inbounds = Some gv).

Fixpoint params2GVs (TD:TargetData) (lp:params) (locals:GVsMap) (globals:GVMap) :
 option (list GVs) :=
match lp with
| nil => Some nil
| (_, v)::lp' => 
    match (getOperandValue TD v locals globals, 
           params2GVs TD lp' locals globals) with
    | (Some gv, Some gvs) => Some (gv::gvs)
    | _ => None
    end
end.

Fixpoint _initializeFrameValues (la:args) (lg:list GVs) (locals:GVsMap) 
  : GVsMap :=
match (la, lg) with
| ((_, id)::la', g::lg') => 
  updateAddAL _ (_initializeFrameValues la' lg' locals) id g
| ((t, id)::la', nil) => 
  (* FIXME: We should initalize them w.r.t their type size. *)
  updateAddAL _ (_initializeFrameValues la' nil locals) id (Full_set _)
| _ => locals
end.

Definition initLocals (la:args) (lg:list GVs): GVsMap := 
_initializeFrameValues la lg nil.

Definition lookupFdefViaPtr Ps fs fptr : option fdef :=
  do fn <- LLVMopsem.lookupFdefViaGVFromFunTable fs fptr;
     lookupFdefViaIDFromProducts Ps fn.

Inductive sInsn : State -> State -> trace -> Prop :=
| sReturn : forall S TD Ps F B rid RetTy Result lc gl fs
                            F' B' c' cs' tmn' lc' EC
                            Mem Mem' als als' lc'',   
  Instruction.isCallInst c' = true ->
  (* FIXME: we should get Result before free?! *)
  free_allocas TD Mem als = Some Mem' ->
  returnUpdateLocals TD c' Result lc lc' gl = Some lc'' ->
  sInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_return rid RetTy Result) lc als)::
                      (mkEC F' B' (c'::cs') tmn' lc' als')::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC F' B' cs' tmn' lc'' als')::EC) gl fs Mem')
    trace_nil 

| sReturnVoid : forall S TD Ps F B rid lc gl fs
                            F' B' c' tmn' lc' EC
                            cs' Mem Mem' als als',   
  Instruction.isCallInst c' = true ->
  free_allocas TD Mem als = Some Mem' ->
  getCallerReturnID c' = None ->
  sInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_return_void rid) lc als)::
                      (mkEC F' B' (c'::cs') tmn' lc' als')::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC F' B' cs' tmn' lc' als')::EC) gl fs Mem')
    trace_nil 

| sBranch : forall S TD Ps F B lc gl fs bid Cond l1 l2 conds c
                              l' ps' cs' tmn' lc' EC Mem als,   
  getOperandValue TD Cond lc gl = Some conds ->
  c @ conds ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  sInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br bid Cond l1 l2) lc als)::EC) 
                       gl fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' als)
                       ::EC) gl fs Mem)
    trace_nil 

| sBranch_uncond : forall S TD Ps F B lc gl fs bid l 
                           l' ps' cs' tmn' lc' EC Mem als,   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  sInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br_uncond bid l) lc als)::EC) 
                       gl fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' als)
                       ::EC) gl fs Mem)
    trace_nil 

| sBop: forall S TD Ps F B lc gl fs id bop sz v1 v2 gvs3 EC cs tmn Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gvs3 ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gvs3) als)::EC) 
                      gl fs Mem)
    trace_nil 

(*
| sFBop: forall S TD Ps F B lc gl fs id fbop fp v1 v2 gv3 EC cs tmn Mem als,
  FBOP TD lc gl fbop fp v1 v2 = Some gv3 ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                      gl fs Mem)
    trace_nil 

| sExtractValue : forall S TD Ps F B lc gl fs id t v gv gv' idxs EC cs tmn 
                          Mem als,
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_extractvalue id t v idxs)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv') als)::EC) 
                       gl fs Mem)
    trace_nil 

| sInsertValue : forall S TD Ps F B lc gl fs id t v t' v' gv gv' gv'' idxs 
                         EC cs tmn Mem als,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_insertvalue id t v t' v' idxs)::cs) tmn 
                       lc als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv'') als)::EC) 
                       gl fs Mem)
    trace_nil 

*)
| sMalloc : forall S TD Ps F B lc gl fs id t v gns gn align EC cs tmn Mem als 
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_malloc id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn 
                        (updateAddAL _ lc id ($ (blk2GV TD mb) $)) 
                      als)::EC) gl fs Mem')
    trace_nil

| sFree : forall S TD Ps F B lc gl fs fid t v EC cs tmn Mem als Mem' mptrs mptr,
  getOperandValue TD v lc gl = Some mptrs ->
  mptr @ mptrs ->
  free TD Mem mptr = Some Mem'->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_free fid t v)::cs) tmn lc als)::EC) 
                       gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) gl fs Mem')
    trace_nil

| sAlloca : forall S TD Ps F B lc gl fs id t v gns gn align EC cs tmn Mem als 
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_alloca id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn 
                        (updateAddAL _ lc id ($ (blk2GV TD mb) $)) 
                      (mb::als))::EC) gl fs Mem')
    trace_nil

| sLoad : forall S TD Ps F B lc gl fs id t align v EC cs tmn Mem als mps mp gv,
  getOperandValue TD v lc gl = Some mps ->
  mp @ mps ->
  mload TD Mem mp t align = Some gv ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_load id t v align)::cs) tmn lc als)::
                       EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id ($ gv $)) als)::EC) 
                       gl fs Mem)
    trace_nil

| sStore : forall S TD Ps F B lc gl fs sid t align v1 v2 EC cs tmn Mem als 
                   mp2 gv1 Mem' gvs1 mps2,
  getOperandValue TD v1 lc gl = Some gvs1 ->
  getOperandValue TD v2 lc gl = Some mps2 ->
  gv1 @ gvs1 -> mp2 @ mps2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_store sid t v1 v2 align)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) gl fs Mem')
    trace_nil

| sGEP : forall S TD Ps F B lc gl fs id inbounds t v idxs vidxs EC mp mp' 
                 cs tmn Mem als,
  getOperandValue TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxs ->
  GEP TD t mp vidxs inbounds = Some mp' ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_gep id inbounds t v idxs)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id mp') als)::EC) 
                       gl fs Mem)
    trace_nil 
(*
| sTrunc : forall S TD Ps F B lc gl fs id truncop t1 v1 t2 gv2 EC cs tmn 
                   Mem als,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gv2 ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                       gl fs Mem)
    trace_nil

| sExt : forall S TD Ps F B lc gl fs id extop t1 v1 t2 gv2 EC cs tmn Mem 
                 als,
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                       gl fs Mem)
    trace_nil
*)
| sCast : forall S TD Ps F B lc gl fs id castop t1 v1 t2 gv2 EC cs tmn Mem 
                  als,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_cast id castop t1 v1 t2)::cs) tmn lc 
                      als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv2) als)::EC) 
                      gl fs Mem)
    trace_nil
(*
| sIcmp : forall S TD Ps F B lc gl fs id cond t v1 v2 gv3 EC cs tmn Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem)
    trace_nil

| sFcmp : forall S TD Ps F B lc gl fs id fcond fp v1 v2 gv3 EC cs tmn Mem 
                  als,
  FCMP TD lc gl fcond fp v1 v2 = Some gv3 ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gv3) als)::EC) 
                       gl fs Mem)
    trace_nil

| sSelect : forall S TD Ps F B lc gl fs id v0 t v1 v2 c EC cs tmn Mem als 
                    gv1 gv2,
  getOperandValue TD v0 lc gl = Some c ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (if isGVZero TD c 
                                        then updateAddAL _ lc id gv2 
                                        else updateAddAL _ lc id gv1) als)
                      ::EC) gl fs Mem)
    trace_nil
*)
| sCall : forall S TD Ps F B lc gl fs rid noret ca fid fv lp cs tmn fptrs fptr
                       l' ps' cs' tmn' EC rt la va lb Mem als ft fa gvs,
  (* only look up the current module for the time being, 
     do not support linkage. *)
  getOperandValue TD fv lc gl = Some fptrs -> 
  fptr @ fptrs -> 
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                       (block_intro l' ps' cs' tmn') cs' tmn' 
                       (initLocals la gvs) 
                       nil)::
                      (mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem)
    trace_nil 
(*
| sExCall : forall S TD Ps F B lc gl fs rid noret ca fid fv lp cs tmn EC 
                    rt la Mem als oresult Mem' lc' va ft fa gvs,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  lookupExFdecViaGV TD Ps gl lc fs fv = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  params2GVs TD lp lc gl = Some gvs ->
  callExternalFunction Mem fid gvs = Some (oresult, Mem') ->
  exCallUpdateLocals noret rid oresult lc = Some lc' ->
  sInsn 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC F B cs tmn lc' als)::EC) gl fs Mem')
    trace_nil 
*).

Hint Constructors sInsn.

Definition s_genInitState (S:system) (main:id) (Args:list GVs) (initmem:mem) 
  : option State :=
match (lookupFdefViaIDFromSystem S main) with
| None => None
| Some CurFunction =>
  match (getParentOfFdefFromSystem CurFunction S) with
  | None => None
  | Some (module_intro CurLayouts CurNamedts CurProducts) =>
    let initargetdata := 
      LLVMopsem.initTargetData CurLayouts CurNamedts initmem in 
    match (LLVMopsem.genGlobalAndInitMem initargetdata CurProducts nil nil 
      initmem) with
    | None => None
    | Some (initGlobal, initFunTable, initMem) =>
      match (getEntryBlock CurFunction) with
      | None => None
      | Some (block_intro l ps cs tmn) => 
          match CurFunction with 
          | fdef_intro (fheader_intro _ rt _ la _) _ =>
            let Values := initLocals la Args in
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
        end
      end
    end
  end
end.

Definition s_isFinialState (state:State) : bool :=
match state with
| (mkState _ _ _ ((mkEC _ _ nil (insn_return_void _) _ _)::nil) _ _ _) => true
| (mkState _ _ _ ((mkEC _ _ nil (insn_return _ _ _) _ _)::nil) _ _ _) => true 
| _ => false
end.

Inductive sop_star : State -> State -> trace -> Prop :=
| sop_star_nil : forall state, sop_star state state trace_nil
| sop_star_cons : forall state1 state2 state3 tr1 tr2,
    sInsn state1 state2 tr1 ->
    sop_star state2 state3 tr2 ->
    sop_star state1 state3 (trace_app tr1 tr2)
.

Inductive sop_plus : State -> State -> trace -> Prop :=
| sop_plus_cons : forall state1 state2 state3 tr1 tr2,
    sInsn state1 state2 tr1 ->
    sop_star state2 state3 tr2 ->
    sop_plus state1 state3 (trace_app tr1 tr2)
.

CoInductive sop_diverges : State -> Trace -> Prop :=
| sop_diverges_intro : forall state1 state2 tr1 tr2,
    sop_plus state1 state2 tr1 ->
    sop_diverges state2 tr2 ->
    sop_diverges state1 (Trace_app tr1 tr2)
.

Inductive s_converges : system -> id -> list GVs -> State -> Prop :=
| s_converges_intro : forall (s:system) (main:id) (VarArgs:list GVs) 
                              (IS FS:State) tr,
  s_genInitState s main VarArgs Mem.empty = Some IS ->
  sop_star IS FS tr ->
  s_isFinialState FS ->
  s_converges s main VarArgs FS
.

Inductive s_diverges : system -> id -> list GVs -> Trace -> Prop :=
| s_diverges_intro : forall (s:system) (main:id) (VarArgs:list GVs) 
                             (IS:State) tr,
  s_genInitState s main VarArgs Mem.empty = Some IS ->
  sop_diverges IS tr ->
  s_diverges s main VarArgs tr
.

Inductive s_goeswrong : system -> id -> list GVs -> State -> Prop :=
| s_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GVs) 
                              (IS FS:State) tr,
  s_genInitState s main VarArgs Mem.empty = Some IS ->
  sop_star IS FS tr ->
  ~ s_isFinialState FS ->
  s_goeswrong s main VarArgs FS
.

Fixpoint instantiate_locals (lc1 : GVMap) (lc2 : GVsMap) : Prop :=
match lc1, lc2 with
| nil, nil => True
| (id1,gv1)::lc1', (id2,gvs2)::lc2' => 
    id1=id2 /\ gv1 @ gvs2 /\ instantiate_locals lc1' lc2'
| _, _ => False
end.

Definition instantiate_EC (ec1 : LLVMopsem.ExecutionContext) 
  (ec2 : ExecutionContext) : Prop :=
match ec1, ec2 with
| LLVMopsem.mkEC f1 b1 cs1 tmn1 lc1 als1, mkEC f2 b2 cs2 tmn2 lc2 als2 =>
    f1 = f2 /\ b1 = b2 /\ cs1 = cs2 /\ tmn1 = tmn2 /\
    instantiate_locals lc1 lc2 /\ als1 = als2
end.

Fixpoint instantiate_ECs (ecs1 : LLVMopsem.ECStack) (ecs2 : ECStack) : Prop :=
match ecs1, ecs2 with
| nil, nil => True
| ec1::ecs1', ec2::ecs2' => instantiate_EC ec1 ec2 /\ instantiate_ECs ecs1' ecs2'
| _, _ => False
end.

Definition instantiate_State (st1 : LLVMopsem.State) (st2 : State) : Prop :=
match st1, st2 with
| LLVMopsem.mkState s1 td1 ps1 ecs1 gl1 fs1 M1,
  mkState s2 td2 ps2 ecs2 gl2 fs2 M2 =>
    s1 = s2 /\ td1 = td2 /\ ps1 = ps2 /\ instantiate_ECs ecs1 ecs2 /\ gl1 = gl2
    /\ fs1 = fs2 /\ M1 = M2
end.

Export LLVMopsem.

Ltac simpl_nd_llvmds :=
  match goal with
  | [Hsim : instantiate_State {| ECS := _::_::_ |} ?st2 |- _ ] =>
     destruct st2 as [S' TD' Ps' ECs' gl' fs' M'];
     destruct Hsim as [eq1 [eq2 [eq3 [Hsim [eq4 [eq5 eq6]]]]]]; subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' als1'] ECs']; 
       try solve [inversion Hsim];
     simpl in Hsim; destruct Hsim as [Hsim1 Hsim2];
     destruct ECs' as [|[f2' b2' cs2' tmn2' lc2' als2'] ECs'];
       try solve [inversion Hsim2];
     destruct Hsim2 as [Hsim2 Hsim3];
     destruct Hsim1 as [J1 [J2 [J3 [J4 [Hsim1 J6]]]]]; subst;
     destruct Hsim2 as [J1 [J2 [J3 [J4 [Hsim2 J6]]]]]; subst
  | [Hsim : instantiate_State {| ECS := _::_|} ?st2 |- _ ] =>
     destruct st2 as [S' TD' Ps' ECs' gl' fs' M'];
     destruct Hsim as [eq1 [eq2 [eq3 [Hsim [eq4 [eq5 eq6]]]]]]; subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' als1'] ECs']; 
       try solve [inversion Hsim];
     simpl in Hsim; destruct Hsim as [Hsim1 Hsim2];
     destruct Hsim1 as [J1 [J2 [J3 [J4 [Hsim1 J6]]]]]; subst
  end.

Lemma instantiate_locals__lookup : forall lc1 lc2 id1 gv1,
  instantiate_locals lc1 lc2 -> 
  lookupAL _ lc1 id1 = Some gv1 ->
  exists gvs2, lookupAL _ lc2 id1 = Some gvs2 /\ gv1 @ gvs2.
Proof.
  induction lc1; destruct lc2; simpl; intros id1 gv1 Hinst Hlk.  
    inv Hlk.
    inv Hinst.
    destruct a. inv Hinst.     

    destruct a. destruct p.
    destruct Hinst as [J1 [J2 J3]]; subst.
    destruct (id1 == i1); subst; eauto.
      inv Hlk. eauto.
Qed.

Lemma instantiate_locals__getOperandValue : forall TD v lc1 lc2 gl gv1,
  instantiate_locals lc1 lc2 -> 
  getOperandValue TD v lc1 gl = Some gv1 ->
  exists gvs2, NDopsem.getOperandValue TD v lc2 gl = Some gvs2 /\
    gv1 @ gvs2.
Proof.
  intros.
  destruct v; simpl in *.
    eapply instantiate_locals__lookup; eauto.
    exists ($ gv1 $). unfold mmap. rewrite H0. simpl. 
    auto using gv_in_gv2gvs.
Qed.

Lemma instantiate_locals__returnUpdateLocals : forall TD lc1 lc2 lc1' lc2' Result
    gl lc1'' c,
  instantiate_locals lc1 lc2 -> 
  instantiate_locals lc1' lc2' -> 
  returnUpdateLocals TD c Result lc1 lc1' gl = ret lc1'' ->
  exists lc2'', 
    NDopsem.returnUpdateLocals TD c Result lc2 lc2' gl = ret lc2'' /\
    instantiate_locals lc1'' lc2''. 
Proof.
  intros.
  unfold returnUpdateLocals in H1.

Admitted.    

Lemma instantiate_locals__switchToNewBasicBlock : forall TD lc1 lc2 gl lc1' b b',
  instantiate_locals lc1 lc2 -> 
  switchToNewBasicBlock TD b' b gl lc1 = Some lc1' ->
  exists lc2', NDopsem.switchToNewBasicBlock TD b' b gl lc2 = Some lc2' /\
    instantiate_locals lc1' lc2'. 
Admitted.

Lemma in_lift_op2 : forall f x y z xs ys,
  f x y = Some z ->
  x @ xs ->
  y @ ys ->
  z @ lift_op2 f xs ys.
Proof.
  intros. unfold lift_op2. 
  unfold Ensembles.In.
  exists x. exists y. exists z. rewrite H. 
  repeat (split; auto).
    apply gv_in_gv2gvs.
Qed.

Lemma instantiate_locals__BOP : forall TD lc1 lc2 gl v1 v2 gv3 bop sz,
  instantiate_locals lc1 lc2 -> 
  BOP TD lc1 gl bop sz v1 v2 = Some gv3 ->
  exists gvs3', NDopsem.BOP TD lc2 gl bop sz v1 v2 = Some gvs3' /\
    gv3 @ gvs3'.
Proof.
  intros.
  apply BOP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]].
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold NDopsem.BOP.
  rewrite H1. rewrite H3.
  exists (lift_op2 (mbop TD bop0 sz0) gvs1 gvs2).
  split; eauto using in_lift_op2.
Qed.
  
Lemma instantiate_locals__updateAddAL : forall lc1 lc2 id0 gv3 gvs3',
  instantiate_locals lc1 lc2 -> 
  gv3 @ gvs3' ->
  instantiate_locals (updateAddAL GenericValue lc1 id0 gv3)
    (updateAddAL GVs lc2 id0 gvs3').
Admitted.

Lemma instantiate_locals__values2GVs : forall TD lc1 lc2 gl vidxs idxs,
  instantiate_locals lc1 lc2 -> 
  values2GVs TD idxs lc1 gl = Some vidxs ->
  exists vidxss, NDopsem.values2GVs TD idxs lc2 gl = Some vidxss /\
    vidxs @@ vidxss.
Admitted.

Lemma instantiate_locals__GEP : forall TD t mp1 mp1' vidxs vidxss inbounds mps2,
  vidxs @@ vidxss ->
  mp1 @ mps2 ->
  GEP TD t mp1 vidxs inbounds = Some mp1' ->
  exists mps2', NDopsem.GEP TD t mps2 vidxss inbounds = Some mps2' /\ 
    mp1' @ mps2'.
Admitted.

Lemma instantiate_locals__CAST : forall TD lc1 lc2 gl t1 v1 t2 gv2 castop0,
  instantiate_locals lc1 lc2 -> 
  CAST TD lc1 gl castop0 t1 v1 t2 = Some gv2 ->
  exists gvs2', NDopsem.CAST TD lc2 gl castop0 t1 v1 t2 = Some gvs2' 
    /\ gv2 @ gvs2'.
Admitted.

Lemma lookupFdefViaGV_inversion : forall TD Ps gl lc fs fv f,
  lookupFdefViaGV TD Ps gl lc fs fv = Some f ->
  exists fptr, exists fn,
    getOperandValue TD fv lc gl = Some fptr /\
    lookupFdefViaGVFromFunTable fs fptr = Some fn /\
    lookupFdefViaIDFromProducts Ps fn = Some f.
Admitted.

Lemma instantiate_locals__params2GVs : forall TD lc1 lc2 gl lp gvs1,
  instantiate_locals lc1 lc2 ->
  params2GVs TD lp lc1 gl = Some gvs1 ->
  exists gvss2, NDopsem.params2GVs TD lp lc2 gl = Some gvss2 /\
    gvs1 @@ gvss2.
Admitted.

Lemma instantiate_locals__initLocals : forall la gvs1 gvss2,
  gvs1 @@ gvss2 ->
  instantiate_locals (initLocals la gvs1) (NDopsem.initLocals la gvss2).
Admitted.

Lemma test : forall st1 st2 st1' tr,
  instantiate_State st1 st2 ->
  LLVMopsem.dsInsn st1 st1' tr ->
  exists st2', sInsn st2 st2' tr /\ instantiate_State st1' st2'.
Proof.
  intros st1 st2 st1' tr Hsim Hop.  
  (dsInsn_cases (induction Hop) Case).
Case "dsReturn". simpl_nd_llvmds. 
  eapply instantiate_locals__returnUpdateLocals in H1; eauto.
  destruct H1 as [lc2'' [H1 H2]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f2' b2' cs' tmn2' lc2'' als2')::ECs') gl' fs' Mem').
  split; eauto.
    repeat (split; auto).
Case "dsReturnVoid". simpl_nd_llvmds. 
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f2' b2' cs' tmn2' lc2' als2')::ECs') gl' fs' Mem').
  split; eauto.
    repeat (split; auto).
Case "dsBranch". simpl_nd_llvmds. 
  eapply instantiate_locals__switchToNewBasicBlock in H1; eauto.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  destruct H1 as [lc2' [J3 J4]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' (block_intro l' ps' cs' tmn') cs' tmn' lc2' als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto).
Case "dsBranch_uncond". simpl_nd_llvmds. 
  eapply instantiate_locals__switchToNewBasicBlock in H0; eauto.
  destruct H0 as [lc2' [J1 J2]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' (block_intro l' ps' cs' tmn') cs' tmn' lc2' als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto).
Case "dsBop". simpl_nd_llvmds. 
  eapply instantiate_locals__BOP in H; eauto.
  destruct H as [gvs3' [J1 J2]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsFBop". admit.
Case "dsExtractValue". admit.
Case "dsInsertValue". admit.
Case "dsMalloc". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gns [J1 J2]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' 
      (updateAddAL _ lc1' id0 ($ (blk2GV TD' mb) $)) 
    als1')::ECs') gl' fs' Mem').
  split; eauto.
    repeat (split; auto).
      apply instantiate_locals__updateAddAL; auto.
      unfold blk2GV, ptr2GV, val2GV.
      apply gv_in_gv2gvs.
Case "dsFree". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs [J1 J2]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' lc1'
    als1')::ECs') gl' fs' Mem').
  split; eauto.
    repeat (split; auto).
Case "dsAlloca". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gns [J1 J2]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' 
      (updateAddAL _ lc1' id0 ($ (blk2GV TD' mb) $)) 
    (mb::als1'))::ECs') gl' fs' Mem').
  split; eauto.
    repeat (split; auto).
      apply instantiate_locals__updateAddAL; auto.
      unfold blk2GV, ptr2GV, val2GV.
      apply gv_in_gv2gvs.
Case "dsLoad". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 ($ gv $))
    als1')::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL, gv_in_gv2gvs).
Case "dsStore". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [mps2 [J3 J4]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' lc1' als1')::ECs') gl' fs' Mem').
  split; eauto.
    repeat (split; auto).
Case "dsGEP". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [mps [J1 J2]].
  eapply instantiate_locals__values2GVs in H0; eauto.
  destruct H0 as [vidxss [J3 J4]].
  eapply instantiate_locals__GEP in H1; eauto.
  destruct H1 as [mps2' [J5 J6]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 mps2') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsTrunc". admit.
Case "dsExt". admit.
Case "dsCast". simpl_nd_llvmds. 
  eapply instantiate_locals__CAST in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "dsIcmp". admit.
Case "dsFcmp". admit.
Case "dsSelect". admit.
Case "dsCall". simpl_nd_llvmds. 
  apply lookupFdefViaGV_inversion in H.
  destruct H as [fptr [fn [J1 [J2 J3]]]].
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs2 [J11 J12]].
  eapply instantiate_locals__params2GVs in H1; eauto.
  destruct H1 as [gvss2 [H11 H12]].
  exists (NDopsem.mkState S' TD' Ps' 
    ((NDopsem.mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                       (block_intro l' ps' cs' tmn') cs' tmn' 
                       (NDopsem.initLocals la gvss2) 
                       nil)::
     (NDopsem.mkEC f1' b1' (insn_call rid noret0 ca ft fv lp :: cs) tmn1' 
      lc1' als1') ::ECs') gl' fs' M').
  split.
    eapply sCall; eauto.
      unfold lookupFdefViaPtr. 
      rewrite J2. simpl. rewrite J3. auto.
    repeat (split; auto using instantiate_locals__initLocals).
Case "dsExCall". admit.
Qed.

End NDopsem.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
