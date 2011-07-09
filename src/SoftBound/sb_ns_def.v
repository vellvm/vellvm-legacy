Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import ssa_def.
Require Import ssa_lib.
Require Import trace.
Require Import Memory.
Require Import genericvalues.
Require Import alist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import ssa_dynamic.
Require Import ndopsem.
Require Import sb_ds_def.

Export NDopsem.

Module SBnsop.

Definition prop_reg_metadata lc rmd pid gvp (md:SBopsem.metadata) : 
    GVsMap * SBopsem.rmetadata  :=
  (updateAddAL _ lc pid gvp, updateAddAL _ rmd pid md).

Record ExecutionContext : Type := mkEC {
CurFunction : fdef;
CurBB       : block;
CurCmds     : cmds;                  (* cmds to run within CurBB *)
Terminator  : terminator;
Locals      : GVsMap;                (* LLVM values used in this invocation *)
Rmap        : SBopsem.rmetadata;
Allocas     : list mblock            (* Track memory allocated by alloca *)
}.

Definition ECStack := list ExecutionContext.

Record State : Type := mkState {
CurSystem          : system;
CurTargetData      : TargetData;
CurProducts        : list product;
ECS                : ECStack;
Globals            : GVMap;
FunTable           : GVMap;
Mem                : mem;
Mmap               : SBopsem.mmetadata
}.

Fixpoint getIncomingValuesForBlockFromPHINodes (TD:TargetData)
  (PNs:list phinode) (b:block) (gl:GVMap) (lc:GVsMap) (rm:SBopsem.rmetadata) : 
  option (list (id * GVs * option SBopsem.metadata)) :=
match PNs with
| nil => Some nil
| (insn_phi id0 t vls)::PNs => 
  match (getValueViaBlockFromPHINode (insn_phi id0 t vls) b) with
  | None => None
  | Some v => 
      match (getOperandValue TD v lc gl, 
             getIncomingValuesForBlockFromPHINodes TD PNs b gl lc rm)
      with
      | (Some gv1, Some idgvs) => 
          if isPointerTypB t then
            match SBopsem.get_reg_metadata TD gl rm v with
            | Some md => Some ((id0,gv1,Some md)::idgvs)
            | None => None
            end
          else Some ((id0,gv1,None)::idgvs)
      | _ => None
      end               
  end
end.

Fixpoint updateValuesForNewBlock 
  (ResultValues:list (id*GVs*option SBopsem.metadata)) (lc:GVsMap) 
  (rm:SBopsem.rmetadata) : GVsMap * SBopsem.rmetadata :=
match ResultValues with
| nil => (lc, rm)
| (id0, v, opmd)::ResultValues' => 
    let '(lc', rm') := updateValuesForNewBlock ResultValues' lc rm in
    match opmd with
    | None => (updateAddAL _ lc' id0 v, rm')
    | Some md => prop_reg_metadata lc' rm' id0 v md
    end
end.

Definition switchToNewBasicBlock (TD:TargetData) (Dest:block) 
  (PrevBB:block) (gl:GVMap) (lc:GVsMap) (rm:SBopsem.rmetadata)
  : option (GVsMap * SBopsem.rmetadata) :=
  let PNs := getPHINodesFromBlock Dest in
  match getIncomingValuesForBlockFromPHINodes TD PNs PrevBB gl lc rm with
  | Some ResultValues => Some (updateValuesForNewBlock ResultValues lc rm)
  | None => None
  end.

(*
  LLVM does not ensure that a function is called with its correct type. So 
  metadata may not be passed into or out from a function correctly. For example,
  if a function is of typ int* -> void, and used as typ void -> int*, then
  the callsite will not initialize metadata for its argument since the callsite
  thinks its signature is void -> void. Plus, the callsite cannot get any
  metadata from the function's return.

  In the semantics, we do not want to take such cases as stuck states, because
  1) the original LLVM semantics does not check the problem. 
  2) our SBpass does not check this issue dynamically either

  So, we let the values be undefined at these cases. Then, we can still prove
  preservation and progress with the same stuck states as LLVMopsem, since
  the undefined values do not ensure any safety. However, we should prove that
  the subset of instructions w/o call and ret can progress w/o memory violation.

  In implementation, the shadow stack interface does the similar things ---
  returning arbitrary values.
*)

Definition returnResult (TD:TargetData) (rt:typ) (Result:value) 
  (lc:GVsMap) (rm:SBopsem.rmetadata) (gl:GVMap) : option (GVs * SBopsem.metadata)
  :=
  match getOperandValue TD Result lc gl with
  | Some gr =>
      if isPointerTypB rt then
        match SBopsem.get_reg_metadata TD gl rm Result with
        | Some md => Some (gr, md)
        | None => None
        end
      else Some (gr, (SBopsem.mkMD null null))
  | _ => None
  end.

Definition returnUpdateLocals (TD:TargetData) (c':cmd) (rt:typ) 
  (Result:value) (lc lc':GVsMap) (rm rm':SBopsem.rmetadata) (gl:GVMap) 
  : option (GVsMap * SBopsem.rmetadata) :=
  match returnResult TD rt Result lc rm gl with
  | Some (gr,md) =>
      match c' with
      | insn_call id0 false _ t _ _ =>
          if SBopsem.isReturnPointerTypB t then 
            Some (prop_reg_metadata lc' rm' id0 gr md)
          else Some (updateAddAL _ lc' id0 gr, rm')
      | _ => Some (lc', rm')
      end
  | _ => None
  end.

Definition exCallUpdateLocals (ft:typ) (noret:bool) (rid:id) 
  (oResult:option GenericValue) (lc :GVsMap) (rm:SBopsem.rmetadata) 
  : option (GVsMap*SBopsem.rmetadata) :=
  match noret with
  | false =>
      match oResult with
      | None => None
      | Some Result => 
          match ft with
          | typ_function (typ_pointer t) _ _ => 
                     Some (updateAddAL _ lc rid ($ Result # (typ_pointer t) $), 
                           updateAddAL _ rm rid (SBopsem.mkMD null null))
          | _ => Some (updateAddAL _ lc rid ($ Result # (getReturnTyp ft) $), rm)
          end
      end
  | true => Some (lc, rm)
  end.

Fixpoint params2GVs (TD:TargetData) (lp:params) (lc:GVsMap) (gl:GVMap) 
  (rm:SBopsem.rmetadata) : option (list (GVs * option SBopsem.metadata)) :=
match lp with
| nil => Some nil
| (t, v)::lp' => 
    match (getOperandValue TD v lc gl, params2GVs TD lp' lc gl rm) with
    | (Some gv, Some gvs) =>
       if isPointerTypB t then 
         Some ((gv, SBopsem.get_reg_metadata TD gl rm v)::gvs)
       else Some ((gv, None)::gvs)
    | _ => None
    end
end.

Fixpoint _initializeFrameValues (la:args) (lg:list (GVs*option SBopsem.metadata))
  (lc:GVsMap) (rm : SBopsem.rmetadata) : GVsMap * SBopsem.rmetadata :=
match (la, lg) with
| ((t, _, id0)::la', (gv, opmd)::lg') => 
     let '(lc',rm') := _initializeFrameValues la' lg' lc rm in
     if isPointerTypB t then
       match opmd with
       | None => (prop_reg_metadata lc' rm' id0 gv (SBopsem.mkMD null null))
       | Some md => (prop_reg_metadata lc' rm' id0 gv md)
       end
     else (updateAddAL _ lc' id0 gv, rm')
| ((t, _, id0)::la', nil) => 
     let '(lc',rm') := _initializeFrameValues la' nil lc rm in
     if isPointerTypB t then
      (prop_reg_metadata lc' rm' id0 ($(gundef t) # t$) (SBopsem.mkMD null null))
     else (updateAddAL _ lc' id0 ($(gundef t) # t$), rm')
| _ => (lc, rm)
end.

Definition initLocals (la:args) (lg:list (GVs*option SBopsem.metadata)) 
  : GVsMap * SBopsem.rmetadata :=
_initializeFrameValues la lg nil nil.

Inductive nsInsn : State -> State -> trace -> Prop :=
| nsReturn : forall S TD Ps F B rid RetTy Result lc rm gl fs F' B' c' cs' tmn' 
    lc' rm' EC Mem MM Mem' als als' lc'' rm'',   
  Instruction.isCallInst c' = true ->
  free_allocas TD Mem als = Some Mem' ->
  returnUpdateLocals TD c' RetTy Result lc lc' rm rm' gl = Some (lc'', rm'') ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B nil (insn_return rid RetTy Result) lc rm als)::
       (mkEC F' B' (c'::cs') tmn' lc' rm' als')::EC) gl fs Mem MM)
    (mkState S TD Ps 
      ((mkEC F' B' cs' tmn' lc'' rm'' als')::EC) gl fs Mem' MM)
    trace_nil

| nsReturnVoid : forall S TD Ps F B rid lc rm gl fs F' B' c' tmn' lc' rm' EC cs' 
    Mem MM Mem' als als',   
  Instruction.isCallInst c' = true ->
  free_allocas TD Mem als = Some Mem' ->
  getCallerReturnID c' = None ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B nil (insn_return_void rid) lc rm als)::
       (mkEC F' B' (c'::cs') tmn' lc' rm' als')::EC) gl fs Mem MM)
    (mkState S TD Ps 
      ((mkEC F' B' cs' tmn' lc' rm' als')::EC) gl fs Mem' MM)
    trace_nil

| nsBranch : forall S TD Ps F B lc rm gl fs bid Cond l1 l2 c l' ps' cs' tmn' lc' 
    rm' EC Mem MM als conds,   
  getOperandValue TD Cond lc gl = Some conds ->
  c @ conds ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc rm = 
    Some (lc', rm') ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B nil (insn_br bid Cond l1 l2) lc rm als)::EC) 
      gl fs Mem MM)
    (mkState S TD Ps 
      ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' rm' als)::EC) 
      gl fs Mem MM)
    trace_nil

| nsBranch_uncond : forall S TD Ps F B lc rm gl fs bid l l' ps' cs' tmn' lc' rm'
    EC Mem MM als,   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc rm = 
    Some (lc', rm') ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B nil (insn_br_uncond bid l) lc rm als)::EC) 
      gl fs Mem MM)
    (mkState S TD Ps 
      ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' rm' als)::EC) 
      gl fs Mem MM)
    trace_nil

| nsBop: forall S TD Ps F B lc rm gl fs id bop sz v1 v2 gv3 EC cs tmn Mem MM als,
  BOP TD lc gl bop sz v1 v2 = Some gv3 ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv3) rm als)::EC) gl fs Mem MM)
    trace_nil

| nsFBop: forall S TD Ps F B lc rm gl fs id fbop fp v1 v2 gv3 EC cs tmn Mem MM 
    als,
  FBOP TD lc gl fbop fp v1 v2 = Some gv3 ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv3) rm als)::EC) 
      gl fs Mem MM)
    trace_nil

| nsExtractValue : forall S TD Ps F B lc rm gl fs id t v gv gv' idxs EC cs tmn 
    Mem MM als,
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_extractvalue id t v idxs)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv') rm als)::EC) gl fs Mem MM)
    trace_nil

| nsInsertValue : forall S TD Ps F B lc rm gl fs id t v t' v' gv gv' gv'' idxs 
    EC cs tmn Mem MM als,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_insertvalue id t v t' v' idxs)::cs) tmn lc rm als)
      ::EC) gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv'') rm als)::EC) gl fs Mem MM)
    trace_nil

| nsMalloc : forall S TD Ps F B lc rm gl fs id t v gn align EC cs tmn Mem MM als 
    Mem' tsz mb lc' rm' n gns,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  GV2int TD Size.ThirtyTwo gn = Some n ->
  prop_reg_metadata lc rm id ($ (blk2GV TD mb) # typ_pointer t $) 
    (SBopsem.mkMD (SBopsem.base2GV TD mb) (SBopsem.bound2GV TD mb tsz n)) = 
      (lc',rm') ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_malloc id t v align)::cs) tmn lc rm als)::EC) 
       gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn lc' rm' als)::EC) gl fs Mem' MM)
    trace_nil

| nsFree : forall S TD Ps F B lc rm gl fs fid t v EC cs tmn Mem als Mem' mptr MM
    mptrs,
  getOperandValue TD v lc gl = Some mptrs ->
  mptr @ mptrs ->
  free TD Mem mptr = Some Mem'->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_free fid t v)::cs) tmn lc rm als)::EC) gl fs Mem MM) 
    (mkState S TD Ps ((mkEC F B cs tmn lc rm als)::EC) gl fs Mem' MM)
    trace_nil

| nsAlloca : forall S TD Ps F B lc rm gl fs id t v gn align EC cs tmn Mem MM als 
    Mem' tsz mb lc' rm' n gns,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  GV2int TD Size.ThirtyTwo gn = Some n ->
  prop_reg_metadata lc rm id ($(blk2GV TD mb) # typ_pointer t$) 
    (SBopsem.mkMD (SBopsem.base2GV TD mb) (SBopsem.bound2GV TD mb tsz n)) = 
      (lc',rm') ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_alloca id t v align)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn lc' rm' (mb::als))::EC) gl fs Mem' MM)
    trace_nil

| nsLoad_nptr : forall S TD Ps F B lc rm gl fs id t align vp EC cs tmn Mem als 
    gvp gv MM md gvps,
  SBopsem.get_reg_metadata TD gl rm vp = Some md ->
  getOperandValue TD vp lc gl = Some gvps ->
  gvp @ gvps ->
  SBopsem.assert_mptr TD t gvp md ->
  mload TD Mem gvp t align = Some gv ->
  isPointerTypB t = false ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_load id t vp align)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id ($ gv # t $)) rm als)::EC) 
        gl fs Mem MM)
    trace_nil

| nsLoad_ptr : forall S TD Ps F B lc rm gl fs id t align vp EC cs tmn Mem MM als 
    gvp gv md md' lc' rm' gvps,
  SBopsem.get_reg_metadata TD gl rm vp = Some md ->
  getOperandValue TD vp lc gl = Some gvps ->
  gvp @ gvps ->
  SBopsem.assert_mptr TD t gvp md ->
  mload TD Mem gvp t align = Some gv ->
  isPointerTypB t = true ->
  SBopsem.get_mem_metadata TD MM gvp = md' -> 
  prop_reg_metadata lc rm id ($ gv # t $) md' = (lc', rm') ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_load id t vp align)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps ((mkEC F B cs tmn lc' rm' als)::EC) gl fs Mem MM)
    trace_nil

| nsStore_nptr : forall S TD Ps F B lc rm gl fs sid t align v vp EC cs tmn Mem MM
    als gv gvp md Mem' gvps gvs,
  SBopsem.get_reg_metadata TD gl rm vp = Some md ->
  getOperandValue TD v lc gl = Some gvs ->
  getOperandValue TD vp lc gl = Some gvps ->
  gvp @ gvps -> gv @ gvs ->
  SBopsem.assert_mptr TD t gvp md ->
  mstore TD Mem gvp t gv align = Some Mem' ->
  isPointerTypB t = false ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_store sid t v vp align)::cs) tmn lc rm als)::EC) 
       gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn lc rm als)::EC) gl fs Mem' MM)
    trace_nil

| nsStore_ptr : forall S TD Ps F B lc rm gl fs sid t align v vp EC cs tmn Mem MM
    als gv gvp md md' Mem' MM' gvps gvs,
  SBopsem.get_reg_metadata TD gl rm vp = Some md ->
  getOperandValue TD v lc gl = Some gvs ->
  getOperandValue TD vp lc gl = Some gvps ->
  gvp @ gvps -> gv @ gvs ->
  SBopsem.assert_mptr TD t gvp md ->
  mstore TD Mem gvp t gv align = Some Mem' ->
  isPointerTypB t = true ->
  SBopsem.get_reg_metadata TD gl rm v = Some md' ->
  SBopsem.set_mem_metadata TD MM gvp md' = MM' -> 
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_store sid t v vp align)::cs) tmn lc rm als)::EC) 
       gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn lc rm als)::EC) gl fs Mem' MM')
    trace_nil

| nsGEP : forall S TD Ps F B lc rm gl fs id inbounds t vp idxs vidxs EC gvp gvp' 
                 cs tmn Mem MM als lc' rm' md,
  SBopsem.get_reg_metadata TD gl rm vp = Some md ->
  getOperandValue TD vp lc gl = Some gvp ->
  values2GVs TD idxs lc gl = Some vidxs ->
  GEP TD t gvp vidxs inbounds = Some gvp' ->
  prop_reg_metadata lc rm id gvp' md = (lc', rm') ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_gep id inbounds t vp idxs)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps ((mkEC F B cs tmn lc' rm' als)::EC) gl fs Mem MM)
    trace_nil 

| nsTrunc : forall S TD Ps F B lc rm gl fs id truncop t1 v1 t2 gv2 EC cs tmn 
                   Mem MM als,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gv2 ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv2) rm als)::EC) gl fs Mem MM)
    trace_nil

| nsExt : forall S TD Ps F B lc rm gl fs id extop t1 v1 t2 gv2 EC cs tmn Mem MM
                 als,
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc rm als)::EC) 
       gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv2) rm als)::EC) gl fs Mem MM)
    trace_nil

| nsBitcast_nptr : forall S TD Ps F B lc rm gl fs id t1 v1 t2 gv2 EC cs tmn Mem 
    MM als,
  CAST TD lc gl castop_bitcast t1 v1 t2 = Some gv2 ->
  isPointerTypB t1 = false ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_cast id castop_bitcast t1 v1 t2)::cs) tmn lc rm als)
        ::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv2) rm als)::EC) gl fs Mem MM)
    trace_nil

| nsBitcast_ptr : forall S TD Ps F B lc rm gl fs id t1 v1 t2 gv2 EC cs tmn Mem MM
    als md lc' rm',
  CAST TD lc gl castop_bitcast t1 v1 t2 = Some gv2 ->
  isPointerTypB t1 = true ->
  SBopsem.get_reg_metadata TD gl rm v1 = Some md ->
  prop_reg_metadata lc rm id gv2 md = (lc', rm') ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_cast id castop_bitcast t1 v1 t2)::cs) tmn lc rm als)
        ::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps ((mkEC F B cs tmn lc' rm' als)::EC) gl fs Mem MM)
    trace_nil

| nsInttoptr : forall S TD Ps F B lc rm gl fs id t1 v1 t2 gv2 EC cs tmn Mem MM
    als lc' rm',
  CAST TD lc gl castop_inttoptr t1 v1 t2 = Some gv2 ->
  prop_reg_metadata lc rm id gv2 (SBopsem.mkMD null null) = (lc', rm') ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_cast id castop_inttoptr t1 v1 t2)::cs) tmn lc rm als)
        ::EC) 
       gl fs Mem MM) 
    (mkState S TD Ps ((mkEC F B cs tmn lc' rm' als)::EC) gl fs Mem MM)
    trace_nil

| nsOtherCast : forall S TD Ps F B lc rm gl fs id castop t1 v1 t2 gv2 EC cs tmn 
    Mem MM als,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  castop <> castop_bitcast /\ castop <> castop_inttoptr ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_cast id castop t1 v1 t2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv2) rm als)::EC) gl fs Mem MM)
    trace_nil

| nsIcmp : forall S TD Ps F B lc rm gl fs id cond t v1 v2 gv3 EC cs tmn Mem MM 
    als,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv3) rm als)::EC) gl fs Mem MM)
    trace_nil

| nsFcmp : forall S TD Ps F B lc rm gl fs id fcond fp v1 v2 gv3 EC cs tmn Mem MM
    als,
  FCMP TD lc gl fcond fp v1 v2 = Some gv3 ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps   
      ((mkEC F B cs tmn (updateAddAL _ lc id gv3) rm als)::EC) gl fs Mem MM)
    trace_nil

| nsSelect_nptr : forall S TD Ps F B lc rm gl fs id v0 t v1 v2 c EC cs tmn Mem MM
    als gv1 gv2 cond,
  getOperandValue TD v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  c @ cond ->
  isPointerTypB t = false ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (if isGVZero TD c 
                            then updateAddAL _ lc id gv2 
                            else updateAddAL _ lc id gv1) rm als)::EC) 
      gl fs Mem MM)
    trace_nil

| nsSelect_ptr : forall S TD Ps F B lc rm gl fs id v0 t v1 v2 c EC cs tmn Mem MM
    als gv1 gv2 md1 md2 lc' rm' cond,
  getOperandValue TD v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  c @ cond ->
  isPointerTypB t = true ->
  SBopsem.get_reg_metadata TD gl rm v1 = Some md1 ->
  SBopsem.get_reg_metadata TD gl rm v2 = Some md2 ->
  (if isGVZero TD c then 
    prop_reg_metadata lc rm id gv2 md2
  else
    prop_reg_metadata lc rm id gv1 md1)
    = (lc', rm') ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn lc' rm' als)::EC) 
      gl fs Mem MM)
    trace_nil

| nsCall : forall S TD Ps F B lc rm gl fs rid noret ca fid fv lp cs tmn ogvs
             fptr fptrs ft l' ps' cs' tmn' EC fa rt la va lb Mem MM als rm' lc',
  (* only look up the current module for the time being, 
     do not support linkage. *)
  getOperandValue TD fv lc gl = Some fptrs -> 
  fptr @ fptrs -> 
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl rm = Some ogvs ->
  initLocals la ogvs = (lc', rm') ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn lc rm als)
        ::EC) gl fs Mem MM)
    (mkState S TD Ps 
      ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                (block_intro l' ps' cs' tmn') cs' tmn' 
                lc' rm' nil)::
       (mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn lc rm als)
         ::EC) gl fs Mem MM)
    trace_nil 

| nsExCall : forall S TD Ps F B lc rm gl fs rid noret ca fid fv lp cs tmn EC 
           gvss fptr fptrs rt fa ft la va Mem als oresult Mem' lc' rm' MM gvs,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  getOperandValue TD fv lc gl = Some fptrs -> 
  fptr @ fptrs -> 
  lookupExFdecViaPtr Ps fs fptr = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  NDopsem.params2GVs TD lp lc gl = Some gvss ->
  gvs @@ gvss ->
  LLVMopsem.callExternalFunction Mem fid gvs = Some (oresult, Mem') ->
  exCallUpdateLocals ft noret rid oresult lc rm = Some (lc',rm') ->
  nsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn lc rm als)
       ::EC) gl fs Mem MM)
    (mkState S TD Ps ((mkEC F B cs tmn lc' rm' als)::EC) gl fs Mem' MM)
    trace_nil 
.

Definition ns_isFinialState (state:State) : bool :=
match state with
| (mkState _ _ _ 
    ((mkEC _ _ nil (insn_return_void _) _ _ _)::nil) _ _ _ _) => true
| (mkState _ _ _ 
    ((mkEC _ _ nil (insn_return _ _ _) _ _ _)::nil) _ _ _ _) => true 
| _ => false
end.

Inductive nsop_star : State -> State -> trace -> Prop :=
| nsop_star_nil : forall state, nsop_star state state trace_nil
| nsop_star_cons : forall state1 state2 state3 tr1 tr2,
    nsInsn state1 state2 tr1 ->
    nsop_star state2 state3 tr2 ->
    nsop_star state1 state3 (trace_app tr1 tr2)
.

Inductive nsop_plus : State -> State -> trace -> Prop :=
| nsop_plus_cons : forall state1 state2 state3 tr1 tr2,
    nsInsn state1 state2 tr1 ->
    nsop_star state2 state3 tr2 ->
    nsop_plus state1 state3 (trace_app tr1 tr2)
.

CoInductive nsop_diverges : State -> Trace -> Prop :=
| nsop_diverges_intro : forall state1 state2 tr1 tr2,
    nsop_plus state1 state2 tr1 ->
    nsop_diverges state2 tr2 ->
    nsop_diverges state1 (Trace_app tr1 tr2)
.

End SBnsop.

Tactic Notation "sb_nsInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "nsReturn" | c "nsReturnVoid" | c "nsBranch" | c "nsBranch_uncond" |
    c "nsBop" | c "nsFBop" | c "nsExtractValue" | c "nsInsertValue" |
    c "nsMalloc" | c "nsFree" | c "nsAlloca" | 
    c "nsLoad_nptr" | c "nsLoad_ptr" | 
    c "nsStore_nptr" | c "nsStore_ptr" | 
    c "nsGEP" | c "nsTrunc" | c "nsExt" | 
    c "nsBitcast_nptr" | c "nsBitcast_ptr" | c "nsInttoptr" | c "nsOthercast" | 
    c "nsIcmp" | c "nsFcmp" | 
    c "nsSelect_nptr" | c "nsSelect_ptr" |  
    c "nsCall" | c "nsExCall" ].


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
