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
Require Import ssa_dynamic.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import sub_symexe.
Require Import Znumtheory.

Export LLVMsyntax.
Export LLVMgv.

Module SoftBound.

Record metadata : Type := mkMD {
  md_base : GenericValue; md_bound : GenericValue
}.

Definition rmetadata := list (id*metadata).

Inductive result : Set :=
| rok : result 
| rabort : result
| rerror : result
.  

Definition base2GV := blk2GV.

Definition bound2GV (TD:TargetData) (b:mblock) (s:sz) n : GenericValue :=
ptr2GV TD (Vptr b (Int.repr 31 ((Size.to_Z s)*n))).

Fixpoint get_const_metadata (c:const) : option (const*const*typ) :=
match c with
| const_gid t gid => 
    match t with
    | typ_function _ _ _ => Some (c, c, (typ_pointer t))
    | _ => Some (c, const_gep false c 
             (Cons_list_const (const_int Size.ThirtyTwo 
               (INTEGER.of_Z 32%Z 1%Z false)) Nil_list_const), (typ_pointer t))
    end
| const_gep _ pc _ => get_const_metadata pc
| _ => None
end.

Definition get_reg_metadata TD M gl (rm:rmetadata) (v:value) 
    : option (metadata * typ) :=
  match v with
  | value_id pid => 
      match lookupAL _ rm pid with
      | Some md => Some (md, typ_pointer (typ_int Size.Eight))
      | _ => None
      end
  | value_const c => 
      match get_const_metadata c with
      | Some (bc, ec, t) => 
          do gvb <- const2GV TD M gl bc;
          do gve <- const2GV TD M gl ec;
          ret (mkMD gvb gve, t)
      | None => Some (mkMD null null, typ_pointer (typ_int Size.Eight))
      end
  end.

Definition assert_mptr (TD:TargetData) (t:typ) (ptr:GenericValue) (md:metadata)
  : bool :=
  let 'mkMD base bound := md in
  match (GV2ptr TD (getPointerSize TD) ptr,
         GV2ptr TD (getPointerSize TD) base,
         GV2ptr TD (getPointerSize TD) bound,
         getTypeAllocSize TD t) with
  | (Some (Vptr pb pofs), Some (Vptr bb bofs), Some (Vptr eb eofs), Some tsz) =>
      zeq pb bb && zeq bb eb &&
      zle (Integers.Int.signed 31 bofs) (Integers.Int.signed 31 pofs) &&
      zle (Integers.Int.signed 31 pofs + Size.to_Z tsz) 
          (Integers.Int.signed 31 eofs)
  | _ => false
  end.  

Definition SELECT TD Mem v0 v1 v2 lc gl : option GenericValue :=
  match (getOperandValue TD Mem v0 lc gl, getOperandValue TD Mem v1 lc gl,
         getOperandValue TD Mem v2 lc gl) with
  | (Some cond, Some gv1, Some gv2) => 
      Some (if isGVZero TD cond then gv2 else gv1)
  | _ => None
  end.

Definition prop_reg_metadata lc rmd pid gvp (md:metadata) : 
    GVMap * rmetadata  :=
  (updateAddAL _ lc pid gvp, updateAddAL _ rmd pid md).

Definition mmetadata := Values.block -> int32 -> option metadata.

Definition get_mem_metadata TD MM (gv:GenericValue) : metadata :=
  match (GV2ptr TD (getPointerSize TD) gv) with
  | Some (Vptr b ofs) => 
      match MM b ofs with
      | Some md => md
      | _ => mkMD null null
      end
  | _ => mkMD null null
  end.

Definition set_mem_metadata TD MM (gv:GenericValue) (md:metadata) 
  : mmetadata :=
  match (GV2ptr TD (getPointerSize TD) gv) with
  | Some (Vptr b ofs) => 
     fun b1 => fun ofs1 =>
       if zeq b1 b && Integers.Int.eq_dec 31 ofs ofs1 then Some md 
       else MM b1 ofs1
  | _ => MM
  end.

Definition blk_temporal_safe M b : Prop :=
let (lo, _) := Mem.bounds M b in
Mem.perm M b lo Nonempty.

Definition temporal_safe (TD:TargetData) (M:mem) (ptr:mptr) : Prop :=
match GV2ptr TD (getPointerSize TD) ptr with
| Some (Vptr b _) => blk_temporal_safe M b
| _ => False
end.

Definition callUpdateLocals (TD:TargetData) (M:mem) (noret:bool) (rid:id) 
  (oResult:option value) (rm rm':rmetadata) (lc lc' gl:GVMap) 
  : option (GVMap * rmetadata):=
    match noret with
    | false =>
        match oResult with
        | None => None
        | Some Result => 
          match (getOperandValue TD M Result lc' gl) with 
          | Some gr => 
              match get_reg_metadata TD M gl rm' Result with
              | Some (md',mt') =>
                  ret (updateAddAL _ lc rid gr, updateAddAL _ rm rid md')
              | None => None
              end
          | None => None
          end
        end
    | true => Some (lc,rm)
    end.

Fixpoint initRmetadata_aux TD Mem gl (la:args) (lp:params) (rm accum:rmetadata) 
  : option rmetadata :=
match (la, lp) with
| ((t,_,id)::la', (_,v)::lp') =>
    if isPointerTypB t then
      match get_reg_metadata TD Mem gl rm v with
      | Some (md, mt) =>
        initRmetadata_aux TD Mem gl la' lp' rm (updateAddAL _ accum id md)
      | _ => None
      end
    else initRmetadata_aux TD Mem gl la' lp' rm accum
| (nil, nil) => Some accum
| _ => None
end.  

Definition initRmetadata TD Mem gl (la:args) (lp:params) (rm:rmetadata) 
  : option rmetadata := 
  initRmetadata_aux TD Mem gl la lp rm nil.

Record ExecutionContext : Type := mkEC {
CurFunction : fdef;
CurBB       : block;
CurCmds     : cmds;                  (* cmds to run within CurBB *)
Terminator  : terminator;
Locals      : GVMap;                 (* LLVM values used in this invocation *)
Rmap        : rmetadata;
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
Mmap               : mmetadata
}.

Definition returnUpdateLocals (TD:TargetData) (M:mem) (c':cmd) (Result:value) 
  (lc lc':GVMap) (rm rm':rmetadata) (gl:GVMap) : option (GVMap * rmetadata) :=
    match (getCallerReturnID c') with
    | Some id0 =>
        match (getOperandValue TD M Result lc gl,
               get_reg_metadata TD M gl rm Result) with
        | (Some gr, None) => Some (updateAddAL _ lc' id0 gr, rm')
        | (Some gr, Some (md,mt)) => Some (prop_reg_metadata lc' rm' id0 gr md)
        | _ => None
        end
    | None => Some (lc', rm')
    end.

Fixpoint getIncomingValuesForBlockFromPHINodes (TD:TargetData) (M:mem) 
  (PNs:list phinode) (b:block) (gl lc:GVMap) (rm:rmetadata) : 
  option (list (id * GenericValue * option (metadata*typ))) :=
match PNs with
| nil => Some nil
| (insn_phi id0 t vls)::PNs => 
  match (getValueViaBlockFromPHINode (insn_phi id0 t vls) b) with
  | None => None
  | Some v => 
      match (getOperandValue TD M v lc gl, 
             getIncomingValuesForBlockFromPHINodes TD M PNs b gl lc rm)
      with
      | (Some gv1, Some idgvs) => 
          Some ((id0,gv1,get_reg_metadata TD M gl rm v)::idgvs)
      | _ => None
      end               
  end
end.

Fixpoint updateValuesForNewBlock 
  (ResultValues:list (id*GenericValue*option (metadata*typ))) (lc:GVMap) 
  (rm:rmetadata) : GVMap * rmetadata :=
match ResultValues with
| nil => (lc, rm)
| (id0, v, opmd)::ResultValues' => 
    let '(lc', rm') := updateValuesForNewBlock ResultValues' lc rm in
    match opmd with
    | None => (updateAddAL _ lc' id0 v, rm')
    | Some (md,_) => prop_reg_metadata lc' rm' id0 v md
    end
end.

Definition switchToNewBasicBlock (TD:TargetData) (M:mem) (Dest:block) 
  (PrevBB:block) (gl lc:GVMap) (rm:rmetadata): option (GVMap * rmetadata) :=
  let PNs := getPHINodesFromBlock Dest in
  match getIncomingValuesForBlockFromPHINodes TD M PNs PrevBB gl lc rm with
  | Some ResultValues => Some (updateValuesForNewBlock ResultValues lc rm)
  | None => None
  end.

Fixpoint params2GVs (TD:TargetData) (M:mem) (lp:params) (lc gl:GVMap) 
 (rm:rmetadata) : option (list (GenericValue * option (metadata*typ))) :=
match lp with
| nil => Some nil
| (_, v)::lp' => 
    match (getOperandValue TD M v lc gl, params2GVs TD M lp' lc gl rm) with
    | (Some gv, Some gvs) => Some ((gv, get_reg_metadata TD M gl rm v)::gvs)
    | _ => None
    end
end.

Fixpoint _initializeFrameValues (la:args) 
  (lg:list (GenericValue*option (metadata*typ))) (lc:GVMap) (rm : rmetadata) 
  : GVMap * rmetadata :=
match (la, lg) with
| ((_, id0)::la', (gv, opmd)::lg') => 
     let '(lc',rm') := _initializeFrameValues la' lg' lc rm in
     match opmd with
     | None => (updateAddAL _ lc' id0 gv, rm')
     | Some (md,_) => prop_reg_metadata lc' rm' id0 gv md
     end
| ((t, id0)::la', nil) => 
  (* FIXME: We should initalize them w.r.t their type size. *)
     let '(lc',rm') := _initializeFrameValues la' nil lc rm in
     (updateAddAL _ lc' id0 gundef, rm')
| _ => (lc, rm)
end.

Definition initLocals (la:args) (lg:list (GenericValue*option (metadata*typ))) 
  (rm : rmetadata) : GVMap * rmetadata :=
_initializeFrameValues la lg nil rm.

Inductive dsInsn : State -> State -> trace -> Prop :=
| dsReturn : forall S TD Ps F B rid RetTy Result lc rm gl fs F' B' c' cs' tmn' 
    lc' rm' EC Mem MM Mem' als als' lc'' rm'',   
  Instruction.isCallInst c' = true ->
  free_allocas TD Mem als = Some Mem' ->
  returnUpdateLocals TD Mem' c' Result lc lc' rm rm' gl = Some (lc'', rm'') ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B nil (insn_return rid RetTy Result) lc rm als)::
       (mkEC F' B' (c'::cs') tmn' lc' rm' als')::EC) gl fs Mem MM)
    (mkState S TD Ps 
      ((mkEC F' B' cs' tmn' lc'' rm'' als')::EC) gl fs Mem' MM)
    trace_nil

| dsReturnVoid : forall S TD Ps F B rid lc rm gl fs F' B' c' tmn' lc' rm' EC cs' 
    Mem MM Mem' als als',   
  Instruction.isCallInst c' = true ->
  free_allocas TD Mem als = Some Mem' ->
  getCallerReturnID c' = None ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B nil (insn_return_void rid) lc rm als)::
       (mkEC F' B' (c'::cs') tmn' lc' rm' als')::EC) gl fs Mem MM)
    (mkState S TD Ps 
      ((mkEC F' B' cs' tmn' lc' rm' als')::EC) gl fs Mem' MM)
    trace_nil

| dsBranch : forall S TD Ps F B lc rm gl fs bid Cond l1 l2 c l' ps' cs' tmn' lc' 
    rm' EC Mem MM als,   
  getOperandValue TD Mem Cond lc gl = Some c ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD Mem (block_intro l' ps' cs' tmn') B gl lc rm = 
    Some (lc', rm') ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B nil (insn_br bid Cond l1 l2) lc rm als)::EC) 
      gl fs Mem MM)
    (mkState S TD Ps 
      ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' rm' als)::EC) 
      gl fs Mem MM)
    trace_nil

| dsBranch_uncond : forall S TD Ps F B lc rm gl fs bid l l' ps' cs' tmn' lc' rm'
    EC Mem MM als,   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD Mem (block_intro l' ps' cs' tmn') B gl lc rm = 
    Some (lc', rm') ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B nil (insn_br_uncond bid l) lc rm als)::EC) 
      gl fs Mem MM)
    (mkState S TD Ps 
      ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' rm' als)::EC) 
      gl fs Mem MM)
    trace_nil

| dsBop: forall S TD Ps F B lc rm gl fs id bop sz v1 v2 gv3 EC cs tmn Mem MM als,
  BOP TD Mem lc gl bop sz v1 v2 = Some gv3 ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv3) rm als)::EC) gl fs Mem MM)
    trace_nil

| dsFBop: forall S TD Ps F B lc rm gl fs id fbop fp v1 v2 gv3 EC cs tmn Mem MM 
    als,
  FBOP TD Mem lc gl fbop fp v1 v2 = Some gv3 ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv3) rm als)::EC) 
      gl fs Mem MM)
    trace_nil

| dsExtractValue : forall S TD Ps F B lc rm gl fs id t v gv gv' idxs EC cs tmn 
    Mem MM als,
  getOperandValue TD Mem v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_extractvalue id t v idxs)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv') rm als)::EC) gl fs Mem MM)
    trace_nil

| dsInsertValue : forall S TD Ps F B lc rm gl fs id t v t' v' gv gv' gv'' idxs 
    EC cs tmn Mem MM als,
  getOperandValue TD Mem v lc gl = Some gv ->
  getOperandValue TD Mem v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_insertvalue id t v t' v' idxs)::cs) tmn lc rm als)
      ::EC) gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv'') rm als)::EC) gl fs Mem MM)
    trace_nil

| dsMalloc : forall S TD Ps F B lc rm gl fs id t v gn align EC cs tmn Mem MM als 
    Mem' tsz mb lc' rm' n,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD Mem v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  GV2int TD Size.ThirtyTwo gn = Some n ->
  prop_reg_metadata lc rm id (blk2GV TD mb) (mkMD (base2GV TD mb) 
    (bound2GV TD mb tsz n)) = (lc',rm') ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_malloc id t v align)::cs) tmn lc rm als)::EC) 
       gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn lc' rm' als)::EC) gl fs Mem' MM)
    trace_nil

| dsFree : forall S TD Ps F B lc rm gl fs fid t v EC cs tmn Mem als Mem' mptr MM,
  getOperandValue TD Mem v lc gl = Some mptr ->
  free TD Mem mptr = Some Mem'->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_free fid t v)::cs) tmn lc rm als)::EC) gl fs Mem MM) 
    (mkState S TD Ps ((mkEC F B cs tmn lc rm als)::EC) gl fs Mem' MM)
    trace_nil

| dsAlloca : forall S TD Ps F B lc rm gl fs id t v gn align EC cs tmn Mem MM als 
    Mem' tsz mb lc' rm' n,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD Mem v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  GV2int TD Size.ThirtyTwo gn = Some n ->
  prop_reg_metadata lc rm id (blk2GV TD mb) (mkMD (base2GV TD mb) 
    (bound2GV TD mb tsz n)) = (lc',rm') ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_alloca id t v align)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn lc' rm' (mb::als))::EC) gl fs Mem' MM)
    trace_nil

| dsLoad_nptr : forall S TD Ps F B lc rm gl fs id t align vp EC cs tmn Mem als 
    gvp gv MM md mt,
  get_reg_metadata TD Mem gl rm vp = Some (md,mt) ->
  getOperandValue TD Mem vp lc gl = Some gvp ->
  assert_mptr TD t gvp md ->
  mload TD Mem gvp t align = Some gv ->
  ~ isPointerTyp t ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_load id t vp align)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv) rm als)::EC) gl fs Mem MM)
    trace_nil

| dsLoad_ptr : forall S TD Ps F B lc rm gl fs id t align vp EC cs tmn Mem MM als 
    gvp gv md md' lc' rm' mt,
  get_reg_metadata TD Mem gl rm vp = Some (md,mt) ->
  getOperandValue TD Mem vp lc gl = Some gvp ->
  assert_mptr TD t gvp md ->
  mload TD Mem gvp t align = Some gv ->
  isPointerTyp t ->
  get_mem_metadata TD MM gvp = md' -> 
  prop_reg_metadata lc rm id gv md' = (lc', rm') ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_load id t vp align)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps ((mkEC F B cs tmn lc' rm' als)::EC) gl fs Mem MM)
    trace_nil

| dsLoad_abort : forall S TD Ps F B lc rm gl fs id t align vp EC cs tmn Mem als 
    gvp MM md mt,
  get_reg_metadata TD Mem gl rm vp = Some (md,mt) ->
  getOperandValue TD Mem vp lc gl = Some gvp ->
  ~ assert_mptr TD t gvp md ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_load id t vp align)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps nil gl fs Mem MM)
    trace_nil

| dsStore_nptr : forall S TD Ps F B lc rm gl fs sid t align v vp EC cs tmn Mem MM
    als gv gvp md Mem' mt,
  get_reg_metadata TD Mem gl rm vp = Some (md,mt) ->
  getOperandValue TD Mem v lc gl = Some gv ->
  getOperandValue TD Mem vp lc gl = Some gvp ->
  assert_mptr TD t gvp md ->
  mstore TD Mem gvp t gv align = Some Mem' ->
  ~ isPointerTyp t ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_store sid t v vp align)::cs) tmn lc rm als)::EC) 
       gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn lc rm als)::EC) gl fs Mem' MM)
    trace_nil

| dsStore_ptr : forall S TD Ps F B lc rm gl fs sid t align v vp EC cs tmn Mem MM
    als gv gvp md md' Mem' MM' mt mt',
  get_reg_metadata TD Mem gl rm vp = Some (md,mt) ->
  getOperandValue TD Mem v lc gl = Some gv ->
  getOperandValue TD Mem vp lc gl = Some gvp ->
  assert_mptr TD t gvp md ->
  mstore TD Mem gvp t gv align = Some Mem' ->
  isPointerTyp t ->
  get_reg_metadata TD Mem gl rm v = Some (md',mt') ->
  set_mem_metadata TD MM gvp md' = MM' -> 
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_store sid t v vp align)::cs) tmn lc rm als)::EC) 
       gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn lc rm als)::EC) gl fs Mem' MM')
    trace_nil

| dsStore_abort : forall S TD Ps F B lc rm gl fs sid t align v vp EC cs tmn Mem 
    MM als gv gvp md mt,
  get_reg_metadata TD Mem gl rm vp = Some (md,mt) ->
  getOperandValue TD Mem v lc gl = Some gv ->
  getOperandValue TD Mem vp lc gl = Some gvp ->
  ~ assert_mptr TD t gvp md ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_store sid t v vp align)::cs) tmn lc rm als)::EC) 
       gl fs Mem MM) 
    (mkState S TD Ps nil gl fs Mem MM)
    trace_nil

| dsGEP : forall S TD Ps F B lc rm gl fs id inbounds t vp idxs vidxs EC gvp gvp' 
                 cs tmn Mem MM als lc' rm' md mt,
  get_reg_metadata TD Mem gl rm vp = Some (md,mt) ->
  getOperandValue TD Mem vp lc gl = Some gvp ->
  values2GVs TD Mem idxs lc gl = Some vidxs ->
  GEP TD t gvp vidxs inbounds = Some gvp' ->
  prop_reg_metadata lc rm id gvp' md = (lc', rm') ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_gep id inbounds t vp idxs)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps ((mkEC F B cs tmn lc' rm' als)::EC) gl fs Mem MM)
    trace_nil 

| dsTrunc : forall S TD Ps F B lc rm gl fs id truncop t1 v1 t2 gv2 EC cs tmn 
                   Mem MM als,
  TRUNC TD Mem lc gl truncop t1 v1 t2 = Some gv2 ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv2) rm als)::EC) gl fs Mem MM)
    trace_nil

| dsExt : forall S TD Ps F B lc rm gl fs id extop t1 v1 t2 gv2 EC cs tmn Mem MM
                 als,
  EXT TD Mem lc gl extop t1 v1 t2 = Some gv2 ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc rm als)::EC) 
       gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv2) rm als)::EC) gl fs Mem MM)
    trace_nil

| dsBitcast_nptr : forall S TD Ps F B lc rm gl fs id t1 v1 t2 gv2 EC cs tmn Mem 
    MM als,
  CAST TD Mem lc gl castop_bitcast t1 v1 t2 = Some gv2 ->
  ~ isPointerTyp t1 ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_cast id castop_bitcast t1 v1 t2)::cs) tmn lc rm als)
        ::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv2) rm als)::EC) gl fs Mem MM)
    trace_nil

| dsBitcast_ptr : forall S TD Ps F B lc rm gl fs id t1 v1 t2 gv2 EC cs tmn Mem MM
    als md lc' rm' mt,
  CAST TD Mem lc gl castop_bitcast t1 v1 t2 = Some gv2 ->
  isPointerTyp t1 ->
  get_reg_metadata TD Mem gl rm v1 = Some (md,mt) ->
  prop_reg_metadata lc rm id gv2 md = (lc', rm') ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_cast id castop_bitcast t1 v1 t2)::cs) tmn lc rm als)
        ::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps ((mkEC F B cs tmn lc' rm' als)::EC) gl fs Mem MM)
    trace_nil

| dsInttoptr : forall S TD Ps F B lc rm gl fs id t1 v1 t2 gv2 EC cs tmn Mem MM
    als lc' rm',
  CAST TD Mem lc gl castop_inttoptr t1 v1 t2 = Some gv2 ->
  prop_reg_metadata lc rm id gv2 (mkMD null null) = (lc', rm') ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_cast id castop_inttoptr t1 v1 t2)::cs) tmn lc rm als)
        ::EC) 
       gl fs Mem MM) 
    (mkState S TD Ps ((mkEC F B cs tmn lc' rm' als)::EC) gl fs Mem MM)
    trace_nil

| dsOtherCast : forall S TD Ps F B lc rm gl fs id castop t1 v1 t2 gv2 EC cs tmn 
    Mem MM als,
  CAST TD Mem lc gl castop t1 v1 t2 = Some gv2 ->
  castop <> castop_bitcast /\ castop <> castop_inttoptr ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_cast id castop t1 v1 t2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv2) rm als)::EC) gl fs Mem MM)
    trace_nil

| dsIcmp : forall S TD Ps F B lc rm gl fs id cond t v1 v2 gv3 EC cs tmn Mem MM 
    als,
  ICMP TD Mem lc gl cond t v1 v2 = Some gv3 ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (updateAddAL _ lc id gv3) rm als)::EC) gl fs Mem MM)
    trace_nil

| dsFcmp : forall S TD Ps F B lc rm gl fs id fcond fp v1 v2 gv3 EC cs tmn Mem MM
    als,
  FCMP TD Mem lc gl fcond fp v1 v2 = Some gv3 ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps   
      ((mkEC F B cs tmn (updateAddAL _ lc id gv3) rm als)::EC) gl fs Mem MM)
    trace_nil

| dsSelect_nptr : forall S TD Ps F B lc rm gl fs id v0 t v1 v2 c EC cs tmn Mem MM
    als gv1 gv2,
  getOperandValue TD Mem v0 lc gl = Some c ->
  getOperandValue TD Mem v1 lc gl = Some gv1 ->
  getOperandValue TD Mem v2 lc gl = Some gv2 ->
  ~ isPointerTyp t ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn (if isGVZero TD c 
                            then updateAddAL _ lc id gv2 
                            else updateAddAL _ lc id gv1) rm als)::EC) 
      gl fs Mem MM)
    trace_nil

| dsSelect_ptr : forall S TD Ps F B lc rm gl fs id v0 t v1 v2 c EC cs tmn Mem MM
    als gv1 gv2 md1 md2 lc' rm' mt1 mt2,
  getOperandValue TD Mem v0 lc gl = Some c ->
  getOperandValue TD Mem v1 lc gl = Some gv1 ->
  getOperandValue TD Mem v2 lc gl = Some gv2 ->
  isPointerTyp t ->
  get_reg_metadata TD Mem gl rm v1 = Some (md1,mt1) ->
  get_reg_metadata TD Mem gl rm v2 = Some (md2,mt2) ->
  (if isGVZero TD c then 
    prop_reg_metadata lc rm id gv2 md2
  else
    prop_reg_metadata lc rm id gv1 md1)
    = (lc', rm') ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 
    (mkState S TD Ps 
      ((mkEC F B cs tmn lc' rm' als)::EC) 
      gl fs Mem MM)
    trace_nil

| dsCall : forall S TD Ps F B lc rm gl fs rid noret ca fid fv lp cs tmn ogvs
                            l' ps' cs' tmn' EC fa rt la va lb Mem MM als rm' lc',
  (* only look up the current module for the time being, 
     do not support linkage. *)
  LLVMopsem.lookupFdefViaGV TD Mem Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD Mem lp lc gl rm = Some ogvs ->
  initLocals la ogvs rm = (lc', rm') ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_call rid noret ca rt fv lp)::cs) tmn lc rm als)
        ::EC) gl fs Mem MM)
    (mkState S TD Ps 
      ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                (block_intro l' ps' cs' tmn') cs' tmn' 
                lc' rm' nil)::
       (mkEC F B ((insn_call rid noret ca rt fv lp)::cs) tmn lc rm als)
         ::EC) gl fs Mem MM)
    trace_nil 

| dsExCall : forall S TD Ps F B lc rm gl fs rid noret tailc fid fv lp cs tmn EC 
                    fa rt la va Mem als oresult Mem' lc' MM gvs,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  LLVMopsem.lookupExFdecViaGV TD Mem Ps gl lc fs fv = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) -> 
  LLVMgv.params2GVs TD Mem lp lc gl = Some gvs ->
  LLVMopsem.callExternalFunction Mem fid gvs = (oresult, Mem') ->
  LLVMopsem.exCallUpdateLocals noret rid oresult lc = Some lc' ->
  dsInsn 
    (mkState S TD Ps 
      ((mkEC F B ((insn_call rid noret tailc rt fv lp)::cs) tmn lc rm als)
       ::EC) gl fs Mem MM)
    (mkState S TD Ps ((mkEC F B cs tmn lc' rm als)::EC) gl fs Mem' MM)
    trace_nil 
.

Definition ds_isFinialState (state:State) : bool :=
match state with
| (mkState _ _ _ 
    ((mkEC _ _ nil (insn_return_void _) _ _ _)::nil) _ _ _ _) => true
| (mkState _ _ _ 
    ((mkEC _ _ nil (insn_return _ _ _) _ _ _)::nil) _ _ _ _) => true 
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

End SoftBound.

Tactic Notation "sb_dbCmd_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBop" | c "dbBop_error" | c "dbFBop" | c "dbFBop_eror" |
    c "dbExtractValue" | c "dbExtractValue_error" | 
    c "dbInsertValue" | c "dbInsertValue_error" |
    c "dbMalloc" | c "dbMalloc_error" | c "dbFree" | c "dbFree_error" |
    c "dbAlloca" | c "dbAlloca_error" | 
    c "dbLoad_nptr" | c "dbLoad_ptr" | c "dbLoad_error1" | 
    c "dbLoad_error2" | c "dbLoad_error3" | c "dbLoad_abort" |
    c "dbStore_nptr" | c "dbStore_ptr" | c "dbStore_error1" |
    c "dbStore_error2" | c "dbStore_error3" | c "dbStore_abort" |  
    c "dbGEP" | c "dbGEP_error" |
    c "dbTrunc" | c "dbTrunc_error" |
    c "dbExt" | c "dbExt_error" |
    c "dbBitcast_nptr" | c "dbBitcast_ptr" | c "dbInttoptr" | c "dbOtherCast" |
    c "dbCast_error" | 
    c "dbIcmp" | c "dbIcmp_error" |
    c "dbFcmp" | c "dbFcmp_error" | 
    c "dbSelect_nptr" | c "dbSelect_ptr"| c "dbSelect_error" |
    c "dbLib" | c "dbLib_error" ].

Tactic Notation "sb_dbTerminator_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBranch" | c "dbBranch_uncond" ].

Tactic Notation "sb_dbCmds_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCmds_nil" | c "dbCmds_cons" | c "dbCmds_cons_error" ].

Tactic Notation "sb_db_mutind_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCall_internal" | c "dbCall_external" |
    c "dbCall_internal_error1" | c "dbCall_internal_error2" |
    c "dbCall_external_error1" | c "dbCall_external_error2" |
    c "dbSubblock_ok" | c "dbSubblock_error" | 
    c "dbSubblocks_nil" | c "dbSubblocks_cons" | c "dbSubblocks_cons_error" |
    c "dbBlock_ok" | c "dbBlock_error1" | c "dbBlock_error2" | 
    c "dbBlocks_nil" | c "dbBlocks_cons" | c "dbBlocks_cons_error" | 
    c "dbFdef_func" | c "dbFdef_func_error1" | c "dbFdef_func_error2" |
    c "dbFdef_func_error3" | c "dbFdef_func_error4" | c "dbFdef_func_error5" |
    c "dbFdef_proc" | c "dbFdef_proc_error1" | c "dbFdef_proc_error2" |
    c "dbFdef_proc_error3" | c "dbFdef_proc_error4" | c "dbFdef_proc_error5"
  ].

Tactic Notation "sb_dsInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "dsReturn" | c "dsReturnVoid" | c "dsBranch" | c "dsBranch_uncond" |
    c "dsBop" | c "dsFBop" | c "dsExtractValue" | c "dsInsertValue" |
    c "dsMalloc" | c "dsFree" | c "dsAlloca" | 
    c "dsLoad_nptr" | c "dsLoad_ptr" | c "dsLoad_abort" | 
    c "dsStore_nptr" | c "dsStore_ptr" | c "dsStore_abort" | 
    c "dsGEP" | c "dsTrunc" | c "dsExt" | 
    c "dsBitcast_nptr" | c "dsBitcast_ptr" | c "dsInttoptr" | c "dsOthercast" | 
    c "dsIcmp" | c "dsFcmp" | 
    c "dsSelect_nptr" | c "dsSelect_ptr" |  
    c "dsCall" | c "dsExCall" ].


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
