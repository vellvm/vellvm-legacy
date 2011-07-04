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
Require Import Floats.

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

Definition undef_gvs c : GVs :=
match c with
| AST.Mint sz => fun gv => exists z, gv = (Vint sz z, c)::nil
| AST.Mfloat32 | AST.Mfloat64 => fun gv => exists f, gv = (Vfloat f, c)::nil
(*| _ =>  Full_set _*)
end.

Definition gv2gvs (gv:GenericValue) : GVs :=
match gv with
| (Vundef, c)::nil => undef_gvs c
| _ => Singleton GenericValue gv
end.

Notation "$ gv $" := (gv2gvs gv) (at level 41).
Notation "% ogv %" := (mmap GenericValue GVs gv2gvs ogv) (at level 41).
Notation "gv @ gvs" := (Ensembles.In GenericValue gvs gv) 
                         (at level 43, right associativity).

Lemma undef_gvs__inhabited : forall c, 
  Ensembles.Inhabited GenericValue (undef_gvs c).
Proof.
  destruct c; simpl.
    apply Ensembles.Inhabited_intro with 
      (x:=(Vint n (Int.zero n), AST.Mint n)::nil).
    unfold Ensembles.In.
    exists (Int.zero n). auto.
    
    apply Ensembles.Inhabited_intro with 
      (x:=(Vfloat Float.zero, AST.Mfloat32)::nil).
    unfold Ensembles.In.
    exists Float.zero. auto.
    
    apply Ensembles.Inhabited_intro with 
      (x:=(Vfloat Float.zero, AST.Mfloat64)::nil).
    unfold Ensembles.In.
    exists Float.zero. auto.
Qed.

Lemma gv2gvs__inhabited : forall gv, 
  Ensembles.Inhabited GenericValue ($ gv $).
Proof.
  intros gv.
  destruct gv; simpl.
    apply Ensembles.Inhabited_intro with (x:=nil).
    apply Ensembles.In_singleton.

    destruct p.
    destruct v; auto using singleton_inhabited, undef_gvs__inhabited.
    destruct gv; auto using singleton_inhabited, undef_gvs__inhabited.
Qed.

Lemma ogv2gvs__inhabited : forall ogv gvs,
  %ogv% = ret gvs ->
  Ensembles.Inhabited GenericValue gvs.
Proof.
  destruct ogv; intros; inv H.
    apply gv2gvs__inhabited.
Qed.

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
  Some (fun gv => exists ma, exists vidxs, exists gv', 
        ma @ mas /\ vidxs @@ vidxss /\
        LLVMgv.GEP TD t ma vidxs inbounds = Some gv' /\ (gv @ $ gv' $)).

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
| (((t, _), id)::la', nil) => 
  (* FIXME: We should initalize them w.r.t their type size. *)
  updateAddAL _ (_initializeFrameValues la' nil locals) id ($(gundef t)$)
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

End NDopsem.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
