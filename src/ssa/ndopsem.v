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

Definition cundef_gvs gv c t : GVs :=
match t with
| typ_int sz => fun gv => exists z, gv = (Vint sz z, c)::nil
| typ_floatpoint _ => fun gv => exists f, gv = (Vfloat f, c)::nil
| typ_pointer _ => 
    fun gv => exists b, exists ofs, gv = (Vptr b ofs, AST.Mint 31)::nil
| _ => Singleton GenericValue gv
end.

Definition cgv2gvs (gv:GenericValue) t : GVs :=
match gv with
| (Vundef, c)::nil => cundef_gvs gv c t
| _ => Singleton GenericValue gv
end.

Definition const2GV (TD:TargetData) (gl:GVMap) (c:const) : option GVs :=
match (_const2GV TD gl c) with
| None => None
| Some (gv, t) => Some (cgv2gvs gv t)
end.

Definition getOperandValue (TD:TargetData) (v:value) (locals:GVsMap) 
  (globals:GVMap) : option GVs := 
match v with
| value_id id => lookupAL _ locals id 
| value_const c => const2GV TD globals c
end.

Definition undef_gvs gv c t : GVs :=
match t with
| typ_int sz =>
    Ensembles.Union _ (Singleton _ ((Vundef, c)::nil))
      (fun gv => exists z, gv = (Vint sz z, c)::nil)
| typ_floatpoint _ => 
    Ensembles.Union _ (Singleton _ ((Vundef, c)::nil))
      (fun gv => exists f, gv = (Vfloat f, c)::nil)
| typ_pointer _ =>
    Ensembles.Union _ (Singleton _ ((Vundef, c)::nil))
      (fun gv => exists b, exists ofs, gv = (Vptr b ofs, c)::nil)
| _ => Ensembles.Union _ (Singleton _ ((Vundef, c)::nil))
         (Singleton GenericValue gv)
end.

Definition gv2gvs (gv:GenericValue) (t:typ) : GVs :=
match gv with
| (Vundef, c)::nil => undef_gvs gv c t
| _ => Singleton GenericValue gv
end.

Notation "$ gv # t $" := (gv2gvs gv t) (at level 41).
Notation "gv @ gvs" := (Ensembles.In GenericValue gvs gv) 
                         (at level 43, right associativity).

Lemma undef_gvs__inhabited : forall gv c t, 
  Ensembles.Inhabited GenericValue (undef_gvs gv c t).
Proof.
  destruct t; simpl;
    eapply Ensembles.Inhabited_intro; 
      try solve [eauto | apply Union_introl; constructor].
Qed.

Lemma gv2gvs__inhabited : forall gv t, 
  Ensembles.Inhabited GenericValue ($ gv # t $).
Proof.
  intros gv t.
  destruct gv; simpl.
    apply Ensembles.Inhabited_intro with (x:=nil).
    apply Ensembles.In_singleton.

    destruct p.
    destruct v; auto using singleton_inhabited, undef_gvs__inhabited.
    destruct gv; auto using singleton_inhabited, undef_gvs__inhabited.
Qed.

Lemma cundef_gvs__inhabited : forall gv c t, 
  Ensembles.Inhabited GenericValue (cundef_gvs gv c t).
Proof.
  destruct t; simpl; 
    try solve [eapply Ensembles.Inhabited_intro; constructor].
    eapply Ensembles.Inhabited_intro.
      exists (Int.zero s). auto.

    eapply Ensembles.Inhabited_intro.
      exists Float.zero. auto.

    eapply Ensembles.Inhabited_intro.
      exists Mem.nullptr. exists (Int.repr 31 0). auto.
Qed.

Lemma cgv2gvs__inhabited : forall gv t, 
  Ensembles.Inhabited GenericValue (cgv2gvs gv t).
Proof.
  intros gv t.
  destruct gv; simpl.
    apply Ensembles.Inhabited_intro with (x:=nil).
    apply Ensembles.In_singleton.

    destruct p.
    destruct v; auto using singleton_inhabited, cundef_gvs__inhabited.
    destruct gv; auto using singleton_inhabited, cundef_gvs__inhabited.
Qed.

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
  gvs1 gvs2 t : GVs :=
  fun gv3 => exists gv1, exists gv2, exists gv3',
    gv1 @ gvs1 /\ gv2 @ gvs2 /\ f gv1 gv2 = Some gv3' /\ (gv3 @ $ gv3' # t $).

Definition BOP (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:bop) (bsz:sz) 
  (v1 v2:value) : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) => 
    Some (lift_op2 (mbop TD op bsz) gvs1 gvs2 (typ_int bsz))
| _ => None
end
.

Definition FBOP (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:fbop) fp
  (v1 v2:value) : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) => 
    Some (lift_op2 (mfbop TD op fp) gvs1 gvs2 (typ_floatpoint fp))
| _ => None
end
.

Definition ICMP (TD:TargetData) (lc:GVsMap) (gl:GVMap) c t (v1 v2:value) 
  : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) => 
    Some (lift_op2 (micmp TD c t) gvs1 gvs2 (typ_int 0%nat))
| _ => None
end
.

Definition FCMP (TD:TargetData) (lc:GVsMap) (gl:GVMap) c fp (v1 v2:value) 
  : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) => 
    Some (lift_op2 (mfcmp TD c fp) gvs1 gvs2 (typ_int 0%nat))
| _ => None
end
.

Definition lift_op1 (f: GenericValue -> option GenericValue) gvs1 t : GVs :=
  fun gv2 => exists gv1, exists gv2', 
    gv1 @ gvs1 /\ f gv1 = Some gv2' /\ (gv2 @ $ gv2' # t $).

Definition CAST (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:castop) 
  (t1:typ) (v1:value) (t2:typ) : option GVs:=
match (getOperandValue TD v1 lc gl) with
| (Some gvs1) => Some (lift_op1 (mcast TD op t1 t2) gvs1 t2)
| _ => None
end
.

Definition TRUNC (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:truncop) 
  (t1:typ) (v1:value) (t2:typ) : option GVs:=
match (getOperandValue TD v1 lc gl) with
| (Some gvs1) => Some (lift_op1 (mtrunc TD op t1 t2) gvs1 t2)
| _ => None
end
.

Definition EXT (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:extop) 
  (t1:typ) (v1:value) (t2:typ) : option GVs:=
match (getOperandValue TD v1 lc gl) with
| (Some gvs1) => Some (lift_op1 (mext TD op t1 t2) gvs1 t2)
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
        LLVMgv.GEP TD t ma vidxs inbounds = Some gv' /\ 
        (gv @ $ gv' # (typ_pointer typ_void) $)).

Definition mget' TD o t' gv: option GenericValue :=
match mget TD gv o t' with 
| Some gv' => Some gv'
| None => Some (gundef t')
end.

Definition extractGenericValue (TD:TargetData) (t:typ) (gvs : GVs) 
  (cidxs : list_const) : option GVs :=
match (intConsts2Nats TD cidxs) with
| None => Some ($ (uninits 1) # (typ_int 7%nat) $)
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some (o, t') => Some (lift_op1 (mget' TD o t') gvs t')
  | None => Some ($ (uninits 1) # (typ_int 7%nat) $)
  end
end.

Definition mset' TD o t t0 gv gv0 : option GenericValue :=
match (mset TD gv o t0 gv0) with
| Some gv' => Some gv'
| None => Some (gundef t)
end.

Definition insertGenericValue (TD:TargetData) (t:typ) (gvs:GVs)
  (cidxs:list_const) (t0:typ) (gvs0:GVs) : option GVs :=
match (intConsts2Nats TD cidxs) with
| None => Some ($ (gundef t) # t $)
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some (o, _) => Some (lift_op2 (mset' TD o t t0) gvs gvs0 t)
  | None => Some ($ (gundef t) # t $)
  end
end.

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
  updateAddAL _ (_initializeFrameValues la' nil locals) id ($(gundef t) # t$)
| _ => locals
end.

Definition initLocals (la:args) (lg:list GVs): GVsMap := 
_initializeFrameValues la lg nil.

Definition lookupFdefViaPtr Ps fs fptr : option fdef :=
  do fn <- LLVMopsem.lookupFdefViaGVFromFunTable fs fptr;
     lookupFdefViaIDFromProducts Ps fn.

Definition lookupExFdecViaPtr (Ps:products) (fs:GVMap) fptr : option fdec :=
do fn <- LLVMopsem.lookupFdefViaGVFromFunTable fs fptr;
    match lookupFdefViaIDFromProducts Ps fn with 
    | Some _ => None
    | None => lookupFdecViaIDFromProducts Ps fn
    end
.

Definition getReturnTyp t0 : typ :=
match t0 with
| typ_function t1 _ _ => t1
| _ => typ_void
end.

Definition exCallUpdateLocals (ft:typ) (noret:bool) (rid:id) 
  (oResult:option GenericValue) (lc :GVsMap) : option GVsMap :=
  match noret with
  | false =>
      match oResult with
      | None => None
      | Some Result => Some (updateAddAL _ lc rid ($ Result # getReturnTyp ft $))
      end
  | true => Some lc
  end.

Inductive nsInsn : State -> State -> trace -> Prop :=
| nsReturn : forall S TD Ps F B rid RetTy Result lc gl fs
                            F' B' c' cs' tmn' lc' EC
                            Mem Mem' als als' lc'',   
  Instruction.isCallInst c' = true ->
  (* FIXME: we should get Result before free?! *)
  free_allocas TD Mem als = Some Mem' ->
  returnUpdateLocals TD c' Result lc lc' gl = Some lc'' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_return rid RetTy Result) lc als)::
                      (mkEC F' B' (c'::cs') tmn' lc' als')::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC F' B' cs' tmn' lc'' als')::EC) gl fs Mem')
    trace_nil 

| nsReturnVoid : forall S TD Ps F B rid lc gl fs
                            F' B' c' tmn' lc' EC
                            cs' Mem Mem' als als',   
  Instruction.isCallInst c' = true ->
  free_allocas TD Mem als = Some Mem' ->
  getCallerReturnID c' = None ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_return_void rid) lc als)::
                      (mkEC F' B' (c'::cs') tmn' lc' als')::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC F' B' cs' tmn' lc' als')::EC) gl fs Mem')
    trace_nil 

| nsBranch : forall S TD Ps F B lc gl fs bid Cond l1 l2 conds c
                              l' ps' cs' tmn' lc' EC Mem als,   
  getOperandValue TD Cond lc gl = Some conds ->
  c @ conds ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  nsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br bid Cond l1 l2) lc als)::EC) 
                       gl fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' als)
                       ::EC) gl fs Mem)
    trace_nil 

| nsBranch_uncond : forall S TD Ps F B lc gl fs bid l 
                           l' ps' cs' tmn' lc' EC Mem als,   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  nsInsn 
    (mkState S TD Ps ((mkEC F B nil (insn_br_uncond bid l) lc als)::EC) 
                       gl fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' als)
                       ::EC) gl fs Mem)
    trace_nil 

| nsBop: forall S TD Ps F B lc gl fs id bop sz v1 v2 gvs3 EC cs tmn Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gvs3 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gvs3) als)::EC) 
                      gl fs Mem)
    trace_nil 

| nsFBop: forall S TD Ps F B lc gl fs id fbop fp v1 v2 gvs3 EC cs tmn Mem als,
  FBOP TD lc gl fbop fp v1 v2 = Some gvs3 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gvs3) als)::EC) 
                      gl fs Mem)
    trace_nil 

| nsExtractValue : forall S TD Ps F B lc gl fs id t v gvs gvs' idxs EC cs tmn 
                          Mem als,
  getOperandValue TD v lc gl = Some gvs ->
  extractGenericValue TD t gvs idxs = Some gvs' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_extractvalue id t v idxs)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gvs') als)::EC) 
                       gl fs Mem)
    trace_nil 

| nsInsertValue : forall S TD Ps F B lc gl fs id t v t' v' gvs gvs' gvs'' idxs 
                         EC cs tmn Mem als,
  getOperandValue TD v lc gl = Some gvs ->
  getOperandValue TD v' lc gl = Some gvs' ->
  insertGenericValue TD t gvs idxs t' gvs' = Some gvs'' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_insertvalue id t v t' v' idxs)::cs) tmn 
                       lc als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gvs'') als)::EC) 
                       gl fs Mem)
    trace_nil 

| nsMalloc : forall S TD Ps F B lc gl fs id t v gns gn align EC cs tmn Mem als 
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_malloc id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn 
                   (updateAddAL _ lc id ($ (blk2GV TD mb) # (typ_pointer t) $)) 
                   als)::EC) gl fs Mem')
    trace_nil

| nsFree : forall S TD Ps F B lc gl fs fid t v EC cs tmn Mem als Mem' mptrs mptr,
  getOperandValue TD v lc gl = Some mptrs ->
  mptr @ mptrs ->
  free TD Mem mptr = Some Mem'->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_free fid t v)::cs) tmn lc als)::EC) 
                       gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) gl fs Mem')
    trace_nil

| nsAlloca : forall S TD Ps F B lc gl fs id t v gns gn align EC cs tmn Mem als 
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_alloca id t v align)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn 
                   (updateAddAL _ lc id ($ (blk2GV TD mb) # (typ_pointer t) $)) 
                   (mb::als))::EC) gl fs Mem')
    trace_nil

| nsLoad : forall S TD Ps F B lc gl fs id t align v EC cs tmn Mem als mps mp gv,
  getOperandValue TD v lc gl = Some mps ->
  mp @ mps ->
  mload TD Mem mp t align = Some gv ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_load id t v align)::cs) tmn lc als)::
                       EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id ($ gv # t $)) als)::
                       EC) gl fs Mem)
    trace_nil

| nsStore : forall S TD Ps F B lc gl fs sid t align v1 v2 EC cs tmn Mem als 
                   mp2 gv1 Mem' gvs1 mps2,
  getOperandValue TD v1 lc gl = Some gvs1 ->
  getOperandValue TD v2 lc gl = Some mps2 ->
  gv1 @ gvs1 -> mp2 @ mps2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_store sid t v1 v2 align)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn lc als)::EC) gl fs Mem')
    trace_nil

| nsGEP : forall S TD Ps F B lc gl fs id inbounds t v idxs vidxs EC mp mp' 
                 cs tmn Mem als,
  getOperandValue TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxs ->
  GEP TD t mp vidxs inbounds = Some mp' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_gep id inbounds t v idxs)::cs) tmn lc
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id mp') als)::EC) 
                       gl fs Mem)
    trace_nil 

| nsTrunc : forall S TD Ps F B lc gl fs id truncop t1 v1 t2 gvs2 EC cs tmn 
                   Mem als,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gvs2 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gvs2) als)::EC) 
                       gl fs Mem)
    trace_nil

| nsExt : forall S TD Ps F B lc gl fs id extop t1 v1 t2 gvs2 EC cs tmn Mem 
                 als,
  EXT TD lc gl extop t1 v1 t2 = Some gvs2 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gvs2) als)::EC) 
                       gl fs Mem)
    trace_nil

| nsCast : forall S TD Ps F B lc gl fs id castop t1 v1 t2 gvs2 EC cs tmn Mem 
                  als,
  CAST TD lc gl castop t1 v1 t2 = Some gvs2 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_cast id castop t1 v1 t2)::cs) tmn lc 
                      als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gvs2) als)::EC) 
                      gl fs Mem)
    trace_nil

| nsIcmp : forall S TD Ps F B lc gl fs id cond t v1 v2 gvs3 EC cs tmn Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gvs3 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gvs3) als)::EC) 
                       gl fs Mem)
    trace_nil

| nsFcmp : forall S TD Ps F B lc gl fs id fcond fp v1 v2 gvs3 EC cs tmn Mem 
                  als,
  FCMP TD lc gl fcond fp v1 v2 = Some gvs3 ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc 
                       als)::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id gvs3) als)::EC) 
                       gl fs Mem)
    trace_nil

| nsSelect : forall S TD Ps F B lc gl fs id v0 t v1 v2 cond c EC cs tmn Mem als 
                    gvs1 gvs2,
  getOperandValue TD v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gvs1 ->
  getOperandValue TD v2 lc gl = Some gvs2 ->
  c @ cond ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc als)
                      ::EC) gl fs Mem) 
    (mkState S TD Ps ((mkEC F B cs tmn (if isGVZero TD c 
                                        then updateAddAL _ lc id gvs2 
                                        else updateAddAL _ lc id gvs1) als)
                      ::EC) gl fs Mem)
    trace_nil

| nsCall : forall S TD Ps F B lc gl fs rid noret ca fid fv lp cs tmn fptrs fptr
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
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                       (block_intro l' ps' cs' tmn') cs' tmn' 
                       (initLocals la gvs) 
                       nil)::
                      (mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem)
    trace_nil 

| nsExCall : forall S TD Ps F B lc gl fs rid noret ca fid fv lp cs tmn EC 
                    rt la Mem als oresult Mem' lc' va ft fa gvs fptr fptrs gvss,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  getOperandValue TD fv lc gl = Some fptrs -> 
  fptr @ fptrs -> 
  lookupExFdecViaPtr Ps fs fptr = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  params2GVs TD lp lc gl = Some gvss ->
  gvs @@ gvss ->
  LLVMopsem.callExternalFunction Mem fid gvs = Some (oresult, Mem') ->
  exCallUpdateLocals ft noret rid oresult lc = Some lc' ->
  nsInsn 
    (mkState S TD Ps ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) gl fs Mem)
    (mkState S TD Ps ((mkEC F B cs tmn lc' als)::EC) gl fs Mem')
    trace_nil 
.

Hint Constructors nsInsn.

Definition ns_genInitState (S:system) (main:id) (Args:list GVs) (initmem:mem) 
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

Definition ns_isFinialState (state:State) : bool :=
match state with
| (mkState _ _ _ ((mkEC _ _ nil (insn_return_void _) _ _)::nil) _ _ _) => true
| (mkState _ _ _ ((mkEC _ _ nil (insn_return _ _ _) _ _)::nil) _ _ _) => true 
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

Inductive ns_converges : system -> id -> list GVs -> State -> Prop :=
| ns_converges_intro : forall (s:system) (main:id) (VarArgs:list GVs) 
                              (IS FS:State) tr,
  ns_genInitState s main VarArgs Mem.empty = Some IS ->
  nsop_star IS FS tr ->
  ns_isFinialState FS ->
  ns_converges s main VarArgs FS
.

Inductive ns_diverges : system -> id -> list GVs -> Trace -> Prop :=
| ns_diverges_intro : forall (s:system) (main:id) (VarArgs:list GVs) 
                             (IS:State) tr,
  ns_genInitState s main VarArgs Mem.empty = Some IS ->
  nsop_diverges IS tr ->
  ns_diverges s main VarArgs tr
.

Inductive ns_goeswrong : system -> id -> list GVs -> State -> Prop :=
| ns_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GVs) 
                              (IS FS:State) tr,
  ns_genInitState s main VarArgs Mem.empty = Some IS ->
  nsop_star IS FS tr ->
  ~ ns_isFinialState FS ->
  ns_goeswrong s main VarArgs FS
.

End NDopsem.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
