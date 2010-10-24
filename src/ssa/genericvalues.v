Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
(* Add LoadPath "../../../theory/metatheory". *)
Require Import List.
Require Import Arith.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import assoclist.
Require Import ssa_def.
Require Import ssa_lib.
Require Import Memory.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import targetdata.
Require Import ZArith.

Module Type LLVMgvType.

Export LLVMsyntax.
Export LLVMlib.
Export LLVMtd.

Variable GenericValue : Type.
Definition GVMap := list (id*GenericValue).
Variable mblock : Type.
Definition mptr := GenericValue.
Variable null : GenericValue.

Variable sizeGenericValue : GenericValue -> nat.
Variable uninits : nat -> GenericValue.
Variable blk2GV : TargetData -> mblock -> GenericValue.
Variable isGVZero : TargetData -> GenericValue -> bool.

(**************************************)
(** Convert const to GV with storesize, and look up GV from operands. *)
Variable const2GV : TargetData -> GVMap -> const -> option GenericValue.

Definition getOperandValue (TD:TargetData) (v:value) (locals:GVMap) (globals:GVMap) : option GenericValue := 
match v with
| value_id id => lookupAL _ locals id 
| value_const c => (const2GV TD globals c)
end.

(**************************************)
(* conversion between different lists *)

Variable params2OpGVs : TargetData -> params -> GVMap -> GVMap -> list (option GenericValue).
Variable opGVs2GVs : list (option GenericValue) -> list GenericValue.
Variable params2GVs : TargetData -> params -> GVMap -> GVMap -> list GenericValue.
Variable values2GVs : TargetData -> list_value -> GVMap -> GVMap -> option (list GenericValue).
Variable intValues2Nats : TargetData -> list_value -> GVMap -> GVMap -> option (list Z).
Variable intConsts2Nats : TargetData -> list_const -> option (list Z).
Variable GVs2Nats : TargetData -> list GenericValue -> option (list Z).

(**************************************)
(* helping functions *)

Variable _initializeFrameValues : args -> list GenericValue -> GVMap -> GVMap.
Variable initLocals : args -> list GenericValue -> GVMap.

Variable extractGenericValue : TargetData -> typ -> GenericValue -> list_const -> option GenericValue.
Variable insertGenericValue : TargetData -> typ -> GenericValue -> list_const ->typ -> GenericValue -> option GenericValue.
Variable GEP : TargetData -> typ -> GenericValue -> list GenericValue -> bool -> option GenericValue.
Variable mbop : TargetData -> bop -> sz -> GenericValue -> GenericValue -> option GenericValue.
Variable mcast : TargetData -> castop -> typ -> GenericValue -> typ -> option GenericValue.
Variable mext : TargetData -> extop -> typ -> GenericValue -> typ -> option GenericValue.
Variable micmp :TargetData -> cond -> typ -> GenericValue -> GenericValue -> option GenericValue.

Definition BOP (TD:TargetData) (lc gl:GVMap) (op:bop) (bsz:sz) (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => mbop TD op bsz gv1 gv2
| _ => None
end
.

Definition CAST (TD:TargetData) (lc gl:GVMap) (op:castop) (t1:typ) (v1:value) (t2:typ) : option GenericValue:=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mcast TD op t1 gv1 t2
| _ => None
end
.

Definition EXT (TD:TargetData) (lc gl:GVMap) (op:extop) (t1:typ) (v1:value) (t2:typ) : option GenericValue :=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mext TD op t1 gv1 t2
| _ => None
end
.

Definition ICMP (TD:TargetData) (lc gl:GVMap) (c:cond) (t:typ) (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => micmp TD c t gv1 gv2
| _ => None
end.

Lemma BOP_inversion : forall TD lc gl b s v1 v2 gv,
  BOP TD lc gl b s v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    mbop TD b s gv1 gv2 = Some gv.
Proof.
  intros TD lc gl b s v1 v2 gv HBOP.
  unfold BOP in HBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HBOP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HBOP].
      remember (mbop TD b s g g0) as R.
      destruct R; inversion HBOP; subst.
        exists g. exists g0. auto.
Qed.

Lemma CAST_inversion : forall TD lc gl op t1 v1 t2 gv,
  CAST TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mcast TD op t1 gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HCAST.
  unfold CAST in HCAST.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HCAST].
    remember (mcast TD op t1 g t2) as R.
    destruct R; inversion HCAST; subst.
      exists g. auto.
Qed.

Lemma EXT_inversion : forall TD lc gl op t1 v1 t2 gv,
  EXT TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mext TD op t1 gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HEXT.
  unfold EXT in HEXT.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HEXT].
    remember (mext TD op t1 g t2) as R.
    destruct R; inversion HEXT; subst.
      exists g. auto.
Qed.

Lemma ICMP_inversion : forall TD lc gl cond t v1 v2 gv,
  ICMP TD lc gl cond t v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    micmp TD cond t gv1 gv2 = Some gv.
Proof.
  intros TD lc gl cond0 t v1 v2 gv HICMP.
  unfold ICMP in HICMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HICMP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HICMP].
      remember (micmp TD cond0 t g g0) as R.
      destruct R; inversion HICMP; subst.
        exists g. exists g0. auto.
Qed.

Axiom intValues2Nats_inversion : forall l0 lc gl TD ns0,
  intValues2Nats TD l0 lc gl = Some ns0 ->
  exists gvs0, 
    values2GVs TD l0 lc gl = Some gvs0 /\
    GVs2Nats TD gvs0 = Some ns0.

Axiom values2GVs_GVs2Nats__intValues2Nats : forall l0 lc gl TD gvs0,
  values2GVs TD l0 lc gl = Some gvs0 ->
  GVs2Nats TD gvs0 = intValues2Nats TD l0 lc gl.

Axiom const2GV_eqAL : forall c gl1 gl2 TD, 
  eqAL _ gl1 gl2 -> 
  const2GV TD gl1 c = const2GV TD gl2 c.

Lemma getOperandValue_eqAL : forall lc1 gl lc2 v TD,
  eqAL _ lc1 lc2 ->
  getOperandValue TD v lc1 gl = getOperandValue TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD HeqAL.
  unfold getOperandValue in *.
  destruct v; auto.
Qed.

Lemma BOP_eqAL : forall lc1 gl lc2 bop0 sz0 v1 v2 TD,
  eqAL _ lc1 lc2 ->
  BOP TD lc1 gl bop0 sz0 v1 v2 = BOP TD lc2 gl bop0 sz0 v1 v2.
Proof.
  intros lc1 gl lc2 bop0 sz0 v1 v2 TD HeqEnv.
  unfold BOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma CAST_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  CAST TD lc1 gl op t1 v1 t2 = CAST TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold CAST in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.


Lemma EXT_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  EXT TD lc1 gl op t1 v1 t2 = EXT TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold EXT in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma ICMP_eqAL : forall lc1 gl lc2 cond t v1 v2 TD,
  eqAL _ lc1 lc2 ->
  ICMP TD lc1 gl cond t v1 v2 = ICMP TD lc2 gl cond t v1 v2.
Proof.
  intros lc1 gl lc2 cond0 t v1 v2 TD HeqAL.
  unfold ICMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Axiom intValues2Nats_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  intValues2Nats TD l0 lc1 gl = intValues2Nats TD l0 lc2 gl.

Axiom values2GVs_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  values2GVs TD l0 lc1 gl = values2GVs TD l0 lc2 gl.

End LLVMgvType.

Module LLVMgv <: LLVMgvType.

(*
Definition GenericValue := mvalue.
Definition GV2nat := mvalue2nat.
Definition GV2ptr := mvalue2mptr.
Definition isGVUndef := isMvalueUndef.
Definition nat2GV := nat2mvalue.
Definition undef2GV := undef2mvalue.
Definition ptr2GV TD p := mptr2mvalue TD p (getPointerSizeInBits TD).
*)

Export LLVMsyntax.
Export LLVMlib.
Export LLVMtd.

Definition GenericValue := list (val*memory_chunk).
Definition GVMap := list (id*GenericValue).

Definition mblock := Values.block.
Definition mptr := GenericValue.
Definition null : GenericValue := (Vptr Mem.nullptr (Int.repr 31 0), Mint 31)::nil.

Fixpoint sizeGenericValue (gv:GenericValue) : nat := 
match gv with
| nil => O
| (_, c)::gv' => size_chunk_nat c + sizeGenericValue gv'
end.

Definition uninits (n:nat) : GenericValue := (Vundef, Mint (n*8-1))::nil.
Definition GV2val (TD:TargetData) (gv:GenericValue) : option val :=
match gv with
| (v,c)::nil => Some v
| _ => None
end.
Definition GV2int (TD:TargetData) (bsz:sz) (gv:GenericValue) : option Z :=
match gv with
| (Vint wz i,c)::nil => 
  if eq_nat_dec (wz+1) (Size.to_nat bsz)
  then Some (Int.unsigned wz i)
  else None
| _ => None
end.
Definition GV2ptr (TD:TargetData) (bsz:sz) (gv:GenericValue) : option val :=
match gv with
| (Vptr a b,c)::nil => Some (Vptr a b)
| _ => None
end.
Fixpoint isGVUndef (gv:GenericValue) : Prop :=
match gv with
| nil => False
| (Vundef,_)::gv' => True
| _::gv' => isGVUndef gv'
end.
Definition val2GV (TD:TargetData) (v:val) (c:memory_chunk) : GenericValue :=
(v,c)::nil.
Definition ptr2GV (TD:TargetData) (ptr:val) : GenericValue :=
val2GV TD ptr (Mint (getPointerSize TD-1)).
Definition blk2GV (TD:TargetData) (b:mblock) : GenericValue :=
ptr2GV TD (Vptr b (Int.repr 31 0)).
Definition isGVZero (TD:TargetData) (gv:GenericValue) : bool :=
match (GV2int TD Size.One gv) with
| Some z => if Coqlib.zeq z 0 then true else false
| _ => false
end.
Definition mgetoffset (TD:TargetData) (t:typ) (idx:list Z) : option int32 := None.
Definition mget (TD:TargetData) (v:GenericValue) (o:int32) (t:typ) : option GenericValue := None.
Definition mset (TD:TargetData) (v:GenericValue) (o:int32) (t0:typ) (v0:GenericValue) : option GenericValue := None.
Definition mgep (TD:TargetData) (t:typ) (ma:val) (idxs:list Z) : option val := None.

(**************************************)
(** Convert const to GV with storesize, and look up GV from operands. *)

Fixpoint _const2GV (TD:TargetData) (gl:GVMap) (c:const) : option (GenericValue*typ) := 
match c with
| const_int sz n => 
         let wz := (Size.to_nat sz) - 1 in
         Some (val2GV TD (Vint wz (Int.repr wz (INTEGER.to_Z n))) (Mint wz), typ_int sz)
| const_undef t =>  
         match (getTypeSizeInBits TD t) with
         | Some wz => Some (val2GV TD Vundef (Mint (wz-1)), t)
         | None => None
         end
| const_null t => Some (val2GV TD (Vptr Mem.nullptr (Int.repr 31 0)) (Mint 31), t)
| const_arr lc => _list_const_arr2GV TD gl lc
| const_struct lc =>
         match (_list_const_struct2GV TD gl lc) with
         | None => None
         | Some ((gv, t), al) => 
           match (sizeGenericValue gv) with
           | 0 => Some (uninits (Align.to_nat al), t)
           | _ => Some (gv++uninits (Align.to_nat al-sizeGenericValue gv), t)
           end
         end
| const_gid t id =>
         match (lookupAL _ gl id) with
         | Some gv => Some (gv, t)
         | None => None
         end
end
with _list_const_arr2GV (TD:TargetData) (gl:GVMap) (cs:list_const) : option (GenericValue*typ) := 
match cs with
| Nil_list_const => Some (nil, typ_int Size.Zero)
| Cons_list_const c lc' =>
  match (_list_const_arr2GV TD gl lc', _const2GV TD gl c) with
  | (Some (gv, t), Some (gv0,t0)) =>
             match (getTypeAllocSize TD t0) with
             | Some sz0 => Some ((gv++gv0)++uninits (sz0 - sizeGenericValue gv0), t0)
             | None => None 
             end
  | _ => None
  end
end
with _list_const_struct2GV (TD:TargetData) (gl:GVMap) (cs:list_const) : option (GenericValue*typ*align) := 
match cs with
| Nil_list_const => Some ((nil, typ_int Size.Zero), Align.Zero)
| Cons_list_const c lc' =>
  match (_list_const_struct2GV TD gl lc', _const2GV TD gl c) with
  | (Some (gv, t, struct_al), Some (gv0,t0)) =>
             match (getABITypeAlignment TD t0, getTypeAllocSize TD t0) with
             | (Some sub_al, Some sub_sz) => 
               match (le_lt_dec sub_al (Align.to_nat struct_al)) with
               | left _ (* struct_al <= sub_al *) =>
                 Some (
                  (gv++
                  (uninits (sub_al - sizeGenericValue gv0))++
                  gv0++
                  (uninits (sub_sz - sizeGenericValue gv0)),
                  t0),
                  (Align.from_nat sub_al)
                 )
               | right _ (* sub_al < struct_al *) =>
                 Some (
                  (gv++
                  (uninits (sub_al - sizeGenericValue gv0))++
                  gv0++
                  (uninits (sub_sz - sizeGenericValue gv0)),
                  t0),
                  struct_al
                 )
               end
             | _ => None 
             end
  | _ => None
  end
end
.

Definition const2GV (TD:TargetData) (gl:GVMap) (c:const) : option GenericValue :=
match (_const2GV TD gl c) with
| None => None
| Some (gv, t) => Some gv
end.

Definition getOperandValue (TD:TargetData) (v:value) (locals:GVMap) (globals:GVMap) : option GenericValue := 
match v with
| value_id id => lookupAL _ locals id 
| value_const c => (const2GV TD globals c)
end.

Definition getOperandInt (TD:TargetData) (bsz:sz) (v:value) (locals:GVMap) (globals:GVMap) : option Z := 
match (getOperandValue TD v locals globals) with
| Some gi => GV2int TD bsz gi
| None => None
end.

Definition getOperandPtr (TD:TargetData) (v:value) (locals:GVMap) (globals:GVMap) : option val := 
match (getOperandValue TD v locals globals) with
| Some gi => GV2ptr TD (getPointerSize TD) gi
| None => None
end.

Definition getOperandPtrInBits (TD:TargetData) (s:sz) (v:value) (locals:GVMap) (globals:GVMap) : option val := 
match (getOperandValue TD v locals globals) with
| Some gi => GV2ptr TD s gi
| None => None
end.

Definition isOperandUndef (TD:TargetData) (t:typ) (v:value) (locals:GVMap) (globals:GVMap) : Prop  := 
match (getOperandValue TD v locals globals) with
| Some gi => isGVUndef gi
| None => False
end.

(**************************************)
(* conversion between different lists *)

Fixpoint params2OpGVs (TD:TargetData) (lp:params) (locals:GVMap) (globals:GVMap) : list (option GenericValue):=
match lp with
| nil => nil
| (_, v)::lp' => getOperandValue TD v locals globals::params2OpGVs TD lp' locals globals
end.

Fixpoint opGVs2GVs (lg:list (option GenericValue)) : list GenericValue :=
match lg with
| nil => nil
| (Some g)::lg' => g::opGVs2GVs lg'
| _::lg' => opGVs2GVs lg'
end.

Definition params2GVs (TD:TargetData) (lp:params) (locals:GVMap) (globals:GVMap) : list GenericValue  := 
  opGVs2GVs (params2OpGVs TD lp locals globals).

Fixpoint values2GVs (TD:TargetData) (lv:list_value) (locals:GVMap) (globals:GVMap) : option (list GenericValue):=
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

Fixpoint intValues2Nats (TD:TargetData) (lv:list_value) (locals:GVMap) (globals:GVMap) : option (list Z):=
match lv with
| Nil_list_value => Some nil
| Cons_list_value v lv' => 
  match (getOperandValue TD v locals globals) with
  | Some GV => 
    match (GV2int TD Size.ThirtyTwo GV) with
    | Some z =>
        match (intValues2Nats TD lv' locals globals) with
        | Some ns => Some (z::ns)
        | None => None
        end
    | _ => None
    end
  | None => None
  end
end.

Fixpoint intConsts2Nats (TD:TargetData) (lv:list_const) : option (list Z):=
match lv with
| Nil_list_const => Some nil
| Cons_list_const (const_int sz0 n) lv' => 
  if Size.dec sz0 Size.ThirtyTwo 
  then
    match (intConsts2Nats TD lv') with
    | Some ns => Some ((INTEGER.to_Z n)::ns)
    | None => None
    end
  else None
| _ => None
end.

Fixpoint GVs2Nats (TD:TargetData) (lgv:list GenericValue) : option (list Z):=
match lgv with
| nil => Some nil
| gv::lgv' => 
    match (GV2int TD Size.ThirtyTwo gv) with
    | Some z =>
        match (GVs2Nats TD lgv') with
        | Some ns => Some (z::ns)
        | None => None
        end
    | _ => None
    end
end.

(**************************************)
(* helping functions *)

Fixpoint _initializeFrameValues (la:args) (lg:list GenericValue) (locals:GVMap) : GVMap :=
match (la, lg) with
| ((_, id)::la', g::lg') => updateAddAL _ (_initializeFrameValues la' lg' locals) id g
| _ => locals
end.

Definition initLocals (la:args) (lg:list GenericValue): GVMap := 
_initializeFrameValues la lg nil.

Definition getEntryBlock (fd:fdef) : option block :=
match fd with
| fdef_intro _ (b::_) => Some b
| _ => None
end.

Definition getEntryCmds (b:block) : cmds :=
match b with
| block_intro _ _ lc _ => lc
end.

(* FIXME : bounds check *)
Definition extractGenericValue (TD:TargetData)(t:typ) (gv : GenericValue) (cidxs : list_const) : option GenericValue :=
match (intConsts2Nats TD cidxs) with
| None => None 
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some o => mget TD gv o t
  | None => None
  end
end.

Definition insertGenericValue (TD:TargetData) (t:typ) (gv:GenericValue)
  (cidxs:list_const) (t0:typ) (gv0:GenericValue) : option GenericValue :=
match (intConsts2Nats TD cidxs) with
| None => None 
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some o => mset TD gv o t0 gv0
  | None => None
  end
end.

Definition GEP (TD:TargetData) (t:typ) (ma:GenericValue) (vidxs:list GenericValue) (inbounds:bool) : option GenericValue :=
match GV2ptr TD (getPointerSize TD) ma with
| Some ptr =>
  match GVs2Nats TD vidxs with
  | None => None 
  | Some idxs => 
    match (mgep TD t ptr idxs) with
    | Some ptr0 => Some (ptr2GV TD ptr0)
    | None => None
    end
  end
| None => None
end.

Definition mbop (TD:TargetData) (op:bop) (bsz:sz) (gv1 gv2:GenericValue) : option GenericValue :=
match (GV2val TD gv1, GV2val TD gv2) with
| (Some (Vint wz1 i1), Some (Vint wz2 i2)) => 
  let bsz' := (Size.to_nat bsz) in 
  if eq_nat_dec (wz1+1) bsz'
  then
     match op with
     | bop_add => Some (val2GV TD (Val.add (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_lshr => Some (val2GV TD (Val.shr (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_and => Some (val2GV TD (Val.and (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_or => Some (val2GV TD (Val.or (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     end
  else None
| _ => None
end.

Definition BOP (TD:TargetData) (lc gl:GVMap) (op:bop) (bsz:sz) (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => mbop TD op bsz gv1 gv2
| _ => None
end
.

Definition mcast (TD:TargetData) (op:castop) (t1:typ) (gv1:GenericValue) (t2:typ) : option GenericValue :=
match op with
| castop_inttoptr => 
  match (t1, t2) with
  | (typ_int sz1, typ_pointer _) => Some gv1
  | _ => None
  end
| castop_ptrtoint =>
  match (t1, t2) with
  | (typ_pointer _, typ_int sz2) => Some gv1
  | _ => None
  end
| castop_bitcase =>
  match (t1, t2) with
  | (typ_int sz1, typ_int sz2) => Some gv1
  | _ => None
  end
end.

Definition CAST (TD:TargetData) (lc gl:GVMap) (op:castop) (t1:typ) (v1:value) (t2:typ) : option GenericValue:=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mcast TD op t1 gv1 t2
| _ => None
end
.

Definition mext (TD:TargetData) (op:extop) (t1:typ) (gv1:GenericValue) (t2:typ) : option GenericValue :=
match (t1, t2) with
| (typ_int sz1, typ_int sz2) => 
   match (GV2val TD gv1) with
   | Some (Vint wz1 i1) =>
     match op with
     | extop_z => Some (val2GV TD (Val.zero_ext (Size.to_Z sz2) (Vint wz1 i1)) (Mint (Size.to_nat sz2-1)))
     | extop_s => Some (val2GV TD (Val.sign_ext (Size.to_Z sz2) (Vint wz1 i1)) (Mint (Size.to_nat sz2-1)))
     end
   | _ => None
   end
| (_, _) => None
end.

Definition EXT (TD:TargetData) (lc gl:GVMap) (op:extop) (t1:typ) (v1:value) (t2:typ) : option GenericValue :=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mext TD op t1 gv1 t2
| _ => None
end
.

Definition micmp (TD:TargetData) (c:cond) (t:typ) (gv1 gv2:GenericValue) : option GenericValue :=
match t with
| typ_int sz =>
  match (GV2val TD gv1, GV2val TD gv2) with
  | (Some (Vint wz1 i1), Some (Vint wz2 i2)) => 
     match c with
     | cond_eq => Some (val2GV TD (Val.cmp Ceq (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ne => Some (val2GV TD (Val.cmp Cne (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ugt => Some (val2GV TD (Val.cmpu Cgt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_uge => Some (val2GV TD (Val.cmpu Cge (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ult => Some (val2GV TD (Val.cmpu Clt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ule => Some (val2GV TD (Val.cmpu Clt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_sgt => Some (val2GV TD (Val.cmp Cgt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_sge => Some (val2GV TD (Val.cmp Cge (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_slt => Some (val2GV TD (Val.cmp Clt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_sle => Some (val2GV TD (Val.cmp Clt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     end
  | _ => None
  end  
| _ => None
end.

Definition ICMP (TD:TargetData) (lc gl:GVMap) (c:cond) (t:typ) (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => micmp TD c t gv1 gv2
| _ => None
end.

Lemma BOP_inversion : forall TD lc gl b s v1 v2 gv,
  BOP TD lc gl b s v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    mbop TD b s gv1 gv2 = Some gv.
Proof.
  intros TD lc gl b s v1 v2 gv HBOP.
  unfold BOP in HBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HBOP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HBOP].
      remember (mbop TD b s g g0) as R.
      destruct R; inversion HBOP; subst.
        exists g. exists g0. auto.
Qed.

Lemma getOperandPtr_inversion : forall TD lc gl v mptr,
  getOperandPtr TD v lc gl = Some mptr ->
  exists gv,
    getOperandValue TD v lc gl = Some gv /\
    GV2ptr TD (getPointerSize TD) gv = Some mptr.
Proof.
  intros TD lc gl v mptr HgetOperandPtr.
  unfold getOperandPtr in HgetOperandPtr.
  remember (getOperandValue TD v lc gl) as ogv.
  destruct ogv; try solve [inversion HgetOperandPtr].
    exists g. auto.
Qed.

Lemma getOperandInt_inversion : forall TD sz lc gl v n,
  getOperandInt TD sz v lc gl = Some n ->
  exists gv,
    getOperandValue TD v lc gl = Some gv /\
    GV2int TD sz gv = Some n.
Proof.
  intros TD sz0 lc gl v mptr HgetOperandInt.
  unfold getOperandInt in HgetOperandInt.
  remember (getOperandValue TD v lc gl) as ogv.
  destruct ogv; try solve [inversion HgetOperandInt].
    exists g. auto.
Qed.

Lemma CAST_inversion : forall TD lc gl op t1 v1 t2 gv,
  CAST TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mcast TD op t1 gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HCAST.
  unfold CAST in HCAST.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HCAST].
    remember (mcast TD op t1 g t2) as R.
    destruct R; inversion HCAST; subst.
      exists g. auto.
Qed.

Lemma EXT_inversion : forall TD lc gl op t1 v1 t2 gv,
  EXT TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mext TD op t1 gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HEXT.
  unfold EXT in HEXT.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HEXT].
    remember (mext TD op t1 g t2) as R.
    destruct R; inversion HEXT; subst.
      exists g. auto.
Qed.

Lemma ICMP_inversion : forall TD lc gl cond t v1 v2 gv,
  ICMP TD lc gl cond t v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    micmp TD cond t gv1 gv2 = Some gv.
Proof.
  intros TD lc gl cond0 t v1 v2 gv HICMP.
  unfold ICMP in HICMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HICMP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HICMP].
      remember (micmp TD cond0 t g g0) as R.
      destruct R; inversion HICMP; subst.
        exists g. exists g0. auto.
Qed.

Lemma GEP_inversion : forall (TD:TargetData) (t:typ) (ma:GenericValue) (vidxs:list GenericValue) ib mptr0,
  GEP TD t ma vidxs ib = Some mptr0 ->
  exists idxs, exists ptr, exists ptr0, 
    GVs2Nats TD vidxs = Some idxs /\ 
    GV2ptr TD (getPointerSize TD) ma = Some ptr /\
    mgep TD t ptr idxs = Some ptr0 /\
    ptr2GV TD ptr0 = mptr0.
Proof.
  intros.
  unfold GEP in H.
  remember (GVs2Nats TD vidxs) as oidxs.
  remember (GV2ptr TD (getPointerSize TD) ma) as R.
  destruct R; try solve [inversion H; subst].
    destruct oidxs; try solve [inversion H; subst].
Qed.

Lemma intValues2Nats_inversion : forall l0 lc gl TD ns0,
  intValues2Nats TD l0 lc gl = Some ns0 ->
  exists gvs0, 
    values2GVs TD l0 lc gl = Some gvs0 /\
    GVs2Nats TD gvs0 = Some ns0.
Proof.
  induction l0; intros; simpl in *.
    inversion H. exists nil. auto.

    remember (getOperandValue TD v lc gl) as ogv.
    destruct ogv; try solve [inversion H].
    remember (GV2int TD Size.ThirtyTwo g) as on.
    destruct on; try solve [inversion H].
    remember (intValues2Nats TD l0 lc gl) as ons.
    destruct ons; inversion H; subst.
    symmetry in Heqons.
    apply IHl0 in Heqons.
    destruct Heqons as [gvs [J1 J2]].
    exists (g::gvs).
    rewrite J1. 
    split; auto.
      simpl. rewrite J2. rewrite <- Heqon. auto.
Qed.

Lemma values2GVs_GVs2Nats__intValues2Nats : forall l0 lc gl TD gvs0,
  values2GVs TD l0 lc gl = Some gvs0 ->
  GVs2Nats TD gvs0 = intValues2Nats TD l0 lc gl.
Proof.
  induction l0; intros lc gl TD gvs0 H; simpl in *.
    inversion H. auto.

    destruct (getOperandValue TD v lc gl); try solve [inversion H].
      remember (values2GVs TD l0 lc gl)as ogv.
      destruct ogv; inversion H; subst.
        rewrite <- IHl0 with (gvs0:=l1); auto.
Qed.

Scheme const_ind2 := Induction for const Sort Prop
  with list_const_ind2 := Induction for list_const Sort Prop.
Combined Scheme const_mutind from const_ind2, list_const_ind2.

Lemma _const2GV_eqAL : 
  (forall c gl1 gl2 TD, eqAL _ gl1 gl2 -> 
    _const2GV TD gl1 c = _const2GV TD gl2 c) /\
  (forall cs gl1 gl2 TD, eqAL _ gl1 gl2 -> 
    _list_const_arr2GV TD gl1 cs = _list_const_arr2GV TD gl2 cs /\
    _list_const_struct2GV TD gl1 cs = _list_const_struct2GV TD gl2 cs).
Proof.
  apply const_mutind; intros; simpl; auto.
    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0.
    destruct H0; auto.

    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0.
    destruct H0.
    rewrite H1. auto.

    rewrite H. auto.

    assert (J:=H1).
    apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1.
    destruct H1.
    rewrite H2. rewrite H1. erewrite H; eauto.
Qed.

Lemma const2GV_eqAL : forall c gl1 gl2 TD, 
  eqAL _ gl1 gl2 -> 
  const2GV TD gl1 c = const2GV TD gl2 c.
Proof.
  intros. unfold const2GV.
  destruct _const2GV_eqAL.
  erewrite H0; eauto.
Qed.

Lemma getOperandValue_eqAL : forall lc1 gl lc2 v TD,
  eqAL _ lc1 lc2 ->
  getOperandValue TD v lc1 gl = getOperandValue TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD HeqAL.
  unfold getOperandValue in *.
  destruct v; auto.
Qed.

Lemma BOP_eqAL : forall lc1 gl lc2 bop0 sz0 v1 v2 TD,
  eqAL _ lc1 lc2 ->
  BOP TD lc1 gl bop0 sz0 v1 v2 = BOP TD lc2 gl bop0 sz0 v1 v2.
Proof.
  intros lc1 gl lc2 bop0 sz0 v1 v2 TD HeqEnv.
  unfold BOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma getOperandPtr_eqAL : forall lc1 gl lc2 v TD,
  eqAL _ lc1 lc2 ->
  getOperandPtr TD v lc1 gl = getOperandPtr TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD HeqEnv.
  unfold getOperandPtr in *.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma getOperandInt_eqAL : forall lc1 gl lc2 sz v TD,
  eqAL _ lc1 lc2 ->
  getOperandInt TD sz v lc1 gl = getOperandInt TD sz v lc2 gl.
Proof.
  intros lc1 gl lc2 sz0 v TD HeqAL.
  unfold getOperandInt in *.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma getOperandPtrInBits_eqAL : forall lc1 gl lc2 sz v TD,
  eqAL _ lc1 lc2 ->
  getOperandPtrInBits TD sz v lc1 gl = getOperandPtrInBits TD sz v lc2 gl.
Proof.
  intros lc1 gl lc2 sz0 v TD HeqAL.
  unfold getOperandPtrInBits in *.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma CAST_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  CAST TD lc1 gl op t1 v1 t2 = CAST TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold CAST in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.


Lemma EXT_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  EXT TD lc1 gl op t1 v1 t2 = EXT TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold EXT in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma ICMP_eqAL : forall lc1 gl lc2 cond t v1 v2 TD,
  eqAL _ lc1 lc2 ->
  ICMP TD lc1 gl cond t v1 v2 = ICMP TD lc2 gl cond t v1 v2.
Proof.
  intros lc1 gl lc2 cond0 t v1 v2 TD HeqAL.
  unfold ICMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma intValues2Nats_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  intValues2Nats TD l0 lc1 gl = intValues2Nats TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD HeqAL; simpl; auto.
    rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v); auto.
    erewrite IHl0; eauto.
Qed.

Lemma values2GVs_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  values2GVs TD l0 lc1 gl = values2GVs TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD HeqAL; simpl; auto.
    rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v); auto.
    erewrite IHl0; eauto.
Qed.

(*
Lemma GEP_eqAL : forall lc1 gl lc2 t ma vidxs ib TD,
  eqAL _ lc1 lc2 ->
  GEP TD lc1 gl t ma vidxs ib = GEP TD lc2 gl t ma vidxs ib.
Proof.
  intros lc1 gl lc2 t ma vidxs ib TD HeqAL.
  unfold GEP in *. auto.
  erewrite intValues2Nats_eqAL; eauto. 
Qed.
*)

End LLVMgv.

