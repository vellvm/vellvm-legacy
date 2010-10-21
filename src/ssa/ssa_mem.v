Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
(* Add LoadPath "../../../theory/metatheory". *)
Require Import ssa_def.
Require Import List.
Require Import tactics.
Require Export Coq.Program.Equality.
Require Export CoqListFacts.
Require Export targetdata.
Require Import monad.
Require Import Arith.
Require Import Memory.
Require Import Values.
Require Import ZArith.
Require Import Integers.
Require Import Coqlib.
Require Import genericvalues.
Require Import AST.

Module LLVMmem.

Export LLVMsyntax.
Export LLVMgv.
Export LLVMtd.

(** Memory is separated as blocks indexed by [mblock], contents in each block
    are indexed by [moffset]. Pointers [mptr] are encoded as pairs [mblock] and [moffset].
    [malloca] maps [mblock] to the end address of each allocated block if the block
    is allocated, [mblock] actually equals to the beginning address of this block.
    We assume that there is a [null] pointer.
*)

(** memory address *)
(*Definition maddr := nat.*)

(* Definition malloca := mblock -> option maddr. *)
Definition moffset := Int.int 31.

(*
(** Bytes stored at each [maddr] *)
Inductive mbyte : Set :=
| mbyte_var : nat -> mbyte   (* We only need 8 bits. *) 
| mbyte_uninit  : mbyte  
.

(** [mem] includes a mapping from [maddr] to [mbyte], and blocks 
    information. *)
Record mem : Set := mkMem {
  data   : maddr -> mbyte;
  allocas : malloca
}.

(** Values used by dynamic semantics *)
Definition mvalue := list mbyte.

(** Initially, every addr maps to uninitial byte, and no blocks are allocated. *)
Definition initmem := mkMem (fun _ => mbyte_uninit) (fun _ => None) : mem.
*)

Definition mem := Mem.mem.
(*Definition initmem : mem := Mem.empty.*)

(** allocate memory with size and alignment *)
Definition malloc (TD:TargetData) (M:mem) (bsz:sz) (al:align) : option (mem * mblock)%type :=
Some (Mem.alloc M 0 (Size.to_Z bsz)).

Definition free (TD:TargetData) (M:mem) (ptr:mptr) : option mem :=
match GV2ptr TD (getPointerSize TD) ptr with
| Some (Vptr b i) =>
  if zeq (Int.unsigned 31 i) 0 
  then
    match (Mem.bounds M b) with
    | (l, h) => Mem.free M b l h
    end
  else None
| _ => None
end.

Fixpoint free_allocas (TD:TargetData) (Mem:mem) (allocas:list mblock) : option mem :=
match allocas with
| nil => Some Mem
| alloca::allocas' =>
  match (free TD Mem (blk2GV TD alloca)) with
  | Some Mem' => free_allocas TD Mem' allocas'
  | None => None
  end
end.

Definition typ2memory_chunk (t:typ) : option memory_chunk :=
  match t with
  | typ_int bsz => Some (Mint (Size.to_nat bsz -1))
  | typ_float => Some Mfloat32
  | typ_double => Some Mfloat64
  | typ_pointer _ => Some (Mint 31)
  | _ => None
  end.

Definition mload (TD:TargetData) (M:mem) (ptr:mptr) (t:typ) (a:align) : option GenericValue :=
match GV2ptr TD (getPointerSize TD) ptr with
| Some (Vptr b ofs) =>
  match typ2memory_chunk t with
  | Some c => 
    match (Mem.load c M b (Int.unsigned 31 ofs)) with
    | Some v => Some (val2GV TD v c)
    | None => None
    end
  | _ => None
  end
| _ => None
end.

Definition mstore (TD:TargetData) (M:mem) (ptr:mptr) (t:typ) (gv:GenericValue) (a:align) : option mem :=
match GV2ptr TD (getPointerSize TD) ptr with
| Some (Vptr b ofs) =>
  match typ2memory_chunk t, GV2val TD gv with
  | Some c, Some v => Mem.store c M b (Int.unsigned 31 ofs) v
  | _, _ => None
  end
| _ => None
end.

(*
(** translating [mvalue] to value of specific typ, failed when [mvalue] is not
    of size [sz]. *)
Variable mvalue2nat : TargetData -> sz -> mvalue -> option nat.
Variable mvalue2mptr : TargetData -> sz -> mvalue -> option mptr.
(** checking if list of bytes or uninit is undef, should all elements in list be uninits? *)
Variable isMvalueUndef : list layout -> typ -> mvalue -> Prop.

(** translating value to [mvalue] with size [sz]. *)
Variable nat2mvalue : TargetData -> nat -> sz -> mvalue.
Variable mptr2mvalue : TargetData -> mptr -> sz -> mvalue.
(** translating undef to mvalue with StoreSize, failed when typ is not storable. *)
Variable undef2mvalue : list layout -> typ -> option mvalue.

(** addition of two [mvalue]'s with size [sz], could be none if
    overflow happens. *)
Variable mvalue_add : TargetData -> sz -> mvalue -> mvalue -> option mvalue.

(** [sz] uninitialized [mvalue]. *)
Fixpoint muninits (sz:nat) : mvalue :=
match sz with
| 0 => nil
| S sz' => mbyte_uninit::muninits sz'
end.

(** compute offset in typ with list of idxs, typ and its subtypes cannot be ptr. *)
Variable mgetoffset : TargetData -> typ -> list nat -> option moffset.

Definition mgep (TD:TargetData) (t:typ) (ma:mptr) (idxs:list nat) : option mptr :=
match ma with
| (mb, mo) => 
  match idxs with
  | nil => None
  | (idx::idxs') =>
    match (getTypeAllocSize TD t, mgetoffset TD t idxs') with
    | (Some sz, Some offset) => Some (mb, mo+sz*idx+offset)
    | _ => None
    end
  end
end.

Definition mget (TD:list layout) (v:mvalue) (o:moffset) (t:typ) : option mvalue :=
do s <- getTypeStoreSize TD t;
   ret firstn s (skipn o v).

Definition mset (TD:list layout) (v:mvalue) (o:moffset) (t0:typ) (v0:mvalue) : option mvalue :=
do s <- getTypeStoreSize TD t0;
   If (beq_nat s (length v0))
   then ret ((firstn s (skipn o v))++v0++(skipn o v))
   else None
   endif.
*)

End LLVMmem.

