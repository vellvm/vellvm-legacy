Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Import tactics.
Require Export Coq.Program.Equality.
Require Export CoqListFacts.
Require Export targetdata.
Require Import monad.
Require Import Arith.

(** memory address *)
Definition maddr := nat.

(** Memory is separated as blocks indexed by [mblock], contents in each block
    are indexed by [moffset]. Pointers [mptr] are encoded as pairs [mblock] and [moffset].
    [malloca] maps [mblock] to the end address of each allocated block if the block
    is allocated, [mblock] actually equals to the beginning address of this block.
    We assume that there is a [null] pointer.
*)
Definition mblock := maddr.
Definition malloca := mblock -> option maddr.
Definition moffset := nat.
Definition mptr := (mblock * moffset)%type.
Variable null : mptr.

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

(** allocate memory with size and alignment *)
Variable malloc : layouts -> mem -> nat -> nat -> option (mem * mblock)%type.

Variable free : mem -> mblock -> option mem.

Fixpoint free_allocas (Mem:mem) (allocas:list mblock) : option mem :=
match allocas with
| nil => Some Mem
| alloca::allocas' =>
  match (free Mem alloca) with
  | Some Mem' => free_allocas Mem' allocas'
  | None => None
  end
end.

Variable mload : layouts -> mem -> mptr -> typ -> option mvalue.

Variable mstore : layouts -> mem -> mptr -> typ -> mvalue -> option mem.

(** translating [mvalue] to value of specific typ, failed when [mvalue] is not
    of size [sz]. *)
Variable mvalue2nat : layouts -> sz -> mvalue -> option nat.
Variable mvalue2mptr : layouts -> sz -> mvalue -> option mptr.
(** checking if list of bytes or uninit is undef, should all elements in list be uninits? *)
Variable isMvalueUndef : list layout -> typ -> mvalue -> Prop.

(** translating value to [mvalue] with size [sz]. *)
Variable nat2mvalue : layouts -> nat -> sz -> mvalue.
Variable mptr2mvalue : layouts -> mptr -> sz -> mvalue.
(** translating undef to mvalue with StoreSize, failed when typ is not storable. *)
Variable undef2mvalue : list layout -> typ -> option mvalue.

(** addition of two [mvalue]'s with size [sz], could be none if
    overflow happens. *)
Variable mvalue_add : layouts -> sz -> mvalue -> mvalue -> option mvalue.

(** [sz] uninitialized [mvalue]. *)
Fixpoint muninits (sz:nat) : mvalue :=
match sz with
| 0 => nil
| S sz' => mbyte_uninit::muninits sz'
end.

(** compute offset in typ with list of idxs, typ and its subtypes cannot be ptr. *)
Variable mgetoffset : layouts -> typ -> list nat -> option moffset.

Definition mgep (TD:layouts) (t:typ) (ma:mptr) (idxs:list nat) : option mptr :=
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


