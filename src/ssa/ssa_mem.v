Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Import tactics.
Require Export Coq.Program.Equality.
Require Export CoqListFacts.
Require Export targetdata.

(** Memory is separated as blocks indexed by [mblock], contents in each block
    are indexed by [moffset]. Addresses are encoded as pairs [mblock] and [moffset].
    We take 0 block with 0 offset as null.
*)
Definition mblock := nat.
Definition moffset := nat.
Definition maddr := (mblock * moffset)%type.

Definition null := (0, 0) : maddr.
Definition uninitptr := maddr.

Inductive mdata : Set :=
| mdata_byte : nat -> mdata   (* We only need 8 bits. *) 
| mdata_uninit  : mdata  
| mdata_ptr : maddr -> mdata
.

Definition mvalue := list mdata.

Definition mem := mblock -> option mvalue.

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

Variable mload : layouts -> mem -> maddr -> typ -> option mvalue.

Variable mstore : layouts -> mem -> maddr -> typ -> mvalue -> option mem.

(** translating list of bytes to nat w.r.t typ *)
Variable mvalue2nat : layouts -> sz -> mvalue -> option nat.

(** translating nat to mvalue with StoreSize*)
Variable nat2mvalue : layouts -> sz -> nat -> mvalue.

(** checking if list of bytes or uninit is undef, should all elements in list be uninits? *)
Variable isMvalueUndef : list layout -> typ -> mvalue -> Prop.

(** translating undef to mvalue with StoreSize*)
Variable undef2mvalue : list layout -> typ -> mvalue.

(** compute offset in typ with list of idxs, typ and its subtypes cannot be ptr, and
    out-of-bounds is disallowed. *)
Variable mgetoffset : layouts -> typ -> list nat -> bool -> option moffset.

(** FIXME: we should also check if sz out-of-bounds. *)
Definition mgep (TD:layouts) (t:typ) (ma:maddr) (idxs:list nat) (inbounds:bool) : option maddr :=
match ma with
| (mb, mo) => 
  match idxs with
  | nil => None
  | (idx::idxs') =>
    match (getTypeAllocSize TD t, mgetoffset TD t idxs' inbounds) with
    | (Some sz, Some offset) => Some (mb, mo+sz*idx+offset)
    | _ => None
    end
  end
end.

