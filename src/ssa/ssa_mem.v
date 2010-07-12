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

Inductive mdata : Set :=
| mdata_byte : nat -> mdata   (* We only need 8 bits. *) 
| mdata_unint  : mdata  
| mdata_ptr : maddr -> mdata
.

Definition mvalue := list mdata.

Definition mem := mblock -> option mvalue.

(** allocate memory with size and alignment *)
Variable malloc : list layout -> mem -> nat -> nat -> option (mem * mblock)%type.

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

Variable mload : list layout -> mem -> maddr -> typ -> option mvalue.

Variable mstore : list layout -> mem -> maddr -> typ -> mvalue -> option mem.

Variable mgep : list layout -> typ -> maddr -> list nat -> bool -> option maddr.

