Require Import Ensembles.
Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Import Arith.
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
Require Import infrastructure_props.
Require Import typings.

Import LLVMsyntax.
Import LLVMtd.
Import LLVMinfra.
Import LLVMgv.
Import LLVMtypings.

(* FIXME: Because memory only stores concrete values, the semantics branches when
   storing data. However, at rule malloc/free/load/store/call/..., the rules also 
   branch. Thoses rules should do what bop/fop/trunc do by lifting det-rules to 
   non-det rules!!! *)

Axiom callExternalFunction : mem -> id -> list GenericValue -> 
  option ((option GenericValue)*mem).

Axiom callIntrinsics : mem -> intrinsic_id -> list GenericValue -> 
  option ((option GenericValue)*mem).

Definition callMalloc (TD:TargetData) (M:mem) (parameters: list GenericValue) 
  : option ((option GenericValue)*mem) :=
match parameters with
| gn::_ => 
    match malloc TD M Size.One gn Align.Four with
    | Some (M', mb) => Some (Some (blk2GV TD mb), M')
    | _ => None
    end
| _ => 
   (* We should prove that given a well-formed program, this case won't happen
      because malloc must have one parameters *)
   None
end.

Definition callFree (TD:TargetData) (M:mem) (parameters: list GenericValue) 
  : option ((option GenericValue)*mem) :=
match parameters with
| ptr::_ => 
    match free TD M ptr with
    | Some M' => Some (None, M')
    | _ => None
    end
| _ => 
   (* We should prove that given a well-formed program, this case won't happen
      because free must have one parameters *)
   None
end.

Definition callExternalOrIntrinsics (TD:TargetData) (M:mem) (fid:id) 
  (dck:deckind) (parameters: list GenericValue) 
  : option ((option GenericValue)*mem) :=
match dck with
| deckind_intrinsic iid => callIntrinsics M iid parameters
| deckind_external eid_malloc => callMalloc TD M parameters   
| deckind_external eid_free => callFree TD M parameters
| deckind_external eid_other => callExternalFunction M fid parameters
end.

