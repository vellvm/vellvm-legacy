Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
(* Add LoadPath "../../../theory/metatheory". *)

Require Import ssa_dynamic.
Require Import trace.
Require Import Metatheory.
Require Import assoclist.
Require Import monad.
Require Import genericvalues.
Require Import ssa_mem.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Floats.
Require Import Coqlib.
Require Import ssa.
Require Import ssa_interpreter.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => "option"  [ "Some" "None" ].

Extract Constant AtomImpl.atom => "String.t".
Extract Constant AtomImpl.eq_atom_dec => "fun a b -> a == b".
Extract Constant AtomImpl.atom_fresh_for_list => "Llvmcaml.atom_fresh_for_list".

Extract Constant LLVMsyntax.id => "String.t".
Extract Constant LLVMsyntax.l => "String.t".
Extract Constant LLVMsyntax.inbounds => "bool".
Extract Constant LLVMsyntax.tailc => "bool".
Extract Constant LLVMsyntax.noret => "bool".

Extract Constant LLVMsyntax.Size.t => "int32".
Extract Constant LLVMsyntax.Size.Zero => "0l".
Extract Constant LLVMsyntax.Size.One => "1l".
Extract Constant LLVMsyntax.Size.Two => "2l".
Extract Constant LLVMsyntax.Size.Four => "4l".
Extract Constant LLVMsyntax.Size.Eight => "8l".
Extract Constant LLVMsyntax.Size.Sixteen => "16l".
Extract Constant LLVMsyntax.Size.ThirtyTwo => "32l".
Extract Constant LLVMsyntax.Size.SixtyFour => "64l".
Extract Constant LLVMsyntax.Size.from_nat => "fun x -> Int32.of_int (Camlcoq.camlint_of_nat x)".
Extract Constant LLVMsyntax.Size.to_nat => "Camlcoq.nat_of_camlint".
Extract Constant LLVMsyntax.Size.to_Z => "Camlcoq.z_of_camlint".
Extract Constant LLVMsyntax.Size.from_Z => "Camlcoq.camlint_of_z".
Extract Constant LLVMsyntax.Size.add => "Int32.add".
Extract Constant LLVMsyntax.Size.sub => "Int32.sub".
Extract Constant LLVMsyntax.Size.mul => "Int32.mul".
Extract Constant LLVMsyntax.Size.div => "Int32.div".
Extract Constant LLVMsyntax.Size.dec => "fun (x:int32) (y:int32) -> Int32.compare x y == 0".

Extract Constant LLVMsyntax.Align.t => "int32".
Extract Constant LLVMsyntax.Align.Zero => "0l".
Extract Constant LLVMsyntax.Align.One => "1l".
Extract Constant LLVMsyntax.Align.Two => "2l".
Extract Constant LLVMsyntax.Align.Four => "4l".
Extract Constant LLVMsyntax.Align.Eight => "8l".
Extract Constant LLVMsyntax.Align.Sixteen => "16l".
Extract Constant LLVMsyntax.Align.ThirtyTwo => "32l".
Extract Constant LLVMsyntax.Align.SixtyFour => "64l".
Extract Constant LLVMsyntax.Align.from_nat => "fun x -> Int32.of_int (Camlcoq.camlint_of_nat x)".
Extract Constant LLVMsyntax.Align.to_nat => "Camlcoq.nat_of_camlint".
Extract Constant LLVMsyntax.Align.to_Z => "Camlcoq.z_of_camlint".
Extract Constant LLVMsyntax.Align.from_Z => "Camlcoq.camlint_of_z".
Extract Constant LLVMsyntax.Align.add => "Int32.add".
Extract Constant LLVMsyntax.Align.sub => "Int32.sub".
Extract Constant LLVMsyntax.Align.mul => "Int32.mul".
Extract Constant LLVMsyntax.Align.div => "Int32.div".
Extract Constant LLVMsyntax.Align.dec => "fun (x:int32) (y:int32) -> Int32.compare x y == 0".

Extract Constant LLVMsyntax.INTEGER.t => "Llvm.llapint".
Extract Constant LLVMsyntax.INTEGER.to_nat => "Llvmcaml.llapint2nat".
Extract Constant LLVMsyntax.INTEGER.to_Z => "Llvmcaml.llapint2z".
Extract Constant LLVMsyntax.INTEGER.dec => "Llvm.APInt.compare".

Extract Constant LLVMlib.inbounds_dec => "(==)".
Extract Constant LLVMlib.tailc_dec => "(==)".
Extract Constant LLVMlib.noret_dec => "(==)".

(* Float *)
Extract Inlined Constant Floats.float => "float".
Extract Constant Floats.Float.zero   => "0.".
(* Extract Constant Floats.Float.one   => "1.". *)
Extract Constant Floats.Float.neg => "( ~-. )".
Extract Constant Floats.Float.abs => "abs_float".
Extract Constant Floats.Float.singleoffloat => "Floataux.singleoffloat".
Extract Constant Floats.Float.intoffloat => "Floataux.intoffloat".
Extract Constant Floats.Float.intuoffloat => "Floataux.intuoffloat".
Extract Constant Floats.Float.floatofint => "Floataux.floatofint".
Extract Constant Floats.Float.floatofintu => "Floataux.floatofintu".
Extract Constant Floats.Float.add => "( +. )".
Extract Constant Floats.Float.sub => "( -. )".
Extract Constant Floats.Float.mul => "( *. )".
Extract Constant Floats.Float.div => "( /. )".
Extract Constant Floats.Float.cmp => "Floataux.cmp".
Extract Constant Floats.Float.eq_dec => "fun (x: float) (y: float) -> x = y".

(* Memdata *)
Extract Constant Memdata.big_endian => "Memdataaux.big_endian".
Extract Constant Memdata.encode_float => "Memdataaux.encode_float".
Extract Constant Memdata.decode_float => "Memdataaux.decode_float".

(* Memory - work around an extraction bug. *)
Extraction NoInline Memory.Mem.valid_pointer.

Extraction Blacklist List String Int.

Cd "extraction".
Recursive Extraction Library ssa_interpreter.
Cd "../".

