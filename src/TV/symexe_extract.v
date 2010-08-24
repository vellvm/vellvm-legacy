Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory".
Require Import symexe_correct.
Require Import ssa.
Require Import Metatheory.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Constant AtomImpl.atom => "String.t".
Extract Constant AtomImpl.eq_atom_dec => "fun a b -> a == b".
Extract Constant AtomImpl.atom_fresh_for_list => "Symexe_aux.atom_fresh_for_list".

Extract Constant LLVMsyntax.id => "String.t".
Extract Constant LLVMsyntax.l => "String.t".
Extract Constant LLVMsyntax.INT => "Big_int.big_int".
Extract Constant LLVMsyntax.sz => "Big_int.big_int".
Extract Constant LLVMsyntax.align => "int".
Extract Constant LLVMsyntax.inbounds => "bool".
Extract Constant LLVMsyntax.tailc => "bool".
Extract Constant LLVMsyntax.noret => "bool".

Extract Constant LLVMsyntax.nth_list_typ => "Symexe_aux.nth_list_typ".

Extract Constant LLVMlib.getCmdTyp => "Symexe_aux.getCmdTyp".
Extract Constant LLVMlib.INT_dec => "(==)".
Extract Constant LLVMlib.sz_dec => "(==)".
Extract Constant LLVMlib.align_dec => "(==)".
Extract Constant LLVMlib.inbounds_dec => "(==)".
Extract Constant LLVMlib.tailc_dec => "(==)".
Extract Constant LLVMlib.noret_dec => "(==)".
Extract Constant LLVMlib.Constant.getTyp => "Symexe_aux.getTyp".
Extract Constant LLVMlib.GlobalValue.getTyp => "Symexe_aux.getTyp".
Extract Constant LLVMlib.Function.getTyp => "Symexe_aux.getTyp".
Extract Constant LLVMlib.Typ.getPrimitiveSizeInBits => "Symexe_aux.getPrimitiveSizeInBits".
Extract Constant LLVMlib.DerivedType.getPrimitiveSizeInBits => "Symexe_aux.getPrimitiveSizeInBits".
Extract Constant LLVMlib.FunctionType.getPrimitiveSizeInBits => "Symexe_aux.getPrimitiveSizeInBits".
Extract Constant LLVMlib.CompositeType.getPrimitiveSizeInBits => "Symexe_aux.getPrimitiveSizeInBits".
Extract Constant LLVMlib.SequentialType.getPrimitiveSizeInBits => "Symexe_aux.getPrimitiveSizeInBits".
Extract Constant LLVMlib.ArrayType.getPrimitiveSizeInBits => "Symexe_aux.getPrimitiveSizeInBits".
Extract Constant LLVMlib.ArrayType.getNumElements => "Symexe_aux.getNumElements".

Extraction Blacklist List String Int.

Extraction "symexe" tv_system.
