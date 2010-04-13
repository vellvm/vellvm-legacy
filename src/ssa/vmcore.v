Require Import ssa_lib.
Require Import List.

(* Signature *)

Module Type SigValue.

 Parameter getNumOperands : insn -> nat.

End SigValue.

Module Type SigUser. 
 Include Type SigValue.

End SigUser.

Module Type SigConstant.
 Include Type SigValue.

End SigConstant.

Module Type SigGlobalValue.
 Include Type SigConstant.

End SigGlobalValue.

Module Type SigFunction.
 Include Type SigGlobalValue.

 Parameter getReturnType : fdef -> typ.
 
End SigFunction.

Module Type SigInstruction.
 Include Type SigUser.

End SigInstruction.

Module Type SigReturnInst.
 Include Type SigInstruction.

 Parameter hasReturnType : insn -> bool.
 Parameter getReturnType : insn -> option typ.

End SigReturnInst.

Module Type SigType.
End SigType.

Module Type SigDerivedType.
 Include Type SigType.
End SigDerivedType.

Module Type SigCompositeType.
 Include Type SigDerivedType.
End SigCompositeType.

Module Type SigSequentialType.
 Include Type SigCompositeType.

 Parameter hasElementType : typ -> bool.
 Parameter getElementType : typ -> option typ.

End SigSequentialType.

Module Type SigArrayType.
 Include Type SigSequentialType.

 Parameter getNumElements : typ -> nat.

End SigArrayType.

(* Instantiation *)

Module Value <: SigValue.

 Definition getNumOperands (i:insn) : nat := 
   length (getInsnOperandsC i).  

End Value.

Module User <: SigUser. Include Value.

End User.

Module Constant <: SigConstant.
 Include Value.

End Constant.

Module GlobalValue <: SigGlobalValue.
 Include Constant.

End GlobalValue.

Module Function <: SigFunction.
 Include GlobalValue.

 Definition getReturnType (fd:fdef) : typ :=
 match fd with
 | fdef_intro (fheader_intro t _ _) _ => t
 end.

End Function.

Module Instruction <: SigInstruction.
 Include User.

End Instruction.

Module ReturnInst <: SigReturnInst.
 Include Instruction.

 Definition hasReturnType (i:insn) : bool :=
 match i with
 | insn_return t v => true
 | _ => false
 end.

 Definition getReturnType (i:insn) : option typ :=
 match i with
 | insn_return t v => Some t
 | _ => None
 end.

End ReturnInst.

Module Typ <: SigType.
End Typ.

Module DerivedType <: SigDerivedType.
 Include Typ.
End DerivedType.

Module CompositeType <: SigCompositeType.
 Include DerivedType.
End CompositeType.

Module SequentialType <: SigSequentialType.
 Include CompositeType.

 Definition hasElementType (t:typ) : bool :=
 match t with
 | typ_array _ t' => true
 | _ => false
 end.

 Definition getElementType (t:typ) : option typ :=
 match t with
 | typ_array _ t' => Some t'
 | _ => None
 end.

End SequentialType.

Module ArrayType <: SigArrayType.
 Include SequentialType.

 Definition getNumElements (t:typ) : nat :=
 match t with
 | typ_array N _ => N
 | _ => 0
 end.

End ArrayType.
