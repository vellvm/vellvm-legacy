Require Import ssa_lib.
Require Import List.

(* Instruction Signature *)

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

 Parameter getDefReturnType : fdef -> typ.
 Parameter getDefFunctionType : fdef -> typ.
 Parameter def_arg_size : fdef -> nat.
 
 Parameter getDecReturnType : fdec -> typ.
 Parameter getDecFunctionType : fdec -> typ.
 Parameter dec_arg_size : fdec -> nat.

End SigFunction.

Module Type SigInstruction.
 Include Type SigUser.

 Parameter isInvokeInst : insn -> bool.
 Parameter isCallInst : insn -> bool.

End SigInstruction.

Module Type SigReturnInst.
 Include Type SigInstruction.

 Parameter hasReturnType : insn -> bool.
 Parameter getReturnType : insn -> option typ.

End SigReturnInst.

Module Type SigCallSite.
 Parameter getCalledFunction : insn -> system -> option fdef.
 Parameter getFdefTyp : fdef -> typ.
 Parameter arg_size : fdef -> nat.
 Parameter getArgument : fdef -> nat -> option arg.
 Parameter getArgumentType : fdef -> nat -> option typ.

End SigCallSite.

Module Type SigCallInst.
 Include Type SigInstruction.

End SigCallInst.

Module Type SigInvokeInst.
 Include Type SigInstruction.

 Parameter getNormalDest : system -> insn -> option block.

End SigInvokeInst.

Module Type SigBinaryOperator.
 Include Type SigInstruction.

 Parameter getFirstOperandType : system -> insn -> option typ.
 Parameter getSecondOperandType : system -> insn -> option typ.
 Parameter getResultType : insn -> option typ.

End SigBinaryOperator.

Module Type SigPHINode.
 Include Type SigInstruction.

 Parameter getNumIncomingValues : insn -> option nat.
 Parameter getIncomingValueType : system  -> insn -> i -> option typ.
End SigPHINode.

(* Type Signature *)

Module Type SigType.
 Parameter isIntOrIntVector : typ -> bool.
 Parameter isInteger : typ -> bool.
End SigType.

Module Type SigDerivedType.
 Include Type SigType.
End SigDerivedType.

Module Type SigFunctionType.
 Include Type SigDerivedType.

 Parameter getNumParams : typ -> option nat.
 Parameter isVarArg : typ -> bool.
 Parameter getParamType : typ -> nat -> option typ.
End SigFunctionType.

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

(* Instruction Instantiation *)

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

 Definition getDefReturnType (fd:fdef) : typ :=
 match fd with
 | fdef_intro (fheader_intro t _ _) _ => t
 end.

 Definition getDefFunctionType (fd:fdef) : typ := getFdefTypC fd.

 Definition def_arg_size (fd:fdef) : nat :=
 match fd with
 | (fdef_intro (fheader_intro _ _ la) _) => length la
 end.

 Definition getDecReturnType (fd:fdec) : typ :=
 match fd with
 | fdec_intro (fheader_intro t _ _) => t
 end.

 Definition getDecFunctionType (fd:fdec) : typ := getFdecTypC fd.

 Definition dec_arg_size (fd:fdec) : nat :=
 match fd with
 | (fdec_intro (fheader_intro _ _ la)) => length la
 end.

End Function.

Module Instruction <: SigInstruction.
 Include User.

 Definition isInvokeInst (i:insn) : bool := isInvokeInsnB i.
 Definition isCallInst (i:insn) : bool := isCallInsnB i.

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

Module CallSite <: SigCallSite.

 Definition getCalledFunction (i:insn) (s:system) : option fdef :=
 match i with 
 | insn_invoke _ _ fid _ _ _ => lookupFdefViaIDFromSystemC s fid
 | insn_call _ _ fid _ => lookupFdefViaIDFromSystemC s fid
 | _ => None
 end.

 Definition getFdefTyp (fd:fdef) : typ := getFdefTypC fd.

 Definition arg_size (fd:fdef) : nat :=
 match fd with
 | (fdef_intro (fheader_intro _ _ la) _) => length la
 end.

 Definition getArgument (fd:fdef) (i:nat) : option arg :=
 match fd with
 | (fdef_intro (fheader_intro _ _ la) _) => 
    match (nth_error la i) with
    | Some a => Some a
    | None => None
    end
 end. 

 Definition getArgumentType (fd:fdef) (i:nat) : option typ :=
 match (getArgument fd i) with
 | Some (t, _) => Some t
 | None => None
 end.

End CallSite.

Module CallInst <: SigCallInst.
 Include Instruction.

End CallInst.

Module InvokeInst <: SigInvokeInst.
 Include Instruction.

 Definition getNormalDest (s:system) (i:insn) : option block :=
 match (getNormalDestFromInvokeInsnC i) with
 | None => None
 | Some l => lookupBlockViaLabelFromSystem s l
 end.

End InvokeInst.

Module BinaryOperator <: SigBinaryOperator.
 Include Instruction.

 Definition getFirstOperandType (s:system) (i:insn) : option typ := 
 match i with
 | insn_add _ _ v1 _ => 
   match v1 with
   | value_id id1 => lookupTypViaIDFromSystemC s id1
   | _ => Some (typ_int 0) (* FIXME: how to set the type of const*)
   end
 | _ => None
 end.

 Definition getSecondOperandType (s:system) (i:insn) : option typ := 
 match i with
 | insn_add _ _ _ v2 => 
   match v2 with
   | value_id id2 => lookupTypViaIDFromSystemC s id2
   | _ => Some (typ_int 0) (* FIXME: how to set the type of const*)
   end
 | _ => None
 end.

 Definition getResultType (i:insn) : option typ := getInsnTypC i.

End BinaryOperator.

Module PHINode <: SigPHINode.
 Include Instruction.

 Definition getNumIncomingValues (i:insn) : option nat :=
 match i with
 | (insn_phi _ _ ln) => Some (length ln)
 | _ => None
 end.

 Definition getIncomingValueType (s:system) (i:insn) (n:nat) : option typ :=
 match i with
 | (insn_phi _ _ ln) => 
    match (nth_error ln n) with
    | Some (id, _) => lookupTypViaIDFromSystemC s id
    | None => None
    end
 | _ => None
 end.

End PHINode.

(* Type Instantiation *)

Module Typ <: SigType.
 Definition isIntOrIntVector (t:typ) : bool :=
 match t with
 | typ_int _ => true
 | _ => false
 end.

 Definition isInteger (t:typ) : bool :=
 match t with
 | typ_int _ => true
 | _ => false
 end.

End Typ.

Module DerivedType <: SigDerivedType.
 Include Typ.
End DerivedType.

Module FunctionType <: SigFunctionType.
 Include DerivedType.

 Definition getNumParams (t:typ) : option nat :=
 match t with
 | (typ_function _ lt) => Some (length lt)
 | _ => None
 end.

 Definition isVarArg (t:typ) : bool := false.

 Definition getParamType (t:typ) (i:nat) : option typ :=
 match t with
 | (typ_function _ lt) => 
    match (nth_error lt i) with
    | Some t => Some t
    | None => None
    end
 | _ => None
 end.

End FunctionType.

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

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../") ***
*** End: ***
 *)
