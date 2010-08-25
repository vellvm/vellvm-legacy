open Llvm

let string_of_icmp op =
	match op with
  | Icmp.Eq -> "eq"
  | Icmp.Ne -> "ne"
  | Icmp.Ugt -> "ugt"
  | Icmp.Uge -> "uge"
  | Icmp.Ult -> "ult"
  | Icmp.Ule -> "ule"
  | Icmp.Sgt -> "sgt"
  | Icmp.Sge -> "sge"
  | Icmp.Slt -> "slt"
  | Icmp.Sle -> "slt"

let string_of_fcmp op =
	match op with
  | Fcmp.False -> "false"
  | Fcmp.Oeq -> "oeq"
  | Fcmp.Ogt -> "ogt"
  | Fcmp.Oge -> "oge"
  | Fcmp.Olt -> "olt"
  | Fcmp.Ole -> "ole"
  | Fcmp.One -> "one"
  | Fcmp.Ord -> "ord"
  | Fcmp.Uno -> "uno"
  | Fcmp.Ueq -> "ueq"
  | Fcmp.Ugt -> "ugt"
  | Fcmp.Uge -> "uge"
  | Fcmp.Ult -> "ult"
  | Fcmp.Ule -> "ule"
  | Fcmp.Une -> "une"
  | Fcmp.True -> "true"

let is_instruction v =
	match (classify_value v) with
  | ValueTy.Ret -> true       
  | ValueTy.Br -> true 
  | ValueTy.Switch -> true 
  | ValueTy.Invoke -> true
  | ValueTy.Unwind -> true
  | ValueTy.Unreachable -> true
  | ValueTy.Add -> true
  | ValueTy.FAdd -> true 
  | ValueTy.Sub -> true
  | ValueTy.FSub -> true
  | ValueTy.Mul -> true
  | ValueTy.FMul -> true
  | ValueTy.UDiv -> true
  | ValueTy.SDiv -> true
  | ValueTy.FDiv -> true
  | ValueTy.URem -> true
  | ValueTy.SRem -> true
  | ValueTy.FRem -> true
  | ValueTy.Shl -> true
  | ValueTy.LShr -> true
  | ValueTy.AShr -> true
  | ValueTy.And -> true
  | ValueTy.Or -> true
  | ValueTy.Xor -> true
  | ValueTy.Malloc -> true
  | ValueTy.Free -> true
  | ValueTy.Alloca -> true
  | ValueTy.Load -> true
  | ValueTy.Store -> true
  | ValueTy.GetElementPtr -> true
  | ValueTy.Trunc -> true
  | ValueTy.ZExt -> true
  | ValueTy.SExt -> true
  | ValueTy.FPToUI -> true
  | ValueTy.FPToSI -> true
  | ValueTy.UIToFP -> true
  | ValueTy.SIToFP -> true
  | ValueTy.FPTrunc -> true
  | ValueTy.FPExt -> true
  | ValueTy.PtrToInt -> true
  | ValueTy.IntToPtr -> true
  | ValueTy.BitCast -> true
  | ValueTy.ICmp -> true
  | ValueTy.FCmp -> true
  | ValueTy.PHI -> true
  | ValueTy.Call -> true
  | ValueTy.Select -> true
  | ValueTy.UserOp1 -> true
  | ValueTy.UserOp2 -> true
  | ValueTy.VAArg -> true
  | ValueTy.ExtractElement -> true
  | ValueTy.InsertElement -> true
  | ValueTy.ShuffleVector -> true
  | ValueTy.ExtractValue -> true
  | ValueTy.InsertValue  -> true
	| _ -> false

let is_cast_instruction v =
	match (classify_value v) with
  | ValueTy.Trunc -> true
  | ValueTy.ZExt -> true
  | ValueTy.SExt -> true
  | ValueTy.FPToUI -> true
  | ValueTy.FPToSI -> true
  | ValueTy.UIToFP -> true
  | ValueTy.SIToFP -> true
  | ValueTy.FPTrunc -> true
  | ValueTy.FPExt -> true
  | ValueTy.PtrToInt -> true
  | ValueTy.IntToPtr -> true
  | ValueTy.BitCast -> true
	| _ -> false

let is_terminater v =
	match (classify_value v) with
  | ValueTy.Ret -> true       
  | ValueTy.Br -> true 
  | ValueTy.Switch -> true 
  | ValueTy.Invoke -> true
  | ValueTy.Unwind -> true
  | ValueTy.Unreachable -> true
	| _ -> false

let is_binary v =
	match (classify_value v) with
  | ValueTy.Add -> true
  | ValueTy.FAdd -> true 
  | ValueTy.Sub -> true
  | ValueTy.FSub -> true
  | ValueTy.Mul -> true
  | ValueTy.FMul -> true
  | ValueTy.UDiv -> true
  | ValueTy.SDiv -> true
  | ValueTy.FDiv -> true
  | ValueTy.URem -> true
  | ValueTy.SRem -> true
  | ValueTy.FRem -> true 
	| _ -> false

let is_unary_instuction v =
	match (classify_value v) with
  | ValueTy.Malloc -> true
  | ValueTy.Free -> true
  | ValueTy.Alloca -> true
  | ValueTy.Load -> true
  | ValueTy.Store -> true
  | ValueTy.Trunc -> true
  | ValueTy.ZExt -> true
  | ValueTy.SExt -> true
  | ValueTy.FPToUI -> true
  | ValueTy.FPToSI -> true
  | ValueTy.UIToFP -> true
  | ValueTy.SIToFP -> true
  | ValueTy.FPTrunc -> true
  | ValueTy.FPExt -> true
  | ValueTy.PtrToInt -> true
  | ValueTy.IntToPtr -> true
  | ValueTy.BitCast -> true
	| ValueTy.VAArg -> true
	| ValueTy.ExtractValue
	| _ -> false

let is_i1_type t =
	match (classify_type t) with
  | TypeKind.Integer -> integer_bitwidth t == 1
	| _ -> false 

let is_i8_type t =
	match (classify_type t) with
  | TypeKind.Integer -> integer_bitwidth t == 8
	| _ -> false 

let is_i16_type t =
	match (classify_type t) with
  | TypeKind.Integer -> integer_bitwidth t == 16
	| _ -> false 

let is_i32_type t =
	match (classify_type t) with
  | TypeKind.Integer -> integer_bitwidth t == 32
	| _ -> false 

let is_i64_type t =
	match (classify_type t) with
  | TypeKind.Integer -> integer_bitwidth t == 64
	| _ -> false 

let string_type_of v =
	string_of_lltype (type_of v)

let string_of_instr_opcode i = string_of_opcode (classify_instr i)

let concat2 sep arr =
  let s = ref "" in
  if 0 < Array.length arr then begin
    s := !s ^ arr.(0);
    for i = 1 to (Array.length arr) - 1 do
      s := !s ^ sep ^ arr.(i)
    done
  end;
  !s
	
let string_of_endian e =
	match e with
	| Llvm_target.Endian.Big -> "big"
	| Llvm_target.Endian.Little -> "little"

let string_of_aligntype at =
	match at with
	| Llvm_target.AlignType.Integer_align -> "i" 
	| Llvm_target.AlignType.Vector_align -> "v"
	| Llvm_target.AlignType.Float_align -> "f"
	| Llvm_target.AlignType.Aggregate_align -> "a"
	| Llvm_target.AlignType.Stack_align -> "s"
