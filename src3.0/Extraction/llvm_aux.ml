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
  | ValueKind.Instruction _ -> true
  | _ -> false

let is_cast_opcode opcode =
  match opcode with
  | Opcode.Trunc -> true
  | Opcode.ZExt -> true
  | Opcode.SExt -> true
  | Opcode.FPToUI -> true
  | Opcode.FPToSI -> true
  | Opcode.UIToFP -> true
  | Opcode.SIToFP -> true
  | Opcode.FPTrunc -> true
  | Opcode.FPExt -> true
  | Opcode.PtrToInt -> true
  | Opcode.IntToPtr -> true
  | Opcode.BitCast -> true
  | _ -> false

let is_cast_instruction v =
  match (classify_value v) with
  | ValueKind.Instruction opcode -> is_cast_opcode opcode
  | _ -> false

let is_terminator_opcode opcode =
  match opcode with
  | Opcode.Ret -> true       
  | Opcode.Br -> true 
  | Opcode.Switch -> true 
  | Opcode.IndirectBr -> true 
  | Opcode.Invoke -> true
  | Opcode.Unwind -> true
  | Opcode.Resume -> true
  | Opcode.Unreachable -> true
  | _ -> false

let is_terminator v =
  match (classify_value v) with
  | ValueKind.Instruction opcode -> is_terminator_opcode opcode
  | _ -> false

let is_binary_opcode opcode =
  match opcode with
  | Opcode.Add -> true
  | Opcode.FAdd -> true 
  | Opcode.Sub -> true
  | Opcode.FSub -> true
  | Opcode.Mul -> true
  | Opcode.FMul -> true
  | Opcode.UDiv -> true
  | Opcode.SDiv -> true
  | Opcode.FDiv -> true
  | Opcode.URem -> true
  | Opcode.SRem -> true
  | Opcode.FRem -> true 
  | _ -> false

let is_binary v =
  match (classify_value v) with
  | ValueKind.Instruction opcode -> is_binary_opcode opcode
  | _ -> false

let is_unary_opcode opcode =
  match opcode with
  | Opcode.Alloca -> true
  | Opcode.Load -> true
  | Opcode.Store -> true
  | Opcode.Trunc -> true
  | Opcode.ZExt -> true
  | Opcode.SExt -> true
  | Opcode.FPToUI -> true
  | Opcode.FPToSI -> true
  | Opcode.UIToFP -> true
  | Opcode.SIToFP -> true
  | Opcode.FPTrunc -> true
  | Opcode.FPExt -> true
  | Opcode.PtrToInt -> true
  | Opcode.IntToPtr -> true
  | Opcode.BitCast -> true
  | Opcode.VAArg -> true
  | _ -> false

let is_unary_instuction v =
  match (classify_value v) with
  | ValueKind.Instruction opcode -> is_unary_opcode opcode
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

let concat2 sep arr =
  let s = ref "" in
  if 0 < Array.length arr then begin
    s := !s ^ arr.(0);
    for i = 1 to (Array.length arr) - 1 do
      s := !s ^ sep ^ arr.(i)
    done
  end;
  !s

let rec my_string_of_lltype m ty =
  match classify_type ty with
    TypeKind.Integer -> "i" ^ string_of_int (integer_bitwidth ty)
  | TypeKind.Pointer -> 
    (let ety = element_type ty in
    match classify_type ety with
    | TypeKind.Struct ->
        (match struct_name ety with
        | None -> (my_string_of_lltype m ety)
        | Some s -> s) ^ "*"
    | _ -> (string_of_lltype (element_type ty)) ^ "*")
  | TypeKind.Struct ->
    (match struct_name ty with
    | None ->
      let s = "{ " ^ (concat2 ", " (
                Array.map (my_string_of_lltype m) (struct_element_types ty)
              )) ^ " }" in
      if is_packed ty
        then "<" ^ s ^ ">"
        else s
    | Some s -> s)
  | TypeKind.Array -> "["   ^ (string_of_int (array_length ty)) ^
                      " x " ^ (my_string_of_lltype m (element_type ty)) ^ "]"
  | TypeKind.Vector -> "<"   ^ (string_of_int (vector_size ty)) ^
                       " x " ^ (my_string_of_lltype m (element_type ty)) ^ ">"
  | TypeKind.Function -> my_string_of_lltype m (return_type ty) ^
                         " (" ^ (concat2 ", " (
                           Array.map (my_string_of_lltype m) (param_types ty)
                         )) ^ ")"
  | TypeKind.Label -> "label"
  | TypeKind.Ppc_fp128 -> "ppc_fp128"
  | TypeKind.Fp128 -> "fp128"
  | TypeKind.X86fp80 -> "x86_fp80"
  | TypeKind.Double -> "double"
  | TypeKind.Float -> "float"
  | TypeKind.Void -> "void"
  | TypeKind.Metadata -> "metadata"  
	
let string_type_of m v =
  my_string_of_lltype m (type_of v)

let string_of_instr_opcode i = string_of_opcode (instr_opcode i)

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

let string_of_valuekd op =
  match op with
  | ValueKind.NullValue -> "NullValue"
  | ValueKind.Argument -> "Argument"
  | ValueKind.BasicBlock -> "BasicBlock"
  | ValueKind.InlineAsm -> "InlineAsm"
  | ValueKind.MDNode -> "MDNode"
  | ValueKind.MDString -> "MDString"
  | ValueKind.BlockAddress -> "BlockAddress"
  | ValueKind.ConstantAggregateZero -> "ConstantAggregateZero"
  | ValueKind.ConstantArray -> "ConstantArray"
  | ValueKind.ConstantExpr -> "ConstantExpr"
  | ValueKind.ConstantFP -> "ConstantFP"
  | ValueKind.ConstantInt -> "ConstantInt"
  | ValueKind.ConstantPointerNull -> "ConstantPointerNull"
  | ValueKind.ConstantStruct -> "ConstantStruct"
  | ValueKind.ConstantVector -> "ConstantVector"
  | ValueKind.Function -> "Function"
  | ValueKind.GlobalAlias -> "GlobalAlias"
  | ValueKind.GlobalVariable -> "GlobalVariable"
  | ValueKind.UndefValue -> "UndefValue"
  | ValueKind.Instruction opcode -> string_of_opcode opcode

let string_of_linkage lk =
match lk with
  | Linkage.External -> "external"
  | Linkage.Available_externally -> "available_externally"
  | Linkage.Link_once -> "linkonce"
  | Linkage.Link_once_odr -> "linkonce_odr"
  | Linkage.Weak -> "weak"
  | Linkage.Weak_odr -> "weak_odr"
  | Linkage.Appending -> "appending"
  | Linkage.Internal -> "internal"
  | Linkage.Private -> "private"
  | Linkage.Dllimport -> "dllimport"
  | Linkage.Dllexport -> "dllexport"
  | Linkage.External_weak -> "external_weak"
  | Linkage.Ghost -> "ghost"
  | Linkage.Common -> "common"
  | Linkage.Linker_private -> "linker_private"

let escaped_value_name (v:llvalue) : string =
   Llvm.escaped_value_name v



