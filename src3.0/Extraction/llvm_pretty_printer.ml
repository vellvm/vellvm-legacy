open Printf
open Llvm
open Llvm_aux

(** [PrintLLVMName], generate slots if [v] does not have a name. *)
let llvm_name st v =
  if (has_name v)
  then
    if (is_globalvalue v)
    then "@"^value_name v
    else "%"^value_name v
  else
  if (is_globalvalue v)
  then
    "@"^(string_of_int (SlotTracker.get_global_slot st v))
  else
    "%"^(string_of_int (SlotTracker.get_local_slot st v))

let llvm_label st b =
  let v = value_of_block b in
  if (has_name v)
  then
    value_name v
  else
    string_of_int (SlotTracker.get_local_slot st v)

(** [writeConstantInt] *)
let rec string_of_constant m st c = 
  match (classify_value c) with
  | ValueKind.UndefValue -> "undef"
  | ValueKind.ConstantExpr -> string_of_constant_expr m st c
  | ValueKind.ConstantAggregateZero -> "zeroinitializer"
  | ValueKind.ConstantInt ->
      if (is_i1_type (type_of c))
      then
        if (Int64.compare (const_int_get_zextvalue c) Int64.zero) == 0 
        then "false"
        else "true"
      else   
        APInt.to_string (APInt.const_int_get_value c)
  | ValueKind.ConstantFP -> APFloat.to_string (APFloat.const_float_get_value c)
  | ValueKind.ConstantArray -> 
      let ops = operands c in 
      Array.fold_right (fun c cs -> (string_of_constant m st c)^" "^cs) ops ""   
  | ValueKind.ConstantStruct ->
      let ops = operands c in 
      Array.fold_right (fun c cs -> (string_of_constant m st c)^" "^cs) ops ""   
  | ValueKind.ConstantVector -> "ConstantVector"
  | ValueKind.ConstantPointerNull -> "null"
  | ValueKind.GlobalVariable ->  llvm_name st c
  | ValueKind.Function ->  llvm_name st c
  | _ -> failwith (string_of_valuekd (classify_value c) ^ " isnt Constant")
and string_of_constant_expr m st c =
  match (constexpr_opcode c) with
  | Opcode.Ret ->
      failwith "Ret isnt a const expr"
  | Opcode.Br ->
      failwith "Br isnt a const expr"
  | Opcode.Switch ->
      failwith "Switch isnt a const expr"
  | Opcode.Invoke ->      
      failwith "Invoke isnt a const expr"
  | Opcode.Unwind ->
      failwith "Unwind isnt a const expr"
  | Opcode.Unreachable ->
      failwith "Unreachable isnt a const expr"
  | Opcode.Add ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const Add must have 2 operand."
      else
        "add ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.FAdd ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const FAdd must have 2 operand."
      else
        "fadd ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.Sub ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const Sub must have 2 operand."
      else
        "sub ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.FSub ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const FSub must have 2 operand."
      else
        "fsub ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.Mul ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const Mul must have 2 operand."
      else
        "mul ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.FMul ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const FMul must have 2 operand."
      else
        "fmul ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.UDiv ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const UDiv must have 2 operand."
      else
        "udiv ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.SDiv ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const SDiv must have 2 operand."
      else
        "sdiv ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.FDiv ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const FDiv must have 2 operand."
      else
        "fdiv ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.URem ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const URem must have 2 operand."
      else
        "urem ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.SRem ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const SRem must have 2 operand."
      else
        "srem ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.FRem ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const FRem must have 2 operand."
      else
        "frem ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.Shl ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const Shl must have 2 operand."
      else
        "shl ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.LShr ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const LShr must have 2 operand."
      else
        "lshr ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.AShr ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const AShr must have 2 operand."
      else
        "ashr ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.And ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const And must have 2 operand."
      else
        "and ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.Or ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const Or must have 2 operand."
      else
        "or ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.Xor ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const XOr must have 2 operand."
      else
        "xor ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.Alloca ->
      failwith "Alloca isnt a const expr"
  | Opcode.Load ->
      failwith "Load isnt a const expr"
  | Opcode.Store ->
      failwith "Store isnt a const expr"
  | Opcode.GetElementPtr ->        
      let n = num_operands c in
      if n < 1
      then failwith "Const GEP must have >=1 operand."
      else
        let ops = operands c in
         let n = num_operands c in
        let rec range b e ops =
          if b < e
          then
            (string_of_constant m st (Array.get ops b))^" "^(range (b + 1) e ops)
          else
            "" in
        "getelementptr ("^
        string_of_bool (Llvm.GetElementPtrInst.is_in_bounds c)^" "^
        string_of_constant m st (Array.get ops 0)^" "^
        range 1 n ops^")"
  | Opcode.Trunc ->        
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const Trunc must have 1 operand."
      else
        "trunc ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  | Opcode.ZExt ->        
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const ZExt must have 1 operand."
      else
        "zext ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  | Opcode.SExt ->        
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const SExt must have 1 operand."
      else
        "sext ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  Opcode.FPToUI ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const FPToUI must have 1 operand."
      else
        "fptoui ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  Opcode.FPToSI ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const FPToSI must have 1 operand."
      else
        "fptosi ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  Opcode.UIToFP ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const UIToFP must have 1 operand."
      else
        "uitofp ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  Opcode.SIToFP ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const SIToFP must have 1 operand."
      else
        "sitofp ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  Opcode.FPTrunc ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const FPTrunc must have 1 operand."
      else
        "fptrunc ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  Opcode.FPExt ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const FPExt must have 1 operand."
      else
        "fpext ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  Opcode.PtrToInt ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const PtrToInt must have 1 operand."
      else
        "ptrtoint ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  Opcode.IntToPtr ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const IntToPtr must have 1 operand."
      else
        "inttoptr ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  Opcode.BitCast ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const BitCast must have 1 operand."
      else
        "bitcast ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  | Opcode.ICmp ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const ICmp must have 2 operand."
      else
        "icmp ("^
        (string_of_icmp (ICmpInst.const_get_predicate c))^" "^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | Opcode.FCmp ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const FCmp must have 2 operand."
      else
        "fcmp ("^
        (string_of_fcmp (FCmpInst.const_get_predicate c))^" "^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  |  Opcode.PHI ->
      failwith "PHI isnt a const expr"
  | Opcode.Call ->
      failwith "Call isnt a const expr"
  | Opcode.Select ->      
      let ops = operands c in
      let n = num_operands c in
      if n != 3
      then failwith "Const Select must have 3 operand."
      else
        "select ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^" "^
        string_of_constant m st (Array.get ops 2)^")"
  | Opcode.UserOp1 ->      
      failwith "UserOp1 isnt a const expr"
  | Opcode.UserOp2 ->      
      failwith "UserOp2 isnt a const expr"
  | Opcode.VAArg ->      
      failwith "VAArg isnt a const expr"
  | Opcode.ExtractElement ->      
      failwith "Const ExtractElement: Not_Supported"
  | Opcode.InsertElement ->      
      failwith "Const InsertElement: Not_Supported"
  | Opcode.ShuffleVector ->      
      failwith "Sont ShuffleVector: Not_Supported"
  | Opcode.ExtractValue ->      
      let ops = operands c in
      let n = num_operands c in
      if n < 2
      then failwith "Const ExtractValue must have >=2 operand."
      else
        let rec range b e ops =
          if b < e
          then
            (string_of_constant m st (Array.get ops b))^" "^(range (b + 1) e ops)
          else
            "" in
        "extractvalue ("^
        string_of_constant m st (Array.get ops 0)^" "^
        (range 1 n ops)^")"
  | Opcode.InsertValue ->      
      let ops = operands c in
      let n = num_operands c in
      if n < 3
      then failwith "Const InsertValue must have >=3 operand."
      else
        let rec range b e ops =
          if b < e
          then
            (string_of_constant m st (Array.get ops b))^" "^(range (b + 1) e ops)
          else
            "" in
        "insertvalue ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^" "^
        (range 2 n ops)^")"
  | Opcode.LandingPad | Opcode.Resume | Opcode.AtomicRMW | Opcode.AtomicCmpXchg
  | Opcode.Fence | Opcode.Invalid2 | Opcode.IndirectBr | Opcode.Invalid -> 
      failwith "LandingPad|Resume|AtomicRMW|AtomicCmpXchg|Fence|Invalid2|IndirectBr|Invalid : Not_Supported"

(** See [WriteAsOperandInternal] - used by [string_of_operand], it prints out
    the name of [v] without its type. *)
let string_of_operand_internal m st v =
  match (classify_value v) with
  | ValueKind.Argument -> llvm_name st v
  | ValueKind.BasicBlock -> llvm_name st v
  | ValueKind.Function -> llvm_name st v                  (*GlobalValue*)
  | ValueKind.GlobalAlias -> llvm_name st v               (*GlobalValue*)
  | ValueKind.GlobalVariable -> llvm_name st v            (*GlobalValue*)
  | ValueKind.UndefValue -> string_of_constant m st v
  | ValueKind.ConstantExpr -> string_of_constant m st v
  | ValueKind.ConstantAggregateZero -> string_of_constant m st v
  | ValueKind.ConstantInt -> string_of_constant m st v
  | ValueKind.ConstantFP -> string_of_constant m st v
  | ValueKind.ConstantArray -> string_of_constant m st v
  | ValueKind.ConstantStruct -> string_of_constant m st v
  | ValueKind.ConstantVector -> string_of_constant m st v
  | ValueKind.ConstantPointerNull -> string_of_constant m st v
  | ValueKind.NullValue -> "NullValue"
  | ValueKind.MDNode -> "MDNode"
  | ValueKind.MDString -> "MDString"
  | ValueKind.InlineAsm -> "InlineAsm"
  | ValueKind.BlockAddress -> "BlockAddress"
  | _ -> llvm_name st v                                    (*Instruction*)

(** See [WriteAsOperand] - Write the name of the specified value out to the 
    specified ostream.  This can be useful when you just want to print int 
    %reg126, not the whole instruction that generated it. *)
(* optional argument must be followed by at least one non-optional argument,*)
(* at this case, ?(btype = true) cannot be at the end of this argument list. *)  
let string_of_operand ?(btype = true) m st v =
  let s =  string_of_operand_internal m st v in
  if btype
  then (string_type_of m v)^" "^s
  else s

let string_of_operands m st i =
  let ops = operands i in
  let n = num_operands i in
  let rec range b e ops =
    if b + 1 < e 
    then
      (string_of_operand m st (Array.get ops b))^", "^(range (b+1) e ops) 
    else
      (string_of_operand m st (Array.get ops b)) in
  if n == 0 
  then 
    ""
  else
    range 0 n ops

let travel_other_instr m st i =
  eprintf "  %s = %s %s\n" (llvm_name st i) (string_of_instr_opcode i) 
    (string_of_operands m st i);
  flush_all ()
  
let travel_cast_instr m st i =
  eprintf "  %s = %s %s to %s\n"
    (llvm_name st i)
    (string_of_opcode (instr_opcode i))
    (string_of_operand m st (operand i 0))
    (string_type_of m i);
  flush_all ()

let travel_instr m st i =
  match (instr_opcode i) with
  | Opcode.Br ->
      if (BranchInst.is_conditional i)
      then 
        begin
          eprintf "  %s = br %s, %s, %s\n"
            (llvm_name st i)
            (string_of_operand m st (BranchInst.get_condition i))
            (string_of_operand m st (value_of_block 
              (BranchInst.get_successor i 0)))
            (string_of_operand m st (value_of_block 
              (BranchInst.get_successor i 1)));
          flush_all ()
        end        
      else
        travel_other_instr m st i
(*
  | Opcode.Malloc ->
      eprintf "  %s = malloc %s, %s, align %n\n"
        (llvm_name st i)
        (string_type_of m (AllocationInst.get_allocated_type i))
        (string_of_operand m st (AllocationInst.get_array_size i))
        (AllocationInst.get_alignment i);
      flush_all ()
*)
  | Opcode.Alloca ->
      eprintf "  %s = alloca %s, %s, align %n\n"
        (llvm_name st i)
        (my_string_of_lltype m (AllocationInst.get_allocated_type i))
        (string_of_operand m st (AllocationInst.get_array_size i))
        (AllocationInst.get_alignment i);
      flush_all ()    
  | Opcode.Load ->
      eprintf "  %s = load %s, align %n\n" 
        (llvm_name st i)  
        (string_of_operands m st i) 
        (LoadInst.get_alignment i);
      flush_all ()            
  | Opcode.Store ->
      eprintf "  %s = store %s, align %n\n" 
        (llvm_name st i)  
        (string_of_operands m st i) 
        (StoreInst.get_alignment i);
      flush_all ()    
  | Opcode.ICmp ->
      eprintf "  %s = icmp %s %s\n" 
        (llvm_name st i) 
        (string_of_icmp (ICmpInst.get_predicate i))
        (string_of_operands m st i);
      flush_all ()            
  | Opcode.FCmp ->
      eprintf "  %s = fcmp %s %s\n" 
        (llvm_name st i)  
        (string_of_fcmp (FCmpInst.get_predicate i))
        (string_of_operands m st i);
      flush_all ()            
  | Opcode.Call ->
      let fv = CallInst.get_called_value i in
      let fname = string_of_operand m st fv in
      let ptyp = type_of fv in
      let ftyp = element_type ptyp in
      let rtyp = return_type ftyp in
      let atyp = " (" ^ (concat2 ", " (
                  Array.map (my_string_of_lltype m) (param_types ftyp)
                 )) ^ ")" in      
      eprintf "  %s = call %s with rtyp=%s atyp=%s fid=%s\n" 
        (llvm_name st i) 
        (string_of_operands m st i)
        (my_string_of_lltype m rtyp) 
        atyp
        fname;
      flush_all ()                             
  | _ ->
      if is_cast_instruction i 
      then travel_cast_instr m st i
      else travel_other_instr m st i

let travel_block m st b =
  prerr_string "label: ";
  prerr_endline (llvm_label st b);
  iter_instrs (travel_instr m st) b;
  prerr_newline ()

let travel_function m st f =
  SlotTracker.incorporate_function st f;
  prerr_string (if (is_declaration f)  then "declare " else "define "); 
  prerr_string "fname: ";
  prerr_string (llvm_name st f);
  prerr_string " with ftyp: ";
  prerr_string (my_string_of_lltype m (type_of f));
  prerr_string " with params: ";
  Array.iter 
    (fun param -> 
      prerr_string (string_of_operand m st param); 
      prerr_string ", "
    ) 
    (params f);
  prerr_newline ();
  iter_blocks (travel_block m st) f;
  SlotTracker.purge_function st
  
let travel_global m st g =
  match (classify_value g) with
  | ValueKind.GlobalVariable -> 
    prerr_string (llvm_name st g);
    prerr_string " = ";
    prerr_string (string_of_linkage (linkage g));
    prerr_string (if (is_global_constant g) then  " constant " else " global ");
    if (has_initializer g)
    then
      prerr_string (string_of_operand m st (get_initializer g));
    prerr_newline ()
  | ValueKind.GlobalAlias -> dump_value g
  | ValueKind.Function -> travel_function m st g
  | _ -> failwith "Not_Global"

let travel_layout dlt =
  let tg = Llvm_target.TargetData.create dlt in
  let n = Llvm_target.get_num_alignment tg in
  prerr_string "layouts: ";
  prerr_endline dlt;
  eprintf "byteorde=%s\n"
    (string_of_endian (Llvm_target.byte_order tg));
  eprintf "p size=%s abi=%s pref=%s\n"
    (string_of_int ((Llvm_target.pointer_size tg)*8))
    (string_of_int ((Llvm_target.pointer_abi_alignment tg)*8))
    (string_of_int ((Llvm_target.pointer_pref_alignment tg)*8));
  for i = 0 to n-1 do
    eprintf "typ=%s bitwidth=%s abi=%s pref=%s\n"
      (string_of_aligntype (Llvm_target.get_align_type_enum tg i))
      (string_of_int (Llvm_target.get_type_bitwidth tg i))
      (string_of_int ((Llvm_target.get_abi_align tg i)*8))
      (string_of_int ((Llvm_target.get_pref_align tg i)*8));
    flush_all()
  done;
  Llvm_target.TargetData.dispose tg
  
let string_of_namedt m ty =
  match classify_type ty with
  TypeKind.Integer -> "i" ^ string_of_int (integer_bitwidth ty)
  | TypeKind.Pointer -> (my_string_of_lltype m (element_type ty)) ^ "*"
  | TypeKind.Struct ->
      let s = "{ " ^ (concat2 ", " (
                Array.map (my_string_of_lltype m) (struct_element_types ty)
              )) ^ " }" in
      if is_packed ty
        then "<" ^ s ^ ">"
        else s
  | TypeKind.Array -> "["   ^ (string_of_int (array_length ty)) ^
                      " x " ^ (my_string_of_lltype m (element_type ty)) ^ "]"
  | TypeKind.Vector -> "<"   ^ (string_of_int (vector_size ty)) ^
                       " x " ^ (my_string_of_lltype m (element_type ty)) ^ ">"
(*  | TypeKind.Opaque -> "opaque" *)
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
    
let travel_namedt m nt =
  match type_by_name m nt with
  | Some ty -> eprintf "%s=%s\n" nt (string_of_namedt m ty)
  | None -> failwith "Cannot find a named type!"    

let travel_module st m =
  prerr_endline "Travel LLVM module:";  
  travel_layout (data_layout m);
  iter_named_types (travel_namedt m) m;
  iter_globals (travel_global m st) m;
  iter_functions (travel_function m st) m

