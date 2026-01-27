open Printf
open Llvm
open Llvm_aux
open Syntax
open Infrastructure

let cnt = ref 0
let init_fake_name () = cnt := 0
let get_fake_name () = incr cnt; -(!cnt)

let llvm_name st v =
  if (has_name v)
  then
    if (is_globalvalue v)
    then "@"^(escaped_value_name v)
    else "%"^(escaped_value_name v)
  else
  if (is_globalvalue v)
  then
    "@"^(string_of_int (SlotTracker.get_global_slot st v))
  else
    let tmp = SlotTracker.get_local_slot st v in
    if tmp < 0 then 
      "%"^(string_of_int (get_fake_name ()))
    else
      "%"^(string_of_int tmp)

let llvm_label st b =
  let v = value_of_block b in
  if (has_name v)
  then
    escaped_value_name v
  else
    string_of_int (SlotTracker.get_local_slot st v)

let rec translate_floating_point ty = 
  match classify_type ty with
  | TypeKind.Ppc_fp128 -> LLVMsyntax.Coq_fp_ppc_fp128
  | TypeKind.Fp128 -> LLVMsyntax.Coq_fp_fp128
  | TypeKind.X86fp80 -> LLVMsyntax.Coq_fp_x86_fp80
  | TypeKind.Double -> LLVMsyntax.Coq_fp_double
  | TypeKind.Float -> LLVMsyntax.Coq_fp_float
  | _ -> failwith "This is not a floating point" 

let translate_var_arg (ftyp:lltype) : LLVMsyntax.varg =
  if is_var_arg ftyp then Some (Array.length (param_types ftyp)) else None

let rec translate_typ ty = 
  match classify_type ty with
  | TypeKind.Integer -> LLVMsyntax.Coq_typ_int (integer_bitwidth ty)
  | TypeKind.Pointer -> 
      (let ety = element_type ty in
      LLVMsyntax.Coq_typ_pointer
        (match classify_type ety with
        | TypeKind.Struct ->
            (match struct_name ety with
            | None -> translate_typ ety
            | Some s -> LLVMsyntax.Coq_typ_namedt s)
        | _ -> translate_typ ety))
  | TypeKind.Struct -> 
      (match struct_name ty with
      | None ->
          LLVMsyntax.Coq_typ_struct
            (Array.fold_right 
              (fun t ts -> translate_typ t :: ts) 
              (struct_element_types ty)
              [])
      | Some s -> LLVMsyntax.Coq_typ_namedt s)
  | TypeKind.Array -> LLVMsyntax.Coq_typ_array 
       (array_length ty, translate_typ (element_type ty))
  | TypeKind.Vector -> failwith "Vector: Not_Supported."
  | TypeKind.Function -> 
      LLVMsyntax.Coq_typ_function 
        (translate_typ (return_type ty),
          (Array.fold_right 
            (fun t ts -> (translate_typ t :: ts)) 
            (param_types ty)
            []),
          translate_var_arg ty)
  | TypeKind.Label -> LLVMsyntax.Coq_typ_label
  | TypeKind.Ppc_fp128 -> 
      LLVMsyntax.Coq_typ_floatpoint (translate_floating_point ty)
  | TypeKind.Fp128 -> 
      LLVMsyntax.Coq_typ_floatpoint (translate_floating_point ty)
  | TypeKind.X86fp80 -> 
      LLVMsyntax.Coq_typ_floatpoint (translate_floating_point ty)
  | TypeKind.Double -> 
      LLVMsyntax.Coq_typ_floatpoint (translate_floating_point ty)
  | TypeKind.Float -> 
      LLVMsyntax.Coq_typ_floatpoint (translate_floating_point ty)
  | TypeKind.Void -> LLVMsyntax.Coq_typ_void
  | TypeKind.Metadata -> LLVMsyntax.Coq_typ_metadata 

let translate_icmp op =
  match op with
  | Icmp.Eq -> LLVMsyntax.Coq_cond_eq
  | Icmp.Ne -> LLVMsyntax.Coq_cond_ne
  | Icmp.Ugt -> LLVMsyntax.Coq_cond_ugt
  | Icmp.Uge -> LLVMsyntax.Coq_cond_uge
  | Icmp.Ult -> LLVMsyntax.Coq_cond_ult
  | Icmp.Ule -> LLVMsyntax.Coq_cond_ule
  | Icmp.Sgt -> LLVMsyntax.Coq_cond_sgt
  | Icmp.Sge -> LLVMsyntax.Coq_cond_sge
  | Icmp.Slt -> LLVMsyntax.Coq_cond_slt
  | Icmp.Sle -> LLVMsyntax.Coq_cond_sle

let translate_fcmp op =
  match op with
  | Fcmp.False -> LLVMsyntax.Coq_fcond_false
  | Fcmp.Oeq -> LLVMsyntax.Coq_fcond_oeq
  | Fcmp.Ogt -> LLVMsyntax.Coq_fcond_ogt
  | Fcmp.Oge -> LLVMsyntax.Coq_fcond_oge
  | Fcmp.Olt -> LLVMsyntax.Coq_fcond_olt
  | Fcmp.Ole -> LLVMsyntax.Coq_fcond_ole
  | Fcmp.One -> LLVMsyntax.Coq_fcond_one
  | Fcmp.Ord -> LLVMsyntax.Coq_fcond_ord
  | Fcmp.Uno -> LLVMsyntax.Coq_fcond_uno
  | Fcmp.Ueq -> LLVMsyntax.Coq_fcond_ueq
  | Fcmp.Ugt -> LLVMsyntax.Coq_fcond_ugt
  | Fcmp.Uge -> LLVMsyntax.Coq_fcond_uge
  | Fcmp.Ult -> LLVMsyntax.Coq_fcond_ult
  | Fcmp.Ule -> LLVMsyntax.Coq_fcond_ule
  | Fcmp.Une -> LLVMsyntax.Coq_fcond_une
  | Fcmp.True -> LLVMsyntax.Coq_fcond_true

let translate_intrinsic_id id =
  match id with
  | IntrinsicID.NotIntrinsic -> failwith "NotIntrinsic"
  | IntrinsicID.Expect -> LLVMsyntax.Coq_iid_expect
  | IntrinsicID.Setjmp -> LLVMsyntax.Coq_iid_setjmp
  | IntrinsicID.SigSetjmp -> LLVMsyntax.Coq_iid_sigsetjmp
  | IntrinsicID.Longjmp -> LLVMsyntax.Coq_iid_longjmp
  | IntrinsicID.SigLongjmp -> LLVMsyntax.Coq_iid_siglongjmp
  | IntrinsicID.Ctpop -> LLVMsyntax.Coq_iid_ctpop
  | IntrinsicID.Bswap -> LLVMsyntax.Coq_iid_bswap
  | IntrinsicID.Ctlz -> LLVMsyntax.Coq_iid_ctlz
  | IntrinsicID.Cttz -> LLVMsyntax.Coq_iid_cttz
  | IntrinsicID.StackSave -> LLVMsyntax.Coq_iid_stacksave
  | IntrinsicID.StackRestore -> LLVMsyntax.Coq_iid_stackrestore
  | IntrinsicID.ReturnAddress -> LLVMsyntax.Coq_iid_returnaddress
  | IntrinsicID.FrameAddress -> LLVMsyntax.Coq_iid_frameaddress
  | IntrinsicID.Prefetch -> LLVMsyntax.Coq_iid_prefetch
  | IntrinsicID.Pcmarker -> LLVMsyntax.Coq_iid_pcmarker
  | IntrinsicID.ReadCycleCounter -> LLVMsyntax.Coq_iid_readcyclecounter
  | IntrinsicID.DbgDeclare -> LLVMsyntax.Coq_iid_dbg_declare
  | IntrinsicID.EhException -> LLVMsyntax.Coq_iid_eh_exception
  | IntrinsicID.EhSelector -> LLVMsyntax.Coq_iid_eh_selector
  | IntrinsicID.EhTypeidFor -> LLVMsyntax.Coq_iid_eh_typeidfor
  | IntrinsicID.VarAnnotation -> LLVMsyntax.Coq_iid_var_annotation
  | IntrinsicID.Memcpy -> LLVMsyntax.Coq_iid_memcpy
  | IntrinsicID.Memmove -> LLVMsyntax.Coq_iid_memmove
  | IntrinsicID.Memset -> LLVMsyntax.Coq_iid_memset
  | IntrinsicID.Sqrt -> LLVMsyntax.Coq_iid_sqrt
  | IntrinsicID.Log -> LLVMsyntax.Coq_iid_log
  | IntrinsicID.Log2 -> LLVMsyntax.Coq_iid_log2
  | IntrinsicID.Log10 -> LLVMsyntax.Coq_iid_log10
  | IntrinsicID.Exp -> LLVMsyntax.Coq_iid_exp
  | IntrinsicID.Exp2 -> LLVMsyntax.Coq_iid_exp2
  | IntrinsicID.Pow -> LLVMsyntax.Coq_iid_pow
  | IntrinsicID.FltRounds -> LLVMsyntax.Coq_iid_flt_rounds
  | IntrinsicID.InvariantStart -> LLVMsyntax.Coq_iid_invariantstart
  | IntrinsicID.LifetimeStart -> LLVMsyntax.Coq_iid_lifetimestart
  | IntrinsicID.InvariantEnd -> LLVMsyntax.Coq_iid_invariantend
  | IntrinsicID.LifetimeEnd -> LLVMsyntax.Coq_iid_lifetimeend
  | IntrinsicID.UnsupportedIntrinsic -> LLVMsyntax.Coq_iid_unsupported

let rec translate_constant m st c =   
  match (classify_value c) with
  | ValueKind.UndefValue -> 
      LLVMsyntax.Coq_const_undef (translate_typ (type_of c)) 
  | ValueKind.ConstantExpr -> translate_constant_expr m st c
  | ValueKind.ConstantAggregateZero -> 
      LLVMsyntax.Coq_const_zeroinitializer (translate_typ (type_of c))
  | ValueKind.ConstantInt -> 
      LLVMsyntax.Coq_const_int (integer_bitwidth
        (type_of c), APInt.const_int_get_value c)
  | ValueKind.ConstantFP ->  
      LLVMsyntax.Coq_const_floatpoint (translate_floating_point (type_of c), 
        APFloat.const_float_get_value c) 
  | ValueKind.ConstantArray -> 
      let ops = operands c in
      LLVMsyntax.Coq_const_arr (
         translate_typ (element_type (type_of c)),
         (Array.fold_right 
            (fun c cs -> 
               (translate_constant m st c :: cs)) ops 
                 [])
      )
  | ValueKind.ConstantStruct ->
      let ops = operands c in
      LLVMsyntax.Coq_const_struct (
         translate_typ (type_of c),
         (Array.fold_right (fun c cs -> 
           (translate_constant m st c :: cs)) ops [])
      )
  | ValueKind.ConstantVector -> failwith "ConstantVector: Not_Supported." 
  | ValueKind.ConstantPointerNull -> 
      LLVMsyntax.Coq_const_null (translate_typ (element_type (type_of c)))
  | ValueKind.GlobalVariable ->    (*GlobalValue*)
    (* FIXME: Do we need typ for gid? use typ_void for the time being. *)
      (LLVMsyntax.Coq_const_gid 
        (translate_typ (element_type (type_of c)), llvm_name st c))
  | ValueKind.Function ->   (*FunctionVal*)
      (LLVMsyntax.Coq_const_gid 
        (translate_typ (element_type (type_of c)), llvm_name st c))
  | _ -> failwith (string_of_valuekd (classify_value c) ^ " isnt Constant")
and translate_constant_expr m st c =
  let oc = constexpr_opcode c in
  match oc with
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
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_add,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.FAdd ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const FAdd must have 2 operand."
      else
        (LLVMsyntax.Coq_const_fbop
          (LLVMsyntax.Coq_fbop_fadd,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.Sub ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const Sub must have 2 operand."
      else
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_sub,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.FSub ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const FSub must have 2 operand."
      else
        (LLVMsyntax.Coq_const_fbop
          (LLVMsyntax.Coq_fbop_fsub,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.Mul ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const Mul must have 2 operand."
      else
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_mul,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.FMul ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const FMul must have 2 operand."
      else
        (LLVMsyntax.Coq_const_fbop
          (LLVMsyntax.Coq_fbop_fmul,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.UDiv ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const UDiv must have 2 operand."
      else
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_udiv,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.SDiv ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const SDiv must have 2 operand."
      else
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_sdiv,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.FDiv ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const FDiv must have 2 operand."
      else
        (LLVMsyntax.Coq_const_fbop
          (LLVMsyntax.Coq_fbop_fdiv,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.URem ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const URem must have 2 operand."
      else
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_urem,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.SRem ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const SRem must have 2 operand."
      else
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_srem,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.FRem ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const FRem must have 2 operand."
      else
        (LLVMsyntax.Coq_const_fbop
          (LLVMsyntax.Coq_fbop_frem,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.Shl ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const Shl must have 2 operand."
      else
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_shl,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.LShr ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const LShr must have 2 operand."
      else
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_lshr,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.AShr ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const AShr must have 2 operand."
      else
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_ashr,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.And ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const And must have 2 operand."
      else
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_and,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.Or ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const Or must have 2 operand."
      else
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_or,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
  | Opcode.Xor ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const XOr must have 2 operand."
      else
        (LLVMsyntax.Coq_const_bop
          (LLVMsyntax.Coq_bop_xor,
          translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1))
        )
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
            (translate_constant m st (Array.get ops b) :: (range (b + 1) e ops))
          else
            [] in
        (LLVMsyntax.Coq_const_gep
          (Llvm.GetElementPtrInst.is_in_bounds c,
           translate_constant m st (Array.get ops 0),
           range 1 n ops)
        )
  | Opcode.Trunc ->        
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const Trunc must have 1 operand."
      else
        (LLVMsyntax.Coq_const_truncop
          (LLVMsyntax.Coq_truncop_int,
          translate_constant m st (Array.get ops 0),
          translate_typ (type_of c))
        )
  | Opcode.ZExt ->        
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const ZExt must have 1 operand."
      else
        (LLVMsyntax.Coq_const_extop
          (LLVMsyntax.Coq_extop_z,
          translate_constant m st (Array.get ops 0),
          translate_typ (type_of c))
        )
  | Opcode.SExt ->        
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const SExt must have 1 operand."
      else
        (LLVMsyntax.Coq_const_extop
          (LLVMsyntax.Coq_extop_s,
          translate_constant m st (Array.get ops 0),
          translate_typ (type_of c))
        )
  |  Opcode.FPToUI ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const FPToUI must have 1 operand."
      else
        (LLVMsyntax.Coq_const_castop
          (LLVMsyntax.Coq_castop_fptoui,
          translate_constant m st (Array.get ops 0),
          translate_typ (type_of c))
        )        
  |  Opcode.FPToSI ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const FPToSI must have 1 operand."
      else
        (LLVMsyntax.Coq_const_castop
          (LLVMsyntax.Coq_castop_fptosi,
          translate_constant m st (Array.get ops 0),
          translate_typ (type_of c))
        )        
  |  Opcode.UIToFP ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const UIToFP must have 1 operand."
      else
        (LLVMsyntax.Coq_const_castop
          (LLVMsyntax.Coq_castop_uitofp,
          translate_constant m st (Array.get ops 0),
          translate_typ (type_of c))
        )        
  |  Opcode.SIToFP ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const SIToFP must have 1 operand."
      else
        (LLVMsyntax.Coq_const_castop
          (LLVMsyntax.Coq_castop_sitofp,
          translate_constant m st (Array.get ops 0),
          translate_typ (type_of c))
        )        
  |  Opcode.FPTrunc ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const FPTrunc must have 1 operand."
      else
        (LLVMsyntax.Coq_const_truncop
          (LLVMsyntax.Coq_truncop_fp,
          translate_constant m st (Array.get ops 0),
          translate_typ (type_of c))
        )        
  |  Opcode.FPExt ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const FPExt must have 1 operand."
      else
        (LLVMsyntax.Coq_const_extop
          (LLVMsyntax.Coq_extop_fp,
          translate_constant m st (Array.get ops 0),
          translate_typ (type_of c))
        )        
  |  Opcode.PtrToInt ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const PtrToInt must have 1 operand."
      else
        (LLVMsyntax.Coq_const_castop
          (LLVMsyntax.Coq_castop_ptrtoint,
          translate_constant m st (Array.get ops 0),
          translate_typ (type_of c))
        )        
  |  Opcode.IntToPtr ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const IntToPtr must have 1 operand."
      else
        (LLVMsyntax.Coq_const_castop
          (LLVMsyntax.Coq_castop_inttoptr,
          translate_constant m st (Array.get ops 0),
          translate_typ (type_of c))
        )        
  |  Opcode.BitCast ->
      let ops = operands c in
      let n = num_operands c in
      if n != 1
      then failwith "Const BitCast must have 1 operand."
      else
        (LLVMsyntax.Coq_const_castop
          (LLVMsyntax.Coq_castop_bitcast,
          translate_constant m st (Array.get ops 0),
          translate_typ (type_of c))
        )        
  | Opcode.ICmp ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const ICmp must have 2 operand."
      else
        (LLVMsyntax.Coq_const_icmp
          (translate_icmp (ICmpInst.const_get_predicate c),
           translate_constant m st (Array.get ops 0),
           translate_constant m st (Array.get ops 1))
        )
  | Opcode.FCmp ->
      let ops = operands c in
      let n = num_operands c in
      if n != 2
      then failwith "Const FCmp must have 2 operand."
      else
        (LLVMsyntax.Coq_const_fcmp
          (translate_fcmp (FCmpInst.const_get_predicate c),
           translate_constant m st (Array.get ops 0),
           translate_constant m st (Array.get ops 1))
        )
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
        (LLVMsyntax.Coq_const_select
          (translate_constant m st (Array.get ops 0),
          translate_constant m st (Array.get ops 1),
          translate_constant m st (Array.get ops 2))
        )        
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
      failwith "Const ShuffleVector: Not_Supported"
  | Opcode.ExtractValue ->      
      let ops = operands c in
      let n = num_operands c in
      if n < 1
      then failwith "Const ExtractValue must have >=1 operand."
      else
        (LLVMsyntax.Coq_const_extractvalue
          (translate_constant m st (Array.get ops 0),
           Array.fold_right 
             (fun idx acc -> 
		let cst = const_int (i32_type (module_context m)) idx in
                ((translate_constant m st cst) :: acc))
             (const_aggregatevalue_get_indices c) 
             [])
        )
  | Opcode.InsertValue ->      
      let ops = operands c in
      let n = num_operands c in
      if n < 2
      then failwith "Const InsertValue must have >=2 operand."
      else
        (LLVMsyntax.Coq_const_insertvalue
          (translate_constant m st (Array.get ops 0),
           translate_constant m st (Array.get ops 1),
           Array.fold_right 
             (fun idx acc -> 
		let cst = const_int (i32_type (module_context m)) idx in
                ((translate_constant m st cst) :: acc))
             (const_aggregatevalue_get_indices c) 
             [])
        )
  | Opcode.LandingPad | Opcode.Resume | Opcode.AtomicRMW | Opcode.AtomicCmpXchg
  | Opcode.Fence | Opcode.Invalid2 | Opcode.IndirectBr | Opcode.Invalid ->      
      failwith ("Const " ^ string_of_opcode oc ^ ": Not_Supported")

let translate_operand_to_value m st v = 
  match (classify_value v) with
  | ValueKind.Argument -> LLVMsyntax.Coq_value_id (llvm_name st v)
  | ValueKind.BasicBlock -> LLVMsyntax.Coq_value_id (llvm_name st v)
  | ValueKind.Function ->                    (*FunctionVal*)
      LLVMsyntax.Coq_value_const 
        (LLVMsyntax.Coq_const_gid 
          (translate_typ (element_type (type_of v)), llvm_name st v))
  | ValueKind.GlobalAlias -> LLVMsyntax.Coq_value_id (llvm_name st v) 
      (*GlobalValue*)
  | ValueKind.GlobalVariable ->              (*GlobalValue*)
      LLVMsyntax.Coq_value_const 
        (LLVMsyntax.Coq_const_gid 
          (translate_typ (element_type (type_of v)), llvm_name st v))
  | ValueKind.UndefValue -> 
      LLVMsyntax.Coq_value_const (translate_constant m st v)
  | ValueKind.ConstantExpr -> 
      LLVMsyntax.Coq_value_const (translate_constant m st v)
  | ValueKind.ConstantAggregateZero -> 
      LLVMsyntax.Coq_value_const (translate_constant m st v)
  | ValueKind.ConstantInt -> 
      LLVMsyntax.Coq_value_const (translate_constant m st v)
  | ValueKind.ConstantFP -> 
      LLVMsyntax.Coq_value_const (translate_constant m st v)
  | ValueKind.ConstantArray -> 
      LLVMsyntax.Coq_value_const (translate_constant m st v)
  | ValueKind.ConstantStruct -> 
      LLVMsyntax.Coq_value_const (translate_constant m st v)
  | ValueKind.ConstantVector -> 
      LLVMsyntax.Coq_value_const (translate_constant m st v)
  | ValueKind.ConstantPointerNull -> 
      LLVMsyntax.Coq_value_const (translate_constant m st v)
  | ValueKind.NullValue -> failwith "NullValue: Not_Supported."
  | ValueKind.BlockAddress -> failwith "BlockAddress: Not_Supported."
  | ValueKind.MDNode -> failwith "MDNodeVal: Not_Supported."
  | ValueKind.MDString -> failwith "MDStringVal: Not_Supported."
  | ValueKind.InlineAsm -> failwith "InlineAsmVal: Not_Supported."
  | _ -> LLVMsyntax.Coq_value_id (llvm_name st v)   (*Instruction*)

let translate_callsite_param_attrs ci nth =
  let pattrs = [] in
  let pattrs = if has_instruction_param_attr ci nth Attribute.Zext then
               LLVMsyntax.Coq_attribute_zext::pattrs else pattrs in
  let pattrs = if has_instruction_param_attr ci nth Attribute.Sext then
               LLVMsyntax.Coq_attribute_sext::pattrs else pattrs in
  let pattrs = if has_instruction_param_attr ci nth Attribute.Inreg then
               LLVMsyntax.Coq_attribute_inreg::pattrs else pattrs in
  let pattrs = if has_instruction_param_attr ci nth Attribute.Byval then
               LLVMsyntax.Coq_attribute_byval::pattrs else pattrs in
  let pattrs = if has_instruction_param_attr ci nth Attribute.Structret then
               LLVMsyntax.Coq_attribute_structret::pattrs else pattrs in
  let pattrs = if has_instruction_param_attr ci nth Attribute.Noalias then
               LLVMsyntax.Coq_attribute_noalias::pattrs else pattrs in
  let pattrs = if has_instruction_param_attr ci nth Attribute.Nocapture then
               LLVMsyntax.Coq_attribute_nocapture::pattrs else pattrs in
  let pattrs = if has_instruction_param_attr ci nth Attribute.Nest then
               LLVMsyntax.Coq_attribute_nest::pattrs else pattrs in
  pattrs

let translate_operand_to_param m st ci nth v = 
  ((translate_typ (type_of v), 
    translate_callsite_param_attrs ci nth),
   translate_operand_to_value m st v)

let array_size_to_int c =
  match (classify_value c) with
  | ValueKind.ConstantInt -> 
      if integer_bitwidth (type_of c) != 32
      then
        failwith "array_size must be with type i32"
      else
        Int64.to_int (Llvm.APInt.get_zext_value
                                (Llvm.APInt.const_int_get_value c))       
  | _ -> failwith (string_of_valuekd (classify_value c) ^ 
           ": array_size must be ConstantIntVal")

let translate_callsite_attrs i =
  let rattrs = [] in
  let rattrs = if has_instruction_ret_attr i Attribute.Zext then
                 LLVMsyntax.Coq_attribute_zext::rattrs else rattrs in
  let rattrs = if has_instruction_ret_attr i Attribute.Sext then
               LLVMsyntax.Coq_attribute_sext::rattrs else rattrs in
  let rattrs = if has_instruction_ret_attr i Attribute.Inreg then
               LLVMsyntax.Coq_attribute_inreg::rattrs else rattrs in
  let rattrs = if has_instruction_ret_attr i Attribute.Noalias then
               LLVMsyntax.Coq_attribute_noalias::rattrs else rattrs in
  let fattrs = [] in
  let fattrs = if has_instruction_attr i Attribute.Noreturn then
               LLVMsyntax.Coq_attribute_noreturn::fattrs else fattrs in
  let fattrs = if has_instruction_attr i Attribute.Nounwind then
               LLVMsyntax.Coq_attribute_nounwind::fattrs else fattrs  in
  let fattrs = if has_instruction_attr i Attribute.Readonly then
               LLVMsyntax.Coq_attribute_readonly::fattrs else fattrs  in
  let fattrs = if has_instruction_attr i Attribute.Readnone then
               LLVMsyntax.Coq_attribute_readnone::fattrs else fattrs  in
  (rattrs, fattrs)

let int_to_callconv i =
  if i = CallConv.c then LLVMsyntax.Coq_callconv_ccc 
  else if i = CallConv.fast then LLVMsyntax.Coq_callconv_fast
  else if i = CallConv.cold then LLVMsyntax.Coq_callconv_cold
  else if i = CallConv.x86_stdcall then LLVMsyntax.Coq_callconv_x86_stdcall
  else if i = CallConv.x86_fastcall then LLVMsyntax.Coq_callconv_x86_fastcall
  else failwith "unknown call conversion"

let translate_instr debug m st i  =
  (* debugging output *)
  (if debug then Llvm_pretty_printer.travel_instr m st i); 

  let oc = instr_opcode i in   
  match oc with
  | Opcode.Ret ->
      begin
        if ReturnInst.is_void i
        then
            LLVMsyntax.Coq_insn_terminator
            (LLVMsyntax.Coq_insn_return_void
              (llvm_name st i)
            )
        else
            let ops = operands i in
            let n = num_operands i in
            if n != 1
            then failwith "Ret must have 1 operand."
            else
              LLVMsyntax.Coq_insn_terminator
              (LLVMsyntax.Coq_insn_return
                (llvm_name st i,
                translate_typ (type_of (Array.get ops 0)),
                translate_operand_to_value m st (Array.get ops 0))
              )
      end
  | Opcode.Br ->
      if (BranchInst.is_conditional i)
      then
        LLVMsyntax.Coq_insn_terminator (
          LLVMsyntax.Coq_insn_br
          (llvm_name st i,
          translate_operand_to_value m st (BranchInst.get_condition i),
          llvm_label st (BranchInst.get_successor i 0),
          llvm_label st (BranchInst.get_successor i 1))
        )
      else
        LLVMsyntax.Coq_insn_terminator (
          LLVMsyntax.Coq_insn_br_uncond
          (llvm_name st i,
          llvm_label st (BranchInst.get_successor i 0))
        )
  | Opcode.Switch ->
      failwith "Switch: Not_Supported"
  | Opcode.Invoke ->      
      failwith "Invoke: Not_Supported"
  | Opcode.Unwind ->
      failwith "Unwind: Not_Supported"
  | Opcode.Unreachable ->
      LLVMsyntax.Coq_insn_terminator (LLVMsyntax.Coq_insn_unreachable 
        (llvm_name st i))
  | Opcode.Add ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "Add must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_add,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.FAdd ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "FAdd must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_fbop
          (llvm_name st i,
          LLVMsyntax.Coq_fbop_fadd,
          (translate_floating_point (type_of i)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.Sub ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "Sub must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_sub,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.FSub ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "FSub must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_fbop
          (llvm_name st i,
          LLVMsyntax.Coq_fbop_fsub,
          (translate_floating_point (type_of i)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.Mul ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "Mul must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_mul,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.FMul ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "FMul must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_fbop
          (llvm_name st i,
          LLVMsyntax.Coq_fbop_fmul,
          (translate_floating_point (type_of i)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.UDiv ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "UDiv must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_udiv,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.SDiv ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "SDiv must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_sdiv,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.FDiv ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "FDiv must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_fbop
          (llvm_name st i,
          LLVMsyntax.Coq_fbop_fdiv,
          (translate_floating_point (type_of i)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.URem ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "URem must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_urem,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.SRem ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "SRem must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_srem,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.FRem ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "FRem must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_fbop
          (llvm_name st i,
          LLVMsyntax.Coq_fbop_frem,
          (translate_floating_point (type_of i)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.Shl ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "Shl must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_shl,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.LShr ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "LShr must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_lshr,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.AShr ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "AShr must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_ashr,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.And ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "And must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_and,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.Or ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "Or must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_or,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.Xor ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "Xor must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_bop
          (llvm_name st i,
          LLVMsyntax.Coq_bop_xor,
          integer_bitwidth (type_of i),
          translate_operand_to_value m st (Array.get ops 0),
          translate_operand_to_value m st (Array.get ops 1))
        )
(*
  | Opcode.Malloc ->
      LLVMsyntax.Coq_insn_cmd
      (LLVMsyntax.Coq_insn_malloc
        (llvm_name st i,
          translate_typ (AllocationInst.get_allocated_type i),
          translate_operand_to_value m st (AllocationInst.get_array_size i),
          (AllocationInst.get_alignment i))
      )
  | Opcode.Free ->
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "Free must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_free
          (llvm_name st i,
            translate_typ (type_of (Array.get ops 0)),
            translate_operand_to_value m st (Array.get ops 0))
        )
*)
  | Opcode.Alloca ->
      LLVMsyntax.Coq_insn_cmd
      (LLVMsyntax.Coq_insn_alloca
        (llvm_name st i,
          translate_typ (AllocationInst.get_allocated_type i),
          translate_operand_to_value m st (AllocationInst.get_array_size i),
          (AllocationInst.get_alignment i))
      )
  | Opcode.Load ->
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "Load must have 1 operand."
      else
        begin
        match translate_typ (type_of (Array.get ops 0)) with
          | LLVMsyntax.Coq_typ_pointer t ->
            LLVMsyntax.Coq_insn_cmd
            (LLVMsyntax.Coq_insn_load
              (llvm_name st i,
                t,
                translate_operand_to_value m st (Array.get ops 0),
                LoadInst.get_alignment i)
            )
          | _ -> failwith "Load must be with ptr type"
        end
  | Opcode.Store ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "Store must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_store
          (llvm_name st i,
            translate_typ (type_of (Array.get ops 0)),
            translate_operand_to_value m st (Array.get ops 0),
            translate_operand_to_value m st (Array.get ops 1),
            StoreInst.get_alignment i)
        )
  | Opcode.GetElementPtr ->        
      let n = num_operands i in
      if n < 1
      then failwith "GEP must have >=1 operand."
      else
        let ops = operands i in
         let n = num_operands i in
        let rec range b e ops =
          if b < e
          then
            ((integer_bitwidth (type_of (Array.get ops b)),
              translate_operand_to_value m st (Array.get ops b)) :: 
             (range (b + 1) e ops))
          else
            [] in
        let ty = translate_typ (element_type (type_of (Array.get ops 0))) in
        let ty' = translate_typ (element_type (type_of i)) in
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_gep
          (llvm_name st i,
           Llvm.GetElementPtrInst.is_in_bounds i,
           ty,  
           (* returns the elt typ of the 1st op's pointer typ *)
           translate_operand_to_value m st (Array.get ops 0),
           range 1 n ops,
           ty')
        )
  | Opcode.Trunc ->        
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "Trunc must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_trunc
          (llvm_name st i,
          LLVMsyntax.Coq_truncop_int,
          translate_typ (type_of (Array.get ops 0)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of i))
        )
  | Opcode.ZExt ->        
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "ZExt must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_ext
          (llvm_name st i,
          LLVMsyntax.Coq_extop_z,
          translate_typ (type_of (Array.get ops 0)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of i))
        )
  | Opcode.SExt ->        
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "SExt must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_ext
          (llvm_name st i,
          LLVMsyntax.Coq_extop_s,
          translate_typ (type_of (Array.get ops 0)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of i))
        )
  |  Opcode.FPToUI ->
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "FPToUI must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_cast
          (llvm_name st i,
          LLVMsyntax.Coq_castop_fptoui,
          translate_typ (type_of (Array.get ops 0)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of i))
        )        
  |  Opcode.FPToSI ->
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "FPToSI must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_cast
          (llvm_name st i,
          LLVMsyntax.Coq_castop_fptosi,
          translate_typ (type_of (Array.get ops 0)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of i))
        )        
  |  Opcode.UIToFP ->
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "UIToFP must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_cast
          (llvm_name st i,
          LLVMsyntax.Coq_castop_uitofp,
          translate_typ (type_of (Array.get ops 0)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of i))
        )        
  |  Opcode.SIToFP ->
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "SIToFP must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_cast
          (llvm_name st i,
          LLVMsyntax.Coq_castop_sitofp,
          translate_typ (type_of (Array.get ops 0)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of i))
        )        
  |  Opcode.FPTrunc ->
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "FPTrunc must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_trunc
          (llvm_name st i,
          LLVMsyntax.Coq_truncop_fp,
          translate_typ (type_of (Array.get ops 0)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of i))
        )
  |  Opcode.FPExt ->
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "FPExt must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_ext
          (llvm_name st i,
          LLVMsyntax.Coq_extop_fp,
          translate_typ (type_of (Array.get ops 0)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of i))
        )
  |  Opcode.PtrToInt ->
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "PtrToInt must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_cast
          (llvm_name st i,
          LLVMsyntax.Coq_castop_ptrtoint,
          translate_typ (type_of (Array.get ops 0)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of i))
        )        
  |  Opcode.IntToPtr ->
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "IntToPtr must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_cast
          (llvm_name st i,
          LLVMsyntax.Coq_castop_inttoptr,
          translate_typ (type_of (Array.get ops 0)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of i))
        )        
  |  Opcode.BitCast ->
      let ops = operands i in
      let n = num_operands i in
      if n != 1
      then failwith "BitCast must have 1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_cast
          (llvm_name st i,
          LLVMsyntax.Coq_castop_bitcast,
          translate_typ (type_of (Array.get ops 0)),
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of i))
        )        
  | Opcode.ICmp ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "ICmp must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_icmp
          (llvm_name st i,
            translate_icmp (ICmpInst.get_predicate i),
            translate_typ (type_of (Array.get ops 0)),
            translate_operand_to_value m st (Array.get ops 0),
            translate_operand_to_value m st (Array.get ops 1))
        )
  | Opcode.FCmp ->
      let ops = operands i in
      let n = num_operands i in
      if n != 2
      then failwith "FCmp must have 2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_fcmp
          (llvm_name st i,
            translate_fcmp (FCmpInst.get_predicate i),
            translate_floating_point (type_of (Array.get ops 0)),
            translate_operand_to_value m st (Array.get ops 0),
            translate_operand_to_value m st (Array.get ops 1))
        )
  |  Opcode.PHI ->
      let v_l_list = incoming i in
      let n = num_operands i in
      if n < 1
      then failwith "GEP must have >=1 operand."
      else
        LLVMsyntax.Coq_insn_phinode
        (LLVMsyntax.Coq_insn_phi
          (llvm_name st i,
           translate_typ (type_of i),
           (List.fold_right          
             (fun (v, l) v_l_list ->
                (translate_operand_to_value m st v, llvm_label st l) :: v_l_list)
             v_l_list
             []
           ))
        )
  | Opcode.Call ->
      let ops = operands i in
      let n = num_operands i in
      (if n <=0 then failwith "Call must have more than 0 operand.");
      let fv = CallInst.get_called_value i in
      let ptyp = type_of fv in
      let ftyp = element_type ptyp in
      let rtyp = return_type ftyp in
      let noret = match (classify_type rtyp) with
        | TypeKind.Void -> true
        | _ -> false in
      let tailc = is_tail_call i in
      let rec range b e ops =
        if b < e
        then
          translate_operand_to_param m st i b (Array.get ops b):: 
            (range (b + 1) e ops)
        else
          [] in
      let (rattrs, fattrs) = translate_callsite_attrs i in
      let cc = int_to_callconv (instruction_call_conv i) in
      LLVMsyntax.Coq_insn_cmd
      (LLVMsyntax.Coq_insn_call
        (llvm_name st i,
          noret,
          (LLVMsyntax.Coq_clattrs_intro (tailc, cc, rattrs, fattrs)),
          translate_typ rtyp,
          translate_var_arg ftyp,
          translate_operand_to_value m st fv,
          range 0 (n-1) ops)
      )
  | Opcode.Select ->      
      let ops = operands i in
      let n = num_operands i in
      if n != 3
      then failwith "Select must have 3 operands."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_select
          (llvm_name st i,
          translate_operand_to_value m st (Array.get ops 0),
          translate_typ (type_of (Array.get ops 1)),
          translate_operand_to_value m st (Array.get ops 1),
          translate_operand_to_value m st (Array.get ops 2))
        )        
  | Opcode.UserOp1 ->      
      failwith "UserOp1: Not_Supported"
  | Opcode.UserOp2 ->      
      failwith "UserOp2: Not_Supported"
  | Opcode.VAArg ->      
      failwith "VAArg: Not_Supported"
  | Opcode.ExtractElement ->      
      failwith "ExtractElement: Not_Supported"
  | Opcode.InsertElement ->      
      failwith "InsertElement: Not_Supported"
  | Opcode.ShuffleVector ->      
      failwith "ShuffleVector: Not_Supported"
  | Opcode.ExtractValue ->      
      let ops = operands i in
      let n = num_operands i in
      let ty' = translate_typ (type_of i) in
      if n < 1
      then failwith "ExtractValue must have >=1 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_extractvalue
          (llvm_name st i,
           translate_typ (type_of (Array.get ops 0)),
           translate_operand_to_value m st (Array.get ops 0),
           Array.fold_right 
             (fun idx acc -> 
		let cst = const_int (i32_type (module_context m)) idx in
                ((translate_constant m st cst) :: acc))
             (ExtractValueInst.get_indices i) 
             [],
           ty'))

  | Opcode.InsertValue ->      
      let ops = operands i in
      let n = num_operands i in
      if n < 2
      then failwith "InsertValue must have >=2 operand."
      else
        LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_insertvalue
          (llvm_name st i,
           translate_typ (type_of (Array.get ops 0)),
           translate_operand_to_value m st (Array.get ops 0),
           translate_typ (type_of (Array.get ops 1)),
           translate_operand_to_value m st (Array.get ops 1),
           Array.fold_right 
             (fun idx acc -> 
		let cst = const_int (i32_type (module_context m)) idx in
                ((translate_constant m st cst) :: acc))
             (InsertValueInst.get_indices i) 
             [])
        )
  | Opcode.LandingPad | Opcode.Resume | Opcode.AtomicRMW | Opcode.AtomicCmpXchg
  | Opcode.Fence | Opcode.Invalid2 | Opcode.IndirectBr | Opcode.Invalid ->      
      failwith (string_of_opcode oc ^ ": Not_Supported")

let translate_block debug m st b bs =
  (* debugging output *)
  (if debug then
    (prerr_string "label: ";
    prerr_endline (llvm_label st b);
    prerr_newline ()));
  
  (* translation *)
  let ((ps, cs, otmn): LLVMsyntax.phinodes * LLVMsyntax.cmds * 
      LLVMsyntax.terminator option) =
    fold_right_instrs
      (fun instr ((ps', cs', otmn'): 
         LLVMsyntax.phinodes * LLVMsyntax.cmds * LLVMsyntax.terminator option) ->
            let i = translate_instr debug m st instr in
            match i with
            | LLVMsyntax.Coq_insn_terminator tmn0 ->
                if List.length ps' == 0 &&
                List.length cs' == 0 &&
                otmn' == None
                then
                  (ps', cs', Some tmn0)
                else
                  failwith "Tmn must be at the end of the block."
            | LLVMsyntax.Coq_insn_phinode phi0 ->
                if otmn' == None
                then
                  failwith "There is not a Tmn at the end of the block."
                else
                  (phi0:: ps', cs', otmn')
            | LLVMsyntax.Coq_insn_cmd cmd0 ->
                if otmn' == None
                then
                  failwith "There is not a Tmn must be at the end of the block."
                else
                if List.length ps' == 0
                then
                  (ps', cmd0:: cs', otmn')
                else
                  failwith "PhiNode must be grouped at the beginning of the block."
      )
      b
      ([], [], None)
  in
  match otmn with
  | Some tmn ->
      (llvm_label st b, LLVMsyntax.Coq_stmts_intro (ps, cs, tmn)):: bs
  | None -> failwith "There is not a Tmn at the end of the block."

let translate_linkage g =
match linkage g with
  | Linkage.External -> LLVMsyntax.Coq_linkage_external
  | Linkage.Available_externally -> LLVMsyntax.Coq_linkage_available_externally
  | Linkage.Link_once -> LLVMsyntax.Coq_linkage_link_once
  | Linkage.Link_once_odr -> LLVMsyntax.Coq_linkage_link_once_odr
  | Linkage.Weak -> LLVMsyntax.Coq_linkage_weak
  | Linkage.Weak_odr -> LLVMsyntax.Coq_linkage_weak_odr
  | Linkage.Appending -> LLVMsyntax.Coq_linkage_appending
  | Linkage.Internal -> LLVMsyntax.Coq_linkage_internal
  | Linkage.Private -> LLVMsyntax.Coq_linkage_private
  | Linkage.Linker_private -> LLVMsyntax.Coq_linkage_linker_private
  | Linkage.Dllimport -> LLVMsyntax.Coq_linkage_dllimport
  | Linkage.Dllexport -> LLVMsyntax.Coq_linkage_dllexport
  | Linkage.External_weak -> LLVMsyntax.Coq_linkage_external_weak
  | Linkage.Ghost -> LLVMsyntax.Coq_linkage_ghost
  | Linkage.Common -> LLVMsyntax.Coq_linkage_common

let translate_visibility g =
match visibility g with
  | Visibility.Default -> LLVMsyntax.Coq_visibility_default
  | Visibility.Hidden -> LLVMsyntax.Coq_visibility_hidden
  | Visibility.Protected -> LLVMsyntax.Coq_visibility_protected

let translate_fun_attrs f =
  let rattrs = [] in
  let rattrs = if has_ret_attr f Attribute.Zext then
               LLVMsyntax.Coq_attribute_zext::rattrs else rattrs in
  let rattrs = if has_ret_attr f Attribute.Sext then
               LLVMsyntax.Coq_attribute_sext::rattrs else rattrs in
  let rattrs = if has_ret_attr f Attribute.Inreg then
               LLVMsyntax.Coq_attribute_inreg::rattrs else rattrs in
  let rattrs = if has_ret_attr f Attribute.Byval then
               LLVMsyntax.Coq_attribute_byval::rattrs else rattrs in
  let rattrs = if has_ret_attr f Attribute.Structret then
               LLVMsyntax.Coq_attribute_structret::rattrs else rattrs in
  let rattrs = if has_ret_attr f Attribute.Noalias then
               LLVMsyntax.Coq_attribute_noalias::rattrs else rattrs in
  let rattrs = if has_ret_attr f Attribute.Nocapture then
               LLVMsyntax.Coq_attribute_nocapture::rattrs else rattrs in
  let rattrs = if has_ret_attr f Attribute.Nest then
               LLVMsyntax.Coq_attribute_nest::rattrs else rattrs in
  let fattrs = [] in
  let fattrs = if has_fn_attr f Attribute.Noreturn then
               LLVMsyntax.Coq_attribute_noreturn::fattrs else fattrs in
  let fattrs = if has_fn_attr f Attribute.Nounwind then
               LLVMsyntax.Coq_attribute_nounwind::fattrs else fattrs in
  let fattrs = if has_fn_attr f Attribute.Alwaysinline then
               LLVMsyntax.Coq_attribute_alwaysinline::fattrs else fattrs in
  let fattrs = if has_fn_attr f Attribute.Noinline then
               LLVMsyntax.Coq_attribute_noinline::fattrs else fattrs in
  let fattrs = if has_fn_attr f Attribute.Optsize then
               LLVMsyntax.Coq_attribute_optforsize::fattrs else fattrs in
  let fattrs = if has_fn_attr f Attribute.Readnone then
               LLVMsyntax.Coq_attribute_readnone::fattrs else fattrs in
  let fattrs = if has_fn_attr f Attribute.Readonly then
               LLVMsyntax.Coq_attribute_readonly::fattrs else fattrs in
  let fattrs = if has_fn_attr f Attribute.Ssp then
               LLVMsyntax.Coq_attribute_stackprotect::fattrs else fattrs in
  let fattrs = if has_fn_attr f Attribute.Sspreq then
               LLVMsyntax.Coq_attribute_stackprotectreq::fattrs else fattrs in
  let fattrs = if has_fn_attr f Attribute.Noredzone then
               LLVMsyntax.Coq_attribute_noredzone::fattrs else fattrs in
  let fattrs = if has_fn_attr f Attribute.Noimplicitfloat then
               LLVMsyntax.Coq_attribute_implicitfloat::fattrs else fattrs in
  let fattrs = if has_fn_attr f Attribute.Naked then
               LLVMsyntax.Coq_attribute_naked::fattrs else fattrs in
  (rattrs, fattrs)

let translate_param_attrs op =
  let pattrs = [] in
  let pattrs = if has_param_attr op Attribute.Zext then
               LLVMsyntax.Coq_attribute_zext::pattrs else pattrs in
  let pattrs = if has_param_attr op Attribute.Sext then
               LLVMsyntax.Coq_attribute_sext::pattrs else pattrs in
  let pattrs = if has_param_attr op Attribute.Inreg then
               LLVMsyntax.Coq_attribute_inreg::pattrs else pattrs in
  let pattrs = if has_param_attr op Attribute.Byval then
               LLVMsyntax.Coq_attribute_byval::pattrs else pattrs in
  let pattrs = if has_param_attr op Attribute.Structret then
               LLVMsyntax.Coq_attribute_structret::pattrs else pattrs in
  let pattrs = if has_param_attr op Attribute.Noalias then
               LLVMsyntax.Coq_attribute_noalias::pattrs else pattrs in
  let pattrs = if has_param_attr op Attribute.Nocapture then
               LLVMsyntax.Coq_attribute_nocapture::pattrs else pattrs in
  let pattrs = if has_param_attr op Attribute.Nest then
               LLVMsyntax.Coq_attribute_nest::pattrs else pattrs in
  pattrs

let translate_operand_to_arg m st v = 
  ((translate_typ (type_of v), translate_param_attrs v), llvm_name st v)

let is_malloc st f =
  match (llvm_name st f) with
    | "@malloc" | "@_Znwj" | "@_Znwm" | "@_Znaj" | "@_Znam" -> true
    | _ -> false

let is_free st f =
  match (llvm_name st f) with
    | "@free" | "@_ZdlPv" | "@_ZdaPv" -> true
    | _ -> false

let translate_deckind st f =
  if (Llvm.is_intrinsic f) then 
    LLVMsyntax.Coq_deckind_intrinsic 
      (translate_intrinsic_id (Llvm.get_intrinsic_id f))
  else
    if (is_malloc st f) then
      LLVMsyntax.Coq_deckind_external LLVMsyntax.Coq_eid_malloc
    else if (is_free st f) then
      LLVMsyntax.Coq_deckind_external LLVMsyntax.Coq_eid_free
    else LLVMsyntax.Coq_deckind_external LLVMsyntax.Coq_eid_other

let translate_function debug m st f ps =
  (if not (is_declaration f) then 
   begin
     (if !Globalstates.gen_llvm_dtree then
       let dt = Llvm_analysis.create_dtree f in
       (if !Globalstates.print_dtree then 
         prerr_string "fname: "; 
         prerr_string (llvm_name st f);
         prerr_newline (); 
         Llvm_analysis.dump_dtree dt);
       Llvm_analysis.dispose_dtree dt);
     (if !Globalstates.gen_llvm_df then
       let df = Llvm_analysis.create_df f in
       (if !Globalstates.print_dtree then 
         prerr_string "fname: "; 
         prerr_string (llvm_name st f);
         prerr_newline (); 
         Llvm_analysis.dump_df df);
       Llvm_analysis.dispose_df df)
   end);

  SlotTracker.incorporate_function st f;
  init_fake_name ();  

  (* debugging output *)
  (if debug then (
    prerr_string (if (is_declaration f)  then "declare " else "define ");
    prerr_string "fname: "; 
    prerr_string (llvm_name st f);
    prerr_string " with ftyp: ";
    prerr_string (string_of_lltype (type_of f));
    prerr_string " with params: ";
    Array.iter
      (fun param ->
            prerr_string (Llvm_pretty_printer.string_of_operand m st param);
            prerr_string ", "
      )
      (params f);
    prerr_newline ())
  );
  
  (* translation *)
  let args = Array.fold_right
      (fun param args' ->
            (translate_operand_to_arg m st param):: args'
      )
      (params f) [] in
  let ft = type_of f in
  let et = element_type ft in
  let rt = return_type et in
  let (rattrs, fattrs) = translate_fun_attrs f in
  let fheader = (LLVMsyntax.Coq_fheader_intro (
    (LLVMsyntax.Coq_fnattrs_intro ((translate_linkage f),
      (translate_visibility f), (int_to_callconv (function_call_conv f)),
       rattrs, fattrs)),
    translate_typ rt, 
    (llvm_name st f), args, translate_var_arg et)) in
  let g =
    if (is_declaration f)
    then
      LLVMsyntax.Coq_product_fdec 
      (LLVMsyntax.Coq_fdec_intro
        (fheader, translate_deckind st f))
    else
      LLVMsyntax.Coq_product_fdef
      (LLVMsyntax.Coq_fdef_intro
        (fheader, fold_right_blocks (translate_block debug m st) f [])) in
  SlotTracker.purge_function st;
  g:: ps

let translate_global debug m st g ps  =
  match (classify_value g) with
  | ValueKind.GlobalVariable ->
      (* debugging output *)
      (if debug then(
        prerr_string (llvm_name st g);
        prerr_string " = ";
        prerr_string (if (is_global_constant g) then "constant " else "global ");
        if (has_initializer g)
        then
          prerr_string (Llvm_pretty_printer.string_of_operand m st 
            (get_initializer g));
        prerr_newline ())
      );
      
      (* translation *)
      if (has_initializer g)
      then
        begin
          if (is_global_constant g)
          then 
             (LLVMsyntax.Coq_product_gvar
              (LLVMsyntax.Coq_gvar_intro
                (llvm_name st g, translate_linkage g,
                 LLVMsyntax.Coq_gvar_spec_constant, 
                 translate_typ (type_of g), translate_constant m st 
                 (get_initializer g), alignment g)
              )
             ):: ps
          else
            (LLVMsyntax.Coq_product_gvar
              (LLVMsyntax.Coq_gvar_intro
                (llvm_name st g, translate_linkage g,
                 LLVMsyntax.Coq_gvar_spec_global, 
                 translate_typ (type_of g), translate_constant m st 
                 (get_initializer g), alignment g)
              )
            ):: ps
        end
      else
        begin
          if (is_global_constant g)
          then 
             (LLVMsyntax.Coq_product_gvar
              (LLVMsyntax.Coq_gvar_external
                (llvm_name st g, LLVMsyntax.Coq_gvar_spec_constant, 
                 translate_typ (type_of g))
              )
             ):: ps
          else
            (LLVMsyntax.Coq_product_gvar
              (LLVMsyntax.Coq_gvar_external
                (llvm_name st g, LLVMsyntax.Coq_gvar_spec_global, 
                 translate_typ (type_of g))
              )
            ):: ps
          end
  | ValueKind.GlobalAlias -> failwith "GlobalAliasVal: Not_Supported"
  | ValueKind.Function -> translate_function debug m st g ps 
  | _ -> failwith "Not_Global"

let translate_layout debug dlt  =
  let tg = Llvm_target.TargetData.create dlt in
  let n = Llvm_target.get_num_alignment tg in
  (* debugging output *)
  (if debug then (
    prerr_string "layouts: ";
    prerr_endline dlt;
    eprintf "byteorde=%s\n"
      (string_of_endian (Llvm_target.byte_order tg));
    eprintf "p size=%s abi=%s pref=%s\n"
      (string_of_int ((Llvm_target.pointer_size_in_bits tg) * 8))
      (string_of_int ((Llvm_target.pointer_abi_alignment tg) * 8))
      (string_of_int ((Llvm_target.pointer_pref_alignment tg) * 8));
    for i = 0 to n - 1 do
      eprintf "typ=%s bitwidth=%s abi=%s pref=%s\n"
        (string_of_aligntype (Llvm_target.get_align_type_enum tg i))
        (string_of_int (Llvm_target.get_type_bitwidth tg i))
        (string_of_int ((Llvm_target.get_abi_align tg i) * 8))
        (string_of_int ((Llvm_target.get_pref_align tg i) * 8));
      flush_all()
    done;
    prerr_endline "Translate ignores Vector_align and Float_align")
  );
  
  (* translation *)
  let rec range b e tg =
    if b < e
    then
      match (Llvm_target.get_align_type_enum tg b) with
      | Llvm_target.AlignType.Integer_align -> 
          LLVMsyntax.Coq_layout_int (Llvm_target.get_type_bitwidth tg b,
                                     (Llvm_target.get_abi_align tg b) * 8,
                                     (Llvm_target.get_pref_align tg b) * 8)::
                                     (range (b + 1) e tg)
      | Llvm_target.AlignType.Vector_align ->
          LLVMsyntax.Coq_layout_vector (Llvm_target.get_type_bitwidth tg b,
                                     (Llvm_target.get_abi_align tg b) * 8,
                                     (Llvm_target.get_pref_align tg b) * 8)::
                                     (range (b + 1) e tg)
      | Llvm_target.AlignType.Float_align -> 
          LLVMsyntax.Coq_layout_float (Llvm_target.get_type_bitwidth tg b,
                                     (Llvm_target.get_abi_align tg b) * 8,
                                     (Llvm_target.get_pref_align tg b) * 8)::
                                     (range (b + 1) e tg)
      | Llvm_target.AlignType.Aggregate_align ->  
          LLVMsyntax.Coq_layout_aggr (Llvm_target.get_type_bitwidth tg b,
                                     (Llvm_target.get_abi_align tg b) * 8,
                                     (Llvm_target.get_pref_align tg b) * 8)::
                                     (range (b + 1) e tg)
      | Llvm_target.AlignType.Stack_align ->  
          LLVMsyntax.Coq_layout_stack (Llvm_target.get_type_bitwidth tg b,
                                     (Llvm_target.get_abi_align tg b) * 8,
                                     (Llvm_target.get_pref_align tg b) * 8)::
                                     (range (b + 1) e tg)
     else
       [] in
  let dl = (match (Llvm_target.byte_order tg) with
           | Llvm_target.Endian.Big -> LLVMsyntax.Coq_layout_be 
           | Llvm_target.Endian.Little -> LLVMsyntax.Coq_layout_le)::
           LLVMsyntax.Coq_layout_ptr (Llvm_target.pointer_size_in_bits tg,
                                      (Llvm_target.pointer_abi_alignment tg) * 8,
                                       (Llvm_target.pointer_pref_alignment tg) *
                                       8)::range 0 n tg in
  Llvm_target.TargetData.dispose tg;
  dl

let translate_named_typ m ty = 
  match classify_type ty with
  | TypeKind.Struct ->
              (Array.fold_right 
                 (fun t ts -> (translate_typ t :: ts)) 
                                (struct_element_types ty)
                                []
                  )
  | _ -> failwith "Named type must be of structure types"

let translate_namedt (debug:bool) (m: llmodule) nt nts =
  (* debugging output *)
  (if debug then Llvm_pretty_printer.travel_namedt m nt); 

    match type_by_name m nt with
  | Some ty -> (nt, translate_named_typ m ty)::nts
  | None -> failwith "Cannot find a named type!"

let translate_module (debug:bool) st (m: llmodule) : LLVMsyntax.coq_module=
  (if debug then prerr_endline "Translate module (LLVM2Coq):");
  let dl = translate_layout debug (data_layout m) in
  let nts = fold_right_named_types (translate_namedt debug m) m [] in
  let ps = (fold_right_functions (translate_function debug m st) m
              (fold_right_globals (translate_global debug m st) m [])) in  
  LLVMsyntax.Coq_module_intro (dl, nts, ps)

