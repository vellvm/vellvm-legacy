open Printf
open Llvm
open Llvm_aux
open Ssa_def
open Ssa_lib

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

let rec translate_floating_point ty = 
  match classify_type ty with
  | TypeKind.Ppc_fp128 -> LLVMsyntax.Coq_fp_ppc_fp128
  | TypeKind.Fp128 -> LLVMsyntax.Coq_fp_fp128
  | TypeKind.X86fp80 -> LLVMsyntax.Coq_fp_x86_fp80
  | TypeKind.Double -> LLVMsyntax.Coq_fp_double
  | TypeKind.Float -> LLVMsyntax.Coq_fp_float
  | _ -> failwith "This is not a floating point" 

let rec translate_typ ty = 
  match classify_type ty with
  | TypeKind.Integer -> LLVMsyntax.Coq_typ_int (integer_bitwidth ty)
  | TypeKind.Pointer -> LLVMsyntax.Coq_typ_pointer (translate_typ (element_type ty))
  | TypeKind.Struct -> LLVMsyntax.Coq_typ_struct
                                (Array.fold_right 
																  (fun t ts -> LLVMsyntax.Cons_list_typ (translate_typ t, ts)) 
																	(struct_element_types ty)
																	LLVMsyntax.Nil_list_typ
																)
  | TypeKind.Array -> LLVMsyntax.Coq_typ_array (array_length ty, translate_typ (element_type ty))
  | TypeKind.Vector -> failwith "Vector: Not_Supported."
  | TypeKind.Opaque -> failwith "Metadata: Not_Supported."
  | TypeKind.Function -> LLVMsyntax.Coq_typ_function 
	                         (translate_typ (return_type ty),
                            (Array.fold_right 
																  (fun t ts -> LLVMsyntax.Cons_list_typ (translate_typ t, ts)) 
																	(param_types ty)
																	LLVMsyntax.Nil_list_typ))
  | TypeKind.Label -> LLVMsyntax.Coq_typ_label
  | TypeKind.Ppc_fp128 -> LLVMsyntax.Coq_typ_floatpoint (translate_floating_point ty)
  | TypeKind.Fp128 -> LLVMsyntax.Coq_typ_floatpoint (translate_floating_point ty)
  | TypeKind.X86fp80 -> LLVMsyntax.Coq_typ_floatpoint (translate_floating_point ty)
  | TypeKind.Double -> LLVMsyntax.Coq_typ_floatpoint (translate_floating_point ty)
  | TypeKind.Float -> LLVMsyntax.Coq_typ_floatpoint (translate_floating_point ty)
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

let rec translate_constant st c = 	
	match (classify_value c) with
	| ValueTy.UndefValueVal -> LLVMsyntax.Coq_const_undef (translate_typ (type_of c)) 
	| ValueTy.ConstantExprVal -> translate_constant_expr st c
	| ValueTy.ConstantAggregateZeroVal -> LLVMsyntax.Coq_const_zeroinitializer (translate_typ (type_of c))
	| ValueTy.ConstantIntVal -> 
		  LLVMsyntax.Coq_const_int (integer_bitwidth
        (type_of c), APInt.const_int_get_value c)
	| ValueTy.ConstantFPVal ->  
		  LLVMsyntax.Coq_const_floatpoint (translate_floating_point (type_of c), APFloat.const_float_get_value c) 
	| ValueTy.ConstantArrayVal -> 
  		let ops = operands c in
  		LLVMsyntax.Coq_const_arr (
				 translate_typ (element_type (type_of c)),
         (Array.fold_right (fun c cs -> LLVMsyntax.Cons_list_const (translate_constant st c, cs)) ops LLVMsyntax.Nil_list_const)
			)
	| ValueTy.ConstantStructVal ->
  		let ops = operands c in
  		LLVMsyntax.Coq_const_struct 
         (Array.fold_right (fun c cs -> LLVMsyntax.Cons_list_const (translate_constant st c, cs)) ops LLVMsyntax.Nil_list_const)
	| ValueTy.ConstantVectorVal -> failwith "ConstantVector: Not_Supported." 
	| ValueTy.ConstantPointerNullVal -> LLVMsyntax.Coq_const_null (translate_typ (type_of c))
	| ValueTy.GlobalVariableVal ->                                                     (*GlobalValue*)
                               (* FIXME: Do we need typ for gid? use typ_void for the time being. *)
															   (LLVMsyntax.Coq_const_gid ((translate_typ (type_of c)), llvm_name st c))
	| ValueTy.FunctionVal ->                                                           (*FunctionVal*)
															   (LLVMsyntax.Coq_const_gid ((translate_typ (type_of c)), llvm_name st c))
	| _ -> failwith (string_of_valuety (classify_value c) ^ " isnt Constant")
and translate_constant_expr st c =
	match (classify_constantexpr c) with
	| InstrOpcode.Ret ->
			failwith "Ret isnt a const expr"
	| InstrOpcode.Br ->
			failwith "Br isnt a const expr"
	| InstrOpcode.Switch ->
			failwith "Switch isnt a const expr"
  | InstrOpcode.Invoke ->			
			failwith "Invoke isnt a const expr"
  | InstrOpcode.Unwind ->
			failwith "Unwind isnt a const expr"
  | InstrOpcode.Unreachable ->
			failwith "Unreachable isnt a const expr"
  | InstrOpcode.Add ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const Add must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_add,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.FAdd ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const FAdd must have 2 operand."
			else
				(LLVMsyntax.Coq_const_fbop
					(LLVMsyntax.Coq_fbop_fadd,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.Sub ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const Sub must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_sub,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.FSub ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const FSub must have 2 operand."
			else
				(LLVMsyntax.Coq_const_fbop
					(LLVMsyntax.Coq_fbop_fsub,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.Mul ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const Mul must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_mul,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.FMul ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const FMul must have 2 operand."
			else
				(LLVMsyntax.Coq_const_fbop
					(LLVMsyntax.Coq_fbop_fmul,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.UDiv ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const UDiv must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_udiv,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.SDiv ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const SDiv must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_sdiv,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.FDiv ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const FDiv must have 2 operand."
			else
				(LLVMsyntax.Coq_const_fbop
					(LLVMsyntax.Coq_fbop_fdiv,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.URem ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const URem must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_urem,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.SRem ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const SRem must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_srem,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.FRem ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const FRem must have 2 operand."
			else
				(LLVMsyntax.Coq_const_fbop
					(LLVMsyntax.Coq_fbop_frem,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.Shl ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const Shl must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_shl,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.LShr ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const LShr must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_lshr,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.AShr ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const AShr must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_ashr,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.And ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const And must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_and,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.Or ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const Or must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_or,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
  | InstrOpcode.Xor ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const XOr must have 2 operand."
			else
				(LLVMsyntax.Coq_const_bop
					(LLVMsyntax.Coq_bop_xor,
					translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1))
				)
	| InstrOpcode.Malloc ->
			failwith "Malloc isnt a const expr"
	| InstrOpcode.Free ->
			failwith "Free isnt a const expr"
	| InstrOpcode.Alloca ->
			failwith "Alloca isnt a const expr"
	| InstrOpcode.Load ->
			failwith "Load isnt a const expr"
	| InstrOpcode.Store ->
			failwith "Store isnt a const expr"
  | InstrOpcode.GetElementPtr ->				
			let n = num_operand c in
			if n < 2
			then failwith "Const GEP must have >=2 operand."
			else
  			let ops = operands c in
   			let n = num_operand c in
	  		let rec range b e ops =
	  			if b < e
	  			then
	  				LLVMsyntax.Cons_list_const (translate_constant st (Array.get ops b), (range (b + 1) e ops))
	  			else
	  				LLVMsyntax.Nil_list_const in
				(LLVMsyntax.Coq_const_gep
					(Llvm.GetElementPtrInst.is_in_bounds c,
					 translate_constant st (Array.get ops 0),
					 range 1 n ops)
				)
  | InstrOpcode.Trunc ->				
			let ops = operands c in
			let n = num_operand c in
			if n != 1
			then failwith "Const Trunc must have 1 operand."
			else
				(LLVMsyntax.Coq_const_truncop
					(LLVMsyntax.Coq_truncop_int,
					translate_constant st (Array.get ops 0),
					translate_typ (type_of c))
				)
  | InstrOpcode.ZExt ->				
			let ops = operands c in
			let n = num_operand c in
			if n != 1
			then failwith "Const ZExt must have 1 operand."
			else
				(LLVMsyntax.Coq_const_extop
					(LLVMsyntax.Coq_extop_z,
					translate_constant st (Array.get ops 0),
					translate_typ (type_of c))
				)
  | InstrOpcode.SExt ->				
			let ops = operands c in
			let n = num_operand c in
			if n != 1
			then failwith "Const SExt must have 1 operand."
			else
				(LLVMsyntax.Coq_const_extop
					(LLVMsyntax.Coq_extop_s,
					translate_constant st (Array.get ops 0),
					translate_typ (type_of c))
				)
  |	InstrOpcode.FPToUI ->
			let ops = operands c in
			let n = num_operand c in
			if n != 1
			then failwith "Const FPToUI must have 1 operand."
			else
				(LLVMsyntax.Coq_const_castop
					(LLVMsyntax.Coq_castop_fptoui,
				  translate_constant st (Array.get ops 0),
					translate_typ (type_of c))
				)	  		
  |	InstrOpcode.FPToSI ->
			let ops = operands c in
			let n = num_operand c in
			if n != 1
			then failwith "Const FPToSI must have 1 operand."
			else
				(LLVMsyntax.Coq_const_castop
					(LLVMsyntax.Coq_castop_fptosi,
				  translate_constant st (Array.get ops 0),
					translate_typ (type_of c))
				)	  		
  |	InstrOpcode.UIToFP ->
			let ops = operands c in
			let n = num_operand c in
			if n != 1
			then failwith "Const UIToFP must have 1 operand."
			else
				(LLVMsyntax.Coq_const_castop
					(LLVMsyntax.Coq_castop_uitofp,
				  translate_constant st (Array.get ops 0),
					translate_typ (type_of c))
				)	  		
  |	InstrOpcode.SIToFP ->
			let ops = operands c in
			let n = num_operand c in
			if n != 1
			then failwith "Const SIToFP must have 1 operand."
			else
				(LLVMsyntax.Coq_const_castop
					(LLVMsyntax.Coq_castop_sitofp,
				  translate_constant st (Array.get ops 0),
					translate_typ (type_of c))
				)	  		
  |	InstrOpcode.FPTrunc ->
			let ops = operands c in
			let n = num_operand c in
			if n != 1
			then failwith "Const FPTrunc must have 1 operand."
			else
				(LLVMsyntax.Coq_const_truncop
					(LLVMsyntax.Coq_truncop_fp,
				  translate_constant st (Array.get ops 0),
					translate_typ (type_of c))
				)	  		
  |	InstrOpcode.FPExt ->
			let ops = operands c in
			let n = num_operand c in
			if n != 1
			then failwith "Const FPExt must have 1 operand."
			else
				(LLVMsyntax.Coq_const_extop
					(LLVMsyntax.Coq_extop_fp,
				  translate_constant st (Array.get ops 0),
					translate_typ (type_of c))
				)	  		
  |	InstrOpcode.PtrToInt ->
			let ops = operands c in
			let n = num_operand c in
			if n != 1
			then failwith "Const PtrToInt must have 1 operand."
			else
				(LLVMsyntax.Coq_const_castop
					(LLVMsyntax.Coq_castop_ptrtoint,
					translate_constant st (Array.get ops 0),
					translate_typ (type_of c))
				)	  		
  |	InstrOpcode.IntToPtr ->
			let ops = operands c in
			let n = num_operand c in
			if n != 1
			then failwith "Const IntToPtr must have 1 operand."
			else
				(LLVMsyntax.Coq_const_castop
					(LLVMsyntax.Coq_castop_inttoptr,
				  translate_constant st (Array.get ops 0),
					translate_typ (type_of c))
				)	  		
  |	InstrOpcode.BitCast ->
			let ops = operands c in
			let n = num_operand c in
			if n != 1
			then failwith "Const BitCast must have 1 operand."
			else
				(LLVMsyntax.Coq_const_castop
					(LLVMsyntax.Coq_castop_bitcast,
					translate_constant st (Array.get ops 0),
					translate_typ (type_of c))
				)	  		
	| InstrOpcode.ICmp ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const ICmp must have 2 operand."
			else
				(LLVMsyntax.Coq_const_icmp
					(translate_icmp (ICmpInst.const_get_predicate c),
					 translate_constant st (Array.get ops 0),
					 translate_constant st (Array.get ops 1))
				)
	| InstrOpcode.FCmp ->
			let ops = operands c in
			let n = num_operand c in
			if n != 2
			then failwith "Const FCmp must have 2 operand."
			else
				(LLVMsyntax.Coq_const_fcmp
					(translate_fcmp (FCmpInst.const_get_predicate c),
					 translate_constant st (Array.get ops 0),
					 translate_constant st (Array.get ops 1))
				)
  |	InstrOpcode.PHI ->
		  failwith "PHI isnt a const expr"
	| InstrOpcode.Call ->
		  failwith "Call isnt a const expr"
  | InstrOpcode.Select ->			
			let ops = operands c in
			let n = num_operand c in
			if n != 3
			then failwith "Const Select must have 3 operand."
			else
				(LLVMsyntax.Coq_const_select
					(translate_constant st (Array.get ops 0),
					translate_constant st (Array.get ops 1),
					translate_constant st (Array.get ops 2))
				)	  		
  | InstrOpcode.UserOp1 ->			
			failwith "UserOp1 isnt a const expr"
  | InstrOpcode.UserOp2 ->			
			failwith "UserOp2 isnt a const expr"
  | InstrOpcode.VAArg ->			
			failwith "VAArg isnt a const expr"
  | InstrOpcode.ExtractElement ->			
			failwith "Const ExtractElement: Not_Supported"
  | InstrOpcode.InsertElement ->			
			failwith "Const InsertElement: Not_Supported"
  | InstrOpcode.ShuffleVector ->			
			failwith "Sont ShuffleVector: Not_Supported"
  | InstrOpcode.ExtractValue ->			
			let ops = operands c in
			let n = num_operand c in
			if n < 2
			then failwith "Const ExtractValue must have >=2 operand."
			else
	  		let rec range b e ops =
	  			if b < e
	  			then
	  				LLVMsyntax.Cons_list_const (translate_constant st (Array.get ops b), (range (b + 1) e ops))
	  			else
	  				LLVMsyntax.Nil_list_const in
				(LLVMsyntax.Coq_const_extractvalue
					(translate_constant st (Array.get ops 0),
					 range 1 n ops)
				)
  | InstrOpcode.InsertValue ->			
			let ops = operands c in
			let n = num_operand c in
			if n < 3
			then failwith "Const InsertValue must have >=3 operand."
			else
	  		let rec range b e ops =
	  			if b < e
	  			then
	  				LLVMsyntax.Cons_list_const (translate_constant st (Array.get ops b), (range (b + 1) e ops))
	  			else
	  				LLVMsyntax.Nil_list_const in
				(LLVMsyntax.Coq_const_insertvalue
					(translate_constant st (Array.get ops 0),
				   translate_constant st (Array.get ops 1),
					 range 2 n ops)
				)

let translate_operand_to_value st v = 
	match (classify_value v) with
	| ValueTy.ArgumentVal -> LLVMsyntax.Coq_value_id (llvm_name st v)
	| ValueTy.BasicBlockVal -> LLVMsyntax.Coq_value_id (llvm_name st v)
	| ValueTy.FunctionVal ->                                                           (*FunctionVal*)
										           LLVMsyntax.Coq_value_const 
															   (LLVMsyntax.Coq_const_gid (translate_typ (type_of v), llvm_name st v))
	| ValueTy.GlobalAliasVal -> LLVMsyntax.Coq_value_id (llvm_name st v)               (*GlobalValue*)
	| ValueTy.GlobalVariableVal ->                                                     (*GlobalValue*)
										           LLVMsyntax.Coq_value_const 
															   (LLVMsyntax.Coq_const_gid (translate_typ (type_of v), llvm_name st v))
	| ValueTy.UndefValueVal -> LLVMsyntax.Coq_value_const (translate_constant st v)
	| ValueTy.ConstantExprVal -> LLVMsyntax.Coq_value_const (translate_constant st v)
	| ValueTy.ConstantAggregateZeroVal -> LLVMsyntax.Coq_value_const (translate_constant st v)
	| ValueTy.ConstantIntVal -> LLVMsyntax.Coq_value_const (translate_constant st v)
	| ValueTy.ConstantFPVal -> LLVMsyntax.Coq_value_const (translate_constant st v)
	| ValueTy.ConstantArrayVal -> LLVMsyntax.Coq_value_const (translate_constant st v)
	| ValueTy.ConstantStructVal -> LLVMsyntax.Coq_value_const (translate_constant st v)
	| ValueTy.ConstantVectorVal -> LLVMsyntax.Coq_value_const (translate_constant st v)
	| ValueTy.ConstantPointerNullVal -> LLVMsyntax.Coq_value_const (translate_constant st v)
	| ValueTy.MDNodeVal -> failwith "MDNodeVal: Not_Supported."
	| ValueTy.MDStringVal -> failwith "MDStringVal: Not_Supported."
	| ValueTy.NamedMDNodeVal -> failwith "NamedMDNodeVal: Not_Supported."
	| ValueTy.InlineAsmVal -> failwith "InlineAsmVal: Not_Supported."
	| ValueTy.PseudoSourceValueVal -> failwith "PseudoSourceValueVal: Not_Supported."
	| _ -> LLVMsyntax.Coq_value_id (llvm_name st v)                                   (*Instruction*)

let translate_operand_to_arg st v = (translate_typ (type_of v), llvm_name st v)

let translate_operand_to_param st v = (translate_typ (type_of v), translate_operand_to_value st v)

let array_size_to_int c =
	match (classify_value c) with
	| ValueTy.ConstantIntVal -> 
		  if integer_bitwidth (type_of c) != 32
			then
				failwith "array_size must be with type i32"
			else
				Int64.to_int (Llvm.APInt.get_zext_value
                                (Llvm.APInt.const_int_get_value c))			 
	| _ -> failwith (string_of_valuety (classify_value c) ^ ": array_size must be ConstantIntVal")

let translate_instr debug st i  =
	(* debugging output *)
	(if debug then Llvm_pretty_printer.travel_instr st i); 
	
	match (classify_instr i) with
	| InstrOpcode.Ret ->
			begin
				if ReturnInst.is_void i
				then
						LLVMsyntax.Coq_insn_terminator
						(LLVMsyntax.Coq_insn_return_void
							(llvm_name st i)
						)
				else
						let ops = operands i in
						let n = num_operand i in
						if n != 1
						then failwith "Ret must have 1 operand."
						else
							LLVMsyntax.Coq_insn_terminator
							(LLVMsyntax.Coq_insn_return
								(llvm_name st i,
								translate_typ (type_of (Array.get ops 0)),
								translate_operand_to_value st (Array.get ops 0))
							)
			end
	| InstrOpcode.Br ->
			if (BranchInst.is_conditional i)
			then
				LLVMsyntax.Coq_insn_terminator (
					LLVMsyntax.Coq_insn_br
					(llvm_name st i,
					translate_operand_to_value st (BranchInst.get_condition i),
					llvm_label st (BranchInst.get_successor i 0),
					llvm_label st (BranchInst.get_successor i 1))
				)
			else
				LLVMsyntax.Coq_insn_terminator (
					LLVMsyntax.Coq_insn_br_uncond
					(llvm_name st i,
					llvm_label st (BranchInst.get_successor i 0))
				)
	| InstrOpcode.Switch ->
			failwith "Switch: Not_Supported"
  | InstrOpcode.Invoke ->			
			failwith "Invoke: Not_Supported"
  | InstrOpcode.Unwind ->
			failwith "Unwind: Not_Supported"
  | InstrOpcode.Unreachable ->
	    LLVMsyntax.Coq_insn_terminator (LLVMsyntax.Coq_insn_unreachable (llvm_name st i))
  | InstrOpcode.Add ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "Add must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_add,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.FAdd ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "FAdd must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_fbop
					(llvm_name st i,
					LLVMsyntax.Coq_fbop_fadd,
					(translate_floating_point (type_of i)),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.Sub ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "Sub must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_sub,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.FSub ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "FSub must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_fbop
					(llvm_name st i,
					LLVMsyntax.Coq_fbop_fsub,
					(translate_floating_point (type_of i)),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.Mul ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "Mul must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_mul,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.FMul ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "FMul must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_fbop
					(llvm_name st i,
					LLVMsyntax.Coq_fbop_fmul,
					(translate_floating_point (type_of i)),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.UDiv ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "UDiv must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_udiv,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.SDiv ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "SDiv must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_sdiv,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.FDiv ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "FDiv must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_fbop
					(llvm_name st i,
					LLVMsyntax.Coq_fbop_fdiv,
					(translate_floating_point (type_of i)),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.URem ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "URem must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_urem,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.SRem ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "SRem must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_srem,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.FRem ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "FRem must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_fbop
					(llvm_name st i,
					LLVMsyntax.Coq_fbop_frem,
					(translate_floating_point (type_of i)),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.Shl ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "Shl must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_shl,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.LShr ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "LShr must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_lshr,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.AShr ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "AShr must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_ashr,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.And ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "And must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_and,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.Or ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "Or must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_or,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
  | InstrOpcode.Xor ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "Xor must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_bop
					(llvm_name st i,
					LLVMsyntax.Coq_bop_xor,
					integer_bitwidth (type_of i),
					translate_operand_to_value st (Array.get ops 0),
					translate_operand_to_value st (Array.get ops 1))
				)
	| InstrOpcode.Malloc ->
			LLVMsyntax.Coq_insn_cmd
			(LLVMsyntax.Coq_insn_malloc
				(llvm_name st i,
					translate_typ (AllocationInst.get_allocated_type i),
					array_size_to_int (AllocationInst.get_array_size i),
					(AllocationInst.get_alignment i))
			)
	| InstrOpcode.Free ->
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "Free must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_free
					(llvm_name st i,
						translate_typ (type_of (Array.get ops 0)),
						translate_operand_to_value st (Array.get ops 0))
				)
	| InstrOpcode.Alloca ->
			LLVMsyntax.Coq_insn_cmd
			(LLVMsyntax.Coq_insn_alloca
				(llvm_name st i,
					translate_typ (AllocationInst.get_allocated_type i),
					array_size_to_int (AllocationInst.get_array_size i),
					(AllocationInst.get_alignment i))
			)
	| InstrOpcode.Load ->
			let ops = operands i in
			let n = num_operand i in
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
    						translate_operand_to_value st (Array.get ops 0),
		    				LoadInst.get_alignment i)
				    )
					| _ -> failwith "Load must be with ptr type"
				end
	| InstrOpcode.Store ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "Store must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_store
					(llvm_name st i,
						translate_typ (type_of (Array.get ops 0)),
						translate_operand_to_value st (Array.get ops 0),
						translate_operand_to_value st (Array.get ops 1),
						StoreInst.get_alignment i)
				)
  | InstrOpcode.GetElementPtr ->				
			let n = num_operand i in
			if n < 2
			then failwith "GEP must have >=2 operand."
			else
  			let ops = operands i in
   			let n = num_operand i in
	  		let rec range b e ops =
	  			if b < e
	  			then
	  				LLVMsyntax.Cons_list_value (translate_operand_to_value st (Array.get ops b), (range (b + 1) e ops))
	  			else
	  				LLVMsyntax.Nil_list_value in
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_gep
					(llvm_name st i,
					 Llvm.GetElementPtrInst.is_in_bounds i,
					 translate_typ (Llvm.element_type (type_of (Array.get ops 0))),  (* returns the elt typ of the 1st op's pointer typ *)
					 translate_operand_to_value st (Array.get ops 0),
					 range 1 n ops)
				)
  | InstrOpcode.Trunc ->				
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "Trunc must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_trunc
					(llvm_name st i,
					LLVMsyntax.Coq_truncop_int,
				  translate_typ (type_of (Array.get ops 0)),
					translate_operand_to_value st (Array.get ops 0),
					translate_typ (type_of i))
				)
  | InstrOpcode.ZExt ->				
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "ZExt must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_ext
					(llvm_name st i,
					LLVMsyntax.Coq_extop_z,
				  translate_typ (type_of (Array.get ops 0)),
					translate_operand_to_value st (Array.get ops 0),
					translate_typ (type_of i))
				)
  | InstrOpcode.SExt ->				
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "SExt must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_ext
					(llvm_name st i,
					LLVMsyntax.Coq_extop_s,
				  translate_typ (type_of (Array.get ops 0)),
					translate_operand_to_value st (Array.get ops 0),
					translate_typ (type_of i))
				)
  |	InstrOpcode.FPToUI ->
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "FPToUI must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_cast
					(llvm_name st i,
					LLVMsyntax.Coq_castop_fptoui,
				  translate_typ (type_of (Array.get ops 0)),
					translate_operand_to_value st (Array.get ops 0),
					translate_typ (type_of i))
				)	  		
  |	InstrOpcode.FPToSI ->
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "FPToSI must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_cast
					(llvm_name st i,
					LLVMsyntax.Coq_castop_fptosi,
				  translate_typ (type_of (Array.get ops 0)),
					translate_operand_to_value st (Array.get ops 0),
					translate_typ (type_of i))
				)	  		
  |	InstrOpcode.UIToFP ->
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "UIToFP must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_cast
					(llvm_name st i,
					LLVMsyntax.Coq_castop_uitofp,
				  translate_typ (type_of (Array.get ops 0)),
					translate_operand_to_value st (Array.get ops 0),
					translate_typ (type_of i))
				)	  		
  |	InstrOpcode.SIToFP ->
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "SIToFP must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_cast
					(llvm_name st i,
					LLVMsyntax.Coq_castop_sitofp,
				  translate_typ (type_of (Array.get ops 0)),
					translate_operand_to_value st (Array.get ops 0),
					translate_typ (type_of i))
				)	  		
  |	InstrOpcode.FPTrunc ->
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "FPTrunc must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_trunc
					(llvm_name st i,
					LLVMsyntax.Coq_truncop_fp,
				  translate_typ (type_of (Array.get ops 0)),
					translate_operand_to_value st (Array.get ops 0),
					translate_typ (type_of i))
				)
  |	InstrOpcode.FPExt ->
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "FPExt must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_ext
					(llvm_name st i,
					LLVMsyntax.Coq_extop_fp,
				  translate_typ (type_of (Array.get ops 0)),
					translate_operand_to_value st (Array.get ops 0),
					translate_typ (type_of i))
				)
  |	InstrOpcode.PtrToInt ->
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "PtrToInt must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_cast
					(llvm_name st i,
					LLVMsyntax.Coq_castop_ptrtoint,
				  translate_typ (type_of (Array.get ops 0)),
					translate_operand_to_value st (Array.get ops 0),
					translate_typ (type_of i))
				)	  		
  |	InstrOpcode.IntToPtr ->
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "IntToPtr must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_cast
					(llvm_name st i,
					LLVMsyntax.Coq_castop_inttoptr,
				  translate_typ (type_of (Array.get ops 0)),
					translate_operand_to_value st (Array.get ops 0),
					translate_typ (type_of i))
				)	  		
  |	InstrOpcode.BitCast ->
			let ops = operands i in
			let n = num_operand i in
			if n != 1
			then failwith "BitCast must have 1 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_cast
					(llvm_name st i,
					LLVMsyntax.Coq_castop_bitcast,
				  translate_typ (type_of (Array.get ops 0)),
					translate_operand_to_value st (Array.get ops 0),
					translate_typ (type_of i))
				)	  		
	| InstrOpcode.ICmp ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "ICmp must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_icmp
					(llvm_name st i,
						translate_icmp (ICmpInst.get_predicate i),
						translate_typ (type_of (Array.get ops 0)),
						translate_operand_to_value st (Array.get ops 0),
						translate_operand_to_value st (Array.get ops 1))
				)
	| InstrOpcode.FCmp ->
			let ops = operands i in
			let n = num_operand i in
			if n != 2
			then failwith "FCmp must have 2 operand."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_fcmp
					(llvm_name st i,
						translate_fcmp (FCmpInst.get_predicate i),
						translate_floating_point (type_of (Array.get ops 0)),
						translate_operand_to_value st (Array.get ops 0),
						translate_operand_to_value st (Array.get ops 1))
				)
  |	InstrOpcode.PHI ->
			let v_l_list = incoming i in
			let n = num_operand i in
			if n < 2
			then failwith "GEP must have >=2 operand."
			else
				LLVMsyntax.Coq_insn_phinode
				(LLVMsyntax.Coq_insn_phi
					(llvm_name st i,
					 translate_typ (type_of i),
					 (List.fold_right					
					   (fun (v, l) v_l_list ->
							  LLVMsyntax.Cons_list_value_l (translate_operand_to_value st v, llvm_label st l, v_l_list)
						 )
						 v_l_list
						 LLVMsyntax.Nil_list_value_l 
					 ))
				)
	| InstrOpcode.Call ->
			let ops = operands i in
			let n = num_operand i in
			(if n <=0 then failwith "Call must have more than 1 operand.");
			let fv = operand i 0 in
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
					translate_operand_to_param st (Array.get ops b):: (range (b + 1) e ops)
				else
					[] in
			LLVMsyntax.Coq_insn_cmd
			(LLVMsyntax.Coq_insn_call
				(llvm_name st i,
					noret,
					tailc,
					translate_typ rtyp,
					translate_operand_to_value st fv,
					range 1 n ops)
			)
  | InstrOpcode.Select ->			
			let ops = operands i in
			let n = num_operand i in
			if n != 3
			then failwith "Select must have 3 operands."
			else
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_select
					(llvm_name st i,
					translate_operand_to_value st (Array.get ops 0),
				  translate_typ (type_of (Array.get ops 1)),
					translate_operand_to_value st (Array.get ops 1),
					translate_operand_to_value st (Array.get ops 2))
				)	  		
  | InstrOpcode.UserOp1 ->			
			failwith "UserOp1: Not_Supported"
  | InstrOpcode.UserOp2 ->			
			failwith "UserOp2: Not_Supported"
  | InstrOpcode.VAArg ->			
			failwith "VAArg: Not_Supported"
  | InstrOpcode.ExtractElement ->			
			failwith "ExtractElement: Not_Supported"
  | InstrOpcode.InsertElement ->			
			failwith "InsertElement: Not_Supported"
  | InstrOpcode.ShuffleVector ->			
			failwith "ShuffleVector: Not_Supported"
  | InstrOpcode.ExtractValue ->			
			let ops = operands i in
			let n = num_operand i in
			if n < 2
			then failwith "ExtractValue must have >=2 operand."
			else
	  		let rec range b e ops =
	  			if b < e
	  			then
	  				LLVMsyntax.Cons_list_const (translate_constant st (Array.get ops b), (range (b + 1) e ops))
	  			else
	  				LLVMsyntax.Nil_list_const in
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_extractvalue
					(llvm_name st i,
				   translate_typ (type_of (Array.get ops 0)),
					 translate_operand_to_value st (Array.get ops 0),
					 range 1 n ops)
				)
  | InstrOpcode.InsertValue ->			
			let ops = operands i in
			let n = num_operand i in
			if n < 3
			then failwith "InsertValue must have >=3 operand."
			else
	  		let rec range b e ops =
	  			if b < e
	  			then
	  				LLVMsyntax.Cons_list_const (translate_constant st (Array.get ops b), (range (b + 1) e ops))
	  			else
	  				LLVMsyntax.Nil_list_const in
				LLVMsyntax.Coq_insn_cmd
				(LLVMsyntax.Coq_insn_insertvalue
					(llvm_name st i,
				   translate_typ (type_of (Array.get ops 0)),
					 translate_operand_to_value st (Array.get ops 0),
				   translate_typ (type_of (Array.get ops 1)),
					 translate_operand_to_value st (Array.get ops 1),
					 range 2 n ops)
				)

let translate_block debug st b bs =
	(* debugging output *)
	(if debug then
		(prerr_string "label: ";
	  prerr_endline (llvm_label st b);
	  prerr_newline ()));
	
	(* translation *)
	let ((ps, cs, otmn): LLVMsyntax.phinodes * LLVMsyntax.cmds * LLVMsyntax.terminator option) =
		fold_right_instrs
			(fun instr ((ps', cs', otmn'): LLVMsyntax.phinodes * LLVMsyntax.cmds * LLVMsyntax.terminator option) ->
						let i = translate_instr debug st instr in
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
			(LLVMsyntax.Coq_block_intro ((llvm_label st b), ps, cs, tmn)):: bs
	| None -> failwith "There is not a Tmn at the end of the block."

let translate_fun_typ t =
	match translate_typ t with
		| LLVMsyntax.Coq_typ_pointer (LLVMsyntax.Coq_typ_function (rt, ts)) -> rt
		| _ -> failwith "Ill-formed function typ"

let translate_function debug st f ps =
	SlotTracker.incorporate_function st f;
	
	(* debugging output *)
	(if debug then (
	  prerr_string (if (is_declaration f)	then "declare " else "define ");
  	prerr_string "fname: "; 
	  prerr_string (llvm_name st f);
	  prerr_string " with ftyp: ";
	  prerr_string (string_of_lltype (type_of f));
  	prerr_string " with params: ";
  	Array.iter
	  	(fun param ->
	  				prerr_string (Llvm_pretty_printer.string_of_operand st param);
	  				prerr_string ", "
	  	)
	  	(params f);
	  prerr_newline ())
	);
	
	(* translation *)
	let args = Array.fold_right
			(fun param args' ->
						(translate_operand_to_arg st param):: args'
			)
			(params f) [] in
	let fheader = (LLVMsyntax.Coq_fheader_intro (translate_fun_typ (type_of f), (llvm_name st f), args)) in
	let g =
		if (is_declaration f)
		then
			LLVMsyntax.Coq_product_fdec fheader
		else
			LLVMsyntax.Coq_product_fdef
			(LLVMsyntax.Coq_fdef_intro
				(fheader, fold_right_blocks (translate_block debug st) f [])) in
	SlotTracker.purge_function st;
	g:: ps

let translate_global debug st g ps  =
	match (classify_value g) with
	| ValueTy.GlobalVariableVal ->
	    (* debugging output *)
			(if debug then(
			  prerr_string (llvm_name st g);
			  prerr_string " = ";
		  	prerr_string (if (is_global_constant g) then "constant " else "global ");
		  	if (has_initializer g)
		  	then
			  	prerr_string (Llvm_pretty_printer.string_of_operand st (get_initializer g));
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
  	  					(llvm_name st g, LLVMsyntax.Coq_gvar_spec_constant, translate_typ (type_of g), translate_constant st (get_initializer g), alignment g)
  	  				)
  	   			):: ps
  				else
    				(LLVMsyntax.Coq_product_gvar
    					(LLVMsyntax.Coq_gvar_intro
    						(llvm_name st g, LLVMsyntax.Coq_gvar_spec_global, translate_typ (type_of g), translate_constant st (get_initializer g), alignment g)
  	  				)
    				):: ps
				end
			else
				begin
    		  if (is_global_constant g)
  			  then 
  	   			(LLVMsyntax.Coq_product_gvar
  	  				(LLVMsyntax.Coq_gvar_external
  	  					(llvm_name st g, LLVMsyntax.Coq_gvar_spec_constant, translate_typ (type_of g))
  	  				)
  	   			):: ps
  				else
    				(LLVMsyntax.Coq_product_gvar
    					(LLVMsyntax.Coq_gvar_external
    						(llvm_name st g, LLVMsyntax.Coq_gvar_spec_global, translate_typ (type_of g))
    					)
    				):: ps
	        end
	| ValueTy.GlobalAliasVal -> failwith "GlobalAliasVal: Not_Supported"
	| ValueTy.FunctionVal -> translate_function debug st g ps 
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
																		 (Llvm_target.get_pref_align tg b) * 8)::(range (b + 1) e tg)
			| Llvm_target.AlignType.Vector_align -> (range (b + 1) e tg)
			| Llvm_target.AlignType.Float_align -> (range (b + 1) e tg)
			| Llvm_target.AlignType.Aggregate_align ->	
			    LLVMsyntax.Coq_layout_aggr (Llvm_target.get_type_bitwidth tg b,
					                           (Llvm_target.get_abi_align tg b) * 8,
																		 (Llvm_target.get_pref_align tg b) * 8)::(range (b + 1) e tg)
			| Llvm_target.AlignType.Stack_align ->	
			    LLVMsyntax.Coq_layout_stack (Llvm_target.get_type_bitwidth tg b,
					                           (Llvm_target.get_abi_align tg b) * 8,
																		 (Llvm_target.get_pref_align tg b) * 8)::(range (b + 1) e tg)
	 	else
	 		[] in
	let dl = (match (Llvm_target.byte_order tg) with
		       | Llvm_target.Endian.Big -> LLVMsyntax.Coq_layout_be 
					 | Llvm_target.Endian.Little -> LLVMsyntax.Coq_layout_le)::
		       LLVMsyntax.Coq_layout_ptr (Llvm_target.pointer_size_in_bits tg,
			  		                          (Llvm_target.pointer_abi_alignment tg) * 8,
				  				     							  (Llvm_target.pointer_pref_alignment tg) * 8)::range 0 n tg in
	Llvm_target.TargetData.dispose tg;
	dl

let translate_module (debug:bool) st (m: llmodule) : LLVMsyntax.coq_module=
	(if debug then prerr_endline "Translate module (LLVM2Coq):");
	let dl = translate_layout debug (data_layout m) in
	let ps = (fold_right_functions (translate_function debug st) m
				      (fold_right_globals (translate_global debug st) m [])) in  
	LLVMsyntax.Coq_module_intro (dl, ps)

