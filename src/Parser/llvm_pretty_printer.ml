open Printf
open Llvm
open Llvm_aux

(** [writeConstantInt] *)
let rec string_of_constant c = 
	match (classify_value c) with
	| ValueTy.UndefValueVal -> "undef"
	| ValueTy.ConstantExprVal -> "ConstantExpr"
	| ValueTy.ConstantAggregateZeroVal -> "string_of_constant v"
	| ValueTy.ConstantIntVal ->
		  if (is_i1_type (type_of c))
			then
				if (Int64.compare (const_int_get_zextvalue c) Int64.zero) == 0 
				then "false"
				else "true"
			else	 
		    APInt.to_string (APInt.const_int_get_value c)
	| ValueTy.ConstantFPVal -> "ConstantFP"
	| ValueTy.ConstantArrayVal -> 
  		let ops = operands c in 
      Array.fold_right (fun c cs -> (string_of_constant c)^" "^cs) ops ""		
	| ValueTy.ConstantStructVal ->
  		let ops = operands c in 
      Array.fold_right (fun c cs -> (string_of_constant c)^" "^cs) ops ""		
	| ValueTy.ConstantVectorVal -> "ConstantVector"
	| ValueTy.ConstantPointerNullVal -> "null"
	| _ -> failwith "Not_Constant"

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

(** See [WriteAsOperandInternal] - used by [string_of_operand], it prints out
    the name of [v] without its type. *)
let string_of_operand_internal st v =
	match (classify_value v) with
	| ValueTy.ArgumentVal -> llvm_name st v
	| ValueTy.BasicBlockVal -> llvm_name st v
	| ValueTy.FunctionVal -> llvm_name st v                  (*GlobalValue*)
	| ValueTy.GlobalAliasVal -> llvm_name st v               (*GlobalValue*)
	| ValueTy.GlobalVariableVal -> llvm_name st v            (*GlobalValue*)
	| ValueTy.UndefValueVal -> string_of_constant v
	| ValueTy.ConstantExprVal -> string_of_constant v
	| ValueTy.ConstantAggregateZeroVal -> string_of_constant v
	| ValueTy.ConstantIntVal -> string_of_constant v
	| ValueTy.ConstantFPVal -> string_of_constant v
	| ValueTy.ConstantArrayVal -> string_of_constant v
	| ValueTy.ConstantStructVal -> string_of_constant v
	| ValueTy.ConstantVectorVal -> string_of_constant v
	| ValueTy.ConstantPointerNullVal -> string_of_constant v
	| ValueTy.MDNodeVal -> "MDNodeVal"
	| ValueTy.MDStringVal -> "MDStringVal"
	| ValueTy.NamedMDNodeVal -> "NamedMDNodeVal"
	| ValueTy.InlineAsmVal -> "InlineAsmVal"
	| ValueTy.PseudoSourceValueVal -> "PseudoSourceValueVal"
	| _ -> llvm_name st v                                    (*Instruction*)

(** See [WriteAsOperand] - Write the name of the specified value out to the specified
    ostream.  This can be useful when you just want to print int %reg126, not
    the whole instruction that generated it. *)
(* optional argument must be followed by at least one non-optional argument,*)
(* at this case, ?(btype = true) cannot be at the end of this argument list. *)		
let string_of_operand ?(btype = true) st v =
  let s =	string_of_operand_internal st v in
	if btype
	then (string_type_of v)^" "^s
	else s

let string_of_operands st i =
	let ops = operands i in
	let n = num_operand i in
	let rec range b e ops =
		if b + 1 < e 
		then
      (string_of_operand st (Array.get ops b))^", "^(range (b+1) e ops) 
		else
      (string_of_operand st (Array.get ops b)) in
	if n == 0 
	then 
		match (classify_instr i) with
	  | InstrOpcode.Ret ->
	    if ReturnInst.is_void i
		  then ""
			else failwith "	Operands_OutOfBound"
		| _ -> ""
	else
		range 0 n ops

let travel_other_instr st i =
  eprintf "  %s = %s %s\n" (llvm_name st i) (string_of_instr_opcode i) (string_of_operands st i);
  flush_all ()
	
let travel_cast_instr st i =
  eprintf "  %s = %s %s to %s\n"
	  (llvm_name st i)
  	(string_of_opcode (classify_instr i))
		(string_of_operand st (operand i 0))
		(string_type_of i);
  flush_all ()

let travel_instr st i =
	match (classify_instr i) with
	| InstrOpcode.Br ->
		  if (BranchInst.is_conditional i)
			then 
			  begin
			    eprintf "  %s = br %s, %s, %s\n"
  				  (llvm_name st i)
  				  (string_of_operand st (BranchInst.get_condition i))
  					(string_of_operand st (value_of_block (BranchInst.get_successor i 0)))
  					(string_of_operand st (value_of_block (BranchInst.get_successor i 1)));
  			  flush_all ()
				end				
			else
				travel_other_instr st i
	| InstrOpcode.Malloc ->
			eprintf "  %s = malloc %s, %s, align %n\n"
				(llvm_name st i)
				(string_of_lltype (AllocationInst.get_allocated_type i))
				(string_of_operand st (AllocationInst.get_array_size i))
				(AllocationInst.get_alignment i);
			flush_all ()
	| InstrOpcode.Alloca ->
			eprintf "  %s = alloca %s, %s, align %n\n"
				(llvm_name st i)
				(string_of_lltype (AllocationInst.get_allocated_type i))
				(string_of_operand st (AllocationInst.get_array_size i))
				(AllocationInst.get_alignment i);
			flush_all ()		
  | InstrOpcode.Load ->
      eprintf "  %s = load %s, align %n\n" 
	  	  (llvm_name st i)  
				(string_of_operands st i) 
				(LoadInst.get_alignment i);
      flush_all ()						
  | InstrOpcode.Store ->
      eprintf "  %s = store %s, align %n\n" 
	  	  (llvm_name st i)  
				(string_of_operands st i) 
				(StoreInst.get_alignment i);
      flush_all ()		
  | InstrOpcode.ICmp ->
      eprintf "  %s = icmp %s %s\n" 
	  	  (llvm_name st i) 
				(string_of_icmp (ICmpInst.get_predicate i))
				(string_of_operands st i);
      flush_all ()						
  | InstrOpcode.FCmp ->
      eprintf "  %s = fcmp %s %s\n" 
	  	  (llvm_name st i)  
				(string_of_fcmp (FCmpInst.get_predicate i))
				(string_of_operands st i);
      flush_all ()						
  | InstrOpcode.Call ->
		  let fv = operand i 0 in
			let fname = llvm_name st fv in
		  let ptyp = type_of fv in
			let ftyp = element_type ptyp in
			let rtyp = return_type ftyp in
			let atyp = " (" ^ (concat2 ", " (
                  Array.map string_of_lltype (param_types ftyp)
                 )) ^ ")" in			
      eprintf "  %s = call %s with rtyp=%s atyp=%s fid=%s\n" 
	  	  (llvm_name st i) 
				(string_of_operands st i)
				(string_of_lltype rtyp) 
				atyp
				fname;
      flush_all ()						     		  			
  | _ ->
      if is_cast_instruction i 
			then travel_cast_instr st i
			else travel_other_instr st i

let travel_block st b =
	prerr_string "label: ";
	prerr_endline (llvm_label st b);
	iter_instrs (travel_instr st) b;
	prerr_newline ()

let travel_function st f =
	SlotTracker.incorporate_function st f;
	prerr_string (if (is_declaration f)	then "declare " else "define "); 
	prerr_string "fname: ";
	prerr_string (llvm_name st f);
	prerr_string " with ftyp: ";
	prerr_string (string_of_lltype (type_of f));
	prerr_string " with params: ";
	Array.iter 
	  (fun param -> 
		  prerr_string (string_of_operand st param); 
			prerr_string ", "
		) 
	  (params f);
	prerr_newline ();
	iter_blocks (travel_block st) f;
	SlotTracker.purge_function st
	
let travel_global st g =
  match (classify_value g) with
	| ValueTy.GlobalVariableVal -> 
	  prerr_string (llvm_name st g);
	  prerr_string " = ";
	  prerr_string (if (is_global_constant g) then  "constant " else "global ");
	  if (has_initializer g)
	  then
	    prerr_string (string_of_operand st (get_initializer g));
	  prerr_newline ()
	| ValueTy.GlobalAliasVal -> dump_value g
	| ValueTy.FunctionVal -> travel_function st g
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

let travel_module st m =
	prerr_endline "Travel LLVM module:";	
	travel_layout (data_layout m);
	iter_globals (travel_global st) m;
	iter_functions (travel_function st) m

