open Llvm_executionengine
open Ssa_def
open LLVMsyntax
open Printf

let coqtype_2_llvmtype (t:LLVMsyntax.typ) : Llvm.lltype = Coq2llvm.translate_typ (Llvm.global_context()) t
let coqbop_2_llvmopcode (op:LLVMsyntax.bop) : Llvm.InstrOpcode.t = Coq2llvm.translate_bop op
let coqfbop_2_llvmopcode (op:LLVMsyntax.fbop) : Llvm.InstrOpcode.t = Coq2llvm.translate_fbop op
let coqtd_2_llvmtd (td:layouts) = Coq2llvm.translate_layouts td
let coqcond_2_llvmicmp (c:cond) : Llvm.Icmp.t = Coq2llvm.translate_icond c
let coqcond_2_llvmfcmp (c:fcond) : Llvm.Fcmp.t = Coq2llvm.translate_fcond c
let getRealName = Coq_pretty_printer.getRealName

let debug = false

module TargetData = struct

  type t = ExecutionEngine.t * Llvm.llmodule

  let getTypeAllocSize (td:t) typ = 
    let (ee, _) = td in
    let ltd = ExecutionEngine.target_data ee in
    Some (Int64.to_int (Llvm_target.get_type_alloc_size ltd (coqtype_2_llvmtype typ)))
		
  let getTypeAllocSizeInBits x y = failwith "undef"
  let _getStructElementOffset x y z = failwith "undef"
  let getStructElementOffset x y z = failwith "undef"
  let getStructElementOffsetInBits x y z = failwith "undef"
  let _getStructElementContainingOffset x y z = failwith "undef"
  let getStructElementContainingOffset x y z = failwith "undef"
  let _getIntAlignmentInfo x = failwith "undef"
  let getIntAlignmentInfo x = failwith "undef"
  let _getPointerAlignmentInfo x = failwith "undef"
  let getPointerAlignmentInfo x = failwith "undef"
  let _getStructAlignmentInfo x = failwith "undef"
  let getStructAlignmentInfo x = failwith "undef"
  let _getPointerSize x = failwith "undef"
  let getPointerSize x = failwith "undef"
  let getPointerSizeInBits x = failwith "undef"
  let getTypeSizeInBits_and_Alignment x = failwith "undef"
  let getListTypeSizeInBits_and_Alignment x = failwith "undef"
  let getAlignment x = failwith "undef"
  let getABITypeAlignment x = failwith "undef"
  let getPrefTypeAlignment x = failwith "undef"
  let getTypeSizeInBits x = failwith "undef"
  let getTypeStoreSize x = failwith "undef"
  let getTypeStoreSizeInBits x = failwith "undef"
  let getStructSizeInBytes x = failwith "undef"
  let getStructSizeInBits x = failwith "undef"
  let getStructAlignment x = failwith "undef"
	let getFloatAlignmentInfo x = failwith "undef"					
		
end	

module GenericValue = struct

  type t = GenericValue.t

  (* useless at runtime *)
  let null = GenericValue.of_null_pointer ()
  let sizeGenericValue x = failwith "sizeGenericValue undef"
  let uninits x = failwith "uninits undef"
  let gv2val x y = failwith "gv2val undef"
  let gv2int x y z = failwith "gv2int undef"
  let gv2ptr x y z = failwith "gv2ptr undef"
  let val2gv x y z = failwith "val2gv undef"
  let ptr2gv x y = failwith "val2gv undef"
  let _zeroconst2GV x y = failwith "_zeroconst2GV undef"
	let _list_typ_zerostruct2GV x y = failwith "_list_typ_zerostruct2GV undef"
	let repeatGV x y = failwith "repeatGV undef"
	let _const2GV x y z = failwith "_const2GV undef"
  let _list_const_arr2GV x y z = failwith "_list_const_arr2GV undef" 
  let _list_const_struct2GV x y z = failwith "_list_const_struct2GV undef" 

  (* used at runtime *)
  let blk2gv (td:TargetData.t) (v:t) = v

  let isZero (td:TargetData.t) (v:t) = GenericValue.as_int v == 0
	
	let rec list_llvalue2list_int (vs:Llvm.llvalue list) : (int list) option =
	match vs with
	| [] -> Some []
	| v::vs' ->		
		if Llvm.is_constantint v
		then
			let i = Int64.to_int (Llvm.APInt.get_sext_value (Llvm.APInt.const_int_get_value v)) in
			match list_llvalue2list_int vs' with
		  | None -> None
			| Some is -> Some (i::is)
		else None 

  let rec const2llvalue (td:TargetData.t) gl (c:const) : Llvm.llvalue option = 
    let ctx = Llvm.global_context() in
    let (ee, mm) = td in
    match c with
    | Coq_const_zeroinitializer _ -> Some (Coq2llvm.translate_constant ctx c)
  	| Coq_const_int (sz, i) -> Some (Coq2llvm.translate_constant ctx c)
    | Coq_const_floatpoint (_, _) -> Some (Coq2llvm.translate_constant ctx c)
  	| Coq_const_undef t -> Some (Coq2llvm.translate_constant ctx c) 
    | Coq_const_null t -> Some (Coq2llvm.translate_constant ctx c) 
    | Coq_const_arr (t, cs) -> Some (Coq2llvm.translate_constant ctx c)  
    | Coq_const_struct cs -> Some (Coq2llvm.translate_constant ctx c)
    | Coq_const_gid (_,id) -> Llvm.lookup_global (getRealName id) mm
  	| Coq_const_truncop (op, c, t) -> 
			(match (const2llvalue td gl c) with
			| Some v -> 
				Some (match op with
			  | Coq_truncop_int -> Llvm.const_trunc v (Coq2llvm.translate_typ ctx t)
				| Coq_truncop_fp -> Llvm.const_fptrunc v (Coq2llvm.translate_typ ctx t))
			| None -> None)
  	| Coq_const_extop (op, c, t) ->   
			(match (const2llvalue td gl c) with
			| Some v -> 
			  Some (match op with
			  | Coq_extop_z -> Llvm.const_zext v (Coq2llvm.translate_typ ctx t)
			  | Coq_extop_s -> Llvm.const_sext v (Coq2llvm.translate_typ ctx t)
			  | Coq_extop_fp -> Llvm.const_fpext v (Coq2llvm.translate_typ ctx t))
			| None -> None)
	  | Coq_const_castop (op, c, t) -> 
			(match (const2llvalue td gl c) with
			| Some v -> 
			  Some (match op with
    	  | LLVMsyntax.Coq_castop_fptoui -> Llvm.const_fptoui v (Coq2llvm.translate_typ ctx t)			
	      | LLVMsyntax.Coq_castop_fptosi -> Llvm.const_fptosi v (Coq2llvm.translate_typ ctx t) 	 
	      | LLVMsyntax.Coq_castop_uitofp -> Llvm.const_uitofp v (Coq2llvm.translate_typ ctx t) 
	      | LLVMsyntax.Coq_castop_sitofp -> Llvm.const_sitofp v (Coq2llvm.translate_typ ctx t) 
        | LLVMsyntax.Coq_castop_ptrtoint -> Llvm.const_ptrtoint v (Coq2llvm.translate_typ ctx t) 
	      | LLVMsyntax.Coq_castop_inttoptr -> Llvm.const_inttoptr v (Coq2llvm.translate_typ ctx t) 
	      | LLVMsyntax.Coq_castop_bitcast -> Llvm.const_bitcast v (Coq2llvm.translate_typ ctx t))
			| None -> None)
    | Coq_const_gep (ib, c, cs) -> 
			(match const2llvalue td gl c, list_const2list_llvalue td gl cs with
			| Some v, Some vs -> 
			  Some (match ib with
			  | true -> Llvm.const_in_bounds_gep v (Array.of_list vs)
			  | false -> Llvm.const_gep v (Array.of_list vs))
			| _, _ -> None)
    |	Coq_const_select (c0, c1, c2) -> 
			(match const2llvalue td gl c0, const2llvalue td gl c1, const2llvalue td gl c2 with
			| Some v0, Some v1, Some v2 ->
				Some (Llvm.const_select v0 v1 v2)
			| _, _, _ -> None) 
    |	Coq_const_icmp (cond, c1, c2) -> 
			(match const2llvalue td gl c1, const2llvalue td gl c2 with
			| Some v1, Some v2 ->
  			Some (Llvm.const_icmp (coqcond_2_llvmicmp cond) v1 v2)
			| _, _ -> None)
    |	Coq_const_fcmp (cond, c1, c2) -> 
			(match const2llvalue td gl c1, const2llvalue td gl c2 with
			| Some v1, Some v2 ->
  		  Some (Llvm.const_fcmp (coqcond_2_llvmfcmp cond) v1 v2)
			| _, _ -> None)
    | Coq_const_extractvalue (c, cs) -> 
			(match const2llvalue td gl c, list_const2list_llvalue td gl cs with
			| Some v, Some vs -> 
				(match list_llvalue2list_int vs with
				| Some is -> Some (Llvm.const_extractvalue v (Array.of_list is))
				| None -> None)
			| _, _ -> None)
    | Coq_const_insertvalue (c1, c2, cs) -> 
			(match const2llvalue td gl c1, const2llvalue td gl c2, list_const2list_llvalue td gl cs with
			| Some v1, Some v2, Some vs -> 
			  (match list_llvalue2list_int vs with
				| Some is -> Some (Llvm.const_insertvalue v1 v2 (Array.of_list is))
				| None -> None)
			| _, _, _ -> None)
    | Coq_const_bop (op, c1, c2) ->	
			(match const2llvalue td gl c1, const2llvalue td gl c2 with
			| Some v1, Some v2 -> 
			  Some (match op with 
			  | LLVMsyntax.Coq_bop_add -> Llvm.const_add v1 v2 			
	      | LLVMsyntax.Coq_bop_sub -> Llvm.const_sub v1 v2
	      | LLVMsyntax.Coq_bop_mul -> Llvm.const_mul v1 v2
	      | LLVMsyntax.Coq_bop_udiv -> Llvm.const_udiv v1 v2
	      | LLVMsyntax.Coq_bop_sdiv -> Llvm.const_sdiv v1 v2
	      | LLVMsyntax.Coq_bop_urem -> Llvm.const_urem v1 v2
	      | LLVMsyntax.Coq_bop_srem -> Llvm.const_srem v1 v2
	      | LLVMsyntax.Coq_bop_shl -> Llvm.const_shl v1 v2
	      | LLVMsyntax.Coq_bop_lshr -> Llvm.const_lshr v1 v2
	      | LLVMsyntax.Coq_bop_ashr -> Llvm.const_ashr v1 v2
	      | LLVMsyntax.Coq_bop_and -> Llvm.const_and v1 v2
	      | LLVMsyntax.Coq_bop_or -> Llvm.const_or v1 v2
	      | LLVMsyntax.Coq_bop_xor -> Llvm.const_xor v1 v2)
			| _, _ -> None)
    | Coq_const_fbop (op, c1, c2) ->	
			(match const2llvalue td gl c1, const2llvalue td gl c2 with
			| Some v1, Some v2 -> 
			  Some (match op with 
			  | LLVMsyntax.Coq_fbop_fadd -> Llvm.const_fadd v1 v2			
	      | LLVMsyntax.Coq_fbop_fsub -> Llvm.const_fsub v1 v2
	      | LLVMsyntax.Coq_fbop_fmul -> Llvm.const_fmul v1 v2
	      | LLVMsyntax.Coq_fbop_fdiv -> Llvm.const_fdiv v1 v2
	      | LLVMsyntax.Coq_fbop_frem -> Llvm.const_frem v1 v2)
			| _, _ -> None)
  and list_const2list_llvalue (td:TargetData.t) gl (cs:list_const) : (Llvm.llvalue list) option =
	  match cs with
    | LLVMsyntax.Cons_list_const (c, cs') -> 
	  	(match const2llvalue td gl c, list_const2list_llvalue td gl cs' with
	  	| Some gv, Some gvs -> Some (gv::gvs)
	  	| _, _ -> None)
	  | LLVMsyntax.Nil_list_const -> Some []

  let const2GV (td:TargetData.t) gl (c:const) : t option =
    let (ee, _) = td in
    match const2llvalue td gl c with
  	| Some v -> Some (ExecutionEngine.get_constant_value v ee)
	  | None -> None
			
  let mgep (td:TargetData.t) (t1:LLVMsyntax.typ) (ma:t) (vidxs:t list) (inbounds:bool) : t option =
    let (ee, _) = td in
    let ltd = ExecutionEngine.target_data ee in
		let gv = GenericValue.gep ltd ma (Llvm.pointer_type (coqtype_2_llvmtype t1)) (Array.of_list vidxs) in
		(if debug then
			eprintf "  Mgep ptr=%s type=%s r=%s\n"
		  (GenericValue.to_string ma) (Coq_pretty_printer.string_of_typ t1) (GenericValue.to_string gv);flush_all());    			
		Some gv

  let extractGenericValue x y z w = failwith "extractGenericValue undef"

  let insertGenericValue x y z a b = failwith "extractGenericValue undef"

  let mbop (td:TargetData.t) (op:LLVMsyntax.bop) (bsz:LLVMsyntax.sz) (gv1:t) (gv2:t) = 
    let gv = (GenericValue.binary_op gv1 gv2 (Llvm.integer_type (Llvm.global_context()) bsz) (coqbop_2_llvmopcode op)) in
    (if debug then
		  eprintf "  M%s i%d gv1=%s gv2=%s r=%s\n" (Coq_pretty_printer.string_of_bop op) bsz 
		  (GenericValue.to_string gv1) (GenericValue.to_string gv2) (GenericValue.to_string gv);flush_all());
		Some gv

  let mfbop (td:TargetData.t) (op:LLVMsyntax.fbop) (fp:LLVMsyntax.floating_point) (gv1:t) (gv2:t) = 
    let gv = (GenericValue.binary_op gv1 gv2 
		            (Coq2llvm.translate_floating_point (Llvm.global_context()) fp) 
								(coqfbop_2_llvmopcode op)) in
    (if debug then
		  eprintf "  M%s %s gv1=%s gv2=%s r=%s\n"
			(Coq_pretty_printer.string_of_fbop op) (Coq_pretty_printer.string_of_floating_point fp)
		  (GenericValue.to_string gv1) (GenericValue.to_string gv2) (GenericValue.to_string gv);flush_all());
		Some gv

	let mcast (td:TargetData.t) (op:LLVMsyntax.castop) (t1:LLVMsyntax.typ) (gv1:t) (t2:LLVMsyntax.typ) =
    let gv =
    (match op with
    | Coq_castop_fptoui -> GenericValue.fptoui gv1 (coqtype_2_llvmtype t1) (coqtype_2_llvmtype t2)
    | Coq_castop_fptosi -> GenericValue.fptosi gv1 (coqtype_2_llvmtype t1) (coqtype_2_llvmtype t2)
    | Coq_castop_uitofp -> GenericValue.uitofp gv1 (coqtype_2_llvmtype t2)
    | Coq_castop_sitofp -> GenericValue.sitofp gv1 (coqtype_2_llvmtype t2)
    | Coq_castop_ptrtoint -> GenericValue.ptrtoint gv1 (coqtype_2_llvmtype t1) (coqtype_2_llvmtype t2)
    | Coq_castop_inttoptr -> let (ee, _) = td in
                             let ltd = ExecutionEngine.target_data ee in
			                       GenericValue.inttoptr ltd gv1 (coqtype_2_llvmtype t2)
    | Coq_castop_bitcast -> GenericValue.bitcast gv1 
                              (coqtype_2_llvmtype t1) 
                              (Llvm.global_context()) 
                              (coqtype_2_llvmtype t2)
    ) in
		(if debug then
      eprintf "  M%s gv1=%s t1=%s t2=%s r=%s\n" (Coq_pretty_printer.string_of_castop op)
			(Coq_pretty_printer.string_of_typ t1) (Coq_pretty_printer.string_of_typ t2)
		  (GenericValue.to_string gv1) (GenericValue.to_string gv);flush_all());
	  Some gv

  let mtrunc (td:TargetData.t) (op:truncop) (t1:typ) (gv1:t) (t2:typ) =
    let gv =
    (match op with
    | Coq_truncop_int -> GenericValue.trunc gv1 (coqtype_2_llvmtype t2) 
    | Coq_truncop_fp -> GenericValue.fptrunc gv1 (coqtype_2_llvmtype t1) (Llvm.global_context()) (coqtype_2_llvmtype t2)
    ) in
		(if debug then
      eprintf "  M%s gv1=%s t1=%s t2=%s r=%s\n" (Coq_pretty_printer.string_of_truncop op)
			(Coq_pretty_printer.string_of_typ t1) (Coq_pretty_printer.string_of_typ t2)
		  (GenericValue.to_string gv1) (GenericValue.to_string gv);flush_all());
	  Some gv

	  let mext (td:TargetData.t) (op:extop) (t1:typ) (gv1:t) (t2:typ) =
    let gv =
    (match op with
    | Coq_extop_z -> GenericValue.zext gv1 (coqtype_2_llvmtype t2)
    | Coq_extop_s -> GenericValue.sext gv1 (coqtype_2_llvmtype t2)
		| Coq_extop_fp -> GenericValue.fpext gv1 (coqtype_2_llvmtype t1) (Llvm.global_context()) (coqtype_2_llvmtype t2)
    ) in
		(if debug then
      eprintf "  M%s gv1=%s t1=%s t2=%s r=%s\n" (Coq_pretty_printer.string_of_extop op)
			(Coq_pretty_printer.string_of_typ t1) (Coq_pretty_printer.string_of_typ t2)
		  (GenericValue.to_string gv1) (GenericValue.to_string gv);flush_all());
	  Some gv

  let micmp (td:TargetData.t) (c:cond) (t:typ) (gv1:t) (gv2:t) =
    let gv = GenericValue.icmp gv1 gv2 (coqtype_2_llvmtype t) (coqcond_2_llvmicmp c) in
		(if debug then 
      eprintf "  Micmp t=%s gv1=%s gv2=%s r=%s\n" (Coq_pretty_printer.string_of_typ t)
		  (GenericValue.to_string gv1) (GenericValue.to_string gv2) (GenericValue.to_string gv);flush_all());
		Some gv

  let mfcmp (td:TargetData.t) (c:fcond) (fp:LLVMsyntax.floating_point) (gv1:t) (gv2:t) =
    let gv = GenericValue.fcmp gv1 gv2 
		           (Coq2llvm.translate_floating_point (Llvm.global_context()) fp) 
							 (coqcond_2_llvmfcmp c) in
		(if debug then 
      eprintf "  Mfcmp t=%s gv1=%s gv2=%s r=%s\n" (Coq_pretty_printer.string_of_floating_point fp)
		  (GenericValue.to_string gv1) (GenericValue.to_string gv2) (GenericValue.to_string gv);flush_all());
		Some gv

	  let dump (gv:t) = GenericValue.dump gv
	let to_string (gv:t) = GenericValue.to_string gv

end

module Mem = struct

  type t = ExecutionEngine.t * Llvm.llmodule

  (* let initmem = failwith "initmem undef" *)

  let malloc (td:TargetData.t) m size (a:LLVMsyntax.align) = 
    let (ee, _) = m in
    match (ExecutionEngine.malloc_memory size ee) with
    | Some gv -> 
    		(if debug then 
					eprintf "  Malloc s=%d a=%d ptr=%s\n" size a (GenericValue.to_string gv);flush_all());				
			  Some (m, gv)
    | None -> 
    		(if debug then eprintf "  Malloc None";flush_all());
			  None

  let free (td:TargetData.t) m ptr =
    let (ee, _) = m in
    let _ = ExecutionEngine.free_memory ptr ee in
    (if debug then 
			eprintf "  Mfree ptr=%s\n" (GenericValue.to_string ptr);flush_all());				
		Some m

  let mload (td:TargetData.t) m ptr t (a:LLVMsyntax.align) =
    let (ee, _) = m in
		let gv = ExecutionEngine.load_value_from_memory ptr (coqtype_2_llvmtype t) ee in
		(if debug then 
			eprintf "  Mload ptr=%s r=%s\n" (GenericValue.to_string ptr) (GenericValue.to_string gv);flush_all());
		Some gv

  let mstore (td:TargetData.t) m ptr t gv (a:LLVMsyntax.align) =
		(if debug then 
			eprintf "  Mstore ptr=%s v=%s\n" (GenericValue.to_string ptr) (GenericValue.to_string gv);flush_all());
		let (ee, _) = m in
    let _ = ExecutionEngine.store_value_to_memory gv ptr (coqtype_2_llvmtype t) ee in
    Some m
		
  let initGlobal (td:TargetData.t) gl m (id0:LLVMsyntax.id) 
                 (t:LLVMsyntax.typ)(c:LLVMsyntax.const)(align0:LLVMsyntax.align) =
    let (ee, mm) = m in
    match Llvm.lookup_global (getRealName id0) mm with
    | Some v -> 
       (match ExecutionEngine.get_pointer_to_global_if_available v ee with
       | Some gv -> Some (gv, m)
       | None -> None)
    | None -> None

  let initTargetData (td:LLVMsyntax.layouts) (m:t) = m

  let callExternalFunction m (fid:LLVMsyntax.id) (args:GenericValue.t list) = 
		(if debug then 
			eprintf "  Mcall external fun=%s\n" fid;flush_all());
		let (ee, mm) = m in
    match Llvm.lookup_function (getRealName fid) mm with
    | Some fv -> (Some (ExecutionEngine.call_external_function fv (Array.of_list args) ee), m)
    | None -> failwith "callExternalFunction: cannot find function"
		
end

