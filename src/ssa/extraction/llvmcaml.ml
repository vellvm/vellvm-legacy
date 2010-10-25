open Llvm_executionengine
open Ssa_def
open LLVMsyntax
open Printf

let coqtype_2_llvmtype (t:LLVMsyntax.typ) : Llvm.lltype = Coq2llvm.translate_typ (Llvm.global_context()) t
let coqbop_2_llvmopcode (op:LLVMsyntax.bop) : Llvm.InstrOpcode.t = Coq2llvm.translate_bop op
let coqtd_2_llvmtd (td:layouts) = Coq2llvm.translate_layouts td
let coqcond_2_llvmicmp (c:cond) : Llvm.Icmp.t = Coq2llvm.translate_icond c

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
  let _const2GV x y z = failwith "_const2GV undef"
  let _list_const_arr2GV x y z = failwith "_list_const_arr2GV undef" 
  let _list_const_struct2GV x y z = failwith "_list_const_struct2GV undef" 

  (* used at runtime *)
  let blk2gv (td:TargetData.t) (v:t) = v

  let isZero (td:TargetData.t) (v:t) = GenericValue.as_int v == 0

  let const2GV (td:TargetData.t) gl (c:const) : t option = 
    let ctx = Llvm.global_context() in
    let (ee, _) = td in
    let ltd = ExecutionEngine.target_data ee in
    match c with
    | Coq_const_int (sz, i) -> Some (GenericValue.of_constant ltd (Coq2llvm.translate_constant ctx c))
    | Coq_const_undef t -> Some (GenericValue.of_constant ltd (Coq2llvm.translate_constant ctx c)) 
    | Coq_const_null t -> Some (GenericValue.of_constant ltd (Coq2llvm.translate_constant ctx c)) 
    | Coq_const_arr (t, cs) -> Some (GenericValue.of_constant ltd (Coq2llvm.translate_constant ctx c))  
    | Coq_const_struct cs -> Some (GenericValue.of_constant ltd (Coq2llvm.translate_constant ctx c))
    | Coq_const_gid (_,id) -> Assoclist.lookupAL gl id

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
		  eprintf "  Mbop s=%d gv1=%s gv2=%s r=%s\n" bsz 
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
      eprintf "  Mcast gv1=%s r=%s\n"
		  (GenericValue.to_string gv1) (GenericValue.to_string gv);flush_all());
	  Some gv

  let mext (td:TargetData.t) (op:extop) (t1:typ) (gv1:t) (t2:typ) =
    let gv =
    (match op with
    | Coq_extop_z -> GenericValue.zext gv1 (coqtype_2_llvmtype t2)
    | Coq_extop_s -> GenericValue.sext gv1 (coqtype_2_llvmtype t2)
    ) in
		(if debug then
      eprintf "  Mext gv1=%s r=%s\n"
		  (GenericValue.to_string gv1) (GenericValue.to_string gv);flush_all());
	  Some gv

  let micmp (td:TargetData.t) (c:cond) (t:typ) (gv1:t) (gv2:t) =
    let gv = GenericValue.icmp gv1 gv2 (coqtype_2_llvmtype t) (coqcond_2_llvmicmp c) in
		(if debug then 
      eprintf "  Micmp t=%s gv1=%s gv2=%s r=%s\n" (Coq_pretty_printer.string_of_typ t)
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
		
	let getRealName (id:LLVMsyntax.id) =
	  if String.length id <= 1
	  then id
	  else 
	  	if String.get id 0 = '@' or String.get id 0 = '%'
  		then String.sub id 1 (String.length id-1)
  		else id

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

