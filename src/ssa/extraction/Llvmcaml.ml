open Llvm_executionengine
open Ssa_def
open LLVMsyntax

let coqtype_2_llvmtype (t:LLVMsyntax.typ) : Llvm.lltype = failwith "undef"
let coqbop_2_llvmopcode (op:LLVMsyntax.bop) : Llvm.InstrOpcode.t = failwith "undef"
let coqtd_2_llvmtd (td:layouts) : Llvm_target.TargetData.t = failwith "undef"
let coqcond_2_llvmicmp (c:cond) : Llvm.Icmp.t = failwith "undef"

module GenericValue = struct

  type t = GenericValue.t

  (* useless at runtime *)
  let null = failwith "undef"
  let sizeGenericValue x = failwith "undef"
  let uninits x = failwith "undef"
  let gv2val x y = failwith "undef"
  let gv2int x y z = failwith "undef"
  let gv2ptr x y z = failwith "undef"
  let val2gv x y z = failwith "undef"
  let ptr2gv x y = failwith "undef"
  let _const2GV x y z = failwith "undef"
  let _list_const_arr2GV x y z = failwith "undef" 
  let _list_const_struct2GV x y z = failwith "undef" 

  (* used at runtime *)
  let blk2gv (td:LLVMsyntax.layouts) (v:t) = v

  let isZero (td:LLVMsyntax.layouts) (v:t) = GenericValue.as_int v == 0

  let const2GV (td:LLVMsyntax.layouts) gl (c:LLVMsyntax.const) : t option = 
    failwith "undef"

  let mgep x y z w = failwith "undef"

  let extractGenericValue x y z w = failwith "undef"

  let insertGenericValue x y z a b = failwith "undef"

  let mbop (td:LLVMsyntax.layouts) (op:LLVMsyntax.bop) (bsz:LLVMsyntax.sz) (gv1:t) (gv2:t) = 
    Some (GenericValue.binary_op gv1 gv2 (Llvm.integer_type (Llvm.global_context()) bsz) (coqbop_2_llvmopcode op))

  let mcast (td:LLVMsyntax.layouts) (op:LLVMsyntax.castop) (t1:LLVMsyntax.typ) (gv1:t) (t2:LLVMsyntax.typ) =
  Some(
  match op with
    | Coq_castop_fptoui -> GenericValue.fptoui gv1 (coqtype_2_llvmtype t1) (coqtype_2_llvmtype t2)
    | Coq_castop_fptosi -> GenericValue.fptosi gv1 (coqtype_2_llvmtype t1) (coqtype_2_llvmtype t2)
    | Coq_castop_uitofp -> GenericValue.uitofp gv1 (coqtype_2_llvmtype t2)
    | Coq_castop_sitofp -> GenericValue.sitofp gv1 (coqtype_2_llvmtype t2)
    | Coq_castop_ptrtoint -> GenericValue.ptrtoint gv1 (coqtype_2_llvmtype t1) (coqtype_2_llvmtype t2)
    | Coq_castop_inttoptr -> GenericValue.inttoptr (coqtd_2_llvmtd td) gv1 (coqtype_2_llvmtype t2)
    | Coq_castop_bitcast -> GenericValue.bitcast gv1 
                              (coqtype_2_llvmtype t1) 
                              (Llvm.global_context()) 
                              (coqtype_2_llvmtype t2)
  )

  let mext (td:layouts) (op:extop) (t1:typ) (gv1:t) (t2:typ) =
  Some(
  match op with
    | Coq_extop_z -> GenericValue.zext gv1 (coqtype_2_llvmtype t2)
    | Coq_extop_s -> GenericValue.sext gv1 (coqtype_2_llvmtype t2)
  )

  let micmp (td:layouts) (c:cond) (t:typ) (gv1:t) (gv2:t) =
  Some (GenericValue.icmp gv1 gv2 (coqtype_2_llvmtype t) (coqcond_2_llvmicmp c))

end

module Mem = struct

  type t = ExecutionEngine.t * Llvm.llmodule

  let initmem = failwith "undef"

  let malloc (td:LLVMsyntax.layouts) m size (a:LLVMsyntax.align) = 
    let (ee, _) = m in
    match (ExecutionEngine.malloc_memory size ee) with
    | Some gv -> Some (m, gv)
    | None -> None

  let free (td:LLVMsyntax.layouts) m ptr =
    let (ee, _) = m in
    let _ = ExecutionEngine.free_memory ptr ee in
    Some m

  let mload (td:LLVMsyntax.layouts) m ptr t (a:LLVMsyntax.align) =
    let (ee, _) = m in
    Some (ExecutionEngine.load_value_from_memory ptr (coqtype_2_llvmtype t) ee)

  let mstore (td:LLVMsyntax.layouts) m ptr t gv (a:LLVMsyntax.align) =
    let (ee, _) = m in
    let _ = ExecutionEngine.store_value_to_memory gv ptr (coqtype_2_llvmtype t) ee in
    Some m

  let initGlobal (td:LLVMsyntax.layouts) gl m (id0:LLVMsyntax.id) 
                 (t:LLVMsyntax.typ)(c:LLVMsyntax.const)(align0:LLVMsyntax.align) =
    let (ee, mm) = m in
    match Llvm.lookup_global id0 mm with
    | Some v -> 
       (match ExecutionEngine.get_pointer_to_global_if_available v ee with
       | Some gv -> Some (gv, m)
       | None -> None)
    | None -> None

end
