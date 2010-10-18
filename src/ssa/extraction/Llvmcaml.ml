open Llvm_executionengine
open Ssa_def

module GenericValue = struct

  type t = GenericValue.t

  let null = failwith "undef"

  let sizeGenericValue x = failwith "undef"
  let uninits x = failwith "undef"
  let gv2val x y = failwith "undef"
  let gv2int x y z = failwith "undef"
  let gv2ptr x y z = failwith "undef"
  let val2GV x y z = failwith "undef"
  let ptr2GV x y = failwith "undef"
  let blk2GV x = failwith "undef"
  let mgep x y z w = failwith "undef"
  let _const2GV x y z = failwith "undef"
  let _list_const_arr2GV x y z = failwith "undef" 
  let _list_const_struct2GV x y z = failwith "undef" 
  let const2GV x y z = failwith "undef"
  let extractGenericValue x y z w = failwith "undef"
  let insertGenericValue x y z a b = failwith "undef"
  let mbop x y z a b = failwith "undef"
  let mcast x y z a b = failwith "undef"
  let mext x y z a b = failwith "undef"
  let micmp x y z a b = failwith "undef"

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

  let coqtype_2_llvmtype t = failwith "undef"

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
