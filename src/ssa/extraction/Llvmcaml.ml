(* This function used at the proof to generate a fresh atom, which should not be used at runtime. *)
let atom_fresh_for_list a = failwith "AtomImpl.atom_fresh_for_list cannot be used at runtime"

(* These conversion functions are very efficient, because the machine representation of
   nat is not practice. We should figure out if we can remove these functions later... *)
let int2nat i = failwith "int2nat is undef"

let nat2int i = failwith "nat2int is undef"

let llapint2nat i = failwith "llapint2nat is undef"

let llapint2z i = failwith "llapint2Z is undef"

let nat2llapint i = failwith "nat2llapint is undef"

(* The functions below use the above conversion functions, I hope we wont use them at runtime. *)
let nth_list_typ i lt = failwith "nth_list_typ cannot be used at runtime"

let getCmdTyp c = failwith "getCmdtyp cannot be used at runtime"

let getTyp c = failwith "getTyp cannot be used at runtime"

let getPrimitiveSizeInBits t = failwith "getPrimitiveSizeInBits cannot be used at runtime"

let getNumElements t = failwith "getNumElements cannot be used at runtime" 

module GenericValue = struct

  type t

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

  type t = unit

  let malloc x y z w = failwith "undef"
  let free x y = failwith "undef"
  let mload x y z a b = failwith "undef"
  let mstore x y z a b c = failwith "undef"
  let genGlobalAndInitMem x y z w = failwith "undef"

end
