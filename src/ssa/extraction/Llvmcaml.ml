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

