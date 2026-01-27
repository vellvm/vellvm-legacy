open Printf
open Syntax
open Infrastructure
open Llvm

(** Coq Pretty Printer *)
let getRealName (id:LLVMsyntax.id) =
    if String.length id <= 1
    then id
    else 
      if String.get id 0 = '@' or String.get id 0 = '%'
      then String.sub id 1 (String.length id-1)
      else id

let check_colons (id0:LLVMsyntax.id) : LLVMsyntax.id =
  if String.contains id0 ':' then "\"" ^ id0 ^ "\"" else id0

let rec string_of_floating_point fp =
  match fp with
  | LLVMsyntax.Coq_fp_float -> "float" 
  | LLVMsyntax.Coq_fp_double -> "double" 
  | LLVMsyntax.Coq_fp_fp128 -> "fp128" 
  | LLVMsyntax.Coq_fp_x86_fp80 -> "x86_fp80" 
  | LLVMsyntax.Coq_fp_ppc_fp128 -> "ppc_fp128"

let rec string_of_typ ty =
  match ty with
  | LLVMsyntax.Coq_typ_int sz -> "i"^(string_of_int sz)
  | LLVMsyntax.Coq_typ_floatpoint fp -> string_of_floating_point fp
  | LLVMsyntax.Coq_typ_void -> "void"
  | LLVMsyntax.Coq_typ_label -> "label"
  | LLVMsyntax.Coq_typ_metadata -> "metadata"
  | LLVMsyntax.Coq_typ_array (sz, t) ->
                     "["   ^ (string_of_int sz) ^
                      " x " ^ (string_of_typ t) ^ "]"
  | LLVMsyntax.Coq_typ_function (t, ts, va) ->    
      string_of_typ t ^ " (" ^ string_of_list_typ ts ^
        (match va with
         | Some _ ->
           (if List.length ts = 0
            then "... " else ", ... ") 
         | None -> "") ^
       ")"
  | LLVMsyntax.Coq_typ_struct ts ->
                     "{ " ^ string_of_list_typ ts ^ " }"
  | LLVMsyntax.Coq_typ_pointer t -> (string_of_typ t) ^ "*"
  | LLVMsyntax.Coq_typ_namedt id -> "%"^check_colons id
and string_of_list_typ ts =
  String.concat "," (List.map string_of_typ ts)

let string_of_bop bop =
  match bop with
  | LLVMsyntax.Coq_bop_add -> "add"       
  | LLVMsyntax.Coq_bop_sub -> "sub"
  | LLVMsyntax.Coq_bop_mul -> "mul"
  | LLVMsyntax.Coq_bop_udiv -> "udiv"
  | LLVMsyntax.Coq_bop_sdiv -> "sdiv"
  | LLVMsyntax.Coq_bop_urem -> "urem"
  | LLVMsyntax.Coq_bop_srem -> "srem"
  | LLVMsyntax.Coq_bop_shl -> "shl"
  | LLVMsyntax.Coq_bop_lshr -> "lshr"       
  | LLVMsyntax.Coq_bop_ashr -> "ashr"
  | LLVMsyntax.Coq_bop_and -> "and"
  | LLVMsyntax.Coq_bop_or -> "or"       
  | LLVMsyntax.Coq_bop_xor -> "xor"  
                  
let string_of_fbop fbop =
  match fbop with
  | LLVMsyntax.Coq_fbop_fadd -> "fadd"       
  | LLVMsyntax.Coq_fbop_fsub -> "fsub"
  | LLVMsyntax.Coq_fbop_fmul -> "fmul"
  | LLVMsyntax.Coq_fbop_fdiv -> "fdiv"
  | LLVMsyntax.Coq_fbop_frem -> "frem"

let string_of_cond cond =
  match cond with
  | LLVMsyntax.Coq_cond_eq -> "eq"       
  | LLVMsyntax.Coq_cond_ne -> "ne"       
  | LLVMsyntax.Coq_cond_ugt -> "ugt"       
  | LLVMsyntax.Coq_cond_uge -> "uge"       
  | LLVMsyntax.Coq_cond_ult -> "ult"       
  | LLVMsyntax.Coq_cond_ule -> "ule"       
  | LLVMsyntax.Coq_cond_sgt -> "sgt"       
  | LLVMsyntax.Coq_cond_sge -> "sge"       
  | LLVMsyntax.Coq_cond_slt -> "slt"       
  | LLVMsyntax.Coq_cond_sle -> "sle"       

let string_of_fcond fcond =
  match fcond with
  | LLVMsyntax.Coq_fcond_false -> "false"       
  | LLVMsyntax.Coq_fcond_oeq -> "oeq"
  | LLVMsyntax.Coq_fcond_ogt -> "ogt"       
  | LLVMsyntax.Coq_fcond_oge -> "oge"       
  | LLVMsyntax.Coq_fcond_olt -> "olt"       
  | LLVMsyntax.Coq_fcond_ole -> "ole"       
  | LLVMsyntax.Coq_fcond_one -> "one"       
  | LLVMsyntax.Coq_fcond_ord -> "ord"       
  | LLVMsyntax.Coq_fcond_ueq -> "ueq"       
  | LLVMsyntax.Coq_fcond_ugt -> "ugt"       
  | LLVMsyntax.Coq_fcond_uge -> "uge"       
  | LLVMsyntax.Coq_fcond_ult -> "ult"       
  | LLVMsyntax.Coq_fcond_ule -> "ule"       
  | LLVMsyntax.Coq_fcond_une -> "une"
  | LLVMsyntax.Coq_fcond_uno -> "uno"       
  | LLVMsyntax.Coq_fcond_true -> "true"       
  
let string_of_extop extop =
  match extop with
  | LLVMsyntax.Coq_extop_s -> "sext"       
  | LLVMsyntax.Coq_extop_z -> "zext"
  | LLVMsyntax.Coq_extop_fp -> "fpext"

let string_of_castop castop =
  match castop with
  | LLVMsyntax.Coq_castop_fptoui -> "fptoui"       
  | LLVMsyntax.Coq_castop_fptosi -> "fptosi"   
  | LLVMsyntax.Coq_castop_uitofp -> "uitofp"
  | LLVMsyntax.Coq_castop_sitofp -> "sitofp"
  | LLVMsyntax.Coq_castop_ptrtoint -> "ptrtoint"
  | LLVMsyntax.Coq_castop_inttoptr -> "inttoptr"
  | LLVMsyntax.Coq_castop_bitcast -> "bitcast"

let string_of_truncop truncop =
  match truncop with
  | LLVMsyntax.Coq_truncop_int -> "trunc"       
  | LLVMsyntax.Coq_truncop_fp -> "fptrunc"

let rec print_concat fo (seq:String.t) (f:'a -> unit) 
  (cs:'a list) : unit =
match cs with
  | [] -> ()
  | c::cs' -> 
      f c;
      (if List.length cs' > 0 then fprintf fo "%s" seq);
      print_concat fo seq f cs'

let rec travel_constant fo c = 
  let travel_convop op t' c t =
    fprintf fo "%s (" op;
    travel_typed_constant fo t' c;
    fprintf fo " to %s )" (string_of_typ t) in
  let travel_bop prefix t c1 c2 =
    fprintf fo "%s (" prefix;
    travel_typed_constant fo t c1;
    fprintf fo ",";
    travel_typed_constant fo t c2;
    fprintf fo ")" in
  match c with
  | LLVMsyntax.Coq_const_int (sz, i) -> fprintf fo "%s" (APInt.to_string i )
  | LLVMsyntax.Coq_const_undef _ -> fprintf fo "undef"
  | LLVMsyntax.Coq_const_null _ -> fprintf fo "null"
  | LLVMsyntax.Coq_const_arr (_, cs) -> 
      (fprintf fo "["; travel_list_constant fo cs; fprintf fo "]")
  | LLVMsyntax.Coq_const_struct (_, cs) -> 
      (fprintf fo "{"; travel_list_constant fo cs; fprintf fo "}")
  | LLVMsyntax.Coq_const_gid (_,id) -> 
      fprintf fo "%s" id
  | LLVMsyntax.Coq_const_zeroinitializer _ -> 
      fprintf fo "zeroinitializer"
  | LLVMsyntax.Coq_const_floatpoint (_, f) -> 
      fprintf fo "%s" (APFloat.to_string f)
  | LLVMsyntax.Coq_const_truncop (op, c, t) -> 
      (match (LLVMinfra.Constant.getTyp c) with
        | Some t' -> travel_convop (string_of_truncop op) t' c t
        | None -> failwith "const trunc must be of a typ.")
  | LLVMsyntax.Coq_const_extop (op, c, t) -> 
      (match (LLVMinfra.Constant.getTyp c) with
        | Some t' -> travel_convop (string_of_extop op) t' c t
        | None -> failwith "const ext must be of a typ.")
  | LLVMsyntax.Coq_const_castop (op, c, t) -> 
      (match (LLVMinfra.Constant.getTyp c) with
        | Some t' -> travel_convop (string_of_castop op) t' c t
        | None -> failwith "const cast must be of a typ.")
  | LLVMsyntax.Coq_const_gep (ib, c, cs) -> 
      (match (LLVMinfra.Constant.getTyp c) with
        | Some t -> 
           (fprintf fo "getelementptr ";
            (match ib with
              | true -> fprintf fo "inbounds ("
              | false -> fprintf fo " (");
            travel_typed_constant fo t c;
            fprintf fo ", ";
            travel_list_constant fo cs;
            fprintf fo ")")
        | None -> failwith "const gep must be of a typ.")
  |  LLVMsyntax.Coq_const_select (c0, c1, c2) -> 
      (match (LLVMinfra.Constant.getTyp c0, LLVMinfra.Constant.getTyp c1) with
        | (Some t0, Some t) ->
           (fprintf fo "select (";
            travel_typed_constant fo t0 c0;
            fprintf fo ", ";
            travel_typed_constant fo t c1;
            fprintf fo ", ";
            travel_typed_constant fo t c2;
            fprintf fo ")")
        | _ -> failwith "const select must be of a typ.")
  |  LLVMsyntax.Coq_const_icmp (cond, c1, c2) ->
      (match (LLVMinfra.Constant.getTyp c1) with
        | Some t -> 
            travel_bop ("icmp "^string_of_cond cond) t c1 c2
        | _ -> failwith "const icmp must be of a typ.")
  |  LLVMsyntax.Coq_const_fcmp (cond, c1, c2) ->
      (match (LLVMinfra.Constant.getTyp c1) with
        | Some t -> 
            travel_bop ("fcmp "^string_of_fcond cond) t c1 c2
        | _ -> failwith "const fcmp must be of a typ.")
  | LLVMsyntax.Coq_const_extractvalue (c, cs) ->
      (match (LLVMinfra.Constant.getTyp c) with
        | Some t -> 
           (fprintf fo "extractvalue (";
            travel_typed_constant fo t c;
            fprintf fo ", ";
            travel_list_idxs fo cs;
            fprintf fo ")")
        | _ -> failwith "const extract must be of a typ.")
  | LLVMsyntax.Coq_const_insertvalue (c1, c2, cs) ->
      (match (LLVMinfra.Constant.getTyp c1, LLVMinfra.Constant.getTyp c2) with
        | (Some t1, Some t2) -> 
           (fprintf fo "insertvalue (";
            travel_typed_constant fo t1 c1;
            fprintf fo ", ";
            travel_typed_constant fo t2 c2;
            fprintf fo ", ";
            travel_list_idxs fo cs;
            fprintf fo ")")
        | _ -> failwith "const insert must be of a typ.")
  | LLVMsyntax.Coq_const_bop (op, c1, c2) -> 
      (match (LLVMinfra.Constant.getTyp c1) with
        | Some t -> 
            travel_bop (string_of_bop op) t c1 c2
        | None -> failwith "const bop must be of a typ.")
  | LLVMsyntax.Coq_const_fbop (op, c1, c2) -> 
      (match (LLVMinfra.Constant.getTyp c1) with
        | Some t -> 
            travel_bop (string_of_fbop op) t c1 c2
        | None -> failwith "const fbop must be of a typ.")
            
and travel_typed_constant fo t0 c0 =
  fprintf fo "%s " (string_of_typ t0);
  travel_constant fo c0 

and travel_list_constant fo cs =
  print_concat fo "," 
    (fun c -> 
     match (LLVMinfra.Constant.getTyp c) with
     | Some t -> travel_typed_constant fo t c
     | None -> failwith "const must be of type.") 
    cs

and travel_list_idxs fo cs =
  print_concat fo "," (travel_constant fo) cs

let rec getSubTypFromConstIdxs nts idxs t =
  let helper idx idxs' lt =
     match idx with
       | LLVMsyntax.Coq_const_int (sz0, i0) ->
           (match List0.nth_error lt (Datatype_base.INTEGER.to_nat i0) with
            | Some t' -> getSubTypFromConstIdxs nts idxs' t'
            | None -> None)
       | _ -> None in
  match idxs with
    | [] -> Some t
    | idx::idxs' ->
          (match t with
             | LLVMsyntax.Coq_typ_array (sz0, t') ->
                 getSubTypFromConstIdxs nts idxs' t'
             | LLVMsyntax.Coq_typ_struct lt -> helper idx idxs' lt
             | LLVMsyntax.Coq_typ_namedt nid ->
                 (match Alist.lookupAL nts nid with
                  | Some lt -> helper idx idxs' lt
                  | None -> None)
             | _ -> None)

let getConstGEPTyp nts idxs t =
  match idxs with
    | [] -> None
    | idx::idxs' ->
          (match t with
             | LLVMsyntax.Coq_typ_pointer t0 ->
                 (match getSubTypFromConstIdxs nts idxs' t0 with
                    | Some t' -> Some (LLVMsyntax.Coq_typ_pointer t')
                    | None -> None)
             | _ -> None)

let rec getTyp nts = function
  | LLVMsyntax.Coq_const_zeroinitializer t -> Some t
  | LLVMsyntax.Coq_const_int (sz0, int5) -> Some (LLVMsyntax.Coq_typ_int
          sz0)
  | LLVMsyntax.Coq_const_floatpoint (fp, float5) -> Some
          (LLVMsyntax.Coq_typ_floatpoint fp)
  | LLVMsyntax.Coq_const_undef t -> Some t
  | LLVMsyntax.Coq_const_null t -> Some (LLVMsyntax.Coq_typ_pointer t)
  | LLVMsyntax.Coq_const_arr (t, lc) -> Some
          (match lc with
             | [] -> LLVMsyntax.Coq_typ_array (Datatype_base.Size.coq_Zero, t)
             | c'::lc' -> LLVMsyntax.Coq_typ_array (List.length lc, t))
  | LLVMsyntax.Coq_const_struct (t, lc) -> Some t
  | LLVMsyntax.Coq_const_gid (t, id5) -> Some (LLVMsyntax.Coq_typ_pointer
          t)
  | LLVMsyntax.Coq_const_truncop (truncop5, const5, t) -> Some t
  | LLVMsyntax.Coq_const_extop (extop5, const5, t) -> Some t
  | LLVMsyntax.Coq_const_castop (castop5, const5, t) -> Some t
  | LLVMsyntax.Coq_const_gep (inbounds5, c0, idxs) ->
          (match getTyp nts c0 with
             | Some t -> getConstGEPTyp nts idxs t
             | None -> None)
  | LLVMsyntax.Coq_const_select (c0, c1, c2) -> getTyp nts c1
  | LLVMsyntax.Coq_const_extractvalue (c0, idxs) ->
          (match getTyp nts c0 with
             | Some t -> getSubTypFromConstIdxs nts idxs t
             | None -> None)
  | LLVMsyntax.Coq_const_insertvalue (c0, c', lc) -> getTyp nts c0
  | LLVMsyntax.Coq_const_bop (bop5, c1, c2) -> getTyp nts c1
  | LLVMsyntax.Coq_const_fbop (fbop5, c1, c2) -> getTyp nts c1
  | _ -> Some (LLVMsyntax.Coq_typ_int Datatype_base.Size.coq_One)

let rec string_of_constant nts c =
  match c with
  | LLVMsyntax.Coq_const_int (sz, i) -> APInt.to_string i
(*      "i"^string_of_int sz^" "^APInt.to_string i*)
  | LLVMsyntax.Coq_const_undef _ -> "undef"
  | LLVMsyntax.Coq_const_null _ -> "null"
  | LLVMsyntax.Coq_const_arr (_, cs) -> "[" ^ string_of_list_constant nts cs ^ "]"
  | LLVMsyntax.Coq_const_struct (_, cs) -> "{" ^ string_of_list_constant nts cs ^ "}"
  | LLVMsyntax.Coq_const_gid (_,id) -> id
  | LLVMsyntax.Coq_const_zeroinitializer _ -> "zeroinitializer"
  | LLVMsyntax.Coq_const_floatpoint (_, f) -> APFloat.to_string f
  | LLVMsyntax.Coq_const_truncop (op, c, t) ->
      (match getTyp nts c with
        | Some t' -> string_of_truncop op^" ("^string_of_typ t'^" "^
            string_of_constant nts c^" to "^string_of_typ t^")"
        | None -> failwith "const trunc must be of a typ.")
  | LLVMsyntax.Coq_const_extop (op, c, t) ->
      (match getTyp nts c with
        | Some t' -> string_of_extop op^" ("^string_of_typ t'^" "^
            string_of_constant nts c^" to "^string_of_typ t^")"
        | None -> failwith "const ext must be of a typ.")
  | LLVMsyntax.Coq_const_castop (op, c, t) ->
      (match getTyp nts c with
        | Some t' -> string_of_castop op^" ("^string_of_typ t'^" "^
            string_of_constant nts c^" to "^string_of_typ t^")"
        | None -> failwith "const cast must be of a typ.")
  | LLVMsyntax.Coq_const_gep (ib, c, cs) ->
      (match getTyp nts c with
        | Some t -> "getelementptr "^
            (match ib with
              | true -> "inbounds"
              | false -> "") ^" ("^
            string_of_typ t ^" "^
            string_of_constant nts c^", "^
            string_of_list_constant nts cs^")"
        | None -> failwith "const gep must be of a typ.")
  |  LLVMsyntax.Coq_const_select (c0, c1, c2) ->
      (match (getTyp nts c0, getTyp nts c1) with
        | (Some t0, Some t) ->
           "select ("^string_of_typ t0^" "^string_of_constant nts c0^", "^
                      string_of_typ t^" "^string_of_constant nts c1^", "^
                      string_of_typ t ^" "^string_of_constant nts c2^")"
        | _ -> failwith "const select must be of a typ.")
  |  LLVMsyntax.Coq_const_icmp (cond, c1, c2) ->
      (match (getTyp nts c1) with
        | Some t ->
            "icmp "^string_of_cond cond^" ("^
               string_of_typ t ^" "^ string_of_constant nts c1^", "^
               string_of_typ t ^" "^ string_of_constant nts c2^")"
        | _ -> failwith "const icmp must be of a typ.")
  |  LLVMsyntax.Coq_const_fcmp (cond, c1, c2) ->
      (match (getTyp nts c1) with
        | Some t ->
           "fcmp "^string_of_fcond cond^" ("^
              string_of_typ t ^" "^string_of_constant nts c1^", "^
              string_of_typ t ^" "^string_of_constant nts c2^")"
        | _ -> failwith "const fcmp must be of a typ.")
  | LLVMsyntax.Coq_const_extractvalue (c, cs) ->
      (match (getTyp nts c) with
        | Some t ->
           "extractvalue ("^
             string_of_typ t ^" "^string_of_constant nts c^", "^
             string_of_list_idxs nts cs^")"
        | _ -> failwith "const extract must be of a typ.")
  | LLVMsyntax.Coq_const_insertvalue (c1, c2, cs) ->
      (match (getTyp nts c1, getTyp nts c2) with
        | (Some t1, Some t2) ->
            "insertvalue ("^
               string_of_typ t1 ^" "^string_of_constant nts c1^", "^
               string_of_typ t2 ^" "^string_of_constant nts c2^", "^
               string_of_list_idxs nts cs^")"
        | _ -> failwith "const insert must be of a typ.")
  | LLVMsyntax.Coq_const_bop (op, c1, c2) ->
      (match (getTyp nts c1) with
        | Some t ->
            string_of_bop op^" ("^
              string_of_typ t ^" "^ string_of_constant nts c1^", "^
              string_of_typ t ^" "^ string_of_constant nts c2^")"
        | None -> failwith "const bop must be of a typ.")
  | LLVMsyntax.Coq_const_fbop (op, c1, c2) ->
      (match (getTyp nts c1) with
        | Some t ->
            string_of_fbop op^" ("^
              string_of_typ t ^" "^ string_of_constant nts c1^", "^
              string_of_typ t ^" "^ string_of_constant nts c2^")"
        | None -> failwith "const bop must be of a typ.")
            
and string_of_list_constant nts cs =
  String.concat "," (List.map
    (fun c ->
      match (getTyp nts c) with
      | Some t -> string_of_typ t ^ " " ^ string_of_constant nts c
      | None -> failwith "const must be of type.")
    cs)

and string_of_list_idxs nts cs =
  String.concat "," (List.map (fun c -> string_of_constant nts c) cs)

let string_of_value nts v =
  match v with
  | LLVMsyntax.Coq_value_id id -> id
  | LLVMsyntax.Coq_value_const c -> string_of_constant nts c

let string_of_attribute a =
match a with
  | LLVMsyntax.Coq_attribute_zext -> "zeroext"
  | LLVMsyntax.Coq_attribute_sext -> "signext"
  | LLVMsyntax.Coq_attribute_noreturn -> "noreturn"
  | LLVMsyntax.Coq_attribute_inreg -> "inreg"
  | LLVMsyntax.Coq_attribute_structret -> "sret"
  | LLVMsyntax.Coq_attribute_nounwind -> "nounwind"
  | LLVMsyntax.Coq_attribute_noalias -> "noalias"
  | LLVMsyntax.Coq_attribute_byval -> "byval"
  | LLVMsyntax.Coq_attribute_nest -> "nest"
  | LLVMsyntax.Coq_attribute_readnone -> "readnone"
  | LLVMsyntax.Coq_attribute_readonly -> "readonly"
  | LLVMsyntax.Coq_attribute_noinline -> "noinline"
  | LLVMsyntax.Coq_attribute_alwaysinline -> "alwaysinline"
  | LLVMsyntax.Coq_attribute_optforsize -> "optsize"
  | LLVMsyntax.Coq_attribute_stackprotect -> "ssp"
  | LLVMsyntax.Coq_attribute_stackprotectreq -> "sspreq"
  | LLVMsyntax.Coq_attribute_nocapture -> "nocapture"
  | LLVMsyntax.Coq_attribute_noredzone -> "noredzone"
  | LLVMsyntax.Coq_attribute_implicitfloat -> "noimplicitfloat"
  | LLVMsyntax.Coq_attribute_naked -> "naked"

let string_of_attributes attrs =
  String.concat " " (List.map (fun attr -> string_of_attribute attr) attrs) 

let string_of_params nts ps =
  "(" ^ (String.concat "," 
          (List.map (fun ((t,a),v) -> (string_of_typ t) ^ " " ^ 
                                      (string_of_attributes a) ^ " " ^
                                      (string_of_value nts v)) 
          ps)) ^ ")"

let rec prefix_of_list_typ ts n =
  if n <= 0 then []
  else
    match ts with
      | [] -> []
      | t::ts' -> t :: (prefix_of_list_typ ts' (n-1))

let params2typs ps va = 
  let ts = List.map (fun ((t,_),_) -> t) ps in
  match va with
    | None -> ts
    | Some n -> prefix_of_list_typ ts n

let rec string_of_list_value nts vs =
  String.concat "," 
    (List.map 
      (fun (sz, v) -> "i"^(string_of_int sz) ^" " ^ string_of_value nts v) 
      vs)

let name_of_label l = "%" ^ l

let rec string_of_list_value_l nts vls =
  String.concat "," 
    (List.map 
      (fun (v, l) -> "[" ^ (string_of_value nts v) ^ ", " ^ name_of_label l ^ "]") 
    vls)

let string_of_va_in_args args va =
  match va with
    | Some _ -> if List.length args = 0 then "... " else ", ... "
    | _ -> ""

let string_of_args_def args va =
  "(" ^ 
  (String.concat "," 
    (List.map 
      (fun ((t,attrs),id) -> 
        (string_of_typ t) ^ " " ^ (string_of_attributes attrs) ^ 
        (try 
          let id' = getRealName id in
          ignore(int_of_string id');
          ""
        with 
          | _ -> " " ^ id)
      ) args
    )
  ) ^ string_of_va_in_args args va ^ ")"

let travel_terminator fo nts i =
  match i with 
  | LLVMsyntax.Coq_insn_br (_, v, l1, l2) -> 
      fprintf fo "  br i1 %s, label %s, label %s\n" (string_of_value nts v) 
        (name_of_label l1) (name_of_label  l2)
  | LLVMsyntax.Coq_insn_br_uncond (_, l) -> 
      fprintf fo "  br label %s \n" (name_of_label  l)
  | LLVMsyntax.Coq_insn_return (_, t, v) ->
      fprintf fo "  ret %s %s\n" (string_of_typ t) (string_of_value nts v)
  | LLVMsyntax.Coq_insn_return_void _ ->
      fprintf fo "  ret void\n"
  | LLVMsyntax.Coq_insn_unreachable _ -> 
      fprintf fo "  unreachable\n"
  ;
  flush_all ()      

let string_of_callconv cc =
match cc with
  | LLVMsyntax.Coq_callconv_ccc -> ""
  | LLVMsyntax.Coq_callconv_fast -> "fastcc"
  | LLVMsyntax.Coq_callconv_cold -> "coldcc"
  | LLVMsyntax.Coq_callconv_x86_stdcall -> "cc 64"
  | LLVMsyntax.Coq_callconv_x86_fastcall -> "cc 65"

let travel_cmd fo nts i =
  match i with
  | LLVMsyntax.Coq_insn_bop (id, bop, sz, v1, v2) ->
      fprintf fo "  %s = %s i%d %s, %s\n" id (string_of_bop bop) sz 
        (string_of_value nts v1) (string_of_value nts v2)
  | LLVMsyntax.Coq_insn_fbop (id, fbop, fp, v1, v2) ->
      fprintf fo "  %s = %s %s %s, %s\n" id (string_of_fbop fbop) 
        (string_of_floating_point fp) (string_of_value nts v1) (string_of_value nts v2)
  | LLVMsyntax.Coq_insn_extractvalue (id, t, v, cs, _) ->
      fprintf fo "  %s = extractvalue %s %s, %s\n" id (string_of_typ t) 
        (string_of_value nts v) (string_of_list_idxs nts cs)
  | LLVMsyntax.Coq_insn_insertvalue (id, t1, v1, t2, v2, cs) ->
      fprintf fo "  %s = insertvalue %s %s, %s %s, %s\n" id (string_of_typ t1)
        (string_of_value nts v1) (string_of_typ t2) (string_of_value nts v2) 
        (string_of_list_idxs nts cs)
  | LLVMsyntax.Coq_insn_malloc (id, t, v, align) ->
      fprintf fo "  %s = malloc %s, i32 %s%s\n" id (string_of_typ t) 
        (string_of_value nts v)
        (if align = 0 then "" else ", align" ^ string_of_int align)
  | LLVMsyntax.Coq_insn_alloca (id, t, v, align) ->
      fprintf fo "  %s = alloca %s, i32 %s%s\n" id (string_of_typ t) 
        (string_of_value nts v) 
        (if align = 0 then "" else ", align " ^ string_of_int align)
  | LLVMsyntax.Coq_insn_free (_, t, v) ->
      fprintf fo "  free %s %s\n" (string_of_typ t) (string_of_value nts v)
  | LLVMsyntax.Coq_insn_load (id, t, v, a) ->
      fprintf fo "  %s = load %s* %s%s\n" id (string_of_typ t) 
        (string_of_value nts v)
        (if a = 0 then "" else ", align " ^ string_of_int a)
  | LLVMsyntax.Coq_insn_store (_, t, v1, v2, a) ->
      fprintf fo "  store %s %s, %s* %s%s\n" (string_of_typ t) 
        (string_of_value nts v1) (string_of_typ t) (string_of_value nts v2)
        (if a = 0 then "" else ", align " ^ string_of_int a)
  | LLVMsyntax.Coq_insn_gep (id, inbounds, t, v, vs, _) ->
      fprintf fo "  %s = getelementptr %s %s* %s, %s\n" id 
        (if inbounds then "inbounds" else "") (string_of_typ t) 
        (string_of_value nts v) (string_of_list_value nts vs)
  | LLVMsyntax.Coq_insn_trunc (id, truncop, t1, v, t2) ->
      fprintf fo "  %s = %s %s %s to %s\n" id (string_of_truncop truncop) 
        (string_of_typ t1) (string_of_value nts v) (string_of_typ t2)
  | LLVMsyntax.Coq_insn_ext (id, extop, t1, v, t2) ->
      fprintf fo "  %s = %s %s %s to %s\n" id (string_of_extop extop) 
        (string_of_typ t1) (string_of_value nts v) (string_of_typ t2)
  | LLVMsyntax.Coq_insn_cast (id, castop, t1, v, t2) ->
      fprintf fo "  %s = %s %s %s to %s\n" id (string_of_castop castop) 
        (string_of_typ t1) (string_of_value nts v) (string_of_typ t2)
  | LLVMsyntax.Coq_insn_icmp (id, cond, t, v1, v2) ->
      fprintf fo "  %s = icmp %s %s %s, %s\n" id (string_of_cond cond) 
        (string_of_typ t) (string_of_value nts v1) (string_of_value nts v2)
  | LLVMsyntax.Coq_insn_fcmp (id, fcond, fp, v1, v2) ->
      fprintf fo "  %s = fcmp %s %s %s, %s\n" id (string_of_fcond fcond) 
        (string_of_floating_point fp) (string_of_value nts v1) (string_of_value nts v2)
  | LLVMsyntax.Coq_insn_select (id, v, t, v1, v2) ->
      fprintf fo "  %s = select i1 %s, %s %s, %s %s\n" id (string_of_value nts v) 
        (string_of_typ t) (string_of_value nts v1) (string_of_typ t) 
        (string_of_value nts v2)
  | LLVMsyntax.Coq_insn_call (id, noret, 
        LLVMsyntax.Coq_clattrs_intro (tailc, cc, ra, ca), rt, va, fv, ps) ->
      fprintf fo "  %s%scall %s %s %s* %s %s %s\n"  
        (if noret then "" else id ^ " = ") 
        (if tailc then "tail " else "") (string_of_callconv cc) 
        (string_of_attributes ra) 
        (string_of_typ (LLVMsyntax.Coq_typ_function (rt, params2typs ps va, va)))
        (string_of_value nts fv) (string_of_params nts ps) (string_of_attributes ca) 
  ;
  flush_all ()        
          
let travel_phi fo nts i =
  match i with
  | LLVMsyntax.Coq_insn_phi (id, t, list_v_l) -> 
      fprintf fo "  %s = phi %s %s\n" id (string_of_typ t) 
        (string_of_list_value_l nts list_v_l)
  ;      
  flush_all ()      
  
let travel_block fo nts b =
  match b with
  | (l, LLVMsyntax.Coq_stmts_intro (ps, cs, tmn)) ->
    (try 
       ignore(int_of_string l);
       fprintf fo "\n"
     with 
       | _ -> fprintf fo "%s:\n" l); 
    flush_all ();
    List.iter (travel_phi fo nts) ps;
    List.iter (travel_cmd fo nts) cs;
    travel_terminator fo nts tmn

let string_of_args_dec fid args va =
  "(" ^ (String.concat "," 
     (List.map (fun ((t,attrs),_) -> 
       (string_of_typ t)^ " " ^(string_of_attributes attrs)) args)) ^ 
     string_of_va_in_args args va ^ 
   ")"
          
let string_of_linkage lk =
match lk with
  | LLVMsyntax.Coq_linkage_external -> ""
  | LLVMsyntax.Coq_linkage_available_externally -> "available_externally"
  | LLVMsyntax.Coq_linkage_link_once -> "linkonce"
  | LLVMsyntax.Coq_linkage_link_once_odr -> "linkonce_odr"
  | LLVMsyntax.Coq_linkage_weak -> "weak"
  | LLVMsyntax.Coq_linkage_weak_odr -> "weak_odr"
  | LLVMsyntax.Coq_linkage_appending -> "appending"
  | LLVMsyntax.Coq_linkage_internal -> "internal"
  | LLVMsyntax.Coq_linkage_private -> "private"
  | LLVMsyntax.Coq_linkage_linker_private -> "linker_private"
  | LLVMsyntax.Coq_linkage_dllimport -> "dllimport"
  | LLVMsyntax.Coq_linkage_dllexport -> "dllexport"
  | LLVMsyntax.Coq_linkage_external_weak -> "extern_weak"
  | LLVMsyntax.Coq_linkage_ghost -> ""
  | LLVMsyntax.Coq_linkage_common -> "common"

let string_of_visibility v =
match v with
  | LLVMsyntax.Coq_visibility_default -> ""
  | LLVMsyntax.Coq_visibility_hidden -> "hidden"
  | LLVMsyntax.Coq_visibility_protected -> "protected"

let travel_fdec fo f =
  match f with
  | LLVMsyntax.Coq_fdec_intro 
      (LLVMsyntax.Coq_fheader_intro 
        ((LLVMsyntax.Coq_fnattrs_intro (lk, vz, cc, ra, fa)), t, fid, args, va),
        _) ->
    fprintf fo "declare %s %s %s %s %s %s %s %s\n" (string_of_linkage lk)
      (string_of_visibility vz) (string_of_callconv cc) 
      (string_of_attributes ra) (string_of_typ t) fid
      (string_of_args_dec fid args va) (string_of_attributes fa); 
    flush_all ()

let travel_fdef fo nts f =
  match f with
  | LLVMsyntax.Coq_fdef_intro 
      (LLVMsyntax.Coq_fheader_intro (
        (LLVMsyntax.Coq_fnattrs_intro (lk, vz, cc, ra, fa)), 
        t, fid, args, va), bs) ->
      fprintf fo "define %s %s %s %s %s %s %s %s{\n"  (string_of_linkage lk)
        (string_of_visibility vz) (string_of_callconv cc) 
        (string_of_attributes ra) (string_of_typ t) fid 
        (string_of_args_def args va) (string_of_attributes fa); 
    flush_all ();
    List.iter (travel_block fo nts) bs;
    fprintf fo "}\n"
          
let string_of_gvar_spec gs =
  match gs with
  | LLVMsyntax.Coq_gvar_spec_global -> "global"           
  | LLVMsyntax.Coq_gvar_spec_constant -> "constant"

let travel_product fo nts g =
  match g with
  | LLVMsyntax.Coq_product_gvar (LLVMsyntax.Coq_gvar_intro 
      (id, lk, spec, t, c, a)) -> 
      begin match t with
        | LLVMsyntax.Coq_typ_pointer t -> 
          fprintf fo "%s = %s %s %s " id (string_of_linkage lk)
            (string_of_gvar_spec spec) (string_of_typ t);
          travel_constant fo c;
          fprintf fo "%s\n" (if a = 0 then "" else ", align " ^ string_of_int a);
          flush_all ()
        | _ -> failwith "global must be of pointer type."
      end
  | LLVMsyntax.Coq_product_gvar (LLVMsyntax.Coq_gvar_external (id, spec, t)) -> 
      begin match t with
        | LLVMsyntax.Coq_typ_pointer t -> 
            fprintf fo "%s = external %s %s\n" id (string_of_gvar_spec spec) 
              (string_of_typ t); 
            flush_all ()
        | _ -> failwith "global must be of pointer type."
      end
  | LLVMsyntax.Coq_product_fdec f -> travel_fdec fo f
  | LLVMsyntax.Coq_product_fdef f -> travel_fdef fo nts f

let travel_layout dlt =
  match dlt with
  | LLVMsyntax.Coq_layout_be -> sprintf "E"
  | LLVMsyntax.Coq_layout_le -> sprintf "e"
  | LLVMsyntax.Coq_layout_ptr (sz, a1, a2) -> sprintf "p:%d:%d:%d" sz a1 a2 
  | LLVMsyntax.Coq_layout_int (sz, a1, a2) -> sprintf "i%d:%d:%d" sz a1 a2  
  | LLVMsyntax.Coq_layout_float (sz, a1, a2) -> sprintf "f%d:%d:%d" sz a1 a2  
  | LLVMsyntax.Coq_layout_aggr (sz, a1, a2) -> sprintf "a%d:%d:%d" sz a1 a2
  | LLVMsyntax.Coq_layout_stack (sz, a1, a2) -> sprintf "s%d:%d:%d" sz a1 a2
  | LLVMsyntax.Coq_layout_vector (sz, a1, a2) -> sprintf "v%d:%d:%d" sz a1 a2

let travel_namedt fo nt =
  match nt with
  | (id, t) ->
    fprintf fo "%%%s = type %s\n" (check_colons id) 
      (string_of_typ (LLVMsyntax.Coq_typ_struct t)); 
    flush_all ()

let travel_module (fo:out_channel) m =
  match m with
  | LLVMsyntax.Coq_module_intro (dlts, nts, ps) -> 
    fprintf fo "target datalayout = \"%s\"\n" 
      (String.concat "-" (List.map travel_layout dlts));
    List.iter (travel_namedt fo) nts;
    List.iter (travel_product fo nts) ps



