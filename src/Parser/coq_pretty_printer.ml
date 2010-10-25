open Printf
open Ssa_def
open Ssa_lib
open Llvm

(** Coq Pretty Printer *)
let rec string_of_typ ty =
  match ty with
  | LLVMsyntax.Coq_typ_int sz -> "i"^(string_of_int sz)
	| LLVMsyntax.Coq_typ_float -> "float"
	| LLVMsyntax.Coq_typ_double -> "double"
	| LLVMsyntax.Coq_typ_void -> "void"
	| LLVMsyntax.Coq_typ_label -> "label"
	| LLVMsyntax.Coq_typ_metadata -> "metadata"
	| LLVMsyntax.Coq_typ_array (sz, t) ->
		                 "["   ^ (string_of_int sz) ^
                      " x " ^ (string_of_typ t) ^ "]"
  | LLVMsyntax.Coq_typ_function (t, ts) ->		
		                 string_of_typ t ^ " (" ^ string_of_list_typ ts ^ ")"
  | LLVMsyntax.Coq_typ_struct ts ->
	                   "{ " ^ string_of_list_typ ts ^ " }"
  | LLVMsyntax.Coq_typ_pointer t -> (string_of_typ t) ^ "*"
and string_of_list_typ ts =
	match ts with
  | LLVMsyntax.Cons_list_typ (t, ts') ->  (string_of_typ t)^" "^(string_of_list_typ ts')
	| LLVMsyntax.Nil_list_typ -> ""

let rec string_of_constant c = 
	match c with
	| LLVMsyntax.Coq_const_int (sz, i) -> APInt.to_string i^":"^string_of_int sz
	| LLVMsyntax.Coq_const_undef _ -> "undef"
	| LLVMsyntax.Coq_const_null _ -> "null"
	| LLVMsyntax.Coq_const_arr (_, cs) -> string_of_list_constant cs
	| LLVMsyntax.Coq_const_struct cs -> string_of_list_constant cs
  | LLVMsyntax.Coq_const_gid (_,id) -> id
and string_of_list_constant cs =
	match cs with
  | LLVMsyntax.Cons_list_const (c, cs') ->  (string_of_constant c)^" "^(string_of_list_constant cs')
	| LLVMsyntax.Nil_list_const -> ""
	
let string_of_value v =
	match v with
	| LLVMsyntax.Coq_value_id id -> id
	| LLVMsyntax.Coq_value_const c -> string_of_constant c

let rec string_of_params ps =
	match ps with
	| [] -> ""
	| (t, v)::ps' -> "("^(string_of_typ t)^","^(string_of_value v)^")"^(string_of_params ps')

let rec string_of_list_value vs =
	match vs with
	| LLVMsyntax.Nil_list_value -> ""
	| LLVMsyntax.Cons_list_value (v, vs') -> (string_of_value v)^" "^(string_of_list_value vs')

let string_of_bop bop =
	match bop with
	| LLVMsyntax.Coq_bop_add -> "add" 			
	| LLVMsyntax.Coq_bop_and -> "and"
	| LLVMsyntax.Coq_bop_or -> "or" 			
	| LLVMsyntax.Coq_bop_lshr -> "lshr" 			
									
let string_of_extop extop =
	match extop with
	| LLVMsyntax.Coq_extop_s -> "sext" 			
	| LLVMsyntax.Coq_extop_z -> "zext"

let string_of_castop castop =
	match castop with
	| LLVMsyntax.Coq_castop_fptoui -> "fptoui" 			
	| LLVMsyntax.Coq_castop_fptosi -> "fptosi"	 
	| LLVMsyntax.Coq_castop_uitofp -> "uitofp"
	| LLVMsyntax.Coq_castop_sitofp -> "sitofp"
  | LLVMsyntax.Coq_castop_ptrtoint -> "ptrtoint"
	| LLVMsyntax.Coq_castop_inttoptr -> "inttoptr"
	| LLVMsyntax.Coq_castop_bitcast -> "bitcast"

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

let rec string_of_list_value_l vls =
	match vls with
  | LLVMsyntax.Cons_list_value_l (v, l, vls') ->  "("^(string_of_value v)^","^l^")"^(string_of_list_value_l vls')
	| LLVMsyntax.Nil_list_value_l -> ""

let rec string_of_args args =
	match args with
	| [] -> ""
	| (t, id)::args' -> "("^(string_of_typ t)^","^id^")"^(string_of_args args')


let travel_terminator i =
	match i with 
	| LLVMsyntax.Coq_insn_br (id, v, l1, l2) -> 
		  eprintf "  %s = br %s %s %s\n" id (string_of_value v) l1 l2
	| LLVMsyntax.Coq_insn_br_uncond (id, l) -> 
		  eprintf "  %s = br %s \n" id l
  | LLVMsyntax.Coq_insn_return (id, t, v) ->
		  eprintf "  %s = ret %s %s\n" id (string_of_typ t) (string_of_value v)
  | LLVMsyntax.Coq_insn_return_void id ->
		  eprintf "  %s = ret void\n" id
  | LLVMsyntax.Coq_insn_unreachable id -> 
		  eprintf "  %s = unreachable\n" id
	;
  flush_all ()			

let travel_cmd i =
	match i with
  | LLVMsyntax.Coq_insn_bop (id, bop, sz, v1, v2) ->
		  eprintf "  %s = bop %s i%d %s %s\n" id (string_of_bop bop) sz (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_extractvalue (id, t, v, cs) ->
		  eprintf "  %s = extractvalue %s %s %s\n" id (string_of_typ t) (string_of_value v) (string_of_list_constant cs)
  | LLVMsyntax.Coq_insn_insertvalue (id, t1, v1, t2, v2, cs) ->
		  eprintf "  %s = insertvalue %s %s %s %s %s\n" id (string_of_typ t1) (string_of_value v1) (string_of_typ t2) (string_of_value v2) (string_of_list_constant cs)
  | LLVMsyntax.Coq_insn_malloc (id, t, sz, align) ->
		  eprintf "  %s = malloc %s %d %d\n" id (string_of_typ t) sz align
  | LLVMsyntax.Coq_insn_alloca (id, t, sz, align) ->
		  eprintf "  %s = alloca %s %d %d\n" id (string_of_typ t) sz align
  | LLVMsyntax.Coq_insn_free (id, t, v) ->
		  eprintf "  %s = free %s %s\n" id (string_of_typ t) (string_of_value v)
  | LLVMsyntax.Coq_insn_load (id, t, v, a) ->
		  eprintf "  %s = load %s* %s %d\n" id (string_of_typ t) (string_of_value v) a
  | LLVMsyntax.Coq_insn_store (id, t, v1, v2, a) ->
		  eprintf "  %s = store %s %s %s %d\n" id (string_of_typ t) (string_of_value v1) (string_of_value v2) a
  | LLVMsyntax.Coq_insn_gep (id, inbounds, t, v, vs) ->
		  eprintf "  %s = gep %s %s %s %s\n" id (string_of_bool inbounds) (string_of_typ t) (string_of_value v) (string_of_list_value vs)
  | LLVMsyntax.Coq_insn_ext (id, extop, t1, v, t2) ->
		  eprintf "  %s = ext %s %s %s %s\n" id (string_of_extop extop) (string_of_typ t1) (string_of_value v) (string_of_typ t2)
  | LLVMsyntax.Coq_insn_cast (id, castop, t1, v, t2) ->
		  eprintf "  %s = cast %s %s %s %s\n" id (string_of_castop castop) (string_of_typ t1) (string_of_value v) (string_of_typ t2)
  | LLVMsyntax.Coq_insn_icmp (id, cond, t, v1, v2) ->
		  eprintf "  %s = icmp %s %s %s %s\n" id (string_of_cond cond) (string_of_typ t) (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_select (id, v, t, v1, v2) ->
		  eprintf "  %s = select %s %s %s %s\n" id (string_of_value v) (string_of_typ t) (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_call (id, noret, tailc, t, fid, ps) ->
		  eprintf "  %s = call %s %s %s %s %s\n" id (string_of_bool noret) (string_of_bool tailc) (string_of_typ t) fid (string_of_params ps)
	;
  flush_all ()				
					
let travel_phi i =
	match i with
	| LLVMsyntax.Coq_insn_phi (id, t, list_v_l) -> 
		  eprintf "  %s = phi %s %s\n" id (string_of_typ t) (string_of_list_value_l list_v_l)
  ;			
  flush_all ()			
	
let travel_block b =
	match b with
	| LLVMsyntax.Coq_block_intro (l, ps, cs, tmn) ->
		eprintf "label: %s\n" l; flush_all ();
		List.iter travel_phi ps;
		List.iter travel_cmd cs;
		travel_terminator tmn

let travel_fdec f =
	match f with
	| LLVMsyntax.Coq_fheader_intro (t, fid, args) ->
		eprintf "declare %s %s %s\n" (string_of_typ t) fid (string_of_args args); flush_all ()

let travel_fdef f =
	match f with
	| LLVMsyntax.Coq_fdef_intro (LLVMsyntax.Coq_fheader_intro (t, fid, args), bs) ->
		eprintf "define %s %s %s\n" (string_of_typ t) fid (string_of_args args); flush_all ();
		List.iter travel_block bs
			  	
let travel_product g =
	match g with
	| LLVMsyntax.Coq_product_gvar (LLVMsyntax.Coq_gvar_intro (id, t, c, a)) -> 
		eprintf "%s = global %s %s %d\n" id (string_of_typ t) (string_of_constant c) a; 
		flush_all ()
	| LLVMsyntax.Coq_product_fdec f -> travel_fdec f
	| LLVMsyntax.Coq_product_fdef f -> travel_fdef f 

let travel_layout dlt =
	match dlt with
	| LLVMsyntax.Coq_layout_be -> eprintf "E\n"
	| LLVMsyntax.Coq_layout_le -> eprintf "e\n"
	| LLVMsyntax.Coq_layout_ptr (sz, a1, a2) -> eprintf "p:%d:%d:%d\n" sz a1 a2 
	| LLVMsyntax.Coq_layout_int (sz, a1, a2) -> eprintf "i:%d:%d:%d\n" sz a1 a2	
	| LLVMsyntax.Coq_layout_aggr (sz, a1, a2) -> eprintf "a:%d:%d:%d\n" sz a1 a2
	| LLVMsyntax.Coq_layout_stack (sz, a1, a2) -> eprintf "s:%d:%d:%d\n" sz a1 a2
	;
	flush_all ()

let travel_module m =
	prerr_endline "Travel Coq module:";
	match m with
	| LLVMsyntax.Coq_module_intro (dlts, ps) -> 
		List.iter travel_layout dlts;
		List.iter travel_product ps



