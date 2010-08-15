type __ = Obj.t

type bool =
  | True
  | False

type nat =
  | O
  | S of nat

type 'a option =
  | Some of 'a
  | None

type ('a, 'b) prod =
  | Pair of 'a * 'b

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
  | Left
  | Right

val eq_nat_dec : nat -> nat -> sumbool

val max : nat -> nat -> nat

val bool_dec : bool -> bool -> sumbool

type 'a list =
  | Nil
  | Cons of 'a * 'a list

type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
  | EmptyString
  | String of ascii * string

type 'a eqDec = 'a -> 'a -> sumbool

type 'a eqDec_eq = 'a -> 'a -> sumbool

module type ATOM = 
 sig 
  type atom 
  
  val eq_atom_dec : atom -> atom -> sumbool
  
  val atom_fresh_for_list : atom list -> atom
 end

module AtomImpl : 
 ATOM

val eqDec_atom : AtomImpl.atom eqDec

type 'x assocList = (AtomImpl.atom, 'x) prod list

val updateAddAL : 'a1 assocList -> AtomImpl.atom -> 'a1 -> 'a1 assocList

val updateAL : 'a1 assocList -> AtomImpl.atom -> 'a1 -> 'a1 assocList

module LLVMsyntax : 
 sig 
  val last_opt : 'a1 list -> 'a1 option
  
  type coq_INT = nat
  
  type id = AtomImpl.atom
  
  type l = AtomImpl.atom
  
  type align = nat
  
  type sz = nat
  
  type i = nat
  
  type typ =
    | Coq_typ_int of sz
    | Coq_typ_void
    | Coq_typ_label
    | Coq_typ_metadata
    | Coq_typ_array of sz * typ
    | Coq_typ_function of typ * list_typ
    | Coq_typ_struct of list_typ
    | Coq_typ_pointer of typ
  and list_typ =
    | Nil_list_typ
    | Cons_list_typ of typ * list_typ
  
  val typ_rect :
    (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ ->
    'a1 -> list_typ -> 'a1) -> (list_typ -> 'a1) -> (typ -> 'a1 -> 'a1) ->
    typ -> 'a1
  
  val typ_rec :
    (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ ->
    'a1 -> list_typ -> 'a1) -> (list_typ -> 'a1) -> (typ -> 'a1 -> 'a1) ->
    typ -> 'a1
  
  val list_typ_rect :
    'a1 -> (typ -> list_typ -> 'a1 -> 'a1) -> list_typ -> 'a1
  
  val list_typ_rec :
    'a1 -> (typ -> list_typ -> 'a1 -> 'a1) -> list_typ -> 'a1
  
  type const =
    | Coq_const_int of sz * coq_INT
    | Coq_const_undef of typ
    | Coq_const_null of typ
    | Coq_const_arr of list_const
    | Coq_const_struct of list_const
    | Coq_const_gid of typ * id
  and list_const =
    | Nil_list_const
    | Cons_list_const of const * list_const
  
  val const_rect :
    (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const ->
    'a1) -> (list_const -> 'a1) -> (typ -> id -> 'a1) -> const -> 'a1
  
  val const_rec :
    (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const ->
    'a1) -> (list_const -> 'a1) -> (typ -> id -> 'a1) -> const -> 'a1
  
  val list_const_rect :
    'a1 -> (const -> list_const -> 'a1 -> 'a1) -> list_const -> 'a1
  
  val list_const_rec :
    'a1 -> (const -> list_const -> 'a1 -> 'a1) -> list_const -> 'a1
  
  type value =
    | Coq_value_id of id
    | Coq_value_const of const
  
  val value_rect : (id -> 'a1) -> (const -> 'a1) -> value -> 'a1
  
  val value_rec : (id -> 'a1) -> (const -> 'a1) -> value -> 'a1
  
  type param = (typ, value) prod
  
  type params = (typ, value) prod list
  
  type cond =
    | Coq_cond_eq
    | Coq_cond_ne
    | Coq_cond_ugt
    | Coq_cond_uge
    | Coq_cond_ult
    | Coq_cond_ule
    | Coq_cond_sgt
    | Coq_cond_sge
    | Coq_cond_slt
    | Coq_cond_sle
  
  val cond_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    cond -> 'a1
  
  val cond_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    cond -> 'a1
  
  type bop =
    | Coq_bop_add
    | Coq_bop_lshr
    | Coq_bop_and
    | Coq_bop_or
  
  val bop_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop -> 'a1
  
  val bop_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop -> 'a1
  
  type extop =
    | Coq_extop_z
    | Coq_extop_s
  
  val extop_rect : 'a1 -> 'a1 -> extop -> 'a1
  
  val extop_rec : 'a1 -> 'a1 -> extop -> 'a1
  
  type castop =
    | Coq_castop_fptoui
    | Coq_castop_fptosi
    | Coq_castop_uitofp
    | Coq_castop_sitofp
    | Coq_castop_ptrtoint
    | Coq_castop_inttoptr
    | Coq_castop_bitcast
  
  val castop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> castop -> 'a1
  
  val castop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> castop -> 'a1
  
  type inbounds = bool
  
  type tailc = bool
  
  type noret = bool
  
  type list_value =
    | Nil_list_value
    | Cons_list_value of value * list_value
  
  val list_value_rect :
    'a1 -> (value -> list_value -> 'a1 -> 'a1) -> list_value -> 'a1
  
  val list_value_rec :
    'a1 -> (value -> list_value -> 'a1 -> 'a1) -> list_value -> 'a1
  
  type list_id_l =
    | Nil_list_id_l
    | Cons_list_id_l of id * l * list_id_l
  
  val list_id_l_rect :
    'a1 -> (id -> l -> list_id_l -> 'a1 -> 'a1) -> list_id_l -> 'a1
  
  val list_id_l_rec :
    'a1 -> (id -> l -> list_id_l -> 'a1 -> 'a1) -> list_id_l -> 'a1
  
  type cmd =
    | Coq_insn_bop of id * bop * sz * value * value
    | Coq_insn_extractvalue of id * typ * value * list_const
    | Coq_insn_insertvalue of id * typ * value * typ * value * list_const
    | Coq_insn_malloc of id * typ * sz * align
    | Coq_insn_free of id * typ * value
    | Coq_insn_alloca of id * typ * sz * align
    | Coq_insn_load of id * typ * value
    | Coq_insn_store of id * typ * value * value
    | Coq_insn_gep of id * inbounds * typ * value * list_value
    | Coq_insn_ext of id * extop * typ * value * typ
    | Coq_insn_cast of id * castop * typ * value * typ
    | Coq_insn_icmp of id * cond * typ * value * value
    | Coq_insn_select of id * value * typ * value * value
    | Coq_insn_call of id * noret * tailc * typ * id * params
  
  val cmd_rect :
    (id -> bop -> sz -> value -> value -> 'a1) -> (id -> typ -> value ->
    list_const -> 'a1) -> (id -> typ -> value -> typ -> value -> list_const
    -> 'a1) -> (id -> typ -> sz -> align -> 'a1) -> (id -> typ -> value ->
    'a1) -> (id -> typ -> sz -> align -> 'a1) -> (id -> typ -> value -> 'a1)
    -> (id -> typ -> value -> value -> 'a1) -> (id -> inbounds -> typ ->
    value -> list_value -> 'a1) -> (id -> extop -> typ -> value -> typ ->
    'a1) -> (id -> castop -> typ -> value -> typ -> 'a1) -> (id -> cond ->
    typ -> value -> value -> 'a1) -> (id -> value -> typ -> value -> value ->
    'a1) -> (id -> noret -> tailc -> typ -> id -> params -> 'a1) -> cmd ->
    'a1
  
  val cmd_rec :
    (id -> bop -> sz -> value -> value -> 'a1) -> (id -> typ -> value ->
    list_const -> 'a1) -> (id -> typ -> value -> typ -> value -> list_const
    -> 'a1) -> (id -> typ -> sz -> align -> 'a1) -> (id -> typ -> value ->
    'a1) -> (id -> typ -> sz -> align -> 'a1) -> (id -> typ -> value -> 'a1)
    -> (id -> typ -> value -> value -> 'a1) -> (id -> inbounds -> typ ->
    value -> list_value -> 'a1) -> (id -> extop -> typ -> value -> typ ->
    'a1) -> (id -> castop -> typ -> value -> typ -> 'a1) -> (id -> cond ->
    typ -> value -> value -> 'a1) -> (id -> value -> typ -> value -> value ->
    'a1) -> (id -> noret -> tailc -> typ -> id -> params -> 'a1) -> cmd ->
    'a1
  
  type phinode =
    | Coq_insn_phi of id * typ * list_id_l
  
  val phinode_rect : (id -> typ -> list_id_l -> 'a1) -> phinode -> 'a1
  
  val phinode_rec : (id -> typ -> list_id_l -> 'a1) -> phinode -> 'a1
  
  type arg = (typ, id) prod
  
  type terminator =
    | Coq_insn_return of id * typ * value
    | Coq_insn_return_void of id
    | Coq_insn_br of id * value * l * l
    | Coq_insn_br_uncond of id * l
    | Coq_insn_unreachable of id
  
  val terminator_rect :
    (id -> typ -> value -> 'a1) -> (id -> 'a1) -> (id -> value -> l -> l ->
    'a1) -> (id -> l -> 'a1) -> (id -> 'a1) -> terminator -> 'a1
  
  val terminator_rec :
    (id -> typ -> value -> 'a1) -> (id -> 'a1) -> (id -> value -> l -> l ->
    'a1) -> (id -> l -> 'a1) -> (id -> 'a1) -> terminator -> 'a1
  
  type cmds = cmd list
  
  type phinodes = phinode list
  
  type args = (typ, id) prod list
  
  type block =
    | Coq_block_intro of l * phinodes * cmds * terminator
  
  val block_rect :
    (l -> phinodes -> cmds -> terminator -> 'a1) -> block -> 'a1
  
  val block_rec :
    (l -> phinodes -> cmds -> terminator -> 'a1) -> block -> 'a1
  
  type fheader =
    | Coq_fheader_intro of typ * id * args
  
  val fheader_rect : (typ -> id -> args -> 'a1) -> fheader -> 'a1
  
  val fheader_rec : (typ -> id -> args -> 'a1) -> fheader -> 'a1
  
  type blocks = block list
  
  type fdec =
    fheader
    (* singleton inductive, whose constructor was fdec_intro *)
  
  val fdec_rect : (fheader -> 'a1) -> fdec -> 'a1
  
  val fdec_rec : (fheader -> 'a1) -> fdec -> 'a1
  
  type fdef =
    | Coq_fdef_intro of fheader * blocks
  
  val fdef_rect : (fheader -> blocks -> 'a1) -> fdef -> 'a1
  
  val fdef_rec : (fheader -> blocks -> 'a1) -> fdef -> 'a1
  
  type gvar =
    | Coq_gvar_intro of id * typ * const * align
  
  val gvar_rect : (id -> typ -> const -> align -> 'a1) -> gvar -> 'a1
  
  val gvar_rec : (id -> typ -> const -> align -> 'a1) -> gvar -> 'a1
  
  type layout =
    | Coq_layout_be
    | Coq_layout_le
    | Coq_layout_ptr of sz * align * align
    | Coq_layout_int of sz * align * align
    | Coq_layout_aggr of sz * align * align
    | Coq_layout_stack of sz * align * align
  
  val layout_rect :
    'a1 -> 'a1 -> (sz -> align -> align -> 'a1) -> (sz -> align -> align ->
    'a1) -> (sz -> align -> align -> 'a1) -> (sz -> align -> align -> 'a1) ->
    layout -> 'a1
  
  val layout_rec :
    'a1 -> 'a1 -> (sz -> align -> align -> 'a1) -> (sz -> align -> align ->
    'a1) -> (sz -> align -> align -> 'a1) -> (sz -> align -> align -> 'a1) ->
    layout -> 'a1
  
  type product =
    | Coq_product_gvar of gvar
    | Coq_product_fdec of fdec
    | Coq_product_fdef of fdef
  
  val product_rect :
    (gvar -> 'a1) -> (fdec -> 'a1) -> (fdef -> 'a1) -> product -> 'a1
  
  val product_rec :
    (gvar -> 'a1) -> (fdec -> 'a1) -> (fdef -> 'a1) -> product -> 'a1
  
  type layouts = layout list
  
  type products = product list
  
  type coq_module =
    | Coq_module_intro of layouts * products
  
  val module_rect : (layouts -> products -> 'a1) -> coq_module -> 'a1
  
  val module_rec : (layouts -> products -> 'a1) -> coq_module -> 'a1
  
  type insn =
    | Coq_insn_phinode of phinode
    | Coq_insn_cmd of cmd
    | Coq_insn_terminator of terminator
  
  val insn_rect :
    (phinode -> 'a1) -> (cmd -> 'a1) -> (terminator -> 'a1) -> insn -> 'a1
  
  val insn_rec :
    (phinode -> 'a1) -> (cmd -> 'a1) -> (terminator -> 'a1) -> insn -> 'a1
  
  type modules = coq_module list
  
  type usedef_id = id -> id list
  
  type usedef_block = block -> block list
  
  type dt = l -> l list
  
  type ids = id list
  
  type opt_INT = coq_INT option
  
  type opt_l = l option
  
  type opt_id = id option
  
  type opt_typ = typ option
  
  type ls = l list
  
  type insns = insn list
  
  type opt_block = block option
  
  type opt_fdec = fdec option
  
  type opt_fdef = fdef option
  
  type id_binding =
    | Coq_id_binding_none
    | Coq_id_binding_cmd of cmd
    | Coq_id_binding_phinode of phinode
    | Coq_id_binding_terminator of terminator
    | Coq_id_binding_gvar of gvar
    | Coq_id_binding_fdec of fdec
    | Coq_id_binding_arg of arg
  
  val id_binding_rect :
    'a1 -> (cmd -> 'a1) -> (phinode -> 'a1) -> (terminator -> 'a1) -> (gvar
    -> 'a1) -> (fdec -> 'a1) -> (arg -> 'a1) -> id_binding -> 'a1
  
  val id_binding_rec :
    'a1 -> (cmd -> 'a1) -> (phinode -> 'a1) -> (terminator -> 'a1) -> (gvar
    -> 'a1) -> (fdec -> 'a1) -> (arg -> 'a1) -> id_binding -> 'a1
  
  type system = modules
  
  type module_info = (coq_module, (usedef_id, usedef_block) prod) prod
  
  type fdef_info = (fdef, dt) prod
  
  type intrinsic_funs = ids
  
  val map_list_id_l : (id -> l -> 'a1) -> list_id_l -> 'a1 list
  
  val make_list_id_l : (id, l) prod list -> list_id_l
  
  val unmake_list_id_l : list_id_l -> (id, l) prod list
  
  val nth_list_id_l : nat -> list_id_l -> (id, l) prod option
  
  val app_list_id_l : list_id_l -> list_id_l -> list_id_l
  
  val map_list_value : (value -> 'a1) -> list_value -> 'a1 list
  
  val make_list_value : value list -> list_value
  
  val unmake_list_value : list_value -> value list
  
  val nth_list_value : nat -> list_value -> value option
  
  val app_list_value : list_value -> list_value -> list_value
  
  val map_list_const : (const -> 'a1) -> list_const -> 'a1 list
  
  val make_list_const : const list -> list_const
  
  val unmake_list_const : list_const -> const list
  
  val nth_list_const : nat -> list_const -> const option
  
  val app_list_const : list_const -> list_const -> list_const
  
  val map_list_typ : (typ -> 'a1) -> list_typ -> 'a1 list
  
  val make_list_typ : typ list -> list_typ
  
  val unmake_list_typ : list_typ -> typ list
  
  val nth_list_typ : nat -> list_typ -> typ option
  
  val app_list_typ : list_typ -> list_typ -> list_typ
  
  val list_const_rec2 :
    (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const ->
    'a2 -> 'a1) -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) -> 'a2 ->
    (const -> 'a1 -> list_const -> 'a2 -> 'a2) -> list_const -> 'a2
  
  val const_rec2 :
    (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const ->
    'a2 -> 'a1) -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) -> 'a2 ->
    (const -> 'a1 -> list_const -> 'a2 -> 'a2) -> const -> 'a1
  
  val const_mutrec :
    (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const ->
    'a2 -> 'a1) -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) -> 'a2 ->
    (const -> 'a1 -> list_const -> 'a2 -> 'a2) -> (const -> 'a1, list_const
    -> 'a2) prod
  
  val list_typ_rec2 :
    (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ ->
    'a1 -> list_typ -> 'a2 -> 'a1) -> (list_typ -> 'a2 -> 'a1) -> (typ -> 'a1
    -> 'a1) -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> list_typ ->
    'a2
  
  val typ_rec2 :
    (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ ->
    'a1 -> list_typ -> 'a2 -> 'a1) -> (list_typ -> 'a2 -> 'a1) -> (typ -> 'a1
    -> 'a1) -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> typ -> 'a1
  
  val typ_mutrec :
    (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ ->
    'a1 -> list_typ -> 'a2 -> 'a1) -> (list_typ -> 'a2 -> 'a1) -> (typ -> 'a1
    -> 'a1) -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> (typ -> 'a1,
    list_typ -> 'a2) prod
 end

type maddr = nat

type mblock = maddr

type malloca = mblock -> maddr option

type mbyte =
  | Mbyte_var of nat
  | Mbyte_uninit

type mem = { data : (maddr -> mbyte); allocas : malloca }

type mvalue = mbyte list

type event =
  | MkEvent

type trace =
  | Trace_nil
  | Trace_cons of event * trace

type genericValue = mvalue

type gVMap = (LLVMsyntax.id, genericValue) prod list

module SimpleSE : 
 sig 
  type coq_ExecutionContext = { coq_CurBB : LLVMsyntax.block;
                                coq_Locals : gVMap; coq_Allocas : 
                                mblock list }
  
  val coq_ExecutionContext_rect :
    (LLVMsyntax.block -> gVMap -> mblock list -> 'a1) -> coq_ExecutionContext
    -> 'a1
  
  val coq_ExecutionContext_rec :
    (LLVMsyntax.block -> gVMap -> mblock list -> 'a1) -> coq_ExecutionContext
    -> 'a1
  
  val coq_CurBB : coq_ExecutionContext -> LLVMsyntax.block
  
  val coq_Locals : coq_ExecutionContext -> gVMap
  
  val coq_Allocas : coq_ExecutionContext -> mblock list
  
  type coq_State = { coq_Frame : coq_ExecutionContext; coq_Mem : mem }
  
  val coq_State_rect :
    (coq_ExecutionContext -> mem -> 'a1) -> coq_State -> 'a1
  
  val coq_State_rec :
    (coq_ExecutionContext -> mem -> 'a1) -> coq_State -> 'a1
  
  val coq_Frame : coq_State -> coq_ExecutionContext
  
  val coq_Mem : coq_State -> mem
  
  type nbranch =
    LLVMsyntax.cmd
    (* singleton inductive, whose constructor was mkNB *)
  
  val nbranch_rect : (LLVMsyntax.cmd -> __ -> 'a1) -> nbranch -> 'a1
  
  val nbranch_rec : (LLVMsyntax.cmd -> __ -> 'a1) -> nbranch -> 'a1
  
  val nbranching_cmd : nbranch -> LLVMsyntax.cmd
  
  val isCallInst_dec : LLVMsyntax.cmd -> sumbool
  
  val cmd2nbranch : LLVMsyntax.cmd -> nbranch option
  
  val cmds2nbranchs : LLVMsyntax.cmd list -> nbranch list option
  
  val nbranchs2cmds : nbranch list -> LLVMsyntax.cmd list
  
  type subblock = { coq_NBs : nbranch list; call_cmd : LLVMsyntax.cmd }
  
  val subblock_rect :
    (nbranch list -> LLVMsyntax.cmd -> __ -> 'a1) -> subblock -> 'a1
  
  val subblock_rec :
    (nbranch list -> LLVMsyntax.cmd -> __ -> 'a1) -> subblock -> 'a1
  
  val coq_NBs : subblock -> nbranch list
  
  val call_cmd : subblock -> LLVMsyntax.cmd
  
  val cmds2sbs : LLVMsyntax.cmds -> (subblock list, nbranch list) prod
  
  type sterm =
    | Coq_sterm_val of LLVMsyntax.value
    | Coq_sterm_bop of LLVMsyntax.bop * LLVMsyntax.sz * sterm * sterm
    | Coq_sterm_extractvalue of LLVMsyntax.typ * sterm
       * LLVMsyntax.list_const
    | Coq_sterm_insertvalue of LLVMsyntax.typ * sterm * 
       LLVMsyntax.typ * sterm * LLVMsyntax.list_const
    | Coq_sterm_malloc of smem * LLVMsyntax.typ * LLVMsyntax.sz
       * LLVMsyntax.align
    | Coq_sterm_alloca of smem * LLVMsyntax.typ * LLVMsyntax.sz
       * LLVMsyntax.align
    | Coq_sterm_load of smem * LLVMsyntax.typ * sterm
    | Coq_sterm_gep of LLVMsyntax.inbounds * LLVMsyntax.typ * 
       sterm * list_sterm
    | Coq_sterm_ext of LLVMsyntax.extop * LLVMsyntax.typ * 
       sterm * LLVMsyntax.typ
    | Coq_sterm_cast of LLVMsyntax.castop * LLVMsyntax.typ * 
       sterm * LLVMsyntax.typ
    | Coq_sterm_icmp of LLVMsyntax.cond * LLVMsyntax.typ * sterm * sterm
    | Coq_sterm_phi of LLVMsyntax.typ * list_sterm_l
    | Coq_sterm_select of sterm * LLVMsyntax.typ * sterm * sterm
  and list_sterm =
    | Nil_list_sterm
    | Cons_list_sterm of sterm * list_sterm
  and list_sterm_l =
    | Nil_list_sterm_l
    | Cons_list_sterm_l of sterm * LLVMsyntax.l * list_sterm_l
  and smem =
    | Coq_smem_init
    | Coq_smem_malloc of smem * LLVMsyntax.typ * LLVMsyntax.sz
       * LLVMsyntax.align
    | Coq_smem_free of smem * LLVMsyntax.typ * sterm
    | Coq_smem_alloca of smem * LLVMsyntax.typ * LLVMsyntax.sz
       * LLVMsyntax.align
    | Coq_smem_load of smem * LLVMsyntax.typ * sterm
    | Coq_smem_store of smem * LLVMsyntax.typ * sterm * sterm
  and sframe =
    | Coq_sframe_init
    | Coq_sframe_alloca of smem * sframe * LLVMsyntax.typ * 
       LLVMsyntax.sz * LLVMsyntax.align
  
  val sterm_rect :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) -> (smem
    -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) -> (smem
    -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.inbounds ->
    LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm -> 'a1) -> (LLVMsyntax.extop
    -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
    (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ ->
    'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a1) -> (sterm -> 'a1
    -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> sterm -> 'a1
  
  val sterm_rec :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) -> (smem
    -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) -> (smem
    -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.inbounds ->
    LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm -> 'a1) -> (LLVMsyntax.extop
    -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
    (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ ->
    'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a1) -> (sterm -> 'a1
    -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> sterm -> 'a1
  
  val list_sterm_rect :
    'a1 -> (sterm -> list_sterm -> 'a1 -> 'a1) -> list_sterm -> 'a1
  
  val list_sterm_rec :
    'a1 -> (sterm -> list_sterm -> 'a1 -> 'a1) -> list_sterm -> 'a1
  
  val list_sterm_l_rect :
    'a1 -> (sterm -> LLVMsyntax.l -> list_sterm_l -> 'a1 -> 'a1) ->
    list_sterm_l -> 'a1
  
  val list_sterm_l_rec :
    'a1 -> (sterm -> LLVMsyntax.l -> list_sterm_l -> 'a1 -> 'a1) ->
    list_sterm_l -> 'a1
  
  val smem_rect :
    'a1 -> (smem -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
    'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
    'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> sterm -> 'a1) -> smem
    -> 'a1
  
  val smem_rec :
    'a1 -> (smem -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
    'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
    'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> sterm -> 'a1) -> smem
    -> 'a1
  
  val sframe_rect :
    'a1 -> (smem -> sframe -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a1) -> sframe -> 'a1
  
  val sframe_rec :
    'a1 -> (smem -> sframe -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a1) -> sframe -> 'a1
  
  val sframe_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a2 -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ ->
    sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l
    -> 'a3 -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    sterm -> 'a1 -> 'a1) -> 'a2 -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2)
    -> 'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
    'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a4) -> 'a5 -> (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ ->
    LLVMsyntax.sz -> LLVMsyntax.align -> 'a5) -> sframe -> 'a5
  
  val smem_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a2 -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ ->
    sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l
    -> 'a3 -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    sterm -> 'a1 -> 'a1) -> 'a2 -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2)
    -> 'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
    'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a4) -> 'a5 -> (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ ->
    LLVMsyntax.sz -> LLVMsyntax.align -> 'a5) -> smem -> 'a4
  
  val list_sterm_l_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a2 -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ ->
    sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l
    -> 'a3 -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    sterm -> 'a1 -> 'a1) -> 'a2 -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2)
    -> 'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
    'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a4) -> 'a5 -> (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ ->
    LLVMsyntax.sz -> LLVMsyntax.align -> 'a5) -> list_sterm_l -> 'a3
  
  val list_sterm_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a2 -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ ->
    sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l
    -> 'a3 -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    sterm -> 'a1 -> 'a1) -> 'a2 -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2)
    -> 'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
    'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a4) -> 'a5 -> (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ ->
    LLVMsyntax.sz -> LLVMsyntax.align -> 'a5) -> list_sterm -> 'a2
  
  val sterm_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a2 -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ ->
    sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l
    -> 'a3 -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    sterm -> 'a1 -> 'a1) -> 'a2 -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2)
    -> 'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
    'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a4) -> 'a5 -> (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ ->
    LLVMsyntax.sz -> LLVMsyntax.align -> 'a5) -> sterm -> 'a1
  
  val se_mutrec :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a2 -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ ->
    sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l
    -> 'a3 -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    sterm -> 'a1 -> 'a1) -> 'a2 -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2)
    -> 'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
    'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a4) -> 'a5 -> (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ ->
    LLVMsyntax.sz -> LLVMsyntax.align -> 'a5) -> ((((sterm -> 'a1, list_sterm
    -> 'a2) prod, list_sterm_l -> 'a3) prod, smem -> 'a4) prod, sframe ->
    'a5) prod
  
  val map_list_sterm : (sterm -> 'a1) -> list_sterm -> 'a1 list
  
  val make_list_sterm : sterm list -> list_sterm
  
  val unmake_list_sterm : list_sterm -> sterm list
  
  val nth_list_sterm : nat -> list_sterm -> sterm option
  
  val app_list_sterm : list_sterm -> list_sterm -> list_sterm
  
  val map_list_sterm_l :
    (sterm -> LLVMsyntax.l -> 'a1) -> list_sterm_l -> 'a1 list
  
  val make_list_sterm_l : (sterm, LLVMsyntax.l) prod list -> list_sterm_l
  
  val unmake_list_sterm_l : list_sterm_l -> (sterm, LLVMsyntax.l) prod list
  
  val nth_list_sterm_l :
    nat -> list_sterm_l -> (sterm, LLVMsyntax.l) prod option
  
  val app_list_sterm_l : list_sterm_l -> list_sterm_l -> list_sterm_l
  
  type sterminator =
    | Coq_stmn_return of LLVMsyntax.id * LLVMsyntax.typ * sterm
    | Coq_stmn_return_void of LLVMsyntax.id
    | Coq_stmn_br of LLVMsyntax.id * sterm * LLVMsyntax.l * LLVMsyntax.l
    | Coq_stmn_br_uncond of LLVMsyntax.id * LLVMsyntax.l
    | Coq_stmn_unreachable of LLVMsyntax.id
  
  val sterminator_rect :
    (LLVMsyntax.id -> LLVMsyntax.typ -> sterm -> 'a1) -> (LLVMsyntax.id ->
    'a1) -> (LLVMsyntax.id -> sterm -> LLVMsyntax.l -> LLVMsyntax.l -> 'a1)
    -> (LLVMsyntax.id -> LLVMsyntax.l -> 'a1) -> (LLVMsyntax.id -> 'a1) ->
    sterminator -> 'a1
  
  val sterminator_rec :
    (LLVMsyntax.id -> LLVMsyntax.typ -> sterm -> 'a1) -> (LLVMsyntax.id ->
    'a1) -> (LLVMsyntax.id -> sterm -> LLVMsyntax.l -> LLVMsyntax.l -> 'a1)
    -> (LLVMsyntax.id -> LLVMsyntax.l -> 'a1) -> (LLVMsyntax.id -> 'a1) ->
    sterminator -> 'a1
  
  type scall =
    | Coq_stmn_call of LLVMsyntax.id * LLVMsyntax.noret * 
       LLVMsyntax.tailc * LLVMsyntax.typ * LLVMsyntax.id
       * (LLVMsyntax.typ, sterm) prod list
  
  val scall_rect :
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.tailc -> LLVMsyntax.typ
    -> LLVMsyntax.id -> (LLVMsyntax.typ, sterm) prod list -> 'a1) -> scall ->
    'a1
  
  val scall_rec :
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.tailc -> LLVMsyntax.typ
    -> LLVMsyntax.id -> (LLVMsyntax.typ, sterm) prod list -> 'a1) -> scall ->
    'a1
  
  type smap = (AtomImpl.atom, sterm) prod list
  
  type sstate = { coq_STerms : smap; coq_SMem : smem; coq_SFrame : 
                  sframe; coq_SEffects : sterm list }
  
  val sstate_rect :
    (smap -> smem -> sframe -> sterm list -> 'a1) -> sstate -> 'a1
  
  val sstate_rec :
    (smap -> smem -> sframe -> sterm list -> 'a1) -> sstate -> 'a1
  
  val coq_STerms : sstate -> smap
  
  val coq_SMem : sstate -> smem
  
  val coq_SFrame : sstate -> sframe
  
  val coq_SEffects : sstate -> sterm list
  
  val sstate_init : sstate
  
  val lookupSmap : smap -> LLVMsyntax.id -> sterm
  
  val value2Sterm : smap -> LLVMsyntax.value -> sterm
  
  val list_param__list_typ_subst_sterm :
    LLVMsyntax.params -> smap -> (LLVMsyntax.typ, sterm) prod list
  
  val se_cmd : sstate -> nbranch -> sstate
  
  val _se_phinodes : sstate -> sstate -> LLVMsyntax.phinode list -> sstate
  
  val se_phinodes : sstate -> LLVMsyntax.phinode list -> sstate
  
  val se_cmds : sstate -> nbranch list -> sstate
  
  val se_terminator : sstate -> LLVMsyntax.terminator -> sterminator
  
  val se_call : sstate -> LLVMsyntax.cmd -> scall
  
  val seffects_denote_trace_rect : 'a1 -> sterm list -> trace -> 'a1
  
  val seffects_denote_trace_rec : 'a1 -> sterm list -> trace -> 'a1
  
  val subst_tt : LLVMsyntax.id -> sterm -> sterm -> sterm
  
  val subst_tlt : LLVMsyntax.id -> sterm -> list_sterm -> list_sterm
  
  val subst_tltl : LLVMsyntax.id -> sterm -> list_sterm_l -> list_sterm_l
  
  val subst_tm : LLVMsyntax.id -> sterm -> smem -> smem
  
  val subst_mt : smap -> sterm -> sterm
  
  val subst_mm : smap -> smem -> smem
 end

val sumbool2bool : sumbool -> bool

type typ_dec_prop = LLVMsyntax.typ -> sumbool

type list_typ_dec_prop = LLVMsyntax.list_typ -> sumbool

val typ_mutrec_dec :
  (LLVMsyntax.typ -> typ_dec_prop, LLVMsyntax.list_typ -> list_typ_dec_prop)
  prod

type const_dec_prop = LLVMsyntax.const -> sumbool

type list_const_dec_prop = LLVMsyntax.list_const -> sumbool

val const_mutrec_dec :
  (LLVMsyntax.const -> const_dec_prop, LLVMsyntax.list_const ->
  list_const_dec_prop) prod

val value_dec : LLVMsyntax.value -> LLVMsyntax.value -> sumbool

val list_value_dec :
  LLVMsyntax.list_value -> LLVMsyntax.list_value -> sumbool

val bop_dec : LLVMsyntax.bop -> LLVMsyntax.bop -> sumbool

val extop_dec : LLVMsyntax.extop -> LLVMsyntax.extop -> sumbool

val castop_dec : LLVMsyntax.castop -> LLVMsyntax.castop -> sumbool

val cond_dec : LLVMsyntax.cond -> LLVMsyntax.cond -> sumbool

type sterm_dec_prop = SimpleSE.sterm -> sumbool

type list_sterm_dec_prop = SimpleSE.list_sterm -> sumbool

type list_sterm_l_dec_prop = SimpleSE.list_sterm_l -> sumbool

type smem_dec_prop = SimpleSE.smem -> sumbool

type sframe_dec_prop = SimpleSE.sframe -> sumbool

val se_dec :
  ((((SimpleSE.sterm -> sterm_dec_prop, SimpleSE.list_sterm ->
  list_sterm_dec_prop) prod, SimpleSE.list_sterm_l -> list_sterm_l_dec_prop)
  prod, SimpleSE.smem -> smem_dec_prop) prod, SimpleSE.sframe ->
  sframe_dec_prop) prod

val smap_dec : SimpleSE.smap -> SimpleSE.smap -> sumbool

val sterms_dec : SimpleSE.sterm list -> SimpleSE.sterm list -> sumbool

val sstate_dec : SimpleSE.sstate -> SimpleSE.sstate -> sumbool

val params_dec : LLVMsyntax.params -> LLVMsyntax.params -> sumbool

val cmd_dec : LLVMsyntax.cmd -> LLVMsyntax.cmd -> sumbool

val terminator_dec :
  LLVMsyntax.terminator -> LLVMsyntax.terminator -> sumbool

val list_id_l_dec : LLVMsyntax.list_id_l -> LLVMsyntax.list_id_l -> sumbool

val phinode_dec : LLVMsyntax.phinode -> LLVMsyntax.phinode -> sumbool

val arg_dec : LLVMsyntax.arg -> LLVMsyntax.arg -> sumbool

val args_dec : LLVMsyntax.args -> LLVMsyntax.args -> sumbool

val fheader_dec : LLVMsyntax.fheader -> LLVMsyntax.fheader -> sumbool

val gvar_dec : LLVMsyntax.gvar -> LLVMsyntax.gvar -> sumbool

val fdec_dec : LLVMsyntax.fdec -> LLVMsyntax.fdec -> sumbool

val layout_dec : LLVMsyntax.layout -> LLVMsyntax.layout -> sumbool

val layouts_dec : LLVMsyntax.layouts -> LLVMsyntax.layouts -> sumbool

val tv_cmds : SimpleSE.nbranch list -> SimpleSE.nbranch list -> bool

val tv_subblock : SimpleSE.subblock -> SimpleSE.subblock -> bool

val tv_subblocks : SimpleSE.subblock list -> SimpleSE.subblock list -> bool

val tv_phinodes : LLVMsyntax.phinodes -> LLVMsyntax.phinodes -> bool

val tv_block : LLVMsyntax.block -> LLVMsyntax.block -> bool

val tv_blocks : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool

val tv_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool

val tv_products : LLVMsyntax.products -> LLVMsyntax.products -> bool

val tv_module : LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool

val tv_system : LLVMsyntax.system -> LLVMsyntax.system -> bool

