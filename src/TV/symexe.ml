type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val eq_nat_dec : nat -> nat -> sumbool **)

let rec eq_nat_dec n m =
  match n with
    | O -> (match m with
              | O -> Left
              | S m0 -> Right)
    | S n0 -> (match m with
                 | O -> Right
                 | S m0 -> eq_nat_dec n0 m0)

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
    | O -> m
    | S n' -> (match m with
                 | O -> n
                 | S m' -> S (max n' m'))

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
    | True -> (match b2 with
                 | True -> Left
                 | False -> Right)
    | False -> (match b2 with
                  | True -> Right
                  | False -> Left)

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

module AtomImpl = 
 struct 
  type atom = nat
  
  (** val eq_atom_dec : atom -> atom -> sumbool **)
  
  let eq_atom_dec n m =
    eq_nat_dec n m
  
  (** val nat_list_max : nat list -> nat **)
  
  let rec nat_list_max = function
    | Nil -> O
    | Cons (a, l1) -> max a (nat_list_max l1)
  
  (** val atom_fresh_for_list : atom list -> atom **)
  
  let atom_fresh_for_list xs =
    S (nat_list_max xs)
 end

(** val eqDec_atom : AtomImpl.atom eqDec **)

let eqDec_atom x y =
  AtomImpl.eq_atom_dec x y

type 'x assocList = (AtomImpl.atom, 'x) prod list

(** val updateAddAL :
    'a1 assocList -> AtomImpl.atom -> 'a1 -> 'a1 assocList **)

let rec updateAddAL m i0 gv =
  match m with
    | Nil -> Cons ((Pair (i0, gv)), Nil)
    | Cons (p, m') ->
        let Pair (i', gv') = p in
        (match eqDec_atom i0 i' with
           | Left -> Cons ((Pair (i', gv)), m')
           | Right -> Cons ((Pair (i', gv')), (updateAddAL m' i0 gv)))

(** val updateAL : 'a1 assocList -> AtomImpl.atom -> 'a1 -> 'a1 assocList **)

let rec updateAL m i0 gv =
  match m with
    | Nil -> Nil
    | Cons (p, m') ->
        let Pair (i', gv') = p in
        (match eqDec_atom i0 i' with
           | Left -> Cons ((Pair (i', gv)), m')
           | Right -> Cons ((Pair (i', gv')), (updateAL m' i0 gv)))

module LLVMsyntax = 
 struct 
  (** val last_opt : 'a1 list -> 'a1 option **)
  
  let rec last_opt = function
    | Nil -> None
    | Cons (a, l') ->
        (match l' with
           | Nil -> Some a
           | Cons (a0, l1) -> last_opt l')
  
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
  
  (** val typ_rect :
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ
      -> 'a1 -> list_typ -> 'a1) -> (list_typ -> 'a1) -> (typ -> 'a1 -> 'a1)
      -> typ -> 'a1 **)
  
  let rec typ_rect f f0 f1 f2 f3 f4 f5 f6 = function
    | Coq_typ_int s -> f s
    | Coq_typ_void -> f0
    | Coq_typ_label -> f1
    | Coq_typ_metadata -> f2
    | Coq_typ_array (s, t0) -> f3 s t0 (typ_rect f f0 f1 f2 f3 f4 f5 f6 t0)
    | Coq_typ_function (t0, l0) ->
        f4 t0 (typ_rect f f0 f1 f2 f3 f4 f5 f6 t0) l0
    | Coq_typ_struct l0 -> f5 l0
    | Coq_typ_pointer t0 -> f6 t0 (typ_rect f f0 f1 f2 f3 f4 f5 f6 t0)
  
  (** val typ_rec :
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ
      -> 'a1 -> list_typ -> 'a1) -> (list_typ -> 'a1) -> (typ -> 'a1 -> 'a1)
      -> typ -> 'a1 **)
  
  let rec typ_rec f f0 f1 f2 f3 f4 f5 f6 = function
    | Coq_typ_int s -> f s
    | Coq_typ_void -> f0
    | Coq_typ_label -> f1
    | Coq_typ_metadata -> f2
    | Coq_typ_array (s, t0) -> f3 s t0 (typ_rec f f0 f1 f2 f3 f4 f5 f6 t0)
    | Coq_typ_function (t0, l0) ->
        f4 t0 (typ_rec f f0 f1 f2 f3 f4 f5 f6 t0) l0
    | Coq_typ_struct l0 -> f5 l0
    | Coq_typ_pointer t0 -> f6 t0 (typ_rec f f0 f1 f2 f3 f4 f5 f6 t0)
  
  (** val list_typ_rect :
      'a1 -> (typ -> list_typ -> 'a1 -> 'a1) -> list_typ -> 'a1 **)
  
  let rec list_typ_rect f f0 = function
    | Nil_list_typ -> f
    | Cons_list_typ (t, l1) -> f0 t l1 (list_typ_rect f f0 l1)
  
  (** val list_typ_rec :
      'a1 -> (typ -> list_typ -> 'a1 -> 'a1) -> list_typ -> 'a1 **)
  
  let rec list_typ_rec f f0 = function
    | Nil_list_typ -> f
    | Cons_list_typ (t, l1) -> f0 t l1 (list_typ_rec f f0 l1)
  
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
  
  (** val const_rect :
      (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const
      -> 'a1) -> (list_const -> 'a1) -> (typ -> id -> 'a1) -> const -> 'a1 **)
  
  let const_rect f f0 f1 f2 f3 f4 = function
    | Coq_const_int (x, x0) -> f x x0
    | Coq_const_undef x -> f0 x
    | Coq_const_null x -> f1 x
    | Coq_const_arr x -> f2 x
    | Coq_const_struct x -> f3 x
    | Coq_const_gid (x, x0) -> f4 x x0
  
  (** val const_rec :
      (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const
      -> 'a1) -> (list_const -> 'a1) -> (typ -> id -> 'a1) -> const -> 'a1 **)
  
  let const_rec f f0 f1 f2 f3 f4 = function
    | Coq_const_int (x, x0) -> f x x0
    | Coq_const_undef x -> f0 x
    | Coq_const_null x -> f1 x
    | Coq_const_arr x -> f2 x
    | Coq_const_struct x -> f3 x
    | Coq_const_gid (x, x0) -> f4 x x0
  
  (** val list_const_rect :
      'a1 -> (const -> list_const -> 'a1 -> 'a1) -> list_const -> 'a1 **)
  
  let rec list_const_rect f f0 = function
    | Nil_list_const -> f
    | Cons_list_const (c, l1) -> f0 c l1 (list_const_rect f f0 l1)
  
  (** val list_const_rec :
      'a1 -> (const -> list_const -> 'a1 -> 'a1) -> list_const -> 'a1 **)
  
  let rec list_const_rec f f0 = function
    | Nil_list_const -> f
    | Cons_list_const (c, l1) -> f0 c l1 (list_const_rec f f0 l1)
  
  type value =
    | Coq_value_id of id
    | Coq_value_const of const
  
  (** val value_rect : (id -> 'a1) -> (const -> 'a1) -> value -> 'a1 **)
  
  let value_rect f f0 = function
    | Coq_value_id x -> f x
    | Coq_value_const x -> f0 x
  
  (** val value_rec : (id -> 'a1) -> (const -> 'a1) -> value -> 'a1 **)
  
  let value_rec f f0 = function
    | Coq_value_id x -> f x
    | Coq_value_const x -> f0 x
  
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
  
  (** val cond_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      cond -> 'a1 **)
  
  let cond_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
    | Coq_cond_eq -> f
    | Coq_cond_ne -> f0
    | Coq_cond_ugt -> f1
    | Coq_cond_uge -> f2
    | Coq_cond_ult -> f3
    | Coq_cond_ule -> f4
    | Coq_cond_sgt -> f5
    | Coq_cond_sge -> f6
    | Coq_cond_slt -> f7
    | Coq_cond_sle -> f8
  
  (** val cond_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      cond -> 'a1 **)
  
  let cond_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
    | Coq_cond_eq -> f
    | Coq_cond_ne -> f0
    | Coq_cond_ugt -> f1
    | Coq_cond_uge -> f2
    | Coq_cond_ult -> f3
    | Coq_cond_ule -> f4
    | Coq_cond_sgt -> f5
    | Coq_cond_sge -> f6
    | Coq_cond_slt -> f7
    | Coq_cond_sle -> f8
  
  type bop =
    | Coq_bop_add
    | Coq_bop_lshr
    | Coq_bop_and
    | Coq_bop_or
  
  (** val bop_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop -> 'a1 **)
  
  let bop_rect f f0 f1 f2 = function
    | Coq_bop_add -> f
    | Coq_bop_lshr -> f0
    | Coq_bop_and -> f1
    | Coq_bop_or -> f2
  
  (** val bop_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop -> 'a1 **)
  
  let bop_rec f f0 f1 f2 = function
    | Coq_bop_add -> f
    | Coq_bop_lshr -> f0
    | Coq_bop_and -> f1
    | Coq_bop_or -> f2
  
  type extop =
    | Coq_extop_z
    | Coq_extop_s
  
  (** val extop_rect : 'a1 -> 'a1 -> extop -> 'a1 **)
  
  let extop_rect f f0 = function
    | Coq_extop_z -> f
    | Coq_extop_s -> f0
  
  (** val extop_rec : 'a1 -> 'a1 -> extop -> 'a1 **)
  
  let extop_rec f f0 = function
    | Coq_extop_z -> f
    | Coq_extop_s -> f0
  
  type castop =
    | Coq_castop_fptoui
    | Coq_castop_fptosi
    | Coq_castop_uitofp
    | Coq_castop_sitofp
    | Coq_castop_ptrtoint
    | Coq_castop_inttoptr
    | Coq_castop_bitcast
  
  (** val castop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> castop -> 'a1 **)
  
  let castop_rect f f0 f1 f2 f3 f4 f5 = function
    | Coq_castop_fptoui -> f
    | Coq_castop_fptosi -> f0
    | Coq_castop_uitofp -> f1
    | Coq_castop_sitofp -> f2
    | Coq_castop_ptrtoint -> f3
    | Coq_castop_inttoptr -> f4
    | Coq_castop_bitcast -> f5
  
  (** val castop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> castop -> 'a1 **)
  
  let castop_rec f f0 f1 f2 f3 f4 f5 = function
    | Coq_castop_fptoui -> f
    | Coq_castop_fptosi -> f0
    | Coq_castop_uitofp -> f1
    | Coq_castop_sitofp -> f2
    | Coq_castop_ptrtoint -> f3
    | Coq_castop_inttoptr -> f4
    | Coq_castop_bitcast -> f5
  
  type inbounds = bool
  
  type tailc = bool
  
  type noret = bool
  
  type list_value =
    | Nil_list_value
    | Cons_list_value of value * list_value
  
  (** val list_value_rect :
      'a1 -> (value -> list_value -> 'a1 -> 'a1) -> list_value -> 'a1 **)
  
  let rec list_value_rect f f0 = function
    | Nil_list_value -> f
    | Cons_list_value (v, l1) -> f0 v l1 (list_value_rect f f0 l1)
  
  (** val list_value_rec :
      'a1 -> (value -> list_value -> 'a1 -> 'a1) -> list_value -> 'a1 **)
  
  let rec list_value_rec f f0 = function
    | Nil_list_value -> f
    | Cons_list_value (v, l1) -> f0 v l1 (list_value_rec f f0 l1)
  
  type list_id_l =
    | Nil_list_id_l
    | Cons_list_id_l of id * l * list_id_l
  
  (** val list_id_l_rect :
      'a1 -> (id -> l -> list_id_l -> 'a1 -> 'a1) -> list_id_l -> 'a1 **)
  
  let rec list_id_l_rect f f0 = function
    | Nil_list_id_l -> f
    | Cons_list_id_l (i0, l1, l2) -> f0 i0 l1 l2 (list_id_l_rect f f0 l2)
  
  (** val list_id_l_rec :
      'a1 -> (id -> l -> list_id_l -> 'a1 -> 'a1) -> list_id_l -> 'a1 **)
  
  let rec list_id_l_rec f f0 = function
    | Nil_list_id_l -> f
    | Cons_list_id_l (i0, l1, l2) -> f0 i0 l1 l2 (list_id_l_rec f f0 l2)
  
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
  
  (** val cmd_rect :
      (id -> bop -> sz -> value -> value -> 'a1) -> (id -> typ -> value ->
      list_const -> 'a1) -> (id -> typ -> value -> typ -> value -> list_const
      -> 'a1) -> (id -> typ -> sz -> align -> 'a1) -> (id -> typ -> value ->
      'a1) -> (id -> typ -> sz -> align -> 'a1) -> (id -> typ -> value ->
      'a1) -> (id -> typ -> value -> value -> 'a1) -> (id -> inbounds -> typ
      -> value -> list_value -> 'a1) -> (id -> extop -> typ -> value -> typ
      -> 'a1) -> (id -> castop -> typ -> value -> typ -> 'a1) -> (id -> cond
      -> typ -> value -> value -> 'a1) -> (id -> value -> typ -> value ->
      value -> 'a1) -> (id -> noret -> tailc -> typ -> id -> params -> 'a1)
      -> cmd -> 'a1 **)
  
  let cmd_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
    | Coq_insn_bop (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3
    | Coq_insn_extractvalue (x, x0, x1, x2) -> f0 x x0 x1 x2
    | Coq_insn_insertvalue (x, x0, x1, x2, x3, x4) -> f1 x x0 x1 x2 x3 x4
    | Coq_insn_malloc (x, x0, x1, x2) -> f2 x x0 x1 x2
    | Coq_insn_free (x, x0, x1) -> f3 x x0 x1
    | Coq_insn_alloca (x, x0, x1, x2) -> f4 x x0 x1 x2
    | Coq_insn_load (x, x0, x1) -> f5 x x0 x1
    | Coq_insn_store (x, x0, x1, x2) -> f6 x x0 x1 x2
    | Coq_insn_gep (x, x0, x1, x2, x3) -> f7 x x0 x1 x2 x3
    | Coq_insn_ext (x, x0, x1, x2, x3) -> f8 x x0 x1 x2 x3
    | Coq_insn_cast (x, x0, x1, x2, x3) -> f9 x x0 x1 x2 x3
    | Coq_insn_icmp (x, x0, x1, x2, x3) -> f10 x x0 x1 x2 x3
    | Coq_insn_select (x, x0, x1, x2, x3) -> f11 x x0 x1 x2 x3
    | Coq_insn_call (x, x0, x1, x2, x3, x4) -> f12 x x0 x1 x2 x3 x4
  
  (** val cmd_rec :
      (id -> bop -> sz -> value -> value -> 'a1) -> (id -> typ -> value ->
      list_const -> 'a1) -> (id -> typ -> value -> typ -> value -> list_const
      -> 'a1) -> (id -> typ -> sz -> align -> 'a1) -> (id -> typ -> value ->
      'a1) -> (id -> typ -> sz -> align -> 'a1) -> (id -> typ -> value ->
      'a1) -> (id -> typ -> value -> value -> 'a1) -> (id -> inbounds -> typ
      -> value -> list_value -> 'a1) -> (id -> extop -> typ -> value -> typ
      -> 'a1) -> (id -> castop -> typ -> value -> typ -> 'a1) -> (id -> cond
      -> typ -> value -> value -> 'a1) -> (id -> value -> typ -> value ->
      value -> 'a1) -> (id -> noret -> tailc -> typ -> id -> params -> 'a1)
      -> cmd -> 'a1 **)
  
  let cmd_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
    | Coq_insn_bop (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3
    | Coq_insn_extractvalue (x, x0, x1, x2) -> f0 x x0 x1 x2
    | Coq_insn_insertvalue (x, x0, x1, x2, x3, x4) -> f1 x x0 x1 x2 x3 x4
    | Coq_insn_malloc (x, x0, x1, x2) -> f2 x x0 x1 x2
    | Coq_insn_free (x, x0, x1) -> f3 x x0 x1
    | Coq_insn_alloca (x, x0, x1, x2) -> f4 x x0 x1 x2
    | Coq_insn_load (x, x0, x1) -> f5 x x0 x1
    | Coq_insn_store (x, x0, x1, x2) -> f6 x x0 x1 x2
    | Coq_insn_gep (x, x0, x1, x2, x3) -> f7 x x0 x1 x2 x3
    | Coq_insn_ext (x, x0, x1, x2, x3) -> f8 x x0 x1 x2 x3
    | Coq_insn_cast (x, x0, x1, x2, x3) -> f9 x x0 x1 x2 x3
    | Coq_insn_icmp (x, x0, x1, x2, x3) -> f10 x x0 x1 x2 x3
    | Coq_insn_select (x, x0, x1, x2, x3) -> f11 x x0 x1 x2 x3
    | Coq_insn_call (x, x0, x1, x2, x3, x4) -> f12 x x0 x1 x2 x3 x4
  
  type phinode =
    | Coq_insn_phi of id * typ * list_id_l
  
  (** val phinode_rect :
      (id -> typ -> list_id_l -> 'a1) -> phinode -> 'a1 **)
  
  let phinode_rect f = function
    | Coq_insn_phi (x, x0, x1) -> f x x0 x1
  
  (** val phinode_rec : (id -> typ -> list_id_l -> 'a1) -> phinode -> 'a1 **)
  
  let phinode_rec f = function
    | Coq_insn_phi (x, x0, x1) -> f x x0 x1
  
  type arg = (typ, id) prod
  
  type terminator =
    | Coq_insn_return of id * typ * value
    | Coq_insn_return_void of id
    | Coq_insn_br of id * value * l * l
    | Coq_insn_br_uncond of id * l
    | Coq_insn_unreachable of id
  
  (** val terminator_rect :
      (id -> typ -> value -> 'a1) -> (id -> 'a1) -> (id -> value -> l -> l ->
      'a1) -> (id -> l -> 'a1) -> (id -> 'a1) -> terminator -> 'a1 **)
  
  let terminator_rect f f0 f1 f2 f3 = function
    | Coq_insn_return (x, x0, x1) -> f x x0 x1
    | Coq_insn_return_void x -> f0 x
    | Coq_insn_br (x, x0, x1, x2) -> f1 x x0 x1 x2
    | Coq_insn_br_uncond (x, x0) -> f2 x x0
    | Coq_insn_unreachable x -> f3 x
  
  (** val terminator_rec :
      (id -> typ -> value -> 'a1) -> (id -> 'a1) -> (id -> value -> l -> l ->
      'a1) -> (id -> l -> 'a1) -> (id -> 'a1) -> terminator -> 'a1 **)
  
  let terminator_rec f f0 f1 f2 f3 = function
    | Coq_insn_return (x, x0, x1) -> f x x0 x1
    | Coq_insn_return_void x -> f0 x
    | Coq_insn_br (x, x0, x1, x2) -> f1 x x0 x1 x2
    | Coq_insn_br_uncond (x, x0) -> f2 x x0
    | Coq_insn_unreachable x -> f3 x
  
  type cmds = cmd list
  
  type phinodes = phinode list
  
  type args = (typ, id) prod list
  
  type block =
    | Coq_block_intro of l * phinodes * cmds * terminator
  
  (** val block_rect :
      (l -> phinodes -> cmds -> terminator -> 'a1) -> block -> 'a1 **)
  
  let block_rect f = function
    | Coq_block_intro (x, x0, x1, x2) -> f x x0 x1 x2
  
  (** val block_rec :
      (l -> phinodes -> cmds -> terminator -> 'a1) -> block -> 'a1 **)
  
  let block_rec f = function
    | Coq_block_intro (x, x0, x1, x2) -> f x x0 x1 x2
  
  type fheader =
    | Coq_fheader_intro of typ * id * args
  
  (** val fheader_rect : (typ -> id -> args -> 'a1) -> fheader -> 'a1 **)
  
  let fheader_rect f = function
    | Coq_fheader_intro (x, x0, x1) -> f x x0 x1
  
  (** val fheader_rec : (typ -> id -> args -> 'a1) -> fheader -> 'a1 **)
  
  let fheader_rec f = function
    | Coq_fheader_intro (x, x0, x1) -> f x x0 x1
  
  type blocks = block list
  
  type fdec =
    fheader
    (* singleton inductive, whose constructor was fdec_intro *)
  
  (** val fdec_rect : (fheader -> 'a1) -> fdec -> 'a1 **)
  
  let fdec_rect f f0 =
    f f0
  
  (** val fdec_rec : (fheader -> 'a1) -> fdec -> 'a1 **)
  
  let fdec_rec f f0 =
    f f0
  
  type fdef =
    | Coq_fdef_intro of fheader * blocks
  
  (** val fdef_rect : (fheader -> blocks -> 'a1) -> fdef -> 'a1 **)
  
  let fdef_rect f = function
    | Coq_fdef_intro (x, x0) -> f x x0
  
  (** val fdef_rec : (fheader -> blocks -> 'a1) -> fdef -> 'a1 **)
  
  let fdef_rec f = function
    | Coq_fdef_intro (x, x0) -> f x x0
  
  type gvar =
    | Coq_gvar_intro of id * typ * const * align
  
  (** val gvar_rect : (id -> typ -> const -> align -> 'a1) -> gvar -> 'a1 **)
  
  let gvar_rect f = function
    | Coq_gvar_intro (x, x0, x1, x2) -> f x x0 x1 x2
  
  (** val gvar_rec : (id -> typ -> const -> align -> 'a1) -> gvar -> 'a1 **)
  
  let gvar_rec f = function
    | Coq_gvar_intro (x, x0, x1, x2) -> f x x0 x1 x2
  
  type layout =
    | Coq_layout_be
    | Coq_layout_le
    | Coq_layout_ptr of sz * align * align
    | Coq_layout_int of sz * align * align
    | Coq_layout_aggr of sz * align * align
    | Coq_layout_stack of sz * align * align
  
  (** val layout_rect :
      'a1 -> 'a1 -> (sz -> align -> align -> 'a1) -> (sz -> align -> align ->
      'a1) -> (sz -> align -> align -> 'a1) -> (sz -> align -> align -> 'a1)
      -> layout -> 'a1 **)
  
  let layout_rect f f0 f1 f2 f3 f4 = function
    | Coq_layout_be -> f
    | Coq_layout_le -> f0
    | Coq_layout_ptr (x, x0, x1) -> f1 x x0 x1
    | Coq_layout_int (x, x0, x1) -> f2 x x0 x1
    | Coq_layout_aggr (x, x0, x1) -> f3 x x0 x1
    | Coq_layout_stack (x, x0, x1) -> f4 x x0 x1
  
  (** val layout_rec :
      'a1 -> 'a1 -> (sz -> align -> align -> 'a1) -> (sz -> align -> align ->
      'a1) -> (sz -> align -> align -> 'a1) -> (sz -> align -> align -> 'a1)
      -> layout -> 'a1 **)
  
  let layout_rec f f0 f1 f2 f3 f4 = function
    | Coq_layout_be -> f
    | Coq_layout_le -> f0
    | Coq_layout_ptr (x, x0, x1) -> f1 x x0 x1
    | Coq_layout_int (x, x0, x1) -> f2 x x0 x1
    | Coq_layout_aggr (x, x0, x1) -> f3 x x0 x1
    | Coq_layout_stack (x, x0, x1) -> f4 x x0 x1
  
  type product =
    | Coq_product_gvar of gvar
    | Coq_product_fdec of fdec
    | Coq_product_fdef of fdef
  
  (** val product_rect :
      (gvar -> 'a1) -> (fdec -> 'a1) -> (fdef -> 'a1) -> product -> 'a1 **)
  
  let product_rect f f0 f1 = function
    | Coq_product_gvar x -> f x
    | Coq_product_fdec x -> f0 x
    | Coq_product_fdef x -> f1 x
  
  (** val product_rec :
      (gvar -> 'a1) -> (fdec -> 'a1) -> (fdef -> 'a1) -> product -> 'a1 **)
  
  let product_rec f f0 f1 = function
    | Coq_product_gvar x -> f x
    | Coq_product_fdec x -> f0 x
    | Coq_product_fdef x -> f1 x
  
  type layouts = layout list
  
  type products = product list
  
  type coq_module =
    | Coq_module_intro of layouts * products
  
  (** val module_rect : (layouts -> products -> 'a1) -> coq_module -> 'a1 **)
  
  let module_rect f = function
    | Coq_module_intro (x, x0) -> f x x0
  
  (** val module_rec : (layouts -> products -> 'a1) -> coq_module -> 'a1 **)
  
  let module_rec f = function
    | Coq_module_intro (x, x0) -> f x x0
  
  type insn =
    | Coq_insn_phinode of phinode
    | Coq_insn_cmd of cmd
    | Coq_insn_terminator of terminator
  
  (** val insn_rect :
      (phinode -> 'a1) -> (cmd -> 'a1) -> (terminator -> 'a1) -> insn -> 'a1 **)
  
  let insn_rect f f0 f1 = function
    | Coq_insn_phinode x -> f x
    | Coq_insn_cmd x -> f0 x
    | Coq_insn_terminator x -> f1 x
  
  (** val insn_rec :
      (phinode -> 'a1) -> (cmd -> 'a1) -> (terminator -> 'a1) -> insn -> 'a1 **)
  
  let insn_rec f f0 f1 = function
    | Coq_insn_phinode x -> f x
    | Coq_insn_cmd x -> f0 x
    | Coq_insn_terminator x -> f1 x
  
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
  
  (** val id_binding_rect :
      'a1 -> (cmd -> 'a1) -> (phinode -> 'a1) -> (terminator -> 'a1) -> (gvar
      -> 'a1) -> (fdec -> 'a1) -> (arg -> 'a1) -> id_binding -> 'a1 **)
  
  let id_binding_rect f f0 f1 f2 f3 f4 f5 = function
    | Coq_id_binding_none -> f
    | Coq_id_binding_cmd x -> f0 x
    | Coq_id_binding_phinode x -> f1 x
    | Coq_id_binding_terminator x -> f2 x
    | Coq_id_binding_gvar x -> f3 x
    | Coq_id_binding_fdec x -> f4 x
    | Coq_id_binding_arg x -> f5 x
  
  (** val id_binding_rec :
      'a1 -> (cmd -> 'a1) -> (phinode -> 'a1) -> (terminator -> 'a1) -> (gvar
      -> 'a1) -> (fdec -> 'a1) -> (arg -> 'a1) -> id_binding -> 'a1 **)
  
  let id_binding_rec f f0 f1 f2 f3 f4 f5 = function
    | Coq_id_binding_none -> f
    | Coq_id_binding_cmd x -> f0 x
    | Coq_id_binding_phinode x -> f1 x
    | Coq_id_binding_terminator x -> f2 x
    | Coq_id_binding_gvar x -> f3 x
    | Coq_id_binding_fdec x -> f4 x
    | Coq_id_binding_arg x -> f5 x
  
  type system = modules
  
  type module_info = (coq_module, (usedef_id, usedef_block) prod) prod
  
  type fdef_info = (fdef, dt) prod
  
  type intrinsic_funs = ids
  
  (** val map_list_id_l : (id -> l -> 'a1) -> list_id_l -> 'a1 list **)
  
  let rec map_list_id_l f = function
    | Nil_list_id_l -> Nil
    | Cons_list_id_l (h0, h1, tl_) -> Cons ((f h0 h1), (map_list_id_l f tl_))
  
  (** val make_list_id_l : (id, l) prod list -> list_id_l **)
  
  let rec make_list_id_l = function
    | Nil -> Nil_list_id_l
    | Cons (p, tl_) ->
        let Pair (h0, h1) = p in
        Cons_list_id_l (h0, h1, (make_list_id_l tl_))
  
  (** val unmake_list_id_l : list_id_l -> (id, l) prod list **)
  
  let rec unmake_list_id_l = function
    | Nil_list_id_l -> Nil
    | Cons_list_id_l (h0, h1, tl_) -> Cons ((Pair (h0, h1)),
        (unmake_list_id_l tl_))
  
  (** val nth_list_id_l : nat -> list_id_l -> (id, l) prod option **)
  
  let rec nth_list_id_l n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_id_l -> None
             | Cons_list_id_l (h0, h1, tl_) -> Some (Pair (h0, h1)))
      | S m ->
          (match l0 with
             | Nil_list_id_l -> None
             | Cons_list_id_l (h0, h1, tl_) -> nth_list_id_l m tl_)
  
  (** val app_list_id_l : list_id_l -> list_id_l -> list_id_l **)
  
  let rec app_list_id_l l0 m =
    match l0 with
      | Nil_list_id_l -> m
      | Cons_list_id_l (h0, h1, tl_) -> Cons_list_id_l (h0, h1,
          (app_list_id_l tl_ m))
  
  (** val map_list_value : (value -> 'a1) -> list_value -> 'a1 list **)
  
  let rec map_list_value f = function
    | Nil_list_value -> Nil
    | Cons_list_value (h, tl_) -> Cons ((f h), (map_list_value f tl_))
  
  (** val make_list_value : value list -> list_value **)
  
  let rec make_list_value = function
    | Nil -> Nil_list_value
    | Cons (h, tl_) -> Cons_list_value (h, (make_list_value tl_))
  
  (** val unmake_list_value : list_value -> value list **)
  
  let rec unmake_list_value = function
    | Nil_list_value -> Nil
    | Cons_list_value (h, tl_) -> Cons (h, (unmake_list_value tl_))
  
  (** val nth_list_value : nat -> list_value -> value option **)
  
  let rec nth_list_value n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_value -> None
             | Cons_list_value (h, tl_) -> Some h)
      | S m ->
          (match l0 with
             | Nil_list_value -> None
             | Cons_list_value (h, tl_) -> nth_list_value m tl_)
  
  (** val app_list_value : list_value -> list_value -> list_value **)
  
  let rec app_list_value l0 m =
    match l0 with
      | Nil_list_value -> m
      | Cons_list_value (h, tl_) -> Cons_list_value (h,
          (app_list_value tl_ m))
  
  (** val map_list_const : (const -> 'a1) -> list_const -> 'a1 list **)
  
  let rec map_list_const f = function
    | Nil_list_const -> Nil
    | Cons_list_const (h, tl_) -> Cons ((f h), (map_list_const f tl_))
  
  (** val make_list_const : const list -> list_const **)
  
  let rec make_list_const = function
    | Nil -> Nil_list_const
    | Cons (h, tl_) -> Cons_list_const (h, (make_list_const tl_))
  
  (** val unmake_list_const : list_const -> const list **)
  
  let rec unmake_list_const = function
    | Nil_list_const -> Nil
    | Cons_list_const (h, tl_) -> Cons (h, (unmake_list_const tl_))
  
  (** val nth_list_const : nat -> list_const -> const option **)
  
  let rec nth_list_const n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_const -> None
             | Cons_list_const (h, tl_) -> Some h)
      | S m ->
          (match l0 with
             | Nil_list_const -> None
             | Cons_list_const (h, tl_) -> nth_list_const m tl_)
  
  (** val app_list_const : list_const -> list_const -> list_const **)
  
  let rec app_list_const l0 m =
    match l0 with
      | Nil_list_const -> m
      | Cons_list_const (h, tl_) -> Cons_list_const (h,
          (app_list_const tl_ m))
  
  (** val map_list_typ : (typ -> 'a1) -> list_typ -> 'a1 list **)
  
  let rec map_list_typ f = function
    | Nil_list_typ -> Nil
    | Cons_list_typ (h, tl_) -> Cons ((f h), (map_list_typ f tl_))
  
  (** val make_list_typ : typ list -> list_typ **)
  
  let rec make_list_typ = function
    | Nil -> Nil_list_typ
    | Cons (h, tl_) -> Cons_list_typ (h, (make_list_typ tl_))
  
  (** val unmake_list_typ : list_typ -> typ list **)
  
  let rec unmake_list_typ = function
    | Nil_list_typ -> Nil
    | Cons_list_typ (h, tl_) -> Cons (h, (unmake_list_typ tl_))
  
  (** val nth_list_typ : nat -> list_typ -> typ option **)
  
  let rec nth_list_typ n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_typ -> None
             | Cons_list_typ (h, tl_) -> Some h)
      | S m ->
          (match l0 with
             | Nil_list_typ -> None
             | Cons_list_typ (h, tl_) -> nth_list_typ m tl_)
  
  (** val app_list_typ : list_typ -> list_typ -> list_typ **)
  
  let rec app_list_typ l0 m =
    match l0 with
      | Nil_list_typ -> m
      | Cons_list_typ (h, tl_) -> Cons_list_typ (h, (app_list_typ tl_ m))
  
  (** val list_const_rec2 :
      (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const
      -> 'a2 -> 'a1) -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) ->
      'a2 -> (const -> 'a1 -> list_const -> 'a2 -> 'a2) -> list_const -> 'a2 **)
  
  let list_const_rec2 f f0 f1 f2 f3 f4 f5 f6 l0 =
    let rec f7 = function
      | Coq_const_int (s, i0) -> f s i0
      | Coq_const_undef t -> f0 t
      | Coq_const_null t -> f1 t
      | Coq_const_arr l1 -> f2 l1 (f8 l1)
      | Coq_const_struct l1 -> f3 l1 (f8 l1)
      | Coq_const_gid (t, i0) -> f4 t i0
    and f8 = function
      | Nil_list_const -> f5
      | Cons_list_const (c, l2) -> f6 c (f7 c) l2 (f8 l2)
    in f8 l0
  
  (** val const_rec2 :
      (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const
      -> 'a2 -> 'a1) -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) ->
      'a2 -> (const -> 'a1 -> list_const -> 'a2 -> 'a2) -> const -> 'a1 **)
  
  let const_rec2 f f0 f1 f2 f3 f4 f5 f6 c =
    let rec f7 = function
      | Coq_const_int (s, i0) -> f s i0
      | Coq_const_undef t -> f0 t
      | Coq_const_null t -> f1 t
      | Coq_const_arr l0 -> f2 l0 (f8 l0)
      | Coq_const_struct l0 -> f3 l0 (f8 l0)
      | Coq_const_gid (t, i0) -> f4 t i0
    and f8 = function
      | Nil_list_const -> f5
      | Cons_list_const (c0, l1) -> f6 c0 (f7 c0) l1 (f8 l1)
    in f7 c
  
  (** val const_mutrec :
      (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const
      -> 'a2 -> 'a1) -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) ->
      'a2 -> (const -> 'a1 -> list_const -> 'a2 -> 'a2) -> (const -> 'a1,
      list_const -> 'a2) prod **)
  
  let const_mutrec h1 h2 h3 h4 h5 h6 h7 h8 =
    Pair ((fun x -> const_rec2 h1 h2 h3 h4 h5 h6 h7 h8 x), (fun x ->
      list_const_rec2 h1 h2 h3 h4 h5 h6 h7 h8 x))
  
  (** val list_typ_rec2 :
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ
      -> 'a1 -> list_typ -> 'a2 -> 'a1) -> (list_typ -> 'a2 -> 'a1) -> (typ
      -> 'a1 -> 'a1) -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) ->
      list_typ -> 'a2 **)
  
  let list_typ_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 l0 =
    let rec f9 = function
      | Coq_typ_int s -> f s
      | Coq_typ_void -> f0
      | Coq_typ_label -> f1
      | Coq_typ_metadata -> f2
      | Coq_typ_array (s, t0) -> f3 s t0 (f9 t0)
      | Coq_typ_function (t0, l1) -> f4 t0 (f9 t0) l1 (f10 l1)
      | Coq_typ_struct l1 -> f5 l1 (f10 l1)
      | Coq_typ_pointer t0 -> f6 t0 (f9 t0)
    and f10 = function
      | Nil_list_typ -> f7
      | Cons_list_typ (t, l2) -> f8 t (f9 t) l2 (f10 l2)
    in f10 l0
  
  (** val typ_rec2 :
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ
      -> 'a1 -> list_typ -> 'a2 -> 'a1) -> (list_typ -> 'a2 -> 'a1) -> (typ
      -> 'a1 -> 'a1) -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> typ
      -> 'a1 **)
  
  let typ_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 t =
    let rec f9 = function
      | Coq_typ_int s -> f s
      | Coq_typ_void -> f0
      | Coq_typ_label -> f1
      | Coq_typ_metadata -> f2
      | Coq_typ_array (s, t1) -> f3 s t1 (f9 t1)
      | Coq_typ_function (t1, l0) -> f4 t1 (f9 t1) l0 (f10 l0)
      | Coq_typ_struct l0 -> f5 l0 (f10 l0)
      | Coq_typ_pointer t1 -> f6 t1 (f9 t1)
    and f10 = function
      | Nil_list_typ -> f7
      | Cons_list_typ (t0, l1) -> f8 t0 (f9 t0) l1 (f10 l1)
    in f9 t
  
  (** val typ_mutrec :
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ
      -> 'a1 -> list_typ -> 'a2 -> 'a1) -> (list_typ -> 'a2 -> 'a1) -> (typ
      -> 'a1 -> 'a1) -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> (typ
      -> 'a1, list_typ -> 'a2) prod **)
  
  let typ_mutrec h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =
    Pair ((fun x -> typ_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 x), (fun x ->
      list_typ_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 x))
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

module SimpleSE = 
 struct 
  type coq_ExecutionContext = { coq_CurBB : LLVMsyntax.block;
                                coq_Locals : gVMap; coq_Allocas : 
                                mblock list }
  
  (** val coq_ExecutionContext_rect :
      (LLVMsyntax.block -> gVMap -> mblock list -> 'a1) ->
      coq_ExecutionContext -> 'a1 **)
  
  let coq_ExecutionContext_rect f e =
    let { coq_CurBB = x; coq_Locals = x0; coq_Allocas = x1 } = e in f x x0 x1
  
  (** val coq_ExecutionContext_rec :
      (LLVMsyntax.block -> gVMap -> mblock list -> 'a1) ->
      coq_ExecutionContext -> 'a1 **)
  
  let coq_ExecutionContext_rec f e =
    let { coq_CurBB = x; coq_Locals = x0; coq_Allocas = x1 } = e in f x x0 x1
  
  (** val coq_CurBB : coq_ExecutionContext -> LLVMsyntax.block **)
  
  let coq_CurBB x = x.coq_CurBB
  
  (** val coq_Locals : coq_ExecutionContext -> gVMap **)
  
  let coq_Locals x = x.coq_Locals
  
  (** val coq_Allocas : coq_ExecutionContext -> mblock list **)
  
  let coq_Allocas x = x.coq_Allocas
  
  type coq_State = { coq_Frame : coq_ExecutionContext; coq_Mem : mem }
  
  (** val coq_State_rect :
      (coq_ExecutionContext -> mem -> 'a1) -> coq_State -> 'a1 **)
  
  let coq_State_rect f s =
    let { coq_Frame = x; coq_Mem = x0 } = s in f x x0
  
  (** val coq_State_rec :
      (coq_ExecutionContext -> mem -> 'a1) -> coq_State -> 'a1 **)
  
  let coq_State_rec f s =
    let { coq_Frame = x; coq_Mem = x0 } = s in f x x0
  
  (** val coq_Frame : coq_State -> coq_ExecutionContext **)
  
  let coq_Frame x = x.coq_Frame
  
  (** val coq_Mem : coq_State -> mem **)
  
  let coq_Mem x = x.coq_Mem
  
  type nbranch =
    LLVMsyntax.cmd
    (* singleton inductive, whose constructor was mkNB *)
  
  (** val nbranch_rect : (LLVMsyntax.cmd -> __ -> 'a1) -> nbranch -> 'a1 **)
  
  let nbranch_rect f n =
    f n __
  
  (** val nbranch_rec : (LLVMsyntax.cmd -> __ -> 'a1) -> nbranch -> 'a1 **)
  
  let nbranch_rec f n =
    f n __
  
  (** val nbranching_cmd : nbranch -> LLVMsyntax.cmd **)
  
  let nbranching_cmd n =
    n
  
  (** val isCallInst_dec : LLVMsyntax.cmd -> sumbool **)
  
  let isCallInst_dec = function
    | LLVMsyntax.Coq_insn_call (i0, n, t, t0, i1, p) -> Right
    | _ -> Left
  
  (** val cmd2nbranch : LLVMsyntax.cmd -> nbranch option **)
  
  let cmd2nbranch c =
    match isCallInst_dec c with
      | Left -> Some c
      | Right -> None
  
  (** val cmds2nbranchs : LLVMsyntax.cmd list -> nbranch list option **)
  
  let rec cmds2nbranchs = function
    | Nil -> Some Nil
    | Cons (c, cs') ->
        (match cmd2nbranch c with
           | Some nb ->
               (match cmds2nbranchs cs' with
                  | Some nbs' -> Some (Cons (nb, nbs'))
                  | None -> None)
           | None -> None)
  
  (** val nbranchs2cmds : nbranch list -> LLVMsyntax.cmd list **)
  
  let rec nbranchs2cmds = function
    | Nil -> Nil
    | Cons (n, nbs') -> Cons (n, (nbranchs2cmds nbs'))
  
  type subblock = { coq_NBs : nbranch list; call_cmd : LLVMsyntax.cmd }
  
  (** val subblock_rect :
      (nbranch list -> LLVMsyntax.cmd -> __ -> 'a1) -> subblock -> 'a1 **)
  
  let subblock_rect f s =
    let { coq_NBs = x; call_cmd = x0 } = s in f x x0 __
  
  (** val subblock_rec :
      (nbranch list -> LLVMsyntax.cmd -> __ -> 'a1) -> subblock -> 'a1 **)
  
  let subblock_rec f s =
    let { coq_NBs = x; call_cmd = x0 } = s in f x x0 __
  
  (** val coq_NBs : subblock -> nbranch list **)
  
  let coq_NBs x = x.coq_NBs
  
  (** val call_cmd : subblock -> LLVMsyntax.cmd **)
  
  let call_cmd x = x.call_cmd
  
  (** val cmds2sbs :
      LLVMsyntax.cmds -> (subblock list, nbranch list) prod **)
  
  let rec cmds2sbs = function
    | Nil -> Pair (Nil, Nil)
    | Cons (c, cs') ->
        (match isCallInst_dec c with
           | Left ->
               let Pair (l0, nbs0) = cmds2sbs cs' in
               (match l0 with
                  | Nil -> Pair (Nil, (Cons (c, nbs0)))
                  | Cons (s, sbs') ->
                      let { coq_NBs = nbs; call_cmd = call0 } = s in
                      Pair ((Cons ({ coq_NBs = (Cons (c, nbs)); call_cmd =
                      call0 }, sbs')), nbs0))
           | Right ->
               let Pair (sbs, nbs0) = cmds2sbs cs' in
               Pair ((Cons ({ coq_NBs = Nil; call_cmd = c }, sbs)), nbs0))
  
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
  
  (** val sterm_rect :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
      (smem -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
      (smem -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.inbounds
      -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm -> 'a1) ->
      (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ
      -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> sterm -> 'a1 **)
  
  let rec sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
    | Coq_sterm_val v -> f v
    | Coq_sterm_bop (b, s0, s1, s2) ->
        f0 b s0 s1 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) s2
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s2)
    | Coq_sterm_extractvalue (t, s0, l0) ->
        f1 t s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) l0
    | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
        f2 t s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t0 s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) l0
    | Coq_sterm_malloc (s0, t, s1, a) -> f3 s0 t s1 a
    | Coq_sterm_alloca (s0, t, s1, a) -> f4 s0 t s1 a
    | Coq_sterm_load (s0, t, s1) ->
        f5 s0 t s1 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1)
    | Coq_sterm_gep (i0, t, s0, l0) ->
        f6 i0 t s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) l0
    | Coq_sterm_ext (e, t, s0, t0) ->
        f7 e t s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t0
    | Coq_sterm_cast (c, t, s0, t0) ->
        f8 c t s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t0
    | Coq_sterm_icmp (c, t, s0, s1) ->
        f9 c t s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1)
    | Coq_sterm_phi (t, l0) -> f10 t l0
    | Coq_sterm_select (s0, t, s1, s2) ->
        f11 s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) s2
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s2)
  
  (** val sterm_rec :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
      (smem -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
      (smem -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.inbounds
      -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm -> 'a1) ->
      (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ
      -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> sterm -> 'a1 **)
  
  let rec sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
    | Coq_sterm_val v -> f v
    | Coq_sterm_bop (b, s0, s1, s2) ->
        f0 b s0 s1 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) s2
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s2)
    | Coq_sterm_extractvalue (t, s0, l0) ->
        f1 t s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) l0
    | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
        f2 t s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t0 s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) l0
    | Coq_sterm_malloc (s0, t, s1, a) -> f3 s0 t s1 a
    | Coq_sterm_alloca (s0, t, s1, a) -> f4 s0 t s1 a
    | Coq_sterm_load (s0, t, s1) ->
        f5 s0 t s1 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1)
    | Coq_sterm_gep (i0, t, s0, l0) ->
        f6 i0 t s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) l0
    | Coq_sterm_ext (e, t, s0, t0) ->
        f7 e t s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t0
    | Coq_sterm_cast (c, t, s0, t0) ->
        f8 c t s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t0
    | Coq_sterm_icmp (c, t, s0, s1) ->
        f9 c t s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1)
    | Coq_sterm_phi (t, l0) -> f10 t l0
    | Coq_sterm_select (s0, t, s1, s2) ->
        f11 s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) s2
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s2)
  
  (** val list_sterm_rect :
      'a1 -> (sterm -> list_sterm -> 'a1 -> 'a1) -> list_sterm -> 'a1 **)
  
  let rec list_sterm_rect f f0 = function
    | Nil_list_sterm -> f
    | Cons_list_sterm (s, l1) -> f0 s l1 (list_sterm_rect f f0 l1)
  
  (** val list_sterm_rec :
      'a1 -> (sterm -> list_sterm -> 'a1 -> 'a1) -> list_sterm -> 'a1 **)
  
  let rec list_sterm_rec f f0 = function
    | Nil_list_sterm -> f
    | Cons_list_sterm (s, l1) -> f0 s l1 (list_sterm_rec f f0 l1)
  
  (** val list_sterm_l_rect :
      'a1 -> (sterm -> LLVMsyntax.l -> list_sterm_l -> 'a1 -> 'a1) ->
      list_sterm_l -> 'a1 **)
  
  let rec list_sterm_l_rect f f0 = function
    | Nil_list_sterm_l -> f
    | Cons_list_sterm_l (s, l1, l2) -> f0 s l1 l2 (list_sterm_l_rect f f0 l2)
  
  (** val list_sterm_l_rec :
      'a1 -> (sterm -> LLVMsyntax.l -> list_sterm_l -> 'a1 -> 'a1) ->
      list_sterm_l -> 'a1 **)
  
  let rec list_sterm_l_rec f f0 = function
    | Nil_list_sterm_l -> f
    | Cons_list_sterm_l (s, l1, l2) -> f0 s l1 l2 (list_sterm_l_rec f f0 l2)
  
  (** val smem_rect :
      'a1 -> (smem -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
      'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
      'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> sterm -> 'a1) ->
      smem -> 'a1 **)
  
  let rec smem_rect f f0 f1 f2 f3 f4 = function
    | Coq_smem_init -> f
    | Coq_smem_malloc (s0, t, s1, a) ->
        f0 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t s1 a
    | Coq_smem_free (s0, t, s1) -> f1 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t s1
    | Coq_smem_alloca (s0, t, s1, a) ->
        f2 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t s1 a
    | Coq_smem_load (s0, t, s1) -> f3 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t s1
    | Coq_smem_store (s0, t, s1, s2) ->
        f4 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t s1 s2
  
  (** val smem_rec :
      'a1 -> (smem -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
      'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
      'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> sterm -> 'a1) ->
      smem -> 'a1 **)
  
  let rec smem_rec f f0 f1 f2 f3 f4 = function
    | Coq_smem_init -> f
    | Coq_smem_malloc (s0, t, s1, a) ->
        f0 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t s1 a
    | Coq_smem_free (s0, t, s1) -> f1 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t s1
    | Coq_smem_alloca (s0, t, s1, a) ->
        f2 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t s1 a
    | Coq_smem_load (s0, t, s1) -> f3 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t s1
    | Coq_smem_store (s0, t, s1, s2) ->
        f4 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t s1 s2
  
  (** val sframe_rect :
      'a1 -> (smem -> sframe -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> sframe -> 'a1 **)
  
  let rec sframe_rect f f0 = function
    | Coq_sframe_init -> f
    | Coq_sframe_alloca (s0, s1, t, s2, a) ->
        f0 s0 s1 (sframe_rect f f0 s1) t s2 a
  
  (** val sframe_rec :
      'a1 -> (smem -> sframe -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> sframe -> 'a1 **)
  
  let rec sframe_rec f f0 = function
    | Coq_sframe_init -> f
    | Coq_sframe_alloca (s0, s1, t, s2, a) ->
        f0 s0 s1 (sframe_rec f f0 s1) t s2 a
  
  (** val sframe_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1
      -> list_sterm -> 'a2 -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) -> (sterm -> 'a1
      -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> 'a2 ->
      (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) -> 'a3 -> (sterm -> 'a1 ->
      LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) -> 'a4 -> (smem -> 'a4 ->
      LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a4) -> 'a5 -> (smem
      -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a5) -> sframe -> 'a5 **)
  
  let sframe_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 s =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s1, s2, s3) -> f0 b s1 s2 (f24 s2) s3 (f24 s3)
      | Coq_sterm_extractvalue (t, s1, l0) -> f1 t s1 (f24 s1) l0
      | Coq_sterm_insertvalue (t, s1, t0, s2, l0) ->
          f2 t s1 (f24 s1) t0 s2 (f24 s2) l0
      | Coq_sterm_malloc (s1, t, s2, a) -> f3 s1 (f27 s1) t s2 a
      | Coq_sterm_alloca (s1, t, s2, a) -> f4 s1 (f27 s1) t s2 a
      | Coq_sterm_load (s1, t, s2) -> f5 s1 (f27 s1) t s2 (f24 s2)
      | Coq_sterm_gep (i0, t, s1, l0) -> f6 i0 t s1 (f24 s1) l0 (f25 l0)
      | Coq_sterm_ext (e, t, s1, t0) -> f7 e t s1 (f24 s1) t0
      | Coq_sterm_cast (c, t, s1, t0) -> f8 c t s1 (f24 s1) t0
      | Coq_sterm_icmp (c, t, s1, s2) -> f9 c t s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_phi (t, l0) -> f10 t l0 (f26 l0)
      | Coq_sterm_select (s1, t, s2, s3) ->
          f11 s1 (f24 s1) t s2 (f24 s2) s3 (f24 s3)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s0, l1) -> f13 s0 (f24 s0) l1 (f25 l1)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s0, l1, l2) -> f15 s0 (f24 s0) l1 l2 (f26 l2)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s1, t, s2, a) -> f17 s1 (f27 s1) t s2 a
      | Coq_smem_free (s1, t, s2) -> f18 s1 (f27 s1) t s2 (f24 s2)
      | Coq_smem_alloca (s1, t, s2, a) -> f19 s1 (f27 s1) t s2 a
      | Coq_smem_load (s1, t, s2) -> f20 s1 (f27 s1) t s2 (f24 s2)
      | Coq_smem_store (s1, t, s2, s3) ->
          f21 s1 (f27 s1) t s2 (f24 s2) s3 (f24 s3)
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s1, s2, t, s3, a) ->
          f23 s1 (f27 s1) s2 (f28 s2) t s3 a
    in f28 s
  
  (** val smem_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1
      -> list_sterm -> 'a2 -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) -> (sterm -> 'a1
      -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> 'a2 ->
      (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) -> 'a3 -> (sterm -> 'a1 ->
      LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) -> 'a4 -> (smem -> 'a4 ->
      LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a4) -> 'a5 -> (smem
      -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a5) -> smem -> 'a4 **)
  
  let smem_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 s =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s1, s2, s3) -> f0 b s1 s2 (f24 s2) s3 (f24 s3)
      | Coq_sterm_extractvalue (t, s1, l0) -> f1 t s1 (f24 s1) l0
      | Coq_sterm_insertvalue (t, s1, t0, s2, l0) ->
          f2 t s1 (f24 s1) t0 s2 (f24 s2) l0
      | Coq_sterm_malloc (s1, t, s2, a) -> f3 s1 (f27 s1) t s2 a
      | Coq_sterm_alloca (s1, t, s2, a) -> f4 s1 (f27 s1) t s2 a
      | Coq_sterm_load (s1, t, s2) -> f5 s1 (f27 s1) t s2 (f24 s2)
      | Coq_sterm_gep (i0, t, s1, l0) -> f6 i0 t s1 (f24 s1) l0 (f25 l0)
      | Coq_sterm_ext (e, t, s1, t0) -> f7 e t s1 (f24 s1) t0
      | Coq_sterm_cast (c, t, s1, t0) -> f8 c t s1 (f24 s1) t0
      | Coq_sterm_icmp (c, t, s1, s2) -> f9 c t s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_phi (t, l0) -> f10 t l0 (f26 l0)
      | Coq_sterm_select (s1, t, s2, s3) ->
          f11 s1 (f24 s1) t s2 (f24 s2) s3 (f24 s3)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s0, l1) -> f13 s0 (f24 s0) l1 (f25 l1)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s0, l1, l2) -> f15 s0 (f24 s0) l1 l2 (f26 l2)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s1, t, s2, a) -> f17 s1 (f27 s1) t s2 a
      | Coq_smem_free (s1, t, s2) -> f18 s1 (f27 s1) t s2 (f24 s2)
      | Coq_smem_alloca (s1, t, s2, a) -> f19 s1 (f27 s1) t s2 a
      | Coq_smem_load (s1, t, s2) -> f20 s1 (f27 s1) t s2 (f24 s2)
      | Coq_smem_store (s1, t, s2, s3) ->
          f21 s1 (f27 s1) t s2 (f24 s2) s3 (f24 s3)
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s1, s2, t, s3, a) ->
          f23 s1 (f27 s1) s2 (f28 s2) t s3 a
    in f27 s
  
  (** val list_sterm_l_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1
      -> list_sterm -> 'a2 -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) -> (sterm -> 'a1
      -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> 'a2 ->
      (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) -> 'a3 -> (sterm -> 'a1 ->
      LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) -> 'a4 -> (smem -> 'a4 ->
      LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a4) -> 'a5 -> (smem
      -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a5) -> list_sterm_l -> 'a3 **)
  
  let list_sterm_l_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 l0 =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_extractvalue (t, s0, l1) -> f1 t s0 (f24 s0) l1
      | Coq_sterm_insertvalue (t, s0, t0, s1, l1) ->
          f2 t s0 (f24 s0) t0 s1 (f24 s1) l1
      | Coq_sterm_malloc (s0, t, s1, a) -> f3 s0 (f27 s0) t s1 a
      | Coq_sterm_alloca (s0, t, s1, a) -> f4 s0 (f27 s0) t s1 a
      | Coq_sterm_load (s0, t, s1) -> f5 s0 (f27 s0) t s1 (f24 s1)
      | Coq_sterm_gep (i0, t, s0, l1) -> f6 i0 t s0 (f24 s0) l1 (f25 l1)
      | Coq_sterm_ext (e, t, s0, t0) -> f7 e t s0 (f24 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f8 c t s0 (f24 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f9 c t s0 (f24 s0) s1 (f24 s1)
      | Coq_sterm_phi (t, l1) -> f10 t l1 (f26 l1)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f11 s0 (f24 s0) t s1 (f24 s1) s2 (f24 s2)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s, l2) -> f13 s (f24 s) l2 (f25 l2)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s, l2, l3) -> f15 s (f24 s) l2 l3 (f26 l3)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s0, t, s1, a) -> f17 s0 (f27 s0) t s1 a
      | Coq_smem_free (s0, t, s1) -> f18 s0 (f27 s0) t s1 (f24 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f19 s0 (f27 s0) t s1 a
      | Coq_smem_load (s0, t, s1) -> f20 s0 (f27 s0) t s1 (f24 s1)
      | Coq_smem_store (s0, t, s1, s2) ->
          f21 s0 (f27 s0) t s1 (f24 s1) s2 (f24 s2)
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f23 s0 (f27 s0) s1 (f28 s1) t s2 a
    in f26 l0
  
  (** val list_sterm_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1
      -> list_sterm -> 'a2 -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) -> (sterm -> 'a1
      -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> 'a2 ->
      (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) -> 'a3 -> (sterm -> 'a1 ->
      LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) -> 'a4 -> (smem -> 'a4 ->
      LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a4) -> 'a5 -> (smem
      -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a5) -> list_sterm -> 'a2 **)
  
  let list_sterm_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 l0 =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_extractvalue (t, s0, l1) -> f1 t s0 (f24 s0) l1
      | Coq_sterm_insertvalue (t, s0, t0, s1, l1) ->
          f2 t s0 (f24 s0) t0 s1 (f24 s1) l1
      | Coq_sterm_malloc (s0, t, s1, a) -> f3 s0 (f27 s0) t s1 a
      | Coq_sterm_alloca (s0, t, s1, a) -> f4 s0 (f27 s0) t s1 a
      | Coq_sterm_load (s0, t, s1) -> f5 s0 (f27 s0) t s1 (f24 s1)
      | Coq_sterm_gep (i0, t, s0, l1) -> f6 i0 t s0 (f24 s0) l1 (f25 l1)
      | Coq_sterm_ext (e, t, s0, t0) -> f7 e t s0 (f24 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f8 c t s0 (f24 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f9 c t s0 (f24 s0) s1 (f24 s1)
      | Coq_sterm_phi (t, l1) -> f10 t l1 (f26 l1)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f11 s0 (f24 s0) t s1 (f24 s1) s2 (f24 s2)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s, l2) -> f13 s (f24 s) l2 (f25 l2)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s, l2, l3) -> f15 s (f24 s) l2 l3 (f26 l3)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s0, t, s1, a) -> f17 s0 (f27 s0) t s1 a
      | Coq_smem_free (s0, t, s1) -> f18 s0 (f27 s0) t s1 (f24 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f19 s0 (f27 s0) t s1 a
      | Coq_smem_load (s0, t, s1) -> f20 s0 (f27 s0) t s1 (f24 s1)
      | Coq_smem_store (s0, t, s1, s2) ->
          f21 s0 (f27 s0) t s1 (f24 s1) s2 (f24 s2)
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f23 s0 (f27 s0) s1 (f28 s1) t s2 a
    in f25 l0
  
  (** val sterm_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1
      -> list_sterm -> 'a2 -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) -> (sterm -> 'a1
      -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> 'a2 ->
      (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) -> 'a3 -> (sterm -> 'a1 ->
      LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) -> 'a4 -> (smem -> 'a4 ->
      LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a4) -> 'a5 -> (smem
      -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a5) -> sterm -> 'a1 **)
  
  let sterm_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 s =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s1, s2, s3) -> f0 b s1 s2 (f24 s2) s3 (f24 s3)
      | Coq_sterm_extractvalue (t, s1, l0) -> f1 t s1 (f24 s1) l0
      | Coq_sterm_insertvalue (t, s1, t0, s2, l0) ->
          f2 t s1 (f24 s1) t0 s2 (f24 s2) l0
      | Coq_sterm_malloc (s1, t, s2, a) -> f3 s1 (f27 s1) t s2 a
      | Coq_sterm_alloca (s1, t, s2, a) -> f4 s1 (f27 s1) t s2 a
      | Coq_sterm_load (s1, t, s2) -> f5 s1 (f27 s1) t s2 (f24 s2)
      | Coq_sterm_gep (i0, t, s1, l0) -> f6 i0 t s1 (f24 s1) l0 (f25 l0)
      | Coq_sterm_ext (e, t, s1, t0) -> f7 e t s1 (f24 s1) t0
      | Coq_sterm_cast (c, t, s1, t0) -> f8 c t s1 (f24 s1) t0
      | Coq_sterm_icmp (c, t, s1, s2) -> f9 c t s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_phi (t, l0) -> f10 t l0 (f26 l0)
      | Coq_sterm_select (s1, t, s2, s3) ->
          f11 s1 (f24 s1) t s2 (f24 s2) s3 (f24 s3)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s0, l1) -> f13 s0 (f24 s0) l1 (f25 l1)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s0, l1, l2) -> f15 s0 (f24 s0) l1 l2 (f26 l2)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s1, t, s2, a) -> f17 s1 (f27 s1) t s2 a
      | Coq_smem_free (s1, t, s2) -> f18 s1 (f27 s1) t s2 (f24 s2)
      | Coq_smem_alloca (s1, t, s2, a) -> f19 s1 (f27 s1) t s2 a
      | Coq_smem_load (s1, t, s2) -> f20 s1 (f27 s1) t s2 (f24 s2)
      | Coq_smem_store (s1, t, s2, s3) ->
          f21 s1 (f27 s1) t s2 (f24 s2) s3 (f24 s3)
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s1, s2, t, s3, a) ->
          f23 s1 (f27 s1) s2 (f28 s2) t s3 a
    in f24 s
  
  (** val se_mutrec :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1
      -> list_sterm -> 'a2 -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) -> (sterm -> 'a1
      -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> 'a2 ->
      (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) -> 'a3 -> (sterm -> 'a1 ->
      LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) -> 'a4 -> (smem -> 'a4 ->
      LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a4) -> 'a5 -> (smem
      -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a5) -> ((((sterm -> 'a1, list_sterm -> 'a2) prod,
      list_sterm_l -> 'a3) prod, smem -> 'a4) prod, sframe -> 'a5) prod **)
  
  let se_mutrec h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 =
    Pair ((Pair ((Pair ((Pair ((fun x ->
      sterm_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
        h18 h19 h20 h21 h22 h23 h24 h25 x), (fun x ->
      list_sterm_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
        h17 h18 h19 h20 h21 h22 h23 h24 h25 x))), (fun x ->
      list_sterm_l_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 x))), (fun x ->
      smem_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
        h18 h19 h20 h21 h22 h23 h24 h25 x))), (fun x ->
      sframe_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
        h18 h19 h20 h21 h22 h23 h24 h25 x))
  
  (** val map_list_sterm : (sterm -> 'a1) -> list_sterm -> 'a1 list **)
  
  let rec map_list_sterm f = function
    | Nil_list_sterm -> Nil
    | Cons_list_sterm (h, tl_) -> Cons ((f h), (map_list_sterm f tl_))
  
  (** val make_list_sterm : sterm list -> list_sterm **)
  
  let rec make_list_sterm = function
    | Nil -> Nil_list_sterm
    | Cons (h, tl_) -> Cons_list_sterm (h, (make_list_sterm tl_))
  
  (** val unmake_list_sterm : list_sterm -> sterm list **)
  
  let rec unmake_list_sterm = function
    | Nil_list_sterm -> Nil
    | Cons_list_sterm (h, tl_) -> Cons (h, (unmake_list_sterm tl_))
  
  (** val nth_list_sterm : nat -> list_sterm -> sterm option **)
  
  let rec nth_list_sterm n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_sterm -> None
             | Cons_list_sterm (h, tl_) -> Some h)
      | S m ->
          (match l0 with
             | Nil_list_sterm -> None
             | Cons_list_sterm (h, tl_) -> nth_list_sterm m tl_)
  
  (** val app_list_sterm : list_sterm -> list_sterm -> list_sterm **)
  
  let rec app_list_sterm l0 m =
    match l0 with
      | Nil_list_sterm -> m
      | Cons_list_sterm (h, tl_) -> Cons_list_sterm (h,
          (app_list_sterm tl_ m))
  
  (** val map_list_sterm_l :
      (sterm -> LLVMsyntax.l -> 'a1) -> list_sterm_l -> 'a1 list **)
  
  let rec map_list_sterm_l f = function
    | Nil_list_sterm_l -> Nil
    | Cons_list_sterm_l (h0, h1, tl_) -> Cons ((f h0 h1),
        (map_list_sterm_l f tl_))
  
  (** val make_list_sterm_l :
      (sterm, LLVMsyntax.l) prod list -> list_sterm_l **)
  
  let rec make_list_sterm_l = function
    | Nil -> Nil_list_sterm_l
    | Cons (p, tl_) ->
        let Pair (h0, h1) = p in
        Cons_list_sterm_l (h0, h1, (make_list_sterm_l tl_))
  
  (** val unmake_list_sterm_l :
      list_sterm_l -> (sterm, LLVMsyntax.l) prod list **)
  
  let rec unmake_list_sterm_l = function
    | Nil_list_sterm_l -> Nil
    | Cons_list_sterm_l (h0, h1, tl_) -> Cons ((Pair (h0, h1)),
        (unmake_list_sterm_l tl_))
  
  (** val nth_list_sterm_l :
      nat -> list_sterm_l -> (sterm, LLVMsyntax.l) prod option **)
  
  let rec nth_list_sterm_l n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_sterm_l -> None
             | Cons_list_sterm_l (h0, h1, tl_) -> Some (Pair (h0, h1)))
      | S m ->
          (match l0 with
             | Nil_list_sterm_l -> None
             | Cons_list_sterm_l (h0, h1, tl_) -> nth_list_sterm_l m tl_)
  
  (** val app_list_sterm_l : list_sterm_l -> list_sterm_l -> list_sterm_l **)
  
  let rec app_list_sterm_l l0 m =
    match l0 with
      | Nil_list_sterm_l -> m
      | Cons_list_sterm_l (h0, h1, tl_) -> Cons_list_sterm_l (h0, h1,
          (app_list_sterm_l tl_ m))
  
  type sterminator =
    | Coq_stmn_return of LLVMsyntax.id * LLVMsyntax.typ * sterm
    | Coq_stmn_return_void of LLVMsyntax.id
    | Coq_stmn_br of LLVMsyntax.id * sterm * LLVMsyntax.l * LLVMsyntax.l
    | Coq_stmn_br_uncond of LLVMsyntax.id * LLVMsyntax.l
    | Coq_stmn_unreachable of LLVMsyntax.id
  
  (** val sterminator_rect :
      (LLVMsyntax.id -> LLVMsyntax.typ -> sterm -> 'a1) -> (LLVMsyntax.id ->
      'a1) -> (LLVMsyntax.id -> sterm -> LLVMsyntax.l -> LLVMsyntax.l -> 'a1)
      -> (LLVMsyntax.id -> LLVMsyntax.l -> 'a1) -> (LLVMsyntax.id -> 'a1) ->
      sterminator -> 'a1 **)
  
  let sterminator_rect f f0 f1 f2 f3 = function
    | Coq_stmn_return (x, x0, x1) -> f x x0 x1
    | Coq_stmn_return_void x -> f0 x
    | Coq_stmn_br (x, x0, x1, x2) -> f1 x x0 x1 x2
    | Coq_stmn_br_uncond (x, x0) -> f2 x x0
    | Coq_stmn_unreachable x -> f3 x
  
  (** val sterminator_rec :
      (LLVMsyntax.id -> LLVMsyntax.typ -> sterm -> 'a1) -> (LLVMsyntax.id ->
      'a1) -> (LLVMsyntax.id -> sterm -> LLVMsyntax.l -> LLVMsyntax.l -> 'a1)
      -> (LLVMsyntax.id -> LLVMsyntax.l -> 'a1) -> (LLVMsyntax.id -> 'a1) ->
      sterminator -> 'a1 **)
  
  let sterminator_rec f f0 f1 f2 f3 = function
    | Coq_stmn_return (x, x0, x1) -> f x x0 x1
    | Coq_stmn_return_void x -> f0 x
    | Coq_stmn_br (x, x0, x1, x2) -> f1 x x0 x1 x2
    | Coq_stmn_br_uncond (x, x0) -> f2 x x0
    | Coq_stmn_unreachable x -> f3 x
  
  type scall =
    | Coq_stmn_call of LLVMsyntax.id * LLVMsyntax.noret * 
       LLVMsyntax.tailc * LLVMsyntax.typ * LLVMsyntax.id
       * (LLVMsyntax.typ, sterm) prod list
  
  (** val scall_rect :
      (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.tailc ->
      LLVMsyntax.typ -> LLVMsyntax.id -> (LLVMsyntax.typ, sterm) prod list ->
      'a1) -> scall -> 'a1 **)
  
  let scall_rect f = function
    | Coq_stmn_call (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
  
  (** val scall_rec :
      (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.tailc ->
      LLVMsyntax.typ -> LLVMsyntax.id -> (LLVMsyntax.typ, sterm) prod list ->
      'a1) -> scall -> 'a1 **)
  
  let scall_rec f = function
    | Coq_stmn_call (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
  
  type smap = (AtomImpl.atom, sterm) prod list
  
  type sstate = { coq_STerms : smap; coq_SMem : smem; coq_SFrame : 
                  sframe; coq_SEffects : sterm list }
  
  (** val sstate_rect :
      (smap -> smem -> sframe -> sterm list -> 'a1) -> sstate -> 'a1 **)
  
  let sstate_rect f s =
    let { coq_STerms = x; coq_SMem = x0; coq_SFrame = x1; coq_SEffects =
      x2 } = s
    in
    f x x0 x1 x2
  
  (** val sstate_rec :
      (smap -> smem -> sframe -> sterm list -> 'a1) -> sstate -> 'a1 **)
  
  let sstate_rec f s =
    let { coq_STerms = x; coq_SMem = x0; coq_SFrame = x1; coq_SEffects =
      x2 } = s
    in
    f x x0 x1 x2
  
  (** val coq_STerms : sstate -> smap **)
  
  let coq_STerms x = x.coq_STerms
  
  (** val coq_SMem : sstate -> smem **)
  
  let coq_SMem x = x.coq_SMem
  
  (** val coq_SFrame : sstate -> sframe **)
  
  let coq_SFrame x = x.coq_SFrame
  
  (** val coq_SEffects : sstate -> sterm list **)
  
  let coq_SEffects x = x.coq_SEffects
  
  (** val sstate_init : sstate **)
  
  let sstate_init =
    { coq_STerms = Nil; coq_SMem = Coq_smem_init; coq_SFrame =
      Coq_sframe_init; coq_SEffects = Nil }
  
  (** val lookupSmap : smap -> LLVMsyntax.id -> sterm **)
  
  let rec lookupSmap sm i0 =
    match sm with
      | Nil -> Coq_sterm_val (LLVMsyntax.Coq_value_id i0)
      | Cons (p, sm') ->
          let Pair (id0, s0) = p in
          (match eqDec_atom i0 id0 with
             | Left -> s0
             | Right -> lookupSmap sm' i0)
  
  (** val value2Sterm : smap -> LLVMsyntax.value -> sterm **)
  
  let value2Sterm sm v = match v with
    | LLVMsyntax.Coq_value_id i0 -> lookupSmap sm i0
    | LLVMsyntax.Coq_value_const c -> Coq_sterm_val v
  
  (** val list_param__list_typ_subst_sterm :
      LLVMsyntax.params -> smap -> (LLVMsyntax.typ, sterm) prod list **)
  
  let rec list_param__list_typ_subst_sterm list_param1 sm =
    match list_param1 with
      | Nil -> Nil
      | Cons (p, list_param1') ->
          let Pair (t, v) = p in
          Cons ((Pair (t,
          (match v with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap sm i0
             | LLVMsyntax.Coq_value_const c -> Coq_sterm_val v))),
          (list_param__list_typ_subst_sterm list_param1' sm))
  
  (** val se_cmd : sstate -> nbranch -> sstate **)
  
  let se_cmd st = function
    | LLVMsyntax.Coq_insn_bop (id0, op0, sz0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_bop (op0, sz0,
          (match v1 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v1),
          (match v2 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_extractvalue (id0, t1, v1, cs3) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_extractvalue (t1,
          (match v1 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v1), cs3)));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_insertvalue (id0, t1, v1, t2, v2, cs3) ->
        { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_insertvalue (t1,
          (match v1 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v1), t2,
          (match v2 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v2), cs3)));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_malloc (id0, t1, sz1, al1) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_malloc (st.coq_SMem, t1,
          sz1, al1))); coq_SMem = (Coq_smem_malloc (st.coq_SMem, t1, sz1,
        al1)); coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_free (id0, t0, v0) -> { coq_STerms = st.coq_STerms;
        coq_SMem = (Coq_smem_free (st.coq_SMem, t0,
        (match v0 with
           | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
           | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v0)));
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_alloca (id0, t1, sz1, al1) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_alloca (st.coq_SMem, t1,
          sz1, al1))); coq_SMem = (Coq_smem_alloca (st.coq_SMem, t1, sz1,
        al1)); coq_SFrame = (Coq_sframe_alloca (st.coq_SMem, st.coq_SFrame,
        t1, sz1, al1)); coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_load (id0, t2, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_load (st.coq_SMem, t2,
          (match v2 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v2))));
        coq_SMem = (Coq_smem_load (st.coq_SMem, t2,
        (match v2 with
           | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
           | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v2)));
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_store (id0, t0, v1, v2) -> { coq_STerms =
        st.coq_STerms; coq_SMem = (Coq_smem_store (st.coq_SMem, t0,
        (match v1 with
           | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
           | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v1),
        (match v2 with
           | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
           | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v2)));
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_gep (id0, inbounds0, t1, v1, lv2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_gep (inbounds0, t1,
          (match v1 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v1),
          (make_list_sterm
            (LLVMsyntax.map_list_value (fun v ->
              match v with
                | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
                | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v) lv2)))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_ext (id0, op0, t1, v1, t2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_ext (op0, t1,
          (match v1 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v1), t2)));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_cast (id0, op0, t1, v1, t2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_cast (op0, t1,
          (match v1 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v1), t2)));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_icmp (id0, c0, t0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_icmp (c0, t0,
          (match v1 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c1 -> Coq_sterm_val v1),
          (match v2 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c1 -> Coq_sterm_val v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_select (id0, v0, t0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_select
          ((match v0 with
              | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
              | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v0), t0,
          (match v1 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v1),
          (match v2 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_call (id0, noret0, tailc0, rt, fid, lp) ->
        assert false (* absurd case *)
  
  (** val _se_phinodes :
      sstate -> sstate -> LLVMsyntax.phinode list -> sstate **)
  
  let rec _se_phinodes st st0 = function
    | Nil -> st
    | Cons (p, ps') ->
        let LLVMsyntax.Coq_insn_phi (id0, t0, idls0) = p in
        _se_phinodes { coq_STerms =
          (updateAL st.coq_STerms id0 (Coq_sterm_phi (t0,
            (make_list_sterm_l
              (LLVMsyntax.map_list_id_l (fun id5 l5 -> Pair
                ((let v = LLVMsyntax.Coq_value_id id5 in
                 match v with
                   | LLVMsyntax.Coq_value_id i0 ->
                       lookupSmap st.coq_STerms i0
                   | LLVMsyntax.Coq_value_const c -> Coq_sterm_val v), l5))
                idls0))))); coq_SMem = st.coq_SMem; coq_SFrame =
          st.coq_SFrame; coq_SEffects = st.coq_SEffects } st0 ps'
  
  (** val se_phinodes : sstate -> LLVMsyntax.phinode list -> sstate **)
  
  let rec se_phinodes st ps =
    _se_phinodes st st ps
  
  (** val se_cmds : sstate -> nbranch list -> sstate **)
  
  let rec se_cmds st = function
    | Nil -> st
    | Cons (c, cs') -> se_cmds (se_cmd st c) cs'
  
  (** val se_terminator : sstate -> LLVMsyntax.terminator -> sterminator **)
  
  let se_terminator st = function
    | LLVMsyntax.Coq_insn_return (id0, t0, v0) -> Coq_stmn_return (id0, t0,
        (match v0 with
           | LLVMsyntax.Coq_value_id i1 -> lookupSmap st.coq_STerms i1
           | LLVMsyntax.Coq_value_const c -> Coq_sterm_val v0))
    | LLVMsyntax.Coq_insn_return_void id0 -> Coq_stmn_return_void id0
    | LLVMsyntax.Coq_insn_br (id0, v0, l1, l2) -> Coq_stmn_br (id0,
        (match v0 with
           | LLVMsyntax.Coq_value_id i1 -> lookupSmap st.coq_STerms i1
           | LLVMsyntax.Coq_value_const c -> Coq_sterm_val v0), l1, l2)
    | LLVMsyntax.Coq_insn_br_uncond (id0, l0) -> Coq_stmn_br_uncond (id0, l0)
    | LLVMsyntax.Coq_insn_unreachable id0 -> Coq_stmn_unreachable id0
  
  (** val se_call : sstate -> LLVMsyntax.cmd -> scall **)
  
  let se_call st = function
    | LLVMsyntax.Coq_insn_call (i1, n, t, t0, i2, p) -> Coq_stmn_call (i1, n,
        t, t0, i2, (list_param__list_typ_subst_sterm p st.coq_STerms))
    | _ -> assert false (* absurd case *)
  
  (** val seffects_denote_trace_rect : 'a1 -> sterm list -> trace -> 'a1 **)
  
  let seffects_denote_trace_rect f l0 t =
    f
  
  (** val seffects_denote_trace_rec : 'a1 -> sterm list -> trace -> 'a1 **)
  
  let seffects_denote_trace_rec f l0 t =
    f
  
  (** val subst_tt : LLVMsyntax.id -> sterm -> sterm -> sterm **)
  
  let rec subst_tt id0 s0 s = match s with
    | Coq_sterm_val v ->
        (match v with
           | LLVMsyntax.Coq_value_id id1 ->
               (match eqDec_atom id0 id1 with
                  | Left -> s0
                  | Right -> s)
           | LLVMsyntax.Coq_value_const c -> Coq_sterm_val
               (LLVMsyntax.Coq_value_const c))
    | Coq_sterm_bop (op, sz0, s1, s2) -> Coq_sterm_bop (op, sz0,
        (subst_tt id0 s0 s1), (subst_tt id0 s0 s2))
    | Coq_sterm_extractvalue (t1, s1, cs) -> Coq_sterm_extractvalue (t1,
        (subst_tt id0 s0 s1), cs)
    | Coq_sterm_insertvalue (t1, s1, t2, s2, cs) -> Coq_sterm_insertvalue
        (t1, (subst_tt id0 s0 s1), t2, (subst_tt id0 s0 s2), cs)
    | Coq_sterm_malloc (m1, t1, sz0, align0) -> Coq_sterm_malloc
        ((subst_tm id0 s0 m1), t1, sz0, align0)
    | Coq_sterm_alloca (m1, t1, sz0, align0) -> Coq_sterm_alloca
        ((subst_tm id0 s0 m1), t1, sz0, align0)
    | Coq_sterm_load (m1, t1, s1) -> Coq_sterm_load (
        (subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1))
    | Coq_sterm_gep (inbounds0, t1, s1, ls2) -> Coq_sterm_gep (inbounds0, t1,
        (subst_tt id0 s0 s1), (subst_tlt id0 s0 ls2))
    | Coq_sterm_ext (extop0, t1, s1, t2) -> Coq_sterm_ext (extop0, t1,
        (subst_tt id0 s0 s1), t2)
    | Coq_sterm_cast (castop0, t1, s1, t2) -> Coq_sterm_cast (castop0, t1,
        (subst_tt id0 s0 s1), t2)
    | Coq_sterm_icmp (cond0, t1, s1, s2) -> Coq_sterm_icmp (cond0, t1,
        (subst_tt id0 s0 s1), (subst_tt id0 s0 s2))
    | Coq_sterm_phi (t1, lsl1) -> Coq_sterm_phi (t1,
        (subst_tltl id0 s0 lsl1))
    | Coq_sterm_select (s1, t1, s2, s3) -> Coq_sterm_select
        ((subst_tt id0 s0 s1), t1, (subst_tt id0 s0 s2),
        (subst_tt id0 s0 s3))
  
  (** val subst_tlt : LLVMsyntax.id -> sterm -> list_sterm -> list_sterm **)
  
  and subst_tlt id0 s0 = function
    | Nil_list_sterm -> Nil_list_sterm
    | Cons_list_sterm (s, ls') -> Cons_list_sterm (
        (subst_tt id0 s0 s), (subst_tlt id0 s0 ls'))
  
  (** val subst_tltl :
      LLVMsyntax.id -> sterm -> list_sterm_l -> list_sterm_l **)
  
  and subst_tltl id0 s0 = function
    | Nil_list_sterm_l -> Nil_list_sterm_l
    | Cons_list_sterm_l (s, l0, ls') -> Cons_list_sterm_l
        ((subst_tt id0 s0 s), l0, (subst_tltl id0 s0 ls'))
  
  (** val subst_tm : LLVMsyntax.id -> sterm -> smem -> smem **)
  
  and subst_tm id0 s0 = function
    | Coq_smem_init -> Coq_smem_init
    | Coq_smem_malloc (m1, t1, sz0, align0) -> Coq_smem_malloc
        ((subst_tm id0 s0 m1), t1, sz0, align0)
    | Coq_smem_free (m1, t1, s1) -> Coq_smem_free (
        (subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1))
    | Coq_smem_alloca (m1, t1, sz0, align0) -> Coq_smem_alloca
        ((subst_tm id0 s0 m1), t1, sz0, align0)
    | Coq_smem_load (m1, t1, s1) -> Coq_smem_load (
        (subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1))
    | Coq_smem_store (m1, t1, s1, s2) -> Coq_smem_store
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1),
        (subst_tt id0 s0 s2))
  
  (** val subst_mt : smap -> sterm -> sterm **)
  
  let rec subst_mt sm s =
    match sm with
      | Nil -> s
      | Cons (p, sm') ->
          let Pair (id0, s0) = p in subst_mt sm' (subst_tt id0 s0 s)
  
  (** val subst_mm : smap -> smem -> smem **)
  
  let rec subst_mm sm m =
    match sm with
      | Nil -> m
      | Cons (p, sm') ->
          let Pair (id0, s0) = p in subst_mm sm' (subst_tm id0 s0 m)
 end

(** val sumbool2bool : sumbool -> bool **)

let sumbool2bool = function
  | Left -> True
  | Right -> False

type typ_dec_prop = LLVMsyntax.typ -> sumbool

type list_typ_dec_prop = LLVMsyntax.list_typ -> sumbool

(** val typ_mutrec_dec :
    (LLVMsyntax.typ -> typ_dec_prop, LLVMsyntax.list_typ ->
    list_typ_dec_prop) prod **)

let typ_mutrec_dec =
  LLVMsyntax.typ_mutrec (fun s t2 ->
    match t2 with
      | LLVMsyntax.Coq_typ_int s0 -> eq_nat_dec s s0
      | _ -> Right) (fun t2 ->
    match t2 with
      | LLVMsyntax.Coq_typ_void -> Left
      | _ -> Right) (fun t2 ->
    match t2 with
      | LLVMsyntax.Coq_typ_label -> Left
      | _ -> Right) (fun t2 ->
    match t2 with
      | LLVMsyntax.Coq_typ_metadata -> Left
      | _ -> Right) (fun s t h t2 ->
    match t2 with
      | LLVMsyntax.Coq_typ_array (s0, t3) ->
          (match h t3 with
             | Left -> eq_nat_dec s s0
             | Right -> Right)
      | _ -> Right) (fun t h l0 h0 t2 ->
    match t2 with
      | LLVMsyntax.Coq_typ_function (t3, l1) ->
          (match h t3 with
             | Left -> h0 l1
             | Right -> Right)
      | _ -> Right) (fun l0 h t2 ->
    match t2 with
      | LLVMsyntax.Coq_typ_struct l1 -> h l1
      | _ -> Right) (fun t h t2 ->
    match t2 with
      | LLVMsyntax.Coq_typ_pointer t3 -> h t3
      | _ -> Right) (fun lt2 ->
    match lt2 with
      | LLVMsyntax.Nil_list_typ -> Left
      | LLVMsyntax.Cons_list_typ (t, lt3) -> Right) (fun t h l0 h0 lt2 ->
    match lt2 with
      | LLVMsyntax.Nil_list_typ -> Right
      | LLVMsyntax.Cons_list_typ (t0, lt3) ->
          (match h t0 with
             | Left -> h0 lt3
             | Right -> Right))

type const_dec_prop = LLVMsyntax.const -> sumbool

type list_const_dec_prop = LLVMsyntax.list_const -> sumbool

(** val const_mutrec_dec :
    (LLVMsyntax.const -> const_dec_prop, LLVMsyntax.list_const ->
    list_const_dec_prop) prod **)

let const_mutrec_dec =
  LLVMsyntax.const_mutrec (fun s i0 c2 ->
    match c2 with
      | LLVMsyntax.Coq_const_int (s0, i1) ->
          (match eq_nat_dec i0 i1 with
             | Left -> eq_nat_dec s s0
             | Right -> Right)
      | _ -> Right) (fun t c2 ->
    match c2 with
      | LLVMsyntax.Coq_const_undef t0 ->
          let Pair (t1, l0) = typ_mutrec_dec in t1 t t0
      | _ -> Right) (fun t c2 ->
    match c2 with
      | LLVMsyntax.Coq_const_null t0 ->
          let Pair (t1, l0) = typ_mutrec_dec in t1 t t0
      | _ -> Right) (fun l0 h c2 ->
    match c2 with
      | LLVMsyntax.Coq_const_arr l1 -> h l1
      | _ -> Right) (fun l0 h c2 ->
    match c2 with
      | LLVMsyntax.Coq_const_struct l1 -> h l1
      | _ -> Right) (fun t i0 c2 ->
    match c2 with
      | LLVMsyntax.Coq_const_gid (t0, i1) ->
          (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
             | Left -> AtomImpl.eq_atom_dec i0 i1
             | Right -> Right)
      | _ -> Right) (fun lc2 ->
    match lc2 with
      | LLVMsyntax.Nil_list_const -> Left
      | LLVMsyntax.Cons_list_const (c, lc3) -> Right) (fun c h l0 h0 lc2 ->
    match lc2 with
      | LLVMsyntax.Nil_list_const -> Right
      | LLVMsyntax.Cons_list_const (c0, lc3) ->
          (match h c0 with
             | Left -> h0 lc3
             | Right -> Right))

(** val value_dec : LLVMsyntax.value -> LLVMsyntax.value -> sumbool **)

let value_dec v1 v2 =
  match v1 with
    | LLVMsyntax.Coq_value_id x ->
        (match v2 with
           | LLVMsyntax.Coq_value_id i1 -> AtomImpl.eq_atom_dec x i1
           | LLVMsyntax.Coq_value_const c -> Right)
    | LLVMsyntax.Coq_value_const x ->
        (match v2 with
           | LLVMsyntax.Coq_value_id i0 -> Right
           | LLVMsyntax.Coq_value_const c0 ->
               let Pair (c, l0) = const_mutrec_dec in c x c0)

(** val list_value_dec :
    LLVMsyntax.list_value -> LLVMsyntax.list_value -> sumbool **)

let rec list_value_dec l0 lv0 =
  match l0 with
    | LLVMsyntax.Nil_list_value ->
        (match lv0 with
           | LLVMsyntax.Nil_list_value -> Left
           | LLVMsyntax.Cons_list_value (v, l1) -> Right)
    | LLVMsyntax.Cons_list_value (v, l1) ->
        (match lv0 with
           | LLVMsyntax.Nil_list_value -> Right
           | LLVMsyntax.Cons_list_value (v0, l2) ->
               (match value_dec v v0 with
                  | Left -> list_value_dec l1 l2
                  | Right -> Right))

(** val bop_dec : LLVMsyntax.bop -> LLVMsyntax.bop -> sumbool **)

let bop_dec b1 b2 =
  match b1 with
    | LLVMsyntax.Coq_bop_add ->
        (match b2 with
           | LLVMsyntax.Coq_bop_add -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_bop_lshr ->
        (match b2 with
           | LLVMsyntax.Coq_bop_lshr -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_bop_and ->
        (match b2 with
           | LLVMsyntax.Coq_bop_and -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_bop_or ->
        (match b2 with
           | LLVMsyntax.Coq_bop_or -> Left
           | _ -> Right)

(** val extop_dec : LLVMsyntax.extop -> LLVMsyntax.extop -> sumbool **)

let extop_dec e1 e2 =
  match e1 with
    | LLVMsyntax.Coq_extop_z ->
        (match e2 with
           | LLVMsyntax.Coq_extop_z -> Left
           | LLVMsyntax.Coq_extop_s -> Right)
    | LLVMsyntax.Coq_extop_s ->
        (match e2 with
           | LLVMsyntax.Coq_extop_z -> Right
           | LLVMsyntax.Coq_extop_s -> Left)

(** val castop_dec : LLVMsyntax.castop -> LLVMsyntax.castop -> sumbool **)

let castop_dec c1 c2 =
  match c1 with
    | LLVMsyntax.Coq_castop_fptoui ->
        (match c2 with
           | LLVMsyntax.Coq_castop_fptoui -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_castop_fptosi ->
        (match c2 with
           | LLVMsyntax.Coq_castop_fptosi -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_castop_uitofp ->
        (match c2 with
           | LLVMsyntax.Coq_castop_uitofp -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_castop_sitofp ->
        (match c2 with
           | LLVMsyntax.Coq_castop_sitofp -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_castop_ptrtoint ->
        (match c2 with
           | LLVMsyntax.Coq_castop_ptrtoint -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_castop_inttoptr ->
        (match c2 with
           | LLVMsyntax.Coq_castop_inttoptr -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_castop_bitcast ->
        (match c2 with
           | LLVMsyntax.Coq_castop_bitcast -> Left
           | _ -> Right)

(** val cond_dec : LLVMsyntax.cond -> LLVMsyntax.cond -> sumbool **)

let cond_dec c1 c2 =
  match c1 with
    | LLVMsyntax.Coq_cond_eq ->
        (match c2 with
           | LLVMsyntax.Coq_cond_eq -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_cond_ne ->
        (match c2 with
           | LLVMsyntax.Coq_cond_ne -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_cond_ugt ->
        (match c2 with
           | LLVMsyntax.Coq_cond_ugt -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_cond_uge ->
        (match c2 with
           | LLVMsyntax.Coq_cond_uge -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_cond_ult ->
        (match c2 with
           | LLVMsyntax.Coq_cond_ult -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_cond_ule ->
        (match c2 with
           | LLVMsyntax.Coq_cond_ule -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_cond_sgt ->
        (match c2 with
           | LLVMsyntax.Coq_cond_sgt -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_cond_sge ->
        (match c2 with
           | LLVMsyntax.Coq_cond_sge -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_cond_slt ->
        (match c2 with
           | LLVMsyntax.Coq_cond_slt -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_cond_sle ->
        (match c2 with
           | LLVMsyntax.Coq_cond_sle -> Left
           | _ -> Right)

type sterm_dec_prop = SimpleSE.sterm -> sumbool

type list_sterm_dec_prop = SimpleSE.list_sterm -> sumbool

type list_sterm_l_dec_prop = SimpleSE.list_sterm_l -> sumbool

type smem_dec_prop = SimpleSE.smem -> sumbool

type sframe_dec_prop = SimpleSE.sframe -> sumbool

(** val se_dec :
    ((((SimpleSE.sterm -> sterm_dec_prop, SimpleSE.list_sterm ->
    list_sterm_dec_prop) prod, SimpleSE.list_sterm_l ->
    list_sterm_l_dec_prop) prod, SimpleSE.smem -> smem_dec_prop) prod,
    SimpleSE.sframe -> sframe_dec_prop) prod **)

let se_dec =
  SimpleSE.se_mutrec (fun v st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_val v0 -> value_dec v v0
      | _ -> Right) (fun b s s0 h s1 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_bop (b0, s2, st2_1, st2_2) ->
          (match bop_dec b b0 with
             | Left ->
                 (match eq_nat_dec s s2 with
                    | Left ->
                        (match h st2_1 with
                           | Left -> h0 st2_2
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun t s h l0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_extractvalue (t0, st3, l1) ->
          (match let Pair (t1, l2) = typ_mutrec_dec in t1 t t0 with
             | Left ->
                 (match h st3 with
                    | Left -> let Pair (c, l2) = const_mutrec_dec in l2 l0 l1
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun t s h t0 s0 h0 l0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_insertvalue (t1, st2_1, t2, st2_2, l1) ->
          (match let Pair (t3, l2) = typ_mutrec_dec in t3 t t1 with
             | Left ->
                 (match h st2_1 with
                    | Left ->
                        (match let Pair (t3, l2) = typ_mutrec_dec in t3 t0 t2 with
                           | Left ->
                               (match h0 st2_2 with
                                  | Left ->
                                      let Pair (c, l2) = const_mutrec_dec in
                                      l2 l0 l1
                                  | Right -> Right)
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun s h t s0 a st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_malloc (s1, t0, s2, a0) ->
          (match h s1 with
             | Left ->
                 (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                    | Left ->
                        (match eq_nat_dec s0 s2 with
                           | Left -> eq_nat_dec a a0
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun s h t s0 a st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_alloca (s1, t0, s2, a0) ->
          (match h s1 with
             | Left ->
                 (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                    | Left ->
                        (match eq_nat_dec s0 s2 with
                           | Left -> eq_nat_dec a a0
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun s h t s0 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_load (s1, t0, st3) ->
          (match h s1 with
             | Left ->
                 (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                    | Left -> h0 st3
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun i0 t s h l0 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_gep (i1, t0, st3, l1) ->
          (match bool_dec i0 i1 with
             | Left ->
                 (match let Pair (t1, l2) = typ_mutrec_dec in t1 t t0 with
                    | Left ->
                        (match h st3 with
                           | Left -> h0 l1
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun e t s h t0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_ext (e0, t1, st3, t2) ->
          (match extop_dec e e0 with
             | Left ->
                 (match let Pair (t3, l0) = typ_mutrec_dec in t3 t t1 with
                    | Left ->
                        (match h st3 with
                           | Left ->
                               let Pair (t3, l0) = typ_mutrec_dec in t3 t0 t2
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun c t s h t0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_cast (c0, t1, st3, t2) ->
          (match castop_dec c c0 with
             | Left ->
                 (match let Pair (t3, l0) = typ_mutrec_dec in t3 t t1 with
                    | Left ->
                        (match h st3 with
                           | Left ->
                               let Pair (t3, l0) = typ_mutrec_dec in t3 t0 t2
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun c t s h s0 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_icmp (c0, t0, st2_1, st2_2) ->
          (match cond_dec c c0 with
             | Left ->
                 (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                    | Left ->
                        (match h st2_1 with
                           | Left -> h0 st2_2
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun t l0 h st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_phi (t0, l1) ->
          (match let Pair (t1, l2) = typ_mutrec_dec in t1 t t0 with
             | Left -> h l1
             | Right -> Right)
      | _ -> Right) (fun s h t s0 h0 s1 h1 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_select (st2_1, t0, st2_2, st2_3) ->
          (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
             | Left ->
                 (match h st2_1 with
                    | Left ->
                        (match h0 st2_2 with
                           | Left -> h1 st2_3
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun sts2 ->
    match sts2 with
      | SimpleSE.Nil_list_sterm -> Left
      | SimpleSE.Cons_list_sterm (s, sts3) -> Right) (fun s h l0 h0 sts2 ->
    match sts2 with
      | SimpleSE.Nil_list_sterm -> Right
      | SimpleSE.Cons_list_sterm (s0, sts3) ->
          (match h s0 with
             | Left -> h0 sts3
             | Right -> Right)) (fun stls2 ->
    match stls2 with
      | SimpleSE.Nil_list_sterm_l -> Left
      | SimpleSE.Cons_list_sterm_l (s, l0, stls3) -> Right)
    (fun s h l0 l1 h0 stls2 ->
    match stls2 with
      | SimpleSE.Nil_list_sterm_l -> Right
      | SimpleSE.Cons_list_sterm_l (s0, l2, stls3) ->
          (match h s0 with
             | Left ->
                 (match AtomImpl.eq_atom_dec l0 l2 with
                    | Left -> h0 stls3
                    | Right -> Right)
             | Right -> Right)) (fun sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_init -> Left
      | _ -> Right) (fun s h t s0 a sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_malloc (sm3, t0, s1, a0) ->
          (match h sm3 with
             | Left ->
                 (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                    | Left ->
                        (match eq_nat_dec s0 s1 with
                           | Left -> eq_nat_dec a a0
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun s h t s0 h0 sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_free (sm3, t0, s1) ->
          (match h sm3 with
             | Left ->
                 (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                    | Left -> h0 s1
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun s h t s0 a sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_alloca (sm3, t0, s1, a0) ->
          (match h sm3 with
             | Left ->
                 (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                    | Left ->
                        (match eq_nat_dec s0 s1 with
                           | Left -> eq_nat_dec a a0
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun s h t s0 h0 sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_load (sm3, t0, s1) ->
          (match h sm3 with
             | Left ->
                 (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                    | Left -> h0 s1
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun s h t s0 h0 s1 h1 sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_store (sm3, t0, s2, s3) ->
          (match h sm3 with
             | Left ->
                 (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                    | Left ->
                        (match h0 s2 with
                           | Left -> h1 s3
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right)
      | _ -> Right) (fun sf2 ->
    match sf2 with
      | SimpleSE.Coq_sframe_init -> Left
      | SimpleSE.Coq_sframe_alloca (s, sf3, t, s0, a) -> Right)
    (fun s h s0 h0 t s1 a sf2 ->
    match sf2 with
      | SimpleSE.Coq_sframe_init -> Right
      | SimpleSE.Coq_sframe_alloca (s2, sf3, t0, s3, a0) ->
          (match h s2 with
             | Left ->
                 (match h0 sf3 with
                    | Left ->
                        (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                           | Left ->
                               (match eq_nat_dec s1 s3 with
                                  | Left -> eq_nat_dec a a0
                                  | Right -> Right)
                           | Right -> Right)
                    | Right -> Right)
             | Right -> Right))

(** val smap_dec : SimpleSE.smap -> SimpleSE.smap -> sumbool **)

let rec smap_dec l0 sm0 =
  match l0 with
    | Nil -> (match sm0 with
                | Nil -> Left
                | Cons (p, l1) -> Right)
    | Cons (a, l1) ->
        (match sm0 with
           | Nil -> Right
           | Cons (p, l2) ->
               (match let Pair (a0, s) = a in
                      let Pair (a1, s0) = p in
                      (match AtomImpl.eq_atom_dec a0 a1 with
                         | Left ->
                             let Pair (p0, x) = se_dec in
                             let Pair (p1, x0) = p0 in
                             let Pair (p2, x1) = p1 in
                             let Pair (h, l3) = p2 in h s s0
                         | Right -> Right) with
                  | Left -> smap_dec l1 l2
                  | Right -> Right))

(** val sterms_dec :
    SimpleSE.sterm list -> SimpleSE.sterm list -> sumbool **)

let rec sterms_dec l0 ts0 =
  match l0 with
    | Nil -> (match ts0 with
                | Nil -> Left
                | Cons (s, l1) -> Right)
    | Cons (a, l1) ->
        (match ts0 with
           | Nil -> Right
           | Cons (s, l2) ->
               (match let Pair (p, x) = se_dec in
                      let Pair (p0, x0) = p in
                      let Pair (p1, x1) = p0 in
                      let Pair (h, l3) = p1 in h a s with
                  | Left -> sterms_dec l1 l2
                  | Right -> Right))

(** val sstate_dec : SimpleSE.sstate -> SimpleSE.sstate -> sumbool **)

let sstate_dec sts1 sts2 =
  let { SimpleSE.coq_STerms = x; SimpleSE.coq_SMem = x0;
    SimpleSE.coq_SFrame = x1; SimpleSE.coq_SEffects = x2 } = sts1
  in
  let { SimpleSE.coq_STerms = sTerms1; SimpleSE.coq_SMem = sMem1;
    SimpleSE.coq_SFrame = sFrame1; SimpleSE.coq_SEffects = sEffects1 } = sts2
  in
  (match smap_dec x sTerms1 with
     | Left ->
         (match let Pair (p, x3) = se_dec in
                let Pair (p0, h) = p in h x0 sMem1 with
            | Left ->
                (match let Pair (p, h) = se_dec in h x1 sFrame1 with
                   | Left -> sterms_dec x2 sEffects1
                   | Right -> Right)
            | Right -> Right)
     | Right -> Right)

(** val params_dec : LLVMsyntax.params -> LLVMsyntax.params -> sumbool **)

let rec params_dec l0 p0 =
  match l0 with
    | Nil -> (match p0 with
                | Nil -> Left
                | Cons (p, l1) -> Right)
    | Cons (a, l1) ->
        (match p0 with
           | Nil -> Right
           | Cons (p, l2) ->
               (match let Pair (t, v) = a in
                      let Pair (t0, v0) = p in
                      (match let Pair (t1, l3) = typ_mutrec_dec in t1 t t0 with
                         | Left -> value_dec v v0
                         | Right -> Right) with
                  | Left -> params_dec l1 l2
                  | Right -> Right))

(** val cmd_dec : LLVMsyntax.cmd -> LLVMsyntax.cmd -> sumbool **)

let cmd_dec c1 c2 =
  match c1 with
    | LLVMsyntax.Coq_insn_bop (i0, b, s, v, v0) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_bop (i1, b0, s0, v1, v2) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match bop_dec b b0 with
                         | Left ->
                             (match eq_nat_dec s s0 with
                                | Left ->
                                    (match value_dec v v1 with
                                       | Left -> value_dec v0 v2
                                       | Right -> Right)
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_extractvalue (i0, t, v, l0) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_extractvalue (i1, t0, v0, l1) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match let Pair (t1, l2) = typ_mutrec_dec in t1 t t0 with
                         | Left ->
                             (match value_dec v v0 with
                                | Left ->
                                    let Pair (c, l2) = const_mutrec_dec in
                                    l2 l0 l1
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_insertvalue (i0, t, v, t0, v0, l0) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_insertvalue (i1, t1, v1, t2, v2, l1) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match let Pair (t3, l2) = typ_mutrec_dec in t3 t t1 with
                         | Left ->
                             (match value_dec v v1 with
                                | Left ->
                                    (match let Pair (t3, l2) = typ_mutrec_dec
                                           in
                                           t3 t0 t2 with
                                       | Left ->
                                           (match value_dec v0 v2 with
                                              | Left ->
                                                  let Pair (
                                                  c, l2) = const_mutrec_dec
                                                  in
                                                  l2 l0 l1
                                              | Right -> Right)
                                       | Right -> Right)
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_malloc (i0, t, s, a) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_malloc (i1, t0, s0, a0) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                         | Left ->
                             (match eq_nat_dec s s0 with
                                | Left -> eq_nat_dec a a0
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_free (i0, t, v) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_free (i1, t0, v0) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                         | Left -> value_dec v v0
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_alloca (i0, t, s, a) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_alloca (i1, t0, s0, a0) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                         | Left ->
                             (match eq_nat_dec s s0 with
                                | Left -> eq_nat_dec a a0
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_load (i0, t, v) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_load (i1, t0, v0) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                         | Left -> value_dec v v0
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_store (i0, t, v, v0) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_store (i1, t0, v1, v2) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                         | Left ->
                             (match value_dec v v1 with
                                | Left -> value_dec v0 v2
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_gep (i0, i1, t, v, l0) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_gep (i2, i3, t0, v0, l1) ->
               (match AtomImpl.eq_atom_dec i0 i2 with
                  | Left ->
                      (match bool_dec i1 i3 with
                         | Left ->
                             (match let Pair (t1, l2) = typ_mutrec_dec in
                                    t1 t t0 with
                                | Left ->
                                    (match value_dec v v0 with
                                       | Left -> list_value_dec l0 l1
                                       | Right -> Right)
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_ext (i0, e, t, v, t0) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_ext (i1, e0, t1, v0, t2) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match extop_dec e e0 with
                         | Left ->
                             (match let Pair (t3, l0) = typ_mutrec_dec in
                                    t3 t t1 with
                                | Left ->
                                    (match value_dec v v0 with
                                       | Left ->
                                           let Pair (t3, l0) = typ_mutrec_dec
                                           in
                                           t3 t0 t2
                                       | Right -> Right)
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_cast (i0, c, t, v, t0) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_cast (i1, c0, t1, v0, t2) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match castop_dec c c0 with
                         | Left ->
                             (match let Pair (t3, l0) = typ_mutrec_dec in
                                    t3 t t1 with
                                | Left ->
                                    (match value_dec v v0 with
                                       | Left ->
                                           let Pair (t3, l0) = typ_mutrec_dec
                                           in
                                           t3 t0 t2
                                       | Right -> Right)
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_icmp (i0, c, t, v, v0) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_icmp (i1, c0, t0, v1, v2) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match cond_dec c c0 with
                         | Left ->
                             (match let Pair (t1, l0) = typ_mutrec_dec in
                                    t1 t t0 with
                                | Left ->
                                    (match value_dec v v1 with
                                       | Left -> value_dec v0 v2
                                       | Right -> Right)
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_select (i0, v, t, v0, v1) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_select (i1, v2, t0, v3, v4) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match value_dec v v2 with
                         | Left ->
                             (match let Pair (t1, l0) = typ_mutrec_dec in
                                    t1 t t0 with
                                | Left ->
                                    (match value_dec v0 v3 with
                                       | Left -> value_dec v1 v4
                                       | Right -> Right)
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_call (i0, n, t, t0, i1, p) ->
        (match c2 with
           | LLVMsyntax.Coq_insn_call (i2, n0, t1, t2, i3, p0) ->
               (match AtomImpl.eq_atom_dec i0 i2 with
                  | Left ->
                      (match AtomImpl.eq_atom_dec i1 i3 with
                         | Left ->
                             (match bool_dec n n0 with
                                | Left ->
                                    (match bool_dec t t1 with
                                       | Left ->
                                           (match let Pair (
                                                  t3, l0) = typ_mutrec_dec
                                                  in
                                                  t3 t0 t2 with
                                              | Left -> params_dec p p0
                                              | Right -> Right)
                                       | Right -> Right)
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)

(** val terminator_dec :
    LLVMsyntax.terminator -> LLVMsyntax.terminator -> sumbool **)

let terminator_dec tmn1 tmn2 =
  match tmn1 with
    | LLVMsyntax.Coq_insn_return (i0, t, v) ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_return (i1, t0, v0) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
                         | Left -> value_dec v v0
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_return_void i0 ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_return_void i1 -> AtomImpl.eq_atom_dec i0 i1
           | _ -> Right)
    | LLVMsyntax.Coq_insn_br (i0, v, l0, l1) ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_br (i1, v0, l2, l3) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match AtomImpl.eq_atom_dec l0 l2 with
                         | Left ->
                             (match AtomImpl.eq_atom_dec l1 l3 with
                                | Left -> value_dec v v0
                                | Right -> Right)
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_br_uncond (i0, l0) ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_br_uncond (i1, l1) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left -> AtomImpl.eq_atom_dec l0 l1
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_insn_unreachable i0 ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_unreachable i1 -> AtomImpl.eq_atom_dec i0 i1
           | _ -> Right)

(** val list_id_l_dec :
    LLVMsyntax.list_id_l -> LLVMsyntax.list_id_l -> sumbool **)

let rec list_id_l_dec l0 l2 =
  match l0 with
    | LLVMsyntax.Nil_list_id_l ->
        (match l2 with
           | LLVMsyntax.Nil_list_id_l -> Left
           | LLVMsyntax.Cons_list_id_l (i0, l1, l3) -> Right)
    | LLVMsyntax.Cons_list_id_l (i0, l1, l3) ->
        (match l2 with
           | LLVMsyntax.Nil_list_id_l -> Right
           | LLVMsyntax.Cons_list_id_l (i1, l4, l5) ->
               (match AtomImpl.eq_atom_dec i0 i1 with
                  | Left ->
                      (match AtomImpl.eq_atom_dec l1 l4 with
                         | Left -> list_id_l_dec l3 l5
                         | Right -> Right)
                  | Right -> Right))

(** val phinode_dec : LLVMsyntax.phinode -> LLVMsyntax.phinode -> sumbool **)

let phinode_dec p1 p2 =
  let LLVMsyntax.Coq_insn_phi (i0, t, l0) = p1 in
  let LLVMsyntax.Coq_insn_phi (i1, t0, l1) = p2 in
  (match AtomImpl.eq_atom_dec i0 i1 with
     | Left ->
         (match let Pair (t1, l2) = typ_mutrec_dec in t1 t t0 with
            | Left -> list_id_l_dec l0 l1
            | Right -> Right)
     | Right -> Right)

(** val arg_dec : LLVMsyntax.arg -> LLVMsyntax.arg -> sumbool **)

let arg_dec a1 a2 =
  let Pair (t, i0) = a1 in
  let Pair (t0, i1) = a2 in
  (match AtomImpl.eq_atom_dec i0 i1 with
     | Left -> let Pair (t1, l0) = typ_mutrec_dec in t1 t t0
     | Right -> Right)

(** val args_dec : LLVMsyntax.args -> LLVMsyntax.args -> sumbool **)

let rec args_dec l0 l2 =
  match l0 with
    | Nil -> (match l2 with
                | Nil -> Left
                | Cons (p, l3) -> Right)
    | Cons (a, l1) ->
        (match l2 with
           | Nil -> Right
           | Cons (p, l3) ->
               (match arg_dec a p with
                  | Left -> args_dec l1 l3
                  | Right -> Right))

(** val fheader_dec : LLVMsyntax.fheader -> LLVMsyntax.fheader -> sumbool **)

let fheader_dec f1 f2 =
  let LLVMsyntax.Coq_fheader_intro (t, i0, a) = f1 in
  let LLVMsyntax.Coq_fheader_intro (t0, i1, a0) = f2 in
  (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
     | Left ->
         (match AtomImpl.eq_atom_dec i0 i1 with
            | Left -> args_dec a a0
            | Right -> Right)
     | Right -> Right)

(** val gvar_dec : LLVMsyntax.gvar -> LLVMsyntax.gvar -> sumbool **)

let gvar_dec g1 g2 =
  let LLVMsyntax.Coq_gvar_intro (i0, t, c, a) = g1 in
  let LLVMsyntax.Coq_gvar_intro (i1, t0, c0, a0) = g2 in
  (match AtomImpl.eq_atom_dec i0 i1 with
     | Left ->
         (match let Pair (t1, l0) = typ_mutrec_dec in t1 t t0 with
            | Left ->
                (match let Pair (c1, l0) = const_mutrec_dec in c1 c c0 with
                   | Left -> eq_nat_dec a a0
                   | Right -> Right)
            | Right -> Right)
     | Right -> Right)

(** val fdec_dec : LLVMsyntax.fdec -> LLVMsyntax.fdec -> sumbool **)

let fdec_dec f1 f2 =
  fheader_dec f1 f2

(** val layout_dec : LLVMsyntax.layout -> LLVMsyntax.layout -> sumbool **)

let layout_dec l1 l2 =
  match l1 with
    | LLVMsyntax.Coq_layout_be ->
        (match l2 with
           | LLVMsyntax.Coq_layout_be -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_layout_le ->
        (match l2 with
           | LLVMsyntax.Coq_layout_le -> Left
           | _ -> Right)
    | LLVMsyntax.Coq_layout_ptr (s, a, a0) ->
        (match l2 with
           | LLVMsyntax.Coq_layout_ptr (s0, a1, a2) ->
               (match eq_nat_dec s s0 with
                  | Left ->
                      (match eq_nat_dec a a1 with
                         | Left -> eq_nat_dec a0 a2
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_layout_int (s, a, a0) ->
        (match l2 with
           | LLVMsyntax.Coq_layout_int (s0, a1, a2) ->
               (match eq_nat_dec s s0 with
                  | Left ->
                      (match eq_nat_dec a a1 with
                         | Left -> eq_nat_dec a0 a2
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_layout_aggr (s, a, a0) ->
        (match l2 with
           | LLVMsyntax.Coq_layout_aggr (s0, a1, a2) ->
               (match eq_nat_dec s s0 with
                  | Left ->
                      (match eq_nat_dec a a1 with
                         | Left -> eq_nat_dec a0 a2
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)
    | LLVMsyntax.Coq_layout_stack (s, a, a0) ->
        (match l2 with
           | LLVMsyntax.Coq_layout_stack (s0, a1, a2) ->
               (match eq_nat_dec s s0 with
                  | Left ->
                      (match eq_nat_dec a a1 with
                         | Left -> eq_nat_dec a0 a2
                         | Right -> Right)
                  | Right -> Right)
           | _ -> Right)

(** val layouts_dec : LLVMsyntax.layouts -> LLVMsyntax.layouts -> sumbool **)

let rec layouts_dec l0 l2 =
  match l0 with
    | Nil -> (match l2 with
                | Nil -> Left
                | Cons (l1, l3) -> Right)
    | Cons (a, l1) ->
        (match l2 with
           | Nil -> Right
           | Cons (l3, l4) ->
               (match layout_dec a l3 with
                  | Left -> layouts_dec l1 l4
                  | Right -> Right))

(** val tv_cmds : SimpleSE.nbranch list -> SimpleSE.nbranch list -> bool **)

let tv_cmds nbs1 nbs2 =
  sumbool2bool
    (sstate_dec (SimpleSE.se_cmds SimpleSE.sstate_init nbs1)
      (SimpleSE.se_cmds SimpleSE.sstate_init nbs2))

(** val tv_subblock : SimpleSE.subblock -> SimpleSE.subblock -> bool **)

let tv_subblock sb1 sb2 =
  let { SimpleSE.coq_NBs = nbs1; SimpleSE.call_cmd = call1 } = sb1 in
  let { SimpleSE.coq_NBs = nbs2; SimpleSE.call_cmd = call2 } = sb2 in
  (match sumbool2bool
           (sstate_dec (SimpleSE.se_cmds SimpleSE.sstate_init nbs1)
             (SimpleSE.se_cmds SimpleSE.sstate_init nbs2)) with
     | True -> sumbool2bool (cmd_dec call1 call2)
     | False -> False)

(** val tv_subblocks :
    SimpleSE.subblock list -> SimpleSE.subblock list -> bool **)

let rec tv_subblocks sbs1 sbs2 =
  match sbs1 with
    | Nil -> (match sbs2 with
                | Nil -> True
                | Cons (s, l0) -> False)
    | Cons (sb1, sbs1') ->
        (match sbs2 with
           | Nil -> False
           | Cons (sb2, sbs2') ->
               (match tv_subblock sb1 sb2 with
                  | True -> tv_subblocks sbs1' sbs2'
                  | False -> False))

(** val tv_phinodes : LLVMsyntax.phinodes -> LLVMsyntax.phinodes -> bool **)

let rec tv_phinodes ps1 ps2 =
  match ps1 with
    | Nil -> (match ps2 with
                | Nil -> True
                | Cons (p, l0) -> False)
    | Cons (p1, ps1') ->
        (match ps2 with
           | Nil -> False
           | Cons (p2, ps2') ->
               (match sumbool2bool (phinode_dec p1 p2) with
                  | True -> tv_phinodes ps1' ps2'
                  | False -> False))

(** val tv_block : LLVMsyntax.block -> LLVMsyntax.block -> bool **)

let tv_block b1 b2 =
  let LLVMsyntax.Coq_block_intro (l1, ps1, cs1, tmn1) = b1 in
  let LLVMsyntax.Coq_block_intro (l2, ps2, cs2, tmn2) = b2 in
  let Pair (sbs1, nbs1) = SimpleSE.cmds2sbs cs1 in
  let Pair (sbs2, nbs2) = SimpleSE.cmds2sbs cs2 in
  (match match match match sumbool2bool (AtomImpl.eq_atom_dec l1 l2) with
                       | True -> tv_phinodes ps1 ps2
                       | False -> False with
                 | True -> tv_subblocks sbs1 sbs2
                 | False -> False with
           | True -> tv_cmds nbs1 nbs2
           | False -> False with
     | True -> sumbool2bool (terminator_dec tmn1 tmn2)
     | False -> False)

(** val tv_blocks : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool **)

let rec tv_blocks bs1 bs2 =
  match bs1 with
    | Nil -> (match bs2 with
                | Nil -> True
                | Cons (b, l0) -> False)
    | Cons (b1, bs1') ->
        (match bs2 with
           | Nil -> False
           | Cons (b2, bs2') ->
               (match tv_block b1 b2 with
                  | True -> tv_blocks bs1' bs2'
                  | False -> False))

(** val tv_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool **)

let tv_fdef f1 f2 =
  let LLVMsyntax.Coq_fdef_intro (fh1, lb1) = f1 in
  let LLVMsyntax.Coq_fdef_intro (fh2, lb2) = f2 in
  (match sumbool2bool (fheader_dec fh1 fh2) with
     | True -> tv_blocks lb1 lb2
     | False -> False)

(** val tv_products : LLVMsyntax.products -> LLVMsyntax.products -> bool **)

let rec tv_products ps1 ps2 =
  match ps1 with
    | Nil -> (match ps2 with
                | Nil -> True
                | Cons (p, l0) -> False)
    | Cons (p, ps1') ->
        (match p with
           | LLVMsyntax.Coq_product_gvar gvar1 ->
               (match ps2 with
                  | Nil -> False
                  | Cons (p0, ps2') ->
                      (match p0 with
                         | LLVMsyntax.Coq_product_gvar gvar2 ->
                             (match sumbool2bool (gvar_dec gvar1 gvar2) with
                                | True -> tv_products ps1' ps2'
                                | False -> False)
                         | _ -> False))
           | LLVMsyntax.Coq_product_fdec f1 ->
               (match ps2 with
                  | Nil -> False
                  | Cons (p0, ps2') ->
                      (match p0 with
                         | LLVMsyntax.Coq_product_fdec f2 ->
                             (match sumbool2bool (fdec_dec f1 f2) with
                                | True -> tv_products ps1' ps2'
                                | False -> False)
                         | _ -> False))
           | LLVMsyntax.Coq_product_fdef f1 ->
               (match ps2 with
                  | Nil -> False
                  | Cons (p0, ps2') ->
                      (match p0 with
                         | LLVMsyntax.Coq_product_fdef f2 ->
                             (match tv_fdef f1 f2 with
                                | True -> tv_products ps1' ps2'
                                | False -> False)
                         | _ -> False)))

(** val tv_module :
    LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool **)

let tv_module m1 m2 =
  let LLVMsyntax.Coq_module_intro (tD1, ps1) = m1 in
  let LLVMsyntax.Coq_module_intro (tD2, ps2) = m2 in
  (match sumbool2bool (layouts_dec tD1 tD2) with
     | True -> tv_products ps1 ps2
     | False -> False)

(** val tv_system : LLVMsyntax.system -> LLVMsyntax.system -> bool **)

let rec tv_system s1 s2 =
  match s1 with
    | Nil -> (match s2 with
                | Nil -> True
                | Cons (m, l0) -> False)
    | Cons (m1, s1') ->
        (match s2 with
           | Nil -> False
           | Cons (m2, s2') ->
               (match tv_module m1 m2 with
                  | True -> tv_system s1' s2'
                  | False -> False))

