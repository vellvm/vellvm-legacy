type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
  | Tt

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
  | true -> false
  | false -> true

type nat =
  | O
  | S of nat

type ('a, 'b) sum =
  | Inl of 'a
  | Inr of 'b

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
  | x,y -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
  | x,y -> y

type comparison =
  | Eq
  | Lt
  | Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
  | Eq -> Eq
  | Lt -> Gt
  | Gt -> Lt

(** val length : 'a1 list -> nat **)

let rec length = function
  | [] -> O
  | y::l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l0 m =
  match l0 with
    | [] -> m
    | a::l1 -> a::(app l1 m)

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type 'a exc = 'a option

(** val value : 'a1 -> 'a1 option **)

let value x =
  Some x

(** val error : 'a1 option **)

let error =
  None

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
    | O -> m
    | S p -> S (plus p m)

(** val eq_nat_dec : nat -> nat -> bool **)

let rec eq_nat_dec n m =
  match n with
    | O -> (match m with
              | O -> true
              | S m0 -> false)
    | S n0 -> (match m with
                 | O -> false
                 | S m0 -> eq_nat_dec n0 m0)

(** val le_lt_dec : nat -> nat -> bool **)

let rec le_lt_dec n m =
  match n with
    | O -> true
    | S n0 -> (match m with
                 | O -> false
                 | S m0 -> le_lt_dec n0 m0)

(** val beq_nat : nat -> nat -> bool **)

let rec beq_nat n m =
  match n with
    | O -> (match m with
              | O -> true
              | S n0 -> false)
    | S n1 -> (match m with
                 | O -> false
                 | S m1 -> beq_nat n1 m1)

(** val iter_nat : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter_nat n f x =
  match n with
    | O -> x
    | S n' -> f (iter_nat n' f x)

type positive =
  | XI of positive
  | XO of positive
  | XH

(** val psucc : positive -> positive **)

let rec psucc = function
  | XI p -> XO (psucc p)
  | XO p -> XI p
  | XH -> XO XH

(** val pplus : positive -> positive -> positive **)

let rec pplus x y =
  match x with
    | XI p ->
        (match y with
           | XI q -> XO (pplus_carry p q)
           | XO q -> XI (pplus p q)
           | XH -> XO (psucc p))
    | XO p ->
        (match y with
           | XI q -> XI (pplus p q)
           | XO q -> XO (pplus p q)
           | XH -> XI p)
    | XH ->
        (match y with
           | XI q -> XO (psucc q)
           | XO q -> XI q
           | XH -> XO XH)

(** val pplus_carry : positive -> positive -> positive **)

and pplus_carry x y =
  match x with
    | XI p ->
        (match y with
           | XI q -> XI (pplus_carry p q)
           | XO q -> XO (pplus_carry p q)
           | XH -> XI (psucc p))
    | XO p ->
        (match y with
           | XI q -> XO (pplus_carry p q)
           | XO q -> XI (pplus p q)
           | XH -> XO (psucc p))
    | XH ->
        (match y with
           | XI q -> XI (psucc q)
           | XO q -> XO (psucc q)
           | XH -> XI XH)

(** val pmult_nat : positive -> nat -> nat **)

let rec pmult_nat x pow2 =
  match x with
    | XI p -> plus pow2 (pmult_nat p (plus pow2 pow2))
    | XO p -> pmult_nat p (plus pow2 pow2)
    | XH -> pow2

(** val nat_of_P : positive -> nat **)

let nat_of_P x =
  pmult_nat x (S O)

(** val p_of_succ_nat : nat -> positive **)

let rec p_of_succ_nat = function
  | O -> XH
  | S x -> psucc (p_of_succ_nat x)

(** val pdouble_minus_one : positive -> positive **)

let rec pdouble_minus_one = function
  | XI p -> XI (XO p)
  | XO p -> XI (pdouble_minus_one p)
  | XH -> XH

type positive_mask =
  | IsNul
  | IsPos of positive
  | IsNeg

(** val pdouble_plus_one_mask : positive_mask -> positive_mask **)

let pdouble_plus_one_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

(** val pdouble_mask : positive_mask -> positive_mask **)

let pdouble_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

(** val pdouble_minus_two : positive -> positive_mask **)

let pdouble_minus_two = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pdouble_minus_one p))
  | XH -> IsNul

(** val pminus_mask : positive -> positive -> positive_mask **)

let rec pminus_mask x y =
  match x with
    | XI p ->
        (match y with
           | XI q -> pdouble_mask (pminus_mask p q)
           | XO q -> pdouble_plus_one_mask (pminus_mask p q)
           | XH -> IsPos (XO p))
    | XO p ->
        (match y with
           | XI q -> pdouble_plus_one_mask (pminus_mask_carry p q)
           | XO q -> pdouble_mask (pminus_mask p q)
           | XH -> IsPos (pdouble_minus_one p))
    | XH -> (match y with
               | XH -> IsNul
               | _ -> IsNeg)

(** val pminus_mask_carry : positive -> positive -> positive_mask **)

and pminus_mask_carry x y =
  match x with
    | XI p ->
        (match y with
           | XI q -> pdouble_plus_one_mask (pminus_mask_carry p q)
           | XO q -> pdouble_mask (pminus_mask p q)
           | XH -> IsPos (pdouble_minus_one p))
    | XO p ->
        (match y with
           | XI q -> pdouble_mask (pminus_mask_carry p q)
           | XO q -> pdouble_plus_one_mask (pminus_mask_carry p q)
           | XH -> pdouble_minus_two p)
    | XH -> IsNeg

(** val pminus : positive -> positive -> positive **)

let pminus x y =
  match pminus_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

(** val pmult : positive -> positive -> positive **)

let rec pmult x y =
  match x with
    | XI p -> pplus y (XO (pmult p y))
    | XO p -> XO (pmult p y)
    | XH -> y

(** val pcompare : positive -> positive -> comparison -> comparison **)

let rec pcompare x y r =
  match x with
    | XI p ->
        (match y with
           | XI q -> pcompare p q r
           | XO q -> pcompare p q Gt
           | XH -> Gt)
    | XO p ->
        (match y with
           | XI q -> pcompare p q Lt
           | XO q -> pcompare p q r
           | XH -> Gt)
    | XH -> (match y with
               | XH -> r
               | _ -> Lt)

(** val positive_eq_dec : positive -> positive -> bool **)

let rec positive_eq_dec p y0 =
  match p with
    | XI p0 ->
        (match y0 with
           | XI p1 -> positive_eq_dec p0 p1
           | _ -> false)
    | XO p0 ->
        (match y0 with
           | XO p1 -> positive_eq_dec p0 p1
           | _ -> false)
    | XH -> (match y0 with
               | XH -> true
               | _ -> false)

(** val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flip f x y =
  f y x

module type DecidableType = 
 sig 
  type t 
  
  val eq_dec : t -> t -> bool
 end

module type DecidableTypeOrig = 
 sig 
  type t 
  
  val eq_dec : t -> t -> bool
 end

module type UsualDecidableTypeOrig = 
 sig 
  type t 
  
  val eq_dec : t -> t -> bool
 end

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
    | O -> m
    | S n' -> (match m with
                 | O -> n
                 | S m' -> S (max n' m'))

type z =
  | Z0
  | Zpos of positive
  | Zneg of positive

(** val zplus : z -> z -> z **)

let zplus x y =
  match x with
    | Z0 -> y
    | Zpos x' ->
        (match y with
           | Z0 -> Zpos x'
           | Zpos y' -> Zpos (pplus x' y')
           | Zneg y' ->
               (match pcompare x' y' Eq with
                  | Eq -> Z0
                  | Lt -> Zneg (pminus y' x')
                  | Gt -> Zpos (pminus x' y')))
    | Zneg x' ->
        (match y with
           | Z0 -> Zneg x'
           | Zpos y' ->
               (match pcompare x' y' Eq with
                  | Eq -> Z0
                  | Lt -> Zpos (pminus y' x')
                  | Gt -> Zneg (pminus x' y'))
           | Zneg y' -> Zneg (pplus x' y'))

(** val zopp : z -> z **)

let zopp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

(** val zsucc : z -> z **)

let zsucc x =
  zplus x (Zpos XH)

(** val zpred : z -> z **)

let zpred x =
  zplus x (Zneg XH)

(** val zminus : z -> z -> z **)

let zminus m n =
  zplus m (zopp n)

(** val zmult : z -> z -> z **)

let zmult x y =
  match x with
    | Z0 -> Z0
    | Zpos x' ->
        (match y with
           | Z0 -> Z0
           | Zpos y' -> Zpos (pmult x' y')
           | Zneg y' -> Zneg (pmult x' y'))
    | Zneg x' ->
        (match y with
           | Z0 -> Z0
           | Zpos y' -> Zneg (pmult x' y')
           | Zneg y' -> Zpos (pmult x' y'))

(** val zcompare : z -> z -> comparison **)

let zcompare x y =
  match x with
    | Z0 -> (match y with
               | Z0 -> Eq
               | Zpos y' -> Lt
               | Zneg y' -> Gt)
    | Zpos x' -> (match y with
                    | Zpos y' -> pcompare x' y' Eq
                    | _ -> Gt)
    | Zneg x' ->
        (match y with
           | Zneg y' -> compOpp (pcompare x' y' Eq)
           | _ -> Lt)

(** val z_of_nat : nat -> z **)

let z_of_nat = function
  | O -> Z0
  | S y -> Zpos (p_of_succ_nat y)

(** val zcompare_rect :
    z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

let zcompare_rect n m h1 h2 h3 =
  let c = zcompare n m in
  (match c with
     | Eq -> h1 __
     | Lt -> h2 __
     | Gt -> h3 __)

(** val zcompare_rec :
    z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

let zcompare_rec =
  zcompare_rect

(** val z_eq_dec : z -> z -> bool **)

let z_eq_dec x y =
  match x with
    | Z0 -> (match y with
               | Z0 -> true
               | _ -> false)
    | Zpos x0 ->
        (match y with
           | Zpos p0 -> positive_eq_dec x0 p0
           | _ -> false)
    | Zneg x0 ->
        (match y with
           | Zneg p0 -> positive_eq_dec x0 p0
           | _ -> false)

(** val z_lt_dec : z -> z -> bool **)

let z_lt_dec x y =
  zcompare_rec x y (fun _ -> false) (fun _ -> true) (fun _ -> false)

(** val z_le_dec : z -> z -> bool **)

let z_le_dec x y =
  zcompare_rec x y (fun _ -> true) (fun _ -> true) (fun _ -> false)

(** val z_lt_ge_dec : z -> z -> bool **)

let z_lt_ge_dec x y =
  z_lt_dec x y

(** val z_le_gt_dec : z -> z -> bool **)

let z_le_gt_dec x y =
  z_le_dec x y

(** val zge_bool : z -> z -> bool **)

let zge_bool x y =
  match zcompare x y with
    | Lt -> false
    | _ -> true

(** val zgt_bool : z -> z -> bool **)

let zgt_bool x y =
  match zcompare x y with
    | Gt -> true
    | _ -> false

(** val bool_dec : bool -> bool -> bool **)

let bool_dec b1 b2 =
  if b1 then if b2 then true else false else if b2 then false else true

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
  | [] -> false
  | y::l1 -> let s = h y a in if s then true else in_dec h a l1

(** val nth_error : 'a1 list -> nat -> 'a1 exc **)

let rec nth_error l0 = function
  | O -> (match l0 with
            | [] -> error
            | x::l1 -> value x)
  | S n0 -> (match l0 with
               | [] -> error
               | a::l1 -> nth_error l1 n0)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
  | [] -> []
  | x::l' -> app (rev l') (x::[])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
  | [] -> []
  | a::t0 -> (f a)::(map f t0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l0 a0 =
  match l0 with
    | [] -> a0
    | b::t0 -> fold_left f t0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
  | [] -> a0
  | b::t0 -> f b (fold_right f a0 t0)

(** val iter_pos : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter_pos n f x =
  match n with
    | XI n' -> f (iter_pos n' f (iter_pos n' f x))
    | XO n' -> iter_pos n' f (iter_pos n' f x)
    | XH -> f x

(** val natlike_rec2 : 'a1 -> (z -> __ -> 'a1 -> 'a1) -> z -> 'a1 **)

let rec natlike_rec2 x x0 = function
  | Z0 -> x
  | Zpos p -> x0 (zpred (Zpos p)) __ (natlike_rec2 x x0 (zpred (Zpos p)))
  | Zneg p -> assert false (* absurd case *)

type 'a set = 'a list

(** val empty_set : 'a1 set **)

let empty_set =
  []

(** val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
  | [] -> a::[]
  | a1::x1 -> if aeq_dec a a1 then a1::x1 else a1::(set_add aeq_dec a x1)

(** val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool **)

let rec set_mem aeq_dec a = function
  | [] -> false
  | a1::x1 -> if aeq_dec a a1 then true else set_mem aeq_dec a x1

(** val set_inter : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_inter aeq_dec x y =
  match x with
    | [] -> []
    | a1::x1 ->
        if set_mem aeq_dec a1 y
        then a1::(set_inter aeq_dec x1 y)
        else set_inter aeq_dec x1 y

(** val set_union : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_union aeq_dec x = function
  | [] -> x
  | a1::y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)

(** val shift_nat : nat -> positive -> positive **)

let shift_nat n z0 =
  iter_nat n (fun x -> XO x) z0

(** val shift_pos : positive -> positive -> positive **)

let shift_pos n z0 =
  iter_pos n (fun x -> XO x) z0

(** val two_power_nat : nat -> z **)

let two_power_nat n =
  Zpos (shift_nat n XH)

(** val two_power_pos : positive -> z **)

let two_power_pos x =
  Zpos (shift_pos x XH)

(** val two_p : z -> z **)

let two_p = function
  | Z0 -> Zpos XH
  | Zpos y -> two_power_pos y
  | Zneg y -> Z0

(** val zdiv_eucl_POS : positive -> z -> z*z **)

let rec zdiv_eucl_POS a b =
  match a with
    | XI a' ->
        let q,r = zdiv_eucl_POS a' b in
        let r' = zplus (zmult (Zpos (XO XH)) r) (Zpos XH) in
        if zgt_bool b r'
        then (zmult (Zpos (XO XH)) q),r'
        else (zplus (zmult (Zpos (XO XH)) q) (Zpos XH)),(zminus r' b)
    | XO a' ->
        let q,r = zdiv_eucl_POS a' b in
        let r' = zmult (Zpos (XO XH)) r in
        if zgt_bool b r'
        then (zmult (Zpos (XO XH)) q),r'
        else (zplus (zmult (Zpos (XO XH)) q) (Zpos XH)),(zminus r' b)
    | XH -> if zge_bool b (Zpos (XO XH)) then Z0,(Zpos XH) else (Zpos XH),Z0

(** val zdiv_eucl : z -> z -> z*z **)

let zdiv_eucl a b =
  match a with
    | Z0 -> Z0,Z0
    | Zpos a' ->
        (match b with
           | Z0 -> Z0,Z0
           | Zpos p -> zdiv_eucl_POS a' b
           | Zneg b' ->
               let q,r = zdiv_eucl_POS a' (Zpos b') in
               (match r with
                  | Z0 -> (zopp q),Z0
                  | _ -> (zopp (zplus q (Zpos XH))),(zplus b r)))
    | Zneg a' ->
        (match b with
           | Z0 -> Z0,Z0
           | Zpos p ->
               let q,r = zdiv_eucl_POS a' b in
               (match r with
                  | Z0 -> (zopp q),Z0
                  | _ -> (zopp (zplus q (Zpos XH))),(zminus b r))
           | Zneg b' -> let q,r = zdiv_eucl_POS a' (Zpos b') in q,(zopp r))

(** val zdiv : z -> z -> z **)

let zdiv a b =
  let q,x = zdiv_eucl a b in q

(** val zmod : z -> z -> z **)

let zmod a b =
  let x,r = zdiv_eucl a b in r

module type Coq_DecidableType = 
 DecidableTypeOrig

module type UsualDecidableType = 
 UsualDecidableTypeOrig

module WFacts_fun = 
 functor (E:Coq_DecidableType) ->
 functor (M:sig 
  type elt = E.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> bool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> t*t
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
 end) ->
 struct 
  (** val eqb : E.t -> E.t -> bool **)
  
  let eqb x y =
    if E.eq_dec x y then true else false
 end

module WDecide_fun = 
 functor (E:Coq_DecidableType) ->
 functor (M:sig 
  type elt = E.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> bool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> t*t
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
 end) ->
 struct 
  module F = WFacts_fun(E)(M)
  
  module FSetLogicalFacts = 
   struct 
    
   end
  
  module FSetDecideAuxiliary = 
   struct 
    
   end
  
  module FSetDecideTestCases = 
   struct 
    
   end
 end

module WProperties_fun = 
 functor (E:Coq_DecidableType) ->
 functor (M:sig 
  type elt = E.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> bool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> t*t
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
 end) ->
 struct 
  module Dec = WDecide_fun(E)(M)
  
  module FM = Dec.F
  
  (** val coq_In_dec : M.elt -> M.t -> bool **)
  
  let coq_In_dec x s =
    if M.mem x s then true else false
  
  (** val of_list : M.elt list -> M.t **)
  
  let of_list l0 =
    fold_right M.add M.empty l0
  
  (** val to_list : M.t -> M.elt list **)
  
  let to_list =
    M.elements
  
  (** val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
      'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2 **)
  
  let fold_rec f i0 s pempty pstep =
    let l0 = rev (M.elements s) in
    let pstep' = fun x a s' s'' x0 -> pstep x a s' s'' __ __ __ x0 in
    let rec f0 l1 pstep'0 s0 =
      match l1 with
        | [] -> pempty s0 __
        | y::l2 ->
            pstep'0 y (fold_right f i0 l2) (of_list l2) s0 __ __ __
              (f0 l2 (fun x a0 s' s'' _ _ _ x0 ->
                pstep'0 x a0 s' s'' __ __ __ x0) (of_list l2))
    in f0 l0 (fun x a s' s'' _ _ _ x0 -> pstep' x a s' s'' x0) s
  
  (** val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2
      -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) ->
      'a2 **)
  
  let fold_rec_bis f i0 s pmorphism pempty pstep =
    fold_rec f i0 s (fun s' _ -> pmorphism M.empty s' i0 __ pempty)
      (fun x a s' s'' _ _ _ x0 ->
      pmorphism (M.add x s') s'' (f x a) __ (pstep x a s' __ __ x0))
  
  (** val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2 **)
  
  let fold_rec_nodep f i0 s x x0 =
    fold_rec_bis f i0 s (fun s0 s' a _ x1 -> x1) x (fun x1 a s' _ _ x2 ->
      x0 x1 a __ x2)
  
  (** val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
      -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2 **)
  
  let fold_rec_weak f i0 x x0 x1 s =
    fold_rec_bis f i0 s x x0 (fun x2 a s' _ _ x3 -> x1 x2 a s' __ x3)
  
  (** val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
      'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 **)
  
  let fold_rel f g i0 j s rempty rstep =
    let l0 = rev (M.elements s) in
    let rstep' = fun x a b x0 -> rstep x a b __ x0 in
    let rec f0 l1 rstep'0 =
      match l1 with
        | [] -> rempty
        | y::l2 ->
            rstep'0 y (fold_right f i0 l2) (fold_right g j l2) __
              (f0 l2 (fun x a0 b _ x0 -> rstep'0 x a0 b __ x0))
    in f0 l0 (fun x a b _ x0 -> rstep' x a b x0)
  
  (** val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
      -> M.t -> 'a1 **)
  
  let set_induction x x0 s =
    fold_rec (fun x1 x2 -> Tt) Tt s x (fun x1 a s' s'' _ _ _ x2 ->
      x0 s' s'' x2 x1 __ __)
  
  (** val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1
      -> 'a1) -> M.t -> 'a1 **)
  
  let set_induction_bis x x0 x1 s =
    fold_rec_bis (fun x2 x3 -> Tt) Tt s (fun s0 s' a _ x2 -> 
      x s0 s' __ x2) x0 (fun x2 a s' _ _ x3 -> x1 x2 s' __ x3)
  
  (** val cardinal_inv_2 : M.t -> nat -> M.elt **)
  
  let cardinal_inv_2 s n =
    let l0 = M.elements s in
    (match l0 with
       | [] -> assert false (* absurd case *)
       | e::l1 -> e)
  
  (** val cardinal_inv_2b : M.t -> M.elt **)
  
  let cardinal_inv_2b s =
    let x = cardinal_inv_2 s in
    (match M.cardinal s with
       | O -> assert false (* absurd case *)
       | S n -> x n)
 end

module MakeRaw = 
 functor (X:DecidableType) ->
 struct 
  type elt = X.t
  
  type t = elt list
  
  (** val empty : t **)
  
  let empty =
    []
  
  (** val is_empty : t -> bool **)
  
  let is_empty = function
    | [] -> true
    | x::x0 -> false
  
  (** val mem : elt -> t -> bool **)
  
  let rec mem x = function
    | [] -> false
    | y::l0 -> if X.eq_dec x y then true else mem x l0
  
  (** val add : elt -> t -> t **)
  
  let rec add x s = match s with
    | [] -> x::[]
    | y::l0 -> if X.eq_dec x y then s else y::(add x l0)
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    x::[]
  
  (** val remove : elt -> t -> t **)
  
  let rec remove x = function
    | [] -> []
    | y::l0 -> if X.eq_dec x y then l0 else y::(remove x l0)
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold f s i0 =
    fold_left (flip f) s i0
  
  (** val union : t -> t -> t **)
  
  let union s =
    fold add s
  
  (** val diff : t -> t -> t **)
  
  let diff s s' =
    fold remove s' s
  
  (** val inter : t -> t -> t **)
  
  let inter s s' =
    fold (fun x s0 -> if mem x s' then add x s0 else s0) s []
  
  (** val subset : t -> t -> bool **)
  
  let subset s s' =
    is_empty (diff s s')
  
  (** val equal : t -> t -> bool **)
  
  let equal s s' =
    if subset s s' then subset s' s else false
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let rec filter f = function
    | [] -> []
    | x::l0 -> if f x then x::(filter f l0) else filter f l0
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let rec for_all f = function
    | [] -> true
    | x::l0 -> if f x then for_all f l0 else false
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let rec exists_ f = function
    | [] -> false
    | x::l0 -> if f x then true else exists_ f l0
  
  (** val partition : (elt -> bool) -> t -> t*t **)
  
  let rec partition f = function
    | [] -> [],[]
    | x::l0 ->
        let s1,s2 = partition f l0 in if f x then (x::s1),s2 else s1,(x::s2)
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    length s
  
  (** val elements : t -> elt list **)
  
  let elements s =
    s
  
  (** val choose : t -> elt option **)
  
  let choose = function
    | [] -> None
    | x::l0 -> Some x
  
  (** val isok : elt list -> bool **)
  
  let rec isok = function
    | [] -> true
    | a::l1 -> if negb (mem a l1) then isok l1 else false
 end

module Make = 
 functor (X:DecidableType) ->
 struct 
  module Raw = MakeRaw(X)
  
  module E = 
   struct 
    type t = X.t
    
    (** val eq_dec : t -> t -> bool **)
    
    let eq_dec =
      X.eq_dec
   end
  
  type elt = X.t
  
  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)
  
  (** val this : t_ -> Raw.t **)
  
  let this t0 =
    t0
  
  type t = t_
  
  (** val mem : elt -> t -> bool **)
  
  let mem x s =
    Raw.mem x (this s)
  
  (** val add : elt -> t -> t **)
  
  let add x s =
    Raw.add x (this s)
  
  (** val remove : elt -> t -> t **)
  
  let remove x s =
    Raw.remove x (this s)
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    Raw.singleton x
  
  (** val union : t -> t -> t **)
  
  let union s s' =
    Raw.union (this s) (this s')
  
  (** val inter : t -> t -> t **)
  
  let inter s s' =
    Raw.inter (this s) (this s')
  
  (** val diff : t -> t -> t **)
  
  let diff s s' =
    Raw.diff (this s) (this s')
  
  (** val equal : t -> t -> bool **)
  
  let equal s s' =
    Raw.equal (this s) (this s')
  
  (** val subset : t -> t -> bool **)
  
  let subset s s' =
    Raw.subset (this s) (this s')
  
  (** val empty : t **)
  
  let empty =
    Raw.empty
  
  (** val is_empty : t -> bool **)
  
  let is_empty s =
    Raw.is_empty (this s)
  
  (** val elements : t -> elt list **)
  
  let elements s =
    Raw.elements (this s)
  
  (** val choose : t -> elt option **)
  
  let choose s =
    Raw.choose (this s)
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold f s =
    Raw.fold f (this s)
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    Raw.cardinal (this s)
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let filter f s =
    Raw.filter f (this s)
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let for_all f s =
    Raw.for_all f (this s)
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let exists_ f s =
    Raw.exists_ f (this s)
  
  (** val partition : (elt -> bool) -> t -> t*t **)
  
  let partition f s =
    let p = Raw.partition f (this s) in (fst p),(snd p)
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec s s' =
    let b = Raw.equal s s' in if b then true else false
 end

module Coq_WDecide_fun = 
 functor (E:Coq_DecidableType) ->
 functor (M:sig 
  type elt = E.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> bool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> t*t
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
 end) ->
 struct 
  module F = WFacts_fun(E)(M)
  
  module FSetLogicalFacts = 
   struct 
    
   end
  
  module FSetDecideAuxiliary = 
   struct 
    
   end
  
  module FSetDecideTestCases = 
   struct 
    
   end
 end

type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
  | EmptyString
  | String of ascii * string

module Coq_Make = 
 functor (X:UsualDecidableType) ->
 functor (KeySet:sig 
  type elt = X.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> bool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> t*t
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
 end) ->
 struct 
  module D = Coq_WDecide_fun(X)(KeySet)
  
  module KeySetProperties = WProperties_fun(X)(KeySet)
  
  module KeySetFacts = WFacts_fun(X)(KeySet)
  
  (** val one : 'a1 -> 'a1 list **)
  
  let one item =
    item::[]
  
  (** val dom : (X.t*'a1) list -> KeySet.t **)
  
  let rec dom = function
    | [] -> KeySet.empty
    | p::e' -> let x,y = p in KeySet.add x (dom e')
  
  (** val get : X.t -> (X.t*'a1) list -> 'a1 option **)
  
  let rec get x = function
    | [] -> None
    | p::f -> let y,c = p in if X.eq_dec x y then Some c else get x f
  
  (** val map : ('a1 -> 'a2) -> (X.t*'a1) list -> (X.t*'a2) list **)
  
  let map f e =
    map (fun b -> let x,a = b in x,(f a)) e
  
  (** val alist_ind :
      'a2 -> (X.t -> 'a1 -> (X.t*'a1) list -> 'a2 -> 'a2) -> (X.t*'a1) list
      -> 'a2 **)
  
  let rec alist_ind x x0 = function
    | [] -> x
    | y::l0 ->
        let iHxs = alist_ind x x0 l0 in let x1,a = y in x0 x1 a l0 iHxs
  
  (** val binds_dec :
      X.t -> 'a1 -> (X.t*'a1) list -> ('a1 -> 'a1 -> bool) -> bool **)
  
  let binds_dec x a e x0 =
    in_dec (fun x1 y ->
      let x2,x3 = x1 in
      let t0,a1 = y in if X.eq_dec x2 t0 then x0 x3 a1 else false) (x,a) e
  
  (** val binds_lookup : X.t -> (X.t*'a1) list -> ('a1, __) sum **)
  
  let binds_lookup x e =
    alist_ind (Inr __) (fun x1 a1 l0 x0 ->
      match x0 with
        | Inl s -> Inl s
        | Inr _ -> let s = X.eq_dec x x1 in if s then Inl a1 else Inr __) e
 end

type 'a eqDec = 'a -> 'a -> bool

type 'a eqDec_eq = 'a -> 'a -> bool

(** val eq_dec0 : 'a1 eqDec_eq -> 'a1 -> 'a1 -> bool **)

let eq_dec0 eqDec_eq0 =
  eqDec_eq0

(** val eqDec_eq_of_EqDec : 'a1 eqDec -> 'a1 eqDec_eq **)

let eqDec_eq_of_EqDec h =
  h

module Coq0_Make = 
 functor (X:Coq_DecidableType) ->
 struct 
  module E = 
   struct 
    type t = X.t
    
    (** val eq_dec : t -> t -> bool **)
    
    let eq_dec =
      X.eq_dec
   end
  
  module X' = 
   struct 
    type t = X.t
    
    (** val eq_dec : t -> t -> bool **)
    
    let eq_dec =
      X.eq_dec
   end
  
  module MSet = Make(X')
  
  type elt = X.t
  
  type t = MSet.t
  
  (** val empty : t **)
  
  let empty =
    MSet.empty
  
  (** val is_empty : t -> bool **)
  
  let is_empty =
    MSet.is_empty
  
  (** val mem : elt -> t -> bool **)
  
  let mem =
    MSet.mem
  
  (** val add : elt -> t -> t **)
  
  let add =
    MSet.add
  
  (** val singleton : elt -> t **)
  
  let singleton =
    MSet.singleton
  
  (** val remove : elt -> t -> t **)
  
  let remove =
    MSet.remove
  
  (** val union : t -> t -> t **)
  
  let union =
    MSet.union
  
  (** val inter : t -> t -> t **)
  
  let inter =
    MSet.inter
  
  (** val diff : t -> t -> t **)
  
  let diff =
    MSet.diff
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec =
    MSet.eq_dec
  
  (** val equal : t -> t -> bool **)
  
  let equal =
    MSet.equal
  
  (** val subset : t -> t -> bool **)
  
  let subset =
    MSet.subset
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold x x0 x1 =
    MSet.fold x x0 x1
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let for_all =
    MSet.for_all
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let exists_ =
    MSet.exists_
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let filter =
    MSet.filter
  
  (** val partition : (elt -> bool) -> t -> t*t **)
  
  let partition =
    MSet.partition
  
  (** val cardinal : t -> nat **)
  
  let cardinal =
    MSet.cardinal
  
  (** val elements : t -> elt list **)
  
  let elements =
    MSet.elements
  
  (** val choose : t -> elt option **)
  
  let choose =
    MSet.choose
  
  module MF = 
   struct 
    (** val eqb : X.t -> X.t -> bool **)
    
    let eqb x y =
      if MSet.E.eq_dec x y then true else false
   end
 end

module type ATOM = 
 sig 
  type atom 
  
  val eq_atom_dec : atom -> atom -> bool
  
  val atom_fresh_for_list : atom list -> atom
 end

module AtomImpl = 
 struct 
  type atom = String.t
  
  (** val eq_atom_dec : atom -> atom -> bool **)
  
  let eq_atom_dec = fun a b -> a == b
  
  (** val nat_list_max : nat list -> nat **)
  
  let rec nat_list_max = function
    | [] -> O
    | y::l1 -> max y (nat_list_max l1)
  
  (** val atom_fresh_for_list : atom list -> atom **)
  
  let atom_fresh_for_list = Symexe_aux.atom_fresh_for_list
 end

module AtomDT = 
 struct 
  type t = AtomImpl.atom
  
  (** val eq_dec : AtomImpl.atom -> AtomImpl.atom -> bool **)
  
  let eq_dec =
    AtomImpl.eq_atom_dec
 end

(** val eqDec_atom : AtomImpl.atom eqDec **)

let eqDec_atom =
  AtomImpl.eq_atom_dec

module AtomSetImpl = Coq0_Make(AtomDT)

module EnvImpl = Coq_Make(AtomDT)(AtomSetImpl)

type 'x assocList = (AtomImpl.atom*'x) list

(** val updateAddAL :
    'a1 assocList -> AtomImpl.atom -> 'a1 -> 'a1 assocList **)

let rec updateAddAL m i0 gv =
  match m with
    | [] -> (i0,gv)::[]
    | p::m' ->
        let i',gv' = p in
        if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) i0 i'
        then (i',gv)::m'
        else (i',gv')::(updateAddAL m' i0 gv)

(** val updateAL : 'a1 assocList -> AtomImpl.atom -> 'a1 -> 'a1 assocList **)

let rec updateAL m i0 gv =
  match m with
    | [] -> []
    | p::m' ->
        let i',gv' = p in
        if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) i0 i'
        then (i',gv)::m'
        else (i',gv')::(updateAL m' i0 gv)

(** val lookupAL : 'a1 assocList -> AtomImpl.atom -> 'a1 option **)

let rec lookupAL m i0 =
  match m with
    | [] -> None
    | p::m' ->
        let i',gv' = p in
        if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) i0 i'
        then Some gv'
        else lookupAL m' i0

(** val zeq : z -> z -> bool **)

let zeq =
  z_eq_dec

(** val zlt : z -> z -> bool **)

let zlt =
  z_lt_ge_dec

(** val zle : z -> z -> bool **)

let zle =
  z_le_gt_dec

(** val zdivide_dec : z -> z -> bool **)

let zdivide_dec p q =
  zeq (zmod q p) Z0

(** val nat_of_Z : z -> nat **)

let nat_of_Z = function
  | Zpos p -> nat_of_P p
  | _ -> O

(** val zRdiv : z -> z -> z **)

let zRdiv a b =
  if zeq (zmod a b) Z0 then zdiv a b else zplus (zdiv a b) (Zpos XH)

(** val list_repeat : nat -> 'a1 -> 'a1 list **)

let rec list_repeat n x =
  match n with
    | O -> []
    | S m -> x::(list_repeat m x)

(** val proj_sumbool : bool -> bool **)

let proj_sumbool = function
  | true -> true
  | false -> false

type comparison0 =
  | Ceq
  | Cne
  | Clt
  | Cle
  | Cgt
  | Cge

module Int = 
 struct 
  (** val wordsize : nat -> nat **)
  
  let wordsize wordsize_one =
    S wordsize_one
  
  (** val modulus : nat -> z **)
  
  let modulus wordsize_one =
    two_power_nat (wordsize wordsize_one)
  
  (** val half_modulus : nat -> z **)
  
  let half_modulus wordsize_one =
    zdiv (modulus wordsize_one) (Zpos (XO XH))
  
  (** val max_unsigned : nat -> z **)
  
  let max_unsigned wordsize_one =
    zminus (modulus wordsize_one) (Zpos XH)
  
  (** val max_signed : nat -> z **)
  
  let max_signed wordsize_one =
    zminus (half_modulus wordsize_one) (Zpos XH)
  
  (** val min_signed : nat -> z **)
  
  let min_signed wordsize_one =
    zopp (half_modulus wordsize_one)
  
  type int = z
    (* singleton inductive, whose constructor was mkint *)
  
  (** val int_rect : nat -> (z -> __ -> 'a1) -> int -> 'a1 **)
  
  let int_rect wordsize_one f i0 =
    f i0 __
  
  (** val int_rec : nat -> (z -> __ -> 'a1) -> int -> 'a1 **)
  
  let int_rec wordsize_one f i0 =
    f i0 __
  
  (** val intval : nat -> int -> z **)
  
  let intval wordsize_one i0 =
    i0
  
  (** val unsigned : nat -> int -> z **)
  
  let unsigned wordsize_one n =
    intval wordsize_one n
  
  (** val signed : nat -> int -> z **)
  
  let signed wordsize_one n =
    if zlt (unsigned wordsize_one n) (half_modulus wordsize_one)
    then unsigned wordsize_one n
    else zminus (unsigned wordsize_one n) (modulus wordsize_one)
  
  (** val repr : nat -> z -> int **)
  
  let repr wordsize_one x =
    zmod x (modulus wordsize_one)
  
  (** val zero : nat -> int **)
  
  let zero wordsize_one =
    repr wordsize_one Z0
  
  (** val one : nat -> int **)
  
  let one wordsize_one =
    repr wordsize_one (Zpos XH)
  
  (** val mone : nat -> int **)
  
  let mone wordsize_one =
    repr wordsize_one (Zneg XH)
  
  (** val iwordsize : nat -> int **)
  
  let iwordsize wordsize_one =
    repr wordsize_one (z_of_nat (wordsize wordsize_one))
  
  (** val eq_dec : nat -> int -> int -> bool **)
  
  let eq_dec wordsize_one x y =
    zeq x y
  
  (** val eq : nat -> int -> int -> bool **)
  
  let eq wordsize_one x y =
    if zeq (unsigned wordsize_one x) (unsigned wordsize_one y)
    then true
    else false
  
  (** val lt : nat -> int -> int -> bool **)
  
  let lt wordsize_one x y =
    if zlt (signed wordsize_one x) (signed wordsize_one y)
    then true
    else false
  
  (** val ltu : nat -> int -> int -> bool **)
  
  let ltu wordsize_one x y =
    if zlt (unsigned wordsize_one x) (unsigned wordsize_one y)
    then true
    else false
  
  (** val neg : nat -> int -> int **)
  
  let neg wordsize_one x =
    repr wordsize_one (zopp (unsigned wordsize_one x))
  
  (** val add : nat -> int -> int -> int **)
  
  let add wordsize_one x y =
    repr wordsize_one
      (zplus (unsigned wordsize_one x) (unsigned wordsize_one y))
  
  (** val sub : nat -> int -> int -> int **)
  
  let sub wordsize_one x y =
    repr wordsize_one
      (zminus (unsigned wordsize_one x) (unsigned wordsize_one y))
  
  (** val mul : nat -> int -> int -> int **)
  
  let mul wordsize_one x y =
    repr wordsize_one
      (zmult (unsigned wordsize_one x) (unsigned wordsize_one y))
  
  (** val coq_Zdiv_round : z -> z -> z **)
  
  let coq_Zdiv_round x y =
    if zlt x Z0
    then if zlt y Z0 then zdiv (zopp x) (zopp y) else zopp (zdiv (zopp x) y)
    else if zlt y Z0 then zopp (zdiv x (zopp y)) else zdiv x y
  
  (** val coq_Zmod_round : z -> z -> z **)
  
  let coq_Zmod_round x y =
    zminus x (zmult (coq_Zdiv_round x y) y)
  
  (** val divs : nat -> int -> int -> int **)
  
  let divs wordsize_one x y =
    repr wordsize_one
      (coq_Zdiv_round (signed wordsize_one x) (signed wordsize_one y))
  
  (** val mods : nat -> int -> int -> int **)
  
  let mods wordsize_one x y =
    repr wordsize_one
      (coq_Zmod_round (signed wordsize_one x) (signed wordsize_one y))
  
  (** val divu : nat -> int -> int -> int **)
  
  let divu wordsize_one x y =
    repr wordsize_one
      (zdiv (unsigned wordsize_one x) (unsigned wordsize_one y))
  
  (** val modu : nat -> int -> int -> int **)
  
  let modu wordsize_one x y =
    repr wordsize_one
      (zmod (unsigned wordsize_one x) (unsigned wordsize_one y))
  
  (** val coq_Z_shift_add : bool -> z -> z **)
  
  let coq_Z_shift_add b x =
    if b
    then zplus (zmult (Zpos (XO XH)) x) (Zpos XH)
    else zmult (Zpos (XO XH)) x
  
  (** val coq_Z_bin_decomp : z -> bool*z **)
  
  let coq_Z_bin_decomp = function
    | Z0 -> false,Z0
    | Zpos p ->
        (match p with
           | XI q -> true,(Zpos q)
           | XO q -> false,(Zpos q)
           | XH -> true,Z0)
    | Zneg p ->
        (match p with
           | XI q -> true,(zminus (Zneg q) (Zpos XH))
           | XO q -> false,(Zneg q)
           | XH -> true,(Zneg XH))
  
  (** val bits_of_Z : nat -> z -> z -> bool **)
  
  let rec bits_of_Z n x =
    match n with
      | O -> (fun i0 -> false)
      | S m ->
          let b,y = coq_Z_bin_decomp x in
          let f = bits_of_Z m y in
          (fun i0 -> if zeq i0 Z0 then b else f (zminus i0 (Zpos XH)))
  
  (** val coq_Z_of_bits : nat -> (z -> bool) -> z -> z **)
  
  let rec coq_Z_of_bits n f i0 =
    match n with
      | O -> Z0
      | S m -> coq_Z_shift_add (f i0) (coq_Z_of_bits m f (zsucc i0))
  
  (** val bitwise_binop :
      nat -> (bool -> bool -> bool) -> int -> int -> int **)
  
  let bitwise_binop wordsize_one f x y =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    let fy = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one y) in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) (fun i0 -> 
        f (fx i0) (fy i0)) Z0)
  
  (** val coq_and : nat -> int -> int -> int **)
  
  let coq_and wordsize_one x y =
    bitwise_binop wordsize_one (fun b1 b2 -> if b1 then b2 else false) x y
  
  (** val coq_or : nat -> int -> int -> int **)
  
  let coq_or wordsize_one x y =
    bitwise_binop wordsize_one (fun b1 b2 -> if b1 then true else b2) x y
  
  (** val xor : nat -> int -> int -> int **)
  
  let xor wordsize_one x y =
    bitwise_binop wordsize_one xorb x y
  
  (** val not : nat -> int -> int **)
  
  let not wordsize_one x =
    xor wordsize_one x (mone wordsize_one)
  
  (** val shl : nat -> int -> int -> int **)
  
  let shl wordsize_one x y =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) fx
        (zopp (unsigned wordsize_one y)))
  
  (** val shru : nat -> int -> int -> int **)
  
  let shru wordsize_one x y =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) fx (unsigned wordsize_one y))
  
  (** val shr : nat -> int -> int -> int **)
  
  let shr wordsize_one x y =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    let sx = fun i0 ->
      fx
        (if zlt i0 (z_of_nat (wordsize wordsize_one))
         then i0
         else zminus (z_of_nat (wordsize wordsize_one)) (Zpos XH))
    in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) sx (unsigned wordsize_one y))
  
  (** val shrx : nat -> int -> int -> int **)
  
  let shrx wordsize_one x y =
    divs wordsize_one x (shl wordsize_one (one wordsize_one) y)
  
  (** val shr_carry : nat -> int -> int -> int **)
  
  let shr_carry wordsize_one x y =
    sub wordsize_one (shrx wordsize_one x y) (shr wordsize_one x y)
  
  (** val rol : nat -> int -> int -> int **)
  
  let rol wordsize_one x y =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    let rx = fun i0 -> fx (zmod i0 (z_of_nat (wordsize wordsize_one))) in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) rx
        (zopp (unsigned wordsize_one y)))
  
  (** val ror : nat -> int -> int -> int **)
  
  let ror wordsize_one x y =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    let rx = fun i0 -> fx (zmod i0 (z_of_nat (wordsize wordsize_one))) in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) rx (unsigned wordsize_one y))
  
  (** val rolm : nat -> int -> int -> int -> int **)
  
  let rolm wordsize_one x a m =
    coq_and wordsize_one (rol wordsize_one x a) m
  
  (** val zero_ext : nat -> z -> int -> int **)
  
  let zero_ext wordsize_one n x =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) (fun i0 ->
        if zlt i0 n then fx i0 else false) Z0)
  
  (** val sign_ext : nat -> z -> int -> int **)
  
  let sign_ext wordsize_one n x =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) (fun i0 ->
        if zlt i0 n then fx i0 else fx (zminus n (Zpos XH))) Z0)
  
  (** val coq_Z_one_bits : nat -> z -> z -> z list **)
  
  let rec coq_Z_one_bits n x i0 =
    match n with
      | O -> []
      | S m ->
          let b,y = coq_Z_bin_decomp x in
          if b
          then i0::(coq_Z_one_bits m y (zplus i0 (Zpos XH)))
          else coq_Z_one_bits m y (zplus i0 (Zpos XH))
  
  (** val one_bits : nat -> int -> int list **)
  
  let one_bits wordsize_one x =
    map (repr wordsize_one)
      (coq_Z_one_bits (wordsize wordsize_one) (unsigned wordsize_one x) Z0)
  
  (** val is_power2 : nat -> int -> int option **)
  
  let is_power2 wordsize_one x =
    match coq_Z_one_bits (wordsize wordsize_one) (unsigned wordsize_one x) Z0 with
      | [] -> None
      | i0::l0 ->
          (match l0 with
             | [] -> Some (repr wordsize_one i0)
             | z0::l1 -> None)
  
  (** val cmp : nat -> comparison0 -> int -> int -> bool **)
  
  let cmp wordsize_one c x y =
    match c with
      | Ceq -> eq wordsize_one x y
      | Cne -> negb (eq wordsize_one x y)
      | Clt -> lt wordsize_one x y
      | Cle -> negb (lt wordsize_one y x)
      | Cgt -> lt wordsize_one y x
      | Cge -> negb (lt wordsize_one x y)
  
  (** val cmpu : nat -> comparison0 -> int -> int -> bool **)
  
  let cmpu wordsize_one c x y =
    match c with
      | Ceq -> eq wordsize_one x y
      | Cne -> negb (eq wordsize_one x y)
      | Clt -> ltu wordsize_one x y
      | Cle -> negb (ltu wordsize_one y x)
      | Cgt -> ltu wordsize_one y x
      | Cge -> negb (ltu wordsize_one x y)
  
  (** val notbool : nat -> int -> int **)
  
  let notbool wordsize_one x =
    if eq wordsize_one x (zero wordsize_one)
    then one wordsize_one
    else zero wordsize_one
  
  (** val powerserie : z list -> z **)
  
  let rec powerserie = function
    | [] -> Z0
    | x::xs -> zplus (two_p x) (powerserie xs)
  
  (** val int_of_one_bits : nat -> int list -> int **)
  
  let rec int_of_one_bits wordsize_one = function
    | [] -> zero wordsize_one
    | a::b ->
        add wordsize_one (shl wordsize_one (one wordsize_one) a)
          (int_of_one_bits wordsize_one b)
 end

module LLVMsyntax = 
 struct 
  (** val last_opt : 'a1 list -> 'a1 option **)
  
  let rec last_opt = function
    | [] -> None
    | a::l' -> (match l' with
                  | [] -> Some a
                  | a0::l1 -> last_opt l')
  
  type coq_INT = Llvm.llapint
  
  type sz = int
  
  type id = String.t
  
  type l = String.t
  
  type align = int
  
  type i = nat
  
  type typ =
    | Coq_typ_int of sz
    | Coq_typ_float
    | Coq_typ_double
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
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 ->
      'a1) -> (typ -> 'a1 -> list_typ -> 'a1) -> (list_typ -> 'a1) -> (typ ->
      'a1 -> 'a1) -> typ -> 'a1 **)
  
  let rec typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
    | Coq_typ_int s -> f s
    | Coq_typ_float -> f0
    | Coq_typ_double -> f1
    | Coq_typ_void -> f2
    | Coq_typ_label -> f3
    | Coq_typ_metadata -> f4
    | Coq_typ_array (s, t1) ->
        f5 s t1 (typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 t1)
    | Coq_typ_function (t1, l0) ->
        f6 t1 (typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 t1) l0
    | Coq_typ_struct l0 -> f7 l0
    | Coq_typ_pointer t1 -> f8 t1 (typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 t1)
  
  (** val typ_rec :
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 ->
      'a1) -> (typ -> 'a1 -> list_typ -> 'a1) -> (list_typ -> 'a1) -> (typ ->
      'a1 -> 'a1) -> typ -> 'a1 **)
  
  let rec typ_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
    | Coq_typ_int s -> f s
    | Coq_typ_float -> f0
    | Coq_typ_double -> f1
    | Coq_typ_void -> f2
    | Coq_typ_label -> f3
    | Coq_typ_metadata -> f4
    | Coq_typ_array (s, t1) ->
        f5 s t1 (typ_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 t1)
    | Coq_typ_function (t1, l0) ->
        f6 t1 (typ_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 t1) l0
    | Coq_typ_struct l0 -> f7 l0
    | Coq_typ_pointer t1 -> f8 t1 (typ_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 t1)
  
  (** val list_typ_rect :
      'a1 -> (typ -> list_typ -> 'a1 -> 'a1) -> list_typ -> 'a1 **)
  
  let rec list_typ_rect f f0 = function
    | Nil_list_typ -> f
    | Cons_list_typ (t0, l1) -> f0 t0 l1 (list_typ_rect f f0 l1)
  
  (** val list_typ_rec :
      'a1 -> (typ -> list_typ -> 'a1 -> 'a1) -> list_typ -> 'a1 **)
  
  let rec list_typ_rec f f0 = function
    | Nil_list_typ -> f
    | Cons_list_typ (t0, l1) -> f0 t0 l1 (list_typ_rec f f0 l1)
  
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
  
  type param = typ*value
  
  type params = (typ*value) list
  
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
  
  type list_value_l =
    | Nil_list_value_l
    | Cons_list_value_l of value * l * list_value_l
  
  (** val list_value_l_rect :
      'a1 -> (value -> l -> list_value_l -> 'a1 -> 'a1) -> list_value_l ->
      'a1 **)
  
  let rec list_value_l_rect f f0 = function
    | Nil_list_value_l -> f
    | Cons_list_value_l (v, l1, l2) -> f0 v l1 l2 (list_value_l_rect f f0 l2)
  
  (** val list_value_l_rec :
      'a1 -> (value -> l -> list_value_l -> 'a1 -> 'a1) -> list_value_l ->
      'a1 **)
  
  let rec list_value_l_rec f f0 = function
    | Nil_list_value_l -> f
    | Cons_list_value_l (v, l1, l2) -> f0 v l1 l2 (list_value_l_rec f f0 l2)
  
  type cmd =
    | Coq_insn_bop of id * bop * sz * value * value
    | Coq_insn_extractvalue of id * typ * value * list_const
    | Coq_insn_insertvalue of id * typ * value * typ * value * list_const
    | Coq_insn_malloc of id * typ * sz * align
    | Coq_insn_free of id * typ * value
    | Coq_insn_alloca of id * typ * sz * align
    | Coq_insn_load of id * typ * value * align
    | Coq_insn_store of id * typ * value * value * align
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
      align -> 'a1) -> (id -> typ -> value -> value -> align -> 'a1) -> (id
      -> inbounds -> typ -> value -> list_value -> 'a1) -> (id -> extop ->
      typ -> value -> typ -> 'a1) -> (id -> castop -> typ -> value -> typ ->
      'a1) -> (id -> cond -> typ -> value -> value -> 'a1) -> (id -> value ->
      typ -> value -> value -> 'a1) -> (id -> noret -> tailc -> typ -> id ->
      params -> 'a1) -> cmd -> 'a1 **)
  
  let cmd_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
    | Coq_insn_bop (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3
    | Coq_insn_extractvalue (x, x0, x1, x2) -> f0 x x0 x1 x2
    | Coq_insn_insertvalue (x, x0, x1, x2, x3, x4) -> f1 x x0 x1 x2 x3 x4
    | Coq_insn_malloc (x, x0, x1, x2) -> f2 x x0 x1 x2
    | Coq_insn_free (x, x0, x1) -> f3 x x0 x1
    | Coq_insn_alloca (x, x0, x1, x2) -> f4 x x0 x1 x2
    | Coq_insn_load (x, x0, x1, x2) -> f5 x x0 x1 x2
    | Coq_insn_store (x, x0, x1, x2, x3) -> f6 x x0 x1 x2 x3
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
      align -> 'a1) -> (id -> typ -> value -> value -> align -> 'a1) -> (id
      -> inbounds -> typ -> value -> list_value -> 'a1) -> (id -> extop ->
      typ -> value -> typ -> 'a1) -> (id -> castop -> typ -> value -> typ ->
      'a1) -> (id -> cond -> typ -> value -> value -> 'a1) -> (id -> value ->
      typ -> value -> value -> 'a1) -> (id -> noret -> tailc -> typ -> id ->
      params -> 'a1) -> cmd -> 'a1 **)
  
  let cmd_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
    | Coq_insn_bop (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3
    | Coq_insn_extractvalue (x, x0, x1, x2) -> f0 x x0 x1 x2
    | Coq_insn_insertvalue (x, x0, x1, x2, x3, x4) -> f1 x x0 x1 x2 x3 x4
    | Coq_insn_malloc (x, x0, x1, x2) -> f2 x x0 x1 x2
    | Coq_insn_free (x, x0, x1) -> f3 x x0 x1
    | Coq_insn_alloca (x, x0, x1, x2) -> f4 x x0 x1 x2
    | Coq_insn_load (x, x0, x1, x2) -> f5 x x0 x1 x2
    | Coq_insn_store (x, x0, x1, x2, x3) -> f6 x x0 x1 x2 x3
    | Coq_insn_gep (x, x0, x1, x2, x3) -> f7 x x0 x1 x2 x3
    | Coq_insn_ext (x, x0, x1, x2, x3) -> f8 x x0 x1 x2 x3
    | Coq_insn_cast (x, x0, x1, x2, x3) -> f9 x x0 x1 x2 x3
    | Coq_insn_icmp (x, x0, x1, x2, x3) -> f10 x x0 x1 x2 x3
    | Coq_insn_select (x, x0, x1, x2, x3) -> f11 x x0 x1 x2 x3
    | Coq_insn_call (x, x0, x1, x2, x3, x4) -> f12 x x0 x1 x2 x3 x4
  
  type phinode =
    | Coq_insn_phi of id * typ * list_value_l
  
  (** val phinode_rect :
      (id -> typ -> list_value_l -> 'a1) -> phinode -> 'a1 **)
  
  let phinode_rect f = function
    | Coq_insn_phi (x, x0, x1) -> f x x0 x1
  
  (** val phinode_rec :
      (id -> typ -> list_value_l -> 'a1) -> phinode -> 'a1 **)
  
  let phinode_rec f = function
    | Coq_insn_phi (x, x0, x1) -> f x x0 x1
  
  type arg = typ*id
  
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
  
  type args = (typ*id) list
  
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
  
  type module_info = coq_module*(usedef_id*usedef_block)
  
  type fdef_info = fdef*dt
  
  type intrinsic_funs = ids
  
  (** val map_list_value_l :
      (value -> l -> 'a1) -> list_value_l -> 'a1 list **)
  
  let rec map_list_value_l f = function
    | Nil_list_value_l -> []
    | Cons_list_value_l (h0, h1, tl_) -> (f h0 h1)::(map_list_value_l f tl_)
  
  (** val make_list_value_l : (value*l) list -> list_value_l **)
  
  let rec make_list_value_l = function
    | [] -> Nil_list_value_l
    | p::tl_ ->
        let h0,h1 = p in Cons_list_value_l (h0, h1, (make_list_value_l tl_))
  
  (** val unmake_list_value_l : list_value_l -> (value*l) list **)
  
  let rec unmake_list_value_l = function
    | Nil_list_value_l -> []
    | Cons_list_value_l (h0, h1, tl_) -> (h0,h1)::(unmake_list_value_l tl_)
  
  (** val nth_list_value_l : nat -> list_value_l -> (value*l) option **)
  
  let rec nth_list_value_l n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_value_l -> None
             | Cons_list_value_l (h0, h1, tl_) -> Some (h0,h1))
      | S m ->
          (match l0 with
             | Nil_list_value_l -> None
             | Cons_list_value_l (h0, h1, tl_) -> nth_list_value_l m tl_)
  
  (** val app_list_value_l : list_value_l -> list_value_l -> list_value_l **)
  
  let rec app_list_value_l l0 m =
    match l0 with
      | Nil_list_value_l -> m
      | Cons_list_value_l (h0, h1, tl_) -> Cons_list_value_l (h0, h1,
          (app_list_value_l tl_ m))
  
  (** val map_list_value : (value -> 'a1) -> list_value -> 'a1 list **)
  
  let rec map_list_value f = function
    | Nil_list_value -> []
    | Cons_list_value (h, tl_) -> (f h)::(map_list_value f tl_)
  
  (** val make_list_value : value list -> list_value **)
  
  let rec make_list_value = function
    | [] -> Nil_list_value
    | h::tl_ -> Cons_list_value (h, (make_list_value tl_))
  
  (** val unmake_list_value : list_value -> value list **)
  
  let rec unmake_list_value = function
    | Nil_list_value -> []
    | Cons_list_value (h, tl_) -> h::(unmake_list_value tl_)
  
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
    | Nil_list_const -> []
    | Cons_list_const (h, tl_) -> (f h)::(map_list_const f tl_)
  
  (** val make_list_const : const list -> list_const **)
  
  let rec make_list_const = function
    | [] -> Nil_list_const
    | h::tl_ -> Cons_list_const (h, (make_list_const tl_))
  
  (** val unmake_list_const : list_const -> const list **)
  
  let rec unmake_list_const = function
    | Nil_list_const -> []
    | Cons_list_const (h, tl_) -> h::(unmake_list_const tl_)
  
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
    | Nil_list_typ -> []
    | Cons_list_typ (h, tl_) -> (f h)::(map_list_typ f tl_)
  
  (** val make_list_typ : typ list -> list_typ **)
  
  let rec make_list_typ = function
    | [] -> Nil_list_typ
    | h::tl_ -> Cons_list_typ (h, (make_list_typ tl_))
  
  (** val unmake_list_typ : list_typ -> typ list **)
  
  let rec unmake_list_typ = function
    | Nil_list_typ -> []
    | Cons_list_typ (h, tl_) -> h::(unmake_list_typ tl_)
  
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
  
  let list_const_rec2 f f0 f1 f2 f3 f4 f5 f6 =
    let rec f7 = function
      | Coq_const_int (s, i0) -> f s i0
      | Coq_const_undef t0 -> f0 t0
      | Coq_const_null t0 -> f1 t0
      | Coq_const_arr l0 -> f2 l0 (f8 l0)
      | Coq_const_struct l0 -> f3 l0 (f8 l0)
      | Coq_const_gid (t0, i0) -> f4 t0 i0
    and f8 = function
      | Nil_list_const -> f5
      | Cons_list_const (c, l1) -> f6 c (f7 c) l1 (f8 l1)
    in f8
  
  (** val const_rec2 :
      (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const
      -> 'a2 -> 'a1) -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) ->
      'a2 -> (const -> 'a1 -> list_const -> 'a2 -> 'a2) -> const -> 'a1 **)
  
  let const_rec2 f f0 f1 f2 f3 f4 f5 f6 =
    let rec f7 = function
      | Coq_const_int (s, i0) -> f s i0
      | Coq_const_undef t0 -> f0 t0
      | Coq_const_null t0 -> f1 t0
      | Coq_const_arr l0 -> f2 l0 (f8 l0)
      | Coq_const_struct l0 -> f3 l0 (f8 l0)
      | Coq_const_gid (t0, i0) -> f4 t0 i0
    and f8 = function
      | Nil_list_const -> f5
      | Cons_list_const (c, l1) -> f6 c (f7 c) l1 (f8 l1)
    in f7
  
  (** val const_mutrec :
      (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const
      -> 'a2 -> 'a1) -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) ->
      'a2 -> (const -> 'a1 -> list_const -> 'a2 -> 'a2) -> (const ->
      'a1)*(list_const -> 'a2) **)
  
  let const_mutrec h1 h2 h3 h4 h5 h6 h7 h8 =
    (const_rec2 h1 h2 h3 h4 h5 h6 h7 h8),(list_const_rec2 h1 h2 h3 h4 h5 h6
                                           h7 h8)
  
  (** val list_typ_rec2 :
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 ->
      'a1) -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a1) -> (list_typ -> 'a2 ->
      'a1) -> (typ -> 'a1 -> 'a1) -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 ->
      'a2) -> list_typ -> 'a2 **)
  
  let list_typ_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 =
    let rec f11 = function
      | Coq_typ_int s -> f s
      | Coq_typ_float -> f0
      | Coq_typ_double -> f1
      | Coq_typ_void -> f2
      | Coq_typ_label -> f3
      | Coq_typ_metadata -> f4
      | Coq_typ_array (s, t1) -> f5 s t1 (f11 t1)
      | Coq_typ_function (t1, l0) -> f6 t1 (f11 t1) l0 (f12 l0)
      | Coq_typ_struct l0 -> f7 l0 (f12 l0)
      | Coq_typ_pointer t1 -> f8 t1 (f11 t1)
    and f12 = function
      | Nil_list_typ -> f9
      | Cons_list_typ (t0, l1) -> f10 t0 (f11 t0) l1 (f12 l1)
    in f12
  
  (** val typ_rec2 :
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 ->
      'a1) -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a1) -> (list_typ -> 'a2 ->
      'a1) -> (typ -> 'a1 -> 'a1) -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 ->
      'a2) -> typ -> 'a1 **)
  
  let typ_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 =
    let rec f11 = function
      | Coq_typ_int s -> f s
      | Coq_typ_float -> f0
      | Coq_typ_double -> f1
      | Coq_typ_void -> f2
      | Coq_typ_label -> f3
      | Coq_typ_metadata -> f4
      | Coq_typ_array (s, t1) -> f5 s t1 (f11 t1)
      | Coq_typ_function (t1, l0) -> f6 t1 (f11 t1) l0 (f12 l0)
      | Coq_typ_struct l0 -> f7 l0 (f12 l0)
      | Coq_typ_pointer t1 -> f8 t1 (f11 t1)
    and f12 = function
      | Nil_list_typ -> f9
      | Cons_list_typ (t0, l1) -> f10 t0 (f11 t0) l1 (f12 l1)
    in f11
  
  (** val typ_mutrec :
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 ->
      'a1) -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a1) -> (list_typ -> 'a2 ->
      'a1) -> (typ -> 'a1 -> 'a1) -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 ->
      'a2) -> (typ -> 'a1)*(list_typ -> 'a2) **)
  
  let typ_mutrec h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =
    (typ_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12),
      (list_typ_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)
 end

module LLVMlib = 
 struct 
  (** val id_dec : LLVMsyntax.id -> LLVMsyntax.id -> bool **)
  
  let id_dec =
    AtomImpl.eq_atom_dec
  
  (** val l_dec : LLVMsyntax.l -> LLVMsyntax.l -> bool **)
  
  let l_dec =
    AtomImpl.eq_atom_dec
  
  (** val coq_INT_dec : LLVMsyntax.coq_INT -> LLVMsyntax.coq_INT -> bool **)
  
  let coq_INT_dec = Llvm.APInt.compare
  
  (** val sz_dec : LLVMsyntax.sz -> LLVMsyntax.sz -> bool **)
  
  let sz_dec = (==)
  
  (** val align_dec : LLVMsyntax.align -> LLVMsyntax.align -> bool **)
  
  let align_dec = (==)
  
  (** val inbounds_dec :
      LLVMsyntax.inbounds -> LLVMsyntax.inbounds -> bool **)
  
  let inbounds_dec = (==)
  
  (** val tailc_dec : LLVMsyntax.tailc -> LLVMsyntax.tailc -> bool **)
  
  let tailc_dec = (==)
  
  (** val noret_dec : LLVMsyntax.noret -> LLVMsyntax.noret -> bool **)
  
  let noret_dec = (==)
  
  (** val szZERO : LLVMsyntax.sz **)
  
  let szZERO = 0
  
  (** val szONE : LLVMsyntax.sz **)
  
  let szONE = 1
  
  (** val nat2sz : nat -> LLVMsyntax.sz **)
  
  let nat2sz = Symexe_aux.nat2int
  
  (** val sz2nat : LLVMsyntax.sz -> nat **)
  
  let sz2nat = Symexe_aux.int2nat
  
  (** val coq_INT2nat : LLVMsyntax.coq_INT -> nat **)
  
  let coq_INT2nat = Symexe_aux.llapint2nat
  
  (** val lempty_set : LLVMsyntax.l set **)
  
  let lempty_set =
    empty_set
  
  (** val lset_add : LLVMsyntax.l -> LLVMsyntax.ls -> LLVMsyntax.l set **)
  
  let lset_add l1 ls2 =
    set_add (eq_dec0 (eqDec_eq_of_EqDec eqDec_atom)) l1 ls2
  
  (** val lset_union : LLVMsyntax.ls -> LLVMsyntax.ls -> LLVMsyntax.l set **)
  
  let lset_union ls1 ls2 =
    set_union (eq_dec0 (eqDec_eq_of_EqDec eqDec_atom)) ls1 ls2
  
  (** val lset_inter : LLVMsyntax.ls -> LLVMsyntax.ls -> LLVMsyntax.l set **)
  
  let lset_inter ls1 ls2 =
    set_inter (eq_dec0 (eqDec_eq_of_EqDec eqDec_atom)) ls1 ls2
  
  (** val lset_eq : LLVMsyntax.ls -> LLVMsyntax.ls -> bool **)
  
  let lset_eq ls1 ls2 =
    match lset_inter ls1 ls2 with
      | [] -> true
      | l0::l1 -> false
  
  (** val lset_neq : LLVMsyntax.ls -> LLVMsyntax.ls -> bool **)
  
  let lset_neq ls1 ls2 =
    match lset_inter ls1 ls2 with
      | [] -> false
      | l0::l1 -> true
  
  (** val lset_single : LLVMsyntax.l -> LLVMsyntax.l set **)
  
  let lset_single l0 =
    lset_add l0 lempty_set
  
  (** val lset_mem : LLVMsyntax.l -> LLVMsyntax.ls -> bool **)
  
  let lset_mem l0 ls0 =
    set_mem (eq_dec0 (eqDec_eq_of_EqDec eqDec_atom)) l0 ls0
  
  (** val getCmdID : LLVMsyntax.cmd -> LLVMsyntax.id **)
  
  let getCmdID = function
    | LLVMsyntax.Coq_insn_bop (id0, b, sz0, v1, v2) -> id0
    | LLVMsyntax.Coq_insn_extractvalue (id0, typs, id1, c1) -> id0
    | LLVMsyntax.Coq_insn_insertvalue (id0, typs, id1, typ1, v1, c2) -> id0
    | LLVMsyntax.Coq_insn_malloc (id0, t0, s, a) -> id0
    | LLVMsyntax.Coq_insn_free (id0, t0, v) -> id0
    | LLVMsyntax.Coq_insn_alloca (id0, t0, s, a) -> id0
    | LLVMsyntax.Coq_insn_load (id0, typ1, v1, a) -> id0
    | LLVMsyntax.Coq_insn_store (id0, typ1, v1, v2, a) -> id0
    | LLVMsyntax.Coq_insn_gep (id0, i1, t0, v, l0) -> id0
    | LLVMsyntax.Coq_insn_ext (id0, e, sz1, v1, sz2) -> id0
    | LLVMsyntax.Coq_insn_cast (id0, c, typ1, v1, typ2) -> id0
    | LLVMsyntax.Coq_insn_icmp (id0, cond0, typ0, v1, v2) -> id0
    | LLVMsyntax.Coq_insn_select (id0, v0, typ0, v1, v2) -> id0
    | LLVMsyntax.Coq_insn_call (id0, n, t0, typ0, id1, paraml) -> id0
  
  (** val getTerminatorID : LLVMsyntax.terminator -> LLVMsyntax.id **)
  
  let getTerminatorID = function
    | LLVMsyntax.Coq_insn_return (id0, t0, v) -> id0
    | LLVMsyntax.Coq_insn_return_void id0 -> id0
    | LLVMsyntax.Coq_insn_br (id0, v, l1, l2) -> id0
    | LLVMsyntax.Coq_insn_br_uncond (id0, l0) -> id0
    | LLVMsyntax.Coq_insn_unreachable id0 -> id0
  
  (** val getPhiNodeID : LLVMsyntax.phinode -> LLVMsyntax.id **)
  
  let getPhiNodeID = function
    | LLVMsyntax.Coq_insn_phi (id0, t0, l0) -> id0
  
  (** val getValueID : LLVMsyntax.value -> LLVMsyntax.id option **)
  
  let getValueID = function
    | LLVMsyntax.Coq_value_id id0 -> Some id0
    | LLVMsyntax.Coq_value_const c -> None
  
  (** val getInsnID : LLVMsyntax.insn -> LLVMsyntax.id **)
  
  let getInsnID = function
    | LLVMsyntax.Coq_insn_phinode p -> getPhiNodeID p
    | LLVMsyntax.Coq_insn_cmd c -> getCmdID c
    | LLVMsyntax.Coq_insn_terminator t0 -> getTerminatorID t0
  
  (** val isPhiNodeB : LLVMsyntax.insn -> bool **)
  
  let isPhiNodeB = function
    | LLVMsyntax.Coq_insn_phinode p -> true
    | _ -> false
  
  (** val getSubTypFromConstIdxs :
      LLVMsyntax.list_const -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
  
  let rec getSubTypFromConstIdxs idxs t0 =
    match idxs with
      | LLVMsyntax.Nil_list_const -> Some t0
      | LLVMsyntax.Cons_list_const (idx, idxs') ->
          (match t0 with
             | LLVMsyntax.Coq_typ_array (sz0, t') ->
                 getSubTypFromConstIdxs idxs' t'
             | LLVMsyntax.Coq_typ_struct lt0 ->
                 (match idx with
                    | LLVMsyntax.Coq_const_int (sz0, i0) ->
                        (match LLVMsyntax.nth_list_typ (coq_INT2nat i0) lt0 with
                           | Some t' -> getSubTypFromConstIdxs idxs' t'
                           | None -> None)
                    | _ -> None)
             | _ -> None)
  
  (** val getSubTypFromValueIdxs :
      LLVMsyntax.list_value -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
  
  let rec getSubTypFromValueIdxs idxs t0 =
    match idxs with
      | LLVMsyntax.Nil_list_value -> Some t0
      | LLVMsyntax.Cons_list_value (idx, idxs') ->
          (match t0 with
             | LLVMsyntax.Coq_typ_array (sz0, t') ->
                 getSubTypFromValueIdxs idxs' t'
             | LLVMsyntax.Coq_typ_struct lt0 ->
                 (match idx with
                    | LLVMsyntax.Coq_value_id i0 -> None
                    | LLVMsyntax.Coq_value_const c ->
                        (match c with
                           | LLVMsyntax.Coq_const_int (
                               sz0, i0) ->
                               (match LLVMsyntax.nth_list_typ
                                        (coq_INT2nat i0) lt0 with
                                  | Some t' ->
                                      getSubTypFromValueIdxs idxs' t'
                                  | None -> None)
                           | _ -> None))
             | _ -> None)
  
  (** val getGEPTyp :
      LLVMsyntax.list_value -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
  
  let getGEPTyp idxs t0 =
    match idxs with
      | LLVMsyntax.Nil_list_value -> None
      | LLVMsyntax.Cons_list_value (idx, idxs') ->
          (match getSubTypFromValueIdxs idxs' t0 with
             | Some t' -> Some (LLVMsyntax.Coq_typ_pointer t')
             | None -> None)
  
  (** val getLoadTyp : LLVMsyntax.typ -> LLVMsyntax.typ option **)
  
  let getLoadTyp = function
    | LLVMsyntax.Coq_typ_pointer t' -> Some t'
    | _ -> None
  
  (** val getCmdTyp : LLVMsyntax.cmd -> LLVMsyntax.typ option **)
  
  let getCmdTyp = function
    | LLVMsyntax.Coq_insn_bop (i1, b, sz0, v, v0) -> Some
        (LLVMsyntax.Coq_typ_int sz0)
    | LLVMsyntax.Coq_insn_extractvalue (i1, typ0, v, idxs) ->
        getSubTypFromConstIdxs idxs typ0
    | LLVMsyntax.Coq_insn_insertvalue (i1, typ0, v, t0, v0, l0) -> Some typ0
    | LLVMsyntax.Coq_insn_malloc (i1, typ0, s, a) -> Some
        (LLVMsyntax.Coq_typ_pointer typ0)
    | LLVMsyntax.Coq_insn_alloca (i1, typ0, s, a) -> Some
        (LLVMsyntax.Coq_typ_pointer typ0)
    | LLVMsyntax.Coq_insn_load (i1, typ0, v, a) -> getLoadTyp typ0
    | LLVMsyntax.Coq_insn_gep (i1, i2, typ0, v, idxs) -> getGEPTyp idxs typ0
    | LLVMsyntax.Coq_insn_ext (i1, e, t0, v, typ2) -> Some typ2
    | LLVMsyntax.Coq_insn_cast (i1, c, t0, v, typ0) -> Some typ0
    | LLVMsyntax.Coq_insn_icmp (i1, c, t0, v, v0) -> Some
        (LLVMsyntax.Coq_typ_int szONE)
    | LLVMsyntax.Coq_insn_select (i1, v, typ0, v0, v1) -> Some typ0
    | LLVMsyntax.Coq_insn_call (i1, n, t0, typ0, i2, p) ->
        if n then Some LLVMsyntax.Coq_typ_void else Some typ0
    | _ -> Some LLVMsyntax.Coq_typ_void
  
  (** val getTerminatorTyp : LLVMsyntax.terminator -> LLVMsyntax.typ **)
  
  let getTerminatorTyp = function
    | LLVMsyntax.Coq_insn_return (i1, typ0, v) -> typ0
    | _ -> LLVMsyntax.Coq_typ_void
  
  (** val getPhiNodeTyp : LLVMsyntax.phinode -> LLVMsyntax.typ **)
  
  let getPhiNodeTyp = function
    | LLVMsyntax.Coq_insn_phi (i1, typ0, l0) -> typ0
  
  (** val getInsnTyp : LLVMsyntax.insn -> LLVMsyntax.typ option **)
  
  let getInsnTyp = function
    | LLVMsyntax.Coq_insn_phinode p -> Some (getPhiNodeTyp p)
    | LLVMsyntax.Coq_insn_cmd c -> getCmdTyp c
    | LLVMsyntax.Coq_insn_terminator t0 -> Some (getTerminatorTyp t0)
  
  (** val getPointerEltTyp : LLVMsyntax.typ -> LLVMsyntax.typ option **)
  
  let getPointerEltTyp = function
    | LLVMsyntax.Coq_typ_pointer t' -> Some t'
    | _ -> None
  
  (** val getValueIDs : LLVMsyntax.value -> LLVMsyntax.ids **)
  
  let getValueIDs v =
    match getValueID v with
      | Some id0 -> id0::[]
      | None -> []
  
  (** val getParamsOperand : LLVMsyntax.params -> LLVMsyntax.ids **)
  
  let rec getParamsOperand = function
    | [] -> []
    | p::lp' -> let t0,v = p in app (getValueIDs v) (getParamsOperand lp')
  
  (** val list_prj1 : ('a1*'a2) list -> 'a1 list **)
  
  let rec list_prj1 = function
    | [] -> []
    | p::ls' -> let x,y = p in x::(list_prj1 ls')
  
  (** val list_prj2 : ('a1*'a2) list -> 'a2 list **)
  
  let rec list_prj2 = function
    | [] -> []
    | p::ls' -> let x,y = p in y::(list_prj2 ls')
  
  (** val getCmdOperands : LLVMsyntax.cmd -> LLVMsyntax.ids **)
  
  let getCmdOperands = function
    | LLVMsyntax.Coq_insn_bop (i1, b, s, v1, v2) ->
        app (getValueIDs v1) (getValueIDs v2)
    | LLVMsyntax.Coq_insn_extractvalue (i1, t0, v, l0) -> getValueIDs v
    | LLVMsyntax.Coq_insn_insertvalue (i1, t0, v1, t1, v2, l0) ->
        app (getValueIDs v1) (getValueIDs v2)
    | LLVMsyntax.Coq_insn_free (i1, t0, v) -> getValueIDs v
    | LLVMsyntax.Coq_insn_load (i1, t0, v, a) -> getValueIDs v
    | LLVMsyntax.Coq_insn_store (i1, t0, v1, v2, a) ->
        app (getValueIDs v1) (getValueIDs v2)
    | LLVMsyntax.Coq_insn_gep (i1, i2, t0, v, l0) -> getValueIDs v
    | LLVMsyntax.Coq_insn_ext (i1, e, t0, v1, typ2) -> getValueIDs v1
    | LLVMsyntax.Coq_insn_cast (i1, c, t0, v, t1) -> getValueIDs v
    | LLVMsyntax.Coq_insn_icmp (i1, c, t0, v1, v2) ->
        app (getValueIDs v1) (getValueIDs v2)
    | LLVMsyntax.Coq_insn_select (i1, v0, t0, v1, v2) ->
        app (getValueIDs v0) (app (getValueIDs v1) (getValueIDs v2))
    | LLVMsyntax.Coq_insn_call (i1, n, t0, t1, i2, lp) -> getParamsOperand lp
    | _ -> []
  
  (** val getTerminatorOperands : LLVMsyntax.terminator -> LLVMsyntax.ids **)
  
  let getTerminatorOperands = function
    | LLVMsyntax.Coq_insn_return (i1, t0, v) -> getValueIDs v
    | LLVMsyntax.Coq_insn_br (i1, v, l0, l1) -> getValueIDs v
    | _ -> []
  
  (** val values2ids : LLVMsyntax.value list -> LLVMsyntax.ids **)
  
  let rec values2ids = function
    | [] -> []
    | v::vs' ->
        (match v with
           | LLVMsyntax.Coq_value_id id0 -> id0::(values2ids vs')
           | LLVMsyntax.Coq_value_const c -> values2ids vs')
  
  (** val getPhiNodeOperands : LLVMsyntax.phinode -> LLVMsyntax.ids **)
  
  let getPhiNodeOperands = function
    | LLVMsyntax.Coq_insn_phi (i1, t0, ls0) ->
        values2ids (list_prj1 (LLVMsyntax.unmake_list_value_l ls0))
  
  (** val getInsnOperands : LLVMsyntax.insn -> LLVMsyntax.ids **)
  
  let getInsnOperands = function
    | LLVMsyntax.Coq_insn_phinode p -> getPhiNodeOperands p
    | LLVMsyntax.Coq_insn_cmd c -> getCmdOperands c
    | LLVMsyntax.Coq_insn_terminator t0 -> getTerminatorOperands t0
  
  (** val getCmdLabels : LLVMsyntax.cmd -> LLVMsyntax.ls **)
  
  let getCmdLabels i0 =
    []
  
  (** val getTerminatorLabels : LLVMsyntax.terminator -> LLVMsyntax.ls **)
  
  let getTerminatorLabels = function
    | LLVMsyntax.Coq_insn_br (i1, v, l1, l2) -> l1::(l2::[])
    | LLVMsyntax.Coq_insn_br_uncond (i1, l0) -> l0::[]
    | _ -> []
  
  (** val getPhiNodeLabels : LLVMsyntax.phinode -> LLVMsyntax.ls **)
  
  let getPhiNodeLabels = function
    | LLVMsyntax.Coq_insn_phi (i1, t0, ls0) ->
        list_prj2 (LLVMsyntax.unmake_list_value_l ls0)
  
  (** val getInsnLabels : LLVMsyntax.insn -> LLVMsyntax.ls **)
  
  let getInsnLabels = function
    | LLVMsyntax.Coq_insn_phinode p -> getPhiNodeLabels p
    | LLVMsyntax.Coq_insn_cmd c -> getCmdLabels c
    | LLVMsyntax.Coq_insn_terminator tmn -> getTerminatorLabels tmn
  
  (** val args2Typs : LLVMsyntax.args -> LLVMsyntax.list_typ **)
  
  let rec args2Typs = function
    | [] -> LLVMsyntax.Nil_list_typ
    | p::la' ->
        let t0,id0 = p in LLVMsyntax.Cons_list_typ (t0, (args2Typs la'))
  
  (** val getFheaderTyp : LLVMsyntax.fheader -> LLVMsyntax.typ **)
  
  let getFheaderTyp = function
    | LLVMsyntax.Coq_fheader_intro (t0, i0, la) ->
        LLVMsyntax.Coq_typ_function (t0, (args2Typs la))
  
  (** val getFdecTyp : LLVMsyntax.fdec -> LLVMsyntax.typ **)
  
  let getFdecTyp fdec0 =
    getFheaderTyp fdec0
  
  (** val getFdefTyp : LLVMsyntax.fdef -> LLVMsyntax.typ **)
  
  let getFdefTyp = function
    | LLVMsyntax.Coq_fdef_intro (fheader0, b) -> getFheaderTyp fheader0
  
  (** val getBindingTyp : LLVMsyntax.id_binding -> LLVMsyntax.typ option **)
  
  let getBindingTyp = function
    | LLVMsyntax.Coq_id_binding_none -> None
    | LLVMsyntax.Coq_id_binding_cmd i0 -> getCmdTyp i0
    | LLVMsyntax.Coq_id_binding_phinode i0 -> Some (getPhiNodeTyp i0)
    | LLVMsyntax.Coq_id_binding_terminator i0 -> Some (getTerminatorTyp i0)
    | LLVMsyntax.Coq_id_binding_gvar g ->
        let LLVMsyntax.Coq_gvar_intro (i0, t0, c, a) = g in
        Some (LLVMsyntax.Coq_typ_pointer t0)
    | LLVMsyntax.Coq_id_binding_fdec fdec0 -> Some (getFdecTyp fdec0)
    | LLVMsyntax.Coq_id_binding_arg a -> let t0,id0 = a in Some t0
  
  (** val getCmdsFromBlock : LLVMsyntax.block -> LLVMsyntax.cmds **)
  
  let getCmdsFromBlock = function
    | LLVMsyntax.Coq_block_intro (l0, p, li, t0) -> li
  
  (** val getPhiNodesFromBlock : LLVMsyntax.block -> LLVMsyntax.phinodes **)
  
  let getPhiNodesFromBlock = function
    | LLVMsyntax.Coq_block_intro (l0, li, c, t0) -> li
  
  (** val getTerminatorFromBlock :
      LLVMsyntax.block -> LLVMsyntax.terminator **)
  
  let getTerminatorFromBlock = function
    | LLVMsyntax.Coq_block_intro (l0, p, c, t0) -> t0
  
  (** val getBindingFdec :
      LLVMsyntax.id_binding -> LLVMsyntax.fdec option **)
  
  let getBindingFdec = function
    | LLVMsyntax.Coq_id_binding_fdec fdec0 -> Some fdec0
    | _ -> None
  
  (** val getBindingArg : LLVMsyntax.id_binding -> LLVMsyntax.arg option **)
  
  let getBindingArg = function
    | LLVMsyntax.Coq_id_binding_arg arg0 -> Some arg0
    | _ -> None
  
  (** val getBindingGvar :
      LLVMsyntax.id_binding -> LLVMsyntax.gvar option **)
  
  let getBindingGvar = function
    | LLVMsyntax.Coq_id_binding_gvar g -> Some g
    | _ -> None
  
  (** val getBindingCmd : LLVMsyntax.id_binding -> LLVMsyntax.cmd option **)
  
  let getBindingCmd = function
    | LLVMsyntax.Coq_id_binding_cmd i0 -> Some i0
    | _ -> None
  
  (** val getBindingInsn :
      LLVMsyntax.id_binding -> LLVMsyntax.insn option **)
  
  let getBindingInsn = function
    | LLVMsyntax.Coq_id_binding_cmd c -> Some (LLVMsyntax.Coq_insn_cmd c)
    | LLVMsyntax.Coq_id_binding_phinode p -> Some
        (LLVMsyntax.Coq_insn_phinode p)
    | LLVMsyntax.Coq_id_binding_terminator tmn -> Some
        (LLVMsyntax.Coq_insn_terminator tmn)
    | _ -> None
  
  (** val getBindingPhiNode :
      LLVMsyntax.id_binding -> LLVMsyntax.phinode option **)
  
  let getBindingPhiNode = function
    | LLVMsyntax.Coq_id_binding_phinode i0 -> Some i0
    | _ -> None
  
  (** val getBindingTerminator :
      LLVMsyntax.id_binding -> LLVMsyntax.terminator option **)
  
  let getBindingTerminator = function
    | LLVMsyntax.Coq_id_binding_terminator i0 -> Some i0
    | _ -> None
  
  (** val getFheaderID : LLVMsyntax.fheader -> LLVMsyntax.id **)
  
  let getFheaderID = function
    | LLVMsyntax.Coq_fheader_intro (t0, id0, a) -> id0
  
  (** val getFdecID : LLVMsyntax.fdec -> LLVMsyntax.id **)
  
  let getFdecID fd =
    getFheaderID fd
  
  (** val getFdefID : LLVMsyntax.fdef -> LLVMsyntax.id **)
  
  let getFdefID = function
    | LLVMsyntax.Coq_fdef_intro (fh, b) -> getFheaderID fh
  
  (** val getLabelViaIDFromList :
      LLVMsyntax.list_value_l -> LLVMsyntax.id -> LLVMsyntax.l option **)
  
  let rec getLabelViaIDFromList ls0 branch =
    match ls0 with
      | LLVMsyntax.Nil_list_value_l -> None
      | LLVMsyntax.Cons_list_value_l (v, l0, ls') ->
          (match v with
             | LLVMsyntax.Coq_value_id id0 ->
                 if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 branch
                 then Some l0
                 else getLabelViaIDFromList ls' branch
             | LLVMsyntax.Coq_value_const c ->
                 getLabelViaIDFromList ls' branch)
  
  (** val getLabelViaIDFromPhiNode :
      LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.l option **)
  
  let getLabelViaIDFromPhiNode phi branch =
    let LLVMsyntax.Coq_insn_phi (i0, t0, ls0) = phi in
    getLabelViaIDFromList ls0 branch
  
  (** val getLabelsFromIdls : LLVMsyntax.list_value_l -> LLVMsyntax.ls **)
  
  let rec getLabelsFromIdls = function
    | LLVMsyntax.Nil_list_value_l -> lempty_set
    | LLVMsyntax.Cons_list_value_l (v, l0, idls') ->
        lset_add l0 (getLabelsFromIdls idls')
  
  (** val getLabelsFromPhiNode : LLVMsyntax.phinode -> LLVMsyntax.ls **)
  
  let getLabelsFromPhiNode = function
    | LLVMsyntax.Coq_insn_phi (i0, t0, ls0) -> getLabelsFromIdls ls0
  
  (** val getLabelsFromPhiNodes :
      LLVMsyntax.phinode list -> LLVMsyntax.ls **)
  
  let rec getLabelsFromPhiNodes = function
    | [] -> lempty_set
    | phi::phis' ->
        lset_union (getLabelsFromPhiNode phi) (getLabelsFromPhiNodes phis')
  
  (** val getIDLabelsFromPhiNode :
      LLVMsyntax.phinode -> LLVMsyntax.list_value_l **)
  
  let getIDLabelsFromPhiNode = function
    | LLVMsyntax.Coq_insn_phi (i0, t0, idls) -> idls
  
  (** val getLabelViaIDFromIDLabels :
      LLVMsyntax.list_value_l -> LLVMsyntax.id -> LLVMsyntax.l option **)
  
  let rec getLabelViaIDFromIDLabels idls id0 =
    match idls with
      | LLVMsyntax.Nil_list_value_l -> None
      | LLVMsyntax.Cons_list_value_l (v, l0, idls') ->
          (match v with
             | LLVMsyntax.Coq_value_id id1 ->
                 if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 id1
                 then Some l0
                 else getLabelViaIDFromIDLabels idls' id0
             | LLVMsyntax.Coq_value_const c ->
                 getLabelViaIDFromIDLabels idls' id0)
  
  (** val _getLabelViaIDPhiNode :
      LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.l option **)
  
  let _getLabelViaIDPhiNode p id0 =
    let LLVMsyntax.Coq_insn_phi (i0, t0, ls0) = p in
    getLabelViaIDFromIDLabels ls0 id0
  
  (** val getLabelViaIDPhiNode :
      LLVMsyntax.insn -> LLVMsyntax.id -> LLVMsyntax.l option **)
  
  let getLabelViaIDPhiNode phi id0 =
    match phi with
      | LLVMsyntax.Coq_insn_phinode p -> _getLabelViaIDPhiNode p id0
      | _ -> None
  
  (** val getReturnTyp : LLVMsyntax.fdef -> LLVMsyntax.typ **)
  
  let getReturnTyp = function
    | LLVMsyntax.Coq_fdef_intro (f, b) ->
        let LLVMsyntax.Coq_fheader_intro (t0, i0, a) = f in t0
  
  (** val getGvarID : LLVMsyntax.gvar -> LLVMsyntax.id **)
  
  let getGvarID = function
    | LLVMsyntax.Coq_gvar_intro (id0, t0, c, a) -> id0
  
  (** val getCallName : LLVMsyntax.insn -> LLVMsyntax.id option **)
  
  let getCallName = function
    | LLVMsyntax.Coq_insn_cmd c ->
        (match c with
           | LLVMsyntax.Coq_insn_call (i1, n, t0, t1, id0, p) -> Some id0
           | _ -> None)
    | _ -> None
  
  (** val getCallerReturnID : LLVMsyntax.cmd -> LLVMsyntax.id option **)
  
  let getCallerReturnID = function
    | LLVMsyntax.Coq_insn_call (id0, n, t0, t1, i0, p) ->
        if n then None else Some id0
    | _ -> None
  
  (** val getIdViaLabelFromIdls :
      LLVMsyntax.list_value_l -> LLVMsyntax.l -> LLVMsyntax.id option **)
  
  let rec getIdViaLabelFromIdls idls l0 =
    match idls with
      | LLVMsyntax.Nil_list_value_l -> None
      | LLVMsyntax.Cons_list_value_l (v, l1, idls') ->
          (match v with
             | LLVMsyntax.Coq_value_id id1 ->
                 if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) l1 l0
                 then Some id1
                 else getIdViaLabelFromIdls idls' l0
             | LLVMsyntax.Coq_value_const c -> getIdViaLabelFromIdls idls' l0)
  
  (** val getIdViaBlockFromIdls :
      LLVMsyntax.list_value_l -> LLVMsyntax.block -> LLVMsyntax.id option **)
  
  let getIdViaBlockFromIdls idls = function
    | LLVMsyntax.Coq_block_intro (l0, p, c, t0) ->
        getIdViaLabelFromIdls idls l0
  
  (** val getIdViaBlockFromPHINode :
      LLVMsyntax.phinode -> LLVMsyntax.block -> LLVMsyntax.id option **)
  
  let getIdViaBlockFromPHINode i0 b =
    let LLVMsyntax.Coq_insn_phi (i1, t0, idls) = i0 in
    getIdViaBlockFromIdls idls b
  
  (** val getPHINodesFromBlock :
      LLVMsyntax.block -> LLVMsyntax.phinode list **)
  
  let getPHINodesFromBlock = function
    | LLVMsyntax.Coq_block_intro (l0, lp, c, t0) -> lp
  
  (** val lookupBindingViaIDFromCmd :
      LLVMsyntax.cmd -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromCmd i0 id0 =
    if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 (getCmdID i0)
    then LLVMsyntax.Coq_id_binding_cmd i0
    else LLVMsyntax.Coq_id_binding_none
  
  (** val lookupBindingViaIDFromCmds :
      LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let rec lookupBindingViaIDFromCmds li id0 =
    match li with
      | [] -> LLVMsyntax.Coq_id_binding_none
      | i0::li' ->
          (match lookupBindingViaIDFromCmd i0 id0 with
             | LLVMsyntax.Coq_id_binding_cmd c ->
                 LLVMsyntax.Coq_id_binding_cmd i0
             | _ -> lookupBindingViaIDFromCmds li' id0)
  
  (** val lookupBindingViaIDFromPhiNode :
      LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromPhiNode i0 id0 =
    if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 (getPhiNodeID i0)
    then LLVMsyntax.Coq_id_binding_phinode i0
    else LLVMsyntax.Coq_id_binding_none
  
  (** val lookupBindingViaIDFromPhiNodes :
      LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let rec lookupBindingViaIDFromPhiNodes li id0 =
    match li with
      | [] -> LLVMsyntax.Coq_id_binding_none
      | i0::li' ->
          (match lookupBindingViaIDFromPhiNode i0 id0 with
             | LLVMsyntax.Coq_id_binding_phinode p ->
                 LLVMsyntax.Coq_id_binding_phinode i0
             | _ -> lookupBindingViaIDFromPhiNodes li' id0)
  
  (** val lookupBindingViaIDFromTerminator :
      LLVMsyntax.terminator -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromTerminator i0 id0 =
    if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 (getTerminatorID i0)
    then LLVMsyntax.Coq_id_binding_terminator i0
    else LLVMsyntax.Coq_id_binding_none
  
  (** val lookupBindingViaIDFromBlock :
      LLVMsyntax.block -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromBlock b id0 =
    let LLVMsyntax.Coq_block_intro (l0, ps, cs, t0) = b in
    (match lookupBindingViaIDFromPhiNodes ps id0 with
       | LLVMsyntax.Coq_id_binding_none ->
           (match lookupBindingViaIDFromCmds cs id0 with
              | LLVMsyntax.Coq_id_binding_none ->
                  lookupBindingViaIDFromTerminator t0 id0
              | x -> x)
       | x -> x)
  
  (** val lookupBindingViaIDFromBlocks :
      LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let rec lookupBindingViaIDFromBlocks lb id0 =
    match lb with
      | [] -> LLVMsyntax.Coq_id_binding_none
      | b::lb' ->
          (match lookupBindingViaIDFromBlock b id0 with
             | LLVMsyntax.Coq_id_binding_none ->
                 lookupBindingViaIDFromBlocks lb' id0
             | x -> x)
  
  (** val lookupBindingViaIDFromArg :
      LLVMsyntax.arg -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromArg a id0 =
    let t0,id' = a in
    if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 id'
    then LLVMsyntax.Coq_id_binding_arg a
    else LLVMsyntax.Coq_id_binding_none
  
  (** val lookupBindingViaIDFromArgs :
      LLVMsyntax.args -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let rec lookupBindingViaIDFromArgs la id0 =
    match la with
      | [] -> LLVMsyntax.Coq_id_binding_none
      | a::la' ->
          (match lookupBindingViaIDFromArg a id0 with
             | LLVMsyntax.Coq_id_binding_arg a' ->
                 LLVMsyntax.Coq_id_binding_arg a'
             | _ -> lookupBindingViaIDFromArgs la' id0)
  
  (** val lookupBindingViaIDFromFdec :
      LLVMsyntax.fdec -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromFdec fd id0 =
    let LLVMsyntax.Coq_fheader_intro (t0, id', la) = fd in
    if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 id'
    then LLVMsyntax.Coq_id_binding_fdec fd
    else lookupBindingViaIDFromArgs la id0
  
  (** val lookupBindingViaIDFromFdef :
      LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromFdef fd id0 =
    let LLVMsyntax.Coq_fdef_intro (fh, lb) = fd in
    lookupBindingViaIDFromBlocks lb id0
  
  (** val lookupBindingViaIDFromProduct :
      LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromProduct p id0 =
    match p with
      | LLVMsyntax.Coq_product_gvar g ->
          let LLVMsyntax.Coq_gvar_intro (id', t0, c, a) = g in
          if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 id'
          then LLVMsyntax.Coq_id_binding_gvar (LLVMsyntax.Coq_gvar_intro
                 (id', t0, c, a))
          else LLVMsyntax.Coq_id_binding_none
      | LLVMsyntax.Coq_product_fdec fdec0 ->
          lookupBindingViaIDFromFdec fdec0 id0
      | LLVMsyntax.Coq_product_fdef fdef0 ->
          lookupBindingViaIDFromFdef fdef0 id0
  
  (** val lookupBindingViaIDFromProducts :
      LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let rec lookupBindingViaIDFromProducts lp id0 =
    match lp with
      | [] -> LLVMsyntax.Coq_id_binding_none
      | p::lp' ->
          (match lookupBindingViaIDFromProduct p id0 with
             | LLVMsyntax.Coq_id_binding_none ->
                 lookupBindingViaIDFromProducts lp' id0
             | x -> x)
  
  (** val lookupBindingViaIDFromModule :
      LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromModule m id0 =
    let LLVMsyntax.Coq_module_intro (os, ps) = m in
    lookupBindingViaIDFromProducts ps id0
  
  (** val lookupBindingViaIDFromModules :
      LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let rec lookupBindingViaIDFromModules lm id0 =
    match lm with
      | [] -> LLVMsyntax.Coq_id_binding_none
      | m::lm' ->
          (match lookupBindingViaIDFromModule m id0 with
             | LLVMsyntax.Coq_id_binding_none ->
                 lookupBindingViaIDFromModules lm' id0
             | x -> x)
  
  (** val lookupBindingViaIDFromSystem :
      LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromSystem s id0 =
    lookupBindingViaIDFromModules s id0
  
  (** val isIDInBlockB : LLVMsyntax.id -> LLVMsyntax.block -> bool **)
  
  let isIDInBlockB id0 b =
    match lookupBindingViaIDFromBlock b id0 with
      | LLVMsyntax.Coq_id_binding_none -> false
      | _ -> true
  
  (** val lookupBlockViaIDFromBlocks :
      LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.block option **)
  
  let rec lookupBlockViaIDFromBlocks lb id0 =
    match lb with
      | [] -> None
      | b::lb' ->
          if isIDInBlockB id0 b
          then Some b
          else lookupBlockViaIDFromBlocks lb' id0
  
  (** val lookupBlockViaIDFromFdef :
      LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.block option **)
  
  let lookupBlockViaIDFromFdef fd id0 =
    let LLVMsyntax.Coq_fdef_intro (fh, lb) = fd in
    lookupBlockViaIDFromBlocks lb id0
  
  (** val lookupFdecViaIDFromProduct :
      LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let lookupFdecViaIDFromProduct p i0 =
    match p with
      | LLVMsyntax.Coq_product_fdec fd ->
          if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) (getFdecID fd) i0
          then Some fd
          else None
      | _ -> None
  
  (** val lookupFdecViaIDFromProducts :
      LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let rec lookupFdecViaIDFromProducts lp i0 =
    match lp with
      | [] -> None
      | p::lp' ->
          (match lookupFdecViaIDFromProduct p i0 with
             | Some fd -> Some fd
             | None -> lookupFdecViaIDFromProducts lp' i0)
  
  (** val lookupFdecViaIDFromModule :
      LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let lookupFdecViaIDFromModule m i0 =
    let LLVMsyntax.Coq_module_intro (os, ps) = m in
    lookupFdecViaIDFromProducts ps i0
  
  (** val lookupFdecViaIDFromModules :
      LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let rec lookupFdecViaIDFromModules lm i0 =
    match lm with
      | [] -> None
      | m::lm' ->
          (match lookupFdecViaIDFromModule m i0 with
             | Some fd -> Some fd
             | None -> lookupFdecViaIDFromModules lm' i0)
  
  (** val lookupFdecViaIDFromSystem :
      LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let lookupFdecViaIDFromSystem s i0 =
    lookupFdecViaIDFromModules s i0
  
  (** val lookupFdefViaIDFromProduct :
      LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.fdef option **)
  
  let lookupFdefViaIDFromProduct p i0 =
    match p with
      | LLVMsyntax.Coq_product_fdef fd ->
          if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) (getFdefID fd) i0
          then Some fd
          else None
      | _ -> None
  
  (** val lookupFdefViaIDFromProducts :
      LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.fdef option **)
  
  let rec lookupFdefViaIDFromProducts lp i0 =
    match lp with
      | [] -> None
      | p::lp' ->
          (match lookupFdefViaIDFromProduct p i0 with
             | Some fd -> Some fd
             | None -> lookupFdefViaIDFromProducts lp' i0)
  
  (** val lookupFdefViaIDFromModule :
      LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.fdef option **)
  
  let lookupFdefViaIDFromModule m i0 =
    let LLVMsyntax.Coq_module_intro (os, ps) = m in
    lookupFdefViaIDFromProducts ps i0
  
  (** val lookupFdefViaIDFromModules :
      LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.fdef option **)
  
  let rec lookupFdefViaIDFromModules lm i0 =
    match lm with
      | [] -> None
      | m::lm' ->
          (match lookupFdefViaIDFromModule m i0 with
             | Some fd -> Some fd
             | None -> lookupFdefViaIDFromModules lm' i0)
  
  (** val lookupFdefViaIDFromSystem :
      LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.fdef option **)
  
  let lookupFdefViaIDFromSystem s i0 =
    lookupFdefViaIDFromModules s i0
  
  (** val lookupTypViaIDFromCmd :
      LLVMsyntax.cmd -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromCmd i0 id0 =
    match getCmdTyp i0 with
      | Some t0 ->
          if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 (getCmdID i0)
          then Some t0
          else None
      | None -> None
  
  (** val lookupTypViaIDFromCmds :
      LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaIDFromCmds li id0 =
    match li with
      | [] -> None
      | i0::li' ->
          (match lookupTypViaIDFromCmd i0 id0 with
             | Some t0 -> Some t0
             | None -> lookupTypViaIDFromCmds li' id0)
  
  (** val lookupTypViaIDFromPhiNode :
      LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromPhiNode i0 id0 =
    if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 (getPhiNodeID i0)
    then Some (getPhiNodeTyp i0)
    else None
  
  (** val lookupTypViaIDFromPhiNodes :
      LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaIDFromPhiNodes li id0 =
    match li with
      | [] -> None
      | i0::li' ->
          (match lookupTypViaIDFromPhiNode i0 id0 with
             | Some t0 -> Some t0
             | None -> lookupTypViaIDFromPhiNodes li' id0)
  
  (** val lookupTypViaIDFromTerminator :
      LLVMsyntax.terminator -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromTerminator i0 id0 =
    if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 (getTerminatorID i0)
    then Some (getTerminatorTyp i0)
    else None
  
  (** val lookupTypViaIDFromBlock :
      LLVMsyntax.block -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromBlock b id0 =
    let LLVMsyntax.Coq_block_intro (l0, ps, cs, t0) = b in
    (match lookupTypViaIDFromPhiNodes ps id0 with
       | Some t1 -> Some t1
       | None ->
           (match lookupTypViaIDFromCmds cs id0 with
              | Some t1 -> Some t1
              | None -> lookupTypViaIDFromTerminator t0 id0))
  
  (** val lookupTypViaIDFromBlocks :
      LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaIDFromBlocks lb id0 =
    match lb with
      | [] -> None
      | b::lb' ->
          (match lookupTypViaIDFromBlock b id0 with
             | Some t0 -> Some t0
             | None -> lookupTypViaIDFromBlocks lb' id0)
  
  (** val lookupTypViaIDFromFdef :
      LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromFdef fd id0 =
    let LLVMsyntax.Coq_fdef_intro (f, lb) = fd in
    lookupTypViaIDFromBlocks lb id0
  
  (** val lookupTypViaIDFromProduct :
      LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromProduct p id0 =
    match p with
      | LLVMsyntax.Coq_product_gvar g ->
          let LLVMsyntax.Coq_gvar_intro (id1, t0, c, a) = g in
          if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 id1
          then Some t0
          else None
      | LLVMsyntax.Coq_product_fdec f -> None
      | LLVMsyntax.Coq_product_fdef fd -> lookupTypViaIDFromFdef fd id0
  
  (** val lookupTypViaIDFromProducts :
      LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaIDFromProducts lp id0 =
    match lp with
      | [] -> None
      | p::lp' ->
          (match lookupTypViaIDFromProduct p id0 with
             | Some t0 -> Some t0
             | None -> lookupTypViaIDFromProducts lp' id0)
  
  (** val lookupTypViaIDFromModule :
      LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromModule m id0 =
    let LLVMsyntax.Coq_module_intro (os, ps) = m in
    lookupTypViaIDFromProducts ps id0
  
  (** val lookupTypViaIDFromModules :
      LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaIDFromModules lm id0 =
    match lm with
      | [] -> None
      | m::lm' ->
          (match lookupTypViaIDFromModule m id0 with
             | Some t0 -> Some t0
             | None -> lookupTypViaIDFromModules lm' id0)
  
  (** val lookupTypViaIDFromSystem :
      LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromSystem s id0 =
    lookupTypViaIDFromModules s id0
  
  type l2block = (LLVMsyntax.l*LLVMsyntax.block) list
  
  (** val genLabel2Block_block : LLVMsyntax.block -> l2block **)
  
  let genLabel2Block_block b = match b with
    | LLVMsyntax.Coq_block_intro (l0, p, c, t0) -> (l0,b)::[]
  
  (** val genLabel2Block_blocks : LLVMsyntax.blocks -> l2block **)
  
  let rec genLabel2Block_blocks = function
    | [] -> []
    | b::bs' -> app (genLabel2Block_block b) (genLabel2Block_blocks bs')
  
  (** val genLabel2Block_fdef : LLVMsyntax.fdef -> l2block **)
  
  let genLabel2Block_fdef = function
    | LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) ->
        genLabel2Block_blocks blocks0
  
  (** val genLabel2Block_product : LLVMsyntax.product -> l2block **)
  
  let rec genLabel2Block_product = function
    | LLVMsyntax.Coq_product_fdef f -> genLabel2Block_fdef f
    | _ -> []
  
  (** val genLabel2Block_products : LLVMsyntax.products -> l2block **)
  
  let rec genLabel2Block_products = function
    | [] -> []
    | p::ps' -> app (genLabel2Block_product p) (genLabel2Block_products ps')
  
  (** val genLabel2Block : LLVMsyntax.coq_module -> l2block **)
  
  let genLabel2Block = function
    | LLVMsyntax.Coq_module_intro (os, ps) -> genLabel2Block_products ps
  
  (** val getEntryOfFdef : LLVMsyntax.fdef -> LLVMsyntax.block option **)
  
  let getEntryOfFdef = function
    | LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) ->
        (match blocks0 with
           | [] -> None
           | b::blocks' -> Some b)
  
  (** val getNonEntryOfFdef : LLVMsyntax.fdef -> LLVMsyntax.blocks **)
  
  let getNonEntryOfFdef = function
    | LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) ->
        (match blocks0 with
           | [] -> []
           | b::blocks' -> blocks')
  
  (** val lookupBlockViaLabelFromFdef :
      LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.block option **)
  
  let lookupBlockViaLabelFromFdef f l0 =
    lookupAL (genLabel2Block_fdef f) l0
  
  (** val lookupBlockViaLabelFromModule :
      LLVMsyntax.coq_module -> LLVMsyntax.l -> LLVMsyntax.block option **)
  
  let lookupBlockViaLabelFromModule m l0 =
    lookupAL (genLabel2Block m) l0
  
  (** val lookupBlockViaLabelFromSystem :
      LLVMsyntax.system -> LLVMsyntax.l -> LLVMsyntax.block option **)
  
  let rec lookupBlockViaLabelFromSystem s l0 =
    match s with
      | [] -> None
      | m::s' ->
          (match lookupAL (genLabel2Block m) l0 with
             | Some b -> Some b
             | None -> lookupBlockViaLabelFromSystem s' l0)
  
  (** val getLabelsFromBlocks : LLVMsyntax.blocks -> LLVMsyntax.ls **)
  
  let rec getLabelsFromBlocks = function
    | [] -> lempty_set
    | b::lb' ->
        let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
        lset_add l0 (getLabelsFromBlocks lb')
  
  (** val mergeInsnUseDef :
      LLVMsyntax.usedef_id -> LLVMsyntax.usedef_id -> LLVMsyntax.usedef_id **)
  
  let mergeInsnUseDef udi1 udi2 i0 =
    app (udi1 i0) (udi2 i0)
  
  (** val mergeBlockUseDef :
      LLVMsyntax.usedef_block -> LLVMsyntax.usedef_block ->
      LLVMsyntax.usedef_block **)
  
  let mergeBlockUseDef udb1 udb2 b =
    app (udb1 b) (udb2 b)
  
  (** val genIdUseDef_id_uses_value :
      LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_id_uses_value v id0 id' =
    match getValueID v with
      | Some id1 ->
          if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id' id1
          then id0::[]
          else []
      | None -> []
  
  (** val genIdUseDef_id_uses_id :
      LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_id_uses_id id0 id1 id' =
    if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id' id0 then id1::[] else []
  
  (** val genIdUseDef_id_uses_params :
      LLVMsyntax.params -> LLVMsyntax.id -> LLVMsyntax.usedef_id **)
  
  let rec genIdUseDef_id_uses_params ps id0 =
    match ps with
      | [] -> (fun x -> [])
      | p::ps' ->
          let t0,v = p in
          mergeInsnUseDef (genIdUseDef_id_uses_value v id0)
            (genIdUseDef_id_uses_params ps' id0)
  
  (** val genIdUseDef_cmd_uses_value :
      LLVMsyntax.value -> LLVMsyntax.cmd -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_cmd_uses_value v i0 =
    genIdUseDef_id_uses_value v (getCmdID i0)
  
  (** val genIdUseDef_terminator_uses_value :
      LLVMsyntax.value -> LLVMsyntax.terminator -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_terminator_uses_value v i0 =
    genIdUseDef_id_uses_value v (getTerminatorID i0)
  
  (** val genIdUseDef_phinode_uses_value :
      LLVMsyntax.value -> LLVMsyntax.phinode -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_phinode_uses_value v i0 =
    genIdUseDef_id_uses_value v (getPhiNodeID i0)
  
  (** val genIdUseDef_cmd_uses_id :
      LLVMsyntax.id -> LLVMsyntax.cmd -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_cmd_uses_id id0 i0 =
    genIdUseDef_id_uses_id id0 (getCmdID i0)
  
  (** val genIdUseDef_terminator_uses_id :
      LLVMsyntax.id -> LLVMsyntax.terminator -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_terminator_uses_id id0 i0 =
    genIdUseDef_id_uses_id id0 (getTerminatorID i0)
  
  (** val genIdUseDef_phinode_uses_id :
      LLVMsyntax.id -> LLVMsyntax.phinode -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_phinode_uses_id id0 i0 =
    genIdUseDef_id_uses_id id0 (getPhiNodeID i0)
  
  (** val genIdUseDef_cmd_uses_params :
      LLVMsyntax.params -> LLVMsyntax.cmd -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_cmd_uses_params ps i0 =
    genIdUseDef_id_uses_params ps (getCmdID i0)
  
  (** val genIdUseDef_terminator_uses_params :
      LLVMsyntax.params -> LLVMsyntax.terminator -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_terminator_uses_params ps i0 =
    genIdUseDef_id_uses_params ps (getTerminatorID i0)
  
  (** val genIdUseDef_phinode_uses_params :
      LLVMsyntax.params -> LLVMsyntax.phinode -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_phinode_uses_params ps i0 =
    genIdUseDef_id_uses_params ps (getPhiNodeID i0)
  
  (** val genIdUseDef_cmd : LLVMsyntax.cmd -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_cmd i0 = match i0 with
    | LLVMsyntax.Coq_insn_bop (id0, b, sz0, v1, v2) ->
        mergeInsnUseDef (genIdUseDef_id_uses_value v1 id0)
          (genIdUseDef_id_uses_value v2 id0)
    | LLVMsyntax.Coq_insn_extractvalue (id0, typ0, value0, l0) ->
        genIdUseDef_id_uses_value value0 id0
    | LLVMsyntax.Coq_insn_insertvalue (id0, typs, v0, typ1, v1, c2) ->
        mergeInsnUseDef (genIdUseDef_cmd_uses_value v0 i0)
          (genIdUseDef_id_uses_value v1 id0)
    | LLVMsyntax.Coq_insn_free (id0, typ0, v) ->
        genIdUseDef_id_uses_value v id0
    | LLVMsyntax.Coq_insn_load (id0, typ1, v1, a) ->
        genIdUseDef_id_uses_value v1 id0
    | LLVMsyntax.Coq_insn_store (id0, typ1, v1, v2, a) ->
        mergeInsnUseDef (genIdUseDef_id_uses_value v1 id0)
          (genIdUseDef_id_uses_value v2 id0)
    | LLVMsyntax.Coq_insn_gep (id0, i1, typ0, value0, l0) ->
        genIdUseDef_id_uses_value value0 id0
    | LLVMsyntax.Coq_insn_ext (id0, e, sz1, v1, sz2) ->
        genIdUseDef_id_uses_value v1 id0
    | LLVMsyntax.Coq_insn_cast (id0, c, typ1, v1, typ2) ->
        genIdUseDef_id_uses_value v1 id0
    | LLVMsyntax.Coq_insn_icmp (id0, cond0, typ0, v1, v2) ->
        mergeInsnUseDef (genIdUseDef_id_uses_value v1 id0)
          (genIdUseDef_id_uses_value v2 id0)
    | LLVMsyntax.Coq_insn_select (id0, v0, typ0, v1, v2) ->
        mergeInsnUseDef (genIdUseDef_id_uses_value v0 id0)
          (mergeInsnUseDef (genIdUseDef_id_uses_value v1 id0)
            (genIdUseDef_id_uses_value v2 id0))
    | LLVMsyntax.Coq_insn_call (id0, n, t0, typ0, id1, paraml) ->
        mergeInsnUseDef (genIdUseDef_id_uses_id id1 id0)
          (genIdUseDef_id_uses_params paraml id0)
    | _ -> (fun x -> [])
  
  (** val genIdUseDef_terminator :
      LLVMsyntax.terminator -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_terminator = function
    | LLVMsyntax.Coq_insn_return (id0, t0, v) ->
        genIdUseDef_id_uses_value v id0
    | LLVMsyntax.Coq_insn_br (id0, v, l1, l2) ->
        genIdUseDef_id_uses_value v id0
    | _ -> (fun x -> [])
  
  (** val genIdUseDef_id_uses_idls :
      LLVMsyntax.list_value_l -> LLVMsyntax.id -> LLVMsyntax.usedef_id **)
  
  let rec genIdUseDef_id_uses_idls idls id0 =
    match idls with
      | LLVMsyntax.Nil_list_value_l -> (fun x -> [])
      | LLVMsyntax.Cons_list_value_l (v, l0, idls') ->
          (match v with
             | LLVMsyntax.Coq_value_id id1 ->
                 mergeInsnUseDef (genIdUseDef_id_uses_id id1 id0)
                   (genIdUseDef_id_uses_idls idls' id0)
             | LLVMsyntax.Coq_value_const c ->
                 genIdUseDef_id_uses_idls idls' id0)
  
  (** val genIdUseDef_phinode :
      LLVMsyntax.phinode -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_phinode = function
    | LLVMsyntax.Coq_insn_phi (id0, typ0, idls) ->
        genIdUseDef_id_uses_idls idls id0
  
  (** val genIdUseDef_cmds : LLVMsyntax.cmds -> LLVMsyntax.usedef_id **)
  
  let rec genIdUseDef_cmds = function
    | [] -> (fun x -> [])
    | i0::is' -> mergeInsnUseDef (genIdUseDef_cmd i0) (genIdUseDef_cmds is')
  
  (** val genIdUseDef_phinodes :
      LLVMsyntax.phinodes -> LLVMsyntax.usedef_id **)
  
  let rec genIdUseDef_phinodes = function
    | [] -> (fun x -> [])
    | i0::is' ->
        mergeInsnUseDef (genIdUseDef_phinode i0) (genIdUseDef_phinodes is')
  
  (** val genIdUseDef_block : LLVMsyntax.block -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_block = function
    | LLVMsyntax.Coq_block_intro (l0, ps, cs, t0) ->
        mergeInsnUseDef (genIdUseDef_phinodes ps)
          (mergeInsnUseDef (genIdUseDef_cmds cs) (genIdUseDef_terminator t0))
  
  (** val genIdUseDef_blocks : LLVMsyntax.blocks -> LLVMsyntax.usedef_id **)
  
  let rec genIdUseDef_blocks = function
    | [] -> (fun x -> [])
    | b::bs' ->
        mergeInsnUseDef (genIdUseDef_block b) (genIdUseDef_blocks bs')
  
  (** val genIdUseDef_fdef : LLVMsyntax.fdef -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_fdef = function
    | LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) ->
        genIdUseDef_blocks blocks0
  
  (** val genIdUseDef_product :
      LLVMsyntax.product -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_product = function
    | LLVMsyntax.Coq_product_fdef f -> genIdUseDef_fdef f
    | _ -> (fun x -> [])
  
  (** val genIdUseDef_products :
      LLVMsyntax.products -> LLVMsyntax.usedef_id **)
  
  let rec genIdUseDef_products = function
    | [] -> (fun x -> [])
    | p::ps' ->
        mergeInsnUseDef (genIdUseDef_product p) (genIdUseDef_products ps')
  
  (** val genIdUseDef : LLVMsyntax.coq_module -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef = function
    | LLVMsyntax.Coq_module_intro (os, ps) -> genIdUseDef_products ps
  
  (** val getIdUseDef :
      LLVMsyntax.usedef_id -> LLVMsyntax.id -> LLVMsyntax.id list **)
  
  let getIdUseDef udi i0 =
    udi i0
  
  (** val getBlockLabel : LLVMsyntax.block -> LLVMsyntax.l **)
  
  let getBlockLabel = function
    | LLVMsyntax.Coq_block_intro (l0, p, c, t0) -> l0
  
  (** val genBlockUseDef_label :
      LLVMsyntax.l -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_label l0 b b' =
    if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) (getBlockLabel b') l0
    then b::[]
    else []
  
  (** val genBlockUseDef_phi_cases :
      LLVMsyntax.list_value_l -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_phi_cases ps b =
    match ps with
      | LLVMsyntax.Nil_list_value_l -> (fun x -> [])
      | LLVMsyntax.Cons_list_value_l (v, l0, ps') ->
          mergeBlockUseDef (genBlockUseDef_label l0 b)
            (genBlockUseDef_phi_cases ps' b)
  
  (** val genBlockUseDef_cmd :
      LLVMsyntax.cmd -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_cmd i0 b x =
    []
  
  (** val genBlockUseDef_terminator :
      LLVMsyntax.terminator -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_terminator i0 b =
    match i0 with
      | LLVMsyntax.Coq_insn_br (i1, v, l1, l2) ->
          mergeBlockUseDef (genBlockUseDef_label l1 b)
            (genBlockUseDef_label l2 b)
      | LLVMsyntax.Coq_insn_br_uncond (i1, l0) -> genBlockUseDef_label l0 b
      | _ -> (fun x -> [])
  
  (** val genBlockUseDef_phinode :
      LLVMsyntax.phinode -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_phinode i0 b =
    let LLVMsyntax.Coq_insn_phi (id0, typ0, idls) = i0 in
    genBlockUseDef_phi_cases idls b
  
  (** val genBlockUseDef_cmds :
      LLVMsyntax.cmds -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_cmds is b =
    match is with
      | [] -> (fun x -> [])
      | i0::is' ->
          mergeBlockUseDef (genBlockUseDef_cmd i0 b)
            (genBlockUseDef_cmds is' b)
  
  (** val genBlockUseDef_phinodes :
      LLVMsyntax.phinodes -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_phinodes is b =
    match is with
      | [] -> (fun x -> [])
      | i0::is' ->
          mergeBlockUseDef (genBlockUseDef_phinode i0 b)
            (genBlockUseDef_phinodes is' b)
  
  (** val genBlockUseDef_block :
      LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_block b = match b with
    | LLVMsyntax.Coq_block_intro (l0, ps, cs, t0) ->
        mergeBlockUseDef (genBlockUseDef_phinodes ps b)
          (mergeBlockUseDef (genBlockUseDef_cmds cs b)
            (genBlockUseDef_terminator t0 b))
  
  (** val genBlockUseDef_blocks :
      LLVMsyntax.blocks -> LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_blocks = function
    | [] -> (fun x -> [])
    | b::bs' ->
        mergeBlockUseDef (genBlockUseDef_blocks bs') (genBlockUseDef_block b)
  
  (** val genBlockUseDef_fdef :
      LLVMsyntax.fdef -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_fdef = function
    | LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) ->
        genBlockUseDef_blocks blocks0
  
  (** val genBlockUseDef_product :
      LLVMsyntax.product -> LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_product = function
    | LLVMsyntax.Coq_product_fdef f -> genBlockUseDef_fdef f
    | _ -> (fun x -> [])
  
  (** val genBlockUseDef_products :
      LLVMsyntax.products -> LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_products = function
    | [] -> (fun x -> [])
    | p::ps' ->
        mergeBlockUseDef (genBlockUseDef_products ps')
          (genBlockUseDef_product p)
  
  (** val genBlockUseDef :
      LLVMsyntax.coq_module -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef = function
    | LLVMsyntax.Coq_module_intro (os, ps) -> genBlockUseDef_products ps
  
  (** val getBlockUseDef :
      LLVMsyntax.usedef_block -> LLVMsyntax.block -> LLVMsyntax.block list **)
  
  let getBlockUseDef udb b =
    udb b
  
  (** val getTerminator : LLVMsyntax.block -> LLVMsyntax.terminator **)
  
  let getTerminator = function
    | LLVMsyntax.Coq_block_intro (l0, p, c, t0) -> t0
  
  (** val getLabelsFromSwitchCases :
      (LLVMsyntax.const*LLVMsyntax.l) list -> LLVMsyntax.ls **)
  
  let rec getLabelsFromSwitchCases = function
    | [] -> lempty_set
    | p::cs' -> let c,l0 = p in lset_add l0 (getLabelsFromSwitchCases cs')
  
  (** val getLabelsFromTerminator :
      LLVMsyntax.terminator -> LLVMsyntax.ls **)
  
  let getLabelsFromTerminator = function
    | LLVMsyntax.Coq_insn_br (i1, v, l1, l2) ->
        lset_add l1 (lset_add l2 lempty_set)
    | LLVMsyntax.Coq_insn_br_uncond (i1, l0) -> lset_add l0 lempty_set
    | _ -> empty_set
  
  (** val getBlocksFromLabels :
      LLVMsyntax.ls -> l2block -> LLVMsyntax.blocks **)
  
  let rec getBlocksFromLabels ls0 l2b =
    match ls0 with
      | [] -> []
      | l0::ls0' ->
          (match lookupAL l2b l0 with
             | Some b -> b::(getBlocksFromLabels ls0' l2b)
             | None -> getBlocksFromLabels ls0' l2b)
  
  (** val succOfBlock :
      LLVMsyntax.block -> LLVMsyntax.coq_module -> LLVMsyntax.blocks **)
  
  let succOfBlock b m =
    getBlocksFromLabels (getLabelsFromTerminator (getTerminator b))
      (genLabel2Block m)
  
  (** val predOfBlock :
      LLVMsyntax.block -> LLVMsyntax.usedef_block -> LLVMsyntax.blocks **)
  
  let predOfBlock b udb =
    udb b
  
  (** val hasSinglePredecessor :
      LLVMsyntax.block -> LLVMsyntax.usedef_block -> bool **)
  
  let hasSinglePredecessor b udb =
    if eq_nat_dec (length (predOfBlock b udb)) (S O) then true else false
  
  (** val genLabelsFromBlocks : LLVMsyntax.blocks -> LLVMsyntax.ls **)
  
  let rec genLabelsFromBlocks = function
    | [] -> lempty_set
    | b::bs' ->
        let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
        lset_union (EnvImpl.one l0) (genLabelsFromBlocks bs')
  
  (** val genLabelsFromFdef : LLVMsyntax.fdef -> LLVMsyntax.ls **)
  
  let genLabelsFromFdef = function
    | LLVMsyntax.Coq_fdef_intro (f0, bs) -> genLabelsFromBlocks bs
  
  (** val inputFromPred :
      LLVMsyntax.blocks -> LLVMsyntax.dt -> LLVMsyntax.ls **)
  
  let rec inputFromPred bs output =
    match bs with
      | [] -> lempty_set
      | b::bs' ->
          let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
          lset_union (output l0) (inputFromPred bs' output)
  
  (** val outputFromInput :
      LLVMsyntax.block -> LLVMsyntax.ls -> LLVMsyntax.ls **)
  
  let outputFromInput b input =
    let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in lset_add l0 input
  
  (** val update_dt :
      LLVMsyntax.dt -> LLVMsyntax.l -> LLVMsyntax.ls -> LLVMsyntax.dt **)
  
  let update_dt d1 l0 ls0 l1 =
    if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) l1 l0 then ls0 else d1 l1
  
  (** val inter_dt : LLVMsyntax.dt -> LLVMsyntax.dt -> LLVMsyntax.dt **)
  
  let inter_dt d1 d2 l0 =
    lset_inter (d1 l0) (d2 l0)
  
  (** val genDominatorTree_blocks_innerloop :
      LLVMsyntax.blocks -> LLVMsyntax.usedef_block -> LLVMsyntax.dt ->
      LLVMsyntax.dt **)
  
  let rec genDominatorTree_blocks_innerloop bs udb output =
    match bs with
      | [] -> output
      | b::bs' ->
          let LLVMsyntax.Coq_block_intro (l0, ps, cs, t0) = b in
          genDominatorTree_blocks_innerloop bs' udb
            (update_dt output l0
              (outputFromInput (LLVMsyntax.Coq_block_intro (l0, ps, cs, t0))
                (inputFromPred
                  (predOfBlock (LLVMsyntax.Coq_block_intro (l0, ps, cs, t0))
                    udb) output)))
  
  (** val eq_dt :
      LLVMsyntax.dt -> LLVMsyntax.dt -> LLVMsyntax.blocks -> bool **)
  
  let rec eq_dt d0 d1 = function
    | [] -> true
    | b::bs' ->
        let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
        if lset_eq (d0 l0) (d1 l0) then eq_dt d0 d1 bs' else false
  
  (** val sizeOfDT : LLVMsyntax.blocks -> LLVMsyntax.dt -> nat **)
  
  let rec sizeOfDT bs output =
    match bs with
      | [] -> O
      | b::bs' ->
          let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
          plus (length (output l0)) (sizeOfDT bs' output)
  
  (** val size : (LLVMsyntax.blocks*LLVMsyntax.dt) -> nat **)
  
  let size = function
    | bs,output -> sizeOfDT bs output
  
  (** val genDominatorTree_blocks_F :
      ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.dt) -> (LLVMsyntax.blocks*LLVMsyntax.dt) ->
      LLVMsyntax.usedef_block -> LLVMsyntax.dt **)
  
  let genDominatorTree_blocks_F genDominatorTree_blocks0 arg0 udb =
    let bs,output = arg0 in
    if eq_dt output (genDominatorTree_blocks_innerloop bs udb output) bs
    then genDominatorTree_blocks_innerloop bs udb output
    else genDominatorTree_blocks0
           (bs,(genDominatorTree_blocks_innerloop bs udb output)) udb
  
  (** val genDominatorTree_blocks_terminate :
      (LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.dt **)
  
  let rec genDominatorTree_blocks_terminate arg0 udb =
    let bs,output = arg0 in
    if eq_dt output (genDominatorTree_blocks_innerloop bs udb output) bs
    then genDominatorTree_blocks_innerloop bs udb output
    else genDominatorTree_blocks_terminate
           (bs,(genDominatorTree_blocks_innerloop bs udb output)) udb
  
  (** val genDominatorTree_blocks :
      (LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.dt **)
  
  let genDominatorTree_blocks x x0 =
    genDominatorTree_blocks_terminate x x0
  
  type coq_R_genDominatorTree_blocks =
    | R_genDominatorTree_blocks_0 of (LLVMsyntax.blocks*LLVMsyntax.dt)
       * LLVMsyntax.usedef_block * LLVMsyntax.blocks * 
       LLVMsyntax.dt * LLVMsyntax.dt
    | R_genDominatorTree_blocks_1 of (LLVMsyntax.blocks*LLVMsyntax.dt)
       * LLVMsyntax.usedef_block * LLVMsyntax.blocks * 
       LLVMsyntax.dt * LLVMsyntax.dt * LLVMsyntax.dt
       * coq_R_genDominatorTree_blocks
  
  (** val coq_R_genDominatorTree_blocks_rect :
      ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __
      -> 'a1) -> ((LLVMsyntax.blocks*LLVMsyntax.dt) ->
      LLVMsyntax.usedef_block -> LLVMsyntax.blocks -> LLVMsyntax.dt -> __ ->
      LLVMsyntax.dt -> __ -> __ -> LLVMsyntax.dt ->
      coq_R_genDominatorTree_blocks -> 'a1 -> 'a1) ->
      (LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.dt -> coq_R_genDominatorTree_blocks -> 'a1 **)
  
  let rec coq_R_genDominatorTree_blocks_rect f f0 arg0 udb d = function
    | R_genDominatorTree_blocks_0 (arg1, udb0, bs, output, output') ->
        f arg1 udb0 bs output __ output' __ __
    | R_genDominatorTree_blocks_1
        (arg1, udb0, bs, output, output', res, r0) ->
        f0 arg1 udb0 bs output __ output' __ __ res r0
          (coq_R_genDominatorTree_blocks_rect f f0 (bs,output') udb0 res r0)
  
  (** val coq_R_genDominatorTree_blocks_rec :
      ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __
      -> 'a1) -> ((LLVMsyntax.blocks*LLVMsyntax.dt) ->
      LLVMsyntax.usedef_block -> LLVMsyntax.blocks -> LLVMsyntax.dt -> __ ->
      LLVMsyntax.dt -> __ -> __ -> LLVMsyntax.dt ->
      coq_R_genDominatorTree_blocks -> 'a1 -> 'a1) ->
      (LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.dt -> coq_R_genDominatorTree_blocks -> 'a1 **)
  
  let rec coq_R_genDominatorTree_blocks_rec f f0 arg0 udb d = function
    | R_genDominatorTree_blocks_0 (arg1, udb0, bs, output, output') ->
        f arg1 udb0 bs output __ output' __ __
    | R_genDominatorTree_blocks_1
        (arg1, udb0, bs, output, output', res, r0) ->
        f0 arg1 udb0 bs output __ output' __ __ res r0
          (coq_R_genDominatorTree_blocks_rec f f0 (bs,output') udb0 res r0)
  
  (** val genDominatorTree_blocks_rect :
      ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __
      -> 'a1) -> ((LLVMsyntax.blocks*LLVMsyntax.dt) ->
      LLVMsyntax.usedef_block -> LLVMsyntax.blocks -> LLVMsyntax.dt -> __ ->
      LLVMsyntax.dt -> __ -> __ -> 'a1 -> 'a1) ->
      (LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block -> 'a1 **)
  
  let rec genDominatorTree_blocks_rect f f0 arg0 udb =
    let f1 = f0 arg0 udb in
    let f2 = f arg0 udb in
    let b,d = arg0 in
    let f3 = f2 b d __ in
    let f4 =
      let output' = genDominatorTree_blocks_innerloop b udb d in
      f3 output' __
    in
    let f5 = f1 b d __ in
    let f6 =
      let output' = genDominatorTree_blocks_innerloop b udb d in
      f5 output' __
    in
    if eq_dt d (genDominatorTree_blocks_innerloop b udb d) b
    then f4 __
    else let f7 = f6 __ in
         let hrec =
           genDominatorTree_blocks_rect f f0
             (b,(genDominatorTree_blocks_innerloop b udb d)) udb
         in
         f7 hrec
  
  (** val genDominatorTree_blocks_rec :
      ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __
      -> 'a1) -> ((LLVMsyntax.blocks*LLVMsyntax.dt) ->
      LLVMsyntax.usedef_block -> LLVMsyntax.blocks -> LLVMsyntax.dt -> __ ->
      LLVMsyntax.dt -> __ -> __ -> 'a1 -> 'a1) ->
      (LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block -> 'a1 **)
  
  let genDominatorTree_blocks_rec =
    genDominatorTree_blocks_rect
  
  (** val coq_R_genDominatorTree_blocks_correct :
      (LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.dt -> coq_R_genDominatorTree_blocks **)
  
  let coq_R_genDominatorTree_blocks_correct x x0 res =
    genDominatorTree_blocks_rect (fun y y0 y1 y2 _ y4 _ _ z0 _ ->
      R_genDominatorTree_blocks_0 (y, y0, y1, y2, y4))
      (fun y y0 y1 y2 _ y4 _ _ y7 z0 _ -> R_genDominatorTree_blocks_1 (y, y0,
      y1, y2, y4, (genDominatorTree_blocks (y1,y4) y0),
      (y7 (genDominatorTree_blocks (y1,y4) y0) __))) x x0 res __
  
  (** val initialize_genDominatorTree_blocks :
      LLVMsyntax.blocks -> LLVMsyntax.ls -> LLVMsyntax.dt -> LLVMsyntax.dt **)
  
  let rec initialize_genDominatorTree_blocks bs u d0 =
    match bs with
      | [] -> d0
      | b::bs' ->
          let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
          initialize_genDominatorTree_blocks bs' u (update_dt d0 l0 u)
  
  (** val genEmptyDT : LLVMsyntax.dt **)
  
  let genEmptyDT x =
    []
  
  (** val initialize_genDominatorTree_entry :
      LLVMsyntax.fdef -> LLVMsyntax.dt **)
  
  let initialize_genDominatorTree_entry f =
    match getEntryOfFdef f with
      | Some b ->
          let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
          update_dt genEmptyDT l0 (lset_single l0)
      | None -> genEmptyDT
  
  (** val initialize_genDominatorTree :
      LLVMsyntax.fdef -> LLVMsyntax.ls -> LLVMsyntax.dt **)
  
  let initialize_genDominatorTree f u =
    initialize_genDominatorTree_blocks (getNonEntryOfFdef f) u
      (initialize_genDominatorTree_entry f)
  
  (** val genDominatorTree :
      LLVMsyntax.fdef -> LLVMsyntax.coq_module -> LLVMsyntax.dt **)
  
  let genDominatorTree f m =
    let LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) = f in
    genDominatorTree_blocks
      (blocks0,(initialize_genDominatorTree f (genLabelsFromFdef f)))
      (genBlockUseDef m)
  
  (** val blockDominatesB :
      LLVMsyntax.dt -> LLVMsyntax.block -> LLVMsyntax.block -> bool **)
  
  let blockDominatesB d b1 b2 =
    let LLVMsyntax.Coq_block_intro (l1, p, c, t0) = b1 in
    let LLVMsyntax.Coq_block_intro (l2, p0, c0, t1) = b2 in
    lset_mem l2 (d l1)
  
  (** val isReachableFromEntryB :
      LLVMsyntax.fdef_info -> LLVMsyntax.block -> bool **)
  
  let isReachableFromEntryB fi b =
    let f,d = fi in
    (match getEntryOfFdef f with
       | Some be -> blockDominatesB d be b
       | None -> false)
  
  (** val isPointerTypB : LLVMsyntax.typ -> bool **)
  
  let isPointerTypB = function
    | LLVMsyntax.Coq_typ_pointer t1 -> true
    | _ -> false
  
  (** val isArrayTypB : LLVMsyntax.typ -> bool **)
  
  let isArrayTypB = function
    | LLVMsyntax.Coq_typ_array (s, t1) -> true
    | _ -> false
  
  (** val isReturnInsnB : LLVMsyntax.terminator -> bool **)
  
  let isReturnInsnB = function
    | LLVMsyntax.Coq_insn_return (i1, t0, v) -> true
    | LLVMsyntax.Coq_insn_return_void i1 -> true
    | _ -> false
  
  (** val _isCallInsnB : LLVMsyntax.cmd -> bool **)
  
  let _isCallInsnB = function
    | LLVMsyntax.Coq_insn_call (i1, n, t0, t1, i2, p) -> true
    | _ -> false
  
  (** val isCallInsnB : LLVMsyntax.insn -> bool **)
  
  let isCallInsnB = function
    | LLVMsyntax.Coq_insn_cmd c -> _isCallInsnB c
    | _ -> false
  
  (** val isNotValidReturnTypB : LLVMsyntax.typ -> bool **)
  
  let isNotValidReturnTypB = function
    | LLVMsyntax.Coq_typ_label -> true
    | LLVMsyntax.Coq_typ_metadata -> true
    | _ -> false
  
  (** val isValidReturnTypB : LLVMsyntax.typ -> bool **)
  
  let isValidReturnTypB t0 =
    negb (isNotValidReturnTypB t0)
  
  (** val isNotFirstClassTypB : LLVMsyntax.typ -> bool **)
  
  let isNotFirstClassTypB = function
    | LLVMsyntax.Coq_typ_void -> true
    | LLVMsyntax.Coq_typ_function (t1, l0) -> true
    | _ -> false
  
  (** val isFirstClassTypB : LLVMsyntax.typ -> bool **)
  
  let isFirstClassTypB t0 =
    negb (isNotFirstClassTypB t0)
  
  (** val isValidArgumentTypB : LLVMsyntax.typ -> bool **)
  
  let isValidArgumentTypB t0 =
    isFirstClassTypB t0
  
  (** val isNotValidElementTypB : LLVMsyntax.typ -> bool **)
  
  let isNotValidElementTypB = function
    | LLVMsyntax.Coq_typ_void -> true
    | LLVMsyntax.Coq_typ_label -> true
    | LLVMsyntax.Coq_typ_metadata -> true
    | LLVMsyntax.Coq_typ_function (t1, l0) -> true
    | _ -> false
  
  (** val isValidElementTypB : LLVMsyntax.typ -> bool **)
  
  let isValidElementTypB t0 =
    negb (isNotValidElementTypB t0)
  
  (** val isBindingFdecB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingFdecB = function
    | LLVMsyntax.Coq_id_binding_fdec fdec0 -> true
    | _ -> false
  
  (** val isBindingGvarB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingGvarB = function
    | LLVMsyntax.Coq_id_binding_gvar g -> true
    | _ -> false
  
  (** val isBindingArgB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingArgB = function
    | LLVMsyntax.Coq_id_binding_arg arg0 -> true
    | _ -> false
  
  (** val isBindingCmdB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingCmdB = function
    | LLVMsyntax.Coq_id_binding_cmd c -> true
    | _ -> false
  
  (** val isBindingTerminatorB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingTerminatorB = function
    | LLVMsyntax.Coq_id_binding_terminator t0 -> true
    | _ -> false
  
  (** val isBindingPhiNodeB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingPhiNodeB = function
    | LLVMsyntax.Coq_id_binding_phinode p -> true
    | _ -> false
  
  (** val isBindingInsnB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingInsnB ib =
    if if isBindingCmdB ib then true else isBindingTerminatorB ib
    then true
    else isBindingPhiNodeB ib
  
  (** val isBindingFdec : LLVMsyntax.id_binding -> LLVMsyntax.fdec option **)
  
  let isBindingFdec = function
    | LLVMsyntax.Coq_id_binding_fdec f -> Some f
    | _ -> None
  
  (** val isBindingArg : LLVMsyntax.id_binding -> LLVMsyntax.arg option **)
  
  let isBindingArg = function
    | LLVMsyntax.Coq_id_binding_arg a -> Some a
    | _ -> None
  
  (** val isBindingGvar : LLVMsyntax.id_binding -> LLVMsyntax.gvar option **)
  
  let isBindingGvar = function
    | LLVMsyntax.Coq_id_binding_gvar g -> Some g
    | _ -> None
  
  (** val isBindingCmd : LLVMsyntax.id_binding -> LLVMsyntax.cmd option **)
  
  let isBindingCmd = function
    | LLVMsyntax.Coq_id_binding_cmd c -> Some c
    | _ -> None
  
  (** val isBindingPhiNode :
      LLVMsyntax.id_binding -> LLVMsyntax.phinode option **)
  
  let isBindingPhiNode = function
    | LLVMsyntax.Coq_id_binding_phinode p -> Some p
    | _ -> None
  
  (** val isBindingTerminator :
      LLVMsyntax.id_binding -> LLVMsyntax.terminator option **)
  
  let isBindingTerminator = function
    | LLVMsyntax.Coq_id_binding_terminator tmn -> Some tmn
    | _ -> None
  
  (** val isBindingInsn : LLVMsyntax.id_binding -> LLVMsyntax.insn option **)
  
  let isBindingInsn = function
    | LLVMsyntax.Coq_id_binding_cmd c -> Some (LLVMsyntax.Coq_insn_cmd c)
    | LLVMsyntax.Coq_id_binding_phinode p -> Some
        (LLVMsyntax.Coq_insn_phinode p)
    | LLVMsyntax.Coq_id_binding_terminator tmn -> Some
        (LLVMsyntax.Coq_insn_terminator tmn)
    | _ -> None
  
  (** val getCmdsIDs : LLVMsyntax.cmd list -> LLVMsyntax.ids **)
  
  let rec getCmdsIDs = function
    | [] -> []
    | c::cs' -> (getCmdID c)::(getCmdsIDs cs')
  
  (** val getPhiNodesIDs : LLVMsyntax.phinode list -> LLVMsyntax.ids **)
  
  let rec getPhiNodesIDs = function
    | [] -> []
    | p::ps' -> (getPhiNodeID p)::(getPhiNodesIDs ps')
  
  (** val getBlockIDs : LLVMsyntax.block -> LLVMsyntax.ids **)
  
  let getBlockIDs = function
    | LLVMsyntax.Coq_block_intro (l0, ps, cs, t0) ->
        app (getPhiNodesIDs ps)
          (app (getCmdsIDs cs) ((getTerminatorID t0)::[]))
  
  (** val getBlocksIDs : LLVMsyntax.block list -> LLVMsyntax.ids **)
  
  let rec getBlocksIDs = function
    | [] -> []
    | b::bs' -> app (getBlockIDs b) (getBlocksIDs bs')
  
  (** val getBlocksLabels : LLVMsyntax.block list -> LLVMsyntax.ls **)
  
  let rec getBlocksLabels = function
    | [] -> []
    | y::bs' ->
        let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = y in
        l0::(getBlocksLabels bs')
  
  (** val getProductID : LLVMsyntax.product -> LLVMsyntax.id **)
  
  let getProductID = function
    | LLVMsyntax.Coq_product_gvar g -> getGvarID g
    | LLVMsyntax.Coq_product_fdec f -> getFdecID f
    | LLVMsyntax.Coq_product_fdef f -> getFdefID f
  
  (** val getProductsIDs : LLVMsyntax.product list -> LLVMsyntax.ids **)
  
  let rec getProductsIDs = function
    | [] -> []
    | p::ps' -> (getProductID p)::(getProductsIDs ps')
  
  (** val sumbool2bool : bool -> bool **)
  
  let sumbool2bool = function
    | true -> true
    | false -> false
  
  type typ_dec_prop = LLVMsyntax.typ -> bool
  
  type list_typ_dec_prop = LLVMsyntax.list_typ -> bool
  
  (** val typ_mutrec_dec :
      (LLVMsyntax.typ -> typ_dec_prop)*(LLVMsyntax.list_typ ->
      list_typ_dec_prop) **)
  
  let typ_mutrec_dec =
    LLVMsyntax.typ_mutrec (fun s t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_int s0 -> sz_dec s s0
        | _ -> false) (fun t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_float -> true
        | _ -> false) (fun t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_double -> true
        | _ -> false) (fun t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_void -> true
        | _ -> false) (fun t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_label -> true
        | _ -> false) (fun t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_metadata -> true
        | _ -> false) (fun s t0 h t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_array (s0, t3) ->
            let s1 = h t3 in if s1 then sz_dec s s0 else false
        | _ -> false) (fun t0 h l0 h0 t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_function (t3, l1) ->
            let s = h t3 in if s then h0 l1 else false
        | _ -> false) (fun l0 h t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_struct l1 -> h l1
        | _ -> false) (fun t0 h t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_pointer t3 -> h t3
        | _ -> false) (fun lt2 ->
      match lt2 with
        | LLVMsyntax.Nil_list_typ -> true
        | LLVMsyntax.Cons_list_typ (t0, lt3) -> false) (fun t0 h l0 h0 lt2 ->
      match lt2 with
        | LLVMsyntax.Nil_list_typ -> false
        | LLVMsyntax.Cons_list_typ (t1, lt3) ->
            let s = h t1 in if s then h0 lt3 else false)
  
  (** val typ_dec : LLVMsyntax.typ -> LLVMsyntax.typ -> bool **)
  
  let typ_dec =
    let t0,l0 = typ_mutrec_dec in t0
  
  (** val list_typ_dec :
      LLVMsyntax.list_typ -> LLVMsyntax.list_typ -> bool **)
  
  let list_typ_dec =
    let t0,l0 = typ_mutrec_dec in l0
  
  type const_dec_prop = LLVMsyntax.const -> bool
  
  type list_const_dec_prop = LLVMsyntax.list_const -> bool
  
  (** val const_mutrec_dec :
      (LLVMsyntax.const -> const_dec_prop)*(LLVMsyntax.list_const ->
      list_const_dec_prop) **)
  
  let const_mutrec_dec =
    LLVMsyntax.const_mutrec (fun s i0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_int (s0, i1) ->
            let s1 = coq_INT_dec i0 i1 in if s1 then sz_dec s s0 else false
        | _ -> false) (fun t0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_undef t1 -> typ_dec t0 t1
        | _ -> false) (fun t0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_null t1 -> typ_dec t0 t1
        | _ -> false) (fun l0 h c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_arr l1 -> h l1
        | _ -> false) (fun l0 h c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_struct l1 -> h l1
        | _ -> false) (fun t0 i0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_gid (t1, i1) ->
            let s = typ_dec t0 t1 in if s then id_dec i0 i1 else false
        | _ -> false) (fun lc2 ->
      match lc2 with
        | LLVMsyntax.Nil_list_const -> true
        | LLVMsyntax.Cons_list_const (c, lc3) -> false) (fun c h l0 h0 lc2 ->
      match lc2 with
        | LLVMsyntax.Nil_list_const -> false
        | LLVMsyntax.Cons_list_const (c0, lc3) ->
            let s = h c0 in if s then h0 lc3 else false)
  
  (** val const_dec : LLVMsyntax.const -> LLVMsyntax.const -> bool **)
  
  let const_dec =
    let c,l0 = const_mutrec_dec in c
  
  (** val list_const_dec :
      LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool **)
  
  let list_const_dec =
    let c,l0 = const_mutrec_dec in l0
  
  (** val value_dec : LLVMsyntax.value -> LLVMsyntax.value -> bool **)
  
  let value_dec v1 v2 =
    match v1 with
      | LLVMsyntax.Coq_value_id x ->
          (match v2 with
             | LLVMsyntax.Coq_value_id i1 -> AtomImpl.eq_atom_dec x i1
             | LLVMsyntax.Coq_value_const c -> false)
      | LLVMsyntax.Coq_value_const x ->
          (match v2 with
             | LLVMsyntax.Coq_value_id i0 -> false
             | LLVMsyntax.Coq_value_const c0 -> const_dec x c0)
  
  (** val params_dec : LLVMsyntax.params -> LLVMsyntax.params -> bool **)
  
  let rec params_dec l0 p0 =
    match l0 with
      | [] -> (match p0 with
                 | [] -> true
                 | p::l1 -> false)
      | y::l1 ->
          (match p0 with
             | [] -> false
             | p::l2 ->
                 if let t0,v = y in
                    let t1,v0 = p in
                    let s = typ_dec t0 t1 in
                    if s then value_dec v v0 else false
                 then params_dec l1 l2
                 else false)
  
  (** val list_value_l_dec :
      LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l -> bool **)
  
  let rec list_value_l_dec l0 l2 =
    match l0 with
      | LLVMsyntax.Nil_list_value_l ->
          (match l2 with
             | LLVMsyntax.Nil_list_value_l -> true
             | LLVMsyntax.Cons_list_value_l (v, l1, l3) -> false)
      | LLVMsyntax.Cons_list_value_l (v, l1, l3) ->
          (match l2 with
             | LLVMsyntax.Nil_list_value_l -> false
             | LLVMsyntax.Cons_list_value_l (v0, l4, l5) ->
                 let s = value_dec v v0 in
                 if s
                 then let s0 = l_dec l1 l4 in
                      if s0 then list_value_l_dec l3 l5 else false
                 else false)
  
  (** val list_value_dec :
      LLVMsyntax.list_value -> LLVMsyntax.list_value -> bool **)
  
  let rec list_value_dec l0 lv0 =
    match l0 with
      | LLVMsyntax.Nil_list_value ->
          (match lv0 with
             | LLVMsyntax.Nil_list_value -> true
             | LLVMsyntax.Cons_list_value (v, l1) -> false)
      | LLVMsyntax.Cons_list_value (v, l1) ->
          (match lv0 with
             | LLVMsyntax.Nil_list_value -> false
             | LLVMsyntax.Cons_list_value (v0, l2) ->
                 if value_dec v v0 then list_value_dec l1 l2 else false)
  
  (** val bop_dec : LLVMsyntax.bop -> LLVMsyntax.bop -> bool **)
  
  let bop_dec b1 b2 =
    match b1 with
      | LLVMsyntax.Coq_bop_add ->
          (match b2 with
             | LLVMsyntax.Coq_bop_add -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_lshr ->
          (match b2 with
             | LLVMsyntax.Coq_bop_lshr -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_and ->
          (match b2 with
             | LLVMsyntax.Coq_bop_and -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_or ->
          (match b2 with
             | LLVMsyntax.Coq_bop_or -> true
             | _ -> false)
  
  (** val extop_dec : LLVMsyntax.extop -> LLVMsyntax.extop -> bool **)
  
  let extop_dec e1 e2 =
    match e1 with
      | LLVMsyntax.Coq_extop_z ->
          (match e2 with
             | LLVMsyntax.Coq_extop_z -> true
             | LLVMsyntax.Coq_extop_s -> false)
      | LLVMsyntax.Coq_extop_s ->
          (match e2 with
             | LLVMsyntax.Coq_extop_z -> false
             | LLVMsyntax.Coq_extop_s -> true)
  
  (** val castop_dec : LLVMsyntax.castop -> LLVMsyntax.castop -> bool **)
  
  let castop_dec c1 c2 =
    match c1 with
      | LLVMsyntax.Coq_castop_fptoui ->
          (match c2 with
             | LLVMsyntax.Coq_castop_fptoui -> true
             | _ -> false)
      | LLVMsyntax.Coq_castop_fptosi ->
          (match c2 with
             | LLVMsyntax.Coq_castop_fptosi -> true
             | _ -> false)
      | LLVMsyntax.Coq_castop_uitofp ->
          (match c2 with
             | LLVMsyntax.Coq_castop_uitofp -> true
             | _ -> false)
      | LLVMsyntax.Coq_castop_sitofp ->
          (match c2 with
             | LLVMsyntax.Coq_castop_sitofp -> true
             | _ -> false)
      | LLVMsyntax.Coq_castop_ptrtoint ->
          (match c2 with
             | LLVMsyntax.Coq_castop_ptrtoint -> true
             | _ -> false)
      | LLVMsyntax.Coq_castop_inttoptr ->
          (match c2 with
             | LLVMsyntax.Coq_castop_inttoptr -> true
             | _ -> false)
      | LLVMsyntax.Coq_castop_bitcast ->
          (match c2 with
             | LLVMsyntax.Coq_castop_bitcast -> true
             | _ -> false)
  
  (** val cond_dec : LLVMsyntax.cond -> LLVMsyntax.cond -> bool **)
  
  let cond_dec c1 c2 =
    match c1 with
      | LLVMsyntax.Coq_cond_eq ->
          (match c2 with
             | LLVMsyntax.Coq_cond_eq -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_ne ->
          (match c2 with
             | LLVMsyntax.Coq_cond_ne -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_ugt ->
          (match c2 with
             | LLVMsyntax.Coq_cond_ugt -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_uge ->
          (match c2 with
             | LLVMsyntax.Coq_cond_uge -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_ult ->
          (match c2 with
             | LLVMsyntax.Coq_cond_ult -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_ule ->
          (match c2 with
             | LLVMsyntax.Coq_cond_ule -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_sgt ->
          (match c2 with
             | LLVMsyntax.Coq_cond_sgt -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_sge ->
          (match c2 with
             | LLVMsyntax.Coq_cond_sge -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_slt ->
          (match c2 with
             | LLVMsyntax.Coq_cond_slt -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_sle ->
          (match c2 with
             | LLVMsyntax.Coq_cond_sle -> true
             | _ -> false)
  
  (** val cmd_dec : LLVMsyntax.cmd -> LLVMsyntax.cmd -> bool **)
  
  let cmd_dec c1 c2 =
    match c1 with
      | LLVMsyntax.Coq_insn_bop (i0, b, s, v, v0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_bop (i1, b0, s0, v1, v2) ->
                 let s1 = id_dec i0 i1 in
                 if s1
                 then let s2 = bop_dec b b0 in
                      if s2
                      then let s3 = sz_dec s s0 in
                           if s3
                           then let s4 = value_dec v v1 in
                                if s4 then value_dec v0 v2 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_extractvalue (i0, t0, v, l0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_extractvalue (i1, t1, v0, l1) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t0 t1 in
                      if s0
                      then let s1 = value_dec v v0 in
                           if s1 then list_const_dec l0 l1 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_insertvalue (i0, t0, v, t1, v0, l0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_insertvalue (i1, t2, v1, t3, v2, l1) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t0 t2 in
                      if s0
                      then let s1 = value_dec v v1 in
                           if s1
                           then let s2 = typ_dec t1 t3 in
                                if s2
                                then let s3 = value_dec v0 v2 in
                                     if s3
                                     then list_const_dec l0 l1
                                     else false
                                else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_malloc (i0, t0, s, a) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_malloc (i1, t1, s0, a0) ->
                 let s1 = id_dec i0 i1 in
                 if s1
                 then let s2 = typ_dec t0 t1 in
                      if s2
                      then let s3 = sz_dec s s0 in
                           if s3 then align_dec a a0 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_free (i0, t0, v) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_free (i1, t1, v0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t0 t1 in
                      if s0 then value_dec v v0 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_alloca (i0, t0, s, a) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_alloca (i1, t1, s0, a0) ->
                 let s1 = id_dec i0 i1 in
                 if s1
                 then let s2 = typ_dec t0 t1 in
                      if s2
                      then let s3 = sz_dec s s0 in
                           if s3 then align_dec a a0 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_load (i0, t0, v, a) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_load (i1, t1, v0, a0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t0 t1 in
                      if s0
                      then let s1 = align_dec a a0 in
                           if s1 then value_dec v v0 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_store (i0, t0, v, v0, a) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_store (i1, t1, v1, v2, a0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t0 t1 in
                      if s0
                      then let s1 = value_dec v v1 in
                           if s1
                           then let s2 = align_dec a a0 in
                                if s2 then value_dec v0 v2 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_gep (i0, i1, t0, v, l0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_gep (i2, i3, t1, v0, l1) ->
                 let s = id_dec i0 i2 in
                 if s
                 then let s0 = inbounds_dec i1 i3 in
                      if s0
                      then let s1 = typ_dec t0 t1 in
                           if s1
                           then let s2 = value_dec v v0 in
                                if s2 then list_value_dec l0 l1 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_ext (i0, e, t0, v, t1) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_ext (i1, e0, t2, v0, t3) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = extop_dec e e0 in
                      if s0
                      then let s1 = typ_dec t0 t2 in
                           if s1
                           then let s2 = value_dec v v0 in
                                if s2 then typ_dec t1 t3 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_cast (i0, c, t0, v, t1) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_cast (i1, c0, t2, v0, t3) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = castop_dec c c0 in
                      if s0
                      then let s1 = typ_dec t0 t2 in
                           if s1
                           then let s2 = value_dec v v0 in
                                if s2 then typ_dec t1 t3 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_icmp (i0, c, t0, v, v0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_icmp (i1, c0, t1, v1, v2) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = cond_dec c c0 in
                      if s0
                      then let s1 = typ_dec t0 t1 in
                           if s1
                           then let s2 = value_dec v v1 in
                                if s2 then value_dec v0 v2 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_select (i0, v, t0, v0, v1) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_select (i1, v2, t1, v3, v4) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = value_dec v v2 in
                      if s0
                      then let s1 = typ_dec t0 t1 in
                           if s1
                           then let s2 = value_dec v0 v3 in
                                if s2 then value_dec v1 v4 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_call (i0, n, t0, t1, i1, p) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_call (i2, n0, t2, t3, i3, p0) ->
                 let s = id_dec i0 i2 in
                 if s
                 then let s0 = id_dec i1 i3 in
                      if s0
                      then let s1 = noret_dec n n0 in
                           if s1
                           then let s2 = tailc_dec t0 t2 in
                                if s2
                                then let s3 = typ_dec t1 t3 in
                                     if s3 then params_dec p p0 else false
                                else false
                           else false
                      else false
                 else false
             | _ -> false)
  
  (** val terminator_dec :
      LLVMsyntax.terminator -> LLVMsyntax.terminator -> bool **)
  
  let terminator_dec tmn1 tmn2 =
    match tmn1 with
      | LLVMsyntax.Coq_insn_return (i0, t0, v) ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_return (i1, t1, v0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t0 t1 in
                      if s0 then value_dec v v0 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_return_void i0 ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_return_void i1 -> id_dec i0 i1
             | _ -> false)
      | LLVMsyntax.Coq_insn_br (i0, v, l0, l1) ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_br (i1, v0, l2, l3) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = l_dec l0 l2 in
                      if s0
                      then let s1 = l_dec l1 l3 in
                           if s1 then value_dec v v0 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_br_uncond (i0, l0) ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_br_uncond (i1, l1) ->
                 let s = id_dec i0 i1 in if s then l_dec l0 l1 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_unreachable i0 ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_unreachable i1 -> id_dec i0 i1
             | _ -> false)
  
  (** val phinode_dec : LLVMsyntax.phinode -> LLVMsyntax.phinode -> bool **)
  
  let phinode_dec p1 p2 =
    let LLVMsyntax.Coq_insn_phi (i0, t0, l0) = p1 in
    let LLVMsyntax.Coq_insn_phi (i1, t1, l1) = p2 in
    let s = id_dec i0 i1 in
    if s
    then let s0 = typ_dec t0 t1 in
         if s0 then list_value_l_dec l0 l1 else false
    else false
  
  (** val insn_dec : LLVMsyntax.insn -> LLVMsyntax.insn -> bool **)
  
  let insn_dec i1 i2 =
    match i1 with
      | LLVMsyntax.Coq_insn_phinode p ->
          (match i2 with
             | LLVMsyntax.Coq_insn_phinode p0 -> phinode_dec p p0
             | _ -> false)
      | LLVMsyntax.Coq_insn_cmd c ->
          (match i2 with
             | LLVMsyntax.Coq_insn_cmd c0 -> cmd_dec c c0
             | _ -> false)
      | LLVMsyntax.Coq_insn_terminator t0 ->
          (match i2 with
             | LLVMsyntax.Coq_insn_terminator t1 -> terminator_dec t0 t1
             | _ -> false)
  
  (** val cmds_dec : LLVMsyntax.cmd list -> LLVMsyntax.cmd list -> bool **)
  
  let rec cmds_dec l0 cs2 =
    match l0 with
      | [] -> (match cs2 with
                 | [] -> true
                 | c::cs3 -> false)
      | y::l1 ->
          (match cs2 with
             | [] -> false
             | c::cs3 ->
                 let s = cmd_dec y c in if s then cmds_dec l1 cs3 else false)
  
  (** val phinodes_dec :
      LLVMsyntax.phinode list -> LLVMsyntax.phinode list -> bool **)
  
  let rec phinodes_dec l0 ps2 =
    match l0 with
      | [] -> (match ps2 with
                 | [] -> true
                 | p::ps3 -> false)
      | y::l1 ->
          (match ps2 with
             | [] -> false
             | p::ps3 ->
                 let s = phinode_dec y p in
                 if s then phinodes_dec l1 ps3 else false)
  
  (** val block_dec : LLVMsyntax.block -> LLVMsyntax.block -> bool **)
  
  let block_dec b1 b2 =
    let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b1 in
    let LLVMsyntax.Coq_block_intro (l1, p0, c0, t1) = b2 in
    let s = id_dec l0 l1 in
    if s
    then let s0 = phinodes_dec p p0 in
         if s0
         then let s1 = cmds_dec c c0 in
              if s1 then terminator_dec t0 t1 else false
         else false
    else false
  
  (** val arg_dec : LLVMsyntax.arg -> LLVMsyntax.arg -> bool **)
  
  let arg_dec a1 a2 =
    let t0,i0 = a1 in
    let t1,i1 = a2 in
    let s = id_dec i0 i1 in if s then typ_dec t0 t1 else false
  
  (** val args_dec : LLVMsyntax.args -> LLVMsyntax.args -> bool **)
  
  let rec args_dec l0 l2 =
    match l0 with
      | [] -> (match l2 with
                 | [] -> true
                 | p::l3 -> false)
      | y::l1 ->
          (match l2 with
             | [] -> false
             | p::l3 ->
                 let s = arg_dec y p in if s then args_dec l1 l3 else false)
  
  (** val fheader_dec : LLVMsyntax.fheader -> LLVMsyntax.fheader -> bool **)
  
  let fheader_dec f1 f2 =
    let LLVMsyntax.Coq_fheader_intro (t0, i0, a) = f1 in
    let LLVMsyntax.Coq_fheader_intro (t1, i1, a0) = f2 in
    let s = typ_dec t0 t1 in
    if s
    then let s0 = id_dec i0 i1 in if s0 then args_dec a a0 else false
    else false
  
  (** val blocks_dec : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool **)
  
  let rec blocks_dec l0 lb' =
    match l0 with
      | [] -> (match lb' with
                 | [] -> true
                 | b::lb'0 -> false)
      | y::l1 ->
          (match lb' with
             | [] -> false
             | b::lb'0 ->
                 let s = block_dec y b in
                 if s then blocks_dec l1 lb'0 else false)
  
  (** val fdec_dec : LLVMsyntax.fdec -> LLVMsyntax.fdec -> bool **)
  
  let fdec_dec f1 f2 =
    fheader_dec f1 f2
  
  (** val fdef_dec : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool **)
  
  let fdef_dec f1 f2 =
    let LLVMsyntax.Coq_fdef_intro (f, b) = f1 in
    let LLVMsyntax.Coq_fdef_intro (f0, b0) = f2 in
    let s = fheader_dec f f0 in if s then blocks_dec b b0 else false
  
  (** val gvar_dec : LLVMsyntax.gvar -> LLVMsyntax.gvar -> bool **)
  
  let gvar_dec g1 g2 =
    let LLVMsyntax.Coq_gvar_intro (i0, t0, c, a) = g1 in
    let LLVMsyntax.Coq_gvar_intro (i1, t1, c0, a0) = g2 in
    let s = id_dec i0 i1 in
    if s
    then let s0 = typ_dec t0 t1 in
         if s0
         then let s1 = const_dec c c0 in if s1 then align_dec a a0 else false
         else false
    else false
  
  (** val product_dec : LLVMsyntax.product -> LLVMsyntax.product -> bool **)
  
  let product_dec p p' =
    match p with
      | LLVMsyntax.Coq_product_gvar g ->
          (match p' with
             | LLVMsyntax.Coq_product_gvar g0 -> gvar_dec g g0
             | _ -> false)
      | LLVMsyntax.Coq_product_fdec f ->
          (match p' with
             | LLVMsyntax.Coq_product_fdec f0 -> fdec_dec f f0
             | _ -> false)
      | LLVMsyntax.Coq_product_fdef f ->
          (match p' with
             | LLVMsyntax.Coq_product_fdef f0 -> fdef_dec f f0
             | _ -> false)
  
  (** val products_dec :
      LLVMsyntax.products -> LLVMsyntax.products -> bool **)
  
  let rec products_dec l0 lp' =
    match l0 with
      | [] -> (match lp' with
                 | [] -> true
                 | p::lp'0 -> false)
      | y::l1 ->
          (match lp' with
             | [] -> false
             | p::lp'0 ->
                 let s = product_dec y p in
                 if s then products_dec l1 lp'0 else false)
  
  (** val layout_dec : LLVMsyntax.layout -> LLVMsyntax.layout -> bool **)
  
  let layout_dec l1 l2 =
    match l1 with
      | LLVMsyntax.Coq_layout_be ->
          (match l2 with
             | LLVMsyntax.Coq_layout_be -> true
             | _ -> false)
      | LLVMsyntax.Coq_layout_le ->
          (match l2 with
             | LLVMsyntax.Coq_layout_le -> true
             | _ -> false)
      | LLVMsyntax.Coq_layout_ptr (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_ptr (s0, a1, a2) ->
                 let s1 = sz_dec s s0 in
                 if s1
                 then let s2 = align_dec a a1 in
                      if s2 then align_dec a0 a2 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_layout_int (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_int (s0, a1, a2) ->
                 let s1 = sz_dec s s0 in
                 if s1
                 then let s2 = align_dec a a1 in
                      if s2 then align_dec a0 a2 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_layout_aggr (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_aggr (s0, a1, a2) ->
                 let s1 = sz_dec s s0 in
                 if s1
                 then let s2 = align_dec a a1 in
                      if s2 then align_dec a0 a2 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_layout_stack (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_stack (s0, a1, a2) ->
                 let s1 = sz_dec s s0 in
                 if s1
                 then let s2 = align_dec a a1 in
                      if s2 then align_dec a0 a2 else false
                 else false
             | _ -> false)
  
  (** val layouts_dec : LLVMsyntax.layouts -> LLVMsyntax.layouts -> bool **)
  
  let rec layouts_dec l0 l2 =
    match l0 with
      | [] -> (match l2 with
                 | [] -> true
                 | l1::l3 -> false)
      | y::l1 ->
          (match l2 with
             | [] -> false
             | l3::l4 ->
                 let s = layout_dec y l3 in
                 if s then layouts_dec l1 l4 else false)
  
  (** val module_dec :
      LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool **)
  
  let module_dec m m' =
    let LLVMsyntax.Coq_module_intro (l0, p) = m in
    let LLVMsyntax.Coq_module_intro (l1, p0) = m' in
    let s = layouts_dec l0 l1 in if s then products_dec p p0 else false
  
  (** val modules_dec : LLVMsyntax.modules -> LLVMsyntax.modules -> bool **)
  
  let rec modules_dec l0 lm' =
    match l0 with
      | [] -> (match lm' with
                 | [] -> true
                 | m::lm'0 -> false)
      | y::l1 ->
          (match lm' with
             | [] -> false
             | m::lm'0 ->
                 let s = module_dec y m in
                 if s then modules_dec l1 lm'0 else false)
  
  (** val system_dec : LLVMsyntax.system -> LLVMsyntax.system -> bool **)
  
  let system_dec =
    modules_dec
  
  (** val typEqB : LLVMsyntax.typ -> LLVMsyntax.typ -> bool **)
  
  let typEqB t1 t2 =
    sumbool2bool (typ_dec t1 t2)
  
  (** val list_typEqB :
      LLVMsyntax.list_typ -> LLVMsyntax.list_typ -> bool **)
  
  let list_typEqB lt1 lt2 =
    sumbool2bool (list_typ_dec lt1 lt2)
  
  (** val idEqB : LLVMsyntax.id -> LLVMsyntax.id -> bool **)
  
  let idEqB i0 i' =
    sumbool2bool (id_dec i0 i')
  
  (** val constEqB : LLVMsyntax.const -> LLVMsyntax.const -> bool **)
  
  let constEqB c1 c2 =
    sumbool2bool (const_dec c1 c2)
  
  (** val list_constEqB :
      LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool **)
  
  let list_constEqB lc1 lc2 =
    sumbool2bool (list_const_dec lc1 lc2)
  
  (** val valueEqB : LLVMsyntax.value -> LLVMsyntax.value -> bool **)
  
  let valueEqB v v' =
    sumbool2bool (value_dec v v')
  
  (** val paramsEqB : LLVMsyntax.params -> LLVMsyntax.params -> bool **)
  
  let paramsEqB lp lp' =
    sumbool2bool (params_dec lp lp')
  
  (** val lEqB : LLVMsyntax.l -> LLVMsyntax.l -> bool **)
  
  let lEqB i0 i' =
    sumbool2bool (l_dec i0 i')
  
  (** val list_value_lEqB :
      LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l -> bool **)
  
  let list_value_lEqB idls idls' =
    sumbool2bool (list_value_l_dec idls idls')
  
  (** val list_valueEqB :
      LLVMsyntax.list_value -> LLVMsyntax.list_value -> bool **)
  
  let list_valueEqB idxs idxs' =
    sumbool2bool (list_value_dec idxs idxs')
  
  (** val bopEqB : LLVMsyntax.bop -> LLVMsyntax.bop -> bool **)
  
  let bopEqB op op' =
    sumbool2bool (bop_dec op op')
  
  (** val extopEqB : LLVMsyntax.extop -> LLVMsyntax.extop -> bool **)
  
  let extopEqB op op' =
    sumbool2bool (extop_dec op op')
  
  (** val condEqB : LLVMsyntax.cond -> LLVMsyntax.cond -> bool **)
  
  let condEqB c c' =
    sumbool2bool (cond_dec c c')
  
  (** val castopEqB : LLVMsyntax.castop -> LLVMsyntax.castop -> bool **)
  
  let castopEqB c c' =
    sumbool2bool (castop_dec c c')
  
  (** val cmdEqB : LLVMsyntax.cmd -> LLVMsyntax.cmd -> bool **)
  
  let cmdEqB i0 i' =
    sumbool2bool (cmd_dec i0 i')
  
  (** val cmdsEqB : LLVMsyntax.cmd list -> LLVMsyntax.cmd list -> bool **)
  
  let cmdsEqB cs1 cs2 =
    sumbool2bool (cmds_dec cs1 cs2)
  
  (** val terminatorEqB :
      LLVMsyntax.terminator -> LLVMsyntax.terminator -> bool **)
  
  let terminatorEqB i0 i' =
    sumbool2bool (terminator_dec i0 i')
  
  (** val phinodeEqB : LLVMsyntax.phinode -> LLVMsyntax.phinode -> bool **)
  
  let phinodeEqB i0 i' =
    sumbool2bool (phinode_dec i0 i')
  
  (** val phinodesEqB :
      LLVMsyntax.phinode list -> LLVMsyntax.phinode list -> bool **)
  
  let phinodesEqB ps1 ps2 =
    sumbool2bool (phinodes_dec ps1 ps2)
  
  (** val blockEqB : LLVMsyntax.block -> LLVMsyntax.block -> bool **)
  
  let blockEqB b1 b2 =
    sumbool2bool (block_dec b1 b2)
  
  (** val blocksEqB : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool **)
  
  let blocksEqB lb lb' =
    sumbool2bool (blocks_dec lb lb')
  
  (** val argsEqB : LLVMsyntax.args -> LLVMsyntax.args -> bool **)
  
  let argsEqB la la' =
    sumbool2bool (args_dec la la')
  
  (** val fheaderEqB : LLVMsyntax.fheader -> LLVMsyntax.fheader -> bool **)
  
  let fheaderEqB fh fh' =
    sumbool2bool (fheader_dec fh fh')
  
  (** val fdecEqB : LLVMsyntax.fdec -> LLVMsyntax.fdec -> bool **)
  
  let fdecEqB fd fd' =
    sumbool2bool (fdec_dec fd fd')
  
  (** val fdefEqB : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool **)
  
  let fdefEqB fd fd' =
    sumbool2bool (fdef_dec fd fd')
  
  (** val gvarEqB : LLVMsyntax.gvar -> LLVMsyntax.gvar -> bool **)
  
  let gvarEqB gv gv' =
    sumbool2bool (gvar_dec gv gv')
  
  (** val productEqB : LLVMsyntax.product -> LLVMsyntax.product -> bool **)
  
  let productEqB p p' =
    sumbool2bool (product_dec p p')
  
  (** val productsEqB :
      LLVMsyntax.products -> LLVMsyntax.products -> bool **)
  
  let productsEqB lp lp' =
    sumbool2bool (products_dec lp lp')
  
  (** val layoutEqB : LLVMsyntax.layout -> LLVMsyntax.layout -> bool **)
  
  let layoutEqB o o' =
    sumbool2bool (layout_dec o o')
  
  (** val layoutsEqB : LLVMsyntax.layouts -> LLVMsyntax.layouts -> bool **)
  
  let layoutsEqB lo lo' =
    sumbool2bool (layouts_dec lo lo')
  
  (** val moduleEqB :
      LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool **)
  
  let moduleEqB m m' =
    sumbool2bool (module_dec m m')
  
  (** val modulesEqB : LLVMsyntax.modules -> LLVMsyntax.modules -> bool **)
  
  let modulesEqB lm lm' =
    sumbool2bool (modules_dec lm lm')
  
  (** val systemEqB : LLVMsyntax.system -> LLVMsyntax.system -> bool **)
  
  let systemEqB s s' =
    sumbool2bool (system_dec s s')
  
  (** val coq_InCmdsB : LLVMsyntax.cmd -> LLVMsyntax.cmds -> bool **)
  
  let rec coq_InCmdsB i0 = function
    | [] -> false
    | i'::li' -> if cmdEqB i0 i' then true else coq_InCmdsB i0 li'
  
  (** val coq_InPhiNodesB :
      LLVMsyntax.phinode -> LLVMsyntax.phinodes -> bool **)
  
  let rec coq_InPhiNodesB i0 = function
    | [] -> false
    | i'::li' -> if phinodeEqB i0 i' then true else coq_InPhiNodesB i0 li'
  
  (** val cmdInBlockB : LLVMsyntax.cmd -> LLVMsyntax.block -> bool **)
  
  let cmdInBlockB i0 = function
    | LLVMsyntax.Coq_block_intro (l0, p, cmds0, t0) -> coq_InCmdsB i0 cmds0
  
  (** val phinodeInBlockB :
      LLVMsyntax.phinode -> LLVMsyntax.block -> bool **)
  
  let phinodeInBlockB i0 = function
    | LLVMsyntax.Coq_block_intro (l0, ps, c, t0) -> coq_InPhiNodesB i0 ps
  
  (** val terminatorInBlockB :
      LLVMsyntax.terminator -> LLVMsyntax.block -> bool **)
  
  let terminatorInBlockB i0 = function
    | LLVMsyntax.Coq_block_intro (l0, p, c, t0) -> terminatorEqB i0 t0
  
  (** val coq_InArgsB : LLVMsyntax.arg -> LLVMsyntax.args -> bool **)
  
  let rec coq_InArgsB a = function
    | [] -> false
    | a'::la' ->
        if let t0,id0 = a in
           let t',id' = a' in if typEqB t0 t' then idEqB id0 id' else false
        then true
        else coq_InArgsB a la'
  
  (** val argInFheaderB : LLVMsyntax.arg -> LLVMsyntax.fheader -> bool **)
  
  let argInFheaderB a = function
    | LLVMsyntax.Coq_fheader_intro (t0, id0, la) -> coq_InArgsB a la
  
  (** val argInFdecB : LLVMsyntax.arg -> LLVMsyntax.fdec -> bool **)
  
  let argInFdecB a fd =
    argInFheaderB a fd
  
  (** val argInFdefB : LLVMsyntax.arg -> LLVMsyntax.fdef -> bool **)
  
  let argInFdefB a = function
    | LLVMsyntax.Coq_fdef_intro (fh, lb) -> argInFheaderB a fh
  
  (** val coq_InBlocksB : LLVMsyntax.block -> LLVMsyntax.blocks -> bool **)
  
  let rec coq_InBlocksB b = function
    | [] -> false
    | b'::lb' -> if blockEqB b b' then true else coq_InBlocksB b lb'
  
  (** val blockInFdefB : LLVMsyntax.block -> LLVMsyntax.fdef -> bool **)
  
  let blockInFdefB b = function
    | LLVMsyntax.Coq_fdef_intro (fh, lb) -> coq_InBlocksB b lb
  
  (** val coq_InProductsB :
      LLVMsyntax.product -> LLVMsyntax.products -> bool **)
  
  let rec coq_InProductsB p = function
    | [] -> false
    | p'::lp' -> if productEqB p p' then true else coq_InProductsB p lp'
  
  (** val productInModuleB :
      LLVMsyntax.product -> LLVMsyntax.coq_module -> bool **)
  
  let productInModuleB p = function
    | LLVMsyntax.Coq_module_intro (os, ps) -> coq_InProductsB p ps
  
  (** val coq_InModulesB :
      LLVMsyntax.coq_module -> LLVMsyntax.modules -> bool **)
  
  let rec coq_InModulesB m = function
    | [] -> false
    | m'::lm' -> if moduleEqB m m' then true else coq_InModulesB m lm'
  
  (** val moduleInSystemB :
      LLVMsyntax.coq_module -> LLVMsyntax.system -> bool **)
  
  let moduleInSystemB m s =
    coq_InModulesB m s
  
  (** val productInSystemModuleB :
      LLVMsyntax.product -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      bool **)
  
  let productInSystemModuleB p s m =
    if moduleInSystemB m s then productInModuleB p m else false
  
  (** val productInSystemModuleIB :
      LLVMsyntax.product -> LLVMsyntax.system -> LLVMsyntax.module_info ->
      bool **)
  
  let productInSystemModuleIB p s = function
    | m,p0 -> productInSystemModuleB p s m
  
  (** val blockInSystemModuleFdefB :
      LLVMsyntax.block -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      LLVMsyntax.fdef -> bool **)
  
  let blockInSystemModuleFdefB b s m f =
    if blockInFdefB b f
    then productInSystemModuleB (LLVMsyntax.Coq_product_fdef f) s m
    else false
  
  (** val blockInSystemModuleIFdefIB :
      LLVMsyntax.block -> LLVMsyntax.system -> LLVMsyntax.module_info ->
      LLVMsyntax.fdef_info -> bool **)
  
  let blockInSystemModuleIFdefIB b s mi fi =
    let m,p = mi in let fd,dt0 = fi in blockInSystemModuleFdefB b s m fd
  
  (** val cmdInSystemModuleFdefBlockB :
      LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let cmdInSystemModuleFdefBlockB i0 s m f b =
    if cmdInBlockB i0 b then blockInSystemModuleFdefB b s m f else false
  
  (** val cmdInSystemModuleIFdefIBlockB :
      LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.module_info ->
      LLVMsyntax.fdef_info -> LLVMsyntax.block -> bool **)
  
  let cmdInSystemModuleIFdefIBlockB i0 s mi fi b =
    let m,p = mi in
    let fd,dt0 = fi in
    if cmdInBlockB i0 b then blockInSystemModuleFdefB b s m fd else false
  
  (** val phinodeInSystemModuleFdefBlockB :
      LLVMsyntax.phinode -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let phinodeInSystemModuleFdefBlockB i0 s m f b =
    if phinodeInBlockB i0 b then blockInSystemModuleFdefB b s m f else false
  
  (** val phinodeInSystemModuleIFdefIBlockB :
      LLVMsyntax.phinode -> LLVMsyntax.system -> LLVMsyntax.module_info ->
      LLVMsyntax.fdef_info -> LLVMsyntax.block -> bool **)
  
  let phinodeInSystemModuleIFdefIBlockB i0 s mi fi b =
    let m,p = mi in
    let fd,dt0 = fi in
    if phinodeInBlockB i0 b then blockInSystemModuleFdefB b s m fd else false
  
  (** val terminatorInSystemModuleFdefBlockB :
      LLVMsyntax.terminator -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let terminatorInSystemModuleFdefBlockB i0 s m f b =
    if terminatorInBlockB i0 b
    then blockInSystemModuleFdefB b s m f
    else false
  
  (** val terminatorInSystemModuleIFdefIBlockB :
      LLVMsyntax.terminator -> LLVMsyntax.system -> LLVMsyntax.module_info ->
      LLVMsyntax.fdef_info -> LLVMsyntax.block -> bool **)
  
  let terminatorInSystemModuleIFdefIBlockB i0 s mi fi b =
    let m,p = mi in
    let fd,dt0 = fi in
    if terminatorInBlockB i0 b
    then blockInSystemModuleFdefB b s m fd
    else false
  
  (** val insnInSystemModuleFdefBlockB :
      LLVMsyntax.insn -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let insnInSystemModuleFdefBlockB i0 s m f b =
    match i0 with
      | LLVMsyntax.Coq_insn_phinode p ->
          phinodeInSystemModuleFdefBlockB p s m f b
      | LLVMsyntax.Coq_insn_cmd c -> cmdInSystemModuleFdefBlockB c s m f b
      | LLVMsyntax.Coq_insn_terminator t0 ->
          terminatorInSystemModuleFdefBlockB t0 s m f b
  
  (** val insnInSystemModuleIFdefIBlockB :
      LLVMsyntax.insn -> LLVMsyntax.system -> LLVMsyntax.module_info ->
      LLVMsyntax.fdef_info -> LLVMsyntax.block -> bool **)
  
  let insnInSystemModuleIFdefIBlockB i0 s mi fi b =
    let m,p = mi in
    let fd,dt0 = fi in insnInSystemModuleFdefBlockB i0 s m fd b
  
  (** val cmdInBlockB_dec : LLVMsyntax.cmd -> LLVMsyntax.block -> bool **)
  
  let cmdInBlockB_dec i0 b =
    let b0 = cmdInBlockB i0 b in if b0 then true else false
  
  (** val phinodeInBlockB_dec :
      LLVMsyntax.phinode -> LLVMsyntax.block -> bool **)
  
  let phinodeInBlockB_dec i0 b =
    let b0 = phinodeInBlockB i0 b in if b0 then true else false
  
  (** val terminatorInBlockB_dec :
      LLVMsyntax.terminator -> LLVMsyntax.block -> bool **)
  
  let terminatorInBlockB_dec i0 b =
    let b0 = terminatorInBlockB i0 b in if b0 then true else false
  
  (** val getParentOfCmdFromBlocks :
      LLVMsyntax.cmd -> LLVMsyntax.blocks -> LLVMsyntax.block option **)
  
  let rec getParentOfCmdFromBlocks i0 = function
    | [] -> None
    | b::lb' ->
        if cmdInBlockB_dec i0 b
        then Some b
        else getParentOfCmdFromBlocks i0 lb'
  
  (** val getParentOfCmdFromFdef :
      LLVMsyntax.cmd -> LLVMsyntax.fdef -> LLVMsyntax.block option **)
  
  let getParentOfCmdFromFdef i0 = function
    | LLVMsyntax.Coq_fdef_intro (f, lb) -> getParentOfCmdFromBlocks i0 lb
  
  (** val getParentOfCmdFromProduct :
      LLVMsyntax.cmd -> LLVMsyntax.product -> LLVMsyntax.block option **)
  
  let getParentOfCmdFromProduct i0 = function
    | LLVMsyntax.Coq_product_fdef fd -> getParentOfCmdFromFdef i0 fd
    | _ -> None
  
  (** val getParentOfCmdFromProducts :
      LLVMsyntax.cmd -> LLVMsyntax.products -> LLVMsyntax.block option **)
  
  let rec getParentOfCmdFromProducts i0 = function
    | [] -> None
    | p::lp' ->
        (match getParentOfCmdFromProduct i0 p with
           | Some b -> Some b
           | None -> getParentOfCmdFromProducts i0 lp')
  
  (** val getParentOfCmdFromModule :
      LLVMsyntax.cmd -> LLVMsyntax.coq_module -> LLVMsyntax.block option **)
  
  let getParentOfCmdFromModule i0 = function
    | LLVMsyntax.Coq_module_intro (os, ps) ->
        getParentOfCmdFromProducts i0 ps
  
  (** val getParentOfCmdFromModules :
      LLVMsyntax.cmd -> LLVMsyntax.modules -> LLVMsyntax.block option **)
  
  let rec getParentOfCmdFromModules i0 = function
    | [] -> None
    | m::lm' ->
        (match getParentOfCmdFromModule i0 m with
           | Some b -> Some b
           | None -> getParentOfCmdFromModules i0 lm')
  
  (** val getParentOfCmdFromSystem :
      LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.block option **)
  
  let getParentOfCmdFromSystem i0 s =
    getParentOfCmdFromModules i0 s
  
  (** val cmdHasParent : LLVMsyntax.cmd -> LLVMsyntax.system -> bool **)
  
  let cmdHasParent i0 s =
    match getParentOfCmdFromSystem i0 s with
      | Some b -> true
      | None -> false
  
  (** val getParentOfPhiNodeFromBlocks :
      LLVMsyntax.phinode -> LLVMsyntax.blocks -> LLVMsyntax.block option **)
  
  let rec getParentOfPhiNodeFromBlocks i0 = function
    | [] -> None
    | b::lb' ->
        if phinodeInBlockB_dec i0 b
        then Some b
        else getParentOfPhiNodeFromBlocks i0 lb'
  
  (** val getParentOfPhiNodeFromFdef :
      LLVMsyntax.phinode -> LLVMsyntax.fdef -> LLVMsyntax.block option **)
  
  let getParentOfPhiNodeFromFdef i0 = function
    | LLVMsyntax.Coq_fdef_intro (f, lb) -> getParentOfPhiNodeFromBlocks i0 lb
  
  (** val getParentOfPhiNodeFromProduct :
      LLVMsyntax.phinode -> LLVMsyntax.product -> LLVMsyntax.block option **)
  
  let getParentOfPhiNodeFromProduct i0 = function
    | LLVMsyntax.Coq_product_fdef fd -> getParentOfPhiNodeFromFdef i0 fd
    | _ -> None
  
  (** val getParentOfPhiNodeFromProducts :
      LLVMsyntax.phinode -> LLVMsyntax.products -> LLVMsyntax.block option **)
  
  let rec getParentOfPhiNodeFromProducts i0 = function
    | [] -> None
    | p::lp' ->
        (match getParentOfPhiNodeFromProduct i0 p with
           | Some b -> Some b
           | None -> getParentOfPhiNodeFromProducts i0 lp')
  
  (** val getParentOfPhiNodeFromModule :
      LLVMsyntax.phinode -> LLVMsyntax.coq_module -> LLVMsyntax.block option **)
  
  let getParentOfPhiNodeFromModule i0 = function
    | LLVMsyntax.Coq_module_intro (os, ps) ->
        getParentOfPhiNodeFromProducts i0 ps
  
  (** val getParentOfPhiNodeFromModules :
      LLVMsyntax.phinode -> LLVMsyntax.modules -> LLVMsyntax.block option **)
  
  let rec getParentOfPhiNodeFromModules i0 = function
    | [] -> None
    | m::lm' ->
        (match getParentOfPhiNodeFromModule i0 m with
           | Some b -> Some b
           | None -> getParentOfPhiNodeFromModules i0 lm')
  
  (** val getParentOfPhiNodeFromSystem :
      LLVMsyntax.phinode -> LLVMsyntax.system -> LLVMsyntax.block option **)
  
  let getParentOfPhiNodeFromSystem i0 s =
    getParentOfPhiNodeFromModules i0 s
  
  (** val phinodeHasParent :
      LLVMsyntax.phinode -> LLVMsyntax.system -> bool **)
  
  let phinodeHasParent i0 s =
    match getParentOfPhiNodeFromSystem i0 s with
      | Some b -> true
      | None -> false
  
  (** val getParentOfTerminatorFromBlocks :
      LLVMsyntax.terminator -> LLVMsyntax.blocks -> LLVMsyntax.block option **)
  
  let rec getParentOfTerminatorFromBlocks i0 = function
    | [] -> None
    | b::lb' ->
        if terminatorInBlockB_dec i0 b
        then Some b
        else getParentOfTerminatorFromBlocks i0 lb'
  
  (** val getParentOfTerminatorFromFdef :
      LLVMsyntax.terminator -> LLVMsyntax.fdef -> LLVMsyntax.block option **)
  
  let getParentOfTerminatorFromFdef i0 = function
    | LLVMsyntax.Coq_fdef_intro (f, lb) ->
        getParentOfTerminatorFromBlocks i0 lb
  
  (** val getParentOfTerminatorFromProduct :
      LLVMsyntax.terminator -> LLVMsyntax.product -> LLVMsyntax.block option **)
  
  let getParentOfTerminatorFromProduct i0 = function
    | LLVMsyntax.Coq_product_fdef fd -> getParentOfTerminatorFromFdef i0 fd
    | _ -> None
  
  (** val getParentOfTerminatorFromProducts :
      LLVMsyntax.terminator -> LLVMsyntax.products -> LLVMsyntax.block option **)
  
  let rec getParentOfTerminatorFromProducts i0 = function
    | [] -> None
    | p::lp' ->
        (match getParentOfTerminatorFromProduct i0 p with
           | Some b -> Some b
           | None -> getParentOfTerminatorFromProducts i0 lp')
  
  (** val getParentOfTerminatorFromModule :
      LLVMsyntax.terminator -> LLVMsyntax.coq_module -> LLVMsyntax.block
      option **)
  
  let getParentOfTerminatorFromModule i0 = function
    | LLVMsyntax.Coq_module_intro (os, ps) ->
        getParentOfTerminatorFromProducts i0 ps
  
  (** val getParentOfTerminatorFromModules :
      LLVMsyntax.terminator -> LLVMsyntax.modules -> LLVMsyntax.block option **)
  
  let rec getParentOfTerminatorFromModules i0 = function
    | [] -> None
    | m::lm' ->
        (match getParentOfTerminatorFromModule i0 m with
           | Some b -> Some b
           | None -> getParentOfTerminatorFromModules i0 lm')
  
  (** val getParentOfTerminatorFromSystem :
      LLVMsyntax.terminator -> LLVMsyntax.system -> LLVMsyntax.block option **)
  
  let getParentOfTerminatorFromSystem i0 s =
    getParentOfTerminatorFromModules i0 s
  
  (** val terminatoreHasParent :
      LLVMsyntax.terminator -> LLVMsyntax.system -> bool **)
  
  let terminatoreHasParent i0 s =
    match getParentOfTerminatorFromSystem i0 s with
      | Some b -> true
      | None -> false
  
  (** val productInModuleB_dec :
      LLVMsyntax.product -> LLVMsyntax.coq_module -> bool **)
  
  let productInModuleB_dec b m =
    let b0 = productInModuleB b m in if b0 then true else false
  
  (** val getParentOfFdefFromModules :
      LLVMsyntax.fdef -> LLVMsyntax.modules -> LLVMsyntax.coq_module option **)
  
  let rec getParentOfFdefFromModules fd = function
    | [] -> None
    | m::lm' ->
        if productInModuleB_dec (LLVMsyntax.Coq_product_fdef fd) m
        then Some m
        else getParentOfFdefFromModules fd lm'
  
  (** val getParentOfFdefFromSystem :
      LLVMsyntax.fdef -> LLVMsyntax.system -> LLVMsyntax.coq_module option **)
  
  let getParentOfFdefFromSystem fd s =
    getParentOfFdefFromModules fd s
  
  (** val lookupIdsViaLabelFromIdls :
      LLVMsyntax.list_value_l -> LLVMsyntax.l -> LLVMsyntax.id list **)
  
  let rec lookupIdsViaLabelFromIdls idls l0 =
    match idls with
      | LLVMsyntax.Nil_list_value_l -> []
      | LLVMsyntax.Cons_list_value_l (v, l1, idls') ->
          (match v with
             | LLVMsyntax.Coq_value_id id1 ->
                 if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) l0 l1
                 then set_add (eq_dec0 (eqDec_eq_of_EqDec eqDec_atom)) id1
                        (lookupIdsViaLabelFromIdls idls' l0)
                 else lookupIdsViaLabelFromIdls idls' l0
             | LLVMsyntax.Coq_value_const c ->
                 lookupIdsViaLabelFromIdls idls' l0)
  
  module type SigValue = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
   end
  
  module type SigUser = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
   end
  
  module type SigConstant = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ
   end
  
  module type SigGlobalValue = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ
   end
  
  module type SigFunction = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ
    
    val getDefReturnType : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val getDefFunctionType : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val def_arg_size : LLVMsyntax.fdef -> nat
    
    val getDecReturnType : LLVMsyntax.fdec -> LLVMsyntax.typ
    
    val getDecFunctionType : LLVMsyntax.fdec -> LLVMsyntax.typ
    
    val dec_arg_size : LLVMsyntax.fdec -> nat
   end
  
  module type SigInstruction = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
   end
  
  module type SigReturnInst = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val hasReturnType : LLVMsyntax.terminator -> bool
    
    val getReturnType : LLVMsyntax.terminator -> LLVMsyntax.typ option
   end
  
  module type SigCallSite = 
   sig 
    val getCalledFunction :
      LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.fdef option
    
    val getFdefTyp : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val arg_size : LLVMsyntax.fdef -> nat
    
    val getArgument : LLVMsyntax.fdef -> nat -> LLVMsyntax.arg option
    
    val getArgumentType : LLVMsyntax.fdef -> nat -> LLVMsyntax.typ option
   end
  
  module type SigCallInst = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
   end
  
  module type SigBinaryOperator = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val getFirstOperandType :
      LLVMsyntax.system -> LLVMsyntax.cmd -> LLVMsyntax.typ option
    
    val getSecondOperandType :
      LLVMsyntax.system -> LLVMsyntax.cmd -> LLVMsyntax.typ option
    
    val getResultType : LLVMsyntax.cmd -> LLVMsyntax.typ option
   end
  
  module type SigPHINode = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val getNumIncomingValues : LLVMsyntax.phinode -> nat
    
    val getIncomingValueType :
      LLVMsyntax.system -> LLVMsyntax.phinode -> LLVMsyntax.i ->
      LLVMsyntax.typ option
   end
  
  module type SigType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> nat
   end
  
  module type SigDerivedType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> nat
   end
  
  module type SigFunctionType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> nat
    
    val getNumParams : LLVMsyntax.typ -> nat option
    
    val isVarArg : LLVMsyntax.typ -> bool
    
    val getParamType : LLVMsyntax.typ -> nat -> LLVMsyntax.typ option
   end
  
  module type SigCompositeType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> nat
   end
  
  module type SigSequentialType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> nat
    
    val hasElementType : LLVMsyntax.typ -> bool
    
    val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option
   end
  
  module type SigArrayType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> nat
    
    val hasElementType : LLVMsyntax.typ -> bool
    
    val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option
    
    val getNumElements : LLVMsyntax.typ -> nat
   end
  
  module Value = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
   end
  
  module User = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
   end
  
  module Constant = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val getTyp : LLVMsyntax.const -> LLVMsyntax.typ **)
    
    let rec getTyp = function
      | LLVMsyntax.Coq_const_int (sz0, i0) -> LLVMsyntax.Coq_typ_int sz0
      | LLVMsyntax.Coq_const_undef t0 -> t0
      | LLVMsyntax.Coq_const_null t0 -> LLVMsyntax.Coq_typ_pointer t0
      | LLVMsyntax.Coq_const_arr lc ->
          (match lc with
             | LLVMsyntax.Nil_list_const -> LLVMsyntax.Coq_typ_array (szZERO,
                 (LLVMsyntax.Coq_typ_int szZERO))
             | LLVMsyntax.Cons_list_const (c', lc') ->
                 LLVMsyntax.Coq_typ_array
                 ((nat2sz (length (LLVMsyntax.unmake_list_const lc))),
                 (getTyp c')))
      | LLVMsyntax.Coq_const_struct lc -> LLVMsyntax.Coq_typ_struct
          (getList_typ lc)
      | LLVMsyntax.Coq_const_gid (t0, i0) -> LLVMsyntax.Coq_typ_pointer t0
    
    (** val getList_typ : LLVMsyntax.list_const -> LLVMsyntax.list_typ **)
    
    and getList_typ = function
      | LLVMsyntax.Nil_list_const -> LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_const (c, cs') -> LLVMsyntax.Cons_list_typ
          ((getTyp c), (getList_typ cs'))
   end
  
  module GlobalValue = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val getTyp : LLVMsyntax.const -> LLVMsyntax.typ **)
    
    let rec getTyp = function
      | LLVMsyntax.Coq_const_int (sz0, i0) -> LLVMsyntax.Coq_typ_int sz0
      | LLVMsyntax.Coq_const_undef t0 -> t0
      | LLVMsyntax.Coq_const_null t0 -> LLVMsyntax.Coq_typ_pointer t0
      | LLVMsyntax.Coq_const_arr lc ->
          (match lc with
             | LLVMsyntax.Nil_list_const -> LLVMsyntax.Coq_typ_array (szZERO,
                 (LLVMsyntax.Coq_typ_int szZERO))
             | LLVMsyntax.Cons_list_const (c', lc') ->
                 LLVMsyntax.Coq_typ_array
                 ((nat2sz (length (LLVMsyntax.unmake_list_const lc))),
                 (getTyp c')))
      | LLVMsyntax.Coq_const_struct lc -> LLVMsyntax.Coq_typ_struct
          (getList_typ lc)
      | LLVMsyntax.Coq_const_gid (t0, i0) -> LLVMsyntax.Coq_typ_pointer t0
    
    (** val getList_typ : LLVMsyntax.list_const -> LLVMsyntax.list_typ **)
    
    and getList_typ = function
      | LLVMsyntax.Nil_list_const -> LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_const (c, cs') -> LLVMsyntax.Cons_list_typ
          ((getTyp c), (getList_typ cs'))
   end
  
  module Function = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val getTyp : LLVMsyntax.const -> LLVMsyntax.typ **)
    
    let rec getTyp = function
      | LLVMsyntax.Coq_const_int (sz0, i0) -> LLVMsyntax.Coq_typ_int sz0
      | LLVMsyntax.Coq_const_undef t0 -> t0
      | LLVMsyntax.Coq_const_null t0 -> LLVMsyntax.Coq_typ_pointer t0
      | LLVMsyntax.Coq_const_arr lc ->
          (match lc with
             | LLVMsyntax.Nil_list_const -> LLVMsyntax.Coq_typ_array (szZERO,
                 (LLVMsyntax.Coq_typ_int szZERO))
             | LLVMsyntax.Cons_list_const (c', lc') ->
                 LLVMsyntax.Coq_typ_array
                 ((nat2sz (length (LLVMsyntax.unmake_list_const lc))),
                 (getTyp c')))
      | LLVMsyntax.Coq_const_struct lc -> LLVMsyntax.Coq_typ_struct
          (getList_typ lc)
      | LLVMsyntax.Coq_const_gid (t0, i0) -> LLVMsyntax.Coq_typ_pointer t0
    
    (** val getList_typ : LLVMsyntax.list_const -> LLVMsyntax.list_typ **)
    
    and getList_typ = function
      | LLVMsyntax.Nil_list_const -> LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_const (c, cs') -> LLVMsyntax.Cons_list_typ
          ((getTyp c), (getList_typ cs'))
    
    (** val getDefReturnType : LLVMsyntax.fdef -> LLVMsyntax.typ **)
    
    let getDefReturnType = function
      | LLVMsyntax.Coq_fdef_intro (f, b) ->
          let LLVMsyntax.Coq_fheader_intro (t0, i0, a) = f in t0
    
    (** val getDefFunctionType : LLVMsyntax.fdef -> LLVMsyntax.typ **)
    
    let getDefFunctionType fd =
      getFdefTyp fd
    
    (** val def_arg_size : LLVMsyntax.fdef -> nat **)
    
    let def_arg_size = function
      | LLVMsyntax.Coq_fdef_intro (f, b) ->
          let LLVMsyntax.Coq_fheader_intro (t0, i0, la) = f in length la
    
    (** val getDecReturnType : LLVMsyntax.fdec -> LLVMsyntax.typ **)
    
    let getDecReturnType = function
      | LLVMsyntax.Coq_fheader_intro (t0, i0, a) -> t0
    
    (** val getDecFunctionType : LLVMsyntax.fdec -> LLVMsyntax.typ **)
    
    let getDecFunctionType fd =
      getFdecTyp fd
    
    (** val dec_arg_size : LLVMsyntax.fdec -> nat **)
    
    let dec_arg_size = function
      | LLVMsyntax.Coq_fheader_intro (t0, i0, la) -> length la
   end
  
  module Instruction = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val isCallInst : LLVMsyntax.cmd -> bool **)
    
    let isCallInst i0 =
      _isCallInsnB i0
   end
  
  module ReturnInst = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val isCallInst : LLVMsyntax.cmd -> bool **)
    
    let isCallInst i0 =
      _isCallInsnB i0
    
    (** val hasReturnType : LLVMsyntax.terminator -> bool **)
    
    let hasReturnType = function
      | LLVMsyntax.Coq_insn_return (i1, t0, v) -> true
      | _ -> false
    
    (** val getReturnType :
        LLVMsyntax.terminator -> LLVMsyntax.typ option **)
    
    let getReturnType = function
      | LLVMsyntax.Coq_insn_return (i1, t0, v) -> Some t0
      | _ -> None
   end
  
  module CallSite = 
   struct 
    (** val getCalledFunction :
        LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.fdef option **)
    
    let getCalledFunction i0 s =
      match i0 with
        | LLVMsyntax.Coq_insn_call (i1, n, t0, t1, fid, p) ->
            lookupFdefViaIDFromSystem s fid
        | _ -> None
    
    (** val getFdefTyp : LLVMsyntax.fdef -> LLVMsyntax.typ **)
    
    let getFdefTyp fd =
      getFdefTyp fd
    
    (** val arg_size : LLVMsyntax.fdef -> nat **)
    
    let arg_size = function
      | LLVMsyntax.Coq_fdef_intro (f, b) ->
          let LLVMsyntax.Coq_fheader_intro (t0, i0, la) = f in length la
    
    (** val getArgument : LLVMsyntax.fdef -> nat -> LLVMsyntax.arg option **)
    
    let getArgument fd i0 =
      let LLVMsyntax.Coq_fdef_intro (f, b) = fd in
      let LLVMsyntax.Coq_fheader_intro (t0, i1, la) = f in nth_error la i0
    
    (** val getArgumentType :
        LLVMsyntax.fdef -> nat -> LLVMsyntax.typ option **)
    
    let getArgumentType fd i0 =
      match getArgument fd i0 with
        | Some a -> let t0,i1 = a in Some t0
        | None -> None
   end
  
  module CallInst = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val isCallInst : LLVMsyntax.cmd -> bool **)
    
    let isCallInst i0 =
      _isCallInsnB i0
   end
  
  module BinaryOperator = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val isCallInst : LLVMsyntax.cmd -> bool **)
    
    let isCallInst i0 =
      _isCallInsnB i0
    
    (** val getFirstOperandType :
        LLVMsyntax.system -> LLVMsyntax.cmd -> LLVMsyntax.typ option **)
    
    let getFirstOperandType s = function
      | LLVMsyntax.Coq_insn_bop (i1, b, s0, v1, v) ->
          (match v1 with
             | LLVMsyntax.Coq_value_id id1 -> lookupTypViaIDFromSystem s id1
             | LLVMsyntax.Coq_value_const c -> Some (Constant.getTyp c))
      | _ -> None
    
    (** val getSecondOperandType :
        LLVMsyntax.system -> LLVMsyntax.cmd -> LLVMsyntax.typ option **)
    
    let getSecondOperandType s = function
      | LLVMsyntax.Coq_insn_bop (i1, b, s0, v, v2) ->
          (match v2 with
             | LLVMsyntax.Coq_value_id id2 -> lookupTypViaIDFromSystem s id2
             | LLVMsyntax.Coq_value_const c -> Some (Constant.getTyp c))
      | _ -> None
    
    (** val getResultType : LLVMsyntax.cmd -> LLVMsyntax.typ option **)
    
    let getResultType i0 =
      getCmdTyp i0
   end
  
  module PHINode = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val isCallInst : LLVMsyntax.cmd -> bool **)
    
    let isCallInst i0 =
      _isCallInsnB i0
    
    (** val getNumIncomingValues : LLVMsyntax.phinode -> nat **)
    
    let getNumIncomingValues = function
      | LLVMsyntax.Coq_insn_phi (i1, t0, ln) ->
          length (LLVMsyntax.unmake_list_value_l ln)
    
    (** val getIncomingValueType :
        LLVMsyntax.system -> LLVMsyntax.phinode -> nat -> LLVMsyntax.typ
        option **)
    
    let getIncomingValueType s i0 n =
      let LLVMsyntax.Coq_insn_phi (i1, t0, ln) = i0 in
      (match LLVMsyntax.nth_list_value_l n ln with
         | Some p ->
             let v,l0 = p in
             (match v with
                | LLVMsyntax.Coq_value_id id0 ->
                    lookupTypViaIDFromSystem s id0
                | LLVMsyntax.Coq_value_const c -> Some (Constant.getTyp c))
         | None -> None)
   end
  
  module Typ = 
   struct 
    (** val isIntOrIntVector : LLVMsyntax.typ -> bool **)
    
    let isIntOrIntVector = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isInteger : LLVMsyntax.typ -> bool **)
    
    let isInteger = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isSized : LLVMsyntax.typ -> bool **)
    
    let rec isSized = function
      | LLVMsyntax.Coq_typ_int s -> true
      | LLVMsyntax.Coq_typ_array (s, t') -> isSized t'
      | LLVMsyntax.Coq_typ_struct lt0 -> isSizedListTyp lt0
      | _ -> false
    
    (** val isSizedListTyp : LLVMsyntax.list_typ -> bool **)
    
    and isSizedListTyp = function
      | LLVMsyntax.Nil_list_typ -> true
      | LLVMsyntax.Cons_list_typ (t0, lt') ->
          if isSized t0 then isSizedListTyp lt' else false
    
    (** val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz **)
    
    let getPrimitiveSizeInBits = function
      | LLVMsyntax.Coq_typ_int sz0 -> sz0
      | _ -> szZERO
   end
  
  module DerivedType = 
   struct 
    (** val isIntOrIntVector : LLVMsyntax.typ -> bool **)
    
    let isIntOrIntVector = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isInteger : LLVMsyntax.typ -> bool **)
    
    let isInteger = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isSized : LLVMsyntax.typ -> bool **)
    
    let rec isSized = function
      | LLVMsyntax.Coq_typ_int s -> true
      | LLVMsyntax.Coq_typ_array (s, t') -> isSized t'
      | LLVMsyntax.Coq_typ_struct lt0 -> isSizedListTyp lt0
      | _ -> false
    
    (** val isSizedListTyp : LLVMsyntax.list_typ -> bool **)
    
    and isSizedListTyp = function
      | LLVMsyntax.Nil_list_typ -> true
      | LLVMsyntax.Cons_list_typ (t0, lt') ->
          if isSized t0 then isSizedListTyp lt' else false
    
    (** val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz **)
    
    let getPrimitiveSizeInBits = function
      | LLVMsyntax.Coq_typ_int sz0 -> sz0
      | _ -> szZERO
   end
  
  module FunctionType = 
   struct 
    (** val isIntOrIntVector : LLVMsyntax.typ -> bool **)
    
    let isIntOrIntVector = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isInteger : LLVMsyntax.typ -> bool **)
    
    let isInteger = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isSized : LLVMsyntax.typ -> bool **)
    
    let rec isSized = function
      | LLVMsyntax.Coq_typ_int s -> true
      | LLVMsyntax.Coq_typ_array (s, t') -> isSized t'
      | LLVMsyntax.Coq_typ_struct lt0 -> isSizedListTyp lt0
      | _ -> false
    
    (** val isSizedListTyp : LLVMsyntax.list_typ -> bool **)
    
    and isSizedListTyp = function
      | LLVMsyntax.Nil_list_typ -> true
      | LLVMsyntax.Cons_list_typ (t0, lt') ->
          if isSized t0 then isSizedListTyp lt' else false
    
    (** val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz **)
    
    let getPrimitiveSizeInBits = function
      | LLVMsyntax.Coq_typ_int sz0 -> sz0
      | _ -> szZERO
    
    (** val getNumParams : LLVMsyntax.typ -> nat option **)
    
    let getNumParams = function
      | LLVMsyntax.Coq_typ_function (t1, lt0) -> Some
          (length (LLVMsyntax.unmake_list_typ lt0))
      | _ -> None
    
    (** val isVarArg : LLVMsyntax.typ -> bool **)
    
    let isVarArg t0 =
      false
    
    (** val getParamType : LLVMsyntax.typ -> nat -> LLVMsyntax.typ option **)
    
    let getParamType t0 i0 =
      match t0 with
        | LLVMsyntax.Coq_typ_function (t1, lt0) ->
            LLVMsyntax.nth_list_typ i0 lt0
        | _ -> None
   end
  
  module CompositeType = 
   struct 
    (** val isIntOrIntVector : LLVMsyntax.typ -> bool **)
    
    let isIntOrIntVector = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isInteger : LLVMsyntax.typ -> bool **)
    
    let isInteger = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isSized : LLVMsyntax.typ -> bool **)
    
    let rec isSized = function
      | LLVMsyntax.Coq_typ_int s -> true
      | LLVMsyntax.Coq_typ_array (s, t') -> isSized t'
      | LLVMsyntax.Coq_typ_struct lt0 -> isSizedListTyp lt0
      | _ -> false
    
    (** val isSizedListTyp : LLVMsyntax.list_typ -> bool **)
    
    and isSizedListTyp = function
      | LLVMsyntax.Nil_list_typ -> true
      | LLVMsyntax.Cons_list_typ (t0, lt') ->
          if isSized t0 then isSizedListTyp lt' else false
    
    (** val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz **)
    
    let getPrimitiveSizeInBits = function
      | LLVMsyntax.Coq_typ_int sz0 -> sz0
      | _ -> szZERO
   end
  
  module SequentialType = 
   struct 
    (** val isIntOrIntVector : LLVMsyntax.typ -> bool **)
    
    let isIntOrIntVector = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isInteger : LLVMsyntax.typ -> bool **)
    
    let isInteger = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isSized : LLVMsyntax.typ -> bool **)
    
    let rec isSized = function
      | LLVMsyntax.Coq_typ_int s -> true
      | LLVMsyntax.Coq_typ_array (s, t') -> isSized t'
      | LLVMsyntax.Coq_typ_struct lt0 -> isSizedListTyp lt0
      | _ -> false
    
    (** val isSizedListTyp : LLVMsyntax.list_typ -> bool **)
    
    and isSizedListTyp = function
      | LLVMsyntax.Nil_list_typ -> true
      | LLVMsyntax.Cons_list_typ (t0, lt') ->
          if isSized t0 then isSizedListTyp lt' else false
    
    (** val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz **)
    
    let getPrimitiveSizeInBits = function
      | LLVMsyntax.Coq_typ_int sz0 -> sz0
      | _ -> szZERO
    
    (** val hasElementType : LLVMsyntax.typ -> bool **)
    
    let hasElementType = function
      | LLVMsyntax.Coq_typ_array (s, t') -> true
      | _ -> false
    
    (** val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let getElementType = function
      | LLVMsyntax.Coq_typ_array (s, t') -> Some t'
      | _ -> None
   end
  
  module ArrayType = 
   struct 
    (** val isIntOrIntVector : LLVMsyntax.typ -> bool **)
    
    let isIntOrIntVector = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isInteger : LLVMsyntax.typ -> bool **)
    
    let isInteger = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isSized : LLVMsyntax.typ -> bool **)
    
    let rec isSized = function
      | LLVMsyntax.Coq_typ_int s -> true
      | LLVMsyntax.Coq_typ_array (s, t') -> isSized t'
      | LLVMsyntax.Coq_typ_struct lt0 -> isSizedListTyp lt0
      | _ -> false
    
    (** val isSizedListTyp : LLVMsyntax.list_typ -> bool **)
    
    and isSizedListTyp = function
      | LLVMsyntax.Nil_list_typ -> true
      | LLVMsyntax.Cons_list_typ (t0, lt') ->
          if isSized t0 then isSizedListTyp lt' else false
    
    (** val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz **)
    
    let getPrimitiveSizeInBits = function
      | LLVMsyntax.Coq_typ_int sz0 -> sz0
      | _ -> szZERO
    
    (** val hasElementType : LLVMsyntax.typ -> bool **)
    
    let hasElementType = function
      | LLVMsyntax.Coq_typ_array (s, t') -> true
      | _ -> false
    
    (** val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let getElementType = function
      | LLVMsyntax.Coq_typ_array (s, t') -> Some t'
      | _ -> None
    
    (** val getNumElements : LLVMsyntax.typ -> nat **)
    
    let getNumElements = function
      | LLVMsyntax.Coq_typ_array (n, t1) -> sz2nat n
      | _ -> O
   end
  
  type reflect =
    | ReflectT
    | ReflectF
  
  (** val reflect_rect :
      (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1 **)
  
  let reflect_rect f f0 b = function
    | ReflectT -> f __
    | ReflectF -> f0 __
  
  (** val reflect_rec :
      (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1 **)
  
  let reflect_rec f f0 b = function
    | ReflectT -> f __
    | ReflectF -> f0 __
  
  (** val reflect_blockDominates :
      LLVMsyntax.dt -> LLVMsyntax.block -> LLVMsyntax.block -> reflect **)
  
  let reflect_blockDominates d b1 b2 =
    let LLVMsyntax.Coq_block_intro (l1, insns1, c, t0) = b1 in
    let LLVMsyntax.Coq_block_intro (l2, insns2, c0, t1) = b2 in
    let c1 = lset_mem l2 (d l1) in if c1 then ReflectT else ReflectF
  
  (** val ifP :
      LLVMsyntax.dt -> LLVMsyntax.block -> LLVMsyntax.block -> 'a1 option ->
      'a1 option -> 'a1 option **)
  
  let ifP d b1 b2 t0 f =
    match reflect_blockDominates d b1 b2 with
      | ReflectT -> t0
      | ReflectF -> f
 end

type float (* AXIOM TO BE REALIZED *)

module Float = 
 struct 
  (** val zero : float **)
  
  let zero =
    failwith "AXIOM TO BE REALIZED"
  
  (** val eq_dec : float -> float -> bool **)
  
  let eq_dec =
    failwith "AXIOM TO BE REALIZED"
  
  (** val neg : float -> float **)
  
  let neg =
    failwith "AXIOM TO BE REALIZED"
  
  (** val abs : float -> float **)
  
  let abs =
    failwith "AXIOM TO BE REALIZED"
  
  (** val singleoffloat : float -> float **)
  
  let singleoffloat =
    failwith "AXIOM TO BE REALIZED"
  
  (** val intoffloat : float -> Int.int **)
  
  let intoffloat =
    failwith "AXIOM TO BE REALIZED"
  
  (** val intuoffloat : float -> Int.int **)
  
  let intuoffloat =
    failwith "AXIOM TO BE REALIZED"
  
  (** val floatofint : Int.int -> float **)
  
  let floatofint =
    failwith "AXIOM TO BE REALIZED"
  
  (** val floatofintu : Int.int -> float **)
  
  let floatofintu =
    failwith "AXIOM TO BE REALIZED"
  
  (** val add : float -> float -> float **)
  
  let add =
    failwith "AXIOM TO BE REALIZED"
  
  (** val sub : float -> float -> float **)
  
  let sub =
    failwith "AXIOM TO BE REALIZED"
  
  (** val mul : float -> float -> float **)
  
  let mul =
    failwith "AXIOM TO BE REALIZED"
  
  (** val div : float -> float -> float **)
  
  let div =
    failwith "AXIOM TO BE REALIZED"
  
  (** val cmp : comparison0 -> float -> float -> bool **)
  
  let cmp =
    failwith "AXIOM TO BE REALIZED"
  
  (** val bits_of_double : float -> Int.int **)
  
  let bits_of_double =
    failwith "AXIOM TO BE REALIZED"
  
  (** val double_of_bits : Int.int -> float **)
  
  let double_of_bits =
    failwith "AXIOM TO BE REALIZED"
  
  (** val bits_of_single : float -> Int.int **)
  
  let bits_of_single =
    failwith "AXIOM TO BE REALIZED"
  
  (** val single_of_bits : Int.int -> float **)
  
  let single_of_bits =
    failwith "AXIOM TO BE REALIZED"
  
  (** val from_words : Int.int -> Int.int -> float **)
  
  let from_words hi lo =
    double_of_bits
      (Int.coq_or (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (Int.shl (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (Int.repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            (Int.unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))))))))))))))))) hi))
          (Int.repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            (Zpos (XO (XO (XO (XO (XO XH))))))))
        (Int.repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (Int.unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))) lo)))
  
  (** val ox8000_0000 : Int.int **)
  
  let ox8000_0000 =
    Int.repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (Int.half_modulus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))
  
  (** val ox4330_0000 : Int.int **)
  
  let ox4330_0000 =
    Int.repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) (Zpos
      (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
      (XO (XO (XI (XI (XO (XO (XI (XI (XO (XO (XO (XO
      XH)))))))))))))))))))))))))))))))
 end

type memory_chunk =
  | Mint of nat
  | Mfloat32
  | Mfloat64

type block0 = z

(** val eq_block : z -> z -> bool **)

let eq_block =
  zeq

type val0 =
  | Vundef
  | Vint of nat * Int.int
  | Vfloat of float
  | Vptr of block0 * Int.int

type meminj = block0 -> (block0*z) option

(** val mint32 : memory_chunk **)

let mint32 =
  Mint (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))

(** val bytesize_chunk : nat -> z **)

let bytesize_chunk wz =
  zRdiv (z_of_nat (S wz)) (Zpos (XO (XO (XO XH))))

(** val bytesize_chunk_nat : nat -> nat **)

let bytesize_chunk_nat wz =
  nat_of_Z (bytesize_chunk wz)

(** val size_chunk : memory_chunk -> z **)

let size_chunk = function
  | Mint wz -> bytesize_chunk wz
  | Mfloat32 -> Zpos (XO (XO XH))
  | Mfloat64 -> Zpos (XO (XO (XO XH)))

(** val size_chunk_nat : memory_chunk -> nat **)

let size_chunk_nat chunk =
  nat_of_Z (size_chunk chunk)

(** val align_chunk : memory_chunk -> z **)

let align_chunk = function
  | Mint wz ->
      if le_lt_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S
           O)))))))))))))))))))))))))))))))
      then bytesize_chunk wz
      else Zpos (XO (XO XH))
  | _ -> Zpos (XO (XO XH))

type memval =
  | Undef
  | Byte of nat * Int.int
  | Pointer of block0 * Int.int * nat

(** val bytes_of_int : nat -> z -> Int.int list **)

let rec bytes_of_int n x =
  match n with
    | O -> []
    | S m ->
        (Int.repr (S (S (S (S (S (S (S O))))))) x)::
        (bytes_of_int m
          (zdiv x (Zpos (XO (XO (XO (XO (XO (XO (XO (XO XH)))))))))))

(** val int_of_bytes : Int.int list -> z **)

let rec int_of_bytes = function
  | [] -> Z0
  | b::l' ->
      zplus (Int.unsigned (S (S (S (S (S (S (S O))))))) b)
        (zmult (int_of_bytes l') (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
          XH))))))))))

(** val inj_bytes : Int.int list -> memval list **)

let inj_bytes bl =
  map (fun x -> Byte ((S (S (S (S (S (S (S (S O)))))))), x)) bl

(** val inj_int : nat -> Int.int -> memval list **)

let inj_int wz x =
  let z0 = Int.unsigned wz x in
  let n = z_of_nat (S wz) in
  let m = zmod n (Zpos (XO (XO (XO XH)))) in
  let sz0 = zRdiv n (Zpos (XO (XO (XO XH)))) in
  let bl = bytes_of_int (nat_of_Z sz0) z0 in
  (match bl with
     | [] -> []
     | b::bl' -> (Byte ((nat_of_Z m), b))::(inj_bytes bl'))

(** val proj_bytes : nat -> memval list -> Int.int list option **)

let rec proj_bytes n vl =
  match n with
    | O -> (match vl with
              | [] -> Some []
              | m::l0 -> None)
    | S m ->
        (match vl with
           | [] -> None
           | m0::vl' ->
               (match m0 with
                  | Byte (wz, b) ->
                      if eq_nat_dec wz (S (S (S (S (S (S (S (S O))))))))
                      then (match proj_bytes m vl' with
                              | Some bl' -> Some (b::bl')
                              | None -> None)
                      else None
                  | _ -> None))

(** val proj_int : nat -> memval list -> Int.int option **)

let proj_int wz vl =
  let n = z_of_nat (S wz) in
  let m = nat_of_Z (zmod n (Zpos (XO (XO (XO XH))))) in
  let sz0 = nat_of_Z (zRdiv n (Zpos (XO (XO (XO XH))))) in
  (match sz0 with
     | O -> None
     | S n' ->
         (match vl with
            | [] -> None
            | m0::vl' ->
                (match m0 with
                   | Byte (wz0, b) ->
                       if eq_nat_dec wz0 m
                       then (match proj_bytes n' vl' with
                               | Some bl' -> Some
                                   (Int.repr wz (int_of_bytes (b::bl')))
                               | None -> None)
                       else None
                   | _ -> None)))

(** val big_endian : bool **)

let big_endian =
  failwith "AXIOM TO BE REALIZED"

(** val rev_if_be : 'a1 list -> 'a1 list **)

let rev_if_be l0 =
  if big_endian then rev l0 else l0

(** val encode_int : nat -> Int.int -> memval list **)

let encode_int wz x =
  rev_if_be (inj_int wz x)

(** val decode_int : memval list -> nat -> val0 **)

let decode_int b wz =
  let b' = rev_if_be b in
  (match proj_int wz b' with
     | Some i0 -> Vint (wz, i0)
     | None -> Vundef)

(** val encode_float : memory_chunk -> float -> Int.int list **)

let encode_float c f =
  rev_if_be
    (match c with
       | Mint wz -> bytes_of_int (bytesize_chunk_nat wz) Z0
       | Mfloat32 ->
           bytes_of_int (S (S (S (S O))))
             (Int.unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               O))))))))))))))))))))))))))))))) (Float.bits_of_single f))
       | Mfloat64 ->
           bytes_of_int (S (S (S (S (S (S (S (S O))))))))
             (Int.unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S
               O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
               (Float.bits_of_double f)))

(** val decode_float : memory_chunk -> Int.int list -> float **)

let decode_float c b =
  let b' = rev_if_be b in
  (match c with
     | Mint n -> Float.zero
     | Mfloat32 ->
         Float.single_of_bits
           (Int.repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))))))))))))))) (int_of_bytes b'))
     | Mfloat64 ->
         Float.double_of_bits
           (Int.repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S
             O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
             (int_of_bytes b')))

(** val inj_pointer : nat -> block0 -> Int.int -> memval list **)

let rec inj_pointer n b ofs =
  match n with
    | O -> []
    | S m -> (Pointer (b, ofs, m))::(inj_pointer m b ofs)

(** val check_pointer : nat -> block0 -> Int.int -> memval list -> bool **)

let rec check_pointer n b ofs vl =
  match n with
    | O -> (match vl with
              | [] -> true
              | m::l0 -> false)
    | S m ->
        (match vl with
           | [] -> false
           | m0::vl' ->
               (match m0 with
                  | Pointer (b', ofs', m') ->
                      if if if proj_sumbool (eq_block b b')
                            then proj_sumbool
                                   (Int.eq_dec (S (S (S (S (S (S (S (S (S (S
                                     (S (S (S (S (S (S (S (S (S (S (S (S (S
                                     (S (S (S (S (S (S (S (S
                                     O))))))))))))))))))))))))))))))) ofs
                                     ofs')
                            else false
                         then beq_nat m m'
                         else false
                      then check_pointer m b ofs vl'
                      else false
                  | _ -> false))

(** val proj_pointer : memval list -> val0 **)

let proj_pointer vl = match vl with
  | [] -> Vundef
  | m::vl' ->
      (match m with
         | Pointer (b, ofs, n) ->
             if check_pointer (size_chunk_nat mint32) b ofs vl
             then Vptr (b, ofs)
             else Vundef
         | _ -> Vundef)

(** val encode_val : memory_chunk -> val0 -> memval list **)

let encode_val chunk = function
  | Vundef -> list_repeat (size_chunk_nat chunk) Undef
  | Vint (wz, n) ->
      (match chunk with
         | Mint wz' ->
             if eq_nat_dec wz wz'
             then encode_int wz n
             else list_repeat (size_chunk_nat chunk) Undef
         | _ -> list_repeat (size_chunk_nat chunk) Undef)
  | Vfloat f -> inj_bytes (encode_float chunk f)
  | Vptr (b, ofs) ->
      (match chunk with
         | Mint wz ->
             if eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O)))))))))))))))))))))))))))))))
             then inj_pointer (size_chunk_nat (Mint wz)) b ofs
             else list_repeat (size_chunk_nat chunk) Undef
         | _ -> list_repeat (size_chunk_nat chunk) Undef)

(** val decode_val : memory_chunk -> memval list -> val0 **)

let decode_val chunk vl =
  match chunk with
    | Mint wz ->
        (match decode_int vl wz with
           | Vundef ->
               if eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))
               then proj_pointer vl
               else Vundef
           | x -> x)
    | Mfloat32 ->
        (match proj_bytes
                 (bytesize_chunk_nat (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   O)))))))))))))))))))))))))))))))) vl with
           | Some bl -> Vfloat (decode_float chunk bl)
           | None -> Vundef)
    | Mfloat64 ->
        (match proj_bytes
                 (bytesize_chunk_nat (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S
                   O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                 vl with
           | Some bl -> Vfloat (decode_float chunk bl)
           | None -> Vundef)

type permission =
  | Freeable
  | Writable
  | Readable
  | Nonempty

(** val update : z -> 'a1 -> (z -> 'a1) -> z -> 'a1 **)

let update x v f y =
  if zeq y x then v else f y

module Mem = 
 struct 
  type mem_ = { mem_contents : (block0 -> z -> memval);
                mem_access : (block0 -> z -> permission option);
                bounds : (block0 -> z*z); nextblock : 
                block0 }
  
  (** val mem__rect :
      ((block0 -> z -> memval) -> (block0 -> z -> permission option) ->
      (block0 -> z*z) -> block0 -> __ -> __ -> __ -> __ -> 'a1) -> mem_ ->
      'a1 **)
  
  let mem__rect f m =
    let { mem_contents = x; mem_access = x0; bounds = x1; nextblock = x2 } =
      m
    in
    f x x0 x1 x2 __ __ __ __
  
  (** val mem__rec :
      ((block0 -> z -> memval) -> (block0 -> z -> permission option) ->
      (block0 -> z*z) -> block0 -> __ -> __ -> __ -> __ -> 'a1) -> mem_ ->
      'a1 **)
  
  let mem__rec f m =
    let { mem_contents = x; mem_access = x0; bounds = x1; nextblock = x2 } =
      m
    in
    f x x0 x1 x2 __ __ __ __
  
  (** val mem_contents : mem_ -> block0 -> z -> memval **)
  
  let mem_contents x = x.mem_contents
  
  (** val mem_access : mem_ -> block0 -> z -> permission option **)
  
  let mem_access x = x.mem_access
  
  (** val bounds : mem_ -> block0 -> z*z **)
  
  let bounds x = x.bounds
  
  (** val nextblock : mem_ -> block0 **)
  
  let nextblock x = x.nextblock
  
  type mem = mem_
  
  (** val perm_order_dec : permission -> permission -> bool **)
  
  let perm_order_dec p1 p2 =
    match p1 with
      | Freeable -> true
      | Writable -> (match p2 with
                       | Freeable -> false
                       | _ -> true)
      | Readable ->
          (match p2 with
             | Readable -> true
             | Nonempty -> true
             | _ -> false)
      | Nonempty -> (match p2 with
                       | Nonempty -> true
                       | _ -> false)
  
  (** val perm_order'_dec : permission option -> permission -> bool **)
  
  let perm_order'_dec op p =
    match op with
      | Some p0 -> perm_order_dec p0 p
      | None -> false
  
  (** val perm_dec : mem -> block0 -> z -> permission -> bool **)
  
  let perm_dec m b ofs p =
    perm_order'_dec (m.mem_access b ofs) p
  
  (** val range_perm_dec : mem -> block0 -> z -> z -> permission -> bool **)
  
  let range_perm_dec m b lo hi p =
    let h =
      natlike_rec2 true (fun z0 _ h0 ->
        if h0 then perm_dec m b (zplus lo z0) p else false)
    in
    let s = zlt lo hi in if s then h (zminus hi lo) else true
  
  (** val valid_access_dec :
      mem -> memory_chunk -> block0 -> z -> permission -> bool **)
  
  let valid_access_dec m chunk b ofs p =
    let s = range_perm_dec m b ofs (zplus ofs (size_chunk chunk)) p in
    if s then zdivide_dec (align_chunk chunk) ofs else false
  
  (** val valid_pointer : mem -> block0 -> z -> bool **)
  
  let valid_pointer m b ofs =
    proj_sumbool (perm_dec m b ofs Nonempty)
  
  (** val empty : mem **)
  
  let empty =
    { mem_contents = (fun b ofs -> Undef); mem_access = (fun b ofs -> None);
      bounds = (fun b -> Z0,Z0); nextblock = (Zpos XH) }
  
  (** val nullptr : block0 **)
  
  let nullptr =
    Z0
  
  (** val alloc : mem -> z -> z -> mem_*block0 **)
  
  let alloc m lo hi =
    { mem_contents = (update m.nextblock (fun ofs -> Undef) m.mem_contents);
      mem_access =
      (update m.nextblock (fun ofs ->
        if if proj_sumbool (zle lo ofs)
           then proj_sumbool (zlt ofs hi)
           else false
        then Some Freeable
        else None) m.mem_access); bounds =
      (update m.nextblock (lo,hi) m.bounds); nextblock =
      (zsucc m.nextblock) },m.nextblock
  
  (** val clearN :
      (block0 -> z -> memval) -> block0 -> z -> z -> block0 -> z -> memval **)
  
  let clearN m b lo hi b' ofs =
    if zeq b' b
    then if if proj_sumbool (zle lo ofs)
            then proj_sumbool (zlt ofs hi)
            else false
         then Undef
         else m b' ofs
    else m b' ofs
  
  (** val unchecked_free : mem -> block0 -> z -> z -> mem **)
  
  let unchecked_free m b lo hi =
    { mem_contents = (clearN m.mem_contents b lo hi); mem_access =
      (update b (fun ofs ->
        if if proj_sumbool (zle lo ofs)
           then proj_sumbool (zlt ofs hi)
           else false
        then None
        else m.mem_access b ofs) m.mem_access); bounds = m.bounds;
      nextblock = m.nextblock }
  
  (** val free : mem -> block0 -> z -> z -> mem option **)
  
  let free m b lo hi =
    if range_perm_dec m b lo hi Freeable
    then Some (unchecked_free m b lo hi)
    else None
  
  (** val free_list : mem -> ((block0*z)*z) list -> mem option **)
  
  let rec free_list m = function
    | [] -> Some m
    | p::l' ->
        let p0,hi = p in
        let b,lo = p0 in
        (match free m b lo hi with
           | Some m' -> free_list m' l'
           | None -> None)
  
  (** val getN : nat -> z -> (z -> memval) -> memval list **)
  
  let rec getN n p c =
    match n with
      | O -> []
      | S n' -> (c p)::(getN n' (zplus p (Zpos XH)) c)
  
  (** val load : memory_chunk -> mem -> block0 -> z -> val0 option **)
  
  let load chunk m b ofs =
    if valid_access_dec m chunk b ofs Readable
    then Some
           (decode_val chunk
             (getN (size_chunk_nat chunk) ofs (m.mem_contents b)))
    else None
  
  (** val loadv : memory_chunk -> mem -> val0 -> val0 option **)
  
  let loadv chunk m = function
    | Vptr (b, ofs) ->
        load chunk m b
          (Int.signed (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))) ofs)
    | _ -> None
  
  (** val loadbytes : mem -> block0 -> z -> z -> memval list option **)
  
  let loadbytes m b ofs n =
    if range_perm_dec m b ofs (zplus ofs n) Readable
    then Some (getN (nat_of_Z n) ofs (m.mem_contents b))
    else None
  
  (** val setN : memval list -> z -> (z -> memval) -> z -> memval **)
  
  let rec setN vl p c =
    match vl with
      | [] -> c
      | v::vl' -> setN vl' (zplus p (Zpos XH)) (update p v c)
  
  (** val store :
      memory_chunk -> mem -> block0 -> z -> val0 -> mem option **)
  
  let store chunk m b ofs v =
    if valid_access_dec m chunk b ofs Writable
    then Some { mem_contents =
           (update b (setN (encode_val chunk v) ofs (m.mem_contents b))
             m.mem_contents); mem_access = m.mem_access; bounds = m.bounds;
           nextblock = m.nextblock }
    else None
  
  (** val storev : memory_chunk -> mem -> val0 -> val0 -> mem option **)
  
  let storev chunk m addr v =
    match addr with
      | Vptr (b, ofs) ->
          store chunk m b
            (Int.signed (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))))))))))))))))) ofs) v
      | _ -> None
  
  (** val drop_perm : mem -> block0 -> z -> z -> permission -> mem option **)
  
  let drop_perm m b lo hi p =
    if range_perm_dec m b lo hi p
    then Some { mem_contents =
           (update b (fun ofs ->
             if if if proj_sumbool (zle lo ofs)
                   then proj_sumbool (zlt ofs hi)
                   else false
                then negb (proj_sumbool (perm_order_dec p Readable))
                else false
             then Undef
             else m.mem_contents b ofs) m.mem_contents); mem_access =
           (update b (fun ofs ->
             if if proj_sumbool (zle lo ofs)
                then proj_sumbool (zlt ofs hi)
                else false
             then Some p
             else m.mem_access b ofs) m.mem_access); bounds = m.bounds;
           nextblock = m.nextblock }
    else None
  
  (** val valid_access_store :
      mem -> memory_chunk -> block0 -> z -> val0 -> mem **)
  
  let valid_access_store m1 chunk b ofs v =
    let s = valid_access_dec m1 chunk b ofs Writable in
    if s
    then { mem_contents =
           (update b (setN (encode_val chunk v) ofs (m1.mem_contents b))
             m1.mem_contents); mem_access = m1.mem_access; bounds =
           m1.bounds; nextblock = m1.nextblock }
    else assert false (* absurd case *)
  
  (** val range_perm_free : mem -> block0 -> z -> z -> mem **)
  
  let range_perm_free m1 b lo hi =
    unchecked_free m1 b lo hi
  
  (** val range_perm_drop_2 :
      mem -> block0 -> z -> z -> permission -> mem **)
  
  let range_perm_drop_2 m b lo hi p =
    let s = range_perm_dec m b lo hi p in
    if s
    then { mem_contents =
           (update b (fun ofs ->
             if if if proj_sumbool (zle lo ofs)
                   then proj_sumbool (zlt ofs hi)
                   else false
                then negb (proj_sumbool (perm_order_dec p Readable))
                else false
             then Undef
             else m.mem_contents b ofs) m.mem_contents); mem_access =
           (update b (fun ofs ->
             if if proj_sumbool (zle lo ofs)
                then proj_sumbool (zlt ofs hi)
                else false
             then Some p
             else m.mem_access b ofs) m.mem_access); bounds = m.bounds;
           nextblock = m.nextblock }
    else assert false (* absurd case *)
  
  (** val mem_inj_rect : meminj -> mem -> mem -> (__ -> __ -> 'a1) -> 'a1 **)
  
  let mem_inj_rect f m1 m2 f0 =
    f0 __ __
  
  (** val mem_inj_rec : meminj -> mem -> mem -> (__ -> __ -> 'a1) -> 'a1 **)
  
  let mem_inj_rec f m1 m2 f0 =
    f0 __ __
  
  (** val extends__rect : mem -> mem -> (__ -> __ -> 'a1) -> 'a1 **)
  
  let extends__rect m1 m2 f =
    f __ __
  
  (** val extends__rec : mem -> mem -> (__ -> __ -> 'a1) -> 'a1 **)
  
  let extends__rec m1 m2 f =
    f __ __
  
  (** val inject__rect :
      meminj -> mem -> mem -> (__ -> __ -> __ -> __ -> __ -> __ -> 'a1) ->
      'a1 **)
  
  let inject__rect f m1 m2 f0 =
    f0 __ __ __ __ __ __
  
  (** val inject__rec :
      meminj -> mem -> mem -> (__ -> __ -> __ -> __ -> __ -> __ -> 'a1) ->
      'a1 **)
  
  let inject__rec f m1 m2 f0 =
    f0 __ __ __ __ __ __
  
  (** val flat_inj : block0 -> meminj **)
  
  let flat_inj thr b =
    if zlt b thr then Some (b,Z0) else None
 end

type event =
  | MkEvent

type trace =
  | Trace_nil
  | Trace_cons of event * trace

type genericValue = (val0*memory_chunk) list

type gVMap = (LLVMsyntax.id*genericValue) list

type mblock = block0

type mem0 = Mem.mem

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
  
  type coq_State = { coq_Frame : coq_ExecutionContext; coq_Mem : mem0 }
  
  (** val coq_State_rect :
      (coq_ExecutionContext -> mem0 -> 'a1) -> coq_State -> 'a1 **)
  
  let coq_State_rect f s =
    let { coq_Frame = x; coq_Mem = x0 } = s in f x x0
  
  (** val coq_State_rec :
      (coq_ExecutionContext -> mem0 -> 'a1) -> coq_State -> 'a1 **)
  
  let coq_State_rec f s =
    let { coq_Frame = x; coq_Mem = x0 } = s in f x x0
  
  (** val coq_Frame : coq_State -> coq_ExecutionContext **)
  
  let coq_Frame x = x.coq_Frame
  
  (** val coq_Mem : coq_State -> mem0 **)
  
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
  
  (** val isCallInst_dec : LLVMsyntax.cmd -> bool **)
  
  let isCallInst_dec = function
    | LLVMsyntax.Coq_insn_call (i0, n, t0, t1, i1, p) -> false
    | _ -> true
  
  (** val cmd2nbranch : LLVMsyntax.cmd -> nbranch option **)
  
  let cmd2nbranch c =
    if isCallInst_dec c then Some c else None
  
  (** val cmds2nbranchs : LLVMsyntax.cmd list -> nbranch list option **)
  
  let rec cmds2nbranchs = function
    | [] -> Some []
    | c::cs' ->
        let o = cmd2nbranch c in
        let o0 = cmds2nbranchs cs' in
        (match o with
           | Some nb ->
               (match o0 with
                  | Some nbs' -> Some (nb::nbs')
                  | None -> None)
           | None -> None)
  
  (** val nbranchs2cmds : nbranch list -> LLVMsyntax.cmd list **)
  
  let rec nbranchs2cmds = function
    | [] -> []
    | n::nbs' -> n::(nbranchs2cmds nbs')
  
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
  
  (** val cmds2sbs : LLVMsyntax.cmds -> subblock list*nbranch list **)
  
  let rec cmds2sbs = function
    | [] -> [],[]
    | c::cs' ->
        if isCallInst_dec c
        then let l0,nbs0 = cmds2sbs cs' in
             (match l0 with
                | [] -> [],(c::nbs0)
                | s::sbs' ->
                    let { coq_NBs = nbs; call_cmd = call0 } = s in
                    ({ coq_NBs = (c::nbs); call_cmd = call0 }::sbs'),nbs0)
        else let sbs,nbs0 = cmds2sbs cs' in
             ({ coq_NBs = []; call_cmd = c }::sbs),nbs0
  
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
    | Coq_sterm_load of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
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
    | Coq_smem_load of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_smem_store of smem * LLVMsyntax.typ * sterm * 
       sterm * LLVMsyntax.align
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
      (smem -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
      'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
      -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ
      -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ ->
      list_sterm_l -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> sterm -> 'a1 **)
  
  let rec sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
    | Coq_sterm_val v -> f v
    | Coq_sterm_bop (b, s0, s1, s2) ->
        f0 b s0 s1 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) s2
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s2)
    | Coq_sterm_extractvalue (t0, s0, l0) ->
        f1 t0 s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) l0
    | Coq_sterm_insertvalue (t0, s0, t1, s1, l0) ->
        f2 t0 s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t1
          s1 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) l0
    | Coq_sterm_malloc (s0, t0, s1, a) -> f3 s0 t0 s1 a
    | Coq_sterm_alloca (s0, t0, s1, a) -> f4 s0 t0 s1 a
    | Coq_sterm_load (s0, t0, s1, a) ->
        f5 s0 t0 s1 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) a
    | Coq_sterm_gep (i0, t0, s0, l0) ->
        f6 i0 t0 s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0)
          l0
    | Coq_sterm_ext (e, t0, s0, t1) ->
        f7 e t0 s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t1
    | Coq_sterm_cast (c, t0, s0, t1) ->
        f8 c t0 s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t1
    | Coq_sterm_icmp (c, t0, s0, s1) ->
        f9 c t0 s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1)
    | Coq_sterm_phi (t0, l0) -> f10 t0 l0
    | Coq_sterm_select (s0, t0, s1, s2) ->
        f11 s0 (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t0 s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) s2
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s2)
  
  (** val sterm_rec :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
      (smem -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
      (smem -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
      'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
      -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ
      -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ ->
      list_sterm_l -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> sterm -> 'a1 **)
  
  let rec sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
    | Coq_sterm_val v -> f v
    | Coq_sterm_bop (b, s0, s1, s2) ->
        f0 b s0 s1 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) s2
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s2)
    | Coq_sterm_extractvalue (t0, s0, l0) ->
        f1 t0 s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) l0
    | Coq_sterm_insertvalue (t0, s0, t1, s1, l0) ->
        f2 t0 s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t1 s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) l0
    | Coq_sterm_malloc (s0, t0, s1, a) -> f3 s0 t0 s1 a
    | Coq_sterm_alloca (s0, t0, s1, a) -> f4 s0 t0 s1 a
    | Coq_sterm_load (s0, t0, s1, a) ->
        f5 s0 t0 s1 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) a
    | Coq_sterm_gep (i0, t0, s0, l0) ->
        f6 i0 t0 s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) l0
    | Coq_sterm_ext (e, t0, s0, t1) ->
        f7 e t0 s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t1
    | Coq_sterm_cast (c, t0, s0, t1) ->
        f8 c t0 s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t1
    | Coq_sterm_icmp (c, t0, s0, s1) ->
        f9 c t0 s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1)
    | Coq_sterm_phi (t0, l0) -> f10 t0 l0
    | Coq_sterm_select (s0, t0, s1, s2) ->
        f11 s0 (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) t0 s1
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
      LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
      sterm -> LLVMsyntax.align -> 'a1) -> smem -> 'a1 **)
  
  let rec smem_rect f f0 f1 f2 f3 f4 = function
    | Coq_smem_init -> f
    | Coq_smem_malloc (s0, t0, s1, a) ->
        f0 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t0 s1 a
    | Coq_smem_free (s0, t0, s1) ->
        f1 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t0 s1
    | Coq_smem_alloca (s0, t0, s1, a) ->
        f2 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t0 s1 a
    | Coq_smem_load (s0, t0, s1, a) ->
        f3 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t0 s1 a
    | Coq_smem_store (s0, t0, s1, s2, a) ->
        f4 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t0 s1 s2 a
  
  (** val smem_rec :
      'a1 -> (smem -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
      'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
      sterm -> LLVMsyntax.align -> 'a1) -> smem -> 'a1 **)
  
  let rec smem_rec f f0 f1 f2 f3 f4 = function
    | Coq_smem_init -> f
    | Coq_smem_malloc (s0, t0, s1, a) ->
        f0 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t0 s1 a
    | Coq_smem_free (s0, t0, s1) ->
        f1 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t0 s1
    | Coq_smem_alloca (s0, t0, s1, a) ->
        f2 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t0 s1 a
    | Coq_smem_load (s0, t0, s1, a) ->
        f3 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t0 s1 a
    | Coq_smem_store (s0, t0, s1, s2, a) ->
        f4 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t0 s1 s2 a
  
  (** val sframe_rect :
      'a1 -> (smem -> sframe -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> sframe -> 'a1 **)
  
  let rec sframe_rect f f0 = function
    | Coq_sframe_init -> f
    | Coq_sframe_alloca (s0, s1, t0, s2, a) ->
        f0 s0 s1 (sframe_rect f f0 s1) t0 s2 a
  
  (** val sframe_rec :
      'a1 -> (smem -> sframe -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> sframe -> 'a1 **)
  
  let rec sframe_rec f f0 = function
    | Coq_sframe_init -> f
    | Coq_sframe_alloca (s0, s1, t0, s2, a) ->
        f0 s0 s1 (sframe_rec f f0 s1) t0 s2 a
  
  (** val sframe_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds ->
      LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm -> 'a2 -> 'a1) ->
      (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ
      -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l ->
      'a3 -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm
      -> 'a1 -> 'a1) -> 'a2 -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) ->
      'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
      'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 ->
      (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a5) -> sframe -> 'a5 **)
  
  let sframe_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_extractvalue (t0, s0, l0) -> f1 t0 s0 (f24 s0) l0
      | Coq_sterm_insertvalue (t0, s0, t1, s1, l0) ->
          f2 t0 s0 (f24 s0) t1 s1 (f24 s1) l0
      | Coq_sterm_malloc (s0, t0, s1, a) -> f3 s0 (f27 s0) t0 s1 a
      | Coq_sterm_alloca (s0, t0, s1, a) -> f4 s0 (f27 s0) t0 s1 a
      | Coq_sterm_load (s0, t0, s1, a) -> f5 s0 (f27 s0) t0 s1 (f24 s1) a
      | Coq_sterm_gep (i0, t0, s0, l0) -> f6 i0 t0 s0 (f24 s0) l0 (f25 l0)
      | Coq_sterm_ext (e, t0, s0, t1) -> f7 e t0 s0 (f24 s0) t1
      | Coq_sterm_cast (c, t0, s0, t1) -> f8 c t0 s0 (f24 s0) t1
      | Coq_sterm_icmp (c, t0, s0, s1) -> f9 c t0 s0 (f24 s0) s1 (f24 s1)
      | Coq_sterm_phi (t0, l0) -> f10 t0 l0 (f26 l0)
      | Coq_sterm_select (s0, t0, s1, s2) ->
          f11 s0 (f24 s0) t0 s1 (f24 s1) s2 (f24 s2)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s, l1) -> f13 s (f24 s) l1 (f25 l1)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s, l1, l2) -> f15 s (f24 s) l1 l2 (f26 l2)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s0, t0, s1, a) -> f17 s0 (f27 s0) t0 s1 a
      | Coq_smem_free (s0, t0, s1) -> f18 s0 (f27 s0) t0 s1 (f24 s1)
      | Coq_smem_alloca (s0, t0, s1, a) -> f19 s0 (f27 s0) t0 s1 a
      | Coq_smem_load (s0, t0, s1, a) -> f20 s0 (f27 s0) t0 s1 (f24 s1) a
      | Coq_smem_store (s0, t0, s1, s2, a) ->
          f21 s0 (f27 s0) t0 s1 (f24 s1) s2 (f24 s2) a
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s0, s1, t0, s2, a) ->
          f23 s0 (f27 s0) s1 (f28 s1) t0 s2 a
    in f28
  
  (** val smem_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds ->
      LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm -> 'a2 -> 'a1) ->
      (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ
      -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l ->
      'a3 -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm
      -> 'a1 -> 'a1) -> 'a2 -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) ->
      'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
      'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 ->
      (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a5) -> smem -> 'a4 **)
  
  let smem_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_extractvalue (t0, s0, l0) -> f1 t0 s0 (f24 s0) l0
      | Coq_sterm_insertvalue (t0, s0, t1, s1, l0) ->
          f2 t0 s0 (f24 s0) t1 s1 (f24 s1) l0
      | Coq_sterm_malloc (s0, t0, s1, a) -> f3 s0 (f27 s0) t0 s1 a
      | Coq_sterm_alloca (s0, t0, s1, a) -> f4 s0 (f27 s0) t0 s1 a
      | Coq_sterm_load (s0, t0, s1, a) -> f5 s0 (f27 s0) t0 s1 (f24 s1) a
      | Coq_sterm_gep (i0, t0, s0, l0) -> f6 i0 t0 s0 (f24 s0) l0 (f25 l0)
      | Coq_sterm_ext (e, t0, s0, t1) -> f7 e t0 s0 (f24 s0) t1
      | Coq_sterm_cast (c, t0, s0, t1) -> f8 c t0 s0 (f24 s0) t1
      | Coq_sterm_icmp (c, t0, s0, s1) -> f9 c t0 s0 (f24 s0) s1 (f24 s1)
      | Coq_sterm_phi (t0, l0) -> f10 t0 l0 (f26 l0)
      | Coq_sterm_select (s0, t0, s1, s2) ->
          f11 s0 (f24 s0) t0 s1 (f24 s1) s2 (f24 s2)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s, l1) -> f13 s (f24 s) l1 (f25 l1)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s, l1, l2) -> f15 s (f24 s) l1 l2 (f26 l2)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s0, t0, s1, a) -> f17 s0 (f27 s0) t0 s1 a
      | Coq_smem_free (s0, t0, s1) -> f18 s0 (f27 s0) t0 s1 (f24 s1)
      | Coq_smem_alloca (s0, t0, s1, a) -> f19 s0 (f27 s0) t0 s1 a
      | Coq_smem_load (s0, t0, s1, a) -> f20 s0 (f27 s0) t0 s1 (f24 s1) a
      | Coq_smem_store (s0, t0, s1, s2, a) ->
          f21 s0 (f27 s0) t0 s1 (f24 s1) s2 (f24 s2) a
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s0, s1, t0, s2, a) ->
          f23 s0 (f27 s0) s1 (f28 s1) t0 s2 a
    in f27
  
  (** val list_sterm_l_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds ->
      LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm -> 'a2 -> 'a1) ->
      (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ
      -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l ->
      'a3 -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm
      -> 'a1 -> 'a1) -> 'a2 -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) ->
      'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
      'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 ->
      (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a5) -> list_sterm_l -> 'a3 **)
  
  let list_sterm_l_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_extractvalue (t0, s0, l0) -> f1 t0 s0 (f24 s0) l0
      | Coq_sterm_insertvalue (t0, s0, t1, s1, l0) ->
          f2 t0 s0 (f24 s0) t1 s1 (f24 s1) l0
      | Coq_sterm_malloc (s0, t0, s1, a) -> f3 s0 (f27 s0) t0 s1 a
      | Coq_sterm_alloca (s0, t0, s1, a) -> f4 s0 (f27 s0) t0 s1 a
      | Coq_sterm_load (s0, t0, s1, a) -> f5 s0 (f27 s0) t0 s1 (f24 s1) a
      | Coq_sterm_gep (i0, t0, s0, l0) -> f6 i0 t0 s0 (f24 s0) l0 (f25 l0)
      | Coq_sterm_ext (e, t0, s0, t1) -> f7 e t0 s0 (f24 s0) t1
      | Coq_sterm_cast (c, t0, s0, t1) -> f8 c t0 s0 (f24 s0) t1
      | Coq_sterm_icmp (c, t0, s0, s1) -> f9 c t0 s0 (f24 s0) s1 (f24 s1)
      | Coq_sterm_phi (t0, l0) -> f10 t0 l0 (f26 l0)
      | Coq_sterm_select (s0, t0, s1, s2) ->
          f11 s0 (f24 s0) t0 s1 (f24 s1) s2 (f24 s2)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s, l1) -> f13 s (f24 s) l1 (f25 l1)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s, l1, l2) -> f15 s (f24 s) l1 l2 (f26 l2)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s0, t0, s1, a) -> f17 s0 (f27 s0) t0 s1 a
      | Coq_smem_free (s0, t0, s1) -> f18 s0 (f27 s0) t0 s1 (f24 s1)
      | Coq_smem_alloca (s0, t0, s1, a) -> f19 s0 (f27 s0) t0 s1 a
      | Coq_smem_load (s0, t0, s1, a) -> f20 s0 (f27 s0) t0 s1 (f24 s1) a
      | Coq_smem_store (s0, t0, s1, s2, a) ->
          f21 s0 (f27 s0) t0 s1 (f24 s1) s2 (f24 s2) a
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s0, s1, t0, s2, a) ->
          f23 s0 (f27 s0) s1 (f28 s1) t0 s2 a
    in f26
  
  (** val list_sterm_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds ->
      LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm -> 'a2 -> 'a1) ->
      (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ
      -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l ->
      'a3 -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm
      -> 'a1 -> 'a1) -> 'a2 -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) ->
      'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
      'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 ->
      (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a5) -> list_sterm -> 'a2 **)
  
  let list_sterm_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_extractvalue (t0, s0, l0) -> f1 t0 s0 (f24 s0) l0
      | Coq_sterm_insertvalue (t0, s0, t1, s1, l0) ->
          f2 t0 s0 (f24 s0) t1 s1 (f24 s1) l0
      | Coq_sterm_malloc (s0, t0, s1, a) -> f3 s0 (f27 s0) t0 s1 a
      | Coq_sterm_alloca (s0, t0, s1, a) -> f4 s0 (f27 s0) t0 s1 a
      | Coq_sterm_load (s0, t0, s1, a) -> f5 s0 (f27 s0) t0 s1 (f24 s1) a
      | Coq_sterm_gep (i0, t0, s0, l0) -> f6 i0 t0 s0 (f24 s0) l0 (f25 l0)
      | Coq_sterm_ext (e, t0, s0, t1) -> f7 e t0 s0 (f24 s0) t1
      | Coq_sterm_cast (c, t0, s0, t1) -> f8 c t0 s0 (f24 s0) t1
      | Coq_sterm_icmp (c, t0, s0, s1) -> f9 c t0 s0 (f24 s0) s1 (f24 s1)
      | Coq_sterm_phi (t0, l0) -> f10 t0 l0 (f26 l0)
      | Coq_sterm_select (s0, t0, s1, s2) ->
          f11 s0 (f24 s0) t0 s1 (f24 s1) s2 (f24 s2)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s, l1) -> f13 s (f24 s) l1 (f25 l1)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s, l1, l2) -> f15 s (f24 s) l1 l2 (f26 l2)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s0, t0, s1, a) -> f17 s0 (f27 s0) t0 s1 a
      | Coq_smem_free (s0, t0, s1) -> f18 s0 (f27 s0) t0 s1 (f24 s1)
      | Coq_smem_alloca (s0, t0, s1, a) -> f19 s0 (f27 s0) t0 s1 a
      | Coq_smem_load (s0, t0, s1, a) -> f20 s0 (f27 s0) t0 s1 (f24 s1) a
      | Coq_smem_store (s0, t0, s1, s2, a) ->
          f21 s0 (f27 s0) t0 s1 (f24 s1) s2 (f24 s2) a
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s0, s1, t0, s2, a) ->
          f23 s0 (f27 s0) s1 (f28 s1) t0 s2 a
    in f25
  
  (** val sterm_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds ->
      LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm -> 'a2 -> 'a1) ->
      (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ
      -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l ->
      'a3 -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm
      -> 'a1 -> 'a1) -> 'a2 -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) ->
      'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
      'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 ->
      (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a5) -> sterm -> 'a1 **)
  
  let sterm_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_extractvalue (t0, s0, l0) -> f1 t0 s0 (f24 s0) l0
      | Coq_sterm_insertvalue (t0, s0, t1, s1, l0) ->
          f2 t0 s0 (f24 s0) t1 s1 (f24 s1) l0
      | Coq_sterm_malloc (s0, t0, s1, a) -> f3 s0 (f27 s0) t0 s1 a
      | Coq_sterm_alloca (s0, t0, s1, a) -> f4 s0 (f27 s0) t0 s1 a
      | Coq_sterm_load (s0, t0, s1, a) -> f5 s0 (f27 s0) t0 s1 (f24 s1) a
      | Coq_sterm_gep (i0, t0, s0, l0) -> f6 i0 t0 s0 (f24 s0) l0 (f25 l0)
      | Coq_sterm_ext (e, t0, s0, t1) -> f7 e t0 s0 (f24 s0) t1
      | Coq_sterm_cast (c, t0, s0, t1) -> f8 c t0 s0 (f24 s0) t1
      | Coq_sterm_icmp (c, t0, s0, s1) -> f9 c t0 s0 (f24 s0) s1 (f24 s1)
      | Coq_sterm_phi (t0, l0) -> f10 t0 l0 (f26 l0)
      | Coq_sterm_select (s0, t0, s1, s2) ->
          f11 s0 (f24 s0) t0 s1 (f24 s1) s2 (f24 s2)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s, l1) -> f13 s (f24 s) l1 (f25 l1)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s, l1, l2) -> f15 s (f24 s) l1 l2 (f26 l2)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s0, t0, s1, a) -> f17 s0 (f27 s0) t0 s1 a
      | Coq_smem_free (s0, t0, s1) -> f18 s0 (f27 s0) t0 s1 (f24 s1)
      | Coq_smem_alloca (s0, t0, s1, a) -> f19 s0 (f27 s0) t0 s1 a
      | Coq_smem_load (s0, t0, s1, a) -> f20 s0 (f27 s0) t0 s1 (f24 s1) a
      | Coq_smem_store (s0, t0, s1, s2, a) ->
          f21 s0 (f27 s0) t0 s1 (f24 s1) s2 (f24 s2) a
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s0, s1, t0, s2, a) ->
          f23 s0 (f27 s0) s1 (f28 s1) t0 s2 a
    in f24
  
  (** val se_mutrec :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds ->
      LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm -> 'a2 -> 'a1) ->
      (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ
      -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l ->
      'a3 -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm
      -> 'a1 -> 'a1) -> 'a2 -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) ->
      'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
      'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 ->
      (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
      LLVMsyntax.align -> 'a5) -> ((((sterm -> 'a1)*(list_sterm ->
      'a2))*(list_sterm_l -> 'a3))*(smem -> 'a4))*(sframe -> 'a5) **)
  
  let se_mutrec h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 =
    ((((sterm_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
         h18 h19 h20 h21 h22 h23 h24 h25),(list_sterm_rec2 h1 h2 h3 h4 h5 h6
                                            h7 h8 h9 h10 h11 h12 h13 h14 h15
                                            h16 h17 h18 h19 h20 h21 h22 h23
                                            h24 h25)),
      (list_sterm_l_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        h16 h17 h18 h19 h20 h21 h22 h23 h24 h25)),(smem_rec2 h1 h2 h3 h4 h5
                                                  h6 h7 h8 h9 h10 h11 h12 h13
                                                  h14 h15 h16 h17 h18 h19 h20
                                                  h21 h22 h23 h24 h25)),
      (sframe_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
        h18 h19 h20 h21 h22 h23 h24 h25)
  
  (** val map_list_sterm : (sterm -> 'a1) -> list_sterm -> 'a1 list **)
  
  let rec map_list_sterm f = function
    | Nil_list_sterm -> []
    | Cons_list_sterm (h, tl_) -> (f h)::(map_list_sterm f tl_)
  
  (** val make_list_sterm : sterm list -> list_sterm **)
  
  let rec make_list_sterm = function
    | [] -> Nil_list_sterm
    | h::tl_ -> Cons_list_sterm (h, (make_list_sterm tl_))
  
  (** val unmake_list_sterm : list_sterm -> sterm list **)
  
  let rec unmake_list_sterm = function
    | Nil_list_sterm -> []
    | Cons_list_sterm (h, tl_) -> h::(unmake_list_sterm tl_)
  
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
    | Nil_list_sterm_l -> []
    | Cons_list_sterm_l (h0, h1, tl_) -> (f h0 h1)::(map_list_sterm_l f tl_)
  
  (** val make_list_sterm_l : (sterm*LLVMsyntax.l) list -> list_sterm_l **)
  
  let rec make_list_sterm_l = function
    | [] -> Nil_list_sterm_l
    | p::tl_ ->
        let h0,h1 = p in Cons_list_sterm_l (h0, h1, (make_list_sterm_l tl_))
  
  (** val unmake_list_sterm_l : list_sterm_l -> (sterm*LLVMsyntax.l) list **)
  
  let rec unmake_list_sterm_l = function
    | Nil_list_sterm_l -> []
    | Cons_list_sterm_l (h0, h1, tl_) -> (h0,h1)::(unmake_list_sterm_l tl_)
  
  (** val nth_list_sterm_l :
      nat -> list_sterm_l -> (sterm*LLVMsyntax.l) option **)
  
  let rec nth_list_sterm_l n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_sterm_l -> None
             | Cons_list_sterm_l (h0, h1, tl_) -> Some (h0,h1))
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
       * (LLVMsyntax.typ*sterm) list
  
  (** val scall_rect :
      (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.tailc ->
      LLVMsyntax.typ -> LLVMsyntax.id -> (LLVMsyntax.typ*sterm) list -> 'a1)
      -> scall -> 'a1 **)
  
  let scall_rect f = function
    | Coq_stmn_call (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
  
  (** val scall_rec :
      (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.tailc ->
      LLVMsyntax.typ -> LLVMsyntax.id -> (LLVMsyntax.typ*sterm) list -> 'a1)
      -> scall -> 'a1 **)
  
  let scall_rec f = function
    | Coq_stmn_call (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
  
  type smap = (AtomImpl.atom*sterm) list
  
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
    { coq_STerms = []; coq_SMem = Coq_smem_init; coq_SFrame =
      Coq_sframe_init; coq_SEffects = [] }
  
  (** val lookupSmap : smap -> LLVMsyntax.id -> sterm **)
  
  let rec lookupSmap sm i0 =
    match sm with
      | [] -> Coq_sterm_val (LLVMsyntax.Coq_value_id i0)
      | p::sm' ->
          let id0,s0 = p in
          if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) i0 id0
          then s0
          else lookupSmap sm' i0
  
  (** val value2Sterm : smap -> LLVMsyntax.value -> sterm **)
  
  let value2Sterm sm v = match v with
    | LLVMsyntax.Coq_value_id i0 -> lookupSmap sm i0
    | LLVMsyntax.Coq_value_const c -> Coq_sterm_val v
  
  (** val list_param__list_typ_subst_sterm :
      LLVMsyntax.params -> smap -> (LLVMsyntax.typ*sterm) list **)
  
  let rec list_param__list_typ_subst_sterm list_param1 sm =
    match list_param1 with
      | [] -> []
      | p::list_param1' ->
          let t0,v = p in
          (t0,(value2Sterm sm v))::(list_param__list_typ_subst_sterm
                                     list_param1' sm)
  
  (** val se_cmd : sstate -> nbranch -> sstate **)
  
  let se_cmd st = function
    | LLVMsyntax.Coq_insn_bop (id0, op0, sz0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_bop (op0, sz0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_extractvalue (id0, t1, v1, cs3) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_extractvalue (t1,
          (value2Sterm st.coq_STerms v1), cs3))); coq_SMem = st.coq_SMem;
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_insertvalue (id0, t1, v1, t2, v2, cs3) ->
        { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_insertvalue (t1,
          (value2Sterm st.coq_STerms v1), t2, (value2Sterm st.coq_STerms v2),
          cs3))); coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame;
        coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_malloc (id0, t1, sz1, al1) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_malloc (st.coq_SMem, t1,
          sz1, al1))); coq_SMem = (Coq_smem_malloc (st.coq_SMem, t1, sz1,
        al1)); coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_free (id0, t0, v0) -> { coq_STerms = st.coq_STerms;
        coq_SMem = (Coq_smem_free (st.coq_SMem, t0,
        (value2Sterm st.coq_STerms v0))); coq_SFrame = st.coq_SFrame;
        coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_alloca (id0, t1, sz1, al1) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_alloca (st.coq_SMem, t1,
          sz1, al1))); coq_SMem = (Coq_smem_alloca (st.coq_SMem, t1, sz1,
        al1)); coq_SFrame = (Coq_sframe_alloca (st.coq_SMem, st.coq_SFrame,
        t1, sz1, al1)); coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_load (id0, t2, v2, align0) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_load (st.coq_SMem, t2,
          (value2Sterm st.coq_STerms v2), align0))); coq_SMem =
        (Coq_smem_load (st.coq_SMem, t2, (value2Sterm st.coq_STerms v2),
        align0)); coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_store (id0, t0, v1, v2, align0) -> { coq_STerms =
        st.coq_STerms; coq_SMem = (Coq_smem_store (st.coq_SMem, t0,
        (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2),
        align0)); coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_gep (id0, inbounds0, t1, v1, lv2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_gep (inbounds0, t1,
          (value2Sterm st.coq_STerms v1),
          (make_list_sterm
            (LLVMsyntax.map_list_value (value2Sterm st.coq_STerms) lv2)))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_ext (id0, op0, t1, v1, t2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_ext (op0, t1,
          (value2Sterm st.coq_STerms v1), t2))); coq_SMem = st.coq_SMem;
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_cast (id0, op0, t1, v1, t2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_cast (op0, t1,
          (value2Sterm st.coq_STerms v1), t2))); coq_SMem = st.coq_SMem;
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_icmp (id0, c0, t0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_icmp (c0, t0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_select (id0, v0, t0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_select
          ((value2Sterm st.coq_STerms v0), t0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_call (id0, noret0, tailc0, rt, fid, lp) ->
        assert false (* absurd case *)
  
  (** val _se_phinodes :
      sstate -> sstate -> LLVMsyntax.phinode list -> sstate **)
  
  let rec _se_phinodes st st0 = function
    | [] -> st
    | p::ps' ->
        let LLVMsyntax.Coq_insn_phi (id0, t0, idls0) = p in
        _se_phinodes { coq_STerms =
          (updateAL st.coq_STerms id0 (Coq_sterm_phi (t0,
            (make_list_sterm_l
              (LLVMsyntax.map_list_value_l (fun v5 l5 ->
                (value2Sterm st.coq_STerms v5),l5) idls0))))); coq_SMem =
          st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
          st.coq_SEffects } st0 ps'
  
  (** val se_phinodes : sstate -> LLVMsyntax.phinode list -> sstate **)
  
  let rec se_phinodes st ps =
    _se_phinodes st st ps
  
  (** val se_cmds : sstate -> nbranch list -> sstate **)
  
  let rec se_cmds st = function
    | [] -> st
    | c::cs' -> se_cmds (se_cmd st c) cs'
  
  (** val se_terminator : sstate -> LLVMsyntax.terminator -> sterminator **)
  
  let se_terminator st = function
    | LLVMsyntax.Coq_insn_return (id0, t0, v0) -> Coq_stmn_return (id0, t0,
        (value2Sterm st.coq_STerms v0))
    | LLVMsyntax.Coq_insn_return_void id0 -> Coq_stmn_return_void id0
    | LLVMsyntax.Coq_insn_br (id0, v0, l1, l2) -> Coq_stmn_br (id0,
        (value2Sterm st.coq_STerms v0), l1, l2)
    | LLVMsyntax.Coq_insn_br_uncond (id0, l0) -> Coq_stmn_br_uncond (id0, l0)
    | LLVMsyntax.Coq_insn_unreachable id0 -> Coq_stmn_unreachable id0
  
  (** val se_call : sstate -> LLVMsyntax.cmd -> scall **)
  
  let se_call st = function
    | LLVMsyntax.Coq_insn_call (i1, n, t0, t1, i2, p) -> Coq_stmn_call (i1,
        n, t0, t1, i2, (list_param__list_typ_subst_sterm p st.coq_STerms))
    | _ -> assert false (* absurd case *)
  
  (** val seffects_denote_trace_rect : 'a1 -> sterm list -> trace -> 'a1 **)
  
  let seffects_denote_trace_rect f l0 t0 =
    f
  
  (** val seffects_denote_trace_rec : 'a1 -> sterm list -> trace -> 'a1 **)
  
  let seffects_denote_trace_rec f l0 t0 =
    f
  
  (** val subst_tt : LLVMsyntax.id -> sterm -> sterm -> sterm **)
  
  let rec subst_tt id0 s0 s = match s with
    | Coq_sterm_val v ->
        (match v with
           | LLVMsyntax.Coq_value_id id1 ->
               if eq_dec0 (eqDec_eq_of_EqDec eqDec_atom) id0 id1
               then s0
               else s
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
    | Coq_sterm_load (m1, t1, s1, align0) -> Coq_sterm_load
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1), align0)
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
    | Coq_smem_load (m1, t1, s1, align0) -> Coq_smem_load
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1), align0)
    | Coq_smem_store (m1, t1, s1, s2, align0) -> Coq_smem_store
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1),
        (subst_tt id0 s0 s2), align0)
  
  (** val subst_mt : smap -> sterm -> sterm **)
  
  let rec subst_mt sm s =
    match sm with
      | [] -> s
      | p::sm' -> let id0,s0 = p in subst_mt sm' (subst_tt id0 s0 s)
  
  (** val subst_mm : smap -> smem -> smem **)
  
  let rec subst_mm sm m =
    match sm with
      | [] -> m
      | p::sm' -> let id0,s0 = p in subst_mm sm' (subst_tm id0 s0 m)
 end

type sterm_dec_prop = SimpleSE.sterm -> bool

type list_sterm_dec_prop = SimpleSE.list_sterm -> bool

type list_sterm_l_dec_prop = SimpleSE.list_sterm_l -> bool

type smem_dec_prop = SimpleSE.smem -> bool

type sframe_dec_prop = SimpleSE.sframe -> bool

(** val se_dec :
    ((((SimpleSE.sterm -> sterm_dec_prop)*(SimpleSE.list_sterm ->
    list_sterm_dec_prop))*(SimpleSE.list_sterm_l ->
    list_sterm_l_dec_prop))*(SimpleSE.smem ->
    smem_dec_prop))*(SimpleSE.sframe -> sframe_dec_prop) **)

let se_dec =
  SimpleSE.se_mutrec (fun v st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_val v0 -> LLVMlib.value_dec v v0
      | _ -> false) (fun b s s0 h s1 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_bop (b0, s2, st2_1, st2_2) ->
          let s3 = LLVMlib.bop_dec b b0 in
          if s3
          then let s4 = LLVMlib.sz_dec s s2 in
               if s4
               then let s5 = h st2_1 in if s5 then h0 st2_2 else false
               else false
          else false
      | _ -> false) (fun t0 s h l0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_extractvalue (t1, st3, l1) ->
          let s0 = LLVMlib.typ_dec t0 t1 in
          if s0
          then let s1 = h st3 in
               if s1 then LLVMlib.list_const_dec l0 l1 else false
          else false
      | _ -> false) (fun t0 s h t1 s0 h0 l0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_insertvalue (t2, st2_1, t3, st2_2, l1) ->
          let s1 = LLVMlib.typ_dec t0 t2 in
          if s1
          then let s2 = h st2_1 in
               if s2
               then let s3 = LLVMlib.typ_dec t1 t3 in
                    if s3
                    then let s4 = h0 st2_2 in
                         if s4 then LLVMlib.list_const_dec l0 l1 else false
                    else false
               else false
          else false
      | _ -> false) (fun s h t0 s0 a st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_malloc (s1, t1, s2, a0) ->
          let s3 = h s1 in
          if s3
          then let s4 = LLVMlib.typ_dec t0 t1 in
               if s4
               then let s5 = LLVMlib.sz_dec s0 s2 in
                    if s5 then LLVMlib.align_dec a a0 else false
               else false
          else false
      | _ -> false) (fun s h t0 s0 a st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_alloca (s1, t1, s2, a0) ->
          let s3 = h s1 in
          if s3
          then let s4 = LLVMlib.typ_dec t0 t1 in
               if s4
               then let s5 = LLVMlib.sz_dec s0 s2 in
                    if s5 then LLVMlib.align_dec a a0 else false
               else false
          else false
      | _ -> false) (fun s h t0 s0 h0 a st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_load (s1, t1, st3, a0) ->
          let s2 = h s1 in
          if s2
          then let s3 = LLVMlib.typ_dec t0 t1 in
               if s3
               then let s4 = LLVMlib.align_dec a a0 in
                    if s4 then h0 st3 else false
               else false
          else false
      | _ -> false) (fun i0 t0 s h l0 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_gep (i1, t1, st3, l1) ->
          let s0 = bool_dec i0 i1 in
          if s0
          then let s1 = LLVMlib.typ_dec t0 t1 in
               if s1
               then let s2 = h st3 in if s2 then h0 l1 else false
               else false
          else false
      | _ -> false) (fun e t0 s h t1 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_ext (e0, t2, st3, t3) ->
          let s0 = LLVMlib.extop_dec e e0 in
          if s0
          then let s1 = LLVMlib.typ_dec t0 t2 in
               if s1
               then let s2 = h st3 in
                    if s2 then LLVMlib.typ_dec t1 t3 else false
               else false
          else false
      | _ -> false) (fun c t0 s h t1 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_cast (c0, t2, st3, t3) ->
          let s0 = LLVMlib.castop_dec c c0 in
          if s0
          then let s1 = LLVMlib.typ_dec t0 t2 in
               if s1
               then let s2 = h st3 in
                    if s2 then LLVMlib.typ_dec t1 t3 else false
               else false
          else false
      | _ -> false) (fun c t0 s h s0 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_icmp (c0, t1, st2_1, st2_2) ->
          let s1 = LLVMlib.cond_dec c c0 in
          if s1
          then let s2 = LLVMlib.typ_dec t0 t1 in
               if s2
               then let s3 = h st2_1 in if s3 then h0 st2_2 else false
               else false
          else false
      | _ -> false) (fun t0 l0 h st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_phi (t1, l1) ->
          let s = LLVMlib.typ_dec t0 t1 in if s then h l1 else false
      | _ -> false) (fun s h t0 s0 h0 s1 h1 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_select (st2_1, t1, st2_2, st2_3) ->
          let s2 = LLVMlib.typ_dec t0 t1 in
          if s2
          then let s3 = h st2_1 in
               if s3
               then let s4 = h0 st2_2 in if s4 then h1 st2_3 else false
               else false
          else false
      | _ -> false) (fun sts2 ->
    match sts2 with
      | SimpleSE.Nil_list_sterm -> true
      | SimpleSE.Cons_list_sterm (s, sts3) -> false) (fun s h l0 h0 sts2 ->
    match sts2 with
      | SimpleSE.Nil_list_sterm -> false
      | SimpleSE.Cons_list_sterm (s0, sts3) ->
          let s1 = h s0 in if s1 then h0 sts3 else false) (fun stls2 ->
    match stls2 with
      | SimpleSE.Nil_list_sterm_l -> true
      | SimpleSE.Cons_list_sterm_l (s, l0, stls3) -> false)
    (fun s h l0 l1 h0 stls2 ->
    match stls2 with
      | SimpleSE.Nil_list_sterm_l -> false
      | SimpleSE.Cons_list_sterm_l (s0, l2, stls3) ->
          let s1 = h s0 in
          if s1
          then let s2 = LLVMlib.l_dec l0 l2 in if s2 then h0 stls3 else false
          else false) (fun sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_init -> true
      | _ -> false) (fun s h t0 s0 a sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_malloc (sm3, t1, s1, a0) ->
          let s2 = h sm3 in
          if s2
          then let s3 = LLVMlib.typ_dec t0 t1 in
               if s3
               then let s4 = LLVMlib.sz_dec s0 s1 in
                    if s4 then LLVMlib.align_dec a a0 else false
               else false
          else false
      | _ -> false) (fun s h t0 s0 h0 sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_free (sm3, t1, s1) ->
          let s2 = h sm3 in
          if s2
          then let s3 = LLVMlib.typ_dec t0 t1 in if s3 then h0 s1 else false
          else false
      | _ -> false) (fun s h t0 s0 a sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_alloca (sm3, t1, s1, a0) ->
          let s2 = h sm3 in
          if s2
          then let s3 = LLVMlib.typ_dec t0 t1 in
               if s3
               then let s4 = LLVMlib.sz_dec s0 s1 in
                    if s4 then LLVMlib.align_dec a a0 else false
               else false
          else false
      | _ -> false) (fun s h t0 s0 h0 a sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_load (sm3, t1, s1, a0) ->
          let s2 = h sm3 in
          if s2
          then let s3 = LLVMlib.typ_dec t0 t1 in
               if s3
               then let s4 = LLVMlib.align_dec a a0 in
                    if s4 then h0 s1 else false
               else false
          else false
      | _ -> false) (fun s h t0 s0 h0 s1 h1 a sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_store (sm3, t1, s2, s3, a0) ->
          let s4 = h sm3 in
          if s4
          then let s5 = LLVMlib.typ_dec t0 t1 in
               if s5
               then let s6 = LLVMlib.align_dec a a0 in
                    if s6
                    then let s7 = h0 s2 in if s7 then h1 s3 else false
                    else false
               else false
          else false
      | _ -> false) (fun sf2 ->
    match sf2 with
      | SimpleSE.Coq_sframe_init -> true
      | SimpleSE.Coq_sframe_alloca (s, sf3, t0, s0, a) -> false)
    (fun s h s0 h0 t0 s1 a sf2 ->
    match sf2 with
      | SimpleSE.Coq_sframe_init -> false
      | SimpleSE.Coq_sframe_alloca (s2, sf3, t1, s3, a0) ->
          let s4 = h s2 in
          if s4
          then let s5 = h0 sf3 in
               if s5
               then let s6 = LLVMlib.typ_dec t0 t1 in
                    if s6
                    then let s7 = LLVMlib.sz_dec s1 s3 in
                         if s7 then LLVMlib.align_dec a a0 else false
                    else false
               else false
          else false)

(** val sterm_dec : SimpleSE.sterm -> SimpleSE.sterm -> bool **)

let sterm_dec =
  let p,x = se_dec in let p0,x0 = p in let p1,x1 = p0 in let h,l0 = p1 in h

(** val smem_dec : SimpleSE.smem -> SimpleSE.smem -> bool **)

let smem_dec =
  let p,x = se_dec in let p0,h = p in h

(** val sframe_dec : SimpleSE.sframe -> SimpleSE.sframe -> bool **)

let sframe_dec =
  let p,h = se_dec in h

(** val smap_dec : SimpleSE.smap -> SimpleSE.smap -> bool **)

let rec smap_dec l0 sm0 =
  match l0 with
    | [] -> (match sm0 with
               | [] -> true
               | p::l1 -> false)
    | y::l1 ->
        (match sm0 with
           | [] -> false
           | p::l2 ->
               if let a,s = y in
                  let a0,s0 = p in
                  let s1 = LLVMlib.id_dec a a0 in
                  if s1 then sterm_dec s s0 else false
               then smap_dec l1 l2
               else false)

(** val sterms_dec : SimpleSE.sterm list -> SimpleSE.sterm list -> bool **)

let rec sterms_dec l0 ts0 =
  match l0 with
    | [] -> (match ts0 with
               | [] -> true
               | s::l1 -> false)
    | y::l1 ->
        (match ts0 with
           | [] -> false
           | s::l2 -> if sterm_dec y s then sterms_dec l1 l2 else false)

(** val sstate_dec : SimpleSE.sstate -> SimpleSE.sstate -> bool **)

let sstate_dec sts1 sts2 =
  let { SimpleSE.coq_STerms = x; SimpleSE.coq_SMem = x0;
    SimpleSE.coq_SFrame = x1; SimpleSE.coq_SEffects = x2 } = sts1
  in
  let { SimpleSE.coq_STerms = sTerms1; SimpleSE.coq_SMem = sMem1;
    SimpleSE.coq_SFrame = sFrame1; SimpleSE.coq_SEffects = sEffects1 } = sts2
  in
  if smap_dec x sTerms1
  then if smem_dec x0 sMem1
       then if sframe_dec x1 sFrame1 then sterms_dec x2 sEffects1 else false
       else false
  else false

(** val tv_cmds : SimpleSE.nbranch list -> SimpleSE.nbranch list -> bool **)

let tv_cmds nbs1 nbs2 =
  LLVMlib.sumbool2bool
    (sstate_dec (SimpleSE.se_cmds SimpleSE.sstate_init nbs1)
      (SimpleSE.se_cmds SimpleSE.sstate_init nbs2))

(** val tv_subblock : SimpleSE.subblock -> SimpleSE.subblock -> bool **)

let tv_subblock sb1 sb2 =
  let { SimpleSE.coq_NBs = nbs1; SimpleSE.call_cmd = call1 } = sb1 in
  let { SimpleSE.coq_NBs = nbs2; SimpleSE.call_cmd = call2 } = sb2 in
  let st1 = SimpleSE.se_cmds SimpleSE.sstate_init nbs1 in
  let st2 = SimpleSE.se_cmds SimpleSE.sstate_init nbs2 in
  if LLVMlib.sumbool2bool (sstate_dec st1 st2)
  then LLVMlib.sumbool2bool (LLVMlib.cmd_dec call1 call2)
  else false

(** val tv_subblocks :
    SimpleSE.subblock list -> SimpleSE.subblock list -> bool **)

let rec tv_subblocks sbs1 sbs2 =
  match sbs1 with
    | [] -> (match sbs2 with
               | [] -> true
               | s::l0 -> false)
    | sb1::sbs1' ->
        (match sbs2 with
           | [] -> false
           | sb2::sbs2' ->
               if tv_subblock sb1 sb2
               then tv_subblocks sbs1' sbs2'
               else false)

(** val tv_phinodes : LLVMsyntax.phinodes -> LLVMsyntax.phinodes -> bool **)

let rec tv_phinodes ps1 ps2 =
  match ps1 with
    | [] -> (match ps2 with
               | [] -> true
               | p::l0 -> false)
    | p1::ps1' ->
        (match ps2 with
           | [] -> false
           | p2::ps2' ->
               if LLVMlib.sumbool2bool (LLVMlib.phinode_dec p1 p2)
               then tv_phinodes ps1' ps2'
               else false)

(** val tv_block : LLVMsyntax.block -> LLVMsyntax.block -> bool **)

let tv_block b1 b2 =
  let LLVMsyntax.Coq_block_intro (l1, ps1, cs1, tmn1) = b1 in
  let LLVMsyntax.Coq_block_intro (l2, ps2, cs2, tmn2) = b2 in
  let p = SimpleSE.cmds2sbs cs1 in
  let p0 = SimpleSE.cmds2sbs cs2 in
  let sbs1,nbs1 = p in
  let sbs2,nbs2 = p0 in
  if if if if LLVMlib.sumbool2bool (AtomImpl.eq_atom_dec l1 l2)
           then tv_phinodes ps1 ps2
           else false
        then tv_subblocks sbs1 sbs2
        else false
     then tv_cmds nbs1 nbs2
     else false
  then LLVMlib.sumbool2bool (LLVMlib.terminator_dec tmn1 tmn2)
  else false

(** val tv_blocks : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool **)

let rec tv_blocks bs1 bs2 =
  match bs1 with
    | [] -> (match bs2 with
               | [] -> true
               | b::l0 -> false)
    | b1::bs1' ->
        (match bs2 with
           | [] -> false
           | b2::bs2' ->
               if tv_block b1 b2 then tv_blocks bs1' bs2' else false)

(** val tv_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool **)

let tv_fdef f1 f2 =
  let LLVMsyntax.Coq_fdef_intro (fh1, lb1) = f1 in
  let LLVMsyntax.Coq_fdef_intro (fh2, lb2) = f2 in
  if LLVMlib.sumbool2bool (LLVMlib.fheader_dec fh1 fh2)
  then tv_blocks lb1 lb2
  else false

(** val tv_products : LLVMsyntax.products -> LLVMsyntax.products -> bool **)

let rec tv_products ps1 ps2 =
  match ps1 with
    | [] -> (match ps2 with
               | [] -> true
               | p::l0 -> false)
    | p::ps1' ->
        (match p with
           | LLVMsyntax.Coq_product_gvar gvar1 ->
               (match ps2 with
                  | [] -> false
                  | p0::ps2' ->
                      (match p0 with
                         | LLVMsyntax.Coq_product_gvar gvar2 ->
                             if LLVMlib.sumbool2bool
                                  (LLVMlib.gvar_dec gvar1 gvar2)
                             then tv_products ps1' ps2'
                             else false
                         | _ -> false))
           | LLVMsyntax.Coq_product_fdec f1 ->
               (match ps2 with
                  | [] -> false
                  | p0::ps2' ->
                      (match p0 with
                         | LLVMsyntax.Coq_product_fdec f2 ->
                             if LLVMlib.sumbool2bool (LLVMlib.fdec_dec f1 f2)
                             then tv_products ps1' ps2'
                             else false
                         | _ -> false))
           | LLVMsyntax.Coq_product_fdef f1 ->
               (match ps2 with
                  | [] -> false
                  | p0::ps2' ->
                      (match p0 with
                         | LLVMsyntax.Coq_product_fdef f2 ->
                             if tv_fdef f1 f2
                             then tv_products ps1' ps2'
                             else false
                         | _ -> false)))

(** val tv_module :
    LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool **)

let tv_module m1 m2 =
  let LLVMsyntax.Coq_module_intro (tD1, ps1) = m1 in
  let LLVMsyntax.Coq_module_intro (tD2, ps2) = m2 in
  if LLVMlib.sumbool2bool (LLVMlib.layouts_dec tD1 tD2)
  then tv_products ps1 ps2
  else false

(** val tv_system : LLVMsyntax.system -> LLVMsyntax.system -> bool **)

let rec tv_system s1 s2 =
  match s1 with
    | [] -> (match s2 with
               | [] -> true
               | m::l0 -> false)
    | m1::s1' ->
        (match s2 with
           | [] -> false
           | m2::s2' -> if tv_module m1 m2 then tv_system s1' s2' else false)

