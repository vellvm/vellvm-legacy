type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
  | Tt

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

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
  | x , y -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
  | x , y -> y

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

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
    | O -> m
    | S n' -> (match m with
                 | O -> n
                 | S m' -> S (max n' m'))

(** val bool_dec : bool -> bool -> bool **)

let bool_dec b1 b2 =
  if b1 then if b2 then true else false else if b2 then false else true

(** val length : 'a1 list -> nat **)

let rec length = function
  | [] -> O
  | a :: m -> S (length m)

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l0 m =
  match l0 with
    | [] -> m
    | a :: l1 -> a :: (app l1 m)

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
  | [] -> false
  | a0 :: l1 -> if h a0 a then true else in_dec h a l1

(** val nth_error : 'a1 list -> nat -> 'a1 exc **)

let rec nth_error l0 = function
  | O -> (match l0 with
            | [] -> error
            | x :: l1 -> value x)
  | S n0 -> (match l0 with
               | [] -> error
               | a :: l1 -> nth_error l1 n0)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
  | [] -> []
  | x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
  | [] -> []
  | a :: t0 -> (f a) :: (map f t0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l0 a0 =
  match l0 with
    | [] -> a0
    | b :: t0 -> fold_left f t0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
  | [] -> a0
  | b :: t0 -> f b (fold_right f a0 t0)

type 'a set = 'a list

(** val empty_set : 'a1 set **)

let empty_set =
  []

(** val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
  | [] -> a :: []
  | a1 :: x1 ->
      if aeq_dec a a1 then a1 :: x1 else a1 :: (set_add aeq_dec a x1)

(** val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool **)

let rec set_mem aeq_dec a = function
  | [] -> false
  | a1 :: x1 -> if aeq_dec a a1 then true else set_mem aeq_dec a x1

(** val set_inter : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_inter aeq_dec x x0 =
  match x with
    | [] -> []
    | a1 :: x1 ->
        if set_mem aeq_dec a1 x0
        then a1 :: (set_inter aeq_dec x1 x0)
        else set_inter aeq_dec x1 x0

(** val set_union : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_union aeq_dec x = function
  | [] -> x
  | a1 :: y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)

module type DecidableType = 
 sig 
  type t 
  
  val eq_dec : t -> t -> bool
 end

module type UsualDecidableType = 
 sig 
  type t 
  
  val eq_dec : t -> t -> bool
 end

module WFacts_fun = 
 functor (E:DecidableType) ->
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
  
  val partition : (elt -> bool) -> t -> t * t
  
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
 functor (E:DecidableType) ->
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
  
  val partition : (elt -> bool) -> t -> t * t
  
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
 functor (E:DecidableType) ->
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
  
  val partition : (elt -> bool) -> t -> t * t
  
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
  
  let to_list x =
    M.elements x
  
  (** val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
      'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2 **)
  
  let fold_rec f i0 s pempty pstep =
    let rec f0 l0 pstep' s0 =
      match l0 with
        | [] -> pempty s0 __
        | a :: l1 ->
            pstep' a (fold_right f i0 l1) (of_list l1) s0 __ __ __
              (f0 l1 (fun x a0 s' s'' _ _ _ x0 ->
                pstep' x a0 s' s'' __ __ __ x0) (of_list l1))
    in f0 (rev (M.elements s)) (fun x a s' s'' _ _ _ x0 ->
         pstep x a s' s'' __ __ __ x0) s
  
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
    let rec f0 l0 rstep' =
      match l0 with
        | [] -> rempty
        | a :: l1 ->
            rstep' a (fold_right f i0 l1) (fold_right g j l1) __
              (f0 l1 (fun x a0 b _ x0 -> rstep' x a0 b __ x0))
    in f0 (rev (M.elements s)) (fun x a b _ x0 -> rstep x a b __ x0)
  
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
    match M.elements s with
      | [] -> assert false (* absurd case *)
      | e :: l0 -> e
  
  (** val cardinal_inv_2b : M.t -> M.elt **)
  
  let cardinal_inv_2b s =
    match M.cardinal s with
      | O -> assert false (* absurd case *)
      | S n ->
          (match M.elements s with
             | [] -> assert false (* absurd case *)
             | e :: l0 -> e)
 end

module Raw = 
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
    | x :: x0 -> false
  
  (** val mem : elt -> t -> bool **)
  
  let rec mem x = function
    | [] -> false
    | y :: l0 -> if X.eq_dec x y then true else mem x l0
  
  (** val add : elt -> t -> t **)
  
  let rec add x s = match s with
    | [] -> x :: []
    | y :: l0 -> if X.eq_dec x y then s else y :: (add x l0)
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    x :: []
  
  (** val remove : elt -> t -> t **)
  
  let rec remove x = function
    | [] -> []
    | y :: l0 -> if X.eq_dec x y then l0 else y :: (remove x l0)
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let rec fold f s i0 =
    match s with
      | [] -> i0
      | x :: l0 -> fold f l0 (f x i0)
  
  (** val union : t -> t -> t **)
  
  let union s x =
    fold add s x
  
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
    | x :: l0 -> if f x then x :: (filter f l0) else filter f l0
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let rec for_all f = function
    | [] -> true
    | x :: l0 -> if f x then for_all f l0 else false
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let rec exists_ f = function
    | [] -> false
    | x :: l0 -> if f x then true else exists_ f l0
  
  (** val partition : (elt -> bool) -> t -> t * t **)
  
  let rec partition f = function
    | [] -> [] , []
    | x :: l0 ->
        let s1 , s2 = partition f l0 in
        if f x then (x :: s1) , s2 else s1 , (x :: s2)
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    length s
  
  (** val elements : t -> elt list **)
  
  let elements s =
    s
  
  (** val choose : t -> elt option **)
  
  let choose = function
    | [] -> None
    | x :: l0 -> Some x
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec s s' =
    if equal s s' then true else false
 end

module Coq_WDecide_fun = 
 functor (E:DecidableType) ->
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
  
  val partition : (elt -> bool) -> t -> t * t
  
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

module Make = 
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
  
  val partition : (elt -> bool) -> t -> t * t
  
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
    item :: []
  
  (** val dom : (X.t * 'a1) list -> KeySet.t **)
  
  let rec dom = function
    | [] -> KeySet.empty
    | p :: e' -> let x , y = p in KeySet.add x (dom e')
  
  (** val get : X.t -> (X.t * 'a1) list -> 'a1 option **)
  
  let rec get x = function
    | [] -> None
    | p :: f -> let y , c = p in if X.eq_dec x y then Some c else get x f
  
  (** val map : ('a1 -> 'a2) -> (X.t * 'a1) list -> (X.t * 'a2) list **)
  
  let map f e =
    map (fun b -> let x , a = b in x , (f a)) e
  
  (** val alist_ind :
      'a2 -> (X.t -> 'a1 -> (X.t * 'a1) list -> 'a2 -> 'a2) -> (X.t * 'a1)
      list -> 'a2 **)
  
  let rec alist_ind x x0 = function
    | [] -> x
    | a :: l0 -> let x1 , a0 = a in x0 x1 a0 l0 (alist_ind x x0 l0)
  
  (** val binds_dec :
      X.t -> 'a1 -> (X.t * 'a1) list -> ('a1 -> 'a1 -> bool) -> bool **)
  
  let binds_dec x a e x0 =
    in_dec (fun x1 y ->
      let x2 , x3 = x1 in
      let t0 , a1 = y in if X.eq_dec x2 t0 then x0 x3 a1 else false) (x , a)
      e
  
  (** val binds_lookup : X.t -> (X.t * 'a1) list -> ('a1, __) sum **)
  
  let binds_lookup x e =
    alist_ind (Inr __) (fun x1 a1 l0 x0 ->
      match x0 with
        | Inl s -> Inl s
        | Inr _ -> if X.eq_dec x x1 then Inl a1 else Inr __) e
 end

type 'a eqDec = 'a -> 'a -> bool

type 'a eqDec_eq = 'a -> 'a -> bool

module Coq_Make = 
 functor (X:DecidableType) ->
 struct 
  module Raw = Raw(X)
  
  module E = X
  
  type slist =
    Raw.t
    (* singleton inductive, whose constructor was Build_slist *)
  
  (** val slist_rect : (Raw.t -> __ -> 'a1) -> slist -> 'a1 **)
  
  let slist_rect f s =
    f s __
  
  (** val slist_rec : (Raw.t -> __ -> 'a1) -> slist -> 'a1 **)
  
  let slist_rec f s =
    f s __
  
  (** val this : slist -> Raw.t **)
  
  let this s =
    s
  
  type t = slist
  
  type elt = X.t
  
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
  
  let fold f s x =
    Raw.fold f (this s) x
  
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
  
  (** val partition : (elt -> bool) -> t -> t * t **)
  
  let partition f s =
    let p = Raw.partition f (this s) in (fst p) , (snd p)
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec s s' =
    Raw.eq_dec (this s) (this s')
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
    | a :: l1 -> max a (nat_list_max l1)
  
  (** val atom_fresh_for_list : atom list -> atom **)
  
  let atom_fresh_for_list = Symexe_aux.atom_fresh_for_list
 end

module AtomDT = 
 struct 
  type t = AtomImpl.atom
  
  (** val eq_dec : AtomImpl.atom -> AtomImpl.atom -> bool **)
  
  let eq_dec x y =
    AtomImpl.eq_atom_dec x y
 end

(** val eqDec_atom : AtomImpl.atom eqDec **)

let eqDec_atom x y =
  AtomImpl.eq_atom_dec x y

module AtomSetImpl = Coq_Make(AtomDT)

module EnvImpl = Make(AtomDT)(AtomSetImpl)

type 'x assocList = (AtomImpl.atom * 'x) list

(** val updateAddAL :
    'a1 assocList -> AtomImpl.atom -> 'a1 -> 'a1 assocList **)

let rec updateAddAL m i0 gv =
  match m with
    | [] -> (i0 , gv) :: []
    | p :: m' ->
        let i' , gv' = p in
        if eqDec_atom i0 i'
        then (i' , gv) :: m'
        else (i' , gv') :: (updateAddAL m' i0 gv)

(** val updateAL : 'a1 assocList -> AtomImpl.atom -> 'a1 -> 'a1 assocList **)

let rec updateAL m i0 gv =
  match m with
    | [] -> []
    | p :: m' ->
        let i' , gv' = p in
        if eqDec_atom i0 i'
        then (i' , gv) :: m'
        else (i' , gv') :: (updateAL m' i0 gv)

(** val lookupAL : 'a1 assocList -> AtomImpl.atom -> 'a1 option **)

let rec lookupAL m i0 =
  match m with
    | [] -> None
    | p :: m' ->
        let i' , gv' = p in
        if eqDec_atom i0 i' then Some gv' else lookupAL m' i0

module LLVMsyntax = 
 struct 
  (** val last_opt : 'a1 list -> 'a1 option **)
  
  let rec last_opt = function
    | [] -> None
    | a :: l' -> (match l' with
                    | [] -> Some a
                    | a0 :: l1 -> last_opt l')
  
  type coq_INT = Llvm.llapint
  
  type id = String.t
  
  type l = String.t
  
  type align = int
  
  type sz = int
  
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
    | Coq_typ_array (s, t1) -> f3 s t1 (typ_rect f f0 f1 f2 f3 f4 f5 f6 t1)
    | Coq_typ_function (t1, l0) ->
        f4 t1 (typ_rect f f0 f1 f2 f3 f4 f5 f6 t1) l0
    | Coq_typ_struct l0 -> f5 l0
    | Coq_typ_pointer t1 -> f6 t1 (typ_rect f f0 f1 f2 f3 f4 f5 f6 t1)
  
  (** val typ_rec :
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ
      -> 'a1 -> list_typ -> 'a1) -> (list_typ -> 'a1) -> (typ -> 'a1 -> 'a1)
      -> typ -> 'a1 **)
  
  let rec typ_rec f f0 f1 f2 f3 f4 f5 f6 = function
    | Coq_typ_int s -> f s
    | Coq_typ_void -> f0
    | Coq_typ_label -> f1
    | Coq_typ_metadata -> f2
    | Coq_typ_array (s, t1) -> f3 s t1 (typ_rec f f0 f1 f2 f3 f4 f5 f6 t1)
    | Coq_typ_function (t1, l0) ->
        f4 t1 (typ_rec f f0 f1 f2 f3 f4 f5 f6 t1) l0
    | Coq_typ_struct l0 -> f5 l0
    | Coq_typ_pointer t1 -> f6 t1 (typ_rec f f0 f1 f2 f3 f4 f5 f6 t1)
  
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
  
  type param = typ * value
  
  type params = (typ * value) list
  
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
  
  type arg = typ * id
  
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
  
  type args = (typ * id) list
  
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
  
  type module_info = coq_module * (usedef_id * usedef_block)
  
  type fdef_info = fdef * dt
  
  type intrinsic_funs = ids
  
  (** val map_list_value_l :
      (value -> l -> 'a1) -> list_value_l -> 'a1 list **)
  
  let rec map_list_value_l f = function
    | Nil_list_value_l -> []
    | Cons_list_value_l (h0, h1, tl_) -> (f h0 h1) ::
        (map_list_value_l f tl_)
  
  (** val make_list_value_l : (value * l) list -> list_value_l **)
  
  let rec make_list_value_l = function
    | [] -> Nil_list_value_l
    | p :: tl_ ->
        let h0 , h1 = p in
        Cons_list_value_l (h0, h1, (make_list_value_l tl_))
  
  (** val unmake_list_value_l : list_value_l -> (value * l) list **)
  
  let rec unmake_list_value_l = function
    | Nil_list_value_l -> []
    | Cons_list_value_l (h0, h1, tl_) -> (h0 , h1) ::
        (unmake_list_value_l tl_)
  
  (** val nth_list_value_l : nat -> list_value_l -> (value * l) option **)
  
  let rec nth_list_value_l n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_value_l -> None
             | Cons_list_value_l (h0, h1, tl_) -> Some (h0 , h1))
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
    | Cons_list_value (h, tl_) -> (f h) :: (map_list_value f tl_)
  
  (** val make_list_value : value list -> list_value **)
  
  let rec make_list_value = function
    | [] -> Nil_list_value
    | h :: tl_ -> Cons_list_value (h, (make_list_value tl_))
  
  (** val unmake_list_value : list_value -> value list **)
  
  let rec unmake_list_value = function
    | Nil_list_value -> []
    | Cons_list_value (h, tl_) -> h :: (unmake_list_value tl_)
  
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
    | Cons_list_const (h, tl_) -> (f h) :: (map_list_const f tl_)
  
  (** val make_list_const : const list -> list_const **)
  
  let rec make_list_const = function
    | [] -> Nil_list_const
    | h :: tl_ -> Cons_list_const (h, (make_list_const tl_))
  
  (** val unmake_list_const : list_const -> const list **)
  
  let rec unmake_list_const = function
    | Nil_list_const -> []
    | Cons_list_const (h, tl_) -> h :: (unmake_list_const tl_)
  
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
    | Cons_list_typ (h, tl_) -> (f h) :: (map_list_typ f tl_)
  
  (** val make_list_typ : typ list -> list_typ **)
  
  let rec make_list_typ = function
    | [] -> Nil_list_typ
    | h :: tl_ -> Cons_list_typ (h, (make_list_typ tl_))
  
  (** val unmake_list_typ : list_typ -> typ list **)
  
  let rec unmake_list_typ = function
    | Nil_list_typ -> []
    | Cons_list_typ (h, tl_) -> h :: (unmake_list_typ tl_)
  
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
      | Coq_const_undef t0 -> f0 t0
      | Coq_const_null t0 -> f1 t0
      | Coq_const_arr l1 -> f2 l1 (f8 l1)
      | Coq_const_struct l1 -> f3 l1 (f8 l1)
      | Coq_const_gid (t0, i0) -> f4 t0 i0
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
      | Coq_const_undef t0 -> f0 t0
      | Coq_const_null t0 -> f1 t0
      | Coq_const_arr l0 -> f2 l0 (f8 l0)
      | Coq_const_struct l0 -> f3 l0 (f8 l0)
      | Coq_const_gid (t0, i0) -> f4 t0 i0
    and f8 = function
      | Nil_list_const -> f5
      | Cons_list_const (c0, l1) -> f6 c0 (f7 c0) l1 (f8 l1)
    in f7 c
  
  (** val const_mutrec :
      (sz -> coq_INT -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (list_const
      -> 'a2 -> 'a1) -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) ->
      'a2 -> (const -> 'a1 -> list_const -> 'a2 -> 'a2) -> (const -> 'a1) *
      (list_const -> 'a2) **)
  
  let const_mutrec h1 h2 h3 h4 h5 h6 h7 h8 =
    (fun x -> const_rec2 h1 h2 h3 h4 h5 h6 h7 h8 x) , (fun x ->
      list_const_rec2 h1 h2 h3 h4 h5 h6 h7 h8 x)
  
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
      | Coq_typ_array (s, t1) -> f3 s t1 (f9 t1)
      | Coq_typ_function (t1, l1) -> f4 t1 (f9 t1) l1 (f10 l1)
      | Coq_typ_struct l1 -> f5 l1 (f10 l1)
      | Coq_typ_pointer t1 -> f6 t1 (f9 t1)
    and f10 = function
      | Nil_list_typ -> f7
      | Cons_list_typ (t0, l2) -> f8 t0 (f9 t0) l2 (f10 l2)
    in f10 l0
  
  (** val typ_rec2 :
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ
      -> 'a1 -> list_typ -> 'a2 -> 'a1) -> (list_typ -> 'a2 -> 'a1) -> (typ
      -> 'a1 -> 'a1) -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> typ
      -> 'a1 **)
  
  let typ_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 t0 =
    let rec f9 = function
      | Coq_typ_int s -> f s
      | Coq_typ_void -> f0
      | Coq_typ_label -> f1
      | Coq_typ_metadata -> f2
      | Coq_typ_array (s, t2) -> f3 s t2 (f9 t2)
      | Coq_typ_function (t2, l0) -> f4 t2 (f9 t2) l0 (f10 l0)
      | Coq_typ_struct l0 -> f5 l0 (f10 l0)
      | Coq_typ_pointer t2 -> f6 t2 (f9 t2)
    and f10 = function
      | Nil_list_typ -> f7
      | Cons_list_typ (t1, l1) -> f8 t1 (f9 t1) l1 (f10 l1)
    in f9 t0
  
  (** val typ_mutrec :
      (sz -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz -> typ -> 'a1 -> 'a1) -> (typ
      -> 'a1 -> list_typ -> 'a2 -> 'a1) -> (list_typ -> 'a2 -> 'a1) -> (typ
      -> 'a1 -> 'a1) -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> (typ
      -> 'a1) * (list_typ -> 'a2) **)
  
  let typ_mutrec h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =
    (fun x -> typ_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 x) , (fun x ->
      list_typ_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 x)
 end

module LLVMlib = 
 struct 
  (** val id_dec : LLVMsyntax.id -> LLVMsyntax.id -> bool **)
  
  let id_dec x y =
    AtomImpl.eq_atom_dec x y
  
  (** val l_dec : LLVMsyntax.l -> LLVMsyntax.l -> bool **)
  
  let l_dec x y =
    AtomImpl.eq_atom_dec x y
  
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
  
  (** val nat2INT : nat -> LLVMsyntax.coq_INT **)
  
  let nat2INT = Symexe_aux.nat2llapint
  
  (** val lempty_set : LLVMsyntax.l set **)
  
  let lempty_set =
    empty_set
  
  (** val lset_add : LLVMsyntax.l -> LLVMsyntax.ls -> LLVMsyntax.l set **)
  
  let lset_add l1 ls2 =
    set_add (fun x x0 -> eqDec_atom x x0) l1 ls2
  
  (** val lset_union : LLVMsyntax.ls -> LLVMsyntax.ls -> LLVMsyntax.l set **)
  
  let lset_union ls1 ls2 =
    set_union (fun x x0 -> eqDec_atom x x0) ls1 ls2
  
  (** val lset_inter : LLVMsyntax.ls -> LLVMsyntax.ls -> LLVMsyntax.l set **)
  
  let lset_inter ls1 ls2 =
    set_inter (fun x x0 -> eqDec_atom x x0) ls1 ls2
  
  (** val lset_eq : LLVMsyntax.ls -> LLVMsyntax.ls -> bool **)
  
  let lset_eq ls1 ls2 =
    match lset_inter ls1 ls2 with
      | [] -> true
      | l0 :: l1 -> false
  
  (** val lset_neq : LLVMsyntax.ls -> LLVMsyntax.ls -> bool **)
  
  let lset_neq ls1 ls2 =
    match lset_inter ls1 ls2 with
      | [] -> false
      | l0 :: l1 -> true
  
  (** val lset_single : LLVMsyntax.l -> LLVMsyntax.l set **)
  
  let lset_single l0 =
    lset_add l0 lempty_set
  
  (** val lset_mem : LLVMsyntax.l -> LLVMsyntax.ls -> bool **)
  
  let lset_mem l0 ls0 =
    set_mem (fun x x0 -> eqDec_atom x x0) l0 ls0
  
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
             | LLVMsyntax.Coq_typ_struct lt ->
                 (match idx with
                    | LLVMsyntax.Coq_const_int (sz0, i0) ->
                        (match LLVMsyntax.nth_list_typ (coq_INT2nat i0) lt with
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
             | LLVMsyntax.Coq_typ_struct lt ->
                 (match idx with
                    | LLVMsyntax.Coq_value_id i0 -> None
                    | LLVMsyntax.Coq_value_const c ->
                        (match c with
                           | LLVMsyntax.Coq_const_int (
                               sz0, i0) ->
                               (match LLVMsyntax.nth_list_typ
                                        (coq_INT2nat i0) lt with
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
    | LLVMsyntax.Coq_insn_gep (i1, i2, typ0, v, idxs) ->
        (match idxs with
           | LLVMsyntax.Nil_list_value -> None
           | LLVMsyntax.Cons_list_value (idx, idxs') ->
               (match getSubTypFromValueIdxs idxs' typ0 with
                  | Some t' -> Some (LLVMsyntax.Coq_typ_pointer t')
                  | None -> None))
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
      | Some id0 -> id0 :: []
      | None -> []
  
  (** val getParamsOperand : LLVMsyntax.params -> LLVMsyntax.ids **)
  
  let rec getParamsOperand = function
    | [] -> []
    | p :: lp' ->
        let t0 , v = p in app (getValueIDs v) (getParamsOperand lp')
  
  (** val list_prj1 : ('a1 * 'a2) list -> 'a1 list **)
  
  let rec list_prj1 = function
    | [] -> []
    | p :: ls' -> let x , y = p in x :: (list_prj1 ls')
  
  (** val list_prj2 : ('a1 * 'a2) list -> 'a2 list **)
  
  let rec list_prj2 = function
    | [] -> []
    | p :: ls' -> let x , y = p in y :: (list_prj2 ls')
  
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
    | v :: vs' ->
        (match v with
           | LLVMsyntax.Coq_value_id id0 -> id0 :: (values2ids vs')
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
    | LLVMsyntax.Coq_insn_br (i1, v, l1, l2) -> l1 :: (l2 :: [])
    | LLVMsyntax.Coq_insn_br_uncond (i1, l0) -> l0 :: []
    | _ -> []
  
  (** val getPhiNodeLabels : LLVMsyntax.phinode -> LLVMsyntax.ls **)
  
  let getPhiNodeLabels = function
    | LLVMsyntax.Coq_insn_phi (i1, t0, ls0) ->
        list_prj2 (LLVMsyntax.unmake_list_value_l ls0)
  
  (** val getInsnLabels : LLVMsyntax.insn -> LLVMsyntax.ls **)
  
  let getInsnLabels = function
    | LLVMsyntax.Coq_insn_phinode p -> getPhiNodeLabels p
    | LLVMsyntax.Coq_insn_cmd c -> []
    | LLVMsyntax.Coq_insn_terminator tmn -> getTerminatorLabels tmn
  
  (** val args2Typs : LLVMsyntax.args -> LLVMsyntax.list_typ **)
  
  let rec args2Typs = function
    | [] -> LLVMsyntax.Nil_list_typ
    | p :: la' ->
        let t0 , id0 = p in LLVMsyntax.Cons_list_typ (t0, (args2Typs la'))
  
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
    | LLVMsyntax.Coq_id_binding_arg a -> let t0 , id0 = a in Some t0
  
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
                 if eqDec_atom id0 branch
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
    | phi :: phis' ->
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
                 if eqDec_atom id0 id1
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
                 if eqDec_atom l1 l0
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
    if eqDec_atom id0 (getCmdID i0)
    then LLVMsyntax.Coq_id_binding_cmd i0
    else LLVMsyntax.Coq_id_binding_none
  
  (** val lookupBindingViaIDFromCmds :
      LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let rec lookupBindingViaIDFromCmds li id0 =
    match li with
      | [] -> LLVMsyntax.Coq_id_binding_none
      | i0 :: li' ->
          (match lookupBindingViaIDFromCmd i0 id0 with
             | LLVMsyntax.Coq_id_binding_cmd c ->
                 LLVMsyntax.Coq_id_binding_cmd i0
             | _ -> lookupBindingViaIDFromCmds li' id0)
  
  (** val lookupBindingViaIDFromPhiNode :
      LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromPhiNode i0 id0 =
    if eqDec_atom id0 (getPhiNodeID i0)
    then LLVMsyntax.Coq_id_binding_phinode i0
    else LLVMsyntax.Coq_id_binding_none
  
  (** val lookupBindingViaIDFromPhiNodes :
      LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let rec lookupBindingViaIDFromPhiNodes li id0 =
    match li with
      | [] -> LLVMsyntax.Coq_id_binding_none
      | i0 :: li' ->
          (match lookupBindingViaIDFromPhiNode i0 id0 with
             | LLVMsyntax.Coq_id_binding_phinode p ->
                 LLVMsyntax.Coq_id_binding_phinode i0
             | _ -> lookupBindingViaIDFromPhiNodes li' id0)
  
  (** val lookupBindingViaIDFromTerminator :
      LLVMsyntax.terminator -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromTerminator i0 id0 =
    if eqDec_atom id0 (getTerminatorID i0)
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
              | LLVMsyntax.Coq_id_binding_cmd c ->
                  LLVMsyntax.Coq_id_binding_cmd c
              | LLVMsyntax.Coq_id_binding_phinode p ->
                  LLVMsyntax.Coq_id_binding_phinode p
              | LLVMsyntax.Coq_id_binding_terminator t1 ->
                  LLVMsyntax.Coq_id_binding_terminator t1
              | LLVMsyntax.Coq_id_binding_gvar g ->
                  LLVMsyntax.Coq_id_binding_gvar g
              | LLVMsyntax.Coq_id_binding_fdec f ->
                  LLVMsyntax.Coq_id_binding_fdec f
              | LLVMsyntax.Coq_id_binding_arg a ->
                  LLVMsyntax.Coq_id_binding_arg a)
       | LLVMsyntax.Coq_id_binding_cmd c -> LLVMsyntax.Coq_id_binding_cmd c
       | LLVMsyntax.Coq_id_binding_phinode p ->
           LLVMsyntax.Coq_id_binding_phinode p
       | LLVMsyntax.Coq_id_binding_terminator t1 ->
           LLVMsyntax.Coq_id_binding_terminator t1
       | LLVMsyntax.Coq_id_binding_gvar g -> LLVMsyntax.Coq_id_binding_gvar g
       | LLVMsyntax.Coq_id_binding_fdec f -> LLVMsyntax.Coq_id_binding_fdec f
       | LLVMsyntax.Coq_id_binding_arg a -> LLVMsyntax.Coq_id_binding_arg a)
  
  (** val lookupBindingViaIDFromBlocks :
      LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let rec lookupBindingViaIDFromBlocks lb id0 =
    match lb with
      | [] -> LLVMsyntax.Coq_id_binding_none
      | b :: lb' ->
          (match lookupBindingViaIDFromBlock b id0 with
             | LLVMsyntax.Coq_id_binding_none ->
                 lookupBindingViaIDFromBlocks lb' id0
             | LLVMsyntax.Coq_id_binding_cmd c ->
                 LLVMsyntax.Coq_id_binding_cmd c
             | LLVMsyntax.Coq_id_binding_phinode p ->
                 LLVMsyntax.Coq_id_binding_phinode p
             | LLVMsyntax.Coq_id_binding_terminator t0 ->
                 LLVMsyntax.Coq_id_binding_terminator t0
             | LLVMsyntax.Coq_id_binding_gvar g ->
                 LLVMsyntax.Coq_id_binding_gvar g
             | LLVMsyntax.Coq_id_binding_fdec f ->
                 LLVMsyntax.Coq_id_binding_fdec f
             | LLVMsyntax.Coq_id_binding_arg a ->
                 LLVMsyntax.Coq_id_binding_arg a)
  
  (** val lookupBindingViaIDFromArg :
      LLVMsyntax.arg -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromArg a id0 =
    let t0 , id' = a in
    if eqDec_atom id0 id'
    then LLVMsyntax.Coq_id_binding_arg a
    else LLVMsyntax.Coq_id_binding_none
  
  (** val lookupBindingViaIDFromArgs :
      LLVMsyntax.args -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let rec lookupBindingViaIDFromArgs la id0 =
    match la with
      | [] -> LLVMsyntax.Coq_id_binding_none
      | a :: la' ->
          (match lookupBindingViaIDFromArg a id0 with
             | LLVMsyntax.Coq_id_binding_arg a' ->
                 LLVMsyntax.Coq_id_binding_arg a'
             | _ -> lookupBindingViaIDFromArgs la' id0)
  
  (** val lookupBindingViaIDFromFdec :
      LLVMsyntax.fdec -> LLVMsyntax.id -> LLVMsyntax.id_binding **)
  
  let lookupBindingViaIDFromFdec fd id0 =
    let LLVMsyntax.Coq_fheader_intro (t0, id', la) = fd in
    if eqDec_atom id0 id'
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
          if eqDec_atom id0 id'
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
      | p :: lp' ->
          (match lookupBindingViaIDFromProduct p id0 with
             | LLVMsyntax.Coq_id_binding_none ->
                 lookupBindingViaIDFromProducts lp' id0
             | LLVMsyntax.Coq_id_binding_cmd c ->
                 LLVMsyntax.Coq_id_binding_cmd c
             | LLVMsyntax.Coq_id_binding_phinode p0 ->
                 LLVMsyntax.Coq_id_binding_phinode p0
             | LLVMsyntax.Coq_id_binding_terminator t0 ->
                 LLVMsyntax.Coq_id_binding_terminator t0
             | LLVMsyntax.Coq_id_binding_gvar g ->
                 LLVMsyntax.Coq_id_binding_gvar g
             | LLVMsyntax.Coq_id_binding_fdec f ->
                 LLVMsyntax.Coq_id_binding_fdec f
             | LLVMsyntax.Coq_id_binding_arg a ->
                 LLVMsyntax.Coq_id_binding_arg a)
  
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
      | m :: lm' ->
          (match lookupBindingViaIDFromModule m id0 with
             | LLVMsyntax.Coq_id_binding_none ->
                 lookupBindingViaIDFromModules lm' id0
             | LLVMsyntax.Coq_id_binding_cmd c ->
                 LLVMsyntax.Coq_id_binding_cmd c
             | LLVMsyntax.Coq_id_binding_phinode p ->
                 LLVMsyntax.Coq_id_binding_phinode p
             | LLVMsyntax.Coq_id_binding_terminator t0 ->
                 LLVMsyntax.Coq_id_binding_terminator t0
             | LLVMsyntax.Coq_id_binding_gvar g ->
                 LLVMsyntax.Coq_id_binding_gvar g
             | LLVMsyntax.Coq_id_binding_fdec f ->
                 LLVMsyntax.Coq_id_binding_fdec f
             | LLVMsyntax.Coq_id_binding_arg a ->
                 LLVMsyntax.Coq_id_binding_arg a)
  
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
      | b :: lb' ->
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
          if eqDec_atom (getFdecID fd) i0 then Some fd else None
      | _ -> None
  
  (** val lookupFdecViaIDFromProducts :
      LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let rec lookupFdecViaIDFromProducts lp i0 =
    match lp with
      | [] -> None
      | p :: lp' ->
          (match p with
             | LLVMsyntax.Coq_product_fdec fd ->
                 if eqDec_atom (getFdecID fd) i0
                 then Some fd
                 else lookupFdecViaIDFromProducts lp' i0
             | _ -> lookupFdecViaIDFromProducts lp' i0)
  
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
      | m :: lm' ->
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
          if eqDec_atom (getFdefID fd) i0 then Some fd else None
      | _ -> None
  
  (** val lookupFdefViaIDFromProducts :
      LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.fdef option **)
  
  let rec lookupFdefViaIDFromProducts lp i0 =
    match lp with
      | [] -> None
      | p :: lp' ->
          (match p with
             | LLVMsyntax.Coq_product_fdef fd ->
                 if eqDec_atom (getFdefID fd) i0
                 then Some fd
                 else lookupFdefViaIDFromProducts lp' i0
             | _ -> lookupFdefViaIDFromProducts lp' i0)
  
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
      | m :: lm' ->
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
      | Some t0 -> if eqDec_atom id0 (getCmdID i0) then Some t0 else None
      | None -> None
  
  (** val lookupTypViaIDFromCmds :
      LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaIDFromCmds li id0 =
    match li with
      | [] -> None
      | i0 :: li' ->
          (match getCmdTyp i0 with
             | Some t0 ->
                 if eqDec_atom id0 (getCmdID i0)
                 then Some t0
                 else lookupTypViaIDFromCmds li' id0
             | None -> lookupTypViaIDFromCmds li' id0)
  
  (** val lookupTypViaIDFromPhiNode :
      LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromPhiNode i0 id0 =
    if eqDec_atom id0 (getPhiNodeID i0)
    then Some (getPhiNodeTyp i0)
    else None
  
  (** val lookupTypViaIDFromPhiNodes :
      LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaIDFromPhiNodes li id0 =
    match li with
      | [] -> None
      | i0 :: li' ->
          (match lookupTypViaIDFromPhiNode i0 id0 with
             | Some t0 -> Some t0
             | None -> lookupTypViaIDFromPhiNodes li' id0)
  
  (** val lookupTypViaIDFromTerminator :
      LLVMsyntax.terminator -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromTerminator i0 id0 =
    if eqDec_atom id0 (getTerminatorID i0)
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
      | b :: lb' ->
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
          if eqDec_atom id0 id1 then Some t0 else None
      | LLVMsyntax.Coq_product_fdec f -> None
      | LLVMsyntax.Coq_product_fdef fd -> lookupTypViaIDFromFdef fd id0
  
  (** val lookupTypViaIDFromProducts :
      LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaIDFromProducts lp id0 =
    match lp with
      | [] -> None
      | p :: lp' ->
          (match match p with
                   | LLVMsyntax.Coq_product_gvar g ->
                       let LLVMsyntax.Coq_gvar_intro (id1, t0, c, a) = g in
                       if eqDec_atom id0 id1 then Some t0 else None
                   | LLVMsyntax.Coq_product_fdec f -> None
                   | LLVMsyntax.Coq_product_fdef fd ->
                       lookupTypViaIDFromFdef fd id0 with
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
      | m :: lm' ->
          (match lookupTypViaIDFromModule m id0 with
             | Some t0 -> Some t0
             | None -> lookupTypViaIDFromModules lm' id0)
  
  (** val lookupTypViaIDFromSystem :
      LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromSystem s id0 =
    lookupTypViaIDFromModules s id0
  
  type l2block = (LLVMsyntax.l * LLVMsyntax.block) list
  
  (** val genLabel2Block_block : LLVMsyntax.block -> l2block **)
  
  let genLabel2Block_block b = match b with
    | LLVMsyntax.Coq_block_intro (l0, p, c, t0) -> (l0 , b) :: []
  
  (** val genLabel2Block_blocks : LLVMsyntax.blocks -> l2block **)
  
  let rec genLabel2Block_blocks = function
    | [] -> []
    | b :: bs' -> app (genLabel2Block_block b) (genLabel2Block_blocks bs')
  
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
    | p :: ps' ->
        app (genLabel2Block_product p) (genLabel2Block_products ps')
  
  (** val genLabel2Block : LLVMsyntax.coq_module -> l2block **)
  
  let genLabel2Block = function
    | LLVMsyntax.Coq_module_intro (os, ps) -> genLabel2Block_products ps
  
  (** val getEntryOfFdef : LLVMsyntax.fdef -> LLVMsyntax.block option **)
  
  let getEntryOfFdef = function
    | LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) ->
        (match blocks0 with
           | [] -> None
           | b :: blocks' -> Some b)
  
  (** val getNonEntryOfFdef : LLVMsyntax.fdef -> LLVMsyntax.blocks **)
  
  let getNonEntryOfFdef = function
    | LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) ->
        (match blocks0 with
           | [] -> []
           | b :: blocks' -> blocks')
  
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
      | m :: s' ->
          (match lookupAL (genLabel2Block m) l0 with
             | Some b -> Some b
             | None -> lookupBlockViaLabelFromSystem s' l0)
  
  (** val getLabelsFromBlocks : LLVMsyntax.blocks -> LLVMsyntax.ls **)
  
  let rec getLabelsFromBlocks = function
    | [] -> lempty_set
    | b :: lb' ->
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
      | Some id1 -> if eqDec_atom id' id1 then id0 :: [] else []
      | None -> []
  
  (** val genIdUseDef_id_uses_id :
      LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_id_uses_id id0 id1 id' =
    if eqDec_atom id' id0 then id1 :: [] else []
  
  (** val genIdUseDef_id_uses_params :
      LLVMsyntax.params -> LLVMsyntax.id -> LLVMsyntax.usedef_id **)
  
  let rec genIdUseDef_id_uses_params ps id0 x =
    match ps with
      | [] -> []
      | p :: ps' ->
          let t0 , v = p in
          app
            (match getValueID v with
               | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
               | None -> []) (genIdUseDef_id_uses_params ps' id0 x)
  
  (** val genIdUseDef_cmd_uses_value :
      LLVMsyntax.value -> LLVMsyntax.cmd -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_cmd_uses_value v i0 x =
    match getValueID v with
      | Some id0 -> if eqDec_atom x id0 then (getCmdID i0) :: [] else []
      | None -> []
  
  (** val genIdUseDef_terminator_uses_value :
      LLVMsyntax.value -> LLVMsyntax.terminator -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_terminator_uses_value v i0 x =
    match getValueID v with
      | Some id0 ->
          if eqDec_atom x id0 then (getTerminatorID i0) :: [] else []
      | None -> []
  
  (** val genIdUseDef_phinode_uses_value :
      LLVMsyntax.value -> LLVMsyntax.phinode -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_phinode_uses_value v i0 x =
    match getValueID v with
      | Some id0 -> if eqDec_atom x id0 then (getPhiNodeID i0) :: [] else []
      | None -> []
  
  (** val genIdUseDef_cmd_uses_id :
      LLVMsyntax.id -> LLVMsyntax.cmd -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_cmd_uses_id id0 i0 x =
    if eqDec_atom x id0 then (getCmdID i0) :: [] else []
  
  (** val genIdUseDef_terminator_uses_id :
      LLVMsyntax.id -> LLVMsyntax.terminator -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_terminator_uses_id id0 i0 x =
    if eqDec_atom x id0 then (getTerminatorID i0) :: [] else []
  
  (** val genIdUseDef_phinode_uses_id :
      LLVMsyntax.id -> LLVMsyntax.phinode -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_phinode_uses_id id0 i0 x =
    if eqDec_atom x id0 then (getPhiNodeID i0) :: [] else []
  
  (** val genIdUseDef_cmd_uses_params :
      LLVMsyntax.params -> LLVMsyntax.cmd -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_cmd_uses_params ps i0 x =
    genIdUseDef_id_uses_params ps (getCmdID i0) x
  
  (** val genIdUseDef_terminator_uses_params :
      LLVMsyntax.params -> LLVMsyntax.terminator -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_terminator_uses_params ps i0 x =
    genIdUseDef_id_uses_params ps (getTerminatorID i0) x
  
  (** val genIdUseDef_phinode_uses_params :
      LLVMsyntax.params -> LLVMsyntax.phinode -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_phinode_uses_params ps i0 x =
    genIdUseDef_id_uses_params ps (getPhiNodeID i0) x
  
  (** val genIdUseDef_cmd : LLVMsyntax.cmd -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_cmd i0 x =
    match i0 with
      | LLVMsyntax.Coq_insn_bop (id0, b, sz0, v1, v2) ->
          app
            (match getValueID v1 with
               | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
               | None -> [])
            (match getValueID v2 with
               | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
               | None -> [])
      | LLVMsyntax.Coq_insn_extractvalue (id0, typ0, value0, l0) ->
          (match getValueID value0 with
             | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
             | None -> [])
      | LLVMsyntax.Coq_insn_insertvalue (id0, typs, v0, typ1, v1, c2) ->
          app
            (match getValueID v0 with
               | Some id1 ->
                   if eqDec_atom x id1 then (getCmdID i0) :: [] else []
               | None -> [])
            (match getValueID v1 with
               | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
               | None -> [])
      | LLVMsyntax.Coq_insn_free (id0, typ0, v) ->
          (match getValueID v with
             | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
             | None -> [])
      | LLVMsyntax.Coq_insn_load (id0, typ1, v1, a) ->
          (match getValueID v1 with
             | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
             | None -> [])
      | LLVMsyntax.Coq_insn_store (id0, typ1, v1, v2, a) ->
          app
            (match getValueID v1 with
               | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
               | None -> [])
            (match getValueID v2 with
               | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
               | None -> [])
      | LLVMsyntax.Coq_insn_gep (id0, i1, typ0, value0, l0) ->
          (match getValueID value0 with
             | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
             | None -> [])
      | LLVMsyntax.Coq_insn_ext (id0, e, sz1, v1, sz2) ->
          (match getValueID v1 with
             | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
             | None -> [])
      | LLVMsyntax.Coq_insn_cast (id0, c, typ1, v1, typ2) ->
          (match getValueID v1 with
             | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
             | None -> [])
      | LLVMsyntax.Coq_insn_icmp (id0, cond0, typ0, v1, v2) ->
          app
            (match getValueID v1 with
               | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
               | None -> [])
            (match getValueID v2 with
               | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
               | None -> [])
      | LLVMsyntax.Coq_insn_select (id0, v0, typ0, v1, v2) ->
          app
            (match getValueID v0 with
               | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
               | None -> [])
            (app
              (match getValueID v1 with
                 | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
                 | None -> [])
              (match getValueID v2 with
                 | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
                 | None -> []))
      | LLVMsyntax.Coq_insn_call (id0, n, t0, typ0, id1, paraml) ->
          app (if eqDec_atom x id1 then id0 :: [] else [])
            (genIdUseDef_id_uses_params paraml id0 x)
      | _ -> []
  
  (** val genIdUseDef_terminator :
      LLVMsyntax.terminator -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_terminator i0 x =
    match i0 with
      | LLVMsyntax.Coq_insn_return (id0, t0, v) ->
          (match getValueID v with
             | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
             | None -> [])
      | LLVMsyntax.Coq_insn_br (id0, v, l1, l2) ->
          (match getValueID v with
             | Some id1 -> if eqDec_atom x id1 then id0 :: [] else []
             | None -> [])
      | _ -> []
  
  (** val genIdUseDef_id_uses_idls :
      LLVMsyntax.list_value_l -> LLVMsyntax.id -> LLVMsyntax.usedef_id **)
  
  let rec genIdUseDef_id_uses_idls idls id0 x =
    match idls with
      | LLVMsyntax.Nil_list_value_l -> []
      | LLVMsyntax.Cons_list_value_l (v, l0, idls') ->
          (match v with
             | LLVMsyntax.Coq_value_id id1 ->
                 app (if eqDec_atom x id1 then id0 :: [] else [])
                   (genIdUseDef_id_uses_idls idls' id0 x)
             | LLVMsyntax.Coq_value_const c ->
                 genIdUseDef_id_uses_idls idls' id0 x)
  
  (** val genIdUseDef_phinode :
      LLVMsyntax.phinode -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_phinode i0 x =
    let LLVMsyntax.Coq_insn_phi (id0, typ0, idls) = i0 in
    genIdUseDef_id_uses_idls idls id0 x
  
  (** val genIdUseDef_cmds : LLVMsyntax.cmds -> LLVMsyntax.usedef_id **)
  
  let rec genIdUseDef_cmds is x =
    match is with
      | [] -> []
      | i0 :: is' -> app (genIdUseDef_cmd i0 x) (genIdUseDef_cmds is' x)
  
  (** val genIdUseDef_phinodes :
      LLVMsyntax.phinodes -> LLVMsyntax.usedef_id **)
  
  let rec genIdUseDef_phinodes is x =
    match is with
      | [] -> []
      | i0 :: is' ->
          app (genIdUseDef_phinode i0 x) (genIdUseDef_phinodes is' x)
  
  (** val genIdUseDef_block : LLVMsyntax.block -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_block b x =
    let LLVMsyntax.Coq_block_intro (l0, ps, cs, t0) = b in
    app (genIdUseDef_phinodes ps x)
      (app (genIdUseDef_cmds cs x) (genIdUseDef_terminator t0 x))
  
  (** val genIdUseDef_blocks : LLVMsyntax.blocks -> LLVMsyntax.usedef_id **)
  
  let rec genIdUseDef_blocks bs x =
    match bs with
      | [] -> []
      | b :: bs' -> app (genIdUseDef_block b x) (genIdUseDef_blocks bs' x)
  
  (** val genIdUseDef_fdef : LLVMsyntax.fdef -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_fdef f x =
    let LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) = f in
    genIdUseDef_blocks blocks0 x
  
  (** val genIdUseDef_product :
      LLVMsyntax.product -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef_product p x =
    match p with
      | LLVMsyntax.Coq_product_gvar g ->
          let LLVMsyntax.Coq_gvar_intro (id0, t0, v, a) = g in []
      | LLVMsyntax.Coq_product_fdec f -> []
      | LLVMsyntax.Coq_product_fdef f -> genIdUseDef_fdef f x
  
  (** val genIdUseDef_products :
      LLVMsyntax.products -> LLVMsyntax.usedef_id **)
  
  let rec genIdUseDef_products ps x =
    match ps with
      | [] -> []
      | p :: ps' ->
          app
            (match p with
               | LLVMsyntax.Coq_product_gvar g ->
                   let LLVMsyntax.Coq_gvar_intro (id0, t0, v, a) = g in []
               | LLVMsyntax.Coq_product_fdec f -> []
               | LLVMsyntax.Coq_product_fdef f -> genIdUseDef_fdef f x)
            (genIdUseDef_products ps' x)
  
  (** val genIdUseDef : LLVMsyntax.coq_module -> LLVMsyntax.usedef_id **)
  
  let genIdUseDef m x =
    let LLVMsyntax.Coq_module_intro (os, ps) = m in genIdUseDef_products ps x
  
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
    if eqDec_atom (getBlockLabel b') l0 then b :: [] else []
  
  (** val genBlockUseDef_phi_cases :
      LLVMsyntax.list_value_l -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_phi_cases ps b x =
    match ps with
      | LLVMsyntax.Nil_list_value_l -> []
      | LLVMsyntax.Cons_list_value_l (v, l0, ps') ->
          app (if eqDec_atom (getBlockLabel x) l0 then b :: [] else [])
            (genBlockUseDef_phi_cases ps' b x)
  
  (** val genBlockUseDef_cmd :
      LLVMsyntax.cmd -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_cmd i0 b x =
    []
  
  (** val genBlockUseDef_terminator :
      LLVMsyntax.terminator -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_terminator i0 b x =
    match i0 with
      | LLVMsyntax.Coq_insn_br (i1, v, l1, l2) ->
          app (if eqDec_atom (getBlockLabel x) l1 then b :: [] else [])
            (if eqDec_atom (getBlockLabel x) l2 then b :: [] else [])
      | LLVMsyntax.Coq_insn_br_uncond (i1, l0) ->
          if eqDec_atom (getBlockLabel x) l0 then b :: [] else []
      | _ -> []
  
  (** val genBlockUseDef_phinode :
      LLVMsyntax.phinode -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_phinode i0 b x =
    let LLVMsyntax.Coq_insn_phi (id0, typ0, idls) = i0 in
    genBlockUseDef_phi_cases idls b x
  
  (** val genBlockUseDef_cmds :
      LLVMsyntax.cmds -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_cmds is b x =
    match is with
      | [] -> []
      | i0 :: is' -> app [] (genBlockUseDef_cmds is' b x)
  
  (** val genBlockUseDef_phinodes :
      LLVMsyntax.phinodes -> LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_phinodes is b x =
    match is with
      | [] -> []
      | i0 :: is' ->
          app (genBlockUseDef_phinode i0 b x)
            (genBlockUseDef_phinodes is' b x)
  
  (** val genBlockUseDef_block :
      LLVMsyntax.block -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_block b x =
    let LLVMsyntax.Coq_block_intro (l0, ps, cs, t0) = b in
    app (genBlockUseDef_phinodes ps b x)
      (app (genBlockUseDef_cmds cs b x) (genBlockUseDef_terminator t0 b x))
  
  (** val genBlockUseDef_blocks :
      LLVMsyntax.blocks -> LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_blocks bs x =
    match bs with
      | [] -> []
      | b :: bs' ->
          app (genBlockUseDef_blocks bs' x) (genBlockUseDef_block b x)
  
  (** val genBlockUseDef_fdef :
      LLVMsyntax.fdef -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_fdef f x =
    let LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) = f in
    genBlockUseDef_blocks blocks0 x
  
  (** val genBlockUseDef_product :
      LLVMsyntax.product -> LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_product p x =
    match p with
      | LLVMsyntax.Coq_product_fdef f -> genBlockUseDef_fdef f x
      | _ -> []
  
  (** val genBlockUseDef_products :
      LLVMsyntax.products -> LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_products ps x =
    match ps with
      | [] -> []
      | p :: ps' ->
          app (genBlockUseDef_products ps' x) (genBlockUseDef_product p x)
  
  (** val genBlockUseDef :
      LLVMsyntax.coq_module -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef m x =
    let LLVMsyntax.Coq_module_intro (os, ps) = m in
    genBlockUseDef_products ps x
  
  (** val getBlockUseDef :
      LLVMsyntax.usedef_block -> LLVMsyntax.block -> LLVMsyntax.block list **)
  
  let getBlockUseDef udb b =
    udb b
  
  (** val getTerminator : LLVMsyntax.block -> LLVMsyntax.terminator **)
  
  let getTerminator = function
    | LLVMsyntax.Coq_block_intro (l0, p, c, t0) -> t0
  
  (** val getLabelsFromSwitchCases :
      (LLVMsyntax.const * LLVMsyntax.l) list -> LLVMsyntax.ls **)
  
  let rec getLabelsFromSwitchCases = function
    | [] -> lempty_set
    | p :: cs' ->
        let c , l0 = p in lset_add l0 (getLabelsFromSwitchCases cs')
  
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
      | l0 :: ls0' ->
          (match lookupAL l2b l0 with
             | Some b -> b :: (getBlocksFromLabels ls0' l2b)
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
    if eq_nat_dec (length (udb b)) (S O) then true else false
  
  (** val genLabelsFromBlocks : LLVMsyntax.blocks -> LLVMsyntax.ls **)
  
  let rec genLabelsFromBlocks = function
    | [] -> lempty_set
    | b :: bs' ->
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
      | b :: bs' ->
          let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
          lset_union (output l0) (inputFromPred bs' output)
  
  (** val outputFromInput :
      LLVMsyntax.block -> LLVMsyntax.ls -> LLVMsyntax.ls **)
  
  let outputFromInput b input =
    let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in lset_add l0 input
  
  (** val update_dt :
      LLVMsyntax.dt -> LLVMsyntax.l -> LLVMsyntax.ls -> LLVMsyntax.dt **)
  
  let update_dt d1 l0 ls0 l1 =
    if eqDec_atom l1 l0 then ls0 else d1 l1
  
  (** val inter_dt : LLVMsyntax.dt -> LLVMsyntax.dt -> LLVMsyntax.dt **)
  
  let inter_dt d1 d2 l0 =
    lset_inter (d1 l0) (d2 l0)
  
  (** val genDominatorTree_blocks_innerloop :
      LLVMsyntax.blocks -> LLVMsyntax.usedef_block -> LLVMsyntax.dt ->
      LLVMsyntax.dt **)
  
  let rec genDominatorTree_blocks_innerloop bs udb output x =
    match bs with
      | [] -> output x
      | b :: bs' ->
          let LLVMsyntax.Coq_block_intro (l0, ps, cs, t0) = b in
          genDominatorTree_blocks_innerloop bs' udb (fun l1 ->
            if eqDec_atom l1 l0
            then outputFromInput (LLVMsyntax.Coq_block_intro (l0, ps, cs,
                   t0))
                   (inputFromPred
                     (udb (LLVMsyntax.Coq_block_intro (l0, ps, cs, t0)))
                     output)
            else output l1) x
  
  (** val eq_dt :
      LLVMsyntax.dt -> LLVMsyntax.dt -> LLVMsyntax.blocks -> bool **)
  
  let rec eq_dt d0 d1 = function
    | [] -> true
    | b :: bs' ->
        let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
        if lset_eq (d0 l0) (d1 l0) then eq_dt d0 d1 bs' else false
  
  (** val sizeOfDT : LLVMsyntax.blocks -> LLVMsyntax.dt -> nat **)
  
  let rec sizeOfDT bs output =
    match bs with
      | [] -> O
      | b :: bs' ->
          let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
          plus (length (output l0)) (sizeOfDT bs' output)
  
  (** val size : (LLVMsyntax.blocks * LLVMsyntax.dt) -> nat **)
  
  let size = function
    | bs , output -> sizeOfDT bs output
  
  (** val genDominatorTree_blocks_F :
      ((LLVMsyntax.blocks * LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.dt) -> (LLVMsyntax.blocks * LLVMsyntax.dt) ->
      LLVMsyntax.usedef_block -> LLVMsyntax.dt **)
  
  let genDominatorTree_blocks_F genDominatorTree_blocks0 arg0 udb x =
    let bs , output = arg0 in
    if eq_dt output (genDominatorTree_blocks_innerloop bs udb output) bs
    then genDominatorTree_blocks_innerloop bs udb output x
    else genDominatorTree_blocks0 (bs ,
           (genDominatorTree_blocks_innerloop bs udb output)) udb x
  
  (** val genDominatorTree_blocks_terminate :
      (LLVMsyntax.blocks * LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.dt **)
  
  let rec genDominatorTree_blocks_terminate arg0 udb =
    let bs , output = arg0 in
    if eq_dt output (genDominatorTree_blocks_innerloop bs udb output) bs
    then genDominatorTree_blocks_innerloop bs udb output
    else genDominatorTree_blocks_terminate (bs ,
           (genDominatorTree_blocks_innerloop bs udb output)) udb
  
  (** val genDominatorTree_blocks :
      (LLVMsyntax.blocks * LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.dt **)
  
  let genDominatorTree_blocks x x0 x1 =
    genDominatorTree_blocks_terminate x x0 x1
  
  type coq_R_genDominatorTree_blocks =
    | R_genDominatorTree_blocks_0 of (LLVMsyntax.blocks * LLVMsyntax.dt)
       * LLVMsyntax.usedef_block * LLVMsyntax.blocks * 
       LLVMsyntax.dt * LLVMsyntax.dt
    | R_genDominatorTree_blocks_1 of (LLVMsyntax.blocks * LLVMsyntax.dt)
       * LLVMsyntax.usedef_block * LLVMsyntax.blocks * 
       LLVMsyntax.dt * LLVMsyntax.dt * LLVMsyntax.dt
       * coq_R_genDominatorTree_blocks
  
  (** val coq_R_genDominatorTree_blocks_rect :
      ((LLVMsyntax.blocks * LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __
      -> 'a1) -> ((LLVMsyntax.blocks * LLVMsyntax.dt) ->
      LLVMsyntax.usedef_block -> LLVMsyntax.blocks -> LLVMsyntax.dt -> __ ->
      LLVMsyntax.dt -> __ -> __ -> LLVMsyntax.dt ->
      coq_R_genDominatorTree_blocks -> 'a1 -> 'a1) -> (LLVMsyntax.blocks *
      LLVMsyntax.dt) -> LLVMsyntax.usedef_block -> LLVMsyntax.dt ->
      coq_R_genDominatorTree_blocks -> 'a1 **)
  
  let rec coq_R_genDominatorTree_blocks_rect f f0 arg0 udb d = function
    | R_genDominatorTree_blocks_0 (arg1, udb0, bs, output, output') ->
        f arg1 udb0 bs output __ output' __ __
    | R_genDominatorTree_blocks_1 (arg1, udb0, bs, output, output', res, r0) ->
        f0 arg1 udb0 bs output __ output' __ __ res r0
          (coq_R_genDominatorTree_blocks_rect f f0 (bs , output') udb0 res
            r0)
  
  (** val coq_R_genDominatorTree_blocks_rec :
      ((LLVMsyntax.blocks * LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __
      -> 'a1) -> ((LLVMsyntax.blocks * LLVMsyntax.dt) ->
      LLVMsyntax.usedef_block -> LLVMsyntax.blocks -> LLVMsyntax.dt -> __ ->
      LLVMsyntax.dt -> __ -> __ -> LLVMsyntax.dt ->
      coq_R_genDominatorTree_blocks -> 'a1 -> 'a1) -> (LLVMsyntax.blocks *
      LLVMsyntax.dt) -> LLVMsyntax.usedef_block -> LLVMsyntax.dt ->
      coq_R_genDominatorTree_blocks -> 'a1 **)
  
  let rec coq_R_genDominatorTree_blocks_rec f f0 arg0 udb d = function
    | R_genDominatorTree_blocks_0 (arg1, udb0, bs, output, output') ->
        f arg1 udb0 bs output __ output' __ __
    | R_genDominatorTree_blocks_1 (arg1, udb0, bs, output, output', res, r0) ->
        f0 arg1 udb0 bs output __ output' __ __ res r0
          (coq_R_genDominatorTree_blocks_rec f f0 (bs , output') udb0 res r0)
  
  (** val genDominatorTree_blocks_rect :
      ((LLVMsyntax.blocks * LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __
      -> 'a1) -> ((LLVMsyntax.blocks * LLVMsyntax.dt) ->
      LLVMsyntax.usedef_block -> LLVMsyntax.blocks -> LLVMsyntax.dt -> __ ->
      LLVMsyntax.dt -> __ -> __ -> 'a1 -> 'a1) -> (LLVMsyntax.blocks *
      LLVMsyntax.dt) -> LLVMsyntax.usedef_block -> 'a1 **)
  
  let rec genDominatorTree_blocks_rect f f0 arg0 udb =
    let b , d = arg0 in
    if eq_dt d (genDominatorTree_blocks_innerloop b udb d) b
    then f arg0 udb b d __ (genDominatorTree_blocks_innerloop b udb d) __ __
    else f0 arg0 udb b d __ (genDominatorTree_blocks_innerloop b udb d) __ __
           (genDominatorTree_blocks_rect f f0 (b ,
             (genDominatorTree_blocks_innerloop b udb d)) udb)
  
  (** val genDominatorTree_blocks_rec :
      ((LLVMsyntax.blocks * LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __
      -> 'a1) -> ((LLVMsyntax.blocks * LLVMsyntax.dt) ->
      LLVMsyntax.usedef_block -> LLVMsyntax.blocks -> LLVMsyntax.dt -> __ ->
      LLVMsyntax.dt -> __ -> __ -> 'a1 -> 'a1) -> (LLVMsyntax.blocks *
      LLVMsyntax.dt) -> LLVMsyntax.usedef_block -> 'a1 **)
  
  let genDominatorTree_blocks_rec f f0 arg0 udb =
    genDominatorTree_blocks_rect f f0 arg0 udb
  
  (** val coq_R_genDominatorTree_blocks_correct :
      (LLVMsyntax.blocks * LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
      LLVMsyntax.dt -> coq_R_genDominatorTree_blocks **)
  
  let coq_R_genDominatorTree_blocks_correct x x0 res =
    genDominatorTree_blocks_rect (fun y y0 y1 y2 _ y4 _ _ z _ ->
      R_genDominatorTree_blocks_0 (y, y0, y1, y2, y4))
      (fun y y0 y1 y2 _ y4 _ _ y7 z _ -> R_genDominatorTree_blocks_1 (y, y0,
      y1, y2, y4, (genDominatorTree_blocks (y1 , y4) y0),
      (y7 (genDominatorTree_blocks (y1 , y4) y0) __))) x x0 res __
  
  (** val initialize_genDominatorTree_blocks :
      LLVMsyntax.blocks -> LLVMsyntax.ls -> LLVMsyntax.dt -> LLVMsyntax.dt **)
  
  let rec initialize_genDominatorTree_blocks bs u d0 x =
    match bs with
      | [] -> d0 x
      | b :: bs' ->
          let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
          initialize_genDominatorTree_blocks bs' u (fun l1 ->
            if eqDec_atom l1 l0 then u else d0 l1) x
  
  (** val genEmptyDT : LLVMsyntax.dt **)
  
  let genEmptyDT x =
    []
  
  (** val initialize_genDominatorTree_entry :
      LLVMsyntax.fdef -> LLVMsyntax.dt **)
  
  let initialize_genDominatorTree_entry f x =
    match getEntryOfFdef f with
      | Some b ->
          let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
          if eqDec_atom x l0 then lset_single l0 else []
      | None -> []
  
  (** val initialize_genDominatorTree :
      LLVMsyntax.fdef -> LLVMsyntax.ls -> LLVMsyntax.dt **)
  
  let initialize_genDominatorTree f u x =
    initialize_genDominatorTree_blocks (getNonEntryOfFdef f) u (fun x0 ->
      match getEntryOfFdef f with
        | Some b ->
            let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
            if eqDec_atom x0 l0 then lset_single l0 else []
        | None -> []) x
  
  (** val genDominatorTree :
      LLVMsyntax.fdef -> LLVMsyntax.coq_module -> LLVMsyntax.dt **)
  
  let genDominatorTree f m x =
    let LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) = f in
    genDominatorTree_blocks (blocks0 ,
      (initialize_genDominatorTree f (genLabelsFromFdef f)))
      (genBlockUseDef m) x
  
  (** val blockDominatesB :
      LLVMsyntax.dt -> LLVMsyntax.block -> LLVMsyntax.block -> bool **)
  
  let blockDominatesB d b1 b2 =
    let LLVMsyntax.Coq_block_intro (l1, p, c, t0) = b1 in
    let LLVMsyntax.Coq_block_intro (l2, p0, c0, t1) = b2 in
    lset_mem l2 (d l1)
  
  (** val isReachableFromEntryB :
      LLVMsyntax.fdef_info -> LLVMsyntax.block -> bool **)
  
  let isReachableFromEntryB fi b =
    let f , d = fi in
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
    | c :: cs' -> (getCmdID c) :: (getCmdsIDs cs')
  
  (** val getPhiNodesIDs : LLVMsyntax.phinode list -> LLVMsyntax.ids **)
  
  let rec getPhiNodesIDs = function
    | [] -> []
    | p :: ps' -> (getPhiNodeID p) :: (getPhiNodesIDs ps')
  
  (** val getBlockIDs : LLVMsyntax.block -> LLVMsyntax.ids **)
  
  let getBlockIDs = function
    | LLVMsyntax.Coq_block_intro (l0, ps, cs, t0) ->
        app (getPhiNodesIDs ps)
          (app (getCmdsIDs cs) ((getTerminatorID t0) :: []))
  
  (** val getBlocksIDs : LLVMsyntax.block list -> LLVMsyntax.ids **)
  
  let rec getBlocksIDs = function
    | [] -> []
    | b :: bs' -> app (getBlockIDs b) (getBlocksIDs bs')
  
  (** val getBlocksLabels : LLVMsyntax.block list -> LLVMsyntax.ls **)
  
  let rec getBlocksLabels = function
    | [] -> []
    | y :: bs' ->
        let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = y in
        l0 :: (getBlocksLabels bs')
  
  (** val getProductID : LLVMsyntax.product -> LLVMsyntax.id **)
  
  let getProductID = function
    | LLVMsyntax.Coq_product_gvar g -> getGvarID g
    | LLVMsyntax.Coq_product_fdec f -> getFdecID f
    | LLVMsyntax.Coq_product_fdef f -> getFdefID f
  
  (** val getProductsIDs : LLVMsyntax.product list -> LLVMsyntax.ids **)
  
  let rec getProductsIDs = function
    | [] -> []
    | p :: ps' -> (getProductID p) :: (getProductsIDs ps')
  
  (** val sumbool2bool : bool -> bool **)
  
  let sumbool2bool = function
    | true -> true
    | false -> false
  
  type typ_dec_prop = LLVMsyntax.typ -> bool
  
  type list_typ_dec_prop = LLVMsyntax.list_typ -> bool
  
  (** val typ_mutrec_dec :
      (LLVMsyntax.typ -> typ_dec_prop) * (LLVMsyntax.list_typ ->
      list_typ_dec_prop) **)
  
  let typ_mutrec_dec =
    LLVMsyntax.typ_mutrec (fun s t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_int s0 -> sz_dec s s0
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
            if h t3 then sz_dec s s0 else false
        | _ -> false) (fun t0 h l0 h0 t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_function (t3, l1) ->
            if h t3 then h0 l1 else false
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
            if h t1 then h0 lt3 else false)
  
  (** val typ_dec : LLVMsyntax.typ -> LLVMsyntax.typ -> bool **)
  
  let typ_dec t1 t2 =
    let t0 , l0 = typ_mutrec_dec in t0 t1 t2
  
  (** val list_typ_dec :
      LLVMsyntax.list_typ -> LLVMsyntax.list_typ -> bool **)
  
  let list_typ_dec lt1 lt2 =
    let t0 , l0 = typ_mutrec_dec in l0 lt1 lt2
  
  type const_dec_prop = LLVMsyntax.const -> bool
  
  type list_const_dec_prop = LLVMsyntax.list_const -> bool
  
  (** val const_mutrec_dec :
      (LLVMsyntax.const -> const_dec_prop) * (LLVMsyntax.list_const ->
      list_const_dec_prop) **)
  
  let const_mutrec_dec =
    LLVMsyntax.const_mutrec (fun s i0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_int (s0, i1) ->
            if coq_INT_dec i0 i1 then sz_dec s s0 else false
        | _ -> false) (fun t0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_undef t1 ->
            let t2 , l0 = typ_mutrec_dec in t2 t0 t1
        | _ -> false) (fun t0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_null t1 ->
            let t2 , l0 = typ_mutrec_dec in t2 t0 t1
        | _ -> false) (fun l0 h c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_arr l1 -> h l1
        | _ -> false) (fun l0 h c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_struct l1 -> h l1
        | _ -> false) (fun t0 i0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_gid (t1, i1) ->
            if let t2 , l0 = typ_mutrec_dec in t2 t0 t1
            then id_dec i0 i1
            else false
        | _ -> false) (fun lc2 ->
      match lc2 with
        | LLVMsyntax.Nil_list_const -> true
        | LLVMsyntax.Cons_list_const (c, lc3) -> false) (fun c h l0 h0 lc2 ->
      match lc2 with
        | LLVMsyntax.Nil_list_const -> false
        | LLVMsyntax.Cons_list_const (c0, lc3) ->
            if h c0 then h0 lc3 else false)
  
  (** val const_dec : LLVMsyntax.const -> LLVMsyntax.const -> bool **)
  
  let const_dec c1 c2 =
    let c , l0 = const_mutrec_dec in c c1 c2
  
  (** val list_const_dec :
      LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool **)
  
  let list_const_dec lc1 lc2 =
    let c , l0 = const_mutrec_dec in l0 lc1 lc2
  
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
             | LLVMsyntax.Coq_value_const c0 ->
                 let c , l0 = const_mutrec_dec in c x c0)
  
  (** val params_dec : LLVMsyntax.params -> LLVMsyntax.params -> bool **)
  
  let rec params_dec l0 p0 =
    match l0 with
      | [] -> (match p0 with
                 | [] -> true
                 | p :: l1 -> false)
      | a :: l1 ->
          (match p0 with
             | [] -> false
             | p :: l2 ->
                 if let t0 , v = a in
                    let t1 , v0 = p in
                    if let t2 , l3 = typ_mutrec_dec in t2 t0 t1
                    then value_dec v v0
                    else false
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
                 if value_dec v v0
                 then if l_dec l1 l4 then list_value_l_dec l3 l5 else false
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
                 if id_dec i0 i1
                 then if bop_dec b b0
                      then if sz_dec s s0
                           then if value_dec v v1
                                then value_dec v0 v2
                                else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_extractvalue (i0, t0, v, l0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_extractvalue (i1, t1, v0, l1) ->
                 if id_dec i0 i1
                 then if let t2 , l2 = typ_mutrec_dec in t2 t0 t1
                      then if value_dec v v0
                           then let c , l2 = const_mutrec_dec in l2 l0 l1
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_insertvalue (i0, t0, v, t1, v0, l0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_insertvalue (i1, t2, v1, t3, v2, l1) ->
                 if id_dec i0 i1
                 then if let t4 , l2 = typ_mutrec_dec in t4 t0 t2
                      then if value_dec v v1
                           then if let t4 , l2 = typ_mutrec_dec in t4 t1 t3
                                then if value_dec v0 v2
                                     then let c , l2 = const_mutrec_dec in
                                          l2 l0 l1
                                     else false
                                else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_malloc (i0, t0, s, a) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_malloc (i1, t1, s0, a0) ->
                 if id_dec i0 i1
                 then if let t2 , l0 = typ_mutrec_dec in t2 t0 t1
                      then if sz_dec s s0 then align_dec a a0 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_free (i0, t0, v) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_free (i1, t1, v0) ->
                 if id_dec i0 i1
                 then if let t2 , l0 = typ_mutrec_dec in t2 t0 t1
                      then value_dec v v0
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_alloca (i0, t0, s, a) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_alloca (i1, t1, s0, a0) ->
                 if id_dec i0 i1
                 then if let t2 , l0 = typ_mutrec_dec in t2 t0 t1
                      then if sz_dec s s0 then align_dec a a0 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_load (i0, t0, v, a) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_load (i1, t1, v0, a0) ->
                 if id_dec i0 i1
                 then if let t2 , l0 = typ_mutrec_dec in t2 t0 t1
                      then if align_dec a a0 then value_dec v v0 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_store (i0, t0, v, v0, a) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_store (i1, t1, v1, v2, a0) ->
                 if id_dec i0 i1
                 then if let t2 , l0 = typ_mutrec_dec in t2 t0 t1
                      then if value_dec v v1
                           then if align_dec a a0
                                then value_dec v0 v2
                                else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_gep (i0, i1, t0, v, l0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_gep (i2, i3, t1, v0, l1) ->
                 if id_dec i0 i2
                 then if inbounds_dec i1 i3
                      then if let t2 , l2 = typ_mutrec_dec in t2 t0 t1
                           then if value_dec v v0
                                then list_value_dec l0 l1
                                else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_ext (i0, e, t0, v, t1) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_ext (i1, e0, t2, v0, t3) ->
                 if id_dec i0 i1
                 then if extop_dec e e0
                      then if let t4 , l0 = typ_mutrec_dec in t4 t0 t2
                           then if value_dec v v0
                                then let t4 , l0 = typ_mutrec_dec in t4 t1 t3
                                else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_cast (i0, c, t0, v, t1) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_cast (i1, c0, t2, v0, t3) ->
                 if id_dec i0 i1
                 then if castop_dec c c0
                      then if let t4 , l0 = typ_mutrec_dec in t4 t0 t2
                           then if value_dec v v0
                                then let t4 , l0 = typ_mutrec_dec in t4 t1 t3
                                else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_icmp (i0, c, t0, v, v0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_icmp (i1, c0, t1, v1, v2) ->
                 if id_dec i0 i1
                 then if cond_dec c c0
                      then if let t2 , l0 = typ_mutrec_dec in t2 t0 t1
                           then if value_dec v v1
                                then value_dec v0 v2
                                else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_select (i0, v, t0, v0, v1) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_select (i1, v2, t1, v3, v4) ->
                 if id_dec i0 i1
                 then if value_dec v v2
                      then if let t2 , l0 = typ_mutrec_dec in t2 t0 t1
                           then if value_dec v0 v3
                                then value_dec v1 v4
                                else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_call (i0, n, t0, t1, i1, p) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_call (i2, n0, t2, t3, i3, p0) ->
                 if id_dec i0 i2
                 then if id_dec i1 i3
                      then if noret_dec n n0
                           then if tailc_dec t0 t2
                                then if let t4 , l0 = typ_mutrec_dec in
                                        t4 t1 t3
                                     then params_dec p p0
                                     else false
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
                 if id_dec i0 i1
                 then if let t2 , l0 = typ_mutrec_dec in t2 t0 t1
                      then value_dec v v0
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_return_void i0 ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_return_void i1 -> id_dec i0 i1
             | _ -> false)
      | LLVMsyntax.Coq_insn_br (i0, v, l0, l1) ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_br (i1, v0, l2, l3) ->
                 if id_dec i0 i1
                 then if l_dec l0 l2
                      then if l_dec l1 l3 then value_dec v v0 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_br_uncond (i0, l0) ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_br_uncond (i1, l1) ->
                 if id_dec i0 i1 then l_dec l0 l1 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_unreachable i0 ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_unreachable i1 -> id_dec i0 i1
             | _ -> false)
  
  (** val phinode_dec : LLVMsyntax.phinode -> LLVMsyntax.phinode -> bool **)
  
  let phinode_dec p1 p2 =
    let LLVMsyntax.Coq_insn_phi (i0, t0, l0) = p1 in
    let LLVMsyntax.Coq_insn_phi (i1, t1, l1) = p2 in
    if id_dec i0 i1
    then if let t2 , l2 = typ_mutrec_dec in t2 t0 t1
         then list_value_l_dec l0 l1
         else false
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
                 | c :: cs3 -> false)
      | a :: l1 ->
          (match cs2 with
             | [] -> false
             | c :: cs3 -> if cmd_dec a c then cmds_dec l1 cs3 else false)
  
  (** val phinodes_dec :
      LLVMsyntax.phinode list -> LLVMsyntax.phinode list -> bool **)
  
  let rec phinodes_dec l0 ps2 =
    match l0 with
      | [] -> (match ps2 with
                 | [] -> true
                 | p :: ps3 -> false)
      | a :: l1 ->
          (match ps2 with
             | [] -> false
             | p :: ps3 ->
                 if phinode_dec a p then phinodes_dec l1 ps3 else false)
  
  (** val block_dec : LLVMsyntax.block -> LLVMsyntax.block -> bool **)
  
  let block_dec b1 b2 =
    let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b1 in
    let LLVMsyntax.Coq_block_intro (l1, p0, c0, t1) = b2 in
    if id_dec l0 l1
    then if phinodes_dec p p0
         then if cmds_dec c c0 then terminator_dec t0 t1 else false
         else false
    else false
  
  (** val arg_dec : LLVMsyntax.arg -> LLVMsyntax.arg -> bool **)
  
  let arg_dec a1 a2 =
    let t0 , i0 = a1 in
    let t1 , i1 = a2 in
    if id_dec i0 i1 then let t2 , l0 = typ_mutrec_dec in t2 t0 t1 else false
  
  (** val args_dec : LLVMsyntax.args -> LLVMsyntax.args -> bool **)
  
  let rec args_dec l0 l2 =
    match l0 with
      | [] -> (match l2 with
                 | [] -> true
                 | p :: l3 -> false)
      | a :: l1 ->
          (match l2 with
             | [] -> false
             | p :: l3 -> if arg_dec a p then args_dec l1 l3 else false)
  
  (** val fheader_dec : LLVMsyntax.fheader -> LLVMsyntax.fheader -> bool **)
  
  let fheader_dec f1 f2 =
    let LLVMsyntax.Coq_fheader_intro (t0, i0, a) = f1 in
    let LLVMsyntax.Coq_fheader_intro (t1, i1, a0) = f2 in
    if let t2 , l0 = typ_mutrec_dec in t2 t0 t1
    then if id_dec i0 i1 then args_dec a a0 else false
    else false
  
  (** val blocks_dec : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool **)
  
  let rec blocks_dec l0 lb' =
    match l0 with
      | [] -> (match lb' with
                 | [] -> true
                 | b :: lb'0 -> false)
      | a :: l1 ->
          (match lb' with
             | [] -> false
             | b :: lb'0 ->
                 if block_dec a b then blocks_dec l1 lb'0 else false)
  
  (** val fdec_dec : LLVMsyntax.fdec -> LLVMsyntax.fdec -> bool **)
  
  let fdec_dec f1 f2 =
    fheader_dec f1 f2
  
  (** val fdef_dec : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool **)
  
  let fdef_dec f1 f2 =
    let LLVMsyntax.Coq_fdef_intro (f, b) = f1 in
    let LLVMsyntax.Coq_fdef_intro (f0, b0) = f2 in
    if fheader_dec f f0 then blocks_dec b b0 else false
  
  (** val gvar_dec : LLVMsyntax.gvar -> LLVMsyntax.gvar -> bool **)
  
  let gvar_dec g1 g2 =
    let LLVMsyntax.Coq_gvar_intro (i0, t0, c, a) = g1 in
    let LLVMsyntax.Coq_gvar_intro (i1, t1, c0, a0) = g2 in
    if id_dec i0 i1
    then if let t2 , l0 = typ_mutrec_dec in t2 t0 t1
         then if let c1 , l0 = const_mutrec_dec in c1 c c0
              then align_dec a a0
              else false
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
                 | p :: lp'0 -> false)
      | a :: l1 ->
          (match lp' with
             | [] -> false
             | p :: lp'0 ->
                 if product_dec a p then products_dec l1 lp'0 else false)
  
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
                 if sz_dec s s0
                 then if align_dec a a1 then align_dec a0 a2 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_layout_int (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_int (s0, a1, a2) ->
                 if sz_dec s s0
                 then if align_dec a a1 then align_dec a0 a2 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_layout_aggr (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_aggr (s0, a1, a2) ->
                 if sz_dec s s0
                 then if align_dec a a1 then align_dec a0 a2 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_layout_stack (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_stack (s0, a1, a2) ->
                 if sz_dec s s0
                 then if align_dec a a1 then align_dec a0 a2 else false
                 else false
             | _ -> false)
  
  (** val layouts_dec : LLVMsyntax.layouts -> LLVMsyntax.layouts -> bool **)
  
  let rec layouts_dec l0 l2 =
    match l0 with
      | [] -> (match l2 with
                 | [] -> true
                 | l1 :: l3 -> false)
      | a :: l1 ->
          (match l2 with
             | [] -> false
             | l3 :: l4 ->
                 if layout_dec a l3 then layouts_dec l1 l4 else false)
  
  (** val module_dec :
      LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool **)
  
  let module_dec m m' =
    let LLVMsyntax.Coq_module_intro (l0, p) = m in
    let LLVMsyntax.Coq_module_intro (l1, p0) = m' in
    if layouts_dec l0 l1 then products_dec p p0 else false
  
  (** val modules_dec : LLVMsyntax.modules -> LLVMsyntax.modules -> bool **)
  
  let rec modules_dec l0 lm' =
    match l0 with
      | [] -> (match lm' with
                 | [] -> true
                 | m :: lm'0 -> false)
      | a :: l1 ->
          (match lm' with
             | [] -> false
             | m :: lm'0 ->
                 if module_dec a m then modules_dec l1 lm'0 else false)
  
  (** val system_dec : LLVMsyntax.system -> LLVMsyntax.system -> bool **)
  
  let system_dec s s' =
    modules_dec s s'
  
  (** val typEqB : LLVMsyntax.typ -> LLVMsyntax.typ -> bool **)
  
  let typEqB t1 t2 =
    sumbool2bool (let t0 , l0 = typ_mutrec_dec in t0 t1 t2)
  
  (** val list_typEqB :
      LLVMsyntax.list_typ -> LLVMsyntax.list_typ -> bool **)
  
  let list_typEqB lt1 lt2 =
    sumbool2bool (let t0 , l0 = typ_mutrec_dec in l0 lt1 lt2)
  
  (** val idEqB : LLVMsyntax.id -> LLVMsyntax.id -> bool **)
  
  let idEqB i0 i' =
    sumbool2bool (id_dec i0 i')
  
  (** val constEqB : LLVMsyntax.const -> LLVMsyntax.const -> bool **)
  
  let constEqB c1 c2 =
    sumbool2bool (let c , l0 = const_mutrec_dec in c c1 c2)
  
  (** val list_constEqB :
      LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool **)
  
  let list_constEqB lc1 lc2 =
    sumbool2bool (let c , l0 = const_mutrec_dec in l0 lc1 lc2)
  
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
    | i' :: li' -> if cmdEqB i0 i' then true else coq_InCmdsB i0 li'
  
  (** val coq_InPhiNodesB :
      LLVMsyntax.phinode -> LLVMsyntax.phinodes -> bool **)
  
  let rec coq_InPhiNodesB i0 = function
    | [] -> false
    | i' :: li' -> if phinodeEqB i0 i' then true else coq_InPhiNodesB i0 li'
  
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
    | a' :: la' ->
        if let t0 , id0 = a in
           let t' , id' = a' in
           if sumbool2bool (let t1 , l0 = typ_mutrec_dec in t1 t0 t')
           then idEqB id0 id'
           else false
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
    | b' :: lb' -> if blockEqB b b' then true else coq_InBlocksB b lb'
  
  (** val blockInFdefB : LLVMsyntax.block -> LLVMsyntax.fdef -> bool **)
  
  let blockInFdefB b = function
    | LLVMsyntax.Coq_fdef_intro (fh, lb) -> coq_InBlocksB b lb
  
  (** val coq_InProductsB :
      LLVMsyntax.product -> LLVMsyntax.products -> bool **)
  
  let rec coq_InProductsB p = function
    | [] -> false
    | p' :: lp' -> if productEqB p p' then true else coq_InProductsB p lp'
  
  (** val productInModuleB :
      LLVMsyntax.product -> LLVMsyntax.coq_module -> bool **)
  
  let productInModuleB p = function
    | LLVMsyntax.Coq_module_intro (os, ps) -> coq_InProductsB p ps
  
  (** val coq_InModulesB :
      LLVMsyntax.coq_module -> LLVMsyntax.modules -> bool **)
  
  let rec coq_InModulesB m = function
    | [] -> false
    | m' :: lm' -> if moduleEqB m m' then true else coq_InModulesB m lm'
  
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
    | m , p0 ->
        let ui , ub = p0 in
        if moduleInSystemB m s then productInModuleB p m else false
  
  (** val blockInSystemModuleFdefB :
      LLVMsyntax.block -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      LLVMsyntax.fdef -> bool **)
  
  let blockInSystemModuleFdefB b s m f =
    if blockInFdefB b f
    then if moduleInSystemB m s
         then productInModuleB (LLVMsyntax.Coq_product_fdef f) m
         else false
    else false
  
  (** val blockInSystemModuleIFdefIB :
      LLVMsyntax.block -> LLVMsyntax.system -> LLVMsyntax.module_info ->
      LLVMsyntax.fdef_info -> bool **)
  
  let blockInSystemModuleIFdefIB b s mi fi =
    let m , p = mi in
    let ui , ub = p in let fd , dt0 = fi in blockInSystemModuleFdefB b s m fd
  
  (** val cmdInSystemModuleFdefBlockB :
      LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let cmdInSystemModuleFdefBlockB i0 s m f b =
    if cmdInBlockB i0 b then blockInSystemModuleFdefB b s m f else false
  
  (** val cmdInSystemModuleIFdefIBlockB :
      LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.module_info ->
      LLVMsyntax.fdef_info -> LLVMsyntax.block -> bool **)
  
  let cmdInSystemModuleIFdefIBlockB i0 s mi fi b =
    let m , p = mi in
    let ui , ub = p in
    let fd , dt0 = fi in
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
    let m , p = mi in
    let ui , ub = p in
    let fd , dt0 = fi in
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
    let m , p = mi in
    let ui , ub = p in
    let fd , dt0 = fi in
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
    let m , p = mi in
    let ui , ub = p in
    let fd , dt0 = fi in insnInSystemModuleFdefBlockB i0 s m fd b
  
  (** val cmdInBlockB_dec : LLVMsyntax.cmd -> LLVMsyntax.block -> bool **)
  
  let cmdInBlockB_dec i0 b =
    if cmdInBlockB i0 b then true else false
  
  (** val phinodeInBlockB_dec :
      LLVMsyntax.phinode -> LLVMsyntax.block -> bool **)
  
  let phinodeInBlockB_dec i0 b =
    if phinodeInBlockB i0 b then true else false
  
  (** val terminatorInBlockB_dec :
      LLVMsyntax.terminator -> LLVMsyntax.block -> bool **)
  
  let terminatorInBlockB_dec i0 b =
    if terminatorInBlockB i0 b then true else false
  
  (** val getParentOfCmdFromBlocks :
      LLVMsyntax.cmd -> LLVMsyntax.blocks -> LLVMsyntax.block option **)
  
  let rec getParentOfCmdFromBlocks i0 = function
    | [] -> None
    | b :: lb' ->
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
    | p :: lp' ->
        (match match p with
                 | LLVMsyntax.Coq_product_fdef fd ->
                     getParentOfCmdFromFdef i0 fd
                 | _ -> None with
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
    | m :: lm' ->
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
    | b :: lb' ->
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
    | p :: lp' ->
        (match match p with
                 | LLVMsyntax.Coq_product_fdef fd ->
                     getParentOfPhiNodeFromFdef i0 fd
                 | _ -> None with
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
    | m :: lm' ->
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
    | b :: lb' ->
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
    | p :: lp' ->
        (match match p with
                 | LLVMsyntax.Coq_product_fdef fd ->
                     getParentOfTerminatorFromFdef i0 fd
                 | _ -> None with
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
    | m :: lm' ->
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
    if productInModuleB b m then true else false
  
  (** val getParentOfFdefFromModules :
      LLVMsyntax.fdef -> LLVMsyntax.modules -> LLVMsyntax.coq_module option **)
  
  let rec getParentOfFdefFromModules fd = function
    | [] -> None
    | m :: lm' ->
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
                 if eqDec_atom l0 l1
                 then set_add (fun x x0 -> eqDec_atom x x0) id1
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
      let LLVMsyntax.Coq_fheader_intro (t0, i1, la) = f in
      (match nth_error la i0 with
         | Some a -> Some a
         | None -> None)
    
    (** val getArgumentType :
        LLVMsyntax.fdef -> nat -> LLVMsyntax.typ option **)
    
    let getArgumentType fd i0 =
      match getArgument fd i0 with
        | Some a -> let t0 , i1 = a in Some t0
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
             let v , l0 = p in
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
      | LLVMsyntax.Coq_typ_struct lt -> isSizedListTyp lt
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
      | LLVMsyntax.Coq_typ_struct lt -> isSizedListTyp lt
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
      | LLVMsyntax.Coq_typ_struct lt -> isSizedListTyp lt
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
      | LLVMsyntax.Coq_typ_function (t1, lt) -> Some
          (length (LLVMsyntax.unmake_list_typ lt))
      | _ -> None
    
    (** val isVarArg : LLVMsyntax.typ -> bool **)
    
    let isVarArg t0 =
      false
    
    (** val getParamType : LLVMsyntax.typ -> nat -> LLVMsyntax.typ option **)
    
    let getParamType t0 i0 =
      match t0 with
        | LLVMsyntax.Coq_typ_function (t1, lt) ->
            (match LLVMsyntax.nth_list_typ i0 lt with
               | Some t2 -> Some t2
               | None -> None)
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
      | LLVMsyntax.Coq_typ_struct lt -> isSizedListTyp lt
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
      | LLVMsyntax.Coq_typ_struct lt -> isSizedListTyp lt
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
      | LLVMsyntax.Coq_typ_struct lt -> isSizedListTyp lt
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
    if lset_mem l2 (d l1) then ReflectT else ReflectF
  
  (** val ifP :
      LLVMsyntax.dt -> LLVMsyntax.block -> LLVMsyntax.block -> 'a1 option ->
      'a1 option -> 'a1 option **)
  
  let ifP d b1 b2 t0 f =
    match reflect_blockDominates d b1 b2 with
      | ReflectT -> t0
      | ReflectF -> f
 end

type maddr = nat

type mblock = maddr

type malloca = mblock -> maddr option

type mbyte =
  | Mbyte_var of nat
  | Mbyte_uninit

type mem0 = { data : (maddr -> mbyte); allocas : malloca }

type mvalue = mbyte list

type event =
  | MkEvent

type trace =
  | Trace_nil
  | Trace_cons of event * trace

type genericValue = mvalue

type gVMap = (LLVMsyntax.id * genericValue) list

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
    | c :: cs' ->
        (match cmd2nbranch c with
           | Some nb ->
               (match cmds2nbranchs cs' with
                  | Some nbs' -> Some (nb :: nbs')
                  | None -> None)
           | None -> None)
  
  (** val nbranchs2cmds : nbranch list -> LLVMsyntax.cmd list **)
  
  let rec nbranchs2cmds = function
    | [] -> []
    | n :: nbs' -> n :: (nbranchs2cmds nbs')
  
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
  
  (** val cmds2sbs : LLVMsyntax.cmds -> subblock list * nbranch list **)
  
  let rec cmds2sbs = function
    | [] -> [] , []
    | c :: cs' ->
        if isCallInst_dec c
        then let l0 , nbs0 = cmds2sbs cs' in
             (match l0 with
                | [] -> [] , (c :: nbs0)
                | s :: sbs' ->
                    let { coq_NBs = nbs; call_cmd = call0 } = s in
                    ({ coq_NBs = (c :: nbs); call_cmd = call0 } :: sbs') ,
                    nbs0)
        else let sbs , nbs0 = cmds2sbs cs' in
             ({ coq_NBs = []; call_cmd = c } :: sbs) , nbs0
  
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
  
  let sframe_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 s =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s1, s2, s3) -> f0 b s1 s2 (f24 s2) s3 (f24 s3)
      | Coq_sterm_extractvalue (t0, s1, l0) -> f1 t0 s1 (f24 s1) l0
      | Coq_sterm_insertvalue (t0, s1, t1, s2, l0) ->
          f2 t0 s1 (f24 s1) t1 s2 (f24 s2) l0
      | Coq_sterm_malloc (s1, t0, s2, a) -> f3 s1 (f27 s1) t0 s2 a
      | Coq_sterm_alloca (s1, t0, s2, a) -> f4 s1 (f27 s1) t0 s2 a
      | Coq_sterm_load (s1, t0, s2, a) -> f5 s1 (f27 s1) t0 s2 (f24 s2) a
      | Coq_sterm_gep (i0, t0, s1, l0) -> f6 i0 t0 s1 (f24 s1) l0 (f25 l0)
      | Coq_sterm_ext (e, t0, s1, t1) -> f7 e t0 s1 (f24 s1) t1
      | Coq_sterm_cast (c, t0, s1, t1) -> f8 c t0 s1 (f24 s1) t1
      | Coq_sterm_icmp (c, t0, s1, s2) -> f9 c t0 s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_phi (t0, l0) -> f10 t0 l0 (f26 l0)
      | Coq_sterm_select (s1, t0, s2, s3) ->
          f11 s1 (f24 s1) t0 s2 (f24 s2) s3 (f24 s3)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s0, l1) -> f13 s0 (f24 s0) l1 (f25 l1)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s0, l1, l2) -> f15 s0 (f24 s0) l1 l2 (f26 l2)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s1, t0, s2, a) -> f17 s1 (f27 s1) t0 s2 a
      | Coq_smem_free (s1, t0, s2) -> f18 s1 (f27 s1) t0 s2 (f24 s2)
      | Coq_smem_alloca (s1, t0, s2, a) -> f19 s1 (f27 s1) t0 s2 a
      | Coq_smem_load (s1, t0, s2, a) -> f20 s1 (f27 s1) t0 s2 (f24 s2) a
      | Coq_smem_store (s1, t0, s2, s3, a) ->
          f21 s1 (f27 s1) t0 s2 (f24 s2) s3 (f24 s3) a
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s1, s2, t0, s3, a) ->
          f23 s1 (f27 s1) s2 (f28 s2) t0 s3 a
    in f28 s
  
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
  
  let smem_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 s =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s1, s2, s3) -> f0 b s1 s2 (f24 s2) s3 (f24 s3)
      | Coq_sterm_extractvalue (t0, s1, l0) -> f1 t0 s1 (f24 s1) l0
      | Coq_sterm_insertvalue (t0, s1, t1, s2, l0) ->
          f2 t0 s1 (f24 s1) t1 s2 (f24 s2) l0
      | Coq_sterm_malloc (s1, t0, s2, a) -> f3 s1 (f27 s1) t0 s2 a
      | Coq_sterm_alloca (s1, t0, s2, a) -> f4 s1 (f27 s1) t0 s2 a
      | Coq_sterm_load (s1, t0, s2, a) -> f5 s1 (f27 s1) t0 s2 (f24 s2) a
      | Coq_sterm_gep (i0, t0, s1, l0) -> f6 i0 t0 s1 (f24 s1) l0 (f25 l0)
      | Coq_sterm_ext (e, t0, s1, t1) -> f7 e t0 s1 (f24 s1) t1
      | Coq_sterm_cast (c, t0, s1, t1) -> f8 c t0 s1 (f24 s1) t1
      | Coq_sterm_icmp (c, t0, s1, s2) -> f9 c t0 s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_phi (t0, l0) -> f10 t0 l0 (f26 l0)
      | Coq_sterm_select (s1, t0, s2, s3) ->
          f11 s1 (f24 s1) t0 s2 (f24 s2) s3 (f24 s3)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s0, l1) -> f13 s0 (f24 s0) l1 (f25 l1)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s0, l1, l2) -> f15 s0 (f24 s0) l1 l2 (f26 l2)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s1, t0, s2, a) -> f17 s1 (f27 s1) t0 s2 a
      | Coq_smem_free (s1, t0, s2) -> f18 s1 (f27 s1) t0 s2 (f24 s2)
      | Coq_smem_alloca (s1, t0, s2, a) -> f19 s1 (f27 s1) t0 s2 a
      | Coq_smem_load (s1, t0, s2, a) -> f20 s1 (f27 s1) t0 s2 (f24 s2) a
      | Coq_smem_store (s1, t0, s2, s3, a) ->
          f21 s1 (f27 s1) t0 s2 (f24 s2) s3 (f24 s3) a
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s1, s2, t0, s3, a) ->
          f23 s1 (f27 s1) s2 (f28 s2) t0 s3 a
    in f27 s
  
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
  
  let list_sterm_l_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 l0 =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_extractvalue (t0, s0, l1) -> f1 t0 s0 (f24 s0) l1
      | Coq_sterm_insertvalue (t0, s0, t1, s1, l1) ->
          f2 t0 s0 (f24 s0) t1 s1 (f24 s1) l1
      | Coq_sterm_malloc (s0, t0, s1, a) -> f3 s0 (f27 s0) t0 s1 a
      | Coq_sterm_alloca (s0, t0, s1, a) -> f4 s0 (f27 s0) t0 s1 a
      | Coq_sterm_load (s0, t0, s1, a) -> f5 s0 (f27 s0) t0 s1 (f24 s1) a
      | Coq_sterm_gep (i0, t0, s0, l1) -> f6 i0 t0 s0 (f24 s0) l1 (f25 l1)
      | Coq_sterm_ext (e, t0, s0, t1) -> f7 e t0 s0 (f24 s0) t1
      | Coq_sterm_cast (c, t0, s0, t1) -> f8 c t0 s0 (f24 s0) t1
      | Coq_sterm_icmp (c, t0, s0, s1) -> f9 c t0 s0 (f24 s0) s1 (f24 s1)
      | Coq_sterm_phi (t0, l1) -> f10 t0 l1 (f26 l1)
      | Coq_sterm_select (s0, t0, s1, s2) ->
          f11 s0 (f24 s0) t0 s1 (f24 s1) s2 (f24 s2)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s, l2) -> f13 s (f24 s) l2 (f25 l2)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s, l2, l3) -> f15 s (f24 s) l2 l3 (f26 l3)
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
    in f26 l0
  
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
  
  let list_sterm_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 l0 =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_extractvalue (t0, s0, l1) -> f1 t0 s0 (f24 s0) l1
      | Coq_sterm_insertvalue (t0, s0, t1, s1, l1) ->
          f2 t0 s0 (f24 s0) t1 s1 (f24 s1) l1
      | Coq_sterm_malloc (s0, t0, s1, a) -> f3 s0 (f27 s0) t0 s1 a
      | Coq_sterm_alloca (s0, t0, s1, a) -> f4 s0 (f27 s0) t0 s1 a
      | Coq_sterm_load (s0, t0, s1, a) -> f5 s0 (f27 s0) t0 s1 (f24 s1) a
      | Coq_sterm_gep (i0, t0, s0, l1) -> f6 i0 t0 s0 (f24 s0) l1 (f25 l1)
      | Coq_sterm_ext (e, t0, s0, t1) -> f7 e t0 s0 (f24 s0) t1
      | Coq_sterm_cast (c, t0, s0, t1) -> f8 c t0 s0 (f24 s0) t1
      | Coq_sterm_icmp (c, t0, s0, s1) -> f9 c t0 s0 (f24 s0) s1 (f24 s1)
      | Coq_sterm_phi (t0, l1) -> f10 t0 l1 (f26 l1)
      | Coq_sterm_select (s0, t0, s1, s2) ->
          f11 s0 (f24 s0) t0 s1 (f24 s1) s2 (f24 s2)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s, l2) -> f13 s (f24 s) l2 (f25 l2)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s, l2, l3) -> f15 s (f24 s) l2 l3 (f26 l3)
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
    in f25 l0
  
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
  
  let sterm_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 s =
    let rec f24 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s1, s2, s3) -> f0 b s1 s2 (f24 s2) s3 (f24 s3)
      | Coq_sterm_extractvalue (t0, s1, l0) -> f1 t0 s1 (f24 s1) l0
      | Coq_sterm_insertvalue (t0, s1, t1, s2, l0) ->
          f2 t0 s1 (f24 s1) t1 s2 (f24 s2) l0
      | Coq_sterm_malloc (s1, t0, s2, a) -> f3 s1 (f27 s1) t0 s2 a
      | Coq_sterm_alloca (s1, t0, s2, a) -> f4 s1 (f27 s1) t0 s2 a
      | Coq_sterm_load (s1, t0, s2, a) -> f5 s1 (f27 s1) t0 s2 (f24 s2) a
      | Coq_sterm_gep (i0, t0, s1, l0) -> f6 i0 t0 s1 (f24 s1) l0 (f25 l0)
      | Coq_sterm_ext (e, t0, s1, t1) -> f7 e t0 s1 (f24 s1) t1
      | Coq_sterm_cast (c, t0, s1, t1) -> f8 c t0 s1 (f24 s1) t1
      | Coq_sterm_icmp (c, t0, s1, s2) -> f9 c t0 s1 (f24 s1) s2 (f24 s2)
      | Coq_sterm_phi (t0, l0) -> f10 t0 l0 (f26 l0)
      | Coq_sterm_select (s1, t0, s2, s3) ->
          f11 s1 (f24 s1) t0 s2 (f24 s2) s3 (f24 s3)
    and f25 = function
      | Nil_list_sterm -> f12
      | Cons_list_sterm (s0, l1) -> f13 s0 (f24 s0) l1 (f25 l1)
    and f26 = function
      | Nil_list_sterm_l -> f14
      | Cons_list_sterm_l (s0, l1, l2) -> f15 s0 (f24 s0) l1 l2 (f26 l2)
    and f27 = function
      | Coq_smem_init -> f16
      | Coq_smem_malloc (s1, t0, s2, a) -> f17 s1 (f27 s1) t0 s2 a
      | Coq_smem_free (s1, t0, s2) -> f18 s1 (f27 s1) t0 s2 (f24 s2)
      | Coq_smem_alloca (s1, t0, s2, a) -> f19 s1 (f27 s1) t0 s2 a
      | Coq_smem_load (s1, t0, s2, a) -> f20 s1 (f27 s1) t0 s2 (f24 s2) a
      | Coq_smem_store (s1, t0, s2, s3, a) ->
          f21 s1 (f27 s1) t0 s2 (f24 s2) s3 (f24 s3) a
    and f28 = function
      | Coq_sframe_init -> f22
      | Coq_sframe_alloca (s1, s2, t0, s3, a) ->
          f23 s1 (f27 s1) s2 (f28 s2) t0 s3 a
    in f24 s
  
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
      LLVMsyntax.align -> 'a5) -> ((((sterm -> 'a1) * (list_sterm -> 'a2)) *
      (list_sterm_l -> 'a3)) * (smem -> 'a4)) * (sframe -> 'a5) **)
  
  let se_mutrec h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 =
    ((((fun x ->
      sterm_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
        h18 h19 h20 h21 h22 h23 h24 h25 x) , (fun x ->
      list_sterm_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
        h17 h18 h19 h20 h21 h22 h23 h24 h25 x)) , (fun x ->
      list_sterm_l_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 x)) , (fun x ->
      smem_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
        h18 h19 h20 h21 h22 h23 h24 h25 x)) , (fun x ->
      sframe_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
        h18 h19 h20 h21 h22 h23 h24 h25 x)
  
  (** val map_list_sterm : (sterm -> 'a1) -> list_sterm -> 'a1 list **)
  
  let rec map_list_sterm f = function
    | Nil_list_sterm -> []
    | Cons_list_sterm (h, tl_) -> (f h) :: (map_list_sterm f tl_)
  
  (** val make_list_sterm : sterm list -> list_sterm **)
  
  let rec make_list_sterm = function
    | [] -> Nil_list_sterm
    | h :: tl_ -> Cons_list_sterm (h, (make_list_sterm tl_))
  
  (** val unmake_list_sterm : list_sterm -> sterm list **)
  
  let rec unmake_list_sterm = function
    | Nil_list_sterm -> []
    | Cons_list_sterm (h, tl_) -> h :: (unmake_list_sterm tl_)
  
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
    | Cons_list_sterm_l (h0, h1, tl_) -> (f h0 h1) ::
        (map_list_sterm_l f tl_)
  
  (** val make_list_sterm_l : (sterm * LLVMsyntax.l) list -> list_sterm_l **)
  
  let rec make_list_sterm_l = function
    | [] -> Nil_list_sterm_l
    | p :: tl_ ->
        let h0 , h1 = p in
        Cons_list_sterm_l (h0, h1, (make_list_sterm_l tl_))
  
  (** val unmake_list_sterm_l :
      list_sterm_l -> (sterm * LLVMsyntax.l) list **)
  
  let rec unmake_list_sterm_l = function
    | Nil_list_sterm_l -> []
    | Cons_list_sterm_l (h0, h1, tl_) -> (h0 , h1) ::
        (unmake_list_sterm_l tl_)
  
  (** val nth_list_sterm_l :
      nat -> list_sterm_l -> (sterm * LLVMsyntax.l) option **)
  
  let rec nth_list_sterm_l n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_sterm_l -> None
             | Cons_list_sterm_l (h0, h1, tl_) -> Some (h0 , h1))
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
       * (LLVMsyntax.typ * sterm) list
  
  (** val scall_rect :
      (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.tailc ->
      LLVMsyntax.typ -> LLVMsyntax.id -> (LLVMsyntax.typ * sterm) list ->
      'a1) -> scall -> 'a1 **)
  
  let scall_rect f = function
    | Coq_stmn_call (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
  
  (** val scall_rec :
      (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.tailc ->
      LLVMsyntax.typ -> LLVMsyntax.id -> (LLVMsyntax.typ * sterm) list ->
      'a1) -> scall -> 'a1 **)
  
  let scall_rec f = function
    | Coq_stmn_call (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
  
  type smap = (AtomImpl.atom * sterm) list
  
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
      | p :: sm' ->
          let id0 , s0 = p in
          if eqDec_atom i0 id0 then s0 else lookupSmap sm' i0
  
  (** val value2Sterm : smap -> LLVMsyntax.value -> sterm **)
  
  let value2Sterm sm v = match v with
    | LLVMsyntax.Coq_value_id i0 -> lookupSmap sm i0
    | LLVMsyntax.Coq_value_const c -> Coq_sterm_val v
  
  (** val list_param__list_typ_subst_sterm :
      LLVMsyntax.params -> smap -> (LLVMsyntax.typ * sterm) list **)
  
  let rec list_param__list_typ_subst_sterm list_param1 sm =
    match list_param1 with
      | [] -> []
      | p :: list_param1' ->
          let t0 , v = p in
          (t0 ,
          (match v with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap sm i0
             | LLVMsyntax.Coq_value_const c -> Coq_sterm_val v)) ::
          (list_param__list_typ_subst_sterm list_param1' sm)
  
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
    | LLVMsyntax.Coq_insn_load (id0, t2, v2, align0) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_load (st.coq_SMem, t2,
          (match v2 with
             | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
             | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v2), align0)));
        coq_SMem = (Coq_smem_load (st.coq_SMem, t2,
        (match v2 with
           | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
           | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v2), align0));
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_store (id0, t0, v1, v2, align0) -> { coq_STerms =
        st.coq_STerms; coq_SMem = (Coq_smem_store (st.coq_SMem, t0,
        (match v1 with
           | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
           | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v1),
        (match v2 with
           | LLVMsyntax.Coq_value_id i0 -> lookupSmap st.coq_STerms i0
           | LLVMsyntax.Coq_value_const c0 -> Coq_sterm_val v2), align0));
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
    | [] -> st
    | p :: ps' ->
        let LLVMsyntax.Coq_insn_phi (id0, t0, idls0) = p in
        _se_phinodes { coq_STerms =
          (updateAL st.coq_STerms id0 (Coq_sterm_phi (t0,
            (make_list_sterm_l
              (LLVMsyntax.map_list_value_l (fun v5 l5 ->
                (match v5 with
                   | LLVMsyntax.Coq_value_id i0 ->
                       lookupSmap st.coq_STerms i0
                   | LLVMsyntax.Coq_value_const c -> Coq_sterm_val v5) , l5)
                idls0))))); coq_SMem = st.coq_SMem; coq_SFrame =
          st.coq_SFrame; coq_SEffects = st.coq_SEffects } st0 ps'
  
  (** val se_phinodes : sstate -> LLVMsyntax.phinode list -> sstate **)
  
  let rec se_phinodes st ps =
    _se_phinodes st st ps
  
  (** val se_cmds : sstate -> nbranch list -> sstate **)
  
  let rec se_cmds st = function
    | [] -> st
    | c :: cs' -> se_cmds (se_cmd st c) cs'
  
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
               if eqDec_atom id0 id1 then s0 else s
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
      | p :: sm' -> let id0 , s0 = p in subst_mt sm' (subst_tt id0 s0 s)
  
  (** val subst_mm : smap -> smem -> smem **)
  
  let rec subst_mm sm m =
    match sm with
      | [] -> m
      | p :: sm' -> let id0 , s0 = p in subst_mm sm' (subst_tm id0 s0 m)
 end

type sterm_dec_prop = SimpleSE.sterm -> bool

type list_sterm_dec_prop = SimpleSE.list_sterm -> bool

type list_sterm_l_dec_prop = SimpleSE.list_sterm_l -> bool

type smem_dec_prop = SimpleSE.smem -> bool

type sframe_dec_prop = SimpleSE.sframe -> bool

(** val se_dec :
    ((((SimpleSE.sterm -> sterm_dec_prop) * (SimpleSE.list_sterm ->
    list_sterm_dec_prop)) * (SimpleSE.list_sterm_l -> list_sterm_l_dec_prop))
    * (SimpleSE.smem -> smem_dec_prop)) * (SimpleSE.sframe ->
    sframe_dec_prop) **)

let se_dec =
  SimpleSE.se_mutrec (fun v st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_val v0 -> LLVMlib.value_dec v v0
      | _ -> false) (fun b s s0 h s1 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_bop (b0, s2, st2_1, st2_2) ->
          if LLVMlib.bop_dec b b0
          then if LLVMlib.sz_dec s s2
               then if h st2_1 then h0 st2_2 else false
               else false
          else false
      | _ -> false) (fun t0 s h l0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_extractvalue (t1, st3, l1) ->
          if let t2 , l2 = LLVMlib.typ_mutrec_dec in t2 t0 t1
          then if h st3
               then let c , l2 = LLVMlib.const_mutrec_dec in l2 l0 l1
               else false
          else false
      | _ -> false) (fun t0 s h t1 s0 h0 l0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_insertvalue (t2, st2_1, t3, st2_2, l1) ->
          if let t4 , l2 = LLVMlib.typ_mutrec_dec in t4 t0 t2
          then if h st2_1
               then if let t4 , l2 = LLVMlib.typ_mutrec_dec in t4 t1 t3
                    then if h0 st2_2
                         then let c , l2 = LLVMlib.const_mutrec_dec in
                              l2 l0 l1
                         else false
                    else false
               else false
          else false
      | _ -> false) (fun s h t0 s0 a st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_malloc (s1, t1, s2, a0) ->
          if h s1
          then if let t2 , l0 = LLVMlib.typ_mutrec_dec in t2 t0 t1
               then if LLVMlib.sz_dec s0 s2
                    then LLVMlib.align_dec a a0
                    else false
               else false
          else false
      | _ -> false) (fun s h t0 s0 a st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_alloca (s1, t1, s2, a0) ->
          if h s1
          then if let t2 , l0 = LLVMlib.typ_mutrec_dec in t2 t0 t1
               then if LLVMlib.sz_dec s0 s2
                    then LLVMlib.align_dec a a0
                    else false
               else false
          else false
      | _ -> false) (fun s h t0 s0 h0 a st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_load (s1, t1, st3, a0) ->
          if h s1
          then if let t2 , l0 = LLVMlib.typ_mutrec_dec in t2 t0 t1
               then if LLVMlib.align_dec a a0 then h0 st3 else false
               else false
          else false
      | _ -> false) (fun i0 t0 s h l0 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_gep (i1, t1, st3, l1) ->
          if bool_dec i0 i1
          then if let t2 , l2 = LLVMlib.typ_mutrec_dec in t2 t0 t1
               then if h st3 then h0 l1 else false
               else false
          else false
      | _ -> false) (fun e t0 s h t1 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_ext (e0, t2, st3, t3) ->
          if LLVMlib.extop_dec e e0
          then if let t4 , l0 = LLVMlib.typ_mutrec_dec in t4 t0 t2
               then if h st3
                    then let t4 , l0 = LLVMlib.typ_mutrec_dec in t4 t1 t3
                    else false
               else false
          else false
      | _ -> false) (fun c t0 s h t1 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_cast (c0, t2, st3, t3) ->
          if LLVMlib.castop_dec c c0
          then if let t4 , l0 = LLVMlib.typ_mutrec_dec in t4 t0 t2
               then if h st3
                    then let t4 , l0 = LLVMlib.typ_mutrec_dec in t4 t1 t3
                    else false
               else false
          else false
      | _ -> false) (fun c t0 s h s0 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_icmp (c0, t1, st2_1, st2_2) ->
          if LLVMlib.cond_dec c c0
          then if let t2 , l0 = LLVMlib.typ_mutrec_dec in t2 t0 t1
               then if h st2_1 then h0 st2_2 else false
               else false
          else false
      | _ -> false) (fun t0 l0 h st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_phi (t1, l1) ->
          if let t2 , l2 = LLVMlib.typ_mutrec_dec in t2 t0 t1
          then h l1
          else false
      | _ -> false) (fun s h t0 s0 h0 s1 h1 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_select (st2_1, t1, st2_2, st2_3) ->
          if let t2 , l0 = LLVMlib.typ_mutrec_dec in t2 t0 t1
          then if h st2_1
               then if h0 st2_2 then h1 st2_3 else false
               else false
          else false
      | _ -> false) (fun sts2 ->
    match sts2 with
      | SimpleSE.Nil_list_sterm -> true
      | SimpleSE.Cons_list_sterm (s, sts3) -> false) (fun s h l0 h0 sts2 ->
    match sts2 with
      | SimpleSE.Nil_list_sterm -> false
      | SimpleSE.Cons_list_sterm (s0, sts3) ->
          if h s0 then h0 sts3 else false) (fun stls2 ->
    match stls2 with
      | SimpleSE.Nil_list_sterm_l -> true
      | SimpleSE.Cons_list_sterm_l (s, l0, stls3) -> false)
    (fun s h l0 l1 h0 stls2 ->
    match stls2 with
      | SimpleSE.Nil_list_sterm_l -> false
      | SimpleSE.Cons_list_sterm_l (s0, l2, stls3) ->
          if h s0
          then if LLVMlib.l_dec l0 l2 then h0 stls3 else false
          else false) (fun sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_init -> true
      | _ -> false) (fun s h t0 s0 a sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_malloc (sm3, t1, s1, a0) ->
          if h sm3
          then if let t2 , l0 = LLVMlib.typ_mutrec_dec in t2 t0 t1
               then if LLVMlib.sz_dec s0 s1
                    then LLVMlib.align_dec a a0
                    else false
               else false
          else false
      | _ -> false) (fun s h t0 s0 h0 sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_free (sm3, t1, s1) ->
          if h sm3
          then if let t2 , l0 = LLVMlib.typ_mutrec_dec in t2 t0 t1
               then h0 s1
               else false
          else false
      | _ -> false) (fun s h t0 s0 a sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_alloca (sm3, t1, s1, a0) ->
          if h sm3
          then if let t2 , l0 = LLVMlib.typ_mutrec_dec in t2 t0 t1
               then if LLVMlib.sz_dec s0 s1
                    then LLVMlib.align_dec a a0
                    else false
               else false
          else false
      | _ -> false) (fun s h t0 s0 h0 a sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_load (sm3, t1, s1, a0) ->
          if h sm3
          then if let t2 , l0 = LLVMlib.typ_mutrec_dec in t2 t0 t1
               then if LLVMlib.align_dec a a0 then h0 s1 else false
               else false
          else false
      | _ -> false) (fun s h t0 s0 h0 s1 h1 a sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_store (sm3, t1, s2, s3, a0) ->
          if h sm3
          then if let t2 , l0 = LLVMlib.typ_mutrec_dec in t2 t0 t1
               then if LLVMlib.align_dec a a0
                    then if h0 s2 then h1 s3 else false
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
          if h s2
          then if h0 sf3
               then if let t2 , l0 = LLVMlib.typ_mutrec_dec in t2 t0 t1
                    then if LLVMlib.sz_dec s1 s3
                         then LLVMlib.align_dec a a0
                         else false
                    else false
               else false
          else false)

(** val smap_dec : SimpleSE.smap -> SimpleSE.smap -> bool **)

let rec smap_dec l0 sm0 =
  match l0 with
    | [] -> (match sm0 with
               | [] -> true
               | p :: l1 -> false)
    | a :: l1 ->
        (match sm0 with
           | [] -> false
           | p :: l2 ->
               if let a0 , s = a in
                  let a1 , s0 = p in
                  if LLVMlib.id_dec a0 a1
                  then let p0 , x = se_dec in
                       let p1 , x0 = p0 in
                       let p2 , x1 = p1 in let h , l3 = p2 in h s s0
                  else false
               then smap_dec l1 l2
               else false)

(** val sterms_dec : SimpleSE.sterm list -> SimpleSE.sterm list -> bool **)

let rec sterms_dec l0 ts0 =
  match l0 with
    | [] -> (match ts0 with
               | [] -> true
               | s :: l1 -> false)
    | a :: l1 ->
        (match ts0 with
           | [] -> false
           | s :: l2 ->
               if let p , x = se_dec in
                  let p0 , x0 = p in
                  let p1 , x1 = p0 in let h , l3 = p1 in h a s
               then sterms_dec l1 l2
               else false)

(** val sstate_dec : SimpleSE.sstate -> SimpleSE.sstate -> bool **)

let sstate_dec sts1 sts2 =
  let { SimpleSE.coq_STerms = x; SimpleSE.coq_SMem = x0;
    SimpleSE.coq_SFrame = x1; SimpleSE.coq_SEffects = x2 } = sts1
  in
  let { SimpleSE.coq_STerms = sTerms1; SimpleSE.coq_SMem = sMem1;
    SimpleSE.coq_SFrame = sFrame1; SimpleSE.coq_SEffects = sEffects1 } = sts2
  in
  if smap_dec x sTerms1
  then if let p , x3 = se_dec in let p0 , h = p in h x0 sMem1
       then if let p , h = se_dec in h x1 sFrame1
            then sterms_dec x2 sEffects1
            else false
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
  if LLVMlib.sumbool2bool
       (sstate_dec (SimpleSE.se_cmds SimpleSE.sstate_init nbs1)
         (SimpleSE.se_cmds SimpleSE.sstate_init nbs2))
  then LLVMlib.sumbool2bool (LLVMlib.cmd_dec call1 call2)
  else false

(** val tv_subblocks :
    SimpleSE.subblock list -> SimpleSE.subblock list -> bool **)

let rec tv_subblocks sbs1 sbs2 =
  match sbs1 with
    | [] -> (match sbs2 with
               | [] -> true
               | s :: l0 -> false)
    | sb1 :: sbs1' ->
        (match sbs2 with
           | [] -> false
           | sb2 :: sbs2' ->
               if tv_subblock sb1 sb2
               then tv_subblocks sbs1' sbs2'
               else false)

(** val tv_phinodes : LLVMsyntax.phinodes -> LLVMsyntax.phinodes -> bool **)

let rec tv_phinodes ps1 ps2 =
  match ps1 with
    | [] -> (match ps2 with
               | [] -> true
               | p :: l0 -> false)
    | p1 :: ps1' ->
        (match ps2 with
           | [] -> false
           | p2 :: ps2' ->
               if LLVMlib.sumbool2bool (LLVMlib.phinode_dec p1 p2)
               then tv_phinodes ps1' ps2'
               else false)

(** val tv_block : LLVMsyntax.block -> LLVMsyntax.block -> bool **)

let tv_block b1 b2 =
  let LLVMsyntax.Coq_block_intro (l1, ps1, cs1, tmn1) = b1 in
  let LLVMsyntax.Coq_block_intro (l2, ps2, cs2, tmn2) = b2 in
  let sbs1 , nbs1 = SimpleSE.cmds2sbs cs1 in
  let sbs2 , nbs2 = SimpleSE.cmds2sbs cs2 in
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
               | b :: l0 -> false)
    | b1 :: bs1' ->
        (match bs2 with
           | [] -> false
           | b2 :: bs2' ->
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
               | p :: l0 -> false)
    | p :: ps1' ->
        (match p with
           | LLVMsyntax.Coq_product_gvar gvar1 ->
               (match ps2 with
                  | [] -> false
                  | p0 :: ps2' ->
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
                  | p0 :: ps2' ->
                      (match p0 with
                         | LLVMsyntax.Coq_product_fdec f2 ->
                             if LLVMlib.sumbool2bool (LLVMlib.fdec_dec f1 f2)
                             then tv_products ps1' ps2'
                             else false
                         | _ -> false))
           | LLVMsyntax.Coq_product_fdef f1 ->
               (match ps2 with
                  | [] -> false
                  | p0 :: ps2' ->
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
               | m :: l0 -> false)
    | m1 :: s1' ->
        (match s2 with
           | [] -> false
           | m2 :: s2' ->
               if tv_module m1 m2 then tv_system s1' s2' else false)

