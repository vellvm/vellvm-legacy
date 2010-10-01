type __ = Obj.t

type unit0 =
  | Tt

val negb : bool -> bool

type nat =
  | O
  | S of nat

type ('a, 'b) sum =
  | Inl of 'a
  | Inr of 'b

val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type 'a exc = 'a option

val value : 'a1 -> 'a1 option

val error : 'a1 option

val plus : nat -> nat -> nat

val eq_nat_dec : nat -> nat -> bool

val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3

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

val max : nat -> nat -> nat

val bool_dec : bool -> bool -> bool

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val nth_error : 'a1 list -> nat -> 'a1 exc

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

type 'a set = 'a list

val empty_set : 'a1 set

val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set

val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool

val set_inter : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set

val set_union : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set

module type Coq_DecidableType = 
 DecidableTypeOrig

module type UsualDecidableType = 
 UsualDecidableTypeOrig

module WFacts_fun : 
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
 sig 
  val eqb : E.t -> E.t -> bool
 end

module WDecide_fun : 
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
 sig 
  module F : 
   sig 
    val eqb : E.t -> E.t -> bool
   end
  
  module FSetLogicalFacts : 
   sig 
    
   end
  
  module FSetDecideAuxiliary : 
   sig 
    
   end
  
  module FSetDecideTestCases : 
   sig 
    
   end
 end

module WProperties_fun : 
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
 sig 
  module Dec : 
   sig 
    module F : 
     sig 
      val eqb : E.t -> E.t -> bool
     end
    
    module FSetLogicalFacts : 
     sig 
      
     end
    
    module FSetDecideAuxiliary : 
     sig 
      
     end
    
    module FSetDecideTestCases : 
     sig 
      
     end
   end
  
  module FM : 
   sig 
    val eqb : E.t -> E.t -> bool
   end
  
  val coq_In_dec : M.elt -> M.t -> bool
  
  val of_list : M.elt list -> M.t
  
  val to_list : M.t -> M.elt list
  
  val fold_rec :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
    'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_bis :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2 ->
    'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_nodep :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ -> 'a2
    -> 'a2) -> 'a2
  
  val fold_rec_weak :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
    -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2
  
  val fold_rel :
    (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
    'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3
  
  val set_induction :
    (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1) ->
    M.t -> 'a1
  
  val set_induction_bis :
    (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1 ->
    'a1) -> M.t -> 'a1
  
  val cardinal_inv_2 : M.t -> nat -> M.elt
  
  val cardinal_inv_2b : M.t -> M.elt
 end

module MakeRaw : 
 functor (X:DecidableType) ->
 sig 
  type elt = X.t
  
  type t = elt list
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val union : t -> t -> t
  
  val diff : t -> t -> t
  
  val inter : t -> t -> t
  
  val subset : t -> t -> bool
  
  val equal : t -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val partition : (elt -> bool) -> t -> t*t
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  val isok : elt list -> bool
 end

module Make : 
 functor (X:DecidableType) ->
 sig 
  module Raw : 
   sig 
    type elt = X.t
    
    type t = elt list
    
    val empty : t
    
    val is_empty : t -> bool
    
    val mem : elt -> t -> bool
    
    val add : elt -> t -> t
    
    val singleton : elt -> t
    
    val remove : elt -> t -> t
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val union : t -> t -> t
    
    val diff : t -> t -> t
    
    val inter : t -> t -> t
    
    val subset : t -> t -> bool
    
    val equal : t -> t -> bool
    
    val filter : (elt -> bool) -> t -> t
    
    val for_all : (elt -> bool) -> t -> bool
    
    val exists_ : (elt -> bool) -> t -> bool
    
    val partition : (elt -> bool) -> t -> t*t
    
    val cardinal : t -> nat
    
    val elements : t -> elt list
    
    val choose : t -> elt option
    
    val isok : elt list -> bool
   end
  
  module E : 
   sig 
    type t = X.t
    
    val eq_dec : t -> t -> bool
   end
  
  type elt = X.t
  
  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)
  
  val this : t_ -> Raw.t
  
  type t = t_
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val remove : elt -> t -> t
  
  val singleton : elt -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val empty : t
  
  val is_empty : t -> bool
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val cardinal : t -> nat
  
  val filter : (elt -> bool) -> t -> t
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val partition : (elt -> bool) -> t -> t*t
  
  val eq_dec : t -> t -> bool
 end

module Coq_WDecide_fun : 
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
 sig 
  module F : 
   sig 
    val eqb : E.t -> E.t -> bool
   end
  
  module FSetLogicalFacts : 
   sig 
    
   end
  
  module FSetDecideAuxiliary : 
   sig 
    
   end
  
  module FSetDecideTestCases : 
   sig 
    
   end
 end

type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
  | EmptyString
  | String of ascii * string

module Coq_Make : 
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
 sig 
  module D : 
   sig 
    module F : 
     sig 
      val eqb : X.t -> X.t -> bool
     end
    
    module FSetLogicalFacts : 
     sig 
      
     end
    
    module FSetDecideAuxiliary : 
     sig 
      
     end
    
    module FSetDecideTestCases : 
     sig 
      
     end
   end
  
  module KeySetProperties : 
   sig 
    module Dec : 
     sig 
      module F : 
       sig 
        val eqb : X.t -> X.t -> bool
       end
      
      module FSetLogicalFacts : 
       sig 
        
       end
      
      module FSetDecideAuxiliary : 
       sig 
        
       end
      
      module FSetDecideTestCases : 
       sig 
        
       end
     end
    
    module FM : 
     sig 
      val eqb : X.t -> X.t -> bool
     end
    
    val coq_In_dec : KeySet.elt -> KeySet.t -> bool
    
    val of_list : KeySet.elt list -> KeySet.t
    
    val to_list : KeySet.t -> KeySet.elt list
    
    val fold_rec :
      (KeySet.elt -> 'a1 -> 'a1) -> 'a1 -> KeySet.t -> (KeySet.t -> __ ->
      'a2) -> (KeySet.elt -> 'a1 -> KeySet.t -> KeySet.t -> __ -> __ -> __ ->
      'a2 -> 'a2) -> 'a2
    
    val fold_rec_bis :
      (KeySet.elt -> 'a1 -> 'a1) -> 'a1 -> KeySet.t -> (KeySet.t -> KeySet.t
      -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (KeySet.elt -> 'a1 -> KeySet.t ->
      __ -> __ -> 'a2 -> 'a2) -> 'a2
    
    val fold_rec_nodep :
      (KeySet.elt -> 'a1 -> 'a1) -> 'a1 -> KeySet.t -> 'a2 -> (KeySet.elt ->
      'a1 -> __ -> 'a2 -> 'a2) -> 'a2
    
    val fold_rec_weak :
      (KeySet.elt -> 'a1 -> 'a1) -> 'a1 -> (KeySet.t -> KeySet.t -> 'a1 -> __
      -> 'a2 -> 'a2) -> 'a2 -> (KeySet.elt -> 'a1 -> KeySet.t -> __ -> 'a2 ->
      'a2) -> KeySet.t -> 'a2
    
    val fold_rel :
      (KeySet.elt -> 'a1 -> 'a1) -> (KeySet.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2
      -> KeySet.t -> 'a3 -> (KeySet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) ->
      'a3
    
    val set_induction :
      (KeySet.t -> __ -> 'a1) -> (KeySet.t -> KeySet.t -> 'a1 -> KeySet.elt
      -> __ -> __ -> 'a1) -> KeySet.t -> 'a1
    
    val set_induction_bis :
      (KeySet.t -> KeySet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (KeySet.elt ->
      KeySet.t -> __ -> 'a1 -> 'a1) -> KeySet.t -> 'a1
    
    val cardinal_inv_2 : KeySet.t -> nat -> KeySet.elt
    
    val cardinal_inv_2b : KeySet.t -> KeySet.elt
   end
  
  module KeySetFacts : 
   sig 
    val eqb : X.t -> X.t -> bool
   end
  
  val one : 'a1 -> 'a1 list
  
  val dom : (X.t*'a1) list -> KeySet.t
  
  val get : X.t -> (X.t*'a1) list -> 'a1 option
  
  val map : ('a1 -> 'a2) -> (X.t*'a1) list -> (X.t*'a2) list
  
  val alist_ind :
    'a2 -> (X.t -> 'a1 -> (X.t*'a1) list -> 'a2 -> 'a2) -> (X.t*'a1) list ->
    'a2
  
  val binds_dec :
    X.t -> 'a1 -> (X.t*'a1) list -> ('a1 -> 'a1 -> bool) -> bool
  
  val binds_lookup : X.t -> (X.t*'a1) list -> ('a1, __) sum
 end

type 'a eqDec = 'a -> 'a -> bool

type 'a eqDec_eq = 'a -> 'a -> bool

val eq_dec0 : 'a1 eqDec_eq -> 'a1 -> 'a1 -> bool

val eqDec_eq_of_EqDec : 'a1 eqDec -> 'a1 eqDec_eq

module Coq0_Make : 
 functor (X:Coq_DecidableType) ->
 sig 
  module E : 
   sig 
    type t = X.t
    
    val eq_dec : t -> t -> bool
   end
  
  module X' : 
   sig 
    type t = X.t
    
    val eq_dec : t -> t -> bool
   end
  
  module MSet : 
   sig 
    module Raw : 
     sig 
      type elt = X.t
      
      type t = elt list
      
      val empty : t
      
      val is_empty : t -> bool
      
      val mem : elt -> t -> bool
      
      val add : elt -> t -> t
      
      val singleton : elt -> t
      
      val remove : elt -> t -> t
      
      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
      
      val union : t -> t -> t
      
      val diff : t -> t -> t
      
      val inter : t -> t -> t
      
      val subset : t -> t -> bool
      
      val equal : t -> t -> bool
      
      val filter : (elt -> bool) -> t -> t
      
      val for_all : (elt -> bool) -> t -> bool
      
      val exists_ : (elt -> bool) -> t -> bool
      
      val partition : (elt -> bool) -> t -> t*t
      
      val cardinal : t -> nat
      
      val elements : t -> elt list
      
      val choose : t -> elt option
      
      val isok : elt list -> bool
     end
    
    module E : 
     sig 
      type t = X.t
      
      val eq_dec : X.t -> X.t -> bool
     end
    
    type elt = X.t
    
    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)
    
    val this : t_ -> Raw.t
    
    type t = t_
    
    val mem : elt -> t -> bool
    
    val add : elt -> t -> t
    
    val remove : elt -> t -> t
    
    val singleton : elt -> t
    
    val union : t -> t -> t
    
    val inter : t -> t -> t
    
    val diff : t -> t -> t
    
    val equal : t -> t -> bool
    
    val subset : t -> t -> bool
    
    val empty : t
    
    val is_empty : t -> bool
    
    val elements : t -> elt list
    
    val choose : t -> elt option
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val cardinal : t -> nat
    
    val filter : (elt -> bool) -> t -> t
    
    val for_all : (elt -> bool) -> t -> bool
    
    val exists_ : (elt -> bool) -> t -> bool
    
    val partition : (elt -> bool) -> t -> t*t
    
    val eq_dec : t -> t -> bool
   end
  
  type elt = X.t
  
  type t = MSet.t
  
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
  
  module MF : 
   sig 
    val eqb : X.t -> X.t -> bool
   end
 end

module type ATOM = 
 sig 
  type atom 
  
  val eq_atom_dec : atom -> atom -> bool
  
  val atom_fresh_for_list : atom list -> atom
 end

module AtomImpl : 
 ATOM

module AtomDT : 
 sig 
  type t = AtomImpl.atom
  
  val eq_dec : AtomImpl.atom -> AtomImpl.atom -> bool
 end

val eqDec_atom : AtomImpl.atom eqDec

module AtomSetImpl : 
 sig 
  type elt = AtomImpl.atom
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : AtomImpl.atom -> t -> bool
  
  val add : AtomImpl.atom -> t -> t
  
  val singleton : AtomImpl.atom -> t
  
  val remove : AtomImpl.atom -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> bool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (AtomImpl.atom -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (AtomImpl.atom -> bool) -> t -> bool
  
  val exists_ : (AtomImpl.atom -> bool) -> t -> bool
  
  val filter : (AtomImpl.atom -> bool) -> t -> t
  
  val partition : (AtomImpl.atom -> bool) -> t -> t*t
  
  val cardinal : t -> nat
  
  val elements : t -> AtomImpl.atom list
  
  val choose : t -> AtomImpl.atom option
 end

module EnvImpl : 
 sig 
  module D : 
   sig 
    module F : 
     sig 
      val eqb : AtomImpl.atom -> AtomImpl.atom -> bool
     end
    
    module FSetLogicalFacts : 
     sig 
      
     end
    
    module FSetDecideAuxiliary : 
     sig 
      
     end
    
    module FSetDecideTestCases : 
     sig 
      
     end
   end
  
  module KeySetProperties : 
   sig 
    module Dec : 
     sig 
      module F : 
       sig 
        val eqb : AtomImpl.atom -> AtomImpl.atom -> bool
       end
      
      module FSetLogicalFacts : 
       sig 
        
       end
      
      module FSetDecideAuxiliary : 
       sig 
        
       end
      
      module FSetDecideTestCases : 
       sig 
        
       end
     end
    
    module FM : 
     sig 
      val eqb : AtomImpl.atom -> AtomImpl.atom -> bool
     end
    
    val coq_In_dec : AtomSetImpl.elt -> AtomSetImpl.t -> bool
    
    val of_list : AtomSetImpl.elt list -> AtomSetImpl.t
    
    val to_list : AtomSetImpl.t -> AtomSetImpl.elt list
    
    val fold_rec :
      (AtomSetImpl.elt -> 'a1 -> 'a1) -> 'a1 -> AtomSetImpl.t ->
      (AtomSetImpl.t -> __ -> 'a2) -> (AtomSetImpl.elt -> 'a1 ->
      AtomSetImpl.t -> AtomSetImpl.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2
    
    val fold_rec_bis :
      (AtomSetImpl.elt -> 'a1 -> 'a1) -> 'a1 -> AtomSetImpl.t ->
      (AtomSetImpl.t -> AtomSetImpl.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
      (AtomSetImpl.elt -> 'a1 -> AtomSetImpl.t -> __ -> __ -> 'a2 -> 'a2) ->
      'a2
    
    val fold_rec_nodep :
      (AtomSetImpl.elt -> 'a1 -> 'a1) -> 'a1 -> AtomSetImpl.t -> 'a2 ->
      (AtomSetImpl.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2
    
    val fold_rec_weak :
      (AtomSetImpl.elt -> 'a1 -> 'a1) -> 'a1 -> (AtomSetImpl.t ->
      AtomSetImpl.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (AtomSetImpl.elt ->
      'a1 -> AtomSetImpl.t -> __ -> 'a2 -> 'a2) -> AtomSetImpl.t -> 'a2
    
    val fold_rel :
      (AtomSetImpl.elt -> 'a1 -> 'a1) -> (AtomSetImpl.elt -> 'a2 -> 'a2) ->
      'a1 -> 'a2 -> AtomSetImpl.t -> 'a3 -> (AtomSetImpl.elt -> 'a1 -> 'a2 ->
      __ -> 'a3 -> 'a3) -> 'a3
    
    val set_induction :
      (AtomSetImpl.t -> __ -> 'a1) -> (AtomSetImpl.t -> AtomSetImpl.t -> 'a1
      -> AtomSetImpl.elt -> __ -> __ -> 'a1) -> AtomSetImpl.t -> 'a1
    
    val set_induction_bis :
      (AtomSetImpl.t -> AtomSetImpl.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
      (AtomSetImpl.elt -> AtomSetImpl.t -> __ -> 'a1 -> 'a1) -> AtomSetImpl.t
      -> 'a1
    
    val cardinal_inv_2 : AtomSetImpl.t -> nat -> AtomSetImpl.elt
    
    val cardinal_inv_2b : AtomSetImpl.t -> AtomSetImpl.elt
   end
  
  module KeySetFacts : 
   sig 
    val eqb : AtomImpl.atom -> AtomImpl.atom -> bool
   end
  
  val one : 'a1 -> 'a1 list
  
  val dom : (AtomImpl.atom*'a1) list -> AtomSetImpl.t
  
  val get : AtomImpl.atom -> (AtomImpl.atom*'a1) list -> 'a1 option
  
  val map :
    ('a1 -> 'a2) -> (AtomImpl.atom*'a1) list -> (AtomImpl.atom*'a2) list
  
  val alist_ind :
    'a2 -> (AtomImpl.atom -> 'a1 -> (AtomImpl.atom*'a1) list -> 'a2 -> 'a2)
    -> (AtomImpl.atom*'a1) list -> 'a2
  
  val binds_dec :
    AtomImpl.atom -> 'a1 -> (AtomImpl.atom*'a1) list -> ('a1 -> 'a1 -> bool)
    -> bool
  
  val binds_lookup :
    AtomImpl.atom -> (AtomImpl.atom*'a1) list -> ('a1, __) sum
 end

type 'x assocList = (AtomImpl.atom*'x) list

val updateAddAL : 'a1 assocList -> AtomImpl.atom -> 'a1 -> 'a1 assocList

val updateAL : 'a1 assocList -> AtomImpl.atom -> 'a1 -> 'a1 assocList

val lookupAL : 'a1 assocList -> AtomImpl.atom -> 'a1 option

module LLVMsyntax : 
 sig 
  val last_opt : 'a1 list -> 'a1 option
  
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
  
  type list_value_l =
    | Nil_list_value_l
    | Cons_list_value_l of value * l * list_value_l
  
  val list_value_l_rect :
    'a1 -> (value -> l -> list_value_l -> 'a1 -> 'a1) -> list_value_l -> 'a1
  
  val list_value_l_rec :
    'a1 -> (value -> l -> list_value_l -> 'a1 -> 'a1) -> list_value_l -> 'a1
  
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
  
  val cmd_rect :
    (id -> bop -> sz -> value -> value -> 'a1) -> (id -> typ -> value ->
    list_const -> 'a1) -> (id -> typ -> value -> typ -> value -> list_const
    -> 'a1) -> (id -> typ -> sz -> align -> 'a1) -> (id -> typ -> value ->
    'a1) -> (id -> typ -> sz -> align -> 'a1) -> (id -> typ -> value -> align
    -> 'a1) -> (id -> typ -> value -> value -> align -> 'a1) -> (id ->
    inbounds -> typ -> value -> list_value -> 'a1) -> (id -> extop -> typ ->
    value -> typ -> 'a1) -> (id -> castop -> typ -> value -> typ -> 'a1) ->
    (id -> cond -> typ -> value -> value -> 'a1) -> (id -> value -> typ ->
    value -> value -> 'a1) -> (id -> noret -> tailc -> typ -> id -> params ->
    'a1) -> cmd -> 'a1
  
  val cmd_rec :
    (id -> bop -> sz -> value -> value -> 'a1) -> (id -> typ -> value ->
    list_const -> 'a1) -> (id -> typ -> value -> typ -> value -> list_const
    -> 'a1) -> (id -> typ -> sz -> align -> 'a1) -> (id -> typ -> value ->
    'a1) -> (id -> typ -> sz -> align -> 'a1) -> (id -> typ -> value -> align
    -> 'a1) -> (id -> typ -> value -> value -> align -> 'a1) -> (id ->
    inbounds -> typ -> value -> list_value -> 'a1) -> (id -> extop -> typ ->
    value -> typ -> 'a1) -> (id -> castop -> typ -> value -> typ -> 'a1) ->
    (id -> cond -> typ -> value -> value -> 'a1) -> (id -> value -> typ ->
    value -> value -> 'a1) -> (id -> noret -> tailc -> typ -> id -> params ->
    'a1) -> cmd -> 'a1
  
  type phinode =
    | Coq_insn_phi of id * typ * list_value_l
  
  val phinode_rect : (id -> typ -> list_value_l -> 'a1) -> phinode -> 'a1
  
  val phinode_rec : (id -> typ -> list_value_l -> 'a1) -> phinode -> 'a1
  
  type arg = typ*id
  
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
  
  type args = (typ*id) list
  
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
  
  type module_info = coq_module*(usedef_id*usedef_block)
  
  type fdef_info = fdef*dt
  
  type intrinsic_funs = ids
  
  val map_list_value_l : (value -> l -> 'a1) -> list_value_l -> 'a1 list
  
  val make_list_value_l : (value*l) list -> list_value_l
  
  val unmake_list_value_l : list_value_l -> (value*l) list
  
  val nth_list_value_l : nat -> list_value_l -> (value*l) option
  
  val app_list_value_l : list_value_l -> list_value_l -> list_value_l
  
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
    (const -> 'a1 -> list_const -> 'a2 -> 'a2) -> (const -> 'a1)*(list_const
    -> 'a2)
  
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
    -> 'a1) -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> (typ ->
    'a1)*(list_typ -> 'a2)
 end

module LLVMlib : 
 sig 
  val id_dec : LLVMsyntax.id -> LLVMsyntax.id -> bool
  
  val l_dec : LLVMsyntax.l -> LLVMsyntax.l -> bool
  
  val coq_INT_dec : LLVMsyntax.coq_INT -> LLVMsyntax.coq_INT -> bool
  
  val sz_dec : LLVMsyntax.sz -> LLVMsyntax.sz -> bool
  
  val align_dec : LLVMsyntax.align -> LLVMsyntax.align -> bool
  
  val inbounds_dec : LLVMsyntax.inbounds -> LLVMsyntax.inbounds -> bool
  
  val tailc_dec : LLVMsyntax.tailc -> LLVMsyntax.tailc -> bool
  
  val noret_dec : LLVMsyntax.noret -> LLVMsyntax.noret -> bool
  
  val szZERO : LLVMsyntax.sz
  
  val szONE : LLVMsyntax.sz
  
  val nat2sz : nat -> LLVMsyntax.sz
  
  val sz2nat : LLVMsyntax.sz -> nat
  
  val coq_INT2nat : LLVMsyntax.coq_INT -> nat
  
  val nat2INT : nat -> LLVMsyntax.coq_INT
  
  val lempty_set : LLVMsyntax.l set
  
  val lset_add : LLVMsyntax.l -> LLVMsyntax.ls -> LLVMsyntax.l set
  
  val lset_union : LLVMsyntax.ls -> LLVMsyntax.ls -> LLVMsyntax.l set
  
  val lset_inter : LLVMsyntax.ls -> LLVMsyntax.ls -> LLVMsyntax.l set
  
  val lset_eq : LLVMsyntax.ls -> LLVMsyntax.ls -> bool
  
  val lset_neq : LLVMsyntax.ls -> LLVMsyntax.ls -> bool
  
  val lset_single : LLVMsyntax.l -> LLVMsyntax.l set
  
  val lset_mem : LLVMsyntax.l -> LLVMsyntax.ls -> bool
  
  val getCmdID : LLVMsyntax.cmd -> LLVMsyntax.id
  
  val getTerminatorID : LLVMsyntax.terminator -> LLVMsyntax.id
  
  val getPhiNodeID : LLVMsyntax.phinode -> LLVMsyntax.id
  
  val getValueID : LLVMsyntax.value -> LLVMsyntax.id option
  
  val getInsnID : LLVMsyntax.insn -> LLVMsyntax.id
  
  val isPhiNodeB : LLVMsyntax.insn -> bool
  
  val getSubTypFromConstIdxs :
    LLVMsyntax.list_const -> LLVMsyntax.typ -> LLVMsyntax.typ option
  
  val getSubTypFromValueIdxs :
    LLVMsyntax.list_value -> LLVMsyntax.typ -> LLVMsyntax.typ option
  
  val getGEPTyp :
    LLVMsyntax.list_value -> LLVMsyntax.typ -> LLVMsyntax.typ option
  
  val getLoadTyp : LLVMsyntax.typ -> LLVMsyntax.typ option
  
  val getCmdTyp : LLVMsyntax.cmd -> LLVMsyntax.typ option
  
  val getTerminatorTyp : LLVMsyntax.terminator -> LLVMsyntax.typ
  
  val getPhiNodeTyp : LLVMsyntax.phinode -> LLVMsyntax.typ
  
  val getInsnTyp : LLVMsyntax.insn -> LLVMsyntax.typ option
  
  val getPointerEltTyp : LLVMsyntax.typ -> LLVMsyntax.typ option
  
  val getValueIDs : LLVMsyntax.value -> LLVMsyntax.ids
  
  val getParamsOperand : LLVMsyntax.params -> LLVMsyntax.ids
  
  val list_prj1 : ('a1*'a2) list -> 'a1 list
  
  val list_prj2 : ('a1*'a2) list -> 'a2 list
  
  val getCmdOperands : LLVMsyntax.cmd -> LLVMsyntax.ids
  
  val getTerminatorOperands : LLVMsyntax.terminator -> LLVMsyntax.ids
  
  val values2ids : LLVMsyntax.value list -> LLVMsyntax.ids
  
  val getPhiNodeOperands : LLVMsyntax.phinode -> LLVMsyntax.ids
  
  val getInsnOperands : LLVMsyntax.insn -> LLVMsyntax.ids
  
  val getCmdLabels : LLVMsyntax.cmd -> LLVMsyntax.ls
  
  val getTerminatorLabels : LLVMsyntax.terminator -> LLVMsyntax.ls
  
  val getPhiNodeLabels : LLVMsyntax.phinode -> LLVMsyntax.ls
  
  val getInsnLabels : LLVMsyntax.insn -> LLVMsyntax.ls
  
  val args2Typs : LLVMsyntax.args -> LLVMsyntax.list_typ
  
  val getFheaderTyp : LLVMsyntax.fheader -> LLVMsyntax.typ
  
  val getFdecTyp : LLVMsyntax.fdec -> LLVMsyntax.typ
  
  val getFdefTyp : LLVMsyntax.fdef -> LLVMsyntax.typ
  
  val getBindingTyp : LLVMsyntax.id_binding -> LLVMsyntax.typ option
  
  val getCmdsFromBlock : LLVMsyntax.block -> LLVMsyntax.cmds
  
  val getPhiNodesFromBlock : LLVMsyntax.block -> LLVMsyntax.phinodes
  
  val getTerminatorFromBlock : LLVMsyntax.block -> LLVMsyntax.terminator
  
  val getBindingFdec : LLVMsyntax.id_binding -> LLVMsyntax.fdec option
  
  val getBindingArg : LLVMsyntax.id_binding -> LLVMsyntax.arg option
  
  val getBindingGvar : LLVMsyntax.id_binding -> LLVMsyntax.gvar option
  
  val getBindingCmd : LLVMsyntax.id_binding -> LLVMsyntax.cmd option
  
  val getBindingInsn : LLVMsyntax.id_binding -> LLVMsyntax.insn option
  
  val getBindingPhiNode : LLVMsyntax.id_binding -> LLVMsyntax.phinode option
  
  val getBindingTerminator :
    LLVMsyntax.id_binding -> LLVMsyntax.terminator option
  
  val getFheaderID : LLVMsyntax.fheader -> LLVMsyntax.id
  
  val getFdecID : LLVMsyntax.fdec -> LLVMsyntax.id
  
  val getFdefID : LLVMsyntax.fdef -> LLVMsyntax.id
  
  val getLabelViaIDFromList :
    LLVMsyntax.list_value_l -> LLVMsyntax.id -> LLVMsyntax.l option
  
  val getLabelViaIDFromPhiNode :
    LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.l option
  
  val getLabelsFromIdls : LLVMsyntax.list_value_l -> LLVMsyntax.ls
  
  val getLabelsFromPhiNode : LLVMsyntax.phinode -> LLVMsyntax.ls
  
  val getLabelsFromPhiNodes : LLVMsyntax.phinode list -> LLVMsyntax.ls
  
  val getIDLabelsFromPhiNode : LLVMsyntax.phinode -> LLVMsyntax.list_value_l
  
  val getLabelViaIDFromIDLabels :
    LLVMsyntax.list_value_l -> LLVMsyntax.id -> LLVMsyntax.l option
  
  val _getLabelViaIDPhiNode :
    LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.l option
  
  val getLabelViaIDPhiNode :
    LLVMsyntax.insn -> LLVMsyntax.id -> LLVMsyntax.l option
  
  val getReturnTyp : LLVMsyntax.fdef -> LLVMsyntax.typ
  
  val getGvarID : LLVMsyntax.gvar -> LLVMsyntax.id
  
  val getCallName : LLVMsyntax.insn -> LLVMsyntax.id option
  
  val getCallerReturnID : LLVMsyntax.cmd -> LLVMsyntax.id option
  
  val getIdViaLabelFromIdls :
    LLVMsyntax.list_value_l -> LLVMsyntax.l -> LLVMsyntax.id option
  
  val getIdViaBlockFromIdls :
    LLVMsyntax.list_value_l -> LLVMsyntax.block -> LLVMsyntax.id option
  
  val getIdViaBlockFromPHINode :
    LLVMsyntax.phinode -> LLVMsyntax.block -> LLVMsyntax.id option
  
  val getPHINodesFromBlock : LLVMsyntax.block -> LLVMsyntax.phinode list
  
  val lookupBindingViaIDFromCmd :
    LLVMsyntax.cmd -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromCmds :
    LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromPhiNode :
    LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromPhiNodes :
    LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromTerminator :
    LLVMsyntax.terminator -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromBlock :
    LLVMsyntax.block -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromBlocks :
    LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromArg :
    LLVMsyntax.arg -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromArgs :
    LLVMsyntax.args -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromFdec :
    LLVMsyntax.fdec -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromFdef :
    LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromProduct :
    LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromProducts :
    LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromModule :
    LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromModules :
    LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val lookupBindingViaIDFromSystem :
    LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.id_binding
  
  val isIDInBlockB : LLVMsyntax.id -> LLVMsyntax.block -> bool
  
  val lookupBlockViaIDFromBlocks :
    LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.block option
  
  val lookupBlockViaIDFromFdef :
    LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.block option
  
  val lookupFdecViaIDFromProduct :
    LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.fdec option
  
  val lookupFdecViaIDFromProducts :
    LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.fdec option
  
  val lookupFdecViaIDFromModule :
    LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.fdec option
  
  val lookupFdecViaIDFromModules :
    LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.fdec option
  
  val lookupFdecViaIDFromSystem :
    LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.fdec option
  
  val lookupFdefViaIDFromProduct :
    LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.fdef option
  
  val lookupFdefViaIDFromProducts :
    LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.fdef option
  
  val lookupFdefViaIDFromModule :
    LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.fdef option
  
  val lookupFdefViaIDFromModules :
    LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.fdef option
  
  val lookupFdefViaIDFromSystem :
    LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.fdef option
  
  val lookupTypViaIDFromCmd :
    LLVMsyntax.cmd -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromCmds :
    LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromPhiNode :
    LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromPhiNodes :
    LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromTerminator :
    LLVMsyntax.terminator -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromBlock :
    LLVMsyntax.block -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromBlocks :
    LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromFdef :
    LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromProduct :
    LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromProducts :
    LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromModule :
    LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromModules :
    LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromSystem :
    LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  type l2block = (LLVMsyntax.l*LLVMsyntax.block) list
  
  val genLabel2Block_block : LLVMsyntax.block -> l2block
  
  val genLabel2Block_blocks : LLVMsyntax.blocks -> l2block
  
  val genLabel2Block_fdef : LLVMsyntax.fdef -> l2block
  
  val genLabel2Block_product : LLVMsyntax.product -> l2block
  
  val genLabel2Block_products : LLVMsyntax.products -> l2block
  
  val genLabel2Block : LLVMsyntax.coq_module -> l2block
  
  val getEntryOfFdef : LLVMsyntax.fdef -> LLVMsyntax.block option
  
  val getNonEntryOfFdef : LLVMsyntax.fdef -> LLVMsyntax.blocks
  
  val lookupBlockViaLabelFromFdef :
    LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.block option
  
  val lookupBlockViaLabelFromModule :
    LLVMsyntax.coq_module -> LLVMsyntax.l -> LLVMsyntax.block option
  
  val lookupBlockViaLabelFromSystem :
    LLVMsyntax.system -> LLVMsyntax.l -> LLVMsyntax.block option
  
  val getLabelsFromBlocks : LLVMsyntax.blocks -> LLVMsyntax.ls
  
  val mergeInsnUseDef :
    LLVMsyntax.usedef_id -> LLVMsyntax.usedef_id -> LLVMsyntax.usedef_id
  
  val mergeBlockUseDef :
    LLVMsyntax.usedef_block -> LLVMsyntax.usedef_block ->
    LLVMsyntax.usedef_block
  
  val genIdUseDef_id_uses_value :
    LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.usedef_id
  
  val genIdUseDef_id_uses_id :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.usedef_id
  
  val genIdUseDef_id_uses_params :
    LLVMsyntax.params -> LLVMsyntax.id -> LLVMsyntax.usedef_id
  
  val genIdUseDef_cmd_uses_value :
    LLVMsyntax.value -> LLVMsyntax.cmd -> LLVMsyntax.usedef_id
  
  val genIdUseDef_terminator_uses_value :
    LLVMsyntax.value -> LLVMsyntax.terminator -> LLVMsyntax.usedef_id
  
  val genIdUseDef_phinode_uses_value :
    LLVMsyntax.value -> LLVMsyntax.phinode -> LLVMsyntax.usedef_id
  
  val genIdUseDef_cmd_uses_id :
    LLVMsyntax.id -> LLVMsyntax.cmd -> LLVMsyntax.usedef_id
  
  val genIdUseDef_terminator_uses_id :
    LLVMsyntax.id -> LLVMsyntax.terminator -> LLVMsyntax.usedef_id
  
  val genIdUseDef_phinode_uses_id :
    LLVMsyntax.id -> LLVMsyntax.phinode -> LLVMsyntax.usedef_id
  
  val genIdUseDef_cmd_uses_params :
    LLVMsyntax.params -> LLVMsyntax.cmd -> LLVMsyntax.usedef_id
  
  val genIdUseDef_terminator_uses_params :
    LLVMsyntax.params -> LLVMsyntax.terminator -> LLVMsyntax.usedef_id
  
  val genIdUseDef_phinode_uses_params :
    LLVMsyntax.params -> LLVMsyntax.phinode -> LLVMsyntax.usedef_id
  
  val genIdUseDef_cmd : LLVMsyntax.cmd -> LLVMsyntax.usedef_id
  
  val genIdUseDef_terminator : LLVMsyntax.terminator -> LLVMsyntax.usedef_id
  
  val genIdUseDef_id_uses_idls :
    LLVMsyntax.list_value_l -> LLVMsyntax.id -> LLVMsyntax.usedef_id
  
  val genIdUseDef_phinode : LLVMsyntax.phinode -> LLVMsyntax.usedef_id
  
  val genIdUseDef_cmds : LLVMsyntax.cmds -> LLVMsyntax.usedef_id
  
  val genIdUseDef_phinodes : LLVMsyntax.phinodes -> LLVMsyntax.usedef_id
  
  val genIdUseDef_block : LLVMsyntax.block -> LLVMsyntax.usedef_id
  
  val genIdUseDef_blocks : LLVMsyntax.blocks -> LLVMsyntax.usedef_id
  
  val genIdUseDef_fdef : LLVMsyntax.fdef -> LLVMsyntax.usedef_id
  
  val genIdUseDef_product : LLVMsyntax.product -> LLVMsyntax.usedef_id
  
  val genIdUseDef_products : LLVMsyntax.products -> LLVMsyntax.usedef_id
  
  val genIdUseDef : LLVMsyntax.coq_module -> LLVMsyntax.usedef_id
  
  val getIdUseDef :
    LLVMsyntax.usedef_id -> LLVMsyntax.id -> LLVMsyntax.id list
  
  val getBlockLabel : LLVMsyntax.block -> LLVMsyntax.l
  
  val genBlockUseDef_label :
    LLVMsyntax.l -> LLVMsyntax.block -> LLVMsyntax.usedef_block
  
  val genBlockUseDef_phi_cases :
    LLVMsyntax.list_value_l -> LLVMsyntax.block -> LLVMsyntax.usedef_block
  
  val genBlockUseDef_cmd :
    LLVMsyntax.cmd -> LLVMsyntax.block -> LLVMsyntax.usedef_block
  
  val genBlockUseDef_terminator :
    LLVMsyntax.terminator -> LLVMsyntax.block -> LLVMsyntax.usedef_block
  
  val genBlockUseDef_phinode :
    LLVMsyntax.phinode -> LLVMsyntax.block -> LLVMsyntax.usedef_block
  
  val genBlockUseDef_cmds :
    LLVMsyntax.cmds -> LLVMsyntax.block -> LLVMsyntax.usedef_block
  
  val genBlockUseDef_phinodes :
    LLVMsyntax.phinodes -> LLVMsyntax.block -> LLVMsyntax.usedef_block
  
  val genBlockUseDef_block : LLVMsyntax.block -> LLVMsyntax.usedef_block
  
  val genBlockUseDef_blocks : LLVMsyntax.blocks -> LLVMsyntax.usedef_block
  
  val genBlockUseDef_fdef : LLVMsyntax.fdef -> LLVMsyntax.usedef_block
  
  val genBlockUseDef_product : LLVMsyntax.product -> LLVMsyntax.usedef_block
  
  val genBlockUseDef_products :
    LLVMsyntax.products -> LLVMsyntax.usedef_block
  
  val genBlockUseDef : LLVMsyntax.coq_module -> LLVMsyntax.usedef_block
  
  val getBlockUseDef :
    LLVMsyntax.usedef_block -> LLVMsyntax.block -> LLVMsyntax.block list
  
  val getTerminator : LLVMsyntax.block -> LLVMsyntax.terminator
  
  val getLabelsFromSwitchCases :
    (LLVMsyntax.const*LLVMsyntax.l) list -> LLVMsyntax.ls
  
  val getLabelsFromTerminator : LLVMsyntax.terminator -> LLVMsyntax.ls
  
  val getBlocksFromLabels : LLVMsyntax.ls -> l2block -> LLVMsyntax.blocks
  
  val succOfBlock :
    LLVMsyntax.block -> LLVMsyntax.coq_module -> LLVMsyntax.blocks
  
  val predOfBlock :
    LLVMsyntax.block -> LLVMsyntax.usedef_block -> LLVMsyntax.blocks
  
  val hasSinglePredecessor :
    LLVMsyntax.block -> LLVMsyntax.usedef_block -> bool
  
  val genLabelsFromBlocks : LLVMsyntax.blocks -> LLVMsyntax.ls
  
  val genLabelsFromFdef : LLVMsyntax.fdef -> LLVMsyntax.ls
  
  val inputFromPred : LLVMsyntax.blocks -> LLVMsyntax.dt -> LLVMsyntax.ls
  
  val outputFromInput : LLVMsyntax.block -> LLVMsyntax.ls -> LLVMsyntax.ls
  
  val update_dt :
    LLVMsyntax.dt -> LLVMsyntax.l -> LLVMsyntax.ls -> LLVMsyntax.dt
  
  val inter_dt : LLVMsyntax.dt -> LLVMsyntax.dt -> LLVMsyntax.dt
  
  val genDominatorTree_blocks_innerloop :
    LLVMsyntax.blocks -> LLVMsyntax.usedef_block -> LLVMsyntax.dt ->
    LLVMsyntax.dt
  
  val eq_dt : LLVMsyntax.dt -> LLVMsyntax.dt -> LLVMsyntax.blocks -> bool
  
  val sizeOfDT : LLVMsyntax.blocks -> LLVMsyntax.dt -> nat
  
  val size : (LLVMsyntax.blocks*LLVMsyntax.dt) -> nat
  
  val genDominatorTree_blocks_F :
    ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.dt) -> (LLVMsyntax.blocks*LLVMsyntax.dt) ->
    LLVMsyntax.usedef_block -> LLVMsyntax.dt
  
  val genDominatorTree_blocks_terminate :
    (LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.dt
  
  val genDominatorTree_blocks :
    (LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.dt
  
  type coq_R_genDominatorTree_blocks =
    | R_genDominatorTree_blocks_0 of (LLVMsyntax.blocks*LLVMsyntax.dt)
       * LLVMsyntax.usedef_block * LLVMsyntax.blocks * 
       LLVMsyntax.dt * LLVMsyntax.dt
    | R_genDominatorTree_blocks_1 of (LLVMsyntax.blocks*LLVMsyntax.dt)
       * LLVMsyntax.usedef_block * LLVMsyntax.blocks * 
       LLVMsyntax.dt * LLVMsyntax.dt * LLVMsyntax.dt
       * coq_R_genDominatorTree_blocks
  
  val coq_R_genDominatorTree_blocks_rect :
    ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __ ->
    'a1) -> ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __ ->
    LLVMsyntax.dt -> coq_R_genDominatorTree_blocks -> 'a1 -> 'a1) ->
    (LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.dt -> coq_R_genDominatorTree_blocks -> 'a1
  
  val coq_R_genDominatorTree_blocks_rec :
    ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __ ->
    'a1) -> ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __ ->
    LLVMsyntax.dt -> coq_R_genDominatorTree_blocks -> 'a1 -> 'a1) ->
    (LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.dt -> coq_R_genDominatorTree_blocks -> 'a1
  
  val genDominatorTree_blocks_rect :
    ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __ ->
    'a1) -> ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __ ->
    'a1 -> 'a1) -> (LLVMsyntax.blocks*LLVMsyntax.dt) ->
    LLVMsyntax.usedef_block -> 'a1
  
  val genDominatorTree_blocks_rec :
    ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __ ->
    'a1) -> ((LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.blocks -> LLVMsyntax.dt -> __ -> LLVMsyntax.dt -> __ -> __ ->
    'a1 -> 'a1) -> (LLVMsyntax.blocks*LLVMsyntax.dt) ->
    LLVMsyntax.usedef_block -> 'a1
  
  val coq_R_genDominatorTree_blocks_correct :
    (LLVMsyntax.blocks*LLVMsyntax.dt) -> LLVMsyntax.usedef_block ->
    LLVMsyntax.dt -> coq_R_genDominatorTree_blocks
  
  val initialize_genDominatorTree_blocks :
    LLVMsyntax.blocks -> LLVMsyntax.ls -> LLVMsyntax.dt -> LLVMsyntax.dt
  
  val genEmptyDT : LLVMsyntax.dt
  
  val initialize_genDominatorTree_entry : LLVMsyntax.fdef -> LLVMsyntax.dt
  
  val initialize_genDominatorTree :
    LLVMsyntax.fdef -> LLVMsyntax.ls -> LLVMsyntax.dt
  
  val genDominatorTree :
    LLVMsyntax.fdef -> LLVMsyntax.coq_module -> LLVMsyntax.dt
  
  val blockDominatesB :
    LLVMsyntax.dt -> LLVMsyntax.block -> LLVMsyntax.block -> bool
  
  val isReachableFromEntryB :
    LLVMsyntax.fdef_info -> LLVMsyntax.block -> bool
  
  val isPointerTypB : LLVMsyntax.typ -> bool
  
  val isArrayTypB : LLVMsyntax.typ -> bool
  
  val isReturnInsnB : LLVMsyntax.terminator -> bool
  
  val _isCallInsnB : LLVMsyntax.cmd -> bool
  
  val isCallInsnB : LLVMsyntax.insn -> bool
  
  val isNotValidReturnTypB : LLVMsyntax.typ -> bool
  
  val isValidReturnTypB : LLVMsyntax.typ -> bool
  
  val isNotFirstClassTypB : LLVMsyntax.typ -> bool
  
  val isFirstClassTypB : LLVMsyntax.typ -> bool
  
  val isValidArgumentTypB : LLVMsyntax.typ -> bool
  
  val isNotValidElementTypB : LLVMsyntax.typ -> bool
  
  val isValidElementTypB : LLVMsyntax.typ -> bool
  
  val isBindingFdecB : LLVMsyntax.id_binding -> bool
  
  val isBindingGvarB : LLVMsyntax.id_binding -> bool
  
  val isBindingArgB : LLVMsyntax.id_binding -> bool
  
  val isBindingCmdB : LLVMsyntax.id_binding -> bool
  
  val isBindingTerminatorB : LLVMsyntax.id_binding -> bool
  
  val isBindingPhiNodeB : LLVMsyntax.id_binding -> bool
  
  val isBindingInsnB : LLVMsyntax.id_binding -> bool
  
  val isBindingFdec : LLVMsyntax.id_binding -> LLVMsyntax.fdec option
  
  val isBindingArg : LLVMsyntax.id_binding -> LLVMsyntax.arg option
  
  val isBindingGvar : LLVMsyntax.id_binding -> LLVMsyntax.gvar option
  
  val isBindingCmd : LLVMsyntax.id_binding -> LLVMsyntax.cmd option
  
  val isBindingPhiNode : LLVMsyntax.id_binding -> LLVMsyntax.phinode option
  
  val isBindingTerminator :
    LLVMsyntax.id_binding -> LLVMsyntax.terminator option
  
  val isBindingInsn : LLVMsyntax.id_binding -> LLVMsyntax.insn option
  
  val getCmdsIDs : LLVMsyntax.cmd list -> LLVMsyntax.ids
  
  val getPhiNodesIDs : LLVMsyntax.phinode list -> LLVMsyntax.ids
  
  val getBlockIDs : LLVMsyntax.block -> LLVMsyntax.ids
  
  val getBlocksIDs : LLVMsyntax.block list -> LLVMsyntax.ids
  
  val getBlocksLabels : LLVMsyntax.block list -> LLVMsyntax.ls
  
  val getProductID : LLVMsyntax.product -> LLVMsyntax.id
  
  val getProductsIDs : LLVMsyntax.product list -> LLVMsyntax.ids
  
  val sumbool2bool : bool -> bool
  
  type typ_dec_prop = LLVMsyntax.typ -> bool
  
  type list_typ_dec_prop = LLVMsyntax.list_typ -> bool
  
  val typ_mutrec_dec :
    (LLVMsyntax.typ -> typ_dec_prop)*(LLVMsyntax.list_typ ->
    list_typ_dec_prop)
  
  val typ_dec : LLVMsyntax.typ -> LLVMsyntax.typ -> bool
  
  val list_typ_dec : LLVMsyntax.list_typ -> LLVMsyntax.list_typ -> bool
  
  type const_dec_prop = LLVMsyntax.const -> bool
  
  type list_const_dec_prop = LLVMsyntax.list_const -> bool
  
  val const_mutrec_dec :
    (LLVMsyntax.const -> const_dec_prop)*(LLVMsyntax.list_const ->
    list_const_dec_prop)
  
  val const_dec : LLVMsyntax.const -> LLVMsyntax.const -> bool
  
  val list_const_dec : LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool
  
  val value_dec : LLVMsyntax.value -> LLVMsyntax.value -> bool
  
  val params_dec : LLVMsyntax.params -> LLVMsyntax.params -> bool
  
  val list_value_l_dec :
    LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l -> bool
  
  val list_value_dec : LLVMsyntax.list_value -> LLVMsyntax.list_value -> bool
  
  val bop_dec : LLVMsyntax.bop -> LLVMsyntax.bop -> bool
  
  val extop_dec : LLVMsyntax.extop -> LLVMsyntax.extop -> bool
  
  val castop_dec : LLVMsyntax.castop -> LLVMsyntax.castop -> bool
  
  val cond_dec : LLVMsyntax.cond -> LLVMsyntax.cond -> bool
  
  val cmd_dec : LLVMsyntax.cmd -> LLVMsyntax.cmd -> bool
  
  val terminator_dec : LLVMsyntax.terminator -> LLVMsyntax.terminator -> bool
  
  val phinode_dec : LLVMsyntax.phinode -> LLVMsyntax.phinode -> bool
  
  val insn_dec : LLVMsyntax.insn -> LLVMsyntax.insn -> bool
  
  val cmds_dec : LLVMsyntax.cmd list -> LLVMsyntax.cmd list -> bool
  
  val phinodes_dec :
    LLVMsyntax.phinode list -> LLVMsyntax.phinode list -> bool
  
  val block_dec : LLVMsyntax.block -> LLVMsyntax.block -> bool
  
  val arg_dec : LLVMsyntax.arg -> LLVMsyntax.arg -> bool
  
  val args_dec : LLVMsyntax.args -> LLVMsyntax.args -> bool
  
  val fheader_dec : LLVMsyntax.fheader -> LLVMsyntax.fheader -> bool
  
  val blocks_dec : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool
  
  val fdec_dec : LLVMsyntax.fdec -> LLVMsyntax.fdec -> bool
  
  val fdef_dec : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool
  
  val gvar_dec : LLVMsyntax.gvar -> LLVMsyntax.gvar -> bool
  
  val product_dec : LLVMsyntax.product -> LLVMsyntax.product -> bool
  
  val products_dec : LLVMsyntax.products -> LLVMsyntax.products -> bool
  
  val layout_dec : LLVMsyntax.layout -> LLVMsyntax.layout -> bool
  
  val layouts_dec : LLVMsyntax.layouts -> LLVMsyntax.layouts -> bool
  
  val module_dec : LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool
  
  val modules_dec : LLVMsyntax.modules -> LLVMsyntax.modules -> bool
  
  val system_dec : LLVMsyntax.system -> LLVMsyntax.system -> bool
  
  val typEqB : LLVMsyntax.typ -> LLVMsyntax.typ -> bool
  
  val list_typEqB : LLVMsyntax.list_typ -> LLVMsyntax.list_typ -> bool
  
  val idEqB : LLVMsyntax.id -> LLVMsyntax.id -> bool
  
  val constEqB : LLVMsyntax.const -> LLVMsyntax.const -> bool
  
  val list_constEqB : LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool
  
  val valueEqB : LLVMsyntax.value -> LLVMsyntax.value -> bool
  
  val paramsEqB : LLVMsyntax.params -> LLVMsyntax.params -> bool
  
  val lEqB : LLVMsyntax.l -> LLVMsyntax.l -> bool
  
  val list_value_lEqB :
    LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l -> bool
  
  val list_valueEqB : LLVMsyntax.list_value -> LLVMsyntax.list_value -> bool
  
  val bopEqB : LLVMsyntax.bop -> LLVMsyntax.bop -> bool
  
  val extopEqB : LLVMsyntax.extop -> LLVMsyntax.extop -> bool
  
  val condEqB : LLVMsyntax.cond -> LLVMsyntax.cond -> bool
  
  val castopEqB : LLVMsyntax.castop -> LLVMsyntax.castop -> bool
  
  val cmdEqB : LLVMsyntax.cmd -> LLVMsyntax.cmd -> bool
  
  val cmdsEqB : LLVMsyntax.cmd list -> LLVMsyntax.cmd list -> bool
  
  val terminatorEqB : LLVMsyntax.terminator -> LLVMsyntax.terminator -> bool
  
  val phinodeEqB : LLVMsyntax.phinode -> LLVMsyntax.phinode -> bool
  
  val phinodesEqB :
    LLVMsyntax.phinode list -> LLVMsyntax.phinode list -> bool
  
  val blockEqB : LLVMsyntax.block -> LLVMsyntax.block -> bool
  
  val blocksEqB : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool
  
  val argsEqB : LLVMsyntax.args -> LLVMsyntax.args -> bool
  
  val fheaderEqB : LLVMsyntax.fheader -> LLVMsyntax.fheader -> bool
  
  val fdecEqB : LLVMsyntax.fdec -> LLVMsyntax.fdec -> bool
  
  val fdefEqB : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool
  
  val gvarEqB : LLVMsyntax.gvar -> LLVMsyntax.gvar -> bool
  
  val productEqB : LLVMsyntax.product -> LLVMsyntax.product -> bool
  
  val productsEqB : LLVMsyntax.products -> LLVMsyntax.products -> bool
  
  val layoutEqB : LLVMsyntax.layout -> LLVMsyntax.layout -> bool
  
  val layoutsEqB : LLVMsyntax.layouts -> LLVMsyntax.layouts -> bool
  
  val moduleEqB : LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool
  
  val modulesEqB : LLVMsyntax.modules -> LLVMsyntax.modules -> bool
  
  val systemEqB : LLVMsyntax.system -> LLVMsyntax.system -> bool
  
  val coq_InCmdsB : LLVMsyntax.cmd -> LLVMsyntax.cmds -> bool
  
  val coq_InPhiNodesB : LLVMsyntax.phinode -> LLVMsyntax.phinodes -> bool
  
  val cmdInBlockB : LLVMsyntax.cmd -> LLVMsyntax.block -> bool
  
  val phinodeInBlockB : LLVMsyntax.phinode -> LLVMsyntax.block -> bool
  
  val terminatorInBlockB : LLVMsyntax.terminator -> LLVMsyntax.block -> bool
  
  val coq_InArgsB : LLVMsyntax.arg -> LLVMsyntax.args -> bool
  
  val argInFheaderB : LLVMsyntax.arg -> LLVMsyntax.fheader -> bool
  
  val argInFdecB : LLVMsyntax.arg -> LLVMsyntax.fdec -> bool
  
  val argInFdefB : LLVMsyntax.arg -> LLVMsyntax.fdef -> bool
  
  val coq_InBlocksB : LLVMsyntax.block -> LLVMsyntax.blocks -> bool
  
  val blockInFdefB : LLVMsyntax.block -> LLVMsyntax.fdef -> bool
  
  val coq_InProductsB : LLVMsyntax.product -> LLVMsyntax.products -> bool
  
  val productInModuleB : LLVMsyntax.product -> LLVMsyntax.coq_module -> bool
  
  val coq_InModulesB : LLVMsyntax.coq_module -> LLVMsyntax.modules -> bool
  
  val moduleInSystemB : LLVMsyntax.coq_module -> LLVMsyntax.system -> bool
  
  val productInSystemModuleB :
    LLVMsyntax.product -> LLVMsyntax.system -> LLVMsyntax.coq_module -> bool
  
  val productInSystemModuleIB :
    LLVMsyntax.product -> LLVMsyntax.system -> LLVMsyntax.module_info -> bool
  
  val blockInSystemModuleFdefB :
    LLVMsyntax.block -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
    LLVMsyntax.fdef -> bool
  
  val blockInSystemModuleIFdefIB :
    LLVMsyntax.block -> LLVMsyntax.system -> LLVMsyntax.module_info ->
    LLVMsyntax.fdef_info -> bool
  
  val cmdInSystemModuleFdefBlockB :
    LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
    LLVMsyntax.fdef -> LLVMsyntax.block -> bool
  
  val cmdInSystemModuleIFdefIBlockB :
    LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.module_info ->
    LLVMsyntax.fdef_info -> LLVMsyntax.block -> bool
  
  val phinodeInSystemModuleFdefBlockB :
    LLVMsyntax.phinode -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
    LLVMsyntax.fdef -> LLVMsyntax.block -> bool
  
  val phinodeInSystemModuleIFdefIBlockB :
    LLVMsyntax.phinode -> LLVMsyntax.system -> LLVMsyntax.module_info ->
    LLVMsyntax.fdef_info -> LLVMsyntax.block -> bool
  
  val terminatorInSystemModuleFdefBlockB :
    LLVMsyntax.terminator -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
    LLVMsyntax.fdef -> LLVMsyntax.block -> bool
  
  val terminatorInSystemModuleIFdefIBlockB :
    LLVMsyntax.terminator -> LLVMsyntax.system -> LLVMsyntax.module_info ->
    LLVMsyntax.fdef_info -> LLVMsyntax.block -> bool
  
  val insnInSystemModuleFdefBlockB :
    LLVMsyntax.insn -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
    LLVMsyntax.fdef -> LLVMsyntax.block -> bool
  
  val insnInSystemModuleIFdefIBlockB :
    LLVMsyntax.insn -> LLVMsyntax.system -> LLVMsyntax.module_info ->
    LLVMsyntax.fdef_info -> LLVMsyntax.block -> bool
  
  val cmdInBlockB_dec : LLVMsyntax.cmd -> LLVMsyntax.block -> bool
  
  val phinodeInBlockB_dec : LLVMsyntax.phinode -> LLVMsyntax.block -> bool
  
  val terminatorInBlockB_dec :
    LLVMsyntax.terminator -> LLVMsyntax.block -> bool
  
  val getParentOfCmdFromBlocks :
    LLVMsyntax.cmd -> LLVMsyntax.blocks -> LLVMsyntax.block option
  
  val getParentOfCmdFromFdef :
    LLVMsyntax.cmd -> LLVMsyntax.fdef -> LLVMsyntax.block option
  
  val getParentOfCmdFromProduct :
    LLVMsyntax.cmd -> LLVMsyntax.product -> LLVMsyntax.block option
  
  val getParentOfCmdFromProducts :
    LLVMsyntax.cmd -> LLVMsyntax.products -> LLVMsyntax.block option
  
  val getParentOfCmdFromModule :
    LLVMsyntax.cmd -> LLVMsyntax.coq_module -> LLVMsyntax.block option
  
  val getParentOfCmdFromModules :
    LLVMsyntax.cmd -> LLVMsyntax.modules -> LLVMsyntax.block option
  
  val getParentOfCmdFromSystem :
    LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.block option
  
  val cmdHasParent : LLVMsyntax.cmd -> LLVMsyntax.system -> bool
  
  val getParentOfPhiNodeFromBlocks :
    LLVMsyntax.phinode -> LLVMsyntax.blocks -> LLVMsyntax.block option
  
  val getParentOfPhiNodeFromFdef :
    LLVMsyntax.phinode -> LLVMsyntax.fdef -> LLVMsyntax.block option
  
  val getParentOfPhiNodeFromProduct :
    LLVMsyntax.phinode -> LLVMsyntax.product -> LLVMsyntax.block option
  
  val getParentOfPhiNodeFromProducts :
    LLVMsyntax.phinode -> LLVMsyntax.products -> LLVMsyntax.block option
  
  val getParentOfPhiNodeFromModule :
    LLVMsyntax.phinode -> LLVMsyntax.coq_module -> LLVMsyntax.block option
  
  val getParentOfPhiNodeFromModules :
    LLVMsyntax.phinode -> LLVMsyntax.modules -> LLVMsyntax.block option
  
  val getParentOfPhiNodeFromSystem :
    LLVMsyntax.phinode -> LLVMsyntax.system -> LLVMsyntax.block option
  
  val phinodeHasParent : LLVMsyntax.phinode -> LLVMsyntax.system -> bool
  
  val getParentOfTerminatorFromBlocks :
    LLVMsyntax.terminator -> LLVMsyntax.blocks -> LLVMsyntax.block option
  
  val getParentOfTerminatorFromFdef :
    LLVMsyntax.terminator -> LLVMsyntax.fdef -> LLVMsyntax.block option
  
  val getParentOfTerminatorFromProduct :
    LLVMsyntax.terminator -> LLVMsyntax.product -> LLVMsyntax.block option
  
  val getParentOfTerminatorFromProducts :
    LLVMsyntax.terminator -> LLVMsyntax.products -> LLVMsyntax.block option
  
  val getParentOfTerminatorFromModule :
    LLVMsyntax.terminator -> LLVMsyntax.coq_module -> LLVMsyntax.block option
  
  val getParentOfTerminatorFromModules :
    LLVMsyntax.terminator -> LLVMsyntax.modules -> LLVMsyntax.block option
  
  val getParentOfTerminatorFromSystem :
    LLVMsyntax.terminator -> LLVMsyntax.system -> LLVMsyntax.block option
  
  val terminatoreHasParent :
    LLVMsyntax.terminator -> LLVMsyntax.system -> bool
  
  val productInModuleB_dec :
    LLVMsyntax.product -> LLVMsyntax.coq_module -> bool
  
  val getParentOfFdefFromModules :
    LLVMsyntax.fdef -> LLVMsyntax.modules -> LLVMsyntax.coq_module option
  
  val getParentOfFdefFromSystem :
    LLVMsyntax.fdef -> LLVMsyntax.system -> LLVMsyntax.coq_module option
  
  val lookupIdsViaLabelFromIdls :
    LLVMsyntax.list_value_l -> LLVMsyntax.l -> LLVMsyntax.id list
  
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
  
  module Value : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
   end
  
  module User : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
   end
  
  module Constant : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ
    
    val getList_typ : LLVMsyntax.list_const -> LLVMsyntax.list_typ
   end
  
  module GlobalValue : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ
    
    val getList_typ : LLVMsyntax.list_const -> LLVMsyntax.list_typ
   end
  
  module Function : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ
    
    val getList_typ : LLVMsyntax.list_const -> LLVMsyntax.list_typ
    
    val getDefReturnType : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val getDefFunctionType : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val def_arg_size : LLVMsyntax.fdef -> nat
    
    val getDecReturnType : LLVMsyntax.fdec -> LLVMsyntax.typ
    
    val getDecFunctionType : LLVMsyntax.fdec -> LLVMsyntax.typ
    
    val dec_arg_size : LLVMsyntax.fdec -> nat
   end
  
  module Instruction : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
   end
  
  module ReturnInst : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val hasReturnType : LLVMsyntax.terminator -> bool
    
    val getReturnType : LLVMsyntax.terminator -> LLVMsyntax.typ option
   end
  
  module CallSite : 
   sig 
    val getCalledFunction :
      LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.fdef option
    
    val getFdefTyp : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val arg_size : LLVMsyntax.fdef -> nat
    
    val getArgument : LLVMsyntax.fdef -> nat -> LLVMsyntax.arg option
    
    val getArgumentType : LLVMsyntax.fdef -> nat -> LLVMsyntax.typ option
   end
  
  module CallInst : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
   end
  
  module BinaryOperator : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val getFirstOperandType :
      LLVMsyntax.system -> LLVMsyntax.cmd -> LLVMsyntax.typ option
    
    val getSecondOperandType :
      LLVMsyntax.system -> LLVMsyntax.cmd -> LLVMsyntax.typ option
    
    val getResultType : LLVMsyntax.cmd -> LLVMsyntax.typ option
   end
  
  module PHINode : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val getNumIncomingValues : LLVMsyntax.phinode -> nat
    
    val getIncomingValueType :
      LLVMsyntax.system -> LLVMsyntax.phinode -> nat -> LLVMsyntax.typ option
   end
  
  module Typ : 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val isSizedListTyp : LLVMsyntax.list_typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
   end
  
  module DerivedType : 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val isSizedListTyp : LLVMsyntax.list_typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
   end
  
  module FunctionType : 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val isSizedListTyp : LLVMsyntax.list_typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
    
    val getNumParams : LLVMsyntax.typ -> nat option
    
    val isVarArg : LLVMsyntax.typ -> bool
    
    val getParamType : LLVMsyntax.typ -> nat -> LLVMsyntax.typ option
   end
  
  module CompositeType : 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val isSizedListTyp : LLVMsyntax.list_typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
   end
  
  module SequentialType : 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val isSizedListTyp : LLVMsyntax.list_typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
    
    val hasElementType : LLVMsyntax.typ -> bool
    
    val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option
   end
  
  module ArrayType : 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val isSizedListTyp : LLVMsyntax.list_typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
    
    val hasElementType : LLVMsyntax.typ -> bool
    
    val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option
    
    val getNumElements : LLVMsyntax.typ -> nat
   end
  
  type reflect =
    | ReflectT
    | ReflectF
  
  val reflect_rect : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1
  
  val reflect_rec : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1
  
  val reflect_blockDominates :
    LLVMsyntax.dt -> LLVMsyntax.block -> LLVMsyntax.block -> reflect
  
  val ifP :
    LLVMsyntax.dt -> LLVMsyntax.block -> LLVMsyntax.block -> 'a1 option ->
    'a1 option -> 'a1 option
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

type gVMap = (LLVMsyntax.id*genericValue) list

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
  
  type coq_State = { coq_Frame : coq_ExecutionContext; coq_Mem : mem0 }
  
  val coq_State_rect :
    (coq_ExecutionContext -> mem0 -> 'a1) -> coq_State -> 'a1
  
  val coq_State_rec :
    (coq_ExecutionContext -> mem0 -> 'a1) -> coq_State -> 'a1
  
  val coq_Frame : coq_State -> coq_ExecutionContext
  
  val coq_Mem : coq_State -> mem0
  
  type nbranch =
    LLVMsyntax.cmd
    (* singleton inductive, whose constructor was mkNB *)
  
  val nbranch_rect : (LLVMsyntax.cmd -> __ -> 'a1) -> nbranch -> 'a1
  
  val nbranch_rec : (LLVMsyntax.cmd -> __ -> 'a1) -> nbranch -> 'a1
  
  val nbranching_cmd : nbranch -> LLVMsyntax.cmd
  
  val isCallInst_dec : LLVMsyntax.cmd -> bool
  
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
  
  val cmds2sbs : LLVMsyntax.cmds -> subblock list*nbranch list
  
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
  
  val sterm_rect :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) -> (smem
    -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) -> (smem
    -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ ->
    sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l
    -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a1) -> sterm -> 'a1
  
  val sterm_rec :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) -> (smem
    -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) -> (smem
    -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ ->
    sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l
    -> 'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a1) -> sterm -> 'a1
  
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
    LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
    sterm -> LLVMsyntax.align -> 'a1) -> smem -> 'a1
  
  val smem_rec :
    'a1 -> (smem -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
    'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> LLVMsyntax.sz ->
    LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
    LLVMsyntax.align -> 'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm ->
    sterm -> LLVMsyntax.align -> 'a1) -> smem -> 'a1
  
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
    'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ ->
    sterm -> 'a1 -> list_sterm -> 'a2 -> 'a1) -> (LLVMsyntax.extop ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
    (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ ->
    'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) -> (sterm
    -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> 'a2
    -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) -> 'a3 -> (sterm -> 'a1 ->
    LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) -> 'a4 -> (smem -> 'a4 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
    'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
    'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a4) -> 'a5 -> (smem -> 'a4 -> sframe -> 'a5 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a5) -> sframe ->
    'a5
  
  val smem_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ ->
    sterm -> 'a1 -> list_sterm -> 'a2 -> 'a1) -> (LLVMsyntax.extop ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
    (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ ->
    'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) -> (sterm
    -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> 'a2
    -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) -> 'a3 -> (sterm -> 'a1 ->
    LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) -> 'a4 -> (smem -> 'a4 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
    'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
    'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a4) -> 'a5 -> (smem -> 'a4 -> sframe -> 'a5 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a5) -> smem ->
    'a4
  
  val list_sterm_l_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ ->
    sterm -> 'a1 -> list_sterm -> 'a2 -> 'a1) -> (LLVMsyntax.extop ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
    (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ ->
    'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) -> (sterm
    -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> 'a2
    -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) -> 'a3 -> (sterm -> 'a1 ->
    LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) -> 'a4 -> (smem -> 'a4 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
    'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
    'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a4) -> 'a5 -> (smem -> 'a4 -> sframe -> 'a5 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a5) ->
    list_sterm_l -> 'a3
  
  val list_sterm_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ ->
    sterm -> 'a1 -> list_sterm -> 'a2 -> 'a1) -> (LLVMsyntax.extop ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
    (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ ->
    'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) -> (sterm
    -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> 'a2
    -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) -> 'a3 -> (sterm -> 'a1 ->
    LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) -> 'a4 -> (smem -> 'a4 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
    'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
    'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a4) -> 'a5 -> (smem -> 'a4 -> sframe -> 'a5 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a5) -> list_sterm
    -> 'a2
  
  val sterm_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ ->
    sterm -> 'a1 -> list_sterm -> 'a2 -> 'a1) -> (LLVMsyntax.extop ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
    (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ ->
    'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) -> (sterm
    -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> 'a2
    -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) -> 'a3 -> (sterm -> 'a1 ->
    LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) -> 'a4 -> (smem -> 'a4 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
    'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
    'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a4) -> 'a5 -> (smem -> 'a4 -> sframe -> 'a5 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a5) -> sterm ->
    'a1
  
  val se_mutrec :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) -> (smem
    -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a1) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ ->
    sterm -> 'a1 -> list_sterm -> 'a2 -> 'a1) -> (LLVMsyntax.extop ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
    (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ ->
    'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm ->
    'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) -> (sterm
    -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> 'a2
    -> (sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) -> 'a3 -> (sterm -> 'a1 ->
    LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) -> 'a4 -> (smem -> 'a4 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
    'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) -> (smem -> 'a4 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a4) -> (smem ->
    'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a4) -> 'a5 -> (smem -> 'a4 -> sframe -> 'a5 ->
    LLVMsyntax.typ -> LLVMsyntax.sz -> LLVMsyntax.align -> 'a5) -> ((((sterm
    -> 'a1)*(list_sterm -> 'a2))*(list_sterm_l -> 'a3))*(smem ->
    'a4))*(sframe -> 'a5)
  
  val map_list_sterm : (sterm -> 'a1) -> list_sterm -> 'a1 list
  
  val make_list_sterm : sterm list -> list_sterm
  
  val unmake_list_sterm : list_sterm -> sterm list
  
  val nth_list_sterm : nat -> list_sterm -> sterm option
  
  val app_list_sterm : list_sterm -> list_sterm -> list_sterm
  
  val map_list_sterm_l :
    (sterm -> LLVMsyntax.l -> 'a1) -> list_sterm_l -> 'a1 list
  
  val make_list_sterm_l : (sterm*LLVMsyntax.l) list -> list_sterm_l
  
  val unmake_list_sterm_l : list_sterm_l -> (sterm*LLVMsyntax.l) list
  
  val nth_list_sterm_l : nat -> list_sterm_l -> (sterm*LLVMsyntax.l) option
  
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
       * (LLVMsyntax.typ*sterm) list
  
  val scall_rect :
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.tailc -> LLVMsyntax.typ
    -> LLVMsyntax.id -> (LLVMsyntax.typ*sterm) list -> 'a1) -> scall -> 'a1
  
  val scall_rec :
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.tailc -> LLVMsyntax.typ
    -> LLVMsyntax.id -> (LLVMsyntax.typ*sterm) list -> 'a1) -> scall -> 'a1
  
  type smap = (AtomImpl.atom*sterm) list
  
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
    LLVMsyntax.params -> smap -> (LLVMsyntax.typ*sterm) list
  
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

type sterm_dec_prop = SimpleSE.sterm -> bool

type list_sterm_dec_prop = SimpleSE.list_sterm -> bool

type list_sterm_l_dec_prop = SimpleSE.list_sterm_l -> bool

type smem_dec_prop = SimpleSE.smem -> bool

type sframe_dec_prop = SimpleSE.sframe -> bool

val se_dec :
  ((((SimpleSE.sterm -> sterm_dec_prop)*(SimpleSE.list_sterm ->
  list_sterm_dec_prop))*(SimpleSE.list_sterm_l ->
  list_sterm_l_dec_prop))*(SimpleSE.smem -> smem_dec_prop))*(SimpleSE.sframe
  -> sframe_dec_prop)

val sterm_dec : SimpleSE.sterm -> SimpleSE.sterm -> bool

val smem_dec : SimpleSE.smem -> SimpleSE.smem -> bool

val sframe_dec : SimpleSE.sframe -> SimpleSE.sframe -> bool

val smap_dec : SimpleSE.smap -> SimpleSE.smap -> bool

val sterms_dec : SimpleSE.sterm list -> SimpleSE.sterm list -> bool

val sstate_dec : SimpleSE.sstate -> SimpleSE.sstate -> bool

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

