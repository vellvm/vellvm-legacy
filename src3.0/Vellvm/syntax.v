Require Import Arith.
Require Import Bool.
Require Import List.
Require Import ott_list_core.


Require Import ListSet.
Require Import Logic_Type.
Require Import monad.
Require Import Metatheory.
Require Import ZArith.
Require Import Coqlib.
Require Import Floats.
Require Import alist.
Require Import syntax_base.


Module LLVMsyntax.

Include LLVMsyntax_base.

Tactic Notation "cmd_cases" tactic(first) tactic(c) :=
  first;
  [ c "insn_bop" | c "insn_fbop" |
    c "insn_extractvalue" | c "insn_insertvalue" |
    c "insn_malloc" | c "insn_free" |
    c "insn_alloca" | c "insn_load" | c "insn_store" | c "insn_gep" |
    c "insn_trunc" | c "insn_ext" | c "insn_cast" |
    c "insn_icmp" | c "insn_fcmp" | c "insn_select" |
    c "insn_call" ].

Tactic Notation "product_cases" tactic(first) tactic(c) :=
  first;
  [ c "product_gvar" | c "product_fdec" | c "product_fdef" ].

Tactic Notation "typ_cases" tactic(first) tactic(c) :=
  first;
  [ c "typ_int" | c "typ_floatingpoint" |
    c "typ_void" | c "typ_label" |
    c "typ_metadata" | c "typ_array" |
    c "typ_function" | c "typ_struct" | c "typ_pointer" |
    c "typ_namedt" | c "typ_nil" | c "typ_cons" ].

Definition const_rec2 (P : const -> Set) (P0 : list const -> Set)
  (f : forall t : typ, P (const_zeroinitializer t))
  (f0 : forall (s : sz) (i : Int), P (const_int s i))
  (f1 : forall (f1 : floating_point) (f2 : Float), P (const_floatpoint f1 f2))
  (f2 : forall t : typ, P (const_undef t))
  (f3 : forall t : typ, P (const_null t))
  (f4 : forall (t : typ) (l : list const), P0 l -> P (const_arr t l))
  (f5 : forall (t : typ) (l : list const), P0 l -> P (const_struct t l))
  (f6 : forall (t : typ) (i : id), P (const_gid t i))
  (f7 : forall (t : truncop) (c : const),
        P c -> forall t0 : typ, P (const_truncop t c t0))
  (f8 : forall (e : extop) (c : const),
        P c -> forall t : typ, P (const_extop e c t))
  (f9 : forall (c : castop) (c0 : const),
        P c0 -> forall t : typ, P (const_castop c c0 t))
  (f10 : forall (i : inbounds) (c : const),
         P c -> forall l : list const, P0 l -> P (const_gep i c l))
  (f11 : forall c : const,
         P c ->
         forall c0 : const,
         P c0 -> forall c1 : const, P c1 -> P (const_select c c0 c1))
  (f12 : forall (c : cond) (c0 : const),
         P c0 -> forall c1 : const, P c1 -> P (const_icmp c c0 c1))
  (f13 : forall (f13 : fcond) (c : const),
         P c -> forall c0 : const, P c0 -> P (const_fcmp f13 c c0))
  (f14 : forall c : const,
         P c -> forall l : list const, P0 l -> P (const_extractvalue c l))
  (f15 : forall c : const,
         P c ->
         forall c0 : const,
         P c0 -> forall l : list const, P0 l -> P (const_insertvalue c c0 l))
  (f16 : forall (b : bop) (c : const),
         P c -> forall c0 : const, P c0 -> P (const_bop b c c0))
  (f17 : forall (f17 : fbop) (c : const),
         P c -> forall c0 : const, P c0 -> P (const_fbop f17 c c0))
  (f18 : P0 nil)
  (f19 : forall c : const,
         P c -> forall l : list const, P0 l -> P0 (c :: l)) :=
  fix F (c : const) : P c :=
  let F0 := fix F0 (l : list const) : P0 l :=
    match l return P0 l with
    | nil => f18
    | c :: l => f19 c (F c) l (F0 l)
    end in
  match c as c0 return (P c0) with
  | const_zeroinitializer t => f t
  | const_int s i => f0 s i
  | const_floatpoint f20 f21 => f1 f20 f21
  | const_undef t => f2 t
  | const_null t => f3 t
  | const_arr t l => f4 t l (F0 l)
  | const_struct t l => f5 t l (F0 l)
  | const_gid t i => f6 t i
  | const_truncop t c0 t0 => f7 t c0 (F c0) t0
  | const_extop e c0 t => f8 e c0 (F c0) t
  | const_castop c0 c1 t => f9 c0 c1 (F c1) t
  | const_gep i c0 l => f10 i c0 (F c0) l (F0 l)
  | const_select c0 c1 c2 => f11 c0 (F c0) c1 (F c1) c2 (F c2)
  | const_icmp c0 c1 c2 => f12 c0 c1 (F c1) c2 (F c2)
  | const_fcmp f20 c0 c1 => f13 f20 c0 (F c0) c1 (F c1)
  | const_extractvalue c0 l => f14 c0 (F c0) l (F0 l)
  | const_insertvalue c0 c1 l => f15 c0 (F c0) c1 (F c1) l (F0 l)
  | const_bop b c0 c1 => f16 b c0 (F c0) c1 (F c1)
  | const_fbop f20 c0 c1 => f17 f20 c0 (F c0) c1 (F c1)
  end.

Definition list_const_rec2 (P : const -> Set) (P0 : list const -> Set)
  (f : forall t : typ, P (const_zeroinitializer t))
  (f0 : forall (s : sz) (i : Int), P (const_int s i))
  (f1 : forall (f1 : floating_point) (f2 : Float), P (const_floatpoint f1 f2))
  (f2 : forall t : typ, P (const_undef t))
  (f3 : forall t : typ, P (const_null t))
  (f4 : forall (t : typ) (l : list const), P0 l -> P (const_arr t l))
  (f5 : forall (t : typ) (l : list const), P0 l -> P (const_struct t l))
  (f6 : forall (t : typ) (i : id), P (const_gid t i))
  (f7 : forall (t : truncop) (c : const),
        P c -> forall t0 : typ, P (const_truncop t c t0))
  (f8 : forall (e : extop) (c : const),
        P c -> forall t : typ, P (const_extop e c t))
  (f9 : forall (c : castop) (c0 : const),
        P c0 -> forall t : typ, P (const_castop c c0 t))
  (f10 : forall (i : inbounds) (c : const),
         P c -> forall l : list const, P0 l -> P (const_gep i c l))
  (f11 : forall c : const,
         P c ->
         forall c0 : const,
         P c0 -> forall c1 : const, P c1 -> P (const_select c c0 c1))
  (f12 : forall (c : cond) (c0 : const),
         P c0 -> forall c1 : const, P c1 -> P (const_icmp c c0 c1))
  (f13 : forall (f13 : fcond) (c : const),
         P c -> forall c0 : const, P c0 -> P (const_fcmp f13 c c0))
  (f14 : forall c : const,
         P c -> forall l : list const, P0 l -> P (const_extractvalue c l))
  (f15 : forall c : const,
         P c ->
         forall c0 : const,
         P c0 -> forall l : list const, P0 l -> P (const_insertvalue c c0 l))
  (f16 : forall (b : bop) (c : const),
         P c -> forall c0 : const, P c0 -> P (const_bop b c c0))
  (f17 : forall (f17 : fbop) (c : const),
         P c -> forall c0 : const, P c0 -> P (const_fbop f17 c c0))
  (f18 : P0 nil)
  (f19 : forall c : const,
         P c -> forall l : list const, P0 l -> P0 (c :: l)) :=
  let F := const_rec2 P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
    f11 f12 f13 f14 f15 f16 f17 f18 f19 in
  fix F0 (l : list const) : P0 l :=
    match l return P0 l with
    | nil => f18
    | c :: l => f19 c (F c) l (F0 l)
    end.

Definition const_mutrec P P' :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21=>
      (pair (@const_rec2 P P' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21)
            (@list_const_rec2 P P' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21)).

Definition typ_rec2 (P : typ -> Set) (P0 : list typ -> Set)
  (f : forall s : sz, P (typ_int s))
  (f0 : forall f0 : floating_point, P (typ_floatpoint f0))
  (f1 : P typ_void) (f2 : P typ_label) (f3 : P typ_metadata)
  (f4 : forall (s : sz) (t : typ), P t -> P (typ_array s t))
  (f5 : forall t : typ,
        P t ->
        forall l : list typ, P0 l -> forall v : varg, P (typ_function t l v))
  (f6 : forall l : list typ, P0 l -> P (typ_struct l))
  (f7 : forall t : typ, P t -> P (typ_pointer t))
  (f8 : forall i : id, P (typ_namedt i)) (f9 : P0 nil)
  (f10 : forall t : typ,
         P t -> forall l : list typ, P0 l -> P0 (t :: l)) :=
  fix F (t : typ) : P t :=
  let F0 :=
    fix F0 (l : list typ) : P0 l :=
    match l return P0 l with
      | nil => f9
      | t :: l0 => f10 t (F t) l0 (F0 l0)
    end in
  match t as t0 return (P t0) with
  | typ_int s => f s
  | typ_floatpoint f11 => f0 f11
  | typ_void => f1
  | typ_label => f2
  | typ_metadata => f3
  | typ_array s t0 => f4 s t0 (F t0)
  | typ_function t0 l v => f5 t0 (F t0) l (F0 l) v
  | typ_struct l => f6 l (F0 l)
  | typ_pointer t0 => f7 t0 (F t0)
  | typ_namedt i => f8 i
  end.

Definition list_typ_rec2 (P : typ -> Set) (P0 : list typ -> Set)
  (f : forall s : sz, P (typ_int s))
  (f0 : forall f0 : floating_point, P (typ_floatpoint f0))
  (f1 : P typ_void) (f2 : P typ_label) (f3 : P typ_metadata)
  (f4 : forall (s : sz) (t : typ), P t -> P (typ_array s t))
  (f5 : forall t : typ,
        P t ->
        forall l : list typ, P0 l -> forall v : varg, P (typ_function t l v))
  (f6 : forall l : list typ, P0 l -> P (typ_struct l))
  (f7 : forall t : typ, P t -> P (typ_pointer t))
  (f8 : forall i : id, P (typ_namedt i)) (f9 : P0 nil)
  (f10 : forall t : typ,
         P t -> forall l : list typ, P0 l -> P0 (t :: l)) :=
  let F := typ_rec2 P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 in
  fix F0 (l : list typ) : P0 l :=
  match l return P0 l with
    | nil => f9
    | t :: l0 => f10 t (F t) l0 (F0 l0)
  end.

Definition typ_mutrec P P' :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
      (pair (@typ_rec2 P P' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)
            (@list_typ_rec2 P P' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)).

Definition const_ind2 (P : const -> Prop) (P0 : list const -> Prop)
  (f : forall t : typ, P (const_zeroinitializer t))
  (f0 : forall (s : sz) (i : Int), P (const_int s i))
  (f1 : forall (f1 : floating_point) (f2 : Float), P (const_floatpoint f1 f2))
  (f2 : forall t : typ, P (const_undef t))
  (f3 : forall t : typ, P (const_null t))
  (f4 : forall (t : typ) (l : list const), P0 l -> P (const_arr t l))
  (f5 : forall (t : typ) (l : list const), P0 l -> P (const_struct t l))
  (f6 : forall (t : typ) (i : id), P (const_gid t i))
  (f7 : forall (t : truncop) (c : const),
        P c -> forall t0 : typ, P (const_truncop t c t0))
  (f8 : forall (e : extop) (c : const),
        P c -> forall t : typ, P (const_extop e c t))
  (f9 : forall (c : castop) (c0 : const),
        P c0 -> forall t : typ, P (const_castop c c0 t))
  (f10 : forall (i : inbounds) (c : const),
         P c -> forall l : list const, P0 l -> P (const_gep i c l))
  (f11 : forall c : const,
         P c ->
         forall c0 : const,
         P c0 -> forall c1 : const, P c1 -> P (const_select c c0 c1))
  (f12 : forall (c : cond) (c0 : const),
         P c0 -> forall c1 : const, P c1 -> P (const_icmp c c0 c1))
  (f13 : forall (f13 : fcond) (c : const),
         P c -> forall c0 : const, P c0 -> P (const_fcmp f13 c c0))
  (f14 : forall c : const,
         P c -> forall l : list const, P0 l -> P (const_extractvalue c l))
  (f15 : forall c : const,
         P c ->
         forall c0 : const,
         P c0 -> forall l : list const, P0 l -> P (const_insertvalue c c0 l))
  (f16 : forall (b : bop) (c : const),
         P c -> forall c0 : const, P c0 -> P (const_bop b c c0))
  (f17 : forall (f17 : fbop) (c : const),
         P c -> forall c0 : const, P c0 -> P (const_fbop f17 c c0))
  (f18 : P0 nil)
  (f19 : forall c : const,
         P c -> forall l : list const, P0 l -> P0 (c :: l)) :=
  fix F (c : const) : P c :=
  let F0 := fix F0 (l : list const) : P0 l :=
    match l return P0 l with
    | nil => f18
    | c :: l => f19 c (F c) l (F0 l)
    end in
  match c as c0 return (P c0) with
  | const_zeroinitializer t => f t
  | const_int s i => f0 s i
  | const_floatpoint f20 f21 => f1 f20 f21
  | const_undef t => f2 t
  | const_null t => f3 t
  | const_arr t l => f4 t l (F0 l)
  | const_struct t l => f5 t l (F0 l)
  | const_gid t i => f6 t i
  | const_truncop t c0 t0 => f7 t c0 (F c0) t0
  | const_extop e c0 t => f8 e c0 (F c0) t
  | const_castop c0 c1 t => f9 c0 c1 (F c1) t
  | const_gep i c0 l => f10 i c0 (F c0) l (F0 l)
  | const_select c0 c1 c2 => f11 c0 (F c0) c1 (F c1) c2 (F c2)
  | const_icmp c0 c1 c2 => f12 c0 c1 (F c1) c2 (F c2)
  | const_fcmp f20 c0 c1 => f13 f20 c0 (F c0) c1 (F c1)
  | const_extractvalue c0 l => f14 c0 (F c0) l (F0 l)
  | const_insertvalue c0 c1 l => f15 c0 (F c0) c1 (F c1) l (F0 l)
  | const_bop b c0 c1 => f16 b c0 (F c0) c1 (F c1)
  | const_fbop f20 c0 c1 => f17 f20 c0 (F c0) c1 (F c1)
  end.

Definition list_const_ind2 (P : const -> Prop) (P0 : list const -> Prop)
  (f : forall t : typ, P (const_zeroinitializer t))
  (f0 : forall (s : sz) (i : Int), P (const_int s i))
  (f1 : forall (f1 : floating_point) (f2 : Float), P (const_floatpoint f1 f2))
  (f2 : forall t : typ, P (const_undef t))
  (f3 : forall t : typ, P (const_null t))
  (f4 : forall (t : typ) (l : list const), P0 l -> P (const_arr t l))
  (f5 : forall (t : typ) (l : list const), P0 l -> P (const_struct t l))
  (f6 : forall (t : typ) (i : id), P (const_gid t i))
  (f7 : forall (t : truncop) (c : const),
        P c -> forall t0 : typ, P (const_truncop t c t0))
  (f8 : forall (e : extop) (c : const),
        P c -> forall t : typ, P (const_extop e c t))
  (f9 : forall (c : castop) (c0 : const),
        P c0 -> forall t : typ, P (const_castop c c0 t))
  (f10 : forall (i : inbounds) (c : const),
         P c -> forall l : list const, P0 l -> P (const_gep i c l))
  (f11 : forall c : const,
         P c ->
         forall c0 : const,
         P c0 -> forall c1 : const, P c1 -> P (const_select c c0 c1))
  (f12 : forall (c : cond) (c0 : const),
         P c0 -> forall c1 : const, P c1 -> P (const_icmp c c0 c1))
  (f13 : forall (f13 : fcond) (c : const),
         P c -> forall c0 : const, P c0 -> P (const_fcmp f13 c c0))
  (f14 : forall c : const,
         P c -> forall l : list const, P0 l -> P (const_extractvalue c l))
  (f15 : forall c : const,
         P c ->
         forall c0 : const,
         P c0 -> forall l : list const, P0 l -> P (const_insertvalue c c0 l))
  (f16 : forall (b : bop) (c : const),
         P c -> forall c0 : const, P c0 -> P (const_bop b c c0))
  (f17 : forall (f17 : fbop) (c : const),
         P c -> forall c0 : const, P c0 -> P (const_fbop f17 c c0))
  (f18 : P0 nil)
  (f19 : forall c : const,
         P c -> forall l : list const, P0 l -> P0 (c :: l)) :=
  let F := const_rec2 P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
    f11 f12 f13 f14 f15 f16 f17 f18 f19 in
  fix F0 (l : list const) : P0 l :=
    match l return P0 l with
    | nil => f18
    | c :: l => f19 c (F c) l (F0 l)
    end.

Combined Scheme const_mutind from const_ind2, list_const_ind2.

Definition typ_ind2 (P : typ -> Prop) (P0 : list typ -> Prop)
  (f : forall s : sz, P (typ_int s))
  (f0 : forall f0 : floating_point, P (typ_floatpoint f0))
  (f1 : P typ_void) (f2 : P typ_label) (f3 : P typ_metadata)
  (f4 : forall (s : sz) (t : typ), P t -> P (typ_array s t))
  (f5 : forall t : typ,
        P t ->
        forall l : list typ, P0 l -> forall v : varg, P (typ_function t l v))
  (f6 : forall l : list typ, P0 l -> P (typ_struct l))
  (f7 : forall t : typ, P t -> P (typ_pointer t))
  (f8 : forall i : id, P (typ_namedt i)) (f9 : P0 nil)
  (f10 : forall t : typ,
         P t -> forall l : list typ, P0 l -> P0 (t :: l)) :=
  fix F (t : typ) : P t :=
  let F0 :=
    fix F0 (l : list typ) : P0 l :=
    match l return P0 l with
      | nil => f9
      | t :: l0 => f10 t (F t) l0 (F0 l0)
    end in
  match t as t0 return (P t0) with
  | typ_int s => f s
  | typ_floatpoint f11 => f0 f11
  | typ_void => f1
  | typ_label => f2
  | typ_metadata => f3
  | typ_array s t0 => f4 s t0 (F t0)
  | typ_function t0 l v => f5 t0 (F t0) l (F0 l) v
  | typ_struct l => f6 l (F0 l)
  | typ_pointer t0 => f7 t0 (F t0)
  | typ_namedt i => f8 i
  end.

Definition list_typ_ind2 (P : typ -> Prop) (P0 : list typ -> Prop)
  (f : forall s : sz, P (typ_int s))
  (f0 : forall f0 : floating_point, P (typ_floatpoint f0))
  (f1 : P typ_void) (f2 : P typ_label) (f3 : P typ_metadata)
  (f4 : forall (s : sz) (t : typ), P t -> P (typ_array s t))
  (f5 : forall t : typ,
        P t ->
        forall l : list typ, P0 l -> forall v : varg, P (typ_function t l v))
  (f6 : forall l : list typ, P0 l -> P (typ_struct l))
  (f7 : forall t : typ, P t -> P (typ_pointer t))
  (f8 : forall i : id, P (typ_namedt i)) (f9 : P0 nil)
  (f10 : forall t : typ,
         P t -> forall l : list typ, P0 l -> P0 (t :: l)) :=
  let F := typ_rec2 P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 in
  fix F0 (l : list typ) : P0 l :=
  match l return P0 l with
    | nil => f9
    | t :: l0 => f10 t (F t) l0 (F0 l0)
  end.

Combined Scheme typ_mutind from typ_ind2, list_typ_ind2.


End LLVMsyntax.

Ltac destruct_cmd cmd :=
let i0 := fresh "i0" in
let i1 := fresh "i1" in
let b := fresh "b" in
let s0 := fresh "s0" in
let v := fresh "v" in
let v0 := fresh "v0" in
let v1 := fresh "v1" in
let f0 := fresh "f0" in
let f1 := fresh "f1" in
let t := fresh "t" in
let t0 := fresh "t0" in
let t1 := fresh "t1" in
let l2 := fresh "l2" in
let a := fresh "a" in
let p := fresh "p" in
let n := fresh "n" in
let c := fresh "c" in
let e := fresh "e" in
destruct cmd as [i0 b s0 v v0|i0 f0 f1 v v0|i0 t v l2 t0|i0 t v t0 v0 l2|
                 i0 t v a|i0 t v|i0 t v a|i0 t v a|i0 t v v0 a|i0 i1 t v l2 t0|
                 i0 t t0 v t1|i0 e t v t0|i0 c t v t0|i0 c t v v0|
                 i0 f0 f1 v v0|i0 v t v0 v1|i0 n c t0 v0 v p].

Ltac destruct_typ t :=
let s0 := fresh "s0" in
let f := fresh "f" in
let t0 := fresh "t0" in
let lt0 := fresh "lt0" in
let i0 := fresh "i0" in
destruct t as [s0 | f | | | | s0 t0 | t0 lt0 | lt0 | t0 | i0 ].

Ltac destruct_const cst :=
let Int5 := fresh "Int5" in
let i0 := fresh "i0" in
let b := fresh "b" in
let sz5 := fresh "sz5" in
let f0 := fresh "f0" in
let f1 := fresh "f1" in
let t := fresh "t" in
let t0 := fresh "t0" in
let l2 := fresh "l2" in
let c0 := fresh "c0" in
let c1 := fresh "c1" in
let c2 := fresh "c2" in
let e := fresh "e" in
let cs0 := fresh "cs0" in
destruct cst as [t|sz5 Int5|f0 f1|t|t|t cs0|t cs0|t i0|t c0 t0|e c0 t0|c0 c1 t0|
                 i0 c0 cs0|c0 c1 c2|c0 c1 c2|f0 c1 c2|c0 cs0|c0 c1 cs0|
                 b c0 c1|f0 c0 c1].

Ltac destruct_tmn tmn :=
let id5 := fresh "id5" in
let t := fresh "t" in
let value5 := fresh "value5" in
let l2 := fresh "l2" in
let l3 := fresh "l3" in
let i0 := fresh "i0" in
destruct tmn as [id5 t value5 | id5 | id5 value5 l2 l3 | i0 l2 | ].
