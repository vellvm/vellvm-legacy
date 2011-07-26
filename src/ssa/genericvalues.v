Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import List.
Require Import Arith.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import alist.
Require Import ssa_def.
Require Import ssa_lib.
Require Import Memory.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import targetdata.
Require Import ZArith.
Require Import Floats.
Require Import ssa_static.

Module LLVMgv.

Export LLVMsyntax.
Export LLVMlib.
Export LLVMtd.

Definition moffset := Int.int 31.
Definition mem := Mem.mem.
Definition GenericValue := list (val*memory_chunk).
Definition GVMap := list (id*GenericValue).

Definition mblock := Values.block.
Definition mptr := GenericValue.
Definition null : GenericValue := 
  (Vptr Mem.nullptr (Int.repr 31 0), Mint 31)::nil.

Fixpoint eq_gv (gv1 gv2:GenericValue) : bool :=
match gv1, gv2 with
| nil, nil => true
| (v1,c1)::gv1', (v2,c2)::gv2' => Val.eq v1 v2 && 
                                  memory_chunk_eq c1 c2 && 
                                  eq_gv gv1' gv2'
| _, _ => false
end.

Definition uninits (n:nat) : GenericValue := 
   Coqlib.list_repeat n (Vundef, Mint 7).

Definition gundef (TD:TargetData) (t:typ) : option GenericValue := 
match (getTypeSizeInBits TD t) with
| Some sz => Some ((Vundef, Mint (sz-1))::nil)
| None => None
end.

Definition GV2val (TD:TargetData) (gv:GenericValue) : option val :=
match gv with
| (v,c)::nil => Some v
| _ => Some Vundef
end.
Definition GV2int (TD:TargetData) (bsz:sz) (gv:GenericValue) : option Z :=
match gv with
| (Vint wz i,c)::nil =>
  if eq_nat_dec (wz+1) (Size.to_nat bsz)
  then Some (Int.signed wz i)
  else None
| _ => None
end.
Definition GV2ptr (TD:TargetData) (bsz:sz) (gv:GenericValue) : option val :=
match gv with
| (Vptr a b,c)::nil => Some (Vptr a b)
| _ => None
end.
Fixpoint isGVUndef (gv:GenericValue) : Prop :=
match gv with
| nil => False
| (Vundef,_)::gv' => True
| _::gv' => isGVUndef gv'
end.
Definition val2GV (TD:TargetData) (v:val) (c:memory_chunk) : GenericValue :=
(v,c)::nil.
Definition ptr2GV (TD:TargetData) (ptr:val) : GenericValue :=
val2GV TD ptr (Mint (Size.mul Size.Eight (getPointerSize TD)-1)).
Definition blk2GV (TD:TargetData) (b:mblock) : GenericValue :=
ptr2GV TD (Vptr b (Int.repr 31 0)).
Definition isGVZero (TD:TargetData) (gv:GenericValue) : bool :=
match (GV2int TD Size.One gv) with
| Some z => if Coqlib.zeq z 0 then true else false
| _ => false
end.

Definition mgep (TD:TargetData) (t:typ) (ma:val) (idxs:list Z) : option val :=
match ma with
| Vptr b ofs => 
  match idxs with
  | nil => None
  | _ =>
    match (mgetoffset TD (typ_array 0%nat t) idxs) with
    | Some (offset, _) => Some (Vptr b (Int.add 31 ofs (Int.repr 31 offset)))
    | _ => None
    end
  end
| _ => None
end.

Fixpoint sizeGenericValue (gv:GenericValue) : nat :=
match gv with
| nil => 0%nat
| (v,c)::gv' => (size_chunk_nat c + sizeGenericValue gv')%nat
end.

Fixpoint splitGenericValue (gv:GenericValue) (pos:Z): 
  option (GenericValue*GenericValue) :=
if (Coqlib.zeq pos 0) then Some (nil, gv)
else
  if (Coqlib.zlt pos 0) then None
  else
    match gv with
    | nil => None
    | (v,c)::gv' => 
        match splitGenericValue gv' (pos - size_chunk c) with
        | Some (gvl', gvr') => Some ((v,c)::gvl', gvr')
        | None => None
        end
    end.

Definition mget (TD:TargetData) (gv:GenericValue) (o:Z) (t:typ) 
  : option GenericValue :=
do s <- getTypeStoreSize TD t;
  match (splitGenericValue gv o) with
  | Some (gvl, gvr) =>
      match (splitGenericValue gvr (Z_of_nat s)) with
      | Some (gvrl, gvrr) => Some gvrl
      | None => None
      end
  | None => None
  end.

Definition mset (TD:TargetData) (gv:GenericValue) (o:Z) (t0:typ) 
  (gv0:GenericValue) : option GenericValue :=
let n := Coqlib.nat_of_Z o in
do s <- getTypeStoreSize TD t0;
  if (beq_nat s (length gv0)) then 
    match (splitGenericValue gv o) with
    | Some (gvl, gvr) =>
       match (splitGenericValue gvr (Z_of_nat s)) with
       | Some (gvrl, gvrr) => Some (gvl++gv0++gvrr)
       | None => None
       end
    | None => None
    end
  else None.

Fixpoint GVs2Nats (TD:TargetData) (lgv:list GenericValue) : option (list Z):=
match lgv with
| nil => Some nil
| gv::lgv' => 
    match (GV2int TD Size.ThirtyTwo gv) with
    | Some z =>
        match (GVs2Nats TD lgv') with
        | Some ns => Some (z::ns)
        | None => None
        end
    | _ => None
    end
end.

(* FIXME : bounds check *)
Definition extractGenericValue (TD:TargetData) (t:typ) (gv : GenericValue) 
  (cidxs : list_const) : option GenericValue :=
match (intConsts2Nats TD cidxs) with
| None => None
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some (o, t') => match mget TD gv o t' with 
                    | Some gv' => Some gv'
                    | None => gundef TD t'
                    end
  | None => None
  end
end.

Definition insertGenericValue (TD:TargetData) (t:typ) (gv:GenericValue)
  (cidxs:list_const) (t0:typ) (gv0:GenericValue) : option GenericValue :=
match (intConsts2Nats TD cidxs) with
| None => None
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some (o, _) => match (mset TD gv o t0 gv0) with
                   | Some gv' => Some gv'
                   | None => gundef TD t
                   end
  | None => None
  end
end.

Definition mtrunc (TD:TargetData) (op:truncop) (t1:typ) (t2:typ) 
  (gv1:GenericValue) : option GenericValue :=
match GV2val TD gv1 with
| Some (Vint wz1 i1) =>
    match (t1, t2) with
    | (typ_int sz1, typ_int sz2) =>
        Some (val2GV TD (Val.trunc (Vint wz1 i1) sz2) (Mint (sz2-1)))
    | _ => gundef TD t2
    end
| Some (Vfloat f) =>
    match (t1, t2) with
    | (typ_floatpoint fp1, typ_floatpoint fp2) =>
        if floating_point_order fp2 fp1 
        then 
          match fp2 with
          | fp_float => Some (val2GV TD (Val.ftrunc (Vfloat f)) Mfloat32)
          | fp_double => Some (val2GV TD (Val.ftrunc (Vfloat f)) Mfloat64)
          | _ => None (* FIXME: not supported 80 and 128 yet. *)
          end
        else None
    | _ => gundef TD t2
    end
| _ => gundef TD t2
end.

Definition mbop (TD:TargetData) (op:bop) (bsz:sz) (gv1 gv2:GenericValue) 
  : option GenericValue :=
let bsz' := (Size.to_nat bsz) in 
match (GV2val TD gv1, GV2val TD gv2) with
| (Some (Vint wz1 i1), Some (Vint wz2 i2)) => 
  if eq_nat_dec (wz1+1) bsz'
  then
     match op with
     | bop_add => 
         Some (val2GV TD (Val.add (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_sub => 
         Some (val2GV TD (Val.sub (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_mul => 
         Some (val2GV TD (Val.mul (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_udiv => 
         Some (val2GV TD (Val.divu (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_sdiv => 
         Some (val2GV TD (Val.divs (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_urem => 
         Some (val2GV TD (Val.modu (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_srem => 
         Some (val2GV TD (Val.mods (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_shl => 
         Some (val2GV TD (Val.shl (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_lshr => 
         Some (val2GV TD (Val.shrx (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_ashr => 
         Some (val2GV TD (Val.shr (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_and => 
         Some (val2GV TD (Val.and (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_or => 
         Some (val2GV TD (Val.or (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     | bop_xor => 
         Some (val2GV TD (Val.xor (Vint wz1 i1) (Vint wz2 i2)) (Mint (bsz'-1)))
     end
  else gundef TD (typ_int bsz')
| _ => gundef TD (typ_int bsz')
end.

Definition mfbop (TD:TargetData) (op:fbop) (fp:floating_point) 
  (gv1 gv2:GenericValue) : option GenericValue :=
match (GV2val TD gv1, GV2val TD gv2) with
| (Some (Vfloat f1), Some (Vfloat f2)) => 
  let v :=
     match op with
     | fbop_fadd => Val.addf (Vfloat f1) (Vfloat f2)
     | fbop_fsub => Val.subf (Vfloat f1) (Vfloat f2)
     | fbop_fmul => Val.mulf (Vfloat f1) (Vfloat f2)
     | fbop_fdiv => Val.divf (Vfloat f1) (Vfloat f2)
     | fbop_frem => Val.modf (Vfloat f1) (Vfloat f2)
     end in
  match fp with
  | fp_float => Some (val2GV TD v Mfloat32)
  | fp_double => Some (val2GV TD v Mfloat64)
  | _ => None (* FIXME: not supported 80 and 128 yet. *)
  end
| _ => gundef TD (typ_floatpoint fp)
end.

Definition mptrtoint (TD:TargetData) (M:mem) (gv1:GenericValue) (sz2:nat)
 : option GenericValue :=
    match GV2val TD gv1 with
    | Some (Vptr b1 ofs1) =>
        match Mem.ptr2int M b1 0 with
        | Some z => 
            Some (val2GV TD 
                   (Vint sz2 (Int.repr sz2 (z + Int.signed 31 ofs1))) 
                   (Mint (sz2-1)))
        | None => Some (val2GV TD (Vint sz2 (Int.zero sz2)) (Mint (sz2-1)))
        end
    | Some (Vinttoptr i) => 
        Some (val2GV TD (Vint sz2 (Int.repr sz2 (Int.unsigned 31 i))) 
               (Mint (sz2-1)))
    | _ => gundef TD (typ_int sz2)
    end.

Definition mbitcast (t1:typ) (gv1:GenericValue)(t2:typ) : option GenericValue :=
match (t1, t2) with
| (typ_int sz1, typ_int sz2) => Some gv1
| (typ_pointer _, typ_pointer _) => Some gv1
| _ => None
end.

Definition minttoptr (TD:TargetData) (M:mem) (gv1:GenericValue) 
  : option GenericValue :=
  match GV2val TD gv1 with
  | Some (Vint wz1 i1) =>
      match Mem.int2ptr M (Int.signed wz1 i1) with
      | Some (b,ofs) => Some (ptr2GV TD (Vptr b (Int.repr 31 ofs)))
      | None => 
          Some (ptr2GV TD (Vinttoptr (Int.repr 31 (Int.unsigned wz1 i1))))
      end
  | _ => gundef TD (typ_pointer typ_void)
  end.

(* Here is another idea to support inttoptr and ptrtoint. We should 
   distinguish two kinds of ptr: at global spaces, and at heap or stack. The
   first kind of ptr has an known address at compile time, and at runtime 
   their addresses cannot be reused; the second kind of ptr has no such 
   properties.

   So, we can support i2p and p2i for the first ptr w/o parameterizing Mem
   everywhere (at const2GV and getOperandValue), because we can maintain a 
   fixed mapping that is created at program initialization.

   For p2i, it is total. i2p can be undef if the int value is not in the map.

   This makes values in registers hold the substitution properities. If const2GV
   is with Mem, that means its result can be affected by memory state, so we can-
   not substitute it arbitrarily.

   Having Mem  everywhere, and not distinguishing the two kinds of
   ptr, complicates proofs, because we need to argue that
   1) memory model does not reuse addresses for globals, this is true for our
      corrent memory model, because it has inifite memory, and never reuses,
      but needs more work if we support finite memory later.

   2) It is hard to define simulation relations between the pointers or 
      intergers casted from two programs, because related pointers can be in
      different memory addresses.

   This also indicates that the 2nd kind of ptr should eval to undef by i2p or
   p2i, because what their values are depends on runtime and platform.

   For the time being, we simply consider both of the kinds of ptrs fomr i2p
   to be undef, and integers from p2i to be undef, too.
   
*)
Definition mcast (TD:TargetData) (op:castop) (t1:typ) (t2:typ) (gv1:GenericValue)
 : option GenericValue :=
match op with
| castop_inttoptr => gundef TD t2
| castop_ptrtoint => gundef TD t2
| castop_bitcase => mbitcast t1 gv1 t2 
end.

Definition mext (TD:TargetData) (op:extop) (t1:typ) (t2:typ) (gv1:GenericValue) 
  : option GenericValue :=
match (t1, t2) with
| (typ_int sz1, typ_int sz2) => 
   match (GV2val TD gv1) with
   | Some (Vint wz1 i1) =>
     match op with
     | extop_z => Some (val2GV TD (Val.zero_ext (Size.to_Z sz2) (Vint wz1 i1)) 
                        (Mint (Size.to_nat sz2-1)))
     | extop_s => Some (val2GV TD (Val.sign_ext (Size.to_Z sz2) (Vint wz1 i1)) 
                        (Mint (Size.to_nat sz2-1)))
     | _ => None
     end
   | _ => gundef TD t2
   end
| (typ_floatpoint fp1, typ_floatpoint fp2) => 
  if floating_point_order fp1 fp2 
  then
    match (GV2val TD gv1) with
    | Some (Vfloat f1) =>
      match op with
      | extop_fp =>
         match fp2 with
         | fp_float => Some (val2GV TD (Vfloat f1) Mfloat32)
         | fp_double => Some (val2GV TD (Vfloat f1) Mfloat64)
         | _ => None (* FIXME: not supported 80 and 128 yet. *)
         end
      | _ => None
      end
    | _ => gundef TD t2
    end
  else None
| (_, _) => None
end.

Definition micmp_int TD c gv1 gv2 : option GenericValue :=
  match (GV2val TD gv1, GV2val TD gv2) with
  | (Some (Vint wz1 i1), Some (Vint wz2 i2)) => 
     match c with
     | cond_eq => 
         Some (val2GV TD (Val.cmp Ceq (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ne => 
         Some (val2GV TD (Val.cmp Cne (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ugt => 
         Some (val2GV TD (Val.cmpu Cgt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_uge => 
         Some (val2GV TD (Val.cmpu Cge (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ult => 
         Some (val2GV TD (Val.cmpu Clt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_ule => 
         Some (val2GV TD (Val.cmpu Cle (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_sgt => 
         Some (val2GV TD (Val.cmp Cgt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_sge => 
         Some (val2GV TD (Val.cmp Cge (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_slt => 
         Some (val2GV TD (Val.cmp Clt (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     | cond_sle => 
         Some (val2GV TD (Val.cmp Cle (Vint wz1 i1) (Vint wz2 i2)) (Mint 0))
     end
  | _ => gundef TD (typ_int 1)
  end.  

Definition micmp_ptr (TD:TargetData) (M:mem) (c:cond) (gv1 gv2:GenericValue) 
  : option GenericValue :=
  match (mptrtoint TD M gv1 Size.ThirtyTwo, mptrtoint TD M gv2 Size.ThirtyTwo)
    with
  | (Some gv1', Some gv2') => micmp_int TD c gv1' gv2'
  | _ => None
  end.

Definition micmp (TD:TargetData) (c:cond) (t:typ) (gv1 gv2:GenericValue) 
  : option GenericValue :=
match t with
| typ_int sz => micmp_int TD c gv1 gv2
| typ_pointer _ => gundef TD (typ_int 1)
| _ => None
end.

Definition mfcmp (TD:TargetData) (c:fcond) (fp:floating_point) 
  (gv1 gv2:GenericValue) : option GenericValue :=
match (GV2val TD gv1, GV2val TD gv2) with
| (Some (Vfloat f1), Some (Vfloat f2)) => 
   let ov := 
     match c with
     | fcond_false => Some (val2GV TD Vfalse (Mint 0))
     | fcond_oeq => 
         Some (val2GV TD (Val.cmpf Ceq (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_ogt => 
         Some (val2GV TD (Val.cmpf Cgt (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_oge => 
         Some (val2GV TD (Val.cmpf Cge (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_olt =>
         Some (val2GV TD (Val.cmpf Clt (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_ole => 
         Some (val2GV TD (Val.cmpf Cle (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_one => 
         Some (val2GV TD (Val.cmpf Cne (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_ord => None (*FIXME: not supported yet. *)
     | fcond_ueq => 
         Some (val2GV TD (Val.cmpf Ceq (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_ugt => 
         Some (val2GV TD (Val.cmpf Cgt (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_uge => 
         Some (val2GV TD (Val.cmpf Cge (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_ult => 
         Some (val2GV TD (Val.cmpf Clt (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_ule => 
         Some (val2GV TD (Val.cmpf Cle (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_une => 
         Some (val2GV TD (Val.cmpf Cne (Vfloat f1) (Vfloat f2)) (Mint 0))
     | fcond_uno => None (*FIXME: not supported yet. *)
     | fcond_true => Some (val2GV TD Vtrue (Mint 0))
     end in
   match fp with
   | fp_float => ov
   | fp_double => ov
   | _ => None (*FIXME: not supported 80 and 128 yet. *)
   end  
| _ => gundef TD (typ_int 1)
end.

(**************************************)
(** Convert const to GV with storesize, and look up GV from operands. *)

Fixpoint repeatGV (gv:GenericValue) (n:nat) : GenericValue :=
match n with
| O => nil
| S n' => gv++repeatGV gv n'
end.

Fixpoint zeroconst2GV (TD:TargetData) (t:typ) : option GenericValue :=
match t with
| typ_int sz => 
  let wz := (Size.to_nat sz) - 1 in
  Some (val2GV TD (Vint wz (Int.repr wz 0)) (Mint wz))
| typ_floatpoint fp =>
  match fp with
  | fp_float => Some (val2GV TD (Vfloat Float.zero) Mfloat32)
  | fp_double => Some (val2GV TD (Vfloat Float.zero) Mfloat64)
  | _ => None (* FIXME: not supported 80 and 128 yet. *)
  end
| typ_void => None          
| typ_label => None                     
| typ_metadata => None                
| typ_array sz t => 
  match sz with
  | O => Some (uninits 1)  
  | _ =>
    match zeroconst2GV TD t with
    | Some gv0 =>
      match getTypeAllocSize TD t with
      | Some asz => 
         Some (repeatGV (gv0++uninits (Size.to_nat asz - sizeGenericValue gv0)) 
                 (Size.to_nat sz))
      | _ => None 
      end
    | _ => None
    end
  end
| typ_struct ts => 
  match zeroconsts2GV TD ts with
  | Some nil => Some (uninits 1)  
  | Some gv0 => Some gv0
  | None => None
  end
| typ_pointer t' => Some null
| typ_function _ _ _ => None
| typ_opaque => None
| typ_namedt _ => None (*FIXME: Can zeroconstant be of named type? How about termination. *)
end             
with zeroconsts2GV (TD:TargetData) (lt:list_typ) : option GenericValue := 
match lt with
| Nil_list_typ => Some nil
| Cons_list_typ t lt' =>
  match (zeroconsts2GV TD lt', zeroconst2GV TD t) with
  | (Some gv, Some gv0) =>
       match getTypeAllocSize TD t with
       | Some asz => Some (gv++gv0++uninits (asz - sizeGenericValue gv0))
       | _ => None 
       end
  | _ => None
  end
end
.

Tactic Notation "typ_cases" tactic(first) tactic(c) :=
  first;
  [ c "typ_int" | c "typ_floatingpoint" |
    c "typ_void" | c "typ_label" |
    c "typ_metadata" | c "typ_array" |
    c "typ_function" | c "typ_struct" | c "typ_pointer" | c "typ_opaque" |
    c "typ_namedt" | c "typ_nil" | c "typ_cons" ].

Ltac inv H := inversion H; subst; clear H.

Lemma sizeGenericValue__app : forall gv1 gv2,
  sizeGenericValue (gv1 ++ gv2) = sizeGenericValue gv1 + sizeGenericValue gv2.
Proof.
  induction gv1; intros; simpl; auto.
    destruct a. rewrite IHgv1. omega.
Qed.

Lemma sizeGenericValue__repeatGV : forall gv n,
  sizeGenericValue (repeatGV gv n) = n * sizeGenericValue gv.
Proof.
  induction n; simpl; auto.
    rewrite sizeGenericValue__app. rewrite IHn. auto.
Qed.

Lemma sizeGenericValue__uninits : forall n, sizeGenericValue (uninits n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma nat_of_Z_inj_ge : forall a b, (a >= b)%Z -> 
  (Coqlib.nat_of_Z a >= Coqlib.nat_of_Z b)%nat.
Proof.
  induction a; destruct b; intros; simpl; 
    try solve [auto | contradict H; auto | omega].
  apply nat_compare_le.
  rewrite <- nat_of_P_compare_morphism.

  assert (p >= p0)%positive as J. auto with zarith.
  unfold Pge in J.
  remember ((p ?= p0)%positive Eq) as R.
  destruct R; try solve [congruence].
    symmetry in HeqR. apply ZC3 in HeqR. rewrite HeqR. congruence.
    symmetry in HeqR. apply ZC1 in HeqR. rewrite HeqR. congruence.
Qed.    

Require Import Znumtheory.

Lemma RoundUpAlignment_spec : 
  forall a b, (b > 0)%nat -> (RoundUpAlignment a b >= a)%nat.
Proof.
  intros. unfold RoundUpAlignment.
  assert ((Z_of_nat a + Z_of_nat b) / Z_of_nat b * Z_of_nat b >= Z_of_nat a)
    as J.
    apply Coqlib.roundup_is_correct.
      destruct b; try solve [contradict H; omega | apply Coqlib.Z_of_S_gt_O].
  apply nat_of_Z_inj_ge in J.  
  rewrite Coqlib.Z_of_nat_eq in J. auto.
Qed.


Lemma list_system_typ_spec : forall (s : system) (l0 : list_typ),
  exists ls0 : list system,
    split
       (LLVMwf.unmake_list_system_typ
          (LLVMwf.make_list_system_typ
             (map_list_typ (fun typ_ : typ => (s, typ_)) l0))) =
    (ls0, unmake_list_typ l0).
Proof.
  induction l0; simpl; eauto.
    destruct IHl0 as [ls J].
    rewrite J. eauto.
Qed.

Lemma unmake_list_system_typ_inv : forall lst ls t l0,
  split (LLVMwf.unmake_list_system_typ lst) = (ls, t :: unmake_list_typ l0) ->
  exists s, exists ls', exists lst',
    lst = LLVMwf.Cons_list_system_typ s t lst' /\ ls = s::ls' /\ 
    split (LLVMwf.unmake_list_system_typ lst') = (ls', unmake_list_typ l0).
Proof.
  induction lst; intros; simpl in *.
    inv H.
  
    remember (split (LLVMwf.unmake_list_system_typ lst)) as R.
    destruct R as [g d].
    inv H.
    exists s. exists g. exists lst. auto.
Qed.

Lemma Z_of_nat_ge_0 : forall n, Z_of_nat n >= 0.
Proof.
  destruct n.
    simpl; auto with zarith.  
    auto using Coqlib.Z_of_S_gt_O with zarith.  
Qed.


Lemma feasible_array_typ_inv : forall TD s t,
  Constant.feasible_typ TD (typ_array s t) -> Constant.feasible_typ TD t.
Proof.
  intros.
  simpl in *.
  unfold getTypeSizeInBits_and_Alignment in *.
  destruct TD.
  destruct (_getTypeSizeInBits_and_Alignment l0
           (_getTypeSizeInBits_and_Alignment_for_namedts l0 (rev n) true)
           true t) as [[]|]; eauto.
Qed.

Lemma feasible_struct_typ_inv : forall TD ts,
  Constant.feasible_typ TD (typ_struct ts) -> Constant.feasible_typs TD ts.
Proof.
  intros.
  unfold Constant.feasible_typ in H.
  unfold Constant.feasible_typs. 
  unfold getTypeSizeInBits_and_Alignment in *.
  destruct TD.
  simpl in *.
  destruct (_getListTypeSizeInBits_and_Alignment l0
           (_getTypeSizeInBits_and_Alignment_for_namedts l0 (rev n) true)
           ts) as [[]|]; eauto.
Qed.

Lemma nat_of_Z_inj_gt : forall a b, (a > b)%Z -> (b >= 0)%Z ->
  (Coqlib.nat_of_Z a > Coqlib.nat_of_Z b)%nat.
Proof.
  induction a; destruct b; intros; simpl; 
    try solve [auto | contradict H; auto | omega].

  assert (J:=@ZL4 p).
  destruct J as [h J]. rewrite J. omega.

  apply nat_compare_lt.
  rewrite <- nat_of_P_compare_morphism.
  assert (p > p0)%positive as J. auto with zarith.
  unfold Pgt in J.
  remember ((p ?= p0)%positive Eq) as R.
  destruct R; try solve [congruence].
    symmetry in HeqR. apply ZC1 in HeqR. rewrite HeqR. congruence.

  apply Zgt_compare in H. inversion H.
Qed.    

Definition feasible_typ_inv_prop (t:typ) := forall TD s,
  LLVMwf.wf_typ s t -> Constant.feasible_typ TD t -> 
  exists sz, exists al,
    getTypeSizeInBits_and_Alignment TD true t = Some (sz, al) /\ 
    (sz > 0)%nat /\ (al > 0)%nat.

Definition feasible_typs_inv_prop (lt:list_typ) := forall TD lst,
  LLVMwf.wf_typ_list lst -> Constant.feasible_typs TD lt -> 
  (exists ls, 
    split (LLVMwf.unmake_list_system_typ lst) = (ls, unmake_list_typ lt)) ->
  (forall t, In t (unmake_list_typ lt) -> Constant.feasible_typ TD t) /\
  exists sz, exists al,
    getListTypeSizeInBits_and_Alignment TD true lt = Some (sz,al) /\
    ((sz > 0)%nat -> (al > 0)%nat).

Lemma feasible_typ_inv_mutrec :
  (forall t, feasible_typ_inv_prop t) *
  (forall lt, feasible_typs_inv_prop lt).
Proof.
  (typ_cases (apply typ_mutrec; 
    unfold feasible_typ_inv_prop, feasible_typs_inv_prop) Case);
    intros;
    unfold getTypeSizeInBits_and_Alignment in *; 
    simpl in *; try (destruct TD); 
    try solve [eauto | inversion H0 | inversion H2].
Case "typ_int".
  inv H. eauto.
Case "typ_floatingpoint".
  destruct f; inv H; try solve [inversion H0 | eauto].
    unfold Constant.feasible_typ_aux in H0. simpl in H0.
    exists 32%nat. exists (getFloatAlignmentInfo l0 32 true).
    split; auto. omega.

    unfold Constant.feasible_typ_aux in H0. simpl in H0.
    exists 64%nat. exists (getFloatAlignmentInfo l0 64 true).
    split; auto. omega.
Case "typ_array".
  inv H0.
  eapply H in H1; eauto.
  destruct H1 as [sz [al [J1 [J2 J3]]]].
  rewrite J1. 
  destruct s.
    exists 8%nat. exists 1%nat. split; auto. omega.

    exists (RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) al * 8 *
             Size.to_nat (S s))%nat.
    exists al. split; auto. split; auto.
    assert (RoundUpAlignment (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) al
      >= (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)))%nat as J4.
      apply RoundUpAlignment_spec; auto.
    assert (Coqlib.ZRdiv (Z_of_nat sz) 8 > 0) as J5.
      apply Coqlib.ZRdiv_prop3; try omega.
    apply nat_of_Z_inj_gt in J5; try omega.
    simpl in J5.
    assert (RoundUpAlignment (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) al
      * 8 > 0)%nat as J6. omega. clear J4 J5.
    assert (Size.to_nat (S s) > 0)%nat as J7. unfold Size.to_nat. omega.
    remember (RoundUpAlignment (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) 
      al * 8)%nat as R1. 
    remember (Size.to_nat (S s)) as R2. 
    clear - J6 J7.
    assert (0 * R2 < R1 * R2)%nat as J.
      apply mult_lt_compat_r; auto.
    simpl in J. auto.

Case "typ_struct".
  inv H0.
  eapply H in H1; eauto using list_system_typ_spec.
  destruct H1 as [J0 [sz [al [J1 J2]]]].
  unfold getListTypeSizeInBits_and_Alignment in J1.
  rewrite J1. 
  destruct sz.
    exists 8%nat. exists 1%nat. split; auto. omega.
    exists (S sz0). exists al. split; auto. split. omega. apply J2. omega.

Case "typ_pointer".
  unfold Constant.feasible_typ_aux in H1. simpl in H1.
  unfold getPointerSizeInBits, Size.to_nat.
  simpl.
  exists 32%nat. exists (getPointerAlignmentInfo l0 true).
  split; auto. omega.

Case "typ_nil".
  split.
    intros. inversion H2.
    simpl. exists 0%nat. exists 0%nat. split; auto.

Case "typ_cons".
  destruct H2 as [J1 J2]. destruct H3 as [l3 H3].
  apply unmake_list_system_typ_inv in H3.
  destruct H3 as [s [ls' [lst' [J1' [J2' J3']]]]]; subst.
  inv H1.
  eapply H0 in J2; eauto.
  destruct J2 as [J21 [sz2 [al2 [J22 J23]]]].
  split.
    intros. 
    destruct H1 as [H1 | H1]; subst; auto.
      
    simpl.
    unfold getListTypeSizeInBits_and_Alignment in J22.
    unfold getTypeSizeInBits_and_Alignment_for_namedts in J22.
    rewrite J22.
    eapply H in J1; eauto.
    destruct J1 as [sz1 [al1 [J11 [J12 J13]]]].
    unfold getTypeSizeInBits_and_Alignment_for_namedts in J11.
    rewrite J11.
    destruct (le_lt_dec al1 al2); eauto.
      exists (sz2 +
             RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz1) 8)) al1 * 8)%nat.
      exists al2.
      split; auto.
        intros. clear - J13 l2. omega.
Qed.

Lemma feasible_typ_inv : forall t TD s,
  LLVMwf.wf_typ s t -> Constant.feasible_typ TD t -> 
  exists sz, exists al,
    getTypeSizeInBits_and_Alignment TD true t = Some (sz, al) /\ 
    (sz > 0)%nat /\ (al > 0)%nat.
Proof.
  destruct feasible_typ_inv_mutrec; auto.
Qed.

Definition feasible_typ_inv_prop' (t:typ) := forall TD,
  Constant.feasible_typ TD t -> 
  exists sz, exists al,
    getTypeSizeInBits_and_Alignment TD true t = Some (sz, al) /\ (al > 0)%nat.

Definition feasible_typs_inv_prop' (lt:list_typ) := forall TD,
  Constant.feasible_typs TD lt -> 
  (forall t, In t (unmake_list_typ lt) -> Constant.feasible_typ TD t) /\
  exists sz, exists al,
    getListTypeSizeInBits_and_Alignment TD true lt = Some (sz,al) /\
    ((sz > 0)%nat -> (al > 0)%nat).

Lemma feasible_typ_inv_mutrec' :
  (forall t, feasible_typ_inv_prop' t) *
  (forall lt, feasible_typs_inv_prop' lt).
Proof.
  (typ_cases (apply typ_mutrec; 
    unfold feasible_typ_inv_prop', feasible_typs_inv_prop') Case);
    intros;
    unfold getTypeSizeInBits_and_Alignment in *; 
    simpl in *; try (destruct TD); 
    try solve [eauto | inversion H | inversion H1].
Case "typ_floatingpoint".
  destruct f; try solve [inv H].
    exists 32%nat. exists (getFloatAlignmentInfo l0 32 true).
    split; auto. 

    exists 64%nat. exists (getFloatAlignmentInfo l0 64 true).
    split; auto.
Case "typ_array".
  eapply H in H0; eauto.
  destruct H0 as [sz [al [J1 J2]]].
  rewrite J1. 
  destruct s.
    exists 8%nat. exists 1%nat. split; auto.

    exists (RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) al * 8 *
             Size.to_nat (S s))%nat.
    exists al. split; auto.
Case "typ_struct".
  eapply H in H0; eauto using list_system_typ_spec.
  destruct H0 as [J0 [sz [al [J1 J2]]]].
  unfold getListTypeSizeInBits_and_Alignment in J1.
  rewrite J1. 
  destruct sz.
    exists 8%nat. exists 1%nat. split; auto.
    exists (S sz0). exists al. split; auto. apply J2. omega.

Case "typ_nil".
  split.
    intros. inversion H0.
    simpl. exists 0%nat. exists 0%nat. split; auto.

Case "typ_cons".
  destruct H1 as [J1 J2]. 
  eapply H0 in J2; eauto.
  destruct J2 as [J21 [sz2 [al2 [J22 J23]]]].
  split.
    intros. 
    destruct H1 as [H1 | H1]; subst; auto.
      
    simpl.
    unfold getListTypeSizeInBits_and_Alignment in J22.
    unfold getTypeSizeInBits_and_Alignment_for_namedts in J22.
    rewrite J22.
    eapply H in J1; eauto.
    destruct J1 as [sz1 [al1 [J11 J12]]].
    unfold getTypeSizeInBits_and_Alignment_for_namedts in J11.
    rewrite J11.
    destruct (le_lt_dec al1 al2); eauto.
      exists (sz2 +
             RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz1) 8)) al1 * 8)%nat.
      exists al2.
      split; auto.
        intros. clear - J12 l2. omega.
Qed.

Lemma feasible_typ_inv' : forall t TD,
  Constant.feasible_typ TD t -> 
  exists sz, exists al,
    getTypeSizeInBits_and_Alignment TD true t = Some (sz, al) /\ (al > 0)%nat.
Proof.
  destruct feasible_typ_inv_mutrec'; auto.
Qed.

Lemma ZRdiv_prop6 : forall (a c:nat), 
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat (a * 8 * c)) 8) = (a * c)%nat.
Proof.
  intros.
  assert (a * 8 * c = a * c * 8)%nat as J5. ring.
  rewrite J5. clear J5.
  unfold Coqlib.ZRdiv. rewrite inj_mult. rewrite Z_mod_mult. simpl.
  rewrite Z_div_mult_full; try solve [auto with zarith].
  rewrite Coqlib.Z_of_nat_eq; auto.
Qed.

Lemma getTypeAllocSize_inv : forall TD typ5 sz,
  getTypeAllocSize TD typ5 = ret sz ->
  exists sz0, exists al0, getABITypeAlignment TD typ5 = Some al0 /\
    getTypeSizeInBits_and_Alignment TD true typ5 = Some (sz0, al0) /\
    sz = RoundUpAlignment (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz0) 8)) al0.
Proof.
  intros.
  unfold getTypeAllocSize in H.
  unfold getTypeStoreSize in H.
  unfold getTypeSizeInBits in H.
  unfold getABITypeAlignment in *.
  unfold getAlignment in *.
  remember (getTypeSizeInBits_and_Alignment TD true typ5) as R.
  destruct R as [[sz1 al1]|]; inv H.
  eauto.
Qed.

Lemma getTypeAllocSize_roundup : forall los nts sz2 al2 t
  (H31 : Constant.feasible_typ (los, nts) t)
  (J6 : _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
         true t = ret (sz2, al2))
  (s0 : sz) (HeqR3 : ret s0 = getTypeAllocSize (los, nts) t),
  ((Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8)) +
    (s0 - (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8))))%nat = s0.
Proof.
  intros.
  unfold getTypeAllocSize, getABITypeAlignment, getAlignment, getTypeStoreSize,
    getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
    getTypeSizeInBits_and_Alignment_for_namedts in HeqR3.
  rewrite J6 in HeqR3.
  inv HeqR3.
  assert (RoundUpAlignment (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8)) 
      al2 >= (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8)))%nat as J8.
    apply RoundUpAlignment_spec.
      eapply feasible_typ_inv' in H31; eauto.
      destruct H31 as [sz0 [al0 [J13 J14]]].
      unfold getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts in J13.
      rewrite J6 in J13. inv J13. auto.
  rewrite <- le_plus_minus; auto.
Qed.

Lemma getTypeAllocSize_inv' : forall los nts typ5 sz sz2 al2,
  getTypeAllocSize (los,nts) typ5 = ret sz ->
  _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
         true typ5 = ret (sz2, al2) ->
  sz = RoundUpAlignment (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8)) al2.
Proof.
  intros.
  apply getTypeAllocSize_inv in H.
  destruct H as [sz1 [al1 [J1 [J2 J3]]]].
  unfold getTypeSizeInBits_and_Alignment in J2.
  unfold getTypeSizeInBits_and_Alignment_for_namedts in J2.
  rewrite J2 in H0. inv H0. auto.
Qed.

Lemma ZRdiv_prop7 : forall sz1 R4,
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat (sz1 + R4 * 8)) 8) =
    (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz1) 8) + R4)%nat.
Proof.
  intros.
  unfold Coqlib.ZRdiv. rewrite inj_plus. rewrite inj_mult. simpl.
  rewrite Z_mod_plus; try solve [omega].
  rewrite Z_div_plus; try solve [omega].
  assert (Z_of_nat sz1 / 8 >= 0) as G1. 
    apply Z_div_ge0; auto using Z_of_nat_ge_0 with zarith.
  assert (Z_of_nat R4 >= 0) as G2. 
    apply Z_of_nat_ge_0.
  destruct (Coqlib.zeq (Z_of_nat sz1 mod 8) 0).
    rewrite Coqlib.nat_of_Z_plus; auto.
      rewrite Coqlib.Z_of_nat_eq; auto.
  
    rewrite Coqlib.nat_of_Z_plus; try solve [omega].
    rewrite Coqlib.nat_of_Z_plus; try solve [omega].
    rewrite Coqlib.nat_of_Z_plus; try solve [omega].
    rewrite Coqlib.Z_of_nat_eq; try solve [omega].
Qed.

Lemma int_typsize : forall s0 s
  (H0 : LLVMwf.wf_typ s0 (typ_int s)),
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat s) 8) =
    (size_chunk_nat (Mint (s - 1)) + 0)%nat.
Proof.
  intros.
  unfold size_chunk_nat, size_chunk, bytesize_chunk.
  assert (s > 0)%nat as WF.
    inv H0. auto.
  assert (S (s - 1) = s) as EQ. omega.
  rewrite EQ. auto.
Qed.

Definition zeroconst2GV__getTypeSizeInBits_prop (t:typ) := forall s los nts gv,
  zeroconst2GV (los,nts) t = Some gv ->
  LLVMwf.wf_typ s t -> Constant.feasible_typ (los,nts) t ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
     (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t
     = Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.

Definition zeroconsts2GV__getListTypeSizeInBits_prop (lt:list_typ) := 
  forall los nts gv lst,
  zeroconsts2GV (los,nts) lt = Some gv ->
  LLVMwf.wf_typ_list lst -> Constant.feasible_typs (los,nts) lt ->
  (exists ls, 
    split (LLVMwf.unmake_list_system_typ lst) = (ls, unmake_list_typ lt)) ->
  exists sz, exists al,
    _getListTypeSizeInBits_and_Alignment los 
     (getTypeSizeInBits_and_Alignment_for_namedts (los, nts) true) lt = 
       Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.

Lemma zeroconst2GV_typsize_mutrec :
  (forall t, zeroconst2GV__getTypeSizeInBits_prop t) *
  (forall lt, zeroconsts2GV__getListTypeSizeInBits_prop lt).
Proof.
  (typ_cases (apply typ_mutrec; 
    unfold zeroconst2GV__getTypeSizeInBits_prop, 
           zeroconsts2GV__getListTypeSizeInBits_prop) Case);
    intros; simpl in *; try solve [eauto | inversion H | inversion H1 ].
Case "typ_int".
  inv H.
  simpl.
  exists (Size.to_nat s). exists (getIntAlignmentInfo los (Size.to_nat s) true).
  erewrite int_typsize; eauto.

Case "typ_floatingpoint".
  destruct f; inv H; simpl; unfold size_chunk_nat, size_chunk, bytesize_chunk.
    exists 32%nat. exists (getFloatAlignmentInfo los 32 true).
    simpl. auto.

    exists 64%nat. exists (getFloatAlignmentInfo los 64 true).
    simpl. auto.

Case "typ_array".
  destruct s;  try solve [inv H0; exists 8%nat; exists 1%nat; auto].
  remember (zeroconst2GV (los, nts) t) as R1.
  destruct R1; try solve [inv H0].
  remember (getTypeAllocSize (los, nts) t) as R2.
  destruct R2; inv H0.
  assert (
    (g ++ uninits (Size.to_nat s1 - sizeGenericValue g)) ++
          repeatGV (g ++ uninits (Size.to_nat s1 - sizeGenericValue g)) s = 
    repeatGV (g ++ uninits (Size.to_nat s1 - sizeGenericValue g)) (S s)) as G.
    simpl. auto.
  rewrite G.
  symmetry in HeqR1.
  inv H1.
  apply H with (s:=s0) in HeqR1; eauto using feasible_array_typ_inv.
  destruct HeqR1 as [sz [al [J1 J2]]].
  rewrite J1.  rewrite J2.
  exists (RoundUpAlignment (sizeGenericValue g) al * 8 * Size.to_nat (S s))%nat.
  exists al.
  split; auto.
  unfold getTypeAllocSize, getABITypeAlignment, getAlignment, getTypeStoreSize,
    getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
    getTypeSizeInBits_and_Alignment_for_namedts in HeqR2.
  rewrite J1 in HeqR2.
  inv HeqR2.
  rewrite sizeGenericValue__repeatGV.
  rewrite sizeGenericValue__app.
  rewrite sizeGenericValue__uninits. rewrite J2. unfold Size.to_nat.
  assert (RoundUpAlignment (sizeGenericValue g) al >= (sizeGenericValue g))%nat 
    as J3.
    apply RoundUpAlignment_spec.
      eapply feasible_typ_inv in H2; eauto.
      destruct H2 as [sz0 [al0 [J3 [J4 J5]]]].
      unfold getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts in J3.
      rewrite J1 in J3. inv J3. auto.

  assert ((sizeGenericValue g +
     (RoundUpAlignment (sizeGenericValue g) al - sizeGenericValue g))%nat = 
     (RoundUpAlignment (sizeGenericValue g) al)) as J4.
    rewrite <- le_plus_minus; auto.
  rewrite J4.
  rewrite ZRdiv_prop6.
  ring.

Case "typ_struct".
  remember (zeroconsts2GV (los, nts) l0) as R1.
  destruct R1; inv H0.
  symmetry in HeqR1.
  inv H1.
  eapply H in HeqR1; eauto using list_system_typ_spec, feasible_struct_typ_inv.
  destruct HeqR1 as [sz [al [J1 J2]]].
  rewrite J1.
  destruct sz.
    exists 8%nat. exists 1%nat.
    split; auto.
      simpl in J2.
      destruct g as [|[]]; inv H4; auto.
        simpl in J2.
        assert (J3 := size_chunk_nat_pos' m).
        contradict J2; omega.

    exists (S sz0). exists al.
    split; auto.
      rewrite J2.
      destruct g as [|[]]; inv H4; auto.
        assert (Coqlib.ZRdiv (Z_of_nat (S sz0)) 8 > 0) as J.
          apply Coqlib.ZRdiv_prop3; try solve [omega | apply Coqlib.Z_of_S_gt_O].
        apply Coqlib.nat_of_Z_pos in J.
        contradict J2. simpl in *. omega.

Case "typ_pointer".
  inv H0.
  exists (Size.to_nat (getPointerSizeInBits los)).
  exists (getPointerAlignmentInfo los true).
  split; auto.
     
Case "typ_nil".
  inv H. 
  exists 0%nat. exists 0%nat. auto.

Case "typ_cons".
  destruct H4 as [ls H4].
  apply unmake_list_system_typ_inv in H4.
  destruct H4 as [s [ls' [lst' [J1 [J2 J3]]]]]; subst.
  inv H2.
  remember (zeroconsts2GV (los, nts) l0) as R1.
  destruct R1; inv H1.
  remember (zeroconst2GV (los, nts) t) as R2.
  destruct R2; inv H4.
  remember (getTypeAllocSize (los, nts) t) as R3.
  destruct R3; inv H2.
  symmetry in HeqR1. symmetry in HeqR2.
  destruct H3 as [H31 H32].
  eapply H in HeqR2; eauto.
  eapply H0 in HeqR1; eauto.
  destruct HeqR1 as [sz1 [al1 [J4 J5]]].
  destruct HeqR2 as [sz2 [al2 [J6 J7]]].
  rewrite J4. rewrite J6.
  rewrite sizeGenericValue__app.
  rewrite sizeGenericValue__app.
  rewrite sizeGenericValue__uninits. 
  rewrite <- J5. rewrite <- J7. 
  erewrite getTypeAllocSize_roundup; eauto.
  eapply getTypeAllocSize_inv' in J6; eauto. subst.
  exists ((sz1 +
             RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8)) al2 * 8 )%nat).
  exists (if le_lt_dec al2 al1 then al1 else al2).
  split; auto.
    apply ZRdiv_prop7.
Qed.

Lemma zeroconst2GV__getTypeSizeInBits : forall t s los nts gv,
  zeroconst2GV (los,nts) t = Some gv ->
  LLVMwf.wf_typ s t -> Constant.feasible_typ (los,nts) t ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof.
  destruct zeroconst2GV_typsize_mutrec; auto.
Qed.

Fixpoint _const2GV (TD:TargetData) (gl:GVMap) (c:const) 
  : option (GenericValue*typ) := 
match c with
| const_zeroinitializer t => 
  match zeroconst2GV TD t with
  | Some gv => Some (gv, t)
  | None => None
  end
| const_int sz n => 
         let wz := (Size.to_nat sz - 1)%nat in
         Some (val2GV TD (Vint wz (Int.repr wz (INTEGER.to_Z n))) (Mint wz), 
               typ_int sz)
| const_floatpoint fp f =>
         match fp with
         | fp_float => Some (val2GV TD (Vfloat f) Mfloat32, typ_floatpoint fp)
         | fp_double => Some (val2GV TD (Vfloat f) Mfloat64, typ_floatpoint fp)
         | _ => None (* FIXME: not supported 80 and 128 yet. *)
         end
| const_undef t =>  
         match (gundef TD t) with
         | Some gv => Some (gv, t)
         | None => None
         end
| const_null t => 
         Some (val2GV TD (Vptr Mem.nullptr (Int.repr 31 0)) (Mint 31), 
               typ_pointer t)
| const_arr t lc => 
         match _list_const_arr2GV TD gl t lc with
         | Some gv => 
             match length (unmake_list_const lc) with
             | O => Some (uninits 1, 
                            typ_array (length (unmake_list_const lc)) t)
             | _ => Some (gv, 
                            typ_array (length (unmake_list_const lc)) t)
             end
         | _ => None
         end
| const_struct lc => 
         match (_list_const_struct2GV TD gl lc) with
         | None => None
         | Some (nil, ts) => Some (uninits 1, typ_struct ts)
         | Some (gv, ts) => Some (gv, typ_struct ts)
         end
| const_gid t id =>
         match (lookupAL _ gl id) with
         | Some gv => Some (gv, typ_pointer t)
         | None => None
         end
| const_truncop op c1 t2 =>
         match _const2GV TD gl c1 with
         | Some (gv1, t1) => 
           match mtrunc TD op t1 t2 gv1 with
           | Some gv2 => Some (gv2, t2)
           | _ => None
           end
         | _ => None
         end
| const_extop op c1 t2 =>
         match _const2GV TD gl c1 with
         | Some (gv1, t1) => 
           match mext TD op t1 t2 gv1 with
           | Some gv2 => Some (gv2, t2)
           | _ => None
           end
         | _ => None
         end
| const_castop op c1 t2 =>
         match _const2GV TD gl c1 with
         | Some (gv1, t1) => 
           match mcast TD op t1 t2 gv1 with
           | Some gv2 => Some (gv2, t2)
           | _ => None
           end
         | _ => None
         end
| const_gep ib c1 cs2 =>
       match _const2GV TD gl c1 with
       | Some (gv1, typ_pointer t1) =>
         match getConstGEPTyp cs2 (typ_pointer t1) with
         | Some t2 => 
           match GV2ptr TD (getPointerSize TD) gv1 with
           | Some ptr =>
             match intConsts2Nats TD cs2 with
             | None => match gundef TD t2 with
                       | Some gv => Some (gv, t2)
                       | None => None
                       end
             | Some idxs => 
               match (mgep TD t1 ptr idxs) with
               | Some ptr0 => Some (ptr2GV TD ptr0, t2)
               | None => match gundef TD t2 with
                         | Some gv => Some (gv, t2)
                         | None => None
                         end
               end
             end
           | None => match gundef TD t2 with
                     | Some gv => Some (gv, t2)
                     | None => None
                     end
           end
         | _ => None
         end
       | _ => None
       end
| const_select c0 c1 c2 =>
  match _const2GV TD gl c0, _const2GV TD gl c1, _const2GV TD gl c2 with
  | Some (gv0, t0), Some gvt1, Some gvt2 => if isGVZero TD gv0 
                                            then Some gvt2
                                            else Some gvt1
  | _, _, _ => None
  end
| const_icmp cond c1 c2 =>
         match _const2GV TD gl c1, _const2GV TD gl c2 with
         | Some (gv1, t1), Some (gv2, _) => 
             match micmp TD cond t1 gv1 gv2 with
             | Some gv2 => Some (gv2, typ_int Size.One)
             | _ => None
             end
         | _, _ => None
         end
| const_fcmp cond c1 c2 =>
         match _const2GV TD gl c1, _const2GV TD gl c2 with
         | Some (gv1, typ_floatpoint fp1), Some (gv2, _) => 
           match mfcmp TD cond fp1 gv1 gv2 with
           | Some gv2 => Some (gv2, typ_int Size.One)
           | _ => None
           end
         | _, _ => None
         end
| const_extractvalue c1 cs2 =>
       match _const2GV TD gl c1 with
       | Some (gv1, t1) =>
         match getSubTypFromConstIdxs cs2 t1 with 
         | Some t2 =>
           match extractGenericValue TD t1 gv1 cs2 with
           | Some gv2 => Some (gv2, t2)
           | _ => None
           end
         | _ => None
         end
       | _ => None
       end
| const_insertvalue c1 c2 cs3 =>
         match _const2GV TD gl c1, _const2GV TD gl c2 with
         | Some (gv1, t1), Some (gv2, t2) => 
           match insertGenericValue TD t1 gv1 cs3 t2 gv2 with
           | Some gv3 => Some (gv3, t1)
           | _ => None
           end
         | _, _ => None
         end
| const_bop op c1 c2 =>
         match _const2GV TD gl c1, _const2GV TD gl c2 with
         | Some (gv1, typ_int sz1), Some (gv2, _) => 
           match mbop TD op sz1 gv1 gv2 with
           | Some gv3 => Some (gv3, typ_int sz1)
           | _ => None
           end
         | _, _ => None
         end
| const_fbop op c1 c2 =>
         match _const2GV TD gl c1, _const2GV TD gl c2 with
         | Some (gv1, typ_floatpoint fp1), Some (gv2, _) => 
           match mfbop TD op fp1 gv1 gv2 with
           | Some gv3 => Some (gv3, typ_floatpoint fp1)
           | _ => None
           end
         | _, _ => None
         end
end
with _list_const_arr2GV (TD:TargetData) (gl:GVMap) (t:typ) (cs:list_const) 
  : option GenericValue := 
match cs with
| Nil_list_const => Some nil
| Cons_list_const c lc' =>
  match (_list_const_arr2GV TD gl t lc', _const2GV TD gl c) with
  | (Some gv, Some (gv0, t0)) =>
      if typ_dec t t0 then
             match getTypeAllocSize TD t0 with
             | Some asz0 => 
                 Some ((gv++gv0)++uninits (asz0 - sizeGenericValue gv0))
             | _ => None 
             end
      else None
  | _ => None
  end
end
with _list_const_struct2GV (TD:TargetData) (gl:GVMap) (cs:list_const) 
  : option (GenericValue*list_typ) := 
match cs with
| Nil_list_const => Some (nil, Nil_list_typ)
| Cons_list_const c lc' =>
  match (_list_const_struct2GV TD gl lc', _const2GV TD gl c) with
  | (Some (gv, ts), Some (gv0,t0)) =>
       match getTypeAllocSize TD t0 with
       | Some asz => 
            Some (gv++gv0++uninits (asz - sizeGenericValue gv0), 
                  Cons_list_typ t0 ts)
       | _ => None 
       end
  | _ => None
  end
end
.

Export LLVMwf.

Scheme wf_const_ind2 := Induction for wf_const Sort Prop
  with wf_const_list_ind2 := Induction for wf_const_list Sort Prop.

Combined Scheme wf_const_mutind from wf_const_ind2, wf_const_list_ind2.

Tactic Notation "wfconst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wfconst_zero" | c "wfconst_int" | c "wfconst_floatingpoint" |
    c "wfconst_undef" | c "wfconst_null" | c "wfconst_array" |
    c "wfconst_struct" | c "wfconst_gid" | c "wfconst_trunc_int" |
    c "wfconst_trunc_fp" | c "wfconst_zext" | c "wfconst_sext" |
    c "wfconst_fpext" | c "wfconst_ptrtoint" | c "wfconst_inttoptr" |
    c "wfconst_bitcast" | c "wfconst_gep" | c "wfconst_select" |
    c "wfconst_icmp" | c "wfconst_fcmp" | c "wfconst_extractvalue" | 
    c "wfconst_insertvalue" | c "wfconst_bop" | c "wfconst_fbop" | 
    c "wfconst_nil" | c "wfconst_cons" ].

Lemma gundef__getTypeSizeInBits : forall los nts gv s t'
  (Hwft : wf_typ s t')
  (H0 : Constant.feasible_typ (los, nts) t')
  (HeqR : ret gv = gundef (los, nts) t'),
   exists sz0 : nat,
     exists al : nat,
       _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
         true t' = ret (sz0, al) /\
       Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz0) 8) = sizeGenericValue gv.
Proof.
  intros.
  unfold gundef in HeqR.
  eapply feasible_typ_inv in H0; eauto.
  destruct H0 as [sz [al [J1 [J2 J3]]]].
  unfold getTypeSizeInBits in HeqR.
  rewrite J1 in HeqR.
  inv HeqR.
  unfold getTypeSizeInBits_and_Alignment,
         getTypeSizeInBits_and_Alignment_for_namedts in J1.
  rewrite J1.
  exists sz. exists al.
  simpl. unfold size_chunk_nat, size_chunk, bytesize_chunk.
  assert (S (sz - 1) = sz) as EQ. omega.
  rewrite EQ. split; auto.
Qed.

Lemma make_list_const_spec1 : forall
  (const_list : list_const)
  (system5 : system)
  (td5 : targetdata)
  (typ5 : typ)
  (sz5 : sz)
  (lsdc : list (system * targetdata * const))
  (lt : list typ)
  (HeqR : (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const
                    (fun const_ : const => (system5, td5, const_, typ5))
                    const_list))))
  (TD : TargetData)
  (H0 : Constant.feasible_typ TD (typ_array sz5 typ5)),
  Constant.feasible_typs TD (make_list_typ lt).
Proof.
  intros.
  generalize dependent lsdc.
  generalize dependent lt.
  induction const_list; intros; simpl in *.
     inv HeqR. simpl. auto.
  
     remember (split
              (unmake_list_system_targetdata_const_typ
                 (make_list_system_targetdata_const_typ
                    (map_list_const
                       (fun const_ : const => (system5, td5, const_, typ5))
                       const_list)))) as R2.
     destruct R2. inv HeqR. simpl.
     split; eauto.
Qed.

Lemma make_list_const_spec2 : forall
  (const_list : list_const)
  (system5 : system)
  (typ5 : typ)
  (td5 : targetdata)
  (typ5 : typ)
  (sz5 : sz)
  (lsdc : list (system * targetdata * const))
  (lt : list typ)
  (HeqR : (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const
                    (fun const_ : const => (system5, td5, const_, typ5))
                    const_list))))
  (lsd : list (system*targetdata))
  (lc : list const)
  (HeqR' : (lsd, lc) = split lsdc),
  make_list_const lc = const_list.
Proof.
  induction const_list; intros; simpl in *.
    inv HeqR. simpl in HeqR'. inv HeqR'. auto.
  
    remember (split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const
                    (fun const_ : const => (system5, td5, const_, typ5))
                    const_list)))) as R1.
    destruct R1. inv HeqR. simpl in HeqR'.
    remember (split (unmake_list_system_targetdata_const_typ
                 (make_list_system_targetdata_const_typ
                    (map_list_const
                       (fun const_ : const => (system5, td5, const_, typ0))
                       const_list)))) as R2.
    destruct R2. inv H0; simpl.
    simpl in HeqR'.
    remember (split l2) as R3.
    destruct R3. inv HeqR'. simpl.
    erewrite IHconst_list; eauto.        
Qed.

Lemma length_unmake_make_list_const : forall lc,
  length (unmake_list_const (make_list_const lc)) = length lc.
Proof.
  induction lc; simpl; auto.
Qed.

Lemma map_list_const_typ_spec1 : forall system5 TD const_typ_list lsdc lt,
  (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const_typ
                    (fun (const_ : const) (typ_ : typ) =>
                     (system5, TD, const_, typ_)) const_typ_list))) ->
  lt = map_list_const_typ (fun (_ : const) (typ_ : typ) => typ_) const_typ_list.
Proof.
  induction const_typ_list; simpl; intros.
    inv H. auto.
    
    remember (split
              (unmake_list_system_targetdata_const_typ
                 (make_list_system_targetdata_const_typ
                    (map_list_const_typ
                       (fun (const_ : const) (typ_ : typ) =>
                        (system5, TD, const_, typ_))
                       const_typ_list)))) as R1. 
    destruct R1. inv H.
    erewrite <- IHconst_typ_list; eauto.
Qed.

Lemma map_list_const_typ_spec2 : forall system5 TD const_typ_list lsdc lt lc lsd,
  (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const_typ
                    (fun (const_ : const) (typ_ : typ) =>
                     (system5, TD, const_, typ_)) const_typ_list))) ->
  (lsd, lc) = split lsdc ->
  lc = map_list_const_typ (fun (const_ : const) (_ : typ) => const_) 
         const_typ_list.
Proof.
  induction const_typ_list; simpl; intros.
    inv H. inv H0. auto.
  
    remember (split
            (unmake_list_system_targetdata_const_typ
               (make_list_system_targetdata_const_typ
                  (map_list_const_typ
                     (fun (const_ : const) (typ_ : typ) =>
                      (system5, TD, const_, typ_))
                     const_typ_list)))) as R1. 
    destruct R1. inv H.
    simpl in H0.
    remember (split l0).
    destruct p. inv H0.
    erewrite <- IHconst_typ_list; eauto.
Qed.

Lemma map_list_const_typ_spec3 : forall system5 TD const_typ_list lsdc lt lc lsd
  (HeqR : (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const_typ
                    (fun (const_ : const) (typ_ : typ) =>
                     (system5, TD, const_, typ_)) const_typ_list))))
  (HeqR' : (lsd, lc) = split lsdc)
  (H1 : Constant.feasible_typs TD
         (make_list_typ
            (map_list_const_typ (fun (_ : const) (typ_ : typ) => typ_)
               const_typ_list))),
  Constant.feasible_typs TD (make_list_typ lt).
Proof.
    induction const_typ_list; simpl; intros.
      inv HeqR. simpl in HeqR'. inv HeqR'. auto.

      remember (@split (prod (prod system targetdata) const) typ
               (unmake_list_system_targetdata_const_typ
                  (make_list_system_targetdata_const_typ
                     (@map_list_const_typ
                        (prod (prod (prod system targetdata) const) typ)
                        (fun (const_ : const) (typ_ : typ) =>
                         @pair (prod (prod system targetdata) const) typ
                           (@pair (prod system targetdata) const
                              (@pair system targetdata system5 TD) const_)
                           typ_) const_typ_list)))) as R1.
      destruct R1. inv HeqR. simpl in HeqR'.
      remember (split l0) as R2.
      destruct R2. inv HeqR'.
      simpl in *. destruct H1 as [H11 H12].
      split; eauto.
Qed.

Lemma sizeGenericValue_cons_pos : forall p gv0, 
  (sizeGenericValue (p :: gv0) > 0)%nat.
Proof.
  intros. destruct p. simpl.
  assert (J:=@size_chunk_nat_pos' m).
  omega.
Qed.

Definition wf_global TD system5 gl := forall id5 typ5, 
  lookupTypViaGIDFromSystem system5 id5 = ret typ5 ->
  exists gv, exists sz, 
    lookupAL GenericValue gl id5 = Some gv /\  
    getTypeSizeInBits TD (typ_pointer typ5) = Some sz /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.

Definition wf_list_targetdata_typ (S:system) (TD:targetdata) gl lsd :=
  forall S1 TD1, In (S1,TD1) lsd -> wf_global TD S1 gl /\ S = S1 /\ TD = TD1.

Lemma const2GV_typsize_mutind_array : forall const_list system5 typ5 
  (los : list layout) (nts : list namedt) gl 
  (lsdc : list (system * targetdata * const)) lt
  (HeqR0 : (lsdc, lt) =
          split
            (unmake_list_system_targetdata_const_typ
               (make_list_system_targetdata_const_typ
                  (map_list_const
                     (fun const_ : const =>
                      (system5, (los, nts), const_, typ5)) const_list))))
  (lsd : list (system * targetdata)) lc
  (HeqR' : (lsd, lc) = split lsdc)
  ls (ld : list targetdata)
  (HeqR'' : (ls, ld) = split lsd)
  (H3 : wf_global (los, nts) system5 gl),
  wf_list_targetdata_typ system5 (los, nts) gl lsd.
Proof.
  intros.
  unfold wf_list_targetdata_typ.
  generalize dependent lsdc.
  generalize dependent lt.
  generalize dependent lc.
  generalize dependent ld.
  generalize dependent ls0.
  generalize dependent lsd.
  induction const_list; intros; simpl in *.
    inv HeqR0. inv HeqR'. inv H.
    
    remember (@split (prod (prod system targetdata) const) typ
                (unmake_list_system_targetdata_const_typ
                   (make_list_system_targetdata_const_typ
                      (@map_list_const
                         (prod
                            (prod
                               (prod system
                                  (prod (list layout) (list namedt))) const)
                            typ)
                         (fun const_ : const =>
                          @pair
                            (prod
                               (prod system
                                  (prod (list layout) (list namedt))) const)
                            typ
                            (@pair
                               (prod system
                                  (prod (list layout) (list namedt))) const
                               (@pair system
                                  (prod (list layout) (list namedt)) system5
                                  (@pair (list layout) (list namedt) los nts))
                               const_) typ5) const_list)))) as R.
    destruct R.
    inv HeqR0. simpl in HeqR'.
    remember (split l0) as R1.
    destruct R1.
    inv HeqR'. simpl in HeqR''.
    remember (split l2) as R2.
    destruct R2.
    inv HeqR''. simpl in H.
    destruct H as [H | H]; subst; eauto.
      inv H. split; auto.
Qed.

Lemma const2GV_typsize_mutind_struct : forall const_typ_list system5 los nts gl
  lsdc lt
  (HeqR : (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const_typ
                    (fun (const_ : const) (typ_ : typ) =>
                     (system5, (los, nts), const_, typ_)) const_typ_list))))
  lsd lc
  (HeqR' : (lsd, lc) = split lsdc)
  (H3 : wf_global (los, nts) system5 gl),
  wf_list_targetdata_typ system5 (los, nts) gl lsd.
Proof.
  intros.
  generalize dependent lsdc.
  generalize dependent lt.
  generalize dependent lc.
  generalize dependent lsd.
  induction const_typ_list; simpl; intros.
    inv HeqR. simpl in HeqR'. inv HeqR'.
    unfold wf_list_targetdata_typ.
    intros S TD Hin. inversion Hin.
    
    remember (split
              (unmake_list_system_targetdata_const_typ
                 (make_list_system_targetdata_const_typ
                    (map_list_const_typ
                       (fun (const_ : const) (typ_ : typ) =>
                        (system5, (los, nts), const_, typ_))
                       const_typ_list)))) as R1. 
    destruct R1. inv HeqR. simpl in HeqR'.
    remember (split l0) as R2.
    destruct R2. inv HeqR'.
    unfold wf_list_targetdata_typ in *.
    intros S TD Hin. 
    simpl in Hin.
    destruct Hin as [Hin | Hin]; eauto.
      inv Hin. split; auto.
Qed.

Lemma make_list_const_spec4 : forall
  (const_list : list_const)
  (system5 : system)
  (td5 : targetdata)
  (typ5 : typ)
  (lsdc : list (system * targetdata * const))
  (lt : list typ)
  (HeqR : (lsdc, lt) =
         split
           (unmake_list_system_targetdata_const_typ
              (make_list_system_targetdata_const_typ
                 (map_list_const
                    (fun const_ : const => (system5, td5, const_, typ5))
                    const_list))))
  t (Hin : In t lt), t = typ5.
Proof.
  intros.
  generalize dependent lsdc.
  generalize dependent lt.
  induction const_list; intros; simpl in *.
     inv HeqR. inv Hin.
  
     remember (split
              (unmake_list_system_targetdata_const_typ
                 (make_list_system_targetdata_const_typ
                    (map_list_const
                       (fun const_ : const => (system5, td5, const_, typ5))
                       const_list)))) as R2.
     destruct R2. inv HeqR.
     simpl in Hin. 
     destruct Hin; eauto.
Qed.

Lemma wf_list_targetdata_typ_cons_inv : forall S TD gl S'  TD' lsd,
  wf_list_targetdata_typ S TD gl ((S', TD') :: lsd) ->
  wf_list_targetdata_typ S TD gl lsd /\ S' = S /\ TD' = TD /\ wf_global TD S gl.
Proof.
  intros. 
  unfold wf_list_targetdata_typ in *.
  assert (In (S', TD') ((S', TD') :: lsd)) as J. simpl. auto.
  apply H in J. 
  destruct J as [J1 [J2 J3]]; subst.
  split.
    intros S1 TD1 Hin.    
    apply H. simpl. auto.
  split; auto.
Qed.

  
Ltac tinv H := try solve [inversion H].

Lemma mtrunc_typsize : forall S los nts top t1 t2 gv1 gv2,
  wf_typ S t2 ->
  Constant.feasible_typ (los, nts) t2 ->
  mtrunc (los,nts) top t1 t2 gv1 = Some gv2 ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t2 = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv2.
Proof.  
  intros. unfold mtrunc, GV2val in H1.
  destruct gv1; tinv H1.
    eapply gundef__getTypeSizeInBits; eauto.
  destruct p.
  destruct gv1; 
    try solve [inversion H1; eapply gundef__getTypeSizeInBits; eauto].
  destruct v; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct t1; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct t2; try solve [eapply gundef__getTypeSizeInBits; eauto].
      inv H1.
      simpl. exists (Size.to_nat s0).
      exists (getIntAlignmentInfo los (Size.to_nat s0) true).
      erewrite int_typsize; eauto.
  
    destruct t1; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct t2; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct (floating_point_order f1 f0); tinv H1.
    destruct f1; inv H1.
      simpl. exists 32%nat. exists (getFloatAlignmentInfo los 32 true).
      auto.
  
      simpl. exists 64%nat. exists (getFloatAlignmentInfo los 64 true).
      auto.
Qed.

Lemma mext_typsize : forall S los nts eop t1 t2 gv1 gv2,
  wf_typ S t2 ->
  Constant.feasible_typ (los, nts) t2 ->
  mext (los,nts) eop t1 t2 gv1 = Some gv2 ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t2 = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv2.
Proof.  
  intros. unfold mext, GV2val in H1.
  destruct t1; tinv H1.
    destruct t2; tinv H1.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
    destruct p.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
    destruct v; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct eop; inv H1.
      simpl. exists (Size.to_nat s0).
      exists (getIntAlignmentInfo los (Size.to_nat s0) true).
      erewrite int_typsize; eauto.

      simpl. exists (Size.to_nat s0).
      exists (getIntAlignmentInfo los (Size.to_nat s0) true).
      erewrite int_typsize; eauto.

    destruct t2; tinv H1.
    destruct (floating_point_order f f0); tinv H1.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
    destruct p.
    destruct gv1; 
      try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
    destruct v; try solve [eapply gundef__getTypeSizeInBits; eauto].
    destruct eop; inv H1.
    destruct f0; inv H3; simpl.
      exists 32%nat. exists (getFloatAlignmentInfo los 32 true). auto.
      exists 64%nat. exists (getFloatAlignmentInfo los 64 true). auto.
Qed.

Lemma mcmp_typsize_helper : forall TD gv, 
  gundef TD (typ_int 1%nat) = ret gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat Size.One) 8) = sizeGenericValue gv.
Proof.
  intros. destruct TD.
  unfold gundef in H. simpl in H. inv H. simpl. auto.
Qed.

Lemma micmp_typsize : forall los nts cond5 t1 gv1 gv2 gv,
  micmp (los,nts) cond5 t1 gv1 gv2 = Some gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat Size.One) 8) = sizeGenericValue gv.
Proof.
  intros. unfold micmp in H.
  destruct t1;
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  unfold micmp_int, GV2val in H.
  destruct gv1; 
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct p.
  destruct gv1; 
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct v; 
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct gv2; 
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct p.
  destruct gv2; 
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct v; 
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct cond5; inv H; auto.
Qed.

Lemma mfcmp_typsize : forall los nts fcond5 fp gv1 gv2 gv,
  mfcmp (los,nts) fcond5 fp gv1 gv2 = Some gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat Size.One) 8) = sizeGenericValue gv.
Proof.
  intros. unfold mfcmp, GV2val in H.
  destruct gv1; 
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct p.
  destruct gv1; 
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct v; 
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct gv2; 
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct p.
  destruct gv2; 
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct v; 
    try solve [inversion H | eapply mcmp_typsize_helper; eauto].
  destruct fp; try solve [inv H | destruct fcond5; inv H; auto].
Qed.

Lemma getSubTypFromConstIdxs__mgetoffset_aux : forall TD const_list idxs o t' 
    t1 typ' o0
  (HeqR1 : ret idxs = intConsts2Nats TD const_list)
  (HeqR2 : ret (o, t') = mgetoffset_aux TD t1 idxs o0)
  (e0 : getSubTypFromConstIdxs const_list t1 = ret typ'),
  t' = typ'.
Proof.
  induction const_list; simpl; intros.
    inv HeqR1. simpl in HeqR2. inv HeqR2. inv e0; auto.

    destruct c; tinv HeqR1.
    destruct (Size.dec s Size.ThirtyTwo); tinv HeqR1.
    remember (intConsts2Nats TD const_list) as R3.
    destruct R3; inv HeqR1.
    destruct t1; tinv e0.
      simpl in HeqR2.
      destruct (getTypeAllocSize TD t1); inv HeqR2; eauto.

      simpl in HeqR2.
      destruct (_getStructElementOffset TD l1 (Coqlib.nat_of_Z 
        (INTEGER.to_Z i0)) 0); inv HeqR2; eauto.
      unfold INTEGER.to_nat in e0.
      unfold INTEGER.to_Z in H0.
      destruct (nth_list_typ (Coqlib.nat_of_Z i0) l1); inv e0.
      simpl in H0. eauto.
Qed.

Lemma getSubTypFromConstIdxs__mgetoffset : forall TD const_list idxs o t' t1
    typ'
  (HeqR1 : ret idxs = intConsts2Nats TD const_list)
  (HeqR2 : ret (o, t') = mgetoffset TD t1 idxs)
  (e0 : getSubTypFromConstIdxs const_list t1 = ret typ'),
  t' = typ'.
Proof.
  unfold mgetoffset. intros.
  eapply getSubTypFromConstIdxs__mgetoffset_aux; eauto.
Qed.

Lemma splitGenericValue_spec0 : forall gv pos gv1 gv2,
  splitGenericValue gv pos = Some (gv1, gv2) -> pos >= 0.
Proof.
  induction gv; simpl; intros.
    destruct (Coqlib.zeq pos 0); subst.
      auto with zarith.
      destruct (Coqlib.zlt pos 0); inv H.

    destruct (Coqlib.zeq pos 0); subst.
      auto with zarith.

      destruct (Coqlib.zlt pos 0); tinv H; auto.
Qed.

Lemma splitGenericValue_spec : forall gv pos gv1 gv2,
  splitGenericValue gv pos = Some (gv1, gv2) ->
  sizeGenericValue gv1 = Coqlib.nat_of_Z pos /\ 
  (sizeGenericValue gv1 + sizeGenericValue gv2 = sizeGenericValue gv)%nat.
Proof.
  induction gv; simpl; intros.
    destruct (Coqlib.zeq pos 0); subst.
      inv H. auto.
      destruct (Coqlib.zlt pos 0); inv H.

    destruct a.
    destruct (Coqlib.zeq pos 0); subst.
      inv H. auto.

      destruct (Coqlib.zlt pos 0); tinv H.
      remember (splitGenericValue gv (pos - size_chunk m)) as R.
      destruct R as [[]|]; inv H.
      simpl. 
      symmetry in HeqR.
      assert (J:=HeqR). apply splitGenericValue_spec0 in J.
      eapply IHgv in HeqR; eauto.
      destruct HeqR as [J1 J2].
      rewrite <- J2. rewrite J1.
      assert ((size_chunk_nat m + Coqlib.nat_of_Z (pos - size_chunk m))%nat =
        Coqlib.nat_of_Z pos) as J3.
        unfold size_chunk_nat.
        assert (J0:=@size_chunk_pos m).
        rewrite <- Coqlib.nat_of_Z_plus; auto.
          assert (size_chunk m + (pos - size_chunk m) = pos) as EQ.
            ring.
          rewrite EQ. auto.

          auto with zarith.
      rewrite J3. rewrite <- plus_assoc_reverse. rewrite J3. 
      split; auto.
Qed.

Lemma mget_typsize : forall los nts gv1 o typ' gv'
  (HeqR4 : ret gv' = mget (los, nts) gv1 o typ'),
   exists sz1 : nat,
     exists al0 : nat,
       _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
         true typ' = ret (sz1, al0) /\
       Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz1) 8) = sizeGenericValue gv'.
Proof.
  intros.
  unfold mget in HeqR4.
  remember (getTypeStoreSize (los, nts) typ') as R.
  destruct R; tinv HeqR4.
  simpl in HeqR4.
  remember (splitGenericValue gv1 o) as R1.
  destruct R1 as [[? gvr]|]; tinv HeqR4.
  remember (splitGenericValue gvr (Z_of_nat n)) as R2.
  destruct R2 as [[gvrl ?]|]; inv HeqR4.
  unfold getTypeStoreSize, getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
    getTypeSizeInBits_and_Alignment_for_namedts in HeqR.
  remember (_getTypeSizeInBits_and_Alignment los
               (_getTypeSizeInBits_and_Alignment_for_namedts los 
                  (rev nts) true) true typ') as R3.
  destruct R3 as [[sz ?]|]; tinv HeqR.
  exists sz. exists n0.
  split; auto. inv HeqR.
    symmetry in HeqR2.
    apply splitGenericValue_spec in HeqR2.
    destruct HeqR2 as [J1 J2].
    rewrite J1.
    erewrite Coqlib.Z_of_nat_eq; eauto.     
Qed.

Lemma extractGenericValue_typsize : forall los nts t1 gv1 const_list typ' gv
  sz al system5
  (HeqR3 : ret gv = extractGenericValue (los, nts) t1 gv1 const_list)
  (e0 : getSubTypFromConstIdxs const_list t1 = ret typ')
  (J1 : _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
         true t1 = ret (sz, al))
  (J2 : Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv1)
  (H0 : Constant.feasible_typ (los, nts) typ')
  (w1 : wf_typ system5 typ'),
  exists sz0 : nat,
    exists al0 : nat,
        _getTypeSizeInBits_and_Alignment los
          (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
          true typ' = ret (sz0, al0) /\
        Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz0) 8) = sizeGenericValue gv.
Proof.
  intros.
  unfold extractGenericValue in HeqR3.
  remember (intConsts2Nats (los, nts) const_list) as R1.
  destruct R1 as [idxs|]; tinv HeqR3.
  remember (mgetoffset (los, nts) t1 idxs) as R2.
  destruct R2 as [[o t']|]; tinv HeqR3.
  remember (mget (los, nts) gv1 o t') as R4.
  eapply getSubTypFromConstIdxs__mgetoffset in e0; eauto.
  destruct R4 as [gv'|]; inv HeqR3.
    eapply mget_typsize; eauto.
    eapply gundef__getTypeSizeInBits; eauto.
Qed.    

Lemma mset_typsize : forall los nts gv1 o t2 gv2 gv sz2 al2
  (J3 : _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
         true t2 = ret (sz2, al2))
  (J4 : Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8) = sizeGenericValue gv2)
  (HeqR4 : ret gv = mset (los, nts) gv1 o t2 gv2),
  sizeGenericValue gv1 = sizeGenericValue gv.
Proof.
  intros.
  unfold mset in HeqR4.
  remember (getTypeStoreSize (los, nts) t2) as R.
  destruct R; tinv HeqR4.
  simpl in HeqR4.
  destruct (n =n= length gv2); tinv HeqR4.
  remember (splitGenericValue gv1 o) as R1.
  destruct R1 as [[? gvr]|]; tinv HeqR4.
  remember (splitGenericValue gvr (Z_of_nat n)) as R2.
  destruct R2 as [[gvrl ?]|]; inv HeqR4.
  symmetry in HeqR2.
  apply splitGenericValue_spec in HeqR2.
  destruct HeqR2 as [J1 J2].
  symmetry in HeqR1.
  apply splitGenericValue_spec in HeqR1.
  destruct HeqR1 as [J3' J4'].
  rewrite <- J4'. rewrite <- J2.
  rewrite sizeGenericValue__app.
  rewrite sizeGenericValue__app. 
  unfold getTypeStoreSize, getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
    getTypeSizeInBits_and_Alignment_for_namedts in HeqR.
  rewrite J3 in HeqR.
  inv HeqR.
  rewrite Coqlib.Z_of_nat_eq in J1.
  rewrite <- J1 in J4. rewrite J4. auto.
Qed.

Lemma insertGenericValue_typsize : forall los nts t1 gv1 const_list gv t2 gv2
    system5 sz al sz2 al2
  (J1 : _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
         true t1 = ret (sz, al))
  (J2 : Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv1)
  (J3 : _getTypeSizeInBits_and_Alignment los
         (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
         true t2 = ret (sz2, al2))
  (J4 : Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8) = sizeGenericValue gv2)
  (H0 : Constant.feasible_typ (los, nts) t1)
  (w1 : wf_typ system5 t1)
  (HeqR3 : ret gv = insertGenericValue (los, nts) t1 gv1 const_list t2 gv2),
  sizeGenericValue gv1 = sizeGenericValue gv.
Proof.
  intros.
  unfold insertGenericValue in HeqR3.
  remember (intConsts2Nats (los, nts) const_list) as R1.
  destruct R1 as [idxs|]; tinv HeqR3.
  remember (mgetoffset (los, nts) t1 idxs) as R2.
  destruct R2 as [[o t']|]; tinv HeqR3.
  remember (mset (los, nts) gv1 o t2 gv2) as R4.
  destruct R4 as [gv'|]; inv HeqR3.
    eapply mset_typsize in HeqR4; eauto. 

    eapply gundef__getTypeSizeInBits in H1; eauto.
    destruct H1 as [sz1 [al1 [J3' J4']]].
    rewrite J1 in J3'. inv J3'.
    rewrite <- J4'. rewrite <- J2. auto.
Qed.    

Lemma mbop_typsize_helper : forall TD system5 s gv, 
  wf_typ system5 (typ_int s) -> 
  feasible_typ TD (typ_int s) ->
  gundef TD (typ_int s) = ret gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat s) 8) = sizeGenericValue gv.
Proof.
  intros. destruct TD.
  symmetry in H1.
  eapply gundef__getTypeSizeInBits in H1; eauto.
    simpl in H1. destruct H1 as [sz0 [al [J1 J2]]]. inv J1. auto.
    inv H0. auto.
Qed.

Lemma mbop_typsize : forall system5 los nts bop5 s gv1 gv2 gv,
  wf_typ system5 (typ_int s) -> 
  feasible_typ (los, nts) (typ_int s) ->
  mbop (los,nts) bop5 s gv1 gv2 = Some gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat s) 8) = sizeGenericValue gv.
Proof.
  intros. unfold mbop, GV2val in H1.
  destruct gv1; 
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  destruct p.
  destruct gv1; 
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  destruct v; 
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  destruct gv2; 
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  destruct p.
  destruct gv2; 
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  destruct v; 
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  destruct (eq_nat_dec (wz + 1) (Size.to_nat s));
    try solve [inversion H1 | eapply mbop_typsize_helper; eauto].
  unfold Size.to_nat in e. subst.
  assert (S (Size.to_nat (wz + 1)%nat - 1) = wz + 1)%nat as EQ.
    unfold Size.to_nat. omega.
  destruct bop5; inv H1;
    try solve [simpl; unfold size_chunk_nat, size_chunk, bytesize_chunk;
               rewrite EQ; auto].
Qed.

Lemma mfbop_typsize : forall system5 los nts fbop5 f gv1 gv2 gv,
  wf_typ system5 (typ_floatpoint f) -> 
  feasible_typ (los, nts) (typ_floatpoint f) ->
  mfbop (los,nts) fbop5 f gv1 gv2 = Some gv ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true 
        (typ_floatpoint f) = Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof.
  intros. 
  inv H0.
  unfold mfbop, GV2val in H1.
  destruct gv1; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
  destruct p.
  destruct gv1; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
  destruct v; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
  destruct gv2; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
  destruct p.
  destruct gv2; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
  destruct v; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
  destruct f; 
    try solve [inversion H1 | eapply gundef__getTypeSizeInBits; eauto].
    destruct fbop5; inv H1; simpl; eauto.
    destruct fbop5; inv H1; simpl; eauto.
Qed.

Definition const2GV__getTypeSizeInBits_Prop S TD c t (H:wf_const S TD c t) := 
  forall los nts gl gv t',
  TD = (los, nts) ->
  Constant.feasible_typ TD t ->
  _const2GV (los,nts) gl c = Some (gv, t') ->
  wf_global TD S gl ->
  t = t' /\
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.

Definition consts2GV__getTypeSizeInBits_Prop sdct (H:wf_const_list sdct) := 
  let 'lsdct := unmake_list_system_targetdata_const_typ sdct in
  let '(lsdc, lt) := split lsdct in
  let '(lsd, lc) := split lsdc in
  let '(ls, ld) := split lsd in
  forall S TD los nts gl, 
  TD = (los, nts) ->
  wf_list_targetdata_typ S TD gl lsd ->
  (forall gv t, 
    Constant.feasible_typ TD t ->
    (forall t0, In t0 lt -> t0 = t) ->
   _list_const_arr2GV TD gl t (make_list_const lc) = Some gv ->
   exists sz, 
    getTypeAllocSize TD t = Some sz /\
    (sz * length lc)%nat = sizeGenericValue gv) /\
  (forall gv lt', 
    Constant.feasible_typs TD (make_list_typ lt) ->
   _list_const_struct2GV TD gl (make_list_const lc) = Some (gv, lt') ->
   lt' = make_list_typ lt /\
   exists sz, exists al,
    _getListTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) lt' = 
        Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv).

Lemma const2GV_typsize_mutind : 
  (forall S td c t H, @const2GV__getTypeSizeInBits_Prop S td c t H) /\
  (forall sdct H, @consts2GV__getTypeSizeInBits_Prop sdct H).
Proof.
  (wfconst_cases (apply wf_const_mutind; 
                    unfold const2GV__getTypeSizeInBits_Prop, 
                           consts2GV__getTypeSizeInBits_Prop) Case);
    intros; subst; simpl in *.
Case "wfconst_zero".
  remember (zeroconst2GV (los, nts) typ5) as R.
  destruct R; inv H1.
  split; auto.
    eapply zeroconst2GV__getTypeSizeInBits; eauto.

Case "wfconst_int".
  inv H1.
  split; auto.
  exists (Size.to_nat sz5). 
  exists (getIntAlignmentInfo los (Size.to_nat sz5) true).
  erewrite int_typsize; eauto.

Case "wfconst_floatingpoint".
  destruct floating_point5; inv H1; 
    simpl; unfold size_chunk_nat, size_chunk, bytesize_chunk; split; auto.
    exists 32%nat. exists (getFloatAlignmentInfo los 32 true).
    simpl. auto.

    exists 64%nat. exists (getFloatAlignmentInfo los 64 true).
    simpl. auto.

Case "wfconst_undef".
  remember (gundef (los, nts) typ5) as R.
  destruct R; inv H1.
  split; eauto using gundef__getTypeSizeInBits.

Case "wfconst_null".
  inv H1. simpl.
  split; auto.
    exists (Size.to_nat (getPointerSizeInBits los)).
    exists (getPointerAlignmentInfo los true).
    unfold getPointerSizeInBits. simpl. auto.

Case "wfconst_array". Focus.
  remember (_list_const_arr2GV (los, nts) gl typ5 const_list) as R.
  destruct R; inv H2.
  remember (@split (prod (prod system targetdata) const) typ
          (unmake_list_system_targetdata_const_typ
             (make_list_system_targetdata_const_typ
                (@map_list_const
                   (prod (prod (prod system targetdata) const) typ)
                   (fun const_ : const =>
                    @pair (prod (prod system targetdata) const) typ
                      (@pair (prod system targetdata) const
                         (@pair system targetdata system5
                            (@pair (list layout) (list namedt) los nts))
                         const_) typ5) const_list)))) as R.
  destruct R as [lsdc lt]. 
  remember (split lsdc) as R'.
  destruct R' as [lsd lc].
  remember (split lsd) as R''.
  destruct R'' as [ls ld].
  rewrite e in H4. unfold Size.to_nat in *.
  destruct sz5; inv H4.
    split; auto.
    exists 8%nat. exists 1%nat. 
    split; auto.

    split; auto.
    destruct (@H system5 (los,nts) los nts gl) as [J1 J2]; 
      eauto using const2GV_typsize_mutind_array.
    symmetry in HeqR.
    assert (make_list_const lc = const_list) as EQ.
      eapply make_list_const_spec2; eauto.
    rewrite <- EQ in HeqR.
    apply J1 in HeqR; eauto using make_list_const_spec4.
    destruct HeqR as [sz [J3 J4]].
    apply getTypeAllocSize_inv in J3.
    destruct J3 as [sz0 [al0 [J31 [J32 J33]]]]; subst.
    unfold getTypeSizeInBits_and_Alignment in J32.
    unfold getTypeSizeInBits_and_Alignment_for_namedts in J32.
    rewrite J32.
    rewrite <- J4.        
    exists (RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz0) 8)) al0 * 8 *
             S sz5)%nat. exists al0.
    rewrite length_unmake_make_list_const in e. rewrite e.
    split; auto.
      rewrite ZRdiv_prop6. auto.

Unfocus.

Case "wfconst_struct". Focus.
  remember (@split (prod (prod system targetdata) const) typ
          (unmake_list_system_targetdata_const_typ
             (make_list_system_targetdata_const_typ
                (@map_list_const_typ
                   (prod (prod (prod system targetdata) const) typ)
                   (fun (const_ : const) (typ_ : typ) =>
                    @pair (prod (prod system targetdata) const) typ
                      (@pair (prod system targetdata) const
                         (@pair system targetdata system5
                            (@pair (list layout) (list namedt) los nts))
                         const_) typ_) const_typ_list)))) as R.
  destruct R as [lsdc lt]. 
  remember (split lsdc) as R'.
  destruct R' as [lsd lc].
  remember (split lsd) as R''.
  destruct R'' as [ls ld].
  remember (_list_const_struct2GV (los, nts) gl
           (make_list_const
              (map_list_const_typ (fun (const_ : const) (_ : typ) => const_)
                 const_typ_list))) as R1.
  destruct R1 as [[gv0 ts]|]; inv H2.
  destruct (@H system5 (los,nts) los nts gl) as [J1 J2]; 
    eauto using const2GV_typsize_mutind_struct.

  symmetry in HeqR1.
  erewrite <- map_list_const_typ_spec2 in HeqR1; eauto.
  apply J2 in HeqR1; eauto using map_list_const_typ_spec3. clear J1 J2 H.
  destruct HeqR1 as [J5 [sz [al [J6 J7]]]]; subst.
  destruct gv0; inv H4.
    erewrite <- map_list_const_typ_spec1; eauto.
    rewrite J6.
    split; auto.
      destruct sz.
        exists 8%nat. exists 1%nat. auto.

        assert (Coqlib.ZRdiv (Z_of_nat (S sz0)) 8 > 0) as J.
          apply Coqlib.ZRdiv_prop3; auto using Coqlib.Z_of_S_gt_O; omega.
        apply nat_of_Z_inj_gt in J; try omega. simpl in J, J7.
        rewrite J7 in J. contradict J. omega.

    erewrite <- map_list_const_typ_spec1; eauto.
    rewrite J6.
    rewrite <- J7.
    split; auto.
      destruct sz.
        clear - J7.
        assert (J := @sizeGenericValue_cons_pos p gv0).
        rewrite <- J7 in J. contradict J; simpl; omega.

        eauto.
Unfocus.

Case "wfconst_gid".
  remember (lookupAL GenericValue gl id5) as R.
  destruct R; inv H1.
  split; auto.
    apply H2 in e.
    destruct e as [gv0 [sz [J1 [J2 J3]]]].
    rewrite J1 in HeqR. inv HeqR.
    unfold getTypeSizeInBits in J2. simpl in J2.
    inv J2.
    rewrite <- J3. eauto.

Case "wfconst_trunc_int". Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  remember (mtrunc (los, nts) truncop_int t (typ_int sz2) g) as R.
  destruct R; inv H4.
  split; auto.
   symmetry in HeqR.
   eapply mtrunc_typsize in HeqR; eauto.
Unfocus.

Case "wfconst_trunc_fp". Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  remember (mtrunc (los, nts) truncop_int t (typ_floatpoint floating_point2) g) 
    as R.
  destruct R; inv H4.
  split; auto.
   symmetry in HeqR.
   eapply mtrunc_typsize in HeqR; eauto.
Unfocus.

Case "wfconst_zext". Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  remember (mext (los, nts) extop_z t (typ_int sz2) g) as R.
  destruct R; inv H4.
  split; auto.
    symmetry in HeqR.
    eapply mext_typsize in HeqR; eauto.
Unfocus.

Case "wfconst_sext".  Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  remember (mext (los, nts) extop_s t (typ_int sz2) g) as R.
  destruct R; inv H4.
  split; auto.
    symmetry in HeqR.
    eapply mext_typsize in HeqR; eauto.
Unfocus.

Case "wfconst_fpext".  Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  remember (mext (los, nts) extop_fp t (typ_floatpoint floating_point2) g) as R.
  destruct R; inv H4.
  split; auto.
    symmetry in HeqR.
    eapply mext_typsize in HeqR; eauto.
Unfocus.

Case "wfconst_ptrtoint". Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  simpl.
  split; auto.
    exists (Size.to_nat sz5).
    exists (getIntAlignmentInfo los (Size.to_nat sz5) true).
    erewrite int_typsize; eauto.
Unfocus.

Case "wfconst_inttoptr". Focus.
  destruct (_const2GV (los, nts) gl const5) as [[]|]; inv H2.
  split; auto.
    exists (Size.to_nat (getPointerSizeInBits los)).
    exists (getPointerAlignmentInfo los true).
    simpl. auto.
Unfocus.

Case "wfconst_bitcast". Focus.
  remember (_const2GV (los, nts) gl const5) as R1.
  destruct R1 as [[]|]; inv H2.
  remember (mbitcast t g (typ_pointer typ2)) as R.
  destruct R; inv H4.
  unfold mbitcast in HeqR.
  destruct t; inv HeqR.
  eapply H in H1; eauto.
  destruct H1; eauto.
Unfocus.

Case "wfconst_gep". Focus.
  inv f.
  remember (_const2GV (los, nts) gl const_5) as R1.
  destruct R1 as [[]|]; tinv H3.
  destruct t; tinv H3.
  symmetry in HeqR1.
  eapply H in HeqR1; eauto.
  destruct HeqR1 as [Heq [sz [al [J1 J2]]]].
  inv J1. inv Heq.
  rewrite e0 in H3.
  assert(
    match gundef (los, nts) typ' with
       | ret gv => ret (gv, typ')
       | merror => merror
       end = ret (gv, t') ->
    typ' = t' /\
    (exists sz0 : nat,
      exists al : nat,
        _getTypeSizeInBits_and_Alignment los
          (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
          true typ' = ret (sz0, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz0) 8) = sizeGenericValue gv)) as G.
    intros W3.
    remember (gundef (los, nts) typ') as R3;
    destruct R3; inv W3;
    split; try solve 
      [auto | eapply gundef__getTypeSizeInBits with (s:=system5); eauto].
  remember (GV2ptr (los, nts) (getPointerSize0 los) g) as R.
  destruct R; auto.
    remember (intConsts2Nats (los, nts) const_list) as R2.
    destruct R2; auto.
      remember (mgep (los, nts) t v l0) as R3.
      destruct R3; auto.
        inv H3.
        split; auto.  
          unfold getConstGEPTyp in e0.
          destruct const_list; tinv e0.  
          remember (getSubTypFromConstIdxs const_list t) as R4.
          destruct R4; inv e0. 
          simpl.
          exists (Size.to_nat (getPointerSizeInBits los)).
          exists (getPointerAlignmentInfo los true).
          auto.

Unfocus.

Case "wfconst_select". Focus.
  remember (_const2GV (los, nts) gl const0) as R0.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R0 as [[gv0 t0]|]; tinv H4.
  destruct R1 as [[gv1 t1]|]; tinv H4.
  destruct R2 as [[gv2 t2]|]; tinv H4.
  destruct (isGVZero (los, nts) gv0); inv H4; eauto.
Unfocus.

Case "wfconst_icmp". Focus.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H3.
  destruct R2 as [[gv2 t2]|]; tinv H3.
  remember (micmp (los, nts) cond5 t1 gv1 gv2) as R3.
  destruct R3; inv H3; eauto.
  split; auto.
    symmetry in HeqR3.
    eapply micmp_typsize in HeqR3; eauto.
Unfocus.

Case "wfconst_fcmp". Focus.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H3.
  destruct t1; tinv H3.
  destruct R2 as [[gv2 t2]|]; tinv H3.
  remember (mfcmp (los, nts) fcond5 f1 gv1 gv2) as R3.
  destruct R3; inv H3; eauto.
  split; auto.
    symmetry in HeqR3.
    eapply mfcmp_typsize in HeqR3; eauto.
Unfocus.

Case "wfconst_extractvalue". Focus.
  remember (_const2GV (los, nts) gl const_5) as R1.
  destruct R1 as [[gv1 t1]|]; tinv H3.
  remember (getSubTypFromConstIdxs const_list t1) as R2.
  destruct R2 as [t2|]; tinv H3.
  remember (extractGenericValue (los, nts) t1 gv1 const_list) as R3.
  destruct R3 as [gv2|]; inv H3.
  clear H0.
  symmetry in HeqR1.
  inv f.
  apply H in HeqR1; auto.
  destruct HeqR1 as [Heq [sz [al [J1 J2]]]]; subst.
  destruct e0 as [idxs [o [J3 J4]]].
  symmetry in J3.
  eapply getSubTypFromConstIdxs__mgetoffset in J3; eauto.
  subst.
  split; eauto using extractGenericValue_typsize.
Unfocus.

Case "wfconst_insertvalue". Focus.
  clear H1.
  remember (_const2GV (los, nts) gl const_5) as R1.
  destruct R1 as [[gv1 t1]|]; tinv H4.
  remember (_const2GV (los, nts) gl const') as R2.
  destruct R2 as [[gv2 t2]|]; tinv H4.
  remember (insertGenericValue (los, nts) t1 gv1 const_list t2 gv2) as R3.
  destruct R3 as [gv3|]; inv H4.
  symmetry in HeqR1.
  apply H in HeqR1; auto.
  destruct HeqR1 as [Heq [sz [al [J1 J2]]]]; subst.
  rewrite J1. 
  symmetry in HeqR2.
  inv f.
  apply H0 in HeqR2; auto.
  destruct HeqR2 as [Heq [sz2 [al2 [J3 J4]]]]; subst.
  split; auto.
    exists sz. exists al.
    split; auto.
      eapply insertGenericValue_typsize in HeqR3; eauto.
      rewrite <- HeqR3. auto.
Unfocus.

Case "wfconst_bop". Focus.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H3.
  destruct t1; tinv H3.
  destruct R2 as [[gv2 t2]|]; tinv H3.
  remember (mbop (los, nts) bop5 s gv1 gv2) as R3.
  destruct R3; inv H3; eauto.
  symmetry in HeqR1.
  eapply H in HeqR1; eauto.
  destruct HeqR1 as [Heq _]. inv Heq.
  split; auto.
    symmetry in HeqR3.
    eapply mbop_typsize in HeqR3; eauto.
      apply feasible_typ_intro; auto.
Unfocus.

Case "wfconst_fbop". Focus.
  remember (_const2GV (los, nts) gl const1) as R1.
  remember (_const2GV (los, nts) gl const2) as R2.
  destruct R1 as [[gv1 t1]|]; tinv H3.
  destruct t1; tinv H3.
  destruct R2 as [[gv2 t2]|]; tinv H3.
  remember (mfbop (los, nts) fbop5 f gv1 gv2) as R3.
  destruct R3; inv H3; eauto.
  symmetry in HeqR1.
  eapply H in HeqR1; eauto.
  destruct HeqR1 as [Heq _]. inv Heq.
  split; auto.
    symmetry in HeqR3.
    eapply mfbop_typsize in HeqR3; eauto.
      apply feasible_typ_intro; auto.
Unfocus.

Case "wfconst_nil".
  intros; subst.

  split; intros; subst.
    inv H2. 
    apply feasible_typ_inv' in H.
    destruct H as [sz [al [H H']]].
    unfold getTypeAllocSize. unfold getTypeStoreSize. unfold getTypeSizeInBits.
    unfold getABITypeAlignment. unfold getAlignment.
    rewrite H. simpl. eauto.

    inv H1. simpl.
    split; eauto.    

Case "wfconst_cons".
  remember (split (unmake_list_system_targetdata_const_typ l')) as R1.
  destruct R1 as [lsdc lt].
  simpl.  
  remember (split lsdc) as R2.
  destruct R2 as [lsd lc].
  simpl.  
  remember (split lsd) as R3.
  destruct R3 as [ls ld].
  simpl.
  intros S TD los nts gl EQ Hwfl; subst.
  split.
    intros gv t Hft Hin Hc2g.
    remember (_list_const_arr2GV (los, nts) gl t (make_list_const lc)) as R.
    destruct R; try solve [inv Hc2g].
    remember (_const2GV (los, nts) gl const_) as R'.
    destruct R' as [[gv0 t0]|]; try solve [inv Hc2g].
    destruct (typ_dec t t0); subst; try solve [inv Hc2g].
    remember (getTypeAllocSize (los, nts) t0) as R1.
    destruct R1; inv Hc2g.
    assert (typ5 = t0) as EQ. eapply Hin; eauto.
    subst.
    exists s. split; auto.
    apply wf_list_targetdata_typ_cons_inv in Hwfl.
    destruct Hwfl as [J1 [J2 [J3 J4]]]; subst.
    symmetry in HeqR'.
    apply H in HeqR'; auto.
    destruct HeqR' as [Heq [sz [al [J5 J6]]]]; subst.
    eapply H0 in J1; eauto. destruct J1 as [J1 _]. clear H H0.
    symmetry in HeqR.
    apply J1 in HeqR; auto.
    destruct HeqR as [sz0 [J7 J8]].
    simpl_env.
    rewrite sizeGenericValue__app.
    rewrite sizeGenericValue__app.
    rewrite sizeGenericValue__uninits.
    rewrite <- J8. rewrite <- J6.
    rewrite J7 in HeqR0. inv HeqR0.
    erewrite getTypeAllocSize_roundup; eauto.

    intros gv lt' [J1 J2] Hc2g.
    remember (_list_const_struct2GV (los, nts) gl (make_list_const lc)) as R.
    destruct R as [[gv1 ts1]|]; try solve [inv Hc2g].
    remember (_const2GV (los, nts) gl const_) as R'.
    destruct R' as [[gv0 t0]|]; try solve [inv Hc2g].
    remember (getTypeAllocSize (los, nts) t0) as R1.
    destruct R1; inv Hc2g.
    apply wf_list_targetdata_typ_cons_inv in Hwfl.
    destruct Hwfl as [J1' [J2' [J3 J4]]]; subst.
    symmetry in HeqR'.
    apply H in HeqR'; auto.
    destruct HeqR' as [Heq [sz [al [J5 J6]]]]; subst.
    eapply H0 in J1'; eauto. destruct J1' as [_ J1']. clear H H0.
    symmetry in HeqR.
    apply J1' in HeqR; auto.
    destruct HeqR as [Heq [sz0 [al0 [J7 J8]]]]; subst.
    split; auto.
    rewrite sizeGenericValue__app.
    rewrite sizeGenericValue__app.
    rewrite sizeGenericValue__uninits.
    rewrite <- J8. rewrite <- J6. simpl. rewrite J7. rewrite J5.
    erewrite getTypeAllocSize_roundup; eauto.
    exists (sz0 +
             RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) al * 8)%nat.
    exists (if le_lt_dec al al0 then al0 else al).
    split; auto.
      eapply getTypeAllocSize_inv' in J5; eauto. subst.
      apply ZRdiv_prop7.
Qed.

Lemma const2GV__getTypeSizeInBits_aux : forall S los nts c t gl gv t',
  wf_const S (los, nts) c t ->
  Constant.feasible_typ (los, nts) t ->
  _const2GV (los,nts) gl c = Some (gv, t') ->
  wf_global (los, nts) S gl ->
  t = t' /\
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof.
  intros.
  destruct const2GV_typsize_mutind.
  eapply H3; eauto.
Qed.

Definition cundef_gv gv t : GenericValue :=
match t with
| typ_int sz => (Vint sz (Int.zero sz), Mint (sz -1))::nil
| typ_floatpoint fp_float => (Vfloat Float.zero, Mfloat32)::nil
| typ_floatpoint fp_double => (Vfloat Float.zero, Mfloat64)::nil
| typ_pointer _ => null
| _ => gv
end.

Lemma cundef_gv__getTypeSizeInBits : forall S los nts gv t sz al,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = 
    sizeGenericValue (cundef_gv gv t).
Proof.
  intros.
  destruct t; simpl in *; auto.
    inv H0.
    erewrite int_typsize; eauto.

    destruct f; tinv H; inv H0; auto.

    inv H0. auto.
Qed.

Definition cgv2gv (gv:GenericValue) (t:typ) : GenericValue :=
match gv with
| (Vundef, _)::nil => cundef_gv gv t
| _ => gv
end.

Lemma cgv2gv__getTypeSizeInBits : forall S los nts gv t sz al,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = 
    sizeGenericValue (cgv2gv gv t).
Proof.
  intros.
  destruct gv; auto.
  destruct p.
  destruct v; auto.
  destruct gv; auto.
  simpl. eapply cundef_gv__getTypeSizeInBits; eauto.
Qed.

Notation "? gv # t ?" := (cgv2gv gv t) (at level 41).

Definition const2GV (TD:TargetData) (gl:GVMap) (c:const) : option GenericValue :=
match (_const2GV TD gl c) with
| None => None
| Some (gv, t) => Some (? gv # t ?)
end.

Lemma const2GV__getTypeSizeInBits : forall S TD c t gl gv,
  wf_typ S t ->
  wf_const S TD c t ->
  Constant.feasible_typ TD t ->
  const2GV TD gl c = Some gv ->
  wf_global TD S gl ->
  exists sz, 
    getTypeSizeInBits TD t = Some sz /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof.
  intros.
  unfold const2GV in H2.
  remember (_const2GV TD gl c) as R.
  destruct R as [[]|]; inv H2.
  symmetry in HeqR.
  destruct TD.
  unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment.
  eapply const2GV__getTypeSizeInBits_aux in HeqR; eauto.
  destruct HeqR as [Heq [sz [al [J1 J2]]]]; subst.
  exists sz. 
  rewrite J1.
  split; auto.
    eapply cgv2gv__getTypeSizeInBits; eauto.
Qed.

Definition getOperandValue (TD:TargetData) (v:value) (locals:GVMap) 
  (globals:GVMap) : option GenericValue := 
match v with
| value_id id => lookupAL _ locals id 
| value_const c => const2GV TD globals c
end.

Definition getOperandInt (TD:TargetData) (bsz:sz) (v:value) (locals:GVMap) 
  (globals:GVMap) : option Z := 
match (getOperandValue TD v locals globals) with
| Some gi => GV2int TD bsz gi
| None => None
end.

Definition getOperandPtr (TD:TargetData) (v:value) (locals:GVMap) 
  (globals:GVMap) : option val := 
match (getOperandValue TD v locals globals) with
| Some gi => GV2ptr TD (getPointerSize TD) gi
| None => None
end.

Definition getOperandPtrInBits (TD:TargetData) (s:sz) (v:value) (locals:GVMap) 
  (globals:GVMap) : option val := 
match (getOperandValue TD v locals globals) with
| Some gi => GV2ptr TD s gi
| None => None
end.

Definition isOperandUndef (TD:TargetData) (t:typ) (v:value) (locals:GVMap) 
  (globals:GVMap) : Prop  := 
match (getOperandValue TD v locals globals) with
| Some gi => isGVUndef gi
| None => False
end.

(**************************************)
(* conversion between different lists *)

Fixpoint params2GVs (TD:TargetData) (lp:params) (locals:GVMap) 
  (globals:GVMap) : option (list GenericValue) :=
match lp with
| nil => Some nil
| (_, v)::lp' => 
    match (getOperandValue TD v locals globals, 
          params2GVs TD lp' locals globals) with
    | (Some gv, Some gvs) => Some (gv::gvs)
    | _ => None
    end
end.

Fixpoint values2GVs (TD:TargetData) (lv:list_value) (locals:GVMap) 
  (globals:GVMap) : option (list GenericValue):=
match lv with
| Nil_list_value => Some nil
| Cons_list_value v lv' => 
  match (getOperandValue TD v locals globals) with
  | Some GV => 
    match (values2GVs TD lv' locals globals) with
    | Some GVs => Some (GV::GVs)
    | None => None
    end
  | None => None
  end
end.

Fixpoint intValues2Nats (TD:TargetData) (lv:list_value) (locals:GVMap)
  (globals:GVMap) : option (list Z):=
match lv with
| Nil_list_value => Some nil
| Cons_list_value v lv' => 
  match (getOperandValue TD v locals globals) with
  | Some GV => 
    match (GV2int TD Size.ThirtyTwo GV) with
    | Some z =>
        match (intValues2Nats TD lv' locals globals) with
        | Some ns => Some (z::ns)
        | None => None
        end
    | _ => None
    end
  | None => None
  end
end.

(**************************************)
(* helper functions *)

Definition fit_gv TD (t:typ) (gv:GenericValue) : option GenericValue :=
match (getTypeSizeInBits TD t) with
| Some sz => 
    if beq_nat (sizeGenericValue gv) 
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8))
    then Some gv
    else gundef TD t
| None => None
end.

Lemma fit_gv__getTypeSizeInBits : forall TD gv s t gv'
  (Hwft : wf_typ s t)
  (H0 : Constant.feasible_typ TD t)
  (HeqR : ret gv' = fit_gv TD t gv),
  exists sz, 
    getTypeSizeInBits TD t = Some sz /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv'.
Proof.
  intros.
  unfold fit_gv in HeqR.
  assert (J:=H0).
  eapply feasible_typ_inv in H0; eauto.
  destruct H0 as [sz [al [J1 [J2 J3]]]].
  unfold getTypeSizeInBits in *.
  exists sz.
  rewrite J1 in HeqR. rewrite J1.
  split; auto.
    remember (sizeGenericValue gv =n= 
                Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8))
      as R.
    destruct R.
      inv HeqR.
      apply beq_nat_eq in HeqR0; auto.

      destruct TD.
      eapply gundef__getTypeSizeInBits in J; eauto.
      destruct J as [sz0 [al0 [J4 J5]]].
      unfold getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts in J1.
      rewrite J1 in J4.
      inv J4. auto.
Qed.

Fixpoint _initializeFrameValues TD (la:args) (lg:list GenericValue) 
  (locals:GVMap) : option GVMap :=
match (la, lg) with
| (((t, _), id)::la', g::lg') => 
  match _initializeFrameValues TD la' lg' locals, fit_gv TD t g with
  | Some lc', Some gv => Some (updateAddAL _ lc' id (? gv # t ?))
  | _, _ => None
  end
| (((t, _), id)::la', nil) => 
  (* FIXME: We should initalize them w.r.t their type size. *)
  match _initializeFrameValues TD la' nil locals, gundef TD t with
  | Some lc', Some gv => Some (updateAddAL _ lc' id (? gv # t ?))
  | _, _ => None
  end
| _ => Some locals
end.

Definition initLocals TD (la:args) (lg:list GenericValue): option GVMap := 
_initializeFrameValues TD la lg nil.

Definition BOP (TD:TargetData) (lc gl:GVMap) (op:bop) (bsz:sz) 
  (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => mbop TD op bsz gv1 gv2
| _ => None
end
.

Definition FBOP (TD:TargetData) (lc gl:GVMap) (op:fbop) 
  (fp:floating_point) (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => mfbop TD op fp gv1 gv2
| _ => None
end
.

Definition TRUNC (TD:TargetData) (lc gl:GVMap) (op:truncop) (t1:typ) 
  (v1:value) (t2:typ) : option GenericValue :=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mtrunc TD op t1 t2 gv1
| _ => None
end
.

Definition CAST (TD:TargetData) (lc gl:GVMap) (op:castop) (t1:typ) 
  (v1:value) (t2:typ) : option GenericValue:=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mcast TD op t1 t2 gv1
| _ => None
end
.

Definition EXT (TD:TargetData) (lc gl:GVMap) (op:extop) (t1:typ) 
  (v1:value) (t2:typ) : option GenericValue :=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mext TD op t1 t2 gv1
| _ => None
end
.

Definition ICMP (TD:TargetData) (lc gl:GVMap) (c:cond) (t:typ) 
  (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => micmp TD c t gv1 gv2
| _ => None
end.

Definition FCMP (TD:TargetData) (lc gl:GVMap) (c:fcond) 
  (fp:floating_point) (v1 v2:value) : option GenericValue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => mfcmp TD c fp gv1 gv2
| _ => None
end.

Definition GEP (TD:TargetData) (t:typ) (ma:GenericValue) 
  (vidxs:list GenericValue) (inbounds:bool) : option GenericValue :=
match GV2ptr TD (getPointerSize TD) ma with
| Some ptr =>
  match GVs2Nats TD vidxs with
  | None => gundef TD (typ_pointer (typ_int 1%nat))
  | Some idxs => 
    match (mgep TD t ptr idxs) with
    | Some ptr0 => Some (ptr2GV TD ptr0)
    | None => gundef TD (typ_pointer (typ_int 1%nat))
    end
  end
| None => gundef TD (typ_pointer (typ_int 1%nat))
end.

Lemma BOP_inversion : forall TD lc gl b s v1 v2 gv,
  BOP TD lc gl b s v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    mbop TD b s gv1 gv2 = Some gv.
Proof.
  intros TD lc gl b s v1 v2 gv HBOP.
  unfold BOP in HBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HBOP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HBOP].
      remember (mbop TD b s g g0) as R.
      destruct R; inversion HBOP; subst.
        exists g. exists g0. auto.
Qed.

Lemma FBOP_inversion : forall TD lc gl b fp v1 v2 gv,
  FBOP TD lc gl b fp v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    mfbop TD b fp gv1 gv2 = Some gv.
Proof.
  intros TD lc gl b fp v1 v2 gv HFBOP.
  unfold FBOP in HFBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HFBOP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HFBOP].
      remember (mfbop TD b fp g g0) as R.
      destruct R; inversion HFBOP; subst.
        exists g. exists g0. auto.
Qed.

Lemma getOperandPtr_inversion : forall TD lc gl v mptr,
  getOperandPtr TD v lc gl = Some mptr ->
  exists gv,
    getOperandValue TD v lc gl = Some gv /\
    GV2ptr TD (getPointerSize TD) gv = Some mptr.
Proof.
  intros TD lc gl v mptr HgetOperandPtr.
  unfold getOperandPtr in HgetOperandPtr.
  remember (getOperandValue TD v lc gl) as ogv.
  destruct ogv; try solve [inversion HgetOperandPtr].
    exists g. auto.
Qed.

Lemma getOperandInt_inversion : forall TD sz lc gl v n,
  getOperandInt TD sz v lc gl = Some n ->
  exists gv,
    getOperandValue TD v lc gl = Some gv /\
    GV2int TD sz gv = Some n.
Proof.
  intros TD sz0 lc gl v mptr HgetOperandInt.
  unfold getOperandInt in HgetOperandInt.
  remember (getOperandValue TD v lc gl) as ogv.
  destruct ogv; try solve [inversion HgetOperandInt].
    exists g. auto.
Qed.

Lemma CAST_inversion : forall TD lc gl op t1 v1 t2 gv,
  CAST TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mcast TD op t1 t2 gv1 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HCAST.
  unfold CAST in HCAST.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HCAST].
    remember (mcast TD op t1 t2 g) as R.
    destruct R; inversion HCAST; subst.
      exists g. auto.
Qed.

Lemma TRUNC_inversion : forall TD lc gl op t1 v1 t2 gv,
  TRUNC TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mtrunc TD op t1 t2 gv1 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HTRUNC.
  unfold TRUNC in HTRUNC.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HTRUNC].
    remember (mtrunc TD op t1 t2 g) as R.
    destruct R; inversion HTRUNC; subst.
      exists g. auto.
Qed.

Lemma EXT_inversion : forall TD lc gl op t1 v1 t2 gv,
  EXT TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mext TD op t1 t2 gv1 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HEXT.
  unfold EXT in HEXT.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HEXT].
    remember (mext TD op t1 t2 g) as R.
    destruct R; inversion HEXT; subst.
      exists g. auto.
Qed.

Lemma ICMP_inversion : forall TD lc gl cond t v1 v2 gv,
  ICMP TD lc gl cond t v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    micmp TD cond t gv1 gv2 = Some gv.
Proof.
  intros TD lc gl cond0 t v1 v2 gv HICMP.
  unfold ICMP in HICMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HICMP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HICMP].
      remember (micmp TD cond0 t g g0) as R.
      destruct R; inversion HICMP; subst.
        exists g. exists g0. auto.
Qed.

Lemma FCMP_inversion : forall TD lc gl cond fp v1 v2 gv,
  FCMP TD lc gl cond fp v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    mfcmp TD cond fp gv1 gv2 = Some gv.
Proof.
  intros TD lc gl cond0 fp v1 v2 gv HFCMP.
  unfold FCMP in HFCMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HFCMP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HFCMP].
      remember (mfcmp TD cond0 fp g g0) as R.
      destruct R; inversion HFCMP; subst.
        exists g. exists g0. auto.
Qed.

(*
Lemma GEP_inversion : forall (TD:TargetData) (t:typ) (ma:GenericValue) 
  (vidxs:list GenericValue) ib mptr0,
  GEP TD t ma vidxs ib = Some mptr0 ->
  exists idxs, exists ptr, exists ptr0, 
    GVs2Nats TD vidxs = Some idxs /\ 
    GV2ptr TD (getPointerSize TD) ma = Some ptr /\
    mgep TD t ptr idxs = Some ptr0 /\
    ptr2GV TD ptr0 = mptr0.
Proof.
  intros.
  unfold GEP in H.
  remember (GVs2Nats TD vidxs) as oidxs.
  remember (GV2ptr TD (getPointerSize TD) ma) as R.
  destruct R.
    destruct oidxs.
      remember (mgep TD t v l0) as og.
      destruct og; inversion H; subst.
        exists l0. exists v. exists v0. auto.
        exists l0. exists v. exists v0. auto.

Qed.
*)

Lemma intValues2Nats_inversion : forall l0 lc gl TD ns0,
  intValues2Nats TD l0 lc gl = Some ns0 ->
  exists gvs0, 
    values2GVs TD l0 lc gl = Some gvs0 /\
    GVs2Nats TD gvs0 = Some ns0.
Proof.
  induction l0; intros; simpl in *.
    inversion H. exists nil. auto.

    remember (getOperandValue TD v lc gl) as ogv.
    destruct ogv; try solve [inversion H].
    remember (GV2int TD Size.ThirtyTwo g) as on.
    destruct on; try solve [inversion H].
    remember (intValues2Nats TD l0 lc gl) as ons.
    destruct ons; inversion H; subst.
    symmetry in Heqons.
    apply IHl0 in Heqons.
    destruct Heqons as [gvs [J1 J2]].
    exists (g::gvs).
    rewrite J1. 
    split; auto.
      simpl. rewrite J2. rewrite <- Heqon. auto.
Qed.

Lemma values2GVs_GVs2Nats__intValues2Nats : forall l0 lc gl TD gvs0,
  values2GVs TD l0 lc gl = Some gvs0 ->
  GVs2Nats TD gvs0 = intValues2Nats TD l0 lc gl.
Proof.
  induction l0; intros lc gl TD gvs0 H; simpl in *.
    inversion H. auto.

    destruct (getOperandValue TD v lc gl); try solve [inversion H].
      remember (values2GVs TD l0 lc gl)as ogv.
      destruct ogv; inversion H; subst.
        rewrite <- IHl0 with (gvs0:=l1); auto.
Qed.

Lemma const2GV_eqAL_aux : 
  (forall c gl1 gl2 TD, eqAL _ gl1 gl2 -> 
     _const2GV TD gl1 c = _const2GV TD gl2 c) /\
  (forall cs gl1 gl2 TD, eqAL _ gl1 gl2 -> 
    (forall t, _list_const_arr2GV TD gl1 t cs = _list_const_arr2GV TD gl2 t cs) 
    /\
    _list_const_struct2GV TD gl1 cs = _list_const_struct2GV TD gl2 cs).
Proof.
  apply const_mutind; intros; simpl; 
  try solve [
    auto |

    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0;
      destruct H0; auto |

    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0;
    destruct H0;
    rewrite H1; auto |

    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0;
    destruct H0;
    rewrite H0; auto |

    rewrite H; auto |

    assert (J:=H1);
    apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1;
    destruct H1;
    rewrite H2; rewrite H1; erewrite H; eauto |

    assert (J:=H1);
    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1;
    rewrite H1;
    assert (J':=J);
    apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J;
    rewrite J; auto
  ].

  apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1.
  rewrite H1. auto.

  assert (J:=H2).
  apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H2.
  rewrite H2.
  assert (J':=J).
  apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J.
  rewrite J.
  apply H1 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J'.
  rewrite J'. auto.

  assert (J:=H1).
  apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1.
  rewrite H1. auto.

  assert (J:=H2).
  apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H2.
  rewrite H2.
  assert (J':=J).
  apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J.
  rewrite J. auto.

  split.
    intros.
    assert (J:=H1);
    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1;
    rewrite H1;
    assert (J':=J);
    apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J.
    destruct J. rewrite H2; auto.

    assert (J:=H1);
    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1;
    rewrite H1;
    assert (J':=J);
    apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in J.
    destruct J. rewrite H3; auto.
Qed.

Lemma const2GV_eqAL : forall c gl1 gl2 TD, 
  eqAL _ gl1 gl2 -> 
  const2GV TD gl1 c = const2GV TD gl2 c.
Proof.
  intros. unfold const2GV.
  destruct const2GV_eqAL_aux.
  erewrite H0; eauto.
Qed.

Lemma getOperandValue_eqAL : forall lc1 gl lc2 v TD,
  eqAL _ lc1 lc2 ->
  getOperandValue TD v lc1 gl = getOperandValue TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD HeqAL.
  unfold getOperandValue in *.
  destruct v; auto.
Qed.

Lemma BOP_eqAL : forall lc1 gl lc2 bop0 sz0 v1 v2 TD,
  eqAL _ lc1 lc2 ->
  BOP TD lc1 gl bop0 sz0 v1 v2 = BOP TD lc2 gl bop0 sz0 v1 v2.
Proof.
  intros lc1 gl lc2 bop0 sz0 v1 v2 TD HeqEnv.
  unfold BOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma FBOP_eqAL : forall lc1 gl lc2 fbop0 fp0 v1 v2 TD,
  eqAL _ lc1 lc2 ->
  FBOP TD lc1 gl fbop0 fp0 v1 v2 = FBOP TD lc2 gl fbop0 fp0 v1 v2.
Proof.
  intros lc1 gl lc2 fbop0 fp0 v1 v2 TD HeqEnv.
  unfold FBOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma getOperandPtr_eqAL : forall lc1 gl lc2 v TD,
  eqAL _ lc1 lc2 ->
  getOperandPtr TD v lc1 gl = getOperandPtr TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD HeqEnv.
  unfold getOperandPtr in *.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma getOperandInt_eqAL : forall lc1 gl lc2 sz v TD,
  eqAL _ lc1 lc2 ->
  getOperandInt TD sz v lc1 gl = getOperandInt TD sz v lc2 gl.
Proof.
  intros lc1 gl lc2 sz0 v TD HeqAL.
  unfold getOperandInt in *.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma getOperandPtrInBits_eqAL : forall lc1 gl lc2 sz v TD,
  eqAL _ lc1 lc2 ->
  getOperandPtrInBits TD sz v lc1 gl = getOperandPtrInBits TD sz v lc2 gl.
Proof.
  intros lc1 gl lc2 sz0 v TD HeqAL.
  unfold getOperandPtrInBits in *.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma CAST_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  CAST TD lc1 gl op t1 v1 t2 = CAST TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold CAST in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma TRUNC_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  TRUNC TD lc1 gl op t1 v1 t2 = TRUNC TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold TRUNC in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma EXT_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  EXT TD lc1 gl op t1 v1 t2 = EXT TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold EXT in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma ICMP_eqAL : forall lc1 gl lc2 cond t v1 v2 TD,
  eqAL _ lc1 lc2 ->
  ICMP TD lc1 gl cond t v1 v2 = ICMP TD lc2 gl cond t v1 v2.
Proof.
  intros lc1 gl lc2 cond0 t v1 v2 TD HeqAL.
  unfold ICMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma FCMP_eqAL : forall lc1 gl lc2 cond fp v1 v2 TD,
  eqAL _ lc1 lc2 ->
  FCMP TD lc1 gl cond fp v1 v2 = FCMP TD lc2 gl cond fp v1 v2.
Proof.
  intros lc1 gl lc2 cond0 fp v1 v2 TD HeqAL.
  unfold FCMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma intValues2Nats_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  intValues2Nats TD  l0 lc1 gl = intValues2Nats TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD HeqAL; simpl; auto.
    rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v); auto.
    erewrite IHl0; eauto.
Qed.

Lemma values2GVs_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  values2GVs TD l0 lc1 gl = values2GVs TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD HeqAL; simpl; auto.
    rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v); auto.
    erewrite IHl0; eauto.
Qed.

(*
Lemma GEP_eqAL : forall lc1 gl lc2 t ma vidxs ib TD,
  eqAL _ lc1 lc2 ->
  GEP TD lc1 gl t ma vidxs ib = GEP TD lc2 gl t ma vidxs ib.
Proof.
  intros lc1 gl lc2 t ma vidxs ib TD HeqAL.
  unfold GEP in *. auto.
  erewrite intValues2Nats_eqAL; eauto. 
Qed.
*)

(** allocate memory with size and alignment *)

Definition malloc (TD:TargetData) (M:mem) (bsz:sz) (gn:GenericValue) (al:align) 
  : option (mem * mblock)%type :=
match GV2int TD Size.ThirtyTwo gn with
| Some n => 
    if (Coqlib.zle 0 ((Size.to_Z bsz) * n)) then
      Some (Mem.alloc M 0 ((Size.to_Z bsz) * n))
    else None
| None => None
end.

Definition malloc_one (TD:TargetData) (M:mem) (bsz:sz) (al:align) 
  : option (mem * mblock)%type :=
if (Coqlib.zle 0 (Size.to_Z bsz)) then
  Some (Mem.alloc M 0 (Size.to_Z bsz))
else None.

Definition free (TD:TargetData) (M:mem) (ptr:mptr) : option mem :=
match GV2ptr TD (getPointerSize TD) ptr with
| Some (Vptr b i) =>
  if Coqlib.zeq (Int.signed 31 i) 0 
  then
    match (Mem.bounds M b) with
    | (l, h) => Mem.free M b l h
    end
  else None
| _ => None
end.

Fixpoint free_allocas (TD:TargetData) (Mem:mem) (allocas:list mblock) 
  : option mem :=
match allocas with
| nil => Some Mem
| alloca::allocas' =>
  match (free TD Mem (blk2GV TD alloca)) with
  | Some Mem' => free_allocas TD Mem' allocas'
  | None => None
  end
end.

Definition uninitMCs (n:nat) : list memory_chunk := 
  Coqlib.list_repeat n (Mint 7).

Fixpoint repeatMC (mcs:list memory_chunk) (n:nat) : list memory_chunk :=
match n with
| O => nil
| S n' => mcs ++ repeatMC mcs n'
end.

Fixpoint sizeMC (mc:list memory_chunk) : nat :=
match mc with
| nil => 0%nat
| c::mc' => (size_chunk_nat c + sizeMC mc')%nat
end.

Fixpoint flatten_typ (TD:TargetData) (t:typ) : option (list memory_chunk) :=
match t with
| typ_int sz => Some (Mint (Size.to_nat sz - 1) :: nil)
| typ_floatpoint fp =>
  match fp with
  | fp_float => Some (Mfloat32 :: nil)
  | fp_double => Some (Mfloat64 :: nil)
  | _ => None (* FIXME: not supported 80 and 128 yet. *)
  end
| typ_void => None          
| typ_label => None                     
| typ_metadata => None                
| typ_array sz t => 
  match sz with
  | O => Some (uninitMCs 1)  
  | _ =>
    match flatten_typ TD t with
    | Some mc0 =>
      match getTypeAllocSize TD t with
      | Some asz => 
         Some (repeatMC (mc0++uninitMCs (Size.to_nat asz - sizeMC mc0)) 
                 (Size.to_nat sz))
      | _ => None 
      end
    | _ => None
    end
  end
| typ_struct ts => 
  match flatten_typs TD ts with
  | Some nil => Some (uninitMCs 1)  
  | Some gv0 => Some gv0
  | None => None
  end
| typ_pointer t' => Some (Mint 31::nil)
| typ_function _ _ _ => None
| typ_opaque => None
| typ_namedt _ => None (*FIXME: Can zeroconstant be of named type? How about termination. *)
end             
with flatten_typs (TD:TargetData) (lt:list_typ) : option (list memory_chunk) := 
match lt with
| Nil_list_typ => Some nil
| Cons_list_typ t lt' =>
  match (flatten_typs TD lt', flatten_typ TD t) with
  | (Some mc, Some mc0) =>
       match getTypeAllocSize TD t with
       | Some asz => Some (mc++mc0++uninitMCs (asz - sizeMC mc0))
       | _ => None 
       end
  | _ => None
  end
end
.

Lemma sizeMC__app : forall mc1 mc2, 
  sizeMC (mc1 ++ mc2) = (sizeMC mc1 + sizeMC mc2)%nat.
Proof.
  induction mc1; intros; simpl; auto.
    rewrite IHmc1. omega.
Qed.

Lemma sizeMC__repeatMC : forall mc n,
  sizeMC (repeatMC mc n) = (n * sizeMC mc)%nat.
Proof.
  induction n; simpl; auto.
    rewrite sizeMC__app. rewrite IHn. auto.
Qed.

Lemma sizeMC__uninitMCs : forall n, sizeMC (uninitMCs n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Definition flatten_typ__getTypeSizeInBits_prop (t:typ) := forall s los nts mc,
  flatten_typ (los,nts) t = Some mc ->
  LLVMwf.wf_typ s t -> Constant.feasible_typ (los,nts) t ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeMC mc.

Definition flatten_typs__getListTypeSizeInBits_prop (lt:list_typ) := 
  forall los nts mc lst,
  flatten_typs (los,nts) lt = Some mc ->
  LLVMwf.wf_typ_list lst -> Constant.feasible_typs (los,nts) lt ->
  (exists ls, 
    split (LLVMwf.unmake_list_system_typ lst) = (ls, unmake_list_typ lt)) ->
  exists sz, exists al,
    _getListTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) lt = 
        Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeMC mc.

Lemma flatten_typ_typsize_mutrec :
  (forall t, flatten_typ__getTypeSizeInBits_prop t) *
  (forall lt, flatten_typs__getListTypeSizeInBits_prop lt).
Proof.
  (typ_cases (apply typ_mutrec; 
    unfold flatten_typ__getTypeSizeInBits_prop, 
           flatten_typs__getListTypeSizeInBits_prop) Case);
    intros; simpl in *; try solve [eauto | inversion H | inversion H1 ].
Case "typ_int".
  inv H.
  simpl.
  exists (Size.to_nat s). exists (getIntAlignmentInfo los (Size.to_nat s) true).
  erewrite int_typsize; eauto.

Case "typ_floatingpoint".
  destruct f; inv H; simpl; unfold size_chunk_nat, size_chunk, bytesize_chunk.
    exists 32%nat. exists (getFloatAlignmentInfo los 32 true).
    simpl. auto.

    exists 64%nat. exists (getFloatAlignmentInfo los 64 true).
    simpl. auto.

Case "typ_array".
  destruct s;  try solve [inv H0; exists 8%nat; exists 1%nat; auto].
  remember (flatten_typ (los, nts) t) as R1.
  destruct R1; try solve [inv H0].
  remember (getTypeAllocSize (los, nts) t) as R2.
  destruct R2; inv H0.
  assert (
    (l0 ++ uninitMCs (Size.to_nat s1 - sizeMC l0)) ++
          repeatMC (l0 ++ uninitMCs (Size.to_nat s1 - sizeMC l0)) s = 
    repeatMC (l0 ++ uninitMCs (Size.to_nat s1 - sizeMC l0)) (S s)) as G.
    simpl. auto.
  rewrite G.
  symmetry in HeqR1.
  inv H1.
  apply H with (s:=s0) in HeqR1; eauto using feasible_array_typ_inv.
  destruct HeqR1 as [sz [al [J1 J2]]].
  rewrite J1.  rewrite J2.
  exists (RoundUpAlignment (sizeMC l0) al * 8 * Size.to_nat (S s))%nat.
  exists al.
  split; auto.
  unfold getTypeAllocSize, getABITypeAlignment, getAlignment, getTypeStoreSize,
    getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
    getTypeSizeInBits_and_Alignment_for_namedts in HeqR2.
  rewrite J1 in HeqR2.
  inv HeqR2.
  rewrite sizeMC__repeatMC.
  rewrite sizeMC__app.
  rewrite sizeMC__uninitMCs. rewrite J2. unfold Size.to_nat.
  assert (RoundUpAlignment (sizeMC l0) al >= (sizeMC l0))%nat as J3.
    apply RoundUpAlignment_spec.
      eapply feasible_typ_inv in H2; eauto.
      destruct H2 as [sz0 [al0 [J3 [J4 J5]]]].
      unfold getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts in J3.
      rewrite J1 in J3. inv J3. auto.

  assert ((sizeMC l0 + (RoundUpAlignment (sizeMC l0) al - sizeMC l0))%nat = 
     (RoundUpAlignment (sizeMC l0) al)) as J4.
    rewrite <- le_plus_minus; auto.
  rewrite J4.
  rewrite ZRdiv_prop6.
  ring.

Case "typ_struct".
  remember (flatten_typs (los, nts) l0) as R1.
  destruct R1; inv H0.
  symmetry in HeqR1.
  inv H1.
  eapply H in HeqR1; eauto using list_system_typ_spec, feasible_struct_typ_inv.
  destruct HeqR1 as [sz [al [J1 J2]]].
  rewrite J1.
  destruct sz.
    exists 8%nat. exists 1%nat.
    split; auto.
      simpl in J2.
      destruct l1; inv H4; auto.
        simpl in J2.
        assert (J3 := size_chunk_nat_pos' m).
        contradict J2; omega.

    exists (S sz0). exists al.
    split; auto.
      rewrite J2.
      destruct l1; inv H4; auto.
        assert (Coqlib.ZRdiv (Z_of_nat (S sz0)) 8 > 0) as J.
          apply Coqlib.ZRdiv_prop3; try solve [omega | apply Coqlib.Z_of_S_gt_O].
        apply Coqlib.nat_of_Z_pos in J.
        contradict J2. simpl in *. omega.

Case "typ_pointer".
  inv H0.
  exists (Size.to_nat (getPointerSizeInBits los)).
  exists (getPointerAlignmentInfo los true).
  split; auto.
     
Case "typ_nil".
  inv H. 
  exists 0%nat. exists 0%nat. auto.

Case "typ_cons".
  destruct H4 as [ls H4].
  apply unmake_list_system_typ_inv in H4.
  destruct H4 as [s [ls' [lst' [J1 [J2 J3]]]]]; subst.
  inv H2.
  remember (flatten_typs (los, nts) l0) as R1.
  destruct R1; inv H1.
  remember (flatten_typ (los, nts) t) as R2.
  destruct R2; inv H4.
  remember (getTypeAllocSize (los, nts) t) as R3.
  destruct R3; inv H2.
  symmetry in HeqR1. symmetry in HeqR2.
  destruct H3 as [H31 H32].
  eapply H in HeqR2; eauto.
  eapply H0 in HeqR1; eauto.
  destruct HeqR1 as [sz1 [al1 [J4 J5]]].
  destruct HeqR2 as [sz2 [al2 [J6 J7]]].
  rewrite J4. rewrite J6.
  rewrite sizeMC__app.
  rewrite sizeMC__app.
  rewrite sizeMC__uninitMCs. 
  rewrite <- J5. rewrite <- J7. 
  erewrite getTypeAllocSize_roundup; eauto.
  eapply getTypeAllocSize_inv' in J6; eauto. subst.
  exists ((sz1 +
             RoundUpAlignment
               (Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz2) 8)) al2 * 8 )%nat).
  exists (if le_lt_dec al2 al1 then al1 else al2).
  split; auto.
    apply ZRdiv_prop7.
Qed.

Lemma flatten_typ__getTypeSizeInBits : forall t s los nts mc,
  flatten_typ (los,nts) t = Some mc ->
  LLVMwf.wf_typ s t -> Constant.feasible_typ (los,nts) t ->
  exists sz, exists al,
    _getTypeSizeInBits_and_Alignment los 
      (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
         Some (sz, al) /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeMC mc.
Proof.
  destruct flatten_typ_typsize_mutrec; auto.
Qed.

Fixpoint mload_aux M (mc:list memory_chunk) b ofs : option GenericValue :=
match mc with
| nil => Some nil
| c::mc' =>
    match (Mem.load c M b ofs, mload_aux M mc' b (ofs+size_chunk c)) with
    | (Some v, Some gv) => Some ((v,c) :: gv)
    | _ => None
    end
end.

Lemma mload_aux__sizeGenericValue : forall M b mc ofs gv,
  mload_aux M mc b ofs = Some gv ->
  sizeMC mc = sizeGenericValue gv.
Proof.
  induction mc; simpl; intros.
    inv H. auto.

    destruct (Mem.load a M b ofs); tinv H.
    remember (mload_aux M mc b (ofs + size_chunk a)) as R.
    destruct R; inv H.
    simpl.
    erewrite IHmc; eauto.
Qed.

Definition mload (TD:TargetData) (M:mem) (ptr:mptr) (t:typ) (a:align) 
  : option GenericValue :=
match GV2ptr TD (getPointerSize TD) ptr with
| Some (Vptr b ofs) =>
  match flatten_typ TD t with
  | Some mc => mload_aux M mc b (Int.signed 31 ofs)
  | _ => None
  end
| _ => None
end.

Lemma mload_inv : forall Mem2 t align0 TD gvp2 
  (gv2 : GenericValue)
  (H21 : mload TD Mem2 gvp2 t align0 = ret gv2),
  exists b, exists ofs, exists m, exists mc, 
    gvp2 = (Vptr b ofs,m)::nil /\ flatten_typ TD t = Some mc /\
    mload_aux Mem2 mc b (Int.signed 31 ofs) = Some gv2.
Proof.
  intros.
  unfold mload in H21.
  remember (GV2ptr TD (getPointerSize TD) gvp2) as R.
  destruct R; try solve [inversion H21].
  destruct v; try solve [inversion H21].
  unfold GV2ptr in HeqR.
  destruct gvp2; try solve [inversion HeqR].
  destruct p.
  destruct v; try solve [inversion HeqR].
  destruct gvp2; inv HeqR.
  exists b0. exists i1. exists m.
  destruct (flatten_typ TD t); inv H21.
  eauto.
Qed.

Lemma mload__getTypeSizeInBits : forall t s TD gv a ptr M,
  mload TD M ptr t a = Some gv ->
  LLVMwf.wf_typ s t -> Constant.feasible_typ TD t ->
  exists sz, 
    getTypeSizeInBits TD t = Some sz /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof.
  intros.
  apply mload_inv in H.
  destruct H as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment.
  erewrite <- mload_aux__sizeGenericValue; eauto.
  destruct TD.
  eapply flatten_typ__getTypeSizeInBits in J2; eauto.
  destruct J2 as [sz [al [J21 J22]]].
  rewrite J21. eauto.
Qed.

Fixpoint mstore_aux M (gv:GenericValue) b ofs : option mem :=
match gv with
| nil => Some M
| (v,c)::gv' =>
    match (Mem.store c M b ofs v) with
    | Some M' => mstore_aux M' gv' b (ofs+size_chunk c)
    | _ => None
    end
end.

Definition mstore (TD:TargetData) (M:mem) (ptr:mptr) (t:typ) (gv:GenericValue) 
  (a:align) : option mem :=
match GV2ptr TD (getPointerSize TD) ptr with
| Some (Vptr b ofs) => mstore_aux M gv b (Int.signed 31 ofs)
| _ => None
end.

Lemma free_inv : forall TD Mem0 gv Mem',
  free TD Mem0 gv = ret Mem' ->
  exists blk, exists ofs, exists hi, exists lo,
    GV2ptr TD (getPointerSize TD) gv = Some (Vptr blk ofs) /\
    Int.signed 31 ofs = 0%Z /\
    (lo, hi) = Mem.bounds Mem0 blk /\
    Mem.free Mem0 blk lo hi = Some Mem'.
Proof.
  intros TD Mem0 gv Mem' H0.
  unfold free in H0.
  destruct (GV2ptr TD (getPointerSize TD) gv); try solve [inversion H0; subst].
  destruct v; try solve [inversion H0; subst].
  destruct (Coqlib.zeq (Int.signed 31 i0) 0); try solve [inversion H0; subst].
  remember (Mem.bounds Mem0 b) as R.
  destruct R as [l h].
  exists b. exists i0. rewrite e. rewrite <- HeqR. exists h. exists l.
  repeat (split; auto).
Qed.  

Lemma malloc_inv : forall TD Mem0 tsz gn align0 Mem' mb,
  malloc TD Mem0 tsz gn align0 = ret (Mem', mb) ->
  exists n, GV2int TD Size.ThirtyTwo gn = Some n /\
    (0 <= (Size.to_Z tsz) * n)%Z /\
    Mem.alloc Mem0 0 (Size.to_Z tsz * n) = (Mem', mb).
Proof.
  intros.
  unfold malloc in H.
  destruct (GV2int TD Size.ThirtyTwo gn); try solve [inversion H; subst].
  destruct (Coqlib.zle 0 (Size.to_Z tsz * z)); inversion H; subst.
  exists z.
  destruct (Mem.alloc Mem0 0 (Size.to_Z tsz * z)).
  repeat (split; auto).
Qed.

Lemma store_inv : forall TD Mem0 gvp t gv align Mem',
  mstore TD Mem0 gvp t gv align = Some Mem' ->
  exists b, exists ofs,
    GV2ptr TD (getPointerSize TD) gvp = Some (Vptr b ofs) /\
    mstore_aux Mem0 gv b (Int.signed 31 ofs) = Some Mem'.
Proof.
  intros TD Mem0 gvp t gv align Mem' H.
  unfold mstore in H.
  destruct (GV2ptr TD (getPointerSize TD) gvp); try solve [inversion H; subst].
  destruct v; try solve [inversion H; subst].
  exists b. exists i0. split; auto.
Qed.

End LLVMgv.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
