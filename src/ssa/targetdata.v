Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "../../../theory/metatheory".
Require Import Zpower.
Require Import Zdiv.
Require Import List.
Require Import ssa.

Export LLVMsyntax.

Definition nat_of_Z (z: Z) : nat :=
  match z with
  | Z0 => O
  | Zpos p => nat_of_P p
  | Zneg p => O
end.

Lemma Z_of_nat__nat_of_Z:
  forall z, (z >= 0)%Z -> Z_of_nat (nat_of_Z z) = z.
Proof.
  intros. destruct z; simpl.
  auto.
  symmetry. apply Zpos_eq_Z_of_nat_o_nat_of_P.
  compute in H. congruence.
Qed.

Lemma nat_of_Z__Z_of_nat : forall n,
  n >= 0 ->
  nat_of_Z (Z_of_nat n) = n.
Proof.
  intros. destruct n; simpl.
  auto.
  apply nat_of_P_o_P_of_succ_nat_eq_succ.
Qed.

Definition ndiv (n m:nat) := nat_of_Z (Zdiv (Z_of_nat (n)) (Z_of_nat m)).  

(**
 Alignments come in two flavors: ABI and preferred. ABI alignment (abi_align,
 below) dictates how a type will be aligned within an aggregate and when used
 as an argument.  Preferred alignment (pref_align, below) determines a type's
 alignment when emitted as a global.

 Specifier string details:

 E|e: Endianness. "E" specifies a big-endian target data model, "e"
 specifies a little-endian target data model.

 p:size:abi_align:pref_align: Pointer size, ABI and preferred alignment.

 Type:size:abi_align:pref_align: Numeric type alignment. Type is one of i|f|v|a, 
 corresponding to integer, floating point, or aggregate.  Size indicates the size, 
 e.g., 32 or 64 bits.

 Note that in the case of aggregates, 0 is the default ABI and preferred
 alignment. This is a special case, where the aggregate's computed worst-case
 alignment will be used.

 At any case, if 0 is the preferred alignment, then the preferred alignment
 equals to its ABI alignment.

  // Default alignments
  align_type,      abi_align, pref_align, bit_width
  INTEGER_ALIGN,   1,         1,          1   // i1
  INTEGER_ALIGN,   1,         1,          8   // i8
  INTEGER_ALIGN,   2,         2,          16  // i16
  INTEGER_ALIGN,   4,         4,          32  // i32
  INTEGER_ALIGN,   4,         8,          64  // i64
  AGGREGATE_ALIGN, 0,         8,          0   // struct
  PTR,             8,         8,          64  // ptr
  BigEndian

 When LLVM is determining the alignment for a given type, it uses the following rules:
   1. If the type sought is an exact match for one of the specifications, that 
      specification is used.
   2. If no match is found, and the type sought is an integer type, then the smallest 
      integer type that is larger than the bitwidth of the sought type is used. If none 
      of the specifications are larger than the bitwidth then the the largest integer 
      type is used. For example, given the default specifications above, the i7 type will 
      use the alignment of i8 (next largest) while both i65 and i256 will use the alignment 
      of i64 (largest specified).
*)

Definition layouts := list layout.

Definition DTD : layouts := 
                   (layout_be::layout_int 1 1 1::layout_int 8 1 1::layout_int 16 2 2::
                    layout_int 32 4 4::layout_int 64 4 8::layout_aggr 0 0 8::
                    layout_ptr 64 0 0::nil).

(** RoundUpAlignment - Round the specified value up to the next alignment
    boundary specified by Alignment.  For example, 7 rounded up to an
    alignment boundary of 4 is 8.  8 rounded up to the alignment boundary of 4
    is 8 because it is already aligned. *)
Definition RoundUpAlignment (val alignment:nat) : nat :=
  let zv := Z_of_nat val in
  let za := two_power_nat alignment in
  let zr := (zv + za)%Z in
  nat_of_Z (zr / za * za).

(** getAlignmentInfo - Return the alignment (either ABI if ABIInfo = true or
    preferred if ABIInfo = false) the target wants for the specified datatype.
*)
Fixpoint _getIntAlignmentInfo (TD:layouts) (BitWidth: nat) (ABIInfo: bool) 
  (obest:option (nat*(nat*nat))) (olargest:option (nat*(nat*nat))) {struct TD} : option nat :=
  match TD with
  | nil => 
    (* Okay, we didn't find an exact solution.  Fall back here depending on what
       is being looked for.

       If we didn't find an integer alignment, fall back on most conservative. *)
    match (obest, olargest) with
    | (Some (_, (babi, bpre)), _) => 
      (if ABIInfo then Some babi else Some bpre)
    | (None, Some (_, (labi, lpre))) => 
      (if ABIInfo then Some labi else Some lpre)
    | _ => None
    end
  | (layout_int isz abi pre)::TD' =>
    if beq_nat isz BitWidth 
    then 
      (* Check to see if we have an exact match and remember the best match we see. *)
      (if ABIInfo then Some abi else Some pre)
    else 
      (* The obest match so far depends on what we're looking for. 
         The "obest match" for integers is the smallest size that is larger than
         the BitWidth requested. 
         
         However, if there isn't one that's larger, then we must use the
         largest one we have (see below) *) 
      match (obest, olargest, le_lt_dec BitWidth isz) with
      | (Some (bestbt, _), Some (largestbt, _), left _ (* BitWidth <= isz *) ) =>
        match (le_lt_dec largestbt isz) with
        | left _ (* isz <= largestbt *) =>
          _getIntAlignmentInfo TD' BitWidth ABIInfo obest olargest
        | right _ (* largestbt < isz *) =>
          _getIntAlignmentInfo TD' BitWidth ABIInfo (Some (isz, (abi, pre))) (Some (isz, (abi, pre)))
        end

      | (Some (bestbt, _), Some (largestbt, _), right _ (* isz < BitWidth *) ) =>
        match (le_lt_dec largestbt isz) with
        | left _ (* isz <= largestbt *) =>
          match (le_lt_dec isz bestbt) with
          | left _ (* bestbt <= isz *) =>
            _getIntAlignmentInfo TD' BitWidth ABIInfo obest olargest
          | right _ (* isz < bestbt *) =>
            _getIntAlignmentInfo TD' BitWidth ABIInfo (Some (isz, (abi, pre))) (Some (isz, (abi, pre)))
          end
        | right _ (* largestbt < isz *) =>
          _getIntAlignmentInfo TD' BitWidth ABIInfo (Some (isz, (abi, pre))) (Some (isz, (abi, pre)))
        end

      | (None, Some (largestbt, _), left _ (* BitWidth <= isz *) ) =>
        match (le_lt_dec largestbt isz) with
        | left _ (* isz <= largestbt *) =>
          _getIntAlignmentInfo TD' BitWidth ABIInfo obest olargest
        | right _ (* largestbt < isz *) =>
          _getIntAlignmentInfo TD' BitWidth ABIInfo obest (Some (isz, (abi, pre)))
        end

      | (None, Some (largestbt, _), right _ (* isz < BitWidth *) ) =>
        match (le_lt_dec largestbt isz) with
        | left _ (* isz <= largestbt *) =>
          _getIntAlignmentInfo TD' BitWidth ABIInfo (Some (isz, (abi, pre))) olargest
        | right _ (* largestbt < isz *) =>
          _getIntAlignmentInfo TD' BitWidth ABIInfo (Some (isz, (abi, pre))) (Some (isz, (abi, pre)))
        end

      | (Some (bestbt, _), None, left _ (* BitWidth <= isz *) ) =>
          _getIntAlignmentInfo TD' BitWidth ABIInfo obest (Some (isz, (abi, pre)))
      | (Some (bestbt, _), None, right _ (* isz < BitWidth *) ) =>
          match (le_lt_dec isz bestbt) with
          | left _ (* bestbt <= isz *) =>
            _getIntAlignmentInfo TD' BitWidth ABIInfo obest (Some (isz, (abi, pre)))
          | right _ (* isz < bestbt *) =>
            _getIntAlignmentInfo TD' BitWidth ABIInfo (Some (isz, (abi, pre))) (Some (isz, (abi, pre)))
          end
      | (None, None, left _ (* BitWidth <= isz *) ) =>
          _getIntAlignmentInfo TD' BitWidth ABIInfo obest (Some (isz, (abi, pre)))
      | (None, None, right _ (* isz < BitWidth *) ) =>
          _getIntAlignmentInfo TD' BitWidth ABIInfo (Some (isz, (abi, pre))) (Some (isz, (abi, pre)))
      end 
  | _::TD' =>
    _getIntAlignmentInfo TD' BitWidth ABIInfo obest olargest
  end.

Definition getIntDefaultAlignmentInfo (BitWidth: nat) (ABIInfo: bool) : nat :=
  match (le_lt_dec 1 BitWidth) with
  | left _ (* BitWidth <= 1 *) => if BitWidth then 1 else 1
  | right _ (* 1 < BitWidth *) =>
    match (le_lt_dec 8 BitWidth) with
    | left _ (* BitWidth <= 8 *) => if BitWidth then 1 else 1
    | right _ (* 8 < BitWidth *) =>
      match (le_lt_dec 16 BitWidth) with
      | left _ (* BitWidth <= 16 *) => if BitWidth then 2 else 2
      | right _ (* 16 < BitWidth *) =>
        match (le_lt_dec 32 BitWidth) with
        | left _ (* BitWidth <= 32 *) => if BitWidth then 4 else 4
        | right _ (* 32 < BitWidth *) => if BitWidth then 4 else 8
        end
      end
    end
  end.

Definition getIntAlignmentInfo (TD:layouts) (BitWidth: nat) (ABIInfo: bool) : nat :=
  match (_getIntAlignmentInfo TD BitWidth ABIInfo None None) with
  | Some n => n
  | None => getIntDefaultAlignmentInfo BitWidth ABIInfo
  end.

(** Target pointer alignment when ABIInfo is true
    Return target's alignment for stack-based pointers when ABIInfo is false *)
Fixpoint _getPointerAlignmentInfo (TD:layouts) (ABIInfo: bool) : option nat :=
  match TD with
  | nil => None
  | (layout_ptr psz abi pre)::_ => if ABIInfo then Some abi else Some pre
  | _::TD' => _getPointerAlignmentInfo TD' ABIInfo
  end.

Definition getPointerAlignmentInfo (TD:layouts) (ABIInfo: bool) : nat :=
  match (_getPointerAlignmentInfo TD ABIInfo) with
  | Some n => n
  | None => 8
  end.

Fixpoint _getStructAlignmentInfo (TD:layouts) (ABIInfo: bool) : option nat :=
  match TD with
  | nil => None
  | (layout_aggr sz abi pre)::_ => if ABIInfo then Some abi else Some pre
  | _::TD' => _getStructAlignmentInfo TD' ABIInfo
  end.

Definition getStructAlignmentInfo (TD:layouts) (ABIInfo: bool) : nat :=
  match (_getStructAlignmentInfo TD ABIInfo) with
  | Some n => n
  | None => if ABIInfo then 0 else 8
  end.

(** Target pointer size *)
Fixpoint _getPointerSize (TD:layouts) : option nat :=
  match TD with
  | nil => None
  | (layout_ptr psz abi pre)::_ => Some (ndiv psz 8)
  | _::TD' => _getPointerSize TD'
  end.

Definition getPointerSize (TD:layouts) : nat :=
  match (_getPointerSize TD) with
  | Some n => n
  | None => 8
  end.

(** Target pointer size, in bits *)
Definition getPointerSizeInBits (TD:layouts) : nat :=
  8 * (getPointerSize TD).

(** Merged getTypeSizeInBits, getTypeStoreSize, getTypeAllocSize, 
    getTypeAllocSizeInBits, getAlignment and getStructLayout *)
Fixpoint getTypeSizeInBits_and_Alignment (TD:layouts) (abi_or_pref:bool) (t:typ)
  : option (nat*nat) :=
  let getTypeStoreSize := 
      fun typeSizeInBits => ndiv (typeSizeInBits+7) 8 in

  let getTypeAllocSize :=
      fun typeSizeInBits ABIalignment =>
      (* Round up to the next alignment boundary *)
      RoundUpAlignment (getTypeStoreSize typeSizeInBits) ABIalignment in

  let getTypeAllocSizeInBits :=
      fun typeSizeInBits ABIalignment =>
      8*getTypeAllocSize typeSizeInBits ABIalignment in

  match t with
  | typ_label => Some (getPointerSizeInBits TD, getPointerAlignmentInfo TD abi_or_pref) 

  | typ_pointer _ => Some (getPointerSizeInBits TD, getPointerAlignmentInfo TD abi_or_pref) 

  | typ_void => Some (8, getIntAlignmentInfo TD 8 abi_or_pref) 

  | typ_int sz => Some (sz, getIntAlignmentInfo TD sz abi_or_pref) 

  | typ_array n t' => 
    (* getting ABI alignment *)
    match (getTypeSizeInBits_and_Alignment TD true t') with 
    | None => None
    | Some (sz, al) => 
      Some ((getTypeAllocSizeInBits sz al)*n, al)
    end

  | typ_struct lt => 
    (* Loop over each of the elements, placing them in memory. *)
    match (
      fold_left 
      (fun struct_op_sz_al sub_op_sz_al =>
        match (struct_op_sz_al, sub_op_sz_al) with
        | (Some (struct_sz, struct_al), Some (sub_sz, sub_al)) =>
          (* Add padding if necessary to align the data element properly. *)
          (* Keep track of maximum alignment constraint. *)
          (* Consume space for this data item *)
          match (le_lt_dec sub_al struct_al) with
          | left _ (* struct_al <= sub_al *) =>
            Some (
              RoundUpAlignment struct_sz sub_al + getTypeAllocSize sub_sz sub_al,
              sub_al
            )
          | right _ (* sub_al < struct_al *) =>
            Some (
              RoundUpAlignment struct_sz sub_al + getTypeAllocSize sub_sz sub_al,
              struct_al
            )
          end
        | _ => None
        end
      )
      (map (getTypeSizeInBits_and_Alignment TD true) lt) (* getting ABI alignment *)
      (Some (0, 0)) ) with
    | None => None
    | (Some (sz, al)) => 
      (* Empty structures have alignment of 1 byte. *)
      (* Add padding to the end of the struct so that it could be put in an array
         and all array elements would be aligned correctly. *)
       match sz with
       | 0 => Some (8*(RoundUpAlignment 1 al), al)
       | _ => Some (8*(RoundUpAlignment sz al), al)
       end
    end      
  | _ => None
  end.

(** abi_or_pref Flag that determines which alignment is returned. true
  returns the ABI alignment, false returns the preferred alignment.

  Get the ABI (abi_or_pref == true) or preferred alignment (abi_or_pref
  == false) for the requested type t.
 *)
Definition getAlignment (TD:layouts) (t:typ) (abi_or_pref:bool) : option nat :=
  match (getTypeSizeInBits_and_Alignment TD abi_or_pref t) with
  | (Some (sz, al)) => Some al
  | None => None
  end.

(** getABITypeAlignment - Return the minimum ABI-required alignment for the
    specified type. *)
Definition getABITypeAlignment (TD:layouts) (t:typ) : option nat :=
  getAlignment TD t true.

(** getPrefTypeAlignment - Return the preferred stack/global alignment for
    the specified type.  This is always at least as good as the ABI alignment. *)
Definition getPrefTypeAlignment (TD:layouts) (t:typ) : option nat :=
  getAlignment TD t false.

(*
 Size examples:
  
   Type        SizeInBits  StoreSizeInBits  AllocSizeInBits[*]
   ----        ----------  ---------------  ---------------
    i1            1           8                8
    i8            8           8                8
    i19          19          24               32
    i32          32          32               32
    i100        100         104              128
    i128        128         128              128
    Float        32          32               32
    Double       64          64               64
    X86_FP80     80          80               96
  
   [*] The alloc size depends on the alignment, and thus on the target.
       These values are for x86-32 linux.
*)

(** getTypeSizeInBits - Return the number of bits necessary to hold the
    specified type.  For example, returns 36 for i36 and 80 for x86_fp80. *)
Definition getTypeSizeInBits (TD:list layout) (t:typ) : option nat :=
  match (getTypeSizeInBits_and_Alignment TD true t) with
  | (Some (sz, al)) => Some sz
  | None => None
  end.

(** getTypeStoreSize - Return the maximum number of bytes that may be
    overwritten by storing the specified type.  For example, returns 5
    for i36 and 10 for x86_fp80. *)
Definition getTypeStoreSize (TD:layouts) (t:typ) : option nat :=
  match (getTypeSizeInBits TD t) with
  | None => None
  | Some sz => Some (ndiv (sz+7) 8)
  end.

(** getTypeStoreSizeInBits - Return the maximum number of bits that may be
    overwritten by storing the specified type; always a multiple of 8.  For
    example, returns 40 for i36 and 80 for x86_fp80.*)
Definition getTypeStoreSizeInBits (TD:layouts) (t:typ) : option nat :=
  match (getTypeStoreSize TD t) with
  | None => None
  | Some n => Some (8*n)
  end.

(** getTypeAllocSize - Return the offset in bytes between successive objects
    of the specified type, including alignment padding.  This is the amount
    that alloca reserves for this type.  For example, returns 12 or 16 for
    x86_fp80, depending on alignment. *)
Definition getTypeAllocSize (TD:layouts) (t:typ) : option nat :=
  match (getTypeStoreSize TD t, getABITypeAlignment TD t) with
  | (Some ss, Some ta) => 
    (* Round up to the next alignment boundary *)
    Some (RoundUpAlignment ss ta)
  | _ => None
  end.

(** getTypeAllocSizeInBits - Return the offset in bits between successive
    objects of the specified type, including alignment padding; always a
    multiple of 8.  This is the amount that alloca reserves for this type.
    For example, returns 96 or 128 for x86_fp80, depending on alignment. *)
Definition getTypeAllocSizeInBits (TD:list layout) (t:typ) : option nat :=
  match (getTypeAllocSize TD t) with
  | None => None
  | Some n => Some (8*n)
  end.

Definition getStructSizeInBytes (TD:layouts) (t:typ) : option nat :=
match t with
| typ_struct lt => 
  match (getTypeSizeInBits TD t) with
  | Some sz => Some (ndiv sz 8)
  | None => None
  end
| _ => None
end.

Definition getStructSizeInBits (TD:layouts) (t:typ) : option nat :=
match t with
| typ_struct lt => getTypeSizeInBits TD t
| _ => None
end.

Definition getStructAlignment (TD:layouts) (t:typ) : option nat :=
match t with
| typ_struct lt => getABITypeAlignment TD t
| _ => None
end.

Fixpoint _getStructElementOffset (TD:layouts) (ts:list typ) (idx:nat) 
         (struct_sz struct_al : nat) : option nat :=
match (ts, idx) with
| (t::nil, 0) => 
        match (getTypeAllocSize TD t, getABITypeAlignment TD t) with
        | (Some sub_sz, Some sub_al) =>
           (* Add padding if necessary to align the data element properly. *)
           Some (RoundUpAlignment struct_sz sub_al)
        | _ => None
        end
| (t::ts', S idx') =>
        match (getTypeAllocSize TD t, getABITypeAlignment TD t) with
        | (Some sub_sz, Some sub_al) =>
          (* Add padding if necessary to align the data element properly. *)
          (* Keep track of maximum alignment constraint. *)
          (* Consume space for this data item *)
          match (le_lt_dec sub_al struct_al) with
          | left _ (* struct_al <= sub_al *) =>
            _getStructElementOffset TD ts' idx'
              (RoundUpAlignment struct_sz sub_al + sub_sz)
              sub_al
          | right _ (* sub_al < struct_al *) =>
            _getStructElementOffset TD ts' idx'
              (RoundUpAlignment struct_sz sub_al + sub_sz)
              struct_al
          end
        | _ => None
        end
| _ => None
end.

Definition getStructElementOffset (TD:layouts) (t:typ) (idx:nat) : option nat :=
match t with
| typ_struct lt => _getStructElementOffset TD lt idx 0 0
| _ => None
end.

Definition getStructElementOffsetInBits (TD:layouts) (t:typ) (idx:nat) : option nat :=
match t with
| typ_struct lt => match (_getStructElementOffset TD lt idx 0 0) with
                   | None => None
                   | Some n => Some (n*8)
                   end
| _ => None
end.

(** getElementContainingOffset - Given a valid offset into the structure,
    return the structure index that contains it. *)
Fixpoint _getStructElementContainingOffset (TD:layouts) (ts:list typ) (offset:nat)(idx:nat)
         (struct_sz struct_al : nat) : option nat :=
match ts with
| nil => None
| t::ts' =>
        match (getTypeAllocSize TD t, getABITypeAlignment TD t) with
        | (Some sub_sz, Some sub_al) =>
          (* Add padding if necessary to align the data element properly. *)
          (* Keep track of maximum alignment constraint. *)
          (* Consume space for this data item *)
          match (le_lt_dec sub_al struct_al) with
          | left _ (* struct_al <= sub_al *) =>
             match (le_lt_dec offset (RoundUpAlignment struct_sz sub_al + sub_sz)) with
             | left _ (* (RoundUpAlignment struct_sz sub_al + sub_sz) <= offset*) => 
                _getStructElementContainingOffset TD ts' offset (S idx)
                   (RoundUpAlignment struct_sz sub_al + sub_sz)
                    sub_al
             | right _ => Some idx
             end
          | right _ (* sub_al < struct_al *) =>
             match (le_lt_dec offset (RoundUpAlignment struct_sz sub_al + sub_sz)) with
             | left _ (* (RoundUpAlignment struct_sz sub_al + sub_sz) <= offset*) => 
                _getStructElementContainingOffset TD ts' offset (S idx)
                   (RoundUpAlignment struct_sz sub_al + sub_sz)
                    struct_al
             | right _ => Some idx
             end
          end
        | _ => None
        end
end.

(** 
   Multiple fields can have the same offset if any of them are zero sized.
   For example, in { i32, [0 x i32], i32 }, searching for offset 4 will stop
   at the i32 element, because it is the last element at that offset.  This is
   the right one to return, because anything after it will have a higher
   offset, implying that this element is non-empty.
*)
Definition getStructElementContainingOffset (TD:layouts) (t:typ) (offset:nat) : option nat :=
match t with
| typ_struct lt => _getStructElementContainingOffset TD lt offset 0 0 0
| _ => None
end.

