(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** In-memory representation of values. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

(** * Properties of memory chunks *)

(** Memory reads and writes are performed by quantities called memory chunks,
  encoding the type, size and signedness of the chunk being addressed.
  The following functions extract the size information from a chunk. *)

Definition Mint32 := Mint 31.

Definition bytesize_chunk (wz:nat) := ZRdiv (Z_of_nat (S wz)) 8.
Definition bytesize_chunk_nat (wz:nat) := nat_of_Z (bytesize_chunk wz).
Definition wordsize_chunk (wz:nat) := (bytesize_chunk wz) * 8.

Lemma bytesize_chunk_pos:
  forall wz, bytesize_chunk wz > 0.
Proof.
  intros. unfold bytesize_chunk.
  apply ZRdiv_prop5.
Qed.

Lemma bytesize_chunk_conv:
  forall wz, bytesize_chunk wz = Z_of_nat (bytesize_chunk_nat wz).
Proof.
  intros.
  unfold bytesize_chunk, bytesize_chunk_nat, bytesize_chunk.
  decEq. 
  rewrite nat_of_Z_eq. auto.
    apply ZRdiv_prop2; auto with zarith.
Qed.

Lemma bytesize_chunk_nat_pos:
  forall wz, exists n, bytesize_chunk_nat wz = S n.
Proof.
  intros. 
  generalize (bytesize_chunk_pos wz). rewrite bytesize_chunk_conv. 
  destruct (bytesize_chunk_nat wz).
  simpl; intros; omegaContradiction.
  intros; exists n; auto.
Qed.

Definition size_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint wz => bytesize_chunk wz
  | Mfloat32 => 4
  | Mfloat64 => 8
  end.

Lemma size_chunk_pos:
  forall chunk, size_chunk chunk > 0.
Proof.
  intros. destruct chunk; simpl; try solve [omega | apply bytesize_chunk_pos].
Qed.

Definition size_chunk_nat (chunk: memory_chunk) : nat :=
  nat_of_Z(size_chunk chunk).

Lemma size_chunk_conv:
  forall chunk, size_chunk chunk = Z_of_nat (size_chunk_nat chunk).
Proof.
  intros. destruct chunk; try solve [reflexivity | apply bytesize_chunk_conv].
Qed.

Lemma size_chunk_nat_pos:
  forall chunk, exists n, size_chunk_nat chunk = S n.
Proof.
  intros. 
  generalize (size_chunk_pos chunk). rewrite size_chunk_conv. 
  destruct (size_chunk_nat chunk).
  simpl; intros; omegaContradiction.
  intros; exists n; auto.
Qed.

Lemma size_chunk_nat_pos':
  forall chunk, (size_chunk_nat chunk > 0)%nat.
Proof.
  intros.
  destruct (@size_chunk_nat_pos chunk) as [n J].
  rewrite J. omega.
Qed.

(** Memory reads and writes must respect alignment constraints:
  the byte offset of the location being addressed should be an exact
  multiple of the natural alignment for the chunk being addressed.
  This natural alignment is defined by the following 
  [align_chunk] function.  Some target architectures
  (e.g. the PowerPC) have no alignment constraints, which we could
  reflect by taking [align_chunk chunk = 1].  However, other architectures
  have stronger alignment requirements.  The following definition is
  appropriate for PowerPC and ARM. *)

Definition align_chunk (chunk: memory_chunk) : Z := 
  match chunk with
  | Mint wz => 
    if le_lt_dec wz 31
    then bytesize_chunk wz
    else 4
  | _ => 4
  end.

Lemma align_chunk_pos:
  forall chunk, align_chunk chunk > 0.
Proof.
  intro. destruct chunk; simpl; try omega.
    destruct (le_lt_dec n 31); try omega.
      apply bytesize_chunk_pos.
Qed.

(*
Lemma align_size_chunk_divides:
  forall chunk, (align_chunk chunk | size_chunk chunk).
Proof.
  intros. destruct chunk; simpl; try solve [
    apply Zdivide_refl |
    destruct (le_lt_dec n 3); auto with zarith |
    exists 2; auto ]. 

    destruct (le_lt_dec n 3); auto with zarith.
Qed.
*)

Lemma bytesize_chunk_7_eq_1 : bytesize_chunk 7 = 1.
Proof.
  unfold bytesize_chunk.
  unfold ZRdiv. compute. auto.
Qed.

Lemma bytesize_chunk_31_eq_4 : bytesize_chunk 31 = 4.
Proof.
  unfold bytesize_chunk.
  unfold ZRdiv. compute. auto.
Qed.

Lemma bytesize_chunk_63_eq_8 : bytesize_chunk 63 = 8.
Proof.
  unfold bytesize_chunk.
  unfold ZRdiv. compute. auto.
Qed.

Lemma bytesize_chunk_le_31 : forall n,
  (n <= 31)%nat ->
  bytesize_chunk n <= 4.
Proof.
  unfold bytesize_chunk.
  unfold ZRdiv.
  intros.
  destruct n.
    compute. intro. inversion H0.
Admitted.

Lemma bytesize_chunk_gt_31 : forall n,
  (31 < n)%nat ->
  bytesize_chunk n > 4.
Proof.
Admitted.

Lemma bytesize_chunk_31_neq : forall n1 n2,
  (n1 <= 31 < n2)%nat ->
  bytesize_chunk n1 <> bytesize_chunk n2.
Proof.
  intros.
  destruct H.
  apply bytesize_chunk_le_31 in H.
  apply bytesize_chunk_gt_31 in H0.
  omega.
Qed.

Lemma bytesize_chunk_31_neq' : forall n1 n2,
  (n1 <= 31 < n2)%nat ->
  bytesize_chunk n2 <> bytesize_chunk n1.
Proof.
  intros.
  destruct H.
  apply bytesize_chunk_le_31 in H.
  apply bytesize_chunk_gt_31 in H0.
  omega.
Qed.

Lemma align_chunk_compat:
  forall chunk1 chunk2,
  size_chunk chunk1 = size_chunk chunk2 -> align_chunk chunk1 = align_chunk chunk2.
Proof.
  intros chunk1 chunk2. 
  destruct chunk1; destruct chunk2; simpl; try congruence; auto.
    destruct (le_lt_dec n 31); auto.
      destruct (le_lt_dec n0 31); auto.
        intro. contradict H; auto using bytesize_chunk_31_neq.
      destruct (le_lt_dec n0 31); auto.
        intro. contradict H; auto using bytesize_chunk_31_neq'.

    destruct (le_lt_dec n 31); auto.

    destruct (le_lt_dec n 31); auto.
      apply bytesize_chunk_le_31 in l.
      intro. rewrite H in l. contradict l; auto.

    destruct (le_lt_dec n 31); auto.

    destruct (le_lt_dec n 31); auto.
      apply bytesize_chunk_le_31 in l.
      intro. rewrite <- H in l. contradict l; auto.
Qed.

Definition chunk_eq (c1 c2:memory_chunk) : Prop :=
  size_chunk c1 = size_chunk c2 /\
  match c1, c2 with
  | Mint wz1, Mint wz2 => wz1 = wz2
  | _, _ => True
  end.

Lemma chunk_eq_refl : forall c, chunk_eq c c.
Proof.
  destruct c; split; auto.
Qed.

(** * Memory values *)

(** A ``memory value'' is a byte-sized quantity that describes the current
  content of a memory cell.  It can be either:
- a concrete 8-bit integer;
- a byte-sized fragment of an opaque pointer;
- the special constant [Undef] that represents uninitialized memory.
*)

(** Values stored in memory cells. *)

Inductive memval: Type :=
  | Undef: memval
  | Byte: nat -> byte -> memval
  | Pointer: block -> int32 -> nat -> memval.

(** * Encoding and decoding integers *)

(** We define functions to convert between integers and lists of bytes
  according to a given memory chunk. *)

(** bytes_of_int *)

Fixpoint bytes_of_int (n: nat) (x: Z) {struct n}: list byte :=
  match n with
  | O => nil
  | S m => Int.repr 7 x :: bytes_of_int m (x / 256)
  end.

Lemma length_bytes_of_int:
  forall n x, length (bytes_of_int n x) = n.
Proof.
  induction n; simpl; intros. auto. decEq. auto.
Qed.

Lemma bytes_of_int_mod:
  forall n x y,
  Int.eqmod (two_p (Z_of_nat n * 8)) x y ->
  bytes_of_int n x = bytes_of_int n y.
Proof.
  induction n.
  intros; simpl; auto.
  intros until y.
  rewrite inj_S. 
  replace (Zsucc (Z_of_nat n) * 8) with (Z_of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega. 
  intro EQM.
  simpl; decEq. 
  apply (Int.eqm_samerepr 7). red. 
  eapply Int.eqmod_divides; eauto. apply Zdivide_factor_l.
  apply IHn.
  destruct EQM as [k EQ]. exists k. rewrite EQ. 
  rewrite <- Z_div_plus_full_l. decEq. change (two_p 8) with 256. ring. omega.
Qed.

Lemma bytes_of_int_mod':
  forall z x y,
  z >= 0 ->
  Int.eqmod (two_p (z * 8)) x y ->
  bytes_of_int (nat_of_Z z) x =
  bytes_of_int (nat_of_Z z) y.
Proof.
  intros.
  rewrite <- (@nat_of_Z_eq z) in H0; auto.
  apply bytes_of_int_mod; auto.
Qed.

Lemma bytes_of_int_prop1: forall n z,
  (n > 0)%nat ->
  exists b, exists bl, 
    bytes_of_int n z = b::bl.
Proof. 
  destruct n; intros.
    contradict H; omega.

    simpl.
    exists (Int.repr 7 z).
    exists (bytes_of_int n (z/256)).
    auto.
Qed.

(** int_of_bytes *)

Fixpoint int_of_bytes (l: list byte): Z :=
  match l with
  | nil => 0
  | b :: l' => Int.unsigned 7 b + int_of_bytes l' * 256
  end.

Lemma int_of_bytes_of_int:
  forall n x,
  int_of_bytes (bytes_of_int n x) = x mod (two_p (Z_of_nat n * 8)).
Proof.
  induction n; intros.
  simpl. rewrite Zmod_1_r. auto.
  rewrite inj_S. simpl.
  replace (Zsucc (Z_of_nat n) * 8) with (Z_of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega. 
  rewrite Zmod_recombine. rewrite IHn. rewrite Zplus_comm. reflexivity. 
  apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
Qed.

Lemma int_of_bytes_of_int_wz:
  forall n wz x,
  0 < Z_of_nat n ->
  Int.repr wz (int_of_bytes (bytes_of_int n (Int.unsigned wz x))) = 
  Int.zero_ext wz (Z_of_nat n * 8) x.
Proof.
  intros. rewrite int_of_bytes_of_int. 
  rewrite <- (Int.repr_unsigned wz (Int.zero_ext wz (Z_of_nat n * 8) x)). 
  decEq. symmetry. apply Int.zero_ext_mod; try solve [omega]. 
Qed.

Lemma int_of_bytes_of_int_2:
  forall n x,
  (n = 1 \/ n = 2)%nat ->
  Int.repr 31 (int_of_bytes (bytes_of_int n (Int.unsigned 31 x))) = Int.zero_ext 31 (Z_of_nat n * 8) x.
Proof.
  intros. apply int_of_bytes_of_int_wz.
  destruct H; subst n; compute; auto.
Qed.

Definition inj_bytes (bl: list byte) : list memval :=
  List.map (Byte 8) bl.

Remark length_inj_bytes:
  forall bl, length (inj_bytes bl) = length bl.
Proof.
  intros. apply List.map_length. 
Qed.

(** inj_int *)

Definition inj_int (wz:nat) (x: Int.int wz) : list memval :=
  let z := Int.unsigned wz x in
  let n := Z_of_nat (S wz) in
  let m := n mod 8 in
  let sz := ZRdiv n 8 in
  let bl := bytes_of_int (nat_of_Z sz) z in
  match bl with
  | nil => nil
  | b::bl' => Byte (nat_of_Z m) b :: inj_bytes bl'
  end.

Lemma length_inj_int : forall wz n,
  length (inj_int wz n) = bytesize_chunk_nat wz.
Proof.
  intros.
  unfold inj_int, bytesize_chunk_nat, bytesize_chunk.
  assert (J:=@length_bytes_of_int 
    (nat_of_Z (ZRdiv (Z_of_nat (S wz)) 8)) 
    (Int.unsigned wz n)).
  remember (bytes_of_int (nat_of_Z (ZRdiv (Z_of_nat (S wz)) 8)) 
    (Int.unsigned wz n)) as bl.
  destruct bl; auto.
    simpl in *.
    rewrite <- J.
    decEq.
    apply map_length.
Qed.   

(** proj_bytes *)

Fixpoint proj_bytes (n:nat) (vl: list memval) {struct n} : option (list byte) :=
  match n, vl with
  | O, nil => Some nil
  | S m, Byte wz b :: vl' =>
      if eq_nat_dec wz 8 
      then
        match (proj_bytes m vl') with
        | Some bl' => Some (b :: bl')
        | None => None
        end
      else None
  | _, _ => None
  end.

Remark proj_inj_bytes:
  forall bl, proj_bytes (length bl) (inj_bytes bl) = Some bl.
Proof.
  induction bl; simpl. auto. rewrite IHbl. auto.
Qed.

Lemma inj_proj_bytes:
  forall cl bl, proj_bytes (length cl) cl = Some bl -> cl = inj_bytes bl.
Proof.
  induction cl; simpl; intros. 
  inv H; auto.
  destruct a; try congruence.
  destruct (eq_nat_dec n 8); subst.
    destruct (proj_bytes (length cl) cl); inv H.
      simpl. decEq. auto.
      inversion H.
Qed.

Lemma proj_bytes_prop1 : forall n wz x bl,
  proj_bytes n (map (Byte 8) (bytes_of_int n (Int.unsigned wz x / 256))) = Some bl ->
  x = Int.repr wz (Int.unsigned wz x mod Int.modulus 7 + int_of_bytes bl * 256).
Proof.
  intros.
  
Admitted.

Lemma proj_bytes_prop2: forall vl n,
  length vl = n ->
  exists bl, proj_bytes n (map (Byte 8) vl) = Some bl.
Proof.
  induction vl; intros; subst; simpl.
    exists nil. auto.
    
    destruct (@IHvl (length vl)) as [bl J]; auto.
    rewrite J.
    exists (a::bl). auto.
Qed.

Lemma proj_bytes_prop3: forall vl n bl,
  proj_bytes n (map (Byte 8) vl) = Some bl ->
  length bl = n /\ length vl = n.
Admitted.

(** proj_int *)

Definition proj_int (wz:nat) (vl: list memval) : option (Int.int wz) :=
  let n := Z_of_nat (S wz) in
  let m := nat_of_Z (n mod 8) in
  let sz := nat_of_Z (ZRdiv n 8) in
  match sz, vl with
  | O, nil => None
  | S n', Byte wz0 b :: vl' =>
    if eq_nat_dec wz0 m
    then 
      match (proj_bytes n' vl') with
      | Some bl' => Some (Int.repr wz (int_of_bytes (b::bl')))
      | None => None
      end
    else None
  | _, _ => None
  end.

Lemma proj_inj_int_eq : 
  forall wz x,
  proj_int wz (inj_int wz x) = Some x.
Proof.
  intros.
  unfold proj_int, inj_int.
  remember (nat_of_Z (ZRdiv (Z_of_nat (S wz)) 8)) as n.
  assert (n > 0)%nat.
    subst.
    apply ZRdiv_prop6.
  Opaque Z_of_nat.
  destruct n; simpl.
    contradict H; omega.

    destruct (eq_nat_dec 
      (nat_of_Z ((Z_of_nat (S wz)) mod 8))
      (nat_of_Z ((Z_of_nat (S wz)) mod 8))
      ).
      destruct (@proj_bytes_prop2 (bytes_of_int n (Int.unsigned wz x/256)) n) 
        as [bl EQ].
        apply length_bytes_of_int.
        unfold inj_bytes.
        rewrite EQ. 

        apply proj_bytes_prop1 in EQ. rewrite <- EQ. auto.
      contradict n0; auto.
Qed.

Lemma proj_inj_int_neq : 
  forall wz1 wz2 x,
  wz1 <> wz2 ->
  proj_int wz1 (inj_int wz2 x) = None.
Proof.
  intros.
  unfold proj_int, inj_int.
  remember (nat_of_Z (ZRdiv (Z_of_nat (S wz1)) 8)) as n.
  assert (n > 0)%nat.
    subst.
    apply ZRdiv_prop6.
  Opaque Z_of_nat.
  destruct n; simpl.
    contradict H; omega.
    destruct (@bytes_of_int_prop1 
      (nat_of_Z (ZRdiv (Z_of_nat (S wz2)) 8))
      (Int.unsigned wz2 x))
      as [b [bl EQ]].
      apply ZRdiv_prop6.
    rewrite EQ.      

    unfold inj_bytes.
    destruct (eq_nat_dec 
      (nat_of_Z ((Z_of_nat (S wz2)) mod 8))
      (nat_of_Z ((Z_of_nat (S wz1)) mod 8))
      ); auto.
      apply nat_of_Z_inj in e; try solve [apply mod_prop1].
        remember (proj_bytes n (map (Byte 8) bl)) as R.
        destruct R; auto.
          symmetry in HeqR.
          apply proj_bytes_prop3 in HeqR.
          destruct HeqR as [EQ1 EQ2]; subst.
          assert(J:=@length_bytes_of_int (nat_of_Z (ZRdiv (Z_of_nat (S wz2)) 8)) (Int.unsigned wz2 x)).
          rewrite EQ in J.
          simpl in J. rewrite EQ2 in J.
          rewrite Heqn in J.
          apply nat_of_Z_inj in J; try solve [apply ZRdiv_prop4].
            apply zrdiv_zmod_prop1 in J; auto with zarith.
              apply inj_eq_rev in J; auto.
              inversion J; subst.        
              contradict H; auto.
Qed.

Parameter big_endian: bool.

Definition rev_if_be (A:Type) (l: list A) : list A :=
  if big_endian then List.rev l else l.

Lemma rev_if_be_involutive:
  forall A l, rev_if_be A (rev_if_be A l) = l.
Proof.
  intros; unfold rev_if_be; destruct big_endian. 
  apply List.rev_involutive. 
  auto.
Qed.

Lemma rev_if_be_length:
  forall A l, length (rev_if_be A l) = length l.
Proof.
  intros; unfold rev_if_be; destruct big_endian.
  apply List.rev_length.
  auto.
Qed.

(* generate the stored bytes of x (with size wz). *)
Definition encode_int (wz:nat) (x: Int.int wz) : list memval :=
  rev_if_be _ (inj_int wz x).

Definition decode_int (b: list memval) (wz:nat) : val :=
  let b' := rev_if_be _ b in
  match (proj_int wz b') with
  | Some i => Vint wz i
  | None => Vundef
  end.

Lemma encode_int_length:
  forall wz n, length(encode_int wz n) = bytesize_chunk_nat wz.
Proof.
  intros. unfold encode_int. rewrite rev_if_be_length.
  apply length_inj_int.
Qed.

Lemma decode_encode_int_eq:
  forall wz x,
  decode_int (encode_int wz x) wz = Vint wz x.
Proof.
  intros. unfold decode_int, encode_int; auto;
  rewrite rev_if_be_involutive.

  rewrite proj_inj_int_eq. auto.
Qed.

Lemma decode_encode_int_neq:
  forall wz1 wz2 x,
  wz1 <> wz2 ->
  decode_int (encode_int wz1 x) wz2 = Vundef.
Proof.
  intros. unfold decode_int, encode_int; auto;
  rewrite rev_if_be_involutive.

  rewrite proj_inj_int_neq; auto.
Qed.

Remark encode_mod:
  forall wz x y, 
  Int.eqmod (two_p (wordsize_chunk wz)) (Int.unsigned wz x) (Int.unsigned wz y) ->
  encode_int wz x = encode_int wz y.
Proof.
  intros. unfold encode_int. decEq.
  unfold inj_int.
  unfold wordsize_chunk in H. 
  unfold bytesize_chunk in H.
  apply bytes_of_int_mod' in H; try solve [apply ZRdiv_prop4].
  rewrite H. auto.
Qed.

(** * Encoding and decoding floats *)

Definition encode_float (c: memory_chunk) (f: float) : list byte :=
  rev_if_be _ (match c with
  | Mint wz => bytes_of_int (bytesize_chunk_nat wz) 0
  | Mfloat32 => bytes_of_int 4%nat (Int.unsigned 31 (Float.bits_of_single f))
  | Mfloat64 => bytes_of_int 8%nat (Int.unsigned 63 (Float.bits_of_double f))
  end).

Definition decode_float (c: memory_chunk) (b: list byte) : float :=
  let b' := rev_if_be _ b in
  match c with
  | Mfloat32 => Float.single_of_bits (Int.repr 31 (int_of_bytes b'))
  | Mfloat64 => Float.double_of_bits (Int.repr 63 (int_of_bytes b'))
  | _ => Float.zero
  end.

Lemma encode_float_length:
  forall chunk n, length(encode_float chunk n) = size_chunk_nat chunk.
Proof.
  unfold encode_float; intros. 
  rewrite rev_if_be_length. 
  destruct chunk; try solve [
    apply length_bytes_of_int |
    unfold size_chunk_nat, size_chunk;
      rewrite Z_of_nat_eq; apply length_bytes_of_int].
Qed.

Lemma decode_encode_float32: forall n,
  decode_float Mfloat32 (encode_float Mfloat32 n) = Float.singleoffloat n.
Proof.
  intros; unfold decode_float, encode_float. 
  rewrite rev_if_be_involutive. 
  rewrite int_of_bytes_of_int. rewrite <- Float.single_of_bits_of_single. 
  decEq. 
  transitivity (Int.repr 31 (Int.unsigned 31 (Float.bits_of_single n))). 
  apply Int.eqm_samerepr. apply Int.eqm_sym. apply Int.eqmod_mod. apply two_p_gt_ZERO. omega. 
  apply Int.repr_unsigned.
Qed.

Lemma decode_encode_float64: forall n,
  decode_float Mfloat64 (encode_float Mfloat64 n) = n.
Proof.
  intros; unfold decode_float, encode_float. 
  rewrite rev_if_be_involutive. 
  rewrite int_of_bytes_of_int.
  set (x := Float.bits_of_double n).
  transitivity (Float.double_of_bits(Int.repr 63 (Int.unsigned 63 x))).
  decEq. 
  apply Int.eqm_samerepr. apply Int.eqm_sym. apply Int.eqmod_mod. apply two_p_gt_ZERO. omega. 
  rewrite Int.repr_unsigned. apply Float.double_of_bits_of_double.
Qed.

Lemma encode_float32_cast:
  forall f,
  encode_float Mfloat32 (Float.singleoffloat f) = encode_float Mfloat32 f.
Proof.
  intros; unfold encode_float. decEq. decEq. decEq. 
  apply Float.bits_of_singleoffloat.
Qed.

Lemma decode_float32_cast:
  forall l,
  Float.singleoffloat (decode_float Mfloat32 l) = decode_float Mfloat32 l.
Proof.
  intros; unfold decode_float. rewrite Float.singleoffloat_of_bits. auto.
Qed.

(** * Encoding and decoding values *)

Fixpoint inj_pointer (n: nat) (b: block) (ofs: Int.int 31) {struct n}: list memval :=
  match n with
  | O => nil
  | S m => Pointer b ofs m :: inj_pointer m b ofs
  end.

Fixpoint check_pointer (n: nat) (b: block) (ofs: Int.int 31) (vl: list memval) 
                       {struct n} : bool :=
  match n, vl with
  | O, nil => true
  | S m, Pointer b' ofs' m' :: vl' =>
      eq_block b b' && Int.eq_dec 31 ofs ofs' && beq_nat m m' && check_pointer m b ofs vl'
  | _, _ => false
  end.

Definition proj_pointer (vl: list memval) : val :=
  match vl with
  | Pointer b ofs n :: vl' =>
      if check_pointer (size_chunk_nat Mint32) b ofs vl
      then Vptr b ofs
      else Vundef
  | _ => Vundef
  end.

Lemma inj_pointer_length:
  forall b ofs n, List.length(inj_pointer n b ofs) = n.
Proof.
  induction n; simpl; congruence.
Qed.

Lemma check_inj_pointer:
  forall b ofs n, check_pointer n b ofs (inj_pointer n b ofs) = true.
Proof.
  induction n; simpl. auto. 
  unfold proj_sumbool. rewrite dec_eq_true. rewrite dec_eq_true.  
  rewrite <- beq_nat_refl. simpl; auto.
Qed.

Definition encode_val (chunk: memory_chunk) (v: val) : list memval :=
  match v, chunk with
  | Vptr b ofs, Mint wz => 
    if eq_nat_dec wz 31 
    then inj_pointer (size_chunk_nat (Mint wz)) b ofs
    else list_repeat (size_chunk_nat chunk) Undef
  | Vint wz n, Mint wz' =>
    if eq_nat_dec wz wz' 
    then encode_int wz n
    else list_repeat (size_chunk_nat chunk) Undef
  | Vfloat f, _ => inj_bytes (encode_float chunk f)
  | _, _ => list_repeat (size_chunk_nat chunk) Undef
  end.

Definition decode_val (chunk: memory_chunk) (vl: list memval) : val :=
  match chunk with
  | Mint wz => 
    match decode_int vl wz with
    | Vundef => if eq_nat_dec wz 31 then proj_pointer vl else Vundef
    | v => v
    end
  | Mfloat32 =>
    match proj_bytes (bytesize_chunk_nat 31) vl with
    | Some bl => Vfloat(decode_float chunk bl)
    | None => Vundef
    end
  | Mfloat64 =>
    match proj_bytes (bytesize_chunk_nat 63) vl with
    | Some bl => Vfloat(decode_float chunk bl)
    | None => Vundef
    end
  end.

Lemma encode_val_length:
  forall chunk v, length (encode_val chunk v) = size_chunk_nat chunk.
Proof.
  intros. destruct v; simpl.

  apply length_list_repeat.

  destruct chunk; simpl; unfold size_chunk_nat, size_chunk; auto with zarith.
  destruct (eq_nat_dec wz n); subst.
    apply encode_int_length.
    apply length_list_repeat.

  rewrite length_inj_bytes. apply encode_float_length.

  destruct chunk; simpl; unfold size_chunk_nat, size_chunk; auto.
    destruct (eq_nat_dec n 31); subst.
      apply inj_pointer_length.
      apply length_list_repeat.
Qed.

Definition decode_encode_val (v1: val) (chunk1 chunk2: memory_chunk) (v2: val) : Prop :=
  match v1, chunk1, chunk2 with
  | Vundef, _, _ => v2 = Vundef

  | Vint wz n, Mint wz1, Mint wz2 => 
    if eq_nat_dec wz wz1
    then 
      if eq_nat_dec wz wz2
      then v2 = Vint wz n
      else v2 = Vundef
    else v2 = Vundef
  | Vint wz n, Mint wz', Mfloat32 => 
    if eq_nat_dec wz 31
    then 
      if eq_nat_dec wz' 31
      then 
        match (proj_bytes (bytesize_chunk_nat wz) (encode_int wz n)) with
        | Some bl => v2 = Vfloat(decode_float Mfloat32 bl)
        | None => False
        end
      else True
    else True
  | Vint wz n, _, _ => True   (* nothing interesting to say about v2 *)

  | Vptr b ofs, Mint wz1, Mint wz2 => 
    if eq_nat_dec wz1 31
    then 
      if eq_nat_dec wz2 31
      then v2 = Vptr b ofs
      else v2 = Vundef
    else v2 = Vundef
  | Vptr b ofs, _, _ => v2 = Vundef

  | Vfloat f, Mfloat32, Mfloat32 => v2 = Vfloat(Float.singleoffloat f)
  | Vfloat f, Mfloat32, Mint wz => 
    if eq_nat_dec wz 31
    then v2 = decode_int (inj_bytes (encode_float Mfloat32 f)) 31
    else True
  | Vfloat f, Mfloat64, Mfloat64 => v2 = Vfloat f
  | Vfloat f, _, _ => True   (* nothing interesting to say about v2 *)
  end.

Remark proj_bytes_undef:
  forall n, (n > 0)%nat -> proj_bytes n (list_repeat n Undef) = None.
Proof.
  induction n; simpl; intro; auto.
    contradict H; omega.
Qed.

Remark proj_pointer_undef':
  forall n, proj_pointer (list_repeat n Undef) = Vundef.
Proof.
  induction n; simpl; auto.
Qed.

Lemma list_repeat_cons_inv : forall m a b,
  a :: b = list_repeat m Undef ->
  a = Undef /\
  exists m', S m' = m /\ b = list_repeat m' Undef.
Proof.
  induction m; intros; simpl in *.
    inversion H.

    inversion H; subst.
    split; auto.
    exists m. split; auto.
Qed.

Lemma proj_int_undef : forall n m,
  proj_int n (list_repeat m Undef) = None.
Proof.
  intros.
  unfold proj_int.
  remember (nat_of_Z (ZRdiv (Z_of_nat (S n)) 8)) as N.
  induction N; simpl.
    destruct (list_repeat m Undef); auto.

    remember (list_repeat m Undef) as L.
    destruct L; auto.
      apply list_repeat_cons_inv in HeqL.
      destruct HeqL as [H1 [m' [H2 H3]]]; subst; auto.
Qed.      

Lemma list_repeat_undef : forall n,
  list_repeat n Undef ++ Undef :: nil =
  Undef :: list_repeat n Undef.
Proof.
  induction n; simpl; auto.
    rewrite IHn. auto.
Qed.

Lemma rev_if_be_nil : forall (A:Type), rev_if_be A nil = nil.
Proof.
  unfold rev_if_be.
  destruct big_endian; auto.
Qed.

Lemma rev_if_be_repeat_undef : forall n,
  rev_if_be _ (list_repeat n Undef) = list_repeat n Undef.
Proof.
  induction n; simpl.
    apply rev_if_be_nil.

    unfold rev_if_be in *.
    destruct big_endian; auto.
      simpl.
      rewrite IHn. auto.
      apply list_repeat_undef.
Qed.

Lemma proj_pointer_encode_int : forall wz i,
  proj_pointer (encode_int wz i) = Vundef.
Proof.
  intros.
  unfold proj_pointer, encode_int, inj_int.
  destruct (bytes_of_int (nat_of_Z (ZRdiv (Z_of_nat (S wz)) 8)) (Int.unsigned wz i)); simpl; auto.
    rewrite rev_if_be_nil. auto.
Admitted.

Lemma decode_int_repeat_Undef : forall n m,
  decode_int (list_repeat n Undef) m = Vundef.
Proof.
  intros.
  unfold decode_int.
  rewrite rev_if_be_repeat_undef.
  rewrite proj_int_undef. auto.
Qed.

Lemma proj_bytes_encode_int32 : forall i,
  exists bl, proj_bytes (bytesize_chunk_nat 31) (encode_int 31 i) = Some bl.
Admitted.

Lemma decode_int_encode_float32 : forall f,
  exists i, decode_int (inj_bytes (encode_float Mfloat32 f)) 31 = Vint 31 i.
Admitted.

Lemma proj_bytes_encode_float32 : forall f,
  exists bl, proj_bytes (bytesize_chunk_nat 31) (inj_bytes (encode_float Mfloat32 f)) = Some bl.
Admitted.      

Lemma proj_bytes_encode_float64 : forall f,
  exists bl, proj_bytes (bytesize_chunk_nat 63) (inj_bytes (encode_float Mfloat64 f)) = Some bl.
Admitted.      

Lemma encode_float32_length : forall f,
  length (encode_float Mfloat32 f) = bytesize_chunk_nat 31.
Admitted.

Lemma encode_float64_length : forall f,
  length (encode_float Mfloat64 f) = bytesize_chunk_nat 63.
Admitted.

Lemma decode_int_inj_pointer:
  forall b ofs, 
  decode_int (inj_pointer (size_chunk_nat Mint32) b ofs) 31 = Vptr b ofs.
Proof.
Admitted.

Lemma decode_int_inj_pointer_undef:
  forall b ofs n, 
  n <> 31%nat ->
  decode_int (inj_pointer (size_chunk_nat Mint32) b ofs) n = Vundef.
Proof.
Admitted.

Remark proj_bytes_undef':
  forall n m, (m > 0)%nat -> proj_bytes n (list_repeat m Undef) = None.
Proof.
  induction n; simpl; intros; auto.
Admitted.

Lemma decode_encode_val_general:
  forall v chunk1 chunk2,
  decode_encode_val v chunk1 chunk2 (decode_val chunk2 (encode_val chunk1 v)).
Proof.
  intros. destruct v.
(* Vundef *)
  simpl. destruct (size_chunk_nat_pos chunk1) as [psz EQ]. 
  rewrite EQ. simpl.
  unfold decode_val. simpl. destruct chunk2; auto.
  change (Undef::list_repeat psz Undef) with (list_repeat (S psz) Undef).
  rewrite decode_int_repeat_Undef.
  destruct (eq_nat_dec n 31); subst; auto.
(* Vint *)
  simpl.
  destruct chunk1; auto; destruct chunk2; auto; unfold decode_val, encode_val; 
  try rewrite proj_inj_bytes.

    destruct (eq_nat_dec wz n); subst; auto.
      destruct (eq_nat_dec n n0); subst; auto.
        rewrite decode_encode_int_eq; auto.
        rewrite decode_encode_int_neq; auto.
        destruct (eq_nat_dec n0 31); subst; auto.
          apply proj_pointer_encode_int.
      rewrite decode_int_repeat_Undef.
      destruct (eq_nat_dec n0 31); subst; auto.
        apply proj_pointer_undef'.
      
    destruct (eq_nat_dec wz 31); subst; auto.
      destruct (eq_nat_dec n 31); subst; auto.
        destruct (eq_nat_dec 31 31); subst.
          destruct (@proj_bytes_encode_int32 i) as [bl EQ].
          rewrite EQ.
          simpl. auto.
          
          contradict n; auto.
(* Vfloat *)
  unfold decode_val, encode_val, decode_encode_val;
  destruct chunk1; auto; destruct chunk2; auto; unfold decode_val.

    destruct (eq_nat_dec n 31); subst; auto.
      destruct (@decode_int_encode_float32 f) as [i EQ].
      rewrite EQ. auto.

      destruct (@proj_bytes_encode_float32 f) as [bl EQ].
      rewrite EQ. simpl.
      decEq.
      rewrite <- decode_encode_float32.
      unfold decode_float.
      rewrite <- (encode_float32_length f) in EQ.
      rewrite proj_inj_bytes in EQ.
      inversion EQ; subst; auto.

    destruct (@proj_bytes_encode_float64 f) as [bl EQ].
    rewrite EQ. simpl.
    decEq.
    rewrite <- decode_encode_float64.
    unfold decode_float.
    rewrite <- (encode_float64_length f) in EQ.
    rewrite proj_inj_bytes in EQ.
    inversion EQ; subst; auto.

(* Vptr *)
  unfold decode_val, encode_val, decode_encode_val;
  destruct chunk1; auto; destruct chunk2; auto.

    destruct (eq_nat_dec n 31); subst; auto.
      destruct (eq_nat_dec n0 31); subst; auto.
        rewrite decode_int_inj_pointer; auto.
        rewrite decode_int_inj_pointer_undef; auto.

      rewrite decode_int_repeat_Undef.
      destruct (eq_nat_dec n0 31); subst; auto.
        rewrite proj_pointer_undef'; auto.

    destruct (eq_nat_dec n 31); subst; auto.
      rewrite proj_bytes_undef'; auto using size_chunk_nat_pos'.

    destruct (eq_nat_dec n 31); subst; auto.
      rewrite proj_bytes_undef'; auto using size_chunk_nat_pos'.

    rewrite decode_int_repeat_Undef.
    destruct (eq_nat_dec n 31); subst; auto.
   
    rewrite decode_int_repeat_Undef.
    destruct (eq_nat_dec n 31); subst; auto.
Qed.

Lemma decode_encode_val_similar:
  forall v1 chunk1 chunk2 v2,
  type_of_chunk chunk1 = type_of_chunk chunk2 ->
  chunk_eq chunk1 chunk2 ->
  Val.has_type v1 (type_of_chunk chunk1) ->
  decode_encode_val v1 chunk1 chunk2 v2 ->
  v2 = Val.load_result chunk2 v1.
Proof.
  intros. 
  destruct v1.
  simpl in *. destruct chunk2; simpl; auto.
 
  red in H1.
  destruct chunk1; simpl in H1; try contradiction;
  destruct chunk2; simpl in *; discriminate || auto.
  destruct (eq_nat_dec wz n); subst.
    destruct (eq_nat_dec n n0); subst.
      destruct (eq_nat_dec n0 n0); subst; auto.
        contradict n; auto.
      destruct (eq_nat_dec n0 n); subst; auto.
        contradict n1; auto.
    destruct (eq_nat_dec n0 wz); subst; auto.
      unfold chunk_eq in H0.
      destruct H0; subst.
      contradict n1; auto.

  unfold chunk_eq in H0. destruct H0.
  red in H1.
  destruct chunk1; simpl in H1; try contradiction;
  destruct chunk2; simpl in *; discriminate || auto.
    
  unfold chunk_eq in H0. destruct H0.
  red in H1.
  destruct chunk1; simpl in H1; try contradiction;
  destruct chunk2; simpl in *; discriminate || auto.
  subst.
  destruct (eq_nat_dec n0 31); subst; auto.
Qed.

Lemma decode_val_type:
  forall chunk cl,
  Val.has_type (decode_val chunk cl) (type_of_chunk chunk).
Proof.
  intros. unfold decode_val.
  destruct chunk; simpl; auto. 

    unfold decode_int.
    destruct (proj_int n (rev_if_be memval cl)); simpl; auto.
      destruct (eq_nat_dec n 31); simpl; auto.
        unfold proj_pointer.
        destruct cl; simpl; auto.
          destruct m; simpl; auto.
            destruct (check_pointer (size_chunk_nat Mint32) b i (Pointer b i n0::cl)); simpl; auto.

    destruct (proj_bytes (bytesize_chunk_nat 31) cl); simpl; auto.
    destruct (proj_bytes (bytesize_chunk_nat 63) cl); simpl; auto.
Qed.

(*
Lemma encode_val_int8_signed_unsigned:
  forall v, encode_val Mint8signed v = encode_val Mint8unsigned v.
Proof.
  intros. destruct v; simpl; auto.
Qed.

Lemma encode_val_int16_signed_unsigned:
  forall v, encode_val Mint16signed v = encode_val Mint16unsigned v.
Proof.
  intros. destruct v; simpl; auto.
Qed.

Lemma encode_val_int8_zero_ext:
  forall n, encode_val Mint8unsigned (Vint (Int.zero_ext 8 n)) = encode_val Mint8unsigned (Vint n).
Proof.
  intros; unfold encode_val. rewrite encode_int8_zero_ext. auto.
Qed.

Lemma encode_val_int8_sign_ext:
  forall n, encode_val Mint8signed (Vint (Int.sign_ext 8 n)) = encode_val Mint8signed (Vint n).
Proof.
  intros; unfold encode_val. rewrite encode_int8_sign_ext. auto.
Qed.

Lemma encode_val_int16_zero_ext:
  forall n, encode_val Mint16unsigned (Vint (Int.zero_ext 16 n)) = encode_val Mint16unsigned (Vint n).
Proof.
  intros; unfold encode_val. rewrite encode_int16_zero_ext. auto.
Qed.

Lemma encode_val_int16_sign_ext:
  forall n, encode_val Mint16signed (Vint (Int.sign_ext 16 n)) = encode_val Mint16signed (Vint n).
Proof.
  intros; unfold encode_val. rewrite encode_int16_sign_ext. auto.
Qed.
*)

Lemma decode_val_int_inv:
  forall chunk cl n i,
  decode_val chunk cl = Vint n i ->
  type_of_chunk chunk = Tint /\
  Vint n i = decode_int cl n.
Proof.
  intros until i. unfold decode_val.
  destruct chunk; intro EQ.
    remember (decode_int cl n0) as R.
    unfold decode_int in HeqR.
    remember (proj_int n0 (rev_if_be memval cl)) as R'.
    split. simpl. auto.
      unfold decode_int.
      destruct R'; subst.
        inversion EQ; subst.
        rewrite <- HeqR'. auto.

        destruct (eq_nat_dec n0 31); subst; try solve [inversion EQ].
          unfold proj_pointer in EQ.
          destruct cl; try solve [inversion EQ].
          destruct m; try solve [inversion EQ].
          destruct (check_pointer (size_chunk_nat Mint32) b i0 (Pointer b i0 n0::cl)); try solve [inversion EQ].

    destruct (proj_bytes (bytesize_chunk_nat 31) cl); subst; try solve [inversion EQ].
    destruct (proj_bytes (bytesize_chunk_nat 63) cl); subst; try solve [inversion EQ].
Qed.

Lemma decode_val_float_inv:
  forall chunk cl f,
  decode_val chunk cl = Vfloat f ->
  type_of_chunk chunk = Tfloat /\
  exists bl, proj_bytes (size_chunk_nat chunk) cl = Some bl /\ f = decode_float chunk bl.
Proof.
  intros until f. unfold decode_val. 
  destruct chunk; intro EQ.
    remember (decode_int cl n) as R.
    unfold decode_int in HeqR.
    remember (proj_int n (rev_if_be memval cl)) as R'.
    destruct R'; subst; try solve [inversion EQ].
      destruct (eq_nat_dec n 31); subst; try solve [inversion EQ].
        unfold proj_pointer in EQ.
        destruct cl; try solve [inversion EQ].
        destruct m; try solve [inversion EQ].
        destruct (check_pointer (size_chunk_nat Mint32) b i (Pointer b i n::cl)); try solve [inversion EQ].

    remember (proj_bytes (bytesize_chunk_nat 31) cl) as R.
    destruct R; subst; try solve [inversion EQ].
    split; auto.
      unfold decode_float in EQ.
      inversion EQ; subst.
      exists l. split; auto.

    remember (proj_bytes (bytesize_chunk_nat 63) cl) as R.
    destruct R; subst; try solve [inversion EQ].
    split; auto.
      unfold decode_float in EQ.
      inversion EQ; subst.
      exists l. split; auto.
Qed.

Lemma decode_val_cast:
  forall chunk l,
  let v := decode_val chunk l in
  match chunk with
  | Mfloat32 => v = Val.singleoffloat v
  | _ => True
  end.
Proof.
  unfold decode_val; intros; destruct chunk; auto; destruct (proj_bytes (bytesize_chunk_nat 31) l); auto.
  unfold Val.singleoffloat. decEq. symmetry. apply decode_float32_cast. 
Qed.

(** Pointers cannot be forged. *)

Definition memval_valid_first (mv: memval) : Prop :=
  match mv with
  | Pointer b ofs n => n = pred (size_chunk_nat Mint32)
  | _ => True
  end.

Definition memval_valid_cont (mv: memval) : Prop :=
  match mv with
  | Pointer b ofs n => n <> pred (size_chunk_nat Mint32)
  | _ => True
  end.

Inductive encoding_shape: list memval -> Prop :=
  | encoding_shape_intro: forall mv1 mvl,
      memval_valid_first mv1 ->
      (forall mv, In mv mvl -> memval_valid_cont mv) ->
      encoding_shape (mv1 :: mvl).

Lemma encoding_shape_undef : forall n,
  (n > 0)%nat ->
  encoding_shape (list_repeat n Undef).
Proof.
  induction n; intros.
    contradict H; omega.

    simpl.
    apply encoding_shape_intro.
      simpl. auto.
      intros. apply in_list_repeat in H0. subst. simpl. auto.
Qed.

Lemma encoding_shape_int : forall n i,
  encoding_shape (encode_int n i).
Proof.
  unfold encode_int, inj_int. intros.
  destruct (@bytes_of_int_prop1 (nat_of_Z (ZRdiv (Z_of_nat (S n)) 8)) (Int.unsigned n i)) 
    as [b [bl EQ]]; auto.
    apply ZRdiv_prop6.
  rewrite EQ.
Admitted.

Lemma encoding_shape_pointer : forall b i,
  encoding_shape (inj_pointer (size_chunk_nat (Mint 31)) b i).
Proof.
  intros.
  unfold size_chunk_nat, size_chunk.
  rewrite bytesize_chunk_31_eq_4.
  simpl.
  apply encoding_shape_intro; simpl; auto.
    intros.
    unfold memval_valid_cont.
    unfold size_chunk_nat, size_chunk. 
    destruct H; subst; simpl; auto.
      rewrite bytesize_chunk_31_eq_4. compute. intro. inversion H.
    destruct H; subst; simpl; auto.
      rewrite bytesize_chunk_31_eq_4. compute. intro. inversion H.
    destruct H; subst; simpl; auto.
      rewrite bytesize_chunk_31_eq_4. compute. intro. inversion H.
      inversion H.
Qed.

Lemma encode_val_shape:
  forall chunk v, encoding_shape (encode_val chunk v).
Proof.
  intros. 
  destruct (size_chunk_nat_pos chunk) as [sz1 EQ].
  assert (encoding_shape (list_repeat (size_chunk_nat chunk) Undef)).
    rewrite EQ; simpl; constructor. exact I. 
    intros. replace mv with Undef. exact I. symmetry; eapply in_list_repeat; eauto.
  assert (forall bl, length bl = size_chunk_nat chunk ->
          encoding_shape (inj_bytes bl)).
    intros. destruct bl; simpl in *. congruence. 
    constructor. exact I. unfold inj_bytes. intros.
    exploit list_in_map_inv; eauto. intros [x [A B]]. subst mv. exact I.
  destruct v; simpl. 
  auto.

  destruct chunk; auto.
    destruct (eq_nat_dec wz n); subst; auto.   
      apply encoding_shape_int.

  apply H0. apply encode_float_length.

  destruct chunk; auto.
    destruct (eq_nat_dec n 31); subst; auto.
      apply encoding_shape_pointer.

(*
  simpl; intros. intuition; subst mv; red; simpl; congruence.
  apply H0. apply encode_int_length. 
  apply H0. apply encode_float_length.
  destruct chunk; auto. 
  constructor. red. auto.
  simpl; intros. intuition; subst mv; red; simpl; congruence.
*)
Qed.

Lemma check_pointer_inv:
  forall b ofs n mv,
  check_pointer n b ofs mv = true -> mv = inj_pointer n b ofs.
Proof.
  induction n; destruct mv; simpl. 
  auto.
  congruence.
  congruence.
  destruct m; try congruence. intro. 
  destruct (andb_prop _ _ H). destruct (andb_prop _ _ H0). 
  destruct (andb_prop _ _ H2).
  decEq. decEq. symmetry; eapply proj_sumbool_true; eauto.
  symmetry; eapply proj_sumbool_true; eauto.
  symmetry; apply beq_nat_true; auto.
  auto.
Qed.

Inductive decoding_shape: list memval -> Prop :=
  | decoding_shape_intro: forall mv1 mvl,
      memval_valid_first mv1 -> mv1 <> Undef ->
      (forall mv, In mv mvl -> memval_valid_cont mv /\ mv <> Undef) ->
      decoding_shape (mv1 :: mvl).

Lemma decode_pointer_shape' : forall mvl,
  proj_pointer mvl = Vundef \/ decoding_shape mvl.
Proof.
  intros.
  unfold proj_pointer.
  destruct mvl; auto.
  destruct m; auto.
  remember (check_pointer (size_chunk_nat Mint32) b i (Pointer b i n::mvl)) as R.
  destruct R; auto.
  right.
  symmetry in HeqR.
  apply check_pointer_inv in HeqR.
  unfold size_chunk_nat, size_chunk in HeqR.
  simpl in HeqR. 
  rewrite bytesize_chunk_31_eq_4 in HeqR.
  simpl in HeqR.
  rewrite HeqR.
  apply decoding_shape_intro; simpl; auto.
    intro J. inversion J.
    intros. 
    destruct H; subst; simpl; auto.
      split.
        unfold size_chunk_nat, size_chunk.
        simpl. rewrite bytesize_chunk_31_eq_4.
        compute. intro J. inversion J.
        intro J. inversion J.
    destruct H; subst; simpl; auto.
      split.
        unfold size_chunk_nat, size_chunk.
        simpl. rewrite bytesize_chunk_31_eq_4.
        compute. intro J. inversion J.
        intro J. inversion J.
    destruct H; subst; simpl; auto.
      split.
        unfold size_chunk_nat, size_chunk.
        simpl. rewrite bytesize_chunk_31_eq_4.
        compute. intro J. inversion J.
        intro J. inversion J.
      inversion H.
Qed.

Lemma decoding_shape_inj_bytes : forall l,
  (length l > 0)%nat ->
  decoding_shape (inj_bytes l).
Proof.
  destruct l; intros; simpl; auto.
    simpl in H. contradict H; omega.
    apply decoding_shape_intro; simpl; auto.
      intro J. inversion J.
      intros. 
Admitted.

Lemma decode_val_shape:
  forall chunk mvl,
  List.length mvl = size_chunk_nat chunk ->
  decode_val chunk mvl = Vundef \/ decoding_shape mvl.
Proof.
  intros. destruct (size_chunk_nat_pos chunk) as [sz EQ]. 
  unfold decode_val.
  destruct chunk.
    unfold decode_int.
    remember (proj_int n (rev_if_be _ mvl)) as R.
    unfold proj_int in HeqR.
    destruct R.
      destruct (nat_of_Z (ZRdiv (Z_of_nat (S n)) 8)).        
        destruct (rev_if_be _ mvl); try solve [inversion HeqR].

        remember (rev_if_be _ mvl) as R'.
        destruct R'; try solve [inversion HeqR].
        destruct m; try solve [inversion HeqR].
        destruct (eq_nat_dec n1 (nat_of_Z (Z_of_nat (S n) mod 8))); try solve [inversion HeqR].
        remember (proj_bytes n0 R') as R''.
        destruct R''; try solve [inversion HeqR].
         right. admit.
      destruct (eq_nat_dec n 31); subst; auto.
        apply decode_pointer_shape'.

    unfold bytesize_chunk_nat.
    rewrite bytesize_chunk_31_eq_4.
    unfold size_chunk_nat, size_chunk in H. 
    rewrite <- H.
    remember (proj_bytes (length mvl) mvl) as R.
    destruct R; auto.
      symmetry in HeqR.
      apply inj_proj_bytes in HeqR.
      rewrite HeqR.
      right. apply decoding_shape_inj_bytes.
        rewrite HeqR in H.
        rewrite length_inj_bytes in H.
        rewrite H. compute. auto.
         
    unfold bytesize_chunk_nat.
    rewrite bytesize_chunk_63_eq_8.
    unfold size_chunk_nat, size_chunk in H. 
    rewrite <- H.
    remember (proj_bytes (length mvl) mvl) as R.
    destruct R; auto.
      symmetry in HeqR.
      apply inj_proj_bytes in HeqR.
      rewrite HeqR.
      right. apply decoding_shape_inj_bytes.
        rewrite HeqR in H.
        rewrite length_inj_bytes in H.
        rewrite H. compute. admit.
(*
  caseEq (proj_bytes mvl).
  intros bl PROJ. right. exploit inj_proj_bytes; eauto. intros. subst mvl.
  destruct bl; simpl in H. congruence. simpl. constructor. 
  red; auto. congruence.
  unfold inj_bytes; intros. exploit list_in_map_inv; eauto. intros [b [A B]]. 
  subst mv. split. red; auto. congruence.
  intros. destruct chunk; auto. unfold proj_pointer.
  destruct mvl; auto. destruct m; auto. 
  caseEq (check_pointer (size_chunk_nat Mint32) b i (Pointer b i n :: mvl)); auto.
  intros. right. exploit check_pointer_inv; eauto. simpl; intros; inv H2.
  constructor. red. auto. congruence. 
  simpl; intros. intuition; subst mv; simpl; congruence.
*)
Qed.

Lemma encode_val_pointer_inv:
  forall chunk v b ofs n mvl,
  encode_val chunk v = Pointer b ofs n :: mvl ->
  chunk = Mint32 /\ v = Vptr b ofs /\ mvl = inj_pointer (pred (size_chunk_nat Mint32)) b ofs.
Proof.
  intros until mvl. 
  destruct (size_chunk_nat_pos chunk) as [sz SZ].
  unfold encode_val. rewrite SZ. destruct v.
  simpl. congruence. 

  destruct chunk.
    destruct (eq_nat_dec wz n0); subst.
      intro.
      unfold encode_int in H.
      admit.

      intro.
      admit.
    intro.
    admit.

    intro.
    admit.

  intro. admit.


  destruct chunk.
    destruct (eq_nat_dec n0 31); subst.
      intro.
      admit.

      intro.
      admit.
    intro.
    admit.

    intro.
    admit.

(*
  intros until mvl. 
  destruct (size_chunk_nat_pos chunk) as [sz SZ].
  unfold encode_val. rewrite SZ. destruct v.
  simpl. congruence. 
  generalize (encode_int_length chunk i). destruct (encode_int chunk i); simpl; congruence.
  generalize (encode_float_length chunk f). destruct (encode_float chunk f); simpl; congruence.
  destruct chunk; try (simpl; congruence). 
  simpl. intuition congruence. 
*)
Qed.

Lemma decode_val_pointer_inv:
  forall chunk mvl b ofs,
  decode_val chunk mvl = Vptr b ofs ->
  chunk = Mint32 /\ mvl = inj_pointer (size_chunk_nat Mint32) b ofs.
Proof.
  intros until ofs; unfold decode_val.
  destruct chunk.
    unfold decode_int.
    destruct (proj_int n (rev_if_be _ mvl)).
      intro J. inversion J.
      destruct (eq_nat_dec n 31); subst.
        intro J. split; auto.
          admit.          

        intro J. inversion J.

    destruct (proj_bytes (bytesize_chunk_nat 31) mvl).
      intro J. inversion J.
      intro J. inversion J.

    destruct (proj_bytes (bytesize_chunk_nat 63) mvl).
      intro J. inversion J.
      intro J. inversion J.

(*
  intros until ofs; unfold decode_val.
  destruct (proj_bytes mvl). 
  destruct chunk; congruence.
  destruct chunk; try congruence.
  unfold proj_pointer. destruct mvl. congruence. destruct m; try congruence.
  case_eq (check_pointer (size_chunk_nat Mint32) b0 i (Pointer b0 i n :: mvl)); intros.
  inv H0. split; auto. apply check_pointer_inv; auto. 
  congruence.
*)
Qed.

Inductive pointer_encoding_shape: list memval -> Prop :=
  | pointer_encoding_shape_intro: forall mv1 mvl,
      ~memval_valid_cont mv1 ->
      (forall mv, In mv mvl -> ~memval_valid_first mv) ->
      pointer_encoding_shape (mv1 :: mvl).

Lemma encode_pointer_shape:
  forall b ofs, pointer_encoding_shape (encode_val Mint32 (Vptr b ofs)).
Proof.
  intros. simpl. 
  unfold size_chunk_nat, size_chunk.
  rewrite bytesize_chunk_31_eq_4. simpl.
  constructor.
  unfold memval_valid_cont. red; intro. elim H. auto. 
  unfold memval_valid_first. simpl; intros; intuition; subst mv.
    unfold size_chunk_nat, size_chunk in H0.
    simpl in H0. rewrite bytesize_chunk_31_eq_4 in H0. 
    contradict H0. compute. intro J. inversion J.
    
    unfold size_chunk_nat, size_chunk in H0.
    simpl in H0. rewrite bytesize_chunk_31_eq_4 in H0. 
    contradict H0. compute. intro J. inversion J.

    unfold size_chunk_nat, size_chunk in H0.
    simpl in H0. rewrite bytesize_chunk_31_eq_4 in H0. 
    contradict H0. compute. intro J. inversion J.

(*
  intros. simpl. constructor.
  unfold memval_valid_cont. red; intro. elim H. auto. 
  unfold memval_valid_first. simpl; intros; intuition; subst mv; congruence.
*)
Qed.

Lemma decode_pointer_shape:
  forall chunk mvl b ofs,
  decode_val chunk mvl = Vptr b ofs ->
  chunk = Mint32 /\ pointer_encoding_shape mvl.
Proof.
  intros. exploit decode_val_pointer_inv; eauto. intros [A B].
  split; auto. subst mvl.

  assert (J:=@encode_pointer_shape b ofs).
  unfold encode_val in J.
  simpl in J. auto.
Qed.

(** * Compatibility with memory injections *)

(** Relating two memory values according to a memory injection. *)

Inductive memval_inject (f: meminj): memval -> memval -> Prop :=
  | memval_inject_byte:
      forall wz n, memval_inject f (Byte wz n) (Byte wz n)
  | memval_inject_ptr:
      forall b1 ofs1 b2 ofs2 delta n,
      f b1 = Some (b2, delta) ->
      ofs2 = Int.add 31 ofs1 (Int.repr 31 delta) ->
      memval_inject f (Pointer b1 ofs1 n) (Pointer b2 ofs2 n)
  | memval_inject_undef:
      forall mv, memval_inject f Undef mv.

Lemma memval_inject_incr:
  forall f f' v1 v2, memval_inject f v1 v2 -> inject_incr f f' -> memval_inject f' v1 v2.
Proof.
  intros. inv H; econstructor. rewrite (H0 _ _ _ H1). reflexivity. auto.
Qed.

(** [decode_val], applied to lists of memory values that are pairwise
  related by [memval_inject], returns values that are related by [val_inject]. *)

Lemma proj_bytes_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n bl,
  proj_bytes n vl = Some bl ->
  proj_bytes n vl' = Some bl.
Proof.
  induction 1; simpl. congruence.
  inv H; try congruence.

  intros.
  destruct n0; simpl in *; auto.
    destruct (eq_nat_dec wz 8); auto.
      remember (proj_bytes n0 al) as R.
      destruct R.
        rewrite (IHlist_forall2 n0 l); auto.
        inversion H.

  intros.
  destruct n0; simpl in *; auto.

  intros.
  destruct n; simpl in *; auto.
    inversion H.
Qed.

Lemma proj_int_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n i,
  proj_int n vl = Some i ->
  proj_int n vl' = Some i.
Proof.
  intros.
  unfold proj_int in *.
  destruct (nat_of_Z (ZRdiv (Z_of_nat (S n)) 8)); auto.
    destruct vl; destruct vl'; auto.

  destruct vl; destruct vl'; auto.
    inversion H0.
    inversion H.

  destruct m; destruct m0; auto; try solve 
    [inversion H0 | inversion H; subst; inversion H4].

    inversion H; subst. inversion H4; subst.
    destruct (eq_nat_dec n2 (nat_of_Z (Z_of_nat (S n) mod 8))); auto.
    remember (proj_bytes n0 vl) as R.
    destruct R.
      apply proj_bytes_inject with (n:=n0)(bl:=l) in H6; auto.
      rewrite H6. auto.

      inversion H0.
Qed.  

Lemma check_pointer_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n b ofs b' delta,
  check_pointer n b ofs vl = true ->
  f b = Some(b', delta) ->
  check_pointer n b' (Int.add 31 ofs (Int.repr 31 delta)) vl' = true.
Proof.
  induction 1; intros; destruct n; simpl in *; auto. 
  inv H; auto.
  destruct (andb_prop _ _ H1). destruct (andb_prop _ _ H). 
  destruct (andb_prop _ _ H5). 
  assert (n = n0) by (apply beq_nat_true; auto).
  assert (b = b0) by (eapply proj_sumbool_true; eauto). 
  assert (ofs = ofs1) by (eapply proj_sumbool_true; eauto).
  subst. rewrite H3 in H2; inv H2. 
  unfold proj_sumbool. rewrite dec_eq_true. rewrite dec_eq_true. 
  rewrite <- beq_nat_refl. simpl. eauto. 
  congruence.
Qed.

Lemma proj_pointer_inject:
  forall f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (proj_pointer vl1) (proj_pointer vl2).
Proof.
  intros. unfold proj_pointer.
  inversion H; subst. auto. inversion H0; subst; auto.
  case_eq (check_pointer (size_chunk_nat Mint32) b0 ofs1 (Pointer b0 ofs1 n :: al)); intros.
  exploit check_pointer_inject. eexact H. eauto. eauto. 
  intro. rewrite H4. econstructor; eauto. 
  constructor.
Qed.

Lemma proj_bytes_not_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n,
  proj_bytes n vl = None -> proj_bytes n vl' <> None -> In Undef vl.
Proof.
  induction 1; simpl; intros.
  congruence.
  inv H; try congruence. 

  destruct n; simpl in H1, H2; auto.
    contradict H2; auto.
    destruct (eq_nat_dec wz 8); subst.
      remember (proj_bytes n al) as R.
      remember (proj_bytes n bl) as R'.
      destruct R; destruct R';
        try solve [inversion H1 | inversion H2 | contradict H2; auto].
        right. eapply IHlist_forall2; eauto.
          rewrite <- HeqR'. intro. inversion H.          
    contradict H2; auto.

  destruct n; simpl in H2; contradict H2; auto.     
  auto.

(*
  induction 1; simpl; intros.
  congruence.
  inv H; try congruence. 
  right. apply IHlist_forall2.
  destruct (proj_bytes al); congruence.
  destruct (proj_bytes bl); congruence.
  auto.
*)
Qed.

Lemma proj_int_not_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n,
  proj_int n vl = None ->
  proj_int n vl' <> None ->
  In Undef vl.
Proof.
  intros.
  unfold proj_int in *.
  destruct (nat_of_Z (ZRdiv (Z_of_nat (S n)) 8)); auto.
    destruct vl'; contradict H1; auto.

  destruct vl; destruct vl'; auto.
    contradict H1; auto.
    inversion H.
    contradict H1; auto.

  destruct m; destruct m0; auto; try solve 
    [simpl; auto | contradict H1; auto | inversion H; subst; inversion H5].

    inversion H; subst. inversion H5; subst.
    remember (proj_bytes n0 vl) as R.
    remember (proj_bytes n0 vl') as R'.
    destruct (eq_nat_dec n2 (nat_of_Z (Z_of_nat (S n) mod 8)));
      try solve [contradict H1; auto].
      destruct R; destruct R'; try solve [inversion H0 | contradict H1; auto].
        apply proj_bytes_not_inject with (n:=n0) in H7; simpl; auto.
          rewrite <- HeqR'. intro J. inversion J.
Qed.  

Lemma check_pointer_undef:
  forall n b ofs vl,
  In Undef vl -> check_pointer n b ofs vl = false.
Proof.
  induction n; intros; simpl. 
  destruct vl. elim H. auto.
  destruct vl. auto.
  destruct m; auto. simpl in H; destruct H. congruence.
  rewrite IHn; auto. apply andb_false_r. 
Qed.

Lemma proj_pointer_undef:
  forall vl, In Undef vl -> proj_pointer vl = Vundef.
Proof.
  intros; unfold proj_pointer.
  destruct vl; auto. destruct m; auto. 
  rewrite check_pointer_undef. auto. auto.
Qed.

Lemma list_forall2_memval_inject_rev_if_be : forall f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  list_forall2 (memval_inject f) (rev_if_be _ vl1) (rev_if_be _ vl2).
Proof.
  induction vl1; intros.
    inversion H; subst.
    unfold rev_if_be.
    destruct big_endian; simpl; auto.
  
    inversion H; subst.
    apply IHvl1 in H4.
    unfold rev_if_be in *.
    destruct big_endian; simpl; auto.
      apply list_forall2_app; auto.
        apply list_forall2_cons; auto.
          apply list_forall2_nil.
Qed.

Theorem decode_val_inject:
  forall f vl1 vl2 chunk,
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (decode_val chunk vl1) (decode_val chunk vl2).
Proof.
  intros. unfold decode_val. 
  destruct chunk.
    unfold decode_int.
    apply list_forall2_memval_inject_rev_if_be in H.
    remember (proj_int n (rev_if_be memval vl1)) as R.
    remember (proj_int n (rev_if_be memval vl2)) as R'.
    destruct R; destruct R'; auto.
      rewrite proj_int_inject with (f:=f)(vl:=rev_if_be _ vl1)(vl':=rev_if_be _ vl2) (i:=i) in HeqR'; auto.
        inversion HeqR'; auto.
      rewrite proj_int_inject with (f:=f)(vl:=rev_if_be _ vl1)(vl':=rev_if_be _ vl2) (i:=i) in HeqR'; auto.
        inversion HeqR'; auto.

      symmetry in HeqR.
      apply proj_int_not_inject with (n:=n) in H; auto.
        rewrite proj_pointer_undef; auto.
        destruct (eq_nat_dec n 31); subst; auto.

        admit.

        rewrite <- HeqR'. intro J. inversion J.

      destruct (eq_nat_dec n 31); subst; auto.
        unfold proj_pointer.
        admit.

    remember (proj_bytes (bytesize_chunk_nat 31) vl1) as R.
    remember (proj_bytes (bytesize_chunk_nat 31) vl2) as R'.
    destruct R; destruct R'; auto.
      rewrite proj_bytes_inject with (f:=f)(vl:=vl1)(vl':=vl2)(bl:=l) in HeqR'; auto.
        inversion HeqR'; auto.
      rewrite proj_bytes_inject with (f:=f)(vl:=vl1)(vl':=vl2)(bl:=l) in HeqR'; auto.
        inversion HeqR'; auto.

    remember (proj_bytes (bytesize_chunk_nat 63) vl1) as R.
    remember (proj_bytes (bytesize_chunk_nat 63) vl2) as R'.
    destruct R; destruct R'; auto.
      rewrite proj_bytes_inject with (f:=f)(vl:=vl1)(vl':=vl2)(bl:=l) in HeqR'; auto.
        inversion HeqR'; auto.
      rewrite proj_bytes_inject with (f:=f)(vl:=vl1)(vl':=vl2)(bl:=l) in HeqR'; auto.
        inversion HeqR'; auto.

(*
  case_eq (proj_bytes vl1); intros. 
  exploit proj_bytes_inject; eauto. intros. rewrite H1. 
  destruct chunk; constructor.
  destruct chunk; auto.
  case_eq (proj_bytes vl2); intros.
  rewrite proj_pointer_undef. auto. eapply proj_bytes_not_inject; eauto. congruence.
  apply proj_pointer_inject; auto.
*)
Qed.

(** Symmetrically, [encode_val], applied to values related by [val_inject],
  returns lists of memory values that are pairwise
  related by [memval_inject]. *)

Lemma inj_bytes_inject:
  forall f bl, list_forall2 (memval_inject f) (inj_bytes bl) (inj_bytes bl).
Proof.
  induction bl; constructor; auto. constructor.
Qed.

Lemma inj_int_inject:
  forall f n i, list_forall2 (memval_inject f) (inj_int n i) (inj_int n i).
Proof.
  intros.
  unfold inj_int.
  destruct (bytes_of_int (nat_of_Z (ZRdiv (Z_of_nat (S n)) 8)) (Int.unsigned n i)).
    apply list_forall2_nil.
    apply list_forall2_cons.
      apply memval_inject_byte.
      apply inj_bytes_inject.
Qed.

Lemma repeat_Undef_inject_any:
  forall f vl,
  list_forall2 (memval_inject f) (list_repeat (length vl) Undef) vl.
Proof.
  induction vl; simpl; constructor; auto. constructor. 
Qed.  

Lemma repeat_Undef_inject_self:
  forall f n,
  list_forall2 (memval_inject f) (list_repeat n Undef) (list_repeat n Undef).
Proof.
  induction n; simpl; constructor; auto. constructor.
Qed.  

Theorem encode_val_inject:
  forall f v1 v2 chunk,
  val_inject f v1 v2 ->
  list_forall2 (memval_inject f) (encode_val chunk v1) (encode_val chunk v2).
Proof.
  intros. inv H; simpl.

  destruct chunk.
    destruct (eq_nat_dec wz n); subst.
      unfold encode_int.
      apply list_forall2_memval_inject_rev_if_be.
      apply inj_int_inject.

      apply repeat_Undef_inject_self.
   apply repeat_Undef_inject_self.
   apply repeat_Undef_inject_self.
   apply inj_bytes_inject.


  destruct chunk.
    destruct (eq_nat_dec n 31); subst.
      unfold size_chunk_nat, size_chunk.     
      rewrite bytesize_chunk_31_eq_4.
      unfold inj_pointer; simpl; repeat econstructor; auto.

      apply repeat_Undef_inject_self.
   apply repeat_Undef_inject_self.
   apply repeat_Undef_inject_self.

  rewrite <- encode_val_length with (v:=v2).
  apply repeat_Undef_inject_any.

(*
  intros. inv H; simpl.
  apply inj_bytes_inject.
  apply inj_bytes_inject.
  destruct chunk; try apply repeat_Undef_inject_self. 
  unfold inj_pointer; simpl; repeat econstructor; auto. 
  replace (size_chunk_nat chunk) with (length (encode_val chunk v2)).
  apply repeat_Undef_inject_any. apply encode_val_length. 
*)
Qed.

(** The identity injection has interesting properties. *)

Definition inject_id : meminj := fun b => Some(b, 0).

Lemma val_inject_id:
  forall v1 v2,
  val_inject inject_id v1 v2 <-> Val.lessdef v1 v2.
Proof.
  intros; split; intros.
  inv H. constructor. constructor.
  unfold inject_id in H0. inv H0. rewrite Int.add_zero. constructor.
  constructor.
  inv H. destruct v2; econstructor. unfold inject_id; reflexivity. rewrite Int.add_zero; auto.
  constructor.
Qed.

Lemma memval_inject_id:
  forall mv, memval_inject inject_id mv mv.
Proof.
  destruct mv; econstructor. unfold inject_id; reflexivity. rewrite Int.add_zero; auto. 
Qed.


