Require Import Memory.
Require Import Values.
Require Import Coqlib.
Require Import Integers.
Require Import AST.
Require Import Znumtheory.
Require Import memory_sim.
Require Import vellvm.
Require Import memory_props.
Require Import promotable_props.
Require Import genericvalues.
Require Import genericvalues_inject.

Module SASmsim.

(** * Generic injections *)

(** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- ignore data stored at [lo, hi) in block b, although they still need to be valid.
*)

Export Mem.

Definition notin_ignores (ignores:list (Values.block*Z*Z)) (b1:Values.block) 
  (ofs:Z) : Prop :=
List.Forall (fun ignore =>
             let '(b,lo,hi) := ignore in
             b1 <> b \/ (b1 = b /\ (ofs < lo \/ ofs >= hi))) ignores.

Record mem_inj (f: meminj) (ignores:list (Values.block*Z*Z)) (m1 m2: mem) 
  : Prop :=
  mk_mem_inj {
    mi_access:
      forall b1 b2 delta chunk ofs p,
      f b1 = Some(b2, delta) ->
      valid_access m1 chunk b1 ofs p ->
      valid_access m2 chunk b2 (ofs + delta) p;
    mi_memval:
      forall b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs Nonempty ->
      notin_ignores ignores b1 ofs ->
      MoreMem.memval_inject f (m1.(mem_contents) b1 ofs) 
        (m2.(mem_contents) b2 (ofs + delta))
  }.

(** Preservation of permissions *)

Lemma perm_inj:
  forall igns f m1 m2 b1 ofs p b2 delta,
  mem_inj f igns m1 m2 ->
  perm m1 b1 ofs p ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) p.
Proof.
  intros. 
  assert (valid_access m1 (Mint 7) b1 ofs p).
    split. red; intros. simpl in H2. rewrite bytesize_chunk_7_eq_1 in H2. replace ofs0 with ofs by omega. auto.
    simpl. apply Zone_divide.
  exploit mi_access; eauto. intros [A B].
  apply A. simpl; rewrite bytesize_chunk_7_eq_1; omega. 
Qed.

(** Preservation of loads. *)

Definition notin_ignores_with_size (ignores:list (Values.block*Z*Z)) 
  (b1:Values.block) (ofs:Z) (size:Z) : Prop :=
List.Forall (fun ignore =>
             let '(b,lo,hi) := ignore in
             b1 <> b \/ (b1 = b /\ (ofs + size <= lo \/ ofs >= hi))) ignores.

Lemma notin_ignores_with_size__notin_ignores: forall b ofs size (Hge: size > 0) 
  igns, 
  notin_ignores_with_size igns b ofs size ->
  notin_ignores igns b ofs.
Proof.
  unfold notin_ignores_with_size, notin_ignores.
  induction igns as [|[[]]]; simpl; intros; auto.
    inv H.
    constructor; auto.
    destruct H2 as [H2 | [H6 [H4 | H4]]]; subst; auto.
      right. split; auto. omega. 
Qed.

Lemma notin_ignores_with_size_delta: forall b ofs delta size igns
  (J:delta>=0),
  notin_ignores_with_size igns b ofs (delta+size) ->
  notin_ignores_with_size igns b (ofs+delta) size.
Proof.
  unfold notin_ignores_with_size.
  intros.
  induction H; auto.
    destruct x as [[b1 lo1] hi1].
    constructor; auto.
    destruct H as [H2 | [H6 [H4 | H4]]]; subst; try solve 
      [auto | right; split; auto; omega]. 
Qed.

Lemma notin_ignores_with_size_inc: forall b ofs size igns, 
  notin_ignores_with_size igns b ofs (Zsucc size) ->
  notin_ignores_with_size igns b (ofs+1) size.
Proof.
  intros.
  apply notin_ignores_with_size_delta; auto.
    omega.
    replace (1+size) with (Zsucc size) by omega. auto.
Qed.

Lemma getN_inj:
  forall igns f m1 m2 b1 b2 delta,
  mem_inj f igns m1 m2 ->
  f b1 = Some(b2, delta) ->
  forall n ofs,
  range_perm m1 b1 ofs (ofs + Z_of_nat n) Readable ->
  notin_ignores_with_size igns b1 ofs (Z_of_nat n) ->
  list_forall2 (MoreMem.memval_inject f) 
               (getN n ofs (m1.(mem_contents) b1))
               (getN n (ofs + delta) (m2.(mem_contents) b2)).
Proof.
  induction n; intros; simpl.
    constructor.

    rewrite inj_S in *. 
    constructor. 
      eapply mi_memval; eauto.
        apply perm_implies with Readable.
          apply H1. omega. 
          constructor. 
        eapply notin_ignores_with_size__notin_ignores; eauto.
        assert (J:=@Z_of_S_gt_O n). omega.

      replace (ofs + delta + 1) with ((ofs + 1) + delta) by omega.
      apply IHn. 
        red; intros; apply H1; omega. 
        apply notin_ignores_with_size_inc; auto.
Qed.

Lemma load_inj:
  forall igns f m1 m2 chunk b1 ofs b2 delta v1,
  MoreMem.meminj_no_overlap f ->
  MoreMem.meminj_zero_delta f ->
  mem_inj f igns m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  notin_ignores_with_size igns b1 ofs (size_chunk chunk) ->
  exists v2, 
    load chunk m2 b2 (ofs + delta) = Some v2 /\ MoreMem.val_inject f v1 v2.
Proof.
Local Transparent load.
  intros.
  exists (decode_val chunk (getN (size_chunk_nat chunk) 
            (ofs + delta) (m2.(mem_contents) b2))).
  split. 
    unfold load. apply pred_dec_true.  
    eapply mi_access; eauto with mem. 

    exploit load_result; eauto. intro. subst.
    apply MoreMem.decode_val_inject; auto.
    eapply getN_inj; eauto. 
      rewrite <- size_chunk_conv. exploit load_valid_access; eauto. intros [A B]. auto.
      rewrite <- size_chunk_conv. auto.
Qed.

Lemma load_inj2:
  forall igns f m1 m2 chunk b1 ofs b2 delta v1 v2,
  MoreMem.meminj_no_overlap f ->
  MoreMem.meminj_zero_delta f ->
  mem_inj f igns m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  notin_ignores_with_size igns b1 ofs (size_chunk chunk) ->
  load chunk m2 b2 (ofs + delta) = Some v2 ->
  MoreMem.val_inject f v1 v2.
Proof.
  intros.
  eapply load_inj in H2; eauto.
  destruct H2 as [v2' [H2 H6]].
  uniq_result. auto.
Qed.

(** Preservation of stores. *)

Lemma setN_inj_inside:
  forall delta f vl1 vl2,
  list_forall2 (MoreMem.memval_inject f) vl1 vl2 ->
  forall p c1 c2,
  (forall q, p <= q < p + Z_of_nat (length vl1) ->
             MoreMem.memval_inject f ((setN vl1 p c1) q) 
                                     ((setN vl2 (p + delta) c2) (q + delta))).
Proof.
  induction 1; intros; simpl in *.
    contradict H; omega.

    replace (p + delta + 1) with ((p + 1) + delta) by omega.
    destruct (Z_le_dec (p+1) q).
      apply IHlist_forall2; auto. 
      rewrite Zpos_P_of_succ_nat in H1.
      auto with zarith.

      assert (p = q) as EQ. omega. 
      subst.
      repeat rewrite setN_outside by omega.
      rewrite update_s. rewrite update_s. auto.
Qed.

Lemma setN_inj_outside:
  forall delta f vl1 vl2
  (Heq: length vl1 = length vl2),
  forall p c1 c2,
  (forall q, MoreMem.memval_inject f (c1 q) (c2 (q + delta)) ->
             p > q \/ q >= p + Z_of_nat (length vl1) ->
             MoreMem.memval_inject f ((setN vl1 p c1) q) 
                                     ((setN vl2 (p + delta) c2) (q + delta))).
Proof.
  intros.
  repeat rewrite setN_outside by omega.
  auto.
Qed.

Lemma store_mapped_inj:
  forall igns f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inj f igns m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  MoreMem.meminj_no_overlap f ->
  f b1 = Some (b2, delta) ->
  MoreMem.val_inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inj f igns n1 n2.
Proof.
  intros. inversion H. 
  assert (valid_access m2 chunk b2 (ofs + delta) Writable).
    eapply mi_access0; eauto with mem.
  destruct (valid_access_store _ _ _ _ v2 H4) as [n2 STORE]. 
  exists n2; split. eauto.
  constructor.
(* access *)
  intros.
  eapply store_valid_access_1; [apply STORE |].
  eapply mi_access0; eauto.
  eapply store_valid_access_2; [apply H0 |]. auto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs0 Nonempty). eapply perm_store_2; eauto. 
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite (store_mem_contents _ _ _ _ _ _ STORE).
  unfold update. 
  destruct (zeq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite zeq_true.
  eapply mi_memval0 in H7; eauto.
  apply MoreMem.encode_val_inject with (chunk:=chunk) in H3; auto.  
  assert (length (encode_val chunk v1) = length (encode_val chunk v2)) as EQ.
    eapply list_forall2_length_eq; eauto.
  destruct (Z_gt_dec ofs ofs0).
    apply setN_inj_outside; auto.
    destruct (Z_ge_dec ofs0 (ofs + Z_of_nat (length (encode_val chunk v1)))).
      apply setN_inj_outside; auto.
      eapply setN_inj_inside; eauto. omega.

  destruct (zeq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. auto.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros. 
  assert (b2 <> b2).
    eapply H1; eauto. 
  congruence.
  (* block <> b1, block <> b2 *)
  eauto.
Qed.

Lemma store_mapped_inj2:
  forall igns f chunk m1 b1 ofs v1 n1 m2 b2 delta v2 n2,
  mem_inj f igns m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  MoreMem.meminj_no_overlap f ->
  f b1 = Some (b2, delta) ->
  MoreMem.val_inject f v1 v2 ->
  store chunk m2 b2 (ofs + delta) v2 = Some n2 ->
  mem_inj f igns n1 n2.
Proof.
  intros.
  eapply store_mapped_inj in H0; eauto.
  destruct H0 as [n2' [J1 J2]].
  uniq_result. auto.
Qed.

Lemma store_unmapped_inj:
  forall igns f chunk m1 b1 ofs v1 n1 m2,
  mem_inj f igns m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  mem_inj f igns n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* access *)
  eauto with mem.
(* mem_contents *)
  intros. 
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite update_o. eauto with mem. 
  congruence.
Qed.

Lemma store_outside_inj:
  forall igns f m1 m2 chunk b ofs v m2',
  mem_inj f igns m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Nonempty ->
    ofs' + delta < ofs \/ ofs' + delta >= ofs + size_chunk chunk) ->
  store chunk m2 b ofs v = Some m2' ->
  mem_inj f igns m1 m2'.
Proof.
  intros. inversion H. constructor.
(* access *)
  eauto with mem.
(* mem_contents *)
  intros. 
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  unfold update. destruct (zeq b2 b). subst b2.
  rewrite setN_outside. auto. 
  rewrite encode_val_length. rewrite <- size_chunk_conv. 
  eapply H0; eauto. 
  eauto with mem.
Qed.

Definition in_ignores_with_size (ignores:list (Values.block*Z*Z)) 
  (b1:Values.block) (ofs:Z) (size:Z) : Prop :=
exists b, exists lo, exists hi,
  In (b,lo,hi) ignores /\ b1 = b /\ ofs + size <= hi /\ ofs >= lo.

Lemma in_ignores_with_size__notin_ignores__inv: forall b ofs1 ofs2 size igns
  (Hnzero: size>=0),
  in_ignores_with_size igns b ofs1 size ->
  notin_ignores igns b ofs2 ->
  ofs2 < ofs1 \/ ofs2 >= ofs1 + size.
Proof.
  unfold in_ignores_with_size, notin_ignores.
  intros.
  destruct H as [b0 [lo0 [hi0 [H [J1 [J2 J3]]]]]]; subst.
  induction igns as [|[[]]]; simpl; intros.
    inv H.

    inv H0.
    simpl in H.
    destruct H as [H | H]; eauto.
    inv H.
    destruct H3 as [H3 | [H3 [H5 | H5]]]; subst; try congruence; omega.
Qed.

Lemma store_inside_inj_left:
  forall igns f m1 m2 chunk b ofs v m1',
  mem_inj f igns m1 m2 ->
  in_ignores_with_size igns b ofs (size_chunk chunk) ->
  store chunk m1 b ofs v = Some m1' ->
  mem_inj f igns m1' m2.
Proof.
  intros. inversion H. constructor.
(* access *)
  eauto with mem.
(* mem_contents *)
  intros. 
  assert (perm m1 b1 ofs0 Nonempty) as Jp. 
    eapply perm_store_2; eauto.
  eapply mi_memval0 in Jp; eauto.
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  unfold update. 
  destruct (zeq b1 b); subst; auto.
    rewrite setN_outside; auto.
      rewrite encode_val_length. rewrite <- size_chunk_conv.
      eapply in_ignores_with_size__notin_ignores__inv; eauto.
        assert (J:=@size_chunk_pos chunk). omega.
Qed.

Lemma store_inside_inj_left_inc:
  forall igns f m1 m2 chunk b ofs lo hi v m1',
  mem_inj f igns m1 m2 ->
  lo <= ofs /\ ofs + (size_chunk chunk) <= hi ->
  store chunk m1 b ofs v = Some m1' ->
  mem_inj f ((b,lo,hi)::igns) m1' m2.
Proof.
  intros. inversion H. constructor.
(* access *)
  eauto with mem.
(* mem_contents *)
  intros. 
  assert (perm m1 b1 ofs0 Nonempty) as Jp. 
    eapply perm_store_2; eauto.
  inv H4.
  eapply mi_memval0 in Jp; eauto.
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  unfold update. 
  destruct (zeq b1 b); subst; auto.
    rewrite setN_outside; auto.
      rewrite encode_val_length. rewrite <- size_chunk_conv.
      destruct H7 as [H7 | [? [J | J]]]; try congruence; omega.
Qed.

Lemma store_inside_inj2':
  forall igns f m1 m2 chunk b1 b2 ofs v1 v2 n1 delta hi,
  mem_inj f ((b1,ofs,hi)::igns) m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  MoreMem.meminj_no_overlap f ->
  f b1 = Some (b2, delta) ->
  MoreMem.val_inject f v1 v2 ->
  exists n2, 
    store chunk m2 b2 (ofs+delta) v2 = Some n2 /\
    mem_inj f ((b1,ofs + (size_chunk chunk),hi)::igns) n1 n2.
Proof.
  intros. inversion H. 
  assert (valid_access m2 chunk b2 (ofs + delta) Writable).
    eapply mi_access0; eauto with mem.
  destruct (valid_access_store _ _ _ _ v2 H4) as [n2 STORE]. 
  exists n2; split. eauto.
  constructor.
(* access *)
  intros.
  eapply store_valid_access_1; [apply STORE |].
  eapply mi_access0; eauto.
  eapply store_valid_access_2; [apply H0 |]. auto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs0 Nonempty). eapply perm_store_2; eauto. 
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite (store_mem_contents _ _ _ _ _ _ STORE).
  unfold update. 
  destruct (zeq b0 b1); subst.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite zeq_true.
  apply MoreMem.encode_val_inject with (chunk:=chunk) in H3; auto.  
  assert (length (encode_val chunk v1) = length (encode_val chunk v2)) as EQ.
    eapply list_forall2_length_eq; eauto.
  destruct (Z_gt_dec ofs ofs0).
    apply setN_inj_outside; auto.
    assert (notin_ignores ((b1, ofs, hi) :: igns) b1 ofs0) 
      as Higns.
      unfold notin_ignores.
      inv H7.
      constructor; auto.
        destruct H11 as [H11 | [H11 [H13 | H13]]]; auto.
        right. split; auto. omega.
    eapply mi_memval0 in Higns; eauto.

    destruct (Z_ge_dec ofs0 (ofs + Z_of_nat (length (encode_val chunk v1)))).
      apply setN_inj_outside; auto.
      assert (notin_ignores ((b1, ofs, hi) :: igns) b1 ofs0) 
        as Higns.
        unfold notin_ignores.
        inv H7.
        constructor; auto.
          destruct H11 as [H11 | [H11 [H13 | H13]]]; auto.
          rewrite encode_val_length in z. rewrite <- size_chunk_conv in z.
          contradict H13; omega.
      eapply mi_memval0 in Higns; eauto.

      eapply setN_inj_inside; eauto. omega.

  destruct (zeq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  unfold MoreMem.meminj_no_overlap in H1.
  eapply H1 in n; eauto.
  congruence.
  (* block <> b1, block <> b2 *)
  eapply mi_memval0; eauto.
    inv H7.
    unfold notin_ignores.
    constructor; auto.
Qed.

Lemma store_inside_inj2:
  forall igns f m1 m2 chunk b1 b2 ofs v1 v2 n1 n2 delta hi,
  mem_inj f ((b1,ofs,hi)::igns) m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  MoreMem.meminj_no_overlap f ->
  f b1 = Some (b2, delta) ->
  MoreMem.val_inject f v1 v2 ->
  store chunk m2 b2 (ofs+delta) v2 = Some n2 ->
  mem_inj f ((b1,ofs+(size_chunk chunk),hi)::igns) n1 n2.
Proof.
  intros.
  eapply store_inside_inj2' in H; eauto.
  destruct H as [n2' [J1 J2]].
  uniq_result. auto.
Qed.

Lemma store_inside_inj_right:
  forall igns f m1 m2 chunk b ofs v m2',
  mem_inj f igns m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Nonempty ->
    in_ignores_with_size igns b' (ofs-delta) (size_chunk chunk)) ->
  store chunk m2 b ofs v = Some m2' ->
  mem_inj f igns m1 m2'.
Proof.
  intros. inversion H. constructor.
(* access *)
  eauto with mem.
(* mem_contents *)
  intros. 
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  unfold update. 
  destruct (zeq b2 b); subst; auto.
  rewrite setN_outside; auto. 
  rewrite encode_val_length. rewrite <- size_chunk_conv. 
  eapply H0 in H3; eauto. 
    eapply in_ignores_with_size__notin_ignores__inv in H3; eauto.
      omega.
      assert (J:=@size_chunk_pos chunk). omega.
Qed.

(** Preservation of allocations *)

Lemma alloc_right_inj:
  forall igns f m1 m2 lo hi b2 m2',
  mem_inj f igns m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  mem_inj f igns m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* access *)
  intros. eauto with mem. 
(* mem_contents *)
  intros.
  assert (valid_access m2 (Mint 7) b0 (ofs + delta) Nonempty).
    eapply mi_access0; eauto.
    split. 
      simpl. red; intros. 
      rewrite bytesize_chunk_7_eq_1 in H4. 
      assert (ofs0 = ofs) by omega. congruence.

      simpl. apply Zone_divide. 
  assert (valid_block m2 b0) by eauto with mem.
Local Transparent alloc.
  rewrite <- MEM; simpl. 
  rewrite update_o. 
    eauto with mem.
    unfold valid_block in H5. omega.
Qed.

Lemma alloc_left_unmapped_inj:
  forall igns f m1 m2 lo hi m1' b1,
  mem_inj f igns m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  f b1 = None ->
  mem_inj f igns m1' m2.
Proof.
  intros. inversion H. constructor.
(* access *)
  unfold update; intros.
  exploit valid_access_alloc_inv; eauto. unfold eq_block. intros. 
  destruct (zeq b0 b1). congruence. eauto.
(* mem_contents *)
  injection H0; intros NEXT MEM. intros. 
  rewrite <- MEM; simpl. rewrite NEXT. unfold update.
  exploit perm_alloc_inv; eauto. intros. 
  destruct (zeq b0 b1). 
    subst. congruence.
    eauto.
Qed.

Lemma free_right_inj:
  forall igns f m1 m2 b lo hi m2',
  mem_inj f igns m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs p ->
    lo <= ofs + delta < hi -> False) ->
  mem_inj f igns m1 m2'.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
(* access *)
  intros. exploit mi_access0; eauto. intros [RG AL]. split; auto.
  red; intros. eapply perm_free_1; eauto. 
  destruct (zeq b2 b); auto. subst b. right.
  destruct (zlt ofs0 lo); auto. destruct (zle hi ofs0); auto.
  elimtype False. eapply H1 with (ofs := ofs0 - delta). eauto. 
  apply H3. omega. omega.
(* mem_contents *)
  intros. rewrite FREE; simpl.
  specialize (mi_memval0 _ _ _ _ H2 H3).
  assert (b=b2 /\ lo <= ofs+delta < hi \/ 
          (b<>b2 \/ ofs+delta<lo \/ hi <= ofs+delta)) as J 
    by (unfold Values.block; omega).
  destruct J as [[J1 J2] | J]; subst.
    specialize (H1 _ _ _ _ H2 H3). elimtype False; auto.
    rewrite (clearN_out _ _ _ _ _ _ J); auto.
Qed.

Lemma free_inj:
  forall igns f m1 m2 b1 b2 delta lo hi m1' m2',
  MoreMem.meminj_no_overlap f ->
  MoreMem.meminj_zero_delta f ->
  mem_inj f igns m1 m2 ->
  free m1 b1 lo hi = Some m1' ->
  free m2 b2 (lo+delta) (hi+delta) = Some m2' ->
  f b1 = Some (b2, delta) ->
  mem_inj f igns m1' m2'.
Proof.
  intros igns f m1 m2 b1 b2 delta lo hi m1' m2' J J' H H0 H1 H2.
  exploit free_result; eauto. 
  intro FREE. inversion H. constructor.
(* access *)
  intros. exploit mi_access0; eauto with mem. 
  intros [RG AL]. split; auto.
  red; intros. eapply perm_free_1; eauto. 
  destruct (zeq b3 b2); auto. 
    subst b2. right.
    destruct (zlt ofs0 (lo + delta)); auto. 
    destruct (zle (hi + delta) ofs0); auto.
    destruct (@MoreMem.meminj_no_overlap_spec f b0 b3 delta0 b1 delta J H3 H2)
      as [G1 G2]; subst.
    assert (lo <= ofs0 - delta < hi) as J1.
      clear - z z0. auto with zarith.
    assert (ofs <= ofs0 - delta < ofs + size_chunk chunk) as J2.
      clear - H5. auto with zarith.
    destruct H4 as [H41 H42].
    apply H41 in J2.
    eapply perm_free_2 with (p:=p) in J1; eauto.
    congruence.
(* mem_contents *)
  intros. rewrite FREE; simpl.
  assert (FREE':=H0). apply free_result in FREE'.
  rewrite FREE'; simpl.   
  assert (b0=b1 /\ lo <= ofs < hi \/ (b1<>b0 \/ ofs<lo \/ hi <= ofs)) as J1
    by (unfold Values.block; omega).
  assert (b2=b3 /\ lo+delta <= ofs+delta < hi+delta \/ 
    (b2<>b3 \/ ofs+delta<lo+delta \/ hi+delta <= ofs+delta)) 
    as J2 by (unfold Values.block; omega).
  destruct J1 as [J1 | J1].
    destruct J1 as [J11 J12]; subst.
    eapply perm_free_2 with (p:=Nonempty) in H0; eauto.
    congruence.

    rewrite (clearN_out _ _ _ _ _ _ J1).
    destruct J2 as [J2 | J2].
      destruct J2 as [J21 J22]; subst.
      destruct (@MoreMem.meminj_no_overlap_spec f b0 b3 delta0 b1 delta J H3 H2)
        as [G1 G2]; subst.
      assert (lo <= ofs < hi) as EQ.
        clear - J22. auto with zarith.
      clear - J1 EQ.
      destruct J1 as [J1 | J1]; try solve [congruence].
      contradict EQ; auto with zarith.

      assert (W1:=H2). apply J' in W1. subst.
      assert (W2:=H3). apply J' in W2. subst.
      rewrite (clearN_out _ _ _ _ _ _ J2).
      eapply perm_free_3 in H4; eauto.
Qed.

Lemma free_left_nonmap_inj:
  forall igns f m1 m2 b lo hi m1' (Hprop: f b = None),
  mem_inj f igns m1 m2 ->
  Mem.free m1 b lo hi = Some m1' ->
  mem_inj f igns m1' m2.
Proof.
  intros. exploit Mem.free_result; eauto. intro FREE. inversion H. constructor.
(* access *)
  intros. eauto with mem.
(* mem_contents *)
  intros. rewrite FREE; simpl.
  assert (b=b1 /\ lo <= ofs < hi \/ (b<>b1 \/ ofs<lo \/ hi <= ofs)) as J
    by (unfold Values.block; omega).
  destruct J as [[J1 J2] | J]; subst.
    uniq_result.

    rewrite (Mem.clearN_out _ _ _ _ _ _ J).
    apply mi_memval0; auto.
    eapply Mem.perm_free_3; eauto.
Qed.

Lemma inject_id_no_overlap: MoreMem.meminj_no_overlap inject_id.
Proof.
  unfold MoreMem.meminj_no_overlap, inject_id.
  intros. uniq_result. auto.
Qed.

Lemma inject_id_zero_delta: MoreMem.meminj_zero_delta inject_id.
Proof.
  unfold MoreMem.meminj_zero_delta, inject_id.
  intros. uniq_result. auto.
Qed.

Lemma notin_ignores_strengthen: forall b ofs igns2 igns1,
  notin_ignores (igns1++igns2) b ofs ->
  notin_ignores igns2 b ofs.
Proof.
  induction igns1 as [|[[]]]; simpl; intros; auto.
    inv H. auto.
Qed.

Lemma mem_inj_ignores_weaken: forall mi igns' M1 M2 
  (Hin : mem_inj mi igns' M1 M2) igns,
  mem_inj mi (igns ++ igns') M1 M2.
Proof.
  induction igns; auto.
    inv IHigns.  
    constructor; auto.
      intros.
      simpl_env in H1.
      apply mi_memval0; eauto using notin_ignores_strengthen.
Qed.

Lemma in_ignores_with_smaller_size: forall b ofs size1 size2 
  (Hge: size1>=size2) igns,
  in_ignores_with_size igns b ofs size1 ->
  in_ignores_with_size igns b ofs size2.
Proof.
  unfold in_ignores_with_size.
  intros.
  destruct H as [b0 [lo0 [hi0 [H [J1 [J2 J3]]]]]]; subst.
  exists b0. exists lo0. exists hi0.
  split; auto. split; auto. split; omega.
Qed.

Lemma in_ignores_with_size_delta: forall b ofs delta size igns
  (J:delta>=0),
  in_ignores_with_size igns b ofs (delta+size) ->
  in_ignores_with_size igns b (ofs+delta) size.
Proof.
  unfold in_ignores_with_size.
  intros.
  destruct H as [b0 [lo0 [hi0 [H [J1 [J2 J3]]]]]]; subst.
  exists b0. exists lo0. exists hi0.
  split; auto. split; auto. split; omega.
Qed.

Lemma mstore_aux_inside_inj_left: forall (TD : TargetData) (M2 : mem) 
  (b : Values.block) igns (gv1 : GenericValue) (M1 : mem) (M1' : mem) ofs
  (J2 : mstore_aux M1 gv1 b ofs = Some M1')
  (Hin : mem_inj inject_id igns M1 M2)
  (Higns: in_ignores_with_size igns b ofs (Z_of_nat (sizeGenericValue gv1))),
  mem_inj inject_id igns M1' M2.
Proof.
  induction gv1 as [|[]]; simpl; intros.
    uniq_result. auto.

    inv_mbind.
    rewrite inj_plus in Higns.
    rewrite <- size_chunk_conv in Higns.
    apply IHgv1 in H0; auto.
      eapply store_inside_inj_left; eauto.
        eapply in_ignores_with_smaller_size; eauto.
          omega.
      apply in_ignores_with_size_delta; auto.
        assert (J:=@size_chunk_pos m). omega.
Qed.

Lemma mstore_aux_inside_inj_left': forall (TD : TargetData) (M2 : mem) 
  (b : Values.block) lo hi
  igns (gv1 : GenericValue) (M1 : mem) (M1' : mem) ofs
  (J2 : mstore_aux M1 gv1 b ofs = Some M1')
  (Hin : mem_inj inject_id igns M1 M2)
  (Hrange: lo <= ofs /\ ofs + Z_of_nat (sizeGenericValue gv1) <= hi),
  mem_inj inject_id ((b, lo, hi) :: igns) M1' M2.
Proof.
  intros.
  simpl_env.
  eapply mstore_aux_inside_inj_left; eauto.
    apply mem_inj_ignores_weaken; auto.

    unfold in_ignores_with_size.
    exists b. exists lo. exists hi. simpl. 
    split; auto. split; auto. omega.
Qed.

Lemma mstore_inside_inj_left: forall (TD : TargetData) (M1 : mem)
  (gv1 : GenericValue) (a : align) (M1' : mem) t
  (M2 : mem) igns (mb : mblock)
  (H23 : mstore TD M1 ($ blk2GV TD mb # typ_pointer t $) t gv1 a = ret M1')
  (Hin : mem_inj inject_id igns M1 M2),
  mem_inj inject_id ((mb, 0, Size.to_Z (sizeGenericValue gv1))::igns) M1' M2.
Proof.
  intros.
  apply mstore_inversion in H23.
  rewrite Promotability.simpl_blk2GV in H23.
  destruct H23 as [b [ofs [cm [J1 J2]]]].
  inv J1.
  rewrite Int.signed_repr in J2; auto using Promotability.min_le_zero_le_max.
  eapply mstore_aux_inside_inj_left'; eauto.
  unfold Size.to_Z.
  split; omega.
Qed.

Lemma mstore_inside_inj_left': forall (TD : TargetData) (M1 : mem)
  (gv1 : GenericValue) (a : align) (M1' : mem) t
  (M2 : mem) igns (mb : mblock)
  (H23 : mstore TD M1 ($ blk2GV TD mb # typ_pointer t $) t gv1 a = ret M1')
  (Hin : mem_inj inject_id 
          ((mb, 0, Size.to_Z (sizeGenericValue gv1))::igns) M1 M2),
  mem_inj inject_id ((mb, 0, Size.to_Z (sizeGenericValue gv1))::igns) M1' M2.
Proof.
  intros.
  apply mstore_inversion in H23.
  rewrite Promotability.simpl_blk2GV in H23.
  destruct H23 as [b [ofs [cm [J1 J2]]]].
  inv J1.
  rewrite Int.signed_repr in J2; auto using Promotability.min_le_zero_le_max.
  eapply mstore_aux_inside_inj_left; eauto.
    unfold in_ignores_with_size.
    simpl. exists b. exists 0. exists (Size.to_Z (sizeGenericValue gv1)).
    split; auto. split; auto. unfold Size.to_Z. split; omega.
Qed.

Lemma alloc_inject_id_inj:
  forall igns m1 m2 lo hi b1 b2 m1' m2'
  (Heq: nextblock m1 = nextblock m2)
  (Hinj: mem_inj inject_id igns m1 m2)
  (Hal1: alloc m1 lo hi = (m1', b1))
  (Hal2: alloc m2 lo hi = (m2', b2)),
  mem_inj inject_id igns m1' m2'.
Proof.
  intros. 
  injection Hal1. intros NEXT1 MEM1; subst.
  injection Hal2. intros NEXT2 MEM2; subst.
  inversion Hinj. constructor.
(* access *)
  intros. unfold inject_id in H. inv H.
  replace (ofs+0) with ofs by omega.
  eapply valid_access_alloc_inv in H0; eauto.
  destruct (eq_block b2 (nextblock m1)); subst.
    apply valid_access_alloc_same with (chunk:=chunk)(ofs:=ofs) in Hal2; 
      try solve [auto | omega | tauto].
    rewrite Heq.
    eapply valid_access_implies; try solve [eauto | constructor].

    eapply valid_access_alloc_other in Hal2; eauto.
    apply mi_access0 with (b2:=b2)(delta:=0) in H0; auto.
    replace (ofs+0) with ofs in H0 by omega. auto.
(* mem_contents *)
  simpl.
  intros. unfold inject_id in H. inv H.
  eapply perm_alloc_inv in H0; eauto.
  destruct (zeq b2 (nextblock m1)); subst.
    rewrite <- Heq.
    repeat rewrite update_s. constructor.

    apply mi_memval0 with (b2:=b2)(delta:=0) in H0; auto.
    repeat (rewrite update_o; try solve [auto | congruence]).
Qed.

Lemma notin_ignores_with_smaller_size: forall b ofs size1 size2 
  (Hge: size1>=size2) igns,
  notin_ignores_with_size igns b ofs size1 ->
  notin_ignores_with_size igns b ofs size2.
Proof.
  unfold notin_ignores_with_size.
  intros.
  induction H; simpl; auto.
    destruct x as [[b0 lo0] hi0].
    constructor; auto.
      destruct H as [H | [J1 [J2 | J3]]]; subst; auto.
        right. split; auto. omega.
Qed.

Lemma mload_aux_inj2:
  forall igns f b2 b1 (Hp1: MoreMem.meminj_no_overlap f)
  (Hp2: MoreMem.meminj_zero_delta f)
  mcs ofs delta gv1 gv2 m1 m2,
  mem_inj f igns m1 m2 ->
  mload_aux m1 mcs b1 ofs = Some gv1 ->
  f b1 = Some (b2, delta) ->
  notin_ignores_with_size igns b1 ofs (Z_of_nat (sizeMC mcs)) ->
  mload_aux m2 mcs b2 (ofs + delta) = Some gv2 ->
  gv_inject f gv1 gv2.
Proof.
  induction mcs; simpl; intros.
    inv H0. inv H3. auto.

    inv_mbind.
    constructor.
      eapply load_inj2; eauto.
        eapply notin_ignores_with_smaller_size in H2; eauto.
          rewrite inj_plus. rewrite <- size_chunk_conv. omega.
      replace (ofs + delta + size_chunk a) with
              (ofs + size_chunk a + delta) in HeqR0 by omega.
      eapply IHmcs with (ofs:=ofs+size_chunk a); eauto.
        rewrite inj_plus in H2. rewrite <- size_chunk_conv in H2. 
        apply notin_ignores_with_size_delta; auto.
          assert (J:=size_chunk_pos a). omega.
Qed.

Lemma mload_aux_inject_id_inj2:
  forall igns b mcs ofs gv1 gv2 m1 m2,
  mem_inj inject_id igns m1 m2 ->
  mload_aux m1 mcs b ofs = Some gv1 ->
  notin_ignores_with_size igns b ofs (Z_of_nat (sizeMC mcs)) ->
  mload_aux m2 mcs b ofs = Some gv2 ->
  gv1 = gv2.
Proof.
  intros.
  replace ofs with (ofs+0) in H2 by omega.
  eapply mload_aux_inj2 in H1; 
    eauto using inject_id_no_overlap, inject_id_zero_delta.
    apply gv_inject_id__eq in H1; auto.
    unfold inject_id. auto.
Qed.

Lemma no_alias_with_blk__notin_ignores_with_size: forall b' ofs' m' size mbs
  (Hnalias: 
    Forall (fun re : Values.block * Z * Z =>
            let '(mb, _, _) := re in
            memory_props.MemProps.no_alias_with_blk 
              ((Vptr b' ofs', m') :: nil) mb) mbs),
  notin_ignores_with_size mbs b' (Int.signed 31 ofs') size.
Proof.
  unfold notin_ignores_with_size.
  induction 1; simpl; auto.
    destruct x as [[]]. simpl in H.
    constructor; auto.
Qed.

Lemma mstore_aux_mapped_inj2: forall igns f b1 b2 delta
  (Hp: MoreMem.meminj_no_overlap f)
  (Hf: f b1 = Some (b2, delta)) gvs1 gvs2 m1 n1 m2 n2 ofs
  (Hmsim: mem_inj f igns m1 m2) (Hst1: mstore_aux m1 gvs1 b1 ofs = Some n1)
  (Hinj: gv_inject f gvs1 gvs2)
  (Hst2: mstore_aux m2 gvs2 b2 (ofs + delta) = Some n2),
  mem_inj f igns n1 n2.
Proof.
  induction gvs1 as [|[]]; simpl; intros.
    inv Hst1. inv Hinj. inv Hst2. auto.

    inv Hinj. simpl in Hst2.
    inv_mbind.
    assert (mem_inj f igns m3 m0) as Hinj'.
      eapply store_mapped_inj2 in Hmsim; eauto.
    replace (ofs + delta + size_chunk m) with
            (ofs + size_chunk m + delta) in H0 by omega.
    eapply IHgvs1; eauto.
Qed.

Lemma mstore_aux_inject_id_mapped_inj2: forall igns b gvs m1 n1 m2 n2 ofs
  (Hmsim: mem_inj inject_id igns m1 m2) 
  (Hst1: mstore_aux m1 gvs b ofs = Some n1)
  (Hst2: mstore_aux m2 gvs b ofs = Some n2),
  mem_inj inject_id igns n1 n2.
Proof.
  intros.
  replace ofs with (ofs+0) in Hst2 by omega.
  eapply mstore_aux_mapped_inj2 in Hmsim; 
    eauto using inject_id_no_overlap, inject_id_zero_delta.
    unfold inject_id. auto.
    apply gv_inject_id__refl; auto.
Qed.

Lemma mstore_aux_store_inside_inj2': forall igns f b1 b2 delta
  (Hp: MoreMem.meminj_no_overlap f)
  (Hf: f b1 = Some (b2, delta)) hi gvs1 gvs2 m1 n1 m2 n2 ofs
  (Hmsim: mem_inj f ((b1,ofs,hi)::igns) m1 m2) (Hst1: mstore_aux m1 gvs1 b1 ofs = Some n1)
  (Hinj: gv_inject f gvs1 gvs2)
  (Hst2: mstore_aux m2 gvs2 b2 (ofs + delta) = Some n2),
  mem_inj f ((b1,ofs+Z_of_nat (sizeGenericValue gvs1),hi)::igns) n1 n2.
Proof.
  induction gvs1 as [|[]]; simpl; intros.
    inv Hst1. inv Hinj. inv Hst2. 
    replace (ofs+0) with ofs by omega.
    auto.

    inv Hinj. simpl in Hst2.
    inv_mbind.
    assert (mem_inj f ((b1,ofs+size_chunk m,hi)::igns) m3 m0) as Hinj'.
      eapply store_inside_inj2 in Hmsim; eauto.
    replace (ofs + delta + size_chunk m) with
            (ofs + size_chunk m + delta) in H0 by omega.
    rewrite inj_plus.
    rewrite <- size_chunk_conv.
    replace (ofs + (size_chunk m + Z_of_nat (sizeGenericValue gvs1))) with
            (ofs + size_chunk m + Z_of_nat (sizeGenericValue gvs1)) by omega.
    eapply IHgvs1; eauto.
Qed.

Lemma notin_ignores__add_empty: forall b hi b1 ofs igns
  (Hnotin : notin_ignores igns b1 ofs),
  notin_ignores ((b, hi, hi) :: igns) b1 ofs.
Proof.
  unfold notin_ignores.
  intros.
  constructor; auto. 
    destruct (zeq b1 b); subst; auto.
    right.
    split; auto.
      omega.
Qed.

Lemma mem_inj__remove_empty_igns: forall f b hi igns n1 n2
  (Hmsim : mem_inj f ((b, hi, hi) :: igns) n1 n2),
  mem_inj f igns n1 n2.
Proof.
  intros.
  inv Hmsim.
  constructor; auto.
    intros.
    apply mi_memval0; auto using notin_ignores__add_empty.
Qed.

Lemma mem_inj__remove_unperm_igns: forall f b lo hi igns n1 n2
  (Hmsim : mem_inj f ((b, lo, hi) :: igns) n1 n2)
  (Hunperm: forall ofs p, lo <= ofs < hi -> ~Mem.perm n1 b ofs p),
  mem_inj f igns n1 n2.
Proof.
  intros.
  inv Hmsim.
  constructor; auto.
    intros.
    apply mi_memval0; auto. clear mi_memval0.
      unfold notin_ignores in *.
      constructor; auto.
        destruct (Z_eq_dec b1 b); subst; auto.
          right.
          split; auto.
            destruct (Z_lt_dec ofs lo); subst; auto.
            destruct (Z_ge_dec ofs hi); subst; auto.
              contradict H0.
              apply Hunperm. omega.
Qed.

Lemma mstore_aux_inside_inj2: forall igns f b1 b2 delta
  (Hp: MoreMem.meminj_no_overlap f)
  (Hf: f b1 = Some (b2, delta)) gvs1 gvs2 m1 n1 m2 n2 ofs
  (Hmsim: mem_inj f ((b1,ofs,ofs+Z_of_nat (sizeGenericValue gvs1))::igns) m1 m2) 
  (Hst1: mstore_aux m1 gvs1 b1 ofs = Some n1)
  (Hinj: gv_inject f gvs1 gvs2)
  (Hst2: mstore_aux m2 gvs2 b2 (ofs + delta) = Some n2),
  mem_inj f igns n1 n2.
Proof.
  intros.
  eapply mstore_aux_store_inside_inj2' in Hmsim; eauto.
  eapply mem_inj__remove_empty_igns; eauto.
Qed.

Lemma mstore_aux_inject_id_inside_inj2: forall igns b
  gvs m1 n1 m2 n2 ofs
  (Hmsim: mem_inj inject_id 
            ((b,ofs,ofs+Z_of_nat (sizeGenericValue gvs))::igns) m1 m2) 
  (Hst1: mstore_aux m1 gvs b ofs = Some n1)
  (Hst2: mstore_aux m2 gvs b ofs = Some n2),
  mem_inj inject_id igns n1 n2.
Proof.
  intros.
  replace ofs with (ofs+0) in Hst2 by omega.
  eapply mstore_aux_inside_inj2 in Hmsim; 
    eauto using inject_id_no_overlap, inject_id_zero_delta.
    unfold inject_id. auto.
    apply gv_inject_id__refl; auto.
Qed.

End SASmsim.

Fixpoint ombs__ignores (tsz:Z) (ombs: list (option Values.block))
  : list (Values.block*Z*Z) :=
match ombs with
| nil => nil
| Some mb::ombs' => (mb, 0, tsz)::ombs__ignores tsz ombs'
| None::ombs' => ombs__ignores tsz ombs'
end.

(* go to vellvm? *)
Lemma wf__getTypeStoreSize_eq_sizeGenericValue: forall (gl2 : GVMap)
  (lc2 : Opsem.GVsMap) (S : system) (los : layouts) (nts : namedts)
  (Ps : list product) (v1 : value) (gv1 : GenericValue)
  (Hwfg : LLVMgv.wf_global (los, nts) S gl2) (n : nat) t
  (HeqR : ret n = getTypeStoreSize (los, nts) t) F
  (H24 : @Opsem.getOperandValue DGVs (los, nts) v1 lc2 gl2 = ret gv1)
  (Hwflc1 : OpsemPP.wf_lc (los, nts) F lc2)
  (Hwfv : wf_value S (module_intro los nts Ps) F v1 t),
  n = sizeGenericValue gv1.
Proof.
  intros.
  eapply OpsemPP.getOperandValue__wf_gvs in Hwflc1; eauto.
  inv Hwflc1.
  assert (gv1 @ gv1) as Hinst. auto.
  apply H2 in Hinst.
  unfold gv_chunks_match_typ in Hinst.
  clear - Hinst HeqR Hwfv. inv_mbind.
  apply wf_value__wf_typ in Hwfv. destruct Hwfv as [J1 J2].
  symmetry in HeqR0.
  eapply flatten_typ__getTypeSizeInBits in HeqR0; eauto.
  destruct HeqR0 as [sz [al [A B]]].          
  unfold getTypeAllocSize, getTypeStoreSize, getABITypeAlignment,
         getTypeSizeInBits, getAlignment, 
         getTypeSizeInBits_and_Alignment in HeqR.
  rewrite A in HeqR.
  inv HeqR. rewrite B.
  eapply vm_matches_typ__sizeMC_eq_sizeGenericValue; eauto.
Qed.

Lemma wf_ECStack_head_in_tail__no_alias_with_blk: 
  forall (pinfo : palloca_props.PhiInfo)
  (lc2 : AssocList (GVsT DGVs)) (gv2 : GVsT DGVs) (S : system) (los : layouts)
  (nts : namedts) (Ps : products) (Mem : Memory.mem) (F : fdef) (t : typ)
  (v : value) (gl : GVMap) (Hwfv : wf_value S (module_intro los nts Ps) F v t)
  (maxb : Values.block) (Hget : getOperandValue (los, nts) v lc2 gl = ret gv2)
  (EC : Opsem.ExecutionContext) (Hwfg: MemProps.wf_globals maxb gl)
  (Hnals1 : Promotability.wf_ECStack_head_in_tail maxb pinfo 
             (los, nts) Mem lc2 EC)
  (b : Values.block) (i0 : int32) (m : AST.memory_chunk)
  (HeqR : lookupAL (GVsT DGVs) (Opsem.Locals EC) (palloca_props.PI_id pinfo) =
          ret ((Vptr b i0, m) :: nil))
  (G : Opsem.CurFunction EC = palloca_props.PI_f pinfo),
  MemProps.no_alias_with_blk gv2 b.
Proof.
  intros.
  destruct EC. simpl in *.
  destruct (@Hnals1 ((Vptr b i0, m) :: nil)) as [J5 [J2 J4]]; auto.
  destruct v as [id2 | c2]; simpl in *.
    apply J2 in Hget.
    simpl in Hget. tauto.
  
    inv Hwfv.
    destruct J5 as [mb [J6 [[J7 _] _]]].
    rewrite Promotability.simpl_blk2GV in J6. inv J6.
    symmetry in Hget.
    eapply Promotability.const2GV_disjoint_with_runtime_alloca with (t:=t) 
      (mb:=mb) in Hget; eauto.
    rewrite Promotability.simpl_blk2GV in Hget. 
    simpl in Hget. tauto.
Qed.

Lemma wf_defs__no_alias_with_blk: forall (pinfo : palloca_props.PhiInfo) 
  (los : layouts)
  (nts : namedts) (maxb : Values.block) (Mem : mem) (EC : Opsem.ExecutionContext)
  (gv2 : GenericValue) (gl : GVMap) (Hwfg : MemProps.wf_globals maxb gl)
  (v : value) (S : system) (t : typ) (Ps : products)
  (Hneq : primitives.used_in_value (palloca_props.PI_id pinfo) v = false)
  (Hget : getOperandValue (los, nts) v (@Opsem.Locals DGVs EC) gl = ret gv2)
  (Hwfv : wf_value S (module_intro los nts Ps) (Opsem.CurFunction EC) v t)
  (b : Values.block) (i0 : int32) (m : AST.memory_chunk)
  (HeqR : lookupAL (GVsT DGVs) (Opsem.Locals EC) (palloca_props.PI_id pinfo) =
            ret ((Vptr b i0, m) :: nil))
  (Hinscope : Promotability.wf_defs maxb pinfo (los, nts) Mem
               (Opsem.Locals EC) (Opsem.Allocas EC))
  (G : Opsem.CurFunction EC = palloca_props.PI_f pinfo),
  MemProps.no_alias_with_blk gv2 b.
Proof.
  intros.
  apply_clear Hinscope in HeqR.
  destruct HeqR as [J1 J2].
  destruct v as [id2 | c2].
    apply J2 in Hget.
    unfold Promotability.wf_non_alloca_GVs in Hget.
    simpl in Hneq.
    destruct (id_dec id2 (palloca_props.PI_id pinfo)); tinv Hneq.
    simpl in Hget. tauto.
  
    unfold Promotability.wf_alloca_GVs in J1.
    destruct J1 as [_ [[mb [J6 [_ [[J7 _] _]]]] _]].
    rewrite Promotability.simpl_blk2GV in J6. inv J6.
    symmetry in Hget. inv Hwfv.
    eapply Promotability.const2GV_disjoint_with_runtime_alloca with (t:=t) 
      (mb:=mb) in Hget; eauto.
    rewrite Promotability.simpl_blk2GV in Hget. 
    simpl in Hget. tauto.
Qed.
