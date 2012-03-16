Require Import Memory.
Require Import Values.
Require Import Coqlib.
Require Import Integers.
Require Import AST.
Require Import Znumtheory.
Require Import vellvm_tactics.
Require Import memory_sim.

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

Record mem_inj (f: meminj) (b:block) (lo hi:Z) (m1 m2: mem) : Prop :=
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
      b1 <> b \/ (b1 = b /\ (ofs < lo \/ ofs >= hi)) ->
      MoreMem.memval_inject f (m1.(mem_contents) b1 ofs) 
        (m2.(mem_contents) b2 (ofs + delta))
  }.

(** Preservation of permissions *)

Lemma perm_inj:
  forall b lo hi f m1 m2 b1 ofs p b2 delta,
  mem_inj f b lo hi m1 m2 ->
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

Lemma getN_inj:
  forall b lo hi f m1 m2 b1 b2 delta,
  mem_inj f b lo hi m1 m2 ->
  f b1 = Some(b2, delta) ->
  forall n ofs,
  range_perm m1 b1 ofs (ofs + Z_of_nat n) Readable ->
  b1 <> b \/ (b1 = b /\ (ofs + Z_of_nat n <= lo \/ ofs >= hi)) ->
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
        destruct H2 as [H2 | [H2 [H3 | H4]]]; subst; auto.
        right. 
        assert (J:=@Z_of_S_gt_O n).
        split; try solve [auto | omega].

      replace (ofs + delta + 1) with ((ofs + 1) + delta) by omega.
      apply IHn. 
        red; intros; apply H1; omega. 

        destruct H2 as [H2 | [H2 [H3 | H4]]]; subst; try solve 
          [auto | right; split; try solve [auto | omega]].
Qed.

Lemma load_inj:
  forall b lo hi f m1 m2 chunk b1 ofs b2 delta v1,
  MoreMem.meminj_no_overlap f ->
  MoreMem.meminj_zero_delta f ->
  mem_inj f b lo hi m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  b1 <> b \/ (b1 = b /\ (ofs + size_chunk chunk <= lo \/ ofs >= hi)) ->
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

(* go to Coqlib *)
Lemma list_forall2_length_eq:
  forall (A B: Type) (P1: A -> B -> Prop) (l1: list A) (l2: list B),
  list_forall2 P1 l1 l2 -> length l1 = length l2.
Proof.
  induction 1; intros; auto.
    simpl. congruence.
Qed.

Lemma store_mapped_inj:
  forall b lo hi f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inj f b lo hi m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  MoreMem.meminj_no_overlap f ->
  f b1 = Some (b2, delta) ->
  MoreMem.val_inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inj f b lo hi n1 n2.
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

Lemma store_mapped_inj_inside:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inj f b1 ofs (ofs+size_chunk chunk) m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  MoreMem.meminj_no_overlap f ->
  f b1 = Some (b2, delta) ->
  MoreMem.val_inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ MoreMem.mem_inj f n1 n2.
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
  apply MoreMem.encode_val_inject with (chunk:=chunk) in H3; auto.  
  assert (length (encode_val chunk v1) = length (encode_val chunk v2)) as EQ.
    eapply list_forall2_length_eq; eauto.
  destruct (Z_gt_dec ofs ofs0).
    apply setN_inj_outside; auto.
    eapply mi_memval0 in H7; eauto.
      right. split; auto. omega.
    destruct (Z_ge_dec ofs0 (ofs + Z_of_nat (length (encode_val chunk v1)))).
      apply setN_inj_outside; auto.
      eapply mi_memval0 in H7; eauto.
        rewrite encode_val_length in z. rewrite <- size_chunk_conv in z.
        right. split; auto.

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

Lemma store_unmapped_inj:
  forall b lo hi f chunk m1 b1 ofs v1 n1 m2,
  mem_inj f b lo hi m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  mem_inj f b lo hi n1 m2.
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
  forall b0 lo0 hi0 f m1 m2 chunk b ofs v m2',
  mem_inj f b0 lo0 hi0 m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Nonempty ->
    ofs' + delta < ofs \/ ofs' + delta >= ofs + size_chunk chunk) ->
  store chunk m2 b ofs v = Some m2' ->
  mem_inj f b0 lo0 hi0 m1 m2'.
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

(** Preservation of allocations *)

Lemma alloc_right_inj:
  forall b9 lo9 hi9 f m1 m2 lo hi b2 m2',
  mem_inj f b9 lo9 hi9 m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  mem_inj f b9 lo9 hi9 m1 m2'.
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
  forall b9 lo9 hi9 f m1 m2 lo hi m1' b1,
  mem_inj f b9 lo9 hi9 m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  f b1 = None ->
  mem_inj f b9 lo9 hi9 m1' m2.
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
  forall b9 lo9 hi9 f m1 m2 b lo hi m2',
  mem_inj f b9 lo9 hi9 m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs p ->
    lo <= ofs + delta < hi -> False) ->
  mem_inj f b9 lo9 hi9 m1 m2'.
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
    by (unfold block; omega).
  destruct J as [[J1 J2] | J]; subst.
    specialize (H1 _ _ _ _ H2 H3). elimtype False; auto.
    rewrite (clearN_out _ _ _ _ _ _ J); auto.
Qed.

Lemma free_inj:
  forall b9 lo9 hi9 f m1 m2 b1 b2 delta lo hi m1' m2',
  MoreMem.meminj_no_overlap f ->
  MoreMem.meminj_zero_delta f ->
  mem_inj f b9 lo9 hi9 m1 m2 ->
  free m1 b1 lo hi = Some m1' ->
  free m2 b2 (lo+delta) (hi+delta) = Some m2' ->
  f b1 = Some (b2, delta) ->
  mem_inj f b9 lo9 hi9 m1' m2'.
Proof.
  intros b9 lo9 hi9 f m1 m2 b1 b2 delta lo hi m1' m2' J J' H H0 H1 H2.
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
    by (unfold block; omega).
  assert (b2=b3 /\ lo+delta <= ofs+delta < hi+delta \/ 
    (b2<>b3 \/ ofs+delta<lo+delta \/ hi+delta <= ofs+delta)) 
    as J2 by (unfold block; omega).
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
  forall b9 lo9 hi9 f m1 m2 b lo hi m1' (Hprop: f b = None),
  mem_inj f b9 lo9 hi9 m1 m2 ->
  Mem.free m1 b lo hi = Some m1' ->
  mem_inj f b9 lo9 hi9 m1' m2.
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

End SASmsim.
