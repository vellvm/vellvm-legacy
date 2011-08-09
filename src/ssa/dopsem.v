Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import Metatheory.
Require Import alist.
Require Import monad.
Require Import genericvalues.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import ssa_def.
Require Import opsem.
Require Import opsem_props.
Require Import opsem_wf.

Module DGVs <: GenericValuesSig.

Export LLVMsyntax.
Export LLVMgv.

Definition t := GenericValue.
Definition Map := list (id * t).
Definition instantiate_gvs (gv : GenericValue) (gvs : t) : Prop := gvs = gv.
Definition inhabited (gvs : t) : Prop := True.
Definition cundef_gvs := LLVMgv.cundef_gv.
Definition undef_gvs gv (ty:typ) : t := gv.
Definition cgv2gvs := LLVMgv.cgv2gv.
Definition gv2gvs (gv:GenericValue) (ty:typ) : t := gv.

Hint Unfold instantiate_gvs inhabited.

Notation "gv @ gvs" :=  
  (instantiate_gvs gv gvs) (at level 43, right associativity).
Notation "$ gv # t $" := (gv2gvs gv t) (at level 41).

Lemma cundef_gvs__getTypeSizeInBits : forall S los nts gv ty sz al gv',
  wf_typ S ty ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true ty = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  gv' @ (cundef_gvs gv ty) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = 
    sizeGenericValue gv'.
Proof.
  unfold instantiate_gvs. 
  intros. inv H2.
  eapply LLVMgv.cundef_gv__getTypeSizeInBits; eauto.
Qed.

Lemma cundef_gvs__inhabited : forall gv ty, inhabited (cundef_gvs gv ty).
Proof. auto. Qed.

Lemma undef_gvs__getTypeSizeInBits : forall S los nts gv t sz al gv',
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  gv' @ (undef_gvs gv t) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = 
    sizeGenericValue gv'.
Proof. 
  unfold instantiate_gvs. 
  intros. inv H2. auto.
Qed.

Lemma undef_gvs__inhabited : forall gv ty, inhabited (undef_gvs gv ty).
Proof. auto. Qed.

Lemma cgv2gvs__getTypeSizeInBits : forall S los nts gv t sz al gv',
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  gv' @ (cgv2gvs gv t) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = 
    sizeGenericValue gv'.
Proof.
  unfold instantiate_gvs. 
  intros. inv H2.
  eapply LLVMgv.cgv2gv__getTypeSizeInBits; eauto.
Qed.

Lemma cgv2gvs__inhabited : forall gv t, inhabited (cgv2gvs gv t).
Proof. auto. Qed.

Lemma gv2gvs__getTypeSizeInBits : forall S los nts gv t sz al,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  forall gv', gv' @ (gv2gvs gv t) ->
  sizeGenericValue gv' = Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8).
Proof.
  unfold instantiate_gvs. 
  intros. inv H2. auto.
Qed.

Lemma gv2gvs__inhabited : forall gv t, inhabited ($ gv # t $).
Proof. auto. Qed.

Definition lift_op1 (f: GenericValue -> option GenericValue) (gvs1:t) (ty:typ) : 
  option t := f gvs1.

Definition lift_op2 (f: GenericValue -> GenericValue -> option GenericValue)
  (gvs1 gvs2:t) (ty: typ) : option t := f gvs1 gvs2.

Lemma lift_op1__inhabited : forall f gvs1 ty gvs2
  (H:forall x, exists z, f x = Some z),
  inhabited gvs1 -> 
  lift_op1 f gvs1 ty = Some gvs2 ->
  inhabited gvs2.
Proof. auto. Qed.

Lemma lift_op2__inhabited : forall f gvs1 gvs2 t gvs3
  (H:forall x y, exists z, f x y = Some z),
  inhabited gvs1 -> inhabited gvs2 ->
  lift_op2 f gvs1 gvs2 t = Some gvs3 ->
  inhabited gvs3.
Proof. auto. Qed.

Lemma lift_op1__isnt_stuck : forall f gvs1 ty
  (H:forall x, exists z, f x = Some z),
  exists gvs2, lift_op1 f gvs1 ty = Some gvs2.
Proof. unfold lift_op1. auto. Qed.

Lemma lift_op2__isnt_stuck : forall f gvs1 gvs2 t
  (H:forall x y, exists z, f x y = Some z),
  exists gvs3, lift_op2 f gvs1 gvs2 t = Some gvs3.
Proof. unfold lift_op2. auto. Qed.

Lemma lift_op1__getTypeSizeInBits : forall S los nts f g t sz al gvs,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  (forall x y, x @ g -> f x = Some y -> 
   sizeGenericValue y = nat_of_Z (ZRdiv (Z_of_nat sz) 8)) ->
  lift_op1 f g t = Some gvs ->
  forall gv : GenericValue,
  gv @ gvs ->
  sizeGenericValue gv = nat_of_Z (ZRdiv (Z_of_nat sz) 8).
Proof. intros. unfold lift_op1 in H2. inv H3. eauto. Qed.

Lemma lift_op2__getTypeSizeInBits : forall S los nts f g1 g2 t sz al gvs,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  (forall x y z, x @ g1 -> y @ g2 -> f x y = Some z -> 
   sizeGenericValue z = nat_of_Z (ZRdiv (Z_of_nat sz) 8)) ->
  lift_op2 f g1 g2 t = Some gvs ->
  forall gv : GenericValue,
  gv @ gvs ->
  sizeGenericValue gv = nat_of_Z (ZRdiv (Z_of_nat sz) 8).
Proof. intros. unfold lift_op2 in H2. inv H3. eauto. Qed.

Lemma inhabited_inv : forall gvs, inhabited gvs -> exists gv, gv @ gvs.
Proof. eauto. Qed.

Lemma instantiate_undef__undef_gvs : forall gv t, gv @ (undef_gvs gv t).
Proof. auto. Qed.

Lemma instantiate_gv__gv2gvs : forall gv t, gv @ ($ gv # t $).
Proof. auto. Qed.

Lemma none_undef2gvs_inv : forall gv gv' t,
  gv @ $ gv' # t $ -> (forall mc, (Vundef, mc)::nil <> gv') -> gv = gv'.
Proof.
  intros.
  destruct gv'; try solve [inv H; auto].
Qed.

End DGVs.

Ltac dgvs_instantiate_inv :=
  match goal with
  | [ H : DGVs.instantiate_gvs _ _ |- _ ] => inv H
  end.

Module DOS := OpsemPP DGVs.

Lemma dos_in_list_gvs_intro : forall gvs, DOS.Sem.in_list_gvs gvs gvs.
Proof. 
  induction gvs; simpl; auto. 
Qed.

Lemma dos_in_list_gvs_inv : forall gvs gvss, 
  DOS.Sem.in_list_gvs gvs gvss -> gvs = gvss.
Proof.
  induction 1; subst; try dgvs_instantiate_inv; auto. 
Qed.

Hint Resolve dos_in_list_gvs_intro.



(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)

