Require Import Metatheory.
Require Import alist.
Require Import monad.
Require Import targetdata.
Require Import genericvalues.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import syntax.
Require Import typings.
Require Import static.
Require Import opsem.
Require Import opsem_props.
Require Import opsem_wf.
Require Import vellvm_tactics.
Require Import infrastructure.
Require Import infrastructure_props.

Import LLVMsyntax.
Import LLVMgv.
Import LLVMtd.
Import LLVMtypings.
Import LLVMinfra.

Module MDGVs.

Definition t := GenericValue.
Definition instantiate_gvs (gv : GenericValue) (gvs : t) : Prop := gvs = gv.
Definition inhabited (gvs : t) : Prop := True.
Definition cundef_gvs := LLVMgv.cundef_gv.
Definition undef_gvs gv (ty:typ) : t := gv.
Definition cgv2gvs := LLVMgv.cgv2gv.
Definition gv2gvs (gv:GenericValue) (ty:typ) : t := gv.

Notation "gv @ gvs" :=
  (instantiate_gvs gv gvs) (at level 43, right associativity).
Notation "$ gv # t $" := (gv2gvs gv t) (at level 41).
Hint Unfold inhabited instantiate_gvs.

Lemma cundef_gvs__getTypeSizeInBits : forall S los nts gv ty sz al gv',
  wf_typ S (los,nts) ty ->
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
  eapply cundef_gv__getTypeSizeInBits; eauto.
Qed.

Lemma cundef_gvs__matches_chunks : forall S los nts gv ty gv',
  wf_typ S (los,nts) ty ->
  gv_chunks_match_typ (los, nts) gv ty ->
  gv' @ (cundef_gvs gv ty) ->
  gv_chunks_match_typ (los, nts) gv' ty.
Proof.
  unfold instantiate_gvs.
  intros. subst.
  eapply cundef_gv__matches_chunks; eauto.
Qed.

Lemma cundef_gvs__inhabited : forall gv ty, inhabited (cundef_gvs gv ty).
Proof. auto. Qed.

Lemma undef_gvs__getTypeSizeInBits : forall S los nts gv t sz al gv',
  wf_typ S (los,nts) t ->
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

Lemma undef_gvs__matches_chunks : forall S los nts gv ty gv',
  wf_typ S (los,nts) ty ->
  gv_chunks_match_typ (los, nts) gv ty ->
  gv' @ (undef_gvs gv ty) ->
  gv_chunks_match_typ (los, nts) gv' ty.
Proof.
  unfold instantiate_gvs.
  intros. subst. auto.
Qed.

Lemma undef_gvs__inhabited : forall gv ty, inhabited (undef_gvs gv ty).
Proof. auto. Qed.

Lemma cgv2gvs__getTypeSizeInBits : forall S los nts gv t sz al gv',
  wf_typ S (los,nts) t ->
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
  eapply cgv2gv__getTypeSizeInBits; eauto.
Qed.

Lemma cgv2gvs__matches_chunks : forall S los nts gv t gv',
  wf_typ S (los,nts) t ->
  gv_chunks_match_typ (los, nts) gv t ->
  gv' @ (cgv2gvs gv t) ->
  gv_chunks_match_typ (los, nts) gv' t.
Proof.
  unfold instantiate_gvs.
  intros. subst. unfold cgv2gvs.
  destruct gv; auto.
  destruct p as [[]]; auto. 
  destruct gv; auto.
  eapply cundef_gvs__matches_chunks; eauto.
Qed.

Lemma cgv2gvs__inhabited : forall gv t, inhabited (cgv2gvs gv t).
Proof. auto. Qed.

Lemma gv2gvs__getTypeSizeInBits : forall S los nts gv t sz al,
  wf_typ S (los,nts) t ->
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

Lemma gv2gvs__matches_chunks : forall S los nts gv t,
  wf_typ S (los,nts) t ->
  gv_chunks_match_typ (los, nts) gv t ->
  forall gv', gv' @ (gv2gvs gv t) ->
  gv_chunks_match_typ (los, nts) gv' t.
Proof.
  unfold instantiate_gvs.
  intros. subst. auto.
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
  wf_typ S (los,nts) t ->
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

Lemma lift_op1__matches_chunks : forall S los nts f g t gvs,
  wf_typ S (los,nts) t ->
  (forall x y, instantiate_gvs x g -> f x = Some y ->
    gv_chunks_match_typ (los, nts) y t) ->
  lift_op1 f g t = Some gvs ->
  forall gv : GenericValue,
  instantiate_gvs gv gvs ->
  gv_chunks_match_typ (los, nts) gv t.
Proof. intros. unfold lift_op1 in H1. inv H2. eauto. Qed.

Lemma lift_op2__getTypeSizeInBits : forall S los nts f g1 g2 t sz al gvs,
  wf_typ S (los,nts) t ->
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

Lemma lift_op2__matches_chunks : forall S los nts f g1 g2 t gvs,
  wf_typ S (los,nts) t ->
  (forall x y z,
   instantiate_gvs x g1 -> instantiate_gvs y g2 -> f x y = Some z ->
   gv_chunks_match_typ (los, nts) z t) ->
  lift_op2 f g1 g2 t = Some gvs ->
  forall gv : GenericValue,
  instantiate_gvs gv gvs ->
  gv_chunks_match_typ (los, nts) gv t.
Proof. intros. unfold lift_op2 in H1. inv H2. eauto. Qed.

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

End MDGVs.

Definition DGVs : GenericValues := mkGVs
MDGVs.t
MDGVs.instantiate_gvs
MDGVs.inhabited
MDGVs.cgv2gvs
MDGVs.gv2gvs
MDGVs.lift_op1
MDGVs.lift_op2
MDGVs.cgv2gvs__getTypeSizeInBits
MDGVs.cgv2gvs__matches_chunks
MDGVs.cgv2gvs__inhabited
MDGVs.gv2gvs__getTypeSizeInBits
MDGVs.gv2gvs__matches_chunks
MDGVs.gv2gvs__inhabited
MDGVs.lift_op1__inhabited
MDGVs.lift_op2__inhabited
MDGVs.lift_op1__isnt_stuck
MDGVs.lift_op2__isnt_stuck
MDGVs.lift_op1__getTypeSizeInBits
MDGVs.lift_op2__getTypeSizeInBits
MDGVs.lift_op1__matches_chunks
MDGVs.lift_op2__matches_chunks
MDGVs.inhabited_inv
MDGVs.instantiate_gv__gv2gvs
MDGVs.none_undef2gvs_inv.

Notation "gv @ gvs" :=
  (DGVs.(instantiate_gvs) gv gvs) (at level 43, right associativity).
Notation "$ gv # t $" := (DGVs.(gv2gvs) gv t) (at level 41).
Notation "vidxs @@ vidxss" := (@Opsem.in_list_gvs DGVs vidxs vidxss)
  (at level 43, right associativity).

Lemma dos_in_list_gvs_inv : forall gvs gvss, gvs @@ gvss -> gvs = gvss.
Proof.
  induction 1; subst; auto.
    inv H; auto.
Qed.

Lemma dos_in_gvs_inv : forall gvs gvss, gvs @ gvss -> gvs = gvss.
Proof.
  intros. inv H; auto.
Qed.

Ltac dgvs_instantiate_inv :=
  match goal with
  | [ H : DGVs.(instantiate_gvs) _ _ |- _ ] => inv H
  | [ H : _ @@ _ |- _ ] => apply dos_in_list_gvs_inv in H; subst
  end.

Lemma dos_instantiate_gvs_intro : forall gv, gv @ gv.
Proof.
Local Transparent instantiate_gvs.
  unfold instantiate_gvs. simpl. auto.
Global Opaque instantiate_gvs.
Qed.

Hint Resolve dos_instantiate_gvs_intro.

Lemma dos_in_list_gvs_intro : forall gvs, gvs @@ gvs.
Proof.
  induction gvs; simpl; auto.
Qed.

Hint Resolve dos_in_list_gvs_intro.

(*************************************)
Definition DGVMap := @Opsem.GVsMap DGVs.

(*************************************)
(* Aux invariants of wf ECs *)

Definition wfEC_inv s m (EC: @Opsem.ExecutionContext DGVs) : Prop :=
uniqFdef (Opsem.CurFunction EC) /\ 
blockInFdefB (Opsem.CurBB EC) (Opsem.CurFunction EC) = true /\
match Opsem.CurCmds EC with
| nil => wf_insn s m (Opsem.CurFunction EC) (Opsem.CurBB EC) 
           (insn_terminator (Opsem.Terminator EC))
| c::_ => wf_insn s m (Opsem.CurFunction EC) (Opsem.CurBB EC) 
           (insn_cmd c)
end /\
exists l0, exists ps0, exists cs0,
  Opsem.CurBB EC = (l0, stmts_intro ps0 (cs0 ++ Opsem.CurCmds EC)
    (Opsem.Terminator EC)).

Definition wfECs_inv s m (ECs: list (@Opsem.ExecutionContext DGVs)) : Prop :=
List.Forall (wfEC_inv s m) ECs.

Lemma wf_EC__wfEC_inv: forall S los nts Ps EC
  (HwfS : wf_system S) 
  (HMinS : moduleInSystemB (module_intro los nts Ps) S = true)
  (Hwfec : OpsemPP.wf_ExecutionContext (los, nts) Ps EC),
  wfEC_inv S (module_intro los nts Ps) EC.
Proof.
  destruct EC; simpl.
  intros.
  destruct Hwfec as [J1 [J2 [J3 [J4 [J5 J6]]]]].
  unfold wfEC_inv. simpl.
  split; eauto 2 using wf_system__uniqFdef.
  split; auto.
  split; auto.
    destruct J6 as [l1 [ps1 [cs1 J6]]]; subst.
    destruct CurCmds.
      eapply wf_system__wf_tmn in J2; eauto.
      eapply wf_system__wf_cmd in J2; eauto using in_middle.
Qed.

Lemma wf_ECStack__wfECs_inv: forall S los nts Ps ECs
  (HwfS : wf_system S) 
  (HMinS : moduleInSystemB (module_intro los nts Ps) S = true)
  (Hwf : OpsemPP.wf_ECStack (los, nts) Ps ECs),
  wfECs_inv S (module_intro los nts Ps) ECs.
Proof.
  unfold wfECs_inv.
  induction ECs as [|]; simpl; intros; auto.
    destruct Hwf as [J1 [J2 J3]].
    constructor; eauto using wf_EC__wfEC_inv.
Qed.

Lemma wf_State__wfECs_inv: forall cfg St (Hwfc: OpsemPP.wf_Config cfg) 
  (Hwfst: OpsemPP.wf_State cfg St), 
  wfECs_inv (OpsemAux.CurSystem cfg) 
    (module_intro (fst (OpsemAux.CurTargetData cfg))
                  (snd (OpsemAux.CurTargetData cfg))
                  (OpsemAux.CurProducts cfg) )
    (Opsem.ECS St).
Proof.
  intros.
  destruct cfg as [? [? ?] ? ?].
  destruct St.
  destruct Hwfc as [? [? [? ?]]].
  destruct Hwfst. simpl.
  eapply wf_ECStack__wfECs_inv; eauto.
Qed.

Definition uniqEC (EC: @Opsem.ExecutionContext DGVs) : Prop :=
uniqFdef (Opsem.CurFunction EC) /\ 
blockInFdefB (Opsem.CurBB EC) (Opsem.CurFunction EC) = true /\
exists l0, exists ps0, exists cs0,
  Opsem.CurBB EC = (l0, stmts_intro ps0 (cs0 ++ Opsem.CurCmds EC)
    (Opsem.Terminator EC)).

Definition uniqECs (ECs: list (@Opsem.ExecutionContext DGVs)) : Prop :=
List.Forall uniqEC ECs.

Lemma wfEC_inv__uniqEC: forall s m EC (Hwf: wfEC_inv s m EC), uniqEC EC.
Proof.
  intros.
  destruct Hwf as [J1 [J3 [_ J2]]]. split; auto.
Qed.

Lemma wfECs_inv__uniqECs: forall s m ECs (Hwf: wfECs_inv s m ECs), uniqECs ECs.
Proof.
  unfold wfECs_inv, uniqECs.
  intros.
  induction Hwf; auto.
    constructor; auto.
      apply wfEC_inv__uniqEC in H; auto.
Qed.

Lemma wf_State__uniqECs: forall cfg St (Hwfc: OpsemPP.wf_Config cfg) 
  (Hwfst: OpsemPP.wf_State cfg St), uniqECs (Opsem.ECS St).
Proof.
  intros.
  destruct cfg as [? [? ?] ? ?].
  destruct St.
  destruct Hwfc as [? [? [? ?]]].
  destruct Hwfst. simpl.
  eapply wf_ECStack__wfECs_inv in H4; eauto.
  eapply wfECs_inv__uniqECs; eauto.
Qed.

Ltac find_uniqEC :=
repeat match goal with
| H: uniqECs (Opsem.ECS {|Opsem.ECS := _; Opsem.Mem := _ |}) |- uniqEC _ => 
  simpl in H
| H: uniqECs (?EC::_) |- uniqEC ?EC => inv H; auto
| H: uniqECs (_::?EC::_) |- uniqEC ?EC => inv H; auto
| H: Forall uniqEC (?EC::_) |- uniqEC ?EC => inv H; auto
| H: Forall uniqEC (_::?EC::_) |- uniqEC ?EC => inv H; auto
end.

Lemma GEP_inv: forall TD t (mp1 : GVsT DGVs) inbounds0 vidxs mp2 t'
  (H1 : Opsem.GEP TD t mp1 vidxs inbounds0 t' = ret mp2),
  gundef TD (typ_pointer t') = ret mp2 \/
  exists blk, exists ofs1, exists ofs2 : int32, exists m1, exists m2,
    mp1 = (Vptr blk ofs1, m1) :: nil /\ mp2 = (Vptr blk ofs2, m2) :: nil.
Proof.
Local Transparent lift_op1.
  intros.
  unfold Opsem.GEP in H1. unfold lift_op1 in H1. simpl in H1.
  unfold MDGVs.lift_op1 in H1.
  unfold gep in H1. unfold GEP in H1.
  remember (GV2ptr TD (getPointerSize TD) mp1) as R1.
  destruct R1; auto.
  destruct (GVs2Nats TD vidxs); auto.
  remember (mgep TD t v l0) as R2.
  destruct R2; auto.
  inv H1.
  unfold mgep in HeqR2.
  destruct v; tinv HeqR2.
  destruct l0; tinv HeqR2.
  destruct (mgetoffset TD (typ_array 0%nat t) (z :: l0)) as [[]|];
    inv HeqR2.
  unfold GV2ptr in HeqR1.
  destruct mp1 as [|[]]; tinv HeqR1.
  destruct v; tinv HeqR1.
  destruct mp1; inv HeqR1.
  unfold ptr2GV. unfold val2GV. right. exists b0. exists i1.
  exists (Int.add 31 i1 (Int.repr 31 z0)). exists m.
  exists (AST.Mint (Size.mul Size.Eight (getPointerSize TD) - 1)).
  eauto.
Opaque lift_op1.
Qed.

