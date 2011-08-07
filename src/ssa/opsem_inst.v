Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import Ensembles.
Require Import ssa_def.
Require Import ssa_lib.
Require Import ssa_props.
Require Import ssa_analysis.
Require Import ssa_static.
Require Import ssa_static_lib.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import Floats.
Require Import AST.
Require Import Maps.
Require Import opsem.
Require Import opsem_props.
Require Import dopsem.

(************** Instantiate GVs ******************)

Module NDGVs <: GenericValuesSig.

Export LLVMsyntax.
Export LLVMgv.

Lemma singleton_inhabited : forall U (x:U), Inhabited U (Singleton U x).
Proof.
  intros. apply Inhabited_intro with (x:=x); auto using In_singleton.
Qed.

Lemma full_set_inhabited : forall U, 
  (exists x:U, True) -> Inhabited U (Full_set U).
Proof.
  intros. inversion H.
  apply Inhabited_intro with (x:=x); auto using Full_intro.
Qed.

Definition t := Ensemble GenericValue.
Definition Map := list (id * t).
Definition instantiate_gvs (gv : GenericValue) (gvs : t) : Prop :=
  Ensembles.In _ gvs gv.
Definition inhabited (gvs : t) : Prop := Ensembles.Inhabited _ gvs.
Hint Unfold instantiate_gvs inhabited.
Definition cundef_gvs gv ty : t :=
match ty with
| typ_int sz => fun gv => exists z, gv = (Vint sz z, Mint (sz - 1))::nil
| typ_floatpoint fp_float => fun gv => exists f, gv = (Vfloat f, Mfloat32)::nil
| typ_floatpoint fp_double => fun gv => exists f, gv = (Vfloat f, Mfloat64)::nil
| typ_pointer _ => 
    fun gv => exists b, exists ofs, gv = (Vptr b ofs, AST.Mint 31)::nil
| _ => Singleton GenericValue gv
end.

Definition undef_gvs gv ty : t :=
match ty with
| typ_int sz =>
    Ensembles.Union _ (Singleton _ gv)
      (fun gv => exists z, gv = (Vint sz z, Mint (sz-1))::nil)
| typ_floatpoint fp_float => 
    Ensembles.Union _ (Singleton _ gv)
      (fun gv => exists f, gv = (Vfloat f, Mfloat32)::nil)
| typ_floatpoint fp_double => 
    Ensembles.Union _ (Singleton _ gv)
      (fun gv => exists f, gv = (Vfloat f, Mfloat64)::nil)
| typ_pointer _ =>
    Ensembles.Union _ (Singleton _ gv)
      (fun gv => exists b, exists ofs, gv = (Vptr b ofs, AST.Mint 31)::nil)
| _ => Singleton GenericValue gv
end.

Definition cgv2gvs (gv:GenericValue) ty : t :=
match gv with
| (Vundef, _)::nil => cundef_gvs gv ty
| _ => Singleton _ gv
end.

Definition gv2gvs (gv:GenericValue) (ty:typ) : t :=
match gv with
| (Vundef, _)::nil => undef_gvs gv ty
| _ => Singleton GenericValue gv
end.

Notation "gv @ gvs" :=  
  (instantiate_gvs gv gvs) (at level 43, right associativity).
Notation "$ gv # t $" := (gv2gvs gv t) (at level 41).

Lemma cundef_gvs__getTypeSizeInBits : forall S los nts gv t sz al gv',
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  gv' @ (cundef_gvs gv t) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = 
    sizeGenericValue gv'.
Proof.
  intros S los nts gv t sz al gv' Hwft Heq1 Heq2 Hin.
  destruct t; simpl in *;
    try solve [inv Heq1; inv Hin; erewrite int_typsize; eauto |
               inv Heq1; inv Hin; eauto].
    destruct f; try solve [inv Heq1; inv Hin; eauto].
    inv Heq1. inv Hin. inv H. simpl. auto.
Qed.

Lemma cundef_gvs__inhabited : forall gv ty, inhabited (cundef_gvs gv ty).
Proof.
  destruct ty; simpl; 
    try solve [eapply Ensembles.Inhabited_intro; constructor].
    eapply Ensembles.Inhabited_intro.
      exists (Int.zero s). auto.

    destruct f; try solve [
      eapply Ensembles.Inhabited_intro; exists Float.zero; auto |
      eapply Ensembles.Inhabited_intro; constructor].

    eapply Ensembles.Inhabited_intro.
      exists Mem.nullptr. exists (Int.repr 31 0). auto.
Qed.

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
  intros S los nts gv t sz al gv' Hwft Heq1 Heq2 Hin.
  destruct t; simpl in *;
    try solve [inv Heq1; inv Hin; erewrite int_typsize; eauto |
               inv Heq1; inv Hin; eauto].

    inv Heq1; inv Hin; inv H; unfold Size.to_nat; 
      try solve [eauto | erewrite int_typsize; eauto].

    destruct f; try solve [inv Heq1; inv Hin; eauto |
                           inv Heq1; inv Hin; inv H; auto].

    inv Heq1; inv Hin; inv H; auto.
      inv H0. auto.
Qed.

Lemma undef_gvs__inhabited : forall gv ty, inhabited (undef_gvs gv ty).
Proof.
  destruct ty; simpl; try solve [
    eapply Ensembles.Inhabited_intro; apply Union_introl; constructor |
    eapply Ensembles.Inhabited_intro; constructor].

    destruct f; try solve [
      eapply Ensembles.Inhabited_intro; apply Union_introl; constructor |
      eapply Ensembles.Inhabited_intro; constructor].
Qed.

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
  intros S los nts gv t sz al gv' Hwft Heq1 Heq2 Hin.
  destruct gv; simpl in *.
    inv Hin. simpl. auto.

    destruct p.
    destruct v; try solve [inv Hin; simpl; auto].
    destruct gv; try solve [inv Hin; simpl; auto].
      eapply cundef_gvs__getTypeSizeInBits in Hin; eauto.
Qed.

Lemma cgv2gvs__inhabited : forall gv t, inhabited (cgv2gvs gv t).
Proof.
  intros gv t.
  destruct gv; simpl.
    apply Ensembles.Inhabited_intro with (x:=nil).
    apply Ensembles.In_singleton.

    destruct p.
    destruct v; auto using singleton_inhabited, cundef_gvs__inhabited.
    destruct gv; auto using singleton_inhabited, cundef_gvs__inhabited.
Qed.

Lemma gv2gvs__getTypeSizeInBits : forall S los nts gv t sz al,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  forall gv', gv' @ (gv2gvs gv t) ->
  sizeGenericValue gv' = Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8).
Proof.
  intros S los nts gv t sz al gv' Hwft Heq1 Heq2 Hin.
  destruct gv; simpl in *.
    inv Hin. simpl. auto.

    destruct p.
    destruct v; try solve [inv Hin; simpl; auto].
    destruct gv; try solve [inv Hin; simpl; auto].
      eapply undef_gvs__getTypeSizeInBits in Hin; eauto.
Qed.

Lemma gv2gvs__inhabited : forall gv t, inhabited ($ gv # t $).
Proof.
  intros gv t.
  destruct gv; simpl.
    apply Ensembles.Inhabited_intro with (x:=nil).
    apply Ensembles.In_singleton.

    destruct p.
    destruct v; auto using singleton_inhabited, undef_gvs__inhabited.
    destruct gv; auto using singleton_inhabited, undef_gvs__inhabited.
Qed.

Definition lift_op1 (f: GenericValue -> option GenericValue) gvs1 ty : option t 
  :=
  Some (fun gv2 => exists gv1, exists gv2', 
    gv1 @ gvs1 /\ f gv1 = Some gv2' /\ (gv2 @ $ gv2' # ty $)).

Definition lift_op2 (f: GenericValue -> GenericValue -> option GenericValue)
  gvs1 gvs2 ty : option t :=
  Some (fun gv3 => exists gv1, exists gv2, exists gv3',
    gv1 @ gvs1 /\ gv2 @ gvs2 /\ f gv1 gv2 = Some gv3' /\ (gv3 @ $ gv3' # ty $)).

Lemma lift_op1__inhabited : forall f gvs1 ty gvs2
  (H:forall x, exists z, f x = Some z),
  inhabited gvs1 -> 
  lift_op1 f gvs1 ty = Some gvs2 -> 
  inhabited gvs2.
Proof.
  intros. inv H1. inv H0.
  destruct (@H x) as [z J].
  destruct (@gv2gvs__inhabited z ty).
  exists x0. unfold Ensembles.In. exists x. exists z.
  rewrite J.
  repeat (split; auto).
Qed.

Lemma lift_op2__inhabited : forall f gvs1 gvs2 ty gv3
  (H:forall x y, exists z, f x y = Some z),
  inhabited gvs1 -> inhabited gvs2 ->
  lift_op2 f gvs1 gvs2 ty = Some gv3 ->
  inhabited gv3.
Proof.
  intros. inv H0. inv H1. inv H2.
  destruct (@H x x0) as [z J].
  destruct (@gv2gvs__inhabited z ty).
  exists x1. unfold Ensembles.In. exists x. exists x0. exists z.
  rewrite J.
  repeat (split; auto).
Qed.

Lemma lift_op1__isnt_stuck : forall f gvs1 ty
  (H:forall x, exists z, f x = Some z),
  exists gvs2, lift_op1 f gvs1 ty = Some gvs2.
Proof.
  intros. unfold lift_op1. eauto.
Qed.

Lemma lift_op2__isnt_stuck : forall f gvs1 gvs2 ty
  (H:forall x y, exists z, f x y = Some z),
  exists gv3, lift_op2 f gvs1 gvs2 ty = Some gv3.
Proof.
  intros. unfold lift_op2. eauto.
Qed.

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
Proof.
  intros. inv H2.
  destruct H3 as [x [y [J1 [J2 J3]]]].
  apply H1 in J2; auto.
  eapply gv2gvs__getTypeSizeInBits; eauto.
Qed.

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
Proof.
  intros. inv H2.
  destruct H3 as [x [y [z [J1 [J2 [J3 J4]]]]]].
  apply H1 in J3; auto.
  eapply gv2gvs__getTypeSizeInBits; eauto.
Qed.

Lemma inhabited_inv : forall gvs, inhabited gvs -> exists gv, gv @ gvs.
Proof.
  intros. inv H; eauto.
Qed.

Lemma instantiate_undef__undef_gvs : forall gv t, gv @ (undef_gvs gv t).
Proof.
  intros. unfold undef_gvs.
  destruct t0; try solve [apply Union_introl; constructor | constructor].
  destruct f; try solve [apply Union_introl; constructor | constructor].
Qed.

Lemma instantiate_gv__gv2gvs : forall gv t, gv @ ($ gv # t $).
Proof.
  intros.
  destruct gv; simpl; try constructor.
  destruct p; simpl; try constructor.
  destruct v; simpl; try constructor.
  destruct gv; simpl; 
    try solve [constructor | auto using instantiate_undef__undef_gvs].  
Qed.

Lemma none_undef2gvs_inv : forall gv gv' t,
  gv @ $ gv' # t $ -> (forall mc, (Vundef, mc)::nil <> gv') -> gv = gv'.
Proof.
  intros.
  destruct gv'; try solve [inv H; auto].
  destruct p.
  destruct v; try solve [inv H; auto].
  destruct gv'; try solve [inv H; auto].
  assert (J:=@H0 m). congruence.
Qed.

End NDGVs.

Module NDOS := Opsem NDGVs.

Module OpsemInstantiation.

Definition instantiate_gvs (gvs1:DGVs.t) (gvs2: NDGVs.t) : Prop :=
forall gv1, 
  DGVs.instantiate_gvs gv1 gvs1 -> NDGVs.instantiate_gvs gv1 gvs2.

Hint Unfold instantiate_gvs.

Lemma instantiate_gvs__incl : forall x y x0,
  instantiate_gvs x y ->
  DGVs.instantiate_gvs x0 x ->
  NDGVs.instantiate_gvs x0 y.
Proof. auto. Qed.

Lemma instantiate_gvs__gv2gvs : forall gv t, 
  instantiate_gvs (DGVs.gv2gvs gv t) (NDGVs.gv2gvs gv t).
Proof. 
  intros.
  unfold DGVs.gv2gvs, NDGVs.gv2gvs.
  destruct gv; try solve [intros gvs1 J; inv J; constructor].
  destruct p.
  destruct v; try solve [intros gvs1 J; inv J; constructor].
  destruct gv; try solve [intros gvs1 J; inv J; constructor].
  destruct t; simpl;
    try solve [intros gvs1 J; inv J; 
               (constructor || apply Union_introl; constructor)].
  destruct f; simpl;
    try solve [intros gvs1 J; inv J; 
               (constructor || apply Union_introl; constructor)].
Qed.

Lemma instantiate_gvs__cgv2gvs : forall gv t, 
  instantiate_gvs (DGVs.cgv2gvs gv t) (NDGVs.cgv2gvs gv t).
Proof. 
  intros.
  unfold DGVs.cgv2gvs, NDGVs.cgv2gvs.
  destruct gv; try solve [intros gvs1 J; inv J; constructor].
  destruct p.
  destruct v; try solve [intros gvs1 J; inv J; constructor].
  destruct gv; try solve [intros gvs1 J; inv J; constructor].
  destruct t; simpl;
    try solve [intros gvs1 J; inv J;
               try solve [constructor |
               exists (Int.zero s); auto |
               exists Mem.nullptr; exists (Int.repr 31 0); auto]].
  destruct f; simpl;
    try solve [intros gvs1 J; inv J;
               try solve [constructor |
               exists Float.zero; auto]].
Qed.

Lemma instantiate_gvs__lift_op1 : forall f xs1 xs2 t ys1,
  instantiate_gvs xs1 xs2 ->
  DGVs.lift_op1 f xs1 t = Some ys1 ->
  exists ys2, NDGVs.lift_op1 f xs2 t = Some ys2 /\ instantiate_gvs ys1 ys2.
Proof.
  unfold DGVs.lift_op1, NDGVs.lift_op1.
  intros.
  exists (fun gv2 : GenericValue =>
          exists gv1 : GenericValue,
            exists gv2' : GenericValue,
              NDGVs.instantiate_gvs gv1 xs2 /\
              f gv1 = ret gv2' /\
              NDGVs.instantiate_gvs gv2 (NDGVs.gv2gvs gv2' t)).
  split; auto.
  exists xs1. exists gv1. inv H1.
  repeat (split; eauto using NDGVs.instantiate_gv__gv2gvs).
Qed.

Lemma instantiate_gvs__lift_op2 : forall f xs1 ys1 xs2 ys2 t zxs1,
  instantiate_gvs xs1 xs2 ->
  instantiate_gvs ys1 ys2 ->
  DGVs.lift_op2 f xs1 ys1 t = Some zxs1 ->
  exists zxs2, NDGVs.lift_op2 f xs2 ys2 t = Some zxs2 /\ 
    instantiate_gvs zxs1 zxs2.
Proof.
  unfold DGVs.lift_op2, NDGVs.lift_op2.
  intros.
  exists (fun gv3 : GenericValue =>
          exists gv1 : GenericValue,
            exists gv2 : GenericValue,
              exists gv3' : GenericValue,
                NDGVs.instantiate_gvs gv1 xs2 /\
                NDGVs.instantiate_gvs gv2 ys2 /\
                f gv1 gv2 = ret gv3' /\
                NDGVs.instantiate_gvs gv3 (NDGVs.gv2gvs gv3' t)).
  split; auto.
  exists xs1. exists ys1. exists zxs1. inv H2.
  repeat (split; eauto using NDGVs.instantiate_gv__gv2gvs).
Qed.

Global Opaque NDGVs.instantiate_gvs NDGVs.inhabited NDGVs.cgv2gvs NDGVs.gv2gvs
  NDGVs.lift_op1 NDGVs.lift_op2 NDGVs.t
  DGVs.instantiate_gvs DGVs.inhabited DGVs.cgv2gvs DGVs.gv2gvs
  DGVs.lift_op1 DGVs.lift_op2 DGVs.t.

Fixpoint instantiate_locals (lc1 : DOS.GVsMap) (lc2 : NDOS.GVsMap) : Prop :=
match lc1, lc2 with
| nil, nil => True
| (id1,gvs1)::lc1', (id2,gvs2)::lc2' => 
    id1=id2 /\ instantiate_gvs gvs1 gvs2 /\ instantiate_locals lc1' lc2'
| _, _ => False
end.

Definition instantiate_EC (ec1 : DOS.ExecutionContext) 
  (ec2 : NDOS.ExecutionContext) : Prop :=
match ec1, ec2 with
| DOS.mkEC f1 b1 cs1 tmn1 lc1 als1, NDOS.mkEC f2 b2 cs2 tmn2 lc2 als2 =>
    f1 = f2 /\ b1 = b2 /\ cs1 = cs2 /\ tmn1 = tmn2 /\
    instantiate_locals lc1 lc2 /\ als1 = als2
end.

Fixpoint instantiate_ECs (ecs1 : DOS.ECStack) (ecs2 : NDOS.ECStack) : Prop :=
match ecs1, ecs2 with
| nil, nil => True
| ec1::ecs1', ec2::ecs2' => instantiate_EC ec1 ec2 /\ instantiate_ECs ecs1' ecs2'
| _, _ => False
end.

Definition instantiate_State (st1 : DOS.State) (st2 : NDOS.State) : Prop :=
match st1, st2 with
| DOS.mkState s1 td1 ps1 ecs1 gl1 fs1 M1,
  NDOS.mkState s2 td2 ps2 ecs2 gl2 fs2 M2 =>
    s1 = s2 /\ td1 = td2 /\ ps1 = ps2 /\ instantiate_ECs ecs1 ecs2 /\ gl1 = gl2
    /\ fs1 = fs2 /\ M1 = M2
end.

Lemma instantiate_locals__lookup : forall lc1 lc2 id1 gv1,
  instantiate_locals lc1 lc2 -> 
  lookupAL _ lc1 id1 = Some gv1 ->
  exists gvs2, lookupAL _ lc2 id1 = Some gvs2 /\ instantiate_gvs gv1 gvs2.
Proof.
  induction lc1; destruct lc2; simpl; intros id1 gv1 Hinst Hlk.  
    inv Hlk.
    inv Hinst.
    destruct a. inv Hinst.     

    destruct a. destruct p.
    destruct Hinst as [J1 [J2 J3]]; subst.
    destruct (id1 == i1); subst; eauto.
      inv Hlk. eauto.
Qed.

Lemma same_singleton_set : forall gv,
  Same_set GenericValue (Singleton _ gv) (Singleton _ gv).
Proof.
  unfold Same_set, Included. auto.
Qed.

Lemma instantiate_locals__getOperandValue : forall TD v lc1 lc2 gl gvs1,
  instantiate_locals lc1 lc2 -> 
  DOS.getOperandValue TD v lc1 gl = Some gvs1 ->
  exists gvs2, NDOS.getOperandValue TD v lc2 gl = Some gvs2 /\
    instantiate_gvs gvs1 gvs2.
Proof.
  intros.
  destruct v; simpl in *.
    eapply instantiate_locals__lookup; eauto.

    unfold DOS.const2GV in H0. unfold NDOS.const2GV.
    destruct (_const2GV TD gl c) as [[gv ?]|]; inv H0.
    eauto using instantiate_gvs__cgv2gvs.
Qed.

Lemma instantiate_locals__updateAddAL : forall gvs3 gvs3',
  instantiate_gvs gvs3 gvs3' ->
  forall lc1 lc2 id0,
  instantiate_locals lc1 lc2 -> 
  instantiate_locals (updateAddAL _ lc1 id0 gvs3) (updateAddAL _ lc2 id0 gvs3').
Proof.
  induction lc1; destruct lc2; simpl; intros id0 H1; auto.
    inv H1.  
    destruct a. inv H1.
    destruct a. destruct p. destruct H1 as [eq [H1 H2]]; subst.
    destruct (id0 == i1); subst; simpl.
      split; auto.
      split; auto.
Qed.   

Lemma instantiate_locals__returnUpdateLocals : forall TD lc1 lc2 lc1' lc2' Result
    gl lc1'' c,
  instantiate_locals lc1 lc2 -> 
  instantiate_locals lc1' lc2' -> 
  DOS.returnUpdateLocals TD c Result lc1 lc1' gl = ret lc1'' ->
  exists lc2'', 
    NDOS.returnUpdateLocals TD c Result lc2 lc2' gl = ret lc2'' /\
    instantiate_locals lc1'' lc2''. 
Proof.
  intros.
  unfold DOS.returnUpdateLocals in H1.
  remember (DOS.getOperandValue TD Result lc1 gl) as R.
  destruct R; tinv H1.
  symmetry in HeqR.
  eapply instantiate_locals__getOperandValue in HeqR; eauto.
  destruct HeqR as [gvs2 [J1 J2]].
  unfold NDOS.returnUpdateLocals.
  rewrite J1. 
  destruct c; tinv H1.
  destruct n; inv H1; eauto.
  destruct t; tinv H3.
  remember (DGVs.lift_op1 (fit_gv TD t) g t) as R.
  destruct R as [gr'|]; inv H3.
  symmetry in HeqR.
  eapply instantiate_gvs__lift_op1 in HeqR; eauto.
  destruct HeqR as [ys2 [J3 J4]]. rewrite J3.
  eauto using instantiate_locals__updateAddAL.
Qed.

Lemma instantiate_locals__getIncomingValuesForBlockFromPHINodes : forall TD b
    gl lc1 lc2 (Hlc : instantiate_locals lc1 lc2) ps re1,  
  DOS.getIncomingValuesForBlockFromPHINodes TD ps b gl lc1 = Some re1 ->
  exists re2,
    NDOS.getIncomingValuesForBlockFromPHINodes TD ps b gl lc2 = Some re2 /\
    instantiate_locals re1 re2.
Proof.
  induction ps; simpl; intros.  
    inv H. exists nil. simpl. auto.

    destruct a.
    destruct (getValueViaBlockFromValuels l0 b); tinv H.
    remember (DOS.getOperandValue TD v lc1 gl) as R.
    destruct R; tinv H.
    symmetry in HeqR.  
    eapply instantiate_locals__getOperandValue in HeqR; eauto.
    destruct HeqR as [gvs2 [J1 J2]].
    remember (DOS.getIncomingValuesForBlockFromPHINodes TD ps b gl lc1) as R1.
    destruct R1; inv H.  
    rewrite J1.
    symmetry in HeqR1.
    destruct (@IHps l1) as [re2 [J3 J4]]; auto.
    rewrite J3.
    exists ((i0, gvs2) :: re2). simpl. auto.
Qed.

Lemma instantiate_locals__updateValuesForNewBlock : forall lc1 lc2 re1 re2,
  instantiate_locals lc1 lc2 ->
  instantiate_locals re1 re2 ->
  instantiate_locals (DOS.updateValuesForNewBlock re1 lc1)
     (NDOS.updateValuesForNewBlock re2 lc2).
Proof.
  induction re1; destruct re2; simpl; intros; auto.
    inv H0.
    destruct a. inv H0.
    destruct a. destruct p. destruct H0 as [eq [J1 J2]]; subst.
    apply instantiate_locals__updateAddAL; auto.    
Qed.

Lemma instantiate_locals__switchToNewBasicBlock : forall TD lc1 lc2 gl lc1' b b',
  instantiate_locals lc1 lc2 -> 
  DOS.switchToNewBasicBlock TD b' b gl lc1 = Some lc1' ->
  exists lc2', NDOS.switchToNewBasicBlock TD b' b gl lc2 = Some lc2' /\
    instantiate_locals lc1' lc2'. 
Proof.
  intros.
  unfold DOS.switchToNewBasicBlock in H0.
  unfold NDOS.switchToNewBasicBlock.
  remember (DOS.getIncomingValuesForBlockFromPHINodes TD 
    (getPHINodesFromBlock b') b gl lc1) as R.
  destruct R; inv H0.
  symmetry in HeqR.
  eapply instantiate_locals__getIncomingValuesForBlockFromPHINodes in HeqR; eauto.
  destruct HeqR as [re2 [J1 J2]].
  rewrite J1.
  eauto using instantiate_locals__updateValuesForNewBlock.
Qed.

Lemma instantiate_locals__BOP : forall TD lc1 lc2 gl v1 v2 gvs3 bop sz,
  instantiate_locals lc1 lc2 -> 
  DOS.BOP TD lc1 gl bop sz v1 v2 = Some gvs3 ->
  exists gvs3', NDOS.BOP TD lc2 gl bop sz v1 v2 = Some gvs3' /\
    instantiate_gvs gvs3 gvs3'.
Proof.
  intros.
  apply DOSprop.BOP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold NDOS.BOP.
  rewrite H1. rewrite H3.
  eauto using instantiate_gvs__lift_op2.
Qed.
  
Lemma instantiate_locals__FBOP : forall TD lc1 lc2 gl v1 v2 gv3 fbop fp,
  instantiate_locals lc1 lc2 -> 
  DOS.FBOP TD lc1 gl fbop fp v1 v2 = Some gv3 ->
  exists gvs3', NDOS.FBOP TD lc2 gl fbop fp v1 v2 = Some gvs3' /\
    instantiate_gvs gv3 gvs3'.
Proof.
  intros.
  apply DOSprop.FBOP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold NDOS.FBOP.
  rewrite H1. rewrite H3.
  eauto using instantiate_gvs__lift_op2.
Qed.

Lemma instantiate_locals__ICMP : forall TD lc1 lc2 gl v1 v2 gv3 c t,
  instantiate_locals lc1 lc2 -> 
  DOS.ICMP TD lc1 gl c t v1 v2 = Some gv3 ->
  exists gvs3', NDOS.ICMP TD lc2 gl c t v1 v2 = Some gvs3' /\
    instantiate_gvs gv3 gvs3'.
Proof.
  intros.
  apply DOSprop.ICMP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold NDOS.ICMP.
  rewrite H1. rewrite H3.
  eauto using instantiate_gvs__lift_op2.
Qed.

Lemma instantiate_locals__FCMP : forall TD lc1 lc2 gl v1 v2 gv3 c t,
  instantiate_locals lc1 lc2 -> 
  DOS.FCMP TD lc1 gl c t v1 v2 = Some gv3 ->
  exists gvs3', NDOS.FCMP TD lc2 gl c t v1 v2 = Some gvs3' /\
    instantiate_gvs gv3 gvs3'.
Proof.
  intros.
  apply DOSprop.FCMP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold NDOS.FCMP.
  rewrite H1. rewrite H3.
  eauto using instantiate_gvs__lift_op2.
Qed.

Definition instantiate_list_gvs (l1 : list DGVs.t) (l2 : list NDGVs.t) :=
List.Forall2 instantiate_gvs l1 l2.

Hint Unfold instantiate_list_gvs.

Lemma instantiate_locals__values2GVs : forall TD lc1 lc2 gl idxs vidxs,
  instantiate_locals lc1 lc2 -> 
  DOS.values2GVs TD idxs lc1 gl = Some vidxs ->
  exists vidxss, NDOS.values2GVs TD idxs lc2 gl = Some vidxss /\
    instantiate_list_gvs vidxs vidxss.
Proof.
  induction idxs; simpl; intros.
    inv H0. exists nil. auto.

    remember (DOS.getOperandValue TD v lc1 gl) as R.
    destruct R; tinv H0.
    remember (DOS.values2GVs TD idxs lc1 gl) as R1.
    destruct R1; inv H0.
    symmetry in HeqR.
    eapply instantiate_locals__getOperandValue in HeqR; eauto.
    destruct HeqR as [gvs2 [H3 H4]].
    destruct (@IHidxs l0) as [vidxss [J1 J2]]; auto.
    rewrite H3. rewrite J1. eauto.
Qed.

Lemma in_instantiate_list_gvs : forall vidxss1 vidxss2 vidxs1
  (Hinst1 : instantiate_list_gvs vidxss1 vidxss2)
  (Hin1 : DOS.in_list_gvs vidxs1 vidxss1),
  NDOS.in_list_gvs vidxs1 vidxss2.
Proof.
  intros.
  generalize dependent vidxs1.
  induction Hinst1; intros; inv Hin1; auto.
    eapply IHHinst1 in H4; eauto using instantiate_gvs__incl.
Qed.

Lemma instantiate_locals__GEP : forall TD t mp1 mp1' vidxs1 vidxss1 vidxss2 
    inbounds mps2,
  instantiate_list_gvs vidxss1 vidxss2 ->
  instantiate_gvs mp1 mps2 ->
  DOS.in_list_gvs vidxs1 vidxss1 ->
  DOS.GEP TD t mp1 vidxs1 inbounds = Some mp1' ->
  exists vidxs2, exists mps2', 
    NDOS.in_list_gvs vidxs2 vidxss2 /\
    NDOS.GEP TD t mps2 vidxs2 inbounds = Some mps2' /\ 
    instantiate_gvs mp1' mps2'.
Proof.
  intros TD t mp1 mp1' vidxs1 vidxss1 vidxss2 inbounds mps2 Hinst1 Hinst2 Hin1 
    Hgep.
  inv Hgep.
  unfold NDOS.GEP.
  unfold DOS.GEP in H0.
  eapply instantiate_gvs__lift_op1 in H0; eauto.
  destruct H0 as [ys2 [J1 J2]].
  exists vidxs1.  
  eauto using in_instantiate_list_gvs.
Qed.

Lemma instantiate_locals__extractGenericValue : forall TD lc1 lc2 t gv2
    cidxs gv1 gvs1,
  instantiate_locals lc1 lc2 -> 
  instantiate_gvs gv1 gvs1 ->
  DOS.extractGenericValue TD t gv1 cidxs = Some gv2 ->
  exists gvs2, NDOS.extractGenericValue TD t gvs1 cidxs = Some gvs2 
    /\ instantiate_gvs gv2 gvs2.
Proof.
  intros.
  unfold DOS.extractGenericValue in H1.
  unfold NDOS.extractGenericValue.
  destruct (intConsts2Nats TD cidxs); inv H1.
  destruct (mgetoffset TD t l0) as [[]|]; inv H3.
  eauto using instantiate_gvs__lift_op1.
Qed.

Lemma instantiate_locals__insertGenericValue : forall TD lc1 lc2 t1 t2 gv2 
    cidxs gv1 gvs1 gvs2 gv3,
  instantiate_locals lc1 lc2 -> 
  instantiate_gvs gv1 gvs1 ->
  instantiate_gvs gv2 gvs2 ->
  DOS.insertGenericValue TD t1 gv1 cidxs t2 gv2 = Some gv3 ->
  exists gvs3, NDOS.insertGenericValue TD t1 gvs1 cidxs t2 gvs2 = Some gvs3
    /\ instantiate_gvs gv3 gvs3.
Proof.
  intros.
  unfold DOS.insertGenericValue in H2.
  unfold NDOS.insertGenericValue.
  destruct (intConsts2Nats TD cidxs); inv H2.
  destruct (mgetoffset TD t1 l0) as [[]|]; inv H4.
  eauto using instantiate_gvs__lift_op2.
Qed.

Lemma instantiate_locals__CAST : forall TD lc1 lc2 gl t1 v1 t2 gv2 castop0,
  instantiate_locals lc1 lc2 -> 
  DOS.CAST TD lc1 gl castop0 t1 v1 t2 = Some gv2 ->
  exists gvs2', NDOS.CAST TD lc2 gl castop0 t1 v1 t2 = Some gvs2' 
    /\ instantiate_gvs gv2 gvs2'.
Proof.
  intros.
  apply DOSprop.CAST_inversion in H0.
  destruct H0 as [gv1 [J1 J2]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  unfold NDOS.CAST.
  rewrite H1.
  eauto using instantiate_gvs__lift_op1.
Qed.

Lemma instantiate_locals__TRUNC : forall TD lc1 lc2 gl t1 v1 t2 gv2 top0,
  instantiate_locals lc1 lc2 -> 
  DOS.TRUNC TD lc1 gl top0 t1 v1 t2 = Some gv2 ->
  exists gvs2', NDOS.TRUNC TD lc2 gl top0 t1 v1 t2 = Some gvs2' 
    /\ instantiate_gvs gv2 gvs2'.
Proof.
  intros.
  apply DOSprop.TRUNC_inversion in H0.
  destruct H0 as [gv1 [J1 J2]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  unfold NDOS.TRUNC.
  rewrite H1.
  eauto using instantiate_gvs__lift_op1.
Qed.

Lemma instantiate_locals__EXT : forall TD lc1 lc2 gl t1 v1 t2 gv2 top0,
  instantiate_locals lc1 lc2 -> 
  DOS.EXT TD lc1 gl top0 t1 v1 t2 = Some gv2 ->
  exists gvs2', NDOS.EXT TD lc2 gl top0 t1 v1 t2 = Some gvs2' 
    /\ instantiate_gvs gv2 gvs2'.
Proof.
  intros.
  apply DOSprop.EXT_inversion in H0.
  destruct H0 as [gv1 [J1 J2]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  unfold NDOS.EXT.
  rewrite H1.
  eauto using instantiate_gvs__lift_op1.
Qed.

Lemma instantiate_locals__params2GVs : forall TD lc1 lc2 gl 
  (Hlc:instantiate_locals lc1 lc2) lp gvs1,
  DOS.params2GVs TD lp lc1 gl = Some gvs1 ->
  exists gvss2, NDOS.params2GVs TD lp lc2 gl = Some gvss2 /\
    instantiate_list_gvs gvs1 gvss2.
Proof.
  induction lp; simpl; intros.
    inv H. eauto.

    destruct a.
    remember (DOS.getOperandValue TD v lc1 gl) as R1.
    destruct R1; tinv H.
    remember (DOS.params2GVs TD lp lc1 gl) as R2.
    destruct R2; inv H.
    symmetry in HeqR1.
    eapply instantiate_locals__getOperandValue in HeqR1; eauto.
    destruct HeqR1 as [gvs2 [H3 H4]].
    destruct (@IHlp l0) as [gvsss2 [J1 J2]]; auto.
    rewrite H3. rewrite J1. eauto.
Qed.

Lemma instantiate_locals__initializeFrameValues : forall TD lc1 lc2
  (H2: instantiate_locals lc1 lc2) la gvs1 gvs2 lc1'
  (H1 : instantiate_list_gvs gvs1 gvs2),
  DOS._initializeFrameValues TD la gvs1 lc1 = Some lc1' ->
  exists lc2',
    NDOS._initializeFrameValues TD la gvs2 lc2 = Some lc2' /\
    instantiate_locals lc1' lc2'.
Proof.
  induction la; simpl; intros.
    inv H. eauto.

    destruct a. destruct p.
    destruct gvs1; simpl.
      destruct gvs2; inv H1.
      remember (DOS._initializeFrameValues TD la nil lc1) as R1.
      destruct R1; tinv H.
      destruct (gundef TD t); inv H.
      symmetry in HeqR1.
      eapply IHla in HeqR1; eauto.
        destruct HeqR1 as [lc2' [J1 J2]].
        unfold NDOS.GVs.
        rewrite J1.
        eauto using instantiate_locals__updateAddAL, instantiate_gvs__gv2gvs.

      simpl in H1.
      destruct gvs2; inv H1.
      remember (DOS._initializeFrameValues TD la gvs1 lc1) as R1.
      destruct R1; tinv H.
      remember (DGVs.lift_op1 (fit_gv TD t) t0 t) as R2.
      destruct R2; inv H.
      symmetry in HeqR1.
      eapply IHla in HeqR1; eauto.
      destruct HeqR1 as [lc2' [J1 J2]].
      rewrite J1.
      symmetry in HeqR2.
      eapply instantiate_gvs__lift_op1 in HeqR2; eauto.
      destruct HeqR2 as [ys2 [J3 J4]].
      rewrite J3.
      eauto using instantiate_locals__updateAddAL.
Qed. 

Lemma instantiate_locals__initLocals : forall TD gvs1 gvss2 
  (H : instantiate_list_gvs gvs1 gvss2) la lc1,
  DOS.initLocals TD la gvs1 = Some lc1 ->
  exists lc2, 
    NDOS.initLocals TD la gvss2 = Some lc2 /\
    instantiate_locals lc1 lc2.
Proof.
  unfold DOS.initLocals, NDOS.initLocals.
  intros.
  eapply instantiate_locals__initializeFrameValues; eauto.
    simpl. auto.
Qed.

Lemma instantiate_list_gvs__incl : forall x y x0,
  instantiate_list_gvs x y ->
  DOS.in_list_gvs x0 x ->
  NDOS.in_list_gvs x0 y.
Proof.
  intros.  
  generalize dependent x0.
  induction H; simpl; intros.
    inv H0; auto.
    inv H1; auto.
      apply IHForall2 in H6. eauto using instantiate_gvs__incl.
Qed.

Lemma instantiate_locals__exCallUpdateLocals : forall TD lc1 lc2 lc1' rid oResult
    nr ft,
  instantiate_locals lc1 lc2 -> 
  DOS.exCallUpdateLocals TD ft nr rid oResult lc1 = ret lc1' ->
  exists lc2', 
    NDOS.exCallUpdateLocals TD ft nr rid oResult lc2 = ret lc2' /\
    instantiate_locals lc1' lc2'. 
Proof.
  intros.
  unfold DOS.exCallUpdateLocals in H0.
  unfold NDOS.exCallUpdateLocals.
  destruct nr; inv H0; eauto.
  destruct oResult; inv H2; eauto.
  destruct ft; inv H1; eauto.
  remember (fit_gv TD ft g) as R.
  destruct R; inv H2.
  eauto using instantiate_locals__updateAddAL, instantiate_gvs__gv2gvs.
Qed.

Ltac simpl_nd_llvmds :=
  match goal with
  | [Hsim : instantiate_State {| DOS.ECS := _::_::_ |} ?st2 |- _ ] =>
     destruct st2 as [S' TD' Ps' ECs' gl' fs' M'];
     destruct Hsim as [eq1 [eq2 [eq3 [Hsim [eq4 [eq5 eq6]]]]]]; subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' als1'] ECs']; 
       try solve [inversion Hsim];
     simpl in Hsim; destruct Hsim as [Hsim1 Hsim2];
     destruct ECs' as [|[f2' b2' cs2' tmn2' lc2' als2'] ECs'];
       try solve [inversion Hsim2];
     destruct Hsim2 as [Hsim2 Hsim3];
     destruct Hsim1 as [J1 [J2 [J3 [J4 [Hsim1 J6]]]]]; subst;
     destruct Hsim2 as [J1 [J2 [J3 [J4 [Hsim2 J6]]]]]; subst
  | [Hsim : instantiate_State {| DOS.ECS := _::_|} ?st2 |- _ ] =>
     destruct st2 as [S' TD' Ps' ECs' gl' fs' M'];
     destruct Hsim as [eq1 [eq2 [eq3 [Hsim [eq4 [eq5 eq6]]]]]]; subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' als1'] ECs']; 
       try solve [inversion Hsim];
     simpl in Hsim; destruct Hsim as [Hsim1 Hsim2];
     destruct Hsim1 as [J1 [J2 [J3 [J4 [Hsim1 J6]]]]]; subst
  end.

Lemma instantiate_dsInsn : forall st1 st2 st1' tr,
  instantiate_State st1 st2 ->
  DOS.sInsn st1 st1' tr ->
  (exists st2', NDOS.sInsn st2 st2' tr /\ instantiate_State st1' st2').
Proof.
  intros st1 st2 st1' tr Hsim Hop.  
  (sInsn_cases (induction Hop) Case).
Case "sReturn". simpl_nd_llvmds. 
  eapply instantiate_locals__returnUpdateLocals in H1; eauto.
  destruct H1 as [lc2'' [H1 H2]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f2' b2' cs' tmn2' lc2'' als2')::ECs') gl' fs' Mem').
  split; eauto.
    repeat (split; auto).
Case "sReturnVoid". simpl_nd_llvmds. 
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f2' b2' cs' tmn2' lc2' als2')::ECs') gl' fs' Mem').
  split; eauto.
    repeat (split; auto).
Case "sBranch". simpl_nd_llvmds. 
  eapply instantiate_locals__switchToNewBasicBlock in H2; eauto.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  destruct H2 as [lc2' [J3 J4]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' (block_intro l' ps' cs' tmn') cs' tmn' lc2' als1')
      ::ECs') gl' fs' M').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto).
Case "sBranch_uncond". simpl_nd_llvmds. 
  eapply instantiate_locals__switchToNewBasicBlock in H0; eauto.
  destruct H0 as [lc2' [J1 J2]]. 
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' (block_intro l' ps' cs' tmn') cs' tmn' lc2' als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto).
Case "sBop". simpl_nd_llvmds. 
  eapply instantiate_locals__BOP in H; eauto.
  destruct H as [gvs3' [J1 J2]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sFBop". simpl_nd_llvmds. 
  eapply instantiate_locals__FBOP in H; eauto.
  destruct H as [gvs3' [J1 J2]]. 
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sExtractValue". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  eapply instantiate_locals__extractGenericValue in H0; eauto.
  destruct H0 as [gvs2' [J3 J4]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sInsertValue". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs2' [J1' J2']].
  eapply instantiate_locals__insertGenericValue in H1; eauto.
  destruct H1 as [gvs2'' [J3 J4]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2'') als1')
      ::ECs') gl' fs' M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sMalloc". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gns2 [J1 J2]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' 
      (updateAddAL _ lc1' id0 (NDGVs.gv2gvs (blk2GV TD' mb) (typ_pointer t))) 
    als1')::ECs') gl' fs' Mem').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              instantiate_gvs__gv2gvs).
Case "sFree". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs [J1 J2]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' lc1'
    als1')::ECs') gl' fs' Mem').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto).
Case "sAlloca". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gns2 [J1 J2]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' 
      (updateAddAL _ lc1' id0 (NDGVs.gv2gvs  (blk2GV TD' mb) (typ_pointer t))) 
    (mb::als1'))::ECs') gl' fs' Mem').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              instantiate_gvs__gv2gvs).
Case "sLoad". simpl_nd_llvmds.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 (NDGVs.gv2gvs gv t))
    als1')::ECs') gl' fs' M').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              instantiate_gvs__gv2gvs).
Case "sStore". simpl_nd_llvmds.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [mps2' [J3 J4]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' lc1' als1')::ECs') gl' fs' Mem').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto).
Case "sGEP". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [mps [J1 J2]].
  eapply instantiate_locals__values2GVs in H0; eauto.
  destruct H0 as [vidxss2 [J3 J4]].
  eapply instantiate_locals__GEP in H1; eauto.
  destruct H1 as [vidxs2 [mps2' [J5 [J6 J7]]]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 mps2') als1')
      ::ECs') gl' fs' M').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sTrunc". simpl_nd_llvmds.
  eapply instantiate_locals__TRUNC in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') als1')
      ::ECs') gl' fs' M').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sExt". simpl_nd_llvmds. 
  eapply instantiate_locals__EXT in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') als1')
      ::ECs') gl' fs' M').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sCast". simpl_nd_llvmds. 
  eapply instantiate_locals__CAST in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') als1')
      ::ECs') gl' fs' M').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sIcmp". simpl_nd_llvmds. 
  eapply instantiate_locals__ICMP in H; eauto.
  destruct H as [gvs3' [J1 J2]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') gl' fs' M').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sFcmp". simpl_nd_llvmds. 
  eapply instantiate_locals__FCMP in H; eauto.
  destruct H as [gvs3' [J1 J2]]. 
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') gl' fs' M').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sSelect". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs0' [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs1' [J3 J4]].
  eapply instantiate_locals__getOperandValue in H1; eauto.
  destruct H1 as [gvs2' [J5 J6]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' (if isGVZero TD' c 
                                     then updateAddAL _ lc1' id0 gvs2' 
                                     else updateAddAL _ lc1' id0 gvs1') als1')
      ::ECs') gl' fs' M').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto).
      destruct (isGVZero TD' c); auto using instantiate_locals__updateAddAL.
Case "sCall". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J11 J12]].
  eapply instantiate_locals__params2GVs in H3; eauto.
  destruct H3 as [gvss2 [H11 H12]].
  eapply instantiate_locals__initLocals in H4; eauto.
  destruct H4 as [lc2' [H21 H22]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                       (block_intro l' ps' cs' tmn') cs' tmn' lc2'
                       nil)::
     (NDOS.mkEC f1' b1' (insn_call rid noret0 ca ft fv lp :: cs) tmn1' 
      lc1' als1') ::ECs') gl' fs' M').
  split; eauto using instantiate_gvs__incl.
    repeat (split; auto).
Case "sExCall". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J11 J12]].
  eapply instantiate_locals__params2GVs in H2; eauto.
  destruct H2 as [gvss2 [H11 H12]].
  eapply instantiate_locals__exCallUpdateLocals in H5; eauto.
  destruct H5 as [lc2' [H21 H22]].
  exists (NDOS.mkState S' TD' Ps' 
    ((NDOS.mkEC f1' b1' cs tmn1' lc2' als1') ::ECs') gl' fs' Mem').
  split.
    eapply NDOS.sExCall; eauto using instantiate_gvs__incl,
                                    instantiate_list_gvs__incl.
    repeat (split; auto).
Qed.

End OpsemInstantiation.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
