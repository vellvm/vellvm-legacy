Require Import syntax.
Require Import infrastructure.
Require Import Coq.Program.Equality.
Require Import CoqListFacts.
Require Import Metatheory.
Require Import alist.
Require Import Coqlib.
Require Import Kildall.
Require Import Maps.
Require Import targetdata.
Require Export vellvm_tactics.
Require Import util.

Import LLVMsyntax.
Import LLVMinfra.

(* eq is refl *)

Lemma neq_refl : forall n, n =n= n.
Proof.
  intros.
  symmetry.
  apply beq_nat_refl.
Qed.

Lemma true_sumbool2bool : forall A (H:sumbool A (~A)),
  A -> sumbool2bool A (~A) H = true.
Proof.
  intros A H H0.
  destruct H; auto.
Qed.

Lemma false_sumbool2bool : forall A (H:sumbool A (~A)),
  ~A -> sumbool2bool A (~A) H = false.
Proof.
  intros A H H0.
  destruct H; auto.
    contradict a; auto.
Qed.

Ltac sumbool2bool_refl := intros; apply true_sumbool2bool; auto.

Lemma typEqB_refl : forall t, typEqB t t.
Proof. sumbool2bool_refl. Qed.

Lemma list_typEqB_refl : forall ts, list_typEqB ts ts.
Proof. sumbool2bool_refl. Qed.

Lemma idEqB_refl : forall i, idEqB i i.
Proof. sumbool2bool_refl. Qed.

Lemma lEqB_refl : forall l, lEqB l l.
Proof. sumbool2bool_refl. Qed.

Lemma constEqB_refl : forall c, constEqB c c.
Proof. sumbool2bool_refl. Qed.

Lemma list_constEqB_refl : forall cs, list_constEqB cs cs.
Proof. sumbool2bool_refl. Qed.

Lemma valueEqB_refl: forall v, valueEqB v v.
Proof. sumbool2bool_refl. Qed.

Lemma bopEqB_refl: forall op, bopEqB op op.
Proof. sumbool2bool_refl. Qed.

Lemma extopEqB_refl: forall op, extopEqB op op.
Proof. sumbool2bool_refl. Qed.

Lemma castopEqB_refl: forall op, castopEqB op op.
Proof. sumbool2bool_refl. Qed.

Lemma condEqB_refl: forall c, condEqB c c.
Proof. sumbool2bool_refl. Qed.

Lemma eqb_refl : forall i0, eqb i0 i0.
unfold eqb.
destruct i0; unfold is_true; auto.
Qed.

Lemma list_valueEqB_refl : forall vs, list_valueEqB vs vs.
Proof. sumbool2bool_refl. Qed.

Lemma paramsEqB_refl : forall p, paramsEqB p p.
Proof. sumbool2bool_refl. Qed.

Lemma cmdEqB_refl : forall c, cmdEqB c c.
Proof. sumbool2bool_refl. Qed.

Lemma terminatorEqB_refl : forall tmn, terminatorEqB tmn tmn.
Proof. sumbool2bool_refl. Qed.

Lemma list_value_lEqB_refl : forall l0, list_value_lEqB l0 l0.
Proof. sumbool2bool_refl. Qed.

Lemma phinodeEqB_refl : forall p, phinodeEqB p p.
Proof. sumbool2bool_refl. Qed.

Lemma phinodesEqB_refl : forall ps, phinodesEqB ps ps.
Proof. sumbool2bool_refl. Qed.

Lemma cmdsEqB_refl : forall cs, cmdsEqB cs cs.
Proof. sumbool2bool_refl. Qed.

Lemma blockEqB_refl : forall B,
  blockEqB B B.
Proof. sumbool2bool_refl. Qed.

Lemma blocksEqB_refl : forall bs, blocksEqB bs bs.
Proof. sumbool2bool_refl. Qed.

Lemma argsEqB_refl : forall args0, argsEqB args0 args0.
Proof. sumbool2bool_refl. Qed.

Lemma fheaderEqB_refl : forall f, fheaderEqB f f.
Proof. sumbool2bool_refl. Qed.

Lemma fdecEqB_refl : forall f, fdecEqB f f.
Proof. sumbool2bool_refl. Qed.

Lemma fdefEqB_refl : forall f, fdefEqB f f.
Proof. sumbool2bool_refl. Qed.

Lemma gvarEqB_refl : forall g, gvarEqB g g.
Proof. sumbool2bool_refl. Qed.

Lemma productEqB_refl : forall p,
  productEqB p p.
Proof. sumbool2bool_refl. Qed.

Lemma productsEqB_refl : forall ps,
  productsEqB ps ps.
Proof. sumbool2bool_refl. Qed.

Lemma layoutEqB_refl : forall a, layoutEqB a a.
Proof. sumbool2bool_refl. Qed.

Lemma layoutsEqB_refl : forall la, layoutsEqB la la.
Proof. sumbool2bool_refl. Qed.

Lemma moduleEqB_refl : forall M, moduleEqB M M.
Proof. sumbool2bool_refl. Qed.

Lemma modulesEqB_refl : forall Ms, modulesEqB Ms Ms.
Proof. sumbool2bool_refl. Qed.

Lemma systemEqB_refl : forall S, systemEqB S S.
Proof. sumbool2bool_refl. Qed.

(* refl implies eq *)

Lemma neq_inv : forall n m, n =n= m -> n = m.
Proof.
  intros. apply beq_nat_eq; auto.
Qed.

Ltac sumbool2bool_inv := intros e1 e2 H; apply sumbool2bool_true in H; auto.

Lemma typEqB_inv : forall t1 t2, typEqB t1 t2 -> t1= t2.
Proof. sumbool2bool_inv. Qed.

Lemma list_typEqB_inv : forall ts1 ts2, list_typEqB ts1 ts2 -> ts1=ts2.
Proof. sumbool2bool_inv. Qed.

Lemma idEqB_inv : forall i1 i2, idEqB i1 i2 -> i1 = i2.
Proof. sumbool2bool_inv. Qed.

Lemma lEqB_inv : forall l1 l2, lEqB l1 l2 -> l1 = l2.
Proof. sumbool2bool_inv. Qed.

Lemma constEqB_inv : forall c1 c2, constEqB c1 c2 -> c1 = c2.
Proof. sumbool2bool_inv. Qed.

Lemma list_constEqB_inv : forall cs1 cs2, list_constEqB cs1 cs2 -> cs1 = cs2.
Proof. sumbool2bool_inv. Qed.

Lemma valueEqB_inv: forall v1 v2, valueEqB v1 v2 -> v1 = v2.
Proof. sumbool2bool_inv. Qed.

Lemma bopEqB_inv: forall op1 op2, bopEqB op1 op2 -> op1=op2.
Proof. sumbool2bool_inv. Qed.

Lemma extopEqB_inv: forall op1 op2, extopEqB op1 op2 -> op1=op2.
Proof. sumbool2bool_inv. Qed.

Lemma castopEqB_inv: forall op1 op2, castopEqB op1 op2 -> op1=op2.
Proof. sumbool2bool_inv. Qed.

Lemma condEqB_inv: forall c1 c2, condEqB c1 c2 -> c1=c2.
Proof. sumbool2bool_inv. Qed.

Lemma eqb_inv : forall i1 i2, eqb i1 i2 -> i1=i2.
Proof. destruct i1; destruct i2; auto. Qed.

Lemma list_valueEqB_inv : forall vs1 vs2, list_valueEqB vs1 vs2 -> vs1=vs2.
Proof. sumbool2bool_inv. Qed.

Lemma paramsEqB_inv : forall p1 p2, paramsEqB p1 p2 -> p1=p2.
Proof. sumbool2bool_inv. Qed.

Lemma cmdEqB_inv : forall c1 c2, cmdEqB c1 c2 -> c1 = c2.
Proof. sumbool2bool_inv. Qed.

Lemma terminatorEqB_inv : forall tmn1 tmn2, terminatorEqB tmn1 tmn2 -> tmn1=tmn2.
Proof. sumbool2bool_inv. Qed.

Lemma list_value_lEqB_inv : forall l1 l2, list_value_lEqB l1 l2 -> l1=l2.
Proof. sumbool2bool_inv. Qed.

Lemma phinodeEqB_inv : forall p1 p2, phinodeEqB p1 p2 -> p1=p2.
Proof. sumbool2bool_inv. Qed.

Lemma phinodesEqB_inv : forall ps1 ps2, phinodesEqB ps1 ps2 -> ps1=ps2.
Proof. sumbool2bool_inv. Qed.

Lemma cmdsEqB_inv : forall cs1 cs2, cmdsEqB cs1 cs2 -> cs1=cs2.
Proof. sumbool2bool_inv. Qed.

Lemma blockEqB_inv : forall B1 B2,
  blockEqB B1 B2 -> B1 = B2.
Proof. sumbool2bool_inv. Qed.

Lemma blocksEqB_inv : forall bs1 bs2, blocksEqB bs1 bs2 -> bs1=bs2.
Proof. sumbool2bool_inv. Qed.

Lemma argsEqB_inv : forall as1 as2, argsEqB as1 as2 -> as1=as2.
Proof. sumbool2bool_inv. Qed.

Lemma fheaderEqB_inv : forall f1 f2, fheaderEqB f1 f2 -> f1=f2.
Proof. sumbool2bool_inv. Qed.

Lemma fdecEqB_inv : forall f1 f2, fdecEqB f1 f2 -> f1=f2.
Proof. sumbool2bool_inv. Qed.

Lemma fdefEqB_inv : forall f1 f2, fdefEqB f1 f2 -> f1=f2.
Proof. sumbool2bool_inv. Qed.

Lemma gvarEqB_inv : forall g1 g2, gvarEqB g1 g2 -> g1=g2.
Proof. sumbool2bool_inv. Qed.

Lemma productEqB_inv : forall p1 p2,
  productEqB p1 p2 -> p1 = p2.
Proof. sumbool2bool_inv. Qed.

Lemma productsEqB_inv : forall ps1 ps2, productsEqB ps1 ps2 -> ps1=ps2.
Proof. sumbool2bool_inv. Qed.

Lemma layoutEqB_inv : forall a1 a2, layoutEqB a1 a2 -> a1=a2.
Proof. sumbool2bool_inv. Qed.

Lemma layoutsEqB_inv : forall as1 as2, layoutsEqB as1 as2 -> as1=as2.
Proof. sumbool2bool_inv. Qed.

Lemma moduleEqB_inv : forall M M',
  moduleEqB M M' ->
  M = M'.
Proof. sumbool2bool_inv. Qed.

Lemma modulesEqB_inv : forall Ms Ms',
  modulesEqB Ms Ms' ->
  Ms = Ms'.
Proof. sumbool2bool_inv. Qed.

Lemma systemEqB_inv : forall S S',
  systemEqB S S' ->
  S = S'.
Proof. sumbool2bool_inv. Qed.

Lemma productNEqB_intro : forall p1 p2,
  p1 <> p2 -> productEqB p1 p2 = false.
Proof. 
  intros. apply false_sumbool2bool; auto.
Qed.

(* nth_err *)

Lemma nil_nth_error_Some__False : forall X n (v:X),
  nth_error (@nil X) n = Some v -> False.
Proof.
  induction n; intros; simpl in *; inversion H.
Qed.

Lemma nth_error_cons__inv : forall X b lb n (b':X),
  nth_error (b::lb) n = Some b' ->
  b = b' \/ (exists n', S n' = n /\ nth_error lb n' = Some b').
Proof.
  destruct n; intros; simpl in *.
    inversion H; auto.

    right. exists n. split; auto.
Qed.

Lemma nth_error_cons__inv' : forall X b lb n (b':X),
  nth_error (b::lb) n = Some b' ->
  (n = O /\ b = b') \/ (exists n', S n' = n /\ nth_error lb n' = Some b').
Proof.
  destruct n; intros; simpl in *.
    inversion H; auto.

    right. exists n. split; auto.
Qed.

Lemma blockInFdefB__exists_nth_error : forall lb B fh,
  blockInFdefB B (fdef_intro fh lb) ->
  exists n, nth_error lb n = Some B.
Proof.
  induction lb; intros; simpl in *.
    inversion H.

    apply orb_prop in H.
    destruct H.
      apply blockEqB_inv in H. subst.
      exists O. simpl; auto.

      apply IHlb in H; auto.
      destruct H as [n H].
      exists (S n). simpl. auto.
Qed.

Lemma nth_error__InBlocksB : forall n lb B,
  nth_error lb n = Some B ->
  InBlocksB B lb.
Proof.
  induction n; intros; simpl in *.
    destruct lb; inversion H; subst; simpl.
      apply orb_true_intro.
      left. apply blockEqB_refl.

    destruct lb; inversion H; subst; simpl.
      apply orb_true_intro.
      right. apply IHn; auto.
Qed.

Lemma nth_error__blockInFdef : forall fh lb n B,
  nth_error lb n = Some B ->
  blockInFdefB B (fdef_intro fh lb).
Proof.
  intros.
  eapply nth_error__InBlocksB; eauto.
Qed.

(* NoDup *)

Lemma NotIn_inv : forall X (a:X) (lb1 lb2:list X),
  ~ In a (lb1++lb2) ->
  ~ In a lb1 /\ ~ In a lb2.
Proof.
  intros.
  split; intro J'; apply H; auto using in_or_app.
Qed.

Lemma NoDup_split : forall A (l1 l2:list A),
  NoDup (l1++l2) ->
  NoDup l1 /\ NoDup l2.
Proof.
  induction l1; intros.
    simpl in *.
    split; auto using NoDup_nil.

    inversion H; subst.
    apply IHl1 in H3.
    destruct H3 as [J1 J2].
    split; auto.
      apply NoDup_cons; auto.
        intro J. apply H2. apply in_or_app; auto.
Qed.

Lemma NoDup_last_inv : forall X (a:X) l0,
  NoDup (l0++a::nil) ->
  ~ In a l0.
Proof.
  induction l0; intros.
    intro J. inversion J.

    simpl in H.
    inversion H; subst.
    apply IHl0 in H3.
    intro J.
    simpl in J.
    inversion J; subst; auto.
      apply NotIn_inv in H2.
      destruct H2.
      apply H1; simpl; auto.
Qed.

Lemma NoDup_disjoint : forall l1 l2 (i0:atom),
  NoDup (l1++l2) ->
  In i0 l2 ->
  ~ In i0 l1.
Proof.
  induction l1; intros.
    intro J. inversion J.

    simpl. simpl_env in H.
    inv H.
    eapply IHl1 in H4; eauto.
    destruct (eq_atom_dec i0 a); subst.
      intro J. apply H3. apply in_or_app; auto.
      intro J. destruct J; auto.
Qed.

Lemma NoDup_disjoint' : forall l1 l2 (i0:atom),
  NoDup (l1++l2) ->
  In i0 l1 ->
  ~ In i0 l2.
Proof.
  induction l1; intros.
    inversion H0.

    simpl. simpl_env in H.
    inv H. simpl in H0.
    destruct H0 as [H0 | H0]; subst; eauto.
      intro J. apply H3. apply in_or_app; auto.
Qed.

Hint Constructors NoDup.

Lemma In_weakening : forall A (l2 l3 l1:list A) a,
  In a (l1 ++ l3) -> In a (l1 ++ l2 ++ l3).
Proof.
  induction l1; simpl; intros.
    apply in_or_app; auto.
    destruct H as [H | H]; auto.
Qed.

Ltac split_NoDup :=
repeat match goal with
| Huniq: NoDup (_++_) |- _ =>
  let H1:=fresh "Huniq" in
  let H2:=fresh "Huniq" in
  apply NoDup_split in Huniq;
  destruct Huniq as [H1 H2]
end.

Lemma NoDup_strenthening : forall A (l2 l3 l1:list A),
  NoDup (l1 ++ l2 ++ l3) -> NoDup (l1 ++ l3).
Proof.
  induction l1; simpl; intros.
    apply NoDup_split in H. destruct H; auto.

    inv H. apply NoDup_cons; auto using In_weakening.
Qed.

Lemma NoDup_split': forall A (l1 l2:list A),
  NoDup (l1++l2) ->
  NoDup l1 /\ NoDup l2 /\ (forall (a:A), In a l1 -> ~ In a l2).
Proof.
  induction l1; simpl; intros; auto.
    inv H.
    apply IHl1 in H3. destruct H3 as [J1 [J2 J3]].
    split.
      constructor; auto.
        intro J. apply H2. apply in_or_app; auto.
    split; auto.
      intros.
      destruct H as [H | H]; subst; auto.
        intro J. apply H2. apply in_or_app; auto.
Qed.

Lemma NoDup_insert: forall A (l1 l2:list A) a,
  NoDup (l1++l2) ->
  ~ In a (l1 ++ l2) ->
  NoDup (l1++a::l2).
Proof.
  induction l1; simpl; intros.
    constructor; auto.

    inv H.
    apply IHl1 with (a:=a0) in H4; auto.
    constructor; auto.
      intro J. apply H3.
      apply in_app_or in J.
      apply in_or_app.
      destruct J as [J | J]; auto.
      simpl in J.
      destruct J as [J | J]; auto.
      subst. contradict H0; auto.
Qed.

Lemma NoDup_commut: forall A (l1 l2:list A),
  NoDup (l1++l2) -> NoDup (l2++l1).
Proof.
  induction l1; simpl; intros.
    simpl_env. auto.

    inv H.
    apply NoDup_insert; auto.
    intro J. apply in_app_or in J.
    apply H2. apply in_or_app.
    destruct J as [J | J]; auto.
Qed.

Lemma NoDup_rev: forall A (l1:list A) (Huniq: NoDup l1), NoDup (rev l1).
Proof.
  induction 1; simpl; auto.
    apply NoDup_commut. simpl.
    constructor; auto.
      intro J. apply H. apply in_rev; auto.
Qed.

Lemma NoDup_app: forall A (l1 l2:list A),
  NoDup l1 -> NoDup l2 ->
  (forall (a:A), In a l1 -> ~ In a l2) ->
  NoDup (l1++l2).
Proof.
  induction l1; simpl; intros; auto.
    inv H.
    constructor; auto.
      intro J. apply in_app_or in J.
      destruct J as [J | J]; auto.
      assert (a = a \/ In a l1) as Hin. auto.
      apply H1 in Hin. auto.
Qed.

(* gets *)

Lemma getProductsIDs_app : forall ps1 ps2,
  getProductsIDs (ps1++ps2) = getProductsIDs ps1++getProductsIDs ps2.
Proof.
  induction ps1; intros; auto.
    simpl. 
    rewrite IHps1. auto.
Qed.

Lemma getCmdsLocs_app : forall cs1 cs2,
  getCmdsLocs (cs1++cs2) = getCmdsLocs cs1++getCmdsLocs cs2.
Proof.
  induction cs1; intros; auto.
    simpl. rewrite IHcs1. auto.
Qed.

Lemma getCmdsIDs_app : forall cs1 cs2,
  getCmdsIDs (cs1++cs2) = getCmdsIDs cs1++getCmdsIDs cs2.
Proof.
  induction cs1; intros; auto.
    simpl.
    rewrite IHcs1.
    destruct (getCmdID a); auto.
Qed.

Lemma getPhiNodesIDs_app : forall ps1 ps2,
  getPhiNodesIDs (ps1++ps2) = getPhiNodesIDs ps1++getPhiNodesIDs ps2.
Proof.
  induction ps1; intros; auto.
    simpl.
    rewrite IHps1; auto.
Qed.

Lemma getBlocksLocs_app : forall lb1 lb2,
  getBlocksLocs (lb1++lb2) = getBlocksLocs lb1++getBlocksLocs lb2.
Proof.
  induction lb1; intros; auto.
    simpl. rewrite IHlb1. simpl_env. auto.
Qed.

Lemma getArgsIDs_app : forall l1 l2,
  getArgsIDs (l1++l2) = getArgsIDs l1 ++ getArgsIDs l2.
Proof.
  induction l1; simpl; intros; auto.
    destruct a. simpl. rewrite IHl1; auto.
Qed.

(* inclusion *)

Lemma InBlocksB_middle : forall lb1 B lb2,
  InBlocksB B (lb1++B::lb2).
Proof.
  induction lb1; intros; simpl; auto.
    apply orb_true_intro.
    left. apply blockEqB_refl.

    apply orb_true_intro.
    right. apply IHlb1.
Qed.

Lemma uniqBlocks__uniqLabel2Block : forall lb (H: uniqBlocks lb),
  uniq lb.
Proof.
  intros. destruct H; auto.
Qed.

Lemma uniqBlocks_nil : uniqBlocks nil.
Proof.
  unfold uniqBlocks. 
  simpl. split. constructor. auto using NoDup_nil. 
Qed.

Lemma uniqBlocks_inv : forall lb1 lb2 (H: uniqBlocks (lb1++lb2)),
  uniqBlocks lb1 /\ uniqBlocks lb2.
Proof.
  unfold uniqBlocks. 
  intros.
  destruct H as [H1 H2].
  rewrite getBlocksLocs_app in H2.
  apply NoDup_split in H2.
  apply uniq_app_iff in H1.
  tauto.
Qed.

Lemma nth_error__lookupAL_blocks : forall n lb1 B1
  (H: uniqBlocks lb1) (H0: nth_error lb1 n = Some B1),
  exists l0,  lookupAL _ lb1 l0 = Some (snd B1).
Proof.
  induction n as [|n]; simpl; 
    intros; destruct lb1 as [|[l0 s0] lb1]; inv H0.
    exists l0.  simpl.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l0); 
      try congruence.

    simpl_env in H.
    assert (J:=H).
    apply uniqBlocks_inv in J. destruct J.
    apply IHn in H2; auto.
    destruct H2 as [l2 H2].
    exists l2.
    simpl.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l2 l0); 
      subst; auto.   
      apply lookupAL_Some_indom in H2.
      destruct H. inv H. fsetdec.
Qed.

Lemma nth_error_uniqBlocks__indom : forall n lb B
  (H: uniqBlocks lb)
  (H0: nth_error lb n = Some B),
  (getBlockLabel B) `in` dom lb.
Proof.
  induction n; intros.
    destruct lb; inversion H0; subst.
    destruct B. simpl. fsetdec.

    destruct lb as [|[] ?]; try solve [inversion H0].
    simpl in *.
    simpl_env in H.
    apply uniqBlocks_inv in H.
    destruct H.
    apply IHn in H0; auto.
Qed.

Lemma uniqBlocks__uniq_nth_error : forall n lb1 n' B1,
  uniqBlocks lb1 ->
  nth_error lb1 n = Some B1 ->
  nth_error lb1 n' = Some B1 ->
  n = n'.
Proof.
  induction n; intros.
    destruct n'; auto.
      simpl in *.
      destruct lb1; inversion H0; subst.
      assert (J:=H).
      simpl_env in J. apply uniqBlocks_inv in J. destruct J.
      apply nth_error_uniqBlocks__indom in H1; auto.
      destruct H. simpl in H. destruct B1. inversion H; subst.
      simpl in H1. fsetdec.

    destruct n'; auto.
      simpl in *.
      destruct lb1; inversion H1; subst.
      assert (J:=H).
      simpl_env in J. apply uniqBlocks_inv in J. destruct J.
      apply nth_error_uniqBlocks__indom in H0; auto.
      destruct H. simpl in H. destruct B1. inversion H; subst.
      simpl in H0. fsetdec.

      simpl in *.
      destruct lb1; inversion H0.
      simpl_env in H. apply uniqBlocks_inv in H. destruct H.
      apply IHn with (n':=n')(B1:=B1) in H0; auto.
Qed.

Ltac solve_refl :=
match goal with
| |- ?c =cmd= ?c = true => apply cmdEqB_refl
| |- ?p =phi= ?p = true => apply phinodeEqB_refl
| |- moduleEqB ?m ?m = true => apply moduleEqB_refl
| |- ?t =tmn= ?t = true => apply terminatorEqB_refl
| |- ?b =b= ?b = true => apply blockEqB_refl
| |- (?l0, ?s0) =b= (?l0, ?s0) = true => apply blockEqB_refl
| |- productEqB ?p ?p = true => apply productEqB_refl
end.

Lemma In_InBlocksB: forall b bs, In b bs -> InBlocksB b bs = true.
Proof.
  induction bs; intros.
    tauto.

    simpl.
    apply orb_true_intro.
    destruct_in H; auto.
      left. solve_refl.
Qed.

Lemma lookupBlock_blocks_inv : forall lb f l0 stmts0
  (H2: lookupAL _ lb l0 = Some stmts0),
  blockInFdefB (l0, stmts0) (fdef_intro f lb).
Proof.
  intros.
  simpl.
  apply lookupAL_in in H2; auto.
  apply In_InBlocksB; auto.
Qed.

Lemma lookupBlockViaLabelFromFdef_inv : forall F l0 stmts0
  (H2: lookupBlockViaLabelFromFdef F l0 = Some stmts0),
  blockInFdefB (l0, stmts0) F.
Proof.
  intros.
  destruct F as [[] bs]. 
  apply lookupBlock_blocks_inv; auto.
Qed.

Lemma lookupFdefViaIDFromProducts_inv : forall Ps fid F,
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  InProductsB (product_fdef F) Ps.
Proof.
  induction Ps; intros.
    simpl in H. inversion H.

    simpl in *.
    unfold lookupFdefViaIDFromProduct in H.
    apply orb_true_intro.
    destruct a as [g|f|f];
      try solve [apply IHPs in H; auto].
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdefID f) fid); subst.
        inversion H; subst.
        left. apply productEqB_refl.

        apply IHPs in H. auto.
Qed.

Lemma lookupFdecViaIDFromProducts_inv : forall Ps fid F,
  lookupFdecViaIDFromProducts Ps fid = Some F ->
  InProductsB (product_fdec F) Ps.
Proof.
  induction Ps; intros.
    simpl in H. inversion H.

    simpl in *.
    unfold lookupFdecViaIDFromProduct in H.
    apply orb_true_intro.
    destruct a as [g|f|f];
      try solve [apply IHPs in H; auto].
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdecID f) fid); subst.
        inversion H; subst.
        left. apply productEqB_refl.

        apply IHPs in H. auto.
Qed.

Lemma lookupBlockViaLabelFromFdef__blockInFdefB :
  forall (f : fdef) (l0 : l) stmts0,
    lookupBlockViaLabelFromFdef f l0 = Some stmts0 ->
    blockInFdefB (l0, stmts0) f.
Proof.
  destruct f. intros.
  apply lookupBlock_blocks_inv; auto.
Qed.

Lemma entryBlockInFdef : forall F B,
  getEntryBlock F = Some B ->
  blockInFdefB B F.
Proof.
  intros.
  unfold getEntryBlock in H.
  destruct F as [f b].
  destruct b; inversion H; subst.
    simpl.
    apply orb_true_intro.
    left. apply blockEqB_refl.
Qed.

Lemma blockInSystemModuleFdef_inv : forall B F Ps los nts S,
  blockInSystemModuleFdef B S (module_intro los nts Ps) F ->
  blockInFdefB B F /\
  InProductsB (product_fdef F) Ps /\
  moduleInSystem (module_intro los nts Ps) S /\
  productInSystemModuleB (product_fdef F) S (module_intro los nts Ps).
Proof.
  intros.
  unfold blockInSystemModuleFdef in H.
  unfold blockInSystemModuleFdefB in H.
  unfold productInSystemModuleB in *.
  unfold productInModuleB in *.
  apply andb_true_iff in H. destruct H.
  split; auto.
  apply andb_true_iff in H0. destruct H0.
  split; auto.
  split; auto.
  eapply andb_true_iff.
  split; auto.
Qed.

Lemma blockInSystemModuleFdef_intro : forall B F Ps los nts S,
  blockInFdefB B F ->
  InProductsB (product_fdef F) Ps ->
  moduleInSystem (module_intro los nts Ps) S ->
  blockInSystemModuleFdef B S (module_intro los nts Ps) F.
Proof.
  intros.
  unfold blockInSystemModuleFdef.
  unfold blockInSystemModuleFdefB.
  unfold productInSystemModuleB.
  unfold productInModuleB.
  eapply andb_true_iff.
  split; auto.
  eapply andb_true_iff.
  split; auto.
Qed.

Lemma InBlocksB__In: forall b bs, InBlocksB b bs = true -> In b bs.
Proof.
  induction bs; simpl; intros.
    congruence.

    binvt H as H1 H2; auto.
      apply blockEqB_inv in H1. auto.
Qed.

Lemma NotIn_NotInBlocksB : forall lb l0 stmt0 (H: l0 `notin` (dom lb)),
  ~ InBlocksB (l0, stmt0) lb.
Proof.
  intros.
  intros Hin.
  apply InBlocksB__In in Hin.
  apply In_InDom in Hin. congruence.
Qed.

Lemma InBlocksB_In : forall lb l0 stmts0 (H: InBlocksB (l0, stmts0) lb),
  l0 `in` (dom lb).
Proof.
  intros.
  destruct (AtomSetProperties.In_dec l0 (dom lb)) as [J1 | J1]; auto.
    contradict H.
    eapply NotIn_NotInBlocksB; eauto.
Qed.

Lemma InBlocksB__NotIn : forall l2 bs l0 stmts0,
  InBlocksB (l0, stmts0) bs = true ->
  l2 `notin` (dom bs) ->
  l0 <> l2.
Proof.
  intros l2 bs l0 stmts0 HbInF H1.
  apply InBlocksB_In in HbInF.
  destruct (eq_dec l0 l2); subst; auto.
Qed.

Lemma InBlocksB__lookupAL : forall bs l3 stmts3
  (Huniq : uniqBlocks bs)
  (HBinF : InBlocksB (l3, stmts3) bs = true)
  stmts1 (J9 : lookupAL _ bs l3 = Some stmts1),
  stmts1 = stmts3.
Proof.
  intros.
  destruct Huniq as [Huniq _].
  apply InBlocksB__In in HBinF.
  apply In_lookupAL in HBinF; auto.
  congruence.
Qed.

Lemma entryBlockInSystemBlockFdef : forall los nts Ps S fid F B,
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  getEntryBlock F = Some B ->
  blockInSystemModuleFdef B S (module_intro los nts Ps) F.
Proof.
  intros.
  apply lookupFdefViaIDFromProducts_inv in H0.
  apply entryBlockInFdef in H1.
  apply blockInSystemModuleFdef_intro; auto.
Qed.

Lemma productInSystemModuleB_inv : forall P Ps nts los S,
  productInSystemModuleB P S (module_intro los nts Ps) ->
  InProductsB P Ps /\
  moduleInSystem (module_intro los nts Ps) S.
Proof.
  intros.
  unfold productInSystemModuleB in *.
  unfold productInModuleB in *.
  apply andb_true_iff in H. destruct H.
  split; auto.
Qed.

Lemma productInSystemModuleB_intro : forall P Ps nts los S,
  InProductsB P Ps ->
  moduleInSystem (module_intro los nts Ps) S ->
  productInSystemModuleB P S (module_intro los nts Ps).
Proof.
  intros.
  unfold productInSystemModuleB.
  unfold productInModuleB.
  eapply andb_true_iff.
  split; auto.
Qed.

Lemma lookupFdefViaIDFromProductsInSystem : forall los nts Ps S fid F,
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  productInSystemModuleB (product_fdef F) S (module_intro los nts Ps).
Proof.
  intros.
  apply lookupFdefViaIDFromProducts_inv in H0.
  apply productInSystemModuleB_intro; auto.
Qed.

Lemma InBlocksB_uniq : forall lb l1 stmts1 stmts2
  (Huniq: uniqBlocks lb) (Hin1: InBlocksB (l1, stmts1) lb)
  (Hin2: InBlocksB (l1, stmts2) lb),
  stmts1 = stmts2.
Proof.
  intros.
  destruct Huniq as [Huniq _].
  apply InBlocksB__In in Hin1.
  apply InBlocksB__In in Hin2.
  apply In_lookupAL in Hin1; auto.
  apply In_lookupAL in Hin2; auto.
  congruence.
Qed.

Lemma blockInFdefB_uniq : forall l1 stmts1 stmts2 F (H: uniqFdef F),
  blockInFdefB (l1, stmts1) F ->
  blockInFdefB (l1, stmts2) F ->
  stmts1 = stmts2.
Proof.
  intros.
  unfold blockInFdefB in *.
  destruct F as [f b]. destruct f. destruct H.
  eapply InBlocksB_uniq; eauto.
Qed.

Lemma blockInSystemModuleFdef_uniq : forall l1 stmts1 stmts2 S M F
  (H: uniqFdef F) (H0: blockInSystemModuleFdef (l1, stmts1) S M F)
  (H1: blockInSystemModuleFdef (l1, stmts2) S M F),
  stmts1 = stmts2.
Proof.
  intros.
  unfold blockInSystemModuleFdef in *.
  unfold blockInSystemModuleFdefB in *.
  apply andb_true_iff in H0.
  apply andb_true_iff in H1.
  destruct H0.
  destruct H1.
  eapply blockInFdefB_uniq; eauto.
Qed.

Lemma blockInFdefB__In : forall lb b fh (H: blockInFdefB b (fdef_intro fh lb)),
  In b lb.
Proof.
  simpl. intros. apply InBlocksB__In; auto.
Qed.

Lemma In__blockInFdef : forall fh lb b (H: In b lb),
  blockInFdefB b (fdef_intro fh lb).
Proof.
  intros.
  eapply In_InBlocksB; eauto.
Qed.

Lemma productInSystemModuleB_nth_error__blockInSystemModuleFdef : 
  forall fh lb S los nts Ps b,
  productInSystemModuleB (product_fdef (fdef_intro fh lb)) S 
    (module_intro los nts Ps) ->
  In b lb ->
  blockInSystemModuleFdef b S (module_intro los nts Ps) (fdef_intro fh lb).
Proof.
  intros.
  apply productInSystemModuleB_inv in H.
  destruct H.
  apply blockInSystemModuleFdef_intro; auto.
  unfold blockInFdefB.
  eapply In_InBlocksB; eauto.
Qed.

(* uniqueness *)
Lemma uniqProducts__uniqFdec : forall Ps F,
  uniqProducts Ps ->
  InProductsB (product_fdec F) Ps ->
  uniqFdec F.
Proof.
  induction Ps as [|P Ps]; intros F Huniq Hin. discriminate.

    simpl in *.
    inversion Huniq. subst.
    apply orb_prop in Hin.
    destruct Hin.
      apply productEqB_inv in H. subst. trivial.
      apply IHPs; trivial.

Qed.

Lemma uniqProducts__uniqFdef : forall Ps F,
  uniqProducts Ps ->
  InProductsB (product_fdef F) Ps ->
  uniqFdef F.
Proof.
  induction Ps as [|P Ps]; intros F Huniq Hin. inversion Hin.

  inversion Huniq as [|P' Ps' HuniqP HuniqPs]. clear Huniq. subst.
  apply orb_prop in Hin. destruct Hin as [Hin | Hin]; eauto.
  apply productEqB_inv in Hin. subst. auto.
Qed.

Lemma uniqSystem__uniqFdef : forall S F M,
  uniqSystem S ->
  productInSystemModuleB (product_fdef F) S M ->
  uniqFdef F.
Proof.
  induction S; intros.
    unfold productInSystemModuleB in H0.
    apply andb_true_iff in H0.
    destruct H0.
    unfold moduleInSystemB in H0.
    inversion H0.

    unfold productInSystemModuleB in H0.
    apply andb_true_iff in H0.
    destruct H0.
    unfold moduleInSystemB in H0.
    inversion H0. clear H0.
    apply orb_prop in H3.
    simpl in H.
    destruct H as [J1 J2].
    destruct H3 as [H3 | H3].
      apply moduleEqB_inv in H3. subst.
      destruct a.
      simpl in H1. simpl in J1. destruct J1.
      eapply uniqProducts__uniqFdef; eauto.

      apply IHS with (M:=M); auto.
        unfold productInSystemModuleB.
        eapply andb_true_iff; auto.
Qed.

Lemma uniqSystem__uniqFdec : forall S F M,
  uniqSystem S ->
  productInSystemModuleB (product_fdec F) S M ->
  uniqFdec F.
Proof.
  induction S; intros.
    unfold productInSystemModuleB in H0.
    apply andb_true_iff in H0.
    destruct H0.
    unfold moduleInSystemB in H0.
    inversion H0.

    unfold productInSystemModuleB in H0.
    apply andb_true_iff in H0.
    destruct H0.
    unfold moduleInSystemB in H0.
    inversion H0. clear H0.
    apply orb_prop in H3.
    simpl in H.
    destruct H as [J1 J2].
    destruct H3 as [H3 | H3].
      apply moduleEqB_inv in H3. subst.
      destruct a.
      simpl in H1. simpl in J1. destruct J1.
      eapply uniqProducts__uniqFdec; eauto.

      apply IHS with (M:=M); auto.
        unfold productInSystemModuleB.
        eapply andb_true_iff; auto.
Qed.

Lemma uniqSystem__uniqProducts : forall S los nts Ps,
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  uniqProducts Ps.
Proof.
  induction S; intros.
    inversion H0.

    simpl in *.
    destruct H.
    destruct a.
    unfold moduleInSystem in H0.
    unfold moduleInSystemB in H0.
    inversion H0.
    apply orb_prop in H3.
    destruct H3; eauto.
      apply sumbool2bool_true in H2.
      inversion H2;  subst.
      inversion H; auto.
Qed.

Lemma lookupFdefViaIDFromProducts_uniq : forall los nts Ps S fid F,
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  uniqFdef F.
Proof.
  intros.
  apply lookupFdefViaIDFromProducts_inv in H1.
  apply uniqSystem__uniqProducts in H0; auto.
  eapply uniqProducts__uniqFdef; simpl; eauto.
Qed.

Lemma lookupFdecViaIDFromProducts_uniq : forall los nts Ps S fid F,
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdecViaIDFromProducts Ps fid = Some F ->
  uniqFdec F.
Proof.
  intros.
  apply lookupFdecViaIDFromProducts_inv in H1.
  apply uniqSystem__uniqProducts in H0; auto.
  eapply uniqProducts__uniqFdec; simpl; eauto.
Qed.

Lemma InBlocksB__lookupAL_blocks : forall lb1 l' stmts'
  (H: uniqBlocks lb1) (H0: InBlocksB (l', stmts') lb1),
  lookupAL _ lb1 l' = Some stmts'.
Proof.
  intros.
  destruct H as [H _].
  apply InBlocksB__In in H0.
  apply In_lookupAL; auto.
Qed.

Lemma In__lookupAL_blocks : forall lb1 l0 stmts0
  (H: uniqBlocks lb1) (H0: In (l0, stmts0) lb1),
  lookupAL _ lb1 l0 = Some stmts0.
Proof.
  intros.
  destruct H as [H _].
  apply In_lookupAL; auto.
Qed.

Lemma In_uniqBlocks__indom : forall lb b,
  In b lb ->
  (getBlockLabel b) `in` dom lb.
Proof.
  intros. destruct b.
  apply In_InDom in H; auto.
Qed.

Lemma NoDup__InBlocksB : forall bs b,
  NoDup (getBlocksLocs bs) ->
  InBlocksB b bs = true ->
  NoDup (getStmtsLocs (snd b)).
Proof.
  induction bs; simpl; intros.
    inversion H0.

    apply NoDup_split in H. destruct H.
    apply orb_prop in H0.
    destruct H0 as [H0 | H0]; eauto.
      apply blockEqB_inv in H0. subst. auto.
Qed.

Lemma uniqBlocks__uniqBlock : forall lb l1 ps1 cs1 tmn1
  (H: uniqBlocks lb) (H0: In (l1, stmts_intro ps1 cs1 tmn1) lb),
  NoDup (getCmdsLocs cs1).
Proof.
  intros.
  apply In_InBlocksB in H0.
  destruct H as [_ H].
  apply NoDup__InBlocksB in H0; auto.
  simpl in H0.
  split_NoDup; auto.
Qed.

Lemma uniqFdef__uniqBlock : forall fh lb l1 ps1 cs1 tmn1
  (H: uniqFdef (fdef_intro fh lb))
  (H0: In (l1, stmts_intro ps1 cs1 tmn1) lb),
  NoDup (getCmdsLocs cs1).
Proof.
  intros.
  unfold uniqFdef in H. destruct fh. destruct H.
  eapply uniqBlocks__uniqBlock; eauto.
Qed.

Lemma uniqFdef__uniqBlock' : forall fh lb n l1 ps1 cs1 tmn1,
  uniqFdef (fdef_intro fh lb) ->
  nth_error lb n = Some (l1, stmts_intro ps1 cs1 tmn1) ->
  NoDup (getCmdsLocs cs1).
Proof.
  destruct fh.
  simpl. intros. destruct H.
  apply nth_error__InBlocksB in H0.  
  apply InBlocksB__In in H0.
  eapply uniqBlocks__uniqBlock; eauto.
Qed.

Lemma lookupFdefViaIDFromProducts_ideq : forall Ps fid fa rt la va lb fid',
  lookupFdefViaIDFromProducts Ps fid =
    Some (fdef_intro (fheader_intro fa rt fid' la va) lb) ->
  fid = fid'.
Proof.
  induction Ps; intros.
    inversion H.

    simpl in H.
    destruct a as [g|f|f]; simpl in H; eauto 2.
      destruct f as [f b]. destruct f as [f0 t0 i0 a0 v0].
      simpl in H.
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) i0 fid);
        simpl in H; subst; eauto 2.
        inversion H; auto.
Qed.

Lemma lookupFdecViaIDFromProducts_ideq : forall Ps fid fa rt la va fid' dck,
  lookupFdecViaIDFromProducts Ps fid =
    Some (fdec_intro (fheader_intro fa rt fid' la va) dck) ->
  fid = fid'.
Proof.
  induction Ps; intros.
    inversion H.

    simpl in H.
    destruct a as [g|f|f]; simpl in H; eauto 2.
      destruct f as [f b]. destruct f as [f0 t0 i0 a0 v0].
      simpl in H.
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) i0 fid);
        simpl in H; subst; eauto 2.
        inversion H; auto.
Qed.

Lemma getValueViaLabelFromValuels__nth_list_value_l : forall
  (l1 : l)  v vls
  (J : getValueViaLabelFromValuels vls l1 = Some v),
  exists n, nth_error vls n = Some (v, l1).
Proof.
  intros.
  induction vls; intros; simpl in *.
    inversion J.

    destruct a as [v0 l0]; destruct (l0 == l1); subst.
      inversion J; subst; simpl in *.
      exists 0%nat. auto.

      destruct IHvls as [n' IHvls]; auto.
      exists (S n'). simpl. auto.
Qed.

Lemma InPhiNodes_lookupTypViaIDFromPhiNodes : forall ps id1,
  In id1 (getPhiNodesIDs ps) ->
  exists t, lookupTypViaIDFromPhiNodes ps id1 = Some t.
Proof.
  induction ps; intros; simpl in *.
    inversion H.

    destruct H as [H | H]; subst.
      destruct a as [i0 t].
      simpl. unfold lookupTypViaIDFromPhiNode. simpl.
      destruct (i0==i0); subst.
        exists t. auto.
        contradict n; auto.

      apply IHps in H.
      destruct H as [t H].
      rewrite H.
      destruct (lookupTypViaIDFromPhiNode a id1).
        exists t0. auto.
        exists t. auto.
Qed.

Lemma InPhiNodes_lookupTypViaIDFromFdef : forall f id1 l' ps cs tmn,
  Some (stmts_intro ps cs tmn) = lookupBlockViaLabelFromFdef f l' ->
  In id1 (getPhiNodesIDs ps) ->
  exists t, lookupTypViaIDFromFdef f id1 = Some t.
Proof.
  intros.
  destruct f as [f b]. destruct f as [fnattrs5 typ5 id5 args5 varg5].
  simpl in *.
  destruct (lookupTypViaIDFromArgs args5 id1) as [t0|].
    exists t0. auto.

    induction b as [|a0 b]; simpl in *.
      inversion H.

      destruct a0 as [l0 [ps0 cs0 tmn0]]; simpl in *.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l' l0); subst.
        inversion H; subst.
        apply InPhiNodes_lookupTypViaIDFromPhiNodes in H0.
        destruct H0 as [t1 H0].
        rewrite H0. exists t1. auto.

        apply IHb in H.
        destruct H as [t1 H].
        rewrite H.
        destruct (lookupTypViaIDFromPhiNodes ps0 id1) as [t2|].
          exists t2. auto.
          destruct (lookupTypViaIDFromCmds cs0 id1) as [t2|].
            exists t2. auto.
            destruct (lookupTypViaIDFromTerminator tmn0 id1) as [t2|].
              exists t2. auto.
              exists t1. auto.
Qed.

Lemma InArgsIDs_lookupTypViaIDFromArgs : forall la id1,
  In id1 (getArgsIDs la) ->
  exists t, lookupTypViaIDFromArgs la id1 = Some t.
Proof.
  induction la; intros; simpl in *.
    inversion H.

    destruct a. destruct p.
    simpl in H.
    destruct H as [H | H]; subst.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 id1); subst.
        exists t. auto.
        contradict n; auto.

      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst.
        exists t. auto.
        eauto.
Qed.

Lemma InArgsIDs_lookupTypViaIDFromFdef : forall id1 t0 fa id0 la0 va0 bs,
  In id1 (getArgsIDs la0) ->
  exists t,
  lookupTypViaIDFromFdef (fdef_intro (fheader_intro fa t0 id0 la0 va0) bs) id1 =
    Some t.
Proof.
  intros.
  simpl in *.
  apply InArgsIDs_lookupTypViaIDFromArgs in H.
  destruct H as [t H].
  rewrite H.
  exists t.
  auto.
Qed.

Lemma blockInFdefB_lookupBlockViaLabelFromFdef : forall F l' stmts',
  uniqFdef F ->
  blockInFdefB (l', stmts') F ->
  lookupBlockViaLabelFromFdef F l' = Some stmts'.
Proof.
  intros. destruct F as [f b].
  destruct f as [fnattrs5 typ5 id5 args5 varg5]. destruct H. simpl in *.
  apply InBlocksB__lookupAL_blocks; auto.
Qed.

Lemma lookupBlockViaIDFromFdef__blockInFdefB : forall F id1 B,
  lookupBlockViaIDFromFdef F id1 = Some B ->
  blockInFdefB B F.
Proof.
  intros.
  destruct F as [f b].
  simpl in *.
  induction b as [|a b]; simpl in *.
    inversion H.

    destruct (in_dec eq_dec id1 (getStmtsIDs (snd a))).
      inv H. apply orb_true_iff. left.
      apply blockEqB_refl.

      apply orb_true_iff. right. apply IHb in H; auto.
Qed.

Lemma lookupBlockViaIDFromBlocks__InGetBlockIDs : forall bs id1 B,
  lookupBlockViaIDFromBlocks bs id1 = Some B ->
  In id1 (getStmtsIDs (snd B)).
Proof.
  intros.
  induction bs as [|a bs]; simpl in *.
    congruence.

    destruct (in_dec eq_dec id1 (getStmtsIDs (snd a))); eauto.
      inv H. auto.
Qed.

Lemma lookupBlockViaIDFromFdef__InGetBlockIDs : forall F id1 B,
  lookupBlockViaIDFromFdef F id1 = Some B ->
  In id1 (getStmtsIDs (snd B)).
Proof.
  intros.
  destruct F as [f b].
  eapply lookupBlockViaIDFromBlocks__InGetBlockIDs; eauto.
Qed.

Lemma getValueViaLabelFromValuels__In : forall vls v l1 vs1 ls1,
  getValueViaLabelFromValuels vls l1 = Some v ->
  split vls = (vs1, ls1) ->
  In l1 ls1.
Proof.
  induction vls; intros; simpl in *.
    inversion H.

    remember (split vls) as R.
    destruct R as [vs ls].
    destruct a as [v0 l0].
    inv H0.
    destruct (l0 == l1); subst.
      simpl. auto.

      simpl. right. eauto.
Qed.

Lemma In__getValueViaLabelFromValuels : forall vls l1 vs1 ls1,
  In l1 ls1 ->
  split vls = (vs1, ls1) ->
  NoDup ls1 ->
  exists v, getValueViaLabelFromValuels vls l1 = Some v.
Proof.
  induction vls; intros; simpl in *.
    inv H0. inversion H.

    destruct a as [v0 l0].
    destruct (l0 == l1); subst; eauto.
    remember (split vls) as R.
    destruct R.
    symmetry in HeqR.
    inv H0. inv H1.
    simpl in H.
    destruct H as [H | H]; subst.
      contradict n; auto.

      eapply IHvls in H; eauto.
Qed.

Lemma valueInTmnOperands__InOps : forall vid tmn,
  valueInTmnOperands (value_id vid) tmn ->
  In vid (getInsnOperands (insn_terminator tmn)).
Proof.
  intros vid tmn H.
  destruct tmn; simpl in *; subst; simpl; eauto.
Qed.


Lemma In_middle : forall A (c:A) cs1 cs2, In c (cs1++c::cs2).
Proof.
  induction cs1; simpl; auto.
Qed.

Ltac destruct_in H :=
match type of H with
| In _ [_] => simpl in H; destruct H as [H | H]; subst; try tauto
| In _ (_::_) => simpl in H; destruct H as [H | H]; subst; try tauto
| In _ (_++_) => apply in_app_or in H; destruct H as [H | H]
end.

Lemma valueInValues__iff__InOps : forall vid l0,
  In (value_id vid) l0 <->
  In vid (values2ids l0).
Proof.
  induction l0 as [|v]; intros; simpl in *.
    tauto.

    destruct IHl0 as [G1 G2].
    split; intro H.
      destruct H as [H | H]; simpl in *; subst; simpl; auto.
      destruct v; simpl; eauto.

      destruct v; simpl; eauto.
      destruct_in H.
Qed.

Lemma valueInValues__InOps : forall vid l0,
  In (value_id vid) l0 -> In vid (values2ids l0).
Proof.
  intros. eapply valueInValues__iff__InOps; eauto.
Qed.

Lemma valueInParams__InOps : forall vid p,
  valueInParams (value_id vid) p -> In vid (getParamsOperand p).
Proof.
  unfold getParamsOperand, valueInParams.
  induction p; intros; simpl in *; auto.
    destruct a.
    remember (split p) as R.
    destruct R; simpl in *.
    destruct H as [H | H]; subst; simpl in *; auto.
    destruct v; simpl; eauto.
Qed.

Lemma valueInCmdOperands__InOps : forall vid c,
  valueInCmdOperands (value_id vid) c ->
  In vid (getInsnOperands (insn_cmd c)).
Proof.
  intros vid c H.
  destruct c; simpl in *; try solve [
    destruct H; subst; simpl; try solve [auto | apply in_or_app; simpl; auto]
  ].

    destruct H; subst; simpl; auto.
      apply in_or_app. right. apply valueInValues__InOps; auto.

    destruct H; subst; simpl; auto.
    destruct H; subst; simpl.
      apply in_or_app; simpl; auto.
      apply in_or_app. right.
        apply in_or_app; simpl; auto.

    destruct H; subst; simpl; auto.
      apply in_or_app. right. apply valueInParams__InOps; auto.
Qed.

Lemma uniqF__uniqBlocks : forall fh lb,
  uniqFdef (fdef_intro fh lb) -> uniqBlocks lb.
Proof.
  intros. destruct fh. inversion H; auto.
Qed.

Lemma getCmdID_in_getCmdsLocs : forall cs i0 c,
  getCmdID c = Some i0 ->
  In c cs ->
  In i0 (getCmdsLocs cs ).
Proof.
  induction cs; intros.
    inversion H0.

    simpl in *.
    destruct H0 as [H0 | H0]; subst; eauto 3.
      apply getCmdLoc_getCmdID in H; auto.
Qed.

Lemma getCmdLoc_in_getCmdsLocs : forall cs c,
  In c cs ->
  In (getCmdLoc c) (getCmdsLocs cs).
Proof.
  induction cs; intros.
    inversion H.

    simpl in *.
    destruct H as [H | H]; subst; eauto 3.
Qed.

Lemma in_getStmtsLocs__in_getBlocksLocs : forall bs b i0,
  In i0 (getStmtsLocs (snd b)) ->
  InBlocksB b bs ->
  In i0 (getBlocksLocs bs).
Proof.
  induction bs; simpl; intros.
    inversion H0.

    apply orb_prop in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0. subst.
      apply in_or_app; auto.

      apply in_or_app; eauto.
Qed.

Lemma NotInArgsIDs_lookupTypViaIDFromArgs : forall la id1,
  ~ In id1 (getArgsIDs la) ->
  lookupTypViaIDFromArgs la id1 = None.
Proof.
  induction la; intros; simpl in *; auto.
    destruct a. destruct p.
    simpl in H.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst;
      eauto.
      contradict H; eauto.
Qed.

Lemma NotInPhiNodesIDs__lookupTypViaIDFromPhiNodes : forall la id1,
  ~ In id1 (getPhiNodesIDs la) ->
  lookupTypViaIDFromPhiNodes la id1 = None.
Proof.
  induction la; intros; simpl in *; auto.
    destruct a as [i0 ps0 cs0 t0]. unfold lookupTypViaIDFromPhiNode.
    simpl in H. simpl.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst;
      eauto.
      contradict H; eauto.
Qed.

Lemma NotInCmdLocs__lookupTypViaIDFromCmds : forall cs id1,
  ~ In id1 (getCmdsLocs cs) ->
  lookupTypViaIDFromCmds cs id1 = None.
Proof.
  induction cs; intros; simpl in *; auto.
    unfold lookupTypViaIDFromCmd.
    destruct (getCmdTyp a); auto.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 (getCmdLoc a));
      subst; eauto.
    contradict H; auto.
Qed.

Lemma lookupTypViaIDFromCmds__InCmdsLocs : forall cs id1 t,
  lookupTypViaIDFromCmds cs id1 = Some t ->
  In id1 (getCmdsLocs cs).
Proof.
  intros.
  destruct (In_dec eq_atom_dec id1 (getCmdsLocs cs)); auto.
    apply NotInCmdLocs__lookupTypViaIDFromCmds in n.
    rewrite H in n. inversion n.
Qed.

Lemma lookupTypViaIDFromPhiNodes__InPhiNodesIDs : forall la id1 t,
  lookupTypViaIDFromPhiNodes la id1 = Some t ->
  In id1 (getPhiNodesIDs la).
Proof.
  intros.
  destruct (In_dec eq_atom_dec id1 (getPhiNodesIDs la)); auto.
    apply NotInPhiNodesIDs__lookupTypViaIDFromPhiNodes in n.
    rewrite H in n. inversion n.
Qed.

Lemma notInBlock__lookupTypViaIDFromBlock : forall b i0,
  ~ In i0 (getStmtsLocs (snd b)) ->
  lookupTypViaIDFromBlock b i0 = None.
Proof.
  intros.
  destruct b as [l0 [p c t]]. simpl in *.
  remember (lookupTypViaIDFromPhiNodes p i0) as R.
  destruct R.
    symmetry in HeqR.
    apply lookupTypViaIDFromPhiNodes__InPhiNodesIDs in HeqR.
    contradict H. apply in_or_app; auto.
  remember (lookupTypViaIDFromCmds c i0) as R1.
  destruct R1.
    symmetry in HeqR1.
    apply lookupTypViaIDFromCmds__InCmdsLocs in HeqR1.
    contradict H. apply in_or_app. right. apply in_or_app; auto.
  unfold lookupTypViaIDFromTerminator.
  destruct (i0 == getTerminatorID t); subst; auto.
    contradict H. apply in_or_app. right. apply in_or_app; simpl; auto.
Qed.

Lemma lookupTypViaIDFromBlock__inBlock : forall b i0 t0,
  lookupTypViaIDFromBlock b i0 = Some t0 -> In i0 (getStmtsLocs (snd b)).
Proof.
  intros.
  destruct (In_dec eq_atom_dec i0 (getStmtsLocs (snd b))); auto.
    apply notInBlock__lookupTypViaIDFromBlock in n.
    rewrite H in n. inversion n.
Qed.

Lemma lookupTypViaIDFromBlock__inBlocks : forall bs b i0 t0,
  lookupTypViaIDFromBlock b i0 = Some t0 ->
  NoDup (getBlocksLocs bs) ->
  InBlocksB b bs = true ->
  lookupTypViaIDFromBlocks bs i0 = Some t0.
Proof.
  induction bs; simpl; intros.
    inversion H1.

    assert (J:=H0).
    apply NoDup_split in H0. destruct H0.
    apply orb_prop in H1.
    destruct H1 as [H1 | H1]; eauto.
      apply blockEqB_inv in H1. subst.
      rewrite H. auto.

      assert (H':=H).
      apply lookupTypViaIDFromBlock__inBlock in H.
      apply NoDup_disjoint with (i0:=i0) in J;
        eauto using in_getStmtsLocs__in_getBlocksLocs.
      apply notInBlock__lookupTypViaIDFromBlock in J.
      rewrite J. eauto.
Qed.

Lemma InCmds_lookupTypViaIDFromCmds : forall cs id1 c t1,
  NoDup (getCmdsLocs cs) ->
  In c cs ->
  getCmdLoc c = id1 ->
  getCmdTyp c = Some t1 ->
  lookupTypViaIDFromCmds cs id1 = Some t1.
Proof.
  induction cs; intros.
    inversion H0.

    simpl in *.
    inv H. unfold lookupTypViaIDFromCmd.
    destruct H0 as [H0 | H0]; subst.
      rewrite H2.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) 
                  (getCmdLoc c) (getCmdLoc c)); subst;
        auto.
        contradict n; auto.

      remember (getCmdTyp a) as R.
      destruct R; eauto.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) 
                  (getCmdLoc c) (getCmdLoc a));
        subst; eauto.

        apply getCmdLoc_in_getCmdsLocs in H0; auto.
        rewrite e in H0.
        contradict H0; auto.
Qed.

Lemma InCmds_lookupTypViaIDFromPhiNodes : forall cs id1 c t1,
  NoDup (getCmdsLocs cs) ->
  In c cs ->
  getCmdID c = Some id1 ->
  getCmdTyp c = Some t1 ->
  lookupTypViaIDFromCmds cs id1 = Some t1.
Proof.
  intros.
  eapply InCmds_lookupTypViaIDFromCmds; eauto 1.
  apply getCmdLoc_getCmdID in H1; auto.
Qed.

Lemma uniqF__lookupCmdTypViaIDFromFdef : forall l1 ps1 cs1 tmn1 f c i0 t0,
  uniqFdef f ->
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true ->
  In c cs1 ->
  getCmdLoc c = i0 ->
  getCmdTyp c = Some t0 ->
  lookupTypViaIDFromFdef f i0 = Some t0.
Proof.
  intros.
  destruct f as [f b].
  destruct f as [fnattrs5 typ5 id5 args5 varg5]. inversion H.
  apply NoDup_split in H5.
  destruct H5.
  simpl in *.
  assert (In i0 (getCmdsLocs cs1)) as HInCs.
    subst.
    eapply getCmdLoc_in_getCmdsLocs in H1; eauto.
  assert (In i0 (getBlocksLocs b)) as Hin.
    eapply in_getStmtsLocs__in_getBlocksLocs in H0; eauto.
    simpl. apply in_or_app. right. apply in_or_app; auto.
  destruct H as [J1 J2].
  assert (~ In i0 (getArgsIDs args5)) as Hnotin.
    eapply NoDup_disjoint; eauto.
  apply NotInArgsIDs_lookupTypViaIDFromArgs in Hnotin.
  rewrite Hnotin.
  eapply lookupTypViaIDFromBlock__inBlocks; eauto.
  simpl.
  apply NoDup__InBlocksB in H0; auto.
  simpl in H0.
  rewrite_env ((getPhiNodesIDs ps1 ++ getCmdsLocs cs1) ++ [getTerminatorID tmn1])
    in H0.
  apply NoDup_split in H0. destruct H0 as [H0 _].
  assert (~ In i0 (getPhiNodesIDs ps1)) as HnotinPs.
    eapply NoDup_disjoint; eauto.
  apply NotInPhiNodesIDs__lookupTypViaIDFromPhiNodes in HnotinPs.
  rewrite HnotinPs.
  apply NoDup_split in H0. destruct H0 as [_ H0].
  erewrite InCmds_lookupTypViaIDFromCmds; eauto.
Qed.

Lemma uniqF__lookupTypViaIDFromFdef : forall l1 ps1 cs1 tmn1 f c i0 t0,
  uniqFdef f ->
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true ->
  In c cs1 ->
  getCmdID c = Some i0 ->
  getCmdTyp c = Some t0 ->
  lookupTypViaIDFromFdef f i0 = Some t0.
Proof.
  intros.
  eapply uniqF__lookupCmdTypViaIDFromFdef; eauto 1.
  apply getCmdLoc_getCmdID in H2; auto.
Qed.

Lemma uniqFdef__uniqBlockLocs : forall F b1,
  uniqFdef F -> blockInFdefB b1 F -> NoDup (getStmtsLocs (snd b1)).
Proof.
  intros.
  destruct F as [f b]. destruct f.
  destruct H as [H _]. simpl in H0. destruct H.
  apply NoDup__InBlocksB in H0; auto.
Qed.

Lemma notInBlocks__lookupTypViaIDFromBlocks : forall bs i0,
  ~ In i0 (getBlocksLocs bs) ->
  lookupTypViaIDFromBlocks bs i0 = None.
Proof.
  induction bs; simpl; intros; auto.
    rewrite notInBlock__lookupTypViaIDFromBlock.
      rewrite IHbs; auto.
      intro J. apply H. apply in_or_app. auto.
    intro J. apply H. apply in_or_app. auto.
Qed.

Lemma lookupTypViaIDFromBlocks__InGetBlocksLocs: forall bs id5 t,
  lookupTypViaIDFromBlocks bs id5 = Some t ->
  In id5 (getBlocksLocs bs).
Proof.
  intros.
  destruct (in_dec eq_atom_dec id5 (getBlocksLocs bs)); auto.
  apply notInBlocks__lookupTypViaIDFromBlocks in n.
  rewrite H in n. inv n.
Qed.

Lemma lookupTypViaIDFromBlocks__inBlocks : forall bs b i0,
  NoDup (getBlocksLocs bs) ->
  InBlocksB b bs = true ->
  In i0 (getStmtsLocs (snd b)) ->
  lookupTypViaIDFromBlocks bs i0 = lookupTypViaIDFromBlock b i0.
Proof.
  induction bs; simpl; intros.
    inversion H0.

    assert (J:=H).
    apply NoDup_split in H. destruct H.
    apply orb_prop in H0.
    destruct H0 as [H0 | H0]; eauto.
      apply blockEqB_inv in H0. subst.
      apply NoDup_disjoint' with (i0:=i0) in J; auto.
      apply notInBlocks__lookupTypViaIDFromBlocks in J.
      rewrite J. destruct (lookupTypViaIDFromBlock a i0); auto.

      apply NoDup_disjoint with (i0:=i0) in J;
        eauto using in_getStmtsLocs__in_getBlocksLocs.
      rewrite notInBlock__lookupTypViaIDFromBlock; auto.
Qed.

Lemma InCmds_lookupTypViaIDFromCmds' : forall cs id1 c,
  NoDup (getCmdsLocs cs) ->
  In c cs ->
  getCmdID c = Some id1 ->
  lookupTypViaIDFromCmds cs id1 = getCmdTyp c.
Proof.
  induction cs; intros.
    inversion H0.

    simpl in *.
    inv H. unfold lookupTypViaIDFromCmd.
    destruct H0 as [H0 | H0]; subst.
      apply getCmdLoc_getCmdID in H1.
      rewrite H1.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 id1); subst.
        rewrite NotInCmdLocs__lookupTypViaIDFromCmds; auto.
        destruct (getCmdTyp c); auto.

        contradict n; auto.

      remember (getCmdTyp a) as R.
      destruct R; eauto.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 (getCmdLoc a));
        subst; eauto.

        apply getCmdID_in_getCmdsLocs with (i0:=getCmdLoc a) in H0; auto.
        contradict H0; auto.
Qed.

Lemma uniqF__lookupTypViaIDFromFdef' : forall l1 ps1 cs1 tmn1 f c i0,
  uniqFdef f ->
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true ->
  In c cs1 ->
  getCmdID c = Some i0 ->
  lookupTypViaIDFromFdef f i0 = getCmdTyp c.
Proof.
  intros.
  destruct f as [f b]. destruct f as [fnattrs5 typ5 id5 args5 varg5]. inversion H.
  apply NoDup_split in H4.
  destruct H4.
  simpl in *.
  assert (In i0 (getCmdsLocs cs1)) as HInCs.
    eapply getCmdID_in_getCmdsLocs in H1; eauto.
  assert (In i0 (getBlocksLocs b)) as Hin.
    eapply in_getStmtsLocs__in_getBlocksLocs in H0; eauto.
    simpl. apply in_or_app. right. apply in_or_app; auto.
  destruct H as [J1 J2].
  assert (~ In i0 (getArgsIDs args5)) as Hnotin.
    eapply NoDup_disjoint; eauto.
  apply NotInArgsIDs_lookupTypViaIDFromArgs in Hnotin.
  rewrite Hnotin.
  erewrite lookupTypViaIDFromBlocks__inBlocks; eauto.
    simpl.
    apply NoDup__InBlocksB in H0; auto.
    assert (J:=H0).
    rewrite_env ((getPhiNodesIDs ps1 ++ getCmdsLocs cs1) ++
      [getTerminatorID tmn1]) in H0.
    apply NoDup_split in H0. destruct H0 as [H0 _].
    assert (~ In i0 (getPhiNodesIDs ps1)) as HnotinPs.
      eapply NoDup_disjoint in H0; eauto.
    apply NotInPhiNodesIDs__lookupTypViaIDFromPhiNodes in HnotinPs.
    rewrite HnotinPs.
    apply NoDup_split in H0. destruct H0 as [_ H0].
    erewrite InCmds_lookupTypViaIDFromCmds'; eauto.
    destruct (getCmdTyp c); auto.
      unfold lookupTypViaIDFromTerminator.
      destruct (i0 == getTerminatorID tmn1); subst; auto.
        clear - J HInCs.
        simpl in J.
        apply NoDup_split in J. destruct J as [_ J].
        eapply NoDup_disjoint' in J; eauto.
          contradict J; simpl; auto.

    simpl. apply in_or_app. right. apply in_or_app. auto.
Qed.

Lemma lookupTypViaIDFromFdef__lookupTypViaIDFromPhiNodes : forall F id1 t b1,
  uniqFdef F ->
  lookupTypViaIDFromFdef F id1 = Some t ->
  blockInFdefB b1 F ->
  In id1 (getPhiNodesIDs (getPHINodesFromBlock b1)) ->
  lookupTypViaIDFromPhiNodes (getPHINodesFromBlock b1) id1 = Some t.
Proof.
  intros F id1 t b1 Huniq Hlk HBinF Hin.
  destruct F as [f b]. destruct f as [fnattrs5 typ5 id5 args5 varg5]. simpl in *.
  destruct Huniq as [Huniq1 Huniq2].
  destruct Huniq1 as [_ Huniq1].
  assert (Huniq1':=Huniq1).
  eapply NoDup__InBlocksB with (b:=b1) in Huniq1; eauto.
  destruct b1 as [l0 [p c t1]]. simpl in *.
  eapply NoDup_disjoint with (i0:=id1) in Huniq2; eauto.
    rewrite NotInArgsIDs_lookupTypViaIDFromArgs in Hlk; auto.
    erewrite lookupTypViaIDFromBlocks__inBlocks in Hlk; eauto.
      simpl in Hlk.
      destruct (lookupTypViaIDFromPhiNodes p id1); auto.
      remember (lookupTypViaIDFromCmds c id1) as R.
      destruct R.
        symmetry in HeqR.
        apply lookupTypViaIDFromCmds__InCmdsLocs in HeqR.
        eapply NoDup_disjoint' with (i0:=id1) in Huniq1; eauto.
          contradict Huniq1. apply in_or_app; auto.

        unfold lookupTypViaIDFromTerminator in Hlk.
        destruct (id1 == getTerminatorID t1); subst; try solve [inv Hlk].
        eapply NoDup_disjoint' with (i0:=getTerminatorID t1) in Huniq1; eauto.
          contradict Huniq1. apply in_or_app. simpl. auto.

      simpl. apply in_or_app. auto.

    eapply in_getStmtsLocs__in_getBlocksLocs; eauto.
      simpl. apply in_or_app. auto.
Qed.

Lemma NoDup_lookupTypViaIDFromArgs : forall la1 t a i0 la2,
  NoDup (getArgsIDs (la1 ++ (t, a, i0) :: la2)) ->
  lookupTypViaIDFromArgs (la1 ++ (t, a, i0) :: la2) i0 = Some t.
Proof.
  induction la1; simpl; intros.
    destruct (i0 == i0); auto.
      contradict n; auto.

    destruct a. destruct p.
    inv H.
    destruct (i0 == i1); subst; auto.
      rewrite getArgsIDs_app in H2. simpl in H2.
      contradict H2.
      apply in_or_app. simpl. auto.
Qed.

Lemma NoDupBlockLocs__notInCmds : forall ps2 cs2' c' tmn',
  NoDup (getStmtsLocs (stmts_intro ps2 (cs2' ++ [c']) tmn')) ->
  ~ In (getCmdLoc c') (getCmdsLocs cs2').
Proof.
  intros.
  simpl in H.
  apply NoDup_split in H.
  destruct H as [_ J].
  apply NoDup_split in J.
  destruct J as [J _].
  rewrite getCmdsLocs_app in J.
  simpl in J.
  apply NoDup_last_inv in J. auto.
Qed.

Lemma NoDupBlockLocs__NoDupCmds : forall ps2 cs2' tmn',
  NoDup (getStmtsLocs (stmts_intro ps2 cs2' tmn')) ->
  NoDup (getCmdsLocs cs2').
Proof.
  intros.
  simpl in H.
  apply NoDup_split in H.
  destruct H as [_ J].
  apply NoDup_split in J.
  destruct J as [J _]. auto.
Qed.

Lemma NoDup_lookupTypViaIDFromPhiNodes : forall ps1 i0 t0 l0 ps2,
  NoDup (getPhiNodesIDs (ps1 ++ insn_phi i0 t0 l0 :: ps2)) ->
  lookupTypViaIDFromPhiNodes (ps1 ++ insn_phi i0 t0 l0 :: ps2) i0 = Some t0.
Proof.
  induction ps1; simpl; unfold lookupTypViaIDFromPhiNode; simpl; intros.
    destruct (i0 == i0); auto.
      contradict n; auto.

    destruct a as [i1 t1].
    inv H. simpl.
    destruct (i0 == i1); subst; auto.
      rewrite getPhiNodesIDs_app in H2. simpl in H2.
      contradict H2.
      apply in_or_app. simpl. auto.
Qed.

Lemma in_middle : forall A (c:A) cs1 cs2, In c (cs1 ++ c :: cs2).
Proof.
  intros.
  apply in_app_iff; simpl; auto.
Qed.

Lemma uniqBlocksLocs__uniqBlockLocs : forall bs b,
  NoDup (getBlocksLocs bs) ->
  InBlocksB b bs = true ->
  NoDup (getStmtsLocs (snd b)).
Proof.
  induction bs; intros.
     inv H0.

     simpl in *.
     apply orb_prop in H0.
     apply NoDup_split in H.
     destruct H.
     destruct H0 as [H0 | H0]; subst; auto.
       apply blockEqB_inv in H0; subst; auto.
Qed.

Lemma mgetoffset_aux__getSubTypFromConstIdxs : forall TD const_list idxs o t'
    t1 o0
  (HeqR1 : Some idxs = intConsts2Nats TD const_list)
  (HeqR2 : Some (o, t') = mgetoffset_aux TD t1 idxs o0),
  getSubTypFromConstIdxs const_list t1 = Some t'.
Proof.
  induction const_list; simpl; intros.
    inv HeqR1. simpl in HeqR2. inv HeqR2. auto.

    destruct_const a; tinv HeqR1.
    destruct (Size.dec sz5 Size.ThirtyTwo); tinv HeqR1.
    remember (intConsts2Nats TD const_list) as R3.
    destruct R3; inv HeqR1.
    destruct t1; tinv HeqR2.
      simpl in HeqR2.
      destruct (LLVMtd.getTypeAllocSize TD t1); inv HeqR2; eauto.
      simpl in HeqR2.
      destruct (LLVMtd._getStructElementOffset TD l1 (Coqlib.nat_of_Z
        (INTEGER.to_Z Int5)) 0); inv HeqR2; eauto.
      unfold INTEGER.to_Z in H0. unfold INTEGER.to_nat.
      destruct (nth_error l1 (Coqlib.nat_of_Z Int5)); tinv H0.
      simpl in H0. eauto.
Qed.

Lemma mgetoffset__getSubTypFromConstIdxs : forall TD const_list idxs o t' t1
  (HeqR1 : Some idxs = intConsts2Nats TD const_list)
  (HeqR2 : Some (o, t') = mgetoffset TD t1 idxs),
  getSubTypFromConstIdxs const_list t1 = Some t'.
Proof.
  unfold mgetoffset. intros.
  eapply mgetoffset_aux__getSubTypFromConstIdxs; eauto.
Qed.

Lemma lookupPhiNodeViaIDFromPhiNodes_middle : forall ps1 i0 t0 l0 ps2,
  NoDup (getPhiNodesIDs (ps1 ++ insn_phi i0 t0 l0 :: ps2)) ->
  lookupPhiNodeViaIDFromPhiNodes (ps1 ++ insn_phi i0 t0 l0 :: ps2) i0 =
    Some (insn_phi i0 t0 l0).
Proof.
  induction ps1; simpl; intros; auto.
    destruct (i0==i0); try (auto || congruence).

    inv H.
    destruct (getPhiNodeID a==i0); subst; eauto.
      rewrite getPhiNodesIDs_app in H2.
      apply NotIn_inv in H2. destruct H2.
      contradict H0; simpl; auto.
Qed.

Lemma notin__lookupPhiNodeViaIDFromPhiNodes_none : forall i0 ps,
  ~ In i0 (getPhiNodesIDs ps) ->
  lookupPhiNodeViaIDFromPhiNodes ps i0 = None.
Proof.
  induction ps; simpl; intros; auto.
    destruct(@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getPhiNodeID a) i0);
      subst; auto.
      contradict H; auto.
Qed.

Lemma lookupCmdViaIDFromCmds__lookupPhiNodeInsnViaIDFromPhiNodes : forall
    id0 ps' tmn' cs' c,
  NoDup (getStmtsLocs (stmts_intro ps' cs' tmn')) ->
  lookupCmdViaIDFromCmds cs' id0 = Some c ->
  lookupPhiNodeViaIDFromPhiNodes ps' id0 = None.
Proof.
  induction cs'; simpl; intros.
    congruence.

    destruct (eq_atom_dec id0 (getCmdLoc a)); inv H0.
      apply NoDup_disjoint with (i0:=getCmdLoc c) in H; simpl;
        eauto using notin__lookupPhiNodeViaIDFromPhiNodes_none.
      eapply IHcs'; eauto.
        simpl. simpl_env in *. apply NoDup_strenthening in H; auto.
Qed.

Lemma lookupPhiNodeViaIDFromPhinodes__In : forall id0 ps p,
  lookupPhiNodeViaIDFromPhiNodes ps id0 = Some p ->
  In id0 (getPhiNodesIDs ps).
Proof.
  induction ps; simpl; intros.
    congruence.
    destruct (getPhiNodeID a == id0); inv H; eauto.
Qed.

Lemma lookupCmdViaIDFromCmds__In : forall id0 cs c,
  lookupCmdViaIDFromCmds cs id0 = Some c ->
  In id0 (getCmdsLocs cs).
Proof.
  induction cs; simpl; intros.
    congruence.
     destruct (eq_atom_dec id0 (getCmdLoc a)); inv H; eauto.
Qed.

Lemma in_first_chunk: forall X (a:X) A B C, In a A -> In a (A++B++C).
Proof.
  intros. apply in_or_app. auto.
Qed.

Lemma in_second_chunk: forall X (b:X) A B C, In b B -> In b (A++B++C).
Proof.
  intros. apply in_or_app. right. apply in_or_app. auto.
Qed.

Lemma in_third_chunk: forall X (c:X) A B C, In c C -> In c (A++B++C).
Proof.
  intros. apply in_or_app. right. apply in_or_app. auto.
Qed.

Lemma lookupInsnViaIDFromBlock__In : forall b id0 instr,
  lookupInsnViaIDFromBlock b id0 = Some instr ->
  In id0 (getStmtsLocs (snd b)).
Proof.
  destruct b as [l0 [p c t]]; simpl; intros.
  remember (lookupPhiNodeViaIDFromPhiNodes p id0) as R1.
  destruct R1; inv H.
    apply in_first_chunk; eauto using lookupPhiNodeViaIDFromPhinodes__In.
    remember (lookupCmdViaIDFromCmds c id0) as R2.
    destruct R2; inv H1.
      apply in_second_chunk; eauto using lookupCmdViaIDFromCmds__In.
     
      destruct_if. apply in_third_chunk; simpl; auto.
Qed.

Lemma lookupCmdViaIDFromBlocks__lookupPhiNodeInsnViaIDFromPhiNodes : forall
    id0 c l' ps' cs' tmn' bs,
  NoDup (getBlocksLocs bs) ->
  lookupInsnViaIDFromBlocks bs id0 = Some (insn_cmd c) ->
  InBlocksB (l', stmts_intro ps' cs' tmn') bs ->
  lookupPhiNodeViaIDFromPhiNodes ps' id0 = None.
Proof.
  induction bs; simpl; intros.
    congruence.

    apply orb_true_iff in H1.
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst. simpl in H0.
      destruct (lookupPhiNodeViaIDFromPhiNodes ps' id0); inv H0.
      remember (lookupCmdViaIDFromCmds cs' id0) as R.
      destruct R; inv H2; auto.

      remember (lookupInsnViaIDFromBlock a id0) as R.
      assert (H':=H).
      apply NoDup_split in H. destruct H.
      destruct R; inv H0; eauto.
      symmetry in HeqR.
      apply lookupInsnViaIDFromBlock__In in HeqR.
      eapply NoDup_disjoint' in H'; eauto.
      assert (~ In id0 (getStmtsLocs (stmts_intro ps' cs' tmn'))) as J.
        intro J. apply H'.
        eapply in_getStmtsLocs__in_getBlocksLocs in H1; eauto.
      apply notin__lookupPhiNodeViaIDFromPhiNodes_none; auto.
        intro J'. apply J. apply in_or_app; auto.
 Qed.

Lemma lookupTmnViaIDFromBlocks__lookupPhiNodeInsnViaIDFromPhiNodes : forall
    bs id0 tmn l' ps' cs' tmn',
  NoDup (getBlocksLocs bs) ->
  lookupInsnViaIDFromBlocks bs id0 = Some (insn_terminator tmn) ->
  InBlocksB (l', stmts_intro ps' cs' tmn') bs ->
  lookupPhiNodeViaIDFromPhiNodes ps' id0 = None.
Proof.
  induction bs; simpl; intros.
    congruence.

    apply orb_true_iff in H1.
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst. simpl in H0.
      destruct (lookupPhiNodeViaIDFromPhiNodes ps' id0); inv H0.
      destruct (lookupCmdViaIDFromCmds cs' id0); inv H2; auto.

      remember (lookupInsnViaIDFromBlock a id0) as R.
      assert (H':=H).
      apply NoDup_split in H. destruct H.
      destruct R; inv H0; eauto.
      symmetry in HeqR.
      apply lookupInsnViaIDFromBlock__In in HeqR.
      eapply NoDup_disjoint' in H'; eauto.
      assert (~ In id0 (getStmtsLocs (stmts_intro ps' cs' tmn'))) as J.
        intro J. apply H'.
        eapply in_getStmtsLocs__in_getBlocksLocs in H1; eauto.
      apply notin__lookupPhiNodeViaIDFromPhiNodes_none; auto.
        intro J'. apply J. apply in_or_app; auto.
Qed.

Lemma lookupNoneViaIDFromBlocks__lookupPhiNodeInsnViaIDFromPhiNodes : forall
    bs id0 l' ps' cs' tmn',
  NoDup (getBlocksLocs bs) ->
  lookupInsnViaIDFromBlocks bs id0 = None ->
  InBlocksB (l', stmts_intro ps' cs' tmn') bs ->
  lookupPhiNodeViaIDFromPhiNodes ps' id0 = None.
Proof.
  induction bs; simpl; intros.
    congruence.

    apply orb_true_iff in H1.
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst. simpl in H0.
      destruct (lookupPhiNodeViaIDFromPhiNodes ps' id0).
        congruence. auto.

      apply NoDup_split in H. destruct H.
      destruct (lookupInsnViaIDFromBlock a id0); inv H0; eauto.
Qed.

Lemma lookupPhiViaIDFromBlocks__lookupPhiNodeInsnViaIDFromPhiNodes : forall
    bs id0 p l' ps' cs' tmn' p',
  NoDup (getBlocksLocs bs) ->
  lookupInsnViaIDFromBlocks bs id0 = Some (insn_phinode p) ->
  InBlocksB (l', stmts_intro ps' cs' tmn') bs ->
  lookupPhiNodeViaIDFromPhiNodes ps' id0 = Some p' ->
  p = p'.
Proof.
  induction bs; simpl; intros.
    congruence.

    apply orb_true_iff in H1.
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst. simpl in H0.
      destruct (lookupPhiNodeViaIDFromPhiNodes ps' id0); congruence.

      remember (lookupInsnViaIDFromBlock a id0) as R.
      assert (H':=H).
      apply NoDup_split in H. destruct H.
      destruct R; inv H0; eauto.
      symmetry in HeqR.
      apply lookupInsnViaIDFromBlock__In in HeqR.
      eapply NoDup_disjoint' in H'; eauto.
      assert (~ In id0 (getStmtsLocs (stmts_intro ps' cs' tmn'))) as J.
        intro J. apply H'.
        eapply in_getStmtsLocs__in_getBlocksLocs in H1; eauto.
      assert (lookupPhiNodeViaIDFromPhiNodes ps' id0 = None) as J'.
        apply notin__lookupPhiNodeViaIDFromPhiNodes_none; auto.
        intro J'. apply J. apply in_or_app; auto.
      rewrite H2 in J'. congruence.
Qed.

Lemma notin__lookupCmdViaIDFromCmds_none : forall id0 cs,
  ~ In id0 (getCmdsLocs cs) ->
  lookupCmdViaIDFromCmds cs id0 = None.
Proof.
  induction cs; simpl; intros; auto.
    destruct (eq_atom_dec id0 (getCmdLoc a)); subst; auto.
      contradict H; auto.
Qed.

Lemma notin__lookupPhiNodeViaIDFromPhinodes_none : forall id0 ps,
  ~ In id0 (getPhiNodesIDs ps) ->
  lookupPhiNodeViaIDFromPhiNodes ps id0 = None.
Proof.
  induction ps; simpl; intros; auto.
    destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom)(getPhiNodeID a) id0);
      subst; eauto.
      contradict H; auto.
Qed.

Lemma notin__lookupInsnViaIDFromBlock_none : forall b id0,
  ~ In id0 (getStmtsLocs (snd b)) ->
  lookupInsnViaIDFromBlock b id0 = None.
Proof.
  destruct b as [l0 [p c t]]; simpl; intros.
  assert (lookupPhiNodeViaIDFromPhiNodes p id0 = None) as J.
    apply notin__lookupPhiNodeViaIDFromPhinodes_none.
    intro J. apply H. apply in_or_app; auto.
  rewrite J.
  assert (lookupCmdViaIDFromCmds c id0 = None) as J'.
    apply notin__lookupCmdViaIDFromCmds_none.
    intro J'. apply H.
    apply in_or_app. right.
    apply in_or_app; auto.
  fill_ctxhole.
  destruct_if. 
  contradict H. apply in_third_chunk; simpl; auto.
Qed.

Lemma in_middle__lookupCmdViaIDFromCmds : forall cs1 id1 c
  (Hid : getCmdID c = Some id1) cs1',
  NoDup (getCmdsLocs (cs1' ++ c :: cs1)) ->
  lookupCmdViaIDFromCmds (cs1' ++ c :: cs1) id1 = Some c.
Proof.
  induction cs1'; simpl; intros; auto.
    apply getCmdLoc_getCmdID in Hid.
    rewrite Hid.
    destruct (eq_atom_dec id1 id1); congruence; auto.

    inv H.
    destruct (eq_atom_dec id1 (getCmdLoc a)); subst; auto.
      apply getCmdLoc_getCmdID in Hid.
      contradict H2. rewrite getCmdsLocs_app.
      apply in_or_app. simpl. auto.
Qed.

Lemma InGetCmdsLocs_middle: forall cs1 c1 cs2,
  In (getCmdLoc c1) (getCmdsLocs (cs1 ++ c1 :: cs2)).
Proof.
  intros.
  rewrite getCmdsLocs_app. apply in_or_app. simpl. auto.
Qed.

Lemma InGetCmdsIDs_middle: forall cs1 c1 cs2 id1 (Hid: getCmdID c1 = Some id1),
  In id1 (getCmdsLocs (cs1 ++ c1 :: cs2)).
Proof.
  intros.
  apply getCmdLoc_getCmdID in Hid. subst.
  apply InGetCmdsLocs_middle.
Qed.

Lemma cmdInBlock__lookupInsnViaIDFromBlock : forall id1 c
  (Hid : getCmdID c = Some id1) l3 ps1 cs1' cs1 tmn1
  (Huniq : NoDup (getStmtsLocs (stmts_intro ps1 (cs1' ++ c :: cs1) tmn1))),
  lookupInsnViaIDFromBlock (l3, stmts_intro ps1 (cs1' ++ c :: cs1) tmn1) id1 =
    Some (insn_cmd c).
Proof.
  simpl. intros.
  assert (lookupPhiNodeViaIDFromPhiNodes ps1 id1 = None) as J.
    apply notin__lookupPhiNodeViaIDFromPhinodes_none.
    eapply NoDup_disjoint; eauto.
    apply in_or_app. left.
    eapply InGetCmdsIDs_middle; eauto.
  rewrite J.
  assert (lookupCmdViaIDFromCmds (cs1' ++ c :: cs1) id1 = Some c) as J'.
    apply NoDup_split in Huniq. inv Huniq.
    apply NoDup_split in H0. inv H0.
    apply in_middle__lookupCmdViaIDFromCmds; auto.
  rewrite J'. 
  apply NoDup_split in Huniq. destruct Huniq as [_ Huniq].
  apply NoDup_disjoint' with (i0:=id1) in Huniq; 
    eauto using InGetCmdsIDs_middle.
Qed.

Lemma cmdInBlocks__InGetBlocksLocs : forall bs1 l3 ps1 cs1' c cs1 tmn1 id1,
  getCmdID c = Some id1 ->
  InBlocksB (l3, stmts_intro ps1 (cs1' ++ c :: cs1) tmn1) bs1 = true ->
  In id1 (getBlocksLocs bs1).
Proof.
  induction bs1; simpl; intros.
    congruence.

    apply orb_true_iff in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0. subst.
      apply in_or_app. left. simpl.
      apply in_or_app. right.
      apply in_or_app. left.
      rewrite getCmdsLocs_app.
      apply in_or_app. right. simpl.
      apply getCmdLoc_getCmdID in H. auto.

      apply in_or_app. right. eauto.
Qed.

Lemma InBlocksB__lookupInsnViaIDFromBlocks : forall bs1 id1 c
  (Hid : getCmdID c = Some id1)
  (Huniq : NoDup (getBlocksLocs bs1)) l3 ps1 cs1' cs1 tmn1
  (Hin : InBlocksB (l3, stmts_intro ps1 (cs1' ++ c :: cs1) tmn1) bs1 = true),
  lookupInsnViaIDFromBlocks bs1 id1 = Some (insn_cmd c).
Proof.
  induction bs1; simpl; intros.
    congruence.

    apply orb_true_iff in Hin.
    assert (J:=Huniq).
    apply NoDup_split in J.
    destruct J.
    destruct Hin as [Hin | Hin].
      apply blockEqB_inv in Hin. subst.
      eapply cmdInBlock__lookupInsnViaIDFromBlock in H; eauto.
      rewrite H. auto.

      assert (lookupInsnViaIDFromBlock a id1 = None) as J.
        apply notin__lookupInsnViaIDFromBlock_none; auto.
        eapply NoDup_disjoint in Huniq; eauto.
        eapply cmdInBlocks__InGetBlocksLocs; eauto.
      rewrite J; eauto.
Qed.

Lemma map_app_inv : forall A B l1 l2 l (f:A->B),
  List.map f l = l1 ++ l2 ->
  exists l1', exists l2',
    l = l1' ++ l2' /\ List.map f l1' = l1 /\ List.map f l2' = l2.
Proof.
  induction l1; simpl; intros.
    exists nil. exists l0. auto.

    destruct l0; inv H.
    apply IHl1 in H2. destruct H2 as [l1' [l2' [J1 [J2 J3]]]]; subst.
    exists (a0::l1'). exists l2'. auto.
Qed.

Lemma insnInFdefBlockB__insnInBlockB : forall instr f b,
  insnInFdefBlockB instr f b = true ->
  insnInBlockB instr b = true.
Proof.
  intros.
  destruct instr; simpl in *; try (apply andb_true_iff in H; destruct H; auto).
Qed.

Lemma insnInFdefBlockB__blockInFdefB : forall instr f b,
  insnInFdefBlockB instr f b = true ->
  blockInFdefB b f = true.
Proof.
  intros.
  destruct instr; simpl in *; try (apply andb_true_iff in H; destruct H; auto).
Qed.

Lemma In_InCmdLocs : forall c cs,
  In c cs -> In (getCmdLoc c) (getCmdsLocs cs).
Proof.
  induction cs; intros; inv H; simpl; auto.
Qed.

Lemma NoDup_getCmdsLocs_prop : forall c1 c2 cs,
  NoDup (getCmdsLocs cs) ->
  In c1 cs ->
  In c2 cs ->
  getCmdLoc c1 = getCmdLoc c2 ->
  c1 = c2.
Proof.
  induction cs; simpl; intros.
    inv H0.

    inv H.
    destruct H0 as [H0 | H0]; subst.
      destruct H1 as [H1 | H1]; subst; auto.
        rewrite H2 in H5. apply In_InCmdLocs in H1. contradict H1; auto.
      destruct H1 as [H1 | H1]; subst; auto.
        rewrite <- H2 in H5. apply In_InCmdLocs in H0. contradict H0; auto.
Qed.

Lemma InCmdsB_in : forall c cs, InCmdsB c cs = true -> In c cs.
Proof.
  induction cs; simpl; intros.
    congruence.
    apply orb_true_iff in H.
    destruct H as [H | H]; auto.
    apply cmdEqB_inv in H; auto.
Qed.

Lemma In_InCmdsB : forall c cs, In c cs -> InCmdsB c cs = true.
Proof.
  induction cs; simpl; intros.
    inv H.

    apply orb_true_iff.
    destruct H as [H | H]; subst; auto.
      left. apply cmdEqB_refl.
Qed.

Lemma fold_left_eq : forall B f (J:forall a b, f a b = false -> a = false),
  forall (l1:list B) a, List.fold_left f l1 a = false -> a = false.
Proof.
  induction l1; simpl; intros; eauto.
Qed.

Lemma fold_left_congruence : forall B (f:Prop -> B -> Prop)
  (J:forall (a b:Prop) c, (a->b) -> (f a c -> f b c))
  (l1:list B) (a b:Prop),
  (a -> b) ->
  (List.fold_left f l1 a -> List.fold_left f l1 b).
Proof. induction l1; simpl; intros; eauto. Qed.

Lemma fold_left_prop : forall B (f:Prop -> B -> Prop),
  (forall (a:Prop) b, f a b -> a) ->
  (forall (a b:Prop) c, (a->b) -> (f a c -> f b c)) ->
  forall (l1:list B) (a:Prop),
  (List.fold_left f l1 a -> a).
Proof.
  induction l1; simpl; intros; auto.
    apply IHl1; auto.
    apply fold_left_congruence with (a:=f a0 a); auto.
    apply H.
Qed.

Lemma fold_left_or_false : forall B (f:bool -> B -> bool)
  (J:forall a b, f a b = false -> a = false),
  forall (l1:list B) init,
    List.fold_left f l1 init = false ->
    List.fold_left f l1 false = false /\ init = false.
Proof.
  induction l1; simpl; intros; eauto.
    assert (H':=H).
    apply IHl1 in H.
    destruct H as [H1 H2].
    apply J in H2. subst.
    split; auto.
Qed.

Lemma fold_left_and_true : forall B (f:bool -> B -> bool)
  (J:forall a b, f a b = true -> a = true),
  forall (l1:list B) init,
    List.fold_left f l1 init = true ->
    List.fold_left f l1 true = true /\ init = true.
Proof.
  induction l1; simpl; intros; eauto.
    assert (H':=H).
    apply IHl1 in H.
    destruct H as [H1 H2].
    apply J in H2. subst.
    split; auto.
Qed.

Lemma fold_left_or_spec : forall B (f:bool -> B -> bool)
  (J:forall a b, a = true -> f a b = true),
  forall (l1:list B), List.fold_left f l1 true = true.
Proof.
  induction l1; simpl; intros; eauto.
    rewrite J; auto.
Qed.

Lemma filter_ext: forall (A:Type) (f g:A->bool)
  (Heq: forall a, f a = g a) (l0:list A), List.filter f l0 = List.filter g l0.
Proof.
  induction l0; intros; simpl; auto.
    rewrite Heq. rewrite IHl0. auto.
Qed.

Lemma filter_true: forall (A:Type) (f:A->bool)
  (Heq: forall a, f a = true) (l0:list A), l0 = List.filter f l0.
Proof.
  induction l0; intros; simpl; auto.
    rewrite Heq. congruence.
Qed.

Lemma fold_left_or_false_elim : forall B (f: B -> bool)
  l0 init (H:fold_left (fun a b => a || f b) l0 init = false),
  forall x (Hin: In x l0), f x = false.
Proof.
  induction l0; simpl; intros. 
    tauto.

    apply fold_left_or_false in H.
      destruct H as [H1 H2].
      binvf H2 as H3 H4. 
      destruct Hin as [Hin | Hin]; subst; eauto.
      
      intros. binvf H0 as H3 H4. auto.
Qed.

Lemma not_id_dec__neq : forall id5 id0,
  @eq _ (@proj_sumbool _ _ (id_dec id5 id0)) false ->
  id5 <> id0.
Proof.
  intros.
  destruct (id_dec id5 id0); subst; auto.
    simpl in *. congruence.
Qed.

Lemma IngetCmdsLocs__lookupCmdViaIDFromCmds: forall c1 cs1
  (Huniq: NoDup (getCmdsLocs cs1)) (H0 : In c1 cs1),
  lookupCmdViaIDFromCmds cs1 (getCmdLoc c1) = Some c1.
Proof.
  induction cs1; simpl; intros.
    inv H0.

    destruct H0 as [H0 | H0]; subst.
      destruct (eq_atom_dec (getCmdLoc c1) (getCmdLoc c1)); auto.
        congruence.
      inv Huniq.
      destruct (eq_atom_dec (getCmdLoc c1) (getCmdLoc a)); auto.
        contradict H2. rewrite <- e. apply In_InCmdLocs; auto.
Qed.

Lemma IngetCmdsIDs__lookupCmdViaIDFromFdef: forall c1 l1 ps1 cs1 tmn1 f
  (Huniq: uniqFdef f)
  (H : blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true)
  (H0 : In c1 cs1),
  lookupInsnViaIDFromFdef f (getCmdLoc c1) = Some (insn_cmd c1).
Proof.
  destruct f as [[] bs]. simpl. intros.
  destruct Huniq as [_ Huniq].
  apply NoDup_split in Huniq.
  destruct Huniq as [_ Huniq].
  generalize dependent l1.
  generalize dependent ps1.
  generalize dependent cs1.
  generalize dependent tmn1.
  induction bs as [|a0 bs]; simpl; intros.
    inv H.

    simpl in Huniq.
    apply NoDup_split' in Huniq.
    destruct Huniq as [J1 [J2 J3]].
    apply orb_true_iff in H.
    destruct H as [H | H].
      apply blockEqB_inv in H.
      subst. simpl.
      assert (~ In (getCmdLoc c1) (getPhiNodesIDs ps1)) as Hnotin.
        simpl in J1.
        apply NoDup_disjoint with (i0:=getCmdLoc c1)
          in J1; auto.
        apply in_or_app. left. apply In_InCmdLocs; auto.
      rewrite notin__lookupPhiNodeViaIDFromPhiNodes_none; auto.
      simpl in J1. apply NoDup_split in J1. destruct J1 as [_ J1].
      apply NoDup_split in J1. destruct J1 as [Huniq _].
      rewrite IngetCmdsLocs__lookupCmdViaIDFromCmds; auto.

      assert (~ In (getCmdLoc c1) (getStmtsLocs (snd a0))) as Hnotin.
        intro J. apply J3 in J. apply J.
        eapply in_getStmtsLocs__in_getBlocksLocs in H; eauto.
        simpl. apply in_or_app. right.
        apply in_or_app. left. apply In_InCmdLocs; auto.
      rewrite notin__lookupInsnViaIDFromBlock_none; auto.
      eapply IHbs; eauto.
Qed.

Lemma in_getCmdsIDs__in_getCmdsLocs: forall id1 cs,
  In id1 (getCmdsIDs cs) -> In id1 (getCmdsLocs cs).
Proof.
  induction cs; simpl; intros; auto.
    remember (getCmdID a) as R.
    destruct R; auto.
    symmetry in HeqR.
    apply getCmdLoc_getCmdID in HeqR. subst.
    simpl in H. destruct H; auto.
Qed.

Lemma in_getStmtsIDs__in_getStmtsLocs: forall id1 sts,
  In id1 (getStmtsIDs sts) -> In id1 (getStmtsLocs sts).
Proof.
  destruct sts as []. simpl. intros.
  apply in_app_or in H.
  apply in_or_app.
  destruct H as [H | H]; auto.
  right.
  apply in_or_app.
  left. apply in_getCmdsIDs__in_getCmdsLocs; auto.
Qed.

Lemma rev_non_nil: forall A (ls1:list A),
  ls1 <> nil <-> rev ls1 <> nil.
Proof.
  induction ls1; simpl.
    split; auto.  
    split; intro J; auto with datatypes v62.      
Qed.

Lemma cons_last: forall A (hd:A) tl, 
  exists pre, exists last, hd::tl = pre++[last].
Proof.
  intros.
  assert (hd::tl <> nil) as Hnnil.
    congruence.
  apply exists_last in Hnnil.
  destruct Hnnil as [? [? ?]].
  eauto.
Qed.

Lemma inGetBlockIDs__lookupBlockViaIDFromFdef: forall id1 b f,
  uniqFdef f -> In id1 (getStmtsIDs (snd b)) -> blockInFdefB b f = true ->
  lookupBlockViaIDFromFdef f id1 = Some b.
Proof.
  destruct f as [[fa tu fid la va] bs]. simpl.
  intros [J1 J2].
  apply NoDup_split in J2. destruct J2 as [_ J2].
  generalize dependent b.
  generalize dependent id1.
  induction bs as [|a bs]; simpl; intros.
    congruence.

    apply orb_true_iff in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0. subst.
      destruct (@in_dec id (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom)) id1
         (getStmtsIDs (snd a))); auto.
        contradict H; auto.

      destruct (@in_dec id (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom)) id1
         (getStmtsIDs (snd a))).
        apply in_getStmtsIDs__in_getStmtsLocs in H.
        apply in_getStmtsIDs__in_getStmtsLocs in i0.
        simpl in *.
        apply NoDup_disjoint' with (i0:=id1) in J2; auto.
          apply in_getStmtsLocs__in_getBlocksLocs with (i0:=id1) in H0; auto.
            contradict J2. auto.

        simpl_env in J1.
        apply uniqBlocks_inv in J1.
        destruct J1. simpl in J2. apply NoDup_split in J2. destruct J2.
        apply IHbs; auto.
Qed.

Lemma lookupBlockViaIDFromFdef__uniq: forall f id0 b1 b2,
  uniqFdef f ->
  lookupBlockViaIDFromFdef f id0 = Some b1 ->
  lookupBlockViaIDFromFdef f id0 = Some b2 ->
  b1 = b2.
Proof.
  destruct f as [[fa tu fid la va] bs]. simpl.
  induction bs as [|a bs]; simpl; intros.
    inv H0.

    destruct (in_dec eq_dec id0 (getStmtsIDs (snd a))); eauto.
      congruence. congruence.
Qed.

Lemma block_eq1: forall f id0 b1 b2,
  uniqFdef f -> blockInFdefB b2 f = true ->
  lookupBlockViaIDFromFdef f id0 = Some b1 ->
  In id0 (getStmtsIDs (snd b2)) ->
  b1 = b2.
Proof.
  intros.
  eapply inGetBlockIDs__lookupBlockViaIDFromFdef in H2; eauto.
  eapply lookupBlockViaIDFromFdef__uniq in H1; eauto.
Qed.

Lemma lookupTypViaIDFromPhiNodes__NotInPhiNodesIDs : forall la id1,
  lookupTypViaIDFromPhiNodes la id1 = None ->
  ~ In id1 (getPhiNodesIDs la).
Proof.
  induction la; intros; simpl in *; auto.
    destruct a. unfold lookupTypViaIDFromPhiNode in *. simpl in *.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 id5); subst.
      congruence.

      apply IHla in H. intro J.
      destruct J; subst; auto.
Qed.

Lemma getCmdTyp__total: forall c, getCmdTyp c <> None.
Proof. 
  destruct c; simpl; try congruence.
    destruct_if; congruence.
Qed.

Lemma lookupTypViaIDFromCmds__NotInCmdLocs : forall cs id1,
  lookupTypViaIDFromCmds cs id1 = None ->
  ~ In id1 (getCmdsLocs cs).
Proof.
  induction cs; intros; simpl in *; auto.
    unfold lookupTypViaIDFromCmd in *.
    remember (getCmdTyp a) as R.
    destruct R.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 (getCmdLoc a));
        subst.
        congruence.

        apply IHcs in H. intro J.
        destruct J; subst; auto.

      symmetry in HeqR. contradict HeqR. apply getCmdTyp__total.
Qed.

Lemma lookupTypViaIDFromTerminator__neq : forall tmn id1,
  lookupTypViaIDFromTerminator tmn id1 = None ->
  id1 <> (getTerminatorID tmn).
Proof.
  intros.
  unfold lookupTypViaIDFromTerminator in *.
  destruct_if. auto.
Qed.

Lemma lookupTypViaIDFromBlock__notInBlock : forall b i0,
  lookupTypViaIDFromBlock b i0 = None ->
  ~ In i0 (getStmtsLocs (snd b)).
Proof.
  destruct b as [? []]. simpl; intros; auto.
    remember (lookupTypViaIDFromPhiNodes phinodes5 i0) as R.
    destruct R.
      inv H.
      remember (lookupTypViaIDFromCmds cmds5 i0) as R.
      destruct R.
        inv H.
        symmetry in HeqR, HeqR0.
        apply lookupTypViaIDFromPhiNodes__NotInPhiNodesIDs in HeqR.
        apply lookupTypViaIDFromCmds__NotInCmdLocs in HeqR0.
        intro J. apply in_app_or in J. destruct J; auto.
        
        apply lookupTypViaIDFromTerminator__neq in H.
        apply in_app_or in H0.
        destruct H0 as [H0 | H0]; auto.
          simpl in H0. destruct H0 as [H0 | H0]; auto.
Qed.

Lemma inGetBlockLocs__lookupTypViaIDFromFdef: forall f id1 b,
  In id1 (getStmtsLocs (snd b)) ->
  blockInFdefB b f = true ->
  exists t, lookupTypViaIDFromFdef f id1 = Some t.
Proof.
  destruct f as [[fa ty fid la va] bs]. simpl. intros.
  destruct (lookupTypViaIDFromArgs la id1); eauto.
  induction bs as [|a bs]; simpl in *; intros.
    congruence.

    remember (lookupTypViaIDFromBlock a id1) as R.
    destruct R; eauto.
    apply orb_true_iff in H0.
    destruct H0 as [H0 | H0]; eauto.
      apply blockEqB_inv in H0. subst.
      symmetry in HeqR.
      apply lookupTypViaIDFromBlock__notInBlock in HeqR.
      contradict H; auto.
Qed.

Lemma in_getPhiNodesIDs_inv: forall id1 p,
  In id1 (getPhiNodesIDs p) ->
  exists ps1 : list phinode,
    exists p1 : phinode,
      exists ps2 : list phinode,
        p = ps1 ++ p1 :: ps2 /\ getPhiNodeID p1 = id1.
Proof.
  induction p; simpl; intros.
    inv H.

    destruct H as [H | H]; subst.
      exists nil. exists a. exists p. simpl. split; auto.

      apply IHp in H.
      destruct H as [ps1 [p1 [ps2 [J1 J2]]]]; subst.
      exists (a::ps1). exists p1. exists ps2. split; auto.
Qed.

Lemma in_getCmdsLocs_inv: forall id1 cs,
  In id1 (getCmdsLocs cs) ->
  exists cs1, exists c, exists cs2,
        cs = cs1 ++ c :: cs2 /\ getCmdLoc c = id1.
Proof.
  induction cs; simpl; intros.
    inv H.

    destruct H as [H | H]; subst.
      exists nil. exists a. exists cs. auto.

      apply IHcs in H.
      destruct H as [cs1 [c [cs2 [J1 J2]]]]; subst.
      exists (a::cs1). exists c. exists cs2. auto.
Qed.

Lemma IngetPhiNodesIDs__lookupPhiNodeViaIDFromPhiNodes: forall id2 ps1
  (H0 : In id2 (getPhiNodesIDs ps1)),
  exists p2, lookupPhiNodeViaIDFromPhiNodes ps1 id2 = Some p2 /\
             getPhiNodeID p2 = id2.
Proof.
  induction ps1; simpl; intros.
    inv H0.

    destruct H0 as [H0 | H0]; subst.
      destruct (getPhiNodeID a == getPhiNodeID a); eauto.
        congruence.

      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getPhiNodeID a)
                 id2); subst; eauto.
Qed.

Lemma lookupInsnViaIDFromBlocks__In : forall id0 instr bs,
  lookupInsnViaIDFromBlocks bs id0 = Some instr ->
  In id0 (getBlocksLocs bs).
Proof.
  induction bs; simpl; intros.
    inv H.

    apply in_or_app.
    remember (lookupInsnViaIDFromBlock a id0) as R.
    destruct R; eauto.
      inv H.
      symmetry in HeqR.
      apply lookupInsnViaIDFromBlock__In in HeqR; auto.
Qed.

Lemma IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef: forall id2 l1 ps1 cs1 tmn1 f
  (Huniq: uniqFdef f)
  (H : blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true)
  (H0 : In id2 (getPhiNodesIDs ps1)),
  exists p2, lookupInsnViaIDFromFdef f id2 = Some (insn_phinode p2) /\
             getPhiNodeID p2 = id2.
Proof.
  destruct f as [[] bs]. simpl. intros.
  destruct Huniq as [_ Huniq].
  apply NoDup_split in Huniq.
  destruct Huniq as [_ Huniq].
  generalize dependent l1.
  generalize dependent ps1.
  generalize dependent cs1.
  generalize dependent tmn1.
  generalize dependent id2.
  induction bs; simpl; intros.
    congruence.

    apply orb_true_iff in H.
    destruct H as [H | H].
      apply blockEqB_inv in H.
      subst. simpl.
      apply IngetPhiNodesIDs__lookupPhiNodeViaIDFromPhiNodes in H0.
      destruct H0 as [ps [H0 Heq]]; subst.
      rewrite H0. eauto.

      simpl_env in Huniq. rewrite getBlocksLocs_app in Huniq.
      assert (Huniq':=Huniq).
      apply NoDup_split in Huniq'. destruct Huniq'.
      eapply IHbs in H; eauto.
      destruct H as [p2 [H Heq]]; subst.
      rewrite H.
      apply lookupInsnViaIDFromBlocks__In in H.
      eapply NoDup_disjoint in Huniq; eauto.
      simpl in Huniq. simpl_env in Huniq.
      apply notin__lookupInsnViaIDFromBlock_none in Huniq.
      rewrite Huniq. eauto.
Qed.

Lemma IngetArgsIDs__lookupCmdViaIDFromFdef: forall fa rt fid la va lb id0
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (H0 : In id0 (getArgsIDs la)),
  lookupInsnViaIDFromFdef (fdef_intro (fheader_intro fa rt fid la va) lb) id0
    = None.
Proof.
  simpl. intros.
  destruct Huniq as [_ Huniq].
  remember (lookupInsnViaIDFromBlocks lb id0) as R.
  destruct R; auto.
  eapply NoDup_disjoint' in Huniq; eauto.
  contradict Huniq.
  eapply lookupInsnViaIDFromBlocks__In; eauto.
Qed.

Lemma In_InPhiNodesB: forall p ps, In p ps -> InPhiNodesB p ps.
Proof.
  induction ps; simpl; intros.
    inv H.
    apply orb_true_iff.
    destruct H as [H | H]; subst.
      left. apply phinodeEqB_refl.
      right. apply IHps; auto.
Qed.

Lemma app_cons_is_larger: forall A cs3 cs2 (c:A),
  cs2 = cs3 ++ c :: cs2 -> False.
Proof.
  intros.
  assert (J:=app_length cs3 (c::cs2)).
  rewrite <- H in J.
  simpl in J. omega.
Qed.

Lemma app_inv_tail_nil : forall A (l1 l2:list A),
  l1 ++ l2 = l2 -> l1 = nil.
Proof.
  intros.
  change l2 with (nil ++ l2) in H at 2.
  apply app_inv_tail in H; auto.
Qed.

Lemma InPhiNodesB_In: forall p ps, InPhiNodesB p ps -> In p ps.
Proof.
  induction ps; simpl; intros.
    inv H.
    apply orb_true_iff in H.
    destruct H as [H | H]; subst.
      apply phinodeEqB_inv in H. subst. auto.
      right. apply IHps; auto.
Qed.

Lemma nth_list_sz_value__valueInListValue: forall nth idxs sz0 v0,
  nth_error idxs nth = Some (sz0, v0) ->
  valueInListValue v0 idxs.
Proof.
  induction nth; simpl; intros.
    destruct idxs; inv H.
    unfold valueInListValue. simpl. auto.

    destruct idxs; inv H.
    apply IHnth in H1.
    unfold valueInListValue in *. simpl. auto.
Qed.

Lemma notin_getBlocksLocs__notin_getStmtsLocs : forall bs b i0,
  ~ In i0 (getBlocksLocs bs) ->
  InBlocksB b bs ->
  ~ In i0 (getStmtsLocs (snd b)).
Proof.
  intros. intro J. apply H.
  eapply in_getStmtsLocs__in_getBlocksLocs; eauto.
Qed.

Lemma lookupCmdViaIDFromFdef_spec : forall f id2 l1 ps1 cs1 tmn1
  (Huniq: uniqFdef f)
  (G : exists c2, lookupInsnViaIDFromFdef f id2 = Some (insn_cmd c2)),
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true ->
  In id2 (getPhiNodesIDs ps1 ++ getCmdsLocs cs1) ->
  In id2 (getCmdsLocs cs1).
Proof.
  intros.
  apply in_app_or in H0.
  destruct H0 as [H0 | H0]; auto.
  eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef in H; eauto.
  destruct H as [p2 [J1 J2]]; subst.
  destruct G as [c2 G].
  rewrite G in J1. inv J1.
Qed.

Lemma lookupPhiNodeViaIDFromPhiNodes__NotIn : forall id0 ps,
  lookupPhiNodeViaIDFromPhiNodes ps id0 = None ->
  ~ In id0 (getPhiNodesIDs ps).
Proof.
  induction ps; simpl; intros; auto.
    destruct (getPhiNodeID a == id0); tinv H.
      apply IHps in H. intro J. destruct J; subst; auto.
Qed.

Lemma lookupCmdViaIDFromCmds__NotIn : forall id0 cs,
  lookupCmdViaIDFromCmds cs id0 = None ->
  ~ In id0 (getCmdsLocs cs).
Proof.
  induction cs; simpl; intros; auto.
    destruct (eq_atom_dec id0 (getCmdLoc a)); subst; tinv H.
      apply IHcs in H. intro J. destruct J; subst; auto.
Qed.

Lemma lookupInsnViaIDFromBlock__NotIn : forall id0 b,
  lookupInsnViaIDFromBlock b id0 = None ->
  ~ In id0 (getStmtsLocs (snd b)).
Proof.
  destruct b as [? []]. simpl. intros.
  remember (lookupPhiNodeViaIDFromPhiNodes phinodes5 id0) as R.
  destruct R; tinv H.
  remember (lookupCmdViaIDFromCmds cmds5 id0) as R.
  destruct R; tinv H.
  destruct_if.
  symmetry in HeqR, HeqR0.
  apply lookupPhiNodeViaIDFromPhiNodes__NotIn in HeqR.
  apply lookupCmdViaIDFromCmds__NotIn in HeqR0.
  intro J.
  apply in_app_or in J. destruct J as [J | J]; auto.
  apply in_app_or in J. destruct J as [J | J]; auto.
  simpl in J. destruct J as [J | J]; auto.
Qed.

Lemma lookupCmdViaIDFromCmds__InCmds : forall cs c i0,
  lookupCmdViaIDFromCmds cs i0 = Some c ->
  In c cs.
Proof.
  induction cs; simpl; intros.
    inv H.
    destruct (eq_atom_dec i0 (getCmdLoc a)); eauto.
      inv H; auto.
Qed.

Lemma lookupInsnViaIDFromBlock__InCmds : forall l0 p cs t c1,
  NoDup (getStmtsLocs (stmts_intro p cs t)) ->
  lookupInsnViaIDFromBlock (l0, stmts_intro p cs t) (getCmdLoc c1) =
    Some (insn_cmd c1) ->
  In c1 cs.
Proof.
  intros. simpl in *.
  remember (lookupPhiNodeViaIDFromPhiNodes p (getCmdLoc c1)) as R.
  destruct R; tinv H0.
  remember (lookupCmdViaIDFromCmds cs (getCmdLoc c1)) as R.
  destruct R; inv H0.
    apply NoDup_split in H. destruct H as [_ H].
    apply NoDup_split in H. destruct H as [H _].
    eapply lookupCmdViaIDFromCmds__InCmds; eauto.

    destruct_if.
Qed.

Lemma lookupPhiNodeViaIDFromPhiNodes__InPhiNodes : forall ps p i0,
  lookupPhiNodeViaIDFromPhiNodes ps i0 = Some p ->
  In p ps.
Proof.
  induction ps; simpl; intros.
    inv H.
    destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) 
      (getPhiNodeID a) i0); inv H; eauto.
Qed.

Lemma InGetPhiNodesIDs_middle: forall ps1 p1 ps2,
  In (getPhiNodeID p1) (getPhiNodesIDs (ps1 ++ p1 :: ps2)).
Proof.
  intros.
  rewrite getPhiNodesIDs_app. apply in_or_app. simpl. auto.
Qed.

Lemma getPhiNodeID_in_getPhiNodesIDs : forall ps p,
  In p ps ->
  In (getPhiNodeID p) (getPhiNodesIDs ps).
Proof.
  induction ps; intros.
    inversion H.

    simpl in *.
    destruct H as [H | H]; subst; eauto.
Qed.

Ltac solve_NoDup_notin :=
match goal with
| Huniq: NoDup (getCmdsLocs (?cs2' ++ [?c'])) |-
  ~ In (getCmdLoc ?c') (getCmdsLocs ?cs2') =>
  rewrite getCmdsLocs_app in Huniq; simpl in Huniq;
  apply NoDup_last_inv in Huniq; auto
end.

Lemma InCmdsB_InCmdsLocs : forall c cs,
  InCmdsB c cs = true -> In (getCmdLoc c) (getCmdsLocs cs).
Proof. intros. apply In_InCmdLocs. apply InCmdsB_in; auto. Qed.

Lemma getCmdID_getCmdLoc: forall c
  (Hsome: getCmdID c <> None), getCmdID c = Some (getCmdLoc c).
Proof. 
  destruct c; simpl; intros; try solve [auto | congruence].
    destruct_if; try solve [auto | congruence].
Qed.

Lemma InGetCmdsIDs_middle': forall cs1 c1 cs2 id1 (Hid: getCmdID c1 = Some id1),
  In id1 (getCmdsIDs (cs1 ++ c1 :: cs2)).
Proof.
  intros.
  rewrite getCmdsIDs_app. apply in_or_app. right. simpl.
  fill_ctxhole. simpl. auto.
Qed.

Lemma InCmdsB_middle__eq: forall c b C (Heq: getCmdLoc c = getCmdLoc b) 
  A (Huniq: NoDup (getCmdsLocs (A++b::C)))
  (Hin: InCmdsB c (A ++ b :: C) = true), c = b.
Proof.
  induction A; simpl; intros.
    binvt Hin as Hin Hin.
      apply cmdEqB_inv in Hin; auto.

      apply InCmdsB_InCmdsLocs in Hin.
      inv Huniq. rewrite Heq in Hin. tauto.

    inv Huniq.
    binvt Hin as Hin Hin; auto. 
      apply cmdEqB_inv in Hin. subst.
      contradict H1. rewrite Heq. apply InGetCmdsLocs_middle.
Qed.

Lemma uniqFdef__blockInFdefB__nodup_cmds: forall l0 ps0 cs0 tmn0 f
  (H: uniqFdef f) (H0: blockInFdefB (l0, stmts_intro ps0 cs0 tmn0) f),
  NoDup (getCmdsLocs cs0).
Proof.
  intros.
  destruct f as [fh bs].
  apply blockInFdefB__In in H0.
  eapply uniqFdef__uniqBlock in H0; eauto.
Qed.

Lemma getCmdLoc__in__getCmdsIDs: forall (c : cmd) (cs : cmds)
  (Huniq: NoDup (getCmdsLocs cs))
  (Hsome : getCmdID c <> None) (H' : InCmdsB c cs = true),
  In (getCmdLoc c) (getCmdsIDs cs).
Proof.
  intros.
  assert (G:=H').
  apply InCmdsB_InCmdsLocs in H'.
  apply in_getCmdsLocs_inv in H'.
  destruct H' as [A [b [C [EQ1 EQ2]]]]; subst.
  apply InGetCmdsIDs_middle'.
  rewrite <- EQ2.
  apply InCmdsB_middle__eq in G; auto.
    subst. apply getCmdID_getCmdLoc; auto.
Qed.

Lemma uniqFdef__uniqArgsID: forall f (Huniq : uniqFdef f),
  NoDup (getArgsIDs (getArgsOfFdef f)).
Proof.
  destruct f as [[]]. simpl. intros.
  destruct Huniq. split_NoDup. auto.
Qed.

Ltac solve_NoDup :=
match goal with
| H1: uniqFdef ?F,
  H2: insnInFdefBlockB _ ?F (?l0, stmts_intro ?ps0 ?cs0 ?tmn0)  = true |-
  NoDup (getPhiNodesIDs ?ps0 ++ getCmdsLocs ?cs0 ++ getTerminatorID ?tmn0 :: nil)
  =>
  apply insnInFdefBlockB__blockInFdefB in H2;
  apply uniqFdef__uniqBlockLocs in H2; auto
| J1 : NoDup (getStmtsLocs (snd (_, stmts_intro ?ps1 _ _))) |- 
  NoDup (getPhiNodesIDs ?ps1) =>
  simpl in J1; apply NoDup_split in J1; destruct J1; auto
| H: uniqFdef ?f, H1: blockInFdefB (_, ?s) ?f = true |- NoDup (getStmtsLocs ?s) =>
  apply uniqFdef__uniqBlockLocs in H1; auto
| H: uniqFdef ?f, H1: blockInFdefB ?b ?f = true |- NoDup (getStmtsLocs (snd ?b)) =>
  apply uniqFdef__uniqBlockLocs in H1; auto
| H1: uniqFdef ?F,
  H2: blockInFdefB (?l0, stmts_intro ?ps0 ?cs0 ?tmn0) ?F = true |-
  NoDup (getCmdsLocs ?cs0) =>
  apply uniqFdef__uniqBlockLocs in H2; auto;
  simpl in H2; split_NoDup; auto
| Huniq: uniqFdef ?f |- NoDup (getArgsIDs (getArgsOfFdef ?f)) =>
    apply uniqFdef__uniqArgsID; auto
end.

Lemma getCmdLoc__in__getStmtsIDs: forall c f b
  (Hsome : getCmdID c <> None) (Huniq : uniqFdef f)
  (HbInF : blockInFdefB b f = true) (HcInB : cmdInBlockB c b = true),
  In (getCmdLoc c) (getStmtsIDs (snd b)).
Proof.
  intros.
  destruct b as [l1 [ps1 cs1 tmn1]].
  simpl in *.
  apply getCmdLoc__in__getCmdsIDs in HcInB; auto.
    apply in_or_app. auto.
    solve_NoDup.
Qed.

Lemma In_InProductsB: forall p ps, In p ps -> InProductsB p ps = true.
Proof.
  induction ps; intros.
    tauto.

    simpl. apply orb_true_intro.
    destruct_in H.
      left. solve_refl.
Qed.

Lemma InProductsB_In: forall p ps, InProductsB p ps = true -> In p ps.
Proof.
  induction ps; simpl; intros.
    congruence.

    apply orb_true_elim in H.
    destruct H as [H | H]; auto.
      apply productEqB_inv in H. auto.
Qed.

Lemma In_InModulesB: forall m ms, In m ms -> InModulesB m ms = true.
Proof.
  induction ms; intros.
    tauto.

    simpl. apply orb_true_intro.
    destruct_in H.
      left. solve_refl.
Qed.

Lemma InModulesB_In: forall m ms, InModulesB m ms = true -> In m ms.
Proof.
  induction ms; simpl; intros.
    congruence.

    apply orb_true_elim in H.
    destruct H as [H | H]; auto.
      apply moduleEqB_inv in H. auto.
Qed.

Lemma moduleInSystem_middle: forall Ms2 M Ms1,
  moduleInSystem M (Ms1 ++ M :: Ms2).
Proof.
  intros. apply In_InModulesB. apply in_middle.
Qed.

Lemma InProductsB_middle: forall Ps2 P Ps1,
  InProductsB P (Ps1 ++ P :: Ps2) = true.
Proof.
  induction Ps1; simpl.
    rewrite productEqB_refl. auto.
    rewrite IHPs1. apply orb_true_intro; auto.
Qed.  

Ltac solve_in_list :=
unfold is_true in *;
repeat match goal with
| H1: InBlocksB ?b ?bs = true |- In ?b ?bs => apply InBlocksB_In; auto
| H1: In ?b ?bs |- InBlocksB ?b ?bs = true => apply In_InBlocksB; auto
| H1: In ?p ?ps |- InProductsB ?p ?ps = true => apply In_InProductsB; auto
| H1: InProductsB ?p ?ps = true |- In ?p ?ps => apply InProductsB_In; auto
| H1: In ?m ?ms |- InModulesB ?m ?ms = true => apply In_InModulesB; auto
| H1: InModulesB ?m ?ms = true |- In ?m ?ms => apply InModulesB_In; auto
| |- moduleInSystem ?M (_++?M::_) => apply moduleInSystem_middle
| |- InProductsB ?p (_++?p::_) => apply InProductsB_middle
| H1: ~ In ?id0 (?A ++ ?C) |- ~ In ?id0 ?A => intro Q; apply H1
| H1: ~ In ?id0 (?A ++ ?C) |- ~ In ?id0 ?C => intro Q; apply H1
| H1: In ?id0 ?B |- In ?id0 (?A ++ ?B ++ ?C) =>
    apply in_or_app; right
| H1: In ?id0 ?A |- In ?id0 (?A ++ ?C) =>
    apply in_or_app; auto
| H1: In ?id0 ?C |- In ?id0 (?A ++ ?C) =>
    apply in_or_app; auto
| H1: In ?id0 (?A ++ ?B) |- In ?id0 (?A ++ ?C) =>
    apply in_app_or in H1;
    apply in_or_app;
    destruct H1 as [H1 | H1]; auto;
    right
| H1: In ?id0 (?A ++ ?B) |- In ?id0 (?C ++ ?B) =>
    apply in_app_or in H1;
    apply in_or_app;
    destruct H1 as [H1 | H1]; auto;
    left
| H1: In ?id0 (getStmtsIDs ?b) |- In ?id0 (getStmtsLocs ?b) =>
    apply in_getStmtsIDs__in_getStmtsLocs; auto
| H1: In ?id0 (getCmdsIDs ?b) |- In ?id0 (getCmdsLocs ?b) =>
    apply in_getCmdsIDs__in_getCmdsLocs; auto
| H1: In ?id0 (getStmtsIDs ?b) |- In ?id0 (getStmtsLocs ?b ++ _) =>
    apply in_or_app; left; apply in_getStmtsIDs__in_getStmtsLocs; auto
| H1: In ?id0 (getCmdsIDs ?b) |- In ?id0 (getCmdsLocs ?b ++ _) =>
    apply in_or_app; left; apply in_getCmdsIDs__in_getCmdsLocs; auto
| H1: In ?c ?cs |- In (getCmdLoc ?c) (getCmdsLocs ?cs) =>
    apply getCmdLoc_in_getCmdsLocs; auto
| H1: InCmdsB ?c ?cs = true |- In ?c ?cs => apply InCmdsB_in; auto
| H1: cmdInBlockB ?c (_, stmts_intro _ ?cs _) = true |- In ?c ?cs => 
    simpl in H1; apply InCmdsB_in; auto
| H1: In ?c ?cs |- InCmdsB ?c ?cs = true => apply In_InCmdsB; auto
| H1: In ?id0 (?A ++ ?B), H2: ~ In ?id0 ?B |- In ?id0 ?A =>
    apply in_app_or in H1; destruct H1; try solve [auto | tauto]
| H1: In ?id0 (?A ++ ?B), H2: ~ In ?id0 ?A |- In ?id0 ?B =>
    apply in_app_or in H1; destruct H1; try solve [auto | tauto]
| |- In ?a (?A ++ ?B ++ ?a :: nil) =>
    apply in_or_app; right; apply in_or_app; simpl; auto 
| |- In ?a (_ ++ _::_ ++ ?a::_) =>
    apply in_or_app; right; simpl; right; apply in_middle
| |- InCmdsB ?a (_ ++ _::_ ++ ?a::_) = true => apply In_InCmdsB
| |- In ?a (_ ++ ?a::_) => apply in_middle
| |- InCmdsB ?a (_ ++ ?a::_) = true => apply In_InCmdsB
| H1: cmdInBlockB ?c (_, stmts_intro _ ?cs _) = true |- 
  In (getCmdLoc ?c) (getCmdsLocs ?cs) =>
    simpl in H1; apply getCmdLoc_in_getCmdsLocs; auto
| |- cmdInBlockB ?a (_, stmts_intro _ (_ ++ _::_ ++ ?a::_) _ ) = true => simpl
| |- cmdInBlockB ?a (_, stmts_intro _ (_ ++ ?a::_ ++ ?a::_) _ ) = true  => simpl
| |- cmdInBlockB ?a (_, stmts_intro _ (_ ++ ?a::_) _ ) = true  => simpl
| H: lookupBlockViaIDFromFdef _ ?id0 = Some (_, ?s0) |- In ?id0 (getStmtsIDs ?s0) =>
    apply lookupBlockViaIDFromFdef__InGetBlockIDs in H
| H: lookupBlockViaIDFromFdef _ ?id0 = Some ?b |- In ?id0 (getStmtsIDs (snd ?b)) =>
    apply lookupBlockViaIDFromFdef__InGetBlockIDs in H
| H: lookupBlockViaIDFromFdef _ ?id0 = Some (_, ?s0) |- In ?id0 (getStmtsLocs ?s0) =>
    apply lookupBlockViaIDFromFdef__InGetBlockIDs in H;
    apply in_getStmtsIDs__in_getStmtsLocs; auto
| H: lookupBlockViaIDFromFdef _ ?id0 = Some ?b |- In ?id0 (getStmtsLocs (snd ?b)) =>
    apply lookupBlockViaIDFromFdef__InGetBlockIDs in H;
    apply in_getStmtsIDs__in_getStmtsLocs; auto
| H1: In ?p ?ps |- InPhiNodesB ?p ?ps = true => apply In_InPhiNodesB; auto
| H1: InPhiNodesB ?p ?ps = true |- In ?p ?ps => apply InPhiNodesB_In; auto
| H1: InPhiNodesB ?p ?ps = true |- InPhiNodesB ?p (_++?ps) = true => 
    apply In_InPhiNodesB
| H1: InPhiNodesB ?p ?ps = true |- InPhiNodesB ?p (?ps++_) = true => 
    apply In_InPhiNodesB
| H1: lookupPhiNodeViaIDFromPhiNodes ?ps _ = Some ?p |- In ?p ?ps =>
    apply lookupPhiNodeViaIDFromPhiNodes__InPhiNodes in H1; auto
| H1: lookupPhiNodeViaIDFromPhiNodes ?ps _ = Some ?p |- 
    InPhiNodesB ?p ?ps = true =>
    apply In_InPhiNodesB; 
    apply lookupPhiNodeViaIDFromPhiNodes__InPhiNodes in H1; auto
| H1: In ?a (getPhiNodesIDs ?ps) |- In ?a (getStmtsLocs (stmts_intro ?ps _ _)) =>
    simpl; apply in_or_app; auto
| H1: In ?a (getPhiNodesIDs ?ps) |- 
  In ?a (getStmtsLocs (snd (_, stmts_intro ?ps _ _))) =>
    simpl; apply in_or_app; auto
| HBinF : InBlocksB ?b ?bs = true, Hin : In ?i1 (getStmtsLocs (snd ?b)) |-
  In ?i1 (getBlocksLocs ?bs) =>
  eapply in_getStmtsLocs__in_getBlocksLocs in HBinF; eauto
| HBinF : InBlocksB ?b ?bs, Hin : In ?i1 (getStmtsLocs (snd ?b)) |-
  In ?i1 (getBlocksLocs ?bs) =>
  eapply in_getStmtsLocs__in_getBlocksLocs in HBinF; eauto
| HBinF : blockInFdefB ?b (fdef_intro _ ?bs) = true, 
  Hin : In ?i1 (getStmtsLocs (snd ?b)) |-
  In ?i1 (getBlocksLocs ?bs) =>
  simpl in HBinF; eapply in_getStmtsLocs__in_getBlocksLocs in HBinF; eauto
| H1: In ?id0 ?C |- In ?id0 (?A ++ ?B ++ ?C) =>
    apply in_or_app; right; apply in_or_app; right; auto
| |- In (getPhiNodeID ?p1) (getPhiNodesIDs (_ ++ ?p1 :: _)) =>
  apply InGetPhiNodesIDs_middle; auto
| |- In (getPhiNodeID ?p1) (getPhiNodesIDs (_ ++ ?p1 :: _) ++ _) =>
  apply in_or_app; left; apply InGetPhiNodesIDs_middle; auto
| H : insnInBlockB (insn_cmd ?c) (_, stmts_intro _ ?cs _) = true |- In ?c ?cs =>
  simpl in H
| H : In ?c ?cs |- cmdInBlockB ?c (_, stmts_intro _ ?cs _) => 
  simpl; apply In_InCmdsB; auto
| |- InPhiNodesB ?p (_++?p::_) = true => apply In_InPhiNodesB
| H : In ?p ?ps |- In (getPhiNodeID ?p) (getPhiNodesIDs ?ps) =>
  apply getPhiNodeID_in_getPhiNodesIDs; auto
| H : InPhiNodesB ?p ?ps = true |- In (getPhiNodeID ?p) (getPhiNodesIDs ?ps) =>
  apply InPhiNodesB_In in H; apply getPhiNodeID_in_getPhiNodesIDs; auto
| H: In ?p ?ps |- 
  In (getPhiNodeID ?p) (getStmtsLocs (snd (_, stmts_intro ?ps1 _ _))) =>
  simpl; apply in_or_app; left
| |- In (getCmdLoc ?c) (getCmdsLocs (_++[?c])) =>
    apply getCmdLoc_in_getCmdsLocs; apply in_or_app; right
| |- In ?c [?c] => simpl; auto
| |- In (getCmdLoc ?c) (getCmdsLocs (_++?c::_)) =>
    apply InGetCmdsLocs_middle; auto
| |- In (getCmdLoc ?c) (getCmdsLocs (_++_::?c::_)) =>
    apply getCmdLoc_in_getCmdsLocs; apply in_or_app; right; simpl; auto
| HBinF : InBlocksB ?b ?bs, Hin : In ?i1 (getStmtsIDs (snd ?b)) |-
  In ?i1 (getBlocksLocs ?bs) =>
  apply in_getStmtsIDs__in_getStmtsLocs in Hin
| HBinF : blockInFdefB ?b (fdef_intro _ ?bs), 
  Hin : In ?i1 (getStmtsIDs (snd ?b)) |-
  In ?i1 (getBlocksLocs ?bs) =>
  apply in_getStmtsIDs__in_getStmtsLocs in Hin
| G : InPhiNodesB ?p ?ps = true |- 
  In (getPhiNodeID ?p) (getPhiNodesIDs ?ps ++ _) =>
  apply in_or_app; left
| Huniq: NoDup (getCmdsLocs ?cs), Hsome : getCmdID ?c <> None, 
  H': InCmdsB ?c ?cs = true |- In (getCmdLoc ?c) (getCmdsIDs ?cs) =>
  apply getCmdLoc__in__getCmdsIDs; auto
| Hid: getCmdID ?c1 = Some ?id1 |- In ?id1 (getCmdsIDs (?cs1 ++ ?c1 :: ?cs2)) =>
  apply InGetCmdsIDs_middle'; auto
| H: cmdInBlockB ?c (_, stmts_intro _ ?cs _) = true |-
  In (getCmdLoc ?c) (getCmdsLocs ?cs ++ _) =>
  simpl in H; apply in_or_app; left
| J12 : In ?id2 (?A ++ _), n : ~ In ?id2 ?A |- _ =>
  apply in_app_or in J12;
  destruct J12 as [J12 | J12]; try solve [contradict J12; auto]
| H : InCmdsB ?c ?cs = true |- In (getCmdLoc ?c) (getCmdsLocs ?cs ++ _) =>
  apply in_or_app; left
| H : InCmdsB ?c ?cs = true |- In (getCmdLoc ?c) (getCmdsLocs ?cs) =>
  apply getCmdLoc_in_getCmdsLocs
| |- In (getCmdLoc ?c) (getCmdsLocs (_ ++ ?c :: _) ++ _) =>
  apply in_or_app; left
| H1: In ?a (?A ++ ?B ++ ?C), H2: ~ In ?a ?C |- _ =>
  rewrite_env ((A++B)++C) in H1
| H1: In ?a (?A ++ ?B), H2: ~ In ?a ?B |- _ =>
  apply in_app_or in H1; 
  destruct H1 as [H1 | H1]; try solve [contradict H1; auto]
| Hsome : getCmdID ?c <> None, Huniq : uniqFdef ?f,
  HbInF : blockInFdefB ?b ?f = true, HcInB : cmdInBlockB ?c ?b = true |-
  In (getCmdLoc ?c) (getStmtsIDs (snd ?b)) =>
  eapply getCmdLoc__in__getStmtsIDs in HbInF; eauto
| |- In (getCmdLoc ?c) (getCmdsLocs (_ ++ ?c :: _ ++ _ :: _)) =>
  apply getCmdLoc_in_getCmdsLocs
| |- In (getCmdLoc ?c) (getCmdsLocs (_ ++ _ :: _ ++ ?c :: _)) =>
  apply getCmdLoc_in_getCmdsLocs
| |- In (getCmdLoc ?c) (getCmdsLocs (_ ++ _ :: _ ++ ?c :: _) ++ _) =>
  apply in_or_app; left
| |- In (getCmdLoc ?c) (_ ++ getCmdsLocs (_ ++ _ :: _ ++ ?c :: _) ++ _) =>
  apply in_or_app; right; apply in_or_app; left
| |- In ?id1 (getPhiNodesIDs (_ ++ insn_phi ?id1 _ _ :: _) ++ _) =>
  simpl; apply in_or_app; left; rewrite getPhiNodesIDs_app; simpl
| |- InCmdsB ?c (?A ++ [?c]) = true => 
  apply In_InCmdsB; rewrite_env (A++c::nil)
| |- InCmdsB ?c (?A ++ [?c] ++ ?B ) = true =>
  apply In_InCmdsB; rewrite_env (A++c::B)
| |- InPhiNodesB ?a (?a::_) = true => simpl; apply orb_true_iff; left; solve_refl
| |- InCmdsB ?a (?a::_) = true => simpl; apply orb_true_iff; left; solve_refl
| Heq : nil = _ ++ _ :: _ |- _ =>
    symmetry in Heq; contradict Heq; apply app_cons_not_nil; auto
| Heq : _ ++ _ :: _ = nil |- _ =>
    contradict Heq; apply app_cons_not_nil; auto
end.

Lemma lookupBlockViaIDFromBlocks__in_getBlocksLocs: forall b1 id1 bs,
  lookupBlockViaIDFromBlocks bs id1 = Some b1 ->
  In id1 (getBlocksLocs bs).
Proof.
  induction bs; simpl; intros.
    inv H.
    
    destruct_if.
      solve_in_list.
      apply IHbs in H1. solve_in_list.
Qed.

Lemma lookupInsnViaIDFromFdef_lookupBlockViaIDFromFdef_In:
  forall F (Huniq: uniqFdef F) c1 l0 p cs t
  (J2 : lookupInsnViaIDFromFdef F (getCmdLoc c1) = Some (insn_cmd c1))
  (Hlkb : lookupBlockViaIDFromFdef F (getCmdLoc c1) =
    Some (l0, stmts_intro p cs t)),
  In c1 cs.
Proof.
  destruct F as [[fa ty fid la va] bs]. simpl. 
  intros [J1 J2].
  apply NoDup_split in J2. destruct J2 as [_ J2].
  induction bs as [|a bs]; simpl; intros.
    congruence.

    simpl_env in J1. apply uniqBlocks_inv in J1. destruct J1.
    simpl_env in J2. rewrite getBlocksLocs_app in J2. 
    remember (lookupInsnViaIDFromBlock a (getCmdLoc c1)) as R.
    destruct R.
      inv J0.
      symmetry in HeqR. assert (HeqR':=HeqR).
      apply lookupInsnViaIDFromBlock__In in HeqR.
      destruct (in_dec eq_dec (getCmdLoc c1) (getStmtsIDs (snd a))).
        inv Hlkb.
        unfold uniqBlocks in H. simpl in H. 
        destruct H as [H1 H2]. simpl_env in H2.
        apply lookupInsnViaIDFromBlock__InCmds in HeqR'; simpl; auto.

        simpl in J2. simpl_env in J2.
        apply NoDup_disjoint' with (i0:=getCmdLoc c1) in J2; auto.
        apply lookupBlockViaIDFromBlocks__in_getBlocksLocs in Hlkb.
        tauto.

      symmetry in HeqR.
      apply lookupInsnViaIDFromBlock__NotIn in HeqR.
      destruct (in_dec eq_dec (getCmdLoc c1) (getStmtsIDs (snd a))).
        apply in_getStmtsIDs__in_getStmtsLocs in i0.
        contradict i0; auto.

        apply NoDup_split in J2. destruct J2.
        apply IHbs in Hlkb; auto.
Qed.

Lemma phinode_isnt_cmd : forall f l3 ps cs tmn id1 c1,
  uniqFdef f ->
  Some (stmts_intro ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  In id1 (getPhiNodesIDs ps) ->
  lookupInsnViaIDFromFdef f id1 = Some (insn_cmd c1) ->
  False.
Proof.
  intros. symmetry in H0.
  apply lookupBlockViaLabelFromFdef__blockInFdefB in H0; auto.
  eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef in H0; eauto.
  destruct H0 as [p2 [J1 J2]]; subst.
  rewrite H2 in J1. inv J1.
Qed.

Lemma destruct_insnInFdefBlockB : forall instr f b,
  insnInFdefBlockB instr f b = true ->
  insnInBlockB instr b = true /\ blockInFdefB b f = true.
Proof.
  intros.
  split.
    eapply insnInFdefBlockB__insnInBlockB; eauto.
    eapply insnInFdefBlockB__blockInFdefB; eauto.
Qed.

Lemma insnInFdefBlockB_intro: forall (instr : insn) (f : fdef) (b : block),
  insnInBlockB instr b = true -> blockInFdefB b f = true ->
  insnInFdefBlockB instr f b = true.
Proof. destruct instr; simpl; intros; apply andb_true_iff; auto. Qed.

Lemma lookupInsnViaIDFromFdef__insnInFdefBlockB : forall F id1 instr1,
  lookupInsnViaIDFromFdef F id1 = Some instr1 ->
  exists b1, insnInFdefBlockB instr1 F b1.
Proof.
  destruct F as [fh bs]. simpl.
  induction bs as [|a bs]; simpl; intros.
    inv H.

    remember (lookupInsnViaIDFromBlock a id1) as R.
    destruct R.
      inv H.
      exists a.
      destruct a as [l0 [p c t]]. simpl in *.
      assert (blockInFdefB (l0, stmts_intro p c t)
         (fdef_intro fh ((l0, stmts_intro p c t) :: bs)) = true) as HBinF.
        apply orb_true_iff. left. apply blockEqB_refl.

      remember (lookupPhiNodeViaIDFromPhiNodes p id1) as R.
      destruct R; inv HeqR.
        symmetry in HeqR0.
        apply lookupPhiNodeViaIDFromPhiNodes__InPhiNodes in HeqR0.
        apply andb_true_iff.
        split; auto.
          simpl. solve_in_list.
          
      remember (lookupCmdViaIDFromCmds c id1) as R.
      destruct R; inv H0.
        symmetry in HeqR.
        apply lookupCmdViaIDFromCmds__InCmds in HeqR.
        apply andb_true_iff. split; auto. simpl. solve_in_list.

        destruct_if.
        simpl. 
        apply andb_true_iff. split; auto. 
        apply terminatorEqB_refl.

      apply IHbs in H.
      destruct H as [b H].
      apply destruct_insnInFdefBlockB in H. destruct H as [J1 J2].
      exists b. 
      apply insnInFdefBlockB_intro; auto. 
      simpl. apply orb_true_iff; auto.
Qed.

Lemma in_getPhiNodeID__in_getPhiNodesIDs : forall p ps,
  In p ps -> In (getPhiNodeID p) (getPhiNodesIDs ps).
Proof.
  induction ps; simpl; intros; auto.
    destruct H as [H | H]; subst; auto.
Qed.

Lemma getValueViaLabelFromValuels__in_unmake_list_value_l: forall l1 v0 vls
  l2 l3,
  getValueViaLabelFromValuels vls l1 = Some v0 ->
  (l2, l3) = split vls ->
  In l1 l3.
Proof.
  induction vls; simpl; intros.
    congruence.

    destruct a as [v l0].
    destruct (split vls).
    inv H0.
    simpl.
    destruct (l0 == l1); eauto.
Qed.

Lemma In_list_prj1__getValueViaLabelFromValuels: forall vls v,
  (let '(_, ls1) := split vls in NoDup ls1) ->
  In v (list_prj1 value l vls) ->
  exists l1, getValueViaLabelFromValuels vls l1 = Some v.
Proof.
  induction vls; intros; simpl in *.
    inv H0.

    destruct a as [v0 l0].
    destruct H0 as [H0 | H0]; subst.
      exists l0.
      destruct (l0 == l0); subst; try congruence; auto.

      apply IHvls in H0.
        destruct H0 as [l1 H0].
        exists l1. rewrite H0.
        remember (split vls) as R.
        destruct R.
        eapply getValueViaLabelFromValuels__in_unmake_list_value_l in H0; eauto.
        inv H.
        destruct (l0 == l1); auto.
          subst. contradict H0; auto.

        destruct (split vls).
        inv H; auto.
Qed.

Lemma getValueViaLabelFromValuels__In_list_prj1 :
  forall vls v l1,
  getValueViaLabelFromValuels vls l1 = Some v ->
  In v (list_prj1 value l vls).
Proof.
  induction vls; intros; simpl in *.
    congruence.

    destruct a as [v0 l0].
    destruct (l0 == l1); simpl in *; subst; eauto.
      inv H. auto.
Qed.

Lemma head_tail_commut: forall A (a:A) cs,
  exists cs', exists a', [a] ++ cs = cs' ++ [a'].
Proof.
  induction cs.
    exists nil. exists a. auto.

    destruct IHcs as [cs' [a' IHcs]].
    destruct cs'.
      inv IHcs.
      exists [a']. exists a0. auto.

      inv IHcs.
      exists ([a1]++a0::cs'). exists a'. auto.
Qed.

Lemma NoDup_cmds_split_middle: forall cs2 cs2' c cs1 cs1',
  NoDup (getCmdsLocs (cs1 ++ c :: cs2)) ->
  cs1 ++ c :: cs2 = cs1' ++ c :: cs2' ->
  cs1 = cs1' /\ cs2 = cs2'.
Proof.
  induction cs1; destruct cs1'; simpl; intros.
    inv H0. auto.

    inv H0.
    inv H.
    contradict H2.
    rewrite getCmdsLocs_app. simpl. apply in_middle.

    inv H0.
    inv H.
    contradict H2.
    rewrite getCmdsLocs_app. simpl. apply in_middle.

    inv H0.
    inv H.
    eapply IHcs1 in H4; eauto.
    destruct H4 as [J1 J2]; subst; auto.
Qed.

Lemma lookupFdefViaIDFromProducts__InProductsB: forall i1 f1 Ps1,
  lookupFdefViaIDFromProducts Ps1 i1 = Some f1 ->
  InProductsB (product_fdef f1) Ps1 = true.
Proof.
  induction Ps1 as [|[]]; simpl; intros; try solve [
    congruence |
    rewrite productNEqB_intro; try congruence; rewrite IHPs1; auto
    ].
    
    destruct_if.
      rewrite productEqB_refl. auto.
      rewrite IHPs1; auto. apply orb_true_r.
Qed.

Lemma lookupFdefViaIDFromSystem_ideq : forall S fid f,
  lookupFdefViaIDFromSystem S fid = Some f -> fid = getFdefID f.
Proof.
  induction S as [|[]]; simpl; intros.
    congruence.

    destruct f as [[]].
    destruct_match; eauto using lookupFdefViaIDFromProducts_ideq.
Qed.

Lemma lookupFdefViaIDFromProducts__notin_getFdefsIDs: forall fid Ps,
  lookupFdefViaIDFromProducts Ps fid = None -> 
  ~ In fid (getFdefsIDs Ps).
Proof.
  induction Ps as [|[]]; simpl; intros; auto.
    destruct_if.
      apply IHPs in H1. 
      intro J.
      destruct J; auto.
Qed.

Lemma lookupFdefViaIDFromProducts__in_getFdefsIDs: forall fid f Ps,
  lookupFdefViaIDFromProducts Ps fid = Some f -> 
  In fid (getFdefsIDs Ps).
Proof.
  induction Ps as [|[]]; simpl; intros; auto.
    congruence.

    destruct_if; auto.
Qed.

Lemma InProductsB__in_getFdefsIDs: forall f Ps,
  InProductsB (product_fdef f) Ps = true -> 
  In (getFdefID f) (getFdefsIDs Ps).
Proof.
  induction Ps as [|[]]; simpl; intros.
    congruence.

    rewrite productNEqB_intro in H; try congruence;
    rewrite orb_false_l in H; auto.

    rewrite productNEqB_intro in H; try congruence;
    rewrite orb_false_l in H; auto.

    apply orb_true_iff in H.
    destruct H; auto.
      apply productEqB_inv in H. inv H. auto.
Qed.

Lemma getParentOfFdefFromSystem__moduleInProductsInSystemB: 
  forall f los1 nts1 Ps1 S1, 
  getParentOfFdefFromSystem f S1 = Some (module_intro los1 nts1 Ps1) ->
  moduleInSystemB (module_intro los1 nts1 Ps1) S1 = true /\
  InProductsB (product_fdef f) Ps1 = true.
Proof.
  induction S1; simpl; intros.
    congruence.

    destruct_if; simpl in e. 
      rewrite moduleEqB_refl. tauto.

      apply IHS1 in H1. destruct H1 as [J1 J2].
      rewrite J1. rewrite orb_true_r.
      tauto.
Qed.

Lemma getValueViaBlockFromValuels__eql : forall B1 B2 vls,
  getBlockLabel B1 = getBlockLabel B2 ->
  getValueViaBlockFromValuels vls B1 = getValueViaBlockFromValuels vls B2.
Proof.
  intros.
  destruct B1. destruct B2. simpl in H. subst. simpl. auto.
Qed.

Lemma lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef :
  forall F l1 s1 id1 (Huniq: uniqFdef F)
  (J2 : lookupBlockViaLabelFromFdef F l1 = Some s1)
  (J3 : In id1 (getStmtsIDs s1)),
  lookupBlockViaIDFromFdef F id1 = Some (l1, s1).
Proof.
  intros.
  apply lookupBlockViaLabelFromFdef_inv in J2; auto.
  apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
Qed.

Lemma lookupBlockViaIDFromFdef_getStmtsLocs_getStmtsIDs: forall F i0 block1
  block2 (Huniq : uniqFdef F) (HBinF: blockInFdefB block1 F = true)
  (HeqR1' : In i0 (getStmtsLocs (snd block1)))
  (H5 : lookupBlockViaIDFromFdef F i0 = Some block2),
  In i0 (getStmtsIDs (snd block1)).
Proof.
  destruct F as [[fa ty fid la va] bs]. simpl.
  intros i0 block1 block2 [Huniq1 Huniq2].
  apply NoDup_split in Huniq2. destruct Huniq2 as [_ Huniq2].
  induction bs; simpl; intros.
    congruence.

    destruct (in_dec eq_dec i0 (getStmtsIDs (snd a))).
      inv H5.
      apply orb_true_iff in HBinF.
      destruct HBinF as [HBinF | HBinF].
        apply blockEqB_inv in HBinF. subst. auto.

        unfold uniqBlocks in Huniq1.
        destruct Huniq1 as [_ Huniq1].
        simpl in Huniq1.
        eapply in_getStmtsLocs__in_getBlocksLocs in HBinF; eauto.
        apply NoDup_disjoint with (i0:=i0) in Huniq1; auto.
          contradict Huniq1.
          apply in_getStmtsIDs__in_getStmtsLocs; auto.

      apply orb_true_iff in HBinF.
      destruct HBinF as [HBinF | HBinF].
        apply blockEqB_inv in HBinF. subst.
        unfold uniqBlocks in Huniq1.
        destruct Huniq1 as [_ Huniq1].
        simpl in Huniq1.
        apply NoDup_disjoint' with (i0:=i0) in Huniq1; auto.
        contradict Huniq1.
        assert (lookupBlockViaIDFromFdef 
                 (fdef_intro (fheader_intro fa ty fid la va) bs) i0 = 
                   Some block2) as J.
          simpl. auto.
        assert (J1:=J).
        apply lookupBlockViaIDFromFdef__blockInFdefB in J1.
        apply in_getStmtsLocs__in_getBlocksLocs with (b:=block2); auto.
        apply in_getStmtsIDs__in_getStmtsLocs; auto.
        apply lookupBlockViaIDFromFdef__InGetBlockIDs in J; auto.

        simpl_env in Huniq1. apply uniqBlocks_inv in Huniq1. destruct Huniq1. 
        simpl in Huniq2. apply NoDup_split in Huniq2. destruct Huniq2.
        apply IHbs; auto.
Qed.

Lemma block_eq2: forall f id1 b1 b2,
  uniqFdef f -> blockInFdefB b2 f = true ->
  blockInFdefB b1 f = true ->
  In id1 (getStmtsLocs (snd b1)) ->
  In id1 (getStmtsLocs (snd b2)) ->
  b1 = b2.
Proof.
  destruct f as [[] bs]. simpl.
  intros.
  destruct H as [_ H].
  apply NoDup_split in H.
  destruct H as [_ H].
  induction bs; simpl in *; intros.
    congruence.

    binvt H0 as J1 J1.
      apply blockEqB_inv in J1. subst.
      binvt H1 as J2 J2.
        apply blockEqB_inv in J2. subst.
        auto.
     
        eapply in_getStmtsLocs__in_getBlocksLocs in J2; eauto.
        eapply NoDup_disjoint in H; eauto. tauto.
        
      binvt H1 as J2 J2.
        apply blockEqB_inv in J2. subst.
        eapply in_getStmtsLocs__in_getBlocksLocs in H3; eauto.
        eapply NoDup_disjoint in H; eauto. tauto.

        apply NoDup_split in H. destruct H. auto.
Qed.

Lemma lookupBlockViaIDFromFdef__lookupBlockViaLabelFromFdef__eq : forall F stmts1
  i0 block2 l'
  (Huniq : uniqFdef F)
  (Hlkup : Some stmts1 = lookupBlockViaLabelFromFdef F l')
  (HeqR1' : In i0 (getStmtsLocs stmts1))
  (H5 : lookupBlockViaIDFromFdef F i0 = Some block2),
  (l', stmts1) = block2.
Proof.
  intros.
  symmetry in Hlkup.
  apply lookupBlockViaLabelFromFdef_inv in Hlkup; auto.
  assert (G:=H5).
  apply lookupBlockViaIDFromFdef__blockInFdefB in H5.
  apply lookupBlockViaIDFromFdef__InGetBlockIDs in G.
  eapply block_eq2; eauto.
  eapply in_getStmtsIDs__in_getStmtsLocs; eauto.
Qed.

Lemma insnInFdefBlockB__lookupBlockViaIDFromFdef : forall i1 F b1
  (Huniq: uniqFdef F) (Hsome: getInsnID i1 <> None)
  (H : insnInFdefBlockB i1 F b1 = true),
  lookupBlockViaIDFromFdef F (getInsnLoc i1) = Some b1.
Proof.
  intros.
  assert (H':=H).
  apply insnInFdefBlockB__blockInFdefB in H.
  apply insnInFdefBlockB__insnInBlockB in H'.
  apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
  destruct b1 as [? []]. simpl in *.
  destruct i1; simpl in *; try congruence.
    solve_in_list.  

  apply in_or_app. right.
  eapply uniqFdef__blockInFdefB__nodup_cmds in H; eauto.
  solve_in_list.
Qed.

Lemma lookupPhiNodeViaIDFromPhiNodes__eqid : forall p id1 p0
  (HeqR0 : Some p0 = lookupPhiNodeViaIDFromPhiNodes p id1),
  getInsnLoc (insn_phinode p0) = id1.
Proof.
  induction p; simpl; intros.
    inv HeqR0.

    destruct_if; auto.
      apply IHp in H0. simpl in H0. auto.
Qed.

Lemma lookupCmdViaIDFromCmds__eqid : forall cs id1 c
  (HeqR0 : Some c = lookupCmdViaIDFromCmds cs id1),
  getInsnLoc (insn_cmd c) = id1.
Proof.
  induction cs; simpl; intros.
    inv HeqR0.

    destruct (eq_atom_dec id1 (getCmdLoc a)).
      inv HeqR0. auto.
      apply IHcs in HeqR0. simpl in HeqR0. auto.
Qed.

Lemma lookupInsnViaIDFromFdef__eqid : forall F id1 insn1,
  lookupInsnViaIDFromFdef F id1 = Some insn1 ->
  getInsnLoc insn1 = id1.
Proof.
  destruct F as [[fa ty fid la va] bs]. simpl.
  induction bs as [|a bs]; simpl; intros.
    inv H.

    remember (lookupInsnViaIDFromBlock a id1) as R.
    destruct R; eauto 2.
      inv H.
      destruct a as [? []]. simpl in HeqR.
      remember (lookupPhiNodeViaIDFromPhiNodes phinodes5 id1) as R.
      destruct R.
        inv HeqR.
        apply lookupPhiNodeViaIDFromPhiNodes__eqid in HeqR0; auto.

        remember (lookupCmdViaIDFromCmds cmds5 id1) as R.
        destruct R; inv HeqR.
          apply lookupCmdViaIDFromCmds__eqid in HeqR1; auto.

          destruct_if. simpl. auto.
Qed.

Lemma cmdInBlockB__inGetBlockLocs: forall c b,
  cmdInBlockB c b -> In (getCmdLoc c) (getStmtsLocs (snd b)).
Proof.
  destruct b as [? []]. simpl. intros.
  apply InCmdsB_in in H. apply In_InCmdLocs in H.
  apply in_or_app. right. apply in_or_app. auto.
Qed.

Lemma insnInFdefBlockB__lookupBlockViaIDFromFdef__eq: forall c1 F1 b1 block'
  (Huniq: uniqFdef F1) (H0 : insnInFdefBlockB (insn_cmd c1) F1 b1 = true)
  (H5 : lookupBlockViaIDFromFdef F1 (getCmdLoc c1) = Some block'),
  b1 = block'.
Proof.
  intros. destruct F1 as [[]].
  simpl in *.
  destruct Huniq as [_ Huniq].
  apply NoDup_split in Huniq.
  destruct Huniq as [_ Huniq].
  bdestruct H0 as H1 H2.
  clear - Huniq H1 H2 H5.
  induction blocks5; simpl in *.
    congruence.

    binvt H2 as H3 H3.
      apply blockEqB_inv in H3. subst.
      destruct (in_dec eq_dec (getCmdLoc c1) (getStmtsIDs (snd a))).
        inv H5; auto.
        
        apply lookupBlockViaIDFromBlocks__in_getBlocksLocs in H5.
        apply cmdInBlockB__inGetBlockLocs in H1.
        eapply NoDup_disjoint in Huniq; eauto. 
        tauto.

      destruct (in_dec eq_dec (getCmdLoc c1) (getStmtsIDs (snd a))).
        inv H5.      
        apply cmdInBlockB__inGetBlockLocs in H1.
        eapply in_getStmtsLocs__in_getBlocksLocs in H3; eauto.
        eapply NoDup_disjoint in Huniq; eauto. 
        contradict Huniq.
        apply in_getStmtsIDs__in_getStmtsLocs; auto.

        apply NoDup_split in Huniq. tauto.
Qed.

Lemma getCmdLoc_in_getCmdsLocs': forall c1 cs ls
  (H0 : InCmdsB c1 cs), In (getCmdLoc c1) (getCmdsLocs cs ++ ls).
Proof.
  intros. apply in_or_app. left. apply getCmdLoc_in_getCmdsLocs; auto.
  apply InCmdsB_in; auto.
Qed.

Lemma getCmdsLocs_uniq: forall c1 c2 cs,
  NoDup (getCmdsLocs cs) ->
  In c1 cs ->
  In c2 cs ->
  getCmdLoc c1 = getCmdLoc c2 ->
  c1 = c2.
Proof.
  induction cs; simpl; intros.
    inv H0.

    inv H.
    destruct H0 as [H0 | H0]; subst.
      destruct H1 as [H1 | H1]; auto.
        apply getCmdLoc_in_getCmdsLocs in H1.
        rewrite H2 in H5. congruence.

      destruct H1 as [H1 | H1]; subst; eauto.
        apply getCmdLoc_in_getCmdsLocs in H0.
        rewrite H2 in H0. congruence.
Qed.

Lemma in_middle_inv: forall cs1 c cs2 cs1' cs2',
  NoDup (getCmdsLocs (cs1 ++ c :: cs2)) ->
  cs1 ++ c :: cs2 = cs1' ++ c :: cs2' ->
  cs1 = cs1' /\ cs2 = cs2'.
Proof.
  induction cs1; simpl; intros.
    destruct cs1'; inv H0; auto.
      inv H. contradict H2. apply InGetCmdsLocs_middle.

    inv H.
    destruct cs1'; inv H0.
      contradict H3. apply InGetCmdsLocs_middle.
      apply IHcs1 in H2; auto. destruct H2; subst; auto.
Qed.

Lemma InGetBlockLocs_uniqBlocks_false: forall a bs b id0
  (H : uniqBlocks (a :: bs))
  (H1 : InBlocksB b bs = true)
  (H3 : In id0 (getStmtsLocs (snd b)))
  (H2 : In id0 (getStmtsLocs (snd a))),
  False.
Proof.
  intros.
  eapply in_getStmtsLocs__in_getBlocksLocs in H1; eauto.
  unfold uniqBlocks in H.
  destruct H as [_ H].
  simpl in H.
  apply NoDup_disjoint with (i0:=id0) in H; auto.
Qed.

Lemma cmdInBlockB_eqBlock_aux: forall a bs b c
  (H : uniqBlocks (a :: bs))
  (H1 : InBlocksB b bs = true)
  (H3 : cmdInBlockB c b)
  (H2 : cmdInBlockB c a),
  False.
Proof.
  intros.
  apply cmdInBlockB__inGetBlockLocs in H2.
  apply cmdInBlockB__inGetBlockLocs in H3.
  eapply InGetBlockLocs_uniqBlocks_false in H1; eauto.
Qed.

Lemma in_getStmtsIDs__in_getBlocksLocs : forall bs b i0,
  In i0 (getStmtsIDs (snd b)) ->
  InBlocksB b bs ->
  In i0 (getBlocksLocs bs).
Proof.
  intros.
  eapply in_getStmtsLocs__in_getBlocksLocs in H0; eauto.
  apply in_getStmtsIDs__in_getStmtsLocs; auto.
Qed.

Lemma InGetBlockIDs_uniqBlocks_false: forall a bs b id0
  (H : uniqBlocks (a :: bs))
  (H1 : InBlocksB b bs = true)
  (H3 : In id0 (getStmtsIDs (snd b)))
  (H2 : In id0 (getStmtsIDs (snd a))),
  False.
Proof.
  intros.
  apply in_getStmtsIDs__in_getStmtsLocs in H2.
  apply in_getStmtsIDs__in_getStmtsLocs in H3.
  eapply InGetBlockLocs_uniqBlocks_false; eauto.
Qed.

Lemma InGetBlockIDs__lookupBlockViaIDFromFdef: forall F1 b i0,
  uniqFdef F1 ->
  blockInFdefB b F1 ->
  In i0 (getStmtsIDs (snd b)) ->
  lookupBlockViaIDFromFdef F1 i0 = Some b.
Proof.
  destruct F1 as [[fa ty fid la va] bs]. simpl.
  intros b i0 Huniq.
  destruct Huniq as [Huniq Huniq'].
  apply NoDup_split in Huniq'. destruct Huniq' as [_ Huniq'].
  induction bs as [|a bs]; simpl; intros.
    congruence.

    binvt H as H H.
      apply blockEqB_inv in H. subst.
      destruct (@in_dec id (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom)) i0
         (getStmtsIDs (snd a))); auto.
        contradict H0; auto.

      destruct (@in_dec id (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom)) i0
         (getStmtsIDs (snd a))).
        eapply InGetBlockIDs_uniqBlocks_false in H; eauto.
        inv H.

        simpl_env in Huniq. apply uniqBlocks_inv in Huniq. destruct Huniq.
        simpl in Huniq'. apply NoDup_split in Huniq'. destruct Huniq'. eauto.        
Qed.

Lemma cmdInBlockB_eqBlock : forall F1 b b' c,
  uniqFdef F1 ->
  blockInFdefB b F1 ->
  blockInFdefB b' F1 ->
  cmdInBlockB c b ->
  cmdInBlockB c b' -> b = b'.
Proof.
  destruct F1 as [[fa ty fid la va] bs]. simpl.
  intros b b' c [Huniq Huniq'].
  apply NoDup_split in Huniq'. destruct Huniq' as [_ Huniq'].
  induction bs; simpl; intros.
    congruence.

    apply orb_true_iff in H.
    apply orb_true_iff in H0.
    destruct H as [H | H].
      apply blockEqB_inv in H. subst.
      destruct H0 as [H0 | H0].
        apply blockEqB_inv in H0. subst. auto.
        eapply cmdInBlockB_eqBlock_aux in H0; eauto. inv H0.

      destruct H0 as [H0 | H0].
        apply blockEqB_inv in H0. subst.
        eapply cmdInBlockB_eqBlock_aux in H2; eauto. inv H2.

        simpl_env in Huniq. apply uniqBlocks_inv in Huniq. destruct Huniq.
        simpl in Huniq'. apply NoDup_split in Huniq'. destruct Huniq'. eauto.        
Qed.

Lemma nodup_getCmdsLocs_in_first: forall c1 cs1 cs2,
  NoDup (getCmdsLocs (cs1++cs2)) ->
  In (getCmdLoc c1) (getCmdsLocs cs1) ->
  In c1 (cs1++cs2) ->
  In c1 cs1.
Proof.
  intros.
  apply in_app_or in H1.
  destruct H1; auto.
  rewrite getCmdsLocs_app in H.
  apply NoDup_disjoint' with (i0:=getCmdLoc c1) in H; auto.
  apply In_InCmdLocs in H1. contradict H1; auto.
Qed.

Lemma blockInFdefB__cmdInFdefBlockB__eqBlock: forall l3 ps1 cs tmn1 f c b1
  (Huniq: uniqFdef f) 
  (Hin : blockInFdefB (l3, stmts_intro ps1 cs tmn1) f = true)
  (H : cmdInFdefBlockB c f b1 = true)
  (Hin : In c cs),
  (l3, stmts_intro ps1 cs tmn1) = b1.
Proof.
  intros.
  unfold cmdInFdefBlockB in H.
  bdestruct H as H1 H2.
  eapply cmdInBlockB_eqBlock; eauto.
    simpl. apply In_InCmdsB; auto.
Qed.

Lemma incl_insert: forall A (l1 l2:list A) a, incl (l1++l2) (l1++a::l2).
Proof.
  induction l1; simpl; intros; intros x J; simpl; auto.
    simpl in J. destruct J as [J | J]; auto.
    right. apply IHl1; auto.
Qed.

Lemma incl_app: forall A (l0 l1 l2:list A),
  incl l1 l2 -> incl (l0++l1) (l0++l2).
Proof.
  intros. intros x J.
  apply in_or_app. apply in_app_or in J.
  destruct J as [J | J]; auto.
Qed.

Lemma lookupBlockViaIDFromBlocks__InGetBlocksLocs : forall bs id1 b,
  lookupBlockViaIDFromBlocks bs id1 = Some b ->
  In id1 (getBlocksLocs bs).
Proof.
  induction bs; simpl; intros.
    inv H.

    apply in_or_app.
    destruct (in_dec eq_dec id1 (getStmtsIDs (snd a))); eauto.
    inv H. left. apply in_getStmtsIDs__in_getStmtsLocs; auto.
Qed.

Lemma firstn_nil : forall A n, firstn n (@nil A) = nil.
Proof. induction n; simpl; auto. Qed.

Lemma skipn_nil : forall A n, skipn n (@nil A) = nil.
Proof. induction n; simpl; auto. Qed.

Lemma app_middle_split: forall A (l1 l2 l3 l4:list A) a,
  l1++a::l2 = l3++l4 ->
  (exists l12, l1 = l3++l12 /\ l4 = l12++a::l2) \/
  (exists l21, l3 = l1++a::l21 /\ l2 = l21++l4).
Proof.
  induction l1; simpl; intros.
    destruct l3.
      destruct l4; inv H.
        left. exists nil. auto.
      inv H. right. exists l3. auto.

    destruct l3.
      destruct l4; inv H.
        left. exists (a1::l1). auto.
      inv H. apply IHl1 in H2.
      destruct H2 as [[l21 [J1 J2]]|[l21 [J1 J2]]]; subst; simpl; eauto.
Qed.

Lemma nth_error_In : forall A n (l1:list A) a,
  nth_error l1 n = Some a -> In a l1.
Proof.
  induction n; simpl; intros; destruct l1; inv H; simpl; auto.
Qed.

Lemma nth_error_firstn_skipn: forall c n cs1 cs2,
  NoDup (getCmdsLocs (cs1++c::cs2)) ->
  nth_error (cs1++c::cs2) n = Some c ->
  firstn n (cs1++c::cs2) = cs1 /\
  skipn n (cs1++c::cs2) = c::cs2.
Proof.
  induction n; simpl; intros.
    destruct cs1; inv H0; auto.
      inv H. contradict H2. apply InGetCmdsLocs_middle.

    destruct cs1; inv H0; simpl in *.
      inv H.
      apply nth_error_In in H2.
      contradict H3. apply In_InCmdLocs; auto.

      inv H.
      apply IHn in H2; auto.
      destruct H2 as [J1 J2].
      rewrite J1. rewrite J2. auto.
Qed.

Lemma notin_app_inv: forall A (l1 l2:list A) a,
  ~ In a (l1 ++ l2) -> ~ In a l1 /\ ~ In a l2.
Proof.
  intros.
  split; intro J; apply H; apply in_or_app; auto.
Qed.

Lemma notin_app: forall A (l1 l2:list A) a,
  ~ In a l1 -> ~ In a l2 ->
  ~ In a (l1 ++ l2).
Proof.
  intros. intro J.
  apply in_app_or in J.
  destruct J as [J | J].
    apply H; auto.
    apply H0; auto.
Qed.

Lemma InGetValueIDs__eq: forall vid v,
  In vid (getValueIDs v) -> v = value_id vid.
Proof.
  destruct v; simpl; intros.
    destruct H as [H | H]; subst; auto.
      inv H.
    inv H.
Qed.

Lemma InOps__valueInListValue: forall (vid : id) (l0 : list (sz * value))
  (H : In vid
        (values2ids (List.map snd l0))),
  valueInListValue (value_id vid) l0.
Proof.
  unfold valueInListValue.
  induction l0; simpl in *; intros.
    inv H.

    destruct a as [v []]; simpl in *;
    destruct v; auto;
      inv H; auto.
Qed.      

Lemma InOps__valueInParams : forall vid p,
  In vid (getParamsOperand p) -> valueInParams (value_id vid) p.
Proof.
  unfold getParamsOperand, valueInParams.
  induction p; intros; simpl in *; auto.
    destruct a.
    remember (split p) as R.
    destruct R; simpl in *.
    destruct v; simpl; eauto.
    destruct H as [H | H]; subst; simpl in *; auto.
Qed.

Lemma InOps__valueInCmdOperands : forall vid c,
  In vid (getInsnOperands (insn_cmd c)) ->
  valueInCmdOperands (value_id vid) c.
Proof.
  intros vid c H.
  destruct c; simpl in *; try solve [
    apply in_app_or in H;
      destruct H as [H | H]; apply InGetValueIDs__eq in H; auto |
    apply InGetValueIDs__eq in H; auto].

    apply in_app_or in H.
    destruct H as [H | H].
      apply InGetValueIDs__eq in H; auto.
      apply InOps__valueInListValue in H; auto.

    apply in_app_or in H.
    destruct H as [H | H].
      apply InGetValueIDs__eq in H; auto.
    apply in_app_or in H.
    destruct H as [H | H]; apply InGetValueIDs__eq in H; auto.

    apply in_app_or in H.
    destruct H as [H | H].
      apply InGetValueIDs__eq in H; auto.
      apply InOps__valueInParams in H; auto.
Qed.

Lemma InOps__valueInTmnOperands : forall vid tmn,
  In vid (getInsnOperands (insn_terminator tmn)) ->
  valueInTmnOperands (value_id vid) tmn.
Proof.
  intros vid tmn H.
  destruct tmn; simpl in *; subst; simpl; try solve
    [auto | apply InGetValueIDs__eq in H; auto].
Qed.

Lemma InOps__valueInPhiNodeOperands: forall x vls
  (Hin' : In x
    (values2ids (list_prj1 value l vls))),
  exists n1 : nat,
    exists l2 : l, nth_error vls n1 = Some (value_id x, l2).
Proof.
  induction vls; simpl; intros.
    inv Hin'.

    destruct a as [[] l0].
      simpl in Hin'.
      destruct Hin' as [J | J]; subst.
        exists O. exists l0. simpl. auto.

        apply IHvls in J. destruct J as [n1 [l2 J]].
        exists (S n1). exists l2. simpl. auto.

      apply IHvls in Hin'. destruct Hin' as [n1 [l2 J]].
      exists (S n1). exists l2. simpl. auto.
Qed.

Lemma valueInValues__InOps' : forall vid l0
  (H: In (value_id vid) (list_prj1 value l l0)),
  In vid (values2ids (list_prj1 value l l0)).
Proof.
  induction l0 as [|[v]]; intros; simpl in *;  auto.
    destruct H as [H | H]; simpl in *; subst; simpl; auto.
    destruct v; simpl; eauto.
Qed.

Lemma valueInInsnOperands__InOps : forall vid instr,
  valueInInsnOperands (value_id vid) instr ->
  In vid (getInsnOperands instr).
Proof.
  intros.
  destruct instr as [[]|c|tmn]; simpl in *.
    apply valueInValues__InOps'; auto.
    apply valueInCmdOperands__InOps; auto.
    apply valueInTmnOperands__InOps; auto.
Qed.

Lemma InOps__valueInListValue': forall v0 (l0 : list (sz * value))
  (Hin0 : In v0
           (List.map
              (fun pat_ : sz * value => let (_, value_) := pat_ in value_)
              l0)),
  valueInListValue v0 l0.
Proof.
  unfold valueInListValue.
  induction l0 as [|[v]]; simpl in *; intros; auto.
Qed.      

Lemma InOps__in_list_prj1: forall v0 l0
  (Hin0 : In v0
           (List.map
              (fun pat_ : value * l => let (value_, _) := pat_ in value_)
              l0)),
  In v0 (list_prj1 value l l0).
Proof.
  induction l0 as [|[]]; simpl; intros; tauto.
Qed.

Lemma app_list_value_l_cons: forall (vls1 vls2 : list (value * l)) v0 l0,
  app vls1 ((v0, l0) :: vls2) =
  app
    (app vls1 ((v0, l0) :: nil)) vls2.
Proof.
  induction vls1; simpl; intros; auto.
    rewrite IHvls1; auto.
Qed.

Lemma terminatorInBlockB__inGetBlockLocs: forall t b,
  terminatorInBlockB t b -> In (getTerminatorID t) (getStmtsLocs (snd b)).
Proof.
  destruct b as [? []]. simpl. intros.
  apply terminatorEqB_inv in H. subst.
  apply in_or_app. right. apply in_or_app. simpl; auto.
Qed.

Lemma getTerminatorID__neq__getCmdLoc: forall t c b1 b2 f,
  (let '(fdef_intro _ bs) := f in NoDup (getBlocksLocs bs)) ->
  insnInFdefBlockB (insn_terminator t) f b1 = true->
  insnInFdefBlockB (insn_cmd c) f b2 = true ->
  getTerminatorID t <> getCmdLoc c.
Proof.
  destruct f as [? bs].
  induction bs; simpl; intros.
    apply andb_true_iff in H0. destruct H0 as [_ H0]. inv H0.

    apply andb_true_iff in H0. destruct H0 as [J1 J2].
    apply andb_true_iff in H1. destruct H1 as [J3 J4].
    apply orb_true_iff in J2.
    apply orb_true_iff in J4.
    apply NoDup_split' in H. destruct H as [G1 [G2 G3]].
    destruct J2 as [J2 | J2].
      apply blockEqB_inv in J2. inv J2.
      destruct J4 as [J4 | J4].
        apply blockEqB_inv in J4. inv J4.
        clear - G1 J1 J3.
        destruct a as [? []]. simpl in *.
        apply terminatorEqB_inv in J1. subst.
        apply InCmdsB_in in J3.
        apply NoDup_split in G1.
        destruct G1 as [_ G1].
        apply NoDup_disjoint with (i0:=getTerminatorID terminator5) in G1;
          simpl; auto.
          intro J. apply G1. rewrite J. apply In_InCmdLocs; auto.

        intro J.
        apply (@G3 (getCmdLoc c)).
          rewrite <- J.
          apply terminatorInBlockB__inGetBlockLocs; auto.

          eapply in_getStmtsLocs__in_getBlocksLocs; eauto.
          apply cmdInBlockB__inGetBlockLocs; auto.

      destruct J4 as [J4 | J4].
        apply blockEqB_inv in J4. inv J4.
        intro J.
        apply (@G3 (getCmdLoc c)).
          apply cmdInBlockB__inGetBlockLocs; auto.

          eapply in_getStmtsLocs__in_getBlocksLocs; eauto.
          rewrite <- J.
          apply terminatorInBlockB__inGetBlockLocs; auto.

        apply IHbs; auto.
          apply andb_true_iff. auto.
          apply andb_true_iff. auto.
Qed.

Lemma in_getCmdsIDs_inv: forall id1 cs,
  In id1 (getCmdsIDs cs) ->
  exists cs1, exists c, exists cs2,
        cs = cs1 ++ c :: cs2 /\ getCmdID c = Some id1.
Proof.
  induction cs; simpl; intros.
    inv H.

    remember (getCmdID a) as R.
    destruct R.
      simpl in H.
      destruct H as [H | H]; subst.
        exists nil. exists a. exists cs. auto.

        apply IHcs in H.
        destruct H as [cs1 [c [cs2 [J1 J2]]]]; subst.
        exists (a::cs1). exists c. exists cs2. auto.
      apply IHcs in H.
      destruct H as [cs1 [c [cs2 [J1 J2]]]]; subst.
      exists (a::cs1). exists c. exists cs2. auto.
Qed.

Lemma lookupInsnViaIDFromFdef__lookupTypViaIDFromFdef: forall F id0 c 
  (Huniq: uniqFdef F)
  (Hlkup: lookupInsnViaIDFromFdef F id0 = Some (insn_cmd c)) 
  (Hc: getCmdID c = Some id0) t0 (Ht: getCmdTyp c = Some t0),
  lookupTypViaIDFromFdef F id0 = Some t0.
Proof.
  intros.
  apply lookupInsnViaIDFromFdef__insnInFdefBlockB in Hlkup.
  destruct Hlkup as [b1 G]. simpl in G.
  apply andb_true_iff in G. destruct G as [G1 G2].
  destruct b1 as [? []]. simpl in G1.
  apply InCmdsB_in in G1.
  eapply uniqF__lookupTypViaIDFromFdef in G1; simpl; eauto.
Qed.

Lemma getCmdID__getCmdLoc: forall c id0
  (Hsome: getCmdID c = Some id0), getCmdLoc c = id0.
Proof. 
  destruct c; simpl; intros; try solve [auto | congruence].
    destruct_if; try solve [auto | congruence].
Qed.

Lemma lookupCmdViaIDFromCmds__getCmdID : forall cs id1 c
  (Hin: In id1 (getCmdsIDs cs)) (Huniq: NoDup (getCmdsLocs cs))
  (HeqR0 : Some c = lookupCmdViaIDFromCmds cs id1),
  getCmdID c = Some id1.
Proof.
  induction cs; simpl; intros.
    congruence.

    inv Huniq.
    destruct (eq_atom_dec id1 (getCmdLoc a)).
      inv HeqR0. 
      destruct (getCmdID a).
        simpl in Hin.
        destruct Hin.
          subst. auto.
          contradict H1. solve_in_list.

        contradict H1. solve_in_list.

      remember (getCmdID a) as R.
      destruct R.
        simpl in Hin.
        destruct Hin; subst.
          symmetry in HeqR. apply getCmdID__getCmdLoc in HeqR. congruence.

          apply IHcs in HeqR0; auto.
        apply IHcs in HeqR0; auto.
Qed.

Ltac solve_NoDup_disjoint :=
match goal with
| H: NoDup (?A++?B++?a::nil) |- ~ In ?a (?A++?B) =>
  rewrite_env ((A++B)++[a]) in H;
  apply NoDup_disjoint with (i0:=a); simpl; eauto
end.

Lemma lookupInsnViaIDFromBlock__getInsnID:   
  forall id1 insn1 b1 (Hin: In id1 (getStmtsIDs (snd b1))) 
  (Huniq: NoDup (getStmtsLocs (snd b1))),
  lookupInsnViaIDFromBlock b1 id1 = Some insn1 ->
  getInsnID insn1 = Some id1.
Proof.
  destruct b1 as [? []].
  simpl.
  intros.
  remember (lookupPhiNodeViaIDFromPhiNodes phinodes5 id1) as R.
  destruct R.
    inv H. 
    apply lookupPhiNodeViaIDFromPhiNodes__eqid in HeqR; auto.
    simpl in *. subst. auto.
 
    symmetry in HeqR.
    apply lookupPhiNodeViaIDFromPhiNodes__NotIn in HeqR.
    remember (lookupCmdViaIDFromCmds cmds5 id1) as R.
    destruct R; inv H.
      eapply lookupCmdViaIDFromCmds__getCmdID; eauto.
        solve_in_list.
        split_NoDup; auto.

      destruct_if. 
      rewrite_env 
      ((getPhiNodesIDs phinodes5 ++ getCmdsLocs cmds5) ++ [getTerminatorID terminator5]) in Huniq.
      eapply NoDup_disjoint with (i0:=getTerminatorID terminator5) in Huniq; simpl; eauto.
      contradict Huniq. solve_in_list.    
Qed.

Lemma lookupInsnViaIDFromFdef_lookupBlockViaIDFromFdef__getInsnID:   
  forall id1 insn1 b1 (Hin: In id1 (getStmtsIDs (snd b1))) F (Huniq: uniqFdef F),
  lookupInsnViaIDFromFdef F id1 = Some insn1 ->
  lookupBlockViaIDFromFdef F id1 = Some b1 ->
  getInsnID insn1 = Some id1.
Proof.
  destruct F as [[fa ty fid la va] bs]. simpl.
  intros [_ Huniq]. apply NoDup_split in Huniq. destruct Huniq as [_ Huniq].
  induction bs as [|a bs]; simpl; intros.
    congruence.

    simpl in Huniq. 
    remember (lookupInsnViaIDFromBlock a id1) as R.
    destruct R as [i | ]; inv H.
      destruct (@in_dec id (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom)) id1
             (getStmtsIDs (snd a))); inv H0.
        apply NoDup_split in Huniq.
        destruct Huniq as [Huniq _].
        eapply lookupInsnViaIDFromBlock__getInsnID; eauto.
        
        symmetry in HeqR.
        apply lookupInsnViaIDFromBlock__In in HeqR.
        apply lookupBlockViaIDFromBlocks__in_getBlocksLocs in H1.
        apply NoDup_disjoint with (i0:=id1) in Huniq; auto.
        tauto.

      destruct (@in_dec id (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom)) id1
             (getStmtsIDs (snd a))); inv H0.
        symmetry in HeqR.
        apply lookupInsnViaIDFromBlock__NotIn in HeqR.
        contradict HeqR. solve_in_list.
        
        apply NoDup_split in Huniq. destruct Huniq as [_ Huniq].
        apply IHbs; auto.
Qed.

Lemma In_getCmdsIDs__getCmdID_eq_getCmdLoc: forall c cs 
  (Huniq: NoDup (getCmdsLocs cs)),
  In (getCmdLoc c) (getCmdsIDs cs) ->
  In c cs ->
  getCmdID c = Some (getCmdLoc c).
Proof.
  induction cs; simpl; intros.
    tauto.

    inv Huniq.
    destruct H0 as [H0 | H0]; subst.
      remember (getCmdID c) as R.
      destruct R.
        simpl in H.
        destruct H as [H | H]; subst; eauto.
        erewrite getCmdID__getCmdLoc; eauto.

        contradict H3. solve_in_list.

      remember (getCmdID a) as R.
      destruct R; auto.
        simpl in H.
        destruct H as [H | H]; subst; auto.
          contradict H3.
          erewrite getCmdID__getCmdLoc; eauto.
          solve_in_list.
Qed.

Lemma phinodeInBlockB__inGetBlockLocs: forall p b,
  phinodeInBlockB p b -> In (getPhiNodeID p) (getStmtsLocs (snd b)).
Proof.
  destruct b as [? []]. simpl. intros.
  apply InPhiNodesB_In in H. apply in_getPhiNodeID__in_getPhiNodesIDs in H.
  solve_in_list.
Qed.

Lemma terminatorInBlockB_inGetBlockLocs: forall t b,
  terminatorInBlockB t b -> In (getTerminatorID t) (getStmtsLocs (snd b)).
Proof.
  intros.
  destruct b as [? []]. simpl in *. intros.
  apply terminatorEqB_inv in H. subst.
  solve_in_list.
Qed.

Lemma insnInBlockB__inGetBlockLocs: forall instr b,
  insnInBlockB instr b ->
  In (getInsnLoc instr) (getStmtsLocs (snd b)).
Proof.
  intros.
  destruct instr; simpl in *.
    apply phinodeInBlockB__inGetBlockLocs in H; auto.
    apply cmdInBlockB__inGetBlockLocs in H; auto.
    apply terminatorInBlockB_inGetBlockLocs in H; auto.
Qed.

Lemma getInsnLoc__notin__getArgsIDs: forall f id1 instr1 (Huniq : uniqFdef f)
  (J2 : lookupInsnViaIDFromFdef f id1 = Some instr1),
  ~ In (getInsnLoc instr1) (getArgsIDsOfFdef f).
Proof.
  intros.
  destruct f as [[]].
  apply lookupInsnViaIDFromFdef__insnInFdefBlockB in J2.
  destruct J2 as [b1 J2]. simpl in J2.
  apply destruct_insnInFdefBlockB in J2.
  destruct J2 as [H1 H2].
  apply insnInBlockB__inGetBlockLocs in H1.
  eapply in_getStmtsLocs__in_getBlocksLocs in H2; eauto.
  simpl in Huniq.
  destruct Huniq as [_ Huniq].
  eapply NoDup_disjoint; eauto.
Qed.

Lemma getInsnLoc__notin__getArgsIDs': forall f id1 instr1 (Huniq : uniqFdef f)
  (Hlkc : lookupInsnViaIDFromFdef f id1 = Some instr1),
  ~ In id1 (getArgsIDsOfFdef f).
Proof.
  intros.
  assert (G:=Hlkc).
  apply lookupInsnViaIDFromFdef__eqid in G. subst.
  eapply getInsnLoc__notin__getArgsIDs in Hlkc; eauto.
Qed.

Lemma getInsnLoc__notin__getArgsIDs'': forall f instr b (Huniq : uniqFdef f)
  (J2 : insnInFdefBlockB instr f b = true),
  ~ In (getInsnLoc instr) (getArgsIDsOfFdef f).
Proof.
  intros.
  apply destruct_insnInFdefBlockB in J2.
  destruct J2 as [H1 H2].
  destruct f as [[]].
  apply insnInBlockB__inGetBlockLocs in H1.
  eapply in_getStmtsLocs__in_getBlocksLocs in H2; eauto.
  simpl in Huniq. simpl.
  eapply NoDup_disjoint; eauto. tauto.
Qed.

Lemma blockInFdefB__lookupBlockViaLabelFromFdef : forall f l3 ps cs tmn
  (Huniq : uniqFdef f)
  (HBinF : blockInFdefB (l3, stmts_intro ps cs tmn) f = true) stmts1
  (J9 : lookupBlockViaLabelFromFdef f l3 = Some stmts1),
  stmts1 = stmts_intro ps cs tmn.
Proof.
  destruct f as [[] ?]. simpl.
  intros.
  eapply InBlocksB__lookupAL; eauto. tauto.
Qed.


Ltac solve_blockInFdefB :=
match goal with
| |- is_true (blockInFdefB ?B ?F) => unfold is_true
| |- _ => idtac
end;
 match goal with
 | _:Some ?s =
     (if ?e
      then lookupBlockViaLabelFromFdef ?F _
      else lookupBlockViaLabelFromFdef ?F _)
   |- blockInFdefB (_,?s) ?F = true => destruct e
 | _:(if ?e
      then lookupBlockViaLabelFromFdef ?F _
      else lookupBlockViaLabelFromFdef ?F _) = Some ?s
   |- blockInFdefB (_,?s) ?F = true => destruct e
 | |- _ => idtac
 end;
 repeat
  match goal with
  | H2:insnInFdefBlockB _ ?F ?b = true
    |- blockInFdefB ?b ?F = true =>
        apply insnInFdefBlockB__blockInFdefB in H2; auto
  | H2:lookupBlockViaIDFromFdef ?F _ = Some ?b
    |- blockInFdefB ?b ?F = true =>
        apply lookupBlockViaIDFromFdef__blockInFdefB in H2; auto
  | H1:uniqFdef ?F, H2:Some ?s = lookupBlockViaLabelFromFdef ?F _
    |- blockInFdefB (_, ?s) ?F = true => symmetry  in H2
  | H1:uniqFdef ?F, H2:lookupBlockViaLabelFromFdef ?F _ = Some ?s
    |- blockInFdefB (_, ?s) ?F = true =>
        try destruct s; apply lookupBlockViaLabelFromFdef_inv in H2; auto;
        subst; auto
  | H:getEntryBlock ?F = Some ?B
    |- blockInFdefB ?B ?F = true => apply entryBlockInFdef; auto
  | H:getEntryBlock (fdef_intro _ ?ls) = Some ?B
    |- InBlocksB ?B ?lb = true => apply entryBlockInFdef in H; auto
  | |- _ => idtac
  end.

Lemma IngetTmnID__lookupTmnViaIDFromFdef: forall l1 ps1 cs1 tmn1 f
  (Huniq: uniqFdef f)
  (H : blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true),
  lookupInsnViaIDFromFdef f (getTerminatorID tmn1) = Some (insn_terminator tmn1).
Proof.
  destruct f as [[] bs]. simpl. intros.
  destruct Huniq as [_ Huniq].
  apply NoDup_split in Huniq.
  destruct Huniq as [_ Huniq].
  generalize dependent l1.
  generalize dependent ps1.
  generalize dependent cs1.
  generalize dependent tmn1.
  induction bs as [|a0 bs]; simpl; intros.
    inv H.

    simpl in Huniq.
    apply NoDup_split' in Huniq.
    destruct Huniq as [J1 [J2 J3]].
    apply orb_true_iff in H.
    destruct H as [H | H].
      apply blockEqB_inv in H.
      subst. simpl.
      assert (~ In (getTerminatorID tmn1) 
               (getPhiNodesIDs ps1 ++ getCmdsLocs cs1)) as Hnotin.
        simpl in J1.
        rewrite_env ((getPhiNodesIDs ps1 ++
          getCmdsLocs cs1) ++ getTerminatorID tmn1 :: nil) in J1.
        apply NoDup_disjoint with (i0:=getTerminatorID tmn1)
          in J1; simpl; auto.
      rewrite notin__lookupPhiNodeViaIDFromPhiNodes_none; auto.
      rewrite notin__lookupCmdViaIDFromCmds_none; auto.
        destruct_if. congruence.
        solve_in_list.
        solve_in_list.

      assert (~ In (getTerminatorID tmn1) (getStmtsLocs (snd a0))) as Hnotin.
        intro J. apply J3 in J. apply J. 
        eapply in_getStmtsLocs__in_getBlocksLocs in H; eauto.
        simpl. solve_in_list.
      rewrite notin__lookupInsnViaIDFromBlock_none; auto.
      eapply IHbs; eauto.
Qed.

Lemma lookupInsnViaIDFromFdef__insnInFdefBlockB' : forall F id1 instr,
  lookupInsnViaIDFromFdef F id1 = Some instr ->
  exists b1, insnInFdefBlockB instr F b1.
Proof.
  destruct F as [fh bs]. simpl.
  induction bs as [|a bs]; simpl; intros.
    inv H.

    remember (lookupInsnViaIDFromBlock a id1) as R.
    destruct R.
      inv H.
      exists a.
      destruct a as [l0 [p c t]]. simpl in *.
      remember (lookupPhiNodeViaIDFromPhiNodes p id1) as R.
      destruct R; inv HeqR.
        simpl.
        apply andb_true_iff. split; auto.
        symmetry_ctx. solve_in_list.
        apply orb_true_iff. left. apply blockEqB_refl.
      remember (lookupCmdViaIDFromCmds c id1) as R.
      destruct R; inv H0.
        symmetry in HeqR.
        apply lookupCmdViaIDFromCmds__InCmds in HeqR.
        apply In_InCmdsB in HeqR.
        apply andb_true_iff. split; auto.
        apply orb_true_iff. left. apply blockEqB_refl.
      destruct_if.
        apply andb_true_iff. simpl. 
        split.
          apply terminatorEqB_refl.
          apply orb_true_iff. left. apply blockEqB_refl.

      apply IHbs in H.
      destruct H as [b H].
      apply destruct_insnInFdefBlockB in H.
      destruct H as [J1 J2].
      exists b. apply insnInFdefBlockB_intro; auto.
      simpl. simpl in J2.
      apply orb_true_iff; auto.
Qed.

Lemma IngetCmdsIDs__lookupCmdViaIDFromFdef': forall f c b
  (Huniq: uniqFdef f)
  (H : insnInFdefBlockB (insn_cmd c) f b = true),
  lookupInsnViaIDFromFdef f (getCmdLoc c) = Some (insn_cmd c).
Proof.
  intros.
  apply destruct_insnInFdefBlockB in H.
  destruct H. destruct b as [? []]. 
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef; eauto.
    solve_in_list.
Qed.

Lemma getBlocksLocs__notin__getArgsIDs: forall f b (Huniq : uniqFdef f)
  (HBinF: blockInFdefB b f = true) i0 (Hin: In i0 (getStmtsLocs (snd b))),
  ~ In i0 (getArgsIDsOfFdef f).
Proof.
  destruct f as [[]].
  intros. 
  destruct Huniq as [Huniq1 Huniq2].
  eapply NoDup_disjoint; eauto. 
  solve_in_list.
Qed.

Lemma In_getStmtsIDs__insnInBlockB: forall i0 b,
  In i0 (getStmtsIDs (snd b)) -> 
  exists instr, insnInBlockB instr b = true /\ getInsnID instr = Some i0.
Proof.
  destruct b as [? []]. simpl.
  intro J.
  apply in_app_or in J.
  destruct J as [J | J].
    apply in_getPhiNodesIDs_inv in J.
    destruct J as [ps1 [p1 [ps2 [EQ Hin]]]]; subst.
    exists (insn_phinode p1). simpl.
    split; auto.
      solve_in_list.

    apply in_getCmdsIDs_inv in J.
    destruct J as [cs1 [c1 [cs2 [EQ Hin]]]]; subst.
    exists (insn_cmd c1). simpl.
    split; auto.
      solve_in_list.
Qed.

Lemma lookupBlockViaIDFromFdef__insnInBlockB: forall f i0 b
  (Hlkup: lookupBlockViaIDFromFdef f i0 = Some b),
  exists instr : insn,
    insnInBlockB instr b = true /\
    getInsnID instr = Some i0.
Proof.
  destruct f as [fh bs].
  induction bs; simpl; intros.
    congruence.

    destruct_if.
      apply In_getStmtsIDs__insnInBlockB; auto.
      eauto.
Qed.
     
Lemma IngetPhiNodesIDs__lookupPhiNodeViaIDFromPhiNodes': forall p1 ps1
  (Huniq: NoDup (getPhiNodesIDs ps1)) (H0 : In p1 ps1),
  lookupPhiNodeViaIDFromPhiNodes ps1 (getPhiNodeID p1) = Some p1.
Proof.
  induction ps1; simpl; intros.
    inv H0.

    destruct H0 as [H0 | H0]; subst.
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) 
        (getPhiNodeID p1) (getPhiNodeID p1)); auto.
        congruence.
      inv Huniq.
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) 
        (getPhiNodeID a) (getPhiNodeID p1)); auto.
        contradict H2. rewrite e. solve_in_list.
Qed.

Lemma IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef': forall p l1 ps1 cs1 tmn1 f
  (Huniq: uniqFdef f)
  (H : blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true)
  (H0 : In p ps1),
  lookupInsnViaIDFromFdef f (getPhiNodeID p) = Some (insn_phinode p).
Proof.
  destruct f as [[] bs]. simpl. intros.
  destruct Huniq as [_ Huniq].
  apply NoDup_split in Huniq.
  destruct Huniq as [_ Huniq].
  generalize dependent l1.
  generalize dependent ps1.
  generalize dependent cs1.
  generalize dependent tmn1.
  induction bs as [|a0 bs]; simpl; intros.
    inv H.

    simpl in Huniq.
    apply NoDup_split' in Huniq.
    destruct Huniq as [J1 [J2 J3]].
    apply orb_true_iff in H.
    destruct H as [H | H].
      apply blockEqB_inv in H.
      subst. simpl.
      rewrite IngetPhiNodesIDs__lookupPhiNodeViaIDFromPhiNodes'; auto.
      solve_NoDup.

      assert (~ In (getPhiNodeID p) (getStmtsLocs (snd a0))) as Hnotin.
        intro J. apply J3 in J. apply J.
        eapply in_getStmtsLocs__in_getBlocksLocs in H; eauto.
        solve_in_list.
      rewrite notin__lookupInsnViaIDFromBlock_none; auto.
      eapply IHbs; eauto.
Qed.

Lemma IngetInsnsLocs__lookupInsnViaIDFromFdef: forall f instr b
  (Huniq: uniqFdef f)
  (H : insnInFdefBlockB instr f b = true),
  lookupInsnViaIDFromFdef f (getInsnLoc instr) = Some instr.
Proof.
  intros.
  apply destruct_insnInFdefBlockB in H.
  destruct H. destruct b as [? []]. 
  destruct instr; simpl in H.
    eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef'; eauto. solve_in_list.
    eapply IngetCmdsIDs__lookupCmdViaIDFromFdef; eauto. solve_in_list.

    apply terminatorEqB_inv in H. subst.
    eapply IngetTmnID__lookupTmnViaIDFromFdef; eauto.
Qed.

Lemma getInsnID__getInsnLoc: forall instr id0
  (Hsome: getInsnID instr = Some id0), getInsnLoc instr = id0.
Proof. 
  destruct instr; simpl; intros; try congruence.
    eapply getCmdID__getCmdLoc; eauto.
Qed.

Lemma lookupBlockViaIDFromFdef__lookupInsnViaIDFromFdef: forall f i0 b
  (Hlkup: lookupBlockViaIDFromFdef f i0 = Some b) (Huniq: uniqFdef f),
  exists instr : insn,
    lookupInsnViaIDFromFdef f i0  = Some instr /\ getInsnID instr = Some i0.
Proof.
  intros.
  assert (G:=Hlkup).
  apply lookupBlockViaIDFromFdef__insnInBlockB in G.
  apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkup.
  destruct G as [instr [G1 G2]].
  exists instr.
  split; auto.
    apply getInsnID__getInsnLoc in G2. subst.
    eapply IngetInsnsLocs__lookupInsnViaIDFromFdef with (b:=b); eauto 1.
    apply insnInFdefBlockB_intro; auto.
Qed.

Ltac solve_insnInFdefBlockB :=
match goal with
| H1: blockInFdefB ?b ?f = true, H2: cmdInBlockB ?c ?b = true |- 
  insnInFdefBlockB (insn_cmd ?c) ?f ?b = true =>
  apply insnInFdefBlockB_intro; auto
end.

Lemma lookupBlockViaIDFromFdef__notin_getArgsIDsOfFdef: forall f id1 b
  (Hlk: lookupBlockViaIDFromFdef f id1 = Some b) (Huniq: uniqFdef f),
  ~ In id1 (getArgsIDsOfFdef f).
Proof.
  intros.
  assert (Hlk':=Hlk).
  apply lookupBlockViaIDFromFdef__blockInFdefB in Hlk.
  apply lookupBlockViaIDFromFdef__InGetBlockIDs in Hlk'.
  destruct f as [[]]. simpl in Huniq.
  destruct Huniq.
  eapply NoDup_disjoint in H0; eauto.
  simpl in Hlk.
  apply in_getStmtsIDs__in_getStmtsLocs in Hlk'.
  eapply in_getStmtsLocs__in_getBlocksLocs in Hlk; eauto.
Qed.

Ltac solve_notin_getArgsIDs :=
match goal with
| Hlk: Some _ = lookupBlockViaIDFromFdef ?f ?id1, Huniq: uniqFdef ?f |- 
  ~ In ?id1 (getArgsIDsOfFdef ?f) =>
  symmetry in Hlk;
  eapply lookupBlockViaIDFromFdef__notin_getArgsIDsOfFdef in Hlk; eauto
| Hlk: lookupBlockViaIDFromFdef ?f ?id1 = Some _, Huniq: uniqFdef ?f |- 
  ~ In ?id1 (getArgsIDsOfFdef ?f) =>
  eapply lookupBlockViaIDFromFdef__notin_getArgsIDsOfFdef in Hlk; eauto
| Huniq : uniqFdef ?f, 
  J2 : lookupInsnViaIDFromFdef ?f ?id1 = Some ?instr1 |-
  ~ In (getInsnLoc ?instr1) (getArgsIDsOfFdef ?f) =>
  apply getInsnLoc__notin__getArgsIDs in J2; auto
| Huniq : uniqFdef ?f, 
  J2 : lookupInsnViaIDFromFdef ?f ?id1 = Some ?instr1 |-
  ~ In ?id1 (getArgsIDsOfFdef ?f) =>
  apply getInsnLoc__notin__getArgsIDs' in J2; auto
| Huniq : uniqFdef ?f, 
  J2 : insnInFdefBlockB ?instr ?f ?b = true |-
  ~ In (getInsnLoc ?instr1) (getArgsIDsOfFdef ?f) =>
  apply getInsnLoc__notin__getArgsIDs'' in J2; auto
end.

Lemma in__cmdInBlockB: forall c l1 ps1 cs1 tmn1,
  In c cs1 ->
  cmdInBlockB c (l1, stmts_intro ps1 cs1 tmn1) = true.
Proof. simpl. intros. solve_in_list. Qed.

Lemma getCmdID_in_getCmdsIDs : forall cs i0 c,
  getCmdID c = Some i0 ->
  In c cs ->
  In i0 (getCmdsIDs cs).
Proof.
  induction cs; intros.
    inv H0.

    simpl in *.
    destruct H0 as [H0 | H0]; subst.
      rewrite H. simpl. auto.
      
      apply IHcs in H; auto.
      destruct (getCmdID a); simpl; auto.
Qed.

Lemma getCmdID_in_getBlocksIDs : forall i0 c ps0 cs0 tmn0,
  getCmdID c = Some i0 ->
  In c cs0 ->
  In i0 (getStmtsIDs (stmts_intro ps0 cs0 tmn0)).
Proof.
  intros. 
  simpl. 
  apply in_or_app. right.
  eapply getCmdID_in_getCmdsIDs; eauto.
Qed.

Lemma uniqFdef_cmds_split_middle: forall (cs2 cs2' : list cmd) (c : cmd) 
  (cs1 cs1' : list cmd) F l0 ps0 tmn0
  (Huniq: uniqFdef F)
  (HBinF: blockInFdefB (l0, stmts_intro ps0 (cs1 ++ c :: cs2) tmn0) F = true)
  (H: cs1 ++ c :: cs2 = cs1' ++ c :: cs2'), cs1 = cs1' /\ cs2 = cs2'.
Proof.
  intros.
  apply uniqFdef__blockInFdefB__nodup_cmds in HBinF; auto.
  apply NoDup_cmds_split_middle in H; auto.
Qed.

Lemma InBlocksB_map: forall b f bs (HBinF : InBlocksB b bs),
  InBlocksB (f b) (List.map f bs).
Proof.
  induction bs; simpl; intros; auto.
    binvt HBinF as HBinF HBinF.
      apply blockEqB_inv in HBinF. subst.
      apply orb_true_iff.
      left. apply blockEqB_refl.
    
      apply orb_true_iff.
      right. apply IHbs in HBinF. auto.
Qed.

Lemma In_getArgsIDs_spec: forall t a i0 args5
  (Hin: In (t, a, i0) args5), In i0 (getArgsIDs args5).
Proof.
  induction args5 as [|[[]]]; simpl; intros; auto.
    destruct Hin as [Hin | Hin]; auto.
      left. congruence.
Qed.

Lemma lookupBlockViaLabelFromFdef_self: forall f l0 s0 (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (l0,s0) f = true),
  lookupBlockViaLabelFromFdef f l0 = Some s0.
Proof.
  intros.
  apply blockInFdefB_lookupBlockViaLabelFromFdef in HBinF; auto.
Qed.

Ltac solve_lookupBlockViaLabelFromFdef :=
match goal with
| Huniq: uniqFdef ?f, HBinF: blockInFdefB (?l, ?s) ?f = true |- 
  lookupBlockViaLabelFromFdef ?f ?l = Some ?s =>
    eapply lookupBlockViaLabelFromFdef_self; eauto
| Huniq: uniqFdef ?f, 
  HBinF: lookupBlockViaIDFromFdef ?f _ = Some (?l, ?s) |- 
  lookupBlockViaLabelFromFdef ?f ?l = Some ?s =>
    apply lookupBlockViaIDFromFdef__blockInFdefB in HBinF;
    eapply lookupBlockViaLabelFromFdef_self; eauto
| H1: uniqFdef ?f,
  H2: blockInFdefB (?l, stmts_intro ?ps ?cs ?tmn) ?f = true |-
  lookupBlockViaLabelFromFdef ?f ?l = Some (stmts_intro ?ps ?cs ?tmn) =>
  apply blockInFdefB_lookupBlockViaLabelFromFdef; auto
| Huniq: uniqFdef ?F',
  HBinF: blockInFdefB (?l', stmts_intro ?ps' ?cs' ?tmn') ?F |-
  lookupBlockViaLabelFromFdef ?F ?l' = Some (stmts_intro ?ps' ?cs' ?tmn') =>
  apply blockInFdefB_lookupBlockViaLabelFromFdef; auto
end.

Ltac simpl_locs_in_ctx :=
match goal with
| H: context [getCmdsLocs (_ ++ _)] |- _ => rewrite getCmdsLocs_app in H
| H: context [getCmdsLocs (_ :: _)] |- _ => simpl in H
end.

Ltac simpl_locs :=
match goal with
| |- context [getCmdsLocs (_ ++ _)] => rewrite getCmdsLocs_app
| |- context [getCmdsLocs (_ :: _)] => simpl
end.

Ltac inv_mbind_app :=
  match goal with
  | H: match ?e with
       | Some _ => _
       | None => _
       end = _ |- _ => remember e as R; destruct R
  end.

Ltac xsolve_in_list :=
match goal with
| |- In ?a (_++_) =>
  apply in_or_app;
  first [left; solve [xsolve_in_list] | right; solve [xsolve_in_list]]
| |- In ?a (_::_) =>
  simpl;
  first [left; solve [auto] | right; solve [xsolve_in_list]]
| |- In ?a _ => solve_in_list || auto
end.

Lemma uniqModules_elim: forall M Ms (Hin: In M Ms) (Huniq: uniqModules Ms),
  uniqModule M.
Proof.
  induction Ms; simpl; intros.
    tauto.
    destruct Hin as [Hin | Hin]; subst; tauto.
Qed.

Lemma uniqF__uniqBlocksLocs : forall fh lb,
  uniqFdef (fdef_intro fh lb) -> NoDup (getBlocksLocs lb).
Proof.
  intros. destruct fh. inversion H. split_NoDup; auto.
Qed.

Lemma InPhiNodes_lookupTypViaIDFromPhiNodes' : forall ps p,
  NoDup (getPhiNodesIDs ps) ->
  In p ps ->
  lookupTypViaIDFromPhiNodes ps (getPhiNodeID p) = Some (getPhiNodeTyp p).
Proof.
  induction ps; intros.
    inversion H0.

    simpl in *.
    inv H. unfold lookupTypViaIDFromPhiNodes, lookupTypViaIDFromPhiNode.
    destruct H0 as [H0 | H0]; subst.
      destruct (@eq_dec id 
        (@EqDec_eq_of_EqDec id EqDec_atom) (getPhiNodeID p) (getPhiNodeID p)); 
        subst; auto.
        congruence.

      destruct (@eq_dec id 
        (@EqDec_eq_of_EqDec id EqDec_atom) (getPhiNodeID p) (getPhiNodeID a)); 
        subst; auto.

        contradict H3; auto.
        rewrite <- e. solve_in_list.
Qed.

Lemma InArgs_lookupTypViaIDFromArgs : forall t1 attr1 id1 la0
  (Hnodup: NoDup (getArgsIDs la0))
  (Hin: In (t1, attr1, id1) la0),
  lookupTypViaIDFromArgs la0 id1 = Some t1.
Proof.
  induction la0 as [|[[]]]; intros.
    tauto.

    simpl.
    destruct_in Hin.
      uniq_result.
      destruct_if. congruence.

      inv Hnodup.
      destruct_if.
        apply In_getArgsIDs_spec in Hin. tauto.
Qed.

Lemma InArgs_lookupTypViaIDFromFdef : forall t1 attr1 id1 f la0
  (Hnodup: NoDup (getArgsIDs la0))
  (Hin: In (t1, attr1, id1) la0) (Heq: la0 = getArgsOfFdef f),
  lookupTypViaIDFromFdef f id1 = Some t1.
Proof.
  unfold lookupTypViaIDFromFdef.
  intros.
  destruct f as [[]]. simpl in Heq. subst.
  erewrite InArgs_lookupTypViaIDFromArgs; eauto.
Qed.

Lemma uniqF__lookupPhiNodeTypViaIDFromFdef : forall l1 ps1 cs1 tmn1 f p,
  uniqFdef f ->
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true ->
  In p ps1 ->
  lookupTypViaIDFromFdef f (getPhiNodeID p) = Some (getPhiNodeTyp p).
Proof.
  intros.
  destruct f as [f b].
  destruct f as [fnattrs5 typ5 id5 args5 varg5]. inversion H.
  split_NoDup.
  simpl in *.
  assert (In (getPhiNodeID p) (getBlocksLocs b)) as Hin.
    eapply in_getStmtsLocs__in_getBlocksLocs in H0; eauto.
    simpl. xsolve_in_list.
  destruct H as [J1 J2].
  assert (~ In (getPhiNodeID p) (getArgsIDs args5)) as Hnotin.
    eapply NoDup_disjoint; eauto.
  apply NotInArgsIDs_lookupTypViaIDFromArgs in Hnotin.
  rewrite Hnotin.
  eapply lookupTypViaIDFromBlock__inBlocks; eauto.
  simpl.
  apply NoDup__InBlocksB in H0; auto.
  simpl in H0.
  split_NoDup.
  rewrite InPhiNodes_lookupTypViaIDFromPhiNodes'; auto.
Qed.

Lemma lookupTypViaIDFromArgs_elim : forall id0 t la
  (Hin: lookupTypViaIDFromArgs la id0 = Some t),
  exists attr0, In (t, attr0, id0) la.
Proof.
  induction la as [|[[]]]; simpl; intros.
    congruence.

    destruct_if. 
      eauto.
      apply IHla in H0. destruct H0 as [? H0]. eauto.
Qed.

Lemma lookupTypViaIDFromPhiNodes_elim : forall id0 t ps
  (Hin: lookupTypViaIDFromPhiNodes ps id0 = Some t),
  exists p, 
    In p ps /\
    getPhiNodeTyp p = t /\ getPhiNodeID p = id0.
Proof.
  induction ps; simpl; intros.
    congruence.

    inv_mbind_app.
      inv Hin.
      unfold lookupTypViaIDFromPhiNode in *.
      destruct_if.
      eauto.

      apply IHps in Hin.
      destruct Hin as [p [J1 [J2 J3]]]; subst.
      eauto.
Qed.

Lemma lookupTypViaIDFromCmds_elim : forall id0 t cs
  (Hin: lookupTypViaIDFromCmds cs id0 = Some t),
  exists c, 
    In c cs /\
    getCmdTyp c = Some t /\ getCmdLoc c = id0.
Proof.
  induction cs; simpl; intros.
    congruence.

    inv_mbind_app.
      inv Hin.
      unfold lookupTypViaIDFromCmd in *.
      inv_mbind.
      destruct_if.
      exists a. split; auto. 

      apply IHcs in Hin.
      destruct Hin as [c [J1 [J2 J3]]]; subst.
      eauto.
Qed.

Lemma lookupTypViaIDFromBlock_elim : forall id0 t b
  (Hin: lookupTypViaIDFromBlock b id0 = Some t),
  (exists instr, 
    insnInBlockB instr b = true /\
    getInsnTyp instr = Some t /\ getInsnLoc instr = id0).
Proof.
  unfold lookupTypViaIDFromBlock. destruct b as [? []].
  intros.
    inv_mbind_app.
    inv Hin. symmetry in HeqR.
    apply lookupTypViaIDFromPhiNodes_elim in HeqR.
    destruct HeqR as [p [J1 [J2 J3]]]. 
    subst. 
    exists (insn_phinode p). 
    simpl. split; auto. solve_in_list.
 
    inv_mbind_app.
    inv Hin. symmetry in HeqR0.
    apply lookupTypViaIDFromCmds_elim in HeqR0.
    destruct HeqR0 as [c [J1 [J2 J3]]]. 
    subst. 
    exists (insn_cmd c). 
    simpl. split; auto. solve_in_list.

    exists (insn_terminator terminator5).
    unfold lookupTypViaIDFromTerminator in Hin.
    destruct_if.
    simpl. split; auto. solve_refl.
Qed.

Lemma lookupTypViaIDFromBlocks_elim : forall id0 t bs
  (Hin: lookupTypViaIDFromBlocks bs id0 = Some t),
  exists b, In b bs /\
  exists instr, 
    insnInBlockB instr b = true /\ 
    getInsnTyp instr = Some t /\ getInsnLoc instr = id0.
Proof.
  induction bs as [|b bs]; simpl; intros.
    congruence.

    inv_mbind_app.
      inv Hin. symmetry_ctx.
      apply lookupTypViaIDFromBlock_elim in HeqR; auto.
      exists b. split; auto.

      apply IHbs in Hin.
      destruct Hin as [b0 [Hin J]].
      exists b0. repeat (split; auto).
Qed.

Lemma lookupTypViaIDFromFdef_elim : forall f id0 t
  (Hin: lookupTypViaIDFromFdef f id0 = Some t),
  (exists attr0, In (t, attr0, id0) (getArgsOfFdef f)) \/
  exists b, 
  exists instr, 
    insnInFdefBlockB instr f b = true /\
    getInsnTyp instr = Some t /\ getInsnLoc instr = id0.
Proof.
  unfold lookupTypViaIDFromFdef.
  intros.
  destruct f as [[]].
  inv_mbind_app.
    uniq_result.
    left.
    apply lookupTypViaIDFromArgs_elim; auto.

    right.
    apply lookupTypViaIDFromBlocks_elim in Hin.
    destruct Hin as [b [J1 [instr [J2 [J3 J4]]]]].
    exists b.
    exists instr.
    split; auto.
    apply insnInFdefBlockB_intro; auto.
      simpl. apply In_InBlocksB; auto.
Qed.

Lemma uniqF__lookupTmnTypViaIDFromFdef : forall l1 ps1 cs1 tmn1 f,
  uniqFdef f ->
  blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true ->
  lookupTypViaIDFromFdef f (getTerminatorID tmn1) = Some (getTerminatorTyp tmn1).
Proof.
  intros.
  destruct f as [f b].
  destruct f as [fnattrs5 typ5 id5 args5 varg5]. inversion H.
  assert (In (getTerminatorID tmn1) (getBlocksLocs b)) as Hin.
    eapply in_getStmtsLocs__in_getBlocksLocs in H0; eauto.
    simpl. solve_in_list.
  assert (~ In (getTerminatorID tmn1) (getArgsIDs args5)) as Hnotin.
    eapply NoDup_disjoint; eauto.
  apply NotInArgsIDs_lookupTypViaIDFromArgs in Hnotin.
  simpl.
  rewrite Hnotin. split_NoDup.
  eapply lookupTypViaIDFromBlock__inBlocks; eauto.
  simpl.
  apply NoDup__InBlocksB in H0; auto.
  simpl in H0.
  assert (~ In (getTerminatorID tmn1) (getPhiNodesIDs ps1)) as HnotinPs.
    eapply NoDup_disjoint; eauto.
      solve_in_list.
  apply NotInPhiNodesIDs__lookupTypViaIDFromPhiNodes in HnotinPs.
  rewrite HnotinPs.
  apply NoDup_split in H0. destruct H0 as [_ H0].
  assert (~ In (getTerminatorID tmn1) (getCmdsLocs cs1)) as HnotinCs.
    eapply NoDup_disjoint; eauto.
      xsolve_in_list.
  apply NotInCmdLocs__lookupTypViaIDFromCmds in HnotinCs.
  rewrite HnotinCs. 
  unfold lookupTypViaIDFromTerminator. 
  destruct_if. congruence.
Qed.

Lemma lookupTypViaIDFromFdef_intro : forall f id0 t
  (Huniq: uniqFdef f)
  (Hin:
   (exists attr0, In (t, attr0, id0) (getArgsOfFdef f)) \/
    exists b, 
    exists instr, 
      insnInFdefBlockB instr f b = true /\
      getInsnTyp instr = Some t /\ getInsnLoc instr = id0
  ),
  lookupTypViaIDFromFdef f id0 = Some t.
Proof.
  intros.
  destruct Hin as [[attr0 Hin] | 
                   [b [instr [Hin [J1 J2]]] ]].
    eapply InArgs_lookupTypViaIDFromFdef; eauto.
    solve_NoDup.

    apply destruct_insnInFdefBlockB in Hin.
    destruct Hin as [Hin1 Hin2].
    destruct b as [? []]. simpl in Hin1.
    destruct instr; simpl in *.
      uniq_result.
      eapply uniqF__lookupPhiNodeTypViaIDFromFdef; eauto.
        solve_in_list.

      eapply uniqF__lookupCmdTypViaIDFromFdef; eauto.
        solve_in_list.

      uniq_result.    
      apply terminatorEqB_inv in Hin1. subst.
      eapply uniqF__lookupTmnTypViaIDFromFdef; eauto.    
Qed.

Ltac solve_isNotPhiNode := unfold isPhiNode; simpl; congruence.

Lemma in_map_fst__in_map: forall value_ vls,
  In value_ 
    (List.map (fun pat_ : value * l => let (value_0, _) := pat_ in value_0) vls) 
  ->
  exists l0, In (value_, l0) vls.
Proof.
  induction vls as [|[]]; intros.
    inv H.

    simpl in H. simpl.
    inv H; eauto.
      apply IHvls in H0. 
      destruct H0 as [l1 H0]. eauto.
Qed.

Lemma getArgsOfFdef__getArgsIDsOfFdef: forall f t attr0 id5
  (Hin: In (t, attr0, id5) (getArgsOfFdef f)), In id5 (getArgsIDsOfFdef f).
Proof.
  destruct f as [[? ? ? la ?] bs]. simpl.
  induction la as [|[]]; simpl; intros; auto.
    destruct Hin as [Hin | Hin]; eauto 3.
      inv Hin. auto.
Qed.

Lemma InOps__valueInValues' : forall vid l0
  (H: In vid (values2ids (list_prj1 value l l0))),
  In (value_id vid) (list_prj1 value l l0).
Proof.
  induction l0 as [|[v]]; intros; simpl in *; auto.
    destruct v; simpl; eauto.
    destruct_in H; simpl in *; subst; simpl; auto.
Qed.

Lemma InOps__valueInInsnOperands : forall vid instr,
  In vid (getInsnOperands instr) ->
  valueInInsnOperands (value_id vid) instr.
Proof.
  intros.
  destruct instr as [[]|c|tmn]; simpl in *.
    apply InOps__valueInValues'; auto.
    apply InOps__valueInCmdOperands; auto.
    apply InOps__valueInTmnOperands; auto.
Qed.

Lemma fold_left_or_true_elim: forall B (f: B -> bool)
  l0 (H:fold_left (fun a b => a || f b) l0 false = true),
  exists x, In x l0 /\ f x = true.
Proof.
  induction l0; simpl; intros. 
    congruence.

    remember (f a) as R. 
    destruct R.
      eauto.
      apply IHl0 in H. destruct H as [x [J1 J2]]. eauto.
Qed.

Ltac solve_block_eq :=
match goal with
| Hlkup: lookupBlockViaIDFromFdef ?F ?id = Some ?b |- 
  _ = ?b =>
    eapply block_eq2 with (id1:=id); try solve 
      [eauto 1 | solve_blockInFdefB | simpl; xsolve_in_list | solve_in_list]
| Hlkup: Some ?b = lookupBlockViaIDFromFdef ?F ?id |- 
  _ = ?b =>
    eapply block_eq2 with (id1:=id); try solve 
      [eauto 1 | solve_blockInFdefB | simpl; xsolve_in_list | solve_in_list]
| Hlkup: lookupBlockViaIDFromFdef ?F ?id = Some ?b |- 
  ?b = _ =>
    eapply block_eq2 with (id1:=id); try solve 
      [eauto 1 | solve_blockInFdefB | simpl; xsolve_in_list | solve_in_list]
| Hlkup: Some ?b = lookupBlockViaIDFromFdef ?F ?id |- 
  ?b = _ =>
    eapply block_eq2 with (id1:=id); try solve 
      [eauto 1 | solve_blockInFdefB | simpl; xsolve_in_list | solve_in_list]
end.

Ltac lookupBlockViaLabelFromFdef_inv_tac :=
match goal with
| Huniq:uniqFdef ?f, Hlk:lookupBlockViaLabelFromFdef ?f _ = Some ?b
  |- _ =>
      let EQ := fresh "EQ" in
      let HBinF := fresh "HBinF" in
      destruct b; apply lookupBlockViaLabelFromFdef_inv in Hlk; auto
end.

Ltac solve_lookupBlockViaIDFromFdef :=
match goal with
| Huniq: uniqFdef ?f, 
  H: insnInFdefBlockB _ ?f ?b = true |- 
  lookupBlockViaIDFromFdef ?f _ = Some ?b =>
  apply insnInFdefBlockB__lookupBlockViaIDFromFdef in H; simpl; 
    try solve [auto | congruence]
end.

Lemma fst_split__map_fst: forall A B (l1:list (A*B)),
  fst (split l1) = List.map fst l1.
Proof.
  induction l1 as [|[]]; simpl; auto.
    destruct_let. simpl. rewrite <- IHl1. auto.
Qed.

Lemma snd_split__map_snd: forall A B (l1:list (A*B)),
  snd (split l1) = List.map snd l1.
Proof.
  induction l1 as [|[]]; simpl; auto.
    destruct_let. simpl. rewrite <- IHl1. auto.
Qed.

Lemma split_r_in : forall A B (l1:list (A*B))(b:B),
  In b (snd (split l1)) -> exists a, In (a,b) l1.
Proof.
  induction l1 as [|[]]; simpl; intros; try tauto.
    destruct_let. simpl in *.
    destruct H as [H | H]; subst; eauto.
      apply IHl1 in H. 
      destruct H as [a0 H]. eauto.
Qed.

Lemma split_l_in : forall A B (l1:list (A*B))(a:A),
  In a (fst (split l1)) -> exists b, In (a,b) l1.
Proof.
  induction l1 as [|[]]; simpl; intros; try tauto.
    destruct_let. simpl in *.
    destruct H as [H | H]; subst; eauto.
      apply IHl1 in H. 
      destruct H as [b0 H]. eauto.
Qed.

Ltac destruct_phinodeInFdefBlockB_tac :=
match goal with
| Hin: phinodeInFdefBlockB _ _ ?b = true |- _ =>
  let HPinB:=fresh "HPinB" in
  let HBinF:=fresh "HBinF" in
  destruct b as [? []];
  apply andb_true_iff in Hin;
  destruct Hin as [HPinB HBinF];
  simpl in HPinB;
  apply InPhiNodesB_In in HPinB
end.

Lemma lookupTypViaIDFromFdef_elim': forall (f : fdef) (vid : id) (t : typ)
  (Hlk: lookupTypViaIDFromFdef f vid = Some t) (HuniqF: uniqFdef f),
  In vid (getArgsIDsOfFdef f) \/
  exists instr : insn,
    lookupInsnViaIDFromFdef f vid = Some instr /\
    getInsnTyp instr = Some t /\ getInsnLoc instr = vid.
Proof.
  intros. 
  apply lookupTypViaIDFromFdef_elim in Hlk; auto.
  destruct Hlk as [[att0 Hin] | [b [instr [J1 [J2 J3]]]]]; subst.
    left. destruct f as [[]]. simpl in *.
    eapply In_getArgsIDs_spec; eauto.

    right. exists instr. split; auto.
    eapply IngetInsnsLocs__lookupInsnViaIDFromFdef; eauto.
Qed.

Lemma getValueViaLabelFromValuels__InValueList: forall (l1 : l) 
  (vls1 : list (value * l))
  (v : value) (Hnth : getValueViaLabelFromValuels vls1 l1 = Some v),
  In (v, l1) vls1.
Proof.
  induction vls1 as [|[]]; simpl in *; intros.
    congruence.
    destruct_if; auto.
Qed.

Ltac solve_lookupInsnViaIDFromFdef :=
match goal with
| _: In ?p ?ps, _:blockInFdefB (_, stmts_intro ?ps _ _) ?f = true,
  _: uniqFdef ?f |-
  lookupInsnViaIDFromFdef ?f (getPhiNodeID ?p) = Some (insn_phinode ?p) =>
  eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef'; eauto 1
| _: insnInFdefBlockB ?i ?f _ = true, _: uniqFdef ?f |-
  lookupInsnViaIDFromFdef ?f (getInsnLoc ?i) = Some ?i =>
  eapply IngetInsnsLocs__lookupInsnViaIDFromFdef; eauto 1
| Huniq: uniqFdef ?f, 
  H: insnInFdefBlockB (insn_cmd ?c) ?f ?b = true |- 
  lookupInsnViaIDFromFdef ?f (getCmdLoc ?c) = Some (insn_cmd ?c) =>
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef'; eauto
| Huniq: uniqFdef ?f, 
  H: blockInFdefB (_, stmts_intro _ ?cs _) ?f = true,
  H1: In ?c ?cs |- 
  lookupInsnViaIDFromFdef ?f (getCmdLoc ?c) = Some (insn_cmd ?c) =>
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef; eauto
end.

Lemma getEntryLabel__getEntryBlock: forall f le
  (Hentry: getEntryLabel f = Some le),
  exists be, getEntryBlock f = Some be /\ 
             getBlockLabel be = le.
Proof.
  intros.
  destruct f as [fh [|[]]]; inv Hentry.
  simpl. eauto.
Qed.

Lemma getEntryBlock__getEntryLabel: forall f be,
  getEntryBlock f = Some be ->
  getEntryLabel f = Some (getBlockLabel be).
Proof.
  destruct f as [? bs]. simpl.
  destruct bs as [|[]]; simpl; intros.
    congruence.
    uniq_result. simpl. auto.
Qed.

Lemma getEntryBlock__getEntryLabel_none: forall f,
  getEntryBlock f = None <->
  getEntryLabel f = None.
Proof.
  destruct f as [? bs]. simpl.
  destruct bs as [|[]]; simpl; intros; split; try solve [auto | congruence].
Qed.

Lemma nonempty_getEntryBlock__getEntryLabel: forall f,
  getEntryBlock f <> None ->
  exists entry, getEntryLabel f = Some entry.
Proof.
  destruct f as [? bs]. simpl.
  destruct bs as [|[]]; simpl; intros; eauto.
    congruence.
Qed.

