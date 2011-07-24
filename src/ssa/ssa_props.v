Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import Coq.Program.Equality.
Require Import CoqListFacts.
Require Import Metatheory.
Require Import alist.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import Coqlib.
Require Import Kildall.
Require Import Maps.

Export LLVMsyntax.
Export LLVMlib.
Export LLVMgv.
Export LLVMopsem.

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

(* NoDup *)

Lemma NotIn_inv : forall X (a:X) (lb1 lb2:list X),
  ~ In a (lb1++lb2) ->
  ~ In a lb1 /\ ~ In a lb2.
Proof.
  intros.
  split; intro J'; apply H; auto using in_or_app.
Qed.

Lemma NoDup_inv : forall X (lb1 lb2:list X),
  NoDup (lb1++lb2) ->
  NoDup lb1 /\ NoDup lb2.
Proof.
  induction lb1; intros.
    split; auto using NoDup_nil.

    simpl in *. inversion H; subst.
    apply IHlb1 in H3. destruct H3.
    apply NotIn_inv in H2.
    destruct H2 as [J1 J2].
    split; auto using NoDup_cons.
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

(* gets *)

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

Lemma getBlocksLabels_app : forall lb1 lb2,
  getBlocksLabels (lb1++lb2) = getBlocksLabels lb1++getBlocksLabels lb2.
Proof.
  induction lb1; intros; auto.
    simpl. rewrite IHlb1. destruct a. simpl_env. auto.
Qed.

Lemma genLabel2Block_block_inv : forall b l0 b',
  lookupAL _ (genLabel2Block_block b) l0 = Some b' ->
  b = b'.
Proof.
  intros. unfold genLabel2Block_block in H.
  destruct b.
  simpl in H.
  destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l1); subst; inversion H; auto.
Qed.        

Lemma NotInGetBlocksLabels__NotInGenLabel2Block_blocks : forall lb l0,
  ~ In l0 (getBlocksLabels lb) ->
  l0 `notin` dom (genLabel2Block_blocks lb).
Proof.
  induction lb; intros.
    simpl. auto.

    destruct a. simpl in *.
    destruct (l1==l0); subst.
      contradict H; auto.

      destruct (In_dec eq_atom_dec l0 (getBlocksLabels lb)) as [J | J].
        contradict H; auto.
        apply IHlb in J; auto.
Qed.

Lemma inc__getLabel2Block_blocks : forall a bs 
  (Hinc : incl [a] (bound_blocks bs)),
  exists b : block, lookupAL block (genLabel2Block_blocks bs) a = Some b.
Proof. 
  intros.
  induction bs; simpl in *; auto.
    assert (J:=@Hinc a). simpl in J. destruct J; auto.
    destruct a0; simpl in *.
    destruct (a==l0); subst.
      exists (block_intro l0 p c t). auto.

      apply IHbs. intros x J.
      assert (x=a) as EQ.
        simpl in J. destruct J; auto. inversion H.
      subst.      
      apply Hinc in J. simpl in J.
      destruct J as [J | J]; subst; auto.
      contradict n; auto.
Qed.

Lemma getBlockLabel_in_genLabel2Block_block : forall B,
  getBlockLabel B `in` dom (genLabel2Block_block B).
Proof.
  destruct B. simpl. auto.
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

Lemma uniqBlocks__uniqLabel2Block : forall lb,
  uniqBlocks lb ->
  uniq (genLabel2Block_blocks lb).
Proof.
  induction lb; intros; simpl; auto.
    destruct a.
    unfold uniqBlocks in H.
    destruct H.
    unfold genLabel2Block_block.
    simpl in *.
    inversion H; subst.
    apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H3.
    apply uniq_cons; auto.
      apply IHlb.
      rewrite ass_app in H0.
      apply NoDup_inv in H0. destruct H0.
      split; auto.
Qed.


Lemma uniqBlocks_nil : uniqBlocks nil.
unfold uniqBlocks. simpl. split; auto using NoDup_nil.
Qed.

Lemma uniqBlocks_inv : forall lb1 lb2,
  uniqBlocks (lb1++lb2) ->
  uniqBlocks lb1 /\ uniqBlocks lb2.
Proof.
  induction lb1; intros.
    split; auto using uniqBlocks_nil.

    destruct a.
    simpl in H.
    inversion H; subst. simpl in *.
    inversion H0; subst.
    clear H H0.
    rewrite getBlocksLocs_app in H1.
    rewrite getBlocksLabels_app in H4, H5.
    apply NoDup_inv in H5. destruct H5.
    simpl_env in H1.
    rewrite ass_app in H1.
    rewrite ass_app in H1.
    rewrite ass_app in H1.
    apply NoDup_inv in H1. destruct H1.
    apply NotIn_inv in H4. destruct H4.
    split.
      split; simpl. 
        auto using NoDup_cons.
        rewrite <- ass_app in H1.
        rewrite <- ass_app in H1.
        simpl_env. auto.
      split; auto.
Qed.

Lemma genLabel2Block_blocks_inv : forall lb f l0 l' ps' cs' tmn',
  uniqBlocks lb ->
  lookupAL _ (genLabel2Block_blocks lb) l0 = Some (block_intro l' ps' cs' tmn') ->
  l0 = l' /\
  blockInFdefB (block_intro l' ps' cs' tmn') (fdef_intro f lb).
Proof.
  induction lb; intros; simpl in *.
    inversion H0.

    assert (J:=H).
    apply uniqBlocks__uniqLabel2Block in H.
    apply mergeALs_inv in H0; auto.
    destruct H0 as [H0 | H0].
      unfold genLabel2Block_block in H0.
      destruct a. simpl in H0.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l1); subst.
        inversion H0; subst. clear H0.
        split; auto.
        apply orb_true_intro.
        left. apply blockEqB_refl.

        inversion H0.

      simpl_env in J. 
      apply uniqBlocks_inv in J.
      destruct J.
      apply IHlb in H0; simpl_env; auto.
      destruct H0.
      split; auto.
      apply orb_true_intro; auto.
Qed.

Lemma lookupBlockViaLabelFromFdef_inv : forall F l0 l' ps' cs' tmn',
  uniqFdef F ->
  lookupBlockViaLabelFromFdef F l0 = Some (block_intro l' ps' cs' tmn') ->
  l0 = l' /\
  blockInFdefB (block_intro l' ps' cs' tmn') F.
Proof.
  intros.
  unfold lookupBlockViaLabelFromFdef in H.
  unfold genLabel2Block_fdef in H.
  destruct F. destruct f. destruct H.
  apply genLabel2Block_blocks_inv; auto.
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
    destruct a; 
      try solve [apply IHPs in H; auto].
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdefID f) fid); subst.
        inversion H; subst.
        left. apply productEqB_refl.

        apply IHPs in H. auto. 
Qed.

Lemma lookupFdefViaGV_inv : forall TD Ps gl lc fs fv F,
  lookupFdefViaGV TD Ps gl lc fs fv = Some F ->
  InProductsB (product_fdef F) Ps.
Proof.
  intros.
  unfold lookupFdefViaGV in H.
  destruct (getOperandValue TD fv lc gl); simpl in H; try solve [inversion H].
  destruct (lookupFdefViaGVFromFunTable fs g); try solve [inversion H].
  apply lookupFdefViaIDFromProducts_inv in H; auto.
Qed.

Lemma entryBlockInFdef : forall F B,
  getEntryBlock F = Some B ->
  blockInFdefB B F.
Proof.
  intros.
  unfold getEntryBlock in H.
  destruct F.
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

Lemma NotIn_NotInBlocksB : forall lb l0 ps cs tmn,
  ~ In l0 (getBlocksLabels lb) ->
  ~ InBlocksB (block_intro l0 ps cs tmn) lb.
Proof.
  induction lb; intros; simpl in *.
    intro J. inversion J.

    destruct a.
    simpl in *.
    remember (block_intro l0 ps cs tmn =b= block_intro l1 p c t) as J.
    destruct J.
      unfold blockEqB in HeqJ.
      unfold lEqB in HeqJ.
      destruct (l0==l1); subst.
        contradict H; auto.

        symmetry in HeqJ.
        apply sumbool2bool_true in HeqJ.
        inversion HeqJ; subst.
        contradict n; auto.

      intro J.
      apply H.
      right.
      apply orb_prop in J.
      destruct J as [J | J].
        inversion J.
     
        destruct (@In_dec _ eq_dec l0 (getBlocksLabels lb)) as [J1 | J1]; auto.
        apply IHlb with (ps:=ps)(cs:=cs)(tmn:=tmn) in J1.
        rewrite J in J1.
        contradict J1; auto.
        unfold is_true. auto.
Qed.

Lemma InBlocksB_In : forall lb l0 ps cs tmn,
  InBlocksB (block_intro l0 ps cs tmn) lb ->
  In l0 (getBlocksLabels lb).
Proof.
  intros.
  destruct (@In_dec _ eq_dec l0 (getBlocksLabels lb)) as [J1 | J1]; auto.
    apply NotIn_NotInBlocksB with (ps:=ps)(cs:=cs)(tmn:=tmn) in J1.
    contradict H; auto.
Qed.

Lemma InBlocksB__NotIn : forall l2 bs l0 cs ps tmn,
  InBlocksB (block_intro l0 cs ps tmn) bs = true ->
  ~ In l2 (getBlocksLabels bs) ->
  l0 <> l2.
Proof.
  intros l2 bs l0 cs ps tmn HbInF H1.
  apply InBlocksB_In in HbInF.
  destruct (eq_dec l0 l2); subst; auto.
Qed.

Lemma InBlocksB__lookupAL : forall bs l3 ps cs tmn
  (Huniq : uniqBlocks bs)
  (HBinF : InBlocksB (block_intro l3 ps cs tmn) bs = true)
  (b1 : block)
  (J9 : lookupAL block (genLabel2Block_blocks bs) l3 = Some b1),
  b1 = block_intro l3 ps cs tmn.
Proof.
  intros.
  simpl in Huniq.
  induction bs; simpl in *.
    inversion J9; subst.

    apply orb_prop in HBinF.   
    destruct HBinF as [HBinF | HBinF].
      apply blockEqB_inv in HBinF; subst.
      simpl in J9.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l3 l3); subst;
        simpl.
        inversion J9; subst; auto.
        contradict n; auto.

      assert (Huniq':=Huniq).
      simpl_env in Huniq'.
      apply uniqBlocks_inv in Huniq'.
      destruct Huniq'.
      destruct a. destruct Huniq as [Huniq _]. simpl in *.
      inversion Huniq; subst.
      assert (J:=HBinF).
      apply InBlocksB_In in J.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l3 l0); subst.
        contradict J; auto.
        apply IHbs; auto.
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

Lemma entryBlockInSystemBlockFdef' : forall los nts Ps gl lc fs fv F S B,
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaGV (los, nts) Ps gl lc fs fv = Some F ->
  getEntryBlock F = Some B ->
  blockInSystemModuleFdef B S (module_intro los nts Ps) F.
Proof.
  intros.
  apply lookupFdefViaGV_inv in H0.
  apply entryBlockInFdef in H1.  
  apply blockInSystemModuleFdef_intro; auto.
Qed.

Lemma productInSystemModuleB_inv : forall F Ps nts los S,
  productInSystemModuleB (product_fdef F) S (module_intro los nts Ps) ->
  InProductsB (product_fdef F) Ps /\
  moduleInSystem (module_intro los nts Ps) S.
Proof.
  intros.
  unfold productInSystemModuleB in *.
  unfold productInModuleB in *.
  apply andb_true_iff in H. destruct H.
  split; auto.
Qed.


Lemma productInSystemModuleB_intro : forall F Ps nts los S,
  InProductsB (product_fdef F) Ps ->
  moduleInSystem (module_intro los nts Ps) S ->
  productInSystemModuleB (product_fdef F) S (module_intro los nts Ps).
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

Lemma lookupFdefViaGVInSystem : forall los nts Ps gl lc fs S fv F,
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaGV (los, nts) Ps gl lc fs fv = Some F ->
  productInSystemModuleB (product_fdef F) S (module_intro los nts Ps).
Proof.
  intros.
  apply lookupFdefViaGV_inv in H0.
  apply productInSystemModuleB_intro; auto.
Qed.


Lemma InBlocksB_uniq : forall lb l1 ps1 cs1 tmn1 ps2 cs2 tmn2,
  uniqBlocks lb ->
  InBlocksB (block_intro l1 ps1 cs1 tmn1) lb ->
  InBlocksB (block_intro l1 ps2 cs2 tmn2) lb ->
  ps1 = ps2 /\ cs1 = cs2 /\ tmn1 = tmn2.
Proof.
  induction lb; intros.
    unfold InBlocksB in *.
    inversion H0.

    inversion H; subst. clear H.
    simpl in *.
    destruct a.
    inversion H2; subst. clear H2.
    assert (J:=H5).
    apply NotIn_NotInBlocksB with (ps:=p)(cs:=c)(tmn:=t) in H5.
    apply orb_prop in H0.
    apply orb_prop in H1.
    destruct H0 as [H0 | H0].    
      apply blockEqB_inv in H0.
      inversion H0; subst. clear H0.
      destruct H1 as [H1 | H1].
        apply blockEqB_inv in H1.
        inversion H1; subst. clear H1.
        auto.

        apply InBlocksB_In in H1.
        contradict H1; auto.
 
      destruct H1 as [H1 | H1].
        apply blockEqB_inv in H1.
        inversion H1; subst. clear H1.
        apply InBlocksB_In in H0.
        contradict H0; auto.

        eapply IHlb; eauto.
          apply NoDup_split in H3.
          destruct H3.
          split; auto.
Qed.

Lemma blockInFdefB_uniq : forall l1 ps1 cs1 tmn1 ps2 cs2 tmn2 F,
  uniqFdef F ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F ->
  blockInFdefB (block_intro l1 ps2 cs2 tmn2) F ->
  ps1 = ps2 /\ cs1 = cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold blockInFdefB in *.
  destruct F. destruct f. destruct H.
  eapply InBlocksB_uniq; eauto.
Qed.

Lemma blockInSystemModuleFdef_uniq : forall l1 ps1 cs1 tmn1 ps2 cs2 tmn2 S M F,
  uniqFdef F ->
  blockInSystemModuleFdef (block_intro l1 ps1 cs1 tmn1) S M F ->
  blockInSystemModuleFdef (block_intro l1 ps2 cs2 tmn2) S M F ->
  ps1 = ps2 /\ cs1 = cs2 /\ tmn1 = tmn2.
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

Lemma productInSystemModuleB_nth_error__blockInSystemModuleFdef : forall fh lb S los nts Ps n B,
  productInSystemModuleB (product_fdef (fdef_intro fh lb)) S (module_intro los nts Ps) ->
  nth_error lb n = Some B ->
  blockInSystemModuleFdef B S (module_intro los nts Ps) (fdef_intro fh lb).
Proof.
  intros.
  apply productInSystemModuleB_inv in H.
  destruct H.
  apply blockInSystemModuleFdef_intro; auto.
  unfold blockInFdefB.
  eapply nth_error__InBlocksB; eauto.
Qed.

(* uniqness *)
Lemma uniqProducts__uniqFdef : forall Ps F,
  uniqProducts Ps ->
  InProductsB (product_fdef F) Ps ->
  uniqFdef F.
Proof.
  induction Ps; intros.
    inversion H0.
    
    simpl in *.
    destruct H.
    apply orb_prop in H0.
    destruct H0; eauto.
      apply productEqB_inv in H0. subst.
      simpl in H. auto.
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

Lemma lookupFdefViaGV_uniq : forall los nts Ps gl lc fs S fv F,
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaGV (los, nts) Ps gl lc fs fv = Some F ->
  uniqFdef F.
Proof.
  intros.
  apply lookupFdefViaGV_inv in H1.
  apply uniqSystem__uniqProducts in H0; auto.
  eapply uniqProducts__uniqFdef; simpl; eauto.
Qed.

Lemma nth_error__lookupAL_genLabel2Block_blocks : forall n lb1 B1,
  uniqBlocks lb1 ->
  nth_error lb1 n = Some B1 ->
  exists l0,  lookupAL _ (genLabel2Block_blocks lb1) l0 = Some B1.
Proof.
  induction n; intros.
    simpl in H0. destruct lb1; inversion H0; subst.
    exists (getBlockLabel B1).
    simpl. destruct B1. simpl.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l0 l0); subst; auto.
      contradict n; auto.

    simpl in H0.
    destruct lb1; inversion H0; subst.
    simpl_env in H.
    assert (J:=H).
    apply uniqBlocks_inv in J. destruct J.
    apply IHn in H0; auto.
    destruct H0 as [l0 H0].
    exists l0. simpl. destruct b.
    destruct H. simpl in *.
    inversion H; subst.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l1); subst; auto.
      apply lookupAL_Some_indom in H0.
      apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H7.
      contradict H0; auto.

      rewrite H2. auto.
Qed.          

Lemma nth_error_uniqBlocks__indom : forall n lb B,
  uniqBlocks lb ->
  nth_error lb n = Some B ->
  (getBlockLabel B) `in` dom (genLabel2Block_blocks lb).
Proof.
  induction n; intros.
    destruct lb; inversion H0; subst.
    simpl in *.
    assert (J:=@getBlockLabel_in_genLabel2Block_block B).
    simpl_env. fsetdec.

    destruct lb; try solve [inversion H0].
    simpl in *.
    simpl_env in H.
    apply uniqBlocks_inv in H. 
    destruct H.
    apply IHn in H0; auto.
    simpl_env. fsetdec.
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
      apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H7.
      simpl in H1. contradict H7; auto.

    destruct n'; auto.
      simpl in *.
      destruct lb1; inversion H1; subst.
      assert (J:=H).
      simpl_env in J. apply uniqBlocks_inv in J. destruct J.
      apply nth_error_uniqBlocks__indom in H0; auto.
      destruct H. simpl in H. destruct B1. inversion H; subst.
      apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H7.
      simpl in H0. contradict H7; auto.
     
      simpl in *.
      destruct lb1; inversion H0.
      simpl_env in H. apply uniqBlocks_inv in H. destruct H.
      apply IHn with (n':=n')(B1:=B1) in H0; auto.
Qed.      
      
Lemma uniqBlocks__uniqBlock : forall lb n l1 ps1 cs1 tmn1,
  uniqBlocks lb ->
  nth_error lb n = Some (block_intro l1 ps1 cs1 tmn1) ->
  NoDup (getCmdsLocs cs1).
Proof.
  induction lb; intros.
    apply nil_nth_error_Some__False in H0.
    inversion H0.

    apply nth_error_cons__inv in H0.
    simpl_env in H. 
    apply uniqBlocks_inv in H.
    destruct H as [J1 J2].
    destruct H0 as [EQ | [n' [EQ H0]]]; subst; eauto.
      unfold uniqBlocks in J1.
      destruct J1.
      simpl in H0.
      simpl_env in H0.
      apply NoDup_inv in H0.
      destruct H0.
      apply NoDup_inv in H1.
      destruct H1; auto.
Qed.

Lemma uniqFdef__uniqBlock : forall fh lb n l1 ps1 cs1 tmn1,
  uniqFdef (fdef_intro fh lb) ->
  nth_error lb n = Some (block_intro l1 ps1 cs1 tmn1) ->
  NoDup (getCmdsLocs cs1).
Proof.
  intros.
  unfold uniqFdef in H. destruct fh. destruct H.
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
    destruct a; simpl in H; eauto.
      destruct f. destruct f.
      simpl in H.
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) i0 fid); 
        simpl in H; subst; eauto.
        inversion H; auto.
Qed.     

Lemma lookupFdecViaIDFromProducts_ideq : forall Ps fid fa rt la va fid',
  lookupFdecViaIDFromProducts Ps fid = 
    Some (fdec_intro (fheader_intro fa rt fid' la va)) ->
  fid = fid'.
Proof.
  induction Ps; intros.
    inversion H.

    simpl in H.
    destruct a; simpl in H; eauto.
      destruct f. destruct f.
      simpl in H.
      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) i0 fid); simpl in H; subst; eauto.
        inversion H; auto.
Qed.     


Lemma eqAL_lookupExFdecViaGV : forall gl TD Ps lc lc' fs fv,
  eqAL _ lc lc' ->
  lookupExFdecViaGV TD Ps gl lc fs fv = lookupExFdecViaGV TD Ps gl lc' fs fv.
Proof.
  intros.
  unfold lookupExFdecViaGV.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma eqAL_lookupExFdefViaGV : forall gl TD Ps lc lc' fs fv,
  eqAL _ lc lc' ->
  lookupFdefViaGV TD Ps gl lc fs fv = lookupFdefViaGV TD Ps gl lc' fs fv.
Proof.
  intros.
  unfold lookupFdefViaGV.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma lookupAL_update_udb_eq : forall ud l0 l1,
  exists ls0, lookupAL _ (update_udb ud l0 l1) l1 = Some ls0 /\ In l0 ls0.
Proof.
  intros.
  unfold update_udb.
  remember (lookupAL (list l) ud l1) as R1.
  destruct R1.
    remember (in_dec l_dec l0 l2) as R2.
    destruct R2.
      exists l2. split; auto.
      exists (l0 :: l2). simpl. split; auto.
        apply lookupAL_updateAddAL_eq; auto.
    remember (in_dec l_dec l0 nil) as R2.
    destruct R2.
      inversion i0.
      exists (l0 :: nil). simpl. split; auto.
        apply lookupAL_updateAddAL_eq; auto.
Qed.  

Lemma update_udb__mono : forall l0 ud l1 l2,
  l0 `in` dom ud ->
  l0 `in` dom (update_udb ud l1 l2).
Proof.
  intros.
  unfold update_udb.
  destruct (in_dec l_dec l1
           match lookupAL (list l) ud l2 with
           | Some ls0 => ls0
           | merror => nil
           end); auto.
    apply updateAddAL_mono; auto.
Qed. 

Lemma lookupAL_update_udb_spec : forall l0 ud l1 l2 re,
  lookupAL _ ud l0 = Some re ->
  exists re', lookupAL _ (update_udb ud l1 l2) l0 = Some re' /\
    incl re re'.
Proof.
  intros.
  unfold update_udb.
  remember (lookupAL (list l) ud l2) as R1.
  destruct R1.
    remember (in_dec l_dec l1 l3) as R2.
    destruct R2.
      exists re. split; auto using incl_refl.
      destruct (eq_atom_dec l2 l0); subst.
        rewrite H in HeqR1. inversion HeqR1; subst.
        exists (l1 :: re). 
        split.
          apply lookupAL_updateAddAL_eq; auto.
          apply incl_tl; auto using incl_refl.
        exists re. 
        split.
          rewrite <- lookupAL_updateAddAL_neq; auto.
          auto using incl_refl.

    remember (in_dec l_dec l1 nil) as R2.
    destruct R2.
      inversion i0.
      destruct (eq_atom_dec l2 l0); subst.
        rewrite H in HeqR1. inversion HeqR1.

        exists re. 
        split.
          rewrite <- lookupAL_updateAddAL_neq; auto.
          auto using incl_refl.
Qed.  

Definition usedef_block_inc (ud1 ud2:usedef_block) :=
  forall l0 l1, 
     lookupAL _ ud1 l0 = Some l1 ->
     exists l2, lookupAL _ ud2 l0 = Some l2 /\ incl l1 l2.

Lemma update_udb_inc : forall ud1 ud2 l1 l2,
  usedef_block_inc ud1 ud2 ->
  usedef_block_inc (update_udb ud1 l1 l2) (update_udb ud2 l1 l2).
Proof.
  unfold update_udb.
  intros.
  remember (lookupAL (list l) ud1 l2) as R1.
  remember (lookupAL (list l) ud2 l2) as R2.
  destruct R1.
    symmetry in HeqR1.
    apply H in HeqR1.
    destruct HeqR1 as [l3' [J1 J2]].
    rewrite J1 in HeqR2. subst.
    destruct (in_dec l_dec l1 l0).
        destruct (in_dec l_dec l1 l3'); auto.
          apply J2 in i0. contradict i0; auto.
        destruct (in_dec l_dec l1 l3').
          intros x ls0 J.
          destruct (eq_atom_dec l2 x); subst.
             rewrite lookupAL_updateAddAL_eq in J. inv J.
             exists l3'. split; auto.
             intros z H0.
             simpl in H0.               
             destruct H0 as [H0 | H0]; subst; eauto.

             rewrite <- lookupAL_updateAddAL_neq in J; auto.
          intros x ls0 J.
          destruct (eq_atom_dec l2 x); subst.
             rewrite lookupAL_updateAddAL_eq in J. inv J.
             rewrite lookupAL_updateAddAL_eq.
             exists (l1::l3'). split; auto.
             intros z H0.
             simpl in H0. simpl.               
             destruct H0 as [H0 | H0]; subst; eauto.

             rewrite <- lookupAL_updateAddAL_neq in J; auto.
             rewrite <- lookupAL_updateAddAL_neq; auto.
    destruct R2. 
      destruct (in_dec l_dec l1 nil).
        inversion i0.
        destruct (in_dec l_dec l1 l0).
          intros x ls0 J.
          destruct (eq_atom_dec l2 x); subst.
             rewrite lookupAL_updateAddAL_eq in J. inv J.
             exists l0. split; auto.
             intros z H0.
             simpl in H0.               
             destruct H0 as [H0 | H0]; subst; auto.
               inversion H0.
             rewrite <- lookupAL_updateAddAL_neq in J; auto.
          intros x ls0 J.
          destruct (eq_atom_dec l2 x); subst.
             rewrite lookupAL_updateAddAL_eq in J. inv J.
             rewrite lookupAL_updateAddAL_eq.
             exists (l1::l0). split; auto.
             intros z H0.
             simpl in H0. simpl.               
             destruct H0 as [H0 | H0]; subst; auto.
               inversion H0.
             rewrite <- lookupAL_updateAddAL_neq in J; auto.
             rewrite <- lookupAL_updateAddAL_neq; auto.
      destruct (in_dec l_dec l1 nil).
        inversion i0.
        destruct (in_dec l_dec l1 nil).
          inversion i0.
          intros x ls0 J.
          destruct (eq_atom_dec l2 x); subst.
             rewrite lookupAL_updateAddAL_eq in J. inv J.
             rewrite lookupAL_updateAddAL_eq.
             exists (l1::nil). split; auto using incl_refl.

             rewrite <- lookupAL_updateAddAL_neq in J; auto.
             rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma genBlockUseDef_block_inc : forall b ud1 ud2,
  usedef_block_inc ud1 ud2 ->
  usedef_block_inc (genBlockUseDef_block b ud1) (genBlockUseDef_block b ud2).
Proof.
  intros. 
  destruct b. simpl. 
  destruct t; auto.
    apply update_udb_inc; auto.
    apply update_udb_inc; auto.
    apply update_udb_inc; auto.
Qed.

Lemma genBlockUseDef_blocks_inc : forall bs ud1 ud2,
  usedef_block_inc ud1 ud2 ->
  usedef_block_inc (genBlockUseDef_blocks bs ud1) (genBlockUseDef_blocks bs ud2).
Proof.
  induction bs; simpl; intros; auto.
    apply IHbs.
    apply genBlockUseDef_block_inc; auto.
Qed.

Lemma hasNonPredecessor__mono : forall b bs ud,
  hasNonePredecessor b (genBlockUseDef_blocks bs ud) = true ->
  hasNonePredecessor b (genBlockUseDef_blocks bs nil) = true.
Proof.
  unfold hasNonePredecessor.
  unfold predOfBlock.
  intros.
  assert (usedef_block_inc nil ud) as J0.
    intros x l0 J. inversion J.
  assert (J:=@genBlockUseDef_blocks_inc bs nil ud J0).
  remember (lookupAL (list l) (genBlockUseDef_blocks bs ud) (getBlockLabel b))
    as R1.  
  remember (lookupAL (list l) (genBlockUseDef_blocks bs nil) (getBlockLabel b))
    as R2.
  destruct R1.
    destruct R2; auto.
      destruct l1; auto.
        destruct l0; inversion H.
          symmetry in HeqR2.
          apply J in HeqR2. 
          destruct HeqR2 as [l3 [J1 J2]].
          rewrite J1 in HeqR1. inv HeqR1.
          assert (In l1 (l1::l2)) as J'. simpl. auto.
          apply J2 in J'. inv J'.
    destruct R2; auto.
      destruct l0; auto.
        symmetry in HeqR2.
        apply J in HeqR2. 
        destruct HeqR2 as [l3 [J1 J2]].
        rewrite J1 in HeqR1. inv HeqR1.
Qed.

Lemma getValueViaLabelFromValuels__nth_list_value_l : forall
  (l1 : l)  v vls
  (J : getValueViaLabelFromValuels vls l1 = Some v),
  exists n, nth_list_value_l n vls = Some (v, l1).
Proof.
  intros.
  induction vls; intros; simpl in *.
    inversion J.

    destruct (l0 == l1); subst.
      inversion J; subst; simpl in *.
      exists 0%nat. auto.

      destruct IHvls as [n' IHvls]; auto.
      exists (S n'). simpl. auto.
Qed.

Lemma genBlockUseDef_blocks__mono : forall bs ud l0,
  l0 `in` dom ud ->
  l0 `in` dom (genBlockUseDef_blocks bs ud).
Proof.
  induction bs; intros ud l0 Hin; simpl in *; auto.  
    destruct a; simpl.
    destruct t; simpl; auto.
      apply IHbs. 
        apply update_udb__mono; auto.
        apply update_udb__mono; auto.
      apply IHbs. 
        apply update_udb__mono; auto.
Qed.        

Lemma lookupAL_genBlockUseDef_blocks_spec : forall bs l0 ud re,
  lookupAL _ ud l0 = Some re ->
  exists re', lookupAL _ (genBlockUseDef_blocks bs ud) l0 = Some re' /\
    incl re re'.
Proof.
  induction bs; intros ud l0 re Hin; simpl in *; auto.  
    exists re. split; auto using incl_refl.

    destruct a.
    destruct t; simpl; auto.
      apply lookupAL_update_udb_spec with (l1:=l1)(l2:=l3) in Hin.
      destruct Hin as [re1 [Hin Hinc1]].
      apply lookupAL_update_udb_spec with (l1:=l1)(l2:=l2) in Hin.
      destruct Hin as [re2 [Hin Hinc2]].
      apply IHbs in Hin.
      destruct Hin as [re3 [Hin Hinc3]].
      exists re3. split; eauto using incl_tran.

      apply lookupAL_update_udb_spec with (l1:=l1)(l2:=l2) in Hin.
      destruct Hin as [re1 [Hin Hinc1]].
      apply IHbs in Hin.
      destruct Hin as [re2 [Hin Hinc2]].
      exists re2. split; eauto using incl_tran.
Qed.        

Lemma getIncomingValuesForBlockFromPHINodes_spec : forall ps TD b gl lc lc'
    id1,
  Some lc' = getIncomingValuesForBlockFromPHINodes TD ps b gl lc ->
  In id1 (getPhiNodesIDs ps) ->
  exists gv, lookupAL _ lc' id1 = Some gv.  
Proof.    
  induction ps; intros; simpl in *.
    inversion H0.

    destruct a.
    simpl in H0.
    destruct H0 as [H0 | H0]; subst.
      destruct (getValueViaBlockFromValuels l0 b); try solve [inversion H].   
        destruct (getOperandValue TD v lc gl); inversion H; subst. 
        destruct (getIncomingValuesForBlockFromPHINodes TD ps b gl lc);
          inversion H1; subst.         
        exists g. simpl. 
        destruct (id1==id1); auto.
          contradict n; auto.

      destruct (getValueViaBlockFromValuels l0 b); try solve [inversion H].   
        destruct (getOperandValue TD v lc gl); inversion H; subst. 
        remember (getIncomingValuesForBlockFromPHINodes TD ps b gl lc) 
          as R.
        destruct R; inversion H2; subst.         
        simpl.
        destruct (id1==i0); subst; eauto.
Qed.
    
Lemma updateValuesForNewBlock_spec1 : forall rs lc id1 gv,
  lookupAL _ rs id1 = Some gv ->
  lookupAL _ (updateValuesForNewBlock rs lc) id1 = Some gv.
Proof.  
  induction rs; intros; simpl in *.   
    inversion H.

    destruct a.
    destruct (id1==a); subst.
      inversion H; subst. apply lookupAL_updateAddAL_eq; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma updateValuesForNewBlock_spec2 : forall rs lc id1 gv,
  lookupAL _ lc id1 = Some gv ->
  exists gv', lookupAL _ (updateValuesForNewBlock rs lc) id1 = Some gv'.
Proof.  
  induction rs; intros; simpl in *.   
    exists gv. auto.

    destruct a.
    destruct (id1==i0); subst.
      exists g. apply lookupAL_updateAddAL_eq; auto.
      rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma InPhiNodes_lookupTypViaIDFromPhiNodes : forall ps id1,
  In id1 (getPhiNodesIDs ps) ->
  exists t, lookupTypViaIDFromPhiNodes ps id1 = Some t.
Proof.
  induction ps; intros; simpl in *.
    inversion H. 

    destruct H as [H | H]; subst.
      destruct a. simpl. unfold lookupTypViaIDFromPhiNode. simpl.
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
  Some (block_intro l' ps cs tmn) = lookupBlockViaLabelFromFdef f l' ->
  In id1 (getPhiNodesIDs ps) ->
  exists t, lookupTypViaIDFromFdef f id1 = Some t.
Proof.
  intros.
  destruct f. destruct f.
  simpl in *.
  destruct (lookupTypViaIDFromArgs a id1).
    exists t0. auto.

    induction b; simpl in *.
      inversion H.
    
      destruct a0. simpl in *.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l' l0); subst.
        inversion H; subst.
        apply InPhiNodes_lookupTypViaIDFromPhiNodes in H0.
        destruct H0 as [t1 H0].
        rewrite H0. exists t1. auto.

        apply IHb in H.
        destruct H as [t1 H].
        rewrite H. 
        destruct (lookupTypViaIDFromPhiNodes p id1).
          exists t2. auto.
          destruct (lookupTypViaIDFromCmds c id1).
            exists t2. auto.
            destruct (lookupTypViaIDFromTerminator t0 id1).
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

Lemma initLocals_spec : forall TD la gvs id1 lc,
  In id1 (getArgsIDs la) ->
  initLocals TD la gvs = Some lc ->
  exists gv, lookupAL _ lc id1 = Some gv.
Proof.
  unfold initLocals.
  induction la; intros; simpl in *.
    inversion H.

    destruct a as [[t c] id0].  
    simpl in H.
    destruct H as [H | H]; subst; simpl.
      destruct gvs. 
        remember (_initializeFrameValues TD la nil nil) as R1.
        destruct R1; tinv H0.
        remember (gundef TD t) as R2.
        destruct R2; inv H0.
        exists (? g0 # t ?). apply lookupAL_updateAddAL_eq; auto.      

        remember (_initializeFrameValues TD la gvs nil) as R1.
        destruct R1; tinv H0.
        remember (fit_gv TD g t) as R2.
        destruct R2; inv H0.
        exists (? g1 # t ?). apply lookupAL_updateAddAL_eq; auto.      

      destruct (eq_atom_dec id0 id1); subst.
        destruct gvs.
          remember (_initializeFrameValues TD la nil nil) as R1.
          destruct R1; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          exists (? g0 # t ?). apply lookupAL_updateAddAL_eq; auto.      

          remember (_initializeFrameValues TD la gvs nil) as R1.
          destruct R1; tinv H0.
          remember (fit_gv TD g t) as R2.
          destruct R2; inv H0.
          exists (? g1 # t ?). apply lookupAL_updateAddAL_eq; auto.      

        destruct gvs.
          remember (_initializeFrameValues TD la nil nil) as R1.
          destruct R1; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1]. 
          exists gv. rewrite <- lookupAL_updateAddAL_neq; auto.

          remember (_initializeFrameValues TD la gvs nil) as R1.
          destruct R1; tinv H0.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1]. 
          remember (fit_gv TD g t) as R2.
          destruct R2; inv H0.
          exists gv. rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma InBlocksB__lookupAL_genLabel2Block_blocks : forall lb1 l' ps' cs' tmn',
  uniqBlocks lb1 ->
  InBlocksB (block_intro l' ps' cs' tmn') lb1 ->
  lookupAL _ (genLabel2Block_blocks lb1) l' = Some (block_intro l' ps' cs' tmn').
Proof.
  induction lb1; intros.
    inversion H0.

    simpl in H0. destruct a. simpl.
    apply orb_prop in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0.
      inv H0.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l0); subst; 
        auto.
        contradict n; auto.

        simpl_env in H.
        assert (J:=H).
        apply uniqBlocks_inv in J. destruct J.
        eapply IHlb1 in H2; eauto.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l' l0); subst;
          auto.

      destruct H.
      simpl in H. inv H.
      apply lookupAL_Some_indom in H2.
      apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H6.
      contradict H6; auto.
Qed.          

Lemma blockInFdefB_lookupBlockViaLabelFromFdef : forall F l' ps' cs' tmn',
  uniqFdef F ->
  blockInFdefB (block_intro l' ps' cs' tmn') F ->
  lookupBlockViaLabelFromFdef F l' = Some (block_intro l' ps' cs' tmn').
Proof.
  intros. destruct F. destruct f. destruct H. simpl in *.
  apply InBlocksB__lookupAL_genLabel2Block_blocks; auto.
Qed.

Lemma lookupBlockViaIDFromFdef__blockInFdefB : forall F id1 B,
  lookupBlockViaIDFromFdef F id1 = Some B ->
  blockInFdefB B F.
Proof.         
  intros.
  destruct F.
  simpl in *.
  induction b; simpl in *.
    inversion H.

    destruct a. simpl in *.
    destruct (in_dec eq_dec id1 (getPhiNodesIDs p ++ getCmdsIDs c)).
      inv H. apply orb_true_iff. left.
      apply blockEqB_refl.

      apply orb_true_iff. right. apply IHb in H; auto.
Qed.

Lemma lookupBlockViaIDFromFdef__InGetBlockIDs : forall F id1 B,
  lookupBlockViaIDFromFdef F id1 = Some B ->
  In id1 (getBlockIDs B).
Proof.         
  intros.
  destruct F.
  simpl in *.
  induction b; simpl in *.
    inversion H.

    destruct a. simpl in *.
    remember (in_dec eq_dec id1 (getPhiNodesIDs p ++ getCmdsIDs c)) as R.
    destruct R; eauto.
      inv H. auto.
Qed.

Lemma getValueViaLabelFromValuels__In : forall vls v l1 vs1 ls1,
  getValueViaLabelFromValuels vls l1 = Some v ->
  split (unmake_list_value_l vls) = (vs1, ls1) ->
  In l1 ls1.
Proof.
  induction vls; intros; simpl in *.
    inversion H.

    remember (split (unmake_list_value_l vls)) as R.
    destruct R.
    inv H0.
    destruct (l0 == l1); subst.
      simpl. auto.

      simpl. right. eauto.
Qed.

Lemma In__getValueViaLabelFromValuels : forall vls l1 vs1 ls1,
  In l1 ls1 ->
  split (unmake_list_value_l vls) = (vs1, ls1) ->
  NoDup ls1 ->
  exists v, getValueViaLabelFromValuels vls l1 = Some v.
Proof.
  induction vls; intros; simpl in *.
    inv H0. inversion H.
   
    destruct (l0 == l1); subst; eauto.
    remember (split (unmake_list_value_l vls)) as R.
    destruct R.
    symmetry in HeqR.
    inv H0. inv H1.
    simpl in H.
    destruct H as [H | H]; subst.
      contradict n; auto.
    
      eapply IHvls in H; eauto.
Qed.      

Lemma successors_terminator__successors_blocks : forall
  (bs : blocks)
  (l0 : l)
  (cs : phinodes)
  (ps : cmds)
  (tmn : terminator)
  (l1 : l)
  (HuniqF : uniqBlocks bs)
  (HbInF : InBlocksB (block_intro l0 cs ps tmn) bs)
  (Hin : In l1 (successors_terminator tmn)),
  successors_terminator tmn = (successors_blocks bs) !!! l0.
Proof.
  intros.
  induction bs.
    inversion HbInF.
  
    assert (J:=HuniqF).
    simpl_env in J.
    apply uniqBlocks_inv in J.
    destruct J as [J1 J2]. 
    simpl in *.
    apply orb_prop in HbInF.
    destruct a.
    destruct HbInF as [HbInF | HbInF].
      unfold blockEqB in HbInF.
      apply sumbool2bool_true in HbInF. inv HbInF.
      unfold successors_list.
      rewrite ATree.gss. auto.
  
      apply IHbs in J2; auto.
      unfold successors_list in *.
      destruct HuniqF as [J _].
      inv J.
      rewrite ATree.gso; auto.
        clear - HbInF H1. 
        eapply InBlocksB__NotIn; eauto.
Qed.

Lemma successors_predOfBlock : forall f l1 ps1 cs1 tmn1 l0 ps0 cs0 tmn0,
  uniqFdef f ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  In l0 (successors_terminator tmn1) ->
  In l1 (predOfBlock (block_intro l0 ps0 cs0 tmn0) (genBlockUseDef_fdef f)).
Proof.
  unfold predOfBlock.
  destruct f. destruct f. intros.
  destruct H as [H _].
  generalize dependent l1.
  generalize dependent ps1.
  generalize dependent cs1.
  generalize dependent tmn1.
  generalize dependent l0.
  generalize dependent ps0.
  generalize dependent cs0.
  generalize dependent tmn0.
  induction b; intros; simpl in *.
    inversion H0.

    assert (G:=H). simpl_env in G.
    apply uniqBlocks_inv in G.
    destruct G as [G1 G2].
    destruct a0. simpl.
    apply orb_prop in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0.
      inv H0.
      destruct t0; auto.
        apply IHb with (ps1:=p)(cs1:=c)(tmn1:=insn_return i0 t0 v0); auto.
        apply IHb with (ps1:=p)(cs1:=c)(tmn1:=insn_return_void i0); auto.

        simpl in H1.
        destruct H1 as [H1 | [H1 | H1]]; subst.
          assert (J:=@lookupAL_update_udb_eq (update_udb nil l2 l3) l2 l0).
          destruct J as [ls0 [J1 J2]].
          apply lookupAL_genBlockUseDef_blocks_spec with (bs:=b) in J1; auto.
          destruct J1 as [ls1 [J1 J3]].
          rewrite J1. apply J3; auto.

          assert (J:=@lookupAL_update_udb_eq nil l2 l0).
          destruct J as [ls0 [J J0]].
          apply lookupAL_update_udb_spec with (l1:=l2)(l2:=l1) in J; auto.
          destruct J as [ls1 [J J1]].
          apply lookupAL_genBlockUseDef_blocks_spec with (bs:=b) in J; auto.
          destruct J as [ls2 [J J2]].
          rewrite J. apply J2. apply J1. auto.

          inversion H1.
        simpl in H1.
        destruct H1 as [H1 | H1]; subst.
          assert (J:=@lookupAL_update_udb_eq nil l2 l0).
          destruct J as [ls0 [J J0]].
          apply lookupAL_genBlockUseDef_blocks_spec with (bs:=b) in J; auto.
          destruct J as [ls2 [J J2]].
          rewrite J. apply J2. auto.

          inversion H1.

        apply IHb with (ps1:=p)(cs1:=c)(tmn1:=insn_unreachable i0); auto.

      eapply IHb in H1; eauto.
        remember (lookupAL (list l) (genBlockUseDef_blocks b nil) l0) as R.
        destruct R; try solve [inversion H1].
        destruct H as [J1 J2].
        simpl in J1.
        inv J1.
        apply InBlocksB_In in H0.
        destruct (eq_atom_dec l1 l2); subst.
          contradict H0; auto.

          clear - HeqR H1.
          simpl.
          assert (usedef_block_inc nil 
            (match t0 with
             | insn_return _ _ _ => nil
             | insn_return_void _ => nil
             | insn_br _ _ l4 l5 => update_udb (update_udb nil l2 l5) l2 l4
             | insn_br_uncond _ l4 => update_udb nil l2 l4
             | insn_unreachable _ => nil
             end)) as J.
            intros x A J. inversion J.
          apply genBlockUseDef_blocks_inc with (bs:=b) in J.
          symmetry in HeqR.
          apply J in HeqR.
          destruct HeqR as [l4 [J1 J2]].
          rewrite J1. apply J2 in H1; auto.
Qed.

Lemma in_app_list_value_right : forall l1 v l2,
  In v (unmake_list_value l2) ->
  In v (unmake_list_value (app_list_value l1 l2)).
Proof.
  induction l1; simpl; intros; auto.
Qed.    

Lemma app_list_value_assoc : forall l1 l2 l3,
  app_list_value l1 (app_list_value l2 l3) =
    app_list_value (app_list_value l1 l2) l3.
Proof.
  induction l1; intros; simpl; auto.
    rewrite IHl1; auto.
Qed.

Lemma cons_eq_app_list_value : forall a1 l1,
  Cons_list_value a1 l1 = app_list_value (Cons_list_value a1 Nil_list_value) l1.
Proof.
  intros. simpl. auto.
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

Lemma valueInValues__InOps : forall vid l0,
  In (value_id vid) (unmake_list_value l0) ->
  In vid (values2ids (unmake_list_value l0)).
Proof.
  induction l0; intros; simpl in *; auto.
    destruct H as [H | H]; subst; simpl; auto.
    destruct v; simpl; eauto.
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
    destruct H0 as [H0 | H0]; subst; eauto.
      apply getCmdLoc_getCmdID in H; auto.   
Qed.

Lemma in_getBlockLocs__in_getBlocksLocs : forall bs b i0,
  In i0 (getBlockLocs b) ->
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

Lemma NotInPhiNodesIDs__lookupTypViaIDFromPhiNodes : forall la id1,
  ~ In id1 (getPhiNodesIDs la) ->
  lookupTypViaIDFromPhiNodes la id1 = None.
Proof.
  induction la; intros; simpl in *; auto.
    destruct a. unfold lookupTypViaIDFromPhiNode.
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
  ~ In i0 (getBlockLocs b) ->
  lookupTypViaIDFromBlock b i0 = None.
Proof.
  intros.
  destruct b. simpl in *.
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
  lookupTypViaIDFromBlock b i0 = Some t0 -> In i0 (getBlockLocs b).
Proof.
  intros.
  destruct (In_dec eq_atom_dec i0 (getBlockLocs b)); auto.
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
    apply NoDup_inv in H0. destruct H0.
    apply orb_prop in H1.
    destruct H1 as [H1 | H1]; eauto.
      apply blockEqB_inv in H1. subst.
      rewrite H. auto.
    
      assert (H':=H).
      apply lookupTypViaIDFromBlock__inBlock in H.
      apply NoDup_disjoint with (i0:=i0) in J; 
        eauto using in_getBlockLocs__in_getBlocksLocs.
      apply notInBlock__lookupTypViaIDFromBlock in J.
      rewrite J. eauto.
Qed.

Lemma NoDup__InBlocksB : forall bs b,
  NoDup (getBlocksLocs bs) ->
  InBlocksB b bs = true ->
  NoDup (getBlockLocs b).
Proof.
  induction bs; simpl; intros.
    inversion H0.

    apply NoDup_inv in H. destruct H.
    apply orb_prop in H0.
    destruct H0 as [H0 | H0]; eauto.
      apply blockEqB_inv in H0. subst. auto.
Qed.

Lemma InCmds_lookupTypViaIDFromPhiNodes : forall cs id1 c t1,
  NoDup (getCmdsLocs cs) ->
  In c cs ->
  getCmdID c = Some id1 ->
  getCmdTyp c = Some t1 ->
  lookupTypViaIDFromCmds cs id1 = Some t1.
Proof.
  induction cs; intros.
    inversion H0.

    simpl in *.
    inv H. unfold lookupTypViaIDFromCmd.
    destruct H0 as [H0 | H0]; subst.
      rewrite H2.
      apply getCmdLoc_getCmdID in H1.
      rewrite H1.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 id1); subst;
        auto.
        contradict n; auto.

      remember (getCmdTyp a) as R.
      destruct R; eauto.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 (getCmdLoc a));
        subst; eauto.

        apply getCmdID_in_getCmdsLocs with (i0:=getCmdLoc a) in H0; auto.
        contradict H0; auto.
Qed.

Lemma uniqF__lookupTypViaIDFromFdef : forall l1 ps1 cs1 tmn1 f c i0 t0,
  uniqFdef f ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true -> 
  In c cs1 ->
  getCmdID c = Some i0 ->
  getCmdTyp c = Some t0 ->
  lookupTypViaIDFromFdef f i0 = Some t0.
Proof.
  intros.
  destruct f. destruct f. inversion H.
  apply NoDup_inv in H5.
  destruct H5.
  simpl in *.
  assert (In i0 (getCmdsLocs cs1)) as HInCs.
    eapply getCmdID_in_getCmdsLocs in H1; eauto.
  assert (In i0 (getBlocksLocs b)) as Hin.
    eapply in_getBlockLocs__in_getBlocksLocs in H0; eauto.
    simpl. apply in_or_app. right. apply in_or_app; auto.
  destruct H as [J1 J2].
  assert (~ In i0 (getArgsIDs a)) as Hnotin.
    eapply NoDup_disjoint; eauto.
  apply NotInArgsIDs_lookupTypViaIDFromArgs in Hnotin.
  rewrite Hnotin.
  eapply lookupTypViaIDFromBlock__inBlocks; eauto.
  simpl.
  apply NoDup__InBlocksB in H0; auto.
  simpl in H0.
  rewrite_env ((getPhiNodesIDs ps1 ++ getCmdsLocs cs1) ++ [getTerminatorID tmn1])
    in H0.
  apply NoDup_inv in H0. destruct H0 as [H0 _].
  assert (~ In i0 (getPhiNodesIDs ps1)) as HnotinPs.
    eapply NoDup_disjoint; eauto.
  apply NotInPhiNodesIDs__lookupTypViaIDFromPhiNodes in HnotinPs.
  rewrite HnotinPs.
  apply NoDup_inv in H0. destruct H0 as [_ H0]. 
  erewrite InCmds_lookupTypViaIDFromPhiNodes; eauto.
Qed.

Lemma uniqFdef__uniqBlockLocs : forall F b1,
  uniqFdef F -> blockInFdefB b1 F -> NoDup (getBlockLocs b1).
Proof.
  intros.
  destruct F. destruct f.
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

Lemma lookupTypViaIDFromBlocks__inBlocks : forall bs b i0,
  NoDup (getBlocksLocs bs) ->
  InBlocksB b bs = true ->
  In i0 (getBlockLocs b) ->
  lookupTypViaIDFromBlocks bs i0 = lookupTypViaIDFromBlock b i0.
Proof.
  induction bs; simpl; intros.
    inversion H0.

    assert (J:=H).
    apply NoDup_inv in H. destruct H.
    apply orb_prop in H0. 
    destruct H0 as [H0 | H0]; eauto.
      apply blockEqB_inv in H0. subst.
      apply NoDup_disjoint' with (i0:=i0) in J; auto.
      apply notInBlocks__lookupTypViaIDFromBlocks in J.
      rewrite J. destruct (lookupTypViaIDFromBlock a i0); auto.

      apply NoDup_disjoint with (i0:=i0) in J;
        eauto using in_getBlockLocs__in_getBlocksLocs.
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
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true -> 
  In c cs1 ->
  getCmdID c = Some i0 ->
  lookupTypViaIDFromFdef f i0 = getCmdTyp c.
Proof.
  intros.
  destruct f. destruct f. inversion H.
  apply NoDup_inv in H4.
  destruct H4.
  simpl in *.
  assert (In i0 (getCmdsLocs cs1)) as HInCs.
    eapply getCmdID_in_getCmdsLocs in H1; eauto.
  assert (In i0 (getBlocksLocs b)) as Hin.
    eapply in_getBlockLocs__in_getBlocksLocs in H0; eauto.
    simpl. apply in_or_app. right. apply in_or_app; auto.
  destruct H as [J1 J2].
  assert (~ In i0 (getArgsIDs a)) as Hnotin.
    eapply NoDup_disjoint; eauto.
  apply NotInArgsIDs_lookupTypViaIDFromArgs in Hnotin.
  rewrite Hnotin.
  erewrite lookupTypViaIDFromBlocks__inBlocks; eauto. 
    simpl.
    apply NoDup__InBlocksB in H0; auto.
    assert (J:=H0).
    rewrite_env ((getPhiNodesIDs ps1 ++ getCmdsLocs cs1) ++ 
      [getTerminatorID tmn1]) in H0.
    apply NoDup_inv in H0. destruct H0 as [H0 _].
    assert (~ In i0 (getPhiNodesIDs ps1)) as HnotinPs.
      eapply NoDup_disjoint in H0; eauto.
    apply NotInPhiNodesIDs__lookupTypViaIDFromPhiNodes in HnotinPs.
    rewrite HnotinPs.
    apply NoDup_inv in H0. destruct H0 as [_ H0]. 
    erewrite InCmds_lookupTypViaIDFromCmds'; eauto.
    destruct (getCmdTyp c); auto.
      unfold lookupTypViaIDFromTerminator.
      destruct (i0 == getTerminatorID tmn1); subst; auto.
        clear - J HInCs.
        simpl in J.
        apply NoDup_inv in J. destruct J as [_ J].
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
  destruct F. destruct f. simpl in *.
  destruct Huniq as [Huniq1 Huniq2].
  destruct Huniq1 as [_ Huniq1].
  assert (Huniq1':=Huniq1).
  eapply NoDup__InBlocksB with (b:=b1) in Huniq1; eauto.
  destruct b1. simpl in *.
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

    eapply in_getBlockLocs__in_getBlocksLocs; eauto.
      simpl. apply in_or_app. auto.
Qed.

Lemma getArgsIDs_app : forall l1 l2,
  getArgsIDs (l1++l2) = getArgsIDs l1 ++ getArgsIDs l2.
Proof.
  induction l1; simpl; intros; auto.
    destruct a. simpl. rewrite IHl1; auto.
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

Lemma NoDupBlockLocs__notInCmds : forall l2 ps2 cs2' c' tmn',
  NoDup (getBlockLocs (block_intro l2 ps2 (cs2' ++ [c']) tmn')) ->
  ~ In (getCmdLoc c') (getCmdsLocs cs2').
Proof.
  intros.
  simpl in H.
  apply NoDup_inv in H.
  destruct H as [_ J].
  apply NoDup_inv in J.
  destruct J as [J _].
  rewrite getCmdsLocs_app in J.
  simpl in J.
  apply NoDup_last_inv in J. auto.
Qed.

Lemma NoDupBlockLocs__NoDupCmds : forall l2 ps2 cs2' tmn',
  NoDup (getBlockLocs (block_intro l2 ps2 cs2' tmn')) ->
  NoDup (getCmdsLocs cs2').
Proof.
  intros.
  simpl in H.
  apply NoDup_inv in H.
  destruct H as [_ J].
  apply NoDup_inv in J.
  destruct J as [J _]. auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
