Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import Coq.Program.Equality.
Require Import CoqListFacts.
Require Import Metatheory.
Require Import assoclist.
Require Import genericvalues.

Export LLVMsyntax.
Export LLVMlib.

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

Lemma list_id_lEqB_refl : forall l0, list_id_lEqB l0 l0.
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

Lemma list_id_lEqB_inv : forall l1 l2, list_id_lEqB l1 l2 -> l1=l2.
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

Lemma getCmdsIDs_app : forall cs1 cs2,
  getCmdsIDs (cs1++cs2) = getCmdsIDs cs1++getCmdsIDs cs2.
Proof.
  induction cs1; intros; auto.
    simpl. rewrite IHcs1. auto.
Qed.

Lemma getBlocksIDs_app : forall lb1 lb2,
  getBlocksIDs (lb1++lb2) = getBlocksIDs lb1++getBlocksIDs lb2.
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
  destruct (l0==l1); subst; inversion H; auto.
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
    rewrite getBlocksIDs_app in H1.
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
      destruct (l0 == l1); subst.
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
  destruct F.
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
    destruct a.
      apply IHPs in H. auto.
      apply IHPs in H. auto.
      destruct (getFdefID f==fid); subst.
        inversion H; subst.
        left. apply productEqB_refl.

        apply IHPs in H. auto. 
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

Lemma blockInSystemModuleFdef_inv : forall B F Ps TD S,
  blockInSystemModuleFdef B S (module_intro TD Ps) F ->
  blockInFdefB B F /\
  InProductsB (product_fdef F) Ps /\
  moduleInSystem (module_intro TD Ps) S /\
  productInSystemModuleB (product_fdef F) S (module_intro TD Ps).
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

Lemma blockInSystemModuleFdef_intro : forall B F Ps TD S,
  blockInFdefB B F ->
  InProductsB (product_fdef F) Ps ->
  moduleInSystem (module_intro TD Ps) S ->
  blockInSystemModuleFdef B S (module_intro TD Ps) F.
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

Lemma entryBlockInSystemBlockFdef : forall TD Ps S fid F B,
  moduleInSystem (module_intro TD Ps) S ->
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  getEntryBlock F = Some B ->
  blockInSystemModuleFdef B S (module_intro TD Ps) F.
Proof.
  intros.
  apply lookupFdefViaIDFromProducts_inv in H0.
  apply entryBlockInFdef in H1.  
  apply blockInSystemModuleFdef_intro; auto.
Qed.

Lemma productInSystemModuleB_inv : forall F Ps TD S,
  productInSystemModuleB (product_fdef F) S (module_intro TD Ps) ->
  InProductsB (product_fdef F) Ps /\
  moduleInSystem (module_intro TD Ps) S.
Proof.
  intros.
  unfold productInSystemModuleB in *.
  unfold productInModuleB in *.
  apply andb_true_iff in H. destruct H.
  split; auto.
Qed.


Lemma productInSystemModuleB_intro : forall F Ps TD S,
  InProductsB (product_fdef F) Ps ->
  moduleInSystem (module_intro TD Ps) S ->
  productInSystemModuleB (product_fdef F) S (module_intro TD Ps).
Proof.
  intros.
  unfold productInSystemModuleB.
  unfold productInModuleB.
  eapply andb_true_iff.
  split; auto.
Qed.

Lemma lookupFdefViaIDFromProductsInSystem : forall TD Ps S fid F,
  moduleInSystem (module_intro TD Ps) S ->
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  productInSystemModuleB (product_fdef F) S (module_intro TD Ps).
Proof.
  intros.
  apply lookupFdefViaIDFromProducts_inv in H0.
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
  destruct F.
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
      exists 0. simpl; auto.

      apply IHlb in H; auto.
      destruct H as [n H].
      exists (S n). simpl. auto.
Qed.

Lemma productInSystemModuleB_nth_error__blockInSystemModuleFdef : forall fh lb S TD Ps n B,
  productInSystemModuleB (product_fdef (fdef_intro fh lb)) S (module_intro TD Ps) ->
  nth_error lb n = Some B ->
  blockInSystemModuleFdef B S (module_intro TD Ps) (fdef_intro fh lb).
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

Lemma uniqSystem__uniqProducts : forall S TD Ps,
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
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

Lemma lookupFdefViaIDFromProducts_uniq : forall TD Ps S fid F,
  uniqSystem S ->
  moduleInSystem (module_intro TD Ps) S ->
  lookupFdefViaIDFromProducts Ps fid = Some F ->
  uniqFdef F.
Proof.
  intros.
  apply lookupFdefViaIDFromProducts_inv in H1.
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
    destruct (l0==l1); subst; auto.
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
  NoDup (getCmdsIDs cs1).
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
  NoDup (getCmdsIDs cs1).
Proof.
  intros.
  unfold uniqFdef in H.
  eapply uniqBlocks__uniqBlock; eauto.
Qed.


  
