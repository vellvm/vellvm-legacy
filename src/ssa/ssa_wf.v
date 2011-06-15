Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
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
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import ssa_static.
Require Import ssa_dynamic.
Require Import ssa_props.
Require Import ssa_analysis.

Export LLVMwf.
Export AtomSet.

Fixpoint cmds_dominates_cmd (cs:cmds) (id0:id) : list atom :=
match cs with
| nil => nil
| c1::cs' => 
    let ctx := cmds_dominates_cmd cs' id0 in
    if eq_atom_dec (getCmdLoc c1) id0 then nil
    else
      match getCmdID c1 with
      | Some id1 => id1::ctx
      | None => ctx
      end
end.

Definition inscope_of_block (f:fdef) (l1:l) (opt_ctx:option (list atom)) (lbl:l)
  :=
  match opt_ctx with
  | Some ctx =>
     match lookupBlockViaLabelFromFdef f lbl with
     | None => None
     | Some b => 
         if eq_atom_dec lbl l1 then Some ctx
         else Some (getBlockIDs b ++ ctx)
     end
  | None => None
  end.

Definition inscope_of_cmd (f:fdef) (b1:block) (c:cmd) : option (list atom) :=
let id0 := getCmdLoc c in
let '(block_intro l1 ps cs _) := b1 in
let '(fdef_intro (fheader_intro _ _ _ la _) _) := f in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l1 dt in
fold_left (inscope_of_block f l1) els
  (Some (getPhiNodesIDs ps ++ cmds_dominates_cmd cs id0 ++ getArgsIDs la))
.

Definition inscope_of_tmn (f:fdef) (b1:block) (tmn:terminator) 
  : option (list atom) :=
let '(block_intro l1 ps cs _) := b1 in
let '(fdef_intro (fheader_intro _ _ _ la _) _) := f in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l1 dt in
fold_left (inscope_of_block f l1) els
  (Some (getPhiNodesIDs ps ++ getCmdsIDs cs ++ getArgsIDs la))
.

Definition defs_dominate (f:fdef) (curb incomingb:block) (i:insn) 
  : option (list atom) :=
match i with
| insn_phinode p => 
    let '(block_intro _ _ _ tmn) := incomingb in
    inscope_of_tmn f incomingb tmn
| insn_cmd c => inscope_of_cmd f curb c
| insn_terminator tmn => inscope_of_tmn f curb tmn
end.

Export LLVMgv.
Export LLVMopsem.

(* The relation says that any value can be of any typ, which is exactly true
   for an LLVM that allows cast between any pointer types. Type safety needs 
   a subtyping relation w.r.t data type layout. *)
Inductive wf_genericvalue : GenericValue -> typ -> Prop :=
| wf_genericvalue_intro : forall gv t, wf_genericvalue gv t.

Hint Constructors wf_genericvalue.

Inductive wf_defs (f:fdef) (lc:GVMap) : list atom -> Prop :=
| wf_defs_nil : wf_defs f lc nil
| wf_defs_cons : forall id1 t1 gv1 defs',
    lookupTypViaIDFromFdef f id1 = Some t1 ->
    lookupAL _ lc id1 = Some gv1 ->
    wf_genericvalue gv1 t1 ->
    wf_defs f lc defs' ->
    wf_defs f lc (id1::defs').

Lemma wf_defs_elim : forall ids1 F lc,
  wf_defs F lc ids1 ->
  forall id1, In id1 ids1 ->
  exists t1, exists gv1,
    lookupTypViaIDFromFdef F id1 = Some t1 /\
    lookupAL _ lc id1 = Some gv1 /\
    wf_genericvalue gv1 t1.
Proof.
  induction ids1; intros; simpl in H0; inv H0.  
    inv H.
    exists t1. exists gv1. split; auto.

    inv H.
    eapply IHids1 in H6; eauto.
Qed.    

Lemma wf_defs_intro : forall ids1 F lc,
  (forall id1, In id1 ids1 ->
   exists t1, exists gv1,
     lookupTypViaIDFromFdef F id1 = Some t1 /\
     lookupAL _ lc id1 = Some gv1 /\
     wf_genericvalue gv1 t1) ->
  wf_defs F lc ids1.
Proof.
  induction ids1; intros.
    apply wf_defs_nil.  

    destruct (@H a) as [t1 [gv1 [J1 [J2 J3]]]]; simpl; auto.
    eapply wf_defs_cons; eauto.
      apply IHids1.
      intros id1 J.
      apply H. simpl. auto.
Qed.

Lemma wf_defs_eq : forall ids2 ids1 F' lc',
  set_eq _ ids1 ids2 ->
  wf_defs F' lc' ids1 ->
  wf_defs F' lc' ids2.
Proof.
  intros.
  apply wf_defs_intro.
  intros id1 Hin.
  destruct H as [J1 J2].
  eapply wf_defs_elim in H0; eauto.
Qed.

Lemma wf_defs_updateAddAL : forall g F' lc' ids1 ids2 i1 t1,
  wf_defs F' lc' ids1 ->
  set_eq _ (i1::ids1) ids2 ->
  lookupTypViaIDFromFdef F' i1 = ret t1 ->
  wf_defs F' (updateAddAL GenericValue lc' i1 g) ids2.
Proof.
  intros g F' lc' ids1 ids2 i1 t1 HwfDefs Heq Hlkup.  
  apply wf_defs_intro.  
  intros id1 Hin.
  destruct Heq as [Hinc1 Hinc2].
  apply Hinc2 in Hin.
  simpl in Hin.
  destruct (eq_dec i1 id1); subst.
    exists t1. exists g. 
    split; auto.
    split; auto. 
      apply lookupAL_updateAddAL_eq; auto.      

    destruct Hin as [Eq | Hin]; subst; try solve [contradict n; auto].
    eapply wf_defs_elim in HwfDefs; eauto.
    destruct HwfDefs as [t2 [gv2 [J1 [J2 J3]]]].
    exists t2. exists gv2.
    split; auto.
    split; auto. 
      rewrite <- lookupAL_updateAddAL_neq; auto.      
Qed.

Definition wf_ExecutionContext (ps:list product) (ec:ExecutionContext) : Prop :=
let '(mkEC f b cs tmn lc als) := ec in
isReachableFromEntry f b /\
blockInFdefB b f = true /\
InProductsB (product_fdef f) ps = true /\
match cs with
| nil => 
    match inscope_of_tmn f b tmn with
    | Some ids => wf_defs f lc ids
    | None => False
    end
| c::_ =>
    match inscope_of_cmd f b c with
    | Some ids => wf_defs f lc ids
    | None => False
    end
end /\
exists l1, exists ps, exists cs',
b = block_intro l1 ps (cs'++cs) tmn.

Definition wf_call (ec:ExecutionContext) (ecs:ECStack) : Prop :=
let '(mkEC f _ _ _ _ _) := ec in
forall b, blockInFdefB b f ->
let '(block_intro _ _ _ tmn) := b in
match tmn with
| insn_return _ _ _ =>
    match ecs with
    | nil => True
    | mkEC f' b' (insn_call _ _ _ _ _ _ ::_) tmn' lc' als'::ecs' => True
    | _ => False
    end
| insn_return_void _ =>
    match ecs with
    | nil => True
    | mkEC f' b' (insn_call _ true _ _ _ _ ::_) tmn' lc' als'::ecs' => True
    | _ => False
    end
| _ => True
end.

Fixpoint wf_ECStack (ps:list product) (ecs:ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' => wf_ExecutionContext ps ec /\ wf_ECStack ps ecs' /\ wf_call ec ecs'
end.

Definition wf_State (S:State) : Prop :=
let '(mkState s (los, nts) ps ecs _ _ _) := S in
wf_system nil s /\
moduleInSystemB (module_intro los nts ps) s = true /\
wf_ECStack ps ecs.

Lemma getCmdsIDs__cmds_dominates_cmd : forall cs2' c',
  ~ In (getCmdLoc c') (LLVMlib.getCmdsLocs cs2') ->
  set_eq _ (getCmdsIDs (cs2' ++ [c']))
  (cmds_dominates_cmd (cs2' ++ [c']) (getCmdLoc c') ++ 
    match getCmdID c' with
    | Some id1 => [id1]
    | None => nil
    end).   
Proof.
  induction cs2'; intros c' Hnotin.
    simpl in *.
    destruct (eq_atom_dec (getCmdLoc c') (getCmdLoc c')) as [_ | n];
      try solve [contradict n; auto].
      remember (getCmdID c') as R.
      destruct R; simpl_env; apply set_eq_refl.

    simpl in *.
    assert (~ In (getCmdLoc c') (getCmdsLocs cs2')) as J.
      auto.
    apply IHcs2' in J.
    remember (getCmdID a) as R1.
    remember (getCmdID c') as R2.
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c')); 
      try solve [contradict e; auto].
    destruct R1; auto.
      simpl_env.
      apply set_eq_app; auto using set_eq_refl.
Qed.      

Definition opt_set_eq (ops1 ops2:option (list atom)) : Prop :=
match (ops1, ops2) with
| (None, None) => True
| (Some s1, Some s2) => set_eq _ s1 s2
| _ => False
end.

Lemma inscope_of_block__opt_set_eq : forall f l1 l' opr1 opr2,
  opt_set_eq opr1 opr2 ->
  opt_set_eq (inscope_of_block f l1 opr1 l') (inscope_of_block f l1 opr2 l').
Proof.
  unfold inscope_of_block.
  intros.
  destruct (lookupBlockViaLabelFromFdef f l').
    destruct (eq_atom_dec l' l1); subst.
      destruct opr1.
        destruct opr2; try solve [inversion H | auto].
        destruct opr2; try solve [inversion H | auto].
      unfold opt_set_eq in *.
      destruct opr1.
        destruct opr2; try solve [inversion H ].
          apply set_eq_app; auto using set_eq_refl.
        destruct opr2; try solve [inversion H | auto ].
    unfold opt_set_eq in *.
    destruct opr1.
      destruct opr2; try solve [inversion H | auto].
      destruct opr2; try solve [inversion H | auto].
Qed.
 
Lemma fold_left__opt_set_eq_aux : forall ls0 opr1 opr2 f l1,
  opt_set_eq opr1 opr2 ->
  opt_set_eq (fold_left (inscope_of_block f l1) ls0 opr1) 
           (fold_left (inscope_of_block f l1) ls0 opr2).
Proof.
  induction ls0; intros opr1 opr2 f l1 Heq; simpl in *; auto.
    apply IHls0.
      apply inscope_of_block__opt_set_eq; auto.
Qed.

Lemma fold_left__opt_set_eq : forall (ls0:list atom) f l1 init1 init2 r1,
  set_eq _ init1 init2 ->  
  fold_left (inscope_of_block f l1) ls0 (Some init1) = Some r1 ->
  exists r2, fold_left (inscope_of_block f l1) ls0 (Some init2) = Some r2 /\ 
    set_eq _ r1 r2.
Proof.
  intros.
  assert (opt_set_eq (Some init1) (Some init2)) as EQ. unfold opt_set_eq. auto.
  apply fold_left__opt_set_eq_aux with (ls0:=ls0)(f:=f)(l1:=l1) in EQ.
  remember (fold_left (inscope_of_block f l1) ls0 (ret init2)) as R. 
  unfold opt_set_eq in EQ.    
  rewrite H0 in EQ.
  destruct R; try solve [inversion EQ].
  exists l0. auto.
Qed.
 
Lemma inscope_of_block__opt_union : forall f l1 l' init1 init2 r1,
  inscope_of_block f l1 (Some init1) l' = Some r1 ->
  exists r2, inscope_of_block f l1 (Some (init1++init2)) l' = Some r2 /\
    set_eq _ (r1++init2) r2.
Proof.
  intros.
  unfold inscope_of_block in *.
  destruct (lookupBlockViaLabelFromFdef f l').
    destruct (eq_atom_dec l' l1); subst; inv H.
      exists (r1++init2). auto using set_eq_refl.
      exists (getBlockIDs b ++ init1 ++ init2). 
        simpl_env. auto using set_eq_refl.
    inversion H.
Qed.

Lemma fold_left__none : forall (ls0:list atom) f l1,
  fold_left (inscope_of_block f l1) ls0 None = None.
Proof.
  induction ls0; intros f l1; simpl in *; auto.
Qed.

Lemma fold_left__opt_union : forall (ls0:list atom) f l1 init1 init2 r1,
  fold_left (inscope_of_block f l1) ls0 (Some init1) = Some r1 ->
  exists r2, 
    fold_left (inscope_of_block f l1) ls0 (Some (init1++init2)) = Some r2 
      /\ set_eq _ (r1++init2) r2.
Proof.
  induction ls0; intros f l1 init1 init2 r1 H; simpl in *; auto.
    inv H. exists (r1 ++ init2). split; auto using set_eq_refl.

    destruct (lookupBlockViaLabelFromFdef f a).
      destruct (eq_atom_dec a l1); subst; auto.
        apply IHls0 with (init2:=init2) in H; auto.
          simpl_env in H. auto.
      rewrite fold_left__none in H. inversion H.
Qed.

Lemma inscope_of_cmd_tmn : forall f l2 ps2 cs2' c' tmn' ids1,
~ In (getCmdLoc c') (getCmdsLocs cs2') ->
Some ids1 = inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']) tmn') c' ->
exists ids2, 
  Some ids2 = inscope_of_tmn f (block_intro l2 ps2 (cs2'++[c']) tmn') tmn' /\
  match getCmdID c' with
  | Some id1 => set_eq _ (id1::ids1) ids2
  | None => set_eq _ ids1 ids2
  end.
Proof.
  intros f l2 ps2 cs2' c' tmn' ids1 Hnotin Hinscope.
  unfold inscope_of_cmd in Hinscope.
  unfold inscope_of_tmn.
  destruct f as [[? ? ? la va] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro f t i0 la va) bs)) !! l2) as R.
  destruct R as [R_contents R_bound]. simpl in *.
  apply getCmdsIDs__cmds_dominates_cmd in Hnotin.
  symmetry in Hinscope.
  remember (getCmdID c') as R.
  destruct R.
    apply fold_left__opt_union with (init2:=[i1]) in Hinscope.
    destruct Hinscope as [r2 [Hinscope Heq]].
    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++
      ((getCmdsIDs (cs2' ++ [c'])) ++ (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
        simpl_env. 
        eapply set_eq_trans with (y:=r2); eauto.
        eapply set_eq_trans with (y:=ids1 ++ [i1]); eauto.
          apply set_eq_swap.          
      simpl_env.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_trans with (y:=(cmds_dominates_cmd (cs2' ++ [c']) 
         (getCmdLoc c') ++ [i1]) ++ getArgsIDs la).
        simpl_env.
        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_swap.          

        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_sym; auto.          

    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++ 
      ((getCmdsIDs (cs2' ++ [c'])) ++ (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_app; auto using set_eq_refl.
      simpl_env in Hnotin.
      apply set_eq_sym; auto.          
Qed.

Lemma cmds_dominates_cmd__cmds_dominates_cmd : forall cs2' c' c cs',
  NoDup (getCmdsLocs (cs2'++[c']++[c]++cs')) ->
  set_eq _ (cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c))
    (cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c') ++
     match getCmdID c' with
     | Some id1 => [id1]
     | None => nil
     end).   
Proof.
  induction cs2'; intros c' c cs' Hnodup.
    simpl in *.
    inv Hnodup. simpl in H1.
    remember (getCmdID c') as R.
    destruct (eq_atom_dec (getCmdLoc c') (getCmdLoc c)).
      contradict e; auto.

      destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_|n1];
        try solve [contradict n1; auto].
      destruct (eq_atom_dec (getCmdLoc c') (getCmdLoc c')) as [_|n2];
        try solve [contradict n2; auto].
      destruct R; auto using set_eq_refl.

    simpl in *.
    inv Hnodup.
    rewrite getCmdsLocs_app in H1.
    apply NotIn_inv in H1.    
    destruct H1 as [H11 H12].
    simpl in H12.
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c)) as [e1 | ];
      try solve [contradict e1; auto].
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c')) as [e1 | ];
      try solve [contradict e1; auto].
    destruct (getCmdID a); auto.
      apply IHcs2' in H2. clear IHcs2'.
      simpl_env.
       apply set_eq_app; auto using set_eq_refl.
Qed.      

Lemma inscope_of_cmd_cmd : forall f l2 ps2 cs2' c' c cs' tmn' ids1,
NoDup (getCmdsLocs (cs2'++[c']++[c]++cs')) ->
Some ids1 = inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn') c' 
  ->
exists ids2, 
  Some ids2 = 
    inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn') c /\
  match getCmdID c' with
  | Some id1 => set_eq _ (id1::ids1) ids2
  | None => set_eq _ ids1 ids2
  end.
Proof.
  intros f l2 ps2 cs2' c' c cs' tmn' ids1 Hnodup Hinscope.
  unfold inscope_of_cmd in Hinscope.
  unfold inscope_of_cmd.
  destruct f as [[? ? ? la va] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro f t i0 la va) bs)) !! l2) as R.
  destruct R as [R_contents R_bound].
  apply cmds_dominates_cmd__cmds_dominates_cmd in Hnodup. simpl in *.
  symmetry in Hinscope.
  remember (getCmdID c') as R.
  destruct R.
    apply fold_left__opt_union with (init2:=[i1]) in Hinscope.
    destruct Hinscope as [r2 [Hinscope Heq]].
    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++ 
      ((cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c)) ++
      (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
        simpl_env. 
        eapply set_eq_trans with (y:=r2); eauto.
        eapply set_eq_trans with (y:=ids1 ++ [i1]); eauto.
          apply set_eq_swap.          
      simpl_env.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_trans with (y:=(cmds_dominates_cmd (cs2' ++ [c']++[c]++cs') 
         (getCmdLoc c') ++ [i1]) ++ getArgsIDs la).
        simpl_env.
        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_swap.          

        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_sym; auto.          

    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++
      ((cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c)) ++
      (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_app; auto using set_eq_refl.
      simpl_env in Hnodup.
      apply set_eq_sym; auto.          
Qed.

Lemma fold_left__bound_blocks : forall ls0 fa t i0 la va bs l0 init,
  incl ls0 (bound_blocks bs) ->
  exists r, 
    fold_left (inscope_of_block 
      (fdef_intro (fheader_intro fa t i0 la va) bs) l0) ls0 (Some init) = 
       Some r.
Proof.
  induction ls0; intros fa t i0 la va bs l0 init Hinc; simpl in *.
    exists init. auto.

    assert (incl ls0 (bound_blocks bs)) as J.
      simpl_env in Hinc.
      eapply incl_app_invr; eauto.
    assert (exists b, lookupAL block (genLabel2Block_blocks bs) a = Some b) 
      as Hlkup.
      clear - Hinc.
      simpl_env in Hinc.
      apply incl_app_invl in Hinc.
      apply inc__getLabel2Block_blocks; auto.

    destruct Hlkup as [b Hlkup].
    rewrite Hlkup. 
    destruct (eq_atom_dec a l0); subst; auto.
Qed.

Lemma fold_left__spec : forall ls0 l0 init r f,
  fold_left (inscope_of_block f l0) ls0 (Some init) = Some r ->
    incl init r /\
    (forall l1 b1, 
      In l1 (ListSet.set_diff eq_atom_dec ls0 [l0]) -> 
      lookupBlockViaLabelFromFdef f l1 = Some b1 ->
      incl (getBlockIDs b1) r) /\
    (forall id1,
      In id1 r ->
      In id1 init \/
      exists b1, exists l1, In l1 (ListSet.set_diff eq_atom_dec ls0 [l0]) /\
        lookupBlockViaLabelFromFdef f l1 = Some b1 /\
        In id1 (getBlockIDs b1)
    ).
Proof.
  induction ls0; intros l0 init r f Hfold; simpl in *.
    inv Hfold.
    split. apply incl_refl.
    split; auto. 
      intros ? ? Hfalse. inversion Hfalse.
      
    remember (lookupBlockViaLabelFromFdef f a) as R.
    destruct R.
      destruct (eq_atom_dec a l0); subst; auto.
      apply IHls0 in Hfold.
      destruct Hfold as [J1 [J2 J3]].
      split.
        eapply incl_app_invr; eauto.
      split.
        intros l1 b1 Hin Hlkup.
        apply ListSet.set_add_elim in Hin.
        destruct Hin as [Hin | Hin]; subst; eauto.                  
          rewrite Hlkup in HeqR. inv HeqR.
          eapply incl_app_invl; eauto.
        intros id1 Hin.
        apply J3 in Hin.
        destruct Hin as [Hin | [b1 [l1 [H1 [H2 H3]]]]].
          apply in_app_or in Hin.
          destruct Hin as [Hin | Hin]; auto.
          right. 
          exists b. exists a.
          split; auto.
            apply ListSet.set_add_intro; auto.
             
          right.
          exists b1. exists l1.
          split; auto.
            apply ListSet.set_add_intro; auto.

      rewrite fold_left__none in Hfold. inversion Hfold.
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

Lemma atomset_eq__proof_irr1 : forall
  (bs : blocks)
  (l' : l)
  (t : AMap.t (DomDS.dt (bound_blocks bs)))
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_blocks bs))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = t !! l')
  (bs_contents : ListSet.set atom)
  (bs_bound0 : incl bs_contents (bound_blocks bs))
  (HeqR2 : {|
          DomDS.L.bs_contents := bs_contents;
          DomDS.L.bs_bound := bs_bound0 |} = t !! l'),
  contents' = bs_contents.
Admitted.

Lemma atomset_eq__proof_irr2 : forall
  max
  (contents' : ListSet.set atom)
  (inbound' : incl contents' max)
  a
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = a),
  contents' = Dominators.bs_contents max a.
Admitted.

Lemma hasNonPredecessor__mono : forall b bs ud,
  hasNonePredecessor b (genBlockUseDef_blocks bs ud) = true ->
  hasNonePredecessor b (genBlockUseDef_blocks bs nil) = true.
Admitted.

Lemma getEntryBlock_inv : forall 
  (bs : blocks)
  (l3 : l)
  (l' : l)
  (ps : phinodes)
  (cs : cmds)
  (tmn : terminator)
  (fh : fheader)
  (ifs : intrinsic_funs)
  (s : system)
  (m : module)
  (HwfF : wf_fdef ifs s m (fdef_intro fh bs))
  (HBinF : InBlocksB (block_intro l3 ps cs tmn) bs = true)
  (a : atom)
  (Hsucc : In l' (successors_terminator tmn))
  ps1 cs1 tmn1
  (H : getEntryBlock (fdef_intro fh bs) = ret block_intro a ps1 cs1 tmn1),
  l' <> a.
Proof.
  intros.  
   destruct (eq_atom_dec l' a); subst; auto.
   inv HwfF.
   simpl in H11.
   rewrite H in H6. inv H6.
   clear - H11 Hsucc HBinF.
   induction bs; simpl in *.
     inversion HBinF.
  
     apply orb_prop in HBinF.          
     destruct HBinF as [HBinF | HBinF].
       apply blockEqB_inv in HBinF; subst.
       simpl in H11.
       destruct tmn; try solve [inversion Hsucc].
         unfold hasNonePredecessor in H11.
         unfold predOfBlock in H11. simpl in H11.  
         simpl in Hsucc. 
         destruct Hsucc as [Hsucc | [Hsucc | Hsucc]]; subst; 
           try inversion Hsucc.
  
           destruct (@lookupAL_update_udb_eq (update_udb nil l3 l1) l3 a)
             as [re [Hlk Hin]]. 
           apply lookupAL_genBlockUseDef_blocks_spec with (bs:=bs) in Hlk.
           destruct Hlk as [re' [Hlk Hinc]].
           rewrite Hlk in H11.
           destruct re'; inversion H11.
           apply Hinc in Hin. inversion Hin.
  
           destruct (@lookupAL_update_udb_eq nil l3 a) as [re [Hlk Hin]].
           apply lookupAL_update_udb_spec with (l1:=l3)(l2:=l0) in Hlk.
           destruct Hlk as [re1 [Hlk Hinc1]].
           apply lookupAL_genBlockUseDef_blocks_spec with (bs:=bs) in Hlk.  
           destruct Hlk as [re2 [Hlk Hinc2]].
           rewrite Hlk in H11.
           destruct re2; inversion H11.
           apply Hinc1 in Hin. 
           apply Hinc2 in Hin. 
           inversion Hin.
  
         unfold hasNonePredecessor in H11.
         unfold predOfBlock in H11. simpl in H11.  
         simpl in Hsucc. 
         destruct Hsucc as [Hsucc | Hsucc]; subst; try inversion Hsucc.
           destruct (@lookupAL_update_udb_eq nil l3 a) as [re [Hlk Hin]]. 
           apply lookupAL_genBlockUseDef_blocks_spec with (bs:=bs) in Hlk.
           destruct Hlk as [re' [Hlk Hinc]].
           rewrite Hlk in H11.
           destruct re'; inversion H11.
           apply Hinc in Hin. inversion Hin.
     apply hasNonPredecessor__mono in H11; eauto.
Qed.

Lemma dom_successors : forall
  (bs : blocks)
  (l3 : l)
  (l' : l)
  ps cs tmn fh ifs s m
  (HwfF : wf_fdef ifs s m (fdef_intro fh bs))
  (Huniq : uniqBlocks bs)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) (fdef_intro fh bs) = true)
  (Doms : AMap.t
           (Dominators.t (bound_fdef (fdef_intro fh bs))))
  (HeqDoms : Doms = dom_analyze (fdef_intro fh bs))
  (contents3 : ListSet.set atom)
  (inbound3 : incl contents3 (bound_fdef (fdef_intro fh bs)))
  (Heqdefs3 : {|
             DomDS.L.bs_contents := contents3;
             DomDS.L.bs_bound := inbound3 |} = Doms !! l3)
  (Hsucc : In l' (successors_terminator tmn))
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_fdef (fdef_intro fh bs)))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = Doms !! l'),
  incl contents' (l3 :: contents3).
Proof. 
  intros. simpl in *.
  unfold dom_analyze in *.
  remember (entry_dom bs) as R.
  destruct R as [R Hp].
  destruct R as [[le start] | ].
  Case "entry is good".
    remember (DomDS.fixpoint (bound_blocks bs) (successors_blocks bs)
                (transfer (bound_blocks bs)) ((le, start) :: nil)) as R1.
    destruct start.
    destruct bs_contents; try inv Hp.
    destruct bs_contents; try inv Hp.
    destruct R1; subst.
    SCase "analysis is done".
      symmetry in HeqR1.
      assert (In l' (successors_blocks bs) !!! l3) as J1.
        clear - HBinF Hsucc Huniq.
        assert (successors_terminator tmn = (successors_blocks bs) !!! l3) as EQ.
          eapply successors_terminator__successors_blocks; eauto.
        rewrite <- EQ. auto.
      
      apply DomDS.fixpoint_solution with (s:=l')(n:=l3) in HeqR1; eauto.
      unfold transfer, DomDS.L.ge, DomDS.L.top, DomDS.L.bot, DomDS.L.sub, 
        DomDS.L.eq, Dominators.add in HeqR1.
      remember (t !! l') as R2.
      destruct R2.              
      assert (contents' = bs_contents) as EQ.
        clear - Heqdefs' HeqR2.
        eapply atomset_eq__proof_irr1; eauto.
      subst.
      remember (t !! l3) as R3.
      destruct R3.              
      assert (contents3 = bs_contents0) as EQ.
        clear - Heqdefs3 HeqR3.
        eapply atomset_eq__proof_irr1; eauto.
      subst.
      clear - Heqdefs3 Heqdefs' HeqR2 HeqR3 HeqR1.
      destruct HeqR1 as [HeqR1 | [HeqR1 | HeqR1]].
        destruct HeqR1 as [G1 G2].
        intros x G.
        apply G1 in G. inversion G.
        destruct (in_dec eq_atom_dec l3 (bound_blocks bs)).
          eapply incl_set_eq_right; eauto using set_eq_sym.
          apply incl_tran with (m:=bs_contents0).
            eapply incl_set_eq_right; eauto using set_eq_sym.
            apply incl_tl; auto using incl_refl.
          
        destruct (in_dec eq_atom_dec l3 (bound_blocks bs)); auto.
          apply incl_tl; auto.

    SCase "analysis fails".
      subst.
      unfold Dominators.top in Heqdefs3, Heqdefs'.
      simpl in Heqdefs3, Heqdefs'.
      assert (exists ps, exists cs, exists tmn,
        getEntryBlock (fdef_intro fh bs) = Some (block_intro a ps cs tmn)).
        unfold entry_dom in HeqR.
        destruct bs.
          inversion HeqR.
          destruct b. inv HeqR.
          exists p. exists c. exists t. auto.
      assert (l' <> a) as Neq.
        clear - H Hsucc HwfF HBinF. 
        destruct H as [ps1 [cs1 [tmn1 H]]].
        eapply getEntryBlock_inv; eauto.
      rewrite AMap.gso in Heqdefs'; auto.
      rewrite AMap.gi in Heqdefs'.
      inv Heqdefs'.
      clear.
      intros x J. inversion J.

  Case "entry is wrong".   
    subst. inversion HBinF.
Qed.

Lemma wf_defs_br_aux : forall lc l' ps' cs' lc' F tmn' gl TD Mem0
  (l3 : l)
  (ps : phinodes)
  (cs : list cmd) tmn
  (Hlkup : Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hswitch : switchToNewBasicBlock TD Mem0 (block_intro l' ps' cs' tmn')
         (block_intro l3 ps cs tmn) gl lc = ret lc')
  (t : list atom)
  (Hwfdfs : wf_defs F lc t)
  (ids0' : list atom)
  (Hinc : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) t),
  wf_defs F lc' ids0'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  apply wf_defs_intro.
  intros id1 Hid1.
  remember (getIncomingValuesForBlockFromPHINodes TD Mem0 ps'
                (block_intro l3 ps cs tmn) gl lc) as R1.
  destruct R1; inv Hswitch.
  destruct (In_dec eq_atom_dec id1 (getPhiNodesIDs ps')) as [Hin | Hnotin].
    eapply getIncomingValuesForBlockFromPHINodes_spec in HeqR1; eauto.
    destruct HeqR1 as [gv HeqR1].
    apply updateValuesForNewBlock_spec1 with (lc:=lc) in HeqR1.
    eapply InPhiNodes_lookupTypViaIDFromFdef in Hlkup; eauto.
    destruct Hlkup as [t1 Hlkup].
    exists t1. exists gv.
    split; auto.

    apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) in Hnotin;
      auto.
    apply Hinc in Hnotin.
    apply wf_defs_elim with (id1:=id1) in Hwfdfs; auto.
    destruct Hwfdfs as [t1 [gv1 [J1 [J2 J3]]]].
    apply updateValuesForNewBlock_spec2 with (rs:=l0) in J2.
    destruct J2 as [gv' J2].
    exists t1. exists gv'. 
    split; auto.
Qed.

Lemma inscope_of_tmn_br_aux : forall F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 ifs
  s m lc lc' TD Mem0 gl,
wf_fdef ifs s m F ->
uniqFdef F ->
blockInFdefB (block_intro l3 ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs tmn) tmn ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock TD Mem0 (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs tmn) gl lc = Some lc' ->
wf_defs F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs F lc' ids0'.
Proof.
  intros F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 ifs s m lc lc' TD Mem0 gl HwfF 
    Huniq HBinF Hsucc Hinscope Hlkup Hswitch Hwfdfs.
  symmetry in Hlkup.
  assert (J:=Hlkup).
  apply lookupBlockViaLabelFromFdef_inv in J; auto.
  destruct J as [Heq J]; subst.
  unfold inscope_of_tmn in Hinscope.
  unfold inscope_of_tmn. unfold inscope_of_cmd.
  destruct F as [[? ? ? la va] bs].
  remember (dom_analyze (fdef_intro (fheader_intro f t i0 la va) bs)) as Doms.
  remember (Doms !! l3)as defs3.
  remember (Doms !! l')as defs'.
  destruct defs3 as [contents3 inbound3]. 
  destruct defs' as [contents' inbound']. 

  assert (incl contents' (l3::contents3)) as Hsub.
    clear - HBinF Hsucc Heqdefs3 Heqdefs' HeqDoms Huniq HwfF.
    simpl in Huniq.
    eapply dom_successors; eauto.

  destruct cs'.
  Case "cs'=nil".
    assert (J1:=inbound').
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getCmdsIDs nil ++ getArgsIDs la)(t:=t)(i0:=i0)(la:=la)(va:=va)(bs:=bs)
      (fa:=f)(l0:=l') in J1.
    destruct J1 as [r J1].
    exists r. split; auto.

    assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
      as Jinc.
      clear - Hinscope J1 Hsub HBinF Huniq.
      apply fold_left__spec in J1.
      symmetry in Hinscope.
      apply fold_left__spec in Hinscope.
      destruct J1 as [J1 [J2 J3]].
      destruct Hinscope as [J4 [J5 J6]].
      intros id1 J.
      assert (J':=J).
      apply ListSet.set_diff_elim1 in J.
      apply ListSet.set_diff_elim2 in J'.
      apply J3 in J.
      destruct J as [J | J].
      SCase "id1 in init and the current block".
        simpl in J.
        apply in_app_or in J.
        destruct J as [J | J]; try solve [contradict J; auto].
        apply J4.
        apply in_or_app. right.
        apply in_or_app; auto.
      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq. 
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4.
            rewrite_env 
              ((getPhiNodesIDs ps ++ getCmdsIDs cs) ++ getArgsIDs la).
            apply in_or_app; auto.
      
            apply J5 in J9; auto.
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.

    split; auto.
      eapply wf_defs_br_aux; eauto.
        
  Case "cs'<>nil".
    assert (J1:=inbound').
    unfold cmds_dominates_cmd. simpl.
    destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_ | n]; 
      try solve [contradict n; auto].
    simpl_env.
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getArgsIDs la)(t:=t)(i0:=i0)(la:=la)(va:=va)(bs:=bs)(l0:=l')(fa:=f) in J1.
    destruct J1 as [r J1].
    exists r.  split; auto.

    assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
      as Jinc.
      clear - Hinscope J1 Hsub HBinF Huniq.
      apply fold_left__spec in J1.
      symmetry in Hinscope.
      apply fold_left__spec in Hinscope.
      destruct J1 as [J1 [J2 J3]].
      destruct Hinscope as [J4 [J5 J6]].
      intros id1 J.
      assert (J':=J).
      apply ListSet.set_diff_elim1 in J.
      apply ListSet.set_diff_elim2 in J'.
      apply J3 in J.
      destruct J as [J | J].
      SCase "id1 in init and the current block".
        simpl in J.
        apply in_app_or in J.
        destruct J as [J | J]; try solve [contradict J; auto].
        apply J4.
        apply in_or_app. right.
        apply in_or_app; auto.
      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq.
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4.
            rewrite_env 
              ((getPhiNodesIDs ps ++ getCmdsIDs cs) ++ getArgsIDs la).
            apply in_or_app; auto.
      
            apply J5 in J9; auto. 
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.

    split; auto.
      eapply wf_defs_br_aux; eauto.
Qed.

Lemma inscope_of_tmn_br_uncond : forall F l3 ps cs bid ids0 l' ps' cs' tmn' l0 
 ifs s m gl lc lc' TD Mem0,
wf_fdef ifs s m F ->
uniqFdef F ->
blockInFdefB (block_intro l3 ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0)) 
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock TD Mem0 (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs (insn_br_uncond bid l0)) gl lc = Some lc' ->
wf_defs F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs F lc' ids0'.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

Lemma inscope_of_tmn_br : forall F l0 ps cs bid l1 l2 ids0 l' ps' cs' tmn' Cond 
  c TD Mem0 gl lc ifs s m lc',
wf_fdef ifs s m F ->
uniqFdef F ->
blockInFdefB (block_intro l0 ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) 
  (insn_br bid Cond l1 l2) ->
getOperandValue TD Mem0 Cond lc gl = ret c ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
switchToNewBasicBlock TD Mem0 (block_intro l' ps' cs' tmn')
  (block_intro l0 ps cs (insn_br bid Cond l1 l2)) gl lc = Some lc' ->
wf_defs F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs F lc' ids0'.
Proof.
  intros.
  remember (isGVZero TD c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

Lemma wf_system__wf_tmn : forall l1 ps1 cs1 tmn1 f ps los nts s ifs,
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true -> 
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  wf_insn ifs s (module_intro los nts ps) f (block_intro l1 ps1 cs1 tmn1) 
    (insn_terminator tmn1).
Admitted.

(** * Correctness of reachability analysis *)

(** The entry point of the function is reachable. *)

Lemma reachable_entrypoint:
  forall (f:fdef) l0 ps cs tmn, 
    LLVMlib.getEntryBlock f = Some (block_intro l0 ps cs tmn) ->
    (reachable f)!!l0 = true.
Proof.
  intros f l0 ps cs tmn Hentry. unfold reachable.
  caseEq (reachable_aux f).
    unfold reachable_aux; intros reach A.
    rewrite Hentry in A.
    assert (LBoolean.ge reach!!l0 true).
      eapply ReachDS.fixpoint_entry. eexact A. auto with coqlib.
    unfold LBoolean.ge in H. tauto.

    intros. apply AMap.gi.
Qed.

(** The successors of a reachable instruction are reachable. *)

Lemma reachable_successors:
  forall f l0 cs ps tmn l1,
  uniqFdef f ->
  blockInFdefB (block_intro l0 cs ps tmn) f ->
  In l1 (successors_terminator tmn) ->
  (reachable f)!!l0 = true ->
  (reachable f)!!l1 = true.
Proof.
  intros f l0 cs ps tmn l1 HuniqF HbInF Hin.
  unfold reachable.
  caseEq (reachable_aux f).
    unfold reachable_aux. intro reach; intros.
    remember (LLVMlib.getEntryBlock f) as R.
    destruct R; inv H.
    destruct b as [le ? ? ?].
    assert (LBoolean.ge reach!!l1 reach!!l0) as J.
      change (reach!!l0) with ((fun pc r => r) l0 (reach!!l0)).
      eapply ReachDS.fixpoint_solution; eauto.
        destruct f as [? bs]. simpl in *.
        clear - HuniqF HbInF Hin.
        assert ((successors_terminator tmn) = (successors_blocks bs) !!! l0) 
          as EQ.
          eapply successors_terminator__successors_blocks; eauto.
        rewrite <- EQ; auto.            
    elim J; intro. congruence. auto.

  intros. apply AMap.gi.
Qed.

Lemma wf_system__uniqFdef : forall ifs S los nts Ps f,
  wf_system ifs S -> 
  moduleInSystemB (module_intro los nts Ps) S = true ->
  InProductsB (product_fdef f) Ps = true ->
  uniqFdef f.
Admitted.

Lemma wf_system__wf_fdef : forall ifs S los nts Ps f,
  wf_system ifs S -> 
  moduleInSystemB (module_intro los nts Ps) S = true ->
  InProductsB (product_fdef f) Ps = true ->
  wf_fdef ifs S (module_intro los nts Ps) f.
Admitted.

Lemma wf_system__wf_block : forall b f ps los nts s ifs,
  blockInFdefB b f = true -> 
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  wf_block ifs s (module_intro los nts ps) f b.
Admitted.

Lemma wf_system__uniq_block : forall b f ps los nts s ifs,
  blockInFdefB b f = true -> 
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  NoDup (getBlockLocs b).
Admitted.

Lemma dom_entrypoint : forall f l0 ps cs tmn
  (Hentry : LLVMlib.getEntryBlock f = Some (block_intro l0 ps cs tmn)),
  incl (Dominators.bs_contents (bound_fdef f) ((dom_analyze f) !! l0)) [l0].
Proof.
  intros.
  unfold dom_analyze.
  destruct f.
  remember (entry_dom b) as R.
  destruct R as [R Hp].
  destruct R as [[le start] | ].
  Case "entry is good". 
    remember (DomDS.fixpoint (bound_blocks b) (successors_blocks b)
                (transfer (bound_blocks b)) ((le, start) :: nil)) as R1.
    destruct start.
    destruct bs_contents; try inv Hp.
    destruct bs_contents; try inv Hp.
    subst le. 
    destruct b; try solve [inversion HeqR].
    destruct b. simpl in HeqR. inversion HeqR. subst a.
    simpl in Hentry. inversion Hentry. subst l0 p c t.
    clear HeqR Hentry.    
    destruct R1; subst.
    SCase "analysis is done".
      symmetry in HeqR1.
      apply DomDS.fixpoint_entry with (n:=l1)(v:={|
                DomDS.L.bs_contents := l1 :: nil;
                DomDS.L.bs_bound := bs_bound |}) in HeqR1; simpl; eauto.
      unfold DomDS.L.ge in HeqR1.
      unfold DomDS.L.eq, DomDS.L.top, DomDS.L.bot, DomDS.L.sub in HeqR1.
      simpl in *.

      remember (t !! l1) as R.
      destruct R.
      erewrite <- atomset_eq__proof_irr2; eauto.
      destruct HeqR1 as [HeqR1 | [ HeqR1 | HeqR1 ]]; auto.
      SSCase "1".       
        apply set_eq_empty_inv in HeqR1. subst.
        intros x J. inversion J.
      SSCase "2".   
        eapply incl_set_eq_right; eauto using set_eq_sym.
    
    SCase "analysis fails".
      simpl.      
      rewrite AMap.gss. simpl.
      apply incl_refl.

  Case "entry is wrong". 
    subst. inversion Hentry.
Qed.

Lemma preservation_dbCall_case : forall los nts lc gl fid lp l' fa rt la va lb 
  Mem0 bs_contents
  (bs_bound : incl bs_contents (bound_blocks lb))
  (H0 : incl bs_contents [l']),
   match
     fold_left
       (inscope_of_block (fdef_intro (fheader_intro fa rt fid la va) lb) l')
       bs_contents (ret getArgsIDs la)
   with
   | ret ids0 =>
       wf_defs (fdef_intro (fheader_intro fa rt fid la va) lb)
         (initLocals la (params2GVs (los, nts) Mem0 lp lc gl)) ids0
   | merror => False
   end.
Proof.
  intros.
  assert (J:=bs_bound).
  apply fold_left__bound_blocks with (t:=rt)(i0:=fid)(la:=la)(va:=va)(fa:=fa)
    (l0:=l')(init:=getArgsIDs la) in J.
  destruct J as [r J].
  rewrite J.       
  apply fold_left__spec in J.
  destruct J as [_ [_ J]].
  apply wf_defs_intro.
  intros id1 Hin.
  apply J in Hin.
  destruct Hin as [Hin | Hin].    
    assert (J1:=Hin).
    apply InArgsIDs_lookupTypViaIDFromFdef with (t0:=rt)(id0:=fid)(la0:=la)
      (va0:=va)(bs:=lb)(fa:=fa) in J1.
    destruct J1 as [t J1].
    exists t. rewrite J1.
    apply initLocals_spec with (gvs:=params2GVs (los, nts) Mem0 lp lc gl) in Hin.
    destruct Hin as [gv Hin].
    exists gv. split; auto.
  
    destruct Hin as [b1 [l1 [Hin _]]].
    simpl in H0. clear - H0 Hin.
    assert (J:=Hin).
    apply ListSet.set_diff_elim1 in Hin.
    apply ListSet.set_diff_elim2 in J.
    apply H0 in Hin.
    simpl in Hin. 
    destruct Hin as [Hin | Hin]; subst; try inversion Hin.
    simpl in J. contradict J; auto.
Qed.

Lemma wf_system__wf_cmd : forall l1 ps1 cs1 tmn1 f ps los nts s ifs c,
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true -> 
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  In c cs1 ->
  wf_insn ifs s (module_intro los nts ps) f (block_intro l1 ps1 cs1 tmn1) 
    (insn_cmd c).
Admitted.

Lemma uniqF__lookupTypViaIDFromFdef : forall l1 ps1 cs1 tmn1 f c i0 t0,
  uniqFdef f ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true -> 
  In c cs1 ->
  getCmdID c = Some i0 ->
  getCmdTyp c = Some t0 ->
  lookupTypViaIDFromFdef f i0 = Some t0.
Admitted.

Lemma wf_system__blockInFdefB__wf_block : forall b f ps los nts s ifs,
  blockInFdefB b f = true -> 
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  wf_block ifs s (module_intro los nts ps) f b.
Admitted.

Lemma wf_system__lookup__wf_block : forall b f l0 ps los nts s ifs,
  Some b = lookupBlockViaLabelFromFdef f l0 ->
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  wf_block ifs s (module_intro los nts ps) f b.
Admitted.

Lemma entryBlock_has_no_phinodes : forall ifs s f l1 ps1 cs1 tmn1 los nts ps,
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  getEntryBlock f = Some (block_intro l1 ps1 cs1 tmn1) ->
  ps1 = nil.  
Proof.
  intros ifs s f l1 ps1 cs1 tmn1 los nts ps HFinP HMinS Hwfs Hentry.
  assert (wf_fdef ifs s (module_intro los nts ps) f) as Hwff.
    eapply wf_system__wf_fdef; eauto.
  assert (wf_block ifs s (module_intro los nts ps) f 
    (block_intro l1 ps1 cs1 tmn1)) as Hwfb.
    apply entryBlockInFdef in Hentry.
    eapply wf_system__blockInFdefB__wf_block; eauto.
  inv Hwfb.
  clear H9 H10.
  destruct ps1; auto.
  inv H8.
  clear H9.
  inv H6.
  inv H12.
  unfold check_list_value_l in H5.
  remember (split (unmake_list_value_l value_l_list)) as R.
  destruct R.
  destruct H5 as [J1 [J2 J3]].
  inv Hwff.
  rewrite H10 in Hentry. inv Hentry.
  unfold hasNonePredecessor in H12.
  simpl in *.
  destruct (predOfBlock
            (block_intro l1 (insn_phi id5 typ5 value_l_list :: ps1) cs1 tmn1)
            (genBlockUseDef_blocks blocks5 nil)); inversion H12.
  simpl in J1. contradict J1. omega.
Qed.

Lemma preservation : forall S1 S2 tr,
  dsInsn S1 S2 tr -> wf_State S1 -> wf_State S2.
Proof.
  intros S1 S2 tr HdsInsn HwfS1.
  (dsInsn_cases (induction HdsInsn) Case); destruct TD as [los nts].
Focus.
Case "dsReturn".
  destruct HwfS1 as 
    [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]] 
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]; subst.
  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return rid RetTy Result))
             (insn_return rid RetTy Result)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  SCase "1".
    split; auto.
    split; auto.  
    split; auto. 
    split; auto.
    split.
    SSCase "1.1".
      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        assert (~ In (getCmdLoc c') (getCmdsLocs cs2')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        unfold returnUpdateLocals in H1. simpl in H1.
        destruct R.
          destruct n; inv HeqR.
          remember (getOperandValue (los,nts) Mem' Result lc gl) as R1.
          destruct R1; inv H1.          
          assert (Hwfc := HBinF2).
          assert (In (insn_call i0 false c t v p) 
            (cs2'++[insn_call i0 false c t v p])) as HinCs.
            apply in_or_app. right. simpl. auto.
          eapply wf_system__wf_cmd with (c:=insn_call i0 false c t v p) 
            in Hwfc; eauto.
          inv Hwfc.
          eapply wf_defs_updateAddAL with (t1:=typ1) ; eauto.
            eapply uniqF__lookupTypViaIDFromFdef; eauto.
              eapply wf_system__uniqFdef; eauto.

          destruct n; inv HeqR. inv H1.
          eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsLocs (cs2' ++ [c'] ++ [c] ++ cs'))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        unfold returnUpdateLocals in H1. simpl in H1.
        destruct R.
          destruct n; inv HeqR.
          remember (getOperandValue (los,nts) Mem' Result lc gl) as R1.
          destruct R1; inv H1.
          assert (In (insn_call i0 false c0 t v p) 
            (cs2'++[insn_call i0 false c0 t v p] ++ [c] ++ cs')) as HinCs.
            apply in_or_app. right. simpl. auto.
          assert (Hwfc := HBinF2).
          eapply wf_system__wf_cmd with (c:=insn_call i0 false c0 t v p) 
            in Hwfc; eauto.
          inv Hwfc.
          eapply wf_defs_updateAddAL with (t1:=typ1) ; eauto.
            eapply uniqF__lookupTypViaIDFromFdef; eauto.
              eapply wf_system__uniqFdef; eauto.

          destruct n; inv HeqR. inv H1.
          eapply wf_defs_eq; eauto. 
    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[c']).   
      simpl_env. auto.
Unfocus.

Focus.
Case "dsReturnVoid".
  destruct HwfS1 as 
    [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]] 
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]; subst.
  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return_void rid))
             (insn_return_void rid)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  SCase "1".
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.   
    SSCase "1.1".
      apply HwfCall' in HBinF1. simpl in HBinF1.
      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        assert (~ In (getCmdLoc c') (getCmdsLocs cs2')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnotin.
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        destruct n; inversion HBinF1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsLocs (cs2' ++ [c'] ++ [c] ++ cs'))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnodup.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        destruct n; inversion HBinF1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto. 

    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[c']).   
      simpl_env. auto.
Unfocus.

Focus.
Case "dsBranch".
  destruct HwfS1 as 
    [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]
    ]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br bid Cond l1 l2))
             (insn_br bid Cond l1 l2)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split; auto.
  SCase "1".
    split.
      clear - Hreach1 H0 HBinF1 HFinPs1 HmInS HwfSystem.
      eapply wf_system__uniqFdef in HwfSystem; eauto.
      unfold isReachableFromEntry in *.
      destruct (isGVZero (los, nts) c).
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; eauto.
        destruct H0 as [H0 _].
        eapply reachable_successors; eauto.
          simpl. auto.
      
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; eauto.
        destruct H0 as [H0 _].
        eapply reachable_successors; eauto.
          simpl. auto.
    split. 
      clear - H0 HBinF1 HFinPs1 HmInS HwfSystem.
      eapply wf_system__uniqFdef with (f:=F) in HwfSystem; eauto.
      destruct (isGVZero (los, nts) c).
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; auto.
          destruct H0; auto.
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; auto.
          destruct H0; auto.
    split; auto.
    split.
      assert (HwfF := HwfSystem).
      eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
      eapply wf_system__uniqFdef with (f:=F) in HwfSystem; eauto.
      clear - H0 HeqR1 H1 Hinscope1 H HwfSystem HBinF1 HwfF.
      eapply inscope_of_tmn_br in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Focus.
Case "dsBranch_uncond".
  destruct HwfS1 as 
    [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]] 
     [HwfEC HwfCall]]]
    ]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br_uncond bid l0))
             (insn_br_uncond bid l0)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  SCase "1".
    split; auto.
    split.
      clear - Hreach1 H HBinF1 HFinPs1 HmInS HwfSystem.
      eapply wf_system__uniqFdef with (f:=F) in HwfSystem; eauto.
      unfold isReachableFromEntry in *.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
      destruct H as [H _].
      eapply reachable_successors; eauto.
        simpl. auto.
    split.
      clear - H HBinF1 HFinPs1 HmInS HwfSystem.
      eapply wf_system__uniqFdef with (f:=F) in HwfSystem; eauto.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
        destruct H; auto.
    split; auto.
    split.
      assert (HwfF := HwfSystem).
      eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
      eapply wf_system__uniqFdef with (f:=F) in HwfSystem; eauto.
      clear - H0 HeqR1 Hinscope1 H HwfSystem HBinF1 HwfF.
      assert (Hwds := HeqR1).
      eapply inscope_of_tmn_br_uncond with (cs':=cs')(l':=l')(ps':=ps')
        (tmn':=tmn') in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Focus.
Case "dsBop".
  destruct HwfS1 as 
    [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]
    ]; subst.
  remember (inscope_of_cmd F
             (block_intro l3 ps3 (cs3' ++ insn_bop id0 bop0 sz0 v1 v2 :: cs) tmn)
             (insn_bop id0 bop0 sz0 v1 v2)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split.
  SCase "1".
    split; auto.
    split; auto.
    split; auto.
    split.  
    SSCase "1.1".
      destruct cs; simpl_env in *.
      SSSCase "1.1.1".
        assert (~ In id0 (getCmdsLocs cs3')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.
        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        apply BOP_inversion in H.
        assert (In (insn_bop id0 bop0 sz0 v1 v2) 
          (cs3' ++ [insn_bop id0 bop0 sz0 v1 v2])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=insn_bop id0 bop0 sz0 v1 v2) in Hwfc; 
          eauto.
        eapply wf_defs_updateAddAL with (t1:=typ_int sz0) ; eauto.
          eapply uniqF__lookupTypViaIDFromFdef; eauto.
            eapply wf_system__uniqFdef; eauto.
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsLocs (cs3' ++ [insn_bop id0 bop0 sz0 v1 v2] ++ [c] 
          ++ cs))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In (insn_bop id0 bop0 sz0 v1 v2) 
          (cs3' ++ [insn_bop id0 bop0 sz0 v1 v2] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=insn_bop id0 bop0 sz0 v1 v2) in Hwfc; 
          eauto.
        eapply wf_defs_updateAddAL with (t1:=typ_int sz0) ; eauto.
          eapply uniqF__lookupTypViaIDFromFdef; eauto.
            eapply wf_system__uniqFdef; eauto.

    SSCase "1.2".
      exists l3. exists ps3. exists (cs3'++[insn_bop id0 bop0 sz0 v1 v2]).   
      simpl_env. auto.
  split; auto.
Unfocus.

Case "dsFBop". admit.
Case "dsExtractValue". admit.
Case "dsInsertValue". admit.
Case "dsMalloc". admit.
Case "dsFree". admit.
Case "dsAlloca". admit.
Case "dsLoad". admit.
Case "dsStore". admit.
Case "dsGEP". admit.
Case "dsTrunc". admit.
Case "dsExt". admit.
Case "dsCast". admit.
Case "dsIcmp". admit.
Case "dsFcmp". admit.
Case "dsSelect". admit.

Focus.
Case "dsCall".
  destruct HwfS1 as [HwfSys [HmInS [HwfEC [HwfECs HwfCall]]]].
  assert (InProductsB (product_fdef (fdef_intro 
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    eapply lookupFdefViaGV_inv; eauto.
  split; auto.
  split; auto.
  split.
  SCase "1".     
    split.
      simpl. eapply reachable_entrypoint; eauto.
    split.
     apply entryBlockInFdef in H0; auto.
    split; auto.
    split.
     assert (ps'=nil) as EQ.
       eapply entryBlock_has_no_phinodes with (ifs:=nil)(s:=S); eauto.        
     subst.
     apply dom_entrypoint in H0.
     destruct cs'.
       unfold inscope_of_tmn.
       remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
         !! l') as R.
       destruct R.
       destruct HwfEC as [Hreach [HBinF [HFinPs [Hinscope [l1 [ps [cs' Heq]]]]]]]
         ; subst.       
       eapply preservation_dbCall_case; eauto.

       unfold inscope_of_cmd.
       remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
         !! l') as R.
       destruct R. simpl.
       destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n]; 
         try solve [contradict n; auto]. 
       eapply preservation_dbCall_case; eauto.

    exists l'. exists ps'. exists nil. simpl_env. auto.
  split.
  SCase "2".
    split; auto.
  SCase "3".
    simpl. intros b HbInBs. destruct b.
    destruct t; auto.
      (* We cannot show: void cannot be assigned as a call ret. Because a 
         function can have a wrong signature, which cannot be checked
         statically. *)
      admit.
Unfocus.

Case "dsExCall". admit.
Qed.

Lemma wf_operand_list__elim : forall ops f1 b1 insn1 id1,
  wf_operand_list ops ->
  In (f1, b1, insn1, id1) (unmake_list_fdef_block_insn_id ops) ->
  wf_operand f1 b1 insn1 id1.
Proof.
  induction ops; intros f1 b1 insn1 id1 Hwfops Hin; simpl in *.
    inversion Hin.

    inv Hwfops.
    destruct Hin as [Hin | Hin]; auto.
      inv Hin; auto.
Qed.     

Lemma wf_insn__wf_insn_base : forall ifs s m f b insn,
  ~ isPhiNode insn -> wf_insn ifs s m f b insn -> wf_insn_base f b insn.
Proof.
  intros ifs s m f b insn Hnonphi Hwf.
  inv Hwf; auto.
    inv H; auto.
    inv H; auto.
    inv H; auto.
    unfold isPhiNode in Hnonphi. simpl in Hnonphi. contradict Hnonphi; auto.
Qed.

Lemma state_tmn_typing : forall ifs s m f l1 ps1 cs1 tmn1 defs id1 lc,
  isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1) ->
  wf_insn ifs s m f (block_intro l1 ps1 cs1 tmn1) (insn_terminator tmn1) ->
  Some defs = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1 ->
  wf_defs f lc defs ->
  uniqFdef f ->
  In id1 (getInsnOperands (insn_terminator tmn1)) ->
  exists t, exists gv, 
    lookupTypViaIDFromFdef f id1 = munit t /\
    lookupAL _ lc id1 = Some gv /\ wf_genericvalue gv t.
Proof.
  intros ifs s m f l1 ps1 cs1 tmn1 defs id1 lc Hreach HwfInstr Hinscope HwfDefs 
    HuniqF HinOps.
  apply wf_insn__wf_insn_base in HwfInstr; 
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.  
 
  assert (
     In (f, block_intro l1 ps1 cs1 tmn1, insn_terminator tmn1, id1)
     (unmake_list_fdef_block_insn_id
        (make_list_fdef_block_insn_id
           (map_list_id
              (fun id_ : id =>
               (f, block_intro l1 ps1 cs1 tmn1, insn_terminator tmn1, id_))
              id_list)))
    ) as G.
    rewrite H5 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=block_intro l1 ps1 cs1 tmn1)
    (insn1:=insn_terminator tmn1)(id1:=id1) in H6; auto.

  inv H6.
  clear - H11 HwfDefs Hinscope H0 Hreach H9 HuniqF.
  eapply wf_defs_elim; eauto.
    unfold inscope_of_tmn in Hinscope.
    destruct f. destruct f.
    remember ((dom_analyze (fdef_intro (fheader_intro f t i0 a v) b)) !! l1) 
      as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H11 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      destruct J' as [J' _].
      destruct J' as [[cs2 [c1 [cs3 [J1 J2]]]] | [ps2 [p1 [ps3 [J1 J2]]]]]; 
        subst.
        rewrite getCmdsIDs_app. simpl. rewrite J2.
        apply in_or_app. right.
        apply in_or_app. left.
        apply in_or_app. right. simpl. auto.
    
        rewrite getPhiNodesIDs_app. simpl.
        apply in_or_app. left. 
        apply in_or_app. right. simpl. auto.
          
     unfold blockStrictDominates in J'.
     rewrite <- HeqR in J'.
     destruct block'.
     assert (In l0 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as J.       
       destruct J' as [J1 J2].
       apply ListSet.set_diff_intro; auto.
         simpl. intro J. destruct J as [J | J]; auto.
     destruct Hinscope as [_ [Hinscope _]].
     assert (
       lookupBlockViaLabelFromFdef (fdef_intro (fheader_intro f t i0 a v) b) l0 =
       ret block_intro l0 p c t0) as J1.
       apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
         eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
     apply Hinscope with (b1:=block_intro l0 p c t0) in J; auto.
       apply J.
       eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma NoDup__In_cmds_dominates_cmd : forall cs1 c cs2 id1,
  NoDup (getCmdsLocs (cs1 ++ c :: cs2)) ->
  In id1 (getCmdsIDs cs1) ->
  In id1 (cmds_dominates_cmd (cs1 ++ c :: cs2) (getCmdLoc c)).
Proof.
  induction cs1; intros; simpl in *.
    inversion H0.

    inv H.
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c)).
      assert (False) as F.
        apply H3. 
        rewrite e.
        rewrite getCmdsLocs_app. simpl.
        apply in_or_app. right. simpl. auto.
      inversion F.

      destruct (getCmdID a); auto.
      simpl in *. destruct H0 as [H0 | H0]; auto.
Qed.   

Lemma state_cmd_typing : forall ifs s m f b c defs id1 lc,
  NoDup (getBlockLocs b) ->
  isReachableFromEntry f b ->
  wf_insn ifs s m f b (insn_cmd c) ->
  Some defs = inscope_of_cmd f b c ->
  wf_defs f lc defs ->
  uniqFdef f ->
  In id1 (getInsnOperands (insn_cmd c)) ->
  exists t, exists gv, 
    lookupTypViaIDFromFdef f id1 = munit t /\
    lookupAL _ lc id1 = Some gv /\ wf_genericvalue gv t.
Proof.
  intros ifs s m f b c defs id1 lc Hnodup Hreach HwfInstr Hinscope HwfDefs 
    HuniqF HinOps.
  apply wf_insn__wf_insn_base in HwfInstr;
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.  

  assert (
     In (f, b, insn_cmd c, id1)
     (unmake_list_fdef_block_insn_id
        (make_list_fdef_block_insn_id
           (map_list_id
              (fun id_ : id =>
               (f, b, insn_cmd c, id_))
              id_list)))
    ) as G.
    rewrite H5 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=b)(insn1:=insn_cmd c)(id1:=id1) 
    in H6; auto.

  inv H6. 
  eapply wf_defs_elim; eauto.
    unfold inscope_of_cmd in Hinscope.
    destruct b. destruct f. destruct f.
    remember ((dom_analyze (fdef_intro (fheader_intro f t0 i0 a v) b)) !! l0) 
      as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H11 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      simpl in J'.
      destruct J' as [[ps2 [p1 [ps3 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]];
        subst.

        rewrite getPhiNodesIDs_app. simpl.
        apply in_or_app. left. 
        apply in_or_app. right. simpl. auto.
          
        clear - J2 Hnodup.
        apply in_or_app. right.
        apply in_or_app. left. 
          simpl in Hnodup. apply NoDup_inv in Hnodup.
          destruct Hnodup as [_ Hnodup].
          apply NoDup_inv in Hnodup.
          destruct Hnodup as [Hnodup _].
          rewrite_env ((cs1 ++ c1 :: cs2) ++ c :: cs3).
          rewrite_env ((cs1 ++ c1 :: cs2) ++ c :: cs3) in Hnodup.
          apply NoDup__In_cmds_dominates_cmd; auto.
            rewrite getCmdsIDs_app.
            apply in_or_app. right. simpl. rewrite J2. simpl. auto.
    
     clear Hreach H0 HwfDefs.
     unfold blockStrictDominates in J'.
     rewrite <- HeqR in J'.
     destruct block'.
     assert (In l1 (ListSet.set_diff eq_atom_dec bs_contents [l0])) as J.       
       destruct J' as [J1 J2].
       apply ListSet.set_diff_intro; auto.
         simpl. intro J. destruct J as [J | J]; auto.
     destruct Hinscope as [_ [Hinscope _]].
     assert (
       lookupBlockViaLabelFromFdef (fdef_intro (fheader_intro f t0 i0 a v) b) l1
         = ret block_intro l1 p0 c1 t1) as J1.
       apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
         eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
     apply Hinscope with (b1:=block_intro l1 p0 c1 t1) in J; auto.
       apply J.
       eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma wf_operand_list__wf_operand : forall id_list fdef5 block5 insn5 id_ n,
  wf_operand_list (make_list_fdef_block_insn_id (map_list_id
    (fun id_ : id => (fdef5, block5, insn5, id_)) id_list)) ->
  nth_list_id n id_list = Some id_ ->
  wf_operand fdef5 block5 insn5 id_.
Proof.
  induction id_list; intros fdef5 block5 insn5 id_ n Hwfops Hnth.
    destruct n; inversion Hnth.

    simpl in Hwfops.
    inv Hwfops.
    destruct n; inv Hnth; eauto.
Qed.        

Lemma wf_phi_operands__elim : forall f b i0 t0 vls0 vid1 l1 n,
  wf_phi_operands f b i0 t0 vls0 ->
  nth_list_value_l n vls0 = Some (value_id vid1, l1) ->
  (vid1 <> i0 \/ (not (isReachableFromEntry f b))) /\
  exists vb, exists b1,
    lookupBlockViaIDFromFdef f vid1 = Some vb /\
    lookupBlockViaLabelFromFdef f l1 = Some b1 /\
    (blockDominates f vb b1 \/ (not (isReachableFromEntry f b))).
Proof.
  induction vls0; intros.
    destruct n; inversion H0.

    destruct v; inv H.
      destruct n; inv H0; eauto.
        split; auto.        
        exists vb. exists b1. split; auto.
      destruct n; inv H0; eauto.
Qed.

Lemma wf_value_list__wf_value : forall
  (s : system)
  (f : fdef)
  (lc : GVMap)
  (l1 : l)
  (t0 : typ)
  (vid : id)
  l2
  (H2 : wf_value_list
         (make_list_system_fdef_value_typ
            (map_list_value_l
               (fun (value_ : value) (_ : l) => (s, f, value_, t0)) l2)))
  (J : getValueViaLabelFromValuels l2 l1 = ret value_id vid),
  wf_value s f (value_id vid) t0.
Proof.
  intros.
  induction l2; simpl in *.
    inversion J.
    
    inv H2.
    destruct (l0==l1); subst; eauto.
      inv J. auto.
Qed.        

Lemma successors_predOfBlock : forall f l1 ps1 cs1 tmn1 l0 ps0 cs0 tmn0,
  uniqFdef f ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  In l0 (successors_terminator tmn1) ->
  In l1 (predOfBlock (block_intro l0 ps0 cs0 tmn0) (genBlockUseDef_fdef f)).
Proof.
  unfold predOfBlock.
  destruct f. induction b; intros; simpl in *.
    inversion H0.

    assert (G:=H). simpl_env in G.
    apply uniqBlocks_inv in G.
    destruct G as [G1 G2].
    destruct a. simpl.
    apply orb_prop in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0.
      inv H0.
      destruct t; eauto.
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

      eapply IHb in H1; eauto.
        remember (lookupAL (list l) (genBlockUseDef_blocks b nil) l0) as R.
        destruct R; try solve [inversion H1].
        destruct H as [J1 J2].
        simpl in J1.
        inv J1.
        apply InBlocksB_In in H0.
        destruct (eq_atom_dec l1 l2); subst.
          contradict H0; auto.
Admitted.

Lemma const2GV_isnt_stuck : forall TD M gl vc,
  exists gv, const2GV TD M gl vc = Some gv.
 (* what if a constant is stuck~? if int2ptr is not allowed,
    we should prove this, because globals are not changed! *)
Admitted.

Lemma wf_phinodes__getIncomingValuesForBlockFromPHINodes : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  (i0 : id)
  (l0 : l)
  (lc : GVMap)
  (gl : GVMap)
  (M : mem)
  (t : list atom)
  l1 ps1 cs1
  (HeqR : ret t = inscope_of_tmn f 
    (block_intro l1 ps1 cs1 (insn_br_uncond i0 l0)) (insn_br_uncond i0 l0))
  (Hinscope : wf_defs f lc t)
  (HuniqF : uniqFdef f)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  ps2
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 cs1 (insn_br_uncond i0 l0)) f = true)
  (HwfB : wf_block nil s (module_intro los nts ps) f 
             (block_intro l1 ps1 cs1 (insn_br_uncond i0 l0)))
  (H8 : wf_phinodes nil s (module_intro los nts ps) f
         (block_intro l0 ps' cs' tmn') ps2)
  (Hin: exists ps1, ps' = ps1 ++ ps2),
   exists RVs : list (id * GenericValue),
     getIncomingValuesForBlockFromPHINodes (los, nts) M ps2 
       (block_intro l1 ps1 cs1 (insn_br_uncond i0 l0)) gl lc =
       ret RVs.
Proof.
  intros.
  induction ps2; simpl.
    exists nil. auto.
  
    destruct a. inv H8. inv H6.
    assert (exists v, getValueViaLabelFromValuels l2 l1 = Some v) as J.      
      clear - H14 HbInF HuniqF.
      inv H14.
      unfold check_list_value_l in H0.
      remember (split (unmake_list_value_l l2)) as R.
      destruct R.
      destruct H0 as [J1 [J2 J3]].
      eapply In__getValueViaLabelFromValuels; eauto.
      destruct J2 as [_ J2].
      apply J2.
      eapply successors_predOfBlock; eauto.
        simpl. auto.

    destruct J as [v J].
    rewrite J.
    destruct v as [vid | vc].
    Case "vid".
      assert (exists gv1, lookupAL GenericValue lc vid = Some gv1) as J1.
        Focus.
        destruct H14 as [Hwfops Hwfvls].             
        assert (Hnth:=J).
        eapply getValueViaLabelFromValuels__nth_list_value_l in Hnth; eauto.
        destruct Hnth as [n Hnth].
        assert (HwfV:=J).
        eapply wf_value_list__wf_value in HwfV; eauto.
        eapply wf_phi_operands__elim in Hwfops; eauto.
        destruct Hwfops as [Hneqid [vb [b1 [Hlkvb [Hlkb1 Hdom]]]]].
        assert (b1 = block_intro l1 ps1 cs1 (insn_br_uncond i0 l0)) 
          as EQ.
          clear - Hlkb1 HbInF HuniqF.
          apply blockInFdefB_lookupBlockViaLabelFromFdef in HbInF; auto.
          rewrite HbInF in Hlkb1. inv Hlkb1; auto.

        subst.
        clear - Hdom Hinscope HeqR J Hreach H2 HbInF Hlkvb Hlkb1 HuniqF.
        destruct Hdom as [J3 | J3]; try solve [contradict Hreach; auto].
        clear Hreach.        
        unfold blockDominates in J3.         
        destruct vb.
        unfold inscope_of_tmn in HeqR.
        destruct f. destruct f.
        remember ((dom_analyze (fdef_intro (fheader_intro f t2 i1 a v) b)) !! l1)
          as R1.
        destruct R1.
        symmetry in HeqR.    
        apply fold_left__spec in HeqR.
        destruct (eq_atom_dec l3 l1); subst.
        SCase "l3=l1".
          destruct HeqR as [HeqR _].
          assert (In vid t) as G.
            clear - J HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
            assert (J':=Hlkvb).
            apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
            apply lookupBlockViaLabelFromFdef_inv in Hlkb1; auto.
            destruct Hlkb1 as [J1 J2].
            eapply blockInFdefB_uniq in J2; eauto.
            destruct J2 as [J2 [J4 J5]]; subst.
            apply lookupBlockViaIDFromFdef__InGetBlockIDs in J'.
            simpl in J'.
            apply HeqR.
            rewrite_env ((getPhiNodesIDs ps1 ++ getCmdsIDs cs1)++getArgsIDs a).
            apply in_or_app; auto.       
          apply wf_defs_elim with (id1:=vid) in Hinscope; auto.
          destruct Hinscope as [? [gv1 [? [Hinscope ?]]]].
          exists gv1. auto.

        SCase "l3<>l1".
          assert (In l3 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as G.
            apply ListSet.set_diff_intro; auto.
              simpl. intro JJ. destruct JJ as [JJ | JJ]; auto.
          assert (
            lookupBlockViaLabelFromFdef 
              (fdef_intro (fheader_intro f t2 i1 a v) b) l3 = 
              ret block_intro l3 p c t1) as J1.
            clear - Hlkvb HuniqF.
            apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
            apply blockInFdefB_lookupBlockViaLabelFromFdef in Hlkvb; auto.
          destruct HeqR as [_ [HeqR _]].
          apply HeqR in J1; auto.
          assert (In vid t) as InVid.
            clear - J1 HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
            apply J1.
            apply lookupBlockViaIDFromFdef__InGetBlockIDs in Hlkvb; auto.
          apply wf_defs_elim with (id1:=vid) in Hinscope; auto.
          destruct Hinscope as [? [gv1 [? [Hinscope ?]]]].
          exists gv1. auto.
        Unfocus.
  
      destruct J1 as [gv1 J1].
      rewrite J1. 
      apply IHps2 in H7.
        destruct H7 as [RVs H7].
        rewrite H7. 
        exists ((i1, gv1) :: RVs). auto.
  
        destruct Hin as [ps3 Hin]. subst.
        exists (ps3++[insn_phi i1 t0 l2]).
        simpl_env. auto.
  
    Case "vc".
      destruct (@const2GV_isnt_stuck (los,nts) M gl vc).
      rewrite H.
      apply IHps2 in H7.
        destruct H7 as [RVs H7].
        rewrite H7. 
        exists ((i1, x) :: RVs). auto.
  
        destruct Hin as [ps3 Hin]. subst.
        exists (ps3++[insn_phi i1 t0 l2]).
        simpl_env. auto.
Qed.

Lemma progress : forall S1,
  wf_State S1 -> 
    ds_isFinialState S1 = true \/ exists S2, exists tr, dsInsn S1 S2 tr.
Proof.
  intros S1 HwfS1.
  destruct S1 as [s [los nts] ps ecs gl fs M].
  destruct HwfS1 as [HwfSys1 [HmInS1 HwfECs]].
  destruct ecs.
    admit. (* we should rule out this case. *)

  destruct e as [f b cs tmn lc als].
  destruct HwfECs as [[Hreach [HbInF [HfInPs [Hinscope [l1 [ps1 [cs1 Heq]]]]]]] 
                      [HwfECs HwfCall]].
  subst b.
  destruct cs.
  Case "cs=nil".
    remember (inscope_of_tmn f (block_intro l1 ps1 (cs1 ++ nil) tmn) tmn) as R.
    destruct R; try solve [inversion Hinscope].
    destruct tmn.
    SCase "tmn=ret".
      simpl in HwfCall.
      destruct ecs.
        simpl; auto.      

        right.
        destruct e as [f' b' cs' tmn' lc' als'].
        assert (J:=HbInF).
        apply HwfCall in J. clear HwfCall.
        destruct cs'; try solve [inversion J].
        destruct c; try solve [inversion J]. clear J.
        assert (exists M', free_allocas (los,nts) M als = Some M') as J.
          admit.
        destruct J as [M' J].
        assert (exists lc'', 
          returnUpdateLocals (los,nts) M' (insn_call i1 n c t0 v0 p) v lc lc' gl
            = Some lc'') as Hretup.
          unfold returnUpdateLocals. simpl.
          destruct n.
            exists lc'. auto.
            
            destruct v as [vid | vc].
              assert (HwfInstr:=HbInF).
              eapply wf_system__wf_tmn in HwfInstr; eauto.
              assert (exists t, exists gv, 
                lookupTypViaIDFromFdef f vid = munit t /\
                lookupAL _ lc vid = Some gv /\ 
                wf_genericvalue gv t) as Hlkup.
                assert (In vid (getInsnOperands (insn_terminator 
                  (insn_return i0 t (value_id vid))))) as HinOps.
                  simpl. auto.
                eapply state_tmn_typing in HwfInstr; eauto.
                  eapply wf_system__uniqFdef; eauto.

              destruct Hlkup as [gt [gv [Hlktyp [Hlkup Hwfgv]]]].
              simpl.
              rewrite Hlkup. exists (updateAddAL GenericValue lc' i1 gv). auto.

              simpl.
              destruct (@const2GV_isnt_stuck (los,nts) M' gl vc).
              rewrite H.
              exists (updateAddAL GenericValue lc' i1 x). auto.
          
            destruct Hretup as [lc'' Hretup].
            exists (mkState s (los, nts) ps ((mkEC f' b' cs' tmn' lc'' als')::
              ecs) gl fs M').
            exists trace_nil.
            eauto.  

    SCase "tmn=ret void". admit.
    SCase "tmn=br". admit.
    SCase "tmn=br_uncond". 
      right.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists ps', exists cs', exists tmn',
        Some (block_intro l2 ps' cs' tmn') = lookupBlockViaLabelFromFdef f l2) 
          as HlkB.
        eapply wf_system__wf_tmn in HbInF; eauto.
        inv HbInF.        
        exists ps1. exists (cs1++nil). exists (insn_br_uncond i0 l2).
        rewrite H6. 
        apply lookupBlockViaLabelFromFdef_inv in H6; auto.
        destruct H6 as [H6 _]; subst. auto.

      destruct HlkB as [ps' [cs' [tmn' HlkB]]].
      assert (exists RVs, 
        getIncomingValuesForBlockFromPHINodes (los, nts) M ps'
          (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc =
        Some RVs) as J.
        assert (HwfB := HbInF).
        eapply wf_system__blockInFdefB__wf_block in HwfB; eauto.
        eapply wf_system__lookup__wf_block in HlkB; eauto.
        clear - HeqR Hinscope HbInF HlkB HwfB Hreach HuniqF.
        inv HlkB. clear H9 H10.
        eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes; eauto.      
          simpl in *.
          apply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1++nil)
            (tmn:=insn_br_uncond i0 l2); simpl; auto.

          exists nil. auto.

      destruct J as [RVs J].
      assert (exists lc', switchToNewBasicBlock (los, nts) M
        (block_intro l2 ps' cs' tmn') 
        (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc = 
          Some lc') as Hswitch.
        unfold switchToNewBasicBlock. simpl.
        rewrite J. 
        exists (updateValuesForNewBlock RVs lc). auto.
      destruct Hswitch as [lc' Hswitch].
      exists (mkState s (los, nts) ps 
              ((mkEC f (block_intro l2 ps' cs' tmn') cs' tmn' lc' als)
              ::ecs) gl fs M).
      exists trace_nil. eauto.

    SCase "tmn=unreachable". admit.

  Case "cs<>nil".
    admit.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
