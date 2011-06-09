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
Require Import assoclist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import ssa_analysis.
Require Import ssa_static.
Require Import ssa_dynamic.
Require Import ssa_props.

Export LLVMwf.
Export AtomSet.

Definition getCmdID' (i:cmd) : option id :=
match i with
| insn_bop id _ sz v1 v2 => Some id
| insn_fbop id _ _ _ _ => Some id
(* | insn_extractelement id typ0 id0 c1 => id *)
(* | insn_insertelement id typ0 id0 typ1 v1 c2 => id *)
| insn_extractvalue id typs id0 c1 => Some id
| insn_insertvalue id typs id0 typ1 v1 c2 => Some id 
| insn_malloc id _ _ _ => Some id
| insn_free id _ _ => None
| insn_alloca id _ _ _ => Some id
| insn_load id typ1 v1 _ => Some id
| insn_store id typ1 v1 v2 _ => None
| insn_gep id _ _ _ _ => Some id
| insn_trunc id _ typ1 v1 typ2 => Some id 
| insn_ext id _ sz1 v1 sz2 => Some id
| insn_cast id _ typ1 v1 typ2 => Some id
| insn_icmp id cond typ v1 v2 => Some id
| insn_fcmp id cond typ v1 v2 => Some id 
| insn_select id v0 typ v1 v2 => Some id
| insn_call id nr _ typ v0 paraml => if nr then None else Some id
end.

Fixpoint cmds_dominates_cmd_aux (cs:cmds) (id0:id) (ctx:list atom) : list atom :=
match cs with
| nil => ctx
| c1::cs' => 
    if eq_atom_dec (getCmdID c1) id0 then ctx
    else
      match getCmdID' c1 with
      | Some id1 =>cmds_dominates_cmd_aux cs' id0 (id1::ctx)
      | None => cmds_dominates_cmd_aux cs' id0 ctx
      end
end.

Definition cmds_dominates_cmd (cs:cmds) (id0:id) : list atom :=
cmds_dominates_cmd_aux cs id0 nil. 

Fixpoint getCmdsIDs' (cs:cmds) : list atom :=
match cs with
| nil => nil
| c::cs' =>
    match getCmdID' c with 
    | Some id1 => id1::getCmdsIDs' cs'
    | None => getCmdsIDs' cs'
    end
end.

Fixpoint getPhiNodesIDs' (ps: phinodes) : list atom :=
match ps with
| nil => nil
| p::ps' => getPhiNodeID p :: getPhiNodesIDs' ps'
end.

Definition getBlockIDs' (b:block) : list atom :=
let '(block_intro _ ps cs _) := b in
getPhiNodesIDs' ps ++ getCmdsIDs' cs.

Fixpoint getArgsIDs' (la:args) : list atom :=
match la with
| nil => nil
| (_,id1)::la' => id1::getArgsIDs' la'
end.

Definition inscope_of_block (f:fdef) (l1:l) (opt_ctx:option (list atom)) (lbl:l)
  :=
  match opt_ctx with
  | Some ctx =>
     match lookupBlockViaIDFromFdef f lbl with
     | None => None
     | Some b => 
         if eq_atom_dec lbl l1 then Some ctx
         else Some (getBlockIDs' b ++ ctx)
     end
  | None => None
  end.

Definition inscope_of_cmd (f:fdef) (b1:block) (c:cmd) : option (list atom) :=
let id0 := getCmdID c in
let '(block_intro l1 ps cs _) := b1 in
let '(fdef_intro (fheader_intro _ _ la) _) := f in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l1 dt in
fold_left (inscope_of_block f l1) els
  (Some (getPhiNodesIDs' ps ++ cmds_dominates_cmd cs id0 ++ getArgsIDs' la))
.

Definition inscope_of_tmn (f:fdef) (b1:block) (tmn:terminator) 
  : option (list atom) :=
let '(block_intro l1 ps cs _) := b1 in
let '(fdef_intro (fheader_intro _ _ la) _) := f in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l1 dt in
fold_left (inscope_of_block f l1) els
  (Some (getPhiNodesIDs' ps ++ getCmdsIDs' cs ++ getArgsIDs' la))
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

(* FIXME: this could be the tricky part. *)
Inductive wf_genericvalue : GenericValue -> typ -> Prop :=
| wf_genericvalue_intro : forall gv t, wf_genericvalue gv t.

Inductive wf_defs (f:fdef) (lc:GVMap) : list atom -> Prop :=
| wf_defs_nil : wf_defs f lc nil
| wf_defs_cons : forall id1 t1 gv1 defs',
    lookupTypViaIDFromFdef f id1 = Some t1 ->
    lookupAL _ lc id1 = Some gv1 ->
    wf_genericvalue gv1 t1 ->
    wf_defs f lc defs' ->
    wf_defs f lc (id1::defs').

Lemma wf_defs__forall : forall ids1 F lc,
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

Lemma forall__wf_defs : forall ids1 F lc,
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
  apply forall__wf_defs.
  intros id1 Hin.
  destruct H as [J1 J2].
  eapply wf_defs__forall in H0; eauto.
Qed.

Lemma wf_defs_updateAddAL : forall g TD Mem' Result lc gl F' lc' ids1 ids2 i1,
  ret g = getOperandValue TD Mem' Result lc gl ->
  wf_defs F' lc' ids1 ->
  set_eq _ (i1::ids1) ids2 ->
  wf_defs F' (updateAddAL GenericValue lc' i1 g) ids2.
Proof.
  intros g TD Mem' Result lc gl F' lc' ids1 ids2 i1 Hget HwfDefs Heq.
  (* need to show that g is welltyped.*)
Admitted.

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

Lemma getCmdID_getCmdID' : forall a i0,
  getCmdID' a = Some i0 ->
  getCmdID a = i0.
Proof.
  intros a i0 H.
  destruct a; inv H; auto.
    simpl. destruct n; inv H1; auto.
Qed.

Lemma set_eq_app : forall x1 x2 y1 y2,
  set_eq atom x1 y1 -> set_eq atom x2 y2 -> set_eq atom (x1++x2) (y1++y2).
Admitted.

Lemma set_eq_swap : forall x1 x2,
  set_eq atom (x1++x2) (x2++x1).
Admitted.

Lemma set_eq_empty_inv2 : forall x, 
  set_eq atom (ListSet.empty_set _) x -> x = ListSet.empty_set _.
Proof.
  intros.
  apply set_eq_sym in H.
  eapply set_eq_empty_inv; eauto.
Qed.

Lemma cmds_dominates_cmd_aux__eq : forall cs id0 defs1 defs2,
  set_eq _ defs1 defs2 ->
  set_eq _ (cmds_dominates_cmd_aux cs id0 defs1)
           (cmds_dominates_cmd_aux cs id0 defs2).
Proof.
  induction cs; intros id0 defs1 defs2 Heq; simpl; auto.
    destruct (eq_atom_dec (getCmdID a) id0); auto.
    destruct (getCmdID' a); auto.
Admitted.

Lemma cmds_dominates_cmd_aux__commut : forall cs id0 defs1 defs2,
  set_eq _ (cmds_dominates_cmd_aux cs id0 (defs1 ++ defs2))
           (defs1 ++ cmds_dominates_cmd_aux cs id0 defs2).
Proof.
  induction cs; intros; simpl.
    apply set_eq_refl.

    remember (getCmdID a) as id1.
    destruct (eq_atom_dec id1 id0); subst.
      apply set_eq_refl.

      remember (getCmdID' a) as R.
      destruct R; auto.
        eapply set_eq_trans with 
          (y:=cmds_dominates_cmd_aux cs id0 (defs1 ++ i0 :: defs2)); eauto.
        apply cmds_dominates_cmd_aux__eq.
          rewrite_env (([i0]++defs1)++defs2).
          rewrite_env ((defs1++[i0])++defs2).
          apply set_eq_app.
             apply set_eq_swap; auto.
             apply set_eq_refl.
Qed.

Lemma getCmdsIDs__cmds_dominates_cmd : forall cs2' c',
  ~ In (getCmdID c') (LLVMlib.getCmdsIDs cs2') ->
  set_eq _ (getCmdsIDs' (cs2' ++ [c']))
  (cmds_dominates_cmd (cs2' ++ [c']) (getCmdID c') ++ 
    match getCmdID' c' with
    | Some id1 => [id1]
    | None => nil
    end).   
Proof.
  unfold cmds_dominates_cmd.
  induction cs2'; intros c' Hnotin.
    simpl in *.
    destruct (eq_atom_dec (getCmdID c') (getCmdID c')) as [_ | n];
      try solve [contradict n; auto].
      remember (getCmdID' c') as R.
      destruct R; simpl_env; apply set_eq_refl.

    simpl in *.
    assert (~ In (getCmdID c') (getCmdsIDs cs2')) as J.
      auto.
    apply IHcs2' in J.
    remember (getCmdID' a) as R1.
    remember (getCmdID' c') as R2.
    destruct (eq_atom_dec (getCmdID a) (getCmdID c')); 
      try solve [contradict e; auto].
    destruct R1; auto.
      simpl_env.
      apply set_eq_trans with (y:=[i0] ++
        cmds_dominates_cmd_aux (cs2' ++ [c']) (getCmdID c') nil ++
        match R2 with
        | ret id1 => [id1]
        | merror => nil
        end).
        apply set_eq_app; auto using set_eq_refl.

        rewrite_env (([i0] ++
          cmds_dominates_cmd_aux (cs2' ++ [c']) (getCmdID c') nil) ++
          match R2 with
          | ret id1 => [id1]
          | merror => nil
          end).
        apply set_eq_app.
          apply set_eq_sym.
          rewrite_env ([i0]++nil).
          apply cmds_dominates_cmd_aux__commut.
          apply set_eq_refl.
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
  destruct (lookupBlockViaIDFromFdef f l').
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
  destruct (lookupBlockViaIDFromFdef f l').
    destruct (eq_atom_dec l' l1); subst; inv H.
      exists (r1++init2). auto using set_eq_refl.
      exists (getBlockIDs' b ++ init1 ++ init2). 
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

    destruct (lookupBlockViaIDFromFdef f a).
      destruct (eq_atom_dec a l1); subst; auto.
        apply IHls0 with (init2:=init2) in H; auto.
          simpl_env in H. auto.
      rewrite fold_left__none in H. inversion H.
Qed.

Lemma inscope_of_cmd_tmn : forall f l2 ps2 cs2' c' tmn' ids1,
~ In (getCmdID c') (getCmdsIDs cs2') ->
Some ids1 = inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']) tmn') c' ->
exists ids2, 
  Some ids2 = inscope_of_tmn f (block_intro l2 ps2 (cs2'++[c']) tmn') tmn' /\
  match getCmdID' c' with
  | Some id1 => set_eq _ (id1::ids1) ids2
  | None => set_eq _ ids1 ids2
  end.
Proof.
  intros f l2 ps2 cs2' c' tmn' ids1 Hnotin Hinscope.
  unfold inscope_of_cmd in Hinscope.
  unfold inscope_of_tmn.
  destruct f as [[? ? la] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro t i0 la) bs)) !! l2) as R.
  destruct R as [R_contents R_bound]. simpl in *.
  apply getCmdsIDs__cmds_dominates_cmd in Hnotin.
  symmetry in Hinscope.
  remember (getCmdID' c') as R.
  destruct R.
    apply fold_left__opt_union with (init2:=[i1]) in Hinscope.
    destruct Hinscope as [r2 [Hinscope Heq]].
    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs' ps2) ++
      ((getCmdsIDs' (cs2' ++ [c'])) ++ (getArgsIDs' la)))) in Hinscope.
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
         (getCmdID c') ++ [i1]) ++ getArgsIDs' la).
        simpl_env.
        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_swap.          

        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_sym; auto.          

    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs' ps2) ++ 
      ((getCmdsIDs' (cs2' ++ [c'])) ++ (getArgsIDs' la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_app; auto using set_eq_refl.
      simpl_env in Hnotin.
      apply set_eq_sym; auto.          
Qed.

Lemma set_eq__rewrite_env : forall x1 x2 x3 y1 y2 y3,
  set_eq atom ((x1 ++ x2) ++ x3) ((y1 ++ y2) ++ y3) ->
  set_eq atom (x1 ++ x2 ++ x3) (y1 ++ y2 ++ y3).
Proof.
  intros.
  simpl_env in H. auto.
Qed.

Lemma cmds_dominates_cmd__cmds_dominates_cmd : forall cs2' c' c cs',
  NoDup (getCmdsIDs (cs2'++[c']++[c]++cs')) ->
  set_eq _ (cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdID c))
    (cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdID c') ++
     match getCmdID' c' with
     | Some id1 => [id1]
     | None => nil
     end).   
Proof.
  unfold cmds_dominates_cmd in *.
  induction cs2'; intros c' c cs' Hnodup.
    simpl in *.
    inv Hnodup. simpl in H1.
    remember (getCmdID' c') as R.
    destruct (eq_atom_dec (getCmdID c') (getCmdID c)).
      contradict e; auto.

      destruct (eq_atom_dec (getCmdID c) (getCmdID c)) as [_|n1];
        try solve [contradict n1; auto].
      destruct (eq_atom_dec (getCmdID c') (getCmdID c')) as [_|n2];
        try solve [contradict n2; auto].
      destruct R; auto using set_eq_refl.

    simpl in *.
    inv Hnodup.
    rewrite getCmdsIDs_app in H1.
    apply NotIn_inv in H1.    
    destruct H1 as [H11 H12].
    simpl in H12.
    destruct (eq_atom_dec (getCmdID a) (getCmdID c)) as [e1 | ];
      try solve [contradict e1; auto].
    destruct (eq_atom_dec (getCmdID a) (getCmdID c')) as [e1 | ];
      try solve [contradict e1; auto].
    destruct (getCmdID' a); auto.
      apply IHcs2' in H2. clear IHcs2'.
      rewrite_env ([i0]++nil).
      apply set_eq_trans with (y:=[i0]++
        (cmds_dominates_cmd_aux (cs2' ++ c' :: c :: cs') (getCmdID c) nil)).
        apply cmds_dominates_cmd_aux__commut.
      apply set_eq_trans with (y:=[i0] ++
        (cmds_dominates_cmd_aux (cs2' ++ c' :: c :: cs') (getCmdID c') nil ++
         match getCmdID' c' with
         | ret id1 => [id1]
         | merror => nil
         end)).
       apply set_eq_app; auto using set_eq_refl.

       rewrite_env (([i0] ++
         cmds_dominates_cmd_aux (cs2' ++ c' :: c :: cs') (getCmdID c') nil) ++
         match getCmdID' c' with
         | ret id1 => [id1]
         | merror => nil
         end).
       apply set_eq_app; auto using set_eq_refl.
       apply set_eq_sym.
         apply cmds_dominates_cmd_aux__commut.
Qed.      

Lemma inscope_of_cmd_cmd : forall f l2 ps2 cs2' c' c cs' tmn' ids1,
NoDup (getCmdsIDs (cs2'++[c']++[c]++cs')) ->
Some ids1 = inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn') c' 
  ->
exists ids2, 
  Some ids2 = 
    inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn') c /\
  match getCmdID' c' with
  | Some id1 => set_eq _ (id1::ids1) ids2
  | None => set_eq _ ids1 ids2
  end.
Proof.
  intros f l2 ps2 cs2' c' c cs' tmn' ids1 Hnodup Hinscope.
  unfold inscope_of_cmd in Hinscope.
  unfold inscope_of_cmd.
  destruct f as [[? ? la] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro t i0 la) bs)) !! l2) as R.
  destruct R as [R_contents R_bound].
  apply cmds_dominates_cmd__cmds_dominates_cmd in Hnodup. simpl in *.
  symmetry in Hinscope.
  remember (getCmdID' c') as R.
  destruct R.
    apply fold_left__opt_union with (init2:=[i1]) in Hinscope.
    destruct Hinscope as [r2 [Hinscope Heq]].
    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs' ps2) ++ 
      ((cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdID c)) ++
      (getArgsIDs' la)))) in Hinscope.
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
         (getCmdID c') ++ [i1]) ++ getArgsIDs' la).
        simpl_env.
        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_swap.          

        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_sym; auto.          

    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs' ps2) ++
      ((cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdID c)) ++
      (getArgsIDs' la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_app; auto using set_eq_refl.
      simpl_env in Hnodup.
      apply set_eq_sym; auto.          
Qed.

Lemma fold_left__bound_blocks : forall ls0 t i0 la bs l0 init,
  incl ls0 (bound_blocks bs) ->
  exists r, 
    fold_left (inscope_of_block 
                (fdef_intro (fheader_intro t i0 la) bs) l0) ls0 (Some init) = 
      Some r.
Admitted.

Lemma fold_left__spec : forall ls0 l0 init r f,
  fold_left (inscope_of_block f l0) ls0 (Some init) = Some r ->
    incl init r /\
    (forall l1 b1, 
      In l1 ls0 -> l1 <> l0 -> 
      lookupBlockViaIDFromFdef f l1 = Some b1 ->
      incl (getBlockIDs' b1) r) /\
    (forall id1,
      In id1 r ->
      In id1 init \/
      exists b1, exists l1, l1 <> l0 /\ In l1 ls0 /\
        lookupBlockViaIDFromFdef f l1 = Some b1 /\
        In id1 (getBlockIDs' b1)
    ).
Admitted.

Lemma fold_left__incl : forall ls0 f l0 init ls1 r0 r1,
  incl ls0 ls1 ->
  fold_left (inscope_of_block f l0) ls0 (Some init) = Some r0 ->
  fold_left (inscope_of_block f l0) ls1 (Some init) = Some r1 ->
  incl r0 r1.
Admitted.

Lemma inscope_of_tmn_br_aux : forall F l3 ps cs tmn ids0 l' ps' cs' tmn' l0,
uniqFdef F ->
blockInFdefB (block_intro l3 ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs tmn) tmn ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs' ps')) ids0.
Proof.
  intros F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 Huniq HBinF Hsucc Hinscope Hlkup.
  symmetry in Hlkup.
  assert (J:=Hlkup).
  apply lookupBlockViaLabelFromFdef_inv in J; auto.
  destruct J as [Heq J]; subst.
  unfold inscope_of_tmn in Hinscope.
  unfold inscope_of_tmn. unfold inscope_of_cmd.
  destruct F as [[? ? la] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro t i0 la) bs)) !! l3)as defs3.
  remember ((dom_analyze (fdef_intro (fheader_intro t i0 la) bs)) !! l')as defs'.
  destruct defs3 as [contents3 inbound3]. 
  destruct defs' as [contents' inbound']. 
  simpl in *.
  assert (incl contents' contents3) as Hsub.


    admit. (* by correctness of domination analysis *)
  destruct cs'.
  Case "cs'=nil".
    assert (J1:=inbound').
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs' ps' ++ 
      getCmdsIDs' nil ++ getArgsIDs' la)(t:=t)(i0:=i0)(la:=la)(bs:=bs)(l0:=l')
      in J1.
    destruct J1 as [r J1].
    exists r. split; auto.
    clear - Hinscope J1 Hsub HBinF.
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
      destruct J as [b1 [l1 [J7 [J8 [J9 J10]]]]].
      apply Hsub in J8.
        destruct (eq_atom_dec l1 l3); subst.
          simpl in J9. 
          assert (b1=block_intro l3 ps cs tmn) as EQ.
            clear - J9 HBinF. admit.
          subst.
          simpl in J10.
          apply J4.
          rewrite_env 
            ((getPhiNodesIDs' ps ++ getCmdsIDs' cs) ++ getArgsIDs' la).
          apply in_or_app; auto.

          apply J5 in J9; auto.
          
  Case "cs'<>nil".
    assert (J1:=inbound').
    unfold cmds_dominates_cmd. simpl.
    destruct (eq_atom_dec (getCmdID c) (getCmdID c)) as [_ | n]; 
      try solve [contradict n; auto].
    simpl_env.
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs' ps' ++ 
      getArgsIDs' la)(t:=t)(i0:=i0)(la:=la)(bs:=bs)(l0:=l') in J1.
    destruct J1 as [r J1].
    exists r. split; auto.
    clear - Hinscope J1 Hsub HBinF.
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
      destruct J as [b1 [l1 [J7 [J8 [J9 J10]]]]].
      apply Hsub in J8.
        destruct (eq_atom_dec l1 l3); subst.
          simpl in J9. 
          assert (b1=block_intro l3 ps cs tmn) as EQ.
            clear - J9 HBinF. admit.
          subst.
          simpl in J10.
          apply J4.
          rewrite_env 
            ((getPhiNodesIDs' ps ++ getCmdsIDs' cs) ++ getArgsIDs' la).
          apply in_or_app; auto.

          apply J5 in J9; auto. 
Qed.

Lemma inscope_of_tmn_br_uncond : forall F l3 ps cs bid ids0 l' ps' cs' tmn' l0,
uniqFdef F ->
blockInFdefB (block_intro l3 ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0)) 
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs' ps')) ids0.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

Lemma inscope_of_tmn_br : forall F l0 ps cs bid l1 l2 ids0 l' ps' cs' tmn' Cond 
  c TD Mem0 gl lc,
uniqFdef F ->
blockInFdefB (block_intro l0 ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) 
  (insn_br bid Cond l1 l2) ->
getOperandValue TD Mem0 Cond lc gl = ret c ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs' ps')) ids0.
Proof.
  intros.
  remember (isGVZero TD c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

Lemma wf_defs_br : forall TD Mem0 Cond lc gl c l' ps' cs' lc' F l1 l2 bid tmn'
  (H : getOperandValue TD Mem0 Cond lc gl = ret c)
  (H0 : ret block_intro l' ps' cs' tmn' =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1))
  (l3 : l)
  (ps3 : phinodes)
  (cs3' : list cmd)
  (H1 : switchToNewBasicBlock TD Mem0 (block_intro l' ps' cs' tmn')
         (block_intro l3 ps3 (cs3' ++ nil) (insn_br bid Cond l1 l2)) gl lc =
       ret lc')
  (t : list atom)
  (Hinscope1 : wf_defs F lc t)
  (ids0' : list atom)
  (HeqR12 : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs' ps')) t),
  wf_defs F lc' ids0'.
Admitted.

Lemma wf_defs_br_uncond : forall lc l' ps' cs' lc' F bid tmn' gl l0 TD 
  Mem0
  (H0 : ret block_intro l' ps' cs' tmn' =lookupBlockViaLabelFromFdef F l0)
  (l3 : l)
  (ps3 : phinodes)
  (cs3' : list cmd)
  (H1 : switchToNewBasicBlock TD Mem0 (block_intro l' ps' cs' tmn')
         (block_intro l3 ps3 (cs3' ++ nil) (insn_br_uncond bid l0)) gl lc =
       ret lc')
  (t : list atom)
  (Hinscope1 : wf_defs F lc t)
  (ids0' : list atom)
  (HeqR12 : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs' ps')) t),
  wf_defs F lc' ids0'.
Admitted.

Lemma wf_system__wf_insn : forall l1 ps1 cs1 tmn1 f ps los nts s ifs,
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
                clear - HbInF H1. admit.
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
  NoDup (getBlockIDs b).
Admitted.

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
        assert (~ In (getCmdID c') (getCmdsIDs cs2')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsIDs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.
        clear - HeqR2 Hinscope2 H1 H HwfSystem Hnotin.
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID' c') as R.
        destruct c'; try solve [inversion H].
        unfold returnUpdateLocals in H1. simpl in H1.
        destruct R.
          destruct n; inv HeqR.
          remember (getOperandValue (los,nts) Mem' Result lc gl) as R1.
          destruct R1; inv H1.
          (* ?! how to know if g is well-typed!. *)
          eapply wf_defs_updateAddAL; eauto.

          destruct n; inv HeqR. inv H1.
          eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsIDs (cs2' ++ [c'] ++ [c] ++ cs'))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        clear - HeqR2 Hinscope2 H1 H HwfSystem Hnodup.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID' c') as R.
        destruct c'; try solve [inversion H].
        unfold returnUpdateLocals in H1. simpl in H1.
        destruct R.
          destruct n; inv HeqR.
          remember (getOperandValue (los,nts) Mem' Result lc gl) as R1.
          destruct R1; inv H1.
          eapply wf_defs_updateAddAL; eauto.

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
        assert (~ In (getCmdID c') (getCmdsIDs cs2')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsIDs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnotin.
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID' c') as R.
        destruct c'; try solve [inversion H].
        destruct n; inversion HBinF1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsIDs (cs2' ++ [c'] ++ [c] ++ cs'))) as Hnodup.
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
        remember (getCmdID' c') as R.
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
      eapply wf_system__uniqFdef with (f:=F) in HwfSystem; eauto.
      clear - H0 HeqR1 H1 Hinscope1 H HwfSystem HBinF1.
      eapply inscope_of_tmn_br in HeqR1; eauto.
      destruct HeqR1 as [ids0' HeqR1].
      destruct cs'.
        destruct HeqR1 as [HeqR11 HeqR12]. 
        rewrite <- HeqR11.
        eapply wf_defs_br; eauto.

        destruct HeqR1 as [HeqR11 HeqR12]. 
        rewrite <- HeqR11.
        eapply wf_defs_br; eauto.

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
      eapply wf_system__uniqFdef with (f:=F) in HwfSystem; eauto.
      clear - H0 HeqR1 Hinscope1 H HwfSystem HBinF1.
      eapply inscope_of_tmn_br_uncond with (cs':=cs')(l':=l')(ps':=ps')
        (tmn':=tmn') in HeqR1; eauto.
      destruct HeqR1 as [ids0' HeqR1].
      destruct cs'.
        destruct HeqR1 as [HeqR11 HeqR12]. 
        rewrite <- HeqR11.
        eapply wf_defs_br_uncond; eauto.

        destruct HeqR1 as [HeqR11 HeqR12]. 
        rewrite <- HeqR11.
        eapply wf_defs_br_uncond; eauto.

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
        assert (~ In id0 (getCmdsIDs cs3')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsIDs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.
        clear - HeqR1 Hinscope1 H Hnotin.
        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        apply BOP_inversion in H.
        admit. (* need to prove that gv3 is wf-typed. *)
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsIDs (cs3' ++ [insn_bop id0 bop0 sz0 v1 v2] ++ [c] 
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
        admit. (* need to prove that gv3 is wf-typed. *)

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
  split; auto.
  split; auto.
  split.
  SCase "1".
    split.
      simpl. eapply reachable_entrypoint; eauto.
    split.
      apply entryBlockInFdef in H0; auto.
    split.
      eapply lookupFdefViaGV_inv; eauto.
    split.
      admit. (* need to prove that initial state is good! *)
    exists l'. exists ps'. exists nil. simpl_env. auto.
  split.
  SCase "2".
    split; auto.
  SCase "3".
    simpl. intros b HbInBs. destruct b.
    destruct t; auto.
      admit. (* static: void cannot be assigned as a call ret. *)
Unfocus.

Case "dsExCall". admit.
Qed.

Lemma state_tmn_typing : forall ifs s m f b tmn1 defs id1 lc,
  wf_insn ifs s m f b (insn_terminator tmn1) ->
  Some defs = inscope_of_tmn f b tmn1 ->
  wf_defs f lc defs ->
  In id1 (getInsnOperands (insn_terminator tmn1)) ->
  exists t, exists gv, lookupAL _ lc id1 = Some gv /\ wf_genericvalue gv t.
Proof.
  intros ifs s m f b tmn1 defs id1 lc HwfInstr Hinscope HwfDefs HinOps.
  inv HwfInstr.
Case "ret".
  unfold getInsnOperands, getTerminatorOperands, getValueIDs in HinOps.
  destruct value5 as [vid | vc]; try solve [inversion HinOps].
  simpl in HinOps. 
  destruct HinOps as [HinOps | HinOps]; try solve [inversion HinOps].
  subst.
  inv H7.
  simpl in H6. unfold getValueIDs in H6. simpl in H6.
  destruct id_list; inv H6.
  simpl in H8.
  inv H8. clear H13. 
  inv H7.             
  assert (isBindingInsn (lookupBindingViaIDFromFdef f i0) = ret insn') as J.
    admit.
  assert (J':=J).
  apply H14 in J'. clear H14.
  inv J'.
  clear H8.
  unfold isPhiNode in H11.
  simpl in H11.
  assert (notT (false = true)) as J'. 
    intro J2. inversion J2.
  apply H14 in J'. clear H14.
  clear - J J' HwfDefs Hinscope H0.
  assert (In i0 defs) as J1.
    admit.
  admit.
Admitted.

Lemma state_cmd_typing : forall ifs s m f b c defs id1 lc,
  wf_insn ifs s m f b (insn_cmd c) ->
  Some defs = inscope_of_cmd f b c ->
  wf_defs f lc defs ->
  In id1 (getInsnOperands (insn_cmd c)) ->
  exists t, exists gv, lookupAL _ lc id1 = Some gv /\ wf_genericvalue gv t.
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

Lemma getValueViaLabelFromValuels__getInsnOperands : forall
  (lc : GVMap)
  (l1 : l)
  (i1 : id)
  (t0 : typ)
  (vid : id)
  (value_l_id_block_list : list_value_l_id_block)
  (J : getValueViaLabelFromValuels
        (make_list_value_l
           (map_list_value_l_id_block
              (fun (value_ : value) (l_ : l) (_ : id) (_ : block) =>
               (value_, l_)) value_l_id_block_list)) l1 = 
      ret value_id vid)
  (id_list : list_id)
  (H10 : getInsnOperands
          (insn_phinode
             (insn_phi i1 t0
                (make_list_value_l
                   (map_list_value_l_id_block
                      (fun (value_ : value) (l_ : l) (_ : id) (_ : block) =>
                       (value_, l_)) value_l_id_block_list)))) =
        unmake_list_id id_list),
  exists n, nth_list_id n id_list = Some vid.
Proof.
  intros.
  generalize dependent id_list.
  induction value_l_id_block_list; intros; simpl in *.
    inversion J.

    destruct (l0 == l1); subst.
      inv J; simpl in *.
      destruct id_list; inv H10.
        exists 0%nat. auto.

      destruct v.
        destruct id_list; inv H10.
          apply IHvalue_l_id_block_list with (id_list:=id_list) in J; eauto.
          destruct J as [n' J].
          destruct (i3 == vid); subst.
            exists 0%nat. simpl. auto.
            exists (S n'). simpl. auto.

          apply IHvalue_l_id_block_list with (id_list:=id_list) in J; eauto.
Qed.


Lemma wf_value_list__wf_value : forall
  (s : system)
  (f : fdef)
  (lc : GVMap)
  (l1 : l)
  (t0 : typ)
  (vid : id)
  (value_l_id_block_list : list_value_l_id_block)
  (H2 : wf_value_list
         (make_list_system_fdef_value_typ
            (map_list_value_l_id_block
               (fun (value_ : value) (_ : l) (_ : id) (_ : block) =>
                (s, f, value_, t0)) value_l_id_block_list)))
  (J : getValueViaLabelFromValuels
        (make_list_value_l
           (map_list_value_l_id_block
              (fun (value_ : value) (l_ : l) (_ : id) (_ : block) =>
               (value_, l_)) value_l_id_block_list)) l1 = 
      ret value_id vid),
  wf_value s f (value_id vid) t0.
Proof.
  intros.
  induction value_l_id_block_list; simpl in *.
    inversion J.
    
    inv H2.
    destruct (l0==l1); subst; eauto.
      inv J. auto.
Qed.        


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
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  ps2
  (HbInF : wf_block nil s (module_intro los nts ps) f 
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

          destruct a.
          assert (exists v, getValueViaLabelFromValuels l2 l1 = Some v) as J.
            admit. (*wf*)
          destruct J as [v J].
          rewrite J.
          destruct v as [vid | vc].
            inv H8.
            assert (exists gv1, lookupAL GenericValue lc vid = Some gv1) as J1.
              Focus.
              inv H6.              
              inv H23.
              eapply getValueViaLabelFromValuels__getInsnOperands in H10; eauto.
              destruct H10 as [n H10].
              eapply wf_operand_list__wf_operand in H12; eauto.
              assert (HwfV:=J).
              eapply wf_value_list__wf_value in HwfV; eauto.
              clear - H10 HeqR Hinscope H12 J HwfV H15.
              inv H12.  
              assert (isBindingInsn (lookupBindingViaIDFromFdef f vid) = 
                ret insn') as HBind.
                admit.
              assert (HwfSSA:=HBind).
              apply H6 in HwfSSA. clear H6.
              inv HwfSSA. clear H7.
              unfold isPhiNode in H6.
              simpl in H6.
              destruct H6 as [J1 [J2 J3]]; auto.
              assert (l'' = l1) as EQ.
                clear - H15 J J1 HBind.
                admit. (* incoming edges are identical. *)
              subst.
              assert (block'' = 
                block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l0)) as EQ.
                clear - J2. admit. (* block IDs are unique. *)
              subst.
              assert (getInsnID insn' = vid) as EQ.
                clear - HBind. admit.
              subst.
              clear - J3 Hinscope HeqR H2.
              admit. (* ?!?!?!? *)
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

            admit. (* constant *)
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
          returnUpdateLocals (los,nts) M' (insn_call i1 n t0 t1 v0 p) v lc lc' gl
            = Some lc'') as Hretup.
          unfold returnUpdateLocals. simpl.
          destruct n.
            exists lc'. auto.
            
            destruct v as [vid | vc].
              assert (HwfInstr:=HbInF).
              eapply wf_system__wf_insn in HwfInstr; eauto.
              assert (exists t, exists gv, lookupAL _ lc vid = Some gv /\ 
                wf_genericvalue gv t) as Hlkup.
                assert (In vid (getInsnOperands (insn_terminator 
                  (insn_return i0 t (value_id vid))))) as HinOps.
                  simpl. auto.
                eapply state_tmn_typing in HwfInstr; eauto.

              destruct Hlkup as [gt [gv [Hlkup Hwfgv]]].
              simpl.
              rewrite Hlkup. exists (updateAddAL GenericValue lc' i1 gv). auto.

              admit. (* what if a constant is stuck~? if int2ptr is not allowed,
                        we should prove this, because globals are not changed!
                      *)
          
            destruct Hretup as [lc'' Hretup].
            exists (mkState s (los, nts) ps ((mkEC f' b' cs' tmn' lc'' als')::
              ecs) gl fs M').
            exists trace_nil.
            eauto.  

    SCase "tmn=ret void". admit.
    SCase "tmn=br". admit.
    SCase "tmn=br_uncond". 
      right.
      assert (exists ps', exists cs', exists tmn',
        Some (block_intro l2 ps' cs' tmn') = lookupBlockViaLabelFromFdef f l2) 
          as HlkB.
        admit. (* wf *)
      destruct HlkB as [ps' [cs' [tmn' HlkB]]].
      assert (exists RVs, 
        getIncomingValuesForBlockFromPHINodes (los, nts) M ps'
          (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc =
        Some RVs) as J.
        eapply wf_system__blockInFdefB__wf_block in HbInF; eauto.
        eapply wf_system__lookup__wf_block in HlkB; eauto.
        clear - HeqR Hinscope HbInF HlkB.
        inv HlkB. clear H9 H10 H7.
        eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes; eauto.      
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
