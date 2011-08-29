Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import List.
Require Import Arith.
Require Import monad.
Require Import Metatheory.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import ListSet.

(**********************************)
(* Dom and Reaching analysis *)

Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Import LLVMsyntax.
Import LLVMinfra.

Fixpoint successors_blocks (bs: blocks) : ATree.t ls :=
match bs with
| nil => ATree.empty ls
| block_intro l0 _ _ tmn :: bs' => 
    ATree.set l0 (successors_terminator tmn) (successors_blocks bs')
end.

Definition successors (f: fdef) : ATree.t ls :=
let '(fdef_intro _ bs) := f in
successors_blocks bs.

Definition transfer (bound: set atom) (lbl: l) (before: Dominators.t bound) :=
  Dominators.add _ before lbl.

(** The static analysis itself is then an instantiation of Kildall's
  generic solver for forward dataflow inequations. [analyze f]
  returns a mapping from program points to mappings of pseudo-registers
  to approximations.  It can fail to reach a fixpoint in a reasonable
  number of iterations, in which case [None] is returned. *)

Module DomDS := Dataflow_Solver_Var_Top(AtomNodeSet).

Fixpoint bound_blocks (bs: blocks) : set atom :=
match bs with
| nil => empty_set _
| block_intro l0 _ _ tmn :: bs' => l0::(bound_blocks bs')
end.

Definition bound_fdef (f: fdef) : set atom :=
let '(fdef_intro _ bs) := f in
bound_blocks bs.

Lemma entry_dom : forall (bs:list block), 
  {oresult : option (l * Dominators.BoundedSet (bound_blocks bs)) &
     match oresult with
     | None => bs = nil
     | Some (le, Dominators.mkBoundedSet (l1::nil) _) => le = l1
     | _ => False
     end
  }.
Proof.
  intros.
  destruct bs; simpl in *.
    exists None. auto.

    destruct b.
    assert (incl [l0] (l0 :: bound_blocks bs)) as J.
      simpl_env.
      apply incl_appl; auto using incl_refl.
    exists (Some (l0, Dominators.mkBoundedSet _ [l0] J)).  
    simpl. auto.
Defined.

Definition dom_analyze (f: fdef) : AMap.t (Dominators.t (bound_fdef f)) :=
  let '(fdef_intro _ bs) := f in
  let bound := bound_blocks bs in
  let top := Dominators.top bound in
  match entry_dom bs with
  | (existT (Some (le, start)) _) =>
      match DomDS.fixpoint bound (successors_blocks bs) (transfer bound) 
        ((le, start) :: nil) with
      | None => (AMap.set le start (AMap.init top))
      | Some res => res
      end
  | (existT None _) => AMap.init top
  end.

(*
Program Definition dom_analyze (f: fdef): AMap.t (Dominators.t (bound_fdef f)) :=
  let bound := bound_fdef f in
  let top := Dominators.top bound in
  match getEntryBlock f with
  | Some (block_intro le _ _ _) =>
      match DomDS.fixpoint bound (successors f) (transfer bound) 
        ((le, Dominators.mkBoundedSet _ [le] _) :: nil) with
      | None => AMap.init top
      | Some res => res
      end
  | None => AMap.init top
  end.
Next Obligation.
  destruct f. 
  destruct b; simpl in *; inv Heq_anonymous. 
    simpl_env.
    apply incl_appl; auto using incl_refl.
Qed.
*)

Definition blockDominates (f: fdef) (b1 b2: block) : Prop :=
let '(block_intro l1 _ _ _) := b1 in
let '(block_intro l2 _ _ _) := b2 in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l2 dt in
set_In l1 els.

Definition blockStrictDominates (f: fdef) (b1 b2: block) : Prop :=
let '(block_intro l1 _ _ _) := b1 in
let '(block_intro l2 _ _ _) := b2 in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l2 dt in
l1 <> l2 /\ set_In l1 els.

Definition insnDominates (id1:id) (i2:insn) (b:block) : Prop :=
match b with 
| (block_intro l5 ps cs tmn) =>
  match i2 with
  | insn_terminator tmn2 =>
      ((exists cs1, exists c1, exists cs2, 
         cs = cs1++c1::cs2 /\ getCmdID c1 = Some id1) \/ 
       (exists ps1, exists p1, exists ps2, 
         ps = ps1++p1::ps2 /\ getPhiNodeID p1 = id1)
       ) /\ tmn2 = tmn
  | insn_cmd c2 =>
      (exists ps1, exists p1, exists ps2, 
         ps = ps1++p1::ps2 /\ getPhiNodeID p1 = id1) \/
      (exists cs1, exists c1, exists cs2, exists cs3,
         cs = cs1++c1::cs2 ++ c2 :: cs3 /\ getCmdID c1 = Some id1)
  | _ => False
  end
end.

Module ReachDS := Dataflow_Solver(LBoolean)(AtomNodeSet).

Definition reachable_aux (f: fdef) : option (AMap.t bool) :=
  match getEntryBlock f with
  | Some (block_intro le _ _ _) =>
     ReachDS.fixpoint (successors f) (fun pc r => r) ((le, true) :: nil)
  | None => None
  end.

Definition reachable (f: fdef) : AMap.t bool :=
  match reachable_aux f with  
  | None => AMap.init true
  | Some rs => rs
  end.

Definition isReachableFromEntry (f:fdef) (b1:block) : Prop :=
let '(block_intro l1 _ _ _) := b1 in
AMap.get l1 (reachable f).
 
(********************************************)
(** * Correctness of analysis *)

Axiom atomset_eq__proof_irr2 : forall (* proof irrelevence *)
  max
  (contents' : ListSet.set atom)
  (inbound' : incl contents' max)
  a
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = a),
  contents' = Dominators.bs_contents max a.

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
Proof. 
  intros.  
  apply atomset_eq__proof_irr2 in Heqdefs'; subst.
  apply atomset_eq__proof_irr2 in HeqR2; subst.
  auto.
Qed.

Lemma reachable_entrypoint:
  forall (f:fdef) l0 ps cs tmn, 
    getEntryBlock f = Some (block_intro l0 ps cs tmn) ->
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
    remember (getEntryBlock f) as R.
    destruct R; inv H.
    destruct b as [le ? ? ?].
    assert (LBoolean.ge reach!!l1 reach!!l0) as J.
      change (reach!!l0) with ((fun pc r => r) l0 (reach!!l0)).
      eapply ReachDS.fixpoint_solution; eauto.
        destruct f as [[?] bs]. simpl in *.
        clear - HuniqF HbInF Hin. destruct HuniqF.
        assert ((successors_terminator tmn) = (successors_blocks bs) !!! l0) 
          as EQ.
          eapply successors_terminator__successors_blocks; eauto.
        rewrite <- EQ; auto.            
    elim J; intro. congruence. auto.

  intros. apply AMap.gi.
Qed.

Ltac tinv H := try solve [inv H].
Import AtomSet.

Lemma dom_entrypoint : forall f l0 ps cs tmn
  (Hentry : getEntryBlock f = Some (block_intro l0 ps cs tmn)),
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
    destruct bs_contents; tinv Hp.
    destruct bs_contents; tinv Hp.
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

(***************************)
(* domination prop *)

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

Lemma getCmdsIDs__cmds_dominates_cmd : forall cs2' c',
  ~ In (getCmdLoc c') (getCmdsLocs cs2') ->
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

Inductive wf_phi_operands (f:fdef) (b:block) (id0:id) (t0:typ) : 
    list_value_l -> Prop :=
| wf_phi_operands_nil : wf_phi_operands f b id0 t0 Nil_list_value_l
| wf_phi_operands_cons_vid : forall vid1 l1 vls b1 vb, 
    vid1 <> id0 \/ (not (isReachableFromEntry f b)) ->
    lookupBlockViaIDFromFdef f vid1 = Some vb ->
    lookupBlockViaLabelFromFdef f l1 = Some b1 ->
    blockDominates f vb b1 \/ (not (isReachableFromEntry f b)) ->
    wf_phi_operands f b id0 t0 vls ->
    wf_phi_operands f b id0 t0 (Cons_list_value_l (value_id vid1) l1 vls)
| wf_phi_operands_cons_vc : forall c1 l1 vls, 
    wf_phi_operands f b id0 t0 vls ->
    wf_phi_operands f b id0 t0 (Cons_list_value_l (value_const c1) l1 vls).

Definition check_list_value_l (f:fdef) (b:block) (vls:list_value_l) := 
  let ud := genBlockUseDef_fdef f in
  let vls1 := unmake_list_value_l vls in
  let '(vs1,ls1) := List.split vls1 in 
  let ls2 := predOfBlock b ud in
  (length ls2 > 0)%nat /\
  AtomSet.set_eq _ ls1 ls2 /\
  NoDup ls1.

Definition wf_phinode (f:fdef) (b:block) (p:phinode) :=
let '(insn_phi id0 t0 vls0) := p in
wf_phi_operands f b id0 t0 vls0 /\ check_list_value_l f b vls0. 

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
