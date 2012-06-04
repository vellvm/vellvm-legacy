Require Import Ensembles.
Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Require Import dom_set.
Require Import analysis.
Require Import typings.
Require Import typings_props.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import Lattice.
Require Import Floats.
Require Import AST.
Require Import Maps.
Require Import opsem.
Require Import opsem_props.
Require Import opsem_wf.

(************** Opsem Dominator ******************************************* ***)

Module OpsemDom. Section OpsemDom.

Context `{GVsSig : GenericValues}.

Export Opsem.
Export OpsemProps.
Import AtomSet.

Notation GVs := GVsSig.(GVsT).
Notation "gv @ gvs" :=
  (GVsSig.(instantiate_gvs) gv gvs) (at level 43, right associativity).
Notation "$ gv # t $" := (GVsSig.(gv2gvs) gv t) (at level 41).
Notation "vidxs @@ vidxss" := (in_list_gvs vidxs vidxss)
  (at level 43, right associativity).

(* Select/GEP are impure because of non-deterministics *)
Definition pure_cmd (c:cmd) : Prop :=
match c with
| insn_bop _ _ _ _ _
| insn_fbop _ _ _ _ _
| insn_extractvalue _ _ _ _ _
| insn_insertvalue _ _ _ _ _ _
| insn_trunc _ _ _ _ _
| insn_ext _ _ _ _ _
| insn_cast _ _ _ _ _
| insn_icmp _ _ _ _ _
| insn_fcmp _ _ _ _ _ => True
| _ => False
end.

Definition eval_rhs TD gl (lc:GVsMap) (c:cmd) (gv:GVs) : Prop :=
match c with
| insn_bop _ bop0 sz v1 v2 => BOP TD lc gl bop0 sz v1 v2 = Some gv
| insn_fbop _ fbop fp v1 v2 => FBOP TD lc gl fbop fp v1 v2  = Some gv
| insn_extractvalue id t v idxs _ =>
    exists gv0, getOperandValue TD v lc gl = Some gv0 /\
                extractGenericValue TD t gv0 idxs = Some gv
| insn_insertvalue _ t v t' v' idxs =>
    exists gv1, exists gv2,
      getOperandValue TD v lc gl = Some gv1 /\
      getOperandValue TD v' lc gl = Some gv2 /\
      insertGenericValue TD t gv1 idxs t' gv2 = Some gv
| insn_trunc _ truncop t1 v1 t2 => TRUNC TD lc gl truncop t1 v1 t2 = Some gv
| insn_ext _ extop t1 v1 t2 => EXT TD lc gl extop t1 v1 t2 = Some gv
| insn_cast _ castop t1 v1 t2 => CAST TD lc gl castop t1 v1 t2 = Some gv
| insn_icmp _ cond0 t v1 v2 => ICMP TD lc gl cond0 t v1 v2 = Some gv
| insn_fcmp _ fcond fp v1 v2 => FCMP TD lc gl fcond fp v1 v2 = Some gv
| _ => ~ pure_cmd c
end.

Definition wf_GVs TD gl (f:fdef) (lc:GVsMap) (id1:id) (gvs1:GVs) : Prop :=
forall c1,
  lookupInsnViaIDFromFdef f id1 = Some (insn_cmd c1) ->
  (eval_rhs TD gl lc c1 gvs1 /\
   forall b1, cmdInFdefBlockB c1 f b1 = true -> isReachableFromEntry f b1).

Definition wf_defs TD gl (f:fdef) (lc:GVsMap)(ids0:list atom) : Prop :=
forall id0 gvs0,
  In id0 ids0 ->
  lookupAL _ lc id0 = Some gvs0 ->
  wf_GVs TD gl f lc id0 gvs0.

Lemma wf_defs_eq : forall ids2 ids1 TD gl F' lc',
  set_eq ids1 ids2 ->
  wf_defs TD gl F' lc' ids1 ->
  wf_defs TD gl F' lc' ids2.
Proof.
  intros.
  intros id2 gvs1 Hin Hlk.
  destruct H as [J1 J2]. eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec1 : forall TD S M f  
    gl lc id1 l3 cs tmn ps lc' gvs b,
  Some lc' = getIncomingValuesForBlockFromPHINodes TD ps b gl lc ->
  In id1 (getPhiNodesIDs ps) ->
  Some (block_intro l3 ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_fdef S M f -> uniqFdef f ->
  lookupAL _ lc' id1 = Some gvs ->
  wf_GVs TD gl f lc id1 gvs.
Proof.
  intros. intros c1 Hin. eapply phinode_isnt_cmd in H1; eauto. inv H1.
Qed.

Require Import Maps.

Lemma eval_rhs_updateValuesForNewBlock : forall TD gl c lc gv rs,
  (forall i, i `in` dom rs -> ~ In i (getCmdOperands c)) ->
  (eval_rhs TD gl (updateValuesForNewBlock rs lc) c gv <->
   eval_rhs TD gl lc c gv).
Proof.
  induction rs; simpl; intros.
    split; auto.

Ltac eru_tac1 :=
let foo a i1 i2 rs H :=
  destruct (id_dec a i1); subst; try solve [
    assert (i1 `in` add i1 (dom rs)) as IN; auto;
    apply H in IN; contradict IN; auto |

    rewrite <- lookupAL_updateAddAL_neq; auto;
    destruct (id_dec a i2); subst; try solve [
      assert (i2 `in` add i2 (dom rs)) as IN; auto;
      apply H in IN; contradict IN; auto |
  
      rewrite <- lookupAL_updateAddAL_neq; auto
    ]
  ] in
match goal with
| rs : list (atom * GVs),
  H : forall i : atom, i `in` add ?a (dom ?rs) -> ~ (?i1 = i \/ ?i2 = i \/ False)
  |- _ =>
  match goal with
  | |- _ <-> match lookupAL _ _ ?i1 with
             | ret _ =>
               match lookupAL _ _ ?i2 with
               | ret _ => _
               | merror => _
               end
             | merror => _
             end = _ => foo a i1 i2 rs H
  | |- _ <-> (exists _ : _, exists _ : _,
             lookupAL _ _ ?i1 = ret _ /\ lookupAL _ _ ?i2 = ret _ /\ _) =>
      foo a i1 i2 rs H
  end
end.

Ltac eru_tac2 :=
let foo a i1 rs H :=
  destruct (id_dec a i1); subst; try solve [
    assert (i1 `in` add i1 (dom rs)) as IN; auto;
    apply H in IN; contradict IN; auto |
    rewrite <- lookupAL_updateAddAL_neq; auto
  ] in
match goal with
| rs : list (atom * GVs),
  H : forall i : atom, i `in` add ?a (dom ?rs) -> ~ (?i1 = i \/ False)
  |- _ =>
  match goal with
  | |- _ <-> match lookupAL _ _ ?i1 with
             | ret _ =>
               match const2GV _ _ _ with
               | ret _ => _
               | merror => _
               end
             | merror => _
             end = _ => foo a i1 rs H
  | |- _ <-> (exists _ : _, exists _ : _,
             lookupAL _ _ ?i1 = ret _ /\ const2GV _ _ _ = ret _ /\ _) =>
      foo a i1 rs H
  end
end.

Ltac eru_tac3 :=
let foo a i1 rs H :=
  destruct (id_dec a i1); subst; try solve [
    assert (i1 `in` add i1 (dom rs)) as IN; auto;
    apply H in IN; contradict IN; auto |
    rewrite <- lookupAL_updateAddAL_neq; auto
  ] in
match goal with
| rs : list (atom * GVs),
  H : forall i : atom, i `in` add ?a (dom ?rs) -> ~ (?i1 = i \/ False)
  |- _ =>
  match goal with
  | |- _ <-> match const2GV _ _ _ with
             | ret _ =>
               match lookupAL _ _ ?i1 with
               | ret _ => _
               | merror => _
               end
             | merror => _
             end = _ => foo a i1 rs H
  | |- _ <-> (exists _ : _, exists _ : _,
             const2GV _ _ _ = ret _ /\ lookupAL _ _ ?i1 = ret _ /\ _) =>
      foo a i1 rs H
  end
end.

Ltac eru_tac4 :=
let foo a i1 rs H :=
  destruct (id_dec a i1); subst; try solve [
    assert (i1 `in` add i1 (dom rs)) as IN; auto;
    apply H in IN; contradict IN; auto |
    rewrite <- lookupAL_updateAddAL_neq; auto
  ] in
match goal with
| rs : list (atom * GVs),
  H : forall i : atom, i `in` add ?a (dom ?rs) -> ~ (?i1 = i \/ False)
  |- _ =>
  match goal with
  | |- _ <-> match lookupAL _ _ ?i1 with
             | ret _ => _
             | merror => _
             end = _ => foo a i1 rs H
  | |- _ <-> (exists _ : _, lookupAL _ _ ?i1 = ret _ /\ _) => foo a i1 rs H
  end
end.

    destruct a as [a g].
    destruct c as [i0 b s0 v v0|i0 f0 f1 v v0|i0 t v l2|i0 t v t0 v0 l2|
                   i0 t v ?|i0 t v|i0 t v ?|i0 t v ?|i0 t v v0 ?|i0 i1 t v l2|
                   i0 t t0 v t1|i0 e t v t0|i0 c t v t0|i0 c t v v0|
                   i0 f0 f1 v v0|i0 v t v0 v1|i0 n c t v p]; simpl;
      unfold BOP, FBOP, TRUNC, EXT, ICMP, FCMP, CAST; try solve [ 
        auto |
        destruct v as [i1|c1]; destruct v0 as [i2|c2]; simpl in *;
          try solve [auto | eru_tac1 | eru_tac2 | eru_tac3] |
        destruct v as [i1|c1]; simpl in *; try solve [auto | eru_tac4]
      ].
Qed.

Lemma wf_defs_br_aux : forall TD gl S M lc l' ps' cs' lc' F tmn' b
  (Hreach : isReachableFromEntry F b)
  (Hreach': isReachableFromEntry F (block_intro l' ps' cs' tmn'))
  (Hlkup : Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hswitch : switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') b gl lc =
    ret lc')
  (t : list atom)
  (Hwfdfs : wf_defs TD gl F lc t)
  (ids0' : list atom)
  (HwfF : wf_fdef S M F) (HuniqF: uniqFdef F)
  (contents' : ListSet.set atom)
  (Heqdefs' : contents' = AlgDom.sdom F l')
  (Hinscope : (fold_left (inscope_of_block F l') contents'
    (ret (getPhiNodesIDs ps' ++ getArgsIDsOfFdef F)) = ret ids0'))
  (Hinc : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) t),
  wf_defs TD gl F lc' ids0'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  intros id1 gvs Hid1 Hlk.
  remember (getIncomingValuesForBlockFromPHINodes TD ps' b gl lc) as R1.
  destruct R1 as [rs|]; inv Hswitch.
  destruct (In_dec eq_atom_dec id1 (getPhiNodesIDs ps')) as [Hin | Hnotin].
  Case "id1 in ps'".
    apply updateValuesForNewBlock_spec6 in Hlk; auto.
      eapply getIncomingValuesForBlockFromPHINodes_spec1 with (gvs:=gvs) in HeqR1;
        eauto.
      intros c1 Hlkc1. eapply phinode_isnt_cmd in Hlkup; eauto. inv Hlkup.

      eapply getIncomingValuesForBlockFromPHINodes_spec6 in HeqR1; eauto.

  Case "id1 notin ps'".
    assert (Hnotin' := Hnotin).
    apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) in Hnotin;
      auto.
    apply Hinc in Hnotin. assert (HeqR1':=HeqR1).
    eapply getIncomingValuesForBlockFromPHINodes_spec8 in HeqR1; eauto.
    eapply updateValuesForNewBlock_spec7 in Hlk; eauto.
    apply Hwfdfs in Hlk; auto.
      intros c1 Hlkc1.
      assert (~ In id1 (getArgsIDsOfFdef F)) as Hnotina.
        apply getInsnLoc__notin__getArgsIDs' in Hlkc1; auto.
      destruct (@Hlk c1) as [Hlkc1' Hreach'']; auto.
      split; auto.
      apply eval_rhs_updateValuesForNewBlock; auto.
         intros i0 Hin.
         destruct (in_dec id_dec i0 (getCmdOperands c1)); auto.
           elimtype False.
           eapply operands_of_cmd__cannot_be__phis_that_cmd_doms; eauto.
             intro J. apply in_app_or in J. destruct J; auto.
             eapply getIncomingValuesForBlockFromPHINodes_spec7 in HeqR1'; eauto.
Qed.

Lemma inscope_of_tmn_br_aux : forall S M F l3 ps cs tmn ids0 l' ps' cs' tmn'
  l0 lc lc' gl TD (Hreach : isReachableFromEntry F (block_intro l3 ps cs tmn)),
wf_fdef S M F -> uniqFdef F ->
blockInFdefB (block_intro l3 ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs tmn) tmn ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs tmn) gl lc = Some lc' ->
wf_defs TD gl F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs TD gl F lc' ids0'.
Proof.
  intros S M F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 lc lc' gl TD Hreach
    HwfF HuniqF HBinF Hsucc Hinscope Hlkup Hswitch Hwfdfs.
  symmetry in Hlkup.
  assert (J:=Hlkup).
  apply lookupBlockViaLabelFromFdef_inv in J; auto.
  destruct J as [Heq J]; subst.
  unfold inscope_of_tmn in Hinscope.
  unfold inscope_of_tmn. unfold inscope_of_cmd, inscope_of_id.
  destruct F as [fh bs].

  assert (incl (AlgDom.sdom (fdef_intro fh bs) l')
    (l3::(AlgDom.sdom (fdef_intro fh bs) l3))) as Hsub.
    clear - HBinF Hsucc HuniqF HwfF.
    eapply dom_successors; eauto.

  assert (isReachableFromEntry (fdef_intro fh bs) (block_intro l' ps' nil tmn'))
    as Hreach'.
    eapply isReachableFromEntry_successors in Hlkup; eauto.

  assert (J1:=AlgDom.sdom_in_bound fh bs l').
  destruct fh as [f t i0 a v].
  apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++
      getCmdsIDs nil ++ getArgsIDs a)(bs:=bs)(l0:=l')
      (fh:=fheader_intro f t i0 a v) in J1; auto.
  destruct J1 as [r J1].
  exists r. 

  assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
    as Jinc.
    clear - Hinscope J1 Hsub HBinF HuniqF.
    eapply inscope_of_tmn__inscope_of_cmd_at_beginning in J1; eauto. 

  destruct cs'.
  Case "cs'=nil".
    simpl.
    split; auto.
    split; auto.
      subst. simpl in J1. simpl_env in J1.
      eapply wf_defs_br_aux in Hswitch; eauto.

  Case "cs'<>nil".
    assert (~ In (getCmdLoc c) (getPhiNodesIDs ps')) as Hnotin.
      apply uniqFdef__uniqBlockLocs in J; auto.
      simpl in J. 
      eapply NoDup_disjoint in J; simpl; eauto.
    rewrite init_scope_spec1; auto.
    unfold cmds_dominates_cmd. simpl.
    destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_ | n];
      try solve [contradict n; auto].
    split; auto.
    split; auto.
      subst. eapply wf_defs_br_aux in Hswitch; eauto.
Qed.

Lemma inscope_of_tmn_br_uncond : forall S M F l3 ps cs ids0 l' ps' cs' tmn' 
  l0 lc lc' bid TD gl,
isReachableFromEntry F (block_intro l3 ps cs (insn_br_uncond bid l0)) ->
wf_fdef S M F -> uniqFdef F ->
blockInFdefB (block_intro l3 ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0))
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs (insn_br_uncond bid l0)) gl lc = Some lc' ->
wf_defs TD gl F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs TD gl F lc' ids0'.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

Lemma inscope_of_tmn_br : forall S M F l0 ps cs bid l1 l2 ids0 l' ps' cs' 
  tmn' Cond c lc lc' gl TD,
isReachableFromEntry F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) ->
wf_fdef S M F -> uniqFdef F ->
blockInFdefB (block_intro l0 ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2))
  (insn_br bid Cond l1 l2) ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
  (block_intro l0 ps cs (insn_br bid Cond l1 l2)) gl lc = Some lc' ->
wf_defs TD gl F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs TD gl F lc' ids0'.
Proof.
  intros.
  remember (isGVZero TD c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

Lemma state_tmn_typing : forall TD S M f l1 ps1 cs1 tmn1 defs id1 lc gv gl,
  isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1) ->
  wf_insn S M f (block_intro l1 ps1 cs1 tmn1) (insn_terminator tmn1) ->
  Some defs = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1 ->
  wf_defs TD gl f lc defs ->
  wf_fdef S M f -> uniqFdef f ->
  In id1 (getInsnOperands (insn_terminator tmn1)) ->
  lookupAL _ lc id1 = Some gv ->
  wf_GVs TD gl f lc id1 gv /\ In id1 defs.
Proof.
  intros TD S M f l1 ps1 cs1 tmn1 defs id1 lc gv gl Hreach HwfInstr 
    Hinscope HwfDefs HwfF HuniqF HinOps Hlkup.
  apply wf_insn__wf_insn_base in HwfInstr;
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr. find_wf_operand_list. subst. find_wf_operand_by_id.

  assert (In id1 defs) as Hin.
    eapply terminator_operands__in_scope; eauto.
  auto.
Qed.

Lemma state_cmd_typing : forall S M f b c defs id1 lc gv TD gl,
  NoDup (getBlockLocs b) ->
  isReachableFromEntry f b ->
  wf_insn S M f b (insn_cmd c) ->
  Some defs = inscope_of_cmd f b c ->
  wf_defs TD gl f lc defs ->
  wf_fdef S M f -> uniqFdef f ->
  In id1 (getInsnOperands (insn_cmd c)) ->
  lookupAL _ lc id1 = Some gv ->
  wf_GVs TD gl f lc id1 gv /\ In id1 defs.
Proof.
  intros S M f b c defs id1 lc gv TD gl Hnodup Hreach HwfInstr Hinscope 
    HwfDefs HwfF HuniqF HinOps Hlkup.
  apply wf_insn__wf_insn_base in HwfInstr;
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr. find_wf_operand_list. subst. find_wf_operand_by_id.

  assert (In id1 defs) as Hin.
    eapply cmd_operands__in_scope; eauto.
  auto.
Qed.

(*********************************************)
(** * Preservation *)

Definition wf_ExecutionContext TD gl (ps:list product) (ec:ExecutionContext)
  : Prop :=
let '(mkEC f b cs tmn lc als) := ec in
isReachableFromEntry f b /\
blockInFdefB b f = true /\
InProductsB (product_fdef f) ps = true /\
match cs with
| nil =>
    match inscope_of_tmn f b tmn with
    | Some ids => wf_defs TD gl f lc ids
    | None => False
    end
| c::_ =>
    match inscope_of_cmd f b c with
    | Some ids => wf_defs TD gl f lc ids
    | None => False
    end
end /\
exists l1, exists ps, exists cs',
b = block_intro l1 ps (cs'++cs) tmn.

Definition wf_call (ec:@ExecutionContext GVsSig) (ecs:@ECStack GVsSig) : Prop :=
let '(mkEC f _ _ _ _ _) := ec in
forall b, blockInFdefB b f ->
let '(block_intro _ _ _ tmn) := b in
match tmn with
| insn_return _ _ _ | insn_return_void _ =>
    match ecs with
    | nil => True
    | mkEC f' b' (insn_call _ _ _ _ _ _ _ ::_) tmn' lc' als'::ecs'
        => True
    | _ => False
    end
| _ => True
end.

Fixpoint wf_ECStack TD gl (ps:list product) (ecs:ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' =>
    wf_ExecutionContext TD gl ps ec /\ wf_ECStack TD gl ps ecs' /\
    wf_call ec ecs'
end.

Definition wf_State (cfg:Config) (S:State) : Prop :=
let '(mkCfg s (los, nts) ps gl _ ) := cfg in
let '(mkState ecs _) := S in
ecs <> nil /\
wf_system s /\
moduleInSystemB (module_intro los nts ps) s = true /\
wf_ECStack (los,nts) gl ps ecs.

Lemma wf_State__inv : forall S los nts Ps F B c cs tmn lc als EC gl fs Mem0,
  wf_State (mkCfg S (los,nts) Ps gl fs)
    (mkState ((mkEC F B (c::cs) tmn lc als)::EC) Mem0) ->
  wf_insn S (module_intro los nts Ps) F B (insn_cmd c).
Proof.
  intros.
  destruct H as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  eapply wf_system__wf_cmd; eauto using in_middle.
Qed.

Lemma eval_rhs_updateAddAL : forall TD gl id1 gvs1 lc gv c,
  ~ In id1 (getCmdOperands c) ->
  (eval_rhs TD gl (@updateAddAL GVs lc id1 gvs1) c gv <->
   eval_rhs TD gl lc c gv).
Proof.
  destruct c as [i0 b s0 v v0|i0 f0 f1 v v0|i0 t v l2|i0 t v t0 v0 l2|
                 i0 t v ?|i0 t v|i0 t v ?|i0 t v ?|i0 t v v0 ?|i0 i1 t v l2|
                 i0 t t0 v t1|i0 e t v t0|i0 c t v t0|i0 c t v v0|
                 i0 f0 f1 v v0|i0 v t v0 v1|i0 n c t v p]; 
    simpl; intros; try solve [split; auto].
    unfold BOP.
    destruct v as [i1|c1]; destruct v0 as [i2|c2]; simpl in *; try solve [split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct (id_dec id1 i2); subst.
          contradict H; auto.
          rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].
      destruct (id_dec id1 i2); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].

    unfold FBOP.
    destruct v as [i1|c1]; destruct v0 as [i2|c2]; simpl in *; try solve [split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct (id_dec id1 i2); subst.
          contradict H; auto.
          rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].
      destruct (id_dec id1 i2); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].

    destruct v as [i1|c1]; simpl in *; try solve [split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        split; auto.

    destruct v as [i1|c1]; destruct v0 as [i2|c2]; simpl in *; try solve [split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct (id_dec id1 i2); subst.
          contradict H; auto.
          rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].
      destruct (id_dec id1 i2); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].

    unfold TRUNC.
    destruct v as [i1|c1]; simpl in *; try solve [split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        split; auto.

    unfold EXT.
    destruct v as [i1|c1]; simpl in *; try solve [split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        split; auto.

    unfold CAST.
    destruct v as [i1|c1]; simpl in *; try solve [split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        split; auto.

    unfold ICMP.
    destruct v as [i1|c1]; destruct v0 as [i2|c2]; simpl in *; try solve [split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct (id_dec id1 i2); subst.
          contradict H; auto.
          rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].
      destruct (id_dec id1 i2); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].

    unfold FCMP.
    destruct v as [i1|c1]; destruct v0 as [i2|c2]; simpl in *; try solve [split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct (id_dec id1 i2); subst.
          contradict H; auto.
          rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].
      destruct (id_dec id1 i2); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; try solve [auto | split; auto].
Qed.

Lemma wf_defs_updateAddAL : forall S M g1 lc' ids1 ids2 F1 B1 l3 ps1 
  cs tmn1 c TD gl (HinCs: In c cs)
  (Hreach: isReachableFromEntry F1 (block_intro l3 ps1 cs tmn1))
  (HBinF1: blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true)
  (HBinF2: blockInFdefB B1 F1 = true)
  (HwfF1 : wf_fdef S M F1) (HuniqF:uniqFdef F1) 
  (HcInB : cmdInBlockB c B1 = true)
  (Hinscope : ret ids1 = inscope_of_id F1 B1 (getCmdLoc c)),
  wf_defs TD gl F1 lc' ids1 ->
  set_eq (getCmdLoc c::ids1) ids2 ->
  wf_GVs TD gl F1 lc' (getCmdLoc c) g1 ->
  wf_defs TD gl F1 (updateAddAL _ lc' (getCmdLoc c) g1) ids2.
Proof.
  intros S M g1 lc' ids1 ids2 F1 B1 l3 ps1 cs tmn1 c TD gl HinCs Hreach 
    HBinF1 HBinF2 HwfF1 HuniqF HcInB HInscope HwfDefs Heq Hwfgvs.
  intros id1 gvs1 Hin Hlk.
  destruct Heq as [Hinc1 Hinc2].
  apply Hinc2 in Hin.
  simpl in Hin.
  intros c1 Hlkc1.
  assert (id1 = getCmdLoc c1) as EQ.
    apply lookupInsnViaIDFromFdef__eqid in Hlkc1. simpl in Hlkc1. auto.
  subst.
  assert (J:=Hlkc1).
  eapply wf_fdef__wf_insn_base in J; eauto.
  destruct J as [b1 HwfI].
  inv HwfI.
  destruct (eq_dec (getCmdLoc c) (getCmdLoc c1)).
  Case "1".
    rewrite e in *.
    rewrite lookupAL_updateAddAL_eq in Hlk; auto.
    find_wf_operand_list. subst.
    inv Hlk.
    destruct (@Hwfgvs c1) as [Heval Hreach']; auto.
    split; auto.
    apply eval_rhs_updateAddAL; auto.
      eapply cmd_doesnt_use_self; eauto.

  Case "2".
    destruct Hin as [Eq | Hin]; try solve [contradict n; auto].
    rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
    find_wf_operand_list. subst.
    assert (Hlk':=Hlk).
    apply HwfDefs in Hlk; auto.
    destruct (@Hlk c1) as [Heval Hreach']; auto.
    split; auto.
    apply eval_rhs_updateAddAL; auto.
      eapply cmd_doesnt_use_nondom_operands; eauto.
Qed.

Lemma preservation_pure_cmd_updated_case : forall
  (F : fdef)
  (B : block)
  (lc : GVsMap)
  (gv3 : GVs)
  (cs : list cmd)
  (tmn : terminator)
  id0 c0 los nts gl Mem0 als EC fs Ps S
  (Hid : Some id0 = getCmdID c0) (Hpure : pure_cmd c0)
  (Hwfgv : wf_GVs (los, nts) gl F lc id0 gv3)
  (HwfS1 : wf_State {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            Globals := gl;
            FunTable := fs |}
            {|
            ECS := {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := c0 :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Allocas := als |} :: EC;
            Mem := Mem0 |}),
   wf_State {|
     CurSystem := S;
     CurTargetData := (los, nts);
     CurProducts := Ps;
     Globals := gl;
     FunTable := fs |}
     {|
     ECS := {|
            CurFunction := F;
            CurBB := B;
            CurCmds := cs;
            Terminator := tmn;
            Locals := updateAddAL GVs lc id0 gv3;
            Allocas := als |} :: EC;
     Mem := Mem0 |}.
Proof.
  intros.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0)
    as R1.
  assert (HeqR1':=HeqR1).
  unfold inscope_of_cmd, inscope_of_id in HeqR1'.
  assert (uniqFdef F) as HuniqF.
    eapply wf_system__uniqFdef; eauto.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto | congruence]).
      assert (Hid':=Hid).
      symmetry in Hid.
      apply getCmdLoc_getCmdID in Hid.
      subst.
      assert (cmdInBlockB c0 (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) = true)
        as Hin.
        simpl. apply In_InCmdsB. apply in_middle.
      assert (NoDup (getBlockLocs (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn))) 
        as Hnotin.
        eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.
      destruct cs; simpl_env in *.
      Case "1.1.1".
        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite <- Hid' in J2.
        assert (HwfF:=HFinPs1). eapply wf_system__wf_fdef in HwfF; eauto.
        eapply wf_defs_updateAddAL; eauto.

      Case "1.1.2".
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite <- Hid' in J2.
        assert (HwfF:=HFinPs1). eapply wf_system__wf_fdef in HwfF; eauto.
        eapply wf_defs_updateAddAL; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
Qed.

Lemma uniqFdef__lookupInsnViaIDFromBlocks : forall bs1 id1 c1 c2,
  lookupInsnViaIDFromBlocks bs1 id1 = ret insn_cmd c1 ->
  lookupInsnViaIDFromBlocks bs1 id1 = ret insn_cmd c2 ->
  c1 = c2.
Proof. congruence. Qed.

Lemma BOP__wf_gvs : forall
  (F1 : fdef) (v : value) (v0 : value) lc
  (id1 : id) (bop0 : bop) gvs3 TD sz0 gl
  (H11 : BOP TD lc gl bop0 sz0 v v0 = ret gvs3)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1
  (Hreach: isReachableFromEntry F1
    (block_intro l3 ps1 (cs1' ++ insn_bop id1 bop0 sz0 v v0 :: cs1) tmn1))
  (Hin : blockInFdefB
           (block_intro l3 ps1 (cs1' ++ insn_bop id1 bop0 sz0 v v0 :: cs1) tmn1)
           F1 = true),
  wf_GVs TD gl F1 lc id1 gvs3.
Proof.
  intros.
  destruct F1 as [fh1 bs1].
  assert (lookupInsnViaIDFromBlocks bs1 id1 =
    Some (insn_cmd (insn_bop id1 bop0 sz0 v v0))) as Hlk1.
    apply uniqF__uniqBlocks in Huniq. inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  intros c1 Hlkc1.
  assert (c1 = insn_bop id1 bop0 sz0 v v0) as EQ.
    eapply uniqFdef__lookupInsnViaIDFromBlocks in Hlk1; eauto.
  subst.
  split; auto.
    intros.
    assert (block_intro l3 ps1 (cs1' ++ insn_bop id1 bop0 sz0 v v0 :: cs1) tmn1
      = b1) as EQ.
      eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
    subst. auto.
Qed.

Lemma FBOP__wf_gvs : forall
  (F1 : fdef) (v : value) (v0 : value) lc
  (id1 : id) (fbop0 : fbop) gvs3 TD fp0 gl
  (H11 : FBOP TD lc gl fbop0 fp0 v v0 = ret gvs3)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1
  (Hreach: isReachableFromEntry F1
    (block_intro l3 ps1 (cs1' ++ insn_fbop id1 fbop0 fp0 v v0 :: cs1) tmn1))
  (Hin : blockInFdefB
           (block_intro l3 ps1 (cs1' ++ insn_fbop id1 fbop0 fp0 v v0 :: cs1) tmn1)
           F1 = true),
  wf_GVs TD gl F1 lc id1 gvs3.
Proof.
  intros.
  destruct F1 as [fh1 bs1].
  assert (lookupInsnViaIDFromBlocks bs1 id1 =
    Some (insn_cmd (insn_fbop id1 fbop0 fp0 v v0))) as Hlk1.
    apply uniqF__uniqBlocks in Huniq. inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  intros c1 Hlkc1.
  assert (c1 = insn_fbop id1 fbop0 fp0 v v0) as EQ.
    eapply uniqFdef__lookupInsnViaIDFromBlocks in Hlk1; eauto.
  subst.
  split; auto.
    intros.
    assert (block_intro l3 ps1 (cs1' ++ insn_fbop id1 fbop0 fp0 v v0 :: cs1) tmn1
      = b1) as EQ.
      eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
    subst. auto.
Qed.

Lemma extractvalue__wf_gvs : forall
  (F1 : fdef) (v : value) lc
  id1 t idxs gv TD gl gv0
  (J1 : getOperandValue TD v lc gl = Some gv0)
  (J2 : extractGenericValue TD t gv0 idxs = Some gv)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1 t'
  (Hreach: isReachableFromEntry F1
    (block_intro l3 ps1 (cs1' ++ insn_extractvalue id1 t v idxs t' :: cs1) tmn1))
  (Hin : blockInFdefB
          (block_intro l3 ps1 
            (cs1' ++ insn_extractvalue id1 t v idxs t' :: cs1) tmn1)
          F1 = true),
  wf_GVs TD gl F1 lc id1 gv.
Proof.
  intros.
  destruct F1 as [fh1 bs1].
  assert (lookupInsnViaIDFromBlocks bs1 id1 =
    Some (insn_cmd (insn_extractvalue id1 t v idxs t'))) as Hlk1.
    apply uniqF__uniqBlocks in Huniq. inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  intros c1 Hlkc1.
  assert (c1 = insn_extractvalue id1 t v idxs t') as EQ.
    eapply uniqFdef__lookupInsnViaIDFromBlocks in Hlk1; eauto.
  subst.
  split.
    simpl. exists gv0. split; auto.

    intros.
    assert (block_intro l3 ps1 (cs1' ++ insn_extractvalue id1 t v idxs t' :: cs1)
      tmn1 = b1) as EQ.
      eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
    subst. auto.
Qed.

Lemma insertvalue__wf_gvs : forall
  (F1 : fdef) (v v' : value) lc
  id1 t t' idxs gv1 gv2 TD gl gv0
  (J1 : getOperandValue TD v lc gl = Some gv1)
  (J2 : getOperandValue TD v' lc gl = Some gv2)
  (J3 : insertGenericValue TD t gv1 idxs t' gv2 = Some gv0)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1
  (Hreach: isReachableFromEntry F1
    (block_intro l3 ps1 (cs1' ++ insn_insertvalue id1 t v t' v' idxs :: cs1)
      tmn1))
  (Hin : blockInFdefB
          (block_intro l3 ps1
            (cs1' ++ insn_insertvalue id1 t v t' v' idxs :: cs1) tmn1)
          F1 = true),
  wf_GVs TD gl F1 lc id1 gv0.
Proof.
  intros.
  destruct F1 as [fh1 bs1].
  assert (lookupInsnViaIDFromBlocks bs1 id1 =
    Some (insn_cmd (insn_insertvalue id1 t v t' v' idxs))) as Hlk1.
    apply uniqF__uniqBlocks in Huniq. inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  intros c1 Hlkc1.
  assert (c1 = insn_insertvalue id1 t v t' v' idxs) as EQ.
    eapply uniqFdef__lookupInsnViaIDFromBlocks in Hlk1; eauto.
  subst.
  split.
    simpl. exists gv1. exists gv2. split; auto.

    intros.
    assert (block_intro l3 ps1
      (cs1' ++ insn_insertvalue id1 t v t' v' idxs :: cs1) tmn1 = b1) as EQ.
      eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
    subst. auto.
Qed.

Lemma TRUNC__wf_gvs : forall
  (F1 : fdef) truncop0 t1 v1 t2 lc
  (id1 : id) gvs TD gl
  (H11 : TRUNC TD lc gl truncop0 t1 v1 t2 = Some gvs)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1
  (Hreach: isReachableFromEntry F1
    (block_intro l3 ps1 (cs1' ++ insn_trunc id1 truncop0 t1 v1 t2 :: cs1) tmn1))
  (Hin : blockInFdefB
           (block_intro l3 ps1 (cs1' ++ insn_trunc id1 truncop0 t1 v1 t2 :: cs1)
             tmn1) F1 = true),
  wf_GVs TD gl F1 lc id1 gvs.
Proof.
  intros.
  destruct F1 as [fh1 bs1].
  assert (lookupInsnViaIDFromBlocks bs1 id1 =
    Some (insn_cmd (insn_trunc id1 truncop0 t1 v1 t2))) as Hlk1.
    apply uniqF__uniqBlocks in Huniq. inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  intros c1 Hlkc1.
  assert (c1 = insn_trunc id1 truncop0 t1 v1 t2) as EQ.
    eapply uniqFdef__lookupInsnViaIDFromBlocks in Hlk1; eauto.
  subst.
  split; auto.
    intros.
    assert (block_intro l3 ps1 (cs1' ++ insn_trunc id1 truncop0 t1 v1 t2 :: cs1)
      tmn1 = b1) as EQ.
      eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
    subst. auto.
Qed.

Lemma EXT__wf_gvs : forall
  (F1 : fdef) extop0 t1 v1 t2 lc
  (id1 : id) gvs TD gl
  (H11 : EXT TD lc gl extop0 t1 v1 t2 = Some gvs)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1
  (Hreach: isReachableFromEntry F1
    (block_intro l3 ps1 (cs1' ++ insn_ext id1 extop0 t1 v1 t2 :: cs1) tmn1))
  (Hin : blockInFdefB
           (block_intro l3 ps1 (cs1' ++ insn_ext id1 extop0 t1 v1 t2 :: cs1)
             tmn1) F1 = true),
  wf_GVs TD gl F1 lc id1 gvs.
Proof.
  intros.
  destruct F1 as [fh1 bs1].
  assert (lookupInsnViaIDFromBlocks bs1 id1 =
    Some (insn_cmd (insn_ext id1 extop0 t1 v1 t2))) as Hlk1.
    apply uniqF__uniqBlocks in Huniq. inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  intros c1 Hlkc1.
  assert (c1 = insn_ext id1 extop0 t1 v1 t2) as EQ.
    eapply uniqFdef__lookupInsnViaIDFromBlocks in Hlk1; eauto.
  subst.
  split; auto.
    intros.
    assert (block_intro l3 ps1 (cs1' ++ insn_ext id1 extop0 t1 v1 t2 :: cs1)
      tmn1 = b1) as EQ.
      eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
    subst. auto.
Qed.

Lemma CAST__wf_gvs : forall
  (F1 : fdef) castop0 t1 v1 t2 lc
  (id1 : id) gvs TD gl
  (H11 : CAST TD lc gl castop0 t1 v1 t2 = Some gvs)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1
  (Hreach: isReachableFromEntry F1
    (block_intro l3 ps1 (cs1' ++ insn_cast id1 castop0 t1 v1 t2 :: cs1) tmn1))
  (Hin : blockInFdefB
           (block_intro l3 ps1 (cs1' ++ insn_cast id1 castop0 t1 v1 t2 :: cs1)
             tmn1) F1 = true),
  wf_GVs TD gl F1 lc id1 gvs.
Proof.
  intros.
  destruct F1 as [fh1 bs1].
  assert (lookupInsnViaIDFromBlocks bs1 id1 =
    Some (insn_cmd (insn_cast id1 castop0 t1 v1 t2))) as Hlk1.
    apply uniqF__uniqBlocks in Huniq. inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  intros c1 Hlkc1.
  assert (c1 = insn_cast id1 castop0 t1 v1 t2) as EQ.
    eapply uniqFdef__lookupInsnViaIDFromBlocks in Hlk1; eauto.
  subst.
  split; auto.
    intros.
    assert (block_intro l3 ps1 (cs1' ++ insn_cast id1 castop0 t1 v1 t2 :: cs1)
      tmn1 = b1) as EQ.
      eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
    subst. auto.
Qed.

Lemma ICMP__wf_gvs : forall
  (F1 : fdef) (v : value) (v0 : value) lc
  (id1 : id) (cnd0 : cond) gvs3 TD t0 gl
  (H11 : ICMP TD lc gl cnd0 t0 v v0 = ret gvs3)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1
  (Hreach: isReachableFromEntry F1
    (block_intro l3 ps1 (cs1' ++ insn_icmp id1 cnd0 t0 v v0 :: cs1) tmn1))
  (Hin : blockInFdefB
           (block_intro l3 ps1 (cs1' ++ insn_icmp id1 cnd0 t0 v v0 :: cs1) tmn1)
           F1 = true),
  wf_GVs TD gl F1 lc id1 gvs3.
Proof.
  intros.
  destruct F1 as [fh1 bs1].
  assert (lookupInsnViaIDFromBlocks bs1 id1 =
    Some (insn_cmd (insn_icmp id1 cnd0 t0 v v0))) as Hlk1.
    apply uniqF__uniqBlocks in Huniq. inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  intros c1 Hlkc1.
  assert (c1 = insn_icmp id1 cnd0 t0 v v0) as EQ.
    eapply uniqFdef__lookupInsnViaIDFromBlocks in Hlk1; eauto.
  subst.
  split; auto.
    intros.
    assert (block_intro l3 ps1 (cs1' ++ insn_icmp id1 cnd0 t0 v v0 :: cs1) tmn1
      = b1) as EQ.
      eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
    subst. auto.
Qed.

Lemma FCMP__wf_gvs : forall
  (F1 : fdef) (v1 v2 : value) lc
  (id1 : id) fcond0 fp0 gvs3 TD gl
  (H11 : FCMP TD lc gl fcond0 fp0 v1 v2 = ret gvs3)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1
  (Hreach: isReachableFromEntry F1
    (block_intro l3 ps1 (cs1' ++ insn_fcmp id1 fcond0 fp0 v1 v2 :: cs1) tmn1))
  (Hin : blockInFdefB
           (block_intro l3 ps1 (cs1' ++ insn_fcmp id1 fcond0 fp0 v1 v2 :: cs1)
           tmn1) F1 = true),
  wf_GVs TD gl F1 lc id1 gvs3.
Proof.
  intros.
  destruct F1 as [fh1 bs1].
  assert (lookupInsnViaIDFromBlocks bs1 id1 =
    Some (insn_cmd (insn_fcmp id1 fcond0 fp0 v1 v2))) as Hlk1.
    apply uniqF__uniqBlocks in Huniq. inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  intros c1 Hlkc1.
  assert (c1 = insn_fcmp id1 fcond0 fp0 v1 v2) as EQ.
    eapply uniqFdef__lookupInsnViaIDFromBlocks in Hlk1; eauto.
  subst.
  split; auto.
    intros.
    assert (block_intro l3 ps1 (cs1' ++ insn_fcmp id1 fcond0 fp0 v1 v2 :: cs1)
      tmn1 = b1) as EQ.
      eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
    subst. auto.
Qed.

Lemma preservation_cmd_non_updated_case : forall
  (S : system)
  (los : layouts)
  (nts : namedts)
  (Ps : list product)
  (F : fdef)
  (B : block)
  (lc : GVsMap)
  (gl : GVMap)
  (fs : GVMap)
  (EC : list ExecutionContext)
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 : mem)
  (als : list mblock)
  c0
  (Hid : getCmdID c0 = None)
  (HwfS1 : wf_State {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            Globals := gl;
            FunTable := fs |}
            {|
            ECS := {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := c0 :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Allocas := als |} :: EC;
            Mem := Mem0 |}),
   wf_State {|
     CurSystem := S;
     CurTargetData := (los, nts);
     CurProducts := Ps;
     Globals := gl;
     FunTable := fs |}
     {|
     ECS := {|
            CurFunction := F;
            CurBB := B;
            CurCmds := cs;
            Terminator := tmn;
            Locals := lc;
            Allocas := als |} :: EC;
     Mem := Mem0 |}.
Proof.
  intros.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0)
    as R1.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto | congruence]).
      assert (NoDup (getBlockLocs (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn))) 
        as Hnotin.
        eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.
      destruct cs; simpl_env in *.
      Case "1.1.1".
        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq; eauto.

      Case "1.1.2".
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq ; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
Qed.

Lemma preservation_dbCall_case : forall fid fa rt la va lb gvs los
  nts s lc Ps gl
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (HwfF: wf_fdef s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hinit : initLocals (los,nts) la gvs = Some lc),
  wf_defs (los,nts) gl (fdef_intro (fheader_intro fa rt fid la va) lb) lc
    (getArgsIDs la).
Proof.
  intros.
  assert (incl nil (bound_blocks lb)) as J.
    intros x J. inv J.
  intros id1 gvs1 Hin Hlklc.
  intros x Hlkx. 
  contradict Hin.
    apply getInsnLoc__notin__getArgsIDs' in Hlkx; auto.
Qed.

Definition wf_impure_id (f:fdef) (id1:id) : Prop :=
forall c1,
  lookupInsnViaIDFromFdef f id1 = Some (insn_cmd c1) ->
  (forall b1, cmdInFdefBlockB c1 f b1 = true -> isReachableFromEntry f b1).

Lemma impure_cmd__eval_rhs: forall TD gl lc c gv3,
  ~ pure_cmd c -> eval_rhs TD gl lc c gv3.
Proof.
  destruct c; simpl; intros; try solve [auto | contradict H; auto].
Qed.

Lemma wf_impure_id__wf_gvs: forall F c TD gl lc gv b,
  uniqFdef F -> wf_impure_id F (getCmdLoc c) -> ~ pure_cmd c ->
  cmdInBlockB c b -> blockInFdefB b F ->
  wf_GVs TD gl F lc (getCmdLoc c) gv.
Proof.
  intros. intros x Hlkx.
  assert (c = x) as EQ. 
    destruct b.
    simpl in H2.
    apply IngetCmdsIDs__lookupCmdViaIDFromFdef with (c1:=c) in H3; auto.
      congruence.
      apply InCmdsB_in; auto.
  subst.
  split.
    apply impure_cmd__eval_rhs; auto.
    unfold wf_impure_id in H0. eauto.
Qed.

Lemma preservation_impure_cmd_updated_case : forall
  (F : fdef)
  (B : block)
  (lc : GVsMap)
  (gv3 : GVs)
  (cs : list cmd)
  (tmn : terminator)
  id0 c0 los nts gl Mem0 als EC fs Ps S
  (Hid : Some id0 = getCmdID c0) (Hinpure: ~ pure_cmd c0)
  (Hwfgv : wf_impure_id F id0)
  (HwfS1 : wf_State {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            Globals := gl;
            FunTable := fs |}
            {|
            ECS := {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := c0 :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Allocas := als |} :: EC;
            Mem := Mem0 |}),
   wf_State {|
     CurSystem := S;
     CurTargetData := (los, nts);
     CurProducts := Ps;
     Globals := gl;
     FunTable := fs |}
     {|
     ECS := {|
            CurFunction := F;
            CurBB := B;
            CurCmds := cs;
            Terminator := tmn;
            Locals := updateAddAL GVs lc id0 gv3;
            Allocas := als |} :: EC;
     Mem := Mem0 |}.
Proof.
  intros.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0)
    as R1.
  assert (HeqR1':=HeqR1).
  unfold inscope_of_cmd, inscope_of_id in HeqR1'.
  assert (uniqFdef F) as HuniqF.
    eapply wf_system__uniqFdef; eauto.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto | congruence]).
      assert (Hid':=Hid).
      symmetry in Hid.
      apply getCmdLoc_getCmdID in Hid.
      subst.
      assert (cmdInBlockB c0 (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) = true)
        as Hin.
        simpl. apply In_InCmdsB. apply in_middle.
      assert (NoDup (getBlockLocs (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn))) 
        as Hnotin.
        eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.
      destruct cs; simpl_env in *.
      Case "1.1.1".
        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite <- Hid' in J2.
        assert (HwfF:=HFinPs1). eapply wf_system__wf_fdef in HwfF; eauto.
        eapply wf_defs_updateAddAL; eauto.
          eapply wf_impure_id__wf_gvs; eauto.

      Case "1.1.2".
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc;
          eauto.
        rewrite <- Hid' in J2.
        assert (HwfF:=HFinPs1). eapply wf_system__wf_fdef in HwfF; eauto.
        eapply wf_defs_updateAddAL; eauto.
          eapply wf_impure_id__wf_gvs; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
Qed.

Lemma isReachableFromEntry_helper : forall F l1 ps1 cs1 c1 cs2 tmn1 c0 b1,
  uniqFdef F ->
  isReachableFromEntry F (block_intro l1 ps1 (cs1++c1::cs2) tmn1) ->
  blockInFdefB (block_intro l1 ps1 (cs1++c1::cs2) tmn1) F = true ->
  lookupInsnViaIDFromFdef F (getCmdLoc c1) = ret insn_cmd c0 ->
  cmdInFdefBlockB c0 F b1 = true ->
  isReachableFromEntry F b1.
Proof.
  intros. 
  assert (b1 = block_intro l1 ps1 (cs1++c1::cs2) tmn1) as EQ.
    unfold cmdInFdefBlockB in H3.
    bdestruct H3 as J1 J2.
    apply lookupInsnViaIDFromFdef__eqid in H2. simpl in H2.
    apply cmdInBlockB__inGetBlockLocs in J1. rewrite H2 in J1.
    eapply block_eq2 with (id1:=getCmdLoc c1); eauto.
      simpl. apply in_or_app. right. apply in_or_app. left.
      apply InGetCmdsLocs_middle.
  subst. auto.
Qed.

Lemma preservation : forall cfg S1 S2 tr,
  sInsn cfg S1 S2 tr -> wf_State cfg S1 -> wf_State cfg S2.
Proof.
  intros cfg S1 S2 tr HsInsn HwfS1.
  (sInsn_cases (induction HsInsn) Case); destruct TD as [los nts].
Focus.
Case "sReturn".
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]]; subst.
  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return rid RetTy Result))
             (insn_return rid RetTy Result)) as R1.
  destruct R1; try solve [inversion Hinscope1].
  split. congruence.
  split; auto.
  split; auto.
  SCase "1".
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.

    remember (getCmdID c') as R.
    destruct c' as [ | | | | | | | | | | | | | | | | i0 n c rt va v p]; 
      try solve [inversion H].
    assert (In (insn_call i0 n c rt va v p)
      (cs2'++[insn_call i0 n c rt va v p] ++ cs')) as HinCs.
      apply in_or_app. right. simpl. auto.
    assert (Hwfc := HBinF2).
    eapply wf_system__wf_cmd with (c:=insn_call i0 n c rt va v p) in Hwfc; 
      eauto.
    assert (wf_fdef S (module_intro los nts Ps) F') as HwfF.
      eapply wf_system__wf_fdef; eauto.
    assert (uniqFdef F') as HuniqF.
      eapply wf_system__uniqFdef; eauto.

    SSCase "1.1".
      assert (NoDup (getBlockLocs 
                       (block_intro l2 ps2
                          (cs2' ++ insn_call i0 n c rt va v p :: cs') tmn'))) 
        as Hnotin.
        eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.
      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        assert (HeqR2':=HeqR2).
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        unfold returnUpdateLocals in H1. simpl in H1.
        remember (getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR.
          remember (GVsSig.(lift_op1) (fit_gv (los, nts) rt) g rt) as R2.
          destruct R2; inv H1.
          change i0 with
            (getCmdLoc (insn_call i0 false c rt va v p)); auto.
          eapply wf_defs_updateAddAL; eauto.
            simpl. apply In_InCmdsB. apply in_middle.
            eapply wf_impure_id__wf_gvs; eauto.
              simpl. intros c0 Hlkc0. intros b1 J.
              clear - Hreach2 J HuniqF Hlkc0 HBinF2.
              eapply isReachableFromEntry_helper; eauto.

              simpl. apply In_InCmdsB. solve_in_list.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto.

      SSSCase "1.1.2".
        assert (HeqR2':=HeqR2).
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        unfold returnUpdateLocals in H1. simpl in H1.
        remember (getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR.
          remember (GVsSig.(lift_op1) (fit_gv (los, nts) rt) g rt) as R2.
          destruct R2; inv H1.
          inv Hwfc. uniq_result.
          change i0 with
            (getCmdLoc (insn_call i0 false c rt va v
              (List.map
                 (fun p : typ * attributes * value =>
                   let '(typ_', attr, value_'') := p in
                    (typ_', attr, value_''))
                 typ'_attributes'_value''_list))); auto.
          eapply wf_defs_updateAddAL; eauto 2.
            simpl. apply In_InCmdsB. apply in_middle.
            eapply wf_impure_id__wf_gvs; eauto.
              simpl. intros c1 Hlkc1. intros b1 J.
              clear - Hreach2 J HuniqF Hlkc1 HBinF2.
              eapply isReachableFromEntry_helper with (cs2:=[c0]++cs')
                (cs1:=cs2')(c1:=insn_call i0 false c rt va v
                     (List.map
                        (fun p : typ * attributes * value =>
                          let '(typ_', attr, value_'') := p in
                            (typ_', attr, value_''))
                        typ'_attributes'_value''_list)) in Hreach2;
                 eauto.

              simpl. apply In_InCmdsB. solve_in_list.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto.
    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[c']).
      simpl_env. auto.
Unfocus.

Focus.
Case "sReturnVoid".
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]]; subst.
  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return_void rid))
             (insn_return_void rid)) as R1.
  destruct R1; try solve [inversion Hinscope1].
  split. congruence.
  split; auto.
  split; auto.
  SCase "1".
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    SSCase "1.1".
      apply HwfCall' in HBinF1. simpl in HBinF1.
      assert (NoDup (getBlockLocs 
                       (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn'))) 
        as Hnotin.
        eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.
      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnotin H1.
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct_cmd c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto.

      SSSCase "1.1.2".
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnotin H1.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct_cmd c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto.

    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[c']).
      simpl_env. auto.
Unfocus.

Case "sBranch".
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br bid Cond l1 l2))
             (insn_br bid Cond l1 l2)) as R1.
  destruct R1; try solve [inversion Hinscope1].
  split. congruence.
  split; auto.
  split; auto.
  split; auto.
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
    assert (blockInFdefB (block_intro l' ps' cs' tmn') F = true) as HBinF'.
      clear - H1 HBinF1 HwfF HuniqF.
      symmetry in H1.
      destruct (isGVZero (los, nts) c);
        apply lookupBlockViaLabelFromFdef_inv in H1;
          try solve [auto | destruct H1; auto].
    split.
      clear - Hreach1 H1 HBinF1 HwfF HuniqF.
      symmetry in H1.
      destruct (isGVZero (los, nts) c);
        eapply isReachableFromEntry_successors in H1;
          try solve [eauto | simpl; auto].
    split; auto.
    split; auto.
    split.
      clear - H2 HeqR1 H1 Hinscope1 HBinF1 HwfF HuniqF Hreach1.
      eapply inscope_of_tmn_br in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Focus.
Case "sBranch_uncond".
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br_uncond bid l0))
             (insn_br_uncond bid l0)) as R1.
  destruct R1; try solve [inversion Hinscope1].
  split. congruence.
  split; auto.
  split; auto.
  split; auto.
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
    assert (blockInFdefB (block_intro l' ps' cs' tmn') F = true) as HBinF'.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H;
          try solve [auto | destruct H; auto].
    split.
      symmetry in H.
      eapply isReachableFromEntry_successors in H;
        try solve [eauto | simpl; auto].
    split; auto.
    split; auto.
    split.
      clear - H0 HeqR1 Hinscope1 H HBinF1 HwfF HuniqF Hreach1.
      assert (Hwds := HeqR1).
      eapply inscope_of_tmn_br_uncond with (cs':=cs')(l':=l')(ps':=ps')
        (tmn':=tmn') in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Case "sBop". eapply preservation_pure_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  eapply BOP__wf_gvs; eauto.
Case "sFBop". eapply preservation_pure_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  eapply FBOP__wf_gvs; eauto.
Case "sExtractValue".
  eapply preservation_pure_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  eapply extractvalue__wf_gvs; eauto.
Case "sInsertValue".
  eapply preservation_pure_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  eapply insertvalue__wf_gvs in H1; eauto.
Case "sMalloc".
  eapply preservation_impure_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  intros c0 Hlkc0 b1 J. eapply wf_system__uniqFdef in HFinPs1; eauto.
  eapply isReachableFromEntry_helper; eauto.
Case "sFree". eapply preservation_cmd_non_updated_case in HwfS1; eauto.
Case "sAlloca".
  eapply preservation_impure_cmd_updated_case in HwfS1; simpl; eauto 2.
    destruct HwfS1 as [_ HwfS1].
    split; eauto. congruence.

    destruct HwfS1 as
      [_ [HwfSystem [HmInS [
       [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
       [HwfEC HwfCall]]]]]; subst.
    intros c0 Hlkc0 b1 J. eapply wf_system__uniqFdef in HFinPs1; eauto.
    eapply isReachableFromEntry_helper; eauto.
Case "sLoad".
  eapply preservation_impure_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  intros c0 Hlkc0 b1 J. eapply wf_system__uniqFdef in HFinPs1; eauto.
  eapply isReachableFromEntry_helper; eauto.
Case "sStore". eapply preservation_cmd_non_updated_case in HwfS1; eauto.
Case "sGEP".
  assert (J:=HwfS1).
  destruct J as
    [_ [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
         [HwfEC HwfCall]]]]]; subst.
  assert (J:=HBinF1).
  eapply wf_system__wf_cmd with (c:=insn_gep id0 inbounds0 t v idxs t') in HBinF1;
    eauto using in_middle.
  inv HBinF1; eauto.
  eapply preservation_impure_cmd_updated_case in HwfS1; simpl; eauto.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  destruct F as [fh1 bs1].
  assert (lookupInsnViaIDFromBlocks bs1 id0 =
    Some (insn_cmd (insn_gep id0 inbounds0 t v idxs t'))) as Hlk1.
    apply uniqF__uniqBlocks in HuniqF. inv HuniqF.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  intros c1 Hlkc1 b1 Hin.
  assert (c1 = insn_gep id0 inbounds0 t v idxs t') as EQ.
    eapply uniqFdef__lookupInsnViaIDFromBlocks in Hlk1; eauto.
  subst.
  assert (block_intro l3 ps3 (cs3' ++ insn_gep id0 inbounds0 t v idxs t':: cs)
    tmn = b1) as EQ.
    eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
  subst. auto.

Case "sTrunc".
  eapply preservation_pure_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  eapply TRUNC__wf_gvs; eauto.

Case "sExt".
  eapply preservation_pure_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  eapply EXT__wf_gvs; eauto.

Case "sCast".
  eapply preservation_pure_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  eapply CAST__wf_gvs; eauto.

Case "sIcmp". eapply preservation_pure_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  eapply ICMP__wf_gvs; eauto.

Case "sFcmp".
  eapply preservation_pure_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfS1 as
    [_ [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
     [HwfEC HwfCall]]]]]; subst.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  eapply FCMP__wf_gvs; eauto.

Case "sSelect".
  assert (J:=HwfS1).
  destruct J as
    [_ [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]
         [HwfEC HwfCall]]]]]; subst.
  assert (J:=HBinF1).
  eapply wf_system__wf_cmd with (c:=insn_select id0 v0 t v1 v2) in HBinF1;
    eauto using in_middle.
  inv HBinF1; eauto.
  assert (wf_impure_id F id0) as W.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
    destruct F as [fh1 bs1].
    assert (lookupInsnViaIDFromBlocks bs1 id0 =
      Some (insn_cmd (insn_select id0 v0 t v1 v2))) as Hlk1.
      apply uniqF__uniqBlocks in HuniqF. inv HuniqF.
      eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
    intros c1 Hlkc1 b1 Hin.
    assert (c1 = insn_select id0 v0 t v1 v2) as EQ.
    eapply uniqFdef__lookupInsnViaIDFromBlocks in Hlk1; eauto.
    subst.
    assert (block_intro l3 ps3 (cs3' ++ insn_select id0 v0 t v1 v2 :: cs)
      tmn = b1) as EQ.
      eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
    subst. auto.
  destruct (isGVZero (los, nts) c);
    eapply preservation_impure_cmd_updated_case in HwfS1; simpl; eauto.

Focus.
Case "sCall".
  destruct HwfS1 as [_ [HwfSys [HmInS [
    [Hreach [HBinF [HFinPs [Hinscope [l1 [ps [cs'' Heq]]]]]]]
    [HwfECs HwfCall]]]]]; subst.
  assert (InProductsB (product_fdef (fdef_intro
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    apply lookupFdefViaPtr_inversion in H1.
    destruct H1 as [fn [H11 H12]].
    eapply lookupFdefViaIDFromProducts_inv; eauto.
  split. congruence.
  split; auto.
  split; auto.
  split; auto.
  SCase "1".
    assert (uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb)) as Huniq.
      eapply wf_system__uniqFdef; eauto.
    assert (wf_fdef S (module_intro los nts Ps) 
      (fdef_intro (fheader_intro fa rt fid la va) lb)) as HwfF.
      eapply wf_system__wf_fdef; eauto.
    split.
      simpl. eapply reachable_entrypoint; eauto.
    split.
      apply entryBlockInFdef in H2; auto.
    split; auto.
    split.
      assert (ps'=nil) as EQ.
        eapply entryBlock_has_no_phinodes with (s:=S); eauto.        
      subst.
      apply AlgDom.dom_entrypoint in H2.
      destruct cs'.
        unfold inscope_of_tmn.
        rewrite H2. simpl.
        eapply preservation_dbCall_case; eauto.

        unfold inscope_of_cmd, inscope_of_id.
        rewrite init_scope_spec1; auto.
        rewrite H2. simpl.
        destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n];
          try solve [contradict n; auto].
        eapply preservation_dbCall_case; eauto.

    exists l'. exists ps'. exists nil. simpl_env. auto.
  split.
  SCase "2".
    repeat (split; auto). eauto.
  SCase "3".
    simpl. intros b HbInBs. destruct b as [? ? ? t].
    destruct t; auto.

Unfocus.

Case "sExCall".
  match goal with
  | H6: exCallUpdateLocals _ _ _ _ _ _ = _ |- _ => 
      unfold exCallUpdateLocals in H6 end.
  destruct noret0.
    match goal with | H6: Some _ = Some _ |- _ => inv H6 end.
    eapply preservation_cmd_non_updated_case in HwfS1; eauto.

    match goal with
    | H6: match _ with
          | Some _ => _ 
          | None => _
          end = _ |- _ =>
      destruct oresult; tinv H6;
      remember (fit_gv (los, nts) rt1 g) as R;
      destruct R; inv H6
    end.
    eapply preservation_impure_cmd_updated_case in HwfS1; simpl; eauto.
    intros x Hlkx b1 J.
    destruct HwfS1 as [_ [HwfSys [HmInS [
      [Hreach [HBinF [HFinPs [Hinscope [l1 [ps [cs'' Heq]]]]]]]
      [HwfECs HwfCall]]]]]; subst.
    eapply isReachableFromEntry_helper; eauto.
    eapply wf_system__uniqFdef in HFinPs; eauto.
Qed.

End OpsemDom. End OpsemDom.
