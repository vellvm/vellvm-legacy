Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import primitives.
Require Import mem2reg.
Require Import opsem_props.
Require Import palloca_props.
Require Import phiplacement_bsim_defs.
Require Import top_wfS.
Require Import trans_tactic.

(*********************************************************)
(*
   preserving reachablity and succ does not require WF_PhiInfo 
   So, we do not use PhiInfo 
*)

Definition phinodes_placement_fdef pid ty al nids sccs prds (f:fdef): fdef :=
match f with
| fdef_intro fh bs => 
  fdef_intro fh (List.map (phinodes_placement_block pid ty al nids sccs prds) bs)
end.

Lemma phinodes_placement_fdef_spec1: forall rd pid ty al sccs prds f,
  phinodes_placement rd pid ty al sccs prds f  =
  phinodes_placement_fdef pid ty al 
    (fst (gen_fresh_ids rd (getFdefLocs f))) sccs prds f.
Proof.
  unfold phinodes_placement, phinodes_placement_fdef.
  intros.
  destruct_let. destruct f. auto.
Qed.

Lemma phinodes_placement_block__getBlockLabel: forall pid t al nids succs
  preds b,
  getBlockLabel b =
  getBlockLabel (phinodes_placement_block pid t al nids succs preds b).
Proof.
  destruct b as [l0 ? ? ?]; simpl.
    destruct (nids ! l0) as [[[]]|]; auto.
    destruct (preds ! l0) as [[]|]; auto.
Qed.

Lemma phinodes_placement_block__getBlockTmn: forall pid t al nids succs preds b, 
  getBlockTmn b = 
    getBlockTmn (phinodes_placement_block pid t al nids succs preds b).
Proof. 
  destruct b as [l0 ? ? t0]; simpl.
    destruct (nids ! l0) as [[[]]|]; auto.
    destruct (preds ! l0) as [[]|]; auto.
Qed.

Lemma phinodes_placement_block__getBlockTmn_match: forall pid t al nids succs 
  preds b, 
  terminator_match (getBlockTmn b) 
    (getBlockTmn (phinodes_placement_block pid t al nids succs preds b)).
Proof. 
  intros.
  rewrite <- phinodes_placement_block__getBlockTmn.
  destruct (getBlockTmn b); simpl; auto.
Qed.

Lemma phinodes_placement_fdef_spec2: forall pid t al nids succs preds fh bs, 
  phinodes_placement_fdef pid t al nids succs preds (fdef_intro fh bs) = 
    fdef_intro fh 
      (List.map (phinodes_placement_block pid t al nids succs preds) bs).
Proof. simpl. auto. Qed.

Definition phiplacement pid t al nids succs preds := mkPass 
(phinodes_placement_block pid t al nids succs preds)
(phinodes_placement_fdef pid t al nids succs preds)
(phinodes_placement_fdef_spec2 pid t al nids succs preds)
(phinodes_placement_block__getBlockLabel pid t al nids succs preds)
(phinodes_placement_block__getBlockTmn_match pid t al nids succs preds)
.

Ltac fold_phiplacement_tac :=
  match goal with
  | |- context [phinodes_placement_fdef ?pid ?t ?al ?nids ?succs ?preds ?f] =>
    replace (phinodes_placement_fdef pid t al nids succs preds f) 
      with (ftrans (phiplacement pid t al nids succs preds) f); auto
  end.

Lemma phinodes_placement_reachablity_analysis: forall f rd pid ty al,
  reachablity_analysis f =
  reachablity_analysis
     (phinodes_placement rd pid ty al (successors f)
        (make_predecessors (successors f)) f).
Proof.
  intros.
  rewrite phinodes_placement_fdef_spec1.
  fold_phiplacement_tac.
  apply TransCFG.pres_reachablity_analysis.
Qed.

Lemma phinodes_placement_successors: forall f rd pid ty al,
  successors f =
  successors
    (phinodes_placement rd pid ty al (successors f)
       (make_predecessors (successors f)) f).
Proof.
  intros.
  rewrite phinodes_placement_fdef_spec1.
  fold_phiplacement_tac.
  apply TransCFG.pres_successors.
Qed.

(* preserving uniqness and wfness require WF_PhiInfo *)

Definition phinodes_placement_blk (pinfo:PhiInfo) (b:block): block :=
phinodes_placement_block (PI_id pinfo) (PI_typ pinfo) (PI_align pinfo)
  (PI_newids pinfo) (PI_succs pinfo) (PI_preds pinfo) b.

Definition phinodes_placement_f (pinfo:PhiInfo) (f:fdef): fdef :=
match f with
| fdef_intro fh bs => fdef_intro fh (List.map (phinodes_placement_blk pinfo) bs)
end.

Lemma phinodes_placement_f_spec1: forall pinfo,
  phinodes_placement (PI_rd pinfo) (PI_id pinfo) (PI_typ pinfo) (PI_align pinfo)
    (PI_succs pinfo) (PI_preds pinfo) (PI_f pinfo) =
  phinodes_placement_f pinfo (PI_f pinfo).
Proof.
  unfold phinodes_placement, phinodes_placement_f, phinodes_placement_blk, 
         PI_newids.
  intros.
  destruct_let. destruct (PI_f pinfo). auto.
Qed.

Lemma phinodes_placement_blk__getBlockLabel: forall pinfo b,
  getBlockLabel b =
  getBlockLabel (phinodes_placement_blk pinfo b).
Proof.
  unfold phinodes_placement_blk. intro.
  apply phinodes_placement_block__getBlockLabel; auto.
Qed.

Lemma phinodes_placement_blk__getBlockTmn_match: forall pinfo b, 
  terminator_match (getBlockTmn b) 
    (getBlockTmn (phinodes_placement_blk pinfo b)).
Proof. 
  intros.
  unfold phinodes_placement_blk.
  apply phinodes_placement_block__getBlockTmn_match; auto.
Qed.

Lemma phinodes_placement_f_spec2: forall pinfo fh bs, 
  phinodes_placement_f pinfo (fdef_intro fh bs) = 
    fdef_intro fh (List.map (phinodes_placement_blk pinfo) bs).
Proof. simpl. auto. Qed.

Definition PhiPlacement pinfo := mkPass 
(phinodes_placement_blk pinfo)
(phinodes_placement_f pinfo)
(phinodes_placement_f_spec2 pinfo)
(phinodes_placement_blk__getBlockLabel pinfo)
(phinodes_placement_blk__getBlockTmn_match pinfo)
.

Ltac fold_PhiPlacement_tac :=
repeat match goal with
| |- context [phinodes_placement_f ?pinfo ?f] =>
  replace (phinodes_placement_f pinfo f) 
    with (ftrans (PhiPlacement pinfo) f); auto
| |- context [phinodes_placement_blk ?pinfo ?b] =>
  replace (phinodes_placement_blk pinfo b) 
    with (btrans (PhiPlacement pinfo) b); auto
| |- context [phinodes_placement_f ?pinfo] =>
  replace (phinodes_placement_f pinfo) 
    with (ftrans (PhiPlacement pinfo)); auto
| |- context [phinodes_placement_blk ?pinfo] =>
  replace (phinodes_placement_blk pinfo) 
    with (btrans (PhiPlacement pinfo)); auto
end.

(*********************************************************)
(* wfness *)

Lemma phinodes_placement_blk_tail_inv: forall pinfo b lid pid sid scs
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR2 : ret scs = (PI_succs pinfo) ! (getBlockLabel b))
  (Hnonempty: scs <> nil),
  exists l0, exists ps0, exists cs0, exists tmn0, exists ps1, exists cs1,
    b = block_intro l0 ps0 cs0 tmn0 /\
    phinodes_placement_blk pinfo b = 
      block_intro l0 (ps1++ps0)
        (cs1 ++ cs0 ++ 
         [insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo))
           (PI_align pinfo)]) tmn0.
Proof.
  intros. destruct b as [l0 ps0 cs0 tmn0]. simpl in *. 
  exists l0. exists ps0. exists cs0. exists tmn0.
  rewrite <- HeqR1. rewrite <- HeqR2. 
  destruct scs; try congruence.
  destruct ((PI_preds pinfo) ! l0) as [[]|].
    exists nil. exists nil. auto.

    match goal with
    | |- context [ block_intro _ (?p::_) (?c::_++_) _] => 
         exists [p]; exists [c]; simpl_env; auto
    end.
 
    exists nil. exists nil. auto.
Qed.

Lemma phinodes_placement_blk_head_inv: forall pinfo b lid pid sid pds
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR3 : ret pds = (PI_preds pinfo) ! (getBlockLabel b))
  (Hneq : pds <> nil),
  exists l0, exists ps0, exists cs0, exists tmn0, exists cs2,
    b = block_intro l0 ps0 cs0 tmn0 /\
    phinodes_placement_blk pinfo b = 
      block_intro l0 
        ([gen_phinode pid (PI_typ pinfo) (PI_newids pinfo) pds]++ps0)
        ([insn_store sid (PI_typ pinfo) (value_id pid)
           (value_id (PI_id pinfo)) (PI_align pinfo)] ++ cs0 ++ cs2) tmn0.
Proof.
  intros. destruct b as [l0 ps0 cs0 tmn0]. simpl in *. 
  exists l0. exists ps0. exists cs0. exists tmn0.
  rewrite <- HeqR1. rewrite <- HeqR3. 
  destruct pds; try congruence.
  destruct ((PI_succs pinfo) ! l0) as [[]|].
    exists nil. auto.

    match goal with
    | |- context [ (_::_++[?c]) ] => exists [c]; simpl_env; auto
    end.

    exists nil. auto.
Qed.

Lemma phinodes_placement_blk_inv': forall pinfo b,
  exists l0, exists ps0, exists cs0, exists tmn0, 
    exists ps1, exists cs1, exists cs2,
    b = block_intro l0 ps0 cs0 tmn0 /\
    phinodes_placement_blk pinfo b = 
      block_intro l0 (ps1++ps0) (cs1 ++ cs0 ++ cs2) tmn0 /\
    ((ps1 = nil /\ cs1 = nil) \/ 
      exists lid, exists pid, exists sid,
        ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b) /\
      exists pds, 
        ps1 = [gen_phinode pid (PI_typ pinfo) (PI_newids pinfo) pds] /\
        cs1 = [insn_store sid (PI_typ pinfo) (value_id pid)
                 (value_id (PI_id pinfo)) (PI_align pinfo)] /\
        ret pds = (PI_preds pinfo) ! (getBlockLabel b) /\
        pds <> nil) /\
     (cs2 = nil \/
      exists lid, exists pid, exists sid,
        ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b) /\
      exists scs,
        cs2 = [insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo))
                  (PI_align pinfo)] /\
        ret scs = (PI_succs pinfo) ! (getBlockLabel b) /\
        scs <> nil).
Proof.
  intros. destruct b as [l0 ps0 cs0 tmn0]. simpl in *. 
  exists l0. exists ps0. exists cs0. exists tmn0.

Ltac phinodes_placement_blk_inv'_tac1 :=
  right;
  match goal with
  | |- context [ret (_, _, _) = ret (?lid, ?pid, ?sid)] =>
       exists lid; exists pid; exists sid
  end;
  split; auto;
  match goal with
  | |- context [Some _ = Some ([?a]++?A)] => 
       exists ([a]++A); simpl;
       repeat (split; try solve [auto | congruence])
  end.

Ltac phinodes_placement_blk_inv'_tac2 :=
  simpl_env; repeat (split; auto); phinodes_placement_blk_inv'_tac1.

  destruct ((PI_newids pinfo) ! l0) as [[[lid pid] sid]|].
    destruct ((PI_preds pinfo) ! l0) as [[|pd pds]|]; try solve [
      exists nil; exists nil;
      destruct ((PI_succs pinfo) ! l0) as [[|sc scs]|]; try solve [
        exists nil; tauto |
        match goal with
        | |- context [ (_++[?c]) ] => 
             exists [c]; phinodes_placement_blk_inv'_tac2
        end
      ] |

      match goal with
      | |- context [ block_intro _ (?p::_) (?c::_++_) _] => 
           exists [p]; exists [c]
      end;
      destruct ((PI_succs pinfo) ! l0) as [[]|]; try solve [
        exists nil; phinodes_placement_blk_inv'_tac2 |
        match goal with
        | |- context [ (_::_++[?c]) ] => 
             exists [c]; phinodes_placement_blk_inv'_tac2
        end
      ]
    ].

    exists nil. exists nil. exists nil. simpl_env. tauto.
Qed.

Lemma phinodes_placement_blk_inv: forall pinfo b,
  exists l0, exists ps0, exists cs0, exists tmn0, 
    exists ps1, exists cs1, exists cs2,
    b = block_intro l0 ps0 cs0 tmn0 /\
    phinodes_placement_blk pinfo b = 
      block_intro l0 (ps1++ps0) (cs1 ++ cs0 ++ cs2) tmn0.
Proof.
  intros.
  assert (J:=phinodes_placement_blk_inv' pinfo b).
  destruct J as [l0 [ps0 [cs0 [tmn0 [ps1 [cs1 [cs2 [EQ [J _]]]]]]]]]; subst.
  eauto 9.
Qed.

Lemma inserted_phi_operands__elim_aux: forall pinfo v l1 pds acc
  (Hin : In (v, l1)
          (fold_left
             (fun (acc : list (value * atom)) (p : atom) =>
              (match (PI_newids pinfo) ! p with
               | ret (lid0, _, _) => value_id lid0
               | merror => value_const (const_undef (PI_typ pinfo))
               end, p) :: acc) pds acc)),
  In (v, l1) acc \/ (In l1 pds /\ 
  match v with
  | value_id vid1 => 
      exists pid, exists sid, (PI_newids pinfo) ! l1 = Some (vid1, pid, sid)
  | value_const vc => vc = const_undef (PI_typ pinfo)
  end).
Proof.
  induction pds as [|a]; simpl; intros; auto.
    apply IHpds in Hin.
    destruct Hin as [Hin | [J1 J2]].
      destruct_in Hin.
        remember ((PI_newids pinfo) ! a) as R.
        destruct R as [[[]]|]; inv Hin; right; split; eauto.

      right. split; auto.  
Qed.

Lemma inserted_phi_operands__elim: forall pinfo v l1 pds
  (Hin : In (v, l1)
          (fold_left
             (fun (acc : list (value * atom)) (p : atom) =>
              (match (PI_newids pinfo) ! p with
               | ret (lid0, _, _) => value_id lid0
               | merror => value_const (const_undef (PI_typ pinfo))
               end, p) :: acc) pds nil)),
  In l1 pds /\ 
  match v with
  | value_id vid1 => 
      exists pid, exists sid, (PI_newids pinfo) ! l1 = Some (vid1, pid, sid)
  | value_const vc => vc = const_undef (PI_typ pinfo)
  end.
Proof.
  intros.
  apply inserted_phi_operands__elim_aux in Hin.
  destruct Hin as [Hin | Hin]; auto.
    tauto.
Qed.

Lemma phinodes_placement_insnDominates: forall pinfo b b' instr
  (Hin: insnInFdefBlockB instr (PI_f pinfo) b = true)
  (Heqb': b' = phinodes_placement_blk pinfo b) id_
  (Hdom: insnDominates id_ instr b),
  insnDominates id_ instr b'.
Proof.
  unfold insnDominates.
  intros. subst.
  assert (J:=phinodes_placement_blk_inv pinfo b).
  destruct J as [l0 [ps0 [cs0 [tmn0 [ps1 [cs1 [cs2 [EQ J]]]]]]]]; subst.
  rewrite J. 
  destruct instr; auto.
    destruct Hdom as [[ps1' [p1 [ps2 [J1 J2]]]] | 
                      [cs1' [c1 [cs2' [cs3 [J1 J2]]]]]]; subst.
      left. exists (ps1++ps1'). exists p1. exists ps2. simpl_env. auto.
      right. exists (cs1++cs1'). exists c1. exists cs2'. exists (cs3++cs2).
        simpl_env. auto.
    destruct Hdom as [Hdom EQ]; subst.
    split; auto.
    destruct Hdom as [[cs1' [c1 [cs2' [J1 J2]]]] |
                      [ps1' [p1 [ps2 [J1 J2]]]]]; subst.
      left. exists (cs1++cs1'). exists c1. exists (cs2'++cs2).
        simpl_env. auto.
      right. exists (ps1++ps1'). exists p1. exists ps2. simpl_env. auto.
Qed.

Lemma phinodes_placement_getBlockIDs: forall pinfo id0 b
  (Hin: In id0 (getBlockIDs b)),
  In id0 (getBlockIDs (phinodes_placement_blk pinfo b)).
Proof.
  intros.
  assert (J:=phinodes_placement_blk_inv pinfo b).
  destruct J as [l0 [ps0 [cs0 [tmn0 [ps1 [cs1 [cs2 [EQ J]]]]]]]]; subst.
  rewrite J. clear - Hin. simpl in *.
  destruct_in Hin.
    rewrite getPhiNodesIDs_app.
    xsolve_in_list.

    repeat (rewrite getCmdsIDs_app).
    xsolve_in_list.
Qed.

Lemma phinodes_placement_lookupBlockViaIDFromFdef: forall pinfo id0 b
  (HuniqF: uniqFdef (PI_f pinfo)) (Hwfpi: WF_PhiInfo pinfo)   
  (Hlkup: lookupBlockViaIDFromFdef (PI_f pinfo) id0 = Some b),
  lookupBlockViaIDFromFdef (phinodes_placement_f pinfo (PI_f pinfo)) id0 
    = Some (phinodes_placement_blk pinfo b).
Proof.
  intros.
  assert (J:=Hlkup).
  apply lookupBlockViaIDFromFdef__InGetBlockIDs in Hlkup.
  apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
    rewrite <- phinodes_placement_f_spec1.
    apply phinodes_placement__uniqFdef; auto.

    apply phinodes_placement_getBlockIDs; auto.

    fold_PhiPlacement_tac.
    apply TransCFG.pres_blockInFdefB; auto.
      solve_blockInFdefB.
Qed.

Section PresWF.

Variable (los:layouts) (nts:namedts) (Ps1 Ps2:products) (pinfo:PhiInfo)
         (M M':module) (f':fdef).
Hypothesis (Hwfpi: WF_PhiInfo pinfo)   
           (HeqM: M = module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
           (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
           (HeqF': f' = phinodes_placement_f pinfo (PI_f pinfo))
           (HwfF: wf_fdef [M] M (PI_f pinfo)) 
           (HuniqF: uniqFdef (PI_f pinfo)).

Lemma Heq_fheader: fheaderOfFdef (PI_f pinfo) = fheaderOfFdef f'.
Proof.
  subst.
  rewrite <- phinodes_placement_f_spec1.
  apply phinodes_placement_fheaderOfFdef.
Qed.

Lemma phinodes_placement_preserves_wf_typ: forall t,
  wf_typ [M] (los,nts) t -> wf_typ [M'] (los,nts) t.
Proof.
  assert (J:=Heq_fheader).
  eapply TopWFS.subst_fdef_preserves_single_wf_typ; eauto.
Qed.

Lemma wf_PI_typ': wf_typ [M'] (los, nts) (PI_typ pinfo).
Proof.
  assert (J:=phinodes_placement_preserves_wf_typ).
  subst.
  apply WF_PhiInfo_spec21 in HwfF; auto.
Qed.

Lemma phinodes_placement_insnInFdefBlockB: forall b instr
  (Hin: insnInFdefBlockB instr (PI_f pinfo) b = true),
  insnInFdefBlockB instr (phinodes_placement_f pinfo (PI_f pinfo))
    (phinodes_placement_blk pinfo b) = true.
Proof.
  intros.
  apply destruct_insnInFdefBlockB in Hin.
  destruct Hin as [Hin1 Hin2].
  apply insnInFdefBlockB_intro.
    assert (J:=phinodes_placement_blk_inv pinfo b).
    destruct J as [l0 [ps0 [cs0 [tmn0 [ps1 [cs1 [cs2 [EQ J]]]]]]]]; subst.
    rewrite J. clear J.
    destruct instr; simpl in *; auto.
      apply In_InPhiNodesB. xsolve_in_list.
      apply In_InCmdsB. xsolve_in_list.

    fold_PhiPlacement_tac.
    apply TransCFG.pres_blockInFdefB; auto.
Qed.

Lemma phinodes_placement_lookupTypViaIDFromFdef: forall id0 t
  (Hlkty: lookupTypViaIDFromFdef (PI_f pinfo) id0 = Some t),
  lookupTypViaIDFromFdef f' id0 = Some t.
Proof.
  intros.
  assert (Huniq':uniqFdef f').
    subst. 
    rewrite <- phinodes_placement_f_spec1.
    apply phinodes_placement__uniqFdef; auto.
  apply lookupTypViaIDFromFdef_intro; auto.
  subst.
  apply lookupTypViaIDFromFdef_elim in Hlkty; auto.
  destruct Hlkty as [[attr0 Hin] | [b [instr [Hin [J1 J2]]] ]].
    left. fold_PhiPlacement_tac.
    rewrite <- TransCFG.pres_getArgsOfFdef.
    eauto.

    apply phinodes_placement_insnInFdefBlockB in Hin. 
    right.
    exists (phinodes_placement_blk pinfo b). eauto.
Qed.

Lemma phinodes_placement_preserves_wf_const: forall c t,
  wf_const [M] (los,nts) c t -> wf_const [M'] (los,nts) c t.
Proof.
  assert (J:=Heq_fheader).
  eapply TopWFS.subst_fdef_preserves_single_wf_const; eauto.
Qed.

Lemma phinodes_placement_wf_value : forall v t
  (Hwfv: wf_value [M] M (PI_f pinfo) v t),
  wf_value [M'] M' f' v t.
Proof.
  intros.
  assert (J1:=phinodes_placement_preserves_wf_const).
  assert (J3:=phinodes_placement_preserves_wf_typ).
  assert (J2:=phinodes_placement_lookupTypViaIDFromFdef).
  inv Hwfv; uniq_result; constructor; eauto.
Qed.

Lemma phinodes_placement_wf_operand: forall b b'
  (Heqb': b' = phinodes_placement_blk pinfo b) instr id_
  (Hwfop: wf_operand (PI_f pinfo) b instr id_),
  wf_operand f' b' instr id_.
Proof.
  intros.
  inv Hwfop.
  assert (J:=H). 
  apply phinodes_placement_insnInFdefBlockB in H.
  econstructor; eauto 1.  
    fold_PhiPlacement_tac.
    rewrite <- TransCFG.pres_getArgsIDsOfFdef.
    rewrite <- TransCFG.pres_isReachableFromEntry.
    destruct H3 as [[[b0 [J1 H3]] | H3]| J3]; auto.
    left. left.
    exists (phinodes_placement_blk pinfo b0).
    split.
      simpl.
      apply phinodes_placement_lookupBlockViaIDFromFdef; auto.

      fold_PhiPlacement_tac.
      rewrite <- TransCFG.pres_blockStrictDominates; auto.
      destruct H3 as [H3 | H3]; auto.
      left.
      eapply phinodes_placement_insnDominates; eauto.
Qed.

Lemma phinodes_placement_wf_insn_base: forall b b'
  (Heqb': b' = phinodes_placement_blk pinfo b) instr
  (HwfI: wf_insn_base (PI_f pinfo) b instr),
  wf_insn_base f' b' instr.
Proof.
  intros.
  assert (J:=@phinodes_placement_wf_operand b b' Heqb' instr).
  inv HwfI.
  apply phinodes_placement_insnInFdefBlockB in H.
  econstructor; eauto 1.
    intros id_ Hin.
    apply H2 in Hin. auto.
Qed.

Lemma phinodes_placement_wf_trunc : forall b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) instr
  (HwfI : wf_trunc [M] M (PI_f pinfo) b instr),
  wf_trunc [M'] M' f' b' instr.
Proof.
  intros.
  assert (J1:=@phinodes_placement_wf_insn_base b b' Heqb' instr).
  assert (J2:=phinodes_placement_wf_value).
  assert (J3:=@phinodes_placement_preserves_wf_typ).
  inv HwfI; uniq_result; try solve [
    econstructor; eauto 3
  ].
Qed.

Lemma phinodes_placement_wf_ext : forall b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) instr
  (HwfI : wf_ext [M] M (PI_f pinfo) b instr),
  wf_ext [M'] M' f' b' instr.
Proof.
  intros.
  assert (J1:=@phinodes_placement_wf_insn_base b b' Heqb' instr).
  assert (J2:=phinodes_placement_wf_value).
  assert (J3:=@phinodes_placement_preserves_wf_typ).
  inv HwfI; uniq_result; try solve [
    econstructor; eauto 3
  ].
Qed.

Lemma phinodes_placement_wf_cast : forall b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) instr
  (HwfI : wf_cast [M] M (PI_f pinfo) b instr),
  wf_cast [M'] M' f' b' instr.
Proof.
  intros.
  assert (J1:=@phinodes_placement_wf_insn_base b b' Heqb' instr).
  assert (J2:=phinodes_placement_wf_value).
  assert (J3:=@phinodes_placement_preserves_wf_typ).
  inv HwfI; uniq_result; try solve [
    econstructor; eauto 3
  ].
Qed.

Lemma phinodes_placement_wf_phi_operands : forall b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) id0 t0 vls0
  (Hwfps: wf_phi_operands (PI_f pinfo) b id0 t0 vls0),
  wf_phi_operands f' b' id0 t0 vls0.
Proof.
  intros. subst.
  apply wf_phi_operands__intro.
  intros.
  eapply wf_phi_operands__elim' in Hwfps; eauto.
  fold_PhiPlacement_tac.
  rewrite <- TransCFG.pres_getArgsIDsOfFdef.
  destruct Hwfps as [b1 [J1 Hwfps]].
  exists (phinodes_placement_blk pinfo b1).
  fold_PhiPlacement_tac.
  rewrite <- TransCFG.pres_isReachableFromEntry.
  split.
    apply TransCFG.pres_lookupBlockViaLabelFromFdef; auto.

    destruct Hwfps as [[[b0 [J2 Hwfps]] | J3] | J3]; auto.
    left. left.
    exists (phinodes_placement_blk pinfo b0).
    split.
      simpl.
      apply phinodes_placement_lookupBlockViaIDFromFdef; auto.

      fold_PhiPlacement_tac.
      rewrite <- TransCFG.pres_blockDominates; auto.
Qed.

Lemma phinodes_placement_wf_phinode : forall b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) pnode
  (HwfI : wf_phinode (PI_f pinfo) b pnode),
  wf_phinode f' b' pnode.
Proof.
  unfold wf_phinode.
  intros.
  destruct pnode as [id0 t0 vls0].
  destruct HwfI as [J1 J2].
  eapply phinodes_placement_wf_phi_operands in J1; eauto.
  split; auto.
    subst. fold_PhiPlacement_tac.
    apply TransCFG.pres_check_list_value_l; auto.
Qed.

Lemma phinodes_placement_wf_insn : forall b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) instr
  (HwfI : wf_insn [M] M (PI_f pinfo) b instr),
  wf_insn [M'] M' f' b' instr.
Proof.
  intros.
  assert (J1:=@phinodes_placement_wf_insn_base b b' Heqb' instr).
  assert (J2:=phinodes_placement_wf_value).
  assert (J3:=@phinodes_placement_preserves_wf_typ).
  assert (J4:=@phinodes_placement_preserves_wf_const).
  assert (J5:=@phinodes_placement_wf_trunc b b' Heqb' instr).
  assert (J6:=@phinodes_placement_wf_ext b b' Heqb' instr).
  assert (J7:=@phinodes_placement_wf_cast b b' Heqb' instr).
  assert (J8:=@phinodes_placement_wf_phinode b b' Heqb').

Ltac phinodes_placement_wf_insn_tac :=
repeat match goal with
| H1 : lookupBlockViaLabelFromFdef (PI_f pinfo) _ = ret _ |- _ =>
  apply (@TransCFG.pres_lookupBlockViaLabelFromFdef (PhiPlacement pinfo)) in H1
| H1 : context [Function.getDefReturnType (PI_f pinfo)] |- _ =>
  rewrite <- (@TransCFG.pres_getDefReturnType (PhiPlacement pinfo)) in H1
| |- context [Function.getDefReturnType (PI_f pinfo)] =>
  rewrite <- (@TransCFG.pres_getDefReturnType (PhiPlacement pinfo))
| H1 : insnInFdefBlockB _ (PI_f pinfo) _ = true |- _ =>
  apply phinodes_placement_insnInFdefBlockB in H1
end.

  inv HwfI; uniq_result; try solve [
    phinodes_placement_wf_insn_tac;
    econstructor; eauto 3
  ].

Qed.

Lemma phinodes_placement_wf_cmds : forall b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) cs 
  (Hwfcs : wf_cmds [M] M (PI_f pinfo) b cs),
  wf_cmds [M'] M' f' b' cs.
Proof.
  intros.
  induction cs; intros.
    constructor.

    inversion Hwfcs.
    econstructor; eauto using phinodes_placement_wf_insn.
Qed.

Lemma phinodes_placement_wf_phinodes : forall b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) ps
  (Hwfps : wf_phinodes [M] M (PI_f pinfo) b ps),
  wf_phinodes [M'] M' f' b' ps.
Proof.
  intros.
  induction ps; intros.
    constructor.

    inversion Hwfps.
    econstructor; eauto using phinodes_placement_wf_insn.
Qed.

Lemma inserted_load__in__phinodes_placement_blk: forall b lid pid sid scs
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR2 : ret scs = (PI_succs pinfo) ! (getBlockLabel b))
  (Hnonempty: scs <> nil) (Hin: blockInFdefB b (PI_f pinfo) = true),
  insnInFdefBlockB
     (insn_cmd
        (insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo))
           (PI_align pinfo))) (phinodes_placement_f pinfo (PI_f pinfo))
     (phinodes_placement_blk pinfo b) = true.
Proof.
  intros.
  eapply phinodes_placement_blk_tail_inv in HeqR1; eauto 1.
  destruct HeqR1 as [l0 [ps0 [cs0 [tmn0 [ps1 [cs1 [EQ1 EQ2]]]]]]]; subst.
  apply insnInFdefBlockB_intro.
    rewrite EQ2.
    simpl. apply In_InCmdsB. xsolve_in_list.
  
    fold_PhiPlacement_tac.
    apply TransCFG.pres_blockInFdefB; auto.
Qed.

Lemma phinodes_placement_blk_rev_eq: forall (pinfo : PhiInfo) (b : block)
  (Huniq : uniqFdef (PI_f pinfo))
  (Hin : blockInFdefB b (PI_f pinfo) = true) (be : block)
  (Hentry : getEntryBlock (PI_f pinfo) = ret be)
  (e : getBlockLabel (phinodes_placement_blk pinfo be) =
       getBlockLabel (phinodes_placement_blk pinfo b)),
  be = b.
Proof.
  intros.
  rewrite <- phinodes_placement_blk__getBlockLabel in e.
  rewrite <- phinodes_placement_blk__getBlockLabel in e.
  apply entryBlockInFdef in Hentry.
  destruct b. destruct be.        
  simpl in e. subst l0.
  eapply blockInFdefB_uniq in Hin; eauto.
  f_equal; tauto.
Qed.

Lemma wf_operand_pid__in__inserted_load: forall b lid pid sid scs
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR2 : ret scs = (PI_succs pinfo) ! (getBlockLabel b))
  (Hnonempty: scs <> nil) (Huniq: uniqFdef (PI_f pinfo))
  (Hin: blockInFdefB b (PI_f pinfo) = true),
  wf_operand (phinodes_placement_f pinfo (PI_f pinfo))
     (phinodes_placement_blk pinfo b)
     (insn_cmd
        (insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo))
           (PI_align pinfo))) (PI_id pinfo).
Proof.
  intros.
  econstructor; simpl; eauto 2; simpl; auto.
    eapply inserted_load__in__phinodes_placement_blk; eauto.
    solve_isNotPhiNode.

    left. 
    destruct (isReachableFromEntry_dec
                (phinodes_placement_f pinfo (PI_f pinfo))
                (phinodes_placement_blk pinfo b)); auto.
    left.
    assert (J:=Hwfpi).
    apply WF_PhiInfo__lookupBlockViaIDFromFdef in J; auto.
    destruct J as [be [Hentry Hlkup]]. 
    apply phinodes_placement_lookupBlockViaIDFromFdef in Hlkup; auto.
    exists (phinodes_placement_blk pinfo be).
    split; auto.

    destruct (eq_atom_dec (getBlockLabel (phinodes_placement_blk pinfo be))
                          (getBlockLabel (phinodes_placement_blk pinfo b))).
    Case "be = b".
      left.
      assert (be = b) as EQ.
        eapply phinodes_placement_blk_rev_eq; eauto.
      subst.
      assert (J:=Hwfpi).
      apply WF_PhiInfo_spec22 in J; auto.
      destruct J as [l0 [ps0 [cs1 [cs3 [tmn0 Hentry']]]]].
      uniq_result.
      eapply phinodes_placement_blk_tail_inv in HeqR1; eauto 1.
      destruct HeqR1 as [l1 [ps1 [cs4 [tmn1 [ps5 [cs5 [EQ1 EQ2]]]]]]].
      uniq_result.
      rewrite EQ2. clear EQ2.
      simpl. right.
      simpl_env.
      match goal with
      | |- context [?A ++ ?B ++ [?c] ++ ?D ++ [?e] = _ ] =>
        exists (A++B); exists c; exists D; exists nil; simpl_env; split; auto
      end.

    Case "be <> b".
      right.
      fold_PhiPlacement_tac.
      erewrite <- TransCFG.pres_blockStrictDominates; eauto.
      assert (isReachableFromEntry (PI_f pinfo) b) as Hreach.
        erewrite (@TransCFG.pres_isReachableFromEntry (PhiPlacement pinfo)); 
          eauto.
      rewrite <- phinodes_placement_blk__getBlockLabel in n.
      rewrite <- phinodes_placement_blk__getBlockLabel in n.
      eapply entry_blockStrictDominates_others; eauto.
Qed.

Lemma inserted_store__in__phinodes_placement_blk: forall b lid pid sid pds
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR3 : ret pds = (PI_preds pinfo) ! (getBlockLabel b))
  (Hneq : pds <> nil) (Hin: blockInFdefB b (PI_f pinfo) = true),
  insnInFdefBlockB
     (insn_cmd
        (insn_store sid (PI_typ pinfo) (value_id pid)
           (value_id (PI_id pinfo)) (PI_align pinfo)))
     (phinodes_placement_f pinfo (PI_f pinfo))
     (phinodes_placement_blk pinfo b) = true.
Proof.
  intros.
  eapply phinodes_placement_blk_head_inv in HeqR1; eauto 1.
  destruct HeqR1 as [l0 [ps0 [cs0 [tmn0 [cs2 [EQ1 EQ2]]]]]]; subst.
  apply insnInFdefBlockB_intro.
    rewrite EQ2.
    simpl.
    apply orb_true_intro. left. solve_refl.
  
    fold_PhiPlacement_tac.
    apply TransCFG.pres_blockInFdefB; auto.
Qed.

Lemma insert_phi__lookupBlockViaIDFromFdef: forall b lid pid sid pds
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR3 : ret pds = (PI_preds pinfo) ! (getBlockLabel b))
  (Hneq : pds <> nil) (Hin: blockInFdefB b (PI_f pinfo) = true),
  lookupBlockViaIDFromFdef (phinodes_placement_f pinfo (PI_f pinfo)) pid =
    ret (phinodes_placement_blk pinfo b).
Proof.
  intros.
  eapply phinodes_placement_blk_head_inv in HeqR1; eauto 1.
  destruct HeqR1 as [l0 [ps0 [cs0 [tmn0 [cs2 [EQ1 EQ2]]]]]]; subst.
  rewrite EQ2.
  eapply inGetBlockIDs__lookupBlockViaIDFromFdef; eauto 1.
    rewrite <- phinodes_placement_f_spec1.
    apply phinodes_placement__uniqFdef; auto.

    simpl. auto.
  
    rewrite <- EQ2.
    fold_PhiPlacement_tac.
    apply TransCFG.pres_blockInFdefB; auto.
Qed.

Lemma inserted_phi__wf_value: forall b lid pid sid pds
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR3 : ret pds = (PI_preds pinfo) ! (getBlockLabel b))
  (Hneq : pds <> nil) (HBinF: blockInFdefB b (PI_f pinfo) = true),
  wf_value [M'] M' f' (value_id pid) (PI_typ pinfo).
Proof.
  intros. 
  assert (Hwft:=wf_PI_typ').
  subst.
  constructor; auto.
    eapply phinodes_placement_blk_head_inv in HeqR1; eauto.
    destruct HeqR1 as [l0 [ps0 [cs0 [tmn0 [cs2 [J3 J4]]]]]]; subst.
    match goal with
    | J4: _ = block_intro ?l0 ([?p0]++?ps0) ?cs2 ?tmn |- _ =>
    apply uniqF__lookupPhiNodeTypViaIDFromFdef with (l1:=l0)
      (ps1:=[p0]++ps0) (cs1:=cs2)(tmn1:=tmn)(p:=p0); auto
    end.
      rewrite <- phinodes_placement_f_spec1.
      apply phinodes_placement__uniqFdef; auto.
  
      rewrite <- J4. 
      fold_PhiPlacement_tac.
      apply TransCFG.pres_blockInFdefB; auto.
  
      xsolve_in_list.
Qed.

Lemma wf_operand_phi__in__inserted_store: forall b lid pid sid pds
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR3 : ret pds = (PI_preds pinfo) ! (getBlockLabel b))
  (Hneq : pds <> nil) (Hin: blockInFdefB b (PI_f pinfo) = true),
   wf_operand (phinodes_placement_f pinfo (PI_f pinfo))
     (phinodes_placement_blk pinfo b)
     (insn_cmd
        (insn_store sid (PI_typ pinfo) (value_id pid)
           (value_id (PI_id pinfo)) (PI_align pinfo))) pid.
Proof.
  intros.
  econstructor; simpl; eauto 2; simpl; auto.
    eapply inserted_store__in__phinodes_placement_blk; eauto.
    solve_isNotPhiNode.

    left. 
    destruct (isReachableFromEntry_dec
                  (phinodes_placement_f pinfo (PI_f pinfo))
                  (phinodes_placement_blk pinfo b)); auto.
    left.
    exists (phinodes_placement_blk pinfo b).
    split.
      eapply insert_phi__lookupBlockViaIDFromFdef; eauto.
   
      left.
      eapply phinodes_placement_blk_head_inv in HeqR1; eauto 1.
      destruct HeqR1 as [l1 [ps1 [cs4 [tmn1 [cs5 [EQ1 EQ2]]]]]].
      subst.
      rewrite EQ2.
      simpl.
      left.
      match goal with
      | |- context [?a :: ?B] => 
           exists nil; exists a; exists B; simpl_env; split; auto
      end.
Qed.

Lemma wf_operand_pid__in__inserted_store: forall b lid pid sid pds
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR3 : ret pds = (PI_preds pinfo) ! (getBlockLabel b))
  (Hneq : pds <> nil) (Hin: blockInFdefB b (PI_f pinfo) = true),
  wf_operand (phinodes_placement_f pinfo (PI_f pinfo))
     (phinodes_placement_blk pinfo b)
     (insn_cmd
        (insn_store sid (PI_typ pinfo) (value_id pid)
           (value_id (PI_id pinfo)) (PI_align pinfo))) (PI_id pinfo).
Proof.
  intros.
  econstructor; simpl; eauto 2; simpl; auto.
    eapply inserted_store__in__phinodes_placement_blk; eauto.
    solve_isNotPhiNode.

    left. 
    destruct (isReachableFromEntry_dec
                (phinodes_placement_f pinfo (PI_f pinfo))
                (phinodes_placement_blk pinfo b)); auto.
    left.
    assert (J:=Hwfpi).
    apply WF_PhiInfo__lookupBlockViaIDFromFdef in J; auto.
    destruct J as [be [Hentry Hlkup]]. 
    apply phinodes_placement_lookupBlockViaIDFromFdef in Hlkup; auto.
    exists (phinodes_placement_blk pinfo be).
    split; auto.
    destruct (eq_atom_dec (getBlockLabel (phinodes_placement_blk pinfo be))
                          (getBlockLabel (phinodes_placement_blk pinfo b))).
    Case "be = b".
      left.
      assert (be = b) as EQ.
        eapply phinodes_placement_blk_rev_eq; eauto.
      subst.
      assert (J:=Hwfpi).
      apply WF_PhiInfo_spec22 in J; auto.
      destruct J as [l0 [ps0 [cs1 [cs3 [tmn0 Hentry']]]]].
      uniq_result. simpl in HeqR3.
      assert (forall pd pds, (PI_preds pinfo) ! l0 <> Some (pd::pds)) as Hprds.
        intros.
        eapply PI_preds_of_entry_cannot_be_nonempty in Hentry; eauto 1.
      rewrite <- HeqR3 in Hprds.
      destruct pds; congruence.

    Case "be <> b".
      right. 
      fold_PhiPlacement_tac.
      erewrite <- TransCFG.pres_blockStrictDominates; eauto.
      assert (isReachableFromEntry (PI_f pinfo) b) as Hreach.
        erewrite (@TransCFG.pres_isReachableFromEntry (PhiPlacement pinfo)); 
          eauto.
      rewrite <- phinodes_placement_blk__getBlockLabel in n.
      rewrite <- phinodes_placement_blk__getBlockLabel in n.
      eapply entry_blockStrictDominates_others; eauto.
Qed.

Lemma inserted_phi__in__phinodes_placement_blk: forall b lid pid sid pds
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR3 : ret pds = (PI_preds pinfo) ! (getBlockLabel b))
  (Hneq : pds <> nil) (Hin: blockInFdefB b (PI_f pinfo) = true),
  insnInFdefBlockB
     (insn_phinode (gen_phinode pid (PI_typ pinfo) (PI_newids pinfo) pds))
     (phinodes_placement_f pinfo (PI_f pinfo))
     (phinodes_placement_blk pinfo b) = true.
Proof.
  intros.
  eapply phinodes_placement_blk_head_inv in HeqR1; eauto 1.
  destruct HeqR1 as [l0 [ps0 [cs0 [tmn0 [cs2 [EQ1 EQ2]]]]]]; subst.
  apply insnInFdefBlockB_intro.
    rewrite EQ2.
    simpl.
    apply orb_true_intro. left. solve_refl.
  
    fold_PhiPlacement_tac.
    apply TransCFG.pres_blockInFdefB; auto.
Qed.

Lemma WF_PhiInfo_br_preds_succs': forall (pinfo : PhiInfo) 
  (Hwfpi : WF_PhiInfo pinfo) (HuniqF : uniqFdef (PI_f pinfo)) (pds : list l)
  (b : block) (HeqR3 : ret pds = (PI_preds pinfo) ! (getBlockLabel b))
  (l0 : l) (Hin : In l0 pds) (b1 : block)
  (Hlkup : lookupBlockViaLabelFromFdef (PI_f pinfo) l0 = ret b1),
  l0 = getBlockLabel b1 /\
  exists succs,
    succs <> nil /\ ret succs = (PI_succs pinfo) ! (getBlockLabel b1).
Proof.
  intros.
  symmetry in HeqR3.
  eapply WF_PhiInfo_br_preds_succs in HeqR3; eauto.
  destruct HeqR3 as [succs [J1 J2]].
  assert (succs <> nil) as Hneq'.
    destruct succs; tinv J2. congruence.
  symmetry in J1.
  assert (l0 = getBlockLabel b1) as EQ.
    destruct b1.
    apply lookupBlockViaLabelFromFdef_inv in Hlkup; auto.
    destruct Hlkup; subst. auto.
  subst.
  eauto.
Qed.

Lemma snd_split_gen_phinode_incoming_aux: forall 
  (nids: ATree.t (id * id * id)) pds acc,
  snd (split (fold_left (fun (acc : list (value * atom)) (p : atom) =>
             (match nids ! p with
              | ret (lid0, _, _) => value_id lid0
              | merror => value_const (const_undef (PI_typ pinfo))
              end, p) :: acc) pds acc)) = (rev pds) ++ snd (split acc).
Proof.
  intros.
  repeat rewrite snd_split__map_snd.
  generalize dependent acc.
  induction pds as [|p]; simpl; intros; auto.
    rewrite IHpds.
    destruct (nids ! p) as [[[]]|]; simpl; simpl_env; auto.
Qed.

Lemma snd_split_gen_phinode_incoming: forall (nids: ATree.t (id * id * id)) pds,
  snd (split (fold_left (fun (acc : list (value * atom)) (p : atom) =>
             (match nids ! p with
              | ret (lid0, _, _) => value_id lid0
              | merror => value_const (const_undef (PI_typ pinfo))
              end, p) :: acc) pds nil)) = rev pds.
Proof.
  intros.
  rewrite snd_split_gen_phinode_incoming_aux. 
  simpl. simpl_env. auto.
Qed.

Lemma wf_inserted_phi: forall b lid pid sid pds
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR3 : ret pds = (PI_preds pinfo) ! (getBlockLabel b)) (Hneq : pds <> nil),
  wf_phinode (phinodes_placement_f pinfo (PI_f pinfo))
    (phinodes_placement_blk pinfo b)
    (gen_phinode pid (PI_typ pinfo) (PI_newids pinfo) pds).
Proof.
  intros.
  constructor.
  Case "1".
    apply wf_phi_operands__intro.
    intros.
    apply inserted_phi_operands__elim in Hin.
    destruct Hin as [Hin [pid' [sid' Hnids]]].
    assert ((PI_newids pinfo) ! l1 <> merror) as G. congruence.
    apply PI_newids_are_in_PI_rd in G; auto.
    apply PI_rd__lookupBlockViaLabelFromFdef in G; auto.
    destruct G as [b1 Hlkup].
    assert (Hlkup':=Hlkup).
    apply (@TransCFG.pres_lookupBlockViaLabelFromFdef (PhiPlacement pinfo)) 
      in Hlkup'.
    fold_PhiPlacement_tac.
    exists (btrans (PhiPlacement pinfo) b1).
    split; auto.
    left. left.
    exists (btrans (PhiPlacement pinfo) b1).
    split.
    SCase "1.1".
      apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
      SSCase "1.1.2".
        simpl. 
        rewrite <- phinodes_placement_f_spec1.
        apply phinodes_placement__uniqFdef; auto.

      SSCase "1.1.3".
        eapply WF_PhiInfo_br_preds_succs' in HeqR3; eauto.
        destruct HeqR3 as [EQ [succs [Hneq' J2]]]; subst.
        symmetry in Hnids.
        eapply phinodes_placement_blk_tail_inv in Hnids; eauto.
        destruct Hnids as [l0 [ps0 [cs0 [tmn0 [ps2 [cs2 [J3 J4]]]]]]]; subst.
        simpl in *. rewrite J4.
        simpl. repeat rewrite getCmdsIDs_app. simpl. 
        xsolve_in_list.

      SSCase "1.1.4".
        apply TransCFG.pres_blockInFdefB; auto.
        solve_blockInFdefB.

    SCase "1.2".
      apply blockDominates_refl.

  Case "2".
   fold_PhiPlacement_tac.
   unfold check_list_value_l.
   rewrite <- TransCFG.pres_predecessors_of_block.
   assert (J:=snd_split_gen_phinode_incoming (PI_newids pinfo) pds).
   unfold l in *.
   remember (split (fold_left
              (fun (acc : list (value * atom)) (p : atom) =>
               (match (PI_newids pinfo) ! p with
                | ret (lid0, _, _) => value_id lid0
                | merror => value_const (const_undef (PI_typ pinfo))
                end, p) :: acc) pds nil)) as R.
   destruct R. simpl in J. subst. 
   unfold successors_list.
   unfold predecessors.
   unfold PI_preds, PI_succs in HeqR3.
   rewrite <- HeqR3.
   split.
     destruct pds; try solve [ simpl; omega | congruence].
   split.
     apply AtomSet.set_eq_rev.
   
     apply NoDup_rev.
     eapply predecessors_dom__uniq; eauto.
Qed.

Lemma inserted_load__lookupTypViaIDFromFdef: forall (pds : list l) b
  (HeqR3 : ret pds = (PI_preds pinfo) ! (getBlockLabel b))
  (vid1 : id) (l0 : l) (Hin : In l0 pds) (pid' : id) (sid' : id)
  (J : (PI_newids pinfo) ! l0 = ret (vid1, pid', sid')),
  lookupTypViaIDFromFdef (phinodes_placement_f pinfo (PI_f pinfo)) vid1 =
    ret PI_typ pinfo.
Proof.
  intros.
  assert ((PI_newids pinfo) ! l0 <> merror) as G. congruence.
  apply PI_newids_are_in_PI_rd in G; auto.
  apply PI_rd__lookupBlockViaLabelFromFdef in G; auto.
  destruct G as [b1 Hlkup].
  
  eapply WF_PhiInfo_br_preds_succs' in HeqR3; eauto.
  destruct HeqR3 as [EQ [succs [Hneq' J1]]]; subst.
  eapply phinodes_placement_blk_tail_inv in J1; eauto.
  destruct J1 as [l0 [ps0 [cs0 [tmn0 [ps2 [cs2 [J3 J4]]]]]]]; subst.
  
  match goal with
  | J4: _ = block_intro ?l0 ?ps0 (?cs2 ++ ?cs3 ++ [?c0]) ?tmn |- _ =>
    apply uniqF__lookupTypViaIDFromFdef with (l1:=l0)(ps1:=ps0)
      (cs1:=cs2 ++ cs3 ++ [c0])(tmn1:=tmn)(c:=c0); auto
  end.
    rewrite <- phinodes_placement_f_spec1.
    apply phinodes_placement__uniqFdef; auto.
  
    rewrite <- J4. 
    fold_PhiPlacement_tac.
    apply TransCFG.pres_blockInFdefB; auto.
    simpl in Hlkup.
    solve_blockInFdefB.
  
    xsolve_in_list.
Qed.

Lemma inserted_incoming_value__wf_value: forall b lid pid sid pds
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR3 : ret pds = (PI_preds pinfo) ! (getBlockLabel b)),
  forall value_ : value,
  In value_
     (List.map (fun pat_ : value * l => let (value_0, _) := pat_ in value_0)
        (fold_left
           (fun (acc : list (value * atom)) (p : atom) =>
            (match (PI_newids pinfo) ! p with
             | ret (lid0, _, _) => value_id lid0
             | merror => value_const (const_undef (PI_typ pinfo))
             end, p) :: acc) pds nil)) ->
  wf_value [M'] M' f' value_ (PI_typ pinfo).
Proof.
  intros.
  apply in_map_fst__in_map in H.
  destruct H as [l0 Hin].
  apply inserted_phi_operands__elim in Hin.
  destruct Hin as [Hin J].
  assert (wf_typ [M'] (los, nts) (PI_typ pinfo)) as Hwft.
    apply wf_PI_typ'.
  destruct value_ as [vid1 | vc1].
    destruct J as [pid' [sid' J]].
    subst.
    constructor; auto.
      eapply inserted_load__lookupTypViaIDFromFdef; eauto.

    subst.
    constructor; auto.
      constructor; auto.
Qed.

Lemma wf_inserted: forall b b' (Hwfl: wf_layouts los)
  (Heqb': b' = phinodes_placement_blk pinfo b)
  (HBinF: blockInFdefB b (PI_f pinfo) = true),
  match (PI_newids pinfo) ! (getBlockLabel b) with
  | Some (lid, pid, sid) =>
      match (PI_succs pinfo) ! (getBlockLabel b) with
      | Some (_::_) =>
          wf_insn [M'] M' f' b' 
            (insn_cmd (insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo))
                                 (PI_align pinfo)))
      | _ => True
      end /\
      match (PI_preds pinfo) ! (getBlockLabel b) with
      | Some ((_::_) as pds) =>
         wf_insn [M'] M' f' b' 
           (insn_cmd (insn_store sid (PI_typ pinfo) (value_id pid)
                        (value_id (PI_id pinfo)) (PI_align pinfo))) /\
         wf_phinodes [M'] M' f' b' 
            [gen_phinode pid (PI_typ pinfo) (PI_newids pinfo) pds]
      | _ => True
      end
  | _ => True
  end.
Proof.
  intros. 
  assert (wf_value [M'] M' f' (value_id (PI_id pinfo)) 
            (typ_pointer (PI_typ pinfo))) as Hwfv.
    eapply phinodes_placement_wf_value; eauto.
      subst. apply WF_PhiInfo__wf_value; auto.
  assert (wf_typ [M'] (los,nts) (PI_typ pinfo)) as Hwft.
    apply wf_PI_typ'.
  remember ((PI_newids pinfo) ! (getBlockLabel b)) as R1.
  remember ((PI_succs pinfo) ! (getBlockLabel b)) as R2.
  remember ((PI_preds pinfo) ! (getBlockLabel b)) as R3.
  destruct R1 as [[[lid pid] sid]|]; auto.
  split.
    destruct R2 as [[]|]; auto.
    assert (l0 :: l1 <> nil) as Hneq. congruence.
    subst.
    constructor; auto.
      eapply wf_insn_base_intro; eauto 1.
        eapply inserted_load__in__phinodes_placement_blk; eauto.

        simpl. intros id_ Hin.
        destruct Hin as [Hin | Hin]; subst; try tauto.
        eapply wf_operand_pid__in__inserted_load; eauto. 

    destruct R3 as [[]|]; auto.
    assert (l0 :: l1 <> nil) as Hneq. congruence.
    split.
      assert (wf_value [M'] M' f' (value_id pid) (PI_typ pinfo)) as Hwfphi.
        eapply inserted_phi__wf_value; eauto.
      subst.
      constructor; auto.
        eapply wf_insn_base_intro; eauto 1.
          eapply inserted_store__in__phinodes_placement_blk; eauto. 

          simpl. intros id_ Hin.
          destruct Hin as [Hin | [Hin | Hin]]; subst; try tauto.
            eapply wf_operand_phi__in__inserted_store; eauto. 
            eapply wf_operand_pid__in__inserted_store; eauto. 

      assert (J:=@inserted_incoming_value__wf_value b lid pid sid (l0::l1)
        HeqR1 HeqR3).
      subst.
      constructor; try constructor.
        auto.
        eapply inserted_phi__in__phinodes_placement_blk; eauto. 
        eapply wf_inserted_phi; eauto. 
Qed.

Lemma phinodes_placement_blockInSystemModuleFdefB: forall b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b)
  (Hin: blockInSystemModuleFdefB b [M] M (PI_f pinfo)),
  blockInSystemModuleFdefB b' [M'] M' f'.
Proof.
  intros.
  subst.
  apply blockInSystemModuleFdef_inv in Hin.
  destruct Hin as [J1 [J2 [J3 J4]]].
  apply blockInSystemModuleFdef_intro.
    fold_PhiPlacement_tac.
    apply TransCFG.pres_blockInFdefB; auto.

    apply InProductsB_middle.

    unfold moduleInSystem. simpl.
    apply orb_true_intro.
    left. solve_refl.
Qed.

Lemma phinodes_placement_wf_block : forall b (Hwfl: wf_layouts los)
  (HwfB : wf_block [M] M (PI_f pinfo) b) (Huniq : NoDup (getBlockLocs b))
  (HBinF: blockInFdefB b (PI_f pinfo) = true),
  wf_block [M'] M' f' (phinodes_placement_blk pinfo b).
Proof.

Ltac phinodes_placement_wf_block_tac1 :=
  match goal with
  | |- wf_cmds _ _ _ _ (_++_) =>
       apply wf_cmds_app; try solve [auto | phinodes_placement_wf_block_tac1]
  | |- wf_cmds _ _ _ _ [_] =>
       apply wf_cmds_cons; try solve [tauto | constructor]
  | |- wf_phinodes _ _ _ _ (_++_) =>
       apply wf_phinodes_app; try solve [auto | phinodes_placement_wf_block_tac1]
  | |- wf_phinodes _ _ _ _ [_] =>
       tauto
  end.

Ltac phinodes_placement_wf_block_tac2 :=
  constructor; try solve [auto | phinodes_placement_wf_block_tac1].

  intros.
  assert (HwfNew:=HBinF).
  eapply wf_inserted in HwfNew; eauto.
  inv_wf_block HwfB. 

  eapply phinodes_placement_blockInSystemModuleFdefB in HBinSMF; eauto.
  eapply phinodes_placement_wf_cmds in Hwfcs; eauto.
  eapply phinodes_placement_wf_phinodes in Hwfps; eauto.
  eapply phinodes_placement_wf_insn in Hwfi; eauto.
  unfold phinodes_placement_blk, phinodes_placement_block in *.
  subst b. simpl in HwfNew.
  remember (PI_newids pinfo) ! l5 as R1.
  destruct R1 as [[[lid pid] sid]|]; try solve [constructor; auto].
  remember ((PI_preds pinfo) ! l5) as R2.
  remember ((PI_succs pinfo) ! l5) as R3.
  destruct R2 as [[]|];
    destruct R3 as [[]|]; 
      try solve [simpl_env in *; phinodes_placement_wf_block_tac2].
Qed.

Lemma phinodes_placement_wf_blocks : forall (Hwfl: wf_layouts los) bs 
  (Hin: forall b, In b bs -> blockInFdefB b (PI_f pinfo) = true)
  (HwfBs : wf_blocks [M] M (PI_f pinfo) bs) (Huniq : NoDup (getBlocksLocs bs)),
  wf_blocks [M'] M' f' (List.map (phinodes_placement_blk pinfo) bs).
Proof.
  intros. 
  induction bs; simpl.
    constructor.

    simpl in Huniq.
    split_NoDup. inversion HwfBs.
    constructor; auto.
      eapply phinodes_placement_wf_block; eauto 1.
        apply Hin; simpl; auto.
      apply IHbs; auto.
        intros b Hin'. apply Hin. simpl; auto.
Qed.

Lemma phinodes_placement_preserves_wf_fheader: forall fh,
  wf_fheader [M] (los,nts) fh -> wf_fheader [M'] (los,nts) fh.
Proof.
  assert (J:=Heq_fheader).
  eapply TopWFS.subst_fdef_preserves_single_wf_fheader; eauto.
Qed.

Lemma phinodes_placement_wf_fdef: forall (Hwfl: wf_layouts los),
  wf_fdef [M'] M' (phinodes_placement_f pinfo (PI_f pinfo)).
Proof.
  intros. assert (HwfF':=HwfF).
  assert (G:=phinodes_placement_preserves_wf_fheader).
  inv_wf_fdef HwfF'.
  match goal with
  | Hentry : getEntryBlock _ = _,
    Hnpred : has_no_predecessors _ _ = _,
    Hsuccess: dom_analysis_is_successful _ |- _ =>
     eapply (@TransCFG.pres_getEntryBlock (PhiPlacement pinfo)) 
       in Hentry; eauto;
     erewrite (@TransCFG.pres_has_no_predecessors (PhiPlacement pinfo)) 
       in Hnpred;
     eapply (@TransCFG.pres_dom_analysis_is_successful (PhiPlacement pinfo)) 
       in Hsuccess; eauto
  end.
  rewrite EQ2 in Hwfb.
  match goal with
  | H2: fdef_intro _ _ = PI_f _,
    H9: wf_blocks _ _ _ _ |- _ =>
    rewrite H2 in H9;
    eapply phinodes_placement_wf_blocks in H9; try solve [
      eauto |
      rewrite <- H2 in HuniqF; eapply uniqF__uniqBlocksLocs; eauto |
      rewrite <- H2; simpl; intros; apply In_InBlocksB; auto
    ]
  end.

  subst. uniq_result. rewrite <- EQ3.
  eapply wf_fdef_intro; eauto 2.
    clear. 
    apply productInSystemModuleB_intro.
      simpl. unfold is_true. apply InProductsB_middle.

      unfold moduleInSystem. simpl. apply orb_true_intro. 
      left. apply moduleEqB_refl.

    rewrite EQ3. auto.

    match goal with
    | H2: fdef_intro _ _ = PI_f _, H9: wf_blocks _ _ _ _ |- _ =>
      rewrite <- H2 in H9; auto
    end.
Qed.
    
End PresWF.

Lemma phinodes_placement_wfS: forall rd f Ps1 Ps2 los nts pid ty al
  num l0 ps0 cs0 tmn0 dones (Hreach: ret rd = reachablity_analysis f)
  (Hentry: getEntryBlock f = Some (block_intro l0 ps0 cs0 tmn0))
  (Hfind: find_promotable_alloca f cs0 dones = Some (pid, ty, num, al))
  (HwfS :
     wf_system 
       [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  wf_system 
    [module_intro los nts
      (Ps1 ++
       product_fdef (phinodes_placement rd pid ty al (successors f)
                    (make_predecessors (successors f)) f) :: Ps2)].
Proof.
  intros.
  assert (Hwfl: wf_layouts los).
    eapply wf_system__wf_layouts in HwfS; simpl; eauto.
  eapply find_promotable_alloca__WF_PhiInfo in Hfind; eauto.
  eapply TopWFS.trans_wfS with (f:=f) in HwfS; intros;
    eauto using phinodes_placement_fheaderOfFdef.
    match goal with
    | _: WF_PhiInfo ?pinfo0 |- _ =>
      eapply phinodes_placement_wf_fdef with (pinfo:=pinfo0) in HwfF; eauto
    end.
       rewrite <- phinodes_placement_f_spec1 in HwfF; auto.

       apply wf_single_system__wf_uniq_fdef in HwfS.
       destruct HwfS; auto.

    eapply phinodes_placement__uniqFdef in Hfind; eauto.
Qed.

Lemma inserted_store_is_promotable: forall id5 pinfo acc lid pid sid l0
  (Hfresh: In id5 (getFdefLocs (PI_f pinfo)))
  (Hnids: ret (lid, pid, sid) = (PI_newids pinfo) ! l0),
  is_promotable_cmd id5 acc
    (insn_store sid (PI_typ pinfo) (value_id pid)
      (value_id (PI_id pinfo)) (PI_align pinfo)) = acc.
Proof.
  intros.
  unfold is_promotable_cmd.
  simpl.
  destruct (id_dec pid id5); subst; simpl.
    eapply PI_newids_arent_in_getFdefLocs in Hnids; eauto 3.
      tauto.

    destruct (id_dec (PI_id pinfo) id5); subst; simpl; auto.
    unfold valueEqB.
    destruct (value_dec (value_id pid) (value_id (PI_id pinfo))); 
      simpl; congruence.
Qed.

Lemma inserted_phi_is_promotable: forall pinfo id5 l0 pds pid
  (Hfresh: In id5 (getFdefLocs (PI_f pinfo)))
  (HeqR3 : ret pds = (PI_preds pinfo) ! l0),
  used_in_phi id5
    (gen_phinode pid (PI_typ pinfo) (PI_newids pinfo) pds) = false.
Proof.
  intros. simpl.
  apply used_in_list_value_l_false__intro.
  intros.
  apply inserted_phi_operands__elim in H.
  destruct H as [_ H].
  destruct v0; auto.
  destruct H as [pid' [sid H]].
  simpl.
  destruct (id_dec id0 id5); subst; auto.
  eapply PI_newids_arent_in_getFdefLocs in Hfresh; eauto 3.
    tauto.
Qed.

Lemma phinodes_placement_is_promotable_fun: forall pinfo b acc id5
  (Hfresh: In id5 (getFdefLocs (PI_f pinfo)))
  (Hin: blockInFdefB b (PI_f pinfo) = true),
  is_promotable_fun id5 acc b = 
    is_promotable_fun id5 acc (phinodes_placement_blk pinfo b).
Proof.
  unfold is_promotable_fun. intros.
  assert (J:=phinodes_placement_blk_inv' pinfo b).
  destruct J as [l0 [ps0 [cs0 [tmn0 [ps1 [cs1 [cs2 [EQ [J1 [J2 J3]]]]]]]]]]; 
    subst.
  rewrite J1. 
  destruct J2 as [[EQ1 EQ2]|[lid [pid [sid [J4 [pds [J5 [J6 [J7 J8]]]]]]]]]; 
    subst; simpl_env.
    destruct J3 as [EQ|[lid [pid [sid [J4 [scs [J5 [J6 J7]]]]]]]]; 
      subst; simpl_env; auto.

      destruct_if.
      rewrite List.fold_left_app.
      simpl. rewrite load_is_promotable; auto.

    eapply inserted_phi_is_promotable with (pid:=pid) in J7; eauto 1.
    simpl in J7. simpl. rewrite J7. 
    rewrite orb_false_r. 
    erewrite inserted_store_is_promotable; eauto 1.
    destruct J3 as [EQ|[lid' [pid' [sid' [J4' [scs [J5' [J6' J7']]]]]]]]; 
      subst; simpl_env; auto.

      repeat rewrite List.fold_left_app.
      simpl.
      rewrite load_is_promotable; auto.
Qed.

Lemma phinodes_placement_is_promotable_funs: forall id5 pinfo bs init
  (Hfresh: In id5 (getFdefLocs (PI_f pinfo)))
  (Hin: forall b, In b bs -> blockInFdefB b (PI_f pinfo) = true),
  fold_left (is_promotable_fun id5) bs init = 
     fold_left (is_promotable_fun id5)
       (List.map (phinodes_placement_blk pinfo) bs) init.
Proof.
  induction bs; auto.
    simpl. intros. subst.
    rewrite <- phinodes_placement_is_promotable_fun; auto.
Qed.

Lemma phinodes_placement_is_promotable: forall id5 pinfo
  (Hfresh: In id5 (getFdefLocs (PI_f pinfo))),
  is_promotable (PI_f pinfo) id5 = 
  is_promotable (phinodes_placement_f pinfo (PI_f pinfo)) id5.
Proof.
  unfold is_promotable. 
  intros.
  remember (PI_f pinfo) as f.
  destruct f as [fh bs].
  rewrite phinodes_placement_f_spec2.
  rewrite Heqf in Hfresh.
  rewrite <- phinodes_placement_is_promotable_funs; auto.
  rewrite <- Heqf. simpl. intros. apply In_InBlocksB; auto.
Qed.

Lemma phinodes_placement_find_promotable_alloca: forall pinfo dones cs
  (Hin: forall c, In c cs -> exists b, cmdInFdefBlockB c (PI_f pinfo) b),
  find_promotable_alloca (PI_f pinfo) cs dones = 
    find_promotable_alloca (phinodes_placement_f pinfo (PI_f pinfo)) cs dones.
Proof.
  induction cs as [|[]]; simpl; intros; auto.
    rewrite <- IHcs; auto.
    rewrite <- phinodes_placement_is_promotable; auto.
    match goal with
    | Hin:context [insn_alloca ?id5 ?ty5 ?val5 ?al5 = _ \/ In _ ?cs] |- _ =>
      assert (exists b, cmdInFdefBlockB 
                (insn_alloca id5 ty5 val5 al5) (PI_f pinfo) b) as J;
        try solve [apply Hin; auto];
      destruct J as [[l0 ps0 cs0 tmn0] J]
    end.
    apply andb_true_iff in J.
    destruct J as [J1 J2].
    simpl in J1.
    apply InCmdsB_in in J1.
    apply in_split in J1.
    destruct J1 as [l1 [l2 J1]]; subst.
    eapply getCmdLoc_in_getFdefLocs in J2; eauto.
Qed.

Lemma phinodes_placement_wfPI: forall rd f Ps1 Ps2 los nts pid ty al
  num l0 ps0 cs0 tmn0 dones (Hreach: ret rd = reachablity_analysis f)
  (Hentry: getEntryBlock f = Some (block_intro l0 ps0 cs0 tmn0))
  (Hfind: find_promotable_alloca f cs0 dones = Some (pid, ty, num, al))
  (HwfS :
     wf_system 
       [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  WF_PhiInfo {|
    PI_f := phinodes_placement rd pid ty al (successors f)
              (make_predecessors (successors f)) f;
    PI_rd := rd;
    PI_id := pid;
    PI_typ := ty;
    PI_num := num;
    PI_align := al |}.
Proof.
  intros.
  assert (Hwfpi:=Hfind).
  eapply find_promotable_alloca__WF_PhiInfo in Hwfpi; eauto.
  match goal with
  | _: WF_PhiInfo ?pinfo0 |- _ => set pinfo0 as pinfo
  end.  
  assert (Some rd = 
           reachablity_analysis (phinodes_placement_f pinfo (PI_f pinfo))) 
    as Hreach'.
    fold_PhiPlacement_tac. 
    rewrite <- TransCFG.pres_reachablity_analysis; auto.
  assert (getEntryBlock (phinodes_placement_f pinfo (PI_f pinfo)) =
      Some (phinodes_placement_blk pinfo (block_intro l0 ps0 cs0 tmn0))) 
    as Hentry'.
    fold_PhiPlacement_tac.
    erewrite TransCFG.pres_getEntryBlock; eauto.
  assert (J:=phinodes_placement_blk_inv' pinfo (block_intro l0 ps0 cs0 tmn0)).
  destruct J as [l1 [ps1 [cs1 [tmn1 [ps2 [cs3 [cs2 [EQ [J1 J2]]]]]]]]]; subst.
  inv EQ.
  assert (find_promotable_alloca 
            (phinodes_placement_f pinfo (PI_f pinfo)) (cs3 ++ cs1 ++ cs2) dones = 
               Some (pid, ty, num, al)) as R.
    rewrite <- find_promotable_alloca_weaken_head.
      rewrite <- find_promotable_alloca_weaken_tail.
        rewrite <- phinodes_placement_find_promotable_alloca; auto.
        intros. exists (block_intro l1 ps1 cs1 tmn1).
        apply andb_true_intro.
        simpl.
        split. solve_in_list.
               solve_blockInFdefB.
        
        destruct J2 as [_ J2].
        destruct J2 as [J2 | [lid [pid' [sid [J3 [scs [J4 J5]]]]]]]; 
          subst; simpl; constructor; simpl; auto.
      destruct J2 as [J2 _].
      destruct J2 as [[J21 J22] | [lid [pid' [sid [J3 [pds [J4 [J5 J6]]]]]]]]; 
        subst; simpl; constructor; simpl; auto.
   
  rewrite J1 in Hentry'.
  eapply find_promotable_alloca__WF_PhiInfo in R; eauto.
  rewrite <- phinodes_placement_f_spec1 in R.
  subst pinfo. simpl in *. unfold PI_preds, PI_succs in R. simpl in *. auto.
Qed.

