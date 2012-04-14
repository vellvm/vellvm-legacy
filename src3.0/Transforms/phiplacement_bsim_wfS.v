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

Ltac unfold_PhiPlacement_tac :=
repeat match goal with
| |- context [ftrans (PhiPlacement ?pinfo) ?f] =>
  replace (ftrans (PhiPlacement pinfo) f)
    with (phinodes_placement_f pinfo f); auto
| |- context [btrans (PhiPlacement ?pinfo) ?b] =>
  replace (btrans (PhiPlacement pinfo) b)
    with (phinodes_placement_blk pinfo b); auto
| |- context [ftrans (PhiPlacement ?pinfo)] =>
  replace (ftrans (PhiPlacement pinfo))
    with (phinodes_placement_f pinfo); auto
| |- context [btrans (PhiPlacement ?pinfo)] =>
  replace (btrans (PhiPlacement pinfo))
    with (phinodes_placement_blk pinfo); auto
end.

(*********************************************************)
(* wfness *)

Lemma wf_typ_independent: forall (sys1 sys2 : system) (td: targetdata)
  (t: typ) (Hwft: wf_typ sys1 td t), wf_typ sys2 td t.
Proof.
  intros.
  inv Hwft.
  constructor; eauto using wf_styp_independent, noncycled_independent.
Qed.

Lemma uniqF__uniqBlocksLocs : forall fh lb,
  uniqFdef (fdef_intro fh lb) -> NoDup (getBlocksLocs lb).
Proof.
  intros. destruct fh. inversion H. split_NoDup; auto.
Qed.

Lemma wf_styp__isValidElementTyp: forall S td t (Hty: wf_styp S td t),
  isValidElementTyp t.
Proof.
  intros.
  unfold isValidElementTyp, isValidElementTypB, isNotValidElementTypB.
  inv Hty; simpl; auto.
Qed.

Lemma getPointerAlignmentInfo_pos: forall los, 
 (getPointerAlignmentInfo los true > 0)%nat.
Admitted. (* Typing should check this on the top *)

Lemma wf_typ_pointer: forall S td t (Hwft: wf_typ S td t),
  wf_typ S td (typ_pointer t).
Proof.
  intros. 
  inv Hwft.
  constructor; auto.
    constructor; auto.
      eapply wf_styp__isValidElementTyp; eauto.
      apply getPointerAlignmentInfo_pos.
Qed.

Lemma WF_PhiInfo__wf_value: forall pinfo (Hwfpi : WF_PhiInfo pinfo) S M
  (HUniq: uniqFdef (PI_f pinfo)) (HwfF : wf_fdef S M (PI_f pinfo)),
  wf_value S M (PI_f pinfo) (value_id (PI_id pinfo)) 
    (typ_pointer (PI_typ pinfo)).
Proof.
  intros.
  destruct M.
  constructor.
    apply WF_PhiInfo_spec21 in HwfF; auto.
    apply wf_typ_pointer; auto.

    apply WF_PhiInfo_spec20 in HUniq; auto.
Qed.

Lemma WF_PhiInfo__lookupBlockViaIDFromFdef: forall pinfo 
  (Hwfpi : WF_PhiInfo pinfo) (Huniq: uniqFdef (PI_f pinfo)),
  exists b, 
    getEntryBlock (PI_f pinfo) = Some b /\
    lookupBlockViaIDFromFdef (PI_f pinfo) (PI_id pinfo) = Some b.
Proof.
  intros.
  subst.
  apply WF_PhiInfo_spec22 in Hwfpi; auto.
  destruct Hwfpi as [l0 [ps0 [cs1 [cs2 [tmn0 Hentry]]]]].
  match goal with
  | Hentry: getEntryBlock _ = Some ?b |- _ => exists b; split; auto
  end.
  eapply inGetBlockIDs__lookupBlockViaIDFromFdef; eauto 1.
    simpl. rewrite getCmdsIDs_app. simpl. xsolve_in_list.
    solve_blockInFdefB.
Qed.

(* from dtree.v *)
Definition getEntryLabel (f:fdef) : option l :=
match f with
| fdef_intro _ ((block_intro l0 _ _ _)::_) => Some l0
| _ => None
end.

(* from dtree_props.v *)
Lemma dom_analysis__entry_doms_others1: forall S M f 
  (HwfF: wf_fdef S M f) entry
  (H: getEntryLabel f = Some entry)
  (Hex: exists b,  match (AMap.get b (dom_analyze f)) with
                   | Dominators.mkBoundedSet dts _ => dts <> nil
                   end),
  (forall b, b <> entry /\ reachable f b ->
     match (AMap.get b (dom_analyze f)) with
     | Dominators.mkBoundedSet dts _ => In entry dts
     end).
Proof.
  intros.
  destruct H0 as [J1 J2].
  case_eq ((dom_analyze f) !! b).
  intros bs_contents bs_bound H1.
  unfold dom_analyze in H1, Hex.
  destruct f as [f b0].
  remember (entry_dom b0) as R.
  destruct R.
  destruct x as [[]|]; subst.
    destruct b0 as [|b0 b2]; inv H.
    destruct b1; tinv y.
    destruct bs_contents0; tinv y.
    destruct b0 as [l1 p c t]. inv HeqR.
    inv H2.
    remember (
      DomDS.fixpoint (bound_blocks (block_intro entry p c t :: b2))
           (successors_blocks (block_intro entry p c t :: b2))
           (transfer (bound_blocks (block_intro entry p c t :: b2)))
           ((entry,
            {| DomDS.L.bs_contents := nil; DomDS.L.bs_bound := bs_bound0 |})
            :: nil)) as R.
    destruct R.
      symmetry in HeqR.
      eapply EntryDomsOthers.dom_entry_doms_others with (entry:=entry) in HeqR;
        eauto.
        unfold EntryDomsOthers.entry_doms_others in HeqR.
        apply HeqR in J1.
        unfold Dominators.member in J1.
        unfold EntryDomsOthers.dt, EntryDomsOthers.bound, DomDS.dt, DomDS.L.t
          in J1.
        unfold Dominators.t in H1. simpl in J1, H1.
        rewrite H1 in J1; auto.

        split.
           remember (Kildall.successors_list
             (EntryDomsOthers.predecessors (block_intro entry p c t :: b2))
               entry) as R.
           destruct R; auto.
           assert (
             In a
               (Kildall.successors_list
                 (EntryDomsOthers.predecessors (block_intro entry p c t :: b2))
               entry)) as Hin. rewrite <- HeqR0. simpl; auto.
           apply Kildall.make_predecessors_correct' in Hin.
           change (successors_blocks (block_intro entry p c t :: b2)) with
             (successors (fdef_intro f (block_intro entry p c t :: b2))) in Hin.
           apply successors__blockInFdefB in Hin.
           destruct Hin as [ps0 [cs0 [tmn0 [G1 G2]]]].
           eapply getEntryBlock_inv with (l3:=a)(a:=entry) in G2; simpl; eauto.
           congruence.

        split; auto.
          exists{| DomDS.L.bs_contents := nil; DomDS.L.bs_bound := bs_bound0 |}.
          simpl.
          split; auto.
            split; intros x Hin; auto.

      rewrite AMap.gso in H1; auto.
      rewrite AMap.gi in H1. inv H1.
      destruct Hex as [b0 Hex].
      destruct (l_dec entry b0); subst.
        rewrite AMap.gss in Hex; auto. congruence.

        rewrite AMap.gso in Hex; auto. rewrite AMap.gi in Hex. simpl in Hex.
        contradict Hex; auto.

    inv H.
Qed.

Lemma entry_blockStrictDominates_others: forall s m f (HwfF : wf_fdef s m f)
  (b be : block) (Hentry : getEntryBlock f = ret be)
  (n : getBlockLabel be <> getBlockLabel b)
  (Hreach : isReachableFromEntry f b),
  blockStrictDominates f be b.
Proof.
  unfold blockStrictDominates.
  intros.
  destruct be as [l1 ? ? ?].
  destruct b as [l2 ? ? ?].
  simpl in n.
  assert (getEntryLabel f = Some l1) as Gentry.
    destruct f as [? blocks5].
    destruct blocks5; inv Hentry. auto.
  eapply dom_analysis__entry_doms_others1 with (b:=l2) in Gentry; eauto.
    admit. (* typings should ensure dom_analysis always succeeds. *)
Qed.

Lemma isReachableFromEntry_dec: forall f b,
  isReachableFromEntry f b \/ ~ isReachableFromEntry f b.
Proof.
  destruct f as [fh bs]. destruct b as [l0 ? ? ?]. simpl.
  apply reachable_dec; auto.
Qed.

Lemma wf_cmds_intro: forall s m f b cs,
  (forall c, In c cs -> wf_insn s m f b (insn_cmd c)) ->
  wf_cmds s m f b cs.
Proof.
  induction cs; intros.
    constructor.
    constructor.
      apply H; simpl; auto.
      apply IHcs. intros. apply H; simpl; auto.
Qed.

Lemma wf_cmds_elim: forall s m f b cs,
  wf_cmds s m f b cs -> forall c, In c cs -> wf_insn s m f b (insn_cmd c).
Proof.
  intros s m f b cs J.
  induction J; intros.
    inv H.

    simpl in H0.
    destruct H0 as [H0 | H0]; subst; auto.
Qed.

Lemma wf_cmds_app: forall s m f b cs2 (Hwfcs2: wf_cmds s m f b cs2) cs1
  (Hwfcs1: wf_cmds s m f b cs1), wf_cmds s m f b (cs1++cs2).
Proof.
  induction cs1; simpl; intros; auto.
    inv Hwfcs1. constructor; auto.
Qed.

Lemma wf_phinodes_app: forall s m f b ps2 (Hwfps2: wf_phinodes s m f b ps2) ps1
  (Hwfps1: wf_phinodes s m f b ps1), wf_phinodes s m f b (ps1++ps2).
Proof.
  induction ps1; simpl; intros; auto.
    inv Hwfps1. constructor; auto.
Qed.

Ltac inv_wf_block H :=
let S5 := fresh "S5" in
let M5 := fresh "M5" in
let F5 := fresh "F5" in
let l5 := fresh "l5" in 
let ps5 := fresh "ps5" in 
let cs5 := fresh "cs5" in 
let tmn5 := fresh "tmn5" in 
let HBinSMF := fresh "HBinSMF" in 
let Hwfps := fresh "Hwfps" in 
let Hwfcs := fresh "Hwfcs" in 
let Hwfi := fresh "Hwfi" in 
let EQ1 := fresh "EQ1" in
let EQ2 := fresh "EQ2" in
let EQ3 := fresh "EQ3" in 
let EQ4 := fresh "EQ4" in
inversion H as 
  [S5 M5 F5 l5 ps5 cs5 tmn5 HBinSMF Hwfps Hwfcs Hwfi EQ1 EQ2 EQ3 EQ4];
subst S5 M5 F5.

Ltac inv_wf_fdef H :=
let S5 := fresh "S5" in
let los5 := fresh "los5" in
let nts5 := fresh "nts5" in
let prods5 := fresh "prods5" in
let fh5 := fresh "fh5" in
let bs5 := fresh "bs5" in
let b5 := fresh "b5" in
let udb5 := fresh "udb5" in
let HpInS := fresh "HpInS" in
let Hwffh := fresh "Hwffh" in
let Hentry := fresh "Hentry" in
let EQ0 := fresh "EQ0" in
let Hnpred := fresh "Hnpred" in
let Hwfb := fresh "Hwfb" in
let EQ1 := fresh "EQ1" in
let EQ2 := fresh "EQ2" in
let EQ3 := fresh "EQ3" in
inversion H as 
  [S5 los5 nts5 prods5 fh5 bs5 b5 udb5 HpInS Hwffh Hentry EQ0 Hnpred
   Hwfb EQ1 EQ2 EQ3]; subst udb5 S5.

Lemma In_InBlocksB: forall b bs, In b bs -> InBlocksB b bs = true.
Admitted.

(* entry_cmds_simulation in phiplacement_bsim_defs.v should 
   also use the lemma *)
Lemma PI_preds_of_entry_cannot_be_nonempty: forall s m pinfo
  (HwfF: wf_fdef s m (PI_f pinfo)) b
  (Hentry: getEntryBlock (PI_f pinfo) = Some b),
  forall (pd : l) (pds : list l), 
    (PI_preds pinfo) ! (getBlockLabel b) <> ret (pd :: pds).
Proof.
  intros.
  unfold PI_preds.
  intros. intro J.
  assert (In pd (make_predecessors (PI_succs pinfo))!!!(getBlockLabel b)) as G.
    unfold successors_list. unfold l in J. rewrite J. simpl. auto.
  apply make_predecessors_correct' in G.
  unfold PI_succs in G.
  apply successors__blockInFdefB in G.
  destruct G as [ps1 [cs1' [tmn1 [G1 G2]]]].
  destruct (PI_f pinfo) as [fh bs].
  simpl in G1.
  destruct b.
  eapply getEntryBlock_inv in G1; eauto.
Qed.

(* wf_phi_operands doesnt depend on i0 and t0, which should be removed. *)
Lemma wf_phi_operands__intro : forall f b i0 t0 vls0,
  (forall vid1 l1 (Hin: In (value_id vid1, l1) vls0), 
     exists b1,
      lookupBlockViaLabelFromFdef f l1 = Some b1 /\
      ((exists vb,
         lookupBlockViaIDFromFdef f vid1 = Some vb /\
         (blockDominates f vb b1 \/ not (isReachableFromEntry f b))) \/
      In vid1 (getArgsIDsOfFdef f))) ->
  wf_phi_operands f b i0 t0 vls0.
Proof.
  induction vls0 as [|[[vid5|] l0]]; intros.
    constructor.

    assert (In (value_id vid5, l0) ((value_id vid5, l0) :: vls0)) as Hin.
      xsolve_in_list.
    apply H in Hin.
    destruct Hin as [b1 [J1 J2]].
    econstructor; eauto.
      apply IHvls0.
      intros.
      apply H. simpl. auto.

    constructor.
      apply IHvls0.
      intros.
      apply H. simpl. auto.
Qed.

Lemma wf_phi_operands__elim' : forall f b i0 t0 vls0 vid1 l1
  (Hwfop: wf_phi_operands f b i0 t0 vls0)
  (Hin: In (value_id vid1, l1) vls0),
  exists b1,
    lookupBlockViaLabelFromFdef f l1 = Some b1 /\
    ((exists vb,
       lookupBlockViaIDFromFdef f vid1 = Some vb /\
       (blockDominates f vb b1 \/ not (isReachableFromEntry f b))) \/
    In vid1 (getArgsIDsOfFdef f)).
Proof.
  induction 1; intros.
    tauto.

    destruct_in Hin.
      inv Hin. eauto.

    destruct_in Hin.
      congruence.
Qed.

(* from dtree_props.v *)
Lemma In_bound_fdef__blockInFdefB: forall f l3,
  In l3 (bound_fdef f) ->
  exists ps, exists cs, exists tmn,
    blockInFdefB (block_intro l3 ps cs tmn) f = true.
Admitted. (* infra *)

Lemma PI_newids_are_in_PI_rd: forall pinfo l1 (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  (PI_newids pinfo) ! l1 <> merror ->
  In l1 (PI_rd pinfo).
Proof.
  intros.
Admitted.

Lemma PI_rd__lookupBlockViaLabelFromFdef: forall pinfo (Hwfpi: WF_PhiInfo pinfo) l0,
  In l0 (PI_rd pinfo) ->
  exists b1 : block,
    lookupBlockViaLabelFromFdef (PI_f pinfo) l0 = ret b1 /\
    isReachableFromEntry (PI_f pinfo) b1.
Admitted.

Lemma blockDominates_refl: forall f b, blockDominates f b b.
Proof.
  unfold blockDominates.
  destruct b. destruct (dom_analyze f) !! l5. auto.
Qed.

Lemma WF_PhiInfo_br_preds_succs: forall pinfo l0 l3 (Hwfpi : WF_PhiInfo pinfo)
  prds (Hin : In l3 prds) (Heq' : (PI_preds pinfo) ! l0 = ret prds),
  exists succs, (PI_succs pinfo) ! l3 = ret succs /\ In l0 succs.
Proof.
  unfold PI_preds. unfold PI_succs.
  intros.
  destruct Hwfpi as [J1 J2].
  assert (In l3 ((make_predecessors (successors (PI_f pinfo)))!!!l0)) as Hin'.
    unfold successors_list.
    unfold ls, l in *.
    rewrite Heq'. auto.
  apply make_predecessors_correct' in Hin'.
  unfold successors_list in Hin'.
  remember (@ATree.get (list atom) l3 (successors (PI_f pinfo))) as R.
  destruct R; tinv Hin'. eauto.
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

Lemma uniqF__lookupPhiNodeTypViaIDFromFdef : forall l1 ps1 cs1 tmn1 f p,
  uniqFdef f ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  In p ps1 ->
  lookupTypViaIDFromFdef f (getPhiNodeID p) = Some (getPhiNodeTyp p).
Proof.
  intros.
  destruct f as [f b].
  destruct f as [fnattrs5 typ5 id5 args5 varg5]. inversion H.
  split_NoDup.
  simpl in *.
  assert (In (getPhiNodeID p) (getBlocksLocs b)) as Hin.
    eapply in_getBlockLocs__in_getBlocksLocs in H0; eauto.
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

Lemma phinodes_placement_blk_inv: forall pinfo b,
  exists l0, exists ps0, exists cs0, exists tmn0, 
    exists ps1, exists cs1, exists cs2,
    b = block_intro l0 ps0 cs0 tmn0 /\
    phinodes_placement_blk pinfo b = 
      block_intro l0 (ps1++ps0) (cs1 ++ cs0 ++ cs2) tmn0.
Proof.
  intros. destruct b as [l0 ps0 cs0 tmn0]. simpl in *. 
  exists l0. exists ps0. exists cs0. exists tmn0.
  destruct ((PI_newids pinfo) ! l0) as [[[]]|].
    destruct ((PI_preds pinfo) ! l0) as [[]|]; try solve [
      exists nil; exists nil;
      destruct ((PI_succs pinfo) ! l0) as [[]|]; try solve [
        exists nil; auto |
        match goal with
        | |- context [ (_++[?c]) ] => exists [c]; simpl_env; auto
        end
      ] |

      match goal with
      | |- context [ block_intro _ (?p::_) (?c::_++_) _] => 
           exists [p]; exists [c]
      end;
      destruct ((PI_succs pinfo) ! l0) as [[]|]; try solve [
        exists nil; auto |
        match goal with
        | |- context [ (_::_++[?c]) ] => exists [c]; simpl_env; auto
        end
      ]
    ].

    exists nil. exists nil. exists nil. simpl_env. auto.
Qed.

Ltac solve_refl :=
match goal with
| |- ?c =cmd= ?c = true => apply cmdEqB_refl
| |- ?p =phi= ?p = true => apply phinodeEqB_refl
| |- moduleEqB ?m ?m = true => apply moduleEqB_refl
end.

Section PresWF.

Variable (los:layouts) (nts:namedts) (Ps1 Ps2:products) (pinfo:PhiInfo)
         (M M':module) (f':fdef).
Hypothesis (Hwfpi: WF_PhiInfo pinfo)   
           (HeqM: M = module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
           (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
           (HeqF': f' = phinodes_placement_f pinfo (PI_f pinfo))
           (HwfF: wf_fdef [M] M (PI_f pinfo)) 
           (HuniqF: uniqFdef (PI_f pinfo)).

Lemma phinodes_placement_lookupTypViaIDFromFdef: forall id0 t
  (Hlkty: lookupTypViaIDFromFdef (PI_f pinfo) id0 = Some t),
  lookupTypViaIDFromFdef f' id0 = Some t.
Admitted.

Lemma phinodes_placement_wf_const : forall c t
  (Hwfc: wf_const [M] (los,nts) c t),
  wf_const [M'] (los,nts) c t.

Admitted.

Lemma phinodes_placement_wf_value : forall v t
  (Hwfv: wf_value [M] M (PI_f pinfo) v t),
  wf_value [M'] M' f' v t.
Proof.
  intros.
  assert (J1:=phinodes_placement_wf_const).
  assert (J2:=phinodes_placement_lookupTypViaIDFromFdef).
  inv Hwfv; uniq_result;
    constructor; eauto using wf_typ_independent.
Qed.

Lemma phinodes_placement_insnInFdefBlockB: forall b instr,
  insnInFdefBlockB instr (PI_f pinfo) b = true ->
  insnInFdefBlockB instr (phinodes_placement_f pinfo (PI_f pinfo))
    (phinodes_placement_blk pinfo b) = true.
Admitted.

Lemma phinodes_placement_insnDominates: forall b b' instr
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

Lemma phinodes_placemen_getArgsIDsOfFdef:
  getArgsIDsOfFdef (PI_f pinfo) =
    getArgsIDsOfFdef (phinodes_placement_f pinfo (PI_f pinfo)).
Admitted.

Lemma phinodes_placement_lookupBlockViaIDFromFdef: forall id0 b,
  lookupBlockViaIDFromFdef (PI_f pinfo) id0 = Some b ->
  lookupBlockViaIDFromFdef (phinodes_placement_f pinfo (PI_f pinfo)) id0 
    = Some (phinodes_placement_blk pinfo b).
Admitted.

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
    rewrite <- phinodes_placemen_getArgsIDsOfFdef.
    destruct H3 as [[b0 [J1 H3]] | J3]; auto.
    left.
    exists (phinodes_placement_blk pinfo b0).
    split.
      apply phinodes_placement_lookupBlockViaIDFromFdef; auto.

      fold_PhiPlacement_tac.
      rewrite <- TransCFG.pres_blockStrictDominates; auto.
      rewrite <- TransCFG.pres_isReachableFromEntry; auto.
      destruct H3 as [H3 | [H3 | H3]]; auto.
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

Lemma phinodes_placement_getDefReturnType:
  Function.getDefReturnType (phinodes_placement_f pinfo (PI_f pinfo)) =
  Function.getDefReturnType (PI_f pinfo).
Proof.
  assert (fheaderOfFdef (PI_f pinfo) = 
          fheaderOfFdef (phinodes_placement_f pinfo (PI_f pinfo))) as EQ.
    rewrite <- phinodes_placement_f_spec1.
    apply phinodes_placement_fheaderOfFdef.
  unfold Function.getDefReturnType.
  destruct (phinodes_placement_f pinfo (PI_f pinfo)) as [[]].
  destruct (PI_f pinfo) as [[]].
  inv EQ. auto.
Qed.

Lemma phinodes_placement_lookupBlockViaLabelFromFdef: forall l0 b,
  lookupBlockViaLabelFromFdef (PI_f pinfo) l0 = Some b ->
  lookupBlockViaLabelFromFdef (phinodes_placement_f pinfo (PI_f pinfo)) l0 
    = Some (phinodes_placement_blk pinfo b).
Admitted.

Lemma phinodes_placement_wf_trunc : forall b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) instr
  (HwfI : wf_trunc [M] M (PI_f pinfo) b instr),
  wf_trunc [M'] M' f' b' instr.
Proof.
  intros.
  assert (J1:=@phinodes_placement_wf_insn_base b b' Heqb' instr).
  assert (J2:=phinodes_placement_wf_value).
  assert (J3:=@wf_typ_independent [M] [M'] (los,nts)).
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
  assert (J3:=@wf_typ_independent [M] [M'] (los,nts)).
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
  assert (J3:=@wf_typ_independent [M] [M'] (los,nts)).
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
  rewrite <- phinodes_placemen_getArgsIDsOfFdef.
  destruct Hwfps as [b1 [J1 Hwfps]].
  exists (phinodes_placement_blk pinfo b1).
  split.
    apply phinodes_placement_lookupBlockViaLabelFromFdef; auto.

    destruct Hwfps as [[b0 [J2 Hwfps]] | J3]; auto.
    left.
    exists (phinodes_placement_blk pinfo b0).
    split.
      apply phinodes_placement_lookupBlockViaIDFromFdef; auto.

      fold_PhiPlacement_tac.
      rewrite <- TransCFG.pres_blockDominates; auto.
      rewrite <- TransCFG.pres_isReachableFromEntry; auto.
Qed.

Lemma phinodes_placement_check_list_value_l : forall b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) vls0
  (hwfps: check_list_value_l (PI_f pinfo) b vls0),
  check_list_value_l f' b' vls0.
Proof.
  unfold check_list_value_l.
  intros. destruct_let. subst.
  fold_PhiPlacement_tac.
  rewrite <- TransCFG.pres_genBlockUseDef_fdef; auto.
  rewrite <- TransCFG.pres_predOfBlock; auto.
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
  eapply phinodes_placement_check_list_value_l in J2; eauto.
Qed.

Lemma phinodes_placement_wf_insn : forall b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) instr
  (HwfI : wf_insn [M] M (PI_f pinfo) b instr),
  wf_insn [M'] M' f' b' instr.
Proof.
  intros.
  assert (J1:=@phinodes_placement_wf_insn_base b b' Heqb' instr).
  assert (J2:=phinodes_placement_wf_value).
  assert (J3:=@wf_typ_independent [M] [M'] (los,nts)).
  assert (J4:=phinodes_placement_wf_const).
  assert (J5:=@phinodes_placement_wf_trunc b b' Heqb' instr).
  assert (J6:=@phinodes_placement_wf_ext b b' Heqb' instr).
  assert (J7:=@phinodes_placement_wf_cast b b' Heqb' instr).
  assert (J8:=@phinodes_placement_wf_phinode b b' Heqb').

Ltac phinodes_placement_wf_insn_tac :=
repeat match goal with
| H1 : lookupBlockViaLabelFromFdef (PI_f pinfo) _ = ret _ |- _ =>
  apply phinodes_placement_lookupBlockViaLabelFromFdef in H1
| H1 : context [Function.getDefReturnType (PI_f pinfo)] |- _ =>
  rewrite <- phinodes_placement_getDefReturnType in H1
| |- context [Function.getDefReturnType (PI_f pinfo)] =>
  rewrite <- phinodes_placement_getDefReturnType
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

Ltac solve_isNotPhiNode := unfold isPhiNode; simpl; congruence.

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

    left. assert (J:=Hwfpi).
    apply WF_PhiInfo__lookupBlockViaIDFromFdef in J; auto.
    destruct J as [be [Hentry Hlkup]]. 
    apply phinodes_placement_lookupBlockViaIDFromFdef in Hlkup.
    exists (phinodes_placement_blk pinfo be).
    split; auto.
    destruct (isReachableFromEntry_dec
                (phinodes_placement_f pinfo (PI_f pinfo))
                (phinodes_placement_blk pinfo b)); auto.
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
      right. left.
      fold_PhiPlacement_tac.
      erewrite <- TransCFG.pres_blockStrictDominates; eauto.
      assert (isReachableFromEntry (PI_f pinfo) b) as Hreach.
        erewrite (@TransCFG.pres_isReachableFromEntry (PhiPlacement pinfo)); 
          eauto.
      rewrite <- phinodes_placement_blk__getBlockLabel in n.
      rewrite <- phinodes_placement_blk__getBlockLabel in n.
      eapply entry_blockStrictDominates_others; eauto.
Qed.

Lemma wf_PI_typ': wf_typ [M'] (los, nts) (PI_typ pinfo).
Proof.
  subst.
  apply WF_PhiInfo_spec21 in HwfF; auto.
  eapply wf_typ_independent; eauto.
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
    exists (phinodes_placement_blk pinfo b).
    split.
      eapply insert_phi__lookupBlockViaIDFromFdef; eauto.
   
      destruct (isReachableFromEntry_dec
                  (phinodes_placement_f pinfo (PI_f pinfo))
                  (phinodes_placement_blk pinfo b)); auto.
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

    left. assert (J:=Hwfpi).
    apply WF_PhiInfo__lookupBlockViaIDFromFdef in J; auto.
    destruct J as [be [Hentry Hlkup]]. 
    apply phinodes_placement_lookupBlockViaIDFromFdef in Hlkup.
    exists (phinodes_placement_blk pinfo be).
    split; auto.
    destruct (isReachableFromEntry_dec
                (phinodes_placement_f pinfo (PI_f pinfo))
                (phinodes_placement_blk pinfo b)); auto.
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
      right. left.
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

Lemma inserted_phi_operands__elim_aux: forall v l1 pds acc
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

Lemma inserted_phi_operands__elim: forall v l1 pds
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

Lemma wf_inserted_phi: forall b lid pid sid pds
  (HeqR1 : ret (lid, pid, sid) = (PI_newids pinfo) ! (getBlockLabel b))
  (HeqR3 : ret pds = (PI_preds pinfo) ! (getBlockLabel b)) (Hneq : pds <> nil),
  wf_phinode (phinodes_placement_f pinfo (PI_f pinfo))
    (phinodes_placement_blk pinfo b)
    (gen_phinode pid (PI_typ pinfo) (PI_newids pinfo) pds).
Proof.
  intros.
  constructor.
    apply wf_phi_operands__intro.
    intros.
    apply inserted_phi_operands__elim in Hin.
    destruct Hin as [Hin [pid' [sid' Hnids]]].
      assert ((PI_newids pinfo) ! l1 <> merror) as G. congruence.
      apply PI_newids_are_in_PI_rd in G; auto.
      apply PI_rd__lookupBlockViaLabelFromFdef in G; auto.
      destruct G as [b1 [Hlkup Hreach]].
      assert (Hlkup':=Hlkup).
      apply (@TransCFG.pres_lookupBlockViaLabelFromFdef (PhiPlacement pinfo)) 
        in Hlkup'.
      rewrite (@TransCFG.pres_isReachableFromEntry (PhiPlacement pinfo)) 
        in Hreach.
      fold_PhiPlacement_tac.
      exists (btrans (PhiPlacement pinfo) b1).
      split; auto.
      left.
      exists (btrans (PhiPlacement pinfo) b1).
      split.
        apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
          simpl. 
          rewrite <- phinodes_placement_f_spec1.
          apply phinodes_placement__uniqFdef; auto.

          eapply WF_PhiInfo_br_preds_succs' in HeqR3; eauto.
          destruct HeqR3 as [EQ [succs [Hneq' J2]]]; subst.
          symmetry in Hnids.
          eapply phinodes_placement_blk_tail_inv in Hnids; eauto.
          destruct Hnids as [l0 [ps0 [cs0 [tmn0 [ps2 [cs2 [J3 J4]]]]]]]; subst.
          unfold_PhiPlacement_tac. rewrite J4.
          simpl. repeat rewrite getCmdsIDs_app. simpl. 
          xsolve_in_list.

          apply TransCFG.pres_blockInFdefB; auto.
          solve_blockInFdefB.

        left.
        apply blockDominates_refl.
               
    unfold check_list_value_l.
    admit. (* 1) redefined predOfBlock by make_pred, or prove they equal.
              2) br v l1 l2 should ensure l1 <> l2, or ignore the checking *)
Qed.

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
  destruct G as [b1 [Hlkup Hreach]].
  
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

Lemma wf_inserted: forall b b' 
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

Lemma phinodes_placement_wf_block : forall b
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

Lemma phinodes_placement_wf_blocks : forall bs 
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

Lemma phinodes_placement_wf_fdef: 
  wf_fdef [M'] M' (phinodes_placement_f pinfo (PI_f pinfo)).
Proof.
  intros. assert (HwfF':=HwfF).
  inv_wf_fdef HwfF'.
  match goal with
  | Hentry : getEntryBlock _ = _,
    HuniqF : uniqFdef _,
    Hnpred : hasNonePredecessor _ _ = _,
    HwfBs : wf_blocks _ _ _ _ |- _ =>
     eapply (@TransCFG.pres_getEntryBlock (PhiPlacement pinfo)) 
       in Hentry; eauto;
     eapply (@TransCFG.pres_hasNonePredecessor (PhiPlacement pinfo)) 
       in Hnpred; eauto
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
       
    match goal with
    | H4: wf_fheader _ _ _ |- _ => clear - H4; inv H4
    end.
    econstructor; eauto.
      intros t0 Hint0.
      apply H0 in Hint0.
      eapply wf_typ_independent; eauto.
  
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
Admitted. (* WF prev *)


