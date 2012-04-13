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

Section PresWF.

Variable (los:layouts) (nts:namedts) (Ps1 Ps2:products) (pinfo:PhiInfo).
Hypothesis (Hwfpi: WF_PhiInfo pinfo).

Lemma phinodes_placement_wf_insn : forall (M M':module) (f':fdef)
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqF': f' = phinodes_placement_f pinfo (PI_f pinfo)) b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) instr
  (HwfI : wf_insn [M] M (PI_f pinfo) b instr),
  wf_insn [M'] M' f' b' instr.
Proof.
Admitted.

Lemma phinodes_placement_wf_cmds : forall (M M':module) (f':fdef)
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqF': f' = phinodes_placement_f pinfo (PI_f pinfo)) b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) cs 
  (Hwfcs : wf_cmds [M] M (PI_f pinfo) b cs),
  wf_cmds [M'] M' f' b' cs.
Proof.
Admitted.

Lemma phinodes_placement_wf_phinodes : forall (M M':module) (f':fdef)
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqF': f' = phinodes_placement_f pinfo (PI_f pinfo)) b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b) ps
  (Hwfps : wf_phinodes [M] M (PI_f pinfo) b ps),
  wf_phinodes [M'] M' f' b' ps.
Proof.
Admitted.

Lemma phinodes_placement_lookupTypViaIDFromFdef: forall (f':fdef)
  (HeqF': f' = phinodes_placement_f pinfo (PI_f pinfo)) id0 t
  (Hlkty: lookupTypViaIDFromFdef (PI_f pinfo) id0 = Some t),
  lookupTypViaIDFromFdef f' id0 = Some t.
Admitted.

Lemma phinodes_placement_wf_value : forall (M M':module) (f':fdef)
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqF': f' = phinodes_placement_f pinfo (PI_f pinfo)) v t
  (Hwfv: wf_value [M] M (PI_f pinfo) v t),
  wf_value [M'] M' f' v t.
Proof.
  intros.
  inv Hwfv; try constructor.
(*    apply insert_lookupIDFromFdef; auto. *)
Admitted.

Lemma wf_inserted: forall (M M':module) (f':fdef) 
  (HwfF: wf_fdef [M] M (PI_f pinfo))
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqF': f' = phinodes_placement_f pinfo (PI_f pinfo)) b b' 
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
    admit.
  assert (wf_typ [M'] (los,nts) (PI_typ pinfo)) as Hwft.
    admit.
  subst.
  remember ((PI_newids pinfo) ! (getBlockLabel b)) as R1.
  remember ((PI_succs pinfo) ! (getBlockLabel b)) as R2.
  remember ((PI_preds pinfo) ! (getBlockLabel b)) as R3.
  destruct R1 as [[[lid pid] sid]|]; auto.
  split.
    destruct R2 as [[]|]; auto.
    constructor; auto.
      admit.

    destruct R3 as [[]|]; auto.
    split.
      constructor; auto.
        admit.
        admit.

      constructor; auto.
        unfold gen_phinode.
        admit.

        constructor.
Qed.

Lemma phinodes_placement_blockInSystemModuleFdefB: forall (M M':module) (f':fdef)
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqF': f' = phinodes_placement_f pinfo (PI_f pinfo)) b b' 
  (Heqb': b' = phinodes_placement_blk pinfo b)
  (Hin: blockInSystemModuleFdefB b [M] M (PI_f pinfo)),
  blockInSystemModuleFdefB b' [M'] M' f'.
Admitted.

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
  [S5 M5 F5 l5 ps5 cs5 tmn5 HBinSMF Hwfps Hwfcs Hwfi EQ1 EQ2 EQ3 EQ4]; subst.

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

Lemma phinodes_placement_wf_block : forall (M M':module) (f':fdef)
  (HwfF: wf_fdef [M] M (PI_f pinfo))
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqF': f' = phinodes_placement_f pinfo (PI_f pinfo)) b
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
  assert (HwfNew:=HwfF).
  eapply wf_inserted in HwfNew; eauto.
  inv_wf_block HwfB. simpl in HwfNew.
  eapply phinodes_placement_blockInSystemModuleFdefB in HBinSMF; eauto.
  eapply phinodes_placement_wf_cmds in Hwfcs; eauto.
  eapply phinodes_placement_wf_phinodes in Hwfps; eauto.
  eapply phinodes_placement_wf_insn in Hwfi; eauto.
  unfold phinodes_placement_blk, phinodes_placement_block in *.
  remember (PI_newids pinfo) ! l5 as R1.
  destruct R1 as [[[lid pid] sid]|]; try solve [constructor; auto].
  remember ((PI_preds pinfo) ! l5) as R2.
  remember ((PI_succs pinfo) ! l5) as R3.
  destruct R2 as [[]|];
    destruct R3 as [[]|]; 
      try solve [simpl_env in *; phinodes_placement_wf_block_tac2].
Qed.

Lemma phinodes_placement_wf_blocks : forall (M M':module) (f':fdef)
  (HwfF: wf_fdef [M] M (PI_f pinfo)) 
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqF': f' = phinodes_placement_f pinfo (PI_f pinfo))
  bs (Hin: forall b, In b bs -> blockInFdefB b (PI_f pinfo) = true)
  (HwfBs : wf_blocks [M] M (PI_f pinfo) bs) (Huniq : NoDup (getBlocksLocs bs)),
  wf_blocks [M'] M' f' (List.map (phinodes_placement_blk pinfo) bs).
Proof.
  intros. subst.
  induction bs; simpl.
    constructor.

    simpl in Huniq.
    split_NoDup. inv HwfBs.
    constructor; auto.
      eapply phinodes_placement_wf_block; eauto 1.
        apply Hin; simpl; auto.
      apply IHbs; auto.
        intros b Hin'. apply Hin. simpl; auto.
Qed.

Lemma In_InBlocksB: forall b bs, In b bs -> InBlocksB b bs = true.
Admitted.

Lemma phinodes_placement_wf_fdef: forall (M M':module) (f':fdef)
  (HeqM: M = module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2))
  (HeqM': M' = module_intro los nts (Ps1 ++ product_fdef f' :: Ps2))
  (HeqF': f' = phinodes_placement_f pinfo (PI_f pinfo))
  f (HwfF: wf_fdef [M] M f) 
  (Heq: f = PI_f pinfo) (HuniqF: uniqFdef f), 
  wf_fdef [M'] M' (phinodes_placement_f pinfo (PI_f pinfo)).
Proof.
  intros. subst. assert (HwfF':=HwfF).
  inv HwfF'.
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
    | H2: fdef_intro _ _ = PI_f _,
      H9: wf_blocks _ _ _ _ |- _ =>
      rewrite H2 in H9;
      eapply phinodes_placement_wf_blocks in H9; try solve [
        eauto |
        rewrite <- H2; fold_PhiPlacement_tac |
        rewrite <- H2 in HuniqF; eapply uniqF__uniqBlocksLocs; eauto |
        rewrite <- H2; simpl; intros; apply In_InBlocksB; auto
      ]
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


