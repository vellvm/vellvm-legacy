Require Import vellvm.
Require Import Iteration.
Require Import iter_pass.
Require Import program_sim.
Require Import palloca_props.

(**********************************************************)

Definition keep_pinfo (f:fdef) (pinfo1 pinfo2: PhiInfo) :=
PI_f pinfo2 = f /\
PI_rd pinfo1 = PI_rd pinfo2 /\
PI_id pinfo1 = PI_id pinfo2 /\
PI_typ pinfo1 = PI_typ pinfo2 /\
PI_align pinfo1 = PI_align pinfo2.

Hint Unfold keep_pinfo.

Ltac instantiate_pinfo :=
match goal with
| pinfo := {|
           PI_f := ?f;
           PI_rd := _;
           PI_id := _;
           PI_typ := _;
           PI_num := _;
           PI_align := _ |} : PhiInfo, 
  HwfS : WF_PhiInfo ?pi |- 
  exists _ : _, WF_PhiInfo _ /\ keep_pinfo ?f ?pi _ =>
  exists pi; repeat (split; auto)
| HwfS : WF_PhiInfo (update_pinfo ?f ?pi) |- _ => 
  exists (update_pinfo f pi); repeat (split; auto)
| HwfS : WF_PhiInfo ?pi, Heq: (PI_f ?pi) = ?f |- 
  exists _ : _, WF_PhiInfo _ /\ keep_pinfo ?f ?pi _ =>
  rewrite <- Heq; exists pi; repeat (split; auto)
| HwfS : WF_PhiInfo ?pi |- 
  exists _ : _, WF_PhiInfo _ /\ keep_pinfo (PI_f ?pi) ?pi _ =>
  exists pi; repeat (split; auto)
end.

Lemma keep_pinfo_trans: forall f f' p1 p2 p3
  (H1: keep_pinfo f p1 p2) (H2: keep_pinfo f' p2 p3),
  keep_pinfo f' p1 p3.
Proof.
  intros.
  destruct H1 as [A [B [C [D E]]]].
  destruct H2 as [A' [B' [C' [D' E']]]].
  repeat split; try solve [auto | etransitivity; eauto].
Qed.

Lemma change_keep_pinfo: forall f pinfo1 pinfo2
  (H1: PI_id pinfo1 = PI_id pinfo2)
  (H2: PI_typ pinfo1 = PI_typ pinfo2)
  (H3: PI_align pinfo1 = PI_align pinfo2)
  (H4: PI_rd pinfo1 = PI_rd pinfo2),
  (exists pinfo' : PhiInfo, WF_PhiInfo pinfo' /\ keep_pinfo f pinfo1 pinfo') -> 
  exists pinfo' : PhiInfo, WF_PhiInfo pinfo' /\ keep_pinfo f pinfo2 pinfo'.
Proof.
  intros.
  destruct H as [A [B C]].
  exists A. split; auto.
  unfold keep_pinfo in *.
  rewrite <- H1. rewrite <- H2. rewrite <- H3. rewrite <- H4. auto.
Qed.

Lemma update_pinfo_refl: forall f0 pinfo pinfo' 
  (Hkp: keep_pinfo f0 pinfo pinfo'), (update_pinfo pinfo' f0) = pinfo'.
Proof.
  intros.
  destruct Hkp as [EQ _]; subst. destruct pinfo'. auto.
Qed.

Ltac solve_keep_pinfo :=
match goal with
| Hkeep : keep_pinfo ?f ?pinfo ?pinfo' |- ?f = PI_f ?pinfo' =>
  destruct Hkeep as [? ?]; auto
| Hkeep : keep_pinfo _ ?pinfo ?pinfo' |-
    keep_pinfo ?f ?pinfo (update_pinfo ?pinfo' ?f) =>
  destruct Hkeep as [? [? [? [? ?]]]];
  unfold update_pinfo;
  repeat split; simpl; auto
| Hkeep : keep_pinfo _ ?pinfo ?pinfo' |- PI_id ?pinfo = PI_id ?pinfo' =>
  destruct Hkeep as [? [? [? ?]]]; auto
| Hkeep : keep_pinfo _ ?pinfo ?pinfo' |- PI_id ?pinfo' = PI_id ?pinfo =>
  destruct Hkeep as [? [? [? ?]]]; auto
| Hkeep : keep_pinfo _ ?pinfo ?pinfo' |- PI_rd ?pinfo' = PI_rd ?pinfo =>
  destruct Hkeep as [? [? [? ?]]]; auto
| Hkeep : keep_pinfo ?f ?pinfo ?pinfo' |- PI_f ?pinfo' = ?f =>
  destruct Hkeep as [? ?]; auto
| Hkeep : keep_pinfo ?f1 ?pinfo ?pinfo',
  HeqR : exists _:_,
            WF_PhiInfo _ /\ keep_pinfo ?f0 ?pinfo' _ |-
  exists _:_, WF_PhiInfo _ /\ keep_pinfo ?f0 ?pinfo _ =>
  let A:=fresh "A" in
  destruct HeqR as [A [? ?]];
  exists A; split; auto; apply keep_pinfo_trans with (f:=f1)(p2:=pinfo'); auto
| G: exists _:_, WF_PhiInfo _ /\ keep_pinfo ?f (update_pinfo ?pi _) _ |-
  exists _:_, WF_PhiInfo _ /\ keep_pinfo ?f ?pi _ =>
  let A:=fresh "A" in
  destruct G as [A [? ?]]; exists A; split; auto
| pinfo := {|
           PI_f := _;
           PI_rd := _;
           PI_id := ?pid;
           PI_typ := _;
           PI_num := _;
           PI_align := _ |} : PhiInfo, 
  Hkeep : keep_pinfo _ ?pinfo ?pinfo' |- PI_id ?pinfo' = ?pid =>
  destruct Hkeep as [? [? [? ?]]]; auto
| pinfo := {|
           PI_f := _;
           PI_rd := _;
           PI_id := ?pid;
           PI_typ := _;
           PI_num := _;
           PI_align := _ |} : PhiInfo, 
  Hkeep : keep_pinfo _ ?pinfo ?pinfo' |- ?pid = PI_id ?pinfo' =>
  destruct Hkeep as [? [? [? ?]]]; auto
| H: ?f _ _ = ?e |- ?f _ _ = ?e => rewrite H; f_equal; solve_keep_pinfo
| H: ?e = ?f _ _ |- ?f _ _ = ?e => rewrite H; f_equal; solve_keep_pinfo
end.

(**********************************************************)

Module IterationPassCorrect.

Ltac iter_blocks_tac :=
repeat match goal with
| H1: context [?A ++ ?b0 :: ?C] |- _ => 
  match type of b0 with
  | block => rewrite_env ((A++[b0])++C) in H1
  end
| |- context [?A ++ ?b0 :: ?C] => 
  match type of b0 with
  | block => rewrite_env ((A++[b0])++C)
  end
| H1:forall _:_, _ -> _ |- _ => progress (eapply H1; eauto)
end.

Section IterationPassCFG.

Variable (pass:IterPass).

Hypothesis iter_block_unchanged: forall f' efs' f b0 ctx efs,
  (f', false, efs') = pass.(iter_block) f b0 ctx efs ->
  f' = f /\ efs = efs'.

Hypothesis iter_block_reachablity_successors: forall f b ctx f0
  efs0 efs (Hpass : (f0, true, efs0) = pass.(iter_block) f b ctx efs),
  reachablity_analysis f = reachablity_analysis f0 /\
  successors f = successors f0.

Lemma iter_blocks_reachablity_successors_aux: forall f0 efs0 efs
  flag fh bs2 bs1 ctx rd
  (Hpass:IterationPass.iter_blocks pass (fdef_intro fh (bs1++bs2)) bs2 ctx rd efs
    = (f0, flag, efs0)),
  reachablity_analysis (fdef_intro fh (bs1++bs2)) =
    reachablity_analysis f0 /\
  successors (fdef_intro fh (bs1++bs2)) = successors f0.
Proof.
  induction bs2 as [|b0 bs2]; simpl; intros.
    inv Hpass. auto.

    destruct (in_dec id_dec (getBlockLabel b0) rd).
    Case "reachable".
      remember
        (pass.(iter_block) (fdef_intro fh (bs1 ++ b0 :: bs2)) b0 ctx efs) as R.
      destruct R as [[f' []] efs']; inv Hpass; auto.
        eapply iter_block_reachablity_successors; eauto.

        apply iter_block_unchanged in HeqR. destruct HeqR; subst.
        iter_blocks_tac.

    Case "unreachable". 
      iter_blocks_tac.
Qed.

Lemma iter_blocks_reachablity_successors: forall f0 efs0 efs 
  flag fh bs ctx rd
  (Hpass:IterationPass.iter_blocks pass (fdef_intro fh bs) bs ctx rd efs =
    (f0, flag, efs0)),
  reachablity_analysis (fdef_intro fh bs) =
    reachablity_analysis f0 /\
  successors (fdef_intro fh bs) = successors f0.
Proof.
  intros.
  rewrite_env (nil ++ bs).
  eapply iter_blocks_reachablity_successors_aux; eauto.
Qed.

Lemma iter_reachablity_successors: forall f1 efs1 f2 efs2 ctx rd
  (Hpass: SafePrimIter.iterate _ (IterationPass.iter_step pass ctx rd) 
    (f1, efs1) = (f2, efs2)),
  reachablity_analysis f2 = reachablity_analysis f1 /\
  successors f2 = successors f1.
Proof.
  intros. subst.
  set (P:=fun (re:(fdef * pass.(effects))) =>
          let '(f, _) := re in
          reachablity_analysis f = reachablity_analysis f1 /\
          successors f = successors f1).
  assert (P (f1, efs1)) as HPf1.
    unfold P. split; auto.
  apply SafePrimIter.iterate_prop with (P:=P) in Hpass; auto.
    unfold IterationPass.iter_step.
    intros a HPa.
    destruct a as [f dones].
    unfold IterationPass.iter_fdef.
    destruct f as [fh bs].
    remember (IterationPass.iter_blocks pass (fdef_intro fh bs) bs ctx rd dones) 
      as R.
    destruct R as [[f0 flag0] dones0]; auto.
    assert (P (f0, dones0)) as HPf0.
      unfold P.
      symmetry in HeqR.
      apply iter_blocks_reachablity_successors in HeqR.
      destruct HeqR. destruct HPa.
      split.
        transitivity (reachablity_analysis (fdef_intro fh bs)); auto.
        transitivity (successors (fdef_intro fh bs)); auto.

    destruct flag0; auto.
Qed.

End IterationPassCFG.

Section IterationPassSimWFP. 

Variable (pass:IterPass).

Hypothesis iter_block_unchanged: forall f' efs' f b0 ctx efs,
  (f', false, efs') = pass.(iter_block) f b0 ctx efs ->
  f' = f /\ efs = efs'.

Hypothesis PI_ctx: PhiInfo -> pass.(context).

Variable (los:layouts) (nts:namedts) (Ps1 Ps2: products).

Hypothesis iter_block_wfPI: forall fh efs f0 efs0
  (pinfo:PhiInfo) (Hwfpi: WF_PhiInfo pinfo)
  bs1 b0 bs2 (Hreach: In (getBlockLabel b0) (PI_rd pinfo))
  (Hpass : (f0, true, efs0) =
           pass.(iter_block) (fdef_intro fh (bs1 ++ b0 :: bs2)) b0 
             (PI_ctx pinfo) efs)
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ b0 :: bs2))
  (HwfS :
     wf_system
       [module_intro los nts
         (Ps1 ++ product_fdef (fdef_intro fh (bs1 ++ b0 :: bs2)) :: Ps2)]),
  exists pinfo', WF_PhiInfo pinfo' /\ keep_pinfo f0 pinfo pinfo'.

Lemma iter_blocks_wfPI_aux: forall fh efs f0 efs0 flag bs2 bs1
  (pinfo:PhiInfo) (Hwfpi: WF_PhiInfo pinfo)
  (Hpass:IterationPass.iter_blocks pass (fdef_intro fh (bs1++bs2)) bs2 
    (PI_ctx pinfo) (PI_rd pinfo) efs = (f0, flag, efs0))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ bs2))
  (HwfS :
     wf_system
       [module_intro los nts
         (Ps1 ++
          product_fdef
            (fdef_intro fh (bs1 ++ bs2)) :: Ps2)]),
  exists pinfo', WF_PhiInfo pinfo' /\ keep_pinfo f0 pinfo pinfo'.
Proof.
  induction bs2 as [|b0 bs2]; simpl; intros.
    inv Hpass. instantiate_pinfo.

    destruct (in_dec id_dec (getBlockLabel b0) (PI_rd pinfo)).
    Case "reachable".
      remember
        (pass.(iter_block)
          (fdef_intro fh (bs1 ++ b0 :: bs2)) b0 (PI_ctx pinfo) efs) as R.
      destruct R as [[f' []] efs']; inv Hpass; eauto.
        apply iter_block_unchanged in HeqR. destruct HeqR; subst.
        iter_blocks_tac.
    Case "unreachable". 
      iter_blocks_tac.
Qed.

Lemma iter_blocks_wfPI: forall fh efs f0 efs0 flag bs
  (pinfo:PhiInfo) (Hwfpi: WF_PhiInfo pinfo)
  (Hpass:IterationPass.iter_blocks pass (fdef_intro fh bs) bs 
    (PI_ctx pinfo) (PI_rd pinfo) efs = (f0, flag, efs0))
  (Heq: PI_f pinfo = fdef_intro fh bs)
  (HwfS :
     wf_system
       [module_intro los nts
         (Ps1 ++ product_fdef (fdef_intro fh bs) :: Ps2)]),
  exists pinfo', WF_PhiInfo pinfo' /\ keep_pinfo f0 pinfo pinfo'.
Proof.
  intros.
  rewrite_env (nil ++ bs) in HwfS.
  eapply iter_blocks_wfPI_aux; eauto; simpl; eauto.
Qed.

Hypothesis iter_block_wfS: forall fh efs f0 efs0
  (pinfo:PhiInfo) (Hwfpi: WF_PhiInfo pinfo)
  main VarArgs bs1 b0 bs2 (Hreach:In (getBlockLabel b0) (PI_rd pinfo))
  (Hpass : (f0, true, efs0) =
           pass.(iter_block) (fdef_intro fh (bs1 ++ b0 :: bs2)) b0 
             (PI_ctx pinfo) efs)
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ b0 :: bs2)) S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f0 :: Ps2)])
  (Heq1: S2 = 
    [module_intro los nts
      (Ps1 ++ product_fdef (fdef_intro fh (bs1 ++ b0 :: bs2)) :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.

Lemma iter_blocks_sim_wfS_aux: forall fh efs f0 efs0 main VarArgs flag bs2 bs1
  (pinfo:PhiInfo) (Hwfpi: WF_PhiInfo pinfo)
  (Hpass:IterationPass.iter_blocks pass (fdef_intro fh (bs1++bs2)) bs2 
    (PI_ctx pinfo) (PI_rd pinfo) efs = (f0, flag, efs0))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ bs2))
  S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++  product_fdef f0 :: Ps2)])
  (heq2: S2 = [module_intro los nts
      (Ps1 ++ product_fdef (fdef_intro fh (bs1++bs2)) :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.
Proof.
  induction bs2 as [|b0 bs2]; simpl; intros.
    inv Hpass; split; auto using program_sim_refl.

    destruct (in_dec id_dec (getBlockLabel b0) (PI_rd pinfo)).
    Case "reachable".
      remember
        (pass.(iter_block)
          (fdef_intro fh (bs1 ++ b0 :: bs2)) b0 (PI_ctx pinfo) efs) as R.
      destruct R as [[f' []] efs']; inv Hpass; eauto.
        apply iter_block_unchanged in HeqR. destruct HeqR; subst.
        iter_blocks_tac.
    Case "unreachable". 
      iter_blocks_tac.
Qed.

Lemma iter_blocks_sim_wfS: forall fh efs f0 efs0 main VarArgs flag bs
  (pinfo:PhiInfo) (Hwfpi: WF_PhiInfo pinfo)
  (Hpass:IterationPass.iter_blocks pass (fdef_intro fh bs) bs (PI_ctx pinfo) 
    (PI_rd pinfo) efs = (f0, flag, efs0))
  (Heq: PI_f pinfo = fdef_intro fh bs)
  S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++  product_fdef f0 :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef (fdef_intro fh bs) :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs), 
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\ defined_program S1 main VarArgs.
Proof.
  intros until bs.
  rewrite_env (nil ++ bs).
  intros. subst.
  eapply iter_blocks_sim_wfS_aux; eauto.
Qed.

Hypothesis keep_pinfo__PI_ctx: forall f pinfo pinfo',
  keep_pinfo f pinfo pinfo' -> PI_ctx pinfo = PI_ctx pinfo'.

Lemma iter_wfS_wfPI: forall f1 efs1 f2 efs2 main rd
  VarArgs ctx (pinfo:PhiInfo) (Hwfpi: WF_PhiInfo pinfo)
  (Hpass: SafePrimIter.iterate _ (IterationPass.iter_step pass ctx rd) (f1, efs1) 
    = (f2, efs2))
  (Heq1: PI_f pinfo = f1) (Heq2: PI_ctx pinfo = ctx) (Heq2: PI_rd pinfo = rd)
  S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  (program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs) /\
  exists pinfo', WF_PhiInfo pinfo' /\ keep_pinfo f2 pinfo pinfo'.
Proof.
  intros. subst.
  set (P:=fun (re:(fdef * pass.(effects))) =>
          let '(f, _) := re in
          (program_sim [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
            [module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2)]
            main VarArgs /\
           wf_system
            [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] /\
           defined_program 
            [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
            main VarArgs) /\
          exists pinfo', WF_PhiInfo pinfo' /\ keep_pinfo f pinfo pinfo'
       ).
  assert (P (PI_f pinfo, efs1)) as HPf1.
    unfold P.
    split; auto using program_sim_refl. instantiate_pinfo.
  apply SafePrimIter.iterate_prop with (P:=P) in Hpass; auto.
    unfold IterationPass.iter_step.
    intros a HPa.
    destruct a as [f efs].
    unfold IterationPass.iter_fdef.
    destruct f as [fh bs].
    remember (IterationPass.iter_blocks pass (fdef_intro fh bs) bs 
                (PI_ctx pinfo) (PI_rd pinfo) efs) as R.
    destruct R as [[f0 flag0] efs0]; auto.
    assert (P (f0, efs0)) as HPf0.
      unfold P.
      symmetry in HeqR.
      destruct HPa as 
        [[Hsima [HwfSa Hoka]] [pinfo' [HwfPIa Hkeep]]].
      replace (PI_rd pinfo) with (PI_rd pinfo') in HeqR; try solve_keep_pinfo.
      erewrite keep_pinfo__PI_ctx in HeqR; eauto. 
      split.
        apply program_sim_wfS_trans with (P2:=
                [module_intro los nts
                 (Ps1 ++ product_fdef (fdef_intro fh bs) :: Ps2)]); auto.
          intros.
          eapply iter_blocks_sim_wfS in HeqR; eauto; try solve_keep_pinfo.
        eapply iter_blocks_wfPI in HeqR; eauto; try solve_keep_pinfo.

    destruct flag0; auto.
Qed.

End IterationPassSimWFP.

Section IterationPassSimWF. 

Variable (pass:IterPass).

Hypothesis iter_block_unchanged: forall f' efs' f b0 ctx efs,
  (f', false, efs') = pass.(iter_block) f b0 ctx efs ->
  f' = f /\ efs = efs'.

Variable (los:layouts) (nts:namedts) (Ps1 Ps2: products) (rd:list l) 
         (ctx:pass.(context)).

Hypothesis iter_block_wfS: forall fh efs f0 efs0
  main VarArgs bs1 b0 bs2 (Hreach:In (getBlockLabel b0) rd)
  (Hpass : (f0, true, efs0) =
           pass.(iter_block) (fdef_intro fh (bs1 ++ b0 :: bs2)) b0 
             ctx efs) S1 S2
  (Hrd: reachablity_analysis (fdef_intro fh (bs1 ++ b0 :: bs2)) = Some rd)
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f0 :: Ps2)])
  (Heq1: S2 = 
    [module_intro los nts
      (Ps1 ++ product_fdef (fdef_intro fh (bs1 ++ b0 :: bs2)) :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.

Lemma iter_blocks_sim_wfS_aux': forall fh efs f0 efs0 main VarArgs flag bs2 bs1
  (Hpass:IterationPass.iter_blocks pass (fdef_intro fh (bs1++bs2)) bs2 
     ctx rd efs = (f0, flag, efs0))
  (Hrd: reachablity_analysis (fdef_intro fh (bs1 ++ bs2)) = Some rd)
  S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++  product_fdef f0 :: Ps2)])
  (heq2: S2 = [module_intro los nts
      (Ps1 ++ product_fdef (fdef_intro fh (bs1++bs2)) :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs.
Proof.
  induction bs2 as [|b0 bs2]; simpl; intros.
    inv Hpass; split; auto using program_sim_refl.

    destruct (in_dec id_dec (getBlockLabel b0) rd).
    Case "reachable".
      remember
        (pass.(iter_block)
          (fdef_intro fh (bs1 ++ b0 :: bs2)) b0 ctx efs) as R.
      destruct R as [[f' []] efs']; inv Hpass; eauto.
        apply iter_block_unchanged in HeqR. destruct HeqR; subst.
        iter_blocks_tac.
    Case "unreachable". 
      iter_blocks_tac.
Qed.

Lemma iter_blocks_sim_wfS': forall fh efs f0 efs0 main VarArgs flag bs
  (Hpass:IterationPass.iter_blocks pass (fdef_intro fh bs) bs ctx 
    rd efs = (f0, flag, efs0)) S1 S2
  (Hrd: reachablity_analysis (fdef_intro fh bs) = Some rd)
  (Heq1: S1 = [module_intro los nts (Ps1 ++  product_fdef f0 :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef (fdef_intro fh bs) :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs), 
  program_sim S1 S2 main VarArgs /\ wf_system S1 /\ defined_program S1 main VarArgs.
Proof.
  intros until bs.
  rewrite_env (nil ++ bs).
  intros. subst.
  eapply iter_blocks_sim_wfS_aux'; eauto.
Qed.

Hypothesis iter_block_reachablity_successors: forall f b ctx f0
  efs0 efs (Hpass : (f0, true, efs0) = pass.(iter_block) f b ctx efs),
  reachablity_analysis f = reachablity_analysis f0 /\
  successors f = successors f0.

Lemma iter_wfS: forall f1 efs1 f2 efs2 main VarArgs
  (Hpass: SafePrimIter.iterate _ (IterationPass.iter_step pass ctx rd) (f1, efs1) 
    = (f2, efs2))
  (Hrd: reachablity_analysis f1 = Some rd) S1 S2
  (Heq1: S1 = [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)])
  (Heq2: S2 = [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
  (HwfS : wf_system S2) (Hok: defined_program S2 main VarArgs),
  (program_sim S1 S2 main VarArgs /\ wf_system S1 /\
    defined_program S1 main VarArgs) /\
  reachablity_analysis f2 = reachablity_analysis f1 /\
  successors f2 = successors f1.
Proof.
  intros. subst.
  set (P:=fun (re:(fdef * pass.(effects))) =>
          let '(f, _) := re in
          (program_sim [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
            [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]
            main VarArgs /\
           wf_system
            [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)] /\
           defined_program 
            [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
            main VarArgs) /\
         reachablity_analysis f = reachablity_analysis f1 /\
         successors f = successors f1
       ).
  assert (P (f1, efs1)) as HPf1.
    unfold P.
    split; auto using program_sim_refl.
  apply SafePrimIter.iterate_prop with (P:=P) in Hpass; auto.
    unfold IterationPass.iter_step.
    intros a HPa.
    destruct a as [f efs].
    unfold IterationPass.iter_fdef.
    destruct f as [fh bs].
    remember (IterationPass.iter_blocks pass (fdef_intro fh bs) bs 
                ctx rd efs) as R.
    destruct R as [[f0 flag0] efs0]; auto.
    assert (P (f0, efs0)) as HPf0.
      unfold P.
      symmetry in HeqR.
      destruct HPa as [[Hsima [HwfSa Hoka]] [Hreacha Hsucca]].
      rewrite <- Hreacha in Hrd.
      split.
        apply program_sim_wfS_trans with (P2:=
                [module_intro los nts
                 (Ps1 ++ product_fdef (fdef_intro fh bs) :: Ps2)]); auto.
        eapply iter_blocks_sim_wfS' in HeqR; eauto.

        eapply iter_blocks_reachablity_successors in HeqR; eauto.
        destruct HeqR. split; congruence.

    destruct flag0; auto.
Qed.

End IterationPassSimWF.

End IterationPassCorrect.
