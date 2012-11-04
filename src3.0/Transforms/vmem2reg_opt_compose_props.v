Require Import vellvm.
Require Import ListSet.
Require Import primitives.
Require Import palloca_props.
Require Import vmem2reg.
Require Import vmem2reg_opt.

(***************************************************************)
Lemma lookupAL_map_iff: forall A f m id0 ac0,
  lookupAL A (ListMap.map f m) id0 = Some ac0 <->
    exists ac1, ac0 = f ac1 /\ lookupAL A m id0 = Some ac1.
Proof.
  induction m as [|[id1 v1] m]; simpl; intros.
    split; intro J; try congruence.
      destruct J as [ac1 [? J]]; congruence.

    destruct_if.
    split; intro J.
      uniq_result. eauto.

      destruct J as [ac1 [? ?]]; uniq_result; auto.
Qed.

Lemma action_dec: forall (ac1 ac2: action), {ac1 = ac2} + {ac1 <> ac2}.
Proof. decide equality; auto using value_dec, typ_dec. Qed.

Lemma id_action_dec: forall (ia1 ia2: id*action), {ia1 = ia2} + {ia1 <> ia2}.
Proof. decide equality; auto using id_dec, action_dec. Qed.

(***************************************************************)
(* Properties of ListComposedPass.subst_actions *)
Lemma list_subst_actions__uniq: forall id0 ac0 actions (Huniq: uniq actions),
  uniq (ListComposedPass.subst_actions id0 ac0 actions).
Proof.
  unfold ListComposedPass.subst_actions.
  intros. destruct (action2value ac0); auto.
Qed.

Lemma list_subst_actions__dom: forall id0 ac0 actions,
  dom (ListComposedPass.subst_actions id0 ac0 actions) [=] dom actions.
Proof.
  unfold ListComposedPass.subst_actions.
  intros. 
  destruct (action2value ac0); try fsetdec.
    apply dom_map.
Qed.

Lemma list_subst_actions__length: forall id0 ac0 actions,
  length actions = length (ListComposedPass.subst_actions id0 ac0 actions).
Proof.
  unfold ListComposedPass.subst_actions, ListMap.map.
  intros. destruct (action2value ac0); auto.
    erewrite <- List.map_length; eauto.
Qed.

Lemma list_subst_actions_app: forall id0 ac0 actions2 actions1,
  ListComposedPass.subst_actions id0 ac0 (actions1++actions2) = 
    ListComposedPass.subst_actions id0 ac0 actions1++
      ListComposedPass.subst_actions id0 ac0 actions2.
Proof.
  unfold ListComposedPass.subst_actions.
  intros.
  destruct (action2value ac0); auto.
  apply map_app.
Qed.

Lemma list_subst_actions_app_inv: forall id0 ac0 acs acs1' acs2'
  (Heq: ListComposedPass.subst_actions id0 ac0 acs = acs1' ++ acs2'),
  exists acs1, exists acs2,
    acs = acs1 ++ acs2 /\ 
    ListComposedPass.subst_actions id0 ac0 acs1 = acs1' /\
    ListComposedPass.subst_actions id0 ac0 acs2 = acs2'.
Proof.
  unfold ListComposedPass.subst_actions.
  intros.
  destruct (action2value ac0).
    apply map_app_inv; auto.
    subst. eauto.
Qed.

(* If ac contains (fst elt), replace it by (snd elt). *)
Definition subst_action_action (ac:action) (elt:id * action): action :=
let '(id1, ac1) := elt in
match action2value ac1 with
| Some v1 => subst_action id1 v1 ac
| _ => ac
end.

Lemma list_subst_actions_cons_inv: forall id0 ac0 acs id1 ac1' acs2'
  (Heq: ListComposedPass.subst_actions id0 ac0 acs = (id1, ac1') :: acs2'),
  exists ac1, exists acs2,
    acs = (id1, ac1) :: acs2 /\ 
    subst_action_action ac1 (id0, ac0)= ac1' /\
    ListComposedPass.subst_actions id0 ac0 acs2 = acs2'.
Proof.
  unfold ListComposedPass.subst_actions.
  intros.
  case_eq (action2value ac0).
    intros v Heqv. rewrite Heqv in Heq.
    unfold ListMap.map in *.
    apply map_cons_inv in Heq; auto.
    destruct Heq as [[] [x2 [EQ [J1 J2]]]]; subst.
    inv J2.
    exists a0. exists x2.
    split; auto.
    split; auto.
      unfold subst_action_action, subst_action.
      rewrite Heqv. auto.

    intros Heqv. rewrite Heqv in Heq.
    subst. 
    unfold subst_action_action. rewrite Heqv. eauto.
Qed.

(***************************************************************)
(* Substitute actions from left to right. *)
Program Fixpoint substs_actions (pairs: AssocList action) 
  {measure (length pairs)} : AssocList action :=
match pairs with 
| nil => nil
| (id1, ac1)::pairs' => 
    (id1, ac1)::substs_actions (ListComposedPass.subst_actions id1 ac1 pairs')
end.
Next Obligation.
  rewrite <- list_subst_actions__length; simpl; auto.
Qed.

Ltac unfold_substs_actions :=
match goal with
| |- appcontext [substs_actions ?arg] =>
   unfold substs_actions;
   Program.Wf.WfExtensionality.unfold_sub substs_actions arg
end.

(***************************************************************)
(* Properties of find_stld_pairs_cmds *)
Definition ids_in_stld_state (st:stld_state) : list id :=
match st with
| STLD_store i1 _ => [i1]
| _ => nil
end.

Lemma find_stld_pairs_cmds_aux__uniq: forall pid cs s acs
  (Huniq : NoDup (getCmdsLocs cs ++ ids_in_stld_state s ++ List.map fst acs)),
  uniq (snd (fold_left (find_stld_pair_cmd pid) cs (s, acs))).
Proof.
  induction cs as [|c cs]; simpl; intros.
    apply NoDup_fst__uniq; auto.
    split_NoDup; auto.
 
    destruct c; simpl in *; try solve [inv Huniq; apply IHcs; auto].
      destruct_if; try (inv Huniq; apply IHcs; simpl; auto).
        eapply NoDup_strenthening; eauto.

      destruct value1; try (inv Huniq; apply IHcs; simpl; auto).
      destruct_if; try (inv Huniq; apply IHcs; simpl; auto).
      destruct s; try (inv Huniq; apply IHcs; simpl; auto).
        match goal with
        | |- context [?A ++ ?b :: ?c :: ?D] =>
          rewrite_env ((A++[b]) ++ c ::  D)
        end.
        apply NoDup_insert; simpl_env; auto.

        apply NoDup_insert; auto.

      destruct value2; try (inv Huniq; apply IHcs; simpl; auto).
      destruct_if; try (inv Huniq; apply IHcs; simpl; auto).
      destruct s; inv Huniq; apply IHcs; simpl; apply NoDup_insert; auto.
Qed.

Lemma find_stld_pairs_cmds__uniq: forall pid cs actions
  (Huniq: NoDup (getCmdsLocs cs))
  (Hfind: actions = find_stld_pairs_cmds cs pid),
  uniq actions.
Proof.
  unfold find_stld_pairs_cmds.
  intros. subst.
  apply -> uniq__iff__uniq_rev.
  apply find_stld_pairs_cmds_aux__uniq; simpl_env; auto.
Qed.

Definition id_in_stld_state (i0:id) (st:stld_state) : Prop :=
match st with
| STLD_store i1 _ => i0 = i1
| _ => False
end.

Lemma find_stld_pairs_cmds_aux__incl: forall pid cs acs s,
  forall (a : atom) 
  (Hin: a `in` dom (snd (fold_left (find_stld_pair_cmd pid) cs (s, acs)))), 
  In a (getCmdsLocs cs) \/ a `in` dom acs \/ id_in_stld_state a s.
Proof.
  induction cs as [|c cs]; simpl; intros; auto.
    destruct c; simpl; try (apply IHcs in Hin; tauto).
      destruct_if; subst; try (apply IHcs in Hin; tauto).

      destruct value1; try (apply IHcs in Hin; tauto).
      destruct_if; subst; try (apply IHcs in Hin; tauto).
      destruct s; apply IHcs in Hin; simpl in Hin; try tauto;
        destruct Hin; try solve [auto | fsetdec].

      destruct value2; try (apply IHcs in Hin; tauto).
      destruct_if; subst; try (apply IHcs in Hin; tauto).
      destruct s; apply IHcs in Hin; simpl in Hin; simpl;
        destruct Hin; try solve [auto | fsetdec].
Qed.

Lemma find_stld_pairs_cmds__incl: forall pid cs,
  forall (a : atom) (Hin: a `in` dom (find_stld_pairs_cmds cs pid)), 
  In a (getCmdsLocs cs).
Proof.
  unfold find_stld_pairs_cmds.
  intros.
  apply in_dom__iff__in_rev_dom in Hin.
  apply find_stld_pairs_cmds_aux__incl in Hin.
  simpl in Hin. 
  destruct Hin as [Hin | [Hin | Hin]]; auto.
    fsetdec. tauto.
Qed.

(* Properties of find_stld_pairs_blocks *)
Lemma find_stld_pairs_block__uniq: forall pid rd b actions
  (Huniq: NoDup (getStmtsLocs (snd b)))
  (Hfind: actions = find_stld_pairs_block pid rd b),
  uniq actions.
Proof.
  destruct b as [? []]. simpl.
  intros.
  destruct_if; auto.
    split_NoDup.
    eapply find_stld_pairs_cmds__uniq; eauto.
Qed.

Lemma find_stld_pairs_block__incl: forall pid rd b,
  forall (a : atom) (Hin: a `in` dom (find_stld_pairs_block pid rd b)), 
  In a (getStmtsLocs (snd b)).
Proof.
  destruct b as [? []]. simpl.
  destruct_if; intros.
    apply find_stld_pairs_cmds__incl in Hin.
    xsolve_in_list.

    simpl in Hin. fsetdec.
Qed.

Lemma find_stld_pairs_blocks__incl: forall pid rd bs,
  forall a : atom,
  a `in` dom (flat_map (find_stld_pairs_block pid rd) bs) -> 
  In a (getBlocksLocs bs).
Proof.
  induction bs as [|b bs]; simpl; intros; subst.
    fsetdec.
    
    apply in_or_app.
    rewrite dom_app in H.
    apply AtomSetFacts.union_iff in H.
    destruct H as [H | H]; eauto using find_stld_pairs_block__incl.
Qed.

Lemma find_stld_pairs_blocks__uniq: forall pid rd bs actions
  (Huniq: NoDup (getBlocksLocs bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs),
  uniq actions.
Proof.
  induction bs as [|b bs]; simpl; intros; subst.
    constructor.

    apply uniq_app_iff.
    assert (J:=Huniq).
    apply NoDup_split in J. destruct J as [J1 J2].
    split.
      eapply find_stld_pairs_block__uniq; eauto.
    split; auto.
      apply disj__disjoint with (A1:=getStmtsLocs (snd b)) (B1:=getBlocksLocs bs); 
        auto.
        intros. eapply NoDup_disjoint'; eauto.
        apply find_stld_pairs_block__incl; auto.
        apply find_stld_pairs_blocks__incl; auto.
Qed.

Lemma find_stld_pairs_blocks__split: forall pid rd bs acs1 ac acs2
  (Hmap: flat_map (find_stld_pairs_block pid rd) bs = acs1 ++ ac :: acs2),
  exists b, exists bs1, exists bs2,
  exists acs11, exists acs12, exists acs21, exists acs22,
    bs = bs1 ++ b :: bs2 /\
    acs1 = acs11 ++ acs12 /\
    acs2 = acs21 ++ acs22 /\
    find_stld_pairs_block pid rd b = acs12 ++ ac :: acs21 /\
    flat_map (find_stld_pairs_block pid rd) bs1 = acs11 /\
    flat_map (find_stld_pairs_block pid rd) bs2 = acs22.
Proof.
  induction bs as [|b bs]; simpl; intros.
    symmetry in Hmap. contradict Hmap. apply app_cons_not_nil.

    apply app_split in Hmap.
    destruct Hmap as [[u1 [u2 [J1 [J2 J3]]]]|[z1 [z2 [J1 [J2 J3]]]]].
      exists b. exists nil. exists bs. exists nil. exists acs1. 
      exists u1. exists u2. simpl. eauto 10.

      apply_clear IHbs in J2.
      destruct J2 as 
        [b0 [bs1 [bs2 [acs11 [acs12 [acs21 [acs22 [J2 
          [J7 [J4 [J5 [J6 J8]]]]]]]]]]]]; subst.
      exists b0. exists (b::bs1). exists bs2.
      exists (find_stld_pairs_block pid rd b ++ 
              flat_map (find_stld_pairs_block pid rd) bs1).
      exists acs12. exists acs21.
      exists (flat_map (find_stld_pairs_block pid rd) bs2).
      simpl_env. split; auto.
Qed.

Lemma find_stld_pairs_block__reach: forall pid rd l0 sts0
  acs1 ac acs2
  (Hfind: find_stld_pairs_block pid rd (l0, sts0) =
            acs1 ++ ac :: acs2),
  In l0 rd.
Proof.
  simpl. intros.
  destruct_if; auto.
    symmetry in H0. contradict H0. destruct sts0. apply app_cons_not_nil.
Qed.

Lemma find_stld_pairs_block__reach': forall (fh : fheader) (bs : blocks)
  (HuniqF : uniqFdef (fdef_intro fh bs)) (pid : id) (rd : list l) (id0 : atom)
  (Hin : id0 `in` dom (flat_map (find_stld_pairs_block pid rd) bs)),
  exists l0 : l, exists sts0 : stmts,
    blockInFdefB (l0, sts0) (fdef_intro fh bs) /\
    In id0 (getStmtsLocs sts0) /\
    In l0 rd.
Proof.
  intros.
  apply binds_In_inv in Hin.
  destruct Hin as [a Hin].
  unfold binds in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [b [Hin1 Hin2]].
  assert (J:=Hin2).
  apply binds_In in J.
  apply find_stld_pairs_block__incl in J.
  destruct b as [l0 sts0].
  exists l0. exists sts0.
  split. simpl. solve_in_list.
  split; auto.
    apply in_split in Hin2.
    destruct Hin2 as [l1 [l2 Hfind]].   
    apply find_stld_pairs_block__reach in Hfind; auto.
Qed.

Lemma find_stld_pairs_block__reach'': forall (fh : fheader) (bs : blocks)
  (HuniqF : uniqFdef (fdef_intro fh bs)) (pid : id) (rd : list l) (id0 : atom)
  (l0 : l) (sts0 : stmts)
  (H : lookupBlockViaIDFromFdef (fdef_intro fh bs) id0 = ret (l0, sts0))
  (Hin : id0 `in` dom (flat_map (find_stld_pairs_block pid rd) bs)),
  In l0 rd.
Proof.
  intros.
  eapply find_stld_pairs_block__reach' in Hin; eauto.
  destruct Hin as [l1 [sts1 [J1 [J2 J3]]]].
  assert (J':=H).
  apply lookupBlockViaIDFromBlocks__InGetBlockIDs in J'.
  apply in_getStmtsIDs__in_getStmtsLocs in J'.
  assert ((l1, sts1) = (l0, sts0)) as EQ.
    eapply block_eq2; eauto 1.
      solve_blockInFdefB.
  inv EQ. auto.
Qed.

(***************************************************************)
(* Properties of find_next_stld *)
Lemma find_next_stld_strengthen: forall cs2 pid cs1 
  (Hnst: store_in_cmds pid cs1 = false)
  (Hnld: load_in_cmds pid cs1 = false),
  find_next_stld cs2 pid = find_next_stld (cs1++cs2) pid.
Proof.
  induction cs1 as [|c cs1]; simpl; intros; auto.
    apply store_in_cmds_false_cons_inv in Hnst.
    destruct Hnst as [Hnst1 Hnst2].
    apply load_in_cmds_false_cons_inv in Hnld.
    destruct Hnld as [Hnld1 Hnld2].
    destruct c; auto.
      destruct value1; auto.
      destruct_if.
      simpl in Hnld1.
      destruct (id_dec id0 id0); simpl in Hnld1; try congruence.

      destruct value2; auto.
      destruct_if.
      simpl in Hnst1.
      destruct (id_dec id0 id0); simpl in Hnst1; try congruence.   
Qed.

(* Properties of find_next_stld_inl *)
Lemma find_init_stld_inl_remove_neq_spec: forall dones id' pid cs1 v2 id2 cs2
  (Hneq: id2 <> id')
  (Hst : Some (inl (id2, v2, cs2)) = find_init_stld cs1 pid dones),
  Some (inl (id2, v2, remove_cmds id' cs2)) =
             find_init_stld (remove_cmds id' cs1) pid dones.
Proof.
  induction cs1 as [|c cs1]; simpl; intros.
    congruence.

    destruct (id_dec (getCmdLoc c) id'); subst; simpl.
    Case "1".
      destruct c; auto.
      SCase "1.1".
        destruct_if; auto.
        destruct_if; auto.
      SCase "1.2".
        destruct value2; auto.
        destruct_if; auto.
        destruct_if; auto.
          simpl in Hneq. congruence.
    Case "2".
      destruct c; auto.
      SCase "1.1".
        destruct_if; auto.
        destruct_if; auto.
      SCase "1.2".
        destruct value2; auto.
        destruct_if; auto.
        destruct_if; auto.
Qed.

Lemma find_init_stld_inl_in: forall (cs5 : cmds) (id' : atom) (v0 : value)
  (cs0 : cmds) (dones : list id) pinfo
  (Hfind : ret inl (id', v0, cs0) = find_init_stld cs5 (PI_id pinfo) dones),
  In id' (getCmdsLocs cs5).
Proof.
  intros.
  apply find_init_stld_inl_spec in Hfind.
  destruct Hfind as [cs1 [ty1 [al1 Hst]]]; subst.
  rewrite getCmdsLocs_app. simpl. xsolve_in_list.
Qed.

Lemma find_next_stld_inl_spec': forall pid i1 cs
 (H: ret inl i1 = find_next_stld cs pid),
 exists cs1, exists cs2, exists ty, exists al,
   cs = cs1 ++
          insn_load i1 ty (value_id pid) al :: cs2 /\
   store_in_cmds pid cs1 = false /\
   load_in_cmds pid cs1 = false.
Proof.
  induction cs; simpl; intros.
    congruence.

    destruct a; try find_next_stld_spec_tac.
      destruct value1; try solve [find_next_stld_spec_tac].
      destruct_if.
        exists nil. exists cs. exists typ5. exists align5.
        split; auto.

        find_next_stld_spec_tac.
        destruct H2. split; auto.
        split.
          apply store_in_cmds_false_cons_intro; auto.
          apply load_in_cmds_false_cons_intro; auto.
            simpl. destruct_dec.
 
      destruct value2; try solve [find_next_stld_spec_tac].
      destruct_if; try find_next_stld_spec_tac.
        destruct H2.
        split; auto. 
        split.
          simpl_env.
          apply store_in_cmds_merge.
          split; auto. 
            unfold store_in_cmds. simpl.
            destruct_dec. 
          apply load_in_cmds_false_cons_intro; auto.
Qed.

Lemma find_next_stld_inl_remove_neq_spec: forall id' pid cs1 id3
  (Hneq: id3 <> id')
  (Hst : Some (inl id3) = find_next_stld cs1 pid),
  Some (inl id3) = find_next_stld (remove_cmds id' cs1) pid.
Proof.
  induction cs1 as [|c cs1]; simpl; intros; auto.
    destruct (id_dec (getCmdLoc c) id'); subst; simpl.
    Case "1".
      destruct c; auto.
      SCase "1.1".
        destruct value1; auto.
        destruct_if; auto.
          simpl in Hneq. congruence.
      SCase "1.2".
        destruct value2; auto.
        destruct_if; auto.
    Case "2".
      destruct c; auto.
      SCase "2.1".
        destruct value1; auto.
        destruct_if; auto.
      SCase "2.2".
        destruct value2; auto.
        destruct_if; auto.
Qed.

Lemma find_init_stld_inl_subst_spec: forall dones id' v' pid cs1 v2 id2 cs2
  (Hnused: used_in_value pid v' = false) (Hneq: id' <> pid) 
  (Hst : Some (inl (id2, v2, cs2)) = find_init_stld cs1 pid dones),
  Some (inl (id2, subst_value id' v' v2, List.map (subst_cmd id' v') cs2)) =
             find_init_stld (List.map (subst_cmd id' v') cs1) pid dones.
Proof.
  induction cs1 as [|c cs1]; simpl; intros.
    congruence.

    destruct c; simpl; auto.
    Case "1.1".
      destruct_if; auto.
      destruct_if; auto.
    Case "1.2".
      destruct value2; simpl; auto.
      destruct_if; auto.
      destruct_if; auto.
      destruct (id_dec id0 id'); subst.
        destruct v'.
          simpl in Hnused.
          destruct_if. 
            destruct_if; auto. congruence.
            destruct_if; auto. 
              destruct (id_dec id0 id0); simpl in Hnused; try congruence.

          destruct_if; auto. 
            congruence.
           
        destruct_if; auto.
Qed.

Lemma find_next_stld_inl_subst_spec: forall id' v' pid cs1 id3
  (Hnused: used_in_value pid v' = false) (Hneq: id' <> pid) 
  (Hst : Some (inl id3) = find_next_stld cs1 pid),
  Some (inl id3) = find_next_stld (List.map (subst_cmd id' v') cs1) pid.
Proof.
  induction cs1 as [|c cs1]; simpl; intros.
    congruence.

    destruct c; simpl; auto.
    Case "1.1".
      destruct value1; simpl; auto.
      destruct (id_dec id0 id'); subst.
        destruct v'.
          simpl in Hnused.
          destruct (id_dec pid id0); subst.
            destruct (id_dec id0 id0); simpl in Hnused; try congruence.
            destruct_if; auto. congruence.
          destruct_if; auto. congruence.
        destruct_if; auto. 
    Case "1.2".
      destruct value2; simpl; auto.
      destruct (id_dec id0 id'); subst.
        destruct v'.
          simpl in Hnused.
          destruct_if. 
          destruct_if; auto. 
            destruct (id_dec id0 id0); simpl in Hnused; try congruence.

          destruct_if; auto. 
        destruct_if; auto.
Qed.

Lemma find_init_stld_inl_doesnt_use_pid: forall pinfo l5 ps5 cs5 tmn5 dones
  (Hwfpi: WF_PhiInfo pinfo)
  (Huniq : uniqFdef (PI_f pinfo)) s m (HwfF: wf_fdef s m (PI_f pinfo))
  (HBinF : blockInFdefB (l5, stmts_intro ps5 cs5 tmn5) (PI_f pinfo) = true)
  id' v' cs0
  (Hst: Some (inl (id', v', cs0)) = find_init_stld cs5 (PI_id pinfo) dones),
  used_in_value (PI_id pinfo) v' = false /\ id' <> (PI_id pinfo).
Proof.
  intros.
  apply find_init_stld_inl_spec in Hst.
  destruct Hst as [cs1 [ty [al EQ]]]; subst.
  split.
    eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HBinF; eauto 1 using in_middle.
    apply WF_PhiInfo_spec4 with (v0:=v') in HBinF; auto.

    apply WF_PhiInfo_spec10 in HBinF; auto.
Qed.

Lemma find_init_stld_inl_intro_aux: forall id0 v cs4 ty0 al0 pid dones cs3
  (Hinc: incl (getCmdsLocs cs3) dones) 
  (Huniq: NoDup (dones ++ id0 :: getCmdsLocs cs4)),
  Some (inl (id0, v, cs4)) =
     find_init_stld
       (cs3 ++ insn_store id0 ty0 v (value_id pid) al0 :: cs4) pid
       dones.
Proof.
  induction cs3 as [|c3 cs3]; simpl; intros.
    destruct_if.
      eapply NoDup_disjoint' in Huniq; eauto.
      contradict Huniq; simpl; auto.

      destruct_if. congruence.

    destruct c3; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
        clear HeqR.
        contradict n. apply Hinc. simpl; auto.

      destruct value2 as [qid|]; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
        clear HeqR.
        contradict n. apply Hinc. simpl; auto.
Qed.

Lemma find_init_stld_inl_intro: forall id0 v cs4 ty0 al0 pid cs3
  (Huniq: NoDup (getCmdsLocs cs3 ++ id0 :: getCmdsLocs cs4)),
  Some (inl (id0, v, cs4)) =
     find_init_stld
       (cs3 ++ insn_store id0 ty0 v (value_id pid) al0 :: cs4) pid
       (getCmdsLocs cs3).
Proof.
  intros.
  apply find_init_stld_inl_intro_aux; auto with datatypes v62.
Qed.

Lemma find_init_stld_inl_in': forall (cs5 : cmds) (id' : atom) (v0 : value)
  (dones : list id) pinfo cs01 c0 cs02
  (Hfind : ret inl (id', v0, cs01 ++ c0 :: cs02) = 
             find_init_stld cs5 (PI_id pinfo) dones),
  In c0 cs5.
Proof.
  intros.
  apply find_init_stld_inl_spec in Hfind.
  destruct Hfind as [cs1 [ty1 [al1 Hst]]]; subst.
  xsolve_in_list.
Qed.

Lemma find_next_stld_inl_intro: forall c0 cs01 pid cs02
  (Hnst : store_in_cmds pid cs01 = false)
  (Hld : load_in_cmd pid c0 = true) (Hnld : load_in_cmds pid cs01 = false),
  ret inl (getCmdLoc c0) = find_next_stld (cs01 ++ c0 :: cs02) pid.
Proof.
  intros.
  rewrite <- find_next_stld_strengthen; auto.
  destruct c0; tinv Hld.
  destruct value1; tinv Hld.
  simpl in Hld. simpl.
  destruct (id_dec id0 pid); subst; tinv Hld.
  destruct_if; eauto.
    congruence.
Qed.

(* Properties of find_next_stld_inr *)
Lemma find_next_stld_inr_remove_neq_spec: forall id' pid cs1 v3 id3
  (Hneq: id3 <> id')
  (Hst : Some (inr (id3, v3)) = find_next_stld cs1 pid),
  Some (inr (id3, v3)) = find_next_stld (remove_cmds id' cs1) pid.
Proof.
  induction cs1 as [|c cs1]; simpl; intros; auto.
    destruct (id_dec (getCmdLoc c) id'); subst; simpl.
    Case "1".
      destruct c; auto.
      SCase "1.1".
        destruct value1; auto.
        destruct_if; auto.
      SCase "1.2".
        destruct value2; auto.
        destruct_if; auto.
          simpl in Hneq. congruence.
    Case "2".
      destruct c; auto.
      SCase "2.1".
        destruct value1; auto.
        destruct_if; auto.
      SCase "2.2".
        destruct value2; auto.
        destruct_if; auto.
Qed.

Lemma find_next_stld_inr_in: forall (cs5 : cmds) (id' : atom) (v0 : value)
  pinfo
  (Hfind : ret inr (id', v0) = find_next_stld cs5 (PI_id pinfo)),
  In id' (getCmdsLocs cs5).
Proof.
  intros.
  apply find_next_stld_inr_spec in Hfind.
  destruct Hfind as [cs1 [cs2 [ty1 [al1 [J1 J2]]]]]; subst.
  rewrite getCmdsLocs_app. simpl. xsolve_in_list.
Qed.

Lemma find_next_stld_inr_spec': forall pinfo i1 v0 cs
 (H: ret inr (i1, v0) = find_next_stld cs (PI_id pinfo)),
 exists cs1, exists cs2, exists ty, exists al,
   cs = cs1 ++
          insn_store i1 ty v0 (value_id (PI_id pinfo)) al :: cs2 /\
   load_in_cmds (PI_id pinfo) cs1 = false /\
   store_in_cmds (PI_id pinfo) cs1 = false.
Proof.
  induction cs; simpl; intros.
    congruence.

    destruct a; try find_next_stld_spec_tac.
      destruct value1; try solve [find_next_stld_spec_tac].
      destruct_if.
        find_next_stld_spec_tac.
        destruct H2.
        split; auto. 
        split.
          simpl_env.
          apply load_in_cmds_merge.
          split; auto. 
            unfold load_in_cmds. simpl.
            destruct (id_dec id0 (PI_id pinfo)); try solve [auto | congruence].

          simpl_env.
          apply store_in_cmds_merge.
          split; auto. 

      destruct value2; try solve [find_next_stld_spec_tac].
      repeat (destruct_if; try solve [find_next_stld_spec_tac]).
      exists nil. exists cs. exists typ5. exists align5.
      split; auto.

      find_next_stld_spec_tac.
      destruct H2.      
      repeat split; auto.
        unfold store_in_cmds. simpl.
        destruct (id_dec id0 (PI_id pinfo)); try solve [auto | congruence].
Qed.


Lemma find_init_stld_inr_subst_spec: forall dones id' v' pid cs1 v2 cs2
  (Hnused: used_in_value pid v' = false)
  (Hst : Some (inr (v2, cs2)) = find_init_stld cs1 pid dones),
  Some (inr (subst_value id' v' v2, List.map (subst_cmd id' v') cs2)) =
             find_init_stld (List.map (subst_cmd id' v') cs1) pid dones.
Proof.
  induction cs1 as [|c cs1]; simpl; intros.
    congruence.

    destruct c; simpl; auto.
    Case "1.1".
      destruct_if; auto.
      destruct_if; auto.
    Case "1.2".
      destruct value2; simpl; auto.
      destruct (id_dec id0 id'); subst.
        destruct v'.
          simpl in Hnused.
          destruct_if; auto.
          destruct_if; auto. 
          destruct_if; auto. 
            destruct (id_dec id0 id0); simpl in Hnused; try congruence.

          destruct_if; auto. 
          destruct_if; auto. 
           
        destruct_if; auto.
        destruct_if; auto.
Qed.

Lemma find_init_stld_inr_remove_neq_spec: forall dones id' pid cs1 v2 cs2
  (Hneq: pid <> id')
  (Hst : Some (inr (v2, cs2)) = find_init_stld cs1 pid dones),
  Some (inr (v2, remove_cmds id' cs2)) =
             find_init_stld (remove_cmds id' cs1) pid dones.
Proof.
  induction cs1 as [|c cs1]; simpl; intros.
    congruence.

    destruct (id_dec (getCmdLoc c) id'); subst; simpl.
    Case "1".
      destruct c; auto.
      SCase "1.1".
        destruct_if; auto.
        destruct_if; auto.
          simpl in Hneq. congruence.
      SCase "1.2".
        destruct value2; auto.
        destruct_if; auto.
        destruct_if; auto.
    Case "2".
      destruct c; auto.
      SCase "1.1".
        destruct_if; auto.
        destruct_if; auto.
      SCase "1.2".
        destruct value2; auto.
        destruct_if; auto.
        destruct_if; auto.
Qed.
        
Lemma find_next_stld_inr_subst_spec: forall id' v' pid cs1 v3 id3
  (Hnused: used_in_value pid v' = false) (Hneq: id' <> pid) 
  (Hst : Some (inr (id3, v3)) = find_next_stld cs1 pid),
  Some (inr (id3, v3 {[v' // id']})) = 
    find_next_stld (List.map (subst_cmd id' v') cs1) pid.
Proof.
  induction cs1 as [|c cs1]; simpl; intros.
    congruence.

    destruct c; simpl; auto.
    Case "1.1".
      destruct value1; simpl; auto.
      destruct_if; auto.
      destruct (id_dec id0 id'); subst.
        destruct v'; auto.
          simpl in Hnused.
          destruct_if; auto. 
            destruct (id_dec id0 id0); simpl in Hnused; try congruence.

        destruct_if; auto. congruence.
    Case "1.2".
      destruct value2; simpl; auto.
      destruct (id_dec id0 id'); subst.
        destruct v'.
          simpl in Hnused.
          destruct_if. 
            destruct_if; auto. congruence.
            destruct_if; auto. 
              destruct (id_dec id0 id0); simpl in Hnused; try congruence.

          destruct_if; auto. 
            congruence.
           
        destruct_if; auto.
Qed.

Lemma find_init_stld_inr_intro_aux: forall cs4 t num0 al0 pid dones cs3
  (Hinc: incl (getCmdsLocs cs3) dones) 
  (Huniq: NoDup (dones ++ pid :: getCmdsLocs cs4)),
  Some (inr (value_const (const_undef t), cs4)) =
     find_init_stld
       (cs3 ++ insn_alloca pid t num0 al0 :: cs4) pid
       dones.
Proof.
  induction cs3 as [|c3 cs3]; simpl; intros.
    destruct_if.
      eapply NoDup_disjoint' in Huniq; eauto.
      contradict Huniq; simpl; auto.

      destruct_if. congruence.

    destruct c3; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
        clear HeqR.
        contradict n. apply Hinc. simpl; auto.

      destruct value2 as [qid|]; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
      destruct_if; try (apply IHcs3; eauto with datatypes v62).
        clear HeqR.
        contradict n. apply Hinc. simpl; auto.
Qed.

Lemma find_init_stld_inr_intro: forall cs4 t num0 al0 pid cs3
  (Huniq: NoDup (getCmdsLocs cs3 ++ pid :: getCmdsLocs cs4)),
  Some (inr (value_const (const_undef t), cs4)) =
     find_init_stld
       (cs3 ++ insn_alloca pid t num0 al0 :: cs4) pid
       (getCmdsLocs cs3).
Proof.
  intros.
  apply find_init_stld_inr_intro_aux; auto with datatypes v62.
Qed.

Lemma find_next_stld_inr_intro: forall c0 cs01 pid cs02
  (Hnst : store_in_cmds pid cs01 = false)
  (Hst : store_in_cmd pid c0 = true) (Hnld : load_in_cmds pid cs01 = false),
  exists v1 : value,
    ret inr (getCmdLoc c0, v1) = find_next_stld (cs01 ++ c0 :: cs02) pid.
Proof.
  intros.
  rewrite <- find_next_stld_strengthen; auto.
  destruct c0; tinv Hst.
  destruct value2; tinv Hst.
  simpl in Hst. simpl.
  destruct (id_dec id0 pid); subst; tinv Hst.
  destruct_if; eauto.
    congruence.
Qed.

(* Properties of finding SAS. *)
Lemma find_st_ld__sas_in: forall cs0 i0 v cs dones pinfo
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones) v0
  (i1 : id) (Hld : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo)),
  In i1 (getCmdsLocs cs0).
Proof.
  intros.
  apply find_init_stld_inl_spec in Hst.
  destruct Hst as [cs1 [ty1 [al1 Hst]]]; subst.
  apply find_next_stld_inr_in in Hld.
  rewrite getCmdsLocs_app. simpl. xsolve_in_list.
Qed.

Lemma find_st_ld__sas_spec: forall cs0 i0 v cs dones pinfo
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones) v0
  (i1 : id) (Hld : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo)),
  exists cs1 : list cmd, exists ty0 : typ, exists al0 : align,
    cs0 = cs1 ++ insn_store i0 ty0 v (value_id (PI_id pinfo)) al0 :: cs /\
  exists cs2 : list cmd, exists cs3 : list cmd,
    exists ty1 : typ, exists al1 : align,
    cs = cs2 ++ insn_store i1 ty1 v0 (value_id (PI_id pinfo)) al1 :: cs3 /\
    load_in_cmds (PI_id pinfo) cs2 = false /\
    store_in_cmds (PI_id pinfo) cs2 = false.
Proof.
  intros.
  apply find_init_stld_inl_spec in Hst.
  destruct Hst as [cs1 [ty1 [al1 Hst]]]; subst.
  apply find_next_stld_inr_spec' in Hld.
  destruct Hld as [cs2 [cs3 [ty2 [al2 [Hld [J1 J2]]]]]]; subst.
  eauto 11.
Qed.

(* Properties of finding LAS. *)
Require Import trans_tactic.

Lemma find_st_ld__las_spec: forall cs0 i0 v cs dones pinfo
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones) 
  (i1 : id) (Hld : ret (inl i1) = find_next_stld cs (PI_id pinfo)),
  exists cs1 : list cmd, exists ty0 : typ, exists al0 : align,
    cs0 = cs1 ++ insn_store i0 ty0 v (value_id (PI_id pinfo)) al0 :: cs /\
  exists cs2, exists cs3, exists ty1, exists al1,
    cs = cs2 ++ insn_load i1 ty1 (value_id (PI_id pinfo)) al1 :: cs3 /\
    store_in_cmds (PI_id pinfo) cs2 = false /\
    load_in_cmds (PI_id pinfo) cs2 = false.
Proof.
  intros.
  apply find_init_stld_inl_spec in Hst.
  destruct Hst as [cs1 [ty1 [al1 Hst]]]; subst.
  apply find_next_stld_inl_spec' in Hld.
  destruct Hld as [cs2 [cs3 [ty2 [al2 [Hld [J1 J2]]]]]]; subst.
  eauto 11.
Qed.

Lemma find_st_ld_las_doesnt_use_pid: forall pinfo l5 ps5 cs5 tmn5 dones
  (Hwfpi: WF_PhiInfo pinfo)
  (Huniq : uniqFdef (PI_f pinfo)) s m (HwfF: wf_fdef s m (PI_f pinfo))
  (HBinF : blockInFdefB (l5, stmts_intro ps5 cs5 tmn5) (PI_f pinfo) = true)
  id' v' cs0 id0
  (Hst: Some (inl (id0, v', cs0)) = find_init_stld cs5 (PI_id pinfo) dones)
  (Hld: ret inl id' = find_next_stld cs0 (PI_id pinfo)),
  used_in_value (PI_id pinfo) v' = false /\ id' <> (PI_id pinfo).
Proof.
  intros.
  eapply find_st_ld__las_spec in Hst; eauto.
  destruct Hst as [cs1 [ty [al [EQ [cs2 [cs3 [ty1 [al1 [EQ1 [J1 J2]]]]]]]]]]; 
    subst.
  split.
    eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HBinF; eauto 1 using in_middle.
    apply WF_PhiInfo_spec4 with (v0:=v') in HBinF; auto.

    match goal with
    | H: context [?A ++ ?b :: ?C ++ ?d :: ?E] |- _ =>
      rewrite_env ((A++b::C)++d::E) in H;
      apply WF_PhiInfo_spec10 in H; auto
    end.
Qed.

(* Properties of finding LAA. *)
Lemma find_st_ld_laa_doesnt_use_pid: forall pinfo l5 ps5 cs5 tmn5 dones
  (Hwfpi: WF_PhiInfo pinfo)
  (Huniq : uniqFdef (PI_f pinfo)) s m (HwfF: wf_fdef s m (PI_f pinfo))
  (HBinF : blockInFdefB (l5, stmts_intro ps5 cs5 tmn5) (PI_f pinfo) = true)
  id' v' cs0
  (Hst: Some (inr (v', cs0)) = find_init_stld cs5 (PI_id pinfo) dones)
  (Hld: ret inl id' = find_next_stld cs0 (PI_id pinfo)),
  used_in_value (PI_id pinfo) v' = false /\ id' <> (PI_id pinfo).
Proof.
  intros.
  apply find_init_stld_inr_spec in Hst.
  destruct Hst as [cs1 [ty1 [num1 [al1 [EQ Hst]]]]]; subst.
  apply find_next_stld_inl_spec' in Hld.
  destruct Hld as [cs2 [cs3 [ty2 [al2 [Hld [J1 J2]]]]]]; subst.
  split.
    simpl. auto.

    match goal with
    | H: context [?A ++ ?b :: ?C ++ ?d :: ?E] |- _ =>
      rewrite_env ((A++b::C)++d::E) in H;
      apply WF_PhiInfo_spec10 in H; auto
    end.
Qed.

(***************************************************************)

Definition loads_must_be_in_pre (acs: AssocList action) (pid:id) (cs:cmds)
  : Prop :=
Forall (fun c => load_in_cmd pid c = true -> getCmdLoc c `in` dom acs) cs.

Lemma filter_pres_loads_must_be_in_pre: forall acs check pid cs
  (Hnld: loads_must_be_in_pre acs pid cs),
  loads_must_be_in_pre acs pid (filter check cs).
Proof.
  induction 1; simpl; intros.
    constructor.

    destruct_if.
    constructor; auto.
Qed.

Lemma no_loads__loads_must_be_in_pre: forall pid acs cs
  (H: load_in_cmds pid cs = false),
  loads_must_be_in_pre acs pid cs.
Proof.
  induction cs as [|c cs]; intros.
    constructor.

    apply load_in_cmds_false_cons_inv in H.
    destruct H as [H1 H2].
    constructor.
      intros. congruence.
      apply IHcs; auto.
Qed.

Lemma loads_must_be_in_pre_merge: forall acs pid cs1 cs2
  (Hlds1: loads_must_be_in_pre acs pid cs1) 
  (Hlds2: loads_must_be_in_pre acs pid cs2),
  loads_must_be_in_pre acs pid (cs1 ++ cs2).
Proof.
  unfold loads_must_be_in_pre.
  intros.
  apply Forall_app; auto.
Qed.

Lemma loads_must_be_in_pre_load_in_cmds_false__loads_must_be_in_pre: 
  forall acs pid cs1 cs2
  (Hlds1: loads_must_be_in_pre acs pid cs1) 
  (Hlds2: load_in_cmds pid cs2 = false),
  loads_must_be_in_pre acs pid (cs1 ++ cs2).
Proof.
  intros.
  apply loads_must_be_in_pre_merge; auto.
  apply no_loads__loads_must_be_in_pre; auto.
Qed.

Lemma remove_pres_loads_must_be_in_pre: forall id' ac' actions pid cs
  (Hld: loads_must_be_in_pre ((id', ac') :: actions) pid cs),
  loads_must_be_in_pre actions pid 
    (filter (fun c : cmd => negb (id_dec (getCmdLoc c) id')) cs).
Proof.
  induction 1; simpl; intros.
    constructor.

    destruct_dec; simpl.
      constructor; auto.
        intros Heq. apply H in Heq.
        simpl in Heq. fsetdec.
Qed.

Lemma loads_must_be_in_nil__no_loads: forall pid cs 
  (H: loads_must_be_in_pre nil pid cs), load_in_cmds pid cs = false.
Proof.
  induction 1; simpl; auto.
    apply load_in_cmds_false_cons_intro; auto.
      case_eq (load_in_cmd pid x); auto.
        intro Heq.
        apply H in Heq. fsetdec.
Qed.

Lemma loads_must_be_in_pre_append: forall acs pid cs3 c
  (Hlds: loads_must_be_in_pre acs pid cs3) (Hld: load_in_cmd pid c = false),
  loads_must_be_in_pre acs pid (cs3 ++ [c]).
Proof.
  intros.
  apply Forall_forall.
  intros x Hinx H.
  destruct_in Hinx.
    eapply Forall_forall in Hlds; eauto.
    destruct_in Hinx. congruence.
Qed.

Lemma loads_must_be_in_pre_weaken: forall acs1 acs2 pid cs 
  (Hlds: loads_must_be_in_pre acs2 pid cs),
  loads_must_be_in_pre (acs1++acs2) pid cs.
Proof.
  induction 1; constructor; auto.
    intro Heq. apply H in Heq. rewrite dom_app. auto.
Qed.

Lemma loads_must_be_in_pre_append': forall ac acs pid cs3 c
  (Hlds: loads_must_be_in_pre acs pid cs3) (Hld: load_in_cmd pid c = true)
  (Heq: fst ac = getCmdLoc c),
  loads_must_be_in_pre ([ac]++acs) pid (cs3 ++ [c]).
Proof.
  intros.
  apply Forall_forall.
  intros x Hinx H.
  destruct_in Hinx.
    eapply Forall_forall in Hlds; eauto.
    apply Hlds in H. simpl_env. auto.

    destruct_in Hinx. 
      destruct ac. simpl in *. subst. auto.
Qed.

Lemma loads_must_be_in_pre_rev: forall acs pid cs
  (Hwf: loads_must_be_in_pre (rev acs) pid cs),
  loads_must_be_in_pre acs pid cs.
Proof.
  unfold loads_must_be_in_pre. intros.
  apply Forall_forall. intros x Hinx Heq.
  eapply Forall_forall in Hwf; eauto.
  apply Hwf in Heq.
  apply binds_In_inv in Heq.
  destruct Heq as [ac Heq].
  apply binds_In with (a:=ac); auto.
  unfold binds in *.
  apply in_rev; auto.
Qed.

(***************************************************************)
(* cs: a list of commands in a block
   pid: the promotable id 
   elt: an elimination action 

   elt is well-formed if the micro step is found in cs. *)
Definition wf_cs_action (cs:cmds) (pid:id) (elt:id * action): Prop :=
let '(id', ac') := elt in
match ac' with
| AC_remove =>  
    exists v0, exists cs0, exists id1, exists v1, exists dones,
      Some (inl (id', v0, cs0)) = find_init_stld cs pid dones /\
      Some (inr (id1, v1)) = find_next_stld cs0 pid
| AC_vsubst v' =>  
    exists id0, exists cs0, exists dones,
      Some (inl (id0, v', cs0)) = find_init_stld cs pid dones /\
      Some (inl id') = find_next_stld cs0 pid
| AC_tsubst t' =>
    exists cs0, exists dones,
      Some (inr (value_const (const_undef t'), cs0)) = 
        find_init_stld cs pid dones /\
      Some (inl id') = find_next_stld cs0 pid
end.

(***************************************************************)
(* The elimination pairs found from the original program are not 
   well-formed. For example, 
     store x p
     y = load p
     z = load p
   find_xxx_stld can find the LAS (z, x) only after y is removed.
   To address the issue, we define the following weakened well-formedness. 
   For any pair elt=(c1, c2) in the list cs=(cs1, c1, cs2, c2, cs2), 
   cs2 only contains the loads that can be removed by the actions cs2 before
   elt. *)
Definition wf_cs_action_pre (acs: AssocList action) (cs:cmds) (pid:id) 
  (elt:id * action): Prop :=
let '(id', ac') := elt in
match ac' with
| AC_remove =>  
    exists v0, exists cs01, exists c0, exists cs02, exists dones,    
      Some (inl (id', v0, cs01 ++ c0 :: cs02)) = find_init_stld cs pid dones /\
      store_in_cmds pid cs01 = false /\
      store_in_cmd pid c0 = true /\ loads_must_be_in_pre acs pid cs01
| AC_vsubst v' =>  
    exists id0, exists cs01, exists c0, exists cs02, exists dones,    
      Some (inl (id0, v', cs01 ++ c0 :: cs02)) = find_init_stld cs pid dones /\
      store_in_cmds pid cs01 = false /\ getCmdLoc c0 = id' /\
      load_in_cmd pid c0 = true /\ loads_must_be_in_pre acs pid cs01
| AC_tsubst t' =>
    exists cs01, exists c0, exists cs02, exists dones,
      Some (inr (value_const (const_undef t'), cs01 ++ c0 :: cs02)) = 
        find_init_stld cs pid dones /\
      store_in_cmds pid cs01 = false /\ getCmdLoc c0 = id' /\
      load_in_cmd pid c0 = true /\ loads_must_be_in_pre acs pid cs01
end.

(* Properties of wf_cs_action_pre *)
Lemma wf_cs_action_nil__wf_cs_action: forall cs pid elt
  (Hwf: wf_cs_action_pre nil cs pid elt), wf_cs_action cs pid elt.
Proof.
  unfold wf_cs_action_pre, wf_cs_action.
  destruct elt as [id' [|v'|t']]; simpl; intros.
  Case "1".
    destruct Hwf as [v0 [cs01 [c0 [cs02 [dones [Hfind1 [Hnst [Hst Hnld]]]]]]]].
    exists v0. exists (cs01 ++ c0 :: cs02). exists (getCmdLoc c0).
    apply loads_must_be_in_nil__no_loads in Hnld.    
    eapply find_next_stld_inr_intro with (cs02:=cs02) in Hnld; eauto.
    destruct Hnld as [v1 Hnld]. eauto.
  Case "2".
    destruct Hwf 
      as [id0 [cs01 [c0 [cs02 [dones [Hfind1 [Hnst [Heq [Hld Hnld]]]]]]]]]; subst.
    exists id0. exists (cs01 ++ c0 :: cs02). exists dones.
    apply loads_must_be_in_nil__no_loads in Hnld.    
    eapply find_next_stld_inl_intro with (cs02:=cs02) in Hnld; eauto.
  Case "3".
    destruct Hwf 
      as [cs01 [c0 [cs02 [dones [Hfind1 [Hnst [Heq [Hld Hnld]]]]]]]]; subst.
    exists (cs01 ++ c0 :: cs02). exists dones.
    apply loads_must_be_in_nil__no_loads in Hnld.    
    eapply find_next_stld_inl_intro with (cs02:=cs02) in Hnld; eauto.
Qed.

Lemma wf_cs_action_pre_rev: forall acs cs pid ac 
  (Hwf: wf_cs_action_pre (rev acs) cs pid ac),
  wf_cs_action_pre acs cs pid ac.
Proof.
  unfold wf_cs_action_pre. intros.
  destruct ac as [? []].
    destruct Hwf as [v0 [cs01 [c0 [cs02 [dones [J1 [J2 [J3 J4]]]]]]]].
    apply loads_must_be_in_pre_rev in J4. eauto 9.

    destruct Hwf as [id0 [cs01 [c0 [cs02 [dones [J1 [J2 [J3 [J4 J5]]]]]]]]].
    apply loads_must_be_in_pre_rev in J5. eauto 10.

    destruct Hwf as [cs01 [c0 [cs02 [dones [J1 [J2 [J3 [J4 J5]]]]]]]].
    apply loads_must_be_in_pre_rev in J5. eauto 9.
Qed.

Lemma wf_cs_action_pre_weaken: forall acs1 acs2 cs pid ac 
  (Hwf: wf_cs_action_pre acs2 cs pid ac),
  wf_cs_action_pre (acs1++acs2) cs pid ac.
Proof.
  unfold wf_cs_action_pre. intros.
  destruct ac as [? []].
    destruct Hwf as [v0 [cs01 [c0 [cs02 [dones [J1 [J2 [J3 J4]]]]]]]].
    apply loads_must_be_in_pre_weaken with (acs1:=acs1) in J4. eauto 9.

    destruct Hwf as [id0 [cs01 [c0 [cs02 [dones [J1 [J2 [J3 [J4 J5]]]]]]]]].
    apply loads_must_be_in_pre_weaken with (acs1:=acs1) in J5. eauto 10.

    destruct Hwf as [cs01 [c0 [cs02 [dones [J1 [J2 [J3 [J4 J5]]]]]]]].
    apply loads_must_be_in_pre_weaken with (acs1:=acs1) in J5. eauto 9.
Qed.

(***************************************************************)
(* The non-accumerator find_stld_pair_cmd *)
Definition find_stld_pair_cmd' (pid:id) (acc:stld_state * AssocList action) 
  (c:cmd) : stld_state * option (id * action) :=
let '(st, actions) := acc in
match c with
| insn_alloca qid ty value5 align5 =>
    if id_dec pid qid
    then (STLD_alloca ty, None)
    else (st, None)
| insn_store sid typ5 v0 value2 align5 =>
    match value2 with
    | value_id qid =>
       if id_dec pid qid
       then 
         match st with
         | STLD_store sid' _ => (STLD_store sid v0, Some (sid', AC_remove))
         | _ => (STLD_store sid v0, None)
         end
      else (st, None)
    | value_const const5 => (st, None)
    end
| insn_load lid typ5 value1 align5 =>
    match value1 with
    | value_id qid =>
       if id_dec pid qid
       then 
         match st with
         | STLD_store _ v' => (st, Some (lid, AC_vsubst v'))
         | STLD_alloca ty' => (st, Some (lid, AC_tsubst ty'))
         | _ => (st, None)
         end
       else (st, None)
    | value_const const5 => (st, None)
    end
| _ => (st, None)
end.

Lemma find_stld_pair_cmd__find_stld_pair_cmd': forall pid st1 c,
  find_stld_pair_cmd pid st1 c =
  (let (s, o) := find_stld_pair_cmd' pid st1 c in
   match o with
   | ret ac => (s, ac :: snd st1)
   | merror => (s, snd st1)
   end).
Proof.
  destruct st1 as [s1 acc1].
  destruct c; simpl; intros; auto.
    destruct_if; uniq_result; auto.

    destruct value1; auto.
    destruct_if; auto.
    destruct s1; auto.

    destruct value2; auto.
    destruct_if; auto.
    destruct s1; auto.
Qed.

Lemma find_stld_pairs_cmds__find_stld_pairs_cmds': forall pid cs st1,
  fold_left (find_stld_pair_cmd pid) cs st1 =
  fold_left (fun st c => 
             match find_stld_pair_cmd' pid st c with
             | (s, Some ac) => (s, ac::snd st)
             | (s, None) => (s, snd st)
             end) cs st1.
Proof.
  induction cs as [|c cs]; simpl; intros; auto.
    rewrite IHcs.
    f_equal.
    apply find_stld_pair_cmd__find_stld_pair_cmd'.
Qed.

Local Opaque find_stld_pair_cmd' find_stld_pair_cmd.

Lemma find_stld_pairs_cmds_cons_inv: forall pid cs s acs s' acs'
  (Heq: fold_left (find_stld_pair_cmd pid) cs (s, acs) = (s', acs')),
  exists acs0, acs' = acs0 ++ acs.
Proof.
  induction cs as [|c cs]; simpl; intros.
    uniq_result. exists nil. auto.

    rewrite find_stld_pair_cmd__find_stld_pair_cmd' in Heq.
    case_eq (find_stld_pair_cmd' pid (s, acs) c).
    intros s0 o Heq'.
    rewrite Heq' in Heq.
    destruct o as [ac'|]; simpl in Heq. 
      apply IHcs in Heq.
      destruct Heq as [acs0 Heq]; subst.
      exists (acs0 ++ [ac']). simpl_env. auto.
    
      apply IHcs in Heq; auto.
Qed.

Lemma find_stld_pairs_cmds__split_aux: forall pid cs acs1 ac acs2 s0 acs0 s2
  (Heq: fold_left (find_stld_pair_cmd pid) cs (s0, acs0) = 
          (s2, acs2 ++ ac :: acs1 ++ acs0)),
  exists cs1, exists c, exists cs2, exists s1, exists s,
    cs = cs1 ++ c :: cs2 /\
    fold_left (find_stld_pair_cmd pid) cs1 (s0, acs0) = (s1, acs1 ++ acs0) /\
    find_stld_pair_cmd' pid (s1, acs1 ++ acs0) c = (s, Some ac) /\    
    fold_left (find_stld_pair_cmd pid) cs2 (s, ac::acs1 ++ acs0) = 
      (s2, acs2 ++ ac :: acs1 ++ acs0).
Proof.
  induction cs as [|c cs]; simpl; intros; subst.
  Case "base".
    inversion Heq. anti_simpl_env.  
  Case "ind".
    rewrite find_stld_pair_cmd__find_stld_pair_cmd' in Heq.
    case_eq (find_stld_pair_cmd' pid (s0, acs0) c).
    intros s o Heq'.
    rewrite Heq' in Heq.
    destruct o as [ac'|]; simpl in Heq. 
    SCase "1".
      assert (J:=Heq).
      apply find_stld_pairs_cmds_cons_inv in J. destruct J as [acs3 J].
      anti_simpl_env.
      destruct acs1 as [|ac1 acs1].
      SSCase "1.1".
        anti_simpl_env.
        exists nil. exists c. exists cs. exists s0. exists s. 
        split; auto.
      SSCase "1.2".
        destruct (cons_last _ ac1 acs1) as [pre [last EQ]].
        rewrite EQ in J, Heq.
        anti_simpl_env. 
        rewrite_env (acs2 ++ ac :: pre ++ (ac' :: acs0)) in Heq.
        apply IHcs in Heq; auto.
        destruct Heq as [cs1 [c' [cs2 [s1 [s3 [J1 [J2 [J3 J4]]]]]]]].
        exists (c::cs1). exists c'. exists cs2. exists s1. exists s3. 
        split.
          simpl. subst. auto.
        split.
          simpl. rewrite find_stld_pair_cmd__find_stld_pair_cmd'. rewrite Heq'.      
          rewrite_env (([ac1] ++ acs1) ++ acs0). rewrite EQ. simpl_env. auto.
        split.
          rewrite_env (([ac1] ++ acs1) ++ acs0). rewrite EQ. simpl_env. auto.
          rewrite_env (([ac1] ++ acs1) ++ acs0). rewrite EQ. simpl_env. auto.

    SCase "2".
      apply IHcs in Heq; auto.
      destruct Heq as [cs1 [c' [cs2 [s1 [s3 [J1 [J2 [J3 J4]]]]]]]].
      exists (c::cs1). exists c'. exists cs2. exists s1. exists s3.
      simpl. rewrite find_stld_pair_cmd__find_stld_pair_cmd'. rewrite Heq'.      
      subst; split; auto.
Qed.

Lemma find_stld_pairs_cmds__split: forall pid cs acs1 ac acs2 s2
  (Heq: fold_left (find_stld_pair_cmd pid) cs (STLD_init, nil) = 
          (s2, acs2 ++ ac :: acs1)),
  exists cs1, exists c, exists cs2, exists s1, exists s, 
    cs = cs1 ++ c :: cs2 /\
    fold_left (find_stld_pair_cmd pid) cs1 (STLD_init, nil) = (s1, acs1) /\
    find_stld_pair_cmd' pid (s1, acs1) c = (s, Some ac) /\    
    fold_left (find_stld_pair_cmd pid) cs2 (s, ac::acs1) = 
      (s2, acs2 ++ ac :: acs1).
Proof.
  intros.
  replace acs1 with (acs1++nil) in Heq; auto.
  apply find_stld_pairs_cmds__split_aux in Heq.
  simpl_env in *. auto.
Qed.

Transparent find_stld_pair_cmd' find_stld_pair_cmd.

(***************************************************************)
(* A list of acs is well-formed in terms of cs and pid if any action in acs
   is well-formed. *)
Definition wf_cs_actions (acs: AssocList action) (cs:cmds) (pid:id) : Prop :=
forall acs1 ac acs2 (Heq: acs = acs1 ++ ac :: acs2),
  wf_cs_action_pre acs1 cs pid ac.

Lemma wf_cs_actions_nil: forall cs pid, wf_cs_actions nil cs pid.
Proof.
  unfold wf_cs_actions.
  intros. symmetry in Heq. contradict Heq. apply app_cons_not_nil.
Qed.

(***************************************************************)
(* A list of acs is well-formed in terms of block if acs
   is well-formed w.r.t commands of the block. *)
Definition wf_block_action (acs: AssocList action) (b:block) (pid:id) 
  : Prop :=
let '(_, stmts_intro _ cs _) := b in
wf_cs_actions acs cs pid.

(***************************************************************)
(* A list of acs is well-formed in terms of blocks bs if any action in acs
   is well-formed w.r.t commands of a block in bs. *)
Definition wf_actions (bs:blocks) (pid:id) (rd:list l) (acs: AssocList action) 
  : Prop :=
forall acs1 ac acs2 (Heq: acs = acs1 ++ ac :: acs2),
  exists l0, exists ps0, exists cs0, exists tmn0,
    In (l0, stmts_intro ps0 cs0 tmn0) bs /\ In l0 rd /\
    wf_cs_action_pre acs1 cs0 pid ac.

Require Import Program.Tactics.

Lemma wf_actions__in: forall bs pid rd acs ac
  (Hwfa: wf_actions bs pid rd acs) (Hin: In ac acs),
  exists acs1, exists acs2,
  exists l0, exists ps0, exists cs0, exists tmn0,
    acs = acs1 ++ ac :: acs2 /\
    In (l0, stmts_intro ps0 cs0 tmn0) bs /\ In l0 rd /\
    wf_cs_action_pre acs1 cs0 pid ac.
Proof.
  intros.
  apply in_split in Hin.
  destruct Hin as [acs1 [acs2 Hin]].
  assert (J:=Hin).
  apply Hwfa in J. destruct_conjs. eauto 10.
Qed.

(***************************************************************)
(* The invariant that stld_state and actions found should preserve. 
   cs is the processed commands;
   pid is the promotable id;
   elt is the state and current found actions.
   *)
Definition wf_stld_state (cs:cmds) (pid:id) (elt :stld_state * AssocList action)
  : Prop :=
let '(s, acs) := elt in
match s with
| STLD_init => alloca_in_cmds pid cs = false /\ store_in_cmds pid cs = false
| STLD_store id0 v0 =>
    exists cs1 : list cmd, exists ty0 : typ, exists al0 : align, exists cs2, 
      cs = cs1 ++ insn_store id0 ty0 v0 (value_id pid) al0 :: cs2 /\
      store_in_cmds pid cs2 = false /\ loads_must_be_in_pre acs pid cs2
| STLD_alloca t0 =>
    exists cs1, exists num, exists al, exists cs2, 
      cs = cs1 ++ insn_alloca pid t0 num al :: cs2 /\
      store_in_cmds pid cs2 = false /\ loads_must_be_in_pre acs pid cs2
end.

Lemma wf_stld_state_append: forall st cs1 pid c 
  (Hwf: wf_stld_state cs1 pid st)
  (Hnot: alloca_in_cmd pid c = false /\ 
         store_in_cmd pid c = false /\ 
         load_in_cmd pid c = false),
  wf_stld_state (cs1 ++ [c]) pid st.
Proof.
  intros.
  destruct st as [s acs].
  destruct Hnot as [J1 [J2 J3]].
  destruct s; simpl in *.
    destruct Hwf.
    split.
      apply alloca_in_cmds_merge; auto.
      apply store_in_cmds_merge; auto.

    destruct Hwf as [cs2 [t0 [al0 [cs3 [EQ [G1 G2]]]]]]; subst.
    exists cs2. exists t0. exists al0. exists (cs3 ++ [c]).
    simpl_env.
    split; auto.
    split.
      apply store_in_cmds_merge; auto.
      apply loads_must_be_in_pre_append; auto.

    destruct Hwf as [cs2 [num0 [al0 [cs3 [EQ [G1 G2]]]]]]; subst.
    exists cs2. exists num0. exists al0. exists (cs3 ++ [c]).
    simpl_env.
    split; auto.
    split.
      apply store_in_cmds_merge; auto.
      apply loads_must_be_in_pre_append; auto.
Qed.

Ltac wf_stld_state_append_tac :=
  try solve 
    [apply wf_stld_state_append; simpl; try solve [auto | destruct_dec]].

Lemma find_stld_pair_cmd__wf_stld_state: forall (pid : id) cs c st
  (Hwfst: wf_stld_state cs pid st),
  wf_stld_state (cs++[c]) pid (find_stld_pair_cmd pid st c).
Proof.
  intros.
  destruct st as [s acs].
  destruct c; wf_stld_state_append_tac; simpl.
    Case "1".        
      destruct (id_dec pid id5); wf_stld_state_append_tac.
        subst id5. simpl.
        exists cs. exists value5. exists align5. exists nil.
        unfold loads_must_be_in_pre, store_in_cmds. auto.
    Case "2".
      destruct value1 as [qid|]; wf_stld_state_append_tac.
      destruct (id_dec pid qid); wf_stld_state_append_tac.
        subst qid.
        destruct s.
        SCase "2.1".
          simpl in *. destruct Hwfst.
          split.
            apply alloca_in_cmds_merge; auto.
            apply store_in_cmds_merge; auto.
        SCase "2.2".
          simpl in *.
          destruct Hwfst as [cs3 [ty0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
          exists cs3. exists ty0. exists al0.
          exists (cs4++[insn_load id5 typ5 (value_id pid) align5]).
          simpl_env. 
          split; auto.
          split.
            apply store_in_cmds_merge; auto.
            apply loads_must_be_in_pre_append'; auto.
              simpl. destruct_dec.
        SCase "2.3".
          simpl in *.
          destruct Hwfst as [cs3 [num0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
          exists cs3. exists num0. exists al0. 
          exists (cs4++[insn_load id5 typ5 (value_id pid) align5]).
          simpl_env. 
          split; auto.
          split.
            apply store_in_cmds_merge; auto.
            apply loads_must_be_in_pre_append'; auto.
              simpl. destruct_dec.
    Case "3".
      destruct value2 as [qid|]; wf_stld_state_append_tac.
      destruct (id_dec pid qid); wf_stld_state_append_tac.
        subst qid.
        destruct s.
        SCase "3.1".
          simpl. exists cs. exists typ5. exists align5. exists nil.
          unfold loads_must_be_in_pre, store_in_cmds. auto.
        SCase "3.2".
          simpl in *.
          destruct Hwfst as [cs3 [ty0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
          exists (cs3 ++ insn_store i0 ty0 v (value_id pid) al0 :: cs4). 
          exists typ5. exists align5. exists nil.
          simpl_env. 
          split; auto.
          split; auto.
            constructor.
        SCase "3.3".
          simpl in *.
          destruct Hwfst as [cs3 [num0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
          exists (cs3 ++ insn_alloca pid t num0 al0 :: cs4). 
          exists typ5. exists align5. exists nil.
          simpl_env. 
          split; auto.
          split; auto.
            constructor.
Qed.

Lemma find_stld_pairs_cmds__wf_stld_state_aux: forall (pid : id) cs 
  cs2 cs1 st1 (Heq: cs = cs1 ++ cs2)
  (Hwfst: wf_stld_state cs1 pid st1),
  wf_stld_state cs pid (fold_left (find_stld_pair_cmd pid) cs2 st1).
Proof.
  induction cs2 as [|c2 cs2]; simpl; intros; subst; auto.
    simpl_env. auto.

    apply IHcs2 with (cs3:=cs1++[c2]); simpl_env; auto.
    clear IHcs2.
    apply find_stld_pair_cmd__wf_stld_state; auto.
Qed.

Lemma find_stld_pairs_cmds__wf_stld_state: forall (pid : id) cs,
  wf_stld_state cs pid (fold_left (find_stld_pair_cmd pid) cs (STLD_init, nil)).
Proof.
  intros.
  assert (cs = nil ++ cs) as EQ. auto.
  eapply find_stld_pairs_cmds__wf_stld_state_aux in EQ; eauto.
  simpl. unfold alloca_in_cmds, store_in_cmds. auto.
Qed.


Lemma find_stld_pair_cmd'__wf_cs_action_pre: forall cs cs1 c cs2 st1 st2 pid 
  (Heq: cs = cs1 ++ c :: cs2)
  (Huniq: NoDup (getCmdsLocs cs))
  (Hwfst1: wf_stld_state cs1 pid st1) ac
  (Hfind: find_stld_pair_cmd' pid st1 c = (st2, Some ac)),
  wf_cs_action_pre (snd st1) cs pid ac.
Proof.

Ltac find_stld_pair_cmd'__wf_cs_action_pre_tac :=
  match goal with
  | Huniq: NoDup _ |- context [(?A ++ ?b :: ?C) ++ ?d :: ?E] =>
    rewrite_env (A++b::(C++d::E));
    rewrite_env (A++b::(C++d::E)) in Huniq;
    exists C; exists d; exists E; exists (getCmdsLocs A)
  end.

  intros. subst.
  destruct st1 as [s1 acc1]. 
  destruct c; simpl in Hfind; tinv Hfind.
  Case "1".
    destruct_if; tinv Hfind.
  Case "2".
    destruct value1; tinv Hfind.
    destruct_if.
    destruct s1; inv H0.
    SCase "2.1".
      simpl in *.
      destruct Hwfst1 as [cs3 [ty0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
      exists i0. 
      find_stld_pair_cmd'__wf_cs_action_pre_tac.
      split.
        rewrite getCmdsLocs_app in Huniq. simpl in Huniq.
        apply find_init_stld_inl_intro; auto.
      split; auto.
      split; auto.
      split; simpl; auto.
        destruct_dec.
    SCase "2.2".
      simpl in *.
      destruct Hwfst1 as [cs3 [num0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
      find_stld_pair_cmd'__wf_cs_action_pre_tac.
      split.
        rewrite getCmdsLocs_app in Huniq. simpl in Huniq.
        apply find_init_stld_inr_intro; auto.
      split; auto.
      split; auto.
      split; simpl; auto.
        destruct_dec.
  Case "3".
    destruct value2; tinv Hfind.
    destruct_if.
    destruct s1; inv H0.
    simpl in *.
    destruct Hwfst1 as [cs3 [ty0 [al0 [cs4 [EQ [Hnst Hnld]]]]]]; subst.
    exists v. 
    find_stld_pair_cmd'__wf_cs_action_pre_tac.
    split.
      rewrite getCmdsLocs_app in Huniq. simpl in Huniq.
      apply find_init_stld_inl_intro; auto.
    split; auto.
    split; simpl; auto.
      destruct_dec.
Qed.

(* Properties of wf_cs_actions *)
Lemma find_stld_pairs_cmds__wf_cs_actions: forall pid cs 
  (Huniq: NoDup (getCmdsLocs cs)),
  wf_cs_actions (find_stld_pairs_cmds cs pid) cs pid.
Proof.
  unfold find_stld_pairs_cmds.
  intros.
  intros acs1 ac acs2 Heq.
  case_eq (fold_left (find_stld_pair_cmd pid) cs (STLD_init, nil)).
  intros s' ac' Hfind.
  rewrite Hfind in Heq. simpl in Heq.
  assert (ac' = rev acs2 ++ ac :: rev acs1) as EQ.
    rewrite <- rev_involutive with (l:=ac').
    rewrite Heq. rewrite rev_app_distr. simpl. simpl_env. auto.
  subst. clear Heq.
  apply find_stld_pairs_cmds__split in Hfind.
  destruct Hfind as [cs1 [c [cs2 [s1 [s [J1 [J2 [J3 J4]]]]]]]].
  eapply find_stld_pair_cmd'__wf_cs_action_pre in J3; eauto.
    simpl in J3. apply wf_cs_action_pre_rev; auto.

    rewrite <- J2. apply find_stld_pairs_cmds__wf_stld_state; auto.
Qed.

Lemma find_stld_pairs_block__wf_cs_actions: forall pid rd b
  (Huniq: NoDup (getStmtsLocs (snd b))),
  wf_block_action (find_stld_pairs_block pid rd b) b pid.
Proof.
  destruct b as [? [? cs ?]]. simpl. intros.
  destruct_if; auto using wf_cs_actions_nil.
  split_NoDup.
  apply find_stld_pairs_cmds__wf_cs_actions; auto.
Qed.

Lemma find_stld_pairs_blocks__wf_actions: forall pid rd bs actions
  (Huniq: NoDup (getBlocksLocs bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs),
  wf_actions bs pid rd actions.
Proof.
  intros.
  unfold wf_actions.
  intros. subst.
  apply find_stld_pairs_blocks__split in Heq.
  destruct Heq as 
    [b [bs1 [bs2 [acs11 [acs12 [acs21 [acs22 
      [J1 [J2 [J3 [J4 [J5 J6]]]]]]]]]]]]; subst.
  destruct b as [l0 [ps0 cs0 tmn0]].
  exists l0. exists ps0. exists cs0. exists tmn0.
  split. xsolve_in_list.
  split. apply find_stld_pairs_block__reach in J4; auto.
    simpl in J4.
    destruct_if.
      apply wf_cs_action_pre_weaken.
      rewrite getBlocksLocs_app in Huniq. simpl in Huniq.
      split_NoDup. 
      apply find_stld_pairs_cmds__wf_cs_actions with (pid:=pid) in Huniq; auto.
      apply Huniq in H0; auto.

      symmetry in H0. contradict H0. apply app_cons_not_nil.
Qed.

(***************************************************************)
(* Apply actions to ac *)
Definition pipelined_actions_action (actions: list (id*action)) (ac:action) 
  : action :=
List.fold_left subst_action_action actions ac.

(* First fold pairs from left to right, then apply the result list to f. *)
Definition pipelined_actions (pairs: AssocList action) (f:fdef) : fdef :=
List.fold_left apply_action (substs_actions pairs) f.

(* Substitute actions from right to left. *)
Fixpoint pipelined_actions__composed_actions (actions: list (id*action))
  : list (id*action) :=
match actions with
| nil => nil
| (id0,ac0)::actions' => 
    (id0, pipelined_actions_action actions' ac0)::
      pipelined_actions__composed_actions actions'
end.

(* First substitute actions from left to right,
   then substitute actions from right to left,
   then apply the actions to f. *)
Definition composed_pipelined_actions (pairs: AssocList action) (f:fdef): fdef :=
ListComposedPass.substs_fdef 
  (pipelined_actions__composed_actions (substs_actions pairs)) f.

(***************************************************************)
(* The graphs formed by actions are cyclic. *)
Require Import Paths.

Section ActionGraph.

Variable actions: AssocList action.

Definition avertexes : V_set :=
fun (v:Vertex) => 
  let '(index n) := v in 
  n `in` dom actions \/ exists id0, In (id0, AC_vsubst (value_id n)) actions.

Definition aarcs : A_set :=
fun (arc:Arc) =>
  let '(A_ends (index n2) (index n1)) := arc in
  In (n2, AC_vsubst (value_id n1)) actions. 

Definition acyclic_actions : Prop :=
  forall x y vl al p (Hcyc: Cycle avertexes aarcs x y vl al p), 
    vl = V_nil.

End ActionGraph.

(* go to typings_props.v *)
Lemma idDominates_trans: forall s m f (HwfF:wf_fdef s m f)
  (HuniqF: uniqFdef f) id1 id2 id3
  (Hdom1: idDominates f id1 id2) (Hdom2: idDominates f id2 id3),
  idDominates f id1 id3.
Proof.
  unfold idDominates, inscope_of_id.
  intros.
  inv_mbind.
  symmetry_ctx.
  assert (blockInFdefB (l3,s1) f = true) as HBinF0.
    solve_blockInFdefB.
  assert (blockInFdefB (l1,s0) f = true) as HBinF1.
    solve_blockInFdefB.
  destruct s1 as [ps2 cs2 tmn2].
  destruct s0 as [ps3 cs3 tmn3].
  apply fold_left__spec in HeqR2.
  apply fold_left__spec in HeqR0.
  destruct HeqR2 as [_ [_ HeqR2]].
  destruct HeqR0 as [Hinit0 [_ HeqR0]].
  apply_clear HeqR2 in Hdom1.
  apply_clear HeqR0 in Hdom2.
  assert (~ In id3 (getArgsIDsOfFdef f)) as Hnotin1.
    solve_notin_getArgsIDs.
  assert (~ In id2 (getArgsIDsOfFdef f)) as Hnotin2.
    solve_notin_getArgsIDs.
  assert (In id2 (getStmtsLocs (stmts_intro ps2 cs2 tmn2))) as Hin9.
    solve_in_list.
  assert (In id3 (getStmtsLocs (stmts_intro ps3 cs3 tmn3))) as Hin10.
    solve_in_list.
  destruct Hdom1 as [Hdom1 | [sts1 [a1 [J1 [J2 J3]]]]].
  Case "local".
    unfold init_scope in Hdom1.
    destruct_if.
    SCase "in args". 
      admit.
    SCase "not in args".
      destruct Hdom2 as [Hdom2 | [sts2 [a2 [J4 [J5 J6]]]]].
      SSCase "local".
        unfold init_scope in Hdom2.
        destruct_if; try tauto.
(*
        assert (NoDup (getCmdsLocs cs3)) as Hnodup.
          solve_NoDup.
        assert (In id2 (cmds_dominates_cmd cs3 id3)) as Hin2.
          apply in_app_or in Hdom2.
          destruct Hdom2 as [Hdom2 | Hdom2]; try solve [contradict Hdom2; auto].
          apply in_app_or in Hdom2.
          destruct Hdom2 as [Hdom2 | Hdom2]; try solve [contradict Hdom2; auto].
          auto.
        assert (In id1 (cmds_dominates_cmd cs3 id2)) as Hin1.
          apply in_app_or in Hdom1.
          destruct Hdom1 as [Hdom1 | Hdom1]; try solve [contradict Hdom1; auto].
          apply in_app_or in Hdom1.
          destruct Hdom1 as [Hdom1 | Hdom1]; try solve [contradict Hdom1; auto].
          auto.
        assert (In id1 (getCmdsLocs cs3) /\ In id2 (getCmdsLocs cs3)) as Hin.
          apply cmds_dominates_cmd_spec in Hin2.
          apply cmds_dominates_cmd_spec in Hin1.
          split; solve_in_list.
        destruct Hin as [Hin3 Hin4].
        eapply cmds_dominates_cmd_acyclic; eauto.
*)
        admit.
      SSCase "remote".
        admit.
(*
        apply ListSet.set_diff_elim2 in J4; auto.
        simpl in J4. auto.
*)
  Case "remote".
    admit.
(*
      assert ((a1, sts1) = (l1, stmts_intro ps3 cs3 tmn3)) as EQ.
        eapply block_eq2 with (id1:=id1); eauto 1.
          solve_blockInFdefB.
          solve_in_list.
      inv EQ.
      apply lookupBlockViaLabelFromFdef_inv in J2; auto.
      destruct J2; subst.
      destruct Hdom2 as [Hdom2 | [sts2 [a2 [J4 [J5 J6]]]]].
      SCase "local".
        unfold init_scope in Hdom2.
        destruct_if; try tauto.
        assert ((l3, stmts_intro ps2 cs2 tmn2) =
                (l1, stmts_intro ps3 cs3 tmn3)) as EQ.
          eapply block_eq2 with (id1:=id2); eauto 1.
            simpl.
            solve_in_list.
            apply cmds_dominates_cmd_spec in Hdom2.
            solve_in_list.
        inv EQ.
        apply ListSet.set_diff_elim2 in J1; auto.
        simpl in J1. auto.
      SCase "remote".
        assert ((a2, sts2) = (l3, stmts_intro ps2 cs2 tmn2)) as EQ.
          eapply block_eq2 with (id1:=id2); eauto 1.
            solve_blockInFdefB.
            solve_in_list.
        inv EQ.
        apply lookupBlockViaLabelFromFdef_inv in J5; auto.
        assert (l3 <> l1) as Hneq.
          intro J. subst.
          apply ListSet.set_diff_elim2 in J4; auto.
          simpl in J4. auto.
        eapply sdom_acyclic in Hneq; eauto 1.
          apply ListSet.set_diff_elim1 in J4; auto.
          apply ListSet.set_diff_elim1 in J1; auto.
*)
Qed.

Lemma find_stld_pairs_block__isReachableFromEntry: forall s m fh bs 
  (HwfF:wf_fdef s m (fdef_intro fh bs))
  (HuniqF: uniqFdef (fdef_intro fh bs)) pid rd actions
  (Hreach: ret rd = reachablity_analysis (fdef_intro fh bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs),
  forall id0 (a:avertexes actions (index id0)) (b : block),
  lookupBlockViaIDFromFdef (fdef_intro fh bs) id0 = ret b ->
  isReachableFromEntry (fdef_intro fh bs) b.
Proof.
  intros. destruct b as [l0 sts0].
  eapply reachablity_analysis__reachable; eauto.
  subst. 
  destruct a as [Hin | Hin].
  Case "1".
    eapply find_stld_pairs_block__reach''; eauto.
  Case "2".
    destruct Hin as [id1 Hin].
    assert (Hin':=Hin).
    apply binds_In in Hin'.
    eapply find_stld_pairs_block__reach' in Hin'; eauto.
    destruct Hin' as [l1 [sts1 [J1 [J2 J3]]]].
    assert (Huniq:=HuniqF).
    apply uniqF__uniqBlocksLocs in Huniq.    
    remember (flat_map (find_stld_pairs_block pid rd) bs) as acs.
    apply find_stld_pairs_blocks__wf_actions in Heqacs; auto.
    eapply wf_actions__in in Hin; eauto.
    destruct Hin as 
      [acs1 [acs2 [l2 [ps0 [cs0 [tmn0 [EQ [Hin1 [Hin2 Hwf]]]]]]]]]; subst.
    simpl in Hwf.
    destruct Hwf as [id2 [cs01 [c0 [cs02 [dones [J6 [J7 [J8 [J4 J5]]]]]]]]].
    apply find_init_stld_inl_spec in J6.
    destruct J6 as [cs1 [ty [al J6]]]; subst.
    remember (insn_store id2 ty (value_id id0) (value_id pid) al) as c1.
    remember (l2, stmts_intro ps0
               (cs1 ++ c1 :: cs01 ++ c0 :: cs02) tmn0) as b.
    remember (fdef_intro fh bs) as f.
    assert (exists ids1, Some ids1 = inscope_of_cmd f b c1) as R1.
      assert (J:=inscope_of_cmd__total f b c1).
      destruct (inscope_of_cmd f b c1); eauto.
      congruence.
    destruct R1 as [ids1 R1].
    assert (blockInFdefB b f = true) as HBInF.
      subst f. simpl. solve_in_list.
    assert (cmdInBlockB c1 b = true) as HC1InB.
      subst. solve_in_list.
    assert (isReachableFromEntry f b) as Hreach'.
      subst b. simpl.
      eapply reachablity_analysis__reachable; eauto.
    assert (In id0 (getCmdOperands c1)) as Hinops.
      subst c1. simpl. auto.
    assert (J:=R1).
    eapply cmd_operands__in_scope' with (id1:=id0) in J; eauto 1.
    subst b. 
    eapply inscope_of_cmd__id_in_reachable_block in R1; eauto.
      apply R1 in H. simpl in H.
      eapply reachable__reachablity_analysis; eauto.
      
      solve_in_list.
Qed.

Lemma find_stld_pairs_blocks__idDominates: forall s m fh bs 
  (HwfF:wf_fdef s m (fdef_intro fh bs))
  (HuniqF: uniqFdef (fdef_intro fh bs)) actions rd pid
  (Hreach: ret rd = reachablity_analysis (fdef_intro fh bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs) id1 id2
  (Hin: In (id1, AC_vsubst (value_id id2)) actions),
  idDominates (fdef_intro fh bs) id2 id1.
Proof.
  intros.
  assert (Huniq:=HuniqF).
  apply uniqF__uniqBlocksLocs in Huniq.
  assert (J:=Hfind).
  apply find_stld_pairs_blocks__wf_actions in J; auto.
  eapply wf_actions__in in J; eauto.
  destruct J as 
    [acs1 [acs2 [l0 [ps0 [cs0 [tmn0 [EQ [Hin1 [Hin2 Hwf]]]]]]]]]; subst.
  simpl in Hwf.
  destruct Hwf as [id0 [cs01 [c0 [cs02 [dones [J1 [J2 [J3 [J4 J5]]]]]]]]].
  apply find_init_stld_inl_spec in J1.
  destruct J1 as [cs1 [ty [al J1]]]; subst.
  remember (l0, stmts_intro ps0
             (cs1 ++
              insn_store id0 ty (value_id id2) (value_id pid) al
              :: cs01 ++ c0 :: cs02) tmn0) as b.
  remember (insn_store id0 ty (value_id id2) (value_id pid) al) as c1.
  remember (fdef_intro fh bs) as f.
  assert (getCmdID c0 <> merror) as Hmerror.
    destruct c0; inv J4. simpl. congruence.
  assert (isReachableFromEntry f b) as Hreach'.
    subst f.
    eapply find_stld_pairs_block__isReachableFromEntry 
      with (pid:=pid)(id0:=getCmdLoc c0); eauto 1.
      simpl. left. simpl_env. eapply binds_In; eauto.

      assert (insnInFdefBlockB (insn_cmd c0) (fdef_intro fh bs) b = true) 
        as Hin'.
        subst. simpl. apply andb_true_iff.
        split; solve_in_list.
      solve_lookupBlockViaIDFromFdef.
  assert (blockInFdefB b f = true) as HBInF.
    subst f. simpl. solve_in_list.
  assert (cmdInBlockB c0 b = true) as HC0InB.
    subst. solve_in_list.
  assert (cmdInBlockB c1 b = true) as HC1InB.
    subst. solve_in_list.
  assert (exists ids1, Some ids1 = inscope_of_cmd f b c1) as R1.
    assert (J:=inscope_of_cmd__total f b c1).
    destruct (inscope_of_cmd f b c1); eauto.
    congruence.
  destruct R1 as [ids1 R1].
  assert (exists ids0, Some ids0 = inscope_of_cmd f b c0) as R0.
    assert (J:=inscope_of_cmd__total f b c0).
    destruct (inscope_of_cmd f b c0); eauto.
    congruence.
  destruct R0 as [ids0 R0].
  eapply inscope_of_cmd__idDominates; eauto 1.
    assert (AtomSet.set_eq (ids1 ++ getCmdsIDs (c1::cs01)) ids0) as EQ'.
      subst. unfold inscope_of_cmd in *.
      eapply inscope_of_id__append_cmds; eauto.
        solve_NoDup.
    eapply cmd_operands__in_scope' with (id1:=id2) in R1; eauto 1.
      apply EQ'. solve_in_list.
      subst c1. simpl. auto.
Qed.

Lemma find_stld_pairs_blocks__walk_idDominates: forall s m fh bs 
  (HwfF:wf_fdef s m (fdef_intro fh bs))
  (HuniqF: uniqFdef (fdef_intro fh bs)) actions rd pid
  (Hreach: ret rd = reachablity_analysis (fdef_intro fh bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs)
  id1 id2 vl al (Hnnil: vl <> V_nil)
  (Hw: Walk (avertexes actions) (aarcs actions) (index id1) (index id2) vl al),
  idDominates (fdef_intro fh bs) id2 id1.
Proof.
  intros.
  remember (avertexes actions) as V.
  remember (aarcs actions) as A.
  remember (index id1) as x.
  remember (index id2) as y.
  generalize dependent id1.
  generalize dependent id2.
  induction Hw; intros; subst.
  Case "1".
    congruence.
  Case "2".
    destruct y as [id3].
    eapply find_stld_pairs_blocks__idDominates in a; eauto.
    destruct vl as [|v' vl].
    SCase "2.1".
      inv Hw; auto.
    SCase "2.2".
      eapply idDominates_trans; eauto 1.
      apply IHHw; auto. 
        intro H. inv H.
Qed.

Lemma find_stld_pairs_blocks_acyclic: forall s m fh bs 
  (HwfF: wf_fdef s m (fdef_intro fh bs))
  (HuniqF: uniqFdef (fdef_intro fh bs)) pid rd actions
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs)
  (Hreach: ret rd = reachablity_analysis (fdef_intro fh bs)),
  acyclic_actions actions.
Proof.
  unfold acyclic_actions, Cycle.
  intros. subst.
  assert (Hwfa:=HuniqF). 
  apply uniqF__uniqBlocksLocs in Hwfa.
  apply find_stld_pairs_blocks__wf_actions 
    with (pid:=pid)(rd:=rd)(actions:=flat_map (find_stld_pairs_block pid rd) bs)
    in Hwfa; auto.
  destruct vl as [|v vl]; auto.
  assert (Hin:=p). apply P_endx_inv in Hin.
  apply Path_isa_walk in p. 
  destruct y as [id0].
  eapply find_stld_pairs_blocks__walk_idDominates in p; eauto.
  Case "1".
    eapply idDominates_acyclic in p; eauto.
    SCase "1.1".
      inv p.
    SCase "1.2".
      intros.
      eapply find_stld_pairs_block__isReachableFromEntry in Hin; eauto.     
  Case "2".
    intro H. inv H.
Qed.

(***************************************************************)
(* Given acyclic and unique actions, the two composed passes are equivalent. *)
Lemma list_compose_actions__list_composed_substs: forall actions 
  (Hacyclic: acyclic_actions actions) (Huniq: uniq actions) f,
  ListComposedPass.substs_fdef (ListComposedPass.compose_actions actions) f =
  composed_pipelined_actions actions f.
Admitted.
