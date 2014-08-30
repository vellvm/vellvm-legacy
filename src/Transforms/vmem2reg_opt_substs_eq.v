Require Import vellvm.
Require Import ListSet.
Require Import primitives.
Require Import Dipaths.
Require Import palloca_props.
Require Import vmem2reg_opt.
Require Import vmem2reg_opt_compose_props.

Lemma map__map_fst: forall A B (f:A->B) (acs:AssocList A),
  List.map fst acs = List.map fst (ListMap.map f acs).
Proof.
  induction acs as [|[]]; simpl; congruence.
Qed.

(***************************************************************)
(* The graphs formed by actions are cyclic. *)

Section ActionGraph.

Variable actions: AssocList action.

Definition vertex_in_actions_dom (v:Vertex) : Prop :=
let '(index val) := v in 
match val with
| value_id n => n `in` dom actions
| _ => False 
end.

Definition vertex_in_actions_codom (v:Vertex) : Prop :=
let '(index val) := v in 
exists id0, exists ac0, In (id0, ac0) actions /\ action2value ac0 = Some val.

Definition avertexes : @V_set value :=
fun (v:Vertex) => 
vertex_in_actions_dom v \/ vertex_in_actions_codom v.

(* Note that D_walk goes from right to left. 
   e.g a path from x to y is D_walk y x.
   So does A_ends. *)
Definition aarcs : @A_set value :=
fun (arc:Arc) =>
match arc with
| (A_ends (index v1) (index (value_id id2))) => 
  exists ac1, In (id2, ac1) actions /\ action2value ac1 = Some v1
| _ => False
end.

Definition acyclic_actions : Prop :=
forall (x:Vertex) (vl:V_list) (al:A_list) 
       (Hcyc: D_walk avertexes aarcs x x vl al), vl = V_nil.

(* We require that the head (v2) is always in dom. 
   That the non-end vertex (vl) are in dom is true, because they must be
   the start vertex of arcs.
*)
Definition actions_walk v1 v2 vl al : Prop :=
D_walk avertexes aarcs v1 v2 vl al /\ 
vertex_in_actions_dom v2.

End ActionGraph.

(* Properties of avertexes *)
Lemma avertexes_split: forall acs1 acs2 x (H1: avertexes (acs1++acs2) x),
  avertexes acs1 x \/ avertexes acs2 x.
Proof.
  intros.
  destruct H1 as [H1 | H1].
    unfold vertex_in_actions_dom in *.
    destruct x as [[]]; tinv H1.
      unfold avertexes.
      simpl.
      simpl_env in H1.
      fsetdec.
  
    unfold avertexes.
    unfold vertex_in_actions_codom in *.
    destruct x. destruct H1 as [id0 [ac0 [H1 Ha2v]]].
    apply in_app_or in H1.    
    destruct H1 as [H1 | H1]; eauto 6. 
Qed.

Lemma avertexes_incl: forall acs1 acs2 x 
  (H1: avertexes acs1 x) (Hinc: incl acs1 acs2),
  avertexes acs2 x.
Proof.
  intros.
  destruct H1 as [H1 | H1].
    unfold vertex_in_actions_dom in *.
    destruct x as [[]]; tinv H1.
      unfold avertexes.
      simpl.
      left.
      apply binds_In_inv in H1.
      destruct H1 as [a H1].
      apply Hinc in H1.
      eapply In_InDom; eauto.
  
    unfold avertexes.
    unfold vertex_in_actions_codom in *.
    destruct x. destruct H1 as [id0 [ac0 [H1 Ha2v]]].
    apply Hinc in H1. eauto.
Qed.

Lemma avertexes_merge: forall acs1 acs2 x 
  (H1: avertexes acs1 x \/ avertexes acs2 x),
  avertexes (acs1++acs2) x.
Proof.
  intros.
  destruct H1 as [H1 | H1].
    eapply avertexes_incl; eauto.
    apply incl_appl; auto using incl_refl.

    eapply avertexes_incl; eauto.
    apply incl_appr; auto using incl_refl.
Qed.

Lemma avertexes_weakening_head: forall acs acs1 x
  (H1: avertexes acs1 x),
  avertexes (acs++acs1) x.
Proof.
  intros.
  apply avertexes_merge; auto.
Qed.

Lemma avertexes_weakening: forall acs acs1 acs2
  (H: forall x, avertexes acs1 x -> avertexes acs2 x) x 
  (H1: avertexes (acs++acs1) x),
  avertexes (acs++acs2) x.
Proof.
  intros.
  apply avertexes_split in H1.
  destruct H1 as [H1 | H1]; eapply avertexes_merge; eauto.
Qed.

Lemma vertex_in_actions_dom__neq__avertexes: forall (id0 : id)
  (ac0 : action) (acs : list (id * action)) (x : Vertex)
  (Hneq : x <> index (value_id id0))
  (Hdom : vertex_in_actions_dom ((id0, ac0) :: acs) x),
  avertexes acs x.
Proof.
  intros.
  unfold avertexes.
  left.
  destruct x as [[]]; simpl in *; auto.
  destruct (id_dec id5 id0); fsetdec.
Qed.

Lemma avertexes__notin__strengthen_head: forall (id0 : id) (ac0 : action)
  (acs : list (id * action)) (y : Vertex) (vl : V_list)
  (Hnotin : ~ In (index (value_id id0)) (y :: vl)) (x : Vertex)
  (H : avertexes ((id0, ac0) :: acs) x)
  (H0 : aarcs ((id0, ac0) :: acs) (A_ends x y)),
  avertexes acs x.
Proof.
  intros.
  simpl in H0.
  destruct x.
  destruct y as [[]]; tinv H0.
  unfold avertexes in H.
  unfold avertexes. 
  simpl in H. simpl.
  destruct H0 as [ac1 [[H0 | H0] Ha2v]]; eauto.
    inv H0.
    simpl in Hnotin. tauto.
Qed.

(* Properties of action2value *)
Lemma action2id__inv: forall ac0 id0 (Heq: action2value ac0 = Some (value_id id0)),
  ac0 = AC_vsubst (value_id id0).
Proof.
  intros.
  destruct ac0 as [|[id1|]|]; inv Heq; auto.
Qed.

(* Properties of aarcs *)
Lemma aarcs_incl: forall acs1 acs2 x (Ha : aarcs acs1 x) (Hinc: incl acs1 acs2), 
  aarcs acs2 x.
Proof.
  intros.
  unfold aarcs in *.
  destruct x as [[] [[]]]; auto.
    destruct Ha as [ac1 [Hin Ha2v]]; eauto.
Qed.

Lemma aarcs_weakening_head: forall acs1 acs2 x (Ha : aarcs acs2 x), 
  aarcs (acs1 ++ acs2) x.
Proof.
  intros.
  simpl_env. 
  unfold aarcs in *.
  destruct x as [[] [[]]]; auto.
    destruct Ha as [ac1 [Hin Ha2v]].
    exists ac1. split; auto. xsolve_in_list.
Qed.

Lemma aarcs__notin__strengthen_head: forall (id0 : id) (ac0 : action)
  (acs : list (id * action)) (y : Vertex) (vl : V_list)
  (Hnotin : ~ In (index (value_id id0)) (y :: vl)) (x : Vertex)
  (H0 : aarcs ((id0, ac0) :: acs) (A_ends x y)),
  aarcs acs (A_ends x y).
Proof.
  intros.
  simpl in H0. simpl.
  destruct x.
  destruct y as [[]]; tinv H0.
  destruct H0 as [ac1 [[H0 | H0] Ha2v]]; eauto.
    inv H0.
    simpl in Hnotin. tauto.
Qed.

Lemma aarcs_y__vertex_in_actions_dom: forall acs z x 
  (Ha : aarcs acs (A_ends x z)), vertex_in_actions_dom acs z.
Proof.
  intros.
  simpl in Ha.
  destruct x; destruct z as [[]]; tinv Ha.
  destruct Ha as [ac1 [Hin Ha2v]].
  simpl. apply In_InDom in Hin; auto.  
Qed.

Lemma aarcs__In: forall acs id1 id3
  (Ha : aarcs acs (A_ends (index (value_id id1)) (index (value_id id3)))),
  In (id3, AC_vsubst (value_id id1)) acs.
Proof.
  simpl. intros.
  destruct Ha as [ac1 [Hin Ha2v]].
  apply action2id__inv in Ha2v; subst ac1; auto.
Qed.

Lemma In__aarcs: forall acs v id3
  (Ha : In (id3, AC_vsubst v) acs),
  aarcs acs (A_ends (index v) (index (value_id id3))).
Proof.
  simpl. intros. eauto.
Qed.

(************************************)
Definition end_of_actions (v:@Vertex value) (acs:AssocList action) : Prop :=
let '(index v0) := v in
match v0 with
| value_id id0 => lookupAL _ acs id0 = None
| _ => True
end.

Lemma list_subst_actions__end_of_actions: forall v2 id0 ac0 acs
  (Hend: end_of_actions v2 acs),
  end_of_actions v2 (ListComposedPass.subst_actions id0 ac0 acs).
Proof.
  intros.
  assert (J:=list_subst_actions__dom id0 ac0 acs).
  unfold ListComposedPass.subst_actions in *.
  remember (action2value ac0) as ov0.
  destruct ov0 as [v0|]; auto.
  unfold end_of_actions in *.
  destruct v2 as [[vid|]]; auto.
  apply lookupAL_None_notindom in Hend.
  apply notin_lookupAL_None. 
  fsetdec.
Qed.

Lemma list_subst_actions__end_of_actions_inv: forall v2 id0 ac0 acs
  (Hend: end_of_actions v2 (ListComposedPass.subst_actions id0 ac0 acs)),
  end_of_actions v2 acs.
Proof.
  intros.
  assert (J:=list_subst_actions__dom id0 ac0 acs).
  unfold ListComposedPass.subst_actions in *.
  intros.
  remember (action2value ac0) as ov0.
  destruct ov0 as [v0|]; auto.
  unfold end_of_actions in *.
  destruct v2 as [[vid|]]; auto.
  apply lookupAL_None_notindom in Hend.
  apply notin_lookupAL_None. fsetdec.
Qed.

Lemma end_of_actions__incl: forall acs1 acs2 x (Hinc: incl acs2 acs1)
  (Hend: end_of_actions x acs1), end_of_actions x acs2.
Proof.
  intros.
  destruct x as [[]]; auto.
    simpl in *.
    apply lookupAL_None_notindom in Hend.
    apply notin_lookupAL_None.
    eapply incl_notin; eauto.    
Qed.

Lemma end_of_actions__strengthen_head: forall acs1 acs2 x
  (Hend: end_of_actions x (acs1++acs2)), end_of_actions x acs2.
Proof.
  intros.
  eapply end_of_actions__incl in Hend; eauto.
    apply incl_appr; auto using incl_refl.
Qed.

Lemma eq_dom__end_of_actions: forall (acs1 acs2 : AssocList action) 
  (Heqdom: dom acs1 [=] dom acs2) v0 (Hend: end_of_actions v0 acs1),
  end_of_actions v0 acs2.
Proof.
  intros.
  destruct v0 as [[]]; auto.
  simpl in *.
  apply lookupAL_None_notindom in Hend.
  apply notin_lookupAL_None.
  fsetdec.
Qed.

Lemma uniq_head__end_of_actions: forall (acs1 : AssocList action) (ac0 : action)
  (id0 : atom) (Huniq : uniq ((id0, ac0) :: acs1)),
  end_of_actions (index (value_id id0)) acs1.
Proof.
  intros.
  simpl. inv Huniq.
  apply notin_lookupAL_None; auto.
Qed.

(* Properties of vertex_in_actions_xxx *)
Lemma list_subst_actions__vertex_in_actions_dom_inv: forall id0 ac0 
  (acs:AssocList action) x acs' 
  (Heq: acs' = (ListComposedPass.subst_actions id0 ac0 acs))
  (Hdom: vertex_in_actions_dom acs' x),
  vertex_in_actions_dom acs x.
Proof.
  unfold vertex_in_actions_dom. 
  intros. subst. 
  destruct x as [[id1|cst1]]; tinv Hdom.
  assert (J:=list_subst_actions__dom id0 ac0 acs).
  fsetdec.
Qed.

Lemma list_subst_actions__vertex_in_actions_dom: forall id0 ac0 
  (acs:AssocList action) x
  (Hdom: vertex_in_actions_dom acs x) acs' 
  (Heq: acs' = (ListComposedPass.subst_actions id0 ac0 acs)),
  vertex_in_actions_dom acs' x.
Proof.
  unfold vertex_in_actions_dom. 
  intros. subst. 
  destruct x as [[id1|cst1]]; tinv Hdom.
  assert (J:=list_subst_actions__dom id0 ac0 acs).
  fsetdec.
Qed.

Lemma list_subst_actions__forall_vertex_in_actions_dom: forall id0 ac0 
  (acs:AssocList action) xs
  (Hdom: Forall (vertex_in_actions_dom acs) xs) acs' 
  (Heq: acs' = (ListComposedPass.subst_actions id0 ac0 acs)),
  Forall (vertex_in_actions_dom acs') xs.
Proof.
  induction 1; intros; subst.
    constructor.

    constructor; auto.
      eapply list_subst_actions__vertex_in_actions_dom; eauto.
Qed.

Lemma in_D_walk__vertex_in_actions_dom: forall (acs : list (atom * action))
  (x y z : Vertex) (vl : V_list) (al : A_list)
  (H : D_walk (avertexes acs) (aarcs acs) y x vl al) (Hin : In z vl),
  vertex_in_actions_dom acs z.
Proof.
  induction 1; intros.
    inv Hin.

    simpl in Hin.
    destruct Hin as [Hin | Hin]; subst; auto.
    eapply aarcs_y__vertex_in_actions_dom; eauto.
Qed.

Lemma vertex_in_actions_dom__eq_dom: forall acs1 acs2 v 
  (Heq: dom acs1 [=] dom acs2) (Hv: vertex_in_actions_dom acs1 v),
  vertex_in_actions_dom acs2 v.
Proof.
  destruct v as [[]]; simpl; intros; auto.
    fsetdec.  
Qed.

Lemma vertex_in_actions_dom_weakening_head: forall acs1 acs2 x 
  (Hdom : vertex_in_actions_dom acs2 x), 
  vertex_in_actions_dom (acs1 ++ acs2) x.
Proof.
  intros.
  destruct x as [[]]; auto.
  simpl in *. simpl_env. fsetdec.
Qed.

Lemma vertex_in_actions_dom__neq__strengthen_head: forall (id0 : id)
  (ac0 : action) (acs : list (id * action)) (v2 : Vertex)
  (Hneq : v2 <> index (value_id id0))
  (Hdom : vertex_in_actions_dom ((id0, ac0) :: acs) v2),
  vertex_in_actions_dom acs v2.
Proof.
  intros.
  destruct v2 as [[]]; simpl in *; auto.
    destruct (id_dec id5 id0); fsetdec.
Qed.

Lemma end_of_actions__vertex_notin_actions_dom: forall acs v
  (Hend: end_of_actions v acs) (Hdom: vertex_in_actions_dom acs v),
  False.
Proof.
  intros.
  destruct v as [x].
  simpl in *.
  destruct x; auto.
    apply lookupAL_None_notindom in Hend; auto.
Qed.

Lemma vertex_notin_actions_codom_app: forall acs1 acs2 v,
  (~ vertex_in_actions_codom (acs1++acs2) v) <->
  (~ vertex_in_actions_codom acs1 v /\ ~ vertex_in_actions_codom acs2 v).
Proof.
  intros.
  destruct v.
  split; intro H.
  Case "1".
    split; intros [x [ac [J Ha2v]]]; apply H;
       exists x; exists ac; split; auto; xsolve_in_list.
  Case "2".   
    destruct H as [H1 H2].
    intro J.
    destruct J as [x [ac [J Ha2v]]].
    apply in_app_or in J.
    destruct J as [J | J].
      apply H1; exists x; exists ac; auto.
      apply H2; exists x; exists ac; auto.
Qed.

Definition in_codom_of_actions (id0:id) (acs:AssocList action) : Prop :=
Exists (fun elt =>
        let '(_, ac) := elt in
        match action2value ac with
        | Some v => used_in_value id0 v
        | _ => False
        end) acs.

Definition notin_codom_of_actions (id0:id) (acs:AssocList action) : Prop :=
Forall (fun elt =>
        let '(_, ac) := elt in
        match action2value ac with
        | Some v => used_in_value id0 v = false
        | _ => True
        end) acs.

Lemma notin_codom_of_actions__iff__vertex_notin_actions_codom: forall acs id0,
  notin_codom_of_actions id0 acs <-> 
  ~ vertex_in_actions_codom acs (index (value_id id0)).
Proof.
  intros.
  induction acs as [|[id1 ac1] acs].
  Case "1".
    split; intro H.
      simpl. intro J. destruct J as [? [? [? ?]]]. auto.
      constructor.
  Case "2".
    split; intro H.
    SCase "2.1".
      inv H.
      intro J. destruct J as [x [ac [J Ha2v]]].
      apply action2id__inv in Ha2v; subst ac.
      simpl in J.
      destruct J as [J | J].
      SSCase "2.1.1".
        inv J. 
        simpl in *. 
        destruct_dec.
      SSCase "2.1.2".
        eapply Forall_forall in H3; eauto.
        simpl in H3. 
        destruct_dec.
    SCase "2.2".       
      simpl_env in H.
      apply vertex_notin_actions_codom_app in H.
      destruct H as [H1 H2]. 
      constructor.
         destruct ac1; simpl; auto.
         simpl in H1. 
         remember (used_in_value id0 v) as R.
         destruct R; auto.
         elimtype False.
         apply H1. 
         destruct v; tinv HeqR.
         simpl in HeqR. destruct_dec. eauto.
      
         apply IHacs; auto.
Qed.

(*********************************)
Lemma find_stld_pairs_block__isReachableFromEntry: forall s m fh bs 
  (HwfF:wf_fdef s m (fdef_intro fh bs))
  (HuniqF: uniqFdef (fdef_intro fh bs)) pid rd actions
  (Hreach: ret rd = reachablity_analysis (fdef_intro fh bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs),
  forall id0 (a:avertexes actions (index (value_id id0))) (b : block),
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
    destruct Hin as [id1 [ac1 [Hin Ha2v]]].
    apply action2id__inv in Ha2v; subst ac1.
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

Lemma find_stld_pairs_blocks__valueDominates: forall s m fh bs 
  (HwfF:wf_fdef s m (fdef_intro fh bs))
  (HuniqF: uniqFdef (fdef_intro fh bs)) actions rd pid
  (Hreach: ret rd = reachablity_analysis (fdef_intro fh bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs) id1 v2
  (Hin: In (id1, AC_vsubst v2) actions),
  valueDominates (fdef_intro fh bs) v2 (value_id id1).
Proof.
  intros.
  destruct v2 as [id2|]; simpl; auto.
  intros.
  eapply find_stld_pairs_blocks__idDominates; eauto.
Qed.

(* DW *)
Lemma D_walk_head_inv : forall acs v1 v2 vl al
  (Hw: D_walk (avertexes acs) (aarcs acs) v1 v2 vl al),
  (v1 = v2 /\ vl = V_nil /\ al = A_nil) \/ exists id1, v2 = index (value_id id1).
Proof.
  intros.
  destruct vl.
    inv Hw; auto.

    right.
    apply DW_head_inversion in Hw.
      destruct Hw as [y [vl' [al' [J1 [J2 [J3 [J4 J5]]]]]]]; subst.
      simpl in J4.
      destruct y.
      destruct v2 as [[]]; tinv J4; eauto.
     
      congruence.
Qed.

Lemma D_walk_nonend_inv: forall (acs : list (atom * action)) z x vl al
  (Hw : D_walk (avertexes acs) (aarcs acs) x z vl al)
  (Hdom : vertex_in_actions_dom acs z)
  (Hend : end_of_actions x acs),
  exists y, exists vl', exists al',
    D_walk (avertexes acs) (aarcs acs) x y vl' al' /\
    vl = vl' ++ [z] /\
    al = al' ++ [A_ends y z] /\
    (aarcs acs) (A_ends y z) /\ (avertexes acs) y.
Proof.
  intros.
  assert (J:=Hw).
  inv J.
  Case "base".
    destruct z as [[]]; tinv Hdom.
    simpl in *.
    apply lookupAL_None_notindom in Hend.
    fsetdec.
  Case "ind".
    apply DW_head_inversion in Hw; auto; try congruence.
Qed.

(*******************)
Lemma find_stld_pairs_blocks__walk_valueDominates: forall s m fh bs 
  (HwfF:wf_fdef s m (fdef_intro fh bs))
  (HuniqF: uniqFdef (fdef_intro fh bs)) actions rd pid
  (Hreach: ret rd = reachablity_analysis (fdef_intro fh bs))
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs)
  id1 v2 vl al (Hnnil: vl <> V_nil)
  (Hw: D_walk (avertexes actions) (aarcs actions) 
         (index (value_id id1)) (index v2) vl al),
  valueDominates (fdef_intro fh bs) (value_id id1) v2.
Proof.
  intros.
  remember (avertexes actions) as V.
  remember (aarcs actions) as A.
  remember (index (value_id id1)) as x.
  remember (index v2) as y.
  generalize dependent id1.
  generalize dependent v2.
  induction Hw; intros; subst.
  Case "1".
    congruence.
  Case "2".
    destruct y as [[id3|]]; tinv H0.
    match goal with
    | H0: aarcs _ _ |- _ =>
      apply aarcs__In in H0;
      eapply find_stld_pairs_blocks__valueDominates in H0; eauto 1
    end.
    destruct vl as [|v' vl]; inv Hw; auto.
    eapply valueDominates_trans; eauto 1.
      apply IHHw; auto. 
        intro J. inv J.
Qed.

Lemma find_stld_pairs_blocks_acyclic: forall s m fh bs 
  (HwfF: wf_fdef s m (fdef_intro fh bs))
  (HuniqF: uniqFdef (fdef_intro fh bs)) pid rd actions
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs)
  (Hreach: ret rd = reachablity_analysis (fdef_intro fh bs)),
  acyclic_actions actions.
Proof.
  unfold acyclic_actions.
  intros. subst.
  assert (Hwfa:=HuniqF). 
  apply uniqF__uniqBlocksLocs in Hwfa.
  apply find_stld_pairs_blocks__wf_actions 
    with (pid:=pid)(rd:=rd)(actions:=flat_map (find_stld_pairs_block pid rd) bs)
    in Hwfa; auto.
  destruct vl as [|v vl]; auto.
  assert (Hin:=Hcyc). apply DW_endx_inv in Hin.
  assert (J:=Hcyc).
  apply D_walk_head_inv in J.
  destruct J as [[EQ1 [EQ2 EQ3]]|[id0 EQ]]; subst; try congruence.
  eapply find_stld_pairs_blocks__walk_valueDominates in Hcyc; eauto.
  Case "1".
    simpl in Hcyc.
    assert (id_in_reachable_block (fdef_intro fh bs) id0) as Hreach'.
      unfold id_in_reachable_block.
      intros.
      eapply find_stld_pairs_block__isReachableFromEntry in Hin; eauto.     
    apply Hcyc in Hreach'.
    eapply idDominates_acyclic in Hreach'; eauto.
    SCase "1.1".
      inv Hreach'.
    SCase "1.2".
      intros.
      eapply find_stld_pairs_block__isReachableFromEntry in Hin; eauto.     
  Case "2".
    intro H. inv H.
Qed.

(***************************************************************)
Definition used_in_action (id0:id) (ac:action) : bool :=
match ac with
| AC_vsubst v => used_in_value id0 v
| _ => false
end.

Lemma used_in_action__intro: forall id0 ac0 v0 (Ha2v: action2value ac0 = Some v0)
  (Hnuse: used_in_value id0 v0 = false),
  used_in_action id0 ac0 = false.
Proof.
  intros.
  unfold used_in_action.
  destruct ac0; inv Ha2v; auto.
Qed.

Lemma nonused_in_value__subst_value: forall id0 v0 v
  (Hnused: used_in_value id0 v = false),
  v {[v0 // id0]} = v.
Proof.
  destruct v; simpl; intro; auto.
  destruct_if. inv Hnused.
Qed.

Lemma list_subst_actions__noused: forall id0 ac0 (acs:AssocList action) id1 ac1 
  (Hin: In (id1, ac1) acs) (Hnuse: used_in_action id0 ac1 = false),
  In (id1, ac1) (ListComposedPass.subst_actions id0 ac0 acs).
Proof.
  intros.
  unfold ListComposedPass.subst_actions.
  remember (action2value ac0) as ov.
  destruct ov as [v0|]; auto.
  induction acs as [|[ac acs]]; simpl in *; intros; auto.
    destruct Hin as [Hin | Hin]; auto.
      inv Hin. 
      left.
      destruct ac1; simpl in *; auto.
         rewrite nonused_in_value__subst_value; auto.
Qed.

(****************************)
Definition nonused_in_Vertex (id0:id) (v:Vertex) : Prop :=
  let 'index v' := v in used_in_value id0 v' = false.

Definition nonused_in_V_list (id0:id) (vl:V_list) : Prop :=
  Forall (nonused_in_Vertex id0) vl.

Lemma nonused_in_V_list_dec: forall id0 vl,
  nonused_in_V_list id0 vl \/ In (index (value_id id0)) vl.
Proof.
  induction vl; simpl.
    left. constructor.
    
    destruct (V_eq_dec value_dec a (index (value_id id0))).
      subst. right. auto.

      destruct IHvl; auto.
        left. 
        constructor; auto.
          destruct a as [[]]; simpl; auto.
          destruct_dec.
Qed.

(*****)
Definition no_AC_tsubst_action (ac:action) : Prop :=
match ac with
| AC_tsubst _ => False
| _ => True
end.

Definition no_AC_tsubst_actions (acs:AssocList action) : Prop :=
Forall (fun elt =>
        let '(_, ac0) := elt in 
        no_AC_tsubst_action ac0) acs.

Lemma no_AC_tsubst_actions__notin: forall acs id0 t
  (Hnt : no_AC_tsubst_actions acs) (Hin : In (id0, AC_tsubst t) acs),
  False.
Proof.
  intros.
  eapply Forall_forall in Hin; eauto.
  simpl in Hin; auto.
Qed.

Lemma no_AC_tsubst_actions__no_AC_tsubst_action: forall acs id0 ac0
  (Hnt : no_AC_tsubst_actions acs) (Hin : In (id0, ac0) acs),
  no_AC_tsubst_action ac0.
Proof.
  intros.
  eapply Forall_forall in Hin; eauto.
  simpl in Hin; auto.
Qed.

Lemma list_subst_actions__no_AC_tsubst: forall acs id0 ac0
  (Hnt: no_AC_tsubst_actions acs),
  no_AC_tsubst_actions (ListComposedPass.subst_actions id0 ac0 acs).
Proof.
  intros.
  unfold ListComposedPass.subst_actions.
  destruct (action2value ac0); auto.
  induction Hnt as [|[id1 ac1] acs]; constructor; auto.
    destruct ac1; auto.
Qed.

Lemma no_AC_tsubst_action__action2value: forall ac0 v0
  (Hnt: no_AC_tsubst_action ac0) (Ha2v: ret v0 = action2value ac0),
  ac0 = AC_vsubst v0.
Proof.
  intros.
  destruct ac0; inv Hnt; inv Ha2v; auto.
Qed.

Definition substs_actions__no_AC_tsubst_prop (n:nat) := 
  forall actions (Hlen: (length actions = n)%nat)
  (Hnt: no_AC_tsubst_actions actions),
  no_AC_tsubst_actions (substs_actions actions).

Lemma substs_actions__no_AC_tsubst_aux: forall n,
  substs_actions__no_AC_tsubst_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold substs_actions__no_AC_tsubst_prop in *; intros.
  destruct actions as [|[id1 ac1] actions].
  Case "1".
    unfold_substs_actions.
    constructor.
  Case "2".
    unfold_substs_actions.
    inv Hnt.
    constructor; auto.
      assert (length (ListComposedPass.subst_actions id1 ac1 actions) =
              length (ListComposedPass.subst_actions id1 ac1 actions)) as EQ.
        auto.
      apply Hrec in EQ; auto.
      SCase "2.1".
        simpl. rewrite <- list_subst_actions__length; auto.   
      SCase "2.2".
        apply list_subst_actions__no_AC_tsubst; auto.
Qed.

Lemma substs_actions__no_AC_tsubst: forall actions
  (Hnt: no_AC_tsubst_actions actions),
  no_AC_tsubst_actions (substs_actions actions).
Proof.
  intros.
  assert (J:=@substs_actions__no_AC_tsubst_aux (length actions)).
  unfold substs_actions__no_AC_tsubst_prop in J.
  apply J; auto.
Qed.

Lemma find_root__no_AC_tsubst: forall acs
  (Hnts: no_AC_tsubst_actions acs) ac (Hnt: no_AC_tsubst_action ac), 
  no_AC_tsubst_action (ListComposedPass.find_parent_action ac acs).
Proof.
  intros.
  unfold ListComposedPass.find_parent_action.
  destruct ac as [|[id5|]|]; simpl; auto.
    remember (ListMap.find id5 acs) as R.
    destruct R as [[]|]; auto.
    symmetry in HeqR.
    apply lookupAL_in in HeqR.
    apply no_AC_tsubst_actions__notin in HeqR; auto.
Qed.

Lemma list_compose_actions__no_AC_tsubst: forall acs
  (Hnt: no_AC_tsubst_actions acs), 
  no_AC_tsubst_actions (ListComposedPass.compose_actions acs).
Proof.
  induction 1 as [|[] ?]; simpl; constructor.
    apply find_root__no_AC_tsubst; auto.
    apply list_subst_actions__no_AC_tsubst; auto.
Qed.

Lemma list_compose_actions__no_AC_tsubst_pre: forall acs1 acs2
  (Hnt: no_AC_tsubst_actions (acs1++acs2)), 
  no_AC_tsubst_actions (acs1++ListComposedPass.compose_actions acs2).
Proof.
  intros.
  apply Forall_split in Hnt.
  destruct Hnt.
  apply Forall_app; auto.
    apply list_compose_actions__no_AC_tsubst; auto.
Qed.

Lemma substs_actions__no_AC_tsubst_pre: forall acs1 acs2
  (Hnt: no_AC_tsubst_actions (acs1++acs2)), 
  no_AC_tsubst_actions (acs1++substs_actions acs2).
Proof.
  intros.
  apply Forall_split in Hnt.
  destruct Hnt.
  apply Forall_app; auto.
    apply substs_actions__no_AC_tsubst; auto.
Qed.

Lemma list_subst_actions__no_AC_tsubst_pre: forall acs1 acs2
  (Hnt: no_AC_tsubst_actions (acs1++acs2)) id0 ac0, 
  no_AC_tsubst_actions (acs1++ListComposedPass.subst_actions id0 ac0 acs2).
Proof.
  intros.
  apply Forall_split in Hnt.
  destruct Hnt.
  apply Forall_app; auto.
    apply list_subst_actions__no_AC_tsubst; auto.
Qed.

Lemma subst_action__no_AC_tsubst: forall v ac (Hnt: no_AC_tsubst_action ac) id0,
  no_AC_tsubst_action (subst_action id0 v ac).
Proof.
  destruct ac; intros; auto.
Qed.

Lemma pipelined_actions_action__no_AC_tsubst: forall acs
  ac (Hnt: no_AC_tsubst_action ac),
  no_AC_tsubst_action (pipelined_actions_action acs ac).
Proof.
  induction acs as [|[id0 ac0] acs]; simpl; intros; auto.
    destruct (action2value ac0); auto.
      apply IHacs. 
      apply subst_action__no_AC_tsubst; auto.
Qed.

Lemma pipelined_actions__composed_actions__no_AC_tsubst: forall acs
  (Hnt: no_AC_tsubst_actions acs),
  no_AC_tsubst_actions (pipelined_actions__composed_actions acs).
Proof.
  induction 1 as [|[id0 ac0] acs]; simpl; intros.
    constructor.
    constructor.
      apply pipelined_actions_action__no_AC_tsubst; auto.
      apply IHHnt. 
Qed.

Ltac solve_no_AC_tsubst :=
match goal with 
| Hnt: no_AC_tsubst_actions ?acs,
  Hin: In (_, ?ac0) ?acs |- no_AC_tsubst_action ?ac0 =>
  eapply no_AC_tsubst_actions__no_AC_tsubst_action; eauto
| Hnt: no_AC_tsubst_actions ?acs,
  Hin: In (_, AC_tsubst _) ?acs |- _ =>
  eapply no_AC_tsubst_actions__notin in Hin; eauto;
  inv Hin
| Hnt: no_AC_tsubst_actions (_::?acs) |- no_AC_tsubst_actions ?acs =>
  inversion Hnt; auto
| Hnt: no_AC_tsubst_actions (?ac++_) |- no_AC_tsubst_actions ?ac =>
  apply Forall_split in Hnt; destruct Hnt; auto
| Hnt: no_AC_tsubst_actions (_++?ac) |- no_AC_tsubst_actions ?ac =>
  apply Forall_split in Hnt; destruct Hnt; auto
| Hnt : no_AC_tsubst_actions (_ ++ (_, AC_tsubst _) :: _) |- _ =>
  elimtype False;
  eapply no_AC_tsubst_actions__notin in Hnt; eauto using in_middle
| Hnt: no_AC_tsubst_actions (_::?acs) |- 
  no_AC_tsubst_actions (ListComposedPass.subst_actions _ _ ?acs) =>
  apply list_subst_actions__no_AC_tsubst; solve_no_AC_tsubst
| Hnt : no_AC_tsubst_actions (_ ++ (_, ?ac) :: _) |- no_AC_tsubst_action ?ac =>
  eapply no_AC_tsubst_actions__no_AC_tsubst_action in Hnt; eauto using in_middle
| Hnt: no_AC_tsubst_actions (?AC ++ ?ac :: ?AC') |- 
  no_AC_tsubst_actions ?AC' =>        
  rewrite_env ((AC ++ [ac]) ++ AC') in Hnt;
  solve_no_AC_tsubst
| Hnt: no_AC_tsubst_actions ?ac |- no_AC_tsubst_actions (substs_actions ?ac) =>
  apply substs_actions__no_AC_tsubst; auto
| Hnt: no_AC_tsubst_actions ?ac |- 
  no_AC_tsubst_actions (ListComposedPass.compose_actions ?ac) =>
  apply list_compose_actions__no_AC_tsubst; auto
| Hnt: no_AC_tsubst_actions (?acs1++?acs2) |- 
  no_AC_tsubst_actions (?acs1++ListComposedPass.compose_actions ?acs2) =>
  apply list_compose_actions__no_AC_tsubst_pre; auto  
| Hnt: no_AC_tsubst_actions (_::?acs2) |- 
  no_AC_tsubst_actions (ListComposedPass.compose_actions ?acs2) =>
  apply list_compose_actions__no_AC_tsubst; solve_no_AC_tsubst
| Hnt: no_AC_tsubst_actions (_++?acs2) |- 
  no_AC_tsubst_actions (ListComposedPass.compose_actions ?acs2) =>
  apply list_compose_actions__no_AC_tsubst; solve_no_AC_tsubst
| Hnt: no_AC_tsubst_actions (?acs1++?acs2) |- 
  no_AC_tsubst_actions (?acs1++substs_actions ?acs2) =>
  apply substs_actions__no_AC_tsubst_pre; auto  
end.

(* Properties of avertexes *)
Lemma list_subst_actions__nonused_in_Vertex__avertexes: forall id0 ac0 
  (acs:AssocList action) v
  (Hnuse: nonused_in_Vertex id0 v) (Ha: avertexes acs v) acs' 
  (Heq: acs' = (ListComposedPass.subst_actions id0 ac0 acs)),
  avertexes acs' v.
Proof.
  unfold avertexes. 
  intros. subst. 
  destruct v as [v]. simpl in *.
  destruct Ha as [Ha | [id2 [ac2 [Ha Ha2v]]]].
  Case "1".
    destruct v as [id1|cst1]; auto.
      left.   
      assert (J:=list_subst_actions__dom id0 ac0 acs).
      fsetdec.
  Case "2".
    right. 
    exists id2. exists ac2.
    split; auto.
      apply list_subst_actions__noused; auto.
        eapply used_in_action__intro; eauto.
Qed.

Lemma list_subst_actions__vertex_in_actions_dom__avertexes: forall id0 ac0 
  (acs:AssocList action) v
  (Hdom: vertex_in_actions_dom acs v) acs' 
  (Heq: acs' = (ListComposedPass.subst_actions id0 ac0 acs)),
  avertexes acs' v.
Proof.
  unfold avertexes. 
  intros. subst. destruct v as [[id1|cst1]]; tinv Hdom.
  left.  simpl in *.
  assert (J:=list_subst_actions__dom id0 ac0 acs).
  fsetdec.
Qed.

Lemma list_subst_actions__avertexes_inv: forall id0 ac0 
  (acs:AssocList action) v (Hnt: no_AC_tsubst_actions acs)
  (Hin: In (id0, ac0) acs) acs' 
  (Heq: acs' = (ListComposedPass.subst_actions id0 ac0 acs))
  (Ha: avertexes acs' v),
  avertexes acs v.
Proof.
  unfold avertexes. 
  intros. subst. 
  destruct v as [v]. simpl in *.
  destruct Ha as [Ha | [id2 [ac2 [Ha Ha2v]]]].
  Case "1".
    destruct v as [id1|cst1]; auto.
      left.   
      assert (J:=list_subst_actions__dom id0 ac0 acs).
      fsetdec.
  Case "2".
    right. 
    unfold ListComposedPass.subst_actions in Ha.
    remember (action2value ac0) as R.
    destruct R; eauto.
    unfold ListMap.map in Ha.
    apply in_map_iff in Ha.
    destruct Ha as [[id1 a1] [J1 J2]].
    inv J1.
    destruct a1; subst; eauto.
    destruct v1; simpl; eauto.
    simpl in Ha2v.
      destruct_dec; eauto.
      destruct ac0; inv HeqR; eauto.
Qed.
    
(****************************************************)
(* Properties of acyclic_actions *)
Lemma acyclic_actions_incl: forall acs1 acs2
  (H: acyclic_actions acs1) (Hinc: incl acs2 acs1),
  acyclic_actions acs2.
Proof.
  unfold acyclic_actions.
  intros.
  apply D_walk_sub with (v1:=avertexes acs1) 
                        (a1:=aarcs acs1) in Hcyc; eauto.
    intros. eapply avertexes_incl; eauto.
    intros. eapply aarcs_incl; eauto.  
Qed.

Lemma acyclic_actions_strengthening: forall acs1 acs2
  (H: acyclic_actions (acs1++acs2)),
  acyclic_actions acs2.
Proof.
  unfold acyclic_actions.
  intros.
  apply D_walk_sub with (v1:=avertexes (acs1++acs2)) 
                        (a1:=aarcs (acs1++acs2)) in Hcyc; eauto.
    intros. apply avertexes_weakening_head; auto.
    intros. apply aarcs_weakening_head; auto.  
Qed.

Lemma acyclic_ations_isnt_refl: forall id1 ac1 acs1 acs2
  (Hacyc : acyclic_actions (acs1++(id1, ac1) :: acs2)),
  used_in_action id1 ac1 = false.
Proof.
  intros.
  destruct ac1 as [|v0|]; auto.
  destruct v0; auto.
  simpl.
  destruct_dec.
  assert (D_walk (avertexes (acs1++(id1, AC_vsubst (value_id id1)) :: acs2))
                 (aarcs (acs1++(id1, AC_vsubst (value_id id1)) ::acs2))
                 (index (value_id id1)) (index (value_id id1)) 
                 [index (value_id id1)]
                 [A_ends (index (value_id id1)) (index (value_id id1))]) as Hw.
    constructor.
      constructor. left. simpl. simpl_env. auto.
      left. simpl. simpl_env. auto.
      simpl. exists (AC_vsubst (value_id id1)). split; auto. xsolve_in_list.
  apply Hacyc in Hw. inv Hw.
Qed.

Lemma acyclic_actions_has_no_ident_map: forall (id0 : atom) (ac0 : action)
  (acs : list (atom * action))
  (Hacyc : acyclic_actions ((id0, ac0) :: acs)) (v0 : value),
  match ac0 with
  | AC_remove => ac0
  | AC_vsubst v1 => AC_vsubst (v1 {[v0 // id0]})
  | AC_tsubst _ => ac0
  end = ac0.
Proof.
  intros.
  rewrite_env (nil ++ (id0,ac0) :: acs) in Hacyc.
  apply acyclic_ations_isnt_refl in Hacyc.
  destruct ac0; auto.
  destruct v; auto.
  simpl in *.
  destruct_dec. 
  inv Hacyc.
Qed.

Lemma list_subst_acyclic_actions_is_refl: forall id1 ac1 acs1 acs2
  (Hacyc : acyclic_actions (acs1++(id1, ac1) :: acs2)),
  ListComposedPass.subst_actions id1 ac1 [(id1, ac1)] = [(id1, ac1)].
Proof.
  intros.
  unfold ListComposedPass.subst_actions.
  destruct (action2value ac1); auto.
  simpl.
  apply acyclic_ations_isnt_refl in Hacyc.
  destruct ac1 as [|v0|]; auto.
  destruct v0; auto.
  simpl in *.
  destruct_dec. 
  inv Hacyc.
Qed.

Lemma acyclic_actions_has_no_simple_cycles: forall (x : atom) (id0 : id)
  (E : list (atom * action)) (acs1 : list (atom * action))
  (Hacyc' : acyclic_actions
              (acs1 ++ (x, AC_vsubst (value_id id0)) :: E))
  (Hin : In (id0, AC_vsubst (value_id x)) E),
  False.
Proof.
  intros.
  remember (acs1 ++
             (x, AC_vsubst (value_id id0))
             :: E) as acs.
  assert (D_walk (avertexes acs) (aarcs acs) 
          (index (value_id x)) (index (value_id x)) 
          ((index (value_id id0))::(index (value_id x))::nil)
          (A_ends (index (value_id x)) (index (value_id id0))::
           A_ends (index (value_id id0)) (index (value_id x))::nil))
    as Hw.
    Case "1".
    assert (avertexes acs (index (value_id x))) as Hvx. 
      SCase "1.1".
      left. subst. simpl. simpl_env. fsetdec.
    assert (avertexes acs (index (value_id id0))) as Hvid0. 
      SCase "1.2".
      right. subst. exists x. exists (AC_vsubst (value_id id0)). 
      split; auto. xsolve_in_list.
    constructor; auto.
      SCase "1.3".
      constructor; auto.
        SSCase "1.3.1".
        constructor; auto.
        SSCase "1.3.3".
        simpl. subst. exists (AC_vsubst (value_id id0)). 
          split; auto. xsolve_in_list.
      SCase "1.4".
      simpl. subst. exists (AC_vsubst (value_id x)). 
      split; auto. xsolve_in_list.
  Case "2".
  subst.
  apply Hacyc' in Hw. 
  inv Hw.
Qed.

(***********************************)
Definition actions_end_imply (acs1 acs2:AssocList action) : Prop :=
forall vl1 al1 v1 v2
  (Hw: actions_walk acs1 v1 v2 vl1 al1)
  (Hend: end_of_actions v1 acs1),
  exists vl2, exists al2, 
    actions_walk acs2 v1 v2 vl2 al2 /\
    end_of_actions v1 acs2.

Lemma actions_end_imply_refl: forall acs, actions_end_imply acs acs.
Proof.
  unfold actions_end_imply; eauto.
Qed.

Lemma actions_end_imply_trans: forall acs1 acs2 acs3
  (H1: actions_end_imply acs1 acs2) (H2: actions_end_imply acs2 acs3), 
  actions_end_imply acs1 acs3.
Proof.
  unfold actions_end_imply.
  intros. 
  apply H1 in Hw; auto.
  destruct Hw as [vl2 [al2 [J1 J2]]]. eauto.
Qed.

(***************************************)
Definition actions_len_imply (acs1 acs2:AssocList action) : Prop :=
forall vl1 al1 v1 v2
  (Hw: D_walk (avertexes acs1) (aarcs acs1) v1 v2 vl1 al1),
  exists vl2, exists al2, 
    D_walk (avertexes acs2) (aarcs acs2) v1 v2 vl2 al2 /\
    (length vl2 >= length vl1)%nat.

Lemma actions_len_imply__actions_end_imply: forall (acs : list (atom * action))
  (id0 : atom) (ac0 : action)
  (H : actions_len_imply (ListComposedPass.subst_actions id0 ac0 acs) acs),
  actions_end_imply (ListComposedPass.subst_actions id0 ac0 acs) acs.
Proof.
  unfold actions_end_imply. unfold actions_len_imply in *.
  intros.
  destruct Hw as [Hw Hdom].
  apply H in Hw.
  destruct Hw as [vl2 [al2 [Hw Hlen]]].
  exists vl2. exists al2.
  split; eauto using list_subst_actions__end_of_actions_inv.
  split; eauto using list_subst_actions__vertex_in_actions_dom_inv.
Qed.

Lemma actions_len_imply__refl: forall acs,
  actions_len_imply acs acs.
Proof.
  unfold actions_len_imply.
  intros.
  exists vl1. exists al1.
  split; auto.
Qed.

Lemma actions_len_imply__trans: forall acs1 acs2 acs3
  (H12: actions_len_imply acs1 acs2)
  (H23: actions_len_imply acs2 acs3),
  actions_len_imply acs1 acs3.
Proof.
  unfold actions_len_imply.
  intros.
  apply H12 in Hw.
  destruct Hw as [vl2 [al2 [Hw Hlen]]].
  apply H23 in Hw.
  destruct Hw as [vl3 [al3 [Hw Hlen']]].
  exists vl3. exists al3.
  split; auto. omega.
Qed.

(***************************************)
Definition actions_eq (acs1 acs2:AssocList action) : Prop :=
actions_end_imply acs1 acs2 /\ actions_end_imply acs2 acs1.

Lemma actions_eq_refl: forall acs, actions_eq acs acs.
Proof.
  split; apply actions_end_imply_refl.
Qed.

Lemma actions_eq_sym: forall acs1 acs2 (Heq: actions_eq acs1 acs2),
  actions_eq acs2 acs1.
Proof.
  intros.
  destruct Heq.
  split; auto.
Qed.

Lemma actions_eq_trans: forall acs1 acs2 acs3
  (H1: actions_eq acs1 acs2) (H2: actions_eq acs2 acs3), actions_eq acs1 acs3.
Proof.
  intros.
  destruct H1. destruct H2.
  split; eapply actions_end_imply_trans; eauto.
Qed.

(***********************************)
Lemma actions_walk_append :
  forall acs (x y z : Vertex) (vl vl' : V_list) (al al' : A_list)
  (H1: actions_walk acs x y vl al) (H2: actions_walk acs y z vl' al'),
  actions_walk acs x z (vl ++ vl') (al ++ al').
Proof.
  intros.
  destruct H1. destruct H2.
  split; auto.
    eapply DWalk_append; eauto.
Qed.

Lemma actions_walk__notin__strengthen_head: forall id0 ac0 acs v1 v2 vl al
  (Hnotin: ~ In (index (value_id id0)) vl) (Hneq: v2 <> index (value_id id0))
  (Hw: actions_walk ((id0, ac0) :: acs) v1 v2 vl al),
  actions_walk acs v1 v2 vl al.
Proof.
  intros.
  destruct Hw as [Hw Hdom].
  split.
  Case "1".
    induction Hw.
    SCase "1.1".
      constructor.
        eapply vertex_in_actions_dom__neq__avertexes; eauto.
    SCase "1.2".
      constructor.
        apply IHHw; auto. 
          simpl in Hnotin. tauto.

        eapply avertexes__notin__strengthen_head; eauto.
        eapply aarcs__notin__strengthen_head; eauto.
  Case "2".
    eapply vertex_in_actions_dom__neq__strengthen_head; eauto.
Qed.

Lemma actions_walk__weaken_head: forall acs' acs v1 v2 vl al 
  (Huniq: uniq (acs'++acs)) (Hw: actions_walk acs v1 v2 vl al),
  actions_walk (acs' ++ acs) v1 v2 vl al.
Proof.
  intros.
  destruct Hw as [Hw Hdom].
  split.
  Case "1".
    eapply D_walk_sub in Hw; eauto.
    SCase "1.1".
      intros. 
      eapply avertexes_incl; eauto. 
        apply incl_appr; auto using incl_refl.
    SCase "1.2".
      intros.
      eapply aarcs_weakening_head; eauto.
  Case "2".
    apply vertex_in_actions_dom_weakening_head; auto.
Qed.

Lemma actions_D_walk_append :
  forall acs (x y z : Vertex) (vl vl' : V_list) (al al' : A_list)
  (H1: actions_walk acs x y vl al) 
  (H2: D_walk (avertexes acs) (aarcs acs) y z vl' al')
  (H3: vertex_in_actions_dom acs z),
  actions_walk acs x z (vl ++ vl') (al ++ al').
Proof.
  intros.
  destruct H1. 
  split; auto.
    eapply DWalk_append; eauto.
Qed.

(* Lem 44 *)
Lemma list_subst_actions__aarcs: forall id0 ac0 (acs:AssocList action) x y
  (Hnusey: nonused_in_Vertex id0 x)
  (Ha: aarcs acs (A_ends x y)) acs' 
  (Heq: acs' = (ListComposedPass.subst_actions id0 ac0 acs)),
  aarcs acs' (A_ends x y).
Proof.
  intros. 
  destruct x as [x1]. simpl in *.
  destruct y as [[id1|cst1]]; tinv Ha.
  destruct Ha as [ac1 [Hin Ha2v]].
  subst. 
  exists ac1. split; auto.
    apply list_subst_actions__noused; eauto using used_in_action__intro.
Qed.

(* Lem 45 *)
Lemma list_subst_actions__nonused__actions_walk: forall id0 ac0 acs v1 v2 vl al
  (Hw: actions_walk acs v1 v2 vl al)
  acs' (Heq: acs' = (ListComposedPass.subst_actions id0 ac0 acs))
  (Hnuse: nonused_in_V_list id0 (removelast (v1 :: vl))),
  actions_walk acs' v1 v2 vl al.
Proof.
  intros until 1.
  destruct Hw as [Hw Hdom]. intros. 
  assert (vertex_in_actions_dom acs' v2) as J.
    eapply list_subst_actions__vertex_in_actions_dom; eauto.
  split; auto.
  induction Hw.
    constructor.
      left. auto.
     
    assert (Hnuse':=Hnuse).
    apply Forall_inv in Hnuse.
    apply Forall_inv' in Hnuse'.
    constructor; auto.
      eapply list_subst_actions__nonused_in_Vertex__avertexes; eauto.
      eapply list_subst_actions__aarcs; eauto.
Qed.    

(* Lem 46 *)
Lemma list_subst_actions__notin_in: forall id0 ac0 id1 ac1 acs
  (H1: ~ In (id1, ac1) acs)
  (H2: In (id1, ac1) (ListComposedPass.subst_actions id0 ac0 acs)),
  In (id1, AC_vsubst (value_id id0)) acs.
Proof.
  intros.
  destruct ac0;
  induction acs as [|[id3 ac3] acs]; simpl in *; try solve [
    auto |
    destruct H2 as [H2 | H2]; try solve [
      inv H2; try tauto;
      destruct ac3 as [|[id3|]|]; try tauto;
      simpl in *;
      destruct_dec; tauto |

      match goal with
      | IHacs : _ -> _ |- _ => right; apply IHacs; auto
      end ]
    ].
Qed.

Lemma list_subst_actions__notin_eq: forall id0 ac0 id1 ac1 acs
  (H1: ~ In (id1, ac1) acs) (Hnt: no_AC_tsubst_action ac0)
  (H2: In (id1, ac1) (ListComposedPass.subst_actions id0 ac0 acs)),
  ac1 = ac0.
Proof.
  intros.
  destruct ac0;
  induction acs as [|[id3 ac3] acs]; simpl in *; try tauto.
    destruct H2 as [H2 | H2].
      inv H2.
      destruct ac3 as [|[id3|]|]; try tauto.
      simpl in *.
      destruct_dec; tauto.

      apply IHacs; auto.
Qed.

(* Lem 47 *)
Lemma list_subst_actions__in_in: forall id0 ac0 id1 acs
  (H1: In (id1, AC_vsubst (value_id id0)) acs) v
  (Hn: action2value ac0 = Some v),
  In (id1, AC_vsubst v) (ListComposedPass.subst_actions id0 ac0 acs).
Proof.
  induction acs; intros.
    inv H1.

    unfold ListComposedPass.subst_actions.
    rewrite Hn. simpl.
    simpl in H1. 
    destruct H1 as [H1 | H1]; subst.
      simpl. left.
      destruct_dec.

      right. 
      eapply IHacs in H1; eauto.
      unfold ListComposedPass.subst_actions in H1.
      rewrite Hn in H1; auto.
Qed.

Lemma list_subst_actions__aacrs_aarcs: forall id0 ac0 acs v v4
  (Hin : In (id0, ac0) acs) (Heqov : ret v = action2value ac0)
  (H6 : aarcs acs (A_ends (index (value_id id0)) v4)),
  aarcs (ListComposedPass.subst_actions id0 ac0 acs) (A_ends (index v) v4).
Proof.
  intros.
  simpl in H6. simpl.
  destruct v4 as [[]]; auto.
  destruct H6 as [ac1 [H6 Ha2v]].
  apply action2id__inv in Ha2v; subst ac1.
  exists (AC_vsubst v).
  split; auto.
    apply list_subst_actions__in_in; auto.
Qed.

(* Lem 48 *)
Lemma actions_walk_is_simple: forall actions (Hacyc: acyclic_actions actions)
  x y vl al id1 vl1 vl2 vl3 
  (Hnnil: x::vl = vl2 ++ (index (value_id id1)) :: vl3 ++ 
                         (index (value_id id1)) :: vl1)
  (Hw: D_walk (avertexes actions) (aarcs actions) x y vl al),
  False.
Proof.
  intros.
  eapply DW_chunk in Hw; eauto.
  destruct Hw as [al3 Hw].
  apply Hacyc in Hw.
  contradict Hw.
  apply app_cons_not_nil.
Qed.

Lemma list_subst_actions_end_imply_partition: forall acs v1 v5 vl al v2 id3 ac2
  (Huniq : uniq acs) (Hacyc : acyclic_actions acs) (Hin : In (id3, ac2) acs)
  (Hw : actions_walk acs v1 v5 vl al) (Hend : end_of_actions v1 acs)
  (Heqov : ret v2 = action2value ac2)
  (Hin1 : In (index (value_id id3)) (removelast (v1 :: vl))),
  exists v4, exists vl45, exists al45, exists vl12, exists al12,
    actions_walk acs v4 v5 vl45 al45 /\
    actions_walk acs (index (value_id id3)) v4 
      [v4] [A_ends (index (value_id id3)) v4] /\
    actions_walk acs (index v2) (index (value_id id3))
      [(index (value_id id3))] [A_ends (index v2) (index (value_id id3))] /\
    (actions_walk acs v1 (index v2) vl12 al12 \/ 
     (v1 = index v2 /\ vl12 = nil /\ al12 = nil)) /\
    vl = vl12 ++ (index (value_id id3)) :: v4 :: vl45 /\
    al = al12 ++ A_ends (index v2) (index (value_id id3)) :: 
                 A_ends (index (value_id id3)) v4 :: al45 /\
    nonused_in_V_list id3 (removelast (v4 :: vl45)) /\
    nonused_in_V_list id3 (v1 :: vl12).
Proof.
  intros.
  destruct Hw as [Hw Hdom].
  assert (v1 :: vl <> nil) as Hnnil by congruence.
  apply exists_last in Hnnil.
  destruct Hnnil as [vl' [v EQ]].
  rewrite EQ in *.
  rewrite removelast_app in Hin1; try congruence.
  simpl in Hin1. simpl_env in Hin1.
  apply in_split in Hin1. 
  destruct Hin1 as [vl1 [vl2 EQ']]; subst.
  simpl_env in EQ.
  destruct (cons_head _ vl2 v) as [v' [vl2' EQ']].
  rewrite <- EQ' in EQ.  
  destruct vl1 as [|v1' vl1'].
  Case "vl1 = nil".
    inv EQ.
    simpl in Hend.
    apply lookupAL_None_notindom in Hend.
    apply In_InDom in Hin. 
    fsetdec.
  Case "vl1 <> nil".
    simpl_env in EQ.
    inv EQ.
    assert (Hw':=Hw).
    apply DW_split' with (x:=index (value_id id3)) (vl2:=vl1') (vl1:=v'::vl2') 
      in Hw'; auto.
    destruct Hw' as [al1 [al2 [Hw1 [Hw2 EQ]]]]; subst.
    apply DW_last_split in Hw2.
    destruct Hw2 as [v1'0 [al' [Hw2 [Hw3 EQ]]]]; subst.
    assert (index v2 = v1'0) as EQ.
    SCase "1".
      apply DW_inel_ina with (x':=v1'0)(y':=index (value_id id3)) in Hw3.
      SSCase "1.1".
        simpl in Hw3. destruct v1'0.
        destruct Hw3 as [ac3 [Hw3 Ha2v]].
        apply In_lookupAL in Hin; auto.
        apply In_lookupAL in Hw3; auto.
        uniq_result. congruence.
      SSCase "1.2".
        xsolve_in_list.
    subst.
    inv Hw1. 
    assert (avertexes acs v') as J1.
      SCase "1".
      eapply DW_endx_inv; eauto.
    assert (vertex_in_actions_dom acs v') as J2.
      SCase "1".
      eapply in_D_walk__vertex_in_actions_dom in Hw; eauto.
        apply in_or_app. right. simpl. auto.
    assert (vertex_in_actions_dom acs (index (value_id id3))) as J3.
      SCase "1".
      eapply in_D_walk__vertex_in_actions_dom in Hw; eauto.
        xsolve_in_list.
    exists v'. exists vl2'. exists al. exists vl1'. exists al'.
    split.
      SCase "1". split; auto.
    split.
      SCase "1".
      split; auto.
        constructor; auto.
          constructor; auto.
    split.
      SCase "1". split; auto.
    split.
      SCase "1".
      assert (Hw2':=Hw2).
      inv Hw2; auto.
      left.
      split.
        constructor; auto.
          eapply in_D_walk__vertex_in_actions_dom in Hw2'; eauto.
            apply DW_iny_vl in Hw2'; auto.
              intro J. inv J.
    split; auto.
    split. 
      SCase "1". simpl_env. auto.
    split. 
      SCase "1".
      destruct (nonused_in_V_list_dec id3 (removelast (v' :: vl2'))) 
        as [J | J]; auto.
      apply removelast_incl in J.
      apply in_split in J.
      destruct J as [vl21 [vl22 EQ]].
      rewrite EQ in *.
      eapply actions_walk_is_simple with (vl2:=v1'::vl1')(vl3:=vl21)(vl1:=vl22) 
        in Hw; simpl_env; eauto.
      tauto.

      SCase "2".
      destruct (nonused_in_V_list_dec id3 (v1' :: vl1')) as [J | J]; auto.
      apply in_split in J.
      destruct J as [vl21 [vl22 EQ]].
      rewrite EQ in *.
      eapply actions_walk_is_simple with (vl2:=vl21)(vl3:=vl22)(vl1:=v'::vl2')
                           (id1:=id3) in Hw; eauto.
        tauto.

        rewrite_env ((v1' :: vl1') ++ index (value_id id3) :: v' :: vl2').
        rewrite EQ. simpl_env. auto.
Qed.

Lemma list_subst_actions_end_imply: forall acs id0 ac0 (Huniq: uniq acs)
  (Hacyc: acyclic_actions acs) (Hin: In (id0, ac0) acs),
  actions_end_imply acs (ListComposedPass.subst_actions id0 ac0 acs).
Proof.
  unfold actions_end_imply.
  intros.
  remember (action2value ac0) as ov.
  destruct ov as [v|].
  Case "ov=Some v".
    destruct (nonused_in_V_list_dec id0 (removelast (v1::vl1))) 
      as [Hnotin1 | Hin1].
    SCase "id0 notin path".
      eapply list_subst_actions__nonused__actions_walk with (ac0:=ac0) in Hw; 
        eauto.
      exists vl1. exists al1.
      split; auto.
        apply list_subst_actions__end_of_actions; auto.

    SCase "id0 in path".
      eapply list_subst_actions_end_imply_partition in Hin1; eauto.
      destruct Hin1 as [v4 [vl45 [al45 [vl12 [al12 
                         [Hw45 [Hw34 [Hw23 [Hw12 [EQ1 [EQ2 
                         [Hnin45 Hnin12]]]]]]]]]]]]; subst.
      assert (nonused_in_Vertex id0 (index v)) as Hnin.
        SSCase "1".
        destruct Hw12 as [Hw12 | [EQ1 [EQ2 EQ3]]]; subst.
          inv Hw12.
          eapply DW_Forall_head in Hnin12; eauto.

          inv Hnin12; auto.
      eapply list_subst_actions__nonused__actions_walk with (ac0:=ac0) in Hw45;
        eauto.
      apply Forall_removelast in Hnin12.
      exists (vl12 ++ v4 :: vl45).
      exists (al12 ++ A_ends (index v) v4 :: al45).
      split.
      SSCase "1".
        assert (actions_walk (ListComposedPass.subst_actions id0 ac0 acs) 
                (index v) v2 (v4 :: vl45) (A_ends (index v) v4 :: al45)) as Hw25.
          SSSCase "1a".
          simpl_env.
          eapply actions_walk_append; eauto.
          destruct Hw34 as [J1 J2].
          destruct Hw23 as [J4 J5].
          assert (vertex_in_actions_dom 
                    (ListComposedPass.subst_actions id0 ac0 acs) v4) as J3.
            eapply list_subst_actions__vertex_in_actions_dom; eauto.
          split; auto.
          constructor. 
          SSSSCase "1.1".
            constructor; auto.
              left. auto.
          SSSSCase "1.2".
            inv J4.
            eapply list_subst_actions__nonused_in_Vertex__avertexes; eauto.
          SSSSCase "1.3".
            inv J1. 
            apply list_subst_actions__aacrs_aarcs; auto.
        destruct Hw12 as [Hw12 | [EQ1 [EQ2 EQ3]]]; subst; auto.
          eapply list_subst_actions__nonused__actions_walk with (ac0:=ac0) 
            in Hw12; eauto.
          eapply actions_walk_append; eauto.
      SSCase "2".
        apply list_subst_actions__end_of_actions; auto.
  Case "ov=None".
    unfold ListComposedPass.subst_actions.
    rewrite <- Heqov. eauto.
Qed.

(* Lem 49 *)
Fixpoint gen_original_D_walk (acs:AssocList action) id1 (vl:@V_list value)
  : (@V_list value * @A_list value)%type :=
match vl with
| index v1::(index (value_id id2)::_) as vl' =>
    let '(vla, ala) := gen_original_D_walk acs id1 vl' in
    if (in_dec id_action_dec (id2, AC_vsubst v1) acs) 
    then (index (value_id id2)::vla, 
          A_ends (index v1) (index (value_id id2))::ala)
    else (index (value_id id1)::index (value_id id2)::vla, 
          A_ends (index v1) (index (value_id id1))::
          A_ends (index (value_id id1)) (index (value_id id2))::ala)
| _ => (nil, nil)
end.

Lemma gen_original_D_walk__correct: forall acs' id0 ac0 acs x y vl al
  (Hnt: no_AC_tsubst_actions acs)
  (Heq: acs' = ListComposedPass.subst_actions id0 ac0 acs) 
  (Hin: In (id0, ac0) acs)
  (Hw: D_walk (avertexes acs') (aarcs acs') x y vl al) vl' al'
  (Hgen: (vl', al') = gen_original_D_walk acs id0 (x::vl)), 
  D_walk (avertexes acs) (aarcs acs) x y vl' al' /\
  (length vl' >= length vl)%nat.
Proof.
  induction 4; intros.
  Case "base".
    destruct x; inv Hgen.
    split; auto.
      constructor.
        eapply list_subst_actions__avertexes_inv; eauto.
  Case "ind".
    simpl in Hgen.
    destruct x as [vx].
    destruct y as [[]]; tinv H0.
    remember (gen_original_D_walk acs id0 (index (value_id id5) :: vl)) as R.
    destruct R as [vl1 al1].
    edestruct IHHw as [J1 J2]; auto.
    simpl in HeqR.
    rewrite <- HeqR in Hgen. clear HeqR.
    destruct H0 as [ac1 [Ha Ha2v]]. 
    assert (ac1 = AC_vsubst vx) as EQ.
      symmetry in Ha2v.
      apply no_AC_tsubst_action__action2value in Ha2v; auto.
      apply list_subst_actions__no_AC_tsubst with (id0:=id0)(ac0:=ac0) in Hnt.
      rewrite <- Heq in Hnt.
      solve_no_AC_tsubst. 
    subst.
    destruct_if.
    SCase "edge in acs".
      split.
      SSCase "1".
        constructor; auto.
          unfold avertexes. simpl. eauto.
          eapply In__aarcs; eauto.
      SSCase "2".
        simpl. omega.
    SCase "edge notin acs".
      assert (AC_vsubst vx = ac0) as EQ.
        eapply list_subst_actions__notin_eq; eauto.
          solve_no_AC_tsubst.
      subst ac0.
      split.
      SSCase "1".
        constructor; auto.
        SSSCase "1.1".
          constructor; auto.
          SSSSCase "1.1.1".
            unfold avertexes. simpl. eauto.
          SSSSCase "1.1.2".
            apply In__aarcs.
            eapply list_subst_actions__notin_in; eauto.
        SSSCase "1.2".
          unfold avertexes. simpl. eauto.         
        SSSCase "1.3".
          apply In__aarcs; auto.
      SSCase "2".
        simpl. omega.
Qed.

Lemma list_subst_actions_len_imply_inv: forall acs id0 ac0 (Huniq: uniq acs)
  (Hnt: no_AC_tsubst_actions acs) (Hin: In (id0, ac0) acs),
  actions_len_imply (ListComposedPass.subst_actions id0 ac0 acs) acs.
Proof.
  unfold actions_len_imply.
  intros.
  remember (action2value ac0) as ov.
  destruct ov as [v0|].
  Case "ov=Some v".
    remember (gen_original_D_walk acs id0 (v1::vl1)) as R.
    destruct R as [vl1' al1'].
    eapply gen_original_D_walk__correct in HeqR; eauto.
  Case "ov=None".
    unfold ListComposedPass.subst_actions in *.
    rewrite <- Heqov in *. eauto.
Qed.

Lemma list_subst_actions_end_imply_inv: forall acs id0 ac0 (Huniq: uniq acs)
  (Hnt: no_AC_tsubst_actions acs) (Hin: In (id0, ac0) acs),
  actions_end_imply (ListComposedPass.subst_actions id0 ac0 acs) acs.
Proof.
  intros.
  apply list_subst_actions_len_imply_inv in Hin; auto.
  apply actions_len_imply__actions_end_imply; auto.
Qed.

(* Lemma 50 *)
Lemma list_subst_actions_eq: forall acs id0 ac0 (Huniq: uniq acs)
  (Hnt: no_AC_tsubst_actions acs) (Hacyc: acyclic_actions acs) 
  (Hin: In (id0, ac0) acs),
  actions_eq acs (ListComposedPass.subst_actions id0 ac0 acs).
Proof.
  intros.
  split.
    eapply list_subst_actions_end_imply; eauto.
    eapply list_subst_actions_end_imply_inv; eauto.
Qed.

(* Lem 50a *)
Lemma list_subst_actions__AC_remove: forall acs id1 ac1 id0,
  lookupAL _ acs id0 = Some AC_remove <->
    lookupAL _ (ListComposedPass.subst_actions id1 ac1 acs) id0 = 
      Some AC_remove.  
Proof.
  intros.
  unfold ListComposedPass.subst_actions.
  remember (action2value ac1) as R.
  destruct R as [v1|]; try tauto.
  induction acs as [|[id2 ac2] acs']; simpl; try tauto.
    destruct_if.
    split; intro J.
    Case "1".
      uniq_result; auto.        
    Case "2".
      destruct ac2 as [|[id3|]|]; auto.
      simpl in J.
      destruct_if.
Qed.

(* Lemma 51a *)
Lemma list_subst_actions__id: forall id1 ac1,
  [(id1, ac1)] = ListComposedPass.subst_actions id1 ac1 [(id1, ac1)].
Proof.
  intros.
   unfold ListComposedPass.subst_actions.
   remember (action2value ac1) as R.
   destruct R; auto.
   simpl.
   destruct ac1; auto.
   inv HeqR.
   destruct v0; auto.
   simpl.
   destruct_dec.
Qed.

(* Lemma 51 *)
Lemma list_subst_actions_acyclic: forall acs id0 ac0 (Huniq: uniq acs)
  (Hnt: no_AC_tsubst_actions acs) (Hin: In (id0, ac0) acs) 
  (Hacyc: acyclic_actions acs),
  acyclic_actions (ListComposedPass.subst_actions id0 ac0 acs).
Proof.
  unfold acyclic_actions.
  intros. 
  apply list_subst_actions_len_imply_inv in Hcyc; auto.
  destruct Hcyc as [vl2 [al2 [Hw Hlen]]].
  apply Hacyc in Hw. subst. 
  eapply len_le_zero__nil; eauto.
Qed.

Lemma list_subst_actions_cons_acyclic: forall acs id0 ac0 
  (Hnt: no_AC_tsubst_actions ((id0,ac0)::acs)) (Huniq: uniq ((id0,ac0)::acs))
  (Hacyc: acyclic_actions ((id0,ac0)::acs)),
  acyclic_actions ((id0,ac0)::ListComposedPass.subst_actions id0 ac0 acs).
Proof.
  intros. simpl_env.
  rewrite list_subst_actions__id.
  rewrite <- list_subst_actions_app.
  apply list_subst_actions_acyclic; auto.
    simpl. auto.
Qed.

(* Lemma 52 *)
Lemma nonused_in_action__notin_codom_of_actions: forall id0 ac0 acs v0
  (Hnuse: used_in_action id0 ac0 = false) (Hsome: Some v0 = action2value ac0),
  notin_codom_of_actions id0 (ListComposedPass.subst_actions id0 ac0 acs).
Proof.
  unfold ListComposedPass.subst_actions.
  intros. rewrite <- Hsome.
  unfold notin_codom_of_actions.
  induction acs as [|[id1 ac1] acs]; simpl; auto.
    constructor; auto.
      destruct ac1; simpl; auto.
      destruct v as [vid|]; simpl; auto.
      destruct_if; simpl.
        unfold used_in_action in Hnuse.
        destruct ac0; inv Hsome; auto.     

        destruct_dec.
Qed.

(* Lem 53 *)
Lemma actions_len_imply__avertexes_imply : forall acs1 acs2 
  (Hinc: actions_len_imply acs1 acs2) x (H : avertexes acs1 x),
  avertexes acs2 x.
Proof.
  intros.
  unfold actions_len_imply in Hinc.
  assert (D_walk (avertexes acs1) (aarcs acs1) x x nil nil) as Hw.
    constructor; auto.
  apply Hinc in Hw.
  destruct Hw as [vl2 [al2 [Hw Hlen]]].
  apply DW_endx_inv in Hw; auto.
Qed.

Lemma actions_len_imply__avertexes_cons_imply : forall acs1 acs2 
  (Hinc: actions_len_imply acs1 acs2) x id0 ac0 
  (H : avertexes ((id0, ac0)::acs1) x),
  avertexes ((id0, ac0)::acs2) x.
Proof.
  intros.
  simpl_env in *.
  apply avertexes_split in H.
  destruct H.
    apply avertexes_merge; auto.

    apply avertexes_merge; auto.
    right.
    eapply actions_len_imply__avertexes_imply; eauto.
Qed.

Lemma actions_len_imply_cons: forall acs1 acs2 
  (Hinc: actions_len_imply acs1 acs2) id0 ac0, 
  actions_len_imply ((id0, ac0)::acs1) ((id0, ac0)::acs2).
Proof.
  unfold actions_len_imply.
  intros.
  induction Hw.
  Case "base".
    exists nil. exists nil.
    split; auto.
      constructor; auto.  
        eapply actions_len_imply__avertexes_cons_imply; eauto.
  Case "ind".
    destruct IHHw as [vl2 [al2 [Hw' J]]].
    destruct x as [vx]; destruct y as [[]]; tinv H0.
    simpl in H0.
    destruct H0 as [ac1 [[H0 | H0] Ha2v]].
    SCase "1".
      inv H0.
      exists (index (value_id id5)::vl2).
      exists (A_ends (index vx) (index (value_id id5))::al2).
      split.
      SSCase "1.1".
        constructor; auto.
          eapply actions_len_imply__avertexes_cons_imply; eauto.
          simpl. exists ac1. auto.
      SSCase "1.2".
        simpl. omega.
    SCase "2".
      assert (D_walk (avertexes acs1) (aarcs acs1) 
                     (index vx) (index (value_id id5)) 
                     [index (value_id id5)] 
                     [A_ends (index vx) (index (value_id id5))]) as Hw''.
      SSCase "2.1".
        constructor; auto.
        SSSCase "2.1.1".
          constructor; auto.
            unfold avertexes. simpl. left. 
            eapply In_InDom; eauto.
        SSSCase "2.1.2".
          unfold avertexes. simpl. right. eauto.
        SSSCase "2.1.3".
          simpl. eauto.
      apply Hinc in Hw''.
      destruct Hw'' as [vl3 [al3 [Hw'' J']]].
      exists (vl3++vl2). exists (al3++al2).
      split.
      SSCase "2.2".
        eapply DWalk_append; eauto.
          eapply D_walk_sub in Hw''; eauto.
          SSSCase "2.2.1".
            intros x Hv.
            simpl_env. apply avertexes_weakening_head; eauto.            
          SSSCase "2.2.2".
            intros x Ha.
            simpl_env. apply aarcs_weakening_head; auto.
      SSCase "2.3".
        simpl. simpl in J'. rewrite app_length. omega.
Qed.

Lemma actions_len_imply_weakening: forall acs1 acs2 
  (Hinc: actions_len_imply acs1 acs2) acs, 
  actions_len_imply (acs++acs1) (acs++acs2).
Proof.
  induction acs as [|[id0 ac0] acs]; auto.
    simpl_env. simpl.
    apply actions_len_imply_cons; auto.
Qed.

(* Lem 55 *)
Inductive D_walk_segments : Set :=
| PW_arcs : @Vertex value -> @Vertex value -> 
            @V_list value -> @A_list value -> D_walk_segments
| PW_arc : D_walk_segments
.

Definition add_D_walk_segments id0 (v1 v2:@Vertex value) 
  (acc:list D_walk_segments) : list D_walk_segments :=
if (V_eq_dec value_dec (index (value_id id0)) v2) 
then PW_arc::acc
else 
  match acc with
  | nil => [PW_arcs v1 v2 [v2] [A_ends v1 v2]]
  | PW_arc::_ => PW_arcs v1 v2 [v2] [A_ends v1 v2] :: acc
  | PW_arcs x y vl al::acc' =>
      PW_arcs v1 y (v2::vl) (A_ends v1 v2::al)::acc'
  end.

Fixpoint gen_D_walk_segments id0 (vl : @V_list value) : list D_walk_segments :=
match vl with
| v1::((v2::_) as vl') =>
    add_D_walk_segments id0 v1 v2 (gen_D_walk_segments id0 vl')
| v1 :: nil => [PW_arcs v1 v1 nil nil]
| nil => nil
end.

Lemma add_D_walk_segments__nonnil: forall id0 v1 v2 acc,
  nil <> add_D_walk_segments id0 v1 v2 acc.
Proof.
  intros.
  unfold add_D_walk_segments.
  destruct (V_eq_dec value_dec (index (value_id id0)) v2); try congruence.
  destruct acc as [|[] ?]; intro J; inv J.
Qed.

Lemma gen_D_walk_segments__nonnil: forall id0 vl (H: vl <> nil),
  nil <> gen_D_walk_segments id0 vl.
Proof.
  induction vl; simpl; intros.
    congruence.

    destruct vl.
      intro J. inv J.
      apply add_D_walk_segments__nonnil.
Qed.

Lemma add_D_walk_segments__cons_PW_arc_inv: forall id0 v1 v2 acc acc'
  (Heq : PW_arc :: acc' = add_D_walk_segments id0 v1 v2 acc),
  acc = acc' /\ v2 = index (value_id id0).
Proof.
  intros.
  unfold add_D_walk_segments in Heq.
  destruct (V_eq_dec value_dec (index (value_id id0)) v2).
    inv Heq; auto.
  
    destruct acc as [|[]]; inv Heq.
Qed.

Lemma gen_D_walk_segments__cons_PW_arc_inv: forall id0 vl acc
  (Heq: PW_arc::acc = gen_D_walk_segments id0 vl),
  exists v0, exists vl',
    acc = gen_D_walk_segments id0 (index (value_id id0)::vl') /\
    vl = v0 :: index (value_id id0) :: vl'.
Proof.
  induction vl as [|v1 vl]; simpl; intros.
    congruence.

    destruct vl as [|v2 vl]; tinv Heq.
    apply add_D_walk_segments__cons_PW_arc_inv in Heq.
    destruct Heq; subst.
    exists v1. exists vl.
    split; auto.
Qed.

Lemma unfold_gen_D_walk_segments: forall id0 x y vl,
  gen_D_walk_segments id0 (x::y::vl) =
    add_D_walk_segments id0 x y (gen_D_walk_segments id0 (y::vl)).
Proof.
  simpl. auto.
Qed.

Lemma length_add_D_walk_segments: forall (id0 : id) (v v0 : Vertex) ws,
  (length ws <= length (add_D_walk_segments id0 v v0 ws))%nat.
Proof.
  intros.
  unfold add_D_walk_segments.
  destruct_if.
    simpl. omega.
    destruct ws as [|[]]; simpl; omega.
Qed.

Lemma length_gen_D_walk_segments_cons: forall id0 v vl,
  (length (gen_D_walk_segments id0 vl) <=
    length (gen_D_walk_segments id0 (v::vl)))%nat.
Proof.
  destruct vl.
    simpl. omega.

    rewrite unfold_gen_D_walk_segments.
    apply length_add_D_walk_segments.
Qed.

Lemma gen_D_walk_segments__cons_PW_arcs_inv: forall id0 v a x y vl al 
  (Hw: D_walk v a x y vl al) v1 v2 vl1 al1 acc
  (Heq: PW_arcs v1 v2 vl1 al1::acc = gen_D_walk_segments id0 (x::vl)),
  exists vl', exists al',
    (vl' <> nil -> acc = gen_D_walk_segments id0 (v2::vl') /\
                   exists acc', acc = PW_arc :: acc') /\
    (vl' = nil -> acc = nil) /\
    vl = vl1 ++ vl' /\
    al = al1 ++ al' /\
    D_walk v a v2 y vl' al' /\ 
    D_walk v a x v2 vl1 al1 /\ x = v1 /\
    ~ In (index (value_id id0)) vl1.
Proof.
  induction 1; intros.
  Case "base".
    inv Heq.
    exists nil. exists nil.
    split. congruence.
    repeat (split; auto).
      constructor; auto.
      constructor; auto.
  Case "ind".
    rewrite unfold_gen_D_walk_segments in Heq.
    unfold add_D_walk_segments in Heq.
    destruct (V_eq_dec value_dec (index (value_id id0)) y); tinv Heq.
    remember (gen_D_walk_segments id0 (y :: vl)) as R.
    destruct R as [|[] acc']; inv Heq.
    SCase "1".
      contradict HeqR.
      apply gen_D_walk_segments__nonnil. 
        congruence.
    SCase "2".
      edestruct IHHw as [vl' [al' [J1 [J2 [J3 [J4 [J5 [J6 [J7 J8]]]]]]]]]; 
        eauto.
      subst.
      exists vl'. exists al'.
      repeat (split; auto).
      SSCase "2.1".
        constructor; auto.
      SSCase "2.2".
        simpl. intro J.
        destruct J; congruence.
    SCase "3".
      exists vl. exists al.
      rewrite HeqR. 
      repeat (split; auto).
      SSCase "3.0".
         rewrite <- HeqR. eauto.
      SSCase "3.1".
        intro J; subst.
        inv HeqR.
      SSCase "3.2".
        constructor; auto.
        constructor; auto.
          apply DW_endx_inv in Hw; auto.
      SSCase "3.3".
        simpl. intro J.
        destruct J; congruence.
Qed.

Lemma uniq_aarcs_inv: forall (acs1 : AssocList action) (ac0 : action)
  (id0 : atom) (Huniq : uniq ((id0, ac0) :: acs1)) (v1 : Vertex)
  (H1 : aarcs ((id0, ac0) :: acs1) (A_ends v1 (index (value_id id0)))),
  exists v0 : value, ret v0 = action2value ac0 /\ v1 = index v0.
Proof.
  intros.
  simpl in H1.
  destruct v1.
  destruct H1 as [ac1 [[H1 | H1] Ha2v]].
    inv H1. exists a. eauto.
    inv Huniq. apply In_InDom in H1. fsetdec.
Qed.

Lemma uniq_aarcs__avettexes_aarcs: forall (acs1 : AssocList action) 
  (ac0 : action) (Hnt: no_AC_tsubst_action ac0) (id0 : atom) 
  (Huniq : uniq ((id0, ac0) :: acs1)) (v1 : Vertex)
  (H1 : aarcs ((id0, ac0) :: acs1) (A_ends v1 (index (value_id id0)))) acs2,
  avertexes ((id0, ac0) :: acs2) v1 /\
  aarcs ((id0, ac0) :: acs2) (A_ends v1 (index (value_id id0))).
Proof.
  intros.
  apply uniq_aarcs_inv in H1; auto.
  destruct H1 as [v0 [J1 J2]]; subst.
  apply no_AC_tsubst_action__action2value in J1; auto.
  subst.
  unfold avertexes.
  simpl.
  split. eauto 6.
    exists (AC_vsubst v0). auto.
Qed.

Definition actions_end_imply_cons_aux_prop 
  (acs1 acs2 : AssocList action) (id0 : atom) (ac0 : action) (n:nat) := 
  forall (ws : list D_walk_segments)
  (Hnat: n = length ws)
  (al1 : A_list) (vl1 : V_list) (v2 v1 : Vertex)
  (Hq: D_walk (avertexes ((id0, ac0) :: acs1)) (aarcs ((id0, ac0) :: acs1)) v1 v2
    vl1 al1)
  (Hdom: vertex_in_actions_dom ((id0, ac0) :: acs1) v2)
  (Hend: end_of_actions v1 acs1)
  (Heq: ws = gen_D_walk_segments id0 (v1 :: vl1)),
  exists vl2 : V_list,
    exists al2 : A_list,
      actions_walk ((id0, ac0) :: acs2) v1 v2 vl2 al2.

Lemma actions_end_imply_cons_aux: forall
  (acs1 acs2 : AssocList action) (Heqdom: dom acs1 [=] dom acs2)
  (Hinc : actions_end_imply acs1 acs2)
  (ac0 : action) (id0 : atom) (Hnt: no_AC_tsubst_action ac0)
  (Huniq1: uniq ((id0, ac0) :: acs1)) (Huniq2: uniq ((id0, ac0) :: acs2)) n,
  actions_end_imply_cons_aux_prop acs1 acs2 id0 ac0 n.
Proof.
  intros until n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold actions_end_imply_cons_aux_prop. 
  intros.
  destruct ws as [|[] ws].
  Case "base".
    contradict Heq.
    apply gen_D_walk_segments__nonnil. 
      congruence.
  Case "ind PW_arcs".
    eapply gen_D_walk_segments__cons_PW_arcs_inv in Heq; eauto.
    destruct Heq as [vl' [al' [J1 [J2 [J3 [J4 [J5 [J6 [J7 J8]]]]]]]]]; subst.
    inv J5.
    SCase "vl'=nil".
      clear J1.
      destruct (eq_nil_dec _ v3) as [Hv3_nil | Hv3_not_nil].
      SSCase "v3 = nil".
        subst v3. inv J6. 
        exists nil. exists nil.
        split.
        SSSCase "1".
          constructor; auto.
            destruct (V_eq_dec value_dec v2 (index (value_id id0))) 
              as [Heq | Hneq].
            SSSSCase "1.1.1".
              subst v2. left. simpl. auto.
            SSSSCase "1.1.2".
              assert (actions_walk acs1 v2 v2 nil nil) as Hw.
                split.
                  constructor.
                    eapply vertex_in_actions_dom__neq__avertexes; eauto 1.
                  eapply vertex_in_actions_dom__neq__strengthen_head; eauto 1.
              destruct (Hinc _ _ _ _ Hw) as [vl2 [al2 [Hw2 Hend2]]]; auto.
              destruct Hw2 as [Hw2 Hdom2].
              apply DW_endx_inv in Hw2.
              simpl_env.
              apply avertexes_weakening_head; auto.
        SSSCase "2".
          eapply vertex_in_actions_dom__eq_dom in Hdom; eauto. 
            simpl. fsetdec.
      SSCase "v3 <> nil".
      assert (actions_walk acs1 v v2 v3 a) as Hw.
        apply actions_walk__notin__strengthen_head with (id0:=id0)(ac0:=ac0); auto.
          apply DW_iny_vl in J6; auto.
            intro J. subst v2. congruence.
          split; auto.
      destruct (Hinc _ _ _ _ Hw) as [vl2 [al2 [Hw2 Hend2]]]; auto.
      apply actions_walk__weaken_head with (acs':=[(id0,ac0)]) in Hw2; eauto.
    SCase "vl'<>nil".
      clear J2.
      destruct J1 as [EQ1 [acc' EQ2]]; subst; try congruence.
      symmetry in EQ2.
      apply gen_D_walk_segments__cons_PW_arc_inv in EQ2; auto.
      destruct EQ2 as [v1 [vl' [EQ2 EQ3]]]; subst.
      inv EQ3.
      assert (exists vl2 : V_list, exists al2 : A_list,
                actions_walk ((id0, ac0) :: acs2) (index (value_id id0)) 
                  v2 vl2 al2) as J.
        unfold actions_end_imply_cons_aux_prop in Hrec.
        assert (end_of_actions (index (value_id id0)) acs1) as Hend'.
          eapply uniq_head__end_of_actions; eauto.
        apply Hrec with (y:=length 
                              (gen_D_walk_segments id0 
                                 (index (value_id id0) :: vl')))
           (ws:=gen_D_walk_segments id0 (index (value_id id0) :: vl')) in H; auto.
          assert (HH:=length_gen_D_walk_segments_cons id0 v1
                       (index (value_id id0) :: vl')).
          clear - HH. simpl in *. omega.
      destruct J as [vl2 [al2 Hw2]].
      apply uniq_aarcs__avettexes_aarcs with (acs2:=acs2) in H1; auto.
      destruct H1 as [Hv Ha].
      assert (actions_walk ((id0, ac0) :: acs2) v1 v2 
               (index (value_id id0) :: vl2)
               (A_ends v1 (index (value_id id0)) :: al2)) as Hw'.
        destruct Hw2.
        split; auto.
          constructor; auto.
      destruct (eq_nil_dec _ v3) as [Hv3_nil | Hv3_not_nil].
      SSCase "v3 = nil".
        subst v3. inv J6. eauto.
      SSCase "v3 <> nil".
        assert (actions_walk acs1 v v1 v3 a) as Hw.
          apply actions_walk__notin__strengthen_head with (id0:=id0)(ac0:=ac0); auto.
            apply DW_iny_vl in J6; auto.
              intro J. subst v1. congruence.
            split; auto.
              apply in_D_walk__vertex_in_actions_dom with (z:=v1) in J6; auto.
                apply DW_iny_vl in J6; auto.
        destruct (Hinc _ _ _ _ Hw) as [vl1 [al1 [Hw1 Hend1]]]; auto.
        apply actions_walk__weaken_head with (acs':=[(id0,ac0)]) in Hw1; auto.
        exists (vl1++index (value_id id0)::vl2).
        exists (al1++A_ends v1 (index (value_id id0))::al2).
        destruct Hw2.
        split; auto.
          eapply actions_D_walk_append; eauto.
            constructor; auto.
  Case "ind PW_arc".
    eapply gen_D_walk_segments__cons_PW_arc_inv in Heq; eauto.
    destruct Heq as [v0 [vl' [J7 J8]]]; subst.
    inv J8.
    inv Hq.
    assert (exists vl2 : V_list, exists al2 : A_list,
              actions_walk ((id0, ac0) :: acs2) (index (value_id id0)) 
                v2 vl2 al2) as J.
      unfold actions_end_imply_cons_aux_prop in Hrec.
      assert (end_of_actions (index (value_id id0)) acs1) as Hend'.
        eapply uniq_head__end_of_actions; eauto.
      apply Hrec with (y:=length 
                              (gen_D_walk_segments id0 
                                 (index (value_id id0) :: vl')))
           (ws:=gen_D_walk_segments id0 (index (value_id id0) :: vl')) in H1; auto.
    destruct J as [vl2 [al2 Hw2]].
    exists (index (value_id id0)::vl2).
    exists (A_ends v0 (index (value_id id0))::al2).
    destruct Hw2.
    split; auto.
      apply uniq_aarcs__avettexes_aarcs with (acs2:=acs2) in H6; auto.
      destruct H6 as [Hv Ha].
      constructor; auto.
Qed.

Lemma actions_end_imply_cons: forall acs1 acs2 (Heqdom: dom acs1 [=] dom acs2)
  (Hinc: actions_end_imply acs1 acs2) id0 ac0 (Hnt: no_AC_tsubst_action ac0)
  (Huniq1: uniq (((id0, ac0)::acs1))) (Huniq2: uniq (((id0, ac0)::acs2))), 
  actions_end_imply ((id0, ac0)::acs1) ((id0, ac0)::acs2).
Proof.
  intros. 
  unfold actions_end_imply. intros.
  destruct Hw as [Hw Hdom].
  assert (exists vl2 : V_list, exists al2 : A_list,
            actions_walk ((id0, ac0) :: acs2) v1 v2 vl2 al2) as J.
    eapply actions_end_imply_cons_aux; eauto.
      simpl_env in Hend.
      apply end_of_actions__strengthen_head in Hend; auto.
  destruct J as [vl2 [al2 J]].
  exists vl2. exists al2.
  split; auto.
    eapply eq_dom__end_of_actions; eauto.
      simpl_env. fsetdec.
Qed.

Lemma actions_end_imply_weakening: forall acs1 acs2
  (Heqdom: dom acs1 [=] dom acs2)
  (Hinc: actions_end_imply acs1 acs2) acs (Hnt: no_AC_tsubst_actions acs)
  (Huniq1: uniq (acs++acs1)) (Huniq2: uniq (acs++acs2)), 
  actions_end_imply (acs++acs1) (acs++acs2).
Proof.
  induction acs as [|[id0 ac0] acs]; intros; auto.
    simpl_env in *. simpl.
    inv Huniq1. inv Huniq2.
    inv Hnt.
    apply actions_end_imply_cons; auto.
      simpl_env. fsetdec.
Qed.

(* Lem 56 *)
Lemma actions_eq_weakening: forall acs1 acs2 (Hinc: actions_eq acs1 acs2) acs
  (Heqdom: dom acs1 [=] dom acs2) (Hnt: no_AC_tsubst_actions acs)
  (Huniq1: uniq (acs++acs1)) (Huniq2: uniq (acs++acs2)), 
  actions_eq (acs++acs1) (acs++acs2).
Proof.
  intros.
  destruct Hinc.
  assert (Heqdom': dom acs2 [=] dom acs1). fsetdec.
  split; eauto using actions_end_imply_weakening.
Qed.

(* Lem 57 *)
Lemma acyclic_actions_weakening: forall acs1 acs2 
  (Hinc: actions_len_imply acs2 acs1) acs
  (Hacyc: acyclic_actions (acs++acs1)), acyclic_actions (acs++acs2).
Proof.
  intros.
  apply actions_len_imply_weakening with (acs:=acs) in Hinc.
  unfold acyclic_actions. intros.
  apply Hinc in Hcyc.
  destruct Hcyc as [vl2 [al2 [Hw Hlen]]].
  apply Hacyc in Hw.
  subst.
  eapply len_le_zero__nil; eauto.
Qed.

Lemma list_subst_acyclic_actions_tail: forall acs1 acs2 id0 ac0
  (Hnt: no_AC_tsubst_actions acs2) (Huniq: uniq acs2) (Hin: In (id0,ac0) acs2)
  (Hacyc: acyclic_actions (acs1++acs2)),
  acyclic_actions (acs1++(ListComposedPass.subst_actions id0 ac0 acs2)).
Proof.
  intros.
  apply list_subst_actions_len_imply_inv with (id0:=id0)(ac0:=ac0) 
    in Huniq; auto.
    apply acyclic_actions_weakening with (acs:=acs1) in Huniq; auto.
Qed.

Lemma list_subst_acyclic_actions_cons_tail: forall acs1 acs2 id0 ac0
  (Hnt: no_AC_tsubst_actions ((id0,ac0)::acs2)) (Huniq: uniq ((id0,ac0)::acs2))
  (Hacyc: acyclic_actions (acs1++(id0,ac0)::acs2)),
  acyclic_actions 
    (acs1++(id0,ac0)::(ListComposedPass.subst_actions id0 ac0 acs2)).
Proof.
  intros.
  apply list_subst_actions_len_imply_inv with (id0:=id0)(ac0:=ac0) 
    in Huniq; auto.
    apply acyclic_actions_weakening with (acs:=acs1) in Huniq; auto.
      simpl_env in Huniq.
      rewrite list_subst_actions_app in Huniq.
      erewrite list_subst_acyclic_actions_is_refl in Huniq; eauto.

      xsolve_in_list.
Qed.

(* Lem 58 *)
Definition substs_actions_eq_prop (n:nat) := forall acs
  (Hlen: (length acs = n)%nat) (Huniq: uniq acs) 
  (Hnt: no_AC_tsubst_actions acs)
  (Hacyc: acyclic_actions acs),
  actions_eq acs (substs_actions acs).

Lemma substs_actions_eq_aux: forall n,
  substs_actions_eq_prop n.
Proof.
  intros.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold substs_actions_eq_prop in *; intros.
  destruct acs as [|[id0 ac0] acs].
  Case "1".
    unfold_substs_actions.
    apply actions_eq_refl; auto.
  Case "2".
    unfold_substs_actions.
    assert (Hacyc':=Hacyc).
    apply list_subst_actions_acyclic with (id0:=id0)(ac0:=ac0) in Hacyc'; 
      simpl; auto.
    assert (no_AC_tsubst_actions (ListComposedPass.subst_actions id0 ac0 acs)) 
      as Hnt'.
      solve_no_AC_tsubst.
    assert (Huniq':=Huniq).
    assert (J:=Huniq').
    eapply list_subst_actions_eq with (id0:=id0)(ac0:=ac0) in J; simpl; eauto.
    simpl_env in *.
    unfold ListComposedPass.subst_actions in *.
    remember (action2value ac0) as ov0.
    destruct ov0 as [v0|].
    SCase "2.1".
      simpl in *.
      assert (match ac0 with
              | AC_remove => ac0
              | AC_vsubst v1 => AC_vsubst (v1 {[v0 // id0]})
              | AC_tsubst _ => ac0
              end = ac0) as EQ. 
        eapply acyclic_actions_has_no_ident_map; eauto.
      rewrite EQ in *. 
      simpl_env in *.
      remember (ListMap.map
                (fun ac : action =>
                 match ac with
                 | AC_remove => ac
                 | AC_vsubst v1 => AC_vsubst (v1 {[v0 // id0]})
                 | AC_tsubst _ => ac
                 end) acs) as acs'.
      assert (uniq ([(id0, ac0)] ++ acs')) as Huniq''.
        eapply map_fst_uniq in Huniq'; eauto.
        simpl. f_equal. subst acs'. apply map__map_fst.
      assert (uniq ([(id0, ac0)] ++ substs_actions acs')) as Huniq'''.
        eapply map_fst_uniq in Huniq''; eauto.
        simpl. f_equal. apply substs_actions__map_fst.
      apply actions_eq_trans with (acs2:=[(id0, ac0)] ++ acs'); auto.
      SSCase "2.1.1".
        assert (dom acs'[=]dom (substs_actions acs')) as Heqdom.         
          apply substs_actions__dom; auto.
        apply actions_eq_weakening; try solve [auto | solve_no_AC_tsubst].
        eapply Hrec; eauto.
        SSSCase "2.1.2.1.1".
          subst x acs'. unfold ListMap.map.
          rewrite map_length. omega.
        SSSCase "2.1.2.1.2".
          solve_uniq.
        SSSCase "2.1.2.1.3".
          apply acyclic_actions_strengthening in Hacyc'; auto.
    SCase "2.2".
      assert (dom acs[=]dom (substs_actions acs)) as Heqdom.
        apply substs_actions__dom; auto.
      apply actions_eq_weakening; try solve [auto | solve_no_AC_tsubst].
      SSCase "2.2.1".
        eapply Hrec; eauto.
        SSSCase "2.2.1.1".
          subst x. simpl. omega.
        SSSCase "2.2.1.2".
          solve_uniq.
          apply acyclic_actions_strengthening in Hacyc; auto.
      SSCase "2.2.2".
        eapply map_fst_uniq in Huniq'; eauto.
        simpl. f_equal. apply substs_actions__map_fst.
Qed.

Lemma substs_actions_eq: forall acs (Huniq: uniq acs) 
  (Hnt: no_AC_tsubst_actions acs) (Hacyc: acyclic_actions acs), 
  actions_eq acs (substs_actions acs).
Proof.
  intros.
  assert (J:=@substs_actions_eq_aux (length acs)).
  unfold substs_actions_eq_prop in J.
  auto.
Qed.

(* Lem 58a *)
Definition substs_actions__AC_remove_prop (n:nat) := forall acs
  (Hlen: (length acs = n)%nat) id0,
  lookupAL _ acs id0 = Some AC_remove <->
    lookupAL _ (substs_actions acs) id0 = Some AC_remove.  

Lemma substs_actions__AC_remove_aux: forall n,
  substs_actions__AC_remove_prop n.
Proof.
  intros.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold substs_actions__AC_remove_prop in *; intros.
  destruct acs as [|[id1 ac1] acs].
  Case "1".
    unfold_substs_actions. tauto.
  Case "2".
    unfold_substs_actions.
    simpl.
    destruct_if; try tauto.
    transitivity (lookupAL action
                   (ListComposedPass.subst_actions id1 ac1 acs) id0 =
                   ret AC_remove).
    SCase "2.1".
      apply list_subst_actions__AC_remove.
    SCase "2.2".
      apply Hrec with (y:=length acs); auto.
        rewrite <- list_subst_actions__length; auto. 
Qed.

Lemma substs_actions__AC_remove: forall acs id0,
  lookupAL _ acs id0 = Some AC_remove <->
    lookupAL _ (substs_actions acs) id0 = Some AC_remove.  
Proof.
  intros.
  assert (J:=@substs_actions__AC_remove_aux (length acs)).
  unfold substs_actions__AC_remove_prop in J.
  auto.
Qed.

(* Lem 59 *)

(*****************)
Fixpoint remove_from_actions (acs: AssocList action) (id0:id) : 
  option (action * AssocList action) :=
match acs with
| nil => None
| (id1, ac1)::acs' =>
    if (id_dec id0 id1) 
    then Some (ac1, acs')
    else 
      match remove_from_actions acs' id0 with
      | Some (ac2, acs'') => Some (ac2, (id1, ac1)::acs'')
      | None => None
      end
end.

Lemma remove_from_actions_spec0: forall acs ac0 acs' id0
  (Heq_anonymous : ret (ac0, acs') = remove_from_actions acs id0),
  (length acs' < length acs)%nat.
Proof.
  induction acs as [|[id1 ac1]]; intros; simpl in *; try congruence.
    destruct_dec.
      inv Heq_anonymous.
      omega.

      remember (remove_from_actions acs id0) as R.
      destruct R as [[]|]; inv Heq_anonymous.
      apply IHacs in HeqR. simpl. omega.          
Qed.

Lemma remove_from_actions_spec1: forall acs id0
  (Hin: id0 `in` dom acs), 
  exists acs1, exists ac0, exists acs2,
    remove_from_actions acs id0 = Some (ac0, acs1++acs2) /\
    acs = acs1 ++ (id0,ac0) :: acs2.
Proof.
  induction acs as [|[id1 ac1]]; simpl; intros.
    fsetdec.

    destruct_dec.
      exists nil. exists ac1. exists acs. auto.
 
      assert (id0 = id1 \/ id0 `in` dom acs) as Hin'.
        fsetdec.
      destruct Hin'; try congruence.
      apply IHacs in H.
      destruct H as [acs1 [ac0 [acs2 [J EQ]]]]; subst.
      rewrite J.
      exists ((id1, ac1) :: acs1). exists ac0. exists acs2.
      simpl_env. auto.
Qed.

Lemma remove_from_actions_spec2: forall acs id0
  (Hin: id0 `notin` dom acs), 
  remove_from_actions acs id0 = None.
Proof.
  induction acs as [|[id1 ac1]]; simpl; intros.
    auto.

    destruct_dec.
      fsetdec.

      destruct_notin.
      apply IHacs in NotInTac0.
      rewrite NotInTac0. auto. 
Qed.

Lemma remove_from_actions_spec3: forall acs ac0 acs' id0
  (Heq_anonymous : ret (ac0, acs') = remove_from_actions acs id0), 
  exists acs1, exists acs2, 
    acs = acs1 ++ (id0,ac0) :: acs2 /\ acs' = acs1 ++ acs2.
Proof.
  induction acs as [|[id1 ac1]]; simpl; intros.
    congruence.

    destruct_dec.
      inv Heq_anonymous.
      exists nil. exists acs. auto.

      inv_mbind.
      apply IHacs in HeqR.
      inv H0.
      destruct HeqR as [acs1 [acs2 [J1 J2]]]; subst.
      exists ((id1, ac1)::acs1). exists acs2. auto.
Qed.

Lemma remove_from_actions_spec4: forall r acs id0
  (Heq_anonymous : ret r = remove_from_actions acs id0), 
  id0 `in` dom acs.
Proof.
  intros.
  destruct r.
  apply remove_from_actions_spec3 in Heq_anonymous.
  destruct Heq_anonymous as [acs1 [acs2 [J1 J2]]]; subst.
  simpl_env. auto.
Qed.

Lemma remove_from_actions_spec5: forall acs ac0 acs' id0
  (Heq_anonymous : ret (ac0, acs') = remove_from_actions acs id0), 
  incl acs' acs.
Proof.
  intros.
  apply remove_from_actions_spec3 in Heq_anonymous.
  destruct Heq_anonymous as [acs1 [acs2 [J1 J2]]]; subst.
  apply incl_insert.
Qed.

Lemma remove_from_actions_spec6: forall acs ac0 acs' id0 x y vl al
  (Heq_anonymous : ret (ac0, acs') = remove_from_actions acs id0)
  (Hw: D_walk (avertexes acs') (aarcs acs') x y vl al),
  D_walk (avertexes acs) (aarcs acs) x y vl al.
Proof.
  intros.
  eapply D_walk_sub in Hw; eauto.
    intros. eapply avertexes_incl; eauto. 
    eapply remove_from_actions_spec5; eauto.

    intros. eapply aarcs_incl; eauto. 
    eapply remove_from_actions_spec5; eauto.
Qed.

Lemma remove_from_actions_spec7: forall acs id0
  (Hnone: remove_from_actions acs id0 = None),
  lookupAL action acs id0 = None.
Proof.
  induction acs as [|[id1 ac1]]; simpl; intros.
    auto.

    destruct_dec.
    destruct_if.
      congruence.

      remember (remove_from_actions acs id0) as R.
      destruct R as [[]|]; inv Hnone; eauto.
Qed.

Lemma remove_from_actions_spec8: forall acs ac0 acs' id0
  (Heq_anonymous : ret (ac0, acs') = remove_from_actions acs id0)
  (Huniq: uniq acs), uniq acs'.
Proof.
  intros.
  apply remove_from_actions_spec3 in Heq_anonymous.
  destruct Heq_anonymous as [acs1 [acs2 [J1 J2]]]; subst.
  solve_uniq.
Qed.

Lemma remove_from_actions_spec9: forall acs (Huniq: uniq acs) id0 ac0
  (Hin: lookupAL _ acs id0 = Some ac0), 
  exists acs1, exists acs2,
    acs = acs1 ++ (id0,ac0) :: acs2 /\
    remove_from_actions acs id0 = Some (ac0, acs1++acs2).
Proof.
  induction 1; simpl; intros.
    inv Hin.

    destruct_if; destruct_dec.
      exists nil. exists E. eauto.

      apply IHHuniq in H1.
      destruct H1 as [acs1 [acs2 [H1 Hrm]]]; subst.  
      exists ((x,a)::acs1). exists acs2.
      split; auto.
        rewrite Hrm. auto.
Qed.

(***********************)
Program Fixpoint find_root (v0:value) (acs: AssocList action)
  {measure (length acs)} : option value :=
match v0 with
| value_const _ => Some v0
| value_id id0 =>
    match remove_from_actions acs id0 with 
    | None => Some v0
    | Some (ac0, acs') => 
      match action2value ac0 with
      | Some v0' => find_root v0' acs'
      | None => None
      end
    end
end.
Next Obligation.
  eapply remove_from_actions_spec0; eauto.
Qed.

Ltac fold_find_root :=
match goal with
| |- context [find_root_func (existT _ ?arg1 ?arg2)] => 
       fold (find_root arg1 arg2)
end.

Ltac unfold_find_root :=
match goal with
| |- appcontext [find_root ?arg ?acs] =>
   unfold find_root; unfold find_root_func;
   rewrite Wf.WfExtensionality.fix_sub_eq_ext;
   simpl;
   match goal with
   | |- context [remove_from_actions acs ?id0] =>
     let R1:=fresh "R1" in
     let ac:=fresh "ac" in
     let acs':=fresh "acs'" in
     remember (remove_from_actions acs id0) as R1;
     destruct R1 as [[ac acs']|];
     try (
       let R2:=fresh "R2" in
       let v0:=fresh "v0" in
       remember (action2value ac) as R2;
       destruct R2 as [v0|]
     )
   | _ => idtac
   end;
   repeat Wf.fold_sub find_root_func;
   repeat fold_find_root
end.

Require Import Program.Equality.

(***************)
Lemma find_root__const_spec: forall acs c0,
  find_root (value_const c0) acs = Some (value_const c0).
Proof.
  intros.
  unfold_find_root. auto.
Qed.

(***************)
Lemma find_root__id_notin: forall acs' id1 
  (Hend' : lookupAL action acs' id1 = merror),
  find_root (value_id id1) acs' = ret value_id id1.
Proof.
  intros.
  unfold_find_root; try solve [
    auto |
    apply remove_from_actions_spec4 in HeqR1;
    apply lookupAL_None_notindom in Hend';
    fsetdec
  ].
Qed.

Lemma find_root__id_notin': forall acs' id1 
  (Hend' : id1 `notin` dom acs'),
  find_root (value_id id1) acs' = ret value_id id1.
Proof.
  intros.
  apply find_root__id_notin.
  apply notin_lookupAL_None; auto.
Qed.

Lemma unfold_find_root_id: forall id0 acs,
  find_root (value_id id0) acs =
    match remove_from_actions acs id0 with 
    | None => Some (value_id id0)
    | Some (ac0, acs') => 
      match action2value ac0 with
      | Some v0' => find_root v0' acs'
      | None => None
      end
    end.
Proof.
  intros.
  unfold_find_root; auto.
Qed.

(*********************)
Definition find_root__id_spec_prop (n:nat) := forall acs
  (Hlen: (length acs = n)%nat) id0 (v1:value) (Hacyc: acyclic_actions acs)
  (Hnt: no_AC_tsubst_actions acs)
  (Hv: avertexes acs (index (value_id id0)))
  (Hfind: find_root (value_id id0) acs = Some v1),
  exists vl, exists al, exists acs',
    D_walk (avertexes acs) (aarcs acs) (index v1) (index (value_id id0)) vl al /\
    (forall id1, (In (index (value_id id1)) vl \/ id1 `in` dom acs') 
                 <-> id1 `in` dom acs) /\
    end_of_actions (index v1) acs'.

Require Import Program.Tactics.

Lemma find_root__id_spec_aux: forall n, find_root__id_spec_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold find_root__id_spec_prop in *; intros.
  revert Hfind.
  unfold_find_root; intro H.
  Case "1".
    assert (forall id0 (ac0:action) (acs1 acs2 : list (id * action)) id1,
            In (index (value_id id1)) [index (value_id id0)] \/
            id1 `in` dom (acs1 ++ acs2) <->
            id1 `in` dom (acs1 ++ (id0, ac0) :: acs2)) as Hin'.
      clear.
      intros.
      split; intro H.
        destruct H as [H | H].
          simpl in H.
          destruct H as [H | H]; inv H.
          simpl_env. fsetdec.

          simpl_env. simpl_env in H. fsetdec.
        simpl_env. simpl. simpl_env in H. fsetdec.
    assert (EQ:=HeqR1).
    apply remove_from_actions_spec3 in EQ.
    destruct EQ as [acs1 [acs2 [EQ1 EQ2]]]; subst.
    assert (incl (acs1 ++ acs2) (acs1 ++ (id0, ac) :: acs2)) as Hinc'.
      apply incl_insert.
    destruct ac as [|v2|t2]; tinv HeqR2.
    SCase "1.1".
      assert (D_walk (avertexes (acs1 ++ (id0, AC_vsubst v2) :: acs2))
               (aarcs (acs1 ++ (id0, AC_vsubst v2) :: acs2))
               (index v2) (index (value_id id0)) 
               [index (value_id id0)]
               [A_ends (index v2) (index (value_id id0))]) as Hw'.
      SSCase "1.1.0".
        constructor.
        SSSCase "1.1.0.1".
          constructor.
            left. simpl. simpl_env. auto.
        SSSCase "1.1.0.2".
          right. simpl. exists id0. exists (AC_vsubst v2). 
          split; auto. xsolve_in_list.
        SSSCase "1.1.0.3".
          simpl. exists (AC_vsubst v2). split; auto. xsolve_in_list.
      destruct v2 as [id2|c2]; inv HeqR2.
      SSCase "1.1.1".
        remember (lookupAL _ (acs1++acs2) id2) as R.
        destruct R as [r|].
        SSSCase "1.1.1.1".
          apply Hrec with (y:=length (acs1++acs2)) in H; auto.
          SSSSCase "1.1.1.1.1".
            destruct H as [vl [al [acs' [Hw [Heq Hend]]]]].
            assert (
              D_walk (avertexes (acs1 ++ (id0, AC_vsubst (value_id id2)) :: acs2))
                (aarcs (acs1 ++ (id0, AC_vsubst (value_id id2)) :: acs2)) 
                (index v1) (index (value_id id0)) (vl ++ [index (value_id id0)])
                (al ++ [A_ends (index (value_id id2)) (index (value_id id0))])
              ) as Hw''.
              apply DWalk_append with (y:=index (value_id id2)); auto.
                eapply D_walk_sub in Hw; eauto.
                  intros. eapply avertexes_incl; eauto. 
                  intros. eapply aarcs_incl; eauto. 
            exists (vl++[index (value_id id0)]).
            exists (al++[A_ends (index (value_id id2)) (index (value_id id0))]).
            exists ((id0, AC_vsubst (value_id id2))::acs').
            split; auto.
            split; auto.
            SSSSSCase "1.1.1.1.1.2".
              intros. 
              split; intro H.
              SSSSSSCase "1.1.1.1.1.2.1".
                destruct H as [H | H].
                SSSSSSSCase "1.1.1.1.1.2.1.1".
                  apply in_app_or in H.
                  destruct H as [H | H].
                    assert (id1 `in` dom (acs1 ++ acs2)) as Hin.
                      apply Heq; auto.
                    simpl_env. simpl_env in Hin. fsetdec.
          
                    simpl in H.
                    destruct H as [H | H]; inv H.
                    simpl_env. fsetdec.
                SSSSSSSCase "1.1.1.1.1.2.1.2".
                 assert (id1 = id0 \/ id1 `in` dom acs') as Hin.
                   simpl_env. simpl_env in H. fsetdec.
                 simpl_env.
                 destruct Hin as [Hin | Hin]; subst.
                   fsetdec.
          
                   assert (id1 `in` dom (acs1 ++ acs2)) as Hin''.
                     apply Heq; auto.
                   simpl_env. simpl_env in Hin''. fsetdec.
              SSSSSSCase "1.1.1.1.1.2.2".        
                assert (id1 = id0 \/ id1 `in` dom (acs1++acs2)) as Hin.
                  simpl_env. simpl_env in H. fsetdec.
                simpl_env.
                destruct Hin as [Hin | Hin]; subst; auto.
                  apply Heq in Hin.
                  destruct Hin; auto.
                    left. xsolve_in_list.
            SSSSSCase "1.1.1.1.1.3".
              destruct v1 as [id1|c1]; auto.
              simpl.
              destruct_if.
                apply Hacyc in Hw''.
                contradict Hw''.
                apply app_cons_not_nil.
          SSSSCase "1.1.1.1.2".
            apply remove_from_actions_spec0 in HeqR1; auto.
          SSSSCase "1.1.1.1.3".
            eapply acyclic_actions_incl; eauto.
          SSSSCase "1.1.1.1.4".
            eapply Forall_incl; eauto.
          SSSSCase "1.1.1.1.5".
            left. simpl. eapply lookupAL_Some_indom; eauto.
        SSSCase "1.1.1.2".
          symmetry in HeqR.
          rewrite find_root__id_notin in H; auto. 
          inv H.
          exists [index (value_id id0)].
          exists [A_ends (index (value_id id2)) (index (value_id id0))].
          exists (acs1++acs2).
          split; auto.
      SSCase "1.1.2".
        rewrite find_root__const_spec in H. inv H. 
        exists [index (value_id id0)].
        exists [A_ends (index (value_const c2)) (index (value_id id0))].
        exists (acs1++acs2).
        split; auto.
    SCase "1.2".
      solve_no_AC_tsubst.
  Case "2".
    congruence.
  Case "3".
    inv H. 
    exists nil. exists nil. exists acs.
    split. constructor; auto.
    split. intros. split; intro H; tauto.
           apply remove_from_actions_spec7; auto.          
Qed.

Lemma find_root__id_spec: forall acs id0 (v1:value) (Hacyc: acyclic_actions acs)
  (Hnt: no_AC_tsubst_actions acs) (Hv: avertexes acs (index (value_id id0)))
  (Hfind: find_root (value_id id0) acs = Some v1),
  exists vl, exists al, exists acs',
    D_walk (avertexes acs) (aarcs acs) (index v1) (index (value_id id0)) vl al /\
    (forall id1, (In (index (value_id id1)) vl \/ id1 `in` dom acs') 
                 <-> id1 `in` dom acs) /\
    end_of_actions (index v1) acs'.
Proof.
  intros.
  assert (J:=@find_root__id_spec_aux (length acs)).
  unfold find_root__id_spec_prop in J.
  auto.
Qed.

(*******************)
Lemma find_root__D_walk_end: forall acs id0 (v1:value) 
  (Hnt: no_AC_tsubst_actions acs) (Hacyc: acyclic_actions acs) 
  (Hv: avertexes acs (index (value_id id0)))
  (Hfind: find_root (value_id id0) acs = Some v1),
  exists vl, exists al,
    D_walk (avertexes acs) (aarcs acs) (index v1) (index (value_id id0)) vl al /\
    end_of_actions (index v1) acs.
Proof.
  intros.
  apply find_root__id_spec in Hfind; auto.
  destruct Hfind as [vl [al [acs' [Hw [Heq Hend]]]]].
  exists vl. exists al.
  split; auto.
    simpl in *.
    destruct v1; auto.
    remember (lookupAL action acs id5) as R.
    destruct R; auto.
    symmetry in HeqR.
    apply lookupAL_None_notindom in Hend.
    apply lookupAL_Some_indom in HeqR.
    apply Heq in HeqR.
    destruct HeqR as [H | H].
      eapply DW_split'' in Hw; eauto.
      destruct Hw as [vl2 [vl1 [al1 [al2 [EQ [Hw1 [Hw2 EQ']]]]]]]; subst.
      apply Hacyc in Hw2.
      apply app_cons_not_nil in Hw2. tauto.

      fsetdec.
Qed.

(********************)
Definition actions_walk_end__find_root_prop (n:nat) := forall acs
  (Hlen: (length acs = n)%nat) id0 (v1:value) vl al 
  (Hacyc: acyclic_actions acs) (Huniq: uniq acs)
  (Hw: actions_walk acs (index v1) (index (value_id id0)) vl al)
  (Hend: end_of_actions (index v1) acs),
  find_root (value_id id0) acs = Some v1.

Lemma actions_walk_end__find_root_aux: forall n, 
  actions_walk_end__find_root_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold actions_walk_end__find_root_prop in *; intros.
  destruct Hw as [Hw Hdom].
  assert (J:=Hw).
  apply D_walk_nonend_inv in J; auto.
  destruct J as [y [vl' [al' [Hw' [EQ1 [EQ2 [Hin1 Hin2]]]]]]]; subst.
  unfold_find_root.
  Case "1".
    assert (y=index v0) as EQ.
      apply remove_from_actions_spec3 in HeqR1.
      destruct HeqR1 as [acs1 [acs2 [EQ1 EQ2]]]; subst.
      destruct y as [a]. 
      simpl in Hin1. destruct Hin1 as [ac1 [Hin1 Ha2v]].
      apply In_uniq_eq in Hin1; auto. subst.
      symmetry_ctx. uniq_result. auto.
    subst.
    destruct v0 as [id1|c1].
    SCase "1.1".
      assert (end_of_actions (index v1) acs') as Hend'.
        eapply end_of_actions__incl in Hend; eauto.
          apply remove_from_actions_spec5 in HeqR1; auto.
      destruct (eq_nil_dec _ vl') as [Hnil | Hnnil]; subst.
      SSCase "1.1.1".
        inv Hw'.
        clear - Hend'.
        simpl in Hend'.
        apply find_root__id_notin; auto.
      SSCase "1.1.2".
        apply Hrec with (y:=length acs')(vl:=vl')(al:=al'); eauto.
        SSSCase "1.1.0".
         apply remove_from_actions_spec0 in HeqR1; auto.
        SSSCase "1.1.1".         
         eapply acyclic_actions_incl in Hacyc; eauto.
         eapply remove_from_actions_spec5 in HeqR1; auto.
        SSSCase "1.1.a".
         eapply remove_from_actions_spec8 in HeqR1; auto.
        SSSCase "1.1.2".
         assert (id1 <> id0) as Hneq'.
          destruct (id_dec id1 id0); auto.
            subst id1.
            assert (D_walk (avertexes acs) (aarcs acs)
                           (index (value_id id0)) (index (value_id id0))
                           [index (value_id id0)]
                           [A_ends (index (value_id id0)) 
                                   (index (value_id id0))]) as Hw''.
              constructor; auto.
                constructor; auto.
            apply Hacyc in Hw''.
            inv Hw''.
         split.
         SSSSCase "1.1.2.1".
           apply remove_from_actions_spec3 in HeqR1.
           destruct HeqR1 as [acs1 [acs2 [EQ1 EQ2]]]; subst.
           eapply D_walk_weakening; eauto.
           SSSSSCase "1.1.2.1.1".
             intros z Hinz.
             destruct (V_eq_dec value_dec z (index v1)) as [Heq | Hneq]; subst.
             SSSSSSCase "1.1.2.1.1.1".
               assert (avertexes (acs1 ++ (id0, ac) :: acs2) (index v1)) as Hina.
                 apply DW_endx_inv in Hw'; auto.
               destruct Hina as [Hina | Hina]; try solve 
                 [apply end_of_actions__vertex_notin_actions_dom in Hend; 
                  auto; tauto].
               right.
               destruct Hina as [id2 [ac2 [Hina Ha2v]]].
               exists id2. exists ac2.
               split; auto.
                 apply in_middle_split in Hina.
                 destruct Hina as [Hina | Hina]; auto.
                 inv Hina. 
                 symmetry_ctx. uniq_result.
                 apply Hacyc in Hw'.
                 contradict Hw'; auto.
             SSSSSSCase "1.1.2.1.1.2".
               simpl in Hinz.
               destruct Hinz as [Hinz | Hinz]; try congruence.
               assert (avertexes (acs1 ++ (id0, ac) :: acs2) z) as Hina.
                 eapply DW_invl_inv in Hw; eauto.
                   xsolve_in_list.
               apply DW_split'' with (x:=z) in Hw'; auto.
               destruct Hw' as [vl2 [vl1 [al1 [al2 [EQ1 [Hw1 [Hw2 EQ2]]]]]]].
               subst vl'.
               destruct Hina as [Hina | HIna].
               SSSSSSSCase "1.1.2.1.1.2.1".
                 left.
                 destruct z as [[]]; tinv Hina.
                 simpl in Hina. simpl.
                 assert (id5 = id0 \/ id5 `in` dom (acs1 ++ acs2)) as Hin.
                   simpl_env. simpl_env in Hina. fsetdec.
                 destruct Hin as [Hin | Hin]; subst; auto.
                 assert (D_walk (avertexes (acs1 ++ (id0, ac) :: acs2))
                                (aarcs (acs1 ++ (id0, ac) :: acs2))
                                (index (value_id id1)) (index (value_id id1))
                                ((index (value_id id0))::vl1)
                                (A_ends (index (value_id id1)) 
                                  (index (value_id id0))::al1)) as Hw'.
                   constructor; auto.
                 apply Hacyc in Hw'.
                 inv Hw'.
               SSSSSSSCase "1.1.2.1.1.2.2".
                 destruct z as [a].
                 simpl in HIna.
                 destruct HIna as [id2 [ac2 [HIna Ha2v]]].
                 apply in_middle_split in HIna.
                 destruct HIna as [Hin | Hin].
                 SSSSSSSSCase "1.1.2.1.1.2.2.1".
                   right. simpl. eauto.
                 SSSSSSSSCase "1.1.2.1.1.2.2.2".
                   inv Hin.
                   symmetry in HeqR2.
                   apply action2id__inv in HeqR2; subst ac.
                   inv Ha2v.
                   apply DW_last_split in Hw2.
                   destruct Hw2 as [v1' [al' [Hw2 [Hw3 EQ]]]]; subst.
                   apply DW_inel_ina with (x':=v1')
                                          (y':=index (value_id id1)) in Hw3;
                     try solve [simpl; auto].
                   simpl in Hw3. destruct v1' as [id3].
                   destruct Hw3 as [ac3 [Hw3 Ha2v']].
                   symmetry_ctx. uniq_result.
                   apply in_middle_split in Hw3.
                   destruct Hw3 as [Hin | Hin].
                   SSSSSSSSSCase "1.1.2.1.1.2.2.2.2.1".
                     left. simpl.
                     apply In_InDom in Hin; auto.
                   SSSSSSSSSCase "1.1.2.1.1.2.2.2.2.2".
                     inv Hin. congruence. 
           SSSSSCase "1.1.2.1.2".
             intros [z1 z2] Hinz.
             assert (aarcs (acs1 ++ (id0, ac) :: acs2) (A_ends z1 z2)) as Hina.
               eapply DW_inel_ina in Hw'; eauto.
             destruct z1 as [a1]; destruct z2 as [[id2|]]; tinv Hina.
             simpl in Hina. simpl.
             destruct Hina as [ac1 [Hina Ha2v]].
             apply in_middle_split in Hina.
             destruct Hina as [Hin | Hin]; eauto.
             inv Hin. inv HeqR2.
             assert (J:=Hw').
             eapply DW_inxyel_inyvl in J; eauto.
             simpl in J.
             destruct J as [J | J].
             SSSSSSCase "1.1.2.1.2.1".
               inv J.
               apply Hacyc in Hw.
               apply app_cons_not_nil' in Hw. tauto.
             SSSSSSCase "1.1.2.1.2.2".
               symmetry in H0.
               apply action2id__inv in H0; subst ac.
               apply DW_split'' with (x:=index (value_id id0)) in Hw'; auto.
               destruct Hw' as [vl2 [vl1 [al1 [al2 [EQ1 [Hw1 [Hw2 EQ2]]]]]]].
               assert (D_walk (avertexes 
                                (acs1 ++ (id0, AC_vsubst (value_id id1)) :: acs2))
                              (aarcs 
                                (acs1 ++ (id0, AC_vsubst (value_id id1)) :: acs2))
                              (index (value_id id1)) (index (value_id id1))
                              ((index (value_id id0))::vl1)
                              (A_ends (index (value_id id1)) 
                                      (index (value_id id0))::al1)) as Hw''.  
                 constructor; auto.                 
               apply Hacyc in Hw''.
               inv Hw''.
         SSSSCase "1.1.2.2".
           apply in_D_walk__vertex_in_actions_dom with (z:=index (value_id id1)) 
             in Hw'; auto.
           SSSSSCase "1.1.2.2.1".
             apply remove_from_actions_spec3 in HeqR1.
             destruct HeqR1 as [acs1 [acs2 [EQ1 EQ2]]]; subst.
             simpl in Hw'. simpl.
             simpl_env in Hw'. simpl_env. fsetdec.
           SSSSSCase "1.1.2.2.2".
             apply DW_iny_vl in Hw'; auto.
    SCase "1.2".
       rewrite find_root__const_spec.
       assert (J:=Hw').
       inv J; auto.
       apply in_D_walk__vertex_in_actions_dom with (z:=index (value_const c1)) 
         in Hw'; auto.
         inv Hw'.
         apply DW_iny_vl in Hw'; auto. 
           intro J. inv J.         
  Case "2".
    destruct y.
    simpl in Hin1. 
    destruct Hin1 as [ac1 [Hin1 Ha2v]].
    apply remove_from_actions_spec3 in HeqR1.
    destruct HeqR1 as [acs1 [acs2 [EQ1 EQ2]]]; subst.
    apply In_uniq_eq in Hin1; auto. subst.
    uniq_result.
  Case "3".
    simpl in Hdom. 
    symmetry in HeqR1.
    apply remove_from_actions_spec7 in HeqR1.
    apply lookupAL_None_notindom in HeqR1. 
    fsetdec.
Qed.

Lemma actions_walk_end__find_root: forall acs id0 (v1:value) vl al
  (Hacyc: acyclic_actions acs) (Huniq: uniq acs)
  (Hw: actions_walk acs (index v1) (index (value_id id0)) vl al)
  (Hend: end_of_actions (index v1) acs),
  find_root (value_id id0) acs = Some v1.
Proof.
  intros.
  assert (J:=@actions_walk_end__find_root_aux (length acs)).
  unfold actions_walk_end__find_root_prop in J.
  eauto.
Qed.

(* Lem 59a *)
Definition find_root__remove_spec_prop (n:nat) := forall acs
  (Hlen: (length acs = n)%nat) id0
  (Hfind: find_root (value_id id0) acs = None),
  exists vl, exists al, exists id1,
    D_walk (avertexes acs) (aarcs acs) (index (value_id id1)) 
                                       (index (value_id id0)) vl al /\
    In (id1, AC_remove) acs.

Lemma find_root__remove_spec_aux: forall n, find_root__remove_spec_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold find_root__remove_spec_prop in *; intros.
  revert Hfind.
  unfold_find_root; intro H.
  Case "1".
    assert (EQ:=HeqR1).
    apply remove_from_actions_spec3 in EQ.
    destruct EQ as [acs1 [acs2 [EQ1 EQ2]]]; subst.
    assert (incl (acs1 ++ acs2) (acs1 ++ (id0, ac) :: acs2)) as Hinc'.
      apply incl_insert.
    destruct ac as [|v2|t2]; tinv HeqR2.
    SCase "1.1".
      assert (D_walk (avertexes (acs1 ++ (id0, AC_vsubst v2) :: acs2))
               (aarcs (acs1 ++ (id0, AC_vsubst v2) :: acs2))
               (index v2) (index (value_id id0)) 
               [index (value_id id0)]
               [A_ends (index v2) (index (value_id id0))]) as Hw'.
        constructor.
          constructor.
            left. simpl. simpl_env. auto.
          right. simpl. exists id0. exists (AC_vsubst v2). 
            split; auto. xsolve_in_list.
          simpl. exists (AC_vsubst v2). 
            split; auto. xsolve_in_list.
      destruct v2 as [id2|c2]; inv HeqR2.
      SSCase "1.1.1".
        apply Hrec with (y:=length (acs1++acs2)) in H; auto.
        SSSCase "1.1.1".
          destruct H as [vl [al [id1 [Hw Hin]]]].
          exists (vl ++ [index (value_id id0)]).
          exists (al ++ [A_ends (index (value_id id2)) (index (value_id id0))]).
          exists id1.
          split.
          SSSSCase "1.1.1.1".
            apply DWalk_append with (y:=index (value_id id2)); auto.
              eapply D_walk_sub in Hw; eauto.
                intros. eapply avertexes_incl; eauto.             
                intros. eapply aarcs_incl; eauto. 
          SSSSCase "1.1.1.2".
            repeat xsolve_in_list. 
          SSSSCase "1.1.1.3".
            apply remove_from_actions_spec0 in HeqR1; auto.
      SSCase "1.1.2".
        rewrite find_root__const_spec in H. inv H. 
    SCase "1.2".
      inv HeqR2.
      rewrite find_root__const_spec in H. inv H. 
  Case "2".
    destruct ac; inv HeqR2.
    exists nil. exists nil. exists id0.
    assert (EQ:=HeqR1).
    apply remove_from_actions_spec3 in EQ.
    destruct EQ as [acs1 [acs2 [EQ1 EQ2]]]; subst.
    split.
      constructor. 
        left. simpl. simpl_env. fsetdec.
      xsolve_in_list.
  Case "3".
    inv H. 
Qed.

Lemma find_root__remove_spec: forall acs id0
  (Hfind: find_root (value_id id0) acs = None),
  exists vl, exists al, exists id1,
    D_walk (avertexes acs) (aarcs acs) (index (value_id id1)) 
                                       (index (value_id id0)) vl al /\
    In (id1, AC_remove) acs.
Proof.
  intros.
  assert (J:=@find_root__remove_spec_aux (length acs)).
  unfold find_root__remove_spec_prop in J.
  auto.
Qed.

(* Lem 59b *)
Definition wf_AC_remove (acs:AssocList action) : Prop :=
Forall (fun elt =>
        match elt with
        | (id0, AC_remove) => 
            ~ vertex_in_actions_codom acs (index (value_id id0))
        | _ => True
        end) acs.

Lemma find_stld_pairs_blocks__wf_AC_remove: forall s m fh bs 
  (HwfF: wf_fdef s m (fdef_intro fh bs))
  (HuniqF: uniqFdef (fdef_intro fh bs)) pid rd actions
  (Hfind: actions = flat_map (find_stld_pairs_block pid rd) bs)
  (Hreach: ret rd = reachablity_analysis (fdef_intro fh bs)),
  wf_AC_remove actions.
Proof.
  intros.
  assert (NoDup (getBlocksLocs bs)) as Hnodup.
    destruct fh. simpl in HuniqF.
    destruct HuniqF. split_NoDup. auto.
  assert (Hwfacs:=Hfind).
  apply find_stld_pairs_blocks__wf_actions in Hwfacs; auto.
  apply Forall_forall.
  intros [id0 []] Hin; auto.
  intros [id1 [ac1 [Hin' Ha2v]]].
  apply action2id__inv in Ha2v; subst ac1.
  eapply wf_actions__in in Hin; eauto.
  destruct Hin as 
    [acs1 [acs2 [l0 [ps0 [cs0 [tmn0 [EQ [Hin1 [Hin2 Hwf]]]]]]]]]; subst.
  simpl in Hwf.
  destruct Hwf as [v0 [cs01 [c0 [cs02 [dones [J1 [J2 [J3 J4]]]]]]]].
  eapply wf_actions__in in Hin'; eauto.
  destruct Hin' as 
    [acs1' [acs2' [l0' [ps0' [cs0' [tmn0' [EQ' [Hin1' [Hin2' Hwf']]]]]]]]]; 
    subst.
  simpl in Hwf'.
  destruct Hwf' as [id2' [cs01'' [c0' [cs02'' 
                     [dones' [J1' [J2' [J3' [J4' J5']]]]]]]]].
  subst.
  apply find_init_stld_inl_spec in J1.
  destruct J1 as [cs1 [ty [al EQ'']]]; subst.
  apply find_init_stld_inl_spec in J1'.
  destruct J1' as [cs1' [ty' [al' EQ''']]]; subst.
  repeat match goal with
  | H: In ?b ?bs, Hwf: wf_fdef _ _ (fdef_intro ?fh ?bs) |- _ =>
    let HbInF := fresh "HbInF" in
    assert (blockInFdefB b (fdef_intro fh bs)) as HbInF; 
      try solve [simpl; solve_in_list];
    clear H
  end.
  eapply wf_fdef__wf_cmd in HbInF; eauto using in_middle.
  inv HbInF. 
  inv H11.
  assert (In id0 (List.map (fun id_0 : id => id_0) id_list)) as Hin.
    subst. simpl. auto.
  apply_clear H2 in Hin.
  remember ((insn_store id2' ty' (value_id id0) (value_id pid) al')) as st0.
  remember (l0',
            stmts_intro ps0' (cs1' ++ st0 :: cs01'' ++ c0' :: cs02'') tmn0') 
    as b0.
  assert (blockInFdefB b0 (fdef_intro fh bs) = true) as HBinF.
    eapply insnInFdefBlockB__blockInFdefB; eauto.
  assert (J:=inscope_of_cmd__total (fdef_intro fh bs) b0 st0).
  remember (inscope_of_cmd (fdef_intro fh bs) b0 st0) as R.
  destruct R as [ids0|]; try congruence.
  eapply cmd_operands__in_scope in Hin; subst; simpl; eauto.
  Case "1".
    eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HbInF0; 
      eauto using in_middle.
    clear - HbInF0 HuniqF H HBinF HeqR Hin.
    eapply cannot_use_fake_store_id; eauto.
      simpl. auto.
  Case "2".
    solve_NoDup.
  Case "3".
    assert (getCmdLoc c0' `in` dom (flat_map (find_stld_pairs_block pid rd) bs))
      as Hindom.
      rewrite EQ'. 
      simpl_env. 
      fsetdec.
    assert (lookupBlockViaIDFromFdef (fdef_intro fh bs) (getCmdLoc c0') = 
      ret (l0',
           stmts_intro ps0'
             (cs1' ++
              insn_store id2' ty' (value_id id0) (value_id pid) al'
              :: cs01'' ++ c0' :: cs02'') tmn0')) as Hlk.
      apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
        simpl. 
        apply in_or_app. 
        right.
        apply getCmdLoc__in__getCmdsIDs.
          solve_NoDup.
          destruct c0'; tinv J4'. 
            simpl. congruence.
          solve_in_list.
    eapply find_stld_pairs_block__reach'' in Hlk; eauto.     
    eapply reachablity_analysis__reachable; eauto.  
Qed.

(* Lem 59c *)
Lemma find_root__wf_AC_remove_spec: forall acs 
  (Huniq: uniq acs) (Hwf: wf_AC_remove acs) id0
  (Hfind: find_root (value_id id0) acs = None),
  lookupAL _ acs id0 = Some AC_remove.
Proof.
  intros.
  apply find_root__remove_spec in Hfind.
  destruct Hfind as [vl [al [id1 [Hw Hin]]]].
  inv Hw.
  Case "1".
    apply In_lookupAL; auto.
  Case "2".
    eapply Forall_forall in Hin; eauto.
    simpl in Hin.
    contradict Hin.
    destruct y as [[id5|]]; tinv H1.
    exists id5. auto.
Qed.

Lemma find_root__wf_AC_remove_spec': forall acs (Huniq: uniq acs) id0
  (Hlk: lookupAL _ acs id0 = Some AC_remove),
  find_root (value_id id0) acs = None.
Proof.
  intros.
  rewrite unfold_find_root_id.
  apply remove_from_actions_spec9 in Hlk; auto.
  destruct Hlk as [acs1 [acs2 [EQ Hnrm]]]; subst.
  rewrite Hnrm; auto.
Qed.

(* Lem 60 *)
Lemma list_substs_actions__const: forall actions id0 ac0 c0 id1 ac1
  (Hlk: lookupAL _ actions id0 = Some ac0) 
  (Hac: action2value ac0 = Some (value_const c0)),
  lookupAL action (ListComposedPass.subst_actions id1 ac1 actions) id0 = ret ac0.
Proof.
  intros.
  unfold ListComposedPass.subst_actions.
  destruct (action2value ac1); auto.
  induction actions as [|[id2 ac2] acs].
    inv Hlk.
    
    simpl in *.
    destruct_if.
      destruct ac0; inv Hac; auto.
      rewrite IHacs; auto.
Qed.

Definition substs_actions__const_prop (n:nat) := forall actions
  (Hlen: (length actions = n)%nat) id0 ac0 c0 
  (Hlk: lookupAL _ actions id0 = Some ac0) 
  (Hac: action2value ac0 = Some (value_const c0)),
  lookupAL _ (substs_actions actions) id0 = Some ac0.

Lemma substs_actions__const_aux: forall n,
  substs_actions__const_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold substs_actions__const_prop in *; intros.
  destruct actions as [|[id1 ac1] actions].
    inv Hlk.

    unfold_substs_actions.
    simpl in *. 
    destruct_if; auto.
      rewrite H0.
      erewrite Hrec; eauto.
        rewrite <- list_subst_actions__length; auto.
        eapply list_substs_actions__const; eauto.
Qed.

Lemma substs_actions__const: forall actions id0 ac0 c0 
  (Hlk: lookupAL _ actions id0 = Some ac0) 
  (Hac: action2value ac0 = Some (value_const c0)),
  lookupAL _ (substs_actions actions) id0 = Some ac0.
Proof.
  intros.
  assert (J:=@substs_actions__const_aux (length actions)).
  unfold substs_actions__const_prop in J.
  eauto.
Qed.

Lemma substs_actions__none: forall actions id0,
  lookupAL _ actions id0 = None <-> 
    lookupAL _ (substs_actions actions) id0 = None.
Proof.
  intros.
  assert (J:=substs_actions__dom actions).
  split; intro H.
    apply lookupAL_None_notindom in H.
    apply notin_lookupAL_None.
    fsetdec.

    apply lookupAL_None_notindom in H.
    apply notin_lookupAL_None.
    fsetdec.
Qed.

(* Lem 61 *)
Definition substs_actions__actions_len_imply__acyclic_prop (n:nat) := 
  forall actions (Hlen: (length actions = n)%nat) 
  (Huniq: uniq actions) (Hacyc: acyclic_actions actions)
  (Hnt: no_AC_tsubst_actions actions),
  actions_len_imply (substs_actions actions) actions /\
  acyclic_actions (substs_actions actions).

Lemma substs_actions__actions_len_imply__acyclic_aux: forall n,
  substs_actions__actions_len_imply__acyclic_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold substs_actions__actions_len_imply__acyclic_prop in *; intros.
  destruct actions as [|[id1 ac1] actions].
  Case "1".
    unfold_substs_actions.
    split; auto.
      apply actions_len_imply__refl.
  Case "2".
    unfold_substs_actions.
    simpl_env.
    assert (actions_len_imply
      ([(id1, ac1)] ++ ListComposedPass.subst_actions id1 ac1 actions)
      ([(id1, ac1)] ++ actions)) as Himply''.
      assert ([(id1, ac1)] = 
              ListComposedPass.subst_actions id1 ac1 [(id1, ac1)]) as EQ.
        apply list_subst_actions__id.
      rewrite EQ at 1.
      rewrite <- list_subst_actions_app.
      apply list_subst_actions_len_imply_inv; auto.
        simpl. auto. 
    assert (length (ListComposedPass.subst_actions id1 ac1 actions) =
            length (ListComposedPass.subst_actions id1 ac1 actions)) as EQ.
      auto.
    apply Hrec in EQ.
    SCase "2.1".
      destruct EQ as [Himply' Hacyc'].
      assert (actions_len_imply
                ([(id1, ac1)] ++
                 substs_actions (ListComposedPass.subst_actions id1 ac1 actions))
                ([(id1, ac1)] ++ actions)) as Himply.
        apply actions_len_imply__trans with 
          (acs2:=[(id1, ac1)]++(ListComposedPass.subst_actions id1 ac1 actions)); 
          auto.
        apply actions_len_imply_weakening; auto.
      split; auto.
        apply acyclic_actions_weakening with (acs:=nil) in Himply; auto.
    SCase "2.2".
      subst. simpl. rewrite <- list_subst_actions__length; auto.   
    SCase "2.3".
      inv Huniq.
      apply list_subst_actions__uniq; auto.
    SCase "2.4".
      inv Huniq.
      simpl_env in Hacyc.
      eapply acyclic_actions_weakening with (acs:=nil) in Himply''; auto.
      simpl_env in Himply''.
      apply acyclic_actions_strengthening in Himply''; auto.
    SCase "2.5".
      solve_no_AC_tsubst.
Qed.

Lemma substs_actions__actions_len_imply: forall actions
  (Huniq: uniq actions) (Hacyc: acyclic_actions actions)
  (Hnt: no_AC_tsubst_actions actions),
  actions_len_imply (substs_actions actions) actions.
Proof.
  intros.
  assert (J:=@substs_actions__actions_len_imply__acyclic_aux (length actions)).
  unfold substs_actions__actions_len_imply__acyclic_prop in J.
  apply J; auto.
Qed.

Lemma substs_actions__acyclic: forall actions
  (Huniq: uniq actions) (Hacyc: acyclic_actions actions)
  (Hnt: no_AC_tsubst_actions actions),
  acyclic_actions (substs_actions actions).
Proof.
  intros.
  assert (J:=@substs_actions__actions_len_imply__acyclic_aux (length actions)).
  unfold substs_actions__actions_len_imply__acyclic_prop in J.
  apply J; auto.
Qed.

(* Lem 62 *)
Lemma find_root__eq__find_root_substs_actions: forall acs id0
  (Hacyc: acyclic_actions acs) (Huniq: uniq acs) (Hwf: wf_AC_remove acs)
  (Hnt: no_AC_tsubst_actions acs),
  find_root (value_id id0) acs = 
    find_root (value_id id0) (substs_actions acs).
Proof.
  intros.
  assert (vertex_in_actions_dom acs (index (value_id id0)) \/
          ~ vertex_in_actions_dom acs (index (value_id id0))) as Hdec.
    simpl.
    fsetdec.
  destruct Hdec as [Hin | Hnotin].
  Case "1".
    remember (find_root (value_id id0) acs) as R.
    symmetry in HeqR.
    destruct R as [v0|].
    SCase "1.1".
      apply find_root__D_walk_end in HeqR; auto.
      SSCase "1.1.1".
        destruct HeqR as [vl [al [Hw Hend]]].
        assert (actions_walk acs (index v0) (index (value_id id0)) vl al) as Hw'.
          split; auto.
        apply substs_actions_eq in Hw'; auto.
        destruct Hw' as [vl2 [al2 [Hw'' Hend']]]; auto.
        apply actions_walk_end__find_root in Hw''; auto.
          apply substs_actions__acyclic; auto.
          apply substs_actions__uniq; auto.
      SSCase "1.1.2".
        left. auto.
    SCase "1.2".
      apply find_root__wf_AC_remove_spec in HeqR; auto.
      apply substs_actions__AC_remove in HeqR.
      rewrite find_root__wf_AC_remove_spec'; auto using substs_actions__uniq.
  Case "2".
    simpl in Hnotin.
    rewrite find_root__id_notin'; auto.
    rewrite find_root__id_notin'; auto.
      assert (J:=substs_actions__dom acs).
      fsetdec.
Qed.

(* Lem 63 *)
Lemma list_substs_actions__codom_prop: forall actions id0
  (Hndom: id0 `notin` dom actions) id1 ac1 (Hneq: id1 <> id0)
  (Hncodom1: ~ vertex_in_actions_codom [(id1, ac1)] (index (value_id id0)))
  (Hncodom2: ~ vertex_in_actions_codom actions (index (value_id id0))), 
  ~ vertex_in_actions_codom (ListComposedPass.subst_actions id1 ac1 actions)
     (index (value_id id0)).
Proof.
  intros.
  unfold ListComposedPass.subst_actions.
  remember (action2value ac1) as R.
  destruct R as [v4|]; auto.
  induction actions as [|[id2 ac2] acs].
  Case "1".
    simpl. intro J. destruct J as [? [? [J ?]]]. inv J.
  Case "2".
    simpl_env in Hncodom2.
    apply vertex_notin_actions_codom_app in Hncodom2.
    destruct Hncodom2 as [Hncodom21 Hncodom22].
    simpl. intro H.
    destruct H as [id3 [ac3 [[H | H] Ha2v]]].
    SCase "2.1".
      inv H.
      destruct ac2 as [|v2|t2]; inv Ha2v.
      destruct v2 as [id4|]; tinv H0.
      simpl in H0.
      destruct_dec.
        apply Hncodom1.
        exists id1. simpl. 
        destruct ac1; inv HeqR. 
          exists (AC_vsubst (value_id id0)). auto.

        inv H0.
        apply Hncodom21.
        exists id3. exists (AC_vsubst (value_id id0)). split; simpl; auto.
    SCase "2.2".
      simpl in Hndom.
      destruct_notin.
      apply IHacs in Hncodom22; auto.
      apply Hncodom22. 
      exists id3. exists ac3. auto.
Qed.

Definition substs_actions__codom_prop (n:nat) := forall actions
  (Hlen: (length actions = n)%nat) id0
  (Hndom: id0 `notin` dom actions) 
  (Hncodom: ~ vertex_in_actions_codom actions (index (value_id id0))), 
  ~ vertex_in_actions_codom (substs_actions actions) (index (value_id id0)).

Lemma substs_actions__codom_aux: forall n,
  substs_actions__codom_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold substs_actions__codom_prop in *; intros.
  destruct actions as [|[id1 ac1] actions].
  Case "1".
    unfold_substs_actions. 
    intro Hin.
    destruct Hin as [id2 [ac2 [Hin Ha2v]]].
    inv Hin.
  Case "3".
    unfold_substs_actions.
    simpl in Hndom.
    destruct_notin. simpl_env in *.
    apply vertex_notin_actions_codom_app in Hncodom.
    apply vertex_notin_actions_codom_app.
    destruct Hncodom as [Hncdom1 Hncdom2].
    split; auto.
      apply Hrec with (y:=length actions).
        subst. simpl. omega.

        rewrite <- list_subst_actions__length; auto.

        assert (J:=list_subst_actions__dom id1 ac1 actions).
        fsetdec.

        apply list_substs_actions__codom_prop; auto.        
Qed.

Lemma substs_actions__codom: forall actions id0
  (Hndom: id0 `notin` dom actions) 
  (Hncodom: ~ vertex_in_actions_codom actions (index (value_id id0))), 
  ~ vertex_in_actions_codom (substs_actions actions) (index (value_id id0)).
Proof.
  intros.
  assert (J:=@substs_actions__codom_aux (length actions)).
  unfold substs_actions__codom_prop in J.
  eauto.
Qed.

(* Lem 64a *)
Lemma list_subst_actions__notin: forall id1 ac1 actions id0
  (Hntin: id0 `notin` dom actions),
  id0 `notin` dom (ListComposedPass.subst_actions id1 ac1 actions).
Proof.
  intros.
  assert (J:=list_subst_actions__dom id1 ac1 actions).
  fsetdec.
Qed.

(* Lem 64 *)
Fixpoint sorted_actions (acs:AssocList action): Prop :=
match acs with
| nil => True
| (id0, ac0)::acs' => 
    match action2value ac0 with
    | Some _ => ~ vertex_in_actions_codom acs' (index (value_id id0 )) 
    | _ => True
    end /\ sorted_actions acs'
end.

Definition substs_actions__sorted_prop (n:nat) := forall actions
  (Hlen: (length actions = n)%nat) (Hacyc: acyclic_actions actions) 
  (Huniq: uniq actions) (Hnt: no_AC_tsubst_actions actions),
  sorted_actions (substs_actions actions).

Lemma substs_actions__sorted_aux: forall n,
  substs_actions__sorted_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold substs_actions__sorted_prop in *; intros.
  destruct actions as [|[id1 ac1] actions].
  Case "1".
    unfold_substs_actions. simpl. auto.
  Case "2".
    unfold_substs_actions. 
    split.
    SCase "2.1".
      remember (action2value ac1) as R.
      destruct R; auto.
      apply substs_actions__codom.
      SSCase "2.1.1".
        inv Huniq.
        eapply list_subst_actions__notin; eauto.
      SSCase "2.1.2".
        apply notin_codom_of_actions__iff__vertex_notin_actions_codom.
        eapply nonused_in_action__notin_codom_of_actions; eauto 1.
          eapply acyclic_ations_isnt_refl with (acs1:=nil); eauto.
    SCase "2.2".
      apply Hrec with (y:=length actions).
      SSCase "2.2.1".
        subst. simpl. omega.
        rewrite <- list_subst_actions__length; auto.
      SSCase "2.2.2".
        apply list_subst_actions_cons_acyclic in Hacyc; auto.
        simpl_env in Hacyc.
        apply acyclic_actions_strengthening in Hacyc; auto.
      SSCase "2.2.3".
        inv Huniq.
        apply list_subst_actions__uniq; auto.
      SSCase "2.2.4".
        solve_no_AC_tsubst.
Qed.

Lemma substs_actions__sorted: forall actions (Hacyc: acyclic_actions actions) 
  (Huniq: uniq actions) (Hnt: no_AC_tsubst_actions actions), 
  sorted_actions (substs_actions actions).
Proof.
  intros.
  assert (J:=@substs_actions__sorted_aux (length actions)).
  unfold substs_actions__sorted_prop in J.
  eauto.
Qed.

Lemma sorted_actions__strengthening: forall acs1 id2 ac2 acs3
  (Hsrt: sorted_actions (acs1++(id2,ac2)::acs3)),
  sorted_actions (acs1++acs3).
Proof.
  induction acs1 as [|[id0 ac0] acs1]; simpl; intros.
  Case "1".
    destruct Hsrt; auto.
  Case "2".
    destruct Hsrt as [J Hsrt].
    split; eauto.
      destruct (action2value ac0); auto.
      intro H. apply J. 
      destruct H as [id1 [ac1 [Hin Ha2v]]].
      exists id1. exists ac1. split; auto. 
        repeat xsolve_in_list.
Qed.

Lemma sorted_actions__strengthening_head: forall acs1 acs2
  (Hsrt: sorted_actions (acs1++acs2)),
  sorted_actions acs2.
Proof.
  induction acs1 as [|[id0 ac0]]; intros; auto.
    rewrite_env (nil ++ (id0, ac0) :: acs1 ++ acs2) in Hsrt.
    apply sorted_actions__strengthening in Hsrt. auto.
Qed.

(* Lem 65 *)
Lemma pipelined_actions_action__id_in_spec: forall acs1 id2 ac2 acs3
  (Hsome: action2value ac2 <> None) (Huniq: uniq (acs1++(id2,ac2)::acs3))
  (Hnt: no_AC_tsubst_action ac2),
  pipelined_actions_action (acs1++(id2,ac2)::acs3) (AC_vsubst (value_id id2)) =
  pipelined_actions_action acs3 ac2.
Proof.
  induction acs1 as [|[id1 ac1] acs1']; intros; simpl.
  Case "1".
    destruct_dec.
    remember (action2value ac2) as R.
    destruct R.  
    SCase "1.1".
      apply no_AC_tsubst_action__action2value in HeqR; auto.
      subst. auto.
    SCase "1.2".
      congruence.
  Case "2".
    inv Huniq.
    remember (action2value ac1) as R.
    destruct R; eauto.
      destruct_dec.
      simpl_env in H3. fsetdec.
Qed.

Lemma pipelined_actions_action__const_spec: forall ac acs c
  (Hcst: action2value ac = Some (value_const c)),
  pipelined_actions_action acs ac = ac.
Proof.
  intros.
  induction acs as [|[]]; simpl; auto.
    destruct (action2value a); auto.
      destruct ac; inv Hcst; simpl; auto.
Qed.

Lemma pipelined_actions_action__id_notin_spec: forall acs id0
  (Hnotin: lookupAL action acs id0 = None),
  pipelined_actions_action acs (AC_vsubst (value_id id0)) = 
    AC_vsubst (value_id id0).
Proof.
  induction acs as [|[id1 ac1]]; simpl; intros; auto.
    destruct_if.
    destruct_dec.
    destruct (action2value ac1); auto.
Qed.

(* Lem 66 *)
Lemma sorted_actions__lookup_omit_pre: forall acs11 acs12 (id1 id2:id) ac2 acs2
  (Hsrt: sorted_actions (acs11++acs12++(id1,AC_vsubst (value_id id2))::acs2))
  (Hlk: lookupAL _ (acs11++acs12++acs2) id2 = Some ac2) 
  (Hsome: action2value ac2 <> None),
  lookupAL _ (acs12++acs2) id2 = Some ac2.
Proof.
  induction acs11 as [|[id0 ac0] acs11]; simpl; intros; auto.
    destruct Hsrt as [J Hsrt].
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id2 id0); 
      subst; eauto.
      inv Hlk. 
      destruct (action2value ac2); try congruence.
      contradict J.
      exists id1. exists (AC_vsubst (value_id id0)).
      split; auto.
        xsolve_in_list.
Qed.

Definition sorted_actions__find_root_omit_pre_prop (n:nat) := forall acs 
  (Hlen: (length acs = n)%nat) acs11 acs12 (id1 id2:id) acs2
  (Heq: acs = (acs11++acs12++(id1,AC_vsubst (value_id id2))::acs2))
  (Huniq: uniq acs) (Hsrt: sorted_actions acs) v
  (Hsm: find_root (value_id id2) (acs11++acs12++acs2) = Some v),
  find_root (value_id id2) (acs12++acs2) = Some v.

Lemma sorted_actions__find_root_omit_pre_aux: forall n,
  sorted_actions__find_root_omit_pre_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec. 
  unfold sorted_actions__find_root_omit_pre_prop in *; intros.
  subst.
  repeat rewrite unfold_find_root_id in *.
  destruct (AtomSetProperties.In_dec id2 (dom (acs11++acs12++acs2)))
    as [Hin | Hntin].
  Case "1".
    apply remove_from_actions_spec1 in Hin.
    destruct Hin as [acs3 [ac0 [acs4 [Hrm EQ]]]]; subst.
    rewrite Hrm in Hsm.
    remember (action2value ac0) as R.
    destruct R as [v0|]; tinv Hsm. 
    assert (lookupAL _ (acs12++acs2) id2 = Some ac0) as Hsome.
    SCase "1.0".
      eapply sorted_actions__lookup_omit_pre with (acs11:=acs11); eauto 1.
      SSCase "1.0.1".
        rewrite EQ.
        apply In_lookupAL; auto.
          rewrite <- EQ. solve_uniq.
          xsolve_in_list.
      SSCase "1.0.2".
        congruence.
    apply remove_from_actions_spec9 in Hsome; auto.
    SSCase "1.1".
      destruct Hsome as [acs5 [acs6 [EQ1 Hrm']]].
      rewrite Hrm'.
      rewrite <- HeqR.
      destruct v0 as [id0|c0].
      SSSCase "1.1.1".
        rewrite EQ1 in EQ.
        destruct ac0 as [|v0|]; tinv HeqR.
        destruct v0 as [id0'|]; inv HeqR.
        assert (acs11++acs5=acs3 /\ acs6=acs4) as EQ2.
          match goal with
          | H: ?A++?B++?c::?D = _ |- _ =>
            rewrite_env ((A++B)++c::D) in H
          end.
          apply uniq_split_middle in EQ; auto.
            simpl_env. simpl_env in EQ1. unfold id. rewrite <- EQ1.
            solve_uniq.
        destruct EQ2; subst.
        simpl_env in Hsm.
        eapply Hrec with (y:=
            length (acs11++acs5 ++ (id2, AC_vsubst (value_id id0')) :: acs4)
          ) in Hsm; eauto.
        SSSSCase "1.1.1.1".
          unfold id.     
          rewrite <- EQ1.
          repeat rewrite app_length. simpl. 
          repeat apply plus_le_lt_compat; auto.
        SSSSCase "1.1.1.2".
          unfold id.     
          rewrite <- EQ1. 
          solve_uniq.          
        SSSSCase "1.1.1.3".            
          unfold id.     
          rewrite <- EQ1. 
          rewrite_env ((acs11 ++ acs12) ++ (id1, AC_vsubst (value_id id2)) ::
                       acs2) in Hsrt.
          apply sorted_actions__strengthening in Hsrt.
          simpl_env in Hsrt; auto.
      SSSCase "1.1.2".
        rewrite find_root__const_spec.
        rewrite find_root__const_spec in Hsm. auto.
    SSCase "1.2".
      solve_uniq.
  Case "2".
    rewrite remove_from_actions_spec2 in Hsm; auto.    
    rewrite remove_from_actions_spec2; auto.    
Qed.

Lemma sorted_actions__find_root_omit_pre': forall acs 
  acs11 acs12 (id1 id2:id) acs2
  (Heq: acs = (acs11++acs12++(id1,AC_vsubst (value_id id2))::acs2))
  (Huniq: uniq acs) (Hsrt: sorted_actions acs) v
  (Hsm: find_root (value_id id2) (acs11++acs12++acs2) = Some v),
  find_root (value_id id2) (acs12++acs2) = Some v.
Proof.
  intros.
  assert (J:=@sorted_actions__find_root_omit_pre_aux (length acs)).
  unfold sorted_actions__find_root_omit_pre_prop in J.
  eauto.
Qed.

Lemma sorted_actions__find_root_omit_pre: forall acs
  acs1 (id1 id2:id) acs2
  (Heq: acs = (acs1++(id1,AC_vsubst (value_id id2))::acs2))
  (Huniq: uniq acs) (Hsrt: sorted_actions acs) v
  (Hsm: find_root (value_id id2) (acs1++acs2) = Some v),
  find_root (value_id id2) acs2 = Some v.
Proof.
  intros. subst.
  rewrite_env (nil++acs2). 
  rewrite_env (acs1++nil++acs2) in Hsm.
  eapply sorted_actions__find_root_omit_pre' with (acs12:=nil)(id1:=id1)
    in Hsm; eauto.
    simpl_env in *; auto.
Qed.

(* Lem 67 *)
Definition sorted_actions__pipelined_actions_action_eq_find_root_prop (n:nat) :=
  forall acs (Hlen: (length acs = n)%nat) 
  (Huniq: uniq acs) (Hsrt: sorted_actions acs) (Hnt: no_AC_tsubst_actions acs)
  id0 v0 (Hfd: find_root (value_id id0) acs = Some v0),
  action2value (pipelined_actions_action acs (AC_vsubst (value_id id0))) 
    = Some v0.

Lemma sorted_actions__pipelined_actions_action_eq_find_root_aux: forall n,
  sorted_actions__pipelined_actions_action_eq_find_root_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec. 
  unfold sorted_actions__pipelined_actions_action_eq_find_root_prop in *; intros.
  subst. revert Hfd.
  unfold_find_root; intro.
  Case "1".
    apply remove_from_actions_spec3 in HeqR1.
    destruct HeqR1 as [acs1 [acs2 [J1 J2]]]; subst.
    rewrite pipelined_actions_action__id_in_spec; 
      try solve [auto | congruence | solve_no_AC_tsubst].
    destruct v1 as [id1|c1].
    SCase "1.1".
      destruct ac; inv HeqR2.
      apply sorted_actions__find_root_omit_pre with (id1:=id0)
        (acs:=acs1++(id0,AC_vsubst (value_id id1))::acs2) in Hfd; eauto.
      eapply Hrec with (y:=length acs2); eauto 1.
      SSCase "1.1.1.1".
        rewrite app_length. simpl. omega.
      SSCase "1.1.1.2".
        solve_uniq.
      SSCase "1.1.1.3".
        match goal with
        | H: sorted_actions (?A ++ ?b :: ?C) |- _ =>
          rewrite_env ((A++[b])++C) in H;
          apply sorted_actions__strengthening_head in H; auto
        end.
      SSCase "1.1.1.4". 
        solve_no_AC_tsubst.
    SCase "1.2".
      rewrite find_root__const_spec in Hfd. 
      inv Hfd.
      erewrite pipelined_actions_action__const_spec; eauto.
  Case "2". congruence.
  Case "3". 
    inv Hfd.
    symmetry in HeqR1.
    apply remove_from_actions_spec7 in HeqR1.
    rewrite pipelined_actions_action__id_notin_spec; eauto.    
Qed.

Lemma sorted_actions__pipelined_actions_action_eq_find_root: forall 
  acs (Huniq: uniq acs) (Hsrt: sorted_actions acs)
  (Hnt: no_AC_tsubst_actions acs)
  id0 v0 (Hfd: find_root (value_id id0) acs = Some v0),
  action2value (pipelined_actions_action acs (AC_vsubst (value_id id0))) 
    = Some v0.
Proof.
  intros.
  assert (J:=@sorted_actions__pipelined_actions_action_eq_find_root_aux 
                (length acs)).
  unfold sorted_actions__pipelined_actions_action_eq_find_root_prop in J.
  eauto.
Qed.

(* Lem 68 *)
Lemma lookupAL_pipelined_actions__composed_actions__in: forall acs1 id0 ac0 acs2
  (Huniq : uniq (acs1 ++ (id0, ac0) :: acs2)),
  lookupAL _ (pipelined_actions__composed_actions (acs1 ++ (id0, ac0) :: acs2))
    id0 = Some (pipelined_actions_action acs2 ac0).
Proof.
  induction acs1 as [|[id1 ac1]]; simpl; intros.
    destruct_if. congruence.

    inv Huniq.
    destruct_if.
      contradict H3.
      simpl_env. fsetdec.     
Qed.

Lemma lookupAL_pipelined_actions__composed_actions__none: forall acs id0
  (HeqR1 : lookupAL action acs id0 = merror),
  lookupAL action (pipelined_actions__composed_actions acs) id0 = None.
Proof.
  induction acs as [|[id1 ?]]; simpl; intros; auto.
    destruct_if.
    rewrite H0. auto.
Qed.

Lemma sorted_actions__pipelined_actions__composed_actions_eq_find_root:
  forall actions (Huniq: uniq actions)
  (Hsrt: sorted_actions actions) (Hnt: no_AC_tsubst_actions actions) id0 ac0 v0
  (Hlk: lookupAL _ (pipelined_actions__composed_actions actions) id0 = Some ac0)
  (Hfd: find_root (value_id id0) actions = Some v0),
  action2value ac0 = Some v0.
Proof.
  intros.
  revert Hfd.
  unfold_find_root; intro.
  Case "1".
    apply remove_from_actions_spec3 in HeqR1.
    destruct HeqR1 as [acs1 [acs2 [J1 J2]]]; subst.
    rewrite lookupAL_pipelined_actions__composed_actions__in in Hlk; auto.
    inv Hlk.
    destruct v1 as [id1|c1].
    SCase "1.1".
      destruct ac; inv HeqR2.
      eapply sorted_actions__find_root_omit_pre with 
        (acs:=acs1 ++ (id0, AC_vsubst (value_id id1)) :: acs2) in Hfd; eauto.
      apply sorted_actions__pipelined_actions_action_eq_find_root; auto.
      SSCase "1.1.1".
        solve_uniq.
      SSCase "1.1.2".
        match goal with
        | H: sorted_actions (?A ++ ?b :: ?C) |- _ =>
          rewrite_env ((A++[b])++C) in H;
          apply sorted_actions__strengthening_head in H; auto
        end.
      SSCase "1.1.3". solve_no_AC_tsubst.
    SCase "1.2".
      rewrite find_root__const_spec in Hfd. 
      inv Hfd.
      erewrite pipelined_actions_action__const_spec; eauto.
  Case "2". congruence.
  Case "3". 
    inv Hfd.
    symmetry in HeqR1.
    apply remove_from_actions_spec7 in HeqR1.
    rewrite lookupAL_pipelined_actions__composed_actions__none in Hlk; auto.
    congruence.
Qed.

(* Lem 68a *)
Lemma pipelined_actions_action__AC_remove: forall acs,
  pipelined_actions_action acs AC_remove = AC_remove.
Proof.
  induction acs as [|[id2 ac2] acs']; simpl; auto.
    destruct (action2value ac2); auto.
Qed.

Lemma pipelined_actions_action__AC_vconst: forall acs cst5,
  pipelined_actions_action acs (AC_vsubst (value_const cst5)) =
    AC_vsubst (value_const cst5).
Proof.
  induction acs as [|[id2 ac2] acs']; simpl; intros; auto.
    destruct (action2value ac2); auto.
Qed.

Lemma pipelined_actions_action__AC_tsubst: forall acs t,
  pipelined_actions_action acs (AC_tsubst t) = AC_tsubst t.
Proof.
  induction acs as [|[id2 ac2] acs']; simpl; intros; auto.
    destruct (action2value ac2); auto.
Qed.

Lemma pipelined_actions_action__AC_remove_inv: forall acs (Hwf: wf_AC_remove acs)
  acs' (Hinc: incl acs' acs) ac0 id0 (Hin: In (id0, ac0) acs) 
  (Heq: pipelined_actions_action acs' ac0 = AC_remove),
  ac0 = AC_remove.
Proof.
  induction acs' as [|[id2 ac2] acs']; simpl; intros; auto.
    remember (action2value ac2) as R.
    destruct R as [v1|].
    Case "1".
      destruct ac0 as [|[id3|]|]; simpl in Heq; auto.
      SCase "1.1".
        destruct_if.
        SSCase "1.1.1".
          destruct v1 as [id4|].
          SSSCase "1.1.1.1".
            eapply IHacs' with (id0:=id2) in H0; eauto. 
            SSSSCase "1.1.1.1.1".
              congruence.
            SSSSCase "1.1.1.1.2".
              eapply incl_cons_split; eauto.
            SSSSCase "1.1.1.1.3".
              apply Hinc. 
              left. destruct ac2; inv HeqR; auto.
          SSSCase "1.1.1.2".
            rewrite pipelined_actions_action__AC_vconst in H0. congruence.
        SSCase "1.1.2".
          eapply IHacs' in H0; eauto.
            congruence.
            eapply incl_cons_split; eauto.
      SCase "1.2".
        rewrite pipelined_actions_action__AC_vconst in Heq. congruence.
      SCase "1.3".
        rewrite pipelined_actions_action__AC_tsubst in Heq. congruence.
    Case "2".
      eapply IHacs'; eauto.
        eapply incl_cons_split; eauto.
Qed.

Lemma pipelined_actions__composed_actions__AC_remove': forall acs acs'
  (Hwf: wf_AC_remove acs) (Hinc: incl acs' acs) id0,
  lookupAL _ acs' id0 = Some AC_remove <->
    lookupAL _ (pipelined_actions__composed_actions acs') id0 = 
      Some AC_remove.  
Proof.
  induction acs' as [|[id2 ac2] acs']; simpl; intros; try tauto.
    destruct_if.
    Case "1".
      split; intro J.
      SCase "1".
        uniq_result.
        rewrite pipelined_actions_action__AC_remove; auto.
      SCase "2".
        uniq_result.
        apply pipelined_actions_action__AC_remove_inv with (acs:=acs) 
          (id0:=id2) in H0; auto.
        SSCase "2.1".      
          subst.
          rewrite pipelined_actions_action__AC_remove; auto.
        SSCase "2.2". eapply incl_cons_split; eauto.
        SSCase "2.3". apply Hinc. xsolve_in_list.
    Case "2".
      apply IHacs'; auto. 
        eapply incl_cons_split; eauto.
Qed.

Lemma pipelined_actions__composed_actions__AC_remove: forall acs
  (Hwf: wf_AC_remove acs) id0,
  lookupAL _ acs id0 = Some AC_remove <->
    lookupAL _ (pipelined_actions__composed_actions acs) id0 = 
      Some AC_remove.  
Proof.
  intros.
  eapply pipelined_actions__composed_actions__AC_remove'; eauto.
    apply incl_refl.
Qed.

(* Lem 69 *)
Lemma pipelined_actions__composed_actions__substs_actions__eq__find_root:
  forall acs (Huniq: uniq acs) (Hwf: wf_AC_remove acs)
  (Hnt: no_AC_tsubst_actions acs)
  (Hacyc: acyclic_actions acs) id0 ac0 v0
  (Hlk: lookupAL _ (pipelined_actions__composed_actions (substs_actions acs)) 
          id0 = Some ac0)
  (Hfd: find_root (value_id id0) acs = Some v0),
  action2value ac0 = Some v0.
Proof.
  intros.
  rewrite find_root__eq__find_root_substs_actions in Hfd; auto.
  eapply sorted_actions__pipelined_actions__composed_actions_eq_find_root in Hlk;
    eauto.
    apply substs_actions__uniq; auto.
    apply substs_actions__sorted; auto.
    solve_no_AC_tsubst.
Qed.

(* Lem 69a *)
Lemma substs_actions__wf_AC_remove: forall acs (Hwf: wf_AC_remove acs)
  (Huniq: uniq acs) (Hacyc: acyclic_actions acs) (Hnt: no_AC_tsubst_actions acs),
  wf_AC_remove (substs_actions acs).  
Proof.
  intros.
  apply Forall_forall.
  intros [id0 []] Hin; auto.
  intro J.
  destruct J as [id1 [ac1 [Hin' Ha2v]]].
  apply action2id__inv in Ha2v; subst ac1.
  apply substs_actions__actions_len_imply in Hacyc; auto.
  assert (D_walk (avertexes (substs_actions acs))
                 (aarcs (substs_actions acs))
                 (index (value_id id0)) (index (value_id id1)) 
                 [index (value_id id1)]
                 [A_ends (index (value_id id0)) (index (value_id id1))]) as Hw.
    constructor; auto.
      constructor.
        left. simpl. eapply In_InDom; eauto.
      left. simpl. eapply In_InDom; eauto.
      apply In__aarcs; auto.
  apply Hacyc in Hw.
  destruct Hw as [vl2 [al2 [Hw Hlen]]].
  apply In_lookupAL in Hin; auto using substs_actions__uniq.
  apply substs_actions__AC_remove in Hin.
  apply lookupAL_in in Hin.
  inv Hw.
  Case "1".
    contradict Hlen. simpl. omega.
  Case "2".
    clear Hnt.
    eapply Forall_forall in Hin; eauto.
    simpl in Hin.
    destruct y as [[]]; tinv H1.
    eauto.
Qed.

(* Lem 69b *)
Lemma pipelined_actions__composed_actions__substs_actions__AC_remove: forall 
  acs (Huniq: uniq acs) (Hacyc: acyclic_actions acs) (Hwf: wf_AC_remove acs) 
  (Hnt: no_AC_tsubst_actions acs) id0,
  lookupAL _ acs id0 = Some AC_remove <->
    lookupAL _ (pipelined_actions__composed_actions (substs_actions acs)) id0 =
      Some AC_remove.  
Proof.
  intros.
  transitivity (lookupAL _ (substs_actions acs) id0 = Some AC_remove).
    apply substs_actions__AC_remove.
    apply pipelined_actions__composed_actions__AC_remove.
      apply substs_actions__wf_AC_remove; auto.
Qed.

(* Lem 70 *)
(************)
Lemma list_subst_actions__uniq_pre: forall id0 ac0 acs1 acs2
  (Huniq: uniq (acs1++acs2)),
  uniq (acs1++ListComposedPass.subst_actions id0 ac0 acs2).
Proof.
  unfold ListComposedPass.subst_actions.
  intros. 
  destruct (action2value ac0); solve_uniq.
Qed.

Lemma in_list_subst_actions_iff: forall (E : list (atom * action)) (id0 : id)
  (ac0 : action) (id1 : atom) ac1 v1 (Ha2v: action2value ac1 = Some v1)
  (Hin : In (id0, ac0) (ListComposedPass.subst_actions id1 ac1 E)),
  exists ac0' : action, In (id0, ac0') E /\ ac0 = subst_action id1 v1 ac0'.
Proof.
  intros.
  unfold ListComposedPass.subst_actions in Hin.
  rewrite Ha2v in Hin.
  unfold ListMap.map in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [[id3 ac3] [J1 J4]].
  inv J1.
  exists ac3. 
  split; auto.
Qed.

(************)
Lemma list_composed_actions__map_fst: forall actions,
  List.map fst (ListComposedPass.compose_actions actions) = 
    List.map fst actions.
Proof.
  induction actions as [|[id0 ac0] actions]; simpl; auto.
    f_equal.
    rewrite list_subst_actions__map_fst; auto.
Qed.

Lemma list_compose_actions__uniq_pre: forall acs1 acs2 
  (Huniq: uniq (acs1++acs2)), 
  uniq (acs1 ++ ListComposedPass.compose_actions acs2).
Proof.
  intros.
  eapply map_fst__uniq; eauto.
    repeat rewrite List.map_app.
    rewrite list_composed_actions__map_fst; auto.
Qed.

Lemma list_compose_actions__uniq: forall acs (Huniq: uniq acs), 
  uniq (ListComposedPass.compose_actions acs).
Proof.
  intros.
  rewrite_env (nil ++ acs) in Huniq.
  apply list_compose_actions__uniq_pre in Huniq; auto.
Qed.

Lemma list_compose_actions__dom: forall acs,
  dom acs [=] dom (ListComposedPass.compose_actions acs).
Proof.
  intros.
  apply map_fst__dom; auto.
    rewrite list_composed_actions__map_fst; auto.
Qed.

(************)
Definition flattened_actions (acs: AssocList action): Prop :=
Forall (fun elt => 
        let '(id0, ac0 ) := elt in
        ac0 <> AC_remove ->
        ~ vertex_in_actions_codom acs (index (value_id id0))) acs.

Lemma flattened__list_subst_subst_actions_aux: forall id0 ac0 v x acs acs1 acs2
  (Hft: flattened_actions acs) (Hin: In (id0, ac0) acs)
  (Ha2v: action2value ac0 = Some v)
  (Heq: acs = acs1 ++ acs2),
  ListComposedPass.subst_actions id0 ac0
     (ListComposedPass.subst_actions x (AC_vsubst (value_id id0)) acs2) = 
  ListComposedPass.subst_actions x ac0 acs2.
Proof.
  intros.
  unfold ListComposedPass.subst_actions.
  rewrite Ha2v.
  simpl.
  generalize dependent acs1.
  induction acs2 as [|[id1 ac1] acs2]; simpl; intros; subst; auto.
    f_equal.
    Case "1".
      f_equal.
      destruct ac1 as [|[id5|]|]; auto.
      simpl.
      destruct_dec; simpl; destruct_dec.
      eapply Forall_forall in Hft; eauto.
      simpl in Hft.
      assert (ac0 <> AC_remove) as Hneq. 
        destruct ac0; inv Ha2v; congruence.
      apply Hft in Hneq.
      contradict Hneq.
      exists id1. exists (AC_vsubst (value_id id0)).
      split; auto.
        xsolve_in_list.
    Case "2".
      apply IHacs2 with (acs3:=acs1++[(id1,ac1)]); auto.
        simpl_env. auto.
Qed.

Lemma flattened__list_subst_subst_actions: forall id0 ac0 v x acs
  (Hft: flattened_actions acs) (Hin: In (id0, ac0) acs)
  (Ha2v: action2value ac0 = Some v),
  ListComposedPass.subst_actions id0 ac0
     (ListComposedPass.subst_actions x (AC_vsubst (value_id id0)) acs) = 
  ListComposedPass.subst_actions x ac0 acs.
Proof.
  intros.
  eapply flattened__list_subst_subst_actions_aux with (acs1:=nil); eauto.
Qed.

Lemma subst_action__spec1: forall x v ac1
  (Hnrm : subst_action x v ac1 <> AC_remove),
  ac1 <> AC_remove.
Proof.
  intros.
  destruct ac1; simpl in *; congruence.
Qed.

Lemma list_compose_actions__acyclic_flattened: forall acs acs2 
  acs1 (Heq: acs = acs1 ++ acs2) (Huniq: uniq acs) 
  (Hacyc: acyclic_actions acs) (Hnt: no_AC_tsubst_actions acs),
  acyclic_actions (acs1++ListComposedPass.compose_actions acs2) /\
  flattened_actions (ListComposedPass.compose_actions acs2).
Proof.
  induction acs2 as [|[x ac] E]; intros; subst.
  Case "base".
    simpl. 
    split; auto.
      constructor.
  Case "ind".
    assert (no_AC_tsubst_actions (ListComposedPass.compose_actions E)) as Hnt'.
      apply list_compose_actions__no_AC_tsubst.
        solve_no_AC_tsubst.
    apply IHE with (acs2:=acs1++[(x, ac)]) in Hacyc; simpl_env; auto. 
    clear IHE.
    destruct Hacyc as [Hacyc Hft].
    split.
    SCase "1".
      simpl_env in Hacyc. simpl in Hacyc.
      simpl.  
      assert (Hacyc':=Hacyc).
      apply list_subst_acyclic_actions_cons_tail in Hacyc.
      SSCase "1.1".
        simpl.
        destruct ac as [|[id0|]|]; simpl; auto.
        remember (ListMap.find id0 (ListComposedPass.compose_actions E)) as R.
        destruct R as [[]|]; auto.
        SSSCase "1.1.1".
          assert (In (id0, AC_vsubst v) (ListComposedPass.compose_actions E)) 
            as Hin.
            eapply lookupAL_in; eauto.
          assert (aarcs (ListComposedPass.subst_actions x (AC_vsubst (value_id id0))
                          (ListComposedPass.compose_actions E)) 
                        (A_ends (index v) (index (value_id id0)))) as Ha.
          SSSSCase "1.1.1.0".
            eapply list_subst_actions__aarcs; eauto.
            SSSSSCase "1.1.1.0.1".
              simpl.
              remember (used_in_value x v) as R.
              destruct R; auto.
              destruct v; inv HeqR0.
              destruct_dec.
              eapply acyclic_actions_has_no_simple_cycles in Hacyc'; eauto 1.
              tauto.
            SSSSSCase "1.1.1.0.2".
              simpl. exists (AC_vsubst v). auto.
          apply list_subst_acyclic_actions_tail with (id0:=id0)(ac0:=AC_vsubst v) 
            in Hacyc.
          SSSSCase "1.1.1.1".
            simpl_env in Hacyc.
            rewrite list_subst_actions_app in Hacyc.
            assert (ListComposedPass.subst_actions id0 (AC_vsubst v) 
                      [(x, AC_vsubst (value_id id0))] = [(x, AC_vsubst v)]) as EQ1.
              unfold ListComposedPass.subst_actions.
              simpl. destruct_dec.
            assert (ListComposedPass.subst_actions id0 (AC_vsubst v)
                      (ListComposedPass.subst_actions x (AC_vsubst (value_id id0))
                         (ListComposedPass.compose_actions E)) =
                    ListComposedPass.subst_actions x (AC_vsubst v)
                      (ListComposedPass.compose_actions E)) as EQ2.
              apply flattened__list_subst_subst_actions with (v:=v); auto.
            rewrite EQ2 in Hacyc. unfold id, AtomSetImpl.elt in Hacyc, EQ1. 
            rewrite EQ1 in Hacyc.
            apply Hacyc.
          SSSSCase "1.1.1.2".
            constructor.  
              solve_no_AC_tsubst.
              apply list_subst_actions__no_AC_tsubst; auto.
          SSSSCase "1.1.1.3".
            simpl_env.
            apply list_subst_actions__uniq_pre; auto.
            apply list_compose_actions__uniq_pre.
              solve_uniq.
          SSSSCase "1.1.1.4".
            simpl in Ha. destruct Ha as [ac1 [Ha Ha2v]].
            assert (ac1 = AC_vsubst v) as EQ.
              symmetry in Ha2v.
              apply no_AC_tsubst_action__action2value in Ha2v; auto.
              apply no_AC_tsubst_actions__no_AC_tsubst_action in Ha; auto.
              apply list_subst_actions__no_AC_tsubst; auto.
            subst. xsolve_in_list.
        SSSCase "1.1.2".
          assert (In (id0, AC_tsubst t) (ListComposedPass.compose_actions E)) 
            as Hin.
            eapply lookupAL_in; eauto.
          solve_no_AC_tsubst.
      SSCase "1.2". 
        constructor; auto. 
          solve_no_AC_tsubst.
      SSCase "1.3".
        simpl_env.
        apply list_compose_actions__uniq_pre.
          solve_uniq.
    SCase "2".
      simpl.
      apply Forall_forall.
      intros [id0 ac0] Hin.
      intros Hnrm J.
      simpl in J.
      destruct J as [id1 [ac1 [[J | J] Ha2v]]].
      SSCase "2.1".
        inv J. 
        remember (ListComposedPass.find_parent_action ac
                   (ListComposedPass.compose_actions E)) as ac1.
        symmetry in Heqac1.
        apply ListComposedPass.find_parent_action_inv in Heqac1.
        apply action2id__inv in Ha2v; subst ac1.
        destruct Heqac1 as [H2 | H2].
        SSSCase "2.1.1".
          destruct H2 as [EQ H2]; subst.
          destruct H2 as [H2 | H2]; eauto.
          destruct H2 as [id2 [H2 H3]].
          inv H2.
          simpl in Hin.
          destruct Hin as [Hin | Hin].
          SSSSCase "2.1.1.1".
            inv Hin. 
            simpl_env in Hacyc. simpl in Hacyc.
            eapply acyclic_ations_isnt_refl in Hacyc; eauto.
            simpl in Hacyc. destruct_dec.
          SSSSCase "2.1.1.2".
            destruct H3 as [H3 | H3].
            SSSSSCase "2.1.1.2.1".
              assert (J:=list_subst_actions__dom id1 (AC_vsubst (value_id id2))
                       (ListComposedPass.compose_actions E)).
              apply In_InDom in Hin.
              apply lookupAL_None_notindom in H3.
              fsetdec.
            SSSSSCase "2.1.1.2.2".
              unfold ListComposedPass.subst_actions in Hin.
              simpl in Hin.
              unfold ListMap.map in Hin.
              apply in_map_iff in Hin.
              destruct Hin as [[id3 ac3] [J1 J2]].
              inv J1.
              apply In_lookupAL in J2.
                unfold ListMap.find in H3. 
                uniq_result. 
                congruence.

                apply list_compose_actions__uniq.
                solve_uniq.
        SSSCase "2.1.2".
          destruct H2 as [id2 [J1 [J2 J3]]]; subst.
          simpl in Hin.
          destruct Hin as [Hin | Hin].
          SSSSCase "2.1.2.1".
            inv Hin.
            simpl_env in Hacyc. simpl in Hacyc.
            eapply acyclic_actions_has_no_simple_cycles in Hacyc; eauto 1.
            apply lookupAL_in; auto.
          SSSSCase "2.1.2.2".
            assert (exists ac0', 
                    In (id0, ac0') (ListComposedPass.compose_actions E) /\
                    ac0' <> AC_remove) as Hin'.
              eapply in_list_subst_actions_iff with (v1:=value_id id0) in Hin; 
                eauto.
              destruct Hin as [ac0' [Hin EQ]]; subst.
              exists ac0'. 
              split; auto.
                eapply subst_action__spec1; eauto.
            destruct Hin' as [ac0' [Hin' Hnrm']].
            eapply Forall_forall in Hft; eauto.
            simpl in Hft.
            apply Hft; auto. 
            exists id2. exists (AC_vsubst (value_id id0)).
            split; auto.
              apply lookupAL_in; auto.
      SSCase "2.2".
        simpl in Hin.
        destruct Hin as [Hin | Hin].
        SSSCase "2.2.1".
          inv Hin.
          assert (ListComposedPass.find_parent_action ac
                    (ListComposedPass.compose_actions E) = 
                    AC_vsubst (value_id id0)) as EQ.
            remember (ListComposedPass.find_parent_action ac
                        (ListComposedPass.compose_actions E)) as ac'.
            assert (exists v0, action2value ac' = Some v0) as R.
              destruct ac'; simpl; eauto.  
                congruence.
            apply action2id__inv in Ha2v; subst ac1.
            destruct R as [v0 Ha2v].
            eapply in_list_subst_actions_iff in J; eauto. 
            destruct J as [ac0' [Hin EQ]].
            destruct ac0' as [|[]|]; inv EQ.
            destruct_dec.
            destruct (ListComposedPass.find_parent_action ac
                        (ListComposedPass.compose_actions E)); inv Ha2v; auto.
          subst.
          apply ListComposedPass.find_parent_action_inv in EQ.
          destruct EQ as [[EQ H]| EQ]. 
          SSSSCase "2.2.1.1".
            subst.
            destruct H as [H | H].
            SSSSSCase "2.2.1.1.1".
              apply H; eauto.
            SSSSSCase "2.2.1.1.2".
              destruct H as [id4 [EQ _]]; inv EQ.
              simpl_env in Hacyc. simpl in Hacyc.
              apply acyclic_ations_isnt_refl in Hacyc.
              inv Hacyc. 
              destruct_dec.
          SSSSCase "2.2.1.2".
            destruct EQ as [id4 [EQ [Hfd _]]]; subst.
            simpl_env in Hacyc. simpl in Hacyc.
            eapply acyclic_actions_has_no_simple_cycles in Hacyc; eauto.
            apply lookupAL_in; auto.
        SSSCase "2.2.2".
          clear Hnt Hnt'.
          remember (ListComposedPass.find_parent_action ac
                     (ListComposedPass.compose_actions E)) as ac'.
          remember (action2value ac') as R.
          destruct R as [v|].
          SSSSCase "2.2.2.1".
            apply action2id__inv in Ha2v; subst ac1.              
            assert (exists ac1, 
                      In (id0, ac1) (ListComposedPass.compose_actions E) /\
                      ac0 = subst_action x v ac1) as J1.
              eapply in_list_subst_actions_iff in Hin; eauto.
            assert (exists ac2, 
                      In (id1, ac2) (ListComposedPass.compose_actions E) /\
                      AC_vsubst (value_id id0) = subst_action x v ac2) as J2.
              eapply in_list_subst_actions_iff in J; eauto.
            destruct J1 as [ac1 [Hin1 EQ1]]; subst.
            destruct J2 as [ac2 [Hin2 EQ2]].
            destruct ac2 as [|[id2|]|t2]; tinv EQ2.
            simpl in EQ2.
            destruct_dec; inv EQ2.
            SSSSSCase "2.2.2.1.1".
              remember (ListComposedPass.find_parent_action ac
                         (ListComposedPass.compose_actions E)) as ac'.
              destruct ac'; inv HeqR.
              symmetry in Heqac'.
              apply ListComposedPass.find_parent_action_inv in Heqac'.
              destruct Heqac' as [Heqac'|Heqac'].
              SSSSSSCase "2.2.2.1.1.1".
                destruct Heqac' as [EQ [Heqac'|Heqac']]; subst.
                SSSSSSSCase "2.2.2.1.1.1.1".
                  apply Heqac'. eauto.
                SSSSSSSCase "2.2.2.1.1.1.2".
                  destruct Heqac' as [id4 [EQ [Heqac' | Heqac']]]; subst.
                  SSSSSSSSCase "2.2.2.1.1.1.2.1".
                    inv EQ.
                    apply In_InDom in Hin1.
                    apply lookupAL_None_notindom in Heqac'.
                    fsetdec.
                  SSSSSSSSCase "2.2.2.1.1.1.2.2".
                    inv EQ.
                    apply In_lookupAL in Hin1; auto.
                      unfold ListMap.find in Heqac'.
                      rewrite Heqac' in Hin1.
                      inv Hin1.
                      apply Hnrm. auto.
                    
                      apply list_compose_actions__uniq.
                        solve_uniq.
              SSSSSSCase "2.2.2.1.1.2".
                destruct Heqac' as [id4 [EQ [Hfd _]]]; subst.
                eapply Forall_forall in Hin1; eauto.
                simpl in Hin1.
                apply Hin1.
                  eapply subst_action__spec1; eauto.
                  exists id4. exists (AC_vsubst (value_id id0)). 
                  split; auto.
                    apply lookupAL_in; auto.
            SSSSSCase "2.2.2.1.2".
              eapply Forall_forall in Hin1; eauto 1.
              simpl in Hin1.
              apply Hin1; eauto 4.
                eapply subst_action__spec1; eauto.
          SSSSCase "2.2.2.2".
            unfold ListComposedPass.subst_actions in *.
            rewrite <- HeqR in *.
            eapply Forall_forall in Hin; eauto.
            simpl in Hin.
            apply Hin; eauto.
Qed. 

Lemma list_compose_actions__flattened: forall acs 
  (Huniq: uniq acs) (Hacyc: acyclic_actions acs) (Hnt: no_AC_tsubst_actions acs), 
  flattened_actions (ListComposedPass.compose_actions acs).
Proof.
  intros.
  rewrite_env (nil ++ acs) in Hacyc.
  eapply list_compose_actions__acyclic_flattened with (acs:=nil++acs) in Hacyc; 
    eauto.
  tauto.
Qed.

Lemma list_compose_actions__acyclic: forall acs acs2 
  acs1 (Heq: acs = acs1 ++ acs2) (Hnt: no_AC_tsubst_actions (acs1++acs2))
  (Huniq: uniq (acs1++acs2)) (Hacyc: acyclic_actions (acs1++acs2)),
  acyclic_actions (acs1++ListComposedPass.compose_actions acs2).
Proof.
  intros.  
  eapply list_compose_actions__acyclic_flattened in Hacyc; eauto.
  tauto.
Qed.

(* Lem 71 *)
Lemma list_subst_actions_cons_eq: forall acs id0 ac0 
  (Huniq: uniq ([(id0, ac0)] ++ acs))
  (Hacyc: acyclic_actions ([(id0, ac0)] ++ acs))
  (Hnt: no_AC_tsubst_actions ([(id0, ac0)] ++ acs)),
  actions_eq
    ([(id0, ac0)] ++ ListComposedPass.subst_actions id0 ac0 acs)
    ([(id0, ac0)] ++ acs).
Proof.
  intros.
  rewrite <- list_subst_acyclic_actions_is_refl with (acs1:=nil)(acs2:=acs) 
    at 1; auto.
  rewrite <- list_subst_actions_app.
  apply actions_eq_sym.
  apply list_subst_actions_eq; auto.
    xsolve_in_list.
Qed.

Lemma list_compose_actions_eq: forall acs (Huniq: uniq acs) 
  (Hacyc: acyclic_actions acs) (Hnt: no_AC_tsubst_actions acs), 
  actions_eq (ListComposedPass.compose_actions acs) acs.
Proof.
  induction 1 as [|id0 ac0 acs']; simpl; intros.
  Case "1".
    apply actions_eq_refl.
  Case "2".
    assert (uniq ([(id0, ac0)] ++
                  ListComposedPass.compose_actions acs')) as Huniq'.
      apply list_compose_actions__uniq_pre.
        constructor; auto.
    unfold ListMap.add.
    simpl_env.
    apply actions_eq_trans with 
      (acs2:=[(id0, ac0)] ++ ListComposedPass.compose_actions acs').
    SCase "2.1". 
      remember (ListComposedPass.find_parent_action ac0
                 (ListComposedPass.compose_actions acs')) as ac1.
      symmetry in Heqac1.
      apply ListComposedPass.find_parent_action_inv in Heqac1.
      destruct Heqac1 as [Heqac1 | [id1 [Eq [Hfd Hnrm]]]]; subst.
      SSCase "2.1.1".
        destruct Heqac1 as [EQ Heqac1]; subst.
        apply list_subst_actions_cons_eq; auto.
          eapply list_compose_actions__acyclic; eauto.
          simpl_env in Hnt. solve_no_AC_tsubst.
      SSCase "2.1.2". 
        assert (no_AC_tsubst_actions
                  ([(id0, AC_vsubst (value_id id1))] ++
                  ListComposedPass.compose_actions acs')) as Hnt'.
          apply list_compose_actions__no_AC_tsubst_pre; auto.
        apply actions_eq_trans with 
          (acs2:=ListComposedPass.subst_actions id0 (AC_vsubst (value_id id1))
                   ([(id0, AC_vsubst (value_id id1))] ++ 
                    ListComposedPass.compose_actions acs')).
        SSSCase "2.1.2.1". 
          rewrite list_subst_actions_app.
          erewrite list_subst_acyclic_actions_is_refl with
            (acs1:=nil)(acs2:=acs'); eauto.
          apply actions_eq_trans with 
            (acs2:=ListComposedPass.subst_actions id1 ac1
                     ([(id0, AC_vsubst (value_id id1))] ++ 
                      ListComposedPass.subst_actions id0 (AC_vsubst (value_id id1))
                      (ListComposedPass.compose_actions acs'))).
          SSSSCase "2.1.2.1.1".
            rewrite list_subst_actions_app.           
            assert (ListComposedPass.subst_actions id1 ac1 
                      [(id0, AC_vsubst (value_id id1))] = [(id0, ac1)]) as EQ1.
            SSSSSCase "2.1.2.1.1.0".              
              unfold ListComposedPass.subst_actions.
              remember (action2value ac1) as R.
              destruct R.
              SSSSSSCase "2.1.2.1.1.0.1".  
                simpl. destruct_dec.
                assert (no_AC_tsubst_actions 
                         (ListComposedPass.compose_actions acs')) as Hnt''.
                  solve_no_AC_tsubst.
                apply no_AC_tsubst_action__action2value in HeqR; subst; auto.                
                  apply lookupAL_in in Hfd.
                  solve_no_AC_tsubst.
              SSSSSSCase "2.1.2.1.1.0.2".  
                destruct ac1; inv HeqR. 
                  congruence.
            rewrite EQ1. clear EQ1.
            assert (ListComposedPass.subst_actions id1 ac1
                      (ListComposedPass.subst_actions id0 (AC_vsubst (value_id id1))
                         (ListComposedPass.compose_actions acs')) =
                    ListComposedPass.subst_actions id0 ac1
                      (ListComposedPass.compose_actions acs')) as EQ2.
              remember (action2value ac1) as R.
              destruct R as [v1|].
              SSSSSCase "2.1.2.1.1.1".
                apply flattened__list_subst_subst_actions with (v:=v1); auto.
                SSSSSSCase "2.1.2.1.1.1.1".
                  apply list_compose_actions__flattened; auto.
                  SSSSSSSCase "2.1.2.1.1.1.1.1".
                    simpl_env in Hacyc.
                    apply acyclic_actions_strengthening in Hacyc; auto. 
                  SSSSSSSCase "2.1.2.1.1.1.1.2".
                    solve_no_AC_tsubst.
                SSSSSSCase "2.1.2.1.1.1.2".
                  apply lookupAL_in; auto.
              SSSSSCase "2.1.2.1.1.2".
                destruct ac1; inv HeqR. 
                  congruence.
            rewrite EQ2. clear EQ2.
            apply actions_eq_refl.
          SSSSCase "2.1.2.1.2". 
            apply actions_eq_sym.
            apply list_subst_actions_eq.
            SSSSSCase "2.1.2.1.2.1".
              apply list_subst_actions__uniq_pre; auto.
            SSSSSCase "2.1.2.1.2.2".
              apply list_subst_actions__no_AC_tsubst_pre; auto.
            SSSSSCase "2.1.2.1.2.3".
              simpl.
              apply list_subst_actions_cons_acyclic; simpl_env; auto.
                eapply list_compose_actions__acyclic; eauto.                
            SSSSSCase "2.1.2.1.2.4".                        
              apply lookupAL_in in Hfd.
              simpl. right.
              unfold ListComposedPass.subst_actions.
              simpl.
              assert (ac1 = subst_action id0 (value_id id1) ac1) as EQ.
                destruct ac1 as [|[id4|]|]; auto.
                simpl.
                destruct_dec.
                simpl_env in Hacyc.
                eapply list_compose_actions__acyclic in Hacyc; eauto.
                eapply acyclic_actions_has_no_simple_cycles with (acs1:=nil) 
                  in Hfd; eauto.
                tauto.
              rewrite EQ.
              apply in_map_iff. 
              exists (id1, ac1).
              split; auto.
        SSSCase "2.1.2.2".
          apply actions_eq_sym.
          apply list_subst_actions_eq; auto.
          SSSSCase "2.1.2.1.1".
            eapply list_compose_actions__acyclic; eauto.
          SSSSCase "2.1.2.1.2".
            simpl. auto.
    SCase "2.2". 
      apply actions_eq_weakening; auto.
      SSCase "2.2.1".
        simpl_env in Hacyc.
        apply acyclic_actions_strengthening in Hacyc.
        inv Hnt.
        apply IHHuniq; auto.
      SSCase "2.2.2".
        rewrite <- list_compose_actions__dom.
        fsetdec.
      SSCase "2.2.3". simpl_env in Hnt. solve_no_AC_tsubst.
Qed.

(* Lem 71a *)
Lemma list_compose_actions__AC_remove: forall acs id0,
  lookupAL _ acs id0 = Some AC_remove <->
    lookupAL _ (ListComposedPass.compose_actions acs) id0 = Some AC_remove.  
Proof.
  intros.
  induction acs as [|[id1 ac1] acs]; simpl; intros; try tauto.
    destruct_if.
    Case "1".
      split; intro H.
      SCase "1.1".
        uniq_result.
        simpl. auto.
      SCase "1.2".
        uniq_result.
        apply ListComposedPass.find_parent_action_inv in H1.
        destruct H1 as [[EQ H1] | [id2 [EQ [Hfd Hneq]]]]; 
          subst; simpl; congruence.
    Case "2".
      assert (J:=list_subst_actions__AC_remove 
                   (ListComposedPass.compose_actions acs) id1
                   (ListComposedPass.find_parent_action ac1
                     (ListComposedPass.compose_actions acs)) id0).
      tauto.
Qed.

(* Lem 72 *)
Lemma list_composed_actions__single_path: forall (acs : list (atom * action))
  (Huniq : uniq acs) (Hacyc : acyclic_actions acs) (id0 : atom) (ac0 : action)
  (v0 : value) (Hnt: no_AC_tsubst_actions acs)
  (Hlk : lookupAL action (ListComposedPass.compose_actions acs) id0 = ret ac0)
  (Hend : end_of_actions (index v0) acs)
  (vl2 : V_list) (al2 : A_list)
  (Hw'' : D_walk (avertexes (ListComposedPass.compose_actions acs))
            (aarcs (ListComposedPass.compose_actions acs)) 
            (index v0) (index (value_id id0)) vl2 al2),
  action2value ac0 = ret v0.
Proof.
  intros.
  inv Hw''.
  Case "1".
    simpl in Hend.
    assert (J:=list_compose_actions__dom acs).
    apply lookupAL_None_notindom in Hend.
    apply lookupAL_Some_indom in Hlk. 
    fsetdec.
  Case "2".  
    inv H.
    SCase "2.1".
      simpl in H1.
      destruct H1 as [ac1 [H1 Ha2v]].
      apply In_lookupAL in H1; auto.
        uniq_result. auto.
        apply list_compose_actions__uniq; auto.
    SCase "2.2".  
      destruct y as [[]]; tinv H1.
      destruct y0 as [[]]; tinv H4.
      simpl in H1, H4.
      destruct H1 as [ac1 [H1 Ha2v1]].
      destruct H4 as [ac4 [H4 Ha2v4]].
      apply list_compose_actions__flattened in Hacyc; auto.
      eapply Forall_forall in H1; eauto.
      simpl in H1.
      elimtype False.
      apply H1; eauto.
        intro J. subst ac1. inv Ha2v1.
Qed.

Lemma list_compose_actions__eq__find_root:
  forall acs (Huniq: uniq acs) (Hnt: no_AC_tsubst_actions acs)
  (Hacyc: acyclic_actions acs) id0 ac0 v0
  (Hlk: lookupAL _ (ListComposedPass.compose_actions acs) id0 = Some ac0)
  (Hfd: find_root (value_id id0) acs = Some v0),
  action2value ac0 = Some v0.
Proof.
  intros.
  assert (vertex_in_actions_dom acs (index (value_id id0)) \/
          ~ vertex_in_actions_dom acs (index (value_id id0))) as Hdec.
    simpl.
    fsetdec.
  destruct Hdec as [Hin | Hnotin].
  Case "1".
    apply find_root__D_walk_end in Hfd; auto.
    SCase "1.1".
      destruct Hfd as [vl [al [Hw Hend]]].
      assert (actions_walk acs (index v0) (index (value_id id0)) vl al) as Hw'.
        split; auto.
      apply list_compose_actions_eq in Hw'; auto.
      destruct Hw' as [vl2 [al2 [[Hw'' Hdom'] Hend']]]; auto.
      eapply list_composed_actions__single_path; eauto.
    SCase "1.2".
      left. auto.
  Case "2".
    apply lookupAL_Some_indom in Hlk.
    simpl in Hnotin.
    assert (J:=list_compose_actions__dom acs).
    fsetdec.
Qed.

(* Lem 73 *)
Lemma list_compose_actions__eq__pipelined_actions__composed_actions__Some':
  forall acs (Huniq: uniq acs) (Hwf: wf_AC_remove acs) 
  (Hnt: no_AC_tsubst_actions acs) (Hacyc: acyclic_actions acs) id0 ac1 ac2
  (Hlk1: lookupAL _ (ListComposedPass.compose_actions acs) id0 = Some ac1)
  (Hlk2: lookupAL _ (pipelined_actions__composed_actions (substs_actions acs)) 
           id0 = Some ac2),
  ac1 = ac2.
Proof.
  intros.
  assert (no_AC_tsubst_action ac1) as Hnt1.
    apply lookupAL_in in Hlk1.
    apply list_compose_actions__no_AC_tsubst in Hnt.
    solve_no_AC_tsubst.
  assert (no_AC_tsubst_action ac2) as Hnt2.
    apply lookupAL_in in Hlk2.
    apply substs_actions__no_AC_tsubst in Hnt.
    apply pipelined_actions__composed_actions__no_AC_tsubst in Hnt.
    solve_no_AC_tsubst.
  remember (find_root (value_id id0) acs) as R.
  destruct R as [v0|].
  Case "1".
    eapply list_compose_actions__eq__find_root in Hlk1; eauto.
    eapply pipelined_actions__composed_actions__substs_actions__eq__find_root
      in Hlk2; eauto.
    rewrite <- Hlk1 in Hlk2.
    eapply no_AC_tsubst_action__action2value in Hnt1; eauto.
    rewrite <- Hlk2 in Hlk1.
    eapply no_AC_tsubst_action__action2value in Hnt2; eauto.
    congruence.
  Case "2".
    symmetry in HeqR.
    apply find_root__wf_AC_remove_spec in HeqR; auto.
    assert (J:=HeqR).
    apply list_compose_actions__AC_remove in HeqR.
    apply pipelined_actions__composed_actions__substs_actions__AC_remove in J; 
      auto.
    congruence.
Qed.

Lemma pipelined_actions__composed_actions__dom: forall acs, 
  dom (pipelined_actions__composed_actions acs) [=] dom acs.
Proof.
  induction acs as [|[]]; simpl; fsetdec.
Qed.

Lemma list_compose_actions__eq__pipelined_actions__composed_actions__None:
  forall acs id0,
  lookupAL _ (ListComposedPass.compose_actions acs) id0 = None <->
    lookupAL _ (pipelined_actions__composed_actions (substs_actions acs)) 
      id0 = None.
Proof.
  intros.
  assert (J1:=list_compose_actions__dom acs).
  assert (J2:=substs_actions__dom acs).
  assert (J3:=pipelined_actions__composed_actions__dom (substs_actions acs)).
  split; intro J;
    apply lookupAL_None_notindom in J;
    apply notin_lookupAL_None;
    fsetdec.
Qed.

Lemma list_compose_actions__eq__pipelined_actions__composed_actions__Some:
  forall acs (Huniq: uniq acs) (Hwf: wf_AC_remove acs)
  (Hnt: no_AC_tsubst_actions acs) (Hacyc: acyclic_actions acs) id0 ac0,
  lookupAL _ (ListComposedPass.compose_actions acs) id0 = Some ac0 <->
    lookupAL _ (pipelined_actions__composed_actions (substs_actions acs)) 
      id0 = Some ac0.
Proof.
  intros.
  split; intro H.
    remember (lookupAL action (pipelined_actions__composed_actions 
               (substs_actions acs)) id0) as R.
    symmetry in HeqR.
    destruct R as [ac1|].
      f_equal.
      eapply list_compose_actions__eq__pipelined_actions__composed_actions__Some' 
        in H; eauto.

      apply list_compose_actions__eq__pipelined_actions__composed_actions__None 
        in HeqR. 
      uniq_result.

    remember (lookupAL action (ListComposedPass.compose_actions acs) id0) as R.
    symmetry in HeqR.
    destruct R as [ac1|].
      f_equal.
      eapply list_compose_actions__eq__pipelined_actions__composed_actions__Some' 
        in H; eauto.

      apply list_compose_actions__eq__pipelined_actions__composed_actions__None 
        in HeqR. 
      uniq_result.
Qed.

(***************************************************************)
Section eq_actions__eq_list_substs.
Variable (acs1 acs2:AssocList action).
Hypothesis Heq: forall id0 ac0, lookupAL _ acs1 id0 = Some ac0 <->
                                lookupAL _ acs2 id0 = Some ac0.

Lemma eq_actions__eq_list_substs_value: forall v,
  ListComposedPass.substs_value acs1 v = ListComposedPass.substs_value acs2 v.
Proof.
  induction v as [id5|]; simpl; auto.
    remember (ListMap.find id5 acs1) as R1.
    symmetry in HeqR1.
    destruct R1 as [ac1|].
      apply Heq in HeqR1. 
      unfold ListMap.find.
      rewrite HeqR1; auto.

      remember (ListMap.find id5 acs2) as R2.
      symmetry in HeqR2.
      destruct R2 as [ac2|]; auto.
        apply Heq in HeqR2. 
        unfold ListMap.find in HeqR1.
        congruence.
Qed.

Lemma eq_actions__eq_list_substs_list_value_l: forall l0,
  ListComposedPass.substs_list_value_l acs1 l0 =
   ListComposedPass.substs_list_value_l acs2 l0.
Proof.
  induction l0 as [|[v l0] l0']; simpl; auto.
    f_equal; auto.
    f_equal. 
      apply eq_actions__eq_list_substs_value.
Qed.

Lemma eq_actions__eq_list_substs_phi: forall p,
  ListComposedPass.substs_phi acs1 p = ListComposedPass.substs_phi acs2 p.
Proof.
  destruct p.
  simpl.
  intros.
  f_equal.
    apply eq_actions__eq_list_substs_list_value_l.
Qed.

Lemma eq_actions__eq_list_substs_list_value: forall l0,
  ListComposedPass.substs_list_value acs1 l0 =
   ListComposedPass.substs_list_value acs2 l0.
Proof.
  induction l0 as [|[v l0] l0']; simpl; auto.
    f_equal; auto.
    f_equal. 
      apply eq_actions__eq_list_substs_value.
Qed.

Lemma eq_actions__eq_list_substs_cmd: forall c,
  ListComposedPass.substs_cmd acs1 c = ListComposedPass.substs_cmd acs2 c.
Proof.
  destruct c; simpl; f_equal; try solve [
    apply eq_actions__eq_list_substs_value |
    apply eq_actions__eq_list_substs_list_value
  ].
    induction params5 as [|[] ps]; simpl; auto.
      f_equal; auto.
        f_equal.
          apply eq_actions__eq_list_substs_value.
Qed.

Lemma eq_actions__eq_list_substs_tmn: forall tmn,
  ListComposedPass.substs_tmn acs1 tmn = ListComposedPass.substs_tmn acs2 tmn.
Proof.
  destruct tmn; simpl; f_equal;
    apply eq_actions__eq_list_substs_value.
Qed.

Lemma eq_actions__eq_list_substs_block: forall b,
  ListComposedPass.substs_block acs1 b = ListComposedPass.substs_block acs2 b.
Proof.
  destruct b as [l0 [ps0 cs0 tmn0]].
  simpl.
  intros.
  f_equal.
  f_equal.
    induction ps0 as [|p0 ps0]; auto.
      simpl. 
      rewrite IHps0.
      f_equal.
      eapply eq_actions__eq_list_substs_phi; eauto.

    induction cs0 as [|c0 cs0]; auto.
      simpl. 
      rewrite IHcs0.
      f_equal.
      eapply eq_actions__eq_list_substs_cmd; eauto.

    eapply eq_actions__eq_list_substs_tmn; eauto.
Qed.

Lemma eq_actions__eq_list_substs_fdef: forall f,
  ListComposedPass.substs_fdef acs1 f = ListComposedPass.substs_fdef acs2 f.
Proof.
  destruct f as [fh bs].
  simpl.
  intros.
  f_equal.
  induction bs as [|b bs]; auto.
    simpl. 
    rewrite IHbs.
    f_equal.
    eapply eq_actions__eq_list_substs_block; eauto.
Qed.
End eq_actions__eq_list_substs.

(*******************************************************************************)
Definition sim_action (ac1 ac2: action) : Prop :=
action2value ac1 = action2value ac2.

Definition sim_actions (acs1 acs2: AssocList action) : Prop :=
Forall2 (fun elt1 elt2 =>
         let '(id1, ac1) := elt1 in
         let '(id2, ac2) := elt2 in
         id1 = id2 /\ sim_action ac1 ac2) acs1 acs2.

Lemma sim_actions__lookupAL_Some1: forall acs1 acs2
  (Hsim: sim_actions acs1 acs2) id5 ac1
  (Hlk: lookupAL _  acs1 id5 = ret ac1),
  exists ac2, lookupAL _  acs2 id5 = ret ac2 /\ sim_action ac1 ac2.
Proof.
  induction 1 as [|[id1 ac1] [id2 ac2] asc1 acs2 [EQ1 J]]; simpl; intros; subst.
    inv Hlk.
    destruct_if; eauto.
Qed.

Lemma sim_action__sym: forall ac1 ac2 (Hsim: sim_action ac1 ac2), 
  sim_action ac2 ac1.
Proof.
  unfold sim_action. auto.
Qed.

Lemma sim_actions__sym: forall acs1 acs2 (Hsim: sim_actions acs1 acs2), 
  sim_actions acs2 acs1.
Proof.
  induction 1 as [|[id1 ac1] [id2 ac2] asc1 acs2 [EQ1 J]]; simpl.
    constructor.
    constructor; auto.
      split; auto using sim_action__sym.
Qed.

Lemma sim_actions__lookupAL_Some2: forall acs1 acs2
  (Hsim: sim_actions acs1 acs2) id5 ac2
  (Hlk: lookupAL _  acs2 id5 = ret ac2),
  exists ac1, lookupAL _  acs1 id5 = ret ac1 /\ sim_action ac1 ac2.
Proof.
  intros.
  apply sim_actions__sym in Hsim.
  eapply sim_actions__lookupAL_Some1 in Hlk; eauto.
  destruct Hlk as [ac3 [Hlk Hsim']].
  exists ac3. 
  split; auto using sim_action__sym.
Qed.

Lemma sim_actions__lookupAL_None1: forall acs1 acs2
  (Hsim: sim_actions acs1 acs2) id5
  (Hlk: lookupAL _  acs1 id5 = None),
  lookupAL _  acs2 id5 = None.
Proof.
  intros.
  remember (lookupAL _  acs2 id5) as R.
  destruct R; auto.
  symmetry in HeqR.
  eapply sim_actions__lookupAL_Some2 in HeqR; eauto.
  destruct HeqR as [ac1 [Hlk' Hsim']].
  uniq_result.
Qed.

Section sim_actions__eq_list_substs.
Variable (acs1 acs2:AssocList action).
Hypothesis (Hsim: sim_actions acs1 acs2).

Lemma sim_actions__eq_list_substs_value: forall v,
  ListComposedPass.substs_value acs1 v = ListComposedPass.substs_value acs2 v.
Proof.
  induction v as [id5|]; simpl; auto.
    remember (ListMap.find id5 acs1) as R1.
    symmetry in HeqR1.
    unfold ListMap.find.
    destruct R1 as [ac1|].
      eapply sim_actions__lookupAL_Some1 in HeqR1; eauto.
      destruct HeqR1 as [ac2 [Hlk Hsim']].
      rewrite Hlk.
      rewrite Hsim'. auto.

      eapply sim_actions__lookupAL_None1 in HeqR1; eauto.
      rewrite HeqR1; auto.
Qed.

Lemma sim_actions__eq_list_substs_list_value_l: forall l0,
  ListComposedPass.substs_list_value_l acs1 l0 =
   ListComposedPass.substs_list_value_l acs2 l0.
Proof.
  induction l0 as [|[v l0] l0']; simpl; auto.
    f_equal; auto.
    f_equal. 
      apply sim_actions__eq_list_substs_value.
Qed.

Lemma sim_actions__eq_list_substs_phi: forall p,
  ListComposedPass.substs_phi acs1 p = ListComposedPass.substs_phi acs2 p.
Proof.
  destruct p.
  simpl.
  intros.
  f_equal.
    apply sim_actions__eq_list_substs_list_value_l.
Qed.

Lemma sim_actions__eq_list_substs_list_value: forall l0,
  ListComposedPass.substs_list_value acs1 l0 =
   ListComposedPass.substs_list_value acs2 l0.
Proof.
  induction l0 as [|[v l0] l0']; simpl; auto.
    f_equal; auto.
    f_equal. 
      apply sim_actions__eq_list_substs_value.
Qed.

Lemma sim_actions__eq_list_substs_cmd: forall c,
  ListComposedPass.substs_cmd acs1 c = ListComposedPass.substs_cmd acs2 c.
Proof.
  destruct c; simpl; f_equal; try solve [
    apply sim_actions__eq_list_substs_value |
    apply sim_actions__eq_list_substs_list_value
  ].
    induction params5 as [|[] ps]; simpl; auto.
      f_equal; auto.
        f_equal.
          apply sim_actions__eq_list_substs_value.
Qed.

Lemma sim_actions__eq_list_substs_tmn: forall tmn,
  ListComposedPass.substs_tmn acs1 tmn = ListComposedPass.substs_tmn acs2 tmn.
Proof.
  destruct tmn; simpl; f_equal;
    apply sim_actions__eq_list_substs_value.
Qed.

Lemma sim_actions__eq_list_substs_block: forall b,
  ListComposedPass.substs_block acs1 b = ListComposedPass.substs_block acs2 b.
Proof.
  destruct b as [l0 [ps0 cs0 tmn0]].
  simpl.
  intros.
  f_equal.
  f_equal.
    induction ps0 as [|p0 ps0]; auto.
      simpl. 
      rewrite IHps0.
      f_equal.
      eapply sim_actions__eq_list_substs_phi; eauto.

    induction cs0 as [|c0 cs0]; auto.
      simpl. 
      rewrite IHcs0.
      f_equal.
      eapply sim_actions__eq_list_substs_cmd; eauto.

    eapply sim_actions__eq_list_substs_tmn; eauto.
Qed.

Lemma sim_actions__eq_list_substs_fdef: forall f,
  ListComposedPass.substs_fdef acs1 f = ListComposedPass.substs_fdef acs2 f.
Proof.
  destruct f as [fh bs].
  simpl.
  intros.
  f_equal.
  induction bs as [|b bs]; auto.
    simpl. 
    rewrite IHbs.
    f_equal.
    eapply sim_actions__eq_list_substs_block; eauto.
Qed.
End sim_actions__eq_list_substs.

Lemma list_subst_actions__sim: forall
  acs1 acs2 (Hsim: sim_actions acs1 acs2) id0 ac1 ac2
  (Hsim': sim_action ac1 ac2),
  sim_actions (ListComposedPass.subst_actions id0 ac1 acs1)
              (ListComposedPass.subst_actions id0 ac2 acs2).
Proof.
  intros.
  unfold ListComposedPass.subst_actions.
  rewrite Hsim'.
  destruct (action2value ac2); auto.
  induction Hsim as [|[? a0] [? a2] ? ? []]; simpl; subst.
    constructor.
    constructor; auto.
      split; auto.
        unfold sim_action.     
         destruct a0; destruct a2; inv H0; auto.
Qed.

Lemma find_parent_action__sim: forall a0 a2 l0 l2 (H0 : sim_action a0 a2)
  (Hsim : sim_actions l0 l2),
  sim_action
    (ListComposedPass.find_parent_action a0 l0) 
    (ListComposedPass.find_parent_action a2 l2).
Proof.
  intros.
  unfold sim_action.
  destruct a0 as [|[]|]; destruct a2 as [|[]|]; inv H0; simpl; auto.
    remember (ListMap.find id0 l0) as R.
    symmetry in HeqR.
    destruct R as [a|].
      eapply sim_actions__lookupAL_Some1 in HeqR; eauto.
      destruct HeqR as [ac2 [Hlk Hsim'']].
      unfold ListMap.find.        
      rewrite Hlk.   
      destruct a; destruct ac2; inv Hsim''; simpl; auto.
  
      eapply sim_actions__lookupAL_None1 in HeqR; eauto.
      unfold ListMap.find.        
      rewrite HeqR. auto.
Qed.

Lemma list_compose_actions__sim: forall acs1 acs2 (Hsim: sim_actions acs1 acs2),
  sim_actions (ListComposedPass.compose_actions acs1)
              (ListComposedPass.compose_actions acs2).
Proof.
  induction 1 as [|[? a0] [? a2] l0 l2 []]; simpl; subst.
    constructor.

    assert (sim_action
             (ListComposedPass.find_parent_action a0
               (ListComposedPass.compose_actions l0))
             (ListComposedPass.find_parent_action a2
               (ListComposedPass.compose_actions l2))) as H.
      apply find_parent_action__sim; auto.
    constructor.
      split; auto.
      apply list_subst_actions__sim; auto.      
Qed.

Lemma subst_action__sim: forall a0 a1 a2 v (Hsim : sim_action a1 a2),
  sim_action (subst_action a0 v a1) (subst_action a0 v a2).
Proof.
  intros.  
  unfold sim_action.
  destruct a1; destruct a2; inv Hsim; auto.
Qed.

Lemma pipelined_actions_action__sim: forall l0 l' 
  (Hsims: sim_actions l0 l') a0 a2 (Hsim: sim_action a0 a2),
  sim_action (pipelined_actions_action l0 a0) (pipelined_actions_action l' a2).
Proof.
  induction 1 as [|[? a0'] [? a2'] ? ? []]; simpl; subst; intros; auto.
    rewrite H0.
    destruct (action2value a2'); auto.
      apply IHHsims. 
      apply subst_action__sim; auto.
Qed.

Lemma pipelined_actions__composed_actions__sim: forall 
  acs1 acs2 (Hsim: sim_actions acs1 acs2),
  sim_actions (pipelined_actions__composed_actions acs1)
              (pipelined_actions__composed_actions acs2).
Proof.
  intros.
  induction Hsim as [|[? a0] [? a2] ? ? []]; simpl; subst.
    constructor.
    constructor; auto.
      split; auto.
        apply pipelined_actions_action__sim; auto.
Qed.

Definition substs_actions__sim_prop (n:nat) := 
  forall acs1 (Hlen: (length acs1 = n)%nat) acs2 (Hsim: sim_actions acs1 acs2),
  sim_actions (substs_actions acs1)
              (substs_actions acs2).

Lemma substs_actions__sim_aux: forall n,
  substs_actions__sim_prop n.
Proof.
  intro n.
  elim n using (well_founded_induction lt_wf).
  intros x Hrec.
  unfold substs_actions__sim_prop in *; intros.
  destruct acs1 as [|[id1 ac1] acs1]; inv Hsim.
  Case "1".
    unfold_substs_actions.
    constructor.
  Case "2".
    unfold_substs_actions.
    destruct y as [id2 ac2].
    assert (substs_actions ((id2, ac2) :: l') = 
            (id2, ac2) :: 
            substs_actions (ListComposedPass.subst_actions id2 ac2 l')) as EQ.
      unfold_substs_actions. auto.
    rewrite EQ.
    constructor; auto.
      eapply Hrec; eauto.
        simpl. rewrite <- list_subst_actions__length; auto. omega.
        destruct H1; subst. eapply list_subst_actions__sim; eauto.   
Qed.

Lemma substs_actions__sim: forall 
  acs1 acs2 (Hsim: sim_actions acs1 acs2),
  sim_actions (substs_actions acs1)
              (substs_actions acs2).
Proof.
  intros.
  assert (J:=@substs_actions__sim_aux (length acs1)).
  unfold substs_actions__sim_prop in J.
  apply J; auto.
Qed.

(*******************************************************************************)
Definition erase_action (ac:action) : action :=
match ac with
| AC_tsubst t => AC_vsubst (value_const (const_undef t))
| _ => ac
end.

Definition erase_actions (acs:AssocList action) : AssocList action :=
ListMap.map erase_action acs.

Lemma erase_action__sim: forall ac, sim_action ac (erase_action ac).
Proof.
  unfold sim_action.
  destruct ac; simpl; auto.
Qed.

Lemma erase_actions__sim: forall acs, sim_actions acs (erase_actions acs).
Proof.
  induction acs as [|[id0 ac0] acs]; simpl.
    constructor.
    constructor; auto.
      split; auto using erase_action__sim.
Qed.

Lemma erase_action__no_AC_tsubst: forall ac, 
  no_AC_tsubst_action (erase_action ac).
Proof.
  destruct ac; simpl; auto.
Qed.

Lemma erase_actions__no_AC_tsubst: forall acs, 
  no_AC_tsubst_actions (erase_actions acs).
Proof.
  induction acs as [|[]]; simpl; 
    constructor; auto using erase_action__no_AC_tsubst.
Qed.

Lemma erase_actions__map_fst: forall acs,
  List.map fst acs = List.map fst (erase_actions acs).
Proof.
  induction acs as [|[]]; simpl; auto.
    f_equal; auto.
Qed.

Lemma erase_actions__uniq: forall acs (Huniq: uniq acs),
  uniq (erase_actions acs).
Proof.
  intros.
  eapply map_fst_uniq; eauto.
  apply erase_actions__map_fst.
Qed.

Lemma erase_actions__dom: forall acs, dom (erase_actions acs) [=] dom acs.
Proof.
  induction acs as [|[] acs]; simpl; fsetdec.
Qed.

Lemma erase_actions__vertex_in_actions_dom: forall acs v,
  vertex_in_actions_dom (erase_actions acs) v <-> vertex_in_actions_dom acs v.
Proof.
  destruct v as [[]]; simpl; try tauto.
    assert (J:=erase_actions__dom acs).
    fsetdec.
Qed.

Lemma erase_actions__vertex_in_actions_codom: forall acs v,
  vertex_in_actions_codom (erase_actions acs) v <-> 
    vertex_in_actions_codom acs v.
Proof.
  destruct v; simpl.
  split; intros [id0 [ac0 [Hin Ha2v]]].
    unfold erase_actions in Hin.
    unfold ListMap.map in Hin.
    apply List.in_map_iff in Hin.
    destruct Hin as [[id1 ac1] [EQ Hin]].
    inv EQ.
    exists id0. exists ac1.
      rewrite <- erase_action__sim in Ha2v; auto.

    exists id0. exists (erase_action ac0).
    split.
      unfold erase_actions.
      unfold ListMap.map.
      apply List.in_map_iff.
      exists (id0,ac0). auto.

      rewrite <- erase_action__sim; auto.
Qed.

Lemma erase_actions__avertexes: forall acs v,
  avertexes (erase_actions acs) v <-> avertexes acs v.
Proof.
  intros.
  split; intros [Hv | Hv].
    left. apply erase_actions__vertex_in_actions_dom; auto.
    right. apply erase_actions__vertex_in_actions_codom; auto.
 
    left. apply erase_actions__vertex_in_actions_dom; auto.
    right. apply erase_actions__vertex_in_actions_codom; auto.
Qed.

Lemma erase_actions__aarcs: forall acs e,
  aarcs (erase_actions acs) e <-> aarcs acs e.
Proof.
  destruct e as [[] [[]]]; simpl; try tauto.
  split; intros [ac [Hin Ha2v]].
    unfold erase_actions in Hin.
    unfold ListMap.map in Hin.
    apply List.in_map_iff in Hin.
    destruct Hin as [[id1 ac1] [EQ Hin]].
    inv EQ.
    exists ac1.
      rewrite <- erase_action__sim in Ha2v; auto.

    exists (erase_action ac).
    split.
      unfold erase_actions.
      unfold ListMap.map.
      apply List.in_map_iff.
      exists (id5,ac). auto.

      rewrite <- erase_action__sim; auto.
Qed.

Lemma erase_actions__D_walk_inv: forall acs v1 v2 vl al
  (Hw: D_walk (avertexes (erase_actions acs)) (aarcs (erase_actions acs)) v1 v2 vl al),
  D_walk (avertexes acs) (aarcs acs) v1 v2 vl al.
Proof.
  induction 1.
    constructor.
      eapply erase_actions__avertexes; eauto.
    constructor; auto.
      eapply erase_actions__avertexes; eauto.
      eapply erase_actions__aarcs; eauto.
Qed.

Lemma erase_actions__D_walk: forall acs v1 v2 vl al
  (Hw: D_walk (avertexes acs) (aarcs acs) v1 v2 vl al),
  D_walk (avertexes (erase_actions acs)) (aarcs (erase_actions acs)) v1 v2 vl al.
Proof.
  induction 1.
    constructor.
      eapply erase_actions__avertexes; eauto.
    constructor; auto.
      eapply erase_actions__avertexes; eauto.
      eapply erase_actions__aarcs; eauto.
Qed.

Lemma erase_actions__acyclic: forall acs (Hacyc: acyclic_actions acs),
  acyclic_actions (erase_actions acs).
Proof.
  intros.
  intros v vl al Hw.
  apply erase_actions__D_walk_inv in Hw.
  apply Hacyc in Hw; auto.
Qed.

Lemma erase_actions__wf_AC_remove: forall acs (Hwf: wf_AC_remove acs),
  wf_AC_remove (erase_actions acs).
Proof.
  intros.
  apply Forall_forall.
  intros [id0 ac0] Hin.
  destruct ac0; auto.
  intro J.
  rewrite erase_actions__vertex_in_actions_codom in J.
  unfold erase_actions in Hin.
  unfold ListMap.map in Hin.
  apply List.in_map_iff in Hin.
  destruct Hin as [[id1 ac1] [EQ Hin]].
  inv EQ.
  destruct ac1; inv H1.
  eapply Forall_forall in Hin; eauto.
  simpl in Hin.
  apply Hin. eauto.
Qed.

(********************************************************************************)
(* Lem 74 *)
(* Given acyclic and unique actions, the two composed passes are equivalent. *)
Lemma list_compose_actions__list_composed_substs: forall actions 
  (Hwf: wf_AC_remove actions) (Hacyclic: acyclic_actions actions) 
  (Huniq: uniq actions) f,
  ListComposedPass.substs_fdef (ListComposedPass.compose_actions actions) f =
  composed_pipelined_actions actions f.
Proof.
  intros.
  assert (J:=erase_actions__sim actions).
  unfold composed_pipelined_actions.
  transitivity
    (ListComposedPass.substs_fdef 
      (ListComposedPass.compose_actions (erase_actions actions)) f).
  Case "1".
    apply sim_actions__eq_list_substs_fdef.
      apply list_compose_actions__sim; auto.
  Case "2".
    transitivity
      (ListComposedPass.substs_fdef 
        (pipelined_actions__composed_actions 
           (substs_actions (erase_actions actions))) f).
    SCase "2.1".
      apply eq_actions__eq_list_substs_fdef; auto.
      apply list_compose_actions__eq__pipelined_actions__composed_actions__Some; 
        auto.
        apply erase_actions__uniq; auto.
        apply erase_actions__wf_AC_remove; auto.
        apply erase_actions__no_AC_tsubst.
        apply erase_actions__acyclic; auto.
    SCase "2.2".
      apply sim_actions__eq_list_substs_fdef.
        apply pipelined_actions__composed_actions__sim.
        apply substs_actions__sim; auto using sim_actions__sym.
Qed.

