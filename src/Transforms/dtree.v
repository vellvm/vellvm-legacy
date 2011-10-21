Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vellvm.
Require Import Lattice.
Require Import Maps.
Require Import ListSet.

Section MoreMove.

Variable A: Type.
Hypothesis Hdec: forall x y : A, {x = y} + {x <> y}.

Lemma remove_length: forall (a: A) (l1: list A), 
  (length (List.remove Hdec a l1) <= length l1)%nat.
Proof.
  induction l1; simpl; intros.
    omega.
    destruct (Hdec a a0); subst; simpl; omega.
Qed.

Lemma remove_in_length: forall (a: A) (l1: list A), 
  In a l1 -> (length (List.remove Hdec a l1) < length l1)%nat.
Proof.
  induction l1; simpl; intros.
    inv H.

    destruct H as [H | H]; subst.
      destruct (Hdec a a); try congruence.
      assert (J:=@remove_length a l1). omega.    

      destruct (Hdec a a0); subst.
        assert (J:=@remove_length a0 l1). omega.    
        assert (J:=@IHl1 H). simpl. omega.
Qed.

Lemma remove_neq_in: forall (a b:A) (l1: list A),
  a <> b ->
  In a l1 ->
  In a (List.remove Hdec b l1).
Proof.
  induction l1; simpl; intros; auto.
    destruct H0 as [H0 | H0]; subst.
      destruct (Hdec b a); subst; simpl; auto.
        congruence.
      destruct (Hdec b a0); subst; simpl; auto.
Qed.

Lemma remove_neq_in': forall (a b:A) (l1: list A),
  a <> b ->
  In a (List.remove Hdec b l1) ->
  In a l1.
Proof.
  induction l1; simpl; intros; auto.
    destruct (Hdec b a0); subst; simpl; auto.
      simpl in H0.
      destruct H0 as [H0 | H0]; subst; auto.
Qed.

End MoreMove.

Program Fixpoint reachablity_analysis_aux (nvisited: list l) (succs : ATree.t ls) 
  (curr: l) (acc: list l) {measure (List.length nvisited)%nat}
  : option (list l) := 
match (ATree.get curr succs) with
| None => None
| Some nexts => 
    fold_left 
      (fun oacc' next =>
       match oacc' with
       | None => None
       | Some acc' =>
         if (in_dec eq_atom_dec next nvisited) then 
           if (in_dec eq_atom_dec next acc) then
             Some acc'
           else
             match reachablity_analysis_aux (List.remove eq_atom_dec next nvisited) 
                     succs next (next::acc) with
             | None => None
             | Some acc'' => Some (ListSet.set_union eq_atom_dec acc' acc'')
             end
         else 
           Some acc'
       end)
      nexts (Some acc)
end.
Next Obligation. 
  apply remove_in_length; auto.
Qed.

Fixpoint get_reachable_labels (bd:list l) (rd:AMap.t bool) (acc:list l) 
  : list l :=
match bd with
| nil => acc 
| l0::bd' => if (AMap.get l0 rd) 
             then get_reachable_labels bd' rd (l0::acc)
             else get_reachable_labels bd' rd acc
end.

Definition reachablity_analysis (f: fdef) : option (list l) :=
match getEntryBlock f with
| Some (block_intro root _ _ _) =>
    let 'bd := bound_fdef f in
    match areachable_aux f with
    | None => None
    | Some rd => Some (get_reachable_labels bd rd nil)
    end
| None => None
end.

(*
Definition reachablity_analysis (f : fdef) : option (list l) :=
match getEntryBlock f with
| Some (block_intro root _ _ _) =>
    let 'succs := successors f in
    reachablity_analysis_aux 
      (List.remove eq_atom_dec root (bound_fdef f)) succs root [root]
| None => None
end.
*)

Inductive DTree : Set :=
| DT_node : l -> DTrees -> DTree
with DTrees : Set :=
| DT_nil : DTrees
| DT_cons : DTree -> DTrees -> DTrees
.

Fixpoint dtree_dom (dt: DTree) : atoms :=
match dt with
| DT_node l0 dts0 => {{l0}} `union` dtrees_dom dts0
end
with dtrees_dom (dts: DTrees) : atoms :=
match dts with
| DT_nil => empty
| DT_cons dt0 dts0 => dtree_dom dt0 `union` dtrees_dom dts0
end.

Definition imm_domination (f:fdef) (l1 l2:l) : Prop :=
strict_domination f l1 l2 /\
forall l0, strict_domination f l0 l2 -> domination f l0 l1.

Definition get_dtree_root (dt:DTree) : l :=
match dt with
| DT_node l0 _ => l0
end.

Inductive WF_dtree (f:fdef) : DTree -> Prop :=
| WDT_node : forall (l0:l) (dts0:DTrees),
             reachable f l0 ->
             l0 `notin` dtrees_dom dts0 ->
             WF_dtrees f l0 dts0 ->
             WF_dtree f (DT_node l0 dts0)
with WF_dtrees (f:fdef) : l -> DTrees -> Prop :=
| WDT_nil : forall l0, WF_dtrees f l0 DT_nil
| WDT_cons : forall l0 dt0 dts0,
             imm_domination f l0 (get_dtree_root dt0) ->
             AtomSetImpl.inter (dtree_dom dt0) (dtrees_dom dts0) [<=] empty ->
             WF_dtree f dt0 ->
             WF_dtrees f l0 dts0 ->
             WF_dtrees f l0 (DT_cons dt0 dts0)
.

Fixpoint find_idom_aux (res: AMap.t (set l)) (acc:l) (dts: set l): option l :=
match dts with
| nil => Some acc
| l0::dts' =>
    match AMap.get l0 res, AMap.get acc res with
    | dts1, dts2 =>
        if (in_dec l_dec l0 dts2)
        then (* acc << l0 *)
          find_idom_aux res acc dts' 
        else
          if (in_dec l_dec acc dts1)
          then (* l0 << acc *)
            find_idom_aux res l0 dts' 
          else (* l0 and acc are incompariable *)
            None
    end
end.

(* We should prove that this function is not partial. *)
Definition find_idom (res: AMap.t (set l)) (l0:l) : option l :=
match AMap.get l0 res with
| l1::dts0 => find_idom_aux res l1 dts0
| _ => None
end.

Require Import Trees.

Fixpoint dtree_insert dt parent child : option DTree :=
match dt with
| DT_node l0 dts0 => 
    if (id_dec parent l0) then 
      Some (DT_node l0 (DT_cons (DT_node child DT_nil) dts0))
    else 
      match dtrees_insert dts0 parent child with
      | Some dts1 => Some (DT_node l0 dts1)
      | None => None
      end
end
with dtrees_insert (dts: DTrees) parent child : option DTrees :=
match dts with
| DT_nil => Some DT_nil
| DT_cons dt0 dts0 => 
    match dtree_insert dt0 parent child, dtrees_insert dts0 parent child with
    | Some dt1, Some dts1 => Some (DT_cons dt1 dts1)
    | _, _ => None
    end
end.

Fixpoint tree2dtree vs es (tree: Tree vs es) : option DTree :=
match tree with
| T_root (index le) => Some (DT_node le DT_nil)
| T_leaf vs' es' t' (index child) (index parent) _ _ => 
    match tree2dtree vs' es' t' with
    | Some dt' => dtree_insert dt' parent child
    | _ => None
    end
| T_eq vs1 vs2 es1 es2 _ _ t1 => tree2dtree vs1 es1 t1
end.

Definition PreDTree := list (l * l).

Definition getEntryLabel (f:fdef) : option l :=
match f with
| fdef_intro _ ((block_intro l0 _ _ _)::_) => Some l0
| _ => None
end.

Fixpoint cdom (pdt: PreDTree) : atoms :=
match pdt with
| nil => empty
| (_,l2)::pdt' => add l2 (cdom pdt')
end.

Inductive WF_pre_dtree (f:fdef) : PreDTree -> Type :=
| WPDT_entry : forall entry child,
    getEntryLabel f = Some entry ->
    imm_domination f entry child -> 
    WF_pre_dtree f ((entry, child)::nil)
| WPDT_cons : forall parent child pdt,
    WF_pre_dtree f pdt ->
    reachable f parent ->
    imm_domination f parent child -> 
    child `notin` dom pdt `union` cdom pdt ->
    (parent `in` dom pdt \/ exists ancestor, In (ancestor, parent) pdt) -> 
    WF_pre_dtree f ((parent, child) :: pdt).

Definition arcs_of_pre_dtree (pdt: PreDTree) : A_set :=
fun arc =>
  match arc with
  | A_ends (index parent) (index child) => 
      In (parent, child) pdt \/ In (child, parent) pdt
  end.

Definition vertexes_of_pre_dtree (pdt: PreDTree) : V_set :=
fun v =>
  match v with
  | index n => exists n', In (n, n') pdt \/ In (n', n) pdt
  end.

Lemma In_vertexes_of_pre_dtree: forall l1 l2 pdt,
  In (l1, l2) pdt -> vertexes_of_pre_dtree pdt (index l2).
Proof.
  induction pdt; simpl; intros.
    inv H.
    exists l1.
    destruct H as [H | H]; subst; auto.
Qed.

Lemma In_vertexes_of_pre_dtree': forall l1 l2 pdt,
  In (l1, l2) pdt -> vertexes_of_pre_dtree pdt (index l1).
Proof.
  induction pdt; simpl; intros.
    inv H.
    exists l2.
    destruct H as [H | H]; subst; auto.
Qed.

Lemma InDom_vertexes_of_pre_dtree: forall l1 pdt,
  l1 `in` dom pdt -> vertexes_of_pre_dtree pdt (index l1).
Proof.
  induction pdt; simpl; intros.
    fsetdec.

    destruct a.
    assert (l1 = a \/ l1 `in` dom pdt) as Hin.
      fsetdec.
    destruct Hin as [Hin | Hin]; subst.
      exists l0. auto.
      apply IHpdt in Hin. simpl in Hin.
      destruct Hin as [n' [Hin | Hin]]; exists n'; auto.
Qed.

Lemma Notin_vertexes_of_pre_dtree: forall child pdt
  (n : child `notin` dom pdt `union` cdom pdt),
  ~ vertexes_of_pre_dtree pdt (index child).
Proof.
  induction pdt; simpl; intros.
    intro J. destruct J as [_ [J | J]]; inv J.

    intro J. 
    destruct J as [n' [J | J]].
      destruct J as [J | J]; subst.
        fsetdec.
        
        destruct a.    
        apply In_vertexes_of_pre_dtree' in J.
        revert J. 
        apply IHpdt; auto.
      destruct J as [J | J]; subst.
        fsetdec.

        destruct a.    
        apply In_vertexes_of_pre_dtree in J.
        revert J. 
        apply IHpdt; auto.
Qed.

Lemma In_arcs_of_pre_dtree: forall a a0 pdt,
  In (a, a0) pdt ->
  Ensembles.In Arc (arcs_of_pre_dtree pdt) (A_ends (index a) (index a0)).
Proof.
  induction pdt; simpl; intros.
    inv H.

    unfold Ensembles.In. simpl.
    destruct H as [H | H]; subst; auto.
Qed.

Lemma In_arcs_of_pre_dtree': forall a a0 pdt,
  In (a0, a) pdt ->
  Ensembles.In Arc (arcs_of_pre_dtree pdt) (A_ends (index a) (index a0)).
Proof.
  induction pdt; simpl; intros.
    inv H.

    unfold Ensembles.In. simpl.
    destruct H as [H | H]; subst; auto.
Qed.

Lemma WF_pre_dtree_isa_tree: forall f pdt, 
  WF_pre_dtree f pdt -> 
  Tree (vertexes_of_pre_dtree pdt) (arcs_of_pre_dtree pdt).
Proof.
  intros f pdt Hwf.
  induction Hwf.
    apply T_eq with 
      (v:=V_union (V_single (index child)) (V_single (index entry)))
      (a:=A_union (E_set (index entry) (index child)) A_empty).
      apply U_set_eq.
        intros x.
        split; intro J.
          inv J; inv H; simpl.
            exists entry. auto.
            exists child. auto.
          destruct x; simpl in J.
          destruct J as [n' [J | J]].
            destruct J as [J | J]; inv J. 
            apply In_right. apply In_single; auto.

            destruct J as [J | J]; inv J. 
            apply In_left. apply In_single; auto.
      apply A_set_eq.
        intros x.
        split; intro J.
          inv J; inv H; simpl; auto.

          destruct x as [[] []]; simpl in J.
          destruct J as [J | J].
            destruct J as [J | J]; inv J. 
            apply In_left. apply E_right.

            destruct J as [J | J]; inv J. 
            apply In_left. apply E_left.
      apply T_leaf.
        apply T_root.
        apply In_single; auto.

        intro J. inv J. 
        unfold imm_domination, strict_domination in i0.
        destruct i0 as [[_ J] _]; auto.

    apply T_eq with 
      (v:=V_union (V_single (index child)) (vertexes_of_pre_dtree pdt))
      (a:=A_union (E_set (index parent) (index child)) (arcs_of_pre_dtree pdt)).
      apply U_set_eq.
        intros [v].
        split; intro J.
          inv J; inv H.
            exists parent. simpl. auto.

            destruct H0 as [H0 | H0].
              eapply In_vertexes_of_pre_dtree'; simpl; eauto.
              eapply In_vertexes_of_pre_dtree; simpl; eauto.

          destruct J as [n' [J | J]]; simpl in J.
            apply In_right. 
            destruct J as [J | J].
              inv J. 
              clear - o. destruct o as [o | [anc e]].
                eapply InDom_vertexes_of_pre_dtree; eauto.
                apply In_vertexes_of_pre_dtree in e; auto.

              apply In_vertexes_of_pre_dtree' in J; auto.
            destruct J as [J | J].
              inv J. 
              apply In_left. apply In_single.

              apply In_right. 
              apply In_vertexes_of_pre_dtree in J; auto.
      apply A_set_eq.
        intros [v1 v2]. destruct v1, v2.
        split; intro J.
          inv J; inv H; simpl; auto.

          inv J.
            simpl in H. 
            destruct H as [H | H].
              inv H.
              apply In_left. apply E_right.
              apply In_right. apply In_arcs_of_pre_dtree; auto.
            simpl in H. 
            destruct H as [H | H].
              inv H.
              apply In_left. apply E_left.
              apply In_right. apply In_arcs_of_pre_dtree'; auto.
      apply T_leaf; auto.
        clear - o. destruct o as [o | [anc e]].
          eapply InDom_vertexes_of_pre_dtree; eauto.
          apply In_vertexes_of_pre_dtree in e; auto.
        apply Notin_vertexes_of_pre_dtree; auto.
Qed.

Fixpoint find_children (res: AMap.t (set l)) (root:l) 
  (others:set l) (acc:list l): option (list l) :=
match others with 
| nil => Some acc
| l0::others' =>
    match find_idom res l0 with
    | None => None
    | Some l1 =>
        if (id_dec root l1) then
          if (in_dec l_dec l0 acc) 
          then find_children res root others' acc
          else find_children res root others' (l0::acc) 
        else find_children res root others' acc        
    end
end.

Lemma find_children_spec1_aux: forall res root others l0 acc children, 
  find_children res root others acc = ret children ->
  In l0 children ->
  In l0 others \/ In l0 acc.
Proof.
  induction others; simpl; intros.
    inv H; auto.

    destruct (find_idom res a); tinv H.
    destruct (id_dec root l1); subst.
      destruct (in_dec l_dec a acc).
        eapply IHothers in H; eauto.
          destruct H; auto.
        eapply IHothers in H; eauto.
          destruct H; auto.
          simpl in H. destruct H; subst; auto.
      eapply IHothers in H; eauto.
      destruct H; auto.
Qed.

Lemma find_children_spec1: forall res root others children, 
  find_children res root others nil = ret children ->
  incl children others.
Proof.
  intros. intros x Jx.
  eapply find_children_spec1_aux in H; eauto.
  destruct H; auto. inv H.
Qed.

Lemma find_children_spec2_aux: forall res root others acc children, 
  NoDup acc ->
  find_children res root others acc = ret children ->
  NoDup children.
Proof.
  induction others; simpl; intros.
    inv H0; auto.

    destruct (find_idom res a); tinv H0.
    destruct (id_dec root l0); subst; eauto.
    destruct (in_dec l_dec a acc); eauto.
Qed.

Lemma find_children_spec2: forall res root others children, 
  find_children res root others nil = ret children ->
  NoDup children.
Proof.
  intros.
  eapply find_children_spec2_aux in H; eauto.
Qed.

Lemma fold_left_remove_in_length_aux: forall (children others' others:list atom),
  NoDup children ->
  incl children others' ->
  incl others' others ->
  (length others' <= length others)%nat ->
  children <> nil ->
  (length (fold_left
    (fun (acc0 : list atom) (l0 : id) => List.remove eq_atom_dec l0 acc0)
      children others') < length others)%nat.
Proof.
  induction children; simpl; intros.
    congruence.

    assert (In a others') as Hin.
      apply H0; simpl; auto.
    assert (J:=@remove_in_length _ eq_atom_dec a others' Hin).
    assert ((length (List.remove eq_atom_dec a others') < length others)%nat) 
      as J'.
      omega.
    inv H.
    destruct children.
      simpl. auto.

      apply IHchildren; auto.
        intros x Jx.
        assert (In x (a :: a0 :: children)) as Hin'.
          simpl in Jx. destruct Jx; subst; simpl; auto.
        apply H0 in Hin'.
        apply remove_neq_in; auto.
        destruct (id_dec x a); subst; auto.

        intros x Jx. 
        apply H1.
        apply remove_neq_in' in Jx; auto.
        destruct (id_dec x a); subst; auto.
        contradict Jx. apply remove_In.

        omega.

        intro J0. inv J0.
Qed.

Lemma fold_left_remove_in_length: forall (children others:list atom),
  NoDup children ->
  incl children others ->
  children <> nil ->
  (length (fold_left
    (fun (acc0 : list atom) (l0 : id) => List.remove eq_atom_dec l0 acc0)
      children others) < length others)%nat.
Proof.
  intros.
  apply fold_left_remove_in_length_aux; auto.
    apply incl_refl.
Qed.

Fixpoint compute_idoms (res: AMap.t (set l)) (bd: list l) (acc: list (l * l)) :
  list (l * l) :=
match bd with
| nil => acc
| l0 :: bd' =>
    match find_idom res l0 with
    | None => compute_idoms res bd' acc
    | Some l1 => compute_idoms res bd' ((l1,l0)::acc)
    end
end.

Fixpoint find_next_child (idoms: list (l * l)) (parent: l) (others:set l) 
  : option l :=
match idoms with
| nil => None
| (l1, l2)::idoms' =>
    if (l_dec l1 parent) then 
      if (in_dec l_dec l2 others) then Some l2
      else find_next_child idoms' parent others
    else find_next_child idoms' parent others
end.

Fixpoint find_next_sub_pre_dtree_aux (idoms: list (l * l)) (pdt0 pdt:PreDTree) 
  (others:set l) : option (PreDTree * set l) :=
match pdt with
| nil => None
| (p, ch)::pdt' => 
    match find_next_child idoms ch others with
    | None => 
        match find_next_child idoms p others with
        | None => 
            find_next_sub_pre_dtree_aux idoms pdt0 pdt' others
        | Some ch' =>
            Some ((p, ch')::pdt0, List.remove l_dec ch' others)
        end
    | Some ch' => Some ((ch, ch')::pdt0, List.remove l_dec ch' others)
    end
end.

Definition find_next_sub_pre_dtree (idoms: list (l * l)) (pdt:PreDTree) 
  (others:set l) : option (PreDTree * set l) :=
find_next_sub_pre_dtree_aux idoms pdt pdt others.

Lemma find_next_child_inv : forall idoms l1 others l2,
  find_next_child idoms l1 others = ret l2 ->
  In l2 others /\ In (l1, l2) idoms.
Proof.
  induction idoms; simpl; intros.
    inv H.

    destruct a.
    destruct (l_dec l0 l1); subst.
      destruct (in_dec l_dec l3 others).
        inv H. auto.
        apply IHidoms in H. destruct H. split; auto.
      apply IHidoms in H. destruct H. split; auto.
Qed.       

Lemma find_next_sub_pre_dtree_aux_length: forall idoms pdt0 acc others acc' others',
  find_next_sub_pre_dtree_aux idoms pdt0 acc others = ret (acc', others') ->
  (length others' < length others)%nat.
Proof.
  induction acc; simpl; intros.
    inv H. 

    destruct a.
    remember (find_next_child idoms l1 others) as R.
    destruct R.
      inv H.
      symmetry in HeqR.
      apply find_next_child_inv in HeqR.
      destruct HeqR.
      apply remove_in_length; auto.

      remember (find_next_child idoms l0 others) as R.
      destruct R; eauto.
        inv H.
        symmetry in HeqR0.
        apply find_next_child_inv in HeqR0.
        destruct HeqR0.
        apply remove_in_length; auto.
Qed.

Lemma find_next_sub_pre_dtree_length: forall idoms acc others acc' others',
  find_next_sub_pre_dtree idoms acc others = ret (acc', others') ->
  (length others' < length others)%nat.
Proof.
  intros.
  unfold find_next_sub_pre_dtree in H.
  apply find_next_sub_pre_dtree_aux_length in H; auto.
Qed.

Program Fixpoint create_pre_dtree_aux (others:set l) (idoms: list (l * l)) 
  (acc:PreDTree) {measure (List.length others)} : option PreDTree :=
match others with
| nil => Some acc
| _ =>
   match find_next_sub_pre_dtree idoms acc others with
   | None => None
   | Some (acc', others') => create_pre_dtree_aux others' idoms acc'
   end
end.
Next Obligation. 
  eapply find_next_sub_pre_dtree_length; eauto.
Qed.

Program Fixpoint create_dtree_aux (others:set l) (res: AMap.t (set l)) 
  (root:l) {measure (List.length others)}
  : option DTree :=
match find_children res root others nil with
| Some nil => Some (DT_node root DT_nil)
| Some children =>
    let others' := 
      fold_left (fun acc l1 => List.remove id_dec l1 acc) children others in
    let op_dts0 :=
      (fold_left 
        (fun acc l1 => 
         match acc, create_dtree_aux others' res l1 with
         | Some dts0, Some dt0 => Some (DT_cons dt0 dts0) 
         | _, _ => None
         end)
        children (Some DT_nil)) in
    match op_dts0 with
    | Some dts0 => Some (DT_node root dts0)
    | _ => None
    end
| _ => None 
end.
Next Obligation. 
  symmetry in Heq_anonymous.
  apply fold_left_remove_in_length; auto.
    apply find_children_spec2 in Heq_anonymous; auto.
    apply find_children_spec1 in Heq_anonymous; auto.
    intro J. subst. auto.
Qed.
Next Obligation. split; intros; congruence. Qed.

Fixpoint dep_doms__nondep_doms_aux bd0 (res: AMap.t (Dominators.t bd0)) 
  bd (acc: AMap.t (set l)) : AMap.t (set l) :=
match bd with
| nil => acc
| l0::bd' => 
    match AMap.get l0 res with
    | (Dominators.mkBoundedSet dts0 _) =>
        AMap.set l0 dts0 (dep_doms__nondep_doms_aux bd0 res bd' acc)
    end
end.

Definition dep_doms__nondep_doms bd (res: AMap.t (Dominators.t bd)) 
  : AMap.t (set l) :=
dep_doms__nondep_doms_aux bd res bd (AMap.init nil).

Fixpoint init_pre_dtree (idoms: list (l * l)) (root:l) (others:set l)
  : option (PreDTree * list l) :=
match idoms with 
| nil => None
| (p, ch)::idoms' => 
    if (l_dec p root) then 
      if (in_dec l_dec ch others) then 
        Some ([(p, ch)], List.remove l_dec ch others)
      else None
    else init_pre_dtree idoms' root others
end.

Inductive WF_idoms f : list (l*l) -> Type :=
| WF_idoms_nil : WF_idoms f nil 
| WF_idoms_cons : forall l1 l2 idoms, 
    imm_domination f l1 l2 -> WF_idoms f idoms ->
    WF_idoms f ((l1,l2)::idoms)
.

Lemma WF_pre_dtree__reachable: forall f acc l1 l2,
  WF_pre_dtree f acc ->
  In (l1, l2) acc ->
  reachable f l1 /\ reachable f l2.
Admitted.

Lemma find_next_child__imm_domination: forall f idoms (Hwfi: WF_idoms f idoms) 
  l1 others l2,
  find_next_child idoms l1 others = ret l2 ->
  imm_domination f l1 l2.
Proof.
  induction idoms; simpl; intros.
    inv H.

    destruct a.
    inv Hwfi.
    destruct (l_dec l0 l1); subst; eauto.
      destruct (in_dec l_dec l3 others); eauto.
        inv H. auto.
Qed.

Lemma find_next_sub_pre_dtree_aux_wf_pre_dtree: 
  forall f idoms (Hwfi: WF_idoms f idoms) acc prefix 
    (Hwf:WF_pre_dtree f (prefix++acc)) others acc' others'
  (Hdis: forall l0, 
    In l0 others -> 
    l0 `notin` dom (prefix++acc) `union` cdom (prefix++acc)),
  find_next_sub_pre_dtree_aux idoms (prefix++acc) acc others = 
    ret (acc', others') ->
  WF_pre_dtree f acc'.
Proof.
  induction acc; simpl; intros.
    congruence.

    destruct a.
    remember (find_next_child idoms l1 others) as R.
    destruct R.
      inv H.
      apply WPDT_cons; auto.
        apply WF_pre_dtree__reachable with (l1:=l0)(l2:=l1) in Hwf.
          destruct Hwf; auto.
          apply in_middle.
        eapply find_next_child__imm_domination; eauto.

        symmetry in HeqR.
        apply find_next_child_inv in HeqR.
        destruct HeqR as [J1 J2]. auto.

        right.
        exists l0. apply in_middle.

      remember (find_next_child idoms l0 others) as R.
      destruct R.
        inv H.
        apply WPDT_cons; auto.
          apply WF_pre_dtree__reachable with (l1:=l0)(l2:=l1) in Hwf.
            destruct Hwf; auto.
            apply in_middle.
          eapply find_next_child__imm_domination; eauto.

          symmetry in HeqR0.
          apply find_next_child_inv in HeqR0.
          destruct HeqR0 as [J1 J2]. auto.
          left. simpl_env. fsetdec.
      rewrite_env ((prefix ++ [(l0, l1)]) ++ acc) in H.
      apply IHacc in H; simpl_env; simpl; auto.
Qed.

Lemma find_next_sub_pre_dtree_wf_pre_dtree: 
  forall f idoms (Hwfi: WF_idoms f idoms) pdt (Hwf:WF_pre_dtree f pdt) 
    others pdt' others'
  (Hdis: forall l0, 
    In l0 others -> 
    l0 `notin` dom pdt `union` cdom pdt),
  find_next_sub_pre_dtree idoms pdt others = ret (pdt', others') ->
  WF_pre_dtree f pdt'.
Proof.
  intros.
  unfold find_next_sub_pre_dtree in H.
  change pdt with (nil++pdt) in H, Hdis at 1.
  eapply find_next_sub_pre_dtree_aux_wf_pre_dtree in H; eauto.
Qed.

Definition P_create_pre_dtree_aux__WF_pre_dtree (n:nat) :=
  forall f idoms (Hwfi: WF_idoms f idoms) pdt0 others pdt
  (Hdis: forall l0, 
    In l0 others -> 
    l0 `notin` dom pdt0 `union` cdom pdt0),
  List.length others = n ->
  WF_pre_dtree f pdt0 ->
  create_pre_dtree_aux others idoms pdt0 = Some pdt ->
  WF_pre_dtree f pdt.

Require Import Program.

Ltac simple_create_pre_dtree_aux :=
  unfold create_pre_dtree_aux, create_pre_dtree_aux_func;
  rewrite WfExtensionality.fix_sub_eq_ext;
  repeat fold_sub create_pre_dtree_aux_func ; simpl proj1_sig;
  simpl. 

Lemma find_next_sub_pre_dtree_aux_inv: forall idoms pdt0 pdt others pdt' 
  others',
  find_next_sub_pre_dtree_aux idoms pdt0 pdt others = Some (pdt', others') ->
  exists p, exists ch, 
    pdt' = (p,ch)::pdt0 /\ others' = List.remove l_dec ch others /\
    ((exists p', In (p', p) pdt) \/ (exists ch', In (p, ch') pdt)).
Proof.
  induction pdt; simpl; intros.
    inv H.

    destruct a.
    remember (find_next_child idoms l1 others) as R.
    destruct R.
      inv H.
      exists l1. exists l2. 
      repeat split; auto.
      left. exists l0. auto.

      remember (find_next_child idoms l0 others) as R. 
      destruct R.
        inv H.
        exists l0. exists l2. 
        repeat split; auto.
        right. exists l1. auto.
       
        apply IHpdt in H; auto.
        destruct H as [p [ch [Heq1 [Heq2 [[p' J] | [ch' J]]]]]]; subst.
          exists p. exists ch. 
          repeat split; auto.
          left. exists p'. auto.

          exists p. exists ch. 
          repeat split; auto.
          right. exists ch'. auto.
Qed.

Lemma find_next_sub_pre_dtree_inv: forall idoms pdt others pdt' 
  others',
  find_next_sub_pre_dtree idoms pdt others = Some (pdt', others') ->
  exists p, exists ch, 
    pdt' = (p,ch)::pdt /\ others' = List.remove l_dec ch others /\
    ((exists p', In (p', p) pdt) \/ (exists ch', In (p, ch') pdt)).
Proof.
  intros. unfold find_next_sub_pre_dtree in H.
  apply find_next_sub_pre_dtree_aux_inv in H; auto.
Qed.

Lemma in_dom_cdom: forall p1 p2 pdt0,
  In (p1, p2) pdt0 -> p2 `in` cdom pdt0 /\ p1 `in` dom pdt0.
Proof.
  induction pdt0; simpl; intros.
    inv H.
    destruct H as [H | H]; subst.
      fsetdec.

      destruct a.
      apply IHpdt0 in H.
      fsetdec.
Qed.

Lemma create_pre_dtree_aux__WF_pre_dtree_aux: forall n, 
  P_create_pre_dtree_aux__WF_pre_dtree n.
Proof.
  intro n.
  apply lt_wf_rec. clear n.
  intros n IH.
  unfold P_create_pre_dtree_aux__WF_pre_dtree in *.
  intros f idoms Hwfi pdt0 others pdt Hdis Hlen Hwf.
  destruct others as [|l1 others]; simple_create_pre_dtree_aux.
    intro J. inv J; auto.

    remember (find_next_sub_pre_dtree idoms pdt0 (l1 :: others)) as R.
    destruct R as [[acc' others']|].
      repeat fold_sub create_pre_dtree_aux_func ; simpl proj1_sig.
      fold (create_pre_dtree_aux others' idoms acc').
      intro J. subst.
      apply IH with (m:=length others') (f:=f) in J; auto.
        eapply find_next_sub_pre_dtree_length; eauto.

        symmetry in HeqR.
        apply find_next_sub_pre_dtree_inv in HeqR.
        destruct HeqR as [p [ch [Heq [J1 [[p' J2] | [ch' J2]]]]]]; subst.
          intros l0 Hin.
          simpl.
          assert (l0 <> ch) as Hneq.
            assert (J':=@remove_In _ l_dec (l1 :: others) ch).
            destruct (l_dec l0 ch); subst; auto.
          assert (In l0 (l1::others)) as Hin'.
            apply remove_neq_in' in Hin; auto.
          apply Hdis in Hin'.
          apply in_dom_cdom in J2.
          destruct J2 as [J1 J2].
          assert (l0 <> p) as Hneq'.
            destruct (l_dec l0 p); subst; auto.
          fsetdec.
 
          intros l0 Hin.
          simpl.
          assert (l0 <> ch) as Hneq.
            assert (J':=@remove_In _ l_dec (l1 :: others) ch).
            destruct (l_dec l0 ch); subst; auto.
          assert (In l0 (l1::others)) as Hin'.
            apply remove_neq_in' in Hin; auto.
          apply Hdis in Hin'.
          apply in_dom_cdom in J2.
          destruct J2 as [J1 J2].
          assert (l0 <> p) as Hneq'.
            destruct (l_dec l0 p); subst; auto.
          fsetdec.
        eapply find_next_sub_pre_dtree_wf_pre_dtree; eauto.
      intro J. inv J.
Qed.

Lemma create_pre_dtree_aux__WF_pre_dtree : forall f idoms 
  (Hwfi: WF_idoms f idoms) pdt0 others pdt
  (Hdis: forall l0, 
    In l0 others -> 
    l0 `notin` dom pdt0 `union` cdom pdt0),
  WF_pre_dtree f pdt0 ->
  create_pre_dtree_aux others idoms pdt0 = Some pdt ->
  WF_pre_dtree f pdt.
Proof.
  intros.
  assert (J:=@create_pre_dtree_aux__WF_pre_dtree_aux (List.length others)).
  unfold P_create_pre_dtree_aux__WF_pre_dtree in J. eauto.
Qed.

Lemma init_pre_dtree__WF_pre_dtree : forall f root 
  (Hentry:getEntryLabel f = Some root) idoms 
  (Hwfi: WF_idoms f idoms) others pdt0 others0,
  init_pre_dtree idoms root others = Some (pdt0, others0) ->
  WF_pre_dtree f pdt0.
Proof.
  induction idoms; simpl; intros.
    inv H.

    destruct a.
    inv Hwfi.
    destruct (l_dec l0 root); subst; eauto.
      destruct (in_dec l_dec l1 others); inv H.
      apply WPDT_entry; auto.
Qed.

Lemma init_pre_dtree__disjoint: forall root idoms others pdt0 others0,
  init_pre_dtree idoms root others = ret (pdt0, others0) ->
  ~ In root others ->
  forall l0 : atom, In l0 others0 -> l0 `notin` union (dom pdt0) (cdom pdt0).
Proof.
  induction idoms; simpl; intros.
    inv H.

    destruct a.
    destruct (l_dec l1 root); subst.
      destruct (in_dec l_dec l2 others); inv H.
        simpl.
        assert (l0 <> l2) as Hneq.
          assert (J':=@remove_In _ l_dec others l2).
          destruct (l_dec l0 l2); subst; auto.
        assert (In l0 others) as Hin'.
          apply remove_neq_in' in H1; auto.
        assert (l0 <> root) as Hneq'.
          destruct (l_dec l0 root); subst; auto.
        fsetdec.

      eapply IHidoms in H; eauto.        
Qed.

Lemma compute_idoms__WF_idoms_aux: forall f rd idoms acc,
  reachablity_analysis f = Some rd ->
  WF_idoms f acc ->
  compute_idoms (dep_doms__nondep_doms (bound_fdef f) (dom_analyze f)) rd acc 
    = idoms ->
  WF_idoms f idoms.
Proof.
  induction rd; simpl; intros; subst; auto.
    remember 
      (find_idom (dep_doms__nondep_doms (bound_fdef f) (dom_analyze f)) a) as R.
    destruct R.
      apply IHrd with (acc:=(l0, a) :: acc); auto.
        admit.
        apply WF_idoms_cons; auto.
          admit.
      apply IHrd with (acc:=acc); auto.
        admit.
Qed.

Lemma compute_idoms__WF_idoms: forall f rd idoms,
  reachablity_analysis f = Some rd ->
  compute_idoms (dep_doms__nondep_doms (bound_fdef f) (dom_analyze f)) rd nil 
    = idoms ->
  WF_idoms f idoms.
Proof.
  intros.
  apply compute_idoms__WF_idoms_aux in H0; auto.
    apply WF_idoms_nil.
Qed.

Lemma init_create_pre_dtree_aux__WF_pre_dtree : forall f idoms pdt0 others 
  pdt root rd,
  getEntryLabel f = Some root ->
  reachablity_analysis f = Some rd ->
  compute_idoms (dep_doms__nondep_doms (bound_fdef f) (dom_analyze f)) rd nil 
    = idoms ->
  init_pre_dtree idoms root (List.remove eq_atom_dec root rd) 
    = Some (pdt0, others) ->
  create_pre_dtree_aux others idoms pdt0 = Some pdt ->
  WF_pre_dtree f pdt.
Proof.
  intros.
  eapply compute_idoms__WF_idoms in H1; eauto.
  eapply create_pre_dtree_aux__WF_pre_dtree in H3; eauto.
    eapply init_pre_dtree__disjoint; eauto.
      apply remove_In.
    eapply init_pre_dtree__WF_pre_dtree; eauto.
Qed.

Program Definition create_dtree (f: fdef) : option DTree :=
match getEntryBlock f, reachablity_analysis f with
| Some (block_intro root _ _ _), Some rd =>
    let dt := dom_analyze f in
    let b := bound_fdef f in
    let idoms := compute_idoms (dep_doms__nondep_doms b dt) rd nil in
    match init_pre_dtree idoms root (List.remove eq_atom_dec root rd) with
    | None => None
    | Some (pdt0, others) =>
        match (create_pre_dtree_aux others idoms pdt0) with
        | None => None
        | Some pdt => 
            tree2dtree 
              (vertexes_of_pre_dtree pdt) (arcs_of_pre_dtree pdt)
              (WF_pre_dtree_isa_tree f pdt _)
        end
    end
| _, _ => None
end.
Next Obligation. 
  eapply init_create_pre_dtree_aux__WF_pre_dtree; eauto.
    clear - Heq_anonymous.
    destruct f; simpl in *.
    destruct b; simpl in *; inv Heq_anonymous. auto.
Qed.

Scheme dtree_rec2 := Induction for DTree Sort Set
  with dtrees_rec2 := Induction for DTrees Sort Set.

Definition dtree_mutrec P P' :=
  fun h1 h2 h3 => 
    (pair (@dtree_rec2 P P' h1 h2 h3) (@dtrees_rec2 P P' h1 h2 h3)).

Definition dtree_insert__wf_dtree_prop (dt1:DTree) := 
forall f a1 a0 dt2,
  WF_dtree f dt1 ->
  dtree_insert dt1 a1 a0 = ret dt2 ->
  WF_dtree f dt2.

Definition dtrees_insert__wf_dtrees_prop (dts1:DTrees) := 
forall f root a1 a0 dts2,
  WF_dtrees f root dts1 ->
  dtrees_insert dts1 a1 a0 = ret dts2 ->
  WF_dtrees f root dts2.

Lemma dtree_insert__wf_dtree_mutrec :
  (forall dt1, dtree_insert__wf_dtree_prop dt1) *
  (forall dts1, dtrees_insert__wf_dtrees_prop dts1).
Proof.
  apply dtree_mutrec; 
    unfold dtree_insert__wf_dtree_prop, dtrees_insert__wf_dtrees_prop;
    simpl; intros.

    inv H0.
    destruct (id_dec a1 l0); subst.
      inv H1.
      apply WDT_node; simpl; auto.
        admit.
        apply WDT_cons; simpl; auto.
          admit.
          admit.
          apply WDT_node; simpl; auto.
            admit.
            apply WDT_nil.
       
      remember (dtrees_insert d a1 a0) as R.
      destruct R; inv H1. 
        apply WDT_node; simpl; eauto.
          admit.
        
    inv H0. auto.

    remember (dtree_insert d a1 a0) as R.
    destruct R; inv H2. 
    remember (dtrees_insert d0 a1 a0) as R.
    destruct R; inv H4. 
    inv H1.
    apply WDT_cons; simpl; eauto.
      admit.
      admit.
Qed.

Lemma dtree_insert__wf_dtree: forall f a1 a0 dt1 dt2,
  WF_dtree f dt1 ->
  dtree_insert dt1 a1 a0 = ret dt2 ->
  WF_dtree f dt2.
Proof.
  induction dt1; simpl; intros.
    destruct (id_dec a1 l0); subst.
      inv H0.
      inv H.
      apply WDT_node; simpl; auto.
        admit.
        apply WDT_cons; simpl; auto.
          admit.
          admit.
          apply WDT_node; simpl; auto.
            admit.
            apply WDT_nil.
       
      remember (dtrees_insert d a1 a0) as R.
      destruct R.
        inv H0. auto.


Admitted.

Lemma tree2dtree__wf_dtree: forall f vs es tree dt,
  tree2dtree vs es tree = Some dt -> WF_dtree f dt.
Proof.
  induction tree; simpl; intros.
    destruct r. inv H.
    apply WDT_node.
      admit.
      simpl. fsetdec.
      apply WDT_nil.

    destruct f0. destruct n.
    remember (tree2dtree v a tree) as R.
    destruct R.
      eapply dtree_insert__wf_dtree in H; eauto.
      inv H.

    apply IHtree in H; auto.
Qed.

(*
Definition create_dtree (f: fdef) : option DTree :=
match getEntryBlock f, reachablity_analysis f with
| Some (block_intro root _ _ _), Some rd =>
    let 'dt := dom_analyze f in
    let 'b := bound_fdef f in
    create_dtree_aux (dep_doms__nondep_doms b dt) root 
      (List.remove eq_atom_dec root rd)
| _, _ => None
end.
*)

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
