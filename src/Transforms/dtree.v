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
| WDT_note : forall (l0:l) (dts0:DTrees),
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

Program Fixpoint create_dtree_aux (res: AMap.t (set l)) 
  (root:l) (others:set l) {measure (List.length others)}
  : option DTree :=
match find_children res root others nil with
| Some nil => Some (DT_node root DT_nil)
| Some children =>
    let others' := 
      fold_left (fun acc l1 => List.remove id_dec l1 acc) children others in
    let op_dts0 :=
      (fold_left 
        (fun acc l1 => 
         match acc, create_dtree_aux res l1 others' with
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

Definition create_dtree (f: fdef) : option DTree :=
match getEntryBlock f, reachablity_analysis f with
| Some (block_intro root _ _ _), Some rd =>
    let 'dt := dom_analyze f in
    let 'b := bound_fdef f in
    create_dtree_aux (dep_doms__nondep_doms b dt) root 
      (List.remove eq_atom_dec root rd)
| _, _ => None
end.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
