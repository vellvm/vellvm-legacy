Require Export Coqlib.
Require Export Maps.
Require Import syntax.
Require Import infrastructure_props.
Require Import Metatheory.
Require Import Program.Tactics.
Require Import dom_libs.

Import LLVMsyntax.

Record Frame := mkFrame {
  Fr_name: l;
  Fr_scs: ls
}.

Fixpoint find_next_visit_in_scs (visited: ATree.t unit) (scs: ls) 
  : option (l * ls) :=
match scs with
| nil => None
| sc::scs' => 
    match ATree.get sc visited with
    | None => Some (sc, scs')
    | _ => find_next_visit_in_scs visited scs'
    end
end.

Record PostOrder := mkPO {
  PO_cnt: positive;
  PO_a2p: ATree.t positive
}.

Definition postorder_inc (po:PostOrder) (v:l) : PostOrder :=
let '(mkPO cnt a2p) := po in
mkPO (Psucc cnt) (ATree.set v cnt a2p).

Fixpoint find_next_visit_in_stk (succs: ATree.t ls)
  (visited: ATree.t unit) (po:PostOrder) (frs: list Frame) 
  : l * list Frame * PostOrder + PostOrder :=
match frs with
| nil => inr po
| mkFrame v scs::frs' => 
    match find_next_visit_in_scs visited scs with
    | Some (sc, scs') => 
        inl (sc, mkFrame sc (succs!!!sc)::mkFrame v scs'::frs', po)
    | None => find_next_visit_in_stk succs visited (postorder_inc po v) frs'
    end
end.

Ltac inv_mbind_app :=
  match goal with
  | H: _ = match ?e with
       | Some _ => _
       | None => _
       end |- _ => remember e as R; destruct R
  | H: match ?e with
       | Some _ => _
       | None => _
       end = _ |- _ => remember e as R; destruct R
  end.

Lemma find_next_visit_in_scs_spec: forall visited scs sc scs'
  (Hfind : Some (sc, scs') = find_next_visit_in_scs visited scs),
  incl (sc::scs') scs /\ ATree.get sc visited = None.
Proof.
  induction scs as [|sc scs]; simpl; intros.
    congruence.

    inv_mbind_app.
      apply IHscs in Hfind.
      destruct_pairs.
      split; eauto with datatypes v62.
    
      uniq_result.
      split; eauto with datatypes v62.
Qed.

Lemma length_le__length_lt: forall A 
  (eq_dec : forall x y : A, {x = y}+{x <> y})
  (a:A) (l2:list A) (l1:list A) 
  (Huniq: list_norepet l1) (Hinc: incl l1 l2)  
  (Hnotin: ~ In a l1) (Hin: In a l2), 
  (length l1 < length l2)%nat.
Proof.
  intros.
  assert (incl l1 (List.remove eq_dec a l2)) as Hinc'.
    apply remove_notin_incl; eauto with datatypes v62.
  apply incl__length_le in Hinc'; auto.
  assert (length (List.remove eq_dec a l2) < length l2)%nat as Hle.
    apply remove_in_length; auto with datatypes v62.
  omega.
Qed.

Definition stk_takes_succs succs (stk : list Frame) : Prop :=
List.Forall (fun fr : Frame => 
             incl (Fr_scs fr) (XATree.children_of_tree succs)) stk.

Hint Unfold stk_takes_succs.

Lemma find_next_visit_in_stk_spec1: forall succs visited (stk : list Frame)
  (Hp : stk_takes_succs succs stk)  
  po (next : l) (stk' : list Frame) po'
  (Hfind : inl (next, stk', po') = find_next_visit_in_stk succs visited po stk),
  Forall 
    (fun fr : Frame => incl (Fr_scs fr) (XATree.children_of_tree succs)) 
    stk'.
Proof.
  induction 1 as [|[v scs]]; simpl; intros.
    congruence.
        
    inv_mbind_app; eauto 2.
      destruct_let.
      uniq_result.
      apply find_next_visit_in_scs_spec in HeqR.
      destruct_pairs.
      constructor.
        simpl. apply XATree.children_in_children_of_tree.
        constructor; auto.
          simpl in *.
          eauto with datatypes v62.
Qed.

Lemma find_next_visit_in_stk_spec3_helper: forall 
  (succs : ATree.t (list MetatheoryAtom.AtomImpl.atom))
  (visited : ATree.t unit)
  (Hinc : incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  (v : l) (scs : ls)
  (H : incl (Fr_scs {| Fr_name := v; Fr_scs := scs |})
        (XATree.children_of_tree succs))
  (l0 : l) (l1 : ls) (H0 : incl (l0 :: l1) scs)
  (H1 : visited ! l0 = None),
  (length (XATree.parents_of_tree visited) < 
     length (XATree.children_of_tree succs))%nat.
Proof.
  intros.
  assert (In l0 (XATree.children_of_tree succs)) as Hin.
    apply H. simpl. apply H0. xsolve_in_list.
  eapply length_le__length_lt; eauto.
    apply ATree.elements_keys_norepet; auto.
    apply XATree.notin_tree__notin_parents_of_tree; auto.
Qed.

Lemma find_next_visit_in_stk_spec3: forall succs visited 
  (Hinc: incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  (stk : list Frame) 
  (Hp : stk_takes_succs succs stk)
  (next : l) (stk' : list Frame) po po'
  (Hfind : inl (next, stk', po') =
                   find_next_visit_in_stk succs visited po stk),
  (length (XATree.children_of_tree succs) -
    length (XATree.parents_of_tree (ATree.set next tt visited)) <
   length (XATree.children_of_tree succs) - 
    length (XATree.parents_of_tree visited))%nat.
Proof.
  induction 2 as [|[v scs]]; simpl; intros.
    congruence.

    inv_mbind_app; eauto 2.
      destruct_let.
      uniq_result.
      apply find_next_visit_in_scs_spec in HeqR.
      destruct_pairs.
      assert (length (XATree.parents_of_tree (ATree.set l1 tt visited)) =
                length (XATree.parents_of_tree visited) + 1)%nat as Heq.
        apply XATree.parents_of_tree_succ_len; auto.
      assert (length (XATree.parents_of_tree visited) <
                length (XATree.children_of_tree succs))%nat as Hlt.
        eapply find_next_visit_in_stk_spec3_helper; eauto.
      omega.
Qed.

Lemma find_next_visit_in_stk_spec2: forall (succs : ATree.t ls) 
  (visited : ATree.t unit)
  (Hinc : incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  (stk : list Frame)
  (Hp : stk_takes_succs succs stk)
  (next : l) (stk' : list Frame) po po'
  (Hfind : inl (next, stk', po') = find_next_visit_in_stk succs visited po stk),
  incl (XATree.parents_of_tree (ATree.set next tt visited))
    (XATree.children_of_tree succs).
Proof.
  induction 2 as [|[v scs] ? IH]; simpl; intros.
    congruence.

    inv_mbind_app; eauto 2.
      destruct_let.
      uniq_result.
      apply find_next_visit_in_scs_spec in HeqR.
      destruct_pairs.
      intros x Hin.
      apply XATree.parents_of_tree_spec in Hin.
      destruct Hin as [? Hin].
      apply ATree.elements_complete in Hin. 
      rewrite ATree.gsspec in Hin.
      destruct_if.
        eauto with datatypes v62.
           
        apply ATree.elements_correct in H2. 
        apply Hinc.
        apply List.in_map with (f:=fst) in H2; auto.
Qed.

Program Fixpoint dfs_aux (succs: ATree.t ls)
  (visited: ATree.t unit) (po:PostOrder) (stk: list Frame) 
  (Hp: stk_takes_succs succs stk /\
       incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  {measure 
     (length (XATree.children_of_tree succs) - 
      length (XATree.parents_of_tree visited))%nat }
  : PostOrder :=
  match find_next_visit_in_stk succs visited po stk with
  | inr po' => po'
  | inl (next, stk', po') => dfs_aux succs (ATree.set next tt visited) po' stk' _
  end.
Next Obligation.
  split.
    eapply find_next_visit_in_stk_spec1; eauto.
    eapply find_next_visit_in_stk_spec2; eauto.
Qed.
Next Obligation.
  eapply find_next_visit_in_stk_spec3; eauto.
Qed.

Program Definition dfs (succs: ATree.t ls) (entry:l) (pinit:positive) : PostOrder :=
dfs_aux succs (ATree.empty unit) (mkPO pinit (ATree.empty positive)) 
  (mkFrame entry (succs!!!entry)::nil) _.
Next Obligation.
  split.  
    constructor; auto.
      apply XATree.children_in_children_of_tree.
    rewrite XATree.parents_of_empty_tree. 
    intros x Hin. tauto.
Qed.

Fixpoint stk_isa_path (succs: ATree.t ls) (entry:atom) (stk:list Frame) : Prop :=
match stk with
| nil => True
| mkFrame v _::nil => v = entry
| mkFrame sc _::(mkFrame n _::_) as stk' => 
    In sc (succs !!! n) /\ stk_isa_path succs entry stk'
end.

Definition node_in_stk (a2:atom) (stk:list Frame) : Prop :=
exists stk1, exists stk3, exists scs2, stk = stk1 ++ mkFrame a2 scs2  :: stk3.

Definition wf_aorder_aux (succs: ATree.t ls) (entry:atom) (po:PostOrder) 
  (stk: list Frame) : Prop :=
  forall a1 p1 (Hget: (PO_a2p po) ! a1 = Some p1),
    (p1 < PO_cnt po)%positive /\
    forall (Hneq: a1 <> entry), 
    exists a2, 
      In a2 ((XATree.make_predecessors succs) !!! a1) /\ 
      ((exists p2, (PO_a2p po) ! a2 = Some p2 /\ (p2 > p1)%positive) \/
       node_in_stk a2 stk).

Definition wf_stack (succs: ATree.t ls) (entry:atom) (po:PostOrder) 
  (stk: list Frame) : Prop :=
stk_isa_path succs entry stk /\
stk_takes_succs succs stk /\
wf_aorder_aux succs entry po stk.

Definition wf_aorder scs (entry:atom) (a2p:ATree.t positive) : Prop :=
  forall a1 (Hneq: a1 <> entry) p1 (Hget: a2p ! a1 = Some p1),
  exists a2, exists p2,
    In a2 ((XATree.make_predecessors scs) !!! a1) /\ 
    a2p ! a2 = Some p2 /\ (p2 > p1)%positive.

Definition dfs_aux_wf_stack_prop (n:nat) : Prop := forall (succs: ATree.t ls) 
  (visited: ATree.t unit) 
  (Heq: n = (length (XATree.children_of_tree succs) - 
             length (XATree.parents_of_tree visited))%nat)
  entry (po1:PostOrder) (stk: list Frame) 
  (Hp: stk_takes_succs succs stk /\
       incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  po2 (Hdsf: dfs_aux succs visited po1 stk Hp = po2)
  (Hwf: wf_stack succs entry po1 stk),
  wf_aorder succs entry (PO_a2p po2).

Lemma dfs_aux_wf_stack_aux: forall n, dfs_aux_wf_stack_prop n.
Admitted.

Lemma dfs_aux_wf_stack: forall (succs: ATree.t ls) entry
  (visited: ATree.t unit) (po1:PostOrder) (stk: list Frame) 
  (Hp: stk_takes_succs succs stk /\
       incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  po2 (Hdsf: dfs_aux succs visited po1 stk Hp = po2)
  (Hwf: wf_stack succs entry po1 stk),
  wf_aorder succs entry (PO_a2p po2).
Proof.
  intros.
  assert (J:=@dfs_aux_wf_stack_aux 
                (length (XATree.children_of_tree succs) - 
                 length (XATree.parents_of_tree visited))%nat).
  unfold dfs_aux_wf_stack_prop in J.
  eauto.
Qed.

Lemma dfs_wf_order: forall scs entry pinit po (Hdfs: dfs scs entry pinit = po),
  wf_aorder scs entry (PO_a2p po).
Proof.
  unfold dfs. intros.
  apply dfs_aux_wf_stack with (entry:=entry) in Hdfs; auto.
  split. constructor; auto.
  split. constructor; simpl; auto.
          apply XATree.children_in_children_of_tree.
    intros a1 p1 Hget.   
    rewrite ATree.gempty in Hget. congruence.
Qed.

Definition wf_porder scs (entry:positive): Prop :=
 forall n (Hneq: n <> entry),
   exists p, In p ((XPTree.make_predecessors scs) ??? n) /\ 
   (p > n)%positive.

Lemma asuccs_psuccs_pres_order: forall ascs pscs aentry pentry a2p
  (Htrans: asuccs_psuccs a2p ascs = pscs) (Hwf: wf_aorder ascs aentry a2p)
  (Hentry: a2p ! aentry = Some pentry),
  wf_porder pscs pentry.
Admitted.
 
(*
Program Fixpoint dfs_aux' (succs: ATree.t ls) (todo: ls) 
  {measure (length (XATree.children_of_tree succs))%nat }
  : unit :=
  match todo with
  | nil => tt
  | next::todo' => 
      match succs!!!next with
      | sc::scc' => dfs_aux' (ATree.set next scc' succs) (sc::todo'++[next])
      | nil => dfs_aux' succs todo'
      end
  end.
Next Obligation.
  admit.
Qed.
Next Obligation.
  admit.
Qed.
Next Obligation.
  admit.
Qed.

Definition dfs_aux_wf_stack_prop (n:nat) : Prop := forall (succs: ATree.t ls) 
  (visited: ATree.t unit) 
  (Hp: incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  (Heq: n = (length (XATree.children_of_tree succs) - 
             length (XATree.parents_of_tree visited))%nat)
  todo
  (Hdsf: dfs_aux' succs visited todo Hp = tt), True.

Ltac unfold_dfs_aux' :=
match goal with
| |- appcontext [dfs_aux' ?arg] =>
   unfold dfs_aux'; unfold dfs_aux'_func;
   Program.Wf.WfExtensionality.unfold_sub dfs_aux' arg;
   repeat Program.Wf.fold_sub dfs_aux'_func
(*;
   repeat fold_dfs_aux
*)
end.

Require Import Program.Wf.

Lemma dfs_aux_wf_stack_aux: forall n, dfs_aux_wf_stack_prop n.
Proof.
  induction n.
admit.

    unfold dfs_aux_wf_stack_prop.
    intros until todo.
unfold_dfs_aux'.
simpl.

destruct todo. auto.
destruct (visited ! l0).
destruct R.

fold_sub dfs_aux'_func.

match goal with
| |- appcontext [dfs_aux' ?arg] =>
   unfold dfs_aux'; unfold dfs_aux'_func;
   Program.Wf.WfExtensionality.unfold_sub dfs_aux' arg
(*;
   repeat Program.Wf.fold_sub dfs_aux_func;
   repeat fold_dfs_aux
*)
end.
    simpl.

 match goal with
  | |- appcontext C[Fix_sub _ _ _ _ _ ?arg] =>
       let app := context C [dfs_aux'_func arg] in
       change app
  end.

match goal with
| |- context [dfs_aux_func (existT _ ?a (existT _ _ (existT _ ?b _)))] => 
     fold (dfs_aux a)
end.


   unfold dfs_aux.
   unfold dfs_aux_func.
   WfExtensionality.unfold_sub dfs_aux arg.




    unfold_dfs_aux.

*)
