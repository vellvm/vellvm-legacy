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

Definition stk_in_children succs (stk : list Frame) : Prop :=
List.Forall (fun fr : Frame => 
             incl (Fr_scs fr) (XATree.children_of_tree succs)) stk.

Hint Unfold stk_in_children.

Lemma find_next_visit_in_stk_spec1: forall succs visited (stk : list Frame)
  (Hp : stk_in_children succs stk)  
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
  (Hp : stk_in_children succs stk)
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
  (Hp : stk_in_children succs stk)
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

Program Fixpoint dfs_aux1 (succs: ATree.t ls)
  (visited: ATree.t unit) (po:PostOrder) (stk: list Frame) 
  (Hp: stk_in_children succs stk /\
       incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  {measure 
     (length (XATree.children_of_tree succs) - 
      length (XATree.parents_of_tree visited))%nat }
  : PostOrder :=
  match find_next_visit_in_stk succs visited po stk with
  | inr po' => po'
  | inl (next, stk', po') => dfs_aux1 succs (ATree.set next tt visited) po' stk' _
  end.
Next Obligation.
  split.
    eapply find_next_visit_in_stk_spec1; eauto.
    eapply find_next_visit_in_stk_spec2; eauto.
Qed.
Next Obligation.
  eapply find_next_visit_in_stk_spec3; eauto.
Qed.

(************************)

Fixpoint iter (A:Type) (n:nat) (F:A->A)(g:A) : A :=
  match n with
  | O => g
  | S p => F (iter A p F g)
  end.

Definition dfs_aux_type : Type :=
  forall (succs: ATree.t ls)
  (visited: ATree.t unit) (po:PostOrder) (stk: list Frame),
  PostOrder.

Definition dfs_aux_F (f: dfs_aux_type)
  (succs: ATree.t ls)
  (visited: ATree.t unit) (po:PostOrder) (stk: list Frame) 
  : PostOrder :=
  match find_next_visit_in_stk succs visited po stk with
  | inr po' => po'
  | inl (next, stk', po') => f succs (ATree.set next tt visited) po' stk'
  end.

Require Import cpdt_tactics.

Lemma find_next_visit_in_stk_spec12: forall (succs : ATree.t ls) 
  (visited : ATree.t unit) (po : PostOrder) (stk : list Frame)
  (H : stk_in_children succs stk /\
       incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  next stk' po'
  (Heq_anonymous : inl (next, stk', po') =
                   find_next_visit_in_stk succs visited po stk),
  stk_in_children succs stk' /\
  incl (XATree.parents_of_tree (ATree.set next tt visited))
       (XATree.children_of_tree succs).
Proof.
  intros.
  destruct_conjs.
  split.
    eapply find_next_visit_in_stk_spec1; eauto.
    eapply find_next_visit_in_stk_spec2; eauto.
Qed.

Program Fixpoint dfs_aux_terminates (succs: ATree.t ls)
  (visited: ATree.t unit) (po:PostOrder) (stk: list Frame) 
  (Hp: stk_in_children succs stk /\
       incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  {measure 
     (length (XATree.children_of_tree succs) - 
      length (XATree.parents_of_tree visited))%nat }
  : { po':PostOrder | 
      exists p:nat, 
        forall k, (p < k)%nat ->
        forall g:dfs_aux_type,
          iter _ k dfs_aux_F g succs visited po stk = po' } :=
  match find_next_visit_in_stk succs visited po stk with
  | inr po' => po'
  | inl (next, stk', po') => 
      let _:=dfs_aux_terminates succs (ATree.set next tt visited) po' stk' _ in
      _
  end.
Next Obligation.
  exists O; intros k; case k.
    intros. crush.

    intros k' Hltp g; simpl; unfold dfs_aux_F at 1.
    rewrite <- Heq_anonymous; auto.
Qed.
Next Obligation.
  eapply find_next_visit_in_stk_spec12; eauto.
Qed.
Next Obligation.
  eapply find_next_visit_in_stk_spec3; eauto.
Qed.
Next Obligation.
  case dfs_aux_terminates with (succs0:=succs)
    (visited0:=ATree.set next tt visited)(po:=po')(stk:=stk'); auto with arith.
    eapply find_next_visit_in_stk_spec12; eauto.
    eapply find_next_visit_in_stk_spec3; eauto.

  intros x; intros Hex.
  exists x.
  elim Hex; intros p Heq.
  exists (S p).
  intros k.
  case k.
    intros. crush.
  
    intros k' Hplt g; simpl.
    unfold dfs_aux_F at 1.
    rewrite <- Heq_anonymous; auto with arith.
Qed.

Definition dfs_aux (succs: ATree.t ls)
  (visited: ATree.t unit) (po:PostOrder) (stk: list Frame) 
  (Hp: stk_in_children succs stk /\
       incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  : PostOrder :=
  let (po', _) := dfs_aux_terminates succs visited po stk Hp in po'.

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

Require Import Max.

Lemma dfs_aux_fix_eqn: forall succs visited po stk Hp po1
  (Heq: dfs_aux succs visited po stk Hp = po1),
  match find_next_visit_in_stk succs visited po stk with
  | inr po' => po' = po1
  | inl (next, stk', po') => 
      exists Hp', dfs_aux succs (ATree.set next tt visited) po' stk' Hp' = po1
  end.
Proof.
  unfold dfs_aux.
  intros until po1.
  case (dfs_aux_terminates succs visited po stk Hp).
  intros v Hex1 EQ. subst.
  elim Hex1.
  intros p Heq1.
  caseEq (find_next_visit_in_stk succs visited po stk).
    intros [[next stk'] po'] Hfind.
    eapply find_next_visit_in_stk_spec12 in Hp; eauto.
    exists Hp.
    case (dfs_aux_terminates succs (ATree.set next tt visited) po' stk' Hp).    
    intros v' Hex2.
    elim Hex2. 
    intros p' Heq2.
    rewrite <- Heq1 with (k:=S (S (max p p')))
                         (g:=fun _ _ _ _  =>po).
    rewrite <- Heq2 with (k:=S (max p p'))
                         (g:=fun _ _ _ _ =>po).
      simpl. unfold dfs_aux_F at 3. rewrite Hfind. auto.
      eauto using le_max_l with arith.
      eauto using le_max_r with arith.

    intros po0 Hfind.
    rewrite <- Heq1 with (k:=S p)
                         (g:=fun _ _ _ _  =>po).
      simpl. unfold dfs_aux_F at 1. rewrite Hfind. auto.
      eauto using le_max_l with arith.
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

Definition stk_takes_succs succs (stk : list Frame) : Prop :=
List.Forall (fun fr : Frame => 
             incl (Fr_scs fr) (succs !!! (Fr_name fr))) stk.

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
  (Hp: stk_in_children succs stk /\
       incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  po2 (Hdfs: dfs_aux succs visited po1 stk Hp = po2)
  (Hwf: wf_stack succs entry po1 stk),
  wf_aorder succs entry (PO_a2p po2).

Lemma find_next_visit_in_stk_inl_spec: forall succs visited po stk re
  (Heq: find_next_visit_in_stk succs visited po stk = inl re),
  stk <> nil.
Proof.
  induction stk as [|[v scs] stk]; simpl; intros; congruence.
Qed.

Lemma find_next_visit_in_stk__stk_isa_path: forall succs entry 
  stk (Hwfstk: stk_takes_succs succs stk) visited
  po (Hwf: stk_isa_path succs entry stk) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  stk_isa_path succs entry stk'.
Proof.
  induction 1 as [|[v scs] stk IH]; simpl; intros.
    congruence.

    inv_mbind_app.
      destruct_let.
      uniq_result.
      split; auto.
        apply find_next_visit_in_scs_spec in HeqR.
        destruct_conjs.
        apply IH. apply H. auto with coqlib.
        
      apply IHHwfstk in Heq; auto.
      apply find_next_visit_in_stk_inl_spec in Heq. 
      destruct stk as [|[]]; try congruence. 
        tauto.
Qed.

Lemma find_next_visit_in_stk__stk_takes_succs: forall succs stk visited
  (Hwf: stk_takes_succs succs stk) po next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  stk_takes_succs succs stk'.
Proof.
  induction 1 as [|[v scs] stk IH]; simpl; intros.
    congruence.

    inv_mbind_app; eauto 2.
      destruct_let.
      uniq_result.
      constructor.
        simpl. intro x; auto.
        constructor; auto.
          simpl. intro x; intros Hin. apply IH. simpl.
          apply find_next_visit_in_scs_spec in HeqR.
          destruct_conjs. apply H. auto with coqlib.
Qed.

Lemma node_in_stk_push: forall a2 hd v scs l1 stk
  (Hnd: node_in_stk a2 ({| Fr_name := v; Fr_scs := scs |} :: stk)),
  node_in_stk a2 (hd :: {| Fr_name := v; Fr_scs := l1 |} :: stk).
Proof.
  intros.
  destruct Hnd as [stk1 [stk2 [scs' Hin]]].
  destruct stk1 as [|fr1 stk1].
    inv Hin.
    exists [hd]. exists stk2. exists l1. simpl_env. auto.

    inv Hin.
    exists (hd::{|Fr_name:=v; Fr_scs:=l1|}::stk1). 
    exists stk2. exists scs'. simpl_env. auto.
Qed.

Lemma push_wf_aorder_aux: forall (entry : atom) (succs : ATree.t ls)
  (v : l) (scs : ls) (stk : list Frame) (next : l) (po' : PostOrder) (l1 : ls)
  (Hwf : wf_aorder_aux succs entry po'
           ({| Fr_name := v; Fr_scs := scs |} :: stk)),
  wf_aorder_aux succs entry po'
    ({| Fr_name := next; Fr_scs := succs !!! next |}
     :: {| Fr_name := v; Fr_scs := l1 |} :: stk).
Proof.
  intros.
  intros a1 p1 Hget1.
  apply Hwf in Hget1.
  destruct Hget1 as [J1 J2].
  split; auto.
    intro J3.
    apply J2 in J3.
    destruct J3 as [a2 [J3 J4]].
    exists a2.
    split; auto.
      destruct J4 as [J4 | J4]; auto.
        right. eapply node_in_stk_push; eauto.
Qed.

Lemma node_in_stk_hd: forall Fr_name0 Fr_scs0 stk,
  node_in_stk Fr_name0 ({| Fr_name := Fr_name0; Fr_scs := Fr_scs0 |} :: stk).
Proof.
  exists nil. exists stk. exists Fr_scs0. auto.
Qed.

Lemma node_in_stk_pop: forall a2 v scs fr stk
  (Hin: node_in_stk a2
           ({| Fr_name := v; Fr_scs := scs |}
            :: fr :: stk))
  (Hneq: a2 <> v),
  node_in_stk a2 (fr :: stk).
Proof.
  intros.
  destruct Hin as [stk1 [stk2 [scs' Hin]]].
  destruct stk1 as [|fr1 stk1].
    inv Hin. congruence.

    inv Hin.
    rewrite H1. unfold node_in_stk. eauto.
Qed.

Lemma pop_wf_aorder_aux: forall (entry : atom) (succs : ATree.t ls)
  (v : l) (scs : ls) (Fr_name0 : l) (Fr_scs0 : ls) (stk : list Frame)
  (po : PostOrder) (Hin: In v succs !!! Fr_name0)
  (Hwf0 : wf_aorder_aux succs entry po
           ({| Fr_name := v; Fr_scs := scs |}
            :: {| Fr_name := Fr_name0; Fr_scs := Fr_scs0 |} :: stk)),
  wf_aorder_aux succs entry (postorder_inc po v)
    ({| Fr_name := Fr_name0; Fr_scs := Fr_scs0 |} :: stk).
Proof.
  intros.
  intros a1 p1 Hget.
  destruct po as [cnt a2p].
  simpl in Hget.
  rewrite ATree.gsspec in Hget.
  destruct_if.
    simpl.
    split.
      auto with positive.

      intros.
      exists Fr_name0.
      split.
        apply XATree.make_predecessors_correct; auto.
        right. apply node_in_stk_hd.

     apply Hwf0 in H0.
     simpl in H0.
     destruct H0 as [J1 J2].
     split.
       simpl. auto with positive.
      
       intro J.
       apply J2 in J.
       destruct J as [a2 [J3 J4]].
       destruct (eq_atom_dec a2 v); subst.
         exists v.
         split; auto.
           left. 
           exists cnt.
             simpl.
             rewrite ATree.gss.
             split; auto.
               apply ZC2. auto.

         exists a2.
         split; auto.
           simpl.
           destruct J4 as [[p2 [J4 J5]] | J4].
             left. exists p2.
             split; auto.
               rewrite ATree.gso; auto.

            right. eapply node_in_stk_pop; eauto.
Qed.

Lemma find_next_visit_in_stk__wf_aorder_aux: forall entry succs stk visited
  (Hwf: stk_isa_path succs entry stk)
  po (Hwf: wf_aorder_aux succs entry po stk) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  wf_aorder_aux succs entry po' stk'.
Proof.
  induction stk as [|[v scs] stk]; simpl; intros.
    congruence.

    inv_mbind_app.
      destruct_let.
      uniq_result.
      eapply push_wf_aorder_aux; eauto.

      assert (Hneq:=Heq).
      apply find_next_visit_in_stk_inl_spec in Hneq. 
      destruct stk as [|[]]; try congruence. 
      apply IHstk in Heq; try solve [auto | tauto].
      eapply pop_wf_aorder_aux; try solve [eauto | tauto].
Qed.

Lemma find_next_visit_in_stk__wf_stack: forall entry succs stk visited
  po (Hwf: wf_stack succs entry po stk) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  wf_stack succs entry po' stk'.
Proof.
  intros.
  destruct Hwf as [J1 [J2 J3]]. 
  unfold wf_stack.
  eapply find_next_visit_in_stk__wf_aorder_aux in J3; eauto.
  eapply find_next_visit_in_stk__stk_isa_path in J1; eauto.
  eapply find_next_visit_in_stk__stk_takes_succs in J2; eauto.
Qed.

Lemma node_notin_empty_stk: forall a2 (H:node_in_stk a2 nil), False.
Proof.
  unfold node_in_stk.
  intros.
  destruct_conjs.
  symmetry in H2.
  contradict H2.
  apply app_cons_not_nil.
Qed.

Lemma node_in_single_stk: forall a2 entry scs
  (Hnd: node_in_stk a2 ({| Fr_name := entry; Fr_scs := scs |} :: nil)),
  a2 = entry.
Proof.
  unfold node_in_stk.
  intros.
  destruct_conjs.
  destruct Hnd; inv H1; auto.
    symmetry in H4.
    contradict H4.
    apply app_cons_not_nil.
Qed.

Lemma wf_aorder_aux__find_next_visit_in_stk_inr__wf_aorder: forall 
  succs entry stk po1 (Hwf': stk_isa_path succs entry stk)
  (Hwf : wf_aorder_aux succs entry po1 stk) po2 visited
  (Heq: find_next_visit_in_stk succs visited po1 stk = inr po2),
  wf_aorder succs entry (PO_a2p po2).
Proof.
  induction stk as [|[v scs] stk]; simpl; intros.
    uniq_result.
    intros a1 Hneq p1 Hget1.
    apply Hwf in Hget1; auto.
    destruct Hget1 as [_ Hget1].
    apply Hget1 in Hneq.
    destruct Hneq as [a2 [J1 [[p2 [J2 J3]]|]]].
      eauto.
      apply node_notin_empty_stk in H. tauto.

    inv_mbind_app.
      destruct_let. congruence.
      destruct stk as [|[] stk].
        simpl in Heq. uniq_result.       
        destruct po1. simpl.
        intros a1 Hneq p1 Hget1.
        rewrite ATree.gso in Hget1; auto.
        apply Hwf in Hget1; auto.
        simpl in Hget1.
        destruct Hget1 as [G Hget1].
        apply Hget1 in Hneq.
        destruct Hneq as [a2 [J1 [[p2 [J2 J3]]|J2]]].
          destruct (eq_atom_dec a2 entry); subst.      
            exists entry. exists PO_cnt0.
            rewrite ATree.gss.   
            repeat (split; auto).
              apply ZC2. auto.
        
            exists a2. exists p2.
            split; auto.
              rewrite ATree.gso; auto.
            
          apply node_in_single_stk in J2. subst.
          exists entry. exists PO_cnt0.
          rewrite ATree.gss.   
          repeat (split; auto).
            apply ZC2. auto.

        apply IHstk in Heq; try solve [auto | tauto].
        eapply pop_wf_aorder_aux; try solve [eauto | tauto].
Qed.

Lemma wf_stack__find_next_visit_in_stk_inr__wf_aorder: forall succs entry po1 stk
  (Hwf : wf_stack succs entry po1 stk) po2 visited
  (Heq: find_next_visit_in_stk succs visited po1 stk = inr po2),
  wf_aorder succs entry (PO_a2p po2).
Proof.
  intros.
  destruct Hwf as [J1 [J2 J3]].
  eapply wf_aorder_aux__find_next_visit_in_stk_inr__wf_aorder; eauto.
Qed.

Lemma dfs_aux_wf_stack_aux: forall n, dfs_aux_wf_stack_prop n.
Proof.
  intros.
  elim n using (well_founded_induction lt_wf).
  unfold dfs_aux_wf_stack_prop.
  intros x IH. intros.
  apply dfs_aux_fix_eqn in Hdfs.
  caseEq (find_next_visit_in_stk succs visited po1 stk).
    intros [[next stk'] po'] Hfind; fill_holes_in_ctx.
    destruct Hdfs as [Hp' Hdfs].
    eapply IH with (y:=
      (length (XATree.children_of_tree succs) -
       length (XATree.parents_of_tree (ATree.set next tt visited)))%nat) 
      in Hdfs; eauto.
      subst.  
      symmetry in Hfind.
      destruct_conjs.
      eapply find_next_visit_in_stk_spec3 in Hfind; eauto. 

      eapply find_next_visit_in_stk__wf_stack; eauto. 

    intros p Hfind; fill_holes_in_ctx.
    subst.
    eapply wf_stack__find_next_visit_in_stk_inr__wf_aorder; eauto.
Qed.

Lemma dfs_aux_wf_stack: forall (succs: ATree.t ls) entry
  (visited: ATree.t unit) (po1:PostOrder) (stk: list Frame) 
  (Hp: stk_in_children succs stk /\
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
  split. 
    constructor; simpl; auto.
      intro x. auto.

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
 
(************************)

Require Import Dipaths.

Section VertexArc.

Variable successors: ATree.t (list atom).

Definition vertexes' : V_set :=
fun (v:Vertex) => let '(index n) := v in XATree.in_cfg successors n.

Definition arcs' : A_set :=
fun (arc:Arc) =>
  let '(A_ends (index n2) (index n1)) := arc in
  In n2 (successors!!!n1).

Definition reachable' entry av : Prop :=
  exists vl: V_list, exists al: A_list, D_walk vertexes' arcs' av entry vl al.

End VertexArc.

Lemma dfs_reachable: forall scs entry pinit po (Hdfs: dfs scs entry pinit = po),
  forall l0, 
  ~ reachable' scs (index entry) (index l0) <-> (PO_a2p po) ! l0 = None.
Admitted.

