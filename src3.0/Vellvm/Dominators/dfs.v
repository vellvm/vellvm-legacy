Require Export Coqlib.
Require Export Maps.
Require Import syntax.
Require Import infrastructure_props.
Require Import Metatheory.
Require Import Program.Tactics.
Require Import dom_libs.

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

Lemma ATree_set_pres_nonempty: forall (n : atom) visited 
  (Hin : visited ! n <> None) next,
  (ATree.set next tt visited) ! n <> None.
Proof.
  intros.
  rewrite ATree.gsspec.
  destruct_if; congruence.
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

(**********************************************************)

Import LLVMsyntax.

Record Frame := mkFrame {
  Fr_name: l;
  Fr_scs: ls
}.

(**********************************************************)

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

Lemma find_next_visit_in_scs_spec': forall visited scs sc scs'
  (Hfind : Some (sc, scs') = find_next_visit_in_scs visited scs),
  exists scs0,
    scs = scs0 ++ sc::scs' /\ 
    (forall sc0 (Hin: In sc0 scs0), ATree.get sc0 visited <> None) /\
    ATree.get sc visited = None.
Proof.
  induction scs as [|sc scs]; simpl; intros.
    congruence.

    inv_mbind_app.
      apply IHscs in Hfind.
      destruct Hfind as [scs0 Hfind].
      destruct_pairs. subst.
      exists (sc::scs0). 
      repeat (split; eauto with datatypes v62).
        intros sc1 Hin. 
        destruct_in Hin; eauto.
          congruence.
        
      uniq_result.
      exists nil. repeat (split; eauto with datatypes v62).
Qed.

Lemma find_next_visit_in_scs_spec: forall visited scs sc scs'
  (Hfind : Some (sc, scs') = find_next_visit_in_scs visited scs),
  incl (sc::scs') scs /\ ATree.get sc visited = None.
Proof.
  intros.
  apply find_next_visit_in_scs_spec' in Hfind.
  destruct_conjs. subst.
  split; eauto 2 with datatypes v62.
Qed.

(**********************************************************)

Record PostOrder := mkPO {
  PO_cnt: positive;
  PO_a2p: ATree.t positive
}.

Definition postorder_inc (po:PostOrder) (v:l) : PostOrder :=
let '(mkPO cnt a2p) := po in
mkPO (Psucc cnt) (ATree.set v cnt a2p).

Lemma postorder_inc_pres_nonempty: forall po n' n
  (Hnempty: (PO_a2p po) ! n <> None),
  (PO_a2p (postorder_inc po n')) ! n <> None.
Proof.
  destruct po. simpl.
  intros.
  rewrite ATree.gsspec.
  destruct_if. congruence.
Qed.

Lemma postorder_inc_eq: forall po n,
  (PO_a2p (postorder_inc po n)) ! n = Some (PO_cnt po).
Proof.
  destruct po; simpl.
  intros.
  rewrite ATree.gss; auto.
Qed.

Lemma postorder_inc_neq: forall po m n (Hneq: m <> n),
  (PO_a2p (postorder_inc po m)) ! n = (PO_a2p po) ! n.
Proof.
  destruct po; simpl.
  intros.
  rewrite ATree.gso; auto.
Qed.

Lemma postorder_inc_lt: forall po a,
  (PO_cnt po < PO_cnt (postorder_inc po a))%positive.
Proof.
  destruct po. simpl. intro. auto with positive.
Qed.

(*************************************************************)

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

Lemma find_next_visit_in_stk_inl_spec: forall succs visited po stk re
  (Heq: find_next_visit_in_stk succs visited po stk = inl re),
  stk <> nil.
Proof.
  induction stk as [|[v scs] stk]; simpl; intros; congruence.
Qed.

Lemma find_next_visit_in_scs_none_spec: forall visited sc scs 
  (Hfind : None = find_next_visit_in_scs visited scs) (Hin: In sc scs),
  ATree.get sc visited <> None.
Proof.
  induction scs as [|sc0 scs]; simpl; intros.
    congruence.

    destruct Hin as [Hin | Hin]; subst.
      intro J.
      rewrite J in Hfind. congruence.

      inv_mbind_app; eauto.
        congruence.
Qed.

(**************************************************)

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

(************************)

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

(*************************************************************)

Definition node_in_stk (a2:atom) (stk:list Frame) : Prop :=
exists stk1, exists stk3, exists scs2, stk = stk1 ++ mkFrame a2 scs2  :: stk3.

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

Lemma node_in_stk_cons_inv: forall n hd stk
  (Hnd: node_in_stk n (hd :: stk)),
  n = Fr_name hd \/ node_in_stk n stk.
Proof.
  unfold node_in_stk.
  intros.
  destruct Hnd as [A [B [C Hnd]]].
  destruct A as [|A]; inv Hnd; eauto.
Qed.

(*************************************************************)

Module Inv. Section Inv.

Variable wf_stack: ATree.t ls -> ATree.t unit -> PostOrder -> list Frame -> Prop.

Hypothesis find_next_visit_in_stk__wf_stack: forall succs stk visited
  po (Hwf: wf_stack succs visited po stk) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  wf_stack succs (ATree.set next tt visited) po' stk'.

Variable wf_po: ATree.t ls -> PostOrder -> Prop.

Hypothesis wf_stack__find_next_visit_in_stk_inr__wf_order: forall succs 
  stk visited po1 (Hwf : wf_stack succs visited po1 stk) po2 
  (Heq: find_next_visit_in_stk succs visited po1 stk = inr po2),
  wf_po succs po2.

Definition dfs_aux_wf_prop (n:nat) : Prop := 
  forall (succs: ATree.t ls) 
  (visited: ATree.t unit) 
  (Heq: n = (length (XATree.children_of_tree succs) - 
             length (XATree.parents_of_tree visited))%nat)
  (po1:PostOrder) (stk: list Frame) 
  (Hp: stk_in_children succs stk /\
       incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  po2 (Hdfs: dfs_aux succs visited po1 stk Hp = po2)
  (Hwf: wf_stack succs visited po1 stk),
  wf_po succs po2.

Lemma dfs_aux_wf_aux: forall n, dfs_aux_wf_prop n.
Proof.
  intros.
  elim n using (well_founded_induction lt_wf).
  unfold dfs_aux_wf_prop.
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

    intros p Hfind; fill_holes_in_ctx.
    subst.
    eapply wf_stack__find_next_visit_in_stk_inr__wf_order; eauto.
Qed.

Lemma dfs_aux_wf: forall (succs: ATree.t ls) 
  (visited: ATree.t unit) (po1:PostOrder) (stk: list Frame) 
  (Hp: stk_in_children succs stk /\
       incl (XATree.parents_of_tree visited) (XATree.children_of_tree succs))
  po2 (Hdsf: dfs_aux succs visited po1 stk Hp = po2)
  (Hwf: wf_stack succs visited po1 stk),
  wf_po succs po2.
Proof.
  intros.
  assert (J:=@dfs_aux_wf_aux 
                (length (XATree.children_of_tree succs) - 
                 length (XATree.parents_of_tree visited))%nat).
  unfold dfs_aux_wf_prop in J.
  eauto.
Qed.

Variable succs: ATree.t ls.
Variable entry: l.
Variable pinit: positive.

Hypothesis entry_wf_stack: 
  wf_stack succs (ATree.empty unit)
    {| PO_cnt := pinit; PO_a2p := ATree.empty positive |}
    [{| Fr_name := entry; Fr_scs := succs !!! entry |}].

Lemma dfs_wf: forall po 
  (Hdfs: dfs succs entry pinit = po), wf_po succs po. 
Proof.
  unfold dfs. intros.
  apply dfs_aux_wf in Hdfs; auto.
Qed.

End Inv. End Inv.

(*************************************************************)

Module Order.

Fixpoint stk_isa_path (succs: ATree.t ls) (entry:atom) (stk:list Frame) : Prop :=
match stk with
| nil => True
| mkFrame v _::nil => v = entry
| mkFrame sc _::(mkFrame n _::_) as stk' => 
    In sc (succs !!! n) /\ stk_isa_path succs entry stk'
end.

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

Definition wf_stack (entry:atom) (succs: ATree.t ls) (po:PostOrder) 
  (stk: list Frame) : Prop :=
stk_isa_path succs entry stk /\
stk_takes_succs succs stk /\
wf_aorder_aux succs entry po stk.

Definition wf_aorder (entry:atom) scs (a2p:ATree.t positive) : Prop :=
  forall a1 (Hneq: a1 <> entry) p1 (Hget: a2p ! a1 = Some p1),
  exists a2, exists p2,
    In a2 ((XATree.make_predecessors scs) !!! a1) /\ 
    a2p ! a2 = Some p2 /\ (p2 > p1)%positive.

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
  po (Hwf: wf_stack entry succs po stk) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  wf_stack entry succs po' stk'.
Proof.
  intros.
  destruct Hwf as [J1 [J2 J3]]. 
  unfold wf_stack.
  eapply find_next_visit_in_stk__wf_aorder_aux in J3; eauto.
  eapply find_next_visit_in_stk__stk_isa_path in J1; eauto.
  eapply find_next_visit_in_stk__stk_takes_succs in J2; eauto.
Qed.

Lemma wf_aorder_aux__find_next_visit_in_stk_inr__wf_aorder: forall 
  succs entry stk po1 (Hwf': stk_isa_path succs entry stk)
  (Hwf : wf_aorder_aux succs entry po1 stk) po2 visited
  (Heq: find_next_visit_in_stk succs visited po1 stk = inr po2),
  wf_aorder entry succs (PO_a2p po2).
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
  (Hwf : wf_stack entry succs po1 stk) po2 visited
  (Heq: find_next_visit_in_stk succs visited po1 stk = inr po2),
  wf_aorder entry succs (PO_a2p po2).
Proof.
  intros.
  destruct Hwf as [J1 [J2 J3]].
  eapply wf_aorder_aux__find_next_visit_in_stk_inr__wf_aorder; eauto.
Qed.

Lemma entry_wf_stack: forall scs entry pinit,
  wf_stack entry scs {| PO_cnt := pinit; PO_a2p := ATree.empty positive |}
     [{| Fr_name := entry; Fr_scs := scs !!! entry |}].
Proof.
  intros.
  split. constructor; auto.
  split. 
    constructor; simpl; auto.
      intro x. auto.
    intros a1 p1 Hget.   
    rewrite ATree.gempty in Hget. congruence.
Qed.

Lemma dfs_wf_order: forall scs entry pinit po (Hdfs: dfs scs entry pinit = po),
  wf_aorder entry scs (PO_a2p po).
Proof.
  intros.
  eapply Inv.dfs_wf with 
    (wf_stack:=fun succs visited po stk => wf_stack entry succs po stk)
    (wf_po:=fun succs po => wf_aorder entry succs (PO_a2p po)); 
    eauto using wf_stack__find_next_visit_in_stk_inr__wf_aorder,
                find_next_visit_in_stk__wf_stack, entry_wf_stack.
Qed.

Definition wf_porder scs (entry:positive): Prop :=
 forall n (Hneq: n <> entry),
   exists p, In p ((XPTree.make_predecessors scs) ??? n) /\ 
   (p > n)%positive.

Lemma asuccs_psuccs_pres_order: forall ascs pscs aentry pentry a2p
  (Htrans: asuccs_psuccs a2p ascs = pscs) (Hwf: wf_aorder aentry ascs a2p)
  (Hentry: a2p ! aentry = Some pentry),
  wf_porder pscs pentry.
Admitted. (* asuccs_psuccs *)
 
Lemma dfs_wf_porder: forall ascs aentry pinit po (Hdfs: dfs ascs aentry pinit = po)
  pentry pscs (Htrans: asuccs_psuccs (PO_a2p po) ascs = pscs) 
  (Hentry: (PO_a2p po) ! aentry = Some pentry),
  wf_porder pscs pentry.
Proof.
  intros.
  eapply asuccs_psuccs_pres_order; eauto.
  eapply dfs_wf_order; eauto.
Qed.

End Order.

(************************)

Require Import Dipaths.

Section VertexArc.

Variable successors: ATree.t (list atom).

Definition vertexes : V_set :=
fun (v:Vertex) => let '(index n) := v in XATree.in_cfg successors n.

Definition arcs : A_set :=
fun (arc:Arc) =>
  let '(A_ends (index n2) (index n1)) := arc in
  In n2 (successors!!!n1).

Definition reachable entry av : Prop :=
  exists vl: V_list, exists al: A_list, D_walk vertexes arcs av entry vl al.

Lemma reachable_succ: forall (entry : ATree.elt) 
  (fr : l) (next : l) (H1 : reachable (index entry) (index fr))
  (Hscs : In next successors !!! fr),
  reachable (index entry) (index next).
Proof.
  intros.
  destruct H1 as [vl [al Hwk]].
  exists (index fr::vl). exists (A_ends (index next) (index fr)::al).
  apply DW_step; auto.
    apply XATree.in_succ__in_cfg with (p:=fr); auto.
Qed.

Lemma reachable_entry: forall (entry : ATree.elt) 
  (Hincfg: XATree.in_cfg successors entry),
  reachable (index entry) (index entry).
Proof.
  intros.
  exists V_nil. exists A_nil. 
  constructor; auto.
Qed.

End VertexArc.

(************************)

Module ReachableEntry. 

Definition wf_stack entry (po:PostOrder) (stk: list Frame) : Prop :=
  (exists others, exists esuccs, 
     stk = others ++ [mkFrame entry esuccs]) \/
  (PO_a2p po) ! entry <> None.

Definition wf_order entry (po:PostOrder) : Prop :=
  (PO_a2p po) ! entry <> None.

Lemma pop__wf_stack: forall (entry : l) (fr : l) (todo : ls)
  (stk : list Frame) (po1 : PostOrder)
  (Hwf : wf_stack entry po1 ({| Fr_name := fr; Fr_scs := todo |} :: stk)),
  wf_stack entry (postorder_inc po1 fr) stk.
Proof.
  unfold wf_stack.
  intros.
  destruct Hwf as [Hwf | Hwf].
  SCase "1".
    destruct Hwf as [others [esuccs Hwf]].
    destruct others as [|F others]; inv Hwf; eauto.
      rewrite postorder_inc_eq. right. congruence. 
  SCase "2".
    right. apply postorder_inc_pres_nonempty; auto.
Qed.

Lemma find_next_visit_in_stk__wf_stack: forall succs entry stk visited
  po (Hwf: wf_stack entry po stk) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  wf_stack entry po' stk'.
Proof.
  unfold wf_stack.
  induction stk as [|[fr todo] stk]; simpl; intros.
    congruence.

    inv_mbind_app.
    Case "push".
      destruct_let. uniq_result.
      destruct Hwf as [Hwf | Hwf]; auto.
        left. 
        destruct Hwf as [others [esuccs Hwf]].
        destruct others as [|F others]; inv Hwf. 
          simpl_env. eauto.
          exists ({| Fr_name := next; Fr_scs := succs !!! next |}::
                  {| Fr_name := fr; Fr_scs := l1 |}::others).
          exists esuccs. simpl_env. auto.     

    Case "pop".
      apply IHstk in Heq; auto.
        eapply pop__wf_stack; eauto.
Qed.

Lemma wf_stack__find_next_visit_in_stk_inr__wf_aorder: forall succs entry stk po1
  (Hwf : wf_stack entry po1 stk) po2 visited
  (Heq: find_next_visit_in_stk succs visited po1 stk = inr po2),
  wf_order entry po2.
Proof.
  induction stk as [|[fr todo] stk]; simpl; intros.
    uniq_result. 
    destruct Hwf as [|]; auto.
    destruct_conjs. uniq_result'. inv H2.
    
    inv_mbind_app.
      destruct_let. congruence.
      apply IHstk in Heq; auto.
        eapply pop__wf_stack; eauto.
Qed.

Lemma entry_wf_stack: forall scs entry pinit,
  wf_stack entry {| PO_cnt := pinit; PO_a2p := ATree.empty positive |}
     [{| Fr_name := entry; Fr_scs := scs !!! entry |}].
Proof.
  intros.
  left. exists nil. exists scs!!!entry. auto.
Qed.

Lemma dfs_wf: forall scs entry pinit po 
  (Hdfs: dfs scs entry pinit = po), (PO_a2p po) ! entry <> None.
Proof.
  intros.
  eapply Inv.dfs_wf with 
    (wf_stack:=fun succs visited po stk => wf_stack entry po stk)
    (wf_po:=fun succs po => wf_order entry po); 
    eauto using wf_stack__find_next_visit_in_stk_inr__wf_aorder,
                find_next_visit_in_stk__wf_stack, entry_wf_stack.
Qed.
 
End ReachableEntry. 

(************************)

Require Import Program.Equality.

Module ReachableSucc. 

Definition succ_of_numbered_is_visited_or_numbered (succs: ATree.t ls)
  (visited: ATree.t unit) (po:PostOrder): Prop :=
  forall n sc (Hnn: (PO_a2p po) ! n <> None) (Hinsc: In sc (succs !!! n)),
    visited ! sc <> None \/ (PO_a2p po) ! sc <> None.

Definition visited_is_numbered_or_stked (visited: ATree.t unit) (po:PostOrder) 
  (stk: list Frame) : Prop :=
  forall n (Hvisited: visited ! n <> None),
    (PO_a2p po) ! n <> None \/ node_in_stk n stk.

Definition wf_succs_of_fr succs (visited: ATree.t unit) (po:PostOrder) 
  (fr : Frame) : Prop :=
forall sc (Hin: In sc (succs !!! (Fr_name fr))),
  visited ! sc <> None \/ (PO_a2p po) ! sc <> None \/ In sc (Fr_scs fr).

Definition wf_succs_of_stk succs (visited: ATree.t unit) (po:PostOrder) 
  (stk : list Frame): Prop :=
List.Forall (wf_succs_of_fr succs visited po) stk.

Definition wf_stack (succs: ATree.t ls) (visited: ATree.t unit) (po:PostOrder) 
  (stk: list Frame) : Prop :=
  succ_of_numbered_is_visited_or_numbered succs visited po /\
  visited_is_numbered_or_stked visited po stk /\
  wf_succs_of_stk succs visited po stk.

Lemma pushed__wf_succs_of_fr: forall succs visited po next,
  wf_succs_of_fr succs visited po 
    {| Fr_name := next; Fr_scs := succs !!! next |}.
Proof.
  intros. intros n Hin. simpl. auto.
Qed.

Hint Unfold wf_succs_of_fr.

Lemma wf_succs_of_stk__postorder_inc: forall n succs visited po stk
  (Hwf: wf_succs_of_stk succs visited po stk),
  wf_succs_of_stk succs visited (postorder_inc po n) stk.
Proof.
  unfold wf_succs_of_stk.
  intros.
  dependent induction Hwf; auto.
    constructor; auto.
      autounfold. intros.
      apply H in Hin.
      destruct Hin as [Hin | [Hin | Hin]]; auto.
        right. left.
        eapply postorder_inc_pres_nonempty in Hin; eauto.
Qed.

Lemma wf_succs_of_stk__visited_inc: forall next succs visited po stk
  (Hwf: wf_succs_of_stk succs visited po stk),
  wf_succs_of_stk succs (ATree.set next tt visited) po stk.
Proof.
  unfold wf_succs_of_stk.
  intros.
  dependent induction Hwf; auto.
    constructor; auto.
      autounfold. intros.
      apply H in Hin.
      destruct Hin as [Hin | [Hin | Hin]]; auto.
        left. apply ATree_set_pres_nonempty; auto.
Qed.

Lemma find_next_visit_in_stk__wf_succs_of_stk: forall succs stk visited po
  (Hwf: wf_succs_of_stk succs visited po stk) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  wf_succs_of_stk succs (ATree.set next tt visited) po' stk'.
Proof.
  induction stk as [|[fr todo] stk]; simpl; intros.
  Case "base".
    congruence.

  Case "ind".
    inv_mbind_app.
    SCase "push".
      destruct_let. uniq_result.
      inv Hwf.
      constructor.
      SSCase "new fr".
        apply pushed__wf_succs_of_fr.
      constructor.
      SSCase "old hd".
        apply find_next_visit_in_scs_spec' in HeqR.
        destruct HeqR as [scs0 [J1 [J2 J3]]]; subst.
        intros n Hin. 
        apply H1 in Hin.
        destruct Hin as [Hin | [Hin | Hin]]; auto.
        SSSCase "1".
          left. apply ATree_set_pres_nonempty; auto.
        SSSCase "2".
          simpl in Hin. simpl.
          destruct_in Hin.
            left. apply ATree_set_pres_nonempty; auto.
          destruct_in Hin.
            left. rewrite ATree.gss. congruence.
      SSCase "old tl".
        apply wf_succs_of_stk__visited_inc; auto.

    SCase "pop".
      apply IHstk in Heq; auto.
        inv Hwf.
        apply wf_succs_of_stk__postorder_inc; auto.
Qed.

Lemma find_next_visit_in_scs_none__succ_of_numbered_is_visited_or_numbered: 
  forall (succs : ATree.t ls) (visited : ATree.t unit) (po : PostOrder)
  (fr : l) (todo : ls) (stk : list Frame) 
  (J1 : succ_of_numbered_is_visited_or_numbered succs visited po)
  (J3 : wf_succs_of_fr succs visited po {| Fr_name := fr; Fr_scs := todo |})
  (Hnone : None = find_next_visit_in_scs visited todo),
  succ_of_numbered_is_visited_or_numbered succs visited
     (postorder_inc po fr).
Proof.
  intros.
  intros n sc Hnn Hinsc.
  destruct po. simpl in *.
  destruct (eq_atom_dec fr n); subst.
  SCase "fr = n".
    apply J3 in Hinsc.
    destruct Hinsc as [Hinsc | Hinsc]; auto.
    destruct Hinsc as [Hinsc | Hinsc].
    SSCase "1.1.1".
      rewrite ATree.gss in Hnn.
      right.
      rewrite ATree.gsspec.
      destruct_if.
  
    SSCase "1.1.2".
      eapply find_next_visit_in_scs_none_spec in Hnone; eauto.
  
  SCase "fr <> n".
    rewrite ATree.gso in Hnn; auto.
    apply J1 in Hinsc; auto.
    destruct Hinsc as [Hinsc | Hinsc]; auto.
    simpl in Hinsc.
    right.
    rewrite ATree.gsspec.
    destruct_if. congruence.
Qed.

Lemma find_next_visit_in_stk__succ_of_numbered_is_visited_or_numbered: 
  forall succs stk visited po
  (Hwf': wf_succs_of_stk succs visited po stk)
  (Hwf: succ_of_numbered_is_visited_or_numbered succs visited po) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  succ_of_numbered_is_visited_or_numbered succs (ATree.set next tt visited) po'.
Proof.
  induction stk as [|[fr todo] stk]; simpl; intros.
  Case "base".
    congruence.

  Case "ind".
    inv_mbind_app.
    SCase "push".
      destruct_let. uniq_result.
      intros n sc Hnn Hinsc.
      apply Hwf in Hinsc; auto.
      destruct Hinsc as [Hinsc | Hinsc]; auto.
        left. apply ATree_set_pres_nonempty; auto.

    SCase "pop".
      inv Hwf'.
      apply IHstk in Heq; auto.
        apply wf_succs_of_stk__postorder_inc; auto.
        eapply find_next_visit_in_scs_none__succ_of_numbered_is_visited_or_numbered;
          eauto.
Qed.

Lemma visited_is_numbered_or_stked__postorder_inc: forall 
  (visited : ATree.t unit) (po : PostOrder) (fr : l) (todo : ls)
  (stk : list Frame)
  (J2 : visited_is_numbered_or_stked visited po
         ({| Fr_name := fr; Fr_scs := todo |} :: stk)),
  visited_is_numbered_or_stked visited (postorder_inc po fr) stk.
Proof.
  intros.
  intros n Hnv.
  apply J2 in Hnv.
  destruct Hnv as [Hnv | Hnv].
  SCase "2.1".
    left. apply postorder_inc_pres_nonempty; auto.
  SCase "2.2".
    apply node_in_stk_cons_inv in Hnv.
    destruct Hnv as [Hinv | Hinv]; subst; auto.
      simpl. left.
      rewrite postorder_inc_eq. congruence.        
Qed.

Lemma find_next_visit_in_stk__visited_is_numbered_or_stked: 
  forall succs stk visited po
  (Hwf: visited_is_numbered_or_stked visited po stk) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  visited_is_numbered_or_stked (ATree.set next tt visited) po' stk'.
Proof.
  induction stk as [|[fr todo] stk]; simpl; intros.
  Case "base".
    congruence.

  Case "ind".
    inv_mbind_app.
    SCase "push".
      destruct_let. uniq_result.
      intros n Hinv.
      rewrite ATree.gsspec in Hinv.
      destruct_if; subst.
      SSCase "1".
        right. apply node_in_stk_hd.
      SSCase "2".
        apply Hwf in Hinv.
        destruct Hinv as [Hinv | Hinv]; auto.
        eapply node_in_stk_push in Hinv; eauto.

    SCase "pop".
      apply IHstk in Heq; auto.
        eapply visited_is_numbered_or_stked__postorder_inc; eauto.
Qed.

Lemma find_next_visit_in_stk__wf_stack: forall succs stk visited
  po (Hwf: wf_stack succs visited po stk) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  wf_stack succs (ATree.set next tt visited) po' stk'.
Proof.
  intros.
  destruct Hwf as [J1 [J2 J3]]. 
  unfold wf_stack.
  eapply find_next_visit_in_stk__succ_of_numbered_is_visited_or_numbered 
    in J1; eauto.
  eapply find_next_visit_in_stk__visited_is_numbered_or_stked in J2; eauto.
  eapply find_next_visit_in_stk__wf_succs_of_stk in J3; eauto.
Qed.

Lemma find_next_visit_in_scs_none__wf_stack: forall succs visited po fr todo stk
  (Hwf : wf_stack succs visited po ({| Fr_name := fr; Fr_scs := todo |} :: stk))
  (po2 : PostOrder)
  (Hnone : None = find_next_visit_in_scs visited todo),
  wf_stack succs visited (postorder_inc po fr) stk.
Proof.
  intros. 
  destruct Hwf as [J1 [J2 J3]]. 
  split.
    inv J3.
    eapply find_next_visit_in_scs_none__succ_of_numbered_is_visited_or_numbered;
      eauto.
  split.
    eapply visited_is_numbered_or_stked__postorder_inc; eauto.
    inv J3. apply wf_succs_of_stk__postorder_inc; auto.    
Qed.

Definition wf_order (succs: ATree.t ls) (po:PostOrder) : Prop :=
  forall n sc (Hnn: (PO_a2p po) ! n <> None) (Hinsc: In sc (succs !!! n)),
    (PO_a2p po) ! sc <> None.

Lemma wf_stack__find_next_visit_in_stk_inr__wf_order: forall succs 
  stk visited po1 (Hwf : wf_stack succs visited po1 stk) po2 
  (Heq: find_next_visit_in_stk succs visited po1 stk = inr po2),
  wf_order succs po2.
Proof.
  induction stk as [|[fr todo] stk]; simpl; intros.
  Case "base".
    uniq_result.
    destruct Hwf as [J1 [J2 J3]].
    intros n sc Hnn Hinsc.
    apply J1 in Hinsc; auto.
    destruct Hinsc as [Hinsc | Hinsc]; auto.
    apply J2 in Hinsc.
    destruct Hinsc as [Hinsc | Hinsc]; auto.
    apply node_notin_empty_stk in Hinsc. tauto.

  Case "ind".
    inv_mbind_app.
      destruct_let. congruence.
     
      eapply IHstk; eauto using find_next_visit_in_scs_none__wf_stack.
Qed.

Lemma entry_wf_stack: forall scs entry pinit,
  wf_stack scs (ATree.empty unit)
    {| PO_cnt := pinit; PO_a2p := ATree.empty positive |}
    [{| Fr_name := entry; Fr_scs := scs !!! entry |}].
Proof.
  intros.
  split. 
    intros n' sc' Hnn' Hinsc'. 
    simpl in Hnn'.
    rewrite ATree.gempty in Hnn'. congruence.
  split. 
    intros n' Hv'.
    rewrite ATree.gempty in Hv'. congruence.
      
           constructor; auto.
Qed.

Lemma dfs_wf: forall scs entry pinit po 
  (Hdfs: dfs scs entry pinit = po) n sc (Hnn: (PO_a2p po) ! n <> None)
  (Hinsc: In sc scs!!!n), (PO_a2p po) ! sc <> None.
Proof.
  intros until 1.
  eapply Inv.dfs_wf with (wf_stack:=wf_stack)(wf_po:=wf_order) in Hdfs; 
    eauto using wf_stack__find_next_visit_in_stk_inr__wf_order,
                find_next_visit_in_stk__wf_stack, entry_wf_stack.
Qed.

End ReachableSucc. 

(************************)

Module NumberedAreReachable. 

Definition frame_is_reachable entry (succs: ATree.t ls) (fr: Frame) := 
  reachable succs (index entry) (index (Fr_name fr)).

Hint Unfold frame_is_reachable. 

Definition frames_are_reachable entry (succs: ATree.t ls) (stk: list Frame) := 
  List.Forall (frame_is_reachable entry succs) stk.

Definition wf_order entry succs po : Prop :=
  forall n (Hnn: (PO_a2p po) ! n <> None), 
    reachable succs (index entry) (index n).

Definition wf_stack entry (succs: ATree.t ls) (po:PostOrder) 
  (stk: list Frame) : Prop :=
  Order.stk_takes_succs succs stk /\
  frames_are_reachable entry succs stk /\
  wf_order entry succs po.

Lemma find_next_visit_in_stk__frames_are_reachable: 
  forall entry succs stk visited po
  (Hpath: Order.stk_takes_succs succs stk)
  (Hwf: frames_are_reachable entry succs stk) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  frames_are_reachable entry succs stk'.
Proof.
  induction stk as [|[fr todo] stk]; simpl; intros.
    congruence.

    inv Hwf. inv Hpath. simpl in *.
    inv_mbind_app; eauto.
      destruct_let. uniq_result.
        constructor.
          assert (In next succs !!! fr) as Hscs.
            apply find_next_visit_in_scs_spec in HeqR.
            destruct_conjs. auto with coqlib.
          simpl.
          eapply reachable_succ; eauto.
        constructor; auto.
Qed.

Lemma wf_order__postorder_inc: forall entry succs po fr
  (Hreach: frame_is_reachable entry succs fr)
  (Hwf : wf_order entry succs po),
  wf_order entry succs (postorder_inc po (Fr_name fr)).
Proof.
  intros. intros n Hnn.
  destruct po. simpl in *.
  rewrite ATree.gsspec in Hnn.
  destruct_if; subst; auto.
Qed.

Lemma find_next_visit_in_stk__wf_order: 
  forall entry succs stk visited po
  (Hwf': frames_are_reachable entry succs stk)
  (Hwf: wf_order entry succs po) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  wf_order entry succs po'.
Proof.
  induction stk as [|[fr todo] stk]; simpl; intros.
    congruence.

    inv_mbind_app.
    Case "push".
      destruct_let. uniq_result. auto.
    Case "pop".
      inv Hwf'.
      eapply wf_order__postorder_inc in H1; eauto.
Qed.

Lemma find_next_visit_in_stk__wf_stack: forall entry succs stk visited
  po (Hwf: wf_stack entry succs po stk) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  wf_stack entry succs po' stk'.
Proof.
  intros.
  destruct Hwf as [J0 [J1 J2]]. 
  unfold wf_stack.
  eapply find_next_visit_in_stk__wf_order in J2; eauto.
  eapply find_next_visit_in_stk__frames_are_reachable in J1; eauto.
  eapply Order.find_next_visit_in_stk__stk_takes_succs in J0; eauto.
Qed.

Lemma wf_stack__find_next_visit_in_stk_inr__wf_order: forall entry succs 
  stk visited po1 (Hwf : wf_stack entry succs po1 stk) po2 
  (Heq: find_next_visit_in_stk succs visited po1 stk = inr po2),
  wf_order entry succs po2.
Proof.
  unfold wf_stack.
  induction stk as [|[fr todo] stk]; simpl; intros.
    uniq_result. tauto.

    inv_mbind_app.
      destruct_let. congruence.

      apply IHstk in Heq; auto.      
        destruct Hwf as [Hwf1 [Hwf2 Hwf3]].
        inv Hwf1. inv Hwf2.
        split; auto.
        split; auto.
          eapply wf_order__postorder_inc in H3; eauto.
Qed.

Lemma entry_wf_stack: forall scs entry pinit
  (Hincfg: XATree.in_cfg scs entry),
  wf_stack entry scs
    {| PO_cnt := pinit; PO_a2p := ATree.empty positive |}
    [{| Fr_name := entry; Fr_scs := scs !!! entry |}].
Proof.
  intros.
  split. 
    constructor; auto.
      intro x. auto.
  split.
    constructor; auto.
      apply reachable_entry; auto.
    intros n Hnn. simpl in Hnn.
    rewrite ATree.gempty in Hnn. congruence.
Qed.

Lemma dfs_wf: forall scs entry pinit po 
  (Hincfg: XATree.in_cfg scs entry)
  (Hdfs: dfs scs entry pinit = po) n (Hnn: (PO_a2p po) ! n <> None),
  reachable scs (index entry) (index n).
Proof.
  intros until 2.
  eapply Inv.dfs_wf with 
    (wf_stack:=fun scs v po stk=>wf_stack entry scs po stk)
    (wf_po:=wf_order entry) in Hdfs; 
    eauto using wf_stack__find_next_visit_in_stk_inr__wf_order,
                find_next_visit_in_stk__wf_stack, entry_wf_stack.
Qed.

End NumberedAreReachable. 

(************************)

Lemma dfs_reachable_complete: forall scs entry pinit po 
  (Hdfs: dfs scs entry pinit = po) l0
  (Hreach: reachable scs (index entry) (index l0)),
  (PO_a2p po) ! l0 <> None.
Proof.
  unfold reachable.
  intros.
  destruct Hreach as [vl [al Hreach]].
  dependent induction Hreach.
    eapply ReachableEntry.dfs_wf; eauto.

    destruct y as [y].
    eapply ReachableSucc.dfs_wf with (n:=y); eauto.
Qed.

Lemma dfs_reachable_sound: forall scs entry pinit po 
  (Hincfg: XATree.in_cfg scs entry)
  (Hdfs: dfs scs entry pinit = po) l0
  (Hnn: (PO_a2p po) ! l0 <> None),
  reachable scs (index entry) (index l0).
Proof.
  intros.
  eapply NumberedAreReachable.dfs_wf; eauto.
Qed.

Lemma dfs_unreachable_iff_get_none: forall scs entry pinit po 
  (Hdfs: dfs scs entry pinit = po) (Hincfg: XATree.in_cfg scs entry),
  forall l0, 
  ~ reachable scs (index entry) (index l0) <-> (PO_a2p po) ! l0 = None.
Proof.
  intros.
  split; intro J.
    remember (PO_a2p po) ! l0 as R.
    destruct R; auto.
    contradict J.
    eapply dfs_reachable_sound; try solve [eauto | congruence].

    intro G.
    eapply dfs_reachable_complete in G; eauto.
Qed.

Lemma dfs_reachable_iff_get_some: forall scs entry pinit po 
  (Hdfs: dfs scs entry pinit = po) (Hincfg: XATree.in_cfg scs entry),
  forall l0, 
  reachable scs (index entry) (index l0) <-> exists p, (PO_a2p po) ! l0 = Some p.
Proof.
  intros.
  split; intro J.
    eapply dfs_reachable_complete in J; eauto.
    destruct (PO_a2p po)!l0; eauto. congruence.

    destruct_conjs.
    eapply dfs_reachable_sound; try solve [eauto | congruence].
Qed.

(************************)

Module Injective. 

Definition a2p_injective po : Prop :=
  forall (p:positive) a1 a2
  (Hget2 : (PO_a2p po) ! a2 = Some p) (Hget1 : (PO_a2p po) ! a1 = Some p),
  a1 = a2.

Definition a2p_lt_cnt po : Prop :=
  forall p a (Hget: (PO_a2p po) ! a = Some p), (p < PO_cnt po)%positive.

Definition wf_order po : Prop :=
  a2p_lt_cnt po /\ a2p_injective po. 

Lemma a2p_injective__postorder_inc: forall po fr (Hlt: a2p_lt_cnt po)
  (Hinj: a2p_injective po),
  a2p_injective (postorder_inc po fr).
Proof.
  intros.
  intros p a1 a2 Hget2 Hget1.
  destruct (eq_atom_dec fr a2); subst.
    rewrite postorder_inc_eq in Hget2. uniq_result.
    destruct (eq_atom_dec a2 a1); subst; auto.
    rewrite postorder_inc_neq in Hget1; auto.
    apply Hlt in Hget1. contradict Hget1. apply Plt_irrefl.

    rewrite postorder_inc_neq in Hget2; auto.
    destruct (eq_atom_dec fr a1); subst.
      rewrite postorder_inc_eq in Hget1. uniq_result.
      apply Hlt in Hget2. contradict Hget2. apply Plt_irrefl.
 
      rewrite postorder_inc_neq in Hget1; auto.
      eapply Hinj; eauto.
Qed.

Lemma a2p_lt_cnt__postorder_inc: forall po fr (Hlt: a2p_lt_cnt po),
  a2p_lt_cnt (postorder_inc po fr).
Proof.
  intros.
  intros p a Hget.
  destruct (eq_atom_dec fr a); subst.
    rewrite postorder_inc_eq in Hget. uniq_result.
    apply postorder_inc_lt.

    rewrite postorder_inc_neq in Hget; auto.
    apply Hlt in Hget.
    assert (J:=postorder_inc_lt po fr).
    eapply Plt_trans; eauto.
Qed.

Lemma find_next_visit_in_stk__a2p_injective: 
  forall succs stk visited po (Hwf: a2p_injective po) (Hlt: a2p_lt_cnt po) 
  next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  a2p_injective po'.
Proof.
  induction stk as [|[fr todo] stk]; simpl; intros.
    congruence.

    inv_mbind_app.
    Case "push".
      destruct_let. uniq_result. auto.
    Case "pop".
      apply IHstk in Heq; auto using a2p_injective__postorder_inc,
                                     a2p_lt_cnt__postorder_inc.
Qed.

Lemma find_next_visit_in_stk__a2p_lt_cnt: 
  forall succs stk visited po (Hlt: a2p_lt_cnt po) 
  next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  a2p_lt_cnt po'.
Proof.
  induction stk as [|[fr todo] stk]; simpl; intros.
    congruence.

    inv_mbind_app.
    Case "push".
      destruct_let. uniq_result. auto.
    Case "pop".
      apply IHstk in Heq; auto using a2p_lt_cnt__postorder_inc.
Qed.

Lemma find_next_visit_in_stk__wf_order: forall succs stk visited
  po (Hwf: wf_order po) next stk' po'
  (Heq: find_next_visit_in_stk succs visited po stk = inl (next, stk', po')),
  wf_order po'.
Proof.
  intros.
  destruct Hwf as [J1 J2]. 
  unfold wf_order.
  eapply find_next_visit_in_stk__a2p_injective in J2; eauto.
  eapply find_next_visit_in_stk__a2p_lt_cnt in J1; eauto.
Qed.

Lemma wf_order__find_next_visit_in_stk_inr__wf_order: forall succs 
  stk visited po1 (Hwf : wf_order po1) po2 
  (Heq: find_next_visit_in_stk succs visited po1 stk = inr po2),
  wf_order po2.
Proof.
  unfold wf_order.
  induction stk as [|[fr todo] stk]; simpl; intros.
    uniq_result. tauto.

    inv_mbind_app.
      destruct_let. congruence.

      destruct Hwf as [Hwf1 Hwf2].
      apply IHstk in Heq; auto using a2p_injective__postorder_inc,
                                     a2p_lt_cnt__postorder_inc.
Qed.

Lemma entry_wf_order: forall pinit,
  wf_order
    {| PO_cnt := pinit; PO_a2p := ATree.empty positive |}.
Proof.
  intros.
  split.
    intros p a Hget. rewrite ATree.gempty in Hget. congruence.
    intros p a1 a2 Hget1 Hget2. rewrite ATree.gempty in Hget1. congruence.
Qed.

Lemma dfs_wf: forall scs entry pinit po 
  (Hdfs: dfs scs entry pinit = po), wf_order po.
Proof.
  intros.
  eapply Inv.dfs_wf with 
    (wf_stack:=fun scs v po stk=>wf_order po)
    (wf_po:=fun scs po=>wf_order po) in Hdfs; 
    eauto using wf_order__find_next_visit_in_stk_inr__wf_order,
                find_next_visit_in_stk__wf_order, entry_wf_order.
Qed.

Lemma dfs_inj: forall scs entry pinit po 
  (Hdfs: dfs scs entry pinit = po) (p:positive) a1 a2
  (Hget2 : (PO_a2p po) ! a2 = Some p) (Hget1 : (PO_a2p po) ! a1 = Some p),
  a1 = a2.
Proof.
  intros.
  apply dfs_wf in Hdfs.
  destruct Hdfs as [_ J].
  eapply J; eauto.
Qed.

End Injective. 

