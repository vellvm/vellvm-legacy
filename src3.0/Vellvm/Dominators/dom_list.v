Require Export Coqlib.
Require Export Iteration.
Require Export Maps.
Require Import syntax.
Require Import infrastructure_props.
Require Import infrastructure.
Require Import Metatheory.
Require Import Program.Tactics.
Require Import dom_libs.
Require Import dfs.
Require Import push_iter.

(***************************************************)

Require Import Dipaths.
Require Import infrastructure.
Import LLVMsyntax.

Lemma getEntryLabel__getEntryBlock: forall f le,
  LLVMinfra.getEntryLabel f = Some le ->
  exists be, LLVMinfra.getEntryBlock f = Some be /\ 
             LLVMinfra.label_of_block be = le.
Admitted. (* infra *)

Definition a2p_Vertex (a2p:ATree.t positive) (av: Vertex) (pv : Vertex) :=
let '(index a) := av in
let '(index p) := pv in
a2p ! a = Some p.

Definition a2p_V_list (a2p:ATree.t positive) (avl: V_list) (pvl : V_list) :=
List.Forall2 (a2p_Vertex a2p) avl pvl.

Definition a2p_Arc (a2p:ATree.t positive) (aa: Arc) (pa : Arc) :=
let '(A_ends av1 av2) := aa in
let '(A_ends pv1 pv2) := pa in
a2p_Vertex a2p av1 pv1 /\ a2p_Vertex a2p av2 pv2.

Definition a2p_A_list (a2p:ATree.t positive) (aal: A_list) (pal : A_list) :=
List.Forall2 (a2p_Arc a2p) aal pal.

Lemma in_vertexes__get_a2p: forall a2p asuccs pv,
  vertexes (asuccs_psuccs a2p asuccs) pv ->
  exists av, a2p_Vertex a2p av pv.
Admitted. (* asuccs_psuccs *)

Lemma a2p_vertexes: forall a2p asuccs pv av,
  a2p_Vertex a2p av pv ->
  (vertexes (asuccs_psuccs a2p asuccs) pv <-> dfs.vertexes asuccs av).
Admitted. (* asuccs_psuccs *)

Lemma a2p_arcs: forall a2p asuccs pv1 av1 pv2 av2,
  a2p_Vertex a2p av1 pv1 ->
  a2p_Vertex a2p av2 pv2 ->
  (arcs (asuccs_psuccs a2p asuccs) (A_ends pv1 pv2) <->
    dfs.arcs asuccs (A_ends av1 av2)).
Admitted. (* asuccs_psuccs *)

Lemma In__a2p_V_list: forall p pvl a avl a2p
  (J: a2p_V_list a2p avl pvl)
  (Hget: a2p ! a = Some p), 
  In (index p) pvl <-> In (index a) avl.
Admitted. (* asuccs_psuccs *)

Lemma get_a2p_in_a2p_cfg: forall (p : positive) a a2p (Hget: a2p ! a = Some p) 
  asuccs,
  in_cfg (asuccs_psuccs a2p asuccs) p.
Admitted. (* asuccs_psuccs *)

Lemma a2p_D_walk: forall a2p asuccs pv1 pv2 (pvl : V_list) (pal : A_list) 
  (Hwk: D_walk (vertexes (asuccs_psuccs a2p asuccs))
               (arcs (asuccs_psuccs a2p asuccs)) 
               pv1 pv2 pvl pal),
  exists avl, exists aal, exists av1, exists av2,
    D_walk (dfs.vertexes asuccs) (dfs.arcs asuccs) av1 av2 avl aal /\
    a2p_Vertex a2p av1 pv1 /\ a2p_Vertex a2p av2 pv2 /\
    a2p_V_list a2p avl pvl /\ a2p_A_list a2p aal pal.
Proof.
  intros.
  induction Hwk.
    exists V_nil. exists A_nil.
    assert (J:=H).
    apply in_vertexes__get_a2p in J.
    destruct J as [av J].
    exists av. exists av.
    split.
      constructor. 
        eapply a2p_vertexes; eauto.
    split; auto.
    split; auto.
    split; constructor.

    destruct IHHwk as [avl [aal [av1 [av2 [J1 [J2 [J3 [J4 J5]]]]]]]].
    assert (J:=H).
    apply in_vertexes__get_a2p in J.
    destruct J as [av J].
    exists (av1::avl). exists (A_ends av av1::aal).
    exists av. exists av2.
    split.
      constructor; auto.
        eapply a2p_vertexes; eauto.
        eapply a2p_arcs; eauto.
    split; auto.
    split; auto.
    split.
      constructor; auto.
      constructor; simpl; auto.
Qed.

Lemma p2a_D_walk: forall av1 av2 avl aal a2p asuccs
  (Hreach: forall a, dfs.reachable asuccs av2 (index a) <-> 
                     exists p, a2p ! a = Some p)
  (Hwk: D_walk (dfs.vertexes asuccs) (dfs.arcs asuccs) av1 av2 avl aal),
  exists pvl, exists pal, exists pv1, exists pv2,
    D_walk (vertexes (asuccs_psuccs a2p asuccs))
           (arcs (asuccs_psuccs a2p asuccs)) 
           pv1 pv2 pvl pal /\
    a2p_Vertex a2p av1 pv1 /\ a2p_Vertex a2p av2 pv2 /\
    a2p_V_list a2p avl pvl /\ a2p_A_list a2p aal pal.
Proof.
  intros.
  induction Hwk.
    destruct x as [x]. 
    assert (dfs.reachable asuccs (index x) (index x)) as Hr. 
      apply reachable_entry; auto.
    apply Hreach in Hr.
    destruct Hr as [p Hr].
    exists V_nil. exists A_nil.
    exists (index p). exists (index p).
    split.
      constructor. 
        eapply a2p_vertexes; eauto. 
          simpl. auto.
    split; auto.
    split; auto.
    split; constructor.

    destruct IHHwk as [avl [aal [av1 [av2 [J1 [J2 [J3 [J4 J5]]]]]]]]; auto.
    destruct x as [x]. 
    assert (dfs.reachable asuccs z (index x)) as Hr. 
      destruct z as [z]. destruct y as [y].
      eapply reachable_succ with (fr:=y); eauto.
      unfold dfs.reachable. eauto.
    apply Hreach in Hr.
    destruct Hr as [p Hr].
    exists (av1::avl). exists (A_ends (index p) av1::aal).
    exists (index p). exists av2.
    split.
      constructor; auto.
        eapply a2p_vertexes; eauto.
          simpl. auto.
        eapply a2p_arcs; eauto.
          simpl. auto.
    split; auto.
    split; auto.
    split.
      constructor; auto.
      constructor; simpl; auto.
Qed.


Require Import dom_type.

Ltac fill_holes_in_ctx :=
let fill e H :=
  match goal with
  | H1: _ = e |- _ => rewrite <- H1 in H
  | H1: e = _ |- _ => rewrite H1 in H
  end 
in
let fill' e :=
  match goal with
  | H1: _ = e |- _ => rewrite <- H1
  | H1: e = _ |- _ => rewrite H1
  end
in
repeat match goal with
| H: context [match ?e with
     | Some _ => _
     | None => _
     end] |- _ => fill e H
| H: context [match ?e with
     | inl _ => _
     | inr _ => _
     end] |- _ => fill e H
| H: context [match ?e with
     | (_,_) => _
     end] |- _ => fill e H
| H: context [match ?e with
     | (_,_) => _
     end] |- _ => fill e H
| |- context [match ?e with
     | Some _ => _
     | None => _
     end] => fill' e
end.

Import AtomSet.
Import LLVMinfra.

Lemma getEntryBlock__getEntryLabel: forall f be,
  getEntryBlock f = Some be ->
  getEntryLabel f = Some (label_of_block be).
Proof.
  destruct f as [? bs]. simpl.
  destruct bs as [|[]]; simpl; intros.
    congruence.
    uniq_result. simpl. auto.
Qed.

Lemma getEntryBlock__getEntryLabel_none: forall f,
  getEntryBlock f = None <->
  getEntryLabel f = None.
Proof.
  destruct f as [? bs]. simpl.
  destruct bs as [|[]]; simpl; intros; split; try solve [auto | congruence].
Qed.

Lemma in_parents__in_bound_fdef: forall f n 
  (Hparents: In n (XATree.parents_of_tree (cfg.successors f))), 
  In n (cfg.bound_fdef f).
Proof.
  destruct f.
  intros.
  apply cfg.in_parents__in_bound; auto.
Qed.

Lemma in_pparents__in_aparents: forall (a : atom) (p : positive) a2p
  (Hget : a2p ! a = Some p) asuccs
  (Heq : In p (XPTree.parents_of_tree (asuccs_psuccs a2p asuccs))),
  In a (XATree.parents_of_tree asuccs).
Admitted.

Lemma le_in_cfg: forall f le
  (Hentry: LLVMinfra.getEntryLabel f = Some le),
  XATree.in_cfg (cfg.successors f) le.
Admitted. (* asuccs_psuccs *)

Lemma in_pcfg__in_bound_fdef: forall a p a2p (Hl2p : a2p ! a = Some p) f
  (Hin : in_cfg (asuccs_psuccs a2p (cfg.successors f)) p),
  ListSet.set_In a (cfg.bound_fdef f).
Admitted.

Lemma entry_in_pcfg: forall f a p a2p (Hentry: getEntryLabel f = Some a)
  (Hl2p : a2p ! a = Some p),
  in_cfg (asuccs_psuccs a2p (cfg.successors f)) p.
Admitted.

Lemma dfs_inj': forall scs entry pinit po 
  (Hdfs: dfs scs entry pinit = po) (p1 p2:positive) a1 a2 (Hneq: a1 <> a2)
  (Hget2 : (PO_a2p po) ! a2 = Some p1) (Hget1 : (PO_a2p po) ! a1 = Some p2),
  p1 <> p2.
Proof.
  intros.
  intros EQ. subst.
  apply Hneq.
  eapply Injective.dfs_inj; eauto.
Qed.

Lemma entry_in_cfg: forall entry f (Hentry: getEntryLabel f = Some entry),
  ListSet.set_In entry (cfg.bound_fdef f).
Admitted.

Lemma vertexes_conv: forall f,
  cfg.vertexes_fdef f = dfs.vertexes (cfg.successors f).
Admitted.

Lemma arcs_conv: forall f,
  cfg.arcs_fdef f = dfs.arcs (cfg.successors f).
Admitted.

Section adom_pdom.

Variable f:fdef.
Definition asuccs := cfg.successors f.
Variable PO: PostOrder.
Variable le: l.
Hypothesis Hentry: LLVMinfra.getEntryLabel f = Some le.

Hypothesis Hdfs: dfs (cfg.successors f) le 1 = PO.

Lemma unreachable__get_a2p: forall l2,
  ~ cfg.reachable f l2 <-> (PO_a2p PO) ! l2 = None.
Proof.
  intros.
  apply dfs_unreachable_iff_get_none with (l0:=l2) in Hdfs; 
    auto using le_in_cfg.
  apply getEntryLabel__getEntryBlock in Hentry.
  destruct Hentry as [be [Hentry' EQ]]; subst. 
  unfold cfg.reachable. rewrite Hentry'.
  unfold dfs.reachable in Hdfs. destruct be as [le ? ? ?].
  simpl in Hdfs.
  rewrite vertexes_conv. rewrite arcs_conv. auto.
Qed.

Lemma reachable__get_a2p: forall l2,
  cfg.reachable f l2 <-> exists p2, (PO_a2p PO) ! l2 = Some p2.
Proof.
  intros.
  apply dfs_reachable_iff_get_some with (l0:=l2) in Hdfs; 
    auto using le_in_cfg.
  apply getEntryLabel__getEntryBlock in Hentry.
  destruct Hentry as [be [Hentry' EQ]]; subst. 
  unfold cfg.reachable. rewrite Hentry'.
  unfold dfs.reachable in Hdfs. destruct be as [le ? ? ?].
  simpl in Hdfs.
  rewrite vertexes_conv. rewrite arcs_conv. auto.
Qed.

Lemma a2p_domination: forall (l1 l2 : l) (p1 p2 : positive)
  (Hreach: forall a,
           dfs.reachable asuccs (index le) (index a) <->
           exists p : positive, (PO_a2p PO) ! a = Some p)
  (Hget1: Some p1 = (PO_a2p PO) ! l1) (Hget2: Some p2 = (PO_a2p PO) ! l2) pe
  (Hget2: Some pe = (PO_a2p PO) ! le) 
  (Hdom: domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2),
  cfg.domination f l1 l2.
Proof.
  intros.
  unfold cfg.domination. 
  assert (Hentry':=Hentry).
  apply getEntryLabel__getEntryBlock in Hentry'.
  destruct Hentry' as [be [Hentry' EQ]]; subst le.
  rewrite Hentry'. destruct be as [le ? ? ?]. simpl in *.
  unfold domination in Hdom.
  intros vl al Hwk.
  rewrite vertexes_conv in Hwk.
  rewrite arcs_conv in Hwk.
  apply p2a_D_walk with (a2p:=PO_a2p PO) in Hwk; auto.
    destruct Hwk as [pvl [pal [[p1'] [[p2'] [Hwk [J1 [J2 [J3 J4]]]]]]]].
    simpl in J1, J2. symmetry_ctx. uniq_result.
    apply Hdom in Hwk.
    destruct Hwk as [Hin | Heq]; subst.
      eapply In__a2p_V_list in Hin; eauto.
      right. eapply Injective.dfs_inj; eauto.
Qed.

Require dom_decl.

Lemma p2a_strict_domination: forall (l1 l2 : l)
  (Hreach2: cfg.reachable f l2)
  (Hsdom: cfg.strict_domination f l1 l2),
  exists p1, exists p2, exists pe, 
    strict_domination (asuccs_psuccs (PO_a2p PO) asuccs) pe p1 p2 /\
    (PO_a2p PO) ! l1 = Some p1 /\ (PO_a2p PO) ! l2 = Some p2 /\
    (PO_a2p PO) ! le = Some pe.
Proof.
  intros.
  assert (Hentry':=Hentry).
  apply getEntryLabel__getEntryBlock in Hentry'.
  destruct Hentry' as [be [Hentry' EQ]]; subst le.
  destruct be as [le ? ? ?]. simpl in *.
  assert (cfg.reachable f l1) as Hreach1.
    eapply dom_decl.DecDom.sdom_reachable; eauto.
  assert (cfg.reachable f le) as Hreachle.
    eapply reach.reachable_entrypoint; eauto.
  apply reachable__get_a2p in Hreach1.
  apply reachable__get_a2p in Hreach2.
  apply reachable__get_a2p in Hreachle.
  destruct Hreach1 as [p1 Hget1].
  destruct Hreach2 as [p2 Hget2].
  destruct Hreachle as [pe Hgetle].
  exists p1. exists p2. exists pe.
  split.
  Case "1".
    unfold cfg.strict_domination, cfg.domination,
           strict_domination, domination in *.
    destruct Hsdom as [Hsdom Hneq]. 
    rewrite Hentry' in Hsdom. 
    split.
    SCase "1.1".
      intros vl al Hwk.
      apply a2p_D_walk in Hwk.
      destruct Hwk as [avl [aal [[a1] [[a2] [Hwk [J1 [J2 [J3 J4]]]]]]]].
      simpl in *.
      eapply Injective.dfs_inj in Hget2; eauto. subst.
      eapply Injective.dfs_inj in Hgetle; eauto. subst.
      unfold asuccs in Hwk.
      rewrite <- vertexes_conv in Hwk.
      rewrite <- arcs_conv in Hwk.
      apply Hsdom in Hwk.
      destruct Hwk as [Hin | Heq]; subst.
        eapply In__a2p_V_list in Hin; eauto.
        right. uniq_result. auto.
    SCase "1.2".
      intro EQ. subst.
      eapply Injective.dfs_inj in Hget2; eauto.
  Case "2".
    split; auto.
Qed.

End adom_pdom.

Lemma p2a_reachable: forall a2p f pe p3 le l3
  (Hreach: reachable (asuccs_psuccs a2p (cfg.successors f)) pe p3)
  (Hentry: getEntryLabel f = Some le)
  (Hgete: a2p ! le = Some pe)
  (Hget3: a2p ! l3 = Some p3),
  cfg.reachable f l3.
Admitted.

Lemma a2p_reachable: forall a2p f pe p3 le l3
  (Hreach: cfg.reachable f l3)
  (Hentry: getEntryLabel f = Some le)
  (Hgete: a2p ! le = Some pe)
  (Hget3: a2p ! l3 = Some p3),
  reachable (asuccs_psuccs a2p (cfg.successors f)) pe p3.
Admitted.

Lemma areachable__preachable: forall le pe l3 p3 f a2p
  (Hpentry : a2p ! le = Some pe) (Hget3 : a2p ! l3 = Some p3)
  (Hreach3 : dfs.reachable (cfg.successors f) (index le) (index l3)),
  reachable (asuccs_psuccs a2p (cfg.successors f)) pe p3.
Admitted.

Lemma preachable__qreachable: forall le pe l3 p3 f a2p
  (Hpentry : a2p ! le = Some pe) (Hget3 : a2p ! l3 = Some p3)
  (Hreach3 : reachable (asuccs_psuccs a2p (cfg.successors f)) pe p3),
  dfs.reachable (cfg.successors f) (index le) (index l3).
Admitted.

Lemma in_asuccs__in_psuccs: forall l' l3 p3 p' f a2p
 (Hinscs : In l' (cfg.successors f) !!! l3)
 (Hget3 : a2p ! l3 = Some p3) (Hget' : a2p ! l' = Some p'),
 In p' (asuccs_psuccs a2p (cfg.successors f)) ??? p3.
Admitted.

Lemma reachable_isnt_bot: forall (l3 : l) f (res : PMap.t LDoms.t) 
  (a2p : ATree.t positive) (p3 : positive) (le : l) (pe : positive)
  (Hpentry : a2p ! le = Some pe)
  (H0 : pdom_analyze (asuccs_psuccs a2p (cfg.successors f)) pe = res)
  (Hget3 : a2p ! l3 = Some p3)
  (Hreach3 : dfs.reachable (cfg.successors f) (index le) (index l3))
  (Hwf_porder : Order.wf_porder (asuccs_psuccs a2p (cfg.successors f)) pe),
  exists dts3 : list positive, res ?? p3 = Some dts3.
Proof.
  intros.
  apply DomSound.reachable_isnt_bot with (n:=p3) in Hwf_porder.
    simpl in Hwf_porder. rewrite H0 in Hwf_porder.
    unfold LDoms.bot in Hwf_porder.
    destruct (res ?? p3); eauto. congruence.

    eapply areachable__preachable; eauto.      
Qed.

Definition dom_analyze (f: fdef) : PMap.t LDoms.t * ATree.t positive :=
  let asuccs := cfg.successors f in
  match LLVMinfra.getEntryLabel f with
  | Some le =>
      let '(mkPO _ a2p) := dfs asuccs le 1%positive in
      let psuccs := asuccs_psuccs a2p asuccs in
      match ATree.get le a2p with
      | Some pe => (pdom_analyze psuccs pe, a2p)
      | None => (PMap.init LDoms.top, ATree.empty _)
      end
  | None => (PMap.init LDoms.top, ATree.empty _)
  end.

Module AlgDom' : ALGDOM.

Import LLVMsyntax.

Definition dom_analysis_is_successful (f: fdef) : Prop :=
  let asuccs := cfg.successors f in
  match LLVMinfra.getEntryLabel f with
  | Some le =>
      let '(mkPO _ a2p) := dfs asuccs le 1%positive in
      let psuccs := asuccs_psuccs a2p asuccs in
      match ATree.get le a2p with
      | Some pe => pdom_analysis_is_successful psuccs pe
      | None => False
      end
  | None => False
  end.

Definition a2p_p2a (a2p:ATree.t positive) : PTree.t l :=
  ATree.fold (fun acc from to => PTree.set to from acc) a2p (PTree.empty l).

Definition ps2as (p2a: PTree.t l) (ps: list positive) : list l :=
  List.fold_left (fun acc p => 
                  match p2a ? p with
                  | Some a => a::acc
                  | None => acc
                  end) ps nil.

Lemma in_ps__in_ps2as: forall a p a2p (Hget: a2p ! a = Some p) ps
  (Hin : In p ps),
  ListSet.set_In a (ps2as (a2p_p2a a2p) ps).
Admitted.

Lemma in_ps2as__in_ps: forall (a : atom) a2p ps
  (Hin : In a (ps2as (a2p_p2a a2p) ps)),
  exists p, a2p ! a = Some p /\ In p ps.
Admitted.

Definition p2a_dom p2a bd (res: LDoms.t) : list atom :=
match res with
| Some dts2 => ps2as p2a dts2
| None => bd
end.

Definition bound_dom (a2p:ATree.t positive) p2a bd (res: PMap.t LDoms.t) 
  (l0:atom) : list atom :=
match a2p ! l0 with
| Some p0 => p2a_dom p2a bd (res ?? p0)
| None => bd
end.

Definition dom_query f : atom -> list atom :=
let '(dt, a2p) := dom_analyze f in
let b := cfg.bound_fdef f in
let p2a := a2p_p2a a2p in
bound_dom a2p p2a b dt.

Ltac simpl_dom_query :=
match goal with
| Hentry : getEntryBlock ?f = Some _ |- _ =>
  apply getEntryBlock__getEntryLabel in Hentry; simpl in Hentry
| Hentry : getEntryBlock _ = None |- _ =>
  unfold dom_query, dom_analyze, bound_dom;
  apply getEntryBlock__getEntryLabel_none in Hentry;
  rewrite Hentry
| H: dom_analysis_is_successful ?f |- _ =>
  unfold dom_analysis_is_successful in H;
  let Hentry:=fresh "Hentry" in
  let le:=fresh "le" in
  case_eq (getEntryLabel f); 
    try solve [intro Hentry; rewrite Hentry in H; tauto];
  intros le Hentry
| _ => idtac
end;
match goal with
| Hentry : getEntryLabel ?f = Some ?le |- _ =>
  unfold dom_query, dom_analyze, bound_dom;
  fill_holes_in_ctx;
  case_eq (dfs (cfg.successors f) le 1);
  intros PO_cnt PO_a2p Hdfs;
  assert (Hdfs_entry:=Hdfs);
  apply ReachableEntry.dfs_wf in Hdfs_entry;
  simpl in Hdfs_entry;
  case_eq (PO_a2p ! le); try solve [intros; congruence];
  intros pe Hl2p;
  fill_holes_in_ctx;
  try rewrite Hdfs in *; try rewrite Hl2p in *
| _ => idtac
end.

Lemma dom_entrypoint : forall f l0 ps cs tmn
  (Hentry : getEntryBlock f = Some (block_intro l0 ps cs tmn)),
  dom_query f l0 = nil.
Proof.
  intros. 
  simpl_dom_query.
  rewrite DomSound.adom_entrypoint.
  simpl. unfold ps2as. auto.
Qed.

Lemma pmember__aset_in: forall (f : fdef) a a2p p (Hl2p : a2p ! a = Some p)
  dt (Hin : member (asuccs_psuccs a2p (cfg.successors f)) p dt),
  ListSet.set_In a (p2a_dom (a2p_p2a a2p) (cfg.bound_fdef f) dt).
Proof.
  intros.
  unfold member in Hin.
  unfold p2a_dom.
  destruct dt; simpl.
    eapply in_ps__in_ps2as; eauto.
    eapply in_pcfg__in_bound_fdef; eauto.
Qed.

Section entry_doms_others.

Variable f:fdef.

Lemma entry_doms_others: forall entry
  (Hex: dom_analysis_is_successful f)
  (H: getEntryLabel f = Some entry),
  (forall b (H0: b <> entry /\ cfg.reachable f b),
     ListSet.set_In entry (dom_query f b)).
Proof.
  intros.
  destruct H0 as [J1 J2].
  unfold dom_analysis_is_successful in Hex.
  simpl_dom_query.
  case_eq (PO_a2p ! b).
  Case "1".
    intros p Hsome.  
    unfold pdom_analysis_is_successful in Hex.
    unfold pdom_analyze.
    remember (DomDS.fixpoint (asuccs_psuccs PO_a2p (cfg.successors f))
              LDoms.transfer ((pe, LDoms.top) :: nil)) as R.
    destruct R; try tauto.
    symmetry in HeqR.
    apply EntryDomsOthers.fixpoint_wf_doms in HeqR; auto.
    SCase "1".
      unfold EntryDomsOthers.wf_doms in HeqR.
      assert (p <> pe) as Hneq.
        eapply dfs_inj' with (p1:=p)(p2:=pe)(a1:=entry)(a2:=b) in Hdfs; 
          simpl; eauto.
      apply HeqR in Hneq.
      eapply pmember__aset_in; eauto.
    SCase "2".
      eapply entry_in_pcfg; eauto.
    SCase "3".
      eapply Order.dfs_wf_porder in Hdfs; eauto.
  Case "2".
    intros Hnone. apply entry_in_cfg; auto.
Qed.

End entry_doms_others.

Lemma dom_in_bound: forall successors le t
  (Hfix: DomDS.fixpoint successors LDoms.transfer
            ((le, LDoms.top) :: nil) = Some t),
  forall l0 ns0 (Hget: t ?? l0 = Some ns0) n (Hin: In n ns0),
    In n (XPTree.parents_of_tree successors).
Proof.
  intros.
  apply DomsInParents.fixpoint_wf in Hfix; auto.
  assert (J:=Hfix l0).
  unfold DomsInParents.wf_dom in J.
  rewrite Hget in J. auto.
Qed.

Lemma dom_query_in_bound': forall f l5, 
  incl (dom_query f l5) (cfg.bound_fdef f).
Proof.
  intros.
  case_eq (getEntryBlock f).
  Case "1".
    intros [le ? ? ?] Hentry.
    simpl_dom_query.
    case_eq (PO_a2p ! l5).
    SCase "1.1".
      intros p Hsome. 
      unfold pdom_analyze.
      case_eq (DomDS.fixpoint (asuccs_psuccs PO_a2p (cfg.successors f))
            LDoms.transfer ((pe, LDoms.top) :: nil)).
      SSCase "1.1.1".
        intros t Heq.
        case_eq (t ??p); simpl.
        SSSCase "1.1.1.1".
          intros ps Hget. 
          intros a Hin.
          apply in_parents__in_bound_fdef.
          apply in_ps2as__in_ps in Hin.
          destruct Hin as [p' [Hget' Hin]].
          eapply dom_in_bound in Heq; eauto.
          eapply in_pparents__in_aparents; eauto.
        SSSCase "1.1.1.2".
          intros Hget. auto with datatypes v62.
      SSCase "1.1.2".
        intros Heq.
        unfold bound_dom.
        rewrite PMap.gi. unfold ps2as. simpl.
        intros x Hinx. tauto.
    SCase "1.2".
      intros Hnone. auto with datatypes v62.
  Case "2".
    intros Hnone.
    simpl_dom_query.

    rewrite ATree.gempty. auto with datatypes v62.
Qed.

Lemma dom_query_in_bound: forall fh bs l5, 
  incl (dom_query (fdef_intro fh bs) l5) (cfg.bound_blocks bs).
Proof.
  intros. apply dom_query_in_bound'.
Qed.

Lemma dom_successors : forall
  (l3 : l) (l' : l) f
  (contents3 contents': ListSet.set atom)
  (Hinscs : In l' (cfg.successors f) !!! l3)
  (Heqdefs3 : contents3 = dom_query f l3)
  (Heqdefs' : contents' = dom_query f l'),
  incl contents' (l3 :: contents3).
Proof.
  intros. 
  assert (Hinbd': incl contents' (cfg.bound_fdef f)).
    subst. apply dom_query_in_bound'.
  unfold dom_query in *.
  case_eq (dom_analyze f).
  intros res a2p Hdoma.
  rewrite Hdoma in *.
  unfold dom_analyze, bound_dom in *.
  remember (getEntryLabel f) as R.
  destruct f as [fh bs].
  destruct R as [le|].
  Case "entry is good".
    case_eq (dfs (cfg.successors (fdef_intro fh bs)) le 1).
    intros cnt a2p' Hdfs.
    rewrite Hdfs in *.
    assert (Hdfs_entry:=Hdfs).
    apply ReachableEntry.dfs_wf in Hdfs_entry.
    simpl in Hdfs_entry.
    case_eq (a2p' ! le); try solve [intros; congruence].
    intros pe Hpentry.
    rewrite Hpentry in *. 
    inversion Hdoma; subst a2p'.
    case_eq (a2p!l3).
    SCase "l3 is reachable".
      intros p3 Hget3.
      rewrite Hget3 in *.
      assert (dfs.reachable (cfg.successors (fdef_intro fh bs)) 
                (index le) (index l3)) as Hreach3.
        apply dfs_reachable_iff_get_some with (l0:=l3) in Hdfs; 
          auto using le_in_cfg.
        apply Hdfs. eauto.
      assert (dfs.reachable (cfg.successors (fdef_intro fh bs)) 
                (index le) (index l')) as Hreach'.
        eapply reachable_succ; eauto.
      assert (exists p', a2p!l' = Some p') as Hget'.
        apply dfs_reachable_iff_get_some with (l0:=l') in Hdfs; 
          auto using le_in_cfg.
        apply Hdfs; auto.
      destruct Hget' as [p' Hget'].
      rewrite Hget' in *.
      unfold bound_dom in *.
      assert (Hwf_porder:=Hdfs).
      eapply Order.dfs_wf_porder in Hwf_porder; eauto.
      assert (exists dts3, res ?? p3 = Some dts3) as Hget3a.
        eapply reachable_isnt_bot in Hreach3; eauto.
      assert (exists dts', res ?? p' = Some dts') as Hget'a.
        eapply reachable_isnt_bot in Hreach'; eauto.
      destruct Hget3a as [dts3 Hget3a].
      destruct Hget'a as [dts' Hget'a].
      rewrite Hget3a in *.
      rewrite Hget'a in *.
      assert (In p' 
               (asuccs_psuccs a2p (cfg.successors (fdef_intro fh bs))) ??? p3)
             as Hinscs'.
        eapply in_asuccs__in_psuccs; eauto.
      subst. simpl.
      intros a1 Hin. 
      apply in_ps2as__in_ps in Hin.
      destruct Hin as [p1 [Hget1 Hin]].
      apply DomSound.sadom_adom_successors with (n1:=p1)(entrypoint:=pe) 
        in Hinscs'; auto.
      SSCase "1".
        unfold adomination in Hinscs'. simpl in Hinscs'.
        rewrite Hget3a in Hinscs'.
        simpl in Hinscs'.
        destruct Hinscs' as [EQ | Hin']; subst.
        SSSCase "1.1".
          assert (a1 = l3) as EQ.
            eapply Injective.dfs_inj; eauto.
          subst. simpl. auto.
        SSSCase "1.2".
          simpl. right. eapply in_ps__in_ps2as; eauto.
      SSCase "2".
        eapply get_a2p_in_a2p_cfg; eauto.  
      SSCase "3".
        unfold strict_adomination. simpl.
        rewrite Hget'a. simpl. auto.

    SCase "l3 isnt reachable".
      intros Hget3.
      rewrite Hget3 in *.
      subst contents3. auto with datatypes v62.
  Case "entry is wrong".
    inversion Hdoma; subst a2p.
    rewrite ATree.gempty in *.
    subst contents3. auto with datatypes v62.
Qed.

Section sdom_is_complete.

Variable f:fdef.

Lemma sdom_is_complete: forall
  (branches_in_vertexes: forall p ps0 cs0 tmn0 l2
    (J3 : blockInFdefB (block_intro p ps0 cs0 tmn0) f)
    (J4 : In l2 (successors_terminator tmn0)),
    cfg.vertexes_fdef f (index l2)) (* useless???!!! *)
  (l3 : l) (l' : l) ps cs tmn ps' cs' tmn'
  (HuniqF : uniqFdef f)
  (Hsucc: dom_analysis_is_successful f)
  (HBinF' : blockInFdefB (block_intro l' ps' cs' tmn') f = true)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hsdom: cfg.strict_domination f l' l3),
  In l' (dom_query f l3).
Proof.
  intros. 
  simpl_dom_query.  
  destruct (reach.reachable_dec f l3) as [Hreach | Hunreach].
  Case "reach".
    eapply p2a_strict_domination in Hsdom; eauto.
    destruct Hsdom as [p1 [p2 [pe' [Hsdom [J1 [J2 J3]]]]]].
    simpl in J3. rewrite J3 in Hl2p. inversion Hl2p; subst pe.
    apply DomComplete.sadom_is_complete in Hsdom; eauto using get_a2p_in_a2p_cfg.
    SCase "1".
      unfold strict_adomination in Hsdom.
      simpl in J1, J2, Hsdom.
      eapply pmember__aset_in in Hsdom; eauto.
      rewrite J2. auto. 
    SCase "2".
      eapply Order.dfs_wf_porder in Hdfs; eauto.
  Case "unreach".
    eapply unreachable__get_a2p in Hunreach; eauto.
    simpl in Hunreach. rewrite Hunreach. 
    apply cfg.blockInFdefB_in_vertexes in HBinF'; auto.
Qed.

End sdom_is_complete.

Section dom_unreachable.

Variable f:fdef.

Lemma dom_unreachable: forall
  (branches_in_vertexes: forall p ps0 cs0 tmn0 l2
    (J3 : blockInFdefB (block_intro p ps0 cs0 tmn0) f)
    (J4 : In l2 (successors_terminator tmn0)),
    cfg.vertexes_fdef f (index l2)) (* useless? *)
  (Hhasentry: getEntryBlock f <> None) (* useless? *)
  (l3 : l) (l' : l) ps cs tmn
  (Hsucc: dom_analysis_is_successful f)
  (HuniqF: uniqFdef f)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hunreach: ~ cfg.reachable f l3),
  dom_query f l3 = cfg.bound_fdef f.
Proof.
  intros.
  simpl_dom_query.
  case_eq (PO_a2p ! l3); auto.
  intros p3 Hget3.
  apply UnreachableDoms.dom_unreachable with (n3:=p3) in Hsucc; auto.
  Case "1".
    case_eq ((pdom_analyze (asuccs_psuccs PO_a2p (cfg.successors f)) pe) ?? p3);
      try solve [intros l0 Hsome; rewrite Hsome in Hsucc; inv Hsucc | auto].
  Case "2".
    eapply entry_in_pcfg; eauto.
  Case "3".
    intro J. apply Hunreach. eapply p2a_reachable; eauto.
Qed.

End dom_unreachable.

Section sound_acyclic.

Variable f : fdef.
Hypothesis Hhasentry: getEntryBlock f <> None.

Lemma dom_is_sound : forall
  (l3 : l) (l' : l) ps cs tmn
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : In l' (l3::(dom_query f l3))),
  cfg.domination f l' l3.
Proof.
  intros.
  unfold dom_query, dom_analyze in Hin.
  case_eq (getEntryLabel f); try solve [
    intro Hnone; apply getEntryBlock__getEntryLabel_none in Hnone; congruence
  ].
  intros le Hentry.
  rewrite Hentry in Hin.
  case_eq (dfs (cfg.successors f) le 1).
  intros cnt a2p Hdfs.
  rewrite Hdfs in Hin.
  assert (Hdfs_entry:=Hdfs).
  apply ReachableEntry.dfs_wf in Hdfs_entry.
  simpl in Hdfs_entry.
  case_eq (a2p ! le); try solve [intros; congruence].
  intros pe Hl2p.
  rewrite Hl2p in Hin.
  unfold bound_dom in Hin.
  case_eq (a2p ! l3).
  Case "l3 is reachable".
    intros p3 Hget3.
    rewrite Hget3 in Hin.
    assert (wf_porder:=Hdfs).
    eapply Order.dfs_wf_porder in wf_porder; eauto.
    assert (exists dts3, 
             (pdom_analyze (asuccs_psuccs a2p (cfg.successors f)) pe) ?? p3 =
               Some dts3) as Hdts3_some.
      eapply reachable__get_a2p with (l2:=l3) in Hdfs; eauto.
      assert (exists p3, a2p ! l3 = Some p3) as Hget3'. eauto.
      apply Hdfs in Hget3'.
      eapply a2p_reachable in Hget3'; eauto.
      eapply preachable__qreachable in Hget3'; eauto.
      eapply reachable_isnt_bot in wf_porder; eauto.
    destruct Hdts3_some as [dts3 Hdts3_some].
    rewrite Hdts3_some in Hin. simpl in Hin.
    assert (exists p', a2p ! l' = Some p') as Hget'. 
      destruct Hin as [Hin | Hin]; subst; eauto.
        apply in_ps2as__in_ps in Hin; auto.
        destruct_conjs; eauto.
    destruct Hget' as [p' Hget'].
    apply DomSound.adom_is_sound with (n1:=p')(n2:=p3) in wf_porder; auto.
    SCase "1".
      apply a2p_domination with (p1:=p')(p2:=p3)(pe:=pe)(PO:=mkPO cnt a2p)
        (le:=le); auto.
        intros.
        eapply dfs_reachable_iff_get_some in Hdfs; 
          eauto using le_in_cfg.
    SSCase "2".
      eapply get_a2p_in_a2p_cfg; eauto.
    SSCase "3".
      simpl. unfold adomination.
      rewrite Hdts3_some. simpl.
      destruct Hin as [Hin | Hin]; subst.
        uniq_result. auto.
        apply in_ps2as__in_ps in Hin. 
        destruct_conjs. uniq_result. auto.
  Case "l3 is unreachable".
    intros Hget3.
    eapply unreachable__get_a2p with (l2:=l3) in Hdfs; eauto.
    apply Hdfs in Hget3.
    apply dom_decl.DecDom.everything_dominates_unreachable_blocks; auto.
Qed.

End sound_acyclic.

Section pres_dom.

Variable ftrans: fdef -> fdef.
Variable btrans: block -> block.

Hypothesis ftrans_spec: forall fh bs, 
  ftrans (fdef_intro fh bs) = fdef_intro fh (List.map btrans bs).

Hypothesis btrans_eq_label: forall b, getBlockLabel b = getBlockLabel (btrans b).

Lemma pres_getEntryLabel : forall f,
  getEntryLabel f = getEntryLabel (ftrans f).
Proof.
  intros. destruct f as [fh bs]. rewrite ftrans_spec.
  destruct bs as [|b bs]; auto.
  assert (J:=btrans_eq_label b).
  unfold getBlockLabel in J.
  remember (btrans b) as R.
  destruct b; simpl.
  rewrite <- HeqR. destruct R; congruence.
Qed.

Lemma pres_bound_blocks : forall bs,
  cfg.bound_blocks bs = cfg.bound_blocks (List.map btrans bs).
Proof.
  induction bs as [|a bs]; simpl; auto.
    assert (J:=btrans_eq_label a);
    remember (btrans a) as R.
    destruct R as [l1 ? ? ?]; destruct a; simpl in *; subst l1.
    congruence.
Qed.

Hypothesis btrans_eq_tmn: forall b, 
  terminator_match (getBlockTmn b) (getBlockTmn (btrans b)).

Lemma pres_successors_blocks : forall bs,
  cfg.successors_blocks bs = cfg.successors_blocks (List.map btrans bs).
Proof.
  induction bs as [|b bs]; simpl; auto.
    assert (J:=btrans_eq_tmn b).
    assert (J':=btrans_eq_label b).
    remember (btrans b) as R.
    destruct R as [l1 ? ? ?]; destruct b; simpl in *; subst l1.
    rewrite IHbs. 
    terminator_match_tac.
Qed.

Lemma pres_dom_query: forall (f : fdef) (l5 l0 : l),
  ListSet.set_In l5 (dom_query f l0) <->
  ListSet.set_In l5 (dom_query (ftrans f) l0).
Proof.
  intros.
  unfold dom_query, dom_analyze. destruct f as [fh bs]. 
  case_eq (getEntryLabel (fdef_intro fh bs)).
    intros b Hentry.
    rewrite pres_getEntryLabel in Hentry.
    rewrite Hentry. rewrite ftrans_spec. simpl.
    rewrite <- pres_successors_blocks. 
    rewrite <- pres_bound_blocks.
    split; eauto.

    intros Hentry.
    rewrite pres_getEntryLabel in Hentry.
    rewrite Hentry. rewrite ftrans_spec. simpl.
    rewrite <- pres_bound_blocks. split; auto.
Qed.

Lemma pres_dom_analysis_is_successful : forall f,
  dom_analysis_is_successful f <-> 
    dom_analysis_is_successful (ftrans f).
Proof.
  unfold dom_analysis_is_successful.
  destruct f as [fh bs]. 
  case_eq (getEntryLabel (fdef_intro fh bs)).
    intros b Hentry.
    rewrite pres_getEntryLabel in Hentry.
    rewrite Hentry. rewrite ftrans_spec. simpl.
    rewrite <- pres_successors_blocks. split; eauto.

    intros Hentry.
    rewrite pres_getEntryLabel in Hentry.
    rewrite Hentry. 
    split; auto.
Qed.

End pres_dom.

End AlgDom'.

Module AlgDomProps' := AlgDom_Properties (AlgDom').

(*
Require typings_props.

Require dom_decl.
Require reach.

Module Main. Section Main.

Variable f:fdef.
Definition asuccs := cfg.successors f.
Variable PO: PostOrder.
Variable psuccs: PTree.t (list positive).
Variable ppreds: PTree.t (list positive).
Hypothesis Hpsuccs: psuccs = asuccs_psuccs (PO_a2p PO) asuccs.
Hypothesis Hppreds: ppreds = XPTree.make_predecessors psuccs.

Hypothesis Hvertexes: cfg.vertexes_fdef f = dfs.vertexes asuccs.
Hypothesis Harcs: cfg.arcs_fdef f = dfs.arcs asuccs.

Variable le: l.
Hypothesis Hentry: LLVMinfra.getEntryLabel f = Some le.

Hypothesis Hdfs: dfs (cfg.successors f) le 1 = PO.

Definition adom (l1 l2:l) : Prop :=
match (PO_a2p PO) ! l1, (PO_a2p PO) ! l2 with
| Some p1, Some p2 => 
    member psuccs p1 (LDoms.transfer p2 ((dom_analyze f) ?? p2))
| _, None => XATree.in_cfg asuccs l1 /\ XATree.in_cfg asuccs l2
| _, _ => False
end.

Definition sadom (l1 l2:l) : Prop :=
match (PO_a2p PO) ! l1, (PO_a2p PO) ! l2 with
| Some p1, Some p2 => 
    member psuccs p1 ((dom_analyze f) ?? p2)
| _, None => XATree.in_cfg asuccs l1 /\ XATree.in_cfg asuccs l2
| _, _ => False
end.

Variable pe: positive.
Hypothesis Hpentry: (PO_a2p PO) ! le = Some pe.

Hypothesis wf_order: forall n (Hneq: n <> pe),
  exists p, In p (ppreds ??? n) /\ (p > n)%positive.

Lemma dom_is_sound : forall l1 l2 (Hadom: adom l1 l2),
  cfg.domination f l1 l2.
Proof.
  unfold adom, dom_analyze.
  intros.
  fill_holes_in_ctx.
  rewrite Hdfs in Hadom. 
  remember ((PO_a2p PO) ! l1) as R1.
  remember ((PO_a2p PO) ! l2) as R2.
  destruct R2 as [p2|].
  Case "1".
    destruct R1 as [p1|]; try tauto.
    SCase "1.1".
    remember PO as R.
    destruct R. simpl in *.
    fill_holes_in_ctx. subst ppreds psuccs.
    apply DomSound.adom_is_sound with (n1:=p1)(n2:=p2) in wf_order; auto.
      SSCase "1.1.1".
      apply a2p_domination with (p1:=p1)(p2:=p2)(pe:=pe); subst PO; auto.
        intros.
        eapply dfs_reachable_iff_get_some in Hdfs; 
          eauto using le_in_cfg.

      SSCase "1.1.2".
      eapply get_a2p_in_a2p_cfg; eauto.
  Case "2".
    symmetry in HeqR2.
    eapply unreachable__get_a2p in HeqR2.
    apply dom_decl.DecDom.everything_dominates_unreachable_blocks; auto.
    apply getEntryLabel__getEntryBlock in Hentry.
    destruct Hentry as [be [Hentry' EQ]]; subst. congruence.
Qed.

End Main. End Main.

*)
