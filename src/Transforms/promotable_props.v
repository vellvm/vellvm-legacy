Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import dtree.
Require Import primitives.
Require Import Maps.
Require Import mem2reg.
Require Import opsem_props.

Module Promotability.

Definition DGVMap := @Opsem.GVsMap DGVs.

Record PhiInfo := mkPhiInfo {
  PI_f: fdef;
  PI_rd: list l;
  PI_succs: ATree.t (list l);
  PI_preds: ATree.t (list l);
  PI_id: id;
  PI_typ: typ;
  PI_align: align;
  PI_newids: ATree.t (id*id*id)  
}.

Definition promotable_alloca (f:fdef) (pid:id) (ty:typ) (al:align) : Prop :=
match getEntryBlock f with
| Some (block_intro _ _ cs _) =>
    find_promotable_alloca f cs nil = Some (pid, ty, al)
| _ => False
end.

Definition WF_PhiInfo (pinfo: PhiInfo) : Prop :=
let '(mkPhiInfo f rd succs preds pid ty al newids) := pinfo in
promotable_alloca f pid ty al /\
reachablity_analysis f = Some rd /\
succs = successors f /\
preds = make_predecessors succs /\
newids = fst (gen_fresh_ids rd (getFdefLocs f)).

(* wf_global and wf_globals are copied from sb_ds_gv_inject.v 
   We should move the invariant to memory model. *)
Fixpoint wf_global (maxb:Values.block) (gv:GenericValue) 
  : Prop :=
match gv with
| nil => True
| (Vptr b _,_)::gv' => b <= maxb /\ wf_global maxb gv'
| _::gv' => wf_global maxb gv'
end.

Fixpoint wf_global_list maxb (gl:GVMap) : Prop :=
match gl with
| nil => True
| (_,gv)::gl' => wf_global maxb gv /\ wf_global_list maxb gl'
end.

Definition wf_globals maxb (gl:GVMap) : Prop :=
0 <= maxb /\ wf_global_list maxb gl.

Fixpoint no_alias_with_blk (gvs:GenericValue) (blk:Values.block) : Prop :=
match gvs with
| nil => True
| (Vptr b _,_)::gvs' => b <> blk /\ no_alias_with_blk gvs' blk
| _::gvs' => no_alias_with_blk gvs' blk
end.

Fixpoint no_alias (gvs1 gvs2:GenericValue) : Prop :=
match gvs2 with
| nil => True
| (Vptr b _,_)::gvs2' => no_alias_with_blk gvs1 b /\ no_alias gvs1 gvs2'
| _::gvs2' => no_alias gvs1 gvs2'
end.

Definition wf_non_alloca_GVs (pinfo:PhiInfo) (id1:id) (gvs1 gvsa:GenericValue) 
  : Prop :=
(if (id_dec id1 (PI_id pinfo)) then True else no_alias gvs1 gvsa).

Definition wf_alloca_GVs (maxb:Values.block) (pinfo:PhiInfo) TD Mem 
  (gvsa:GenericValue) (als:list Values.block) : Prop :=
(exists mb, gvsa = ($ (blk2GV TD mb) # (typ_pointer (PI_typ pinfo)) $) /\
   In mb als /\ maxb < mb < Mem.nextblock Mem) /\
(forall gptr gvs1 ty al, 
   mload TD Mem gptr ty al = Some gvs1 ->
   no_alias gvs1 gvsa) /\
exists gv,
  mload TD Mem gvsa (PI_typ pinfo) (PI_align pinfo) = Some gv.

Definition wf_defs (maxb:Values.block) (pinfo:PhiInfo) TD M (lc:DGVMap) 
  (ids0:list atom) (als:list Values.block) : Prop :=
forall gvsa
  (Hinp: In (PI_id pinfo) ids0)
  (Hlkp: lookupAL _ lc (PI_id pinfo) = Some gvsa),
  wf_alloca_GVs maxb pinfo TD M gvsa als /\
  (forall id0 gvs0 
   (*Hin0: In id0 ids0*) 
   (Hlk0: lookupAL _ lc id0 = Some gvs0),
   wf_non_alloca_GVs pinfo id0 gvs0 gvsa).

Fixpoint valid_ptrs (bound:Values.block) (gvs:GenericValue): Prop :=
match gvs with
| nil => True
| (Vptr blk _,_)::gvs' => blk < bound /\ valid_ptrs bound gvs'
| _::gvs' => valid_ptrs bound gvs'
end.

Definition wf_lc M lc : Prop :=
forall id0 gvs, 
  lookupAL _ lc id0 = Some gvs -> valid_ptrs (Mem.nextblock M) gvs.

Definition inscope_of_pc f b cs tmn : option (list id) :=
match cs with
| nil => inscope_of_tmn f b tmn
| c::_ => inscope_of_cmd f b c
end.

(* Except domination property, the other properties are the same for a lot of 
   proofs, we should prove them all for once. Or, we do not need to use them
   in this invariant, we can assume the invariant in opsem_wf, which is 
   preserved *)
Definition wf_ExecutionContext (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (ec:Opsem.ExecutionContext) : Prop :=
let '(Opsem.mkEC f b cs tmn lc als) := ec in
(if (fdef_dec (PI_f pinfo) f) then 
  match inscope_of_pc f b cs tmn with
  | Some ids => wf_defs maxb pinfo TD M lc ids als
  | None => False
  end
else True)
/\ wf_lc M lc.

Definition wf_ECStack_head_in_tail (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (lc:DGVMap) (ec0:Opsem.ExecutionContext) : Prop :=
let '(Opsem.mkEC f0 b0 cs0 tmn0 lc0 _) := ec0 in
forall ids0 gvsa, 
  f0 = PI_f pinfo ->
  inscope_of_pc f0 b0 cs0 tmn0 = Some ids0 -> 
  In (PI_id pinfo) ids0 ->
  lookupAL _ lc0 (PI_id pinfo) = Some gvsa ->
  (exists mb, gvsa = ($ (blk2GV TD mb) # (typ_pointer (PI_typ pinfo)) $) /\ 
    maxb < mb < Mem.nextblock M) /\
  (forall id1 gvs1, 
    lookupAL _ lc id1 = Some gvs1 -> 
    no_alias gvs1 gvsa) /\
  (forall gptr t al gvs1, 
    mload TD M gptr t al = Some gvs1 -> 
    no_alias gvs1 gvsa).

Definition wf_ECStack_head_tail (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (lc:DGVMap) (ecs':list Opsem.ExecutionContext) : Prop :=
  forall ec0, In ec0 ecs' -> wf_ECStack_head_in_tail maxb pinfo TD M lc ec0.

Fixpoint wf_ECStack (maxb:Values.block) (pinfo:PhiInfo) TD M (ecs:Opsem.ECStack)
  : Prop :=
match ecs with
| nil => True
| ec::ecs' => 
    wf_ExecutionContext maxb pinfo TD M ec /\
    wf_ECStack maxb pinfo TD M ecs' /\
    wf_ECStack_head_tail maxb pinfo TD M (Opsem.Locals ec) ecs'
end.

Definition wf_Mem maxb (td:targetdata) (M:mem) : Prop :=
(forall gptr ty al gvs, 
  mload td M gptr ty al = Some gvs -> valid_ptrs (Mem.nextblock M) gvs) /\
maxb < Mem.nextblock M.

Definition wf_als maxb M (als: list Values.block) : Prop :=
NoDup als /\ (forall al, In al als -> maxb < al < Mem.nextblock M).

Definition wf_State (maxb:Values.block) (pinfo:PhiInfo) (cfg:OpsemAux.Config) 
  (S:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg _ td _ _ _ ) := cfg in
let '(Opsem.mkState ecs M) := S in
wf_ECStack maxb pinfo td M ecs /\
wf_als maxb M 
  (flat_map (fun ec => let '(Opsem.mkEC _ _ _ _ _ als) := ec in als) ecs) /\
wf_Mem maxb td M.

Lemma wf_defs_eq : forall maxb pinfo TD M lc ids1 ids2 als,
  AtomSet.set_eq _ ids1 ids2 ->
  wf_defs maxb pinfo TD M lc ids1 als ->
  wf_defs maxb pinfo TD M lc ids2 als.
Proof.
  intros. unfold wf_defs in *. intros.
  destruct H as [H1 H2]. eauto.
Qed.

Definition wf_GVs (maxb:Values.block)(pinfo:PhiInfo)(TD:targetdata)(M:mem)
  (lc:DGVMap)(ids1:list id)(als:list Values.block)(id1:id)(gv1:GVsT DGVs)
  : Prop :=
  (forall gvsa,
     In (PI_id pinfo) ids1 ->
     lookupAL _ lc (PI_id pinfo) = Some gvsa ->
     no_alias gv1 gvsa) /\
  (id1 = (PI_id pinfo) ->
     (forall id0 gvs0,
        lookupAL (GVsT DGVs) lc id0 = ret gvs0 ->
        no_alias gvs0 gv1) /\
     wf_alloca_GVs maxb pinfo TD M gv1 als).

Lemma wf_defs_updateAddAL: forall maxb pinfo TD M lc' ids1 ids2 i1 gv1 als
  (HwfDef: wf_defs maxb pinfo TD M lc' ids1 als)
  (Heq: AtomSet.set_eq _ (i1::ids1) ids2)
  (Hwfgvs: wf_GVs maxb pinfo TD M lc' ids1 als i1 gv1),
  wf_defs maxb pinfo TD M (updateAddAL _ lc' i1 gv1) ids2 als.
Proof.
  intros. unfold wf_defs. intros.
  destruct Hwfgvs as [Hwfgvs1 Hwfgvs2].
  destruct Heq as [Hinc1 Hinc2].
  apply Hinc2 in Hinp. simpl in Hinp.
  destruct (eq_dec i1 (PI_id pinfo)); subst.
    rewrite lookupAL_updateAddAL_eq in Hlkp.
    inv Hlkp.
    destruct Hwfgvs2 as [J1 J2]; auto.
    split; auto.
      intros. unfold wf_non_alloca_GVs.
      destruct (id_dec id0 (PI_id pinfo)); subst; auto.
      rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
      apply J1 in Hlk0; auto.

    clear Hwfgvs2.
    rewrite <- lookupAL_updateAddAL_neq in Hlkp; auto.
    destruct Hinp as [EQ | Hinp]; subst; try congruence.
    assert (Hlkp':=Hlkp).
    apply HwfDef in Hlkp; auto.
    destruct Hlkp as [J1 J2].
    split; auto.
      intros.
      destruct (id_dec i1 id0); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk0.
        inv Hlk0. apply Hwfgvs1 in Hlkp'; auto.
        unfold wf_non_alloca_GVs.
        destruct (id_dec id0 (PI_id pinfo)); subst; auto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
Qed.

Lemma preservation_helper1: forall los nts Ps S F l1 ps1 cs1' c0 tmn ifs
  (HwfS : wf_system ifs S)
  (HMinS : moduleInSystemB (module_intro los nts Ps) S = true)
  (HFinPs : InProductsB (product_fdef F) Ps = true)
  (HBinF : blockInFdefB (block_intro l1 ps1 (cs1' ++ [c0]) tmn) F = true),
  ~ In (getCmdLoc c0) (getCmdsLocs cs1').
Proof.
  intros.
  eapply wf_system__uniq_block with (f:=F) in HwfS; eauto.
  simpl in HwfS.
  apply NoDup_inv in HwfS.
  destruct HwfS as [_ J].
  apply NoDup_inv in J.
  destruct J as [J _].
  rewrite getCmdsLocs_app in J.
  simpl in J.
  apply NoDup_last_inv in J. auto.
Qed.

Lemma preservation_helper2: forall los nts Ps S F l1 ps1 cs1' c0 tmn ifs c cs
  (HwfS : wf_system ifs S)
  (HMinS : moduleInSystemB (module_intro los nts Ps) S = true)
  (HFinPs : InProductsB (product_fdef F) Ps = true)
  (HBinF : blockInFdefB 
            (block_intro l1 ps1 (cs1' ++ [c0] ++ [c] ++ cs) tmn) F = true),
  NoDup (getCmdsLocs (cs1' ++ [c0] ++ [c] ++ cs)).
Proof.
  intros.
  eapply wf_system__uniq_block with (f:=F) in HwfS; eauto.
  simpl in HwfS.
  apply NoDup_inv in HwfS.
  destruct HwfS as [_ J].
  apply NoDup_inv in J.
  destruct J as [J _]. auto.
Qed.

Lemma impure_cmd_non_updated_preserves_wf_EC : forall maxb pinfo TD M M' lc F B 
  als tmn cs c0 l1 ps1 cs1' ifs S
  (Heq: B = block_intro l1 ps1 (cs1' ++ c0 :: cs) tmn)
  (HwfS: wf_system ifs S) los nts (Heq': TD = (los, nts)) Ps
  (HMinS: moduleInSystemB (module_intro los nts Ps) S = true)
  (HFinPs: InProductsB (product_fdef F) Ps = true)
  (HBinF: blockInFdefB B F = true)
  (Hid : getCmdID c0 = None)
  (Hwfdefs: forall ids0,
              F = (PI_f pinfo) ->
              inscope_of_pc F B (c0::cs) tmn = Some ids0 ->
              wf_defs maxb pinfo TD M lc ids0 als ->
              wf_defs maxb pinfo TD M' lc ids0 als)
  (Hwflc: wf_lc M lc -> wf_lc M' lc)
  (HwfEC: wf_ExecutionContext maxb pinfo TD M 
            {| Opsem.CurFunction := F;
               Opsem.CurBB := B;
               Opsem.CurCmds := c0 :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
  wf_ExecutionContext maxb pinfo TD M'
    {| Opsem.CurFunction := F;
       Opsem.CurBB := B;
       Opsem.CurCmds := cs;
       Opsem.Terminator := tmn;
       Opsem.Locals := lc;
       Opsem.Allocas := als |}.
Proof.
  simpl. intros.
  destruct HwfEC as [J1 J2].
  split; auto.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  remember (inscope_of_cmd (PI_f pinfo) 
    (block_intro l1 ps1 (cs1' ++ c0 :: cs) tmn) c0) as R1. 
  assert (HeqR1':=HeqR1).
  unfold inscope_of_cmd, inscope_of_id in HeqR1'.

  destruct R1; try solve [inversion J1].
  repeat (split; try solve [auto]).
      unfold inscope_of_pc.
      destruct cs; simpl_env in *.
      SSSSCase "cs = nil".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs1')) 
          as Hnotin.
          eapply preservation_helper1; eauto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1' J2']].
        rewrite <- J1'.
        assert (In c0 (cs1' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        assert (HwfF:=HFinPs). eapply wf_system__wf_fdef in HwfF; eauto.
        rewrite Hid in J2'. 
        eapply wf_defs_eq; eauto.       

      SSSSCase "cs <> nil".
        assert (NoDup (getCmdsLocs (cs1' ++ [c0] ++ [c] ++ cs))) 
          as Hnodup.
          eapply preservation_helper2; eauto.

        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1' J2']].        
        rewrite <- J1'.
        assert (In c0 (cs1' ++ [c0] ++ [c] ++ cs)) 
          as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite Hid in J2'. 
        eapply wf_defs_eq; eauto.
Qed.

(* We need a generic proof for this one and the one for atom *)
Lemma NoDup_disjoint : forall (l1 l2 : list Z) (i0 : Z),
  NoDup (l1 ++ l2) -> In i0 l2 -> ~ In i0 l1.
Admitted.

Ltac inv_mbind :=
  repeat match goal with
         | H : match ?e with
               | Some _ => _
               | None => None
               end = Some _ |- _ => remember e as R; destruct R as [|]; inv H
         end.

Ltac inv_mbind' :=
  repeat match goal with
         | H : match ?e with
               | Some _ => _
               | None => None
               end = Some _ |- _ => remember e as R; destruct R as [|]; inv H
         | H : Some _ = match ?e with
               | Some _ => _
               | None => None
               end |- _ => remember e as R; destruct R as [|]; inv H
         | H :  ret _ = match ?p with
                        | (_, _) => _
                        end |- _ => destruct p
         end.

Ltac unfold_blk2GV := unfold blk2GV, ptr2GV, val2GV.

Lemma simpl_blk2GV: forall td mb t,
  $ blk2GV td mb # typ_pointer t $ =
  ((Vptr mb (Int.repr 31 0),
    AST.Mint (Size.mul Size.Eight (getPointerSize td) - 1)) :: nil).
Proof.
  intros. unfold_blk2GV. 
Local Transparent gv2gvs.
  unfold gv2gvs. simpl. auto.
Opaque gv2gvs. 
Qed.

Lemma null_disjoint_with_ptr: forall td mb t,
  mb > 0 ->
  no_alias null ($ blk2GV td mb # typ_pointer t $).
Proof.
  intros. rewrite simpl_blk2GV. simpl. unfold Mem.nullptr.
  repeat split; auto. intro. subst. omega.
Qed.

Lemma null_valid_ptrs: forall mb, mb > 0 -> valid_ptrs mb null.
Proof.
  intros. unfold null, Mem.nullptr. simpl. 
  split; auto. omega.
Qed.

Lemma uninits_valid_ptrs: forall bd n, valid_ptrs bd (uninits n).
Proof.
  intros.
  induction n; simpl; auto.
Qed.

Lemma uninits_disjoint_with_ptr: forall n td mb t,
  no_alias (uninits n) ($ blk2GV td mb # typ_pointer t $).
Proof.
  intros.
  rewrite simpl_blk2GV.
  induction n; simpl; auto.
Qed.

Lemma uninits_valid_ptrs__disjoint_with_ptr: forall n td mb t bd,
  no_alias (uninits n) ($ blk2GV td mb # typ_pointer t $) /\
  valid_ptrs bd (uninits n).
Proof.
  intros.
  split. apply uninits_disjoint_with_ptr.
         apply uninits_valid_ptrs.
Qed.

Fixpoint no_embedded_ptrs (gvs:GenericValue): Prop :=
match gvs with
| nil => True
| (Vptr _ _,_)::gvs' => False
| _::gvs' => no_embedded_ptrs gvs'
end.

Lemma no_embedded_ptrs__no_alias_with_blk: forall b2 gvs1,
  no_embedded_ptrs gvs1 -> no_alias_with_blk gvs1 b2.
Proof.
  induction gvs1 as [|[]]; simpl; intros; auto.
    destruct v; auto. inv H.
Qed.

Lemma undef__no_embedded_ptrs: forall g td t1
  (Hc2g : ret g = gundef td t1), no_embedded_ptrs g.
Proof.
  unfold gundef. intros.
  inv_mbind'. simpl. auto.
Qed.

Lemma no_embedded_ptrs__no_alias: forall gvs1 gvs2,
  no_embedded_ptrs gvs1 -> no_alias gvs1 gvs2.
Proof.
  induction gvs2 as [|[]]; simpl; intros; auto.
    destruct v; auto.
    split; auto using no_embedded_ptrs__no_alias_with_blk.
Qed.

Lemma undef_disjoint_with_ptr: forall g td t1 g'
  (Hc2g : ret g = gundef td t1), no_alias g g'.
Proof.
  intros. apply undef__no_embedded_ptrs in Hc2g.
  apply no_embedded_ptrs__no_alias; auto.
Qed.

Lemma no_alias_with_blk_app: forall g2 b g1,
  no_alias_with_blk g1 b -> no_alias_with_blk g2 b -> 
  no_alias_with_blk (g1++g2) b.
Proof.
  induction g1; simpl; intros; auto.
    destruct a.
    destruct v; auto.
    destruct H; auto.
Qed.

Lemma no_alias_app: forall g2 g1 g,
  no_alias g1 g -> no_alias g2 g -> no_alias (g1++g2) g.
Proof.
  induction g; simpl; intros; auto.
    destruct a.
    destruct v; auto.
    destruct H. destruct H0.
    split; auto using no_alias_with_blk_app.
Qed.

Lemma no_alias_nil: forall g, no_alias nil g.
Proof.
  induction g; simpl; intros; auto.
    destruct a.
    destruct v; auto.
Qed.

Lemma no_alias_repeatGV: forall g1 g2 n,
  no_alias g1 g2 -> no_alias (repeatGV g1 n) g2.
Proof.
  induction n; simpl; intros.
    apply no_alias_nil.
    apply no_alias_app; auto.
Qed.

Lemma valid_ptrs_app: forall bd g2 g1,
  valid_ptrs bd g1 -> valid_ptrs bd g2 -> valid_ptrs bd (g1++g2).
Proof.
  induction g1 as [|[]]; simpl; intros; auto.
    destruct v; auto.
    destruct H. 
    split; auto.
Qed.

Lemma valid_ptrs_repeatGV: forall n bd g,
  valid_ptrs bd g -> valid_ptrs bd (repeatGV g n).
Proof.
  induction n; simpl; intros; auto.
    apply valid_ptrs_app; auto.
Qed.

Definition zeroconst2GV_disjoint_with_runtime_alloca_prop (t:typ) := 
  forall maxb gl g td mb t0
  (Hwfg: wf_globals maxb gl)
  (Hc2g : ret g = zeroconst2GV td t)
  (Hle: maxb < mb),
  no_alias g ($ blk2GV td mb # typ_pointer t0 $) /\ valid_ptrs (maxb + 1) g.

Definition zeroconsts2GV_disjoint_with_runtime_alloca_prop (lt:list_typ) := 
  forall maxb gl g td mb t0
  (Hwfg: wf_globals maxb gl)
  (Hc2g : ret g = zeroconsts2GV td lt)
  (Hle: maxb < mb),
  no_alias g ($ blk2GV td mb # typ_pointer t0 $) /\ valid_ptrs (maxb + 1) g.

Lemma zeroconst2GV_disjoint_with_runtime_alloca_mutrec :
  (forall t, zeroconst2GV_disjoint_with_runtime_alloca_prop t) *
  (forall lt, zeroconsts2GV_disjoint_with_runtime_alloca_prop lt).
Proof.
  apply typ_mutrec; 
    unfold zeroconst2GV_disjoint_with_runtime_alloca_prop, 
           zeroconsts2GV_disjoint_with_runtime_alloca_prop; 
    intros; simpl in *;
    try solve [inv Hc2g; rewrite simpl_blk2GV; simpl; auto].

  destruct f; inv Hc2g; rewrite simpl_blk2GV; simpl; auto.

  destruct s; 
    try solve [inv Hc2g; auto using uninits_valid_ptrs__disjoint_with_ptr].
    inv_mbind'.
    eapply H with (t0:=t0) in HeqR; eauto.
    assert (no_alias 
      (g0 ++ uninits (Size.to_nat s0 - sizeGenericValue g0))
      ($ blk2GV td mb # typ_pointer t0 $) /\
      valid_ptrs (maxb + 1) 
        (g0 ++ uninits (Size.to_nat s0 - sizeGenericValue g0))) as J.
      destruct HeqR.
      split.
        apply no_alias_app; auto.
          apply uninits_disjoint_with_ptr.
        apply valid_ptrs_app; auto.
          apply uninits_valid_ptrs.
    destruct J as [J1 J2].
    split.
      apply no_alias_app; auto.
      apply no_alias_repeatGV; auto.

      apply valid_ptrs_app; auto.
      apply valid_ptrs_repeatGV; auto.

  inv_mbind'.
  eapply H with (t0:=t0) in HeqR; eauto.
  destruct g0; inv H1; auto.

  inv Hc2g. 
  split.
    apply null_disjoint_with_ptr. destruct Hwfg. omega.
    apply null_valid_ptrs. destruct Hwfg. omega.

  inv_mbind'.
  eapply H with (t0:=t0) in HeqR0; eauto.
  eapply H0 with (t0:=t0) in HeqR; eauto.
  destruct HeqR0. destruct HeqR.
  split.
    apply no_alias_app; auto.
    apply no_alias_app; auto.
    apply uninits_disjoint_with_ptr.

    apply valid_ptrs_app; auto.
    apply valid_ptrs_app; auto.
    apply uninits_valid_ptrs.
Qed.

Lemma zeroconst2GV_disjoint_with_runtime_alloca: forall t maxb gl g td mb t0
  (Hwfg: wf_globals maxb gl)
  (Hc2g : ret g = zeroconst2GV td t)
  (Hle: maxb < mb),
  no_alias g ($ blk2GV td mb # typ_pointer t0 $) /\ valid_ptrs (maxb + 1) g.
Proof.
  destruct zeroconst2GV_disjoint_with_runtime_alloca_mutrec as [J _]; auto.
Qed.

Tactic Notation "eapply_clear" hyp(H1) "in" hyp(H2) :=
  eapply H1 in H2; eauto; clear H1.

Tactic Notation "apply_clear" hyp(H1) "in" hyp(H2) :=
  apply H1 in H2; auto; clear H1.

Lemma wf_global_disjoint_with_runtime_alloca: forall maxb td t0
  mb (Hle : maxb < mb) g0 (Hwfg : wf_global maxb g0),
  no_alias g0 ($ blk2GV td mb # typ_pointer t0 $) /\ valid_ptrs (maxb + 1) g0.
Proof.
  induction g0 as [|[]]; simpl; intros.
    split; auto using no_alias_nil.

    destruct v; auto.
      destruct Hwfg as [J1 J2].
      apply_clear IHg0 in J2. rewrite simpl_blk2GV in *. 
      simpl in *. destruct J2. destruct H.
      split.
        split; auto.    
        split; auto. 
          intro. subst. contradict J1. omega.

        split; auto. omega.
Qed.

Lemma wf_globals_disjoint_with_runtime_alloca: forall maxb td t0
  (g0 : GenericValue) i0  mb (Hle : maxb < mb) gl (Hwfg : wf_globals maxb gl) 
  (HeqR : ret g0 = lookupAL GenericValue gl i0),
  no_alias g0 ($ blk2GV td mb # typ_pointer t0 $) /\ valid_ptrs (maxb + 1) g0.
Proof.
  induction gl as [|[]]; simpl; intros.
    congruence.

    destruct Hwfg. simpl in H0.
    destruct H0 as [J1 J2].
    destruct (i0 == i1); subst.
      inv HeqR. eapply wf_global_disjoint_with_runtime_alloca; eauto.
      apply IHgl; auto. split; auto.
Qed.

Lemma no_embedded_ptrs__valid_ptrs: forall bd gvs,
  no_embedded_ptrs gvs -> valid_ptrs bd gvs.
Proof.
  induction gvs as [|[]]; simpl; intros; auto.
    destruct v; auto.
      inversion H.
Qed.

Lemma mtrunc_preserves_no_embedded_ptrs: forall td top t1 t2 gv gv',
  mtrunc td top t1 t2 gv = Some gv' -> no_embedded_ptrs gv'.
Proof.
  intros.
  unfold mtrunc in H.
  remember (GV2val td gv) as R.
  destruct R; eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
    destruct t1; eauto using undef__no_embedded_ptrs.
    destruct t2; eauto using undef__no_embedded_ptrs.
      inv H. destruct (le_lt_dec wz s0); simpl; auto.

    destruct t1; eauto using undef__no_embedded_ptrs.
    destruct t2; eauto using undef__no_embedded_ptrs.
    destruct (floating_point_order f1 f0); tinv H.
    destruct f1; inv H; unfold val2GV; simpl; auto.
Qed.

Lemma mtrunc_preserves_no_alias: forall td top t1 t2 gv gv' gv0,
  mtrunc td top t1 t2 gv = Some gv' -> no_alias gv' gv0.
Proof.
  intros.
  apply no_embedded_ptrs__no_alias.
  apply mtrunc_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma mtrunc_preserves_valid_ptrs: forall td top t1 t2 gv gv' bd,
  mtrunc td top t1 t2 gv = Some gv' -> valid_ptrs bd gv'.
Proof.
  intros.
  apply no_embedded_ptrs__valid_ptrs.
  apply mtrunc_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma mext_preserves_no_embedded_ptrs: forall td eop t1 t2 gv gv',
  mext td eop t1 t2 gv = Some gv' -> no_embedded_ptrs gv'.
Proof.
  intros.
  unfold mext in H.
  remember (GV2val td gv) as R.
  destruct t1; tinv H.
    destruct t2; tinv H.
    destruct R; eauto using undef__no_embedded_ptrs.
    destruct v; eauto using undef__no_embedded_ptrs.
    destruct eop; inv H; simpl; auto.

    destruct t2; tinv H.
    destruct (floating_point_order f f0); tinv H.
    destruct R; eauto using undef__no_embedded_ptrs.
    destruct v; eauto using undef__no_embedded_ptrs.
    destruct eop; tinv H; simpl; auto.
    destruct f0; inv H; unfold val2GV; simpl; auto.
Qed.

Lemma mext_preserves_no_alias: forall td eop t1 t2 gv gv' gv0,
  mext td eop t1 t2 gv = Some gv' -> no_alias gv' gv0.
Proof.
  intros.
  apply no_embedded_ptrs__no_alias.
  apply mext_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma mext_preserves_valid_ptrs: forall td eop t1 t2 gv gv' bd,
  mext td eop t1 t2 gv = Some gv' -> valid_ptrs bd gv'.
Proof.
  intros.
  apply no_embedded_ptrs__valid_ptrs.
  apply mext_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma mbitcast_inv: forall t1 t2 gv1 gv2,
  mbitcast t1 gv1 t2 = ret gv2 -> gv1 = gv2.
Proof.
  intros.
  unfold mbitcast in H.
  destruct t1; tinv H.
    destruct t2; inv H; auto.
    destruct t2; inv H; auto.
Qed.

Lemma mcast_inv: forall td cop t1 t2 gv1 gv2,
  mcast td cop t1 t2 gv1 = ret gv2 -> gv2 = gv1 \/ gundef td t2 = ret gv2.
Proof.
  intros.
  unfold mcast in H.
  destruct cop; auto;
    try 
    match goal with
    | H : mbitcast _ _ _ = ret _ |- _ => apply mbitcast_inv in H; subst; auto
    end.
Qed.

Lemma mbitcast_preserves_no_alias: forall t1 t2 gv gv' gv0,
  mbitcast t1 gv t2 = Some gv' ->
  no_alias gv gv0 -> no_alias gv' gv0.
Proof.
  intros.
  apply mbitcast_inv in H. subst. auto.
Qed.

Lemma mcast_preserves_no_alias: forall td cop t1 t2 gv gv' gv0,
  mcast td cop t1 t2 gv = Some gv' ->
  no_alias gv gv0 -> no_alias gv' gv0.
Proof.
  intros.
  apply mcast_inv in H. 
  destruct H as [H | H]; subst; eauto using undef_disjoint_with_ptr.
Qed.

Lemma undef_valid_ptrs: forall g td t1 blk
  (Hc2g : ret g = gundef td t1), valid_ptrs blk g.
Proof.
  unfold gundef. intros.
  inv_mbind'. simpl. auto.
Qed.

Lemma mcast_preserves_valid_ptrs: forall td cop t1 t2 gv gv' bd,
  mcast td cop t1 t2 gv = Some gv' -> valid_ptrs bd gv -> valid_ptrs bd gv'.
Proof.
  intros.
  apply mcast_inv in H. 
  destruct H as [H | H]; subst; eauto using undef_valid_ptrs.
Qed.

Lemma no_alias_prop1: forall b i1 m1 i2 m2 g,
  no_alias ((Vptr b i1, m1) :: nil) g -> no_alias ((Vptr b i2, m2) :: nil) g.
Proof.
  induction g as [|[]]; simpl; intros; auto.
    destruct v; auto.
    destruct H. simpl; auto.
Qed.

Lemma GV2ptr_inv: forall g1 td v,
  ret v = GV2ptr td (getPointerSize td) g1 -> 
  exists b, exists ofs, exists m, g1 = (Vptr b ofs, m)::nil /\ v = Vptr b ofs.
Proof.
  intros.
  unfold GV2ptr in H.
  destruct g1 as [|[]]; tinv H.
  destruct v0; tinv H.
  destruct g1 as [|[]]; inv H. 
  unfold ptr2GV. unfold val2GV. eauto.
Qed.

Lemma GV2ptr_preserves_no_alias: forall g1 td g2 v,
  no_alias g1 g2 ->
  ret v = GV2ptr td (getPointerSize td) g1 ->
  no_alias (ptr2GV td v) g2.
Proof.
  intros. apply GV2ptr_inv in H0. destruct H0 as [b [ofs [m [J1 J2]]]]; subst.
  unfold ptr2GV. unfold val2GV. eapply no_alias_prop1; eauto.
Qed.

Lemma GV2ptr_preserves_valid_ptrs: forall bd g1 td v,
  valid_ptrs bd g1 ->
  ret v = GV2ptr td (getPointerSize td) g1 ->
  valid_ptrs bd (ptr2GV td v).
Proof.
  intros. apply GV2ptr_inv in H0. destruct H0 as [b [ofs [m [J1 J2]]]]; subst.
  unfold ptr2GV. unfold val2GV. simpl in *. auto.
Qed.

Lemma mgep_inv: forall td v1 t1 l1 v2,
  ret v2 = mgep td t1 v1 l1 ->
  exists b, exists ofs1, exists ofs2, v1 = Vptr b ofs1 /\ v2 = Vptr b ofs2.
Proof.
  intros.
  unfold mgep in *.
  destruct v1; tinv H.
  destruct l1; tinv H.
  destruct (mgetoffset td (typ_array 0%nat t1) (z :: l1)) as [[]|]; inv H.
  eauto.
Qed.  

Lemma mgep_preserves_no_alias: forall td v t1 l1 v0 gv,
  no_alias (ptr2GV td v) gv ->
  ret v0 = mgep td t1 v l1 ->
  no_alias (ptr2GV td v0) gv.
Proof.
  intros.
  apply mgep_inv in H0. destruct H0 as [b [ofs1 [ofs2 [J1 J2]]]]; subst. 
  unfold ptr2GV in *. unfold val2GV in *. eapply no_alias_prop1; eauto.
Qed.

Lemma mgep_preserves_valid_ptrs: forall td v t1 l1 v0 bd,
  valid_ptrs bd (ptr2GV td v) ->
  ret v0 = mgep td t1 v l1 ->
  valid_ptrs bd (ptr2GV td v0).
Proof.
  intros.
  apply mgep_inv in H0. destruct H0 as [b [ofs1 [ofs2 [J1 J2]]]]; subst. 
  simpl in *. auto.
Qed.

Lemma nonptr_no_alias: forall v t td mb t0,
  (forall b ofs, v <> Vptr b ofs) ->
  no_alias (val2GV td v t) ($ blk2GV td mb # typ_pointer t0 $).
Proof.
  intros.
  rewrite simpl_blk2GV.  
  destruct v; simpl; auto.
    assert (H1:=@H b i0). congruence.
Qed.

Lemma nonptr_no_embedded_ptrs: forall v t td,
  (forall b ofs, v <> Vptr b ofs) -> no_embedded_ptrs (val2GV td v t).
Proof.
  intros.
  destruct v; simpl; auto.
    assert (H1:=@H b i0). congruence.
Qed.

Lemma micmp_int_preserves_no_embedded_ptrs: forall td cop gv1 gv2 gv',
  micmp_int td cop gv1 gv2 = Some gv' -> no_embedded_ptrs gv'.
Proof.
  intros.
  unfold micmp_int in H.
  destruct (GV2val td gv1); eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
  destruct (GV2val td gv2); eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
Opaque Val.cmp Val.cmpu.
  destruct cop; inv H;
    apply nonptr_no_embedded_ptrs; 
      try solve [auto | apply cmp_isnt_ptr | apply cmpu_isnt_ptr].
Transparent Val.cmp Val.cmpu.
Qed.

Lemma micmp_int_preserves_no_alias: forall td cop gv1 gv2 gv' gv0,
  micmp_int td cop gv1 gv2 = Some gv' -> no_alias gv' gv0.
Proof.
  intros.
  apply no_embedded_ptrs__no_alias.
  apply micmp_int_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma micmp_int_preserves_valid_ptrs: forall td cop gv1 gv2 bd gv',
  micmp_int td cop gv1 gv2 = Some gv' -> valid_ptrs bd gv'.
Proof.
  intros.
  apply no_embedded_ptrs__valid_ptrs.
  apply micmp_int_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma micmp_preserves_no_alias: forall td cop t1 gv1 gv2 gv' gv0,
  micmp td cop t1 gv1 gv2 = Some gv' -> no_alias gv' gv0.
Proof.
  intros.
  unfold micmp in H.
  destruct t1; tinv H; eauto using undef_disjoint_with_ptr.
    eapply micmp_int_preserves_no_alias; eauto.
Qed.

Lemma micmp_preserves_valid_ptrs: forall td cop t1 gv1 gv2 gv' bd,
  micmp td cop t1 gv1 gv2 = Some gv' -> valid_ptrs bd gv'.
Proof.
  intros.
  unfold micmp in H.
  destruct t1; tinv H; eauto using undef_valid_ptrs.
    eapply micmp_int_preserves_valid_ptrs; eauto.
Qed.

Lemma mfcmp_preserves_no_alias: forall td fop fp gv1 gv2 gv' gv0,
  mfcmp td fop fp gv1 gv2 = Some gv' -> no_alias gv' gv0.
Proof.
  intros.
  unfold mfcmp in H.
  destruct (GV2val td gv1); eauto using undef_disjoint_with_ptr.
  destruct v; eauto using undef_disjoint_with_ptr.
  destruct (GV2val td gv2); eauto using undef_disjoint_with_ptr.
  destruct v; eauto using undef_disjoint_with_ptr.
  apply no_embedded_ptrs__no_alias.
  destruct fp; tinv H;
    destruct fop; inv H; apply nonptr_no_embedded_ptrs; 
      try solve [auto | apply Vfalse_isnt_ptr | apply Vtrue_isnt_ptr | 
                 apply val_of_bool_isnt_ptr].
Qed.

Lemma mfcmp_preserves_valid_ptrs: forall td fop fp gv1 gv2 gv' bd,
  mfcmp td fop fp gv1 gv2 = Some gv' -> valid_ptrs bd gv'.
Proof.
  intros.
  unfold mfcmp in H.
  destruct (GV2val td gv1); eauto using undef_valid_ptrs.
  destruct v; eauto using undef_valid_ptrs.
  destruct (GV2val td gv2); eauto using undef_valid_ptrs.
  destruct v; eauto using undef_valid_ptrs.
  apply no_embedded_ptrs__valid_ptrs.
  destruct fp; tinv H;
    destruct fop; inv H; apply nonptr_no_embedded_ptrs; 
      try solve [auto | apply Vfalse_isnt_ptr | apply Vtrue_isnt_ptr | 
                 apply val_of_bool_isnt_ptr].
Qed.

Lemma no_alias_with_blk_split: forall g2 b g1,
  no_alias_with_blk (g1++g2) b -> 
  no_alias_with_blk g1 b /\ no_alias_with_blk g2 b.
Proof.
  induction g1 as [|[]]; simpl; intros; auto.
    destruct v; auto.
    destruct H. apply IHg1 in H0. destruct H0. split; auto.
Qed.

Lemma no_alias_split: forall g2 g1 g,
  no_alias (g1++g2) g -> no_alias g1 g /\ no_alias g2 g.
Proof.
  induction g as [|[]]; simpl; intros; auto.
    destruct v; auto.

    destruct H. apply IHg in H0. destruct H0.
    apply no_alias_with_blk_split in H. destruct H.
    repeat split; auto.
Qed.

Lemma valid_ptrs_split: forall bd g2 g1,
  valid_ptrs bd (g1++g2) -> valid_ptrs bd g1 /\ valid_ptrs bd g2.
Proof.
  induction g1 as [|[]]; simpl; intros; auto.
    destruct v; auto.
    destruct H. apply IHg1 in H0. destruct H0.
    repeat split; auto.
Qed.

Lemma splitGenericValue_preserves_no_alias: forall gv g0 z0 g1 g2,
  no_alias g0 gv ->
  ret (g1, g2) = splitGenericValue g0 z0 ->
  no_alias g1 gv /\ no_alias g2 gv.
Proof.
  induction g0 as [|[]]; simpl; intros.
    destruct (zeq z0 0).
      inv H0. split; apply no_alias_nil.
      destruct (zlt z0 0); tinv H0.

    destruct (zeq z0 0).
      inv H0. split; auto using no_alias_nil.

      destruct (zlt z0 0); tinv H0.
      inv_mbind'. inv H2.
      simpl_env in H.
      apply no_alias_split in H; auto.
      destruct H.
      apply IHg0 in HeqR; auto.
      destruct HeqR. split; auto.
      simpl_env. apply no_alias_app; auto.
Qed.

Lemma splitGenericValue_preserves_valid_ptrs: forall bd g0 z0 g1 g2,
  valid_ptrs bd g0 ->
  ret (g1, g2) = splitGenericValue g0 z0 ->
  valid_ptrs bd g1 /\ valid_ptrs bd g2.
Proof.
  induction g0 as [|[]]; simpl; intros.
    destruct (zeq z0 0).
      inv H0. auto.
      destruct (zlt z0 0); tinv H0.

    destruct (zeq z0 0).
      inv H0. simpl. auto.

      destruct (zlt z0 0); tinv H0.
      inv_mbind'. inv H2.
      simpl_env in H.
      assert (valid_ptrs bd [(v,m)] /\ valid_ptrs bd g0) as J.
        simpl. 
        destruct v; auto.
          destruct H; auto.
      destruct J as [J1 J2].
      apply IHg0 in HeqR; auto.
      destruct HeqR. 
      split; auto.
        simpl_env.
        apply valid_ptrs_app; auto.
Qed.

Lemma extractGenericValue_preserves_no_alias: forall td gv t1 g0 g1 l0,
  no_alias g0 gv -> ret g1 = extractGenericValue td t1 g0 l0 -> no_alias g1 gv.
Proof.
  intros.
  unfold extractGenericValue in *.
  inv_mbind'.
  remember (mget td g0 z t) as R.
  destruct R; eauto using undef_disjoint_with_ptr.
  inv H1.
  unfold mget in HeqR1.
  destruct (getTypeStoreSize td t); tinv HeqR1.
  simpl in HeqR1.
  inv_mbind'. inv H2.
  eapply splitGenericValue_preserves_no_alias in HeqR2; eauto.
  destruct HeqR2.
  eapply splitGenericValue_preserves_no_alias in HeqR1; eauto.
  destruct HeqR1; auto.
Qed.

Lemma extractGenericValue_preserves_valid_ptrs: forall td g1 t1 g0 bd l0,
  valid_ptrs bd g0 -> ret g1 = extractGenericValue td t1 g0 l0 -> 
  valid_ptrs bd g1.
Proof.
  intros.
  unfold extractGenericValue in *.
  inv_mbind'.
  remember (mget td g0 z t) as R.
  destruct R; eauto using undef_valid_ptrs.
  inv H1.
  unfold mget in HeqR1.
  destruct (getTypeStoreSize td t); tinv HeqR1.
  simpl in HeqR1.
  inv_mbind'. inv H2.
  eapply splitGenericValue_preserves_valid_ptrs in HeqR2; eauto.
  destruct HeqR2.
  eapply splitGenericValue_preserves_valid_ptrs in HeqR1; eauto.
  destruct HeqR1; auto.
Qed.

Lemma insertGenericValue_preserves_no_alias: forall td gv t1 t2 g0 g1 g2 l0,
  no_alias g0 gv -> no_alias g1 gv ->
  ret g2 = insertGenericValue td t1 g0 l0 t2 g1 -> no_alias g2 gv.
Proof.
  intros.
  unfold insertGenericValue in *.
  inv_mbind'.
  remember (mset td g0 z t2 g1) as R.
  destruct R; eauto using undef_disjoint_with_ptr.
  inv H2.
  unfold mset in HeqR1.
  destruct (getTypeStoreSize td t2); tinv HeqR1.
  simpl in HeqR1.
  destruct (n =n= length g1); tinv HeqR1.
  inv_mbind'. inv H3.
  eapply splitGenericValue_preserves_no_alias in HeqR2; eauto.
  destruct HeqR2.
  eapply splitGenericValue_preserves_no_alias in HeqR1; eauto.
  destruct HeqR1.
  repeat apply no_alias_app; auto.
Qed.

Lemma insertGenericValue_preserves_valid_ptrs: forall td t1 t2 g0 g1 g2 l0 bd,
  valid_ptrs bd g0 -> valid_ptrs bd g1 ->
  ret g2 = insertGenericValue td t1 g0 l0 t2 g1 -> valid_ptrs bd g2.
Proof.
  intros.
  unfold insertGenericValue in *.
  inv_mbind'.
  remember (mset td g0 z t2 g1) as R.
  destruct R; eauto using undef_valid_ptrs.
  inv H2.
  unfold mset in HeqR1.
  destruct (getTypeStoreSize td t2); tinv HeqR1.
  simpl in HeqR1.
  destruct (n =n= length g1); tinv HeqR1.
  inv_mbind'. inv H3.
  eapply splitGenericValue_preserves_valid_ptrs in HeqR2; eauto.
  destruct HeqR2.
  eapply splitGenericValue_preserves_valid_ptrs in HeqR1; eauto.
  destruct HeqR1.
  repeat apply valid_ptrs_app; auto.
Qed.

Lemma mbop_preserves_no_embedded_ptrs: forall td bop0 sz0 gv1 gv2 gv3,
  mbop td bop0 sz0 gv1 gv2 = Some gv3 -> no_embedded_ptrs gv3.
Proof.
  intros.
  unfold mbop in H.
  destruct (GV2val td gv1); eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
  destruct (GV2val td gv2); eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
  destruct (eq_nat_dec (wz + 1) (Size.to_nat sz0)); 
    eauto using undef__no_embedded_ptrs.
  destruct bop0; inv H;
    apply nonptr_no_embedded_ptrs;
      try solve [apply add_isnt_ptr | apply sub_isnt_ptr | apply mul_isnt_ptr |
                 apply divu_isnt_ptr | apply divs_isnt_ptr | apply modu_isnt_ptr |
                 apply mods_isnt_ptr | apply shl_isnt_ptr | apply shrx_isnt_ptr |
                 apply shr_isnt_ptr | apply and_isnt_ptr | apply or_isnt_ptr |
                 apply xor_isnt_ptr].
Qed.

Lemma mbop_preserves_no_alias: forall td bop0 sz0 gv1 gv2 gv3 gv,
  mbop td bop0 sz0 gv1 gv2 = Some gv3 ->
  no_alias gv3 gv.
Proof.
  intros.
  apply no_embedded_ptrs__no_alias.
  apply mbop_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma mbop_preserves_valid_ptrs: forall td bop0 sz0 gv1 gv2 gv3 bd,
  mbop td bop0 sz0 gv1 gv2 = Some gv3 ->
  valid_ptrs bd gv3.
Proof.
  intros.
  apply no_embedded_ptrs__valid_ptrs.
  apply mbop_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma mfbop_preserves_no_embedded_ptrs: forall td fbop0 fp0 gv1 gv2 gv3,
  mfbop td fbop0 fp0 gv1 gv2 = Some gv3 -> no_embedded_ptrs gv3.
Proof.
  intros.
  unfold mfbop in H.
  destruct (GV2val td gv1); eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
  destruct (GV2val td gv2); eauto using undef__no_embedded_ptrs.
  destruct v; eauto using undef__no_embedded_ptrs.
  destruct fp0; tinv H; destruct fbop0; inv H; simpl; auto.
Qed.

Lemma mfbop_preserves_no_alias: forall td fbop0 fp0 gv1 gv2 gv3 gv0,
  mfbop td fbop0 fp0 gv1 gv2 = Some gv3 -> no_alias gv3 gv0.
Proof.
  intros.
  apply no_embedded_ptrs__no_alias.
  apply mfbop_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma mfbop_preserves_valid_ptrs: forall td fbop0 fp0 gv1 gv2 gv3 bd,
  mfbop td fbop0 fp0 gv1 gv2 = Some gv3 -> valid_ptrs bd gv3.
Proof.
  intros.
  apply no_embedded_ptrs__valid_ptrs.
  apply mfbop_preserves_no_embedded_ptrs in H; auto.
Qed.

Lemma undef_valid_ptrs__disjoint_with_ptr: forall g td t1 blk g'
  (Hc2g : ret g = gundef td t1), no_alias g g' /\ valid_ptrs blk g.
Proof.
  intros.
  split.
    eapply undef_disjoint_with_ptr; eauto.
    eapply undef_valid_ptrs; eauto.
Qed.

Definition const2GV_disjoint_with_runtime_alloca_prop (c:const) := 
  forall maxb gl g td mb t t0
  (Hwfg: wf_globals maxb gl)
  (Hc2g : ret (g, t0) = _const2GV td gl c)
  (Hle: maxb < mb),
  no_alias g ($ blk2GV td mb # typ_pointer t $) /\ valid_ptrs (maxb+1) g.

Definition list_const2GV_disjoint_with_runtime_alloca_prop (lc:list_const) :=
  forall maxb gl td mb t
  (Hwfg: wf_globals maxb gl)
  (Hle: maxb < mb),
  (forall gv, 
    _list_const_arr2GV td gl t lc = Some gv ->
    no_alias gv ($ blk2GV td mb # typ_pointer t $) /\ valid_ptrs (maxb+1) gv
  ) /\
  (forall gv t0, 
    _list_const_struct2GV td gl lc = Some (gv,t0) ->
    no_alias gv ($ blk2GV td mb # typ_pointer t $) /\ valid_ptrs (maxb+1) gv
  ).

Lemma const2GV_disjoint_with_runtime_alloca_mutrec :
  (forall c, const2GV_disjoint_with_runtime_alloca_prop c) *
  (forall lc, list_const2GV_disjoint_with_runtime_alloca_prop lc).
Proof.
  apply const_mutrec; 
    unfold const2GV_disjoint_with_runtime_alloca_prop, 
           list_const2GV_disjoint_with_runtime_alloca_prop;
    intros; simpl in *; eauto; inv_mbind'.
Case "zero".
  eapply zeroconst2GV_disjoint_with_runtime_alloca; eauto.
Case "int".
  rewrite simpl_blk2GV. inv Hc2g. simpl. auto.
Case "float".
  rewrite simpl_blk2GV. destruct f; inv Hc2g; simpl; auto.
Case "undef".
  eapply undef_valid_ptrs__disjoint_with_ptr with (t1:=t)(td:=td); auto.
Case "null".
  inv Hc2g. simpl. 
  destruct Hwfg. 
  split.
    apply null_disjoint_with_ptr. omega.
    apply null_valid_ptrs. omega.
Case "arr". 
  eapply H with (td:=td)(gl:=gl)(t:=t) in Hle; eauto.
  destruct Hle.
  destruct (length (unmake_list_const l0)); inv H1; 
    eauto using uninits_valid_ptrs__disjoint_with_ptr.
Case "struct". 
  eapply H with (td:=td)(gl:=gl)(t:=t) in Hle; eauto.
  destruct Hle. 
  destruct g0; inv H1; 
    eauto using uninits_valid_ptrs__disjoint_with_ptr.
Case "gid".
  eapply wf_globals_disjoint_with_runtime_alloca; eauto.
Case "trunc". 
  split. 
    eapply mtrunc_preserves_no_alias; eauto.
    eapply mtrunc_preserves_valid_ptrs; eauto.
Case "ext". 
  split. 
    eapply mext_preserves_no_alias; eauto.
    eapply mext_preserves_valid_ptrs; eauto.
Case "cast". 
  eapply H in HeqR; eauto. destruct HeqR.
  split.
    eapply mcast_preserves_no_alias; eauto.
    eapply mcast_preserves_valid_ptrs; eauto.
Case "gep". 
  destruct t1; tinv H2. 
  inv_mbind'.
  remember (GV2ptr td (getPointerSize td) g0) as R1.
  remember (gundef td t2) as R3.
  destruct R1.
    destruct (intConsts2Nats td l0).
      remember (mgep td t1 v l1) as R2.
      destruct R2.
        inv H3. 
        eapply H with (t:=t) in HeqR; eauto.
        destruct HeqR as [J1 J2].
        split.
          eapply GV2ptr_preserves_no_alias in HeqR1; eauto.
          eapply mgep_preserves_no_alias; eauto.

          eapply GV2ptr_preserves_valid_ptrs in HeqR1; eauto.
          eapply mgep_preserves_valid_ptrs; eauto.

        destruct R3; inv H3; eauto using undef_valid_ptrs__disjoint_with_ptr.
      destruct R3; inv H3; eauto using undef_valid_ptrs__disjoint_with_ptr.
    destruct R3; inv H3; eauto using undef_valid_ptrs__disjoint_with_ptr.

Case "select". destruct (isGVZero td g0); inv H3; eauto.
Case "icmp". 
  split.
    eapply micmp_preserves_no_alias; eauto.
    eapply micmp_preserves_valid_ptrs; eauto.
Case "fcmp". 
  destruct t1; tinv H2. inv_mbind'.
  split.
    eapply mfcmp_preserves_no_alias; eauto.
    eapply mfcmp_preserves_valid_ptrs; eauto.
Case "extractValue". 
  eapply H in HeqR; eauto.
  destruct HeqR.
  split.
    eapply extractGenericValue_preserves_no_alias in HeqR1; eauto.
    eapply extractGenericValue_preserves_valid_ptrs in HeqR1; eauto.
Case "insertValue". 
  eapply H with (t:=t) in HeqR; eauto. clear H.
  eapply H0 with (t:=t) in HeqR0; eauto. clear H0 H1.
  destruct HeqR. destruct HeqR0.
  split.
    eapply insertGenericValue_preserves_no_alias in HeqR1; eauto.
    eapply insertGenericValue_preserves_valid_ptrs in HeqR1; eauto.
Case "bop". 
  destruct t1; tinv H2. inv_mbind'.
  split.
    eapply mbop_preserves_no_alias; eauto.
    eapply mbop_preserves_valid_ptrs; eauto.
Case "fbop". 
  destruct t1; tinv H2. inv_mbind'.
  split.
    eapply mfbop_preserves_no_alias; eauto.
    eapply mfbop_preserves_valid_ptrs; eauto.
Case "nil".
  split.
    intros gv J. inv J. simpl. auto using no_alias_nil.
    intros gv t0 J. inv J. simpl. auto using no_alias_nil.
Case "cons".
  split; intros; inv_mbind'. 
    destruct p. 
    destruct (typ_dec t t0); tinv H2.
    inv_mbind'.
    eapply H with (t:=t0) in HeqR0; eauto.
    eapply H0 with (t:=t0)(td:=td) in Hwfg; eauto.
    destruct Hwfg. symmetry in HeqR. apply H1 in HeqR.
    destruct HeqR0. destruct HeqR.
    split.
      apply no_alias_app.
        apply no_alias_app; auto.
        apply uninits_disjoint_with_ptr.
      apply valid_ptrs_app.
        apply valid_ptrs_app; auto.
        apply uninits_valid_ptrs.

    destruct p. inv_mbind'. 
    destruct p. inv_mbind'. 
    eapply H with (t:=t) in HeqR0; eauto.
    eapply H0 with (t:=t)(td:=td) in Hwfg; eauto.
    destruct Hwfg. symmetry in HeqR. apply H2 in HeqR.
    destruct HeqR0. destruct HeqR.
    split.
      apply no_alias_app; auto.
      apply no_alias_app; auto.
      apply uninits_disjoint_with_ptr.

      apply valid_ptrs_app; auto.
      apply valid_ptrs_app; auto.
      apply uninits_valid_ptrs.
Qed.

Lemma cgv2gvs_preserves_no_alias: forall g0 td mb t t0 maxb,
  no_alias g0 ($ blk2GV td mb # typ_pointer t $) ->
  0 <= maxb < mb ->
  no_alias (cgv2gvs DGVs g0 t0) ($ blk2GV td mb # typ_pointer t $).
Proof.
  intros.
Local Transparent cgv2gvs.
  unfold cgv2gvs. simpl. unfold MDGVs.cgv2gvs. unfold cgv2gv.
  destruct g0 as [|[]]; auto.
  destruct v; auto.
  destruct g0 as [|]; auto.

  unfold cundef_gv.
  rewrite simpl_blk2GV.
  destruct t0; auto.
    destruct f; auto.

    rewrite <- simpl_blk2GV with (t:=t0).
    apply null_disjoint_with_ptr. omega.
Qed.

Lemma const2GV_disjoint_with_runtime_alloca: forall c0 maxb gl g td mb t
  (Hwfg: wf_globals maxb gl)
  (Hc2g : ret g = @Opsem.const2GV DGVs td gl c0)
  (Hle: maxb < mb),
  no_alias g ($ blk2GV td mb # typ_pointer t $).
Proof.
  unfold Opsem.const2GV.
  intros.
  inv_mbind'. inv H0.
  destruct const2GV_disjoint_with_runtime_alloca_mutrec as [J1 J2].
  unfold const2GV_disjoint_with_runtime_alloca_prop in J1. 
  eapply J1 with (t:=t) in HeqR; eauto.
  destruct HeqR. 
  destruct Hwfg.
  eapply cgv2gvs_preserves_no_alias; eauto.
Qed.

Lemma cgv2gvs_preserves_valid_ptrs: forall g0 t0 bd,
  bd > 0 -> valid_ptrs bd g0 -> valid_ptrs bd (cgv2gvs DGVs g0 t0).
Proof.
  intros.
Local Transparent cgv2gvs.
  unfold cgv2gvs. simpl. unfold MDGVs.cgv2gvs. unfold cgv2gv.
  destruct g0 as [|[]]; auto.
  destruct v; auto.
  destruct g0 as [|]; auto.
  unfold cundef_gv.
  destruct t0; auto.
    destruct f; auto.

    apply null_valid_ptrs; auto.
Qed.

Lemma const2GV_valid_ptrs: forall c0 maxb gl g td 
  (Hwfg: wf_globals maxb gl)
  (Hc2g : ret g = @Opsem.const2GV DGVs td gl c0),
  valid_ptrs (maxb + 1) g.
Proof.
  unfold Opsem.const2GV.
  intros.
  inv_mbind'. inv H0.
  destruct const2GV_disjoint_with_runtime_alloca_mutrec as [J1 J2].
  unfold const2GV_disjoint_with_runtime_alloca_prop in J1. 
  eapply J1 with (t:=t)(mb:=maxb+1) in HeqR; eauto; try omega.
  destruct HeqR. 
  destruct Hwfg.
  eapply cgv2gvs_preserves_valid_ptrs; eauto; try omega.
Qed.

Definition inscope_of_EC (ec:@Opsem.ExecutionContext DGVs) : option (list id) :=
let '(Opsem.mkEC f b cs tmn _ _) := ec in inscope_of_pc f b cs tmn.

Lemma preservation_return_helper: forall (g : GVsT DGVs) pinfo lc' Mem'
  als' td maxb Mem ECs lc gl t Result
  (HeqR1 : ret g = Opsem.getOperandValue td Result lc gl)
  (g0 : GVsT DGVs)
  (HeqR2 : ret g0 = lift_op1 DGVs (fit_gv td t) g t)
  (Hwfg : wf_globals maxb gl)
  (l0 : list atom) EC
  (Heq1 : Opsem.CurFunction EC = PI_f pinfo)
  (Heq2 : Opsem.Locals EC = lc')
  (Hfr1 : wf_ECStack_head_tail maxb pinfo td Mem lc (EC :: ECs))
  (Hinscp: inscope_of_EC EC = Some l0)
  (Hinscope2 : wf_defs maxb pinfo td Mem' lc' l0 als')
  (gvsa : GVsT DGVs)
  (Hpindom : In (PI_id pinfo) l0)
  (Hlkp : lookupAL (GVsT DGVs) lc' (PI_id pinfo) = ret gvsa),
  no_alias g0 gvsa.
Proof.
  intros.
  assert (Hlkp':=Hlkp).
  apply Hinscope2 in Hlkp'; auto.
  destruct Hlkp' as [[[mb [EQ [Hin Hbound]]] _] _]; subst.
  assert (In EC (EC::ECs)) as Hin'. simpl. auto.
  apply Hfr1 in Hin'. clear Hfr1.
  destruct EC. simpl in *.
  eapply Hin' in Hlkp; eauto. clear Hin'.
  destruct Hlkp as [_ [G _]].
  Local Transparent lift_op1. simpl in HeqR2.
  unfold MDGVs.lift_op1, fit_gv in HeqR2.
  destruct (getTypeSizeInBits td t); tinv HeqR2.
  destruct (sizeGenericValue g =n= nat_of_Z (ZRdiv (Z_of_nat n) 8)).
    inv HeqR2.
    destruct Result; simpl in HeqR1; eauto.            
    eapply const2GV_disjoint_with_runtime_alloca; eauto.
      omega.
  
    eapply undef_disjoint_with_ptr; eauto.
Qed.

Lemma wf_als_split: forall maxb M als als',
  wf_als maxb M (als++als') -> wf_als maxb M als /\ wf_als maxb M als'.
Proof.
  intros.
  destruct H as [J1 J2].
  apply NoDup_split in J1.
  destruct J1 as [J11 J12].
  split.
    split; auto.
      intros. apply J2. apply in_or_app; auto.
    split; auto.
      intros. apply J2. apply in_or_app; auto.
Qed.

Ltac SSSSSCase name := Case_aux subsubsubsubsubcase name.
Ltac SSSSSSCase name := Case_aux subsubsubsubsubsubcase name.

Lemma load_free': forall (blk : Values.block) (lo : Z) (hi : Z) 
  (b : Values.block) (Mem : Memory.mem) (Mem' : Memory.mem)
  (Hfree : Mem.free Mem blk lo hi = ret Mem')
  (a : AST.memory_chunk) (ofs : Z) (v : val)
  (HeqR : ret v = Mem.load a Mem' b ofs),
  b <> blk \/ lo >= hi \/ ofs + size_chunk a <= lo \/ hi <= ofs.
Proof.
  intros.
  symmetry in HeqR.
  apply Mem.load_valid_access in HeqR.
  destruct (zeq b blk); subst; auto.
  right.
  destruct (zlt lo hi); try omega.
  destruct (zle (ofs + size_chunk a) lo); auto.
  destruct (zle hi ofs); auto.
  contradict HeqR.
  eapply Mem.valid_access_free_2 in Hfree; eauto; try omega.
Qed.      

Lemma free_preserves_mload_aux_inv: forall blk lo hi b Mem Mem' 
  (Hfree:Mem.free Mem blk lo hi = ret Mem') mc ofs gvsa,
  mload_aux Mem' mc b ofs = ret gvsa ->
  mload_aux Mem mc b ofs = ret gvsa.
Proof.
  induction mc; simpl; intros; auto.
    inv_mbind'. symmetry in HeqR0.
    apply IHmc in HeqR0.
    rewrite HeqR0.
    erewrite <- Mem.load_free; eauto.
      rewrite <- HeqR. auto.
      eapply load_free'; eauto.
Qed.

Lemma free_preserves_mload_inv: forall TD Mem' gptr ty al gvsa Mem mptr0
  (H1 : mload TD Mem' gptr ty al = ret gvsa)
  (H2 : free TD Mem mptr0 = ret Mem'),
  mload TD Mem gptr ty al = ret gvsa.
Proof.
  intros.
  apply mload_inv in H1.
  destruct H1 as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold mload. simpl. rewrite J2.
  apply free_inv in H2.
  destruct H2 as [blk' [ofs' [hi [lo [J4 [J5 [J6 J7]]]]]]].
  eapply free_preserves_mload_aux_inv; eauto.
Qed.

Lemma nextblock_free: forall TD M gv M', 
  free TD M gv = ret M' -> Mem.nextblock M = Mem.nextblock M'.
Proof.  
  intros.
  apply free_inv in H.
  destruct H as [blk' [ofs' [hi [lo [J4 [J5 [J6 J7]]]]]]].
  apply Mem.nextblock_free in J7. auto.
Qed.

Lemma free_preserves_wf_ECStack_head_tail : forall maxb pinfo TD M M' lc mptr0
  (Hfree: free TD M mptr0 = ret M') ECs 
  (Hwf: wf_ECStack_head_tail maxb pinfo TD M lc ECs),
  wf_ECStack_head_tail maxb pinfo TD M' lc ECs.
Proof.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros. destruct ec0. intros.
  eapply Hwf in H; eauto. clear Hwf.
  eapply H in H2; eauto. clear H.
  destruct H2 as [[mb [J11 J12]] [J2 J3]]; subst.
  split.
    exists mb. split; auto. 
    erewrite <- nextblock_free; eauto.
  split; auto.
    intros.
    eapply free_preserves_mload_inv in H; eauto.
Qed.

Lemma free_preserves_wf_lc: forall TD Mem' Mem mptr0
  (H2 : free TD Mem mptr0 = ret Mem') lc
  (Hwf: wf_lc Mem lc),
  wf_lc Mem' lc.
Proof.
  unfold wf_lc.
  intros.
  apply Hwf in H.
  apply free_inv in H2.
  destruct H2 as [blk' [ofs' [hi [lo [J4 [J5 [J6 J7]]]]]]].
  erewrite Mem.nextblock_free; eauto.
Qed.

Lemma free_preserves_mload_aux: forall Mem blk lo hi Mem' b
  (Hfree: Mem.free Mem blk lo hi = ret Mem') (Hneq: blk <> b) mc ofs gv,
  mload_aux Mem mc b ofs = ret gv ->
  mload_aux Mem' mc b ofs = ret gv.
Proof.
  induction mc; simpl; intros; auto.
    inv_mbind'. symmetry in HeqR0.
    apply IHmc in HeqR0.
    rewrite HeqR0.
    erewrite Mem.load_free; eauto.
      rewrite <- HeqR. auto.
Qed.

Lemma free_preserves_mload: forall TD Mem Mem' t al gv gptr gvsa
  (H0 : no_alias gptr gvsa)
  (H1 : free TD Mem gptr = ret Mem')
  (H2 : mload TD Mem gvsa t al = ret gv),
  mload TD Mem' gvsa t al = ret gv.
Proof.
  intros.
  apply free_inv in H1.
  destruct H1 as [blk [ofs [hi [lo [J4 [J5 [J6 J7]]]]]]].
  apply mload_inv in H2.
  destruct H2 as [b [ofs' [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold mload. simpl. rewrite J2.
  symmetry in J4.
  apply GV2ptr_inv in J4.
  destruct J4 as [b1 [ofs1 [m1 [J8 J9]]]]; subst.
  inv J9.
  simpl in H0. destruct H0. destruct H. clear H1 H0.
  eapply free_preserves_mload_aux in J3; eauto.
Qed.

Lemma operand__no_alias_with__tail: forall maxb pinfo TD M lc1 lc2 mptr0 gl
  (Hwfgl : wf_globals maxb gl) v mptrs EC
  (Heq1: Opsem.CurFunction EC = PI_f pinfo)
  (Heq2: Opsem.Locals EC = lc2)
  (Hht : wf_ECStack_head_in_tail maxb pinfo TD M lc1 EC)
  (gvsa : GVsT DGVs) (Hin: mptr0 @ mptrs) ids0
  (Heq3 : inscope_of_EC EC = Some ids0)
  (Hin: In (PI_id pinfo) ids0)
  (Hlkp : lookupAL (GVsT DGVs) lc2 (PI_id pinfo) = ret gvsa)
  (Hgetop : Opsem.getOperandValue TD v lc1 gl = ret mptrs),
  no_alias mptr0 gvsa.
Proof.
  intros.
  inv Hin. destruct EC. simpl in *.
  eapply Hht in Hlkp; eauto. clear Hht.
  destruct Hlkp as [[mb [J11 J12]] [Hlkp _]]; subst.
  destruct v; simpl in Hgetop.
    apply Hlkp in Hgetop; auto.
    eapply const2GV_disjoint_with_runtime_alloca; eauto.
      omega.
Qed.

Definition wf_use_at_head (pinfo:PhiInfo) (ids0:list id) (v:value) :=
used_in_value (PI_id pinfo) v = false /\
match v with
| value_const _ => True
| value_id vid => In vid ids0
end.

Lemma free_preserves_wf_defs_in_tail : forall maxb pinfo TD M  
  M' lc1 mptr0 mptrs gl v als lc2 
  (Hgetop: Opsem.getOperandValue TD v lc1 gl = ret mptrs)
  (Hin: mptr0 @ mptrs) (Hwfgl: wf_globals maxb gl)
  (Hfree: free TD M mptr0 = ret M') EC
  (Heq1: Opsem.CurFunction EC = PI_f pinfo)
  (Heq2: Opsem.Locals EC = lc2)
  (Hht: wf_ECStack_head_in_tail maxb pinfo TD M lc1 EC)
  ids0 (Heq3 : inscope_of_EC EC = Some ids0)
  (Hwf: wf_defs maxb pinfo TD M lc2 ids0 als),
  wf_defs maxb pinfo TD M' lc2 ids0 als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    clear J2.
    destruct J1 as [[mb [J11 [J12 J13]]] [J4 [gv J3]]]; subst.
    split.
      erewrite <- nextblock_free; eauto.
    split.
        intros. eapply free_preserves_mload_inv in H; eauto.
        clear J4. 
        assert (no_alias mptr0 ($ blk2GV TD mb # typ_pointer (PI_typ pinfo) $)) 
          as J.
          eapply operand__no_alias_with__tail; eauto.
        exists gv. eapply free_preserves_mload; eauto.
Qed.

Lemma operand__no_alias_with__head: forall maxb pinfo TD lc mptr0 mptrs gl v als
  (Hgetop : Opsem.getOperandValue TD v lc gl = ret mptrs)
  (Hin : mptr0 @ mptrs) (Hwfgl : wf_globals maxb gl) ids0 M
  (Hwfu: wf_use_at_head pinfo ids0 v) (Hwf: wf_defs maxb pinfo TD M lc ids0 als)
  (gvsa : GVsT DGVs) (Hpindom : In (PI_id pinfo) ids0)
  (Hlkp : lookupAL (GVsT DGVs) lc (PI_id pinfo) = ret gvsa),
  no_alias mptr0 gvsa.
Proof.
  intros.
  apply Hwf in Hlkp; auto.
  destruct Hlkp as [[J1 [J4 [gv J3]]] J2].
  inv Hin.
  destruct v; simpl in Hgetop.
    destruct Hwfu as [Hwfu1 Hwfu2].        
    apply J2 in Hgetop; auto.
    unfold wf_non_alloca_GVs in Hgetop.
    destruct (id_dec i0 (PI_id pinfo)); subst; auto.
      inv Hwfu1. 
      destruct (id_dec (PI_id pinfo) (PI_id pinfo)); try congruence.
        inv H0.
  
    destruct J1 as [mb [J11 [J12 J13]]]; subst.
    eapply const2GV_disjoint_with_runtime_alloca; eauto.
      omega.
Qed.

Lemma free_preserves_wf_defs_at_head : forall maxb pinfo TD M  
  M' lc mptr0 mptrs gl v als
  (Hgetop: Opsem.getOperandValue TD v lc gl = ret mptrs)
  (Hin: mptr0 @ mptrs) (Hwfgl: wf_globals maxb gl)
  (Hfree: free TD M mptr0 = ret M')
  ids0 (Hwfu: wf_use_at_head pinfo ids0 v) 
  (Hwf: wf_defs maxb pinfo TD M lc ids0 als),
  wf_defs maxb pinfo TD M' lc ids0 als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  assert (no_alias mptr0 gvsa) as J.
    eapply operand__no_alias_with__head; eauto.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    destruct J1 as [[mb [J11 [J12 J13]]] [J4 [gv J3]]]; subst.
    split.
        erewrite <- nextblock_free; eauto.
    split.
        intros. eapply free_preserves_mload_inv in H; eauto.
        exists gv. eapply free_preserves_mload; eauto.
Qed.

Lemma wf_ECStack_head_tail_cons__inv: forall maxb pinfo TD M lc ec1 ecs2,
  wf_ECStack_head_tail maxb pinfo TD M lc (ec1::ecs2) ->
  wf_ECStack_head_in_tail maxb pinfo TD M lc ec1 /\
  wf_ECStack_head_tail maxb pinfo TD M lc ecs2.
Proof.
  intros.
  split.
    apply H; simpl; auto.
    unfold wf_ECStack_head_tail in *. intros. apply H; simpl; auto.
Qed.

Lemma impure_cmd_preserves_wf_EC_tail : forall maxb pinfo TD M  
  M' EC (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfdefs: forall ids0,
     let '(Opsem.mkEC F B cs tmn lc als) := EC in
     F = (PI_f pinfo) ->
     inscope_of_pc F B cs tmn = Some ids0 ->
     wf_defs maxb pinfo TD M lc ids0 als ->
     wf_defs maxb pinfo TD M' lc ids0 als)
  (Hwflc: wf_lc M (@Opsem.Locals DGVs EC) -> wf_lc M' (Opsem.Locals EC))
  (Hwf: wf_ExecutionContext maxb pinfo TD M EC),
  wf_ExecutionContext maxb pinfo TD M' EC.
Proof.
  destruct EC. simpl. intros.
  destruct Hwf as [J1 J2].
  split; auto.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    unfold inscope_of_pc in *.
    destruct CurCmds.    
      remember (inscope_of_tmn (PI_f pinfo) CurBB Terminator) as R.
      destruct R; auto.

      remember (inscope_of_cmd (PI_f pinfo) CurBB c) as R.
      destruct R; auto.
Qed.

Lemma free_preserves_wf_ECStack_in_tail : forall maxb pinfo TD M  
  M' mptr0 mptrs gl v (Hwfpi: WF_PhiInfo pinfo) lc
  (Hgetop: Opsem.getOperandValue TD v lc gl = ret mptrs)
  (Hin: mptr0 @ mptrs) (Hwfgl: wf_globals maxb gl)
  (Hfree: free TD M mptr0 = ret M') ECs
  (Hht: wf_ECStack_head_tail maxb pinfo TD M lc ECs)
  (Hwf: wf_ECStack maxb pinfo TD M ECs),
  wf_ECStack maxb pinfo TD M' ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct Hwf as [J1 [J2 J3]].
    apply wf_ECStack_head_tail_cons__inv in Hht.
    destruct Hht as [Hht1 Hht2].
    split.
      eapply impure_cmd_preserves_wf_EC_tail with (M:=M); eauto.
        destruct a. intros. subst.
        eapply free_preserves_wf_defs_in_tail; eauto; simpl; auto.
        eapply free_preserves_wf_lc; eauto.
    split; auto.
      eapply free_preserves_wf_ECStack_head_tail; eauto.
(* Can this lemma be more generic by making free_preserves_mload_inv generic? *)
Qed.

Lemma free_preserves_wf_Mem : forall maxb TD M M' mptr0
  (Hfree: free TD M mptr0 = ret M') 
  (Hwf: wf_Mem maxb TD M),
  wf_Mem maxb TD M'.
Proof.
  intros. destruct Hwf as [J1 J2].
  unfold wf_Mem.
  erewrite <- nextblock_free; eauto.
  split; auto.
    intros. 
    eapply free_preserves_mload_inv in H; eauto.
Qed.

Lemma free_preserves_wf_als : forall maxb TD M M' mptr0 als
  (Hfree: free TD M mptr0 = ret M') 
  (Hwf: wf_als maxb M als),
  wf_als maxb M' als.
Proof.
  intros. destruct Hwf as [J1 J2].
  split; auto.
    intros. 
    apply J2 in H.
    erewrite <- nextblock_free; eauto.
Qed.

Lemma free_allocas_preserves_mload_inv: forall TD gptr ty al gvsa als Mem' Mem
  (H1 : mload TD Mem' gptr ty al = ret gvsa)
  (H2 : free_allocas TD Mem als = ret Mem'),
  mload TD Mem gptr ty al = ret gvsa.
Proof.
  induction als; simpl; intros.
    inv H2. auto.

    inv_mbind.
    eapply free_preserves_mload_inv with (Mem':=m); eauto.
Qed.

Lemma free_allocas_preserves_mload: forall TD al t mb gv als Mem' Mem 
  (H0 : ~ In mb als)
  (H1 : free_allocas TD Mem als = ret Mem')
  (H2 : mload TD Mem ($ blk2GV TD mb # typ_pointer t $) t al = ret gv),
  mload TD Mem' ($ blk2GV TD mb # typ_pointer t $) t al = ret gv.
Proof.
  induction als; simpl; intros.
    inv H1. auto.

    inv_mbind.
    apply IHals in H3; auto.
    eapply free_preserves_mload; eauto.
    unfold_blk2GV. 
Local Transparent gv2gvs.
  unfold gv2gvs. simpl. split; auto.
Opaque gv2gvs. 
Qed.

Lemma nextblock_free_allocas: forall TD als M M', 
  free_allocas TD M als = ret M' -> Mem.nextblock M = Mem.nextblock M'.
Proof.  
  induction als; simpl; intros.  
    inv H. auto.

    inv_mbind'. symmetry in HeqR.
    apply nextblock_free in HeqR; auto.
    rewrite HeqR. auto.
Qed.

Lemma free_allocas_preserves_wf_alloca: forall maxb pinfo TD Mem gvsa als0 als Mem',
  wf_alloca_GVs maxb pinfo TD Mem gvsa als0 ->
  NoDup (als ++ als0) ->
  free_allocas TD Mem als = ret Mem' ->
  wf_alloca_GVs maxb pinfo TD Mem' gvsa als0.
Proof.
  intros.
  unfold wf_alloca_GVs in *.
  destruct H as [[mb [J11 [J12 J13]]] [J2 J3]]; subst.
  split.
    erewrite <- nextblock_free_allocas; eauto.
  split.
    intros gptr gvs1 ty al J.  
    eapply free_allocas_preserves_mload_inv in J; eauto.

    destruct J3 as [gv J3].
    exists gv.
    eapply free_allocas_preserves_mload; eauto.
    eapply NoDup_disjoint in H0; eauto.
Qed.

Lemma free_allocas_preserves_wf_defs: forall maxb pinfo TD Mem lc' l0 als0 als Mem',
  wf_defs maxb pinfo TD Mem lc' l0 als0 ->
  NoDup (als ++ als0) ->
  free_allocas TD Mem als = ret Mem' ->
  wf_defs maxb pinfo TD Mem' lc' l0 als0.
  (* This is only true if als is always disjoint with pinfo.id *) 
Proof.
  intros. unfold wf_defs in *. intros.
  apply H in Hlkp; auto. clear H.
  destruct Hlkp as [J1 J2]. 
  split; eauto using free_allocas_preserves_wf_alloca.
Qed.

Lemma free_allocas_preserves_wf_lc: forall td lc als Mem Mem',
  free_allocas td Mem als = ret Mem' -> wf_lc Mem lc -> wf_lc Mem' lc.
Proof.
  induction als; simpl; intros.
    inv H. auto.

    inv_mbind. symmetry in HeqR.
    eapply free_preserves_wf_lc in HeqR; eauto.
Qed.

Lemma updateAddAL__wf_lc: forall gv3 Mem0 lc id0
  (Hwfgv: valid_ptrs (Mem.nextblock Mem0) gv3) (Hwflc: wf_lc Mem0 lc),
  wf_lc Mem0 (updateAddAL (GVsT DGVs) lc id0 gv3).
Proof.
  intros. unfold wf_lc in *. intros.
  destruct (id_dec id0 id1); subst.
    rewrite lookupAL_updateAddAL_eq in H. inv H. eauto.

    rewrite <- lookupAL_updateAddAL_neq in H; auto.
    eapply Hwflc; eauto.
Qed.

Lemma valid_ptrs__trans: forall bound1 bound2 gv,
  valid_ptrs bound1 gv -> bound1 <= bound2 -> valid_ptrs bound2 gv.
Proof.
  induction gv as [|[]]; simpl; intros; auto.
    destruct v; auto.
      destruct H. split; auto. omega.
Qed.

Lemma operand__lt_nextblock: forall maxb TD M (lc:DGVMap) mptr gl
  (Hwfgl : wf_globals maxb gl) v mptrs (Hlt: maxb < Mem.nextblock M)
  (Hwflc: wf_lc M lc) 
  (Hin: mptr @ mptrs) 
  (Hgetop : Opsem.getOperandValue TD v lc gl = ret mptrs),
  valid_ptrs (Mem.nextblock M) mptr.
Proof.
  intros.
  inv Hin.
  destruct v; simpl in Hgetop.
    apply Hwflc in Hgetop; auto.

    eapply const2GV_valid_ptrs in Hwfgl; eauto.
    eapply valid_ptrs__trans; eauto.
      omega.
Qed.     

Lemma returnUpdateLocals__wf_lc: forall maxb td Result (lc:DGVMap) gl c' 
  lc' Mem lc''
  (H1 : Opsem.returnUpdateLocals td c' Result lc lc' gl = ret lc'')
  (Hwflc1 : wf_lc Mem lc) (Hwflc2 : wf_lc Mem lc')
  (Hwfg : wf_globals maxb gl) (Hgbound : maxb < Mem.nextblock Mem),
  wf_lc Mem lc''.
Proof.
  intros.
  unfold Opsem.returnUpdateLocals in H1.
  inv_mbind. 
  destruct c'; tinv H0.
  destruct n.
    inv H0; auto.

    destruct t; tinv H0.
    inv_mbind. 
    apply updateAddAL__wf_lc; auto.
    intros. subst. symmetry in HeqR.
    unfold MDGVs.lift_op1, fit_gv in HeqR0. symmetry in HeqR0.
    inv_mbind. 
    destruct (sizeGenericValue g =n= nat_of_Z (ZRdiv (Z_of_nat n) 8)).
      inv H0. 
      eapply operand__lt_nextblock in HeqR; eauto.

      unfold gundef in H0. inv_mbind. simpl. auto.
Qed.

Lemma free_allocas_preserves_wf_ECStack_head_tail' : forall maxb pinfo td 
  lc ECs als M M',
  free_allocas td M als = ret M' ->
  wf_ECStack_head_tail maxb pinfo td M lc ECs ->
  wf_ECStack_head_tail maxb pinfo td M' lc ECs.
Proof.
  induction als; simpl; intros.
    inv H. auto.

    inv_mbind.
    symmetry in HeqR.
    eapply free_preserves_wf_ECStack_head_tail in HeqR; eauto.
Qed.

Lemma free_allocas_preserves_wf_defs_in_tail : forall maxb pinfo TD
  lc2 ids0 als' als M M' (Hfree: free_allocas TD M als = ret M')
  (Hndp: NoDup (als++als')) (Hwf: wf_defs maxb pinfo TD M lc2 ids0 als'),
  wf_defs maxb pinfo TD M' lc2 ids0 als'.
Proof.
  induction als; simpl; intros.
    inv Hfree. auto.

    inv_mbind. inv Hndp.
    apply IHals in H0; auto.

  unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    clear J2.
    destruct J1 as [[mb [J11 [J12 J13]]] [J4 [gv J3]]]; subst.
    split.
        erewrite <- nextblock_free; eauto.
    split.
        intros. eapply free_preserves_mload_inv in H; eauto.
        exists gv. 
        assert (no_alias (blk2GV TD a) 
                         ($ blk2GV TD mb # typ_pointer (PI_typ pinfo) $)) 
          as Hnoalias.
          apply Hwf in Hlkp; auto.
          destruct Hlkp as [[[mb' [J5 [J6 J7]]] _] _].
Local Transparent gv2gvs.
          unfold gv2gvs in J5. simpl in J5. unfold MDGVs.gv2gvs in J5.
          unfold blk2GV, ptr2GV, val2GV in J5. inv J5.
          unfold_blk2GV. unfold gv2gvs. simpl.
Opaque gv2gvs. 
          repeat split; auto.
          intro EQ. subst. apply H2. apply in_or_app; auto.

        eapply free_preserves_mload; eauto.
Qed.

Lemma free_allocas_preserves_wf_ECStack: forall maxb pinfo td als ECs Mem Mem'
  (Hwfpi: WF_PhiInfo pinfo)
  (Hndup: NoDup (als ++ (flat_map
                  (fun ec : Opsem.ExecutionContext =>
                   let '{| Opsem.Allocas := als |} := ec in als)
                   ECs)))
  (Hwf: wf_ECStack maxb pinfo td Mem ECs)
  (Hfrees: free_allocas td Mem als = ret Mem'),
  wf_ECStack maxb pinfo td Mem' ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct Hwf as [J1 [J2 J3]].
    destruct a. 
    assert (Hndup' := Hndup).
    apply NoDup_strenthening in Hndup.
    split.
      eapply impure_cmd_preserves_wf_EC_tail with (M:=Mem); eauto.
        intros. subst.
        rewrite_env ((als ++ Allocas) ++
          flat_map
            (fun ec : Opsem.ExecutionContext =>
             let '{| Opsem.Allocas := als |} := ec in als) ECs) in Hndup'.
        apply NoDup_split in Hndup'. destruct Hndup'.
        eapply free_allocas_preserves_wf_defs_in_tail; eauto.
        eapply free_allocas_preserves_wf_lc; eauto.
    split; eauto.
      eapply free_allocas_preserves_wf_ECStack_head_tail'; eauto.
(* Can this lemma be more generic by making free_preserves_mload_inv generic? *)
Qed.

Lemma updateAddAL__wf_ECStack_head_tail: forall maxb pinfo td M lc ECs
  id0 gv3 
  (Hwfgv: forall ec0 (Hin : In ec0 ECs) (gvsa : GVsT DGVs) ids0
    (Hscp: inscope_of_EC ec0 = Some ids0) (Hin1: In (PI_id pinfo) ids0)
    (Heq : Opsem.CurFunction ec0 = PI_f pinfo)
    (Hlkup : lookupAL (GVsT DGVs) (Opsem.Locals ec0) (PI_id pinfo) = ret gvsa),
    no_alias gv3 gvsa),
  wf_ECStack_head_tail maxb pinfo td M lc ECs ->
  wf_ECStack_head_tail maxb pinfo td M (updateAddAL (GVsT DGVs) lc id0 gv3) ECs.
Proof.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail in *.
  intros. destruct ec0. intros.
  assert (H0':=H0). eapply Hwfgv in H0'; eauto. clear Hwfgv.
  apply H in H0; auto. clear H. 
  eapply H0 in H4; eauto. clear H0.
  destruct H4 as [J1 [J2 J3]].
  split; auto.
  split; auto.
    intros. 
    destruct (id_dec id0 id1); subst.
      rewrite lookupAL_updateAddAL_eq in H.
      inv H. auto.

      rewrite <- lookupAL_updateAddAL_neq in H; eauto.
Qed.

Lemma free_allocas_preserves_wf_ECStack_head_tail : forall maxb pinfo td M M' 
  lc als lc' F' lc'' ECs gl Result c' EC
  (Heq1: Opsem.CurFunction EC = F') (Heq2: Opsem.Locals EC = lc')
  (Hwfg : wf_globals maxb gl),
  free_allocas td M als = ret M' ->
  Opsem.returnUpdateLocals td c' Result lc lc' gl = ret lc'' ->
  wf_ECStack_head_tail maxb pinfo td M lc (EC::ECs) ->
  wf_ECStack_head_tail maxb pinfo td M lc' ECs ->
  wf_ECStack_head_tail maxb pinfo td M' lc'' ECs.
Proof.
  intros.
  apply wf_ECStack_head_tail_cons__inv in H1.
  destruct H1 as [H11 H12].
  eapply free_allocas_preserves_wf_ECStack_head_tail' in H2; eauto.

  unfold Opsem.returnUpdateLocals in H0.
  inv_mbind. 
  destruct c'; tinv H3.
  destruct n.
    inv H3; auto.

    destruct t; tinv H3.
    inv_mbind. 
    apply updateAddAL__wf_ECStack_head_tail; auto.
    intros. subst. symmetry in HeqR.
    unfold MDGVs.lift_op1, fit_gv in HeqR0. symmetry in HeqR0.
    inv_mbind. 
    apply H12 in Hin; auto. clear H12.
    destruct ec0. simpl in *.
    eapply Hin in Hlkup; eauto. clear Hin.
    destruct Hlkup as [[mb [J1 J2]] [Hlkup _]]; subst.
    destruct (sizeGenericValue g =n= nat_of_Z (ZRdiv (Z_of_nat n) 8)).
      inv H1.
      destruct Result; simpl in HeqR; eauto.
      eapply const2GV_disjoint_with_runtime_alloca; eauto.
        omega.

      unfold gundef in H1. inv_mbind. inv HeqR1.
      unfold_blk2GV.        
Local Transparent gv2gvs.
      unfold gv2gvs. simpl. auto.
Opaque gv2gvs. 
Qed.

Lemma free_allocas_preserves_wf_Mem: forall maxb td als Mem Mem',
  wf_Mem maxb td Mem -> free_allocas td Mem als = ret Mem' -> 
  wf_Mem maxb td Mem'.
Proof.
  induction als; simpl; intros.
    inv H0. auto.

    inv_mbind.
    symmetry in HeqR.
    eapply free_preserves_wf_Mem in HeqR; eauto.
Qed.

Lemma free_allocas_preserves_wf_als : forall maxb TD als als0 M M'
  (Hfree: free_allocas TD M als0 = ret M') 
  (Hwf: wf_als maxb M als),
  wf_als maxb M' als.
Proof.
  induction als0; simpl; intros.
    inv Hfree. auto.

    inv_mbind.
    symmetry in HeqR.
    eapply free_preserves_wf_als in HeqR; eauto.
Qed.

Lemma preservation_return : forall maxb pinfo (HwfPI : WF_PhiInfo pinfo)  
  F B rid RetTy Result lc F' B' c' cs' tmn' lc' EC Mem als als' cfg
  EC1 EC2 (Hwfg: wf_globals maxb (OpsemAux.Globals cfg))
  (EQ1:EC1 = {| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := nil;
                Opsem.Terminator := insn_return rid RetTy Result;
                Opsem.Locals := lc;
                Opsem.Allocas := als |})
  (EQ2:EC2 = {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := c' :: cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc';
                Opsem.Allocas := als' |})
  (Hinv : OpsemPP.wf_State cfg
           {| Opsem.ECS := EC1 :: EC2 :: EC;
              Opsem.Mem := Mem |})
  Mem' lc'' (H : Instruction.isCallInst c' = true)
  (H0 : free_allocas (OpsemAux.CurTargetData cfg) Mem als = ret Mem')
  (H1 : Opsem.returnUpdateLocals 
          (OpsemAux.CurTargetData cfg) c' 
            Result lc lc' (OpsemAux.Globals cfg) = ret lc'')
  (HwfS1 : wf_State maxb pinfo cfg
            {| Opsem.ECS := EC1 :: EC2 :: EC;
               Opsem.Mem := Mem |}),
  wf_State maxb pinfo cfg
     {| Opsem.ECS :=
             {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc'';
                Opsem.Allocas := als' |} :: EC;
        Opsem.Mem := Mem' |}.
Proof.
Local Opaque inscope_of_tmn inscope_of_cmd.

  intros. subst. destruct cfg as [S [los nts] Ps gl fs].
  destruct Hinv as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [_ [_ [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC0 HwfCall]
       ]
       HwfCall'
     ]
    ]]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0.
  destruct HwfS1 as 
    [
      [[Hinscope1 Hwflc1] [[[Hinscope2 Hwflc2] [HwfECs Hfr2]] Hfr1]] 
      [Hdisjals HwfM]
    ]. simpl. simpl in Hdisjals.
  fold wf_ECStack in HwfECs.
  assert (Hdisjals':=Hdisjals).
  destruct Hdisjals' as [Hdisjals' _].
  split.
  SCase "wf_ECStack".
    split.
    SSCase "wf_EC".
    split.
    SSSCase "sdom".

    destruct (fdef_dec (PI_f pinfo) F'); subst; auto.
    unfold inscope_of_pc in Hinscope2.
    remember (inscope_of_cmd 
      (PI_f pinfo) (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c') as R2.
    destruct R2; try solve [inversion Hinscope2].

    remember (getCmdID c') as R.
    destruct c'; try solve [inversion H].
    assert (In (insn_call i0 n c t v p) 
      (cs2'++[insn_call i0 n c t v p] ++ cs')) as HinCs.
      apply in_or_app. right. simpl. auto.
    assert (Hwfc := HBinF2).
    eapply wf_system__wf_cmd with (c:=insn_call i0 n c t v p) in Hwfc; eauto.
    assert (wf_fdef nil S (module_intro los nts Ps) (PI_f pinfo)) as HwfF.
      eapply wf_system__wf_fdef; eauto.
    assert (uniqFdef (PI_f pinfo)) as HuniqF.
      eapply wf_system__uniqFdef; eauto.

    assert (NoDup (als ++ als')) as Hnodup.
      rewrite_env 
        ((als ++ als') ++ 
          flat_map
            (fun ec : Opsem.ExecutionContext =>
             let '{| Opsem.Allocas := als |} := ec in als) EC) in Hdisjals'.
      apply NoDup_split in Hdisjals'.
      destruct Hdisjals'; auto.
    eapply free_allocas_preserves_wf_defs in Hinscope2; eauto. clear Hnodup.
    unfold inscope_of_pc.
    destruct cs'.
    SSSSCase "cs' = nil".
      assert (~ In (getCmdLoc (insn_call i0 n c t v p)) (getCmdsLocs cs2')) 
        as Hnotin.
        eapply preservation_helper1; eauto.

      assert (HeqR2':=HeqR2).
      apply inscope_of_cmd_tmn in HeqR2; auto.
      destruct HeqR2 as [ids2 [J1 J2]].
      simpl_env. rewrite <- J1.
      unfold Opsem.returnUpdateLocals in H1. simpl in H1.
      remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
      destruct R1; try solve [inv H1].
      destruct R.
      SSSSSCase "c' defines a variable".
        destruct n; inv HeqR.
        destruct t; tinv H1.

        remember (MDGVs.lift_op1 (fit_gv (los, nts) t) g t) as R2.
        destruct R2; inv H1.

        apply wf_defs_updateAddAL with (ids1:=l0); auto.
          split.
            eapply preservation_return_helper; eauto; simpl; auto.

            intro; subst.
            admit. (* PI_id pinfo cannot be of an id for callsite *) 

      SSSSSCase "c' defines nothing".
        destruct n; inv HeqR. inv H1.
        simpl in J2.
        eapply wf_defs_eq; eauto. 
        
    SSSSCase "cs' <> nil".
      assert (NoDup (getCmdsLocs (cs2' ++ [insn_call i0 n c t v p] ++ [c0] ++ 
        cs'))) as Hnodup.
        eapply preservation_helper2; eauto.

      assert (HeqR2':=HeqR2). simpl_env in HeqR2.
      apply inscope_of_cmd_cmd in HeqR2; auto.
      destruct HeqR2 as [ids2 [J1 J2]].        
      simpl_env. rewrite <- J1.
      unfold Opsem.returnUpdateLocals in H1. simpl in H1.
      remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
      destruct R1; try solve [inv H1].
      destruct R.
      SSSSSCase "c' defines a variable".
        destruct n; inv HeqR.
        destruct t; tinv H1.
        remember (MDGVs.lift_op1 (fit_gv (los, nts) t) g t) as R2.
        destruct R2; inv H1.
        inv Hwfc. inv H16. inv H7. inv H18.

        apply wf_defs_updateAddAL with (ids1:=l0); auto.
          split.
            eapply preservation_return_helper; eauto; simpl; auto.

            intro; subst.
            admit. (* PI_id pinfo cannot be of an id for callsite *) 

      SSSSSCase "c' defines nothing".
        destruct n; inv HeqR. inv H1.
        simpl in J2.
        eapply wf_defs_eq; eauto. 

      SSSCase "wflc".
        clear - Hwflc1 Hwflc2 H1 Hwfg HwfM H0.
        eapply free_allocas_preserves_wf_lc in H0; eauto.
        destruct HwfM.
        eapply returnUpdateLocals__wf_lc in H1; eauto.

    split.
    SSCase "wf_ECs".
      eapply free_allocas_preserves_wf_ECStack; eauto.
      apply NoDup_strenthening in Hdisjals'; auto.

    SSCase "wf_ECs_head_tail".
      simpl in Hfr1, Hfr2.
      eapply free_allocas_preserves_wf_ECStack_head_tail; eauto; simpl; eauto.

  split.
  SCase "Disjoint Allocas".
    apply wf_als_split in Hdisjals.
    destruct Hdisjals; auto.
    eapply free_allocas_preserves_wf_als; eauto.

  SCase "wfM".
    eapply free_allocas_preserves_wf_Mem; eauto.

Transparent inscope_of_tmn inscope_of_cmd.
Qed.

Definition wf_GVs_in_ECs (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (head:Opsem.ExecutionContext) tail (id1:id)(gv1:GVsT DGVs) : Prop :=
let '(Opsem.mkEC f b cs tmn lc als) := head in
(if (fdef_dec (PI_f pinfo) f) then 
  forall ids0, 
    inscope_of_pc f b cs tmn = Some ids0 ->
    wf_defs maxb pinfo TD M lc ids0 als ->
    wf_GVs maxb pinfo TD M lc ids0 als id1 gv1
else True) /\
(forall ec0 (Hin : In ec0 tail) (gvsa : GVsT DGVs) 
    (Heq : Opsem.CurFunction ec0 = PI_f pinfo) ids0
    (Hscp: inscope_of_EC ec0 = Some ids0) (Hin1: In (PI_id pinfo) ids0)
    (Hlkup : lookupAL (GVsT DGVs) (Opsem.Locals ec0) (PI_id pinfo) = ret gvsa),
    no_alias gv1 gvsa) /\
(valid_ptrs (Mem.nextblock M) gv1).

Lemma preservation_pure_cmd_updated_case : forall (F : fdef)(B : block)
  (lc : DGVMap)(gv3 : GVsT DGVs) (cs : list cmd) (tmn : terminator) id0 c0 Mem0 
  als ECs pinfo 
  (HwfPI : WF_PhiInfo pinfo) (Hid : Some id0 = getCmdID c0) cfg maxb
  EC
  (Heq: EC = {| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := c0 :: cs;
                Opsem.Terminator := tmn;
                Opsem.Locals := lc;
                Opsem.Allocas := als |})
  (Hwfgv : 
    wf_GVs_in_ECs maxb pinfo (OpsemAux.CurTargetData cfg) Mem0 EC ECs id0 gv3)
  (Hinv : OpsemPP.wf_State cfg
           {| Opsem.ECS := EC :: ECs;
              Opsem.Mem := Mem0 |})
  (HwfS1 : wf_State maxb pinfo cfg
            {| Opsem.ECS := EC :: ECs;
               Opsem.Mem := Mem0 |}),
   wf_State maxb pinfo cfg
     {|
     Opsem.ECS := {|
            Opsem.CurFunction := F;
            Opsem.CurBB := B;
            Opsem.CurCmds := cs;
            Opsem.Terminator := tmn;
            Opsem.Locals := updateAddAL (GVsT DGVs) lc id0 gv3;
            Opsem.Allocas := als |} :: ECs;
     Opsem.Mem := Mem0 |}.
Proof.
Local Opaque inscope_of_cmd inscope_of_tmn.

  intros. subst. destruct Hwfgv as [Hwfgv1 [Hwfgv2 Hwfgv3]].
  destruct cfg as [S [los nts] Ps gl fs].
  destruct Hinv as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [HwfEC0 HwfCall]
    ]]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0.
  destruct HwfS1 as 
    [[[Hinscope1 Hwflc1] [HwfECs Hfr2]] [Hdisjals HwfM]].
  simpl. simpl in Hdisjals.
  fold wf_ECStack in HwfECs.
  simpl in Hwfgv1.
  split; auto.
  SCase "wf_ECStack".
    split.
    SSCase "wf_EC".
    split.
    SSSCase "sdom".
    destruct (fdef_dec (PI_f pinfo) F); subst; auto.

  unfold inscope_of_pc in *.
  remember (inscope_of_cmd (PI_f pinfo) 
    (block_intro l1 ps1 (cs1' ++ c0 :: cs) tmn) c0) as R1. 
  assert (HeqR1':=HeqR1).

Transparent inscope_of_cmd.

  unfold inscope_of_cmd, inscope_of_id in HeqR1'.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      assert (Hid':=Hid).
      symmetry in Hid.
      apply getCmdLoc_getCmdID in Hid.
      subst.
      destruct cs; simpl_env in *.
      SSSSCase "cs = nil".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs1')) as Hnotin.
          (* this lemma should be lifted to the top *)
          eapply preservation_helper1; eauto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs1' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        assert (HwfF:=HFinPs1). eapply wf_system__wf_fdef in HwfF; eauto.
        eapply wf_defs_updateAddAL; eauto.

      SSSSCase "cs <> nil".
        assert (NoDup (getCmdsLocs (cs1' ++ [c0] ++ [c] ++ cs))) as Hnodup.
          (* this lemma should be lifted to the top *)
          eapply preservation_helper2; eauto.

        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs1' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        assert (HwfF:=HFinPs1). eapply wf_system__wf_fdef in HwfF; eauto.
        eapply wf_defs_updateAddAL; eauto.

      SSSCase "wflc".
        apply updateAddAL__wf_lc; auto.

    split; auto.
    SSCase "wf_ECs_head_tail".
      eapply updateAddAL__wf_ECStack_head_tail; eauto.
Transparent inscope_of_cmd inscope_of_tmn.

Qed.

Lemma BOP_preserves_no_alias: forall TD lc gl bop0 sz0 v1 v2 gvs3 gvsa, 
  BOP TD lc gl bop0 sz0 v1 v2 = ret gvs3 ->
  no_alias gvs3 gvsa.
Proof.
  intros.
  unfold BOP in H.
  inv_mbind'. eapply mbop_preserves_no_alias in H0; eauto.
Qed.

Lemma BOP_preserves_no_embedded_ptrs: forall TD lc gl bop0 sz0 v1 v2 gvs3, 
  BOP TD lc gl bop0 sz0 v1 v2 = ret gvs3 -> no_embedded_ptrs gvs3.
Proof.
  intros.
  unfold BOP in H.
  inv_mbind'. eapply mbop_preserves_no_embedded_ptrs in H0; eauto.
Qed.

Lemma BOP__wf_GVs_in_ECs : forall (v : value) (v0 : value) (id1 : id) (bop0 : bop)
  gvs3 TD bop0 sz0 lc gl hd tl Mem0 td pinfo maxb (Hneq: id1 <> PI_id pinfo)
  (H11 : BOP TD lc gl bop0 sz0 v v0 = ret gvs3),
  wf_GVs_in_ECs maxb pinfo td Mem0 hd tl id1 gvs3.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct hd.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    split; intros; subst; try congruence.
      eapply BOP_preserves_no_alias; eauto.
  split.
    intros. eapply BOP_preserves_no_alias; eauto.
    intros. subst. apply BOP_preserves_no_embedded_ptrs in H11; auto.
      apply no_embedded_ptrs__valid_ptrs; auto.
Qed.

Lemma operand__no_alias_with__tail': forall maxb gl (Hwfgl : wf_globals maxb gl)
  lc (gv1 : GVsT DGVs) v TD (Hget: Opsem.getOperandValue TD v lc gl = ret gv1)
  (tl : list Opsem.ExecutionContext) pinfo Mem
  (Hwfstk : wf_ECStack_head_tail maxb pinfo TD Mem lc tl)
  (ec0 : Opsem.ExecutionContext) (Hin: In ec0 tl) (gvsa : GVsT DGVs)
  (Heq: Opsem.CurFunction ec0 = PI_f pinfo) ids0
  (Hscp: inscope_of_EC ec0 = ret ids0) (Hin: In (PI_id pinfo) ids0)
  (Hlkup: lookupAL (GVsT DGVs) (Opsem.Locals ec0) (PI_id pinfo) = ret gvsa),
  no_alias gv1 gvsa.
Proof.
  intros. 
  eapply operand__no_alias_with__tail in Hlkup; eauto.
Qed.

Lemma CAST__wf_GVs_in_ECs : forall (v : value) (id1 : id)
  gvs2 TD gl EC Mem pinfo maxb castop0 t1 t2 
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) 
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: forall ids0,
         let '(Opsem.mkEC F B cs tmn _ _) := EC in
         F = (PI_f pinfo) ->
         inscope_of_pc F B cs tmn = Some ids0 ->
         wf_use_at_head pinfo ids0 v)
  (Hneq: id1 <> PI_id pinfo)
  (H11 : Opsem.CAST TD (@Opsem.Locals DGVs EC) gl castop0 t1 v t2 
           = ret gvs2) tl
  (Hwfstk: 
    wf_ECStack_head_tail maxb pinfo TD Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo TD Mem EC tl id1 gvs2.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct EC.
  apply OpsemProps.CAST_inversion in H11.
  destruct H11 as [gv1 [J1 J2]].
  unfold lift_op1 in J2. simpl in J2. unfold MDGVs.lift_op1 in J2.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    split; intros; subst; try congruence.
      assert (H2':=H2).
      apply H0 in H2; auto.
      destruct H2 as [[J5 [J6 J3]] J4]; eauto.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=gv1)
        (M:=Mem) in J1; eauto.
        clear - J1 J2. 
        eapply mcast_preserves_no_alias in J2; eauto.
  split.
    intros.
    eapply operand__no_alias_with__tail' in J1; eauto.
    eapply mcast_preserves_no_alias in J2; eauto.

    intros. subst.
    apply mcast_inv in J2.
    destruct J2 as [J2 | J2]; subst.
      eapply operand__lt_nextblock in J1; eauto.
      eapply undef_valid_ptrs; eauto.      
Qed.

Lemma wf_EC__wf_lc : forall maxb pinfo TD M EC,
  wf_ExecutionContext maxb pinfo TD M EC ->
  wf_lc M (Opsem.Locals EC).
Admitted.

Lemma mload__wf_GVs_in_ECs : forall (v : value) (v0 : value) (id1 : id) 
  gvs3 t align0 EC Mem td pinfo maxb mp
  (Hneq: id1 <> PI_id pinfo) (HwfM: wf_Mem maxb td Mem)
  (H1 : mload td Mem mp t align0 = ret gvs3) tl
  (Hwfstk: wf_ECStack_head_tail maxb pinfo td Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo td Mem EC tl id1 gvs3.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct EC.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    split; intros; subst; try congruence.
      apply H0 in H3; auto.
      destruct H3 as [[J1 [J2 J3]] _]; eauto.
  split.
    intros. simpl in Hwfstk. apply Hwfstk in Hin.
    destruct ec0. simpl in *.
    eapply_clear Hin in Hlkup.
    destruct Hlkup as [_ [_ Hld]]; eauto.

    intros. subst.
    destruct HwfM as [J1 J2]; eauto.
Qed.

Lemma GEP_preserves_no_alias: forall TD t mp vidxs inbounds0 mp' gvsa,
  @Opsem.GEP DGVs TD t mp vidxs inbounds0 = ret mp' ->
  no_alias mp gvsa -> no_alias mp' gvsa.
Proof.
  unfold Opsem.GEP. unfold lift_op1. simpl. unfold MDGVs.lift_op1. unfold gep.
  unfold GEP. intros. 
  remember (GV2ptr TD (getPointerSize TD) mp) as R1.
  destruct R1; eauto using undef_disjoint_with_ptr.
  destruct (GVs2Nats TD vidxs); eauto using undef_disjoint_with_ptr.
  remember (mgep TD t v l0) as R2.
  destruct R2; eauto using undef_disjoint_with_ptr.
  inv H. 
  eapply GV2ptr_preserves_no_alias in HeqR1; eauto.
  eapply mgep_preserves_no_alias; eauto.
Qed.

Lemma GEP_inv: forall TD t (mp1 : GVsT DGVs) inbounds0 vidxs mp2
  (H1 : Opsem.GEP TD t mp1 vidxs inbounds0 = ret mp2),
  gundef TD (typ_pointer (typ_int 1%nat)) = ret mp2 \/
  exists blk, exists ofs1, exists ofs2 : int32, exists m1, exists m2,
    mp1 = (Vptr blk ofs1, m1) :: nil /\ mp2 = (Vptr blk ofs2, m2) :: nil.
Proof.
  intros.
  unfold Opsem.GEP in H1. unfold lift_op1 in H1. simpl in H1.
  unfold MDGVs.lift_op1 in H1.
  unfold gep in H1. unfold GEP in H1.
  remember (GV2ptr TD (getPointerSize TD) mp1) as R1.
  destruct R1; auto.
  destruct (GVs2Nats TD vidxs); auto.
  remember (mgep TD t v l0) as R2.
  destruct R2; auto.
  inv H1.
  unfold mgep in HeqR2.
  destruct v; tinv HeqR2.
  destruct l0; tinv HeqR2.
  destruct (mgetoffset TD (typ_array 0%nat t) (z :: l0)) as [[]|]; 
    inv HeqR2.
  unfold GV2ptr in HeqR1.
  destruct mp1 as [|[]]; tinv HeqR1.
  destruct v; tinv HeqR1.
  destruct mp1; inv HeqR1.
  unfold ptr2GV. unfold val2GV. right. exists b0. exists i1. 
  exists (Int.add 31 i1 (Int.repr 31 z0)). exists m.
  exists (AST.Mint (Size.mul Size.Eight (getPointerSize TD) - 1)).
  eauto.
Qed.

Lemma GEP__wf_GVs_in_ECs : forall (v : value) (v0 : value) (id1 : id) 
  mp' TD t gl EC Mem pinfo maxb (mp:GVsT DGVs) mps 
  inbounds0 vidxs (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) 
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: forall ids0,
         let '(Opsem.mkEC F B cs tmn _ _) := EC in
         F = (PI_f pinfo) ->
         inscope_of_pc F B cs tmn = Some ids0 ->
         wf_use_at_head pinfo ids0 v)
  (H : Opsem.getOperandValue TD v (Opsem.Locals EC) gl = ret mps)
  (H0 : mp @ mps) (Hneq: id1 <> PI_id pinfo)
  (H1 : Opsem.GEP TD t mp vidxs inbounds0 = ret mp') tl
  (Hwfstk: wf_ECStack_head_tail maxb pinfo TD Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo TD Mem EC tl id1 mp'.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct EC.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    split; intros; subst; try congruence.
      assert (H5':=H5).
      apply H3 in H5; auto.
      destruct H5 as [[J1 [J2 J3]] J4]; eauto.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=mp)
        (M:=Mem) in H; eauto.
        clear - H1 H. 
        eapply GEP_preserves_no_alias in H1; eauto.
  split. 
    intros.
    eapply operand__no_alias_with__tail' in H; eauto.
    inv H0.
    eapply GEP_preserves_no_alias in H1; eauto.

    intros. subst. apply GEP_inv in H1; auto.
    destruct H1 as [H1 | [blk [ofs1 [ofs2 [m1 [m2 [J1 J2]]]]]]]; subst.
      eapply undef_valid_ptrs; eauto.

      eapply operand__lt_nextblock in H0; eauto.
Qed.

Lemma params2GVs_preserves_no_alias: forall maxb gl
  (Hwfg : wf_globals maxb gl) TD lc mb t (Hinbound: maxb < mb) lp
  (Hwf : forall (id1 : atom) (gvs1 : GVsT DGVs) t1,
         In (t1, value_id id1) lp -> 
         lookupAL (GVsT DGVs) lc id1 = ret gvs1 -> 
         no_alias gvs1 ($ blk2GV TD mb # typ_pointer t $)) gvs
  (Hps2GVs : Opsem.params2GVs TD lp lc gl = ret gvs),
  forall gv, In gv gvs -> no_alias gv ($ blk2GV TD mb # typ_pointer t $).
Proof.
  induction lp; simpl; intros.
    inv Hps2GVs. inv H.

    destruct a.
    inv_mbind.
    simpl in H.
    destruct H as [H | H]; subst; eauto.
    destruct v; simpl in HeqR; eauto.
      eapply const2GV_disjoint_with_runtime_alloca; eauto.
Qed.

Lemma initializeFrameValues_preserves_no_alias: forall TD mb t la 
  (gvs:list (GVsT DGVs))
  (Hwf: forall gv, In gv gvs -> no_alias gv ($ blk2GV TD mb # typ_pointer t $)) 
  lc (Hinit : Opsem.initLocals TD la gvs = ret lc)
  (id1 : atom) (gvs1 : GVsT DGVs)
  (Hlkup : lookupAL (GVsT DGVs) lc id1 = ret gvs1),
  no_alias gvs1 ($ blk2GV TD mb # typ_pointer t $).
Proof.
  unfold Opsem.initLocals.
  induction la; simpl; intros.
    inv Hinit. inv Hlkup.

    destruct a as [[]].
    destruct gvs.
      inv_mbind. symmetry in HeqR.
      destruct (id_dec i0 id1); subst.
        rewrite lookupAL_updateAddAL_eq in Hlkup. inv Hlkup.
        eapply undef_disjoint_with_ptr; eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hlkup; auto. 
        eapply IHla in HeqR; eauto.

      inv_mbind. symmetry in HeqR.
      destruct (id_dec i0 id1); subst.
        rewrite lookupAL_updateAddAL_eq in Hlkup. inv Hlkup.
        unfold MDGVs.lift_op1, fit_gv in HeqR0.
        symmetry in HeqR0.
        inv_mbind.
        destruct (sizeGenericValue g =n= nat_of_Z (ZRdiv (Z_of_nat n) 8)).
          apply Hwf. 
          inv H0. simpl. auto.

          eapply undef_disjoint_with_ptr; eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hlkup; auto. 
        eapply IHla in HeqR; eauto.
        intros. apply Hwf. simpl. auto.
Qed.

Lemma in_params__used: forall id1 A (lp : list (A * value)) (t1 : A),
  fold_left
    (fun (acc : bool) (p : A * value) =>
     let '(_, v) := p in used_in_value id1 v || acc) lp false ->
  ~ In (t1, value_id id1) lp.
Admitted.

Lemma initLocals_preserves_wf_ECStack_head_tail: forall Mem (lc:DGVMap) maxb TD 
  ECs lc' gl (Hwflc1 : wf_lc Mem lc) pinfo gvs la lp EC
  (Hnouse: 
    PI_f pinfo = Opsem.CurFunction EC ->
    List.fold_left 
      (fun acc p => let '(_, v):=p in used_in_value (PI_id pinfo) v || acc) 
      lp false)
  (Hwfg : wf_globals maxb gl)
  (H3 : Opsem.params2GVs TD lp lc gl = ret gvs)
  (H4 : Opsem.initLocals TD la gvs = ret lc')
  (Heq2 : lc = Opsem.Locals EC)
  (Hfr2 : wf_ECStack_head_tail maxb pinfo TD Mem lc ECs)
  (Hscp: if fdef_dec (PI_f pinfo) (Opsem.CurFunction EC) then
           match inscope_of_EC EC with
           | ret ids0 => 
             wf_defs maxb pinfo TD Mem (Opsem.Locals EC) ids0 (Opsem.Allocas EC)
           | merror => False
           end
         else True),
  wf_ECStack_head_tail maxb pinfo TD Mem lc' (EC :: ECs).
Proof.
  intros. unfold wf_ECStack_head_tail. intros ec0 Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; subst.
    unfold wf_ECStack_head_in_tail. destruct ec0. simpl in *.
    intros.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; try congruence.    
    rewrite H0 in Hscp.
    apply_clear Hscp in H2.
    destruct H2 as [[[mb [J11 [J14 J15]]] [J12 J13]] J2]; subst.
    split; eauto.
    split; intros; eauto.
      eapply initializeFrameValues_preserves_no_alias in H4; eauto.
      eapply params2GVs_preserves_no_alias; eauto. 
        omega.

        intros.
        apply J2 in H6. unfold wf_non_alloca_GVs in H6.
        destruct (id_dec id0 (PI_id pinfo)); subst; auto.
          contradict H5. eapply in_params__used; eauto.

    destruct ec0. simpl.
    intros ids0 gvsa Heq Hscp' Hin' Hlkup.
    apply_clear Hfr2 in Hin. simpl in Hin. eapply_clear Hin in Hscp'. 
    destruct Hscp' as [[mb [J11 J12]] [J2 J3]]; subst.
    split; eauto.
    split; auto.
      intros.
      eapply initializeFrameValues_preserves_no_alias in H4; eauto.
      eapply params2GVs_preserves_no_alias; eauto. omega.
Qed.

Lemma initLocals_preserves_wf_defs : forall fid fa rt la va lb gvs 
  lc Mem TD pinfo maxb (Hwfpi: WF_PhiInfo pinfo)
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hinit : Opsem.initLocals TD la gvs = Some lc) 
  (Heq: fdef_intro (fheader_intro fa rt fid la va) lb = PI_f pinfo),
  wf_defs maxb pinfo TD Mem lc (getArgsIDs la) nil.
Proof.
  intros. intros gvsa Hin Hlkup.
  admit. (* promotable allocas cannot be arguments *)
Qed.

Lemma params2GVs_preserves_wf_lc: forall maxb gl M
  (Hwfg : wf_globals maxb gl) TD lc (Hinbound: maxb < Mem.nextblock M) 
  (Hwf : wf_lc M lc) lp gvs
  (Hps2GVs : @Opsem.params2GVs DGVs TD lp lc gl = ret gvs),
  forall gv, In gv gvs -> valid_ptrs (Mem.nextblock M) gv.
Proof.
  induction lp; simpl; intros.
    inv Hps2GVs. inv H.

    destruct a.
    inv_mbind.
    simpl in H.
    destruct H as [H | H]; subst; eauto.
    destruct v; simpl in HeqR; eauto.
      eapply const2GV_valid_ptrs in HeqR; eauto. 
      eapply valid_ptrs__trans; eauto. omega.
Qed.

Lemma undef__valid_lift_ptrs: forall g td t1 blk
  (Hc2g : ret g = gundef td t1), valid_ptrs blk ($ g # t1 $).
Proof.
  unfold gundef. intros.
  inv_mbind'.
Local Transparent gv2gvs.
  unfold gv2gvs. simpl. auto.
Opaque gv2gvs.
Qed.

Lemma initializeFrameValues_preserves_wf_lc: forall TD la (gvs:list (GVsT DGVs))
  M (Hwf: forall gv, In gv gvs -> valid_ptrs (Mem.nextblock M) gv) 
  lc (Hinit : Opsem.initLocals TD la gvs = ret lc), wf_lc M lc.
Proof.
  unfold Opsem.initLocals. unfold wf_lc.
  induction la; simpl; intros.
    inv Hinit. inv H.

    destruct a as [[]].
    destruct gvs.
      inv_mbind. symmetry in HeqR.
      destruct (id_dec i0 id0); subst.
        rewrite lookupAL_updateAddAL_eq in H. inv H.
        eapply undef__valid_lift_ptrs; eauto.

        rewrite <- lookupAL_updateAddAL_neq in H; auto. 
        eapply IHla in HeqR; eauto.

      inv_mbind. symmetry in HeqR.
      destruct (id_dec i0 id0); subst.
        rewrite lookupAL_updateAddAL_eq in H. inv H.
        unfold MDGVs.lift_op1, fit_gv in HeqR0.
        symmetry in HeqR0.
        inv_mbind.
        destruct (sizeGenericValue g =n= nat_of_Z (ZRdiv (Z_of_nat n) 8)).
          inv H0. eapply Hwf; simpl; eauto.
          
          eapply undef_valid_ptrs; eauto.

        rewrite <- lookupAL_updateAddAL_neq in H; auto. 
        eapply IHla in HeqR; eauto.
        intros. eapply Hwf; simpl; eauto.
Qed.

Lemma initLocals_preserves_wf_lc: forall Mem (lc:DGVMap) maxb TD 
  lc' gl (Hwflc1 : wf_lc Mem lc) gvs la lp
  (Hwfg : wf_globals maxb gl) (Hinbd: maxb < Mem.nextblock Mem)
  (H3 : Opsem.params2GVs TD lp lc gl = ret gvs)
  (H4 : Opsem.initLocals TD la gvs = ret lc')
  (Hfr2 : wf_lc Mem lc),
  wf_lc Mem lc'.
Proof.
  intros.
  eapply initializeFrameValues_preserves_wf_lc in H4; eauto.
  eapply params2GVs_preserves_wf_lc; eauto. 
Qed.

Axiom callExternalProc_preserves_wf_ECStack_head_tail : forall maxb pinfo   
  ECs TD M M' (lc:DGVMap) gvs gvss fid oresult gl lp
  (Hwflc: wf_lc M lc) (Hwfgl: wf_globals maxb gl) (H3 : gvs @@ gvss),
  Opsem.params2GVs TD lp lc gl = ret gvss ->
  OpsemAux.callExternalFunction M fid gvs = ret (oresult, M') ->
  wf_ECStack_head_tail maxb pinfo TD M lc ECs ->
  wf_ECStack_head_tail maxb pinfo TD M' lc ECs.

Axiom callExternalFunction_preserves_wf_ECStack : forall maxb pinfo ECs TD M  
  M' gvs fid oresult, 
  OpsemAux.callExternalFunction M fid gvs = ret (oresult, M') ->
  wf_ECStack maxb pinfo TD M ECs ->
  wf_ECStack maxb pinfo TD M' ECs.

Axiom callExternalProc_preserves_wf_EC : forall maxb pinfo TD M M' rid
  als F B cs tmn gl gvss gvs fid oresult lp (lc:DGVMap) fv ft ca
  (Hwflc: wf_lc M lc) (Hwfgl: wf_globals maxb gl) (H3 : gvs @@ gvss)
  (J1: Opsem.params2GVs TD lp lc gl = ret gvss)
  (J2: OpsemAux.callExternalFunction M fid gvs = ret (oresult, M'))
  (HwfEC: wf_ExecutionContext maxb pinfo TD M 
            {| Opsem.CurFunction := F;
               Opsem.CurBB := B;
               Opsem.CurCmds := insn_call rid true ca ft fv lp :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
  wf_ExecutionContext maxb pinfo TD M'
   {| Opsem.CurFunction := F;
      Opsem.CurBB := B;
      Opsem.CurCmds := cs;
      Opsem.Terminator := tmn;
      Opsem.Locals := lc;
      Opsem.Allocas := als |}.

Axiom callExternalFunction_preserves_wf_Mem : forall maxb TD M fid gvs M' 
  oresult,
  OpsemAux.callExternalFunction M fid gvs = ret (oresult, M') ->
  wf_Mem maxb TD M ->
  wf_Mem maxb TD M'.

Axiom callExternalFunction_preserves_wf_als : forall M gvs M' maxb als fid 
  oresult
  (Hexcall: OpsemAux.callExternalFunction M fid gvs = ret (oresult, M')) 
  (Hwf: wf_als maxb M als),
  wf_als maxb M' als.

Axiom callExternalFun_preserves_wf_ECStack_head_tail : forall maxb pinfo   
  ECs TD M M' (lc:DGVMap) gvs gvss fid result gl lp g0 rid ft
  (Hwflc: wf_lc M lc) (Hwfgl: wf_globals maxb gl) (H3 : gvs @@ gvss)
  (HeqR : ret g0 = fit_gv TD ft result),
  Opsem.params2GVs TD lp lc gl = ret gvss ->
  OpsemAux.callExternalFunction M fid gvs = ret (Some result, M') ->
  wf_ECStack_head_tail maxb pinfo TD M lc ECs ->
  wf_ECStack_head_tail maxb pinfo TD M' 
    (updateAddAL (GVsT DGVs) lc rid ($ g0 # ft $)) ECs.

Axiom callExternalFun_preserves_wf_EC : forall maxb pinfo TD M M' rid
  als F B cs tmn gl gvss gvs fid result lp (lc:DGVMap) fv ft ca g0
  (Hwflc: wf_lc M lc) (Hwfgl: wf_globals maxb gl) (H3 : gvs @@ gvss)
  (J1: Opsem.params2GVs TD lp lc gl = ret gvss)
  (J2: OpsemAux.callExternalFunction M fid gvs = ret (Some result, M'))
  (HeqR : ret g0 = fit_gv TD ft result)
  (HwfEC: wf_ExecutionContext maxb pinfo TD M 
            {| Opsem.CurFunction := F;
               Opsem.CurBB := B;
               Opsem.CurCmds := insn_call rid false ca ft fv lp :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
  wf_ExecutionContext maxb pinfo TD M'
   {| Opsem.CurFunction := F;
      Opsem.CurBB := B;
      Opsem.CurCmds := cs;
      Opsem.Terminator := tmn;
      Opsem.Locals := (updateAddAL (GVsT DGVs) lc rid ($ g0 # ft $));
      Opsem.Allocas := als |}.

Definition wf_use_in_tail (pinfo:PhiInfo) (v:value) :=
used_in_value (PI_id pinfo) v = false.

Lemma store_preserves_mload_aux_inv: forall b1 b2 v2 m2 Mem' Mem ofs2 
  (Hst: Mem.store m2 Mem b2 ofs2 v2 = ret Mem') mc ofs1 gvs0,
  mload_aux Mem' mc b1 ofs1 = ret gvs0 ->
  exists gvs2 : GenericValue,
     mload_aux Mem mc b1 ofs1 = ret gvs2 /\
     (forall v m,
      In (v, m) gvs0 -> (v2, m2) = (v, m) \/ v = Vundef \/ In (v, m) gvs2).
Proof.
  induction mc; simpl; intros.
    inv H. eauto.

    inv_mbind'. symmetry in HeqR0.
    apply IHmc in HeqR0.
    destruct HeqR0 as [gvs2 [J1 J2]].
    rewrite J1.
   
Admitted.

Lemma mstore_aux_preserves_mload_aux_inv: forall mc b1 ofs1 gvs0 b2 gvs1 Mem' Mem ofs2,
  mload_aux Mem' mc b1 ofs1 = ret gvs0 ->
  mstore_aux Mem gvs1 b2 ofs2 = ret Mem' ->
  exists gvs2 : GenericValue,
     mload_aux Mem mc b1 ofs1 = ret gvs2 /\
     (forall v m,
      In (v, m) gvs0 -> In (v, m) gvs1 \/ v = Vundef \/ In (v, m) gvs2).
Proof.
  induction gvs1 as [|[]]; simpl; intros.
    inv H0. exists gvs0. split; auto.
  
    inv_mbind'.
    apply IHgvs1 in H2; auto.
    destruct H2 as [gvs2 [J1 J2]].
    symmetry in HeqR.
    eapply store_preserves_mload_aux_inv in HeqR; eauto.
    destruct HeqR as [gvs3 [J3 J4]].
    exists gvs3.
    split; auto.
    intros.
    apply J2 in H0.
    destruct H0 as [H0 | [H0 | H0]]; subst; auto.
    apply J4 in H0. 
    destruct H0 as [H0 | [H0 | H0]]; subst; auto.
Qed.

Lemma mstore_preserves_mload_inv: forall TD Mem' gptr ty al gvs0 Mem gvs1 t
  mp2 (H1 : mload TD Mem' gptr ty al = ret gvs0) align
  (H2 : mstore TD Mem mp2 t gvs1 align = Some Mem'),
  exists gvs2, mload TD Mem gptr ty al = ret gvs2 /\
     (forall v m,
      In (v, m) gvs0 -> In (v, m) gvs1 \/ v = Vundef \/ In (v, m) gvs2).
Proof.
  intros.
  apply store_inv in H2.
  destruct H2 as [b [ofs [J5 J4]]].
  apply mload_inv in H1.
  destruct H1 as [b1 [ofs1 [m1 [mc [J1 [J2 J3]]]]]]; subst.
  unfold mload. simpl. rewrite J2.
  symmetry in J5. apply GV2ptr_inv in J5. 
  destruct J5 as [b2 [ofs2 [m2 [J6 J7]]]]; subst. inv J7.
  eapply mstore_aux_preserves_mload_aux_inv; eauto.
Qed.

(*
Lemma mstore_preserves_mload_inv: forall TD Mem' gptr ty al gvs0 Mem gv1 t
  mp2 (H1 : mload TD Mem' gptr ty al = ret gvs0) align
  (H2 : mstore TD Mem mp2 t gv1 align = Some Mem'),
  Some gvs0 = gundef TD ty \/
  gvs0 = gv1 \/
  mload TD Mem gptr ty al = ret gvs0.
Proof.
  intros.
  apply store_inv in H2.
  destruct H2 as [b [ofs [J5 J4]]].
  admit. (* mem prop *)
Qed.
*)

Lemma mstore_preserves_mload: forall TD Mem' gptr ty al gvs0 Mem gv1 t
  mp2 (H1 : mload TD Mem gptr ty al = ret gvs0) align
  (H2 : mstore TD Mem mp2 t gv1 align = Some Mem')
  (Hna: no_alias mp2 gptr),
  mload TD Mem' gptr ty al = ret gvs0.
Proof.
  admit. (* mem prop *)
Qed.

Lemma mstore_preserves_mload': forall TD Mem' gptr ty al gvs0 Mem gv1 t
  mp2 (H1 : mload TD Mem gptr ty al = ret gvs0) align
  (H2 : mstore TD Mem mp2 t gv1 align = Some Mem'),
  exists gvs1, mload TD Mem' gptr ty al = ret gvs1.
Proof.
  admit. (* mem prop *)
Qed.

Lemma no_alias_overlap: forall gvs1 gvs2 gvs0 gvsa,
  no_alias gvs1 gvsa ->
  no_alias gvs2 gvsa ->
  (forall (v : val) (m : AST.memory_chunk),
     In (v, m) gvs0 -> In (v, m) gvs1 \/ v = Vundef \/ In (v, m) gvs2) ->
  no_alias gvs0 gvsa.
Admitted.

Lemma mstore_preserves_wf_defs_at_head : forall maxb pinfo TD M  
  M' gl v als lc gvs1 gv1 t mp2 align mps2 vp
  (Hgetop': Opsem.getOperandValue TD vp lc gl = ret mps2)
  (Hgetop: Opsem.getOperandValue TD v lc gl = ret gvs1)
  (Hinp: mp2 @ mps2) (Hin: gv1 @ gvs1) (Hwfgl: wf_globals maxb gl)
  (Hst: mstore TD M mp2 t gv1 align = Some M')
  ids0 (Hwfu: wf_use_at_head pinfo ids0 v) 
  (Hwf: wf_defs maxb pinfo TD M lc ids0 als),
  wf_defs maxb pinfo TD M' lc ids0 als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  assert (no_alias gv1 gvsa) as J.
    eapply operand__no_alias_with__head with (mptrs:=gvs1); eauto.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    destruct J1 as [[mb [J11 [J12 J13]]] [J4 [gv J3]]]; subst.
    split. exists mb. repeat split; auto. omega. admit. (* MemProp *)
    split.
      intros. 
      eapply mstore_preserves_mload_inv in H; eauto.
      destruct H as [gvs2 [H1 H2]].
      apply J4 in H1.
      eapply no_alias_overlap with (gvs1:=gv1); eauto.

      eapply mstore_preserves_mload'; eauto.
Qed.

Lemma mstore_preserves_wf_defs_in_tail : forall maxb pinfo TD M  
  M' lc1 gl v als lc2 gvs1 gv1 t mp2 align mps2 vp
  (Hgetop': Opsem.getOperandValue TD vp lc1 gl = ret mps2)
  (Hgetop: Opsem.getOperandValue TD v lc1 gl = ret gvs1)
  (Hinp: mp2 @ mps2) (Hin: gv1 @ gvs1) (Hwfgl: wf_globals maxb gl)
  (Hst: mstore TD M mp2 t gv1 align = Some M') EC
  (Heq1: Opsem.CurFunction EC = PI_f pinfo)
  (Heq2: Opsem.Locals EC = lc2) 
  (Hht: wf_ECStack_head_in_tail maxb pinfo TD M lc1 EC)
  ids0 (Hscp: inscope_of_EC EC = ret ids0) 
  (Hwf: wf_defs maxb pinfo TD M lc2 ids0 als),
  wf_defs maxb pinfo TD M' lc2 ids0 als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    clear J2.
    destruct J1 as [[mb [J11 [J12 J13]]] [J4 [gv J3]]]; subst.
    split. exists mb. repeat split; auto. omega. admit. (* MemProp *)
    split.
      intros.
      eapply mstore_preserves_mload_inv in Hst; eauto.
      destruct Hst as [gvs2 [H1 H2]].
      apply J4 in H1.
      eapply no_alias_overlap with (gvs1:=gv1); eauto.
      eapply operand__no_alias_with__tail; eauto.

      exists gv. 
      eapply mstore_preserves_mload; eauto.
      eapply operand__no_alias_with__tail; eauto.
Qed.

Lemma mstore_preserves_wf_lc: forall TD M' M mp2 t gv1 align
  (Hst: mstore TD M mp2 t gv1 align = Some M') lc
  (Hwf: wf_lc M lc),
  wf_lc M' lc.
Proof.
  unfold wf_lc.
  intros.
  apply Hwf in H.
  apply store_inv in Hst.
  destruct Hst as [blk' [ofs' [J1 J2]]].
  admit. (* Mem Props *)
Qed.

Lemma mstore_preserves_wf_ECStack_head_tail: forall maxb pinfo ECs TD M 
  gv1 align M' lc mp2 t gvs1 gl v1 (Hwfgl: wf_globals maxb gl) EC
  (H0 : Opsem.getOperandValue TD v1 lc gl = Some gvs1)
  (H1 : gv1 @ gvs1)
  (Hst: mstore TD M mp2 t gv1 align = Some M') lc1 (Heq: lc1 = Opsem.Locals EC)
  (Hht: wf_ECStack_head_tail maxb pinfo TD M lc (EC::ECs))
  (Hwf: wf_ECStack_head_tail maxb pinfo TD M lc1 ECs),
  wf_ECStack_head_tail maxb pinfo TD M' lc1 ECs.
Proof.
  intros.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros. 
  assert (wf_ECStack_head_in_tail maxb pinfo TD M lc ec0) as Hintl.
    apply Hht. simpl; auto.
  destruct ec0. intros.
  assert (no_alias gv1 gvsa) as J.
    eapply operand__no_alias_with__tail with(M:=M)(lc1:=lc); eauto; simpl; auto.
  apply_clear Hwf in H. simpl in H. eapply_clear H in H3.
  destruct H3 as [[mb [J11 J12]] [J2 J3]]; subst.
  split.
    exists mb. split; auto. admit. (* MemProp *)
  split; auto.
    intros.
    eapply mstore_preserves_mload_inv in Hst; eauto.
    destruct Hst as [gvs2 [J1 J4]].
    apply J3 in J1.
    eapply no_alias_overlap with (gvs1:=gv1); eauto.
Qed.

Lemma wf_ECStack_head_tail_cons__intro: forall maxb pinfo TD M lc ec1 ecs2,
  wf_ECStack_head_in_tail maxb pinfo TD M lc ec1 ->
  wf_ECStack_head_tail maxb pinfo TD M lc ecs2 ->
  wf_ECStack_head_tail maxb pinfo TD M lc (ec1::ecs2).
Proof.
  intros.
  unfold wf_ECStack_head_tail in *. 
  intros. 
  simpl in H1.
  destruct H1 as [EQ | H1]; subst; auto.
Qed.

Lemma mstore_preserves_wf_ECStack_in_tail : forall maxb pinfo TD M mp2 t align 
  M' gl vp (Hwfgl: wf_globals maxb gl) lc gvs1 gv1 v1 (Hwfpi: WF_PhiInfo pinfo) 
  mps2 (Hgetop': Opsem.getOperandValue TD vp lc gl = ret mps2)
  (H0 : Opsem.getOperandValue TD v1 lc gl = Some gvs1)
  (Hinp: mp2 @ mps2) (H1 : gv1 @ gvs1)
  (Hst: mstore TD M mp2 t gv1 align = Some M') ECs
  (Hht: wf_ECStack_head_tail maxb pinfo TD M lc ECs)
  (Hwf: wf_ECStack maxb pinfo TD M ECs),
  wf_ECStack maxb pinfo TD M' ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct Hwf as [J1 [J2 J3]].
    apply wf_ECStack_head_tail_cons__inv in Hht.
    destruct Hht as [Hht1 Hht2].
    split.
      eapply impure_cmd_preserves_wf_EC_tail with (M:=M); eauto.
        destruct a. intros. subst.
        eapply mstore_preserves_wf_defs_in_tail with (mps2:=mps2)(gvs1:=gvs1)
          (v:=v1)(lc1:=lc)(vp:=vp) in Hst; eauto; simpl; auto.
        eapply mstore_preserves_wf_lc; eauto.
    split; auto.
      destruct a. simpl in *.
      eapply mstore_preserves_wf_ECStack_head_tail with 
        (EC:=Opsem.mkEC CurFunction CurBB CurCmds Terminator Locals Allocas); 
        eauto.
        apply wf_ECStack_head_tail_cons__intro; auto.
Qed.

Lemma valid_ptrs_overlap: forall gvs1 gvs2 gvs0 bd,
  valid_ptrs bd gvs1 ->
  valid_ptrs bd gvs2 ->
  (forall (v : val) (m : AST.memory_chunk),
     In (v, m) gvs0 -> In (v, m) gvs1 \/ v = Vundef \/ In (v, m) gvs2) ->
  valid_ptrs bd gvs0.
Admitted.

Lemma mstore_preserves_wf_Mem : forall maxb TD M mp2 t gv1 align M' gvs1 gl
  (Hwfgl: wf_globals maxb gl) (lc:DGVMap) v1 (Hwflc: wf_lc M lc) 
  (H0 : Opsem.getOperandValue TD v1 lc gl = Some gvs1)
  (H1 : gv1 @ gvs1)
  (Hst: mstore TD M mp2 t gv1 align = Some M')
  (Hwf: wf_Mem maxb TD M),
  wf_Mem maxb TD M'.
Proof.
  intros. destruct Hwf as [J1 J2].
  assert (Mem.nextblock M = Mem.nextblock M') as EQ.
    admit. (* Mem Props *)
  rewrite EQ in *.
  split; eauto.
    intros.
    eapply mstore_preserves_mload_inv in H; eauto.
    destruct H as [gvs2 [J3 J4]].
    apply J1 in J3.
    eapply valid_ptrs_overlap with (gvs1:=gv1); eauto.
      eapply operand__lt_nextblock with (M:=M) in H0; eauto.
        rewrite EQ in H0; auto.
        rewrite EQ; auto.
Qed.

Lemma mstore_preserves_wf_als : forall TD M mp2 t gv1 align M' maxb als
  (Hst: mstore TD M mp2 t gv1 align = Some M') 
  (Hwf: wf_als maxb M als),
  wf_als maxb M' als.
Proof.
  intros. destruct Hwf as [J1 J2].
  split; auto.
    intros. 
    apply J2 in H; auto.
    admit. (* Mem Props *)
Qed.

Lemma mstore_preserves_wf_ECStack_head_tail': forall maxb pinfo ECs TD M 
  gv1 align M' lc mp2 t gvs1 gl v1 (Hwfgl: wf_globals maxb gl) 
  (H0 : Opsem.getOperandValue TD v1 lc gl = Some gvs1)
  (H1 : gv1 @ gvs1)
  (Hst: mstore TD M mp2 t gv1 align = Some M') 
  (Hwf: wf_ECStack_head_tail maxb pinfo TD M lc ECs),
  wf_ECStack_head_tail maxb pinfo TD M' lc ECs.
Proof.
  intros.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros. destruct ec0. intros.
  assert (no_alias gv1 gvsa) as J.
    eapply operand__no_alias_with__tail with (M:=M); eauto; simpl; auto.
  eapply_clear Hwf in H. simpl in H. eapply_clear H in H3.
  destruct H3 as [[mb [J11 J12]] [J2 J3]]; subst.
  split. exists mb. split; auto. admit. (* MemProp *)
  split; auto.
    intros.
    eapply mstore_preserves_mload_inv in Hst; eauto.
    destruct Hst as [gvs2 [H3 H2]].
    apply J3 in H3.
    eapply no_alias_overlap with (gvs1:=gv1); eauto.
Qed.

Lemma malloc_preserves_mload_inv: forall TD M M' mb align0 gn tsz 
  (Hal : malloc TD M tsz gn align0 = ret (M', mb))
  gptr gvs1 ty al 
  (H : mload TD M' gptr ty al = ret gvs1),
  mload TD M gptr ty al = ret gvs1 \/ ret gvs1 = gundef TD ty.
Admitted. (* MemProp *)

Lemma malloc_preserves_wf_ECStack_head_tail : forall maxb pinfo ECs TD M tsz gn 
  align0 M' lc mb t id0
  (Hmlc: malloc TD M tsz gn align0 = ret (M', mb))
  (Hwf: wf_ECStack_head_tail maxb pinfo TD M lc ECs),
  wf_ECStack_head_tail maxb pinfo TD M' 
    (updateAddAL (GVsT DGVs) lc id0
        ($ blk2GV TD mb # typ_pointer t $)) ECs.
Proof.
  intros.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros. apply Hwf in H. destruct ec0. intros.
  eapply_clear H in H1.
  destruct H1 as [[mb' [J11 J12]] [J2 J3]]; subst; eauto.
  split. exists mb'. split; auto. admit. (* MemProp *)
  split.
    intros.
    destruct (id_dec id0 id1); subst.
      rewrite lookupAL_updateAddAL_eq in H. inv H.
      admit. (* MemProp mb'<M.next=mb *)

      rewrite <- lookupAL_updateAddAL_neq in H; eauto.

    intros.
    eapply malloc_preserves_mload_inv in Hmlc; eauto.
    destruct Hmlc as [G | G]; subst; eauto.
      eapply undef_disjoint_with_ptr; eauto.
Qed.

Lemma malloc_preserves_wf_defs_in_tail : forall maxb pinfo TD M  
  M' als lc mb align0 gn tsz (Hal: malloc TD M tsz gn align0 = ret (M', mb))
  ids0 (Hwf: wf_defs maxb pinfo TD M lc ids0 als),
  wf_defs maxb pinfo TD M lc ids0 als ->
  wf_defs maxb pinfo TD M' lc ids0 als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    clear J2.
    destruct J1 as [[mb' [J11 [J12 J13]]] [J4 [gv J3]]]; subst.
    split. exists mb'. repeat split; auto. omega. admit. (* MemProp *)
    split.
      intros.
      eapply malloc_preserves_mload_inv in H0; eauto.
      destruct H0 as [G | G]; subst; eauto.
        eapply undef_disjoint_with_ptr; eauto.

      exists gv. admit. (* Mem Prop *)
Qed.

Lemma malloc_preserves_wf_lc_in_tail: forall TD M M' tsz gn align0 mb lc
  (Hmalloc: malloc TD M tsz gn align0 = ret (M', mb)) 
  (Hwf: wf_lc M lc), wf_lc M' lc.
Proof.
  unfold wf_lc.
  intros.
  admit. (* Mem Props *)
Qed.

Lemma malloc_preserves_wf_ECStack_head_tail' : forall maxb pinfo ECs TD M tsz gn 
  align0 M' lc mb 
  (Hmlc: malloc TD M tsz gn align0 = ret (M', mb))
  (Hwf: wf_ECStack_head_tail maxb pinfo TD M lc ECs),
  wf_ECStack_head_tail maxb pinfo TD M' lc ECs.
Proof.
  intros.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros. apply Hwf in H. destruct ec0. intros.
  eapply_clear H in H1.
  destruct H1 as [[mb' [J11 J12]] [J2 J3]]; subst; eauto.
  split. exists mb'. split; auto. admit. (* MemProp *)
  split; eauto.
    intros.
    eapply malloc_preserves_mload_inv in Hmlc; eauto.
    destruct Hmlc as [G | G]; subst; eauto.
      eapply undef_disjoint_with_ptr; eauto.
Qed.

Lemma malloc_preserves_wf_ECStack_in_tail : forall maxb pinfo TD M tsz gn align0 
  (Hwfpi: WF_PhiInfo pinfo) M' mb 
  (Hmlc: malloc TD M tsz gn align0 = ret (M', mb)) ECs
  (Hwf: wf_ECStack maxb pinfo TD M ECs),
  wf_ECStack maxb pinfo TD M' ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct Hwf as [J1 [J2 J3]].
    split.
      eapply impure_cmd_preserves_wf_EC_tail with (M:=M); eauto.
        destruct a. intros. subst.
        eapply malloc_preserves_wf_defs_in_tail in Hmlc; eauto.
        eapply malloc_preserves_wf_lc_in_tail; eauto. 
    split; auto.
      destruct a. simpl in *.
      eapply malloc_preserves_wf_ECStack_head_tail'; eauto.
Qed.

Lemma malloc_preserves_wf_Mem : forall maxb TD M tsz gn align0 M' mb
  (Hmlc: malloc TD M tsz gn align0 = ret (M', mb))
  (Hwf: wf_Mem maxb TD M),
  wf_Mem maxb TD M'.
Proof.
  intros. destruct Hwf as [J1 J2].
  assert (Mem.nextblock M + 1 = Mem.nextblock M') as EQ.
    admit. (* Mem Props *)
  split.
    rewrite <- EQ.
    intros.
    eapply malloc_preserves_mload_inv in H; eauto.
    destruct H as [G | G]; subst; eauto.
      apply J1 in G. eapply valid_ptrs__trans; eauto. omega.
      eapply undef_valid_ptrs; eauto.
 
    omega.
Qed.

Lemma malloc_preserves_wf_als : forall maxb TD M M' tsz gn align0 mb als
  (Hmalloc: malloc TD M tsz gn align0 = ret (M', mb)) 
  (Hwf: wf_als maxb M als),
  wf_als maxb M' (mb::als).
Proof.
  intros. destruct Hwf as [J1 J2].
  split.
    constructor; auto.
      intro J. apply J2 in J.
      admit. (* Mem Props *)

    intros. 
    simpl in H. 
    destruct H as [H | H]; subst.
      admit. (* Mem Props *)

      apply J2 in H.
      admit. (* Mem Props *)
Qed.

Lemma impure_cmd_updated_preserves_wf_EC : forall maxb pinfo TD M M' lc F B 
  als als' tmn cs c0 l1 ps1 cs1' ifs S
  (Heq: B = block_intro l1 ps1 (cs1' ++ c0 :: cs) tmn)
  (HwfS: wf_system ifs S) los nts (Heq': TD = (los, nts)) Ps
  (HMinS: moduleInSystemB (module_intro los nts Ps) S = true)
  (HFinPs: InProductsB (product_fdef F) Ps = true)
  (HBinF: blockInFdefB B F = true) id0
  (Hid : getCmdID c0 = Some id0) gv3
  (Hwfdefs: forall ids0,
              F = (PI_f pinfo) ->
              inscope_of_pc F B (c0::cs) tmn = Some ids0 ->
              wf_defs maxb pinfo TD M lc ids0 als ->
              wf_defs maxb pinfo TD M' 
                (updateAddAL (GVsT DGVs) lc id0 gv3) (id0::ids0) als')
  (Hwflc: wf_lc M lc -> wf_lc M' (updateAddAL (GVsT DGVs) lc id0 gv3)) EC
  (Heq: EC = {| Opsem.CurFunction := F;
               Opsem.CurBB := B;
               Opsem.CurCmds := c0 :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |})
  (HwfEC: wf_ExecutionContext maxb pinfo TD M EC),
  wf_ExecutionContext maxb pinfo TD M'
    {| Opsem.CurFunction := F;
       Opsem.CurBB := B;
       Opsem.CurCmds := cs;
       Opsem.Terminator := tmn;
       Opsem.Locals := updateAddAL (GVsT DGVs) lc id0 gv3;
       Opsem.Allocas := als' |}.
Proof.
  simpl. intros. subst.
  destruct HwfEC as [J1 J2].
  split; auto.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  unfold inscope_of_pc in *.
  remember (inscope_of_cmd (PI_f pinfo) 
    (block_intro l1 ps1 (cs1' ++ c0 :: cs) tmn) c0) as R1. 
  assert (HeqR1':=HeqR1).
  unfold inscope_of_cmd, inscope_of_id in HeqR1'.

  destruct R1; try solve [inversion J1].
  repeat (split; try solve [auto]).
      destruct cs; simpl_env in *.
      SSSSCase "cs = nil".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs1')) 
          as Hnotin.
          eapply preservation_helper1; eauto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1' J2']].
        rewrite <- J1'.
        assert (In c0 (cs1' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        assert (HwfF:=HFinPs). eapply wf_system__wf_fdef in HwfF; eauto.
        rewrite Hid in J2'.
        eapply wf_defs_eq; eauto.       

      SSSSCase "cs <> nil".
        assert (NoDup (getCmdsLocs (cs1' ++ [c0] ++ [c] ++ cs))) 
          as Hnodup.
          eapply preservation_helper2; eauto.

        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1' J2']].        
        rewrite <- J1'.
        assert (In c0 (cs1' ++ [c0] ++ [c] ++ cs)) 
          as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite Hid in J2'. 
        eapply wf_defs_eq; eauto.
Qed.

Lemma valid_ptrs__no_alias__fresh_ptr: forall bound TD mb t (Hbd: bound < mb) 
  gvs, valid_ptrs bound gvs -> 
  no_alias gvs ($ blk2GV TD mb # typ_pointer t $).
Proof.
  induction gvs as [|[]]; simpl; intros.
    apply no_alias_nil.

    destruct v; auto.
    destruct H.
    apply IHgvs in H0. rewrite simpl_blk2GV in *. simpl in *.
    destruct H0. 
    repeat split; auto.
      intro J. subst. contradict H; omega.
Qed.

Lemma ptr_no_alias__no_alias_with_blk : forall b i0 m gvs2,
  no_alias [(Vptr b i0, m)] gvs2 -> no_alias_with_blk gvs2 b.
Proof. 
  induction gvs2 as [|[]]; simpl; intros; auto.
    destruct v; auto.
    destruct H. destruct H.
    split; auto.
Qed.

Lemma no_alias_sym: forall gvs2 gvs1, no_alias gvs1 gvs2 -> no_alias gvs2 gvs1.
Proof.
  induction gvs1 as [|[]]; simpl; intros; auto.
    simpl_env in H.
    apply no_alias_split in H.
    destruct H as [H1 H2].
    destruct v; auto.
    split; auto.
      apply ptr_no_alias__no_alias_with_blk in H1; auto.
Qed.

Lemma alloca_preserves_wf_defs_at_head : forall maxb pinfo TD M  
  M' gl als lc t v
  (Hwfgl: wf_globals maxb gl) mb id0 tmn align0 cs cs1' l1 ps1 F gn tsz
  (Hal: malloc TD M tsz gn align0 = ret (M', mb)) (HwfM: wf_Mem maxb TD M)
  (Hwflc : wf_lc M lc),
  forall ids0,
   F = PI_f pinfo ->
   inscope_of_pc F
     (block_intro l1 ps1 (cs1' ++ insn_alloca id0 t v align0 :: cs) tmn)
     (insn_alloca id0 t v align0 :: cs) tmn = ret ids0 ->
   wf_defs maxb pinfo TD M lc ids0 als ->
   wf_defs maxb pinfo TD M'
     (updateAddAL (GVsT DGVs) lc id0
        ($ blk2GV TD mb # typ_pointer t $)) 
     (id0 :: ids0) (mb :: als).
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  destruct (id_dec id0 (PI_id pinfo)); subst.
    rewrite lookupAL_updateAddAL_eq in Hlkp.
    inv Hlkp.
    split.
      split.
        exists mb. admit. (* WF, MemProp *)
      split.
        intros.
        assert (mload TD M gptr ty al = ret gvs1 \/
                Some gvs1 = gundef TD ty) as J.
          eapply malloc_preserves_mload_inv; eauto.
        destruct J as [J | J].
          destruct HwfM as [HwfM _].
          apply HwfM in J.
          eapply valid_ptrs__no_alias__fresh_ptr; eauto.
          admit. (* MemProp *)

          eapply undef_disjoint_with_ptr; eauto.

        admit. (* MemProp by Hal. *)

      intros.
      unfold wf_non_alloca_GVs.
      destruct (id_dec id0 (PI_id pinfo)); auto.
      rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
      apply Hwflc in Hlk0.
      eapply valid_ptrs__no_alias__fresh_ptr; eauto.
      admit. (* MemProp *)

    rewrite <- lookupAL_updateAddAL_neq in Hlkp; auto.
    simpl in Hpindom.
    destruct Hpindom as [Hpindom | Hpindom]; subst; try congruence.
    assert (Hlkp':=Hlkp).
    apply H1 in Hlkp; auto.
    destruct Hlkp as [J1 J2].
    split.
      destruct J1 as [[mb' [J31 [J32 J33]]] [J4 [gv J5]]]; subst.
      split.
        exists mb'. split; auto. simpl. split; auto. admit. (* MemProp *)
      split.
        intros.
        assert (mload TD M gptr ty al = ret gvs1 \/
                Some gvs1 = gundef TD ty) as J.
          eapply malloc_preserves_mload_inv; eauto.
        destruct J as [J | J]; eauto.
          eapply undef_disjoint_with_ptr; eauto.

        exists gv. admit. (* MemProp by Hal. *)

      intros.
      unfold wf_non_alloca_GVs.
      destruct (id_dec id1 (PI_id pinfo)); auto.
      destruct (id_dec id0 id1); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk0.
        inv Hlk0.
        apply Hwflc in Hlkp'.
        apply no_alias_sym.
        eapply valid_ptrs__no_alias__fresh_ptr; eauto.
        admit. (* MemProp *)

        rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
        apply J2 in Hlk0.
        unfold wf_non_alloca_GVs in Hlk0.
        destruct (id_dec id1 (PI_id pinfo)); subst; try congruence.
Qed.

Lemma malloc_preserves_wf_defs_at_head : forall maxb pinfo TD M  
  M' gl als lc t v
  (Hwfgl: wf_globals maxb gl) mb id0 tmn align0 cs cs1' l1 ps1 F gn tsz
  (Hal: malloc TD M tsz gn align0 = ret (M', mb)) (HwfM: wf_Mem maxb TD M)
  (Hwflc : wf_lc M lc),
  forall ids0,
   F = PI_f pinfo ->
   inscope_of_pc F
     (block_intro l1 ps1 (cs1' ++ insn_malloc id0 t v align0 :: cs) tmn)
     (insn_alloca id0 t v align0 :: cs) tmn = ret ids0 ->
   wf_defs maxb pinfo TD M lc ids0 als ->
   wf_defs maxb pinfo TD M'
     (updateAddAL (GVsT DGVs) lc id0
        ($ blk2GV TD mb # typ_pointer t $)) 
     (id0 :: ids0) als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  destruct (id_dec id0 (PI_id pinfo)); subst.
    rewrite lookupAL_updateAddAL_eq in Hlkp.
    inv Hlkp.
    split.
      split.
        exists mb. admit. (* WF, MemProp *)
      split.
        intros.
        assert (mload TD M gptr ty al = ret gvs1 \/
                Some gvs1 = gundef TD ty) as J.
          eapply malloc_preserves_mload_inv; eauto.
        destruct J as [J | J].
          destruct HwfM as [HwfM _].
          apply HwfM in J.
          eapply valid_ptrs__no_alias__fresh_ptr; eauto.
          admit. (* MemProp *)

          eapply undef_disjoint_with_ptr; eauto.

        admit. (* MemProp by Hal. *)

      intros.
      unfold wf_non_alloca_GVs.
      destruct (id_dec id0 (PI_id pinfo)); auto.
      rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
      apply Hwflc in Hlk0.
      eapply valid_ptrs__no_alias__fresh_ptr; eauto.
      admit. (* MemProp *)

    rewrite <- lookupAL_updateAddAL_neq in Hlkp; auto.
    simpl in Hpindom.
    destruct Hpindom as [Hpindom | Hpindom]; subst; try congruence.
    assert (Hlkp':=Hlkp).
    apply H1 in Hlkp; auto.
    destruct Hlkp as [J1 J2].
    split.
      destruct J1 as [[mb' [J31 [J32 J33]]] [J4 [gv J5]]]; subst.
      split.
        exists mb'. simpl. repeat split; auto. omega. admit. (* MemProp *)
      split.
        intros.
        assert (mload TD M gptr ty al = ret gvs1 \/
                Some gvs1 = gundef TD ty) as J.
          eapply malloc_preserves_mload_inv; eauto.
        destruct J as [J | J]; eauto.
          eapply undef_disjoint_with_ptr; eauto.

        exists gv. admit. (* MemProp by Hal. *)

      intros.
      unfold wf_non_alloca_GVs.
      destruct (id_dec id1 (PI_id pinfo)); auto.
      destruct (id_dec id0 id1); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk0.
        inv Hlk0.
        apply Hwflc in Hlkp'.
        apply no_alias_sym.
        eapply valid_ptrs__no_alias__fresh_ptr; eauto.
        admit. (* MemProp *)

        rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
        apply J2 in Hlk0.
        unfold wf_non_alloca_GVs in Hlk0.
        destruct (id_dec id1 (PI_id pinfo)); subst; try congruence.
Qed.

Lemma malloc_preserves_wf_lc: forall TD M M' tsz gn align0 mb t id0 lc
  (Hmalloc: malloc TD M tsz gn align0 = ret (M', mb)) 
  (Hwf: wf_lc M lc),
  wf_lc M' (updateAddAL (GVsT DGVs) lc id0 ($ blk2GV TD mb # typ_pointer t $)).
Proof.
  unfold wf_lc.
  intros.
  destruct (id_dec id0 id1); subst.
    rewrite lookupAL_updateAddAL_eq in H.
    admit. (* Mem Props *)

    rewrite <- lookupAL_updateAddAL_neq in H; auto.
    apply Hwf in H.
    admit. (* Mem Props *)
Qed.

Ltac simpl_ctx Hinv HwfS1 :=
  destruct Hinv as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [HwfEC0 HwfCall]
    ]]]]]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0;
  destruct HwfS1 as [[HwfEC [HwfECs Hwfht]] [Hnonup1 HwfM1]].

Lemma preservation : forall maxb pinfo cfg S1 S2 tr
  (Hinv: OpsemPP.wf_State cfg S1)
  (Hwfg: wf_globals maxb (OpsemAux.Globals cfg)) (Hinbd: 0 <= maxb)
  (HwfPI: WF_PhiInfo pinfo) (HsInsn: Opsem.sInsn cfg S1 S2 tr)
  (HwfS1: wf_State maxb pinfo cfg S1), wf_State maxb pinfo cfg S2.
Proof.
  intros.
  (sInsn_cases (induction HsInsn) Case); destruct TD as [los nts]; simpl HwfS1.

Case "sReturn". eapply preservation_return; eauto. 
Case "sReturnVoid". admit.
Case "sBranch". admit.
Case "sBranch_uncond". admit.
Case "sBop".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    eapply BOP__wf_GVs_in_ECs; eauto.
      admit. (* WF *)
Case "sFBop". admit.
Case "sExtractValue". admit. 
(* tricky case, 
   we need to ensure that all extractable values cannot be aliased *)
Case "sInsertValue". admit. 
(* tricky case, 
   we need to ensure that we are not inserting aliased values *)
Case "sMalloc". 
  simpl_ctx Hinv HwfS1.
  split.
    split.
      eapply impure_cmd_updated_preserves_wf_EC; eauto.
        intros. subst.
        apply wf_EC__wf_lc in HwfEC.
        eapply malloc_preserves_wf_defs_at_head with (tmn:=tmn); eauto.
        eapply malloc_preserves_wf_lc; eauto.
    split.
      eapply malloc_preserves_wf_ECStack_in_tail in H2; eauto.
      eapply malloc_preserves_wf_ECStack_head_tail in H2; eauto.
  split.
    eapply malloc_preserves_wf_als in H2; eauto.
      simpl_env in H2.
      apply wf_als_split in H2. destruct H2; auto.
    eapply malloc_preserves_wf_Mem in H2; eauto.

Case "sFree". 
  simpl_ctx Hinv HwfS1.
  split.
    split.
      eapply impure_cmd_non_updated_preserves_wf_EC with (M:=Mem); eauto.
        intros. subst.
        eapply free_preserves_wf_defs_at_head; eauto.
          admit. (* WF PhiInfo *)
        eapply free_preserves_wf_lc; eauto.
    split.
      eapply free_preserves_wf_ECStack_in_tail in H1; eauto.
      eapply free_preserves_wf_ECStack_head_tail in H1; eauto.
  split.
    eapply free_preserves_wf_als in H1; eauto.
    eapply free_preserves_wf_Mem in H1; eauto.

Case "sAlloca". 
  simpl_ctx Hinv HwfS1.
  split.
    split.
      eapply impure_cmd_updated_preserves_wf_EC; eauto.
        intros. subst.
        apply wf_EC__wf_lc in HwfEC.
        eapply alloca_preserves_wf_defs_at_head; eauto.
        eapply malloc_preserves_wf_lc; eauto.
    split.       
      eapply malloc_preserves_wf_ECStack_in_tail in H2; eauto.
      eapply malloc_preserves_wf_ECStack_head_tail in H2; eauto.
  split.
    eapply malloc_preserves_wf_als in H2; eauto.
    eapply malloc_preserves_wf_Mem in H2; eauto.

Case "sLoad". 
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    destruct HwfS1 as [[[_ Hwflc] [_ Hwfstk]] [_ HwfM]]. 
    eapply mload__wf_GVs_in_ECs; eauto using wf_EC__wf_lc.
      admit. (* WF *)
Case "sStore". 
  simpl_ctx Hinv HwfS1.
  assert (wf_lc Mem lc) as Hwflc.
    apply wf_EC__wf_lc in HwfEC; auto.
  split.
    split.
      eapply impure_cmd_non_updated_preserves_wf_EC with (M:=Mem); eauto.
        intros. subst.
        eapply mstore_preserves_wf_defs_at_head with (gvs1:=gvs1) in H3; eauto.
          admit. (* WF PhiInfo *)
        eapply mstore_preserves_wf_lc; eauto.
    split.
      eapply mstore_preserves_wf_ECStack_in_tail with (gvs1:=gvs1) in H3; eauto.
      eapply mstore_preserves_wf_ECStack_head_tail' with (gvs1:=gvs1) in H3; 
        eauto.
  split.
    eapply mstore_preserves_wf_als in H3; eauto.
    eapply mstore_preserves_wf_Mem with (gvs1:=gvs1) in H3; eauto.

Case "sGEP". 
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    destruct HwfS1 as [[[_ Hwflc] [_ Hwfstk]] [_ [_ HwfM]]]. 
    eapply GEP__wf_GVs_in_ECs; eauto using wf_EC__wf_lc.
      admit. (* WF PI *)
      admit. (* WF *)

Case "sTrunc". admit.
Case "sExt". admit.
Case "sCast". 
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    destruct HwfS1 as [[[_ Hwflc] [_ Hwfstk]] [_ [_ HwfM]]]. 
    eapply CAST__wf_GVs_in_ECs; eauto.
      admit. (* WF PI *)
      admit. (* WF *)

Case "sIcmp". admit.
Case "sFcmp". admit.
Case "sSelect". admit. (* can return ptr *)
Case "sCall". 
Focus.
  destruct Hinv as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [HwfEC0 HwfCall]
    ]]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0.
  destruct HwfS1 as 
    [[[Hinscope1 Hwflc1] [HwfECs Hfr2]] [Hdisjals HwfM]].
  simpl in Hdisjals.
  fold wf_ECStack in HwfECs.
  assert (InProductsB (product_fdef (fdef_intro 
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    apply OpsemAux.lookupFdefViaPtr_inversion in H1.
    destruct H1 as [fn [H11 H12]].
    eapply lookupFdefViaIDFromProducts_inv; eauto.
  split; auto.
  split.
  SCase "1".     
    assert (uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb)) as Huniq.
      eapply wf_system__uniqFdef; eauto.
    assert (wf_fdef nil S (module_intro los nts Ps) 
      (fdef_intro (fheader_intro fa rt fid la va) lb)) as HwfF.
      eapply wf_system__wf_fdef; eauto.
    split.
      destruct (fdef_dec (PI_f pinfo) 
                 (fdef_intro (fheader_intro fa rt fid la va) lb)); auto.
      assert (ps'=nil) as EQ.
        eapply entryBlock_has_no_phinodes with (ifs:=nil)(s:=S); eauto.        
      subst.
      apply dom_entrypoint in H2. 
      unfold inscope_of_pc in *.
      destruct cs'.
        unfold inscope_of_tmn.
        remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
          !! l') as R.
        destruct R. simpl in H2. subst. simpl.

        eapply initLocals_preserves_wf_defs; eauto.

        unfold inscope_of_cmd, inscope_of_id.
        remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
          !! l') as R.
        destruct R. simpl. simpl in H2. subst. simpl.
        destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n]; 
          try solve [contradict n; auto]. 
        eapply initLocals_preserves_wf_defs; eauto.

      destruct HwfM.
      eapply initLocals_preserves_wf_lc; eauto.

  split.
    repeat (split; auto). 
    simpl.
    eapply initLocals_preserves_wf_ECStack_head_tail; eauto.
      simpl. admit. (* WFPI *)

Unfocus.

Case "sExCall". 
  destruct HwfS1 as [[HwfEC [HwfECs Hwfht]] [Hnonup1 HwfM1]].
  assert (wf_lc Mem lc) as Hwflc.
    apply wf_EC__wf_lc in HwfEC; auto.
  unfold Opsem.exCallUpdateLocals in H5.
  destruct noret0.
    inv H5. 
    split.
      split.
        eapply callExternalProc_preserves_wf_EC; eauto.
      split.
        eapply callExternalFunction_preserves_wf_ECStack; eauto.
        eapply callExternalProc_preserves_wf_ECStack_head_tail; eauto.
    split.
      eapply callExternalFunction_preserves_wf_als; eauto.
      eapply callExternalFunction_preserves_wf_Mem; eauto.

    destruct oresult; inv H5.
    destruct ft; tinv H7.
    remember (fit_gv (los, nts) ft g) as R.
    destruct R; inv H7.
    split.
      split.
        eapply callExternalFun_preserves_wf_EC with (ca:=ca)(fv:=fv); eauto. 
      split.
        eapply callExternalFunction_preserves_wf_ECStack; eauto.
        eapply callExternalFun_preserves_wf_ECStack_head_tail; eauto. 
    split.
      eapply callExternalFunction_preserves_wf_als; eauto.
      eapply callExternalFunction_preserves_wf_Mem; eauto.
Qed.

End Promotability.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)

