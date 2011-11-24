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
Require Import memory_props.

Module Promotability.

Export MemProps.

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
  (als:list Values.block) : Prop :=
forall gvsa
  (Hlkp: lookupAL _ lc (PI_id pinfo) = Some gvsa),
  wf_alloca_GVs maxb pinfo TD M gvsa als /\
  (forall id0 gvs0 
   (*Hin0: In id0 ids0*) 
   (Hlk0: lookupAL _ lc id0 = Some gvs0),
   wf_non_alloca_GVs pinfo id0 gvs0 gvsa).

(* Except domination property, the other properties are the same for a lot of 
   proofs, we should prove them all for once. Or, we do not need to use them
   in this invariant, we can assume the invariant in opsem_wf, which is 
   preserved *)
Definition wf_ExecutionContext (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (ec:Opsem.ExecutionContext) : Prop :=
let '(Opsem.mkEC f b cs tmn lc als) := ec in
(if (fdef_dec (PI_f pinfo) f) then wf_defs maxb pinfo TD M lc als else True)
/\ wf_lc M lc.

Definition wf_ECStack_head_in_tail (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (lc:DGVMap) (ec0:Opsem.ExecutionContext) : Prop :=
let '(Opsem.mkEC f0 b0 cs0 tmn0 lc0 _) := ec0 in
forall gvsa, 
  f0 = PI_f pinfo ->
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

Definition wf_State (maxb:Values.block) (pinfo:PhiInfo) (cfg:OpsemAux.Config) 
  (S:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg _ td _ _ _ ) := cfg in
let '(Opsem.mkState ecs M) := S in
wf_ECStack maxb pinfo td M ecs /\
wf_als maxb M 
  (flat_map (fun ec => let '(Opsem.mkEC _ _ _ _ _ als) := ec in als) ecs) /\
wf_Mem maxb td M.

Definition wf_GVs (maxb:Values.block)(pinfo:PhiInfo)(TD:targetdata)(M:mem)
  (lc:DGVMap)(als:list Values.block)(id1:id)(gv1:GVsT DGVs)
  : Prop :=
  (forall gvsa,
     lookupAL _ lc (PI_id pinfo) = Some gvsa ->
     no_alias gv1 gvsa) /\
  (id1 = (PI_id pinfo) ->
     (forall id0 gvs0,
        lookupAL (GVsT DGVs) lc id0 = ret gvs0 ->
        no_alias gvs0 gv1) /\
     wf_alloca_GVs maxb pinfo TD M gv1 als).

Lemma wf_defs_updateAddAL: forall maxb pinfo TD M lc' i1 gv1 als
  (HwfDef: wf_defs maxb pinfo TD M lc' als)
  (Hwfgvs: wf_GVs maxb pinfo TD M lc' als i1 gv1),
  wf_defs maxb pinfo TD M (updateAddAL _ lc' i1 gv1) als.
Proof.
  intros. unfold wf_defs. intros.
  destruct Hwfgvs as [Hwfgvs1 Hwfgvs2].
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
  (Hwfdefs:   F = (PI_f pinfo) ->
              wf_defs maxb pinfo TD M lc als ->
              wf_defs maxb pinfo TD M' lc als)
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
Qed.

(* We need a generic proof for this one and the one for atom *)
Lemma NoDup_disjoint : forall (l2 l1 : list Z) (i0 : Z),
  NoDup (l1 ++ l2) -> In i0 l2 -> ~ In i0 l1.
Proof.
  induction l1; simpl; intros; auto.
    inv H.
    intro J. 
    destruct J as [J | J]; subst.
      apply H3. apply in_or_app. auto.
      eapply IHl1 in H4; eauto.
Qed.

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

Lemma zeroconst2GV_disjoint_with_runtime_alloca: forall t maxb gl g td mb t0
  (Hwfg: wf_globals maxb gl)
  (Hc2g : ret g = zeroconst2GV td t)
  (Hle: maxb < mb),
  no_alias g ($ blk2GV td mb # typ_pointer t0 $) /\ valid_ptrs (maxb + 1) g.
Proof.
  intros. rewrite simpl_blk2GV.
  destruct zeroconst2GV_disjoint_with_runtime_ptr_mutrec as [J _].
  unfold zeroconst2GV_disjoint_with_runtime_ptr_prop in J. 
  eapply J; eauto.
Qed.

Tactic Notation "eapply_clear" hyp(H1) "in" hyp(H2) :=
  eapply H1 in H2; eauto; clear H1.

Tactic Notation "apply_clear" hyp(H1) "in" hyp(H2) :=
  apply H1 in H2; auto; clear H1.

Lemma wf_globals_disjoint_with_runtime_alloca: forall maxb td t0
  (g0 : GenericValue) i0  mb (Hle : maxb < mb) gl (Hwfg : wf_globals maxb gl) 
  (HeqR : ret g0 = lookupAL GenericValue gl i0),
  no_alias g0 ($ blk2GV td mb # typ_pointer t0 $) /\ valid_ptrs (maxb + 1) g0.
Proof.
  intros. rewrite simpl_blk2GV. 
  eapply wf_globals_disjoint_with_runtime_ptr; eauto.
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
  destruct const2GV_disjoint_with_runtime_ptr_mutrec as [J1 J2].
  unfold const2GV_disjoint_with_runtime_ptr_prop in J1. 
  rewrite simpl_blk2GV.
  eapply J1 in HeqR; eauto.
  destruct HeqR. 
  destruct Hwfg.
  eapply cgv2gvs_preserves_no_alias; eauto.
Qed.

Lemma const2GV_valid_ptrs: forall c0 maxb gl g td 
  (Hwfg: wf_globals maxb gl)
  (Hc2g : ret g = @Opsem.const2GV DGVs td gl c0),
  valid_ptrs (maxb + 1) g.
Proof.
  unfold Opsem.const2GV.
  intros.
  inv_mbind'. inv H0.
  destruct const2GV_disjoint_with_runtime_ptr_mutrec as [J1 J2].
  unfold const2GV_disjoint_with_runtime_ptr_prop in J1. 
  eapply J1 with (mb:=maxb+1)(ofs:=Int.repr 31 0)
    (m:=AST.Mint (Size.mul Size.Eight (getPointerSize td) - 1)) in HeqR; 
    eauto; try omega.
  destruct HeqR. 
  destruct Hwfg.
  eapply cgv2gvs_preserves_valid_ptrs; eauto; try omega.
Qed.

Lemma preservation_return_helper: forall (g : GVsT DGVs) pinfo lc' Mem'
  als' td maxb Mem ECs lc gl t Result
  (HeqR1 : ret g = Opsem.getOperandValue td Result lc gl)
  (g0 : GVsT DGVs)
  (HeqR2 : ret g0 = lift_op1 DGVs (fit_gv td t) g t)
  (Hwfg : wf_globals maxb gl) EC
  (Heq1 : Opsem.CurFunction EC = PI_f pinfo)
  (Heq2 : Opsem.Locals EC = lc')
  (Hfr1 : wf_ECStack_head_tail maxb pinfo td Mem lc (EC :: ECs))
  (Hinscope2 : wf_defs maxb pinfo td Mem' lc' als')
  (gvsa : GVsT DGVs)
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
  Opaque lift_op1.
Qed.

Ltac SSSSSCase name := Case_aux subsubsubsubsubcase name.
Ltac SSSSSSCase name := Case_aux subsubsubsubsubsubcase name.

Lemma free_preserves_wf_ECStack_head_tail : forall maxb pinfo TD M M' lc mptr0
  (Hfree: free TD M mptr0 = ret M') ECs 
  (Hwf: wf_ECStack_head_tail maxb pinfo TD M lc ECs),
  wf_ECStack_head_tail maxb pinfo TD M' lc ECs.
Proof.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros. destruct ec0. intros.
  eapply Hwf in H; eauto. clear Hwf.
  eapply_clear H in H1.
  destruct H1 as [[mb [J11 J12]] [J2 J3]]; subst.
  split.
    exists mb. split; auto. 
    erewrite <- nextblock_free; eauto.
  split; auto.
    intros.
    eapply free_preserves_mload_inv in H; eauto.
Qed.

Lemma operand__no_alias_with__tail: forall maxb pinfo TD M lc1 lc2 mptr0 gl
  (Hwfgl : wf_globals maxb gl) v mptrs EC
  (Heq1: Opsem.CurFunction EC = PI_f pinfo)
  (Heq2: Opsem.Locals EC = lc2)
  (Hht : wf_ECStack_head_in_tail maxb pinfo TD M lc1 EC)
  (gvsa : GVsT DGVs) (Hin: mptr0 @ mptrs)
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

Definition wf_use_at_head (pinfo:PhiInfo) (v:value) :=
used_in_value (PI_id pinfo) v = false.

Lemma free_preserves_wf_defs_in_tail : forall maxb pinfo TD M  
  M' lc1 mptr0 mptrs gl v als lc2 
  (Hgetop: Opsem.getOperandValue TD v lc1 gl = ret mptrs)
  (Hin: mptr0 @ mptrs) (Hwfgl: wf_globals maxb gl)
  (Hfree: free TD M mptr0 = ret M') EC
  (Heq1: Opsem.CurFunction EC = PI_f pinfo)
  (Heq2: Opsem.Locals EC = lc2)
  (Hht: wf_ECStack_head_in_tail maxb pinfo TD M lc1 EC)
  (Hwf: wf_defs maxb pinfo TD M lc2 als),
  wf_defs maxb pinfo TD M' lc2 als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hlkp.
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
  (Hin : mptr0 @ mptrs) (Hwfgl : wf_globals maxb gl) M
  (Hwfu: wf_use_at_head pinfo v) (Hwf: wf_defs maxb pinfo TD M lc als)
  (gvsa : GVsT DGVs) (Hlkp : lookupAL (GVsT DGVs) lc (PI_id pinfo) = ret gvsa),
  no_alias mptr0 gvsa.
Proof.
  intros.
  apply Hwf in Hlkp; auto.
  destruct Hlkp as [[J1 [J4 [gv J3]]] J2].
  inv Hin.
  destruct v; simpl in Hgetop.
    apply J2 in Hgetop; auto.
    unfold wf_non_alloca_GVs in Hgetop.
    destruct (id_dec i0 (PI_id pinfo)); subst; auto.
      inv Hwfu. 
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
  (Hwfu: wf_use_at_head pinfo v) 
  (Hwf: wf_defs maxb pinfo TD M lc als),
  wf_defs maxb pinfo TD M' lc als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hlkp.
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
  (Hwfdefs:
     let '(Opsem.mkEC F B cs tmn lc als) := EC in
     F = (PI_f pinfo) ->
     wf_defs maxb pinfo TD M lc als ->
     wf_defs maxb pinfo TD M' lc als)
  (Hwflc: wf_lc M (@Opsem.Locals DGVs EC) -> wf_lc M' (Opsem.Locals EC))
  (Hwf: wf_ExecutionContext maxb pinfo TD M EC),
  wf_ExecutionContext maxb pinfo TD M' EC.
Proof.
  destruct EC. simpl. intros.
  destruct Hwf as [J1 J2].
  split; auto.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
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

Lemma free_allocas_preserves_mload: forall TD al t mb gv als Mem' Mem 
  (H0 : ~ In mb als)
  (H1 : free_allocas TD Mem als = ret Mem')
  (H2 : mload TD Mem ($ blk2GV TD mb # typ_pointer t $) t al = ret gv),
  mload TD Mem' ($ blk2GV TD mb # typ_pointer t $) t al = ret gv.
Proof.
  induction als; simpl; intros.
    inv H1. auto.

    inv_mbind'.
    apply IHals in H3; auto.
    eapply free_preserves_mload; eauto.
    unfold_blk2GV. 
Local Transparent gv2gvs.
  unfold gv2gvs. simpl. split; auto.
Opaque gv2gvs. 
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

Lemma free_allocas_preserves_wf_defs: forall maxb pinfo TD Mem lc' als0 als Mem',
  wf_defs maxb pinfo TD Mem lc' als0 ->
  NoDup (als ++ als0) ->
  free_allocas TD Mem als = ret Mem' ->
  wf_defs maxb pinfo TD Mem' lc' als0.
  (* This is only true if als is always disjoint with pinfo.id *) 
Proof.
  intros. unfold wf_defs in *. intros.
  apply H in Hlkp; auto. clear H.
  destruct Hlkp as [J1 J2]. 
  split; eauto using free_allocas_preserves_wf_alloca.
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
Local Transparent lift_op1. unfold lift_op1 in HeqR0. simpl in HeqR0.
    unfold MDGVs.lift_op1, fit_gv in HeqR0. symmetry in HeqR0.
    inv_mbind. 
    destruct (sizeGenericValue g =n= nat_of_Z (ZRdiv (Z_of_nat n) 8)).
      inv H0. 
      eapply operand__lt_nextblock in HeqR; eauto.

      unfold gundef in H0. inv_mbind. simpl. auto.
Opaque lift_op1.
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
  lc2 als' als M M' (Hfree: free_allocas TD M als = ret M')
  (Hndp: NoDup (als++als')) (Hwf: wf_defs maxb pinfo TD M lc2 als'),
  wf_defs maxb pinfo TD M' lc2 als'.
Proof.
  induction als; simpl; intros.
    inv Hfree. auto.

    inv_mbind. inv Hndp.
    apply IHals in H0; auto.

  unfold wf_defs. 
  intros gvsa Hlkp.
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
  (Hwfgv: forall ec0 (Hin : In ec0 ECs) (gvsa : GVsT DGVs)
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
  eapply_clear H0 in H2.
  destruct H2 as [J1 [J2 J3]].
  split; auto.
  split; auto.
    intros. 
    destruct (id_dec id0 id1); subst.
      rewrite lookupAL_updateAddAL_eq in H.
      inv H. auto.

      rewrite <- lookupAL_updateAddAL_neq in H; eauto.
Qed.

Local Transparent lift_op1. 

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

Lemma NoDup_split': forall A (l1 l2:list A),
  NoDup (l1++l2) ->
  NoDup l1 /\ NoDup l2 /\ (forall (a:A), In a l1 -> ~ In a l2).
Proof.
  induction l1; simpl; intros; auto.
    inv H.
    apply IHl1 in H3. destruct H3 as [J1 [J2 J3]].
    split.
      constructor; auto.
        intro J. apply H2. apply in_or_app; auto.
    split; auto.
      intros. 
      destruct H as [H | H]; subst; auto.
        intro J. apply H2. apply in_or_app; auto.
Qed.

Lemma IngetCmdsLocs__lookupCmdViaIDFromCmds: forall c1 cs1
  (Huniq: NoDup (getCmdsLocs cs1)) (H0 : In c1 cs1),
  lookupCmdViaIDFromCmds cs1 (getCmdLoc c1) = Some c1.
Proof.
  induction cs1; simpl; intros.
    inv H0.

    destruct H0 as [H0 | H0]; subst.
      destruct (eq_atom_dec (getCmdLoc c1) (getCmdLoc c1)); auto.
        congruence.
      inv Huniq.
      destruct (eq_atom_dec (getCmdLoc c1) (getCmdLoc a)); auto.
        contradict H2. rewrite <- e. apply In_InCmdLocs; auto. 
Qed.

Lemma IngetCmdsIDs__lookupCmdViaIDFromFdef: forall c1 l1 ps1 cs1 tmn1 f
  (Huniq: uniqFdef f)
  (H : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (H0 : In c1 cs1),
  lookupInsnViaIDFromFdef f (getCmdLoc c1) = Some (insn_cmd c1).
Proof.
  destruct f as [[] bs]. simpl. intros.
  destruct Huniq as [_ Huniq].
  apply NoDup_split in Huniq.
  destruct Huniq as [_ Huniq].
  generalize dependent l1.
  generalize dependent ps1.
  generalize dependent cs1.
  generalize dependent tmn1.
  induction bs; simpl; intros.
    inv H.

    simpl in Huniq.
    apply NoDup_split' in Huniq.
    destruct Huniq as [J1 [J2 J3]].
    apply orb_true_iff in H.
    destruct H as [H | H].
      apply blockEqB_inv in H.
      subst. simpl.
      assert (~ In (getCmdLoc c1) (getPhiNodesIDs ps1)) as Hnotin.
        simpl in J1. 
        apply infrastructure_props.NoDup_disjoint with (i0:=getCmdLoc c1) 
          in J1; auto.
        apply in_or_app. left. apply In_InCmdLocs; auto.
      rewrite notin__lookupPhiNodeViaIDFromPhiNodes_none; auto.
      simpl in J1. apply NoDup_inv in J1. destruct J1 as [_ J1].
      apply NoDup_inv in J1. destruct J1 as [Huniq _].
      rewrite IngetCmdsLocs__lookupCmdViaIDFromCmds; auto.

      assert (~ In (getCmdLoc c1) (getBlockLocs a0)) as Hnotin.     
        intro J. apply J3 in J. apply J.
        eapply in_getBlockLocs__in_getBlocksLocs in H; eauto.
        simpl. apply in_or_app. right. 
        apply in_or_app. left. apply In_InCmdLocs; auto.
      rewrite notin__lookupInsnViaIDFromBlock_none; auto.
      eapply IHbs; eauto.
Qed.

Lemma find_promotable_alloca_spec: forall f cs nids pid ptyp pal,
  find_promotable_alloca f cs nids = Some (pid, ptyp, pal) ->
  exists pv, In (insn_alloca pid ptyp pv pal) cs /\
             is_promotable f pid.
Proof.
  induction cs; simpl; intros.
    congruence.

    destruct a; try solve [apply IHcs in H; destruct H as [pv [H1 H2]]; eauto].
    remember (is_promotable f i0 && negb (in_dec id_dec i0 nids)) as R.
    destruct R; try solve [apply IHcs in H; destruct H as [pv [H1 H2]]; eauto].
    inv H. 
    symmetry in HeqR. apply andb_true_iff in HeqR. destruct HeqR.
    eauto.
Qed.

Ltac simpl_WF_PhiInfo :=
match goal with
| H : WF_PhiInfo ?pinfo |- _ =>
  destruct pinfo; simpl in *;
  destruct H as [H _];
  unfold promotable_alloca in H;
  match goal with
  | H : match getEntryBlock ?PI_f0 with
        | Some _ => _
        | None => _
        end |- _ =>
    remember (getEntryBlock PI_f0) as R;
    destruct R as [[]|]; tinv H;
    apply find_promotable_alloca_spec in H
  end
end.

Lemma WF_PhiInfo_spec1: forall pinfo, 
  WF_PhiInfo pinfo -> 
  uniqFdef (PI_f pinfo) ->
  exists v, 
    lookupInsnViaIDFromFdef (PI_f pinfo) (PI_id pinfo) = 
      Some (insn_cmd 
             (insn_alloca (PI_id pinfo) (PI_typ pinfo) v (PI_align pinfo))).
Proof.
  intros. 
  simpl_WF_PhiInfo.
  destruct H as [v [H _]].
  exists v. 
  symmetry in HeqR.
  apply entryBlockInFdef in HeqR.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HeqR; eauto.
  simpl in HeqR. auto.
Qed.

Definition is_promotable_fun pid := 
  (fun acc b => 
     let '(block_intro _ ps cs tmn) := b in
     if (List.fold_left (fun re p => re || used_in_phi pid p) ps 
          (used_in_tmn pid tmn)) then false
     else
       fold_left 
         (fun acc0 c =>
          if used_in_cmd pid c then
            match c with
            | insn_load _ _ _ _ => acc0
            | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
            | _ => false
            end
          else acc0) cs acc
  ). 

Lemma fold_left_or_false : forall B (f:bool -> B -> bool)
  (J:forall a b, f a b = false -> a = false), 
  forall (l1:list B) init, 
    List.fold_left f l1 init = false ->
    List.fold_left f l1 false = false /\ init = false.
Proof.
  induction l1; simpl; intros; eauto.
    assert (H':=H).
    apply IHl1 in H.
    destruct H as [H1 H2].
    apply J in H2. subst.
    split; auto.
Qed.

Lemma used_in_phi_fun_spec: forall pid (a0 : bool) (b : phinode),
  a0 || used_in_phi pid b = false -> a0 = false.
Proof.
  intros. apply orb_false_iff in H. destruct H; auto.
Qed.

Lemma unused_in_phis__unused_in_phi: forall (pid id0 : id) (ps : phinodes)
  (p0 : phinode) (J1 : ret p0 = lookupPhiNodeViaIDFromPhiNodes ps id0)
  (J2 : fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p) 
          ps false = false),
  used_in_phi pid p0 = false.
Proof.
  induction ps; simpl; intros.
    congruence.

    assert (fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
              ps false = false /\ used_in_phi pid a = false) as J3.
      apply fold_left_or_false; auto.
        apply used_in_phi_fun_spec.

    destruct J3 as [J3 J4].
    destruct (getPhiNodeID a == id0); subst; eauto.
      inv J1. auto.
Qed.

Lemma unused_in_value__neg_valueEqB: forall pid v,
  used_in_value pid v = false ->
  negb (valueEqB v (value_id pid)).
Proof.
  intros.
  unfold valueEqB. 
  destruct v; inv H; simpl.
    destruct (value_dec (value_id i0) (value_id pid)); simpl.
      inversion e. subst.
      destruct (id_dec pid pid); subst; inv H1; try congruence.
         
      reflexivity.

    destruct (value_dec (value_const c) (value_id pid)); simpl.
      congruence.
      reflexivity.
Qed.

Lemma fold_left_and_true : forall B (f:bool -> B -> bool)
  (J:forall a b, f a b = true -> a = true), 
  forall (l1:list B) init, 
    List.fold_left f l1 init = true ->
    List.fold_left f l1 true = true /\ init = true.
Proof.
  induction l1; simpl; intros; eauto.
    assert (H':=H).
    apply IHl1 in H.
    destruct H as [H1 H2].
    apply J in H2. subst.
    split; auto.
Qed.

Lemma used_in_cmd_fun_spec:
  forall pid acc0 c,
  (if used_in_cmd pid c then
    match c with
    | insn_load _ _ _ _ => acc0
    | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
    | _ => false
    end
  else acc0) = true -> acc0 = true.
Proof.
  intros. clear - H.
  destruct acc0; auto.
  destruct (used_in_cmd pid c); auto.
  destruct c; auto.
  apply andb_true_iff in H. destruct H; auto.
Qed.

Lemma unused_in_cmds__unused_in_cmd: forall (pid id0 : id) (cs : cmds)
  (c0 : cmd) (J1 : ret c0 = lookupCmdViaIDFromCmds cs id0)
  (J2 : fold_left 
          (fun acc0 c =>
           if used_in_cmd pid c then
             match c with
             | insn_load _ _ _ _ => acc0
             | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
             | _ => false
             end
           else acc0) cs true = true),
  match c0 with
  | insn_load _ _ _ _ => True
  | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) 
  | _ => used_in_cmd pid c0 = false
  end.
Proof.
  induction cs; simpl; intros.
    congruence.

    assert (
      fold_left 
        (fun acc0 c =>
         if used_in_cmd pid c then
           match c with
           | insn_load _ _ _ _ => acc0
           | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
           | _ => false
           end
         else acc0) cs true = true /\
      (if used_in_cmd pid a then
         match a with
         | insn_load _ _ _ _ => true
         | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && true
         | _ => false
         end
       else true) = true) as J3.
      apply fold_left_and_true; auto.
        apply used_in_cmd_fun_spec.

    destruct J3 as [J3 J4]. clear J2.
    destruct (eq_atom_dec id0 (getCmdLoc a)); subst.
      inv J1. clear IHcs J3.
      remember (used_in_cmd pid a) as R.
      destruct R.    
        destruct a; auto.
          apply andb_true_iff in J4. 
          destruct J4; auto.
        destruct a; auto.
          simpl in *.
          symmetry in HeqR.
          apply orb_false_iff in HeqR. 
           destruct HeqR. 
           apply unused_in_value__neg_valueEqB; auto.

      clear J4.
      eapply IHcs in J3; eauto.
Qed.

Lemma is_promotable_fun_spec: forall pid (a0: bool) (b: block)
  (H1: is_promotable_fun pid a0 b = true), a0 = true.
Proof.
  intros. clear - H1.
  destruct a0; auto.
  unfold is_promotable_fun in H1.
  destruct b.
  destruct (fold_left
    (fun (re : bool) (p : phinode) => re || used_in_phi pid p) p
    (used_in_tmn pid t)); auto.
  apply fold_left_and_true in H1.
  destruct H1 as [_ H1]; auto.
  apply used_in_cmd_fun_spec.
Qed.

Lemma is_promotable_spec: forall pid id0 instr bs,
  fold_left (is_promotable_fun pid) bs true = true ->
  lookupInsnViaIDFromBlocks bs id0 = ret instr ->
  match instr with
  | insn_cmd c0 =>
    match c0 with
    | insn_load _ _ _ _ => True
    | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) 
    | _ => used_in_cmd pid c0 = false
    end
  | _ => used_in_insn pid instr = false
  end.
Proof.
  induction bs; simpl; intros.
    congruence.

    assert (fold_left (is_promotable_fun pid) bs true = true /\ 
            is_promotable_fun pid true a = true) as J.
      apply fold_left_and_true; auto.
        apply is_promotable_fun_spec.

    destruct J as [J1 J2].
    remember (lookupInsnViaIDFromBlock a id0) as R.
    destruct R.
      inv H0.
      clear - J2 HeqR.
      destruct a; simpl in *.
      remember (fold_left
                 (fun (re : bool) (p : phinode) => re || used_in_phi pid p) p
                 (used_in_tmn pid t)) as R.
      destruct R; tinv J2.
      assert (fold_left 
               (fun (re : bool) (p : phinode) => re || used_in_phi pid p) 
                 p false = false /\
              used_in_tmn pid t = false) as J.
        apply fold_left_or_false; auto.
          apply used_in_phi_fun_spec.        

      destruct J as [J3 J4]. clear HeqR0.
      remember (lookupPhiNodeViaIDFromPhiNodes p id0) as R1.
      remember (lookupCmdViaIDFromCmds c id0) as R2.
      destruct R1.
        inv HeqR.
        clear - J3 HeqR1. simpl.
        eapply unused_in_phis__unused_in_phi in J3; eauto.

        destruct R2; inv HeqR.
        clear - J2 HeqR2. simpl.
        eapply unused_in_cmds__unused_in_cmd in J2; eauto.

      apply IHbs in H0; auto.
Qed.

Lemma WF_PhiInfo_spec3: forall pinfo, 
  WF_PhiInfo pinfo -> 
  forall instr id0, 
    lookupInsnViaIDFromFdef (PI_f pinfo) id0 = Some instr ->
    match instr with
    | insn_cmd c0 =>
      match c0 with
      | insn_load _ _ _ _ => True
      | insn_store _ _ v _ _ => negb (valueEqB v (value_id (PI_id pinfo))) 
      | _ => used_in_cmd (PI_id pinfo) c0 = false
      end
    | _ => used_in_insn (PI_id pinfo) instr = false
    end.
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [v [_ H]].
  destruct PI_f0. simpl in *.
  eapply is_promotable_spec in H0; eauto.
Qed.

Definition valueInInsnOperands (v0:value) (instr:insn) : Prop :=
match instr with
| insn_phinode (insn_phi _ _ ls) => 
    In v0 (list_prj1 _ _ (unmake_list_value_l ls))
| insn_cmd c => valueInCmdOperands v0 c
| insn_terminator tmn => valueInTmnOperands v0 tmn
end.

Lemma used_in_phi__wf_use_at_head: forall pinfo v0 (p : phinode)
  (H0 : used_in_phi (PI_id pinfo) p = false)
  (H1 : valueInInsnOperands v0 (insn_phinode p)),
  wf_use_at_head pinfo v0.
Proof.
  intros.
  unfold wf_use_at_head.
  destruct p; simpl in *.
  induction l0; tinv H1.
    simpl in *.
    apply orb_false_iff in H0.
    destruct H0 as [J1 J2].
    destruct H1 as [H1 | H1]; subst; auto.
Qed.

Lemma neg_valueEqB__unused_in_value: forall pid v,
  negb (valueEqB v (value_id pid)) ->
  used_in_value pid v = false.
Proof.
  intros.
  unfold valueEqB in H.  
  destruct v; auto.
  destruct (value_dec (value_id i0) (value_id pid)); simpl in *.
    congruence.

    destruct (id_dec i0 pid); subst; auto.
      congruence.
Qed.

Lemma unused_in_list_value__unused_in_value: forall pid v0 l0,
  used_in_list_value pid l0 = false ->
  valueInListValue v0 l0 ->
  used_in_value pid v0 = false.
Proof.
  induction l0; simpl; intros.
    inv H0.
     
    apply orb_false_iff in H.
    destruct H as [J1 J2].
    inv H0; auto.
Qed.

Lemma unused_in_params__used_in_value: forall pid v0 ps
  (H1: fold_left
         (fun (acc : bool) (p : typ * attributes * value) =>
          let '(_, v) := p in used_in_value pid v || acc) ps false = false)
  (H2 : valueInParams v0 ps),
  used_in_value pid v0 = false.
Proof.
  induction ps as [|[]]; simpl; intros.
    inv H2.

    assert (forall (a : bool) (b : typ * attributes * value),
      (let '(_, v1) := b in used_in_value pid v1 || a) = false -> a = false).
      intros. destruct b.
      apply orb_false_iff in H.
      destruct H; auto.
    apply fold_left_or_false in H1; auto.
    destruct H1 as [J1 J2]. clear H.
    apply orb_false_iff in J2.
    destruct J2.
    unfold valueInParams in *.
    simpl in H2.
    remember (split ps) as R.
    destruct R.
    simpl in H2.
    destruct H2 as [H2 | H2]; subst; auto.
Qed.   

Lemma WF_PhiInfo_spec4: forall pinfo, 
  WF_PhiInfo pinfo -> 
  forall instr id0 v0, 
    lookupInsnViaIDFromFdef (PI_f pinfo) id0 = Some instr ->
    match instr with
    | insn_cmd c0 =>
      match c0 with
      | insn_load _ _ _ _ => False
      | insn_store _ _ v _ _ => v = v0 
      | _ => valueInCmdOperands v0 c0
      end
    | _ => valueInInsnOperands v0 instr
    end ->
    wf_use_at_head pinfo v0.
Proof.
  intros.
  apply WF_PhiInfo_spec3 in H0; auto.
  destruct instr.
    simpl in H0. 
    eapply used_in_phi__wf_use_at_head in H1; eauto.

    unfold wf_use_at_head.
    destruct c; tinv H1; simpl in *;
      try solve [
        subst; auto |
        match goal with
        | H0 : used_in_value _ ?v1 || used_in_value _ ?v2 = false,
          H1 : ?v0 = ?v1 \/ ?v0 = ?v2 |- _ =>
            apply orb_false_iff in H0;
            destruct H0 as [J1 J2];
            destruct H1; subst; auto
        end
      ].

      subst. 
      apply neg_valueEqB__unused_in_value; auto.

      apply orb_false_iff in H0.
      destruct H0 as [J1 J2].
      destruct H1 as [H1 | H1]; subst; auto.
      eapply unused_in_list_value__unused_in_value in J2; eauto.

      apply orb_false_iff in H0.
      destruct H0 as [J1 J2].
      apply orb_false_iff in J1.
      destruct J1 as [J1 J3].
      destruct H1 as [H1 | [H1 | H1]]; subst; auto.

      apply orb_false_iff in H0.
      destruct H0 as [J1 J2].
      destruct H1 as [H1 | H1]; subst;   
        eauto using unused_in_params__used_in_value.

    unfold wf_use_at_head.
    destruct t; simpl in *; subst; 
      try solve [auto | match goal with
                        | H1: False |- _ => inv H1
                        end].
Qed.

Lemma unused_in_phis__unused_in_phi': forall (pid: id) (ps: phinodes) 
  (p0 : phinode) (J1 : InPhiNodesB p0 ps)
  (J2 : fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p) 
          ps false = false),
  used_in_phi pid p0 = false.
Proof.
  induction ps; simpl; intros.
    congruence.

    assert (fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
              ps false = false /\ used_in_phi pid a = false) as J3.
      apply fold_left_or_false; auto.
        apply used_in_phi_fun_spec.        

    destruct J3 as [J3 J4].
    apply orb_true_iff in J1.
    destruct J1 as [J1 | J1]; auto.
      apply phinodeEqB_inv in J1. subst. auto.
Qed.

Lemma unused_in_cmds__unused_in_cmd': forall (pid id0 : id) (cs : cmds)
  (c0 : cmd) (J1 : InCmdsB c0 cs)
  (J2 : fold_left 
          (fun acc0 c =>
           if used_in_cmd pid c then
             match c with
             | insn_load _ _ _ _ => acc0
             | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
             | _ => false
             end
           else acc0) cs true = true),
  match c0 with
  | insn_load _ _ _ _ => True
  | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) 
  | _ => used_in_cmd pid c0 = false
  end.
Proof.
  induction cs; simpl; intros.
    congruence.

    assert (
      fold_left 
        (fun acc0 c =>
         if used_in_cmd pid c then
           match c with
           | insn_load _ _ _ _ => acc0
           | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
           | _ => false
           end
         else acc0) cs true = true /\
      (if used_in_cmd pid a then
         match a with
         | insn_load _ _ _ _ => true
         | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && true
         | _ => false
         end
       else true) = true) as J3.
      apply fold_left_and_true; auto.
        apply used_in_cmd_fun_spec.

    destruct J3 as [J3 J4]. clear J2.
    apply orb_true_iff in J1.
    destruct J1 as [J1 | J1].
      clear IHcs J3.
      apply cmdEqB_inv in J1. subst.
      remember (used_in_cmd pid a) as R.
      destruct R.    
        destruct a; auto.
          apply andb_true_iff in J4. 
          destruct J4; auto.

        destruct a; auto.
          simpl in *.
          symmetry in HeqR.
          apply orb_false_iff in HeqR. 
          destruct HeqR. 
          apply unused_in_value__neg_valueEqB; auto.

      clear J4.
      eapply IHcs in J3; eauto.
Qed.

Lemma is_promotable_spec': forall pid b instr bs,
  fold_left (is_promotable_fun pid) bs true = true ->
  insnInBlockB instr b ->
  InBlocksB b bs -> 
  match instr with
  | insn_cmd c0 =>
    match c0 with
    | insn_load _ _ _ _ => True
    | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) 
    | _ => used_in_cmd pid c0 = false
    end
  | _ => used_in_insn pid instr = false
  end.
Proof.
  induction bs; simpl; intros; try congruence.

    assert (fold_left (is_promotable_fun pid) bs true = true /\ 
            is_promotable_fun pid true a = true) as J.
      apply fold_left_and_true; auto.
        apply is_promotable_fun_spec.

    destruct J as [J1 J2]. clear H.
    apply orb_true_iff in H1.
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst.
      clear - J2 H0.
      destruct a; simpl in *.
      remember (fold_left
                 (fun (re : bool) (p : phinode) => re || used_in_phi pid p) p
                 (used_in_tmn pid t)) as R.
      destruct R; tinv J2.
      assert (fold_left 
               (fun (re : bool) (p : phinode) => re || used_in_phi pid p) 
                 p false = false /\
              used_in_tmn pid t = false) as J.
        apply fold_left_or_false; auto.
          apply used_in_phi_fun_spec.  

      destruct J as [J3 J4]. clear HeqR.
      destruct instr; simpl in *.
        eapply unused_in_phis__unused_in_phi' in J3; eauto.
        eapply unused_in_cmds__unused_in_cmd' in J2; eauto.
        apply terminatorEqB_inv in H0. subst. auto.

      apply IHbs in J1; auto.
Qed.

Lemma WF_PhiInfo_spec5: forall pinfo pn b, 
  WF_PhiInfo pinfo -> 
  phinodeInFdefBlockB pn (PI_f pinfo) b = true -> 
  used_in_phi (PI_id pinfo) pn = false.
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [v [_ H]].
  destruct PI_f0. simpl in *.
  unfold phinodeInFdefBlockB in H0.
  apply andb_true_iff in H0.
  destruct H0.
  eapply is_promotable_spec' with (instr:=insn_phinode pn) in H1; eauto.
Qed.

Lemma IngetPhiNodesIDs__lookupPhiNodeViaIDFromPhiNodes: forall id2 ps1
  (H0 : In id2 (getPhiNodesIDs ps1)),
  exists p2, lookupPhiNodeViaIDFromPhiNodes ps1 id2 = Some p2 /\
             getPhiNodeID p2 = id2.
Proof.
  induction ps1; simpl; intros.
    inv H0.

    destruct H0 as [H0 | H0]; subst.
      destruct (getPhiNodeID a == getPhiNodeID a); eauto.
        congruence.

      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getPhiNodeID a) 
                 id2); subst; eauto.
Qed.

Lemma lookupInsnViaIDFromBlocks__In : forall id0 instr bs,
  lookupInsnViaIDFromBlocks bs id0 = Some instr ->
  In id0 (getBlocksLocs bs).
Proof.
  induction bs; simpl; intros.
    inv H.

    apply in_or_app.
    remember (lookupInsnViaIDFromBlock a id0) as R.
    destruct R; eauto.
      inv H.
      symmetry in HeqR.
      apply lookupInsnViaIDFromBlock__In in HeqR; auto.
Qed.

Lemma IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef: forall id2 l1 ps1 cs1 tmn1 f
  (Huniq: uniqFdef f)
  (H : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (H0 : In id2 (getPhiNodesIDs ps1)),
  exists p2, lookupInsnViaIDFromFdef f id2 = Some (insn_phinode p2) /\
             getPhiNodeID p2 = id2.
Proof.
  destruct f as [[] bs]. simpl. intros.
  destruct Huniq as [_ Huniq].
  apply NoDup_split in Huniq.
  destruct Huniq as [_ Huniq].
  generalize dependent l1.
  generalize dependent ps1.
  generalize dependent cs1.
  generalize dependent tmn1.
  generalize dependent id2.
  induction bs; simpl; intros.
    congruence.

    apply orb_true_iff in H.
    destruct H as [H | H].
      apply blockEqB_inv in H.
      subst. simpl.
      apply IngetPhiNodesIDs__lookupPhiNodeViaIDFromPhiNodes in H0.
      destruct H0 as [ps [H0 Heq]]; subst.
      rewrite H0. eauto.

      simpl_env in Huniq. rewrite getBlocksLocs_app in Huniq.
      assert (Huniq':=Huniq).
      apply NoDup_inv in Huniq'. destruct Huniq'.
      eapply IHbs in H; eauto.
      destruct H as [p2 [H Heq]]; subst.
      rewrite H. 
      apply lookupInsnViaIDFromBlocks__In in H.
      eapply infrastructure_props.NoDup_disjoint in Huniq; eauto.
      simpl in Huniq. simpl_env in Huniq.
      apply notin__lookupInsnViaIDFromBlock_none in Huniq.
      rewrite Huniq. eauto.
Qed.

Lemma WF_PhiInfo_spec6: forall pinfo l' ps' cs' tmn', 
  WF_PhiInfo pinfo -> 
  uniqFdef (PI_f pinfo) ->
  ret block_intro l' ps' cs' tmn' = lookupBlockViaLabelFromFdef (PI_f pinfo) l' ->
  ~ In (PI_id pinfo) (getPhiNodesIDs ps').
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [pv [H _]].
  symmetry in HeqR.
  apply entryBlockInFdef in HeqR.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H; eauto.
  simpl in H.

  symmetry in H1.
  apply lookupBlockViaLabelFromFdef_inv in H1; auto.
  destruct H1 as [_ H1].
  intro J. 
  eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef in J; eauto.  
  destruct J as [p2 [J1 J2]].
  rewrite H in J1. congruence.
Qed.

Lemma PhiInfo_must_be_promotable_alloca: forall pinfo l0 ps0 cs1 c cs2 tmn0,
  WF_PhiInfo pinfo ->
  uniqFdef (PI_f pinfo) ->
  getCmdLoc c = PI_id pinfo ->
  (forall id1 typ1 v1 al1, c <> insn_alloca id1 typ1 v1 al1) ->
  blockInFdefB (block_intro l0 ps0 (cs1++c::cs2) tmn0) (PI_f pinfo) = true ->
  False. 
Proof.
  intros.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H3; eauto using in_middle.
  apply WF_PhiInfo_spec1 in H; auto.
  destruct H as [v' H].
  simpl in H3. rewrite H1 in H3. rewrite H3 in H. inv H.
  assert (W:=@H2 (PI_id pinfo) (PI_typ pinfo) v' (PI_align pinfo)).
  auto.
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
    destruct cs'.
    SSSSCase "cs' = nil".
      assert (~ In (getCmdLoc (insn_call i0 n c t v p)) (getCmdsLocs cs2')) 
        as Hnotin.
        eapply preservation_helper1; eauto.

      unfold Opsem.returnUpdateLocals in H1. simpl in H1.
      remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
      destruct R1; try solve [inv H1].
      destruct R.
      SSSSSCase "c' defines a variable".
        destruct n; inv HeqR.
        destruct t; tinv H1.

        remember (MDGVs.lift_op1 (fit_gv (los, nts) t) g t) as R2.
        destruct R2; inv H1.
        apply wf_defs_updateAddAL; auto.
          split.
            eapply preservation_return_helper; eauto; simpl; auto.

            intro; subst.
            clear - HwfPI HBinF2 HuniqF.
            apply PhiInfo_must_be_promotable_alloca in HBinF2; 
              try solve [auto | inv HBinF2 | intros; congruence].
 
      SSSSSCase "c' defines nothing".
        destruct n; inv HeqR. inv H1. auto.
        
    SSSSCase "cs' <> nil".
      assert (NoDup (getCmdsLocs (cs2' ++ [insn_call i0 n c t v p] ++ [c0] ++ 
        cs'))) as Hnodup.
        eapply preservation_helper2; eauto.

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

        apply wf_defs_updateAddAL; auto.
          split.
            eapply preservation_return_helper; eauto; simpl; auto.

            intro; subst.
            clear - HwfPI HBinF2 HuniqF.
            apply PhiInfo_must_be_promotable_alloca in HBinF2; 
              try solve [auto | inv HBinF2 | intros; congruence].

      SSSSSCase "c' defines nothing".
        destruct n; inv HeqR. inv H1. auto.

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
    wf_defs maxb pinfo TD M lc als ->
    wf_GVs maxb pinfo TD M lc als id1 gv1
else True) /\
(forall ec0 (Hin : In ec0 tail) (gvsa : GVsT DGVs) 
    (Heq : Opsem.CurFunction ec0 = PI_f pinfo) 
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
      eapply wf_defs_updateAddAL; eauto.

      SSSCase "wflc".
      apply updateAddAL__wf_lc; auto.

    split; auto.
    SSCase "wf_ECs_head_tail".
      eapply updateAddAL__wf_ECStack_head_tail; eauto.
Qed.

Lemma BOP__wf_GVs_in_ECs : forall (v : value) (v0 : value) (id1 : id) (bop0 : bop)
  gvs3 TD bop0 sz0 lc gl hd tl Mem0 td pinfo maxb 
  (Hneq: PI_f pinfo = Opsem.CurFunction hd -> id1 <> PI_id pinfo)
  (H11 : BOP TD lc gl bop0 sz0 v v0 = ret gvs3),
  wf_GVs_in_ECs maxb pinfo td Mem0 hd tl id1 gvs3.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct hd; simpl in *.
  split.   
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
    apply Hneq in EQ. clear Hneq.
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
  (Heq: Opsem.CurFunction ec0 = PI_f pinfo)
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
  (Hwfv: Opsem.CurFunction EC = (PI_f pinfo) ->
         wf_use_at_head pinfo v)
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
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
    assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
    apply Hneq in EQ. clear Hneq.
    split; intros; subst; try congruence.
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
Proof.
  intros. destruct EC. simpl. destruct H; auto.
Qed.  

Lemma mload__wf_GVs_in_ECs : forall (v : value) (v0 : value) (id1 : id) 
  gvs3 t align0 EC Mem td pinfo maxb mp
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo) 
  (HwfM: wf_Mem maxb td Mem)
  (H1 : mload td Mem mp t align0 = ret gvs3) tl
  (Hwfstk: wf_ECStack_head_tail maxb pinfo td Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo td Mem EC tl id1 gvs3.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct EC.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
    apply Hneq in EQ. clear Hneq.
    split; intros; subst; try congruence.
      apply H in H0; auto.
      destruct H0 as [[J1 [J2 J3]] _]; eauto.
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
  (Hwfv: PI_f pinfo = Opsem.CurFunction EC -> 
         wf_use_at_head pinfo v)
  (H : Opsem.getOperandValue TD v (Opsem.Locals EC) gl = ret mps)
  (H0 : mp @ mps)(Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (H1 : Opsem.GEP TD t mp vidxs inbounds0 = ret mp') tl
  (Hwfstk: wf_ECStack_head_tail maxb pinfo TD Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo TD Mem EC tl id1 mp'.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct EC.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
    apply Hneq in EQ. clear Hneq.
    split; intros; subst; try congruence.
     assert (H3':=H3).
     apply H2 in H3; auto.
      destruct H3 as [[J1 [J2 J3]] J4]; eauto.
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

Lemma fold_left_or_spec : forall B (f:bool -> B -> bool)
  (J:forall a b, a = true -> f a b = true), 
  forall (l1:list B), List.fold_left f l1 true = true.
Proof.
  induction l1; simpl; intros; eauto.
    rewrite J; auto.
Qed.

Lemma in_params__used: forall id1 A (t1 : A) (lp : list (A * value)) init,
  fold_left
    (fun (acc : bool) (p : A * value) =>
     let '(_, v) := p in used_in_value id1 v || acc) lp init = false ->
  ~ In (t1, value_id id1) lp.
Proof.
  induction lp as [|[]]; simpl; intros; auto.
    intro J.
    destruct J as [J | J].
      inv J.
      simpl in H.
      destruct (id_dec id1 id1); try congruence.
      simpl in H.
      rewrite fold_left_or_spec in H; try congruence.
        intros. subst. destruct b. apply orb_true_iff; auto.

      apply IHlp in H. congruence.
Qed.

Lemma initLocals_preserves_wf_ECStack_head_tail: forall Mem (lc:DGVMap) maxb TD 
  ECs lc' gl (Hwflc1 : wf_lc Mem lc) pinfo gvs la lp EC
  (Hnouse: 
    PI_f pinfo = Opsem.CurFunction EC ->
    List.fold_left 
      (fun acc p => let '(_, v):=p in used_in_value (PI_id pinfo) v || acc) 
      lp false = false)
  (Hwfg : wf_globals maxb gl)
  (H3 : Opsem.params2GVs TD lp lc gl = ret gvs)
  (H4 : Opsem.initLocals TD la gvs = ret lc')
  (Heq2 : lc = Opsem.Locals EC)
  (Hfr2 : wf_ECStack_head_tail maxb pinfo TD Mem lc ECs)
  (Hscp: if fdef_dec (PI_f pinfo) (Opsem.CurFunction EC) then
           wf_defs maxb pinfo TD Mem (Opsem.Locals EC) (Opsem.Allocas EC)
         else True),
  wf_ECStack_head_tail maxb pinfo TD Mem lc' (EC :: ECs).
Proof.
  intros. unfold wf_ECStack_head_tail. intros ec0 Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; subst.
    unfold wf_ECStack_head_in_tail. destruct ec0. simpl in *.
    intros.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; try congruence.    
    apply_clear Hscp in H0.
    destruct H0 as [[[mb [J11 [J14 J15]]] [J12 J13]] J2]; subst.
    split; eauto.
    split; intros; eauto.
      eapply initializeFrameValues_preserves_no_alias in H4; eauto.
      eapply params2GVs_preserves_no_alias; eauto. 
        omega.

        intros.
        apply J2 in H2. unfold wf_non_alloca_GVs in H2.
        destruct (id_dec id0 (PI_id pinfo)); subst; auto.
          contradict H1. eapply in_params__used; eauto.

    destruct ec0. simpl.
    intros gvsa Heq Hlkup.
    apply_clear Hfr2 in Hin. simpl in Hin. eapply_clear Hin in Hlkup. 
    destruct Hlkup as [[mb [J11 J12]] [J2 J3]]; subst.
    split; eauto.
    split; auto.
      intros.
      eapply initializeFrameValues_preserves_no_alias in H4; eauto.
      eapply params2GVs_preserves_no_alias; eauto. omega.
Qed.

Lemma IngetArgsIDs__lookupCmdViaIDFromFdef: forall fa rt fid la va lb id0
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (H0 : In id0 (getArgsIDs la)),
  lookupInsnViaIDFromFdef (fdef_intro (fheader_intro fa rt fid la va) lb) id0 
    = None.
Proof.
  simpl. intros.
  destruct Huniq as [_ Huniq].
  remember (lookupInsnViaIDFromBlocks lb id0) as R.
  destruct R; auto.
  eapply NoDup_disjoint' in Huniq; eauto.
  contradict Huniq.
  eapply lookupInsnViaIDFromBlocks__In; eauto.
Qed.

Lemma In_initializeFrameValues__In_getArgsIDs: forall (GVsSig : GenericValues) 
  (TD : TargetData) (la : args) (gvs : list (GVsT GVsSig)) (id1 : atom) 
  (lc : Opsem.GVsMap) (gv : GVsT GVsSig) acc,
  Opsem._initializeFrameValues TD la gvs acc = ret lc ->
  lookupAL (GVsT GVsSig) lc id1 = ret gv -> 
  In id1 (getArgsIDs la) \/ id1 `in` dom acc.
Proof.
  induction la as [|[]]; simpl; intros.
    inv H.
    right. apply lookupAL_Some_indom in H0; auto.

    destruct p.
    destruct gvs.
      inv_mbind'.
      destruct (id_dec i0 id1); subst; auto.
      rewrite <- lookupAL_updateAddAL_neq in H0; auto.
      eapply IHla in H0; eauto.
      destruct H0 as [H0 | H0]; auto.

      inv_mbind'.
      destruct (id_dec i0 id1); subst; auto.
      rewrite <- lookupAL_updateAddAL_neq in H0; auto.
      eapply IHla in H0; eauto.
      destruct H0 as [H0 | H0]; auto.
Qed.

Lemma In_initLocals__In_getArgsIDs : forall GVsSig TD la gvs id1 lc gv,
  @Opsem.initLocals GVsSig TD la gvs = Some lc ->
  lookupAL _ lc id1 = Some gv ->
  In id1 (getArgsIDs la).
Proof.
  unfold Opsem.initLocals.
  intros.
  eapply In_initializeFrameValues__In_getArgsIDs in H; eauto.
  destruct H as [H | H]; auto.
    fsetdec.
Qed.

Lemma initLocals_preserves_wf_defs : forall fid fa rt la va lb gvs 
  lc Mem TD pinfo maxb (Hwfpi: WF_PhiInfo pinfo)
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hinit : Opsem.initLocals TD la gvs = Some lc) 
  (Heq: fdef_intro (fheader_intro fa rt fid la va) lb = PI_f pinfo),
  wf_defs maxb pinfo TD Mem lc nil.
Proof.
  intros. intros gvsa Hlkup.
  eapply In_initLocals__In_getArgsIDs in Hinit; eauto.
  eapply IngetArgsIDs__lookupCmdViaIDFromFdef in Hinit; eauto.
  rewrite Heq in *.
  apply WF_PhiInfo_spec1 in Huniq; auto.
  destruct Huniq as [v Huniq].
  rewrite Huniq in Hinit. congruence.
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

Lemma mstore_preserves_wf_defs_at_head : forall maxb pinfo TD M  
  M' gl v als lc gvs1 gv1 t mp2 align mps2 vp
  (Hgetop': Opsem.getOperandValue TD vp lc gl = ret mps2)
  (Hgetop: Opsem.getOperandValue TD v lc gl = ret gvs1)
  (Hinp: mp2 @ mps2) (Hin: gv1 @ gvs1) (Hwfgl: wf_globals maxb gl)
  (Hst: mstore TD M mp2 t gv1 align = Some M')
  (Hwfu: wf_use_at_head pinfo v) 
  (Hwf: wf_defs maxb pinfo TD M lc als),
  wf_defs maxb pinfo TD M' lc als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hlkp.
  assert (no_alias gv1 gvsa) as J.
    eapply operand__no_alias_with__head with (mptrs:=gvs1); eauto.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    destruct J1 as [[mb [J11 [J12 J13]]] [J4 [gv J3]]]; subst.
    split. 
      erewrite <- nextblock_mstore; eauto.
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
  (Hwf: wf_defs maxb pinfo TD M lc2 als),
  wf_defs maxb pinfo TD M' lc2 als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hlkp.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    clear J2.
    destruct J1 as [[mb [J11 [J12 J13]]] [J4 [gv J3]]]; subst.
    split.
      erewrite <- nextblock_mstore; eauto.
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
    erewrite <- nextblock_mstore; eauto.
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
    erewrite nextblock_mstore; eauto.
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
  split.
    erewrite <- nextblock_mstore; eauto.
  split; auto.
    intros.
    eapply mstore_preserves_mload_inv in Hst; eauto.
    destruct Hst as [gvs2 [H3 H2]].
    apply J3 in H3.
    eapply no_alias_overlap with (gvs1:=gv1); eauto.
Qed.

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
  assert (maxb < mb' < Mem.nextblock M') as W.
    erewrite <- nextblock_malloc; eauto. omega.
  split; eauto.
  split.
    intros.
    destruct (id_dec id0 id1); subst.
      rewrite lookupAL_updateAddAL_eq in H. inv H.
      rewrite simpl_blk2GV. rewrite simpl_blk2GV.
      simpl. apply malloc_result in Hmlc. subst.
      split; auto.
      split; auto.
      clear - J12.
      intro J. subst. omega.

      rewrite <- lookupAL_updateAddAL_neq in H; eauto.

    intros.
    eapply malloc_preserves_mload_inv in Hmlc; eauto.
    destruct Hmlc as [G | G]; subst; eauto.
      eapply undefs_disjoint_with_ptr; eauto.
Qed.

Lemma malloc_preserves_wf_defs_in_tail : forall maxb pinfo TD M  
  M' als lc mb align0 gn tsz (Hal: malloc TD M tsz gn align0 = ret (M', mb))
  (Hwf: wf_defs maxb pinfo TD M lc als),
  wf_defs maxb pinfo TD M lc als ->
  wf_defs maxb pinfo TD M' lc als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hlkp.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    clear J2.
    destruct J1 as [[mb' [J11 [J12 J13]]] [J4 [gv J3]]]; subst.
    assert (maxb < mb' < Mem.nextblock M') as W.
      erewrite <- nextblock_malloc; eauto. omega.
    split; eauto.
    split.
      intros.
      eapply malloc_preserves_mload_inv in H0; eauto.
      destruct H0 as [G | G]; subst; eauto.
        eapply undefs_disjoint_with_ptr; eauto.

      exists gv. eapply malloc_preserves_mload; eauto.
Qed.

Lemma malloc_preserves_wf_lc_in_tail: forall TD M M' tsz gn align0 mb lc
  (Hmalloc: malloc TD M tsz gn align0 = ret (M', mb)) 
  (Hwf: wf_lc M lc), wf_lc M' lc.
Proof.
  unfold wf_lc.
  intros. apply Hwf in H.
  eapply valid_ptrs__trans; eauto.
  erewrite <- nextblock_malloc with (M':=M'); eauto. 
  omega.
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
  assert (maxb < mb' < Mem.nextblock M') as W.
    erewrite <- nextblock_malloc; eauto. omega.
  split; eauto.
  split; eauto.
    intros.
    eapply malloc_preserves_mload_inv in Hmlc; eauto.
    destruct Hmlc as [G | G]; subst; eauto.
      eapply undefs_disjoint_with_ptr; eauto.
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

Lemma impure_cmd_updated_preserves_wf_EC : forall maxb pinfo TD M M' lc F B 
  als als' tmn cs c0 l1 ps1 cs1' ifs S
  (Heq: B = block_intro l1 ps1 (cs1' ++ c0 :: cs) tmn)
  (HwfS: wf_system ifs S) los nts (Heq': TD = (los, nts)) Ps
  (HMinS: moduleInSystemB (module_intro los nts Ps) S = true)
  (HFinPs: InProductsB (product_fdef F) Ps = true)
  (HBinF: blockInFdefB B F = true) id0
  (Hid : getCmdID c0 = Some id0) gv3
  (Hwfdefs:   F = (PI_f pinfo) ->
              wf_defs maxb pinfo TD M lc als ->
              wf_defs maxb pinfo TD M' 
                (updateAddAL (GVsT DGVs) lc id0 gv3) als')
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
Qed.

Lemma valid_ptrs__no_alias__fresh_ptr: forall bound TD mb t (Hbd: bound <= mb) 
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

Lemma mload_aux_alloc_same': forall M M' lo hi b 
  (Hal : Mem.alloc M lo hi = (M', b)) mc ofs,
  exists gvs1, mload_aux M' mc b ofs = ret gvs1 /\ 
    forall v m, In (v, m) gvs1 -> v = Vundef.
Proof.
  induction mc; simpl; intros.
    exists nil. 
    split; auto.
      intros. inv H.
Admitted.

(* The current design of malloc is incorrect! It must ensure that mload is
   successful at the allocated address. To do so, malloc must ensure all 
   subcomponents in an aggregated object are well-aligned! *)
Lemma mload_aux_malloc_same': forall TD M M' mb align0 gn tsz mc
  (Hal : malloc TD M tsz gn align0 = ret (M', mb)),
  exists gvs1, mload_aux M' mc mb (Int.signed 31 (Int.repr 31 0)) = ret gvs1.
Proof.
  intros. 
  apply malloc_inv in Hal.
  destruct Hal as [n [J1 [J2 J3]]].
Admitted.

(* We need to restrict the wf_alloca rule *)
Lemma WF_PhiInfo_spec2: forall pinfo ifs S los nts Ps,
  WF_PhiInfo pinfo ->
  wf_fdef ifs S (module_intro los nts Ps) (PI_f pinfo) ->
  exists mc, flatten_typ (los, nts) (PI_typ pinfo) = Some mc.
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [pv [J1 J2]].
  symmetry in HeqR.
  apply entryBlockInFdef in HeqR.
  eapply wf_fdef__wf_cmd in HeqR; eauto.
  inv HeqR.
  apply flatten_typ_total; auto.
Admitted.

Lemma alloca_preserves_wf_defs_at_head : forall maxb pinfo los nts M  
  M' gl als lc t 
  (Hwfpi : WF_PhiInfo pinfo) ifs S Ps
  (HwfF: wf_fdef ifs S (module_intro los nts Ps) (PI_f pinfo))
  (Hwfgl: wf_globals maxb gl) mb id0 align0 F gn tsz
  (Hal: malloc (los, nts) M tsz gn align0 = ret (M', mb)) 
  (HwfM: wf_Mem maxb (los, nts) M)
  (Hwflc : wf_lc M lc) (Hsize: getTypeAllocSize (los, nts) t = ret tsz),
   F = PI_f pinfo ->
   wf_defs maxb pinfo (los, nts) M lc als ->
   wf_defs maxb pinfo (los, nts) M'
     (updateAddAL (GVsT DGVs) lc id0
        ($ blk2GV (los, nts) mb # typ_pointer t $)) (mb :: als).
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hlkp.
  destruct (id_dec id0 (PI_id pinfo)); subst.
    rewrite lookupAL_updateAddAL_eq in Hlkp.
    inv Hlkp.
    split.
      split.
        exists mb. 
        rewrite simpl_blk2GV. rewrite simpl_blk2GV. 
        split; auto. simpl.
        split; auto. 
          erewrite <- nextblock_malloc; eauto.
          apply malloc_result in Hal. subst. 
          destruct HwfM. omega.
      split.
        intros.
        assert (mload (los, nts) M gptr ty al = ret gvs1 \/
                forall v m, In (v, m) gvs1 -> v = Vundef) as J.
          eapply malloc_preserves_mload_inv; eauto.
        destruct J as [J | J].
          destruct HwfM as [HwfM _].
          apply HwfM in J.
          eapply valid_ptrs__no_alias__fresh_ptr; eauto.
          apply malloc_result in Hal. subst. omega.

          eapply undefs_disjoint_with_ptr; eauto.

        rewrite simpl_blk2GV. 
        unfold mload. simpl.
        assert (exists mc, flatten_typ (los, nts) (PI_typ pinfo) = Some mc) 
          as J.
          eapply WF_PhiInfo_spec2; eauto.
        destruct J as [mc J].
        rewrite J.
        eapply mload_aux_malloc_same'; eauto.

      intros.
      unfold wf_non_alloca_GVs.
      destruct (id_dec id0 (PI_id pinfo)); auto.
      rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
      apply Hwflc in Hlk0.
      eapply valid_ptrs__no_alias__fresh_ptr; eauto.
      apply malloc_result in Hal. subst. omega.

    rewrite <- lookupAL_updateAddAL_neq in Hlkp; auto.
    assert (Hlkp':=Hlkp).
    apply H0 in Hlkp; auto.
    destruct Hlkp as [J1 J2].
    split.
      destruct J1 as [[mb' [J31 [J32 J33]]] [J4 [gv J5]]]; subst.
      split.
        exists mb'. 
        split; auto. simpl.
        split; auto. 
          erewrite <- nextblock_malloc; eauto.
          omega.
      split.
        intros.
        assert (mload (los, nts) M gptr ty al = ret gvs1 \/
                forall v m, In (v, m) gvs1 -> v = Vundef) as J.
          eapply malloc_preserves_mload_inv; eauto.
        destruct J as [J | J]; eauto.
          eapply undefs_disjoint_with_ptr; eauto.

        eapply malloc_preserves_mload in Hal; eauto.
       
      intros.
      unfold wf_non_alloca_GVs.
      destruct (id_dec id1 (PI_id pinfo)); auto.
      destruct (id_dec id0 id1); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk0.
        inv Hlk0.
        apply Hwflc in Hlkp'.
        apply no_alias_sym.
        eapply valid_ptrs__no_alias__fresh_ptr; eauto.
        apply malloc_result in Hal. subst. omega.

        rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
        apply J2 in Hlk0.
        unfold wf_non_alloca_GVs in Hlk0.
        destruct (id_dec id1 (PI_id pinfo)); subst; try congruence.
Qed.

Lemma malloc_preserves_wf_defs_at_head : forall maxb pinfo TD M  
  M' gl als lc t 
  (Hwfgl: wf_globals maxb gl) mb id0 align0 F gn tsz
  (Hal: malloc TD M tsz gn align0 = ret (M', mb)) (HwfM: wf_Mem maxb TD M)
  (Hwflc : wf_lc M lc) (Hneq: F = PI_f pinfo -> id0 <> PI_id pinfo),
   F = PI_f pinfo ->
   wf_defs maxb pinfo TD M lc als ->
   wf_defs maxb pinfo TD M'
     (updateAddAL (GVsT DGVs) lc id0
        ($ blk2GV TD mb # typ_pointer t $)) als.
Proof.
  intros. unfold wf_defs.  
  assert (JJ:=H). apply Hneq in JJ. subst.
  intros gvsa Hlkp.
  rewrite <- lookupAL_updateAddAL_neq in Hlkp; auto.
  assert (Hlkp':=Hlkp).
  apply H0 in Hlkp; auto.
  destruct Hlkp as [J1 J2].
  split.
      destruct J1 as [[mb' [J31 [J32 J33]]] [J4 [gv J5]]]; subst.
      split.
        erewrite <- nextblock_malloc; eauto.
        exists mb'. split; auto. split; auto. omega. 

      split.
        intros.
        assert (mload TD M gptr ty al = ret gvs1 \/
                forall v m, In (v, m) gvs1 -> v = Vundef) as J.
          eapply malloc_preserves_mload_inv; eauto.
        destruct J as [J | J]; eauto.
          eapply undefs_disjoint_with_ptr; eauto.

        eapply malloc_preserves_mload in Hal; eauto.

      intros.
      unfold wf_non_alloca_GVs.
      destruct (id_dec id1 (PI_id pinfo)); auto.
      destruct (id_dec id0 id1); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk0.
        inv Hlk0.
        apply Hwflc in Hlkp'.
        apply no_alias_sym.
        eapply valid_ptrs__no_alias__fresh_ptr; eauto.
        apply malloc_result in Hal. subst. omega.

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
    inv H. rewrite simpl_blk2GV. simpl.
    erewrite <- nextblock_malloc; eauto.
    apply malloc_result in Hmalloc. subst.
    split; auto.
      omega.

    rewrite <- lookupAL_updateAddAL_neq in H; auto.
    apply Hwf in H.
    erewrite <- nextblock_malloc; eauto.
    eapply valid_ptrs__trans; eauto.
    omega.
Qed.

Ltac simpl_ctx Hinv HwfS1 :=
  destruct Hinv as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [HwfEC0 HwfCall]
    ]]]]]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0;
  destruct HwfS1 as [[HwfEC [HwfECs Hwfht]] [Hnonup1 HwfM1]].

Ltac preservation_tac4 :=
  match goal with
  | HwfPI : WF_PhiInfo _,
    HFinPs1: InProductsB _ _ = _,
    HBinF1: blockInFdefB _ _ = _,
    HmInS: moduleInSystemB _ _ = _,
    HwfSystem: wf_system _ _ |- _ =>
    simpl; intros; subst;
    clear - HBinF1 HFinPs1 HmInS HwfPI HwfSystem;
    eapply wf_system__uniqFdef in HFinPs1; eauto;
    eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HBinF1; 
      eauto using in_middle;
    eapply WF_PhiInfo_spec3 in HBinF1; eauto; simpl; auto;
    simpl in HBinF1;
    apply orb_false_iff in HBinF1; destruct HBinF1; auto
  end.

Lemma preservation_Call: forall (maxb : Z) (pinfo : PhiInfo)
  (F : fdef) (B : block) (lc : Opsem.GVsMap) (rid : id) (noret0 : noret)
  (ca : clattrs) (fv : value) (lp : params) (cs : list cmd) (tmn : terminator)
  (EC : list Opsem.ExecutionContext) (Mem : mem) (als : list mblock) (ft : typ)
  ECs cfg S los nts Ps gl fs
  (EQ1 : cfg = OpsemAux.mkCfg S (los, nts) Ps gl fs)
  (EQ2 : ECs = {| Opsem.CurFunction := F;
                 Opsem.CurBB := B;
                 Opsem.CurCmds := insn_call rid noret0 ca ft fv lp :: cs;
                 Opsem.Terminator := tmn;
                 Opsem.Locals := lc;
                 Opsem.Allocas := als |} :: EC)
  (Hinv : OpsemPP.wf_State cfg        
           {| Opsem.ECS := ECs;
              Opsem.Mem := Mem |})
  (Hwfg : wf_globals maxb gl)
  (Hinbd : 0 <= maxb) (HwfPI : WF_PhiInfo pinfo) (fid : id) (fptrs : GVsT DGVs)
  (fptr : GenericValue) (lc' : Opsem.GVsMap) (l' : l) (ps' : phinodes)
  (cs' : cmds) (tmn' : terminator) (rt : typ) (la : args) (va : varg)
  (lb : blocks) (fa : fnattrs) (gvs : list (GVsT DGVs))
  (H : Opsem.getOperandValue (los, nts) fv lc gl = ret fptrs)
  (H0 : fptr @ fptrs)
  (H1 : OpsemAux.lookupFdefViaPtr Ps fs fptr =
        ret fdef_intro (fheader_intro fa rt fid la va) lb)
  (H2 : getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) =
        ret block_intro l' ps' cs' tmn')
  (H3 : Opsem.params2GVs (los, nts) lp lc gl = ret gvs)
  (H4 : Opsem.initLocals (los, nts) la gvs = ret lc')
  (HwfS1 : wf_State maxb pinfo cfg
            {| Opsem.ECS := ECs;
               Opsem.Mem := Mem |}),
  wf_State maxb pinfo cfg
     {|
     Opsem.ECS := {|
                  Opsem.CurFunction := fdef_intro
                                         (fheader_intro fa rt fid la va) lb;
                  Opsem.CurBB := block_intro l' ps' cs' tmn';
                  Opsem.CurCmds := cs';
                  Opsem.Terminator := tmn';
                  Opsem.Locals := lc';
                  Opsem.Allocas := nil |}
                  :: ECs;
     Opsem.Mem := Mem |}.
Proof.
  intros. subst.
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
      eapply initLocals_preserves_wf_defs; eauto.

      destruct HwfM.
      eapply initLocals_preserves_wf_lc; eauto.

  split.
    repeat (split; auto). 
    assert(PI_f pinfo = F -> 
           fold_left
             (fun (acc : bool) (p : typ * attributes * value) =>
              let '(_, v) := p in used_in_value (PI_id pinfo) v || acc) lp false
              = false) as J.
      preservation_tac4.
    eapply initLocals_preserves_wf_ECStack_head_tail; eauto.
Qed.

Lemma preservation_return_void : forall maxb pinfo (HwfPI : WF_PhiInfo pinfo)  
  F B rid lc F' B' c' cs' tmn' lc' EC Mem als als' cfg
  EC1 EC2 (Hwfg: wf_globals maxb (OpsemAux.Globals cfg))
  (EQ1:EC1 = {| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := nil;
                Opsem.Terminator := insn_return_void rid;
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
  Mem' (H : Instruction.isCallInst c' = true)
  (H0 : free_allocas (OpsemAux.CurTargetData cfg) Mem als = ret Mem')
  (H1 : getCallerReturnID c' = merror)
  (HwfS1 : wf_State maxb pinfo cfg
            {| Opsem.ECS := EC1 :: EC2 :: EC;
               Opsem.Mem := Mem |}),
  wf_State maxb pinfo cfg
     {| Opsem.ECS :=
             {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc';
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
      eapply free_allocas_preserves_wf_defs in Hinscope2; eauto.

    SSSCase "wflc".
      clear - Hwflc1 Hwflc2 H1 Hwfg HwfM H0.
      eapply free_allocas_preserves_wf_lc in H0; eauto.

    split.
    SSCase "wf_ECs".
      eapply free_allocas_preserves_wf_ECStack; eauto.
      apply NoDup_strenthening in Hdisjals'; auto.

    SSCase "wf_ECs_head_tail".
      simpl in Hfr1, Hfr2.
      eapply free_allocas_preserves_wf_ECStack_head_tail'; eauto.

  split.
  SCase "Disjoint Allocas".
    apply wf_als_split in Hdisjals.
    destruct Hdisjals; auto.
    eapply free_allocas_preserves_wf_als; eauto.

  SCase "wfM".
    eapply free_allocas_preserves_wf_Mem; eauto.

Transparent inscope_of_tmn inscope_of_cmd.
Qed.


Lemma getIncomingValuesForBlockFromPHINodes_spec9: forall TD gl lc b id0 gvs0
  ps' l0,
  ret l0 = Opsem.getIncomingValuesForBlockFromPHINodes TD ps' b gl lc ->
  id0 `in` dom l0 ->
  lookupAL (GVsT DGVs) l0 id0 = ret gvs0 ->
  exists id1, exists t1, exists vls1, exists v, exists n,
    In (insn_phi id1 t1 vls1) ps' /\
    nth_list_value_l n vls1 = Some (v, getBlockLabel b) /\
    Opsem.getOperandValue TD v lc gl= Some gvs0.
Proof.
  induction ps' as [|[]]; simpl; intros.
    inv H. fsetdec.
    
    inv_mbind'. simpl in *.
    destruct (id0 == i0); subst.
      inv H1.
      destruct b. simpl in *.
      symmetry in HeqR.
      apply getValueViaLabelFromValuels__nth_list_value_l in HeqR; auto.
      destruct HeqR as [n HeqR].
      exists i0. exists t. exists l0. exists v. exists n.
      split; auto.

      apply IHps' in H1; auto; try fsetdec.
      destruct H1 as [id1 [t1 [vls1 [v' [n' [J1 [J2 J3]]]]]]].
      exists id1. exists t1. exists vls1. exists v'. exists n'.
      split; auto.
Qed.

Lemma unused_in_phi__wf_use_at_head: forall pinfo id1 t1 v1 l1 n vls1,
  used_in_phi (PI_id pinfo) (insn_phi id1 t1 vls1) = false ->
  nth_list_value_l n vls1 = ret (v1, l1) ->
  wf_use_at_head pinfo v1.
Proof.
  unfold wf_use_at_head.
  induction n; simpl; intros.
    destruct vls1; inv H0.
    simpl in H.
    apply orb_false_iff in H.
    destruct H; auto.

    destruct vls1; inv H0.
    simpl in H.
    apply orb_false_iff in H.
    destruct H; eauto.
Qed.

Lemma In_InPhiNodesB: forall p ps, In p ps -> InPhiNodesB p ps.
Proof.
  induction ps; simpl; intros.
    inv H.
    apply orb_true_iff.
    destruct H as [H | H]; subst.
      left. apply phinodeEqB_refl.
      right. apply IHps; auto.
Qed.

Lemma wf_defs_br : forall lc l' ps' cs' lc' tmn' gl los nts Ps ifs s
  (l3 : l) (ps : phinodes) (cs : list cmd) tmn pinfo (Hwfpi: WF_PhiInfo pinfo)
  (Hlkup : Some (block_intro l' ps' cs' tmn') = 
             lookupBlockViaLabelFromFdef (PI_f pinfo) l')
  (Hswitch : Opsem.switchToNewBasicBlock (los,nts) (block_intro l' ps' cs' tmn')
         (block_intro l3 ps cs tmn) gl lc = ret lc')
  als Mem maxb 
  (Hwfdfs : wf_defs maxb pinfo (los,nts) Mem lc als)
  (Hwflc : wf_lc Mem lc)
  (Hwfg : wf_globals maxb gl)
  (HwfF : wf_fdef ifs s (module_intro los nts Ps) (PI_f pinfo))
  (Huniq : uniqFdef (PI_f pinfo)),
  wf_defs maxb pinfo (los,nts) Mem lc' als.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  inv_mbind'.
  intros gvsa Hlkup'.
  assert (lookupAL (GVsT DGVs) lc (PI_id pinfo) = ret gvsa) as Hlkp.
    destruct (@AtomSetProperties.In_dec (PI_id pinfo) (dom l0)) 
      as [Hin | Hnotin].
      eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec7 in Hin; 
        eauto.
      contradict Hin.
      eapply WF_PhiInfo_spec6 in Hlkup; eauto. 
      
      apply OpsemProps.updateValuesForNewBlock_spec7 in Hlkup'; auto.
  assert (J3:=Hlkp).
  apply Hwfdfs in J3.
  destruct J3 as [J1 J2].
  split; auto.
    intros.
    destruct (@AtomSetProperties.In_dec id0 (dom l0)) as [Hin | Hnotin].
      rewrite OpsemProps.updateValuesForNewBlock_spec6' in Hlk0; auto.
      eapply getIncomingValuesForBlockFromPHINodes_spec9 in HeqR; eauto.
      destruct HeqR as [id1 [t1 [vls1 [v [n [J4 [J5 J6]]]]]]].
      unfold wf_non_alloca_GVs.
      destruct (id_dec id0 (PI_id pinfo)); auto.
      eapply operand__no_alias_with__head; eauto.
        symmetry in Hlkup.
        apply lookupBlockViaLabelFromFdef_inv in Hlkup; auto.
        destruct Hlkup as [_ Hlkup].
        assert (phinodeInFdefBlockB (insn_phi id1 t1 vls1) (PI_f pinfo) 
          (block_intro l' ps' cs' tmn') = true) as Hin'.
          apply andb_true_iff.
          split; auto.
          simpl.
          apply In_InPhiNodesB; auto.
        apply WF_PhiInfo_spec5 in Hin'; auto.
        eapply unused_in_phi__wf_use_at_head in Hin'; eauto.

      apply OpsemProps.updateValuesForNewBlock_spec7 in Hlk0; auto.
Qed.

Lemma wf_lc_br : forall (lc:DGVMap) l' ps' cs' lc' tmn' gl td 
  (l3 : l) (ps : phinodes) (cs : list cmd) tmn F
  (Hlkup : Some (block_intro l' ps' cs' tmn') = 
             lookupBlockViaLabelFromFdef F l')
  (Hswitch : Opsem.switchToNewBasicBlock td (block_intro l' ps' cs' tmn')
         (block_intro l3 ps cs tmn) gl lc = ret lc')
  Mem maxb (Hwflc : wf_lc Mem lc) (HwfM : wf_Mem maxb td Mem)
  (Hwfg : wf_globals maxb gl)
  (Huniq : uniqFdef F),
  wf_lc Mem lc'.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  inv_mbind'.
  intros id0 gvs0 Hlkup'.
  destruct (@AtomSetProperties.In_dec id0 (dom l0)) as [Hin | Hnotin].
      rewrite (@OpsemProps.updateValuesForNewBlock_spec6' DGVs) in Hlkup'; auto.
      eapply getIncomingValuesForBlockFromPHINodes_spec9 in HeqR; eauto.
      destruct HeqR as [id1 [t1 [vls1 [v [n [J4 [J5 J6]]]]]]].
      destruct HwfM.
      eapply operand__lt_nextblock; eauto.

      apply (@OpsemProps.updateValuesForNewBlock_spec7 DGVs) in Hlkup'; auto.
      apply Hwflc in Hlkup'; auto.
Qed.

Lemma wf_ECStack_head_tail_br : forall (lc:DGVMap) l' ps' cs' lc' tmn' gl los 
  nts Ps ifs s (l3 : l) (ps : phinodes) (cs : list cmd) tmn F
  (Hlkup : Some (block_intro l' ps' cs' tmn') = 
             lookupBlockViaLabelFromFdef F l')
  (Hswitch : Opsem.switchToNewBasicBlock (los,nts) (block_intro l' ps' cs' tmn')
         (block_intro l3 ps cs tmn) gl lc = ret lc') EC pinfo
  Mem maxb (Hwflc : wf_ECStack_head_tail maxb pinfo (los, nts) Mem lc EC) 
  (HwfM : wf_Mem maxb (los, nts) Mem)
  (Hwfg : wf_globals maxb gl)
  (HwfF : wf_fdef ifs s (module_intro los nts Ps) F)
  (Huniq : uniqFdef F),
  wf_ECStack_head_tail maxb pinfo (los, nts) Mem lc' EC.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  inv_mbind'.
  intros ec0 Hintl.
  apply Hwflc in Hintl.
  destruct ec0. simpl in *.
  intros. subst.
  assert (H0':=H0).
  apply Hintl in H0; auto.
  destruct H0 as [J1 [J2 J3]].
  split; auto.
  split; auto.
    intros.
    destruct (@AtomSetProperties.In_dec id1 (dom l0)) as [Hin | Hnotin].
      rewrite (@OpsemProps.updateValuesForNewBlock_spec6' DGVs) in H; auto.
      eapply getIncomingValuesForBlockFromPHINodes_spec9 in HeqR; eauto.
      destruct HeqR as [id2 [t1 [vls1 [v [n [J4 [J5 J6]]]]]]].
      eapply operand__no_alias_with__tail with
        (EC:={|
            Opsem.CurFunction := PI_f pinfo;
            Opsem.CurBB := CurBB;
            Opsem.CurCmds := CurCmds;
            Opsem.Terminator := Terminator;
            Opsem.Locals := Locals;
            Opsem.Allocas := Allocas |}); eauto; simpl; auto.

      apply (@OpsemProps.updateValuesForNewBlock_spec7 DGVs) in H; eauto.
Qed.

Lemma preservation_branch: forall (maxb : Z) (pinfo : PhiInfo) (S : system)
  (los : layouts) (nts : namedts) (Ps : list product) (F : fdef) (B : block)
  (lc : Opsem.GVsMap) (gl : GVMap) (fs : GVMap) (bid : id) (Cond : value)
  (l1 : l) (l2 : l) (EC : list Opsem.ExecutionContext) (Mem : mem) 
  (als : list mblock) cfg ECs
  (EQ1 : cfg = OpsemAux.mkCfg S (los, nts) Ps gl fs)
  (EQ2 : ECs = {| Opsem.CurFunction := F;
                 Opsem.CurBB := B;
                 Opsem.CurCmds := nil;
                 Opsem.Terminator := insn_br bid Cond l1 l2;
                 Opsem.Locals := lc;
                 Opsem.Allocas := als |} :: EC)
  (Hinv : OpsemPP.wf_State cfg
           {| Opsem.ECS := ECs; Opsem.Mem := Mem |})
  (Hwfg : wf_globals maxb
           (OpsemAux.Globals
              {|
              OpsemAux.CurSystem := S;
              OpsemAux.CurTargetData := (los, nts);
              OpsemAux.CurProducts := Ps;
              OpsemAux.Globals := gl;
              OpsemAux.FunTable := fs |}))
  (Hinbd : 0 <= maxb) (HwfPI : WF_PhiInfo pinfo) (conds : GVsT DGVs)
  (c : GenericValue) (l' : l) (ps' : phinodes) (cs' : cmds) (tmn' : terminator)
  (lc' : Opsem.GVsMap)
  (H : Opsem.getOperandValue (los, nts) Cond lc gl = ret conds)
  (H0 : c @ conds)
  (H1 : ret block_intro l' ps' cs' tmn' =
       (if isGVZero (los, nts) c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1))
  (H2 : Opsem.switchToNewBasicBlock (los, nts) (block_intro l' ps' cs' tmn') B
         gl lc = ret lc')
  (HwfS1 : wf_State maxb pinfo cfg
            {| Opsem.ECS := ECs; Opsem.Mem := Mem |}),
  wf_State maxb pinfo cfg
     {|
     Opsem.ECS := {|
                  Opsem.CurFunction := F;
                  Opsem.CurBB := block_intro l' ps' cs' tmn';
                  Opsem.CurCmds := cs';
                  Opsem.Terminator := tmn';
                  Opsem.Locals := lc';
                  Opsem.Allocas := als |} :: EC;
     Opsem.Mem := Mem |}.
Proof.
  intros. subst.
  destruct Hinv as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l3 [ps3 [cs3' Heq1]]]]]]]] 
     [HwfEC HwfCall]
     ]
    ]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC.
  destruct HwfS1 as [[[Hinscope1 Hwflc1] [HwfECs Hfr1]] [Hdisjals HwfM]]. 
  simpl. simpl in Hdisjals.
  fold wf_ECStack in HwfECs.
  assert (Hdisjals':=Hdisjals).
  destruct Hdisjals' as [Hdisjals' _].
  assert (HwfF := HwfSystem).
  eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  assert (ret block_intro l' ps' cs' tmn' =
    lookupBlockViaLabelFromFdef F l') as Hlkup.
    symmetry.
    apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
    symmetry in H1.
    destruct (isGVZero (los, nts) c);
      apply lookupBlockViaLabelFromFdef_inv in H1; 
        try solve [auto | destruct H1; auto].
  split; auto.
  split.
  SCase "wf_ECStack".
    split.
      SSCase "sdom".
      destruct (fdef_dec (PI_f pinfo) F); subst; auto.
        eapply wf_defs_br; eauto.
      SSCase "wf_lc".
      eapply wf_lc_br; eauto.
  split; auto.
  SCase "wf_ECs_tail".
    eapply wf_ECStack_head_tail_br; eauto.
Qed.

Lemma preservation_branch_uncond: forall (maxb : Z) (pinfo : PhiInfo) 
  (S : system) (los : layouts) (nts : namedts) (Ps : list product) (F : fdef) 
  (B : block) (lc : Opsem.GVsMap) (gl : GVMap) (fs : GVMap) (bid : id) 
  (l0 : l) (EC : list Opsem.ExecutionContext) (Mem : mem) 
  (als : list mblock) cfg ECs
  (EQ1 : cfg = OpsemAux.mkCfg S (los, nts) Ps gl fs)
  (EQ2 : ECs = {| Opsem.CurFunction := F;
                 Opsem.CurBB := B;
                 Opsem.CurCmds := nil;
                 Opsem.Terminator := insn_br_uncond bid l0;
                 Opsem.Locals := lc;
                 Opsem.Allocas := als |} :: EC)
  (Hinv : OpsemPP.wf_State cfg
           {| Opsem.ECS := ECs; Opsem.Mem := Mem |})
  (Hwfg : wf_globals maxb
           (OpsemAux.Globals
              {|
              OpsemAux.CurSystem := S;
              OpsemAux.CurTargetData := (los, nts);
              OpsemAux.CurProducts := Ps;
              OpsemAux.Globals := gl;
              OpsemAux.FunTable := fs |}))
  (Hinbd : 0 <= maxb) (HwfPI : WF_PhiInfo pinfo)
  (l' : l) (ps' : phinodes) (cs' : cmds) (tmn' : terminator)
  (lc' : Opsem.GVsMap)
  (H1 : ret block_intro l' ps' cs' tmn' = lookupBlockViaLabelFromFdef F l0)
  (H2 : Opsem.switchToNewBasicBlock (los, nts) (block_intro l' ps' cs' tmn') B
         gl lc = ret lc')
  (HwfS1 : wf_State maxb pinfo cfg
            {| Opsem.ECS := ECs; Opsem.Mem := Mem |}),
  wf_State maxb pinfo cfg
     {|
     Opsem.ECS := {|
                  Opsem.CurFunction := F;
                  Opsem.CurBB := block_intro l' ps' cs' tmn';
                  Opsem.CurCmds := cs';
                  Opsem.Terminator := tmn';
                  Opsem.Locals := lc';
                  Opsem.Allocas := als |} :: EC;
     Opsem.Mem := Mem |}.
Proof.
  intros. subst.
  destruct Hinv as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l3 [ps3 [cs3' Heq1]]]]]]]] 
     [HwfEC HwfCall]
     ]
    ]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC.
  destruct HwfS1 as [[[Hinscope1 Hwflc1] [HwfECs Hfr1]] [Hdisjals HwfM]]. 
  simpl. simpl in Hdisjals.
  fold wf_ECStack in HwfECs.
  assert (Hdisjals':=Hdisjals).
  destruct Hdisjals' as [Hdisjals' _].
  assert (HwfF := HwfSystem).
  eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  assert (ret block_intro l' ps' cs' tmn' = lookupBlockViaLabelFromFdef F l') 
    as Hlkup.
    symmetry.
    apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
    symmetry in H1.
    apply lookupBlockViaLabelFromFdef_inv in H1; 
        try solve [auto | destruct H1; auto].
  split; auto.
  split.
  SCase "wf_ECStack".
    split.
      SSCase "sdom".
      destruct (fdef_dec (PI_f pinfo) F); subst; auto.
        eapply wf_defs_br; eauto.
      SSCase "wf_lc".
      eapply wf_lc_br; eauto.
  split; auto.
  SCase "wf_ECs_tail".
    eapply wf_ECStack_head_tail_br; eauto.
Qed.

Lemma FBOP__wf_GVs_in_ECs : forall (v : value) (v0 : value) (id1 : id) 
  (fbop0 : fbop) gvs3 TD fbop0 fp lc gl hd tl Mem0 td pinfo maxb 
  (Hneq: PI_f pinfo = Opsem.CurFunction hd -> id1 <> PI_id pinfo)
  (H11 : FBOP TD lc gl fbop0 fp v v0 = ret gvs3),
  wf_GVs_in_ECs maxb pinfo td Mem0 hd tl id1 gvs3.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct hd; simpl in *.
  split.   
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
    apply Hneq in EQ. clear Hneq.
    split; intros; subst; try congruence.
      eapply FBOP_preserves_no_alias; eauto.
  split.
    intros. eapply FBOP_preserves_no_alias; eauto.
    intros. subst. apply FBOP_preserves_no_embedded_ptrs in H11; auto.
      apply no_embedded_ptrs__valid_ptrs; auto.
Qed.

Lemma insertGenericValue__wf_GVs_in_ECs : forall (v v': value) (id1 : id)
  gvs2 TD gl EC Mem pinfo maxb t t'
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) 
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: Opsem.CurFunction EC = (PI_f pinfo) -> wf_use_at_head pinfo v) 
  (Hwfv': Opsem.CurFunction EC = (PI_f pinfo) -> wf_use_at_head pinfo v') 
  gvs gvs'
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (H : Opsem.getOperandValue TD v (Opsem.Locals EC) gl = ret gvs) 
  (H' : Opsem.getOperandValue TD v' (Opsem.Locals EC) gl = ret gvs') idxs
  (H11 : ret gvs2 = Opsem.insertGenericValue TD t gvs idxs t' gvs') tl
  (Hwfstk: 
    wf_ECStack_head_tail maxb pinfo TD Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo TD Mem EC tl id1 gvs2.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct EC.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
    apply Hneq in EQ. clear Hneq.
    split; intros; subst; try congruence.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=gvs)
        (M:=Mem) in H; eauto.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=gvs')
        (M:=Mem) in H'; eauto.
      eapply insertGenericValue_preserves_no_alias in H11; eauto.
  split.
    intros.
    eapply operand__no_alias_with__tail' in H; eauto.
    eapply operand__no_alias_with__tail' in H'; eauto.
    eapply insertGenericValue_preserves_no_alias in H11; eauto.

    eapply insertGenericValue_preserves_valid_ptrs in H11; eauto.
    eapply operand__lt_nextblock in H; eauto.
    eapply operand__lt_nextblock in H'; eauto.
Qed.

Lemma extractGenericValue__wf_GVs_in_ECs : forall (v : value) (id1 : id)
  gvs2 TD gl EC Mem pinfo maxb t 
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) 
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: Opsem.CurFunction EC = (PI_f pinfo) ->
         wf_use_at_head pinfo v) gvs1
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (H : Opsem.getOperandValue TD v (Opsem.Locals EC) gl = ret gvs1) idxs
  (H11 : ret gvs2 = Opsem.extractGenericValue TD t gvs1 idxs) tl
  (Hwfstk: 
    wf_ECStack_head_tail maxb pinfo TD Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo TD Mem EC tl id1 gvs2.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct EC.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
    apply Hneq in EQ. clear Hneq.
    split; intros; subst; try congruence.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=gvs1)
        (M:=Mem) in H; eauto.
        eapply extractGenericValue_preserves_no_alias in H11; eauto.
  split.
    intros.
    eapply operand__no_alias_with__tail' in H; eauto.
    eapply extractGenericValue_preserves_no_alias in H11; eauto.

    eapply extractGenericValue_preserves_valid_ptrs in H11; eauto.
    eapply operand__lt_nextblock in H; eauto.
Qed.

Lemma EXT__wf_GVs_in_ECs : forall (id1 : id) gvs2 TD gl EC Mem pinfo maxb
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) v1
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: Opsem.CurFunction EC = (PI_f pinfo) ->
         wf_use_at_head pinfo v1) eop0 t1 t2 
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (H11 : Opsem.EXT TD (Opsem.Locals EC) gl eop0 t1 v1 t2 = ret gvs2) tl
  (Hwfstk: 
    wf_ECStack_head_tail maxb pinfo TD Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo TD Mem EC tl id1 gvs2.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct EC.
  apply OpsemProps.EXT_inversion in H11.
  destruct H11 as [gv1 [J1 J2]].
  unfold lift_op1 in J2. simpl in J2. unfold MDGVs.lift_op1 in J2.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
    apply Hneq in EQ. clear Hneq.
    split; intros; subst; try congruence.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=gv1)
        (M:=Mem) in J1; eauto.
        eapply mext_preserves_no_alias in J2; eauto.
  split.
    intros.
    eapply operand__no_alias_with__tail' in J1; eauto.
    eapply mext_preserves_no_alias in J2; eauto.

    eapply mext_preserves_valid_ptrs in J2; eauto.
Qed.

Lemma TRUNC__wf_GVs_in_ECs : forall (id1 : id) gvs2 TD gl EC Mem pinfo maxb
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) v1
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: Opsem.CurFunction EC = (PI_f pinfo) ->
         wf_use_at_head pinfo v1) top0 t1 t2 
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (H11 : Opsem.TRUNC TD (Opsem.Locals EC) gl top0 t1 v1 t2 = ret gvs2) tl
  (Hwfstk: 
    wf_ECStack_head_tail maxb pinfo TD Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo TD Mem EC tl id1 gvs2.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct EC.
  apply OpsemProps.TRUNC_inversion in H11.
  destruct H11 as [gv1 [J1 J2]].
  unfold lift_op1 in J2. simpl in J2. unfold MDGVs.lift_op1 in J2.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
    apply Hneq in EQ. clear Hneq.
    split; intros; subst; try congruence.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=gv1)
        (M:=Mem) in J1; eauto.
        eapply mtrunc_preserves_no_alias in J2; eauto.
  split.
    intros.
    eapply operand__no_alias_with__tail' in J1; eauto.
    eapply mtrunc_preserves_no_alias in J2; eauto.

    eapply mtrunc_preserves_valid_ptrs in J2; eauto.
Qed.

Lemma ICMP__wf_GVs_in_ECs : forall (id1 : id) gvs2 TD gl EC Mem pinfo maxb
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) v1 v2
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv1: Opsem.CurFunction EC = (PI_f pinfo) -> wf_use_at_head pinfo v1)
  (Hwfv2: Opsem.CurFunction EC = (PI_f pinfo) -> wf_use_at_head pinfo v2)
  cond0 t
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (H11 : Opsem.ICMP TD (Opsem.Locals EC) gl cond0 t v1 v2 = ret gvs2) tl
  (Hwfstk: 
    wf_ECStack_head_tail maxb pinfo TD Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo TD Mem EC tl id1 gvs2.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct EC.
  apply OpsemProps.ICMP_inversion in H11.
  destruct H11 as [gv1 [gv2 [J1 [J2 J3]]]].
  Local Transparent lift_op2.
  unfold lift_op2 in J3. simpl in J3. unfold MDGVs.lift_op2 in J3.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
    apply Hneq in EQ. clear Hneq.
    split; intros; subst; try congruence.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=gv1)
        (M:=Mem) in J1; eauto.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=gv2)
        (M:=Mem) in J2; eauto.
      eapply micmp_preserves_no_alias in J3; eauto.
  split.
    intros.
    eapply operand__no_alias_with__tail' in J1; eauto.
    eapply operand__no_alias_with__tail' in J2; eauto.
    eapply micmp_preserves_no_alias in J3; eauto.

    eapply micmp_preserves_valid_ptrs in J3; eauto.
Qed.


Lemma FCMP__wf_GVs_in_ECs : forall (id1 : id) gvs2 TD gl EC Mem pinfo maxb
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) v1 v2
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv1: Opsem.CurFunction EC = (PI_f pinfo) -> wf_use_at_head pinfo v1)
  (Hwfv2: Opsem.CurFunction EC = (PI_f pinfo) -> wf_use_at_head pinfo v2)
  fcond0 fp
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (H11 : Opsem.FCMP TD (Opsem.Locals EC) gl fcond0 fp v1 v2 = ret gvs2) tl
  (Hwfstk: 
    wf_ECStack_head_tail maxb pinfo TD Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo TD Mem EC tl id1 gvs2.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct EC.
  apply OpsemProps.FCMP_inversion in H11.
  destruct H11 as [gv1 [gv2 [J1 [J2 J3]]]].
  Local Transparent lift_op2.
  unfold lift_op2 in J3. simpl in J3. unfold MDGVs.lift_op2 in J3.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
    apply Hneq in EQ. clear Hneq.
    split; intros; subst; try congruence.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=gv1)
        (M:=Mem) in J1; eauto.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=gv2)
        (M:=Mem) in J2; eauto.
      eapply mfcmp_preserves_no_alias in J3; eauto.
  split.
    intros.
    eapply operand__no_alias_with__tail' in J1; eauto.
    eapply operand__no_alias_with__tail' in J2; eauto.
    eapply mfcmp_preserves_no_alias in J3; eauto.

    eapply mfcmp_preserves_valid_ptrs in J3; eauto.
Qed.

Lemma getOperandValue__wf_GVs_in_ECs : forall (v : value) (id1 : id)
  TD gl EC Mem pinfo maxb  
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) 
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: Opsem.CurFunction EC = (PI_f pinfo) ->
         wf_use_at_head pinfo v) gvs
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (H : Opsem.getOperandValue TD v (Opsem.Locals EC) gl = ret gvs) tl
  (Hwfstk: 
    wf_ECStack_head_tail maxb pinfo TD Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo TD Mem EC tl id1 gvs.
Proof.
  intros. 
  unfold wf_GVs_in_ECs. destruct EC.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    assert (PI_f pinfo = PI_f pinfo) as EQ. auto.
    apply Hneq in EQ. clear Hneq.
    split; intros; subst; try congruence.
      eapply operand__no_alias_with__head with (mptr0:=gvs) (M:=Mem) in H1; 
        eauto.
  split.
    intros.
    eapply operand__no_alias_with__tail' in H; eauto.
    eapply operand__lt_nextblock in H; eauto.
Qed.

Ltac preservation_tac0:=
  match goal with
  | HwfPI : WF_PhiInfo _ ,
    HFinPs1: InProductsB _ _ = _,
    HBinF1: blockInFdefB _ _ = _,
    HmInS: moduleInSystemB _ _ = _,
    HwfSystem: wf_system _ _ |- _ =>
    clear - HBinF1 HFinPs1 HmInS HwfPI HwfSystem;
    simpl; intros; subst;
    eapply wf_system__uniqFdef in HFinPs1; eauto; 
    intro J; subst;
    apply PhiInfo_must_be_promotable_alloca in HBinF1;
              try solve [auto | inv HBinF1 | intros; congruence]
  end.

Ltac preservation_tac1:=
match goal with
| Hinv : OpsemPP.wf_State _ _,
  HwfS1 : wf_State _ _ _ _,
  HwfPI : WF_PhiInfo _ |- _ =>
  simpl_ctx Hinv HwfS1;
  preservation_tac0
end.

Ltac preservation_tac2:=
  match goal with
  | HwfPI : WF_PhiInfo _,
    HFinPs1: InProductsB _ _ = _,
    HBinF1: blockInFdefB _ _ = _,
    HmInS: moduleInSystemB _ _ = _,
    HwfSystem: wf_system _ _ |- _ =>
    clear - HBinF1 HFinPs1 HmInS HwfPI HwfSystem;
    simpl; intros; subst;
    eapply wf_system__uniqFdef in HFinPs1; eauto;
    eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HBinF1; 
      eauto using in_middle;
    eapply WF_PhiInfo_spec4 in HBinF1; eauto; simpl; auto
  end.

Ltac preservation_tac3 :=
  match goal with
  | Hinv : OpsemPP.wf_State _ _,
    HwfS1 : wf_State _ _ _ _,
    HwfPI : WF_PhiInfo _ |- _ =>
    simpl_ctx Hinv HwfS1;
    preservation_tac2
  end.


Ltac simpl_ctx' Hinv HwfS1 :=
  destruct Hinv as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [HwfEC0 HwfCall]
    ]]]]]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0;
  destruct HwfS1 as [[[_ Hwflc] [HwfECs Hwfht]] [Hnonup1 [_ HwfM]]].

Lemma preservation : forall maxb pinfo cfg S1 S2 tr
  (Hinv: OpsemPP.wf_State cfg S1)
  (Hwfg: wf_globals maxb (OpsemAux.Globals cfg)) (Hinbd: 0 <= maxb)
  (HwfPI: WF_PhiInfo pinfo) (HsInsn: Opsem.sInsn cfg S1 S2 tr)
  (HwfS1: wf_State maxb pinfo cfg S1), wf_State maxb pinfo cfg S2.
Proof.
  intros.
  (sInsn_cases (induction HsInsn) Case); destruct TD as [los nts]; simpl HwfS1.

Case "sReturn". eapply preservation_return; eauto. 
Case "sReturnVoid". eapply preservation_return_void; eauto. 
Case "sBranch". eapply preservation_branch in Hinv; eauto.
Case "sBranch_uncond". eapply preservation_branch_uncond in Hinv; eauto.

Case "sBop".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    eapply BOP__wf_GVs_in_ECs; eauto.
      preservation_tac1.

Case "sFBop".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    eapply FBOP__wf_GVs_in_ECs; eauto.
      preservation_tac1.

Case "sExtractValue".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    simpl_ctx' Hinv HwfS1.
    eapply extractGenericValue__wf_GVs_in_ECs; simpl;
      try solve [eauto | preservation_tac2 | preservation_tac0].

Case "sInsertValue". 
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    simpl_ctx' Hinv HwfS1.
    eapply insertGenericValue__wf_GVs_in_ECs with (v:=v) (gvs:=gvs) (v':=v')
      (gvs':=gvs'); try solve [eauto | preservation_tac2 | preservation_tac0].

Case "sMalloc". 
  assert (PI_f pinfo = F -> id0 <> PI_id pinfo) as Hneq. 
    preservation_tac1.
  simpl_ctx Hinv HwfS1.
  split.
    split.
      eapply impure_cmd_updated_preserves_wf_EC; eauto.
        intros. subst.
        apply wf_EC__wf_lc in HwfEC.
        eapply malloc_preserves_wf_defs_at_head; eauto.
        eapply malloc_preserves_wf_lc; eauto.
    split.
      eapply malloc_preserves_wf_ECStack_in_tail in H2; eauto.
      eapply malloc_preserves_wf_ECStack_head_tail in H2; eauto.
  split.
    destruct HwfM1.
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
          preservation_tac2.
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

        eapply wf_system__wf_fdef in HwfSystem; eauto.
        eapply alloca_preserves_wf_defs_at_head; eauto.
         
        eapply malloc_preserves_wf_lc; eauto.
    split.       
      eapply malloc_preserves_wf_ECStack_in_tail in H2; eauto.
      eapply malloc_preserves_wf_ECStack_head_tail in H2; eauto.
  split.
    destruct HwfM1.
    eapply malloc_preserves_wf_als in H2; eauto.
    eapply malloc_preserves_wf_Mem in H2; eauto.

Case "sLoad". 
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    assert (PI_f pinfo = F -> id0 <> PI_id pinfo) as Hneq. 
      preservation_tac1.
    destruct HwfS1 as [[[_ Hwflc] [_ Hwfstk]] [_ HwfM]]. 
    eapply mload__wf_GVs_in_ECs; eauto using wf_EC__wf_lc.

Case "sStore". 
  simpl_ctx Hinv HwfS1.
  assert (wf_lc Mem lc) as Hwflc.
    apply wf_EC__wf_lc in HwfEC; auto.
  split.
    split.
      eapply impure_cmd_non_updated_preserves_wf_EC with (M:=Mem); eauto.
        intros. subst.
        eapply mstore_preserves_wf_defs_at_head with (gvs1:=gvs1) in H3; eauto.
          preservation_tac2.
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
    simpl_ctx' Hinv HwfS1.
    eapply GEP__wf_GVs_in_ECs; try solve 
      [eauto using wf_EC__wf_lc | preservation_tac2 | preservation_tac0].

Case "sTrunc".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    simpl_ctx' Hinv HwfS1.
    eapply TRUNC__wf_GVs_in_ECs; 
      try solve [eauto | preservation_tac2 | preservation_tac0].

Case "sExt".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    simpl_ctx' Hinv HwfS1.
    eapply EXT__wf_GVs_in_ECs;
      try solve [eauto | preservation_tac2 | preservation_tac0].

Case "sCast". 
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    simpl_ctx' Hinv HwfS1.
    eapply CAST__wf_GVs_in_ECs;
      try solve [eauto | preservation_tac2 | preservation_tac0].

Case "sIcmp". 
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    simpl_ctx' Hinv HwfS1.
    eapply ICMP__wf_GVs_in_ECs with (v1:=v1)(v2:=v2);
      try solve [eauto | preservation_tac2 | preservation_tac0].

Case "sFcmp". 
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    simpl_ctx' Hinv HwfS1.
    eapply FCMP__wf_GVs_in_ECs with (v1:=v1)(v2:=v2);
      try solve [eauto | preservation_tac2 | preservation_tac0].

Case "sSelect". 
  destruct (isGVZero (los, nts) c);
    eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
      try solve [eauto | 
                 simpl_ctx' Hinv HwfS1;
                 match goal with
                 | H1: Opsem.getOperandValue _ ?v1 _ _ = ret ?gvs1 |- 
                       wf_GVs_in_ECs _ _ _ _ _ _ _ ?gvs1 => 
                   eapply getOperandValue__wf_GVs_in_ECs with (v:=v1); 
                     try solve [eauto | preservation_tac2 | preservation_tac0]
                 end].

Case "sCall". eapply preservation_Call; eauto.

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

Opaque lift_op1. 

End Promotability.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)

