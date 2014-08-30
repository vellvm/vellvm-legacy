Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import primitives.
Require Import Maps.
Require Import vmem2reg.
Require Import opsem_props.
Require Import memory_props.
Require Import palloca_props.
Require Import program_sim.
Require Import trans_tactic.

(* The file proves promotabilityy: promotable allocations aren’t aliased, whose 
   proof itself is also an application of GWF FR. 

   The micro transformations except phinode-nodes elimination rely on the 
   promotable property. The promotable property ensures that a promotable alloca 
   of a program does not escape—the program can access the data stored at the 
   allocation, but cannot pass the address of the allocation to others. 
   Therefore, in the program, the promotable alloca and all other pointers (in 
   memory, local temporaries and temporaries on stack) must not alias. *)

Module Promotability.

Export MemProps.

(********************************************************************************)
(* We first define promotablity. *)

(* If a variable [id1] is not promotable, its value [gvs1] must not alias the
   promotable location [gvsa]. *)
Definition wf_non_alloca_GVs (pinfo:PhiInfo) (id1:id) (gvs1 gvsa:GenericValue)
  : Prop :=
(if (id_dec id1 (PI_id pinfo)) then True else no_alias gvs1 gvsa).

(* mb: the block index for a promotable location [pinfo].
  The allocated memory range of pinfo must be larger than the type size of
  [pinfo]. *)
Definition alloca_size_prop TD (pinfo:PhiInfo) (M:mem) (mb:Values.block): Prop :=
match getTypeAllocSize TD (PI_typ pinfo) with
| Some tsz =>
    (* We can prove hi = tsz * [| PI_num pinfo |].
       But, the invariant is sufficient so far. *)
    (forall lo hi,
      Mem.bounds M mb = (lo, hi) ->
      lo = 0 /\ hi >= Z_of_nat tsz) /\
    Mem.range_perm M mb 0 (Z_of_nat tsz) Freeable
| None => False
end.

(* maxb: the boundary between globals and heap
   gvsa: the value of the promotable alloca
   als: the list of alloca locations of the current function

   1) the data stored at gvsa are consistent with pinfo's type
   2) the location (gvsa) is in als, and its memory range is larger 
      then pinfo's type size.
   3) no pointers stored at memort alias gvsa
   4) gvsa is a valid location to load   
*)
Definition wf_alloca_GVs (maxb:Values.block) (pinfo:PhiInfo) TD Mem
  (gvsa:GenericValue) (als:list Values.block) : Prop :=
encode_decode_ident TD Mem gvsa (PI_typ pinfo) (PI_align pinfo) /\
(exists mb, gvsa = ($ (blk2GV TD mb) # (typ_pointer (PI_typ pinfo)) $) /\
   In mb als /\ maxb < mb < Mem.nextblock Mem /\
   alloca_size_prop TD pinfo Mem mb) /\
(forall gptr gvs1 ty al,
   mload TD Mem gptr ty al = Some gvs1 ->
   no_alias gvs1 gvsa) /\
exists gv,
  mload TD Mem gvsa (PI_typ pinfo) (PI_align pinfo) = Some gv.

(* In the locals [lc], 
     if pinfo is defined, it satisfies wf_alloca_GVs;
     other ids do not alias pinfo. *)
Definition wf_defs (maxb:Values.block) (pinfo:PhiInfo) TD M (lc:DGVMap)
  (als:list Values.block) : Prop :=
forall gvsa
  (Hlkp: lookupAL _ lc (PI_id pinfo) = Some gvsa),
  wf_alloca_GVs maxb pinfo TD M gvsa als /\
  (forall id0 gvs0
   (*Hin0: In id0 ids0*)
   (Hlk0: lookupAL _ lc id0 = Some gvs0),
   wf_non_alloca_GVs pinfo id0 gvs0 gvsa).

(* For each EC, 
   1) the EC for pinfo must satisfy wf_defs.
   2) Locals in all ECs must hold valid pointers. *)
Definition wf_ExecutionContext (maxb:Values.block) (pinfo:PhiInfo) TD M
  (ec:Opsem.ExecutionContext) : Prop :=
let '(Opsem.mkEC f b cs tmn lc als) := ec in
(if (fdef_dec (PI_f pinfo) f) then wf_defs maxb pinfo TD M lc als else True)
/\ wf_lc M lc.

(* The predicate for the non-current ECs's locals, ec0.
   lc is the toppest local
   if the ec0 with local lc0 is for pinfo
   1) the promotable location in lc0 is valid
   2) lc does not alias pinfo
   3) all pointers in memory do no alias pinfo in lc0
*)
Definition wf_ECStack_head_in_tail (maxb:Values.block) (pinfo:PhiInfo) TD M
  (lc:DGVMap) (ec0:Opsem.ExecutionContext) : Prop :=
let '(Opsem.mkEC f0 b0 cs0 tmn0 lc0 _) := ec0 in
forall gvsa : GVsT DGVs,
  f0 = PI_f pinfo ->
  lookupAL _ lc0 (PI_id pinfo) = Some gvsa ->
  (exists mb, gvsa = ($ (blk2GV TD mb) # (typ_pointer (PI_typ pinfo)) $)  /\
    maxb < mb < Mem.nextblock M) /\ 
  (forall id1 gvs1,
    lookupAL _ lc id1 = Some gvs1 ->
    no_alias gvs1 gvsa) /\
  (forall gptr t al gvs1,
    mload TD M gptr t al = Some gvs1 ->
    no_alias gvs1 gvsa) .

(* All non-head ECs satisfy wf_ECStack_head_in_tail. *)
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

(* 1) All ECs satisfy wf_ECStack.
   2) all allocas are valid.
   3) all pointers in memory are valid. *)
Definition wf_State (maxb:Values.block) (pinfo:PhiInfo) (cfg:OpsemAux.Config)
  (S:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg _ td _ _ _ ) := cfg in
let '(Opsem.mkState ecs M) := S in
wf_ECStack maxb pinfo td M ecs /\
wf_als maxb M
  (flat_map (fun ec => let '(Opsem.mkEC _ _ _ _ _ als) := ec in als) ecs) /\
wf_Mem maxb td M.

(********************************************************************************)
(* The following [preservation] proves that wf_State is preserved by small-step 
   evaluation.  *)

(* This predicate is used to specify a value to add to locals.
   M, lc, als are the current state.
   gv1 with name id1 is the new value to add into lc. *)
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

Lemma preservation_helper1: forall los nts Ps S F l1 ps1 cs1' c0 tmn
  (HwfS : wf_system S)
  (HMinS : moduleInSystemB (module_intro los nts Ps) S = true)
  (HFinPs : InProductsB (product_fdef F) Ps = true)
  (HBinF : blockInFdefB (l1, stmts_intro ps1 (cs1' ++ [c0]) tmn) F = true),
  ~ In (getCmdLoc c0) (getCmdsLocs cs1').
Proof.
  intros.
  eapply wf_system__uniq_block with (f:=F) in HwfS; eauto.
  simpl in HwfS.
  apply NoDup_split in HwfS.
  destruct HwfS as [_ J].
  apply NoDup_split in J.
  destruct J as [J _].
  rewrite getCmdsLocs_app in J.
  simpl in J.
  apply NoDup_last_inv in J. auto.
Qed.

Lemma preservation_helper2: forall los nts Ps S F l1 ps1 cs1' c0 tmn c cs
  (HwfS : wf_system S)
  (HMinS : moduleInSystemB (module_intro los nts Ps) S = true)
  (HFinPs : InProductsB (product_fdef F) Ps = true)
  (HBinF : blockInFdefB
            (l1, stmts_intro ps1 (cs1' ++ [c0] ++ [c] ++ cs) tmn) F = true),
  NoDup (getCmdsLocs (cs1' ++ [c0] ++ [c] ++ cs)).
Proof.
  intros.
  eapply wf_system__uniq_block with (f:=F) in HwfS; eauto.
  simpl in HwfS.
  apply NoDup_split in HwfS.
  destruct HwfS as [_ J].
  apply NoDup_split in J.
  destruct J as [J _]. auto.
Qed.

Lemma impure_cmd_non_updated_preserves_wf_EC : forall maxb pinfo TD M M' lc F B
  als tmn cs c0 l1 ps1 cs1' S
  (Heq: B = (l1, stmts_intro ps1 (cs1' ++ c0 :: cs) tmn))
  (HwfS: wf_system S) los nts (Heq': TD = (los, nts)) Ps
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

Lemma preservation_return_helper: forall (g : GVsT DGVs) pinfo lc' Mem'
  als' los nts maxb Mem ECs lc gl S Ps Result rt F t
  (Hwfv: wf_value S (module_intro los nts Ps) F Result rt)
  (HeqR1 : ret g = Opsem.getOperandValue (los,nts) Result lc gl)
  (g0 : GVsT DGVs)
  (HeqR2 : ret g0 = lift_op1 DGVs (fit_gv (los,nts) t) g t)
  (Hwfg : wf_globals maxb gl) EC
  (Heq1 : Opsem.CurFunction EC = PI_f pinfo)
  (Heq2 : Opsem.Locals EC = lc')
  (Hfr1 : wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc (EC :: ECs))
  (Hinscope2 : wf_defs maxb pinfo (los,nts) Mem' lc' als')
  (gvsa : GVsT DGVs)
  (Hlkp : lookupAL (GVsT DGVs) lc' (PI_id pinfo) = ret gvsa),
  no_alias g0 gvsa.
Proof.
  intros.
  assert (Hlkp':=Hlkp).
  apply Hinscope2 in Hlkp'; auto.
  unfold wf_alloca_GVs in Hlkp'.
  destruct Hlkp' as [[_ [[mb [EQ [Hin Hbound]]] _]] _].
  assert (In EC (EC::ECs)) as Hin'. simpl. auto.
  apply Hfr1 in Hin'. clear Hfr1.
  destruct EC. simpl in *. subst.
  eapply Hin' in Hlkp; eauto. clear Hin'.
  destruct Hlkp as [_ [G _]]. 
  Local Transparent lift_op1. simpl in HeqR2.
  unfold MDGVs.lift_op1, fit_gv in HeqR2.
  destruct (getTypeSizeInBits (los,nts) t); tinv HeqR2.
  destruct_if.
    destruct Result; simpl in HeqR1; eauto. 
    inv Hwfv.
    eapply const2GV_disjoint_with_runtime_alloca; eauto.
      omega.

    eapply undef_disjoint_with_ptr; eauto.
  Opaque lift_op1.
Qed.

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

Lemma operand__no_alias_with__tail: forall maxb pinfo los nts Ps M lc1 lc2 mptr0
  gl (Hwfgl : wf_globals maxb gl) v mptrs EC S t F
  (Hwft: wf_value S (module_intro los nts Ps) F v t)
  (Heq1: Opsem.CurFunction EC = PI_f pinfo)
  (Heq2: Opsem.Locals EC = lc2)
  (Hht : wf_ECStack_head_in_tail maxb pinfo (los,nts) M lc1 EC)
  (gvsa : GVsT DGVs) (Hin: mptr0 @ mptrs)
  (Hlkp : lookupAL (GVsT DGVs) lc2 (PI_id pinfo) = ret gvsa)
  (Hgetop : Opsem.getOperandValue (los,nts) v lc1 gl = ret mptrs),
  no_alias mptr0 gvsa.
Proof.
  intros.
  inv Hin. destruct EC. simpl in *.
  eapply Hht in Hlkp; eauto. clear Hht.
  destruct Hlkp as [[mb [J11 J12]] [Hlkp _]]; subst.
  destruct v; simpl in Hgetop.
    apply Hlkp in Hgetop; auto.
    inv Hwft.
    eapply const2GV_disjoint_with_runtime_alloca; eauto.
      omega.
Qed.

Lemma free_preserves_alloca_size_prop: forall TD M ptr M' mb pinfo
  (Hnoalias: no_alias ptr ($ blk2GV TD mb # (typ_pointer (PI_typ pinfo)) $))
  (Halc: alloca_size_prop TD pinfo M mb)
  (Hfree: free TD M ptr = Some M'),
  alloca_size_prop TD pinfo M' mb.
Proof.
  intros.
  unfold alloca_size_prop in *.
  erewrite <- bounds_mfree in Halc; eauto.
  inv_mbind. destruct Halc as [Halc1 Halc2].
  split; auto.
  eapply MemProps.range_perm_mfree_1 in Halc2; eauto.
  rewrite simpl_blk2GV in Hnoalias. simpl in Hnoalias. tauto.
Qed.

Lemma free_preserves_wf_defs_in_tail : forall maxb pinfo los nts M
  M' lc1 mptr0 mptrs gl v als lc2 S Ps t F
  (Hwft: wf_value S (module_intro los nts Ps) F v t)
  (Hgetop: Opsem.getOperandValue (los,nts) v lc1 gl = ret mptrs)
  (Hin: mptr0 @ mptrs) (Hwfgl: wf_globals maxb gl)
  (Hfree: free (los,nts) M mptr0 = ret M') EC
  (Heq1: Opsem.CurFunction EC = PI_f pinfo)
  (Heq2: Opsem.Locals EC = lc2)
  (Hht: wf_ECStack_head_in_tail maxb pinfo (los,nts) M lc1 EC)
  (Hwf: wf_defs maxb pinfo (los,nts) M lc2 als),
  wf_defs maxb pinfo (los,nts) M' lc2 als.
Proof.
  intros. unfold wf_defs.
  intros gvsa Hlkp.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    clear J2.
    destruct J1 as [J5 [[mb [J11 [J12 [J13 J14]]]] [J4 [gv J3]]]]; subst.
    assert (no_alias mptr0
             ($ blk2GV (los,nts) mb # typ_pointer (PI_typ pinfo) $)) as J.
      eapply operand__no_alias_with__tail; eauto.
    split.
      eapply free_preserves_encode_decode_ident; eauto.
    split.
      erewrite <- nextblock_free; eauto.
      eapply free_preserves_alloca_size_prop in J14; eauto.
    split.
      intros. eapply free_preserves_mload_inv in H; eauto.
      clear J4.
      exists gv. eapply free_preserves_mload; eauto.
Qed.

Lemma operand__no_alias_with__head: forall maxb pinfo los nts lc mptr0 mptrs gl v
  Ps S als t F
  (Hwft: wf_value S (module_intro los nts Ps) F v t)
  (Hgetop : Opsem.getOperandValue (los,nts) v lc gl = ret mptrs)
  (Hin : mptr0 @ mptrs) (Hwfgl : wf_globals maxb gl) M
  (Hwfu: wf_use_at_head pinfo v) (Hwf: wf_defs maxb pinfo (los,nts) M lc als)
  (gvsa : GVsT DGVs) (Hlkp : lookupAL (GVsT DGVs) lc (PI_id pinfo) = ret gvsa),
  no_alias mptr0 gvsa.
Proof.
  intros.
  apply Hwf in Hlkp; auto.
  destruct Hlkp as [[_ [J1 [J4 [gv J3]]]] J2].
  inv Hin.
  destruct v as [i0|]; simpl in Hgetop.
    apply J2 in Hgetop; auto.
    unfold wf_non_alloca_GVs in Hgetop.
    destruct (id_dec i0 (PI_id pinfo)); subst; auto.
      inv Hwfu.
      destruct (id_dec (PI_id pinfo) (PI_id pinfo)); try congruence.
        match goal with | H1 : _ = false |- _ => inv H1 end.

    destruct J1 as [mb [J11 [J12 J13]]]; subst.
    inv Hwft.
    eapply const2GV_disjoint_with_runtime_alloca; eauto.
      omega.
Qed.

Lemma free_preserves_wf_defs_at_head : forall maxb pinfo los nts M
  M' lc mptr0 mptrs gl v als S t Ps F
  (Hwft: wf_value S (module_intro los nts Ps) F v t)
  (Hgetop: Opsem.getOperandValue (los,nts) v lc gl = ret mptrs)
  (Hin: mptr0 @ mptrs) (Hwfgl: wf_globals maxb gl)
  (Hfree: free (los,nts) M mptr0 = ret M')
  (Hwfu: wf_use_at_head pinfo v)
  (Hwf: wf_defs maxb pinfo (los,nts) M lc als),
  wf_defs maxb pinfo (los,nts) M' lc als.
Proof.
  intros. unfold wf_defs.
  intros gvsa Hlkp.
  assert (no_alias mptr0 gvsa) as J.
    eapply operand__no_alias_with__head; eauto.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    destruct J1 as [J5 [[mb [J11 [J12 [J13 J14]]]] [J4 [gv J3]]]]; subst.
    split.
      eapply free_preserves_encode_decode_ident; eauto.
    split.
      erewrite <- nextblock_free; eauto.
      eapply free_preserves_alloca_size_prop in J14; eauto.
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

Lemma free_preserves_wf_ECStack_in_tail : forall maxb pinfo los nts M
  M' mptr0 mptrs gl v (Hwfpi: WF_PhiInfo pinfo) lc S Ps t F
  (Hwft: wf_value S (module_intro los nts Ps) F v t)
  (Hgetop: Opsem.getOperandValue (los,nts) v lc gl = ret mptrs)
  (Hin: mptr0 @ mptrs) (Hwfgl: wf_globals maxb gl)
  (Hfree: free (los,nts) M mptr0 = ret M') ECs
  (Hht: wf_ECStack_head_tail maxb pinfo (los,nts) M lc ECs)
  (Hwf: wf_ECStack maxb pinfo (los,nts) M ECs),
  wf_ECStack maxb pinfo (los,nts) M' ECs.
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

Lemma free_allocas_preserves_alloca_size_prop: forall TD mb als M M'
  (Hnoalias: ~ In mb als) pinfo
  (Halc: alloca_size_prop TD pinfo M mb)
  (Hfrees: free_allocas TD M als = Some M'),
  alloca_size_prop TD pinfo M' mb.
Proof.
  induction als; simpl; intros.
    inv Hfrees. auto.

    inv_mbind.
    eapply IHals in H0; eauto.
    eapply free_preserves_alloca_size_prop; eauto.
    rewrite simpl_blk2GV. simpl. tauto.
Qed.

Lemma free_allocas_preserves_wf_alloca: forall maxb pinfo TD Mem gvsa als0 als Mem',
  wf_alloca_GVs maxb pinfo TD Mem gvsa als0 ->
  NoDup (als ++ als0) ->
  free_allocas TD Mem als = ret Mem' ->
  wf_alloca_GVs maxb pinfo TD Mem' gvsa als0.
Proof.
  intros.
  unfold wf_alloca_GVs in *.
  destruct H as [J4 [[mb [J11 [J12 [J13 J14]]]] [J2 J3]]]; subst.
  assert (~ In mb als) as Hnotin.
    eapply NoDup_disjoint; eauto.
  split.
    eapply free_allocas_preserves_encode_decode_ident; eauto.
  split.
    erewrite <- nextblock_free_allocas; eauto.
    eapply free_allocas_preserves_alloca_size_prop in J14; eauto.
  split.
    intros gptr gvs1 ty al J.
    eapply free_allocas_preserves_mload_inv in J; eauto.

    destruct J3 as [gv J3].
    exists gv.
    eapply free_allocas_preserves_mload; eauto.
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

Lemma returnUpdateLocals__wf_lc: forall maxb los nts Result (lc:DGVMap) gl c'
  lc' Mem lc'' S Ps F rt
  (Hwft: wf_value S (module_intro los nts Ps) F Result rt)
  (H1 : Opsem.returnUpdateLocals (los,nts) c' Result lc lc' gl = ret lc'')
  (Hwflc1 : wf_lc Mem lc) (Hwflc2 : wf_lc Mem lc')
  (Hwfg : wf_globals maxb gl) (Hgbound : maxb < Mem.nextblock Mem),
  wf_lc Mem lc''.
Proof.
  intros.
  unfold Opsem.returnUpdateLocals in H1.
  inv_mbind.
  destruct_cmd c'; tinv H0.
  destruct n.
    inv H0; auto.

    inv_mbind.
    apply updateAddAL__wf_lc; auto.
    intros. subst. symmetry in HeqR.
Local Transparent lift_op1. unfold lift_op1 in HeqR0. simpl in HeqR0.
    unfold MDGVs.lift_op1, fit_gv in HeqR0. symmetry in HeqR0.
    inv_mbind.
    destruct_if.
      eapply operand__lt_nextblock in HeqR; eauto.

      unfold gundef in *. inv_mbind. simpl. apply mc2undefs_valid_ptrs.
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
    destruct J1 as [J8 [[mb [J11 [J12 [J13 J14]]]] [J4 [gv J3]]]]; subst.
    assert (no_alias (blk2GV TD a)
                     ($ blk2GV TD mb # typ_pointer (PI_typ pinfo) $))
      as Hnoalias.
      apply Hwf in Hlkp; auto.
      destruct Hlkp as [[_ [[mb' [J5 [J6 J7]]] _]] _].
      repeat rewrite simpl_blk2GV in J5. inv J5.
      repeat rewrite simpl_blk2GV. simpl.
      repeat split; auto.
      intro EQ. subst. apply H2. apply in_or_app; auto.
    split.
      eapply free_preserves_encode_decode_ident with (ptr2:=blk2GV TD a); eauto.
    split.
      erewrite <- nextblock_free; eauto.
      eapply free_preserves_alloca_size_prop with (ptr:=blk2GV TD a) in J14; eauto.
    split.
      intros. eapply free_preserves_mload_inv in H; eauto.
      exists gv.
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

Lemma free_allocas_preserves_wf_ECStack_head_tail : forall maxb pinfo los nts M
  M' lc als lc' F' lc'' ECs gl Result c' EC F
  (Heq1: Opsem.CurFunction EC = F') (Heq2: Opsem.Locals EC = lc')
  (Hwfg : wf_globals maxb gl) S Ps rt
  (Hwft: wf_value S (module_intro los nts Ps) F Result rt),
  free_allocas (los,nts) M als = ret M' ->
  Opsem.returnUpdateLocals (los,nts) c' Result lc lc' gl = ret lc'' ->
  wf_ECStack_head_tail maxb pinfo (los,nts) M lc (EC::ECs) ->
  wf_ECStack_head_tail maxb pinfo (los,nts) M lc' ECs ->
  wf_ECStack_head_tail maxb pinfo (los,nts) M' lc'' ECs.
Proof.
  intros.
  apply wf_ECStack_head_tail_cons__inv in H1.
  destruct H1 as [H11 H12].
  eapply free_allocas_preserves_wf_ECStack_head_tail' in H2; eauto.

  unfold Opsem.returnUpdateLocals in H0.
  inv_mbind.
  destruct_cmd c'; tinv H3.
  destruct n.
    inv H3; auto.

    inv_mbind.
    apply updateAddAL__wf_ECStack_head_tail; auto.
    intros. subst. symmetry in HeqR.
    unfold MDGVs.lift_op1, fit_gv in HeqR0. symmetry in HeqR0.
    inv_mbind.
    apply H12 in Hin; auto. clear H12.
    destruct ec0. simpl in *.
    eapply Hin in Hlkup; eauto. clear Hin.
    destruct Hlkup as [[mb [J1 J2]] [Hlkup _]]; subst.
    destruct_if.
      destruct Result; simpl in HeqR; eauto.
      inv Hwft.
      eapply const2GV_disjoint_with_runtime_alloca; eauto.
        omega.

      unfold gundef in *. inv_mbind. inv HeqR1.
      repeat rewrite simpl_blk2GV. simpl.
      split; auto using no_alias_with_blk__mc2undefs.
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
  (Hwfcfg : OpsemPP.wf_Config cfg)
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
  destruct Hwfcfg as [_ [_ [HwfSystem HmInS]]].
  destruct Hinv as
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]]
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [_ [_ [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC0 HwfCall]
       ]
       HwfCall'
     ]
    ]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0.
  destruct HwfS1 as
    [
      [[Hinscope1 Hwflc1] [[[Hinscope2 Hwflc2] [HwfECs Hfr2]] Hfr1]]
      [Hdisjals HwfM]
    ]. simpl. simpl in Hdisjals.
  fold wf_ECStack in HwfECs.
  assert (Hdisjals':=Hdisjals).
  destruct Hdisjals' as [Hdisjals' _].

  assert (wf_value S (module_intro los nts Ps) F Result RetTy) as Hwfv.
    get_wf_value_for_simop'; eauto.

  split.
  SCase "wf_ECStack".
    split.
    SSCase "wf_EC".
    split.
    SSSCase "sdom".

    destruct (fdef_dec (PI_f pinfo) F'); subst; auto.

    remember (getCmdID c') as R.
    destruct_cmd c'; try solve [inversion H].
    assert (In (insn_call i0 n c t0 v0 v p)
      (cs2'++[insn_call i0 n c t0 v0 v p] ++ cs')) as HinCs.
      apply in_or_app. right. simpl. auto.
    assert (Hwfc := HBinF2).
    eapply wf_system__wf_cmd with (c:=insn_call i0 n c t0 v0 v p) in Hwfc; eauto.
    assert (wf_fdef S (module_intro los nts Ps) (PI_f pinfo)) as HwfF.
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
      assert (~ In (getCmdLoc (insn_call i0 n c t0 v0 v p)) (getCmdsLocs cs2'))
        as Hnotin.
        eapply preservation_helper1; eauto.

      unfold Opsem.returnUpdateLocals in H1. simpl in H1.
      remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
      destruct R1; try solve [inv H1].
      destruct R.
      SSSSSCase "c' defines a variable".
        destruct n; inv HeqR.
        remember (MDGVs.lift_op1 (fit_gv (los, nts) t0) g t0) as R2.
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
      assert (NoDup (getCmdsLocs (cs2' ++ [insn_call i0 n c t0 v0 v p] ++ [c0] ++
        cs'))) as Hnodup.
        eapply preservation_helper2; eauto.

      unfold Opsem.returnUpdateLocals in H1. simpl in H1.
      remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
      destruct R1; try solve [inv H1].
      destruct R.
      SSSSSCase "c' defines a variable".
        destruct n; inv HeqR.
        remember (MDGVs.lift_op1 (fit_gv (los, nts) t0) g t0) as R2.
        destruct R2; inv H1.
        inv Hwfc.
        match goal with
        | H7: module_intro _ _ _ = module_intro _ _ _,
          H20: wf_insn_base _ _ _ |- _ => inv H7; inv H20
        end.
        apply wf_defs_updateAddAL; auto.
          split.
            eapply preservation_return_helper with (Result:=Result); eauto;
              simpl; auto.

            intro; subst.
            clear - HwfPI HBinF2 HuniqF.
            apply PhiInfo_must_be_promotable_alloca in HBinF2;
              try solve [auto | inv HBinF2 | intros; congruence].

      SSSSSCase "c' defines nothing".
        destruct n; inv HeqR. inv H1. auto.

      SSSCase "wflc".
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

Ltac simpl_ctx0 Hwfcfg Hinv HwfS1 :=
  destruct Hwfcfg as [_ [_ [HwfSystem HmInS]]];
  destruct Hinv as
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC0 HwfCall]
    ]]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0;
  destruct HwfS1 as
    [[[Hinscope1 Hwflc1] [HwfECs Hfr2]] [Hdisjals HwfM]].

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
  (Hwfcfg : OpsemPP.wf_Config cfg)
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
  simpl_ctx0 Hwfcfg Hinv HwfS1.
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
  lc (gv1 : GVsT DGVs) v los nts
  (Hget: Opsem.getOperandValue (los,nts) v lc gl = ret gv1)
  (tl : list Opsem.ExecutionContext) pinfo Mem
  (Hwfstk : wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc tl)
  (ec0 : Opsem.ExecutionContext) (Hin: In ec0 tl) (gvsa : GVsT DGVs)
  (Heq: Opsem.CurFunction ec0 = PI_f pinfo) S Ps F t
  (Hwft: wf_value S (module_intro los nts Ps) F v t)
  (Hlkup: lookupAL (GVsT DGVs) (Opsem.Locals ec0) (PI_id pinfo) = ret gvsa),
  no_alias gv1 gvsa.
Proof.
  intros.
  eapply operand__no_alias_with__tail in Hlkup; eauto.
Qed.

Lemma CAST__wf_GVs_in_ECs : forall (v : value) (id1 : id)
  gvs2 los nts gl EC Mem pinfo maxb castop0 t1 t2
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC))
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: Opsem.CurFunction EC = (PI_f pinfo) ->
         wf_use_at_head pinfo v)
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (H11 : Opsem.CAST (los,nts) (@Opsem.Locals DGVs EC) gl castop0 t1 v t2
           = ret gvs2) tl S F Ps
  (Hwft: wf_value S (module_intro los nts Ps) F v t1)
  (Hwfstk:
    wf_ECStack_head_tail maxb pinfo (los,nts) Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo (los,nts) Mem EC tl id1 gvs2.
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
      destruct H0 as [[_ [J1 [J2 J3]]] _]; eauto.
  split.
    intros. simpl in Hwfstk. apply Hwfstk in Hin.
    destruct ec0. simpl in *.
    eapply_clear Hin in Hlkup.
    destruct Hlkup as [_ [_ Hld]]; eauto.

    intros. subst.
    destruct HwfM as [J1 J2]; eauto.
Qed.

Lemma GEP__wf_GVs_in_ECs : forall (v : value) (v0 : value) (id1 : id)
  mp' los nts t gl EC Mem pinfo maxb (mp:GVsT DGVs) mps t'
  inbounds0 vidxs (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC))
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: PI_f pinfo = Opsem.CurFunction EC ->
         wf_use_at_head pinfo v)
  (H : Opsem.getOperandValue (los,nts) v (Opsem.Locals EC) gl = ret mps)
  (H0 : mp @ mps)(Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (H1 : Opsem.GEP (los,nts) t mp vidxs inbounds0 t' = ret mp') tl F S Ps
  (Hwft: wf_value S (module_intro los nts Ps) F v (typ_pointer t))
  (Hwfstk: wf_ECStack_head_tail maxb pinfo (los,nts) Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo (los,nts) Mem EC tl id1 mp'.
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

Lemma initLocals_preserves_wf_ECStack_head_tail: forall Mem (lc:DGVMap) maxb
  los nts ECs lc' gl (Hwflc1 : wf_lc Mem lc) pinfo gvs la lp EC
  (Hnouse:
    PI_f pinfo = Opsem.CurFunction EC ->
    List.fold_left
      (fun acc p => let '(_, v):=p in used_in_value (PI_id pinfo) v || acc)
      lp false = false)
  (Hwfg : wf_globals maxb gl)
  (H3 : Opsem.params2GVs (los,nts) lp lc gl = ret gvs)
  (H4 : Opsem.initLocals (los,nts) la gvs = ret lc')
  (Heq2 : lc = Opsem.Locals EC)
  (Hfr2 : wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc ECs) tavl Ps F S
  (Heq: lp = (List.map
    (fun p : typ * attributes * value =>
      let '(typ_', attributes_', value_'') := p in
     (( typ_' ,  attributes_' ),  value_'' )  ) tavl))
  (Hv: wf_value_list
      (List.map
        (fun p : typ * attributes * value =>
          let '(typ_', attributes_', value_'') := p in
            (S,(module_intro los nts Ps),F,value_'',typ_')) tavl))
  (Hscp: if fdef_dec (PI_f pinfo) (Opsem.CurFunction EC) then
           wf_defs maxb pinfo (los,nts) Mem (Opsem.Locals EC) (Opsem.Allocas EC)
         else True),
  wf_ECStack_head_tail maxb pinfo (los,nts) Mem lc' (EC :: ECs).
Proof.
  intros. unfold wf_ECStack_head_tail. intros ec0 Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; subst.
    unfold wf_ECStack_head_in_tail. destruct ec0. simpl in *.
    intros.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; try congruence.
    apply_clear Hscp in H0.
    destruct H0 as [[_ [[mb [J11 [J14 [J15 J16]]]] [J12 J13]]] J2]; subst.
    split; eauto.
    split; intros; eauto.
      eapply initializeFrameValues_preserves_no_alias in H4; eauto.
      eapply params2GVs_preserves_no_alias; eauto.
        omega.

        intros.
        apply J2 in H2. unfold wf_non_alloca_GVs in H2.
        destruct (id_dec id0 (PI_id pinfo)); subst; auto.
          contradict H1. simpl_env. eapply in_params__used; eauto.

        simpl_env. eauto.

    destruct ec0. simpl.
    intros gvsa Heq Hlkup.
    apply_clear Hfr2 in Hin. simpl in Hin. eapply_clear Hin in Hlkup.
    destruct Hlkup as [[mb [J11 J12]] [J2 J3]]; subst.
    split; eauto.
    split; auto.
      intros.
      eapply initializeFrameValues_preserves_no_alias in H4; eauto.
      eapply params2GVs_preserves_no_alias; eauto. omega.
        simpl_env. eauto.
Qed.

Lemma initLocals_preserves_wf_defs : forall fid fa rt la va lb gvs
  lc Mem TD pinfo maxb (Hwfpi: WF_PhiInfo pinfo)
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hinit : Opsem.initLocals TD la gvs = Some lc)
  (Heq: fdef_intro (fheader_intro fa rt fid la va) lb = PI_f pinfo),
  wf_defs maxb pinfo TD Mem lc nil.
Proof.
  intros. intros gvsa Hlkup.
  eapply OpsemProps.In_initLocals__In_getArgsIDs in Hinit; eauto.
  eapply IngetArgsIDs__lookupCmdViaIDFromFdef in Hinit; eauto.
  rewrite Heq in *.
  apply WF_PhiInfo_spec1 in Huniq; auto.
  rewrite Huniq in Hinit. congruence.
Qed.

Lemma params2GVs_preserves_wf_lc: forall maxb gl M
  (Hwfg : wf_globals maxb gl) los nts Ps lc (Hinbound: maxb < Mem.nextblock M)
  (Hwf : wf_lc M lc) S F tavl lp gvs
  (Heq: lp = (List.map
    (fun p : typ * attributes * value =>
      let '(typ_', attributes_', value_'') := p in
        (( typ_' ,  attributes_' ),  value_'' )  ) tavl))
  (Hv: wf_value_list
      (List.map
        (fun p : typ * attributes * value =>
          let '(typ_', attributes_', value_'') := p in
            (S,(module_intro los nts Ps),F,value_'',typ_')) tavl))
  (Hps2GVs : @Opsem.params2GVs DGVs (los,nts) lp lc gl = ret gvs),
  forall gv, In gv gvs -> valid_ptrs (Mem.nextblock M) gv.
Proof.
  induction tavl; simpl; intros; subst.
    inv Hps2GVs. inv H.

    simpl_prod. simpl in Hps2GVs. inv_mbind'.
    simpl in H.
    rewrite wf_value_list_cons_iff in Hv. destruct Hv.
    destruct H as [H | H]; subst.
      destruct v; simpl in HeqR; eauto.
        inv H1.
        eapply const2GV_valid_ptrs in HeqR; eauto.
        eapply valid_ptrs__trans; eauto. omega.

      eapply IHtavl; eauto. simpl_env. auto.
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
      inv_mbind'. symmetry in HeqR.
      destruct (id_dec i0 id0); subst.
        rewrite lookupAL_updateAddAL_eq in H. inv H.
        eapply undef__valid_lift_ptrs; eauto.

        rewrite <- lookupAL_updateAddAL_neq in H; auto.
        eapply IHla in HeqR; eauto.

      inv_mbind'. symmetry in HeqR.
      destruct (id_dec i0 id0); subst.
        rewrite lookupAL_updateAddAL_eq in H. inv H.
        unfold MDGVs.lift_op1, fit_gv in HeqR0.
        symmetry in HeqR0.
        inv_mbind.
        destruct_if.
          eapply Hwf; simpl; eauto.
          eapply undef_valid_ptrs; eauto.

        rewrite <- lookupAL_updateAddAL_neq in H; auto.
        eapply IHla in HeqR; eauto.
        intros. eapply Hwf; simpl; eauto.
Qed.

Lemma initLocals_preserves_wf_lc: forall Mem (lc:DGVMap) maxb los nts
  lc' gl (Hwflc1 : wf_lc Mem lc) gvs la lp
  (Hwfg : wf_globals maxb gl) (Hinbd: maxb < Mem.nextblock Mem)
  (H3 : Opsem.params2GVs (los,nts) lp lc gl = ret gvs)
  (H4 : Opsem.initLocals (los,nts) la gvs = ret lc') S Ps F tavl
  (Heq: lp = (List.map
    (fun p : typ * attributes * value =>
      let '(typ_', attributes_', value_'') := p in
        (( typ_' ,  attributes_' ),  value_'' )  ) tavl))
  (Hv: wf_value_list
    (List.map
      (fun p : typ * attributes * value =>
        let '(typ_', attributes_', value_'') := p in
         (S,(module_intro los nts Ps),F,value_'',typ_')) tavl))
  (Hfr2 : wf_lc Mem lc),
  wf_lc Mem lc'.
Proof.
  intros.
  eapply initializeFrameValues_preserves_wf_lc in H4; eauto.
  eapply params2GVs_preserves_wf_lc; eauto.
Qed.

Lemma mstore_preserves_alloca_size_prop: forall TD M M' mb pinfo al gv t gv0
  (Halc: alloca_size_prop TD pinfo M mb)
  (Hst: mstore TD M gv t gv0 al = Some M'),
  alloca_size_prop TD pinfo M' mb.
Proof.
  intros.
  unfold alloca_size_prop in *.
  erewrite bounds_mstore in Halc; eauto.
  inv_mbind. destruct Halc as [Halc1 Halc2].
  split; auto.
    eapply MemProps.mstore_preserves_range_perm; eauto.
Qed.

Lemma mstore_preserves_wf_defs_in_tail : forall maxb pinfo los nts M
  M' lc1 gl v als lc2 gvs1 gv1 t mp2 align mps2 vp S Ps F
  (Hwfvp: wf_value S (module_intro los nts Ps) F vp (typ_pointer t))
  (Hwfv: wf_value S (module_intro los nts Ps) F v t)
  (Hgetop': Opsem.getOperandValue (los,nts) vp lc1 gl = ret mps2)
  (Hgetop: Opsem.getOperandValue (los,nts) v lc1 gl = ret gvs1)
  (Hinp: mp2 @ mps2) (Hin: gv1 @ gvs1) (Hwfgl: wf_globals maxb gl)
  (Hst: mstore (los,nts) M mp2 t gv1 align = Some M') EC
  (Heq1: Opsem.CurFunction EC = PI_f pinfo)
  (Heq2: Opsem.Locals EC = lc2)
  (Hht: wf_ECStack_head_in_tail maxb pinfo (los,nts) M lc1 EC)
  (Hwf: wf_defs maxb pinfo (los,nts) M lc2 als),
  wf_defs maxb pinfo (los,nts) M' lc2 als.
Proof.
  intros. unfold wf_defs.
  intros gvsa Hlkp.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    clear J2.
    destruct J1 as [J5 [[mb [J11 [J12 [J13 J14]]]] [J4 [gv J3]]]]; subst.
    split.
      eapply mstore_preserves_encode_decode_ident in Hst; eauto.
      eapply operand__no_alias_with__tail with (v:=vp); eauto.
    split.
      erewrite <- nextblock_mstore; eauto.
      eapply mstore_preserves_alloca_size_prop in J14; eauto.
    split.
      intros.
      eapply mstore_preserves_mload_inv in Hst; eauto.
      destruct Hst as [gvs2 [H1 H2]].
      apply J4 in H1.
      eapply no_alias_overlap with (gvs1:=gv1); eauto.
      eapply operand__no_alias_with__tail; eauto.

      exists gv.
      eapply mstore_preserves_mload; eauto.
      eapply operand__no_alias_with__tail with (v:=vp); eauto.
Qed.

Definition wf_use_in_tail (pinfo:PhiInfo) (v:value) :=
used_in_value (PI_id pinfo) v = false.

Lemma mstore_preserves_wf_defs_at_head : forall maxb pinfo los nts M
  M' gl v als lc gvs1 gv1 t mp2 align mps2 vp S Ps (Hwfpi:WF_PhiInfo pinfo)
  (Huniq: uniqFdef (PI_f pinfo))
  (Hwfvp: wf_value S (module_intro los nts Ps) (PI_f pinfo) vp (typ_pointer t))
  (Hwfv: wf_value S (module_intro los nts Ps) (PI_f pinfo) v t)
  (Hgetop': Opsem.getOperandValue (los,nts) vp lc gl = ret mps2)
  (Hgetop: Opsem.getOperandValue (los,nts) v lc gl = ret gvs1)
  (Hinp: mp2 @ mps2) (Hin: gv1 @ gvs1) (Hwfgl: wf_globals maxb gl)
  (Hmatch: gv_chunks_match_typ (los,nts) gv1 t)
  (Hst: mstore (los,nts) M mp2 t gv1 align = Some M')
  (Hwfu: wf_use_at_head pinfo v)
  (Hwf: wf_defs maxb pinfo (los,nts) M lc als),
  wf_defs maxb pinfo (los,nts) M' lc als.
Proof.
  intros. unfold wf_defs.
  intros gvsa Hlkp.
  assert (no_alias gv1 gvsa) as J.
    eapply operand__no_alias_with__head with (mptrs:=gvs1); eauto.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    destruct J1 as [J5 [[mb [J11 [J12 [J13 J14]]]] [J4 [gv J3]]]]; subst.
    split.
      remember (used_in_value (PI_id pinfo) vp) as R.
      destruct R.
        destruct vp; tinv HeqR.
        simpl in Hgetop'.
        inv HeqR.
        destruct (id_dec id5 (PI_id pinfo)); tinv H0.
        subst.
        uniq_result.
        repeat rewrite simpl_blk2GV in Hst.
        unfold mstore in Hst.
        simpl in Hst.
        unfold encode_decode_ident.
        repeat rewrite simpl_blk2GV. simpl.
        apply mload_inv in J3.
        destruct J3 as [? [? [? [mc [J6 [J7 J8]]]]]].
        simpl in J7. rewrite J7.
        assert (Int.min_signed 31 <= 0 <= Int.max_signed 31) as Hinterval.
          apply min_le_zero_le_max.
        rewrite Int.signed_repr; auto.
        rewrite Int.signed_repr in Hst; auto.
        eapply promotable_mstore_aux_preserves_encode_decode_ident; eauto.
          inv Hwfvp.

          assert (G:=Huniq).
          apply WF_PhiInfo_spec1 in G; auto.
          eapply lookupInsnViaIDFromFdef__lookupTypViaIDFromFdef
            with (t0:=typ_pointer (PI_typ pinfo)) in G; eauto.
          uniq_result.
          unfold gv_chunks_match_typ in Hmatch.
          simpl in Hmatch. rewrite J7 in Hmatch.
          apply vm_matches_typ__eq__snd; auto.
        eapply mstore_preserves_encode_decode_ident in Hst; eauto.
          eapply operand__no_alias_with__head with (mptrs:=mps2)(v:=vp); eauto.
            unfold wf_use_at_head; auto.
    split.
      erewrite <- nextblock_mstore; eauto.
      eapply mstore_preserves_alloca_size_prop in J14; eauto.
    split.
      intros.
      eapply mstore_preserves_mload_inv in H; eauto.
      destruct H as [gvs2 [H1 H2]].
      apply J4 in H1.
      eapply no_alias_overlap with (gvs1:=gv1); eauto.

      eapply mstore_preserves_mload'; eauto.
Qed.

Lemma mstore_preserves_wf_ECStack_head_tail: forall maxb pinfo ECs los nts M
  gv1 align M' lc mp2 t gvs1 gl v1 (Hwfgl: wf_globals maxb gl) EC F S Ps
  (Hwfv: wf_value S (module_intro los nts Ps) F v1 t)
  (H0 : Opsem.getOperandValue (los,nts) v1 lc gl = Some gvs1)
  (H1 : gv1 @ gvs1)
  (Hst: mstore (los,nts) M mp2 t gv1 align = Some M') lc1
  (Heq: lc1 = Opsem.Locals EC)
  (Hht: wf_ECStack_head_tail maxb pinfo (los,nts) M lc (EC::ECs))
  (Hwf: wf_ECStack_head_tail maxb pinfo (los,nts) M lc1 ECs),
  wf_ECStack_head_tail maxb pinfo (los,nts) M' lc1 ECs.
Proof.
  intros.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros.
  assert (wf_ECStack_head_in_tail maxb pinfo (los,nts) M lc ec0) as Hintl.
    apply Hht. simpl; auto.
  destruct ec0. intros.
  assert (no_alias gv1 gvsa) as J.
    eapply operand__no_alias_with__tail with(M:=M)(lc1:=lc); eauto; simpl; auto.
  apply_clear Hwf in H. simpl in H. eapply_clear H in H3.
  destruct H3 as [[mb [J11 [J12 J13]]] [J2 J3]]; subst.
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

Lemma mstore_preserves_wf_ECStack_in_tail : forall maxb pinfo los nts M mp2 t
  align M' gl vp (Hwfgl: wf_globals maxb gl) lc gvs1 gv1 v1
  (Hwfpi: WF_PhiInfo pinfo)
  mps2 (Hgetop': Opsem.getOperandValue (los,nts) vp lc gl = ret mps2)
  (H0 : Opsem.getOperandValue (los,nts) v1 lc gl = Some gvs1) S Ps F
  (Hwfvp: wf_value S (module_intro los nts Ps) F vp (typ_pointer t))
  (Hwfv: wf_value S (module_intro los nts Ps) F v1 t)
  (Hinp: mp2 @ mps2) (H1 : gv1 @ gvs1)
  (Hst: mstore (los,nts) M mp2 t gv1 align = Some M') ECs
  (Hht: wf_ECStack_head_tail maxb pinfo (los,nts) M lc ECs)
  (Hwf: wf_ECStack maxb pinfo (los,nts) M ECs),
  wf_ECStack maxb pinfo (los,nts) M' ECs.
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

Lemma mstore_preserves_wf_Mem : forall maxb los nts M mp2 t gv1 align M' gvs1 gl
  (Hwfgl: wf_globals maxb gl) (lc:DGVMap) v1 (Hwflc: wf_lc M lc) S F Ps
  (Hwfv: wf_value S (module_intro los nts Ps) F v1 t)
  (H0 : Opsem.getOperandValue (los,nts) v1 lc gl = Some gvs1)
  (H1 : gv1 @ gvs1)
  (Hst: mstore (los,nts) M mp2 t gv1 align = Some M')
  (Hwf: wf_Mem maxb (los,nts) M),
  wf_Mem maxb (los,nts) M'.
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

Lemma mstore_preserves_wf_ECStack_head_tail': forall maxb pinfo ECs los nts M
  gv1 align M' lc mp2 t gvs1 gl v1 (Hwfgl: wf_globals maxb gl)
  (H0 : Opsem.getOperandValue (los,nts) v1 lc gl = Some gvs1) S F Ps
  (Hwfv: wf_value S (module_intro los nts Ps) F v1 t)
  (H1 : gv1 @ gvs1)
  (Hst: mstore (los,nts) M mp2 t gv1 align = Some M')
  (Hwf: wf_ECStack_head_tail maxb pinfo (los,nts) M lc ECs),
  wf_ECStack_head_tail maxb pinfo (los,nts) M' lc ECs.
Proof.
  intros.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros. destruct ec0. intros.
  assert (no_alias gv1 gvsa) as J.
    eapply operand__no_alias_with__tail with (M:=M); eauto; simpl; auto.
  eapply_clear Hwf in H. simpl in H. eapply_clear H in H3.
  destruct H3 as [[mb [J11 [J12 J13]]] [J2 J3]]; subst.
  split.
    erewrite <- nextblock_mstore; eauto.
  split; auto.
    intros.
    eapply mstore_preserves_mload_inv in Hst; eauto.
    destruct Hst as [gvs2 [H3 H2]].
    apply J3 in H3.
    eapply no_alias_overlap with (gvs1:=gv1); eauto.
Qed.

Lemma malloc_preserves_alloca_size_prop: forall TD M tsz gn align0 M' mb' pinfo
  mb (Hmlc: malloc TD M tsz gn align0 = ret (M', mb)) maxb
  (J12: maxb < mb' < Mem.nextblock M) (J13: alloca_size_prop TD pinfo M mb'),
  alloca_size_prop TD pinfo M' mb'.
Proof.
  intros.
  erewrite <- malloc_result in J12; eauto.
  unfold alloca_size_prop in *.
  inv_mbind. destruct J13 as [J1 J2].
  eapply MemProps.malloc_preserves_range_perm in J2; eauto.
  apply bounds_malloc in Hmlc.
  destruct Hmlc as [n [Hmlc1 Hmlc2]].
  rewrite Hmlc2.
  destruct (eq_block mb' mb); subst; auto.
    contradict J12. omega.
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
  destruct H1 as [[mb' [J11 [J12 J13]]] [J2 J3]]; subst; eauto.
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
      clear - J13.
      intro J. subst. omega.

      rewrite <- lookupAL_updateAddAL_neq in H; eauto.

    intros.
    eapply malloc_preserves_mload_inv in Hmlc; eauto.
    destruct Hmlc as [[G _]| [G _]]; subst; eauto.
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
    destruct J1 as [J5 [[mb' [J11 [J12 [J13 J14]]]] [J4 [gv J3]]]]; subst.
    assert (maxb < mb' < Mem.nextblock M') as W.
      erewrite <- nextblock_malloc; eauto. omega.
    assert (alloca_size_prop TD pinfo M' mb') as W'.
      eapply malloc_preserves_alloca_size_prop; eauto.
    split.
      eapply malloc_preserves_encode_decode_ident; eauto. omega.
    split; eauto.
    split.
      intros.
      eapply malloc_preserves_mload_inv in H0; eauto.
      destruct H0 as [[G _] | [G _]]; subst; eauto.
        eapply undefs_disjoint_with_ptr; eauto.

      exists gv. eapply malloc_preserves_mload; eauto.
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
  destruct H1 as [[mb' [J11 [J12 J13]]] [J2 J3]]; subst; eauto.
  assert (maxb < mb' < Mem.nextblock M') as W.
    erewrite <- nextblock_malloc; eauto. omega.
  split; eauto.
  split; eauto.
    intros.
    eapply malloc_preserves_mload_inv in Hmlc; eauto.
    destruct Hmlc as [[G _]| [G _]]; subst; eauto.
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
  als als' tmn cs c0 l1 ps1 cs1' S
  (Heq: B = (l1, stmts_intro ps1 (cs1' ++ c0 :: cs) tmn))
  (HwfS: wf_system S) los nts (Heq': TD = (los, nts)) Ps
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

Lemma palloca__alloca_size_prop: forall (pinfo : PhiInfo) (los : layouts)
  (nts : namedts) (M : mem) (M' : mem) (t : typ) (mb : mblock) (align0 : align)
  (gn : GenericValue) (tsz : sz)
  (Hal : malloc (los, nts) M tsz gn align0 = ret (M', mb))
  (Hsize : getTypeAllocSize (los, nts) t = ret tsz)
  (Heq : t = PI_typ pinfo),
  alloca_size_prop (los, nts) pinfo M' mb.
Proof.
  intros.
  unfold alloca_size_prop.
  rewrite Heq in Hsize; auto.
  rewrite Hsize.
  assert (Hal':=Hal).
  apply bounds_malloc in Hal'.
  destruct Hal' as [n [Hal1 Hal2]].
  rewrite Hal2.
  destruct (eq_block mb mb); try congruence.
  split.
    intros lo hi EQ. inv EQ.
    split; auto.
      apply malloc_inv in Hal.
      destruct Hal as [n' [J1 [J2 J3]]].
      uniq_result.
      apply MemProps.z_mult_n__ge__z; auto.
    eapply MemProps.malloc_preserves_range_perm_2; eauto.
Qed.

Lemma alloca_preserves_wf_defs_at_head : forall maxb pinfo los nts M
  M' gl als lc t
  (Hwfpi : WF_PhiInfo pinfo) S Ps
  (HwfF: wf_fdef S (module_intro los nts Ps) (PI_f pinfo))
  (Hwfgl: wf_globals maxb gl) mb id0 align0 F gn tsz
  (Hal: malloc (los, nts) M tsz gn align0 = ret (M', mb))
  (HwfM: wf_Mem maxb (los, nts) M)
  (Hwflc : wf_lc M lc) (Hsize: getTypeAllocSize (los, nts) t = ret tsz)
  (Heq: id0 = PI_id pinfo -> t = PI_typ pinfo),
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
    assert (exists mc, flatten_typ (los, nts) (PI_typ pinfo) = Some mc)
      as G.
      eapply WF_PhiInfo_spec2; eauto.
    destruct G as [mc G].
    split.
      split.
        rewrite simpl_blk2GV. unfold encode_decode_ident.
        rewrite G.
        assert (Int.min_signed 31 <= 0 <= Int.max_signed 31) as Hinterval.
          apply min_le_zero_le_max.
        simpl. rewrite Int.signed_repr; auto.
        apply malloc_inv in Hal.
        destruct Hal as [n [J1 [J2 J3]]].
        assert (update (Mem.nextblock M)
                       (fun ofs => Undef)
                       (Mem.mem_contents M) = (Mem.mem_contents M')) as Hup.
          eapply Mem.alloc_mem_contents; eauto.
        apply Mem.alloc_result in J3. subst.
        clear - Hup.
        apply promotable_alloc_encode_decode_ident_aux; auto.

      split.
        exists mb.
        rewrite simpl_blk2GV. rewrite simpl_blk2GV.
        split; auto. simpl.
        split; auto.
        split.
          erewrite <- nextblock_malloc; eauto.
          apply malloc_result in Hal. subst.
          destruct HwfM. omega.

          eapply palloca__alloca_size_prop; eauto.
      split.
        intros.
        assert (J:=Hal).
        eapply malloc_preserves_mload_inv in J; eauto.
        destruct J as [[J _]| [J _]].
          destruct HwfM as [HwfM _].
          apply HwfM in J.
          eapply valid_ptrs__no_alias__fresh_ptr; eauto.
          apply malloc_result in Hal. subst. omega.

          eapply undefs_disjoint_with_ptr; eauto.

        rewrite simpl_blk2GV.
        unfold mload. rewrite G. simpl.
        rewrite <- Heq in G; auto.
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
      destruct J1 as [J6 [[mb' [J31 [J32 [J33 J34]]]] [J4 [gv J5]]]]; subst.
      split.
        eapply malloc_preserves_encode_decode_ident; eauto. omega.
      split.
        exists mb'.
        split; auto. simpl.
        split; auto.
        split.
          erewrite <- nextblock_malloc; eauto.
          omega.

          eapply malloc_preserves_alloca_size_prop; eauto.
      split.
        intros.
        assert (J:=Hal).
        eapply malloc_preserves_mload_inv in J; eauto.
        destruct J as [[J _]| [J _]]; eauto.
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
      destruct J1 as [J6 [[mb' [J31 [J32 [J33 J34]]]] [J4 [gv J5]]]]; subst.
      split.
        eapply malloc_preserves_encode_decode_ident; eauto. omega.
      split.
        erewrite <- nextblock_malloc; eauto.
        eapply malloc_preserves_alloca_size_prop in Hal; eauto.
        exists mb'. split; auto. split; auto. split; auto. omega.

      split.
        intros.
        assert (J:=Hal).
        eapply malloc_preserves_mload_inv in J; eauto.
        destruct J as [[J _]|[J _]]; eauto.
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

Ltac simpl_ctx Hwfcfg Hinv HwfS1 :=
  destruct Hwfcfg as [_ [Hwfgl0 [HwfSystem HmInS]]];
  destruct Hinv as
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [_ [l1 [ps1 [cs1' Heq1]]]]]]]]
     [HwfEC0 HwfCall]
    ]]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0;
  destruct HwfS1 as [[HwfEC [HwfECs Hwfht]] [Hnonup1 HwfM1]].

Ltac simpl_ctx' Hwfcfg Hinv HwfS1 :=
  destruct Hwfcfg as [_ [_ [HwfSystem HmInS]]];
  destruct Hinv as
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]]
     [HwfEC0 HwfCall]
    ]]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0;
  destruct HwfS1 as [[[_ Hwflc] [HwfECs Hwfht]] [Hnonup1 [_ HwfM]]].

Ltac preservation_tac4 :=
  match goal with
  | HwfPI : WF_PhiInfo _,
    HFinPs1: InProductsB _ _ = _,
    HBinF1: blockInFdefB _ _ = _,
    HmInS: moduleInSystemB _ _ = _,
    HwfSystem: wf_system _ |- _ =>
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
  (EC : list Opsem.ExecutionContext) (Mem : mem) (als : list mblock)
  rt1 va1 ECs cfg S los nts Ps gl fs
  (EQ1 : cfg = OpsemAux.mkCfg S (los, nts) Ps gl fs)
  (EQ2 : ECs = {| Opsem.CurFunction := F;
                 Opsem.CurBB := B;
                 Opsem.CurCmds := insn_call rid noret0 ca rt1 va1 fv lp :: cs;
                 Opsem.Terminator := tmn;
                 Opsem.Locals := lc;
                 Opsem.Allocas := als |} :: EC)
  (Hwfcfg : OpsemPP.wf_Config cfg)
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
        ret (l', stmts_intro ps' cs' tmn'))
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
                  Opsem.CurBB := (l', stmts_intro ps' cs' tmn');
                  Opsem.CurCmds := cs';
                  Opsem.Terminator := tmn';
                  Opsem.Locals := lc';
                  Opsem.Allocas := nil |}
                  :: ECs;
     Opsem.Mem := Mem |}.
Proof.
  intros. subst.
  simpl_ctx0 Hwfcfg Hinv HwfS1.
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
    assert (wf_fdef S (module_intro los nts Ps)
      (fdef_intro (fheader_intro fa rt fid la va) lb)) as HwfF.
      eapply wf_system__wf_fdef; eauto.
    split.
      destruct (fdef_dec (PI_f pinfo)
                 (fdef_intro (fheader_intro fa rt fid la va) lb)); auto.
      assert (ps'=nil) as EQ.
        eapply entryBlock_has_no_phinodes with (s:=S); eauto.
      subst.
      apply AlgDom.dom_entrypoint in H2.
      eapply initLocals_preserves_wf_defs; eauto.

      destruct HwfM.
      eapply wf_system__wf_cmd in HBinF1; eauto using in_middle.
      inv HBinF1.
      find_wf_value_list. eapply initLocals_preserves_wf_lc; eauto.

  split.
    repeat (split; auto).
    assert(PI_f pinfo = F ->
           fold_left
             (fun (acc : bool) (p : typ * attributes * value) =>
              let '(_, v) := p in used_in_value (PI_id pinfo) v || acc) lp false
              = false) as J.
      preservation_tac4.
    eapply wf_system__wf_cmd in HBinF1; eauto using in_middle.
    inv HBinF1. find_wf_value_list.
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
  (Hwfcfg : OpsemPP.wf_Config cfg)
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
  destruct Hwfcfg as [_ [_ [HwfSystem HmInS]]].
  destruct Hinv as
    [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]]
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [_ [_ [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC0 HwfCall]
       ]
       HwfCall'
     ]
    ]]; subst.
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
      destruct_cmd c'; try solve [inversion H].
      assert (In (insn_call i0 n c t0 v0 v p)
        (cs2'++[insn_call i0 n c t0 v0 v p] ++ cs')) as HinCs.
        apply in_or_app. right. simpl. auto.
      assert (Hwfc := HBinF2).
      eapply wf_system__wf_cmd with (c:=insn_call i0 n c t0 v0 v p) in Hwfc; eauto.
      assert (wf_fdef S (module_intro los nts Ps) (PI_f pinfo)) as HwfF.
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

Lemma wf_defs_br : forall lc l' ps' cs' lc' tmn' gl los nts Ps s
  (l3 : l) (ps : phinodes) (cs : list cmd) tmn pinfo (Hwfpi: WF_PhiInfo pinfo)
  (Hlkup : Some (stmts_intro ps' cs' tmn') =
             lookupBlockViaLabelFromFdef (PI_f pinfo) l')
  (Hwfps: wf_phinodes s (module_intro los nts Ps) (PI_f pinfo)
            (l', stmts_intro ps' cs' tmn') ps')
  (Hswitch : Opsem.switchToNewBasicBlock (los,nts) (l', stmts_intro ps' cs' tmn')
         (l3, stmts_intro ps cs tmn) gl lc = ret lc')
  als Mem maxb
  (Hwfdfs : wf_defs maxb pinfo (los,nts) Mem lc als)
  (Hwflc : wf_lc Mem lc)
  (Hwfg : wf_globals maxb gl)
  (HwfF : wf_fdef s (module_intro los nts Ps) (PI_f pinfo))
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
      eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec9 in HeqR;
        eauto.
      destruct HeqR as [id1 [t1 [vls1 [v [n [J4 [J5 J6]]]]]]].
      unfold wf_non_alloca_GVs.
      destruct (id_dec id0 (PI_id pinfo)); auto.
      eapply wf_phinodes__nth_list_value_l__wf_value in Hwfps; eauto.
      eapply operand__no_alias_with__head; eauto.
        symmetry in Hlkup.
        apply lookupBlockViaLabelFromFdef_inv in Hlkup; auto.
        assert (phinodeInFdefBlockB (insn_phi id1 t1 vls1) (PI_f pinfo)
          (l', stmts_intro ps' cs' tmn') = true) as Hin'.
          apply andb_true_iff.
          split; auto.
          simpl.
          apply In_InPhiNodesB; auto.
        apply WF_PhiInfo_spec5 in Hin'; auto.
        eapply unused_in_phi__wf_use_at_head in Hin'; eauto.

      apply OpsemProps.updateValuesForNewBlock_spec7 in Hlk0; auto.
Qed.

Lemma wf_ECStack_head_tail_br : forall (lc:DGVMap) l' ps' cs' lc' tmn' gl los
  nts Ps s (l3 : l) (ps : phinodes) (cs : list cmd) tmn F
  (Hlkup : Some (stmts_intro ps' cs' tmn') =
             lookupBlockViaLabelFromFdef F l')
  (Hswitch : Opsem.switchToNewBasicBlock (los,nts) (l', stmts_intro ps' cs' tmn')
         (l3, stmts_intro ps cs tmn) gl lc = ret lc') EC pinfo
  Mem maxb (Hwflc : wf_ECStack_head_tail maxb pinfo (los, nts) Mem lc EC)
  (HwfM : wf_Mem maxb (los, nts) Mem)
  (Hwfg : wf_globals maxb gl)
  (HwfF : wf_fdef s (module_intro los nts Ps) F)
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
      eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec9 in HeqR;
        eauto.
      destruct HeqR as [id2 [t1 [vls1 [v [n [J4 [J5 J6]]]]]]].
      eapply wf_fdef__wf_phinodes' in Hlkup; eauto.
      eapply wf_phinodes__nth_list_value_l__wf_value in Hlkup; eauto.
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

Lemma wf_lc_br : forall (lc:DGVMap) l' ps' cs' lc' tmn' gl td
  (l3 : l) (ps : phinodes) (cs : list cmd) tmn s F los nts Ps
  (Hwfps: wf_phinodes s (module_intro los nts Ps) F
            (l', stmts_intro ps' cs' tmn') ps')
  (Hlkup : Some (stmts_intro ps' cs' tmn') =
             lookupBlockViaLabelFromFdef F l')
  (Hswitch : Opsem.switchToNewBasicBlock (los,nts)
         (l', stmts_intro ps' cs' tmn')
         (l3, stmts_intro ps cs tmn) gl lc = ret lc')
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
      eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec9 in HeqR;
        eauto.
      destruct HeqR as [id1 [t1 [vls1 [v [n [J4 [J5 J6]]]]]]].
      destruct HwfM.
      eapply wf_phinodes__nth_list_value_l__wf_value in Hwfps; eauto.
      eapply operand__lt_nextblock; eauto.

      apply (@OpsemProps.updateValuesForNewBlock_spec7 DGVs) in Hlkup'; auto.
      apply Hwflc in Hlkup'; auto.
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
  (Hwfcfg : OpsemPP.wf_Config cfg)
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
  (c : GenericValue) (ps' : phinodes) (cs' : cmds) (tmn' : terminator)
  (lc' : Opsem.GVsMap)
  (H : Opsem.getOperandValue (los, nts) Cond lc gl = ret conds)
  (H0 : c @ conds)
  (H1 : ret stmts_intro ps' cs' tmn' =
       (if isGVZero (los, nts) c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1))
  (H2 : Opsem.switchToNewBasicBlock (los, nts) 
         (if isGVZero (los, nts) c then l2 else l1, 
          stmts_intro ps' cs' tmn') B
         gl lc = ret lc')
  (HwfS1 : wf_State maxb pinfo cfg
            {| Opsem.ECS := ECs; Opsem.Mem := Mem |}),
  wf_State maxb pinfo cfg
     {|
     Opsem.ECS := {|
                  Opsem.CurFunction := F;
                  Opsem.CurBB := (if isGVZero (los, nts) c then l2 else l1,
                                  stmts_intro ps' cs' tmn');
                  Opsem.CurCmds := cs';
                  Opsem.Terminator := tmn';
                  Opsem.Locals := lc';
                  Opsem.Allocas := als |} :: EC;
     Opsem.Mem := Mem |}.
Proof.
  intros. subst.
  simpl_ctx0 Hwfcfg Hinv HwfS1.
  simpl. simpl in Hdisjals.
  fold wf_ECStack in HwfECs.
  assert (Hdisjals':=Hdisjals).
  destruct Hdisjals' as [Hdisjals' _].
  assert (HwfF := HwfSystem).
  eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  assert (ret stmts_intro ps' cs' tmn' =
    lookupBlockViaLabelFromFdef F (if isGVZero (los, nts) c then l2 else l1)) 
    as Hlkup.
    symmetry.
    apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
    symmetry in H1.
    destruct (isGVZero (los, nts) c);
      apply lookupBlockViaLabelFromFdef_inv in H1; auto.
  split; auto.
  split.
  SCase "wf_ECStack".
    split.
      SSCase "sdom".
      destruct (fdef_dec (PI_f pinfo) F); subst; auto.
        eapply wf_defs_br; eauto using wf_fdef__wf_phinodes'.
      SSCase "wf_lc".
      eapply wf_lc_br; eauto using wf_fdef__wf_phinodes'.
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
  (Hwfcfg : OpsemPP.wf_Config cfg)
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
  (ps' : phinodes) (cs' : cmds) (tmn' : terminator)
  (lc' : Opsem.GVsMap)
  (H1 : ret stmts_intro ps' cs' tmn' = lookupBlockViaLabelFromFdef F l0)
  (H2 : Opsem.switchToNewBasicBlock (los, nts) (l0, stmts_intro ps' cs' tmn') B
         gl lc = ret lc')
  (HwfS1 : wf_State maxb pinfo cfg
            {| Opsem.ECS := ECs; Opsem.Mem := Mem |}),
  wf_State maxb pinfo cfg
     {|
     Opsem.ECS := {|
                  Opsem.CurFunction := F;
                  Opsem.CurBB := (l0, stmts_intro ps' cs' tmn');
                  Opsem.CurCmds := cs';
                  Opsem.Terminator := tmn';
                  Opsem.Locals := lc';
                  Opsem.Allocas := als |} :: EC;
     Opsem.Mem := Mem |}.
Proof.
  intros. subst.
  simpl_ctx0 Hwfcfg Hinv HwfS1.
  simpl. simpl in Hdisjals.
  fold wf_ECStack in HwfECs.
  assert (Hdisjals':=Hdisjals).
  destruct Hdisjals' as [Hdisjals' _].
  assert (HwfF := HwfSystem).
  eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
  assert (HuniqF := HwfSystem).
  eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
  split; auto.
  split.
  SCase "wf_ECStack".
    split.
      SSCase "sdom".
      destruct (fdef_dec (PI_f pinfo) F); subst; auto.
        eapply wf_defs_br; eauto using wf_fdef__wf_phinodes'.
      SSCase "wf_lc".
      eapply wf_lc_br; eauto using wf_fdef__wf_phinodes'.
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
  gvs2 los nts gl EC Mem pinfo maxb t t'
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC))
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: Opsem.CurFunction EC = (PI_f pinfo) -> wf_use_at_head pinfo v)
  (Hwfv': Opsem.CurFunction EC = (PI_f pinfo) -> wf_use_at_head pinfo v')
  gvs gvs' S Ps F
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (Hwft: wf_value S (module_intro los nts Ps) F v t)
  (Hwft': wf_value S (module_intro los nts Ps) F v' t')
  (H : Opsem.getOperandValue (los,nts) v (Opsem.Locals EC) gl = ret gvs)
  (H' : Opsem.getOperandValue (los,nts) v' (Opsem.Locals EC) gl = ret gvs') idxs
  (H11 : ret gvs2 = Opsem.insertGenericValue (los,nts) t gvs idxs t' gvs') tl
  (Hwfstk:
    wf_ECStack_head_tail maxb pinfo (los,nts) Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo (los,nts) Mem EC tl id1 gvs2.
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
  gvs2 los nts gl EC Mem pinfo maxb t S F Ps
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC))
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: Opsem.CurFunction EC = (PI_f pinfo) ->
         wf_use_at_head pinfo v) gvs1
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (Hwft: wf_value S (module_intro los nts Ps) F v t)
  (H : Opsem.getOperandValue (los,nts) v (Opsem.Locals EC) gl = ret gvs1) idxs
  (H11 : ret gvs2 = Opsem.extractGenericValue (los,nts) t gvs1 idxs) tl
  (Hwfstk:
    wf_ECStack_head_tail maxb pinfo (los,nts) Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo (los,nts) Mem EC tl id1 gvs2.
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

Lemma EXT__wf_GVs_in_ECs : forall (id1 : id) gvs2 los nts gl EC Mem pinfo maxb
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) v1 S F Ps
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: Opsem.CurFunction EC = (PI_f pinfo) ->
         wf_use_at_head pinfo v1) eop0 t1 t2
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (Hwft: wf_value S (module_intro los nts Ps) F v1 t1)
  (H11 : Opsem.EXT (los,nts) (Opsem.Locals EC) gl eop0 t1 v1 t2 = ret gvs2) tl
  (Hwfstk:
    wf_ECStack_head_tail maxb pinfo (los,nts) Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo (los,nts) Mem EC tl id1 gvs2.
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

Lemma TRUNC__wf_GVs_in_ECs : forall (id1 : id) gvs2 los nts gl EC Mem pinfo maxb
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) v1 S Ps F
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: Opsem.CurFunction EC = (PI_f pinfo) ->
         wf_use_at_head pinfo v1) top0 t1 t2
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (Hwft: wf_value S (module_intro los nts Ps) F v1 t1)
  (H11 : Opsem.TRUNC (los,nts) (Opsem.Locals EC) gl top0 t1 v1 t2 = ret gvs2) tl
  (Hwfstk:
    wf_ECStack_head_tail maxb pinfo (los,nts) Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo (los,nts) Mem EC tl id1 gvs2.
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

Lemma ICMP__wf_GVs_in_ECs : forall (id1 : id) gvs2 los nts gl EC Mem pinfo maxb
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) v1 v2 S F Ps
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv1: Opsem.CurFunction EC = (PI_f pinfo) -> wf_use_at_head pinfo v1)
  (Hwfv2: Opsem.CurFunction EC = (PI_f pinfo) -> wf_use_at_head pinfo v2)
  cond0 t
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (Hwft1: wf_value S (module_intro los nts Ps) F v1 t)
  (Hwft2: wf_value S (module_intro los nts Ps) F v2 t)
  (H11 : Opsem.ICMP (los,nts) (Opsem.Locals EC) gl cond0 t v1 v2 = ret gvs2) tl
  (Hwfstk:
    wf_ECStack_head_tail maxb pinfo (los,nts) Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo (los,nts) Mem EC tl id1 gvs2.
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

Lemma FCMP__wf_GVs_in_ECs : forall (id1 : id) gvs2 los nts gl EC Mem pinfo maxb
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) v1 v2 S Ps F
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv1: Opsem.CurFunction EC = (PI_f pinfo) -> wf_use_at_head pinfo v1)
  (Hwfv2: Opsem.CurFunction EC = (PI_f pinfo) -> wf_use_at_head pinfo v2)
  fcond0 fp
  (Hwft1: wf_value S (module_intro los nts Ps) F v1 (typ_floatpoint fp))
  (Hwft2: wf_value S (module_intro los nts Ps) F v2 (typ_floatpoint fp))
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (H11 : Opsem.FCMP (los,nts) (Opsem.Locals EC) gl fcond0 fp v1 v2 = ret gvs2) tl
  (Hwfstk:
    wf_ECStack_head_tail maxb pinfo (los,nts) Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo (los,nts) Mem EC tl id1 gvs2.
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
  los nts gl EC Mem pinfo maxb S Ps F t
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC))
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: Opsem.CurFunction EC = (PI_f pinfo) ->
         wf_use_at_head pinfo v) gvs
  (Hneq: PI_f pinfo = Opsem.CurFunction EC -> id1 <> PI_id pinfo)
  (Hwft1: wf_value S (module_intro los nts Ps) F v t)
  (H : Opsem.getOperandValue (los,nts) v (Opsem.Locals EC) gl = ret gvs) tl
  (Hwfstk:
    wf_ECStack_head_tail maxb pinfo (los,nts) Mem (Opsem.Locals EC) tl),
  wf_GVs_in_ECs maxb pinfo (los,nts) Mem EC tl id1 gvs.
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

Axiom callExternalProc_preserves_wf_ECStack_head_tail : forall maxb pinfo
  ECs TD M M' (lc:DGVMap) gvs gvss fid oresult gl lp dck tret targs tr
  (Hwflc: wf_lc M lc) (Hwfgl: wf_globals maxb gl)
  (H3 : gvs @@ gvss),
  Opsem.params2GVs TD lp lc gl = ret gvss ->
  callExternalOrIntrinsics TD gl M fid tret targs dck gvs =
    ret (oresult, tr, M') ->
  wf_ECStack_head_tail maxb pinfo TD M lc ECs ->
  wf_ECStack_head_tail maxb pinfo TD M' lc ECs.

Axiom callExternalFunction_preserves_wf_ECStack : forall maxb pinfo ECs TD M
  M' gvs fid oresult dck tret targs tr gl,
  callExternalOrIntrinsics TD gl M fid tret targs dck gvs =
    ret (oresult, tr, M') ->
  wf_ECStack maxb pinfo TD M ECs ->
  wf_ECStack maxb pinfo TD M' ECs.

Axiom callExternalProc_preserves_wf_EC : forall maxb pinfo TD M M' rid
  als F B cs tmn gl gvss gvs fid oresult lp (lc:DGVMap) fv rt1 va1 ca dck
  (Hwflc: wf_lc M lc) (Hwfgl: wf_globals maxb gl) (H3 : gvs @@ gvss)
  (J1: Opsem.params2GVs TD lp lc gl = ret gvss) tret targs tr
  (J3: callExternalOrIntrinsics TD gl M fid tret targs dck gvs =
    ret (oresult, tr, M'))
  (HwfEC: wf_ExecutionContext maxb pinfo TD M
            {| Opsem.CurFunction := F;
               Opsem.CurBB := B;
               Opsem.CurCmds := insn_call rid true ca rt1 va1 fv lp :: cs;
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
  oresult dck gl tret targs tr,
  callExternalOrIntrinsics TD gl M fid tret targs dck gvs =
    ret (oresult, tr, M') ->
  wf_Mem maxb TD M ->
  wf_Mem maxb TD M'.

Axiom callExternalFunction_preserves_wf_als : forall TD M gvs M' maxb als fid
  oresult dck gl tret targs tr
  (Hexcall: callExternalOrIntrinsics TD gl M fid tret targs dck gvs =
    ret (oresult, tr, M'))
  (Hwf: wf_als maxb M als),
  wf_als maxb M' als.

Axiom callExternalFun_preserves_wf_ECStack_head_tail : forall maxb pinfo
  ECs TD M M' (lc:DGVMap) gvs gvss fid result gl lp g0 rid ft dck
  (Hwflc: wf_lc M lc) (Hwfgl: wf_globals maxb gl) (H3 : gvs @@ gvss)
  (HeqR : ret g0 = fit_gv TD ft result) tret targs tr,
  Opsem.params2GVs TD lp lc gl = ret gvss ->
  callExternalOrIntrinsics TD gl M fid tret targs dck gvs =
    ret (Some result, tr, M') ->
  wf_ECStack_head_tail maxb pinfo TD M lc ECs ->
  wf_ECStack_head_tail maxb pinfo TD M'
    (updateAddAL (GVsT DGVs) lc rid ($ g0 # ft $)) ECs.

Axiom callExternalFun_preserves_wf_EC : forall maxb pinfo TD M M' rid
  als F B cs tmn gl gvss gvs fid result lp (lc:DGVMap) fv rt1 va1 ca g0 dck
  (Hwflc: wf_lc M lc) (Hwfgl: wf_globals maxb gl) (H3 : gvs @@ gvss)
  (J1: Opsem.params2GVs TD lp lc gl = ret gvss) tret targs tr
  (J3: callExternalOrIntrinsics TD gl M fid tret targs dck gvs =
    ret (Some result, tr, M'))
  (HeqR : ret g0 = fit_gv TD rt1 result)
  (HwfEC: wf_ExecutionContext maxb pinfo TD M
            {| Opsem.CurFunction := F;
               Opsem.CurBB := B;
               Opsem.CurCmds := insn_call rid false ca rt1 va1 fv lp :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
  wf_ExecutionContext maxb pinfo TD M'
   {| Opsem.CurFunction := F;
      Opsem.CurBB := B;
      Opsem.CurCmds := cs;
      Opsem.Terminator := tmn;
      Opsem.Locals := (updateAddAL (GVsT DGVs) lc rid ($ g0 # rt1 $));
      Opsem.Allocas := als |}.

Ltac preservation_tac0:=
  match goal with
  | HwfPI : WF_PhiInfo _ ,
    HFinPs1: InProductsB _ _ = _,
    HBinF1: blockInFdefB _ _ = _,
    HmInS: moduleInSystemB _ _ = _,
    HwfSystem: wf_system _ |- _ =>
    clear - HBinF1 HFinPs1 HmInS HwfPI HwfSystem;
    simpl; intros; subst;
    eapply wf_system__uniqFdef in HFinPs1; eauto;
    intro J; subst;
    apply PhiInfo_must_be_promotable_alloca in HBinF1;
              try solve [auto | inv HBinF1 | intros; congruence]
  end.

Ltac preservation_tac1:=
match goal with
| Hwfcfg : OpsemPP.wf_Config ?cfg,
  Hinv : OpsemPP.wf_State ?cfg _,
  HwfS1 : wf_State _ _ _ _,
  HwfPI : WF_PhiInfo _ |- _ =>
  simpl_ctx Hwfcfg Hinv HwfS1;
  preservation_tac0
end.

Ltac preservation_tac2:=
  match goal with
  | HwfPI : WF_PhiInfo _,
    HFinPs1: InProductsB _ _ = _,
    HBinF1: blockInFdefB _ _ = _,
    HmInS: moduleInSystemB _ _ = _,
    HwfSystem: wf_system _ |- _ =>
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

(* Safety: promotability is preserved. *)
Lemma preservation : forall maxb pinfo cfg S1 S2 tr
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hinv: OpsemPP.wf_State cfg S1)
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
    simpl_ctx' Hwfcfg Hinv HwfS1.
    eapply extractGenericValue__wf_GVs_in_ECs; simpl;
      try solve [eauto | preservation_tac2 | preservation_tac0 |
                 get_wf_value_for_simop; eauto].

Case "sInsertValue".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto];
    eauto.
    simpl_ctx' Hwfcfg Hinv HwfS1.
    eapply insertGenericValue__wf_GVs_in_ECs with (v:=v) (gvs:=gvs) (v':=v')
      (gvs':=gvs'); try solve [eauto | preservation_tac2 | preservation_tac0 |
                               get_wf_value_for_simop; eauto].

Case "sMalloc".
  assert (PI_f pinfo = F -> id0 <> PI_id pinfo) as Hneq.
    preservation_tac1.
  simpl_ctx Hwfcfg Hinv HwfS1.
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
  simpl_ctx Hwfcfg Hinv HwfS1.
  assert (wf_value S (module_intro los nts Ps) F v (typ_pointer t)) as Hwfv.
    get_wf_value_for_simop; eauto.
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
  simpl_ctx Hwfcfg Hinv HwfS1.
  split.
    split.
      eapply impure_cmd_updated_preserves_wf_EC; eauto.
        intros. subst.
        apply wf_EC__wf_lc in HwfEC.

        assert (HwfF:=HwfSystem).
        eapply wf_system__wf_fdef in HwfF; eauto.
        eapply alloca_preserves_wf_defs_at_head; eauto.
          intro EQ. subst.
          eapply WF_PhiInfo_spec17 in HBinF1; eauto using wf_system__uniqFdef.
          destruct HBinF1; auto.

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
  simpl_ctx Hwfcfg Hinv HwfS1.
  assert (wf_lc Mem lc) as Hwflc.
    apply wf_EC__wf_lc in HwfEC; auto.
  assert (wf_value S (module_intro los nts Ps) F v2 (typ_pointer t) /\
          wf_value S (module_intro los nts Ps) F v1 t) as Hwfv.
    get_wf_value_for_simop; eauto.
  destruct Hwfv as [Hwfv1 Hwfv2].
  split.
    split.
      eapply impure_cmd_non_updated_preserves_wf_EC with (M:=Mem); eauto.
        intros. subst.
        eapply mstore_preserves_wf_defs_at_head with (gvs1:=gvs1) in H3;
          eauto using wf_system__uniqFdef.

          eapply OpsemPP.getOperandValue__wf_gvs in Hwfv2; eauto.
          destruct Hwfv2. eauto.

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
    simpl_ctx' Hwfcfg Hinv HwfS1.
    eapply GEP__wf_GVs_in_ECs; try solve
      [eauto using wf_EC__wf_lc | preservation_tac2 | preservation_tac0 |
       get_wf_value_for_simop; eauto].

Case "sTrunc".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto];
    eauto.
    simpl_ctx' Hwfcfg Hinv HwfS1.
    eapply TRUNC__wf_GVs_in_ECs;
      try solve [eauto | preservation_tac2 | preservation_tac0].
      get_wf_value_for_simop; eauto.

Case "sExt".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto];
    eauto.
    simpl_ctx' Hwfcfg Hinv HwfS1.
    eapply EXT__wf_GVs_in_ECs;
      try solve [eauto | preservation_tac2 | preservation_tac0].
      get_wf_value_for_simop; eauto.

Case "sCast".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto];
    eauto.
    simpl_ctx' Hwfcfg Hinv HwfS1.
    eapply CAST__wf_GVs_in_ECs;
      try solve [eauto | preservation_tac2 | preservation_tac0 |
                 get_wf_value_for_simop; eauto].

Case "sIcmp".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto];
    eauto.
    simpl_ctx' Hwfcfg Hinv HwfS1.
    eapply ICMP__wf_GVs_in_ECs with (v1:=v1)(v2:=v2);
      try solve [eauto | preservation_tac2 | preservation_tac0 |
                 get_wf_value_for_simop; eauto].

Case "sFcmp".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto];
    eauto.
    simpl_ctx' Hwfcfg Hinv HwfS1.
    eapply FCMP__wf_GVs_in_ECs with (v1:=v1)(v2:=v2);
      try solve [eauto | preservation_tac2 | preservation_tac0 |
                 get_wf_value_for_simop; eauto].

Case "sSelect".
  destruct (isGVZero (los, nts) c);
    eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto];
      try solve [eauto |
                 simpl_ctx' Hwfcfg Hinv HwfS1;
                 match goal with
                 | H1: Opsem.getOperandValue _ ?v1 _ _ = ret ?gvs1 |-
                       wf_GVs_in_ECs _ _ _ _ _ _ _ ?gvs1 =>
                   eapply getOperandValue__wf_GVs_in_ECs with (v:=v1);
                     try solve [eauto | preservation_tac2 | preservation_tac0 |
                                get_wf_value_for_simop; eauto]
                 end].

Case "sCall". eapply preservation_Call; eauto.

Case "sExCall".
  destruct HwfS1 as [[HwfEC [HwfECs Hwfht]] [Hnonup1 HwfM1]].
  assert (wf_lc Mem lc) as Hwflc.
    apply wf_EC__wf_lc in HwfEC; auto.
  match goal with | H6: Opsem.exCallUpdateLocals _ _ _ _ _ _ = _ |- _ =>
    unfold Opsem.exCallUpdateLocals in H6
  end.
  destruct noret0.
    match goal with | H6: Some _ = Some _ |- _ => inv H6 end.
    split.
      split.
        eapply callExternalProc_preserves_wf_EC; eauto.
      split.
        eapply callExternalFunction_preserves_wf_ECStack; eauto.
        eapply callExternalProc_preserves_wf_ECStack_head_tail; eauto.
    split.
      eapply callExternalFunction_preserves_wf_als; eauto.
      eapply callExternalFunction_preserves_wf_Mem; eauto.

    match goal with
    | H6: match ?oresult with
          | Some _ => _
          | None => _
          end = Some _ |- _ =>
      destruct oresult; tinv H6;
      remember (fit_gv (los, nts) rt1 g) as R;
      destruct R; inv H6
    end.
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

Lemma preservation_star: forall cfg IS IS' tr pinfo maxb
  (Hwfpi: WF_PhiInfo pinfo) (Hwfcfg: OpsemPP.wf_Config cfg)
  (Hwfpp: OpsemPP.wf_State cfg IS)
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg)) (Hinbd: 0 <= maxb),
  Promotability.wf_State maxb pinfo cfg IS ->
  Opsem.sop_star cfg IS IS' tr ->
  Promotability.wf_State maxb pinfo cfg IS'.
Proof.
  intros.
  induction H0; auto.
    apply IHsop_star.
      apply OpsemPP.preservation in H0; auto.
      eapply preservation in H0; eauto.
Qed.

Lemma preservation_plus: forall cfg IS IS' tr pinfo maxb
  (Hwfpi: WF_PhiInfo pinfo) (Hwfcfg: OpsemPP.wf_Config cfg)
  (Hwfpp: OpsemPP.wf_State cfg IS)
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg)) (Hinbd: 0 <= maxb),
  Promotability.wf_State maxb pinfo cfg IS ->
  Opsem.sop_plus cfg IS IS' tr ->
  Promotability.wf_State maxb pinfo cfg IS'.
Proof.
  intros.
  apply OpsemProps.sop_plus__implies__sop_star in H0.
  eapply preservation_star; eauto.
Qed.

Opaque lift_op1.

Lemma s_genInitState__wf_globals_promotable': forall S main VarArgs cfg IS pinfo
  (Hwfpi: WF_PhiInfo pinfo) (HwfS: wf_system S)
  (Hinit : @Opsem.s_genInitState DGVs S main VarArgs Mem.empty = ret (cfg, IS)),
  MemProps.wf_globals (Mem.nextblock (Opsem.Mem IS) - 1) (OpsemAux.Globals cfg)
    /\ 0 <= Mem.nextblock (Opsem.Mem IS) - 1 /\
  Promotability.wf_State (Mem.nextblock (Opsem.Mem IS) - 1) pinfo cfg IS.
Proof.
  intros.
  simpl_s_genInitState.
  simpl.
  assert (HeqR1':=HeqR1).
  eapply genGlobalAndInitMem__wf_globals_Mem in HeqR1'; eauto.
  destruct HeqR1' as [Hwflc [[Hwfg HwfM] _]].
  split; auto.
  split.
    assert (J:=Mem.nextblock_pos m). omega.
  split.
    split.
      split; auto.
        destruct (fdef_dec (PI_f pinfo)
                   (fdef_intro (fheader_intro f t i0 a v) b)); auto.
        intros gvs Hlkup.
        apply getParentOfFdefFromSystem__moduleInProductsInSystemB in HeqR0.
        destruct HeqR0 as [J1 J2].
        assert (uniqFdef (PI_f pinfo)) as Huniq. 
          rewrite e in *. eauto using wf_system__uniqFdef.
        replace a with (getArgsOfFdef (PI_f pinfo)) in HeqR3.
          erewrite WF_PhiInfo__pid_isnt_in_init in Hlkup; eauto.
          congruence.

          rewrite e. auto.
    split; auto.
      intros EC Hin. inv Hin.
  split; auto.
    split; auto.
    intros. inv H.
Qed.

(* Promotablity holds initially. *)
Lemma s_genInitState__wf_globals_promotable: forall S main VarArgs cfg IS pinfo
  (Hwfpi: WF_PhiInfo pinfo) (HwfS: wf_system S)
  (Hinit : @Opsem.s_genInitState DGVs S main VarArgs Mem.empty = ret (cfg, IS)),
  exists maxb,
    MemProps.wf_globals maxb (OpsemAux.Globals cfg) /\ 0 <= maxb /\
    Promotability.wf_State maxb pinfo cfg IS.
Proof.
  intros.
  apply s_genInitState__wf_globals_promotable' with (pinfo:=pinfo) in Hinit;
    auto.
  destruct Hinit as [J1 [J2 J3]]. eauto.
Qed.

(********************************************************************************)
(* More properties for WF_PhiInfo and promotable. *)
Lemma WF_PhiInfo_spec190: forall (pinfo : PhiInfo) (Locals : Opsem.GVsMap)
  Allocas0 (Mem0 : mem) (Hwfpi : WF_PhiInfo pinfo) TD maxb
  (Hnoalias : wf_defs maxb pinfo TD Mem0 Locals Allocas0)
  (gv : GenericValue)
  (HeqR3 : merror = mload TD Mem0 gv (PI_typ pinfo) (PI_align pinfo))
  (HeqR2 : ret gv = lookupAL _ Locals (PI_id pinfo)),
  False.
Proof.
  intros.
  symmetry in HeqR2.
  apply Hnoalias in HeqR2.
  unfold wf_alloca_GVs in HeqR2. rewrite <- HeqR3 in HeqR2.
  destruct HeqR2 as [[_ [_ [_ [gv' HeqR2]]]] _]. congruence.
Qed.

Lemma valid_mload__valid_mstore: forall gv1 pinfo m gv2 mb
  S (Hwfpi: WF_PhiInfo pinfo) los nts Ps (HUniq: uniqFdef (PI_f pinfo))
  (HwfF: wf_fdef S (module_intro los nts Ps) (PI_f pinfo))
  (Heq: gv2 = ($ (blk2GV (los,nts) mb) # (typ_pointer (PI_typ pinfo)) $))
  (Hal: alloca_size_prop (los,nts) pinfo m mb)
  (Hmatch: gv_chunks_match_typ (los,nts) gv1 (PI_typ pinfo)),
  exists m',
    mstore (los,nts) m gv2 (PI_typ pinfo) gv1 (PI_align pinfo) = Some m'.
Proof.
  unfold mstore, gv_chunks_match_typ.
  intros. subst.
  rewrite simpl_blk2GV. simpl.
  unfold alloca_size_prop in Hal.
  inv_mbind.
  rewrite Int.signed_zero.
  apply vm_matches_typ__sizeMC_eq_sizeGenericValue in Hmatch.
  apply mstore_aux_ex with (lo:=0) (hi:=Z_of_nat s).
    tauto.
    omega.

    symmetry_ctx.
    assert (wf_typ S (los,nts) (PI_typ pinfo)) as Hwft.
      eapply WF_PhiInfo_spec21; eauto.
    eapply flatten_typ__getTypeSizeInBits in HeqR; eauto.
    destruct HeqR as [sz1 [al1 [J16 J14]]]; subst.
    apply WF_PhiInfo_spec16 in HwfF; auto.
    destruct HwfF as [sz [al [J1 [J2 J3]]]].
    apply getTypeAllocSize_inv in HeqR0.
    destruct HeqR0 as [sz0 [al0 [J6 [J4 J5]]]]; subst.
    unfold getTypeSizeInBits_and_Alignment in J4.
    unfold getTypeSizeInBits_and_Alignment in J1.
    uniq_result.
    rewrite <- Hmatch. rewrite <- J14.
    assert (RoundUpAlignment (nat_of_Z (ZRdiv (Z_of_nat sz1) 8)) al1 >=
            (nat_of_Z (ZRdiv (Z_of_nat sz1) 8)))%nat as G.
      apply RoundUpAlignment_spec; auto.
    omega.
Qed.

Lemma WF_PhiInfo_spec200: forall (pinfo : PhiInfo) (Locals : Opsem.GVsMap)
  (Hwfpi: WF_PhiInfo pinfo) los nts Ps S (HUniq: uniqFdef (PI_f pinfo))
  (HwfF: wf_fdef S (module_intro los nts Ps) (PI_f pinfo))
  Allocas0 (Mem0 : mem) (Hwfpi : WF_PhiInfo pinfo) maxb
  (Hnoalias : wf_defs maxb pinfo (los,nts) Mem0 Locals Allocas0)
  (gv1 gv2 : GenericValue)
  (Hmatch: gv_chunks_match_typ (los,nts) gv1 (PI_typ pinfo))
  (HeqR3 : merror = mstore (los,nts) Mem0 gv2 (PI_typ pinfo) gv1 (PI_align pinfo))
  (HeqR2 : ret gv2 = lookupAL _ Locals (PI_id pinfo)),
  False.
Proof.
  intros.
  symmetry in HeqR2.
  apply Hnoalias in HeqR2.
  unfold wf_alloca_GVs in HeqR2.
  destruct HeqR2 as [[_ [[mb [Heq [_ [_ Hal]]]] _]] _].
  eapply valid_mload__valid_mstore in Hal; eauto.
  destruct Hal. congruence.
Qed.

(********************************************************************************)
(* Promotability implies non-aliasing. *)
Lemma wf_ECStack_head_in_tail__no_alias_with_blk:
  forall (pinfo : palloca_props.PhiInfo)
  (lc2 : AssocList (GVsT DGVs)) (gv2 : GVsT DGVs) (S : system) (los : layouts)
  (nts : namedts) (Ps : products) (Mem : Memory.mem) (F : fdef) (t : typ)
  (v : value) (gl : GVMap) (Hwfv : wf_value S (module_intro los nts Ps) F v t)
  (maxb : Values.block) (Hget : getOperandValue (los, nts) v lc2 gl = ret gv2)
  (EC : Opsem.ExecutionContext) (Hwfg: MemProps.wf_globals maxb gl)
  (Hnals1 : Promotability.wf_ECStack_head_in_tail maxb pinfo
             (los, nts) Mem lc2 EC)
  (b : Values.block) (i0 : int32) (m : AST.memory_chunk)
  (HeqR : lookupAL (GVsT DGVs) (Opsem.Locals EC) (palloca_props.PI_id pinfo) =
          ret ((Vptr b i0, m) :: nil))
  (G : Opsem.CurFunction EC = palloca_props.PI_f pinfo),
  MemProps.no_alias_with_blk gv2 b.
Proof.
  intros.
  destruct EC. simpl in *.
  destruct (@Hnals1 ((Vptr b i0, m) :: nil)) as [J5 [J2 J4]]; auto.
  destruct v as [id2 | c2]; simpl in *.
    apply J2 in Hget.
    simpl in Hget. tauto.

    inv Hwfv.
    destruct J5 as [mb [J6 [J7 _]]].
    rewrite simpl_blk2GV in J6. inv J6.
    symmetry in Hget.
    eapply const2GV_disjoint_with_runtime_alloca with (t:=t)
      (mb:=mb) in Hget; eauto.
    rewrite simpl_blk2GV in Hget.
    simpl in Hget. tauto.
Qed.

Lemma wf_defs__no_alias_with_blk: forall (pinfo : palloca_props.PhiInfo)
  (los : layouts)
  (nts : namedts) (maxb : Values.block) (Mem : mem) (EC : Opsem.ExecutionContext)
  (gv2 : GenericValue) (gl : GVMap) (Hwfg : MemProps.wf_globals maxb gl)
  (v : value) (S : system) (t : typ) (Ps : products)
  (Hneq : primitives.used_in_value (palloca_props.PI_id pinfo) v = false)
  (Hget : getOperandValue (los, nts) v (@Opsem.Locals DGVs EC) gl = ret gv2)
  (Hwfv : wf_value S (module_intro los nts Ps) (Opsem.CurFunction EC) v t)
  (b : Values.block) (i0 : int32) (m : AST.memory_chunk)
  (HeqR : lookupAL (GVsT DGVs) (Opsem.Locals EC) (palloca_props.PI_id pinfo) =
            ret ((Vptr b i0, m) :: nil))
  (Hinscope : Promotability.wf_defs maxb pinfo (los, nts) Mem
               (Opsem.Locals EC) (Opsem.Allocas EC))
  (G : Opsem.CurFunction EC = palloca_props.PI_f pinfo),
  MemProps.no_alias_with_blk gv2 b.
Proof.
  intros.
  apply_clear Hinscope in HeqR.
  destruct HeqR as [J1 J2].
  destruct v as [id2 | c2].
    apply J2 in Hget.
    unfold Promotability.wf_non_alloca_GVs in Hget.
    simpl in Hneq.
    destruct (id_dec id2 (palloca_props.PI_id pinfo)); tinv Hneq.
    simpl in Hget. tauto.

    unfold Promotability.wf_alloca_GVs in J1.
    destruct J1 as [_ [[mb [J6 [_ [[J7 _] _]]]] _]].
    rewrite simpl_blk2GV in J6. inv J6.
    symmetry in Hget. inv Hwfv.
    eapply const2GV_disjoint_with_runtime_alloca with (t:=t)
      (mb:=mb) in Hget; eauto.
    rewrite simpl_blk2GV in Hget.
    simpl in Hget. tauto.
Qed.

End Promotability.
