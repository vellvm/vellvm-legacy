Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Maps.
Require Import opsem_props.
Require Import promotable_props.
Require Import primitives.
Require Import palloca_props.
Require Import memory_props.
Require Import trans_tactic.
Require Import alive_mop.

Import Promotability.

(* This file instantiates alive_mop with alive stores. *)

(* 
  An alive store can use a different alignment from the promotable alloca's.
  If the store's alignment is not legal w.r.t the promotable's, the original
  program is undefined. Otherwise, the value we load should be the same.

  So far, the memory model assumes all programs' alignments are correct. So,
  we will not check if an alignment is proper. This is one of our future work.
*)
Definition alive_store (sid: id) (sal: align) (v:value) (cs2:cmds) (b:block) 
  (pinfo:PhiInfo) : Prop :=
blockInFdefB b (PI_f pinfo) = true /\
store_in_cmds (PI_id pinfo) cs2 = false /\
let '(_, stmts_intro _ cs _) := b in
exists cs1, exists cs3,
  cs =
  cs1 ++
  insn_store sid (PI_typ pinfo) v (value_id (PI_id pinfo)) sal ::
  cs2 ++
  cs3.

Lemma alive_store__alive_mop: forall sid sal v (cs2:cmds) (b:block) (pinfo:PhiInfo)
  (H: alive_store sid sal v cs2 b pinfo),
  alive_mop v
    (insn_store sid (PI_typ pinfo) v (value_id (PI_id pinfo)) sal) 
    cs2 b pinfo.
Proof.
  intros. destruct b as [? []].
  destruct H as [J1 [J2 [? [? ?]]]]; subst. 
  unfold alive_mop. repeat (split; eauto). 
Qed.

Record StoreInfo (pinfo: PhiInfo) := mkStoreInfo {
  SI_id : id;
  SI_align : align;
  SI_value : value;
  SI_tail : cmds;
  SI_block : block;
  SI_alive : alive_store SI_id SI_align SI_value SI_tail SI_block pinfo
}.

Definition stinfo__eq__minfo pinfo stinfo minfo: Prop :=
M_value pinfo minfo = SI_value pinfo stinfo /\
M_c pinfo minfo = 
   insn_store (SI_id pinfo stinfo) (PI_typ pinfo) (SI_value pinfo stinfo) 
     (value_id (PI_id pinfo)) (SI_align pinfo stinfo) /\
M_tail pinfo minfo = SI_tail pinfo stinfo /\
M_block pinfo minfo = SI_block pinfo stinfo.

Lemma stinfo__minfo: forall pinfo (stinfo: StoreInfo pinfo), 
  { minfo: MopInfo pinfo | stinfo__eq__minfo pinfo stinfo minfo }.
Proof.  
  intros.
  destruct stinfo. 
  exists (mkMopInfo pinfo SI_value0
    (insn_store SI_id0 (PI_typ pinfo) SI_value0 (value_id (PI_id pinfo)) 
      SI_align0)
    SI_tail0 SI_block0 
    (alive_store__alive_mop SI_id0 SI_align0 SI_value0 
      SI_tail0 SI_block0 pinfo SI_alive0)).
  split; auto.
Qed.

Definition wf_defs (pinfo:PhiInfo) (stinfo: StoreInfo pinfo) TD M gl (lc:DGVMap)
  : Prop :=
forall gvsa gvsv
  (Hlkpa: lookupAL _ lc (PI_id pinfo) = Some gvsa)
  (Hlkpv: Opsem.getOperandValue TD (SI_value pinfo stinfo) lc gl
    = Some gvsv),
  mload TD M gvsa (PI_typ pinfo) (PI_align pinfo) = Some gvsv.

Lemma stinfo__wf_defs__minfo: forall (pinfo:PhiInfo) stinfo
  TD M gl (lc:DGVMap) minfo (Heq: stinfo__eq__minfo pinfo stinfo minfo),
  wf_defs pinfo stinfo TD M gl lc <-> alive_mop.wf_defs pinfo minfo TD M gl lc.
Proof.
  intros. destruct Heq as [J1 [J2 [J3 J4]]].
  unfold wf_defs, alive_mop.wf_defs.
  rewrite J1. tauto.
Qed.

Definition follow_alive_store (pinfo:PhiInfo) (stinfo: StoreInfo pinfo)
  (cs:cmds) : Prop :=
let '(_, stmts_intro _ cs0 _) := SI_block pinfo stinfo in
forall cs1 cs3,
  cs0 =
    cs1 ++
    insn_store (SI_id pinfo stinfo) (PI_typ pinfo) (SI_value pinfo stinfo)
      (value_id (PI_id pinfo)) (SI_align pinfo stinfo) ::
    SI_tail pinfo stinfo ++
    cs3 ->
  (exists csa, exists csb,
    cs = csb ++ cs3 /\ SI_tail pinfo stinfo = csa ++ csb).

Lemma stinfo__follow_alive__minfo: forall (pinfo:PhiInfo) 
  stinfo cs minfo 
  (Heq: stinfo__eq__minfo pinfo stinfo minfo),
  follow_alive_store pinfo stinfo cs <-> 
    alive_mop.follow_alive_mop pinfo minfo cs.
Proof.
  intros. destruct Heq as [J1 [J2 [J3 J4]]].
  unfold follow_alive_store, alive_mop.follow_alive_mop.
  rewrite J4. rewrite J2. rewrite J3. tauto.
Qed.

Definition wf_ExecutionContext (pinfo:PhiInfo) (stinfo: StoreInfo pinfo) TD M gl
  (ec:Opsem.ExecutionContext) : Prop :=
Opsem.CurFunction ec = PI_f pinfo ->
Opsem.CurBB ec = SI_block pinfo stinfo ->
follow_alive_store pinfo stinfo (Opsem.CurCmds ec) ->
wf_defs pinfo stinfo TD M gl (Opsem.Locals ec).

Lemma stinfo__wf_EC__minfo: forall (pinfo:PhiInfo) stinfo
  TD M gl ec minfo (Heq: stinfo__eq__minfo pinfo stinfo minfo),
  wf_ExecutionContext pinfo stinfo TD M gl ec <-> 
    alive_mop.wf_ExecutionContext pinfo minfo TD M gl ec.
Proof.
  intros.
  unfold wf_ExecutionContext, alive_mop.wf_ExecutionContext.
  assert (J:=Heq).
  apply stinfo__follow_alive__minfo with (cs:=Opsem.CurCmds ec) in J.
  assert (J':=Heq).
  apply stinfo__wf_defs__minfo with (lc:=Opsem.Locals ec)(TD:=TD)(M:=M)
    (gl:=gl) in J'.
  destruct Heq as [J1 [J2 [J3 J4]]].
  rewrite J4.
  tauto.
Qed.

Fixpoint wf_ECStack (pinfo:PhiInfo) (stinfo: StoreInfo pinfo) TD M gl
  (ecs:Opsem.ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' =>
    wf_ExecutionContext pinfo stinfo TD M gl ec /\
    wf_ECStack pinfo stinfo TD M gl ecs'
end.

Lemma stinfo__wf_ECs__minfo: forall (pinfo:PhiInfo) stinfo
  TD M gl minfo (Heq: stinfo__eq__minfo pinfo stinfo minfo) ecs,
  wf_ECStack pinfo stinfo TD M gl ecs <-> 
    alive_mop.wf_ECStack pinfo minfo TD M gl ecs.
Proof.
  induction ecs.
    tauto.
   
    assert (J:=Heq).
    apply stinfo__wf_EC__minfo with (ec:=a)(TD:=TD)(M:=M)(gl:=gl) in J.
    simpl. tauto.
Qed.

Definition wf_State (pinfo:PhiInfo) (stinfo: StoreInfo pinfo)
  (cfg:OpsemAux.Config) (S:Opsem.State) : Prop :=
wf_ECStack pinfo stinfo (OpsemAux.CurTargetData cfg) (Opsem.Mem S)
  (OpsemAux.Globals cfg) (Opsem.ECS S).

Lemma stinfo__wf_State__minfo: forall (pinfo:PhiInfo) stinfo
  minfo (Heq: stinfo__eq__minfo pinfo stinfo minfo) cfg S,
  wf_State pinfo stinfo cfg S <-> 
    alive_mop.wf_State pinfo minfo cfg S.
Proof.
  intros.
  apply stinfo__wf_ECs__minfo; auto.
Qed.

Ltac destruct_stinfo :=
match goal with
| stinfo: StoreInfo _ |- _ =>
  destruct stinfo as [SI_id0 SI_align0 SI_value0 SI_tail0
                       [SI_l0 [SI_ps0 SI_cs0 SI_tmn0]] SI_prop0];
  simpl in *;
  destruct SI_prop0 as 
    [SI_BInF0 [SI_stincmds0 [SI_cs1 [SI_cs3 SI_EQ]]]]; subst; simpl
end.

Lemma preservation : forall maxb pinfo stinfo cfg S1 S2 tr
  (Hwfg: wf_globals maxb (OpsemAux.Globals cfg))
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (HsInsn: Opsem.sInsn cfg S1 S2 tr)
  (HwfS1: wf_State pinfo stinfo cfg S1), wf_State pinfo stinfo cfg S2.
Proof.
  intros.
  destruct (stinfo__minfo pinfo stinfo) as [minfo Heq].
  eapply stinfo__wf_State__minfo; eauto.
  eapply stinfo__wf_State__minfo in HwfS1; eauto.
  eapply alive_mop.preservation; eauto.
Qed.

Lemma preservation_star : forall maxb pinfo stinfo cfg S1 S2 tr
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg)) (Hle: 0 <= maxb)
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (Hstar: Opsem.sop_star cfg S1 S2 tr)
  (HwfS1: wf_State pinfo stinfo cfg S1), 
  wf_State pinfo stinfo cfg S2.
Proof.
  intros.
  induction Hstar; auto.
    apply IHHstar.
      apply OpsemPP.preservation in H; auto.
      eapply Promotability.preservation in H; eauto.
      eapply preservation in H; eauto.
Qed.  

Lemma preservation_plus : forall maxb pinfo stinfo cfg S1 S2 tr
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg)) (Hle: 0 <= maxb)
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (Hplus: Opsem.sop_plus cfg S1 S2 tr)
  (HwfS1: wf_State pinfo stinfo cfg S1), 
  wf_State pinfo stinfo cfg S2.
Proof.
  intros.
  apply OpsemProps.sop_plus__implies__sop_star in Hplus.
  eapply preservation_star; eauto.
Qed.  

Lemma s_genInitState__alive_store: forall S main VarArgs cfg IS pinfo stinfo
  (HwfS : wf_system S) (Hwfpi: WF_PhiInfo pinfo) 
  (Hinit : @Opsem.s_genInitState DGVs S main VarArgs Mem.empty = ret (cfg, IS)),
  wf_State pinfo stinfo cfg IS.
Proof.
  intros.
  destruct (stinfo__minfo pinfo stinfo) as [minfo Heq].
  eapply stinfo__wf_State__minfo; eauto.
  eapply alive_mop.s_genInitState__alive_mop; eauto.
Qed.
