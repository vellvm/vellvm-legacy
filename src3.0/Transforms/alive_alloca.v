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

Definition alive_alloca (cs2:cmds) (b:block) (pinfo:PhiInfo) : Prop :=
blockInFdefB b (PI_f pinfo) = true /\
store_in_cmds (PI_id pinfo) cs2 = false /\
let '(_, stmts_intro _ cs _) := b in
exists cs1, exists cs3,
  cs =
  cs1 ++
  insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo) (PI_align pinfo) ::
  cs2 ++
  cs3.

Lemma alive_alloca__alive_mop: forall (cs2:cmds) (b:block) (pinfo:PhiInfo)
  (H: alive_alloca cs2 b pinfo),
  alive_mop (value_const (const_undef (PI_typ pinfo))) 
    (insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo) (PI_align pinfo)) 
    cs2 b pinfo.
Proof.
  intros. destruct b as [? []].
  destruct H as [J1 [J2 [? [? ?]]]]; subst. 
  unfold alive_mop. repeat (split; eauto). 
Qed.

Record AllocaInfo (pinfo: PhiInfo) := mkAllocaInfo {
  AI_tail : cmds;
  AI_block : block;
  AI_alive : alive_alloca AI_tail AI_block pinfo
}.

Definition alinfo__eq__minfo pinfo ainfo minfo: Prop :=
M_value pinfo minfo = value_const (const_undef (PI_typ pinfo)) /\
M_c pinfo minfo = 
      insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo) (PI_align pinfo) /\
M_tail pinfo minfo = AI_tail pinfo ainfo /\
M_block pinfo minfo = AI_block pinfo ainfo.

Lemma alinfo__minfo: forall pinfo (ainfo: AllocaInfo pinfo), 
  { minfo: MopInfo pinfo | alinfo__eq__minfo pinfo ainfo minfo }.
Proof.  
  intros.
  destruct ainfo. 
  exists (mkMopInfo pinfo
    (value_const (const_undef (PI_typ pinfo)))
    (insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo) (PI_align pinfo))
    AI_tail0 AI_block0 
    (alive_alloca__alive_mop AI_tail0 AI_block0 pinfo AI_alive0)).
  split; auto.
Qed.

Definition wf_defs (pinfo:PhiInfo) (alinfo: AllocaInfo pinfo) TD M gl (lc:DGVMap)
  : Prop :=
forall gvsa gvsv
  (Hlkpa: lookupAL _ lc (PI_id pinfo) = Some gvsa)
  (Hlkpv: Opsem.getOperandValue TD (value_const (const_undef (PI_typ pinfo))) lc
     gl = Some gvsv),
  mload TD M gvsa (PI_typ pinfo) (PI_align pinfo) = Some gvsv.

Lemma alinfo__wf_defs__minfo: forall (pinfo:PhiInfo) (alinfo: AllocaInfo pinfo) 
  TD M gl (lc:DGVMap) minfo (Heq: alinfo__eq__minfo pinfo alinfo minfo),
  wf_defs pinfo alinfo TD M gl lc <-> alive_mop.wf_defs pinfo minfo TD M gl lc.
Proof.
  intros. destruct Heq as [J1 [J2 [J3 J4]]].
  unfold wf_defs, alive_mop.wf_defs.
  rewrite J1. tauto.
Qed.

Definition follow_alive_alloca (pinfo:PhiInfo) (alinfo: AllocaInfo pinfo)
  (cs:cmds) : Prop :=
let '(_, stmts_intro _ cs0 _) := AI_block pinfo alinfo in
forall cs1 cs3,
  cs0 =
    cs1 ++
    insn_alloca (PI_id pinfo) (PI_typ pinfo) (PI_num pinfo) (PI_align pinfo) ::
    AI_tail pinfo alinfo ++
    cs3 ->
  (exists csa, exists csb,
    cs = csb ++ cs3 /\ AI_tail pinfo alinfo = csa ++ csb).

Lemma alinfo__follow_alive__minfo: forall (pinfo:PhiInfo) 
  (alinfo: AllocaInfo pinfo) cs minfo 
  (Heq: alinfo__eq__minfo pinfo alinfo minfo),
  follow_alive_alloca pinfo alinfo cs <-> 
    alive_mop.follow_alive_mop pinfo minfo cs.
Proof.
  intros. destruct Heq as [J1 [J2 [J3 J4]]].
  unfold follow_alive_alloca, alive_mop.follow_alive_mop.
  rewrite J4. rewrite J2. rewrite J3. tauto.
Qed.

Definition wf_ExecutionContext (pinfo:PhiInfo) (alinfo: AllocaInfo pinfo) TD M gl
  (ec:Opsem.ExecutionContext) : Prop :=
Opsem.CurFunction ec = PI_f pinfo ->
Opsem.CurBB ec = AI_block pinfo alinfo ->
follow_alive_alloca pinfo alinfo (Opsem.CurCmds ec) ->
wf_defs pinfo alinfo TD M gl (Opsem.Locals ec).

Lemma alinfo__wf_EC__minfo: forall (pinfo:PhiInfo) (alinfo: AllocaInfo pinfo) 
  TD M gl ec minfo (Heq: alinfo__eq__minfo pinfo alinfo minfo),
  wf_ExecutionContext pinfo alinfo TD M gl ec <-> 
    alive_mop.wf_ExecutionContext pinfo minfo TD M gl ec.
Proof.
  intros.
  unfold wf_ExecutionContext, alive_mop.wf_ExecutionContext.
  assert (J:=Heq).
  apply alinfo__follow_alive__minfo with (cs:=Opsem.CurCmds ec) in J.
  assert (J':=Heq).
  apply alinfo__wf_defs__minfo with (lc:=Opsem.Locals ec)(TD:=TD)(M:=M)
    (gl:=gl) in J'.
  destruct Heq as [J1 [J2 [J3 J4]]].
  rewrite J4.
  tauto.
Qed.

Fixpoint wf_ECStack (pinfo:PhiInfo) (alinfo: AllocaInfo pinfo) TD M gl
  (ecs:Opsem.ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' =>
    wf_ExecutionContext pinfo alinfo TD M gl ec /\
    wf_ECStack pinfo alinfo TD M gl ecs'
end.

Lemma alinfo__wf_ECs__minfo: forall (pinfo:PhiInfo) (alinfo: AllocaInfo pinfo) 
  TD M gl minfo (Heq: alinfo__eq__minfo pinfo alinfo minfo) ecs,
  wf_ECStack pinfo alinfo TD M gl ecs <-> 
    alive_mop.wf_ECStack pinfo minfo TD M gl ecs.
Proof.
  induction ecs.
    tauto.
   
    assert (J:=Heq).
    apply alinfo__wf_EC__minfo with (ec:=a)(TD:=TD)(M:=M)(gl:=gl) in J.
    simpl. tauto.
Qed.

Definition wf_State (pinfo:PhiInfo) (alinfo: AllocaInfo pinfo)
  (cfg:OpsemAux.Config) (S:Opsem.State) : Prop :=
wf_ECStack pinfo alinfo (OpsemAux.CurTargetData cfg) (Opsem.Mem S)
  (OpsemAux.Globals cfg) (Opsem.ECS S).

Lemma alinfo__wf_State__minfo: forall (pinfo:PhiInfo) (alinfo: AllocaInfo pinfo) 
  minfo (Heq: alinfo__eq__minfo pinfo alinfo minfo) cfg S,
  wf_State pinfo alinfo cfg S <-> 
    alive_mop.wf_State pinfo minfo cfg S.
Proof.
  intros.
  apply alinfo__wf_ECs__minfo; auto.
Qed.

Lemma preservation : forall maxb pinfo alinfo cfg S1 S2 tr
  (Hwfg: wf_globals maxb (OpsemAux.Globals cfg))
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (HsInsn: Opsem.sInsn cfg S1 S2 tr)
  (HwfS1: wf_State pinfo alinfo cfg S1), wf_State pinfo alinfo cfg S2.
Proof.
  intros.
  destruct (alinfo__minfo pinfo alinfo) as [minfo Heq].
  eapply alinfo__wf_State__minfo; eauto.
  eapply alinfo__wf_State__minfo in HwfS1; eauto.
  eapply alive_mop.preservation; eauto.
Qed.

Lemma preservation_star : forall maxb pinfo alinfo cfg S1 S2 tr
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg)) (Hle: 0 <= maxb)
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (Hstar: Opsem.sop_star cfg S1 S2 tr)
  (HwfS1: wf_State pinfo alinfo cfg S1), 
  wf_State pinfo alinfo cfg S2.
Proof.
  intros.
  induction Hstar; auto.
    apply IHHstar.
      apply OpsemPP.preservation in H; auto.
      eapply Promotability.preservation in H; eauto.
      eapply preservation in H; eauto.
Qed.  

Lemma preservation_plus : forall maxb pinfo alinfo cfg S1 S2 tr
  (Hwfg: MemProps.wf_globals maxb (OpsemAux.Globals cfg)) (Hle: 0 <= maxb)
  (Hwfcfg: OpsemPP.wf_Config cfg) (Hwfpp: OpsemPP.wf_State cfg S1) 
  (Hnoalias: Promotability.wf_State maxb pinfo cfg S1) 
  (HwfPI: WF_PhiInfo pinfo) (Hplus: Opsem.sop_plus cfg S1 S2 tr)
  (HwfS1: wf_State pinfo alinfo cfg S1), 
  wf_State pinfo alinfo cfg S2.
Proof.
  intros.
  apply OpsemProps.sop_plus__implies__sop_star in Hplus.
  eapply preservation_star; eauto.
Qed.  

Lemma s_genInitState__alive_alloca: forall S main VarArgs cfg IS pinfo alinfo
  (HwfS : wf_system S) (Hwfpi: WF_PhiInfo pinfo) 
  (Hinit : @Opsem.s_genInitState DGVs S main VarArgs Mem.empty = ret (cfg, IS)),
  wf_State pinfo alinfo cfg IS.
Proof.
  intros.
  destruct (alinfo__minfo pinfo alinfo) as [minfo Heq].
  eapply alinfo__wf_State__minfo; eauto.
  eapply alive_mop.s_genInitState__alive_mop; eauto.
Qed.

