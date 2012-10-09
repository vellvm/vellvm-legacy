Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import opsem_props.
Require Import primitives.
Require Import subst_inv.
Require Import trans_tactic.
Require Import top_sim.
Require Import program_sim.

(* This file proves the dynamic properties of substitution. *)

(*******************************************************************)
(* We first prove semantics preservation by top_sim. *)
Module SubstSim.

Section SubstSim.

Variable (sf:fdef) (sid:id) (sv:value).

(* Prove that substitution satisfies the requirement of top_sim. *)
Definition fdef_simulation f1 f2 : Prop :=
  if (fdef_dec sf f1) then subst_fdef sid sv f1 = f2 else f1 = f2.

Definition cmds_simulation (f1:fdef) cs1 cs2 : Prop :=
  if (fdef_dec sf f1) then
    List.map (subst_cmd sid sv) cs1 = cs2
  else cs1 = cs2.

Definition block_simulation f1 b1 b2 : Prop :=
  (if (fdef_dec sf f1) then subst_block sid sv b1
  else b1) = b2.

Lemma fdef_simulation__eq_fheader: forall f1 f2
  (H: fdef_simulation f1 f2),
  fheaderOfFdef f1 = fheaderOfFdef f2.
Proof.
  unfold fdef_simulation.
  intros.
  destruct (fdef_dec sf f1); inv H; auto.
    destruct f1 as [fh b]; simpl; auto.
Qed.

Lemma fdef_simulation__det_right: forall f f1 f2,
  fdef_simulation f f1 ->
  fdef_simulation f f2 ->
  f1 = f2.
Proof.
  unfold fdef_simulation.
  intros.
  destruct_if; congruence.
Qed.

Definition Fsim := mkFunSim 
fdef_simulation
fdef_simulation__eq_fheader
fdef_simulation__det_right
.

Definition products_simulation Ps1 Ps2 : Prop :=
@TopSim.products_simulation Fsim Ps1 Ps2.

Definition system_simulation S1 S2 : Prop :=
@TopSim.system_simulation Fsim S1 S2.

Definition phis_simulation (f1:fdef) ps1 ps2 : Prop :=
  if (fdef_dec sf f1) then
    List.map (subst_phi sid sv) ps1 = ps2
  else ps1 = ps2.

Definition tmn_simulation (f1:fdef) t t': Prop :=
if (fdef_dec sf f1) then subst_tmn sid sv t = t'
else t = t'.

Definition EC_simulation (EC1 EC2:@Opsem.ExecutionContext DGVs) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1,
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation f1 f2 /\
       tmn_simulation f1 tmn1 tmn2 /\
       als1 = als2 /\
       block_simulation f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11,
         b1 = (l1, stmts_intro ps1 (cs11++cs1) tmn1))
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = (l2, stmts_intro ps2 (cs21++cs2) tmn2)) /\
       lc1 = lc2 /\
       cmds_simulation f1 cs1 cs2
  end.

Fixpoint ECs_simulation (ECs1 ECs2:@Opsem.ECStack DGVs): Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' =>
    EC_simulation EC1 EC2 /\ ECs_simulation ECs1' ECs2'
| _, _ => False
end.

Definition State_simulation
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\
    products_simulation Ps1 Ps2 /\
    ECs_simulation ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2
end.

Lemma cmds_simulation_nil_inv: forall f1 cs,
  cmds_simulation f1 nil cs -> cs = nil.
Proof.
  unfold cmds_simulation. simpl.
  intros. destruct (fdef_dec sf f1); auto.
Qed.

Definition cmd_simulation (f1:fdef) c c': Prop :=
(if (fdef_dec sf f1) then subst_cmd sid sv c
else c) = c'.

Lemma cmds_simulation_cons_inv: forall F c1 cs2 cs',
  cmds_simulation F (c1 :: cs2) cs' ->
  exists c1', exists cs2',
    cs' = c1' :: cs2' /\
    cmd_simulation F c1 c1' /\
    cmds_simulation F cs2 cs2'.
Proof.
  intros.
  unfold cmds_simulation, cmd_simulation in *.
  destruct (fdef_dec sf F); subst; simpl; eauto.
Qed.

Lemma fdef_sim__block_sim : forall f1 f2 sts1 sts2 l0,
  fdef_simulation f1 f2 ->
  lookupBlockViaLabelFromFdef f1 l0 = Some sts1 ->
  lookupBlockViaLabelFromFdef f2 l0 = Some sts2 ->
  block_simulation f1 (l0, sts1) (l0, sts2).
Proof.
  intros.
  unfold fdef_simulation in H.
  unfold block_simulation.
  destruct (fdef_dec sf f1); subst.
    destruct f1. simpl in *.
    f_equal.
    eapply fdef_sim__lookupAL_subst_stmts; eauto.

    uniq_result. auto.
Qed.

Lemma block_simulation_inv : forall F l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2,
  block_simulation F (l1, stmts_intro ps1 cs1 tmn1)
    (l2, stmts_intro ps2 cs2 tmn2) ->
  l1 = l2 /\
  phis_simulation F ps1 ps2 /\
  cmds_simulation F cs1 cs2 /\
  tmn_simulation F tmn1 tmn2.
Proof.
  intros.
  unfold block_simulation, cmds_simulation, phis_simulation, tmn_simulation in *.
  destruct (fdef_dec sf F); inv H; auto.
Qed.

Definition value_simulation (f1:fdef) v v': Prop :=
if (fdef_dec sf f1) then subst_value sid sv v = v'
else v = v'.

Lemma getOperandValue_inTmnOperands_sim : forall los nts s ps gl 
  (f : fdef) 
  (HwfF: wf_fdef s (module_intro los nts ps) f) (Huniq: uniqFdef f)
  (tmn : terminator)
  (lc : GVMap)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f (l1, stmts_intro ps1 cs1 tmn))
  (HbInF : blockInFdefB (l1, stmts_intro ps1 cs1 tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_tmn f (l1, stmts_intro ps1 cs1 tmn) tmn)
  (Hinscope : subst_inv.wf_defs (value_id sid) sv sf
                     (los, nts) gl f lc l0)
  (v v' : value)
  (Hvincs : valueInTmnOperands v tmn) gv gv'
  (Hget' : getOperandValue (los, nts) v' lc gl = Some gv')
  (Hvsim : value_simulation f v v')
  (Hget : getOperandValue (los, nts) v lc gl = Some gv),
  gv = gv'.
Proof.
  intros.
  unfold value_simulation in Hvsim.
  unfold wf_defs in Hinscope.
  destruct (fdef_dec sf f); subst; try solve [uniq_result; auto].
  destruct v as [i0|]; subst; simpl in Hget', Hget, Hinscope;
    try solve [uniq_result; auto].
  destruct (id_dec i0 sid); simpl in Hget'; subst;
    try solve [uniq_result; auto].
  assert (In sid l0) as Hin.
    (* sid is inscope *)
    unfold inscope_of_tmn in HeqR.
    eapply terminator_operands__in_scope' in HeqR; eauto 1.
      apply valueInTmnOperands__InOps; auto.
  eapply Hinscope in Hget; eauto.
Qed.

Lemma getOperandValue_inCmdOperands_sim : forall los nts s gl ps (f : fdef)
  (HwfF : wf_fdef s (module_intro los nts ps) f) (Huniq: uniqFdef f)
  (tmn : terminator)
  (lc : GVMap)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 cs : list cmd)
  (c : cmd)
  (Hreach : isReachableFromEntry f (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_cmd f (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn) c)
  (Hinscope : subst_inv.wf_defs (value_id sid) sv sf
                     (los, nts) gl f lc l0)
  (v v' : value)
  (Hvincs : valueInCmdOperands v c) gv gv'
  (Hget' : getOperandValue (los, nts) v' lc gl = Some gv')
  (Hvsim : value_simulation f v v')
  (Hget : getOperandValue (los, nts) v lc gl = Some gv),
  gv = gv'.
Proof.
  intros.
  unfold value_simulation in Hvsim.
  unfold wf_defs in Hinscope.
  destruct (fdef_dec sf f); subst; try solve [uniq_result; auto].
  destruct v as [i0|]; subst; simpl in Hget', Hget, Hinscope;
    try solve [uniq_result; auto].
  destruct (id_dec i0 sid); simpl in Hget'; subst;
    try solve [uniq_result; auto].
  assert (In sid l0) as Hin.
    (* sid is inscope *)
    unfold inscope_of_cmd in HeqR.
    eapply cmd_operands__in_scope' in HeqR; eauto 1.
      solve_in_list.
      apply valueInCmdOperands__InOps; auto.
  eapply Hinscope in Hget; eauto.
Qed.

Lemma phis_simulation_nil_inv: forall f1 ps,
  phis_simulation f1 nil ps -> ps = nil.
Proof.
  unfold phis_simulation. simpl.
  intros. destruct (fdef_dec sf f1); auto.
Qed.

Definition phi_simulation (f1:fdef) p1 p2 : Prop :=
  if (fdef_dec sf f1) then
    subst_phi sid sv p1 = p2
  else p1 = p2.

Lemma phis_simulation_cons_inv: forall F p1 ps2 ps',
  phis_simulation F (p1 :: ps2) ps' ->
  exists p1', exists ps2',
    ps' = p1' :: ps2' /\
    phi_simulation F p1 p1' /\
    phis_simulation F ps2 ps2'.
Proof.
  intros.
  unfold phis_simulation, phi_simulation in *.
  destruct (fdef_dec sf F); subst; simpl; eauto.
Qed.

Definition list_value_l_simulation (f1:fdef) vls vls': Prop :=
if (fdef_dec sf f1) then
  subst_list_value_l sid sv vls = vls'
else vls = vls'.

Lemma phi_simulation_inv: forall f1 i1 t1 vls1 i2 t2 vls2,
  phi_simulation f1 (insn_phi i1 t1 vls1) (insn_phi i2 t2 vls2) ->
  i1 = i2 /\ t1 = t2 /\ list_value_l_simulation f1 vls1 vls2.
Proof.
  unfold phi_simulation, list_value_l_simulation.
  intros.
  destruct (fdef_dec sf f1); inv H; auto.
Qed.

Lemma getValueViaLabelFromValuels_sim : forall l1 f1 vls1 vls2 v
  v' (Hsim: list_value_l_simulation f1 vls1 vls2)
  (HeqR0 : ret v = getValueViaLabelFromValuels vls1 l1)
  (HeqR' : ret v' = getValueViaLabelFromValuels vls2 l1),
  value_simulation f1 v v'.
Proof.
  induction vls1; simpl; intros; try congruence. simpl_prod.
    unfold list_value_l_simulation, value_simulation in *.
    destruct (fdef_dec sf f1); subst.
      simpl in HeqR'.
      destruct (l0 == l1); subst; eauto.
        congruence.

    simpl in HeqR'.
    destruct (l0 == l1); subst; try (congruence || eauto).
Qed.

Lemma getValueViaLabelFromValuels_getOperandValue_sim : forall
  los nts s gl 
  ps (f : fdef) 
  (HwfF : wf_fdef s (module_intro los nts ps) f) (HuniqF: uniqFdef f)
  (l0 : l) (lc : GVMap) (t : list atom) (l1 : l) (ps1 : phinodes)
  (cs1 : cmds) (tmn1 : terminator)
  (HeqR : ret t = inscope_of_tmn f (l1, stmts_intro ps1 cs1 tmn1) tmn1)
  (Hinscope : subst_inv.wf_defs (value_id sid) sv sf
                     (los, nts) gl f lc t)
  (ps' : phinodes) (cs' : cmds) (tmn' : terminator)
  (i0 : id) (l2 : list (value * l)) (ps2 : list phinode)
  (Hreach : isReachableFromEntry f (l0, stmts_intro ps' cs' tmn'))
  (HbInF : blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true)
  (Hreach' : isReachableFromEntry f (l1, stmts_intro ps1 cs1 tmn1))
  (v0 v0': value)
  (HeqR3 : ret v0 = getValueViaLabelFromValuels l2 l1)
  (g1 : GenericValue)
  (HeqR4 : ret g1 = getOperandValue (los,nts) v0 lc gl)
  (g2 : GVMap) (g : GenericValue) (g0 : GVMap) t1
  (H1 : wf_value_list
          (List.map
             (fun p : value * l =>
               let '(value_, _) := p in
                 (s, module_intro los nts ps, f, value_, t1)) l2))
  (H7 : wf_phinode f (l0, stmts_intro ps' cs' tmn') (insn_phi i0 t1 l2))
  (Hvsim: value_simulation f v0 v0')
  (HeqR1 : ret g = getOperandValue (los,nts) v0' lc gl),
  g1 = g.
Proof.
  intros. symmetry_ctx.
  unfold value_simulation in Hvsim.
  destruct (fdef_dec sf f); subst; try solve [uniq_result; auto].
  destruct v0 as [vid | vc]; simpl in HeqR1, HeqR4; try congruence.
  destruct (id_dec vid sid); subst; simpl in HeqR1;
    try congruence.
  assert (In sid t) as Hid2InScope.
    eapply incoming_value__in_scope in H7; eauto.
  eapply Hinscope in HeqR1; simpl; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_sim : forall
  los nts s gl ps (f : fdef) 
  (HwfF : wf_fdef s (module_intro los nts ps) f) (HuniqF: uniqFdef f)
  l0
  (lc : GVMap)
  (t : list atom)
  l1 ps1 cs1 tmn1
  (HeqR : ret t = inscope_of_tmn f (l1, stmts_intro ps1 cs1 tmn1) tmn1)
  (Hinscope : subst_inv.wf_defs (value_id sid) sv sf
                     (los, nts) gl f lc t)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  (Hsucc : In l0 (successors_terminator tmn1))
  (Hreach : isReachableFromEntry f (l0, stmts_intro ps' cs' tmn'))
  (Hreach' : isReachableFromEntry f (l1, stmts_intro ps1 cs1 tmn1))
  (HbInF : blockInFdefB
            (l1, stmts_intro ps1 cs1 tmn1) f = true)
  (HwfB : wf_block s (module_intro los nts ps) f 
            (l1, stmts_intro ps1 cs1 tmn1))
  B1'
  (Hbsim1: block_simulation f (l1, stmts_intro ps1 cs1 tmn1) B1')
  ps2
  (H8 : wf_phinodes s (module_intro los nts ps) f 
          (l0, stmts_intro ps' cs' tmn') ps2)
  (Hin: exists ps1, ps' = ps1 ++ ps2) RVs RVs' ps2'
  (Hpsim2: phis_simulation f ps2 ps2')
  (Hget : @Opsem.getIncomingValuesForBlockFromPHINodes DGVs (los,nts) ps2
           (l1, stmts_intro ps1 cs1 tmn1) gl lc = ret RVs)
  (Hget' : @Opsem.getIncomingValuesForBlockFromPHINodes DGVs (los,nts)
             ps2' B1' gl lc = ret RVs'),
  RVs = RVs'.
Proof.
  induction ps2 as [|[i1 t1 l2]]; intros; simpl in Hget, Hget'.
    apply phis_simulation_nil_inv in Hpsim2.
    subst. simpl in Hget'. congruence.

    apply phis_simulation_cons_inv in Hpsim2.
    destruct Hpsim2 as [p1' [ps2'0 [Heq [Hpsim1 Hpsim2]]]]; subst.
    simpl in Hget'. destruct p1' as [i2 t2 l3]. 
    apply phi_simulation_inv in Hpsim1.
    destruct Hpsim1 as [Heq1 [Heq2 Hvlsim1]]; subst.
    inv_mbind'.
    destruct B1' as [? []]. simpl in HeqR0.
    apply block_simulation_inv in Hbsim1.
    destruct Hbsim1 as [Heq [Hpsim1 [Hcssim1 Htsim1]]]; subst.
    simpl in HeqR3.
    eapply getValueViaLabelFromValuels_sim in Hvlsim1; eauto.
    match goal with | H8: wf_phinodes _ _ _ _ _ |- _ => inv H8 end.
    assert (g = g0) as Heq.
      match goal with | H5 : wf_insn _ _ _ _ _ |- _ => inv H5 end.
      find_wf_value_list.
      eapply getValueViaLabelFromValuels_getOperandValue_sim with (l0:=l0);
        eauto.
    subst.
    match goal with
    | H6 : wf_phinodes _ _ _ _ _ |- _ =>
      eapply IHps2 with (RVs:=l4) in H6; eauto
    end.
      congruence.

      destruct Hin as [ps3 Hin]. subst.
      exists (ps3++[insn_phi i2 t2 l2]).
      simpl_env. auto.
Qed.

Lemma switchToNewBasicBlock_sim : forall
  los nts s gl 
  ps (f : fdef)
  (HwfF : wf_fdef s (module_intro los nts ps) f) (HuniqF: uniqFdef f)
  l2 (lc : GVMap) (t : list atom) l1 ps1 cs1 tmn1
  (HeqR : ret t = inscope_of_tmn f (l1, stmts_intro ps1 cs1 tmn1) tmn1)
  (Hinscope : subst_inv.wf_defs (value_id sid) sv sf
                     (los, nts) gl f lc t)
  (ps2 : phinodes) (cs2 : cmds) (tmn2 : terminator)
  (Hsucc : In l2 (successors_terminator tmn1))
  (Hreach : isReachableFromEntry f (l2, stmts_intro ps2 cs2 tmn2))
  (Hreach' : isReachableFromEntry f (l1, stmts_intro ps1 cs1 tmn1))
  (HbInF' : blockInFdefB (l2, stmts_intro ps2 cs2 tmn2) f = true)
  (HbInF : blockInFdefB (l1, stmts_intro ps1 cs1 tmn1) f = true)
  lc0 lc0'
  (Hget : @Opsem.switchToNewBasicBlock DGVs (los,nts)
    (l2, stmts_intro ps2 cs2 tmn2)
    (l1, stmts_intro ps1 cs1 tmn1) gl lc = ret lc0) B1' B2'
  (Hbsim1: block_simulation f (l1, stmts_intro ps1 cs1 tmn1) B1')
  (Hbsim2: block_simulation f (l2, stmts_intro ps2 cs2 tmn2) B2')
  (Hget' : @Opsem.switchToNewBasicBlock DGVs (los,nts) B2' B1' gl lc = ret lc0'),
  lc0 = lc0'.
Proof.
  intros.
  assert (HwfB : wf_block s (module_intro los nts ps) f 
           (l1, stmts_intro ps1 cs1 tmn1)).
    apply wf_fdef__blockInFdefB__wf_block; auto.
  assert (H8 : wf_phinodes s (module_intro los nts ps) f 
                 (l2, stmts_intro ps2 cs2 tmn2) ps2).
    apply wf_fdef__wf_phinodes; auto.
  unfold Opsem.switchToNewBasicBlock in *.
  inv_mbind'. app_inv. symmetry_ctx.
  assert (l3 = l0) as EQ.
    destruct B2' as [? []].
    apply block_simulation_inv in Hbsim2.
    destruct Hbsim2 as [J1 [J2 [J3 J4]]]; subst.
    eapply getIncomingValuesForBlockFromPHINodes_sim; eauto.
      exists nil. auto.
  subst. auto.
Qed.

Lemma cmds_at_block_tail_next': forall (l3:l) ps3 cs31 c cs tmn,
  exists l1, exists ps1, exists cs11,
         (l3, stmts_intro ps3 (cs31 ++ c :: cs) tmn) =
         (l1, stmts_intro ps1 (cs11 ++ cs) tmn).
Proof.
  intros.
  exists l3. exists ps3. exists (cs31++[c]). simpl_env. auto.
Qed.

Definition pars_simulation (f1:fdef)
  (ps1 ps2:params) : Prop :=
  (if (fdef_dec sf f1) then
    (List.map
      (fun p =>
       let '(t, v):=p in
       (t, subst_value sid sv v)) ps1)
  else ps1) = ps2.

Lemma getEntryBlock__simulation: forall  f1 f2 b2,
  getEntryBlock f2 = Some b2 ->
  fdef_simulation  f1 f2 ->
  exists b1, getEntryBlock f1 = Some b1 /\ 
    block_simulation  f1 b1 b2.
Proof.
  unfold fdef_simulation.
  unfold block_simulation.
  intros.
  destruct (fdef_dec sf f1); inv H0; eauto.
    remember f1 as R1.
    destruct R1 as [[? ? ? a ?] b]; simpl in *.
    destruct b; simpl in *; inv H.
    exists b. 
    split; auto.
Qed.

Lemma fdef_simulation__entry_block_simulation: forall  F1 F2 B1 B2,
  fdef_simulation  F1 F2 ->
  getEntryBlock F1 = ret B1 ->
  getEntryBlock F2 = ret B2 ->
  block_simulation  F1 B1 B2.
Proof.
  intros.
  eapply getEntryBlock__simulation in H1; eauto.
  destruct H1 as [b1 [J1 J2]].
  uniq_result. auto.
Qed.

(* generalized? *)
Lemma fdef_simulation_inv: forall  fh1 fh2 bs1 bs2,
  fdef_simulation  (fdef_intro fh1 bs1) (fdef_intro fh2 bs2) ->
  fh1 = fh2 /\
  List.Forall2
    (fun b1 b2 => block_simulation  (fdef_intro fh1 bs1) b1 b2)
    bs1 bs2.
Proof.
  intros.
  unfold fdef_simulation in H.
  destruct (fdef_dec sf (fdef_intro fh1 bs1)) as [e|].
    rewrite <- e. clear e.
    simpl in H. inv H.
    split; auto.
      unfold block_simulation.
      destruct (fdef_dec sf sf);
        try congruence.
        clear.
        induction bs1; simpl; constructor; auto.

    inv H.
    split; auto.
      unfold block_simulation.
      destruct (fdef_dec sf (fdef_intro fh2 bs2));
        try congruence.
        clear.
        induction bs2; simpl; constructor; auto.
Qed.

Lemma pars_simulation_nil_inv: forall  f1 ps,
  pars_simulation  f1 nil ps -> ps = nil.
Proof.
  unfold pars_simulation. simpl.
  intros. destruct (fdef_dec sf f1); auto.
Qed.

Definition par_simulation (f1:fdef)
  (p p':typ * attributes * value) : Prop :=
(if (fdef_dec sf f1) then
  let '(t, v) := p in
  (t, v {[ sv // sid ]})
else p) = p'.

Lemma pars_simulation_cons_inv: forall  F p1 ps2 ps',
  pars_simulation  F (p1 :: ps2) ps' ->
  exists p1', exists ps2',
    ps' = p1' :: ps2' /\
    par_simulation  F p1 p1' /\
    pars_simulation  F ps2 ps2'.
Proof.
  intros.
  unfold pars_simulation, par_simulation in *.
  destruct p1.
  destruct (fdef_dec sf F); subst; simpl; eauto.
Qed.

Lemma par_simulation__value_simulation: forall  F t1 v1 t2 v2,
  par_simulation  F (t1,v1) (t2,v2) ->
  value_simulation  F v1 v2.
Proof.
  unfold par_simulation, value_simulation.
  intros.
  destruct (fdef_dec sf F); inv H; auto.
Qed.

Lemma params2GVs_sim_aux : forall
  (s : system) 
  los nts
  (ps : list product)
  (f : fdef)
  (i0 : id)
  n c t0 v0 v p2
  (cs : list cmd)
  (tmn : terminator)
  lc (gl : GVMap) 
  (Hwfg1 : wf_global (los,nts) s gl)
  (HwfF : wf_fdef s (module_intro los nts ps) f) (Huniq: uniqFdef f)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f
             (l1, stmts_intro ps1 (cs1 ++ insn_call i0 n c t0 v0 v p2 :: cs) tmn))
  (HbInF : blockInFdefB
            (l1, stmts_intro ps1 (cs1 ++ insn_call i0 n c t0 v0 v p2 :: cs) tmn) f =
          true)
  (l0 : list atom)
  (HeqR : ret l0 =
         inscope_of_cmd f
           (l1, stmts_intro ps1 (cs1 ++ insn_call i0 n c t0 v0 v p2 :: cs) tmn)
           (insn_call i0 n c t0 v0 v p2))
  (Hinscope : subst_inv.wf_defs (value_id sid)
           sv sf (los, nts) gl f lc l0)
  p22 p22' gvs gvs'
  (Hex : exists p21, p2 = p21 ++ p22)
  (Hp2gv : Opsem.params2GVs (los, nts) p22 lc gl = Some gvs)
  (Hp2gv' : Opsem.params2GVs (los, nts) p22' lc gl = Some gvs')
  (Hpasim : pars_simulation  f p22 p22'),
  gvs = gvs'.
Proof.
  induction p22; simpl; intros; eauto.
    apply pars_simulation_nil_inv in Hpasim. subst.
    simpl in *. congruence.

    destruct a as [[ty0 attr0] vl0].
    destruct Hex as [p21 Hex]; subst.
    apply pars_simulation_cons_inv in Hpasim.
    destruct Hpasim as [p1' [ps2' [EQ [Hpsim' Hpasim']]]]; subst.
    simpl in *. destruct p1'.
    inv_mbind'.

    assert (g0 = g) as Heq.
      apply par_simulation__value_simulation in Hpsim'.
      eapply getOperandValue_inCmdOperands_sim in Hpsim'; eauto.
        simpl. unfold valueInParams. right.
        assert (J:=@in_split_r _ _ (p21 ++ (ty0, attr0, vl0) :: p22)
          (ty0, attr0, vl0)).
        remember (split (p21 ++ (ty0, attr0, vl0) :: p22)) as R.
        destruct R.
        simpl in J. apply J.
        apply In_middle.
    subst.
    erewrite <- IHp22 with (gvs':=l2); eauto.
      exists (p21 ++ [(ty0, attr0,vl0)]). simpl_env. auto.
Qed.

Lemma params2GVs_sim : forall
  (s : system) 
  los nts
  (ps : list product)
  (f : fdef)
  (i0 : id)
  n c t0 v0 v p2
  (cs : list cmd)
  (tmn : terminator)
  lc (gl : GVMap) 
  (Hwfg1 : wf_global (los,nts) s gl)
  (HwfF : wf_fdef s (module_intro los nts ps) f) (Huniq: uniqFdef f)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f
             (l1, stmts_intro ps1 (cs1 ++ insn_call i0 n c t0 v0 v p2 :: cs) tmn))
  (HbInF : blockInFdefB
            (l1, stmts_intro ps1 (cs1 ++ insn_call i0 n c t0 v0 v p2 :: cs) tmn) f =
          true)
  (l0 : list atom)
  (HeqR : ret l0 =
         inscope_of_cmd f
           (l1, stmts_intro ps1 (cs1 ++ insn_call i0 n c t0 v0 v p2 :: cs) tmn)
           (insn_call i0 n c t0 v0 v p2))
  (Hinscope : subst_inv.wf_defs (value_id sid)
           sv sf (los, nts) gl f lc l0)
  p2' gvs gvs'
  (Hp2gv : Opsem.params2GVs (los, nts) p2 lc gl = Some gvs)
  (Hp2gv' : Opsem.params2GVs (los, nts) p2' lc gl = Some gvs')
  (Hpasim : pars_simulation  f p2 p2'),
  gvs = gvs'.
Proof.
  intros.
  eapply params2GVs_sim_aux; eauto.
    exists nil. auto.
Qed.

Definition list_sz_value_simulation (f1:fdef) vls vls': Prop :=
if (fdef_dec sf f1) then
  subst_list_value sid sv vls = vls'
else vls = vls'.

Inductive cmd_simulation' (F:fdef) : cmd -> cmd -> Prop :=
| cmd_simulation_bop : forall id0 bop0 sz0 v1 v2 v1' v2',
    value_simulation  F v1 v1' ->
    value_simulation  F v2 v2' ->
    cmd_simulation'  F (insn_bop id0 bop0 sz0 v1 v2)
                                    (insn_bop id0 bop0 sz0 v1' v2')
| cmd_simulation_fbop : forall id0 fbop0 fp0 v1 v2 v1' v2',
    value_simulation  F v1 v1' ->
    value_simulation  F v2 v2' ->
    cmd_simulation'  F (insn_fbop id0 fbop0 fp0 v1 v2)
                                    (insn_fbop id0 fbop0 fp0 v1' v2')
| cmd_simulation_extractvalue : forall id0 t0 v1 cs2 t1 v1',
    value_simulation  F v1 v1' ->
    cmd_simulation'  F (insn_extractvalue id0 t0 v1 cs2 t1)
                                    (insn_extractvalue id0 t0 v1' cs2 t1)
| cmd_simulation_insertvalue : forall id0 t0 v0 t1 v1 cs2 v0' v1',
    value_simulation  F v0 v0' ->
    value_simulation  F v1 v1' ->
    cmd_simulation'  F (insn_insertvalue id0 t0 v0 t1 v1 cs2)
                                    (insn_insertvalue id0 t0 v0' t1 v1' cs2)
| cmd_simulation_malloc : forall id0 t0 v0 al0 v0',
    value_simulation  F v0 v0' ->
    cmd_simulation'  F (insn_malloc id0 t0 v0 al0)
                                    (insn_malloc id0 t0 v0' al0)
| cmd_simulation_free : forall id0 t0 v0 v0',
    value_simulation  F v0 v0' ->
    cmd_simulation'  F (insn_free id0 t0 v0)
                                    (insn_free id0 t0 v0')
| cmd_simulation_alloca : forall id0 t0 v0 al0 v0',
    value_simulation  F v0 v0' ->
    cmd_simulation'  F (insn_alloca id0 t0 v0 al0)
                                    (insn_alloca id0 t0 v0' al0)
| cmd_simulation_load : forall id0 t0 v0 al0 v0',
    value_simulation  F v0 v0' ->
    cmd_simulation'  F (insn_load id0 t0 v0 al0)
                                    (insn_load id0 t0 v0' al0)
| cmd_simulation_store : forall id0 t0 v0 al0 v0' v1 v1',
    value_simulation  F v0 v0' ->
    value_simulation  F v1 v1' ->
    cmd_simulation'  F (insn_store id0 t0 v0 v1 al0)
                                    (insn_store id0 t0 v0' v1' al0)
| cmd_simulation_gep : forall id0 t0 v0 v0' vs1 vs1' t1 ib0,
    value_simulation  F v0 v0' ->
    list_sz_value_simulation  F vs1 vs1' ->
    cmd_simulation'  F (insn_gep id0 ib0 t0 v0 vs1 t1)
                                    (insn_gep id0 ib0 t0 v0' vs1' t1)
| cmd_simulation_trunc : forall id0 t0 v0 v0' t1 top0,
    value_simulation  F v0 v0' -> 
    cmd_simulation'  F (insn_trunc id0 top0 t0 v0 t1)
                                    (insn_trunc id0 top0 t0 v0' t1)
| cmd_simulation_ext : forall id0 t0 v0 v0' t1 eop0,
    value_simulation  F v0 v0' -> 
    cmd_simulation'  F (insn_ext id0 eop0 t0 v0 t1)
                                    (insn_ext id0 eop0 t0 v0' t1)
| cmd_simulation_cast : forall id0 t0 v0 v0' t1 cop0,
    value_simulation  F v0 v0' -> 
    cmd_simulation'  F (insn_cast id0 cop0 t0 v0 t1)
                                    (insn_cast id0 cop0 t0 v0' t1)
| cmd_simulation_icmp : forall id0 cond0 t0 v1 v2 v1' v2',
    value_simulation  F v1 v1' ->
    value_simulation  F v2 v2' ->
    cmd_simulation'  F (insn_icmp id0 cond0 t0 v1 v2)
                                    (insn_icmp id0 cond0 t0 v1' v2')
| cmd_simulation_fcmp : forall id0 fcond0 t0 v1 v2 v1' v2',
    value_simulation  F v1 v1' ->
    value_simulation  F v2 v2' ->
    cmd_simulation'  F (insn_fcmp id0 fcond0 t0 v1 v2)
                                    (insn_fcmp id0 fcond0 t0 v1' v2')
| cmd_simulation_select : forall id0 v0 t0 v1 v2 v1' v2' v0',
    value_simulation  F v0 v0' ->
    value_simulation  F v1 v1' ->
    value_simulation  F v2 v2' ->
    cmd_simulation'  F (insn_select id0 v0 t0 v1 v2)
                                    (insn_select id0 v0' t0 v1' v2')
| cmd_simulation_call : forall id0 nt0 ca0 t0 va0 v0 lp0 v0' lp0',
    value_simulation  F v0 v0' ->
    pars_simulation  F lp0 lp0' ->
    cmd_simulation'  F (insn_call id0 nt0 ca0 t0 va0 v0 lp0)
                                    (insn_call id0 nt0 ca0 t0 va0 v0' lp0')
.

Lemma value_simulation__refl: forall  F v,
  sf <> F ->
  value_simulation  F v v.
Proof.
  intros.
  unfold value_simulation.
  destruct (fdef_dec sf F); try solve [auto | congruence].
Qed.   

Lemma list_sz_value_simulation__refl: forall  F vs,
  sf <> F ->
  list_sz_value_simulation  F vs vs.
Proof.
  intros.
  unfold list_sz_value_simulation.
  destruct (fdef_dec sf F); try solve [auto | congruence].
Qed.

Lemma pars_simulation__refl: forall  F ps,
  sf <> F ->
  pars_simulation  F ps ps.
Proof.
  intros.
  unfold pars_simulation.
  destruct (fdef_dec sf F); try solve [auto | congruence].
Qed.

Lemma cmd_simulation'__refl: forall  F c,
  sf <> F ->
  cmd_simulation'  F c c.
Proof.
  intros.
  destruct c; constructor; 
    auto using value_simulation__refl, list_sz_value_simulation__refl,
               pars_simulation__refl.
Qed.

Lemma cmd_simulation__cmd_simulation': forall  F c c'
  (Hcsim: cmd_simulation  F c c'),
  cmd_simulation'  F c c'.
Proof.
  unfold cmd_simulation.
  intros.
  destruct (fdef_dec sf F); 
    subst c'; try subst F; auto using cmd_simulation'__refl.
    destruct c; simpl;
    constructor; try solve [
      unfold value_simulation, list_sz_value_simulation, pars_simulation;
      destruct (fdef_dec sf sf); try congruence; auto
    ].
Qed.

Lemma list_sz_value_simulation_nil_inv: forall  f1 idxs,
  list_sz_value_simulation  f1 nil idxs -> idxs = nil.
Proof.
  unfold list_sz_value_simulation. simpl.
  intros. destruct_if; auto.
Qed.

Definition sz_value_simulation (f1:fdef) (idx idx':sz * value) : Prop :=
(if (fdef_dec sf f1) then
  let '(sz0, v) := idx in
  (sz0, v {[ sv // sid  ]})
else idx) = idx'.

Lemma list_sz_value_simulation_cons_inv: forall  F idx1 idxs2 idxs',
  list_sz_value_simulation  F (idx1 :: idxs2) idxs' ->
  exists idx1', exists idxs2',
    idxs' = idx1' :: idxs2' /\
    sz_value_simulation  F idx1 idx1' /\
    list_sz_value_simulation  F idxs2 idxs2'.
Proof.
  intros.
  unfold list_sz_value_simulation, sz_value_simulation in *.
  destruct idx1.
  destruct_if; subst; simpl; eauto.
Qed.

Lemma sz_value_simulation__value_simulation: forall F t1 v1 t2 v2,
  sz_value_simulation  F (t1,v1) (t2,v2) ->
  value_simulation  F v1 v2.
Proof.
  unfold sz_value_simulation, value_simulation.
  intros.
  destruct_if; auto.
Qed.

Lemma values2GVs_sim_aux : forall los nts s gl ps (f : fdef)
  (HwfF : wf_fdef s (module_intro los nts ps) f) (Huniq: uniqFdef f)
  (tmn : terminator)
  (lc : GVMap)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 cs : list cmd)
  (c : cmd)
  (Hreach : isReachableFromEntry f (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_cmd f (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn) c)
  (Hinscope : subst_inv.wf_defs (value_id sid) sv sf
                     (los, nts) gl f lc l0) t' t v id0 inbounds0 
  idxs0 (Heq: insn_gep id0 inbounds0 t v idxs0 t' = c) 
  idxs idxs' vidxss vidxss'
  (Hex: exists idxs1, idxs0 = idxs1 ++ idxs)  
  (Hget' :  @Opsem.values2GVs DGVs (los, nts) idxs lc gl = ret vidxss)
  (Hvsim : list_sz_value_simulation  f idxs idxs')
  (Hget : @Opsem.values2GVs DGVs (los, nts) idxs' lc gl = ret vidxss'),
  vidxss = vidxss'.
Proof.
  induction idxs as [|[]]; simpl; intros.
    uniq_result. 
    apply list_sz_value_simulation_nil_inv in Hvsim. subst. 
    simpl in Hget. 
    uniq_result. auto.

    inv_mbind.
    apply list_sz_value_simulation_cons_inv in Hvsim.
    destruct Hvsim as [idx1' [idxs2' [EQ [Hvsim1 Hvsim2]]]]; subst.
    simpl in Hget.
    inv_mbind.
    destruct Hex as [idxs1 Hex]; subst.
    assert (g = g0) as Heq.
      apply sz_value_simulation__value_simulation in Hvsim1.
      eapply getOperandValue_inCmdOperands_sim in Hvsim1; eauto.
        simpl. unfold valueInParams. right.
        unfold valueInListValue.
        rewrite List.map_app. simpl.
        apply In_middle.
    subst.
    erewrite IHidxs with (vidxss:=l2); eauto.
      exists (idxs1 ++ [(s0,v0)]). simpl_env. auto.
Qed.

Lemma values2GVs_sim : forall los nts s gl ps (f : fdef) 
  (HwfF : wf_fdef s (module_intro los nts ps) f) (Huniq: uniqFdef f)
  (tmn : terminator)
  (lc : GVMap)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 cs : list cmd)
  (c : cmd)
  (Hreach : isReachableFromEntry f (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_cmd f (l1, stmts_intro ps1 (cs1 ++ c :: cs) tmn) c)
  (Hinscope : subst_inv.wf_defs (value_id sid)
                     sv sf
                     (los, nts) gl f lc l0) t' t v id0 inbounds0 
  idxs idxs' (Heq: insn_gep id0 inbounds0 t v idxs t' = c) vidxss vidxss'
  (Hget' :  @Opsem.values2GVs DGVs (los, nts) idxs lc gl = ret vidxss)
  (Hvsim : list_sz_value_simulation  f idxs idxs')
  (Hget : @Opsem.values2GVs DGVs (los, nts) idxs' lc gl = ret vidxss'),
  vidxss = vidxss'.
Proof.
  intros.
  eapply values2GVs_sim_aux with (idxs0:=idxs)(idxs:=idxs)(idxs':=idxs'); eauto.
    exists nil. auto.
Qed.

Ltac destruct_ctx_return :=
match goal with
| Hwfcfg: OpsemPP.wf_Config _,
  Hwfpp : OpsemPP.wf_State
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |} _,
  HwfS1 : wf_State _ _ _ _ _,
  Hsim : State_simulation _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]];
  destruct Hwfpp as 
    [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [ _ HwfCall'
     ]]
    ]; subst;
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  simpl in Hsim;
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 EQ4]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim Hstksim];
  destruct ECs2 as [|[F3 B3 cs3 tmn3 lc3 als3] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim' Hstksim];
  unfold EC_simulation in Hecsim;
  destruct Hecsim as 
      [Hfsim2 [Htsim2 [Heq2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct Hecsim' as 
      [Hfsim2' [Htsim2' [Heq2' [Hbsim2' 
        [Heq3' [Heq4' [Hlcsim2' Hcssim2']]]]]]]; subst;
  destruct HwfS1 as [Hinscope1' [Hinscope2' HwfECs']];
  fold wf_ECStack in HwfECs';
  unfold wf_ExecutionContext in Hinscope1', Hinscope2';
  simpl in Hinscope1', Hinscope2';
  apply cmds_simulation_nil_inv in Hcssim2; subst;
  apply cmds_simulation_cons_inv in Hcssim2'; 
  destruct Hcssim2' as [c1' [cs3' [Heq [Hcsim2' Hcssim2']]]]; subst
end.

Ltac destruct_ctx_other :=
match goal with
| Hwfcfg: OpsemPP.wf_Config _,
  Hwfpp : OpsemPP.wf_State
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |} _,
  HwfS1 : wf_State _ _ _ _ _,
  Hsim : State_simulation _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfcfg as [_ [Hwfg [HwfSystem HmInS]]];
  destruct Hwfpp as 
    [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [HwfECs Hwfcall]]
    ]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs;
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  simpl in Hsim;
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 EQ4]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim Hstksim];
  unfold EC_simulation in Hecsim;
  destruct Hecsim as 
      [Hfsim2 [Htsim2 [Heq2 [Hbsim2 
        [[l3 [ps3 [cs31 Heq3]]]
        [[l4 [ps4 [cs41 Heq4]]] [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct HwfS1 as [Hinscope1' HwfECs'];
  fold wf_ECStack in HwfECs';
  unfold wf_ExecutionContext in Hinscope1';
  simpl in Hinscope1'
end.

Ltac subst_is_sim_tac :=
  destruct_ctx_other;
  match goal with
  | Hcssim2: cmds_simulation _ _ _,
    Hop2: Opsem.sInsn _ _ _ _ |- _ =>
    apply cmds_simulation_cons_inv in Hcssim2;
    destruct Hcssim2 as [c1' [cs3' [Heq [Hcsim2 Hcssim2]]]]; subst;
    apply cmd_simulation__cmd_simulation' in Hcsim2;
    inv Hcsim2;
    inv Hop2
  end;
  repeat (split; eauto 2 using cmds_at_block_tail_next');
    f_equal;
    match goal with
    | _: moduleInSystemB (module_intro ?los ?nts ?Ps) ?S = true,
      _: InProductsB (product_fdef ?F) ?Ps = true |- _ =>
      assert (wf_fdef S (module_intro los nts Ps) F) as HwfF;
        eauto using wf_system__wf_fdef;
      assert (uniqFdef F) as Huniq; eauto using wf_system__uniqFdef;
      unfold Opsem.BOP, Opsem.FBOP, Opsem.GEP, Opsem.TRUNC, Opsem.EXT,
        Opsem.CAST, Opsem.ICMP, Opsem.FCMP in *;
      inv_mbind'; inv_mfalse; app_inv; symmetry_ctx;
      repeat match goal with
      | HeqR : Opsem.getOperandValue _ ?v1 _ _ = ret _,
        HeqR' : Opsem.getOperandValue _ ?v1' _ _ = ret _,
        Hvsim1 : value_simulation _ ?v1 ?v1'|- _ =>
        eapply getOperandValue_inCmdOperands_sim with (v':=v1') in HeqR;
          try (eauto || simpl; auto); subst;
        clear Hvsim1 HeqR'
      | HeqR : Opsem.values2GVs _ ?vs _ _ = ret _,
        HeqR' : Opsem.values2GVs _ ?vs' _ _ = ret _,
        Hvsim1 : list_sz_value_simulation _ ?vs ?vs'|- _ =>
        eapply values2GVs_sim with (idxs':=vs') in HeqR;
          try (eauto || simpl; auto); subst;
        clear Hvsim1 HeqR'
      end;
      uniq_result; auto
    end.

(* preserving backward simulation *)
Lemma step_sim : forall  Cfg1 St1 Cfg2 St2 St2' tr2 tr1 St1'
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (HwfS1: subst_inv.wf_State (value_id sid) sv sf Cfg1 St1)
  (Hsim: State_simulation  Cfg1 St1 Cfg2 St2)
  (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2)
  (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1),
  State_simulation  Cfg1 St1' Cfg2 St2' /\ tr1 = tr2.
Proof.

Local Opaque inscope_of_tmn inscope_of_cmd.

  intros.
  (sInsn_cases (destruct Hop1) Case).

Case "sReturn".

  destruct_ctx_return.

  assert (exists Result2,
    tmn2 = insn_return rid RetTy Result2 /\
    value_simulation  F Result Result2) as Hreturn.
    clear - Htsim2.
    unfold value_simulation, tmn_simulation in *.
    destruct (fdef_dec sf F); inv Htsim2; eauto.
  destruct Hreturn as [Result2 [EQ Hvsim2]]; subst.

  inv Hop2.

  match goal with
  | H0 : free_allocas ?td ?M ?las = _,
    H26 : free_allocas ?td ?M ?las = _ |- _ =>
      rewrite H0 in H26; inv H26
  end.
  wfCall_inv.

  assert (lc'' = lc''0) as EQ.
    clear - H27 H1 Hcsim2' Hvsim2 Hinscope1' HwfSystem HmInS Hreach1 HBinF1
      HFinPs1 Hwfg.
    unfold Opsem.returnUpdateLocals in H1, H27.
    inv_mbind'.
    destruct_cmd c1'; tinv H0.
    assert (i0 = i1 /\ n = n0 /\ t0 = t1) as EQ.
      unfold cmd_simulation in Hcsim2';
      destruct (fdef_dec sf F'); inv Hcsim2'; auto.
    destruct EQ as [Heq1 [Heq2 Heq3]]; subst.
    destruct n0; try solve [inv H0; inv H2; auto].
    inv_mbind'.
    symmetry_ctx.
    eapply getOperandValue_inTmnOperands_sim in HeqR0; eauto
      using wf_system__wf_fdef, wf_system__uniqFdef; simpl; auto.
    subst. uniq_result. auto.

  subst.
  repeat (split; eauto 2 using cmds_at_block_tail_next).

Case "sReturnVoid".
  destruct_ctx_return.

  assert (tmn2 = insn_return_void rid) as Hreturn.
    clear - Htsim2.
    unfold value_simulation, tmn_simulation in *.
    destruct (fdef_dec sf F); inv Htsim2; auto.
  subst.

  inv Hop2.

  match goal with
  | H0 : free_allocas ?td ?M ?las = _,
    H26 : free_allocas ?td ?M ?las = _ |- _ =>
      rewrite H0 in H26; inv H26
  end.
  wfCall_inv.
  repeat (split; eauto 2 using cmds_at_block_tail_next).

Case "sBranch".
Focus.

  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.

  assert (exists Cond2,
    tmn2 = insn_br bid Cond2 l1 l2 /\
    value_simulation  F Cond Cond2) as Hbr.
    clear - Htsim2.
    unfold value_simulation, tmn_simulation in *.
    destruct (fdef_dec sf F); inv Htsim2; eauto.
  destruct Hbr as [Cond2 [EQ Hvsim2]]; subst.

  inv Hop2.
  uniq_result.
  remember (inscope_of_tmn F (l3, stmts_intro ps3 (cs31 ++ nil)
             (insn_br bid Cond l1 l2)) (insn_br bid Cond l1 l2)) as R.
  destruct R; tinv Hinscope1'.

  assert (uniqFdef F) as HuniqF.
    eauto using wf_system__uniqFdef.
  assert (wf_fdef S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.
  assert (c = c0)as Heq.
    eapply getOperandValue_inTmnOperands_sim with (v:=Cond)(v':=Cond2);
      try solve [eauto | simpl; auto].
  subst.
  assert (block_simulation F
           (if isGVZero (los, nts) c0 then l2 else l1, stmts_intro ps' cs' tmn')
           (if isGVZero (los, nts) c0 then l2 else l1, stmts_intro ps'0 cs'0 tmn'0)) 
    as Hbsim.
    clear - H22 H1 Hfsim2.
    destruct (isGVZero (los, nts) c0); eauto using fdef_sim__block_sim.
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'.
  destruct Hbsim' as [_ [Hpsim' [Hcssim' Htsim']]]; subst.

  assert (isReachableFromEntry F 
           (if isGVZero (los, nts) c0 then l2 else l1, 
            stmts_intro ps' cs' tmn') /\
    In (if isGVZero (los, nts) c0 then l2 else l1) 
        (successors_terminator (insn_br bid Cond l1 l2)) /\
    blockInFdefB (if isGVZero (los, nts) c0 then l2 else l1, 
                  stmts_intro ps' cs' tmn') F = true) as J.
    symmetry in H1.
    destruct (isGVZero (los,nts) c0);
      assert (J:=H1);
      apply lookupBlockViaLabelFromFdef_inv in J; eauto;
      (repeat split; auto); try solve [
        auto | eapply reachable_successors in HBinF1; (eauto || simpl; auto)].
  destruct J as [Hreach' [Hsucc' HBinF1']].

  assert (lc' = lc'0) as Heq.
    eapply switchToNewBasicBlock_sim in Hbsim; eauto.
  subst.
  repeat (split; auto).
    exists (if isGVZero (los, nts) c0 then l2 else l1). 
    exists ps'. exists nil. auto.

    exists (if isGVZero (los, nts) c0 then l2 else l1). 
    exists ps'0. exists nil. auto.

Unfocus.

Case "sBranch_uncond".
Focus.

  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.

  assert (tmn2 = insn_br_uncond bid l0) as Hbr.
    clear - Htsim2.
    unfold value_simulation, tmn_simulation in *.
    destruct (fdef_dec sf F); inv Htsim2; eauto.
  subst.

  inv Hop2.
  uniq_result.
  remember (inscope_of_tmn F (l3, stmts_intro ps3 (cs31 ++ nil)
             (insn_br_uncond bid l0)) (insn_br_uncond bid l0)) as R.
  destruct R; tinv Hinscope1'.

  assert (uniqFdef F) as HuniqF.
    eauto using wf_system__uniqFdef.
  assert (wf_fdef S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.

  assert (block_simulation  F
           (l0, stmts_intro ps' cs' tmn')
           (l0, stmts_intro ps'0 cs'0 tmn'0)) as Hbsim.
    clear - H H16 Hfsim2.
    eauto using fdef_sim__block_sim.
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'.
  destruct Hbsim' as [_ [Hpsim' [Hcssim' Htsim']]]; subst.

  assert (isReachableFromEntry F (l0, stmts_intro ps' cs' tmn') /\
    In l0 (successors_terminator (insn_br_uncond bid l0)) /\
    blockInFdefB (l0, stmts_intro ps' cs' tmn') F = true) as J.
    symmetry in H;
    assert (J:=H);
    apply lookupBlockViaLabelFromFdef_inv in J; eauto;
    (repeat split; auto); try solve [
      auto | eapply reachable_successors in HBinF1; (eauto || simpl; auto)].
  destruct J as [Hreach' [Hsucc' HBinF1']].

  assert (lc' = lc'0) as Heq.
    eapply switchToNewBasicBlock_sim in Hbsim; eauto.
  subst.
  repeat (split; auto).
    exists l0. exists ps'. exists nil. auto.
    exists l0. exists ps'0. exists nil. auto.

Unfocus.

Case "sBop". abstract subst_is_sim_tac.
Case "sFBop". abstract subst_is_sim_tac.
Case "sExtractValue". abstract subst_is_sim_tac.
Case "sInsertValue". abstract subst_is_sim_tac.
Case "sMalloc". abstract subst_is_sim_tac.
Case "sFree". abstract subst_is_sim_tac.
Case "sAlloca". abstract subst_is_sim_tac.
Case "sLoad". abstract subst_is_sim_tac.
Case "sStore". abstract subst_is_sim_tac.
Case "sGEP". abstract subst_is_sim_tac.
Case "sTrunc". abstract subst_is_sim_tac.
Case "sExt". abstract subst_is_sim_tac.
Case "sCast". abstract subst_is_sim_tac.
Case "sIcmp". abstract subst_is_sim_tac.
Case "sFcmp". abstract subst_is_sim_tac.
Case "sSelect". abstract subst_is_sim_tac.
Case "sCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_cons_inv in Hcssim2.
  destruct Hcssim2 as [c1' [cs3' [Heq [Hcsim2 Hcssim2]]]]; subst.

  assert (exists fv', exists lp',
    c1' = insn_call rid noret0 ca rt1 va1 fv' lp' /\
    value_simulation  F fv fv' /\
    pars_simulation  F lp lp') as Hcmd.
    clear - Hcsim2.
    unfold value_simulation, cmd_simulation, pars_simulation in *.
    destruct (fdef_dec sf F); inv Hcsim2; eauto.
  destruct Hcmd as [fv' [lp' [Heq [Hvsim Hpasim]]]]; subst.

  assert (wf_fdef S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.
  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.

  inv Hop2.

  SCase "SCall".

  uniq_result.

  assert (fptr = fptr0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=fv') in H;
      try (eauto || simpl; auto).
  subst. clear H.

  assert (Hfsim1:=Hpsim).
  eapply TopSim.lookupFdefViaPtr__simulation in Hfsim1; eauto.
  simpl in Hfsim1.
  assert (Hbsim1:=Hfsim1).
  eapply fdef_simulation__entry_block_simulation in Hbsim1; eauto.
  assert (Hbsim1':=Hbsim1).
  apply block_simulation_inv in Hbsim1'.
  destruct Hbsim1' as [Heq' [Hpsim1' [Hcsim1' Htsim1']]]; subst.
  repeat (split; eauto 4).
    exists l'0. exists ps'. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    assert (gvs = gvs0) as EQ.
      inv_mfalse; symmetry_ctx.
      eapply params2GVs_sim; eauto.
    subst.
    clear - H4 H32 Hfsim1.
    apply fdef_simulation_inv in Hfsim1.
    destruct Hfsim1 as [Heq _]. inv Heq. uniq_result.
    auto.

  SCase "sExCall".

  uniq_result.

  assert (fptr = fptr0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=fv') in H;
      try (eauto || simpl; auto).
  subst. clear H.
  clear - H29 H1 Hpsim.

  eapply TopSim.lookupFdefViaPtr__simulation_l2r in H1; eauto.
  destruct H1 as [f2 [H1 H2]].
  apply OpsemAux.lookupExFdecViaPtr_inversion in H29.
  apply OpsemAux.lookupFdefViaPtr_inversion in H1.
  destruct H29 as [fn [J1 [J2 J3]]].
  destruct H1 as [fn' [J4 J5]].
  uniq_result.

Case "sExCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_cons_inv in Hcssim2.
  destruct Hcssim2 as [c1' [cs3' [Heq [Hcsim2 Hcssim2]]]]; subst.

  assert (exists fv', exists lp',
    c1' = insn_call rid noret0 ca rt1 va1 fv' lp' /\
    value_simulation  F fv fv' /\
    pars_simulation F lp lp') as Hcmd.
    clear - Hcsim2.
    unfold value_simulation, cmd_simulation, pars_simulation in *.
    destruct (fdef_dec sf F); inv Hcsim2; eauto.
  destruct Hcmd as [fv' [lp' [Heq [Hvsim Hpasim]]]]; subst.

  assert (wf_fdef S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.
  assert (uniqFdef F) as Huniq. eauto using wf_system__uniqFdef.

  inv Hop2.

  SCase "SCall".

  uniq_result.

  assert (fptr = fptr0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=fv') in H;
      try (eauto || simpl; auto).
  subst. clear H.

  match goal with
  | Hpsim: products_simulation ?Ps ?Ps2,
    H1: OpsemAux.lookupExFdecViaPtr ?Ps _ _ = _,
    H30: OpsemAux.lookupFdefViaPtr ?Ps2 _ _ = _ |- _ =>
    clear - H30 H1 Hpsim;
    eapply TopSim.lookupExFdecViaPtr__simulation_l2r in H1; eauto;
    simpl in Hpsim;
    apply OpsemAux.lookupExFdecViaPtr_inversion in H1;
    apply OpsemAux.lookupFdefViaPtr_inversion in H30;
    destruct H1 as [fn [J1 [J2 J3]]];
    destruct H30 as [fn' [J4 J5]]
  end.

  uniq_result.

  SCase "sExCall".

  uniq_result.

  assert (fptr = fptr0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=fv') in H;
      try (eauto || simpl; auto).
  subst. clear H.

  assert (Hlkdec:=Hpsim).
  eapply TopSim.lookupExFdecViaPtr__simulation_l2r in Hlkdec; eauto.

  assert (gvss = gvss0) as EQ.
    inv_mfalse; symmetry_ctx.
    eapply params2GVs_sim; eauto.
  subst.
  uniq_result.

  repeat (split; eauto 2 using cmds_at_block_tail_next').

Transparent inscope_of_tmn inscope_of_cmd.

Qed.

(* Properties for initial states, final states and stuck states. *)
Lemma s_genInitState__subst_State_simulation: forall S1 S2 main
  VarArgs cfg2 IS2
  (Hssim: system_simulation S1 S2)
  (Hinit: Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2)),
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation cfg1 IS1 cfg2 IS2.
Proof.
  s_genInitState__State_simulation_tac.
  assert (J:=HeqR2).
  eapply getEntryBlock__simulation in J; eauto.
  destruct J as [b1 [J5 J6]].
  fill_ctxhole.
  destruct b1 as [l2 [ps2 cs2 tmn2]].
  assert (J:=Hfsim).
  apply fdef_simulation__eq_fheader in J.
  inv J.
  fill_ctxhole.
  match goal with
  | |- exists _:_, exists _:_, Some (?A, ?B) = _ /\ _ => exists A; exists B
  end.
  assert (J:=J6).
  apply block_simulation_inv in J.
  destruct J as [J1 [J2 [J3 J7]]]; subst.
  repeat (split; auto).
    exists l0. exists ps2. exists nil. auto.
    exists l0. exists ps0. exists nil. auto.
Qed.

Lemma cmds_simulation_nil_inv' : forall (f1 : fdef) (cs : list cmd),
  cmds_simulation f1 cs nil -> cs = nil.
Proof.
  unfold cmds_simulation. intros.
  destruct_if; auto.
    destruct cs; inv H1; auto.
Qed.

Lemma cmds_simulation_cons_inv' : forall (f1 : fdef) (cs : list cmd) c2 cs2,
  cmds_simulation f1 cs (c2::cs2) -> 
  exists c1, exists cs1, 
    cs = c1::cs1 /\
    cmd_simulation f1 c1 c2 /\
    cmds_simulation f1 cs1 cs2.
Proof.
  unfold cmds_simulation, cmd_simulation. intros.
  destruct_if; eauto.
    destruct cs; inv H1; eauto.
Qed.

Inductive tmn_simulation' (F:fdef) : terminator -> terminator -> Prop :=
| tmn_simulation_return : forall id0 t0 v v',
    value_simulation F v v' ->
    tmn_simulation' F (insn_return id0 t0 v) (insn_return id0 t0 v')
| tmn_simulation_return_void : forall id0,
    tmn_simulation' F (insn_return_void id0) (insn_return_void id0)
| tmn_simulation_br : forall id0 v v' l1 l2,
    value_simulation F v v' ->
    tmn_simulation' F (insn_br id0 v l1 l2) (insn_br id0 v' l1 l2)
| tmn_simulation_br_uncond : forall id0 l0,
    tmn_simulation' F (insn_br_uncond id0 l0) (insn_br_uncond id0 l0)
| tmn_simulation_unreachable : forall id0,
    tmn_simulation' F (insn_unreachable id0) (insn_unreachable id0)
.

Lemma tmn_simulation'__refl: forall F t,
  sf <> F ->
  tmn_simulation' F t t.
Proof.
  intros.
  destruct t; constructor; auto using value_simulation__refl.
Qed.

Lemma tmn_simulation__tmn_simulation': forall F t t'
  (Htsim: tmn_simulation F t t'),
  tmn_simulation' F t t'.
Proof.
  unfold tmn_simulation.
  intros.
  destruct (fdef_dec sf F); subst t'; try subst F; 
    auto using tmn_simulation'__refl.
    destruct t; simpl;
    constructor; try solve [
      unfold value_simulation;
      destruct (fdef_dec sf sf); try congruence; auto
    ].
Qed.

Ltac tmnOps_eq H3 Hwfcfg1 Hwfpp1 HwfS1 :=
      destruct H3 as [l1 [ps1 [cs11 H3]]]; subst;
      destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
      destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
      destruct HwfS1 as [HwfS1 _];
      unfold wf_ExecutionContext, inscope_of_ec in HwfS1;
      inv_mbind;
      eapply getOperandValue_inTmnOperands_sim; 
        eauto 2 using wf_system__wf_fdef, wf_system__uniqFdef; simpl; auto.

Lemma s_isFinialState__subst_State_simulation: forall
  cfg1 FS1 cfg2 FS2
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 FS1) 
  (Hwfcfg2: OpsemPP.wf_Config cfg2) (Hwfpp2: OpsemPP.wf_State cfg2 FS2) 
  (HwfS1: subst_inv.wf_State (value_id sid) sv sf cfg1 FS1)
  (Hstsim : State_simulation cfg1 FS1 cfg2 FS2),
  Opsem.s_isFinialState cfg1 FS1 = Opsem.s_isFinialState cfg2 FS2.
Proof.
  unfold Opsem.s_isFinialState.
  intros.
  destruct cfg2 as [S2 [los2 nts2] gl2 fs2].
  destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
  destruct FS1 as [[|[? ? cs1 ? ?] ES1]]; 
  destruct FS2 as [[|[? ? cs2 ? ?] ES2]]; try solve [
    auto |
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst; inv Hstsim
  ].
  destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst.
  inv X. simpl.
  destruct Hstsim as [Hstsim Hstsim'].
  fold ECs_simulation in Hstsim'.
  destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst.
  destruct cs1, cs2; try solve [
    auto |
    apply cmds_simulation_nil_inv in Hstsim; try congruence |
    apply cmds_simulation_nil_inv' in Hstsim; try congruence
  ].
  apply tmn_simulation__tmn_simulation' in Htmn.
  inv Htmn; auto.
    destruct ES1, ES2; try solve [auto | inv Hstsim'].
      inTmnOp_isnt_stuck v H3 Hwfcfg1 Hwfpp1.
      inTmnOp_isnt_stuck v' H4 Hwfcfg2 Hwfpp2.
      rewrite G. rewrite G0.
      f_equal.
      tmnOps_eq H3 Hwfcfg1 Hwfpp1 HwfS1.

    destruct ES1, ES2; try solve [auto | inv Hstsim'].
Qed.

Ltac undefined_state__State_simulation_r2l_tac1 :=
  match goal with
  | Hstsim: State_simulation _ ?St1 _ ?St2 |- _ =>
    destruct St2 as [[|[? ? [|CurCmds] [] ?] [|[]]] ?]; try tauto;
    destruct CurCmds; try tauto;
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X;
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [Hstsim Hstsim'];
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
    destruct Hstsim' as [Hstsim' _];
    destruct Hstsim' as [? [? [? [? [? [? [? Hstsim']]]]]]]; subst;
   simpl
  end.

Ltac undefined_state__State_simulation_r2l_tac3 :=
  match goal with
  | Hstsim: State_simulation _ ?St1 _ ?St2 |- _ =>
    destruct St2 as [[|[? [? [? ? tmn]] CurCmds tmn' ?] ?] ?]; try tauto;
    destruct tmn; try tauto;
    destruct CurCmds; try tauto;
    destruct tmn'; try tauto;
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? H3]]]]]; subst;
    inv X;
    destruct ECS as [|[] ECS]; try tauto;
    destruct Hstsim as [Hstsim _];
    destruct Hstsim as [? [Htmn [? [? [? [? [? Hstsim]]]]]]]; subst;
    let l5 := fresh "l5" in
    destruct H3 as [l5 [ps5 [cs5 EQ]]]; subst
  end.

Ltac undefined_state__State_simulation_r2l_tac41 :=
  match goal with
  | Hstsim: State_simulation _ ?St1 ?cfg2 ?St2 |- _ =>
    destruct St1 as [ECS ?];
    destruct Hstsim as [X [? [Hstsim [? [? ?]]]]]; subst;
    inv X;
    destruct ECS as [|[? ? ? ? Locals0] ECS]; try tauto;
    destruct Hstsim as [Hstsim _];
    destruct Hstsim as [? [? [? [? [H4 [H5 [? Hstsim]]]]]]]; subst
  end. 

Ltac undefined_state__subst_State_simulation_r2l_tac42 := 
repeat match goal with
| Hwfcfg1: OpsemPP.wf_Config ?cfg1, Hwfpp1: OpsemPP.wf_State ?cfg1 ?St1, 
  HwfS1: wf_State _ _ _ ?cfg1 ?St1, 
  Hvsim: value_simulation _ ?v0 ?v,
  _: ret ?gn = Opsem.getOperandValue ?td ?v ?Locals ?fs2,
  _: block_simulation _ ?b _,
  H4: exists _:_, exists _:_, exists _:_, ?b = _ |- _ =>
    let G := fresh "G" in
    let gvs := fresh "gvs" in
    assert (exists gvs, Opsem.getOperandValue td
       v0 Locals fs2 = Some gvs) as G; try solve [
      destruct H4 as [l5 [ps2 [cs21 H4]]]; subst;
      destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
      destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
      inv_mbind;
      eapply OpsemPP.getOperandValue_inCmdOps_isnt_stuck; eauto 1; simpl; auto
    ];
    destruct G as [gvs G];
    assert (gvs = gn) as EQ; try solve [
      destruct H4 as [l1 [ps1 [cs11 H4]]]; subst;
      destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
      destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
      destruct HwfS1 as [HwfS1 _];
      unfold wf_ExecutionContext, inscope_of_ec in HwfS1;
      inv_mbind;
      eapply getOperandValue_inCmdOperands_sim; 
        eauto 2 using wf_system__wf_fdef, wf_system__uniqFdef; simpl; auto
    ];
    subst;
    clear Hvsim
end.

Ltac undefined_state__subst_State_simulation_r2l_tac43 := 
      match goal with
      | Hstsim: cmds_simulation _ _ (_::_) |- _ =>
      apply cmds_simulation_cons_inv' in Hstsim; subst;
      destruct Hstsim as [c1' [cs2' [J1 [J2 J3]]]]; subst;
      apply cmd_simulation__cmd_simulation' in J2;
      inv J2;
      undefined_state__subst_State_simulation_r2l_tac42
     end.

Lemma undefined_state__subst_State_simulation_r2l: forall cfg1 St1 
  cfg2 St2 (Hstsim : State_simulation cfg1 St1 cfg2 St2)
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfpp1: OpsemPP.wf_State cfg1 St1) 
  (HwfS1: subst_inv.wf_State (value_id sid) sv sf cfg1 St1)
  (Hundef: OpsemPP.undefined_state cfg2 St2), OpsemPP.undefined_state cfg1 St1.
Proof.
  intros.
  unfold OpsemPP.undefined_state in Hundef.
  destruct cfg2 as [S2 [los2 nts2] gl2 fs2].
  destruct cfg1 as [S1 [los1 nts1] gl1 fs1].
  repeat match goal with
  | Hundef : _ \/ _ |- _ => destruct Hundef as [Hundef | Hundef]
  end.
  Case "1".

    undefined_state__State_simulation_r2l_tac1.
    apply cmds_simulation_nil_inv' in Hstsim; subst.
    apply cmds_simulation_cons_inv' in Hstsim'.
    destruct Hstsim' as [c1' [cs1' [J1 [J2 J3]]]]; subst.
    left. 
    unfold tmn_simulation in Htmn. 
    destruct_if; try clear e; subst; simpl; auto.
    match goal with
    | H11: subst_tmn _ _ ?tmn = insn_return _ _ _ |- _ => 
        destruct tmn; inv H11; auto
    end.

  Case "2".
    undefined_state__State_simulation_r2l_tac1.
    apply cmds_simulation_nil_inv' in Hstsim; subst.
    apply cmds_simulation_cons_inv' in Hstsim'.
    destruct Hstsim' as [c1' [cs1' [J1 [J2 J3]]]]; subst.
    right. left.
    assert (getCallerReturnID c = getCallerReturnID c1') as EQ.
      unfold cmd_simulation in J2. subst. clear.
      destruct_if; auto.
      destruct c1'; auto.
    rewrite <- EQ.
    clear - Htmn Hundef.
    unfold tmn_simulation in Htmn. 
    destruct (fdef_dec sf CurFunction1); try clear e; subst; simpl; auto.
    match goal with
    | H11: subst_tmn _ _ ?tmn = insn_return_void _ |- _ => 
        destruct tmn; inv H11; auto
    end.

  Case "3".
    undefined_state__State_simulation_r2l_tac3.
    apply cmds_simulation_nil_inv' in Hstsim. subst.
    right. right. left.
    simpl. 
    unfold tmn_simulation in Htmn. 
    destruct_if; try clear e; subst; simpl; auto.
    match goal with
    | H11: subst_tmn _ _ ?tmn = insn_unreachable _ |- _ => 
      destruct tmn; inv H11; auto
    end.

  Case "4".

    right; right; right; left;
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' Locals] ?] ?]; try solve [
      tauto |

      inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind;
      undefined_state__State_simulation_r2l_tac41;
      undefined_state__subst_State_simulation_r2l_tac43;
        repeat fill_ctxhole; exists gn; fill_ctxhole; auto
    ].

  Case "5".
    right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gn [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__subst_State_simulation_r2l_tac43.
    repeat fill_ctxhole; exists gn; fill_ctxhole; auto.

  Case "6".
    right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gvs [EQ Hundef]]; inv EQ; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__subst_State_simulation_r2l_tac43. 
    repeat fill_ctxhole; exists gvs; fill_ctxhole; auto.

  Case "7".
    right. right. right. right. right. right. left.
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    inv_mbind; destruct Hundef as [gv [mgv [EQ1 [EQ2 Hundef]]]]; 
      inv EQ1; inv EQ2; inv_mbind.
    undefined_state__State_simulation_r2l_tac41.
    undefined_state__subst_State_simulation_r2l_tac43. 
    repeat fill_ctxhole; exists gv; exists mgv; fill_ctxhole; auto.

  Case "8".
    destruct St2 as [[|[? ? [|[] CurCmds] tmn' ?] ?] ?]; try tauto.
    right; right; right; right. right. right. right.
    undefined_state__State_simulation_r2l_tac41.
    inv_mbind.
    destruct Hundef as [fptr [EQ Hundef]]; inv EQ.
    inv_mbind.
    apply cmds_simulation_cons_inv' in Hstsim; subst;
    destruct Hstsim as [c1' [cs2' [J1 [J2 J3]]]]; subst.
    apply cmd_simulation__cmd_simulation' in J2;
    inv J2.  
    undefined_state__subst_State_simulation_r2l_tac42.
    repeat fill_ctxhole.
    exists fptr. split; auto.
    remember (OpsemAux.lookupExFdecViaPtr gl2 FunTable fptr) as R.
    destruct R as [[[]]|].
      inv_mbind.
      destruct Hundef as [gvs0 [EQ Hundef]].
      dgvs_instantiate_inv.
      assert (exists gvs, 
                Opsem.params2GVs (los2,nts2) lp0 Locals fs2 = Some gvs) as G'.
        destruct H4 as [l5 [ps2 [cs21 H4]]]; subst.
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]].
        inv_mbind.
        eapply OpsemPP.params2GVs_isnt_stuck; eauto 1; simpl; auto.
          exists nil. auto.
      destruct G' as [gvs' G'].
      assert (gvs' = l1) as EQ.
        destruct H4 as [l5 [ps1 [cs11 H4]]]; subst;
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
        destruct HwfS1 as [HwfS1 _];
        unfold wf_ExecutionContext, inscope_of_ec in HwfS1;
        inv_mbind.
        eapply params2GVs_sim; 
          eauto 2 using wf_system__wf_fdef, wf_system__uniqFdef; 
            try solve [simpl; auto].
      subst.
      repeat fill_ctxhole.
      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_r2l; eauto.
      simpl.
      exists l1. split; auto.
    
      erewrite TopSim.lookupFdefViaPtr__simulation_None_l2r; eauto.
      erewrite TopSim.lookupExFdecViaPtr__simulation_None_r2l; eauto.
Qed.

Variable (ctx_inv:OpsemAux.Config -> @Opsem.State DGVs -> Prop).
Variable (los : layouts) (nts : namedts).

Hypothesis subst_inv_preservation: forall (cfg1 : OpsemAux.Config)
  (Heqtd: OpsemAux.CurTargetData cfg1 = (los,nts))
  (S1 S1' : Opsem.State) (tr : trace) (Hp: ctx_inv cfg1 S1),
  OpsemPP.wf_Config cfg1 ->
  OpsemPP.wf_State cfg1 S1 ->
  Opsem.sInsn cfg1 S1 S1' tr ->
  subst_inv.wf_State (value_id sid) sv sf cfg1 S1 -> 
  subst_inv.wf_State (value_id sid) sv sf cfg1 S1'.

Lemma step_bsim : forall Cfg1 St1 Cfg2 St2 St2' tr2 (Hp:ctx_inv Cfg1 St1)
  (Heqtd: OpsemAux.CurTargetData Cfg1 = (los,nts))
  (Hwfcfg: OpsemPP.wf_Config Cfg1) (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hwfcfg2: OpsemPP.wf_Config Cfg2) (Hwfpp2: OpsemPP.wf_State Cfg2 St2) 
  (HwfS1: subst_inv.wf_State (value_id sid) sv sf Cfg1 St1)
  (Hsim: State_simulation Cfg1 St1 Cfg2 St2)
  (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2)
  (Hok: ~ sop_goeswrong Cfg1 St1),
  exists St1', 
    Opsem.sInsn Cfg1 St1 St1' tr2 /\
    State_simulation Cfg1 St1' Cfg2 St2'.
Proof.
  intros.
  assert (Hnfinal1: Opsem.s_isFinialState Cfg1 St1 = merror).
    remember (Opsem.s_isFinialState Cfg1 St1) as R.
    destruct R; auto.
    apply s_isFinialState__subst_State_simulation in Hsim; 
      try solve [auto | congruence].
      contradict Hop2.
      apply s_isFinialState__stuck. congruence.
  assert (J:=Hwfpp).
  apply OpsemPP.progress in J; auto.
  destruct J as [Hfinal1 | [[IS1'' [tr0 Hop1]] | Hundef1]]; try congruence.
    assert (OpsemPP.wf_State Cfg1 IS1'') as Hwfpp''.
      apply OpsemPP.preservation in Hop1; auto.
    assert (subst_inv.wf_State (value_id sid) sv sf Cfg1 IS1'') as HwfS1'.
      eapply subst_inv_preservation in Hop1; eauto.
    eapply step_sim in Hsim; eauto.
    destruct Hsim as [Hsim EQ]; subst.
    exists IS1''. 
    split; eauto.

    apply undefined_state__stuck' in Hundef1.
    contradict Hok.
    apply nonfinal_stuck_state_goes_wrong; auto.
Qed.

Hypothesis ctx_inv_preservation: forall (cfg1 : OpsemAux.Config)
  (S1 S1' : Opsem.State) (tr : trace),
  OpsemPP.wf_Config cfg1 ->
  OpsemPP.wf_State cfg1 S1 ->
  Opsem.sInsn cfg1 S1 S1' tr ->
  ctx_inv cfg1 S1 -> ctx_inv cfg1 S1'.

Lemma sop_star__subst_State_simulation: forall cfg1 IS1 cfg2 IS2 tr FS2 
  (Heqtd: OpsemAux.CurTargetData cfg1 = (los,nts))
  (Hp1:ctx_inv cfg1 IS1)
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfcfg2: OpsemPP.wf_Config cfg2) 
  (Hwfpp1: OpsemPP.wf_State cfg1 IS1) (Hwfpp2: OpsemPP.wf_State cfg2 IS2) 
  (HwfS1: subst_inv.wf_State (value_id sid) sv sf cfg1 IS1) 
  (Hstsim : State_simulation cfg1 IS1 cfg2 IS2)
  (Hstsim : State_simulation cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\
    State_simulation cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent cfg1.
  generalize dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    eapply step_bsim in Hstsim; eauto.
    destruct Hstsim as [St1' [Hop1 Hstsim]].
    assert (OpsemPP.wf_State cfg1 St1') as Hwfpp1'.
      apply OpsemPP.preservation in Hop1; auto.
    assert (subst_inv.wf_State (value_id sid) sv sf cfg1 St1') as HwfS1'.
      eapply subst_inv_preservation in Hop1; eauto.
    eapply IHHopstar in Hstsim; 
      eauto using sop_goeswrong__step, (@OpsemPP.preservation DGVs).
    destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
    exists FS1.
    split; eauto.
Qed.

Lemma sop_plus__subst_State_simulation: forall cfg1 IS1 cfg2 IS2 tr FS2 
  (Heqtd: OpsemAux.CurTargetData cfg1 = (los,nts))
  (Hp1:ctx_inv cfg1 IS1)
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfcfg2: OpsemPP.wf_Config cfg2) 
  (Hwfpp1: OpsemPP.wf_State cfg1 IS1) (Hwfpp2: OpsemPP.wf_State cfg2 IS2) 
  (HwfS1: subst_inv.wf_State (value_id sid) sv sf cfg1 IS1)
  (Hstsim : State_simulation cfg1 IS1 cfg2 IS2) 
  (Hstsim : State_simulation cfg1 IS1 cfg2 IS2)
  (Hopplus : Opsem.sop_plus cfg2 IS2 FS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  exists FS1, Opsem.sop_plus cfg1 IS1 FS1 tr /\
    State_simulation cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  inv Hopplus.
  eapply step_bsim in Hstsim; eauto.
  destruct Hstsim as [St1' [Hop1 Hstsim']].
  assert (wf_State (value_id sid) sv sf cfg1 St1') as HwfS1'.
    eapply subst_inv_preservation in Hop1; eauto.
  eapply sop_star__subst_State_simulation in Hstsim'; eauto using
    (@OpsemPP.preservation DGVs), sop_goeswrong__step.
  destruct Hstsim' as [FS1 [Hopstar Hstsim']].
  exists FS1. 
  split; eauto.
Qed.

Lemma subst_inv_preservation_star: forall (cfg : OpsemAux.Config)
  (Heqtd: OpsemAux.CurTargetData cfg = (los,nts))
  (S1 S2 : Opsem.State) (tr : trace) (Hp:ctx_inv cfg S1)
  (Hcfg1: OpsemPP.wf_Config cfg) (Hpp1: OpsemPP.wf_State cfg S1)
  (Hstar: Opsem.sop_star cfg S1 S2 tr)
  (HwfS1: subst_inv.wf_State (value_id sid) sv sf cfg S1),
  subst_inv.wf_State (value_id sid) sv sf cfg S2.
Proof.
  intros.
  induction Hstar; auto.
    apply IHHstar; eauto using (@OpsemPP.preservation DGVs).
Qed.  

Lemma subst_inv_preservation_plus: forall (cfg : OpsemAux.Config)
  (Heqtd: OpsemAux.CurTargetData cfg = (los,nts))
  (S1 S2 : Opsem.State) (tr : trace) (Hp:ctx_inv cfg S1)
  (Hcfg1: OpsemPP.wf_Config cfg) (Hpp1: OpsemPP.wf_State cfg S1)
  (Hplus: Opsem.sop_plus cfg S1 S2 tr)
  (HwfS1: subst_inv.wf_State (value_id sid) sv sf cfg S1),
  subst_inv.wf_State (value_id sid) sv sf cfg S2.
Proof.
  intros.
  apply OpsemProps.sop_plus__implies__sop_star in Hplus.
  eapply subst_inv_preservation_star; eauto.
Qed.

Lemma ctx_inv_preservation_star: forall (cfg1 : OpsemAux.Config)
  (S1 S1' : Opsem.State) (tr : trace)
  (Hcfg1: OpsemPP.wf_Config cfg1) (Hpp1: OpsemPP.wf_State cfg1 S1)
  (Hstar: Opsem.sop_star cfg1 S1 S1' tr),
  ctx_inv cfg1 S1 -> ctx_inv cfg1 S1'.
Proof.
  intros.
  induction Hstar; auto.
    apply IHHstar; eauto using (@OpsemPP.preservation DGVs).
Qed.  

Lemma ctx_inv_preservation_plus: forall (cfg1 : OpsemAux.Config)
  (S1 S1' : Opsem.State) (tr : trace)
  (Hcfg1: OpsemPP.wf_Config cfg1) (Hpp1: OpsemPP.wf_State cfg1 S1)
  (Hplus: Opsem.sop_plus cfg1 S1 S1' tr),
  ctx_inv cfg1 S1 -> ctx_inv cfg1 S1'.
Proof.
  intros.
  apply OpsemProps.sop_plus__implies__sop_star in Hplus.
  eapply ctx_inv_preservation_star; eauto.
Qed.  

Lemma sop_div__subst_State_simulation: forall cfg1 IS1 cfg2 IS2 tr
  (Heqtd: OpsemAux.CurTargetData cfg1 = (los,nts))
  (Hp:ctx_inv cfg1 IS1)
  (Hwfcfg1: OpsemPP.wf_Config cfg1) (Hwfcfg2: OpsemPP.wf_Config cfg2) 
  (Hwfpp1: OpsemPP.wf_State cfg1 IS1) (Hwfpp2: OpsemPP.wf_State cfg2 IS2) 
  (HwfS1: subst_inv.wf_State (value_id sid) sv sf cfg1 IS1) 
  (Hstsim : State_simulation cfg1 IS1 cfg2 IS2)
  (Hstsim : State_simulation cfg1 IS1 cfg2 IS2)
  (Hdiv : Opsem.sop_diverges cfg2 IS2 tr) (Hok: ~ sop_goeswrong cfg1 IS1),
  Opsem.sop_diverges cfg1 IS1 tr.
Proof.
  cofix CIH.
  intros.
  inv Hdiv.
  eapply sop_plus__subst_State_simulation in Hstsim; eauto 1.
  destruct Hstsim as [FS1 [Hopplus Hstsim']].
  econstructor; eauto.
  assert (wf_State (value_id sid) sv sf cfg1 FS1) as HwfS1'.
    eapply subst_inv_preservation_plus; eauto.
  eapply CIH in Hstsim'; eauto using
    (@OpsemPP.preservation_plus DGVs), sop_goeswrong__plus,
    ctx_inv_preservation_plus.
Qed.

Hypothesis s_genInitState__subst_inv: forall (S : system) (main : id) 
  (VarArgs : list (GVsT DGVs)) (cfg : OpsemAux.Config) (IS : Opsem.State),
  wf_system S ->
  Opsem.s_genInitState S main VarArgs Mem.empty = ret (cfg, IS) ->
  wf_State (value_id sid) sv sf cfg IS.

Hypothesis subst_wfS: forall (los : layouts) (nts : namedts)
  (main : id) (VarArgs : list (GVsT DGVs)) 
  (Ps1 : list product) (Ps2 : list product)
  S2 (Heq2: S2= [module_intro los nts (Ps1 ++ product_fdef sf :: Ps2)])
  (HwfS : wf_system S2),
  wf_system
     [module_intro los nts (Ps1 ++ product_fdef (subst_fdef sid sv sf) :: Ps2)].

Hypothesis s_genInitState__ctx_inv: forall (S : system) (main : id) 
  (VarArgs : list (GVsT DGVs)) (cfg : OpsemAux.Config) (IS : Opsem.State),
  wf_system S ->
  Opsem.s_genInitState S main VarArgs Mem.empty = ret (cfg, IS) ->
  ctx_inv cfg IS.

(* the main result *)
Lemma sim: forall (main : id) (VarArgs : list (GVsT DGVs)) 
  (Ps1 : list product) (Ps2 : list product)
  S2 (Heq2: S2= [module_intro los nts (Ps1 ++ product_fdef sf :: Ps2)])
  (Hok: defined_program S2 main VarArgs)
  (HwfS : wf_system S2),
  program_sim
     [module_intro los nts (Ps1 ++ product_fdef (subst_fdef sid sv sf) :: Ps2)]
     S2 main VarArgs.
Proof.
  intros.
  assert (wf_fdef [module_intro los nts (Ps1++product_fdef sf::Ps2)]
            (module_intro los nts (Ps1++product_fdef sf::Ps2)) 
            sf /\ uniqFdef sf) as J.
    subst.
    apply wf_single_system__wf_uniq_fdef; auto.
  destruct J as [HwfF HuniqF].
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation
     [module_intro los nts (Ps1 ++ product_fdef sf :: Ps2)]
     [module_intro los nts
        (Ps1 ++ product_fdef (subst_fdef sid sv sf) :: Ps2)]) as Hssim.
    constructor; auto.
    repeat split; auto.
    subst.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    unfold TopSim.products_simulation. unfold fsim. unfold Fsim. 
    apply uniq_products_simulation; auto.

Ltac subst_sim_init :=
match goal with
| H: Opsem.s_genInitState [module_intro ?los ?nts _] _ _ _ = Some (?cfg, ?IS)
  |- _ =>
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg IS) as Hwfst';
      try solve [eapply s_genInitState__opsem_wf in H; eauto using subst_wfS];
    eapply s_genInitState__subst_State_simulation in H; eauto;
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]];
    assert (OpsemPP.wf_Config cfg1 /\ OpsemPP.wf_State cfg1 IS1) as Hwfst;
      try solve [eapply s_genInitState__opsem_wf; eauto];
    assert (subst_inv.wf_State (value_id sid) sv sf cfg1 IS1) as Hisrhsval;
      try solve [eapply s_genInitState__subst_inv; eauto];
    assert ((los,nts) = OpsemAux.CurTargetData cfg1) as EQ;
      try solve [eapply s_genInitState__targedata; eauto];
    assert (ctx_inv cfg1 IS1) as Hctx;
      try solve [eapply s_genInitState__ctx_inv; eauto]
end.

Ltac subst_sim_end :=
 match goal with
| Hstsim' : State_simulation ?cfg1 ?FS1 ?cfg ?FS,
  Hopstar1 : Opsem.sop_star ?cfg1 _ ?FS1 _ |- _ =>
    assert (OpsemPP.wf_State cfg FS) as Hwfst''; 
      try solve [eapply OpsemPP.preservation_star; eauto; try tauto];
    assert (OpsemPP.wf_State cfg1 FS1) as Hwfst1'';
      try solve [eapply OpsemPP.preservation_star; eauto; try tauto];
    assert (ctx_inv cfg1 FS1) as Hctx1''; try solve [
       eapply ctx_inv_preservation_star in Hopstar1; eauto; try tauto
     ];
    assert (wf_State (value_id sid) sv sf cfg1 FS1); try solve [
        eapply subst_inv_preservation_star in Hopstar1; eauto; try tauto
      ]
end.

  constructor; auto.
    intros tr t Hconv.
    inv Hconv.
    subst_sim_init.
    eapply sop_star__subst_State_simulation in Hstsim; 
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    subst_sim_end.
    match goal with
    | Hstsim' : State_simulation _ _ ?cfg ?FS,
      H: Opsem.s_isFinialState ?cfg ?FS = _ |- _ =>
      eapply s_isFinialState__subst_State_simulation in Hstsim'; eauto; try tauto;
      rewrite <- Hstsim' in H
    end.
    exists t. split; auto using result_match_relf. econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    subst_sim_init.
    eapply sop_div__subst_State_simulation in Hstsim; 
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.

    intros tr t Hgowrong.
    inv Hgowrong.
    assert (OpsemPP.wf_Config cfg /\ OpsemPP.wf_State cfg t) as HwfSt.
      eapply s_genInitState__opsem_wf in H; eauto using subst_wfS.
      destruct H as [Hcfg2 HwfSt2].
      apply OpsemPP.preservation_star in H0; auto.
    assert (OpsemPP.undefined_state cfg t) as Hundef.
      apply stuck__undefined_state in H2; try solve [auto | tauto].
    subst_sim_init.
    eapply sop_star__subst_State_simulation in Hstsim;
      eauto using defined_program__doesnt__go_wrong; try tauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    subst_sim_end.
    assert (OpsemPP.undefined_state cfg1 FS1) as Hundef'.
      eapply undefined_state__subst_State_simulation_r2l in Hundef; 
        try solve [eauto | tauto].
    assert (Opsem.s_isFinialState cfg1 FS1 = merror) as Hfinal'.
      erewrite <- s_isFinialState__subst_State_simulation in H2; 
        try solve [eauto | tauto].
    apply undefined_state__stuck' in Hundef'.
    exists FS1.
    econstructor; eauto.
Qed.

End SubstSim.

End SubstSim.
