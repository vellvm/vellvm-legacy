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
Require Import Maps.
Require Import opsem_props.
Require Import promotable_props.
Require Import primitives.
Require Import id_rhs_val.
Require Import palloca_props.
Require Import memory_props.
Require Import mem2reg.
Require Import program_sim.

Definition sas (sid1 sid2: id) (v1 v2:value) (cs2:cmds) (b:block) 
  (pinfo:PhiInfo) : Prop :=         
blockInFdefB b (PI_f pinfo) = true /\
load_in_cmds (PI_id pinfo) cs2 = false /\
let '(block_intro _ _ cs _) := b in
exists cs1, exists cs3,
  cs = 
  cs1 ++ 
  insn_store sid1 (PI_typ pinfo) v1 (value_id (PI_id pinfo)) (PI_align pinfo) ::
  cs2 ++ 
  insn_store sid2 (PI_typ pinfo) v2 (value_id (PI_id pinfo)) (PI_align pinfo) ::
  cs3.

Record SASInfo (pinfo: PhiInfo) := mkSASInfo {
  SAS_sid1 : id;
  SAS_sid2 : id;
  SAS_value1 : value;
  SAS_value2 : value;
  SAS_tail : cmds;
  SAS_block : block;
  SAS_prop: sas SAS_sid1 SAS_sid2 SAS_value1 SAS_value2 SAS_tail SAS_block pinfo
}.

Definition fdef_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) f1 f2 
  : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_fdef (SAS_sid1 pinfo sasinfo) f1 = f2
  else f1 = f2.

Definition cmds_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) (f1:fdef) 
  cs1 cs2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_cmds (SAS_sid1 pinfo sasinfo) cs1 = cs2
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) (f1:fdef) 
  b1 b2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_block (SAS_sid1 pinfo sasinfo) b1 = b2
  else b1 = b2.

Definition products_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) Ps1 Ps2
  : Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation pinfo sasinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) S1 S2 
  : Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation pinfo sasinfo Ps1 Ps2
   end) S1 S2.

Definition EC_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  (EC1 EC2:@Opsem.ExecutionContext DGVs) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation pinfo sasinfo f1 f2 /\
       tmn1 = tmn2 /\
       als1 = als2 /\
       block_simulation pinfo sasinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       lc1 = lc2 /\
       cmds_simulation pinfo sasinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  (ECs1 ECs2:@Opsem.ECStack DGVs) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation pinfo sasinfo EC1 EC2 /\ 
    ECs_simulation pinfo sasinfo ECs1' ECs2'
| _, _ => False
end.

Definition cs_follow_dead_store (pinfo:PhiInfo) (sasinfo: SASInfo pinfo)
  (cs:cmds) : Prop :=
let '(block_intro _ _ cs0 _) := SAS_block pinfo sasinfo in
forall cs1 cs3, 
  cs0 = 
    cs1 ++ 
    insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
      (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) (PI_align pinfo) ::
    SAS_tail pinfo sasinfo ++ 
    cs3 ->
  (exists csa, exists csb, 
    cs = csb ++ cs3 /\ SAS_tail pinfo sasinfo = csa ++ csb).

Definition EC_follow_dead_store (pinfo:PhiInfo) (sasinfo: SASInfo pinfo)
  (ec:@Opsem.ExecutionContext DGVs) : Prop :=
Opsem.CurFunction ec = PI_f pinfo /\
Opsem.CurBB ec = SAS_block pinfo sasinfo /\
cs_follow_dead_store pinfo sasinfo (Opsem.CurCmds ec).

Definition undead_head_in_tail (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) ptr
  (ec0:@Opsem.ExecutionContext DGVs) : Prop :=
forall gvsa (Heq: Opsem.CurFunction ec0 = PI_f pinfo)
  (Hlkup: lookupAL _ (Opsem.Locals ec0) (PI_id pinfo) = Some gvsa),
  MemProps.no_alias ptr gvsa \/
  ~ MemProps.no_alias ptr gvsa /\ EC_follow_dead_store pinfo sasinfo ec0.

Definition undead_head_tail (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) ptr 
  (ecs':list Opsem.ExecutionContext) : Prop :=
  forall ec0 (Hin: In ec0 ecs'), undead_head_in_tail pinfo sasinfo ptr ec0.

Definition Mem_simulation (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) TD 
  (ecs1:list Opsem.ExecutionContext) Mem1 Mem2 : Prop :=
Mem.nextblock Mem1 = Mem.nextblock Mem2 /\
forall ptr ty al gvs1 gvs2 
  (Hnalias: undead_head_tail pinfo sasinfo ptr ecs1)
  (Hld1: mload TD Mem1 ptr ty al = Some gvs1)
  (Hld2: mload TD Mem2 ptr ty al = Some gvs2),
  gvs1 = gvs2.

Definition State_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\ 
    products_simulation pinfo sasinfo Ps1 Ps2 /\
    ECs_simulation pinfo sasinfo ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ Mem_simulation pinfo sasinfo TD1 ECs1 M1 M2
end.

Definition removable_State (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  (St:@Opsem.State DGVs) : Prop :=
match St with
| Opsem.mkState
    (Opsem.mkEC f b 
      (insn_store sid _ _ _ _ :: cs) 
      tmn lc als::_) _ => 
    if (fdef_dec (PI_f pinfo) f) then 
      if (id_dec sid (SAS_sid1 pinfo sasinfo)) 
      then True else False
    else False
| _ => False
end.

Lemma removable_State_dec : forall pinfo sasinfo St,
  removable_State pinfo sasinfo St \/ ~ removable_State pinfo sasinfo St.
Proof.
  destruct St. 
  destruct ECS as [|[]]; auto.
  destruct CurCmds; auto.
  simpl.
  destruct c; auto.
  destruct (fdef_dec (PI_f pinfo) CurFunction); auto.
  destruct (id_dec i0 (SAS_sid1 pinfo sasinfo)); auto.
Qed.

Lemma sas_is_sim : forall maxb pinfo (sasinfo: SASInfo pinfo) Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hsim: State_simulation pinfo sasinfo Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State pinfo sasinfo St1) St1' tr1 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     State_simulation pinfo sasinfo Cfg1 St1' Cfg2 St2 /\ tr1 = trace_nil) /\
  (forall (Hnrem: ~removable_State pinfo sasinfo St1) St1' St2' tr1 tr2
     (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2) 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     State_simulation pinfo sasinfo Cfg1 St1' Cfg2 St2' /\ tr1 = tr2).
Admitted.

Lemma s_genInitState__sas_State_simulation: forall pinfo sasinfo S1 S2 main 
  VarArgs cfg2 IS2,
  system_simulation pinfo sasinfo S1 S2 ->
  Opsem.s_genInitState S2 main VarArgs Mem.empty = ret (cfg2, IS2) ->
  exists cfg1, exists IS1,
    Opsem.s_genInitState S1 main VarArgs Mem.empty = ret (cfg1, IS1) /\
    State_simulation pinfo sasinfo cfg1 IS1 cfg2 IS2.
Admitted.

Lemma s_isFinialState__sas_State_simulation: forall pinfo sasinfo cfg1 FS1 cfg2 
  FS2 r (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2)
  (Hfinal: s_isFinialState cfg2 FS2 = ret r),
  s_isFinialState cfg1 FS1 = ret r.
Admitted.

Lemma opsem_s_isFinialState__sas_State_simulation: forall 
  pinfo sasinfo cfg1 FS1 cfg2 FS2  
  (Hstsim : State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2),
  Opsem.s_isFinialState FS1 = Opsem.s_isFinialState FS2.
Admitted.

Lemma undefined_state__sas_State_simulation: forall pinfo sasinfo cfg1 St1 cfg2 
  St2 (Hstsim : State_simulation pinfo sasinfo cfg1 St1 cfg2 St2),
  OpsemPP.undefined_state cfg1 St1 -> OpsemPP.undefined_state cfg2 St2.
Admitted.

Lemma sop_star__sas_State_simulation: forall pinfo sasinfo cfg1 IS1 cfg2 IS2 tr
  FS2 (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) maxb
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hstsim : State_simulation pinfo sasinfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_star cfg2 IS2 FS2 tr),
  exists FS1, Opsem.sop_star cfg1 IS1 FS1 tr /\ 
    State_simulation pinfo sasinfo cfg1 FS1 cfg2 FS2.
Proof.
  intros.
  generalize dependent cfg1.
  generalize dependent IS1.
  induction Hopstar; intros.
    exists IS1. split; auto.

    assert (J:=Hwfpp).
    apply OpsemPP.progress in J; auto.
    destruct J as [Hfinal1 | [[IS1' [tr0 Hop1]] | Hundef1]].
      apply opsem_s_isFinialState__sas_State_simulation in Hstsim.
      rewrite Hstsim in Hfinal1.
      contradict H; eauto using s_isFinialState__stuck.

      assert (OpsemPP.wf_State cfg1 IS1') as Hwfpp'.
        admit. (* wf pp *)
      assert (Promotability.wf_State maxb pinfo cfg1 IS1') as Hnoalias'.
        admit. (* wf pp *)
      eapply sas_is_sim in Hstsim; eauto.
      destruct Hstsim as [Hstsim1 Hstsim2].
      destruct (@removable_State_dec pinfo sasinfo IS1) as [Hrm | Hnrm].
        eapply Hstsim1 in Hrm; eauto.
        destruct Hrm as [Hstsim EQ]; subst.
        admit. (* we should do induction on the measure of State_simulation *)

        eapply Hstsim2 in Hnrm; eauto.
        destruct Hnrm as [Hstsim EQ]; subst.
        eapply IHHopstar in Hstsim; eauto.
        destruct Hstsim as [FS1 [Hopstar1 Hstsim]].
        exists FS1.
        split; eauto.

      eapply undefined_state__sas_State_simulation in Hstsim; eauto.
      contradict H; eauto using undefined_state__stuck.
Qed.

Lemma sop_div__sas_State_simulation: forall pinfo laainfo cfg1 IS1 cfg2 IS2 tr
  (Hwfpi: WF_PhiInfo pinfo) (Hwfpp: OpsemPP.wf_State cfg1 IS1) maxb
  (Hnoalias: Promotability.wf_State maxb pinfo cfg1 IS1)
  (Hstsim : State_simulation pinfo laainfo cfg1 IS1 cfg2 IS2)
  (Hopstar : Opsem.sop_diverges cfg2 IS2 tr),
  Opsem.sop_diverges cfg1 IS1 tr.
Admitted.

Lemma find_st_ld__sasinfo: forall l0 ps0 cs0 tmn0 i0 v cs (pinfo:PhiInfo) dones
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones) v0
  (i1 : id) (Hld : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (HBinF : blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true),
  exists sasinfo:SASInfo pinfo,
    SAS_sid1 pinfo sasinfo = i0 /\
    SAS_sid2 pinfo sasinfo = i1 /\
    SAS_value1 pinfo sasinfo = v /\
    SAS_value2 pinfo sasinfo = v0 /\
    SAS_block pinfo sasinfo = (block_intro l0 ps0 cs0 tmn0).
Admitted.

Lemma sas_sim: forall (los : layouts) (nts : namedts) (fh : fheader) 
  (dones : list id) (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) 
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo) 
  (HwfS : 
     wf_system nil
       [module_intro los nts 
         (Ps1 ++ 
          product_fdef 
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
           (List.map (remove_block i0)
             (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) :: Ps2)]
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
    main VarArgs.
Proof.
  intros.
  assert (blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) = true)
    as HBinF.
    rewrite Heq. simpl. apply InBlocksB_middle.
  eapply find_st_ld__sasinfo in HBinF; eauto.
  destruct HBinF as [sasinfo [J1 [J2 [J3 [J4 J5]]]]]; subst.
  assert (Huniq:=HwfS). apply wf_system__uniqSystem in Huniq; auto.
  assert (system_simulation pinfo sasinfo
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (remove_fdef (SAS_sid1 pinfo sasinfo)
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))
         :: Ps2)]) as Hssim.
    unfold system_simulation.
    constructor; auto.
    repeat split; auto.
    unfold products_simulation.
    simpl in Huniq. destruct Huniq as [[_ [_ Huniq]] _].
    apply uniq_products_simulation; auto.
  constructor.
    intros tr t Hconv.
    inv Hconv.
    eapply s_genInitState__sas_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]].    
    assert (OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    assert (exists maxb, 
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom.
      eapply Promotability.s_genInitState__wf_globals_promotable; eauto.
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]].
    eapply sop_star__sas_State_simulation in Hstsim; eauto.
    destruct Hstsim as [FS1 [Hopstar1 Hstsim']].
    eapply s_isFinialState__sas_State_simulation in Hstsim'; eauto.
    econstructor; eauto.

    intros tr Hdiv.
    inv Hdiv.
    eapply s_genInitState__sas_State_simulation in H; eauto.
    destruct H as [cfg1 [IS1 [Hinit Hstsim]]].  
    assert (OpsemPP.wf_State cfg1 IS1) as Hwfst. 
      eapply s_genInitState__opsem_wf; eauto.
    assert (exists maxb, 
              MemProps.wf_globals maxb (OpsemAux.Globals cfg1) /\ 0 <= maxb /\
              Promotability.wf_State maxb pinfo cfg1 IS1) as Hprom.
      eapply Promotability.s_genInitState__wf_globals_promotable; eauto.
    destruct Hprom as [maxb [Hwfg [Hless Hprom]]].
    eapply sop_div__sas_State_simulation in Hstsim; eauto.
    destruct Hstsim as [FS1 Hopdiv1].
    econstructor; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
