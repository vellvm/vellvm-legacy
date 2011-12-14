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
Require Import alive_store.
Require Import id_rhs_val.
Require Import palloca_props.

(* We define a special las used by mem2reg that only considers local commands.
   In general, it should be extended to the las defined w.r.t domination and
   memory dependency (which we are aiming in the future work)

   The current mem2reg also does SAS eliminations before all loads are removed.
   For example,
     st v1 p; ...; st v2 p; ...
   if there are no other lds in the first ..., the first ``st v1 p'' can be 
   removed.

   In practice, such a code after phiplacement may exist if the original code 
   also does store to the promotable alloca. 

   An alternative approach is that we only consider such elimination after all
   possible removed loads are removed, as what the paper presents. mem2reg does
   not check if there are any unremoved loads in unreachable blocks. If so,
   some stores cannot be removed. We need to let mem2reg ignore the loads of
   unreachable blocks to remove what SAS can eliminate.

   For this reason, here, we give the abstract properties that las needs to hold.
   The properties do not depend on the concrete design in mem2reg, such as
   find_init_stld, find_next_stld, ... So the proofs can still work if we change
   mem2reg. We should prove that the design in mem2reg satisfy the properties.
 *)

Definition las (lid sid: id) (v:value) (cs2:cmds) (b:block) (pinfo:PhiInfo)
  : Prop :=
blockInFdefB b (PI_f pinfo) = true /\
store_in_cmds (PI_id pinfo) cs2 = false /\
let '(block_intro _ _ cs _) := b in
exists cs1, exists cs3,
  cs = 
  cs1 ++ 
  insn_store sid (PI_typ pinfo) v (value_id (PI_id pinfo)) (PI_align pinfo) :: 
  cs2 ++ 
  insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) (PI_align pinfo) :: 
  cs3.

Record LASInfo (pinfo: PhiInfo) := mkLASInfo {
  LAS_lid : id;
  LAS_sid : id;
  LAS_value : value;
  LAS_tail : cmds;
  LAS_block : block;
  LAS_prop : las LAS_lid LAS_sid LAS_value LAS_tail LAS_block pinfo
}.

Lemma store_in_cmds_merge: forall i0 cs1 cs2,
  store_in_cmds i0 cs1 = false /\ store_in_cmds i0 cs2 = false ->
  store_in_cmds i0 (cs1++cs2) = false.
Admitted.

Lemma las__alive_store: forall lid sid v cs2 b pinfo,
  las lid sid v cs2 b pinfo ->
  alive_store sid v (cs2 ++
    [insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) (PI_align pinfo)]) 
    b pinfo.
Proof.
  unfold las. unfold alive_store.
  intros. destruct b.
  destruct H as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
  split; auto.
  split.
    apply store_in_cmds_merge.
    split; auto.
     
    exists cs1. exists cs3. simpl_env. auto.
Qed.

Lemma lasinfo__stinfo: forall pinfo (lasinfo: LASInfo pinfo),
  { stinfo: StoreInfo pinfo |
    SI_id pinfo stinfo = LAS_sid pinfo lasinfo /\
    SI_value pinfo stinfo = LAS_value pinfo lasinfo /\
    SI_block pinfo stinfo = LAS_block pinfo lasinfo /\
    SI_tail pinfo stinfo = 
      LAS_tail pinfo lasinfo ++ 
      [insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo) (value_id (PI_id pinfo)) 
        (PI_align pinfo)] }.
Proof.
  intros.
  destruct lasinfo. simpl.
  apply las__alive_store in LAS_prop0.
  exists (mkStoreInfo 
    pinfo LAS_sid0 LAS_value0 
    (LAS_tail0 ++
     [insn_load LAS_lid0 (PI_typ pinfo) (value_id (PI_id pinfo))
        (PI_align pinfo)]) LAS_block0 LAS_prop0).
  auto.
Defined.

Lemma las__alive_store__vev_EC: forall pinfo lasinfo los nts M gl ps ec ifs s 
  (Hwfs: wf_system ifs s) 
  (HmInS: moduleInSystemB (module_intro los nts ps) s = true)
  (Hwfpp: OpsemPP.wf_ExecutionContext (los,nts) ps ec) stinfo Hp
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo),
  alive_store.wf_ExecutionContext pinfo stinfo (los,nts) M gl ec -> 
  vev_ExecutionContext (value_id (LAS_lid pinfo lasinfo)) 
    (LAS_value pinfo lasinfo) (PI_f pinfo) (los,nts) M gl ec.
Proof.
  intros. clear Hlas2st.
  destruct Hp as [J1 [J2 [J3 J4]]].
  intros.
  destruct ec. simpl in *.
  destruct CurCmds; auto.

  destruct Hwfpp as 
    [Hreach [HbInF [HfInPs [_ [Hinscope [l' [ps' [cs' EQ]]]]]]]]; subst.

  remember (inscope_of_cmd CurFunction
                 (block_intro l' ps' (cs' ++ c :: CurCmds) Terminator) c) as R.
  destruct R; auto.

  assert (uniqFdef CurFunction) as Huniq.
    eapply wf_system__uniqFdef; eauto.

  assert (Hnodup:=HbInF).
  apply uniqFdef__blockInFdefB__nodup_cmds in Hnodup; auto.

  intros G1; subst.
  split; intro G1.
  Case "LAS_value is in scope".

  remember (Opsem.getOperandValue (los,nts) (LAS_value pinfo lasinfo) 
      Locals gl) as R.
  destruct R; auto.
  destruct (LAS_lid pinfo lasinfo == getCmdLoc c); auto.

  assert (c = insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
             (value_id (PI_id pinfo)) (PI_align pinfo)) as EQ.
      eapply IngetCmdsIDs__lookupCmdViaIDFromFdef with (c1:=c) in HbInF; eauto
        using in_middle.
      destruct stinfo. simpl in *. subst.
      destruct (LAS_block pinfo lasinfo).
      assert (SI_alive':=SI_alive).
      destruct SI_alive' as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
      rewrite_env (
        (cs1 ++ [insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
                            (LAS_value pinfo lasinfo) (value_id (PI_id pinfo))
                            (PI_align pinfo)] ++
         LAS_tail pinfo lasinfo) ++
         insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
           (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3) in J1.
      eapply IngetCmdsIDs__lookupCmdViaIDFromFdef with (c1:=
        insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo) 
          (value_id (PI_id pinfo)) (PI_align pinfo)) in J1; 
        eauto using in_middle.
      simpl in J1. rewrite <- e in HbInF. 
      rewrite HbInF in J1. inv J1. auto.

  subst.

  assert (block_intro l' ps' 
              (cs' ++ insn_load (LAS_lid pinfo lasinfo) 
                            (PI_typ pinfo) (value_id (PI_id pinfo))
                            (PI_align pinfo) :: CurCmds) Terminator = 
              SI_block pinfo stinfo) as Heq.
      clear H Hinscope HeqR Hreach.
      assert (In 
        (LAS_lid pinfo lasinfo)
        (getBlockIDs
          (block_intro l' ps'
            (cs' ++
              insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
              (value_id (PI_id pinfo)) (PI_align pinfo) :: CurCmds)
            Terminator))) as Hin.
        simpl.
        rewrite getCmdsIDs_app.
        simpl. 
        rewrite_env ((getPhiNodesIDs ps' ++ getCmdsIDs cs') ++ 
                      LAS_lid pinfo lasinfo :: getCmdsIDs CurCmds).
        apply in_middle.

      apply inGetBlockIDs__lookupBlockViaIDFromFdef with 
        (id1:=LAS_lid pinfo lasinfo) in HbInF; auto.
      clear Hin.

      destruct stinfo. simpl in *. subst.
      destruct (LAS_block pinfo lasinfo).
      assert (SI_alive':=SI_alive).
      destruct SI_alive' as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
      assert (In (LAS_lid pinfo lasinfo)
        (getBlockIDs
          (block_intro l1 p
             (cs1 ++
              insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
                (LAS_value pinfo lasinfo) (value_id (PI_id pinfo))
                (PI_align pinfo)
              :: (LAS_tail pinfo lasinfo ++
                  [insn_load (LAS_lid pinfo lasinfo) 
                     (PI_typ pinfo) (value_id (PI_id pinfo)) 
                     (PI_align pinfo)]) ++ cs3) t))) as Hin.
        simpl.
        apply in_or_app. right.
        rewrite getCmdsIDs_app.
        apply in_or_app. right.
        simpl. rewrite getCmdsIDs_app.
        apply in_or_app. left.
        rewrite getCmdsIDs_app. simpl.
        apply in_middle.

      apply inGetBlockIDs__lookupBlockViaIDFromFdef with 
        (id1:=LAS_lid pinfo lasinfo) in J1; auto.
      clear Hin.

      rewrite HbInF in J1. inv J1. auto.

  assert (alive_store.wf_defs pinfo stinfo (los,nts) M gl Locals) as G.
    clear Hinscope Hreach.
    apply H; auto.
      clear H.
      destruct stinfo. simpl in *. subst.
      destruct (LAS_block pinfo lasinfo).
      assert (SI_alive':=SI_alive).
      destruct SI_alive' as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
      inv Heq.
      assert (
          cs' = cs1 ++
                insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
                  (LAS_value pinfo lasinfo) (value_id (PI_id pinfo)) 
                  (PI_align pinfo) :: (LAS_tail pinfo lasinfo) /\
          CurCmds = cs3
          ) as EQ.
        clear - H2 Hnodup.
        rewrite_env (
          (cs1 ++
          insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
            (LAS_value pinfo lasinfo) (value_id (PI_id pinfo)) 
            (PI_align pinfo)
          :: LAS_tail pinfo lasinfo) ++
          insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
              (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3) in H2.
        apply NoDup_cmds_split_middle in H2; auto.

      destruct EQ; subst. clear H2.
      unfold follow_alive_store. simpl.
      intros.
      assert (cs1 = cs0 /\ cs3 = cs2) as EQ.
        clear - H Hnodup.  
        rewrite_env (
          (cs1 ++
          insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
            (LAS_value pinfo lasinfo) (value_id (PI_id pinfo)) 
            (PI_align pinfo)
          :: LAS_tail pinfo lasinfo) ++
          insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
              (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3) in H.
        rewrite_env (
          (cs0 ++
          insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
            (LAS_value pinfo lasinfo) (value_id (PI_id pinfo)) 
            (PI_align pinfo)
          :: LAS_tail pinfo lasinfo) ++
          insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
              (value_id (PI_id pinfo)) (PI_align pinfo) :: cs2) in H.
        apply NoDup_cmds_split_middle in H; auto.
        destruct H as [H1 H2].
        split; auto.
          apply app_inv_tail in H1; auto.

      destruct EQ; subst. clear H.
      exists (LAS_tail pinfo lasinfo).
      exists ([insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
                   (value_id (PI_id pinfo)) (PI_align pinfo)]).
      auto.

  simpl.
  unfold alive_store.wf_defs in G.
  assert (exists gvsa, exists gvsv,
    lookupAL (GVsT DGVs) Locals (PI_id pinfo) = ret gvsa /\
    Opsem.getOperandValue (los,nts) (SI_value pinfo stinfo) Locals gl =
      ret gvsv) as G2.
    admit. (* wf domination *)
  destruct G2 as [gvsa [gvsv [G3 G2]]].
  exists gvsa. exists gvsa. exists gvsv.
  split; auto.
  split; auto.
    rewrite <- J2 in HeqR0.
    rewrite G2 in HeqR0. inv HeqR0.
    eapply G in G2; eauto.

  Case "LAS_lid >> LAS_value".
    simpl.
    remember (lookupAL (GVsT DGVs) Locals (LAS_lid pinfo lasinfo)) as R.
    destruct R; auto.
    remember (LAS_value pinfo lasinfo) as R.
    destruct R; auto.
    destruct (i0 == getCmdLoc c); subst; auto.
    admit. (* LAS_value >> LAS_lid, cyclic! *)   
Qed.

Lemma las__alive_store__vev_ECStack: forall pinfo lasinfo los nts M gl ifs ps s
  (Hwfs: wf_system ifs s) stinfo Hp 
  (HmInS: moduleInSystemB (module_intro los nts ps) s = true)
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo)
  ECs (Hwfpp: OpsemPP.wf_ECStack (los,nts) ps ECs),
  alive_store.wf_ECStack pinfo stinfo (los,nts) M gl ECs -> 
  vev_ECStack (value_id (LAS_lid pinfo lasinfo)) (LAS_value pinfo lasinfo) 
    (PI_f pinfo) (los,nts) M gl ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct H as [J1 J2].
    destruct Hwfpp as [HwfEC [HwfStk Hwfcall]].
    split; eauto.
      eapply las__alive_store__vev_EC; eauto.
Qed.

Lemma las__alive_store__vev: forall pinfo lasinfo cfg S 
  (Hwfpp: OpsemPP.wf_State cfg S) stinfo Hp
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo),
  alive_store.wf_State pinfo stinfo cfg S -> 
  vev_State (value_id (LAS_lid pinfo lasinfo)) (LAS_value pinfo lasinfo) 
    (PI_f pinfo) cfg S.
Proof.
  intros.
  destruct cfg, S.
  destruct CurTargetData as [los nts].
  destruct Hwfpp as [Hwfg [Hwfs [HmInS [Hnempty Hstks]]]].
  unfold alive_store.wf_State in H.
  simpl in H. simpl.
  eapply las__alive_store__vev_ECStack; eauto.
Qed.

Definition fdef_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) f1 f2
  : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    subst_fdef (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo) f1 = f2
  else f1 = f2.

Definition cmds_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) (f1:fdef)
  cs1 cs2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    List.map (subst_cmd (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo)) cs1 
      = cs2
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) f1 b1 b2
  : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then
    subst_block (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo) b1 = b2
  else b1 = b2.

Definition products_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) Ps1 Ps2
  : Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation pinfo lasinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) S1 S2
  : Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation pinfo lasinfo Ps1 Ps1
   end) S1 S2.

Definition EC_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) 
  (EC1 EC2:@Opsem.ExecutionContext DGVs) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation pinfo lasinfo f1 f2 /\
       tmn1 = tmn2 /\ als1 = als2 /\
       block_simulation pinfo lasinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       lc1 = lc2 /\
       cmds_simulation pinfo lasinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) 
  (ECs1 ECs2:@Opsem.ECStack DGVs) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation pinfo lasinfo EC1 EC2 /\ 
    ECs_simulation pinfo lasinfo ECs1' ECs2'
| _, _ => False
end.

Definition State_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) 
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\ 
    products_simulation pinfo lasinfo Ps1 Ps2 /\
    ECs_simulation pinfo lasinfo ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2
end.

Lemma las_is_sim : forall pinfo lasinfo Cfg1 St1 Cfg2 St2 St2' tr2 tr1 St1'
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hsim: State_simulation pinfo lasinfo Cfg1 St1 Cfg2 St2)
  (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2) 
  (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
  State_simulation pinfo lasinfo Cfg1 St1' Cfg2 St2' /\ tr1 = tr2.
Proof.
(*
  intros.
  (sInsn_cases (induction Hop) Case).
*)

Admitted.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
