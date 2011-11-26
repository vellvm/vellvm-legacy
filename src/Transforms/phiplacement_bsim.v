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
Require Import promotable_props.

Ltac zauto := auto with zarith.
Ltac zeauto := eauto with zarith.

Import Promotability.

(* Simulation *)

Definition DGVMap := @Opsem.GVsMap DGVs.

Definition not_temporaries (i0 : id) (newids : ATree.t (id * id * id)) : Prop :=
forall l0,
  match ATree.get l0 newids with
  | Some (lid, pid, sid) => i0 <> lid /\ i0 <> pid /\ i0 <> sid
  | None => True
  end.

Definition reg_simulation (pinfo: PhiInfo) (f1:fdef) (lc1 lc2:DGVMap) : Prop :=  
  let '(mkPhiInfo f rd succs preds pid ty al newids) := pinfo in
  if (fdef_dec f1 f) then 
    (forall i0, 
      not_temporaries i0 newids -> lookupAL _ lc1 i0 = lookupAL _ lc2 i0) 
  else lc1 = lc2.

Definition fdef_simulation (pinfo: PhiInfo) f1 f2: Prop :=
  let '(mkPhiInfo f rd succs preds pid ty al _) := pinfo in
  if (fdef_dec f1 f) then 
    phinodes_placement f1 rd pid ty al succs preds = f2
  else f1 = f2.

Definition wf_tmp_value (pinfo: PhiInfo) TD (M2:mem) (lc2:DGVMap) (tid:id)   
  : Prop :=  
  exists gvsa, exists gv, 
    lookupAL _ lc2 (PI_id pinfo) = Some gvsa /\
    mload TD M2 gvsa (PI_typ pinfo) (PI_align pinfo) = Some gv /\
    lookupAL _ lc2 tid = Some gv.

Definition cmds_simulation (pinfo: PhiInfo) TD (M2:mem) lc2 (f1:fdef) (b1:block) 
  cs1 cs2 : Prop :=
  let '(mkPhiInfo f rd succs preds pid ty al newids) := pinfo in
  if (fdef_dec f1 f) then 
    let '(block_intro l1 _ cs _) := b1 in 
    match ATree.get l1 newids with
    | Some (lid, pid', sid) =>
      let suffix := 
        match ATree.get l1 succs with
        | Some (_::_) => [insn_load lid ty (value_id pid) al]
        | _ => nil
        end in
      let prefix :=
        match ATree.get l1 preds with
        | Some (_ :: _) => 
             [insn_store sid ty (value_id pid') (value_id pid) al]
        | _ => nil
        end in
      (* If cs1 is at the beginning of b1, 
         then cs2 must be at the beginning of b2, or 
                       exactly after the inserted store in b2;
              moreover, if pid' is inserted, its value should be correct. *)
      (cs = cs1 ->          
       (cs2 = prefix ++ cs1 ++ suffix \/ cs2 = cs1 ++ suffix) /\ 
       (prefix <> nil -> wf_tmp_value pinfo TD M2 lc2 pid')) /\
      (* If cs1 isn't at the beginning of b1, 
         then cs2 matches cs1 with suffix. *)
      (cs <> cs1 -> cs2 = cs1 ++ suffix) /\
      (* Moreover, when both cs1 and cs2 are at the end, and 
                        a load is inserted for b2, 
                   the value of the load shoule be correct. *)
      (suffix <> nil -> cs1 = nil -> cs2 = nil -> 
       wf_tmp_value pinfo TD M2 lc2 lid)
    | _ => cs1 = cs2
    end
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) f1 b1 b2: Prop :=
  let '(mkPhiInfo f _ succs preds pid ty al newids) := pinfo in
  if (fdef_dec f1 f) then
     phinodes_placement_block b1 pid ty al newids succs preds = b2
  else b1 = b2.

Definition products_simulation (pinfo: PhiInfo) Ps1 Ps2: Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation pinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) S1 S2: Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation pinfo Ps1 Ps1
   end) S1 S2.

Definition EC_simulation_head (TD:TargetData) Ps1 (pinfo: PhiInfo) 
  (EC1 EC2:Opsem.ExecutionContext) (M2:mem) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       let '(los, nts) := TD in
       blockInFdefB b1 f1 = true /\
       InProductsB (product_fdef f1) Ps1 = true /\
       fdef_simulation pinfo f1 f2 /\
       tmn1 = tmn2 /\ als1 = als2 /\
       (getBlockLabel b1 = getBlockLabel b2) /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       reg_simulation pinfo f1 lc1 lc2 /\
       cmds_simulation pinfo TD M2 lc2 f1 b1 cs1 cs2
  end.

Definition EC_simulation_tail (TD:TargetData) Ps1 (pinfo: PhiInfo) 
  (EC1 EC2:Opsem.ExecutionContext) (M2:mem) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 ((insn_call _ _ _ _ _ _ as c2)::cs2) tmn2 lc2 als2) =>
       let '(los, nts) := TD in
       blockInFdefB b1 f1 = true /\
       InProductsB (product_fdef f1) Ps1 = true /\
       fdef_simulation pinfo f1 f2 /\
       tmn1 = tmn2 /\ als1 = als2 /\
       (getBlockLabel b1 = getBlockLabel b2) /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++c2::cs2) tmn2) /\
       reg_simulation pinfo f1 lc1 lc2 /\
       cmds_simulation pinfo TD M2 lc2 f1 b1 cs1 (c2::cs2)
  | _ => False
  end.

Fixpoint ECs_simulation_tail (TD:TargetData) Ps1 (pinfo: PhiInfo) 
  (ECs1 ECs2:Opsem.ECStack) (M2:mem) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation_tail TD Ps1 pinfo EC1 EC2 M2 /\ 
    ECs_simulation_tail TD Ps1 pinfo ECs1' ECs2' M2
| _, _ => False
end.

Fixpoint ECs_simulation (TD:TargetData) Ps1 (pinfo: PhiInfo) 
  (ECs1 ECs2:Opsem.ECStack) (M2:mem) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation_head TD Ps1 pinfo EC1 EC2 M2 /\ 
    ECs_simulation_tail TD Ps1 pinfo ECs1' ECs2' M2
| _, _ => False
end.

Definition State_simulation (pinfo: PhiInfo) 
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    let '(los, nts) := TD1 in
    wf_system nil S1 /\
    moduleInSystemB (module_intro los nts Ps1) S1 = true /\
    system_simulation pinfo S1 S2 /\ 
    TD1 = TD2 /\ 
    products_simulation pinfo Ps1 Ps2 /\
    ECs_simulation TD1 Ps1 pinfo ECs1 ECs2 M2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2
end.

(*
Lemma cmds_simulation_nil_br_inv: forall B F tmn pinfo cs2
  (HBinF : blockInFdefB B F = true)
  (Heq: exists l1, exists ps1, exists cs11,
          B = block_intro l1 ps1 (cs11 ++ nil) tmn)
  (Hsucc: successors_terminator tmn <> nil)
  (Htcmds: cmds_simulation pinfo F (getBlockLabel B) nil cs2),
  if fdef_dec F pinfo.(PI_f) then   
    match ATree.get (getBlockLabel B) pinfo.(PI_newids) with
    | None => cs2 = nil
    | Some (lid', _, _) =>
        cs2 = [insn_load lid' pinfo.(PI_typ) (value_id pinfo.(PI_id)) 
                pinfo.(PI_align)]
    end
  else
    cs2 = nil.
Admitted.

Lemma lookup_fdef_sim__block_sim : forall pinfo f1 f2 l0 b1,
  fdef_simulation pinfo f1 f2 ->
  lookupBlockViaLabelFromFdef f1 l0 = Some b1 ->
  exists b2,
    lookupBlockViaLabelFromFdef f2 l0 = Some b2 /\
    block_simulation pinfo f1 b1 b2.
Admitted.

Lemma simulation__getOperandValue: forall TD v lc gl2 lc2 g F
  (HeqR : Opsem.getOperandValue TD v lc gl2 = ret g)
  (Hrsim : reg_simulation F lc lc2),
  Opsem.getOperandValue TD v lc2 gl2 = ret g.
Proof.
  intros.
  destruct Hrsim as [J1 _].
  destruct v; auto.
    apply J1 in HeqR; auto.
Qed.

Lemma returnUpdateLocals_rsim : forall TD i0 n c t v p Result lc lc' gl2 
  lc'' F F' lc2' lc2
  (H1 : Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc
         lc' gl2 = ret lc'')
  (Hrsim : reg_simulation F lc lc2)
  (Hrsim' : reg_simulation F' lc' lc2'),
  exists lc2'',
    Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc2 lc2' gl2 
      = ret lc2'' /\ reg_simulation F' lc'' lc2''.
Proof.
  unfold Opsem.returnUpdateLocals in *.
  intros.
  remember (Opsem.getOperandValue TD Result lc gl2) as R.
  destruct R; inv H1.
    destruct n; inv H0.
    erewrite simulation__getOperandValue; eauto. 

    destruct t; tinv H1.
    erewrite simulation__getOperandValue; eauto. 
    destruct (lift_op1 DGVs (fit_gv TD t) g t); inv H1.
    exists (updateAddAL (GVsT DGVs) lc2' i0 g0).
    split; auto.
      destruct Hrsim' as [J1 J2].
      split; intros.
        destruct (id_dec i0 i1); subst.
          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupAL_updateAddAL_eq in H; auto.

          rewrite <- lookupAL_updateAddAL_neq; auto.
          rewrite <- lookupAL_updateAddAL_neq in H; auto.

        admit.
Qed.

(* copied from SB *)
Lemma cmds_at_block_tail_next : forall B c cs tmn2,
  (exists l1, exists ps1, exists cs11, B = 
    block_intro l1 ps1 (cs11 ++ c :: cs) tmn2) ->
  exists l1, exists ps1, exists cs11, B = block_intro l1 ps1 (cs11 ++ cs) tmn2.
Proof.
  intros.
  destruct H as [l1 [ps1 [cs11 H]]]; subst.
  exists l1. exists ps1. exists (cs11 ++ [c]). simpl_env. auto.
Qed.

Ltac destruct_ctx_br :=
match goal with
| [Hsim : State_simulation _
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           Opsem.ECS := {|
                          Opsem.CurFunction := ?F;
                          Opsem.CurBB := _;
                          Opsem.CurCmds := nil;
                          Opsem.Terminator := _;
                          Opsem.Locals := _;
                          Opsem.Allocas := _ |} :: _;
           Opsem.Mem := _ |} ?Cfg2 ?St2 |- _] =>
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Heq2 
    [Heq3 Heq4]]]]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct HsimEC as [HBinF [HFinPs [Htfdef [Heq0 [Heq1 [Hnth [Heqb1 [Heqb2     
    [Hrsim Htcmds]]]]]]]]]; subst
end.

Lemma phinodes_placement_is_correct__sBranch: forall 
  (pinfo : PhiInfo) (Cfg2 : OpsemAux.Config) (St2 : Opsem.State)
  (S : system) (TD : TargetData) (Ps : list product) (F : fdef) (B : block)
  (lc : Opsem.GVsMap) (gl : GVMap) (fs : GVMap) (bid : id) (Cond : value)
  (l1 : l) (l2 : l) (ECs : list Opsem.ExecutionContext) (Mem : mem) 
  (als : list mblock) maxb EC1 Cfg1 (Hwfpi: WF_PhiInfo pinfo)
  (Heq1: Cfg1 = {| OpsemAux.CurSystem := S;
                   OpsemAux.CurTargetData := TD;
                   OpsemAux.CurProducts := Ps;
                   OpsemAux.Globals := gl;
                   OpsemAux.FunTable := fs |})
  (Hnoalias: noalias_EC maxb pinfo TD Mem EC1)
  (Heq2: EC1 = {| Opsem.CurFunction := F;
                  Opsem.CurBB := B;
                  Opsem.CurCmds := nil;
                  Opsem.Terminator := insn_br bid Cond l1 l2;
                  Opsem.Locals := lc;
                  Opsem.Allocas := als |})
  (Hsim : State_simulation pinfo Cfg1
            {| Opsem.ECS := EC1 :: ECs;
               Opsem.Mem := Mem |} Cfg2 St2)
  (conds : GVsT DGVs) (c : GenericValue) (l' : l) (ps' : phinodes)
  (cs' : cmds) (tmn' : terminator) (lc' : Opsem.GVsMap)
  (H : Opsem.getOperandValue TD Cond lc gl = ret conds)
  (H0 : c @ conds)
  (H1 : ret block_intro l' ps' cs' tmn' =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1))
  (H2 : Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc =
       ret lc'),
  exists St2' : Opsem.State,
     Opsem.sop_plus Cfg2 St2 St2' trace_nil /\
     State_simulation pinfo Cfg1
     {|Opsem.ECS := {| Opsem.CurFunction := F;
                       Opsem.CurBB := (block_intro l' ps' cs' tmn');
                       Opsem.CurCmds := cs';
                       Opsem.Terminator := tmn';
                       Opsem.Locals := lc';
                       Opsem.Allocas := als |} :: ECs;
       Opsem.Mem := Mem |} Cfg2 St2'.
Proof.
  intros. subst.
  destruct_ctx_br.
  assert (exists b2,
    (if isGVZero (los, nts) c
     then lookupBlockViaLabelFromFdef F2 l2
     else lookupBlockViaLabelFromFdef F2 l1) = Some b2 /\
    block_simulation pinfo F (block_intro l' ps' cs' tmn') b2) as Hfind.
    symmetry in H1.
    destruct (isGVZero (los, nts) c); 
      eapply lookup_fdef_sim__block_sim in H1; eauto.
  destruct Hfind as [b2 [Hfind Htblock]].
  eapply cmds_simulation_nil_br_inv in Htcmds; 
    try solve [eauto | simpl; congruence].
  destruct (fdef_dec F (PI_f pinfo)) as [ e | n]; subst.
  SCase "F is tranformed".
    assert (phinodes_placement_block (block_intro l' ps' cs' tmn') (PI_id pinfo)
      (PI_typ pinfo) (PI_align pinfo) (PI_newids pinfo) (PI_succs pinfo) 
      (PI_preds pinfo) = b2) as EQ.
      clear - Htblock. destruct pinfo. simpl in *.
      destruct (fdef_dec PI_f0 PI_f0); auto.
        congruence.
    subst. clear Htblock. simpl in Hfind.
    assert ((PI_newids pinfo) ! l' <> None) as Hreach'.
      admit. (* reachable *)
    remember ((PI_newids pinfo) ! l') as R1.
    destruct R1 as [[[lid' pid'] sid']|]; try congruence.
    assert (exists prd, exists prds, (PI_preds pinfo) ! l' = Some (prd::prds)) 
      as R2.
      admit. (* must be of at most one pred *)
    destruct R2 as [prd [prds Heq]].
    rewrite Heq in Hfind.
    assert ((PI_newids pinfo) ! (getBlockLabel B) <> None) as Hreach.
      admit. (* reachable *)
    remember ((PI_newids pinfo) ! (getBlockLabel B)) as R.
    destruct R as [[[lid pid] sid]|]; subst; try congruence.
    assert (exists mp, exists gv,
      getOperandValue (los, nts) (value_id (PI_id pinfo)) lc gl2 = Some mp /\
      mload (los, nts) M2 mp (PI_typ pinfo) (PI_align pinfo) = Some gv) as Halc.
      clear - Hnoalias.
      (* By promotablity *)
      unfold noalias_EC in Hnoalias.
      destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
      assert (exists gvsa, lookupAL _ lc (PI_id pinfo) = Some gvsa) 
        as Hlkup.
        (* WF ssa isnt stuck by accessing undefined variables *)
        admit.
      destruct Hlkup as [gvsa Hlkup]. simpl. 
      change (GVsT DGVs) with GenericValue in Hlkup.
      rewrite Hlkup.
      apply Hnoalias in Hlkup; auto.
      destruct Hlkup as [[J1 [J2 [gv J3]]] _].
      exists gvsa. exists gv. auto.
    destruct Halc as [mp [gv [Hget Hld]]].
    assert (reg_simulation (PI_f pinfo) lc 
             (updateAddAL _ lc2 lid ($ gv # PI_typ pinfo $))) as Hrsim'.
      admit. (* Hrsim HeqR *)
    remember (cs' ++ 
              match (PI_succs pinfo) ! l' with
              | ret nil => nil
              | ret (_ :: _) =>
                  [insn_load lid' (PI_typ pinfo)
                    (value_id (PI_id pinfo)) (PI_align pinfo)]
              | merror => nil
              end) as cs2'.
    remember (block_intro l'
                (gen_phinode pid' (PI_typ pinfo) (PI_newids pinfo)
                   (prd :: prds) :: ps')
                (insn_store sid' (PI_typ pinfo) (value_id pid')
                   (value_id (PI_id pinfo)) (PI_align pinfo) :: cs2') tmn') 
             as b2.
    assert (exists lc2', 
      Opsem.switchToNewBasicBlock (los, nts) b2 B2 gl2 
        (updateAddAL _ lc2 lid ($ gv # PI_typ pinfo $)) = ret lc2' /\
      reg_simulation (PI_f pinfo) lc' lc2' /\ 
      lookupAL _ lc2' pid' = Some gv) as Hswitch.
      admit. (* switch *)
    destruct Hswitch as [lc2' [Hswitch [Hrsim'' Hlk]]].
    assert (mstore (los,nts) M2 mp (PI_typ pinfo) gv (PI_align pinfo) 
      = Some M2) as Hst.
      clear - Hld. admit. (* By MemModel *)
    exists (Opsem.mkState ((Opsem.mkEC F2 b2 cs2' tmn' lc2' als2)::ECs2) M2).
    split.
    SSCase "opsem".
      rewrite <- (@trace_app_nil__eq__trace trace_nil).
      apply Opsem.sop_plus_cons with (state2:=
         Opsem.mkState 
           ((Opsem.mkEC F2 B2 nil (insn_br bid Cond l1 l2) 
             (updateAddAL _ lc2 lid ($ gv # (PI_typ pinfo) $)) als2)::ECs2) M2).
        eapply simulation__getOperandValue with (lc2:=lc2) in Hget; eauto.
        econstructor; eauto.

      rewrite <- (@trace_app_nil__eq__trace trace_nil).
      apply Opsem.sop_star_cons with (state2:=
         Opsem.mkState 
           ((Opsem.mkEC F2 b2 
             (insn_store sid' (PI_typ pinfo) (value_id pid')
               (value_id (PI_id pinfo)) (PI_align pinfo) :: cs2') 
             tmn' lc2' als2)::ECs2) M2).
        subst.
        eapply simulation__getOperandValue with 
          (lc2:=updateAddAL _ lc2 lid ($ gv # (PI_typ pinfo) $)) in H; eauto.

      apply OpsemProps.sInsn__implies__sop_star.
      clear c H0 H1 Hfind.
      econstructor; eauto.
        eapply simulation__getOperandValue with (lc:=lc'); eauto.
          clear - Hget H2.
          admit. (* By WF promotablity *)
    SSCase "sim".
      assert (blockInFdefB (block_intro l' ps' cs' tmn') (PI_f pinfo))as HBinF'.
        assert (HuniqF:=HFinPs).
        eapply wf_system__uniqFdef in HuniqF; eauto.
        destruct (PI_f pinfo) as [[] bs].
        destruct HuniqF as [HuniqBlocks HuniqArgs].
        symmetry in H1.
        destruct (isGVZero (los,nts) c);
          apply genLabel2Block_blocks_inv with (f:=fheader_intro f t i0 a v) 
            in H1; auto; destruct H1; eauto.
      subst.
      repeat (split; eauto 2 using cmds_at_block_tail_next).
        exists l'. exists ps'. exists nil. auto.

        exists l'. 
        exists (gen_phinode pid' (PI_typ pinfo) (PI_newids pinfo) (prd :: prds)
          :: ps').
        exists [insn_store sid' (PI_typ pinfo) (value_id pid')
                 (value_id (PI_id pinfo)) (PI_align pinfo)].
        simpl_env. auto.

        destruct pinfo. simpl in *.
        destruct (fdef_dec PI_f0 PI_f0); try congruence.
          admit. (* WF_PhiInfo *)

  SCase "F isnt tranformed".
    admit. (* simpl case *)
Qed.
*)

Notation "$ gv # t $" := (DGVs.(gv2gvs) gv t) (at level 41).

Definition noalias_EC (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (ec:Opsem.ExecutionContext) : Prop :=
let '(Opsem.mkEC f b cs tmn lc als) := ec in
if (fdef_dec (PI_f pinfo) f) then wf_defs maxb pinfo TD M lc als else True.

Lemma noalias_State__noalias_EC: forall maxb pinfo Cfg EC ECs Mem,
  Promotability.wf_State maxb pinfo Cfg 
    {| Opsem.ECS := EC :: ECs; Opsem.Mem := Mem |} ->
  noalias_EC maxb pinfo (OpsemAux.CurTargetData Cfg) Mem EC.
Proof.
  intros. destruct Cfg.
  destruct H as [[J1 _] _].
  destruct EC. destruct J1 as [J1 _].
  simpl. auto.
Qed.

Ltac destruct_ctx_return :=
match goal with
| [Hsim : State_simulation _ ?Cfg1 ?St1 
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           Opsem.ECS := {|
                          Opsem.CurFunction := ?F;
                          Opsem.CurBB := _;
                          Opsem.CurCmds := nil;
                          Opsem.Terminator := _;
                          Opsem.Locals := _;
                          Opsem.Allocas := _ |}
                          :: {|
                             Opsem.CurFunction := ?F';
                             Opsem.CurBB := _;
                             Opsem.CurCmds := ?c' :: _;
                             Opsem.Terminator := _;
                             Opsem.Locals := _;
                             Opsem.Allocas := _ |} :: _;
           Opsem.Mem := _ |} |- _] =>
  destruct Cfg1 as [S1 TD1 Ps1 gl1 fs1];
  destruct St1 as [ECs1 M1];
  destruct TD1 as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Heq2 
    [Heq3 Heq4]]]]]]]]; subst;
  destruct ECs1 as [|[F1 B1 cs1 tmn1 lc1 als1] ECs1];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct ECs1 as [|[F1' B1' cs1' tmn1' lc1' als1'] ECs1];
    try solve [inversion HsimECs];
  destruct HsimECs as [HsimEC' HsimECs];
  destruct HsimEC as [HBinF [HFinPs [Htfdef [Heq0 [Heq1 [Hnth [Heqb1 [Heqb2     
    [Hrsim Htcmds]]]]]]]]]; subst;
  destruct c'; try solve [inversion HsimEC'];
  destruct HsimEC' as [HBinF' [HFinPs' [Htfdef' [Heq0' [Heq1' [Hnth' 
    [Heqb1' [Heqb2' [Hrsim' Htcmds']]]]]]]]]; subst;
  fold ECs_simulation_tail in HsimECs
end.

Lemma cmds_simulation_nil_ret_inv: forall TD M2 lc2 F1 B1 cs1 pinfo
  (Htcmds: cmds_simulation pinfo TD M2 lc2 F1 B1 cs1 nil),
  cs1 = nil.
Proof.
  intros.
  destruct pinfo. simpl in Htcmds. unfold wf_tmp_value in Htcmds. simpl in Htcmds.
  destruct (fdef_dec F1 PI_f0); subst; auto.
  destruct B1.
  destruct (PI_newids0 ! l0) as [[[]]|]; auto.
  destruct Htcmds as [J1 [J2 _]].
  destruct (list_eq_dec cmd_dec c cs1).
    apply J1 in e. 
    destruct e as [[e | e] _];
      repeat match goal with
      | H : nil = _ ++ _ |- _ => symmetry in H
      | H : _ ++ _ = nil |- _ => apply app_eq_nil in H; destruct H; auto
      end.

    apply J2 in n.
    repeat match goal with
    | H : nil = _ ++ _ |- _ => symmetry in H
    | H : _ ++ _ = nil |- _ => apply app_eq_nil in H; destruct H; auto
    end.
Qed.

Ltac cmds_simulation_cons_inv_tac1 :=
let foo cs2 e :=
    exists cs2;
    rewrite e; simpl_env;
    split; try solve 
      [auto |
       split; intros; try solve
         [split; auto |
          split; try solve [auto | intros; congruence]]
      ] in
match goal with
| e : ?c :: ?cs2 = ?cs1 ++ nil |- _ => foo cs2 e
| e : ?c :: ?cs2 = nil ++ ?cs1 ++ nil |- _ => foo cs2 e
end.

Definition isnt_inserted_ldst pinfo c : Prop :=
match c with
| insn_load id0 _ _ _ | insn_store id0 _ _ _ _ => 
    not_temporaries id0 (PI_newids pinfo)
| _ => True
end.

Ltac cmds_simulation_cons_inv_tac2 :=
let foo e cs1 Hnoldst l0 HeqR :=
    simpl_env in e;
    destruct cs1; inv e; 
      try solve [
        assert (J:=Hnoldst l0); simpl in J; rewrite <- HeqR in J;
        destruct J as [J7 [J8 J9]]; try congruence];
    exists cs1;
    split; try solve 
      [auto |
       split; intros; 
       split; auto; try solve [
         intros; subst;
         match goal with
         | H1 : nil ++ [_] = nil |- _ => inv H1
         end
         ]
      ] in
match goal with
| Hnoldst : isnt_inserted_ldst _ ?c,
  HeqR : Some (_, _, _) = _ ! ?l0 |- _ => 
  match goal with
  | e : ?c :: ?cs2 = nil ++ ?cs1 ++ [insn_load _ _ _ _] |- _ => 
      foo e cs1 Hnoldst l0 HeqR
  | e : ?c :: ?cs2 = ?cs1 ++ [insn_load _ _ _ _] |- _ => foo e cs1 Hnoldst l0 HeqR
  end
end.

Ltac cmds_simulation_cons_inv_tac3 R2 :=
 let l2 := fresh "l2" in
 destruct R2 as [l2|]; try solve [
   destruct l2; try solve 
     [cmds_simulation_cons_inv_tac1|
      cmds_simulation_cons_inv_tac2] |
   cmds_simulation_cons_inv_tac1].

Lemma app_cons_is_larger: forall A cs3 cs2 (c:A),
  cs2 = cs3 ++ c :: cs2 -> False.
Proof.
  intros.
  assert (J:=app_length cs3 (c::cs2)).
  rewrite <- H in J.
  simpl in J. omega.
Qed.

Lemma cmds_simulation_other_cons_inv: forall pinfo TD M2 lc2 F1 B1 cs1 c cs2
  (Htcmds: cmds_simulation pinfo TD M2 lc2 F1 B1 cs1 (c::cs2))
  (Hneq: F1 <> PI_f pinfo),
  exists cs1', 
    cs1 = c::cs1' /\   
    cmds_simulation pinfo TD M2 lc2 F1 B1 cs1' cs2.
Proof.
  intros.
  destruct pinfo. simpl in *. unfold wf_tmp_value in *. simpl in *.
  destruct (fdef_dec F1 PI_f0); subst; try congruence.
  eauto.
Qed.

Lemma cmds_simulation_same_cons_inv: forall pinfo TD M2 lc2 F1 B1 cs1 c cs2
  (Htcmds: cmds_simulation pinfo TD M2 lc2 F1 B1 cs1 (c::cs2))
  (Heq: exists l0, exists ps0, exists cs0, exists tmn0, 
          B1 = block_intro l0 ps0 (cs0++cs1) tmn0)
  (Hnoldst: isnt_inserted_ldst pinfo c)
  (Heq': F1 = PI_f pinfo),
  exists cs1', 
    cs1 = c::cs1' /\   
    cmds_simulation pinfo TD M2 lc2 F1 B1 cs1' cs2.
Proof.
  intros.
  destruct pinfo. simpl in *. unfold wf_tmp_value in *. simpl in *.
  destruct (fdef_dec F1 PI_f0); subst; try congruence.
  destruct B1.
  remember (PI_newids0 ! l0) as R.
  destruct R as [[[]]|]; eauto.
  destruct Htcmds as [J1 [J2 J3]].
  remember (PI_preds0 ! l0) as R1.
  remember (PI_succs0 ! l0) as R2.
  destruct (list_eq_dec cmd_dec c0 cs1).
  Case "1".
    clear J2. apply_clear J1 in e. 
    destruct e as [[e | e] J4];
      destruct R1 as [l1|]; try solve [
        destruct l1; try solve [
          cmds_simulation_cons_inv_tac3 R2 | 
          inv e; assert (J:=Hnoldst l0); simpl in J; rewrite <- HeqR in J;
            destruct J as [J7 [J8 J9]]; try congruence ] | 
        cmds_simulation_cons_inv_tac3 R2].

  Case "2".
    assert (n':=n).
    apply J2 in n. 
    destruct R2 as [l2|].
    SCase "2.1".    
      destruct l2.
      SSCase "2.1.1".    
        exists cs2.
        simpl_env in n. subst cs1.
        split; auto.
        destruct R1 as [l1|].
         SSSCase "2.1.1.1".    
          destruct l1.
          SSSSCase "2.1.1.1.1".    
            split; intros;
              split; try solve [auto | intros; congruence].
            split; intros.
              subst. destruct Heq as [l3 [ps3 [cs3 [tmn3 Heq]]]].
              inversion Heq.
              apply app_cons_is_larger in H2. inv H2.

          SSSSCase "2.1.1.1.2".    
             split; try solve [auto | intros; congruence].
        SSSCase "2.1.1.2".    
        split; intros.
          subst. destruct Heq as [l3 [ps3 [cs3 [tmn3 Heq]]]].
          inversion Heq.
          apply app_cons_is_larger in H2. inv H2.

          split; try solve [auto | intros; congruence].
          
      SSCase "2.1.2".    
        destruct cs1; inversion n.
        SSSCase "2.1.2.1".    
          subst c. 
          assert (J:=Hnoldst l0); simpl in J; rewrite <- HeqR in J;
            destruct J as [J7 [J8 J9]]; try congruence.

        SSSCase "2.1.2.2".    
          exists cs1.
          split; auto.
          destruct R1 as [l3|].
          SSSSCase "2.1.2.2.1".    
            destruct l3.
            SSSSSCase "2.1.2.2.1.1".    
              split; intros;
                split; try solve [auto | intros; congruence].
              intros. subst. inv H3.

            SSSSSCase "2.1.2.2.1.2".    
              split; intros.
                subst. destruct Heq as [l5 [ps3 [cs3 [tmn3 Heq]]]].
                inversion Heq.
                apply app_cons_is_larger in H2. inv H2.
              split; auto.
                intros. subst. inv H3.

          SSSSCase "2.1.2.2.2".    
            split; intros; auto.
            split; intros; auto.
              congruence.
            split; intros; auto.
              subst. inv H3.

    SCase "2.2".    
        exists cs2.
        simpl_env in n. subst cs1.
        split; auto.
        destruct R1 as [l1|].
        SSCase "2.2.1".    
          destruct l1.
          SSSCase "2.2.1.1".    
            split; intros;
              split; try solve [auto | intros; congruence].
          SSSCase "2.2.1.2".    
            split; intros.
              subst. destruct Heq as [l3 [ps3 [cs3 [tmn3 Heq]]]].
              inversion Heq.
              apply app_cons_is_larger in H2. inv H2.

              split; try solve [auto | intros; congruence].
        SSCase "2.2.2".    
          split; intros.
            subst. destruct Heq as [l3 [ps3 [cs3 [tmn3 Heq]]]].
            inversion Heq.
            apply app_cons_is_larger in H2. inv H2.

            split; try solve [auto | intros; congruence].
Qed.

Definition is_temporary i0 (newids : ATree.t (id * id * id)) : Prop :=
exists l0,
  match ATree.get l0 newids with
  | Some (lid, pid, sid) => i0 == lid \/ i0 == pid \/ i0 == sid
  | None => False
  end.

Definition is_inserted_ld pinfo c : Prop :=
match c with
| insn_load id0 _ _ _ => is_temporary id0 (PI_newids pinfo)
| _ => False
end.

Definition is_inserted_st pinfo c : Prop :=
match c with
| insn_store id0 _ _ _ _ => is_temporary id0 (PI_newids pinfo)  
| _ => False
end.

Lemma temporary_must_be_fresh: forall l0 ps0 cs0 c cs2 tmn0 PI_f0 PI_rd0 i0
  (Hin : blockInFdefB (block_intro l0 ps0 (cs0 ++ c :: cs2) tmn0) PI_f0 = true)
  (Hld : is_temporary i0 (fst (gen_fresh_ids PI_rd0 (getFdefLocs PI_f0))))
  (Heq : getCmdLoc c = i0),
  False.
Admitted.

Lemma cmds_simulation_same_head_inv: forall pinfo TD M2 lc2 F1 B1 cs1 c cs2
  (Hin: blockInFdefB B1 F1 = true) (Hwfpi: WF_PhiInfo pinfo)
  (Htcmds: cmds_simulation pinfo TD M2 lc2 F1 B1 cs1 (c::cs2))
  (Heq: exists l0, exists ps0, exists cs0, exists tmn0, 
          B1 = block_intro l0 ps0 (cs0++cs1) tmn0)
  (Hld: is_inserted_st pinfo c)
  (Heq': F1 = PI_f pinfo),
  exists l1, exists ps1, exists tmn1, exists lid, exists pid, exists sid, 
    B1 = block_intro l1 ps1 cs1 tmn1 /\
    ATree.get l1 (PI_newids pinfo) = Some (lid, pid, sid) /\
    c = insn_store sid (PI_typ pinfo) (value_id pid) (value_id (PI_id pinfo)) 
          (PI_align pinfo) /\
    ATree.get l1 (PI_preds pinfo) <> Some nil /\
    ATree.get l1 (PI_preds pinfo) <> None.
Proof.
  intros. subst.
  destruct c; tinv Hld.
  destruct Heq as [l0 [ps0 [cs0 [tmn0 Heq]]]]; subst.
  destruct pinfo. simpl in *. unfold wf_tmp_value in *. simpl in *.
  destruct (fdef_dec PI_f0 PI_f0); try congruence.
  destruct Hwfpi as [_ [_ [_ [_ Hwfpi]]]].
  remember (PI_newids0 ! l0) as R.
  destruct R as [[[]]|]; subst;
    try solve [eapply temporary_must_be_fresh in Hin; eauto; inv Hin].
  destruct Htcmds as [J1 [J2 _]].
  exists l0. exists ps0. exists tmn0. exists i1. exists i2. exists i3.
  remember (PI_preds0 ! l0) as R1.
  remember (PI_succs0 ! l0) as R2.
  destruct (list_eq_dec cmd_dec (cs0++cs1) cs1).
  Case "1".
    assert (cs0 = nil) as EQ. admit. clear e0.
    subst cs0.
    split; auto.
    split; auto.
    clear J2.
    destruct J1 as [J1 _]; auto.
    destruct J1 as [J1 | J1].
      destruct R1.
        destruct l1.  
          admit.

          inv J1. 
          split; auto.
          split; intros; congruence.
        admit.
      admit.

  Case "2".
    clear J1.
    apply_clear J2 in n.
    admit.
Qed.

Lemma cmds_simulation_tail_inv: forall pinfo TD M2 lc2 F1 B1 cs1 c cs2
  (Hin: blockInFdefB B1 F1 = true) (Hwfpi: WF_PhiInfo pinfo)
  (Htcmds: cmds_simulation pinfo TD M2 lc2 F1 B1 cs1 (c::cs2))
  (Heq: exists l0, exists ps0, exists cs0, exists tmn0, 
          B1 = block_intro l0 ps0 (cs0++cs1) tmn0)
  (Hld: is_inserted_ld pinfo c)
  (Heq': F1 = PI_f pinfo),
  exists lid, exists pid, exists sid, 
    cs1 = nil /\ cs2 = nil /\
    ATree.get (getBlockLabel B1) (PI_newids pinfo) = Some (lid, pid, sid) /\
    c = insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) (PI_align pinfo) /\
    ATree.get (getBlockLabel B1) (PI_succs pinfo) <> Some nil /\
    ATree.get (getBlockLabel B1) (PI_succs pinfo) <> None.
Proof.
  intros. subst.
  destruct c; tinv Hld.
  destruct Heq as [l0 [ps0 [cs0 [tmn0 Heq]]]]; subst.
  destruct pinfo. simpl in *. unfold wf_tmp_value in *. simpl in *.
  destruct (fdef_dec PI_f0 PI_f0); try congruence.
  destruct Hwfpi as [_ [_ [_ [_ Hwfpi]]]].
  remember (PI_newids0 ! l0) as R.
  destruct R as [[[]]|]; subst;
    try solve [eapply temporary_must_be_fresh in Hin; eauto; inv Hin].
  destruct Htcmds as [J1 [J2 J3]].
  exists i1. exists i2. exists i3.
  remember (PI_preds0 ! l0) as R1.
  remember (PI_succs0 ! l0) as R2.
  destruct (list_eq_dec cmd_dec (cs0++cs1) cs1).
  Case "1".
    assert (cs0 = nil) as EQ. admit. clear e0.
    subst cs0.
    clear J2.
    destruct J1 as [J1 _]; auto.
    destruct J1 as [J1 | J1].
      destruct R1.
        destruct l1.  
          destruct cs1.
            destruct R2; tinv J1.
              destruct l1; inv J1.
              repeat split; try solve [auto | intros; congruence]. 
            admit.

          inv J1. 
        admit.
      admit.

  Case "2".
    clear J1.
    apply_clear J2 in n.
    admit.
Qed.

Lemma phinodes_placement_is_bsim : forall maxb pinfo Cfg1 St1 Cfg2 St2 St2' tr
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hsim: State_simulation pinfo Cfg1 St1 Cfg2 St2)
  (Hop: Opsem.sInsn Cfg2 St2 St2' tr), 
  exists St1',
    Opsem.sop_star Cfg1 St1 St1' tr /\    
    State_simulation pinfo Cfg1 St1' Cfg2 St2'.
Proof.
  intros.
  (sInsn_cases (induction Hop) Case); 
    try apply noalias_State__noalias_EC in Hnoalias.

Case "sReturn".  
Focus.
  destruct_ctx_return.
  apply cmds_simulation_nil_ret_inv in Htcmds. subst.
  apply cmds_simulation_cons_inv in Htcmds'.
  destruct Htcmds' as [cs2'0 [EQ Htcmds']]; subst.
  eapply returnUpdateLocals_rsim in H1; eauto.
  destruct H1 as [lc2'' [H1 Hrsim'']].
  exists 
    (Opsem.mkState ((Opsem.mkEC F2' B2' cs2'0 tmn2' lc2'' als2')::ECs2) Mem').
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply OpsemProps.sInsn__implies__sop_plus.
    constructor; auto.
  
    repeat (split; eauto 2 using cmds_at_block_tail_next).

Case "sReturnVoid".
  destruct_ctx_return.
  eapply cmds_simulation_nil_ret_inv in Htcmds; eauto. subst.
  apply cmds_simulation_cons_inv in Htcmds'.
  destruct Htcmds' as [cs2'0 [EQ Htcmds']]; subst.
  exists 
    (Opsem.mkState ((Opsem.mkEC F2' B2' cs2'0 tmn2' lc2' als2')::ECs2) Mem').
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply OpsemProps.sInsn__implies__sop_plus.
    constructor; auto.
  
    repeat (split; eauto 2 using cmds_at_block_tail_next).

Case "sBranch". eapply phinodes_placement_is_correct__sBranch; eauto.
Case "sBranch_uncond". admit.
  (* eapply SBpass_is_correct__dsBranch_uncond; eauto. *)
Case "sBop". 

Admitted.
(*
eapply SBpass_is_correct__dsBop; eauto.

Case "sFBop". eapply SBpass_is_correct__dsFBop; eauto.
Case "sExtractValue". eapply SBpass_is_correct__dsExtractValue; eauto.
Case "sInsertValue". eapply SBpass_is_correct__dsInsertValue; eauto.
Case "sMalloc". eapply SBpass_is_correct__dsMalloc; eauto.
Case "sFree". eapply SBpass_is_correct__dsFree; eauto.
Case "sAlloca". eapply SBpass_is_correct__dsAlloca; eauto.
Case "sLoad_nptr". eapply SBpass_is_correct__dsLoad_nptr; eauto.
Case "sLoad_ptr". eapply SBpass_is_correct__dsLoad_ptr; eauto.
Case "sStore_nptr". eapply SBpass_is_correct__dsStore_nptr; eauto.
Case "sStore_ptr". eapply SBpass_is_correct__dsStore_ptr; eauto.
Case "sGEP". eapply SBpass_is_correct__dsGEP; eauto.
Case "sTrunc". eapply SBpass_is_correct__dsTrunc; eauto.
Case "sExt". eapply SBpass_is_correct__dsExt; eauto.
Case "sBitcast_nptr". eapply SBpass_is_correct__dsBitcase_nptr; eauto.
Case "sBitcast_ptr". eapply SBpass_is_correct__dsBitcase_ptr; eauto.
Case "sInttoptr". eapply SBpass_is_correct__dsInttoptr; eauto.
Case "sOthercast". eapply SBpass_is_correct__dsOthercast; eauto.
Case "sIcmp". eapply SBpass_is_correct__dsIcmp; eauto.
Case "sFcmp". eapply SBpass_is_correct__dsFcmp; eauto.
Case "sSelect_nptr". eapply SBpass_is_correct__dsSelect_nptr; eauto.
Case "sSelect_ptr". 
  eapply SBpass_is_correct__dsSelect_ptr; eauto.
  unfold prop_reg_metadata.
  destruct (isGVZero TD c); eauto.
Case "sCall". 
  eapply SBpass_is_correct__dsCall; eauto.
  apply mismatch_cons_false in H27. inv H27.
Case "sExCall". 
  symmetry in H32. apply mismatch_cons_false in H32. inv H32.
  eapply SBpass_is_correct__dsExCall; eauto.
Qed.
*)

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
