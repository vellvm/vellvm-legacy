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

Definition DGVMap := @Opsem.GVsMap DGVs.

Definition value_in_scope (v0:value) (ids0:ids) : Prop :=
match v0 with
| value_const _ => True
| value_id vid => In vid ids0
end.

Definition wf_defs (v1 v2:value) F TD gl (f:fdef) (lc:DGVMap) ids0: Prop :=
F = f ->
forall gvs1 gvs2,
  value_in_scope v1 ids0 ->
  value_in_scope v2 ids0 ->
  getOperandValue TD v1 lc gl = Some gvs1 ->
  getOperandValue TD v2 lc gl = Some gvs2 ->
  gvs1 = gvs2.

Definition inscope_of_ec (ec:@Opsem.ExecutionContext DGVs) : option ids :=
let '(Opsem.mkEC f b cs tmn lc als) := ec in
match cs with
| nil => inscope_of_tmn f b tmn
| c::_ => inscope_of_cmd f b c
end.

Definition wf_ExecutionContext v1 v2 F TD gl (ps:list product) 
  (ec:Opsem.ExecutionContext) : Prop :=
match inscope_of_ec ec with
| Some ids0 => 
    wf_defs v1 v2 F TD gl (Opsem.CurFunction ec) (Opsem.Locals ec) ids0
| _ => False
end.

Fixpoint wf_ECStack v1 v2 F TD gl (ps:list product) (ecs:Opsem.ECStack) : Prop :=
match ecs with
| nil => False
| ec::ecs' => 
    wf_ExecutionContext v1 v2 F TD gl ps ec /\ wf_ECStack v1 v2 F TD gl ps ecs'
end.

Definition wf_State v1 v2 F (cfg:OpsemAux.Config) (S:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg s td ps gl _ ) := cfg in
let '(Opsem.mkState ecs _) := S in
wf_ECStack v1 v2 F td gl ps ecs.

Definition eval_rhs TD (M:mem) gl (lc:DGVMap) (c:cmd) gv : Prop :=
match c with
| insn_bop _ bop0 sz v1 v2 => BOP TD lc gl bop0 sz v1 v2 = Some gv
| insn_fbop _ fbop fp v1 v2 => FBOP TD lc gl fbop fp v1 v2  = Some gv 
| insn_extractvalue id t v idxs => 
    exists gv0, getOperandValue TD v lc gl = Some gv0 /\
                extractGenericValue TD t gv0 idxs = Some gv
| insn_insertvalue _ t v t' v' idxs =>
    exists gv1, exists gv2, 
      getOperandValue TD v lc gl = Some gv1 /\
      getOperandValue TD v' lc gl = Some gv2 /\
      insertGenericValue TD t gv1 idxs t' gv2 = Some gv 
| insn_malloc _ t v aln | insn_alloca _ t v aln =>
    exists tsz, exists gns, exists gn, exists M', exists mb,
      getTypeAllocSize TD t = Some tsz /\
      getOperandValue TD v lc gl = Some gns /\
      gn @ gns /\
      malloc TD M tsz gn aln = Some (M', mb) /\
      gv = ($ (blk2GV TD mb) # (typ_pointer t) $)
| insn_load _ t v aln =>
    exists mps, exists mp, exists gv0,
      getOperandValue TD v lc gl = Some mps /\
      mp @ mps /\
      mload TD M mp t aln = Some gv0 /\
      gv = ($ gv0 # t$)
| insn_gep _ inbounds t v idxs =>
    exists mp, exists vidxss, exists vidxs,
      getOperandValue TD v lc gl = Some mp /\
      values2GVs TD idxs lc gl = Some vidxss /\
      vidxs @@ vidxss /\
      GEP TD t mp vidxs inbounds = Some gv
| insn_trunc _ truncop t1 v1 t2 => TRUNC TD lc gl truncop t1 v1 t2 = Some gv
| insn_ext _ extop t1 v1 t2 => EXT TD lc gl extop t1 v1 t2 = Some gv
| insn_cast _ castop t1 v1 t2 => CAST TD lc gl castop t1 v1 t2 = Some gv
| insn_icmp _ cond0 t v1 v2 => ICMP TD lc gl cond0 t v1 v2 = Some gv
| insn_fcmp _ fcond fp v1 v2 => FCMP TD lc gl fcond fp v1 v2 = Some gv
| insn_select _ v0 t v1 v2 =>
    exists cond, exists gvs1, exists gvs2, exists c,
      getOperandValue TD v0 lc gl = Some cond /\
      getOperandValue TD v1 lc gl = Some gvs1 /\
      getOperandValue TD v2 lc gl = Some gvs2 /\
      c @ cond /\
      gv = if isGVZero TD c then gvs2 else gvs1
| _ => True (* We may also consider call/excall, but ignore them so far *)
end.

Definition vev_defs (v1 v2:value) F TD M gl (f:fdef) (lc:DGVMap) c ids0: Prop :=
  F = f ->
  (value_in_scope v2 ids0 ->
   match Opsem.getOperandValue TD v2 lc gl with 
   | Some gv2 => 
       match v1 with
       | value_const _ => True
       | value_id id1 => 
           if (id1 == getCmdLoc c) then eval_rhs TD M gl lc c gv2
           else True
       end
   | _ => True
   end) /\
  (value_in_scope v1 ids0 ->
   match Opsem.getOperandValue TD v1 lc gl with 
   | Some gv1 => 
       match v2 with
       | value_const _ => True
       | value_id id2 => 
           if (id2 == getCmdLoc c) then eval_rhs TD M gl lc c gv1
           else True
       end
   | _ => True
  end).

Definition vev_ExecutionContext v1 v2 F TD M gl (ec:Opsem.ExecutionContext) 
  : Prop :=
let '(Opsem.mkEC f b cs _ lc _) := ec in
match cs with
| nil => True
| c::_ => 
    match inscope_of_cmd f b c with
    | None => True
    | Some ids0 => vev_defs v1 v2 F TD M gl f lc c ids0
    end
end.

Fixpoint vev_ECStack v1 v2 F TD M gl (ecs:Opsem.ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' => 
    vev_ExecutionContext v1 v2 F TD M gl ec /\ 
    vev_ECStack v1 v2 F TD M gl ecs'
end.

Definition vev_State v1 v2 F (cfg:OpsemAux.Config) (S:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg s td _ gl _ ) := cfg in
let '(Opsem.mkState ecs M) := S in
vev_ECStack v1 v2 F td M gl ecs.

Lemma preservation : forall v1 v2 F cfg S1 S2 tr
  (Hvev: vev_State v1 v2 F cfg S1)
  (Hwfpp: OpsemPP.wf_State cfg S1) (HsInsn: Opsem.sInsn cfg S1 S2 tr)
  (HwfS1: wf_State v1 v2 F cfg S1), wf_State v1 v2 F cfg S2.
Proof.
  intros.
  (sInsn_cases (induction HsInsn) Case); destruct TD as [los nts]; simpl HwfS1.

(*
Case "sReturn". 
Focus.
Local Opaque inscope_of_tmn inscope_of_cmd.

  destruct Hwfpp as 
    [_ [HwfSystem [HmInS [Hnempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [
      [
        [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]]
        [HwfECs HwfCall]
      ]
      HwfCall'
     ]]
    ]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs.

  simpl in Hideqv.

  destruct HwfS1 as [Hinscope1' [Hinscope2' HwfECs']].
  fold wf_ECStack in HwfECs'.
  unfold wf_ExecutionContext in Hinscope1', Hinscope2'.
  simpl in Hinscope1', Hinscope2'.

  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return rid RetTy Result))
             (insn_return rid RetTy Result)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
    unfold wf_ExecutionContext. simpl.
    remember (getCmdID c') as R.
    destruct c'; try solve [inversion H].
(*
    assert (In (insn_call i0 n c t v p) 
      (cs2'++[insn_call i0 n c t v p] ++ cs')) as HinCs.
      apply in_or_app. right. simpl. auto.
    assert (Hwfc := HBinF2).
    eapply wf_system__wf_cmd with (c:=insn_call i0 n c t v p) in Hwfc; eauto.
    assert (wf_fdef nil S (module_intro los nts Ps) F') as HwfF.
      eapply wf_system__wf_fdef; eauto.
    assert (uniqFdef F') as HuniqF.
      eapply wf_system__uniqFdef; eauto.
*)

      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        assert (~ In (getCmdLoc (insn_call i0 n c t v p)) (getCmdsLocs cs2')) 
          as Hnotin.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.
        assert (HeqR2':=HeqR2).
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        unfold Opsem.returnUpdateLocals in H1. simpl in H1.
        remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR.
          destruct t; tinv H1.
          remember (lift_op1 DGVs (fit_gv (los, nts) t) g t) as R2.
          destruct R2; inv H1.
          change i0 with 
            (getCmdLoc (insn_call i0 false c (typ_function t l4 v0) v p)); auto.

forall gvs1 gvs2, 
  In id1 ids0 -> 
  value_in_scope v2 ids0 -> 
  lookupAL _ lc id1 = Some gvs1 -> 
  getOperandValue TD v2 lc gl = Some gvs2 ->
  gvs1 = gvs2.

Lemma wf_defs_updateAddAL : forall id1 v2 ifs S M g1 lc' ids1 ids2 F1 B1 l3 ps1 
  cs tmn1 c TD gl (HinCs: In c cs)
  (Hreach: isReachableFromEntry F1 (block_intro l3 ps1 cs tmn1))
  (HBinF1: blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true)
  (HBinF2: blockInFdefB B1 F1 = true)
  (HwfF1 : wf_fdef ifs S M F1) (HuniqF:uniqFdef F1) 
  (HcInB : cmdInBlockB c B1 = true)
  (Hinscope : ret ids1 = inscope_of_id F1 B1 (getCmdLoc c)),
  wf_defs id1 v2 TD gl F1 lc' ids1 ->
  set_eq _ (getCmdLoc c::ids1) ids2 ->
  wf_GVs TD gl F1 lc' (getCmdLoc c) g1 ->
  wf_defs id1 v2 TD gl F1 (updateAddAL _ lc' (getCmdLoc c) g1) ids2.
Proof.
  intros ifs S M g1 lc' ids1 ids2 F1 B1 l3 ps1 cs tmn1 c TD gl HinCs Hreach 
    HBinF1 HBinF2 HwfF1 HuniqF HcInB HInscope HwfDefs Heq Hwfgvs.
  intros id1 gvs1 Hin Hlk.
  destruct Heq as [Hinc1 Hinc2].
  apply Hinc2 in Hin.
  simpl in Hin.
  intros c1 Hlkc1.
  assert (id1 = getCmdLoc c1) as EQ.
    apply lookupInsnViaIDFromFdef__eqid in Hlkc1. simpl in Hlkc1. auto.
  subst.
  assert (J:=Hlkc1).
  eapply wf_fdef__wf_insn_base in J; eauto.
  destruct J as [b1 HwfI].
  inv HwfI.
  destruct (eq_dec (getCmdLoc c) (getCmdLoc c1)).
  Case "1".
    rewrite e in *.
    rewrite lookupAL_updateAddAL_eq in Hlk; auto.  
    inv Hlk.
    destruct (@Hwfgvs c1) as [Heval Hreach']; auto.
    split; auto.
    apply eval_rhs_updateAddAL; auto.
    destruct (in_dec id_dec (getCmdLoc c1) (getCmdOperands c1)); auto.
    assert (exists n, nth_list_id n id_list = Some (getCmdLoc c1)) as Hnth.
      eapply getCmdOperands__nth_list_id; eauto.
    destruct Hnth as [n Hnth]. 
    eapply wf_operand_list__wf_operand in Hnth; eauto.
    inv Hnth.
    assert (b1 = block') as EQ.
      eapply insnInFdefBlockB__lookupBlockViaIDFromFdef__eq; eauto.
    subst.
    clear - Hinc1 HInscope H11 Hreach HinCs HwfF1 HBinF1 Hreach' H HuniqF.
    assert (H0:=H).
    apply Hreach' in H.
    destruct H11 as [H11 | [H11 | H11]]; auto.
      contradict H11. 
         assert (H':=H0).
         apply insnInFdefBlockB__blockInFdefB in H'.
         apply uniqFdef__uniqBlockLocs in H'; auto.
         apply insnInFdefBlockB__insnInBlockB in H0.
         apply insnDominates_spec1; auto.
      contradict H11. 
      apply insnInFdefBlockB__blockInFdefB in H0.
      eapply blockStrictDominates_isnt_refl; eauto.

  Case "2".
    destruct Hin as [Eq | Hin]; subst; try solve [contradict n; auto].
    rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
    assert (Hlk':=Hlk).
    apply HwfDefs in Hlk; auto.
    destruct (@Hlk c1) as [Heval Hreach']; auto.
    split; auto.
    apply eval_rhs_updateAddAL; auto.
    destruct (in_dec id_dec (getCmdLoc c) (getCmdOperands c1)); auto.
    assert (exists n, nth_list_id n id_list = Some (getCmdLoc c)) as Hnth.
      eapply getCmdOperands__nth_list_id; eauto.
    destruct Hnth as [n' Hnth]. 
    eapply wf_operand_list__wf_operand in Hnth; eauto.
    inv Hnth.
    clear - HInscope Hin H11 Hreach HinCs H0 HwfF1 HBinF1 HBinF2 Hreach' H9 
      HcInB n H HuniqF.
    assert (isReachableFromEntry F1 b1) as Hreach''.
      apply Hreach' in H; auto.
    destruct b1 as [l0 p c0 t]. 
    destruct B1 as [l1 p0 c2 t0]. simpl in HInscope.
    remember ((dom_analyze F1) !! l1) as R.
    destruct R.
    assert (block' = block_intro l3 ps1 cs tmn1) as RQ.
      clear - HinCs HBinF1 H9 HwfF1 Hin HuniqF.
      symmetry.
      eapply lookupBlockViaIDFromFdef__lookupBlockViaLabelFromFdef__eq; eauto.
        symmetry.
        apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
        simpl. apply in_or_app. right. apply in_or_app.
        left. apply getCmdLoc_in_getCmdsLocs; eauto.
    subst.
    destruct H11 as [H11 | [H11 | H11]]; auto.
    SCase "1".
      assert (block_intro l1 p0 c2 t0 = block_intro l0 p c0 t) as EQ.
        apply insnInFdefBlockB__blockInFdefB in H.
        eapply cmdInBlockB_eqBlock with (c:=c); eauto.
        eapply insnDominates_spec4; eauto.
      inv EQ.
      assert (insnDominates (getCmdLoc c1) (insn_cmd c) (block_intro l0 p c0 t))
        as Hdom.
        clear - Hin HInscope HcInB H HwfF1 HuniqF. 
        symmetry in HInscope. destruct F1 as [[] bs].
        apply fold_left__spec in HInscope. 
        destruct HInscope as [_ [_ HInscope]].
        apply HInscope in Hin. clear HInscope.
        destruct Hin as [Hin | [b1 [l1 [J1 [J2 J3]]]]].
        SSCase "1".
          eapply cmds_dominates_cmd__insnDominates; eauto.
            clear - Hin HuniqF. admit. (* c1 cannot be an arg *)

        SSCase "2".
          destruct b1.
          assert (l1 = l2) as EQ.
            apply lookupBlockViaLabelFromFdef_inv in J2; auto.
            destruct J2; auto.
          subst.
          eapply lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef in J2; 
            eauto.
          eapply insnInFdefBlockB__lookupBlockViaIDFromFdef in H; eauto.
          rewrite H in J2. inv J2.          
          apply ListSet.set_diff_elim2 in J1. contradict J1; simpl; auto.

      apply insnDominates_spec2 in Hdom; try solve [simpl; auto].
        eapply uniqFdef__uniqBlockLocs; eauto.
        eapply insnDominates_spec4 in Hdom; eauto.

    SCase "2".
      assert (block_intro l1 p0 c2 t0 = block_intro l3 ps1 cs tmn1) as EQ.
        apply In_InCmdsB in HinCs.
        eapply cmdInBlockB_eqBlock; eauto.
      inv EQ.
      assert (l0 <> l3) as Hneq.
        simpl in H11.
        remember ((dom_analyze F1) !! l0) as R. 
        destruct R.
        simpl in Hreach''. apply insnInFdefBlockB__blockInFdefB in H.
        eapply sdom_isnt_refl with (l':=l3) in Hreach''; eauto.
          rewrite <- HeqR0. simpl. auto.

      assert (In l0 bs_contents) as Hindom'.
        clear - H HeqR HInscope Hin Hneq HBinF1 HwfF1 HuniqF. 
        symmetry in HInscope. destruct F1 as [[] bs].
        apply fold_left__spec in HInscope.
        destruct HInscope as [_ [_ HInscope]].
        apply HInscope in Hin.
        destruct Hin as [Hid1 | [b1 [l1 [J1 [J2 J3]]]]].
          clear - HBinF1 H Hid1 Hneq HwfF1 HuniqF.
          assert (In (getCmdLoc c1)
            (getPhiNodesIDs ps1 ++ cmds_dominates_cmd cs (getCmdLoc c))) as Hin.
            clear - HuniqF Hid1. admit. (* c1 cannot be an arg *)
          eapply cmds_dominates_cmd__insnInFdefBlockB in Hin; eauto.
          eapply insn_cannot_be_in_different_blocks in H; eauto.
          inv H. congruence.

          destruct b1.
          assert (l1 = l2) as EQ.
            apply lookupBlockViaLabelFromFdef_inv in J2; auto.
            destruct J2; auto.
          subst.
          eapply lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef in J2;
            eauto.
          eapply insnInFdefBlockB__lookupBlockViaIDFromFdef in H; eauto.
          rewrite H in J2. inv J2.
          apply ListSet.set_diff_elim1 in J1; auto.             

      assert (In l3 (DomDS.L.bs_contents (bound_fdef F1) 
             ((dom_analyze F1) !! l0))) as Hindom.       
        clear - H11.
        unfold blockStrictDominates in H11.
        destruct ((dom_analyze F1) !! l0). simpl. auto.
      apply insnInFdefBlockB__blockInFdefB in H.
      eapply adom_acyclic in Hindom; eauto.
      rewrite <- HeqR. simpl. auto.
Qed. 











          eapply wf_defs_updateAddAL; eauto.
            simpl. apply In_InCmdsB. apply in_middle.
            apply wf_impure_id__wf_gvs; auto.
              simpl. intros c0 Hlkc0. intros b1 J.
              clear - Hreach2 J HuniqF Hlkc0 HBinF2. 
              eapply isReachableFromEntry_helper; eauto.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsLocs (cs2' ++ [insn_call i0 n c t v p] ++ [c0] ++ 
          cs'))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        assert (HeqR2':=HeqR2).
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        unfold returnUpdateLocals in H1. simpl in H1.
        remember (getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR.
          destruct t; tinv H1.
          remember (GVsSig.(lift_op1) (fit_gv (los, nts) t) g t) as R2.
          destruct R2; inv H1.
          inv Hwfc. inv H16. inv H7. inv H18.
          change i0 with 
            (getCmdLoc (insn_call i0 false c
              (typ_function typ1
                 (make_list_typ
                    (map_list_typ_attributes_value
                       (fun (typ_' : typ) attr (_ : value) => typ_')
                       typ'_attributes'_value''_list)) varg5) v
              (map_list_typ_attributes_value
                 (fun (typ_' : typ) attr (value_'' : value) => 
                    (typ_', attr, value_''))
                 typ'_attributes'_value''_list))); auto.
          eapply wf_defs_updateAddAL; eauto.
            simpl. apply In_InCmdsB. apply in_middle.
            apply wf_impure_id__wf_gvs; auto.
              simpl. intros c1 Hlkc1. intros b1 J.
              clear - Hreach2 J HuniqF Hlkc1 HBinF2. 
              eapply isReachableFromEntry_helper with (cs2:=[c0]++cs')
                (cs1:=cs2')(c1:=insn_call i0 false c
                     (typ_function typ1
                        (make_list_typ
                           (map_list_typ_attributes_value
                              (fun (typ_' : typ) attr (_ : value) => typ_')
                              typ'_attributes'_value''_list)) varg5) v
                     (map_list_typ_attributes_value
                        (fun (typ_' : typ) attr (value_'' : value) =>
                          (typ_', attr, value_'')) 
                        typ'_attributes'_value''_list)) in Hreach2; 
                 eauto.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto. 
    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[c']).   
      simpl_env. auto.

Transparent inscope_of_tmn inscope_of_cmd.
Unfocus.
*)

Admitted.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
