Require Import vellvm.

Ltac wfCall_inv :=
match goal with
| Heq3 : exists _,
           exists _,
             exists _,
               ?B = (_, stmts_intro _ _ _),
  HBinF1 : blockInFdefB ?B ?F = true,
  HwfCall : OpsemPP.wf_call
              {|
              Opsem.CurFunction := ?F;
              Opsem.CurBB := ?B;
              Opsem.CurCmds := nil;
              Opsem.Terminator := _;
              Opsem.Locals := _;
              Opsem.Allocas := _ |}
              ({|
               Opsem.CurFunction := _;
               Opsem.CurBB := _;
               Opsem.CurCmds := ?c' :: _;
               Opsem.Terminator := _;
               Opsem.Locals := _;
               Opsem.Allocas := _ |}  :: _) |- _ =>
  let cs3 := fresh "cs3" in
  destruct Heq3 as [l3 [ps3 [cs3 Heq3]]]; subst;
  assert (HBinF1':=HBinF1);
  apply HwfCall in HBinF1';
  destruct_cmd c'; tinv HBinF1'; clear HBinF1'
end.

Ltac simpl_s_genInitState :=
  match goal with
  | Hinit: Opsem.s_genInitState _ _ _ _ = _ |- _ =>
    unfold Opsem.s_genInitState in Hinit;
    inv_mbind'
  end;
  match goal with
  | m : module |- _ =>
    destruct m as [CurLayouts CurNamedts CurProducts];
    inv_mbind'
  end;
  match goal with
  | H: ret (_, ?s0) = getEntryBlock ?f |- _ =>
    destruct s0 as [ps0 cs0 tmn0];
    destruct f as [[f t i0 a v] b];
    inv_mbind'
  end;
  try repeat match goal with
  | H: ret _ = ret _ |- _ => inv H
  end;
  symmetry_ctx.

Ltac uniq_result :=
repeat dgvs_instantiate_inv;
repeat match goal with
| H1 : ?f ?a ?b ?c ?d = _,
  H2 : ?f ?a ?b ?c ?d = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a ?b ?c = _,
  H2 : ?f ?a ?b ?c = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a ?b = _,
  H2 : ?f ?a ?b = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a = _,
  H2 : ?f ?a = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : _ @ _ |- _ => inv H1
| H : ?f _ = ?f _ |- _ => inv H
| H : ?f _ _ = ?f _ _ |- _ => inv H
| H : ?f _ _ _ = ?f _ _ _ |- _ => inv H
| H : ?f _ _ _ _ = ?f _ _ _ _ |- _ => inv H
| H : ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ => inv H
| H : False |- _ => inv H
| H: moduleEqB _ _ = true |- _ => apply moduleEqB_inv in H; inv H
| H: valueEqB _ _ = true |- _ => apply valueEqB_inv in H; inv H
| H: true = valueEqB _ _ |- _ => 
     symmetry in H; apply valueEqB_inv in H; inv H
| H: phinodeEqB _ _ = true |- _ => apply phinodeEqB_inv in H; inv H
| H: _ =cmd= _ = true |- _ => apply cmdEqB_inv in H; inv H
| H: _ =tmn= _ = true |- _ => apply terminatorEqB_inv in H; inv H
| H: _ =b= _ = true |- _ => apply blockEqB_inv in H; inv H
| H: left ?e = false |- _ => inv H
end.

Ltac unfold_blk2GV := unfold blk2GV, ptr2GV, val2GV.

Ltac anti_simpl_env :=
simpl_env in *;
repeat match goal with
| H: ?A ++ _ = ?A ++ _ |- _ => apply app_inv_head in H
| H: ?A ++ ?B ++ ?C = _ |- _ => rewrite_env ((A++B)++C) in H
| H: ?A ++ ?B ++ ?C ++ ?D = _ |- _ => rewrite_env (((A++B)++C)++D) in H
| H: ?A ++ ?B ++ ?C ++ ?D ++ ?E = _ |- _ =>rewrite_env ((((A++B)++C)++D)++E) in H
| H: _ = ?A ++ ?B ++ ?C |- _ => rewrite_env ((A++B)++C) in H
| H: _ = ?A ++ ?B ++ ?C ++ ?D |- _ => rewrite_env (((A++B)++C)++D) in H
| H: _ = ?A ++ ?B ++ ?C ++ ?D ++ ?E |- _ =>rewrite_env ((((A++B)++C)++D)++E) in H
end;
repeat match goal with
| H: _ ++ ?A = _ ++ ?A |- _ => apply app_inv_tail in H
| H: _ ++ [?a] = _ ++ [?b] |- _ => apply app_inj_tail in H; destruct H; subst
| H: ?A = _ ++ ?A |- _ => symmetry in H; apply app_inv_tail_nil in H
| H: _ ++ ?A = ?A |- _ => apply app_inv_tail_nil in H
| H: (_++[_])++_ = nil |- _ => 
    contradict H; simpl_env; simpl; apply app_cons_not_nil
| H: _++[_]++_ = nil |- _ => contradict H; simpl; apply app_cons_not_nil
| H: ?A++[?a] = nil |- _ => 
       rewrite_env (A++[a]++nil) in H;
       contradict H; simpl; apply app_cons_not_nil
end.

(* go to *)
Lemma getTypeSizeInBits_and_Alignment__getTypeStoreSize: forall TD t sz al,
  getTypeSizeInBits_and_Alignment TD true t = Some (sz, al) ->
  getTypeStoreSize TD t = Some (nat_of_Z (ZRdiv (Z_of_nat sz) 8)).
Proof.
  unfold getTypeStoreSize, getTypeSizeInBits.
  intros. fill_ctxhole. auto.
Qed.

(* go to *)
Ltac inTmnOp_isnt_stuck v H3 Hwfcfg1 Hwfpp1 :=
match type of Hwfpp1 with
| OpsemPP.wf_State 
              {|
              OpsemAux.CurSystem := _;
              OpsemAux.CurTargetData := ?td;
              OpsemAux.CurProducts := _;
              OpsemAux.Globals := ?gl;
              OpsemAux.FunTable := _ |}
    {| Opsem.ECS := {| Opsem.CurFunction := _;
                       Opsem.CurBB := ?b;
                       Opsem.CurCmds := nil;
                       Opsem.Terminator := ?tmn;
                       Opsem.Locals := ?lc;
                       Opsem.Allocas := _
                     |} :: _;
       Opsem.Mem := _ |}  =>
    let G := fresh "G" in
    let gvs := fresh "gvs" in
    assert (exists gvs, Opsem.getOperandValue td v lc gl = Some gvs) as G; 
      try solve [
        destruct H3 as [l5 [ps2 [cs21 H3]]]; subst;
        destruct Hwfcfg1 as [_ [Hwfg1 [Hwfs1 HmInS1]]];
        destruct Hwfpp1 as 
          [_ [[Hreach1 [HbInF1 [HfInPs1 [_ [Hinscope1 _]]]]] _]];
        inv_mbind;
        eapply OpsemPP.getOperandValue_inTmnOperans_isnt_stuck; eauto 1;
          simpl; auto
      ];
    destruct G as [gvs G]
end.

(* go to *)
Ltac destruct_dec :=
match goal with
| |- context [id_dec ?b ?a] =>
  destruct (id_dec b a); subst; try congruence; auto
| H2: context [id_dec ?b ?a] |- _ =>
  destruct (id_dec b a); subst; try solve [auto | congruence | inv H2]
| _ : context [productInModuleB_dec ?p1 ?p2] |- _ =>
  destruct (productInModuleB_dec p1 p2); try congruence
end.

Ltac solve_in_list' :=
match goal with
| Heq : nil = _ ++ _ :: _ |- _ =>
    symmetry in Heq; contradict Heq; apply app_cons_not_nil; auto
| Heq : _ ++ _ :: _ = nil |- _ =>
    contradict Heq; apply app_cons_not_nil; auto
| _ => solve_in_list
end.

(* copied from SB *)
Lemma cmds_at_block_tail_next : forall B c cs tmn2,
  (exists l1:l, exists ps1, exists cs11, B =
    (l1, stmts_intro ps1 (cs11 ++ c :: cs) tmn2)) ->
  exists l1, exists ps1, exists cs11, B = (l1, stmts_intro ps1 (cs11 ++ cs) tmn2).
Proof.
  intros.
  destruct H as [l1 [ps1 [cs11 H]]]; subst.
  exists l1. exists ps1. exists (cs11 ++ [c]). simpl_env. auto.
Qed.

Ltac repeat_solve :=
  repeat (split; eauto 2 using cmds_at_block_tail_next).


