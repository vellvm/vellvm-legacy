Require Import vellvm.

Ltac wfCall_inv :=
match goal with
| Heq3 : exists _,
           exists _,
             exists _,
               ?B = block_intro _ _ _ _,
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
  | H: ret ?m = getParentOfFdefFromSystem _ _ |- _ =>
    destruct m as [CurLayouts CurNamedts CurProducts];
    inv_mbind'
  end;
  match goal with
  | H: ret ?b = getEntryBlock ?f |- _ =>
    destruct b as [l0 ps0 cs0 tmn0];
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
| H : False |- _ => inv H
end.

Ltac unfold_blk2GV := unfold blk2GV, ptr2GV, val2GV.

Ltac get_wf_value_for_simop :=
  match goal with
  | HBinF: blockInFdefB (block_intro _ _ (_++_::_) _) _ = _ |- _ =>
    let HBinF':=fresh "HBinF'" in
    assert (HBinF':=HBinF);
    eapply wf_system__wf_cmd in HBinF'; eauto using in_middle;
    inv HBinF'; 
    match goal with
    | H: wf_trunc _ _ _ _ _ |- _ => inv H
    | H: wf_cast _ _ _ _ _ |- _ => inv H 
    | H: wf_ext _ _ _ _ _ |- _ => inv H 
    | _ => idtac
    end
  end.

Ltac get_wf_value_for_simop' :=
  match goal with
  | HBinF: blockInFdefB (block_intro _ _ (_++nil) _) _ = _ |- _ =>
    let HBinF':=fresh "HBinF'" in
    assert (HBinF':=HBinF);
    eapply wf_system__wf_tmn in HBinF'; eauto using in_middle;
    inv HBinF'
  end.

