Require Export alist.
Require Export Integers.
Require Export Values.
Require Export Coqlib.
Require Export monad.
Require Export events.
Require Export Memory.
Require Export Metatheory.
Require Export Znumtheory.
Require Export datatype_base.
Require Import syntax.
Require Import infrastructure.
Require Export dom_list.
Require Export analysis.
Require Import typings.
Require Import genericvalues.
Require Import targetdata.
Require Export infrastructure_props.
Require Export static.
Require Export opsem.
Require Export opsem_wf.
Require Export dopsem.
Require Export ndopsem.
Require Export external_intrinsics.
Require Export vellvm_tactics.

Export LLVMsyntax.
Export LLVMinfra.
Export LLVMgv.
Export LLVMtd.
Export LLVMtypings.

Ltac destruct_cmd cmd :=
let i0 := fresh "i0" in
let i1 := fresh "i1" in
let b := fresh "b" in
let s0 := fresh "s0" in
let v := fresh "v" in
let v0 := fresh "v0" in
let v1 := fresh "v1" in
let f0 := fresh "f0" in
let f1 := fresh "f1" in
let t := fresh "t" in
let t0 := fresh "t0" in
let t1 := fresh "t1" in
let l2 := fresh "l2" in
let a := fresh "a" in
let p := fresh "p" in
let n := fresh "n" in
let c := fresh "c" in
let e := fresh "e" in
destruct cmd as [i0 b s0 v v0|i0 f0 f1 v v0|i0 t v l2 t0|i0 t v t0 v0 l2|
                 i0 t v a|i0 t v|i0 t v a|i0 t v a|i0 t v v0 a|i0 i1 t v l2 t0|
                 i0 t t0 v t1|i0 e t v t0|i0 c t v t0|i0 c t v v0|
                 i0 f0 f1 v v0|i0 v t v0 v1|i0 n c t0 v0 v p].

Ltac destruct_typ t :=
let s0 := fresh "s0" in
let f := fresh "f" in
let t0 := fresh "t0" in
let lt0 := fresh "lt0" in
let i0 := fresh "i0" in
destruct t as [s0 | f | | | | s0 t0 | t0 lt0 | lt0 | t0 | i0 ].

Ltac destruct_const cst :=
let Int5 := fresh "Int5" in
let i0 := fresh "i0" in
let b := fresh "b" in
let sz5 := fresh "sz5" in
let f0 := fresh "f0" in
let f1 := fresh "f1" in
let t := fresh "t" in
let t0 := fresh "t0" in
let l2 := fresh "l2" in
let c0 := fresh "c0" in
let c1 := fresh "c1" in
let c2 := fresh "c2" in
let e := fresh "e" in
let cs0 := fresh "cs0" in
destruct cst as [t|sz5 Int5|f0 f1|t|t|t cs0|t cs0|t i0|t c0 t0|e c0 t0|c0 c1 t0|
                 i0 c0 cs0|c0 c1 c2|c0 c1 c2|f0 c1 c2|c0 cs0|c0 c1 cs0|
                 b c0 c1|f0 c0 c1].

Ltac destruct_tmn tmn :=
let id5 := fresh "id5" in
let t := fresh "t" in
let value5 := fresh "value5" in
let l2 := fresh "l2" in
let l3 := fresh "l3" in
let i0 := fresh "i0" in
destruct tmn as [id5 t value5 | id5 | id5 value5 l2 l3 | i0 l2 | ].

Ltac repeat_bsplit :=
  repeat (bsplit; auto using eq_sumbool2bool_true).

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

Lemma getTypeSizeInBits_and_Alignment__getTypeStoreSize: forall TD t sz al,
  getTypeSizeInBits_and_Alignment TD true t = Some (sz, al) ->
  getTypeStoreSize TD t = Some (nat_of_Z (ZRdiv (Z_of_nat sz) 8)).
Proof.
  unfold getTypeStoreSize, getTypeSizeInBits.
  intros. fill_ctxhole. auto.
Qed.

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

