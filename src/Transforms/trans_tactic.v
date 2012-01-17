Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
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
  destruct c'; tinv HBinF1'; clear HBinF1'
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
  | H: ret ?p = OpsemAux.genGlobalAndInitMem _ _ _ _ _ |- _ =>
    destruct p as [[initGlobal initFunTable] initMem];
    inv_mbind'
  end;
  match goal with
  | H: ret ?b = getEntryBlock ?f |- _ =>
    destruct b as [l0 ps0 cs0 tmn0];
    destruct f as [[]];
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

Ltac destruct_exists :=
repeat match goal with
| H : exists _, _ |- _ => 
    let A := fresh "A" in
    let J := fresh "J" in
    destruct H as [A J]
end.

Ltac destruct_ands :=
repeat match goal with
| H : _ /\ _ |- _ => destruct H
end.

Ltac zeauto := eauto with zarith.

Ltac inv_mbind'' :=
  repeat match goal with
         | H : match ?e with
               | Some _ => _
               | None => None
               end = Some _ |- _ => remember e as R; destruct R as [|]; inv H
         | H : Some _ = match ?e with
               | Some _ => _
               | None => None
               end |- _ => remember e as R; destruct R as [|]; inv H
         | H :  ret _ = match ?p with
                        | (_, _) => _
                        end |- _ => destruct p
         | H : if ?e then _ else False |- _ => 
             remember e as R; destruct R; tinv H
         | H : if ?e then False else _ |- _ => 
             remember e as R; destruct R; tinv H
         end.

Ltac inv_mbind' :=
  repeat match goal with
         | H : match ?e with
               | Some _ => _
               | None => None
               end = Some _ |- _ => remember e as R; destruct R as [|]; inv H
         | H : Some _ = match ?e with
               | Some _ => _
               | None => None
               end |- _ => remember e as R; destruct R as [|]; inv H
         | H :  ret _ = match ?p with
                        | (_, _) => _
                        end |- _ => destruct p
         end.

Ltac solve_in_prefix :=
repeat match goal with
| G: In ?i (?prefix ++ _) |- In ?i (?prefix ++ _) =>
  apply in_or_app;
  apply in_app_or in G;
  destruct G as [G | G]; auto;
  right
end.

Ltac solve_in_head := 
match goal with
| H0 : In _ ([_] ++ _),
  J2 : _ \/ _ \/ _ |- _ =>
    simpl in H0;
    destruct H0 as [H0 | H0]; subst; try solve [
      destruct J2 as [J2 | [J2 | J2]]; subst;
        repeat match goal with
        | H : _ /\ _ |- _ => destruct H
        end; congruence]
| H0 : In _ (_:: _),
  J2 : _ \/ _ \/ _ |- _ =>
    simpl in H0;
    destruct H0 as [H0 | H0]; subst; try solve [
      destruct J2 as [J2 | [J2 | J2]]; subst;
        repeat match goal with
        | H : _ /\ _ |- _ => destruct H
        end; congruence]
| H0 : _ = _ \/ In _ _,
  J2 : _ \/ _ \/ _ |- _ =>
    simpl in H0;
    destruct H0 as [H0 | H0]; subst; try solve [
      destruct J2 as [J2 | [J2 | J2]]; subst;
        repeat match goal with
        | H : _ /\ _ |- _ => destruct H
        end; congruence]
end.

Ltac zauto := auto with zarith.

Ltac inv_mbind :=
  repeat match goal with
         | H : match ?e with
               | Some _ => _
               | None => None
               end = Some _ |- _ => remember e as R; destruct R as [|]; inv H
         end.

Ltac unfold_blk2GV := unfold blk2GV, ptr2GV, val2GV.

Ltac SSSSSCase name := Case_aux subsubsubsubsubcase name.
Ltac SSSSSSCase name := Case_aux subsubsubsubsubsubcase name.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
