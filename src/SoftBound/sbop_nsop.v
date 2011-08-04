Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa/compcert".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Export targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import genericvalues.
Require Import trace.
Require Import ssa_props.
Require Import alist.
Require Import ssa_dynamic.
Require Import ndopsem.
Require Import sb_ds_def.
Require Import sb_ns_def.

Export LLVMsyntax.
Export LLVMlib.

Lemma sbds__llvmds : forall sbSt sbSt' tr,
  SBnsop.nsInsn sbSt sbSt' tr ->
  NDopsem.nsInsn 
    (SBnsop.sbState__State sbSt) (SBnsop.sbState__State sbSt') tr.
Proof.
  intros sbSt sbSt' tr HdsInsn.
  inv HdsInsn; auto.
Qed.

Ltac invert_prop_reg_metadata :=
  match goal with
  | [H : SBnsop.prop_reg_metadata _ _ _ _ _ = (_, _) |- _ ] =>
      inversion H; subst; eauto
  end.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)

