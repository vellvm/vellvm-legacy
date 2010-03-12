Require Import ssa_def.

(*BEGINCOPY*)

Require Import List.
Require Import Bool.

Section SSALists.

  Variable A : Type.

  Fixpoint last_opt (l:list A) {struct l} : option A := 
  match l with 
    | nil => None 
    | a :: nil => Some a 
    | a :: l => last_opt l
  end.

End SSALists. 

Section Dominator.

  Parameter genDominatorTree : fdef -> dt.

  Parameter blockDominates : dt -> block -> block -> Prop.
  Parameter insnDominates : dt -> insn -> insn -> Prop.

End Dominator.

Section UseDef.

  Definition insnUseDef := insn -> option (insn * block * fdef * module) % type.
  Definition blockUseDef := block -> option (insn * block * fdef * module) % type.
  
  Definition genInsnUse := module -> insnUseDef.
  Definition genBlockUse := module -> blockUseDef.

End UseDef.

(*ENDCOPY*)

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./ott") ***
*** End: ***
 *)
