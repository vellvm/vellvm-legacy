Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vellvm.
Require Import opsem_props.

(* opsem should use this definition *)
Definition s_isFinialState (cfg:OpsemAux.Config) (state:@Opsem.State DGVs) 
  : option GenericValue :=
match state with
| (Opsem.mkState ((Opsem.mkEC _ _ nil (insn_return_void _) _ _)::nil) _ ) => 
    const2GV (OpsemAux.CurTargetData cfg) (OpsemAux.Globals cfg) 
      (const_int Size.One (INTEGER.of_Z 1%Z 1%Z false))
| (Opsem.mkState ((Opsem.mkEC _ _ nil (insn_return _ _ v) lc _)::nil) _ ) => 
    Opsem.getOperandValue (OpsemAux.CurTargetData cfg) v lc 
      (OpsemAux.Globals cfg)
| _ => None
end.

(* opsem should use this definition *)
Inductive s_converges : 
  system -> id -> list (GVsT DGVs) -> trace -> GenericValue -> Prop :=
| s_converges_intro : forall (s:system) (main:id) (VarArgs:list (GVsT DGVs))    
                              cfg (IS FS:Opsem.State) r tr,
  Opsem.s_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  Opsem.sop_star cfg IS FS tr ->
  s_isFinialState cfg FS = Some r ->
  s_converges s main VarArgs tr r
.

Definition stuck_state (cfg:OpsemAux.Config) (st:@Opsem.State DGVs) : Prop :=
~ exists st', exists tr, Opsem.sInsn cfg st st' tr.

(* opsem should use this definition *)
Inductive s_goeswrong : 
  system -> id -> list (GVsT DGVs) -> trace -> @Opsem.State DGVs  -> Prop :=
| s_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list (GVsT DGVs)) 
                              cfg (IS FS:Opsem.State) tr,
  Opsem.s_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  Opsem.sop_star cfg IS FS tr ->
  stuck_state cfg FS ->
  ~ Opsem.s_isFinialState FS ->
  s_goeswrong s main VarArgs tr FS
.

Inductive program_sim (P1 P2:system) (main:id) (VarArgs:list (GVsT DGVs)) :
   Prop :=
| program_sim_intro: 
    (forall tr r, 
      s_converges P1 main VarArgs tr r -> 
      s_converges P2 main VarArgs tr r) -> 
    (forall Tr, 
      Opsem.s_diverges P1 main VarArgs Tr -> 
      Opsem.s_diverges P2 main VarArgs Tr) ->
    program_sim P1 P2 main VarArgs
.

Lemma program_sim_refl: forall P main VarArgs, program_sim P P main VarArgs.
Admitted.

Lemma program_sim_trans: forall P1 P2 P3 main VarArgs, 
  program_sim P1 P2 main VarArgs -> program_sim P2 P3 main VarArgs -> 
  program_sim P1 P3 main VarArgs.
Admitted.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
