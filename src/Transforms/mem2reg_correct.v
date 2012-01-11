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
Require Import palloca_props.
Require Import mem2reg.
Require Import memory_props.

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

(* We are proving the macro-based m2r pass *)
Axiom does_macro_m2r_is_true: mem2reg.does_macro_m2r tt = true.

Lemma macro_m2r_sim_aux: forall (main : id) (VarArgs : list (GVsT DGVs))        
  (los : layouts) (nts : namedts) (Ps2 Ps1: products),
  program_sim
    [module_intro los nts
      (Ps1 ++ List.map
        (fun p : product =>
          match p with
          | product_gvar _ => p
          | product_fdec _ => p
          | product_fdef f => product_fdef (mem2reg_fdef f)
          end) Ps2)] [module_intro los nts (Ps1++Ps2)] main VarArgs.
Proof.
  induction Ps2; simpl; intros.
    admit. (* refl *)

    assert (J:=@IHPs2 (Ps1 ++ [a])). clear IHPs2.
    simpl_env in J. simpl in J. 
    destruct a; auto.



  rewrite_env (nil ++ Ps) at 2.
  rewrite_env (nil ++ List.map
                (fun p : product =>
                 match p with
                 | product_gvar _ => p
                 | product_fdec _ => p
                 | product_fdef f => product_fdef (mem2reg_fdef f)
                 end)).

macro_m2r_sim_aux


  destruct m as [los nts Ps].
  intros.
  constructor.
    intros tr r Hconv.
    inv Hconv.
    unfold Opsem.s_genInitState in H.
    inv_mbind'.
    remember (productInModuleB_dec (product_fdef f)
                (module_intro los nts
                   (List.map
                      (fun p : product =>
                       match p with
                       | product_gvar _ => p
                       | product_fdec _ => p
                       | product_fdef f => product_fdef (mem2reg_fdef f)
                       end) Ps))) as R.
    destruct R; inv HeqR0.
    remember (OpsemAux.genGlobalAndInitMem
           (OpsemAux.initTargetData los nts Mem.empty)
           (List.map
              (fun p : product =>
               match p with
               | product_gvar _ => p
               | product_fdec _ => p
               | product_fdef f => product_fdef (mem2reg_fdef f)
               end) Ps) nil nil Mem.empty) as R.
    destruct R as [[[initGlobal initFunTable] initMem]|]; inv H2.
    inv_mbind'.
    destruct b.
    destruct f as [[]].
    inv_mbind'. symmetry_ctx.

    constructor.
Qed.

Lemma macro_m2r_sim: forall (m:module) (main:id) (VarArgs:list (GVsT DGVs)),
  program_sim [mem2reg.run m] [m] main VarArgs.
Proof.
  destruct m as [los nts Ps].
  unfold mem2reg.run.
  intros.
  assert (J:=@macro_m2r_sim_aux main VarArgs los nts Ps nil).
  auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
