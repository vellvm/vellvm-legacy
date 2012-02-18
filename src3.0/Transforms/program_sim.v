Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vellvm.
Require Import opsem_props.
Require Import memory_props.
Require Import trans_tactic.

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

Lemma genGlobalAndInitMem__wf_global: forall initGlobal initFunTable initMem 
  CurLayouts CurNamedts CurProducts S,
  OpsemAux.genGlobalAndInitMem
    (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty) CurProducts 
      nil nil Mem.empty = ret (initGlobal, initFunTable, initMem) ->
  wf_global (CurLayouts, CurNamedts) S initGlobal.
Admitted.

Lemma getParentOfFdefFromSystem__productInModuleInSystemB: 
  forall CurLayouts CurNamedts CurProducts F S,
  getParentOfFdefFromSystem F S = 
    ret (module_intro CurLayouts CurNamedts CurProducts) ->
  moduleInSystemB (module_intro CurLayouts CurNamedts CurProducts) S = true /\
  InProductsB (product_fdef F) CurProducts = true.
Admitted.  
     
Lemma initLocals__wf_defs: forall CurLayouts CurNamedts VarArgs lc f t fid la v
  bs (Hinit : @Opsem.initLocals DGVs
                (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty) la
                VarArgs = ret lc) l0 ps0 cs0 tmn0
  (Hentry : getEntryBlock (fdef_intro (fheader_intro f t fid la v) bs) =
              ret block_intro l0 ps0 cs0 tmn0),
  match cs0 with
  | nil =>
      match
        inscope_of_tmn (fdef_intro (fheader_intro f t fid la v) bs)
          (block_intro l0 ps0 cs0 tmn0) tmn0
      with
      | ret ids0 =>
          OpsemPP.wf_defs (CurLayouts, CurNamedts)
            (fdef_intro (fheader_intro f t fid la v) bs) lc ids0
      | merror => False
      end
  | c :: _ =>
      match
        inscope_of_cmd (fdef_intro (fheader_intro f t fid la v) bs)
          (block_intro l0 ps0 cs0 tmn0) c
      with
      | ret ids0 =>
          OpsemPP.wf_defs (CurLayouts, CurNamedts)
            (fdef_intro (fheader_intro f t fid la v) bs) lc ids0
      | merror => False
      end
  end.
Proof.
(*
     assert (ps'=nil) as EQ.
       eapply entryBlock_has_no_phinodes with (ifs:=nil)(s:=S); eauto.        
     subst.
     apply dom_entrypoint in H2. 
     destruct cs'.
       unfold inscope_of_tmn.
       remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
         !! l') as R.
       destruct R. simpl in H2. subst.
       eapply preservation_dbCall_case; eauto using wf_params_spec.

       unfold inscope_of_cmd, inscope_of_id.
       remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
         !! l') as R.
       destruct R. simpl. simpl in H2. subst.
       destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n]; 
         try solve [contradict n; auto]. 
       eapply preservation_dbCall_case; eauto using wf_params_spec.
*)
Admitted.

(* OpsemPP.initLocals__wf_lc needs wf_params that is for params.
   At initialization, we only have args...
   Actually OpsemPP.initLocals__wf_lc only needs types in params.
   So, we use the function to create a param from arg.
   We should simplify the proofs of OpsemPP.initLocals__wf_lc, and
   use only types. *)
Definition args_to_params (la: args) : params :=
List.map (fun a0 => let '(t0,attr0,id0) := a0 in (t0,attr0,value_id id0)) la.

Axiom main_wf_params: forall f t i0 a v b S CurLayouts CurNamedts CurProducts
  VarArgs,
  getParentOfFdefFromSystem (fdef_intro (fheader_intro f t i0 a v) b) S = 
    ret module_intro CurLayouts CurNamedts CurProducts ->
  @OpsemPP.wf_params DGVs 
    (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty) 
    VarArgs (args_to_params a).

Lemma s_genInitState__opsem_wf: forall S main VarArgs cfg IS
  (HwfS : wf_system nil S)
  (Hinit : @Opsem.s_genInitState DGVs S main VarArgs Mem.empty = ret (cfg, IS)),
  OpsemPP.wf_State cfg IS.
Proof.
  intros.
  simpl_s_genInitState.
  assert (HeqR0':=HeqR0).
  apply getParentOfFdefFromSystem__productInModuleInSystemB in HeqR0'.
  destruct HeqR0' as [HMinS HinPs].
  assert (uniqFdef (fdef_intro (fheader_intro f t i0 a v) b)) as Huniq.
    eapply wf_system__uniqFdef; eauto.
  assert (wf_fdef nil S (module_intro CurLayouts CurNamedts CurProducts) 
      (fdef_intro (fheader_intro f t i0 a v) b)) as HwfF.
    eapply wf_system__wf_fdef; eauto.
Local Opaque inscope_of_tmn inscope_of_cmd.
  simpl.
  split.
    eapply genGlobalAndInitMem__wf_global in HeqR1; eauto.
  split; auto.
  split; auto.
  split.
    intro J. congruence.
  split.
    split.
      eapply reachable_entrypoint; eauto.
    split.
      apply entryBlockInFdef in HeqR2. simpl in HeqR2. auto.
    split; auto.
    split.
      eapply main_wf_params in HeqR0; eauto.
      eapply OpsemPP.initLocals__wf_lc; eauto.
    split.
      eapply initLocals__wf_defs; eauto.
      exists l0. exists ps0. exists nil. auto.
    split; auto.
      intros. destruct b0 as [? ? ? t0]. destruct t0; auto.
Transparent inscope_of_tmn inscope_of_cmd.
Qed.

Axiom genGlobalAndInitMem__wf_globals_Mem: forall initGlobal initFunTable initMem
  CurLayouts CurNamedts CurProducts la lc (VarArgs : list (GVsT DGVs)),
  OpsemAux.genGlobalAndInitMem
    (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty) CurProducts 
      nil nil Mem.empty = ret (initGlobal, initFunTable, initMem) ->
  Opsem.initLocals (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty) la
            VarArgs = ret lc ->
  MemProps.wf_lc initMem lc /\
  exists maxb : Z, MemProps.wf_globals maxb initGlobal /\ 0 <= maxb /\
    MemProps.wf_Mem maxb
      (OpsemAux.initTargetData CurLayouts CurNamedts Mem.empty) initMem.

Lemma s_isFinialState__stuck: forall St1 St2 cfg tr
  (Hfinal : @Opsem.s_isFinialState DGVs St1 = true),
  ~ Opsem.sInsn cfg St1 St2 tr.
Proof.
  intros.
  destruct St1; simpl in Hfinal.
  destruct ECS; tinv Hfinal.
  destruct e; tinv Hfinal.
  destruct CurCmds; tinv Hfinal.
  intro J.
  destruct Terminator; tinv Hfinal; destruct ECS; tinv Hfinal; inv J.
Qed.

Lemma undefined_state__stuck: forall St1 St2 cfg tr
  (Hundef : @OpsemPP.undefined_state DGVs cfg St1),
  ~ Opsem.sInsn cfg St1 St2 tr.
Proof.
  intros.
  unfold OpsemPP.undefined_state in Hundef.
  destruct cfg; simpl in Hundef.
  destruct St1; simpl in Hundef.
  destruct ECS.
  destruct Hundef as [J | [J | [J | [J | [J | [J | [J | J]]]]]]]; inv J.
  destruct e; tinv Hundef.
  intro Hop.
  destruct CurCmds.
    destruct Hundef as 
      [Hundef | [Hundef | [Hundef | [J | [J | [J | [J | J]]]]]]]; 
      try solve [inversion J].
      destruct Terminator; tinv Hundef.
      destruct ECS; tinv Hundef.
      destruct e; tinv Hundef.
      destruct CurCmds; tinv Hundef.
      inv Hop. uniq_result.

      destruct Terminator; tinv Hundef.
      destruct ECS; tinv Hundef.
      destruct e; tinv Hundef.
      destruct CurCmds; tinv Hundef.
      inv Hop. 
      destruct Hundef as [Hundef | Hundef].
        uniq_result.
        
        remember (getCallerReturnID c) as R.
        destruct R; tinv Hundef.
          congruence.

      destruct CurBB as [? ? ? t]; tinv Hundef.
      destruct t; tinv Hundef.
      destruct Terminator; tinv Hundef.
      inv Hop.

    destruct Hundef as 
      [Hundef | [Hundef | [Hundef | [Hundef | 
        [Hundef | [Hundef | [Hundef | Hundef]]]]]]]; 
      tinv Hundef.
      destruct CurBB as [? ? ? t]; tinv Hundef.
      destruct t; tinv Hundef.
      destruct_cmd c; tinv Hundef.
        remember (Opsem.getOperandValue CurTargetData v Locals Globals) as R.
        destruct R; tinv Hundef.
        remember (getTypeAllocSize CurTargetData t) as R.
        destruct R; tinv Hundef.
        destruct Hundef as [gn [Hinst Hundef]].
        remember (malloc CurTargetData Mem s gn a) as R.
        destruct R; tinv Hundef.
        inv Hop. symmetry_ctx. uniq_result. rewrite H21 in HeqR1. congruence.

        remember (Opsem.getOperandValue CurTargetData v Locals Globals) as R.
        destruct R; tinv Hundef.
        remember (getTypeAllocSize CurTargetData t) as R.
        destruct R; tinv Hundef.
        destruct Hundef as [gn [Hinst Hundef]].
        remember (malloc CurTargetData Mem s gn a) as R.
        destruct R; tinv Hundef.
        inv Hop. symmetry_ctx. uniq_result. rewrite H21 in HeqR1. congruence.
        
      destruct_cmd c; tinv Hundef.
        remember (Opsem.getOperandValue CurTargetData v Locals Globals) as R.
        destruct R; tinv Hundef.
        destruct Hundef as [gn [Hinst Hundef]].
        remember (free CurTargetData Mem gn) as R.
        destruct R; tinv Hundef.
        inv Hop. symmetry_ctx. uniq_result. rewrite H19 in HeqR0. congruence.

      destruct_cmd c; tinv Hundef.
        remember (Opsem.getOperandValue CurTargetData v Locals Globals) as R.
        destruct R; tinv Hundef.
        destruct Hundef as [gn [Hinst Hundef]].
        remember (mload CurTargetData Mem gn t a) as R.
        destruct R; tinv Hundef.
        inv Hop. symmetry_ctx. uniq_result. rewrite H20 in HeqR0. congruence.

      destruct_cmd c; tinv Hundef.
        remember (Opsem.getOperandValue CurTargetData v Locals Globals) as R.
        destruct R; tinv Hundef.
        remember (Opsem.getOperandValue CurTargetData v0 Locals Globals) as R.
        destruct R; tinv Hundef.
        destruct Hundef as [gn [mgv [Hinst1 [Hinst2 Hundef]]]].
        remember (mstore CurTargetData Mem mgv t gn a) as R.
        destruct R; tinv Hundef.
        inv Hop. symmetry_ctx. uniq_result. rewrite H23 in HeqR1. congruence.

      destruct_cmd c; tinv Hundef.
        remember (Opsem.getOperandValue CurTargetData v Locals Globals) as R.
        destruct R; tinv Hundef.
        destruct Hundef as [fptr [Hinst Hundef]].
        remember (OpsemAux.lookupFdefViaPtr CurProducts FunTable fptr) as R.
        destruct R; tinv Hundef.
        remember (OpsemAux.lookupExFdecViaPtr CurProducts FunTable fptr) as R.
        destruct R as [f|].
          destruct f as [[fnattrs5 typ5 id5 args5 varg5] bs].
          remember (Opsem.params2GVs CurTargetData p Locals Globals) as R.
          destruct R; tinv Hundef.
          destruct Hundef as [gvs [Hinst' Hundef]].
          remember (OpsemAux.callExternalFunction Mem id5 gvs) as R.
          destruct R as [[]|].
            remember (Opsem.exCallUpdateLocals CurTargetData t n i0 o Locals) 
              as R.
            destruct R; tinv Hundef.
            inv Hop. 
              symmetry_ctx. uniq_result. rewrite H22 in HeqR0. congruence.
              symmetry_ctx. uniq_result. rewrite H26 in HeqR4. congruence.

            inv Hop. 
              symmetry_ctx. uniq_result. rewrite H22 in HeqR0. congruence.
              symmetry_ctx. uniq_result. rewrite H25 in HeqR3. congruence.

          inv Hop. 
            symmetry_ctx. uniq_result. rewrite H22 in HeqR0. congruence.
            symmetry_ctx. uniq_result. rewrite H22 in HeqR1. congruence.
Qed.

Lemma wf_system__uniqSystem: forall ifs S, wf_system ifs S -> uniqSystem S.
Proof.
  intros. 
  destruct H; auto.
Qed.

Lemma uniq_products_simulation: forall Ps1 f Ps2 f0 trans,
  NoDup (getProductsIDs (Ps1 ++ product_fdef f :: Ps2)) ->
  f0 = f ->
  Forall2
    (fun P1 P2 : product =>
     match P1 with
     | product_fdef f1 =>
         match P2 with
         | product_fdef f2 => 
             if fdef_dec f0 f1
             then trans f1 = f2
             else f1 = f2
         | _ => P1 = P2
         end
     | _ => P1 = P2
     end)
    (Ps1 ++ product_fdef f :: Ps2)
    (Ps1 ++ product_fdef (trans f) :: Ps2).
Admitted.

Require Import mem2reg.

Lemma elim_stld_cmds_unchanged: forall f' dones' f cs0 pid dones,
  (f', false, dones') = elim_stld_cmds f cs0 pid dones ->
  f' = f.
Proof.
  intros.
  unfold elim_stld_cmds in H.
  destruct (find_init_stld cs0 pid dones) as [[[[]]|[]]|].
    destruct (find_next_stld c pid) as [[|[]]|]; inv H.
    destruct (find_next_stld c pid) as [[|[]]|]; inv H.
    inv H; auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
