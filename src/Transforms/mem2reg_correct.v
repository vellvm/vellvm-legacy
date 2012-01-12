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
Require Import opsem_props.
Require Import program_sim.
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
Parameter does_macro_m2r_is_true: mem2reg.does_macro_m2r tt = true.

Lemma program_sim_refl: forall P main VarArgs, program_sim P P main VarArgs.
Admitted.

Lemma program_sim_trans: forall P1 P2 P3 main VarArgs, 
  program_sim P1 P2 main VarArgs -> program_sim P2 P3 main VarArgs -> 
  program_sim P1 P3 main VarArgs.
Admitted.

Parameter print_reachablity_is_true: forall rd, print_reachablity rd = true.

Parameter does_phi_elim_is_true: does_phi_elim tt = true.

Parameter does_stld_elim_is_true: does_stld_elim tt = true.

Lemma phinodes_placement_sim: forall rd f Ps1 Ps2 los nts main VarArgs pid ty al
  l0 ps0 cs0 tmn0 dones (Hreach: ret rd = dtree.reachablity_analysis f)
  (Hentry: getEntryBlock f = Some (block_intro l0 ps0 cs0 tmn0))
  (Hfind: find_promotable_alloca f cs0 dones = Some (pid, ty, al)),
  program_sim
    [module_intro los nts 
      (Ps1 ++ 
       product_fdef (phinodes_placement f rd pid ty al (successors f)
                    (make_predecessors (successors f))) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Admitted.

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

Lemma remove_fdef_sim: forall f pid los nts Ps1 Ps2 main VarArgs,
  used_in_fdef pid f = false ->
  program_sim
    [module_intro los nts 
      (Ps1 ++  product_fdef (remove_fdef pid f) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Admitted.

Lemma las_sim: forall (los : layouts) (nts : namedts) (fh : fheader) 
  (dones : list id) (pid : id) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) 
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 pid dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs pid),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (subst_fdef i1 v
           (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) :: Ps2)]
    [module_intro los nts
       (Ps1 ++
        product_fdef
          (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
    main VarArgs.
Proof.

Admitted.

Lemma las_die_sim: forall (los : layouts) (nts : namedts) (fh : fheader) 
  (dones : list id) (pid : id) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) 
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 pid dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs pid),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
           (List.map (remove_block i1)
             (List.map (subst_block i1 v)
               (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))) :: Ps2)]
    [module_intro los nts
       (Ps1 ++
        product_fdef
          (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
    main VarArgs.
Proof.
  intros.
  assert ((fdef_intro fh
           (List.map (remove_block i1)
             (List.map (subst_block i1 v)
               (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))) =
          remove_fdef i1 
            (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))) 
    as J.
    simpl. auto.
  rewrite J.
  apply program_sim_trans with (P2:=
    [module_intro los nts
        (Ps1 ++
         product_fdef
           (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) :: 
         Ps2)]).
    apply remove_fdef_sim.
      admit. (* subst i --> dead i *)  

      eapply las_sim; eauto.
Qed.

Lemma laa_sim: forall (los : layouts) (nts : namedts) (fh : fheader) 
  (dones : list id) (pid : id) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (v : value)
  (cs : cmds) 
  (Hst : ret inr (v, cs) = find_init_stld cs0 pid dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs pid),
  program_sim
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))
         :: Ps2)]
     [module_intro los nts
        (Ps1 ++
         product_fdef
           (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
     main VarArgs.
Admitted.

Lemma laa_die_sim: forall (los : layouts) (nts : namedts) (fh : fheader) 
  (dones : list id) (pid : id) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (v : value)
  (cs : cmds) 
  (Hst : ret inr (v, cs) = find_init_stld cs0 pid dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs pid),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
            (List.map (remove_block i1)
               (List.map (subst_block i1 v)
                  (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))) :: Ps2)]
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
    main VarArgs.
Proof.
  intros.
  assert ((fdef_intro fh
           (List.map (remove_block i1)
             (List.map (subst_block i1 v)
               (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))) =
          remove_fdef i1 
            (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)))) 
    as J.
    simpl. auto.
  rewrite J.
  apply program_sim_trans with (P2:=
    [module_intro los nts
        (Ps1 ++
         product_fdef
           (subst_fdef i1 v
              (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) :: 
         Ps2)]).
    apply remove_fdef_sim.
      admit. (* subst i --> dead i *)  

      eapply laa_sim; eauto.
Qed.

Lemma sas_sim: forall (los : layouts) (nts : namedts) (fh : fheader) 
  (dones : list id) (pid : id) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) 
  (Hst1 : ret inl (i0, v, cs) = find_init_stld cs0 pid dones)
  (i1 : id) (v0 : value)
  (Hst2 : ret inr (i1, v0) = find_next_stld cs pid),
  program_sim
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh
           (List.map (remove_block i0)
             (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))) :: Ps2)]
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
    main VarArgs.
Admitted.

Lemma elim_stld_cmds_sim: forall los nts fh dones pid f0 dones0 main VarArgs
  bs1 l0 ps0 cs0 tmn0 bs2 Ps1 Ps2
  (Hpass : (f0, true, dones0) =
             elim_stld_cmds
               (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) cs0
               pid dones),
  program_sim 
    [module_intro los nts (Ps1 ++ product_fdef f0 :: Ps2)]
    [module_intro los nts
      (Ps1 ++
       product_fdef
         (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) :: Ps2)]
    main VarArgs.
Proof.
  intros.
  unfold elim_stld_cmds in Hpass.
  remember (find_init_stld cs0 pid dones) as R1.
  destruct R1 as [[[[]]|[]]|]; tinv Hpass.
    remember (find_next_stld c pid) as R2.
    destruct R2 as [[|[]]|]; inv Hpass.
      eapply las_die_sim; eauto.
      eapply sas_sim; eauto.
      apply program_sim_refl.

    remember (find_next_stld c pid) as R2.
    destruct R2 as [[|[]]|]; inv Hpass.
      eapply laa_die_sim; eauto.
      apply program_sim_refl.
      apply program_sim_refl.
Qed.

Lemma elim_stld_blocks_sim_aux: forall los nts fh dones pid f0 dones0 main 
  VarArgs Ps1 Ps2 flag bs2 bs1 
  (Hpass:elim_stld_blocks (fdef_intro fh (bs1++bs2)) bs2 pid dones = 
    (f0, flag, dones0)),
  program_sim
    [module_intro los nts                                                      
      (Ps1 ++ 
       product_fdef f0 :: Ps2)]
    [module_intro los nts 
      (Ps1 ++ product_fdef (fdef_intro fh (bs1++bs2)) :: Ps2)]
    main VarArgs.
Proof.
  induction bs2; simpl; intros.
    inv Hpass; auto using program_sim_refl.

    destruct a as [l0 ps0 cs0 tmn0].
    remember 
      (elim_stld_cmds 
        (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) cs0 pid dones) 
      as R.
    destruct R as [[f' []] dones']; inv Hpass; auto.
      eapply elim_stld_cmds_sim; eauto.

      apply elim_stld_cmds_unchanged in HeqR. subst. 
      rewrite_env ((bs1 ++ [block_intro l0 ps0 cs0 tmn0]) ++ bs2) in H0.
      apply IHbs2 in H0. simpl_env in H0. auto.
Qed.

Lemma elim_stld_blocks_sim: forall los nts fh dones pid f0 dones0 main 
  VarArgs Ps1 Ps2 flag bs 
  (Hpass:elim_stld_blocks (fdef_intro fh bs) bs pid dones = (f0, flag, dones0)),
  program_sim
    [module_intro los nts                                                      
      (Ps1 ++ 
       product_fdef f0 :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef (fdef_intro fh bs) :: Ps2)]
    main VarArgs.
Proof.
  intros.
  rewrite_env (nil ++ bs).
  eapply elim_stld_blocks_sim_aux; eauto.
Qed.

Lemma elim_stld_sim: forall f1 dones1 f2 dones2 Ps1 Ps2 los nts main VarArgs pid
  (Hpass: SafePrimIter.iterate _ (elim_stld_step pid) (f1, dones1) = 
    (f2, dones2)),
  program_sim
    [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]
    main VarArgs.
Proof.
  intros.
  set (P:=fun (re:(fdef * list id)) =>
          let '(f, _) := re in
          program_sim [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
           [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)] main VarArgs
      ).
  assert (P (f1, dones1)) as HPf1.
    unfold P. apply program_sim_refl.
  apply SafePrimIter.iterate_prop with (P:=P) in Hpass; auto.
    unfold elim_stld_step.
    intros a HPa.
    destruct a as [f dones].
    unfold elim_stld_fdef.
    destruct f as [fh bs].
    remember (elim_stld_blocks (fdef_intro fh bs) bs pid dones) as R.
    destruct R as [[f0 flag0] dones0]; auto.
    assert (P (f0, dones0)) as HPf0.
      unfold P.
      apply program_sim_trans with (P2:=
           [module_intro los nts 
             (Ps1 ++ product_fdef (fdef_intro fh bs) :: Ps2)]); auto.
      eapply elim_stld_blocks_sim; eauto.
    destruct flag0; auto.
Qed.

Lemma elim_dead_st_fdef_sim: forall f pid Ps1 Ps2 los nts main VarArgs,
  load_in_fdef pid f = false ->
  program_sim
    [module_intro los nts 
      (Ps1 ++  product_fdef (elim_dead_st_fdef f pid) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Admitted.  

Lemma macro_mem2reg_fdef_sim: forall rd f1 dones1 f2 dones2 Ps1 Ps2 los nts main
  VarArgs (Hreach: ret rd = dtree.reachablity_analysis f1)
  (Hiter: SafePrimIter.iterate (fdef * list id)
            (macro_mem2reg_fdef_step rd (successors f1)
              (make_predecessors (successors f1))) 
            (f1, dones1) = (f2, dones2)),
  program_sim
    [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]
    main VarArgs.
Proof.
  intros.
  set (P:=fun (re:(fdef * list id)) =>
          let '(f, _) := re in
          program_sim [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
           [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)] main VarArgs
      ).
  assert (P (f1, dones1)) as HPf1.
    unfold P. apply program_sim_refl.
  apply SafePrimIter.iterate_prop with (P:=P) in Hiter; auto.
    unfold macro_mem2reg_fdef_step.
    intros a HPa.
    destruct a as [f dones].
    unfold macro_mem2reg_fdef_iter.
    remember (getEntryBlock f) as R.
    destruct R as [[l0 ps0 cs0 tmn0]|]; auto.
    remember (find_promotable_alloca f cs0 dones) as R.
    destruct R as [[[pid ty] al]|]; auto.
    rewrite does_stld_elim_is_true.
      remember (SafePrimIter.iterate (fdef * list id) 
                 (elim_stld_step pid)
                 (phinodes_placement f rd pid ty al (successors f1)
                 (make_predecessors (successors f1)), nil)) as R.
      destruct R as [f0 dones0].
      assert (P (f0, dones0)) as Pf0.
        symmetry in HeqR1.
        unfold P.
        apply program_sim_trans with (P2:=
          [module_intro los nts (Ps1 ++ 
            product_fdef 
               (phinodes_placement f rd pid ty al (successors f1)
                 (make_predecessors (successors f1))) :: Ps2)]).
          eapply elim_stld_sim; eauto.
          apply program_sim_trans with (P2:=
            [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]); auto.
            assert (successors f1 = successors f) as EQ1. admit. rewrite EQ1.
            assert (dtree.reachablity_analysis f1 = 
                      dtree.reachablity_analysis f) as EQ2.
              admit. 
            rewrite EQ2 in Hreach.
            eapply phinodes_placement_sim; eauto.
       assert (P 
                (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef f0 pid,
                 nil)) as Pf.
         remember (load_in_fdef pid f0) as R.
         destruct R; auto.
         unfold P.
         apply program_sim_trans with (P2:=
           [module_intro los nts (Ps1 ++ product_fdef f0 :: Ps2)]); auto.
         apply elim_dead_st_fdef_sim; auto.
       remember (used_in_fdef pid
           (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef f0 pid)) as R.
       destruct R; auto.
       apply program_sim_trans with (P2:=
         [module_intro los nts 
           (Ps1 ++ product_fdef 
                     (if load_in_fdef pid f0 then f0 
                      else elim_dead_st_fdef f0 pid) :: Ps2)]); auto.
       apply remove_fdef_sim; auto.
Qed.

Lemma eliminate_phis_sim: forall f Ps1 Ps2 los nts main VarArgs,
  program_sim
    [module_intro los nts 
      (Ps1 ++ product_fdef (SafePrimIter.iterate fdef eliminate_step f) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Admitted.

Axiom fix_temporary_fdef_sim: forall f1 f2 Ps1 Ps2 los nts main VarArgs
  (Hpass: ret f2 = fix_temporary_fdef f1),
  program_sim
    [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]
    main VarArgs.

Lemma mem2reg_fdef_sim: forall (main : id) (VarArgs : list (GVsT DGVs))
  (los : layouts) (nts : namedts) (f : fdef) (Ps2 Ps1 : products),
  program_sim
    [module_intro los nts (Ps1 ++ product_fdef (mem2reg_fdef f) :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
    main VarArgs.
Proof.
  intros.
  unfold mem2reg_fdef.
  remember (getEntryBlock f) as b. 
  destruct b as [[root ps ts tmn]|]; auto using program_sim_refl.
  remember (dtree.reachablity_analysis f) as R.
  destruct R as [rd|]; auto using program_sim_refl.
  rewrite print_reachablity_is_true.
  rewrite does_macro_m2r_is_true.
  remember (SafePrimIter.iterate (fdef * list id)
                   (macro_mem2reg_fdef_step rd (successors f)
                      (make_predecessors (successors f))) 
                   (f, nil)) as R.
  destruct R as [f1 dones]; auto using program_sim_refl.
  rewrite does_phi_elim_is_true.
  remember (fix_temporary_fdef (SafePrimIter.iterate fdef eliminate_step f1))
    as R.
  destruct R as [f2|]; auto using program_sim_refl.
  apply program_sim_trans with (P2:=
    [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]).
    apply program_sim_trans with (P2:=
      [module_intro los nts 
        (Ps1 ++ product_fdef (SafePrimIter.iterate fdef eliminate_step f1) 
          :: Ps2)]).
      eapply fix_temporary_fdef_sim; eauto.
      apply eliminate_phis_sim; auto.

    eapply macro_mem2reg_fdef_sim; eauto.
Qed.

Lemma mem2reg_run_sim_aux: forall (main : id) (VarArgs : list (GVsT DGVs))        
  (los : layouts) (nts : namedts) (Ps2 Ps1: products),
  program_sim
    [module_intro los nts
      (Ps1 ++ List.map
        (fun p : product =>
          match p with
          | product_fdef f => product_fdef (mem2reg_fdef f)
          | _ => p
          end) Ps2)] [module_intro los nts (Ps1++Ps2)] main VarArgs.
Proof.
  induction Ps2; simpl; intros.
    apply program_sim_refl.

    assert (J:=@IHPs2 (Ps1 ++ [a])). clear IHPs2.
    simpl_env in J. simpl in J. 
    destruct a; auto.
    apply program_sim_trans with (P2:=
      [module_intro los nts
        (Ps1 ++ product_fdef f :: 
           List.map (fun p : product =>
                     match p with
                     | product_fdef f => product_fdef (mem2reg_fdef f)
                     | _ => p
                     end) Ps2)]); auto.
    apply mem2reg_fdef_sim.
Qed.

Lemma mem2reg_run_sim: forall (m:module) (main:id) (VarArgs:list (GVsT DGVs)),
  program_sim [mem2reg.run m] [m] main VarArgs.
Proof.
  destruct m as [los nts Ps].
  unfold mem2reg.run.
  intros.
  assert (J:=@mem2reg_run_sim_aux main VarArgs los nts Ps nil).
  auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
