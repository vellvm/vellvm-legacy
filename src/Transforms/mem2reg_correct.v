Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../SoftBound".
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
Require Import program_sim.
Require Import las.
Require Import laa.
Require Import dae.
Require Import dse.
Require Import die.
Require Import sas.
Require Import phiplacement_bsim.

(* We are proving the macro-based m2r pass *)
Parameter does_macro_m2r_is_true: mem2reg.does_macro_m2r tt = true.

Parameter print_reachablity_is_true: forall rd, print_reachablity rd = true.

Parameter does_phi_elim_is_true: does_phi_elim tt = true.

Parameter does_stld_elim_is_true: does_stld_elim tt = true.

Lemma las_die_sim: forall (los : layouts) (nts : namedts) (fh : fheader) 
  (dones : list id) (pinfo: PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (i0 : id)
  (v : value) (cs : cmds) 
  (Hst : ret inl (i0, v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo) 
  (HwfS : 
     wf_system nil
       [module_intro los nts 
         (Ps1 ++ 
          product_fdef 
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
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
       product_fdef (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))::
       Ps2)]
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
    destruct (@subst_fdef__diinfo 
      (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) i1 v) as 
      [diinfo [J1 J2]].
    eapply die_sim; eauto.
      admit. (* subst pres wfs *)  
    eapply las_sim; eauto.
Qed.

Lemma laa_die_sim: forall (los : layouts) (nts : namedts) (fh : fheader) 
  (dones : list id) (pinfo : PhiInfo) (main : id) (VarArgs : list (GVsT DGVs))
  (bs1 : list block) (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator)
  (bs2 : list block) (Ps1 : list product) (Ps2 : list product) (v : value)
  (cs : cmds) 
  (Hst : ret inr (v, cs) = find_init_stld cs0 (PI_id pinfo) dones)
  (i1 : id) (Hld : ret inl i1 = find_next_stld cs (PI_id pinfo))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo) 
  (HwfS : 
     wf_system nil
       [module_intro los nts 
         (Ps1 ++ 
          product_fdef 
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
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
    destruct (@subst_fdef__diinfo 
      (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) i1 v) as 
      [diinfo [J1 J2]].
    eapply die_sim; eauto.
      admit. (* subst pres wfS *)  

    eapply laa_sim; eauto.
Qed.

Lemma elim_stld_cmds_sim: forall los nts fh dones (pinfo:PhiInfo) f0 dones0 main 
  VarArgs bs1 l0 ps0 cs0 tmn0 bs2 Ps1 Ps2
  (Hpass : (f0, true, dones0) =
           elim_stld_cmds
             (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) cs0
             (PI_id pinfo) dones)
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
  (Hwfpi: WF_PhiInfo pinfo) 
  (HwfS : 
     wf_system nil
       [module_intro los nts 
         (Ps1 ++ 
          product_fdef 
            (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2))
          :: Ps2)]),
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
  remember (find_init_stld cs0 (PI_id pinfo) dones) as R1.
  destruct R1 as [[[[]]|[]]|]; tinv Hpass.
    remember (find_next_stld c (PI_id pinfo)) as R2.
    destruct R2 as [[|[]]|]; inv Hpass.
      eapply las_die_sim; eauto.
      eapply sas_sim; eauto.
      apply program_sim_refl.

    remember (find_next_stld c (PI_id pinfo)) as R2.
    destruct R2 as [[|[]]|]; inv Hpass.
      eapply laa_die_sim; eauto.
      apply program_sim_refl.
      apply program_sim_refl.
Qed.

Lemma elim_stld_blocks_sim_aux: forall los nts fh dones (pinfo:PhiInfo) f0 dones0
  main VarArgs Ps1 Ps2 flag bs2 bs1 
  (Hpass:elim_stld_blocks (fdef_intro fh (bs1++bs2)) bs2 (PI_id pinfo) dones = 
    (f0, flag, dones0))
  (Heq: PI_f pinfo = fdef_intro fh (bs1 ++ bs2))
  (Hwfpi: WF_PhiInfo pinfo) 
  (HwfS : 
     wf_system nil
       [module_intro los nts 
         (Ps1 ++ 
          product_fdef 
            (fdef_intro fh (bs1 ++ bs2)) :: Ps2)]),
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
        (fdef_intro fh (bs1 ++ block_intro l0 ps0 cs0 tmn0 :: bs2)) 
          cs0 (PI_id pinfo) dones) as R.
    destruct R as [[f' []] dones']; inv Hpass; auto.
      eapply elim_stld_cmds_sim; eauto.

      apply elim_stld_cmds_unchanged in HeqR. subst. 
      rewrite_env ((bs1 ++ [block_intro l0 ps0 cs0 tmn0]) ++ bs2) in H0.
      apply IHbs2 in H0; simpl_env in *; auto.
Qed.

Lemma elim_stld_blocks_sim: forall los nts fh dones (pinfo:PhiInfo) f0 dones0 
  main VarArgs Ps1 Ps2 flag bs 
  (Hpass:elim_stld_blocks (fdef_intro fh bs) bs (PI_id pinfo) dones 
           = (f0, flag, dones0))
  (Heq: PI_f pinfo = fdef_intro fh bs)
  (Hwfpi: WF_PhiInfo pinfo) 
  (HwfS : 
     wf_system nil
       [module_intro los nts 
         (Ps1 ++ product_fdef (fdef_intro fh bs) :: Ps2)]),
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

Lemma elim_stld_sim: forall f1 dones1 f2 dones2 Ps1 Ps2 los nts main VarArgs
  pid (pinfo:PhiInfo) 
  (Hpass: SafePrimIter.iterate _ (elim_stld_step pid) 
    (f1, dones1) = (f2, dones2))
  (Heq1: PI_f pinfo = f1) (Heq2: PI_id pinfo = pid)
  (Hwfpi: WF_PhiInfo pinfo) 
  (HwfS : wf_system nil [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]),
  program_sim
    [module_intro los nts (Ps1 ++ product_fdef f2 :: Ps2)]
    [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)]
    main VarArgs.
Proof.
  intros. subst.
  set (P:=fun (re:(fdef * list id)) =>
          let '(f, _) := re in
          program_sim [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]
           [module_intro los nts (Ps1 ++ product_fdef (PI_f pinfo) :: Ps2)] 
           main VarArgs).
  assert (P (PI_f pinfo, dones1)) as HPf1.
    unfold P. apply program_sim_refl.
  apply SafePrimIter.iterate_prop with (P:=P) in Hpass; auto.
    unfold elim_stld_step.
    intros a HPa.
    destruct a as [f dones].
    unfold elim_stld_fdef.
    destruct f as [fh bs].
    remember (elim_stld_blocks (fdef_intro fh bs) bs (PI_id pinfo) dones) as R.
    destruct R as [[f0 flag0] dones0]; auto.
    assert (P (f0, dones0)) as HPf0.
      unfold P.
      apply program_sim_trans with (P2:=
           [module_intro los nts 
             (Ps1 ++ product_fdef (fdef_intro fh bs) :: Ps2)]); auto.
      eapply elim_stld_blocks_sim; eauto.
        admit. (* PhiInfo is preserved *)
        admit. (* wfS is preserved *)
    destruct flag0; auto.
Qed.

Lemma macro_mem2reg_fdef_sim: forall rd f1 dones1 f2 dones2 Ps1 Ps2 los nts main
  VarArgs (Hreach: ret rd = dtree.reachablity_analysis f1)
  (HwfS : wf_system nil [module_intro los nts (Ps1 ++ product_fdef f1 :: Ps2)])
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
    destruct R as [[[[pid ty] num] al]|]; auto.
    set (pinfo:=mkPhiInfo f rd pid ty num al).

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
          eapply elim_stld_sim with 
            (pinfo:=mkPhiInfo (phinodes_placement f rd pid ty al (successors f1)
                      (make_predecessors (successors f1))) rd pid ty num al); 
            eauto.
            admit. (* PhiInfo pres*)
            admit. (* wfS pres*)

          apply program_sim_trans with (P2:=
            [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]); auto.
            assert (successors f1 = successors f) as EQ1. admit. rewrite EQ1.
            assert (dtree.reachablity_analysis f1 = 
                      dtree.reachablity_analysis f) as EQ2.
              admit. 
            rewrite EQ2 in Hreach.
            eapply phinodes_placement_sim; eauto.
              admit. (* wfS pres *) 
       assert (P 
                (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef pid f0,
                 nil)) as Pf.
         remember (load_in_fdef pid f0) as R.
         destruct R; auto.
         unfold P.
         apply program_sim_trans with (P2:=
           [module_intro los nts (Ps1 ++ product_fdef f0 :: Ps2)]); auto.
         apply dse_sim with (pinfo:=mkPhiInfo f0 rd pid ty num al); auto.
           admit. (* WFPI pres *)
           admit. (* wfS pres *)
       remember (used_in_fdef pid
           (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef pid f0)) as R.
       destruct R; auto.
       apply program_sim_trans with (P2:=
         [module_intro los nts 
           (Ps1 ++ product_fdef 
                     (if load_in_fdef pid f0 then f0 
                      else elim_dead_st_fdef pid f0) :: Ps2)]); auto.
       eapply dae_sim with 
         (pinfo:=mkPhiInfo 
           (if load_in_fdef pid f0 then f0 else elim_dead_st_fdef pid f0)
           rd pid ty num al); eauto.
         admit. (* WFPI pres *)
         admit. (* wfS pres *)
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
  (los : layouts) (nts : namedts) (f : fdef) (Ps2 Ps1 : products)
 (HwfS : wf_system nil [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
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
  (los : layouts) (nts : namedts) (Ps2 Ps1: products)
  (HwfS : wf_system nil [module_intro los nts (Ps1 ++ Ps2)]),
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
      admit. (* wfS pres *)
Qed.

Lemma mem2reg_run_sim: forall (m:module) (main:id) (VarArgs:list (GVsT DGVs))
  (HwfS : wf_system nil [m]),
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
