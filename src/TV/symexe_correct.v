Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Export targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import trace.
Require Import symexe_def.
Require Import symexe_complete.
Require Import symexe_sound.

Export SimpleSE.

(* Correctness of the cmds validator *)

Definition tv_cmds (cs1 cs2 : list cmd) (lc gl:GVMap) :=
se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs1 =
se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs2.

Lemma tv_cmds__is__correct : forall TD cs cs' lc1 als1 gl1 Mem1 lc2 als2 gl2 Mem2 tr,
  uniq gl1 ->
  uniq lc1 ->  
  wf_cmds cs' ->
  tv_cmds cs cs' lc1 gl1 ->
  dbCmds TD lc1 als1 gl1 Mem1 cs lc2 als2 gl2 Mem2 tr ->
  dbCmds TD lc1 als1 gl1 Mem1 cs' lc2 als2 gl2 Mem2 tr.
Proof.
  intros TD cs cs' lc1 als1 gl1 Mem1 lc2 als2 gl2 Mem2 tr Huniqg Huniqc Wf Htv_cmds HdbCmds.
  unfold tv_cmds in Htv_cmds.
  assert (Uniqs:=HdbCmds).
  apply dbCmds_uniq in Uniqs; auto.
  destruct Uniqs as [Uniqg2 Uniqc2].
  apply op_cmds__satisfy__se_cmds in HdbCmds; auto.
  rewrite Htv_cmds in HdbCmds.
  apply se_cmds__denote__op_cmds; auto.
Qed.

Definition tv_subblock (sb1 sb2:subblock) (lc gl:GVMap) :=
match (sb1, sb2) with
| (subblock_intro cs1 call1, subblock_intro cs2 call2) =>
  let st1 := se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs1 in
  let st2 := se_cmds (mkSstate (env_to_smap gl lc) smem_init sframe_init nil) cs2 in
  let cl1 := se_call st1 call1 in
  let cl2 := se_call st2 call2 in
  st1 = st2 /\ call1 = call2
end.

Fixpoint tv_subblocks (sbs1 sbs2:list subblock) (lc gl:GVMap) :=
match (sbs1, sbs2) with
| (nil, nil) => True
| (sb1::sbs1', sb2::sbs2') => tv_subblock sb1 sb2 lc gl /\ tv_subblocks sbs1' sbs2' lc gl 
| _ => False
end.

Fixpoint tv_phinodes (ps1 ps2:list phinode) :=
match (ps1, ps2) with
| (nil, nil) => True
| (p1::ps1', p2::ps2') => p1=p2 /\ tv_phinodes ps1' ps2'
| _ => False
end.

Definition tv_block (b1 b2:block) (lc gl:GVMap) :=
match (b1, b2) with
| (block_intro l1 ps1 sbs1 tmn1, block_intro l2 ps2 sbs2 tmn2) =>
  l1 = l2 /\ tv_phinodes ps1 ps2 /\ tv_subblocks sbs1 sbs2 lc gl /\ tmn1 = tmn2
end.

Fixpoint tv_blocks (bs1 bs2:list block) (lc gl:GVMap) :=
match (bs1, bs2) with
| (nil, nil) => True
| (b1::bs1', b2::bs2') => tv_block b1 b2 lc gl /\ tv_blocks bs1' bs2' lc gl 
| _ => False
end.

Variable lc0 gl0 : GVMap.

Definition tv_fdef (f1 f2:fdef) (gl:GVMap) :=
match (f1, f2) with
| (fdef_intro fh1 lb1, fdef_intro fh2 lb2) =>
  fh1 = fh2 /\ tv_blocks lb1 lb2 lc0 gl
end.

Fixpoint tv_products (Ps1 Ps2:list product):=
match (Ps1, Ps2) with
| (nil, nil) => True
| (product_fdec f1::Ps1', product_fdec f2::Ps2') => 
  f1 = f2 /\ tv_products Ps1' Ps2'
| (product_fdef f1::Ps1', product_fdef f2::Ps2') => 
  tv_fdef f1 f2 gl0 /\ tv_products Ps1' Ps2'
| (product_gvar gvar1::Ps1', product_gvar gvar2::Ps2') => 
  gvar1 = gvar2 /\ tv_products Ps1' Ps2'
| _ => False
end.

Definition tv_module (m1 m2:module) :=
match (m1, m2) with
| (module_intro TD1 Ps1, module_intro TD2 Ps2) =>
  TD1 = TD2 /\ tv_products Ps1 Ps2
end.

Fixpoint tv_system (S1 S2:system) :=
match (S1, S2) with
| (nil, nil) => True
| (m1::S1', m2::S2') => tv_module m1 m2 /\ tv_system S1' S2'
| _ => False
end.

Inductive wf_subblock : subblock -> Prop :=
| wf_subblock_intro : forall cs call0, 
  wf_cmds cs ->
  wf_subblock (subblock_intro cs call0).

Inductive wf_subblocks : list subblock -> Prop :=
| wf_subblocks_nil : wf_subblocks nil
| wf_subblocks_cons : forall sb sbs,
  wf_subblock sb ->
  wf_subblocks sbs ->
  wf_subblocks (sb::sbs).

Inductive wf_block : block -> Prop :=
| wf_block_intro : forall l ps sbs tmn, 
  wf_subblocks sbs ->
  wf_block (block_intro l ps sbs tmn).

Lemma tv_terminator__is__correct : forall TD fh1 lb1 fh2 lb2 B1 B2 lc gl tmn B1' lc' tr,
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) gl0 ->
  tv_block B1 B2 lc gl ->
  dbTerminator TD (fdef_intro fh1 lb1) B1 lc gl tmn B1' lc' tr ->
  exists B2', exists n,
    tv_block B1' B2' lc gl /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    dbTerminator TD (fdef_intro fh2 lb2) B2 lc gl tmn B2' lc' tr.
Proof.
  intros TD fh1 lb1 fh2 lb2 B1 B2 lc gl tmn B1' lc' tr Htv_fdef Htv_block HdbTerminator.
  inversion HdbTerminator; subst.
    assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' lc gl /\ 
                                  nth_error lb1 n = Some (block_intro l' ps' sbs' tmn') /\
                                  nth_error lb2 n = Some B2') as J.
      admit. (*lookup*)
    destruct J as [B2' [n [J1 [J2 J3]]]].
    exists B2'. exists n. split; auto. split; auto. split; auto.
    destruct B2' as [l2' ps2' sbs2' tmn2'].
    apply dbBranch with (c:=c); auto.
      admit. (*lookup*)
      admit. (*switch*)
    
    assert (exists B2', exists n, tv_block (block_intro l' ps' sbs' tmn') B2' lc gl /\ 
                                  nth_error lb1 n = Some (block_intro l' ps' sbs' tmn') /\
                                  nth_error lb2 n = Some B2') as J.
      admit. (*lookup*)
    destruct J as [B2' [n [J1 [J2 J3]]]].
    exists B2'. exists n. split; auto. split; auto. split; auto.
    destruct B2' as [l2' ps2' sbs2' tmn2'].
    apply dbBranch_uncond; auto.
      admit. (*lookup*)
      admit. (*switch*)
Qed.

Definition tv_dbCall__is__correct_prop S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr
  (db:dbCall S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr) :=
  forall S2 Ps2,
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  dbCall S2 TD Ps2 lc gl Mem0 call0 lc' gl' Mem' tr.
Definition tv_subblock__is__correct_prop S1 TD Ps1 lc als gl Mem sb1 lc' als' gl' Mem' tr
  (db:dbSubblock S1 TD Ps1 lc als gl Mem sb1 lc' als' gl' Mem' tr) :=
  forall S2 Ps2 sb2,
  uniq gl ->
  uniq lc ->
  wf_subblock sb2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_subblock sb1 sb2 lc gl ->
  dbSubblock S2 TD Ps2 lc als gl Mem sb2 lc' als' gl' Mem' tr.
Definition tv_subblocks__is__correct_prop S1 TD Ps1 lc als gl Mem sbs1 lc' als' gl' Mem' tr
  (db:dbSubblocks S1 TD Ps1 lc als gl Mem sbs1 lc' als' gl' Mem' tr) :=
  forall S2 Ps2 sbs2,
  uniq gl ->
  uniq lc ->
  wf_subblocks sbs2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_subblocks sbs1 sbs2 lc gl ->
  dbSubblocks S2 TD Ps2 lc als gl Mem sbs2 lc' als' gl' Mem' tr.
Definition tv_block__is__correct_prop S1 TD Ps1 F1 arg state1 state2 tr
  (db:dbBlock S1 TD Ps1 F1 arg state1 state2 tr) :=
  forall S2 Ps2 fh1 lb1 fh2 lb2 B1 lc als gl Mem B1' lc' als' gl' Mem' B2,
  state1 = mkState (mkEC B1 lc als) gl Mem ->
  state2 = mkState (mkEC B1' lc' als') gl' Mem' ->
  F1 = fdef_intro fh1 lb1 ->
  uniq gl ->
  uniq lc ->
  wf_block B2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) gl0 ->
  tv_block B1 B2 lc gl ->
  exists B2', exists n,
    dbBlock S2 TD Ps2 (fdef_intro fh2 lb2) arg 
      (mkState (mkEC B2 lc als) gl Mem) 
      (mkState (mkEC B2' lc' als') gl' Mem')
      tr /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' lc gl.
Definition tv_blocks__is__correct_prop S1 TD Ps1 F1 lp state1 state2 tr
  (db:dbBlocks S1 TD Ps1 F1 lp state1 state2 tr) :=
  forall S2 Ps2 fh1 lb1 fh2 lb2 gl lc n tmn1
                            l1 ps1 sbs1 ps1' l1' als
                            lc' gl' Mem Mem' als' tmn1' sbs1',
  state1 = (mkState (mkEC (block_intro l1 ps1 sbs1 tmn1) lc als) gl Mem) ->
  state2 = (mkState (mkEC (block_intro l1' ps1' sbs1' tmn1') lc' als') gl' Mem') ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  F1 = fdef_intro fh1 lb1 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) gl0 ->
  tv_blocks lb1 lb2 lc gl ->
  nth_error lb1 n = Some (block_intro l1 ps1 sbs1 tmn1) ->
  exists l2, exists ps2, exists sbs2, exists tmn2, 
  exists l2', exists ps2', exists sbs2', exists tmn2', exists n',
    nth_error lb2 n = Some (block_intro l2 ps2 sbs2 tmn2) /\
    nth_error lb1 n' = Some (block_intro l1' ps1' sbs1' tmn1') /\
    nth_error lb2 n' = Some (block_intro l2' ps2' sbs2' tmn2') /\
    tv_block (block_intro l1 ps1 sbs1 tmn1) (block_intro l2 ps2 sbs2 tmn2) lc gl /\
    tv_block (block_intro l1' ps1' sbs1' tmn1') (block_intro l2' ps2' sbs2' tmn2') lc gl /\
    dbBlocks S2 TD Ps2 (fdef_intro fh2 lb2) lp
      (mkState (mkEC (block_intro l2 ps2 sbs2 tmn2) lc als) gl Mem)
      (mkState (mkEC (block_intro l2' ps2' sbs2' tmn2') lc' als') gl' Mem')
      tr.
Definition tv_fdef__is__correct_prop fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' Rid oResult tr
  (db:dbFdef fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' Rid oResult tr) :=
  forall Ps2 S2 la lb1,
  lookupFdefViaIDFromProducts Ps1 fid = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists lb2,
    lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2 lc gl /\
    dbFdef fid rt lp S2 TD Ps2 lc gl Mem lc' gl' als' Mem' Rid oResult tr.

Lemma tv_blocks_nth_Some_inv : forall lb1 lb2 lc gl n B1,
  tv_blocks lb1 lb2 lc gl ->
  nth_error lb1 n = Some B1 ->
  exists B2, 
    nth_error lb2 n = Some B2 /\ tv_block B1 B2 lc gl.
Admitted. (*nth*)

Lemma tv__is__correct :
  (forall S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr db, 
     tv_dbCall__is__correct_prop S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr db) /\
  (forall S1 TD Ps1 lc als gl Mem sb1 lc' als' gl' Mem' tr db,
     tv_subblock__is__correct_prop S1 TD Ps1 lc als gl Mem sb1 lc' als' gl' Mem' tr db) /\
  (forall S1 TD Ps1 lc als gl Mem sbs1 lc' als' gl' Mem' tr db,
     tv_subblocks__is__correct_prop S1 TD Ps1 lc als gl Mem sbs1 lc' als' gl' Mem' tr db) /\
  (forall S1 TD Ps1 F1 arg state1 state2 tr db,
     tv_block__is__correct_prop S1 TD Ps1 F1 arg state1 state2 tr db) /\
  (forall S1 TD Ps1 F1 lp state1 state2 tr db,
     tv_blocks__is__correct_prop S1 TD Ps1 F1 lp state1 state2 tr db) /\
  (forall fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' Rid oResult tr db,
     tv_fdef__is__correct_prop fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' Rid oResult tr db).
Proof.
(db_mutind_cases
  apply db_mutind with
    (P  := tv_dbCall__is__correct_prop)
    (P0 := tv_subblock__is__correct_prop)
    (P1 := tv_subblocks__is__correct_prop)
    (P2 := tv_block__is__correct_prop)
    (P3 := tv_blocks__is__correct_prop)
    (P4 := tv_fdef__is__correct_prop) Case);
  unfold tv_dbCall__is__correct_prop, 
         tv_subblock__is__correct_prop, tv_subblocks__is__correct_prop,
         tv_block__is__correct_prop, tv_blocks__is__correct_prop,
         tv_fdef__is__correct_prop; intros; subst.
Case "dbCall_intro".
  inversion d; subst.
    apply H with (S2:=S2)(Ps2:=Ps2) in H2; auto.
    clear H.
    destruct H2 as [lb2 [J1 [J2 J3]]].
    eauto.

    apply H with (S2:=S2)(Ps2:=Ps2) in H2; auto.
    clear H.
    destruct H2 as [lb2 [J1 [J2 J3]]].
    eauto.

Case "dbSubblock_intro".
  destruct sb2.
  unfold tv_subblock in H5.
  simpl in H5.
  destruct H5 as [EQ1 EQ2]; subst.
  inversion H2; subst.
  apply tv_cmds__is__correct with (cs':=l0) in d; eauto.

Case "dbSubblocks_nil".
  destruct sbs2;try solve [auto | simpl in H4; inversion H4].
  
Case "dbSubblocks_cons".
  destruct sbs2; simpl in H6; inversion H6.
  clear H6.
  inversion H3; subst. clear H3.  
  apply H with (S2:=S2)(Ps2:=Ps2) in H7; auto.
  assert (tv_subblocks sbs sbs2 lc2 gl2) as J. 
    admit. (*tv inclusion*)
  apply H0 with (S2:=S2)(Ps2:=Ps2) in J; eauto.
    admit. (*uniq*)
    admit. (*uniq*)

Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  destruct B2 as [l2 ps2 sbs2 tmn2].
  unfold tv_block in H9.
  destruct H9 as [EQ1 [Htv_phinodes [Htv_subblocks EQ2]]]; subst.
  inversion H5; subst. clear H5.
  assert (J:=Htv_subblocks).
  apply H with (S2:=S2)(Ps2:=Ps2) in J; auto.
  apply tv_terminator__is__correct with (B2:=block_intro l2 ps2 sbs2 tmn2)(fh2:=fh2)(lb2:=lb2) in d0; auto.
    destruct d0 as [B2' [n [Htv_block1'2' [J2 [J3 Hdb]]]]].
    exists B2'. exists n. 
    split; eauto.
    split; auto.
    split; auto.
      clear - Htv_block1'2'.
      admit. (*tv inclusion*)

    unfold tv_block.
    split; auto.
    split; auto.
    split; auto.
      clear - Htv_subblocks.
      admit. (*tv inclusion*)      

Case "dbBlocks_nil".
  inversion H0; subst. clear H0.
  apply tv_blocks_nth_Some_inv with (n:=n)(B1:=block_intro l1' ps1' sbs1' tmn1') in H5; auto.
  destruct H5 as [[l2 ps2 sbs2 tmn2] [Hnth_error2 Htv_block]].
  exists l2. exists ps2. exists sbs2. exists tmn2.
  exists l2. exists ps2. exists sbs2. exists tmn2. 
  exists n.
  split; auto.

Case "dbBlocks_cons".
  inversion d; subst.
  assert (J:=H7).  
  apply tv_blocks_nth_Some_inv with (n:=n)(B1:=block_intro l1 ps1 sbs1 tmn1) in J; auto.
  destruct J as [[l2 ps2 sbs2 tmn2] [Hnth_error2 Htv_block12]].
  assert (J:=Htv_block12).
  apply H with (S2:=S0)(Ps2:=Ps2)(fh3:=fh2)(lb3:=lb2)(fh2:=fh1)(lb2:=lb1)(Mem:=Mem0)(B1':=B')(lc':=lc3)(als':=als2)(gl':=gl2)(Mem':=Mem2)(als0:=als) in J; auto.
    destruct J as [B2' [n' [Hdb [J1 [J2 Htv_block12']]]]].
    clear H.
    destruct B' as [l3 ps3 sbs3 tmn3].
    assert (tv_blocks lb1 lb2 lc3 gl2) as H.
      admit. (*tv inclusion*)      
    apply H0 with (S2:=S0)(Ps2:=Ps2)(fh2:=fh1)(fh3:=fh2)(n:=n')(tmn1:=tmn3)
      (l1:=l3)(ps1:=ps3)(sbs1:=sbs3)(ps1'0:=ps1')(l1'0:=l1')(als:=als2)(lc'0:=lc')(gl'0:=gl')
      (Mem:=Mem2)(Mem'0:=Mem')(als'0:=als')(tmn1'0:=tmn1')(sbs1'0:=sbs1') in H; auto.
    destruct H as [l4 [ps4 [sbs4 [tmn4 [l4' [ps4' [sbs4' [tmn4' [n'' [J3 [J4 [J5 [J6 [J7 J8]]]]]]]]]]]]]].
    clear H0.
    exists l2. exists ps2. exists sbs2. exists tmn2.
    exists l4'. exists ps4'. exists sbs4'. exists tmn4'.
    exists n''.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.
      clear - J7.
      admit. (*tv inclusion*)      
      
      rewrite J2 in J3.
      inversion J3; subst. clear J3.
      eauto.

    admit. (*uniq*)
    admit. (*uniq*)
    admit. (*Wf*)

Case "dbFdef_func".
    rewrite H1 in e. inversion e; subst. clear e.
    assert (exists lb2, lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
                        tv_blocks lb lb2 lc gl) as J.
      clear - H1 H3.
      admit. (*lookup*)
    destruct J as [lb2 [H4 H5]].
    exists lb2. split; auto. split; auto.
    assert (tv_blocks lb lb2 (initLocals la (params2GVs TD lp lc gl)) gl) as Htv_blocks.
      clear - H5.
      admit. (*tv inclusion*)      
    apply H with (S2:=S2)(Ps2:=Ps2)(fh1:=fheader_intro rt fid la)(fh2:=fheader_intro rt fid la)(n:=0)
      (ps1':=ps2)(l1':=l2)(als:=nil)(lc':=lc1)(gl':=gl1)
      (Mem:=Mem0)(Mem':=Mem1)(als':=als1)(tmn1':=insn_return rid rt Result)(sbs1':=sbs2) 
      (ps3:=ps1)(sbs3:=sbs1)(tmn2:=tmn1)(l3:=l1)in Htv_blocks; auto.
      clear H.
      destruct Htv_blocks as [l3 [ps3 [sbs3 [tmn2 [l2' [ps2' [sbs2' [tmn2' [n' [J1 [J2 [J3 [J4 [J5 J6]]]]]]]]]]]]]].

      unfold tv_block in J5.
      destruct J5 as [EQ [Htv_phinodes [Htv_subblocks EQ']]]; subst.
      assert (tv_subblocks sbs2 sbs2' lc1 gl1) as Htv_subblocks'.
        clear - Htv_subblocks.
        admit.
      apply H0 with (S2:=S2)(Ps2:=Ps2) in Htv_subblocks'; auto.
        clear H0.
        apply dbFdef_func with (l1:=l3)(ps1:=ps3)(sbs1:=sbs3)(tmn1:=tmn2)(la:=la)(lb:=lb2)
          (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(als1:=als1)(l2:=l2')(ps2:=ps2')(sbs2:=sbs2'); eauto.
          rewrite <- J1. admit.

        admit. (*uniq*)
        admit. (*uniq*)
        admit. (*Wf*) 

      unfold tv_fdef.
      split; auto.
        clear - H5.
        admit. (*tv inclusion*)      

      rewrite <- e0.
      admit.  (*nth*)

Case "dbFdef_proc".
    rewrite H1 in e. inversion e; subst. clear e.
    assert (exists lb2, lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
                        tv_blocks lb lb2 lc gl) as J.
      clear - H1 H3.
      admit.  (*lookup*)
    destruct J as [lb2 [H4 H5]].
    exists lb2. split; auto. split; auto.
    assert (tv_blocks lb lb2 (initLocals la (params2GVs TD lp lc gl)) gl) as Htv_blocks.
      clear - H5.
      admit. (*tv inclusion*)      
    apply H with (S2:=S2)(Ps2:=Ps2)(fh1:=fheader_intro rt fid la)(fh2:=fheader_intro rt fid la)(n:=0)
      (ps1':=ps2)(l1':=l2)(als:=nil)(lc':=lc1)(gl':=gl1)
      (Mem:=Mem0)(Mem':=Mem1)(als':=als1)(tmn1':=insn_return_void rid)(sbs1':=sbs2) 
      (ps3:=ps1)(sbs3:=sbs1)(tmn2:=tmn1)(l3:=l1)in Htv_blocks; auto.
      clear H.
      destruct Htv_blocks as [l3 [ps3 [sbs3 [tmn2 [l2' [ps2' [sbs2' [tmn2' [n' [J1 [J2 [J3 [J4 [J5 J6]]]]]]]]]]]]]].

      unfold tv_block in J5.
      destruct J5 as [EQ [Htv_phinodes [Htv_subblocks EQ']]]; subst.
      assert (tv_subblocks sbs2 sbs2' lc1 gl1) as Htv_subblocks'.
        clear - Htv_subblocks.
        admit.
      apply H0 with (S2:=S2)(Ps2:=Ps2) in Htv_subblocks'; auto.
        clear H0.
        apply dbFdef_proc with (l1:=l3)(ps1:=ps3)(sbs1:=sbs3)(tmn1:=tmn2)(la:=la)(lb:=lb2)
          (lc1:=lc1)(gl1:=gl1)(Mem1:=Mem1)(als1:=als1)(l2:=l2')(ps2:=ps2')(sbs2:=sbs2'); auto.
          rewrite <- J1. admit.

        admit. (*uniq*)
        admit. (*uniq*)
        admit. (*Wf*) 

      unfold tv_fdef.
      split; auto.
        clear - H5.
        admit. (*tv inclusion*)      

      rewrite <- e0.
      admit. (*nth*)
Qed.   

Lemma tv_dbCall__is__correct : forall S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr S2 Ps2,
  dbCall S1 TD Ps1 lc gl Mem0 call0 lc' gl' Mem' tr ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  dbCall S2 TD Ps2 lc gl Mem0 call0 lc' gl' Mem' tr.
Proof.
  intros.
  destruct tv__is__correct as [J _].
  unfold tv_dbCall__is__correct_prop in J.
  eapply J; eauto.
Qed.

Definition tv_subblock__is__correct : forall S1 TD Ps1 lc als gl Mem sb1 lc' als' gl' Mem' tr S2 Ps2 sb2,
  dbSubblock S1 TD Ps1 lc als gl Mem sb1 lc' als' gl' Mem' tr ->
  uniq gl ->
  uniq lc ->
  wf_subblock sb2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_subblock sb1 sb2 lc gl ->
  dbSubblock S2 TD Ps2 lc als gl Mem sb2 lc' als' gl' Mem' tr.
Proof.
  intros.
  destruct tv__is__correct as [_ [J _]].
  unfold tv_subblock__is__correct_prop in J.
  eapply J; eauto.
Qed.

Lemma tv_subblocks__is__correct : forall S1 TD Ps1 lc als gl Mem sbs1 lc' als' gl' Mem' tr S2 Ps2 sbs2,
  dbSubblocks S1 TD Ps1 lc als gl Mem sbs1 lc' als' gl' Mem' tr ->
  uniq gl ->
  uniq lc ->
  wf_subblocks sbs2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_subblocks sbs1 sbs2 lc gl ->
  dbSubblocks S2 TD Ps2 lc als gl Mem sbs2 lc' als' gl' Mem' tr.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [J _]]].
  unfold tv_subblocks__is__correct_prop in J.
  eapply J; eauto.
Qed.

Lemma tv_block__is__correct : forall S1 TD Ps1 arg tr
  S2 Ps2 fh1 lb1 fh2 lb2 B1 lc als gl Mem B1' lc' als' gl' Mem' B2,
  dbBlock S1 TD Ps1 (fdef_intro fh1 lb1) arg (mkState (mkEC B1 lc als) gl Mem) (mkState (mkEC B1' lc' als') gl' Mem') tr ->
  uniq gl ->
  uniq lc ->
  wf_block B2 ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) gl0 ->
  tv_block B1 B2 lc gl ->
  exists B2', exists n,
    dbBlock S2 TD Ps2 (fdef_intro fh2 lb2) arg 
      (mkState (mkEC B2 lc als) gl Mem) 
      (mkState (mkEC B2' lc' als') gl' Mem')
      tr /\
    nth_error lb1 n = Some B1' /\
    nth_error lb2 n = Some B2' /\
    tv_block B1' B2' lc gl.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [_ [J _]]]].
  unfold tv_block__is__correct_prop in J.
  eapply J with (state1:=(mkState (mkEC B1 lc als) gl Mem0))(state2:=(mkState (mkEC B1' lc' als') gl' Mem'))(F1:=(fdef_intro fh1 lb1)); eauto.
Qed.

Lemma tv_blocks__is__correct : forall S1 TD Ps1 lp tr
  S2 Ps2 fh1 lb1 fh2 lb2 gl lc n tmn1
                            l1 ps1 sbs1 ps1' l1' als
                            lc' gl' Mem Mem' als' tmn1' sbs1',
  dbBlocks S1 TD Ps1 (fdef_intro fh1 lb1) lp (mkState (mkEC (block_intro l1 ps1 sbs1 tmn1) lc als) gl Mem) (mkState (mkEC (block_intro l1' ps1' sbs1' tmn1') lc' als') gl' Mem') tr ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  tv_fdef (fdef_intro fh1 lb1) (fdef_intro fh2 lb2) gl0 ->
  tv_blocks lb1 lb2 lc gl ->
  nth_error lb1 n = Some (block_intro l1 ps1 sbs1 tmn1) ->
  exists l2, exists ps2, exists sbs2, exists tmn2, 
  exists l2', exists ps2', exists sbs2', exists tmn2', exists n',
    nth_error lb2 n = Some (block_intro l2 ps2 sbs2 tmn2) /\
    nth_error lb1 n' = Some (block_intro l1' ps1' sbs1' tmn1') /\
    nth_error lb2 n' = Some (block_intro l2' ps2' sbs2' tmn2') /\
    tv_block (block_intro l1 ps1 sbs1 tmn1) (block_intro l2 ps2 sbs2 tmn2) lc gl /\
    tv_block (block_intro l1' ps1' sbs1' tmn1') (block_intro l2' ps2' sbs2' tmn2') lc gl /\
    dbBlocks S2 TD Ps2 (fdef_intro fh2 lb2) lp
      (mkState (mkEC (block_intro l2 ps2 sbs2 tmn2) lc als) gl Mem)
      (mkState (mkEC (block_intro l2' ps2' sbs2' tmn2') lc' als') gl' Mem')
      tr.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [_ [_ [J _]]]]].
  unfold tv_blocks__is__correct_prop in J.
  eapply J with (state1:=(mkState (mkEC (block_intro l1 ps1 sbs1 tmn1) lc als) gl Mem0))(state2:=(mkState (mkEC (block_intro l1' ps1' sbs1' tmn1') lc' als') gl' Mem'))(F1:=(fdef_intro fh1 lb1)); eauto.
Qed.

Lemma tv_fdef__is__correct : forall fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' Rid oResult tr
  Ps2 S2 la lb1,
  dbFdef fid rt lp S1 TD Ps1 lc gl Mem lc' gl' als' Mem' Rid oResult tr ->
  lookupFdefViaIDFromProducts Ps1 fid = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  tv_system S1 S2 ->
  tv_products Ps1 Ps2 ->
  exists lb2,
    lookupFdefViaIDFromProducts Ps2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) /\
    tv_blocks lb1 lb2 lc gl /\
    dbFdef fid rt lp S2 TD Ps2 lc gl Mem lc' gl' als' Mem' Rid oResult tr.
Proof.
  intros.
  destruct tv__is__correct as [_ [_ [_ [_ [_ J]]]]].
  unfold tv_fdef__is__correct_prop in J.
  eapply J; eauto.
Qed.

Extraction "symexe" tv_blocks.

