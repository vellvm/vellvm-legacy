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

Variable lc0 : GVMap.

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

Lemma tv_subblock__is__correct : forall S TD Ps 
                            sb1 sb2 lc als gl lc' gl' tr Mem Mem' als',
  uniq gl ->
  uniq lc ->
  wf_subblock sb2 ->
  tv_subblock sb1 sb2 lc gl ->
  dbSubblock S TD Ps lc als gl Mem sb1 lc' als' gl' Mem' tr ->
  dbSubblock S TD Ps lc als gl Mem sb2 lc' als' gl' Mem' tr.
Proof.
  intros S TD Ps sb1 sb2 lc als gl lc' gl' tr Mem0 Mem' als'
         Huniqg Huniqc Wf Htv_subblock HdbSubblock.
  inversion HdbSubblock; subst. clear HdbSubblock.
  destruct sb2.
  unfold tv_subblock in Htv_subblock.
  simpl in Htv_subblock.
  destruct Htv_subblock as [EQ1 EQ2]; subst.
  inversion Wf; subst.
  apply tv_cmds__is__correct with (cs':=l0) in H; eauto.
Qed.

Lemma tv_subblocks__is__correct : forall sbs1 S TD Ps 
                            sbs2 lc als gl lc' gl' tr Mem Mem' als',
  uniq gl ->
  uniq lc ->
  wf_subblocks sbs2 ->
  tv_subblocks sbs1 sbs2 lc gl ->
  dbSubblocks S TD Ps lc als gl Mem sbs1 lc' als' gl' Mem' tr ->
  dbSubblocks S TD Ps lc als gl Mem sbs2 lc' als' gl' Mem' tr.
Proof.
  induction sbs1; intros S TD Ps sbs2 lc als gl lc' gl' tr Mem0 Mem' als' 
                  Huniqg Huniqc Wf Htv_subblocks HdbSubblocks.
  
  destruct sbs2;try solve [auto | simpl in Htv_subblocks; inversion Htv_subblocks].
  
  destruct sbs2; simpl in Htv_subblocks; inversion Htv_subblocks.
  clear Htv_subblocks.
  inversion HdbSubblocks; subst. clear HdbSubblocks.
  inversion Wf; subst. clear Wf.
  apply tv_subblock__is__correct with (sb2:=s) in H10; auto.
  apply IHsbs1 with (sbs2:=sbs2) in H16; eauto.
    admit. (*uniq*)
    admit. (*uniq*)
    admit. (*tv inclusion*)
Qed.

Lemma tv_blocks__is__correct : forall S TD Ps gl lp lc n tmn1
                            l1 ps1 sbs1 ps' l'
                            lb1 lb2 lc' gl' tr Mem Mem' als' tmn' sbs1',
  tv_blocks lb1 lb2 lc gl ->
  nth_error lb1 n = Some (block_intro l1 ps1 sbs1 tmn1) ->
  dbBlocks S TD Ps lp
    (mkState (mkEC (block_intro l1 ps1 sbs1 tmn1) lc nil) gl Mem)
    (mkState (mkEC (block_intro l' ps' sbs1' tmn') lc' als') gl' Mem')
    tr ->
  exists l2, exists ps2, exists sbs2, exists tmn2, exists sbs2',
    nth_error lb2 n = Some (block_intro l2 ps2 sbs2 tmn2) /\
    tv_block (block_intro l1 ps1 sbs1 tmn1) (block_intro l2 ps2 sbs2 tmn2) lc gl /\
    dbBlocks S TD Ps lp
      (mkState (mkEC (block_intro l2 ps2 sbs2 tmn2) lc nil) gl Mem)
      (mkState (mkEC (block_intro l' ps' sbs2' tmn') lc' als') gl' Mem')
      tr /\ 
    tv_subblocks sbs1' sbs2' lc gl.
Admitted.

Lemma tv_fdef__is__correct : forall TD Ps S1 S2 fid la lb1 lb2 lc gl lc' gl' als' Mem Mem' Rid oResult tr lp rt,
  lookupFdefViaIDFromSystem S1 fid = Some (fdef_intro (fheader_intro rt fid la) lb1) ->
  lookupFdefViaIDFromSystem S2 fid = Some (fdef_intro (fheader_intro rt fid la) lb2) ->
  tv_blocks lb1 lb2 lc gl ->
  dbFdef fid rt lp S1 TD Ps lc gl Mem lc' gl' als' Mem' Rid oResult tr ->
  dbFdef fid rt lp S2 TD Ps lc gl Mem lc' gl' als' Mem' Rid oResult tr.
Proof.
  intros TD Ps S1 S2 fid la lb1 lb2 lc gl lc' gl' als' Mem0 Mem' Rid oResult tr lp rt
         HlookupS1 HlookupS2 Htv_blocks HdbFdef.
  inversion HdbFdef; subst; clear HdbFdef.
    rewrite HlookupS1 in H. inversion H; subst. clear H.
    
    apply tv_blocks__is__correct with (n:=0)(lb1:=lb)(lb2:=lb2) in H1; auto.
      destruct H1 as [l3 [ps3 [sbs3 [tmn3 [sbs2' [J1 [Htv_block [HdbBlocks Htv_subblocks]]]]]]]].
      unfold tv_block in Htv_block. 
      destruct Htv_block as [J2 [Htv_phinodes [Htv_subblocks' J3]]]; subst.
      apply tv_subblocks__is__correct with (sbs2:=sbs2') in H2; auto.
        assert (S1=S2) as Eq. admit.
        subst.
        apply dbFdef_func with (l1:=l3)(ps1:=ps3)(sbs1:=sbs3)(tmn1:=tmn3)(la:=la0)(lb:=lb2)
          (lc1:=lc2)(gl1:=gl1)(Mem1:=Mem2)(als1:=als1)(l2:=l2)(ps2:=ps2)(sbs2:=sbs2'); auto.
          clear - H0 J1 Htv_subblocks' Htv_phinodes Htv_blocks. admit.

          admit. (*uniq*)
          admit. (*uniq*)
          admit. (*Wf*)

        clear - Htv_subblocks.
        admit. (*tv inclusion*)

        clear - Htv_blocks.
        admit. (*tv inclusion*)
        
        clear - H0. admit.

    admit. (*The other case*)
Qed.

Extraction "symexe" tv_blocks.

