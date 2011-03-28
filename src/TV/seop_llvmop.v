Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa/compcert".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Export targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import opsem_conv.
Require Import opsem_pp.
Require Import trace.
Require Import symexe_def.
Require Import ssa_props.
Require Import assoclist.

Export LLVMsyntax.
Export LLVMlib.

Tactic Notation "se_db_mutind_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCall_internal" | c "dbCall_external" | 
    c "dbSubblock_intro" | c "dbSubblocks_nil" | c "dbSubblocks_cons" | 
    c "dbBlock_intro" | c "dbBlocks_nil" | c "dbBlocks_cons" | 
    c "dbFdef_func" | c "dbFdef_proc" ].

Tactic Notation "se_dbCmd_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBop" | c "dbFBop" | c "dbExtractValue" | c "dbInsertValue" |
    c "dbMalloc" | c "dbFree" |
    c "dbAlloca" | c "dbLoad" | c "dbStore" | c "dbGEP" |
    c "dbTrunc" | c "dbExt" | c "dbCast" | 
    c "dbIcmp" | c "dbFcmp" | c "dbSelect" | c "dbLib" ].

Tactic Notation "se_dbTerminator_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBranch" | c "dbBranch_uncond" ].

Tactic Notation "se_dbCmds_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCmds_nil" | c "dbCmds_cons" ].

(****************************************************)
(* seop -> llvmop *)

Lemma seop_dbCmd__llvmop_dbInsn : forall TD lc als gl fs Mem c lc' als' Mem' tr S Ps F B ECs arg tmn cs,
  SimpleSE.dbCmd TD gl lc als Mem c lc' als' Mem' tr ->
  LLVMopsem.dbInsn 
    (mkState S TD Ps ((mkEC F B (c::cs) tmn lc arg als)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC F B cs tmn lc' arg als')::ECs) gl fs Mem')
    tr.
Proof.
  intros TD lc als gl fs Mem0 c lc' als' Mem' tr S Ps F B ECs arg0 tmn cs H.
  (se_dbCmd_cases (destruct H) Case); eauto.
    assert (SimpleSE.callLib Mem0 fid (params2GVs TD lp lc gl) <> None) as J.
      rewrite H. intro J. inversion J.
    apply SimpleSE.callLib__is__defined in J.
    eapply SimpleSE.callLib__is__correct; auto.
Qed.
  
Lemma seop_dbCmds__llvmop_dbop : forall TD lc als gl fs Mem cs cs' lc' als' Mem' tr S Ps F B ECs arg tmn,
  SimpleSE.dbCmds TD gl lc als Mem cs lc' als' Mem' tr ->
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F B (cs++cs') tmn lc arg als)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC F B cs' tmn lc' arg als')::ECs) gl fs Mem')
    tr.
Proof.
  intros TD lc als gl fs Mem0 cs cs' lc' als' Mem' tr S Ps F B ECs arg0 tmn H.
  generalize dependent S.
  generalize dependent Ps.
  generalize dependent F.
  generalize dependent B.
  generalize dependent ECs.
  generalize dependent arg0.
  generalize dependent tmn.
  generalize dependent cs'.
  (se_dbCmds_cases (induction H) Case);intros; auto.
    simpl_env.
    apply seop_dbCmd__llvmop_dbInsn with (S:=S)(Ps:=Ps)(F:=F)(B:=B)(ECs:=ECs)(arg:=arg0)(tmn:=tmn)(cs:=cs++cs')(fs:=fs) in H; auto.
    eapply dbop_cons; eauto.
      apply IHdbCmds.
Qed.

Lemma seop_dbTerminator__llvmop_dbInsn : forall TD lc als gl fs Mem lc' tr S Ps F B ECs arg tmn l' ps' cs' tmn',
  SimpleSE.dbTerminator TD F gl B lc tmn (block_intro l' ps' cs' tmn') lc' tr ->
  LLVMopsem.dbInsn 
    (mkState S TD Ps ((mkEC F B nil tmn lc arg als)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' arg als)::ECs) gl fs Mem)
    tr.
Proof.
  intros TD lc als gl fs Mem0 lc' tr S Ps F B ECs arg0 tmn l' ps' cs' tmn' H.
  inversion H; subst; eauto.
Qed.

Definition seop_dbCall__llvmop_dbCall_prop S TD Ps fs gl lc Mem0 call0 lc' Mem' tr
  (db:SimpleSE.dbCall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr) :=
  forall F B ECs arg tmn cs als,
  LLVMopsem.dbInsn 
    (mkState S TD Ps ((mkEC F B (call0::cs) tmn lc arg als)::ECs) gl fs Mem0)
    (mkState S TD Ps ((mkEC F B cs tmn lc' arg als)::ECs) gl fs Mem')
    tr.
Definition seop_dbSubblock__llvmop_dbop_prop S TD Ps fs gl lc als Mem cs lc' als' Mem' tr
  (db:SimpleSE.dbSubblock S TD Ps fs gl lc als Mem cs lc' als' Mem' tr) :=
  forall F B ECs arg tmn cs',
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F B (cs++cs') tmn lc arg als)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC F B cs' tmn lc' arg als')::ECs) gl fs Mem')
    tr.
Definition seop_dbSubblocks__llvmop_dbop_prop S TD Ps fs gl lc als Mem cs lc' als' Mem' tr
  (db:SimpleSE.dbSubblocks S TD Ps fs gl lc als Mem cs lc' als' Mem' tr) :=
  forall F B ECs arg tmn cs',
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F B (cs++cs') tmn lc arg als)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC F B cs' tmn lc' arg als')::ECs) gl fs Mem')
    tr.
Definition seop_dbBlock__llvmop_dbop_prop S TD Ps fs gl F arg state state' tr
  (db:SimpleSE.dbBlock S TD Ps fs gl F arg state state' tr) :=
  forall l ps cs tmn lc als Mem l' ps' cs' tmn' lc' als' Mem' ECs,
  state = SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem ->
  state' = SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' als') Mem' ->
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F (block_intro l ps cs tmn) cs tmn lc arg als)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' arg als')::ECs) gl fs Mem')
    tr.
Definition seop_dbBlocks__llvmop_dbop_prop S TD Ps fs gl F arg state state' tr
  (db:SimpleSE.dbBlocks S TD Ps fs gl F arg state state' tr) :=
  forall l ps cs tmn lc als Mem l' ps' cs' tmn' lc' als' Mem' ECs,
  state = SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem ->
  state' = SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' als') Mem' ->
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F (block_intro l ps cs tmn) cs tmn lc arg als)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' arg als')::ECs) gl fs Mem')
    tr.
Definition seop_dbFdef__llvmop_dbFdef_prop fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr
  (db:SimpleSE.dbFdef fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr) :=
  forall ECs,
  LLVMopsem.dbFdef fid rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' B' Rid oResult tr.

Lemma seop__llvmop :
  (forall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db, 
     seop_dbCall__llvmop_dbCall_prop S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db,
     seop_dbSubblock__llvmop_dbop_prop S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db,
     seop_dbSubblocks__llvmop_dbop_prop S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl F arg state1 state2 tr db,
     seop_dbBlock__llvmop_dbop_prop S TD Ps fs gl F arg state1 state2 tr db) /\
  (forall S TD Ps fs gl F lp state1 state2 tr db,
     seop_dbBlocks__llvmop_dbop_prop S TD Ps fs gl F lp state1 state2 tr db) /\
  (forall fid rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B' Rid oResult tr db,
     seop_dbFdef__llvmop_dbFdef_prop fid rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B' Rid oResult tr db).
Proof.
(se_db_mutind_cases
  apply SimpleSE.db_mutind with
    (P  := seop_dbCall__llvmop_dbCall_prop)
    (P0 := seop_dbSubblock__llvmop_dbop_prop)
    (P1 := seop_dbSubblocks__llvmop_dbop_prop)
    (P2 := seop_dbBlock__llvmop_dbop_prop)
    (P3 := seop_dbBlocks__llvmop_dbop_prop)
    (P4 := seop_dbFdef__llvmop_dbFdef_prop) Case);
  unfold seop_dbCall__llvmop_dbCall_prop, 
         seop_dbFdef__llvmop_dbFdef_prop, seop_dbSubblock__llvmop_dbop_prop,
         seop_dbSubblocks__llvmop_dbop_prop, seop_dbBlock__llvmop_dbop_prop,
         seop_dbBlocks__llvmop_dbop_prop; intros; subst; eauto.
Case "dbSubblock_intro".
  apply seop_dbCmds__llvmop_dbop with (Ps:=Ps)(F:=F)(B:=B)(ECs:=ECs)(arg:=arg0)(tmn:=tmn)(S:=S)(cs':=call0::cs')(fs:=fs) in d.
  eapply dbop_trans; simpl_env ; eauto.
    apply dbInsn__dbop; auto. 
      apply H.
Case "dbSubblocks_cons".
  rewrite app_ass.
  apply dbop_trans with (state2:=mkState S TD Ps (mkEC F B (cs'++cs'0) tmn lc2 arg0 als2::ECs) gl fs Mem2); eauto.
Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  rewrite <- trace_app_commute.
  apply dbop_trans with (state2:=mkState S TD Ps (mkEC F (block_intro l1 ps0 (cs++cs') tmn0) cs' tmn0 lc2 arg0 als2::ECs) gl fs Mem2); eauto.
    apply seop_dbCmds__llvmop_dbop with (fs:=fs)(Ps:=Ps)(F:=F)(B:=block_intro l1 ps0 (cs++cs') tmn0)(ECs:=ECs)(arg:=arg0)(S:=S)(cs':=nil)(tmn:=tmn0) in d0.
    apply seop_dbTerminator__llvmop_dbInsn with (fs:=fs)(Ps:=Ps)(F:=F)(ECs:=ECs)(arg:=arg0)(S:=S)(als:=als')(Mem:=Mem') in d1.
    simpl_env in d0.
    apply dbop_trans with (state2:=mkState S TD Ps (mkEC F (block_intro l1 ps0 (cs++cs') tmn0) nil tmn0 lc3 arg0 als'::ECs) gl fs Mem'); auto.
      apply dbInsn__dbop; auto. 
Case "dbBlocks_nil".
  inversion H0; subst. clear H0.
  auto.
Case "dbBlocks_cons".
  inversion d; subst.
  destruct B'.
  apply dbop_trans with (state2:=mkState S TD Ps (mkEC F (block_intro l1 p c t) c t lc4 arg0 als3::ECs) gl fs Mem3); eauto.
Case "dbFdef_func".
  apply dbFdef_func with (fid:=fid)(l':=l1)(ps':=ps1)(cs':=cs1)(tmn':=tmn1)(la:=la)(lb:=lb); auto.
    rewrite <- trace_app_commute.
    apply seop_dbCmds__llvmop_dbop with (fs:=fs)(Ps:=Ps)(F:=fdef_intro (fheader_intro rt fid la) lb)(B:=block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result))(ECs:=ECs)(arg:=(params2GVs TD lp lc gl))(S:=S)(cs':=nil)(tmn:=insn_return rid rt Result) in d1.
    simpl_env in d1. 
    apply dbop_trans with (state2:=mkState S TD Ps (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result)) (cs21++cs22) (insn_return rid rt Result) lc1 (params2GVs TD lp lc gl) als1::ECs) gl fs Mem1); auto.
    apply dbop_trans with (state2:=mkState S TD Ps (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result)) cs22 (insn_return rid rt Result) lc2 (params2GVs TD lp lc gl) als2::ECs) gl fs Mem2); auto.
Case "dbFdef_proc".
  apply dbFdef_proc with (fid:=fid)(l':=l1)(ps':=ps1)(cs':=cs1)(tmn':=tmn1)(la:=la)(lb:=lb); auto.
    rewrite <- trace_app_commute.
    apply seop_dbCmds__llvmop_dbop with (fs:=fs)(Ps:=Ps)(F:=fdef_intro (fheader_intro rt fid la) lb)(B:=block_intro l2 ps2 (cs21++cs22) (insn_return_void rid))(ECs:=ECs)(arg:=(params2GVs TD lp lc gl))(S:=S)(cs':=nil)(tmn:=insn_return_void rid) in d1.
    simpl_env in d1. 
    apply dbop_trans with (state2:=mkState S TD Ps (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l2 ps2 (cs21++cs22) (insn_return_void rid)) (cs21++cs22) (insn_return_void rid) lc1 (params2GVs TD lp lc gl) als1::ECs) gl fs Mem1); auto.
    apply dbop_trans with (state2:=mkState S TD Ps (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l2 ps2 (cs21++cs22) (insn_return_void rid)) cs22 (insn_return_void rid) lc2 (params2GVs TD lp lc gl) als2::ECs) gl fs Mem2); auto.
Qed.

Lemma seop_dbCall__llvmop_dbCall : forall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr F B ECs arg tmn cs als,
  SimpleSE.dbCall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr ->
  LLVMopsem.dbInsn 
    (mkState S TD Ps ((mkEC F B (call0::cs) tmn lc arg als)::ECs) gl fs Mem0)
    (mkState S TD Ps ((mkEC F B cs tmn lc' arg als)::ECs) gl fs Mem')
    tr.
Proof.
  intros.
  destruct seop__llvmop as [J _]. 
  apply J; auto.
Qed.

Lemma seop_dbSubblock__llvmop_dbop : forall S TD Ps fs gl lc als Mem cs lc' als' Mem' tr F B ECs arg tmn cs',
  SimpleSE.dbSubblock S TD Ps fs gl lc als Mem cs lc' als' Mem' tr ->
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F B (cs++cs') tmn lc arg als)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC F B cs' tmn lc' arg als')::ECs) gl fs Mem')
    tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [J _]]. 
  apply J; auto.
Qed.

Lemma seop_dbSubblocks__llvmop_dbop : forall S TD Ps fs gl lc als Mem cs lc' als' Mem' tr F B ECs arg tmn cs',
  SimpleSE.dbSubblocks S TD Ps fs gl lc als Mem cs lc' als' Mem' tr ->
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F B (cs++cs') tmn lc arg als)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC F B cs' tmn lc' arg als')::ECs) gl fs Mem')
    tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [_ [J _]]]. 
  apply J; auto.
Qed.

Lemma seop_dbBlock__llvmop_dbop :  forall S TD Ps fs gl F arg tr l ps cs tmn lc als Mem l' ps' cs' tmn' lc' als' Mem' ECs,
  SimpleSE.dbBlock S TD Ps fs gl F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem) 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' als') Mem')
    tr ->
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F (block_intro l ps cs tmn) cs tmn lc arg als)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' arg als')::ECs) gl fs Mem')
    tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [_ [_ [J _]]]]. 
  unfold seop_dbBlock__llvmop_dbop_prop in J.
  eapply J; eauto.
Qed.

Lemma seop_dbBlocks__llvmop_dbop : forall S TD Ps fs gl F arg tr l ps cs tmn lc als Mem l' ps' cs' tmn' lc' als' Mem' ECs,
  SimpleSE.dbBlocks S TD Ps fs gl F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem) 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' als') Mem')
    tr ->  
  LLVMopsem.dbop 
    (mkState S TD Ps ((mkEC F (block_intro l ps cs tmn) cs tmn lc arg als)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' arg als')::ECs) gl fs Mem')
    tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [_ [_ [_ [J _]]]]]. 
  unfold seop_dbBlocks__llvmop_dbop_prop in J.
  eapply J; eauto.
Qed.

Lemma seop_dbFdef__llvmop_dbFdef : forall fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ECs,
  SimpleSE.dbFdef fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ->
  LLVMopsem.dbFdef fid rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' B' Rid oResult tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [_ [_ [_ [_ J]]]]]. 
  eapply J; eauto.
Qed.

(****************************************************)
(* llvmop -> seop *)

Lemma dbBlock__dbBlocks : forall S TD Ps fs gl F arg state state' tr,
  SimpleSE.dbBlock S TD Ps fs gl F arg state state' tr -> 
  SimpleSE.dbBlocks S TD Ps fs gl F arg state state' tr.
Proof.
  intros S TD Ps fs gl F arg0 state state' tr H.
  rewrite <- trace_app_nil__eq__trace.
  eapply SimpleSE.dbBlocks_cons; eauto.
Qed.

Lemma dbTerminator__dbBlock : forall TD F fs gl lc tmn l ps B' lc' tr als Ps S arg Mem,
  SimpleSE.dbTerminator TD F gl (block_intro l ps nil tmn) lc tmn B' lc' tr ->
  SimpleSE.dbBlock S TD Ps fs gl F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps nil tmn) lc als) Mem)
    (SimpleSE.mkState (SimpleSE.mkEC B' lc' als) Mem)
    tr.
Proof.
  intros TD F fs gl lc tmn l0 ps B' lc' tr als Ps S arg0 Mem0 H.
  rewrite <- nil_app_trace__eq__trace.
  rewrite <- nil_app_trace__eq__trace with (tr:=trace_nil).
  assert (@nil cmd=nil++nil) as EQ. auto.
  rewrite EQ.
  apply SimpleSE.dbBlock_intro with (lc2:=lc)(als2:=als)(Mem2:=Mem0)(lc3:=lc); auto.
Qed.

Lemma dbCmd_dbSubblock__dbSubblock : forall S TD Ps lc als gl fs Mem0 c lc1 als1 Mem1 tr1 cs lc2 als2 Mem2 tr2,
  SimpleSE.dbCmd TD gl lc als Mem0 c lc1 als1 Mem1 tr1 ->
  SimpleSE.dbSubblock S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr2 ->
  SimpleSE.dbSubblock S TD Ps fs gl lc als Mem0 (c::cs) lc2 als2 Mem2 (trace_app tr1 tr2).
Proof.
  intros S TD Ps lc als gl fs Mem0 c lc1 als1 Mem1 tr1 cs lc2 als2 Mem2 tr2 H1 H2.
  inversion H2; subst.  
  rewrite trace_app_commute.
  assert (c::cs0++call0::nil = (c::cs0)++call0::nil) as EQ. auto.
  rewrite EQ.
  eapply SimpleSE.dbSubblock_intro; eauto.
Qed.

Lemma dbCmd_dbSubblocks__dbCmd_or_dbSubblocks : forall S TD Ps lc als gl fs Mem0 c lc1 als1 Mem1 tr1 cs lc2 als2 Mem2 tr2,
  SimpleSE.dbCmd TD gl lc als Mem0 c lc1 als1 Mem1 tr1 ->
  SimpleSE.dbSubblocks S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr2 ->
  (SimpleSE.dbCmd TD gl lc als Mem0 c lc2 als2 Mem2 tr1 /\ 
   cs = nil /\ tr2 = trace_nil /\ 
   lc1 = lc2 /\ als1 = als2 /\ Mem1 = Mem2 
  ) \/
  (SimpleSE.dbSubblocks S TD Ps fs gl lc als Mem0 (c::cs) lc2 als2 Mem2 (trace_app tr1 tr2)).
Proof.
  intros S TD Ps lc als gl fs Mem0 c lc1 als1 Mem1 tr1 cs lc2 als2 Mem2 tr2 H1 H2.
  inversion H2; subst.
    left. repeat (split; auto).
    right. 
      rewrite trace_app_commute.
      assert (c::cs0++cs'=(c::cs0)++cs') as EQ. auto.
      rewrite EQ.
      eapply SimpleSE.dbSubblocks_cons; eauto using dbCmd_dbSubblock__dbSubblock.
Qed.

Lemma dbTerminator_eqlabel : forall TD F gl l1 ps1 cs1 tmn1 lc1 B lc2 tr cs2,
  SimpleSE.dbTerminator TD F gl (block_intro l1 ps1 cs1 tmn1) lc1 tmn1 B lc2 tr ->
  SimpleSE.dbTerminator TD F gl (block_intro l1 ps1 cs2 tmn1) lc1 tmn1 B lc2 tr.
Proof.
  intros.
  inversion H; subst; eauto using switchToNewBasicBlock_eq.
Qed.

Lemma dbCmd_dbBlock__dbBlock : forall S TD Ps fs lc als gl Mem0 c lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 
  l1 ps1 cs1 tmn1 B F arg,
  SimpleSE.dbCmd TD gl lc als Mem0 c lc1 als1 Mem1 tr1 ->
  SimpleSE.dbBlock S TD Ps fs gl F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs1 tmn1) lc1 als1) Mem1)
    (SimpleSE.mkState (SimpleSE.mkEC B lc2 als2) Mem2)
    tr2 ->
  SimpleSE.dbBlock S TD Ps fs gl F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 (c::cs1) tmn1) lc als) Mem0)
    (SimpleSE.mkState (SimpleSE.mkEC B lc2 als2) Mem2)
    (trace_app tr1 tr2).
Proof.
  intros S TD Ps fs lc als gl Mem0 c lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 
    l1 ps1 cs1 tmn1 B F arg0 H1 H2.
  inversion H2; subst.  
  rewrite trace_app_commute.
  rewrite trace_app_commute.
  apply dbCmd_dbSubblocks__dbCmd_or_dbSubblocks with (lc:=lc)(als:=als)(gl:=gl)(Mem0:=Mem0)(c:=c)(tr1:=tr1) in H20; auto.
  destruct H20 as [[J11 [EQ [EQ' [EQ1 [EQ2 EQ3]]]]] | J11]; subst.
    assert (c::nil++cs'=nil++c::cs') as EQ. auto.
    rewrite EQ. clear EQ.
    rewrite trace_app_nil__eq__trace.
    rewrite <- nil_app_trace__eq__trace.
    rewrite trace_app_commute.
    eapply SimpleSE.dbBlock_intro; eauto using dbTerminator_eqlabel.

    assert (c::cs++cs'=(c::cs)++cs') as EQ. auto.
    rewrite EQ. clear EQ.
    eapply SimpleSE.dbBlock_intro; eauto using dbTerminator_eqlabel.
Qed.


Lemma dbCmd_dbBlocks__dbCmd_or_dbBlocks : forall S TD Ps fs lc als gl Mem0 c lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 
  l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2 F arg,
  SimpleSE.dbCmd TD gl lc als Mem0 c lc1 als1 Mem1 tr1 ->
  SimpleSE.dbBlocks S TD Ps fs gl F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs1 tmn1) lc1 als1) Mem1)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l2 ps2 cs2 tmn2) lc2 als2) Mem2)
    tr2 ->
  (SimpleSE.dbCmd TD gl lc als Mem0 c lc2 als2 Mem2 tr1 /\ 
   cs1 = cs2 /\ tr2 = trace_nil /\ 
   lc1 = lc2 /\ als1 = als2 /\ Mem1 = Mem2 /\
   l1 = l2 /\ ps1 = ps2 /\ tmn1 = tmn2
  ) \/
  (SimpleSE.dbBlocks S TD Ps fs gl F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 (c::cs1) tmn1) lc als) Mem0)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l2 ps2 cs2 tmn2) lc2 als2) Mem2)
    (trace_app tr1 tr2)).
Proof.
  intros S TD Ps fs lc als gl Mem0 c lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 
    l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2 F arg0 H1 H2.
  inversion H2; subst.
    left. repeat (split; auto).
    right. 
      rewrite trace_app_commute.
      inversion H; subst.
      eapply SimpleSE.dbBlocks_cons; eauto using dbCmd_dbBlock__dbBlock.
Qed.


Lemma dbCall__dbSubblock : forall S TD Ps fs lc gl Mem c lc' Mem' tr als,
  SimpleSE.dbCall S TD Ps fs gl lc Mem c lc' Mem' tr ->
  SimpleSE.dbSubblock S TD Ps fs gl
    lc als Mem
    (c::nil)
    lc' als Mem'
    tr.
Proof.
  intros S TD Ps fs lc gl Mem0 c lc' Mem' tr als H.
  rewrite <- nil_app_trace__eq__trace.
  assert (c::nil=nil++c::nil) as EQ. auto.
  rewrite EQ.
  apply SimpleSE.dbSubblock_intro with (lc2:=lc)(Mem2:=Mem0); auto.
Qed.

Lemma dbCall_isCallInst : forall S TD Ps fs lc gl Mem c lc' Mem' tr,
  SimpleSE.dbCall S TD Ps fs gl lc Mem c lc' Mem' tr ->
  Instruction.isCallInst c = true.
Proof.
  intros S TD Ps lc fs gl Mem0 c lc' Mem' tr HdbCall.
  induction HdbCall; auto.
Qed.

Lemma dbSubblock_dbBlock__dbBlock : forall S TD Ps fs lc als gl Mem0 cs lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 
  l1 ps1 cs1 tmn1 B F arg,
  SimpleSE.dbSubblock S TD Ps fs gl lc als Mem0 cs lc1 als1 Mem1 tr1 ->
  SimpleSE.dbBlock S TD Ps fs gl F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs1 tmn1) lc1 als1) Mem1)
    (SimpleSE.mkState (SimpleSE.mkEC B lc2 als2) Mem2)
    tr2 ->
  SimpleSE.dbBlock S TD Ps fs gl F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 (cs++cs1) tmn1) lc als) Mem0)
    (SimpleSE.mkState (SimpleSE.mkEC B lc2 als2) Mem2)
    (trace_app tr1 tr2).
Proof.
  intros S TD Ps fs lc als gl Mem0 cs lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 
    l1 ps1 cs1 tmn1 B F arg0 H1 H2.
  inversion H2; subst.  
  rewrite trace_app_commute.
  rewrite trace_app_commute.
  rewrite <- app_ass.
  eapply SimpleSE.dbBlock_intro; eauto using dbTerminator_eqlabel.
Qed.

Lemma dbSubblock_dbBlocks__dbSubblock_or_dbBlocks : forall S TD Ps fs lc als gl Mem0 cs lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 
  l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2 F arg,
  SimpleSE.dbSubblock S TD Ps fs gl lc als Mem0 cs lc1 als1 Mem1 tr1 ->
  SimpleSE.dbBlocks S TD Ps fs gl F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs1 tmn1) lc1 als1) Mem1)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l2 ps2 cs2 tmn2) lc2 als2) Mem2)
    tr2 ->
  (  SimpleSE.dbSubblock S TD Ps fs gl lc als Mem0 cs lc1 als1 Mem1 tr1 /\ 
   cs1 = cs2 /\ tr2 = trace_nil /\ 
   lc1 = lc2 /\ als1 = als2 /\ Mem1 = Mem2 /\
   l1 = l2 /\ ps1 = ps2 /\ tmn1 = tmn2
  ) \/
  (SimpleSE.dbBlocks S TD Ps fs gl F arg 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 (cs++cs1) tmn1) lc als) Mem0)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l2 ps2 cs2 tmn2) lc2 als2) Mem2)
    (trace_app tr1 tr2)).
Proof.
  intros S TD Ps fs lc als gl Mem0 cs lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 
    l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2 F arg0 H1 H2.
  inversion H2; subst.
    left. repeat (split; auto).
    right. 
      rewrite trace_app_commute.
      inversion H; subst.
      eapply SimpleSE.dbBlocks_cons; eauto using dbSubblock_dbBlock__dbBlock.
Qed.


Definition llvmop_dbInsn__seop_prop state1 state2 tr
  (db:LLVMopsem.dbInsn state1 state2 tr) :=
  forall S los nts Ps F l ps cs tmn lc arg als ECs gl fs Mem cs0,
  state1 = (mkState S (los, nts) Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl fs Mem) ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps) F ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists Mem', exists cs0',
  state2 = (mkState S (los, nts) Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl fs Mem') /\
  ((cs = nil /\ Mem = Mem' /\ als = als' /\ cs' = cs0' /\
              SimpleSE.dbTerminator (los, nts) F gl
                 (block_intro l ps cs tmn) lc
                 tmn 
                 (block_intro l' ps' cs' tmn') lc' 
                 tr ) \/ 
  (exists c, c::cs' = cs /\ SimpleSE.dbCmd (los, nts) gl lc als Mem c lc' als' Mem' tr) \/
  (exists c, c::cs' = cs /\ SimpleSE.dbCall S (los, nts) Ps fs gl lc Mem c lc' Mem' tr)).
Definition llvmop_dbop__seop_prop state1 state2 tr
  (db:LLVMopsem.dbop state1 state2 tr) :=
  forall S los nts Ps F l ps cs tmn lc arg als ECs gl fs Mem l' ps' cs' tmn' lc' als' gl' fs' Mem' cs0 cs0',
  state1 = (mkState S (los, nts) Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl fs Mem) ->
  state2 = (mkState S (los, nts) Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' fs' Mem') ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps) F ->
  (exists cs1, exists cs2, 
  exists tr1, exists tr2,
  exists lc1, exists als1, exists Mem1,
    trace_app tr1 tr2 = tr /\  
    l = l' /\
    ps = ps' /\
    cs0 = cs0' /\
    tmn = tmn' /\
    cs = cs1++cs2++cs' /\
    SimpleSE.dbSubblocks S (los, nts) Ps fs gl
      lc als Mem
      cs1
      lc1 als1 Mem1
      tr1 /\
    SimpleSE.dbCmds (los, nts) gl
      lc1 als1 Mem1
      cs2
      lc' als' Mem'
      tr2) \/
  (exists cs1, exists cs2, 
  exists tr1, exists tr2, exists tr3,
  exists lc1, exists als1, exists Mem1,
  exists lc2, exists als2,  exists Mem2,
    cs1++cs2++cs'=cs0' /\
    (trace_app (trace_app tr1 tr2) tr3) = tr /\
    SimpleSE.dbBlocks S (los, nts) Ps fs gl F arg 
      (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem) 
      (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs0' tmn') lc1 als1) Mem1)
      tr1 /\
    SimpleSE.dbSubblocks S (los, nts) Ps fs gl
      lc1 als1 Mem1
      cs1
      lc2 als2 Mem2
      tr2 /\
    SimpleSE.dbCmds (los, nts) gl
      lc2 als2 Mem2
      cs2
      lc' als' Mem'
      tr3).
Definition llvmop_dbFdef__seop_dbFdef_prop fid rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' B' Rid oResult tr
  (db:LLVMopsem.dbFdef fid rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' B' Rid oResult tr) :=
  forall los nts,
  TD = (los, nts) ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  SimpleSE.dbFdef fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr.

Lemma llvmop__seop : 
  (forall state1 state2 tr db, @llvmop_dbInsn__seop_prop state1 state2 tr db) /\
  (forall state1 state2 tr db, @llvmop_dbop__seop_prop state1 state2 tr  db) /\
  (forall fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ECs db, 
    @llvmop_dbFdef__seop_dbFdef_prop fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ECs db).
Proof.
(db_mutind_cases
  apply LLVMopsem.db_mutind with
    (P  := llvmop_dbInsn__seop_prop)
    (P0 := llvmop_dbop__seop_prop)
    (P1 := llvmop_dbFdef__seop_dbFdef_prop) Case);
  unfold llvmop_dbInsn__seop_prop, 
         llvmop_dbop__seop_prop, 
         llvmop_dbFdef__seop_dbFdef_prop; intros; subst.
Case "dbBranch".
  inversion H; subst. clear H.
  exists l'. exists ps'. exists cs'. exists tmn'.
  exists (switchToNewBasicBlock (los, nts) (block_intro l' ps' cs' tmn') (block_intro l0 ps cs0 (insn_br bid Cond l1 l2)) gl0 lc0). 
  exists als0. exists Mem1.
  exists cs'. split; auto.
  left. 
  split; auto.
  split; auto.
  split; auto.
  split; auto.
    apply SimpleSE.dbBranch with (c:=c); auto using switchToNewBasicBlock_eq.

Case "dbBranch_uncond".
  inversion H; subst. clear H.
  exists l'. exists ps'. exists cs'. exists tmn'.
  exists (switchToNewBasicBlock (los, nts) (block_intro l' ps' cs' tmn') (block_intro l1 ps cs0 (insn_br_uncond bid l0)) gl0 lc0). 
  exists als0. exists Mem1.
  exists cs'. split; auto.
  left.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
    apply SimpleSE.dbBranch_uncond; auto using switchToNewBasicBlock_eq.

Case "dbBop".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_bop id0 bop0 sz0 v1 v2).
  split; eauto.

Case "dbFBop".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_fbop id0 fbop0 fp v1 v2).
  split; eauto.

Case "dbExtractValue".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv'). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_extractvalue id0 t v idxs).
  split; eauto.

Case "dbInsertValue".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv''). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_insertvalue id0 t v t' v' idxs).
  split; eauto.

Case "dbMalloc".
  inversion H; subst. clear H. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 (blk2GV (los, nts) mb)). exists als0. exists Mem'.
  exists cs1. split; auto.
  right. left.
  exists (insn_malloc id0 t v align0).
  split; eauto.

Case "dbFree".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists Mem'.
  exists cs1. split; auto.
  right. left.
  exists (insn_free fid t v).
  split; eauto.

Case "dbAlloca".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 (blk2GV (los, nts) mb)). exists (mb::als0). exists Mem'.
  exists cs1. split; auto.
  right. left.
  exists (insn_alloca id0 t v align0).
  split; eauto.

Case "dbLoad".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_load id0 t v align0).
  split; eauto.

Case "dbStore".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists Mem'.
  exists cs1. split; auto.
  right. left.
  exists (insn_store sid t v1 v2 align0).
  split; eauto.

Case "dbGEP".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 mp'). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_gep id0 inbounds0 t v idxs).
  split; eauto.

Case "dbTrunc".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv2). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_trunc id0 truncop0 t1 v1 t2).
  split; eauto.

Case "dbExt".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv2). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_ext id0 extop0 t1 v1 t2).
  split; eauto.

Case "dbCast".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv2). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_cast id0 castop0 t1 v1 t2).
  split; eauto.

Case "dbIcmp".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_icmp id0 cond0 t v1 v2).
  split; eauto.

Case "dbFcmp".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_fcmp id0 fcond0 fp v1 v2).
  split; eauto.

Case "dbSelect".
  inversion H; subst. clear H.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (if isGVZero (los, nts) c then updateAddAL _ lc0 id0 gv2 else updateAddAL _ lc0 id0 gv1). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_select id0 v0 t v1 v2).
  split; eauto.

Case "dbCall".
  inversion H0; subst. clear H0.
  apply blockInSystemModuleFdef_inv in H2.
  destruct H2 as [J1 [J2 [J3 _]]].
  exists l0. exists ps. exists cs. exists tmn0.
  exists (callUpdateLocals (los, nts) noret0 rid rt oResult lc0 lc' gl0). exists als0. exists Mem''.
  exists cs1. split; auto.
  destruct (SimpleSE.isCall_dec (insn_call rid noret0 tailc0 rt fv lp)) 
    as [isCall_false | isCall_true].
    (* 
      Like subAL_callUpdateLocals, we should prove that
        if oResult is Some v, callUpdate = exCallupdate, which means that 
           if v is id, the id must be defined ! 
        if oResult is None, they are obviously equivalent. 
     *)
    assert (exists oresult, exCallUpdateLocals noret0 rid rt oresult lc0 =
      callUpdateLocals (los, nts) noret0 rid rt oResult lc0 lc' gl0) as EQ. admit.
    destruct EQ as [oresult EQ].
    right. left.
    exists (insn_call rid noret0 tailc0 rt fv lp).
    rewrite <- EQ.
    (* The axiom callLib should also specify trace. *)
    assert (tr = trace_nil) as EQ'. admit.
    subst.
    simpl in isCall_false. 
    destruct fv as [fid | cn]; try solve [inversion isCall_false].
    split; eauto.
      apply SimpleSE.dbLib.
      eapply SimpleSE.callLib__is__correct with (noret:=noret0) (rid:=rid) (rt:=rt).
        eapply negb_false_iff; auto.
        erewrite EQ. eauto.

    right. right.
    exists (insn_call rid noret0 tailc0 rt fv lp).
    split; eauto.

Case "dbExCall".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (exCallUpdateLocals noret0 rid rt oresult lc0). exists als0. exists Mem'.
  exists cs1. split; auto.
  destruct (SimpleSE.isCall_dec (insn_call rid noret0 tailc0 rt fv lp)) 
    as [isCall_false | isCall_true].
    right. left.
    exists (insn_call rid noret0 tailc0 rt fv lp).
    simpl in isCall_false. 
    destruct fv as [fid0 | cn]; try solve [inversion isCall_false].
    split; eauto.
      apply SimpleSE.dbLib.
      apply negb_false_iff in isCall_false.
      apply SimpleSE.callLib__is__correct with (noret:=noret0) (rid:=rid) (rt:=rt)
        (S:=S0)(TD:=(los,nts))(Ps:=Ps0)(cs:=cs)(tmn:=tmn0)(arg:=arg1)(als:=als0)
        (F:=F0)(B:=block_intro l0 ps cs1 tmn0)(fs:=fs0)(ECs:=ECs) (Mem:=Mem1) (lp:=lp)
        (lc:=lc0)(gl:=gl0)(oresult:=oresult)(Mem':=Mem')(tailc:=tailc0) in isCall_false.
      eapply isCall_false.
        apply LLVMopsem.dbExCall with (fid:=fid)(la:=la); auto.

  right. right.
  exists (insn_call rid noret0 tailc0 rt fv lp).
  split; eauto.

Case "dbop_nil".
  inversion H0; subst. clear H0. 
  left.
  exists nil. exists nil.
  exists trace_nil. exists trace_nil.
  exists lc'. exists als'. exists Mem'.
  repeat (split; auto).
  
Case "dbop_cons".
  destruct (@H S los nts Ps F l0 ps cs tmn lc arg0 als ECs gl fs Mem0 cs0)
    as [l1 [ps1 [cs1 [tmn1 [lc1 [als1 [Mem1 [cs2 [J1 J2]]]]]]]]]; subst; auto.
  clear H.
  assert (mkState S (los, nts) Ps (mkEC F (block_intro l1 ps1 cs2 tmn1) cs1 tmn1 lc1 arg0 als1::ECs) gl fs Mem1 =
          mkState S (los, nts) Ps (mkEC F (block_intro l1 ps1 cs2 tmn1) cs1 tmn1 lc1 arg0 als1::ECs) gl fs Mem1) as J'. auto.
  assert (d':=d).
  apply dbInsn_preservation in d'; auto.
  apply H0 with (fs'0:=fs')(l'0:=l')(ps'0:=ps')(cs'0:=cs')(tmn'0:=tmn')(lc'0:=lc')(als'0:=als')(gl'0:=gl')(Mem'0:=Mem')(cs0'0:=cs0') in J'; auto.
  clear H0.
  destruct J2 as [[EQ [EQ' [EQ1 [EQ2 J2]]]] | [[c [EQ J2]] | [c [EQ J2]]]]; subst.
  SCase "dbTerminator".
    destruct J' as [
                     [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12]]]]]]]]]]]]]] | 
                     [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [Mem2 [lc3 [als3 [Mem3 [EQ1 [EQ2 [J21 [J22 J23]]]]]]]]]]]]]]]
                   ]; subst.
    SSCase "one block".
      subst.
      right.
      exists cs3. exists cs4.
      exists t1. exists tr1. exists tr2.
      exists lc1. exists als1. exists Mem1.
      exists lc2. exists als2. exists Mem2.
      rewrite trace_app_commute.
      repeat (split; auto).
        apply dbBlock__dbBlocks; auto using dbTerminator__dbBlock.

    SSCase "multi block".
      right.
      exists cs3. exists cs4.
      exists (trace_app t1 tr1). exists tr2. exists tr3.
      exists lc2. exists als2. exists Mem2.
      exists lc3. exists als3. exists Mem3.
      rewrite trace_app_commute.
      rewrite trace_app_commute.
      repeat (split; auto).
        apply SimpleSE.dbBlocks_cons with (S2:=SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs2 tmn1) lc1 als1) Mem1); 
          auto using dbTerminator__dbBlock.
  SCase "dbCmd".
    apply dbInsn__inv in d.
    destruct d as [_ [_ [_ [_ [EQ5 [EQ6 [EQ7 [EQ8 _]]]]]]]]; subst.
    destruct J' as [
                     [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12]]]]]]]]]]]]]] | 
                     [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [Mem2 [lc3 [als3 [Mem3 [EQ1 [EQ2 [J21 [J22 J23]]]]]]]]]]]]]]]
                   ]; subst.
    SSCase "one block".
      left.
      apply dbCmd_dbSubblocks__dbCmd_or_dbSubblocks with (lc:=lc)(als:=als)(gl:=gl)(Mem0:=Mem0)(c:=c)(tr1:=t1) in J11; auto.
      destruct J11 as [[J11 [EQ [EQ' [EQ1 [EQ2 EQ3]]]]] | J11]; subst.
        exists nil. exists (c::cs4).
        exists trace_nil. exists (trace_app t1 tr2).
        exists lc. exists als. exists Mem0.
        rewrite nil_app_trace__eq__trace.
        rewrite nil_app_trace__eq__trace.
        repeat (split; eauto). 

        exists (c::cs3). exists cs4.
        exists (trace_app t1 tr1). exists tr2.
        exists lc2. exists als2. exists Mem2.
        rewrite trace_app_commute. simpl_env in *.
        repeat (split; auto).
    
    SSCase "multi block".
      apply dbCmd_dbBlocks__dbCmd_or_dbBlocks with (lc:=lc)(als:=als)(gl:=gl)(Mem0:=Mem0)(c:=c)(tr1:=t1) in J21; auto.
      destruct J21 as [[J21 [EQ [EQ' [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]] | J21]; subst.
        apply dbCmd_dbSubblocks__dbCmd_or_dbSubblocks with (lc:=lc)(als:=als)(gl:=gl)(Mem0:=Mem0)(c:=c)(tr1:=t1) in J22; auto.
        assert (cs2=cs3++cs4++cs') as EQcs.
          apply dbop_preservation in d0; auto.
          assert (uniqFdef F) as UniqF.
            apply blockInSystemModuleFdef_inv in H4.
            destruct H4 as [_ [_ [_ H4]]].
            apply uniqSystem__uniqFdef in H4; auto.
          apply blockInSystemModuleFdef_uniq with (ps1:=ps')(cs1:=cs2)(tmn1:=tmn') in d0; auto.
          destruct d0 as [EQ1 [EQ2 EQ3]]; subst; auto.
        subst.
        destruct J22 as [[J22 [EQ [EQ' [EQ1 [EQ2 EQ3]]]]] | J22]; subst.
          left. 
          exists nil. exists (c::cs4).
          exists trace_nil. exists (trace_app t1 tr3).
          exists lc. exists als. exists Mem0.
          rewrite nil_app_trace__eq__trace.
          rewrite nil_app_trace__eq__trace.
          repeat (split; eauto).

          left.
          exists (c::cs3). exists cs4.
          exists (trace_app t1 tr2). exists tr3.
          exists lc3. exists als3. exists Mem3.
          rewrite nil_app_trace__eq__trace.
          rewrite trace_app_commute.
          repeat (split; eauto).
        
        right.
        exists cs3. exists cs4.
        exists (trace_app t1 tr1). exists tr2. exists tr3.
        exists lc2. exists als2. exists Mem2.
        exists lc3. exists als3. exists Mem3.
        rewrite trace_app_commute.
        rewrite trace_app_commute.
        repeat (split; eauto).

  SCase "dbCall".
    assert (J:=J2).
    apply dbCall_isCallInst in J.
    apply dbCall__dbSubblock with (als:=als1) in J2.
    apply dbInsn_Call__inv in d; auto.
    destruct d as [_ [_ [_ [_ [EQ5 [EQ6 [EQ7 [EQ8 [_ [_ [_ EQ9]]]]]]]]]]]; subst.
    destruct J' as [
                     [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12]]]]]]]]]]]]]] | 
                     [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [Mem2 [lc3 [als3 [Mem3 [EQ1 [EQ2 [J21 [J22 J23]]]]]]]]]]]]]]]
                   ]; subst.
    SSCase "one block".
      left.
      exists (c::cs3). exists cs4.
      exists (trace_app t1 tr1). exists tr2.
      exists lc2. exists als2. exists Mem2.
      rewrite trace_app_commute. simpl_env in *.
      repeat (split; eauto).

    SSCase "multi block".
      apply dbSubblock_dbBlocks__dbSubblock_or_dbBlocks with (lc:=lc)(als:=als1)(gl:=gl)(Mem0:=Mem0)(cs:=c::nil)(tr1:=t1) in J21; auto.
      destruct J21 as [[J21 [EQ [EQ' [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]] | J21]; subst.
        left. 
        exists (c::cs3). exists cs4.
        exists (trace_app t1 tr2). exists tr3.
        exists lc3. exists als3. exists Mem3.
        rewrite nil_app_trace__eq__trace.
        assert (cs2=cs3++cs4++cs') as EQcs.        
          apply dbop_preservation in d0; auto.
          assert (uniqFdef F) as UniqF.
            apply blockInSystemModuleFdef_inv in H4.
            destruct H4 as [_ [_ [_ H4]]].
            apply uniqSystem__uniqFdef in H4; auto.
          apply blockInSystemModuleFdef_uniq with (ps1:=ps')(cs1:=cs2)(tmn1:=tmn') in d0; auto.
          destruct d0 as [EQ1 [EQ2 EQ3]]; subst; auto.
        subst.
        rewrite trace_app_commute. simpl_env in *.
        repeat (split; eauto).
      
        right.
        exists cs3. exists cs4.
        exists (trace_app t1 tr1). exists tr2. exists tr3.
        exists lc2. exists als2. exists Mem2.
        exists lc3. exists als3. exists Mem3.
        rewrite trace_app_commute.
        rewrite trace_app_commute.
        repeat (split; eauto).     

Case "dbFdef_func".
  assert (mkState S (los, nts) Ps 
           (mkEC 
             (fdef_intro (fheader_intro rt fid la) lb) (block_intro l' ps' cs' tmn') cs' tmn' 
             (initLocals la (params2GVs (los, nts) lp lc gl)) 
             (params2GVs (los, nts) lp lc gl) nil::ECs) gl fs Mem0 =
          mkState S (los, nts) Ps 
           (mkEC 
             (fdef_intro (fheader_intro rt fid la) lb) (block_intro l' ps' cs' tmn') cs' tmn' 
             (initLocals la (params2GVs (los, nts) lp lc gl)) 
             (params2GVs (los, nts) lp lc gl) nil::ECs) gl fs Mem0) as J. auto.
  apply H with (l'0:=l'')(ps'0:=ps'')(cs'0:=nil)(tmn'0:=insn_return rid rt Result)(lc'0:=lc')(als'0:=als')(gl':=gl)(fs':=fs)(Mem'0:=Mem')(cs0':=cs'') in J; 
    eauto using entryBlockInSystemBlockFdef'.
  clear H d.
  destruct J as [
                 [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12]]]]]]]]]]]]]] | 
                 [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [Mem2 [lc3 [als3 [Mem3 [EQ1 [EQ2 [J21 [J22 J23]]]]]]]]]]]]]]]
                ]; subst.
  SCase "one block".
    simpl_env in EQ6. subst.
    rewrite <- nil_app_trace__eq__trace with (tr:=tr1).
    eapply SimpleSE.dbFdef_func; eauto.
  
  SCase "multi block".
    simpl_env in *.
    eapply SimpleSE.dbFdef_func; eauto.

Case "dbFdef_proc".
  assert (mkState S (los, nts) Ps 
           (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l' ps' cs' tmn') cs' tmn' 
                 (initLocals la (params2GVs (los, nts) lp lc gl)) 
                 (params2GVs (los, nts) lp lc gl) nil::ECs) gl fs Mem0 =
          mkState S (los, nts) Ps 
           (mkEC (fdef_intro (fheader_intro rt fid la) lb) (block_intro l' ps' cs' tmn') cs' tmn' 
                 (initLocals la (params2GVs (los, nts) lp lc gl)) 
                 (params2GVs (los, nts) lp lc gl) nil::ECs) gl fs Mem0) as J. auto.
  apply H with (l'0:=l'')(ps'0:=ps'')(cs'0:=nil)(tmn'0:=insn_return_void rid)(lc'0:=lc')(als'0:=als')(gl':=gl)(fs':=fs)(Mem'0:=Mem')(cs0':=cs'') in J;
    eauto using entryBlockInSystemBlockFdef'.
  clear H d.
  destruct J as [
                 [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12]]]]]]]]]]]]]] | 
                 [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [Mem2 [lc3 [als3 [Mem3 [EQ1 [EQ2 [J21 [J22 J23]]]]]]]]]]]]]]]
                ]; subst.
  SCase "one block".
    simpl_env in EQ6. subst.
    rewrite <- nil_app_trace__eq__trace with (tr:=tr1).
    eapply SimpleSE.dbFdef_proc; eauto.
  
  SCase "multi block".
    simpl_env in *.
    eapply SimpleSE.dbFdef_proc; eauto.
Qed.


Lemma llvmop_dbInsn__seop : forall state2 tr S los nts Ps F l ps cs tmn lc arg als ECs gl fs Mem cs0,
  LLVMopsem.dbInsn 
    (mkState S (los, nts) Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl fs Mem)  
    state2 
    tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps) F ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists Mem', exists cs0',
  state2 = (mkState S (los, nts) Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl fs Mem') /\
  ((cs = nil /\ Mem = Mem' /\ als = als' /\ cs' = cs0' /\
              SimpleSE.dbTerminator (los, nts) F gl
                 (block_intro l ps cs tmn) lc
                 tmn 
                 (block_intro l' ps' cs' tmn') lc' 
                 tr ) \/ 
  (exists c, c::cs' = cs /\ SimpleSE.dbCmd (los, nts) gl lc als Mem c lc' als' Mem' tr) \/
  (exists c, c::cs' = cs /\ SimpleSE.dbCall S (los, nts) Ps fs gl lc Mem c lc' Mem' tr)).
Proof.
  intros.
  destruct llvmop__seop as [J _]. 
  unfold llvmop_dbInsn__seop_prop in J.
  eapply J; eauto.
Qed.

Lemma llvmop_dbop__seop : forall tr S los nts Ps F l ps cs tmn lc arg als ECs gl fs Mem l' ps' cs' tmn' lc' als' gl' fs' Mem' cs0 cs0',
  LLVMopsem.dbop 
    (mkState S (los, nts) Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc arg als)::ECs) gl fs Mem)
    (mkState S (los, nts) Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' arg als')::ECs) gl' fs' Mem')
    tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps) F ->
  (exists cs1, exists cs2, 
  exists tr1, exists tr2,
  exists lc1, exists als1, exists Mem1,
    trace_app tr1 tr2 = tr /\  
    l = l' /\
    ps = ps' /\
    cs0 = cs0' /\
    tmn = tmn' /\
    cs = cs1++cs2++cs' /\
    SimpleSE.dbSubblocks S (los, nts) Ps fs gl
      lc als Mem
      cs1
      lc1 als1 Mem1
      tr1 /\
    SimpleSE.dbCmds (los, nts) gl
      lc1 als1 Mem1
      cs2
      lc' als' Mem'
      tr2) \/
  (exists cs1, exists cs2, 
  exists tr1, exists tr2, exists tr3,
  exists lc1, exists als1, exists Mem1,
  exists lc2, exists als2, exists Mem2,
    cs1++cs2++cs'=cs0' /\
    (trace_app (trace_app tr1 tr2) tr3) = tr /\
    SimpleSE.dbBlocks S (los, nts) Ps fs gl F arg 
      (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem) 
      (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs0' tmn') lc1 als1) Mem1)
      tr1 /\
    SimpleSE.dbSubblocks S (los, nts) Ps fs gl
      lc1 als1 Mem1
      cs1
      lc2 als2 Mem2
      tr2 /\
    SimpleSE.dbCmds (los, nts) gl
      lc2 als2 Mem2
      cs2
      lc' als' Mem'
      tr3).
Proof.
  intros.
  destruct llvmop__seop as [_ [J _]]. 
  unfold llvmop_dbop__seop_prop in J.
  eapply J; eauto.
Qed.

Lemma llvmop_dbFdef__seop_dbFdef : forall fid rt lp S los nts Ps ECs lc gl fs Mem lc' als' Mem' B' Rid oResult tr,
  LLVMopsem.dbFdef fid rt lp S (los, nts) Ps ECs lc gl fs Mem lc' als' Mem' B' Rid oResult tr ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  SimpleSE.dbFdef fid rt lp S (los, nts) Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr.
Proof.
  intros.
  destruct llvmop__seop as [_ [_ J]]. 
  unfold llvmop_dbFdef__seop_dbFdef_prop in J.
  eapply J; eauto.
Qed.



