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
Require Import symexe_def.
Require Import ssa_props.
Require Import assoclist.
Require Import sb_def.

Export LLVMsyntax.
Export LLVMlib.

Tactic Notation "sb_dbCmd_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBop" | c "dbBop_error" | c "dbFBop" | c "dbFBop_eror" |
    c "dbExtractValue" | c "dbExtractValue_error" | 
    c "dbInsertValue" | c "dbInsertValue_error" |
    c "dbMalloc" | c "dbMalloc_error" | c "dbFree" | c "dbFree_error" |
    c "dbAlloca" | c "dbAlloca_error" | 
    c "dbLoad_nptr" | c "dbLoad_ptr" | c "dbLoad_abort" |
    c "dbStore_nptr" | c "dbStore_ptr" | c "dbStore_abort" |  
    c "dbGEP" | c "dbGEP_error" |
    c "dbTrunc" | c "dbTrunc_error" |
    c "dbExt" | c "dbExt_error" |
    c "dbBitcast_nptr" | c "dbBitcast_ptr" | c "dbInttoptr" | c "dbOtherCast" |
    c "dbCast_error" | 
    c "dbIcmp" | c "dbIcmp_error" |
    c "dbFcmp" | c "dbFcmp_error" | 
    c "dbSelect_nptr" | c "dbSelect_ptr"| c "dbSelect_error" |
    c "dbLib" | c "dbLib_error" ].

Tactic Notation "sb_dbTerminator_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBranch" | c "dbBranch_uncond" ].

Tactic Notation "sb_dbCmds_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCmds_nil" | c "dbCmds_cons" | c "dbCmds_cons_error" ].

(****************************************************)
(* sbop -> seop *)

Ltac invert_prop_reg_metadata :=
  match goal with
  | [H : SoftBound.prop_reg_metadata _ _ _ _ _ = (_, _) |- _ ] =>
      inversion H; subst; eauto
  end.

Lemma updateAddAL_if_commut : forall lc id0 TD cond gv2 gv1,
  updateAddAL GenericValue lc id0 (if isGVZero TD cond then gv2 else gv1) =
  if isGVZero TD cond then 
    (updateAddAL GenericValue lc id0 gv2) else 
    (updateAddAL GenericValue lc id0 gv1).
Admitted.

Lemma sbop_dbCmd__seop_dbCmd : forall TD lc rm als gl Mem MM c lc' rm' als' 
    Mem' MM' tr r, 
  SoftBound.dbCmd TD gl lc rm als Mem MM c lc' rm' als' Mem' MM' tr r ->
  r = SoftBound.rok ->
  SimpleSE.dbCmd TD gl lc als Mem c lc' als' Mem' tr.
Proof.
  intros TD lc rm als gl Mem0 MM0 c lc' rm' als' Mem' MM' tr r H.
  (sb_dbCmd_cases (destruct H) Case); intro J; 
    try solve [inversion J; invert_prop_reg_metadata | eauto].
  Case "dbSelect_nptr".
    unfold SoftBound.SELECT in H.
    remember (getOperandValue TD Mem0 v0 lc gl) as R0.
    remember (getOperandValue TD Mem0 v1 lc gl) as R1.
    remember (getOperandValue TD Mem0 v2 lc gl) as R2.
    destruct R0 as [cond |]; try solve [inversion H].
    destruct R1 as [gv1 |]; try solve [inversion H].
    destruct R2 as [gv2 |]; inversion H; subst.
    rewrite updateAddAL_if_commut. eauto.

  Case "dbSelect_ptr".
    unfold SoftBound.SELECT in H.
    remember (getOperandValue TD Mem0 v0 lc gl) as R0.
    remember (getOperandValue TD Mem0 v1 lc gl) as R1.
    remember (getOperandValue TD Mem0 v2 lc gl) as R2.
    destruct R0 as [cond |]; try solve [inversion H].
    destruct R1 as [gv1 |]; try solve [inversion H].
    destruct R2 as [gv2 |]; inversion H; subst.
    inversion H3; subst.
    assert (lc'=if isGVZero TD cond0 then updateAddAL _ lc id0 gv2
                                     else updateAddAL _ lc id0 gv1) as EQ.
      remember (isGVZero TD cond0) as R3.
      destruct R3; inversion H4; subst; auto.
    rewrite EQ. eauto.
Qed.
  
Ltac invert_result :=
  match goal with
  | [H : SoftBound.is_error SoftBound.rok |- _ ] => inversion H
  | [H : SoftBound.rerror = SoftBound.rok |- _ ] => inversion H
  | [H : SoftBound.rabort = SoftBound.rok |- _ ] => inversion H 
  | [H : SoftBound.rok = SoftBound.rerror |- _ ] => inversion H 
  | [H : SoftBound.rok = SoftBound.rabort |- _ ] => inversion H 
 end.

Lemma sbop_dbCmds__seop_dbCmds : forall TD lc rm als gl Mem MM cs lc' rm' 
    als' Mem' MM' tr r,
  SoftBound.dbCmds TD gl lc rm als Mem MM cs lc' rm' als' Mem' MM' tr r ->
  r = SoftBound.rok ->
  SimpleSE.dbCmds TD gl lc als Mem cs lc' als' Mem' tr.
Proof.
  intros TD lc rm als gl Mem0 MM0 cs lc' rm' als' Mem' MM' tr r H.
  (sb_dbCmds_cases (induction H) Case); intros J; subst;
    try solve [invert_result | eauto using sbop_dbCmd__seop_dbCmd].
Qed.

Lemma sbop_callUpdateLocals__seop_callUpdateLocals : forall TD Mem'' noret0 rid 
  oResult rm rm' lc lc' gl lc'' rm'',
  SoftBound.callUpdateLocals TD Mem'' noret0 rid oResult rm rm' lc lc' gl = 
    ret (lc'', rm'') ->
  callUpdateLocals TD Mem'' noret0 rid oResult lc lc' gl = ret lc''.
Proof.
  intros. 
  unfold SoftBound.callUpdateLocals in H.
  unfold callUpdateLocals.
  destruct noret0; try solve [inversion H; subst; auto].
  destruct oResult; try solve [inversion H; subst; auto].
  destruct (getOperandValue TD Mem'' v lc' gl); 
    try solve [inversion H; subst; auto].
  destruct (SoftBound.get_reg_metadata TD Mem'' gl rm' v);
    try solve [inversion H; subst; auto].
Qed.

Definition sbop_dbCall__seop_dbCall_prop S TD Ps fs gl lc rm Mem0 MM0 call0 lc'
rm' Mem' MM' tr r 
(db:SoftBound.dbCall S TD Ps fs gl lc rm Mem0 MM0 call0 lc' rm' Mem' MM' tr r) :=
  r = SoftBound.rok ->
  SimpleSE.dbCall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr.

Definition sbop_dbSubblock__seop_dbSubblock_prop S TD Ps fs gl lc rm als Mem MM 
cs lc' rm' als' Mem' MM' tr r
(db:SoftBound.dbSubblock S TD Ps fs gl lc rm als Mem MM cs lc' rm' als' Mem' MM' 
    tr r) :=
  r = SoftBound.rok ->
  SimpleSE.dbSubblock S TD Ps fs gl lc als Mem cs lc' als' Mem' tr.

Definition sbop_dbSubblocks__seop_dbSubblocks_prop S TD Ps fs gl lc rm als Mem MM
cs lc' rm' als' Mem' MM' tr r 
(db:SoftBound.dbSubblocks S TD Ps fs gl lc rm als Mem MM cs lc' rm' als' Mem' MM'
  tr r) :=
  r = SoftBound.rok ->
  SimpleSE.dbSubblocks S TD Ps fs gl lc als Mem cs lc' als' Mem' tr.

Definition sbop_dbBlock__seop_dbBlock_prop S TD Ps fs gl F state state' tr r
  (db:SoftBound.dbBlock S TD Ps fs gl F state state' tr r) :=
  forall l ps cs tmn lc rm als Mem MM l' ps' cs' tmn' lc' rm' als' Mem' MM',
  r = SoftBound.rok ->
  state = SoftBound.mkState (SoftBound.mkEC (block_intro l ps cs tmn) lc rm als) 
    Mem MM ->
  state' = SoftBound.mkState (SoftBound.mkEC (block_intro l' ps' cs' tmn') lc' 
    rm' als') Mem' MM' ->
  SimpleSE.dbBlock S TD Ps fs gl F 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' 
    als') Mem') tr.

Definition sbop_dbBlocks__seop_dbBlocks_prop S TD Ps fs gl F state state' tr r
  (db:SoftBound.dbBlocks S TD Ps fs gl F state state' tr r) :=
  forall l ps cs tmn lc rm als Mem MM l' ps' cs' tmn' lc' rm' als' Mem' MM',
  r = SoftBound.rok ->
  state = SoftBound.mkState (SoftBound.mkEC (block_intro l ps cs tmn) lc rm als)
    Mem MM ->
  state' = SoftBound.mkState (SoftBound.mkEC (block_intro l' ps' cs' tmn') lc' 
    rm' als') Mem' MM' ->
  SimpleSE.dbBlocks S TD Ps fs gl F 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem) 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' 
    als') Mem') tr.

Definition sbop_dbFdef__seop_dbFdef_prop fid rt lp S TD Ps lc rm gl fs Mem MM lc'
  rm' als' Mem' MM' B' Rid oResult tr r
  (db:SoftBound.dbFdef fid rt lp S TD Ps lc rm gl fs Mem MM lc' rm' als' Mem' MM'
    B' Rid oResult tr r) :=
  r = SoftBound.rok ->
  SimpleSE.dbFdef fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult
    tr.

Tactic Notation "sb_db_mutind_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCall_internal" | c "dbCall_external" |
    c "dbCall_internal_error1" | c "dbCall_internal_error2" |
    c "dbCall_external_error1" | c "dbCall_external_error2" |
    c "dbSubblock_ok" | c "dbSubblock_error" | 
    c "dbSubblocks_nil" | c "dbSubblocks_cons" | c "dbSubblocks_cons_error" |
    c "dbBlock_ok" | c "dbBlock_error1" | c "dbBlock_error2" | 
    c "dbBlocks_nil" | c "dbBlocks_cons" | c "dbBlocks_cons_error" | 
    c "dbFdef_func" | c "dbFdef_func_error1" | c "dbFdef_func_error2" |
    c "dbFdef_func_error3" | c "dbFdef_func_error4" | c "dbFdef_func_error5" |
    c "dbFdef_proc" | c "dbFdef_proc_error1" | c "dbFdef_proc_error2" |
    c "dbFdef_proc_error3" | c "dbFdef_proc_error4" | c "dbFdef_proc_error5"
  ].

Lemma sbop__seop :
  (forall S TD Ps fs gl lc rm Mem0 MM0 call0 lc' rm' Mem' MM' tr r db, 
     sbop_dbCall__seop_dbCall_prop S TD Ps fs gl lc rm Mem0 MM0 call0 lc' rm' 
       Mem' MM' tr r db) 
    /\
  (forall S TD Ps fs gl lc rm als Mem MM sb lc' rm' als' Mem' MM' tr r db,
     sbop_dbSubblock__seop_dbSubblock_prop S TD Ps fs gl lc rm als Mem MM sb lc' 
       rm' als' Mem' MM' tr r db) /\
  (forall S TD Ps fs gl lc rm als Mem MM sbs lc' rm' als' Mem' MM' tr r db,
     sbop_dbSubblocks__seop_dbSubblocks_prop S TD Ps fs gl lc rm als Mem MM sbs 
       lc' rm' als' Mem' MM' tr r db) /\
  (forall S TD Ps fs gl F state1 state2 tr r db,
     sbop_dbBlock__seop_dbBlock_prop S TD Ps fs gl F state1 state2 tr r db) /\
  (forall S TD Ps fs gl F state1 state2 tr r db,
     sbop_dbBlocks__seop_dbBlocks_prop S TD Ps fs gl F state1 state2 tr r db) /\
  (forall fid rt lp S1 TD Ps1 lc rm gl fs Mem MM lc' rm' als' Mem' MM' B' Rid 
       oResult tr r db,
     sbop_dbFdef__seop_dbFdef_prop fid rt lp S1 TD Ps1 lc rm gl fs Mem MM lc' rm'
       als' Mem' MM' B' Rid oResult tr r db).
Proof.
(sb_db_mutind_cases
  apply SoftBound.sb_db_mutind with
    (P  := sbop_dbCall__seop_dbCall_prop)
    (P0 := sbop_dbSubblock__seop_dbSubblock_prop)
    (P1 := sbop_dbSubblocks__seop_dbSubblocks_prop)
    (P2 := sbop_dbBlock__seop_dbBlock_prop)
    (P3 := sbop_dbBlocks__seop_dbBlocks_prop)
    (P4 := sbop_dbFdef__seop_dbFdef_prop) Case);
  unfold sbop_dbCall__seop_dbCall_prop, 
         sbop_dbFdef__seop_dbFdef_prop, sbop_dbSubblock__seop_dbSubblock_prop,
         sbop_dbSubblocks__seop_dbSubblocks_prop, 
         sbop_dbBlock__seop_dbBlock_prop,
         sbop_dbBlocks__seop_dbBlocks_prop; intros; subst; 
    try solve [ invert_result | 
                eauto using sbop_dbCmds__seop_dbCmds ].
Case "dbCall_internal".
  apply sbop_callUpdateLocals__seop_callUpdateLocals in e1; eauto.

Case "dbBlock_ok".
  inversion H1; subst. clear H1.
  inversion H2; subst. clear H2.
  apply sbop_dbCmds__seop_dbCmds in d0; eauto.

Case "dbBlocks_nil".
  inversion H1; subst. clear H1.
  auto.

Case "dbBlocks_cons".
  inversion d; subst; try solve [ invert_result ].
  destruct B'. eauto.
Qed.

Lemma sbop_dbCall__seop_dbCall : forall S TD Ps fs gl lc rm Mem0 MM0 call0 lc' 
    rm' Mem' MM' tr,
  SoftBound.dbCall S TD Ps fs gl lc rm Mem0 MM0 call0 lc' rm' Mem' MM' tr 
    SoftBound.rok ->
  SimpleSE.dbCall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr.
Proof.
  intros.
  destruct sbop__seop as [J _]. 
  eapply J; eauto.
Qed.

Lemma sbop_dbSubblock__seop_dbSubblock : forall S TD Ps fs gl lc rm als Mem MM cs
    lc' rm' als' Mem' MM' tr,
  SoftBound.dbSubblock S TD Ps fs gl lc rm als Mem MM cs lc' rm' als' Mem' MM' tr
    SoftBound.rok  ->
  SimpleSE.dbSubblock S TD Ps fs gl lc als Mem cs lc' als' Mem' tr.
Proof.
  intros.
  destruct sbop__seop as [_ [J _]]. 
  eapply J; eauto.
Qed.

Lemma sbop_dbSubblocks__seop_dbSubblocks : forall S TD Ps fs gl lc rm als Mem MM 
    cs lc' rm' als' Mem' MM' tr,
  SoftBound.dbSubblocks S TD Ps fs gl lc rm als Mem MM cs lc' rm' als' Mem' MM' 
    tr SoftBound.rok ->
  SimpleSE.dbSubblocks S TD Ps fs gl lc als Mem cs lc' als' Mem' tr.
Proof.
  intros.
  destruct sbop__seop as [_ [_ [J _]]]. 
  eapply J; eauto.
Qed.

Lemma sbop_dbBlock__seop_dbBlock :  forall S TD Ps fs gl F tr l ps cs tmn lc rm 
    als Mem MM l' ps' cs' tmn' lc' rm' als' Mem' MM',
  SoftBound.dbBlock S TD Ps fs gl F 
   (SoftBound.mkState (SoftBound.mkEC (block_intro l ps cs tmn) lc rm als) Mem 
     MM) 
   (SoftBound.mkState (SoftBound.mkEC (block_intro l' ps' cs' tmn') lc' rm' als')
     Mem' MM') tr SoftBound.rok ->
  SimpleSE.dbBlock S TD Ps fs gl F 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem) 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' als') 
    Mem') tr.
Proof.
  intros.
  destruct sbop__seop as [_ [_ [_ [J _]]]]. 
  eapply J; eauto.
Qed.

Lemma sbop_dbBlocks__seop_dbBlocks : forall S TD Ps fs gl F tr l ps cs tmn lc rm
    als Mem MM l' ps' cs' tmn' lc' rm' als' Mem' MM',
  SoftBound.dbBlocks S TD Ps fs gl F
    (SoftBound.mkState (SoftBound.mkEC (block_intro l ps cs tmn) lc rm als) Mem 
      MM) 
    (SoftBound.mkState (SoftBound.mkEC (block_intro l' ps' cs' tmn') lc' rm' 
      als') Mem' MM') tr SoftBound.rok ->  
  SimpleSE.dbBlocks S TD Ps fs gl F
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem) 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' als') 
      Mem') tr.
Proof.
  intros.
  destruct sbop__seop as [_ [_ [_ [_ [J _]]]]]. 
  eapply J; eauto.
Qed.

Lemma sbop_dbFdef__seop_dbFdef : forall fid rt lp S TD Ps lc rm gl fs Mem MM lc' 
    rm' als' Mem' MM' B' Rid oResult tr,
  SoftBound.dbFdef fid rt lp S TD Ps lc rm gl fs Mem MM lc' rm' als' Mem' MM' B'
    Rid oResult tr SoftBound.rok ->
  SimpleSE.dbFdef fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr.
Proof.
  intros.
  destruct sbop__seop as [_ [_ [_ [_ [_ J]]]]]. 
  eapply J; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)

