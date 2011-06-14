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
Require Import ssa_props.
Require Import alist.
Require Import sb_def.
Require Import Coqlib.
Require Import Memdata.
Require Import Memory.
Require Import Integers.
Require Import sb_tactic.
Require Import symexe_def.
Require Import symexe_tactic.
Require Import Znumtheory.
Require Import sb_metadata.
Require Import ssa_dynamic.

Import SoftBound.

Inductive wf_insn : sbState -> Prop :=
| wf_Return : forall S TD Ps F B rid RetTy Result lc rm gl fs F' B' c' cs' tmn' 
    lc' rm' EC Mem MM als als' gr,   
  Instruction.isCallInst c' = true ->
  getOperandValue TD Mem Result lc gl = Some gr ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B nil (insn_return rid RetTy Result) lc rm als)::
       (mk_sbEC F' B' (c'::cs') tmn' lc' rm' als')::EC) gl fs Mem MM)

| wf_ReturnVoid : forall S TD Ps F B rid lc rm gl fs F' B' c' tmn' lc' rm' EC cs'
    Mem MM als als',   
  Instruction.isCallInst c' = true ->
  wf_insn
    (mk_sbState S TD Ps 
      ((mk_sbEC F B nil (insn_return_void rid) lc rm als)::
       (mk_sbEC F' B' (c'::cs') tmn' lc' rm' als')::EC) gl fs Mem MM)

| wf_Branch : forall S TD Ps F B lc rm gl fs bid Cond l1 l2 c l' ps' cs' tmn' lc'
    rm' EC Mem MM als,   
  getOperandValue TD Mem Cond lc gl = Some c ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD Mem (block_intro l' ps' cs' tmn') B gl lc rm = 
    Some (lc', rm') ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B nil (insn_br bid Cond l1 l2) lc rm als)::EC) 
      gl fs Mem MM)

| wf_Branch_uncond : forall S TD Ps F B lc rm gl fs bid l l' ps' cs' tmn' lc' rm'
    EC Mem MM als,   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD Mem (block_intro l' ps' cs' tmn') B gl lc rm = 
    Some (lc', rm') ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B nil (insn_br_uncond bid l) lc rm als)::EC) 
      gl fs Mem MM)

| wf_Bop: forall S TD Ps F B lc rm gl fs id bop sz v1 v2 EC cs tmn Mem MM als gv1
    gv2,
  getOperandValue TD Mem v1 lc gl = Some gv1 ->
  getOperandValue TD Mem v2 lc gl = Some gv2 ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 

| wf_FBop: forall S TD Ps F B lc rm gl fs id fbop fp v1 v2 gv1 gv2 EC cs tmn Mem 
    MM als,
  getOperandValue TD Mem v1 lc gl = Some gv1 ->
  getOperandValue TD Mem v2 lc gl = Some gv2 ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 

| wf_ExtractValue : forall S TD Ps F B lc rm gl fs id t v gv idxs EC cs tmn 
    Mem MM als,
  getOperandValue TD Mem v lc gl = Some gv ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_extractvalue id t v idxs)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 

| wf_InsertValue : forall S TD Ps F B lc rm gl fs id t v t' v' gv gv' idxs 
    EC cs tmn Mem MM als,
  getOperandValue TD Mem v lc gl = Some gv ->
  getOperandValue TD Mem v' lc gl = Some gv' ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_insertvalue id t v t' v' idxs)::cs) tmn lc rm als)
      ::EC) gl fs Mem MM) 

| wf_Malloc : forall S TD Ps F B lc rm gl fs id t v gn align EC cs tmn Mem MM 
    als,
  getOperandValue TD Mem v lc gl = Some gn ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_malloc id t v align)::cs) tmn lc rm als)::EC) 
       gl fs Mem MM) 

| wf_Free : forall S TD Ps F B lc rm gl fs fid t v EC cs tmn Mem als MM mptr,
  getOperandValue TD Mem v lc gl = Some mptr ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_free fid t v)::cs) tmn lc rm als)::EC) gl fs Mem MM) 

| wf_Alloca : forall S TD Ps F B lc rm gl fs id t v gn align EC cs tmn Mem MM 
    als,
  getOperandValue TD Mem v lc gl = Some gn ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_alloca id t v align)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 

| wf_Load : forall S TD Ps F B lc rm gl fs id t align vp EC cs tmn Mem als 
    gvp MM,
  getOperandValue TD Mem vp lc gl = Some gvp ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_load id t vp align)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 

| wf_Store : forall S TD Ps F B lc rm gl fs sid t align v vp EC cs tmn Mem MM
    als gv gvp,
  getOperandValue TD Mem v lc gl = Some gv ->
  getOperandValue TD Mem vp lc gl = Some gvp ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_store sid t v vp align)::cs) tmn lc rm als)::EC) 
       gl fs Mem MM) 

| wf_GEP : forall S TD Ps F B lc rm gl fs id inbounds t vp idxs vidxs EC gvp 
    cs tmn Mem MM als,
  getOperandValue TD Mem vp lc gl = Some gvp ->
  values2GVs TD Mem idxs lc gl = Some vidxs ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_gep id inbounds t vp idxs)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 

| wf_Trunc : forall S TD Ps F B lc rm gl fs id truncop t1 v1 t2 gv1 EC cs tmn 
                   Mem MM als,
  getOperandValue TD Mem v1 lc gl = Some gv1 ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 

| wf_Ext : forall S TD Ps F B lc rm gl fs id extop t1 v1 t2 gv1 EC cs tmn Mem MM
                 als,
  getOperandValue TD Mem v1 lc gl = Some gv1 ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc rm als)::EC) 
       gl fs Mem MM) 

| wf_Cast : forall S TD Ps F B lc rm gl fs id castop t1 v1 t2 gv1 EC cs tmn 
    Mem MM als,
  getOperandValue TD Mem v1 lc gl = Some gv1 ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_cast id castop t1 v1 t2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 

| wf_Icmp : forall S TD Ps F B lc rm gl fs id cond t v1 v2 gv1 gv2 EC cs tmn Mem 
    MM als,
  getOperandValue TD Mem v1 lc gl = Some gv1 ->
  getOperandValue TD Mem v2 lc gl = Some gv2 ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 

| wf_Fcmp : forall S TD Ps F B lc rm gl fs id fcond fp v1 v2 gv1 gv2 EC cs tmn 
    Mem MM als,
  getOperandValue TD Mem v1 lc gl = Some gv1 ->
  getOperandValue TD Mem v2 lc gl = Some gv2 ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 

| wf_Select : forall S TD Ps F B lc rm gl fs id v0 t v1 v2 c EC cs tmn Mem MM
    als gv1 gv2,
  getOperandValue TD Mem v0 lc gl = Some c ->
  getOperandValue TD Mem v1 lc gl = Some gv1 ->
  getOperandValue TD Mem v2 lc gl = Some gv2 ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc rm als)::EC) 
      gl fs Mem MM) 

| wf_Call : forall S TD Ps F B lc rm gl fs rid noret tailc fid fv lp cs tmn
                            l' ps' cs' tmn' EC rt la va lb Mem MM als rm',
  LLVMopsem.lookupFdefViaGV TD Mem Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  initRmetadata TD Mem gl la lp rm = Some rm' ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_call rid noret tailc rt fv lp)::cs) tmn lc rm als)
        ::EC) gl fs Mem MM)

| wf_ExCall : forall S TD Ps F B lc rm gl fs rid noret tailc fid fv lp cs tmn EC 
                    rt la va Mem als oresult Mem' lc' MM,
  LLVMopsem.lookupExFdecViaGV TD Mem Ps gl lc fs fv = 
    Some (fdec_intro (fheader_intro rt fid la va)) ->
  LLVMopsem.callExternalFunction Mem fid (params2GVs TD Mem lp lc gl) = 
    (oresult, Mem') ->
  LLVMopsem.exCallUpdateLocals noret rid oresult lc = Some lc' ->
  wf_insn 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B ((insn_call rid noret tailc rt fv lp)::cs) tmn lc rm als)
       ::EC) gl fs Mem MM)
.

Definition runtime_domination st :=
  exists S, exists TD, exists Ps, exists B, exists lc, exists rm, exists gl,
  exists fs, exists rid, exists noret, exists tailc, exists fid, exists fv,
  exists lp, exists cs, exists tmn, exists l1, exists ps1, exists cs1, 
  exists tmn1, exists EC, exists rt, exists la, exists va, exists lb, exists Mem,
  exists MM,
  exists als, exists rm1, exists lc2, exists rm2, exists als2, exists cs2,
  exists tmn2, exists B2, exists tr, exists F, exists B1,
  F = fdef_intro (fheader_intro rt fid la va) lb /\
  LLVMopsem.lookupFdefViaGV TD Mem Ps gl lc fs fv = Some F /\
  getEntryBlock F = Some B1 /\
  B1 = block_intro l1 ps1 cs1 tmn1 /\
  initRmetadata TD Mem gl la lp rm = Some rm1 /\
  st =  
    (mk_sbState S TD Ps 
      ((mk_sbEC F B2 cs2 tmn2 lc2 rm2 als2)::
       (mk_sbEC F B ((insn_call rid noret tailc rt fv lp)::cs) tmn lc rm als)
         ::EC) gl fs Mem MM) /\
  dsop_star 
    (mk_sbState S TD Ps 
      ((mk_sbEC F B1 cs1 tmn1 (initLocals la (params2GVs TD Mem lp lc gl))
         rm1 nil)::
       (mk_sbEC F B ((insn_call rid noret tailc rt fv lp)::cs) tmn lc rm als)
         ::EC) gl fs Mem MM)
    st tr /\
  wf_insn st.

Fixpoint wf_md_sbECStack TD M (stks:sbECStack) : Prop :=
match stks with
| nil => True
| mk_sbEC _ _ _ _ _ rm _ :: stks' => 
    wf_rmetadata TD M rm /\ wf_md_sbECStack TD M stks'
end.

Definition wf_md_sbState (st:sbState) : Prop :=
let '(mk_sbState _ TD _ stks _ _ M MM) := st in
wf_md_sbECStack TD M stks /\ wf_mmetadata TD M MM.

Lemma dsInsn__preservation : forall st1 st2 tr,
  dsInsn st1 st2 tr -> wf_md_sbState st1 -> wf_md_sbState st2.
Proof.
  intros st1 st2 tr H.
  (sb_dsInsn_cases (destruct H) Case); intros Hwf; simpl in *; try solve [eauto].
Case "dsReturn".
  destruct Hwf as [[Hwfr1 [Hwfr2 Hwf]] Hwfm].
Admitted.

Lemma dsInsn__runtime_domination : forall st1 st2 tr,
  dsInsn st1 st2 tr -> 
  runtime_domination st1 ->
  runtime_domination st2.
Admitted.

Lemma free_allocas_inv : forall TD M als, 
  exists M', free_allocas TD M als = Some M'.  
Proof.
  induction als; simpl.
    exists M. auto.

    unfold free, blk2GV, GV2ptr, ptr2GV, val2GV.
    simpl.
    admit. (* Mem.free returns None if a is dangling. *)
Qed.    

Lemma dsInsn__progress : forall st1,
  wf_insn st1 ->
  wf_md_sbState st1 -> 
  exists st2, exists tr, dsInsn st1 st2 tr.
Proof.
  intros st1 Hwfi Hwfmd.
  destruct st1 as [S TD Ps ECs gl fs M MM]. simpl in *.
  destruct Hwfmd as [Hwfstk Hwfm].
  inv Hwfi; simpl in *.
  Case "Return".
    destruct (@free_allocas_inv TD M als) as [M' J].
    assert (exists lc'', exists rm'', 
      returnUpdateLocals TD M c' Result0 lc lc' rm rm' gl = Some (lc'', rm''))
      as J1.
      unfold returnUpdateLocals.
      rewrite H8.      
      destruct (getCallerReturnID c').
        destruct (get_reg_metadata TD M gl rm Result0).
          admit.
          admit.
        admit.
    destruct J1 as [lc'' [rm'' J1]].
    exists (mk_sbState S TD Ps 
      ((mk_sbEC F' B' cs' tmn' lc'' rm'' als')::EC) gl fs M' MM).
    exists trace_nil.
    apply dsReturn; auto.
         
admit.
admit.
admit.

  Case "Bop".


admit.
admit.
admit.

Admitted.

(*
Lemma dsInsn__progress : forall st1,
  runtime_domination st1 ->
  wf_md_sbState st1 -> 
  exists st2, exists tr, dsInsn st1 st2 tr.
Proof.
  intros st1 Hwfi Hwfmd.
  destruct st1. simpl in *.
  destruct Hwfmd as [Hwfstk Hwfm].
  destruct Hwfi as
  [S [TD [Ps [B [lc [rm [gl
  [fs [rid [noret [tailc [fid [fv
  [lp [cs [tmn [l1 [ps1 [cs1
  [tmn1 [EC [rt [la [lb [Mem [MM
  [als [rm1 [lc2 [rm2 [als2 [cs2
  [tmn2 [B2 [tr [F [B1 [J1 [J2 [J3 [J4 [J5 [J6 [J7 J8]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]. subst.
  inv J8.
*)

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
