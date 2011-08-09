Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import Ensembles.
Require Import ssa_def.
Require Import ssa_lib.
Require Import ssa_props.
Require Import ssa_analysis.
Require Import ssa_static.
Require Import ssa_static_lib.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import AST.
Require Import Maps.
Require Import opsem.

Module OpsemProps (GVsSig : GenericValuesSig).

Module Sem := Opsem GVsSig.
Export Sem.

Lemma func_callUpdateLocals_is_returnUpdateLocals : 
  forall TD rid noret0 tailc0 ft fid lp Result lc lc' gl,
  returnUpdateLocals TD (insn_call rid noret0 tailc0 ft fid lp) Result 
    lc lc' gl =
  callUpdateLocals TD ft noret0 rid (Some Result) lc' lc gl.
Proof.
  intros.
  unfold returnUpdateLocals. 
  unfold callUpdateLocals.
  destruct noret0; auto.
Qed.

Lemma proc_callUpdateLocals_is_id : forall TD ft rid noret0 lc lc' gl lc'',
  callUpdateLocals TD ft noret0 rid None lc' lc gl = Some lc'' -> 
  lc' = lc'' /\ noret0 = true.
Proof.
  intros.
  unfold callUpdateLocals in H. 
  destruct noret0; inversion H; auto.
Qed.

Lemma sInsn__implies__sop_star : forall state state' tr,
  sInsn state state' tr ->
  sop_star state state' tr.
Proof.
  intros state state' tr HdsInsn.
  rewrite <- trace_app_nil__eq__trace.
  eauto.
Qed.

Lemma sInsn__implies__sop_plus : forall state state' tr,
  sInsn state state' tr ->
  sop_plus state state' tr.
Proof.
  intros state state' tr HdsInsn.
  rewrite <- trace_app_nil__eq__trace.
  eauto.
Qed.

Lemma sop_plus__implies__sop_star : forall state state' tr,
  sop_plus state state' tr ->
  sop_star state state' tr.
Proof.
  intros state state' tr Hdsop_plus.
  inversion Hdsop_plus; subst; eauto.
Qed.

Hint Resolve sInsn__implies__sop_star sInsn__implies__sop_plus 
  sop_plus__implies__sop_star. 

Lemma sop_star_trans : forall state1 state2 state3 tr12 tr23,
  sop_star state1 state2 tr12 ->
  sop_star state2 state3 tr23 ->
  sop_star state1 state3 (trace_app tr12 tr23).
Proof.
  intros state1 state2 state3 tr12 tr23 Hdsop12 Hdsop23.
  generalize dependent state3.
  generalize dependent tr23.
  induction Hdsop12; intros; auto.
    rewrite <- trace_app_commute. eauto.
Qed.

Lemma sop_diverging_trans : forall state tr1 state' tr2,
  sop_star state state' tr1 ->
  sop_diverges state' tr2 ->
  sop_diverges state (Trace_app tr1 tr2).
Proof. 
  intros state tr1 state' tr2 state_dsop_state' state'_dsop_diverges.
  generalize dependent tr2.
  (sop_star_cases (induction state_dsop_state') Case); intros; auto.
  Case "sop_star_cons".
    rewrite <- Trace_app_commute. eauto.
Qed.

(***********************************************************)
(** big-step convergence -> small-step convergence *)

(** First, by mutual induction, we prove that bInsn, bops and  
    bFdef imply small-step semantics. *)

Definition bInsn__implies__sop_plus_prop state state' tr 
  (db:bInsn state state' tr) := sop_plus state state' tr.
Definition bops__implies__sop_star_prop state state' tr 
  (db:bops state state' tr) := sop_star state state' tr.
Definition bFdef__implies__sop_star_prop fv rt lp S TD Ps ECs lc gl fs Mem lc'
als' Mem' B'' rid oResult tr 
(db:bFdef fv rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' B'' rid oResult tr) 
  := 
  match oResult with
  | Some Result => forall fptrs,
    getOperandValue TD fv lc gl = Some fptrs -> 
    exists fptr, exists fa, exists fid, exists la, exists va, exists lb, 
    exists l', exists ps', exists cs', exists tmn', exists gvs, exists lc0, 
    fptr @ fptrs /\
    lookupFdefViaPtr Ps fs fptr = 
      Some (fdef_intro (fheader_intro fa rt fid la va) lb) /\
    getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
      Some (block_intro l' ps' cs' tmn') /\
    params2GVs TD lp lc gl = Some gvs /\
    initLocals TD la gvs = Some lc0 /\
    sop_star
      (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                              (block_intro l' ps' cs' tmn') cs' tmn' 
                              lc0
                               nil)::ECs) gl fs Mem)
      (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                               B'' nil (insn_return rid rt Result) lc'
                               als')::ECs) gl fs 
                               Mem')
      tr
  | None => forall fptrs,
    getOperandValue TD fv lc gl = Some fptrs -> 
    exists fptr, exists fa, exists fid, exists la, exists va, exists lb, 
    exists l', exists ps', exists cs', exists tmn', exists gvs, exists lc0, 
    fptr @ fptrs /\
    lookupFdefViaPtr Ps fs fptr = 
      Some (fdef_intro (fheader_intro fa rt fid la va) lb) /\
    getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
      Some (block_intro l' ps' cs' tmn') /\
    params2GVs TD lp lc gl = Some gvs /\
    initLocals TD la gvs = Some lc0 /\
    sop_star
      (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                              (block_intro l' ps' cs' tmn') cs' tmn' 
                              lc0
                              nil)::ECs) gl fs Mem)
      (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                               B'' nil (insn_return_void rid) lc'
                               als')::ECs) gl fs 
                               Mem')
      tr
  end
  .

Lemma b__implies__s:
  (forall state state' t  db, @bInsn__implies__sop_plus_prop state state' t db)
    /\
  (forall state state' t  db, @bops__implies__sop_star_prop state state' t db) 
    /\
  (forall fv rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' B'' rid oret tr db, 
     @bFdef__implies__sop_star_prop fv rt lp S TD Ps ECs lc gl fs Mem lc' als' 
       Mem' B'' rid oret tr db).
Proof.
(b_mutind_cases
  apply b_mutind with
    (P  := bInsn__implies__sop_plus_prop)
    (P0 := bops__implies__sop_star_prop)
    (P1 := bFdef__implies__sop_star_prop)
    Case);
  unfold bInsn__implies__sop_plus_prop, 
         bops__implies__sop_star_prop, 
         bFdef__implies__sop_star_prop; 
  intros; subst; simpl; intuition; eauto.
  Case "bCall".
    inversion b; subst.
    SCase "bFdef_func".
    assert (Hlookup:=H0).
    apply H in H0; auto. clear H.
    destruct H0 as [fptr' [fa0 [fid0 [la0 [va0 [lb0 [l0 [ps0 [cs0 [tmn0 [gvs0 
      [lc0 [J1 [J2 [J3 [J4 [J5 J6]]]]]]]]]]]]]]]]].
    rewrite <- nil_app_trace__eq__trace.
    apply sop_plus_cons with 
      (state2:=mkState S TD Ps 
                      ((mkEC (fdef_intro (fheader_intro fa0 rt fid0 la0 va0) lb0)
                               (block_intro l0 ps0 cs0 tmn0) cs0 tmn0 lc0
                               nil)::
                        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) 
                         tmn lc als)::EC) 
                        gl fs Mem0); eauto.
    rewrite <- trace_app_nil__eq__trace.
    apply sop_star_trans with 
      (state2:=mkState S TD Ps 
                     ((mkEC (fdef_intro (fheader_intro fa0 rt fid0 la0 va0) lb0)
                               (block_intro l'' ps'' cs'' 
                                (insn_return Rid rt Result)) nil 
                                (insn_return Rid rt Result) lc'
                                als')::
                        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) 
                         tmn lc als)::EC) 
                         gl fs Mem'); auto.
      apply sInsn__implies__sop_star.
        apply sReturn; auto.
          erewrite func_callUpdateLocals_is_returnUpdateLocals; eauto.

    SCase "bFdef_proc".
    assert (Hlookup:=H0).
    apply H in H0; auto. clear H.
    destruct H0 as [fptr' [fa0 [fid0 [la0 [va0 [lb0 [l0 [ps0 [cs0 [tmn0 [gvs0 
      [lc0 [J1 [J2 [J3 [J4 [J5 J6]]]]]]]]]]]]]]]]].
    rewrite <- nil_app_trace__eq__trace.
    apply sop_plus_cons with 
      (state2:=mkState S TD Ps 
                      ((mkEC (fdef_intro (fheader_intro fa0 rt fid0 la0 va0) lb0)
                               (block_intro l0 ps0 cs0 tmn0) cs0 tmn0 lc0
                               nil)::
                        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) 
                         tmn lc als)::EC) 
                        gl fs Mem0); eauto.
    rewrite <- trace_app_nil__eq__trace.
    apply proc_callUpdateLocals_is_id in e0.
    destruct e0; subst.
    apply sop_star_trans with 
      (state2:=mkState S TD Ps 
                      ((mkEC (fdef_intro (fheader_intro fa0 rt fid0 la0 va0) lb0)
                               (block_intro l'' ps'' cs'' (insn_return_void Rid))
                                nil (insn_return_void Rid) lc'
                                als')::
                        (mkEC F B ((insn_call rid true ca ft fv lp)::cs) 
                         tmn lc'' als)::EC) 
                        gl fs Mem'); auto.

  Case "bops_cons".
    apply sop_star_trans with (state2:=S2); auto.
        
  Case "bFdef_func".
    rewrite H0 in e. inv e. exists fptr. exists fa. exists fid. exists la.
    exists va. exists lb. exists l'. exists ps'. exists cs'. exists tmn'. 
    exists gvs. exists lc0. repeat (split; auto).

  Case "bFdef_proc".
   rewrite H0 in e. inv e. exists fptr. exists fa. exists fid. exists la.
    exists va. exists lb. exists l'. exists ps'. exists cs'. exists tmn'. 
    exists gvs. exists lc0. repeat (split; auto).
Qed.  
    
Lemma bInsn__implies__sop_plus : forall state state' tr,
  bInsn state state' tr ->
  sop_plus state state' tr.
Proof.
  destruct b__implies__s as [J _]. eauto.
Qed.

Lemma bInsn__implies__sop_star : forall state state' tr,
  bInsn state state' tr ->
  sop_star state state' tr.
Proof. 
  intros state state' tr state_dbInsn_state'.
  apply bInsn__implies__sop_plus in state_dbInsn_state'; auto.
Qed.

Lemma bops__implies__sop_star : forall state state' tr,
  bops state state' tr ->
  sop_star state state' tr.
Proof.
  destruct b__implies__s as [_ [J _]]. eauto.
Qed.

Lemma bFdef_func__implies__sop_star : forall fv rt lp S TD Ps ECs lc gl fs
    Mem lc' als' Mem' B'' rid Result tr fptrs, 
  bFdef fv rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' B'' rid (Some Result) 
    tr ->
  getOperandValue TD fv lc gl = Some fptrs -> 
  exists fptr, exists fa, exists fid, exists la, exists va, exists lb, 
  exists l', exists ps', exists cs', exists tmn', exists gvs, exists lc0, 
  fptr @ fptrs /\
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) /\
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') /\
  params2GVs TD lp lc gl = Some gvs /\
  initLocals TD la gvs = Some lc0 /\
  sop_star 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             (block_intro l' ps' cs' tmn') cs' tmn' lc0
                             nil)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             B'' nil (insn_return rid rt Result) lc'
                             als')::ECs) gl fs Mem')
    tr.
Proof.
  intros fv rt lp S TD Ps EC lc gl fs Mem0 lc' als' Mem' B'' rid Result tr 
    fptrs H H1.
  destruct b__implies__s as [_ [_ J]]. 
  assert (K:=@J fv rt lp S TD Ps EC lc gl fs Mem0 lc' als' Mem' B'' rid 
    (Some Result) tr H fptrs H1); auto.
Qed.

Lemma bFdef_proc__implies__sop_star : forall fv rt lp S TD Ps ECs lc gl fs
    Mem lc' als' Mem' B'' rid tr fptrs,
  bFdef fv rt lp S TD Ps ECs lc gl fs  Mem lc' als' Mem' B'' rid None tr ->
  getOperandValue TD fv lc gl = Some fptrs -> 
  exists fptr, exists fa, exists fid, exists la, exists va, exists lb, 
  exists l', exists ps', exists cs', exists tmn', exists gvs, exists lc0, 
  fptr @ fptrs /\
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) /\
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') /\
  params2GVs TD lp lc gl = Some gvs /\
  initLocals TD la gvs = Some lc0 /\
  sop_star 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                            (block_intro l' ps' cs' tmn') cs' tmn' lc0
                            nil)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             B'' nil (insn_return_void rid) lc'
                             als')::ECs) gl fs Mem')
    tr.
Proof.
  intros fv rt lp S TD Ps EC lc gl fs Mem0 lc' als' Mem' B'' rid tr fptrs H H1.
  destruct b__implies__s as [_ [_ J]]. 
  assert (K:=@J fv rt lp S TD Ps EC lc gl fs Mem0 lc' als' Mem' B'' rid None tr 
    H fptrs H1); auto.
Qed.

(** Then we prove that the whole program holds the same property. *)

Lemma b_converges__implies__s_converges : forall sys main VarArgs FS,
  b_converges sys main VarArgs FS ->
  s_converges sys main VarArgs FS.
Proof.
  intros sys main VarArgs FS Hdb_converges.
  inversion Hdb_converges; subst.
  apply s_converges_intro with (IS:=IS)(tr:=tr); auto.
  apply bops__implies__sop_star; auto.
Qed.

Lemma b_goeswrong__implies__s_goeswrong : forall sys main VarArgs FS,
  b_goeswrong sys main VarArgs FS ->
  s_goeswrong sys main VarArgs FS.
Proof.
  intros sys main VarArgs FS Hdb_goeswrong.
  inversion Hdb_goeswrong; subst.
  apply s_goeswrong_intro with (IS:=IS)(tr:=tr); auto.
  apply bops__implies__sop_star; auto.
Qed.

(***********************************************************)
(** big-step divergence -> small-step divergence *)

(** First,we prove that bInsn, bops and bFdef imply small-step semantics,
    by nested coinduction. *)

Lemma bFdefInf_bopInf__implies__sop_diverges : 
   forall (fv : value) (rt : typ) (lp : params) (S : system)
     (TD : TargetData) (Ps : products) (ECs : list ExecutionContext)
     (lc : GVsMap) (gl fs : GVMap) (Mem0 : mem) (tr : Trace) 
     (fid : id) (fa : fnattrs) (lc1 : GVsMap) (l' : l) 
     (ps' : phinodes) (cs' : cmds) (tmn' : terminator) 
     (la : args) (va : varg) (lb : blocks) (gvs : list GVs) 
     (fptrs0 : GVs) (fptr : GenericValue),
   fptr @ fptrs0 ->
   lookupFdefViaPtr Ps fs fptr =
   ret fdef_intro (fheader_intro fa rt fid la va) lb ->
   getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) =
   ret block_intro l' ps' cs' tmn' ->
   params2GVs TD lp lc gl = ret gvs ->
   initLocals TD la gvs = ret lc1 ->
   bopInf
     {|
     CurSystem := S;
     CurTargetData := TD;
     CurProducts := Ps;
     ECS := {|
            CurFunction := fdef_intro (fheader_intro fa rt fid la va) lb;
            CurBB := block_intro l' ps' cs' tmn';
            CurCmds := cs';
            Terminator := tmn';
            Locals := lc1;
            Allocas := nil |} :: ECs;
     Globals := gl;
     FunTable := fs;
     Mem := Mem0 |} tr ->
   getOperandValue TD fv lc gl = ret fptrs0 ->
   sop_diverges
     {|
     CurSystem := S;
     CurTargetData := TD;
     CurProducts := Ps;
     ECS := {|
            CurFunction := fdef_intro (fheader_intro fa rt fid la va) lb;
            CurBB := block_intro l' ps' cs' tmn';
            CurCmds := cs';
            Terminator := tmn';
            Locals := lc1;
            Allocas := nil |} :: ECs;
     Globals := gl;
     FunTable := fs;
     Mem := Mem0 |} tr.
Proof.
  cofix CIH_bFdefInf.

  assert (forall state tr, 
          bInsnInf state tr -> 
          sop_diverges state tr) as bInsnInf__implies__sop_diverges.
    cofix CIH_bInsnInf.
    intros state tr HbInsnInf.
    
    inversion HbInsnInf; subst.
    rewrite <- nil_app_Trace__eq__Trace.
    assert (HbFdefInf:=H).
    inversion H; subst.
    apply sop_diverges_intro with 
      (state2:=mkState S TD Ps 
                       ((mkEC (fdef_intro (fheader_intro fa rt fid la va)lb)
                               (block_intro l' ps' cs' tmn') cs' tmn' lc1
                               nil)::
                        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) 
                         tmn lc als)::EC) 
                         gl fs Mem0); 
      try solve [clear CIH_bFdefInf CIH_bInsnInf; eauto].
      inv HbFdefInf.
      apply CIH_bFdefInf with (fid:=fid)(l':=l')(ps':=ps')(cs':=cs')(tmn':=tmn')
        (fa:=fa)(la:=la)(va:=va)(lb:=lb)(gvs:=gvs)(lc1:=lc1)(fptr:=fptr)(fv:=fv)
        (lp:=lp)(lc:=lc)(fptrs0:=fptrs) in H6; auto.

  assert (forall state tr, 
          bopInf state tr -> 
          sop_diverges state tr) as bopInf__implies__sop_diverges.
    cofix CIH_bopInf.
    intros state tr0 HbopInf.
    inversion HbopInf; subst.
    Case "bopInf_insn".
      apply bInsnInf__implies__sop_diverges in H; auto.
    Case "bopInf_cons".
      apply bInsn__implies__sop_plus in H.
      inversion H; subst.
      SCase "dsop_plus_cons".
        apply CIH_bopInf in H0. clear CIH_bopInf.
        apply sop_diverges_intro with (state2:=state2); auto.

  intros fv rt lp S TD Ps ECs lc gl fs Mem0 tr fid fa lc1 l' ps' cs' tmn' la va 
    lb gvs fptrs0 fptr Hin Hlookup HgetEntryBlock Hp2gvs Hinit HbFdefInf Hget.
  inversion HbFdefInf; subst; eauto.
Qed.

Lemma bFdefInf__implies__sop_diverges : forall fv rt lp S TD Ps ECs lc gl fs Mem
    tr fptrs,
  bFdefInf fv rt lp S TD Ps ECs lc gl fs Mem tr ->
  getOperandValue TD fv lc gl = Some fptrs -> 
  exists fptr, exists fa, exists fid, exists la, exists va, exists lb, 
  exists l', exists ps', exists cs', exists tmn', exists gvs, exists lc0, 
  fptr @ fptrs /\
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) /\
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') /\
  params2GVs TD lp lc gl = Some gvs /\
  initLocals TD la gvs = Some lc0 /\
  sop_diverges 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                        (block_intro l' ps' cs' tmn') cs' tmn' lc0
                        nil)::ECs) gl fs Mem)
    tr.
Proof.
  intros fv rt lp S TD Ps ECs lc gl fs Mem0 tr fptrs HdbFdefInf Hget.
  inv HdbFdefInf; subst.
  exists fptr. exists fa. exists fid. exists la. exists va. exists lb. exists l'.
  exists ps'. exists cs'. exists tmn'. exists gvs. exists lc1.
  rewrite Hget in H. inv H.
  repeat (split; auto).
    eapply bFdefInf_bopInf__implies__sop_diverges; eauto.
Qed.

Lemma bInsnInf__implies__sop_diverges : forall state tr, 
  bInsnInf state tr -> sop_diverges state tr.
Proof.
  cofix CIH_bInsnInf.
  intros state tr HbInsnInf.
    
  inversion HbInsnInf; subst.
  rewrite <- nil_app_Trace__eq__Trace.
  assert (HbFdefInf:=H).
  inversion H; subst.
  apply sop_diverges_intro with 
    (state2:=mkState S TD Ps 
                     ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb)
                             (block_intro l' ps' cs' tmn') cs' tmn' lc1
                             nil)::
                      (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) tmn
                       lc als)::EC) 
                       gl fs Mem0); 
    try solve [clear CIH_bInsnInf; eauto].
    eapply bFdefInf_bopInf__implies__sop_diverges with (l':=l')(ps':=ps')
      (cs':=cs')(tmn':=tmn')(la:=la)(va:=va)(lb:=lb)(fa:=fa)(gvs:=gvs)(lc1:=lc1) 
      in H6; eauto.
Qed.

Lemma bopInf__implies__sop_diverges : forall state tr, 
  bopInf state tr -> sop_diverges state tr.
Proof.
  cofix CIH_bopInf.
  intros state tr HdbopInf.
  inversion HdbopInf; subst.
  Case "bopInf_insn".
    apply bInsnInf__implies__sop_diverges in H; auto.
  Case "bopInf_cons".
    apply bInsn__implies__sop_plus in H.
    inversion H; subst.
    SCase "sop_plus_cons".
      apply CIH_bopInf in H0. clear CIH_bopInf.
      apply sop_diverges_intro with (state2:=state2); auto.
Qed.

(** Then we prove that the whole program holds the same property. *)

Lemma b_diverges__implies__s_diverges : forall sys main VarArgs tr, 
  b_diverges sys main VarArgs tr ->
  s_diverges sys main VarArgs tr.
Proof.
  intros sys main VarArgs tr Hdb_diverges.
  inversion Hdb_diverges; subst.
  apply s_diverges_intro with (IS:=IS)(tr:=tr); auto.
  apply bopInf__implies__sop_diverges; auto.
Qed.

Lemma BOP_inversion : forall TD lc gl b s v1 v2 gv2,
  BOP TD lc gl b s v1 v2 = Some gv2 ->
  exists gvs1, exists gvs2,
    getOperandValue TD v1 lc gl = Some gvs1 /\
    getOperandValue TD v2 lc gl = Some gvs2 /\
    GVsSig.lift_op2 (mbop TD b s) gvs1 gvs2 (typ_int s) = Some gv2.
Proof.
  intros TD lc gl b s v1 v2 gv2 HBOP.
  unfold BOP in HBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HBOP]. 
  remember (getOperandValue TD v2 lc gl) as ogv2.
  destruct ogv2; inv HBOP.
  eauto.
Qed.

Lemma FBOP_inversion : forall TD lc gl b fp v1 v2 gv,
  FBOP TD lc gl b fp v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    GVsSig.lift_op2 (mfbop TD b fp) gv1 gv2 (typ_floatpoint fp) = Some gv.
Proof.
  intros TD lc gl b fp v1 v2 gv HFBOP.
  unfold FBOP in HFBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HFBOP].
  remember (getOperandValue TD v2 lc gl) as ogv2.
  destruct ogv2; inv HFBOP.
  eauto.
Qed.

Lemma CAST_inversion : forall TD lc gl op t1 v1 t2 gv,
  CAST TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    GVsSig.lift_op1 (mcast TD op t1 t2) gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HCAST.
  unfold CAST in HCAST.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; inv HCAST.
  eauto.
Qed.

Lemma TRUNC_inversion : forall TD lc gl op t1 v1 t2 gv,
  TRUNC TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    GVsSig.lift_op1 (mtrunc TD op t1 t2) gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HTRUNC.
  unfold TRUNC in HTRUNC.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; inv HTRUNC.
  eauto.
Qed.

Lemma EXT_inversion : forall TD lc gl op t1 v1 t2 gv,
  EXT TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    GVsSig.lift_op1 (mext TD op t1 t2) gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HEXT.
  unfold EXT in HEXT.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; inv HEXT.
  eauto.
Qed.

Lemma ICMP_inversion : forall TD lc gl cond t v1 v2 gv,
  ICMP TD lc gl cond t v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    GVsSig.lift_op2 (micmp TD cond t) gv1 gv2 (typ_int 1%nat) = Some gv.
Proof.
  intros TD lc gl cond0 t v1 v2 gv HICMP.
  unfold ICMP in HICMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HICMP].
  remember (getOperandValue TD v2 lc gl) as ogv2.
  destruct ogv2; inv HICMP.
  eauto.
Qed.

Lemma FCMP_inversion : forall TD lc gl cond fp v1 v2 gv,
  FCMP TD lc gl cond fp v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    GVsSig.lift_op2 (mfcmp TD cond fp) gv1 gv2 (typ_int 1%nat) = Some gv.
Proof.
  intros TD lc gl cond0 fp v1 v2 gv HFCMP.
  unfold FCMP in HFCMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HFCMP].
  remember (getOperandValue TD v2 lc gl) as ogv2.
  destruct ogv2; inv HFCMP.
  eauto.
Qed.

(*
Lemma GEP_inversion : forall (TD:TargetData) (t:typ) (ma:GenericValue) 
  (vidxs:list GenericValue) ib mptr0,
  GEP TD t ma vidxs ib = Some mptr0 ->
  exists idxs, exists ptr, exists ptr0, 
    GVs2Nats TD vidxs = Some idxs /\ 
    GV2ptr TD (getPointerSize TD) ma = Some ptr /\
    mgep TD t ptr idxs = Some ptr0 /\
    ptr2GV TD ptr0 = mptr0.
Proof.
  intros.
  unfold GEP in H.
  remember (GVs2Nats TD vidxs) as oidxs.
  remember (GV2ptr TD (getPointerSize TD) ma) as R.
  destruct R.
    destruct oidxs.
      remember (mgep TD t v l0) as og.
      destruct og; inversion H; subst.
        exists l0. exists v. exists v0. auto.
        exists l0. exists v. exists v0. auto.

Qed.
*)

Lemma const2GV_eqAL : forall c gl1 gl2 TD, 
  eqAL _ gl1 gl2 -> 
  const2GV TD gl1 c = const2GV TD gl2 c.
Proof.
  intros. unfold const2GV.
  destruct const2GV_eqAL_aux.
  erewrite H0; eauto.
Qed.

Lemma getOperandValue_eqAL : forall lc1 gl lc2 v TD,
  eqAL _ lc1 lc2 ->
  getOperandValue TD v lc1 gl = getOperandValue TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD HeqAL.
  unfold getOperandValue in *.
  destruct v; auto.
Qed.

Lemma BOP_eqAL : forall lc1 gl lc2 bop0 sz0 v1 v2 TD,
  eqAL _ lc1 lc2 ->
  BOP TD lc1 gl bop0 sz0 v1 v2 = BOP TD lc2 gl bop0 sz0 v1 v2.
Proof.
  intros lc1 gl lc2 bop0 sz0 v1 v2 TD HeqEnv.
  unfold BOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma FBOP_eqAL : forall lc1 gl lc2 fbop0 fp0 v1 v2 TD,
  eqAL _ lc1 lc2 ->
  FBOP TD lc1 gl fbop0 fp0 v1 v2 = FBOP TD lc2 gl fbop0 fp0 v1 v2.
Proof.
  intros lc1 gl lc2 fbop0 fp0 v1 v2 TD HeqEnv.
  unfold FBOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma CAST_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  CAST TD lc1 gl op t1 v1 t2 = CAST TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold CAST in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma TRUNC_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  TRUNC TD lc1 gl op t1 v1 t2 = TRUNC TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold TRUNC in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma EXT_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  EXT TD lc1 gl op t1 v1 t2 = EXT TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold EXT in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma ICMP_eqAL : forall lc1 gl lc2 cond t v1 v2 TD,
  eqAL _ lc1 lc2 ->
  ICMP TD lc1 gl cond t v1 v2 = ICMP TD lc2 gl cond t v1 v2.
Proof.
  intros lc1 gl lc2 cond0 t v1 v2 TD HeqAL.
  unfold ICMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma FCMP_eqAL : forall lc1 gl lc2 cond fp v1 v2 TD,
  eqAL _ lc1 lc2 ->
  FCMP TD lc1 gl cond fp v1 v2 = FCMP TD lc2 gl cond fp v1 v2.
Proof.
  intros lc1 gl lc2 cond0 fp v1 v2 TD HeqAL.
  unfold FCMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma values2GVs_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  values2GVs TD l0 lc1 gl = values2GVs TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD HeqAL; simpl; auto.
    rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v); auto.
    erewrite IHl0; eauto.
Qed.
(*
Lemma lookupFdefViaGV_inversion : forall TD Ps gl lc fs fv f,
  lookupFdefViaGV TD Ps gl lc fs fv = Some f ->
  exists fptr, exists fn,
    getOperandValue TD fv lc gl = Some fptr /\
    lookupFdefViaGVFromFunTable fs fptr = Some fn /\
    lookupFdefViaIDFromProducts Ps fn = Some f.
Proof.
  intros.
  unfold lookupFdefViaGV in H.
  destruct (getOperandValue TD fv lc gl); tinv H.
  simpl in H. exists g.
  destruct (lookupFdefViaGVFromFunTable fs g); tinv H.
  simpl in H. exists i0. eauto.
Qed.  
*)

Lemma eqAL_callUpdateLocals : forall TD noret0 rid oResult lc1 lc2 gl lc1' 
  lc2' ft,
  eqAL _ lc1 lc1' ->
  eqAL _ lc2 lc2' ->
  match (callUpdateLocals TD ft noret0 rid oResult lc1 lc2 gl,
         callUpdateLocals TD ft noret0 rid oResult lc1' lc2' gl) with
  | (Some lc, Some lc') => eqAL _ lc lc'
  | (None, None) => True
  | _ => False
  end.
Proof.
  intros TD noret0 rid oResult lc1 lc2 gl lc1' lc2' ft H1 H2.
    unfold callUpdateLocals.
    destruct noret0; auto.
      destruct oResult; simpl; auto.
        destruct v; simpl.
          rewrite H2.
          destruct (lookupAL _ lc2' i0); auto using eqAL_updateAddAL.

          destruct (const2GV TD gl c); auto using eqAL_updateAddAL.
      destruct oResult; simpl; auto.
        destruct v; simpl.
          rewrite H2.
          destruct (lookupAL _ lc2' i0); auto.
          destruct ft; auto.
          destruct (GVsSig.lift_op1 (fit_gv TD ft) t ft); auto using eqAL_updateAddAL.

          destruct (const2GV TD gl c); auto using eqAL_updateAddAL.
          destruct ft; auto.
          destruct (GVsSig.lift_op1 (fit_gv TD ft) g ft); auto using eqAL_updateAddAL.
Qed.

Lemma eqAL_getIncomingValuesForBlockFromPHINodes : forall TD ps B gl lc lc',
  eqAL _ lc lc' ->
  getIncomingValuesForBlockFromPHINodes TD ps B gl lc = 
  getIncomingValuesForBlockFromPHINodes TD ps B gl lc'.
Proof.
  induction ps; intros; simpl; auto.
    destruct a; auto.
    destruct (getValueViaBlockFromValuels l0 B); auto.
    destruct v; simpl; erewrite IHps; eauto.
      rewrite H. auto.
Qed.
  
Lemma eqAL_updateValuesForNewBlock : forall vs lc lc',
  eqAL _ lc lc' ->
  eqAL _ (updateValuesForNewBlock vs lc) (updateValuesForNewBlock vs lc').
Proof.
  induction vs; intros; simpl; auto.
    destruct a; auto using eqAL_updateAddAL.
Qed.

Lemma eqAL_switchToNewBasicBlock : forall TD B1 B2 gl lc lc',
  eqAL _ lc lc' ->
  match (switchToNewBasicBlock TD B1 B2 gl lc,
         switchToNewBasicBlock TD B1 B2 gl lc') with
  | (Some lc1, Some lc1') => eqAL _ lc1 lc1'
  | (None, None) => True
  | _ => False
  end.
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite eqAL_getIncomingValuesForBlockFromPHINodes; eauto.
  destruct 
    (getIncomingValuesForBlockFromPHINodes TD (getPHINodesFromBlock B1) B2 gl 
    lc'); auto using eqAL_updateValuesForNewBlock.
Qed.

Lemma eqAL_params2GVs : forall lp TD lc gl lc',
  eqAL _ lc lc' ->
  params2GVs TD lp lc gl = params2GVs TD lp lc' gl.
Proof.
  induction lp; intros; simpl; auto.
    destruct a. 
    destruct v; simpl.
      rewrite H. erewrite IHlp; eauto.
      erewrite IHlp; eauto.
Qed.

Lemma eqAL_exCallUpdateLocals : forall TD noret0 rid oResult lc lc' ft,
  eqAL _ lc lc' ->
  match (exCallUpdateLocals TD ft noret0 rid oResult lc,
         exCallUpdateLocals TD ft noret0 rid oResult lc') with
  | (Some lc1, Some lc1') => eqAL _ lc1 lc1'
  | (None, None) => True
  | _ => False
  end.
Proof.
  intros TD noret0 rid oResult lc lc' ft H1.
    unfold exCallUpdateLocals.
    destruct noret0; auto.
    destruct oResult; auto.
    destruct ft; auto.
    destruct (fit_gv TD ft g); auto using eqAL_updateAddAL.
Qed.

Lemma updateValuesForNewBlock_uniq : forall l0 lc,
  uniq lc ->
  uniq (updateValuesForNewBlock l0 lc).
Proof.
  induction l0; intros lc Uniqc; simpl; auto.
    destruct a; apply updateAddAL_uniq; auto.
Qed.

Lemma switchToNewBasicBlock_uniq : forall TD B1 B2 gl lc lc',
  uniq lc ->
  switchToNewBasicBlock TD B1 B2 gl lc = Some lc' ->
  uniq lc'.
Proof.
  intros TD B1 B2 gl lc lc' Uniqc H.
  unfold switchToNewBasicBlock in H.
  destruct (getIncomingValuesForBlockFromPHINodes TD (getPHINodesFromBlock B1)
    B2 gl lc); inversion H; subst.
  apply updateValuesForNewBlock_uniq; auto.
Qed.      

Lemma initializeFrameValues_init : forall TD la l0 lc,
  _initializeFrameValues TD la l0 nil = Some lc ->
  uniq lc.
Proof.
  induction la; intros; simpl in *; auto.
    inv H. auto.

    destruct a as [[t ?] id0].
    destruct l0.
      remember (_initializeFrameValues TD la nil nil) as R.
      destruct R; tinv H.
      destruct (gundef TD t); inv H; eauto using updateAddAL_uniq.

      remember (_initializeFrameValues TD la l0 nil) as R.
      destruct R; tinv H.
      destruct (GVsSig.lift_op1 (fit_gv TD t) g t); inv H; 
        eauto using updateAddAL_uniq.
Qed.

Lemma initLocals_uniq : forall TD la ps lc,
  initLocals TD la ps = Some lc -> uniq lc.
Proof.
  intros la ps.
  unfold initLocals.
  apply initializeFrameValues_init; auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_eq : 
  forall ps TD l1 ps1 cs1 tmn1 ps2 cs2 tmn2,
  getIncomingValuesForBlockFromPHINodes TD ps (block_intro l1 ps1 cs1 tmn1) =
  getIncomingValuesForBlockFromPHINodes TD ps (block_intro l1 ps2 cs2 tmn2).
Proof.
  induction ps; intros; auto.
    simpl.
    erewrite IHps; eauto.
Qed.

Lemma switchToNewBasicBlock_eq : 
  forall TD B l1 ps1 cs1 tmn1 ps2 cs2 tmn2 gl lc,
  switchToNewBasicBlock TD B (block_intro l1 ps1 cs1 tmn1) gl lc =
  switchToNewBasicBlock TD B (block_intro l1 ps2 cs2 tmn2) gl lc.
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite getIncomingValuesForBlockFromPHINodes_eq; eauto.
Qed.

Lemma bops_trans : forall state1 state2 state3 tr1 tr2,
  bops state1 state2 tr1 ->
  bops state2 state3 tr2 ->
  bops state1 state3 (trace_app tr1 tr2).
Proof.
  intros state1 state2 state3 tr1 tr2 H.
  generalize dependent state3.
  generalize dependent tr2.
  induction H; intros; auto.
    rewrite <- trace_app_commute. eauto.
Qed.

Lemma bInsn__bops : forall state1 state2 tr,
  bInsn state1 state2 tr ->
  bops state1 state2 tr.
Proof.
  intros.
  rewrite <- trace_app_nil__eq__trace.
  eauto.
Qed.

Lemma bInsn__inv : forall S1 TD1 Ps1 F1 l1 ps1 cs1 tmn1 c cs tmn3 lc1 als1 
    ECs1 gl1 fs1 Mem1 S2 TD2 Ps2 F2 l2 ps2 cs2 tmn2 tmn4 lc2 als2 ECs2 gl2 
    fs2 Mem2 tr,
  bInsn 
    (mkState S1 TD1 Ps1 (mkEC F1 (block_intro l1 ps1 cs1 tmn1) (c::cs) tmn3 lc1 
      als1::ECs1) gl1 fs1 Mem1) 
    (mkState S2 TD2 Ps2 (mkEC F2 (block_intro l2 ps2 cs2 tmn2) cs tmn4 lc2
      als2::ECs2) gl2 fs2 Mem2)
    tr ->
  S1 = S2 /\ TD1 = TD2 /\ Ps1 = Ps2 /\ F1 = F2 /\ l1 = l2 /\ ps1 = ps2 /\
  cs1 = cs2 /\ tmn1 = tmn2 /\ tmn3 = tmn4 /\ gl1 = gl2 /\ fs1 = fs2.
Proof.
  intros.
  inversion H; subst; repeat (split; auto).
Qed.

Lemma bInsn_Call__inv : forall S1 TD1 Ps1 F1 l1 ps1 cs1 tmn1 c cs tmn3 lc1 
    als1 ECs1 gl1 fs1 Mem1 S2 TD2 Ps2 F2 l2 ps2 cs2 tmn2 tmn4 lc2 als2 ECs2
     gl2 fs2 Mem2 tr,
  bInsn 
    (mkState S1 TD1 Ps1 (mkEC F1 (block_intro l1 ps1 cs1 tmn1) (c::cs) tmn3 lc1 
      als1::ECs1) gl1 fs1 Mem1) 
    (mkState S2 TD2 Ps2 (mkEC F2 (block_intro l2 ps2 cs2 tmn2) cs tmn4 lc2 
      als2::ECs2) gl2 fs2 Mem2)
    tr ->
  Instruction.isCallInst c = true ->
  S1 = S2 /\ TD1 = TD2 /\ Ps1 = Ps2 /\ F1 = F2 /\ l1 = l2 /\ ps1 = ps2 /\
  cs1 = cs2 /\ tmn1 = tmn2 /\ tmn3 = tmn4 /\ gl1 = gl2  /\ fs1 = fs2 /\ 
  als1 = als2.
Proof.
  intros.
  inversion H; subst; try solve [inversion H0 | repeat (split; auto)].
Qed.

Lemma lookupFdefViaPtr_uniq : forall los nts Ps fs S fptr F,
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaPtr Ps fs fptr = Some F ->
  uniqFdef F.
Proof.
  intros.
  apply lookupFdefViaPtr_inversion in H1.
  destruct H1 as [fn [J1 J2]].
  apply lookupFdefViaIDFromProducts_inv in J2; auto.
  apply uniqSystem__uniqProducts in H0; auto.
  eapply uniqProducts__uniqFdef; simpl; eauto.
Qed.

Lemma entryBlockInSystemBlockFdef'' : forall los nts Ps fs fv F S B,
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaPtr Ps fs fv = Some F ->
  getEntryBlock F = Some B ->
  blockInSystemModuleFdef B S (module_intro los nts Ps) F.
Proof.
  intros.
  apply lookupFdefViaPtr_inversion in H0.
  destruct H0 as [fn [J1 J2]].
  apply lookupFdefViaIDFromProducts_inv in J2.
  apply entryBlockInFdef in H1.  
  apply blockInSystemModuleFdef_intro; auto.
Qed.

Lemma lookupFdefViaPtrInSystem : forall los nts Ps fs S fv F,
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaPtr Ps fs fv = Some F ->
  productInSystemModuleB (product_fdef F) S (module_intro los nts Ps).
Proof.
  intros.
  apply lookupFdefViaPtr_inversion in H0.
  destruct H0 as [fn [J1 J2]].
  apply lookupFdefViaIDFromProducts_inv in J2.
  apply productInSystemModuleB_intro; auto.
Qed.

(* preservation of uniqueness and inclusion *)

Definition bInsn_preservation_prop state1 state2 tr
  (db:bInsn state1 state2 tr) :=
  forall S los nts Ps F l ps cs tmn lc als ECs gl fs Mem cs0,
  state1 = (mkState S (los, nts) Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn 
    lc als)::ECs) gl fs Mem) ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S 
    (module_intro los nts Ps) F ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists Mem', exists cs0',
  state2 = (mkState S (los, nts) Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' 
    tmn' lc' als')::ECs) gl fs Mem') /\
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S 
    (module_intro los nts Ps) F.
Definition bops_preservation_prop state1 state2 tr
  (db:bops state1 state2 tr) :=
  forall S los nts Ps F l ps cs tmn lc als ECs gl fs Mem l' ps' cs' tmn' lc'
    als' gl' fs' Mem' cs0 cs0',
  state1 = (mkState S (los, nts) Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn 
    lc als)::ECs) gl fs Mem) ->
  state2 = (mkState S (los, nts) Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' 
    tmn' lc' als')::ECs) gl' fs' Mem') ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S 
    (module_intro los nts Ps) F ->
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S 
    (module_intro los nts Ps) F.
Definition bFdef_preservation_prop fv rt lp S TD Ps ECs lc gl fs Mem lc' als' 
  Mem' B' Rid oResult tr
  (db:bFdef fv rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' B' Rid oResult tr) 
  :=
  forall los nts,
  TD = (los, nts) ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  exists fptrs, exists fptr, exists F, 
    getOperandValue TD fv lc gl = Some fptrs /\
    fptr @ fptrs /\ 
    lookupFdefViaPtr Ps fs fptr = Some F /\
    uniqFdef F /\
    blockInSystemModuleFdef B' S (module_intro los nts Ps) F.

Lemma b_preservation : 
  (forall state1 state2 tr db, @bInsn_preservation_prop state1 state2 tr db) /\
  (forall state1 state2 tr db, @bops_preservation_prop state1 state2 tr  db) /\
  (forall fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ECs db, 
    @bFdef_preservation_prop fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid 
      oResult tr ECs db).
Proof.
(b_mutind_cases
  apply b_mutind with
    (P  := bInsn_preservation_prop)
    (P0 := bops_preservation_prop)
    (P1 := bFdef_preservation_prop) Case);
  unfold bInsn_preservation_prop, 
         bops_preservation_prop, 
         bFdef_preservation_prop; intros; subst.
Case "bBranch".
  inversion H; subst. clear H.
  exists l'. exists ps'. exists cs'. exists tmn'.
  exists lc'. exists als0. exists Mem1.
  exists cs'. split; auto.
  apply andb_true_iff in H1.
  destruct H1.
  eapply andb_true_iff.
  split; auto.
    assert (uniqFdef F0) as UniqF0.
      eapply uniqSystem__uniqFdef with (S:=S0); eauto.
    symmetry in e0.
    destruct (isGVZero (los, nts) c);
      apply lookupBlockViaLabelFromFdef_inv in e0;
      destruct e0; auto.

Case "bBranch_uncond".
  inversion H; subst. clear H.
  exists l'. exists ps'. exists cs'. exists tmn'.
  exists lc'. exists als0. exists Mem1.
  exists cs'. split; auto.
  apply andb_true_iff in H1.
  destruct H1.
  eapply andb_true_iff.
  split; auto.
    assert (uniqFdef F0) as UniqF0.
      eapply uniqSystem__uniqFdef with (S:=S0); eauto.
    symmetry in e.
    apply lookupBlockViaLabelFromFdef_inv in e; auto.
    destruct e; auto.

Case "bBop".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "bFBop".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "bExtractValue".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv'). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "bInsertValue".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv''). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "bMalloc".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 ($ blk2GV (los, nts) mb # typ_pointer t $)). 
  exists als0. exists Mem'. exists cs1. split; auto.

Case "bFree".
  inversion H; subst. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists Mem'.
  exists cs1. split; auto.

Case "bAlloca".
  inversion H; subst. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 (($ blk2GV (los, nts) mb # typ_pointer t $))). 
  exists (mb::als0). exists Mem'. exists cs1. split; auto.

Case "bLoad".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 ($ gv # t $)). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "bStore".
  inversion H; subst. 
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists Mem'.
  exists cs1. split; auto.

Case "bGEP".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 mp'). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "bTrunc".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv2). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "bExt".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv2). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "bCast".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv2). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "bIcmp".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "bFcmp".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.

Case "bSelect".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists (if isGVZero (los, nts) c 
          then updateAddAL _ lc0 id0 gv2 else updateAddAL _ lc0 id0 gv1). 
  exists als0. exists Mem1. exists cs1. split; auto.

Case "bCall".
  inversion H0; subst. clear H0.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc''. exists als0. exists Mem''.
  exists cs1. split; auto.
 
Case "bExCall".
  inversion H; subst.
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc'. exists als0. exists Mem'.
  exists cs1. split; auto.

Case "bops_nil".
  inversion H0; subst. auto.
  
Case "bops_cons".
  apply H with (cs1:=cs)(lc0:=lc)(als0:=als)(ECs0:=ECs)(gl0:=gl)
    (fs0:=fs)(Mem:=Mem0) in H4; auto.
  clear H.
  destruct H4 as [l1 [ps1 [cs1 [tmn1 [lc1 [als1 [Mem1 [cs1' [EQ H4]]]]]]]]]; 
    subst.
  eapply H0; eauto.

Case "bFdef_func".
  exists fptrs. exists fptr.
  exists (fdef_intro (fheader_intro fa rt fid la va) lb).
  split; auto.
  split; auto.
  split; auto.
  split.
    eapply lookupFdefViaPtr_uniq; eauto.
    eapply H with (lc'0:=lc')(cs'0:=nil)(als'0:=als')(gl':=gl)(fs':=fs)
      (Mem'0:=Mem'); 
      eauto using entryBlockInSystemBlockFdef''.   

Case "bFdef_proc".
  exists fptrs. exists fptr.
  exists (fdef_intro (fheader_intro fa rt fid la va) lb).
  split; auto.
  split; auto.
  split; auto.
  split.
    eapply lookupFdefViaPtr_uniq; eauto.
    eapply H; eauto using entryBlockInSystemBlockFdef''.
Qed.

Lemma _bInsn_preservation : forall state2 tr S los nts Ps F l ps cs tmn lc als 
  ECs gl fs Mem cs0,
  bInsn ((mkState S (los, nts) Ps ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc 
    als)::ECs) gl fs Mem)) state2 tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps) 
    F ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists Mem', exists cs0',
  state2 = (mkState S (los, nts) Ps ((mkEC F (block_intro l' ps' cs0' tmn') cs' 
    tmn' lc' als')::ECs) gl fs Mem') /\
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S 
    (module_intro los nts Ps) F.
Proof.
  intros.
  destruct b_preservation as [J _].
  unfold bInsn_preservation_prop in J.
  eapply J; eauto.
Qed.

Lemma bInsn_preservation : forall tr S los nts Ps F l ps cs tmn lc als ECs gl 
    fs Mem cs0 l' ps'  cs' tmn' lc' als' gl' fs' Mem' cs0',
  bInsn 
    ((mkState S (los, nts) Ps 
      ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc als)::ECs) gl fs Mem)) 
    (mkState S (los, nts) Ps 
      ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' als')::ECs) gl' fs' 
        Mem')
    tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps)
    F ->
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S 
    (module_intro los nts Ps) F.
Proof.
  intros.
  apply _bInsn_preservation in H; auto.
  destruct H as [l1 [ps1 [cs1 [tmn1 [lc1 [als1 [Mem1 [cs2 [J1 J2]]]]]]]]].
  inversion J1; subst. clear J1. auto.  
Qed.

Lemma bops_preservation : forall tr S los nts Ps F l ps cs tmn lc als ECs gl
    fs Mem l' ps' cs' tmn' lc' als' gl' fs' Mem' cs0 cs0',
  bops 
    (mkState S (los, nts) Ps 
      ((mkEC F (block_intro l ps cs0 tmn) cs tmn lc als)::ECs) gl fs Mem)
    (mkState S (los, nts) Ps 
      ((mkEC F (block_intro l' ps' cs0' tmn') cs' tmn' lc' als')::ECs) gl' fs' 
        Mem')
    tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps)
    F ->
  blockInSystemModuleFdef (block_intro l' ps' cs0' tmn') S 
    (module_intro los nts Ps) F.
Proof.
  intros.
  destruct b_preservation as [_ [J _]].
  unfold bops_preservation_prop in J.
  eapply J; eauto.
Qed.

Lemma bFdef_preservation : forall fv rt lp S los nts Ps ECs lc gl fs Mem lc' 
    als' Mem' B' Rid oResult tr,
  bFdef fv rt lp S (los, nts) Ps ECs lc gl fs Mem lc' als' Mem' B' Rid oResult tr
    ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  exists fptrs, exists fptr, exists F, 
    getOperandValue (los, nts) fv lc gl = Some fptrs /\
    fptr @ fptrs /\ 
    lookupFdefViaPtr Ps fs fptr = Some F /\
    uniqFdef F /\
    blockInSystemModuleFdef B' S (module_intro los nts Ps) F.
Proof.
  intros.
  destruct b_preservation as [_ [_ J]].
  unfold bFdef_preservation_prop in J.
  eapply J; eauto.
Qed.

End OpsemProps.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
