Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import ssa_def.
Require Import ssa_lib.
Require Import trace.
Require Import List.
Require Import tactics.
Require Import Coq.Program.Equality.
Require Import CoqListFacts.
Require Import alist.

Export LLVMsyntax.
Export LLVMlib.
Export LLVMopsem.

Lemma func_callUpdateLocals_is_returnUpdateLocals : 
  forall TD Mem rid noret0 tailc0 ft fid lp Result lc lc' gl,
  returnUpdateLocals TD Mem (insn_call rid noret0 tailc0 ft fid lp) Result 
    lc lc' gl =
  callUpdateLocals TD Mem noret0 rid (Some Result) lc' lc gl.
Proof.
  intros.
  unfold returnUpdateLocals. 
  unfold callUpdateLocals.
  simpl. 
  destruct noret0; auto.
Qed.

Lemma proc_callUpdateLocals_is_id : forall TD Mem rid noret0 lc lc' gl lc'',
  callUpdateLocals TD Mem noret0 rid None lc' lc gl = Some lc'' -> lc' = lc''.
Proof.
  intros.
  unfold callUpdateLocals in H. 
  destruct noret0; inversion H; auto.
Qed.

(***********************************************************)
(** det small-step                                         *)

Lemma dsInsn__implies__dsop_star : forall state state' tr,
  dsInsn state state' tr ->
  dsop_star state state' tr.
Proof.
  intros state state' tr HdsInsn.
  rewrite <- trace_app_nil__eq__trace.
  eapply dsop_star_cons; eauto.
Qed.

Lemma dsInsn__implies__dsop_plus : forall state state' tr,
  dsInsn state state' tr ->
  dsop_plus state state' tr.
Proof.
  intros state state' tr HdsInsn.
  rewrite <- trace_app_nil__eq__trace.
  eapply dsop_plus_cons; eauto.
Qed.

Lemma dsop_plus__implies__dsop_star : forall state state' tr,
  dsop_plus state state' tr ->
  dsop_star state state' tr.
Proof.
  intros state state' tr Hdsop_plus.
  inversion Hdsop_plus; subst; eauto.
Qed.

Hint Resolve dsInsn__implies__dsop_star dsInsn__implies__dsop_plus dsop_plus__implies__dsop_star. 

Lemma dsop_star_trans : forall state1 state2 state3 tr12 tr23,
  dsop_star state1 state2 tr12 ->
  dsop_star state2 state3 tr23 ->
  dsop_star state1 state3 (trace_app tr12 tr23).
Proof.
  intros state1 state2 state3 tr12 tr23 Hdsop12 Hdsop23.
  generalize dependent state3.
  generalize dependent tr23.
  induction Hdsop12; intros; auto.
    rewrite <- trace_app_commute.
    apply dsop_star_cons with (state2:=state2); auto.
Qed.

Lemma dsop_diverging_trans : forall state tr1 state' tr2,
  dsop_star state state' tr1 ->
  dsop_diverges state' tr2 ->
  dsop_diverges state (Trace_app tr1 tr2).
Proof. 
  intros state tr1 state' tr2 state_dsop_state' state'_dsop_diverges.
  generalize dependent tr2.
  (dsop_star_cases (induction state_dsop_state') Case); intros; auto.
  Case "dsop_star_cons".
    rewrite <- Trace_app_commute.
    apply dsop_diverges_intro with (state2:=state2); auto.
Qed.

(***********************************************************)
(** nondet small-step                                      *)

Lemma nsop_star_split : forall states1 states2 states',
  nsop_star (states1++states2) states' ->
  exists states1', exists states2',
    nsop_star states1 states1' /\
    nsop_star states2 states2' /\
    states' = states1'++states2'.
Proof.
  intros states1 states2 states' H.
  dependent induction H.
    exists states1. exists states2. auto.

    apply cons_eq_app in x.
    destruct x as [[states4 [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (states4++states2~=states4++states2) as EQ. auto.
      apply IHnsop_star in EQ; auto.
      destruct EQ as [states1' [states2' [J1 [J2 EQ]]]]; subst.
      exists ((state, tr)::states1'). exists states2'.
      split; auto.

      exists nil. exists ((state, tr)::states').
      split; auto.

    apply cons_eq_app in x.
    destruct x as [[states4 [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (states4++states2~=states4++states2) as EQ. auto.
      apply IHnsop_star in EQ; auto.
      destruct EQ as [states1' [states2' [J1 [J2 EQ]]]]; subst.
      exists (states0++states1'). exists states2'.
      split; auto. split; auto. apply ass_app.

      exists nil. exists (states0++states3).
      split; auto.

    destruct (@IHnsop_star1 states1 states2) as [states1' [states2' [J1 [J2 EQ]]]]; subst; auto.
    assert (states1'++states2'~=states1'++states2') as EQ. auto.
    apply IHnsop_star2 in EQ; auto.
    destruct EQ as [states1'' [states2'' [J1' [J2' EQ]]]]; subst.
    exists states1''. exists states2''.
    split; eauto.
Qed.

Lemma nsop_plus__implies__nsop_star : forall states states',
  nsop_plus states states' ->
  nsop_star states states'.
Proof.
  intros states states' Hnsop_plus.
  induction Hnsop_plus; subst; eauto.
Qed.

Lemma nsop_star_merge_tail : forall states1 states2 states2',
  nsop_star states2 states2' ->
  nsop_star (states1++states2) (states1++states2').
Proof.
  induction states1; intros states2 states2' H2; simpl; auto.
    destruct a.
    assert ((s,t)::states1++states2'=((s,t)::nil)++states1++states2') as EQ. auto.
    rewrite EQ.
    apply nsop_star_refl; auto.
Qed.

Lemma nsop_star_merge : forall states1 states2 states1' states2',
  nsop_star states1 states1' ->
  nsop_star states2 states2' ->
  nsop_star (states1++states2) (states1'++states2').
Proof.
  intros states1 states2 states1' states2' H1 H2.
  generalize dependent states2.
  generalize dependent states2'.
  (nsop_star_cases (induction H1) Case); intros; simpl; auto.
  Case "nsop_star_nil".
    apply nsop_star_merge_tail; auto.
  Case "nsop_star_cons".
    rewrite app_ass.
    apply nsop_star_cons; auto.
  Case "nsop_star_trans".
    apply nsop_star_trans with (states2:=states2++states2'); auto.
Qed.

Lemma nsop_plus_star_merge : forall states1 states2 states1' states2',
  nsop_plus states1 states1' ->
  nsop_star states2 states2' ->
  nsop_plus (states1++states2) (states1'++states2').
Proof.
  intros states1 states2 states1' states2' H1 H2.
  (nsop_plus_cases (induction H1) Case); intros; simpl; subst.
  Case "nsop_plus_cons".
    rewrite app_ass.
    apply nsop_plus_cons; auto.
      apply nsop_star_merge; auto.
  Case "nsop_plus_trans".
    apply nsop_plus_trans with (states2:=states0++states2'); auto.
      apply nsop_star_merge; auto.
Qed.

Hint Resolve nsop_plus__implies__nsop_star. 

(***********************************************************)
(** det big-step convergence -> det small-step convergence *)

(** First, by mutual induction, we prove that dbInsn, dbop and  
    dbFdef imply small-step semantics. *)

Definition dbInsn__implies__dsop_plus_prop state state' tr (db:dbInsn state state' tr) := 
  dsop_plus state state' tr.
Definition dbop__implies__dsop_star_prop state state' tr (db:dbop state state' tr) := 
  dsop_star state state' tr.
Definition dbFdef__implies__dsop_star_prop fv rt lp S TD Ps ECs lc gl fs Mem lc'
als' Mem' B'' rid oResult tr 
(db:dbFdef fv rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' B'' rid oResult tr) 
  := 
  match oResult with
  | Some Result => forall fid l' ps' cs' tmn' fa la va lb,
    lookupFdefViaGV TD Mem Ps gl lc fs fv =
      Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
    getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
      Some (block_intro l' ps' cs' tmn') ->
    dsop_star
      (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                              (block_intro l' ps' cs' tmn') cs' tmn' 
                              (initLocals la (params2GVs TD Mem lp lc gl))
                               nil)::ECs) gl fs Mem)
      (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                               B'' nil (insn_return rid rt Result) lc'
                               als')::ECs) gl fs 
                               Mem')
      tr
  | None => forall fid l' ps' cs' tmn' fa la va lb,
    lookupFdefViaGV TD Mem Ps gl lc fs fv = 
      Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
    getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
      Some (block_intro l' ps' cs' tmn') ->  
    dsop_star
      (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                              (block_intro l' ps' cs' tmn') cs' tmn' 
                              (initLocals la (params2GVs TD Mem lp lc gl))
                              nil)::ECs) gl fs Mem)
      (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                               B'' nil (insn_return_void rid) lc'
                               als')::ECs) gl fs 
                               Mem')
      tr
  end
  .

Lemma db__implies__ds:
  (forall state state' t  db, @dbInsn__implies__dsop_plus_prop state state' t db)
    /\
  (forall state state' t  db, @dbop__implies__dsop_star_prop state state' t db) 
    /\
  (forall fv rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' B'' rid oret tr db, 
     @dbFdef__implies__dsop_star_prop fv rt lp S TD Ps ECs lc gl fs Mem lc' als' 
       Mem' B'' rid oret tr db).
Proof.
(db_mutind_cases
  apply db_mutind with
    (P  := dbInsn__implies__dsop_plus_prop)
    (P0 := dbop__implies__dsop_star_prop)
    (P1 := dbFdef__implies__dsop_star_prop)
    Case);
  unfold dbInsn__implies__dsop_plus_prop, 
         dbop__implies__dsop_star_prop, 
         dbFdef__implies__dsop_star_prop; 
  intros; subst; simpl; intuition; eauto.
  Case "dbCall".
    inversion d; subst.
    SCase "dbFdef_func".
    assert (Hlookup:=H0).
    apply H with (l':=l')(ps':=ps')(cs':=cs')(tmn':=tmn') in H0; auto.
    rewrite <- nil_app_trace__eq__trace.
    apply dsop_plus_cons with 
      (state2:=mkState S TD Ps 
                       ((mkEC (fdef_intro (fheader_intro fa rt fid la va)lb)
                               (block_intro l' ps' cs' tmn') cs' tmn' 
                               (initLocals la (params2GVs TD Mem0 lp lc gl)) 
                               nil)::
                        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) 
                         tmn lc als)::EC) 
                        gl fs Mem0); auto.
    rewrite <- trace_app_nil__eq__trace.
    apply dsop_star_trans with 
      (state2:=mkState S TD Ps 
                       ((mkEC (fdef_intro (fheader_intro fa rt fid la va)lb)
                               (block_intro l'' ps'' cs'' 
                                (insn_return Rid rt Result)) nil 
                                (insn_return Rid rt Result) lc'
                                als')::
                        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) 
                         tmn lc als)::EC) 
                         gl fs Mem'); auto.
      apply dsInsn__implies__dsop_star.
        apply dsReturn; auto.
          erewrite func_callUpdateLocals_is_returnUpdateLocals; eauto.

    SCase "dbFdef_proc".
    assert (Hlookup:=H0).
    apply H with (l':=l')(ps':=ps')(cs':=cs')(tmn':=tmn') in H0; auto.
    rewrite <- nil_app_trace__eq__trace.
    apply dsop_plus_cons with 
      (state2:=mkState S TD Ps 
                        ((mkEC (fdef_intro (fheader_intro fa rt fid la va)lb)
                               (block_intro l' ps' cs' tmn') cs' tmn' 
                                (initLocals la (params2GVs TD Mem0 lp lc gl)) 
                                nil)::
                        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) 
                         tmn lc als)::EC) 
                        gl fs Mem0); auto.
    rewrite <- trace_app_nil__eq__trace.
    apply proc_callUpdateLocals_is_id in e0; subst.
    apply dsop_star_trans with 
      (state2:=mkState S TD Ps 
                       ((mkEC (fdef_intro (fheader_intro fa rt fid la va)lb)
                               (block_intro l'' ps'' cs'' (insn_return_void Rid))
                                nil (insn_return_void Rid) lc'
                                als')::
                        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) 
                         tmn lc'' als)::EC) 
                        gl fs Mem'); auto.

  Case "dbop_cons".
    apply dsop_star_trans with (state2:=S2); auto.
        
  Case "dbFdef_func".
    rewrite H0 in e. inversion e; subst.
    rewrite H1 in e0. inversion e0; subst.
    exact H.

  Case "dbFdef_proc".
    rewrite H0 in e. inversion e; subst.
    rewrite H1 in e0. inversion e0; subst.
    exact H.
Qed.  
    
Lemma dbInsn__implies__dsop_plus : forall state state' tr,
  dbInsn state state' tr ->
  dsop_plus state state' tr.
Proof.
  destruct db__implies__ds as [J _]. eauto.
Qed.

Lemma dbInsn__implies__dsop_star : forall state state' tr,
  dbInsn state state' tr ->
  dsop_star state state' tr.
Proof. 
  intros state state' tr state_dbInsn_state'.
  apply dbInsn__implies__dsop_plus in state_dbInsn_state'; auto.
Qed.

Lemma dbop__implies__dsop_star : forall state state' tr,
  dbop state state' tr ->
  dsop_star state state' tr.
Proof.
  destruct db__implies__ds as [_ [J _]]. eauto.
Qed.

Lemma dbFdef_func__implies__dsop_star : forall fv fid rt lp S TD Ps ECs lc gl fs
    Mem lc' als' Mem' B'' rid Result tr l' ps' cs' tmn' fa la va lb,
  dbFdef fv rt lp S TD Ps ECs lc gl fs Mem lc' als' Mem' B'' rid (Some Result) 
    tr ->
  lookupFdefViaGV TD Mem Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  dsop_star 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             (block_intro l' ps' cs' tmn') cs' tmn' 
                             (initLocals la (params2GVs TD Mem lp lc gl))
                             nil)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             B'' nil (insn_return rid rt Result) lc'
                             als')::ECs) gl fs Mem')
    tr.
Proof.
  intros fv fid rt lp S TD Ps EC lc gl fs Mem0 lc' als' Mem' B'' rid Result tr 
    l' ps' cs' tmn' fa la va lb H H1 H2.
  destruct db__implies__ds as [_ [_ J]]. 
  assert (K:=@J fv rt lp S TD Ps EC lc gl fs Mem0 lc' als' Mem' B'' rid 
    (Some Result) tr H fid l' ps' cs' tmn' fa la va lb H1 H2); auto.
Qed.

Lemma dbFdef_proc__implies__dsop_star : forall fv fid rt lp S TD Ps ECs lc gl fs
    Mem lc' als' Mem' B'' rid tr l' ps' cs' tmn' fa la va lb,
  dbFdef fv rt lp S TD Ps ECs lc gl fs  Mem lc' als' Mem' B'' rid None tr ->
  lookupFdefViaGV TD Mem Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  dsop_star 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                            (block_intro l' ps' cs' tmn') cs' tmn' 
                            (initLocals la (params2GVs TD Mem lp lc gl))
                            nil)::ECs) gl fs Mem)
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             B'' nil (insn_return_void rid) lc'
                             als')::ECs) gl fs Mem')
    tr.
Proof.
  intros fv fid rt lp S TD Ps EC lc gl fs Mem0 lc' als' Mem' B'' rid tr l' ps' 
    cs' tmn' fa la va lb H H1 H2.
  destruct db__implies__ds as [_ [_ J]]. 
  assert (K:=@J fv rt lp S TD Ps EC lc gl fs Mem0 lc' als' Mem' B'' rid None tr 
    H fid l' ps' cs' tmn' fa la va lb H1 H2); auto.
Qed.

(** Then we prove that the whole program holds the same property. *)

Lemma db_converges__implies__ds_converges : forall sys main VarArgs FS,
  db_converges sys main VarArgs FS ->
  ds_converges sys main VarArgs FS.
Proof.
  intros sys main VarArgs FS Hdb_converges.
  inversion Hdb_converges; subst.
  apply ds_converges_intro with (IS:=IS)(tr:=tr); auto.
  apply dbop__implies__dsop_star; auto.
Qed.

Lemma db_goeswrong__implies__ds_goeswrong : forall sys main VarArgs FS,
  db_goeswrong sys main VarArgs FS ->
  ds_goeswrong sys main VarArgs FS.
Proof.
  intros sys main VarArgs FS Hdb_goeswrong.
  inversion Hdb_goeswrong; subst.
  apply ds_goeswrong_intro with (IS:=IS)(tr:=tr); auto.
  apply dbop__implies__dsop_star; auto.
Qed.

(***********************************************************)
(** det big-step divergence -> det small-step divergence *)

(** First,we prove that dbInsn, dbop and dbFdef imply small-step semantics,
    by nested coinduction. *)

Lemma dbFdefInf__implies__dsop_diverges : forall fv fid rt lp S TD Ps ECs lc gl 
    fs Mem tr l' ps' cs' tmn' fa la va lb,
  dbFdefInf fv rt lp S TD Ps ECs lc gl fs Mem tr ->
  lookupFdefViaGV TD Mem Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  dsop_diverges 
    (mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                        (block_intro l' ps' cs' tmn') cs' tmn'
                        (initLocals la (params2GVs TD Mem lp lc gl)) 
                        nil)::ECs) gl fs Mem)
    tr.
Proof.
  cofix CIH_dbFdefInf.

  assert (forall state tr, 
          dbInsnInf state tr -> 
          dsop_diverges state tr) as dbInsnInf__implies__dsop_diverges.
    cofix CIH_dbInsnInf.
    intros state tr HdbInsnInf.
    
    inversion HdbInsnInf; subst.
    rewrite <- nil_app_Trace__eq__Trace.
    assert (HdbFdefInf:=H).
    inversion H; subst.
    apply dsop_diverges_intro with 
      (state2:=mkState S TD Ps 
                       ((mkEC (fdef_intro (fheader_intro fa rt fid la va)lb)
                               (block_intro l' ps' cs' tmn') cs' tmn' 
                               (initLocals la (params2GVs TD Mem0 lp lc gl)) 
                               nil)::
                        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) 
                         tmn lc als)::EC) 
                         gl fs Mem0); 
      try solve [clear CIH_dbFdefInf CIH_dbInsnInf; auto].
      apply CIH_dbFdefInf with (fid:=fid)(l':=l')(ps':=ps')(cs':=cs')(tmn':=tmn')
        (fa:=fa)(la:=la)(va:=va)(lb:=lb) in HdbFdefInf; auto.

  assert (forall state tr, 
          dbopInf state tr -> 
          dsop_diverges state tr) as dbopInf__implies__dsop_diverges.
    cofix CIH_dbopInf.
    intros state tr HdbopInf.
    inversion HdbopInf; subst.
    Case "dbopInf_insn".
      apply dbInsnInf__implies__dsop_diverges in H; auto.
    Case "dbopInf_cons".
      apply dbInsn__implies__dsop_plus in H.
      inversion H; subst.
      SCase "dsop_plus_cons".
        apply CIH_dbopInf in H0. clear CIH_dbopInf.
        apply dsop_diverges_intro with (state2:=state2); auto.

  intros fv fid rt lp S TD Ps ECs lc gl fs Mem0 tr l' ps' cs' tmn' fa la va lb 
    HdbFdefInf Hlookup HgetEntryBlock.
  inversion HdbFdefInf; subst.
  rewrite Hlookup in H. inversion H; subst.
  rewrite HgetEntryBlock in H0. inversion H0; subst.
  apply dbopInf__implies__dsop_diverges in H1.
  exact H1.
Qed.

Lemma dbInsnInf__implies__dsop_diverges : forall state tr, 
  dbInsnInf state tr -> dsop_diverges state tr.
Proof.
  cofix CIH_dbInsnInf.
  intros state tr HdbInsnInf.
    
  inversion HdbInsnInf; subst.
  rewrite <- nil_app_Trace__eq__Trace.
  assert (HdbFdefInf:=H).
  inversion H; subst.
  apply dsop_diverges_intro with 
    (state2:=mkState S TD Ps 
                     ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb)
                             (block_intro l' ps' cs' tmn') cs' tmn' 
                             (initLocals la (params2GVs TD Mem0 lp lc gl)) 
                             nil)::
                      (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) tmn
                       lc als)::EC) 
                       gl fs Mem0); 
    try solve [clear CIH_dbInsnInf; auto].
    apply dbFdefInf__implies__dsop_diverges with (fid:=fid)(l':=l')(ps':=ps')
      (cs':=cs')(tmn':=tmn')(la:=la)(va:=va)(lb:=lb)(fa:=fa)in HdbFdefInf; auto.
Qed.

Lemma dbopInf__implies__dsop_diverges : forall state tr, 
  dbopInf state tr -> dsop_diverges state tr.
Proof.
  cofix CIH_dbopInf.
  intros state tr HdbopInf.
  inversion HdbopInf; subst.
  Case "dbopInf_insn".
    apply dbInsnInf__implies__dsop_diverges in H; auto.
  Case "dbopInf_cons".
    apply dbInsn__implies__dsop_plus in H.
    inversion H; subst.
    SCase "dsop_plus_cons".
      apply CIH_dbopInf in H0. clear CIH_dbopInf.
      apply dsop_diverges_intro with (state2:=state2); auto.
Qed.

(** Then we prove that the whole program holds the same property. *)

Lemma db_diverges__implies__ds_diverges : forall sys main VarArgs tr, 
  db_diverges sys main VarArgs tr ->
  ds_diverges sys main VarArgs tr.
Proof.
  intros sys main VarArgs tr Hdb_diverges.
  inversion Hdb_diverges; subst.
  apply ds_diverges_intro with (IS:=IS)(tr:=tr); auto.
  apply dbopInf__implies__dsop_diverges; auto.
Qed.

(*****************************************************************)
(** nondet big-step convergence -> nondet small-step convergence *)

(** First, by mutual induction, we prove that nbInsn, nbop and  
    nbFdef imply small-step semantics. *)

Definition nbInsn__implies__nsop_plus_prop state_tr states' 
  (nb:nbInsn state_tr states') := nsop_plus (state_tr::nil) states'.
Definition nbop_star__implies__nsop_star_prop states states' 
  (nb:nbop_star states states') := 
  nsop_star states states'.
Definition nbFdef__implies__nsop_star_prop fv rt lp S TD Ps ECs lc gl fs Mem tr 
lc_gl_als_Mem_block_rid_ore_trs 
(nb:nbFdef fv rt lp S TD Ps ECs lc gl fs Mem tr lc_gl_als_Mem_block_rid_ore_trs)
  := 
  forall fid l' ps' cs' tmn' fa la va lb,
  lookupFdefViaGV TD Mem Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  nsop_star
    ((mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                            (block_intro l' ps' cs' tmn') cs' tmn' 
                            (initLocals la (params2GVs TD Mem lp lc gl))
                            nil)::ECs) gl fs Mem, 
                             tr)::nil)
    (returnStatesFromOp S TD Ps ECs gl fs fa rt fid la va lb 
      lc_gl_als_Mem_block_rid_ore_trs)
  .

Lemma getOperandValue_free_allocas : forall TD Mem v lc gl als Mem',
  free_allocas TD Mem als = Some Mem' ->
  getOperandValue TD Mem v lc gl = getOperandValue TD Mem' v lc gl.
Admitted.

Lemma returnStatesFromOp__nsop_star__updateStatesFromReturns : 
forall lc_als_Mem_block_rid_ore_trs S TD Ps F B rid noret tailc (rt:typ) fv 
  (fid:id) lp (lc:GVMap) als EC cs tmn lc gl fs ft fid la va lb states fa,
  updateStatesFromReturns S TD Ps F B cs tmn lc gl fs rid als EC noret 
    lc_als_Mem_block_rid_ore_trs = Some states ->
  nsop_star
    (returnStatesFromOp S TD Ps (mkEC F B ((insn_call rid noret tailc ft fv lp)::
      cs) tmn lc als::EC)
      gl fs fa rt fid la va lb lc_als_Mem_block_rid_ore_trs)
    states.
Proof.
  induction lc_als_Mem_block_rid_ore_trs; simpl; intros.
  inversion H; subst; auto.

  destruct a as [p tr]. 
  destruct p as [p ore]. 
  destruct p as [p Rid]. 
  destruct p as [p B'']. 
  destruct p as [p Mem']. 
  destruct p as [lc' als'].
  destruct ore as [ re | ].
  Case "ore = Some re".    
    destruct noret0.
    SCase "noret = true".
      remember (free_allocas TD Mem' als') as Mem''.
      destruct Mem''; simpl in H; try solve [inversion H; subst].
      remember (updateStatesFromReturns S TD Ps F B cs tmn lc0 gl fs rid als
        EC true lc_als_Mem_block_rid_ore_trs) as states2.
      destruct states2; simpl in H; inversion H; subst.
      assert (
        (mkState S TD Ps (mkEC F B cs tmn lc0 als::EC) gl fs m, tr)::s = 
        ((mkState S TD Ps (mkEC F B cs tmn lc0 als::EC) 
          gl fs m, tr)::nil) ++ s
      ) as EQ. auto.
      rewrite EQ.
      apply nsop_star_cons; auto.

    SCase "noret=false".
      remember (getOperandValue TD Mem' re lc' gl) as ogv.
      destruct ogv as [g |]; try solve [inversion H].
      remember (free_allocas TD Mem' als') as Mem''.
      destruct Mem''; simpl in H; try solve [inversion H].
      remember (updateStatesFromReturns S TD Ps F B cs tmn lc0 gl fs rid 
        als EC false lc_als_Mem_block_rid_ore_trs) as states2.
      destruct states2; simpl in H; inversion H; subst.
      assert (
        (mkState S TD Ps (mkEC F B cs tmn (alist.updateAddAL _ lc0 rid g) 
                           als::EC) gl fs m, tr)::s = 
        ((mkState S TD Ps (mkEC F B cs tmn (alist.updateAddAL _ lc0 rid g) 
                            als::EC) gl fs m, tr)::nil) 
          ++ s
      ) as EQ. simpl. auto.
      rewrite EQ.
      apply nsop_star_cons; auto.
        apply nsReturn; auto.
          unfold returnUpdateLocals. 
          rewrite <- getOperandValue_free_allocas with (Mem:=Mem')(als:=als'); auto.
          rewrite <- Heqogv; auto.

   Case "ore = None".    
    destruct noret0.
    SCase "noret = true".
      remember (free_allocas TD Mem' als') as Mem''.
      destruct Mem''; simpl in H; try solve [inversion H; subst].
      remember (updateStatesFromReturns S TD Ps F B cs tmn lc0 gl fs rid 
        als EC true lc_als_Mem_block_rid_ore_trs) as states2.
      destruct states2; simpl in H; inversion H; subst.
      assert (
        (mkState S TD Ps (mkEC F B cs tmn lc0 als::EC) gl fs m, tr)::s = 
        ((mkState S TD Ps (mkEC F B cs tmn lc0 als::EC) gl fs m, tr)::nil) 
          ++ s
      ) as EQ. auto.
      rewrite EQ.
      apply nsop_star_cons; auto.

    SCase "noret = flase".
      remember (free_allocas TD Mem' als') as Mem''.
      destruct Mem''; simpl in H; try solve [inversion H; subst].
      remember (updateStatesFromReturns S TD Ps F B cs tmn lc0 gl fs rid 
        als EC false lc_als_Mem_block_rid_ore_trs) as states2.
      destruct states2; simpl in H; inversion H; subst.
      assert (
        (mkState S TD Ps (mkEC F B cs tmn lc0 als::EC) gl fs m, tr)::s = 
        ((mkState S TD Ps (mkEC F B cs tmn lc0 als::EC) gl fs m, tr)::nil) 
         ++ s
      ) as EQ. auto.
      rewrite EQ.
      apply nsop_star_cons; auto.
Qed.

Lemma nb__implies__ns:
  (forall state_tr states' nb, 
     @nbInsn__implies__nsop_plus_prop state_tr states' nb) /\
  (forall states states' nb, 
     @nbop_star__implies__nsop_star_prop states states' nb) /\
  (forall fv rt lp S TD Ps ECs lc gl fs Mem tr lc_Mem_block_re_trs nb, 
     @nbFdef__implies__nsop_star_prop fv rt lp S TD Ps ECs lc gl fs Mem tr 
       lc_Mem_block_re_trs nb).
Proof.
(nb_mutind_cases
  apply nb_mutind with
    (P  := nbInsn__implies__nsop_plus_prop)
    (P0 := nbop_star__implies__nsop_star_prop)
    (P1 := nbFdef__implies__nsop_star_prop)
    Case);
  unfold nbInsn__implies__nsop_plus_prop, 
         nbop_star__implies__nsop_star_prop, 
         nbFdef__implies__nsop_star_prop; 
  intros; subst; simpl; 
    try solve [intuition].
  Case "nbBranch_def".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps 
      (mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' als::EC) gl fs Mem0
       , tr)::nil); auto.
      rewrite app_nil_end; eauto.
  Case "nbBranch_undef".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps 
      (mkEC F (block_intro l1' ps1' cs1' tmn1') cs1' tmn1' lc1' als::EC) gl
        fs Mem0, tr)::
      (mkState S TD Ps (mkEC F (block_intro l2' ps2' cs2' tmn2') cs2' tmn2' lc2'
        als::EC) gl fs Mem0, tr)::nil); auto.
      rewrite app_nil_end; eauto.
  Case "nbBranch_uncond".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps 
      (mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' als::EC) gl fs Mem0
       , tr)::nil); auto.
      rewrite app_nil_end; eauto.
  Case "nbBop".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 gv3) als::EC) gl fs Mem0, tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].
  Case "nbFBop".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 gv3) als::EC) gl fs Mem0, tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].
  Case "nbExtractValue".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 gv') als::EC) gl fs Mem0, tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].
  Case "nbInsertValue".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 gv'') als::EC) gl fs Mem0, tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].
  Case "nbMalloc".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 (blk2GV TD mb)) als::EC) gl fs Mem', tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].
  Case "nbFree".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn lc 
      als::EC) gl fs Mem', tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].
  Case "nbAlloca".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 (blk2GV TD mb)) (mb::als)::EC) gl fs Mem', tr)
      ::nil); auto.
      rewrite app_nil_end; eauto.
  Case "nbLoad".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 gv) als::EC) gl fs Mem0, tr)::nil); auto.
      rewrite app_nil_end; eauto.
  Case "nbStore".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn lc 
      als::EC) gl fs Mem', tr)::nil); auto.
      rewrite app_nil_end; eauto.
  Case "nbGEP".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 mp') als::EC) gl fs Mem0, tr)::nil); auto.
      rewrite app_nil_end; eauto.
  Case "nbTrunc".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 gv2) als::EC) gl fs Mem0, tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].
  Case "nbExt".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 gv2) als::EC) gl fs Mem0, tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].
  Case "nbCast".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 gv2) als::EC) gl fs Mem0, tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].
  Case "nbIcmp".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 gv3) als::EC) gl fs Mem0, tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].
  Case "nbFcmp".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (updateAddAL _ lc id0 gv3) als::EC) gl fs Mem0, tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].
  Case "nbSelect".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      (if isGVZero TD c then updateAddAL _ lc id0 gv2 
       else updateAddAL _ lc id0 gv1) als::EC) gl fs Mem0, tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].
  Case "nbCall".
    inversion n. subst.
    assert (Hlookup:=H0).
    apply H with (l':=l')(ps':=ps')(cs':=cs')(tmn':=tmn') in H0; auto.
    apply nsop_plus_trans with 
      (states2:=(mkState S TD Ps ((mkEC 
        (fdef_intro (fheader_intro fa rt fid la va) lb)
        (block_intro l' ps' cs' tmn') cs' tmn' 
        (initLocals la (params2GVs TD Mem0 lp lc gl)) 
        nil)::
        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) tmn lc als)
        ::EC) gl fs Mem0, tr)::nil); auto.
      rewrite app_nil_end; eauto.

      apply nsop_star_trans with 
        (states2:=returnStatesFromOp S TD Ps (mkEC F B 
          ((insn_call rid noret0 ca ft fv lp)::cs) tmn lc als::EC)
          gl fs fa rt fid la va lb lc_als_Mem_block_rid_ore_trs); auto.
      apply returnStatesFromOp__nsop_star__updateStatesFromReturns with (cs:=cs);
        auto.
  Case "nbExCall".
    apply nsop_plus_trans with (states2:=(mkState S TD Ps (mkEC F B cs tmn 
      lc' als::EC) gl fs Mem', tr)::nil); 
      try solve [auto | rewrite app_nil_end; eauto].

  Case "nbop_star_cons".
    assert ((state, tr)::states=((state, tr)::nil)++states) as EQ. auto.
    rewrite EQ.
    apply nsop_star_merge; auto.

  Case "nbop_star_trans".
    apply nsop_star_trans with (states2:=states2); auto.
        
  Case "nbFdef_intro".
    rewrite H0 in e. inversion e; subst.
    rewrite H1 in e0. inversion e0; subst.
    exact H.
Qed.  

Lemma nbInsn__implies__nsop_plus : forall state_tr states',
  nbInsn state_tr states' ->
  nsop_plus (state_tr::nil) states'.
Proof.
  destruct nb__implies__ns as [J _]. eauto.
Qed.

Lemma nbInsn__implies__nsop_star : forall state_tr states',
  nbInsn state_tr states' ->
  nsop_star (state_tr::nil) states'.
Proof. 
  intros state_tr states' state_nbInsn_state'.
  apply nbInsn__implies__nsop_plus in state_nbInsn_state'; auto.
Qed.

Lemma nbop_star__implies__nsop_star : forall states states',
  nbop_star states states' ->
  nsop_star states states'.
Proof.
  destruct nb__implies__ns as [_ [J _]]. eauto.
Qed.

Lemma nbop_plus__implies__nsop_plus : forall states states',
  nbop_plus states states' ->
  nsop_plus states states'.
Proof.
  intros states states' H.
  induction H.
    apply nbInsn__implies__nsop_plus in H.
    apply nbop_star__implies__nsop_star in H0.
    assert (state_tr::states = (state_tr::nil)++states) as EQ. auto.
    rewrite EQ.
    apply nsop_plus_star_merge; auto.

    apply nbop_star__implies__nsop_star in H0.
    apply nsop_plus_trans with (states2:=states2); auto.
Qed.

Lemma nbFdef__implies__nsop_star : forall fv fid rt lp S TD Ps ECs lc gl fs Mem 
  tr lc_gl_als_Mem_block_rid_re_trs l' ps' cs' tmn' fa la va lb,
  nbFdef fv rt lp S TD Ps ECs lc gl fs Mem tr lc_gl_als_Mem_block_rid_re_trs ->
  lookupFdefViaGV TD Mem Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  nsop_star
    ((mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
     (block_intro l' ps' cs' tmn') cs' tmn' 
     (initLocals la (params2GVs TD Mem lp lc gl))
     nil)::ECs) gl fs Mem, tr)::nil)
     (returnStatesFromOp S TD Ps ECs gl fs fa rt fid la va lb 
       lc_gl_als_Mem_block_rid_re_trs)
  .
Proof.
  intros fv fid rt lp S TD Ps ECs lc gl fs Mem0 tr 
    lc_gl_als_Mem_block_rid_re_trs l' ps' cs' tmn' fa la va lb H.
  revert fv rt lp S TD Ps ECs lc gl fs Mem0 tr lc_gl_als_Mem_block_rid_re_trs H 
    fid l' ps' cs' tmn' fa la va lb.
  destruct nb__implies__ns as [_ [_ J]]. eauto.
Qed.

(** Then we prove that the whole program holds the same property. *)

Lemma nb_converges__implies__ns_converges : forall sys main VarArgs FS,
  nb_converges sys main VarArgs FS ->
  ns_converges sys main VarArgs FS.
Proof.
  intros sys main VarArgs FS Hnb_converges.
  inversion Hnb_converges; subst.
  apply ns_converges_intro with (IS:=IS); auto.
  apply nbop_star__implies__nsop_star; auto.
Qed.

Lemma nb_goeswrong__implies__ns_goeswrong : forall sys main VarArgs FS,
  nb_goeswrong sys main VarArgs FS ->
  ns_goeswrong sys main VarArgs FS.
Proof.
  intros sys main VarArgs FS Hnb_goeswrong.
  inversion Hnb_goeswrong; subst.
  apply ns_goeswrong_intro with (IS:=IS); auto.
  apply nbop_star__implies__nsop_star; auto.
Qed.

(***************************************************************)
(** notdet big-step divergence -> notdet small-step divergence *)

(** First,we prove that nbInsn, nbop and nbFdef imply small-step semantics,
    by nested coinduction. *)

Lemma nbFdefInf__implies__nsop_diverges : forall fv fid rt lp S TD Ps ECs lc gl 
  fs Mem tr l' ps' cs' tmn' fa la va lb trs',
  nbFdefInf fv rt lp S TD Ps ECs lc gl fs Mem tr trs' ->
  lookupFdefViaGV TD Mem Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  nsop_diverges 
    ((mkState S TD Ps ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
      (block_intro l' ps' cs' tmn') cs' tmn'
      (initLocals la (params2GVs TD Mem lp lc gl)) 
      nil)::ECs) gl fs Mem, tr)::nil) trs'.
Proof.
  cofix CIH_nbFdefInf.

  assert (forall state_tr trs, 
          nbInsnInf state_tr trs -> 
          nsop_diverges (state_tr::nil) trs) as nbInsnInf__implies__nsop_diverges.
    cofix CIH_nbInsnInf.
    intros state_tr trs HnbInsnInf.
    
    inversion HnbInsnInf; subst.
    assert (HnbFdefInf:=H).
    inversion H; subst.
    apply nsop_diverges_trans with 
      (states':=(mkState S TD Ps ((mkEC 
        (fdef_intro (fheader_intro fa rt fid la va) lb)
        (block_intro l' ps' cs' tmn') cs' tmn' 
        (initLocals la (params2GVs TD Mem0 lp lc gl)) 
        nil)::
        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) tmn lc als)
        ::EC) gl fs Mem0, tr)::nil).
      apply nsop_plus_trans 
        with (states2:=(mkState S TD Ps 
          ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb)
          (block_intro l' ps' cs' tmn') cs' tmn' 
          (initLocals la (params2GVs TD Mem0 lp lc gl)) 
          nil)::
          (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) tmn lc als)
          ::EC) gl fs Mem0, tr)::nil); auto.
        rewrite app_nil_end; eauto.
      
      apply CIH_nbFdefInf with (fid:=fid)(l':=l')(ps':=ps')(cs':=cs')(tmn':=tmn')
        (la:=la)(va:=va)(lb:=lb)(fa:=fa) in HnbFdefInf; auto.

  assert (forall states trs, 
          nbopInf states trs -> 
          nsop_diverges states trs) as nbopInf__implies__nsop_diverges.
    cofix CIH_nbopInf.
    intros states trs HnbopInf.
    inversion HnbopInf; subst.
    Case "nbopInf_cons".
      apply nsop_diverges_cons; auto.
    Case "nbopInf_trans".
      apply nbop_plus__implies__nsop_plus in H.
      apply CIH_nbopInf in H0.
      apply nsop_diverges_trans with (states':=states2); auto.

  intros fv fid rt lp S TD Ps ECs lc gl fs Mem0 tr l' ps' cs' tmn' fa la va lb 
    trs HnbFdefInf Hlookup HgetEntryBlock.
  inversion HnbFdefInf; subst.
  rewrite Hlookup in H. inversion H; subst.
  rewrite HgetEntryBlock in H0. inversion H0; subst.
  apply nbopInf__implies__nsop_diverges in H1.
  exact H1.
Qed.

Lemma nbInsnInf__implies__nsop_diverges : forall state_tr trs, 
  nbInsnInf state_tr trs -> 
  nsop_diverges (state_tr::nil) trs.
Proof.
  cofix CIH_nbInsnInf.
  intros state_tr trs HnbInsnInf.
    
  inversion HnbInsnInf; subst.
  assert (HnbFdefInf:=H).
  inversion H; subst.
  apply nsop_diverges_trans with 
    (states':=(mkState S TD Ps ((mkEC 
      (fdef_intro (fheader_intro fa rt fid la va) lb)
      (block_intro l' ps' cs' tmn') cs' tmn' 
      (initLocals la (params2GVs TD Mem0 lp lc gl)) 
      nil)::
      (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) tmn lc als)::
      EC) gl fs Mem0, tr)::nil).
    apply nsop_plus_trans 
      with (states2:=(mkState S TD Ps 
        ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb)
        (block_intro l' ps' cs' tmn') cs' tmn' 
        (initLocals la (params2GVs TD Mem0 lp lc gl)) 
        nil)::
        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs) tmn lc als)
        ::EC) gl fs Mem0, tr)::nil); auto.
      rewrite app_nil_end; eauto.
    
    apply nbFdefInf__implies__nsop_diverges with (fid:=fid)(l':=l')(ps':=ps')
      (cs':=cs')(tmn':=tmn')(la:=la)(va:=va)(lb:=lb)(fa:=fa) in HnbFdefInf; auto.
Qed.

Lemma nbopInf__implies__nsop_diverges :forall states trs, 
  nbopInf states trs -> 
  nsop_diverges states trs.
Proof.
  cofix CIH_nbopInf.
  intros states trs HnbopInf.
  inversion HnbopInf; subst.
  Case "nbopInf_cons".
    apply nbInsnInf__implies__nsop_diverges in H.
    apply nsop_diverges_cons; auto.
  Case "nbopInf_trans".
    apply nbop_plus__implies__nsop_plus in H.
    apply CIH_nbopInf in H0.
    apply nsop_diverges_trans with (states':=states2); auto.
Qed.

(** Then we prove that the whole program holds the same property. *)

Lemma nb_diverges__implies__ns_diverges : forall sys main VarArgs trs,
  nb_diverges sys main VarArgs trs ->
  ns_diverges sys main VarArgs trs.
Proof.
  intros sys main VarArgs trs Hnb_diverges.
  inversion Hnb_diverges; subst.
  apply ns_diverges_intro with (IS:=IS)(trs:=trs); auto.
  apply nbopInf__implies__nsop_diverges; auto.
Qed.

(***********************************************************)
(** misc *)

(** We cannot prove tr1 and tr2 are equal, because the Leibniz
    equivalence is too strong to reason about infinite objects.
    We should prove tr1 and tr2 are bisimilar, but we also need
    to change semantics with bisimilarity closure. We dont have
    interesting traces now, so we leave this as future work.
*)
Lemma Trace_eq_head__eq_tail : forall tr tr1 tr2,
  Trace_app tr tr1 = Trace_app tr tr2 ->
  tr1 = tr2.
Proof.
Admitted.

(** Potentially useful when proving small-step -> bigstep.
*)
Lemma dbopInf__dsInsn_dbopInf : forall state tr,
  dbopInf state tr ->
  exists state', exists tr1, exists tr2,
    dsInsn state state' tr1 /\ dbopInf state' tr2 /\ Trace_app tr1 tr2 = tr.
Proof.
  intros state tr state_dbopInf.
  inversion state_dbopInf; subst.
Admitted.

Lemma dsInsn_derministic : forall state state1 state2 tr1 tr2,
  dsInsn state state1 tr1 ->
  dsInsn state state2 tr2 ->
  state1 = state2 /\ tr1 = tr2.
Proof.
  intros state state1 state2 tr1 tr2 HdsInsn1.
  generalize dependent state2.
  generalize dependent tr2.
  (dsInsn_cases (induction HdsInsn1) Case); intros tr2 state2 HdsInsn2.
  Case "dsReturn".
    (dsInsn_cases (destruct HdsInsn2) SCase); auto.
    SCase "dsReturn".
Admitted.

Lemma dsop_diverging__im_dsop_diverging : forall state tr1 state' tr2,
  dsop_diverges state (Trace_app tr1 tr2) ->
  dsop_star state state' tr1 ->
  dsop_diverges state' tr2.
Proof.
  intros state tr1 state' tr2 state_dsop_diverges state_dsop_state'.
  induction state_dsop_state'; auto.
    apply IHstate_dsop_state'; auto.
    rewrite <- Trace_app_commute in state_dsop_diverges.
    inversion state_dsop_diverges; subst.
    inversion H1; subst.
    apply dsInsn_derministic with (state2:=state2)(tr2:=tr1) in H2; auto.
    destruct H2; subst.
    rewrite <- Trace_app_commute in H0.
    apply Trace_eq_head__eq_tail in H0; subst.
    rewrite <- H0.
    apply dsop_diverging_trans with (state':=state4)(tr1:=tr6); auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
