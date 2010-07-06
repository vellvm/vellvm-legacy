Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "../../../theory/metatheory".
Require Import ssa_dynamic.
Require Import ssa.
Require Import List.
Require Import tactics.
Require Export Coq.Program.Equality.
Require Export CoqListFacts.

(***********************************************************)
(** trace and Trace                                        *)

Lemma trace_app_nil__eq__trace : forall tr,
  trace_app tr trace_nil = tr.
Proof.
  induction tr; simpl; auto.
    rewrite IHtr. auto.
Qed.

Lemma nil_app_trace__eq__trace : forall tr,
  trace_app trace_nil tr = tr.
Proof. auto. Qed.

Lemma trace_app_commute : forall tr1 tr2 tr3,
  trace_app tr1 (trace_app tr2 tr3) = trace_app (trace_app tr1 tr2) tr3.
Proof.
  induction tr1; intros; simpl; auto.
    rewrite IHtr1. auto.
Qed.

Lemma nil_app_Trace__eq__Trace : forall tr,
  Trace_app trace_nil tr = tr.
Proof. auto. Qed.

Lemma Trace_app_commute : forall tr1 tr2 tr3,
  Trace_app tr1 (Trace_app tr2 tr3) = Trace_app (trace_app tr1 tr2) tr3.
Proof.
  induction tr1; intros; simpl; auto.
    rewrite IHtr1. auto.
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
  intros state state' tr dsop_plus.
  inversion dsop_plus; subst; eauto.
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

    apply cons_eq_app in H0.
    destruct H0 as [[states4 [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (states4++states2=states4++states2) as EQ. auto.
      apply IHnsop_star in EQ; auto.
      destruct EQ as [states1' [states2' [J1 [J2 EQ]]]]; subst.
      exists ((state, tr)::states1'). exists states2'.
      split; auto.

      exists nil. exists ((state, tr)::states').
      split; auto.

    apply cons_eq_app in H1.
    destruct H1 as [[states4 [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (states4++states3=states4++states3) as EQ. auto.
      apply IHnsop_star in EQ; auto.
      destruct EQ as [states1' [states2' [J1 [J2 EQ]]]]; subst.
      exists (states1++states1'). exists states2'.
      split; auto. split; auto. apply ass_app.

      exists nil. exists (states1++states2).
      split; auto.

    assert (states0++states4=states0++states4) as EQ. auto.
    apply IHnsop_star1 in EQ; auto.
    destruct EQ as [states1' [states2' [J1 [J2 EQ]]]]; subst.
    assert (states1'++states2'=states1'++states2') as EQ. auto.
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
Definition dbFdef__implies__dsop_star_prop fid rt lp S M ECs lc gl lc' gl' B'' Result tr 
           (db:dbFdef fid rt lp S M ECs lc gl lc' gl' B'' Result tr) := 
  forall B' I' la lb,
  lookupFdefViaIDFromSystemC S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some B' ->
  getEntryInsn B' = Some I' ->
  dsop_star
    (mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             B' I' (initLocals la (params2GVs lp lc gl))
                            (params2GVs lp lc gl))::ECs) gl)
    (mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             B'' (insn_return rt Result) lc'
                            (params2GVs lp lc gl))::ECs) gl')
    tr
  .

Lemma db__implies__ds:
  (forall state state' t  db, @dbInsn__implies__dsop_plus_prop state state' t db) /\
  (forall state state' t  db, @dbop__implies__dsop_star_prop state state' t db) /\
  (forall fid rt lp S M ECs lc gl lc' gl' B'' ret tr db, 
     @dbFdef__implies__dsop_star_prop fid rt lp S M ECs lc gl lc' gl' B'' ret tr db).
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
  Case "dbCallInsn".
    inversion d. subst.
    assert (Hlookup:=H0).
    apply H with (B'0:=B'0)(I':=I'0) in H0; auto.
    rewrite <- nil_app_trace__eq__trace.
    apply dsop_plus_cons with 
      (state2:=mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb)
                               B'0 I'0 (initLocals la (params2GVs lp lc gl)) 
                               (params2GVs lp lc gl))::
                        (mkEC F B (insn_call rid rt fid lp) lc arg)::EC) 
                        gl); auto.
    rewrite <- trace_app_nil__eq__trace.
    apply dsop_star_trans with 
      (state2:=mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                               B' (insn_return rt Result) lc'
                               (params2GVs lp lc gl))::
                        (mkEC F B (insn_call rid rt fid lp) lc arg)::EC) 
                        gl'); auto.
      apply dsInsn__implies__dsop_star.
      eapply dsReturn; simpl; eauto.
  
  Case "dbop_cons".
    apply dsop_star_trans with (state2:=S2); auto.
        
  Case "dbFdef_intro".
    rewrite H0 in e. inversion e; subst.
    rewrite H1 in e0. inversion e0; subst.
    rewrite H2 in e1. inversion e1; subst.
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

Lemma dbFdef__implies__dsop_star : forall fid rt lp S M ECs lc gl lc' gl' B'' Result tr B' I' la lb,
  dbFdef fid rt lp S M ECs lc gl lc' gl' B'' Result tr ->
  lookupFdefViaIDFromSystemC S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some B' ->
  getEntryInsn B' = Some I' ->
  dsop_star 
    (mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             B' I' (initLocals la (params2GVs lp lc gl))
                            (params2GVs lp lc gl))::ECs) gl)
    (mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             B'' (insn_return rt Result) lc'
                            (params2GVs lp lc gl))::ECs) gl')
    tr.
Proof.
  intros fid rt lp S M EC lc gl lc' gl' B'' Result tr B' I' la lb H.
  revert fid rt lp S M EC lc gl lc' gl' B'' Result tr H B' I' la lb.
  destruct db__implies__ds as [_ [_ J]]. eauto.
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

Lemma dbFdefInf__implies__dsop_diverges : forall fid rt lp S M ECs lc gl tr B' I' la lb,
  dbFdefInf fid rt lp S M ECs lc gl tr ->
  lookupFdefViaIDFromSystemC S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some B' ->
  getEntryInsn B' = Some I' ->
  dsop_diverges 
    (mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) B' I' 
                        (initLocals la (params2GVs lp lc gl)) 
                        (params2GVs lp lc gl))::ECs) gl)
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
      (state2:=mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb)
                               B' I' (initLocals la (params2GVs lp lc gl)) 
                               (params2GVs lp lc gl))::
                        (mkEC F B (insn_call rid rt fid lp) lc arg)::EC) 
                        gl); 
      try solve [clear CIH_dbFdefInf CIH_dbInsnInf; auto].
      apply CIH_dbFdefInf with (B':=B')(I':=I')(la:=la)(lb:=lb) in HdbFdefInf; auto.

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

  intros fid rt lp S M ECs lc gl tr B' I' la lb 
    HdbFdefInf Hlookup HgetEntryBlock HgetEntryInsn.
  inversion HdbFdefInf; subst.
  rewrite Hlookup in H. inversion H; subst.
  rewrite HgetEntryBlock in H0. inversion H0; subst.
  rewrite HgetEntryInsn in H1. inversion H1; subst.
  apply dbopInf__implies__dsop_diverges in H2.
  exact H2.
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
    (state2:=mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb)
                             B' I' (initLocals la (params2GVs lp lc gl)) 
                             (params2GVs lp lc gl))::
                      (mkEC F B (insn_call rid rt fid lp) lc arg)::EC) 
                      gl); 
    try solve [clear CIH_dbInsnInf; auto].
    apply dbFdefInf__implies__dsop_diverges with (B':=B')(I':=I')(la:=la)(lb:=lb) in HdbFdefInf; auto.
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

Definition nbInsn__implies__nsop_plus_prop state_tr states' (nb:nbInsn state_tr states') := 
  nsop_plus (state_tr::nil) states'.
Definition nbop_star__implies__nsop_star_prop states states' (nb:nbop_star states states') := 
  nsop_star states states'.
Definition nbFdef__implies__nsop_star_prop fid rt lp S M ECs lc gl tr lc_gl_block_re_trs 
           (nb:nbFdef fid rt lp S M ECs lc gl tr lc_gl_block_re_trs) := 
  forall B' I' la lb,
  lookupFdefViaIDFromSystemC S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some B' ->
  getEntryInsn B' = Some I' ->
  nsop_star
    ((mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             B' I' (initLocals la (params2GVs lp lc gl))
                            (params2GVs lp lc gl))::ECs) gl, tr)::nil)
    (returnStatesFromOp S M ECs lp lc gl rt fid la lb lc_gl_block_re_trs)
  .

Lemma returnStatesFromOp__nsop_star__updateStatesFromReturns : forall lc_gl_block_re_trs S M F B rid (rt:typ) (fid:id) lp (lc:GVMap) arg EC I' lc gl rt fid la lb,
  getNextInsnFrom (insn_call rid rt fid lp) B = Some I' ->
  nsop_star
    (returnStatesFromOp S M (mkEC F B (insn_call rid rt fid lp) lc arg::EC)
                        lp lc gl rt fid la lb lc_gl_block_re_trs)
    (updateStatesFromReturns S M F B I' lc rt arg EC rid lc_gl_block_re_trs).
Proof.
  induction lc_gl_block_re_trs; simpl; intros; auto.
  destruct a as [p tr]. 
  destruct p as [p re]. 
  destruct p as [p B'']. 
  destruct p as [lc' gl'].
  remember (rt0 =t= typ_void) as rt0_eq_void.
  destruct rt0_eq_void.
  Case "rt0_is_void".
    assert (
      (mkState S M (mkEC F B I' lc0 arg::EC) gl', tr)::
      (updateStatesFromReturns S M F B I' lc0 rt0 arg EC rid lc_gl_block_re_trs) = 
      ((mkState S M (mkEC F B I' lc0 arg::EC) gl', tr)::nil) ++
      (updateStatesFromReturns S M F B I' lc0 rt0 arg EC rid lc_gl_block_re_trs)
    ) as EQ. auto.
    rewrite EQ.
    apply nsop_star_cons; auto.
      rewrite app_nil_end.
      eapply nsReturn; simpl; eauto.
        rewrite <- Heqrt0_eq_void. auto.

  Case "rt0_isnt_void".
    remember (updateMem lc0 gl' rid (getOperandValue re lc' gl')) as lc_gl.
    destruct lc_gl as [lc'' gl''].
    assert (
      (mkState S M (mkEC F B I' lc'' arg::EC) gl'', tr)::
      (updateStatesFromReturns S M F B I' lc0 rt0 arg EC rid lc_gl_block_re_trs) = 
      ((mkState S M (mkEC F B I' lc'' arg::EC) gl'', tr)::nil) ++
      (updateStatesFromReturns S M F B I' lc0 rt0 arg EC rid lc_gl_block_re_trs)
    ) as EQ. auto.
    rewrite EQ.
    apply nsop_star_cons; auto.
      rewrite app_nil_end.
      eapply nsReturn; simpl; eauto.
        rewrite <- Heqrt0_eq_void. auto.
Qed.

Lemma nb__implies__ns:
  (forall state_tr states' nb, @nbInsn__implies__nsop_plus_prop state_tr states' nb) /\
  (forall states states' nb, @nbop_star__implies__nsop_star_prop states states' nb) /\
  (forall fid rt lp S M ECs lc gl tr lc_gl_block_re_trs nb, 
     @nbFdef__implies__nsop_star_prop fid rt lp S M ECs lc gl tr lc_gl_block_re_trs nb).
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
  intros; subst; simpl; intuition.
  Case "nbBranch_def".
    apply nsop_plus_trans with (states2:=(mkState S M (mkEC F B' I' lc' arg::EC) gl, tr)::nil); auto.
      rewrite app_nil_end; eauto.
  Case "nbBranch_undef".
    apply nsop_plus_trans with (states2:=(mkState S M (mkEC F B1' I1' lc1' arg::EC) gl, tr)::
                                        (mkState S M (mkEC F B2' I2' lc2' arg::EC) gl, tr)::nil); auto.
      rewrite app_nil_end; eauto.
  Case "nbBranch_uncond".
    apply nsop_plus_trans with (states2:=(mkState S M (mkEC F B' I' lc' arg::EC) gl, tr)::nil); auto.
      rewrite app_nil_end; eauto.
  Case "nbCallInsn".
    inversion n. subst.
    assert (Hlookup:=H0).
    apply H with (B':=B')(I':=I'0) in H0; auto.
    apply nsop_plus_trans with 
      (states2:=(mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb)
                               B' I'0 (initLocals la (params2GVs lp lc gl)) 
                               (params2GVs lp lc gl))::
                              (mkEC F B (insn_call rid rt fid lp) lc arg)::EC) 
                               gl, tr)::nil); auto.
      rewrite app_nil_end; eauto.

      apply nsop_star_trans with 
        (states2:=returnStatesFromOp S M (mkEC F B (insn_call rid rt fid lp) lc arg::EC)
                              lp lc gl rt fid la lb lc_gl_block_re_trs); auto.
      apply returnStatesFromOp__nsop_star__updateStatesFromReturns; auto.
  Case "nbAddInsn".
    apply nsop_plus_trans with (states2:=(mkState S M (mkEC F B I' lc' arg::EC) gl', tr)::nil); auto.
      rewrite app_nil_end; eauto.
  
  Case "nbop_star_cons".
    assert ((state, tr)::states=((state, tr)::nil)++states) as EQ. auto.
    rewrite EQ.
    apply nsop_star_merge; auto.

  Case "nbop_star_trans".
    apply nsop_star_trans with (states2:=states2); auto.
        
  Case "nbFdef_intro".
    rewrite H0 in e. inversion e; subst.
    rewrite H1 in e0. inversion e0; subst.
    rewrite H2 in e1. inversion e1; subst.
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

Lemma nbFdef__implies__nsop_star : forall fid rt lp S M ECs lc gl tr lc_gl_block_re_trs B' I' la lb,
  nbFdef fid rt lp S M ECs lc gl tr lc_gl_block_re_trs ->
  lookupFdefViaIDFromSystemC S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some B' ->
  getEntryInsn B' = Some I' ->
  nsop_star
    ((mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                             B' I' (initLocals la (params2GVs lp lc gl))
                            (params2GVs lp lc gl))::ECs) gl, tr)::nil)
    (returnStatesFromOp S M ECs lp lc gl rt fid la lb lc_gl_block_re_trs)
  .
Proof.
  intros fid rt lp S M ECs lc gl tr lc_gl_block_re_trs B' I' la lb H.
  revert fid rt lp S M ECs lc gl tr lc_gl_block_re_trs H B' I' la lb.
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

Lemma nbFdefInf__implies__nsop_diverges : forall fid rt lp S M ECs lc gl tr B' I' la lb trs',
  nbFdefInf fid rt lp S M ECs lc gl tr trs' ->
  lookupFdefViaIDFromSystemC S fid = Some (fdef_intro (fheader_intro rt fid la) lb) ->
  getEntryBlock (fdef_intro (fheader_intro rt fid la) lb) = Some B' ->
  getEntryInsn B' = Some I' ->
  nsop_diverges 
    ((mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb) B' I' 
                        (initLocals la (params2GVs lp lc gl)) 
                        (params2GVs lp lc gl))::ECs) gl, tr)::nil) trs'.
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
      (states':=(mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb)
                               B' I' (initLocals la (params2GVs lp lc gl)) 
                               (params2GVs lp lc gl))::
                        (mkEC F B (insn_call rid rt fid lp) lc arg)::EC) 
                        gl, tr)::nil).
      apply nsop_plus_trans 
        with (states2:=(mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb)
                                         B' I' (initLocals la (params2GVs lp lc gl)) 
                                         (params2GVs lp lc gl))::
                                     (mkEC F B (insn_call rid rt fid lp) lc arg)::EC) 
                                     gl, tr)::nil); auto.
        rewrite app_nil_end; eauto.
      
      apply CIH_nbFdefInf with (B':=B')(I':=I')(la:=la)(lb:=lb) in HnbFdefInf; auto.

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

  intros fid rt lp S M ECs lc gl tr B' I' la lb trs 
    HnbFdefInf Hlookup HgetEntryBlock HgetEntryInsn.
  inversion HnbFdefInf; subst.
  rewrite Hlookup in H. inversion H; subst.
  rewrite HgetEntryBlock in H0. inversion H0; subst.
  rewrite HgetEntryInsn in H1. inversion H1; subst.
  apply nbopInf__implies__nsop_diverges in H2.
  exact H2.
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
    (states':=(mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb)
                             B' I' (initLocals la (params2GVs lp lc gl)) 
                             (params2GVs lp lc gl))::
                      (mkEC F B (insn_call rid rt fid lp) lc arg)::EC) 
                      gl, tr)::nil).
    apply nsop_plus_trans 
      with (states2:=(mkState S M ((mkEC (fdef_intro (fheader_intro rt fid la) lb)
                                       B' I' (initLocals la (params2GVs lp lc gl)) 
                                       (params2GVs lp lc gl))::
                                   (mkEC F B (insn_call rid rt fid lp) lc arg)::EC) 
                                   gl, tr)::nil); auto.
      rewrite app_nil_end; eauto.
    
    apply nbFdefInf__implies__nsop_diverges with (B':=B')(I':=I')(la:=la)(lb:=lb) in HnbFdefInf; auto.
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

