Add LoadPath "./ott".
Add LoadPath "./monads".
Require Import ssa_dynamic.
Require Import ssa.
Require Import List.
Require Import tactics.

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
  intros sys main VarArgs FS Hdb_converges.
  inversion Hdb_converges; subst.
  apply ds_goeswrong_intro with (IS:=IS)(tr:=tr); auto.
  apply dbop__implies__dsop_star; auto.
Qed.

(***********************************************************)
(** det big-step convergence -> det small-step convergence *)

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

Lemma db_diverges__implies__ds_diverges : forall sys main VarArgs,
  db_diverges sys main VarArgs ->
  ds_diverges sys main VarArgs.
Proof.
  intros sys main VarArgs Hdb_diverges.
  inversion Hdb_diverges; subst.
  apply ds_diverges_intro with (IS:=IS)(tr:=tr); auto.
  apply dbopInf__implies__dsop_diverges; auto.
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

