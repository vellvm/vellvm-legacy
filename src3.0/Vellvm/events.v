(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Observable events, execution traces, and semantics of external calls. *)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
(* Vellvm does not have a global env component. We will provide a mapping
   from atom to blk.of explicitly. We use atom instead of ident. *)
(*Require Import Globalenvs.*)
Require Import Metatheory. 
Require Import alist. 
Require Import genericvalues. 
Require Import targetdata. 
Require Import syntax. 
Require Import memory_sim.
Require Import genericvalues_inject.
Require Import vellvm_tactics.
Export LLVMgv.

Set Implicit Arguments.

Module Genv.

Section GENV.

Variable GV: Type.

Record t : Type := mkgenv {
  genv_vars: list (atom * GV);
  genv_find_symbol: atom -> option block;
  genv_find_var_info: block -> option GV;
  genv_vars_inj: forall id1 id2 b,
    genv_find_symbol id1 = Some b ->
    genv_find_symbol id2 = Some b ->
    id1 = id2
}.

Definition find_symbol (ge:t) (id:atom) : option block :=
ge.(genv_find_symbol) id.

Definition find_var_info (ge:t) (b:block) : option GV :=
ge.(genv_find_var_info) b.

End GENV.

End Genv.

Unset Implicit Arguments.

(** * Events and traces *)

(** The observable behaviour of programs is stated in terms of
  input/output events, which represent the actions of the program
  that the external world can observe.  CompCert leaves much flexibility as to
  the exact content of events: the only requirement is that they
  do not expose memory states nor pointer values 
  (other than pointers to global variables), because these
  are not preserved literally during compilation.  For concreteness,
  we use the following type for events.  Each event represents either:

- A system call (e.g. an input/output operation), recording the
  name of the system call, its parameters, and its result.

- A volatile load from a global memory location, recording the chunk
  and address being read and the value just read. 

- A volatile store to a global memory location, recording the chunk
  and address being written and the value stored there. 

- An annotation, recording the text of the annotation and the values
  of the arguments.

  The values attached to these events are of the following form.
  As mentioned above, we do not expose pointer values directly.
  Pointers relative to a global variable are shown with the name
  of the variable instead of the block identifier.
*)

Inductive eventval: Type :=
  | EVint: forall (wz:nat), Int.int wz -> eventval
  | EVfloat: float -> eventval
  | EVptr_global: atom -> int32 -> eventval.

Definition eventgv := list eventval.

Inductive event: Type :=
  | Event_syscall: atom -> list eventgv -> option eventgv -> event
  (* Vellvm does not support Volatile accesses. *)
  (* | Event_vload: memory_chunk -> atom -> int32 -> eventgv -> event *)
  (* | Event_vstore: memory_chunk -> atom -> int32 -> eventgv -> event *)
  (* | Event_annot: atom -> list eventgv -> event *)
  .

(** The dynamic semantics for programs collect traces of events.
  Traces are of two kinds: finite (type [trace]) or infinite (type [traceinf]). *)

Definition trace := list event.

Definition E0 : trace := nil.

Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

CoInductive traceinf : Type :=
  | Econsinf: event -> traceinf -> traceinf.

Fixpoint Eappinf (t: trace) (T: traceinf) {struct t} : traceinf :=
  match t with
  | nil => T
  | ev :: t' => Econsinf ev (Eappinf t' T)
  end.

(** Concatenation of traces is written [**] in the finite case
  or [***] in the infinite case. *)

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).

Lemma E0_left: forall t, E0 ** t = t.
Proof. auto. Qed.

Lemma E0_right: forall t, t ** E0 = t.
Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall t1 t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eapp_E0_inv: forall t1 t2, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0.
Proof (@app_eq_nil event).
  
Lemma E0_left_inf: forall T, E0 *** T = T.
Proof. auto. Qed.

Lemma Eappinf_assoc: forall t1 t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

Hint Rewrite E0_left E0_right Eapp_assoc
             E0_left_inf Eappinf_assoc: trace_rewrite.

Opaque trace E0 Eapp Eappinf.

(** The following [traceEq] tactic proves equalities between traces
  or infinite traces. *)

Ltac substTraceHyp :=
  match goal with
  | [ H: (@eq trace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac decomposeTraceEq :=
  match goal with
  | [ |- (_ ** _) = (_ ** _) ] =>
      apply (f_equal2 Eapp); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac traceEq := 
  repeat substTraceHyp; autorewrite with trace_rewrite; decomposeTraceEq.

(** Bisimilarity between infinite traces. *)

CoInductive traceinf_sim: traceinf -> traceinf -> Prop :=
  | traceinf_sim_cons: forall e T1 T2,
      traceinf_sim T1 T2 ->
      traceinf_sim (Econsinf e T1) (Econsinf e T2).

Lemma traceinf_sim_refl:
  forall T, traceinf_sim T T.
Proof.
  cofix COINDHYP; intros.
  destruct T. constructor. apply COINDHYP.
Qed.
 
Lemma traceinf_sim_sym:
  forall T1 T2, traceinf_sim T1 T2 -> traceinf_sim T2 T1.
Proof.
  cofix COINDHYP; intros. inv H; constructor; auto.
Qed.

Lemma traceinf_sim_trans:
  forall T1 T2 T3, 
  traceinf_sim T1 T2 -> traceinf_sim T2 T3 -> traceinf_sim T1 T3.
Proof.
  cofix COINDHYP;intros. inv H; inv H0; constructor; eauto.
Qed.

CoInductive traceinf_sim': traceinf -> traceinf -> Prop :=
  | traceinf_sim'_cons: forall t T1 T2,
      t <> E0 -> traceinf_sim' T1 T2 -> traceinf_sim' (t *** T1) (t *** T2).

Lemma traceinf_sim'_sim:
  forall T1 T2, traceinf_sim' T1 T2 -> traceinf_sim T1 T2.
Proof.
  cofix COINDHYP; intros. inv H. 
  destruct t. elim H0; auto.
Transparent Eappinf.
Transparent E0.
  simpl. 
  destruct t. simpl. constructor. apply COINDHYP; auto.
  constructor. apply COINDHYP.
  constructor. unfold E0; congruence. auto.
Qed.

(** An alternate presentation of infinite traces as
  infinite concatenations of nonempty finite traces. *)

CoInductive traceinf': Type :=
  | Econsinf': forall (t: trace) (T: traceinf'), t <> E0 -> traceinf'.

Program Definition split_traceinf' (t: trace) (T: traceinf') (NE: t <> E0): event * traceinf' :=
  match t with
  | nil => _
  | e :: nil => (e, T)
  | e :: t' => (e, Econsinf' t' T _)
  end.
Next Obligation.
  elimtype False. elim NE. auto. 
Qed.
Next Obligation.
  red; intro. elim (H e). rewrite H0. auto. 
Qed.

CoFixpoint traceinf_of_traceinf' (T': traceinf') : traceinf :=
  match T' with
  | Econsinf' t T'' NOTEMPTY =>
      let (e, tl) := split_traceinf' t T'' NOTEMPTY in
      Econsinf e (traceinf_of_traceinf' tl)
  end.

Remark unroll_traceinf':
  forall T, T = match T with Econsinf' t T' NE => Econsinf' t T' NE end.
Proof.
  intros. destruct T; auto.
Qed.

Remark unroll_traceinf:
  forall T, T = match T with Econsinf t T' => Econsinf t T' end.
Proof.
  intros. destruct T; auto.
Qed.

Lemma traceinf_traceinf'_app:
  forall t T NE,
  traceinf_of_traceinf' (Econsinf' t T NE) = t *** traceinf_of_traceinf' T.
Proof.
  induction t.
  intros. elim NE. auto.
  intros. simpl.   
  rewrite (unroll_traceinf (traceinf_of_traceinf' (Econsinf' (a :: t) T NE))).
  simpl. destruct t. auto.
Transparent Eappinf.
  simpl. f_equal. apply IHt. 
Qed.

(** Prefixes of traces. *)

Definition trace_prefix (t1 t2: trace) :=
  exists t3, t2 = t1 ** t3.

Definition traceinf_prefix (t1: trace) (T2: traceinf) :=
  exists T3, T2 = t1 *** T3.

Lemma trace_prefix_app:
  forall t1 t2 t,
  trace_prefix t1 t2 ->
  trace_prefix (t ** t1) (t ** t2).
Proof.
  intros. destruct H as [t3 EQ]. exists t3. traceEq. 
Qed.

Lemma traceinf_prefix_app:
  forall t1 T2 t,
  traceinf_prefix t1 T2 ->
  traceinf_prefix (t ** t1) (t *** T2).
Proof.
  intros. destruct H as [T3 EQ]. exists T3. subst T2. traceEq.
Qed.

Set Implicit Arguments.

(** * Relating values and event values *)

Section EVENTVAL.

(** Global environment used to translate between global variable names and their block identifiers. *)
Variable GV: Type.
Variable ge: Genv.t GV.

(** Translation between values and event values. *)

Inductive eventval_match: eventval -> typ -> val -> Prop :=
  | ev_match_int: forall wz i,
      eventval_match (EVint wz i) Tint (Vint wz i)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) Tfloat (Vfloat f)
  | ev_match_ptr: forall id b ofs,
      Genv.find_symbol ge id = Some b ->
      eventval_match (EVptr_global id ofs) Tint (Vptr b ofs).

Inductive eventval_list_match: list eventval -> list typ -> list val -> Prop :=
  | evl_match_nil:
      eventval_list_match nil nil nil
  | evl_match_cons:
      forall ev1 evl ty1 tyl v1 vl,
      eventval_match ev1 ty1 v1 ->
      eventval_list_match evl tyl vl ->
      eventval_list_match (ev1::evl) (ty1::tyl) (v1::vl).

(** Some properties of these translation predicates. *)

Lemma eventval_match_type:
  forall ev ty v,
  eventval_match ev ty v -> Val.has_type v ty.
Proof.
  intros. inv H; constructor.
Qed.

Lemma eventval_list_match_length:
  forall evl tyl vl, eventval_list_match evl tyl vl -> List.length vl = List.length tyl.
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma eventval_match_lessdef:
  forall ev ty v1 v2,
  eventval_match ev ty v1 -> Val.lessdef v1 v2 -> eventval_match ev ty v2.
Proof.
  intros. inv H; inv H0; constructor; auto.
Qed.

Lemma eventval_list_match_lessdef:
  forall evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, Val.lessdef_list vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_lessdef; eauto. eauto.
Qed.

(** Compatibility with memory injections *)

Variable f: block -> option (block * Z).

Definition meminj_preserves_globals : Prop :=
     (forall id b, Genv.find_symbol ge id = Some b -> f b = Some(b, 0))
  /\ (forall b gv, Genv.find_var_info ge b = Some gv -> f b = Some(b, 0))
  /\ (forall b1 b2 delta gv, 
        Genv.find_var_info ge b2 = Some gv -> 
        f b1 = Some(b2, delta) -> b2 = b1).

Hypothesis glob_pres: meminj_preserves_globals.

Lemma eventval_match_inject:
  forall ev ty v1 v2 
    (H:eventval_match ev ty v1) (H0:MoreMem.val_inject f v1 v2), 
    eventval_match ev ty v2.
Proof.
  intros. 
  inv H0; auto; inv H.
    destruct glob_pres as [A [B C]].
    exploit A; eauto. intro EQ; rewrite H1 in EQ; inv EQ.
    rewrite Int.add_zero. econstructor; eauto. 
Qed.

Lemma eventval_match_inject_2:
  forall ev ty v,
  eventval_match ev ty v -> MoreMem.val_inject f v v.
Proof.
  induction 1. constructor. constructor.
  destruct glob_pres as [A [B C]].
  exploit A; eauto. intro EQ.
  econstructor; eauto. rewrite Int.add_zero; auto.
Qed.

Lemma eventval_list_match_inject:
  forall evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, MoreMem.val_list_inject f vl1 vl2 -> 
    eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_inject; eauto. eauto.
Qed.

(** Determinism *)

Ltac drewrite_int :=
  match goal with
  | H: existT _ ?wz ?i = _ |- context [?C ?wz ?i] =>
      let R := fresh "R" in
      remember (C wz i) as R;
      match goal with
      | HeqR: _ = ?C ?wz ?i |- _ =>
        dependent rewrite H in HeqR; subst R
      end
  end.

Lemma eventval_match_determ_1:
  forall ev ty v1 v2 (H:eventval_match ev ty v1) (H0:eventval_match ev ty v2), 
    v1 = v2.
Proof.
  intros. 
  inv H; inv H0; auto. 
    drewrite_int; auto.
    congruence.
Qed.

Lemma eventval_match_determ_2:
  forall ev1 ev2 ty v (H:eventval_match ev1 ty v) (H0: eventval_match ev2 ty v),
    ev1 = ev2.
Proof.
  intros. 
  inv H; inv H0; auto.
    drewrite_int; auto.
    decEq. eapply Genv.genv_vars_inj; eauto. 
Qed.

Lemma eventval_list_match_determ_2:
  forall evl1 tyl vl, eventval_list_match evl1 tyl vl ->
  forall evl2 (H: eventval_list_match evl2 tyl vl), evl1 = evl2.
Proof.
  induction 1; intros. 
    inv H. auto.

    match goal with
    | H1: eventval_list_match _ (_::_) (_::_) |- _ =>
        inv H1; f_equal; eauto
    end.
    eapply eventval_match_determ_2; eauto.
Qed.

(** Validity *)

Definition eventval_valid (ev: eventval) : Prop :=
  match ev with
  | EVint _ _ => True
  | EVfloat _ => True
  | EVptr_global id ofs => exists b, Genv.find_symbol ge id = Some b
  end.

Definition eventval_type (ev: eventval) : typ :=
  match ev with
  | EVint _ _ => Tint
  | EVfloat _ => Tfloat
  | EVptr_global id ofs => Tint
  end.

Lemma eventval_valid_match:
  forall ev ty,
  eventval_valid ev -> eventval_type ev = ty -> exists v, eventval_match ev ty v.
Proof.
  intros. subst ty. destruct ev; simpl in *.
  exists (Vint wz i); constructor.
  exists (Vfloat f0); constructor.
  destruct H as [b A]. 
  match goal with 
  | |- context [EVptr_global _ ?i] => exists (Vptr b i); constructor; auto
  end.
Qed.

Lemma eventval_match_valid:
  forall ev ty v,
  eventval_match ev ty v -> eventval_valid ev /\ eventval_type ev = ty.
Proof.
  induction 1; simpl; auto. split; auto. exists b; auto.
Qed.

End EVENTVAL.

Definition eventgv_match (TD:LLVMtd.TargetData) (ge: Genv.t GenericValue) 
  (egv: eventgv) (t:LLVMsyntax.typ) (gv:GenericValue) : Prop :=
match flatten_typ TD t with
| Some ms =>
    Forall3 (fun ev m g =>
             let '(v, m0) := g in
             eventval_match ge ev (AST.type_of_chunk m) v /\
             m = m0) egv ms gv
| None => False
end.

Definition eventgv_list_match (TD:LLVMtd.TargetData) (ge: Genv.t GenericValue) 
  (egvs: list eventgv) (ts:list LLVMsyntax.typ) (gvs: list GenericValue) : Prop :=
Forall3 (eventgv_match TD ge) egvs ts gvs.

Lemma eventgv_match_type:
  forall TD ge ev ty gv,
  eventgv_match TD ge ev ty gv -> gv_has_type TD gv ty.
Proof.
  unfold eventgv_match, gv_has_type.
  intros.
  match goal with
  | |- match ?e with
       | Some _ => _
       | None => _
       end => destruct e; auto
  end.
  induction H; simpl; auto.
    destruct z as [x0 y0].
    destruct (split l'') as [g d].
    simpl. destruct H; subst.
    constructor; eauto using eventval_match_type.
Qed.

Lemma eventgv_list_match_length:
  forall TD ge evl tyl vl, 
  eventgv_list_match TD ge evl tyl vl -> List.length vl = List.length tyl.
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma eventgv_match_lessdef:
  forall TD ge ev ty v1 v2
  (H: eventgv_match TD ge ev ty v1) (H0: gv_lessdef v1 v2),
  eventgv_match TD ge ev ty v2.
Proof.
  unfold eventgv_match, gv_lessdef.
  intros. inv_mbind. clear HeqR.
  generalize dependent v2.
  induction H; intros; 
    match goal with
    | H0 : Forall2 _ _ _ |- _ => inv H0
    end; simpl; try constructor; eauto.

    match goal with
    | _: match ?z with
         | (_, _) => 
            match ?y0 with
            | (_, _) => _ 
            end
         end |- _ => 
         destruct y0 as [v2 ?]; destruct z as [x0 y0]
    end.
    destruct H; subst. destruct H4; subst.
    split; auto.
      eapply eventval_match_lessdef; eauto; tauto.
Qed.

Lemma eventgv_list_match_lessdef:
  forall TD ge evl tyl vl1, eventgv_list_match TD ge evl tyl vl1 ->
  forall vl2, gv_lessdef_list vl1 vl2 -> eventgv_list_match TD ge evl tyl vl2.
Proof.
  induction 1; intros. 
    inv H; constructor.

    inv H1. unfold eventgv_list_match in IHForall3.
    constructor; eauto.
      eapply eventgv_match_lessdef; eauto.
Qed.

(** Compatibility with memory injections *)

Section EventgvMatchInject.

Variable ge: Genv.t GenericValue.
Variable f: block -> option (block * Z).

Hypothesis glob_pres: @meminj_preserves_globals GenericValue ge f.

Lemma eventgv_match_inject:
  forall TD ev ty v1 v2 (H:eventgv_match TD ge ev ty v1) (H0:gv_inject f v1 v2), 
    eventgv_match TD ge ev ty v2.
Proof.
  unfold eventgv_match.
  intros. inv_mbind. clear HeqR.
  generalize dependent v2.
  induction H; intros;
    match goal with
    | H0: gv_inject _ _ _ |- _ => inv H0
    end; try constructor; 
    match goal with
    | H: _ /\ _ |- _ => destruct H
    end; eauto using eventval_match_inject.
Qed.

Lemma eventgv_match_inject_2:
  forall TD ev ty v,
  eventgv_match TD ge ev ty v -> gv_inject f v v.
Proof.
  unfold eventgv_match.
  intros. inv_mbind. clear HeqR.
  induction H; auto.
    destruct z as [v m]. destruct H; subst.
    constructor; eauto using eventval_match_inject_2.
Qed.

Lemma eventgv_list_match_inject:
  forall TD evl tyl vl1 (H:eventgv_list_match TD ge evl tyl vl1),
  forall vl2 (H0: gv_list_inject f vl1 vl2), eventgv_list_match TD ge evl tyl vl2.
Proof.
  unfold eventgv_list_match.
  induction 1; intros.
    inv H0; constructor.
    inv H1.
    constructor; eauto.
      eapply eventgv_match_inject; eauto.
Qed.

End EventgvMatchInject.

(** Determinism *)

Lemma eventgv_match_determ_1:
  forall TD ge ev ty v1 v2 (H:eventgv_match TD ge ev ty v1) 
    (H0:eventgv_match TD ge ev ty v2), v1 = v2.
Proof.
  unfold eventgv_match.
  intros. inv_mbind. clear HeqR.
  generalize dependent v2.
  induction H; intros. 
    inv H0; auto.
    inv H1.
    destruct z, z0.
    erewrite IHForall3; eauto.
    repeat match goal with
    | H: _/\_ |- _ => destruct H; subst
    end.
    erewrite eventval_match_determ_1 with (v1:=v); eauto.
Qed.

Lemma eventgv_match_determ_2:
  forall TD ge ev1 ev2 ty v (H:eventgv_match TD ge ev1 ty v) 
    (H0: eventgv_match TD ge ev2 ty v), ev1 = ev2.
Proof.
  unfold eventgv_match.
  intros. inv_mbind. clear HeqR.
  generalize dependent ev2.
  induction H; intros. 
    inv H0. auto.

    inv H1.
    destruct z.
    erewrite IHForall3; eauto.
    repeat match goal with
    | H: _/\_ |- _ => destruct H; subst
    end.
    erewrite eventval_match_determ_2 with (ev1:=x); eauto.
Qed.
 
Lemma eventgv_list_match_determ_2:
  forall TD ge evl1 tyl vl, eventgv_list_match TD ge evl1 tyl vl ->
  forall evl2 (H: eventgv_list_match TD ge evl2 tyl vl), evl1 = evl2.
Proof.
  induction 1; intros. 
    inv H. auto.

    match goal with
    | H1: eventgv_list_match _ _ _ (_::_) (_::_) |- _ =>
        inv H1; f_equal; eauto
    end.
    eapply eventgv_match_determ_2; eauto.
Qed.

(** Validity *)

Definition eventgv_valid (ge:Genv.t GenericValue) (egv: eventgv) : Prop :=
List.Forall (eventval_valid ge) egv.

Definition eventgv_type (ge:Genv.t GenericValue) (egv: eventgv) : list typ :=
List.map eventval_type egv.

Definition eventval_has_chunk := 
fun (ev : eventval) (chk : AST.memory_chunk) =>
match ev with
| EVint wz i0 => match chk with
                 | Mint wz' => wz = wz' /\
                               0 <= Int.unsigned wz i0 < Int.modulus wz
                 | _ => False
                 end
| EVfloat f => match chk with
               | Mint _ => False
               | Mfloat32 => f = Float.singleoffloat f
               | Mfloat64 => True
               end
| _ => match chk with
       | Mint wz => wz = 31%nat
       | _ => False
       end
end.

Lemma eventval_valid_match':
  forall (ge:Genv.t GenericValue) ev m,
  eventval_valid ge ev -> 
  eventval_has_chunk ev m -> 
  exists v, 
    eventval_match ge ev (type_of_chunk m) (Val.load_result m v) /\
    Val.has_chunk v m.
Proof.
  intros. destruct ev; simpl in *.
    destruct m; tinv H0.
    destruct H0; subst. 
    exists (Vint n i). simpl. rewrite Int.repr_unsigned. 
    split. constructor.
    split; auto.

    exists (Vfloat f).
    destruct m; tinv H0; simpl.
      rewrite <- H0. 
      split; auto.
        constructor.
      split; auto.
        constructor.

    destruct m; inv H0.
    destruct H as [b H].
    exists (Vptr b i). simpl. 
    split; auto.
      constructor; auto.
Qed.

Lemma eventval_has_chunk__eventval_has_typ: forall ev chk
  (Hchk: eventval_has_chunk ev chk), eventval_type ev = AST.type_of_chunk chk.
Proof.
  intros.
  destruct ev, chk; try inv Hchk; simpl; auto.
Qed.

Definition eventgv_has_chunk (egv:eventgv) (mcs:list AST.memory_chunk): Prop :=
List.Forall2 (fun ev mc => eventval_has_chunk ev mc) egv mcs.

Lemma eventgv_valid_match: forall TD ge ev ty t ms,
  eventgv_type ge ev = ty -> eventgv_valid ge ev -> 
  flatten_typ TD t = Some ms -> 
  List.map type_of_chunk ms = ty ->
  exists v, eventgv_match TD ge ev t v.
Proof.
  unfold eventgv_valid, eventgv_type, eventgv_match.
  intros. subst. rewrite H1. clear H1 t.
  generalize dependent ms.
  induction ev; destruct ms; intro H2; inv H2.
    exists nil. constructor; auto.

    inv H0.
    apply IHev in H3; auto.
    destruct H3 as [vs2 H3].
    eapply eventval_valid_match in H4; eauto.
    destruct H4 as [v1 H4].
    exists ((v1,m)::vs2).
    constructor; auto.
      rewrite H1.
      split; auto.
Qed.

Lemma eventgv_match_valid:
  forall TD ge ev t v,
  eventgv_match TD ge ev t v -> 
  exists ms, 
    flatten_typ TD t = Some ms /\
    eventgv_valid ge ev /\ eventgv_type ge ev = List.map type_of_chunk ms.
Proof.  
  unfold eventgv_match, eventgv_valid, eventgv_type.
  intros. inv_mbind. clear HeqR.
  exists l.
  split; auto.
  induction H; auto.
    destruct z. destruct IHForall3.
    destruct H as [H EQ]; subst.
    apply eventval_match_valid in H. destruct H.
    split.
      constructor; auto.

      simpl.
      f_equal; auto.
Qed.

(** Invariance under changes to the global environment *)

Section EVENTVAL_INV.

Variable GV: Type.
Variable ge1: Genv.t GV.
Variable ge2: Genv.t GV.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eventval_match_preserved:
  forall ev ty v,
  eventval_match ge1 ev ty v -> eventval_match ge2 ev ty v.
Proof.
  induction 1; constructor. rewrite symbols_preserved; auto. 
Qed.

Lemma eventval_list_match_preserved:
  forall evl tyl vl,
  eventval_list_match ge1 evl tyl vl -> eventval_list_match ge2 evl tyl vl.
Proof.
  induction 1; constructor; auto. eapply eventval_match_preserved; eauto.
Qed.

Lemma eventval_valid_preserved:
  forall ev, eventval_valid ge1 ev -> eventval_valid ge2 ev.
Proof.
  unfold eventval_valid; destruct ev; auto. 
  intros [b A]. exists b; rewrite symbols_preserved; auto.
Qed.

End EVENTVAL_INV.

Section EVENTGV_INV.

Variable ge1: Genv.t GenericValue.
Variable ge2: Genv.t GenericValue.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eventgv_match_preserved:
  forall TD ev ty v,
  eventgv_match TD ge1 ev ty v -> eventgv_match TD ge2 ev ty v.
Proof.
  unfold eventgv_match.
  intros. inv_mbind. clear HeqR.
  induction H.
    constructor.

    destruct z. 
    destruct H as [H EQ]; subst.
    constructor; eauto using eventval_match_preserved.
Qed.

Lemma eventgv_list_match_preserved:
  forall TD evl tyl vl,
  eventgv_list_match TD ge1 evl tyl vl -> eventgv_list_match TD ge2 evl tyl vl.
Proof.
  induction 1; constructor; auto. eapply eventgv_match_preserved; eauto.
Qed.

Lemma eventgv_valid_preserved:
  forall ev, eventgv_valid ge1 ev -> eventgv_valid ge2 ev.
Proof.
  unfold eventgv_valid.
  induction 1; simpl; intros; auto.
    constructor; eauto using eventval_valid_preserved.
Qed.

End EVENTGV_INV.

(** * Matching traces. *)

Section MATCH_TRACES.

Variable ge: Genv.t GenericValue.

(** Matching between traces corresponding to single transitions.
  Arguments (provided by the program) must be equal.
  Results (provided by the outside world) can vary as long as they
  can be converted safely to values. *)

Inductive match_traces: trace -> trace -> Prop :=
  | match_traces_E0:
      match_traces nil nil
  | match_traces_syscall_some: forall id args res1 res2,
      eventgv_valid ge res1 -> eventgv_valid ge res2 ->
      eventgv_type ge res1 = eventgv_type ge res2 ->
      match_traces (Event_syscall id args (Some res1) :: nil) (Event_syscall id args (Some res2) :: nil)
  | match_traces_syscall_other: forall id args,
      match_traces (Event_syscall id args None :: nil) (Event_syscall id args None :: nil)
  (* Vellvm does not support Volatile accesses. *)
  (* | match_traces_vload: forall chunk id ofs res1 res2, *)
  (*     eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 -> *)
  (*     match_traces (Event_vload chunk id ofs res1 :: nil) (Event_vload chunk id ofs res2 :: nil) *)
  (* | match_traces_vstore: forall chunk id ofs arg, *)
  (*     match_traces (Event_vstore chunk id ofs arg :: nil) (Event_vstore chunk id ofs arg :: nil) *)
  (* | match_traces_annot: forall id args, *)
  (*     match_traces (Event_annot id args :: nil) (Event_annot id args :: nil) *)
  .

End MATCH_TRACES.

(** Invariance by change of global environment *)

Section MATCH_TRACES_INV.

Variable ge1: Genv.t GenericValue.
Variable ge2: Genv.t GenericValue.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma match_traces_preserved:
  forall t1 t2, match_traces ge1 t1 t2 -> match_traces ge2 t1 t2.
Proof.
  induction 1; constructor; auto; eapply eventgv_valid_preserved; eauto.
Qed.

End MATCH_TRACES_INV.




