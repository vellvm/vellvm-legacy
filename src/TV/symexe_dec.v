Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import trace.
Require Import assoclist.
Require Import ssa_props.
Require Import CoqListFacts.
Require Import symexe_def.

Export SimpleSE.


Definition sumbool2bool A B (dec:sumbool A B) : bool :=
match dec with
| left _ => true
| right _ => false
end.

Lemma sumbool2bool_true : forall A B H,
  sumbool2bool A B H = true -> A.
Proof.
  intros.
  unfold sumbool2bool in H0.
  destruct H; auto.
    inversion H0.
Qed.

Lemma sumbool2bool_false : forall A B H,
  sumbool2bool A B H = false -> B.
Proof.
  intros.
  unfold sumbool2bool in H0.
  destruct H; auto.
    inversion H0.
Qed.

Lemma eq_sumbool2bool_true : forall A (a1 a2:A) (H:{a1=a2}+{~a1=a2}),
  a1 = a2 ->
  sumbool2bool _ _ H = true.
Proof.
  intros; subst.
  destruct H; auto.
Qed.

Definition typ_dec_prop (t1:typ) := forall t2, {t1=t2} + {~t1=t2}.
Definition list_typ_dec_prop (lt1:list_typ) := forall lt2, {lt1=lt2} + {~lt1=lt2}.

Ltac done_right := right; intro J; inversion J; subst; auto.

Lemma typ_mutrec_dec :
  (forall t1, typ_dec_prop t1) *
  (forall lt1, list_typ_dec_prop lt1).
Proof.
  apply typ_mutrec; 
    unfold typ_dec_prop, list_typ_dec_prop;
    intros;
    try solve [
      destruct t2; try solve [done_right | auto]
    ].

  destruct t2; try solve [done_right].
  destruct (@eq_nat_dec s s0); try solve [subst; auto | done_right].

  destruct t2; try solve [done_right].
  destruct (@H t2); subst; try solve [done_right].
  destruct (@eq_nat_dec s s0); subst; try solve [subst; auto | done_right].

  destruct t2; try solve [done_right].
  destruct (@H t2); subst; try solve [done_right].
  destruct (@H0 l1); subst; try solve [subst; auto | done_right].

  destruct t2; try solve [done_right].
  destruct (@H l1); subst; try solve [subst; auto | done_right].

  destruct t2; try solve [done_right].
  destruct (@H t2); subst; try solve [subst; auto | done_right].

  destruct lt2; try solve [auto | done_right].

  destruct lt2; try solve [right; intro J; inversion J].
  destruct (@H t0); subst; try solve [done_right].
  destruct (@H0 lt2); subst; try solve [subst; auto | done_right].
Qed.

Lemma typ_dec : forall (t1 t2:typ), {t1=t2} + {~t1=t2}.
Proof.
  destruct typ_mutrec_dec; auto.
Qed.

Lemma list_typ_dec : forall (lt1 lt2:list_typ), {lt1=lt2} + {~lt1=lt2}.
Proof.
  destruct typ_mutrec_dec; auto.
Qed.

Definition const_dec_prop (c1:const) := forall c2, {c1=c2} + {~c1=c2}.
Definition list_const_dec_prop (lc1:list_const) := forall lc2, {lc1=lc2} + {~lc1=lc2}.

Lemma const_mutrec_dec :
  (forall c1, const_dec_prop c1) *
  (forall lc1, list_const_dec_prop lc1).
Proof.
  apply const_mutrec; 
    unfold const_dec_prop, list_const_dec_prop;
    intros;
    try solve [
      destruct c2; try solve [right; intro J; inversion J | auto] |
      destruct c2; try solve [done_right];
        destruct (@typ_dec t t0); subst; try solve [subst; auto | done_right] |
      destruct c2; try solve [done_right];
        destruct (@H l1); subst; try solve [auto | done_right]
    ].

  destruct c2; try solve [done_right].
  destruct (@eq_nat_dec i0 i1); try solve [done_right].
  destruct (@eq_nat_dec s s0); try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@typ_dec t t0); subst; try solve [done_right].
  destruct (@eq_atom_dec i0 i1); try solve [subst; auto | done_right].

  destruct lc2; try solve [auto | done_right].

  destruct lc2; try solve [done_right].
  destruct (@H c0); subst; try solve [done_right].
  destruct (@H0 lc2); subst; try solve [subst; auto | done_right].
Qed.

Lemma const_dec : forall (c1 c2:const), {c1=c2}+{~c1=c2}.
Proof.
  destruct const_mutrec_dec; auto.
Qed.

Lemma list_const_dec : forall (lc1 lc2:list_const), {lc1=lc2} + {~lc1=lc2}.
Proof.
  destruct const_mutrec_dec; auto.
Qed.

Lemma value_dec : forall (v1 v2:value), {v1=v2}+{~v1=v2}.
Proof.
  destruct v1; destruct v2; try solve [done_right].
    destruct (@eq_atom_dec i0 i1); subst; auto.
       right. intros J. inversion J; subst; auto.
    destruct (@const_dec c c0); subst; auto.
       right. intros J. inversion J; subst; auto.
Qed.    

Lemma list_value_dec : forall (lv1 lv2:list_value), {lv1=lv2}+{~lv1=lv2}.
Proof.
  induction lv1.
    destruct lv2; subst; try solve [subst; auto | done_right].

    destruct lv2; subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@IHlv1 lv2); subst; try solve [auto | done_right].
Qed.

Lemma bop_dec : forall (b1 b2:bop), {b1=b2}+{~b1=b2}.
Proof.
  destruct b1; destruct b2; try solve [auto | done_right].
Qed.

Lemma extop_dec : forall (e1 e2:extop), {e1=e2}+{~e1=e2}.
Proof.
  destruct e1; destruct e2; try solve [auto | done_right].
Qed.

Lemma castop_dec : forall (c1 c2:castop), {c1=c2}+{~c1=c2}.
Proof.
  destruct c1; destruct c2; try solve [auto | done_right].
Qed.

Lemma cond_dec : forall (c1 c2:cond), {c1=c2}+{~c1=c2}.
Proof.
  destruct c1; destruct c2; try solve [auto | done_right].
Qed.

Definition sterm_dec_prop (st1:sterm) := forall st2, {st1=st2} + {~st1=st2}.
Definition list_sterm_dec_prop (sts1:list_sterm) := forall sts2, {sts1=sts2} + {~sts1=sts2}.
Definition list_sterm_l_dec_prop (stls1:list_sterm_l) := forall stls2, {stls1=stls2} + {~stls1=stls2}.
Definition smem_dec_prop (sm1:smem) := forall sm2, {sm1=sm2} + {~sm1=sm2}.
Definition sframe_dec_prop (sf1:sframe) := forall sf2, {sf1=sf2} + {~sf1=sf2}.

Lemma se_dec :
  (forall st1, sterm_dec_prop st1) *
  (forall sts1, list_sterm_dec_prop sts1) *
  (forall stls1, list_sterm_l_dec_prop stls1) *
  (forall sm1, smem_dec_prop sm1) *
  (forall sf1, sframe_dec_prop sf1).
Proof.
  (se_mut_cases (apply se_mutrec) Case); 
    unfold sterm_dec_prop, list_sterm_dec_prop, list_sterm_l_dec_prop, smem_dec_prop, sframe_dec_prop;
    intros.
  Case "sterm_val".
    destruct st2; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "sterm_bop".
    destruct st2; try solve [done_right].
    destruct (@bop_dec b b0); subst; try solve [done_right].
    destruct (@eq_nat_dec s s2); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [auto | done_right].
  Case "sterm_extractvalue".
    destruct st2; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@list_const_dec l0 l1); subst; try solve [auto | done_right].
  Case "sterm_insertvalue".
    destruct st2; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [done_right].
    destruct (@list_const_dec l0 l1); subst; try solve [auto | done_right].
  Case "sterm_malloc".    
    destruct st2; try solve [done_right].
    destruct (@H s1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@eq_nat_dec s0 s2); subst; try solve [done_right].
    destruct (@eq_nat_dec a a0); subst; try solve [auto | done_right].
  Case "sterm_alloca".    
    destruct st2; try solve [done_right].
    destruct (@H s1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@eq_nat_dec s0 s2); subst; try solve [done_right].
    destruct (@eq_nat_dec a a0); subst; try solve [auto | done_right].
  Case "sterm_load".    
    destruct st2; try solve [done_right].
    destruct (@H s1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 st2); subst; try solve [auto | done_right].
  Case "sterm_gep".    
    destruct st2; try solve [done_right].
    destruct (@bool_dec i0 i1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@H0 l1); subst; try solve [auto | done_right].
  Case "sterm_ext".
    destruct st2; try solve [done_right].
    destruct (@extop_dec e e0); subst; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [auto | done_right].
  Case "sterm_cast".
    destruct st2; try solve [done_right].
    destruct (@castop_dec c c0); subst; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [auto | done_right].
  Case "sterm_icmp".
    destruct st2; try solve [done_right].
    destruct (@cond_dec c c0); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [auto | done_right].
  Case "sterm_phi".
    destruct st2; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H l1); subst; try solve [auto | done_right].
  Case "sterm_select".
    destruct st2; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [done_right].
    destruct (@H1 st2_3); subst; try solve [auto | done_right].
  Case "list_sterm_nil".
    destruct sts2; subst; try solve [auto | done_right].
  Case "list_sterm_cons".
    destruct sts2; subst; try solve [auto | done_right].
    destruct (@H s0); subst; try solve [done_right].
    destruct (@H0 sts2); subst; try solve [auto | done_right].
  Case "list_sterm_l_nil".
    destruct stls2; subst; try solve [auto | done_right].
  Case "list_sterm_l_cons".
    destruct stls2; subst; try solve [auto | done_right].
    destruct (@H s0); subst; try solve [done_right].
    destruct (@eq_atom_dec l0 l2); subst; try solve [done_right].
    destruct (@H0 stls2); subst; try solve [auto | done_right].
  Case "smem_init".
    destruct sm2; subst; try solve [auto | done_right].
  Case "smem_malloc".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@eq_nat_dec s0 s1); subst; try solve [done_right].
    destruct (@eq_nat_dec a a0); subst; try solve [auto | done_right].
  Case "smem_free".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 s1); subst; try solve [auto | done_right].
  Case "smem_alloca".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@eq_nat_dec s0 s1); subst; try solve [done_right].
    destruct (@eq_nat_dec a a0); subst; try solve [auto | done_right].
  Case "smem_load".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 s1); subst; try solve [auto | done_right].
  Case "smem_store".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 s2); subst; try solve [auto | done_right].
    destruct (@H1 s3); subst; try solve [auto | done_right].
  Case "sframe_init".
    destruct sf2; subst; try solve [auto | done_right].
  Case "sframe_alloca".
    destruct sf2; subst; try solve [done_right].
    destruct (@H s2); subst; try solve [done_right].
    destruct (@H0 sf2); subst; try solve [auto | done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@eq_nat_dec s1 s3); subst; try solve [done_right].
    destruct (@eq_nat_dec a a0); subst; try solve [auto | done_right].
Qed.

Lemma sterm_dec : forall (st1 st2:sterm), {st1=st2} + {~st1=st2}.
destruct se_dec as [[[[H _] _] _] _]. auto.
Qed.

Lemma list_sterm_dec :  forall (ts1 ts2:list_sterm), {ts1=ts2}+{~ts1=ts2}.
destruct se_dec as [[[[_ H] _] _] _]. auto.
Qed. 

Lemma list_sterm_l_dec :  forall (ts1 ts2:list_sterm_l), {ts1=ts2}+{~ts1=ts2}.
destruct se_dec as [[[_ H] _] _]. auto.
Qed. 

Lemma smem_dec : forall (sm1 sm2:smem), {sm1=sm2} + {~sm1=sm2}.
destruct se_dec as [[_ H] _]. auto.
Qed.

Lemma sframe_dec : forall (sf1 sf2:sframe), {sf1=sf2} + {~sf1=sf2}.
destruct se_dec as [_ H]. auto.
Qed.

Lemma sterminator_dec : forall (st1 st2:sterminator), {st1=st2} + {~st1=st2}.
Proof.
  destruct st1; destruct st2; try solve [done_right | auto].
  Case "stmn_return".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@sterm_dec s s0); subst; try solve [auto | done_right].
  Case "stmn_return_void".
    destruct (@eq_atom_dec i0 i1); subst; try solve [auto | done_right]. 
  Case "stmn_br".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@eq_atom_dec l0 l2); subst; try solve [done_right]. 
    destruct (@eq_atom_dec l1 l3); subst; try solve [done_right]. 
    destruct (@sterm_dec s s0); subst; try solve [auto | done_right].
  Case "stmn_br_uncond".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@eq_atom_dec l0 l1); subst; try solve [auto | done_right]. 
  Case "stmn_unreachable".
    destruct (@eq_atom_dec i0 i1); subst; try solve [auto | done_right]. 
Qed.

Lemma list_typ_sterm_dec : forall (l1 l2:list (typ*sterm)), {l1=l2}+{~l1=l2}.
Proof.
  induction l1.
    destruct l2; subst; try solve [subst; auto | done_right].

    destruct l2; subst; try solve [done_right].
    destruct a. destruct p.
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@sterm_dec s s0); subst; try solve [done_right].
    destruct (@IHl1 l2); subst; try solve [auto | done_right].
Qed.

Lemma scall_dec : forall (sc1 sc2:scall), {sc1=sc2} + {~sc1=sc2}.
Proof.
  destruct sc1; destruct sc2; try solve [done_right | auto].
    destruct (@eq_atom_dec i0 i2); subst; try solve [done_right]. 
    destruct (@eq_atom_dec i1 i3); subst; try solve [done_right]. 
    destruct (@bool_dec n n0); subst; try solve [done_right].
    destruct (@bool_dec t t1); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [done_right].
    destruct (@list_typ_sterm_dec l0 l1); subst; try solve [auto | done_right].
Qed.

Lemma smap_dec : forall (sm1 sm2:smap), {sm1=sm2}+{~sm1=sm2}.
Proof.
  induction sm1.
    destruct sm2; subst; try solve [subst; auto | done_right].

    destruct sm2; subst; try solve [done_right].
    destruct a. destruct p.
    destruct (@eq_atom_dec a a0); subst; try solve [done_right]. 
    destruct (@sterm_dec s s0); subst; try solve [done_right].
    destruct (@IHsm1 sm2); subst; try solve [auto | done_right].
Qed.

Lemma sterms_dec :  forall (ts1 ts2:list sterm), {ts1=ts2}+{~ts1=ts2}.
Proof.
  induction ts1.
    destruct ts2; subst; try solve [subst; auto | done_right].

    destruct ts2; subst; try solve [done_right].
    destruct (@sterm_dec a s); subst; try solve [done_right].
    destruct (@IHts1 ts2); subst; try solve [auto | done_right].
Qed.

Lemma sstate_dec : forall (sts1 sts2:sstate), {sts1=sts2} + {~sts1=sts2}.
Proof.
  destruct sts1; destruct sts2; try solve [done_right | auto].
    destruct (@smap_dec STerms0 STerms1); subst; try solve [done_right].
    destruct (@sframe_dec SFrame0 SFrame1); subst; try solve [done_right].
    destruct (@sterms_dec SEffects0 SEffects1); subst; try solve [done_right].
    destruct (@smem_dec SMem0 SMem1); subst; try solve [auto | done_right].
Qed.

Lemma params_dec : forall (p1 p2:params), {p1=p2}+{~p1=p2}.
Proof.
  induction p1.
    destruct p2; subst; try solve [subst; auto | done_right].

    destruct p2; subst; try solve [done_right].
    destruct a. destruct p.
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@IHp1 p2); subst; try solve [auto | done_right].
Qed.

Lemma cmd_dec : forall (c1 c2:cmd), {c1=c2}+{~c1=c2}.
Proof.
  (cmd_cases (destruct c1) Case); destruct c2; try solve [done_right | auto].
  Case "insn_bop".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@bop_dec b b0); subst; try solve [done_right].
    destruct (@eq_nat_dec s s0); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "insn_extractvalue".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@list_const_dec l0 l1); subst; try solve [auto | done_right].
  Case "insn_insertvalue".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [done_right].
    destruct (@list_const_dec l0 l1); subst; try solve [auto | done_right].
  Case "insn_malloc".    
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@eq_nat_dec s s0); subst; try solve [done_right].
    destruct (@eq_nat_dec a a0); subst; try solve [auto | done_right].
  Case "insn_free".    
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "insn_alloca".    
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@eq_nat_dec s s0); subst; try solve [done_right].
    destruct (@eq_nat_dec a a0); subst; try solve [auto | done_right].
  Case "insn_load".    
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "insn_store".    
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v1); try solve [auto | done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "insn_gep".    
    destruct (@eq_atom_dec i0 i2); subst; try solve [done_right]. 
    destruct (@bool_dec i1 i3); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); try solve [auto | done_right].
    destruct (@list_value_dec l0 l1); subst; try solve [auto | done_right].
  Case "insn_ext".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@extop_dec e e0); subst; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [auto | done_right].
  Case "insn_cast".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@castop_dec c c0); subst; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [auto | done_right].
  Case "insn_icmp".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@cond_dec c c0); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "insn_select".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@value_dec v v2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v0 v3); subst; try solve [done_right].
    destruct (@value_dec v1 v4); subst; try solve [auto | done_right].
  Case "insn_call".
    destruct (@eq_atom_dec i0 i2); subst; try solve [done_right]. 
    destruct (@eq_atom_dec i1 i3); subst; try solve [done_right]. 
    destruct (@bool_dec n n0); subst; try solve [done_right].
    destruct (@bool_dec t t1); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [done_right].
    destruct (@params_dec p p0); subst; try solve [auto | done_right].
Qed.

Lemma terminator_dec : forall (tmn1 tmn2:terminator), {tmn1=tmn2}+{~tmn1=tmn2}.
Proof.
  destruct tmn1; destruct tmn2; try solve [done_right | auto].
  Case "insn_return".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "insn_return_void".
    destruct (@eq_atom_dec i0 i1); subst; try solve [auto | done_right]. 
  Case "insn_br".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@eq_atom_dec l0 l2); subst; try solve [done_right]. 
    destruct (@eq_atom_dec l1 l3); subst; try solve [done_right]. 
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "insn_br_uncond".
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@eq_atom_dec l0 l1); subst; try solve [auto | done_right]. 
  Case "insn_unreachable".
    destruct (@eq_atom_dec i0 i1); subst; try solve [auto | done_right]. 
Qed.

Lemma list_id_l_dec : forall (l1 l2:list_id_l), {l1=l2}+{~l1=l2}.
Proof.
  induction l1.
    destruct l2; subst; try solve [subst; auto | done_right].

    destruct l2; subst; try solve [done_right].
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right].
    destruct (@eq_atom_dec l0 l2); subst; try solve [done_right].
    destruct (@IHl1 l3); subst; try solve [auto | done_right].
Qed.

Lemma phinode_dec : forall (p1 p2:phinode), {p1=p2}+{~p1=p2}.
Proof.
  destruct p1; destruct p2; try solve [done_right | auto].
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@list_id_l_dec l0 l1); subst; try solve [auto | done_right]. 
Qed.

Lemma insn_dec : forall (i1 i2:insn), {i1=i2}+{~i1=i2}.
Proof.
  destruct i1; destruct i2; try solve [done_right | auto].
    destruct (@phinode_dec p p0); subst; try solve [auto | done_right]. 
    destruct (@cmd_dec c c0); subst; try solve [auto | done_right]. 
    destruct (@terminator_dec t t0); subst; try solve [auto | done_right]. 
Qed.

Lemma arg_dec : forall (a1 a2:arg), {a1=a2}+{~a1=a2}.
Proof.
  destruct a1; destruct a2; try solve [subst; auto | done_right].
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [auto | done_right].
Qed.  

Lemma args_dec : forall (l1 l2:args), {l1=l2}+{~l1=l2}.
Proof.
  induction l1.
    destruct l2; subst; try solve [subst; auto | done_right].

    destruct l2; subst; try solve [done_right].
    destruct (@arg_dec a p); subst; try solve [done_right].
    destruct (@IHl1 l2); subst; try solve [auto | done_right].
Qed.

Lemma fheader_dec : forall (f1 f2:fheader), {f1=f2}+{~f1=f2}.
Proof.
  destruct f1; destruct f2; try solve [subst; auto | done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right].
    destruct (@args_dec a a0); subst; try solve [auto | done_right].
Qed.  

Lemma gvar_dec : forall (g1 g2:gvar), {g1=g2}+{~g1=g2}.
Proof.
  destruct g1; destruct g2; try solve [subst; auto | done_right].
    destruct (@eq_atom_dec i0 i1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@const_dec c c0); subst; try solve [done_right].
    destruct (@eq_nat_dec a a0); subst; try solve [auto | done_right].
Qed.  

Lemma fdec_dec : forall (f1 f2:fdec), {f1=f2}+{~f1=f2}.
Proof.
  destruct f1; destruct f2; try solve [subst; auto | done_right].
    destruct (@fheader_dec f f0); subst; try solve [auto | done_right].
Qed.  

Lemma layout_dec : forall (l1 l2:layout), {l1=l2}+{~l1=l2}.
Proof.
  destruct l1; destruct l2; try solve [subst; auto | done_right].
    destruct (@eq_nat_dec s s0); subst; try solve [done_right].
    destruct (@eq_nat_dec a a1); subst; try solve [done_right].
    destruct (@eq_nat_dec a0 a2); subst; try solve [auto | done_right].

    destruct (@eq_nat_dec s s0); subst; try solve [done_right].
    destruct (@eq_nat_dec a a1); subst; try solve [done_right].
    destruct (@eq_nat_dec a0 a2); subst; try solve [auto | done_right].

    destruct (@eq_nat_dec s s0); subst; try solve [done_right].
    destruct (@eq_nat_dec a a1); subst; try solve [done_right].
    destruct (@eq_nat_dec a0 a2); subst; try solve [auto | done_right].

    destruct (@eq_nat_dec s s0); subst; try solve [done_right].
    destruct (@eq_nat_dec a a1); subst; try solve [done_right].
    destruct (@eq_nat_dec a0 a2); subst; try solve [auto | done_right].
Qed.  

Lemma layouts_dec : forall (l1 l2:layouts), {l1=l2}+{~l1=l2}.
Proof.
  induction l1.
    destruct l2; subst; try solve [subst; auto | done_right].

    destruct l2; subst; try solve [done_right].
    destruct (@layout_dec a l0); subst; try solve [done_right].
    destruct (@IHl1 l2); subst; try solve [auto | done_right].
Qed.


