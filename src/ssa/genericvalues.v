Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "../../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Import Arith.
Require Import ssa_mem.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import assoclist.

Definition GenericValue := mvalue.
Definition GV2nat := mvalue2nat.
Definition GV2ptr := mvalue2mptr.
Definition isGVUndef := isMvalueUndef.
Definition nat2GV := nat2mvalue.
Definition undef2GV := undef2mvalue.
Definition ptr2GV TD p := mptr2mvalue TD p (getPointerSizeInBits TD).

Definition GVMap := list (id*GenericValue).
(**************************************)
(** Convert const to GV with storesize, and look up GV from operands. *)

Fixpoint _const2GV (TD:layouts) (gl:GVMap) (c:const) : option (GenericValue*typ) := 
match c with
| const_int sz n => Some (nat2GV TD sz n, typ_int sz)
| const_undef t =>  do gv <- undef2GV TD t; Some (gv, t)
| const_null t =>   Some (ptr2GV TD null, t)
| const_arr lc => _list_const_arr2GV TD gl lc
| const_struct lc =>
         match (_list_const_struct2GV TD gl lc) with
         | None => None
         | Some ((gv, t), al) => 
           match (length gv) with
           | 0 => Some (muninits al, t)
           | _ => Some (gv++muninits (al-length gv), t)
           end
         end
| const_gid t id =>
         match (lookupAL _ gl id) with
         | Some gv => Some (gv, t)
         | None => None
         end
end
with _list_const_arr2GV (TD:layouts) (gl:GVMap) (cs:list_const) : option (GenericValue*typ) := 
match cs with
| Nil_list_const => Some (nil, typ_int 0)
| Cons_list_const c lc' =>
  match (_list_const_arr2GV TD gl lc', _const2GV TD gl c) with
  | (Some (gv, t), Some (gv0,t0)) =>
             match (getTypeAllocSize TD t0) with
             | Some sz0 => Some ((gv++gv0)++muninits (sz0 - length gv0), t0)
             | None => None 
             end
  | _ => None
  end
end
with _list_const_struct2GV (TD:layouts) (gl:GVMap) (cs:list_const) : option (GenericValue*typ*align) := 
match cs with
| Nil_list_const => Some ((nil, typ_int 0), 0)
| Cons_list_const c lc' =>
  match (_list_const_struct2GV TD gl lc', _const2GV TD gl c) with
  | (Some (gv, t, struct_al), Some (gv0,t0)) =>
             match (getABITypeAlignment TD t0, getTypeAllocSize TD t0) with
             | (Some sub_al, Some sub_sz) => 
               match (le_lt_dec sub_al struct_al) with
               | left _ (* struct_al <= sub_al *) =>
                 Some (
                  (gv++
                  (muninits (sub_al - length gv0))++
                  gv0++
                  (muninits (sub_sz - length gv0)),
                  t0),
                  sub_al
                 )
               | right _ (* sub_al < struct_al *) =>
                 Some (
                  (gv++
                  (muninits (sub_al - length gv0))++
                  gv0++
                  (muninits (sub_sz - length gv0)),
                  t0),
                  struct_al
                 )
               end
             | _ => None 
             end
  | _ => None
  end
end
.

Definition const2GV (TD:layouts) (gl:GVMap) (c:const) : option GenericValue :=
match (_const2GV TD gl c) with
| None => None
| Some (gv, t) => Some gv
end.

Definition getOperandValue (TD:layouts) (v:value) (locals:GVMap) (globals:GVMap) : option GenericValue := 
match v with
| value_id id => lookupAL _ locals id 
| value_const c => (const2GV TD globals c)
end.

Definition getOperandInt (TD:layouts) (sz:nat) (v:value) (locals:GVMap) (globals:GVMap) : option nat := 
match (getOperandValue TD v locals globals) with
| Some gi => (GV2nat TD sz gi)
| None => None
end.

Definition isOperandUndef (TD:layouts) (t:typ) (v:value) (locals:GVMap) (globals:GVMap) : Prop  := 
match (getOperandValue TD v locals globals) with
| Some gi => isGVUndef TD t gi
| None => False
end.

Definition getOperandPtr (TD:layouts) (v:value) (locals:GVMap) (globals:GVMap) : option mptr := 
match (getOperandValue TD v locals globals) with
| Some gi => GV2ptr TD (getPointerSize TD) gi
| None => None
end.

Definition getOperandPtrInBits (TD:layouts) (s:sz) (v:value) (locals:GVMap) (globals:GVMap) : option mptr := 
match (getOperandValue TD v locals globals) with
| Some gi => GV2ptr TD s gi
| None => None
end.

(**************************************)
(* conversion between different lists *)

Fixpoint params2OpGVs (TD:layouts) (lp:params) (locals:GVMap) (globals:GVMap) : list (option GenericValue):=
match lp with
| nil => nil
| (_, v)::lp' => getOperandValue TD v locals globals::params2OpGVs TD lp' locals globals
end.

Fixpoint opGVs2GVs (lg:list (option GenericValue)) : list GenericValue :=
match lg with
| nil => nil
| (Some g)::lg' => g::opGVs2GVs lg'
| _::lg' => opGVs2GVs lg'
end.

Definition params2GVs (TD:layouts) (lp:params) (locals:GVMap) (globals:GVMap) := 
  opGVs2GVs (params2OpGVs TD lp locals globals).

Fixpoint values2GVs (TD:layouts) (lv:list_value) (locals:GVMap) (globals:GVMap) : option (list GenericValue):=
match lv with
| Nil_list_value => Some nil
| Cons_list_value v lv' => 
  match (getOperandValue TD v locals globals) with
  | Some GV => 
    match (values2GVs TD lv' locals globals) with
    | Some GVs => Some (GV::GVs)
    | None => None
    end
  | None => None
  end
end.

Fixpoint intValues2Nats (TD:layouts) (lv:list_value) (locals:GVMap) (globals:GVMap) : option (list nat):=
match lv with
| Nil_list_value => Some nil
| Cons_list_value v lv' => 
  match (getOperandValue TD v locals globals) with
  | Some GV => 
    match (GV2nat TD 32 GV) with
    | Some n =>
      match (intValues2Nats TD lv' locals globals) with
      | Some ns => Some (n::ns)
      | None => None
      end
    | None => None
    end
  | None => None
  end
end.

Fixpoint intConsts2Nats (TD:layouts) (lv:list_const) : option (list nat):=
match lv with
| Nil_list_const => Some nil
| Cons_list_const (const_int 32 n) lv' => 
  match (GV2nat TD 32 (nat2GV TD 32 n)) with
  | Some n =>
    match (intConsts2Nats TD lv') with
    | Some ns => Some (n::ns)
    | None => None
    end
  | None => None
  end
| _ => None
end.

Fixpoint GVs2Nats (TD:layouts) (lgv:list GenericValue) : option (list nat):=
match lgv with
| nil => Some nil
| gv::lgv' => 
    match (GV2nat TD 32 gv) with
    | Some n =>
      match (GVs2Nats TD lgv') with
      | Some ns => Some (n::ns)
      | None => None
      end
    | None => None
    end
end.

(**************************************)
(* helping functions *)

Fixpoint _initializeFrameValues (la:args) (lg:list GenericValue) (locals:GVMap) : GVMap :=
match (la, lg) with
| ((_, id)::la', g::lg') => updateAddAL _ (_initializeFrameValues la' lg' locals) id g
| _ => locals
end.

Definition initLocals (la:args) (lg:list GenericValue): GVMap := 
_initializeFrameValues la lg nil.

Definition getEntryBlock (fd:fdef) : option block :=
match fd with
| fdef_intro _ (b::_) => Some b
| _ => None
end.

Definition getEntryCmds (b:block) : cmds :=
match b with
| block_intro _ _ lc _ => lc
end.

(* FIXME : bounds check *)
Definition extractGenericValue (TD:list layout)(t:typ) (gv : GenericValue) (cidxs : list_const) : option GenericValue :=
match (intConsts2Nats TD cidxs) with
| None => None 
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some o => mget TD gv o t
  | None => None
  end
end.

Definition insertGenericValue (TD:layouts) (t:typ) (gv:GenericValue)
  (cidxs:list_const) (t0:typ) (gv0:GenericValue) : option GenericValue :=
match (intConsts2Nats TD cidxs) with
| None => None 
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some o => mset TD gv o t0 gv0
  | None => None
  end
end.

Definition GEP (TD:layouts) (locals globals:GVMap) (t:typ) (ma:mptr) (vidxs:list_value) (inbounds:bool) : option mptr :=
match (intValues2Nats TD vidxs locals globals) with
| None => None 
| Some idxs => mgep TD t ma idxs
end.

Definition mbop (TD:layouts) (op:bop) (bsz:sz) (gv1 gv2:mvalue) : option mvalue :=
match op with
| bop_add => 
  match (GV2nat TD bsz gv1, GV2nat TD bsz gv2) with
  | (Some i1, Some i2) => Some (nat2mvalue TD bsz (i1+i2))
  | _ => None
  end
| _ => None
end.

Definition BOP (TD:layouts) (lc gl:GVMap) (op:bop) (bsz:sz) (v1 v2:value) : option mvalue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => mbop TD op bsz gv1 gv2
| _ => None
end
.

Definition mcast (TD:layouts) (op:castop) (t1:typ) (gv1:mvalue) (t2:typ) : option mvalue :=
match op with
| castop_inttoptr => 
  match (t1, t2) with
  | (typ_int sz1, typ_pointer _) => 
    match (GV2ptr TD sz1 gv1) with
    | Some mp1 => Some (ptr2GV TD mp1)
    | None => None
    end
  | _ => None
  end
| castop_ptrtoint =>
  match (t1, t2) with
  | (typ_pointer _, typ_int sz2) => 
    match (GV2ptr TD (getPointerSize TD) gv1) with
    | Some mp1 => Some (mptr2mvalue TD mp1 sz2)
    | None => None
    end
  | _ => None
  end
| castop_bitcase => Some gv1
end.

Definition CAST (TD:layouts) (lc gl:GVMap) (op:castop) (t1:typ) (v1:value) (t2:typ) : option mvalue :=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mcast TD op t1 gv1 t2
| _ => None
end
.

Definition mext (TD:layouts) (op:extop) (t1:typ) (gv1:mvalue) (t2:typ) : option mvalue :=
match op with
| extop_z => 
  match (t1, t2) with
  | (typ_int sz1, typ_int sz2) => Some gv1
  | _ => None
  end
| extop_s => 
  match (t1, t2) with
  | (typ_int sz1, typ_int sz2) => Some gv1
  | _ => None
  end
end.

Definition EXT (TD:layouts) (lc gl:GVMap) (op:extop) (t1:typ) (v1:value) (t2:typ) : option mvalue :=
match (getOperandValue TD v1 lc gl) with
| (Some gv1) => mext TD op t1 gv1 t2
| _ => None
end
.

Definition micmp (TD:layouts) (c:cond) (t:typ) (gv1 gv2:mvalue) : option mvalue :=
match c with
| cond_eq =>
  match t with
  | typ_int sz => None
  | typ_pointer _ => None
  | _ => None
  end
| cond_ne => None
| cond_ugt => None
| cond_uge => None
| cond_ult => None
| cond_ule => None
| cond_sgt => None
| cond_sge => None
| cond_slt => None
| cond_sle => None
end.

Definition ICMP (TD:layouts) (lc gl:GVMap) (c:cond) (t:typ) (v1 v2:value) : option mvalue :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gv1, Some gv2) => micmp TD c t gv1 gv2
| _ => None
end.

Lemma BOP_inversion : forall TD lc gl b s v1 v2 gv,
  BOP TD lc gl b s v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    mbop TD b s gv1 gv2 = Some gv.
Proof.
  intros TD lc gl b s v1 v2 gv HBOP.
  unfold BOP in HBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HBOP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HBOP].
      remember (mbop TD b s g g0) as R.
      destruct R; inversion HBOP; subst.
        exists g. exists g0. auto.
Qed.

Lemma getOperandPtr_inversion : forall TD lc gl v mptr,
  getOperandPtr TD v lc gl = Some mptr ->
  exists gv,
    getOperandValue TD v lc gl = Some gv /\
    GV2ptr TD (getPointerSize TD) gv = Some mptr.
Proof.
  intros TD lc gl v mptr HgetOperandPtr.
  unfold getOperandPtr in HgetOperandPtr.
  remember (getOperandValue TD v lc gl) as ogv.
  destruct ogv; try solve [inversion HgetOperandPtr].
    exists g. auto.
Qed.

Lemma getOperandInt_inversion : forall TD sz lc gl v n,
  getOperandInt TD sz v lc gl = Some n ->
  exists gv,
    getOperandValue TD v lc gl = Some gv /\
    GV2nat TD sz gv = Some n.
Proof.
  intros TD sz0 lc gl v mptr HgetOperandInt.
  unfold getOperandInt in HgetOperandInt.
  remember (getOperandValue TD v lc gl) as ogv.
  destruct ogv; try solve [inversion HgetOperandInt].
    exists g. auto.
Qed.

Lemma CAST_inversion : forall TD lc gl op t1 v1 t2 gv,
  CAST TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mcast TD op t1 gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HCAST.
  unfold CAST in HCAST.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HCAST].
    remember (mcast TD op t1 g t2) as R.
    destruct R; inversion HCAST; subst.
      exists g. auto.
Qed.

Lemma EXT_inversion : forall TD lc gl op t1 v1 t2 gv,
  EXT TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    mext TD op t1 gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HEXT.
  unfold EXT in HEXT.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HEXT].
    remember (mext TD op t1 g t2) as R.
    destruct R; inversion HEXT; subst.
      exists g. auto.
Qed.

Lemma ICMP_inversion : forall TD lc gl cond t v1 v2 gv,
  ICMP TD lc gl cond t v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    micmp TD cond t gv1 gv2 = Some gv.
Proof.
  intros TD lc gl cond0 t v1 v2 gv HICMP.
  unfold ICMP in HICMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HICMP].
    remember (getOperandValue TD v2 lc gl) as ogv2.
    destruct ogv2; try solve [inversion HICMP].
      remember (micmp TD cond0 t g g0) as R.
      destruct R; inversion HICMP; subst.
        exists g. exists g0. auto.
Qed.

Lemma GEP_inversion : forall (TD:layouts) (lc gl:GVMap) (t:typ) (ma:mptr) (vidxs:list_value) ib mptr0,
  GEP TD lc gl t ma vidxs ib = Some mptr0 ->
  exists idxs, intValues2Nats TD vidxs lc gl = Some idxs /\ mgep TD t ma idxs = Some mptr0.
Proof.
  intros.
  unfold GEP in H.
  remember (intValues2Nats TD vidxs lc gl) as oidxs.
  destruct oidxs; inversion H; subst.
  exists l0. auto.
Qed.

Lemma intValues2Nats_inversion : forall l0 lc gl TD ns0,
  intValues2Nats TD l0 lc gl = Some ns0 ->
  exists gvs0, 
    values2GVs TD l0 lc gl = Some gvs0 /\
    GVs2Nats TD gvs0 = Some ns0.
Proof.
  induction l0; intros; simpl in *.
    inversion H. exists nil. auto.

    remember (getOperandValue TD v lc gl) as ogv.
    destruct ogv; try solve [inversion H].
    remember (GV2nat TD 32 g) as on.
    destruct on; try solve [inversion H].
    remember (intValues2Nats TD l0 lc gl) as ons.
    destruct ons; inversion H; subst.
    symmetry in Heqons.
    apply IHl0 in Heqons.
    destruct Heqons as [gvs [J1 J2]].
    exists (g::gvs).
    rewrite J1. 
    split; auto.
      simpl. rewrite J2. rewrite <- Heqon. auto.
Qed.

Lemma values2GVs_GVs2Nats__intValues2Nats : forall l0 lc gl TD gvs0,
  values2GVs TD l0 lc gl = Some gvs0 ->
  GVs2Nats TD gvs0 = intValues2Nats TD l0 lc gl.
Proof.
  induction l0; intros lc gl TD gvs0 H; simpl in *.
    inversion H. auto.

    destruct (getOperandValue TD v lc gl); try solve [inversion H].
      remember (values2GVs TD l0 lc gl)as ogv.
      destruct ogv; inversion H; subst.
        rewrite <- IHl0 with (gvs0:=l1); auto.
Qed.

Scheme const_ind2 := Induction for const Sort Prop
  with list_const_ind2 := Induction for list_const Sort Prop.
Combined Scheme const_mutind from const_ind2, list_const_ind2.

Lemma _const2GV_eqAL : 
  (forall c gl1 gl2 TD, eqAL _ gl1 gl2 -> 
    _const2GV TD gl1 c = _const2GV TD gl2 c) /\
  (forall cs gl1 gl2 TD, eqAL _ gl1 gl2 -> 
    _list_const_arr2GV TD gl1 cs = _list_const_arr2GV TD gl2 cs /\
    _list_const_struct2GV TD gl1 cs = _list_const_struct2GV TD gl2 cs).
Proof.
  apply const_mutind; intros; simpl; auto.
    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0.
    destruct H0; auto.

    apply H with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H0.
    destruct H0.
    rewrite H1. auto.

    rewrite H. auto.

    assert (J:=H1).
    apply H0 with (TD:=TD)(gl1:=gl1)(gl2:=gl2) in H1.
    destruct H1.
    rewrite H2. rewrite H1. erewrite H; eauto.
Qed.

Lemma const2GV_eqAL : forall c gl1 gl2 TD, 
  eqAL _ gl1 gl2 -> 
  const2GV TD gl1 c = const2GV TD gl2 c.
Proof.
  intros. unfold const2GV.
  destruct _const2GV_eqAL.
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

Lemma getOperandPtr_eqAL : forall lc1 gl lc2 v TD,
  eqAL _ lc1 lc2 ->
  getOperandPtr TD v lc1 gl = getOperandPtr TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD HeqEnv.
  unfold getOperandPtr in *.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma getOperandInt_eqAL : forall lc1 gl lc2 sz v TD,
  eqAL _ lc1 lc2 ->
  getOperandInt TD sz v lc1 gl = getOperandInt TD sz v lc2 gl.
Proof.
  intros lc1 gl lc2 sz0 v TD HeqAL.
  unfold getOperandInt in *.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma getOperandPtrInBits_eqAL : forall lc1 gl lc2 sz v TD,
  eqAL _ lc1 lc2 ->
  getOperandPtrInBits TD sz v lc1 gl = getOperandPtrInBits TD sz v lc2 gl.
Proof.
  intros lc1 gl lc2 sz0 v TD HeqAL.
  unfold getOperandPtrInBits in *.
  erewrite getOperandValue_eqAL; eauto.
Qed.

Lemma CAST_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  CAST TD lc1 gl op t1 v1 t2 = CAST TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold CAST in *.
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

Lemma intValues2Nats_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  intValues2Nats TD l0 lc1 gl = intValues2Nats TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD HeqAL; simpl; auto.
    rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v); auto.
    erewrite IHl0; eauto.
Qed.

Lemma GEP_eqAL : forall lc1 gl lc2 t ma vidxs ib TD,
  eqAL _ lc1 lc2 ->
  GEP TD lc1 gl t ma vidxs ib = GEP TD lc2 gl t ma vidxs ib.
Proof.
  intros lc1 gl lc2 t ma vidxs ib TD HeqAL.
  unfold GEP in *.
  erewrite intValues2Nats_eqAL; eauto.
Qed.

