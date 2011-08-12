Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import syntax.
Require Import infrastructure.
Require Import typings.
Require Import trace.
Require Import Memory.
Require Import genericvalues.
Require Import alist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import targetdata.
Require Import opsem.
Require Import dopsem.
Require Import sb_def.
Require Import sb_ds_trans.
Require Import sb_metadata.
Require Import sb_msim.
Require Import sb_ds_gv_inject.
(*Require Import ssa_static.
Require Import ssa_props.*)

Module DSB := SBspecMetadata DGVs.

Ltac zauto := auto with zarith.
Ltac zeauto := eauto with zarith.


Import LLVMsyntax.
Import LLVMinfra.
Import LLVMgv.
Import LLVMtd.
Import LLVMtypings.
Import SB_ds_pass.

(* Freshness *)

Definition getValueID (v:value) : atoms :=
match v with
| value_id id => {{id}}
| value_const _ => {}
end.

(*
Fixpoint getParamsOperand (lp:params) : atoms :=
match lp with
| nil => {}
  | (t, v)::lp' => getValueID v `union` (getParamsOperand lp')
end.

Definition getCmdOperands (i:cmd) : atoms :=
match i with
| insn_bop _ _ _ v1 v2 => getValueID v1 `union` getValueID v2
| insn_fbop _ _ _ v1 v2 => getValueID v1 `union` getValueID v2
| insn_extractelement _ _ v _ => getValueID v
| insn_insertelement _ _ v1 _ v2 _ => getValueID v1 `union` getValueID v2
| insn_extractvalue _ _ v _ => getValueID v
| insn_insertvalue _ _ v1 _ v2 _ => getValueID v1 `union` getValueID v2
| insn_malloc _ _ v _ => getValueID v
| insn_free _ _ v => getValueID v
| insn_alloca _ _ v _ => getValueID v
| insn_load _ _ v _ => getValueID v
| insn_store _ _ v1 v2 _ => getValueID v1 `union` getValueID v2
| insn_gep _ _ _ v _ => getValueID v
| insn_trunc _ _ _ v _ => getValueID v
| insn_ext _ _ _ v1 typ2 => getValueID v1
| insn_cast _ _ _ v _ => getValueID v
| insn_icmp _ _ _ v1 v2 => getValueID v1 `union` getValueID v2
| insn_fcmp _ _ _ v1 v2 => getValueID v1 `union` getValueID v2
| insn_select _ v0 _ v1 v2 => 
    getValueID v0 `union` getValueID v1 `union` getValueID v2
| insn_call _ _ _ _ v0 lp => getValueID v0 `union` getParamsOperand lp
end.

Definition getCmdIDs (c:cmd) := {{getCmdLoc c}} `union` getCmdOperands c.
*)

Definition id_fresh_in_value v1 i2 : Prop :=
match v1 with
| value_id i1 => i1 <> i2
| _ => True
end.

Fixpoint ids2atoms (ids0:ids) : atoms :=
match ids0 with
| nil => {}
| id0::ids0' => {{id0}} `union` ids2atoms ids0'
end.

Fixpoint codom (rm:rmap) : atoms :=
match rm with
| nil => empty
| (_,(bid,eid))::rm' => singleton bid `union` singleton eid `union` codom rm'
end.

Fixpoint rm_codom_disjoint (rm:rmap) : Prop :=
match rm with
| nil => True
| (id0,(bid,eid))::rm' => 
    id0 <> bid /\ id0 <> eid /\ bid <> eid /\ 
    id0 `notin` codom rm' /\
    bid `notin` dom rm' `union` codom rm' /\
    eid `notin` dom rm' `union` codom rm' /\
    rm_codom_disjoint rm' 
end.

(*
Definition wf_fresh ex_ids c rm : Prop :=
AtomSetImpl.inter (getCmdIDs c) (codom rm) [<=] {} /\
getCmdLoc c `notin` getCmdOperands c /\
(getCmdIDs c) `union` codom rm `union` dom rm [<=] ids2atoms ex_ids /\
rm_codom_disjoint rm.

Fixpoint wf_freshs ex_ids cs rm2 : Prop :=
match cs with
| nil => True
| c::cs' => wf_fresh ex_ids c rm2 /\ wf_freshs ex_ids cs' rm2 
end.
*)

Lemma notin_codom__neq : forall rm d id0 id1 bid eid,
  AtomSetImpl.inter d (codom rm) [<=] {} ->
  id0 `in` d ->
  Some (bid, eid) = lookupAL _ rm id1 ->
  id0 <> bid /\ id0 <> eid.
Proof.
  induction rm; intros d id0 id1 bid eid J1 J2 J3.
    inversion J3.

    destruct a. destruct p. simpl in *.
    destruct (id1 == i0); subst.
      inv J3. clear IHrm. fsetdec.
      eapply IHrm in J3; eauto.
        clear - J1. fsetdec.
Qed.

(*
Lemma notin_codom__neq' : forall rm d id1 bid eid,
  AtomSetImpl.inter d (codom rm) [<=] {} ->
  Some (bid, eid) = lookupAL _ rm id1 ->
  bid `notin` d /\ eid `notin` d.
Proof.
  induction rm; intros d id1 bid eid J1 J2.
    inversion J2.

    destruct a. destruct p. simpl in *.
    destruct (id1 == i0); subst.
      inv J2. clear IHrm. fsetdec.
      eapply IHrm in J2; eauto.
        clear - J1. fsetdec.
Qed.
*)

Lemma ids2atoms_dom : forall x d,
  In x d <-> x `in` ids2atoms d.
Proof.
  induction d.
    split; intro J.
      inversion J.
      contradict J; fsetdec.
    split; simpl; intro J.
      destruct J as [J | J]; subst; auto.
        apply IHd in J. auto.

      assert (x `in` (singleton a) \/ x `in` (ids2atoms d)) as H.
        fsetdec.
      destruct H as [H | H]; try fsetdec.
        apply IHd in H. auto.
Qed.

Lemma tmp_is_fresh : forall i0 d ex_ids tmp ex_ids',
  i0 `in` d ->
  d [<=] ids2atoms ex_ids ->
  (tmp, ex_ids') = mk_tmp ex_ids ->
  i0 <> tmp.
Proof.
  intros. unfold mk_tmp in H1.
  destruct (atom_fresh_for_list ex_ids).
  inv H1.
  assert (x `notin` ids2atoms ex_ids) as J.
    intro H1. apply n.
    apply ids2atoms_dom; auto.              
  fsetdec.
Qed.

Lemma rmap_lookupAL : forall rm bid eid id1,
  ret (bid, eid) = lookupAL (id * id) rm id1 ->
  bid `in` codom rm /\ eid `in` codom rm /\ id1 `in` dom rm.
Proof.
  induction rm; intros.
    inversion H.
    destruct a. destruct p. simpl in *.
    destruct (id1 == a); subst.
      inv H. fsetdec.
      apply IHrm in H. fsetdec.
Qed.

Lemma rm_codom_disjoint_spec : forall rm pid bid eid,
  rm_codom_disjoint rm ->
  Some (bid, eid) = lookupAL _ rm pid ->
  bid <> eid /\ bid <> pid /\ eid <> pid.
Proof.
  induction rm; intros. 
    inversion H0.
    destruct a. destruct p. simpl in *.
    destruct (pid == i0); subst.
      inv H0. destruct H as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
      repeat split; auto.

      destruct H as [_ [_ [_ [_ [_ [_ H]]]]]].
      eapply IHrm in H; eauto.
Qed.

Lemma rm_codom_disjoint_spec' : forall rm bid1 eid1 id1 bid2 eid2 id2,
  rm_codom_disjoint rm ->
  ret (bid1, eid1) = lookupAL (id * id) rm id1 ->
  ret (bid2, eid2) = lookupAL (id * id) rm id2 ->
  id1 <> id2 ->
  bid1 <> bid2 /\ bid1 <> eid2 /\ bid1 <> id2 /\ bid1 <> id1 /\
  eid1 <> bid2 /\ eid1 <> eid2 /\ eid1 <> id1 /\ eid1 <> id2 /\
  bid2 <> id1 /\ eid2 <> id1.
Proof.
  induction rm; intros.
    inversion H0.
    destruct a. destruct p. simpl in *.
    destruct H as [H8 [H9 [H3 [H4 [H5 [H6 H7]]]]]].
    destruct (id1 == i0); subst.
      destruct (id2 == i0); subst.
        contradict H2; auto.

        inv H0.
        eapply rm_codom_disjoint_spec in H7; eauto.
        apply rmap_lookupAL in H1.
        destruct H1 as [H11 [H12 H13]].
        destruct H7 as [H0 [H1 H10]].
        repeat (split; auto). 
          clear - H5 H11. fsetdec.
          clear - H5 H12. fsetdec.
          clear - H5 H13. fsetdec.
          clear - H6 H11. fsetdec.
          clear - H6 H12. fsetdec.
          clear - H6 H13. fsetdec.
          clear - H11 H4. fsetdec.
          clear - H12 H4. fsetdec.
      destruct (id2 == i0); subst; eauto.
        inv H1.
        eapply rm_codom_disjoint_spec in H7; eauto.
        destruct H7 as [H1 [H7 H10]].
        apply rmap_lookupAL in H0.
        destruct H0 as [H11 [H12 H13]].
        repeat (split; auto). 
          clear - H5 H11. fsetdec.
          clear - H6 H11. fsetdec.
          clear - H4 H11. fsetdec.
          clear - H5 H12. fsetdec.
          clear - H6 H12. fsetdec.
          clear - H4 H12. fsetdec.
          clear - H5 H13. fsetdec.
          clear - H6 H13. fsetdec.
Qed.

Lemma tmp_is_fresh' : forall id1 ex_ids tmp ex_ids' bid eid rm,
  codom rm [<=] ids2atoms ex_ids ->
  Some (bid, eid) = lookupAL _ rm id1 ->
  (tmp, ex_ids') = mk_tmp ex_ids ->
  bid <> tmp /\ eid <> tmp.
Proof.
  intros. unfold mk_tmp in H1.
  destruct (atom_fresh_for_list ex_ids).
  inv H1.
  assert (x `notin` ids2atoms ex_ids) as J.
    intro H1. apply n.
    apply ids2atoms_dom; auto.              
  apply rmap_lookupAL in H0.
  fsetdec.
Qed.
(*
Lemma tmp_is_fresh_rm : forall id1 ex_ids tmp ex_ids' bid eid rm c,
  wf_fresh ex_ids c rm ->
  Some (bid, eid) = lookupAL _ rm id1 ->
  (tmp, ex_ids') = mk_tmp ex_ids ->
  bid <> tmp /\ eid <> tmp /\ id1 <> tmp.
Proof.
  intros. unfold mk_tmp in H1.
  destruct (atom_fresh_for_list ex_ids).
  inv H1.
  assert (x `notin` ids2atoms ex_ids) as J.
    intro H1. apply n.
    apply ids2atoms_dom; auto.              
  apply rmap_lookupAL in H0.
  destruct H as [J1 [J2 J3]].
  destruct H0 as [J4 [J5 J6]].
  clear J1 J2.
  split; fsetdec.
Qed.

Lemma wf_fresh__mk_tmp : forall ex_ids c rm2 ptmp ex_ids1,
  wf_fresh ex_ids c rm2 ->
  (ptmp, ex_ids1) = mk_tmp ex_ids ->
  wf_fresh ex_ids1 c rm2.
Proof.
  intros.
  destruct H as [J1 [J2 [J3 J4]]].
  split; auto.
  split; auto.
  split; auto.
    unfold mk_tmp in H0.
    destruct (atom_fresh_for_list ex_ids).
    inv H0.
    simpl.
    assert (x `notin` ids2atoms ex_ids) as J.
      intro H1. apply n.
      apply ids2atoms_dom; auto.              
    fsetdec.
Qed.
*)

Lemma mk_tmp_inc : forall ex_ids ex_ids3 ex_ids5 tmp,
  incl ex_ids ex_ids3 ->
  (tmp, ex_ids5) = mk_tmp ex_ids3 ->
  incl ex_ids ex_ids5.
Proof.
  intros. intros x J. unfold mk_tmp in H0.
  remember (atom_fresh_for_list ex_ids3) as R.
  destruct R. inv H0.
  simpl. auto.
Qed.

(*
Lemma wf_freshs__mk_tmp : forall cs ex_ids rm2 ptmp ex_ids1,
  wf_freshs ex_ids cs rm2 ->
  (ptmp, ex_ids1) = mk_tmp ex_ids ->
  wf_freshs ex_ids1 cs rm2.
Proof.
  induction cs; simpl; intros; auto.
    destruct H as [J1 J2].
    split; eauto using wf_fresh__mk_tmp.
Qed.
*)

(* Simulation *)

Definition reg_simulation (mi:MoreMem.meminj) TD gl (F:fdef) 
  (rm1:SBspecAux.rmetadata) (rm2:rmap) (lc1 lc2:GVMap) : Prop :=
(forall i0 gv1, 
  lookupAL _ lc1 i0 = Some gv1 -> 
  exists gv2, 
    lookupAL _ lc2 i0 = Some gv2 /\ gv_inject mi gv1 gv2
) /\
(forall vp blk1 bofs1 eofs1, 
  SBspecAux.get_reg_metadata TD gl rm1 vp = 
    Some (SBspecAux.mkMD blk1 bofs1 eofs1) -> 
  exists bv2, exists ev2, exists bgv2, exists egv2,
    get_reg_metadata rm2 vp = Some (bv2, ev2) /\
    getOperandValue TD bv2 lc2 gl = Some bgv2 /\
    getOperandValue TD ev2 lc2 gl = Some egv2 /\
    gv_inject mi ((Vptr blk1 bofs1, AST.Mint 31)::nil) bgv2 /\
    gv_inject mi ((Vptr blk1 eofs1, AST.Mint 31)::nil) egv2
) /\
(forall i0 gv1, lookupAL _ lc1 i0 = Some gv1 -> In i0 (getFdefLocs F)).

Definition mem_simulation (mi:MoreMem.meminj) TD (mgb:Values.block) 
  (MM1:SBspecAux.mmetadata) (Mem1 Mem2:mem) : Prop :=
MoreMem.mem_inj mi Mem1 Mem2 /\
0 <= mgb < Mem.nextblock Mem2 /\
(forall b1 ofs1, b1 >= Mem.nextblock Mem1 -> MM1 b1 ofs1 = None) /\
(forall lc2 gl b ofs blk bofs eofs als bid0 eid0 pgv' fs F B cs tmn S Ps 
    EC v cm,  
  wf_globals mgb gl -> 
  SBspecAux.get_mem_metadata TD MM1 ((Vptr b ofs,cm)::nil) = 
    SBspecAux.mkMD blk bofs eofs -> 
  gv_inject mi ((Vptr b ofs,cm)::nil) pgv' ->
  getOperandValue TD v lc2 gl = Some pgv' ->
  exists bgv', exists egv',
  DOS.Sem.sop_star (OpsemAux.mkCfg S TD Ps gl fs)
    (DOS.Sem.mkState 
      ((DOS.Sem.mkEC F B 
        (insn_call bid0 false attrs gmb_typ gmb_fn 
                       ((p8,v)::
                        (p8,vnullp8)::
                        (i32,vint1)::
                        (p32,vnullp32)::
                        nil)::
         insn_call eid0 false attrs gme_typ gme_fn 
                       ((p8,v)::
                        (p8,vnullp8)::
                        (i32,vint1)::
                        (p32,vnullp32)::
                        nil)::
         cs) 
        tmn lc2 als)
        ::EC) Mem2)
    (DOS.Sem.mkState
       ((DOS.Sem.mkEC F B cs tmn 
         (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als)::EC) 
         Mem2)
    trace_nil /\
    gv_inject mi ((Vptr blk bofs, AST.Mint 31)::nil) bgv' /\
    gv_inject mi ((Vptr blk eofs, AST.Mint 31)::nil) egv'
).

Fixpoint als_simulation (mi:MoreMem.meminj) (als1 als2:list mblock) : Prop :=
  match (als1, als2) with
  | (nil, nil) => True
  | (b1::als1', b2::als2') => 
      mi b1 = Some (b2, 0) /\ als_simulation mi als1' als2'
  | _ => False
  end.

Definition label_of_block (b:block) : l :=
match b with
| block_intro l1 _ _ _ => l1
end.

Definition is_user_function fh1 :=
match fh1 with
| (fheader_intro _ _ fid _ _) => isCallLib fid = false
end.

Definition sbEC_simulates_EC_tail (TD:TargetData) Ps1 gl (mi:MoreMem.meminj) 
  (sbEC:DSB.SBSEM.ExecutionContext) (EC:DOS.Sem.ExecutionContext) : Prop :=
  match (sbEC, EC) with
  | (DSB.SBSEM.mkEC f1 b1 ((insn_call i0 nr ca t0 v p)::cs13) tmn1 lc1 rm1 als1, 
     DOS.Sem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       let '(fdef_intro fh1 bs1) := f1 in
       let '(fdef_intro fh2 bs2) := f2 in
       let '(los, nts) := TD in
       is_user_function fh1 /\ 
       blockInFdefB b1 f1 = true /\
       InProductsB (product_fdef f1) Ps1 = true /\
       trans_fdef nts f1 = Some f2 /\
       tmn1 = tmn2 /\ als_simulation mi als1 als2 /\
       (label_of_block b1 = label_of_block b2) /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++(insn_call i0 nr ca t0 v p)::cs13) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       exists ex_ids, exists rm2, 
       exists ex_ids3, exists ex_ids4, exists cs22, exists cs23, exists cs24,
         gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids, rm2) /\
         reg_simulation mi TD gl f1 rm1 rm2 lc1 lc2 /\
         incl ex_ids ex_ids3 /\ 
         call_suffix i0 nr ca t0 v p rm2 = Some cs22 /\
         (*wf_freshs ex_ids3 cs13 rm2 /\*)
         trans_cmds ex_ids3 rm2 cs13 = Some (ex_ids4,cs23) /\
         trans_terminator rm2 tmn1 = Some cs24 /\
         cs2 = cs22 ++ cs23 ++ cs24
  | _ => False
  end.

Definition sbEC_simulates_EC_head (TD:TargetData) Ps1 gl (mi:MoreMem.meminj) 
  (sbEC:DSB.SBSEM.ExecutionContext) (EC:DOS.Sem.ExecutionContext) : Prop :=
  match (sbEC, EC) with
  | (DSB.SBSEM.mkEC f1 b1 cs12 tmn1 lc1 rm1 als1, 
     DOS.Sem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       let '(fdef_intro fh1 bs1) := f1 in
       let '(fdef_intro fh2 bs2) := f2 in
       let '(los, nts) := TD in
       is_user_function fh1 /\ 
       blockInFdefB b1 f1 = true /\
       InProductsB (product_fdef f1) Ps1 = true /\
       trans_fdef nts f1 = Some f2 /\
       tmn1 = tmn2 /\ als_simulation mi als1 als2 /\
       (label_of_block b1 = label_of_block b2) /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs12) tmn1) /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       exists ex_ids, exists rm2, 
       exists ex_ids3, exists ex_ids4, exists cs22, exists cs23,
         gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids, rm2) /\
         reg_simulation mi TD gl f1 rm1 rm2 lc1 lc2 /\
         incl ex_ids ex_ids3 /\ 
         (*wf_freshs ex_ids3 cs12 rm2 /\*)
         trans_cmds ex_ids3 rm2 cs12 = Some (ex_ids4,cs22) /\
         trans_terminator rm2 tmn1 = Some cs23 /\
         cs2 = cs22 ++ cs23
  end.

Fixpoint sbECs_simulate_ECs_tail (TD:TargetData) Ps1 gl (mi:MoreMem.meminj) 
  (sbECs:DSB.SBSEM.ECStack) (ECs:DOS.Sem.ECStack) : Prop :=
  match sbECs, ECs with
  | nil, nil => True
  | sbEC::sbECs', EC::ECs' => 
      sbEC_simulates_EC_tail TD Ps1 gl mi sbEC EC /\ 
      sbECs_simulate_ECs_tail TD Ps1 gl mi sbECs' ECs'
  | _, _ => False
  end.

Definition sbECs_simulate_ECs (TD:TargetData) Ps1 gl (mi:MoreMem.meminj) 
  (sbECs:DSB.SBSEM.ECStack) (ECs:DOS.Sem.ECStack) : Prop :=
  match sbECs, ECs with
  | sbEC::sbECs', EC::ECs' => 
      sbEC_simulates_EC_head TD Ps1 gl mi sbEC EC /\ 
      sbECs_simulate_ECs_tail TD Ps1 gl mi sbECs' ECs'
  | _, _ => False
  end.

Definition ftable_simulation mi fs1 fs2 : Prop :=
  forall fv1 fv2, gv_inject mi fv1 fv2 ->
    OpsemAux.lookupFdefViaGVFromFunTable fs1 fv1 = 
    OpsemAux.lookupFdefViaGVFromFunTable fs2 fv2.

Definition sbState_simulates_State (mi:MoreMem.meminj) (mgb:Values.block)
  (sbCfg:OpsemAux.Config) (sbSt:DSB.SBSEM.State) 
  (Cfg:OpsemAux.Config) (St:DOS.Sem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := sbCfg in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg in
  match (sbSt, St) with
  | (DSB.SBSEM.mkState ECs1 M1 MM1,
     DOS.Sem.mkState ECs2 M2) =>
      let '(los, nts) := TD1 in
      wf_system nil S1 /\
      moduleInSystemB (module_intro los nts Ps1) S1 = true /\
      trans_system S1 = Some S2 /\ 
      TD1 = TD2 /\ 
      trans_products nts Ps1 = Some Ps2 /\ 
      sbECs_simulate_ECs TD1 Ps1 gl1 mi ECs1 ECs2 /\
      gl1 = gl2 /\ 
      ftable_simulation mi fs1 fs2 /\ 
      wf_globals mgb gl1 /\
      wf_sb_mi mgb mi M1 M2 /\
      mem_simulation mi TD1 mgb MM1 M1 M2
  end.

Ltac destruct_ctx_other :=
match goal with
| [Hsim : sbState_simulates_State _ _
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           DSB.SBSEM.ECS := {|
                          DSB.SBSEM.CurFunction := ?F;
                          DSB.SBSEM.CurBB := _;
                          DSB.SBSEM.CurCmds := ?c::_;
                          DSB.SBSEM.Terminator := _;
                          DSB.SBSEM.Locals := _;
                          DSB.SBSEM.Rmap := _;
                          DSB.SBSEM.Allocas := _ |} :: _;
           DSB.SBSEM.Mem := _;
           DSB.SBSEM.Mmap := _ |} ?Cfg ?St |- _] =>
  destruct St as [ECs2 M2];
  destruct Cfg as [S2 TD2 Ps2 gl2 fs2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Htprds [Hfsim
    [Hwfg [Hwfmi HsimM]]]]]]]]]];
    subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct F as [fh1 bs1];
  destruct F2 as [fh2 bs2];
  destruct HsimEC as [Hclib [HBinF [HFinPS [Htfdef [Heq0 [Hasim [Hnth [Heqb1 
    [Heqb2 [ex_ids [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [Hgenmeta [Hrsim [Hinc 
    [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]; subst
end.

Fixpoint params_simulation TD gl mi lc2 
  (ogvs:list (GenericValue * option metadata)) n (cs:cmds) : Prop :=
match (ogvs, cs) with
| (nil, nil) => True
| ((gv, Some (mkMD blk bofs eofs))::ogvs, c1::c2::cs') =>
    exists bv2, exists ev2, exists bgv2, exists egv2, 
      c1 = insn_call fake_id true attrs ssb_typ ssb_fn 
                 ((p8,bv2)::(val32 n)::nil) /\
      c2 = insn_call fake_id true attrs sse_typ sse_fn 
                 ((p8,ev2)::(val32 n)::nil) /\
      getOperandValue TD bv2 lc2 gl = Some bgv2 /\
      getOperandValue TD ev2 lc2 gl = Some egv2 /\
      gv_inject mi ((Vptr blk bofs, AST.Mint 31)::nil) bgv2 /\
      gv_inject mi ((Vptr blk eofs, AST.Mint 31)::nil) egv2 /\
      params_simulation TD gl mi lc2 ogvs (n+1) cs'
| ((gv, None)::ogvs, c1::c2::cs') =>
    params_simulation TD gl mi lc2 ogvs (n+1) cs'
| _ => False
end.

Fixpoint incomingValues_simulation (mi:Values.meminj)
  (re1:list (id * GenericValue * monad metadata))(rm2:rmap)
  (re2:list (id * GenericValue)) : Prop :=
match (re1, re2) with
| (nil, nil) => True
| ((i1,gv1,None)::re1', (i2,gv2)::re2') =>
    i1 = i2 /\ gv_inject mi gv1 gv2 /\ incomingValues_simulation mi re1' rm2 re2'
| ((i1,gv1,Some (SBspecAux.mkMD blk1 bofs1 eofs1))::re1', 
   (eid2,egv2)::(bid2,bgv2)::(i2,gv2)::re2') =>
    i1 = i2 /\ gv_inject mi gv1 gv2 /\ 
    lookupAL _ rm2 i2 = Some (bid2,eid2) /\
    gv_inject mi ((Vptr blk1 bofs1, AST.Mint 31)::nil) bgv2 /\  
    gv_inject mi ((Vptr blk1 eofs1, AST.Mint 31)::nil) egv2 /\
    incomingValues_simulation mi re1' rm2 re2'
| _ => False
end.

Ltac destruct_ctx_br :=
match goal with
| [Hsim : sbState_simulates_State _ _
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           DSB.SBSEM.ECS := {|
                          DSB.SBSEM.CurFunction := ?F;
                          DSB.SBSEM.CurBB := _;
                          DSB.SBSEM.CurCmds := nil;
                          DSB.SBSEM.Terminator := _;
                          DSB.SBSEM.Locals := _;
                          DSB.SBSEM.Rmap := _;
                          DSB.SBSEM.Allocas := _ |} :: _;
           DSB.SBSEM.Mem := _;
           DSB.SBSEM.Mmap := _ |} ?Cfg ?St |- _] =>
  destruct Cfg as [S2 TD2 Ps2 gl2 fs2];
  destruct St as [ECs2 M2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Htprds [Hfsim [Hwfg 
    [Hwfmi HsimM]]]]]]]]]];
    subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct F as [fh1 bs1];
  destruct F2 as [fh2 bs2];
  destruct HsimEC as [Hclib [HBinF [HFinPs [Htfdef [Heq0 [Hasim [Hnth [Heqb1 
    [Heqb2 [ex_ids [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [Hgenmeta [Hrsim [Hinc 
    [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]; subst
end.

Ltac destruct_ctx_return :=
match goal with
| [Hsim : sbState_simulates_State _ _
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           DSB.SBSEM.ECS := {|
                          DSB.SBSEM.CurFunction := ?F;
                          DSB.SBSEM.CurBB := _;
                          DSB.SBSEM.CurCmds := nil;
                          DSB.SBSEM.Terminator := _;
                          DSB.SBSEM.Locals := _;
                          DSB.SBSEM.Rmap := _;
                          DSB.SBSEM.Allocas := _ |}
                          :: {|
                             DSB.SBSEM.CurFunction := ?F';
                             DSB.SBSEM.CurBB := _;
                             DSB.SBSEM.CurCmds := ?c' :: _;
                             DSB.SBSEM.Terminator := _;
                             DSB.SBSEM.Locals := _;
                             DSB.SBSEM.Rmap := _;
                             DSB.SBSEM.Allocas := _ |} :: _;
           DSB.SBSEM.Mem := _;
           DSB.SBSEM.Mmap := _ |} ?Cfg ?St |- _] =>
  destruct Cfg as [S2 TD2 Ps2 gl2 fs2];
  destruct St as [ECs2 M2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Htprds [Hfsim [Hwfg 
    [Hwfmi HsimM]]]]]]]]]];
    subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct ECs2 as [|[F2' B2' cs2' tmn2' lc2' als2'] ECs2];
    try solve [inversion HsimECs];
  destruct HsimECs as [HsimEC' HsimECs];
  destruct F as [fh1 bs1];
  destruct F2 as [fh2 bs2];
  destruct HsimEC as [Hclib [HBinF [HFinPs [Htfdef [Heq0 [Hasim [Hnth [Heqb1 
    [Heqb2 [ex_ids [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [Hgenmeta [Hrsim [Hinc 
    [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]; subst;
  destruct F' as [fh1' bs1'];
  destruct F2' as [fh2' bs2'];
  destruct c'; try solve [inversion HsimEC'];
  destruct HsimEC' as [Hclib' [HBinF' [HFinPs' [Htfdef' [Heq0' [Hasim' [Hnth' 
    [Heqb1' [Heqb2' [ex_ids' [rm2' [ex_ids3' [ex_ids4' [cs22' [cs23' [cs24' 
    [Hgenmeta' [Hrsim' [Hinc' [Hcall' [Htcmds' [Httmn' Heq2']]]]]]]]]]]]
    ]]]]]]]]]]; 
    subst
end.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
